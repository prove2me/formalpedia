-- Prove2me | solution 1 for syracuse_descends_range_2241435_2243435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:59.458407+00:00
-- url     : https://prove2.me/submissions/23202bd5-b68d-4894-9f8f-fb660ddf607f

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

theorem B8510453 : Blo 2241435 8510453 := bbase (se 5 (by rfl) ⟨398927, by rfl⟩ : syracuseStep 8510453 = 797855) (by norm_num)
theorem B5673635 : Blo 2241435 5673635 := bstep (se 1 (by rfl) ⟨4255226, by rfl⟩ : syracuseStep 5673635 = 8510453) B8510453
theorem B3782423 : Blo 2241435 3782423 := bstep (se 1 (by rfl) ⟨2836817, by rfl⟩ : syracuseStep 3782423 = 5673635) B5673635
theorem B2521615 : Blo 2241435 2521615 := bstep (se 1 (by rfl) ⟨1891211, by rfl⟩ : syracuseStep 2521615 = 3782423) B3782423
theorem B3362153 : Blo 2241435 3362153 := bstep (se 2 (by rfl) ⟨1260807, by rfl⟩ : syracuseStep 3362153 = 2521615) B2521615
theorem B2241435 : Blo 2241435 2241435 := bstep (se 1 (by rfl) ⟨1681076, by rfl⟩ : syracuseStep 2241435 = 3362153) B3362153
theorem B2393569 : Blo 2241435 2393569 := bbase (se 2 (by rfl) ⟨897588, by rfl⟩ : syracuseStep 2393569 = 1795177) (by norm_num)
theorem B12765701 : Blo 2241435 12765701 := bstep (se 4 (by rfl) ⟨1196784, by rfl⟩ : syracuseStep 12765701 = 2393569) B2393569
theorem B8510467 : Blo 2241435 8510467 := bstep (se 1 (by rfl) ⟨6382850, by rfl⟩ : syracuseStep 8510467 = 12765701) B12765701
theorem B11347289 : Blo 2241435 11347289 := bstep (se 2 (by rfl) ⟨4255233, by rfl⟩ : syracuseStep 11347289 = 8510467) B8510467
theorem B7564859 : Blo 2241435 7564859 := bstep (se 1 (by rfl) ⟨5673644, by rfl⟩ : syracuseStep 7564859 = 11347289) B11347289
theorem B5043239 : Blo 2241435 5043239 := bstep (se 1 (by rfl) ⟨3782429, by rfl⟩ : syracuseStep 5043239 = 7564859) B7564859
theorem B3362159 : Blo 2241435 3362159 := bstep (se 1 (by rfl) ⟨2521619, by rfl⟩ : syracuseStep 3362159 = 5043239) B5043239
theorem B2241439 : Blo 2241435 2241439 := bstep (se 1 (by rfl) ⟨1681079, by rfl⟩ : syracuseStep 2241439 = 3362159) B3362159
theorem B3362165 : Blo 2241435 3362165 := bbase (se 5 (by rfl) ⟨157601, by rfl⟩ : syracuseStep 3362165 = 315203) (by norm_num)
theorem B2241443 : Blo 2241435 2241443 := bstep (se 1 (by rfl) ⟨1681082, by rfl⟩ : syracuseStep 2241443 = 3362165) B3362165
theorem B3191437 : Blo 2241435 3191437 := bbase (se 3 (by rfl) ⟨598394, by rfl⟩ : syracuseStep 3191437 = 1196789) (by norm_num)
theorem B4255249 : Blo 2241435 4255249 := bstep (se 2 (by rfl) ⟨1595718, by rfl⟩ : syracuseStep 4255249 = 3191437) B3191437
theorem B5673665 : Blo 2241435 5673665 := bstep (se 2 (by rfl) ⟨2127624, by rfl⟩ : syracuseStep 5673665 = 4255249) B4255249
theorem B3782443 : Blo 2241435 3782443 := bstep (se 1 (by rfl) ⟨2836832, by rfl⟩ : syracuseStep 3782443 = 5673665) B5673665
theorem B5043257 : Blo 2241435 5043257 := bstep (se 2 (by rfl) ⟨1891221, by rfl⟩ : syracuseStep 5043257 = 3782443) B3782443
theorem B3362171 : Blo 2241435 3362171 := bstep (se 1 (by rfl) ⟨2521628, by rfl⟩ : syracuseStep 3362171 = 5043257) B5043257
theorem B2241447 : Blo 2241435 2241447 := bstep (se 1 (by rfl) ⟨1681085, by rfl⟩ : syracuseStep 2241447 = 3362171) B3362171
theorem B2521633 : Blo 2241435 2521633 := bbase (se 2 (by rfl) ⟨945612, by rfl⟩ : syracuseStep 2521633 = 1891225) (by norm_num)
theorem B3362177 : Blo 2241435 3362177 := bstep (se 2 (by rfl) ⟨1260816, by rfl⟩ : syracuseStep 3362177 = 2521633) B2521633
theorem B2241451 : Blo 2241435 2241451 := bstep (se 1 (by rfl) ⟨1681088, by rfl⟩ : syracuseStep 2241451 = 3362177) B3362177
theorem B5673685 : Blo 2241435 5673685 := bbase (se 7 (by rfl) ⟨66488, by rfl⟩ : syracuseStep 5673685 = 132977) (by norm_num)
theorem B7564913 : Blo 2241435 7564913 := bstep (se 2 (by rfl) ⟨2836842, by rfl⟩ : syracuseStep 7564913 = 5673685) B5673685
theorem B5043275 : Blo 2241435 5043275 := bstep (se 1 (by rfl) ⟨3782456, by rfl⟩ : syracuseStep 5043275 = 7564913) B7564913
theorem B3362183 : Blo 2241435 3362183 := bstep (se 1 (by rfl) ⟨2521637, by rfl⟩ : syracuseStep 3362183 = 5043275) B5043275
theorem B2241455 : Blo 2241435 2241455 := bstep (se 1 (by rfl) ⟨1681091, by rfl⟩ : syracuseStep 2241455 = 3362183) B3362183
theorem B3362189 : Blo 2241435 3362189 := bbase (se 3 (by rfl) ⟨630410, by rfl⟩ : syracuseStep 3362189 = 1260821) (by norm_num)
theorem B2241459 : Blo 2241435 2241459 := bstep (se 1 (by rfl) ⟨1681094, by rfl⟩ : syracuseStep 2241459 = 3362189) B3362189
theorem B5043293 : Blo 2241435 5043293 := bbase (se 3 (by rfl) ⟨945617, by rfl⟩ : syracuseStep 5043293 = 1891235) (by norm_num)
theorem B3362195 : Blo 2241435 3362195 := bstep (se 1 (by rfl) ⟨2521646, by rfl⟩ : syracuseStep 3362195 = 5043293) B5043293
theorem B2241463 : Blo 2241435 2241463 := bstep (se 1 (by rfl) ⟨1681097, by rfl⟩ : syracuseStep 2241463 = 3362195) B3362195
theorem B3782477 : Blo 2241435 3782477 := bbase (se 3 (by rfl) ⟨709214, by rfl⟩ : syracuseStep 3782477 = 1418429) (by norm_num)
theorem B2521651 : Blo 2241435 2521651 := bstep (se 1 (by rfl) ⟨1891238, by rfl⟩ : syracuseStep 2521651 = 3782477) B3782477
theorem B3362201 : Blo 2241435 3362201 := bstep (se 2 (by rfl) ⟨1260825, by rfl⟩ : syracuseStep 3362201 = 2521651) B2521651
theorem B2241467 : Blo 2241435 2241467 := bstep (se 1 (by rfl) ⟨1681100, by rfl⟩ : syracuseStep 2241467 = 3362201) B3362201
theorem B9088213 : Blo 2241435 9088213 := bbase (se 7 (by rfl) ⟨106502, by rfl⟩ : syracuseStep 9088213 = 213005) (by norm_num)
theorem B12117617 : Blo 2241435 12117617 := bstep (se 2 (by rfl) ⟨4544106, by rfl⟩ : syracuseStep 12117617 = 9088213) B9088213
theorem B8078411 : Blo 2241435 8078411 := bstep (se 1 (by rfl) ⟨6058808, by rfl⟩ : syracuseStep 8078411 = 12117617) B12117617
theorem B21542429 : Blo 2241435 21542429 := bstep (se 3 (by rfl) ⟨4039205, by rfl⟩ : syracuseStep 21542429 = 8078411) B8078411
theorem B14361619 : Blo 2241435 14361619 := bstep (se 1 (by rfl) ⟨10771214, by rfl⟩ : syracuseStep 14361619 = 21542429) B21542429
theorem B19148825 : Blo 2241435 19148825 := bstep (se 2 (by rfl) ⟨7180809, by rfl⟩ : syracuseStep 19148825 = 14361619) B14361619
theorem B12765883 : Blo 2241435 12765883 := bstep (se 1 (by rfl) ⟨9574412, by rfl⟩ : syracuseStep 12765883 = 19148825) B19148825
theorem B17021177 : Blo 2241435 17021177 := bstep (se 2 (by rfl) ⟨6382941, by rfl⟩ : syracuseStep 17021177 = 12765883) B12765883
theorem B11347451 : Blo 2241435 11347451 := bstep (se 1 (by rfl) ⟨8510588, by rfl⟩ : syracuseStep 11347451 = 17021177) B17021177
theorem B7564967 : Blo 2241435 7564967 := bstep (se 1 (by rfl) ⟨5673725, by rfl⟩ : syracuseStep 7564967 = 11347451) B11347451
theorem B5043311 : Blo 2241435 5043311 := bstep (se 1 (by rfl) ⟨3782483, by rfl⟩ : syracuseStep 5043311 = 7564967) B7564967
theorem B3362207 : Blo 2241435 3362207 := bstep (se 1 (by rfl) ⟨2521655, by rfl⟩ : syracuseStep 3362207 = 5043311) B5043311
theorem B2241471 : Blo 2241435 2241471 := bstep (se 1 (by rfl) ⟨1681103, by rfl⟩ : syracuseStep 2241471 = 3362207) B3362207
theorem B3362213 : Blo 2241435 3362213 := bbase (se 4 (by rfl) ⟨315207, by rfl⟩ : syracuseStep 3362213 = 630415) (by norm_num)
theorem B2241475 : Blo 2241435 2241475 := bstep (se 1 (by rfl) ⟨1681106, by rfl⟩ : syracuseStep 2241475 = 3362213) B3362213
theorem B2836873 : Blo 2241435 2836873 := bbase (se 2 (by rfl) ⟨1063827, by rfl⟩ : syracuseStep 2836873 = 2127655) (by norm_num)
theorem B3782497 : Blo 2241435 3782497 := bstep (se 2 (by rfl) ⟨1418436, by rfl⟩ : syracuseStep 3782497 = 2836873) B2836873
theorem B5043329 : Blo 2241435 5043329 := bstep (se 2 (by rfl) ⟨1891248, by rfl⟩ : syracuseStep 5043329 = 3782497) B3782497
theorem B3362219 : Blo 2241435 3362219 := bstep (se 1 (by rfl) ⟨2521664, by rfl⟩ : syracuseStep 3362219 = 5043329) B5043329
theorem B2241479 : Blo 2241435 2241479 := bstep (se 1 (by rfl) ⟨1681109, by rfl⟩ : syracuseStep 2241479 = 3362219) B3362219
theorem B2521669 : Blo 2241435 2521669 := bbase (se 4 (by rfl) ⟨236406, by rfl⟩ : syracuseStep 2521669 = 472813) (by norm_num)
theorem B3362225 : Blo 2241435 3362225 := bstep (se 2 (by rfl) ⟨1260834, by rfl⟩ : syracuseStep 3362225 = 2521669) B2521669
theorem B2241483 : Blo 2241435 2241483 := bstep (se 1 (by rfl) ⟨1681112, by rfl⟩ : syracuseStep 2241483 = 3362225) B3362225
theorem B4255325 : Blo 2241435 4255325 := bbase (se 3 (by rfl) ⟨797873, by rfl⟩ : syracuseStep 4255325 = 1595747) (by norm_num)
theorem B2836883 : Blo 2241435 2836883 := bstep (se 1 (by rfl) ⟨2127662, by rfl⟩ : syracuseStep 2836883 = 4255325) B4255325
theorem B7565021 : Blo 2241435 7565021 := bstep (se 3 (by rfl) ⟨1418441, by rfl⟩ : syracuseStep 7565021 = 2836883) B2836883
theorem B5043347 : Blo 2241435 5043347 := bstep (se 1 (by rfl) ⟨3782510, by rfl⟩ : syracuseStep 5043347 = 7565021) B7565021
theorem B3362231 : Blo 2241435 3362231 := bstep (se 1 (by rfl) ⟨2521673, by rfl⟩ : syracuseStep 3362231 = 5043347) B5043347
theorem B2241487 : Blo 2241435 2241487 := bstep (se 1 (by rfl) ⟨1681115, by rfl⟩ : syracuseStep 2241487 = 3362231) B3362231
theorem B3362237 : Blo 2241435 3362237 := bbase (se 3 (by rfl) ⟨630419, by rfl⟩ : syracuseStep 3362237 = 1260839) (by norm_num)
theorem B2241491 : Blo 2241435 2241491 := bstep (se 1 (by rfl) ⟨1681118, by rfl⟩ : syracuseStep 2241491 = 3362237) B3362237
theorem B5043365 : Blo 2241435 5043365 := bbase (se 4 (by rfl) ⟨472815, by rfl⟩ : syracuseStep 5043365 = 945631) (by norm_num)
theorem B3362243 : Blo 2241435 3362243 := bstep (se 1 (by rfl) ⟨2521682, by rfl⟩ : syracuseStep 3362243 = 5043365) B5043365
theorem B2241495 : Blo 2241435 2241495 := bstep (se 1 (by rfl) ⟨1681121, by rfl⟩ : syracuseStep 2241495 = 3362243) B3362243
theorem B5673797 : Blo 2241435 5673797 := bbase (se 4 (by rfl) ⟨531918, by rfl⟩ : syracuseStep 5673797 = 1063837) (by norm_num)
theorem B3782531 : Blo 2241435 3782531 := bstep (se 1 (by rfl) ⟨2836898, by rfl⟩ : syracuseStep 3782531 = 5673797) B5673797
theorem B2521687 : Blo 2241435 2521687 := bstep (se 1 (by rfl) ⟨1891265, by rfl⟩ : syracuseStep 2521687 = 3782531) B3782531
theorem B3362249 : Blo 2241435 3362249 := bstep (se 2 (by rfl) ⟨1260843, by rfl⟩ : syracuseStep 3362249 = 2521687) B2521687
theorem B2241499 : Blo 2241435 2241499 := bstep (se 1 (by rfl) ⟨1681124, by rfl⟩ : syracuseStep 2241499 = 3362249) B3362249
theorem B5385685 : Blo 2241435 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B7180913 : Blo 2241435 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B4787275 : Blo 2241435 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B6383033 : Blo 2241435 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B4255355 : Blo 2241435 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B11347613 : Blo 2241435 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B7565075 : Blo 2241435 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B5043383 : Blo 2241435 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B3362255 : Blo 2241435 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B2241503 : Blo 2241435 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B3362261 : Blo 2241435 3362261 := bbase (se 7 (by rfl) ⟨39401, by rfl⟩ : syracuseStep 3362261 = 78803) (by norm_num)
theorem B2241507 : Blo 2241435 2241507 := bstep (se 1 (by rfl) ⟨1681130, by rfl⟩ : syracuseStep 2241507 = 3362261) B3362261
theorem B8510741 : Blo 2241435 8510741 := bbase (se 6 (by rfl) ⟨199470, by rfl⟩ : syracuseStep 8510741 = 398941) (by norm_num)
theorem B5673827 : Blo 2241435 5673827 := bstep (se 1 (by rfl) ⟨4255370, by rfl⟩ : syracuseStep 5673827 = 8510741) B8510741
theorem B3782551 : Blo 2241435 3782551 := bstep (se 1 (by rfl) ⟨2836913, by rfl⟩ : syracuseStep 3782551 = 5673827) B5673827
theorem B5043401 : Blo 2241435 5043401 := bstep (se 2 (by rfl) ⟨1891275, by rfl⟩ : syracuseStep 5043401 = 3782551) B3782551
theorem B3362267 : Blo 2241435 3362267 := bstep (se 1 (by rfl) ⟨2521700, by rfl⟩ : syracuseStep 3362267 = 5043401) B5043401
theorem B2241511 : Blo 2241435 2241511 := bstep (se 1 (by rfl) ⟨1681133, by rfl⟩ : syracuseStep 2241511 = 3362267) B3362267
theorem B2521705 : Blo 2241435 2521705 := bbase (se 2 (by rfl) ⟨945639, by rfl⟩ : syracuseStep 2521705 = 1891279) (by norm_num)
theorem B3362273 : Blo 2241435 3362273 := bstep (se 2 (by rfl) ⟨1260852, by rfl⟩ : syracuseStep 3362273 = 2521705) B2521705
theorem B2241515 : Blo 2241435 2241515 := bstep (se 1 (by rfl) ⟨1681136, by rfl⟩ : syracuseStep 2241515 = 3362273) B3362273
theorem B4787309 : Blo 2241435 4787309 := bbase (se 3 (by rfl) ⟨897620, by rfl⟩ : syracuseStep 4787309 = 1795241) (by norm_num)
theorem B12766157 : Blo 2241435 12766157 := bstep (se 3 (by rfl) ⟨2393654, by rfl⟩ : syracuseStep 12766157 = 4787309) B4787309
theorem B8510771 : Blo 2241435 8510771 := bstep (se 1 (by rfl) ⟨6383078, by rfl⟩ : syracuseStep 8510771 = 12766157) B12766157
theorem B5673847 : Blo 2241435 5673847 := bstep (se 1 (by rfl) ⟨4255385, by rfl⟩ : syracuseStep 5673847 = 8510771) B8510771
theorem B7565129 : Blo 2241435 7565129 := bstep (se 2 (by rfl) ⟨2836923, by rfl⟩ : syracuseStep 7565129 = 5673847) B5673847
theorem B5043419 : Blo 2241435 5043419 := bstep (se 1 (by rfl) ⟨3782564, by rfl⟩ : syracuseStep 5043419 = 7565129) B7565129
theorem B3362279 : Blo 2241435 3362279 := bstep (se 1 (by rfl) ⟨2521709, by rfl⟩ : syracuseStep 3362279 = 5043419) B5043419
theorem B2241519 : Blo 2241435 2241519 := bstep (se 1 (by rfl) ⟨1681139, by rfl⟩ : syracuseStep 2241519 = 3362279) B3362279
theorem B3362285 : Blo 2241435 3362285 := bbase (se 3 (by rfl) ⟨630428, by rfl⟩ : syracuseStep 3362285 = 1260857) (by norm_num)
theorem B2241523 : Blo 2241435 2241523 := bstep (se 1 (by rfl) ⟨1681142, by rfl⟩ : syracuseStep 2241523 = 3362285) B3362285
theorem B5043437 : Blo 2241435 5043437 := bbase (se 3 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 5043437 = 1891289) (by norm_num)
theorem B3362291 : Blo 2241435 3362291 := bstep (se 1 (by rfl) ⟨2521718, by rfl⟩ : syracuseStep 3362291 = 5043437) B5043437
theorem B2241527 : Blo 2241435 2241527 := bstep (se 1 (by rfl) ⟨1681145, by rfl⟩ : syracuseStep 2241527 = 3362291) B3362291
theorem B3191557 : Blo 2241435 3191557 := bbase (se 4 (by rfl) ⟨299208, by rfl⟩ : syracuseStep 3191557 = 598417) (by norm_num)
theorem B4255409 : Blo 2241435 4255409 := bstep (se 2 (by rfl) ⟨1595778, by rfl⟩ : syracuseStep 4255409 = 3191557) B3191557
theorem B2836939 : Blo 2241435 2836939 := bstep (se 1 (by rfl) ⟨2127704, by rfl⟩ : syracuseStep 2836939 = 4255409) B4255409
theorem B3782585 : Blo 2241435 3782585 := bstep (se 2 (by rfl) ⟨1418469, by rfl⟩ : syracuseStep 3782585 = 2836939) B2836939
theorem B2521723 : Blo 2241435 2521723 := bstep (se 1 (by rfl) ⟨1891292, by rfl⟩ : syracuseStep 2521723 = 3782585) B3782585
theorem B3362297 : Blo 2241435 3362297 := bstep (se 2 (by rfl) ⟨1260861, by rfl⟩ : syracuseStep 3362297 = 2521723) B2521723
theorem B2241531 : Blo 2241435 2241531 := bstep (se 1 (by rfl) ⟨1681148, by rfl⟩ : syracuseStep 2241531 = 3362297) B3362297
theorem B6058981 : Blo 2241435 6058981 := bbase (se 4 (by rfl) ⟨568029, by rfl⟩ : syracuseStep 6058981 = 1136059) (by norm_num)
theorem B32314565 : Blo 2241435 32314565 := bstep (se 4 (by rfl) ⟨3029490, by rfl⟩ : syracuseStep 32314565 = 6058981) B6058981
theorem B86172173 : Blo 2241435 86172173 := bstep (se 3 (by rfl) ⟨16157282, by rfl⟩ : syracuseStep 86172173 = 32314565) B32314565
theorem B57448115 : Blo 2241435 57448115 := bstep (se 1 (by rfl) ⟨43086086, by rfl⟩ : syracuseStep 57448115 = 86172173) B86172173
theorem B38298743 : Blo 2241435 38298743 := bstep (se 1 (by rfl) ⟨28724057, by rfl⟩ : syracuseStep 38298743 = 57448115) B57448115
theorem B25532495 : Blo 2241435 25532495 := bstep (se 1 (by rfl) ⟨19149371, by rfl⟩ : syracuseStep 25532495 = 38298743) B38298743
theorem B17021663 : Blo 2241435 17021663 := bstep (se 1 (by rfl) ⟨12766247, by rfl⟩ : syracuseStep 17021663 = 25532495) B25532495
theorem B11347775 : Blo 2241435 11347775 := bstep (se 1 (by rfl) ⟨8510831, by rfl⟩ : syracuseStep 11347775 = 17021663) B17021663
theorem B7565183 : Blo 2241435 7565183 := bstep (se 1 (by rfl) ⟨5673887, by rfl⟩ : syracuseStep 7565183 = 11347775) B11347775
theorem B5043455 : Blo 2241435 5043455 := bstep (se 1 (by rfl) ⟨3782591, by rfl⟩ : syracuseStep 5043455 = 7565183) B7565183
theorem B3362303 : Blo 2241435 3362303 := bstep (se 1 (by rfl) ⟨2521727, by rfl⟩ : syracuseStep 3362303 = 5043455) B5043455
theorem B2241535 : Blo 2241435 2241535 := bstep (se 1 (by rfl) ⟨1681151, by rfl⟩ : syracuseStep 2241535 = 3362303) B3362303
theorem B3362309 : Blo 2241435 3362309 := bbase (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) (by norm_num)
theorem B2241539 : Blo 2241435 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B3782605 : Blo 2241435 3782605 := bbase (se 3 (by rfl) ⟨709238, by rfl⟩ : syracuseStep 3782605 = 1418477) (by norm_num)
theorem B5043473 : Blo 2241435 5043473 := bstep (se 2 (by rfl) ⟨1891302, by rfl⟩ : syracuseStep 5043473 = 3782605) B3782605
theorem B3362315 : Blo 2241435 3362315 := bstep (se 1 (by rfl) ⟨2521736, by rfl⟩ : syracuseStep 3362315 = 5043473) B5043473
theorem B2241543 : Blo 2241435 2241543 := bstep (se 1 (by rfl) ⟨1681157, by rfl⟩ : syracuseStep 2241543 = 3362315) B3362315
theorem B2521741 : Blo 2241435 2521741 := bbase (se 3 (by rfl) ⟨472826, by rfl⟩ : syracuseStep 2521741 = 945653) (by norm_num)
theorem B3362321 : Blo 2241435 3362321 := bstep (se 2 (by rfl) ⟨1260870, by rfl⟩ : syracuseStep 3362321 = 2521741) B2521741
theorem B2241547 : Blo 2241435 2241547 := bstep (se 1 (by rfl) ⟨1681160, by rfl⟩ : syracuseStep 2241547 = 3362321) B3362321
theorem B7565237 : Blo 2241435 7565237 := bbase (se 5 (by rfl) ⟨354620, by rfl⟩ : syracuseStep 7565237 = 709241) (by norm_num)
theorem B5043491 : Blo 2241435 5043491 := bstep (se 1 (by rfl) ⟨3782618, by rfl⟩ : syracuseStep 5043491 = 7565237) B7565237
theorem B3362327 : Blo 2241435 3362327 := bstep (se 1 (by rfl) ⟨2521745, by rfl⟩ : syracuseStep 3362327 = 5043491) B5043491
theorem B2241551 : Blo 2241435 2241551 := bstep (se 1 (by rfl) ⟨1681163, by rfl⟩ : syracuseStep 2241551 = 3362327) B3362327
theorem B3362333 : Blo 2241435 3362333 := bbase (se 3 (by rfl) ⟨630437, by rfl⟩ : syracuseStep 3362333 = 1260875) (by norm_num)
theorem B2241555 : Blo 2241435 2241555 := bstep (se 1 (by rfl) ⟨1681166, by rfl⟩ : syracuseStep 2241555 = 3362333) B3362333
theorem B5043509 : Blo 2241435 5043509 := bbase (se 5 (by rfl) ⟨236414, by rfl⟩ : syracuseStep 5043509 = 472829) (by norm_num)
theorem B3362339 : Blo 2241435 3362339 := bstep (se 1 (by rfl) ⟨2521754, by rfl⟩ : syracuseStep 3362339 = 5043509) B5043509
theorem B2241559 : Blo 2241435 2241559 := bstep (se 1 (by rfl) ⟨1681169, by rfl⟩ : syracuseStep 2241559 = 3362339) B3362339
theorem B21543317 : Blo 2241435 21543317 := bbase (se 6 (by rfl) ⟨504921, by rfl⟩ : syracuseStep 21543317 = 1009843) (by norm_num)
theorem B14362211 : Blo 2241435 14362211 := bstep (se 1 (by rfl) ⟨10771658, by rfl⟩ : syracuseStep 14362211 = 21543317) B21543317
theorem B9574807 : Blo 2241435 9574807 := bstep (se 1 (by rfl) ⟨7181105, by rfl⟩ : syracuseStep 9574807 = 14362211) B14362211
theorem B12766409 : Blo 2241435 12766409 := bstep (se 2 (by rfl) ⟨4787403, by rfl⟩ : syracuseStep 12766409 = 9574807) B9574807
theorem B8510939 : Blo 2241435 8510939 := bstep (se 1 (by rfl) ⟨6383204, by rfl⟩ : syracuseStep 8510939 = 12766409) B12766409
theorem B5673959 : Blo 2241435 5673959 := bstep (se 1 (by rfl) ⟨4255469, by rfl⟩ : syracuseStep 5673959 = 8510939) B8510939
theorem B3782639 : Blo 2241435 3782639 := bstep (se 1 (by rfl) ⟨2836979, by rfl⟩ : syracuseStep 3782639 = 5673959) B5673959
theorem B2521759 : Blo 2241435 2521759 := bstep (se 1 (by rfl) ⟨1891319, by rfl⟩ : syracuseStep 2521759 = 3782639) B3782639
theorem B3362345 : Blo 2241435 3362345 := bstep (se 2 (by rfl) ⟨1260879, by rfl⟩ : syracuseStep 3362345 = 2521759) B2521759
theorem B2241563 : Blo 2241435 2241563 := bstep (se 1 (by rfl) ⟨1681172, by rfl⟩ : syracuseStep 2241563 = 3362345) B3362345
theorem B18177205 : Blo 2241435 18177205 := bbase (se 5 (by rfl) ⟨852056, by rfl⟩ : syracuseStep 18177205 = 1704113) (by norm_num)
theorem B24236273 : Blo 2241435 24236273 := bstep (se 2 (by rfl) ⟨9088602, by rfl⟩ : syracuseStep 24236273 = 18177205) B18177205
theorem B16157515 : Blo 2241435 16157515 := bstep (se 1 (by rfl) ⟨12118136, by rfl⟩ : syracuseStep 16157515 = 24236273) B24236273
theorem B21543353 : Blo 2241435 21543353 := bstep (se 2 (by rfl) ⟨8078757, by rfl⟩ : syracuseStep 21543353 = 16157515) B16157515
theorem B14362235 : Blo 2241435 14362235 := bstep (se 1 (by rfl) ⟨10771676, by rfl⟩ : syracuseStep 14362235 = 21543353) B21543353
theorem B9574823 : Blo 2241435 9574823 := bstep (se 1 (by rfl) ⟨7181117, by rfl⟩ : syracuseStep 9574823 = 14362235) B14362235
theorem B6383215 : Blo 2241435 6383215 := bstep (se 1 (by rfl) ⟨4787411, by rfl⟩ : syracuseStep 6383215 = 9574823) B9574823
theorem B8510953 : Blo 2241435 8510953 := bstep (se 2 (by rfl) ⟨3191607, by rfl⟩ : syracuseStep 8510953 = 6383215) B6383215
theorem B11347937 : Blo 2241435 11347937 := bstep (se 2 (by rfl) ⟨4255476, by rfl⟩ : syracuseStep 11347937 = 8510953) B8510953
theorem B7565291 : Blo 2241435 7565291 := bstep (se 1 (by rfl) ⟨5673968, by rfl⟩ : syracuseStep 7565291 = 11347937) B11347937
theorem B5043527 : Blo 2241435 5043527 := bstep (se 1 (by rfl) ⟨3782645, by rfl⟩ : syracuseStep 5043527 = 7565291) B7565291
theorem B3362351 : Blo 2241435 3362351 := bstep (se 1 (by rfl) ⟨2521763, by rfl⟩ : syracuseStep 3362351 = 5043527) B5043527
theorem B2241567 : Blo 2241435 2241567 := bstep (se 1 (by rfl) ⟨1681175, by rfl⟩ : syracuseStep 2241567 = 3362351) B3362351
theorem B3362357 : Blo 2241435 3362357 := bbase (se 5 (by rfl) ⟨157610, by rfl⟩ : syracuseStep 3362357 = 315221) (by norm_num)
theorem B2241571 : Blo 2241435 2241571 := bstep (se 1 (by rfl) ⟨1681178, by rfl⟩ : syracuseStep 2241571 = 3362357) B3362357
theorem B5673989 : Blo 2241435 5673989 := bbase (se 4 (by rfl) ⟨531936, by rfl⟩ : syracuseStep 5673989 = 1063873) (by norm_num)
theorem B3782659 : Blo 2241435 3782659 := bstep (se 1 (by rfl) ⟨2836994, by rfl⟩ : syracuseStep 3782659 = 5673989) B5673989
theorem B5043545 : Blo 2241435 5043545 := bstep (se 2 (by rfl) ⟨1891329, by rfl⟩ : syracuseStep 5043545 = 3782659) B3782659
theorem B3362363 : Blo 2241435 3362363 := bstep (se 1 (by rfl) ⟨2521772, by rfl⟩ : syracuseStep 3362363 = 5043545) B5043545
theorem B2241575 : Blo 2241435 2241575 := bstep (se 1 (by rfl) ⟨1681181, by rfl⟩ : syracuseStep 2241575 = 3362363) B3362363
theorem B2521777 : Blo 2241435 2521777 := bbase (se 2 (by rfl) ⟨945666, by rfl⟩ : syracuseStep 2521777 = 1891333) (by norm_num)
theorem B3362369 : Blo 2241435 3362369 := bstep (se 2 (by rfl) ⟨1260888, by rfl⟩ : syracuseStep 3362369 = 2521777) B2521777
theorem B2241579 : Blo 2241435 2241579 := bstep (se 1 (by rfl) ⟨1681184, by rfl⟩ : syracuseStep 2241579 = 3362369) B3362369
theorem B3029557 : Blo 2241435 3029557 := bbase (se 5 (by rfl) ⟨142010, by rfl⟩ : syracuseStep 3029557 = 284021) (by norm_num)
theorem B4039409 : Blo 2241435 4039409 := bstep (se 2 (by rfl) ⟨1514778, by rfl⟩ : syracuseStep 4039409 = 3029557) B3029557
theorem B2692939 : Blo 2241435 2692939 := bstep (se 1 (by rfl) ⟨2019704, by rfl⟩ : syracuseStep 2692939 = 4039409) B4039409
theorem B3590585 : Blo 2241435 3590585 := bstep (se 2 (by rfl) ⟨1346469, by rfl⟩ : syracuseStep 3590585 = 2692939) B2692939
theorem B2393723 : Blo 2241435 2393723 := bstep (se 1 (by rfl) ⟨1795292, by rfl⟩ : syracuseStep 2393723 = 3590585) B3590585
theorem B6383261 : Blo 2241435 6383261 := bstep (se 3 (by rfl) ⟨1196861, by rfl⟩ : syracuseStep 6383261 = 2393723) B2393723
theorem B4255507 : Blo 2241435 4255507 := bstep (se 1 (by rfl) ⟨3191630, by rfl⟩ : syracuseStep 4255507 = 6383261) B6383261
theorem B5674009 : Blo 2241435 5674009 := bstep (se 2 (by rfl) ⟨2127753, by rfl⟩ : syracuseStep 5674009 = 4255507) B4255507
theorem B7565345 : Blo 2241435 7565345 := bstep (se 2 (by rfl) ⟨2837004, by rfl⟩ : syracuseStep 7565345 = 5674009) B5674009
theorem B5043563 : Blo 2241435 5043563 := bstep (se 1 (by rfl) ⟨3782672, by rfl⟩ : syracuseStep 5043563 = 7565345) B7565345
theorem B3362375 : Blo 2241435 3362375 := bstep (se 1 (by rfl) ⟨2521781, by rfl⟩ : syracuseStep 3362375 = 5043563) B5043563
theorem B2241583 : Blo 2241435 2241583 := bstep (se 1 (by rfl) ⟨1681187, by rfl⟩ : syracuseStep 2241583 = 3362375) B3362375
theorem B3362381 : Blo 2241435 3362381 := bbase (se 3 (by rfl) ⟨630446, by rfl⟩ : syracuseStep 3362381 = 1260893) (by norm_num)
theorem B2241587 : Blo 2241435 2241587 := bstep (se 1 (by rfl) ⟨1681190, by rfl⟩ : syracuseStep 2241587 = 3362381) B3362381
theorem B5043581 : Blo 2241435 5043581 := bbase (se 3 (by rfl) ⟨945671, by rfl⟩ : syracuseStep 5043581 = 1891343) (by norm_num)
theorem B3362387 : Blo 2241435 3362387 := bstep (se 1 (by rfl) ⟨2521790, by rfl⟩ : syracuseStep 3362387 = 5043581) B5043581
theorem B2241591 : Blo 2241435 2241591 := bstep (se 1 (by rfl) ⟨1681193, by rfl⟩ : syracuseStep 2241591 = 3362387) B3362387
theorem B3782693 : Blo 2241435 3782693 := bbase (se 4 (by rfl) ⟨354627, by rfl⟩ : syracuseStep 3782693 = 709255) (by norm_num)
theorem B2521795 : Blo 2241435 2521795 := bstep (se 1 (by rfl) ⟨1891346, by rfl⟩ : syracuseStep 2521795 = 3782693) B3782693
theorem B3362393 : Blo 2241435 3362393 := bstep (se 2 (by rfl) ⟨1260897, by rfl⟩ : syracuseStep 3362393 = 2521795) B2521795
theorem B2241595 : Blo 2241435 2241595 := bstep (se 1 (by rfl) ⟨1681196, by rfl⟩ : syracuseStep 2241595 = 3362393) B3362393
theorem B3191653 : Blo 2241435 3191653 := bbase (se 4 (by rfl) ⟨299217, by rfl⟩ : syracuseStep 3191653 = 598435) (by norm_num)
theorem B17022149 : Blo 2241435 17022149 := bstep (se 4 (by rfl) ⟨1595826, by rfl⟩ : syracuseStep 17022149 = 3191653) B3191653
theorem B11348099 : Blo 2241435 11348099 := bstep (se 1 (by rfl) ⟨8511074, by rfl⟩ : syracuseStep 11348099 = 17022149) B17022149
theorem B7565399 : Blo 2241435 7565399 := bstep (se 1 (by rfl) ⟨5674049, by rfl⟩ : syracuseStep 7565399 = 11348099) B11348099
theorem B5043599 : Blo 2241435 5043599 := bstep (se 1 (by rfl) ⟨3782699, by rfl⟩ : syracuseStep 5043599 = 7565399) B7565399
theorem B3362399 : Blo 2241435 3362399 := bstep (se 1 (by rfl) ⟨2521799, by rfl⟩ : syracuseStep 3362399 = 5043599) B5043599
theorem B2241599 : Blo 2241435 2241599 := bstep (se 1 (by rfl) ⟨1681199, by rfl⟩ : syracuseStep 2241599 = 3362399) B3362399
theorem B3362405 : Blo 2241435 3362405 := bbase (se 4 (by rfl) ⟨315225, by rfl⟩ : syracuseStep 3362405 = 630451) (by norm_num)
theorem B2241603 : Blo 2241435 2241603 := bstep (se 1 (by rfl) ⟨1681202, by rfl⟩ : syracuseStep 2241603 = 3362405) B3362405
theorem B2393749 : Blo 2241435 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B3191665 : Blo 2241435 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B4255553 : Blo 2241435 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B2837035 : Blo 2241435 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B3782713 : Blo 2241435 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B5043617 : Blo 2241435 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B3362411 : Blo 2241435 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B2241607 : Blo 2241435 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B2521813 : Blo 2241435 2521813 := bbase (se 7 (by rfl) ⟨29552, by rfl⟩ : syracuseStep 2521813 = 59105) (by norm_num)
theorem B3362417 : Blo 2241435 3362417 := bstep (se 2 (by rfl) ⟨1260906, by rfl⟩ : syracuseStep 3362417 = 2521813) B2521813
theorem B2241611 : Blo 2241435 2241611 := bstep (se 1 (by rfl) ⟨1681208, by rfl⟩ : syracuseStep 2241611 = 3362417) B3362417
theorem B2837045 : Blo 2241435 2837045 := bbase (se 5 (by rfl) ⟨132986, by rfl⟩ : syracuseStep 2837045 = 265973) (by norm_num)
theorem B7565453 : Blo 2241435 7565453 := bstep (se 3 (by rfl) ⟨1418522, by rfl⟩ : syracuseStep 7565453 = 2837045) B2837045
theorem B5043635 : Blo 2241435 5043635 := bstep (se 1 (by rfl) ⟨3782726, by rfl⟩ : syracuseStep 5043635 = 7565453) B7565453
theorem B3362423 : Blo 2241435 3362423 := bstep (se 1 (by rfl) ⟨2521817, by rfl⟩ : syracuseStep 3362423 = 5043635) B5043635
theorem B2241615 : Blo 2241435 2241615 := bstep (se 1 (by rfl) ⟨1681211, by rfl⟩ : syracuseStep 2241615 = 3362423) B3362423
theorem B3362429 : Blo 2241435 3362429 := bbase (se 3 (by rfl) ⟨630455, by rfl⟩ : syracuseStep 3362429 = 1260911) (by norm_num)
theorem B2241619 : Blo 2241435 2241619 := bstep (se 1 (by rfl) ⟨1681214, by rfl⟩ : syracuseStep 2241619 = 3362429) B3362429
theorem B5043653 : Blo 2241435 5043653 := bbase (se 4 (by rfl) ⟨472842, by rfl⟩ : syracuseStep 5043653 = 945685) (by norm_num)
theorem B3362435 : Blo 2241435 3362435 := bstep (se 1 (by rfl) ⟨2521826, by rfl⟩ : syracuseStep 3362435 = 5043653) B5043653
theorem B2241623 : Blo 2241435 2241623 := bstep (se 1 (by rfl) ⟨1681217, by rfl⟩ : syracuseStep 2241623 = 3362435) B3362435
theorem B5609453 : Blo 2241435 5609453 := bbase (se 3 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 5609453 = 2103545) (by norm_num)
theorem B14958541 : Blo 2241435 14958541 := bstep (se 3 (by rfl) ⟨2804726, by rfl⟩ : syracuseStep 14958541 = 5609453) B5609453
theorem B19944721 : Blo 2241435 19944721 := bstep (se 2 (by rfl) ⟨7479270, by rfl⟩ : syracuseStep 19944721 = 14958541) B14958541
theorem B26592961 : Blo 2241435 26592961 := bstep (se 2 (by rfl) ⟨9972360, by rfl⟩ : syracuseStep 26592961 = 19944721) B19944721
theorem B35457281 : Blo 2241435 35457281 := bstep (se 2 (by rfl) ⟨13296480, by rfl⟩ : syracuseStep 35457281 = 26592961) B26592961
theorem B378210997 : Blo 2241435 378210997 := bstep (se 5 (by rfl) ⟨17728640, by rfl⟩ : syracuseStep 378210997 = 35457281) B35457281
theorem B2017125317 : Blo 2241435 2017125317 := bstep (se 4 (by rfl) ⟨189105498, by rfl⟩ : syracuseStep 2017125317 = 378210997) B378210997
theorem B1344750211 : Blo 2241435 1344750211 := bstep (se 1 (by rfl) ⟨1008562658, by rfl⟩ : syracuseStep 1344750211 = 2017125317) B2017125317
theorem B1793000281 : Blo 2241435 1793000281 := bstep (se 2 (by rfl) ⟨672375105, by rfl⟩ : syracuseStep 1793000281 = 1344750211) B1344750211
theorem B2390667041 : Blo 2241435 2390667041 := bstep (se 2 (by rfl) ⟨896500140, by rfl⟩ : syracuseStep 2390667041 = 1793000281) B1793000281
theorem B1593778027 : Blo 2241435 1593778027 := bstep (se 1 (by rfl) ⟨1195333520, by rfl⟩ : syracuseStep 1593778027 = 2390667041) B2390667041
theorem B2125037369 : Blo 2241435 2125037369 := bstep (se 2 (by rfl) ⟨796889013, by rfl⟩ : syracuseStep 2125037369 = 1593778027) B1593778027
theorem B1416691579 : Blo 2241435 1416691579 := bstep (se 1 (by rfl) ⟨1062518684, by rfl⟩ : syracuseStep 1416691579 = 2125037369) B2125037369
theorem B1888922105 : Blo 2241435 1888922105 := bstep (se 2 (by rfl) ⟨708345789, by rfl⟩ : syracuseStep 1888922105 = 1416691579) B1416691579
theorem B1259281403 : Blo 2241435 1259281403 := bstep (se 1 (by rfl) ⟨944461052, by rfl⟩ : syracuseStep 1259281403 = 1888922105) B1888922105
theorem B839520935 : Blo 2241435 839520935 := bstep (se 1 (by rfl) ⟨629640701, by rfl⟩ : syracuseStep 839520935 = 1259281403) B1259281403
theorem B559680623 : Blo 2241435 559680623 := bstep (se 1 (by rfl) ⟨419760467, by rfl⟩ : syracuseStep 559680623 = 839520935) B839520935
theorem B373120415 : Blo 2241435 373120415 := bstep (se 1 (by rfl) ⟨279840311, by rfl⟩ : syracuseStep 373120415 = 559680623) B559680623
theorem B248746943 : Blo 2241435 248746943 := bstep (se 1 (by rfl) ⟨186560207, by rfl⟩ : syracuseStep 248746943 = 373120415) B373120415
theorem B165831295 : Blo 2241435 165831295 := bstep (se 1 (by rfl) ⟨124373471, by rfl⟩ : syracuseStep 165831295 = 248746943) B248746943
theorem B221108393 : Blo 2241435 221108393 := bstep (se 2 (by rfl) ⟨82915647, by rfl⟩ : syracuseStep 221108393 = 165831295) B165831295
theorem B147405595 : Blo 2241435 147405595 := bstep (se 1 (by rfl) ⟨110554196, by rfl⟩ : syracuseStep 147405595 = 221108393) B221108393
theorem B196540793 : Blo 2241435 196540793 := bstep (se 2 (by rfl) ⟨73702797, by rfl⟩ : syracuseStep 196540793 = 147405595) B147405595
theorem B131027195 : Blo 2241435 131027195 := bstep (se 1 (by rfl) ⟨98270396, by rfl⟩ : syracuseStep 131027195 = 196540793) B196540793
theorem B87351463 : Blo 2241435 87351463 := bstep (se 1 (by rfl) ⟨65513597, by rfl⟩ : syracuseStep 87351463 = 131027195) B131027195
theorem B116468617 : Blo 2241435 116468617 := bstep (se 2 (by rfl) ⟨43675731, by rfl⟩ : syracuseStep 116468617 = 87351463) B87351463
theorem B155291489 : Blo 2241435 155291489 := bstep (se 2 (by rfl) ⟨58234308, by rfl⟩ : syracuseStep 155291489 = 116468617) B116468617
theorem B103527659 : Blo 2241435 103527659 := bstep (se 1 (by rfl) ⟨77645744, by rfl⟩ : syracuseStep 103527659 = 155291489) B155291489
theorem B276073757 : Blo 2241435 276073757 := bstep (se 3 (by rfl) ⟨51763829, by rfl⟩ : syracuseStep 276073757 = 103527659) B103527659
theorem B184049171 : Blo 2241435 184049171 := bstep (se 1 (by rfl) ⟨138036878, by rfl⟩ : syracuseStep 184049171 = 276073757) B276073757
theorem B122699447 : Blo 2241435 122699447 := bstep (se 1 (by rfl) ⟨92024585, by rfl⟩ : syracuseStep 122699447 = 184049171) B184049171
theorem B81799631 : Blo 2241435 81799631 := bstep (se 1 (by rfl) ⟨61349723, by rfl⟩ : syracuseStep 81799631 = 122699447) B122699447
theorem B54533087 : Blo 2241435 54533087 := bstep (se 1 (by rfl) ⟨40899815, by rfl⟩ : syracuseStep 54533087 = 81799631) B81799631
theorem B36355391 : Blo 2241435 36355391 := bstep (se 1 (by rfl) ⟨27266543, by rfl⟩ : syracuseStep 36355391 = 54533087) B54533087
theorem B24236927 : Blo 2241435 24236927 := bstep (se 1 (by rfl) ⟨18177695, by rfl⟩ : syracuseStep 24236927 = 36355391) B36355391
theorem B16157951 : Blo 2241435 16157951 := bstep (se 1 (by rfl) ⟨12118463, by rfl⟩ : syracuseStep 16157951 = 24236927) B24236927
theorem B10771967 : Blo 2241435 10771967 := bstep (se 1 (by rfl) ⟨8078975, by rfl⟩ : syracuseStep 10771967 = 16157951) B16157951
theorem B7181311 : Blo 2241435 7181311 := bstep (se 1 (by rfl) ⟨5385983, by rfl⟩ : syracuseStep 7181311 = 10771967) B10771967
theorem B9575081 : Blo 2241435 9575081 := bstep (se 2 (by rfl) ⟨3590655, by rfl⟩ : syracuseStep 9575081 = 7181311) B7181311
theorem B6383387 : Blo 2241435 6383387 := bstep (se 1 (by rfl) ⟨4787540, by rfl⟩ : syracuseStep 6383387 = 9575081) B9575081
theorem B4255591 : Blo 2241435 4255591 := bstep (se 1 (by rfl) ⟨3191693, by rfl⟩ : syracuseStep 4255591 = 6383387) B6383387
theorem B5674121 : Blo 2241435 5674121 := bstep (se 2 (by rfl) ⟨2127795, by rfl⟩ : syracuseStep 5674121 = 4255591) B4255591
theorem B3782747 : Blo 2241435 3782747 := bstep (se 1 (by rfl) ⟨2837060, by rfl⟩ : syracuseStep 3782747 = 5674121) B5674121
theorem B2521831 : Blo 2241435 2521831 := bstep (se 1 (by rfl) ⟨1891373, by rfl⟩ : syracuseStep 2521831 = 3782747) B3782747
theorem B3362441 : Blo 2241435 3362441 := bstep (se 2 (by rfl) ⟨1260915, by rfl⟩ : syracuseStep 3362441 = 2521831) B2521831
theorem B2241627 : Blo 2241435 2241627 := bstep (se 1 (by rfl) ⟨1681220, by rfl⟩ : syracuseStep 2241627 = 3362441) B3362441
theorem B11348261 : Blo 2241435 11348261 := bbase (se 4 (by rfl) ⟨1063899, by rfl⟩ : syracuseStep 11348261 = 2127799) (by norm_num)
theorem B7565507 : Blo 2241435 7565507 := bstep (se 1 (by rfl) ⟨5674130, by rfl⟩ : syracuseStep 7565507 = 11348261) B11348261
theorem B5043671 : Blo 2241435 5043671 := bstep (se 1 (by rfl) ⟨3782753, by rfl⟩ : syracuseStep 5043671 = 7565507) B7565507
theorem B3362447 : Blo 2241435 3362447 := bstep (se 1 (by rfl) ⟨2521835, by rfl⟩ : syracuseStep 3362447 = 5043671) B5043671
theorem B2241631 : Blo 2241435 2241631 := bstep (se 1 (by rfl) ⟨1681223, by rfl⟩ : syracuseStep 2241631 = 3362447) B3362447
theorem B3362453 : Blo 2241435 3362453 := bbase (se 6 (by rfl) ⟨78807, by rfl⟩ : syracuseStep 3362453 = 157615) (by norm_num)
theorem B2241635 : Blo 2241435 2241635 := bstep (se 1 (by rfl) ⟨1681226, by rfl⟩ : syracuseStep 2241635 = 3362453) B3362453
theorem B13819349 : Blo 2241435 13819349 := bbase (se 7 (by rfl) ⟨161945, by rfl⟩ : syracuseStep 13819349 = 323891) (by norm_num)
theorem B36851597 : Blo 2241435 36851597 := bstep (se 3 (by rfl) ⟨6909674, by rfl⟩ : syracuseStep 36851597 = 13819349) B13819349
theorem B24567731 : Blo 2241435 24567731 := bstep (se 1 (by rfl) ⟨18425798, by rfl⟩ : syracuseStep 24567731 = 36851597) B36851597
theorem B16378487 : Blo 2241435 16378487 := bstep (se 1 (by rfl) ⟨12283865, by rfl⟩ : syracuseStep 16378487 = 24567731) B24567731
theorem B10918991 : Blo 2241435 10918991 := bstep (se 1 (by rfl) ⟨8189243, by rfl⟩ : syracuseStep 10918991 = 16378487) B16378487
theorem B7279327 : Blo 2241435 7279327 := bstep (se 1 (by rfl) ⟨5459495, by rfl⟩ : syracuseStep 7279327 = 10918991) B10918991
theorem B38823077 : Blo 2241435 38823077 := bstep (se 4 (by rfl) ⟨3639663, by rfl⟩ : syracuseStep 38823077 = 7279327) B7279327
theorem B103528205 : Blo 2241435 103528205 := bstep (se 3 (by rfl) ⟨19411538, by rfl⟩ : syracuseStep 103528205 = 38823077) B38823077
theorem B69018803 : Blo 2241435 69018803 := bstep (se 1 (by rfl) ⟨51764102, by rfl⟩ : syracuseStep 69018803 = 103528205) B103528205
theorem B46012535 : Blo 2241435 46012535 := bstep (se 1 (by rfl) ⟨34509401, by rfl⟩ : syracuseStep 46012535 = 69018803) B69018803
theorem B30675023 : Blo 2241435 30675023 := bstep (se 1 (by rfl) ⟨23006267, by rfl⟩ : syracuseStep 30675023 = 46012535) B46012535
theorem B20450015 : Blo 2241435 20450015 := bstep (se 1 (by rfl) ⟨15337511, by rfl⟩ : syracuseStep 20450015 = 30675023) B30675023
theorem B13633343 : Blo 2241435 13633343 := bstep (se 1 (by rfl) ⟨10225007, by rfl⟩ : syracuseStep 13633343 = 20450015) B20450015
theorem B9088895 : Blo 2241435 9088895 := bstep (se 1 (by rfl) ⟨6816671, by rfl⟩ : syracuseStep 9088895 = 13633343) B13633343
theorem B24237053 : Blo 2241435 24237053 := bstep (se 3 (by rfl) ⟨4544447, by rfl⟩ : syracuseStep 24237053 = 9088895) B9088895
theorem B16158035 : Blo 2241435 16158035 := bstep (se 1 (by rfl) ⟨12118526, by rfl⟩ : syracuseStep 16158035 = 24237053) B24237053
theorem B10772023 : Blo 2241435 10772023 := bstep (se 1 (by rfl) ⟨8079017, by rfl⟩ : syracuseStep 10772023 = 16158035) B16158035
theorem B14362697 : Blo 2241435 14362697 := bstep (se 2 (by rfl) ⟨5386011, by rfl⟩ : syracuseStep 14362697 = 10772023) B10772023
theorem B9575131 : Blo 2241435 9575131 := bstep (se 1 (by rfl) ⟨7181348, by rfl⟩ : syracuseStep 9575131 = 14362697) B14362697
theorem B12766841 : Blo 2241435 12766841 := bstep (se 2 (by rfl) ⟨4787565, by rfl⟩ : syracuseStep 12766841 = 9575131) B9575131
theorem B8511227 : Blo 2241435 8511227 := bstep (se 1 (by rfl) ⟨6383420, by rfl⟩ : syracuseStep 8511227 = 12766841) B12766841
theorem B5674151 : Blo 2241435 5674151 := bstep (se 1 (by rfl) ⟨4255613, by rfl⟩ : syracuseStep 5674151 = 8511227) B8511227
theorem B3782767 : Blo 2241435 3782767 := bstep (se 1 (by rfl) ⟨2837075, by rfl⟩ : syracuseStep 3782767 = 5674151) B5674151
theorem B5043689 : Blo 2241435 5043689 := bstep (se 2 (by rfl) ⟨1891383, by rfl⟩ : syracuseStep 5043689 = 3782767) B3782767
theorem B3362459 : Blo 2241435 3362459 := bstep (se 1 (by rfl) ⟨2521844, by rfl⟩ : syracuseStep 3362459 = 5043689) B5043689
theorem B2241639 : Blo 2241435 2241639 := bstep (se 1 (by rfl) ⟨1681229, by rfl⟩ : syracuseStep 2241639 = 3362459) B3362459
theorem B2521849 : Blo 2241435 2521849 := bbase (se 2 (by rfl) ⟨945693, by rfl⟩ : syracuseStep 2521849 = 1891387) (by norm_num)
theorem B3362465 : Blo 2241435 3362465 := bstep (se 2 (by rfl) ⟨1260924, by rfl⟩ : syracuseStep 3362465 = 2521849) B2521849
theorem B2241643 : Blo 2241435 2241643 := bstep (se 1 (by rfl) ⟨1681232, by rfl⟩ : syracuseStep 2241643 = 3362465) B3362465
theorem B10225045 : Blo 2241435 10225045 := bbase (se 6 (by rfl) ⟨239649, by rfl⟩ : syracuseStep 10225045 = 479299) (by norm_num)
theorem B13633393 : Blo 2241435 13633393 := bstep (se 2 (by rfl) ⟨5112522, by rfl⟩ : syracuseStep 13633393 = 10225045) B10225045
theorem B18177857 : Blo 2241435 18177857 := bstep (se 2 (by rfl) ⟨6816696, by rfl⟩ : syracuseStep 18177857 = 13633393) B13633393
theorem B12118571 : Blo 2241435 12118571 := bstep (se 1 (by rfl) ⟨9088928, by rfl⟩ : syracuseStep 12118571 = 18177857) B18177857
theorem B8079047 : Blo 2241435 8079047 := bstep (se 1 (by rfl) ⟨6059285, by rfl⟩ : syracuseStep 8079047 = 12118571) B12118571
theorem B5386031 : Blo 2241435 5386031 := bstep (se 1 (by rfl) ⟨4039523, by rfl⟩ : syracuseStep 5386031 = 8079047) B8079047
theorem B3590687 : Blo 2241435 3590687 := bstep (se 1 (by rfl) ⟨2693015, by rfl⟩ : syracuseStep 3590687 = 5386031) B5386031
theorem B9575165 : Blo 2241435 9575165 := bstep (se 3 (by rfl) ⟨1795343, by rfl⟩ : syracuseStep 9575165 = 3590687) B3590687
theorem B6383443 : Blo 2241435 6383443 := bstep (se 1 (by rfl) ⟨4787582, by rfl⟩ : syracuseStep 6383443 = 9575165) B9575165
theorem B8511257 : Blo 2241435 8511257 := bstep (se 2 (by rfl) ⟨3191721, by rfl⟩ : syracuseStep 8511257 = 6383443) B6383443
theorem B5674171 : Blo 2241435 5674171 := bstep (se 1 (by rfl) ⟨4255628, by rfl⟩ : syracuseStep 5674171 = 8511257) B8511257
theorem B7565561 : Blo 2241435 7565561 := bstep (se 2 (by rfl) ⟨2837085, by rfl⟩ : syracuseStep 7565561 = 5674171) B5674171
theorem B5043707 : Blo 2241435 5043707 := bstep (se 1 (by rfl) ⟨3782780, by rfl⟩ : syracuseStep 5043707 = 7565561) B7565561
theorem B3362471 : Blo 2241435 3362471 := bstep (se 1 (by rfl) ⟨2521853, by rfl⟩ : syracuseStep 3362471 = 5043707) B5043707
theorem B2241647 : Blo 2241435 2241647 := bstep (se 1 (by rfl) ⟨1681235, by rfl⟩ : syracuseStep 2241647 = 3362471) B3362471
theorem B3362477 : Blo 2241435 3362477 := bbase (se 3 (by rfl) ⟨630464, by rfl⟩ : syracuseStep 3362477 = 1260929) (by norm_num)
theorem B2241651 : Blo 2241435 2241651 := bstep (se 1 (by rfl) ⟨1681238, by rfl⟩ : syracuseStep 2241651 = 3362477) B3362477
theorem B5043725 : Blo 2241435 5043725 := bbase (se 3 (by rfl) ⟨945698, by rfl⟩ : syracuseStep 5043725 = 1891397) (by norm_num)
theorem B3362483 : Blo 2241435 3362483 := bstep (se 1 (by rfl) ⟨2521862, by rfl⟩ : syracuseStep 3362483 = 5043725) B5043725
theorem B2241655 : Blo 2241435 2241655 := bstep (se 1 (by rfl) ⟨1681241, by rfl⟩ : syracuseStep 2241655 = 3362483) B3362483
theorem B2837101 : Blo 2241435 2837101 := bbase (se 3 (by rfl) ⟨531956, by rfl⟩ : syracuseStep 2837101 = 1063913) (by norm_num)
theorem B3782801 : Blo 2241435 3782801 := bstep (se 2 (by rfl) ⟨1418550, by rfl⟩ : syracuseStep 3782801 = 2837101) B2837101
theorem B2521867 : Blo 2241435 2521867 := bstep (se 1 (by rfl) ⟨1891400, by rfl⟩ : syracuseStep 2521867 = 3782801) B3782801
theorem B3362489 : Blo 2241435 3362489 := bstep (se 2 (by rfl) ⟨1260933, by rfl⟩ : syracuseStep 3362489 = 2521867) B2521867
theorem B2241659 : Blo 2241435 2241659 := bstep (se 1 (by rfl) ⟨1681244, by rfl⟩ : syracuseStep 2241659 = 3362489) B3362489
theorem B6225797 : Blo 2241435 6225797 := bbase (se 4 (by rfl) ⟨583668, by rfl⟩ : syracuseStep 6225797 = 1167337) (by norm_num)
theorem B4150531 : Blo 2241435 4150531 := bstep (se 1 (by rfl) ⟨3112898, by rfl⟩ : syracuseStep 4150531 = 6225797) B6225797
theorem B5534041 : Blo 2241435 5534041 := bstep (se 2 (by rfl) ⟨2075265, by rfl⟩ : syracuseStep 5534041 = 4150531) B4150531
theorem B7378721 : Blo 2241435 7378721 := bstep (se 2 (by rfl) ⟨2767020, by rfl⟩ : syracuseStep 7378721 = 5534041) B5534041
theorem B4919147 : Blo 2241435 4919147 := bstep (se 1 (by rfl) ⟨3689360, by rfl⟩ : syracuseStep 4919147 = 7378721) B7378721
theorem B3279431 : Blo 2241435 3279431 := bstep (se 1 (by rfl) ⟨2459573, by rfl⟩ : syracuseStep 3279431 = 4919147) B4919147
theorem B8745149 : Blo 2241435 8745149 := bstep (se 3 (by rfl) ⟨1639715, by rfl⟩ : syracuseStep 8745149 = 3279431) B3279431
theorem B5830099 : Blo 2241435 5830099 := bstep (se 1 (by rfl) ⟨4372574, by rfl⟩ : syracuseStep 5830099 = 8745149) B8745149
theorem B31093861 : Blo 2241435 31093861 := bstep (se 4 (by rfl) ⟨2915049, by rfl⟩ : syracuseStep 31093861 = 5830099) B5830099
theorem B41458481 : Blo 2241435 41458481 := bstep (se 2 (by rfl) ⟨15546930, by rfl⟩ : syracuseStep 41458481 = 31093861) B31093861
theorem B27638987 : Blo 2241435 27638987 := bstep (se 1 (by rfl) ⟨20729240, by rfl⟩ : syracuseStep 27638987 = 41458481) B41458481
theorem B294815861 : Blo 2241435 294815861 := bstep (se 5 (by rfl) ⟨13819493, by rfl⟩ : syracuseStep 294815861 = 27638987) B27638987
theorem B196543907 : Blo 2241435 196543907 := bstep (se 1 (by rfl) ⟨147407930, by rfl⟩ : syracuseStep 196543907 = 294815861) B294815861
theorem B131029271 : Blo 2241435 131029271 := bstep (se 1 (by rfl) ⟨98271953, by rfl⟩ : syracuseStep 131029271 = 196543907) B196543907
theorem B87352847 : Blo 2241435 87352847 := bstep (se 1 (by rfl) ⟨65514635, by rfl⟩ : syracuseStep 87352847 = 131029271) B131029271
theorem B58235231 : Blo 2241435 58235231 := bstep (se 1 (by rfl) ⟨43676423, by rfl⟩ : syracuseStep 58235231 = 87352847) B87352847
theorem B155293949 : Blo 2241435 155293949 := bstep (se 3 (by rfl) ⟨29117615, by rfl⟩ : syracuseStep 155293949 = 58235231) B58235231
theorem B103529299 : Blo 2241435 103529299 := bstep (se 1 (by rfl) ⟨77646974, by rfl⟩ : syracuseStep 103529299 = 155293949) B155293949
theorem B138039065 : Blo 2241435 138039065 := bstep (se 2 (by rfl) ⟨51764649, by rfl⟩ : syracuseStep 138039065 = 103529299) B103529299
theorem B92026043 : Blo 2241435 92026043 := bstep (se 1 (by rfl) ⟨69019532, by rfl⟩ : syracuseStep 92026043 = 138039065) B138039065
theorem B61350695 : Blo 2241435 61350695 := bstep (se 1 (by rfl) ⟨46013021, by rfl⟩ : syracuseStep 61350695 = 92026043) B92026043
theorem B40900463 : Blo 2241435 40900463 := bstep (se 1 (by rfl) ⟨30675347, by rfl⟩ : syracuseStep 40900463 = 61350695) B61350695
theorem B27266975 : Blo 2241435 27266975 := bstep (se 1 (by rfl) ⟨20450231, by rfl⟩ : syracuseStep 27266975 = 40900463) B40900463
theorem B18177983 : Blo 2241435 18177983 := bstep (se 1 (by rfl) ⟨13633487, by rfl⟩ : syracuseStep 18177983 = 27266975) B27266975
theorem B12118655 : Blo 2241435 12118655 := bstep (se 1 (by rfl) ⟨9088991, by rfl⟩ : syracuseStep 12118655 = 18177983) B18177983
theorem B8079103 : Blo 2241435 8079103 := bstep (se 1 (by rfl) ⟨6059327, by rfl⟩ : syracuseStep 8079103 = 12118655) B12118655
theorem B10772137 : Blo 2241435 10772137 := bstep (se 2 (by rfl) ⟨4039551, by rfl⟩ : syracuseStep 10772137 = 8079103) B8079103
theorem B14362849 : Blo 2241435 14362849 := bstep (se 2 (by rfl) ⟨5386068, by rfl⟩ : syracuseStep 14362849 = 10772137) B10772137
theorem B19150465 : Blo 2241435 19150465 := bstep (se 2 (by rfl) ⟨7181424, by rfl⟩ : syracuseStep 19150465 = 14362849) B14362849
theorem B25533953 : Blo 2241435 25533953 := bstep (se 2 (by rfl) ⟨9575232, by rfl⟩ : syracuseStep 25533953 = 19150465) B19150465
theorem B17022635 : Blo 2241435 17022635 := bstep (se 1 (by rfl) ⟨12766976, by rfl⟩ : syracuseStep 17022635 = 25533953) B25533953
theorem B11348423 : Blo 2241435 11348423 := bstep (se 1 (by rfl) ⟨8511317, by rfl⟩ : syracuseStep 11348423 = 17022635) B17022635
theorem B7565615 : Blo 2241435 7565615 := bstep (se 1 (by rfl) ⟨5674211, by rfl⟩ : syracuseStep 7565615 = 11348423) B11348423
theorem B5043743 : Blo 2241435 5043743 := bstep (se 1 (by rfl) ⟨3782807, by rfl⟩ : syracuseStep 5043743 = 7565615) B7565615
theorem B3362495 : Blo 2241435 3362495 := bstep (se 1 (by rfl) ⟨2521871, by rfl⟩ : syracuseStep 3362495 = 5043743) B5043743
theorem B2241663 : Blo 2241435 2241663 := bstep (se 1 (by rfl) ⟨1681247, by rfl⟩ : syracuseStep 2241663 = 3362495) B3362495
theorem B3362501 : Blo 2241435 3362501 := bbase (se 4 (by rfl) ⟨315234, by rfl⟩ : syracuseStep 3362501 = 630469) (by norm_num)
theorem B2241667 : Blo 2241435 2241667 := bstep (se 1 (by rfl) ⟨1681250, by rfl⟩ : syracuseStep 2241667 = 3362501) B3362501
theorem B3782821 : Blo 2241435 3782821 := bbase (se 4 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 3782821 = 709279) (by norm_num)
theorem B5043761 : Blo 2241435 5043761 := bstep (se 2 (by rfl) ⟨1891410, by rfl⟩ : syracuseStep 5043761 = 3782821) B3782821
theorem B3362507 : Blo 2241435 3362507 := bstep (se 1 (by rfl) ⟨2521880, by rfl⟩ : syracuseStep 3362507 = 5043761) B5043761
theorem B2241671 : Blo 2241435 2241671 := bstep (se 1 (by rfl) ⟨1681253, by rfl⟩ : syracuseStep 2241671 = 3362507) B3362507
theorem B2521885 : Blo 2241435 2521885 := bbase (se 3 (by rfl) ⟨472853, by rfl⟩ : syracuseStep 2521885 = 945707) (by norm_num)
theorem B3362513 : Blo 2241435 3362513 := bstep (se 2 (by rfl) ⟨1260942, by rfl⟩ : syracuseStep 3362513 = 2521885) B2521885
theorem B2241675 : Blo 2241435 2241675 := bstep (se 1 (by rfl) ⟨1681256, by rfl⟩ : syracuseStep 2241675 = 3362513) B3362513
theorem B7565669 : Blo 2241435 7565669 := bbase (se 4 (by rfl) ⟨709281, by rfl⟩ : syracuseStep 7565669 = 1418563) (by norm_num)
theorem B5043779 : Blo 2241435 5043779 := bstep (se 1 (by rfl) ⟨3782834, by rfl⟩ : syracuseStep 5043779 = 7565669) B7565669
theorem B3362519 : Blo 2241435 3362519 := bstep (se 1 (by rfl) ⟨2521889, by rfl⟩ : syracuseStep 3362519 = 5043779) B5043779
theorem B2241679 : Blo 2241435 2241679 := bstep (se 1 (by rfl) ⟨1681259, by rfl⟩ : syracuseStep 2241679 = 3362519) B3362519
theorem B3362525 : Blo 2241435 3362525 := bbase (se 3 (by rfl) ⟨630473, by rfl⟩ : syracuseStep 3362525 = 1260947) (by norm_num)
theorem B2241683 : Blo 2241435 2241683 := bstep (se 1 (by rfl) ⟨1681262, by rfl⟩ : syracuseStep 2241683 = 3362525) B3362525
theorem B5043797 : Blo 2241435 5043797 := bbase (se 8 (by rfl) ⟨29553, by rfl⟩ : syracuseStep 5043797 = 59107) (by norm_num)
theorem B3362531 : Blo 2241435 3362531 := bstep (se 1 (by rfl) ⟨2521898, by rfl⟩ : syracuseStep 3362531 = 5043797) B5043797
theorem B2241687 : Blo 2241435 2241687 := bstep (se 1 (by rfl) ⟨1681265, by rfl⟩ : syracuseStep 2241687 = 3362531) B3362531
theorem B4787677 : Blo 2241435 4787677 := bbase (se 3 (by rfl) ⟨897689, by rfl⟩ : syracuseStep 4787677 = 1795379) (by norm_num)
theorem B6383569 : Blo 2241435 6383569 := bstep (se 2 (by rfl) ⟨2393838, by rfl⟩ : syracuseStep 6383569 = 4787677) B4787677
theorem B8511425 : Blo 2241435 8511425 := bstep (se 2 (by rfl) ⟨3191784, by rfl⟩ : syracuseStep 8511425 = 6383569) B6383569
theorem B5674283 : Blo 2241435 5674283 := bstep (se 1 (by rfl) ⟨4255712, by rfl⟩ : syracuseStep 5674283 = 8511425) B8511425
theorem B3782855 : Blo 2241435 3782855 := bstep (se 1 (by rfl) ⟨2837141, by rfl⟩ : syracuseStep 3782855 = 5674283) B5674283
theorem B2521903 : Blo 2241435 2521903 := bstep (se 1 (by rfl) ⟨1891427, by rfl⟩ : syracuseStep 2521903 = 3782855) B3782855
theorem B3362537 : Blo 2241435 3362537 := bstep (se 2 (by rfl) ⟨1260951, by rfl⟩ : syracuseStep 3362537 = 2521903) B2521903
theorem B2241691 : Blo 2241435 2241691 := bstep (se 1 (by rfl) ⟨1681268, by rfl⟩ : syracuseStep 2241691 = 3362537) B3362537
theorem B3408421 : Blo 2241435 3408421 := bbase (se 4 (by rfl) ⟨319539, by rfl⟩ : syracuseStep 3408421 = 639079) (by norm_num)
theorem B4544561 : Blo 2241435 4544561 := bstep (se 2 (by rfl) ⟨1704210, by rfl⟩ : syracuseStep 4544561 = 3408421) B3408421
theorem B3029707 : Blo 2241435 3029707 := bstep (se 1 (by rfl) ⟨2272280, by rfl⟩ : syracuseStep 3029707 = 4544561) B4544561
theorem B16158437 : Blo 2241435 16158437 := bstep (se 4 (by rfl) ⟨1514853, by rfl⟩ : syracuseStep 16158437 = 3029707) B3029707
theorem B10772291 : Blo 2241435 10772291 := bstep (se 1 (by rfl) ⟨8079218, by rfl⟩ : syracuseStep 10772291 = 16158437) B16158437
theorem B28726109 : Blo 2241435 28726109 := bstep (se 3 (by rfl) ⟨5386145, by rfl⟩ : syracuseStep 28726109 = 10772291) B10772291
theorem B19150739 : Blo 2241435 19150739 := bstep (se 1 (by rfl) ⟨14363054, by rfl⟩ : syracuseStep 19150739 = 28726109) B28726109
theorem B12767159 : Blo 2241435 12767159 := bstep (se 1 (by rfl) ⟨9575369, by rfl⟩ : syracuseStep 12767159 = 19150739) B19150739
theorem B8511439 : Blo 2241435 8511439 := bstep (se 1 (by rfl) ⟨6383579, by rfl⟩ : syracuseStep 8511439 = 12767159) B12767159
theorem B11348585 : Blo 2241435 11348585 := bstep (se 2 (by rfl) ⟨4255719, by rfl⟩ : syracuseStep 11348585 = 8511439) B8511439
theorem B7565723 : Blo 2241435 7565723 := bstep (se 1 (by rfl) ⟨5674292, by rfl⟩ : syracuseStep 7565723 = 11348585) B11348585
theorem B5043815 : Blo 2241435 5043815 := bstep (se 1 (by rfl) ⟨3782861, by rfl⟩ : syracuseStep 5043815 = 7565723) B7565723
theorem B3362543 : Blo 2241435 3362543 := bstep (se 1 (by rfl) ⟨2521907, by rfl⟩ : syracuseStep 3362543 = 5043815) B5043815
theorem B2241695 : Blo 2241435 2241695 := bstep (se 1 (by rfl) ⟨1681271, by rfl⟩ : syracuseStep 2241695 = 3362543) B3362543
theorem B3362549 : Blo 2241435 3362549 := bbase (se 5 (by rfl) ⟨157619, by rfl⟩ : syracuseStep 3362549 = 315239) (by norm_num)
theorem B2241699 : Blo 2241435 2241699 := bstep (se 1 (by rfl) ⟨1681274, by rfl⟩ : syracuseStep 2241699 = 3362549) B3362549
theorem B6816869 : Blo 2241435 6816869 := bbase (se 4 (by rfl) ⟨639081, by rfl⟩ : syracuseStep 6816869 = 1278163) (by norm_num)
theorem B4544579 : Blo 2241435 4544579 := bstep (se 1 (by rfl) ⟨3408434, by rfl⟩ : syracuseStep 4544579 = 6816869) B6816869
theorem B3029719 : Blo 2241435 3029719 := bstep (se 1 (by rfl) ⟨2272289, by rfl⟩ : syracuseStep 3029719 = 4544579) B4544579
theorem B4039625 : Blo 2241435 4039625 := bstep (se 2 (by rfl) ⟨1514859, by rfl⟩ : syracuseStep 4039625 = 3029719) B3029719
theorem B2693083 : Blo 2241435 2693083 := bstep (se 1 (by rfl) ⟨2019812, by rfl⟩ : syracuseStep 2693083 = 4039625) B4039625
theorem B3590777 : Blo 2241435 3590777 := bstep (se 2 (by rfl) ⟨1346541, by rfl⟩ : syracuseStep 3590777 = 2693083) B2693083
theorem B9575405 : Blo 2241435 9575405 := bstep (se 3 (by rfl) ⟨1795388, by rfl⟩ : syracuseStep 9575405 = 3590777) B3590777
theorem B6383603 : Blo 2241435 6383603 := bstep (se 1 (by rfl) ⟨4787702, by rfl⟩ : syracuseStep 6383603 = 9575405) B9575405
theorem B4255735 : Blo 2241435 4255735 := bstep (se 1 (by rfl) ⟨3191801, by rfl⟩ : syracuseStep 4255735 = 6383603) B6383603
theorem B5674313 : Blo 2241435 5674313 := bstep (se 2 (by rfl) ⟨2127867, by rfl⟩ : syracuseStep 5674313 = 4255735) B4255735
theorem B3782875 : Blo 2241435 3782875 := bstep (se 1 (by rfl) ⟨2837156, by rfl⟩ : syracuseStep 3782875 = 5674313) B5674313
theorem B5043833 : Blo 2241435 5043833 := bstep (se 2 (by rfl) ⟨1891437, by rfl⟩ : syracuseStep 5043833 = 3782875) B3782875
theorem B3362555 : Blo 2241435 3362555 := bstep (se 1 (by rfl) ⟨2521916, by rfl⟩ : syracuseStep 3362555 = 5043833) B5043833
theorem B2241703 : Blo 2241435 2241703 := bstep (se 1 (by rfl) ⟨1681277, by rfl⟩ : syracuseStep 2241703 = 3362555) B3362555
theorem B2521921 : Blo 2241435 2521921 := bbase (se 2 (by rfl) ⟨945720, by rfl⟩ : syracuseStep 2521921 = 1891441) (by norm_num)
theorem B3362561 : Blo 2241435 3362561 := bstep (se 2 (by rfl) ⟨1260960, by rfl⟩ : syracuseStep 3362561 = 2521921) B2521921
theorem B2241707 : Blo 2241435 2241707 := bstep (se 1 (by rfl) ⟨1681280, by rfl⟩ : syracuseStep 2241707 = 3362561) B3362561
theorem B5674333 : Blo 2241435 5674333 := bbase (se 3 (by rfl) ⟨1063937, by rfl⟩ : syracuseStep 5674333 = 2127875) (by norm_num)
theorem B7565777 : Blo 2241435 7565777 := bstep (se 2 (by rfl) ⟨2837166, by rfl⟩ : syracuseStep 7565777 = 5674333) B5674333
theorem B5043851 : Blo 2241435 5043851 := bstep (se 1 (by rfl) ⟨3782888, by rfl⟩ : syracuseStep 5043851 = 7565777) B7565777
theorem B3362567 : Blo 2241435 3362567 := bstep (se 1 (by rfl) ⟨2521925, by rfl⟩ : syracuseStep 3362567 = 5043851) B5043851
theorem B2241711 : Blo 2241435 2241711 := bstep (se 1 (by rfl) ⟨1681283, by rfl⟩ : syracuseStep 2241711 = 3362567) B3362567
theorem B3362573 : Blo 2241435 3362573 := bbase (se 3 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 3362573 = 1260965) (by norm_num)
theorem B2241715 : Blo 2241435 2241715 := bstep (se 1 (by rfl) ⟨1681286, by rfl⟩ : syracuseStep 2241715 = 3362573) B3362573
theorem B5043869 : Blo 2241435 5043869 := bbase (se 3 (by rfl) ⟨945725, by rfl⟩ : syracuseStep 5043869 = 1891451) (by norm_num)
theorem B3362579 : Blo 2241435 3362579 := bstep (se 1 (by rfl) ⟨2521934, by rfl⟩ : syracuseStep 3362579 = 5043869) B5043869
theorem B2241719 : Blo 2241435 2241719 := bstep (se 1 (by rfl) ⟨1681289, by rfl⟩ : syracuseStep 2241719 = 3362579) B3362579
theorem B3782909 : Blo 2241435 3782909 := bbase (se 3 (by rfl) ⟨709295, by rfl⟩ : syracuseStep 3782909 = 1418591) (by norm_num)
theorem B2521939 : Blo 2241435 2521939 := bstep (se 1 (by rfl) ⟨1891454, by rfl⟩ : syracuseStep 2521939 = 3782909) B3782909
theorem B3362585 : Blo 2241435 3362585 := bstep (se 2 (by rfl) ⟨1260969, by rfl⟩ : syracuseStep 3362585 = 2521939) B2521939
theorem B2241723 : Blo 2241435 2241723 := bstep (se 1 (by rfl) ⟨1681292, by rfl⟩ : syracuseStep 2241723 = 3362585) B3362585
theorem B4313845 : Blo 2241435 4313845 := bbase (se 5 (by rfl) ⟨202211, by rfl⟩ : syracuseStep 4313845 = 404423) (by norm_num)
theorem B5751793 : Blo 2241435 5751793 := bstep (se 2 (by rfl) ⟨2156922, by rfl⟩ : syracuseStep 5751793 = 4313845) B4313845
theorem B30676229 : Blo 2241435 30676229 := bstep (se 4 (by rfl) ⟨2875896, by rfl⟩ : syracuseStep 30676229 = 5751793) B5751793
theorem B20450819 : Blo 2241435 20450819 := bstep (se 1 (by rfl) ⟨15338114, by rfl⟩ : syracuseStep 20450819 = 30676229) B30676229
theorem B13633879 : Blo 2241435 13633879 := bstep (se 1 (by rfl) ⟨10225409, by rfl⟩ : syracuseStep 13633879 = 20450819) B20450819
theorem B18178505 : Blo 2241435 18178505 := bstep (se 2 (by rfl) ⟨6816939, by rfl⟩ : syracuseStep 18178505 = 13633879) B13633879
theorem B12119003 : Blo 2241435 12119003 := bstep (se 1 (by rfl) ⟨9089252, by rfl⟩ : syracuseStep 12119003 = 18178505) B18178505
theorem B8079335 : Blo 2241435 8079335 := bstep (se 1 (by rfl) ⟨6059501, by rfl⟩ : syracuseStep 8079335 = 12119003) B12119003
theorem B5386223 : Blo 2241435 5386223 := bstep (se 1 (by rfl) ⟨4039667, by rfl⟩ : syracuseStep 5386223 = 8079335) B8079335
theorem B3590815 : Blo 2241435 3590815 := bstep (se 1 (by rfl) ⟨2693111, by rfl⟩ : syracuseStep 3590815 = 5386223) B5386223
theorem B4787753 : Blo 2241435 4787753 := bstep (se 2 (by rfl) ⟨1795407, by rfl⟩ : syracuseStep 4787753 = 3590815) B3590815
theorem B12767341 : Blo 2241435 12767341 := bstep (se 3 (by rfl) ⟨2393876, by rfl⟩ : syracuseStep 12767341 = 4787753) B4787753
theorem B17023121 : Blo 2241435 17023121 := bstep (se 2 (by rfl) ⟨6383670, by rfl⟩ : syracuseStep 17023121 = 12767341) B12767341
theorem B11348747 : Blo 2241435 11348747 := bstep (se 1 (by rfl) ⟨8511560, by rfl⟩ : syracuseStep 11348747 = 17023121) B17023121
theorem B7565831 : Blo 2241435 7565831 := bstep (se 1 (by rfl) ⟨5674373, by rfl⟩ : syracuseStep 7565831 = 11348747) B11348747
theorem B5043887 : Blo 2241435 5043887 := bstep (se 1 (by rfl) ⟨3782915, by rfl⟩ : syracuseStep 5043887 = 7565831) B7565831
theorem B3362591 : Blo 2241435 3362591 := bstep (se 1 (by rfl) ⟨2521943, by rfl⟩ : syracuseStep 3362591 = 5043887) B5043887
theorem B2241727 : Blo 2241435 2241727 := bstep (se 1 (by rfl) ⟨1681295, by rfl⟩ : syracuseStep 2241727 = 3362591) B3362591
theorem B3362597 : Blo 2241435 3362597 := bbase (se 4 (by rfl) ⟨315243, by rfl⟩ : syracuseStep 3362597 = 630487) (by norm_num)
theorem B2241731 : Blo 2241435 2241731 := bstep (se 1 (by rfl) ⟨1681298, by rfl⟩ : syracuseStep 2241731 = 3362597) B3362597
theorem B2837197 : Blo 2241435 2837197 := bbase (se 3 (by rfl) ⟨531974, by rfl⟩ : syracuseStep 2837197 = 1063949) (by norm_num)
theorem B3782929 : Blo 2241435 3782929 := bstep (se 2 (by rfl) ⟨1418598, by rfl⟩ : syracuseStep 3782929 = 2837197) B2837197
theorem B5043905 : Blo 2241435 5043905 := bstep (se 2 (by rfl) ⟨1891464, by rfl⟩ : syracuseStep 5043905 = 3782929) B3782929
theorem B3362603 : Blo 2241435 3362603 := bstep (se 1 (by rfl) ⟨2521952, by rfl⟩ : syracuseStep 3362603 = 5043905) B5043905
theorem B2241735 : Blo 2241435 2241735 := bstep (se 1 (by rfl) ⟨1681301, by rfl⟩ : syracuseStep 2241735 = 3362603) B3362603
theorem B2521957 : Blo 2241435 2521957 := bbase (se 4 (by rfl) ⟨236433, by rfl⟩ : syracuseStep 2521957 = 472867) (by norm_num)
theorem B3362609 : Blo 2241435 3362609 := bstep (se 2 (by rfl) ⟨1260978, by rfl⟩ : syracuseStep 3362609 = 2521957) B2521957
theorem B2241739 : Blo 2241435 2241739 := bstep (se 1 (by rfl) ⟨1681304, by rfl⟩ : syracuseStep 2241739 = 3362609) B3362609
theorem B6383717 : Blo 2241435 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B4255811 : Blo 2241435 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B2837207 : Blo 2241435 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B7565885 : Blo 2241435 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B5043923 : Blo 2241435 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B3362615 : Blo 2241435 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B2241743 : Blo 2241435 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B3362621 : Blo 2241435 3362621 := bbase (se 3 (by rfl) ⟨630491, by rfl⟩ : syracuseStep 3362621 = 1260983) (by norm_num)
theorem B2241747 : Blo 2241435 2241747 := bstep (se 1 (by rfl) ⟨1681310, by rfl⟩ : syracuseStep 2241747 = 3362621) B3362621
theorem B5043941 : Blo 2241435 5043941 := bbase (se 4 (by rfl) ⟨472869, by rfl⟩ : syracuseStep 5043941 = 945739) (by norm_num)
theorem B3362627 : Blo 2241435 3362627 := bstep (se 1 (by rfl) ⟨2521970, by rfl⟩ : syracuseStep 3362627 = 5043941) B5043941
theorem B2241751 : Blo 2241435 2241751 := bstep (se 1 (by rfl) ⟨1681313, by rfl⟩ : syracuseStep 2241751 = 3362627) B3362627
theorem B5674445 : Blo 2241435 5674445 := bbase (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) (by norm_num)
theorem B3782963 : Blo 2241435 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B2521975 : Blo 2241435 2521975 := bstep (se 1 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 2521975 = 3782963) B3782963
theorem B3362633 : Blo 2241435 3362633 := bstep (se 2 (by rfl) ⟨1260987, by rfl⟩ : syracuseStep 3362633 = 2521975) B2521975
theorem B2241755 : Blo 2241435 2241755 := bstep (se 1 (by rfl) ⟨1681316, by rfl⟩ : syracuseStep 2241755 = 3362633) B3362633
theorem B5386301 : Blo 2241435 5386301 := bbase (se 3 (by rfl) ⟨1009931, by rfl⟩ : syracuseStep 5386301 = 2019863) (by norm_num)
theorem B3590867 : Blo 2241435 3590867 := bstep (se 1 (by rfl) ⟨2693150, by rfl⟩ : syracuseStep 3590867 = 5386301) B5386301
theorem B2393911 : Blo 2241435 2393911 := bstep (se 1 (by rfl) ⟨1795433, by rfl⟩ : syracuseStep 2393911 = 3590867) B3590867
theorem B3191881 : Blo 2241435 3191881 := bstep (se 2 (by rfl) ⟨1196955, by rfl⟩ : syracuseStep 3191881 = 2393911) B2393911
theorem B4255841 : Blo 2241435 4255841 := bstep (se 2 (by rfl) ⟨1595940, by rfl⟩ : syracuseStep 4255841 = 3191881) B3191881
theorem B11348909 : Blo 2241435 11348909 := bstep (se 3 (by rfl) ⟨2127920, by rfl⟩ : syracuseStep 11348909 = 4255841) B4255841
theorem B7565939 : Blo 2241435 7565939 := bstep (se 1 (by rfl) ⟨5674454, by rfl⟩ : syracuseStep 7565939 = 11348909) B11348909
theorem B5043959 : Blo 2241435 5043959 := bstep (se 1 (by rfl) ⟨3782969, by rfl⟩ : syracuseStep 5043959 = 7565939) B7565939
theorem B3362639 : Blo 2241435 3362639 := bstep (se 1 (by rfl) ⟨2521979, by rfl⟩ : syracuseStep 3362639 = 5043959) B5043959
theorem B2241759 : Blo 2241435 2241759 := bstep (se 1 (by rfl) ⟨1681319, by rfl⟩ : syracuseStep 2241759 = 3362639) B3362639
theorem B3362645 : Blo 2241435 3362645 := bbase (se 9 (by rfl) ⟨9851, by rfl⟩ : syracuseStep 3362645 = 19703) (by norm_num)
theorem B2241763 : Blo 2241435 2241763 := bstep (se 1 (by rfl) ⟨1681322, by rfl⟩ : syracuseStep 2241763 = 3362645) B3362645
theorem B7987397 : Blo 2241435 7987397 := bbase (se 4 (by rfl) ⟨748818, by rfl⟩ : syracuseStep 7987397 = 1497637) (by norm_num)
theorem B21299725 : Blo 2241435 21299725 := bstep (se 3 (by rfl) ⟨3993698, by rfl⟩ : syracuseStep 21299725 = 7987397) B7987397
theorem B113598533 : Blo 2241435 113598533 := bstep (se 4 (by rfl) ⟨10649862, by rfl⟩ : syracuseStep 113598533 = 21299725) B21299725
theorem B75732355 : Blo 2241435 75732355 := bstep (se 1 (by rfl) ⟨56799266, by rfl⟩ : syracuseStep 75732355 = 113598533) B113598533
theorem B100976473 : Blo 2241435 100976473 := bstep (se 2 (by rfl) ⟨37866177, by rfl⟩ : syracuseStep 100976473 = 75732355) B75732355
theorem B134635297 : Blo 2241435 134635297 := bstep (se 2 (by rfl) ⟨50488236, by rfl⟩ : syracuseStep 134635297 = 100976473) B100976473
theorem B179513729 : Blo 2241435 179513729 := bstep (se 2 (by rfl) ⟨67317648, by rfl⟩ : syracuseStep 179513729 = 134635297) B134635297
theorem B119675819 : Blo 2241435 119675819 := bstep (se 1 (by rfl) ⟨89756864, by rfl⟩ : syracuseStep 119675819 = 179513729) B179513729
theorem B79783879 : Blo 2241435 79783879 := bstep (se 1 (by rfl) ⟨59837909, by rfl⟩ : syracuseStep 79783879 = 119675819) B119675819
theorem B106378505 : Blo 2241435 106378505 := bstep (se 2 (by rfl) ⟨39891939, by rfl⟩ : syracuseStep 106378505 = 79783879) B79783879
theorem B70919003 : Blo 2241435 70919003 := bstep (se 1 (by rfl) ⟨53189252, by rfl⟩ : syracuseStep 70919003 = 106378505) B106378505
theorem B189117341 : Blo 2241435 189117341 := bstep (se 3 (by rfl) ⟨35459501, by rfl⟩ : syracuseStep 189117341 = 70919003) B70919003
theorem B126078227 : Blo 2241435 126078227 := bstep (se 1 (by rfl) ⟨94558670, by rfl⟩ : syracuseStep 126078227 = 189117341) B189117341
theorem B84052151 : Blo 2241435 84052151 := bstep (se 1 (by rfl) ⟨63039113, by rfl⟩ : syracuseStep 84052151 = 126078227) B126078227
theorem B56034767 : Blo 2241435 56034767 := bstep (se 1 (by rfl) ⟨42026075, by rfl⟩ : syracuseStep 56034767 = 84052151) B84052151
theorem B37356511 : Blo 2241435 37356511 := bstep (se 1 (by rfl) ⟨28017383, by rfl⟩ : syracuseStep 37356511 = 56034767) B56034767
theorem B49808681 : Blo 2241435 49808681 := bstep (se 2 (by rfl) ⟨18678255, by rfl⟩ : syracuseStep 49808681 = 37356511) B37356511
theorem B33205787 : Blo 2241435 33205787 := bstep (se 1 (by rfl) ⟨24904340, by rfl⟩ : syracuseStep 33205787 = 49808681) B49808681
theorem B22137191 : Blo 2241435 22137191 := bstep (se 1 (by rfl) ⟨16602893, by rfl⟩ : syracuseStep 22137191 = 33205787) B33205787
theorem B14758127 : Blo 2241435 14758127 := bstep (se 1 (by rfl) ⟨11068595, by rfl⟩ : syracuseStep 14758127 = 22137191) B22137191
theorem B9838751 : Blo 2241435 9838751 := bstep (se 1 (by rfl) ⟨7379063, by rfl⟩ : syracuseStep 9838751 = 14758127) B14758127
theorem B26236669 : Blo 2241435 26236669 := bstep (se 3 (by rfl) ⟨4919375, by rfl⟩ : syracuseStep 26236669 = 9838751) B9838751
theorem B34982225 : Blo 2241435 34982225 := bstep (se 2 (by rfl) ⟨13118334, by rfl⟩ : syracuseStep 34982225 = 26236669) B26236669
theorem B23321483 : Blo 2241435 23321483 := bstep (se 1 (by rfl) ⟨17491112, by rfl⟩ : syracuseStep 23321483 = 34982225) B34982225
theorem B15547655 : Blo 2241435 15547655 := bstep (se 1 (by rfl) ⟨11660741, by rfl⟩ : syracuseStep 15547655 = 23321483) B23321483
theorem B10365103 : Blo 2241435 10365103 := bstep (se 1 (by rfl) ⟨7773827, by rfl⟩ : syracuseStep 10365103 = 15547655) B15547655
theorem B55280549 : Blo 2241435 55280549 := bstep (se 4 (by rfl) ⟨5182551, by rfl⟩ : syracuseStep 55280549 = 10365103) B10365103
theorem B36853699 : Blo 2241435 36853699 := bstep (se 1 (by rfl) ⟨27640274, by rfl⟩ : syracuseStep 36853699 = 55280549) B55280549
theorem B49138265 : Blo 2241435 49138265 := bstep (se 2 (by rfl) ⟨18426849, by rfl⟩ : syracuseStep 49138265 = 36853699) B36853699
theorem B32758843 : Blo 2241435 32758843 := bstep (se 1 (by rfl) ⟨24569132, by rfl⟩ : syracuseStep 32758843 = 49138265) B49138265
theorem B43678457 : Blo 2241435 43678457 := bstep (se 2 (by rfl) ⟨16379421, by rfl⟩ : syracuseStep 43678457 = 32758843) B32758843
theorem B29118971 : Blo 2241435 29118971 := bstep (se 1 (by rfl) ⟨21839228, by rfl⟩ : syracuseStep 29118971 = 43678457) B43678457
theorem B77650589 : Blo 2241435 77650589 := bstep (se 3 (by rfl) ⟨14559485, by rfl⟩ : syracuseStep 77650589 = 29118971) B29118971
theorem B207068237 : Blo 2241435 207068237 := bstep (se 3 (by rfl) ⟨38825294, by rfl⟩ : syracuseStep 207068237 = 77650589) B77650589
theorem B138045491 : Blo 2241435 138045491 := bstep (se 1 (by rfl) ⟨103534118, by rfl⟩ : syracuseStep 138045491 = 207068237) B207068237
theorem B92030327 : Blo 2241435 92030327 := bstep (se 1 (by rfl) ⟨69022745, by rfl⟩ : syracuseStep 92030327 = 138045491) B138045491
theorem B61353551 : Blo 2241435 61353551 := bstep (se 1 (by rfl) ⟨46015163, by rfl⟩ : syracuseStep 61353551 = 92030327) B92030327
theorem B40902367 : Blo 2241435 40902367 := bstep (se 1 (by rfl) ⟨30676775, by rfl⟩ : syracuseStep 40902367 = 61353551) B61353551
theorem B54536489 : Blo 2241435 54536489 := bstep (se 2 (by rfl) ⟨20451183, by rfl⟩ : syracuseStep 54536489 = 40902367) B40902367
theorem B36357659 : Blo 2241435 36357659 := bstep (se 1 (by rfl) ⟨27268244, by rfl⟩ : syracuseStep 36357659 = 54536489) B54536489
theorem B24238439 : Blo 2241435 24238439 := bstep (se 1 (by rfl) ⟨18178829, by rfl⟩ : syracuseStep 24238439 = 36357659) B36357659
theorem B16158959 : Blo 2241435 16158959 := bstep (se 1 (by rfl) ⟨12119219, by rfl⟩ : syracuseStep 16158959 = 24238439) B24238439
theorem B10772639 : Blo 2241435 10772639 := bstep (se 1 (by rfl) ⟨8079479, by rfl⟩ : syracuseStep 10772639 = 16158959) B16158959
theorem B7181759 : Blo 2241435 7181759 := bstep (se 1 (by rfl) ⟨5386319, by rfl⟩ : syracuseStep 7181759 = 10772639) B10772639
theorem B4787839 : Blo 2241435 4787839 := bstep (se 1 (by rfl) ⟨3590879, by rfl⟩ : syracuseStep 4787839 = 7181759) B7181759
theorem B6383785 : Blo 2241435 6383785 := bstep (se 2 (by rfl) ⟨2393919, by rfl⟩ : syracuseStep 6383785 = 4787839) B4787839
theorem B8511713 : Blo 2241435 8511713 := bstep (se 2 (by rfl) ⟨3191892, by rfl⟩ : syracuseStep 8511713 = 6383785) B6383785
theorem B5674475 : Blo 2241435 5674475 := bstep (se 1 (by rfl) ⟨4255856, by rfl⟩ : syracuseStep 5674475 = 8511713) B8511713
theorem B3782983 : Blo 2241435 3782983 := bstep (se 1 (by rfl) ⟨2837237, by rfl⟩ : syracuseStep 3782983 = 5674475) B5674475
theorem B5043977 : Blo 2241435 5043977 := bstep (se 2 (by rfl) ⟨1891491, by rfl⟩ : syracuseStep 5043977 = 3782983) B3782983
theorem B3362651 : Blo 2241435 3362651 := bstep (se 1 (by rfl) ⟨2521988, by rfl⟩ : syracuseStep 3362651 = 5043977) B5043977
theorem B2241767 : Blo 2241435 2241767 := bstep (se 1 (by rfl) ⟨1681325, by rfl⟩ : syracuseStep 2241767 = 3362651) B3362651
theorem B2521993 : Blo 2241435 2521993 := bbase (se 2 (by rfl) ⟨945747, by rfl⟩ : syracuseStep 2521993 = 1891495) (by norm_num)
theorem B3362657 : Blo 2241435 3362657 := bstep (se 2 (by rfl) ⟨1260996, by rfl⟩ : syracuseStep 3362657 = 2521993) B2521993
theorem B2241771 : Blo 2241435 2241771 := bstep (se 1 (by rfl) ⟨1681328, by rfl⟩ : syracuseStep 2241771 = 3362657) B3362657
theorem B145431125 : Blo 2241435 145431125 := bbase (se 8 (by rfl) ⟨852135, by rfl⟩ : syracuseStep 145431125 = 1704271) (by norm_num)
theorem B96954083 : Blo 2241435 96954083 := bstep (se 1 (by rfl) ⟨72715562, by rfl⟩ : syracuseStep 96954083 = 145431125) B145431125
theorem B64636055 : Blo 2241435 64636055 := bstep (se 1 (by rfl) ⟨48477041, by rfl⟩ : syracuseStep 64636055 = 96954083) B96954083
theorem B43090703 : Blo 2241435 43090703 := bstep (se 1 (by rfl) ⟨32318027, by rfl⟩ : syracuseStep 43090703 = 64636055) B64636055
theorem B28727135 : Blo 2241435 28727135 := bstep (se 1 (by rfl) ⟨21545351, by rfl⟩ : syracuseStep 28727135 = 43090703) B43090703
theorem B19151423 : Blo 2241435 19151423 := bstep (se 1 (by rfl) ⟨14363567, by rfl⟩ : syracuseStep 19151423 = 28727135) B28727135
theorem B12767615 : Blo 2241435 12767615 := bstep (se 1 (by rfl) ⟨9575711, by rfl⟩ : syracuseStep 12767615 = 19151423) B19151423
theorem B8511743 : Blo 2241435 8511743 := bstep (se 1 (by rfl) ⟨6383807, by rfl⟩ : syracuseStep 8511743 = 12767615) B12767615
theorem B5674495 : Blo 2241435 5674495 := bstep (se 1 (by rfl) ⟨4255871, by rfl⟩ : syracuseStep 5674495 = 8511743) B8511743
theorem B7565993 : Blo 2241435 7565993 := bstep (se 2 (by rfl) ⟨2837247, by rfl⟩ : syracuseStep 7565993 = 5674495) B5674495
theorem B5043995 : Blo 2241435 5043995 := bstep (se 1 (by rfl) ⟨3782996, by rfl⟩ : syracuseStep 5043995 = 7565993) B7565993
theorem B3362663 : Blo 2241435 3362663 := bstep (se 1 (by rfl) ⟨2521997, by rfl⟩ : syracuseStep 3362663 = 5043995) B5043995
theorem B2241775 : Blo 2241435 2241775 := bstep (se 1 (by rfl) ⟨1681331, by rfl⟩ : syracuseStep 2241775 = 3362663) B3362663
theorem B3362669 : Blo 2241435 3362669 := bbase (se 3 (by rfl) ⟨630500, by rfl⟩ : syracuseStep 3362669 = 1261001) (by norm_num)
theorem B2241779 : Blo 2241435 2241779 := bstep (se 1 (by rfl) ⟨1681334, by rfl⟩ : syracuseStep 2241779 = 3362669) B3362669
theorem B5044013 : Blo 2241435 5044013 := bbase (se 3 (by rfl) ⟨945752, by rfl⟩ : syracuseStep 5044013 = 1891505) (by norm_num)
theorem B3362675 : Blo 2241435 3362675 := bstep (se 1 (by rfl) ⟨2522006, by rfl⟩ : syracuseStep 3362675 = 5044013) B5044013
theorem B2241783 : Blo 2241435 2241783 := bstep (se 1 (by rfl) ⟨1681337, by rfl⟩ : syracuseStep 2241783 = 3362675) B3362675
theorem B9575765 : Blo 2241435 9575765 := bbase (se 11 (by rfl) ⟨7013, by rfl⟩ : syracuseStep 9575765 = 14027) (by norm_num)
theorem B6383843 : Blo 2241435 6383843 := bstep (se 1 (by rfl) ⟨4787882, by rfl⟩ : syracuseStep 6383843 = 9575765) B9575765
theorem B4255895 : Blo 2241435 4255895 := bstep (se 1 (by rfl) ⟨3191921, by rfl⟩ : syracuseStep 4255895 = 6383843) B6383843
theorem B2837263 : Blo 2241435 2837263 := bstep (se 1 (by rfl) ⟨2127947, by rfl⟩ : syracuseStep 2837263 = 4255895) B4255895
theorem B3783017 : Blo 2241435 3783017 := bstep (se 2 (by rfl) ⟨1418631, by rfl⟩ : syracuseStep 3783017 = 2837263) B2837263
theorem B2522011 : Blo 2241435 2522011 := bstep (se 1 (by rfl) ⟨1891508, by rfl⟩ : syracuseStep 2522011 = 3783017) B3783017
theorem B3362681 : Blo 2241435 3362681 := bstep (se 2 (by rfl) ⟨1261005, by rfl⟩ : syracuseStep 3362681 = 2522011) B2522011
theorem B2241787 : Blo 2241435 2241787 := bstep (se 1 (by rfl) ⟨1681340, by rfl⟩ : syracuseStep 2241787 = 3362681) B3362681
theorem B14363669 : Blo 2241435 14363669 := bbase (se 6 (by rfl) ⟨336648, by rfl⟩ : syracuseStep 14363669 = 673297) (by norm_num)
theorem B38303117 : Blo 2241435 38303117 := bstep (se 3 (by rfl) ⟨7181834, by rfl⟩ : syracuseStep 38303117 = 14363669) B14363669
theorem B25535411 : Blo 2241435 25535411 := bstep (se 1 (by rfl) ⟨19151558, by rfl⟩ : syracuseStep 25535411 = 38303117) B38303117
theorem B17023607 : Blo 2241435 17023607 := bstep (se 1 (by rfl) ⟨12767705, by rfl⟩ : syracuseStep 17023607 = 25535411) B25535411
theorem B11349071 : Blo 2241435 11349071 := bstep (se 1 (by rfl) ⟨8511803, by rfl⟩ : syracuseStep 11349071 = 17023607) B17023607
theorem B7566047 : Blo 2241435 7566047 := bstep (se 1 (by rfl) ⟨5674535, by rfl⟩ : syracuseStep 7566047 = 11349071) B11349071
theorem B5044031 : Blo 2241435 5044031 := bstep (se 1 (by rfl) ⟨3783023, by rfl⟩ : syracuseStep 5044031 = 7566047) B7566047
theorem B3362687 : Blo 2241435 3362687 := bstep (se 1 (by rfl) ⟨2522015, by rfl⟩ : syracuseStep 3362687 = 5044031) B5044031
theorem B2241791 : Blo 2241435 2241791 := bstep (se 1 (by rfl) ⟨1681343, by rfl⟩ : syracuseStep 2241791 = 3362687) B3362687
theorem B3362693 : Blo 2241435 3362693 := bbase (se 4 (by rfl) ⟨315252, by rfl⟩ : syracuseStep 3362693 = 630505) (by norm_num)
theorem B2241795 : Blo 2241435 2241795 := bstep (se 1 (by rfl) ⟨1681346, by rfl⟩ : syracuseStep 2241795 = 3362693) B3362693
theorem B3783037 : Blo 2241435 3783037 := bbase (se 3 (by rfl) ⟨709319, by rfl⟩ : syracuseStep 3783037 = 1418639) (by norm_num)
theorem B5044049 : Blo 2241435 5044049 := bstep (se 2 (by rfl) ⟨1891518, by rfl⟩ : syracuseStep 5044049 = 3783037) B3783037
theorem B3362699 : Blo 2241435 3362699 := bstep (se 1 (by rfl) ⟨2522024, by rfl⟩ : syracuseStep 3362699 = 5044049) B5044049
theorem B2241799 : Blo 2241435 2241799 := bstep (se 1 (by rfl) ⟨1681349, by rfl⟩ : syracuseStep 2241799 = 3362699) B3362699
theorem B2522029 : Blo 2241435 2522029 := bbase (se 3 (by rfl) ⟨472880, by rfl⟩ : syracuseStep 2522029 = 945761) (by norm_num)
theorem B3362705 : Blo 2241435 3362705 := bstep (se 2 (by rfl) ⟨1261014, by rfl⟩ : syracuseStep 3362705 = 2522029) B2522029
theorem B2241803 : Blo 2241435 2241803 := bstep (se 1 (by rfl) ⟨1681352, by rfl⟩ : syracuseStep 2241803 = 3362705) B3362705
theorem B7566101 : Blo 2241435 7566101 := bbase (se 6 (by rfl) ⟨177330, by rfl⟩ : syracuseStep 7566101 = 354661) (by norm_num)
theorem B5044067 : Blo 2241435 5044067 := bstep (se 1 (by rfl) ⟨3783050, by rfl⟩ : syracuseStep 5044067 = 7566101) B7566101
theorem B3362711 : Blo 2241435 3362711 := bstep (se 1 (by rfl) ⟨2522033, by rfl⟩ : syracuseStep 3362711 = 5044067) B5044067
theorem B2241807 : Blo 2241435 2241807 := bstep (se 1 (by rfl) ⟨1681355, by rfl⟩ : syracuseStep 2241807 = 3362711) B3362711
theorem B3362717 : Blo 2241435 3362717 := bbase (se 3 (by rfl) ⟨630509, by rfl⟩ : syracuseStep 3362717 = 1261019) (by norm_num)
theorem B2241811 : Blo 2241435 2241811 := bstep (se 1 (by rfl) ⟨1681358, by rfl⟩ : syracuseStep 2241811 = 3362717) B3362717
theorem B5044085 : Blo 2241435 5044085 := bbase (se 5 (by rfl) ⟨236441, by rfl⟩ : syracuseStep 5044085 = 472883) (by norm_num)
theorem B3362723 : Blo 2241435 3362723 := bstep (se 1 (by rfl) ⟨2522042, by rfl⟩ : syracuseStep 3362723 = 5044085) B5044085
theorem B2241815 : Blo 2241435 2241815 := bstep (se 1 (by rfl) ⟨1681361, by rfl⟩ : syracuseStep 2241815 = 3362723) B3362723
theorem B4544813 : Blo 2241435 4544813 := bbase (se 3 (by rfl) ⟨852152, by rfl⟩ : syracuseStep 4544813 = 1704305) (by norm_num)
theorem B3029875 : Blo 2241435 3029875 := bstep (se 1 (by rfl) ⟨2272406, by rfl⟩ : syracuseStep 3029875 = 4544813) B4544813
theorem B16159333 : Blo 2241435 16159333 := bstep (se 4 (by rfl) ⟨1514937, by rfl⟩ : syracuseStep 16159333 = 3029875) B3029875
theorem B21545777 : Blo 2241435 21545777 := bstep (se 2 (by rfl) ⟨8079666, by rfl⟩ : syracuseStep 21545777 = 16159333) B16159333
theorem B14363851 : Blo 2241435 14363851 := bstep (se 1 (by rfl) ⟨10772888, by rfl⟩ : syracuseStep 14363851 = 21545777) B21545777
theorem B19151801 : Blo 2241435 19151801 := bstep (se 2 (by rfl) ⟨7181925, by rfl⟩ : syracuseStep 19151801 = 14363851) B14363851
theorem B12767867 : Blo 2241435 12767867 := bstep (se 1 (by rfl) ⟨9575900, by rfl⟩ : syracuseStep 12767867 = 19151801) B19151801
theorem B8511911 : Blo 2241435 8511911 := bstep (se 1 (by rfl) ⟨6383933, by rfl⟩ : syracuseStep 8511911 = 12767867) B12767867
theorem B5674607 : Blo 2241435 5674607 := bstep (se 1 (by rfl) ⟨4255955, by rfl⟩ : syracuseStep 5674607 = 8511911) B8511911
theorem B3783071 : Blo 2241435 3783071 := bstep (se 1 (by rfl) ⟨2837303, by rfl⟩ : syracuseStep 3783071 = 5674607) B5674607
theorem B2522047 : Blo 2241435 2522047 := bstep (se 1 (by rfl) ⟨1891535, by rfl⟩ : syracuseStep 2522047 = 3783071) B3783071
theorem B3362729 : Blo 2241435 3362729 := bstep (se 2 (by rfl) ⟨1261023, by rfl⟩ : syracuseStep 3362729 = 2522047) B2522047
theorem B2241819 : Blo 2241435 2241819 := bstep (se 1 (by rfl) ⟨1681364, by rfl⟩ : syracuseStep 2241819 = 3362729) B3362729
theorem B8511925 : Blo 2241435 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B11349233 : Blo 2241435 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B7566155 : Blo 2241435 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B5044103 : Blo 2241435 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B3362735 : Blo 2241435 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B2241823 : Blo 2241435 2241823 := bstep (se 1 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 2241823 = 3362735) B3362735
theorem B3362741 : Blo 2241435 3362741 := bbase (se 5 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 3362741 = 315257) (by norm_num)
theorem B2241827 : Blo 2241435 2241827 := bstep (se 1 (by rfl) ⟨1681370, by rfl⟩ : syracuseStep 2241827 = 3362741) B3362741
theorem B5674637 : Blo 2241435 5674637 := bbase (se 3 (by rfl) ⟨1063994, by rfl⟩ : syracuseStep 5674637 = 2127989) (by norm_num)
theorem B3783091 : Blo 2241435 3783091 := bstep (se 1 (by rfl) ⟨2837318, by rfl⟩ : syracuseStep 3783091 = 5674637) B5674637
theorem B5044121 : Blo 2241435 5044121 := bstep (se 2 (by rfl) ⟨1891545, by rfl⟩ : syracuseStep 5044121 = 3783091) B3783091
theorem B3362747 : Blo 2241435 3362747 := bstep (se 1 (by rfl) ⟨2522060, by rfl⟩ : syracuseStep 3362747 = 5044121) B5044121
theorem B2241831 : Blo 2241435 2241831 := bstep (se 1 (by rfl) ⟨1681373, by rfl⟩ : syracuseStep 2241831 = 3362747) B3362747
theorem B2522065 : Blo 2241435 2522065 := bbase (se 2 (by rfl) ⟨945774, by rfl⟩ : syracuseStep 2522065 = 1891549) (by norm_num)
theorem B3362753 : Blo 2241435 3362753 := bstep (se 2 (by rfl) ⟨1261032, by rfl⟩ : syracuseStep 3362753 = 2522065) B2522065
theorem B2241835 : Blo 2241435 2241835 := bstep (se 1 (by rfl) ⟨1681376, by rfl⟩ : syracuseStep 2241835 = 3362753) B3362753
theorem B5386493 : Blo 2241435 5386493 := bbase (se 3 (by rfl) ⟨1009967, by rfl⟩ : syracuseStep 5386493 = 2019935) (by norm_num)
theorem B3590995 : Blo 2241435 3590995 := bstep (se 1 (by rfl) ⟨2693246, by rfl⟩ : syracuseStep 3590995 = 5386493) B5386493
theorem B4787993 : Blo 2241435 4787993 := bstep (se 2 (by rfl) ⟨1795497, by rfl⟩ : syracuseStep 4787993 = 3590995) B3590995
theorem B3191995 : Blo 2241435 3191995 := bstep (se 1 (by rfl) ⟨2393996, by rfl⟩ : syracuseStep 3191995 = 4787993) B4787993
theorem B4255993 : Blo 2241435 4255993 := bstep (se 2 (by rfl) ⟨1595997, by rfl⟩ : syracuseStep 4255993 = 3191995) B3191995
theorem B5674657 : Blo 2241435 5674657 := bstep (se 2 (by rfl) ⟨2127996, by rfl⟩ : syracuseStep 5674657 = 4255993) B4255993
theorem B7566209 : Blo 2241435 7566209 := bstep (se 2 (by rfl) ⟨2837328, by rfl⟩ : syracuseStep 7566209 = 5674657) B5674657
theorem B5044139 : Blo 2241435 5044139 := bstep (se 1 (by rfl) ⟨3783104, by rfl⟩ : syracuseStep 5044139 = 7566209) B7566209
theorem B3362759 : Blo 2241435 3362759 := bstep (se 1 (by rfl) ⟨2522069, by rfl⟩ : syracuseStep 3362759 = 5044139) B5044139
theorem B2241839 : Blo 2241435 2241839 := bstep (se 1 (by rfl) ⟨1681379, by rfl⟩ : syracuseStep 2241839 = 3362759) B3362759
theorem B3362765 : Blo 2241435 3362765 := bbase (se 3 (by rfl) ⟨630518, by rfl⟩ : syracuseStep 3362765 = 1261037) (by norm_num)
theorem B2241843 : Blo 2241435 2241843 := bstep (se 1 (by rfl) ⟨1681382, by rfl⟩ : syracuseStep 2241843 = 3362765) B3362765
theorem B5044157 : Blo 2241435 5044157 := bbase (se 3 (by rfl) ⟨945779, by rfl⟩ : syracuseStep 5044157 = 1891559) (by norm_num)
theorem B3362771 : Blo 2241435 3362771 := bstep (se 1 (by rfl) ⟨2522078, by rfl⟩ : syracuseStep 3362771 = 5044157) B5044157
theorem B2241847 : Blo 2241435 2241847 := bstep (se 1 (by rfl) ⟨1681385, by rfl⟩ : syracuseStep 2241847 = 3362771) B3362771
theorem B3783125 : Blo 2241435 3783125 := bbase (se 7 (by rfl) ⟨44333, by rfl⟩ : syracuseStep 3783125 = 88667) (by norm_num)
theorem B2522083 : Blo 2241435 2522083 := bstep (se 1 (by rfl) ⟨1891562, by rfl⟩ : syracuseStep 2522083 = 3783125) B3783125
theorem B3362777 : Blo 2241435 3362777 := bstep (se 2 (by rfl) ⟨1261041, by rfl⟩ : syracuseStep 3362777 = 2522083) B2522083
theorem B2241851 : Blo 2241435 2241851 := bstep (se 1 (by rfl) ⟨1681388, by rfl⟩ : syracuseStep 2241851 = 3362777) B3362777
theorem B9576053 : Blo 2241435 9576053 := bbase (se 5 (by rfl) ⟨448877, by rfl⟩ : syracuseStep 9576053 = 897755) (by norm_num)
theorem B6384035 : Blo 2241435 6384035 := bstep (se 1 (by rfl) ⟨4788026, by rfl⟩ : syracuseStep 6384035 = 9576053) B9576053
theorem B17024093 : Blo 2241435 17024093 := bstep (se 3 (by rfl) ⟨3192017, by rfl⟩ : syracuseStep 17024093 = 6384035) B6384035
theorem B11349395 : Blo 2241435 11349395 := bstep (se 1 (by rfl) ⟨8512046, by rfl⟩ : syracuseStep 11349395 = 17024093) B17024093
theorem B7566263 : Blo 2241435 7566263 := bstep (se 1 (by rfl) ⟨5674697, by rfl⟩ : syracuseStep 7566263 = 11349395) B11349395
theorem B5044175 : Blo 2241435 5044175 := bstep (se 1 (by rfl) ⟨3783131, by rfl⟩ : syracuseStep 5044175 = 7566263) B7566263
theorem B3362783 : Blo 2241435 3362783 := bstep (se 1 (by rfl) ⟨2522087, by rfl⟩ : syracuseStep 3362783 = 5044175) B5044175
theorem B2241855 : Blo 2241435 2241855 := bstep (se 1 (by rfl) ⟨1681391, by rfl⟩ : syracuseStep 2241855 = 3362783) B3362783
theorem B3362789 : Blo 2241435 3362789 := bbase (se 4 (by rfl) ⟨315261, by rfl⟩ : syracuseStep 3362789 = 630523) (by norm_num)
theorem B2241859 : Blo 2241435 2241859 := bstep (se 1 (by rfl) ⟨1681394, by rfl⟩ : syracuseStep 2241859 = 3362789) B3362789
theorem B7669525 : Blo 2241435 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B10226033 : Blo 2241435 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B6817355 : Blo 2241435 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B4544903 : Blo 2241435 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B3029935 : Blo 2241435 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B4039913 : Blo 2241435 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B10773101 : Blo 2241435 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B7182067 : Blo 2241435 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B9576089 : Blo 2241435 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B6384059 : Blo 2241435 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B4256039 : Blo 2241435 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B2837359 : Blo 2241435 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B3783145 : Blo 2241435 3783145 := bstep (se 2 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 3783145 = 2837359) B2837359
theorem B5044193 : Blo 2241435 5044193 := bstep (se 2 (by rfl) ⟨1891572, by rfl⟩ : syracuseStep 5044193 = 3783145) B3783145
theorem B3362795 : Blo 2241435 3362795 := bstep (se 1 (by rfl) ⟨2522096, by rfl⟩ : syracuseStep 3362795 = 5044193) B5044193
theorem B2241863 : Blo 2241435 2241863 := bstep (se 1 (by rfl) ⟨1681397, by rfl⟩ : syracuseStep 2241863 = 3362795) B3362795
theorem B2522101 : Blo 2241435 2522101 := bbase (se 5 (by rfl) ⟨118223, by rfl⟩ : syracuseStep 2522101 = 236447) (by norm_num)
theorem B3362801 : Blo 2241435 3362801 := bstep (se 2 (by rfl) ⟨1261050, by rfl⟩ : syracuseStep 3362801 = 2522101) B2522101
theorem B2241867 : Blo 2241435 2241867 := bstep (se 1 (by rfl) ⟨1681400, by rfl⟩ : syracuseStep 2241867 = 3362801) B3362801
theorem B2837369 : Blo 2241435 2837369 := bbase (se 2 (by rfl) ⟨1064013, by rfl⟩ : syracuseStep 2837369 = 2128027) (by norm_num)
theorem B7566317 : Blo 2241435 7566317 := bstep (se 3 (by rfl) ⟨1418684, by rfl⟩ : syracuseStep 7566317 = 2837369) B2837369
theorem B5044211 : Blo 2241435 5044211 := bstep (se 1 (by rfl) ⟨3783158, by rfl⟩ : syracuseStep 5044211 = 7566317) B7566317
theorem B3362807 : Blo 2241435 3362807 := bstep (se 1 (by rfl) ⟨2522105, by rfl⟩ : syracuseStep 3362807 = 5044211) B5044211
theorem B2241871 : Blo 2241435 2241871 := bstep (se 1 (by rfl) ⟨1681403, by rfl⟩ : syracuseStep 2241871 = 3362807) B3362807
theorem B3362813 : Blo 2241435 3362813 := bbase (se 3 (by rfl) ⟨630527, by rfl⟩ : syracuseStep 3362813 = 1261055) (by norm_num)
theorem B2241875 : Blo 2241435 2241875 := bstep (se 1 (by rfl) ⟨1681406, by rfl⟩ : syracuseStep 2241875 = 3362813) B3362813
theorem B5044229 : Blo 2241435 5044229 := bbase (se 4 (by rfl) ⟨472896, by rfl⟩ : syracuseStep 5044229 = 945793) (by norm_num)
theorem B3362819 : Blo 2241435 3362819 := bstep (se 1 (by rfl) ⟨2522114, by rfl⟩ : syracuseStep 3362819 = 5044229) B5044229
theorem B2241879 : Blo 2241435 2241879 := bstep (se 1 (by rfl) ⟨1681409, by rfl⟩ : syracuseStep 2241879 = 3362819) B3362819
theorem B4256077 : Blo 2241435 4256077 := bbase (se 3 (by rfl) ⟨798014, by rfl⟩ : syracuseStep 4256077 = 1596029) (by norm_num)
theorem B5674769 : Blo 2241435 5674769 := bstep (se 2 (by rfl) ⟨2128038, by rfl⟩ : syracuseStep 5674769 = 4256077) B4256077
theorem B3783179 : Blo 2241435 3783179 := bstep (se 1 (by rfl) ⟨2837384, by rfl⟩ : syracuseStep 3783179 = 5674769) B5674769
theorem B2522119 : Blo 2241435 2522119 := bstep (se 1 (by rfl) ⟨1891589, by rfl⟩ : syracuseStep 2522119 = 3783179) B3783179
theorem B3362825 : Blo 2241435 3362825 := bstep (se 2 (by rfl) ⟨1261059, by rfl⟩ : syracuseStep 3362825 = 2522119) B2522119
theorem B2241883 : Blo 2241435 2241883 := bstep (se 1 (by rfl) ⟨1681412, by rfl⟩ : syracuseStep 2241883 = 3362825) B3362825
theorem B11349557 : Blo 2241435 11349557 := bbase (se 5 (by rfl) ⟨532010, by rfl⟩ : syracuseStep 11349557 = 1064021) (by norm_num)
theorem B7566371 : Blo 2241435 7566371 := bstep (se 1 (by rfl) ⟨5674778, by rfl⟩ : syracuseStep 7566371 = 11349557) B11349557
theorem B5044247 : Blo 2241435 5044247 := bstep (se 1 (by rfl) ⟨3783185, by rfl⟩ : syracuseStep 5044247 = 7566371) B7566371
theorem B3362831 : Blo 2241435 3362831 := bstep (se 1 (by rfl) ⟨2522123, by rfl⟩ : syracuseStep 3362831 = 5044247) B5044247
theorem B2241887 : Blo 2241435 2241887 := bstep (se 1 (by rfl) ⟨1681415, by rfl⟩ : syracuseStep 2241887 = 3362831) B3362831
theorem B3362837 : Blo 2241435 3362837 := bbase (se 6 (by rfl) ⟨78816, by rfl⟩ : syracuseStep 3362837 = 157633) (by norm_num)
theorem B2241891 : Blo 2241435 2241891 := bstep (se 1 (by rfl) ⟨1681418, by rfl⟩ : syracuseStep 2241891 = 3362837) B3362837
theorem B10773253 : Blo 2241435 10773253 := bbase (se 4 (by rfl) ⟨1009992, by rfl⟩ : syracuseStep 10773253 = 2019985) (by norm_num)
theorem B14364337 : Blo 2241435 14364337 := bstep (se 2 (by rfl) ⟨5386626, by rfl⟩ : syracuseStep 14364337 = 10773253) B10773253
theorem B19152449 : Blo 2241435 19152449 := bstep (se 2 (by rfl) ⟨7182168, by rfl⟩ : syracuseStep 19152449 = 14364337) B14364337
theorem B12768299 : Blo 2241435 12768299 := bstep (se 1 (by rfl) ⟨9576224, by rfl⟩ : syracuseStep 12768299 = 19152449) B19152449
theorem B8512199 : Blo 2241435 8512199 := bstep (se 1 (by rfl) ⟨6384149, by rfl⟩ : syracuseStep 8512199 = 12768299) B12768299
theorem B5674799 : Blo 2241435 5674799 := bstep (se 1 (by rfl) ⟨4256099, by rfl⟩ : syracuseStep 5674799 = 8512199) B8512199
theorem B3783199 : Blo 2241435 3783199 := bstep (se 1 (by rfl) ⟨2837399, by rfl⟩ : syracuseStep 3783199 = 5674799) B5674799
theorem B5044265 : Blo 2241435 5044265 := bstep (se 2 (by rfl) ⟨1891599, by rfl⟩ : syracuseStep 5044265 = 3783199) B3783199
theorem B3362843 : Blo 2241435 3362843 := bstep (se 1 (by rfl) ⟨2522132, by rfl⟩ : syracuseStep 3362843 = 5044265) B5044265
theorem B2241895 : Blo 2241435 2241895 := bstep (se 1 (by rfl) ⟨1681421, by rfl⟩ : syracuseStep 2241895 = 3362843) B3362843
theorem B2522137 : Blo 2241435 2522137 := bbase (se 2 (by rfl) ⟨945801, by rfl⟩ : syracuseStep 2522137 = 1891603) (by norm_num)
theorem B3362849 : Blo 2241435 3362849 := bstep (se 2 (by rfl) ⟨1261068, by rfl⟩ : syracuseStep 3362849 = 2522137) B2522137
theorem B2241899 : Blo 2241435 2241899 := bstep (se 1 (by rfl) ⟨1681424, by rfl⟩ : syracuseStep 2241899 = 3362849) B3362849
theorem B8512229 : Blo 2241435 8512229 := bbase (se 4 (by rfl) ⟨798021, by rfl⟩ : syracuseStep 8512229 = 1596043) (by norm_num)
theorem B5674819 : Blo 2241435 5674819 := bstep (se 1 (by rfl) ⟨4256114, by rfl⟩ : syracuseStep 5674819 = 8512229) B8512229
theorem B7566425 : Blo 2241435 7566425 := bstep (se 2 (by rfl) ⟨2837409, by rfl⟩ : syracuseStep 7566425 = 5674819) B5674819
theorem B5044283 : Blo 2241435 5044283 := bstep (se 1 (by rfl) ⟨3783212, by rfl⟩ : syracuseStep 5044283 = 7566425) B7566425
theorem B3362855 : Blo 2241435 3362855 := bstep (se 1 (by rfl) ⟨2522141, by rfl⟩ : syracuseStep 3362855 = 5044283) B5044283
theorem B2241903 : Blo 2241435 2241903 := bstep (se 1 (by rfl) ⟨1681427, by rfl⟩ : syracuseStep 2241903 = 3362855) B3362855
theorem B3362861 : Blo 2241435 3362861 := bbase (se 3 (by rfl) ⟨630536, by rfl⟩ : syracuseStep 3362861 = 1261073) (by norm_num)
theorem B2241907 : Blo 2241435 2241907 := bstep (se 1 (by rfl) ⟨1681430, by rfl⟩ : syracuseStep 2241907 = 3362861) B3362861
theorem B5044301 : Blo 2241435 5044301 := bbase (se 3 (by rfl) ⟨945806, by rfl⟩ : syracuseStep 5044301 = 1891613) (by norm_num)
theorem B3362867 : Blo 2241435 3362867 := bstep (se 1 (by rfl) ⟨2522150, by rfl⟩ : syracuseStep 3362867 = 5044301) B5044301
theorem B2241911 : Blo 2241435 2241911 := bstep (se 1 (by rfl) ⟨1681433, by rfl⟩ : syracuseStep 2241911 = 3362867) B3362867
theorem B2837425 : Blo 2241435 2837425 := bbase (se 2 (by rfl) ⟨1064034, by rfl⟩ : syracuseStep 2837425 = 2128069) (by norm_num)
theorem B3783233 : Blo 2241435 3783233 := bstep (se 2 (by rfl) ⟨1418712, by rfl⟩ : syracuseStep 3783233 = 2837425) B2837425
theorem B2522155 : Blo 2241435 2522155 := bstep (se 1 (by rfl) ⟨1891616, by rfl⟩ : syracuseStep 2522155 = 3783233) B3783233
theorem B3362873 : Blo 2241435 3362873 := bstep (se 2 (by rfl) ⟨1261077, by rfl⟩ : syracuseStep 3362873 = 2522155) B2522155
theorem B2241915 : Blo 2241435 2241915 := bstep (se 1 (by rfl) ⟨1681436, by rfl⟩ : syracuseStep 2241915 = 3362873) B3362873
theorem B7182245 : Blo 2241435 7182245 := bbase (se 4 (by rfl) ⟨673335, by rfl⟩ : syracuseStep 7182245 = 1346671) (by norm_num)
theorem B4788163 : Blo 2241435 4788163 := bstep (se 1 (by rfl) ⟨3591122, by rfl⟩ : syracuseStep 4788163 = 7182245) B7182245
theorem B25536869 : Blo 2241435 25536869 := bstep (se 4 (by rfl) ⟨2394081, by rfl⟩ : syracuseStep 25536869 = 4788163) B4788163
theorem B17024579 : Blo 2241435 17024579 := bstep (se 1 (by rfl) ⟨12768434, by rfl⟩ : syracuseStep 17024579 = 25536869) B25536869
theorem B11349719 : Blo 2241435 11349719 := bstep (se 1 (by rfl) ⟨8512289, by rfl⟩ : syracuseStep 11349719 = 17024579) B17024579
theorem B7566479 : Blo 2241435 7566479 := bstep (se 1 (by rfl) ⟨5674859, by rfl⟩ : syracuseStep 7566479 = 11349719) B11349719
theorem B5044319 : Blo 2241435 5044319 := bstep (se 1 (by rfl) ⟨3783239, by rfl⟩ : syracuseStep 5044319 = 7566479) B7566479
theorem B3362879 : Blo 2241435 3362879 := bstep (se 1 (by rfl) ⟨2522159, by rfl⟩ : syracuseStep 3362879 = 5044319) B5044319
theorem B2241919 : Blo 2241435 2241919 := bstep (se 1 (by rfl) ⟨1681439, by rfl⟩ : syracuseStep 2241919 = 3362879) B3362879
theorem B3362885 : Blo 2241435 3362885 := bbase (se 4 (by rfl) ⟨315270, by rfl⟩ : syracuseStep 3362885 = 630541) (by norm_num)
theorem B2241923 : Blo 2241435 2241923 := bstep (se 1 (by rfl) ⟨1681442, by rfl⟩ : syracuseStep 2241923 = 3362885) B3362885
theorem B3783253 : Blo 2241435 3783253 := bbase (se 8 (by rfl) ⟨22167, by rfl⟩ : syracuseStep 3783253 = 44335) (by norm_num)
theorem B5044337 : Blo 2241435 5044337 := bstep (se 2 (by rfl) ⟨1891626, by rfl⟩ : syracuseStep 5044337 = 3783253) B3783253
theorem B3362891 : Blo 2241435 3362891 := bstep (se 1 (by rfl) ⟨2522168, by rfl⟩ : syracuseStep 3362891 = 5044337) B5044337
theorem B2241927 : Blo 2241435 2241927 := bstep (se 1 (by rfl) ⟨1681445, by rfl⟩ : syracuseStep 2241927 = 3362891) B3362891
theorem B2522173 : Blo 2241435 2522173 := bbase (se 3 (by rfl) ⟨472907, by rfl⟩ : syracuseStep 2522173 = 945815) (by norm_num)
theorem B3362897 : Blo 2241435 3362897 := bstep (se 2 (by rfl) ⟨1261086, by rfl⟩ : syracuseStep 3362897 = 2522173) B2522173
theorem B2241931 : Blo 2241435 2241931 := bstep (se 1 (by rfl) ⟨1681448, by rfl⟩ : syracuseStep 2241931 = 3362897) B3362897
theorem B7566533 : Blo 2241435 7566533 := bbase (se 4 (by rfl) ⟨709362, by rfl⟩ : syracuseStep 7566533 = 1418725) (by norm_num)
theorem B5044355 : Blo 2241435 5044355 := bstep (se 1 (by rfl) ⟨3783266, by rfl⟩ : syracuseStep 5044355 = 7566533) B7566533
theorem B3362903 : Blo 2241435 3362903 := bstep (se 1 (by rfl) ⟨2522177, by rfl⟩ : syracuseStep 3362903 = 5044355) B5044355
theorem B2241935 : Blo 2241435 2241935 := bstep (se 1 (by rfl) ⟨1681451, by rfl⟩ : syracuseStep 2241935 = 3362903) B3362903
theorem B3362909 : Blo 2241435 3362909 := bbase (se 3 (by rfl) ⟨630545, by rfl⟩ : syracuseStep 3362909 = 1261091) (by norm_num)
theorem B2241939 : Blo 2241435 2241939 := bstep (se 1 (by rfl) ⟨1681454, by rfl⟩ : syracuseStep 2241939 = 3362909) B3362909
theorem B5044373 : Blo 2241435 5044373 := bbase (se 6 (by rfl) ⟨118227, by rfl⟩ : syracuseStep 5044373 = 236455) (by norm_num)
theorem B3362915 : Blo 2241435 3362915 := bstep (se 1 (by rfl) ⟨2522186, by rfl⟩ : syracuseStep 3362915 = 5044373) B5044373
theorem B2241943 : Blo 2241435 2241943 := bstep (se 1 (by rfl) ⟨1681457, by rfl⟩ : syracuseStep 2241943 = 3362915) B3362915
theorem B3192149 : Blo 2241435 3192149 := bbase (se 13 (by rfl) ⟨584, by rfl⟩ : syracuseStep 3192149 = 1169) (by norm_num)
theorem B8512397 : Blo 2241435 8512397 := bstep (se 3 (by rfl) ⟨1596074, by rfl⟩ : syracuseStep 8512397 = 3192149) B3192149
theorem B5674931 : Blo 2241435 5674931 := bstep (se 1 (by rfl) ⟨4256198, by rfl⟩ : syracuseStep 5674931 = 8512397) B8512397
theorem B3783287 : Blo 2241435 3783287 := bstep (se 1 (by rfl) ⟨2837465, by rfl⟩ : syracuseStep 3783287 = 5674931) B5674931
theorem B2522191 : Blo 2241435 2522191 := bstep (se 1 (by rfl) ⟨1891643, by rfl⟩ : syracuseStep 2522191 = 3783287) B3783287
theorem B3362921 : Blo 2241435 3362921 := bstep (se 2 (by rfl) ⟨1261095, by rfl⟩ : syracuseStep 3362921 = 2522191) B2522191
theorem B2241947 : Blo 2241435 2241947 := bstep (se 1 (by rfl) ⟨1681460, by rfl⟩ : syracuseStep 2241947 = 3362921) B3362921
theorem B3030053 : Blo 2241435 3030053 := bbase (se 4 (by rfl) ⟨284067, by rfl⟩ : syracuseStep 3030053 = 568135) (by norm_num)
theorem B32320565 : Blo 2241435 32320565 := bstep (se 5 (by rfl) ⟨1515026, by rfl⟩ : syracuseStep 32320565 = 3030053) B3030053
theorem B21547043 : Blo 2241435 21547043 := bstep (se 1 (by rfl) ⟨16160282, by rfl⟩ : syracuseStep 21547043 = 32320565) B32320565
theorem B14364695 : Blo 2241435 14364695 := bstep (se 1 (by rfl) ⟨10773521, by rfl⟩ : syracuseStep 14364695 = 21547043) B21547043
theorem B9576463 : Blo 2241435 9576463 := bstep (se 1 (by rfl) ⟨7182347, by rfl⟩ : syracuseStep 9576463 = 14364695) B14364695
theorem B12768617 : Blo 2241435 12768617 := bstep (se 2 (by rfl) ⟨4788231, by rfl⟩ : syracuseStep 12768617 = 9576463) B9576463
theorem B8512411 : Blo 2241435 8512411 := bstep (se 1 (by rfl) ⟨6384308, by rfl⟩ : syracuseStep 8512411 = 12768617) B12768617
theorem B11349881 : Blo 2241435 11349881 := bstep (se 2 (by rfl) ⟨4256205, by rfl⟩ : syracuseStep 11349881 = 8512411) B8512411
theorem B7566587 : Blo 2241435 7566587 := bstep (se 1 (by rfl) ⟨5674940, by rfl⟩ : syracuseStep 7566587 = 11349881) B11349881
theorem B5044391 : Blo 2241435 5044391 := bstep (se 1 (by rfl) ⟨3783293, by rfl⟩ : syracuseStep 5044391 = 7566587) B7566587
theorem B3362927 : Blo 2241435 3362927 := bstep (se 1 (by rfl) ⟨2522195, by rfl⟩ : syracuseStep 3362927 = 5044391) B5044391
theorem B2241951 : Blo 2241435 2241951 := bstep (se 1 (by rfl) ⟨1681463, by rfl⟩ : syracuseStep 2241951 = 3362927) B3362927
theorem B3362933 : Blo 2241435 3362933 := bbase (se 5 (by rfl) ⟨157637, by rfl⟩ : syracuseStep 3362933 = 315275) (by norm_num)
theorem B2241955 : Blo 2241435 2241955 := bstep (se 1 (by rfl) ⟨1681466, by rfl⟩ : syracuseStep 2241955 = 3362933) B3362933
theorem B4256221 : Blo 2241435 4256221 := bbase (se 3 (by rfl) ⟨798041, by rfl⟩ : syracuseStep 4256221 = 1596083) (by norm_num)
theorem B5674961 : Blo 2241435 5674961 := bstep (se 2 (by rfl) ⟨2128110, by rfl⟩ : syracuseStep 5674961 = 4256221) B4256221
theorem B3783307 : Blo 2241435 3783307 := bstep (se 1 (by rfl) ⟨2837480, by rfl⟩ : syracuseStep 3783307 = 5674961) B5674961
theorem B5044409 : Blo 2241435 5044409 := bstep (se 2 (by rfl) ⟨1891653, by rfl⟩ : syracuseStep 5044409 = 3783307) B3783307
theorem B3362939 : Blo 2241435 3362939 := bstep (se 1 (by rfl) ⟨2522204, by rfl⟩ : syracuseStep 3362939 = 5044409) B5044409
theorem B2241959 : Blo 2241435 2241959 := bstep (se 1 (by rfl) ⟨1681469, by rfl⟩ : syracuseStep 2241959 = 3362939) B3362939
theorem B2522209 : Blo 2241435 2522209 := bbase (se 2 (by rfl) ⟨945828, by rfl⟩ : syracuseStep 2522209 = 1891657) (by norm_num)
theorem B3362945 : Blo 2241435 3362945 := bstep (se 2 (by rfl) ⟨1261104, by rfl⟩ : syracuseStep 3362945 = 2522209) B2522209
theorem B2241963 : Blo 2241435 2241963 := bstep (se 1 (by rfl) ⟨1681472, by rfl⟩ : syracuseStep 2241963 = 3362945) B3362945
theorem B5674981 : Blo 2241435 5674981 := bbase (se 4 (by rfl) ⟨532029, by rfl⟩ : syracuseStep 5674981 = 1064059) (by norm_num)
theorem B7566641 : Blo 2241435 7566641 := bstep (se 2 (by rfl) ⟨2837490, by rfl⟩ : syracuseStep 7566641 = 5674981) B5674981
theorem B5044427 : Blo 2241435 5044427 := bstep (se 1 (by rfl) ⟨3783320, by rfl⟩ : syracuseStep 5044427 = 7566641) B7566641
theorem B3362951 : Blo 2241435 3362951 := bstep (se 1 (by rfl) ⟨2522213, by rfl⟩ : syracuseStep 3362951 = 5044427) B5044427
theorem B2241967 : Blo 2241435 2241967 := bstep (se 1 (by rfl) ⟨1681475, by rfl⟩ : syracuseStep 2241967 = 3362951) B3362951
theorem B3362957 : Blo 2241435 3362957 := bbase (se 3 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 3362957 = 1261109) (by norm_num)
theorem B2241971 : Blo 2241435 2241971 := bstep (se 1 (by rfl) ⟨1681478, by rfl⟩ : syracuseStep 2241971 = 3362957) B3362957
theorem B5044445 : Blo 2241435 5044445 := bbase (se 3 (by rfl) ⟨945833, by rfl⟩ : syracuseStep 5044445 = 1891667) (by norm_num)
theorem B3362963 : Blo 2241435 3362963 := bstep (se 1 (by rfl) ⟨2522222, by rfl⟩ : syracuseStep 3362963 = 5044445) B5044445
theorem B2241975 : Blo 2241435 2241975 := bstep (se 1 (by rfl) ⟨1681481, by rfl⟩ : syracuseStep 2241975 = 3362963) B3362963
theorem B3783341 : Blo 2241435 3783341 := bbase (se 3 (by rfl) ⟨709376, by rfl⟩ : syracuseStep 3783341 = 1418753) (by norm_num)
theorem B2522227 : Blo 2241435 2522227 := bstep (se 1 (by rfl) ⟨1891670, by rfl⟩ : syracuseStep 2522227 = 3783341) B3783341
theorem B3362969 : Blo 2241435 3362969 := bstep (se 2 (by rfl) ⟨1261113, by rfl⟩ : syracuseStep 3362969 = 2522227) B2522227
theorem B2241979 : Blo 2241435 2241979 := bstep (se 1 (by rfl) ⟨1681484, by rfl⟩ : syracuseStep 2241979 = 3362969) B3362969
theorem B4853629 : Blo 2241435 4853629 := bbase (se 3 (by rfl) ⟨910055, by rfl⟩ : syracuseStep 4853629 = 1820111) (by norm_num)
theorem B6471505 : Blo 2241435 6471505 := bstep (se 2 (by rfl) ⟨2426814, by rfl⟩ : syracuseStep 6471505 = 4853629) B4853629
theorem B8628673 : Blo 2241435 8628673 := bstep (se 2 (by rfl) ⟨3235752, by rfl⟩ : syracuseStep 8628673 = 6471505) B6471505
theorem B11504897 : Blo 2241435 11504897 := bstep (se 2 (by rfl) ⟨4314336, by rfl⟩ : syracuseStep 11504897 = 8628673) B8628673
theorem B7669931 : Blo 2241435 7669931 := bstep (se 1 (by rfl) ⟨5752448, by rfl⟩ : syracuseStep 7669931 = 11504897) B11504897
theorem B20453149 : Blo 2241435 20453149 := bstep (se 3 (by rfl) ⟨3834965, by rfl⟩ : syracuseStep 20453149 = 7669931) B7669931
theorem B27270865 : Blo 2241435 27270865 := bstep (se 2 (by rfl) ⟨10226574, by rfl⟩ : syracuseStep 27270865 = 20453149) B20453149
theorem B36361153 : Blo 2241435 36361153 := bstep (se 2 (by rfl) ⟨13635432, by rfl⟩ : syracuseStep 36361153 = 27270865) B27270865
theorem B48481537 : Blo 2241435 48481537 := bstep (se 2 (by rfl) ⟨18180576, by rfl⟩ : syracuseStep 48481537 = 36361153) B36361153
theorem B64642049 : Blo 2241435 64642049 := bstep (se 2 (by rfl) ⟨24240768, by rfl⟩ : syracuseStep 64642049 = 48481537) B48481537
theorem B43094699 : Blo 2241435 43094699 := bstep (se 1 (by rfl) ⟨32321024, by rfl⟩ : syracuseStep 43094699 = 64642049) B64642049
theorem B28729799 : Blo 2241435 28729799 := bstep (se 1 (by rfl) ⟨21547349, by rfl⟩ : syracuseStep 28729799 = 43094699) B43094699
theorem B19153199 : Blo 2241435 19153199 := bstep (se 1 (by rfl) ⟨14364899, by rfl⟩ : syracuseStep 19153199 = 28729799) B28729799
theorem B12768799 : Blo 2241435 12768799 := bstep (se 1 (by rfl) ⟨9576599, by rfl⟩ : syracuseStep 12768799 = 19153199) B19153199
theorem B17025065 : Blo 2241435 17025065 := bstep (se 2 (by rfl) ⟨6384399, by rfl⟩ : syracuseStep 17025065 = 12768799) B12768799
theorem B11350043 : Blo 2241435 11350043 := bstep (se 1 (by rfl) ⟨8512532, by rfl⟩ : syracuseStep 11350043 = 17025065) B17025065
theorem B7566695 : Blo 2241435 7566695 := bstep (se 1 (by rfl) ⟨5675021, by rfl⟩ : syracuseStep 7566695 = 11350043) B11350043
theorem B5044463 : Blo 2241435 5044463 := bstep (se 1 (by rfl) ⟨3783347, by rfl⟩ : syracuseStep 5044463 = 7566695) B7566695
theorem B3362975 : Blo 2241435 3362975 := bstep (se 1 (by rfl) ⟨2522231, by rfl⟩ : syracuseStep 3362975 = 5044463) B5044463
theorem B2241983 : Blo 2241435 2241983 := bstep (se 1 (by rfl) ⟨1681487, by rfl⟩ : syracuseStep 2241983 = 3362975) B3362975
theorem B3362981 : Blo 2241435 3362981 := bbase (se 4 (by rfl) ⟨315279, by rfl⟩ : syracuseStep 3362981 = 630559) (by norm_num)
theorem B2241987 : Blo 2241435 2241987 := bstep (se 1 (by rfl) ⟨1681490, by rfl⟩ : syracuseStep 2241987 = 3362981) B3362981
theorem B2837521 : Blo 2241435 2837521 := bbase (se 2 (by rfl) ⟨1064070, by rfl⟩ : syracuseStep 2837521 = 2128141) (by norm_num)
theorem B3783361 : Blo 2241435 3783361 := bstep (se 2 (by rfl) ⟨1418760, by rfl⟩ : syracuseStep 3783361 = 2837521) B2837521
theorem B5044481 : Blo 2241435 5044481 := bstep (se 2 (by rfl) ⟨1891680, by rfl⟩ : syracuseStep 5044481 = 3783361) B3783361
theorem B3362987 : Blo 2241435 3362987 := bstep (se 1 (by rfl) ⟨2522240, by rfl⟩ : syracuseStep 3362987 = 5044481) B5044481
theorem B2241991 : Blo 2241435 2241991 := bstep (se 1 (by rfl) ⟨1681493, by rfl⟩ : syracuseStep 2241991 = 3362987) B3362987
theorem B2522245 : Blo 2241435 2522245 := bbase (se 4 (by rfl) ⟨236460, by rfl⟩ : syracuseStep 2522245 = 472921) (by norm_num)
theorem B3362993 : Blo 2241435 3362993 := bstep (se 2 (by rfl) ⟨1261122, by rfl⟩ : syracuseStep 3362993 = 2522245) B2522245
theorem B2241995 : Blo 2241435 2241995 := bstep (se 1 (by rfl) ⟨1681496, by rfl⟩ : syracuseStep 2241995 = 3362993) B3362993
theorem B3071461 : Blo 2241435 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B4095281 : Blo 2241435 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B2730187 : Blo 2241435 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B3640249 : Blo 2241435 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B4853665 : Blo 2241435 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B25886213 : Blo 2241435 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B17257475 : Blo 2241435 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B46019933 : Blo 2241435 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B30679955 : Blo 2241435 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B20453303 : Blo 2241435 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B13635535 : Blo 2241435 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B18180713 : Blo 2241435 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B12120475 : Blo 2241435 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B16160633 : Blo 2241435 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B10773755 : Blo 2241435 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B7182503 : Blo 2241435 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B4788335 : Blo 2241435 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B3192223 : Blo 2241435 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B4256297 : Blo 2241435 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B2837531 : Blo 2241435 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B7566749 : Blo 2241435 7566749 := bstep (se 3 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 7566749 = 2837531) B2837531
theorem B5044499 : Blo 2241435 5044499 := bstep (se 1 (by rfl) ⟨3783374, by rfl⟩ : syracuseStep 5044499 = 7566749) B7566749
theorem B3362999 : Blo 2241435 3362999 := bstep (se 1 (by rfl) ⟨2522249, by rfl⟩ : syracuseStep 3362999 = 5044499) B5044499
theorem B2241999 : Blo 2241435 2241999 := bstep (se 1 (by rfl) ⟨1681499, by rfl⟩ : syracuseStep 2241999 = 3362999) B3362999
theorem B3363005 : Blo 2241435 3363005 := bbase (se 3 (by rfl) ⟨630563, by rfl⟩ : syracuseStep 3363005 = 1261127) (by norm_num)
theorem B2242003 : Blo 2241435 2242003 := bstep (se 1 (by rfl) ⟨1681502, by rfl⟩ : syracuseStep 2242003 = 3363005) B3363005
theorem B5044517 : Blo 2241435 5044517 := bbase (se 4 (by rfl) ⟨472923, by rfl⟩ : syracuseStep 5044517 = 945847) (by norm_num)
theorem B3363011 : Blo 2241435 3363011 := bstep (se 1 (by rfl) ⟨2522258, by rfl⟩ : syracuseStep 3363011 = 5044517) B5044517
theorem B2242007 : Blo 2241435 2242007 := bstep (se 1 (by rfl) ⟨1681505, by rfl⟩ : syracuseStep 2242007 = 3363011) B3363011
theorem B5675093 : Blo 2241435 5675093 := bbase (se 8 (by rfl) ⟨33252, by rfl⟩ : syracuseStep 5675093 = 66505) (by norm_num)
theorem B3783395 : Blo 2241435 3783395 := bstep (se 1 (by rfl) ⟨2837546, by rfl⟩ : syracuseStep 3783395 = 5675093) B5675093
theorem B2522263 : Blo 2241435 2522263 := bstep (se 1 (by rfl) ⟨1891697, by rfl⟩ : syracuseStep 2522263 = 3783395) B3783395
theorem B3363017 : Blo 2241435 3363017 := bstep (se 2 (by rfl) ⟨1261131, by rfl⟩ : syracuseStep 3363017 = 2522263) B2522263
theorem B2242011 : Blo 2241435 2242011 := bstep (se 1 (by rfl) ⟨1681508, by rfl⟩ : syracuseStep 2242011 = 3363017) B3363017
theorem B8080373 : Blo 2241435 8080373 := bbase (se 5 (by rfl) ⟨378767, by rfl⟩ : syracuseStep 8080373 = 757535) (by norm_num)
theorem B5386915 : Blo 2241435 5386915 := bstep (se 1 (by rfl) ⟨4040186, by rfl⟩ : syracuseStep 5386915 = 8080373) B8080373
theorem B7182553 : Blo 2241435 7182553 := bstep (se 2 (by rfl) ⟨2693457, by rfl⟩ : syracuseStep 7182553 = 5386915) B5386915
theorem B9576737 : Blo 2241435 9576737 := bstep (se 2 (by rfl) ⟨3591276, by rfl⟩ : syracuseStep 9576737 = 7182553) B7182553
theorem B6384491 : Blo 2241435 6384491 := bstep (se 1 (by rfl) ⟨4788368, by rfl⟩ : syracuseStep 6384491 = 9576737) B9576737
theorem B4256327 : Blo 2241435 4256327 := bstep (se 1 (by rfl) ⟨3192245, by rfl⟩ : syracuseStep 4256327 = 6384491) B6384491
theorem B11350205 : Blo 2241435 11350205 := bstep (se 3 (by rfl) ⟨2128163, by rfl⟩ : syracuseStep 11350205 = 4256327) B4256327
theorem B7566803 : Blo 2241435 7566803 := bstep (se 1 (by rfl) ⟨5675102, by rfl⟩ : syracuseStep 7566803 = 11350205) B11350205
theorem B5044535 : Blo 2241435 5044535 := bstep (se 1 (by rfl) ⟨3783401, by rfl⟩ : syracuseStep 5044535 = 7566803) B7566803
theorem B3363023 : Blo 2241435 3363023 := bstep (se 1 (by rfl) ⟨2522267, by rfl⟩ : syracuseStep 3363023 = 5044535) B5044535
theorem B2242015 : Blo 2241435 2242015 := bstep (se 1 (by rfl) ⟨1681511, by rfl⟩ : syracuseStep 2242015 = 3363023) B3363023
theorem B3363029 : Blo 2241435 3363029 := bbase (se 7 (by rfl) ⟨39410, by rfl⟩ : syracuseStep 3363029 = 78821) (by norm_num)
theorem B2242019 : Blo 2241435 2242019 := bstep (se 1 (by rfl) ⟨1681514, by rfl⟩ : syracuseStep 2242019 = 3363029) B3363029
theorem B2394193 : Blo 2241435 2394193 := bbase (se 2 (by rfl) ⟨897822, by rfl⟩ : syracuseStep 2394193 = 1795645) (by norm_num)
theorem B3192257 : Blo 2241435 3192257 := bstep (se 2 (by rfl) ⟨1197096, by rfl⟩ : syracuseStep 3192257 = 2394193) B2394193
theorem B8512685 : Blo 2241435 8512685 := bstep (se 3 (by rfl) ⟨1596128, by rfl⟩ : syracuseStep 8512685 = 3192257) B3192257
theorem B5675123 : Blo 2241435 5675123 := bstep (se 1 (by rfl) ⟨4256342, by rfl⟩ : syracuseStep 5675123 = 8512685) B8512685
theorem B3783415 : Blo 2241435 3783415 := bstep (se 1 (by rfl) ⟨2837561, by rfl⟩ : syracuseStep 3783415 = 5675123) B5675123
theorem B5044553 : Blo 2241435 5044553 := bstep (se 2 (by rfl) ⟨1891707, by rfl⟩ : syracuseStep 5044553 = 3783415) B3783415
theorem B3363035 : Blo 2241435 3363035 := bstep (se 1 (by rfl) ⟨2522276, by rfl⟩ : syracuseStep 3363035 = 5044553) B5044553
theorem B2242023 : Blo 2241435 2242023 := bstep (se 1 (by rfl) ⟨1681517, by rfl⟩ : syracuseStep 2242023 = 3363035) B3363035
theorem B2522281 : Blo 2241435 2522281 := bbase (se 2 (by rfl) ⟨945855, by rfl⟩ : syracuseStep 2522281 = 1891711) (by norm_num)
theorem B3363041 : Blo 2241435 3363041 := bstep (se 2 (by rfl) ⟨1261140, by rfl⟩ : syracuseStep 3363041 = 2522281) B2522281
theorem B2242027 : Blo 2241435 2242027 := bstep (se 1 (by rfl) ⟨1681520, by rfl⟩ : syracuseStep 2242027 = 3363041) B3363041
theorem B9576805 : Blo 2241435 9576805 := bbase (se 4 (by rfl) ⟨897825, by rfl⟩ : syracuseStep 9576805 = 1795651) (by norm_num)
theorem B12769073 : Blo 2241435 12769073 := bstep (se 2 (by rfl) ⟨4788402, by rfl⟩ : syracuseStep 12769073 = 9576805) B9576805
theorem B8512715 : Blo 2241435 8512715 := bstep (se 1 (by rfl) ⟨6384536, by rfl⟩ : syracuseStep 8512715 = 12769073) B12769073
theorem B5675143 : Blo 2241435 5675143 := bstep (se 1 (by rfl) ⟨4256357, by rfl⟩ : syracuseStep 5675143 = 8512715) B8512715
theorem B7566857 : Blo 2241435 7566857 := bstep (se 2 (by rfl) ⟨2837571, by rfl⟩ : syracuseStep 7566857 = 5675143) B5675143
theorem B5044571 : Blo 2241435 5044571 := bstep (se 1 (by rfl) ⟨3783428, by rfl⟩ : syracuseStep 5044571 = 7566857) B7566857
theorem B3363047 : Blo 2241435 3363047 := bstep (se 1 (by rfl) ⟨2522285, by rfl⟩ : syracuseStep 3363047 = 5044571) B5044571
theorem B2242031 : Blo 2241435 2242031 := bstep (se 1 (by rfl) ⟨1681523, by rfl⟩ : syracuseStep 2242031 = 3363047) B3363047
theorem B3363053 : Blo 2241435 3363053 := bbase (se 3 (by rfl) ⟨630572, by rfl⟩ : syracuseStep 3363053 = 1261145) (by norm_num)
theorem B2242035 : Blo 2241435 2242035 := bstep (se 1 (by rfl) ⟨1681526, by rfl⟩ : syracuseStep 2242035 = 3363053) B3363053
theorem B5044589 : Blo 2241435 5044589 := bbase (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) (by norm_num)
theorem B3363059 : Blo 2241435 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B2242039 : Blo 2241435 2242039 := bstep (se 1 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 2242039 = 3363059) B3363059
theorem B4256381 : Blo 2241435 4256381 := bbase (se 3 (by rfl) ⟨798071, by rfl⟩ : syracuseStep 4256381 = 1596143) (by norm_num)
theorem B2837587 : Blo 2241435 2837587 := bstep (se 1 (by rfl) ⟨2128190, by rfl⟩ : syracuseStep 2837587 = 4256381) B4256381
theorem B3783449 : Blo 2241435 3783449 := bstep (se 2 (by rfl) ⟨1418793, by rfl⟩ : syracuseStep 3783449 = 2837587) B2837587
theorem B2522299 : Blo 2241435 2522299 := bstep (se 1 (by rfl) ⟨1891724, by rfl⟩ : syracuseStep 2522299 = 3783449) B3783449
theorem B3363065 : Blo 2241435 3363065 := bstep (se 2 (by rfl) ⟨1261149, by rfl⟩ : syracuseStep 3363065 = 2522299) B2522299
theorem B2242043 : Blo 2241435 2242043 := bstep (se 1 (by rfl) ⟨1681532, by rfl⟩ : syracuseStep 2242043 = 3363065) B3363065
theorem B4670149 : Blo 2241435 4670149 := bbase (se 4 (by rfl) ⟨437826, by rfl⟩ : syracuseStep 4670149 = 875653) (by norm_num)
theorem B6226865 : Blo 2241435 6226865 := bstep (se 2 (by rfl) ⟨2335074, by rfl⟩ : syracuseStep 6226865 = 4670149) B4670149
theorem B4151243 : Blo 2241435 4151243 := bstep (se 1 (by rfl) ⟨3113432, by rfl⟩ : syracuseStep 4151243 = 6226865) B6226865
theorem B2767495 : Blo 2241435 2767495 := bstep (se 1 (by rfl) ⟨2075621, by rfl⟩ : syracuseStep 2767495 = 4151243) B4151243
theorem B3689993 : Blo 2241435 3689993 := bstep (se 2 (by rfl) ⟨1383747, by rfl⟩ : syracuseStep 3689993 = 2767495) B2767495
theorem B9839981 : Blo 2241435 9839981 := bstep (se 3 (by rfl) ⟨1844996, by rfl⟩ : syracuseStep 9839981 = 3689993) B3689993
theorem B6559987 : Blo 2241435 6559987 := bstep (se 1 (by rfl) ⟨4919990, by rfl⟩ : syracuseStep 6559987 = 9839981) B9839981
theorem B8746649 : Blo 2241435 8746649 := bstep (se 2 (by rfl) ⟨3279993, by rfl⟩ : syracuseStep 8746649 = 6559987) B6559987
theorem B5831099 : Blo 2241435 5831099 := bstep (se 1 (by rfl) ⟨4373324, by rfl⟩ : syracuseStep 5831099 = 8746649) B8746649
theorem B3887399 : Blo 2241435 3887399 := bstep (se 1 (by rfl) ⟨2915549, by rfl⟩ : syracuseStep 3887399 = 5831099) B5831099
theorem B10366397 : Blo 2241435 10366397 := bstep (se 3 (by rfl) ⟨1943699, by rfl⟩ : syracuseStep 10366397 = 3887399) B3887399
theorem B6910931 : Blo 2241435 6910931 := bstep (se 1 (by rfl) ⟨5183198, by rfl⟩ : syracuseStep 6910931 = 10366397) B10366397
theorem B18429149 : Blo 2241435 18429149 := bstep (se 3 (by rfl) ⟨3455465, by rfl⟩ : syracuseStep 18429149 = 6910931) B6910931
theorem B12286099 : Blo 2241435 12286099 := bstep (se 1 (by rfl) ⟨9214574, by rfl⟩ : syracuseStep 12286099 = 18429149) B18429149
theorem B65525861 : Blo 2241435 65525861 := bstep (se 4 (by rfl) ⟨6143049, by rfl⟩ : syracuseStep 65525861 = 12286099) B12286099
theorem B174735629 : Blo 2241435 174735629 := bstep (se 3 (by rfl) ⟨32762930, by rfl⟩ : syracuseStep 174735629 = 65525861) B65525861
theorem B116490419 : Blo 2241435 116490419 := bstep (se 1 (by rfl) ⟨87367814, by rfl⟩ : syracuseStep 116490419 = 174735629) B174735629
theorem B77660279 : Blo 2241435 77660279 := bstep (se 1 (by rfl) ⟨58245209, by rfl⟩ : syracuseStep 77660279 = 116490419) B116490419
theorem B51773519 : Blo 2241435 51773519 := bstep (se 1 (by rfl) ⟨38830139, by rfl⟩ : syracuseStep 51773519 = 77660279) B77660279
theorem B34515679 : Blo 2241435 34515679 := bstep (se 1 (by rfl) ⟨25886759, by rfl⟩ : syracuseStep 34515679 = 51773519) B51773519
theorem B46020905 : Blo 2241435 46020905 := bstep (se 2 (by rfl) ⟨17257839, by rfl⟩ : syracuseStep 46020905 = 34515679) B34515679
theorem B30680603 : Blo 2241435 30680603 := bstep (se 1 (by rfl) ⟨23010452, by rfl⟩ : syracuseStep 30680603 = 46020905) B46020905
theorem B20453735 : Blo 2241435 20453735 := bstep (se 1 (by rfl) ⟨15340301, by rfl⟩ : syracuseStep 20453735 = 30680603) B30680603
theorem B13635823 : Blo 2241435 13635823 := bstep (se 1 (by rfl) ⟨10226867, by rfl⟩ : syracuseStep 13635823 = 20453735) B20453735
theorem B18181097 : Blo 2241435 18181097 := bstep (se 2 (by rfl) ⟨6817911, by rfl⟩ : syracuseStep 18181097 = 13635823) B13635823
theorem B12120731 : Blo 2241435 12120731 := bstep (se 1 (by rfl) ⟨9090548, by rfl⟩ : syracuseStep 12120731 = 18181097) B18181097
theorem B8080487 : Blo 2241435 8080487 := bstep (se 1 (by rfl) ⟨6060365, by rfl⟩ : syracuseStep 8080487 = 12120731) B12120731
theorem B5386991 : Blo 2241435 5386991 := bstep (se 1 (by rfl) ⟨4040243, by rfl⟩ : syracuseStep 5386991 = 8080487) B8080487
theorem B57461237 : Blo 2241435 57461237 := bstep (se 5 (by rfl) ⟨2693495, by rfl⟩ : syracuseStep 57461237 = 5386991) B5386991
theorem B38307491 : Blo 2241435 38307491 := bstep (se 1 (by rfl) ⟨28730618, by rfl⟩ : syracuseStep 38307491 = 57461237) B57461237
theorem B25538327 : Blo 2241435 25538327 := bstep (se 1 (by rfl) ⟨19153745, by rfl⟩ : syracuseStep 25538327 = 38307491) B38307491
theorem B17025551 : Blo 2241435 17025551 := bstep (se 1 (by rfl) ⟨12769163, by rfl⟩ : syracuseStep 17025551 = 25538327) B25538327
theorem B11350367 : Blo 2241435 11350367 := bstep (se 1 (by rfl) ⟨8512775, by rfl⟩ : syracuseStep 11350367 = 17025551) B17025551
theorem B7566911 : Blo 2241435 7566911 := bstep (se 1 (by rfl) ⟨5675183, by rfl⟩ : syracuseStep 7566911 = 11350367) B11350367
theorem B5044607 : Blo 2241435 5044607 := bstep (se 1 (by rfl) ⟨3783455, by rfl⟩ : syracuseStep 5044607 = 7566911) B7566911
theorem B3363071 : Blo 2241435 3363071 := bstep (se 1 (by rfl) ⟨2522303, by rfl⟩ : syracuseStep 3363071 = 5044607) B5044607
theorem B2242047 : Blo 2241435 2242047 := bstep (se 1 (by rfl) ⟨1681535, by rfl⟩ : syracuseStep 2242047 = 3363071) B3363071
theorem B3363077 : Blo 2241435 3363077 := bbase (se 4 (by rfl) ⟨315288, by rfl⟩ : syracuseStep 3363077 = 630577) (by norm_num)
theorem B2242051 : Blo 2241435 2242051 := bstep (se 1 (by rfl) ⟨1681538, by rfl⟩ : syracuseStep 2242051 = 3363077) B3363077
theorem B3783469 : Blo 2241435 3783469 := bbase (se 3 (by rfl) ⟨709400, by rfl⟩ : syracuseStep 3783469 = 1418801) (by norm_num)
theorem B5044625 : Blo 2241435 5044625 := bstep (se 2 (by rfl) ⟨1891734, by rfl⟩ : syracuseStep 5044625 = 3783469) B3783469
theorem B3363083 : Blo 2241435 3363083 := bstep (se 1 (by rfl) ⟨2522312, by rfl⟩ : syracuseStep 3363083 = 5044625) B5044625
theorem B2242055 : Blo 2241435 2242055 := bstep (se 1 (by rfl) ⟨1681541, by rfl⟩ : syracuseStep 2242055 = 3363083) B3363083
theorem B2522317 : Blo 2241435 2522317 := bbase (se 3 (by rfl) ⟨472934, by rfl⟩ : syracuseStep 2522317 = 945869) (by norm_num)
theorem B3363089 : Blo 2241435 3363089 := bstep (se 2 (by rfl) ⟨1261158, by rfl⟩ : syracuseStep 3363089 = 2522317) B2522317
theorem B2242059 : Blo 2241435 2242059 := bstep (se 1 (by rfl) ⟨1681544, by rfl⟩ : syracuseStep 2242059 = 3363089) B3363089
theorem B7566965 : Blo 2241435 7566965 := bbase (se 5 (by rfl) ⟨354701, by rfl⟩ : syracuseStep 7566965 = 709403) (by norm_num)
theorem B5044643 : Blo 2241435 5044643 := bstep (se 1 (by rfl) ⟨3783482, by rfl⟩ : syracuseStep 5044643 = 7566965) B7566965
theorem B3363095 : Blo 2241435 3363095 := bstep (se 1 (by rfl) ⟨2522321, by rfl⟩ : syracuseStep 3363095 = 5044643) B5044643
theorem B2242063 : Blo 2241435 2242063 := bstep (se 1 (by rfl) ⟨1681547, by rfl⟩ : syracuseStep 2242063 = 3363095) B3363095
theorem B3363101 : Blo 2241435 3363101 := bbase (se 3 (by rfl) ⟨630581, by rfl⟩ : syracuseStep 3363101 = 1261163) (by norm_num)
theorem B2242067 : Blo 2241435 2242067 := bstep (se 1 (by rfl) ⟨1681550, by rfl⟩ : syracuseStep 2242067 = 3363101) B3363101
theorem B5044661 : Blo 2241435 5044661 := bbase (se 5 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 5044661 = 472937) (by norm_num)
theorem B3363107 : Blo 2241435 3363107 := bstep (se 1 (by rfl) ⟨2522330, by rfl⟩ : syracuseStep 3363107 = 5044661) B5044661
theorem B2242071 : Blo 2241435 2242071 := bstep (se 1 (by rfl) ⟨1681553, by rfl⟩ : syracuseStep 2242071 = 3363107) B3363107
theorem B3591373 : Blo 2241435 3591373 := bbase (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) (by norm_num)
theorem B4788497 : Blo 2241435 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B12769325 : Blo 2241435 12769325 := bstep (se 3 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 12769325 = 4788497) B4788497
theorem B8512883 : Blo 2241435 8512883 := bstep (se 1 (by rfl) ⟨6384662, by rfl⟩ : syracuseStep 8512883 = 12769325) B12769325
theorem B5675255 : Blo 2241435 5675255 := bstep (se 1 (by rfl) ⟨4256441, by rfl⟩ : syracuseStep 5675255 = 8512883) B8512883
theorem B3783503 : Blo 2241435 3783503 := bstep (se 1 (by rfl) ⟨2837627, by rfl⟩ : syracuseStep 3783503 = 5675255) B5675255
theorem B2522335 : Blo 2241435 2522335 := bstep (se 1 (by rfl) ⟨1891751, by rfl⟩ : syracuseStep 2522335 = 3783503) B3783503
theorem B3363113 : Blo 2241435 3363113 := bstep (se 2 (by rfl) ⟨1261167, by rfl⟩ : syracuseStep 3363113 = 2522335) B2522335
theorem B2242075 : Blo 2241435 2242075 := bstep (se 1 (by rfl) ⟨1681556, by rfl⟩ : syracuseStep 2242075 = 3363113) B3363113
theorem B5387069 : Blo 2241435 5387069 := bbase (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) (by norm_num)
theorem B3591379 : Blo 2241435 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B4788505 : Blo 2241435 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B6384673 : Blo 2241435 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B8512897 : Blo 2241435 8512897 := bstep (se 2 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 8512897 = 6384673) B6384673
theorem B11350529 : Blo 2241435 11350529 := bstep (se 2 (by rfl) ⟨4256448, by rfl⟩ : syracuseStep 11350529 = 8512897) B8512897
theorem B7567019 : Blo 2241435 7567019 := bstep (se 1 (by rfl) ⟨5675264, by rfl⟩ : syracuseStep 7567019 = 11350529) B11350529
theorem B5044679 : Blo 2241435 5044679 := bstep (se 1 (by rfl) ⟨3783509, by rfl⟩ : syracuseStep 5044679 = 7567019) B7567019
theorem B3363119 : Blo 2241435 3363119 := bstep (se 1 (by rfl) ⟨2522339, by rfl⟩ : syracuseStep 3363119 = 5044679) B5044679
theorem B2242079 : Blo 2241435 2242079 := bstep (se 1 (by rfl) ⟨1681559, by rfl⟩ : syracuseStep 2242079 = 3363119) B3363119
theorem B3363125 : Blo 2241435 3363125 := bbase (se 5 (by rfl) ⟨157646, by rfl⟩ : syracuseStep 3363125 = 315293) (by norm_num)
theorem B2242083 : Blo 2241435 2242083 := bstep (se 1 (by rfl) ⟨1681562, by rfl⟩ : syracuseStep 2242083 = 3363125) B3363125
theorem B5675285 : Blo 2241435 5675285 := bbase (se 6 (by rfl) ⟨133014, by rfl⟩ : syracuseStep 5675285 = 266029) (by norm_num)
theorem B3783523 : Blo 2241435 3783523 := bstep (se 1 (by rfl) ⟨2837642, by rfl⟩ : syracuseStep 3783523 = 5675285) B5675285
theorem B5044697 : Blo 2241435 5044697 := bstep (se 2 (by rfl) ⟨1891761, by rfl⟩ : syracuseStep 5044697 = 3783523) B3783523
theorem B3363131 : Blo 2241435 3363131 := bstep (se 1 (by rfl) ⟨2522348, by rfl⟩ : syracuseStep 3363131 = 5044697) B5044697
theorem B2242087 : Blo 2241435 2242087 := bstep (se 1 (by rfl) ⟨1681565, by rfl⟩ : syracuseStep 2242087 = 3363131) B3363131
theorem B2522353 : Blo 2241435 2522353 := bbase (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) (by norm_num)
theorem B3363137 : Blo 2241435 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B2242091 : Blo 2241435 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B8080661 : Blo 2241435 8080661 := bbase (se 6 (by rfl) ⟨189390, by rfl⟩ : syracuseStep 8080661 = 378781) (by norm_num)
theorem B21548429 : Blo 2241435 21548429 := bstep (se 3 (by rfl) ⟨4040330, by rfl⟩ : syracuseStep 21548429 = 8080661) B8080661
theorem B14365619 : Blo 2241435 14365619 := bstep (se 1 (by rfl) ⟨10774214, by rfl⟩ : syracuseStep 14365619 = 21548429) B21548429
theorem B9577079 : Blo 2241435 9577079 := bstep (se 1 (by rfl) ⟨7182809, by rfl⟩ : syracuseStep 9577079 = 14365619) B14365619
theorem B6384719 : Blo 2241435 6384719 := bstep (se 1 (by rfl) ⟨4788539, by rfl⟩ : syracuseStep 6384719 = 9577079) B9577079
theorem B4256479 : Blo 2241435 4256479 := bstep (se 1 (by rfl) ⟨3192359, by rfl⟩ : syracuseStep 4256479 = 6384719) B6384719
theorem B5675305 : Blo 2241435 5675305 := bstep (se 2 (by rfl) ⟨2128239, by rfl⟩ : syracuseStep 5675305 = 4256479) B4256479
theorem B7567073 : Blo 2241435 7567073 := bstep (se 2 (by rfl) ⟨2837652, by rfl⟩ : syracuseStep 7567073 = 5675305) B5675305
theorem B5044715 : Blo 2241435 5044715 := bstep (se 1 (by rfl) ⟨3783536, by rfl⟩ : syracuseStep 5044715 = 7567073) B7567073
theorem B3363143 : Blo 2241435 3363143 := bstep (se 1 (by rfl) ⟨2522357, by rfl⟩ : syracuseStep 3363143 = 5044715) B5044715
theorem B2242095 : Blo 2241435 2242095 := bstep (se 1 (by rfl) ⟨1681571, by rfl⟩ : syracuseStep 2242095 = 3363143) B3363143
theorem B3363149 : Blo 2241435 3363149 := bbase (se 3 (by rfl) ⟨630590, by rfl⟩ : syracuseStep 3363149 = 1261181) (by norm_num)
theorem B2242099 : Blo 2241435 2242099 := bstep (se 1 (by rfl) ⟨1681574, by rfl⟩ : syracuseStep 2242099 = 3363149) B3363149
theorem B5044733 : Blo 2241435 5044733 := bbase (se 3 (by rfl) ⟨945887, by rfl⟩ : syracuseStep 5044733 = 1891775) (by norm_num)
theorem B3363155 : Blo 2241435 3363155 := bstep (se 1 (by rfl) ⟨2522366, by rfl⟩ : syracuseStep 3363155 = 5044733) B5044733
theorem B2242103 : Blo 2241435 2242103 := bstep (se 1 (by rfl) ⟨1681577, by rfl⟩ : syracuseStep 2242103 = 3363155) B3363155
theorem B3783557 : Blo 2241435 3783557 := bbase (se 4 (by rfl) ⟨354708, by rfl⟩ : syracuseStep 3783557 = 709417) (by norm_num)
theorem B2522371 : Blo 2241435 2522371 := bstep (se 1 (by rfl) ⟨1891778, by rfl⟩ : syracuseStep 2522371 = 3783557) B3783557
theorem B3363161 : Blo 2241435 3363161 := bstep (se 2 (by rfl) ⟨1261185, by rfl⟩ : syracuseStep 3363161 = 2522371) B2522371
theorem B2242107 : Blo 2241435 2242107 := bstep (se 1 (by rfl) ⟨1681580, by rfl⟩ : syracuseStep 2242107 = 3363161) B3363161
theorem B17026037 : Blo 2241435 17026037 := bbase (se 5 (by rfl) ⟨798095, by rfl⟩ : syracuseStep 17026037 = 1596191) (by norm_num)
theorem B11350691 : Blo 2241435 11350691 := bstep (se 1 (by rfl) ⟨8513018, by rfl⟩ : syracuseStep 11350691 = 17026037) B17026037
theorem B7567127 : Blo 2241435 7567127 := bstep (se 1 (by rfl) ⟨5675345, by rfl⟩ : syracuseStep 7567127 = 11350691) B11350691
theorem B5044751 : Blo 2241435 5044751 := bstep (se 1 (by rfl) ⟨3783563, by rfl⟩ : syracuseStep 5044751 = 7567127) B7567127
theorem B3363167 : Blo 2241435 3363167 := bstep (se 1 (by rfl) ⟨2522375, by rfl⟩ : syracuseStep 3363167 = 5044751) B5044751
theorem B2242111 : Blo 2241435 2242111 := bstep (se 1 (by rfl) ⟨1681583, by rfl⟩ : syracuseStep 2242111 = 3363167) B3363167
theorem B3363173 : Blo 2241435 3363173 := bbase (se 4 (by rfl) ⟨315297, by rfl⟩ : syracuseStep 3363173 = 630595) (by norm_num)
theorem B2242115 : Blo 2241435 2242115 := bstep (se 1 (by rfl) ⟨1681586, by rfl⟩ : syracuseStep 2242115 = 3363173) B3363173
theorem B4256525 : Blo 2241435 4256525 := bbase (se 3 (by rfl) ⟨798098, by rfl⟩ : syracuseStep 4256525 = 1596197) (by norm_num)
theorem B2837683 : Blo 2241435 2837683 := bstep (se 1 (by rfl) ⟨2128262, by rfl⟩ : syracuseStep 2837683 = 4256525) B4256525
theorem B3783577 : Blo 2241435 3783577 := bstep (se 2 (by rfl) ⟨1418841, by rfl⟩ : syracuseStep 3783577 = 2837683) B2837683
theorem B5044769 : Blo 2241435 5044769 := bstep (se 2 (by rfl) ⟨1891788, by rfl⟩ : syracuseStep 5044769 = 3783577) B3783577
theorem B3363179 : Blo 2241435 3363179 := bstep (se 1 (by rfl) ⟨2522384, by rfl⟩ : syracuseStep 3363179 = 5044769) B5044769
theorem B2242119 : Blo 2241435 2242119 := bstep (se 1 (by rfl) ⟨1681589, by rfl⟩ : syracuseStep 2242119 = 3363179) B3363179
theorem B2522389 : Blo 2241435 2522389 := bbase (se 6 (by rfl) ⟨59118, by rfl⟩ : syracuseStep 2522389 = 118237) (by norm_num)
theorem B3363185 : Blo 2241435 3363185 := bstep (se 2 (by rfl) ⟨1261194, by rfl⟩ : syracuseStep 3363185 = 2522389) B2522389
theorem B2242123 : Blo 2241435 2242123 := bstep (se 1 (by rfl) ⟨1681592, by rfl⟩ : syracuseStep 2242123 = 3363185) B3363185
theorem B2837693 : Blo 2241435 2837693 := bbase (se 3 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 2837693 = 1064135) (by norm_num)
theorem B7567181 : Blo 2241435 7567181 := bstep (se 3 (by rfl) ⟨1418846, by rfl⟩ : syracuseStep 7567181 = 2837693) B2837693
theorem B5044787 : Blo 2241435 5044787 := bstep (se 1 (by rfl) ⟨3783590, by rfl⟩ : syracuseStep 5044787 = 7567181) B7567181
theorem B3363191 : Blo 2241435 3363191 := bstep (se 1 (by rfl) ⟨2522393, by rfl⟩ : syracuseStep 3363191 = 5044787) B5044787
theorem B2242127 : Blo 2241435 2242127 := bstep (se 1 (by rfl) ⟨1681595, by rfl⟩ : syracuseStep 2242127 = 3363191) B3363191
theorem B3363197 : Blo 2241435 3363197 := bbase (se 3 (by rfl) ⟨630599, by rfl⟩ : syracuseStep 3363197 = 1261199) (by norm_num)
theorem B2242131 : Blo 2241435 2242131 := bstep (se 1 (by rfl) ⟨1681598, by rfl⟩ : syracuseStep 2242131 = 3363197) B3363197
theorem B5044805 : Blo 2241435 5044805 := bbase (se 4 (by rfl) ⟨472950, by rfl⟩ : syracuseStep 5044805 = 945901) (by norm_num)
theorem B3363203 : Blo 2241435 3363203 := bstep (se 1 (by rfl) ⟨2522402, by rfl⟩ : syracuseStep 3363203 = 5044805) B5044805
theorem B2242135 : Blo 2241435 2242135 := bstep (se 1 (by rfl) ⟨1681601, by rfl⟩ : syracuseStep 2242135 = 3363203) B3363203
theorem B2394317 : Blo 2241435 2394317 := bbase (se 3 (by rfl) ⟨448934, by rfl⟩ : syracuseStep 2394317 = 897869) (by norm_num)
theorem B6384845 : Blo 2241435 6384845 := bstep (se 3 (by rfl) ⟨1197158, by rfl⟩ : syracuseStep 6384845 = 2394317) B2394317
theorem B4256563 : Blo 2241435 4256563 := bstep (se 1 (by rfl) ⟨3192422, by rfl⟩ : syracuseStep 4256563 = 6384845) B6384845
theorem B5675417 : Blo 2241435 5675417 := bstep (se 2 (by rfl) ⟨2128281, by rfl⟩ : syracuseStep 5675417 = 4256563) B4256563
theorem B3783611 : Blo 2241435 3783611 := bstep (se 1 (by rfl) ⟨2837708, by rfl⟩ : syracuseStep 3783611 = 5675417) B5675417
theorem B2522407 : Blo 2241435 2522407 := bstep (se 1 (by rfl) ⟨1891805, by rfl⟩ : syracuseStep 2522407 = 3783611) B3783611
theorem B3363209 : Blo 2241435 3363209 := bstep (se 2 (by rfl) ⟨1261203, by rfl⟩ : syracuseStep 3363209 = 2522407) B2522407
theorem B2242139 : Blo 2241435 2242139 := bstep (se 1 (by rfl) ⟨1681604, by rfl⟩ : syracuseStep 2242139 = 3363209) B3363209
theorem B11350853 : Blo 2241435 11350853 := bbase (se 4 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 11350853 = 2128285) (by norm_num)
theorem B7567235 : Blo 2241435 7567235 := bstep (se 1 (by rfl) ⟨5675426, by rfl⟩ : syracuseStep 7567235 = 11350853) B11350853
theorem B5044823 : Blo 2241435 5044823 := bstep (se 1 (by rfl) ⟨3783617, by rfl⟩ : syracuseStep 5044823 = 7567235) B7567235
theorem B3363215 : Blo 2241435 3363215 := bstep (se 1 (by rfl) ⟨2522411, by rfl⟩ : syracuseStep 3363215 = 5044823) B5044823
theorem B2242143 : Blo 2241435 2242143 := bstep (se 1 (by rfl) ⟨1681607, by rfl⟩ : syracuseStep 2242143 = 3363215) B3363215
theorem B3363221 : Blo 2241435 3363221 := bbase (se 6 (by rfl) ⟨78825, by rfl⟩ : syracuseStep 3363221 = 157651) (by norm_num)
theorem B2242147 : Blo 2241435 2242147 := bstep (se 1 (by rfl) ⟨1681610, by rfl⟩ : syracuseStep 2242147 = 3363221) B3363221
theorem B2693621 : Blo 2241435 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B7182989 : Blo 2241435 7182989 := bstep (se 3 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 7182989 = 2693621) B2693621
theorem B4788659 : Blo 2241435 4788659 := bstep (se 1 (by rfl) ⟨3591494, by rfl⟩ : syracuseStep 4788659 = 7182989) B7182989
theorem B12769757 : Blo 2241435 12769757 := bstep (se 3 (by rfl) ⟨2394329, by rfl⟩ : syracuseStep 12769757 = 4788659) B4788659
theorem B8513171 : Blo 2241435 8513171 := bstep (se 1 (by rfl) ⟨6384878, by rfl⟩ : syracuseStep 8513171 = 12769757) B12769757
theorem B5675447 : Blo 2241435 5675447 := bstep (se 1 (by rfl) ⟨4256585, by rfl⟩ : syracuseStep 5675447 = 8513171) B8513171
theorem B3783631 : Blo 2241435 3783631 := bstep (se 1 (by rfl) ⟨2837723, by rfl⟩ : syracuseStep 3783631 = 5675447) B5675447
theorem B5044841 : Blo 2241435 5044841 := bstep (se 2 (by rfl) ⟨1891815, by rfl⟩ : syracuseStep 5044841 = 3783631) B3783631
theorem B3363227 : Blo 2241435 3363227 := bstep (se 1 (by rfl) ⟨2522420, by rfl⟩ : syracuseStep 3363227 = 5044841) B5044841
theorem B2242151 : Blo 2241435 2242151 := bstep (se 1 (by rfl) ⟨1681613, by rfl⟩ : syracuseStep 2242151 = 3363227) B3363227
theorem B2522425 : Blo 2241435 2522425 := bbase (se 2 (by rfl) ⟨945909, by rfl⟩ : syracuseStep 2522425 = 1891819) (by norm_num)
theorem B3363233 : Blo 2241435 3363233 := bstep (se 2 (by rfl) ⟨1261212, by rfl⟩ : syracuseStep 3363233 = 2522425) B2522425
theorem B2242155 : Blo 2241435 2242155 := bstep (se 1 (by rfl) ⟨1681616, by rfl⟩ : syracuseStep 2242155 = 3363233) B3363233
theorem B6384901 : Blo 2241435 6384901 := bbase (se 4 (by rfl) ⟨598584, by rfl⟩ : syracuseStep 6384901 = 1197169) (by norm_num)
theorem B8513201 : Blo 2241435 8513201 := bstep (se 2 (by rfl) ⟨3192450, by rfl⟩ : syracuseStep 8513201 = 6384901) B6384901
theorem B5675467 : Blo 2241435 5675467 := bstep (se 1 (by rfl) ⟨4256600, by rfl⟩ : syracuseStep 5675467 = 8513201) B8513201
theorem B7567289 : Blo 2241435 7567289 := bstep (se 2 (by rfl) ⟨2837733, by rfl⟩ : syracuseStep 7567289 = 5675467) B5675467
theorem B5044859 : Blo 2241435 5044859 := bstep (se 1 (by rfl) ⟨3783644, by rfl⟩ : syracuseStep 5044859 = 7567289) B7567289
theorem B3363239 : Blo 2241435 3363239 := bstep (se 1 (by rfl) ⟨2522429, by rfl⟩ : syracuseStep 3363239 = 5044859) B5044859
theorem B2242159 : Blo 2241435 2242159 := bstep (se 1 (by rfl) ⟨1681619, by rfl⟩ : syracuseStep 2242159 = 3363239) B3363239
theorem B3363245 : Blo 2241435 3363245 := bbase (se 3 (by rfl) ⟨630608, by rfl⟩ : syracuseStep 3363245 = 1261217) (by norm_num)
theorem B2242163 : Blo 2241435 2242163 := bstep (se 1 (by rfl) ⟨1681622, by rfl⟩ : syracuseStep 2242163 = 3363245) B3363245
theorem B5044877 : Blo 2241435 5044877 := bbase (se 3 (by rfl) ⟨945914, by rfl⟩ : syracuseStep 5044877 = 1891829) (by norm_num)
theorem B3363251 : Blo 2241435 3363251 := bstep (se 1 (by rfl) ⟨2522438, by rfl⟩ : syracuseStep 3363251 = 5044877) B5044877
theorem B2242167 : Blo 2241435 2242167 := bstep (se 1 (by rfl) ⟨1681625, by rfl⟩ : syracuseStep 2242167 = 3363251) B3363251
theorem B2837749 : Blo 2241435 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B3783665 : Blo 2241435 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B2522443 : Blo 2241435 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B3363257 : Blo 2241435 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B2242171 : Blo 2241435 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B43098389 : Blo 2241435 43098389 := bbase (se 6 (by rfl) ⟨1010118, by rfl⟩ : syracuseStep 43098389 = 2020237) (by norm_num)
theorem B28732259 : Blo 2241435 28732259 := bstep (se 1 (by rfl) ⟨21549194, by rfl⟩ : syracuseStep 28732259 = 43098389) B43098389
theorem B19154839 : Blo 2241435 19154839 := bstep (se 1 (by rfl) ⟨14366129, by rfl⟩ : syracuseStep 19154839 = 28732259) B28732259
theorem B25539785 : Blo 2241435 25539785 := bstep (se 2 (by rfl) ⟨9577419, by rfl⟩ : syracuseStep 25539785 = 19154839) B19154839
theorem B17026523 : Blo 2241435 17026523 := bstep (se 1 (by rfl) ⟨12769892, by rfl⟩ : syracuseStep 17026523 = 25539785) B25539785
theorem B11351015 : Blo 2241435 11351015 := bstep (se 1 (by rfl) ⟨8513261, by rfl⟩ : syracuseStep 11351015 = 17026523) B17026523
theorem B7567343 : Blo 2241435 7567343 := bstep (se 1 (by rfl) ⟨5675507, by rfl⟩ : syracuseStep 7567343 = 11351015) B11351015
theorem B5044895 : Blo 2241435 5044895 := bstep (se 1 (by rfl) ⟨3783671, by rfl⟩ : syracuseStep 5044895 = 7567343) B7567343
theorem B3363263 : Blo 2241435 3363263 := bstep (se 1 (by rfl) ⟨2522447, by rfl⟩ : syracuseStep 3363263 = 5044895) B5044895
theorem B2242175 : Blo 2241435 2242175 := bstep (se 1 (by rfl) ⟨1681631, by rfl⟩ : syracuseStep 2242175 = 3363263) B3363263
theorem B3363269 : Blo 2241435 3363269 := bbase (se 4 (by rfl) ⟨315306, by rfl⟩ : syracuseStep 3363269 = 630613) (by norm_num)
theorem B2242179 : Blo 2241435 2242179 := bstep (se 1 (by rfl) ⟨1681634, by rfl⟩ : syracuseStep 2242179 = 3363269) B3363269
theorem B3783685 : Blo 2241435 3783685 := bbase (se 4 (by rfl) ⟨354720, by rfl⟩ : syracuseStep 3783685 = 709441) (by norm_num)
theorem B5044913 : Blo 2241435 5044913 := bstep (se 2 (by rfl) ⟨1891842, by rfl⟩ : syracuseStep 5044913 = 3783685) B3783685
theorem B3363275 : Blo 2241435 3363275 := bstep (se 1 (by rfl) ⟨2522456, by rfl⟩ : syracuseStep 3363275 = 5044913) B5044913
theorem B2242183 : Blo 2241435 2242183 := bstep (se 1 (by rfl) ⟨1681637, by rfl⟩ : syracuseStep 2242183 = 3363275) B3363275
theorem B2522461 : Blo 2241435 2522461 := bbase (se 3 (by rfl) ⟨472961, by rfl⟩ : syracuseStep 2522461 = 945923) (by norm_num)
theorem B3363281 : Blo 2241435 3363281 := bstep (se 2 (by rfl) ⟨1261230, by rfl⟩ : syracuseStep 3363281 = 2522461) B2522461
theorem B2242187 : Blo 2241435 2242187 := bstep (se 1 (by rfl) ⟨1681640, by rfl⟩ : syracuseStep 2242187 = 3363281) B3363281
theorem B7567397 : Blo 2241435 7567397 := bbase (se 4 (by rfl) ⟨709443, by rfl⟩ : syracuseStep 7567397 = 1418887) (by norm_num)
theorem B5044931 : Blo 2241435 5044931 := bstep (se 1 (by rfl) ⟨3783698, by rfl⟩ : syracuseStep 5044931 = 7567397) B7567397
theorem B3363287 : Blo 2241435 3363287 := bstep (se 1 (by rfl) ⟨2522465, by rfl⟩ : syracuseStep 3363287 = 5044931) B5044931
theorem B2242191 : Blo 2241435 2242191 := bstep (se 1 (by rfl) ⟨1681643, by rfl⟩ : syracuseStep 2242191 = 3363287) B3363287
theorem B3363293 : Blo 2241435 3363293 := bbase (se 3 (by rfl) ⟨630617, by rfl⟩ : syracuseStep 3363293 = 1261235) (by norm_num)
theorem B2242195 : Blo 2241435 2242195 := bstep (se 1 (by rfl) ⟨1681646, by rfl⟩ : syracuseStep 2242195 = 3363293) B3363293
theorem B5044949 : Blo 2241435 5044949 := bbase (se 7 (by rfl) ⟨59120, by rfl⟩ : syracuseStep 5044949 = 118241) (by norm_num)
theorem B3363299 : Blo 2241435 3363299 := bstep (se 1 (by rfl) ⟨2522474, by rfl⟩ : syracuseStep 3363299 = 5044949) B5044949
theorem B2242199 : Blo 2241435 2242199 := bstep (se 1 (by rfl) ⟨1681649, by rfl⟩ : syracuseStep 2242199 = 3363299) B3363299
theorem B9577541 : Blo 2241435 9577541 := bbase (se 4 (by rfl) ⟨897894, by rfl⟩ : syracuseStep 9577541 = 1795789) (by norm_num)
theorem B6385027 : Blo 2241435 6385027 := bstep (se 1 (by rfl) ⟨4788770, by rfl⟩ : syracuseStep 6385027 = 9577541) B9577541
theorem B8513369 : Blo 2241435 8513369 := bstep (se 2 (by rfl) ⟨3192513, by rfl⟩ : syracuseStep 8513369 = 6385027) B6385027
theorem B5675579 : Blo 2241435 5675579 := bstep (se 1 (by rfl) ⟨4256684, by rfl⟩ : syracuseStep 5675579 = 8513369) B8513369
theorem B3783719 : Blo 2241435 3783719 := bstep (se 1 (by rfl) ⟨2837789, by rfl⟩ : syracuseStep 3783719 = 5675579) B5675579
theorem B2522479 : Blo 2241435 2522479 := bstep (se 1 (by rfl) ⟨1891859, by rfl⟩ : syracuseStep 2522479 = 3783719) B3783719
theorem B3363305 : Blo 2241435 3363305 := bstep (se 2 (by rfl) ⟨1261239, by rfl⟩ : syracuseStep 3363305 = 2522479) B2522479
theorem B2242203 : Blo 2241435 2242203 := bstep (se 1 (by rfl) ⟨1681652, by rfl⟩ : syracuseStep 2242203 = 3363305) B3363305
theorem B2591785 : Blo 2241435 2591785 := bbase (se 2 (by rfl) ⟨971919, by rfl⟩ : syracuseStep 2591785 = 1943839) (by norm_num)
theorem B3455713 : Blo 2241435 3455713 := bstep (se 2 (by rfl) ⟨1295892, by rfl⟩ : syracuseStep 3455713 = 2591785) B2591785
theorem B4607617 : Blo 2241435 4607617 := bstep (se 2 (by rfl) ⟨1727856, by rfl⟩ : syracuseStep 4607617 = 3455713) B3455713
theorem B6143489 : Blo 2241435 6143489 := bstep (se 2 (by rfl) ⟨2303808, by rfl⟩ : syracuseStep 6143489 = 4607617) B4607617
theorem B4095659 : Blo 2241435 4095659 := bstep (se 1 (by rfl) ⟨3071744, by rfl⟩ : syracuseStep 4095659 = 6143489) B6143489
theorem B2730439 : Blo 2241435 2730439 := bstep (se 1 (by rfl) ⟨2047829, by rfl⟩ : syracuseStep 2730439 = 4095659) B4095659
theorem B14562341 : Blo 2241435 14562341 := bstep (se 4 (by rfl) ⟨1365219, by rfl⟩ : syracuseStep 14562341 = 2730439) B2730439
theorem B9708227 : Blo 2241435 9708227 := bstep (se 1 (by rfl) ⟨7281170, by rfl⟩ : syracuseStep 9708227 = 14562341) B14562341
theorem B6472151 : Blo 2241435 6472151 := bstep (se 1 (by rfl) ⟨4854113, by rfl⟩ : syracuseStep 6472151 = 9708227) B9708227
theorem B276145109 : Blo 2241435 276145109 := bstep (se 7 (by rfl) ⟨3236075, by rfl⟩ : syracuseStep 276145109 = 6472151) B6472151
theorem B184096739 : Blo 2241435 184096739 := bstep (se 1 (by rfl) ⟨138072554, by rfl⟩ : syracuseStep 184096739 = 276145109) B276145109
theorem B122731159 : Blo 2241435 122731159 := bstep (se 1 (by rfl) ⟨92048369, by rfl⟩ : syracuseStep 122731159 = 184096739) B184096739
theorem B163641545 : Blo 2241435 163641545 := bstep (se 2 (by rfl) ⟨61365579, by rfl⟩ : syracuseStep 163641545 = 122731159) B122731159
theorem B109094363 : Blo 2241435 109094363 := bstep (se 1 (by rfl) ⟨81820772, by rfl⟩ : syracuseStep 109094363 = 163641545) B163641545
theorem B72729575 : Blo 2241435 72729575 := bstep (se 1 (by rfl) ⟨54547181, by rfl⟩ : syracuseStep 72729575 = 109094363) B109094363
theorem B48486383 : Blo 2241435 48486383 := bstep (se 1 (by rfl) ⟨36364787, by rfl⟩ : syracuseStep 48486383 = 72729575) B72729575
theorem B32324255 : Blo 2241435 32324255 := bstep (se 1 (by rfl) ⟨24243191, by rfl⟩ : syracuseStep 32324255 = 48486383) B48486383
theorem B21549503 : Blo 2241435 21549503 := bstep (se 1 (by rfl) ⟨16162127, by rfl⟩ : syracuseStep 21549503 = 32324255) B32324255
theorem B14366335 : Blo 2241435 14366335 := bstep (se 1 (by rfl) ⟨10774751, by rfl⟩ : syracuseStep 14366335 = 21549503) B21549503
theorem B19155113 : Blo 2241435 19155113 := bstep (se 2 (by rfl) ⟨7183167, by rfl⟩ : syracuseStep 19155113 = 14366335) B14366335
theorem B12770075 : Blo 2241435 12770075 := bstep (se 1 (by rfl) ⟨9577556, by rfl⟩ : syracuseStep 12770075 = 19155113) B19155113
theorem B8513383 : Blo 2241435 8513383 := bstep (se 1 (by rfl) ⟨6385037, by rfl⟩ : syracuseStep 8513383 = 12770075) B12770075
theorem B11351177 : Blo 2241435 11351177 := bstep (se 2 (by rfl) ⟨4256691, by rfl⟩ : syracuseStep 11351177 = 8513383) B8513383
theorem B7567451 : Blo 2241435 7567451 := bstep (se 1 (by rfl) ⟨5675588, by rfl⟩ : syracuseStep 7567451 = 11351177) B11351177
theorem B5044967 : Blo 2241435 5044967 := bstep (se 1 (by rfl) ⟨3783725, by rfl⟩ : syracuseStep 5044967 = 7567451) B7567451
theorem B3363311 : Blo 2241435 3363311 := bstep (se 1 (by rfl) ⟨2522483, by rfl⟩ : syracuseStep 3363311 = 5044967) B5044967
theorem B2242207 : Blo 2241435 2242207 := bstep (se 1 (by rfl) ⟨1681655, by rfl⟩ : syracuseStep 2242207 = 3363311) B3363311
theorem B3363317 : Blo 2241435 3363317 := bbase (se 5 (by rfl) ⟨157655, by rfl⟩ : syracuseStep 3363317 = 315311) (by norm_num)
theorem B2242211 : Blo 2241435 2242211 := bstep (se 1 (by rfl) ⟨1681658, by rfl⟩ : syracuseStep 2242211 = 3363317) B3363317
theorem B6385061 : Blo 2241435 6385061 := bbase (se 4 (by rfl) ⟨598599, by rfl⟩ : syracuseStep 6385061 = 1197199) (by norm_num)
theorem B4256707 : Blo 2241435 4256707 := bstep (se 1 (by rfl) ⟨3192530, by rfl⟩ : syracuseStep 4256707 = 6385061) B6385061
theorem B5675609 : Blo 2241435 5675609 := bstep (se 2 (by rfl) ⟨2128353, by rfl⟩ : syracuseStep 5675609 = 4256707) B4256707
theorem B3783739 : Blo 2241435 3783739 := bstep (se 1 (by rfl) ⟨2837804, by rfl⟩ : syracuseStep 3783739 = 5675609) B5675609
theorem B5044985 : Blo 2241435 5044985 := bstep (se 2 (by rfl) ⟨1891869, by rfl⟩ : syracuseStep 5044985 = 3783739) B3783739
theorem B3363323 : Blo 2241435 3363323 := bstep (se 1 (by rfl) ⟨2522492, by rfl⟩ : syracuseStep 3363323 = 5044985) B5044985
theorem B2242215 : Blo 2241435 2242215 := bstep (se 1 (by rfl) ⟨1681661, by rfl⟩ : syracuseStep 2242215 = 3363323) B3363323
theorem B2522497 : Blo 2241435 2522497 := bbase (se 2 (by rfl) ⟨945936, by rfl⟩ : syracuseStep 2522497 = 1891873) (by norm_num)
theorem B3363329 : Blo 2241435 3363329 := bstep (se 2 (by rfl) ⟨1261248, by rfl⟩ : syracuseStep 3363329 = 2522497) B2522497
theorem B2242219 : Blo 2241435 2242219 := bstep (se 1 (by rfl) ⟨1681664, by rfl⟩ : syracuseStep 2242219 = 3363329) B3363329
theorem B5675629 : Blo 2241435 5675629 := bbase (se 3 (by rfl) ⟨1064180, by rfl⟩ : syracuseStep 5675629 = 2128361) (by norm_num)
theorem B7567505 : Blo 2241435 7567505 := bstep (se 2 (by rfl) ⟨2837814, by rfl⟩ : syracuseStep 7567505 = 5675629) B5675629
theorem B5045003 : Blo 2241435 5045003 := bstep (se 1 (by rfl) ⟨3783752, by rfl⟩ : syracuseStep 5045003 = 7567505) B7567505
theorem B3363335 : Blo 2241435 3363335 := bstep (se 1 (by rfl) ⟨2522501, by rfl⟩ : syracuseStep 3363335 = 5045003) B5045003
theorem B2242223 : Blo 2241435 2242223 := bstep (se 1 (by rfl) ⟨1681667, by rfl⟩ : syracuseStep 2242223 = 3363335) B3363335
theorem B3363341 : Blo 2241435 3363341 := bbase (se 3 (by rfl) ⟨630626, by rfl⟩ : syracuseStep 3363341 = 1261253) (by norm_num)
theorem B2242227 : Blo 2241435 2242227 := bstep (se 1 (by rfl) ⟨1681670, by rfl⟩ : syracuseStep 2242227 = 3363341) B3363341
theorem B5045021 : Blo 2241435 5045021 := bbase (se 3 (by rfl) ⟨945941, by rfl⟩ : syracuseStep 5045021 = 1891883) (by norm_num)
theorem B3363347 : Blo 2241435 3363347 := bstep (se 1 (by rfl) ⟨2522510, by rfl⟩ : syracuseStep 3363347 = 5045021) B5045021
theorem B2242231 : Blo 2241435 2242231 := bstep (se 1 (by rfl) ⟨1681673, by rfl⟩ : syracuseStep 2242231 = 3363347) B3363347
theorem B3783773 : Blo 2241435 3783773 := bbase (se 3 (by rfl) ⟨709457, by rfl⟩ : syracuseStep 3783773 = 1418915) (by norm_num)
theorem B2522515 : Blo 2241435 2522515 := bstep (se 1 (by rfl) ⟨1891886, by rfl⟩ : syracuseStep 2522515 = 3783773) B3783773
theorem B3363353 : Blo 2241435 3363353 := bstep (se 2 (by rfl) ⟨1261257, by rfl⟩ : syracuseStep 3363353 = 2522515) B2522515
theorem B2242235 : Blo 2241435 2242235 := bstep (se 1 (by rfl) ⟨1681676, by rfl⟩ : syracuseStep 2242235 = 3363353) B3363353
theorem B5387453 : Blo 2241435 5387453 := bbase (se 3 (by rfl) ⟨1010147, by rfl⟩ : syracuseStep 5387453 = 2020295) (by norm_num)
theorem B3591635 : Blo 2241435 3591635 := bstep (se 1 (by rfl) ⟨2693726, by rfl⟩ : syracuseStep 3591635 = 5387453) B5387453
theorem B9577693 : Blo 2241435 9577693 := bstep (se 3 (by rfl) ⟨1795817, by rfl⟩ : syracuseStep 9577693 = 3591635) B3591635
theorem B12770257 : Blo 2241435 12770257 := bstep (se 2 (by rfl) ⟨4788846, by rfl⟩ : syracuseStep 12770257 = 9577693) B9577693
theorem B17027009 : Blo 2241435 17027009 := bstep (se 2 (by rfl) ⟨6385128, by rfl⟩ : syracuseStep 17027009 = 12770257) B12770257
theorem B11351339 : Blo 2241435 11351339 := bstep (se 1 (by rfl) ⟨8513504, by rfl⟩ : syracuseStep 11351339 = 17027009) B17027009
theorem B7567559 : Blo 2241435 7567559 := bstep (se 1 (by rfl) ⟨5675669, by rfl⟩ : syracuseStep 7567559 = 11351339) B11351339
theorem B5045039 : Blo 2241435 5045039 := bstep (se 1 (by rfl) ⟨3783779, by rfl⟩ : syracuseStep 5045039 = 7567559) B7567559
theorem B3363359 : Blo 2241435 3363359 := bstep (se 1 (by rfl) ⟨2522519, by rfl⟩ : syracuseStep 3363359 = 5045039) B5045039
theorem B2242239 : Blo 2241435 2242239 := bstep (se 1 (by rfl) ⟨1681679, by rfl⟩ : syracuseStep 2242239 = 3363359) B3363359
theorem B3363365 : Blo 2241435 3363365 := bbase (se 4 (by rfl) ⟨315315, by rfl⟩ : syracuseStep 3363365 = 630631) (by norm_num)
theorem B2242243 : Blo 2241435 2242243 := bstep (se 1 (by rfl) ⟨1681682, by rfl⟩ : syracuseStep 2242243 = 3363365) B3363365
theorem B2837845 : Blo 2241435 2837845 := bbase (se 11 (by rfl) ⟨2078, by rfl⟩ : syracuseStep 2837845 = 4157) (by norm_num)
theorem B3783793 : Blo 2241435 3783793 := bstep (se 2 (by rfl) ⟨1418922, by rfl⟩ : syracuseStep 3783793 = 2837845) B2837845
theorem B5045057 : Blo 2241435 5045057 := bstep (se 2 (by rfl) ⟨1891896, by rfl⟩ : syracuseStep 5045057 = 3783793) B3783793
theorem B3363371 : Blo 2241435 3363371 := bstep (se 1 (by rfl) ⟨2522528, by rfl⟩ : syracuseStep 3363371 = 5045057) B5045057
theorem B2242247 : Blo 2241435 2242247 := bstep (se 1 (by rfl) ⟨1681685, by rfl⟩ : syracuseStep 2242247 = 3363371) B3363371
theorem B2522533 : Blo 2241435 2522533 := bbase (se 4 (by rfl) ⟨236487, by rfl⟩ : syracuseStep 2522533 = 472975) (by norm_num)
theorem B3363377 : Blo 2241435 3363377 := bstep (se 2 (by rfl) ⟨1261266, by rfl⟩ : syracuseStep 3363377 = 2522533) B2522533
theorem B2242251 : Blo 2241435 2242251 := bstep (se 1 (by rfl) ⟨1681688, by rfl⟩ : syracuseStep 2242251 = 3363377) B3363377
theorem B14366645 : Blo 2241435 14366645 := bbase (se 5 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 14366645 = 1346873) (by norm_num)
theorem B9577763 : Blo 2241435 9577763 := bstep (se 1 (by rfl) ⟨7183322, by rfl⟩ : syracuseStep 9577763 = 14366645) B14366645
theorem B6385175 : Blo 2241435 6385175 := bstep (se 1 (by rfl) ⟨4788881, by rfl⟩ : syracuseStep 6385175 = 9577763) B9577763
theorem B4256783 : Blo 2241435 4256783 := bstep (se 1 (by rfl) ⟨3192587, by rfl⟩ : syracuseStep 4256783 = 6385175) B6385175
theorem B2837855 : Blo 2241435 2837855 := bstep (se 1 (by rfl) ⟨2128391, by rfl⟩ : syracuseStep 2837855 = 4256783) B4256783
theorem B7567613 : Blo 2241435 7567613 := bstep (se 3 (by rfl) ⟨1418927, by rfl⟩ : syracuseStep 7567613 = 2837855) B2837855
theorem B5045075 : Blo 2241435 5045075 := bstep (se 1 (by rfl) ⟨3783806, by rfl⟩ : syracuseStep 5045075 = 7567613) B7567613
theorem B3363383 : Blo 2241435 3363383 := bstep (se 1 (by rfl) ⟨2522537, by rfl⟩ : syracuseStep 3363383 = 5045075) B5045075
theorem B2242255 : Blo 2241435 2242255 := bstep (se 1 (by rfl) ⟨1681691, by rfl⟩ : syracuseStep 2242255 = 3363383) B3363383
theorem B3363389 : Blo 2241435 3363389 := bbase (se 3 (by rfl) ⟨630635, by rfl⟩ : syracuseStep 3363389 = 1261271) (by norm_num)
theorem B2242259 : Blo 2241435 2242259 := bstep (se 1 (by rfl) ⟨1681694, by rfl⟩ : syracuseStep 2242259 = 3363389) B3363389
theorem B5045093 : Blo 2241435 5045093 := bbase (se 4 (by rfl) ⟨472977, by rfl⟩ : syracuseStep 5045093 = 945955) (by norm_num)
theorem B3363395 : Blo 2241435 3363395 := bstep (se 1 (by rfl) ⟨2522546, by rfl⟩ : syracuseStep 3363395 = 5045093) B5045093
theorem B2242263 : Blo 2241435 2242263 := bstep (se 1 (by rfl) ⟨1681697, by rfl⟩ : syracuseStep 2242263 = 3363395) B3363395
theorem B5675741 : Blo 2241435 5675741 := bbase (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) (by norm_num)
theorem B3783827 : Blo 2241435 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B2522551 : Blo 2241435 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B3363401 : Blo 2241435 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B2242267 : Blo 2241435 2242267 := bstep (se 1 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 2242267 = 3363401) B3363401
theorem B4256813 : Blo 2241435 4256813 := bbase (se 3 (by rfl) ⟨798152, by rfl⟩ : syracuseStep 4256813 = 1596305) (by norm_num)
theorem B11351501 : Blo 2241435 11351501 := bstep (se 3 (by rfl) ⟨2128406, by rfl⟩ : syracuseStep 11351501 = 4256813) B4256813
theorem B7567667 : Blo 2241435 7567667 := bstep (se 1 (by rfl) ⟨5675750, by rfl⟩ : syracuseStep 7567667 = 11351501) B11351501
theorem B5045111 : Blo 2241435 5045111 := bstep (se 1 (by rfl) ⟨3783833, by rfl⟩ : syracuseStep 5045111 = 7567667) B7567667
theorem B3363407 : Blo 2241435 3363407 := bstep (se 1 (by rfl) ⟨2522555, by rfl⟩ : syracuseStep 3363407 = 5045111) B5045111
theorem B2242271 : Blo 2241435 2242271 := bstep (se 1 (by rfl) ⟨1681703, by rfl⟩ : syracuseStep 2242271 = 3363407) B3363407
theorem B3363413 : Blo 2241435 3363413 := bbase (se 8 (by rfl) ⟨19707, by rfl⟩ : syracuseStep 3363413 = 39415) (by norm_num)
theorem B2242275 : Blo 2241435 2242275 := bstep (se 1 (by rfl) ⟨1681706, by rfl⟩ : syracuseStep 2242275 = 3363413) B3363413
theorem B3409309 : Blo 2241435 3409309 := bbase (se 3 (by rfl) ⟨639245, by rfl⟩ : syracuseStep 3409309 = 1278491) (by norm_num)
theorem B18182981 : Blo 2241435 18182981 := bstep (se 4 (by rfl) ⟨1704654, by rfl⟩ : syracuseStep 18182981 = 3409309) B3409309
theorem B12121987 : Blo 2241435 12121987 := bstep (se 1 (by rfl) ⟨9091490, by rfl⟩ : syracuseStep 12121987 = 18182981) B18182981
theorem B16162649 : Blo 2241435 16162649 := bstep (se 2 (by rfl) ⟨6060993, by rfl⟩ : syracuseStep 16162649 = 12121987) B12121987
theorem B10775099 : Blo 2241435 10775099 := bstep (se 1 (by rfl) ⟨8081324, by rfl⟩ : syracuseStep 10775099 = 16162649) B16162649
theorem B7183399 : Blo 2241435 7183399 := bstep (se 1 (by rfl) ⟨5387549, by rfl⟩ : syracuseStep 7183399 = 10775099) B10775099
theorem B9577865 : Blo 2241435 9577865 := bstep (se 2 (by rfl) ⟨3591699, by rfl⟩ : syracuseStep 9577865 = 7183399) B7183399
theorem B6385243 : Blo 2241435 6385243 := bstep (se 1 (by rfl) ⟨4788932, by rfl⟩ : syracuseStep 6385243 = 9577865) B9577865
theorem B8513657 : Blo 2241435 8513657 := bstep (se 2 (by rfl) ⟨3192621, by rfl⟩ : syracuseStep 8513657 = 6385243) B6385243
theorem B5675771 : Blo 2241435 5675771 := bstep (se 1 (by rfl) ⟨4256828, by rfl⟩ : syracuseStep 5675771 = 8513657) B8513657
theorem B3783847 : Blo 2241435 3783847 := bstep (se 1 (by rfl) ⟨2837885, by rfl⟩ : syracuseStep 3783847 = 5675771) B5675771
theorem B5045129 : Blo 2241435 5045129 := bstep (se 2 (by rfl) ⟨1891923, by rfl⟩ : syracuseStep 5045129 = 3783847) B3783847
theorem B3363419 : Blo 2241435 3363419 := bstep (se 1 (by rfl) ⟨2522564, by rfl⟩ : syracuseStep 3363419 = 5045129) B5045129
theorem B2242279 : Blo 2241435 2242279 := bstep (se 1 (by rfl) ⟨1681709, by rfl⟩ : syracuseStep 2242279 = 3363419) B3363419
theorem B2522569 : Blo 2241435 2522569 := bbase (se 2 (by rfl) ⟨945963, by rfl⟩ : syracuseStep 2522569 = 1891927) (by norm_num)
theorem B3363425 : Blo 2241435 3363425 := bstep (se 2 (by rfl) ⟨1261284, by rfl⟩ : syracuseStep 3363425 = 2522569) B2522569
theorem B2242283 : Blo 2241435 2242283 := bstep (se 1 (by rfl) ⟨1681712, by rfl⟩ : syracuseStep 2242283 = 3363425) B3363425
theorem B19155797 : Blo 2241435 19155797 := bbase (se 9 (by rfl) ⟨56120, by rfl⟩ : syracuseStep 19155797 = 112241) (by norm_num)
theorem B12770531 : Blo 2241435 12770531 := bstep (se 1 (by rfl) ⟨9577898, by rfl⟩ : syracuseStep 12770531 = 19155797) B19155797
theorem B8513687 : Blo 2241435 8513687 := bstep (se 1 (by rfl) ⟨6385265, by rfl⟩ : syracuseStep 8513687 = 12770531) B12770531
theorem B5675791 : Blo 2241435 5675791 := bstep (se 1 (by rfl) ⟨4256843, by rfl⟩ : syracuseStep 5675791 = 8513687) B8513687
theorem B7567721 : Blo 2241435 7567721 := bstep (se 2 (by rfl) ⟨2837895, by rfl⟩ : syracuseStep 7567721 = 5675791) B5675791
theorem B5045147 : Blo 2241435 5045147 := bstep (se 1 (by rfl) ⟨3783860, by rfl⟩ : syracuseStep 5045147 = 7567721) B7567721
theorem B3363431 : Blo 2241435 3363431 := bstep (se 1 (by rfl) ⟨2522573, by rfl⟩ : syracuseStep 3363431 = 5045147) B5045147
theorem B2242287 : Blo 2241435 2242287 := bstep (se 1 (by rfl) ⟨1681715, by rfl⟩ : syracuseStep 2242287 = 3363431) B3363431
theorem B3363437 : Blo 2241435 3363437 := bbase (se 3 (by rfl) ⟨630644, by rfl⟩ : syracuseStep 3363437 = 1261289) (by norm_num)
theorem B2242291 : Blo 2241435 2242291 := bstep (se 1 (by rfl) ⟨1681718, by rfl⟩ : syracuseStep 2242291 = 3363437) B3363437
theorem B5045165 : Blo 2241435 5045165 := bbase (se 3 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 5045165 = 1891937) (by norm_num)
theorem B3363443 : Blo 2241435 3363443 := bstep (se 1 (by rfl) ⟨2522582, by rfl⟩ : syracuseStep 3363443 = 5045165) B5045165
theorem B2242295 : Blo 2241435 2242295 := bstep (se 1 (by rfl) ⟨1681721, by rfl⟩ : syracuseStep 2242295 = 3363443) B3363443
theorem B6385301 : Blo 2241435 6385301 := bbase (se 6 (by rfl) ⟨149655, by rfl⟩ : syracuseStep 6385301 = 299311) (by norm_num)
theorem B4256867 : Blo 2241435 4256867 := bstep (se 1 (by rfl) ⟨3192650, by rfl⟩ : syracuseStep 4256867 = 6385301) B6385301
theorem B2837911 : Blo 2241435 2837911 := bstep (se 1 (by rfl) ⟨2128433, by rfl⟩ : syracuseStep 2837911 = 4256867) B4256867
theorem B3783881 : Blo 2241435 3783881 := bstep (se 2 (by rfl) ⟨1418955, by rfl⟩ : syracuseStep 3783881 = 2837911) B2837911
theorem B2522587 : Blo 2241435 2522587 := bstep (se 1 (by rfl) ⟨1891940, by rfl⟩ : syracuseStep 2522587 = 3783881) B3783881
theorem B3363449 : Blo 2241435 3363449 := bstep (se 2 (by rfl) ⟨1261293, by rfl⟩ : syracuseStep 3363449 = 2522587) B2522587
theorem B2242299 : Blo 2241435 2242299 := bstep (se 1 (by rfl) ⟨1681724, by rfl⟩ : syracuseStep 2242299 = 3363449) B3363449
theorem B2557009 : Blo 2241435 2557009 := bbase (se 2 (by rfl) ⟨958878, by rfl⟩ : syracuseStep 2557009 = 1917757) (by norm_num)
theorem B3409345 : Blo 2241435 3409345 := bstep (se 2 (by rfl) ⟨1278504, by rfl⟩ : syracuseStep 3409345 = 2557009) B2557009
theorem B4545793 : Blo 2241435 4545793 := bstep (se 2 (by rfl) ⟨1704672, by rfl⟩ : syracuseStep 4545793 = 3409345) B3409345
theorem B6061057 : Blo 2241435 6061057 := bstep (se 2 (by rfl) ⟨2272896, by rfl⟩ : syracuseStep 6061057 = 4545793) B4545793
theorem B32325637 : Blo 2241435 32325637 := bstep (se 4 (by rfl) ⟨3030528, by rfl⟩ : syracuseStep 32325637 = 6061057) B6061057
theorem B43100849 : Blo 2241435 43100849 := bstep (se 2 (by rfl) ⟨16162818, by rfl⟩ : syracuseStep 43100849 = 32325637) B32325637
theorem B28733899 : Blo 2241435 28733899 := bstep (se 1 (by rfl) ⟨21550424, by rfl⟩ : syracuseStep 28733899 = 43100849) B43100849
theorem B38311865 : Blo 2241435 38311865 := bstep (se 2 (by rfl) ⟨14366949, by rfl⟩ : syracuseStep 38311865 = 28733899) B28733899
theorem B25541243 : Blo 2241435 25541243 := bstep (se 1 (by rfl) ⟨19155932, by rfl⟩ : syracuseStep 25541243 = 38311865) B38311865
theorem B17027495 : Blo 2241435 17027495 := bstep (se 1 (by rfl) ⟨12770621, by rfl⟩ : syracuseStep 17027495 = 25541243) B25541243
theorem B11351663 : Blo 2241435 11351663 := bstep (se 1 (by rfl) ⟨8513747, by rfl⟩ : syracuseStep 11351663 = 17027495) B17027495
theorem B7567775 : Blo 2241435 7567775 := bstep (se 1 (by rfl) ⟨5675831, by rfl⟩ : syracuseStep 7567775 = 11351663) B11351663
theorem B5045183 : Blo 2241435 5045183 := bstep (se 1 (by rfl) ⟨3783887, by rfl⟩ : syracuseStep 5045183 = 7567775) B7567775
theorem B3363455 : Blo 2241435 3363455 := bstep (se 1 (by rfl) ⟨2522591, by rfl⟩ : syracuseStep 3363455 = 5045183) B5045183
theorem B2242303 : Blo 2241435 2242303 := bstep (se 1 (by rfl) ⟨1681727, by rfl⟩ : syracuseStep 2242303 = 3363455) B3363455
theorem B3363461 : Blo 2241435 3363461 := bbase (se 4 (by rfl) ⟨315324, by rfl⟩ : syracuseStep 3363461 = 630649) (by norm_num)
theorem B2242307 : Blo 2241435 2242307 := bstep (se 1 (by rfl) ⟨1681730, by rfl⟩ : syracuseStep 2242307 = 3363461) B3363461
theorem B3783901 : Blo 2241435 3783901 := bbase (se 3 (by rfl) ⟨709481, by rfl⟩ : syracuseStep 3783901 = 1418963) (by norm_num)
theorem B5045201 : Blo 2241435 5045201 := bstep (se 2 (by rfl) ⟨1891950, by rfl⟩ : syracuseStep 5045201 = 3783901) B3783901
theorem B3363467 : Blo 2241435 3363467 := bstep (se 1 (by rfl) ⟨2522600, by rfl⟩ : syracuseStep 3363467 = 5045201) B5045201
theorem B2242311 : Blo 2241435 2242311 := bstep (se 1 (by rfl) ⟨1681733, by rfl⟩ : syracuseStep 2242311 = 3363467) B3363467
theorem B2522605 : Blo 2241435 2522605 := bbase (se 3 (by rfl) ⟨472988, by rfl⟩ : syracuseStep 2522605 = 945977) (by norm_num)
theorem B3363473 : Blo 2241435 3363473 := bstep (se 2 (by rfl) ⟨1261302, by rfl⟩ : syracuseStep 3363473 = 2522605) B2522605
theorem B2242315 : Blo 2241435 2242315 := bstep (se 1 (by rfl) ⟨1681736, by rfl⟩ : syracuseStep 2242315 = 3363473) B3363473
theorem B7567829 : Blo 2241435 7567829 := bbase (se 7 (by rfl) ⟨88685, by rfl⟩ : syracuseStep 7567829 = 177371) (by norm_num)
theorem B5045219 : Blo 2241435 5045219 := bstep (se 1 (by rfl) ⟨3783914, by rfl⟩ : syracuseStep 5045219 = 7567829) B7567829
theorem B3363479 : Blo 2241435 3363479 := bstep (se 1 (by rfl) ⟨2522609, by rfl⟩ : syracuseStep 3363479 = 5045219) B5045219
theorem B2242319 : Blo 2241435 2242319 := bstep (se 1 (by rfl) ⟨1681739, by rfl⟩ : syracuseStep 2242319 = 3363479) B3363479
theorem B3363485 : Blo 2241435 3363485 := bbase (se 3 (by rfl) ⟨630653, by rfl⟩ : syracuseStep 3363485 = 1261307) (by norm_num)
theorem B2242323 : Blo 2241435 2242323 := bstep (se 1 (by rfl) ⟨1681742, by rfl⟩ : syracuseStep 2242323 = 3363485) B3363485
theorem B5045237 : Blo 2241435 5045237 := bbase (se 5 (by rfl) ⟨236495, by rfl⟩ : syracuseStep 5045237 = 472991) (by norm_num)
theorem B3363491 : Blo 2241435 3363491 := bstep (se 1 (by rfl) ⟨2522618, by rfl⟩ : syracuseStep 3363491 = 5045237) B5045237
theorem B2242327 : Blo 2241435 2242327 := bstep (se 1 (by rfl) ⟨1681745, by rfl⟩ : syracuseStep 2242327 = 3363491) B3363491
theorem B3740813 : Blo 2241435 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B2493875 : Blo 2241435 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B6650333 : Blo 2241435 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B4433555 : Blo 2241435 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B2955703 : Blo 2241435 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B3940937 : Blo 2241435 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B42036661 : Blo 2241435 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B56048881 : Blo 2241435 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B74731841 : Blo 2241435 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B49821227 : Blo 2241435 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B33214151 : Blo 2241435 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B22142767 : Blo 2241435 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B29523689 : Blo 2241435 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B19682459 : Blo 2241435 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B13121639 : Blo 2241435 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B8747759 : Blo 2241435 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B5831839 : Blo 2241435 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B7775785 : Blo 2241435 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B10367713 : Blo 2241435 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B13823617 : Blo 2241435 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B18431489 : Blo 2241435 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B12287659 : Blo 2241435 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B16383545 : Blo 2241435 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B10922363 : Blo 2241435 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B7281575 : Blo 2241435 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B4854383 : Blo 2241435 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B3236255 : Blo 2241435 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B34520053 : Blo 2241435 34520053 := bstep (se 5 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 34520053 = 3236255) B3236255
theorem B46026737 : Blo 2241435 46026737 := bstep (se 2 (by rfl) ⟨17260026, by rfl⟩ : syracuseStep 46026737 = 34520053) B34520053
theorem B30684491 : Blo 2241435 30684491 := bstep (se 1 (by rfl) ⟨23013368, by rfl⟩ : syracuseStep 30684491 = 46026737) B46026737
theorem B20456327 : Blo 2241435 20456327 := bstep (se 1 (by rfl) ⟨15342245, by rfl⟩ : syracuseStep 20456327 = 30684491) B30684491
theorem B54550205 : Blo 2241435 54550205 := bstep (se 3 (by rfl) ⟨10228163, by rfl⟩ : syracuseStep 54550205 = 20456327) B20456327
theorem B36366803 : Blo 2241435 36366803 := bstep (se 1 (by rfl) ⟨27275102, by rfl⟩ : syracuseStep 36366803 = 54550205) B54550205
theorem B24244535 : Blo 2241435 24244535 := bstep (se 1 (by rfl) ⟨18183401, by rfl⟩ : syracuseStep 24244535 = 36366803) B36366803
theorem B64652093 : Blo 2241435 64652093 := bstep (se 3 (by rfl) ⟨12122267, by rfl⟩ : syracuseStep 64652093 = 24244535) B24244535
theorem B43101395 : Blo 2241435 43101395 := bstep (se 1 (by rfl) ⟨32326046, by rfl⟩ : syracuseStep 43101395 = 64652093) B64652093
theorem B28734263 : Blo 2241435 28734263 := bstep (se 1 (by rfl) ⟨21550697, by rfl⟩ : syracuseStep 28734263 = 43101395) B43101395
theorem B19156175 : Blo 2241435 19156175 := bstep (se 1 (by rfl) ⟨14367131, by rfl⟩ : syracuseStep 19156175 = 28734263) B28734263
theorem B12770783 : Blo 2241435 12770783 := bstep (se 1 (by rfl) ⟨9578087, by rfl⟩ : syracuseStep 12770783 = 19156175) B19156175
theorem B8513855 : Blo 2241435 8513855 := bstep (se 1 (by rfl) ⟨6385391, by rfl⟩ : syracuseStep 8513855 = 12770783) B12770783
theorem B5675903 : Blo 2241435 5675903 := bstep (se 1 (by rfl) ⟨4256927, by rfl⟩ : syracuseStep 5675903 = 8513855) B8513855
theorem B3783935 : Blo 2241435 3783935 := bstep (se 1 (by rfl) ⟨2837951, by rfl⟩ : syracuseStep 3783935 = 5675903) B5675903
theorem B2522623 : Blo 2241435 2522623 := bstep (se 1 (by rfl) ⟨1891967, by rfl⟩ : syracuseStep 2522623 = 3783935) B3783935
theorem B3363497 : Blo 2241435 3363497 := bstep (se 2 (by rfl) ⟨1261311, by rfl⟩ : syracuseStep 3363497 = 2522623) B2522623
theorem B2242331 : Blo 2241435 2242331 := bstep (se 1 (by rfl) ⟨1681748, by rfl⟩ : syracuseStep 2242331 = 3363497) B3363497
theorem B3192701 : Blo 2241435 3192701 := bbase (se 3 (by rfl) ⟨598631, by rfl⟩ : syracuseStep 3192701 = 1197263) (by norm_num)
theorem B8513869 : Blo 2241435 8513869 := bstep (se 3 (by rfl) ⟨1596350, by rfl⟩ : syracuseStep 8513869 = 3192701) B3192701
theorem B11351825 : Blo 2241435 11351825 := bstep (se 2 (by rfl) ⟨4256934, by rfl⟩ : syracuseStep 11351825 = 8513869) B8513869
theorem B7567883 : Blo 2241435 7567883 := bstep (se 1 (by rfl) ⟨5675912, by rfl⟩ : syracuseStep 7567883 = 11351825) B11351825
theorem B5045255 : Blo 2241435 5045255 := bstep (se 1 (by rfl) ⟨3783941, by rfl⟩ : syracuseStep 5045255 = 7567883) B7567883
theorem B3363503 : Blo 2241435 3363503 := bstep (se 1 (by rfl) ⟨2522627, by rfl⟩ : syracuseStep 3363503 = 5045255) B5045255
theorem B2242335 : Blo 2241435 2242335 := bstep (se 1 (by rfl) ⟨1681751, by rfl⟩ : syracuseStep 2242335 = 3363503) B3363503
theorem B3363509 : Blo 2241435 3363509 := bbase (se 5 (by rfl) ⟨157664, by rfl⟩ : syracuseStep 3363509 = 315329) (by norm_num)
theorem B2242339 : Blo 2241435 2242339 := bstep (se 1 (by rfl) ⟨1681754, by rfl⟩ : syracuseStep 2242339 = 3363509) B3363509
theorem B5675933 : Blo 2241435 5675933 := bbase (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) (by norm_num)
theorem B3783955 : Blo 2241435 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B5045273 : Blo 2241435 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B3363515 : Blo 2241435 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B2242343 : Blo 2241435 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B2522641 : Blo 2241435 2522641 := bbase (se 2 (by rfl) ⟨945990, by rfl⟩ : syracuseStep 2522641 = 1891981) (by norm_num)
theorem B3363521 : Blo 2241435 3363521 := bstep (se 2 (by rfl) ⟨1261320, by rfl⟩ : syracuseStep 3363521 = 2522641) B2522641
theorem B2242347 : Blo 2241435 2242347 := bstep (se 1 (by rfl) ⟨1681760, by rfl⟩ : syracuseStep 2242347 = 3363521) B3363521
theorem B4256965 : Blo 2241435 4256965 := bbase (se 4 (by rfl) ⟨399090, by rfl⟩ : syracuseStep 4256965 = 798181) (by norm_num)
theorem B5675953 : Blo 2241435 5675953 := bstep (se 2 (by rfl) ⟨2128482, by rfl⟩ : syracuseStep 5675953 = 4256965) B4256965
theorem B7567937 : Blo 2241435 7567937 := bstep (se 2 (by rfl) ⟨2837976, by rfl⟩ : syracuseStep 7567937 = 5675953) B5675953
theorem B5045291 : Blo 2241435 5045291 := bstep (se 1 (by rfl) ⟨3783968, by rfl⟩ : syracuseStep 5045291 = 7567937) B7567937
theorem B3363527 : Blo 2241435 3363527 := bstep (se 1 (by rfl) ⟨2522645, by rfl⟩ : syracuseStep 3363527 = 5045291) B5045291
theorem B2242351 : Blo 2241435 2242351 := bstep (se 1 (by rfl) ⟨1681763, by rfl⟩ : syracuseStep 2242351 = 3363527) B3363527
theorem B3363533 : Blo 2241435 3363533 := bbase (se 3 (by rfl) ⟨630662, by rfl⟩ : syracuseStep 3363533 = 1261325) (by norm_num)
theorem B2242355 : Blo 2241435 2242355 := bstep (se 1 (by rfl) ⟨1681766, by rfl⟩ : syracuseStep 2242355 = 3363533) B3363533
theorem B5045309 : Blo 2241435 5045309 := bbase (se 3 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 5045309 = 1891991) (by norm_num)
theorem B3363539 : Blo 2241435 3363539 := bstep (se 1 (by rfl) ⟨2522654, by rfl⟩ : syracuseStep 3363539 = 5045309) B5045309
theorem B2242359 : Blo 2241435 2242359 := bstep (se 1 (by rfl) ⟨1681769, by rfl⟩ : syracuseStep 2242359 = 3363539) B3363539
theorem B3783989 : Blo 2241435 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B2522659 : Blo 2241435 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B3363545 : Blo 2241435 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B2242363 : Blo 2241435 2242363 := bstep (se 1 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 2242363 = 3363545) B3363545
theorem B6385493 : Blo 2241435 6385493 := bbase (se 9 (by rfl) ⟨18707, by rfl⟩ : syracuseStep 6385493 = 37415) (by norm_num)
theorem B17027981 : Blo 2241435 17027981 := bstep (se 3 (by rfl) ⟨3192746, by rfl⟩ : syracuseStep 17027981 = 6385493) B6385493
theorem B11351987 : Blo 2241435 11351987 := bstep (se 1 (by rfl) ⟨8513990, by rfl⟩ : syracuseStep 11351987 = 17027981) B17027981
theorem B7567991 : Blo 2241435 7567991 := bstep (se 1 (by rfl) ⟨5675993, by rfl⟩ : syracuseStep 7567991 = 11351987) B11351987
theorem B5045327 : Blo 2241435 5045327 := bstep (se 1 (by rfl) ⟨3783995, by rfl⟩ : syracuseStep 5045327 = 7567991) B7567991
theorem B3363551 : Blo 2241435 3363551 := bstep (se 1 (by rfl) ⟨2522663, by rfl⟩ : syracuseStep 3363551 = 5045327) B5045327
theorem B2242367 : Blo 2241435 2242367 := bstep (se 1 (by rfl) ⟨1681775, by rfl⟩ : syracuseStep 2242367 = 3363551) B3363551
theorem B3363557 : Blo 2241435 3363557 := bbase (se 4 (by rfl) ⟨315333, by rfl⟩ : syracuseStep 3363557 = 630667) (by norm_num)
theorem B2242371 : Blo 2241435 2242371 := bstep (se 1 (by rfl) ⟨1681778, by rfl⟩ : syracuseStep 2242371 = 3363557) B3363557
theorem B2394569 : Blo 2241435 2394569 := bbase (se 2 (by rfl) ⟨897963, by rfl⟩ : syracuseStep 2394569 = 1795927) (by norm_num)
theorem B6385517 : Blo 2241435 6385517 := bstep (se 3 (by rfl) ⟨1197284, by rfl⟩ : syracuseStep 6385517 = 2394569) B2394569
theorem B4257011 : Blo 2241435 4257011 := bstep (se 1 (by rfl) ⟨3192758, by rfl⟩ : syracuseStep 4257011 = 6385517) B6385517
theorem B2838007 : Blo 2241435 2838007 := bstep (se 1 (by rfl) ⟨2128505, by rfl⟩ : syracuseStep 2838007 = 4257011) B4257011
theorem B3784009 : Blo 2241435 3784009 := bstep (se 2 (by rfl) ⟨1419003, by rfl⟩ : syracuseStep 3784009 = 2838007) B2838007
theorem B5045345 : Blo 2241435 5045345 := bstep (se 2 (by rfl) ⟨1892004, by rfl⟩ : syracuseStep 5045345 = 3784009) B3784009
theorem B3363563 : Blo 2241435 3363563 := bstep (se 1 (by rfl) ⟨2522672, by rfl⟩ : syracuseStep 3363563 = 5045345) B5045345
theorem B2242375 : Blo 2241435 2242375 := bstep (se 1 (by rfl) ⟨1681781, by rfl⟩ : syracuseStep 2242375 = 3363563) B3363563
theorem B2522677 : Blo 2241435 2522677 := bbase (se 5 (by rfl) ⟨118250, by rfl⟩ : syracuseStep 2522677 = 236501) (by norm_num)
theorem B3363569 : Blo 2241435 3363569 := bstep (se 2 (by rfl) ⟨1261338, by rfl⟩ : syracuseStep 3363569 = 2522677) B2522677
theorem B2242379 : Blo 2241435 2242379 := bstep (se 1 (by rfl) ⟨1681784, by rfl⟩ : syracuseStep 2242379 = 3363569) B3363569
theorem B2838017 : Blo 2241435 2838017 := bbase (se 2 (by rfl) ⟨1064256, by rfl⟩ : syracuseStep 2838017 = 2128513) (by norm_num)
theorem B7568045 : Blo 2241435 7568045 := bstep (se 3 (by rfl) ⟨1419008, by rfl⟩ : syracuseStep 7568045 = 2838017) B2838017
theorem B5045363 : Blo 2241435 5045363 := bstep (se 1 (by rfl) ⟨3784022, by rfl⟩ : syracuseStep 5045363 = 7568045) B7568045
theorem B3363575 : Blo 2241435 3363575 := bstep (se 1 (by rfl) ⟨2522681, by rfl⟩ : syracuseStep 3363575 = 5045363) B5045363
theorem B2242383 : Blo 2241435 2242383 := bstep (se 1 (by rfl) ⟨1681787, by rfl⟩ : syracuseStep 2242383 = 3363575) B3363575
theorem B3363581 : Blo 2241435 3363581 := bbase (se 3 (by rfl) ⟨630671, by rfl⟩ : syracuseStep 3363581 = 1261343) (by norm_num)
theorem B2242387 : Blo 2241435 2242387 := bstep (se 1 (by rfl) ⟨1681790, by rfl⟩ : syracuseStep 2242387 = 3363581) B3363581
theorem B5045381 : Blo 2241435 5045381 := bbase (se 4 (by rfl) ⟨473004, by rfl⟩ : syracuseStep 5045381 = 946009) (by norm_num)
theorem B3363587 : Blo 2241435 3363587 := bstep (se 1 (by rfl) ⟨2522690, by rfl⟩ : syracuseStep 3363587 = 5045381) B5045381
theorem B2242391 : Blo 2241435 2242391 := bstep (se 1 (by rfl) ⟨1681793, by rfl⟩ : syracuseStep 2242391 = 3363587) B3363587
theorem B4789181 : Blo 2241435 4789181 := bbase (se 3 (by rfl) ⟨897971, by rfl⟩ : syracuseStep 4789181 = 1795943) (by norm_num)
theorem B3192787 : Blo 2241435 3192787 := bstep (se 1 (by rfl) ⟨2394590, by rfl⟩ : syracuseStep 3192787 = 4789181) B4789181
theorem B4257049 : Blo 2241435 4257049 := bstep (se 2 (by rfl) ⟨1596393, by rfl⟩ : syracuseStep 4257049 = 3192787) B3192787
theorem B5676065 : Blo 2241435 5676065 := bstep (se 2 (by rfl) ⟨2128524, by rfl⟩ : syracuseStep 5676065 = 4257049) B4257049
theorem B3784043 : Blo 2241435 3784043 := bstep (se 1 (by rfl) ⟨2838032, by rfl⟩ : syracuseStep 3784043 = 5676065) B5676065
theorem B2522695 : Blo 2241435 2522695 := bstep (se 1 (by rfl) ⟨1892021, by rfl⟩ : syracuseStep 2522695 = 3784043) B3784043
theorem B3363593 : Blo 2241435 3363593 := bstep (se 2 (by rfl) ⟨1261347, by rfl⟩ : syracuseStep 3363593 = 2522695) B2522695
theorem B2242395 : Blo 2241435 2242395 := bstep (se 1 (by rfl) ⟨1681796, by rfl⟩ : syracuseStep 2242395 = 3363593) B3363593
theorem B11352149 : Blo 2241435 11352149 := bbase (se 8 (by rfl) ⟨66516, by rfl⟩ : syracuseStep 11352149 = 133033) (by norm_num)
theorem B7568099 : Blo 2241435 7568099 := bstep (se 1 (by rfl) ⟨5676074, by rfl⟩ : syracuseStep 7568099 = 11352149) B11352149
theorem B5045399 : Blo 2241435 5045399 := bstep (se 1 (by rfl) ⟨3784049, by rfl⟩ : syracuseStep 5045399 = 7568099) B7568099
theorem B3363599 : Blo 2241435 3363599 := bstep (se 1 (by rfl) ⟨2522699, by rfl⟩ : syracuseStep 3363599 = 5045399) B5045399
theorem B2242399 : Blo 2241435 2242399 := bstep (se 1 (by rfl) ⟨1681799, by rfl⟩ : syracuseStep 2242399 = 3363599) B3363599
theorem B3363605 : Blo 2241435 3363605 := bbase (se 6 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 3363605 = 157669) (by norm_num)
theorem B2242403 : Blo 2241435 2242403 := bstep (se 1 (by rfl) ⟨1681802, by rfl⟩ : syracuseStep 2242403 = 3363605) B3363605
theorem B24576149 : Blo 2241435 24576149 := bbase (se 6 (by rfl) ⟨576003, by rfl⟩ : syracuseStep 24576149 = 1152007) (by norm_num)
theorem B16384099 : Blo 2241435 16384099 := bstep (se 1 (by rfl) ⟨12288074, by rfl⟩ : syracuseStep 16384099 = 24576149) B24576149
theorem B21845465 : Blo 2241435 21845465 := bstep (se 2 (by rfl) ⟨8192049, by rfl⟩ : syracuseStep 21845465 = 16384099) B16384099
theorem B14563643 : Blo 2241435 14563643 := bstep (se 1 (by rfl) ⟨10922732, by rfl⟩ : syracuseStep 14563643 = 21845465) B21845465
theorem B38836381 : Blo 2241435 38836381 := bstep (se 3 (by rfl) ⟨7281821, by rfl⟩ : syracuseStep 38836381 = 14563643) B14563643
theorem B51781841 : Blo 2241435 51781841 := bstep (se 2 (by rfl) ⟨19418190, by rfl⟩ : syracuseStep 51781841 = 38836381) B38836381
theorem B34521227 : Blo 2241435 34521227 := bstep (se 1 (by rfl) ⟨25890920, by rfl⟩ : syracuseStep 34521227 = 51781841) B51781841
theorem B23014151 : Blo 2241435 23014151 := bstep (se 1 (by rfl) ⟨17260613, by rfl⟩ : syracuseStep 23014151 = 34521227) B34521227
theorem B15342767 : Blo 2241435 15342767 := bstep (se 1 (by rfl) ⟨11507075, by rfl⟩ : syracuseStep 15342767 = 23014151) B23014151
theorem B10228511 : Blo 2241435 10228511 := bstep (se 1 (by rfl) ⟨7671383, by rfl⟩ : syracuseStep 10228511 = 15342767) B15342767
theorem B6819007 : Blo 2241435 6819007 := bstep (se 1 (by rfl) ⟨5114255, by rfl⟩ : syracuseStep 6819007 = 10228511) B10228511
theorem B9092009 : Blo 2241435 9092009 := bstep (se 2 (by rfl) ⟨3409503, by rfl⟩ : syracuseStep 9092009 = 6819007) B6819007
theorem B6061339 : Blo 2241435 6061339 := bstep (se 1 (by rfl) ⟨4546004, by rfl⟩ : syracuseStep 6061339 = 9092009) B9092009
theorem B8081785 : Blo 2241435 8081785 := bstep (se 2 (by rfl) ⟨3030669, by rfl⟩ : syracuseStep 8081785 = 6061339) B6061339
theorem B43102853 : Blo 2241435 43102853 := bstep (se 4 (by rfl) ⟨4040892, by rfl⟩ : syracuseStep 43102853 = 8081785) B8081785
theorem B28735235 : Blo 2241435 28735235 := bstep (se 1 (by rfl) ⟨21551426, by rfl⟩ : syracuseStep 28735235 = 43102853) B43102853
theorem B19156823 : Blo 2241435 19156823 := bstep (se 1 (by rfl) ⟨14367617, by rfl⟩ : syracuseStep 19156823 = 28735235) B28735235
theorem B12771215 : Blo 2241435 12771215 := bstep (se 1 (by rfl) ⟨9578411, by rfl⟩ : syracuseStep 12771215 = 19156823) B19156823
theorem B8514143 : Blo 2241435 8514143 := bstep (se 1 (by rfl) ⟨6385607, by rfl⟩ : syracuseStep 8514143 = 12771215) B12771215
theorem B5676095 : Blo 2241435 5676095 := bstep (se 1 (by rfl) ⟨4257071, by rfl⟩ : syracuseStep 5676095 = 8514143) B8514143
theorem B3784063 : Blo 2241435 3784063 := bstep (se 1 (by rfl) ⟨2838047, by rfl⟩ : syracuseStep 3784063 = 5676095) B5676095
theorem B5045417 : Blo 2241435 5045417 := bstep (se 2 (by rfl) ⟨1892031, by rfl⟩ : syracuseStep 5045417 = 3784063) B3784063
theorem B3363611 : Blo 2241435 3363611 := bstep (se 1 (by rfl) ⟨2522708, by rfl⟩ : syracuseStep 3363611 = 5045417) B5045417
theorem B2242407 : Blo 2241435 2242407 := bstep (se 1 (by rfl) ⟨1681805, by rfl⟩ : syracuseStep 2242407 = 3363611) B3363611
theorem B2522713 : Blo 2241435 2522713 := bbase (se 2 (by rfl) ⟨946017, by rfl⟩ : syracuseStep 2522713 = 1892035) (by norm_num)
theorem B3363617 : Blo 2241435 3363617 := bstep (se 2 (by rfl) ⟨1261356, by rfl⟩ : syracuseStep 3363617 = 2522713) B2522713
theorem B2242411 : Blo 2241435 2242411 := bstep (se 1 (by rfl) ⟨1681808, by rfl⟩ : syracuseStep 2242411 = 3363617) B3363617
theorem B18184085 : Blo 2241435 18184085 := bbase (se 6 (by rfl) ⟨426189, by rfl⟩ : syracuseStep 18184085 = 852379) (by norm_num)
theorem B12122723 : Blo 2241435 12122723 := bstep (se 1 (by rfl) ⟨9092042, by rfl⟩ : syracuseStep 12122723 = 18184085) B18184085
theorem B8081815 : Blo 2241435 8081815 := bstep (se 1 (by rfl) ⟨6061361, by rfl⟩ : syracuseStep 8081815 = 12122723) B12122723
theorem B10775753 : Blo 2241435 10775753 := bstep (se 2 (by rfl) ⟨4040907, by rfl⟩ : syracuseStep 10775753 = 8081815) B8081815
theorem B7183835 : Blo 2241435 7183835 := bstep (se 1 (by rfl) ⟨5387876, by rfl⟩ : syracuseStep 7183835 = 10775753) B10775753
theorem B4789223 : Blo 2241435 4789223 := bstep (se 1 (by rfl) ⟨3591917, by rfl⟩ : syracuseStep 4789223 = 7183835) B7183835
theorem B3192815 : Blo 2241435 3192815 := bstep (se 1 (by rfl) ⟨2394611, by rfl⟩ : syracuseStep 3192815 = 4789223) B4789223
theorem B8514173 : Blo 2241435 8514173 := bstep (se 3 (by rfl) ⟨1596407, by rfl⟩ : syracuseStep 8514173 = 3192815) B3192815
theorem B5676115 : Blo 2241435 5676115 := bstep (se 1 (by rfl) ⟨4257086, by rfl⟩ : syracuseStep 5676115 = 8514173) B8514173
theorem B7568153 : Blo 2241435 7568153 := bstep (se 2 (by rfl) ⟨2838057, by rfl⟩ : syracuseStep 7568153 = 5676115) B5676115
theorem B5045435 : Blo 2241435 5045435 := bstep (se 1 (by rfl) ⟨3784076, by rfl⟩ : syracuseStep 5045435 = 7568153) B7568153
theorem B3363623 : Blo 2241435 3363623 := bstep (se 1 (by rfl) ⟨2522717, by rfl⟩ : syracuseStep 3363623 = 5045435) B5045435
theorem B2242415 : Blo 2241435 2242415 := bstep (se 1 (by rfl) ⟨1681811, by rfl⟩ : syracuseStep 2242415 = 3363623) B3363623
theorem B3363629 : Blo 2241435 3363629 := bbase (se 3 (by rfl) ⟨630680, by rfl⟩ : syracuseStep 3363629 = 1261361) (by norm_num)
theorem B2242419 : Blo 2241435 2242419 := bstep (se 1 (by rfl) ⟨1681814, by rfl⟩ : syracuseStep 2242419 = 3363629) B3363629
theorem B5045453 : Blo 2241435 5045453 := bbase (se 3 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 5045453 = 1892045) (by norm_num)
theorem B3363635 : Blo 2241435 3363635 := bstep (se 1 (by rfl) ⟨2522726, by rfl⟩ : syracuseStep 3363635 = 5045453) B5045453
theorem B2242423 : Blo 2241435 2242423 := bstep (se 1 (by rfl) ⟨1681817, by rfl⟩ : syracuseStep 2242423 = 3363635) B3363635
theorem B2838073 : Blo 2241435 2838073 := bbase (se 2 (by rfl) ⟨1064277, by rfl⟩ : syracuseStep 2838073 = 2128555) (by norm_num)
theorem B3784097 : Blo 2241435 3784097 := bstep (se 2 (by rfl) ⟨1419036, by rfl⟩ : syracuseStep 3784097 = 2838073) B2838073
theorem B2522731 : Blo 2241435 2522731 := bstep (se 1 (by rfl) ⟨1892048, by rfl⟩ : syracuseStep 2522731 = 3784097) B3784097
theorem B3363641 : Blo 2241435 3363641 := bstep (se 2 (by rfl) ⟨1261365, by rfl⟩ : syracuseStep 3363641 = 2522731) B2522731
theorem B2242427 : Blo 2241435 2242427 := bstep (se 1 (by rfl) ⟨1681820, by rfl⟩ : syracuseStep 2242427 = 3363641) B3363641
theorem B2693957 : Blo 2241435 2693957 := bbase (se 4 (by rfl) ⟨252558, by rfl⟩ : syracuseStep 2693957 = 505117) (by norm_num)
theorem B7183885 : Blo 2241435 7183885 := bstep (se 3 (by rfl) ⟨1346978, by rfl⟩ : syracuseStep 7183885 = 2693957) B2693957
theorem B9578513 : Blo 2241435 9578513 := bstep (se 2 (by rfl) ⟨3591942, by rfl⟩ : syracuseStep 9578513 = 7183885) B7183885
theorem B25542701 : Blo 2241435 25542701 := bstep (se 3 (by rfl) ⟨4789256, by rfl⟩ : syracuseStep 25542701 = 9578513) B9578513
theorem B17028467 : Blo 2241435 17028467 := bstep (se 1 (by rfl) ⟨12771350, by rfl⟩ : syracuseStep 17028467 = 25542701) B25542701
theorem B11352311 : Blo 2241435 11352311 := bstep (se 1 (by rfl) ⟨8514233, by rfl⟩ : syracuseStep 11352311 = 17028467) B17028467
theorem B7568207 : Blo 2241435 7568207 := bstep (se 1 (by rfl) ⟨5676155, by rfl⟩ : syracuseStep 7568207 = 11352311) B11352311
theorem B5045471 : Blo 2241435 5045471 := bstep (se 1 (by rfl) ⟨3784103, by rfl⟩ : syracuseStep 5045471 = 7568207) B7568207
theorem B3363647 : Blo 2241435 3363647 := bstep (se 1 (by rfl) ⟨2522735, by rfl⟩ : syracuseStep 3363647 = 5045471) B5045471
theorem B2242431 : Blo 2241435 2242431 := bstep (se 1 (by rfl) ⟨1681823, by rfl⟩ : syracuseStep 2242431 = 3363647) B3363647
theorem B3363653 : Blo 2241435 3363653 := bbase (se 4 (by rfl) ⟨315342, by rfl⟩ : syracuseStep 3363653 = 630685) (by norm_num)
theorem B2242435 : Blo 2241435 2242435 := bstep (se 1 (by rfl) ⟨1681826, by rfl⟩ : syracuseStep 2242435 = 3363653) B3363653
theorem B3784117 : Blo 2241435 3784117 := bbase (se 5 (by rfl) ⟨177380, by rfl⟩ : syracuseStep 3784117 = 354761) (by norm_num)
theorem B5045489 : Blo 2241435 5045489 := bstep (se 2 (by rfl) ⟨1892058, by rfl⟩ : syracuseStep 5045489 = 3784117) B3784117
theorem B3363659 : Blo 2241435 3363659 := bstep (se 1 (by rfl) ⟨2522744, by rfl⟩ : syracuseStep 3363659 = 5045489) B5045489
theorem B2242439 : Blo 2241435 2242439 := bstep (se 1 (by rfl) ⟨1681829, by rfl⟩ : syracuseStep 2242439 = 3363659) B3363659
theorem B2522749 : Blo 2241435 2522749 := bbase (se 3 (by rfl) ⟨473015, by rfl⟩ : syracuseStep 2522749 = 946031) (by norm_num)
theorem B3363665 : Blo 2241435 3363665 := bstep (se 2 (by rfl) ⟨1261374, by rfl⟩ : syracuseStep 3363665 = 2522749) B2522749
theorem B2242443 : Blo 2241435 2242443 := bstep (se 1 (by rfl) ⟨1681832, by rfl⟩ : syracuseStep 2242443 = 3363665) B3363665
theorem B7568261 : Blo 2241435 7568261 := bbase (se 4 (by rfl) ⟨709524, by rfl⟩ : syracuseStep 7568261 = 1419049) (by norm_num)
theorem B5045507 : Blo 2241435 5045507 := bstep (se 1 (by rfl) ⟨3784130, by rfl⟩ : syracuseStep 5045507 = 7568261) B7568261
theorem B3363671 : Blo 2241435 3363671 := bstep (se 1 (by rfl) ⟨2522753, by rfl⟩ : syracuseStep 3363671 = 5045507) B5045507
theorem B2242447 : Blo 2241435 2242447 := bstep (se 1 (by rfl) ⟨1681835, by rfl⟩ : syracuseStep 2242447 = 3363671) B3363671
theorem B3363677 : Blo 2241435 3363677 := bbase (se 3 (by rfl) ⟨630689, by rfl⟩ : syracuseStep 3363677 = 1261379) (by norm_num)
theorem B2242451 : Blo 2241435 2242451 := bstep (se 1 (by rfl) ⟨1681838, by rfl⟩ : syracuseStep 2242451 = 3363677) B3363677
theorem B5045525 : Blo 2241435 5045525 := bbase (se 6 (by rfl) ⟨118254, by rfl⟩ : syracuseStep 5045525 = 236509) (by norm_num)
theorem B3363683 : Blo 2241435 3363683 := bstep (se 1 (by rfl) ⟨2522762, by rfl⟩ : syracuseStep 3363683 = 5045525) B5045525
theorem B2242455 : Blo 2241435 2242455 := bstep (se 1 (by rfl) ⟨1681841, by rfl⟩ : syracuseStep 2242455 = 3363683) B3363683
theorem B8514341 : Blo 2241435 8514341 := bbase (se 4 (by rfl) ⟨798219, by rfl⟩ : syracuseStep 8514341 = 1596439) (by norm_num)
theorem B5676227 : Blo 2241435 5676227 := bstep (se 1 (by rfl) ⟨4257170, by rfl⟩ : syracuseStep 5676227 = 8514341) B8514341
theorem B3784151 : Blo 2241435 3784151 := bstep (se 1 (by rfl) ⟨2838113, by rfl⟩ : syracuseStep 3784151 = 5676227) B5676227
theorem B2522767 : Blo 2241435 2522767 := bstep (se 1 (by rfl) ⟨1892075, by rfl⟩ : syracuseStep 2522767 = 3784151) B3784151
theorem B3363689 : Blo 2241435 3363689 := bstep (se 2 (by rfl) ⟨1261383, by rfl⟩ : syracuseStep 3363689 = 2522767) B2522767
theorem B2242459 : Blo 2241435 2242459 := bstep (se 1 (by rfl) ⟨1681844, by rfl⟩ : syracuseStep 2242459 = 3363689) B3363689
theorem B4789325 : Blo 2241435 4789325 := bbase (se 3 (by rfl) ⟨897998, by rfl⟩ : syracuseStep 4789325 = 1795997) (by norm_num)
theorem B12771533 : Blo 2241435 12771533 := bstep (se 3 (by rfl) ⟨2394662, by rfl⟩ : syracuseStep 12771533 = 4789325) B4789325
theorem B8514355 : Blo 2241435 8514355 := bstep (se 1 (by rfl) ⟨6385766, by rfl⟩ : syracuseStep 8514355 = 12771533) B12771533
theorem B11352473 : Blo 2241435 11352473 := bstep (se 2 (by rfl) ⟨4257177, by rfl⟩ : syracuseStep 11352473 = 8514355) B8514355
theorem B7568315 : Blo 2241435 7568315 := bstep (se 1 (by rfl) ⟨5676236, by rfl⟩ : syracuseStep 7568315 = 11352473) B11352473
theorem B5045543 : Blo 2241435 5045543 := bstep (se 1 (by rfl) ⟨3784157, by rfl⟩ : syracuseStep 5045543 = 7568315) B7568315
theorem B3363695 : Blo 2241435 3363695 := bstep (se 1 (by rfl) ⟨2522771, by rfl⟩ : syracuseStep 3363695 = 5045543) B5045543
theorem B2242463 : Blo 2241435 2242463 := bstep (se 1 (by rfl) ⟨1681847, by rfl⟩ : syracuseStep 2242463 = 3363695) B3363695
theorem B3363701 : Blo 2241435 3363701 := bbase (se 5 (by rfl) ⟨157673, by rfl⟩ : syracuseStep 3363701 = 315347) (by norm_num)
theorem B2242467 : Blo 2241435 2242467 := bstep (se 1 (by rfl) ⟨1681850, by rfl⟩ : syracuseStep 2242467 = 3363701) B3363701
theorem B10228805 : Blo 2241435 10228805 := bbase (se 4 (by rfl) ⟨958950, by rfl⟩ : syracuseStep 10228805 = 1917901) (by norm_num)
theorem B6819203 : Blo 2241435 6819203 := bstep (se 1 (by rfl) ⟨5114402, by rfl⟩ : syracuseStep 6819203 = 10228805) B10228805
theorem B4546135 : Blo 2241435 4546135 := bstep (se 1 (by rfl) ⟨3409601, by rfl⟩ : syracuseStep 4546135 = 6819203) B6819203
theorem B24246053 : Blo 2241435 24246053 := bstep (se 4 (by rfl) ⟨2273067, by rfl⟩ : syracuseStep 24246053 = 4546135) B4546135
theorem B16164035 : Blo 2241435 16164035 := bstep (se 1 (by rfl) ⟨12123026, by rfl⟩ : syracuseStep 16164035 = 24246053) B24246053
theorem B10776023 : Blo 2241435 10776023 := bstep (se 1 (by rfl) ⟨8082017, by rfl⟩ : syracuseStep 10776023 = 16164035) B16164035
theorem B7184015 : Blo 2241435 7184015 := bstep (se 1 (by rfl) ⟨5388011, by rfl⟩ : syracuseStep 7184015 = 10776023) B10776023
theorem B4789343 : Blo 2241435 4789343 := bstep (se 1 (by rfl) ⟨3592007, by rfl⟩ : syracuseStep 4789343 = 7184015) B7184015
theorem B3192895 : Blo 2241435 3192895 := bstep (se 1 (by rfl) ⟨2394671, by rfl⟩ : syracuseStep 3192895 = 4789343) B4789343
theorem B4257193 : Blo 2241435 4257193 := bstep (se 2 (by rfl) ⟨1596447, by rfl⟩ : syracuseStep 4257193 = 3192895) B3192895
theorem B5676257 : Blo 2241435 5676257 := bstep (se 2 (by rfl) ⟨2128596, by rfl⟩ : syracuseStep 5676257 = 4257193) B4257193
theorem B3784171 : Blo 2241435 3784171 := bstep (se 1 (by rfl) ⟨2838128, by rfl⟩ : syracuseStep 3784171 = 5676257) B5676257
theorem B5045561 : Blo 2241435 5045561 := bstep (se 2 (by rfl) ⟨1892085, by rfl⟩ : syracuseStep 5045561 = 3784171) B3784171
theorem B3363707 : Blo 2241435 3363707 := bstep (se 1 (by rfl) ⟨2522780, by rfl⟩ : syracuseStep 3363707 = 5045561) B5045561
theorem B2242471 : Blo 2241435 2242471 := bstep (se 1 (by rfl) ⟨1681853, by rfl⟩ : syracuseStep 2242471 = 3363707) B3363707
theorem B2522785 : Blo 2241435 2522785 := bbase (se 2 (by rfl) ⟨946044, by rfl⟩ : syracuseStep 2522785 = 1892089) (by norm_num)
theorem B3363713 : Blo 2241435 3363713 := bstep (se 2 (by rfl) ⟨1261392, by rfl⟩ : syracuseStep 3363713 = 2522785) B2522785
theorem B2242475 : Blo 2241435 2242475 := bstep (se 1 (by rfl) ⟨1681856, by rfl⟩ : syracuseStep 2242475 = 3363713) B3363713
theorem B5676277 : Blo 2241435 5676277 := bbase (se 5 (by rfl) ⟨266075, by rfl⟩ : syracuseStep 5676277 = 532151) (by norm_num)
theorem B7568369 : Blo 2241435 7568369 := bstep (se 2 (by rfl) ⟨2838138, by rfl⟩ : syracuseStep 7568369 = 5676277) B5676277
theorem B5045579 : Blo 2241435 5045579 := bstep (se 1 (by rfl) ⟨3784184, by rfl⟩ : syracuseStep 5045579 = 7568369) B7568369
theorem B3363719 : Blo 2241435 3363719 := bstep (se 1 (by rfl) ⟨2522789, by rfl⟩ : syracuseStep 3363719 = 5045579) B5045579
theorem B2242479 : Blo 2241435 2242479 := bstep (se 1 (by rfl) ⟨1681859, by rfl⟩ : syracuseStep 2242479 = 3363719) B3363719
theorem B3363725 : Blo 2241435 3363725 := bbase (se 3 (by rfl) ⟨630698, by rfl⟩ : syracuseStep 3363725 = 1261397) (by norm_num)
theorem B2242483 : Blo 2241435 2242483 := bstep (se 1 (by rfl) ⟨1681862, by rfl⟩ : syracuseStep 2242483 = 3363725) B3363725
theorem B5045597 : Blo 2241435 5045597 := bbase (se 3 (by rfl) ⟨946049, by rfl⟩ : syracuseStep 5045597 = 1892099) (by norm_num)
theorem B3363731 : Blo 2241435 3363731 := bstep (se 1 (by rfl) ⟨2522798, by rfl⟩ : syracuseStep 3363731 = 5045597) B5045597
theorem B2242487 : Blo 2241435 2242487 := bstep (se 1 (by rfl) ⟨1681865, by rfl⟩ : syracuseStep 2242487 = 3363731) B3363731
theorem B3784205 : Blo 2241435 3784205 := bbase (se 3 (by rfl) ⟨709538, by rfl⟩ : syracuseStep 3784205 = 1419077) (by norm_num)
theorem B2522803 : Blo 2241435 2522803 := bstep (se 1 (by rfl) ⟨1892102, by rfl⟩ : syracuseStep 2522803 = 3784205) B3784205
theorem B3363737 : Blo 2241435 3363737 := bstep (se 2 (by rfl) ⟨1261401, by rfl⟩ : syracuseStep 3363737 = 2522803) B2522803
theorem B2242491 : Blo 2241435 2242491 := bstep (se 1 (by rfl) ⟨1681868, by rfl⟩ : syracuseStep 2242491 = 3363737) B3363737
theorem B3592045 : Blo 2241435 3592045 := bbase (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) (by norm_num)
theorem B19157573 : Blo 2241435 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B12771715 : Blo 2241435 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B17028953 : Blo 2241435 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B11352635 : Blo 2241435 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B7568423 : Blo 2241435 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B5045615 : Blo 2241435 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B3363743 : Blo 2241435 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B2242495 : Blo 2241435 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B3363749 : Blo 2241435 3363749 := bbase (se 4 (by rfl) ⟨315351, by rfl⟩ : syracuseStep 3363749 = 630703) (by norm_num)
theorem B2242499 : Blo 2241435 2242499 := bstep (se 1 (by rfl) ⟨1681874, by rfl⟩ : syracuseStep 2242499 = 3363749) B3363749
theorem B2838169 : Blo 2241435 2838169 := bbase (se 2 (by rfl) ⟨1064313, by rfl⟩ : syracuseStep 2838169 = 2128627) (by norm_num)
theorem B3784225 : Blo 2241435 3784225 := bstep (se 2 (by rfl) ⟨1419084, by rfl⟩ : syracuseStep 3784225 = 2838169) B2838169
theorem B5045633 : Blo 2241435 5045633 := bstep (se 2 (by rfl) ⟨1892112, by rfl⟩ : syracuseStep 5045633 = 3784225) B3784225
theorem B3363755 : Blo 2241435 3363755 := bstep (se 1 (by rfl) ⟨2522816, by rfl⟩ : syracuseStep 3363755 = 5045633) B5045633
theorem B2242503 : Blo 2241435 2242503 := bstep (se 1 (by rfl) ⟨1681877, by rfl⟩ : syracuseStep 2242503 = 3363755) B3363755
theorem B2522821 : Blo 2241435 2522821 := bbase (se 4 (by rfl) ⟨236514, by rfl⟩ : syracuseStep 2522821 = 473029) (by norm_num)
theorem B3363761 : Blo 2241435 3363761 := bstep (se 2 (by rfl) ⟨1261410, by rfl⟩ : syracuseStep 3363761 = 2522821) B2522821
theorem B2242507 : Blo 2241435 2242507 := bstep (se 1 (by rfl) ⟨1681880, by rfl⟩ : syracuseStep 2242507 = 3363761) B3363761
theorem B4257269 : Blo 2241435 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B2838179 : Blo 2241435 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B7568477 : Blo 2241435 7568477 := bstep (se 3 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 7568477 = 2838179) B2838179
theorem B5045651 : Blo 2241435 5045651 := bstep (se 1 (by rfl) ⟨3784238, by rfl⟩ : syracuseStep 5045651 = 7568477) B7568477
theorem B3363767 : Blo 2241435 3363767 := bstep (se 1 (by rfl) ⟨2522825, by rfl⟩ : syracuseStep 3363767 = 5045651) B5045651
theorem B2242511 : Blo 2241435 2242511 := bstep (se 1 (by rfl) ⟨1681883, by rfl⟩ : syracuseStep 2242511 = 3363767) B3363767
theorem B3363773 : Blo 2241435 3363773 := bbase (se 3 (by rfl) ⟨630707, by rfl⟩ : syracuseStep 3363773 = 1261415) (by norm_num)
theorem B2242515 : Blo 2241435 2242515 := bstep (se 1 (by rfl) ⟨1681886, by rfl⟩ : syracuseStep 2242515 = 3363773) B3363773
theorem B5045669 : Blo 2241435 5045669 := bbase (se 4 (by rfl) ⟨473031, by rfl⟩ : syracuseStep 5045669 = 946063) (by norm_num)
theorem B3363779 : Blo 2241435 3363779 := bstep (se 1 (by rfl) ⟨2522834, by rfl⟩ : syracuseStep 3363779 = 5045669) B5045669
theorem B2242519 : Blo 2241435 2242519 := bstep (se 1 (by rfl) ⟨1681889, by rfl⟩ : syracuseStep 2242519 = 3363779) B3363779
theorem B5676389 : Blo 2241435 5676389 := bbase (se 4 (by rfl) ⟨532161, by rfl⟩ : syracuseStep 5676389 = 1064323) (by norm_num)
theorem B3784259 : Blo 2241435 3784259 := bstep (se 1 (by rfl) ⟨2838194, by rfl⟩ : syracuseStep 3784259 = 5676389) B5676389
theorem B2522839 : Blo 2241435 2522839 := bstep (se 1 (by rfl) ⟨1892129, by rfl⟩ : syracuseStep 2522839 = 3784259) B3784259
theorem B3363785 : Blo 2241435 3363785 := bstep (se 2 (by rfl) ⟨1261419, by rfl⟩ : syracuseStep 3363785 = 2522839) B2522839
theorem B2242523 : Blo 2241435 2242523 := bstep (se 1 (by rfl) ⟨1681892, by rfl⟩ : syracuseStep 2242523 = 3363785) B3363785
theorem B2694073 : Blo 2241435 2694073 := bbase (se 2 (by rfl) ⟨1010277, by rfl⟩ : syracuseStep 2694073 = 2020555) (by norm_num)
theorem B3592097 : Blo 2241435 3592097 := bstep (se 2 (by rfl) ⟨1347036, by rfl⟩ : syracuseStep 3592097 = 2694073) B2694073
theorem B2394731 : Blo 2241435 2394731 := bstep (se 1 (by rfl) ⟨1796048, by rfl⟩ : syracuseStep 2394731 = 3592097) B3592097
theorem B6385949 : Blo 2241435 6385949 := bstep (se 3 (by rfl) ⟨1197365, by rfl⟩ : syracuseStep 6385949 = 2394731) B2394731
theorem B4257299 : Blo 2241435 4257299 := bstep (se 1 (by rfl) ⟨3192974, by rfl⟩ : syracuseStep 4257299 = 6385949) B6385949
theorem B11352797 : Blo 2241435 11352797 := bstep (se 3 (by rfl) ⟨2128649, by rfl⟩ : syracuseStep 11352797 = 4257299) B4257299
theorem B7568531 : Blo 2241435 7568531 := bstep (se 1 (by rfl) ⟨5676398, by rfl⟩ : syracuseStep 7568531 = 11352797) B11352797
theorem B5045687 : Blo 2241435 5045687 := bstep (se 1 (by rfl) ⟨3784265, by rfl⟩ : syracuseStep 5045687 = 7568531) B7568531
theorem B3363791 : Blo 2241435 3363791 := bstep (se 1 (by rfl) ⟨2522843, by rfl⟩ : syracuseStep 3363791 = 5045687) B5045687
theorem B2242527 : Blo 2241435 2242527 := bstep (se 1 (by rfl) ⟨1681895, by rfl⟩ : syracuseStep 2242527 = 3363791) B3363791
theorem B3363797 : Blo 2241435 3363797 := bbase (se 7 (by rfl) ⟨39419, by rfl⟩ : syracuseStep 3363797 = 78839) (by norm_num)
theorem B2242531 : Blo 2241435 2242531 := bstep (se 1 (by rfl) ⟨1681898, by rfl⟩ : syracuseStep 2242531 = 3363797) B3363797
theorem B8514629 : Blo 2241435 8514629 := bbase (se 4 (by rfl) ⟨798246, by rfl⟩ : syracuseStep 8514629 = 1596493) (by norm_num)
theorem B5676419 : Blo 2241435 5676419 := bstep (se 1 (by rfl) ⟨4257314, by rfl⟩ : syracuseStep 5676419 = 8514629) B8514629
theorem B3784279 : Blo 2241435 3784279 := bstep (se 1 (by rfl) ⟨2838209, by rfl⟩ : syracuseStep 3784279 = 5676419) B5676419
theorem B5045705 : Blo 2241435 5045705 := bstep (se 2 (by rfl) ⟨1892139, by rfl⟩ : syracuseStep 5045705 = 3784279) B3784279
theorem B3363803 : Blo 2241435 3363803 := bstep (se 1 (by rfl) ⟨2522852, by rfl⟩ : syracuseStep 3363803 = 5045705) B5045705
theorem B2242535 : Blo 2241435 2242535 := bstep (se 1 (by rfl) ⟨1681901, by rfl⟩ : syracuseStep 2242535 = 3363803) B3363803
theorem B2522857 : Blo 2241435 2522857 := bbase (se 2 (by rfl) ⟨946071, by rfl⟩ : syracuseStep 2522857 = 1892143) (by norm_num)
theorem B3363809 : Blo 2241435 3363809 := bstep (se 2 (by rfl) ⟨1261428, by rfl⟩ : syracuseStep 3363809 = 2522857) B2522857
theorem B2242539 : Blo 2241435 2242539 := bstep (se 1 (by rfl) ⟨1681904, by rfl⟩ : syracuseStep 2242539 = 3363809) B3363809
theorem B12771989 : Blo 2241435 12771989 := bbase (se 6 (by rfl) ⟨299343, by rfl⟩ : syracuseStep 12771989 = 598687) (by norm_num)
theorem B8514659 : Blo 2241435 8514659 := bstep (se 1 (by rfl) ⟨6385994, by rfl⟩ : syracuseStep 8514659 = 12771989) B12771989
theorem B5676439 : Blo 2241435 5676439 := bstep (se 1 (by rfl) ⟨4257329, by rfl⟩ : syracuseStep 5676439 = 8514659) B8514659
theorem B7568585 : Blo 2241435 7568585 := bstep (se 2 (by rfl) ⟨2838219, by rfl⟩ : syracuseStep 7568585 = 5676439) B5676439
theorem B5045723 : Blo 2241435 5045723 := bstep (se 1 (by rfl) ⟨3784292, by rfl⟩ : syracuseStep 5045723 = 7568585) B7568585
theorem B3363815 : Blo 2241435 3363815 := bstep (se 1 (by rfl) ⟨2522861, by rfl⟩ : syracuseStep 3363815 = 5045723) B5045723
theorem B2242543 : Blo 2241435 2242543 := bstep (se 1 (by rfl) ⟨1681907, by rfl⟩ : syracuseStep 2242543 = 3363815) B3363815
theorem B3363821 : Blo 2241435 3363821 := bbase (se 3 (by rfl) ⟨630716, by rfl⟩ : syracuseStep 3363821 = 1261433) (by norm_num)
theorem B2242547 : Blo 2241435 2242547 := bstep (se 1 (by rfl) ⟨1681910, by rfl⟩ : syracuseStep 2242547 = 3363821) B3363821
theorem B5045741 : Blo 2241435 5045741 := bbase (se 3 (by rfl) ⟨946076, by rfl⟩ : syracuseStep 5045741 = 1892153) (by norm_num)
theorem B3363827 : Blo 2241435 3363827 := bstep (se 1 (by rfl) ⟨2522870, by rfl⟩ : syracuseStep 3363827 = 5045741) B5045741
theorem B2242551 : Blo 2241435 2242551 := bstep (se 1 (by rfl) ⟨1681913, by rfl⟩ : syracuseStep 2242551 = 3363827) B3363827
theorem B6819461 : Blo 2241435 6819461 := bbase (se 4 (by rfl) ⟨639324, by rfl⟩ : syracuseStep 6819461 = 1278649) (by norm_num)
theorem B4546307 : Blo 2241435 4546307 := bstep (se 1 (by rfl) ⟨3409730, by rfl⟩ : syracuseStep 4546307 = 6819461) B6819461
theorem B3030871 : Blo 2241435 3030871 := bstep (se 1 (by rfl) ⟨2273153, by rfl⟩ : syracuseStep 3030871 = 4546307) B4546307
theorem B4041161 : Blo 2241435 4041161 := bstep (se 2 (by rfl) ⟨1515435, by rfl⟩ : syracuseStep 4041161 = 3030871) B3030871
theorem B2694107 : Blo 2241435 2694107 := bstep (se 1 (by rfl) ⟨2020580, by rfl⟩ : syracuseStep 2694107 = 4041161) B4041161
theorem B7184285 : Blo 2241435 7184285 := bstep (se 3 (by rfl) ⟨1347053, by rfl⟩ : syracuseStep 7184285 = 2694107) B2694107
theorem B4789523 : Blo 2241435 4789523 := bstep (se 1 (by rfl) ⟨3592142, by rfl⟩ : syracuseStep 4789523 = 7184285) B7184285
theorem B3193015 : Blo 2241435 3193015 := bstep (se 1 (by rfl) ⟨2394761, by rfl⟩ : syracuseStep 3193015 = 4789523) B4789523
theorem B4257353 : Blo 2241435 4257353 := bstep (se 2 (by rfl) ⟨1596507, by rfl⟩ : syracuseStep 4257353 = 3193015) B3193015
theorem B2838235 : Blo 2241435 2838235 := bstep (se 1 (by rfl) ⟨2128676, by rfl⟩ : syracuseStep 2838235 = 4257353) B4257353
theorem B3784313 : Blo 2241435 3784313 := bstep (se 2 (by rfl) ⟨1419117, by rfl⟩ : syracuseStep 3784313 = 2838235) B2838235
theorem B2522875 : Blo 2241435 2522875 := bstep (se 1 (by rfl) ⟨1892156, by rfl⟩ : syracuseStep 2522875 = 3784313) B3784313
theorem B3363833 : Blo 2241435 3363833 := bstep (se 2 (by rfl) ⟨1261437, by rfl⟩ : syracuseStep 3363833 = 2522875) B2522875
theorem B2242555 : Blo 2241435 2242555 := bstep (se 1 (by rfl) ⟨1681916, by rfl⟩ : syracuseStep 2242555 = 3363833) B3363833
theorem B5536253 : Blo 2241435 5536253 := bbase (se 3 (by rfl) ⟨1038047, by rfl⟩ : syracuseStep 5536253 = 2076095) (by norm_num)
theorem B3690835 : Blo 2241435 3690835 := bstep (se 1 (by rfl) ⟨2768126, by rfl⟩ : syracuseStep 3690835 = 5536253) B5536253
theorem B19684453 : Blo 2241435 19684453 := bstep (se 4 (by rfl) ⟨1845417, by rfl⟩ : syracuseStep 19684453 = 3690835) B3690835
theorem B26245937 : Blo 2241435 26245937 := bstep (se 2 (by rfl) ⟨9842226, by rfl⟩ : syracuseStep 26245937 = 19684453) B19684453
theorem B17497291 : Blo 2241435 17497291 := bstep (se 1 (by rfl) ⟨13122968, by rfl⟩ : syracuseStep 17497291 = 26245937) B26245937
theorem B23329721 : Blo 2241435 23329721 := bstep (se 2 (by rfl) ⟨8748645, by rfl⟩ : syracuseStep 23329721 = 17497291) B17497291
theorem B15553147 : Blo 2241435 15553147 := bstep (se 1 (by rfl) ⟨11664860, by rfl⟩ : syracuseStep 15553147 = 23329721) B23329721
theorem B20737529 : Blo 2241435 20737529 := bstep (se 2 (by rfl) ⟨7776573, by rfl⟩ : syracuseStep 20737529 = 15553147) B15553147
theorem B13825019 : Blo 2241435 13825019 := bstep (se 1 (by rfl) ⟨10368764, by rfl⟩ : syracuseStep 13825019 = 20737529) B20737529
theorem B9216679 : Blo 2241435 9216679 := bstep (se 1 (by rfl) ⟨6912509, by rfl⟩ : syracuseStep 9216679 = 13825019) B13825019
theorem B12288905 : Blo 2241435 12288905 := bstep (se 2 (by rfl) ⟨4608339, by rfl⟩ : syracuseStep 12288905 = 9216679) B9216679
theorem B8192603 : Blo 2241435 8192603 := bstep (se 1 (by rfl) ⟨6144452, by rfl⟩ : syracuseStep 8192603 = 12288905) B12288905
theorem B5461735 : Blo 2241435 5461735 := bstep (se 1 (by rfl) ⟨4096301, by rfl⟩ : syracuseStep 5461735 = 8192603) B8192603
theorem B7282313 : Blo 2241435 7282313 := bstep (se 2 (by rfl) ⟨2730867, by rfl⟩ : syracuseStep 7282313 = 5461735) B5461735
theorem B4854875 : Blo 2241435 4854875 := bstep (se 1 (by rfl) ⟨3641156, by rfl⟩ : syracuseStep 4854875 = 7282313) B7282313
theorem B51785333 : Blo 2241435 51785333 := bstep (se 5 (by rfl) ⟨2427437, by rfl⟩ : syracuseStep 51785333 = 4854875) B4854875
theorem B34523555 : Blo 2241435 34523555 := bstep (se 1 (by rfl) ⟨25892666, by rfl⟩ : syracuseStep 34523555 = 51785333) B51785333
theorem B92062813 : Blo 2241435 92062813 := bstep (se 3 (by rfl) ⟨17261777, by rfl⟩ : syracuseStep 92062813 = 34523555) B34523555
theorem B122750417 : Blo 2241435 122750417 := bstep (se 2 (by rfl) ⟨46031406, by rfl⟩ : syracuseStep 122750417 = 92062813) B92062813
theorem B81833611 : Blo 2241435 81833611 := bstep (se 1 (by rfl) ⟨61375208, by rfl⟩ : syracuseStep 81833611 = 122750417) B122750417
theorem B109111481 : Blo 2241435 109111481 := bstep (se 2 (by rfl) ⟨40916805, by rfl⟩ : syracuseStep 109111481 = 81833611) B81833611
theorem B72740987 : Blo 2241435 72740987 := bstep (se 1 (by rfl) ⟨54555740, by rfl⟩ : syracuseStep 72740987 = 109111481) B109111481
theorem B48493991 : Blo 2241435 48493991 := bstep (se 1 (by rfl) ⟨36370493, by rfl⟩ : syracuseStep 48493991 = 72740987) B72740987
theorem B129317309 : Blo 2241435 129317309 := bstep (se 3 (by rfl) ⟨24246995, by rfl⟩ : syracuseStep 129317309 = 48493991) B48493991
theorem B86211539 : Blo 2241435 86211539 := bstep (se 1 (by rfl) ⟨64658654, by rfl⟩ : syracuseStep 86211539 = 129317309) B129317309
theorem B57474359 : Blo 2241435 57474359 := bstep (se 1 (by rfl) ⟨43105769, by rfl⟩ : syracuseStep 57474359 = 86211539) B86211539
theorem B38316239 : Blo 2241435 38316239 := bstep (se 1 (by rfl) ⟨28737179, by rfl⟩ : syracuseStep 38316239 = 57474359) B57474359
theorem B25544159 : Blo 2241435 25544159 := bstep (se 1 (by rfl) ⟨19158119, by rfl⟩ : syracuseStep 25544159 = 38316239) B38316239
theorem B17029439 : Blo 2241435 17029439 := bstep (se 1 (by rfl) ⟨12772079, by rfl⟩ : syracuseStep 17029439 = 25544159) B25544159
theorem B11352959 : Blo 2241435 11352959 := bstep (se 1 (by rfl) ⟨8514719, by rfl⟩ : syracuseStep 11352959 = 17029439) B17029439
theorem B7568639 : Blo 2241435 7568639 := bstep (se 1 (by rfl) ⟨5676479, by rfl⟩ : syracuseStep 7568639 = 11352959) B11352959
theorem B5045759 : Blo 2241435 5045759 := bstep (se 1 (by rfl) ⟨3784319, by rfl⟩ : syracuseStep 5045759 = 7568639) B7568639
theorem B3363839 : Blo 2241435 3363839 := bstep (se 1 (by rfl) ⟨2522879, by rfl⟩ : syracuseStep 3363839 = 5045759) B5045759
theorem B2242559 : Blo 2241435 2242559 := bstep (se 1 (by rfl) ⟨1681919, by rfl⟩ : syracuseStep 2242559 = 3363839) B3363839
theorem B3363845 : Blo 2241435 3363845 := bbase (se 4 (by rfl) ⟨315360, by rfl⟩ : syracuseStep 3363845 = 630721) (by norm_num)
theorem B2242563 : Blo 2241435 2242563 := bstep (se 1 (by rfl) ⟨1681922, by rfl⟩ : syracuseStep 2242563 = 3363845) B3363845
theorem B3784333 : Blo 2241435 3784333 := bbase (se 3 (by rfl) ⟨709562, by rfl⟩ : syracuseStep 3784333 = 1419125) (by norm_num)
theorem B5045777 : Blo 2241435 5045777 := bstep (se 2 (by rfl) ⟨1892166, by rfl⟩ : syracuseStep 5045777 = 3784333) B3784333
theorem B3363851 : Blo 2241435 3363851 := bstep (se 1 (by rfl) ⟨2522888, by rfl⟩ : syracuseStep 3363851 = 5045777) B5045777
theorem B2242567 : Blo 2241435 2242567 := bstep (se 1 (by rfl) ⟨1681925, by rfl⟩ : syracuseStep 2242567 = 3363851) B3363851
theorem B2522893 : Blo 2241435 2522893 := bbase (se 3 (by rfl) ⟨473042, by rfl⟩ : syracuseStep 2522893 = 946085) (by norm_num)
theorem B3363857 : Blo 2241435 3363857 := bstep (se 2 (by rfl) ⟨1261446, by rfl⟩ : syracuseStep 3363857 = 2522893) B2522893
theorem B2242571 : Blo 2241435 2242571 := bstep (se 1 (by rfl) ⟨1681928, by rfl⟩ : syracuseStep 2242571 = 3363857) B3363857
theorem B7568693 : Blo 2241435 7568693 := bbase (se 5 (by rfl) ⟨354782, by rfl⟩ : syracuseStep 7568693 = 709565) (by norm_num)
theorem B5045795 : Blo 2241435 5045795 := bstep (se 1 (by rfl) ⟨3784346, by rfl⟩ : syracuseStep 5045795 = 7568693) B7568693
theorem B3363863 : Blo 2241435 3363863 := bstep (se 1 (by rfl) ⟨2522897, by rfl⟩ : syracuseStep 3363863 = 5045795) B5045795
theorem B2242575 : Blo 2241435 2242575 := bstep (se 1 (by rfl) ⟨1681931, by rfl⟩ : syracuseStep 2242575 = 3363863) B3363863
theorem B3363869 : Blo 2241435 3363869 := bbase (se 3 (by rfl) ⟨630725, by rfl⟩ : syracuseStep 3363869 = 1261451) (by norm_num)
theorem B2242579 : Blo 2241435 2242579 := bstep (se 1 (by rfl) ⟨1681934, by rfl⟩ : syracuseStep 2242579 = 3363869) B3363869
theorem B5045813 : Blo 2241435 5045813 := bbase (se 5 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 5045813 = 473045) (by norm_num)
theorem B3363875 : Blo 2241435 3363875 := bstep (se 1 (by rfl) ⟨2522906, by rfl⟩ : syracuseStep 3363875 = 5045813) B5045813
theorem B2242583 : Blo 2241435 2242583 := bstep (se 1 (by rfl) ⟨1681937, by rfl⟩ : syracuseStep 2242583 = 3363875) B3363875
theorem B2694145 : Blo 2241435 2694145 := bbase (se 2 (by rfl) ⟨1010304, by rfl⟩ : syracuseStep 2694145 = 2020609) (by norm_num)
theorem B3592193 : Blo 2241435 3592193 := bstep (se 2 (by rfl) ⟨1347072, by rfl⟩ : syracuseStep 3592193 = 2694145) B2694145
theorem B9579181 : Blo 2241435 9579181 := bstep (se 3 (by rfl) ⟨1796096, by rfl⟩ : syracuseStep 9579181 = 3592193) B3592193
theorem B12772241 : Blo 2241435 12772241 := bstep (se 2 (by rfl) ⟨4789590, by rfl⟩ : syracuseStep 12772241 = 9579181) B9579181
theorem B8514827 : Blo 2241435 8514827 := bstep (se 1 (by rfl) ⟨6386120, by rfl⟩ : syracuseStep 8514827 = 12772241) B12772241
theorem B5676551 : Blo 2241435 5676551 := bstep (se 1 (by rfl) ⟨4257413, by rfl⟩ : syracuseStep 5676551 = 8514827) B8514827
theorem B3784367 : Blo 2241435 3784367 := bstep (se 1 (by rfl) ⟨2838275, by rfl⟩ : syracuseStep 3784367 = 5676551) B5676551
theorem B2522911 : Blo 2241435 2522911 := bstep (se 1 (by rfl) ⟨1892183, by rfl⟩ : syracuseStep 2522911 = 3784367) B3784367
theorem B3363881 : Blo 2241435 3363881 := bstep (se 2 (by rfl) ⟨1261455, by rfl⟩ : syracuseStep 3363881 = 2522911) B2522911
theorem B2242587 : Blo 2241435 2242587 := bstep (se 1 (by rfl) ⟨1681940, by rfl⟩ : syracuseStep 2242587 = 3363881) B3363881
theorem B2273189 : Blo 2241435 2273189 := bbase (se 4 (by rfl) ⟨213111, by rfl⟩ : syracuseStep 2273189 = 426223) (by norm_num)
theorem B6061837 : Blo 2241435 6061837 := bstep (se 3 (by rfl) ⟨1136594, by rfl⟩ : syracuseStep 6061837 = 2273189) B2273189
theorem B8082449 : Blo 2241435 8082449 := bstep (se 2 (by rfl) ⟨3030918, by rfl⟩ : syracuseStep 8082449 = 6061837) B6061837
theorem B5388299 : Blo 2241435 5388299 := bstep (se 1 (by rfl) ⟨4041224, by rfl⟩ : syracuseStep 5388299 = 8082449) B8082449
theorem B3592199 : Blo 2241435 3592199 := bstep (se 1 (by rfl) ⟨2694149, by rfl⟩ : syracuseStep 3592199 = 5388299) B5388299
theorem B9579197 : Blo 2241435 9579197 := bstep (se 3 (by rfl) ⟨1796099, by rfl⟩ : syracuseStep 9579197 = 3592199) B3592199
theorem B6386131 : Blo 2241435 6386131 := bstep (se 1 (by rfl) ⟨4789598, by rfl⟩ : syracuseStep 6386131 = 9579197) B9579197
theorem B8514841 : Blo 2241435 8514841 := bstep (se 2 (by rfl) ⟨3193065, by rfl⟩ : syracuseStep 8514841 = 6386131) B6386131
theorem B11353121 : Blo 2241435 11353121 := bstep (se 2 (by rfl) ⟨4257420, by rfl⟩ : syracuseStep 11353121 = 8514841) B8514841
theorem B7568747 : Blo 2241435 7568747 := bstep (se 1 (by rfl) ⟨5676560, by rfl⟩ : syracuseStep 7568747 = 11353121) B11353121
theorem B5045831 : Blo 2241435 5045831 := bstep (se 1 (by rfl) ⟨3784373, by rfl⟩ : syracuseStep 5045831 = 7568747) B7568747
theorem B3363887 : Blo 2241435 3363887 := bstep (se 1 (by rfl) ⟨2522915, by rfl⟩ : syracuseStep 3363887 = 5045831) B5045831
theorem B2242591 : Blo 2241435 2242591 := bstep (se 1 (by rfl) ⟨1681943, by rfl⟩ : syracuseStep 2242591 = 3363887) B3363887
theorem B3363893 : Blo 2241435 3363893 := bbase (se 5 (by rfl) ⟨157682, by rfl⟩ : syracuseStep 3363893 = 315365) (by norm_num)
theorem B2242595 : Blo 2241435 2242595 := bstep (se 1 (by rfl) ⟨1681946, by rfl⟩ : syracuseStep 2242595 = 3363893) B3363893
theorem B5676581 : Blo 2241435 5676581 := bbase (se 4 (by rfl) ⟨532179, by rfl⟩ : syracuseStep 5676581 = 1064359) (by norm_num)
theorem B3784387 : Blo 2241435 3784387 := bstep (se 1 (by rfl) ⟨2838290, by rfl⟩ : syracuseStep 3784387 = 5676581) B5676581
theorem B5045849 : Blo 2241435 5045849 := bstep (se 2 (by rfl) ⟨1892193, by rfl⟩ : syracuseStep 5045849 = 3784387) B3784387
theorem B3363899 : Blo 2241435 3363899 := bstep (se 1 (by rfl) ⟨2522924, by rfl⟩ : syracuseStep 3363899 = 5045849) B5045849
theorem B2242599 : Blo 2241435 2242599 := bstep (se 1 (by rfl) ⟨1681949, by rfl⟩ : syracuseStep 2242599 = 3363899) B3363899
theorem B2522929 : Blo 2241435 2522929 := bbase (se 2 (by rfl) ⟨946098, by rfl⟩ : syracuseStep 2522929 = 1892197) (by norm_num)
theorem B3363905 : Blo 2241435 3363905 := bstep (se 2 (by rfl) ⟨1261464, by rfl⟩ : syracuseStep 3363905 = 2522929) B2522929
theorem B2242603 : Blo 2241435 2242603 := bstep (se 1 (by rfl) ⟨1681952, by rfl⟩ : syracuseStep 2242603 = 3363905) B3363905
theorem B2694169 : Blo 2241435 2694169 := bbase (se 2 (by rfl) ⟨1010313, by rfl⟩ : syracuseStep 2694169 = 2020627) (by norm_num)
theorem B3592225 : Blo 2241435 3592225 := bstep (se 2 (by rfl) ⟨1347084, by rfl⟩ : syracuseStep 3592225 = 2694169) B2694169
theorem B4789633 : Blo 2241435 4789633 := bstep (se 2 (by rfl) ⟨1796112, by rfl⟩ : syracuseStep 4789633 = 3592225) B3592225
theorem B6386177 : Blo 2241435 6386177 := bstep (se 2 (by rfl) ⟨2394816, by rfl⟩ : syracuseStep 6386177 = 4789633) B4789633
theorem B4257451 : Blo 2241435 4257451 := bstep (se 1 (by rfl) ⟨3193088, by rfl⟩ : syracuseStep 4257451 = 6386177) B6386177
theorem B5676601 : Blo 2241435 5676601 := bstep (se 2 (by rfl) ⟨2128725, by rfl⟩ : syracuseStep 5676601 = 4257451) B4257451
theorem B7568801 : Blo 2241435 7568801 := bstep (se 2 (by rfl) ⟨2838300, by rfl⟩ : syracuseStep 7568801 = 5676601) B5676601
theorem B5045867 : Blo 2241435 5045867 := bstep (se 1 (by rfl) ⟨3784400, by rfl⟩ : syracuseStep 5045867 = 7568801) B7568801
theorem B3363911 : Blo 2241435 3363911 := bstep (se 1 (by rfl) ⟨2522933, by rfl⟩ : syracuseStep 3363911 = 5045867) B5045867
theorem B2242607 : Blo 2241435 2242607 := bstep (se 1 (by rfl) ⟨1681955, by rfl⟩ : syracuseStep 2242607 = 3363911) B3363911
theorem B3363917 : Blo 2241435 3363917 := bbase (se 3 (by rfl) ⟨630734, by rfl⟩ : syracuseStep 3363917 = 1261469) (by norm_num)
theorem B2242611 : Blo 2241435 2242611 := bstep (se 1 (by rfl) ⟨1681958, by rfl⟩ : syracuseStep 2242611 = 3363917) B3363917
theorem B5045885 : Blo 2241435 5045885 := bbase (se 3 (by rfl) ⟨946103, by rfl⟩ : syracuseStep 5045885 = 1892207) (by norm_num)
theorem B3363923 : Blo 2241435 3363923 := bstep (se 1 (by rfl) ⟨2522942, by rfl⟩ : syracuseStep 3363923 = 5045885) B5045885
theorem B2242615 : Blo 2241435 2242615 := bstep (se 1 (by rfl) ⟨1681961, by rfl⟩ : syracuseStep 2242615 = 3363923) B3363923
theorem B3784421 : Blo 2241435 3784421 := bbase (se 4 (by rfl) ⟨354789, by rfl⟩ : syracuseStep 3784421 = 709579) (by norm_num)
theorem B2522947 : Blo 2241435 2522947 := bstep (se 1 (by rfl) ⟨1892210, by rfl⟩ : syracuseStep 2522947 = 3784421) B3784421
theorem B3363929 : Blo 2241435 3363929 := bstep (se 2 (by rfl) ⟨1261473, by rfl⟩ : syracuseStep 3363929 = 2522947) B2522947
theorem B2242619 : Blo 2241435 2242619 := bstep (se 1 (by rfl) ⟨1681964, by rfl⟩ : syracuseStep 2242619 = 3363929) B3363929
theorem B7184501 : Blo 2241435 7184501 := bbase (se 5 (by rfl) ⟨336773, by rfl⟩ : syracuseStep 7184501 = 673547) (by norm_num)
theorem B4789667 : Blo 2241435 4789667 := bstep (se 1 (by rfl) ⟨3592250, by rfl⟩ : syracuseStep 4789667 = 7184501) B7184501
theorem B3193111 : Blo 2241435 3193111 := bstep (se 1 (by rfl) ⟨2394833, by rfl⟩ : syracuseStep 3193111 = 4789667) B4789667
theorem B17029925 : Blo 2241435 17029925 := bstep (se 4 (by rfl) ⟨1596555, by rfl⟩ : syracuseStep 17029925 = 3193111) B3193111
theorem B11353283 : Blo 2241435 11353283 := bstep (se 1 (by rfl) ⟨8514962, by rfl⟩ : syracuseStep 11353283 = 17029925) B17029925
theorem B7568855 : Blo 2241435 7568855 := bstep (se 1 (by rfl) ⟨5676641, by rfl⟩ : syracuseStep 7568855 = 11353283) B11353283
theorem B5045903 : Blo 2241435 5045903 := bstep (se 1 (by rfl) ⟨3784427, by rfl⟩ : syracuseStep 5045903 = 7568855) B7568855
theorem B3363935 : Blo 2241435 3363935 := bstep (se 1 (by rfl) ⟨2522951, by rfl⟩ : syracuseStep 3363935 = 5045903) B5045903
theorem B2242623 : Blo 2241435 2242623 := bstep (se 1 (by rfl) ⟨1681967, by rfl⟩ : syracuseStep 2242623 = 3363935) B3363935
theorem B3363941 : Blo 2241435 3363941 := bbase (se 4 (by rfl) ⟨315369, by rfl⟩ : syracuseStep 3363941 = 630739) (by norm_num)
theorem B2242627 : Blo 2241435 2242627 := bstep (se 1 (by rfl) ⟨1681970, by rfl⟩ : syracuseStep 2242627 = 3363941) B3363941
theorem B4789685 : Blo 2241435 4789685 := bbase (se 5 (by rfl) ⟨224516, by rfl⟩ : syracuseStep 4789685 = 449033) (by norm_num)
theorem B3193123 : Blo 2241435 3193123 := bstep (se 1 (by rfl) ⟨2394842, by rfl⟩ : syracuseStep 3193123 = 4789685) B4789685
theorem B4257497 : Blo 2241435 4257497 := bstep (se 2 (by rfl) ⟨1596561, by rfl⟩ : syracuseStep 4257497 = 3193123) B3193123
theorem B2838331 : Blo 2241435 2838331 := bstep (se 1 (by rfl) ⟨2128748, by rfl⟩ : syracuseStep 2838331 = 4257497) B4257497
theorem B3784441 : Blo 2241435 3784441 := bstep (se 2 (by rfl) ⟨1419165, by rfl⟩ : syracuseStep 3784441 = 2838331) B2838331
theorem B5045921 : Blo 2241435 5045921 := bstep (se 2 (by rfl) ⟨1892220, by rfl⟩ : syracuseStep 5045921 = 3784441) B3784441
theorem B3363947 : Blo 2241435 3363947 := bstep (se 1 (by rfl) ⟨2522960, by rfl⟩ : syracuseStep 3363947 = 5045921) B5045921
theorem B2242631 : Blo 2241435 2242631 := bstep (se 1 (by rfl) ⟨1681973, by rfl⟩ : syracuseStep 2242631 = 3363947) B3363947
theorem B2522965 : Blo 2241435 2522965 := bbase (se 9 (by rfl) ⟨7391, by rfl⟩ : syracuseStep 2522965 = 14783) (by norm_num)
theorem B3363953 : Blo 2241435 3363953 := bstep (se 2 (by rfl) ⟨1261482, by rfl⟩ : syracuseStep 3363953 = 2522965) B2522965
theorem B2242635 : Blo 2241435 2242635 := bstep (se 1 (by rfl) ⟨1681976, by rfl⟩ : syracuseStep 2242635 = 3363953) B3363953
theorem B2838341 : Blo 2241435 2838341 := bbase (se 4 (by rfl) ⟨266094, by rfl⟩ : syracuseStep 2838341 = 532189) (by norm_num)
theorem B7568909 : Blo 2241435 7568909 := bstep (se 3 (by rfl) ⟨1419170, by rfl⟩ : syracuseStep 7568909 = 2838341) B2838341
theorem B5045939 : Blo 2241435 5045939 := bstep (se 1 (by rfl) ⟨3784454, by rfl⟩ : syracuseStep 5045939 = 7568909) B7568909
theorem B3363959 : Blo 2241435 3363959 := bstep (se 1 (by rfl) ⟨2522969, by rfl⟩ : syracuseStep 3363959 = 5045939) B5045939
theorem B2242639 : Blo 2241435 2242639 := bstep (se 1 (by rfl) ⟨1681979, by rfl⟩ : syracuseStep 2242639 = 3363959) B3363959
theorem B3363965 : Blo 2241435 3363965 := bbase (se 3 (by rfl) ⟨630743, by rfl⟩ : syracuseStep 3363965 = 1261487) (by norm_num)
theorem B2242643 : Blo 2241435 2242643 := bstep (se 1 (by rfl) ⟨1681982, by rfl⟩ : syracuseStep 2242643 = 3363965) B3363965
theorem B5045957 : Blo 2241435 5045957 := bbase (se 4 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 5045957 = 946117) (by norm_num)
theorem B3363971 : Blo 2241435 3363971 := bstep (se 1 (by rfl) ⟨2522978, by rfl⟩ : syracuseStep 3363971 = 5045957) B5045957
theorem B2242647 : Blo 2241435 2242647 := bstep (se 1 (by rfl) ⟨1681985, by rfl⟩ : syracuseStep 2242647 = 3363971) B3363971
theorem B3456397 : Blo 2241435 3456397 := bbase (se 3 (by rfl) ⟨648074, by rfl⟩ : syracuseStep 3456397 = 1296149) (by norm_num)
theorem B18434117 : Blo 2241435 18434117 := bstep (se 4 (by rfl) ⟨1728198, by rfl⟩ : syracuseStep 18434117 = 3456397) B3456397
theorem B12289411 : Blo 2241435 12289411 := bstep (se 1 (by rfl) ⟨9217058, by rfl⟩ : syracuseStep 12289411 = 18434117) B18434117
theorem B65543525 : Blo 2241435 65543525 := bstep (se 4 (by rfl) ⟨6144705, by rfl⟩ : syracuseStep 65543525 = 12289411) B12289411
theorem B43695683 : Blo 2241435 43695683 := bstep (se 1 (by rfl) ⟨32771762, by rfl⟩ : syracuseStep 43695683 = 65543525) B65543525
theorem B29130455 : Blo 2241435 29130455 := bstep (se 1 (by rfl) ⟨21847841, by rfl⟩ : syracuseStep 29130455 = 43695683) B43695683
theorem B19420303 : Blo 2241435 19420303 := bstep (se 1 (by rfl) ⟨14565227, by rfl⟩ : syracuseStep 19420303 = 29130455) B29130455
theorem B25893737 : Blo 2241435 25893737 := bstep (se 2 (by rfl) ⟨9710151, by rfl⟩ : syracuseStep 25893737 = 19420303) B19420303
theorem B17262491 : Blo 2241435 17262491 := bstep (se 1 (by rfl) ⟨12946868, by rfl⟩ : syracuseStep 17262491 = 25893737) B25893737
theorem B46033309 : Blo 2241435 46033309 := bstep (se 3 (by rfl) ⟨8631245, by rfl⟩ : syracuseStep 46033309 = 17262491) B17262491
theorem B61377745 : Blo 2241435 61377745 := bstep (se 2 (by rfl) ⟨23016654, by rfl⟩ : syracuseStep 61377745 = 46033309) B46033309
theorem B81836993 : Blo 2241435 81836993 := bstep (se 2 (by rfl) ⟨30688872, by rfl⟩ : syracuseStep 81836993 = 61377745) B61377745
theorem B54557995 : Blo 2241435 54557995 := bstep (se 1 (by rfl) ⟨40918496, by rfl⟩ : syracuseStep 54557995 = 81836993) B81836993
theorem B72743993 : Blo 2241435 72743993 := bstep (se 2 (by rfl) ⟨27278997, by rfl⟩ : syracuseStep 72743993 = 54557995) B54557995
theorem B48495995 : Blo 2241435 48495995 := bstep (se 1 (by rfl) ⟨36371996, by rfl⟩ : syracuseStep 48495995 = 72743993) B72743993
theorem B32330663 : Blo 2241435 32330663 := bstep (se 1 (by rfl) ⟨24247997, by rfl⟩ : syracuseStep 32330663 = 48495995) B48495995
theorem B21553775 : Blo 2241435 21553775 := bstep (se 1 (by rfl) ⟨16165331, by rfl⟩ : syracuseStep 21553775 = 32330663) B32330663
theorem B14369183 : Blo 2241435 14369183 := bstep (se 1 (by rfl) ⟨10776887, by rfl⟩ : syracuseStep 14369183 = 21553775) B21553775
theorem B9579455 : Blo 2241435 9579455 := bstep (se 1 (by rfl) ⟨7184591, by rfl⟩ : syracuseStep 9579455 = 14369183) B14369183
theorem B6386303 : Blo 2241435 6386303 := bstep (se 1 (by rfl) ⟨4789727, by rfl⟩ : syracuseStep 6386303 = 9579455) B9579455
theorem B4257535 : Blo 2241435 4257535 := bstep (se 1 (by rfl) ⟨3193151, by rfl⟩ : syracuseStep 4257535 = 6386303) B6386303
theorem B5676713 : Blo 2241435 5676713 := bstep (se 2 (by rfl) ⟨2128767, by rfl⟩ : syracuseStep 5676713 = 4257535) B4257535
theorem B3784475 : Blo 2241435 3784475 := bstep (se 1 (by rfl) ⟨2838356, by rfl⟩ : syracuseStep 3784475 = 5676713) B5676713
theorem B2522983 : Blo 2241435 2522983 := bstep (se 1 (by rfl) ⟨1892237, by rfl⟩ : syracuseStep 2522983 = 3784475) B3784475
theorem B3363977 : Blo 2241435 3363977 := bstep (se 2 (by rfl) ⟨1261491, by rfl⟩ : syracuseStep 3363977 = 2522983) B2522983
theorem B2242651 : Blo 2241435 2242651 := bstep (se 1 (by rfl) ⟨1681988, by rfl⟩ : syracuseStep 2242651 = 3363977) B3363977
theorem B11353445 : Blo 2241435 11353445 := bbase (se 4 (by rfl) ⟨1064385, by rfl⟩ : syracuseStep 11353445 = 2128771) (by norm_num)
theorem B7568963 : Blo 2241435 7568963 := bstep (se 1 (by rfl) ⟨5676722, by rfl⟩ : syracuseStep 7568963 = 11353445) B11353445
theorem B5045975 : Blo 2241435 5045975 := bstep (se 1 (by rfl) ⟨3784481, by rfl⟩ : syracuseStep 5045975 = 7568963) B7568963
theorem B3363983 : Blo 2241435 3363983 := bstep (se 1 (by rfl) ⟨2522987, by rfl⟩ : syracuseStep 3363983 = 5045975) B5045975
theorem B2242655 : Blo 2241435 2242655 := bstep (se 1 (by rfl) ⟨1681991, by rfl⟩ : syracuseStep 2242655 = 3363983) B3363983
theorem B3363989 : Blo 2241435 3363989 := bbase (se 6 (by rfl) ⟨78843, by rfl⟩ : syracuseStep 3363989 = 157687) (by norm_num)
theorem B2242659 : Blo 2241435 2242659 := bstep (se 1 (by rfl) ⟨1681994, by rfl⟩ : syracuseStep 2242659 = 3363989) B3363989
theorem B7184629 : Blo 2241435 7184629 := bbase (se 5 (by rfl) ⟨336779, by rfl⟩ : syracuseStep 7184629 = 673559) (by norm_num)
theorem B9579505 : Blo 2241435 9579505 := bstep (se 2 (by rfl) ⟨3592314, by rfl⟩ : syracuseStep 9579505 = 7184629) B7184629
theorem B12772673 : Blo 2241435 12772673 := bstep (se 2 (by rfl) ⟨4789752, by rfl⟩ : syracuseStep 12772673 = 9579505) B9579505
theorem B8515115 : Blo 2241435 8515115 := bstep (se 1 (by rfl) ⟨6386336, by rfl⟩ : syracuseStep 8515115 = 12772673) B12772673
theorem B5676743 : Blo 2241435 5676743 := bstep (se 1 (by rfl) ⟨4257557, by rfl⟩ : syracuseStep 5676743 = 8515115) B8515115
theorem B3784495 : Blo 2241435 3784495 := bstep (se 1 (by rfl) ⟨2838371, by rfl⟩ : syracuseStep 3784495 = 5676743) B5676743
theorem B5045993 : Blo 2241435 5045993 := bstep (se 2 (by rfl) ⟨1892247, by rfl⟩ : syracuseStep 5045993 = 3784495) B3784495
theorem B3363995 : Blo 2241435 3363995 := bstep (se 1 (by rfl) ⟨2522996, by rfl⟩ : syracuseStep 3363995 = 5045993) B5045993
theorem B2242663 : Blo 2241435 2242663 := bstep (se 1 (by rfl) ⟨1681997, by rfl⟩ : syracuseStep 2242663 = 3363995) B3363995
theorem B2523001 : Blo 2241435 2523001 := bbase (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) (by norm_num)
theorem B3364001 : Blo 2241435 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B2242667 : Blo 2241435 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B6062053 : Blo 2241435 6062053 := bbase (se 4 (by rfl) ⟨568317, by rfl⟩ : syracuseStep 6062053 = 1136635) (by norm_num)
theorem B8082737 : Blo 2241435 8082737 := bstep (se 2 (by rfl) ⟨3031026, by rfl⟩ : syracuseStep 8082737 = 6062053) B6062053
theorem B5388491 : Blo 2241435 5388491 := bstep (se 1 (by rfl) ⟨4041368, by rfl⟩ : syracuseStep 5388491 = 8082737) B8082737
theorem B14369309 : Blo 2241435 14369309 := bstep (se 3 (by rfl) ⟨2694245, by rfl⟩ : syracuseStep 14369309 = 5388491) B5388491
theorem B9579539 : Blo 2241435 9579539 := bstep (se 1 (by rfl) ⟨7184654, by rfl⟩ : syracuseStep 9579539 = 14369309) B14369309
theorem B6386359 : Blo 2241435 6386359 := bstep (se 1 (by rfl) ⟨4789769, by rfl⟩ : syracuseStep 6386359 = 9579539) B9579539
theorem B8515145 : Blo 2241435 8515145 := bstep (se 2 (by rfl) ⟨3193179, by rfl⟩ : syracuseStep 8515145 = 6386359) B6386359
theorem B5676763 : Blo 2241435 5676763 := bstep (se 1 (by rfl) ⟨4257572, by rfl⟩ : syracuseStep 5676763 = 8515145) B8515145
theorem B7569017 : Blo 2241435 7569017 := bstep (se 2 (by rfl) ⟨2838381, by rfl⟩ : syracuseStep 7569017 = 5676763) B5676763
theorem B5046011 : Blo 2241435 5046011 := bstep (se 1 (by rfl) ⟨3784508, by rfl⟩ : syracuseStep 5046011 = 7569017) B7569017
theorem B3364007 : Blo 2241435 3364007 := bstep (se 1 (by rfl) ⟨2523005, by rfl⟩ : syracuseStep 3364007 = 5046011) B5046011
theorem B2242671 : Blo 2241435 2242671 := bstep (se 1 (by rfl) ⟨1682003, by rfl⟩ : syracuseStep 2242671 = 3364007) B3364007
theorem B3364013 : Blo 2241435 3364013 := bbase (se 3 (by rfl) ⟨630752, by rfl⟩ : syracuseStep 3364013 = 1261505) (by norm_num)
theorem B2242675 : Blo 2241435 2242675 := bstep (se 1 (by rfl) ⟨1682006, by rfl⟩ : syracuseStep 2242675 = 3364013) B3364013
theorem B5046029 : Blo 2241435 5046029 := bbase (se 3 (by rfl) ⟨946130, by rfl⟩ : syracuseStep 5046029 = 1892261) (by norm_num)
theorem B3364019 : Blo 2241435 3364019 := bstep (se 1 (by rfl) ⟨2523014, by rfl⟩ : syracuseStep 3364019 = 5046029) B5046029
theorem B2242679 : Blo 2241435 2242679 := bstep (se 1 (by rfl) ⟨1682009, by rfl⟩ : syracuseStep 2242679 = 3364019) B3364019
theorem B2838397 : Blo 2241435 2838397 := bbase (se 3 (by rfl) ⟨532199, by rfl⟩ : syracuseStep 2838397 = 1064399) (by norm_num)
theorem B3784529 : Blo 2241435 3784529 := bstep (se 2 (by rfl) ⟨1419198, by rfl⟩ : syracuseStep 3784529 = 2838397) B2838397
theorem B2523019 : Blo 2241435 2523019 := bstep (se 1 (by rfl) ⟨1892264, by rfl⟩ : syracuseStep 2523019 = 3784529) B3784529
theorem B3364025 : Blo 2241435 3364025 := bstep (se 2 (by rfl) ⟨1261509, by rfl⟩ : syracuseStep 3364025 = 2523019) B2523019
theorem B2242683 : Blo 2241435 2242683 := bstep (se 1 (by rfl) ⟨1682012, by rfl⟩ : syracuseStep 2242683 = 3364025) B3364025
theorem B4041397 : Blo 2241435 4041397 := bbase (se 5 (by rfl) ⟨189440, by rfl⟩ : syracuseStep 4041397 = 378881) (by norm_num)
theorem B5388529 : Blo 2241435 5388529 := bstep (se 2 (by rfl) ⟨2020698, by rfl⟩ : syracuseStep 5388529 = 4041397) B4041397
theorem B7184705 : Blo 2241435 7184705 := bstep (se 2 (by rfl) ⟨2694264, by rfl⟩ : syracuseStep 7184705 = 5388529) B5388529
theorem B19159213 : Blo 2241435 19159213 := bstep (se 3 (by rfl) ⟨3592352, by rfl⟩ : syracuseStep 19159213 = 7184705) B7184705
theorem B25545617 : Blo 2241435 25545617 := bstep (se 2 (by rfl) ⟨9579606, by rfl⟩ : syracuseStep 25545617 = 19159213) B19159213
theorem B17030411 : Blo 2241435 17030411 := bstep (se 1 (by rfl) ⟨12772808, by rfl⟩ : syracuseStep 17030411 = 25545617) B25545617
theorem B11353607 : Blo 2241435 11353607 := bstep (se 1 (by rfl) ⟨8515205, by rfl⟩ : syracuseStep 11353607 = 17030411) B17030411
theorem B7569071 : Blo 2241435 7569071 := bstep (se 1 (by rfl) ⟨5676803, by rfl⟩ : syracuseStep 7569071 = 11353607) B11353607
theorem B5046047 : Blo 2241435 5046047 := bstep (se 1 (by rfl) ⟨3784535, by rfl⟩ : syracuseStep 5046047 = 7569071) B7569071
theorem B3364031 : Blo 2241435 3364031 := bstep (se 1 (by rfl) ⟨2523023, by rfl⟩ : syracuseStep 3364031 = 5046047) B5046047
theorem B2242687 : Blo 2241435 2242687 := bstep (se 1 (by rfl) ⟨1682015, by rfl⟩ : syracuseStep 2242687 = 3364031) B3364031
theorem B3364037 : Blo 2241435 3364037 := bbase (se 4 (by rfl) ⟨315378, by rfl⟩ : syracuseStep 3364037 = 630757) (by norm_num)
theorem B2242691 : Blo 2241435 2242691 := bstep (se 1 (by rfl) ⟨1682018, by rfl⟩ : syracuseStep 2242691 = 3364037) B3364037
theorem B3784549 : Blo 2241435 3784549 := bbase (se 4 (by rfl) ⟨354801, by rfl⟩ : syracuseStep 3784549 = 709603) (by norm_num)
theorem B5046065 : Blo 2241435 5046065 := bstep (se 2 (by rfl) ⟨1892274, by rfl⟩ : syracuseStep 5046065 = 3784549) B3784549
theorem B3364043 : Blo 2241435 3364043 := bstep (se 1 (by rfl) ⟨2523032, by rfl⟩ : syracuseStep 3364043 = 5046065) B5046065
theorem B2242695 : Blo 2241435 2242695 := bstep (se 1 (by rfl) ⟨1682021, by rfl⟩ : syracuseStep 2242695 = 3364043) B3364043
theorem B2523037 : Blo 2241435 2523037 := bbase (se 3 (by rfl) ⟨473069, by rfl⟩ : syracuseStep 2523037 = 946139) (by norm_num)
theorem B3364049 : Blo 2241435 3364049 := bstep (se 2 (by rfl) ⟨1261518, by rfl⟩ : syracuseStep 3364049 = 2523037) B2523037
theorem B2242699 : Blo 2241435 2242699 := bstep (se 1 (by rfl) ⟨1682024, by rfl⟩ : syracuseStep 2242699 = 3364049) B3364049
theorem B7569125 : Blo 2241435 7569125 := bbase (se 4 (by rfl) ⟨709605, by rfl⟩ : syracuseStep 7569125 = 1419211) (by norm_num)
theorem B5046083 : Blo 2241435 5046083 := bstep (se 1 (by rfl) ⟨3784562, by rfl⟩ : syracuseStep 5046083 = 7569125) B7569125
theorem B3364055 : Blo 2241435 3364055 := bstep (se 1 (by rfl) ⟨2523041, by rfl⟩ : syracuseStep 3364055 = 5046083) B5046083
theorem B2242703 : Blo 2241435 2242703 := bstep (se 1 (by rfl) ⟨1682027, by rfl⟩ : syracuseStep 2242703 = 3364055) B3364055
theorem B3364061 : Blo 2241435 3364061 := bbase (se 3 (by rfl) ⟨630761, by rfl⟩ : syracuseStep 3364061 = 1261523) (by norm_num)
theorem B2242707 : Blo 2241435 2242707 := bstep (se 1 (by rfl) ⟨1682030, by rfl⟩ : syracuseStep 2242707 = 3364061) B3364061
theorem B5046101 : Blo 2241435 5046101 := bbase (se 9 (by rfl) ⟨14783, by rfl⟩ : syracuseStep 5046101 = 29567) (by norm_num)
theorem B3364067 : Blo 2241435 3364067 := bstep (se 1 (by rfl) ⟨2523050, by rfl⟩ : syracuseStep 3364067 = 5046101) B5046101
theorem B2242711 : Blo 2241435 2242711 := bstep (se 1 (by rfl) ⟨1682033, by rfl⟩ : syracuseStep 2242711 = 3364067) B3364067
theorem B6386485 : Blo 2241435 6386485 := bbase (se 5 (by rfl) ⟨299366, by rfl⟩ : syracuseStep 6386485 = 598733) (by norm_num)
theorem B8515313 : Blo 2241435 8515313 := bstep (se 2 (by rfl) ⟨3193242, by rfl⟩ : syracuseStep 8515313 = 6386485) B6386485
theorem B5676875 : Blo 2241435 5676875 := bstep (se 1 (by rfl) ⟨4257656, by rfl⟩ : syracuseStep 5676875 = 8515313) B8515313
theorem B3784583 : Blo 2241435 3784583 := bstep (se 1 (by rfl) ⟨2838437, by rfl⟩ : syracuseStep 3784583 = 5676875) B5676875
theorem B2523055 : Blo 2241435 2523055 := bstep (se 1 (by rfl) ⟨1892291, by rfl⟩ : syracuseStep 2523055 = 3784583) B3784583
theorem B3364073 : Blo 2241435 3364073 := bstep (se 2 (by rfl) ⟨1261527, by rfl⟩ : syracuseStep 3364073 = 2523055) B2523055
theorem B2242715 : Blo 2241435 2242715 := bstep (se 1 (by rfl) ⟨1682036, by rfl⟩ : syracuseStep 2242715 = 3364073) B3364073
theorem B3072445 : Blo 2241435 3072445 := bbase (se 3 (by rfl) ⟨576083, by rfl⟩ : syracuseStep 3072445 = 1152167) (by norm_num)
theorem B16386373 : Blo 2241435 16386373 := bstep (se 4 (by rfl) ⟨1536222, by rfl⟩ : syracuseStep 16386373 = 3072445) B3072445
theorem B21848497 : Blo 2241435 21848497 := bstep (se 2 (by rfl) ⟨8193186, by rfl⟩ : syracuseStep 21848497 = 16386373) B16386373
theorem B116525317 : Blo 2241435 116525317 := bstep (se 4 (by rfl) ⟨10924248, by rfl⟩ : syracuseStep 116525317 = 21848497) B21848497
theorem B155367089 : Blo 2241435 155367089 := bstep (se 2 (by rfl) ⟨58262658, by rfl⟩ : syracuseStep 155367089 = 116525317) B116525317
theorem B103578059 : Blo 2241435 103578059 := bstep (se 1 (by rfl) ⟨77683544, by rfl⟩ : syracuseStep 103578059 = 155367089) B155367089
theorem B276208157 : Blo 2241435 276208157 := bstep (se 3 (by rfl) ⟨51789029, by rfl⟩ : syracuseStep 276208157 = 103578059) B103578059
theorem B184138771 : Blo 2241435 184138771 := bstep (se 1 (by rfl) ⟨138104078, by rfl⟩ : syracuseStep 184138771 = 276208157) B276208157
theorem B245518361 : Blo 2241435 245518361 := bstep (se 2 (by rfl) ⟨92069385, by rfl⟩ : syracuseStep 245518361 = 184138771) B184138771
theorem B163678907 : Blo 2241435 163678907 := bstep (se 1 (by rfl) ⟨122759180, by rfl⟩ : syracuseStep 163678907 = 245518361) B245518361
theorem B109119271 : Blo 2241435 109119271 := bstep (se 1 (by rfl) ⟨81839453, by rfl⟩ : syracuseStep 109119271 = 163678907) B163678907
theorem B145492361 : Blo 2241435 145492361 := bstep (se 2 (by rfl) ⟨54559635, by rfl⟩ : syracuseStep 145492361 = 109119271) B109119271
theorem B96994907 : Blo 2241435 96994907 := bstep (se 1 (by rfl) ⟨72746180, by rfl⟩ : syracuseStep 96994907 = 145492361) B145492361
theorem B64663271 : Blo 2241435 64663271 := bstep (se 1 (by rfl) ⟨48497453, by rfl⟩ : syracuseStep 64663271 = 96994907) B96994907
theorem B43108847 : Blo 2241435 43108847 := bstep (se 1 (by rfl) ⟨32331635, by rfl⟩ : syracuseStep 43108847 = 64663271) B64663271
theorem B28739231 : Blo 2241435 28739231 := bstep (se 1 (by rfl) ⟨21554423, by rfl⟩ : syracuseStep 28739231 = 43108847) B43108847
theorem B19159487 : Blo 2241435 19159487 := bstep (se 1 (by rfl) ⟨14369615, by rfl⟩ : syracuseStep 19159487 = 28739231) B28739231
theorem B12772991 : Blo 2241435 12772991 := bstep (se 1 (by rfl) ⟨9579743, by rfl⟩ : syracuseStep 12772991 = 19159487) B19159487
theorem B8515327 : Blo 2241435 8515327 := bstep (se 1 (by rfl) ⟨6386495, by rfl⟩ : syracuseStep 8515327 = 12772991) B12772991
theorem B11353769 : Blo 2241435 11353769 := bstep (se 2 (by rfl) ⟨4257663, by rfl⟩ : syracuseStep 11353769 = 8515327) B8515327
theorem B7569179 : Blo 2241435 7569179 := bstep (se 1 (by rfl) ⟨5676884, by rfl⟩ : syracuseStep 7569179 = 11353769) B11353769
theorem B5046119 : Blo 2241435 5046119 := bstep (se 1 (by rfl) ⟨3784589, by rfl⟩ : syracuseStep 5046119 = 7569179) B7569179
theorem B3364079 : Blo 2241435 3364079 := bstep (se 1 (by rfl) ⟨2523059, by rfl⟩ : syracuseStep 3364079 = 5046119) B5046119
theorem B2242719 : Blo 2241435 2242719 := bstep (se 1 (by rfl) ⟨1682039, by rfl⟩ : syracuseStep 2242719 = 3364079) B3364079
theorem B3364085 : Blo 2241435 3364085 := bbase (se 5 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 3364085 = 315383) (by norm_num)
theorem B2242723 : Blo 2241435 2242723 := bstep (se 1 (by rfl) ⟨1682042, by rfl⟩ : syracuseStep 2242723 = 3364085) B3364085
theorem B2694313 : Blo 2241435 2694313 := bbase (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) (by norm_num)
theorem B14369669 : Blo 2241435 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B9579779 : Blo 2241435 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B6386519 : Blo 2241435 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B4257679 : Blo 2241435 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B5676905 : Blo 2241435 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B3784603 : Blo 2241435 3784603 := bstep (se 1 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 3784603 = 5676905) B5676905
theorem B5046137 : Blo 2241435 5046137 := bstep (se 2 (by rfl) ⟨1892301, by rfl⟩ : syracuseStep 5046137 = 3784603) B3784603
theorem B3364091 : Blo 2241435 3364091 := bstep (se 1 (by rfl) ⟨2523068, by rfl⟩ : syracuseStep 3364091 = 5046137) B5046137
theorem B2242727 : Blo 2241435 2242727 := bstep (se 1 (by rfl) ⟨1682045, by rfl⟩ : syracuseStep 2242727 = 3364091) B3364091
theorem B2523073 : Blo 2241435 2523073 := bbase (se 2 (by rfl) ⟨946152, by rfl⟩ : syracuseStep 2523073 = 1892305) (by norm_num)
theorem B3364097 : Blo 2241435 3364097 := bstep (se 2 (by rfl) ⟨1261536, by rfl⟩ : syracuseStep 3364097 = 2523073) B2523073
theorem B2242731 : Blo 2241435 2242731 := bstep (se 1 (by rfl) ⟨1682048, by rfl⟩ : syracuseStep 2242731 = 3364097) B3364097
theorem B5676925 : Blo 2241435 5676925 := bbase (se 3 (by rfl) ⟨1064423, by rfl⟩ : syracuseStep 5676925 = 2128847) (by norm_num)
theorem B7569233 : Blo 2241435 7569233 := bstep (se 2 (by rfl) ⟨2838462, by rfl⟩ : syracuseStep 7569233 = 5676925) B5676925
theorem B5046155 : Blo 2241435 5046155 := bstep (se 1 (by rfl) ⟨3784616, by rfl⟩ : syracuseStep 5046155 = 7569233) B7569233
theorem B3364103 : Blo 2241435 3364103 := bstep (se 1 (by rfl) ⟨2523077, by rfl⟩ : syracuseStep 3364103 = 5046155) B5046155
theorem B2242735 : Blo 2241435 2242735 := bstep (se 1 (by rfl) ⟨1682051, by rfl⟩ : syracuseStep 2242735 = 3364103) B3364103
theorem B3364109 : Blo 2241435 3364109 := bbase (se 3 (by rfl) ⟨630770, by rfl⟩ : syracuseStep 3364109 = 1261541) (by norm_num)
theorem B2242739 : Blo 2241435 2242739 := bstep (se 1 (by rfl) ⟨1682054, by rfl⟩ : syracuseStep 2242739 = 3364109) B3364109
theorem B5046173 : Blo 2241435 5046173 := bbase (se 3 (by rfl) ⟨946157, by rfl⟩ : syracuseStep 5046173 = 1892315) (by norm_num)
theorem B3364115 : Blo 2241435 3364115 := bstep (se 1 (by rfl) ⟨2523086, by rfl⟩ : syracuseStep 3364115 = 5046173) B5046173
theorem B2242743 : Blo 2241435 2242743 := bstep (se 1 (by rfl) ⟨1682057, by rfl⟩ : syracuseStep 2242743 = 3364115) B3364115
theorem B3784637 : Blo 2241435 3784637 := bbase (se 3 (by rfl) ⟨709619, by rfl⟩ : syracuseStep 3784637 = 1419239) (by norm_num)
theorem B2523091 : Blo 2241435 2523091 := bstep (se 1 (by rfl) ⟨1892318, by rfl⟩ : syracuseStep 2523091 = 3784637) B3784637
theorem B3364121 : Blo 2241435 3364121 := bstep (se 2 (by rfl) ⟨1261545, by rfl⟩ : syracuseStep 3364121 = 2523091) B2523091
theorem B2242747 : Blo 2241435 2242747 := bstep (se 1 (by rfl) ⟨1682060, by rfl⟩ : syracuseStep 2242747 = 3364121) B3364121
theorem B12773173 : Blo 2241435 12773173 := bbase (se 5 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 12773173 = 1197485) (by norm_num)
theorem B17030897 : Blo 2241435 17030897 := bstep (se 2 (by rfl) ⟨6386586, by rfl⟩ : syracuseStep 17030897 = 12773173) B12773173
theorem B11353931 : Blo 2241435 11353931 := bstep (se 1 (by rfl) ⟨8515448, by rfl⟩ : syracuseStep 11353931 = 17030897) B17030897
theorem B7569287 : Blo 2241435 7569287 := bstep (se 1 (by rfl) ⟨5676965, by rfl⟩ : syracuseStep 7569287 = 11353931) B11353931
theorem B5046191 : Blo 2241435 5046191 := bstep (se 1 (by rfl) ⟨3784643, by rfl⟩ : syracuseStep 5046191 = 7569287) B7569287
theorem B3364127 : Blo 2241435 3364127 := bstep (se 1 (by rfl) ⟨2523095, by rfl⟩ : syracuseStep 3364127 = 5046191) B5046191
theorem B2242751 : Blo 2241435 2242751 := bstep (se 1 (by rfl) ⟨1682063, by rfl⟩ : syracuseStep 2242751 = 3364127) B3364127
theorem B3364133 : Blo 2241435 3364133 := bbase (se 4 (by rfl) ⟨315387, by rfl⟩ : syracuseStep 3364133 = 630775) (by norm_num)
theorem B2242755 : Blo 2241435 2242755 := bstep (se 1 (by rfl) ⟨1682066, by rfl⟩ : syracuseStep 2242755 = 3364133) B3364133
theorem B2838493 : Blo 2241435 2838493 := bbase (se 3 (by rfl) ⟨532217, by rfl⟩ : syracuseStep 2838493 = 1064435) (by norm_num)
theorem B3784657 : Blo 2241435 3784657 := bstep (se 2 (by rfl) ⟨1419246, by rfl⟩ : syracuseStep 3784657 = 2838493) B2838493
theorem B5046209 : Blo 2241435 5046209 := bstep (se 2 (by rfl) ⟨1892328, by rfl⟩ : syracuseStep 5046209 = 3784657) B3784657
theorem B3364139 : Blo 2241435 3364139 := bstep (se 1 (by rfl) ⟨2523104, by rfl⟩ : syracuseStep 3364139 = 5046209) B5046209
theorem B2242759 : Blo 2241435 2242759 := bstep (se 1 (by rfl) ⟨1682069, by rfl⟩ : syracuseStep 2242759 = 3364139) B3364139
theorem B2523109 : Blo 2241435 2523109 := bbase (se 4 (by rfl) ⟨236541, by rfl⟩ : syracuseStep 2523109 = 473083) (by norm_num)
theorem B3364145 : Blo 2241435 3364145 := bstep (se 2 (by rfl) ⟨1261554, by rfl⟩ : syracuseStep 3364145 = 2523109) B2523109
theorem B2242763 : Blo 2241435 2242763 := bstep (se 1 (by rfl) ⟨1682072, by rfl⟩ : syracuseStep 2242763 = 3364145) B3364145
theorem B10777445 : Blo 2241435 10777445 := bbase (se 4 (by rfl) ⟨1010385, by rfl⟩ : syracuseStep 10777445 = 2020771) (by norm_num)
theorem B7184963 : Blo 2241435 7184963 := bstep (se 1 (by rfl) ⟨5388722, by rfl⟩ : syracuseStep 7184963 = 10777445) B10777445
theorem B4789975 : Blo 2241435 4789975 := bstep (se 1 (by rfl) ⟨3592481, by rfl⟩ : syracuseStep 4789975 = 7184963) B7184963
theorem B6386633 : Blo 2241435 6386633 := bstep (se 2 (by rfl) ⟨2394987, by rfl⟩ : syracuseStep 6386633 = 4789975) B4789975
theorem B4257755 : Blo 2241435 4257755 := bstep (se 1 (by rfl) ⟨3193316, by rfl⟩ : syracuseStep 4257755 = 6386633) B6386633
theorem B2838503 : Blo 2241435 2838503 := bstep (se 1 (by rfl) ⟨2128877, by rfl⟩ : syracuseStep 2838503 = 4257755) B4257755
theorem B7569341 : Blo 2241435 7569341 := bstep (se 3 (by rfl) ⟨1419251, by rfl⟩ : syracuseStep 7569341 = 2838503) B2838503
theorem B5046227 : Blo 2241435 5046227 := bstep (se 1 (by rfl) ⟨3784670, by rfl⟩ : syracuseStep 5046227 = 7569341) B7569341
theorem B3364151 : Blo 2241435 3364151 := bstep (se 1 (by rfl) ⟨2523113, by rfl⟩ : syracuseStep 3364151 = 5046227) B5046227
theorem B2242767 : Blo 2241435 2242767 := bstep (se 1 (by rfl) ⟨1682075, by rfl⟩ : syracuseStep 2242767 = 3364151) B3364151
theorem B3364157 : Blo 2241435 3364157 := bbase (se 3 (by rfl) ⟨630779, by rfl⟩ : syracuseStep 3364157 = 1261559) (by norm_num)
theorem B2242771 : Blo 2241435 2242771 := bstep (se 1 (by rfl) ⟨1682078, by rfl⟩ : syracuseStep 2242771 = 3364157) B3364157
theorem B5046245 : Blo 2241435 5046245 := bbase (se 4 (by rfl) ⟨473085, by rfl⟩ : syracuseStep 5046245 = 946171) (by norm_num)
theorem B3364163 : Blo 2241435 3364163 := bstep (se 1 (by rfl) ⟨2523122, by rfl⟩ : syracuseStep 3364163 = 5046245) B5046245
theorem B2242775 : Blo 2241435 2242775 := bstep (se 1 (by rfl) ⟨1682081, by rfl⟩ : syracuseStep 2242775 = 3364163) B3364163
theorem B5677037 : Blo 2241435 5677037 := bbase (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) (by norm_num)
theorem B3784691 : Blo 2241435 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B2523127 : Blo 2241435 2523127 := bstep (se 1 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 2523127 = 3784691) B3784691
theorem B3364169 : Blo 2241435 3364169 := bstep (se 2 (by rfl) ⟨1261563, by rfl⟩ : syracuseStep 3364169 = 2523127) B2523127
theorem B2242779 : Blo 2241435 2242779 := bstep (se 1 (by rfl) ⟨1682084, by rfl⟩ : syracuseStep 2242779 = 3364169) B3364169
theorem B6062357 : Blo 2241435 6062357 := bbase (se 6 (by rfl) ⟨142086, by rfl⟩ : syracuseStep 6062357 = 284173) (by norm_num)
theorem B4041571 : Blo 2241435 4041571 := bstep (se 1 (by rfl) ⟨3031178, by rfl⟩ : syracuseStep 4041571 = 6062357) B6062357
theorem B5388761 : Blo 2241435 5388761 := bstep (se 2 (by rfl) ⟨2020785, by rfl⟩ : syracuseStep 5388761 = 4041571) B4041571
theorem B3592507 : Blo 2241435 3592507 := bstep (se 1 (by rfl) ⟨2694380, by rfl⟩ : syracuseStep 3592507 = 5388761) B5388761
theorem B4790009 : Blo 2241435 4790009 := bstep (se 2 (by rfl) ⟨1796253, by rfl⟩ : syracuseStep 4790009 = 3592507) B3592507
theorem B3193339 : Blo 2241435 3193339 := bstep (se 1 (by rfl) ⟨2395004, by rfl⟩ : syracuseStep 3193339 = 4790009) B4790009
theorem B4257785 : Blo 2241435 4257785 := bstep (se 2 (by rfl) ⟨1596669, by rfl⟩ : syracuseStep 4257785 = 3193339) B3193339
theorem B11354093 : Blo 2241435 11354093 := bstep (se 3 (by rfl) ⟨2128892, by rfl⟩ : syracuseStep 11354093 = 4257785) B4257785
theorem B7569395 : Blo 2241435 7569395 := bstep (se 1 (by rfl) ⟨5677046, by rfl⟩ : syracuseStep 7569395 = 11354093) B11354093
theorem B5046263 : Blo 2241435 5046263 := bstep (se 1 (by rfl) ⟨3784697, by rfl⟩ : syracuseStep 5046263 = 7569395) B7569395
theorem B3364175 : Blo 2241435 3364175 := bstep (se 1 (by rfl) ⟨2523131, by rfl⟩ : syracuseStep 3364175 = 5046263) B5046263
theorem B2242783 : Blo 2241435 2242783 := bstep (se 1 (by rfl) ⟨1682087, by rfl⟩ : syracuseStep 2242783 = 3364175) B3364175
theorem B3364181 : Blo 2241435 3364181 := bbase (se 17 (by rfl) ⟨38, by rfl⟩ : syracuseStep 3364181 = 77) (by norm_num)
theorem B2242787 : Blo 2241435 2242787 := bstep (se 1 (by rfl) ⟨1682090, by rfl⟩ : syracuseStep 2242787 = 3364181) B3364181
theorem B2395013 : Blo 2241435 2395013 := bbase (se 4 (by rfl) ⟨224532, by rfl⟩ : syracuseStep 2395013 = 449065) (by norm_num)
theorem B6386701 : Blo 2241435 6386701 := bstep (se 3 (by rfl) ⟨1197506, by rfl⟩ : syracuseStep 6386701 = 2395013) B2395013
theorem B8515601 : Blo 2241435 8515601 := bstep (se 2 (by rfl) ⟨3193350, by rfl⟩ : syracuseStep 8515601 = 6386701) B6386701
theorem B5677067 : Blo 2241435 5677067 := bstep (se 1 (by rfl) ⟨4257800, by rfl⟩ : syracuseStep 5677067 = 8515601) B8515601
theorem B3784711 : Blo 2241435 3784711 := bstep (se 1 (by rfl) ⟨2838533, by rfl⟩ : syracuseStep 3784711 = 5677067) B5677067
theorem B5046281 : Blo 2241435 5046281 := bstep (se 2 (by rfl) ⟨1892355, by rfl⟩ : syracuseStep 5046281 = 3784711) B3784711
theorem B3364187 : Blo 2241435 3364187 := bstep (se 1 (by rfl) ⟨2523140, by rfl⟩ : syracuseStep 3364187 = 5046281) B5046281
theorem B2242791 : Blo 2241435 2242791 := bstep (se 1 (by rfl) ⟨1682093, by rfl⟩ : syracuseStep 2242791 = 3364187) B3364187
theorem B2523145 : Blo 2241435 2523145 := bbase (se 2 (by rfl) ⟨946179, by rfl⟩ : syracuseStep 2523145 = 1892359) (by norm_num)
theorem B3364193 : Blo 2241435 3364193 := bstep (se 2 (by rfl) ⟨1261572, by rfl⟩ : syracuseStep 3364193 = 2523145) B2523145
theorem B2242795 : Blo 2241435 2242795 := bstep (se 1 (by rfl) ⟨1682096, by rfl⟩ : syracuseStep 2242795 = 3364193) B3364193
theorem B6473861 : Blo 2241435 6473861 := bbase (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) (by norm_num)
theorem B4315907 : Blo 2241435 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B11509085 : Blo 2241435 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B30690893 : Blo 2241435 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B20460595 : Blo 2241435 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B27280793 : Blo 2241435 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B18187195 : Blo 2241435 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B24249593 : Blo 2241435 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B16166395 : Blo 2241435 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B21555193 : Blo 2241435 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B28740257 : Blo 2241435 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B19160171 : Blo 2241435 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B12773447 : Blo 2241435 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B8515631 : Blo 2241435 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B5677087 : Blo 2241435 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B7569449 : Blo 2241435 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B5046299 : Blo 2241435 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B3364199 : Blo 2241435 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B2242799 : Blo 2241435 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B3364205 : Blo 2241435 3364205 := bbase (se 3 (by rfl) ⟨630788, by rfl⟩ : syracuseStep 3364205 = 1261577) (by norm_num)
theorem B2242803 : Blo 2241435 2242803 := bstep (se 1 (by rfl) ⟨1682102, by rfl⟩ : syracuseStep 2242803 = 3364205) B3364205
theorem B5046317 : Blo 2241435 5046317 := bbase (se 3 (by rfl) ⟨946184, by rfl⟩ : syracuseStep 5046317 = 1892369) (by norm_num)
theorem B3364211 : Blo 2241435 3364211 := bstep (se 1 (by rfl) ⟨2523158, by rfl⟩ : syracuseStep 3364211 = 5046317) B5046317
theorem B2242807 : Blo 2241435 2242807 := bstep (se 1 (by rfl) ⟨1682105, by rfl⟩ : syracuseStep 2242807 = 3364211) B3364211
theorem B2557589 : Blo 2241435 2557589 := bbase (se 6 (by rfl) ⟨59943, by rfl⟩ : syracuseStep 2557589 = 119887) (by norm_num)
theorem B6820237 : Blo 2241435 6820237 := bstep (se 3 (by rfl) ⟨1278794, by rfl⟩ : syracuseStep 6820237 = 2557589) B2557589
theorem B9093649 : Blo 2241435 9093649 := bstep (se 2 (by rfl) ⟨3410118, by rfl⟩ : syracuseStep 9093649 = 6820237) B6820237
theorem B12124865 : Blo 2241435 12124865 := bstep (se 2 (by rfl) ⟨4546824, by rfl⟩ : syracuseStep 12124865 = 9093649) B9093649
theorem B8083243 : Blo 2241435 8083243 := bstep (se 1 (by rfl) ⟨6062432, by rfl⟩ : syracuseStep 8083243 = 12124865) B12124865
theorem B10777657 : Blo 2241435 10777657 := bstep (se 2 (by rfl) ⟨4041621, by rfl⟩ : syracuseStep 10777657 = 8083243) B8083243
theorem B14370209 : Blo 2241435 14370209 := bstep (se 2 (by rfl) ⟨5388828, by rfl⟩ : syracuseStep 14370209 = 10777657) B10777657
theorem B9580139 : Blo 2241435 9580139 := bstep (se 1 (by rfl) ⟨7185104, by rfl⟩ : syracuseStep 9580139 = 14370209) B14370209
theorem B6386759 : Blo 2241435 6386759 := bstep (se 1 (by rfl) ⟨4790069, by rfl⟩ : syracuseStep 6386759 = 9580139) B9580139
theorem B4257839 : Blo 2241435 4257839 := bstep (se 1 (by rfl) ⟨3193379, by rfl⟩ : syracuseStep 4257839 = 6386759) B6386759
theorem B2838559 : Blo 2241435 2838559 := bstep (se 1 (by rfl) ⟨2128919, by rfl⟩ : syracuseStep 2838559 = 4257839) B4257839
theorem B3784745 : Blo 2241435 3784745 := bstep (se 2 (by rfl) ⟨1419279, by rfl⟩ : syracuseStep 3784745 = 2838559) B2838559
theorem B2523163 : Blo 2241435 2523163 := bstep (se 1 (by rfl) ⟨1892372, by rfl⟩ : syracuseStep 2523163 = 3784745) B3784745
theorem B3364217 : Blo 2241435 3364217 := bstep (se 2 (by rfl) ⟨1261581, by rfl⟩ : syracuseStep 3364217 = 2523163) B2523163
theorem B2242811 : Blo 2241435 2242811 := bstep (se 1 (by rfl) ⟨1682108, by rfl⟩ : syracuseStep 2242811 = 3364217) B3364217
theorem B15345557 : Blo 2241435 15345557 := bbase (se 6 (by rfl) ⟨359661, by rfl⟩ : syracuseStep 15345557 = 719323) (by norm_num)
theorem B10230371 : Blo 2241435 10230371 := bstep (se 1 (by rfl) ⟨7672778, by rfl⟩ : syracuseStep 10230371 = 15345557) B15345557
theorem B6820247 : Blo 2241435 6820247 := bstep (se 1 (by rfl) ⟨5115185, by rfl⟩ : syracuseStep 6820247 = 10230371) B10230371
theorem B18187325 : Blo 2241435 18187325 := bstep (se 3 (by rfl) ⟨3410123, by rfl⟩ : syracuseStep 18187325 = 6820247) B6820247
theorem B12124883 : Blo 2241435 12124883 := bstep (se 1 (by rfl) ⟨9093662, by rfl⟩ : syracuseStep 12124883 = 18187325) B18187325
theorem B8083255 : Blo 2241435 8083255 := bstep (se 1 (by rfl) ⟨6062441, by rfl⟩ : syracuseStep 8083255 = 12124883) B12124883
theorem B10777673 : Blo 2241435 10777673 := bstep (se 2 (by rfl) ⟨4041627, by rfl⟩ : syracuseStep 10777673 = 8083255) B8083255
theorem B7185115 : Blo 2241435 7185115 := bstep (se 1 (by rfl) ⟨5388836, by rfl⟩ : syracuseStep 7185115 = 10777673) B10777673
theorem B38320613 : Blo 2241435 38320613 := bstep (se 4 (by rfl) ⟨3592557, by rfl⟩ : syracuseStep 38320613 = 7185115) B7185115
theorem B25547075 : Blo 2241435 25547075 := bstep (se 1 (by rfl) ⟨19160306, by rfl⟩ : syracuseStep 25547075 = 38320613) B38320613
theorem B17031383 : Blo 2241435 17031383 := bstep (se 1 (by rfl) ⟨12773537, by rfl⟩ : syracuseStep 17031383 = 25547075) B25547075
theorem B11354255 : Blo 2241435 11354255 := bstep (se 1 (by rfl) ⟨8515691, by rfl⟩ : syracuseStep 11354255 = 17031383) B17031383
theorem B7569503 : Blo 2241435 7569503 := bstep (se 1 (by rfl) ⟨5677127, by rfl⟩ : syracuseStep 7569503 = 11354255) B11354255
theorem B5046335 : Blo 2241435 5046335 := bstep (se 1 (by rfl) ⟨3784751, by rfl⟩ : syracuseStep 5046335 = 7569503) B7569503
theorem B3364223 : Blo 2241435 3364223 := bstep (se 1 (by rfl) ⟨2523167, by rfl⟩ : syracuseStep 3364223 = 5046335) B5046335
theorem B2242815 : Blo 2241435 2242815 := bstep (se 1 (by rfl) ⟨1682111, by rfl⟩ : syracuseStep 2242815 = 3364223) B3364223
theorem B3364229 : Blo 2241435 3364229 := bbase (se 4 (by rfl) ⟨315396, by rfl⟩ : syracuseStep 3364229 = 630793) (by norm_num)
theorem B2242819 : Blo 2241435 2242819 := bstep (se 1 (by rfl) ⟨1682114, by rfl⟩ : syracuseStep 2242819 = 3364229) B3364229
theorem B3784765 : Blo 2241435 3784765 := bbase (se 3 (by rfl) ⟨709643, by rfl⟩ : syracuseStep 3784765 = 1419287) (by norm_num)
theorem B5046353 : Blo 2241435 5046353 := bstep (se 2 (by rfl) ⟨1892382, by rfl⟩ : syracuseStep 5046353 = 3784765) B3784765
theorem B3364235 : Blo 2241435 3364235 := bstep (se 1 (by rfl) ⟨2523176, by rfl⟩ : syracuseStep 3364235 = 5046353) B5046353
theorem B2242823 : Blo 2241435 2242823 := bstep (se 1 (by rfl) ⟨1682117, by rfl⟩ : syracuseStep 2242823 = 3364235) B3364235
theorem B2523181 : Blo 2241435 2523181 := bbase (se 3 (by rfl) ⟨473096, by rfl⟩ : syracuseStep 2523181 = 946193) (by norm_num)
theorem B3364241 : Blo 2241435 3364241 := bstep (se 2 (by rfl) ⟨1261590, by rfl⟩ : syracuseStep 3364241 = 2523181) B2523181
theorem B2242827 : Blo 2241435 2242827 := bstep (se 1 (by rfl) ⟨1682120, by rfl⟩ : syracuseStep 2242827 = 3364241) B3364241
theorem B7569557 : Blo 2241435 7569557 := bbase (se 6 (by rfl) ⟨177411, by rfl⟩ : syracuseStep 7569557 = 354823) (by norm_num)
theorem B5046371 : Blo 2241435 5046371 := bstep (se 1 (by rfl) ⟨3784778, by rfl⟩ : syracuseStep 5046371 = 7569557) B7569557
theorem B3364247 : Blo 2241435 3364247 := bstep (se 1 (by rfl) ⟨2523185, by rfl⟩ : syracuseStep 3364247 = 5046371) B5046371
theorem B2242831 : Blo 2241435 2242831 := bstep (se 1 (by rfl) ⟨1682123, by rfl⟩ : syracuseStep 2242831 = 3364247) B3364247
theorem B3364253 : Blo 2241435 3364253 := bbase (se 3 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 3364253 = 1261595) (by norm_num)
theorem B2242835 : Blo 2241435 2242835 := bstep (se 1 (by rfl) ⟨1682126, by rfl⟩ : syracuseStep 2242835 = 3364253) B3364253
theorem B5046389 : Blo 2241435 5046389 := bbase (se 5 (by rfl) ⟨236549, by rfl⟩ : syracuseStep 5046389 = 473099) (by norm_num)
theorem B3364259 : Blo 2241435 3364259 := bstep (se 1 (by rfl) ⟨2523194, by rfl⟩ : syracuseStep 3364259 = 5046389) B5046389
theorem B2242839 : Blo 2241435 2242839 := bstep (se 1 (by rfl) ⟨1682129, by rfl⟩ : syracuseStep 2242839 = 3364259) B3364259
theorem B2877329 : Blo 2241435 2877329 := bbase (se 2 (by rfl) ⟨1078998, by rfl⟩ : syracuseStep 2877329 = 2157997) (by norm_num)
theorem B7672877 : Blo 2241435 7672877 := bstep (se 3 (by rfl) ⟨1438664, by rfl⟩ : syracuseStep 7672877 = 2877329) B2877329
theorem B5115251 : Blo 2241435 5115251 := bstep (se 1 (by rfl) ⟨3836438, by rfl⟩ : syracuseStep 5115251 = 7672877) B7672877
theorem B13640669 : Blo 2241435 13640669 := bstep (se 3 (by rfl) ⟨2557625, by rfl⟩ : syracuseStep 13640669 = 5115251) B5115251
theorem B9093779 : Blo 2241435 9093779 := bstep (se 1 (by rfl) ⟨6820334, by rfl⟩ : syracuseStep 9093779 = 13640669) B13640669
theorem B6062519 : Blo 2241435 6062519 := bstep (se 1 (by rfl) ⟨4546889, by rfl⟩ : syracuseStep 6062519 = 9093779) B9093779
theorem B4041679 : Blo 2241435 4041679 := bstep (se 1 (by rfl) ⟨3031259, by rfl⟩ : syracuseStep 4041679 = 6062519) B6062519
theorem B5388905 : Blo 2241435 5388905 := bstep (se 2 (by rfl) ⟨2020839, by rfl⟩ : syracuseStep 5388905 = 4041679) B4041679
theorem B3592603 : Blo 2241435 3592603 := bstep (se 1 (by rfl) ⟨2694452, by rfl⟩ : syracuseStep 3592603 = 5388905) B5388905
theorem B19160549 : Blo 2241435 19160549 := bstep (se 4 (by rfl) ⟨1796301, by rfl⟩ : syracuseStep 19160549 = 3592603) B3592603
theorem B12773699 : Blo 2241435 12773699 := bstep (se 1 (by rfl) ⟨9580274, by rfl⟩ : syracuseStep 12773699 = 19160549) B19160549
theorem B8515799 : Blo 2241435 8515799 := bstep (se 1 (by rfl) ⟨6386849, by rfl⟩ : syracuseStep 8515799 = 12773699) B12773699
theorem B5677199 : Blo 2241435 5677199 := bstep (se 1 (by rfl) ⟨4257899, by rfl⟩ : syracuseStep 5677199 = 8515799) B8515799
theorem B3784799 : Blo 2241435 3784799 := bstep (se 1 (by rfl) ⟨2838599, by rfl⟩ : syracuseStep 3784799 = 5677199) B5677199
theorem B2523199 : Blo 2241435 2523199 := bstep (se 1 (by rfl) ⟨1892399, by rfl⟩ : syracuseStep 2523199 = 3784799) B3784799
theorem B3364265 : Blo 2241435 3364265 := bstep (se 2 (by rfl) ⟨1261599, by rfl⟩ : syracuseStep 3364265 = 2523199) B2523199
theorem B2242843 : Blo 2241435 2242843 := bstep (se 1 (by rfl) ⟨1682132, by rfl⟩ : syracuseStep 2242843 = 3364265) B3364265
theorem B8515813 : Blo 2241435 8515813 := bbase (se 4 (by rfl) ⟨798357, by rfl⟩ : syracuseStep 8515813 = 1596715) (by norm_num)
theorem B11354417 : Blo 2241435 11354417 := bstep (se 2 (by rfl) ⟨4257906, by rfl⟩ : syracuseStep 11354417 = 8515813) B8515813
theorem B7569611 : Blo 2241435 7569611 := bstep (se 1 (by rfl) ⟨5677208, by rfl⟩ : syracuseStep 7569611 = 11354417) B11354417
theorem B5046407 : Blo 2241435 5046407 := bstep (se 1 (by rfl) ⟨3784805, by rfl⟩ : syracuseStep 5046407 = 7569611) B7569611
theorem B3364271 : Blo 2241435 3364271 := bstep (se 1 (by rfl) ⟨2523203, by rfl⟩ : syracuseStep 3364271 = 5046407) B5046407
theorem B2242847 : Blo 2241435 2242847 := bstep (se 1 (by rfl) ⟨1682135, by rfl⟩ : syracuseStep 2242847 = 3364271) B3364271
theorem B3364277 : Blo 2241435 3364277 := bbase (se 5 (by rfl) ⟨157700, by rfl⟩ : syracuseStep 3364277 = 315401) (by norm_num)
theorem B2242851 : Blo 2241435 2242851 := bstep (se 1 (by rfl) ⟨1682138, by rfl⟩ : syracuseStep 2242851 = 3364277) B3364277
theorem B5677229 : Blo 2241435 5677229 := bbase (se 3 (by rfl) ⟨1064480, by rfl⟩ : syracuseStep 5677229 = 2128961) (by norm_num)
theorem B3784819 : Blo 2241435 3784819 := bstep (se 1 (by rfl) ⟨2838614, by rfl⟩ : syracuseStep 3784819 = 5677229) B5677229
theorem B5046425 : Blo 2241435 5046425 := bstep (se 2 (by rfl) ⟨1892409, by rfl⟩ : syracuseStep 5046425 = 3784819) B3784819
theorem B3364283 : Blo 2241435 3364283 := bstep (se 1 (by rfl) ⟨2523212, by rfl⟩ : syracuseStep 3364283 = 5046425) B5046425
theorem B2242855 : Blo 2241435 2242855 := bstep (se 1 (by rfl) ⟨1682141, by rfl⟩ : syracuseStep 2242855 = 3364283) B3364283
theorem B2523217 : Blo 2241435 2523217 := bbase (se 2 (by rfl) ⟨946206, by rfl⟩ : syracuseStep 2523217 = 1892413) (by norm_num)
theorem B3364289 : Blo 2241435 3364289 := bstep (se 2 (by rfl) ⟨1261608, by rfl⟩ : syracuseStep 3364289 = 2523217) B2523217
theorem B2242859 : Blo 2241435 2242859 := bstep (se 1 (by rfl) ⟨1682144, by rfl⟩ : syracuseStep 2242859 = 3364289) B3364289
theorem B3193453 : Blo 2241435 3193453 := bbase (se 3 (by rfl) ⟨598772, by rfl⟩ : syracuseStep 3193453 = 1197545) (by norm_num)
theorem B4257937 : Blo 2241435 4257937 := bstep (se 2 (by rfl) ⟨1596726, by rfl⟩ : syracuseStep 4257937 = 3193453) B3193453
theorem B5677249 : Blo 2241435 5677249 := bstep (se 2 (by rfl) ⟨2128968, by rfl⟩ : syracuseStep 5677249 = 4257937) B4257937
theorem B7569665 : Blo 2241435 7569665 := bstep (se 2 (by rfl) ⟨2838624, by rfl⟩ : syracuseStep 7569665 = 5677249) B5677249
theorem B5046443 : Blo 2241435 5046443 := bstep (se 1 (by rfl) ⟨3784832, by rfl⟩ : syracuseStep 5046443 = 7569665) B7569665
theorem B3364295 : Blo 2241435 3364295 := bstep (se 1 (by rfl) ⟨2523221, by rfl⟩ : syracuseStep 3364295 = 5046443) B5046443
theorem B2242863 : Blo 2241435 2242863 := bstep (se 1 (by rfl) ⟨1682147, by rfl⟩ : syracuseStep 2242863 = 3364295) B3364295
theorem B3364301 : Blo 2241435 3364301 := bbase (se 3 (by rfl) ⟨630806, by rfl⟩ : syracuseStep 3364301 = 1261613) (by norm_num)
theorem B2242867 : Blo 2241435 2242867 := bstep (se 1 (by rfl) ⟨1682150, by rfl⟩ : syracuseStep 2242867 = 3364301) B3364301
theorem B5046461 : Blo 2241435 5046461 := bbase (se 3 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 5046461 = 1892423) (by norm_num)
theorem B3364307 : Blo 2241435 3364307 := bstep (se 1 (by rfl) ⟨2523230, by rfl⟩ : syracuseStep 3364307 = 5046461) B5046461
theorem B2242871 : Blo 2241435 2242871 := bstep (se 1 (by rfl) ⟨1682153, by rfl⟩ : syracuseStep 2242871 = 3364307) B3364307
theorem B3784853 : Blo 2241435 3784853 := bbase (se 6 (by rfl) ⟨88707, by rfl⟩ : syracuseStep 3784853 = 177415) (by norm_num)
theorem B2523235 : Blo 2241435 2523235 := bstep (se 1 (by rfl) ⟨1892426, by rfl⟩ : syracuseStep 2523235 = 3784853) B3784853
theorem B3364313 : Blo 2241435 3364313 := bstep (se 2 (by rfl) ⟨1261617, by rfl⟩ : syracuseStep 3364313 = 2523235) B2523235
theorem B2242875 : Blo 2241435 2242875 := bstep (se 1 (by rfl) ⟨1682156, by rfl⟩ : syracuseStep 2242875 = 3364313) B3364313
theorem B13640885 : Blo 2241435 13640885 := bbase (se 5 (by rfl) ⟨639416, by rfl⟩ : syracuseStep 13640885 = 1278833) (by norm_num)
theorem B9093923 : Blo 2241435 9093923 := bstep (se 1 (by rfl) ⟨6820442, by rfl⟩ : syracuseStep 9093923 = 13640885) B13640885
theorem B6062615 : Blo 2241435 6062615 := bstep (se 1 (by rfl) ⟨4546961, by rfl⟩ : syracuseStep 6062615 = 9093923) B9093923
theorem B4041743 : Blo 2241435 4041743 := bstep (se 1 (by rfl) ⟨3031307, by rfl⟩ : syracuseStep 4041743 = 6062615) B6062615
theorem B10777981 : Blo 2241435 10777981 := bstep (se 3 (by rfl) ⟨2020871, by rfl⟩ : syracuseStep 10777981 = 4041743) B4041743
theorem B14370641 : Blo 2241435 14370641 := bstep (se 2 (by rfl) ⟨5388990, by rfl⟩ : syracuseStep 14370641 = 10777981) B10777981
theorem B9580427 : Blo 2241435 9580427 := bstep (se 1 (by rfl) ⟨7185320, by rfl⟩ : syracuseStep 9580427 = 14370641) B14370641
theorem B6386951 : Blo 2241435 6386951 := bstep (se 1 (by rfl) ⟨4790213, by rfl⟩ : syracuseStep 6386951 = 9580427) B9580427
theorem B17031869 : Blo 2241435 17031869 := bstep (se 3 (by rfl) ⟨3193475, by rfl⟩ : syracuseStep 17031869 = 6386951) B6386951
theorem B11354579 : Blo 2241435 11354579 := bstep (se 1 (by rfl) ⟨8515934, by rfl⟩ : syracuseStep 11354579 = 17031869) B17031869
theorem B7569719 : Blo 2241435 7569719 := bstep (se 1 (by rfl) ⟨5677289, by rfl⟩ : syracuseStep 7569719 = 11354579) B11354579
theorem B5046479 : Blo 2241435 5046479 := bstep (se 1 (by rfl) ⟨3784859, by rfl⟩ : syracuseStep 5046479 = 7569719) B7569719
theorem B3364319 : Blo 2241435 3364319 := bstep (se 1 (by rfl) ⟨2523239, by rfl⟩ : syracuseStep 3364319 = 5046479) B5046479
theorem B2242879 : Blo 2241435 2242879 := bstep (se 1 (by rfl) ⟨1682159, by rfl⟩ : syracuseStep 2242879 = 3364319) B3364319
theorem B3364325 : Blo 2241435 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B2242883 : Blo 2241435 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B2273489 : Blo 2241435 2273489 := bbase (se 2 (by rfl) ⟨852558, by rfl⟩ : syracuseStep 2273489 = 1705117) (by norm_num)
theorem B24250549 : Blo 2241435 24250549 := bstep (se 5 (by rfl) ⟨1136744, by rfl⟩ : syracuseStep 24250549 = 2273489) B2273489
theorem B32334065 : Blo 2241435 32334065 := bstep (se 2 (by rfl) ⟨12125274, by rfl⟩ : syracuseStep 32334065 = 24250549) B24250549
theorem B21556043 : Blo 2241435 21556043 := bstep (se 1 (by rfl) ⟨16167032, by rfl⟩ : syracuseStep 21556043 = 32334065) B32334065
theorem B14370695 : Blo 2241435 14370695 := bstep (se 1 (by rfl) ⟨10778021, by rfl⟩ : syracuseStep 14370695 = 21556043) B21556043
theorem B9580463 : Blo 2241435 9580463 := bstep (se 1 (by rfl) ⟨7185347, by rfl⟩ : syracuseStep 9580463 = 14370695) B14370695
theorem B6386975 : Blo 2241435 6386975 := bstep (se 1 (by rfl) ⟨4790231, by rfl⟩ : syracuseStep 6386975 = 9580463) B9580463
theorem B4257983 : Blo 2241435 4257983 := bstep (se 1 (by rfl) ⟨3193487, by rfl⟩ : syracuseStep 4257983 = 6386975) B6386975
theorem B2838655 : Blo 2241435 2838655 := bstep (se 1 (by rfl) ⟨2128991, by rfl⟩ : syracuseStep 2838655 = 4257983) B4257983
theorem B3784873 : Blo 2241435 3784873 := bstep (se 2 (by rfl) ⟨1419327, by rfl⟩ : syracuseStep 3784873 = 2838655) B2838655
theorem B5046497 : Blo 2241435 5046497 := bstep (se 2 (by rfl) ⟨1892436, by rfl⟩ : syracuseStep 5046497 = 3784873) B3784873
theorem B3364331 : Blo 2241435 3364331 := bstep (se 1 (by rfl) ⟨2523248, by rfl⟩ : syracuseStep 3364331 = 5046497) B5046497
theorem B2242887 : Blo 2241435 2242887 := bstep (se 1 (by rfl) ⟨1682165, by rfl⟩ : syracuseStep 2242887 = 3364331) B3364331
theorem B2523253 : Blo 2241435 2523253 := bbase (se 5 (by rfl) ⟨118277, by rfl⟩ : syracuseStep 2523253 = 236555) (by norm_num)
theorem B3364337 : Blo 2241435 3364337 := bstep (se 2 (by rfl) ⟨1261626, by rfl⟩ : syracuseStep 3364337 = 2523253) B2523253
theorem B2242891 : Blo 2241435 2242891 := bstep (se 1 (by rfl) ⟨1682168, by rfl⟩ : syracuseStep 2242891 = 3364337) B3364337
theorem B2838665 : Blo 2241435 2838665 := bbase (se 2 (by rfl) ⟨1064499, by rfl⟩ : syracuseStep 2838665 = 2128999) (by norm_num)
theorem B7569773 : Blo 2241435 7569773 := bstep (se 3 (by rfl) ⟨1419332, by rfl⟩ : syracuseStep 7569773 = 2838665) B2838665
theorem B5046515 : Blo 2241435 5046515 := bstep (se 1 (by rfl) ⟨3784886, by rfl⟩ : syracuseStep 5046515 = 7569773) B7569773
theorem B3364343 : Blo 2241435 3364343 := bstep (se 1 (by rfl) ⟨2523257, by rfl⟩ : syracuseStep 3364343 = 5046515) B5046515
theorem B2242895 : Blo 2241435 2242895 := bstep (se 1 (by rfl) ⟨1682171, by rfl⟩ : syracuseStep 2242895 = 3364343) B3364343
theorem B3364349 : Blo 2241435 3364349 := bbase (se 3 (by rfl) ⟨630815, by rfl⟩ : syracuseStep 3364349 = 1261631) (by norm_num)
theorem B2242899 : Blo 2241435 2242899 := bstep (se 1 (by rfl) ⟨1682174, by rfl⟩ : syracuseStep 2242899 = 3364349) B3364349
theorem B5046533 : Blo 2241435 5046533 := bbase (se 4 (by rfl) ⟨473112, by rfl⟩ : syracuseStep 5046533 = 946225) (by norm_num)
theorem B3364355 : Blo 2241435 3364355 := bstep (se 1 (by rfl) ⟨2523266, by rfl⟩ : syracuseStep 3364355 = 5046533) B5046533
theorem B2242903 : Blo 2241435 2242903 := bstep (se 1 (by rfl) ⟨1682177, by rfl⟩ : syracuseStep 2242903 = 3364355) B3364355
theorem B4258021 : Blo 2241435 4258021 := bbase (se 4 (by rfl) ⟨399189, by rfl⟩ : syracuseStep 4258021 = 798379) (by norm_num)
theorem B5677361 : Blo 2241435 5677361 := bstep (se 2 (by rfl) ⟨2129010, by rfl⟩ : syracuseStep 5677361 = 4258021) B4258021
theorem B3784907 : Blo 2241435 3784907 := bstep (se 1 (by rfl) ⟨2838680, by rfl⟩ : syracuseStep 3784907 = 5677361) B5677361
theorem B2523271 : Blo 2241435 2523271 := bstep (se 1 (by rfl) ⟨1892453, by rfl⟩ : syracuseStep 2523271 = 3784907) B3784907
theorem B3364361 : Blo 2241435 3364361 := bstep (se 2 (by rfl) ⟨1261635, by rfl⟩ : syracuseStep 3364361 = 2523271) B2523271
theorem B2242907 : Blo 2241435 2242907 := bstep (se 1 (by rfl) ⟨1682180, by rfl⟩ : syracuseStep 2242907 = 3364361) B3364361
theorem B11354741 : Blo 2241435 11354741 := bbase (se 5 (by rfl) ⟨532253, by rfl⟩ : syracuseStep 11354741 = 1064507) (by norm_num)
theorem B7569827 : Blo 2241435 7569827 := bstep (se 1 (by rfl) ⟨5677370, by rfl⟩ : syracuseStep 7569827 = 11354741) B11354741
theorem B5046551 : Blo 2241435 5046551 := bstep (se 1 (by rfl) ⟨3784913, by rfl⟩ : syracuseStep 5046551 = 7569827) B7569827
theorem B3364367 : Blo 2241435 3364367 := bstep (se 1 (by rfl) ⟨2523275, by rfl⟩ : syracuseStep 3364367 = 5046551) B5046551
theorem B2242911 : Blo 2241435 2242911 := bstep (se 1 (by rfl) ⟨1682183, by rfl⟩ : syracuseStep 2242911 = 3364367) B3364367
theorem B3364373 : Blo 2241435 3364373 := bbase (se 6 (by rfl) ⟨78852, by rfl⟩ : syracuseStep 3364373 = 157705) (by norm_num)
theorem B2242915 : Blo 2241435 2242915 := bstep (se 1 (by rfl) ⟨1682186, by rfl⟩ : syracuseStep 2242915 = 3364373) B3364373
theorem B6913621 : Blo 2241435 6913621 := bbase (se 8 (by rfl) ⟨40509, by rfl⟩ : syracuseStep 6913621 = 81019) (by norm_num)
theorem B9218161 : Blo 2241435 9218161 := bstep (se 2 (by rfl) ⟨3456810, by rfl⟩ : syracuseStep 9218161 = 6913621) B6913621
theorem B12290881 : Blo 2241435 12290881 := bstep (se 2 (by rfl) ⟨4609080, by rfl⟩ : syracuseStep 12290881 = 9218161) B9218161
theorem B16387841 : Blo 2241435 16387841 := bstep (se 2 (by rfl) ⟨6145440, by rfl⟩ : syracuseStep 16387841 = 12290881) B12290881
theorem B10925227 : Blo 2241435 10925227 := bstep (se 1 (by rfl) ⟨8193920, by rfl⟩ : syracuseStep 10925227 = 16387841) B16387841
theorem B14566969 : Blo 2241435 14566969 := bstep (se 2 (by rfl) ⟨5462613, by rfl⟩ : syracuseStep 14566969 = 10925227) B10925227
theorem B19422625 : Blo 2241435 19422625 := bstep (se 2 (by rfl) ⟨7283484, by rfl⟩ : syracuseStep 19422625 = 14566969) B14566969
theorem B25896833 : Blo 2241435 25896833 := bstep (se 2 (by rfl) ⟨9711312, by rfl⟩ : syracuseStep 25896833 = 19422625) B19422625
theorem B17264555 : Blo 2241435 17264555 := bstep (se 1 (by rfl) ⟨12948416, by rfl⟩ : syracuseStep 17264555 = 25896833) B25896833
theorem B11509703 : Blo 2241435 11509703 := bstep (se 1 (by rfl) ⟨8632277, by rfl⟩ : syracuseStep 11509703 = 17264555) B17264555
theorem B7673135 : Blo 2241435 7673135 := bstep (se 1 (by rfl) ⟨5754851, by rfl⟩ : syracuseStep 7673135 = 11509703) B11509703
theorem B20461693 : Blo 2241435 20461693 := bstep (se 3 (by rfl) ⟨3836567, by rfl⟩ : syracuseStep 20461693 = 7673135) B7673135
theorem B27282257 : Blo 2241435 27282257 := bstep (se 2 (by rfl) ⟨10230846, by rfl⟩ : syracuseStep 27282257 = 20461693) B20461693
theorem B18188171 : Blo 2241435 18188171 := bstep (se 1 (by rfl) ⟨13641128, by rfl⟩ : syracuseStep 18188171 = 27282257) B27282257
theorem B12125447 : Blo 2241435 12125447 := bstep (se 1 (by rfl) ⟨9094085, by rfl⟩ : syracuseStep 12125447 = 18188171) B18188171
theorem B8083631 : Blo 2241435 8083631 := bstep (se 1 (by rfl) ⟨6062723, by rfl⟩ : syracuseStep 8083631 = 12125447) B12125447
theorem B5389087 : Blo 2241435 5389087 := bstep (se 1 (by rfl) ⟨4041815, by rfl⟩ : syracuseStep 5389087 = 8083631) B8083631
theorem B7185449 : Blo 2241435 7185449 := bstep (se 2 (by rfl) ⟨2694543, by rfl⟩ : syracuseStep 7185449 = 5389087) B5389087
theorem B19161197 : Blo 2241435 19161197 := bstep (se 3 (by rfl) ⟨3592724, by rfl⟩ : syracuseStep 19161197 = 7185449) B7185449
theorem B12774131 : Blo 2241435 12774131 := bstep (se 1 (by rfl) ⟨9580598, by rfl⟩ : syracuseStep 12774131 = 19161197) B19161197
theorem B8516087 : Blo 2241435 8516087 := bstep (se 1 (by rfl) ⟨6387065, by rfl⟩ : syracuseStep 8516087 = 12774131) B12774131
theorem B5677391 : Blo 2241435 5677391 := bstep (se 1 (by rfl) ⟨4258043, by rfl⟩ : syracuseStep 5677391 = 8516087) B8516087
theorem B3784927 : Blo 2241435 3784927 := bstep (se 1 (by rfl) ⟨2838695, by rfl⟩ : syracuseStep 3784927 = 5677391) B5677391
theorem B5046569 : Blo 2241435 5046569 := bstep (se 2 (by rfl) ⟨1892463, by rfl⟩ : syracuseStep 5046569 = 3784927) B3784927
theorem B3364379 : Blo 2241435 3364379 := bstep (se 1 (by rfl) ⟨2523284, by rfl⟩ : syracuseStep 3364379 = 5046569) B5046569
theorem B2242919 : Blo 2241435 2242919 := bstep (se 1 (by rfl) ⟨1682189, by rfl⟩ : syracuseStep 2242919 = 3364379) B3364379
theorem B2523289 : Blo 2241435 2523289 := bbase (se 2 (by rfl) ⟨946233, by rfl⟩ : syracuseStep 2523289 = 1892467) (by norm_num)
theorem B3364385 : Blo 2241435 3364385 := bstep (se 2 (by rfl) ⟨1261644, by rfl⟩ : syracuseStep 3364385 = 2523289) B2523289
theorem B2242923 : Blo 2241435 2242923 := bstep (se 1 (by rfl) ⟨1682192, by rfl⟩ : syracuseStep 2242923 = 3364385) B3364385
theorem B8516117 : Blo 2241435 8516117 := bbase (se 6 (by rfl) ⟨199596, by rfl⟩ : syracuseStep 8516117 = 399193) (by norm_num)
theorem B5677411 : Blo 2241435 5677411 := bstep (se 1 (by rfl) ⟨4258058, by rfl⟩ : syracuseStep 5677411 = 8516117) B8516117
theorem B7569881 : Blo 2241435 7569881 := bstep (se 2 (by rfl) ⟨2838705, by rfl⟩ : syracuseStep 7569881 = 5677411) B5677411
theorem B5046587 : Blo 2241435 5046587 := bstep (se 1 (by rfl) ⟨3784940, by rfl⟩ : syracuseStep 5046587 = 7569881) B7569881
theorem B3364391 : Blo 2241435 3364391 := bstep (se 1 (by rfl) ⟨2523293, by rfl⟩ : syracuseStep 3364391 = 5046587) B5046587
theorem B2242927 : Blo 2241435 2242927 := bstep (se 1 (by rfl) ⟨1682195, by rfl⟩ : syracuseStep 2242927 = 3364391) B3364391
theorem B3364397 : Blo 2241435 3364397 := bbase (se 3 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 3364397 = 1261649) (by norm_num)
theorem B2242931 : Blo 2241435 2242931 := bstep (se 1 (by rfl) ⟨1682198, by rfl⟩ : syracuseStep 2242931 = 3364397) B3364397
theorem B5046605 : Blo 2241435 5046605 := bbase (se 3 (by rfl) ⟨946238, by rfl⟩ : syracuseStep 5046605 = 1892477) (by norm_num)
theorem B3364403 : Blo 2241435 3364403 := bstep (se 1 (by rfl) ⟨2523302, by rfl⟩ : syracuseStep 3364403 = 5046605) B5046605
theorem B2242935 : Blo 2241435 2242935 := bstep (se 1 (by rfl) ⟨1682201, by rfl⟩ : syracuseStep 2242935 = 3364403) B3364403
theorem B2838721 : Blo 2241435 2838721 := bbase (se 2 (by rfl) ⟨1064520, by rfl⟩ : syracuseStep 2838721 = 2129041) (by norm_num)
theorem B3784961 : Blo 2241435 3784961 := bstep (se 2 (by rfl) ⟨1419360, by rfl⟩ : syracuseStep 3784961 = 2838721) B2838721
theorem B2523307 : Blo 2241435 2523307 := bstep (se 1 (by rfl) ⟨1892480, by rfl⟩ : syracuseStep 2523307 = 3784961) B3784961
theorem B3364409 : Blo 2241435 3364409 := bstep (se 2 (by rfl) ⟨1261653, by rfl⟩ : syracuseStep 3364409 = 2523307) B2523307
theorem B2242939 : Blo 2241435 2242939 := bstep (se 1 (by rfl) ⟨1682204, by rfl⟩ : syracuseStep 2242939 = 3364409) B3364409
theorem B6062789 : Blo 2241435 6062789 := bbase (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) (by norm_num)
theorem B4041859 : Blo 2241435 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B5389145 : Blo 2241435 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B3592763 : Blo 2241435 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B2395175 : Blo 2241435 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B25548533 : Blo 2241435 25548533 := bstep (se 5 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 25548533 = 2395175) B2395175
theorem B17032355 : Blo 2241435 17032355 := bstep (se 1 (by rfl) ⟨12774266, by rfl⟩ : syracuseStep 17032355 = 25548533) B25548533
theorem B11354903 : Blo 2241435 11354903 := bstep (se 1 (by rfl) ⟨8516177, by rfl⟩ : syracuseStep 11354903 = 17032355) B17032355
theorem B7569935 : Blo 2241435 7569935 := bstep (se 1 (by rfl) ⟨5677451, by rfl⟩ : syracuseStep 7569935 = 11354903) B11354903
theorem B5046623 : Blo 2241435 5046623 := bstep (se 1 (by rfl) ⟨3784967, by rfl⟩ : syracuseStep 5046623 = 7569935) B7569935
theorem B3364415 : Blo 2241435 3364415 := bstep (se 1 (by rfl) ⟨2523311, by rfl⟩ : syracuseStep 3364415 = 5046623) B5046623
theorem B2242943 : Blo 2241435 2242943 := bstep (se 1 (by rfl) ⟨1682207, by rfl⟩ : syracuseStep 2242943 = 3364415) B3364415
theorem B3364421 : Blo 2241435 3364421 := bbase (se 4 (by rfl) ⟨315414, by rfl⟩ : syracuseStep 3364421 = 630829) (by norm_num)
theorem B2242947 : Blo 2241435 2242947 := bstep (se 1 (by rfl) ⟨1682210, by rfl⟩ : syracuseStep 2242947 = 3364421) B3364421
theorem B3784981 : Blo 2241435 3784981 := bbase (se 6 (by rfl) ⟨88710, by rfl⟩ : syracuseStep 3784981 = 177421) (by norm_num)
theorem B5046641 : Blo 2241435 5046641 := bstep (se 2 (by rfl) ⟨1892490, by rfl⟩ : syracuseStep 5046641 = 3784981) B3784981
theorem B3364427 : Blo 2241435 3364427 := bstep (se 1 (by rfl) ⟨2523320, by rfl⟩ : syracuseStep 3364427 = 5046641) B5046641
theorem B2242951 : Blo 2241435 2242951 := bstep (se 1 (by rfl) ⟨1682213, by rfl⟩ : syracuseStep 2242951 = 3364427) B3364427
theorem B2523325 : Blo 2241435 2523325 := bbase (se 3 (by rfl) ⟨473123, by rfl⟩ : syracuseStep 2523325 = 946247) (by norm_num)
theorem B3364433 : Blo 2241435 3364433 := bstep (se 2 (by rfl) ⟨1261662, by rfl⟩ : syracuseStep 3364433 = 2523325) B2523325
theorem B2242955 : Blo 2241435 2242955 := bstep (se 1 (by rfl) ⟨1682216, by rfl⟩ : syracuseStep 2242955 = 3364433) B3364433
theorem B7569989 : Blo 2241435 7569989 := bbase (se 4 (by rfl) ⟨709686, by rfl⟩ : syracuseStep 7569989 = 1419373) (by norm_num)
theorem B5046659 : Blo 2241435 5046659 := bstep (se 1 (by rfl) ⟨3784994, by rfl⟩ : syracuseStep 5046659 = 7569989) B7569989
theorem B3364439 : Blo 2241435 3364439 := bstep (se 1 (by rfl) ⟨2523329, by rfl⟩ : syracuseStep 3364439 = 5046659) B5046659
theorem B2242959 : Blo 2241435 2242959 := bstep (se 1 (by rfl) ⟨1682219, by rfl⟩ : syracuseStep 2242959 = 3364439) B3364439
theorem B3364445 : Blo 2241435 3364445 := bbase (se 3 (by rfl) ⟨630833, by rfl⟩ : syracuseStep 3364445 = 1261667) (by norm_num)
theorem B2242963 : Blo 2241435 2242963 := bstep (se 1 (by rfl) ⟨1682222, by rfl⟩ : syracuseStep 2242963 = 3364445) B3364445
theorem B5046677 : Blo 2241435 5046677 := bbase (se 6 (by rfl) ⟨118281, by rfl⟩ : syracuseStep 5046677 = 236563) (by norm_num)
theorem B3364451 : Blo 2241435 3364451 := bstep (se 1 (by rfl) ⟨2523338, by rfl⟩ : syracuseStep 3364451 = 5046677) B5046677
theorem B2242967 : Blo 2241435 2242967 := bstep (se 1 (by rfl) ⟨1682225, by rfl⟩ : syracuseStep 2242967 = 3364451) B3364451
theorem B5389213 : Blo 2241435 5389213 := bbase (se 3 (by rfl) ⟨1010477, by rfl⟩ : syracuseStep 5389213 = 2020955) (by norm_num)
theorem B7185617 : Blo 2241435 7185617 := bstep (se 2 (by rfl) ⟨2694606, by rfl⟩ : syracuseStep 7185617 = 5389213) B5389213
theorem B4790411 : Blo 2241435 4790411 := bstep (se 1 (by rfl) ⟨3592808, by rfl⟩ : syracuseStep 4790411 = 7185617) B7185617
theorem B3193607 : Blo 2241435 3193607 := bstep (se 1 (by rfl) ⟨2395205, by rfl⟩ : syracuseStep 3193607 = 4790411) B4790411
theorem B8516285 : Blo 2241435 8516285 := bstep (se 3 (by rfl) ⟨1596803, by rfl⟩ : syracuseStep 8516285 = 3193607) B3193607
theorem B5677523 : Blo 2241435 5677523 := bstep (se 1 (by rfl) ⟨4258142, by rfl⟩ : syracuseStep 5677523 = 8516285) B8516285
theorem B3785015 : Blo 2241435 3785015 := bstep (se 1 (by rfl) ⟨2838761, by rfl⟩ : syracuseStep 3785015 = 5677523) B5677523
theorem B2523343 : Blo 2241435 2523343 := bstep (se 1 (by rfl) ⟨1892507, by rfl⟩ : syracuseStep 2523343 = 3785015) B3785015
theorem B3364457 : Blo 2241435 3364457 := bstep (se 2 (by rfl) ⟨1261671, by rfl⟩ : syracuseStep 3364457 = 2523343) B2523343
theorem B2242971 : Blo 2241435 2242971 := bstep (se 1 (by rfl) ⟨1682228, by rfl⟩ : syracuseStep 2242971 = 3364457) B3364457
theorem B9580837 : Blo 2241435 9580837 := bbase (se 4 (by rfl) ⟨898203, by rfl⟩ : syracuseStep 9580837 = 1796407) (by norm_num)
theorem B12774449 : Blo 2241435 12774449 := bstep (se 2 (by rfl) ⟨4790418, by rfl⟩ : syracuseStep 12774449 = 9580837) B9580837
theorem B8516299 : Blo 2241435 8516299 := bstep (se 1 (by rfl) ⟨6387224, by rfl⟩ : syracuseStep 8516299 = 12774449) B12774449
theorem B11355065 : Blo 2241435 11355065 := bstep (se 2 (by rfl) ⟨4258149, by rfl⟩ : syracuseStep 11355065 = 8516299) B8516299
theorem B7570043 : Blo 2241435 7570043 := bstep (se 1 (by rfl) ⟨5677532, by rfl⟩ : syracuseStep 7570043 = 11355065) B11355065
theorem B5046695 : Blo 2241435 5046695 := bstep (se 1 (by rfl) ⟨3785021, by rfl⟩ : syracuseStep 5046695 = 7570043) B7570043
theorem B3364463 : Blo 2241435 3364463 := bstep (se 1 (by rfl) ⟨2523347, by rfl⟩ : syracuseStep 3364463 = 5046695) B5046695
theorem B2242975 : Blo 2241435 2242975 := bstep (se 1 (by rfl) ⟨1682231, by rfl⟩ : syracuseStep 2242975 = 3364463) B3364463
theorem B3364469 : Blo 2241435 3364469 := bbase (se 5 (by rfl) ⟨157709, by rfl⟩ : syracuseStep 3364469 = 315419) (by norm_num)
theorem B2242979 : Blo 2241435 2242979 := bstep (se 1 (by rfl) ⟨1682234, by rfl⟩ : syracuseStep 2242979 = 3364469) B3364469
theorem B4258165 : Blo 2241435 4258165 := bbase (se 5 (by rfl) ⟨199601, by rfl⟩ : syracuseStep 4258165 = 399203) (by norm_num)
theorem B5677553 : Blo 2241435 5677553 := bstep (se 2 (by rfl) ⟨2129082, by rfl⟩ : syracuseStep 5677553 = 4258165) B4258165
theorem B3785035 : Blo 2241435 3785035 := bstep (se 1 (by rfl) ⟨2838776, by rfl⟩ : syracuseStep 3785035 = 5677553) B5677553
theorem B5046713 : Blo 2241435 5046713 := bstep (se 2 (by rfl) ⟨1892517, by rfl⟩ : syracuseStep 5046713 = 3785035) B3785035
theorem B3364475 : Blo 2241435 3364475 := bstep (se 1 (by rfl) ⟨2523356, by rfl⟩ : syracuseStep 3364475 = 5046713) B5046713
theorem B2242983 : Blo 2241435 2242983 := bstep (se 1 (by rfl) ⟨1682237, by rfl⟩ : syracuseStep 2242983 = 3364475) B3364475
theorem B2523361 : Blo 2241435 2523361 := bbase (se 2 (by rfl) ⟨946260, by rfl⟩ : syracuseStep 2523361 = 1892521) (by norm_num)
theorem B3364481 : Blo 2241435 3364481 := bstep (se 2 (by rfl) ⟨1261680, by rfl⟩ : syracuseStep 3364481 = 2523361) B2523361
theorem B2242987 : Blo 2241435 2242987 := bstep (se 1 (by rfl) ⟨1682240, by rfl⟩ : syracuseStep 2242987 = 3364481) B3364481
theorem B5677573 : Blo 2241435 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B7570097 : Blo 2241435 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B5046731 : Blo 2241435 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B3364487 : Blo 2241435 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B2242991 : Blo 2241435 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B3364493 : Blo 2241435 3364493 := bbase (se 3 (by rfl) ⟨630842, by rfl⟩ : syracuseStep 3364493 = 1261685) (by norm_num)
theorem B2242995 : Blo 2241435 2242995 := bstep (se 1 (by rfl) ⟨1682246, by rfl⟩ : syracuseStep 2242995 = 3364493) B3364493
theorem B5046749 : Blo 2241435 5046749 := bbase (se 3 (by rfl) ⟨946265, by rfl⟩ : syracuseStep 5046749 = 1892531) (by norm_num)
theorem B3364499 : Blo 2241435 3364499 := bstep (se 1 (by rfl) ⟨2523374, by rfl⟩ : syracuseStep 3364499 = 5046749) B5046749
theorem B2242999 : Blo 2241435 2242999 := bstep (se 1 (by rfl) ⟨1682249, by rfl⟩ : syracuseStep 2242999 = 3364499) B3364499
theorem B3785069 : Blo 2241435 3785069 := bbase (se 3 (by rfl) ⟨709700, by rfl⟩ : syracuseStep 3785069 = 1419401) (by norm_num)
theorem B2523379 : Blo 2241435 2523379 := bstep (se 1 (by rfl) ⟨1892534, by rfl⟩ : syracuseStep 2523379 = 3785069) B3785069
theorem B3364505 : Blo 2241435 3364505 := bstep (se 2 (by rfl) ⟨1261689, by rfl⟩ : syracuseStep 3364505 = 2523379) B2523379
theorem B2243003 : Blo 2241435 2243003 := bstep (se 1 (by rfl) ⟨1682252, by rfl⟩ : syracuseStep 2243003 = 3364505) B3364505
theorem B77693525 : Blo 2241435 77693525 := bbase (se 8 (by rfl) ⟨455235, by rfl⟩ : syracuseStep 77693525 = 910471) (by norm_num)
theorem B51795683 : Blo 2241435 51795683 := bstep (se 1 (by rfl) ⟨38846762, by rfl⟩ : syracuseStep 51795683 = 77693525) B77693525
theorem B34530455 : Blo 2241435 34530455 := bstep (se 1 (by rfl) ⟨25897841, by rfl⟩ : syracuseStep 34530455 = 51795683) B51795683
theorem B23020303 : Blo 2241435 23020303 := bstep (se 1 (by rfl) ⟨17265227, by rfl⟩ : syracuseStep 23020303 = 34530455) B34530455
theorem B30693737 : Blo 2241435 30693737 := bstep (se 2 (by rfl) ⟨11510151, by rfl⟩ : syracuseStep 30693737 = 23020303) B23020303
theorem B20462491 : Blo 2241435 20462491 := bstep (se 1 (by rfl) ⟨15346868, by rfl⟩ : syracuseStep 20462491 = 30693737) B30693737
theorem B27283321 : Blo 2241435 27283321 := bstep (se 2 (by rfl) ⟨10231245, by rfl⟩ : syracuseStep 27283321 = 20462491) B20462491
theorem B36377761 : Blo 2241435 36377761 := bstep (se 2 (by rfl) ⟨13641660, by rfl⟩ : syracuseStep 36377761 = 27283321) B27283321
theorem B48503681 : Blo 2241435 48503681 := bstep (se 2 (by rfl) ⟨18188880, by rfl⟩ : syracuseStep 48503681 = 36377761) B36377761
theorem B32335787 : Blo 2241435 32335787 := bstep (se 1 (by rfl) ⟨24251840, by rfl⟩ : syracuseStep 32335787 = 48503681) B48503681
theorem B21557191 : Blo 2241435 21557191 := bstep (se 1 (by rfl) ⟨16167893, by rfl⟩ : syracuseStep 21557191 = 32335787) B32335787
theorem B28742921 : Blo 2241435 28742921 := bstep (se 2 (by rfl) ⟨10778595, by rfl⟩ : syracuseStep 28742921 = 21557191) B21557191
theorem B19161947 : Blo 2241435 19161947 := bstep (se 1 (by rfl) ⟨14371460, by rfl⟩ : syracuseStep 19161947 = 28742921) B28742921
theorem B12774631 : Blo 2241435 12774631 := bstep (se 1 (by rfl) ⟨9580973, by rfl⟩ : syracuseStep 12774631 = 19161947) B19161947
theorem B17032841 : Blo 2241435 17032841 := bstep (se 2 (by rfl) ⟨6387315, by rfl⟩ : syracuseStep 17032841 = 12774631) B12774631
theorem B11355227 : Blo 2241435 11355227 := bstep (se 1 (by rfl) ⟨8516420, by rfl⟩ : syracuseStep 11355227 = 17032841) B17032841
theorem B7570151 : Blo 2241435 7570151 := bstep (se 1 (by rfl) ⟨5677613, by rfl⟩ : syracuseStep 7570151 = 11355227) B11355227
theorem B5046767 : Blo 2241435 5046767 := bstep (se 1 (by rfl) ⟨3785075, by rfl⟩ : syracuseStep 5046767 = 7570151) B7570151
theorem B3364511 : Blo 2241435 3364511 := bstep (se 1 (by rfl) ⟨2523383, by rfl⟩ : syracuseStep 3364511 = 5046767) B5046767
theorem B2243007 : Blo 2241435 2243007 := bstep (se 1 (by rfl) ⟨1682255, by rfl⟩ : syracuseStep 2243007 = 3364511) B3364511
theorem B3364517 : Blo 2241435 3364517 := bbase (se 4 (by rfl) ⟨315423, by rfl⟩ : syracuseStep 3364517 = 630847) (by norm_num)
theorem B2243011 : Blo 2241435 2243011 := bstep (se 1 (by rfl) ⟨1682258, by rfl⟩ : syracuseStep 2243011 = 3364517) B3364517
theorem B2838817 : Blo 2241435 2838817 := bbase (se 2 (by rfl) ⟨1064556, by rfl⟩ : syracuseStep 2838817 = 2129113) (by norm_num)
theorem B3785089 : Blo 2241435 3785089 := bstep (se 2 (by rfl) ⟨1419408, by rfl⟩ : syracuseStep 3785089 = 2838817) B2838817
theorem B5046785 : Blo 2241435 5046785 := bstep (se 2 (by rfl) ⟨1892544, by rfl⟩ : syracuseStep 5046785 = 3785089) B3785089
theorem B3364523 : Blo 2241435 3364523 := bstep (se 1 (by rfl) ⟨2523392, by rfl⟩ : syracuseStep 3364523 = 5046785) B5046785
theorem B2243015 : Blo 2241435 2243015 := bstep (se 1 (by rfl) ⟨1682261, by rfl⟩ : syracuseStep 2243015 = 3364523) B3364523
theorem B2523397 : Blo 2241435 2523397 := bbase (se 4 (by rfl) ⟨236568, by rfl⟩ : syracuseStep 2523397 = 473137) (by norm_num)
theorem B3364529 : Blo 2241435 3364529 := bstep (se 2 (by rfl) ⟨1261698, by rfl⟩ : syracuseStep 3364529 = 2523397) B2523397
theorem B2243019 : Blo 2241435 2243019 := bstep (se 1 (by rfl) ⟨1682264, by rfl⟩ : syracuseStep 2243019 = 3364529) B3364529
theorem B2395261 : Blo 2241435 2395261 := bbase (se 3 (by rfl) ⟨449111, by rfl⟩ : syracuseStep 2395261 = 898223) (by norm_num)
theorem B3193681 : Blo 2241435 3193681 := bstep (se 2 (by rfl) ⟨1197630, by rfl⟩ : syracuseStep 3193681 = 2395261) B2395261
theorem B4258241 : Blo 2241435 4258241 := bstep (se 2 (by rfl) ⟨1596840, by rfl⟩ : syracuseStep 4258241 = 3193681) B3193681
theorem B2838827 : Blo 2241435 2838827 := bstep (se 1 (by rfl) ⟨2129120, by rfl⟩ : syracuseStep 2838827 = 4258241) B4258241
theorem B7570205 : Blo 2241435 7570205 := bstep (se 3 (by rfl) ⟨1419413, by rfl⟩ : syracuseStep 7570205 = 2838827) B2838827
theorem B5046803 : Blo 2241435 5046803 := bstep (se 1 (by rfl) ⟨3785102, by rfl⟩ : syracuseStep 5046803 = 7570205) B7570205
theorem B3364535 : Blo 2241435 3364535 := bstep (se 1 (by rfl) ⟨2523401, by rfl⟩ : syracuseStep 3364535 = 5046803) B5046803
theorem B2243023 : Blo 2241435 2243023 := bstep (se 1 (by rfl) ⟨1682267, by rfl⟩ : syracuseStep 2243023 = 3364535) B3364535
theorem B3364541 : Blo 2241435 3364541 := bbase (se 3 (by rfl) ⟨630851, by rfl⟩ : syracuseStep 3364541 = 1261703) (by norm_num)
theorem B2243027 : Blo 2241435 2243027 := bstep (se 1 (by rfl) ⟨1682270, by rfl⟩ : syracuseStep 2243027 = 3364541) B3364541
theorem B5046821 : Blo 2241435 5046821 := bbase (se 4 (by rfl) ⟨473139, by rfl⟩ : syracuseStep 5046821 = 946279) (by norm_num)
theorem B3364547 : Blo 2241435 3364547 := bstep (se 1 (by rfl) ⟨2523410, by rfl⟩ : syracuseStep 3364547 = 5046821) B5046821
theorem B2243031 : Blo 2241435 2243031 := bstep (se 1 (by rfl) ⟨1682273, by rfl⟩ : syracuseStep 2243031 = 3364547) B3364547
theorem B5677685 : Blo 2241435 5677685 := bbase (se 5 (by rfl) ⟨266141, by rfl⟩ : syracuseStep 5677685 = 532283) (by norm_num)
theorem B3785123 : Blo 2241435 3785123 := bstep (se 1 (by rfl) ⟨2838842, by rfl⟩ : syracuseStep 3785123 = 5677685) B5677685
theorem B2523415 : Blo 2241435 2523415 := bstep (se 1 (by rfl) ⟨1892561, by rfl⟩ : syracuseStep 2523415 = 3785123) B3785123
theorem B3364553 : Blo 2241435 3364553 := bstep (se 2 (by rfl) ⟨1261707, by rfl⟩ : syracuseStep 3364553 = 2523415) B2523415
theorem B2243035 : Blo 2241435 2243035 := bstep (se 1 (by rfl) ⟨1682276, by rfl⟩ : syracuseStep 2243035 = 3364553) B3364553
theorem B12949109 : Blo 2241435 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B8632739 : Blo 2241435 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B5755159 : Blo 2241435 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B7673545 : Blo 2241435 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B40925573 : Blo 2241435 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B27283715 : Blo 2241435 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B18189143 : Blo 2241435 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B12126095 : Blo 2241435 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B8084063 : Blo 2241435 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B21557501 : Blo 2241435 21557501 := bstep (se 3 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 21557501 = 8084063) B8084063
theorem B14371667 : Blo 2241435 14371667 := bstep (se 1 (by rfl) ⟨10778750, by rfl⟩ : syracuseStep 14371667 = 21557501) B21557501
theorem B9581111 : Blo 2241435 9581111 := bstep (se 1 (by rfl) ⟨7185833, by rfl⟩ : syracuseStep 9581111 = 14371667) B14371667
theorem B6387407 : Blo 2241435 6387407 := bstep (se 1 (by rfl) ⟨4790555, by rfl⟩ : syracuseStep 6387407 = 9581111) B9581111
theorem B4258271 : Blo 2241435 4258271 := bstep (se 1 (by rfl) ⟨3193703, by rfl⟩ : syracuseStep 4258271 = 6387407) B6387407
theorem B11355389 : Blo 2241435 11355389 := bstep (se 3 (by rfl) ⟨2129135, by rfl⟩ : syracuseStep 11355389 = 4258271) B4258271
theorem B7570259 : Blo 2241435 7570259 := bstep (se 1 (by rfl) ⟨5677694, by rfl⟩ : syracuseStep 7570259 = 11355389) B11355389
theorem B5046839 : Blo 2241435 5046839 := bstep (se 1 (by rfl) ⟨3785129, by rfl⟩ : syracuseStep 5046839 = 7570259) B7570259
theorem B3364559 : Blo 2241435 3364559 := bstep (se 1 (by rfl) ⟨2523419, by rfl⟩ : syracuseStep 3364559 = 5046839) B5046839
theorem B2243039 : Blo 2241435 2243039 := bstep (se 1 (by rfl) ⟨1682279, by rfl⟩ : syracuseStep 2243039 = 3364559) B3364559
theorem B3364565 : Blo 2241435 3364565 := bbase (se 7 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 3364565 = 78857) (by norm_num)
theorem B2243043 : Blo 2241435 2243043 := bstep (se 1 (by rfl) ⟨1682282, by rfl⟩ : syracuseStep 2243043 = 3364565) B3364565
theorem B4790573 : Blo 2241435 4790573 := bbase (se 3 (by rfl) ⟨898232, by rfl⟩ : syracuseStep 4790573 = 1796465) (by norm_num)
theorem B3193715 : Blo 2241435 3193715 := bstep (se 1 (by rfl) ⟨2395286, by rfl⟩ : syracuseStep 3193715 = 4790573) B4790573
theorem B8516573 : Blo 2241435 8516573 := bstep (se 3 (by rfl) ⟨1596857, by rfl⟩ : syracuseStep 8516573 = 3193715) B3193715
theorem B5677715 : Blo 2241435 5677715 := bstep (se 1 (by rfl) ⟨4258286, by rfl⟩ : syracuseStep 5677715 = 8516573) B8516573
theorem B3785143 : Blo 2241435 3785143 := bstep (se 1 (by rfl) ⟨2838857, by rfl⟩ : syracuseStep 3785143 = 5677715) B5677715
theorem B5046857 : Blo 2241435 5046857 := bstep (se 2 (by rfl) ⟨1892571, by rfl⟩ : syracuseStep 5046857 = 3785143) B3785143
theorem B3364571 : Blo 2241435 3364571 := bstep (se 1 (by rfl) ⟨2523428, by rfl⟩ : syracuseStep 3364571 = 5046857) B5046857
theorem B2243047 : Blo 2241435 2243047 := bstep (se 1 (by rfl) ⟨1682285, by rfl⟩ : syracuseStep 2243047 = 3364571) B3364571
theorem B2523433 : Blo 2241435 2523433 := bbase (se 2 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 2523433 = 1892575) (by norm_num)
theorem B3364577 : Blo 2241435 3364577 := bstep (se 2 (by rfl) ⟨1261716, by rfl⟩ : syracuseStep 3364577 = 2523433) B2523433
theorem B2243051 : Blo 2241435 2243051 := bstep (se 1 (by rfl) ⟨1682288, by rfl⟩ : syracuseStep 2243051 = 3364577) B3364577
theorem B2877601 : Blo 2241435 2877601 := bbase (se 2 (by rfl) ⟨1079100, by rfl⟩ : syracuseStep 2877601 = 2158201) (by norm_num)
theorem B3836801 : Blo 2241435 3836801 := bstep (se 2 (by rfl) ⟨1438800, by rfl⟩ : syracuseStep 3836801 = 2877601) B2877601
theorem B2557867 : Blo 2241435 2557867 := bstep (se 1 (by rfl) ⟨1918400, by rfl⟩ : syracuseStep 2557867 = 3836801) B3836801
theorem B3410489 : Blo 2241435 3410489 := bstep (se 2 (by rfl) ⟨1278933, by rfl⟩ : syracuseStep 3410489 = 2557867) B2557867
theorem B2273659 : Blo 2241435 2273659 := bstep (se 1 (by rfl) ⟨1705244, by rfl⟩ : syracuseStep 2273659 = 3410489) B3410489
theorem B12126181 : Blo 2241435 12126181 := bstep (se 4 (by rfl) ⟨1136829, by rfl⟩ : syracuseStep 12126181 = 2273659) B2273659
theorem B16168241 : Blo 2241435 16168241 := bstep (se 2 (by rfl) ⟨6063090, by rfl⟩ : syracuseStep 16168241 = 12126181) B12126181
theorem B10778827 : Blo 2241435 10778827 := bstep (se 1 (by rfl) ⟨8084120, by rfl⟩ : syracuseStep 10778827 = 16168241) B16168241
theorem B14371769 : Blo 2241435 14371769 := bstep (se 2 (by rfl) ⟨5389413, by rfl⟩ : syracuseStep 14371769 = 10778827) B10778827
theorem B9581179 : Blo 2241435 9581179 := bstep (se 1 (by rfl) ⟨7185884, by rfl⟩ : syracuseStep 9581179 = 14371769) B14371769
theorem B12774905 : Blo 2241435 12774905 := bstep (se 2 (by rfl) ⟨4790589, by rfl⟩ : syracuseStep 12774905 = 9581179) B9581179
theorem B8516603 : Blo 2241435 8516603 := bstep (se 1 (by rfl) ⟨6387452, by rfl⟩ : syracuseStep 8516603 = 12774905) B12774905
theorem B5677735 : Blo 2241435 5677735 := bstep (se 1 (by rfl) ⟨4258301, by rfl⟩ : syracuseStep 5677735 = 8516603) B8516603
theorem B7570313 : Blo 2241435 7570313 := bstep (se 2 (by rfl) ⟨2838867, by rfl⟩ : syracuseStep 7570313 = 5677735) B5677735
theorem B5046875 : Blo 2241435 5046875 := bstep (se 1 (by rfl) ⟨3785156, by rfl⟩ : syracuseStep 5046875 = 7570313) B7570313
theorem B3364583 : Blo 2241435 3364583 := bstep (se 1 (by rfl) ⟨2523437, by rfl⟩ : syracuseStep 3364583 = 5046875) B5046875
theorem B2243055 : Blo 2241435 2243055 := bstep (se 1 (by rfl) ⟨1682291, by rfl⟩ : syracuseStep 2243055 = 3364583) B3364583
theorem B3364589 : Blo 2241435 3364589 := bbase (se 3 (by rfl) ⟨630860, by rfl⟩ : syracuseStep 3364589 = 1261721) (by norm_num)
theorem B2243059 : Blo 2241435 2243059 := bstep (se 1 (by rfl) ⟨1682294, by rfl⟩ : syracuseStep 2243059 = 3364589) B3364589
theorem B5046893 : Blo 2241435 5046893 := bbase (se 3 (by rfl) ⟨946292, by rfl⟩ : syracuseStep 5046893 = 1892585) (by norm_num)
theorem B3364595 : Blo 2241435 3364595 := bstep (se 1 (by rfl) ⟨2523446, by rfl⟩ : syracuseStep 3364595 = 5046893) B5046893
theorem B2243063 : Blo 2241435 2243063 := bstep (se 1 (by rfl) ⟨1682297, by rfl⟩ : syracuseStep 2243063 = 3364595) B3364595
theorem B4258325 : Blo 2241435 4258325 := bbase (se 6 (by rfl) ⟨99804, by rfl⟩ : syracuseStep 4258325 = 199609) (by norm_num)
theorem B2838883 : Blo 2241435 2838883 := bstep (se 1 (by rfl) ⟨2129162, by rfl⟩ : syracuseStep 2838883 = 4258325) B4258325
theorem B3785177 : Blo 2241435 3785177 := bstep (se 2 (by rfl) ⟨1419441, by rfl⟩ : syracuseStep 3785177 = 2838883) B2838883
theorem B2523451 : Blo 2241435 2523451 := bstep (se 1 (by rfl) ⟨1892588, by rfl⟩ : syracuseStep 2523451 = 3785177) B3785177
theorem B3364601 : Blo 2241435 3364601 := bstep (se 2 (by rfl) ⟨1261725, by rfl⟩ : syracuseStep 3364601 = 2523451) B2523451
theorem B2243067 : Blo 2241435 2243067 := bstep (se 1 (by rfl) ⟨1682300, by rfl⟩ : syracuseStep 2243067 = 3364601) B3364601
theorem B4922237 : Blo 2241435 4922237 := bbase (se 3 (by rfl) ⟨922919, by rfl⟩ : syracuseStep 4922237 = 1845839) (by norm_num)
theorem B3281491 : Blo 2241435 3281491 := bstep (se 1 (by rfl) ⟨2461118, by rfl⟩ : syracuseStep 3281491 = 4922237) B4922237
theorem B17501285 : Blo 2241435 17501285 := bstep (se 4 (by rfl) ⟨1640745, by rfl⟩ : syracuseStep 17501285 = 3281491) B3281491
theorem B11667523 : Blo 2241435 11667523 := bstep (se 1 (by rfl) ⟨8750642, by rfl⟩ : syracuseStep 11667523 = 17501285) B17501285
theorem B15556697 : Blo 2241435 15556697 := bstep (se 2 (by rfl) ⟨5833761, by rfl⟩ : syracuseStep 15556697 = 11667523) B11667523
theorem B10371131 : Blo 2241435 10371131 := bstep (se 1 (by rfl) ⟨7778348, by rfl⟩ : syracuseStep 10371131 = 15556697) B15556697
theorem B6914087 : Blo 2241435 6914087 := bstep (se 1 (by rfl) ⟨5185565, by rfl⟩ : syracuseStep 6914087 = 10371131) B10371131
theorem B4609391 : Blo 2241435 4609391 := bstep (se 1 (by rfl) ⟨3457043, by rfl⟩ : syracuseStep 4609391 = 6914087) B6914087
theorem B49166837 : Blo 2241435 49166837 := bstep (se 5 (by rfl) ⟨2304695, by rfl⟩ : syracuseStep 49166837 = 4609391) B4609391
theorem B32777891 : Blo 2241435 32777891 := bstep (se 1 (by rfl) ⟨24583418, by rfl⟩ : syracuseStep 32777891 = 49166837) B49166837
theorem B21851927 : Blo 2241435 21851927 := bstep (se 1 (by rfl) ⟨16388945, by rfl⟩ : syracuseStep 21851927 = 32777891) B32777891
theorem B14567951 : Blo 2241435 14567951 := bstep (se 1 (by rfl) ⟨10925963, by rfl⟩ : syracuseStep 14567951 = 21851927) B21851927
theorem B9711967 : Blo 2241435 9711967 := bstep (se 1 (by rfl) ⟨7283975, by rfl⟩ : syracuseStep 9711967 = 14567951) B14567951
theorem B12949289 : Blo 2241435 12949289 := bstep (se 2 (by rfl) ⟨4855983, by rfl⟩ : syracuseStep 12949289 = 9711967) B9711967
theorem B138125749 : Blo 2241435 138125749 := bstep (se 5 (by rfl) ⟨6474644, by rfl⟩ : syracuseStep 138125749 = 12949289) B12949289
theorem B184167665 : Blo 2241435 184167665 := bstep (se 2 (by rfl) ⟨69062874, by rfl⟩ : syracuseStep 184167665 = 138125749) B138125749
theorem B122778443 : Blo 2241435 122778443 := bstep (se 1 (by rfl) ⟨92083832, by rfl⟩ : syracuseStep 122778443 = 184167665) B184167665
theorem B81852295 : Blo 2241435 81852295 := bstep (se 1 (by rfl) ⟨61389221, by rfl⟩ : syracuseStep 81852295 = 122778443) B122778443
theorem B109136393 : Blo 2241435 109136393 := bstep (se 2 (by rfl) ⟨40926147, by rfl⟩ : syracuseStep 109136393 = 81852295) B81852295
theorem B72757595 : Blo 2241435 72757595 := bstep (se 1 (by rfl) ⟨54568196, by rfl⟩ : syracuseStep 72757595 = 109136393) B109136393
theorem B48505063 : Blo 2241435 48505063 := bstep (se 1 (by rfl) ⟨36378797, by rfl⟩ : syracuseStep 48505063 = 72757595) B72757595
theorem B64673417 : Blo 2241435 64673417 := bstep (se 2 (by rfl) ⟨24252531, by rfl⟩ : syracuseStep 64673417 = 48505063) B48505063
theorem B43115611 : Blo 2241435 43115611 := bstep (se 1 (by rfl) ⟨32336708, by rfl⟩ : syracuseStep 43115611 = 64673417) B64673417
theorem B57487481 : Blo 2241435 57487481 := bstep (se 2 (by rfl) ⟨21557805, by rfl⟩ : syracuseStep 57487481 = 43115611) B43115611
theorem B38324987 : Blo 2241435 38324987 := bstep (se 1 (by rfl) ⟨28743740, by rfl⟩ : syracuseStep 38324987 = 57487481) B57487481
theorem B25549991 : Blo 2241435 25549991 := bstep (se 1 (by rfl) ⟨19162493, by rfl⟩ : syracuseStep 25549991 = 38324987) B38324987
theorem B17033327 : Blo 2241435 17033327 := bstep (se 1 (by rfl) ⟨12774995, by rfl⟩ : syracuseStep 17033327 = 25549991) B25549991
theorem B11355551 : Blo 2241435 11355551 := bstep (se 1 (by rfl) ⟨8516663, by rfl⟩ : syracuseStep 11355551 = 17033327) B17033327
theorem B7570367 : Blo 2241435 7570367 := bstep (se 1 (by rfl) ⟨5677775, by rfl⟩ : syracuseStep 7570367 = 11355551) B11355551
theorem B5046911 : Blo 2241435 5046911 := bstep (se 1 (by rfl) ⟨3785183, by rfl⟩ : syracuseStep 5046911 = 7570367) B7570367
theorem B3364607 : Blo 2241435 3364607 := bstep (se 1 (by rfl) ⟨2523455, by rfl⟩ : syracuseStep 3364607 = 5046911) B5046911
theorem B2243071 : Blo 2241435 2243071 := bstep (se 1 (by rfl) ⟨1682303, by rfl⟩ : syracuseStep 2243071 = 3364607) B3364607
theorem B3364613 : Blo 2241435 3364613 := bbase (se 4 (by rfl) ⟨315432, by rfl⟩ : syracuseStep 3364613 = 630865) (by norm_num)
theorem B2243075 : Blo 2241435 2243075 := bstep (se 1 (by rfl) ⟨1682306, by rfl⟩ : syracuseStep 2243075 = 3364613) B3364613
theorem B3785197 : Blo 2241435 3785197 := bbase (se 3 (by rfl) ⟨709724, by rfl⟩ : syracuseStep 3785197 = 1419449) (by norm_num)
theorem B5046929 : Blo 2241435 5046929 := bstep (se 2 (by rfl) ⟨1892598, by rfl⟩ : syracuseStep 5046929 = 3785197) B3785197
theorem B3364619 : Blo 2241435 3364619 := bstep (se 1 (by rfl) ⟨2523464, by rfl⟩ : syracuseStep 3364619 = 5046929) B5046929
theorem B2243079 : Blo 2241435 2243079 := bstep (se 1 (by rfl) ⟨1682309, by rfl⟩ : syracuseStep 2243079 = 3364619) B3364619
theorem B2523469 : Blo 2241435 2523469 := bbase (se 3 (by rfl) ⟨473150, by rfl⟩ : syracuseStep 2523469 = 946301) (by norm_num)
theorem B3364625 : Blo 2241435 3364625 := bstep (se 2 (by rfl) ⟨1261734, by rfl⟩ : syracuseStep 3364625 = 2523469) B2523469
theorem B2243083 : Blo 2241435 2243083 := bstep (se 1 (by rfl) ⟨1682312, by rfl⟩ : syracuseStep 2243083 = 3364625) B3364625
theorem B7570421 : Blo 2241435 7570421 := bbase (se 5 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 7570421 = 709727) (by norm_num)
theorem B5046947 : Blo 2241435 5046947 := bstep (se 1 (by rfl) ⟨3785210, by rfl⟩ : syracuseStep 5046947 = 7570421) B7570421
theorem B3364631 : Blo 2241435 3364631 := bstep (se 1 (by rfl) ⟨2523473, by rfl⟩ : syracuseStep 3364631 = 5046947) B5046947
theorem B2243087 : Blo 2241435 2243087 := bstep (se 1 (by rfl) ⟨1682315, by rfl⟩ : syracuseStep 2243087 = 3364631) B3364631
theorem B3364637 : Blo 2241435 3364637 := bbase (se 3 (by rfl) ⟨630869, by rfl⟩ : syracuseStep 3364637 = 1261739) (by norm_num)
theorem B2243091 : Blo 2241435 2243091 := bstep (se 1 (by rfl) ⟨1682318, by rfl⟩ : syracuseStep 2243091 = 3364637) B3364637
theorem B5046965 : Blo 2241435 5046965 := bbase (se 5 (by rfl) ⟨236576, by rfl⟩ : syracuseStep 5046965 = 473153) (by norm_num)
theorem B3364643 : Blo 2241435 3364643 := bstep (se 1 (by rfl) ⟨2523482, by rfl⟩ : syracuseStep 3364643 = 5046965) B5046965
theorem B2243095 : Blo 2241435 2243095 := bstep (se 1 (by rfl) ⟨1682321, by rfl⟩ : syracuseStep 2243095 = 3364643) B3364643
theorem B12775157 : Blo 2241435 12775157 := bbase (se 5 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 12775157 = 1197671) (by norm_num)
theorem B8516771 : Blo 2241435 8516771 := bstep (se 1 (by rfl) ⟨6387578, by rfl⟩ : syracuseStep 8516771 = 12775157) B12775157
theorem B5677847 : Blo 2241435 5677847 := bstep (se 1 (by rfl) ⟨4258385, by rfl⟩ : syracuseStep 5677847 = 8516771) B8516771
theorem B3785231 : Blo 2241435 3785231 := bstep (se 1 (by rfl) ⟨2838923, by rfl⟩ : syracuseStep 3785231 = 5677847) B5677847
theorem B2523487 : Blo 2241435 2523487 := bstep (se 1 (by rfl) ⟨1892615, by rfl⟩ : syracuseStep 2523487 = 3785231) B3785231
theorem B3364649 : Blo 2241435 3364649 := bstep (se 2 (by rfl) ⟨1261743, by rfl⟩ : syracuseStep 3364649 = 2523487) B2523487
theorem B2243099 : Blo 2241435 2243099 := bstep (se 1 (by rfl) ⟨1682324, by rfl⟩ : syracuseStep 2243099 = 3364649) B3364649
theorem B6387589 : Blo 2241435 6387589 := bbase (se 4 (by rfl) ⟨598836, by rfl⟩ : syracuseStep 6387589 = 1197673) (by norm_num)
theorem B8516785 : Blo 2241435 8516785 := bstep (se 2 (by rfl) ⟨3193794, by rfl⟩ : syracuseStep 8516785 = 6387589) B6387589
theorem B11355713 : Blo 2241435 11355713 := bstep (se 2 (by rfl) ⟨4258392, by rfl⟩ : syracuseStep 11355713 = 8516785) B8516785
theorem B7570475 : Blo 2241435 7570475 := bstep (se 1 (by rfl) ⟨5677856, by rfl⟩ : syracuseStep 7570475 = 11355713) B11355713
theorem B5046983 : Blo 2241435 5046983 := bstep (se 1 (by rfl) ⟨3785237, by rfl⟩ : syracuseStep 5046983 = 7570475) B7570475
theorem B3364655 : Blo 2241435 3364655 := bstep (se 1 (by rfl) ⟨2523491, by rfl⟩ : syracuseStep 3364655 = 5046983) B5046983
theorem B2243103 : Blo 2241435 2243103 := bstep (se 1 (by rfl) ⟨1682327, by rfl⟩ : syracuseStep 2243103 = 3364655) B3364655
theorem B3364661 : Blo 2241435 3364661 := bbase (se 5 (by rfl) ⟨157718, by rfl⟩ : syracuseStep 3364661 = 315437) (by norm_num)
theorem B2243107 : Blo 2241435 2243107 := bstep (se 1 (by rfl) ⟨1682330, by rfl⟩ : syracuseStep 2243107 = 3364661) B3364661
theorem B5677877 : Blo 2241435 5677877 := bbase (se 5 (by rfl) ⟨266150, by rfl⟩ : syracuseStep 5677877 = 532301) (by norm_num)
theorem B3785251 : Blo 2241435 3785251 := bstep (se 1 (by rfl) ⟨2838938, by rfl⟩ : syracuseStep 3785251 = 5677877) B5677877
theorem B5047001 : Blo 2241435 5047001 := bstep (se 2 (by rfl) ⟨1892625, by rfl⟩ : syracuseStep 5047001 = 3785251) B3785251
theorem B3364667 : Blo 2241435 3364667 := bstep (se 1 (by rfl) ⟨2523500, by rfl⟩ : syracuseStep 3364667 = 5047001) B5047001
theorem B2243111 : Blo 2241435 2243111 := bstep (se 1 (by rfl) ⟨1682333, by rfl⟩ : syracuseStep 2243111 = 3364667) B3364667
theorem B2523505 : Blo 2241435 2523505 := bbase (se 2 (by rfl) ⟨946314, by rfl⟩ : syracuseStep 2523505 = 1892629) (by norm_num)
theorem B3364673 : Blo 2241435 3364673 := bstep (se 2 (by rfl) ⟨1261752, by rfl⟩ : syracuseStep 3364673 = 2523505) B2523505
theorem B2243115 : Blo 2241435 2243115 := bstep (se 1 (by rfl) ⟨1682336, by rfl⟩ : syracuseStep 2243115 = 3364673) B3364673
theorem B3593045 : Blo 2241435 3593045 := bbase (se 9 (by rfl) ⟨10526, by rfl⟩ : syracuseStep 3593045 = 21053) (by norm_num)
theorem B9581453 : Blo 2241435 9581453 := bstep (se 3 (by rfl) ⟨1796522, by rfl⟩ : syracuseStep 9581453 = 3593045) B3593045
theorem B6387635 : Blo 2241435 6387635 := bstep (se 1 (by rfl) ⟨4790726, by rfl⟩ : syracuseStep 6387635 = 9581453) B9581453
theorem B4258423 : Blo 2241435 4258423 := bstep (se 1 (by rfl) ⟨3193817, by rfl⟩ : syracuseStep 4258423 = 6387635) B6387635
theorem B5677897 : Blo 2241435 5677897 := bstep (se 2 (by rfl) ⟨2129211, by rfl⟩ : syracuseStep 5677897 = 4258423) B4258423
theorem B7570529 : Blo 2241435 7570529 := bstep (se 2 (by rfl) ⟨2838948, by rfl⟩ : syracuseStep 7570529 = 5677897) B5677897
theorem B5047019 : Blo 2241435 5047019 := bstep (se 1 (by rfl) ⟨3785264, by rfl⟩ : syracuseStep 5047019 = 7570529) B7570529
theorem B3364679 : Blo 2241435 3364679 := bstep (se 1 (by rfl) ⟨2523509, by rfl⟩ : syracuseStep 3364679 = 5047019) B5047019
theorem B2243119 : Blo 2241435 2243119 := bstep (se 1 (by rfl) ⟨1682339, by rfl⟩ : syracuseStep 2243119 = 3364679) B3364679
theorem B3364685 : Blo 2241435 3364685 := bbase (se 3 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 3364685 = 1261757) (by norm_num)
theorem B2243123 : Blo 2241435 2243123 := bstep (se 1 (by rfl) ⟨1682342, by rfl⟩ : syracuseStep 2243123 = 3364685) B3364685
theorem B5047037 : Blo 2241435 5047037 := bbase (se 3 (by rfl) ⟨946319, by rfl⟩ : syracuseStep 5047037 = 1892639) (by norm_num)
theorem B3364691 : Blo 2241435 3364691 := bstep (se 1 (by rfl) ⟨2523518, by rfl⟩ : syracuseStep 3364691 = 5047037) B5047037
theorem B2243127 : Blo 2241435 2243127 := bstep (se 1 (by rfl) ⟨1682345, by rfl⟩ : syracuseStep 2243127 = 3364691) B3364691
theorem B3785285 : Blo 2241435 3785285 := bbase (se 4 (by rfl) ⟨354870, by rfl⟩ : syracuseStep 3785285 = 709741) (by norm_num)
theorem B2523523 : Blo 2241435 2523523 := bstep (se 1 (by rfl) ⟨1892642, by rfl⟩ : syracuseStep 2523523 = 3785285) B3785285
theorem B3364697 : Blo 2241435 3364697 := bstep (se 2 (by rfl) ⟨1261761, by rfl⟩ : syracuseStep 3364697 = 2523523) B2523523
theorem B2243131 : Blo 2241435 2243131 := bstep (se 1 (by rfl) ⟨1682348, by rfl⟩ : syracuseStep 2243131 = 3364697) B3364697
theorem B17033813 : Blo 2241435 17033813 := bbase (se 8 (by rfl) ⟨99807, by rfl⟩ : syracuseStep 17033813 = 199615) (by norm_num)
theorem B11355875 : Blo 2241435 11355875 := bstep (se 1 (by rfl) ⟨8516906, by rfl⟩ : syracuseStep 11355875 = 17033813) B17033813
theorem B7570583 : Blo 2241435 7570583 := bstep (se 1 (by rfl) ⟨5677937, by rfl⟩ : syracuseStep 7570583 = 11355875) B11355875
theorem B5047055 : Blo 2241435 5047055 := bstep (se 1 (by rfl) ⟨3785291, by rfl⟩ : syracuseStep 5047055 = 7570583) B7570583
theorem B3364703 : Blo 2241435 3364703 := bstep (se 1 (by rfl) ⟨2523527, by rfl⟩ : syracuseStep 3364703 = 5047055) B5047055
theorem B2243135 : Blo 2241435 2243135 := bstep (se 1 (by rfl) ⟨1682351, by rfl⟩ : syracuseStep 2243135 = 3364703) B3364703
theorem B3364709 : Blo 2241435 3364709 := bbase (se 4 (by rfl) ⟨315441, by rfl⟩ : syracuseStep 3364709 = 630883) (by norm_num)
theorem B2243139 : Blo 2241435 2243139 := bstep (se 1 (by rfl) ⟨1682354, by rfl⟩ : syracuseStep 2243139 = 3364709) B3364709
theorem B4258469 : Blo 2241435 4258469 := bbase (se 4 (by rfl) ⟨399231, by rfl⟩ : syracuseStep 4258469 = 798463) (by norm_num)
theorem B2838979 : Blo 2241435 2838979 := bstep (se 1 (by rfl) ⟨2129234, by rfl⟩ : syracuseStep 2838979 = 4258469) B4258469
theorem B3785305 : Blo 2241435 3785305 := bstep (se 2 (by rfl) ⟨1419489, by rfl⟩ : syracuseStep 3785305 = 2838979) B2838979
theorem B5047073 : Blo 2241435 5047073 := bstep (se 2 (by rfl) ⟨1892652, by rfl⟩ : syracuseStep 5047073 = 3785305) B3785305
theorem B3364715 : Blo 2241435 3364715 := bstep (se 1 (by rfl) ⟨2523536, by rfl⟩ : syracuseStep 3364715 = 5047073) B5047073
theorem B2243143 : Blo 2241435 2243143 := bstep (se 1 (by rfl) ⟨1682357, by rfl⟩ : syracuseStep 2243143 = 3364715) B3364715
theorem B2523541 : Blo 2241435 2523541 := bbase (se 6 (by rfl) ⟨59145, by rfl⟩ : syracuseStep 2523541 = 118291) (by norm_num)
theorem B3364721 : Blo 2241435 3364721 := bstep (se 2 (by rfl) ⟨1261770, by rfl⟩ : syracuseStep 3364721 = 2523541) B2523541
theorem B2243147 : Blo 2241435 2243147 := bstep (se 1 (by rfl) ⟨1682360, by rfl⟩ : syracuseStep 2243147 = 3364721) B3364721
theorem B2838989 : Blo 2241435 2838989 := bbase (se 3 (by rfl) ⟨532310, by rfl⟩ : syracuseStep 2838989 = 1064621) (by norm_num)
theorem B7570637 : Blo 2241435 7570637 := bstep (se 3 (by rfl) ⟨1419494, by rfl⟩ : syracuseStep 7570637 = 2838989) B2838989
theorem B5047091 : Blo 2241435 5047091 := bstep (se 1 (by rfl) ⟨3785318, by rfl⟩ : syracuseStep 5047091 = 7570637) B7570637
theorem B3364727 : Blo 2241435 3364727 := bstep (se 1 (by rfl) ⟨2523545, by rfl⟩ : syracuseStep 3364727 = 5047091) B5047091
theorem B2243151 : Blo 2241435 2243151 := bstep (se 1 (by rfl) ⟨1682363, by rfl⟩ : syracuseStep 2243151 = 3364727) B3364727
theorem B3364733 : Blo 2241435 3364733 := bbase (se 3 (by rfl) ⟨630887, by rfl⟩ : syracuseStep 3364733 = 1261775) (by norm_num)
theorem B2243155 : Blo 2241435 2243155 := bstep (se 1 (by rfl) ⟨1682366, by rfl⟩ : syracuseStep 2243155 = 3364733) B3364733
theorem B5047109 : Blo 2241435 5047109 := bbase (se 4 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 5047109 = 946333) (by norm_num)
theorem B3364739 : Blo 2241435 3364739 := bstep (se 1 (by rfl) ⟨2523554, by rfl⟩ : syracuseStep 3364739 = 5047109) B5047109
theorem B2243159 : Blo 2241435 2243159 := bstep (se 1 (by rfl) ⟨1682369, by rfl⟩ : syracuseStep 2243159 = 3364739) B3364739
theorem B4790821 : Blo 2241435 4790821 := bbase (se 4 (by rfl) ⟨449139, by rfl⟩ : syracuseStep 4790821 = 898279) (by norm_num)
theorem B6387761 : Blo 2241435 6387761 := bstep (se 2 (by rfl) ⟨2395410, by rfl⟩ : syracuseStep 6387761 = 4790821) B4790821
theorem B4258507 : Blo 2241435 4258507 := bstep (se 1 (by rfl) ⟨3193880, by rfl⟩ : syracuseStep 4258507 = 6387761) B6387761
theorem B5678009 : Blo 2241435 5678009 := bstep (se 2 (by rfl) ⟨2129253, by rfl⟩ : syracuseStep 5678009 = 4258507) B4258507
theorem B3785339 : Blo 2241435 3785339 := bstep (se 1 (by rfl) ⟨2839004, by rfl⟩ : syracuseStep 3785339 = 5678009) B5678009
theorem B2523559 : Blo 2241435 2523559 := bstep (se 1 (by rfl) ⟨1892669, by rfl⟩ : syracuseStep 2523559 = 3785339) B3785339
theorem B3364745 : Blo 2241435 3364745 := bstep (se 2 (by rfl) ⟨1261779, by rfl⟩ : syracuseStep 3364745 = 2523559) B2523559
theorem B2243163 : Blo 2241435 2243163 := bstep (se 1 (by rfl) ⟨1682372, by rfl⟩ : syracuseStep 2243163 = 3364745) B3364745
theorem B11356037 : Blo 2241435 11356037 := bbase (se 4 (by rfl) ⟨1064628, by rfl⟩ : syracuseStep 11356037 = 2129257) (by norm_num)
theorem B7570691 : Blo 2241435 7570691 := bstep (se 1 (by rfl) ⟨5678018, by rfl⟩ : syracuseStep 7570691 = 11356037) B11356037
theorem B5047127 : Blo 2241435 5047127 := bstep (se 1 (by rfl) ⟨3785345, by rfl⟩ : syracuseStep 5047127 = 7570691) B7570691
theorem B3364751 : Blo 2241435 3364751 := bstep (se 1 (by rfl) ⟨2523563, by rfl⟩ : syracuseStep 3364751 = 5047127) B5047127
theorem B2243167 : Blo 2241435 2243167 := bstep (se 1 (by rfl) ⟨1682375, by rfl⟩ : syracuseStep 2243167 = 3364751) B3364751
theorem B3364757 : Blo 2241435 3364757 := bbase (se 6 (by rfl) ⟨78861, by rfl⟩ : syracuseStep 3364757 = 157723) (by norm_num)
theorem B2243171 : Blo 2241435 2243171 := bstep (se 1 (by rfl) ⟨1682378, by rfl⟩ : syracuseStep 2243171 = 3364757) B3364757
theorem B9095125 : Blo 2241435 9095125 := bbase (se 7 (by rfl) ⟨106583, by rfl⟩ : syracuseStep 9095125 = 213167) (by norm_num)
theorem B12126833 : Blo 2241435 12126833 := bstep (se 2 (by rfl) ⟨4547562, by rfl⟩ : syracuseStep 12126833 = 9095125) B9095125
theorem B8084555 : Blo 2241435 8084555 := bstep (se 1 (by rfl) ⟨6063416, by rfl⟩ : syracuseStep 8084555 = 12126833) B12126833
theorem B5389703 : Blo 2241435 5389703 := bstep (se 1 (by rfl) ⟨4042277, by rfl⟩ : syracuseStep 5389703 = 8084555) B8084555
theorem B3593135 : Blo 2241435 3593135 := bstep (se 1 (by rfl) ⟨2694851, by rfl⟩ : syracuseStep 3593135 = 5389703) B5389703
theorem B2395423 : Blo 2241435 2395423 := bstep (se 1 (by rfl) ⟨1796567, by rfl⟩ : syracuseStep 2395423 = 3593135) B3593135
theorem B12775589 : Blo 2241435 12775589 := bstep (se 4 (by rfl) ⟨1197711, by rfl⟩ : syracuseStep 12775589 = 2395423) B2395423
theorem B8517059 : Blo 2241435 8517059 := bstep (se 1 (by rfl) ⟨6387794, by rfl⟩ : syracuseStep 8517059 = 12775589) B12775589
theorem B5678039 : Blo 2241435 5678039 := bstep (se 1 (by rfl) ⟨4258529, by rfl⟩ : syracuseStep 5678039 = 8517059) B8517059
theorem B3785359 : Blo 2241435 3785359 := bstep (se 1 (by rfl) ⟨2839019, by rfl⟩ : syracuseStep 3785359 = 5678039) B5678039
theorem B5047145 : Blo 2241435 5047145 := bstep (se 2 (by rfl) ⟨1892679, by rfl⟩ : syracuseStep 5047145 = 3785359) B3785359
theorem B3364763 : Blo 2241435 3364763 := bstep (se 1 (by rfl) ⟨2523572, by rfl⟩ : syracuseStep 3364763 = 5047145) B5047145
theorem B2243175 : Blo 2241435 2243175 := bstep (se 1 (by rfl) ⟨1682381, by rfl⟩ : syracuseStep 2243175 = 3364763) B3364763
theorem B2523577 : Blo 2241435 2523577 := bbase (se 2 (by rfl) ⟨946341, by rfl⟩ : syracuseStep 2523577 = 1892683) (by norm_num)
theorem B3364769 : Blo 2241435 3364769 := bstep (se 2 (by rfl) ⟨1261788, by rfl⟩ : syracuseStep 3364769 = 2523577) B2523577
theorem B2243179 : Blo 2241435 2243179 := bstep (se 1 (by rfl) ⟨1682384, by rfl⟩ : syracuseStep 2243179 = 3364769) B3364769
theorem B2273789 : Blo 2241435 2273789 := bbase (se 3 (by rfl) ⟨426335, by rfl⟩ : syracuseStep 2273789 = 852671) (by norm_num)
theorem B6063437 : Blo 2241435 6063437 := bstep (se 3 (by rfl) ⟨1136894, by rfl⟩ : syracuseStep 6063437 = 2273789) B2273789
theorem B16169165 : Blo 2241435 16169165 := bstep (se 3 (by rfl) ⟨3031718, by rfl⟩ : syracuseStep 16169165 = 6063437) B6063437
theorem B10779443 : Blo 2241435 10779443 := bstep (se 1 (by rfl) ⟨8084582, by rfl⟩ : syracuseStep 10779443 = 16169165) B16169165
theorem B7186295 : Blo 2241435 7186295 := bstep (se 1 (by rfl) ⟨5389721, by rfl⟩ : syracuseStep 7186295 = 10779443) B10779443
theorem B4790863 : Blo 2241435 4790863 := bstep (se 1 (by rfl) ⟨3593147, by rfl⟩ : syracuseStep 4790863 = 7186295) B7186295
theorem B6387817 : Blo 2241435 6387817 := bstep (se 2 (by rfl) ⟨2395431, by rfl⟩ : syracuseStep 6387817 = 4790863) B4790863
theorem B8517089 : Blo 2241435 8517089 := bstep (se 2 (by rfl) ⟨3193908, by rfl⟩ : syracuseStep 8517089 = 6387817) B6387817
theorem B5678059 : Blo 2241435 5678059 := bstep (se 1 (by rfl) ⟨4258544, by rfl⟩ : syracuseStep 5678059 = 8517089) B8517089
theorem B7570745 : Blo 2241435 7570745 := bstep (se 2 (by rfl) ⟨2839029, by rfl⟩ : syracuseStep 7570745 = 5678059) B5678059
theorem B5047163 : Blo 2241435 5047163 := bstep (se 1 (by rfl) ⟨3785372, by rfl⟩ : syracuseStep 5047163 = 7570745) B7570745
theorem B3364775 : Blo 2241435 3364775 := bstep (se 1 (by rfl) ⟨2523581, by rfl⟩ : syracuseStep 3364775 = 5047163) B5047163
theorem B2243183 : Blo 2241435 2243183 := bstep (se 1 (by rfl) ⟨1682387, by rfl⟩ : syracuseStep 2243183 = 3364775) B3364775
theorem B3364781 : Blo 2241435 3364781 := bbase (se 3 (by rfl) ⟨630896, by rfl⟩ : syracuseStep 3364781 = 1261793) (by norm_num)
theorem B2243187 : Blo 2241435 2243187 := bstep (se 1 (by rfl) ⟨1682390, by rfl⟩ : syracuseStep 2243187 = 3364781) B3364781
theorem B5047181 : Blo 2241435 5047181 := bbase (se 3 (by rfl) ⟨946346, by rfl⟩ : syracuseStep 5047181 = 1892693) (by norm_num)
theorem B3364787 : Blo 2241435 3364787 := bstep (se 1 (by rfl) ⟨2523590, by rfl⟩ : syracuseStep 3364787 = 5047181) B5047181
theorem B2243191 : Blo 2241435 2243191 := bstep (se 1 (by rfl) ⟨1682393, by rfl⟩ : syracuseStep 2243191 = 3364787) B3364787
theorem B2839045 : Blo 2241435 2839045 := bbase (se 4 (by rfl) ⟨266160, by rfl⟩ : syracuseStep 2839045 = 532321) (by norm_num)
theorem B3785393 : Blo 2241435 3785393 := bstep (se 2 (by rfl) ⟨1419522, by rfl⟩ : syracuseStep 3785393 = 2839045) B2839045
theorem B2523595 : Blo 2241435 2523595 := bstep (se 1 (by rfl) ⟨1892696, by rfl⟩ : syracuseStep 2523595 = 3785393) B3785393
theorem B3364793 : Blo 2241435 3364793 := bstep (se 2 (by rfl) ⟨1261797, by rfl⟩ : syracuseStep 3364793 = 2523595) B2523595
theorem B2243195 : Blo 2241435 2243195 := bstep (se 1 (by rfl) ⟨1682396, by rfl⟩ : syracuseStep 2243195 = 3364793) B3364793
theorem B77700181 : Blo 2241435 77700181 := bbase (se 8 (by rfl) ⟨455274, by rfl⟩ : syracuseStep 77700181 = 910549) (by norm_num)
theorem B103600241 : Blo 2241435 103600241 := bstep (se 2 (by rfl) ⟨38850090, by rfl⟩ : syracuseStep 103600241 = 77700181) B77700181
theorem B69066827 : Blo 2241435 69066827 := bstep (se 1 (by rfl) ⟨51800120, by rfl⟩ : syracuseStep 69066827 = 103600241) B103600241
theorem B46044551 : Blo 2241435 46044551 := bstep (se 1 (by rfl) ⟨34533413, by rfl⟩ : syracuseStep 46044551 = 69066827) B69066827
theorem B30696367 : Blo 2241435 30696367 := bstep (se 1 (by rfl) ⟨23022275, by rfl⟩ : syracuseStep 30696367 = 46044551) B46044551
theorem B40928489 : Blo 2241435 40928489 := bstep (se 2 (by rfl) ⟨15348183, by rfl⟩ : syracuseStep 40928489 = 30696367) B30696367
theorem B27285659 : Blo 2241435 27285659 := bstep (se 1 (by rfl) ⟨20464244, by rfl⟩ : syracuseStep 27285659 = 40928489) B40928489
theorem B18190439 : Blo 2241435 18190439 := bstep (se 1 (by rfl) ⟨13642829, by rfl⟩ : syracuseStep 18190439 = 27285659) B27285659
theorem B12126959 : Blo 2241435 12126959 := bstep (se 1 (by rfl) ⟨9095219, by rfl⟩ : syracuseStep 12126959 = 18190439) B18190439
theorem B8084639 : Blo 2241435 8084639 := bstep (se 1 (by rfl) ⟨6063479, by rfl⟩ : syracuseStep 8084639 = 12126959) B12126959
theorem B5389759 : Blo 2241435 5389759 := bstep (se 1 (by rfl) ⟨4042319, by rfl⟩ : syracuseStep 5389759 = 8084639) B8084639
theorem B28745381 : Blo 2241435 28745381 := bstep (se 4 (by rfl) ⟨2694879, by rfl⟩ : syracuseStep 28745381 = 5389759) B5389759
theorem B19163587 : Blo 2241435 19163587 := bstep (se 1 (by rfl) ⟨14372690, by rfl⟩ : syracuseStep 19163587 = 28745381) B28745381
theorem B25551449 : Blo 2241435 25551449 := bstep (se 2 (by rfl) ⟨9581793, by rfl⟩ : syracuseStep 25551449 = 19163587) B19163587
theorem B17034299 : Blo 2241435 17034299 := bstep (se 1 (by rfl) ⟨12775724, by rfl⟩ : syracuseStep 17034299 = 25551449) B25551449
theorem B11356199 : Blo 2241435 11356199 := bstep (se 1 (by rfl) ⟨8517149, by rfl⟩ : syracuseStep 11356199 = 17034299) B17034299
theorem B7570799 : Blo 2241435 7570799 := bstep (se 1 (by rfl) ⟨5678099, by rfl⟩ : syracuseStep 7570799 = 11356199) B11356199
theorem B5047199 : Blo 2241435 5047199 := bstep (se 1 (by rfl) ⟨3785399, by rfl⟩ : syracuseStep 5047199 = 7570799) B7570799
theorem B3364799 : Blo 2241435 3364799 := bstep (se 1 (by rfl) ⟨2523599, by rfl⟩ : syracuseStep 3364799 = 5047199) B5047199
theorem B2243199 : Blo 2241435 2243199 := bstep (se 1 (by rfl) ⟨1682399, by rfl⟩ : syracuseStep 2243199 = 3364799) B3364799
theorem B3364805 : Blo 2241435 3364805 := bbase (se 4 (by rfl) ⟨315450, by rfl⟩ : syracuseStep 3364805 = 630901) (by norm_num)
theorem B2243203 : Blo 2241435 2243203 := bstep (se 1 (by rfl) ⟨1682402, by rfl⟩ : syracuseStep 2243203 = 3364805) B3364805
theorem B3785413 : Blo 2241435 3785413 := bbase (se 4 (by rfl) ⟨354882, by rfl⟩ : syracuseStep 3785413 = 709765) (by norm_num)
theorem B5047217 : Blo 2241435 5047217 := bstep (se 2 (by rfl) ⟨1892706, by rfl⟩ : syracuseStep 5047217 = 3785413) B3785413
theorem B3364811 : Blo 2241435 3364811 := bstep (se 1 (by rfl) ⟨2523608, by rfl⟩ : syracuseStep 3364811 = 5047217) B5047217
theorem B2243207 : Blo 2241435 2243207 := bstep (se 1 (by rfl) ⟨1682405, by rfl⟩ : syracuseStep 2243207 = 3364811) B3364811
theorem B2523613 : Blo 2241435 2523613 := bbase (se 3 (by rfl) ⟨473177, by rfl⟩ : syracuseStep 2523613 = 946355) (by norm_num)
theorem B3364817 : Blo 2241435 3364817 := bstep (se 2 (by rfl) ⟨1261806, by rfl⟩ : syracuseStep 3364817 = 2523613) B2523613
theorem B2243211 : Blo 2241435 2243211 := bstep (se 1 (by rfl) ⟨1682408, by rfl⟩ : syracuseStep 2243211 = 3364817) B3364817
theorem B7570853 : Blo 2241435 7570853 := bbase (se 4 (by rfl) ⟨709767, by rfl⟩ : syracuseStep 7570853 = 1419535) (by norm_num)
theorem B5047235 : Blo 2241435 5047235 := bstep (se 1 (by rfl) ⟨3785426, by rfl⟩ : syracuseStep 5047235 = 7570853) B7570853
theorem B3364823 : Blo 2241435 3364823 := bstep (se 1 (by rfl) ⟨2523617, by rfl⟩ : syracuseStep 3364823 = 5047235) B5047235
theorem B2243215 : Blo 2241435 2243215 := bstep (se 1 (by rfl) ⟨1682411, by rfl⟩ : syracuseStep 2243215 = 3364823) B3364823
theorem B3364829 : Blo 2241435 3364829 := bbase (se 3 (by rfl) ⟨630905, by rfl⟩ : syracuseStep 3364829 = 1261811) (by norm_num)
theorem B2243219 : Blo 2241435 2243219 := bstep (se 1 (by rfl) ⟨1682414, by rfl⟩ : syracuseStep 2243219 = 3364829) B3364829
theorem B5047253 : Blo 2241435 5047253 := bbase (se 7 (by rfl) ⟨59147, by rfl⟩ : syracuseStep 5047253 = 118295) (by norm_num)
theorem B3364835 : Blo 2241435 3364835 := bstep (se 1 (by rfl) ⟨2523626, by rfl⟩ : syracuseStep 3364835 = 5047253) B5047253
theorem B2243223 : Blo 2241435 2243223 := bstep (se 1 (by rfl) ⟨1682417, by rfl⟩ : syracuseStep 2243223 = 3364835) B3364835
theorem B2592965 : Blo 2241435 2592965 := bbase (se 4 (by rfl) ⟨243090, by rfl⟩ : syracuseStep 2592965 = 486181) (by norm_num)
theorem B6914573 : Blo 2241435 6914573 := bstep (se 3 (by rfl) ⟨1296482, by rfl⟩ : syracuseStep 6914573 = 2592965) B2592965
theorem B4609715 : Blo 2241435 4609715 := bstep (se 1 (by rfl) ⟨3457286, by rfl⟩ : syracuseStep 4609715 = 6914573) B6914573
theorem B12292573 : Blo 2241435 12292573 := bstep (se 3 (by rfl) ⟨2304857, by rfl⟩ : syracuseStep 12292573 = 4609715) B4609715
theorem B16390097 : Blo 2241435 16390097 := bstep (se 2 (by rfl) ⟨6146286, by rfl⟩ : syracuseStep 16390097 = 12292573) B12292573
theorem B10926731 : Blo 2241435 10926731 := bstep (se 1 (by rfl) ⟨8195048, by rfl⟩ : syracuseStep 10926731 = 16390097) B16390097
theorem B7284487 : Blo 2241435 7284487 := bstep (se 1 (by rfl) ⟨5463365, by rfl⟩ : syracuseStep 7284487 = 10926731) B10926731
theorem B9712649 : Blo 2241435 9712649 := bstep (se 2 (by rfl) ⟨3642243, by rfl⟩ : syracuseStep 9712649 = 7284487) B7284487
theorem B6475099 : Blo 2241435 6475099 := bstep (se 1 (by rfl) ⟨4856324, by rfl⟩ : syracuseStep 6475099 = 9712649) B9712649
theorem B8633465 : Blo 2241435 8633465 := bstep (se 2 (by rfl) ⟨3237549, by rfl⟩ : syracuseStep 8633465 = 6475099) B6475099
theorem B5755643 : Blo 2241435 5755643 := bstep (se 1 (by rfl) ⟨4316732, by rfl⟩ : syracuseStep 5755643 = 8633465) B8633465
theorem B3837095 : Blo 2241435 3837095 := bstep (se 1 (by rfl) ⟨2877821, by rfl⟩ : syracuseStep 3837095 = 5755643) B5755643
theorem B2558063 : Blo 2241435 2558063 := bstep (se 1 (by rfl) ⟨1918547, by rfl⟩ : syracuseStep 2558063 = 3837095) B3837095
theorem B6821501 : Blo 2241435 6821501 := bstep (se 3 (by rfl) ⟨1279031, by rfl⟩ : syracuseStep 6821501 = 2558063) B2558063
theorem B18190669 : Blo 2241435 18190669 := bstep (se 3 (by rfl) ⟨3410750, by rfl⟩ : syracuseStep 18190669 = 6821501) B6821501
theorem B24254225 : Blo 2241435 24254225 := bstep (se 2 (by rfl) ⟨9095334, by rfl⟩ : syracuseStep 24254225 = 18190669) B18190669
theorem B16169483 : Blo 2241435 16169483 := bstep (se 1 (by rfl) ⟨12127112, by rfl⟩ : syracuseStep 16169483 = 24254225) B24254225
theorem B10779655 : Blo 2241435 10779655 := bstep (se 1 (by rfl) ⟨8084741, by rfl⟩ : syracuseStep 10779655 = 16169483) B16169483
theorem B14372873 : Blo 2241435 14372873 := bstep (se 2 (by rfl) ⟨5389827, by rfl⟩ : syracuseStep 14372873 = 10779655) B10779655
theorem B9581915 : Blo 2241435 9581915 := bstep (se 1 (by rfl) ⟨7186436, by rfl⟩ : syracuseStep 9581915 = 14372873) B14372873
theorem B6387943 : Blo 2241435 6387943 := bstep (se 1 (by rfl) ⟨4790957, by rfl⟩ : syracuseStep 6387943 = 9581915) B9581915
theorem B8517257 : Blo 2241435 8517257 := bstep (se 2 (by rfl) ⟨3193971, by rfl⟩ : syracuseStep 8517257 = 6387943) B6387943
theorem B5678171 : Blo 2241435 5678171 := bstep (se 1 (by rfl) ⟨4258628, by rfl⟩ : syracuseStep 5678171 = 8517257) B8517257
theorem B3785447 : Blo 2241435 3785447 := bstep (se 1 (by rfl) ⟨2839085, by rfl⟩ : syracuseStep 3785447 = 5678171) B5678171
theorem B2523631 : Blo 2241435 2523631 := bstep (se 1 (by rfl) ⟨1892723, by rfl⟩ : syracuseStep 2523631 = 3785447) B3785447
theorem B3364841 : Blo 2241435 3364841 := bstep (se 2 (by rfl) ⟨1261815, by rfl⟩ : syracuseStep 3364841 = 2523631) B2523631
theorem B2243227 : Blo 2241435 2243227 := bstep (se 1 (by rfl) ⟨1682420, by rfl⟩ : syracuseStep 2243227 = 3364841) B3364841
theorem B19163861 : Blo 2241435 19163861 := bbase (se 7 (by rfl) ⟨224576, by rfl⟩ : syracuseStep 19163861 = 449153) (by norm_num)
theorem B12775907 : Blo 2241435 12775907 := bstep (se 1 (by rfl) ⟨9581930, by rfl⟩ : syracuseStep 12775907 = 19163861) B19163861
theorem B8517271 : Blo 2241435 8517271 := bstep (se 1 (by rfl) ⟨6387953, by rfl⟩ : syracuseStep 8517271 = 12775907) B12775907
theorem B11356361 : Blo 2241435 11356361 := bstep (se 2 (by rfl) ⟨4258635, by rfl⟩ : syracuseStep 11356361 = 8517271) B8517271
theorem B7570907 : Blo 2241435 7570907 := bstep (se 1 (by rfl) ⟨5678180, by rfl⟩ : syracuseStep 7570907 = 11356361) B11356361
theorem B5047271 : Blo 2241435 5047271 := bstep (se 1 (by rfl) ⟨3785453, by rfl⟩ : syracuseStep 5047271 = 7570907) B7570907
theorem B3364847 : Blo 2241435 3364847 := bstep (se 1 (by rfl) ⟨2523635, by rfl⟩ : syracuseStep 3364847 = 5047271) B5047271
theorem B2243231 : Blo 2241435 2243231 := bstep (se 1 (by rfl) ⟨1682423, by rfl⟩ : syracuseStep 2243231 = 3364847) B3364847
theorem B3364853 : Blo 2241435 3364853 := bbase (se 5 (by rfl) ⟨157727, by rfl⟩ : syracuseStep 3364853 = 315455) (by norm_num)
theorem B2243235 : Blo 2241435 2243235 := bstep (se 1 (by rfl) ⟨1682426, by rfl⟩ : syracuseStep 2243235 = 3364853) B3364853
theorem B6063589 : Blo 2241435 6063589 := bbase (se 4 (by rfl) ⟨568461, by rfl⟩ : syracuseStep 6063589 = 1136923) (by norm_num)
theorem B8084785 : Blo 2241435 8084785 := bstep (se 2 (by rfl) ⟨3031794, by rfl⟩ : syracuseStep 8084785 = 6063589) B6063589
theorem B10779713 : Blo 2241435 10779713 := bstep (se 2 (by rfl) ⟨4042392, by rfl⟩ : syracuseStep 10779713 = 8084785) B8084785
theorem B7186475 : Blo 2241435 7186475 := bstep (se 1 (by rfl) ⟨5389856, by rfl⟩ : syracuseStep 7186475 = 10779713) B10779713
theorem B4790983 : Blo 2241435 4790983 := bstep (se 1 (by rfl) ⟨3593237, by rfl⟩ : syracuseStep 4790983 = 7186475) B7186475
theorem B6387977 : Blo 2241435 6387977 := bstep (se 2 (by rfl) ⟨2395491, by rfl⟩ : syracuseStep 6387977 = 4790983) B4790983
theorem B4258651 : Blo 2241435 4258651 := bstep (se 1 (by rfl) ⟨3193988, by rfl⟩ : syracuseStep 4258651 = 6387977) B6387977
theorem B5678201 : Blo 2241435 5678201 := bstep (se 2 (by rfl) ⟨2129325, by rfl⟩ : syracuseStep 5678201 = 4258651) B4258651
theorem B3785467 : Blo 2241435 3785467 := bstep (se 1 (by rfl) ⟨2839100, by rfl⟩ : syracuseStep 3785467 = 5678201) B5678201
theorem B5047289 : Blo 2241435 5047289 := bstep (se 2 (by rfl) ⟨1892733, by rfl⟩ : syracuseStep 5047289 = 3785467) B3785467
theorem B3364859 : Blo 2241435 3364859 := bstep (se 1 (by rfl) ⟨2523644, by rfl⟩ : syracuseStep 3364859 = 5047289) B5047289
theorem B2243239 : Blo 2241435 2243239 := bstep (se 1 (by rfl) ⟨1682429, by rfl⟩ : syracuseStep 2243239 = 3364859) B3364859
theorem B2523649 : Blo 2241435 2523649 := bbase (se 2 (by rfl) ⟨946368, by rfl⟩ : syracuseStep 2523649 = 1892737) (by norm_num)
theorem B3364865 : Blo 2241435 3364865 := bstep (se 2 (by rfl) ⟨1261824, by rfl⟩ : syracuseStep 3364865 = 2523649) B2523649
theorem B2243243 : Blo 2241435 2243243 := bstep (se 1 (by rfl) ⟨1682432, by rfl⟩ : syracuseStep 2243243 = 3364865) B3364865
theorem B5678221 : Blo 2241435 5678221 := bbase (se 3 (by rfl) ⟨1064666, by rfl⟩ : syracuseStep 5678221 = 2129333) (by norm_num)
theorem B7570961 : Blo 2241435 7570961 := bstep (se 2 (by rfl) ⟨2839110, by rfl⟩ : syracuseStep 7570961 = 5678221) B5678221
theorem B5047307 : Blo 2241435 5047307 := bstep (se 1 (by rfl) ⟨3785480, by rfl⟩ : syracuseStep 5047307 = 7570961) B7570961
theorem B3364871 : Blo 2241435 3364871 := bstep (se 1 (by rfl) ⟨2523653, by rfl⟩ : syracuseStep 3364871 = 5047307) B5047307
theorem B2243247 : Blo 2241435 2243247 := bstep (se 1 (by rfl) ⟨1682435, by rfl⟩ : syracuseStep 2243247 = 3364871) B3364871
theorem B3364877 : Blo 2241435 3364877 := bbase (se 3 (by rfl) ⟨630914, by rfl⟩ : syracuseStep 3364877 = 1261829) (by norm_num)
theorem B2243251 : Blo 2241435 2243251 := bstep (se 1 (by rfl) ⟨1682438, by rfl⟩ : syracuseStep 2243251 = 3364877) B3364877
theorem B5047325 : Blo 2241435 5047325 := bbase (se 3 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 5047325 = 1892747) (by norm_num)
theorem B3364883 : Blo 2241435 3364883 := bstep (se 1 (by rfl) ⟨2523662, by rfl⟩ : syracuseStep 3364883 = 5047325) B5047325
theorem B2243255 : Blo 2241435 2243255 := bstep (se 1 (by rfl) ⟨1682441, by rfl⟩ : syracuseStep 2243255 = 3364883) B3364883
theorem B3785501 : Blo 2241435 3785501 := bbase (se 3 (by rfl) ⟨709781, by rfl⟩ : syracuseStep 3785501 = 1419563) (by norm_num)
theorem B2523667 : Blo 2241435 2523667 := bstep (se 1 (by rfl) ⟨1892750, by rfl⟩ : syracuseStep 2523667 = 3785501) B3785501
theorem B3364889 : Blo 2241435 3364889 := bstep (se 2 (by rfl) ⟨1261833, by rfl⟩ : syracuseStep 3364889 = 2523667) B2523667
theorem B2243259 : Blo 2241435 2243259 := bstep (se 1 (by rfl) ⟨1682444, by rfl⟩ : syracuseStep 2243259 = 3364889) B3364889
theorem B6063653 : Blo 2241435 6063653 := bbase (se 4 (by rfl) ⟨568467, by rfl⟩ : syracuseStep 6063653 = 1136935) (by norm_num)
theorem B4042435 : Blo 2241435 4042435 := bstep (se 1 (by rfl) ⟨3031826, by rfl⟩ : syracuseStep 4042435 = 6063653) B6063653
theorem B5389913 : Blo 2241435 5389913 := bstep (se 2 (by rfl) ⟨2021217, by rfl⟩ : syracuseStep 5389913 = 4042435) B4042435
theorem B14373101 : Blo 2241435 14373101 := bstep (se 3 (by rfl) ⟨2694956, by rfl⟩ : syracuseStep 14373101 = 5389913) B5389913
theorem B9582067 : Blo 2241435 9582067 := bstep (se 1 (by rfl) ⟨7186550, by rfl⟩ : syracuseStep 9582067 = 14373101) B14373101
theorem B12776089 : Blo 2241435 12776089 := bstep (se 2 (by rfl) ⟨4791033, by rfl⟩ : syracuseStep 12776089 = 9582067) B9582067
theorem B17034785 : Blo 2241435 17034785 := bstep (se 2 (by rfl) ⟨6388044, by rfl⟩ : syracuseStep 17034785 = 12776089) B12776089
theorem B11356523 : Blo 2241435 11356523 := bstep (se 1 (by rfl) ⟨8517392, by rfl⟩ : syracuseStep 11356523 = 17034785) B17034785
theorem B7571015 : Blo 2241435 7571015 := bstep (se 1 (by rfl) ⟨5678261, by rfl⟩ : syracuseStep 7571015 = 11356523) B11356523
theorem B5047343 : Blo 2241435 5047343 := bstep (se 1 (by rfl) ⟨3785507, by rfl⟩ : syracuseStep 5047343 = 7571015) B7571015
theorem B3364895 : Blo 2241435 3364895 := bstep (se 1 (by rfl) ⟨2523671, by rfl⟩ : syracuseStep 3364895 = 5047343) B5047343
theorem B2243263 : Blo 2241435 2243263 := bstep (se 1 (by rfl) ⟨1682447, by rfl⟩ : syracuseStep 2243263 = 3364895) B3364895
theorem B3364901 : Blo 2241435 3364901 := bbase (se 4 (by rfl) ⟨315459, by rfl⟩ : syracuseStep 3364901 = 630919) (by norm_num)
theorem B2243267 : Blo 2241435 2243267 := bstep (se 1 (by rfl) ⟨1682450, by rfl⟩ : syracuseStep 2243267 = 3364901) B3364901
theorem B2839141 : Blo 2241435 2839141 := bbase (se 4 (by rfl) ⟨266169, by rfl⟩ : syracuseStep 2839141 = 532339) (by norm_num)
theorem B3785521 : Blo 2241435 3785521 := bstep (se 2 (by rfl) ⟨1419570, by rfl⟩ : syracuseStep 3785521 = 2839141) B2839141
theorem B5047361 : Blo 2241435 5047361 := bstep (se 2 (by rfl) ⟨1892760, by rfl⟩ : syracuseStep 5047361 = 3785521) B3785521
theorem B3364907 : Blo 2241435 3364907 := bstep (se 1 (by rfl) ⟨2523680, by rfl⟩ : syracuseStep 3364907 = 5047361) B5047361
theorem B2243271 : Blo 2241435 2243271 := bstep (se 1 (by rfl) ⟨1682453, by rfl⟩ : syracuseStep 2243271 = 3364907) B3364907
theorem B2523685 : Blo 2241435 2523685 := bbase (se 4 (by rfl) ⟨236595, by rfl⟩ : syracuseStep 2523685 = 473191) (by norm_num)
theorem B3364913 : Blo 2241435 3364913 := bstep (se 2 (by rfl) ⟨1261842, by rfl⟩ : syracuseStep 3364913 = 2523685) B2523685
theorem B2243275 : Blo 2241435 2243275 := bstep (se 1 (by rfl) ⟨1682456, by rfl⟩ : syracuseStep 2243275 = 3364913) B3364913
theorem B4547773 : Blo 2241435 4547773 := bbase (se 3 (by rfl) ⟨852707, by rfl⟩ : syracuseStep 4547773 = 1705415) (by norm_num)
theorem B6063697 : Blo 2241435 6063697 := bstep (se 2 (by rfl) ⟨2273886, by rfl⟩ : syracuseStep 6063697 = 4547773) B4547773
theorem B8084929 : Blo 2241435 8084929 := bstep (se 2 (by rfl) ⟨3031848, by rfl⟩ : syracuseStep 8084929 = 6063697) B6063697
theorem B10779905 : Blo 2241435 10779905 := bstep (se 2 (by rfl) ⟨4042464, by rfl⟩ : syracuseStep 10779905 = 8084929) B8084929
theorem B7186603 : Blo 2241435 7186603 := bstep (se 1 (by rfl) ⟨5389952, by rfl⟩ : syracuseStep 7186603 = 10779905) B10779905
theorem B9582137 : Blo 2241435 9582137 := bstep (se 2 (by rfl) ⟨3593301, by rfl⟩ : syracuseStep 9582137 = 7186603) B7186603
theorem B6388091 : Blo 2241435 6388091 := bstep (se 1 (by rfl) ⟨4791068, by rfl⟩ : syracuseStep 6388091 = 9582137) B9582137
theorem B4258727 : Blo 2241435 4258727 := bstep (se 1 (by rfl) ⟨3194045, by rfl⟩ : syracuseStep 4258727 = 6388091) B6388091
theorem B2839151 : Blo 2241435 2839151 := bstep (se 1 (by rfl) ⟨2129363, by rfl⟩ : syracuseStep 2839151 = 4258727) B4258727
theorem B7571069 : Blo 2241435 7571069 := bstep (se 3 (by rfl) ⟨1419575, by rfl⟩ : syracuseStep 7571069 = 2839151) B2839151
theorem B5047379 : Blo 2241435 5047379 := bstep (se 1 (by rfl) ⟨3785534, by rfl⟩ : syracuseStep 5047379 = 7571069) B7571069
theorem B3364919 : Blo 2241435 3364919 := bstep (se 1 (by rfl) ⟨2523689, by rfl⟩ : syracuseStep 3364919 = 5047379) B5047379
theorem B2243279 : Blo 2241435 2243279 := bstep (se 1 (by rfl) ⟨1682459, by rfl⟩ : syracuseStep 2243279 = 3364919) B3364919
theorem B3364925 : Blo 2241435 3364925 := bbase (se 3 (by rfl) ⟨630923, by rfl⟩ : syracuseStep 3364925 = 1261847) (by norm_num)
theorem B2243283 : Blo 2241435 2243283 := bstep (se 1 (by rfl) ⟨1682462, by rfl⟩ : syracuseStep 2243283 = 3364925) B3364925
theorem B5047397 : Blo 2241435 5047397 := bbase (se 4 (by rfl) ⟨473193, by rfl⟩ : syracuseStep 5047397 = 946387) (by norm_num)
theorem B3364931 : Blo 2241435 3364931 := bstep (se 1 (by rfl) ⟨2523698, by rfl⟩ : syracuseStep 3364931 = 5047397) B5047397
theorem B2243287 : Blo 2241435 2243287 := bstep (se 1 (by rfl) ⟨1682465, by rfl⟩ : syracuseStep 2243287 = 3364931) B3364931
theorem B5678333 : Blo 2241435 5678333 := bbase (se 3 (by rfl) ⟨1064687, by rfl⟩ : syracuseStep 5678333 = 2129375) (by norm_num)
theorem B3785555 : Blo 2241435 3785555 := bstep (se 1 (by rfl) ⟨2839166, by rfl⟩ : syracuseStep 3785555 = 5678333) B5678333
theorem B2523703 : Blo 2241435 2523703 := bstep (se 1 (by rfl) ⟨1892777, by rfl⟩ : syracuseStep 2523703 = 3785555) B3785555
theorem B3364937 : Blo 2241435 3364937 := bstep (se 2 (by rfl) ⟨1261851, by rfl⟩ : syracuseStep 3364937 = 2523703) B2523703
theorem B2243291 : Blo 2241435 2243291 := bstep (se 1 (by rfl) ⟨1682468, by rfl⟩ : syracuseStep 2243291 = 3364937) B3364937
theorem B4258757 : Blo 2241435 4258757 := bbase (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) (by norm_num)
theorem B11356685 : Blo 2241435 11356685 := bstep (se 3 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 11356685 = 4258757) B4258757
theorem B7571123 : Blo 2241435 7571123 := bstep (se 1 (by rfl) ⟨5678342, by rfl⟩ : syracuseStep 7571123 = 11356685) B11356685
theorem B5047415 : Blo 2241435 5047415 := bstep (se 1 (by rfl) ⟨3785561, by rfl⟩ : syracuseStep 5047415 = 7571123) B7571123
theorem B3364943 : Blo 2241435 3364943 := bstep (se 1 (by rfl) ⟨2523707, by rfl⟩ : syracuseStep 3364943 = 5047415) B5047415
theorem B2243295 : Blo 2241435 2243295 := bstep (se 1 (by rfl) ⟨1682471, by rfl⟩ : syracuseStep 2243295 = 3364943) B3364943
theorem B3364949 : Blo 2241435 3364949 := bbase (se 8 (by rfl) ⟨19716, by rfl⟩ : syracuseStep 3364949 = 39433) (by norm_num)
theorem B2243299 : Blo 2241435 2243299 := bstep (se 1 (by rfl) ⟨1682474, by rfl⟩ : syracuseStep 2243299 = 3364949) B3364949
theorem B4210237 : Blo 2241435 4210237 := bbase (se 3 (by rfl) ⟨789419, by rfl⟩ : syracuseStep 4210237 = 1578839) (by norm_num)
theorem B22454597 : Blo 2241435 22454597 := bstep (se 4 (by rfl) ⟨2105118, by rfl⟩ : syracuseStep 22454597 = 4210237) B4210237
theorem B14969731 : Blo 2241435 14969731 := bstep (se 1 (by rfl) ⟨11227298, by rfl⟩ : syracuseStep 14969731 = 22454597) B22454597
theorem B19959641 : Blo 2241435 19959641 := bstep (se 2 (by rfl) ⟨7484865, by rfl⟩ : syracuseStep 19959641 = 14969731) B14969731
theorem B13306427 : Blo 2241435 13306427 := bstep (se 1 (by rfl) ⟨9979820, by rfl⟩ : syracuseStep 13306427 = 19959641) B19959641
theorem B8870951 : Blo 2241435 8870951 := bstep (se 1 (by rfl) ⟨6653213, by rfl⟩ : syracuseStep 8870951 = 13306427) B13306427
theorem B5913967 : Blo 2241435 5913967 := bstep (se 1 (by rfl) ⟨4435475, by rfl⟩ : syracuseStep 5913967 = 8870951) B8870951
theorem B7885289 : Blo 2241435 7885289 := bstep (se 2 (by rfl) ⟨2956983, by rfl⟩ : syracuseStep 7885289 = 5913967) B5913967
theorem B21027437 : Blo 2241435 21027437 := bstep (se 3 (by rfl) ⟨3942644, by rfl⟩ : syracuseStep 21027437 = 7885289) B7885289
theorem B14018291 : Blo 2241435 14018291 := bstep (se 1 (by rfl) ⟨10513718, by rfl⟩ : syracuseStep 14018291 = 21027437) B21027437
theorem B9345527 : Blo 2241435 9345527 := bstep (se 1 (by rfl) ⟨7009145, by rfl⟩ : syracuseStep 9345527 = 14018291) B14018291
theorem B6230351 : Blo 2241435 6230351 := bstep (se 1 (by rfl) ⟨4672763, by rfl⟩ : syracuseStep 6230351 = 9345527) B9345527
theorem B4153567 : Blo 2241435 4153567 := bstep (se 1 (by rfl) ⟨3115175, by rfl⟩ : syracuseStep 4153567 = 6230351) B6230351
theorem B5538089 : Blo 2241435 5538089 := bstep (se 2 (by rfl) ⟨2076783, by rfl⟩ : syracuseStep 5538089 = 4153567) B4153567
theorem B14768237 : Blo 2241435 14768237 := bstep (se 3 (by rfl) ⟨2769044, by rfl⟩ : syracuseStep 14768237 = 5538089) B5538089
theorem B9845491 : Blo 2241435 9845491 := bstep (se 1 (by rfl) ⟨7384118, by rfl⟩ : syracuseStep 9845491 = 14768237) B14768237
theorem B13127321 : Blo 2241435 13127321 := bstep (se 2 (by rfl) ⟨4922745, by rfl⟩ : syracuseStep 13127321 = 9845491) B9845491
theorem B8751547 : Blo 2241435 8751547 := bstep (se 1 (by rfl) ⟨6563660, by rfl⟩ : syracuseStep 8751547 = 13127321) B13127321
theorem B46674917 : Blo 2241435 46674917 := bstep (se 4 (by rfl) ⟨4375773, by rfl⟩ : syracuseStep 46674917 = 8751547) B8751547
theorem B31116611 : Blo 2241435 31116611 := bstep (se 1 (by rfl) ⟨23337458, by rfl⟩ : syracuseStep 31116611 = 46674917) B46674917
theorem B20744407 : Blo 2241435 20744407 := bstep (se 1 (by rfl) ⟨15558305, by rfl⟩ : syracuseStep 20744407 = 31116611) B31116611
theorem B27659209 : Blo 2241435 27659209 := bstep (se 2 (by rfl) ⟨10372203, by rfl⟩ : syracuseStep 27659209 = 20744407) B20744407
theorem B590063125 : Blo 2241435 590063125 := bstep (se 6 (by rfl) ⟨13829604, by rfl⟩ : syracuseStep 590063125 = 27659209) B27659209
theorem B786750833 : Blo 2241435 786750833 := bstep (se 2 (by rfl) ⟨295031562, by rfl⟩ : syracuseStep 786750833 = 590063125) B590063125
theorem B524500555 : Blo 2241435 524500555 := bstep (se 1 (by rfl) ⟨393375416, by rfl⟩ : syracuseStep 524500555 = 786750833) B786750833
theorem B699334073 : Blo 2241435 699334073 := bstep (se 2 (by rfl) ⟨262250277, by rfl⟩ : syracuseStep 699334073 = 524500555) B524500555
theorem B466222715 : Blo 2241435 466222715 := bstep (se 1 (by rfl) ⟨349667036, by rfl⟩ : syracuseStep 466222715 = 699334073) B699334073
theorem B310815143 : Blo 2241435 310815143 := bstep (se 1 (by rfl) ⟨233111357, by rfl⟩ : syracuseStep 310815143 = 466222715) B466222715
theorem B207210095 : Blo 2241435 207210095 := bstep (se 1 (by rfl) ⟨155407571, by rfl⟩ : syracuseStep 207210095 = 310815143) B310815143
theorem B138140063 : Blo 2241435 138140063 := bstep (se 1 (by rfl) ⟨103605047, by rfl⟩ : syracuseStep 138140063 = 207210095) B207210095
theorem B92093375 : Blo 2241435 92093375 := bstep (se 1 (by rfl) ⟨69070031, by rfl⟩ : syracuseStep 92093375 = 138140063) B138140063
theorem B61395583 : Blo 2241435 61395583 := bstep (se 1 (by rfl) ⟨46046687, by rfl⟩ : syracuseStep 61395583 = 92093375) B92093375
theorem B81860777 : Blo 2241435 81860777 := bstep (se 2 (by rfl) ⟨30697791, by rfl⟩ : syracuseStep 81860777 = 61395583) B61395583
theorem B54573851 : Blo 2241435 54573851 := bstep (se 1 (by rfl) ⟨40930388, by rfl⟩ : syracuseStep 54573851 = 81860777) B81860777
theorem B36382567 : Blo 2241435 36382567 := bstep (se 1 (by rfl) ⟨27286925, by rfl⟩ : syracuseStep 36382567 = 54573851) B54573851
theorem B48510089 : Blo 2241435 48510089 := bstep (se 2 (by rfl) ⟨18191283, by rfl⟩ : syracuseStep 48510089 = 36382567) B36382567
theorem B32340059 : Blo 2241435 32340059 := bstep (se 1 (by rfl) ⟨24255044, by rfl⟩ : syracuseStep 32340059 = 48510089) B48510089
theorem B21560039 : Blo 2241435 21560039 := bstep (se 1 (by rfl) ⟨16170029, by rfl⟩ : syracuseStep 21560039 = 32340059) B32340059
theorem B14373359 : Blo 2241435 14373359 := bstep (se 1 (by rfl) ⟨10780019, by rfl⟩ : syracuseStep 14373359 = 21560039) B21560039
theorem B9582239 : Blo 2241435 9582239 := bstep (se 1 (by rfl) ⟨7186679, by rfl⟩ : syracuseStep 9582239 = 14373359) B14373359
theorem B6388159 : Blo 2241435 6388159 := bstep (se 1 (by rfl) ⟨4791119, by rfl⟩ : syracuseStep 6388159 = 9582239) B9582239
theorem B8517545 : Blo 2241435 8517545 := bstep (se 2 (by rfl) ⟨3194079, by rfl⟩ : syracuseStep 8517545 = 6388159) B6388159
theorem B5678363 : Blo 2241435 5678363 := bstep (se 1 (by rfl) ⟨4258772, by rfl⟩ : syracuseStep 5678363 = 8517545) B8517545
theorem B3785575 : Blo 2241435 3785575 := bstep (se 1 (by rfl) ⟨2839181, by rfl⟩ : syracuseStep 3785575 = 5678363) B5678363
theorem B5047433 : Blo 2241435 5047433 := bstep (se 2 (by rfl) ⟨1892787, by rfl⟩ : syracuseStep 5047433 = 3785575) B3785575
theorem B3364955 : Blo 2241435 3364955 := bstep (se 1 (by rfl) ⟨2523716, by rfl⟩ : syracuseStep 3364955 = 5047433) B5047433
theorem B2243303 : Blo 2241435 2243303 := bstep (se 1 (by rfl) ⟨1682477, by rfl⟩ : syracuseStep 2243303 = 3364955) B3364955
theorem B2523721 : Blo 2241435 2523721 := bbase (se 2 (by rfl) ⟨946395, by rfl⟩ : syracuseStep 2523721 = 1892791) (by norm_num)
theorem B3364961 : Blo 2241435 3364961 := bstep (se 2 (by rfl) ⟨1261860, by rfl⟩ : syracuseStep 3364961 = 2523721) B2523721
theorem B2243307 : Blo 2241435 2243307 := bstep (se 1 (by rfl) ⟨1682480, by rfl⟩ : syracuseStep 2243307 = 3364961) B3364961
theorem B4547837 : Blo 2241435 4547837 := bbase (se 3 (by rfl) ⟨852719, by rfl⟩ : syracuseStep 4547837 = 1705439) (by norm_num)
theorem B12127565 : Blo 2241435 12127565 := bstep (se 3 (by rfl) ⟨2273918, by rfl⟩ : syracuseStep 12127565 = 4547837) B4547837
theorem B8085043 : Blo 2241435 8085043 := bstep (se 1 (by rfl) ⟨6063782, by rfl⟩ : syracuseStep 8085043 = 12127565) B12127565
theorem B10780057 : Blo 2241435 10780057 := bstep (se 2 (by rfl) ⟨4042521, by rfl⟩ : syracuseStep 10780057 = 8085043) B8085043
theorem B14373409 : Blo 2241435 14373409 := bstep (se 2 (by rfl) ⟨5390028, by rfl⟩ : syracuseStep 14373409 = 10780057) B10780057
theorem B19164545 : Blo 2241435 19164545 := bstep (se 2 (by rfl) ⟨7186704, by rfl⟩ : syracuseStep 19164545 = 14373409) B14373409
theorem B12776363 : Blo 2241435 12776363 := bstep (se 1 (by rfl) ⟨9582272, by rfl⟩ : syracuseStep 12776363 = 19164545) B19164545
theorem B8517575 : Blo 2241435 8517575 := bstep (se 1 (by rfl) ⟨6388181, by rfl⟩ : syracuseStep 8517575 = 12776363) B12776363
theorem B5678383 : Blo 2241435 5678383 := bstep (se 1 (by rfl) ⟨4258787, by rfl⟩ : syracuseStep 5678383 = 8517575) B8517575
theorem B7571177 : Blo 2241435 7571177 := bstep (se 2 (by rfl) ⟨2839191, by rfl⟩ : syracuseStep 7571177 = 5678383) B5678383
theorem B5047451 : Blo 2241435 5047451 := bstep (se 1 (by rfl) ⟨3785588, by rfl⟩ : syracuseStep 5047451 = 7571177) B7571177
theorem B3364967 : Blo 2241435 3364967 := bstep (se 1 (by rfl) ⟨2523725, by rfl⟩ : syracuseStep 3364967 = 5047451) B5047451
theorem B2243311 : Blo 2241435 2243311 := bstep (se 1 (by rfl) ⟨1682483, by rfl⟩ : syracuseStep 2243311 = 3364967) B3364967
theorem B3364973 : Blo 2241435 3364973 := bbase (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) (by norm_num)
theorem B2243315 : Blo 2241435 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B5047469 : Blo 2241435 5047469 := bbase (se 3 (by rfl) ⟨946400, by rfl⟩ : syracuseStep 5047469 = 1892801) (by norm_num)
theorem B3364979 : Blo 2241435 3364979 := bstep (se 1 (by rfl) ⟨2523734, by rfl⟩ : syracuseStep 3364979 = 5047469) B5047469
theorem B2243319 : Blo 2241435 2243319 := bstep (se 1 (by rfl) ⟨1682489, by rfl⟩ : syracuseStep 2243319 = 3364979) B3364979
theorem B10232693 : Blo 2241435 10232693 := bbase (se 5 (by rfl) ⟨479657, by rfl⟩ : syracuseStep 10232693 = 959315) (by norm_num)
theorem B6821795 : Blo 2241435 6821795 := bstep (se 1 (by rfl) ⟨5116346, by rfl⟩ : syracuseStep 6821795 = 10232693) B10232693
theorem B4547863 : Blo 2241435 4547863 := bstep (se 1 (by rfl) ⟨3410897, by rfl⟩ : syracuseStep 4547863 = 6821795) B6821795
theorem B6063817 : Blo 2241435 6063817 := bstep (se 2 (by rfl) ⟨2273931, by rfl⟩ : syracuseStep 6063817 = 4547863) B4547863
theorem B8085089 : Blo 2241435 8085089 := bstep (se 2 (by rfl) ⟨3031908, by rfl⟩ : syracuseStep 8085089 = 6063817) B6063817
theorem B5390059 : Blo 2241435 5390059 := bstep (se 1 (by rfl) ⟨4042544, by rfl⟩ : syracuseStep 5390059 = 8085089) B8085089
theorem B7186745 : Blo 2241435 7186745 := bstep (se 2 (by rfl) ⟨2695029, by rfl⟩ : syracuseStep 7186745 = 5390059) B5390059
theorem B4791163 : Blo 2241435 4791163 := bstep (se 1 (by rfl) ⟨3593372, by rfl⟩ : syracuseStep 4791163 = 7186745) B7186745
theorem B6388217 : Blo 2241435 6388217 := bstep (se 2 (by rfl) ⟨2395581, by rfl⟩ : syracuseStep 6388217 = 4791163) B4791163
theorem B4258811 : Blo 2241435 4258811 := bstep (se 1 (by rfl) ⟨3194108, by rfl⟩ : syracuseStep 4258811 = 6388217) B6388217
theorem B2839207 : Blo 2241435 2839207 := bstep (se 1 (by rfl) ⟨2129405, by rfl⟩ : syracuseStep 2839207 = 4258811) B4258811
theorem B3785609 : Blo 2241435 3785609 := bstep (se 2 (by rfl) ⟨1419603, by rfl⟩ : syracuseStep 3785609 = 2839207) B2839207
theorem B2523739 : Blo 2241435 2523739 := bstep (se 1 (by rfl) ⟨1892804, by rfl⟩ : syracuseStep 2523739 = 3785609) B3785609
theorem B3364985 : Blo 2241435 3364985 := bstep (se 2 (by rfl) ⟨1261869, by rfl⟩ : syracuseStep 3364985 = 2523739) B2523739
theorem B2243323 : Blo 2241435 2243323 := bstep (se 1 (by rfl) ⟨1682492, by rfl⟩ : syracuseStep 2243323 = 3364985) B3364985
theorem B10780133 : Blo 2241435 10780133 := bbase (se 4 (by rfl) ⟨1010637, by rfl⟩ : syracuseStep 10780133 = 2021275) (by norm_num)
theorem B28747021 : Blo 2241435 28747021 := bstep (se 3 (by rfl) ⟨5390066, by rfl⟩ : syracuseStep 28747021 = 10780133) B10780133
theorem B38329361 : Blo 2241435 38329361 := bstep (se 2 (by rfl) ⟨14373510, by rfl⟩ : syracuseStep 38329361 = 28747021) B28747021
theorem B25552907 : Blo 2241435 25552907 := bstep (se 1 (by rfl) ⟨19164680, by rfl⟩ : syracuseStep 25552907 = 38329361) B38329361
theorem B17035271 : Blo 2241435 17035271 := bstep (se 1 (by rfl) ⟨12776453, by rfl⟩ : syracuseStep 17035271 = 25552907) B25552907
theorem B11356847 : Blo 2241435 11356847 := bstep (se 1 (by rfl) ⟨8517635, by rfl⟩ : syracuseStep 11356847 = 17035271) B17035271
theorem B7571231 : Blo 2241435 7571231 := bstep (se 1 (by rfl) ⟨5678423, by rfl⟩ : syracuseStep 7571231 = 11356847) B11356847
theorem B5047487 : Blo 2241435 5047487 := bstep (se 1 (by rfl) ⟨3785615, by rfl⟩ : syracuseStep 5047487 = 7571231) B7571231
theorem B3364991 : Blo 2241435 3364991 := bstep (se 1 (by rfl) ⟨2523743, by rfl⟩ : syracuseStep 3364991 = 5047487) B5047487
theorem B2243327 : Blo 2241435 2243327 := bstep (se 1 (by rfl) ⟨1682495, by rfl⟩ : syracuseStep 2243327 = 3364991) B3364991
theorem B3364997 : Blo 2241435 3364997 := bbase (se 4 (by rfl) ⟨315468, by rfl⟩ : syracuseStep 3364997 = 630937) (by norm_num)
theorem B2243331 : Blo 2241435 2243331 := bstep (se 1 (by rfl) ⟨1682498, by rfl⟩ : syracuseStep 2243331 = 3364997) B3364997
theorem B3785629 : Blo 2241435 3785629 := bbase (se 3 (by rfl) ⟨709805, by rfl⟩ : syracuseStep 3785629 = 1419611) (by norm_num)
theorem B5047505 : Blo 2241435 5047505 := bstep (se 2 (by rfl) ⟨1892814, by rfl⟩ : syracuseStep 5047505 = 3785629) B3785629
theorem B3365003 : Blo 2241435 3365003 := bstep (se 1 (by rfl) ⟨2523752, by rfl⟩ : syracuseStep 3365003 = 5047505) B5047505
theorem B2243335 : Blo 2241435 2243335 := bstep (se 1 (by rfl) ⟨1682501, by rfl⟩ : syracuseStep 2243335 = 3365003) B3365003
theorem B2523757 : Blo 2241435 2523757 := bbase (se 3 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 2523757 = 946409) (by norm_num)
theorem B3365009 : Blo 2241435 3365009 := bstep (se 2 (by rfl) ⟨1261878, by rfl⟩ : syracuseStep 3365009 = 2523757) B2523757
theorem B2243339 : Blo 2241435 2243339 := bstep (se 1 (by rfl) ⟨1682504, by rfl⟩ : syracuseStep 2243339 = 3365009) B3365009
theorem B7571285 : Blo 2241435 7571285 := bbase (se 9 (by rfl) ⟨22181, by rfl⟩ : syracuseStep 7571285 = 44363) (by norm_num)
theorem B5047523 : Blo 2241435 5047523 := bstep (se 1 (by rfl) ⟨3785642, by rfl⟩ : syracuseStep 5047523 = 7571285) B7571285
theorem B3365015 : Blo 2241435 3365015 := bstep (se 1 (by rfl) ⟨2523761, by rfl⟩ : syracuseStep 3365015 = 5047523) B5047523
theorem B2243343 : Blo 2241435 2243343 := bstep (se 1 (by rfl) ⟨1682507, by rfl⟩ : syracuseStep 2243343 = 3365015) B3365015
theorem B3365021 : Blo 2241435 3365021 := bbase (se 3 (by rfl) ⟨630941, by rfl⟩ : syracuseStep 3365021 = 1261883) (by norm_num)
theorem B2243347 : Blo 2241435 2243347 := bstep (se 1 (by rfl) ⟨1682510, by rfl⟩ : syracuseStep 2243347 = 3365021) B3365021
theorem B5047541 : Blo 2241435 5047541 := bbase (se 5 (by rfl) ⟨236603, by rfl⟩ : syracuseStep 5047541 = 473207) (by norm_num)
theorem B3365027 : Blo 2241435 3365027 := bstep (se 1 (by rfl) ⟨2523770, by rfl⟩ : syracuseStep 3365027 = 5047541) B5047541
theorem B2243351 : Blo 2241435 2243351 := bstep (se 1 (by rfl) ⟨1682513, by rfl⟩ : syracuseStep 2243351 = 3365027) B3365027
theorem B2877985 : Blo 2241435 2877985 := bbase (se 2 (by rfl) ⟨1079244, by rfl⟩ : syracuseStep 2877985 = 2158489) (by norm_num)
theorem B3837313 : Blo 2241435 3837313 := bstep (se 2 (by rfl) ⟨1438992, by rfl⟩ : syracuseStep 3837313 = 2877985) B2877985
theorem B20465669 : Blo 2241435 20465669 := bstep (se 4 (by rfl) ⟨1918656, by rfl⟩ : syracuseStep 20465669 = 3837313) B3837313
theorem B54575117 : Blo 2241435 54575117 := bstep (se 3 (by rfl) ⟨10232834, by rfl⟩ : syracuseStep 54575117 = 20465669) B20465669
theorem B36383411 : Blo 2241435 36383411 := bstep (se 1 (by rfl) ⟨27287558, by rfl⟩ : syracuseStep 36383411 = 54575117) B54575117
theorem B24255607 : Blo 2241435 24255607 := bstep (se 1 (by rfl) ⟨18191705, by rfl⟩ : syracuseStep 24255607 = 36383411) B36383411
theorem B32340809 : Blo 2241435 32340809 := bstep (se 2 (by rfl) ⟨12127803, by rfl⟩ : syracuseStep 32340809 = 24255607) B24255607
theorem B21560539 : Blo 2241435 21560539 := bstep (se 1 (by rfl) ⟨16170404, by rfl⟩ : syracuseStep 21560539 = 32340809) B32340809
theorem B28747385 : Blo 2241435 28747385 := bstep (se 2 (by rfl) ⟨10780269, by rfl⟩ : syracuseStep 28747385 = 21560539) B21560539
theorem B19164923 : Blo 2241435 19164923 := bstep (se 1 (by rfl) ⟨14373692, by rfl⟩ : syracuseStep 19164923 = 28747385) B28747385
theorem B12776615 : Blo 2241435 12776615 := bstep (se 1 (by rfl) ⟨9582461, by rfl⟩ : syracuseStep 12776615 = 19164923) B19164923
theorem B8517743 : Blo 2241435 8517743 := bstep (se 1 (by rfl) ⟨6388307, by rfl⟩ : syracuseStep 8517743 = 12776615) B12776615
theorem B5678495 : Blo 2241435 5678495 := bstep (se 1 (by rfl) ⟨4258871, by rfl⟩ : syracuseStep 5678495 = 8517743) B8517743
theorem B3785663 : Blo 2241435 3785663 := bstep (se 1 (by rfl) ⟨2839247, by rfl⟩ : syracuseStep 3785663 = 5678495) B5678495
theorem B2523775 : Blo 2241435 2523775 := bstep (se 1 (by rfl) ⟨1892831, by rfl⟩ : syracuseStep 2523775 = 3785663) B3785663
theorem B3365033 : Blo 2241435 3365033 := bstep (se 2 (by rfl) ⟨1261887, by rfl⟩ : syracuseStep 3365033 = 2523775) B2523775
theorem B2243355 : Blo 2241435 2243355 := bstep (se 1 (by rfl) ⟨1682516, by rfl⟩ : syracuseStep 2243355 = 3365033) B3365033
theorem B23023925 : Blo 2241435 23023925 := bbase (se 5 (by rfl) ⟨1079246, by rfl⟩ : syracuseStep 23023925 = 2158493) (by norm_num)
theorem B15349283 : Blo 2241435 15349283 := bstep (se 1 (by rfl) ⟨11511962, by rfl⟩ : syracuseStep 15349283 = 23023925) B23023925
theorem B10232855 : Blo 2241435 10232855 := bstep (se 1 (by rfl) ⟨7674641, by rfl⟩ : syracuseStep 10232855 = 15349283) B15349283
theorem B6821903 : Blo 2241435 6821903 := bstep (se 1 (by rfl) ⟨5116427, by rfl⟩ : syracuseStep 6821903 = 10232855) B10232855
theorem B4547935 : Blo 2241435 4547935 := bstep (se 1 (by rfl) ⟨3410951, by rfl⟩ : syracuseStep 4547935 = 6821903) B6821903
theorem B6063913 : Blo 2241435 6063913 := bstep (se 2 (by rfl) ⟨2273967, by rfl⟩ : syracuseStep 6063913 = 4547935) B4547935
theorem B8085217 : Blo 2241435 8085217 := bstep (se 2 (by rfl) ⟨3031956, by rfl⟩ : syracuseStep 8085217 = 6063913) B6063913
theorem B10780289 : Blo 2241435 10780289 := bstep (se 2 (by rfl) ⟨4042608, by rfl⟩ : syracuseStep 10780289 = 8085217) B8085217
theorem B7186859 : Blo 2241435 7186859 := bstep (se 1 (by rfl) ⟨5390144, by rfl⟩ : syracuseStep 7186859 = 10780289) B10780289
theorem B4791239 : Blo 2241435 4791239 := bstep (se 1 (by rfl) ⟨3593429, by rfl⟩ : syracuseStep 4791239 = 7186859) B7186859
theorem B3194159 : Blo 2241435 3194159 := bstep (se 1 (by rfl) ⟨2395619, by rfl⟩ : syracuseStep 3194159 = 4791239) B4791239
theorem B8517757 : Blo 2241435 8517757 := bstep (se 3 (by rfl) ⟨1597079, by rfl⟩ : syracuseStep 8517757 = 3194159) B3194159
theorem B11357009 : Blo 2241435 11357009 := bstep (se 2 (by rfl) ⟨4258878, by rfl⟩ : syracuseStep 11357009 = 8517757) B8517757
theorem B7571339 : Blo 2241435 7571339 := bstep (se 1 (by rfl) ⟨5678504, by rfl⟩ : syracuseStep 7571339 = 11357009) B11357009
theorem B5047559 : Blo 2241435 5047559 := bstep (se 1 (by rfl) ⟨3785669, by rfl⟩ : syracuseStep 5047559 = 7571339) B7571339
theorem B3365039 : Blo 2241435 3365039 := bstep (se 1 (by rfl) ⟨2523779, by rfl⟩ : syracuseStep 3365039 = 5047559) B5047559
theorem B2243359 : Blo 2241435 2243359 := bstep (se 1 (by rfl) ⟨1682519, by rfl⟩ : syracuseStep 2243359 = 3365039) B3365039
theorem B3365045 : Blo 2241435 3365045 := bbase (se 5 (by rfl) ⟨157736, by rfl⟩ : syracuseStep 3365045 = 315473) (by norm_num)
theorem B2243363 : Blo 2241435 2243363 := bstep (se 1 (by rfl) ⟨1682522, by rfl⟩ : syracuseStep 2243363 = 3365045) B3365045
theorem B5678525 : Blo 2241435 5678525 := bbase (se 3 (by rfl) ⟨1064723, by rfl⟩ : syracuseStep 5678525 = 2129447) (by norm_num)
theorem B3785683 : Blo 2241435 3785683 := bstep (se 1 (by rfl) ⟨2839262, by rfl⟩ : syracuseStep 3785683 = 5678525) B5678525
theorem B5047577 : Blo 2241435 5047577 := bstep (se 2 (by rfl) ⟨1892841, by rfl⟩ : syracuseStep 5047577 = 3785683) B3785683
theorem B3365051 : Blo 2241435 3365051 := bstep (se 1 (by rfl) ⟨2523788, by rfl⟩ : syracuseStep 3365051 = 5047577) B5047577
theorem B2243367 : Blo 2241435 2243367 := bstep (se 1 (by rfl) ⟨1682525, by rfl⟩ : syracuseStep 2243367 = 3365051) B3365051
theorem B2523793 : Blo 2241435 2523793 := bbase (se 2 (by rfl) ⟨946422, by rfl⟩ : syracuseStep 2523793 = 1892845) (by norm_num)
theorem B3365057 : Blo 2241435 3365057 := bstep (se 2 (by rfl) ⟨1261896, by rfl⟩ : syracuseStep 3365057 = 2523793) B2523793
theorem B2243371 : Blo 2241435 2243371 := bstep (se 1 (by rfl) ⟨1682528, by rfl⟩ : syracuseStep 2243371 = 3365057) B3365057
theorem B4258909 : Blo 2241435 4258909 := bbase (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) (by norm_num)
theorem B5678545 : Blo 2241435 5678545 := bstep (se 2 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 5678545 = 4258909) B4258909
theorem B7571393 : Blo 2241435 7571393 := bstep (se 2 (by rfl) ⟨2839272, by rfl⟩ : syracuseStep 7571393 = 5678545) B5678545
theorem B5047595 : Blo 2241435 5047595 := bstep (se 1 (by rfl) ⟨3785696, by rfl⟩ : syracuseStep 5047595 = 7571393) B7571393
theorem B3365063 : Blo 2241435 3365063 := bstep (se 1 (by rfl) ⟨2523797, by rfl⟩ : syracuseStep 3365063 = 5047595) B5047595
theorem B2243375 : Blo 2241435 2243375 := bstep (se 1 (by rfl) ⟨1682531, by rfl⟩ : syracuseStep 2243375 = 3365063) B3365063
theorem B3365069 : Blo 2241435 3365069 := bbase (se 3 (by rfl) ⟨630950, by rfl⟩ : syracuseStep 3365069 = 1261901) (by norm_num)
theorem B2243379 : Blo 2241435 2243379 := bstep (se 1 (by rfl) ⟨1682534, by rfl⟩ : syracuseStep 2243379 = 3365069) B3365069
theorem B5047613 : Blo 2241435 5047613 := bbase (se 3 (by rfl) ⟨946427, by rfl⟩ : syracuseStep 5047613 = 1892855) (by norm_num)
theorem B3365075 : Blo 2241435 3365075 := bstep (se 1 (by rfl) ⟨2523806, by rfl⟩ : syracuseStep 3365075 = 5047613) B5047613
theorem B2243383 : Blo 2241435 2243383 := bstep (se 1 (by rfl) ⟨1682537, by rfl⟩ : syracuseStep 2243383 = 3365075) B3365075
theorem B3785717 : Blo 2241435 3785717 := bbase (se 5 (by rfl) ⟨177455, by rfl⟩ : syracuseStep 3785717 = 354911) (by norm_num)
theorem B2523811 : Blo 2241435 2523811 := bstep (se 1 (by rfl) ⟨1892858, by rfl⟩ : syracuseStep 2523811 = 3785717) B3785717
theorem B3365081 : Blo 2241435 3365081 := bstep (se 2 (by rfl) ⟨1261905, by rfl⟩ : syracuseStep 3365081 = 2523811) B2523811
theorem B2243387 : Blo 2241435 2243387 := bstep (se 1 (by rfl) ⟨1682540, by rfl⟩ : syracuseStep 2243387 = 3365081) B3365081
theorem B5390221 : Blo 2241435 5390221 := bbase (se 3 (by rfl) ⟨1010666, by rfl⟩ : syracuseStep 5390221 = 2021333) (by norm_num)
theorem B7186961 : Blo 2241435 7186961 := bstep (se 2 (by rfl) ⟨2695110, by rfl⟩ : syracuseStep 7186961 = 5390221) B5390221
theorem B4791307 : Blo 2241435 4791307 := bstep (se 1 (by rfl) ⟨3593480, by rfl⟩ : syracuseStep 4791307 = 7186961) B7186961
theorem B6388409 : Blo 2241435 6388409 := bstep (se 2 (by rfl) ⟨2395653, by rfl⟩ : syracuseStep 6388409 = 4791307) B4791307
theorem B17035757 : Blo 2241435 17035757 := bstep (se 3 (by rfl) ⟨3194204, by rfl⟩ : syracuseStep 17035757 = 6388409) B6388409
theorem B11357171 : Blo 2241435 11357171 := bstep (se 1 (by rfl) ⟨8517878, by rfl⟩ : syracuseStep 11357171 = 17035757) B17035757
theorem B7571447 : Blo 2241435 7571447 := bstep (se 1 (by rfl) ⟨5678585, by rfl⟩ : syracuseStep 7571447 = 11357171) B11357171
theorem B5047631 : Blo 2241435 5047631 := bstep (se 1 (by rfl) ⟨3785723, by rfl⟩ : syracuseStep 5047631 = 7571447) B7571447
theorem B3365087 : Blo 2241435 3365087 := bstep (se 1 (by rfl) ⟨2523815, by rfl⟩ : syracuseStep 3365087 = 5047631) B5047631
theorem B2243391 : Blo 2241435 2243391 := bstep (se 1 (by rfl) ⟨1682543, by rfl⟩ : syracuseStep 2243391 = 3365087) B3365087
theorem B3365093 : Blo 2241435 3365093 := bbase (se 4 (by rfl) ⟨315477, by rfl⟩ : syracuseStep 3365093 = 630955) (by norm_num)
theorem B2243395 : Blo 2241435 2243395 := bstep (se 1 (by rfl) ⟨1682546, by rfl⟩ : syracuseStep 2243395 = 3365093) B3365093
theorem B4791325 : Blo 2241435 4791325 := bbase (se 3 (by rfl) ⟨898373, by rfl⟩ : syracuseStep 4791325 = 1796747) (by norm_num)
theorem B6388433 : Blo 2241435 6388433 := bstep (se 2 (by rfl) ⟨2395662, by rfl⟩ : syracuseStep 6388433 = 4791325) B4791325
theorem B4258955 : Blo 2241435 4258955 := bstep (se 1 (by rfl) ⟨3194216, by rfl⟩ : syracuseStep 4258955 = 6388433) B6388433
theorem B2839303 : Blo 2241435 2839303 := bstep (se 1 (by rfl) ⟨2129477, by rfl⟩ : syracuseStep 2839303 = 4258955) B4258955
theorem B3785737 : Blo 2241435 3785737 := bstep (se 2 (by rfl) ⟨1419651, by rfl⟩ : syracuseStep 3785737 = 2839303) B2839303
theorem B5047649 : Blo 2241435 5047649 := bstep (se 2 (by rfl) ⟨1892868, by rfl⟩ : syracuseStep 5047649 = 3785737) B3785737
theorem B3365099 : Blo 2241435 3365099 := bstep (se 1 (by rfl) ⟨2523824, by rfl⟩ : syracuseStep 3365099 = 5047649) B5047649
theorem B2243399 : Blo 2241435 2243399 := bstep (se 1 (by rfl) ⟨1682549, by rfl⟩ : syracuseStep 2243399 = 3365099) B3365099
theorem B2523829 : Blo 2241435 2523829 := bbase (se 5 (by rfl) ⟨118304, by rfl⟩ : syracuseStep 2523829 = 236609) (by norm_num)
theorem B3365105 : Blo 2241435 3365105 := bstep (se 2 (by rfl) ⟨1261914, by rfl⟩ : syracuseStep 3365105 = 2523829) B2523829
theorem B2243403 : Blo 2241435 2243403 := bstep (se 1 (by rfl) ⟨1682552, by rfl⟩ : syracuseStep 2243403 = 3365105) B3365105
theorem B2839313 : Blo 2241435 2839313 := bbase (se 2 (by rfl) ⟨1064742, by rfl⟩ : syracuseStep 2839313 = 2129485) (by norm_num)
theorem B7571501 : Blo 2241435 7571501 := bstep (se 3 (by rfl) ⟨1419656, by rfl⟩ : syracuseStep 7571501 = 2839313) B2839313
theorem B5047667 : Blo 2241435 5047667 := bstep (se 1 (by rfl) ⟨3785750, by rfl⟩ : syracuseStep 5047667 = 7571501) B7571501
theorem B3365111 : Blo 2241435 3365111 := bstep (se 1 (by rfl) ⟨2523833, by rfl⟩ : syracuseStep 3365111 = 5047667) B5047667
theorem B2243407 : Blo 2241435 2243407 := bstep (se 1 (by rfl) ⟨1682555, by rfl⟩ : syracuseStep 2243407 = 3365111) B3365111
theorem B3365117 : Blo 2241435 3365117 := bbase (se 3 (by rfl) ⟨630959, by rfl⟩ : syracuseStep 3365117 = 1261919) (by norm_num)
theorem B2243411 : Blo 2241435 2243411 := bstep (se 1 (by rfl) ⟨1682558, by rfl⟩ : syracuseStep 2243411 = 3365117) B3365117
theorem B5047685 : Blo 2241435 5047685 := bbase (se 4 (by rfl) ⟨473220, by rfl⟩ : syracuseStep 5047685 = 946441) (by norm_num)
theorem B3365123 : Blo 2241435 3365123 := bstep (se 1 (by rfl) ⟨2523842, by rfl⟩ : syracuseStep 3365123 = 5047685) B5047685
theorem B2243415 : Blo 2241435 2243415 := bstep (se 1 (by rfl) ⟨1682561, by rfl⟩ : syracuseStep 2243415 = 3365123) B3365123
theorem B3194245 : Blo 2241435 3194245 := bbase (se 4 (by rfl) ⟨299460, by rfl⟩ : syracuseStep 3194245 = 598921) (by norm_num)
theorem B4258993 : Blo 2241435 4258993 := bstep (se 2 (by rfl) ⟨1597122, by rfl⟩ : syracuseStep 4258993 = 3194245) B3194245
theorem B5678657 : Blo 2241435 5678657 := bstep (se 2 (by rfl) ⟨2129496, by rfl⟩ : syracuseStep 5678657 = 4258993) B4258993
theorem B3785771 : Blo 2241435 3785771 := bstep (se 1 (by rfl) ⟨2839328, by rfl⟩ : syracuseStep 3785771 = 5678657) B5678657
theorem B2523847 : Blo 2241435 2523847 := bstep (se 1 (by rfl) ⟨1892885, by rfl⟩ : syracuseStep 2523847 = 3785771) B3785771
theorem B3365129 : Blo 2241435 3365129 := bstep (se 2 (by rfl) ⟨1261923, by rfl⟩ : syracuseStep 3365129 = 2523847) B2523847
theorem B2243419 : Blo 2241435 2243419 := bstep (se 1 (by rfl) ⟨1682564, by rfl⟩ : syracuseStep 2243419 = 3365129) B3365129
theorem B11357333 : Blo 2241435 11357333 := bbase (se 6 (by rfl) ⟨266187, by rfl⟩ : syracuseStep 11357333 = 532375) (by norm_num)
theorem B7571555 : Blo 2241435 7571555 := bstep (se 1 (by rfl) ⟨5678666, by rfl⟩ : syracuseStep 7571555 = 11357333) B11357333
theorem B5047703 : Blo 2241435 5047703 := bstep (se 1 (by rfl) ⟨3785777, by rfl⟩ : syracuseStep 5047703 = 7571555) B7571555
theorem B3365135 : Blo 2241435 3365135 := bstep (se 1 (by rfl) ⟨2523851, by rfl⟩ : syracuseStep 3365135 = 5047703) B5047703
theorem B2243423 : Blo 2241435 2243423 := bstep (se 1 (by rfl) ⟨1682567, by rfl⟩ : syracuseStep 2243423 = 3365135) B3365135
theorem B3365141 : Blo 2241435 3365141 := bbase (se 6 (by rfl) ⟨78870, by rfl⟩ : syracuseStep 3365141 = 157741) (by norm_num)
theorem B2243427 : Blo 2241435 2243427 := bstep (se 1 (by rfl) ⟨1682570, by rfl⟩ : syracuseStep 2243427 = 3365141) B3365141
theorem B5390317 : Blo 2241435 5390317 := bbase (se 3 (by rfl) ⟨1010684, by rfl⟩ : syracuseStep 5390317 = 2021369) (by norm_num)
theorem B28748357 : Blo 2241435 28748357 := bstep (se 4 (by rfl) ⟨2695158, by rfl⟩ : syracuseStep 28748357 = 5390317) B5390317
theorem B19165571 : Blo 2241435 19165571 := bstep (se 1 (by rfl) ⟨14374178, by rfl⟩ : syracuseStep 19165571 = 28748357) B28748357
theorem B12777047 : Blo 2241435 12777047 := bstep (se 1 (by rfl) ⟨9582785, by rfl⟩ : syracuseStep 12777047 = 19165571) B19165571
theorem B8518031 : Blo 2241435 8518031 := bstep (se 1 (by rfl) ⟨6388523, by rfl⟩ : syracuseStep 8518031 = 12777047) B12777047
theorem B5678687 : Blo 2241435 5678687 := bstep (se 1 (by rfl) ⟨4259015, by rfl⟩ : syracuseStep 5678687 = 8518031) B8518031
theorem B3785791 : Blo 2241435 3785791 := bstep (se 1 (by rfl) ⟨2839343, by rfl⟩ : syracuseStep 3785791 = 5678687) B5678687
theorem B5047721 : Blo 2241435 5047721 := bstep (se 2 (by rfl) ⟨1892895, by rfl⟩ : syracuseStep 5047721 = 3785791) B3785791
theorem B3365147 : Blo 2241435 3365147 := bstep (se 1 (by rfl) ⟨2523860, by rfl⟩ : syracuseStep 3365147 = 5047721) B5047721
theorem B2243431 : Blo 2241435 2243431 := bstep (se 1 (by rfl) ⟨1682573, by rfl⟩ : syracuseStep 2243431 = 3365147) B3365147
theorem B2523865 : Blo 2241435 2523865 := bbase (se 2 (by rfl) ⟨946449, by rfl⟩ : syracuseStep 2523865 = 1892899) (by norm_num)
theorem B3365153 : Blo 2241435 3365153 := bstep (se 2 (by rfl) ⟨1261932, by rfl⟩ : syracuseStep 3365153 = 2523865) B2523865
theorem B2243435 : Blo 2241435 2243435 := bstep (se 1 (by rfl) ⟨1682576, by rfl⟩ : syracuseStep 2243435 = 3365153) B3365153
theorem C0 (j : ℕ) (h1 : 560358 ≤ j) (h2 : j ≤ 560858) : Blo 2241435 (4 * j + 3) := by
  interval_cases j
  · exact B2241435
  · exact B2241439
  · exact B2241443
  · exact B2241447
  · exact B2241451
  · exact B2241455
  · exact B2241459
  · exact B2241463
  · exact B2241467
  · exact B2241471
  · exact B2241475
  · exact B2241479
  · exact B2241483
  · exact B2241487
  · exact B2241491
  · exact B2241495
  · exact B2241499
  · exact B2241503
  · exact B2241507
  · exact B2241511
  · exact B2241515
  · exact B2241519
  · exact B2241523
  · exact B2241527
  · exact B2241531
  · exact B2241535
  · exact B2241539
  · exact B2241543
  · exact B2241547
  · exact B2241551
  · exact B2241555
  · exact B2241559
  · exact B2241563
  · exact B2241567
  · exact B2241571
  · exact B2241575
  · exact B2241579
  · exact B2241583
  · exact B2241587
  · exact B2241591
  · exact B2241595
  · exact B2241599
  · exact B2241603
  · exact B2241607
  · exact B2241611
  · exact B2241615
  · exact B2241619
  · exact B2241623
  · exact B2241627
  · exact B2241631
  · exact B2241635
  · exact B2241639
  · exact B2241643
  · exact B2241647
  · exact B2241651
  · exact B2241655
  · exact B2241659
  · exact B2241663
  · exact B2241667
  · exact B2241671
  · exact B2241675
  · exact B2241679
  · exact B2241683
  · exact B2241687
  · exact B2241691
  · exact B2241695
  · exact B2241699
  · exact B2241703
  · exact B2241707
  · exact B2241711
  · exact B2241715
  · exact B2241719
  · exact B2241723
  · exact B2241727
  · exact B2241731
  · exact B2241735
  · exact B2241739
  · exact B2241743
  · exact B2241747
  · exact B2241751
  · exact B2241755
  · exact B2241759
  · exact B2241763
  · exact B2241767
  · exact B2241771
  · exact B2241775
  · exact B2241779
  · exact B2241783
  · exact B2241787
  · exact B2241791
  · exact B2241795
  · exact B2241799
  · exact B2241803
  · exact B2241807
  · exact B2241811
  · exact B2241815
  · exact B2241819
  · exact B2241823
  · exact B2241827
  · exact B2241831
  · exact B2241835
  · exact B2241839
  · exact B2241843
  · exact B2241847
  · exact B2241851
  · exact B2241855
  · exact B2241859
  · exact B2241863
  · exact B2241867
  · exact B2241871
  · exact B2241875
  · exact B2241879
  · exact B2241883
  · exact B2241887
  · exact B2241891
  · exact B2241895
  · exact B2241899
  · exact B2241903
  · exact B2241907
  · exact B2241911
  · exact B2241915
  · exact B2241919
  · exact B2241923
  · exact B2241927
  · exact B2241931
  · exact B2241935
  · exact B2241939
  · exact B2241943
  · exact B2241947
  · exact B2241951
  · exact B2241955
  · exact B2241959
  · exact B2241963
  · exact B2241967
  · exact B2241971
  · exact B2241975
  · exact B2241979
  · exact B2241983
  · exact B2241987
  · exact B2241991
  · exact B2241995
  · exact B2241999
  · exact B2242003
  · exact B2242007
  · exact B2242011
  · exact B2242015
  · exact B2242019
  · exact B2242023
  · exact B2242027
  · exact B2242031
  · exact B2242035
  · exact B2242039
  · exact B2242043
  · exact B2242047
  · exact B2242051
  · exact B2242055
  · exact B2242059
  · exact B2242063
  · exact B2242067
  · exact B2242071
  · exact B2242075
  · exact B2242079
  · exact B2242083
  · exact B2242087
  · exact B2242091
  · exact B2242095
  · exact B2242099
  · exact B2242103
  · exact B2242107
  · exact B2242111
  · exact B2242115
  · exact B2242119
  · exact B2242123
  · exact B2242127
  · exact B2242131
  · exact B2242135
  · exact B2242139
  · exact B2242143
  · exact B2242147
  · exact B2242151
  · exact B2242155
  · exact B2242159
  · exact B2242163
  · exact B2242167
  · exact B2242171
  · exact B2242175
  · exact B2242179
  · exact B2242183
  · exact B2242187
  · exact B2242191
  · exact B2242195
  · exact B2242199
  · exact B2242203
  · exact B2242207
  · exact B2242211
  · exact B2242215
  · exact B2242219
  · exact B2242223
  · exact B2242227
  · exact B2242231
  · exact B2242235
  · exact B2242239
  · exact B2242243
  · exact B2242247
  · exact B2242251
  · exact B2242255
  · exact B2242259
  · exact B2242263
  · exact B2242267
  · exact B2242271
  · exact B2242275
  · exact B2242279
  · exact B2242283
  · exact B2242287
  · exact B2242291
  · exact B2242295
  · exact B2242299
  · exact B2242303
  · exact B2242307
  · exact B2242311
  · exact B2242315
  · exact B2242319
  · exact B2242323
  · exact B2242327
  · exact B2242331
  · exact B2242335
  · exact B2242339
  · exact B2242343
  · exact B2242347
  · exact B2242351
  · exact B2242355
  · exact B2242359
  · exact B2242363
  · exact B2242367
  · exact B2242371
  · exact B2242375
  · exact B2242379
  · exact B2242383
  · exact B2242387
  · exact B2242391
  · exact B2242395
  · exact B2242399
  · exact B2242403
  · exact B2242407
  · exact B2242411
  · exact B2242415
  · exact B2242419
  · exact B2242423
  · exact B2242427
  · exact B2242431
  · exact B2242435
  · exact B2242439
  · exact B2242443
  · exact B2242447
  · exact B2242451
  · exact B2242455
  · exact B2242459
  · exact B2242463
  · exact B2242467
  · exact B2242471
  · exact B2242475
  · exact B2242479
  · exact B2242483
  · exact B2242487
  · exact B2242491
  · exact B2242495
  · exact B2242499
  · exact B2242503
  · exact B2242507
  · exact B2242511
  · exact B2242515
  · exact B2242519
  · exact B2242523
  · exact B2242527
  · exact B2242531
  · exact B2242535
  · exact B2242539
  · exact B2242543
  · exact B2242547
  · exact B2242551
  · exact B2242555
  · exact B2242559
  · exact B2242563
  · exact B2242567
  · exact B2242571
  · exact B2242575
  · exact B2242579
  · exact B2242583
  · exact B2242587
  · exact B2242591
  · exact B2242595
  · exact B2242599
  · exact B2242603
  · exact B2242607
  · exact B2242611
  · exact B2242615
  · exact B2242619
  · exact B2242623
  · exact B2242627
  · exact B2242631
  · exact B2242635
  · exact B2242639
  · exact B2242643
  · exact B2242647
  · exact B2242651
  · exact B2242655
  · exact B2242659
  · exact B2242663
  · exact B2242667
  · exact B2242671
  · exact B2242675
  · exact B2242679
  · exact B2242683
  · exact B2242687
  · exact B2242691
  · exact B2242695
  · exact B2242699
  · exact B2242703
  · exact B2242707
  · exact B2242711
  · exact B2242715
  · exact B2242719
  · exact B2242723
  · exact B2242727
  · exact B2242731
  · exact B2242735
  · exact B2242739
  · exact B2242743
  · exact B2242747
  · exact B2242751
  · exact B2242755
  · exact B2242759
  · exact B2242763
  · exact B2242767
  · exact B2242771
  · exact B2242775
  · exact B2242779
  · exact B2242783
  · exact B2242787
  · exact B2242791
  · exact B2242795
  · exact B2242799
  · exact B2242803
  · exact B2242807
  · exact B2242811
  · exact B2242815
  · exact B2242819
  · exact B2242823
  · exact B2242827
  · exact B2242831
  · exact B2242835
  · exact B2242839
  · exact B2242843
  · exact B2242847
  · exact B2242851
  · exact B2242855
  · exact B2242859
  · exact B2242863
  · exact B2242867
  · exact B2242871
  · exact B2242875
  · exact B2242879
  · exact B2242883
  · exact B2242887
  · exact B2242891
  · exact B2242895
  · exact B2242899
  · exact B2242903
  · exact B2242907
  · exact B2242911
  · exact B2242915
  · exact B2242919
  · exact B2242923
  · exact B2242927
  · exact B2242931
  · exact B2242935
  · exact B2242939
  · exact B2242943
  · exact B2242947
  · exact B2242951
  · exact B2242955
  · exact B2242959
  · exact B2242963
  · exact B2242967
  · exact B2242971
  · exact B2242975
  · exact B2242979
  · exact B2242983
  · exact B2242987
  · exact B2242991
  · exact B2242995
  · exact B2242999
  · exact B2243003
  · exact B2243007
  · exact B2243011
  · exact B2243015
  · exact B2243019
  · exact B2243023
  · exact B2243027
  · exact B2243031
  · exact B2243035
  · exact B2243039
  · exact B2243043
  · exact B2243047
  · exact B2243051
  · exact B2243055
  · exact B2243059
  · exact B2243063
  · exact B2243067
  · exact B2243071
  · exact B2243075
  · exact B2243079
  · exact B2243083
  · exact B2243087
  · exact B2243091
  · exact B2243095
  · exact B2243099
  · exact B2243103
  · exact B2243107
  · exact B2243111
  · exact B2243115
  · exact B2243119
  · exact B2243123
  · exact B2243127
  · exact B2243131
  · exact B2243135
  · exact B2243139
  · exact B2243143
  · exact B2243147
  · exact B2243151
  · exact B2243155
  · exact B2243159
  · exact B2243163
  · exact B2243167
  · exact B2243171
  · exact B2243175
  · exact B2243179
  · exact B2243183
  · exact B2243187
  · exact B2243191
  · exact B2243195
  · exact B2243199
  · exact B2243203
  · exact B2243207
  · exact B2243211
  · exact B2243215
  · exact B2243219
  · exact B2243223
  · exact B2243227
  · exact B2243231
  · exact B2243235
  · exact B2243239
  · exact B2243243
  · exact B2243247
  · exact B2243251
  · exact B2243255
  · exact B2243259
  · exact B2243263
  · exact B2243267
  · exact B2243271
  · exact B2243275
  · exact B2243279
  · exact B2243283
  · exact B2243287
  · exact B2243291
  · exact B2243295
  · exact B2243299
  · exact B2243303
  · exact B2243307
  · exact B2243311
  · exact B2243315
  · exact B2243319
  · exact B2243323
  · exact B2243327
  · exact B2243331
  · exact B2243335
  · exact B2243339
  · exact B2243343
  · exact B2243347
  · exact B2243351
  · exact B2243355
  · exact B2243359
  · exact B2243363
  · exact B2243367
  · exact B2243371
  · exact B2243375
  · exact B2243379
  · exact B2243383
  · exact B2243387
  · exact B2243391
  · exact B2243395
  · exact B2243399
  · exact B2243403
  · exact B2243407
  · exact B2243411
  · exact B2243415
  · exact B2243419
  · exact B2243423
  · exact B2243427
  · exact B2243431
  · exact B2243435
theorem solution (m : ℕ) (hlo : 2241435 ≤ m) (hhi : m ≤ 2243435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 560358 ≤ j := by omega
    have hj2 : j ≤ 560858 := by omega
    have hb : Blo 2241435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
