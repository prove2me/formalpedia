-- Prove2me | solution 1 for syracuse_descends_range_2301435_2303435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:50:00.279269+00:00
-- url     : https://prove2.me/submissions/ae07216c-b725-4617-8372-247a73e4800f

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

theorem B4369133 : Blo 2301435 4369133 := bbase (se 3 (by rfl) ⟨819212, by rfl⟩ : syracuseStep 4369133 = 1638425) (by norm_num)
theorem B2912755 : Blo 2301435 2912755 := bstep (se 1 (by rfl) ⟨2184566, by rfl⟩ : syracuseStep 2912755 = 4369133) B4369133
theorem B3883673 : Blo 2301435 3883673 := bstep (se 2 (by rfl) ⟨1456377, by rfl⟩ : syracuseStep 3883673 = 2912755) B2912755
theorem B2589115 : Blo 2301435 2589115 := bstep (se 1 (by rfl) ⟨1941836, by rfl⟩ : syracuseStep 2589115 = 3883673) B3883673
theorem B3452153 : Blo 2301435 3452153 := bstep (se 2 (by rfl) ⟨1294557, by rfl⟩ : syracuseStep 3452153 = 2589115) B2589115
theorem B2301435 : Blo 2301435 2301435 := bstep (se 1 (by rfl) ⟨1726076, by rfl⟩ : syracuseStep 2301435 = 3452153) B3452153
theorem B5050325 : Blo 2301435 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B3366883 : Blo 2301435 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B4489177 : Blo 2301435 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B5985569 : Blo 2301435 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B3990379 : Blo 2301435 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B5320505 : Blo 2301435 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B3547003 : Blo 2301435 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B4729337 : Blo 2301435 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B3152891 : Blo 2301435 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B8407709 : Blo 2301435 8407709 := bstep (se 3 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 8407709 = 3152891) B3152891
theorem B5605139 : Blo 2301435 5605139 := bstep (se 1 (by rfl) ⟨4203854, by rfl⟩ : syracuseStep 5605139 = 8407709) B8407709
theorem B14947037 : Blo 2301435 14947037 := bstep (se 3 (by rfl) ⟨2802569, by rfl⟩ : syracuseStep 14947037 = 5605139) B5605139
theorem B9964691 : Blo 2301435 9964691 := bstep (se 1 (by rfl) ⟨7473518, by rfl⟩ : syracuseStep 9964691 = 14947037) B14947037
theorem B6643127 : Blo 2301435 6643127 := bstep (se 1 (by rfl) ⟨4982345, by rfl⟩ : syracuseStep 6643127 = 9964691) B9964691
theorem B4428751 : Blo 2301435 4428751 := bstep (se 1 (by rfl) ⟨3321563, by rfl⟩ : syracuseStep 4428751 = 6643127) B6643127
theorem B5905001 : Blo 2301435 5905001 := bstep (se 2 (by rfl) ⟨2214375, by rfl⟩ : syracuseStep 5905001 = 4428751) B4428751
theorem B3936667 : Blo 2301435 3936667 := bstep (se 1 (by rfl) ⟨2952500, by rfl⟩ : syracuseStep 3936667 = 5905001) B5905001
theorem B5248889 : Blo 2301435 5248889 := bstep (se 2 (by rfl) ⟨1968333, by rfl⟩ : syracuseStep 5248889 = 3936667) B3936667
theorem B3499259 : Blo 2301435 3499259 := bstep (se 1 (by rfl) ⟨2624444, by rfl⟩ : syracuseStep 3499259 = 5248889) B5248889
theorem B9331357 : Blo 2301435 9331357 := bstep (se 3 (by rfl) ⟨1749629, by rfl⟩ : syracuseStep 9331357 = 3499259) B3499259
theorem B12441809 : Blo 2301435 12441809 := bstep (se 2 (by rfl) ⟨4665678, by rfl⟩ : syracuseStep 12441809 = 9331357) B9331357
theorem B33178157 : Blo 2301435 33178157 := bstep (se 3 (by rfl) ⟨6220904, by rfl⟩ : syracuseStep 33178157 = 12441809) B12441809
theorem B22118771 : Blo 2301435 22118771 := bstep (se 1 (by rfl) ⟨16589078, by rfl⟩ : syracuseStep 22118771 = 33178157) B33178157
theorem B58983389 : Blo 2301435 58983389 := bstep (se 3 (by rfl) ⟨11059385, by rfl⟩ : syracuseStep 58983389 = 22118771) B22118771
theorem B39322259 : Blo 2301435 39322259 := bstep (se 1 (by rfl) ⟨29491694, by rfl⟩ : syracuseStep 39322259 = 58983389) B58983389
theorem B26214839 : Blo 2301435 26214839 := bstep (se 1 (by rfl) ⟨19661129, by rfl⟩ : syracuseStep 26214839 = 39322259) B39322259
theorem B17476559 : Blo 2301435 17476559 := bstep (se 1 (by rfl) ⟨13107419, by rfl⟩ : syracuseStep 17476559 = 26214839) B26214839
theorem B11651039 : Blo 2301435 11651039 := bstep (se 1 (by rfl) ⟨8738279, by rfl⟩ : syracuseStep 11651039 = 17476559) B17476559
theorem B7767359 : Blo 2301435 7767359 := bstep (se 1 (by rfl) ⟨5825519, by rfl⟩ : syracuseStep 7767359 = 11651039) B11651039
theorem B5178239 : Blo 2301435 5178239 := bstep (se 1 (by rfl) ⟨3883679, by rfl⟩ : syracuseStep 5178239 = 7767359) B7767359
theorem B3452159 : Blo 2301435 3452159 := bstep (se 1 (by rfl) ⟨2589119, by rfl⟩ : syracuseStep 3452159 = 5178239) B5178239
theorem B2301439 : Blo 2301435 2301439 := bstep (se 1 (by rfl) ⟨1726079, by rfl⟩ : syracuseStep 2301439 = 3452159) B3452159
theorem B3452165 : Blo 2301435 3452165 := bbase (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) (by norm_num)
theorem B2301443 : Blo 2301435 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B3883693 : Blo 2301435 3883693 := bbase (se 3 (by rfl) ⟨728192, by rfl⟩ : syracuseStep 3883693 = 1456385) (by norm_num)
theorem B5178257 : Blo 2301435 5178257 := bstep (se 2 (by rfl) ⟨1941846, by rfl⟩ : syracuseStep 5178257 = 3883693) B3883693
theorem B3452171 : Blo 2301435 3452171 := bstep (se 1 (by rfl) ⟨2589128, by rfl⟩ : syracuseStep 3452171 = 5178257) B5178257
theorem B2301447 : Blo 2301435 2301447 := bstep (se 1 (by rfl) ⟨1726085, by rfl⟩ : syracuseStep 2301447 = 3452171) B3452171
theorem B2589133 : Blo 2301435 2589133 := bbase (se 3 (by rfl) ⟨485462, by rfl⟩ : syracuseStep 2589133 = 970925) (by norm_num)
theorem B3452177 : Blo 2301435 3452177 := bstep (se 2 (by rfl) ⟨1294566, by rfl⟩ : syracuseStep 3452177 = 2589133) B2589133
theorem B2301451 : Blo 2301435 2301451 := bstep (se 1 (by rfl) ⟨1726088, by rfl⟩ : syracuseStep 2301451 = 3452177) B3452177
theorem B7767413 : Blo 2301435 7767413 := bbase (se 5 (by rfl) ⟨364097, by rfl⟩ : syracuseStep 7767413 = 728195) (by norm_num)
theorem B5178275 : Blo 2301435 5178275 := bstep (se 1 (by rfl) ⟨3883706, by rfl⟩ : syracuseStep 5178275 = 7767413) B7767413
theorem B3452183 : Blo 2301435 3452183 := bstep (se 1 (by rfl) ⟨2589137, by rfl⟩ : syracuseStep 3452183 = 5178275) B5178275
theorem B2301455 : Blo 2301435 2301455 := bstep (se 1 (by rfl) ⟨1726091, by rfl⟩ : syracuseStep 2301455 = 3452183) B3452183
theorem B3452189 : Blo 2301435 3452189 := bbase (se 3 (by rfl) ⟨647285, by rfl⟩ : syracuseStep 3452189 = 1294571) (by norm_num)
theorem B2301459 : Blo 2301435 2301459 := bstep (se 1 (by rfl) ⟨1726094, by rfl⟩ : syracuseStep 2301459 = 3452189) B3452189
theorem B5178293 : Blo 2301435 5178293 := bbase (se 5 (by rfl) ⟨242732, by rfl⟩ : syracuseStep 5178293 = 485465) (by norm_num)
theorem B3452195 : Blo 2301435 3452195 := bstep (se 1 (by rfl) ⟨2589146, by rfl⟩ : syracuseStep 3452195 = 5178293) B5178293
theorem B2301463 : Blo 2301435 2301463 := bstep (se 1 (by rfl) ⟨1726097, by rfl⟩ : syracuseStep 2301463 = 3452195) B3452195
theorem B3321605 : Blo 2301435 3321605 := bbase (se 4 (by rfl) ⟨311400, by rfl⟩ : syracuseStep 3321605 = 622801) (by norm_num)
theorem B8857613 : Blo 2301435 8857613 := bstep (se 3 (by rfl) ⟨1660802, by rfl⟩ : syracuseStep 8857613 = 3321605) B3321605
theorem B5905075 : Blo 2301435 5905075 := bstep (se 1 (by rfl) ⟨4428806, by rfl⟩ : syracuseStep 5905075 = 8857613) B8857613
theorem B7873433 : Blo 2301435 7873433 := bstep (se 2 (by rfl) ⟨2952537, by rfl⟩ : syracuseStep 7873433 = 5905075) B5905075
theorem B5248955 : Blo 2301435 5248955 := bstep (se 1 (by rfl) ⟨3936716, by rfl⟩ : syracuseStep 5248955 = 7873433) B7873433
theorem B3499303 : Blo 2301435 3499303 := bstep (se 1 (by rfl) ⟨2624477, by rfl⟩ : syracuseStep 3499303 = 5248955) B5248955
theorem B4665737 : Blo 2301435 4665737 := bstep (se 2 (by rfl) ⟨1749651, by rfl⟩ : syracuseStep 4665737 = 3499303) B3499303
theorem B3110491 : Blo 2301435 3110491 := bstep (se 1 (by rfl) ⟨2332868, by rfl⟩ : syracuseStep 3110491 = 4665737) B4665737
theorem B16589285 : Blo 2301435 16589285 := bstep (se 4 (by rfl) ⟨1555245, by rfl⟩ : syracuseStep 16589285 = 3110491) B3110491
theorem B11059523 : Blo 2301435 11059523 := bstep (se 1 (by rfl) ⟨8294642, by rfl⟩ : syracuseStep 11059523 = 16589285) B16589285
theorem B7373015 : Blo 2301435 7373015 := bstep (se 1 (by rfl) ⟨5529761, by rfl⟩ : syracuseStep 7373015 = 11059523) B11059523
theorem B4915343 : Blo 2301435 4915343 := bstep (se 1 (by rfl) ⟨3686507, by rfl⟩ : syracuseStep 4915343 = 7373015) B7373015
theorem B13107581 : Blo 2301435 13107581 := bstep (se 3 (by rfl) ⟨2457671, by rfl⟩ : syracuseStep 13107581 = 4915343) B4915343
theorem B8738387 : Blo 2301435 8738387 := bstep (se 1 (by rfl) ⟨6553790, by rfl⟩ : syracuseStep 8738387 = 13107581) B13107581
theorem B5825591 : Blo 2301435 5825591 := bstep (se 1 (by rfl) ⟨4369193, by rfl⟩ : syracuseStep 5825591 = 8738387) B8738387
theorem B3883727 : Blo 2301435 3883727 := bstep (se 1 (by rfl) ⟨2912795, by rfl⟩ : syracuseStep 3883727 = 5825591) B5825591
theorem B2589151 : Blo 2301435 2589151 := bstep (se 1 (by rfl) ⟨1941863, by rfl⟩ : syracuseStep 2589151 = 3883727) B3883727
theorem B3452201 : Blo 2301435 3452201 := bstep (se 2 (by rfl) ⟨1294575, by rfl⟩ : syracuseStep 3452201 = 2589151) B2589151
theorem B2301467 : Blo 2301435 2301467 := bstep (se 1 (by rfl) ⟨1726100, by rfl⟩ : syracuseStep 2301467 = 3452201) B3452201
theorem B11059541 : Blo 2301435 11059541 := bbase (se 10 (by rfl) ⟨16200, by rfl⟩ : syracuseStep 11059541 = 32401) (by norm_num)
theorem B7373027 : Blo 2301435 7373027 := bstep (se 1 (by rfl) ⟨5529770, by rfl⟩ : syracuseStep 7373027 = 11059541) B11059541
theorem B4915351 : Blo 2301435 4915351 := bstep (se 1 (by rfl) ⟨3686513, by rfl⟩ : syracuseStep 4915351 = 7373027) B7373027
theorem B6553801 : Blo 2301435 6553801 := bstep (se 2 (by rfl) ⟨2457675, by rfl⟩ : syracuseStep 6553801 = 4915351) B4915351
theorem B8738401 : Blo 2301435 8738401 := bstep (se 2 (by rfl) ⟨3276900, by rfl⟩ : syracuseStep 8738401 = 6553801) B6553801
theorem B11651201 : Blo 2301435 11651201 := bstep (se 2 (by rfl) ⟨4369200, by rfl⟩ : syracuseStep 11651201 = 8738401) B8738401
theorem B7767467 : Blo 2301435 7767467 := bstep (se 1 (by rfl) ⟨5825600, by rfl⟩ : syracuseStep 7767467 = 11651201) B11651201
theorem B5178311 : Blo 2301435 5178311 := bstep (se 1 (by rfl) ⟨3883733, by rfl⟩ : syracuseStep 5178311 = 7767467) B7767467
theorem B3452207 : Blo 2301435 3452207 := bstep (se 1 (by rfl) ⟨2589155, by rfl⟩ : syracuseStep 3452207 = 5178311) B5178311
theorem B2301471 : Blo 2301435 2301471 := bstep (se 1 (by rfl) ⟨1726103, by rfl⟩ : syracuseStep 2301471 = 3452207) B3452207
theorem B3452213 : Blo 2301435 3452213 := bbase (se 5 (by rfl) ⟨161822, by rfl⟩ : syracuseStep 3452213 = 323645) (by norm_num)
theorem B2301475 : Blo 2301435 2301475 := bstep (se 1 (by rfl) ⟨1726106, by rfl⟩ : syracuseStep 2301475 = 3452213) B3452213
theorem B5825621 : Blo 2301435 5825621 := bbase (se 8 (by rfl) ⟨34134, by rfl⟩ : syracuseStep 5825621 = 68269) (by norm_num)
theorem B3883747 : Blo 2301435 3883747 := bstep (se 1 (by rfl) ⟨2912810, by rfl⟩ : syracuseStep 3883747 = 5825621) B5825621
theorem B5178329 : Blo 2301435 5178329 := bstep (se 2 (by rfl) ⟨1941873, by rfl⟩ : syracuseStep 5178329 = 3883747) B3883747
theorem B3452219 : Blo 2301435 3452219 := bstep (se 1 (by rfl) ⟨2589164, by rfl⟩ : syracuseStep 3452219 = 5178329) B5178329
theorem B2301479 : Blo 2301435 2301479 := bstep (se 1 (by rfl) ⟨1726109, by rfl⟩ : syracuseStep 2301479 = 3452219) B3452219
theorem B2589169 : Blo 2301435 2589169 := bbase (se 2 (by rfl) ⟨970938, by rfl⟩ : syracuseStep 2589169 = 1941877) (by norm_num)
theorem B3452225 : Blo 2301435 3452225 := bstep (se 2 (by rfl) ⟨1294584, by rfl⟩ : syracuseStep 3452225 = 2589169) B2589169
theorem B2301483 : Blo 2301435 2301483 := bstep (se 1 (by rfl) ⟨1726112, by rfl⟩ : syracuseStep 2301483 = 3452225) B3452225
theorem B4147357 : Blo 2301435 4147357 := bbase (se 3 (by rfl) ⟨777629, by rfl⟩ : syracuseStep 4147357 = 1555259) (by norm_num)
theorem B5529809 : Blo 2301435 5529809 := bstep (se 2 (by rfl) ⟨2073678, by rfl⟩ : syracuseStep 5529809 = 4147357) B4147357
theorem B14746157 : Blo 2301435 14746157 := bstep (se 3 (by rfl) ⟨2764904, by rfl⟩ : syracuseStep 14746157 = 5529809) B5529809
theorem B9830771 : Blo 2301435 9830771 := bstep (se 1 (by rfl) ⟨7373078, by rfl⟩ : syracuseStep 9830771 = 14746157) B14746157
theorem B6553847 : Blo 2301435 6553847 := bstep (se 1 (by rfl) ⟨4915385, by rfl⟩ : syracuseStep 6553847 = 9830771) B9830771
theorem B4369231 : Blo 2301435 4369231 := bstep (se 1 (by rfl) ⟨3276923, by rfl⟩ : syracuseStep 4369231 = 6553847) B6553847
theorem B5825641 : Blo 2301435 5825641 := bstep (se 2 (by rfl) ⟨2184615, by rfl⟩ : syracuseStep 5825641 = 4369231) B4369231
theorem B7767521 : Blo 2301435 7767521 := bstep (se 2 (by rfl) ⟨2912820, by rfl⟩ : syracuseStep 7767521 = 5825641) B5825641
theorem B5178347 : Blo 2301435 5178347 := bstep (se 1 (by rfl) ⟨3883760, by rfl⟩ : syracuseStep 5178347 = 7767521) B7767521
theorem B3452231 : Blo 2301435 3452231 := bstep (se 1 (by rfl) ⟨2589173, by rfl⟩ : syracuseStep 3452231 = 5178347) B5178347
theorem B2301487 : Blo 2301435 2301487 := bstep (se 1 (by rfl) ⟨1726115, by rfl⟩ : syracuseStep 2301487 = 3452231) B3452231
theorem B3452237 : Blo 2301435 3452237 := bbase (se 3 (by rfl) ⟨647294, by rfl⟩ : syracuseStep 3452237 = 1294589) (by norm_num)
theorem B2301491 : Blo 2301435 2301491 := bstep (se 1 (by rfl) ⟨1726118, by rfl⟩ : syracuseStep 2301491 = 3452237) B3452237
theorem B5178365 : Blo 2301435 5178365 := bbase (se 3 (by rfl) ⟨970943, by rfl⟩ : syracuseStep 5178365 = 1941887) (by norm_num)
theorem B3452243 : Blo 2301435 3452243 := bstep (se 1 (by rfl) ⟨2589182, by rfl⟩ : syracuseStep 3452243 = 5178365) B5178365
theorem B2301495 : Blo 2301435 2301495 := bstep (se 1 (by rfl) ⟨1726121, by rfl⟩ : syracuseStep 2301495 = 3452243) B3452243
theorem B3883781 : Blo 2301435 3883781 := bbase (se 4 (by rfl) ⟨364104, by rfl⟩ : syracuseStep 3883781 = 728209) (by norm_num)
theorem B2589187 : Blo 2301435 2589187 := bstep (se 1 (by rfl) ⟨1941890, by rfl⟩ : syracuseStep 2589187 = 3883781) B3883781
theorem B3452249 : Blo 2301435 3452249 := bstep (se 2 (by rfl) ⟨1294593, by rfl⟩ : syracuseStep 3452249 = 2589187) B2589187
theorem B2301499 : Blo 2301435 2301499 := bstep (se 1 (by rfl) ⟨1726124, by rfl⟩ : syracuseStep 2301499 = 3452249) B3452249
theorem B17477045 : Blo 2301435 17477045 := bbase (se 5 (by rfl) ⟨819236, by rfl⟩ : syracuseStep 17477045 = 1638473) (by norm_num)
theorem B11651363 : Blo 2301435 11651363 := bstep (se 1 (by rfl) ⟨8738522, by rfl⟩ : syracuseStep 11651363 = 17477045) B17477045
theorem B7767575 : Blo 2301435 7767575 := bstep (se 1 (by rfl) ⟨5825681, by rfl⟩ : syracuseStep 7767575 = 11651363) B11651363
theorem B5178383 : Blo 2301435 5178383 := bstep (se 1 (by rfl) ⟨3883787, by rfl⟩ : syracuseStep 5178383 = 7767575) B7767575
theorem B3452255 : Blo 2301435 3452255 := bstep (se 1 (by rfl) ⟨2589191, by rfl⟩ : syracuseStep 3452255 = 5178383) B5178383
theorem B2301503 : Blo 2301435 2301503 := bstep (se 1 (by rfl) ⟨1726127, by rfl⟩ : syracuseStep 2301503 = 3452255) B3452255
theorem B3452261 : Blo 2301435 3452261 := bbase (se 4 (by rfl) ⟨323649, by rfl⟩ : syracuseStep 3452261 = 647299) (by norm_num)
theorem B2301507 : Blo 2301435 2301507 := bstep (se 1 (by rfl) ⟨1726130, by rfl⟩ : syracuseStep 2301507 = 3452261) B3452261
theorem B4369277 : Blo 2301435 4369277 := bbase (se 3 (by rfl) ⟨819239, by rfl⟩ : syracuseStep 4369277 = 1638479) (by norm_num)
theorem B2912851 : Blo 2301435 2912851 := bstep (se 1 (by rfl) ⟨2184638, by rfl⟩ : syracuseStep 2912851 = 4369277) B4369277
theorem B3883801 : Blo 2301435 3883801 := bstep (se 2 (by rfl) ⟨1456425, by rfl⟩ : syracuseStep 3883801 = 2912851) B2912851
theorem B5178401 : Blo 2301435 5178401 := bstep (se 2 (by rfl) ⟨1941900, by rfl⟩ : syracuseStep 5178401 = 3883801) B3883801
theorem B3452267 : Blo 2301435 3452267 := bstep (se 1 (by rfl) ⟨2589200, by rfl⟩ : syracuseStep 3452267 = 5178401) B5178401
theorem B2301511 : Blo 2301435 2301511 := bstep (se 1 (by rfl) ⟨1726133, by rfl⟩ : syracuseStep 2301511 = 3452267) B3452267
theorem B2589205 : Blo 2301435 2589205 := bbase (se 6 (by rfl) ⟨60684, by rfl⟩ : syracuseStep 2589205 = 121369) (by norm_num)
theorem B3452273 : Blo 2301435 3452273 := bstep (se 2 (by rfl) ⟨1294602, by rfl⟩ : syracuseStep 3452273 = 2589205) B2589205
theorem B2301515 : Blo 2301435 2301515 := bstep (se 1 (by rfl) ⟨1726136, by rfl⟩ : syracuseStep 2301515 = 3452273) B3452273
theorem B2912861 : Blo 2301435 2912861 := bbase (se 3 (by rfl) ⟨546161, by rfl⟩ : syracuseStep 2912861 = 1092323) (by norm_num)
theorem B7767629 : Blo 2301435 7767629 := bstep (se 3 (by rfl) ⟨1456430, by rfl⟩ : syracuseStep 7767629 = 2912861) B2912861
theorem B5178419 : Blo 2301435 5178419 := bstep (se 1 (by rfl) ⟨3883814, by rfl⟩ : syracuseStep 5178419 = 7767629) B7767629
theorem B3452279 : Blo 2301435 3452279 := bstep (se 1 (by rfl) ⟨2589209, by rfl⟩ : syracuseStep 3452279 = 5178419) B5178419
theorem B2301519 : Blo 2301435 2301519 := bstep (se 1 (by rfl) ⟨1726139, by rfl⟩ : syracuseStep 2301519 = 3452279) B3452279
theorem B3452285 : Blo 2301435 3452285 := bbase (se 3 (by rfl) ⟨647303, by rfl⟩ : syracuseStep 3452285 = 1294607) (by norm_num)
theorem B2301523 : Blo 2301435 2301523 := bstep (se 1 (by rfl) ⟨1726142, by rfl⟩ : syracuseStep 2301523 = 3452285) B3452285
theorem B5178437 : Blo 2301435 5178437 := bbase (se 4 (by rfl) ⟨485478, by rfl⟩ : syracuseStep 5178437 = 970957) (by norm_num)
theorem B3452291 : Blo 2301435 3452291 := bstep (se 1 (by rfl) ⟨2589218, by rfl⟩ : syracuseStep 3452291 = 5178437) B5178437
theorem B2301527 : Blo 2301435 2301527 := bstep (se 1 (by rfl) ⟨1726145, by rfl⟩ : syracuseStep 2301527 = 3452291) B3452291
theorem B6553973 : Blo 2301435 6553973 := bbase (se 5 (by rfl) ⟨307217, by rfl⟩ : syracuseStep 6553973 = 614435) (by norm_num)
theorem B4369315 : Blo 2301435 4369315 := bstep (se 1 (by rfl) ⟨3276986, by rfl⟩ : syracuseStep 4369315 = 6553973) B6553973
theorem B5825753 : Blo 2301435 5825753 := bstep (se 2 (by rfl) ⟨2184657, by rfl⟩ : syracuseStep 5825753 = 4369315) B4369315
theorem B3883835 : Blo 2301435 3883835 := bstep (se 1 (by rfl) ⟨2912876, by rfl⟩ : syracuseStep 3883835 = 5825753) B5825753
theorem B2589223 : Blo 2301435 2589223 := bstep (se 1 (by rfl) ⟨1941917, by rfl⟩ : syracuseStep 2589223 = 3883835) B3883835
theorem B3452297 : Blo 2301435 3452297 := bstep (se 2 (by rfl) ⟨1294611, by rfl⟩ : syracuseStep 3452297 = 2589223) B2589223
theorem B2301531 : Blo 2301435 2301531 := bstep (se 1 (by rfl) ⟨1726148, by rfl⟩ : syracuseStep 2301531 = 3452297) B3452297
theorem B11651525 : Blo 2301435 11651525 := bbase (se 4 (by rfl) ⟨1092330, by rfl⟩ : syracuseStep 11651525 = 2184661) (by norm_num)
theorem B7767683 : Blo 2301435 7767683 := bstep (se 1 (by rfl) ⟨5825762, by rfl⟩ : syracuseStep 7767683 = 11651525) B11651525
theorem B5178455 : Blo 2301435 5178455 := bstep (se 1 (by rfl) ⟨3883841, by rfl⟩ : syracuseStep 5178455 = 7767683) B7767683
theorem B3452303 : Blo 2301435 3452303 := bstep (se 1 (by rfl) ⟨2589227, by rfl⟩ : syracuseStep 3452303 = 5178455) B5178455
theorem B2301535 : Blo 2301435 2301535 := bstep (se 1 (by rfl) ⟨1726151, by rfl⟩ : syracuseStep 2301535 = 3452303) B3452303
theorem B3452309 : Blo 2301435 3452309 := bbase (se 6 (by rfl) ⟨80913, by rfl⟩ : syracuseStep 3452309 = 161827) (by norm_num)
theorem B2301539 : Blo 2301435 2301539 := bstep (se 1 (by rfl) ⟨1726154, by rfl⟩ : syracuseStep 2301539 = 3452309) B3452309
theorem B3686629 : Blo 2301435 3686629 := bbase (se 4 (by rfl) ⟨345621, by rfl⟩ : syracuseStep 3686629 = 691243) (by norm_num)
theorem B4915505 : Blo 2301435 4915505 := bstep (se 2 (by rfl) ⟨1843314, by rfl⟩ : syracuseStep 4915505 = 3686629) B3686629
theorem B13108013 : Blo 2301435 13108013 := bstep (se 3 (by rfl) ⟨2457752, by rfl⟩ : syracuseStep 13108013 = 4915505) B4915505
theorem B8738675 : Blo 2301435 8738675 := bstep (se 1 (by rfl) ⟨6554006, by rfl⟩ : syracuseStep 8738675 = 13108013) B13108013
theorem B5825783 : Blo 2301435 5825783 := bstep (se 1 (by rfl) ⟨4369337, by rfl⟩ : syracuseStep 5825783 = 8738675) B8738675
theorem B3883855 : Blo 2301435 3883855 := bstep (se 1 (by rfl) ⟨2912891, by rfl⟩ : syracuseStep 3883855 = 5825783) B5825783
theorem B5178473 : Blo 2301435 5178473 := bstep (se 2 (by rfl) ⟨1941927, by rfl⟩ : syracuseStep 5178473 = 3883855) B3883855
theorem B3452315 : Blo 2301435 3452315 := bstep (se 1 (by rfl) ⟨2589236, by rfl⟩ : syracuseStep 3452315 = 5178473) B5178473
theorem B2301543 : Blo 2301435 2301543 := bstep (se 1 (by rfl) ⟨1726157, by rfl⟩ : syracuseStep 2301543 = 3452315) B3452315
theorem B2589241 : Blo 2301435 2589241 := bbase (se 2 (by rfl) ⟨970965, by rfl⟩ : syracuseStep 2589241 = 1941931) (by norm_num)
theorem B3452321 : Blo 2301435 3452321 := bstep (se 2 (by rfl) ⟨1294620, by rfl⟩ : syracuseStep 3452321 = 2589241) B2589241
theorem B2301547 : Blo 2301435 2301547 := bstep (se 1 (by rfl) ⟨1726160, by rfl⟩ : syracuseStep 2301547 = 3452321) B3452321
theorem B2457761 : Blo 2301435 2457761 := bbase (se 2 (by rfl) ⟨921660, by rfl⟩ : syracuseStep 2457761 = 1843321) (by norm_num)
theorem B6554029 : Blo 2301435 6554029 := bstep (se 3 (by rfl) ⟨1228880, by rfl⟩ : syracuseStep 6554029 = 2457761) B2457761
theorem B8738705 : Blo 2301435 8738705 := bstep (se 2 (by rfl) ⟨3277014, by rfl⟩ : syracuseStep 8738705 = 6554029) B6554029
theorem B5825803 : Blo 2301435 5825803 := bstep (se 1 (by rfl) ⟨4369352, by rfl⟩ : syracuseStep 5825803 = 8738705) B8738705
theorem B7767737 : Blo 2301435 7767737 := bstep (se 2 (by rfl) ⟨2912901, by rfl⟩ : syracuseStep 7767737 = 5825803) B5825803
theorem B5178491 : Blo 2301435 5178491 := bstep (se 1 (by rfl) ⟨3883868, by rfl⟩ : syracuseStep 5178491 = 7767737) B7767737
theorem B3452327 : Blo 2301435 3452327 := bstep (se 1 (by rfl) ⟨2589245, by rfl⟩ : syracuseStep 3452327 = 5178491) B5178491
theorem B2301551 : Blo 2301435 2301551 := bstep (se 1 (by rfl) ⟨1726163, by rfl⟩ : syracuseStep 2301551 = 3452327) B3452327
theorem B3452333 : Blo 2301435 3452333 := bbase (se 3 (by rfl) ⟨647312, by rfl⟩ : syracuseStep 3452333 = 1294625) (by norm_num)
theorem B2301555 : Blo 2301435 2301555 := bstep (se 1 (by rfl) ⟨1726166, by rfl⟩ : syracuseStep 2301555 = 3452333) B3452333
theorem B5178509 : Blo 2301435 5178509 := bbase (se 3 (by rfl) ⟨970970, by rfl⟩ : syracuseStep 5178509 = 1941941) (by norm_num)
theorem B3452339 : Blo 2301435 3452339 := bstep (se 1 (by rfl) ⟨2589254, by rfl⟩ : syracuseStep 3452339 = 5178509) B5178509
theorem B2301559 : Blo 2301435 2301559 := bstep (se 1 (by rfl) ⟨1726169, by rfl⟩ : syracuseStep 2301559 = 3452339) B3452339
theorem B2912917 : Blo 2301435 2912917 := bbase (se 6 (by rfl) ⟨68271, by rfl⟩ : syracuseStep 2912917 = 136543) (by norm_num)
theorem B3883889 : Blo 2301435 3883889 := bstep (se 2 (by rfl) ⟨1456458, by rfl⟩ : syracuseStep 3883889 = 2912917) B2912917
theorem B2589259 : Blo 2301435 2589259 := bstep (se 1 (by rfl) ⟨1941944, by rfl⟩ : syracuseStep 2589259 = 3883889) B3883889
theorem B3452345 : Blo 2301435 3452345 := bstep (se 2 (by rfl) ⟨1294629, by rfl⟩ : syracuseStep 3452345 = 2589259) B2589259
theorem B2301563 : Blo 2301435 2301563 := bstep (se 1 (by rfl) ⟨1726172, by rfl⟩ : syracuseStep 2301563 = 3452345) B3452345
theorem B2332969 : Blo 2301435 2332969 := bbase (se 2 (by rfl) ⟨874863, by rfl⟩ : syracuseStep 2332969 = 1749727) (by norm_num)
theorem B12442501 : Blo 2301435 12442501 := bstep (se 4 (by rfl) ⟨1166484, by rfl⟩ : syracuseStep 12442501 = 2332969) B2332969
theorem B66360005 : Blo 2301435 66360005 := bstep (se 4 (by rfl) ⟨6221250, by rfl⟩ : syracuseStep 66360005 = 12442501) B12442501
theorem B44240003 : Blo 2301435 44240003 := bstep (se 1 (by rfl) ⟨33180002, by rfl⟩ : syracuseStep 44240003 = 66360005) B66360005
theorem B29493335 : Blo 2301435 29493335 := bstep (se 1 (by rfl) ⟨22120001, by rfl⟩ : syracuseStep 29493335 = 44240003) B44240003
theorem B19662223 : Blo 2301435 19662223 := bstep (se 1 (by rfl) ⟨14746667, by rfl⟩ : syracuseStep 19662223 = 29493335) B29493335
theorem B26216297 : Blo 2301435 26216297 := bstep (se 2 (by rfl) ⟨9831111, by rfl⟩ : syracuseStep 26216297 = 19662223) B19662223
theorem B17477531 : Blo 2301435 17477531 := bstep (se 1 (by rfl) ⟨13108148, by rfl⟩ : syracuseStep 17477531 = 26216297) B26216297
theorem B11651687 : Blo 2301435 11651687 := bstep (se 1 (by rfl) ⟨8738765, by rfl⟩ : syracuseStep 11651687 = 17477531) B17477531
theorem B7767791 : Blo 2301435 7767791 := bstep (se 1 (by rfl) ⟨5825843, by rfl⟩ : syracuseStep 7767791 = 11651687) B11651687
theorem B5178527 : Blo 2301435 5178527 := bstep (se 1 (by rfl) ⟨3883895, by rfl⟩ : syracuseStep 5178527 = 7767791) B7767791
theorem B3452351 : Blo 2301435 3452351 := bstep (se 1 (by rfl) ⟨2589263, by rfl⟩ : syracuseStep 3452351 = 5178527) B5178527
theorem B2301567 : Blo 2301435 2301567 := bstep (se 1 (by rfl) ⟨1726175, by rfl⟩ : syracuseStep 2301567 = 3452351) B3452351
theorem B3452357 : Blo 2301435 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B2301571 : Blo 2301435 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B3883909 : Blo 2301435 3883909 := bbase (se 4 (by rfl) ⟨364116, by rfl⟩ : syracuseStep 3883909 = 728233) (by norm_num)
theorem B5178545 : Blo 2301435 5178545 := bstep (se 2 (by rfl) ⟨1941954, by rfl⟩ : syracuseStep 5178545 = 3883909) B3883909
theorem B3452363 : Blo 2301435 3452363 := bstep (se 1 (by rfl) ⟨2589272, by rfl⟩ : syracuseStep 3452363 = 5178545) B5178545
theorem B2301575 : Blo 2301435 2301575 := bstep (se 1 (by rfl) ⟨1726181, by rfl⟩ : syracuseStep 2301575 = 3452363) B3452363
theorem B2589277 : Blo 2301435 2589277 := bbase (se 3 (by rfl) ⟨485489, by rfl⟩ : syracuseStep 2589277 = 970979) (by norm_num)
theorem B3452369 : Blo 2301435 3452369 := bstep (se 2 (by rfl) ⟨1294638, by rfl⟩ : syracuseStep 3452369 = 2589277) B2589277
theorem B2301579 : Blo 2301435 2301579 := bstep (se 1 (by rfl) ⟨1726184, by rfl⟩ : syracuseStep 2301579 = 3452369) B3452369
theorem B7767845 : Blo 2301435 7767845 := bbase (se 4 (by rfl) ⟨728235, by rfl⟩ : syracuseStep 7767845 = 1456471) (by norm_num)
theorem B5178563 : Blo 2301435 5178563 := bstep (se 1 (by rfl) ⟨3883922, by rfl⟩ : syracuseStep 5178563 = 7767845) B7767845
theorem B3452375 : Blo 2301435 3452375 := bstep (se 1 (by rfl) ⟨2589281, by rfl⟩ : syracuseStep 3452375 = 5178563) B5178563
theorem B2301583 : Blo 2301435 2301583 := bstep (se 1 (by rfl) ⟨1726187, by rfl⟩ : syracuseStep 2301583 = 3452375) B3452375
theorem B3452381 : Blo 2301435 3452381 := bbase (se 3 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 3452381 = 1294643) (by norm_num)
theorem B2301587 : Blo 2301435 2301587 := bstep (se 1 (by rfl) ⟨1726190, by rfl⟩ : syracuseStep 2301587 = 3452381) B3452381
theorem B5178581 : Blo 2301435 5178581 := bbase (se 7 (by rfl) ⟨60686, by rfl⟩ : syracuseStep 5178581 = 121373) (by norm_num)
theorem B3452387 : Blo 2301435 3452387 := bstep (se 1 (by rfl) ⟨2589290, by rfl⟩ : syracuseStep 3452387 = 5178581) B5178581
theorem B2301591 : Blo 2301435 2301591 := bstep (se 1 (by rfl) ⟨1726193, by rfl⟩ : syracuseStep 2301591 = 3452387) B3452387
theorem B5530069 : Blo 2301435 5530069 := bbase (se 7 (by rfl) ⟨64805, by rfl⟩ : syracuseStep 5530069 = 129611) (by norm_num)
theorem B7373425 : Blo 2301435 7373425 := bstep (se 2 (by rfl) ⟨2765034, by rfl⟩ : syracuseStep 7373425 = 5530069) B5530069
theorem B9831233 : Blo 2301435 9831233 := bstep (se 2 (by rfl) ⟨3686712, by rfl⟩ : syracuseStep 9831233 = 7373425) B7373425
theorem B6554155 : Blo 2301435 6554155 := bstep (se 1 (by rfl) ⟨4915616, by rfl⟩ : syracuseStep 6554155 = 9831233) B9831233
theorem B8738873 : Blo 2301435 8738873 := bstep (se 2 (by rfl) ⟨3277077, by rfl⟩ : syracuseStep 8738873 = 6554155) B6554155
theorem B5825915 : Blo 2301435 5825915 := bstep (se 1 (by rfl) ⟨4369436, by rfl⟩ : syracuseStep 5825915 = 8738873) B8738873
theorem B3883943 : Blo 2301435 3883943 := bstep (se 1 (by rfl) ⟨2912957, by rfl⟩ : syracuseStep 3883943 = 5825915) B5825915
theorem B2589295 : Blo 2301435 2589295 := bstep (se 1 (by rfl) ⟨1941971, by rfl⟩ : syracuseStep 2589295 = 3883943) B3883943
theorem B3452393 : Blo 2301435 3452393 := bstep (se 2 (by rfl) ⟨1294647, by rfl⟩ : syracuseStep 3452393 = 2589295) B2589295
theorem B2301595 : Blo 2301435 2301595 := bstep (se 1 (by rfl) ⟨1726196, by rfl⟩ : syracuseStep 2301595 = 3452393) B3452393
theorem B3936941 : Blo 2301435 3936941 := bbase (se 3 (by rfl) ⟨738176, by rfl⟩ : syracuseStep 3936941 = 1476353) (by norm_num)
theorem B2624627 : Blo 2301435 2624627 := bstep (se 1 (by rfl) ⟨1968470, by rfl⟩ : syracuseStep 2624627 = 3936941) B3936941
theorem B6999005 : Blo 2301435 6999005 := bstep (se 3 (by rfl) ⟨1312313, by rfl⟩ : syracuseStep 6999005 = 2624627) B2624627
theorem B18664013 : Blo 2301435 18664013 := bstep (se 3 (by rfl) ⟨3499502, by rfl⟩ : syracuseStep 18664013 = 6999005) B6999005
theorem B12442675 : Blo 2301435 12442675 := bstep (se 1 (by rfl) ⟨9332006, by rfl⟩ : syracuseStep 12442675 = 18664013) B18664013
theorem B16590233 : Blo 2301435 16590233 := bstep (se 2 (by rfl) ⟨6221337, by rfl⟩ : syracuseStep 16590233 = 12442675) B12442675
theorem B11060155 : Blo 2301435 11060155 := bstep (se 1 (by rfl) ⟨8295116, by rfl⟩ : syracuseStep 11060155 = 16590233) B16590233
theorem B14746873 : Blo 2301435 14746873 := bstep (se 2 (by rfl) ⟨5530077, by rfl⟩ : syracuseStep 14746873 = 11060155) B11060155
theorem B19662497 : Blo 2301435 19662497 := bstep (se 2 (by rfl) ⟨7373436, by rfl⟩ : syracuseStep 19662497 = 14746873) B14746873
theorem B13108331 : Blo 2301435 13108331 := bstep (se 1 (by rfl) ⟨9831248, by rfl⟩ : syracuseStep 13108331 = 19662497) B19662497
theorem B8738887 : Blo 2301435 8738887 := bstep (se 1 (by rfl) ⟨6554165, by rfl⟩ : syracuseStep 8738887 = 13108331) B13108331
theorem B11651849 : Blo 2301435 11651849 := bstep (se 2 (by rfl) ⟨4369443, by rfl⟩ : syracuseStep 11651849 = 8738887) B8738887
theorem B7767899 : Blo 2301435 7767899 := bstep (se 1 (by rfl) ⟨5825924, by rfl⟩ : syracuseStep 7767899 = 11651849) B11651849
theorem B5178599 : Blo 2301435 5178599 := bstep (se 1 (by rfl) ⟨3883949, by rfl⟩ : syracuseStep 5178599 = 7767899) B7767899
theorem B3452399 : Blo 2301435 3452399 := bstep (se 1 (by rfl) ⟨2589299, by rfl⟩ : syracuseStep 3452399 = 5178599) B5178599
theorem B2301599 : Blo 2301435 2301599 := bstep (se 1 (by rfl) ⟨1726199, by rfl⟩ : syracuseStep 2301599 = 3452399) B3452399
theorem B3452405 : Blo 2301435 3452405 := bbase (se 5 (by rfl) ⟨161831, by rfl⟩ : syracuseStep 3452405 = 323663) (by norm_num)
theorem B2301603 : Blo 2301435 2301603 := bstep (se 1 (by rfl) ⟨1726202, by rfl⟩ : syracuseStep 2301603 = 3452405) B3452405
theorem B2457821 : Blo 2301435 2457821 := bbase (se 3 (by rfl) ⟨460841, by rfl⟩ : syracuseStep 2457821 = 921683) (by norm_num)
theorem B6554189 : Blo 2301435 6554189 := bstep (se 3 (by rfl) ⟨1228910, by rfl⟩ : syracuseStep 6554189 = 2457821) B2457821
theorem B4369459 : Blo 2301435 4369459 := bstep (se 1 (by rfl) ⟨3277094, by rfl⟩ : syracuseStep 4369459 = 6554189) B6554189
theorem B5825945 : Blo 2301435 5825945 := bstep (se 2 (by rfl) ⟨2184729, by rfl⟩ : syracuseStep 5825945 = 4369459) B4369459
theorem B3883963 : Blo 2301435 3883963 := bstep (se 1 (by rfl) ⟨2912972, by rfl⟩ : syracuseStep 3883963 = 5825945) B5825945
theorem B5178617 : Blo 2301435 5178617 := bstep (se 2 (by rfl) ⟨1941981, by rfl⟩ : syracuseStep 5178617 = 3883963) B3883963
theorem B3452411 : Blo 2301435 3452411 := bstep (se 1 (by rfl) ⟨2589308, by rfl⟩ : syracuseStep 3452411 = 5178617) B5178617
theorem B2301607 : Blo 2301435 2301607 := bstep (se 1 (by rfl) ⟨1726205, by rfl⟩ : syracuseStep 2301607 = 3452411) B3452411
theorem B2589313 : Blo 2301435 2589313 := bbase (se 2 (by rfl) ⟨970992, by rfl⟩ : syracuseStep 2589313 = 1941985) (by norm_num)
theorem B3452417 : Blo 2301435 3452417 := bstep (se 2 (by rfl) ⟨1294656, by rfl⟩ : syracuseStep 3452417 = 2589313) B2589313
theorem B2301611 : Blo 2301435 2301611 := bstep (se 1 (by rfl) ⟨1726208, by rfl⟩ : syracuseStep 2301611 = 3452417) B3452417
theorem B5825965 : Blo 2301435 5825965 := bbase (se 3 (by rfl) ⟨1092368, by rfl⟩ : syracuseStep 5825965 = 2184737) (by norm_num)
theorem B7767953 : Blo 2301435 7767953 := bstep (se 2 (by rfl) ⟨2912982, by rfl⟩ : syracuseStep 7767953 = 5825965) B5825965
theorem B5178635 : Blo 2301435 5178635 := bstep (se 1 (by rfl) ⟨3883976, by rfl⟩ : syracuseStep 5178635 = 7767953) B7767953
theorem B3452423 : Blo 2301435 3452423 := bstep (se 1 (by rfl) ⟨2589317, by rfl⟩ : syracuseStep 3452423 = 5178635) B5178635
theorem B2301615 : Blo 2301435 2301615 := bstep (se 1 (by rfl) ⟨1726211, by rfl⟩ : syracuseStep 2301615 = 3452423) B3452423
theorem B3452429 : Blo 2301435 3452429 := bbase (se 3 (by rfl) ⟨647330, by rfl⟩ : syracuseStep 3452429 = 1294661) (by norm_num)
theorem B2301619 : Blo 2301435 2301619 := bstep (se 1 (by rfl) ⟨1726214, by rfl⟩ : syracuseStep 2301619 = 3452429) B3452429
theorem B5178653 : Blo 2301435 5178653 := bbase (se 3 (by rfl) ⟨970997, by rfl⟩ : syracuseStep 5178653 = 1941995) (by norm_num)
theorem B3452435 : Blo 2301435 3452435 := bstep (se 1 (by rfl) ⟨2589326, by rfl⟩ : syracuseStep 3452435 = 5178653) B5178653
theorem B2301623 : Blo 2301435 2301623 := bstep (se 1 (by rfl) ⟨1726217, by rfl⟩ : syracuseStep 2301623 = 3452435) B3452435
theorem B3883997 : Blo 2301435 3883997 := bbase (se 3 (by rfl) ⟨728249, by rfl⟩ : syracuseStep 3883997 = 1456499) (by norm_num)
theorem B2589331 : Blo 2301435 2589331 := bstep (se 1 (by rfl) ⟨1941998, by rfl⟩ : syracuseStep 2589331 = 3883997) B3883997
theorem B3452441 : Blo 2301435 3452441 := bstep (se 2 (by rfl) ⟨1294665, by rfl⟩ : syracuseStep 3452441 = 2589331) B2589331
theorem B2301627 : Blo 2301435 2301627 := bstep (se 1 (by rfl) ⟨1726220, by rfl⟩ : syracuseStep 2301627 = 3452441) B3452441
theorem B11060309 : Blo 2301435 11060309 := bbase (se 8 (by rfl) ⟨64806, by rfl⟩ : syracuseStep 11060309 = 129613) (by norm_num)
theorem B7373539 : Blo 2301435 7373539 := bstep (se 1 (by rfl) ⟨5530154, by rfl⟩ : syracuseStep 7373539 = 11060309) B11060309
theorem B9831385 : Blo 2301435 9831385 := bstep (se 2 (by rfl) ⟨3686769, by rfl⟩ : syracuseStep 9831385 = 7373539) B7373539
theorem B13108513 : Blo 2301435 13108513 := bstep (se 2 (by rfl) ⟨4915692, by rfl⟩ : syracuseStep 13108513 = 9831385) B9831385
theorem B17478017 : Blo 2301435 17478017 := bstep (se 2 (by rfl) ⟨6554256, by rfl⟩ : syracuseStep 17478017 = 13108513) B13108513
theorem B11652011 : Blo 2301435 11652011 := bstep (se 1 (by rfl) ⟨8739008, by rfl⟩ : syracuseStep 11652011 = 17478017) B17478017
theorem B7768007 : Blo 2301435 7768007 := bstep (se 1 (by rfl) ⟨5826005, by rfl⟩ : syracuseStep 7768007 = 11652011) B11652011
theorem B5178671 : Blo 2301435 5178671 := bstep (se 1 (by rfl) ⟨3884003, by rfl⟩ : syracuseStep 5178671 = 7768007) B7768007
theorem B3452447 : Blo 2301435 3452447 := bstep (se 1 (by rfl) ⟨2589335, by rfl⟩ : syracuseStep 3452447 = 5178671) B5178671
theorem B2301631 : Blo 2301435 2301631 := bstep (se 1 (by rfl) ⟨1726223, by rfl⟩ : syracuseStep 2301631 = 3452447) B3452447
theorem B3452453 : Blo 2301435 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B2301635 : Blo 2301435 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B2913013 : Blo 2301435 2913013 := bbase (se 5 (by rfl) ⟨136547, by rfl⟩ : syracuseStep 2913013 = 273095) (by norm_num)
theorem B3884017 : Blo 2301435 3884017 := bstep (se 2 (by rfl) ⟨1456506, by rfl⟩ : syracuseStep 3884017 = 2913013) B2913013
theorem B5178689 : Blo 2301435 5178689 := bstep (se 2 (by rfl) ⟨1942008, by rfl⟩ : syracuseStep 5178689 = 3884017) B3884017
theorem B3452459 : Blo 2301435 3452459 := bstep (se 1 (by rfl) ⟨2589344, by rfl⟩ : syracuseStep 3452459 = 5178689) B5178689
theorem B2301639 : Blo 2301435 2301639 := bstep (se 1 (by rfl) ⟨1726229, by rfl⟩ : syracuseStep 2301639 = 3452459) B3452459
theorem B2589349 : Blo 2301435 2589349 := bbase (se 4 (by rfl) ⟨242751, by rfl⟩ : syracuseStep 2589349 = 485503) (by norm_num)
theorem B3452465 : Blo 2301435 3452465 := bstep (se 2 (by rfl) ⟨1294674, by rfl⟩ : syracuseStep 3452465 = 2589349) B2589349
theorem B2301643 : Blo 2301435 2301643 := bstep (se 1 (by rfl) ⟨1726232, by rfl⟩ : syracuseStep 2301643 = 3452465) B3452465
theorem B3413125 : Blo 2301435 3413125 := bbase (se 4 (by rfl) ⟨319980, by rfl⟩ : syracuseStep 3413125 = 639961) (by norm_num)
theorem B4550833 : Blo 2301435 4550833 := bstep (se 2 (by rfl) ⟨1706562, by rfl⟩ : syracuseStep 4550833 = 3413125) B3413125
theorem B6067777 : Blo 2301435 6067777 := bstep (se 2 (by rfl) ⟨2275416, by rfl⟩ : syracuseStep 6067777 = 4550833) B4550833
theorem B8090369 : Blo 2301435 8090369 := bstep (se 2 (by rfl) ⟨3033888, by rfl⟩ : syracuseStep 8090369 = 6067777) B6067777
theorem B5393579 : Blo 2301435 5393579 := bstep (se 1 (by rfl) ⟨4045184, by rfl⟩ : syracuseStep 5393579 = 8090369) B8090369
theorem B14382877 : Blo 2301435 14382877 := bstep (se 3 (by rfl) ⟨2696789, by rfl⟩ : syracuseStep 14382877 = 5393579) B5393579
theorem B19177169 : Blo 2301435 19177169 := bstep (se 2 (by rfl) ⟨7191438, by rfl⟩ : syracuseStep 19177169 = 14382877) B14382877
theorem B51139117 : Blo 2301435 51139117 := bstep (se 3 (by rfl) ⟨9588584, by rfl⟩ : syracuseStep 51139117 = 19177169) B19177169
theorem B68185489 : Blo 2301435 68185489 := bstep (se 2 (by rfl) ⟨25569558, by rfl⟩ : syracuseStep 68185489 = 51139117) B51139117
theorem B90913985 : Blo 2301435 90913985 := bstep (se 2 (by rfl) ⟨34092744, by rfl⟩ : syracuseStep 90913985 = 68185489) B68185489
theorem B60609323 : Blo 2301435 60609323 := bstep (se 1 (by rfl) ⟨45456992, by rfl⟩ : syracuseStep 60609323 = 90913985) B90913985
theorem B40406215 : Blo 2301435 40406215 := bstep (se 1 (by rfl) ⟨30304661, by rfl⟩ : syracuseStep 40406215 = 60609323) B60609323
theorem B53874953 : Blo 2301435 53874953 := bstep (se 2 (by rfl) ⟨20203107, by rfl⟩ : syracuseStep 53874953 = 40406215) B40406215
theorem B35916635 : Blo 2301435 35916635 := bstep (se 1 (by rfl) ⟨26937476, by rfl⟩ : syracuseStep 35916635 = 53874953) B53874953
theorem B23944423 : Blo 2301435 23944423 := bstep (se 1 (by rfl) ⟨17958317, by rfl⟩ : syracuseStep 23944423 = 35916635) B35916635
theorem B31925897 : Blo 2301435 31925897 := bstep (se 2 (by rfl) ⟨11972211, by rfl⟩ : syracuseStep 31925897 = 23944423) B23944423
theorem B21283931 : Blo 2301435 21283931 := bstep (se 1 (by rfl) ⟨15962948, by rfl⟩ : syracuseStep 21283931 = 31925897) B31925897
theorem B14189287 : Blo 2301435 14189287 := bstep (se 1 (by rfl) ⟨10641965, by rfl⟩ : syracuseStep 14189287 = 21283931) B21283931
theorem B18919049 : Blo 2301435 18919049 := bstep (se 2 (by rfl) ⟨7094643, by rfl⟩ : syracuseStep 18919049 = 14189287) B14189287
theorem B50450797 : Blo 2301435 50450797 := bstep (se 3 (by rfl) ⟨9459524, by rfl⟩ : syracuseStep 50450797 = 18919049) B18919049
theorem B67267729 : Blo 2301435 67267729 := bstep (se 2 (by rfl) ⟨25225398, by rfl⟩ : syracuseStep 67267729 = 50450797) B50450797
theorem B358761221 : Blo 2301435 358761221 := bstep (se 4 (by rfl) ⟨33633864, by rfl⟩ : syracuseStep 358761221 = 67267729) B67267729
theorem B239174147 : Blo 2301435 239174147 := bstep (se 1 (by rfl) ⟨179380610, by rfl⟩ : syracuseStep 239174147 = 358761221) B358761221
theorem B159449431 : Blo 2301435 159449431 := bstep (se 1 (by rfl) ⟨119587073, by rfl⟩ : syracuseStep 159449431 = 239174147) B239174147
theorem B212599241 : Blo 2301435 212599241 := bstep (se 2 (by rfl) ⟨79724715, by rfl⟩ : syracuseStep 212599241 = 159449431) B159449431
theorem B141732827 : Blo 2301435 141732827 := bstep (se 1 (by rfl) ⟨106299620, by rfl⟩ : syracuseStep 141732827 = 212599241) B212599241
theorem B94488551 : Blo 2301435 94488551 := bstep (se 1 (by rfl) ⟨70866413, by rfl⟩ : syracuseStep 94488551 = 141732827) B141732827
theorem B62992367 : Blo 2301435 62992367 := bstep (se 1 (by rfl) ⟨47244275, by rfl⟩ : syracuseStep 62992367 = 94488551) B94488551
theorem B41994911 : Blo 2301435 41994911 := bstep (se 1 (by rfl) ⟨31496183, by rfl⟩ : syracuseStep 41994911 = 62992367) B62992367
theorem B27996607 : Blo 2301435 27996607 := bstep (se 1 (by rfl) ⟨20997455, by rfl⟩ : syracuseStep 27996607 = 41994911) B41994911
theorem B37328809 : Blo 2301435 37328809 := bstep (se 2 (by rfl) ⟨13998303, by rfl⟩ : syracuseStep 37328809 = 27996607) B27996607
theorem B49771745 : Blo 2301435 49771745 := bstep (se 2 (by rfl) ⟨18664404, by rfl⟩ : syracuseStep 49771745 = 37328809) B37328809
theorem B33181163 : Blo 2301435 33181163 := bstep (se 1 (by rfl) ⟨24885872, by rfl⟩ : syracuseStep 33181163 = 49771745) B49771745
theorem B22120775 : Blo 2301435 22120775 := bstep (se 1 (by rfl) ⟨16590581, by rfl⟩ : syracuseStep 22120775 = 33181163) B33181163
theorem B14747183 : Blo 2301435 14747183 := bstep (se 1 (by rfl) ⟨11060387, by rfl⟩ : syracuseStep 14747183 = 22120775) B22120775
theorem B9831455 : Blo 2301435 9831455 := bstep (se 1 (by rfl) ⟨7373591, by rfl⟩ : syracuseStep 9831455 = 14747183) B14747183
theorem B6554303 : Blo 2301435 6554303 := bstep (se 1 (by rfl) ⟨4915727, by rfl⟩ : syracuseStep 6554303 = 9831455) B9831455
theorem B4369535 : Blo 2301435 4369535 := bstep (se 1 (by rfl) ⟨3277151, by rfl⟩ : syracuseStep 4369535 = 6554303) B6554303
theorem B2913023 : Blo 2301435 2913023 := bstep (se 1 (by rfl) ⟨2184767, by rfl⟩ : syracuseStep 2913023 = 4369535) B4369535
theorem B7768061 : Blo 2301435 7768061 := bstep (se 3 (by rfl) ⟨1456511, by rfl⟩ : syracuseStep 7768061 = 2913023) B2913023
theorem B5178707 : Blo 2301435 5178707 := bstep (se 1 (by rfl) ⟨3884030, by rfl⟩ : syracuseStep 5178707 = 7768061) B7768061
theorem B3452471 : Blo 2301435 3452471 := bstep (se 1 (by rfl) ⟨2589353, by rfl⟩ : syracuseStep 3452471 = 5178707) B5178707
theorem B2301647 : Blo 2301435 2301647 := bstep (se 1 (by rfl) ⟨1726235, by rfl⟩ : syracuseStep 2301647 = 3452471) B3452471
theorem B3452477 : Blo 2301435 3452477 := bbase (se 3 (by rfl) ⟨647339, by rfl⟩ : syracuseStep 3452477 = 1294679) (by norm_num)
theorem B2301651 : Blo 2301435 2301651 := bstep (se 1 (by rfl) ⟨1726238, by rfl⟩ : syracuseStep 2301651 = 3452477) B3452477
theorem B5178725 : Blo 2301435 5178725 := bbase (se 4 (by rfl) ⟨485505, by rfl⟩ : syracuseStep 5178725 = 971011) (by norm_num)
theorem B3452483 : Blo 2301435 3452483 := bstep (se 1 (by rfl) ⟨2589362, by rfl⟩ : syracuseStep 3452483 = 5178725) B5178725
theorem B2301655 : Blo 2301435 2301655 := bstep (se 1 (by rfl) ⟨1726241, by rfl⟩ : syracuseStep 2301655 = 3452483) B3452483
theorem B5826077 : Blo 2301435 5826077 := bbase (se 3 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 5826077 = 2184779) (by norm_num)
theorem B3884051 : Blo 2301435 3884051 := bstep (se 1 (by rfl) ⟨2913038, by rfl⟩ : syracuseStep 3884051 = 5826077) B5826077
theorem B2589367 : Blo 2301435 2589367 := bstep (se 1 (by rfl) ⟨1942025, by rfl⟩ : syracuseStep 2589367 = 3884051) B3884051
theorem B3452489 : Blo 2301435 3452489 := bstep (se 2 (by rfl) ⟨1294683, by rfl⟩ : syracuseStep 3452489 = 2589367) B2589367
theorem B2301659 : Blo 2301435 2301659 := bstep (se 1 (by rfl) ⟨1726244, by rfl⟩ : syracuseStep 2301659 = 3452489) B3452489
theorem B4369565 : Blo 2301435 4369565 := bbase (se 3 (by rfl) ⟨819293, by rfl⟩ : syracuseStep 4369565 = 1638587) (by norm_num)
theorem B11652173 : Blo 2301435 11652173 := bstep (se 3 (by rfl) ⟨2184782, by rfl⟩ : syracuseStep 11652173 = 4369565) B4369565
theorem B7768115 : Blo 2301435 7768115 := bstep (se 1 (by rfl) ⟨5826086, by rfl⟩ : syracuseStep 7768115 = 11652173) B11652173
theorem B5178743 : Blo 2301435 5178743 := bstep (se 1 (by rfl) ⟨3884057, by rfl⟩ : syracuseStep 5178743 = 7768115) B7768115
theorem B3452495 : Blo 2301435 3452495 := bstep (se 1 (by rfl) ⟨2589371, by rfl⟩ : syracuseStep 3452495 = 5178743) B5178743
theorem B2301663 : Blo 2301435 2301663 := bstep (se 1 (by rfl) ⟨1726247, by rfl⟩ : syracuseStep 2301663 = 3452495) B3452495
theorem B3452501 : Blo 2301435 3452501 := bbase (se 8 (by rfl) ⟨20229, by rfl⟩ : syracuseStep 3452501 = 40459) (by norm_num)
theorem B2301667 : Blo 2301435 2301667 := bstep (se 1 (by rfl) ⟨1726250, by rfl⟩ : syracuseStep 2301667 = 3452501) B3452501
theorem B9831557 : Blo 2301435 9831557 := bbase (se 4 (by rfl) ⟨921708, by rfl⟩ : syracuseStep 9831557 = 1843417) (by norm_num)
theorem B6554371 : Blo 2301435 6554371 := bstep (se 1 (by rfl) ⟨4915778, by rfl⟩ : syracuseStep 6554371 = 9831557) B9831557
theorem B8739161 : Blo 2301435 8739161 := bstep (se 2 (by rfl) ⟨3277185, by rfl⟩ : syracuseStep 8739161 = 6554371) B6554371
theorem B5826107 : Blo 2301435 5826107 := bstep (se 1 (by rfl) ⟨4369580, by rfl⟩ : syracuseStep 5826107 = 8739161) B8739161
theorem B3884071 : Blo 2301435 3884071 := bstep (se 1 (by rfl) ⟨2913053, by rfl⟩ : syracuseStep 3884071 = 5826107) B5826107
theorem B5178761 : Blo 2301435 5178761 := bstep (se 2 (by rfl) ⟨1942035, by rfl⟩ : syracuseStep 5178761 = 3884071) B3884071
theorem B3452507 : Blo 2301435 3452507 := bstep (se 1 (by rfl) ⟨2589380, by rfl⟩ : syracuseStep 3452507 = 5178761) B5178761
theorem B2301671 : Blo 2301435 2301671 := bstep (se 1 (by rfl) ⟨1726253, by rfl⟩ : syracuseStep 2301671 = 3452507) B3452507
theorem B2589385 : Blo 2301435 2589385 := bbase (se 2 (by rfl) ⟨971019, by rfl⟩ : syracuseStep 2589385 = 1942039) (by norm_num)
theorem B3452513 : Blo 2301435 3452513 := bstep (se 2 (by rfl) ⟨1294692, by rfl⟩ : syracuseStep 3452513 = 2589385) B2589385
theorem B2301675 : Blo 2301435 2301675 := bstep (se 1 (by rfl) ⟨1726256, by rfl⟩ : syracuseStep 2301675 = 3452513) B3452513
theorem B3990797 : Blo 2301435 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B2660531 : Blo 2301435 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B7094749 : Blo 2301435 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B9459665 : Blo 2301435 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B6306443 : Blo 2301435 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B4204295 : Blo 2301435 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B2802863 : Blo 2301435 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B7474301 : Blo 2301435 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B4982867 : Blo 2301435 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B3321911 : Blo 2301435 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B8858429 : Blo 2301435 8858429 := bstep (se 3 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 8858429 = 3321911) B3321911
theorem B5905619 : Blo 2301435 5905619 := bstep (se 1 (by rfl) ⟨4429214, by rfl⟩ : syracuseStep 5905619 = 8858429) B8858429
theorem B3937079 : Blo 2301435 3937079 := bstep (se 1 (by rfl) ⟨2952809, by rfl⟩ : syracuseStep 3937079 = 5905619) B5905619
theorem B2624719 : Blo 2301435 2624719 := bstep (se 1 (by rfl) ⟨1968539, by rfl⟩ : syracuseStep 2624719 = 3937079) B3937079
theorem B3499625 : Blo 2301435 3499625 := bstep (se 2 (by rfl) ⟨1312359, by rfl⟩ : syracuseStep 3499625 = 2624719) B2624719
theorem B9332333 : Blo 2301435 9332333 := bstep (se 3 (by rfl) ⟨1749812, by rfl⟩ : syracuseStep 9332333 = 3499625) B3499625
theorem B6221555 : Blo 2301435 6221555 := bstep (se 1 (by rfl) ⟨4666166, by rfl⟩ : syracuseStep 6221555 = 9332333) B9332333
theorem B4147703 : Blo 2301435 4147703 := bstep (se 1 (by rfl) ⟨3110777, by rfl⟩ : syracuseStep 4147703 = 6221555) B6221555
theorem B2765135 : Blo 2301435 2765135 := bstep (se 1 (by rfl) ⟨2073851, by rfl⟩ : syracuseStep 2765135 = 4147703) B4147703
theorem B7373693 : Blo 2301435 7373693 := bstep (se 3 (by rfl) ⟨1382567, by rfl⟩ : syracuseStep 7373693 = 2765135) B2765135
theorem B19663181 : Blo 2301435 19663181 := bstep (se 3 (by rfl) ⟨3686846, by rfl⟩ : syracuseStep 19663181 = 7373693) B7373693
theorem B13108787 : Blo 2301435 13108787 := bstep (se 1 (by rfl) ⟨9831590, by rfl⟩ : syracuseStep 13108787 = 19663181) B19663181
theorem B8739191 : Blo 2301435 8739191 := bstep (se 1 (by rfl) ⟨6554393, by rfl⟩ : syracuseStep 8739191 = 13108787) B13108787
theorem B5826127 : Blo 2301435 5826127 := bstep (se 1 (by rfl) ⟨4369595, by rfl⟩ : syracuseStep 5826127 = 8739191) B8739191
theorem B7768169 : Blo 2301435 7768169 := bstep (se 2 (by rfl) ⟨2913063, by rfl⟩ : syracuseStep 7768169 = 5826127) B5826127
theorem B5178779 : Blo 2301435 5178779 := bstep (se 1 (by rfl) ⟨3884084, by rfl⟩ : syracuseStep 5178779 = 7768169) B7768169
theorem B3452519 : Blo 2301435 3452519 := bstep (se 1 (by rfl) ⟨2589389, by rfl⟩ : syracuseStep 3452519 = 5178779) B5178779
theorem B2301679 : Blo 2301435 2301679 := bstep (se 1 (by rfl) ⟨1726259, by rfl⟩ : syracuseStep 2301679 = 3452519) B3452519
theorem B3452525 : Blo 2301435 3452525 := bbase (se 3 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 3452525 = 1294697) (by norm_num)
theorem B2301683 : Blo 2301435 2301683 := bstep (se 1 (by rfl) ⟨1726262, by rfl⟩ : syracuseStep 2301683 = 3452525) B3452525
theorem B5178797 : Blo 2301435 5178797 := bbase (se 3 (by rfl) ⟨971024, by rfl⟩ : syracuseStep 5178797 = 1942049) (by norm_num)
theorem B3452531 : Blo 2301435 3452531 := bstep (se 1 (by rfl) ⟨2589398, by rfl⟩ : syracuseStep 3452531 = 5178797) B5178797
theorem B2301687 : Blo 2301435 2301687 := bstep (se 1 (by rfl) ⟨1726265, by rfl⟩ : syracuseStep 2301687 = 3452531) B3452531
theorem B5530301 : Blo 2301435 5530301 := bbase (se 3 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 5530301 = 2073863) (by norm_num)
theorem B3686867 : Blo 2301435 3686867 := bstep (se 1 (by rfl) ⟨2765150, by rfl⟩ : syracuseStep 3686867 = 5530301) B5530301
theorem B2457911 : Blo 2301435 2457911 := bstep (se 1 (by rfl) ⟨1843433, by rfl⟩ : syracuseStep 2457911 = 3686867) B3686867
theorem B6554429 : Blo 2301435 6554429 := bstep (se 3 (by rfl) ⟨1228955, by rfl⟩ : syracuseStep 6554429 = 2457911) B2457911
theorem B4369619 : Blo 2301435 4369619 := bstep (se 1 (by rfl) ⟨3277214, by rfl⟩ : syracuseStep 4369619 = 6554429) B6554429
theorem B2913079 : Blo 2301435 2913079 := bstep (se 1 (by rfl) ⟨2184809, by rfl⟩ : syracuseStep 2913079 = 4369619) B4369619
theorem B3884105 : Blo 2301435 3884105 := bstep (se 2 (by rfl) ⟨1456539, by rfl⟩ : syracuseStep 3884105 = 2913079) B2913079
theorem B2589403 : Blo 2301435 2589403 := bstep (se 1 (by rfl) ⟨1942052, by rfl⟩ : syracuseStep 2589403 = 3884105) B3884105
theorem B3452537 : Blo 2301435 3452537 := bstep (se 2 (by rfl) ⟨1294701, by rfl⟩ : syracuseStep 3452537 = 2589403) B2589403
theorem B2301691 : Blo 2301435 2301691 := bstep (se 1 (by rfl) ⟨1726268, by rfl⟩ : syracuseStep 2301691 = 3452537) B3452537
theorem B5918005 : Blo 2301435 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B31562693 : Blo 2301435 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B21041795 : Blo 2301435 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B14027863 : Blo 2301435 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B18703817 : Blo 2301435 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B12469211 : Blo 2301435 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B8312807 : Blo 2301435 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B5541871 : Blo 2301435 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B7389161 : Blo 2301435 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B4926107 : Blo 2301435 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B3284071 : Blo 2301435 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B17515045 : Blo 2301435 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B93413573 : Blo 2301435 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B62275715 : Blo 2301435 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B41517143 : Blo 2301435 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B27678095 : Blo 2301435 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B18452063 : Blo 2301435 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B12301375 : Blo 2301435 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B16401833 : Blo 2301435 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B174952885 : Blo 2301435 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B233270513 : Blo 2301435 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B155513675 : Blo 2301435 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B103675783 : Blo 2301435 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B138234377 : Blo 2301435 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B92156251 : Blo 2301435 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B122875001 : Blo 2301435 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B81916667 : Blo 2301435 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B54611111 : Blo 2301435 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B36407407 : Blo 2301435 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B48543209 : Blo 2301435 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B32362139 : Blo 2301435 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B21574759 : Blo 2301435 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B28766345 : Blo 2301435 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B76710253 : Blo 2301435 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B102280337 : Blo 2301435 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B68186891 : Blo 2301435 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B181831709 : Blo 2301435 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B121221139 : Blo 2301435 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B161628185 : Blo 2301435 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B107752123 : Blo 2301435 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B143669497 : Blo 2301435 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B191559329 : Blo 2301435 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B127706219 : Blo 2301435 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B85137479 : Blo 2301435 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B56758319 : Blo 2301435 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B37838879 : Blo 2301435 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B25225919 : Blo 2301435 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B16817279 : Blo 2301435 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B44846077 : Blo 2301435 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B59794769 : Blo 2301435 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B39863179 : Blo 2301435 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B53150905 : Blo 2301435 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B70867873 : Blo 2301435 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B94490497 : Blo 2301435 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 2301435 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 2301435 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 2301435 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 2301435 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 2301435 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 2301435 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 2301435 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B29494975 : Blo 2301435 29494975 := bstep (se 1 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 29494975 = 44242463) B44242463
theorem B39326633 : Blo 2301435 39326633 := bstep (se 2 (by rfl) ⟨14747487, by rfl⟩ : syracuseStep 39326633 = 29494975) B29494975
theorem B26217755 : Blo 2301435 26217755 := bstep (se 1 (by rfl) ⟨19663316, by rfl⟩ : syracuseStep 26217755 = 39326633) B39326633
theorem B17478503 : Blo 2301435 17478503 := bstep (se 1 (by rfl) ⟨13108877, by rfl⟩ : syracuseStep 17478503 = 26217755) B26217755
theorem B11652335 : Blo 2301435 11652335 := bstep (se 1 (by rfl) ⟨8739251, by rfl⟩ : syracuseStep 11652335 = 17478503) B17478503
theorem B7768223 : Blo 2301435 7768223 := bstep (se 1 (by rfl) ⟨5826167, by rfl⟩ : syracuseStep 7768223 = 11652335) B11652335
theorem B5178815 : Blo 2301435 5178815 := bstep (se 1 (by rfl) ⟨3884111, by rfl⟩ : syracuseStep 5178815 = 7768223) B7768223
theorem B3452543 : Blo 2301435 3452543 := bstep (se 1 (by rfl) ⟨2589407, by rfl⟩ : syracuseStep 3452543 = 5178815) B5178815
theorem B2301695 : Blo 2301435 2301695 := bstep (se 1 (by rfl) ⟨1726271, by rfl⟩ : syracuseStep 2301695 = 3452543) B3452543
theorem B3452549 : Blo 2301435 3452549 := bbase (se 4 (by rfl) ⟨323676, by rfl⟩ : syracuseStep 3452549 = 647353) (by norm_num)
theorem B2301699 : Blo 2301435 2301699 := bstep (se 1 (by rfl) ⟨1726274, by rfl⟩ : syracuseStep 2301699 = 3452549) B3452549
theorem B3884125 : Blo 2301435 3884125 := bbase (se 3 (by rfl) ⟨728273, by rfl⟩ : syracuseStep 3884125 = 1456547) (by norm_num)
theorem B5178833 : Blo 2301435 5178833 := bstep (se 2 (by rfl) ⟨1942062, by rfl⟩ : syracuseStep 5178833 = 3884125) B3884125
theorem B3452555 : Blo 2301435 3452555 := bstep (se 1 (by rfl) ⟨2589416, by rfl⟩ : syracuseStep 3452555 = 5178833) B5178833
theorem B2301703 : Blo 2301435 2301703 := bstep (se 1 (by rfl) ⟨1726277, by rfl⟩ : syracuseStep 2301703 = 3452555) B3452555
theorem B2589421 : Blo 2301435 2589421 := bbase (se 3 (by rfl) ⟨485516, by rfl⟩ : syracuseStep 2589421 = 971033) (by norm_num)
theorem B3452561 : Blo 2301435 3452561 := bstep (se 2 (by rfl) ⟨1294710, by rfl⟩ : syracuseStep 3452561 = 2589421) B2589421
theorem B2301707 : Blo 2301435 2301707 := bstep (se 1 (by rfl) ⟨1726280, by rfl⟩ : syracuseStep 2301707 = 3452561) B3452561
theorem B7768277 : Blo 2301435 7768277 := bbase (se 7 (by rfl) ⟨91034, by rfl⟩ : syracuseStep 7768277 = 182069) (by norm_num)
theorem B5178851 : Blo 2301435 5178851 := bstep (se 1 (by rfl) ⟨3884138, by rfl⟩ : syracuseStep 5178851 = 7768277) B7768277
theorem B3452567 : Blo 2301435 3452567 := bstep (se 1 (by rfl) ⟨2589425, by rfl⟩ : syracuseStep 3452567 = 5178851) B5178851
theorem B2301711 : Blo 2301435 2301711 := bstep (se 1 (by rfl) ⟨1726283, by rfl⟩ : syracuseStep 2301711 = 3452567) B3452567
theorem B3452573 : Blo 2301435 3452573 := bbase (se 3 (by rfl) ⟨647357, by rfl⟩ : syracuseStep 3452573 = 1294715) (by norm_num)
theorem B2301715 : Blo 2301435 2301715 := bstep (se 1 (by rfl) ⟨1726286, by rfl⟩ : syracuseStep 2301715 = 3452573) B3452573
theorem B5178869 : Blo 2301435 5178869 := bbase (se 5 (by rfl) ⟨242759, by rfl⟩ : syracuseStep 5178869 = 485519) (by norm_num)
theorem B3452579 : Blo 2301435 3452579 := bstep (se 1 (by rfl) ⟨2589434, by rfl⟩ : syracuseStep 3452579 = 5178869) B5178869
theorem B2301719 : Blo 2301435 2301719 := bstep (se 1 (by rfl) ⟨1726289, by rfl⟩ : syracuseStep 2301719 = 3452579) B3452579
theorem B2952865 : Blo 2301435 2952865 := bbase (se 2 (by rfl) ⟨1107324, by rfl⟩ : syracuseStep 2952865 = 2214649) (by norm_num)
theorem B15748613 : Blo 2301435 15748613 := bstep (se 4 (by rfl) ⟨1476432, by rfl⟩ : syracuseStep 15748613 = 2952865) B2952865
theorem B10499075 : Blo 2301435 10499075 := bstep (se 1 (by rfl) ⟨7874306, by rfl⟩ : syracuseStep 10499075 = 15748613) B15748613
theorem B6999383 : Blo 2301435 6999383 := bstep (se 1 (by rfl) ⟨5249537, by rfl⟩ : syracuseStep 6999383 = 10499075) B10499075
theorem B4666255 : Blo 2301435 4666255 := bstep (se 1 (by rfl) ⟨3499691, by rfl⟩ : syracuseStep 4666255 = 6999383) B6999383
theorem B24886693 : Blo 2301435 24886693 := bstep (se 4 (by rfl) ⟨2333127, by rfl⟩ : syracuseStep 24886693 = 4666255) B4666255
theorem B33182257 : Blo 2301435 33182257 := bstep (se 2 (by rfl) ⟨12443346, by rfl⟩ : syracuseStep 33182257 = 24886693) B24886693
theorem B44243009 : Blo 2301435 44243009 := bstep (se 2 (by rfl) ⟨16591128, by rfl⟩ : syracuseStep 44243009 = 33182257) B33182257
theorem B29495339 : Blo 2301435 29495339 := bstep (se 1 (by rfl) ⟨22121504, by rfl⟩ : syracuseStep 29495339 = 44243009) B44243009
theorem B19663559 : Blo 2301435 19663559 := bstep (se 1 (by rfl) ⟨14747669, by rfl⟩ : syracuseStep 19663559 = 29495339) B29495339
theorem B13109039 : Blo 2301435 13109039 := bstep (se 1 (by rfl) ⟨9831779, by rfl⟩ : syracuseStep 13109039 = 19663559) B19663559
theorem B8739359 : Blo 2301435 8739359 := bstep (se 1 (by rfl) ⟨6554519, by rfl⟩ : syracuseStep 8739359 = 13109039) B13109039
theorem B5826239 : Blo 2301435 5826239 := bstep (se 1 (by rfl) ⟨4369679, by rfl⟩ : syracuseStep 5826239 = 8739359) B8739359
theorem B3884159 : Blo 2301435 3884159 := bstep (se 1 (by rfl) ⟨2913119, by rfl⟩ : syracuseStep 3884159 = 5826239) B5826239
theorem B2589439 : Blo 2301435 2589439 := bstep (se 1 (by rfl) ⟨1942079, by rfl⟩ : syracuseStep 2589439 = 3884159) B3884159
theorem B3452585 : Blo 2301435 3452585 := bstep (se 2 (by rfl) ⟨1294719, by rfl⟩ : syracuseStep 3452585 = 2589439) B2589439
theorem B2301723 : Blo 2301435 2301723 := bstep (se 1 (by rfl) ⟨1726292, by rfl⟩ : syracuseStep 2301723 = 3452585) B3452585
theorem B2457949 : Blo 2301435 2457949 := bbase (se 3 (by rfl) ⟨460865, by rfl⟩ : syracuseStep 2457949 = 921731) (by norm_num)
theorem B3277265 : Blo 2301435 3277265 := bstep (se 2 (by rfl) ⟨1228974, by rfl⟩ : syracuseStep 3277265 = 2457949) B2457949
theorem B8739373 : Blo 2301435 8739373 := bstep (se 3 (by rfl) ⟨1638632, by rfl⟩ : syracuseStep 8739373 = 3277265) B3277265
theorem B11652497 : Blo 2301435 11652497 := bstep (se 2 (by rfl) ⟨4369686, by rfl⟩ : syracuseStep 11652497 = 8739373) B8739373
theorem B7768331 : Blo 2301435 7768331 := bstep (se 1 (by rfl) ⟨5826248, by rfl⟩ : syracuseStep 7768331 = 11652497) B11652497
theorem B5178887 : Blo 2301435 5178887 := bstep (se 1 (by rfl) ⟨3884165, by rfl⟩ : syracuseStep 5178887 = 7768331) B7768331
theorem B3452591 : Blo 2301435 3452591 := bstep (se 1 (by rfl) ⟨2589443, by rfl⟩ : syracuseStep 3452591 = 5178887) B5178887
theorem B2301727 : Blo 2301435 2301727 := bstep (se 1 (by rfl) ⟨1726295, by rfl⟩ : syracuseStep 2301727 = 3452591) B3452591
theorem B3452597 : Blo 2301435 3452597 := bbase (se 5 (by rfl) ⟨161840, by rfl⟩ : syracuseStep 3452597 = 323681) (by norm_num)
theorem B2301731 : Blo 2301435 2301731 := bstep (se 1 (by rfl) ⟨1726298, by rfl⟩ : syracuseStep 2301731 = 3452597) B3452597
theorem B5826269 : Blo 2301435 5826269 := bbase (se 3 (by rfl) ⟨1092425, by rfl⟩ : syracuseStep 5826269 = 2184851) (by norm_num)
theorem B3884179 : Blo 2301435 3884179 := bstep (se 1 (by rfl) ⟨2913134, by rfl⟩ : syracuseStep 3884179 = 5826269) B5826269
theorem B5178905 : Blo 2301435 5178905 := bstep (se 2 (by rfl) ⟨1942089, by rfl⟩ : syracuseStep 5178905 = 3884179) B3884179
theorem B3452603 : Blo 2301435 3452603 := bstep (se 1 (by rfl) ⟨2589452, by rfl⟩ : syracuseStep 3452603 = 5178905) B5178905
theorem B2301735 : Blo 2301435 2301735 := bstep (se 1 (by rfl) ⟨1726301, by rfl⟩ : syracuseStep 2301735 = 3452603) B3452603
theorem B2589457 : Blo 2301435 2589457 := bbase (se 2 (by rfl) ⟨971046, by rfl⟩ : syracuseStep 2589457 = 1942093) (by norm_num)
theorem B3452609 : Blo 2301435 3452609 := bstep (se 2 (by rfl) ⟨1294728, by rfl⟩ : syracuseStep 3452609 = 2589457) B2589457
theorem B2301739 : Blo 2301435 2301739 := bstep (se 1 (by rfl) ⟨1726304, by rfl⟩ : syracuseStep 2301739 = 3452609) B3452609
theorem B4369717 : Blo 2301435 4369717 := bbase (se 5 (by rfl) ⟨204830, by rfl⟩ : syracuseStep 4369717 = 409661) (by norm_num)
theorem B5826289 : Blo 2301435 5826289 := bstep (se 2 (by rfl) ⟨2184858, by rfl⟩ : syracuseStep 5826289 = 4369717) B4369717
theorem B7768385 : Blo 2301435 7768385 := bstep (se 2 (by rfl) ⟨2913144, by rfl⟩ : syracuseStep 7768385 = 5826289) B5826289
theorem B5178923 : Blo 2301435 5178923 := bstep (se 1 (by rfl) ⟨3884192, by rfl⟩ : syracuseStep 5178923 = 7768385) B7768385
theorem B3452615 : Blo 2301435 3452615 := bstep (se 1 (by rfl) ⟨2589461, by rfl⟩ : syracuseStep 3452615 = 5178923) B5178923
theorem B2301743 : Blo 2301435 2301743 := bstep (se 1 (by rfl) ⟨1726307, by rfl⟩ : syracuseStep 2301743 = 3452615) B3452615
theorem B3452621 : Blo 2301435 3452621 := bbase (se 3 (by rfl) ⟨647366, by rfl⟩ : syracuseStep 3452621 = 1294733) (by norm_num)
theorem B2301747 : Blo 2301435 2301747 := bstep (se 1 (by rfl) ⟨1726310, by rfl⟩ : syracuseStep 2301747 = 3452621) B3452621
theorem B5178941 : Blo 2301435 5178941 := bbase (se 3 (by rfl) ⟨971051, by rfl⟩ : syracuseStep 5178941 = 1942103) (by norm_num)
theorem B3452627 : Blo 2301435 3452627 := bstep (se 1 (by rfl) ⟨2589470, by rfl⟩ : syracuseStep 3452627 = 5178941) B5178941
theorem B2301751 : Blo 2301435 2301751 := bstep (se 1 (by rfl) ⟨1726313, by rfl⟩ : syracuseStep 2301751 = 3452627) B3452627
theorem B3884213 : Blo 2301435 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B2589475 : Blo 2301435 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B3452633 : Blo 2301435 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2301755 : Blo 2301435 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B27997973 : Blo 2301435 27997973 := bbase (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) (by norm_num)
theorem B18665315 : Blo 2301435 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B12443543 : Blo 2301435 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B8295695 : Blo 2301435 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B5530463 : Blo 2301435 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B3686975 : Blo 2301435 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B2457983 : Blo 2301435 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B6554621 : Blo 2301435 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B17478989 : Blo 2301435 17478989 := bstep (se 3 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 17478989 = 6554621) B6554621
theorem B11652659 : Blo 2301435 11652659 := bstep (se 1 (by rfl) ⟨8739494, by rfl⟩ : syracuseStep 11652659 = 17478989) B17478989
theorem B7768439 : Blo 2301435 7768439 := bstep (se 1 (by rfl) ⟨5826329, by rfl⟩ : syracuseStep 7768439 = 11652659) B11652659
theorem B5178959 : Blo 2301435 5178959 := bstep (se 1 (by rfl) ⟨3884219, by rfl⟩ : syracuseStep 5178959 = 7768439) B7768439
theorem B3452639 : Blo 2301435 3452639 := bstep (se 1 (by rfl) ⟨2589479, by rfl⟩ : syracuseStep 3452639 = 5178959) B5178959
theorem B2301759 : Blo 2301435 2301759 := bstep (se 1 (by rfl) ⟨1726319, by rfl⟩ : syracuseStep 2301759 = 3452639) B3452639
theorem B3452645 : Blo 2301435 3452645 := bbase (se 4 (by rfl) ⟨323685, by rfl⟩ : syracuseStep 3452645 = 647371) (by norm_num)
theorem B2301763 : Blo 2301435 2301763 := bstep (se 1 (by rfl) ⟨1726322, by rfl⟩ : syracuseStep 2301763 = 3452645) B3452645
theorem B6554645 : Blo 2301435 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B4369763 : Blo 2301435 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B2913175 : Blo 2301435 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B3884233 : Blo 2301435 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B5178977 : Blo 2301435 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B3452651 : Blo 2301435 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B2301767 : Blo 2301435 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B2589493 : Blo 2301435 2589493 := bbase (se 5 (by rfl) ⟨121382, by rfl⟩ : syracuseStep 2589493 = 242765) (by norm_num)
theorem B3452657 : Blo 2301435 3452657 := bstep (se 2 (by rfl) ⟨1294746, by rfl⟩ : syracuseStep 3452657 = 2589493) B2589493
theorem B2301771 : Blo 2301435 2301771 := bstep (se 1 (by rfl) ⟨1726328, by rfl⟩ : syracuseStep 2301771 = 3452657) B3452657
theorem B2913185 : Blo 2301435 2913185 := bbase (se 2 (by rfl) ⟨1092444, by rfl⟩ : syracuseStep 2913185 = 2184889) (by norm_num)
theorem B7768493 : Blo 2301435 7768493 := bstep (se 3 (by rfl) ⟨1456592, by rfl⟩ : syracuseStep 7768493 = 2913185) B2913185
theorem B5178995 : Blo 2301435 5178995 := bstep (se 1 (by rfl) ⟨3884246, by rfl⟩ : syracuseStep 5178995 = 7768493) B7768493
theorem B3452663 : Blo 2301435 3452663 := bstep (se 1 (by rfl) ⟨2589497, by rfl⟩ : syracuseStep 3452663 = 5178995) B5178995
theorem B2301775 : Blo 2301435 2301775 := bstep (se 1 (by rfl) ⟨1726331, by rfl⟩ : syracuseStep 2301775 = 3452663) B3452663
theorem B3452669 : Blo 2301435 3452669 := bbase (se 3 (by rfl) ⟨647375, by rfl⟩ : syracuseStep 3452669 = 1294751) (by norm_num)
theorem B2301779 : Blo 2301435 2301779 := bstep (se 1 (by rfl) ⟨1726334, by rfl⟩ : syracuseStep 2301779 = 3452669) B3452669
theorem B5179013 : Blo 2301435 5179013 := bbase (se 4 (by rfl) ⟨485532, by rfl⟩ : syracuseStep 5179013 = 971065) (by norm_num)
theorem B3452675 : Blo 2301435 3452675 := bstep (se 1 (by rfl) ⟨2589506, by rfl⟩ : syracuseStep 3452675 = 5179013) B5179013
theorem B2301783 : Blo 2301435 2301783 := bstep (se 1 (by rfl) ⟨1726337, by rfl⟩ : syracuseStep 2301783 = 3452675) B3452675
theorem B8295797 : Blo 2301435 8295797 := bbase (se 5 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 8295797 = 777731) (by norm_num)
theorem B5530531 : Blo 2301435 5530531 := bstep (se 1 (by rfl) ⟨4147898, by rfl⟩ : syracuseStep 5530531 = 8295797) B8295797
theorem B7374041 : Blo 2301435 7374041 := bstep (se 2 (by rfl) ⟨2765265, by rfl⟩ : syracuseStep 7374041 = 5530531) B5530531
theorem B4916027 : Blo 2301435 4916027 := bstep (se 1 (by rfl) ⟨3687020, by rfl⟩ : syracuseStep 4916027 = 7374041) B7374041
theorem B3277351 : Blo 2301435 3277351 := bstep (se 1 (by rfl) ⟨2458013, by rfl⟩ : syracuseStep 3277351 = 4916027) B4916027
theorem B4369801 : Blo 2301435 4369801 := bstep (se 2 (by rfl) ⟨1638675, by rfl⟩ : syracuseStep 4369801 = 3277351) B3277351
theorem B5826401 : Blo 2301435 5826401 := bstep (se 2 (by rfl) ⟨2184900, by rfl⟩ : syracuseStep 5826401 = 4369801) B4369801
theorem B3884267 : Blo 2301435 3884267 := bstep (se 1 (by rfl) ⟨2913200, by rfl⟩ : syracuseStep 3884267 = 5826401) B5826401
theorem B2589511 : Blo 2301435 2589511 := bstep (se 1 (by rfl) ⟨1942133, by rfl⟩ : syracuseStep 2589511 = 3884267) B3884267
theorem B3452681 : Blo 2301435 3452681 := bstep (se 2 (by rfl) ⟨1294755, by rfl⟩ : syracuseStep 3452681 = 2589511) B2589511
theorem B2301787 : Blo 2301435 2301787 := bstep (se 1 (by rfl) ⟨1726340, by rfl⟩ : syracuseStep 2301787 = 3452681) B3452681
theorem B11652821 : Blo 2301435 11652821 := bbase (se 7 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 11652821 = 273113) (by norm_num)
theorem B7768547 : Blo 2301435 7768547 := bstep (se 1 (by rfl) ⟨5826410, by rfl⟩ : syracuseStep 7768547 = 11652821) B11652821
theorem B5179031 : Blo 2301435 5179031 := bstep (se 1 (by rfl) ⟨3884273, by rfl⟩ : syracuseStep 5179031 = 7768547) B7768547
theorem B3452687 : Blo 2301435 3452687 := bstep (se 1 (by rfl) ⟨2589515, by rfl⟩ : syracuseStep 3452687 = 5179031) B5179031
theorem B2301791 : Blo 2301435 2301791 := bstep (se 1 (by rfl) ⟨1726343, by rfl⟩ : syracuseStep 2301791 = 3452687) B3452687
theorem B3452693 : Blo 2301435 3452693 := bbase (se 6 (by rfl) ⟨80922, by rfl⟩ : syracuseStep 3452693 = 161845) (by norm_num)
theorem B2301795 : Blo 2301435 2301795 := bstep (se 1 (by rfl) ⟨1726346, by rfl⟩ : syracuseStep 2301795 = 3452693) B3452693
theorem B5905925 : Blo 2301435 5905925 := bbase (se 4 (by rfl) ⟨553680, by rfl⟩ : syracuseStep 5905925 = 1107361) (by norm_num)
theorem B3937283 : Blo 2301435 3937283 := bstep (se 1 (by rfl) ⟨2952962, by rfl⟩ : syracuseStep 3937283 = 5905925) B5905925
theorem B2624855 : Blo 2301435 2624855 := bstep (se 1 (by rfl) ⟨1968641, by rfl⟩ : syracuseStep 2624855 = 3937283) B3937283
theorem B27998453 : Blo 2301435 27998453 := bstep (se 5 (by rfl) ⟨1312427, by rfl⟩ : syracuseStep 27998453 = 2624855) B2624855
theorem B18665635 : Blo 2301435 18665635 := bstep (se 1 (by rfl) ⟨13999226, by rfl⟩ : syracuseStep 18665635 = 27998453) B27998453
theorem B24887513 : Blo 2301435 24887513 := bstep (se 2 (by rfl) ⟨9332817, by rfl⟩ : syracuseStep 24887513 = 18665635) B18665635
theorem B66366701 : Blo 2301435 66366701 := bstep (se 3 (by rfl) ⟨12443756, by rfl⟩ : syracuseStep 66366701 = 24887513) B24887513
theorem B44244467 : Blo 2301435 44244467 := bstep (se 1 (by rfl) ⟨33183350, by rfl⟩ : syracuseStep 44244467 = 66366701) B66366701
theorem B29496311 : Blo 2301435 29496311 := bstep (se 1 (by rfl) ⟨22122233, by rfl⟩ : syracuseStep 29496311 = 44244467) B44244467
theorem B19664207 : Blo 2301435 19664207 := bstep (se 1 (by rfl) ⟨14748155, by rfl⟩ : syracuseStep 19664207 = 29496311) B29496311
theorem B13109471 : Blo 2301435 13109471 := bstep (se 1 (by rfl) ⟨9832103, by rfl⟩ : syracuseStep 13109471 = 19664207) B19664207
theorem B8739647 : Blo 2301435 8739647 := bstep (se 1 (by rfl) ⟨6554735, by rfl⟩ : syracuseStep 8739647 = 13109471) B13109471
theorem B5826431 : Blo 2301435 5826431 := bstep (se 1 (by rfl) ⟨4369823, by rfl⟩ : syracuseStep 5826431 = 8739647) B8739647
theorem B3884287 : Blo 2301435 3884287 := bstep (se 1 (by rfl) ⟨2913215, by rfl⟩ : syracuseStep 3884287 = 5826431) B5826431
theorem B5179049 : Blo 2301435 5179049 := bstep (se 2 (by rfl) ⟨1942143, by rfl⟩ : syracuseStep 5179049 = 3884287) B3884287
theorem B3452699 : Blo 2301435 3452699 := bstep (se 1 (by rfl) ⟨2589524, by rfl⟩ : syracuseStep 3452699 = 5179049) B5179049
theorem B2301799 : Blo 2301435 2301799 := bstep (se 1 (by rfl) ⟨1726349, by rfl⟩ : syracuseStep 2301799 = 3452699) B3452699
theorem B2589529 : Blo 2301435 2589529 := bbase (se 2 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 2589529 = 1942147) (by norm_num)
theorem B3452705 : Blo 2301435 3452705 := bstep (se 2 (by rfl) ⟨1294764, by rfl⟩ : syracuseStep 3452705 = 2589529) B2589529
theorem B2301803 : Blo 2301435 2301803 := bstep (se 1 (by rfl) ⟨1726352, by rfl⟩ : syracuseStep 2301803 = 3452705) B3452705
theorem B4916069 : Blo 2301435 4916069 := bbase (se 4 (by rfl) ⟨460881, by rfl⟩ : syracuseStep 4916069 = 921763) (by norm_num)
theorem B3277379 : Blo 2301435 3277379 := bstep (se 1 (by rfl) ⟨2458034, by rfl⟩ : syracuseStep 3277379 = 4916069) B4916069
theorem B8739677 : Blo 2301435 8739677 := bstep (se 3 (by rfl) ⟨1638689, by rfl⟩ : syracuseStep 8739677 = 3277379) B3277379
theorem B5826451 : Blo 2301435 5826451 := bstep (se 1 (by rfl) ⟨4369838, by rfl⟩ : syracuseStep 5826451 = 8739677) B8739677
theorem B7768601 : Blo 2301435 7768601 := bstep (se 2 (by rfl) ⟨2913225, by rfl⟩ : syracuseStep 7768601 = 5826451) B5826451
theorem B5179067 : Blo 2301435 5179067 := bstep (se 1 (by rfl) ⟨3884300, by rfl⟩ : syracuseStep 5179067 = 7768601) B7768601
theorem B3452711 : Blo 2301435 3452711 := bstep (se 1 (by rfl) ⟨2589533, by rfl⟩ : syracuseStep 3452711 = 5179067) B5179067
theorem B2301807 : Blo 2301435 2301807 := bstep (se 1 (by rfl) ⟨1726355, by rfl⟩ : syracuseStep 2301807 = 3452711) B3452711
theorem B3452717 : Blo 2301435 3452717 := bbase (se 3 (by rfl) ⟨647384, by rfl⟩ : syracuseStep 3452717 = 1294769) (by norm_num)
theorem B2301811 : Blo 2301435 2301811 := bstep (se 1 (by rfl) ⟨1726358, by rfl⟩ : syracuseStep 2301811 = 3452717) B3452717
theorem B5179085 : Blo 2301435 5179085 := bbase (se 3 (by rfl) ⟨971078, by rfl⟩ : syracuseStep 5179085 = 1942157) (by norm_num)
theorem B3452723 : Blo 2301435 3452723 := bstep (se 1 (by rfl) ⟨2589542, by rfl⟩ : syracuseStep 3452723 = 5179085) B5179085
theorem B2301815 : Blo 2301435 2301815 := bstep (se 1 (by rfl) ⟨1726361, by rfl⟩ : syracuseStep 2301815 = 3452723) B3452723
theorem B2913241 : Blo 2301435 2913241 := bbase (se 2 (by rfl) ⟨1092465, by rfl⟩ : syracuseStep 2913241 = 2184931) (by norm_num)
theorem B3884321 : Blo 2301435 3884321 := bstep (se 2 (by rfl) ⟨1456620, by rfl⟩ : syracuseStep 3884321 = 2913241) B2913241
theorem B2589547 : Blo 2301435 2589547 := bstep (se 1 (by rfl) ⟨1942160, by rfl⟩ : syracuseStep 2589547 = 3884321) B3884321
theorem B3452729 : Blo 2301435 3452729 := bstep (se 2 (by rfl) ⟨1294773, by rfl⟩ : syracuseStep 3452729 = 2589547) B2589547
theorem B2301819 : Blo 2301435 2301819 := bstep (se 1 (by rfl) ⟨1726364, by rfl⟩ : syracuseStep 2301819 = 3452729) B3452729
theorem B3687077 : Blo 2301435 3687077 := bbase (se 4 (by rfl) ⟨345663, by rfl⟩ : syracuseStep 3687077 = 691327) (by norm_num)
theorem B9832205 : Blo 2301435 9832205 := bstep (se 3 (by rfl) ⟨1843538, by rfl⟩ : syracuseStep 9832205 = 3687077) B3687077
theorem B26219213 : Blo 2301435 26219213 := bstep (se 3 (by rfl) ⟨4916102, by rfl⟩ : syracuseStep 26219213 = 9832205) B9832205
theorem B17479475 : Blo 2301435 17479475 := bstep (se 1 (by rfl) ⟨13109606, by rfl⟩ : syracuseStep 17479475 = 26219213) B26219213
theorem B11652983 : Blo 2301435 11652983 := bstep (se 1 (by rfl) ⟨8739737, by rfl⟩ : syracuseStep 11652983 = 17479475) B17479475
theorem B7768655 : Blo 2301435 7768655 := bstep (se 1 (by rfl) ⟨5826491, by rfl⟩ : syracuseStep 7768655 = 11652983) B11652983
theorem B5179103 : Blo 2301435 5179103 := bstep (se 1 (by rfl) ⟨3884327, by rfl⟩ : syracuseStep 5179103 = 7768655) B7768655
theorem B3452735 : Blo 2301435 3452735 := bstep (se 1 (by rfl) ⟨2589551, by rfl⟩ : syracuseStep 3452735 = 5179103) B5179103
theorem B2301823 : Blo 2301435 2301823 := bstep (se 1 (by rfl) ⟨1726367, by rfl⟩ : syracuseStep 2301823 = 3452735) B3452735
theorem B3452741 : Blo 2301435 3452741 := bbase (se 4 (by rfl) ⟨323694, by rfl⟩ : syracuseStep 3452741 = 647389) (by norm_num)
theorem B2301827 : Blo 2301435 2301827 := bstep (se 1 (by rfl) ⟨1726370, by rfl⟩ : syracuseStep 2301827 = 3452741) B3452741
theorem B3884341 : Blo 2301435 3884341 := bbase (se 5 (by rfl) ⟨182078, by rfl⟩ : syracuseStep 3884341 = 364157) (by norm_num)
theorem B5179121 : Blo 2301435 5179121 := bstep (se 2 (by rfl) ⟨1942170, by rfl⟩ : syracuseStep 5179121 = 3884341) B3884341
theorem B3452747 : Blo 2301435 3452747 := bstep (se 1 (by rfl) ⟨2589560, by rfl⟩ : syracuseStep 3452747 = 5179121) B5179121
theorem B2301831 : Blo 2301435 2301831 := bstep (se 1 (by rfl) ⟨1726373, by rfl⟩ : syracuseStep 2301831 = 3452747) B3452747
theorem B2589565 : Blo 2301435 2589565 := bbase (se 3 (by rfl) ⟨485543, by rfl⟩ : syracuseStep 2589565 = 971087) (by norm_num)
theorem B3452753 : Blo 2301435 3452753 := bstep (se 2 (by rfl) ⟨1294782, by rfl⟩ : syracuseStep 3452753 = 2589565) B2589565
theorem B2301835 : Blo 2301435 2301835 := bstep (se 1 (by rfl) ⟨1726376, by rfl⟩ : syracuseStep 2301835 = 3452753) B3452753
theorem B7768709 : Blo 2301435 7768709 := bbase (se 4 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 7768709 = 1456633) (by norm_num)
theorem B5179139 : Blo 2301435 5179139 := bstep (se 1 (by rfl) ⟨3884354, by rfl⟩ : syracuseStep 5179139 = 7768709) B7768709
theorem B3452759 : Blo 2301435 3452759 := bstep (se 1 (by rfl) ⟨2589569, by rfl⟩ : syracuseStep 3452759 = 5179139) B5179139
theorem B2301839 : Blo 2301435 2301839 := bstep (se 1 (by rfl) ⟨1726379, by rfl⟩ : syracuseStep 2301839 = 3452759) B3452759
theorem B3452765 : Blo 2301435 3452765 := bbase (se 3 (by rfl) ⟨647393, by rfl⟩ : syracuseStep 3452765 = 1294787) (by norm_num)
theorem B2301843 : Blo 2301435 2301843 := bstep (se 1 (by rfl) ⟨1726382, by rfl⟩ : syracuseStep 2301843 = 3452765) B3452765
theorem B5179157 : Blo 2301435 5179157 := bbase (se 6 (by rfl) ⟨121386, by rfl⟩ : syracuseStep 5179157 = 242773) (by norm_num)
theorem B3452771 : Blo 2301435 3452771 := bstep (se 1 (by rfl) ⟨2589578, by rfl⟩ : syracuseStep 3452771 = 5179157) B5179157
theorem B2301847 : Blo 2301435 2301847 := bstep (se 1 (by rfl) ⟨1726385, by rfl⟩ : syracuseStep 2301847 = 3452771) B3452771
theorem B8739845 : Blo 2301435 8739845 := bbase (se 4 (by rfl) ⟨819360, by rfl⟩ : syracuseStep 8739845 = 1638721) (by norm_num)
theorem B5826563 : Blo 2301435 5826563 := bstep (se 1 (by rfl) ⟨4369922, by rfl⟩ : syracuseStep 5826563 = 8739845) B8739845
theorem B3884375 : Blo 2301435 3884375 := bstep (se 1 (by rfl) ⟨2913281, by rfl⟩ : syracuseStep 3884375 = 5826563) B5826563
theorem B2589583 : Blo 2301435 2589583 := bstep (se 1 (by rfl) ⟨1942187, by rfl⟩ : syracuseStep 2589583 = 3884375) B3884375
theorem B3452777 : Blo 2301435 3452777 := bstep (se 2 (by rfl) ⟨1294791, by rfl⟩ : syracuseStep 3452777 = 2589583) B2589583
theorem B2301851 : Blo 2301435 2301851 := bstep (se 1 (by rfl) ⟨1726388, by rfl⟩ : syracuseStep 2301851 = 3452777) B3452777
theorem B5530693 : Blo 2301435 5530693 := bbase (se 4 (by rfl) ⟨518502, by rfl⟩ : syracuseStep 5530693 = 1037005) (by norm_num)
theorem B7374257 : Blo 2301435 7374257 := bstep (se 2 (by rfl) ⟨2765346, by rfl⟩ : syracuseStep 7374257 = 5530693) B5530693
theorem B4916171 : Blo 2301435 4916171 := bstep (se 1 (by rfl) ⟨3687128, by rfl⟩ : syracuseStep 4916171 = 7374257) B7374257
theorem B13109789 : Blo 2301435 13109789 := bstep (se 3 (by rfl) ⟨2458085, by rfl⟩ : syracuseStep 13109789 = 4916171) B4916171
theorem B8739859 : Blo 2301435 8739859 := bstep (se 1 (by rfl) ⟨6554894, by rfl⟩ : syracuseStep 8739859 = 13109789) B13109789
theorem B11653145 : Blo 2301435 11653145 := bstep (se 2 (by rfl) ⟨4369929, by rfl⟩ : syracuseStep 11653145 = 8739859) B8739859
theorem B7768763 : Blo 2301435 7768763 := bstep (se 1 (by rfl) ⟨5826572, by rfl⟩ : syracuseStep 7768763 = 11653145) B11653145
theorem B5179175 : Blo 2301435 5179175 := bstep (se 1 (by rfl) ⟨3884381, by rfl⟩ : syracuseStep 5179175 = 7768763) B7768763
theorem B3452783 : Blo 2301435 3452783 := bstep (se 1 (by rfl) ⟨2589587, by rfl⟩ : syracuseStep 3452783 = 5179175) B5179175
theorem B2301855 : Blo 2301435 2301855 := bstep (se 1 (by rfl) ⟨1726391, by rfl⟩ : syracuseStep 2301855 = 3452783) B3452783
theorem B3452789 : Blo 2301435 3452789 := bbase (se 5 (by rfl) ⟨161849, by rfl⟩ : syracuseStep 3452789 = 323699) (by norm_num)
theorem B2301859 : Blo 2301435 2301859 := bstep (se 1 (by rfl) ⟨1726394, by rfl⟩ : syracuseStep 2301859 = 3452789) B3452789
theorem B4916189 : Blo 2301435 4916189 := bbase (se 3 (by rfl) ⟨921785, by rfl⟩ : syracuseStep 4916189 = 1843571) (by norm_num)
theorem B3277459 : Blo 2301435 3277459 := bstep (se 1 (by rfl) ⟨2458094, by rfl⟩ : syracuseStep 3277459 = 4916189) B4916189
theorem B4369945 : Blo 2301435 4369945 := bstep (se 2 (by rfl) ⟨1638729, by rfl⟩ : syracuseStep 4369945 = 3277459) B3277459
theorem B5826593 : Blo 2301435 5826593 := bstep (se 2 (by rfl) ⟨2184972, by rfl⟩ : syracuseStep 5826593 = 4369945) B4369945
theorem B3884395 : Blo 2301435 3884395 := bstep (se 1 (by rfl) ⟨2913296, by rfl⟩ : syracuseStep 3884395 = 5826593) B5826593
theorem B5179193 : Blo 2301435 5179193 := bstep (se 2 (by rfl) ⟨1942197, by rfl⟩ : syracuseStep 5179193 = 3884395) B3884395
theorem B3452795 : Blo 2301435 3452795 := bstep (se 1 (by rfl) ⟨2589596, by rfl⟩ : syracuseStep 3452795 = 5179193) B5179193
theorem B2301863 : Blo 2301435 2301863 := bstep (se 1 (by rfl) ⟨1726397, by rfl⟩ : syracuseStep 2301863 = 3452795) B3452795
theorem B2589601 : Blo 2301435 2589601 := bbase (se 2 (by rfl) ⟨971100, by rfl⟩ : syracuseStep 2589601 = 1942201) (by norm_num)
theorem B3452801 : Blo 2301435 3452801 := bstep (se 2 (by rfl) ⟨1294800, by rfl⟩ : syracuseStep 3452801 = 2589601) B2589601
theorem B2301867 : Blo 2301435 2301867 := bstep (se 1 (by rfl) ⟨1726400, by rfl⟩ : syracuseStep 2301867 = 3452801) B3452801
theorem B5826613 : Blo 2301435 5826613 := bbase (se 5 (by rfl) ⟨273122, by rfl⟩ : syracuseStep 5826613 = 546245) (by norm_num)
theorem B7768817 : Blo 2301435 7768817 := bstep (se 2 (by rfl) ⟨2913306, by rfl⟩ : syracuseStep 7768817 = 5826613) B5826613
theorem B5179211 : Blo 2301435 5179211 := bstep (se 1 (by rfl) ⟨3884408, by rfl⟩ : syracuseStep 5179211 = 7768817) B7768817
theorem B3452807 : Blo 2301435 3452807 := bstep (se 1 (by rfl) ⟨2589605, by rfl⟩ : syracuseStep 3452807 = 5179211) B5179211
theorem B2301871 : Blo 2301435 2301871 := bstep (se 1 (by rfl) ⟨1726403, by rfl⟩ : syracuseStep 2301871 = 3452807) B3452807
theorem B3452813 : Blo 2301435 3452813 := bbase (se 3 (by rfl) ⟨647402, by rfl⟩ : syracuseStep 3452813 = 1294805) (by norm_num)
theorem B2301875 : Blo 2301435 2301875 := bstep (se 1 (by rfl) ⟨1726406, by rfl⟩ : syracuseStep 2301875 = 3452813) B3452813
theorem B5179229 : Blo 2301435 5179229 := bbase (se 3 (by rfl) ⟨971105, by rfl⟩ : syracuseStep 5179229 = 1942211) (by norm_num)
theorem B3452819 : Blo 2301435 3452819 := bstep (se 1 (by rfl) ⟨2589614, by rfl⟩ : syracuseStep 3452819 = 5179229) B5179229
theorem B2301879 : Blo 2301435 2301879 := bstep (se 1 (by rfl) ⟨1726409, by rfl⟩ : syracuseStep 2301879 = 3452819) B3452819
theorem B3884429 : Blo 2301435 3884429 := bbase (se 3 (by rfl) ⟨728330, by rfl⟩ : syracuseStep 3884429 = 1456661) (by norm_num)
theorem B2589619 : Blo 2301435 2589619 := bstep (se 1 (by rfl) ⟨1942214, by rfl⟩ : syracuseStep 2589619 = 3884429) B3884429
theorem B3452825 : Blo 2301435 3452825 := bstep (se 2 (by rfl) ⟨1294809, by rfl⟩ : syracuseStep 3452825 = 2589619) B2589619
theorem B2301883 : Blo 2301435 2301883 := bstep (se 1 (by rfl) ⟨1726412, by rfl⟩ : syracuseStep 2301883 = 3452825) B3452825
theorem B16592309 : Blo 2301435 16592309 := bbase (se 5 (by rfl) ⟨777764, by rfl⟩ : syracuseStep 16592309 = 1555529) (by norm_num)
theorem B11061539 : Blo 2301435 11061539 := bstep (se 1 (by rfl) ⟨8296154, by rfl⟩ : syracuseStep 11061539 = 16592309) B16592309
theorem B7374359 : Blo 2301435 7374359 := bstep (se 1 (by rfl) ⟨5530769, by rfl⟩ : syracuseStep 7374359 = 11061539) B11061539
theorem B19664957 : Blo 2301435 19664957 := bstep (se 3 (by rfl) ⟨3687179, by rfl⟩ : syracuseStep 19664957 = 7374359) B7374359
theorem B13109971 : Blo 2301435 13109971 := bstep (se 1 (by rfl) ⟨9832478, by rfl⟩ : syracuseStep 13109971 = 19664957) B19664957
theorem B17479961 : Blo 2301435 17479961 := bstep (se 2 (by rfl) ⟨6554985, by rfl⟩ : syracuseStep 17479961 = 13109971) B13109971
theorem B11653307 : Blo 2301435 11653307 := bstep (se 1 (by rfl) ⟨8739980, by rfl⟩ : syracuseStep 11653307 = 17479961) B17479961
theorem B7768871 : Blo 2301435 7768871 := bstep (se 1 (by rfl) ⟨5826653, by rfl⟩ : syracuseStep 7768871 = 11653307) B11653307
theorem B5179247 : Blo 2301435 5179247 := bstep (se 1 (by rfl) ⟨3884435, by rfl⟩ : syracuseStep 5179247 = 7768871) B7768871
theorem B3452831 : Blo 2301435 3452831 := bstep (se 1 (by rfl) ⟨2589623, by rfl⟩ : syracuseStep 3452831 = 5179247) B5179247
theorem B2301887 : Blo 2301435 2301887 := bstep (se 1 (by rfl) ⟨1726415, by rfl⟩ : syracuseStep 2301887 = 3452831) B3452831
theorem B3452837 : Blo 2301435 3452837 := bbase (se 4 (by rfl) ⟨323703, by rfl⟩ : syracuseStep 3452837 = 647407) (by norm_num)
theorem B2301891 : Blo 2301435 2301891 := bstep (se 1 (by rfl) ⟨1726418, by rfl⟩ : syracuseStep 2301891 = 3452837) B3452837
theorem B2913337 : Blo 2301435 2913337 := bbase (se 2 (by rfl) ⟨1092501, by rfl⟩ : syracuseStep 2913337 = 2185003) (by norm_num)
theorem B3884449 : Blo 2301435 3884449 := bstep (se 2 (by rfl) ⟨1456668, by rfl⟩ : syracuseStep 3884449 = 2913337) B2913337
theorem B5179265 : Blo 2301435 5179265 := bstep (se 2 (by rfl) ⟨1942224, by rfl⟩ : syracuseStep 5179265 = 3884449) B3884449
theorem B3452843 : Blo 2301435 3452843 := bstep (se 1 (by rfl) ⟨2589632, by rfl⟩ : syracuseStep 3452843 = 5179265) B5179265
theorem B2301895 : Blo 2301435 2301895 := bstep (se 1 (by rfl) ⟨1726421, by rfl⟩ : syracuseStep 2301895 = 3452843) B3452843
theorem B2589637 : Blo 2301435 2589637 := bbase (se 4 (by rfl) ⟨242778, by rfl⟩ : syracuseStep 2589637 = 485557) (by norm_num)
theorem B3452849 : Blo 2301435 3452849 := bstep (se 2 (by rfl) ⟨1294818, by rfl⟩ : syracuseStep 3452849 = 2589637) B2589637
theorem B2301899 : Blo 2301435 2301899 := bstep (se 1 (by rfl) ⟨1726424, by rfl⟩ : syracuseStep 2301899 = 3452849) B3452849
theorem B4370021 : Blo 2301435 4370021 := bbase (se 4 (by rfl) ⟨409689, by rfl⟩ : syracuseStep 4370021 = 819379) (by norm_num)
theorem B2913347 : Blo 2301435 2913347 := bstep (se 1 (by rfl) ⟨2185010, by rfl⟩ : syracuseStep 2913347 = 4370021) B4370021
theorem B7768925 : Blo 2301435 7768925 := bstep (se 3 (by rfl) ⟨1456673, by rfl⟩ : syracuseStep 7768925 = 2913347) B2913347
theorem B5179283 : Blo 2301435 5179283 := bstep (se 1 (by rfl) ⟨3884462, by rfl⟩ : syracuseStep 5179283 = 7768925) B7768925
theorem B3452855 : Blo 2301435 3452855 := bstep (se 1 (by rfl) ⟨2589641, by rfl⟩ : syracuseStep 3452855 = 5179283) B5179283
theorem B2301903 : Blo 2301435 2301903 := bstep (se 1 (by rfl) ⟨1726427, by rfl⟩ : syracuseStep 2301903 = 3452855) B3452855
theorem B3452861 : Blo 2301435 3452861 := bbase (se 3 (by rfl) ⟨647411, by rfl⟩ : syracuseStep 3452861 = 1294823) (by norm_num)
theorem B2301907 : Blo 2301435 2301907 := bstep (se 1 (by rfl) ⟨1726430, by rfl⟩ : syracuseStep 2301907 = 3452861) B3452861
theorem B5179301 : Blo 2301435 5179301 := bbase (se 4 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 5179301 = 971119) (by norm_num)
theorem B3452867 : Blo 2301435 3452867 := bstep (se 1 (by rfl) ⟨2589650, by rfl⟩ : syracuseStep 3452867 = 5179301) B5179301
theorem B2301911 : Blo 2301435 2301911 := bstep (se 1 (by rfl) ⟨1726433, by rfl⟩ : syracuseStep 2301911 = 3452867) B3452867
theorem B5826725 : Blo 2301435 5826725 := bbase (se 4 (by rfl) ⟨546255, by rfl⟩ : syracuseStep 5826725 = 1092511) (by norm_num)
theorem B3884483 : Blo 2301435 3884483 := bstep (se 1 (by rfl) ⟨2913362, by rfl⟩ : syracuseStep 3884483 = 5826725) B5826725
theorem B2589655 : Blo 2301435 2589655 := bstep (se 1 (by rfl) ⟨1942241, by rfl⟩ : syracuseStep 2589655 = 3884483) B3884483
theorem B3452873 : Blo 2301435 3452873 := bstep (se 2 (by rfl) ⟨1294827, by rfl⟩ : syracuseStep 3452873 = 2589655) B2589655
theorem B2301915 : Blo 2301435 2301915 := bstep (se 1 (by rfl) ⟨1726436, by rfl⟩ : syracuseStep 2301915 = 3452873) B3452873
theorem B6555077 : Blo 2301435 6555077 := bbase (se 4 (by rfl) ⟨614538, by rfl⟩ : syracuseStep 6555077 = 1229077) (by norm_num)
theorem B4370051 : Blo 2301435 4370051 := bstep (se 1 (by rfl) ⟨3277538, by rfl⟩ : syracuseStep 4370051 = 6555077) B6555077
theorem B11653469 : Blo 2301435 11653469 := bstep (se 3 (by rfl) ⟨2185025, by rfl⟩ : syracuseStep 11653469 = 4370051) B4370051
theorem B7768979 : Blo 2301435 7768979 := bstep (se 1 (by rfl) ⟨5826734, by rfl⟩ : syracuseStep 7768979 = 11653469) B11653469
theorem B5179319 : Blo 2301435 5179319 := bstep (se 1 (by rfl) ⟨3884489, by rfl⟩ : syracuseStep 5179319 = 7768979) B7768979
theorem B3452879 : Blo 2301435 3452879 := bstep (se 1 (by rfl) ⟨2589659, by rfl⟩ : syracuseStep 3452879 = 5179319) B5179319
theorem B2301919 : Blo 2301435 2301919 := bstep (se 1 (by rfl) ⟨1726439, by rfl⟩ : syracuseStep 2301919 = 3452879) B3452879
theorem B3452885 : Blo 2301435 3452885 := bbase (se 7 (by rfl) ⟨40463, by rfl⟩ : syracuseStep 3452885 = 80927) (by norm_num)
theorem B2301923 : Blo 2301435 2301923 := bstep (se 1 (by rfl) ⟨1726442, by rfl⟩ : syracuseStep 2301923 = 3452885) B3452885
theorem B8740133 : Blo 2301435 8740133 := bbase (se 4 (by rfl) ⟨819387, by rfl⟩ : syracuseStep 8740133 = 1638775) (by norm_num)
theorem B5826755 : Blo 2301435 5826755 := bstep (se 1 (by rfl) ⟨4370066, by rfl⟩ : syracuseStep 5826755 = 8740133) B8740133
theorem B3884503 : Blo 2301435 3884503 := bstep (se 1 (by rfl) ⟨2913377, by rfl⟩ : syracuseStep 3884503 = 5826755) B5826755
theorem B5179337 : Blo 2301435 5179337 := bstep (se 2 (by rfl) ⟨1942251, by rfl⟩ : syracuseStep 5179337 = 3884503) B3884503
theorem B3452891 : Blo 2301435 3452891 := bstep (se 1 (by rfl) ⟨2589668, by rfl⟩ : syracuseStep 3452891 = 5179337) B5179337
theorem B2301927 : Blo 2301435 2301927 := bstep (se 1 (by rfl) ⟨1726445, by rfl⟩ : syracuseStep 2301927 = 3452891) B3452891
theorem B2589673 : Blo 2301435 2589673 := bbase (se 2 (by rfl) ⟨971127, by rfl⟩ : syracuseStep 2589673 = 1942255) (by norm_num)
theorem B3452897 : Blo 2301435 3452897 := bstep (se 2 (by rfl) ⟨1294836, by rfl⟩ : syracuseStep 3452897 = 2589673) B2589673
theorem B2301931 : Blo 2301435 2301931 := bstep (se 1 (by rfl) ⟨1726448, by rfl⟩ : syracuseStep 2301931 = 3452897) B3452897
theorem B4148165 : Blo 2301435 4148165 := bbase (se 4 (by rfl) ⟨388890, by rfl⟩ : syracuseStep 4148165 = 777781) (by norm_num)
theorem B2765443 : Blo 2301435 2765443 := bstep (se 1 (by rfl) ⟨2074082, by rfl⟩ : syracuseStep 2765443 = 4148165) B4148165
theorem B3687257 : Blo 2301435 3687257 := bstep (se 2 (by rfl) ⟨1382721, by rfl⟩ : syracuseStep 3687257 = 2765443) B2765443
theorem B2458171 : Blo 2301435 2458171 := bstep (se 1 (by rfl) ⟨1843628, by rfl⟩ : syracuseStep 2458171 = 3687257) B3687257
theorem B13110245 : Blo 2301435 13110245 := bstep (se 4 (by rfl) ⟨1229085, by rfl⟩ : syracuseStep 13110245 = 2458171) B2458171
theorem B8740163 : Blo 2301435 8740163 := bstep (se 1 (by rfl) ⟨6555122, by rfl⟩ : syracuseStep 8740163 = 13110245) B13110245
theorem B5826775 : Blo 2301435 5826775 := bstep (se 1 (by rfl) ⟨4370081, by rfl⟩ : syracuseStep 5826775 = 8740163) B8740163
theorem B7769033 : Blo 2301435 7769033 := bstep (se 2 (by rfl) ⟨2913387, by rfl⟩ : syracuseStep 7769033 = 5826775) B5826775
theorem B5179355 : Blo 2301435 5179355 := bstep (se 1 (by rfl) ⟨3884516, by rfl⟩ : syracuseStep 5179355 = 7769033) B7769033
theorem B3452903 : Blo 2301435 3452903 := bstep (se 1 (by rfl) ⟨2589677, by rfl⟩ : syracuseStep 3452903 = 5179355) B5179355
theorem B2301935 : Blo 2301435 2301935 := bstep (se 1 (by rfl) ⟨1726451, by rfl⟩ : syracuseStep 2301935 = 3452903) B3452903
theorem B3452909 : Blo 2301435 3452909 := bbase (se 3 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 3452909 = 1294841) (by norm_num)
theorem B2301939 : Blo 2301435 2301939 := bstep (se 1 (by rfl) ⟨1726454, by rfl⟩ : syracuseStep 2301939 = 3452909) B3452909
theorem B5179373 : Blo 2301435 5179373 := bbase (se 3 (by rfl) ⟨971132, by rfl⟩ : syracuseStep 5179373 = 1942265) (by norm_num)
theorem B3452915 : Blo 2301435 3452915 := bstep (se 1 (by rfl) ⟨2589686, by rfl⟩ : syracuseStep 3452915 = 5179373) B5179373
theorem B2301943 : Blo 2301435 2301943 := bstep (se 1 (by rfl) ⟨1726457, by rfl⟩ : syracuseStep 2301943 = 3452915) B3452915
theorem B3687277 : Blo 2301435 3687277 := bbase (se 3 (by rfl) ⟨691364, by rfl⟩ : syracuseStep 3687277 = 1382729) (by norm_num)
theorem B4916369 : Blo 2301435 4916369 := bstep (se 2 (by rfl) ⟨1843638, by rfl⟩ : syracuseStep 4916369 = 3687277) B3687277
theorem B3277579 : Blo 2301435 3277579 := bstep (se 1 (by rfl) ⟨2458184, by rfl⟩ : syracuseStep 3277579 = 4916369) B4916369
theorem B4370105 : Blo 2301435 4370105 := bstep (se 2 (by rfl) ⟨1638789, by rfl⟩ : syracuseStep 4370105 = 3277579) B3277579
theorem B2913403 : Blo 2301435 2913403 := bstep (se 1 (by rfl) ⟨2185052, by rfl⟩ : syracuseStep 2913403 = 4370105) B4370105
theorem B3884537 : Blo 2301435 3884537 := bstep (se 2 (by rfl) ⟨1456701, by rfl⟩ : syracuseStep 3884537 = 2913403) B2913403
theorem B2589691 : Blo 2301435 2589691 := bstep (se 1 (by rfl) ⟨1942268, by rfl⟩ : syracuseStep 2589691 = 3884537) B3884537
theorem B3452921 : Blo 2301435 3452921 := bstep (se 2 (by rfl) ⟨1294845, by rfl⟩ : syracuseStep 3452921 = 2589691) B2589691
theorem B2301947 : Blo 2301435 2301947 := bstep (se 1 (by rfl) ⟨1726460, by rfl⟩ : syracuseStep 2301947 = 3452921) B3452921
theorem B2365193 : Blo 2301435 2365193 := bbase (se 2 (by rfl) ⟨886947, by rfl⟩ : syracuseStep 2365193 = 1773895) (by norm_num)
theorem B6307181 : Blo 2301435 6307181 := bstep (se 3 (by rfl) ⟨1182596, by rfl⟩ : syracuseStep 6307181 = 2365193) B2365193
theorem B67276597 : Blo 2301435 67276597 := bstep (se 5 (by rfl) ⟨3153590, by rfl⟩ : syracuseStep 67276597 = 6307181) B6307181
theorem B89702129 : Blo 2301435 89702129 := bstep (se 2 (by rfl) ⟨33638298, by rfl⟩ : syracuseStep 89702129 = 67276597) B67276597
theorem B59801419 : Blo 2301435 59801419 := bstep (se 1 (by rfl) ⟨44851064, by rfl⟩ : syracuseStep 59801419 = 89702129) B89702129
theorem B79735225 : Blo 2301435 79735225 := bstep (se 2 (by rfl) ⟨29900709, by rfl⟩ : syracuseStep 79735225 = 59801419) B59801419
theorem B106313633 : Blo 2301435 106313633 := bstep (se 2 (by rfl) ⟨39867612, by rfl⟩ : syracuseStep 106313633 = 79735225) B79735225
theorem B70875755 : Blo 2301435 70875755 := bstep (se 1 (by rfl) ⟨53156816, by rfl⟩ : syracuseStep 70875755 = 106313633) B106313633
theorem B47250503 : Blo 2301435 47250503 := bstep (se 1 (by rfl) ⟨35437877, by rfl⟩ : syracuseStep 47250503 = 70875755) B70875755
theorem B31500335 : Blo 2301435 31500335 := bstep (se 1 (by rfl) ⟨23625251, by rfl⟩ : syracuseStep 31500335 = 47250503) B47250503
theorem B84000893 : Blo 2301435 84000893 := bstep (se 3 (by rfl) ⟨15750167, by rfl⟩ : syracuseStep 84000893 = 31500335) B31500335
theorem B224002381 : Blo 2301435 224002381 := bstep (se 3 (by rfl) ⟨42000446, by rfl⟩ : syracuseStep 224002381 = 84000893) B84000893
theorem B298669841 : Blo 2301435 298669841 := bstep (se 2 (by rfl) ⟨112001190, by rfl⟩ : syracuseStep 298669841 = 224002381) B224002381
theorem B199113227 : Blo 2301435 199113227 := bstep (se 1 (by rfl) ⟨149334920, by rfl⟩ : syracuseStep 199113227 = 298669841) B298669841
theorem B132742151 : Blo 2301435 132742151 := bstep (se 1 (by rfl) ⟨99556613, by rfl⟩ : syracuseStep 132742151 = 199113227) B199113227
theorem B88494767 : Blo 2301435 88494767 := bstep (se 1 (by rfl) ⟨66371075, by rfl⟩ : syracuseStep 88494767 = 132742151) B132742151
theorem B58996511 : Blo 2301435 58996511 := bstep (se 1 (by rfl) ⟨44247383, by rfl⟩ : syracuseStep 58996511 = 88494767) B88494767
theorem B39331007 : Blo 2301435 39331007 := bstep (se 1 (by rfl) ⟨29498255, by rfl⟩ : syracuseStep 39331007 = 58996511) B58996511
theorem B26220671 : Blo 2301435 26220671 := bstep (se 1 (by rfl) ⟨19665503, by rfl⟩ : syracuseStep 26220671 = 39331007) B39331007
theorem B17480447 : Blo 2301435 17480447 := bstep (se 1 (by rfl) ⟨13110335, by rfl⟩ : syracuseStep 17480447 = 26220671) B26220671
theorem B11653631 : Blo 2301435 11653631 := bstep (se 1 (by rfl) ⟨8740223, by rfl⟩ : syracuseStep 11653631 = 17480447) B17480447
theorem B7769087 : Blo 2301435 7769087 := bstep (se 1 (by rfl) ⟨5826815, by rfl⟩ : syracuseStep 7769087 = 11653631) B11653631
theorem B5179391 : Blo 2301435 5179391 := bstep (se 1 (by rfl) ⟨3884543, by rfl⟩ : syracuseStep 5179391 = 7769087) B7769087
theorem B3452927 : Blo 2301435 3452927 := bstep (se 1 (by rfl) ⟨2589695, by rfl⟩ : syracuseStep 3452927 = 5179391) B5179391
theorem B2301951 : Blo 2301435 2301951 := bstep (se 1 (by rfl) ⟨1726463, by rfl⟩ : syracuseStep 2301951 = 3452927) B3452927
theorem B3452933 : Blo 2301435 3452933 := bbase (se 4 (by rfl) ⟨323712, by rfl⟩ : syracuseStep 3452933 = 647425) (by norm_num)
theorem B2301955 : Blo 2301435 2301955 := bstep (se 1 (by rfl) ⟨1726466, by rfl⟩ : syracuseStep 2301955 = 3452933) B3452933
theorem B3884557 : Blo 2301435 3884557 := bbase (se 3 (by rfl) ⟨728354, by rfl⟩ : syracuseStep 3884557 = 1456709) (by norm_num)
theorem B5179409 : Blo 2301435 5179409 := bstep (se 2 (by rfl) ⟨1942278, by rfl⟩ : syracuseStep 5179409 = 3884557) B3884557
theorem B3452939 : Blo 2301435 3452939 := bstep (se 1 (by rfl) ⟨2589704, by rfl⟩ : syracuseStep 3452939 = 5179409) B5179409
theorem B2301959 : Blo 2301435 2301959 := bstep (se 1 (by rfl) ⟨1726469, by rfl⟩ : syracuseStep 2301959 = 3452939) B3452939
theorem B2589709 : Blo 2301435 2589709 := bbase (se 3 (by rfl) ⟨485570, by rfl⟩ : syracuseStep 2589709 = 971141) (by norm_num)
theorem B3452945 : Blo 2301435 3452945 := bstep (se 2 (by rfl) ⟨1294854, by rfl⟩ : syracuseStep 3452945 = 2589709) B2589709
theorem B2301963 : Blo 2301435 2301963 := bstep (se 1 (by rfl) ⟨1726472, by rfl⟩ : syracuseStep 2301963 = 3452945) B3452945
theorem B7769141 : Blo 2301435 7769141 := bbase (se 5 (by rfl) ⟨364178, by rfl⟩ : syracuseStep 7769141 = 728357) (by norm_num)
theorem B5179427 : Blo 2301435 5179427 := bstep (se 1 (by rfl) ⟨3884570, by rfl⟩ : syracuseStep 5179427 = 7769141) B7769141
theorem B3452951 : Blo 2301435 3452951 := bstep (se 1 (by rfl) ⟨2589713, by rfl⟩ : syracuseStep 3452951 = 5179427) B5179427
theorem B2301967 : Blo 2301435 2301967 := bstep (se 1 (by rfl) ⟨1726475, by rfl⟩ : syracuseStep 2301967 = 3452951) B3452951
theorem B3452957 : Blo 2301435 3452957 := bbase (se 3 (by rfl) ⟨647429, by rfl⟩ : syracuseStep 3452957 = 1294859) (by norm_num)
theorem B2301971 : Blo 2301435 2301971 := bstep (se 1 (by rfl) ⟨1726478, by rfl⟩ : syracuseStep 2301971 = 3452957) B3452957
theorem B5179445 : Blo 2301435 5179445 := bbase (se 5 (by rfl) ⟨242786, by rfl⟩ : syracuseStep 5179445 = 485573) (by norm_num)
theorem B3452963 : Blo 2301435 3452963 := bstep (se 1 (by rfl) ⟨2589722, by rfl⟩ : syracuseStep 3452963 = 5179445) B5179445
theorem B2301975 : Blo 2301435 2301975 := bstep (se 1 (by rfl) ⟨1726481, by rfl⟩ : syracuseStep 2301975 = 3452963) B3452963
theorem B5986973 : Blo 2301435 5986973 := bbase (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) (by norm_num)
theorem B15965261 : Blo 2301435 15965261 := bstep (se 3 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 15965261 = 5986973) B5986973
theorem B10643507 : Blo 2301435 10643507 := bstep (se 1 (by rfl) ⟨7982630, by rfl⟩ : syracuseStep 10643507 = 15965261) B15965261
theorem B7095671 : Blo 2301435 7095671 := bstep (se 1 (by rfl) ⟨5321753, by rfl⟩ : syracuseStep 7095671 = 10643507) B10643507
theorem B4730447 : Blo 2301435 4730447 := bstep (se 1 (by rfl) ⟨3547835, by rfl⟩ : syracuseStep 4730447 = 7095671) B7095671
theorem B12614525 : Blo 2301435 12614525 := bstep (se 3 (by rfl) ⟨2365223, by rfl⟩ : syracuseStep 12614525 = 4730447) B4730447
theorem B8409683 : Blo 2301435 8409683 := bstep (se 1 (by rfl) ⟨6307262, by rfl⟩ : syracuseStep 8409683 = 12614525) B12614525
theorem B5606455 : Blo 2301435 5606455 := bstep (se 1 (by rfl) ⟨4204841, by rfl⟩ : syracuseStep 5606455 = 8409683) B8409683
theorem B7475273 : Blo 2301435 7475273 := bstep (se 2 (by rfl) ⟨2803227, by rfl⟩ : syracuseStep 7475273 = 5606455) B5606455
theorem B4983515 : Blo 2301435 4983515 := bstep (se 1 (by rfl) ⟨3737636, by rfl⟩ : syracuseStep 4983515 = 7475273) B7475273
theorem B3322343 : Blo 2301435 3322343 := bstep (se 1 (by rfl) ⟨2491757, by rfl⟩ : syracuseStep 3322343 = 4983515) B4983515
theorem B8859581 : Blo 2301435 8859581 := bstep (se 3 (by rfl) ⟨1661171, by rfl⟩ : syracuseStep 8859581 = 3322343) B3322343
theorem B5906387 : Blo 2301435 5906387 := bstep (se 1 (by rfl) ⟨4429790, by rfl⟩ : syracuseStep 5906387 = 8859581) B8859581
theorem B3937591 : Blo 2301435 3937591 := bstep (se 1 (by rfl) ⟨2953193, by rfl⟩ : syracuseStep 3937591 = 5906387) B5906387
theorem B21000485 : Blo 2301435 21000485 := bstep (se 4 (by rfl) ⟨1968795, by rfl⟩ : syracuseStep 21000485 = 3937591) B3937591
theorem B56001293 : Blo 2301435 56001293 := bstep (se 3 (by rfl) ⟨10500242, by rfl⟩ : syracuseStep 56001293 = 21000485) B21000485
theorem B37334195 : Blo 2301435 37334195 := bstep (se 1 (by rfl) ⟨28000646, by rfl⟩ : syracuseStep 37334195 = 56001293) B56001293
theorem B24889463 : Blo 2301435 24889463 := bstep (se 1 (by rfl) ⟨18667097, by rfl⟩ : syracuseStep 24889463 = 37334195) B37334195
theorem B16592975 : Blo 2301435 16592975 := bstep (se 1 (by rfl) ⟨12444731, by rfl⟩ : syracuseStep 16592975 = 24889463) B24889463
theorem B11061983 : Blo 2301435 11061983 := bstep (se 1 (by rfl) ⟨8296487, by rfl⟩ : syracuseStep 11061983 = 16592975) B16592975
theorem B7374655 : Blo 2301435 7374655 := bstep (se 1 (by rfl) ⟨5530991, by rfl⟩ : syracuseStep 7374655 = 11061983) B11061983
theorem B9832873 : Blo 2301435 9832873 := bstep (se 2 (by rfl) ⟨3687327, by rfl⟩ : syracuseStep 9832873 = 7374655) B7374655
theorem B13110497 : Blo 2301435 13110497 := bstep (se 2 (by rfl) ⟨4916436, by rfl⟩ : syracuseStep 13110497 = 9832873) B9832873
theorem B8740331 : Blo 2301435 8740331 := bstep (se 1 (by rfl) ⟨6555248, by rfl⟩ : syracuseStep 8740331 = 13110497) B13110497
theorem B5826887 : Blo 2301435 5826887 := bstep (se 1 (by rfl) ⟨4370165, by rfl⟩ : syracuseStep 5826887 = 8740331) B8740331
theorem B3884591 : Blo 2301435 3884591 := bstep (se 1 (by rfl) ⟨2913443, by rfl⟩ : syracuseStep 3884591 = 5826887) B5826887
theorem B2589727 : Blo 2301435 2589727 := bstep (se 1 (by rfl) ⟨1942295, by rfl⟩ : syracuseStep 2589727 = 3884591) B3884591
theorem B3452969 : Blo 2301435 3452969 := bstep (se 2 (by rfl) ⟨1294863, by rfl⟩ : syracuseStep 3452969 = 2589727) B2589727
theorem B2301979 : Blo 2301435 2301979 := bstep (se 1 (by rfl) ⟨1726484, by rfl⟩ : syracuseStep 2301979 = 3452969) B3452969
theorem B8296501 : Blo 2301435 8296501 := bbase (se 5 (by rfl) ⟨388898, by rfl⟩ : syracuseStep 8296501 = 777797) (by norm_num)
theorem B11062001 : Blo 2301435 11062001 := bstep (se 2 (by rfl) ⟨4148250, by rfl⟩ : syracuseStep 11062001 = 8296501) B8296501
theorem B7374667 : Blo 2301435 7374667 := bstep (se 1 (by rfl) ⟨5531000, by rfl⟩ : syracuseStep 7374667 = 11062001) B11062001
theorem B9832889 : Blo 2301435 9832889 := bstep (se 2 (by rfl) ⟨3687333, by rfl⟩ : syracuseStep 9832889 = 7374667) B7374667
theorem B6555259 : Blo 2301435 6555259 := bstep (se 1 (by rfl) ⟨4916444, by rfl⟩ : syracuseStep 6555259 = 9832889) B9832889
theorem B8740345 : Blo 2301435 8740345 := bstep (se 2 (by rfl) ⟨3277629, by rfl⟩ : syracuseStep 8740345 = 6555259) B6555259
theorem B11653793 : Blo 2301435 11653793 := bstep (se 2 (by rfl) ⟨4370172, by rfl⟩ : syracuseStep 11653793 = 8740345) B8740345
theorem B7769195 : Blo 2301435 7769195 := bstep (se 1 (by rfl) ⟨5826896, by rfl⟩ : syracuseStep 7769195 = 11653793) B11653793
theorem B5179463 : Blo 2301435 5179463 := bstep (se 1 (by rfl) ⟨3884597, by rfl⟩ : syracuseStep 5179463 = 7769195) B7769195
theorem B3452975 : Blo 2301435 3452975 := bstep (se 1 (by rfl) ⟨2589731, by rfl⟩ : syracuseStep 3452975 = 5179463) B5179463
theorem B2301983 : Blo 2301435 2301983 := bstep (se 1 (by rfl) ⟨1726487, by rfl⟩ : syracuseStep 2301983 = 3452975) B3452975
theorem B3452981 : Blo 2301435 3452981 := bbase (se 5 (by rfl) ⟨161858, by rfl⟩ : syracuseStep 3452981 = 323717) (by norm_num)
theorem B2301987 : Blo 2301435 2301987 := bstep (se 1 (by rfl) ⟨1726490, by rfl⟩ : syracuseStep 2301987 = 3452981) B3452981
theorem B5826917 : Blo 2301435 5826917 := bbase (se 4 (by rfl) ⟨546273, by rfl⟩ : syracuseStep 5826917 = 1092547) (by norm_num)
theorem B3884611 : Blo 2301435 3884611 := bstep (se 1 (by rfl) ⟨2913458, by rfl⟩ : syracuseStep 3884611 = 5826917) B5826917
theorem B5179481 : Blo 2301435 5179481 := bstep (se 2 (by rfl) ⟨1942305, by rfl⟩ : syracuseStep 5179481 = 3884611) B3884611
theorem B3452987 : Blo 2301435 3452987 := bstep (se 1 (by rfl) ⟨2589740, by rfl⟩ : syracuseStep 3452987 = 5179481) B5179481
theorem B2301991 : Blo 2301435 2301991 := bstep (se 1 (by rfl) ⟨1726493, by rfl⟩ : syracuseStep 2301991 = 3452987) B3452987
theorem B2589745 : Blo 2301435 2589745 := bbase (se 2 (by rfl) ⟨971154, by rfl⟩ : syracuseStep 2589745 = 1942309) (by norm_num)
theorem B3452993 : Blo 2301435 3452993 := bstep (se 2 (by rfl) ⟨1294872, by rfl⟩ : syracuseStep 3452993 = 2589745) B2589745
theorem B2301995 : Blo 2301435 2301995 := bstep (se 1 (by rfl) ⟨1726496, by rfl⟩ : syracuseStep 2301995 = 3452993) B3452993
theorem B4983557 : Blo 2301435 4983557 := bbase (se 4 (by rfl) ⟨467208, by rfl⟩ : syracuseStep 4983557 = 934417) (by norm_num)
theorem B53157941 : Blo 2301435 53157941 := bstep (se 5 (by rfl) ⟨2491778, by rfl⟩ : syracuseStep 53157941 = 4983557) B4983557
theorem B35438627 : Blo 2301435 35438627 := bstep (se 1 (by rfl) ⟨26578970, by rfl⟩ : syracuseStep 35438627 = 53157941) B53157941
theorem B23625751 : Blo 2301435 23625751 := bstep (se 1 (by rfl) ⟨17719313, by rfl⟩ : syracuseStep 23625751 = 35438627) B35438627
theorem B31501001 : Blo 2301435 31501001 := bstep (se 2 (by rfl) ⟨11812875, by rfl⟩ : syracuseStep 31501001 = 23625751) B23625751
theorem B84002669 : Blo 2301435 84002669 := bstep (se 3 (by rfl) ⟨15750500, by rfl⟩ : syracuseStep 84002669 = 31501001) B31501001
theorem B56001779 : Blo 2301435 56001779 := bstep (se 1 (by rfl) ⟨42001334, by rfl⟩ : syracuseStep 56001779 = 84002669) B84002669
theorem B37334519 : Blo 2301435 37334519 := bstep (se 1 (by rfl) ⟨28000889, by rfl⟩ : syracuseStep 37334519 = 56001779) B56001779
theorem B24889679 : Blo 2301435 24889679 := bstep (se 1 (by rfl) ⟨18667259, by rfl⟩ : syracuseStep 24889679 = 37334519) B37334519
theorem B16593119 : Blo 2301435 16593119 := bstep (se 1 (by rfl) ⟨12444839, by rfl⟩ : syracuseStep 16593119 = 24889679) B24889679
theorem B11062079 : Blo 2301435 11062079 := bstep (se 1 (by rfl) ⟨8296559, by rfl⟩ : syracuseStep 11062079 = 16593119) B16593119
theorem B7374719 : Blo 2301435 7374719 := bstep (se 1 (by rfl) ⟨5531039, by rfl⟩ : syracuseStep 7374719 = 11062079) B11062079
theorem B4916479 : Blo 2301435 4916479 := bstep (se 1 (by rfl) ⟨3687359, by rfl⟩ : syracuseStep 4916479 = 7374719) B7374719
theorem B6555305 : Blo 2301435 6555305 := bstep (se 2 (by rfl) ⟨2458239, by rfl⟩ : syracuseStep 6555305 = 4916479) B4916479
theorem B4370203 : Blo 2301435 4370203 := bstep (se 1 (by rfl) ⟨3277652, by rfl⟩ : syracuseStep 4370203 = 6555305) B6555305
theorem B5826937 : Blo 2301435 5826937 := bstep (se 2 (by rfl) ⟨2185101, by rfl⟩ : syracuseStep 5826937 = 4370203) B4370203
theorem B7769249 : Blo 2301435 7769249 := bstep (se 2 (by rfl) ⟨2913468, by rfl⟩ : syracuseStep 7769249 = 5826937) B5826937
theorem B5179499 : Blo 2301435 5179499 := bstep (se 1 (by rfl) ⟨3884624, by rfl⟩ : syracuseStep 5179499 = 7769249) B7769249
theorem B3452999 : Blo 2301435 3452999 := bstep (se 1 (by rfl) ⟨2589749, by rfl⟩ : syracuseStep 3452999 = 5179499) B5179499
theorem B2301999 : Blo 2301435 2301999 := bstep (se 1 (by rfl) ⟨1726499, by rfl⟩ : syracuseStep 2301999 = 3452999) B3452999
theorem B3453005 : Blo 2301435 3453005 := bbase (se 3 (by rfl) ⟨647438, by rfl⟩ : syracuseStep 3453005 = 1294877) (by norm_num)
theorem B2302003 : Blo 2301435 2302003 := bstep (se 1 (by rfl) ⟨1726502, by rfl⟩ : syracuseStep 2302003 = 3453005) B3453005
theorem B5179517 : Blo 2301435 5179517 := bbase (se 3 (by rfl) ⟨971159, by rfl⟩ : syracuseStep 5179517 = 1942319) (by norm_num)
theorem B3453011 : Blo 2301435 3453011 := bstep (se 1 (by rfl) ⟨2589758, by rfl⟩ : syracuseStep 3453011 = 5179517) B5179517
theorem B2302007 : Blo 2301435 2302007 := bstep (se 1 (by rfl) ⟨1726505, by rfl⟩ : syracuseStep 2302007 = 3453011) B3453011
theorem B3884645 : Blo 2301435 3884645 := bbase (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) (by norm_num)
theorem B2589763 : Blo 2301435 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B3453017 : Blo 2301435 3453017 := bstep (se 2 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 3453017 = 2589763) B2589763
theorem B2302011 : Blo 2301435 2302011 := bstep (se 1 (by rfl) ⟨1726508, by rfl⟩ : syracuseStep 2302011 = 3453017) B3453017
theorem B4148309 : Blo 2301435 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B2765539 : Blo 2301435 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B3687385 : Blo 2301435 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B4916513 : Blo 2301435 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B3277675 : Blo 2301435 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B17480933 : Blo 2301435 17480933 := bstep (se 4 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 17480933 = 3277675) B3277675
theorem B11653955 : Blo 2301435 11653955 := bstep (se 1 (by rfl) ⟨8740466, by rfl⟩ : syracuseStep 11653955 = 17480933) B17480933
theorem B7769303 : Blo 2301435 7769303 := bstep (se 1 (by rfl) ⟨5826977, by rfl⟩ : syracuseStep 7769303 = 11653955) B11653955
theorem B5179535 : Blo 2301435 5179535 := bstep (se 1 (by rfl) ⟨3884651, by rfl⟩ : syracuseStep 5179535 = 7769303) B7769303
theorem B3453023 : Blo 2301435 3453023 := bstep (se 1 (by rfl) ⟨2589767, by rfl⟩ : syracuseStep 3453023 = 5179535) B5179535
theorem B2302015 : Blo 2301435 2302015 := bstep (se 1 (by rfl) ⟨1726511, by rfl⟩ : syracuseStep 2302015 = 3453023) B3453023
theorem B3453029 : Blo 2301435 3453029 := bbase (se 4 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 3453029 = 647443) (by norm_num)
theorem B2302019 : Blo 2301435 2302019 := bstep (se 1 (by rfl) ⟨1726514, by rfl⟩ : syracuseStep 2302019 = 3453029) B3453029
theorem B2765549 : Blo 2301435 2765549 := bbase (se 3 (by rfl) ⟨518540, by rfl⟩ : syracuseStep 2765549 = 1037081) (by norm_num)
theorem B7374797 : Blo 2301435 7374797 := bstep (se 3 (by rfl) ⟨1382774, by rfl⟩ : syracuseStep 7374797 = 2765549) B2765549
theorem B4916531 : Blo 2301435 4916531 := bstep (se 1 (by rfl) ⟨3687398, by rfl⟩ : syracuseStep 4916531 = 7374797) B7374797
theorem B3277687 : Blo 2301435 3277687 := bstep (se 1 (by rfl) ⟨2458265, by rfl⟩ : syracuseStep 3277687 = 4916531) B4916531
theorem B4370249 : Blo 2301435 4370249 := bstep (se 2 (by rfl) ⟨1638843, by rfl⟩ : syracuseStep 4370249 = 3277687) B3277687
theorem B2913499 : Blo 2301435 2913499 := bstep (se 1 (by rfl) ⟨2185124, by rfl⟩ : syracuseStep 2913499 = 4370249) B4370249
theorem B3884665 : Blo 2301435 3884665 := bstep (se 2 (by rfl) ⟨1456749, by rfl⟩ : syracuseStep 3884665 = 2913499) B2913499
theorem B5179553 : Blo 2301435 5179553 := bstep (se 2 (by rfl) ⟨1942332, by rfl⟩ : syracuseStep 5179553 = 3884665) B3884665
theorem B3453035 : Blo 2301435 3453035 := bstep (se 1 (by rfl) ⟨2589776, by rfl⟩ : syracuseStep 3453035 = 5179553) B5179553
theorem B2302023 : Blo 2301435 2302023 := bstep (se 1 (by rfl) ⟨1726517, by rfl⟩ : syracuseStep 2302023 = 3453035) B3453035
theorem B2589781 : Blo 2301435 2589781 := bbase (se 8 (by rfl) ⟨15174, by rfl⟩ : syracuseStep 2589781 = 30349) (by norm_num)
theorem B3453041 : Blo 2301435 3453041 := bstep (se 2 (by rfl) ⟨1294890, by rfl⟩ : syracuseStep 3453041 = 2589781) B2589781
theorem B2302027 : Blo 2301435 2302027 := bstep (se 1 (by rfl) ⟨1726520, by rfl⟩ : syracuseStep 2302027 = 3453041) B3453041
theorem B2913509 : Blo 2301435 2913509 := bbase (se 4 (by rfl) ⟨273141, by rfl⟩ : syracuseStep 2913509 = 546283) (by norm_num)
theorem B7769357 : Blo 2301435 7769357 := bstep (se 3 (by rfl) ⟨1456754, by rfl⟩ : syracuseStep 7769357 = 2913509) B2913509
theorem B5179571 : Blo 2301435 5179571 := bstep (se 1 (by rfl) ⟨3884678, by rfl⟩ : syracuseStep 5179571 = 7769357) B7769357
theorem B3453047 : Blo 2301435 3453047 := bstep (se 1 (by rfl) ⟨2589785, by rfl⟩ : syracuseStep 3453047 = 5179571) B5179571
theorem B2302031 : Blo 2301435 2302031 := bstep (se 1 (by rfl) ⟨1726523, by rfl⟩ : syracuseStep 2302031 = 3453047) B3453047
theorem B3453053 : Blo 2301435 3453053 := bbase (se 3 (by rfl) ⟨647447, by rfl⟩ : syracuseStep 3453053 = 1294895) (by norm_num)
theorem B2302035 : Blo 2301435 2302035 := bstep (se 1 (by rfl) ⟨1726526, by rfl⟩ : syracuseStep 2302035 = 3453053) B3453053
theorem B5179589 : Blo 2301435 5179589 := bbase (se 4 (by rfl) ⟨485586, by rfl⟩ : syracuseStep 5179589 = 971173) (by norm_num)
theorem B3453059 : Blo 2301435 3453059 := bstep (se 1 (by rfl) ⟨2589794, by rfl⟩ : syracuseStep 3453059 = 5179589) B5179589
theorem B2302039 : Blo 2301435 2302039 := bstep (se 1 (by rfl) ⟨1726529, by rfl⟩ : syracuseStep 2302039 = 3453059) B3453059
theorem B7000357 : Blo 2301435 7000357 := bbase (se 4 (by rfl) ⟨656283, by rfl⟩ : syracuseStep 7000357 = 1312567) (by norm_num)
theorem B9333809 : Blo 2301435 9333809 := bstep (se 2 (by rfl) ⟨3500178, by rfl⟩ : syracuseStep 9333809 = 7000357) B7000357
theorem B6222539 : Blo 2301435 6222539 := bstep (se 1 (by rfl) ⟨4666904, by rfl⟩ : syracuseStep 6222539 = 9333809) B9333809
theorem B16593437 : Blo 2301435 16593437 := bstep (se 3 (by rfl) ⟨3111269, by rfl⟩ : syracuseStep 16593437 = 6222539) B6222539
theorem B11062291 : Blo 2301435 11062291 := bstep (se 1 (by rfl) ⟨8296718, by rfl⟩ : syracuseStep 11062291 = 16593437) B16593437
theorem B14749721 : Blo 2301435 14749721 := bstep (se 2 (by rfl) ⟨5531145, by rfl⟩ : syracuseStep 14749721 = 11062291) B11062291
theorem B9833147 : Blo 2301435 9833147 := bstep (se 1 (by rfl) ⟨7374860, by rfl⟩ : syracuseStep 9833147 = 14749721) B14749721
theorem B6555431 : Blo 2301435 6555431 := bstep (se 1 (by rfl) ⟨4916573, by rfl⟩ : syracuseStep 6555431 = 9833147) B9833147
theorem B4370287 : Blo 2301435 4370287 := bstep (se 1 (by rfl) ⟨3277715, by rfl⟩ : syracuseStep 4370287 = 6555431) B6555431
theorem B5827049 : Blo 2301435 5827049 := bstep (se 2 (by rfl) ⟨2185143, by rfl⟩ : syracuseStep 5827049 = 4370287) B4370287
theorem B3884699 : Blo 2301435 3884699 := bstep (se 1 (by rfl) ⟨2913524, by rfl⟩ : syracuseStep 3884699 = 5827049) B5827049
theorem B2589799 : Blo 2301435 2589799 := bstep (se 1 (by rfl) ⟨1942349, by rfl⟩ : syracuseStep 2589799 = 3884699) B3884699
theorem B3453065 : Blo 2301435 3453065 := bstep (se 2 (by rfl) ⟨1294899, by rfl⟩ : syracuseStep 3453065 = 2589799) B2589799
theorem B2302043 : Blo 2301435 2302043 := bstep (se 1 (by rfl) ⟨1726532, by rfl⟩ : syracuseStep 2302043 = 3453065) B3453065
theorem B11654117 : Blo 2301435 11654117 := bbase (se 4 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 11654117 = 2185147) (by norm_num)
theorem B7769411 : Blo 2301435 7769411 := bstep (se 1 (by rfl) ⟨5827058, by rfl⟩ : syracuseStep 7769411 = 11654117) B11654117
theorem B5179607 : Blo 2301435 5179607 := bstep (se 1 (by rfl) ⟨3884705, by rfl⟩ : syracuseStep 5179607 = 7769411) B7769411
theorem B3453071 : Blo 2301435 3453071 := bstep (se 1 (by rfl) ⟨2589803, by rfl⟩ : syracuseStep 3453071 = 5179607) B5179607
theorem B2302047 : Blo 2301435 2302047 := bstep (se 1 (by rfl) ⟨1726535, by rfl⟩ : syracuseStep 2302047 = 3453071) B3453071
theorem B3453077 : Blo 2301435 3453077 := bbase (se 6 (by rfl) ⟨80931, by rfl⟩ : syracuseStep 3453077 = 161863) (by norm_num)
theorem B2302051 : Blo 2301435 2302051 := bstep (se 1 (by rfl) ⟨1726538, by rfl⟩ : syracuseStep 2302051 = 3453077) B3453077
theorem B4148381 : Blo 2301435 4148381 := bbase (se 3 (by rfl) ⟨777821, by rfl⟩ : syracuseStep 4148381 = 1555643) (by norm_num)
theorem B2765587 : Blo 2301435 2765587 := bstep (se 1 (by rfl) ⟨2074190, by rfl⟩ : syracuseStep 2765587 = 4148381) B4148381
theorem B3687449 : Blo 2301435 3687449 := bstep (se 2 (by rfl) ⟨1382793, by rfl⟩ : syracuseStep 3687449 = 2765587) B2765587
theorem B9833197 : Blo 2301435 9833197 := bstep (se 3 (by rfl) ⟨1843724, by rfl⟩ : syracuseStep 9833197 = 3687449) B3687449
theorem B13110929 : Blo 2301435 13110929 := bstep (se 2 (by rfl) ⟨4916598, by rfl⟩ : syracuseStep 13110929 = 9833197) B9833197
theorem B8740619 : Blo 2301435 8740619 := bstep (se 1 (by rfl) ⟨6555464, by rfl⟩ : syracuseStep 8740619 = 13110929) B13110929
theorem B5827079 : Blo 2301435 5827079 := bstep (se 1 (by rfl) ⟨4370309, by rfl⟩ : syracuseStep 5827079 = 8740619) B8740619
theorem B3884719 : Blo 2301435 3884719 := bstep (se 1 (by rfl) ⟨2913539, by rfl⟩ : syracuseStep 3884719 = 5827079) B5827079
theorem B5179625 : Blo 2301435 5179625 := bstep (se 2 (by rfl) ⟨1942359, by rfl⟩ : syracuseStep 5179625 = 3884719) B3884719
theorem B3453083 : Blo 2301435 3453083 := bstep (se 1 (by rfl) ⟨2589812, by rfl⟩ : syracuseStep 3453083 = 5179625) B5179625
theorem B2302055 : Blo 2301435 2302055 := bstep (se 1 (by rfl) ⟨1726541, by rfl⟩ : syracuseStep 2302055 = 3453083) B3453083
theorem B2589817 : Blo 2301435 2589817 := bbase (se 2 (by rfl) ⟨971181, by rfl⟩ : syracuseStep 2589817 = 1942363) (by norm_num)
theorem B3453089 : Blo 2301435 3453089 := bstep (se 2 (by rfl) ⟨1294908, by rfl⟩ : syracuseStep 3453089 = 2589817) B2589817
theorem B2302059 : Blo 2301435 2302059 := bstep (se 1 (by rfl) ⟨1726544, by rfl⟩ : syracuseStep 2302059 = 3453089) B3453089
theorem B33187157 : Blo 2301435 33187157 := bbase (se 12 (by rfl) ⟨12153, by rfl⟩ : syracuseStep 33187157 = 24307) (by norm_num)
theorem B22124771 : Blo 2301435 22124771 := bstep (se 1 (by rfl) ⟨16593578, by rfl⟩ : syracuseStep 22124771 = 33187157) B33187157
theorem B14749847 : Blo 2301435 14749847 := bstep (se 1 (by rfl) ⟨11062385, by rfl⟩ : syracuseStep 14749847 = 22124771) B22124771
theorem B9833231 : Blo 2301435 9833231 := bstep (se 1 (by rfl) ⟨7374923, by rfl⟩ : syracuseStep 9833231 = 14749847) B14749847
theorem B6555487 : Blo 2301435 6555487 := bstep (se 1 (by rfl) ⟨4916615, by rfl⟩ : syracuseStep 6555487 = 9833231) B9833231
theorem B8740649 : Blo 2301435 8740649 := bstep (se 2 (by rfl) ⟨3277743, by rfl⟩ : syracuseStep 8740649 = 6555487) B6555487
theorem B5827099 : Blo 2301435 5827099 := bstep (se 1 (by rfl) ⟨4370324, by rfl⟩ : syracuseStep 5827099 = 8740649) B8740649
theorem B7769465 : Blo 2301435 7769465 := bstep (se 2 (by rfl) ⟨2913549, by rfl⟩ : syracuseStep 7769465 = 5827099) B5827099
theorem B5179643 : Blo 2301435 5179643 := bstep (se 1 (by rfl) ⟨3884732, by rfl⟩ : syracuseStep 5179643 = 7769465) B7769465
theorem B3453095 : Blo 2301435 3453095 := bstep (se 1 (by rfl) ⟨2589821, by rfl⟩ : syracuseStep 3453095 = 5179643) B5179643
theorem B2302063 : Blo 2301435 2302063 := bstep (se 1 (by rfl) ⟨1726547, by rfl⟩ : syracuseStep 2302063 = 3453095) B3453095
theorem B3453101 : Blo 2301435 3453101 := bbase (se 3 (by rfl) ⟨647456, by rfl⟩ : syracuseStep 3453101 = 1294913) (by norm_num)
theorem B2302067 : Blo 2301435 2302067 := bstep (se 1 (by rfl) ⟨1726550, by rfl⟩ : syracuseStep 2302067 = 3453101) B3453101
theorem B5179661 : Blo 2301435 5179661 := bbase (se 3 (by rfl) ⟨971186, by rfl⟩ : syracuseStep 5179661 = 1942373) (by norm_num)
theorem B3453107 : Blo 2301435 3453107 := bstep (se 1 (by rfl) ⟨2589830, by rfl⟩ : syracuseStep 3453107 = 5179661) B5179661
theorem B2302071 : Blo 2301435 2302071 := bstep (se 1 (by rfl) ⟨1726553, by rfl⟩ : syracuseStep 2302071 = 3453107) B3453107
theorem B2913565 : Blo 2301435 2913565 := bbase (se 3 (by rfl) ⟨546293, by rfl⟩ : syracuseStep 2913565 = 1092587) (by norm_num)
theorem B3884753 : Blo 2301435 3884753 := bstep (se 2 (by rfl) ⟨1456782, by rfl⟩ : syracuseStep 3884753 = 2913565) B2913565
theorem B2589835 : Blo 2301435 2589835 := bstep (se 1 (by rfl) ⟨1942376, by rfl⟩ : syracuseStep 2589835 = 3884753) B3884753
theorem B3453113 : Blo 2301435 3453113 := bstep (se 2 (by rfl) ⟨1294917, by rfl⟩ : syracuseStep 3453113 = 2589835) B2589835
theorem B2302075 : Blo 2301435 2302075 := bstep (se 1 (by rfl) ⟨1726556, by rfl⟩ : syracuseStep 2302075 = 3453113) B3453113
theorem B5250349 : Blo 2301435 5250349 := bbase (se 3 (by rfl) ⟨984440, by rfl⟩ : syracuseStep 5250349 = 1968881) (by norm_num)
theorem B28001861 : Blo 2301435 28001861 := bstep (se 4 (by rfl) ⟨2625174, by rfl⟩ : syracuseStep 28001861 = 5250349) B5250349
theorem B18667907 : Blo 2301435 18667907 := bstep (se 1 (by rfl) ⟨14000930, by rfl⟩ : syracuseStep 18667907 = 28001861) B28001861
theorem B12445271 : Blo 2301435 12445271 := bstep (se 1 (by rfl) ⟨9333953, by rfl⟩ : syracuseStep 12445271 = 18667907) B18667907
theorem B8296847 : Blo 2301435 8296847 := bstep (se 1 (by rfl) ⟨6222635, by rfl⟩ : syracuseStep 8296847 = 12445271) B12445271
theorem B5531231 : Blo 2301435 5531231 := bstep (se 1 (by rfl) ⟨4148423, by rfl⟩ : syracuseStep 5531231 = 8296847) B8296847
theorem B3687487 : Blo 2301435 3687487 := bstep (se 1 (by rfl) ⟨2765615, by rfl⟩ : syracuseStep 3687487 = 5531231) B5531231
theorem B19666597 : Blo 2301435 19666597 := bstep (se 4 (by rfl) ⟨1843743, by rfl⟩ : syracuseStep 19666597 = 3687487) B3687487
theorem B26222129 : Blo 2301435 26222129 := bstep (se 2 (by rfl) ⟨9833298, by rfl⟩ : syracuseStep 26222129 = 19666597) B19666597
theorem B17481419 : Blo 2301435 17481419 := bstep (se 1 (by rfl) ⟨13111064, by rfl⟩ : syracuseStep 17481419 = 26222129) B26222129
theorem B11654279 : Blo 2301435 11654279 := bstep (se 1 (by rfl) ⟨8740709, by rfl⟩ : syracuseStep 11654279 = 17481419) B17481419
theorem B7769519 : Blo 2301435 7769519 := bstep (se 1 (by rfl) ⟨5827139, by rfl⟩ : syracuseStep 7769519 = 11654279) B11654279
theorem B5179679 : Blo 2301435 5179679 := bstep (se 1 (by rfl) ⟨3884759, by rfl⟩ : syracuseStep 5179679 = 7769519) B7769519
theorem B3453119 : Blo 2301435 3453119 := bstep (se 1 (by rfl) ⟨2589839, by rfl⟩ : syracuseStep 3453119 = 5179679) B5179679
theorem B2302079 : Blo 2301435 2302079 := bstep (se 1 (by rfl) ⟨1726559, by rfl⟩ : syracuseStep 2302079 = 3453119) B3453119
theorem B3453125 : Blo 2301435 3453125 := bbase (se 4 (by rfl) ⟨323730, by rfl⟩ : syracuseStep 3453125 = 647461) (by norm_num)
theorem B2302083 : Blo 2301435 2302083 := bstep (se 1 (by rfl) ⟨1726562, by rfl⟩ : syracuseStep 2302083 = 3453125) B3453125
theorem B3884773 : Blo 2301435 3884773 := bbase (se 4 (by rfl) ⟨364197, by rfl⟩ : syracuseStep 3884773 = 728395) (by norm_num)
theorem B5179697 : Blo 2301435 5179697 := bstep (se 2 (by rfl) ⟨1942386, by rfl⟩ : syracuseStep 5179697 = 3884773) B3884773
theorem B3453131 : Blo 2301435 3453131 := bstep (se 1 (by rfl) ⟨2589848, by rfl⟩ : syracuseStep 3453131 = 5179697) B5179697
theorem B2302087 : Blo 2301435 2302087 := bstep (se 1 (by rfl) ⟨1726565, by rfl⟩ : syracuseStep 2302087 = 3453131) B3453131
theorem B2589853 : Blo 2301435 2589853 := bbase (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) (by norm_num)
theorem B3453137 : Blo 2301435 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B2302091 : Blo 2301435 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B7769573 : Blo 2301435 7769573 := bbase (se 4 (by rfl) ⟨728397, by rfl⟩ : syracuseStep 7769573 = 1456795) (by norm_num)
theorem B5179715 : Blo 2301435 5179715 := bstep (se 1 (by rfl) ⟨3884786, by rfl⟩ : syracuseStep 5179715 = 7769573) B7769573
theorem B3453143 : Blo 2301435 3453143 := bstep (se 1 (by rfl) ⟨2589857, by rfl⟩ : syracuseStep 3453143 = 5179715) B5179715
theorem B2302095 : Blo 2301435 2302095 := bstep (se 1 (by rfl) ⟨1726571, by rfl⟩ : syracuseStep 2302095 = 3453143) B3453143
theorem B3453149 : Blo 2301435 3453149 := bbase (se 3 (by rfl) ⟨647465, by rfl⟩ : syracuseStep 3453149 = 1294931) (by norm_num)
theorem B2302099 : Blo 2301435 2302099 := bstep (se 1 (by rfl) ⟨1726574, by rfl⟩ : syracuseStep 2302099 = 3453149) B3453149
theorem B5179733 : Blo 2301435 5179733 := bbase (se 10 (by rfl) ⟨7587, by rfl⟩ : syracuseStep 5179733 = 15175) (by norm_num)
theorem B3453155 : Blo 2301435 3453155 := bstep (se 1 (by rfl) ⟨2589866, by rfl⟩ : syracuseStep 3453155 = 5179733) B5179733
theorem B2302103 : Blo 2301435 2302103 := bstep (se 1 (by rfl) ⟨1726577, by rfl⟩ : syracuseStep 2302103 = 3453155) B3453155
theorem B3687533 : Blo 2301435 3687533 := bbase (se 3 (by rfl) ⟨691412, by rfl⟩ : syracuseStep 3687533 = 1382825) (by norm_num)
theorem B2458355 : Blo 2301435 2458355 := bstep (se 1 (by rfl) ⟨1843766, by rfl⟩ : syracuseStep 2458355 = 3687533) B3687533
theorem B6555613 : Blo 2301435 6555613 := bstep (se 3 (by rfl) ⟨1229177, by rfl⟩ : syracuseStep 6555613 = 2458355) B2458355
theorem B8740817 : Blo 2301435 8740817 := bstep (se 2 (by rfl) ⟨3277806, by rfl⟩ : syracuseStep 8740817 = 6555613) B6555613
theorem B5827211 : Blo 2301435 5827211 := bstep (se 1 (by rfl) ⟨4370408, by rfl⟩ : syracuseStep 5827211 = 8740817) B8740817
theorem B3884807 : Blo 2301435 3884807 := bstep (se 1 (by rfl) ⟨2913605, by rfl⟩ : syracuseStep 3884807 = 5827211) B5827211
theorem B2589871 : Blo 2301435 2589871 := bstep (se 1 (by rfl) ⟨1942403, by rfl⟩ : syracuseStep 2589871 = 3884807) B3884807
theorem B3453161 : Blo 2301435 3453161 := bstep (se 2 (by rfl) ⟨1294935, by rfl⟩ : syracuseStep 3453161 = 2589871) B2589871
theorem B2302107 : Blo 2301435 2302107 := bstep (se 1 (by rfl) ⟨1726580, by rfl⟩ : syracuseStep 2302107 = 3453161) B3453161
theorem B4430045 : Blo 2301435 4430045 := bbase (se 3 (by rfl) ⟨830633, by rfl⟩ : syracuseStep 4430045 = 1661267) (by norm_num)
theorem B2953363 : Blo 2301435 2953363 := bstep (se 1 (by rfl) ⟨2215022, by rfl⟩ : syracuseStep 2953363 = 4430045) B4430045
theorem B3937817 : Blo 2301435 3937817 := bstep (se 2 (by rfl) ⟨1476681, by rfl⟩ : syracuseStep 3937817 = 2953363) B2953363
theorem B2625211 : Blo 2301435 2625211 := bstep (se 1 (by rfl) ⟨1968908, by rfl⟩ : syracuseStep 2625211 = 3937817) B3937817
theorem B3500281 : Blo 2301435 3500281 := bstep (se 2 (by rfl) ⟨1312605, by rfl⟩ : syracuseStep 3500281 = 2625211) B2625211
theorem B4667041 : Blo 2301435 4667041 := bstep (se 2 (by rfl) ⟨1750140, by rfl⟩ : syracuseStep 4667041 = 3500281) B3500281
theorem B24890885 : Blo 2301435 24890885 := bstep (se 4 (by rfl) ⟨2333520, by rfl⟩ : syracuseStep 24890885 = 4667041) B4667041
theorem B16593923 : Blo 2301435 16593923 := bstep (se 1 (by rfl) ⟨12445442, by rfl⟩ : syracuseStep 16593923 = 24890885) B24890885
theorem B44250461 : Blo 2301435 44250461 := bstep (se 3 (by rfl) ⟨8296961, by rfl⟩ : syracuseStep 44250461 = 16593923) B16593923
theorem B29500307 : Blo 2301435 29500307 := bstep (se 1 (by rfl) ⟨22125230, by rfl⟩ : syracuseStep 29500307 = 44250461) B44250461
theorem B19666871 : Blo 2301435 19666871 := bstep (se 1 (by rfl) ⟨14750153, by rfl⟩ : syracuseStep 19666871 = 29500307) B29500307
theorem B13111247 : Blo 2301435 13111247 := bstep (se 1 (by rfl) ⟨9833435, by rfl⟩ : syracuseStep 13111247 = 19666871) B19666871
theorem B8740831 : Blo 2301435 8740831 := bstep (se 1 (by rfl) ⟨6555623, by rfl⟩ : syracuseStep 8740831 = 13111247) B13111247
theorem B11654441 : Blo 2301435 11654441 := bstep (se 2 (by rfl) ⟨4370415, by rfl⟩ : syracuseStep 11654441 = 8740831) B8740831
theorem B7769627 : Blo 2301435 7769627 := bstep (se 1 (by rfl) ⟨5827220, by rfl⟩ : syracuseStep 7769627 = 11654441) B11654441
theorem B5179751 : Blo 2301435 5179751 := bstep (se 1 (by rfl) ⟨3884813, by rfl⟩ : syracuseStep 5179751 = 7769627) B7769627
theorem B3453167 : Blo 2301435 3453167 := bstep (se 1 (by rfl) ⟨2589875, by rfl⟩ : syracuseStep 3453167 = 5179751) B5179751
theorem B2302111 : Blo 2301435 2302111 := bstep (se 1 (by rfl) ⟨1726583, by rfl⟩ : syracuseStep 2302111 = 3453167) B3453167
theorem B3453173 : Blo 2301435 3453173 := bbase (se 5 (by rfl) ⟨161867, by rfl⟩ : syracuseStep 3453173 = 323735) (by norm_num)
theorem B2302115 : Blo 2301435 2302115 := bstep (se 1 (by rfl) ⟨1726586, by rfl⟩ : syracuseStep 2302115 = 3453173) B3453173
theorem B50461141 : Blo 2301435 50461141 := bbase (se 7 (by rfl) ⟨591341, by rfl⟩ : syracuseStep 50461141 = 1182683) (by norm_num)
theorem B67281521 : Blo 2301435 67281521 := bstep (se 2 (by rfl) ⟨25230570, by rfl⟩ : syracuseStep 67281521 = 50461141) B50461141
theorem B179417389 : Blo 2301435 179417389 := bstep (se 3 (by rfl) ⟨33640760, by rfl⟩ : syracuseStep 179417389 = 67281521) B67281521
theorem B239223185 : Blo 2301435 239223185 := bstep (se 2 (by rfl) ⟨89708694, by rfl⟩ : syracuseStep 239223185 = 179417389) B179417389
theorem B159482123 : Blo 2301435 159482123 := bstep (se 1 (by rfl) ⟨119611592, by rfl⟩ : syracuseStep 159482123 = 239223185) B239223185
theorem B106321415 : Blo 2301435 106321415 := bstep (se 1 (by rfl) ⟨79741061, by rfl⟩ : syracuseStep 106321415 = 159482123) B159482123
theorem B283523773 : Blo 2301435 283523773 := bstep (se 3 (by rfl) ⟨53160707, by rfl⟩ : syracuseStep 283523773 = 106321415) B106321415
theorem B378031697 : Blo 2301435 378031697 := bstep (se 2 (by rfl) ⟨141761886, by rfl⟩ : syracuseStep 378031697 = 283523773) B283523773
theorem B252021131 : Blo 2301435 252021131 := bstep (se 1 (by rfl) ⟨189015848, by rfl⟩ : syracuseStep 252021131 = 378031697) B378031697
theorem B168014087 : Blo 2301435 168014087 := bstep (se 1 (by rfl) ⟨126010565, by rfl⟩ : syracuseStep 168014087 = 252021131) B252021131
theorem B112009391 : Blo 2301435 112009391 := bstep (se 1 (by rfl) ⟨84007043, by rfl⟩ : syracuseStep 112009391 = 168014087) B168014087
theorem B74672927 : Blo 2301435 74672927 := bstep (se 1 (by rfl) ⟨56004695, by rfl⟩ : syracuseStep 74672927 = 112009391) B112009391
theorem B49781951 : Blo 2301435 49781951 := bstep (se 1 (by rfl) ⟨37336463, by rfl⟩ : syracuseStep 49781951 = 74672927) B74672927
theorem B33187967 : Blo 2301435 33187967 := bstep (se 1 (by rfl) ⟨24890975, by rfl⟩ : syracuseStep 33187967 = 49781951) B49781951
theorem B22125311 : Blo 2301435 22125311 := bstep (se 1 (by rfl) ⟨16593983, by rfl⟩ : syracuseStep 22125311 = 33187967) B33187967
theorem B14750207 : Blo 2301435 14750207 := bstep (se 1 (by rfl) ⟨11062655, by rfl⟩ : syracuseStep 14750207 = 22125311) B22125311
theorem B9833471 : Blo 2301435 9833471 := bstep (se 1 (by rfl) ⟨7375103, by rfl⟩ : syracuseStep 9833471 = 14750207) B14750207
theorem B6555647 : Blo 2301435 6555647 := bstep (se 1 (by rfl) ⟨4916735, by rfl⟩ : syracuseStep 6555647 = 9833471) B9833471
theorem B4370431 : Blo 2301435 4370431 := bstep (se 1 (by rfl) ⟨3277823, by rfl⟩ : syracuseStep 4370431 = 6555647) B6555647
theorem B5827241 : Blo 2301435 5827241 := bstep (se 2 (by rfl) ⟨2185215, by rfl⟩ : syracuseStep 5827241 = 4370431) B4370431
theorem B3884827 : Blo 2301435 3884827 := bstep (se 1 (by rfl) ⟨2913620, by rfl⟩ : syracuseStep 3884827 = 5827241) B5827241
theorem B5179769 : Blo 2301435 5179769 := bstep (se 2 (by rfl) ⟨1942413, by rfl⟩ : syracuseStep 5179769 = 3884827) B3884827
theorem B3453179 : Blo 2301435 3453179 := bstep (se 1 (by rfl) ⟨2589884, by rfl⟩ : syracuseStep 3453179 = 5179769) B5179769
theorem B2302119 : Blo 2301435 2302119 := bstep (se 1 (by rfl) ⟨1726589, by rfl⟩ : syracuseStep 2302119 = 3453179) B3453179
theorem B2589889 : Blo 2301435 2589889 := bbase (se 2 (by rfl) ⟨971208, by rfl⟩ : syracuseStep 2589889 = 1942417) (by norm_num)
theorem B3453185 : Blo 2301435 3453185 := bstep (se 2 (by rfl) ⟨1294944, by rfl⟩ : syracuseStep 3453185 = 2589889) B2589889
theorem B2302123 : Blo 2301435 2302123 := bstep (se 1 (by rfl) ⟨1726592, by rfl⟩ : syracuseStep 2302123 = 3453185) B3453185
theorem B5827261 : Blo 2301435 5827261 := bbase (se 3 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 5827261 = 2185223) (by norm_num)
theorem B7769681 : Blo 2301435 7769681 := bstep (se 2 (by rfl) ⟨2913630, by rfl⟩ : syracuseStep 7769681 = 5827261) B5827261
theorem B5179787 : Blo 2301435 5179787 := bstep (se 1 (by rfl) ⟨3884840, by rfl⟩ : syracuseStep 5179787 = 7769681) B7769681
theorem B3453191 : Blo 2301435 3453191 := bstep (se 1 (by rfl) ⟨2589893, by rfl⟩ : syracuseStep 3453191 = 5179787) B5179787
theorem B2302127 : Blo 2301435 2302127 := bstep (se 1 (by rfl) ⟨1726595, by rfl⟩ : syracuseStep 2302127 = 3453191) B3453191
theorem B3453197 : Blo 2301435 3453197 := bbase (se 3 (by rfl) ⟨647474, by rfl⟩ : syracuseStep 3453197 = 1294949) (by norm_num)
theorem B2302131 : Blo 2301435 2302131 := bstep (se 1 (by rfl) ⟨1726598, by rfl⟩ : syracuseStep 2302131 = 3453197) B3453197
theorem B5179805 : Blo 2301435 5179805 := bbase (se 3 (by rfl) ⟨971213, by rfl⟩ : syracuseStep 5179805 = 1942427) (by norm_num)
theorem B3453203 : Blo 2301435 3453203 := bstep (se 1 (by rfl) ⟨2589902, by rfl⟩ : syracuseStep 3453203 = 5179805) B5179805
theorem B2302135 : Blo 2301435 2302135 := bstep (se 1 (by rfl) ⟨1726601, by rfl⟩ : syracuseStep 2302135 = 3453203) B3453203
theorem B3884861 : Blo 2301435 3884861 := bbase (se 3 (by rfl) ⟨728411, by rfl⟩ : syracuseStep 3884861 = 1456823) (by norm_num)
theorem B2589907 : Blo 2301435 2589907 := bstep (se 1 (by rfl) ⟨1942430, by rfl⟩ : syracuseStep 2589907 = 3884861) B3884861
theorem B3453209 : Blo 2301435 3453209 := bstep (se 2 (by rfl) ⟨1294953, by rfl⟩ : syracuseStep 3453209 = 2589907) B2589907
theorem B2302139 : Blo 2301435 2302139 := bstep (se 1 (by rfl) ⟨1726604, by rfl⟩ : syracuseStep 2302139 = 3453209) B3453209
theorem B2458393 : Blo 2301435 2458393 := bbase (se 2 (by rfl) ⟨921897, by rfl⟩ : syracuseStep 2458393 = 1843795) (by norm_num)
theorem B13111429 : Blo 2301435 13111429 := bstep (se 4 (by rfl) ⟨1229196, by rfl⟩ : syracuseStep 13111429 = 2458393) B2458393
theorem B17481905 : Blo 2301435 17481905 := bstep (se 2 (by rfl) ⟨6555714, by rfl⟩ : syracuseStep 17481905 = 13111429) B13111429
theorem B11654603 : Blo 2301435 11654603 := bstep (se 1 (by rfl) ⟨8740952, by rfl⟩ : syracuseStep 11654603 = 17481905) B17481905
theorem B7769735 : Blo 2301435 7769735 := bstep (se 1 (by rfl) ⟨5827301, by rfl⟩ : syracuseStep 7769735 = 11654603) B11654603
theorem B5179823 : Blo 2301435 5179823 := bstep (se 1 (by rfl) ⟨3884867, by rfl⟩ : syracuseStep 5179823 = 7769735) B7769735
theorem B3453215 : Blo 2301435 3453215 := bstep (se 1 (by rfl) ⟨2589911, by rfl⟩ : syracuseStep 3453215 = 5179823) B5179823
theorem B2302143 : Blo 2301435 2302143 := bstep (se 1 (by rfl) ⟨1726607, by rfl⟩ : syracuseStep 2302143 = 3453215) B3453215
theorem B3453221 : Blo 2301435 3453221 := bbase (se 4 (by rfl) ⟨323739, by rfl⟩ : syracuseStep 3453221 = 647479) (by norm_num)
theorem B2302147 : Blo 2301435 2302147 := bstep (se 1 (by rfl) ⟨1726610, by rfl⟩ : syracuseStep 2302147 = 3453221) B3453221
theorem B2913661 : Blo 2301435 2913661 := bbase (se 3 (by rfl) ⟨546311, by rfl⟩ : syracuseStep 2913661 = 1092623) (by norm_num)
theorem B3884881 : Blo 2301435 3884881 := bstep (se 2 (by rfl) ⟨1456830, by rfl⟩ : syracuseStep 3884881 = 2913661) B2913661
theorem B5179841 : Blo 2301435 5179841 := bstep (se 2 (by rfl) ⟨1942440, by rfl⟩ : syracuseStep 5179841 = 3884881) B3884881
theorem B3453227 : Blo 2301435 3453227 := bstep (se 1 (by rfl) ⟨2589920, by rfl⟩ : syracuseStep 3453227 = 5179841) B5179841
theorem B2302151 : Blo 2301435 2302151 := bstep (se 1 (by rfl) ⟨1726613, by rfl⟩ : syracuseStep 2302151 = 3453227) B3453227
theorem B2589925 : Blo 2301435 2589925 := bbase (se 4 (by rfl) ⟨242805, by rfl⟩ : syracuseStep 2589925 = 485611) (by norm_num)
theorem B3453233 : Blo 2301435 3453233 := bstep (se 2 (by rfl) ⟨1294962, by rfl⟩ : syracuseStep 3453233 = 2589925) B2589925
theorem B2302155 : Blo 2301435 2302155 := bstep (se 1 (by rfl) ⟨1726616, by rfl⟩ : syracuseStep 2302155 = 3453233) B3453233
theorem B4916821 : Blo 2301435 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B6555761 : Blo 2301435 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B4370507 : Blo 2301435 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B2913671 : Blo 2301435 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B7769789 : Blo 2301435 7769789 := bstep (se 3 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 7769789 = 2913671) B2913671
theorem B5179859 : Blo 2301435 5179859 := bstep (se 1 (by rfl) ⟨3884894, by rfl⟩ : syracuseStep 5179859 = 7769789) B7769789
theorem B3453239 : Blo 2301435 3453239 := bstep (se 1 (by rfl) ⟨2589929, by rfl⟩ : syracuseStep 3453239 = 5179859) B5179859
theorem B2302159 : Blo 2301435 2302159 := bstep (se 1 (by rfl) ⟨1726619, by rfl⟩ : syracuseStep 2302159 = 3453239) B3453239
theorem B3453245 : Blo 2301435 3453245 := bbase (se 3 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 3453245 = 1294967) (by norm_num)
theorem B2302163 : Blo 2301435 2302163 := bstep (se 1 (by rfl) ⟨1726622, by rfl⟩ : syracuseStep 2302163 = 3453245) B3453245
theorem B5179877 : Blo 2301435 5179877 := bbase (se 4 (by rfl) ⟨485613, by rfl⟩ : syracuseStep 5179877 = 971227) (by norm_num)
theorem B3453251 : Blo 2301435 3453251 := bstep (se 1 (by rfl) ⟨2589938, by rfl⟩ : syracuseStep 3453251 = 5179877) B5179877
theorem B2302167 : Blo 2301435 2302167 := bstep (se 1 (by rfl) ⟨1726625, by rfl⟩ : syracuseStep 2302167 = 3453251) B3453251
theorem B5827373 : Blo 2301435 5827373 := bbase (se 3 (by rfl) ⟨1092632, by rfl⟩ : syracuseStep 5827373 = 2185265) (by norm_num)
theorem B3884915 : Blo 2301435 3884915 := bstep (se 1 (by rfl) ⟨2913686, by rfl⟩ : syracuseStep 3884915 = 5827373) B5827373
theorem B2589943 : Blo 2301435 2589943 := bstep (se 1 (by rfl) ⟨1942457, by rfl⟩ : syracuseStep 2589943 = 3884915) B3884915
theorem B3453257 : Blo 2301435 3453257 := bstep (se 2 (by rfl) ⟨1294971, by rfl⟩ : syracuseStep 3453257 = 2589943) B2589943
theorem B2302171 : Blo 2301435 2302171 := bstep (se 1 (by rfl) ⟨1726628, by rfl⟩ : syracuseStep 2302171 = 3453257) B3453257
theorem B4148597 : Blo 2301435 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B11062925 : Blo 2301435 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B7375283 : Blo 2301435 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B4916855 : Blo 2301435 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B3277903 : Blo 2301435 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B4370537 : Blo 2301435 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B11654765 : Blo 2301435 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B7769843 : Blo 2301435 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B5179895 : Blo 2301435 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B3453263 : Blo 2301435 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B2302175 : Blo 2301435 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B3453269 : Blo 2301435 3453269 := bbase (se 10 (by rfl) ⟨5058, by rfl⟩ : syracuseStep 3453269 = 10117) (by norm_num)
theorem B2302179 : Blo 2301435 2302179 := bstep (se 1 (by rfl) ⟨1726634, by rfl⟩ : syracuseStep 2302179 = 3453269) B3453269
theorem B6555829 : Blo 2301435 6555829 := bbase (se 5 (by rfl) ⟨307304, by rfl⟩ : syracuseStep 6555829 = 614609) (by norm_num)
theorem B8741105 : Blo 2301435 8741105 := bstep (se 2 (by rfl) ⟨3277914, by rfl⟩ : syracuseStep 8741105 = 6555829) B6555829
theorem B5827403 : Blo 2301435 5827403 := bstep (se 1 (by rfl) ⟨4370552, by rfl⟩ : syracuseStep 5827403 = 8741105) B8741105
theorem B3884935 : Blo 2301435 3884935 := bstep (se 1 (by rfl) ⟨2913701, by rfl⟩ : syracuseStep 3884935 = 5827403) B5827403
theorem B5179913 : Blo 2301435 5179913 := bstep (se 2 (by rfl) ⟨1942467, by rfl⟩ : syracuseStep 5179913 = 3884935) B3884935
theorem B3453275 : Blo 2301435 3453275 := bstep (se 1 (by rfl) ⟨2589956, by rfl⟩ : syracuseStep 3453275 = 5179913) B5179913
theorem B2302183 : Blo 2301435 2302183 := bstep (se 1 (by rfl) ⟨1726637, by rfl⟩ : syracuseStep 2302183 = 3453275) B3453275
theorem B2589961 : Blo 2301435 2589961 := bbase (se 2 (by rfl) ⟨971235, by rfl⟩ : syracuseStep 2589961 = 1942471) (by norm_num)
theorem B3453281 : Blo 2301435 3453281 := bstep (se 2 (by rfl) ⟨1294980, by rfl⟩ : syracuseStep 3453281 = 2589961) B2589961
theorem B2302187 : Blo 2301435 2302187 := bstep (se 1 (by rfl) ⟨1726640, by rfl⟩ : syracuseStep 2302187 = 3453281) B3453281
theorem B29501333 : Blo 2301435 29501333 := bbase (se 6 (by rfl) ⟨691437, by rfl⟩ : syracuseStep 29501333 = 1382875) (by norm_num)
theorem B19667555 : Blo 2301435 19667555 := bstep (se 1 (by rfl) ⟨14750666, by rfl⟩ : syracuseStep 19667555 = 29501333) B29501333
theorem B13111703 : Blo 2301435 13111703 := bstep (se 1 (by rfl) ⟨9833777, by rfl⟩ : syracuseStep 13111703 = 19667555) B19667555
theorem B8741135 : Blo 2301435 8741135 := bstep (se 1 (by rfl) ⟨6555851, by rfl⟩ : syracuseStep 8741135 = 13111703) B13111703
theorem B5827423 : Blo 2301435 5827423 := bstep (se 1 (by rfl) ⟨4370567, by rfl⟩ : syracuseStep 5827423 = 8741135) B8741135
theorem B7769897 : Blo 2301435 7769897 := bstep (se 2 (by rfl) ⟨2913711, by rfl⟩ : syracuseStep 7769897 = 5827423) B5827423
theorem B5179931 : Blo 2301435 5179931 := bstep (se 1 (by rfl) ⟨3884948, by rfl⟩ : syracuseStep 5179931 = 7769897) B7769897
theorem B3453287 : Blo 2301435 3453287 := bstep (se 1 (by rfl) ⟨2589965, by rfl⟩ : syracuseStep 3453287 = 5179931) B5179931
theorem B2302191 : Blo 2301435 2302191 := bstep (se 1 (by rfl) ⟨1726643, by rfl⟩ : syracuseStep 2302191 = 3453287) B3453287
theorem B3453293 : Blo 2301435 3453293 := bbase (se 3 (by rfl) ⟨647492, by rfl⟩ : syracuseStep 3453293 = 1294985) (by norm_num)
theorem B2302195 : Blo 2301435 2302195 := bstep (se 1 (by rfl) ⟨1726646, by rfl⟩ : syracuseStep 2302195 = 3453293) B3453293
theorem B5179949 : Blo 2301435 5179949 := bbase (se 3 (by rfl) ⟨971240, by rfl⟩ : syracuseStep 5179949 = 1942481) (by norm_num)
theorem B3453299 : Blo 2301435 3453299 := bstep (se 1 (by rfl) ⟨2589974, by rfl⟩ : syracuseStep 3453299 = 5179949) B5179949
theorem B2302199 : Blo 2301435 2302199 := bstep (se 1 (by rfl) ⟨1726649, by rfl⟩ : syracuseStep 2302199 = 3453299) B3453299
theorem B8092325 : Blo 2301435 8092325 := bbase (se 4 (by rfl) ⟨758655, by rfl⟩ : syracuseStep 8092325 = 1517311) (by norm_num)
theorem B5394883 : Blo 2301435 5394883 := bstep (se 1 (by rfl) ⟨4046162, by rfl⟩ : syracuseStep 5394883 = 8092325) B8092325
theorem B7193177 : Blo 2301435 7193177 := bstep (se 2 (by rfl) ⟨2697441, by rfl⟩ : syracuseStep 7193177 = 5394883) B5394883
theorem B4795451 : Blo 2301435 4795451 := bstep (se 1 (by rfl) ⟨3596588, by rfl⟩ : syracuseStep 4795451 = 7193177) B7193177
theorem B3196967 : Blo 2301435 3196967 := bstep (se 1 (by rfl) ⟨2397725, by rfl⟩ : syracuseStep 3196967 = 4795451) B4795451
theorem B34100981 : Blo 2301435 34100981 := bstep (se 5 (by rfl) ⟨1598483, by rfl⟩ : syracuseStep 34100981 = 3196967) B3196967
theorem B22733987 : Blo 2301435 22733987 := bstep (se 1 (by rfl) ⟨17050490, by rfl⟩ : syracuseStep 22733987 = 34100981) B34100981
theorem B60623965 : Blo 2301435 60623965 := bstep (se 3 (by rfl) ⟨11366993, by rfl⟩ : syracuseStep 60623965 = 22733987) B22733987
theorem B80831953 : Blo 2301435 80831953 := bstep (se 2 (by rfl) ⟨30311982, by rfl⟩ : syracuseStep 80831953 = 60623965) B60623965
theorem B107775937 : Blo 2301435 107775937 := bstep (se 2 (by rfl) ⟨40415976, by rfl⟩ : syracuseStep 107775937 = 80831953) B80831953
theorem B574804997 : Blo 2301435 574804997 := bstep (se 4 (by rfl) ⟨53887968, by rfl⟩ : syracuseStep 574804997 = 107775937) B107775937
theorem B383203331 : Blo 2301435 383203331 := bstep (se 1 (by rfl) ⟨287402498, by rfl⟩ : syracuseStep 383203331 = 574804997) B574804997
theorem B255468887 : Blo 2301435 255468887 := bstep (se 1 (by rfl) ⟨191601665, by rfl⟩ : syracuseStep 255468887 = 383203331) B383203331
theorem B170312591 : Blo 2301435 170312591 := bstep (se 1 (by rfl) ⟨127734443, by rfl⟩ : syracuseStep 170312591 = 255468887) B255468887
theorem B454166909 : Blo 2301435 454166909 := bstep (se 3 (by rfl) ⟨85156295, by rfl⟩ : syracuseStep 454166909 = 170312591) B170312591
theorem B302777939 : Blo 2301435 302777939 := bstep (se 1 (by rfl) ⟨227083454, by rfl⟩ : syracuseStep 302777939 = 454166909) B454166909
theorem B807407837 : Blo 2301435 807407837 := bstep (se 3 (by rfl) ⟨151388969, by rfl⟩ : syracuseStep 807407837 = 302777939) B302777939
theorem B538271891 : Blo 2301435 538271891 := bstep (se 1 (by rfl) ⟨403703918, by rfl⟩ : syracuseStep 538271891 = 807407837) B807407837
theorem B358847927 : Blo 2301435 358847927 := bstep (se 1 (by rfl) ⟨269135945, by rfl⟩ : syracuseStep 358847927 = 538271891) B538271891
theorem B239231951 : Blo 2301435 239231951 := bstep (se 1 (by rfl) ⟨179423963, by rfl⟩ : syracuseStep 239231951 = 358847927) B358847927
theorem B159487967 : Blo 2301435 159487967 := bstep (se 1 (by rfl) ⟨119615975, by rfl⟩ : syracuseStep 159487967 = 239231951) B239231951
theorem B106325311 : Blo 2301435 106325311 := bstep (se 1 (by rfl) ⟨79743983, by rfl⟩ : syracuseStep 106325311 = 159487967) B159487967
theorem B141767081 : Blo 2301435 141767081 := bstep (se 2 (by rfl) ⟨53162655, by rfl⟩ : syracuseStep 141767081 = 106325311) B106325311
theorem B94511387 : Blo 2301435 94511387 := bstep (se 1 (by rfl) ⟨70883540, by rfl⟩ : syracuseStep 94511387 = 141767081) B141767081
theorem B63007591 : Blo 2301435 63007591 := bstep (se 1 (by rfl) ⟨47255693, by rfl⟩ : syracuseStep 63007591 = 94511387) B94511387
theorem B84010121 : Blo 2301435 84010121 := bstep (se 2 (by rfl) ⟨31503795, by rfl⟩ : syracuseStep 84010121 = 63007591) B63007591
theorem B56006747 : Blo 2301435 56006747 := bstep (se 1 (by rfl) ⟨42005060, by rfl⟩ : syracuseStep 56006747 = 84010121) B84010121
theorem B37337831 : Blo 2301435 37337831 := bstep (se 1 (by rfl) ⟨28003373, by rfl⟩ : syracuseStep 37337831 = 56006747) B56006747
theorem B24891887 : Blo 2301435 24891887 := bstep (se 1 (by rfl) ⟨18668915, by rfl⟩ : syracuseStep 24891887 = 37337831) B37337831
theorem B16594591 : Blo 2301435 16594591 := bstep (se 1 (by rfl) ⟨12445943, by rfl⟩ : syracuseStep 16594591 = 24891887) B24891887
theorem B22126121 : Blo 2301435 22126121 := bstep (se 2 (by rfl) ⟨8297295, by rfl⟩ : syracuseStep 22126121 = 16594591) B16594591
theorem B14750747 : Blo 2301435 14750747 := bstep (se 1 (by rfl) ⟨11063060, by rfl⟩ : syracuseStep 14750747 = 22126121) B22126121
theorem B9833831 : Blo 2301435 9833831 := bstep (se 1 (by rfl) ⟨7375373, by rfl⟩ : syracuseStep 9833831 = 14750747) B14750747
theorem B6555887 : Blo 2301435 6555887 := bstep (se 1 (by rfl) ⟨4916915, by rfl⟩ : syracuseStep 6555887 = 9833831) B9833831
theorem B4370591 : Blo 2301435 4370591 := bstep (se 1 (by rfl) ⟨3277943, by rfl⟩ : syracuseStep 4370591 = 6555887) B6555887
theorem B2913727 : Blo 2301435 2913727 := bstep (se 1 (by rfl) ⟨2185295, by rfl⟩ : syracuseStep 2913727 = 4370591) B4370591
theorem B3884969 : Blo 2301435 3884969 := bstep (se 2 (by rfl) ⟨1456863, by rfl⟩ : syracuseStep 3884969 = 2913727) B2913727
theorem B2589979 : Blo 2301435 2589979 := bstep (se 1 (by rfl) ⟨1942484, by rfl⟩ : syracuseStep 2589979 = 3884969) B3884969
theorem B3453305 : Blo 2301435 3453305 := bstep (se 2 (by rfl) ⟨1294989, by rfl⟩ : syracuseStep 3453305 = 2589979) B2589979
theorem B2302203 : Blo 2301435 2302203 := bstep (se 1 (by rfl) ⟨1726652, by rfl⟩ : syracuseStep 2302203 = 3453305) B3453305
theorem B39335381 : Blo 2301435 39335381 := bbase (se 7 (by rfl) ⟨460961, by rfl⟩ : syracuseStep 39335381 = 921923) (by norm_num)
theorem B26223587 : Blo 2301435 26223587 := bstep (se 1 (by rfl) ⟨19667690, by rfl⟩ : syracuseStep 26223587 = 39335381) B39335381
theorem B17482391 : Blo 2301435 17482391 := bstep (se 1 (by rfl) ⟨13111793, by rfl⟩ : syracuseStep 17482391 = 26223587) B26223587
theorem B11654927 : Blo 2301435 11654927 := bstep (se 1 (by rfl) ⟨8741195, by rfl⟩ : syracuseStep 11654927 = 17482391) B17482391
theorem B7769951 : Blo 2301435 7769951 := bstep (se 1 (by rfl) ⟨5827463, by rfl⟩ : syracuseStep 7769951 = 11654927) B11654927
theorem B5179967 : Blo 2301435 5179967 := bstep (se 1 (by rfl) ⟨3884975, by rfl⟩ : syracuseStep 5179967 = 7769951) B7769951
theorem B3453311 : Blo 2301435 3453311 := bstep (se 1 (by rfl) ⟨2589983, by rfl⟩ : syracuseStep 3453311 = 5179967) B5179967
theorem B2302207 : Blo 2301435 2302207 := bstep (se 1 (by rfl) ⟨1726655, by rfl⟩ : syracuseStep 2302207 = 3453311) B3453311
theorem B3453317 : Blo 2301435 3453317 := bbase (se 4 (by rfl) ⟨323748, by rfl⟩ : syracuseStep 3453317 = 647497) (by norm_num)
theorem B2302211 : Blo 2301435 2302211 := bstep (se 1 (by rfl) ⟨1726658, by rfl⟩ : syracuseStep 2302211 = 3453317) B3453317
theorem B3884989 : Blo 2301435 3884989 := bbase (se 3 (by rfl) ⟨728435, by rfl⟩ : syracuseStep 3884989 = 1456871) (by norm_num)
theorem B5179985 : Blo 2301435 5179985 := bstep (se 2 (by rfl) ⟨1942494, by rfl⟩ : syracuseStep 5179985 = 3884989) B3884989
theorem B3453323 : Blo 2301435 3453323 := bstep (se 1 (by rfl) ⟨2589992, by rfl⟩ : syracuseStep 3453323 = 5179985) B5179985
theorem B2302215 : Blo 2301435 2302215 := bstep (se 1 (by rfl) ⟨1726661, by rfl⟩ : syracuseStep 2302215 = 3453323) B3453323
theorem B2589997 : Blo 2301435 2589997 := bbase (se 3 (by rfl) ⟨485624, by rfl⟩ : syracuseStep 2589997 = 971249) (by norm_num)
theorem B3453329 : Blo 2301435 3453329 := bstep (se 2 (by rfl) ⟨1294998, by rfl⟩ : syracuseStep 3453329 = 2589997) B2589997
theorem B2302219 : Blo 2301435 2302219 := bstep (se 1 (by rfl) ⟨1726664, by rfl⟩ : syracuseStep 2302219 = 3453329) B3453329
theorem B7770005 : Blo 2301435 7770005 := bbase (se 6 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 7770005 = 364219) (by norm_num)
theorem B5180003 : Blo 2301435 5180003 := bstep (se 1 (by rfl) ⟨3885002, by rfl⟩ : syracuseStep 5180003 = 7770005) B7770005
theorem B3453335 : Blo 2301435 3453335 := bstep (se 1 (by rfl) ⟨2590001, by rfl⟩ : syracuseStep 3453335 = 5180003) B5180003
theorem B2302223 : Blo 2301435 2302223 := bstep (se 1 (by rfl) ⟨1726667, by rfl⟩ : syracuseStep 2302223 = 3453335) B3453335
theorem B3453341 : Blo 2301435 3453341 := bbase (se 3 (by rfl) ⟨647501, by rfl⟩ : syracuseStep 3453341 = 1295003) (by norm_num)
theorem B2302227 : Blo 2301435 2302227 := bstep (se 1 (by rfl) ⟨1726670, by rfl⟩ : syracuseStep 2302227 = 3453341) B3453341
theorem B5180021 : Blo 2301435 5180021 := bbase (se 5 (by rfl) ⟨242813, by rfl⟩ : syracuseStep 5180021 = 485627) (by norm_num)
theorem B3453347 : Blo 2301435 3453347 := bstep (se 1 (by rfl) ⟨2590010, by rfl⟩ : syracuseStep 3453347 = 5180021) B5180021
theorem B2302231 : Blo 2301435 2302231 := bstep (se 1 (by rfl) ⟨1726673, by rfl⟩ : syracuseStep 2302231 = 3453347) B3453347
theorem B4430285 : Blo 2301435 4430285 := bbase (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) (by norm_num)
theorem B2953523 : Blo 2301435 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B7876061 : Blo 2301435 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B5250707 : Blo 2301435 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B3500471 : Blo 2301435 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B2333647 : Blo 2301435 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B3111529 : Blo 2301435 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B4148705 : Blo 2301435 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B11063213 : Blo 2301435 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B7375475 : Blo 2301435 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B19667933 : Blo 2301435 19667933 := bstep (se 3 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 19667933 = 7375475) B7375475
theorem B13111955 : Blo 2301435 13111955 := bstep (se 1 (by rfl) ⟨9833966, by rfl⟩ : syracuseStep 13111955 = 19667933) B19667933
theorem B8741303 : Blo 2301435 8741303 := bstep (se 1 (by rfl) ⟨6555977, by rfl⟩ : syracuseStep 8741303 = 13111955) B13111955
theorem B5827535 : Blo 2301435 5827535 := bstep (se 1 (by rfl) ⟨4370651, by rfl⟩ : syracuseStep 5827535 = 8741303) B8741303
theorem B3885023 : Blo 2301435 3885023 := bstep (se 1 (by rfl) ⟨2913767, by rfl⟩ : syracuseStep 3885023 = 5827535) B5827535
theorem B2590015 : Blo 2301435 2590015 := bstep (se 1 (by rfl) ⟨1942511, by rfl⟩ : syracuseStep 2590015 = 3885023) B3885023
theorem B3453353 : Blo 2301435 3453353 := bstep (se 2 (by rfl) ⟨1295007, by rfl⟩ : syracuseStep 3453353 = 2590015) B2590015
theorem B2302235 : Blo 2301435 2302235 := bstep (se 1 (by rfl) ⟨1726676, by rfl⟩ : syracuseStep 2302235 = 3453353) B3453353
theorem B8741317 : Blo 2301435 8741317 := bbase (se 4 (by rfl) ⟨819498, by rfl⟩ : syracuseStep 8741317 = 1638997) (by norm_num)
theorem B11655089 : Blo 2301435 11655089 := bstep (se 2 (by rfl) ⟨4370658, by rfl⟩ : syracuseStep 11655089 = 8741317) B8741317
theorem B7770059 : Blo 2301435 7770059 := bstep (se 1 (by rfl) ⟨5827544, by rfl⟩ : syracuseStep 7770059 = 11655089) B11655089
theorem B5180039 : Blo 2301435 5180039 := bstep (se 1 (by rfl) ⟨3885029, by rfl⟩ : syracuseStep 5180039 = 7770059) B7770059
theorem B3453359 : Blo 2301435 3453359 := bstep (se 1 (by rfl) ⟨2590019, by rfl⟩ : syracuseStep 3453359 = 5180039) B5180039
theorem B2302239 : Blo 2301435 2302239 := bstep (se 1 (by rfl) ⟨1726679, by rfl⟩ : syracuseStep 2302239 = 3453359) B3453359
theorem B3453365 : Blo 2301435 3453365 := bbase (se 5 (by rfl) ⟨161876, by rfl⟩ : syracuseStep 3453365 = 323753) (by norm_num)
theorem B2302243 : Blo 2301435 2302243 := bstep (se 1 (by rfl) ⟨1726682, by rfl⟩ : syracuseStep 2302243 = 3453365) B3453365
theorem B5827565 : Blo 2301435 5827565 := bbase (se 3 (by rfl) ⟨1092668, by rfl⟩ : syracuseStep 5827565 = 2185337) (by norm_num)
theorem B3885043 : Blo 2301435 3885043 := bstep (se 1 (by rfl) ⟨2913782, by rfl⟩ : syracuseStep 3885043 = 5827565) B5827565
theorem B5180057 : Blo 2301435 5180057 := bstep (se 2 (by rfl) ⟨1942521, by rfl⟩ : syracuseStep 5180057 = 3885043) B3885043
theorem B3453371 : Blo 2301435 3453371 := bstep (se 1 (by rfl) ⟨2590028, by rfl⟩ : syracuseStep 3453371 = 5180057) B5180057
theorem B2302247 : Blo 2301435 2302247 := bstep (se 1 (by rfl) ⟨1726685, by rfl⟩ : syracuseStep 2302247 = 3453371) B3453371
theorem B2590033 : Blo 2301435 2590033 := bbase (se 2 (by rfl) ⟨971262, by rfl⟩ : syracuseStep 2590033 = 1942525) (by norm_num)
theorem B3453377 : Blo 2301435 3453377 := bstep (se 2 (by rfl) ⟨1295016, by rfl⟩ : syracuseStep 3453377 = 2590033) B2590033
theorem B2302251 : Blo 2301435 2302251 := bstep (se 1 (by rfl) ⟨1726688, by rfl⟩ : syracuseStep 2302251 = 3453377) B3453377
theorem B2458513 : Blo 2301435 2458513 := bbase (se 2 (by rfl) ⟨921942, by rfl⟩ : syracuseStep 2458513 = 1843885) (by norm_num)
theorem B3278017 : Blo 2301435 3278017 := bstep (se 2 (by rfl) ⟨1229256, by rfl⟩ : syracuseStep 3278017 = 2458513) B2458513
theorem B4370689 : Blo 2301435 4370689 := bstep (se 2 (by rfl) ⟨1639008, by rfl⟩ : syracuseStep 4370689 = 3278017) B3278017
theorem B5827585 : Blo 2301435 5827585 := bstep (se 2 (by rfl) ⟨2185344, by rfl⟩ : syracuseStep 5827585 = 4370689) B4370689
theorem B7770113 : Blo 2301435 7770113 := bstep (se 2 (by rfl) ⟨2913792, by rfl⟩ : syracuseStep 7770113 = 5827585) B5827585
theorem B5180075 : Blo 2301435 5180075 := bstep (se 1 (by rfl) ⟨3885056, by rfl⟩ : syracuseStep 5180075 = 7770113) B7770113
theorem B3453383 : Blo 2301435 3453383 := bstep (se 1 (by rfl) ⟨2590037, by rfl⟩ : syracuseStep 3453383 = 5180075) B5180075
theorem B2302255 : Blo 2301435 2302255 := bstep (se 1 (by rfl) ⟨1726691, by rfl⟩ : syracuseStep 2302255 = 3453383) B3453383
theorem B3453389 : Blo 2301435 3453389 := bbase (se 3 (by rfl) ⟨647510, by rfl⟩ : syracuseStep 3453389 = 1295021) (by norm_num)
theorem B2302259 : Blo 2301435 2302259 := bstep (se 1 (by rfl) ⟨1726694, by rfl⟩ : syracuseStep 2302259 = 3453389) B3453389
theorem B5180093 : Blo 2301435 5180093 := bbase (se 3 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 5180093 = 1942535) (by norm_num)
theorem B3453395 : Blo 2301435 3453395 := bstep (se 1 (by rfl) ⟨2590046, by rfl⟩ : syracuseStep 3453395 = 5180093) B5180093
theorem B2302263 : Blo 2301435 2302263 := bstep (se 1 (by rfl) ⟨1726697, by rfl⟩ : syracuseStep 2302263 = 3453395) B3453395
theorem B3885077 : Blo 2301435 3885077 := bbase (se 6 (by rfl) ⟨91056, by rfl⟩ : syracuseStep 3885077 = 182113) (by norm_num)
theorem B2590051 : Blo 2301435 2590051 := bstep (se 1 (by rfl) ⟨1942538, by rfl⟩ : syracuseStep 2590051 = 3885077) B3885077
theorem B3453401 : Blo 2301435 3453401 := bstep (se 2 (by rfl) ⟨1295025, by rfl⟩ : syracuseStep 3453401 = 2590051) B2590051
theorem B2302267 : Blo 2301435 2302267 := bstep (se 1 (by rfl) ⟨1726700, by rfl⟩ : syracuseStep 2302267 = 3453401) B3453401
theorem B3500525 : Blo 2301435 3500525 := bbase (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) (by norm_num)
theorem B2333683 : Blo 2301435 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B3111577 : Blo 2301435 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B16595077 : Blo 2301435 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B22126769 : Blo 2301435 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B14751179 : Blo 2301435 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B9834119 : Blo 2301435 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B6556079 : Blo 2301435 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B17482877 : Blo 2301435 17482877 := bstep (se 3 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 17482877 = 6556079) B6556079
theorem B11655251 : Blo 2301435 11655251 := bstep (se 1 (by rfl) ⟨8741438, by rfl⟩ : syracuseStep 11655251 = 17482877) B17482877
theorem B7770167 : Blo 2301435 7770167 := bstep (se 1 (by rfl) ⟨5827625, by rfl⟩ : syracuseStep 7770167 = 11655251) B11655251
theorem B5180111 : Blo 2301435 5180111 := bstep (se 1 (by rfl) ⟨3885083, by rfl⟩ : syracuseStep 5180111 = 7770167) B7770167
theorem B3453407 : Blo 2301435 3453407 := bstep (se 1 (by rfl) ⟨2590055, by rfl⟩ : syracuseStep 3453407 = 5180111) B5180111
theorem B2302271 : Blo 2301435 2302271 := bstep (se 1 (by rfl) ⟨1726703, by rfl⟩ : syracuseStep 2302271 = 3453407) B3453407
theorem B3453413 : Blo 2301435 3453413 := bbase (se 4 (by rfl) ⟨323757, by rfl⟩ : syracuseStep 3453413 = 647515) (by norm_num)
theorem B2302275 : Blo 2301435 2302275 := bstep (se 1 (by rfl) ⟨1726706, by rfl⟩ : syracuseStep 2302275 = 3453413) B3453413
theorem B3738125 : Blo 2301435 3738125 := bbase (se 3 (by rfl) ⟨700898, by rfl⟩ : syracuseStep 3738125 = 1401797) (by norm_num)
theorem B2492083 : Blo 2301435 2492083 := bstep (se 1 (by rfl) ⟨1869062, by rfl⟩ : syracuseStep 2492083 = 3738125) B3738125
theorem B3322777 : Blo 2301435 3322777 := bstep (se 2 (by rfl) ⟨1246041, by rfl⟩ : syracuseStep 3322777 = 2492083) B2492083
theorem B4430369 : Blo 2301435 4430369 := bstep (se 2 (by rfl) ⟨1661388, by rfl⟩ : syracuseStep 4430369 = 3322777) B3322777
theorem B2953579 : Blo 2301435 2953579 := bstep (se 1 (by rfl) ⟨2215184, by rfl⟩ : syracuseStep 2953579 = 4430369) B4430369
theorem B3938105 : Blo 2301435 3938105 := bstep (se 2 (by rfl) ⟨1476789, by rfl⟩ : syracuseStep 3938105 = 2953579) B2953579
theorem B10501613 : Blo 2301435 10501613 := bstep (se 3 (by rfl) ⟨1969052, by rfl⟩ : syracuseStep 10501613 = 3938105) B3938105
theorem B7001075 : Blo 2301435 7001075 := bstep (se 1 (by rfl) ⟨5250806, by rfl⟩ : syracuseStep 7001075 = 10501613) B10501613
theorem B4667383 : Blo 2301435 4667383 := bstep (se 1 (by rfl) ⟨3500537, by rfl⟩ : syracuseStep 4667383 = 7001075) B7001075
theorem B6223177 : Blo 2301435 6223177 := bstep (se 2 (by rfl) ⟨2333691, by rfl⟩ : syracuseStep 6223177 = 4667383) B4667383
theorem B8297569 : Blo 2301435 8297569 := bstep (se 2 (by rfl) ⟨3111588, by rfl⟩ : syracuseStep 8297569 = 6223177) B6223177
theorem B11063425 : Blo 2301435 11063425 := bstep (se 2 (by rfl) ⟨4148784, by rfl⟩ : syracuseStep 11063425 = 8297569) B8297569
theorem B14751233 : Blo 2301435 14751233 := bstep (se 2 (by rfl) ⟨5531712, by rfl⟩ : syracuseStep 14751233 = 11063425) B11063425
theorem B9834155 : Blo 2301435 9834155 := bstep (se 1 (by rfl) ⟨7375616, by rfl⟩ : syracuseStep 9834155 = 14751233) B14751233
theorem B6556103 : Blo 2301435 6556103 := bstep (se 1 (by rfl) ⟨4917077, by rfl⟩ : syracuseStep 6556103 = 9834155) B9834155
theorem B4370735 : Blo 2301435 4370735 := bstep (se 1 (by rfl) ⟨3278051, by rfl⟩ : syracuseStep 4370735 = 6556103) B6556103
theorem B2913823 : Blo 2301435 2913823 := bstep (se 1 (by rfl) ⟨2185367, by rfl⟩ : syracuseStep 2913823 = 4370735) B4370735
theorem B3885097 : Blo 2301435 3885097 := bstep (se 2 (by rfl) ⟨1456911, by rfl⟩ : syracuseStep 3885097 = 2913823) B2913823
theorem B5180129 : Blo 2301435 5180129 := bstep (se 2 (by rfl) ⟨1942548, by rfl⟩ : syracuseStep 5180129 = 3885097) B3885097
theorem B3453419 : Blo 2301435 3453419 := bstep (se 1 (by rfl) ⟨2590064, by rfl⟩ : syracuseStep 3453419 = 5180129) B5180129
theorem B2302279 : Blo 2301435 2302279 := bstep (se 1 (by rfl) ⟨1726709, by rfl⟩ : syracuseStep 2302279 = 3453419) B3453419
theorem B2590069 : Blo 2301435 2590069 := bbase (se 5 (by rfl) ⟨121409, by rfl⟩ : syracuseStep 2590069 = 242819) (by norm_num)
theorem B3453425 : Blo 2301435 3453425 := bstep (se 2 (by rfl) ⟨1295034, by rfl⟩ : syracuseStep 3453425 = 2590069) B2590069
theorem B2302283 : Blo 2301435 2302283 := bstep (se 1 (by rfl) ⟨1726712, by rfl⟩ : syracuseStep 2302283 = 3453425) B3453425
theorem B2913833 : Blo 2301435 2913833 := bbase (se 2 (by rfl) ⟨1092687, by rfl⟩ : syracuseStep 2913833 = 2185375) (by norm_num)
theorem B7770221 : Blo 2301435 7770221 := bstep (se 3 (by rfl) ⟨1456916, by rfl⟩ : syracuseStep 7770221 = 2913833) B2913833
theorem B5180147 : Blo 2301435 5180147 := bstep (se 1 (by rfl) ⟨3885110, by rfl⟩ : syracuseStep 5180147 = 7770221) B7770221
theorem B3453431 : Blo 2301435 3453431 := bstep (se 1 (by rfl) ⟨2590073, by rfl⟩ : syracuseStep 3453431 = 5180147) B5180147
theorem B2302287 : Blo 2301435 2302287 := bstep (se 1 (by rfl) ⟨1726715, by rfl⟩ : syracuseStep 2302287 = 3453431) B3453431
theorem B3453437 : Blo 2301435 3453437 := bbase (se 3 (by rfl) ⟨647519, by rfl⟩ : syracuseStep 3453437 = 1295039) (by norm_num)
theorem B2302291 : Blo 2301435 2302291 := bstep (se 1 (by rfl) ⟨1726718, by rfl⟩ : syracuseStep 2302291 = 3453437) B3453437
theorem B5180165 : Blo 2301435 5180165 := bbase (se 4 (by rfl) ⟨485640, by rfl⟩ : syracuseStep 5180165 = 971281) (by norm_num)
theorem B3453443 : Blo 2301435 3453443 := bstep (se 1 (by rfl) ⟨2590082, by rfl⟩ : syracuseStep 3453443 = 5180165) B5180165
theorem B2302295 : Blo 2301435 2302295 := bstep (se 1 (by rfl) ⟨1726721, by rfl⟩ : syracuseStep 2302295 = 3453443) B3453443
theorem B4370773 : Blo 2301435 4370773 := bbase (se 10 (by rfl) ⟨6402, by rfl⟩ : syracuseStep 4370773 = 12805) (by norm_num)
theorem B5827697 : Blo 2301435 5827697 := bstep (se 2 (by rfl) ⟨2185386, by rfl⟩ : syracuseStep 5827697 = 4370773) B4370773
theorem B3885131 : Blo 2301435 3885131 := bstep (se 1 (by rfl) ⟨2913848, by rfl⟩ : syracuseStep 3885131 = 5827697) B5827697
theorem B2590087 : Blo 2301435 2590087 := bstep (se 1 (by rfl) ⟨1942565, by rfl⟩ : syracuseStep 2590087 = 3885131) B3885131
theorem B3453449 : Blo 2301435 3453449 := bstep (se 2 (by rfl) ⟨1295043, by rfl⟩ : syracuseStep 3453449 = 2590087) B2590087
theorem B2302299 : Blo 2301435 2302299 := bstep (se 1 (by rfl) ⟨1726724, by rfl⟩ : syracuseStep 2302299 = 3453449) B3453449
theorem B11655413 : Blo 2301435 11655413 := bbase (se 5 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 11655413 = 1092695) (by norm_num)
theorem B7770275 : Blo 2301435 7770275 := bstep (se 1 (by rfl) ⟨5827706, by rfl⟩ : syracuseStep 7770275 = 11655413) B11655413
theorem B5180183 : Blo 2301435 5180183 := bstep (se 1 (by rfl) ⟨3885137, by rfl⟩ : syracuseStep 5180183 = 7770275) B7770275
theorem B3453455 : Blo 2301435 3453455 := bstep (se 1 (by rfl) ⟨2590091, by rfl⟩ : syracuseStep 3453455 = 5180183) B5180183
theorem B2302303 : Blo 2301435 2302303 := bstep (se 1 (by rfl) ⟨1726727, by rfl⟩ : syracuseStep 2302303 = 3453455) B3453455
theorem B3453461 : Blo 2301435 3453461 := bbase (se 6 (by rfl) ⟨80940, by rfl⟩ : syracuseStep 3453461 = 161881) (by norm_num)
theorem B2302307 : Blo 2301435 2302307 := bstep (se 1 (by rfl) ⟨1726730, by rfl⟩ : syracuseStep 2302307 = 3453461) B3453461
theorem B5531789 : Blo 2301435 5531789 := bbase (se 3 (by rfl) ⟨1037210, by rfl⟩ : syracuseStep 5531789 = 2074421) (by norm_num)
theorem B3687859 : Blo 2301435 3687859 := bstep (se 1 (by rfl) ⟨2765894, by rfl⟩ : syracuseStep 3687859 = 5531789) B5531789
theorem B19668581 : Blo 2301435 19668581 := bstep (se 4 (by rfl) ⟨1843929, by rfl⟩ : syracuseStep 19668581 = 3687859) B3687859
theorem B13112387 : Blo 2301435 13112387 := bstep (se 1 (by rfl) ⟨9834290, by rfl⟩ : syracuseStep 13112387 = 19668581) B19668581
theorem B8741591 : Blo 2301435 8741591 := bstep (se 1 (by rfl) ⟨6556193, by rfl⟩ : syracuseStep 8741591 = 13112387) B13112387
theorem B5827727 : Blo 2301435 5827727 := bstep (se 1 (by rfl) ⟨4370795, by rfl⟩ : syracuseStep 5827727 = 8741591) B8741591
theorem B3885151 : Blo 2301435 3885151 := bstep (se 1 (by rfl) ⟨2913863, by rfl⟩ : syracuseStep 3885151 = 5827727) B5827727
theorem B5180201 : Blo 2301435 5180201 := bstep (se 2 (by rfl) ⟨1942575, by rfl⟩ : syracuseStep 5180201 = 3885151) B3885151
theorem B3453467 : Blo 2301435 3453467 := bstep (se 1 (by rfl) ⟨2590100, by rfl⟩ : syracuseStep 3453467 = 5180201) B5180201
theorem B2302311 : Blo 2301435 2302311 := bstep (se 1 (by rfl) ⟨1726733, by rfl⟩ : syracuseStep 2302311 = 3453467) B3453467
theorem B2590105 : Blo 2301435 2590105 := bbase (se 2 (by rfl) ⟨971289, by rfl⟩ : syracuseStep 2590105 = 1942579) (by norm_num)
theorem B3453473 : Blo 2301435 3453473 := bstep (se 2 (by rfl) ⟨1295052, by rfl⟩ : syracuseStep 3453473 = 2590105) B2590105
theorem B2302315 : Blo 2301435 2302315 := bstep (se 1 (by rfl) ⟨1726736, by rfl⟩ : syracuseStep 2302315 = 3453473) B3453473
theorem B8741621 : Blo 2301435 8741621 := bbase (se 5 (by rfl) ⟨409763, by rfl⟩ : syracuseStep 8741621 = 819527) (by norm_num)
theorem B5827747 : Blo 2301435 5827747 := bstep (se 1 (by rfl) ⟨4370810, by rfl⟩ : syracuseStep 5827747 = 8741621) B8741621
theorem B7770329 : Blo 2301435 7770329 := bstep (se 2 (by rfl) ⟨2913873, by rfl⟩ : syracuseStep 7770329 = 5827747) B5827747
theorem B5180219 : Blo 2301435 5180219 := bstep (se 1 (by rfl) ⟨3885164, by rfl⟩ : syracuseStep 5180219 = 7770329) B7770329
theorem B3453479 : Blo 2301435 3453479 := bstep (se 1 (by rfl) ⟨2590109, by rfl⟩ : syracuseStep 3453479 = 5180219) B5180219
theorem B2302319 : Blo 2301435 2302319 := bstep (se 1 (by rfl) ⟨1726739, by rfl⟩ : syracuseStep 2302319 = 3453479) B3453479
theorem B3453485 : Blo 2301435 3453485 := bbase (se 3 (by rfl) ⟨647528, by rfl⟩ : syracuseStep 3453485 = 1295057) (by norm_num)
theorem B2302323 : Blo 2301435 2302323 := bstep (se 1 (by rfl) ⟨1726742, by rfl⟩ : syracuseStep 2302323 = 3453485) B3453485
theorem B5180237 : Blo 2301435 5180237 := bbase (se 3 (by rfl) ⟨971294, by rfl⟩ : syracuseStep 5180237 = 1942589) (by norm_num)
theorem B3453491 : Blo 2301435 3453491 := bstep (se 1 (by rfl) ⟨2590118, by rfl⟩ : syracuseStep 3453491 = 5180237) B5180237
theorem B2302327 : Blo 2301435 2302327 := bstep (se 1 (by rfl) ⟨1726745, by rfl⟩ : syracuseStep 2302327 = 3453491) B3453491
theorem B2913889 : Blo 2301435 2913889 := bbase (se 2 (by rfl) ⟨1092708, by rfl⟩ : syracuseStep 2913889 = 2185417) (by norm_num)
theorem B3885185 : Blo 2301435 3885185 := bstep (se 2 (by rfl) ⟨1456944, by rfl⟩ : syracuseStep 3885185 = 2913889) B2913889
theorem B2590123 : Blo 2301435 2590123 := bstep (se 1 (by rfl) ⟨1942592, by rfl⟩ : syracuseStep 2590123 = 3885185) B3885185
theorem B3453497 : Blo 2301435 3453497 := bstep (se 2 (by rfl) ⟨1295061, by rfl⟩ : syracuseStep 3453497 = 2590123) B2590123
theorem B2302331 : Blo 2301435 2302331 := bstep (se 1 (by rfl) ⟨1726748, by rfl⟩ : syracuseStep 2302331 = 3453497) B3453497
theorem B26225045 : Blo 2301435 26225045 := bbase (se 6 (by rfl) ⟨614649, by rfl⟩ : syracuseStep 26225045 = 1229299) (by norm_num)
theorem B17483363 : Blo 2301435 17483363 := bstep (se 1 (by rfl) ⟨13112522, by rfl⟩ : syracuseStep 17483363 = 26225045) B26225045
theorem B11655575 : Blo 2301435 11655575 := bstep (se 1 (by rfl) ⟨8741681, by rfl⟩ : syracuseStep 11655575 = 17483363) B17483363
theorem B7770383 : Blo 2301435 7770383 := bstep (se 1 (by rfl) ⟨5827787, by rfl⟩ : syracuseStep 7770383 = 11655575) B11655575
theorem B5180255 : Blo 2301435 5180255 := bstep (se 1 (by rfl) ⟨3885191, by rfl⟩ : syracuseStep 5180255 = 7770383) B7770383
theorem B3453503 : Blo 2301435 3453503 := bstep (se 1 (by rfl) ⟨2590127, by rfl⟩ : syracuseStep 3453503 = 5180255) B5180255
theorem B2302335 : Blo 2301435 2302335 := bstep (se 1 (by rfl) ⟨1726751, by rfl⟩ : syracuseStep 2302335 = 3453503) B3453503
theorem B3453509 : Blo 2301435 3453509 := bbase (se 4 (by rfl) ⟨323766, by rfl⟩ : syracuseStep 3453509 = 647533) (by norm_num)
theorem B2302339 : Blo 2301435 2302339 := bstep (se 1 (by rfl) ⟨1726754, by rfl⟩ : syracuseStep 2302339 = 3453509) B3453509
theorem B3885205 : Blo 2301435 3885205 := bbase (se 6 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 3885205 = 182119) (by norm_num)
theorem B5180273 : Blo 2301435 5180273 := bstep (se 2 (by rfl) ⟨1942602, by rfl⟩ : syracuseStep 5180273 = 3885205) B3885205
theorem B3453515 : Blo 2301435 3453515 := bstep (se 1 (by rfl) ⟨2590136, by rfl⟩ : syracuseStep 3453515 = 5180273) B5180273
theorem B2302343 : Blo 2301435 2302343 := bstep (se 1 (by rfl) ⟨1726757, by rfl⟩ : syracuseStep 2302343 = 3453515) B3453515
theorem B2590141 : Blo 2301435 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B3453521 : Blo 2301435 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B2302347 : Blo 2301435 2302347 := bstep (se 1 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 2302347 = 3453521) B3453521
theorem B7770437 : Blo 2301435 7770437 := bbase (se 4 (by rfl) ⟨728478, by rfl⟩ : syracuseStep 7770437 = 1456957) (by norm_num)
theorem B5180291 : Blo 2301435 5180291 := bstep (se 1 (by rfl) ⟨3885218, by rfl⟩ : syracuseStep 5180291 = 7770437) B7770437
theorem B3453527 : Blo 2301435 3453527 := bstep (se 1 (by rfl) ⟨2590145, by rfl⟩ : syracuseStep 3453527 = 5180291) B5180291
theorem B2302351 : Blo 2301435 2302351 := bstep (se 1 (by rfl) ⟨1726763, by rfl⟩ : syracuseStep 2302351 = 3453527) B3453527
theorem B3453533 : Blo 2301435 3453533 := bbase (se 3 (by rfl) ⟨647537, by rfl⟩ : syracuseStep 3453533 = 1295075) (by norm_num)
theorem B2302355 : Blo 2301435 2302355 := bstep (se 1 (by rfl) ⟨1726766, by rfl⟩ : syracuseStep 2302355 = 3453533) B3453533
theorem B5180309 : Blo 2301435 5180309 := bbase (se 6 (by rfl) ⟨121413, by rfl⟩ : syracuseStep 5180309 = 242827) (by norm_num)
theorem B3453539 : Blo 2301435 3453539 := bstep (se 1 (by rfl) ⟨2590154, by rfl⟩ : syracuseStep 3453539 = 5180309) B5180309
theorem B2302359 : Blo 2301435 2302359 := bstep (se 1 (by rfl) ⟨1726769, by rfl⟩ : syracuseStep 2302359 = 3453539) B3453539
theorem B2333777 : Blo 2301435 2333777 := bbase (se 2 (by rfl) ⟨875166, by rfl⟩ : syracuseStep 2333777 = 1750333) (by norm_num)
theorem B6223405 : Blo 2301435 6223405 := bstep (se 3 (by rfl) ⟨1166888, by rfl⟩ : syracuseStep 6223405 = 2333777) B2333777
theorem B8297873 : Blo 2301435 8297873 := bstep (se 2 (by rfl) ⟨3111702, by rfl⟩ : syracuseStep 8297873 = 6223405) B6223405
theorem B5531915 : Blo 2301435 5531915 := bstep (se 1 (by rfl) ⟨4148936, by rfl⟩ : syracuseStep 5531915 = 8297873) B8297873
theorem B3687943 : Blo 2301435 3687943 := bstep (se 1 (by rfl) ⟨2765957, by rfl⟩ : syracuseStep 3687943 = 5531915) B5531915
theorem B4917257 : Blo 2301435 4917257 := bstep (se 2 (by rfl) ⟨1843971, by rfl⟩ : syracuseStep 4917257 = 3687943) B3687943
theorem B3278171 : Blo 2301435 3278171 := bstep (se 1 (by rfl) ⟨2458628, by rfl⟩ : syracuseStep 3278171 = 4917257) B4917257
theorem B8741789 : Blo 2301435 8741789 := bstep (se 3 (by rfl) ⟨1639085, by rfl⟩ : syracuseStep 8741789 = 3278171) B3278171
theorem B5827859 : Blo 2301435 5827859 := bstep (se 1 (by rfl) ⟨4370894, by rfl⟩ : syracuseStep 5827859 = 8741789) B8741789
theorem B3885239 : Blo 2301435 3885239 := bstep (se 1 (by rfl) ⟨2913929, by rfl⟩ : syracuseStep 3885239 = 5827859) B5827859
theorem B2590159 : Blo 2301435 2590159 := bstep (se 1 (by rfl) ⟨1942619, by rfl⟩ : syracuseStep 2590159 = 3885239) B3885239
theorem B3453545 : Blo 2301435 3453545 := bstep (se 2 (by rfl) ⟨1295079, by rfl⟩ : syracuseStep 3453545 = 2590159) B2590159
theorem B2302363 : Blo 2301435 2302363 := bstep (se 1 (by rfl) ⟨1726772, by rfl⟩ : syracuseStep 2302363 = 3453545) B3453545
theorem B5987981 : Blo 2301435 5987981 := bbase (se 3 (by rfl) ⟨1122746, by rfl⟩ : syracuseStep 5987981 = 2245493) (by norm_num)
theorem B3991987 : Blo 2301435 3991987 := bstep (se 1 (by rfl) ⟨2993990, by rfl⟩ : syracuseStep 3991987 = 5987981) B5987981
theorem B21290597 : Blo 2301435 21290597 := bstep (se 4 (by rfl) ⟨1995993, by rfl⟩ : syracuseStep 21290597 = 3991987) B3991987
theorem B14193731 : Blo 2301435 14193731 := bstep (se 1 (by rfl) ⟨10645298, by rfl⟩ : syracuseStep 14193731 = 21290597) B21290597
theorem B37849949 : Blo 2301435 37849949 := bstep (se 3 (by rfl) ⟨7096865, by rfl⟩ : syracuseStep 37849949 = 14193731) B14193731
theorem B25233299 : Blo 2301435 25233299 := bstep (se 1 (by rfl) ⟨18924974, by rfl⟩ : syracuseStep 25233299 = 37849949) B37849949
theorem B16822199 : Blo 2301435 16822199 := bstep (se 1 (by rfl) ⟨12616649, by rfl⟩ : syracuseStep 16822199 = 25233299) B25233299
theorem B44859197 : Blo 2301435 44859197 := bstep (se 3 (by rfl) ⟨8411099, by rfl⟩ : syracuseStep 44859197 = 16822199) B16822199
theorem B29906131 : Blo 2301435 29906131 := bstep (se 1 (by rfl) ⟨22429598, by rfl⟩ : syracuseStep 29906131 = 44859197) B44859197
theorem B39874841 : Blo 2301435 39874841 := bstep (se 2 (by rfl) ⟨14953065, by rfl⟩ : syracuseStep 39874841 = 29906131) B29906131
theorem B26583227 : Blo 2301435 26583227 := bstep (se 1 (by rfl) ⟨19937420, by rfl⟩ : syracuseStep 26583227 = 39874841) B39874841
theorem B17722151 : Blo 2301435 17722151 := bstep (se 1 (by rfl) ⟨13291613, by rfl⟩ : syracuseStep 17722151 = 26583227) B26583227
theorem B11814767 : Blo 2301435 11814767 := bstep (se 1 (by rfl) ⟨8861075, by rfl⟩ : syracuseStep 11814767 = 17722151) B17722151
theorem B7876511 : Blo 2301435 7876511 := bstep (se 1 (by rfl) ⟨5907383, by rfl⟩ : syracuseStep 7876511 = 11814767) B11814767
theorem B5251007 : Blo 2301435 5251007 := bstep (se 1 (by rfl) ⟨3938255, by rfl⟩ : syracuseStep 5251007 = 7876511) B7876511
theorem B3500671 : Blo 2301435 3500671 := bstep (se 1 (by rfl) ⟨2625503, by rfl⟩ : syracuseStep 3500671 = 5251007) B5251007
theorem B4667561 : Blo 2301435 4667561 := bstep (se 2 (by rfl) ⟨1750335, by rfl⟩ : syracuseStep 4667561 = 3500671) B3500671
theorem B3111707 : Blo 2301435 3111707 := bstep (se 1 (by rfl) ⟨2333780, by rfl⟩ : syracuseStep 3111707 = 4667561) B4667561
theorem B8297885 : Blo 2301435 8297885 := bstep (se 3 (by rfl) ⟨1555853, by rfl⟩ : syracuseStep 8297885 = 3111707) B3111707
theorem B5531923 : Blo 2301435 5531923 := bstep (se 1 (by rfl) ⟨4148942, by rfl⟩ : syracuseStep 5531923 = 8297885) B8297885
theorem B7375897 : Blo 2301435 7375897 := bstep (se 2 (by rfl) ⟨2765961, by rfl⟩ : syracuseStep 7375897 = 5531923) B5531923
theorem B9834529 : Blo 2301435 9834529 := bstep (se 2 (by rfl) ⟨3687948, by rfl⟩ : syracuseStep 9834529 = 7375897) B7375897
theorem B13112705 : Blo 2301435 13112705 := bstep (se 2 (by rfl) ⟨4917264, by rfl⟩ : syracuseStep 13112705 = 9834529) B9834529
theorem B8741803 : Blo 2301435 8741803 := bstep (se 1 (by rfl) ⟨6556352, by rfl⟩ : syracuseStep 8741803 = 13112705) B13112705
theorem B11655737 : Blo 2301435 11655737 := bstep (se 2 (by rfl) ⟨4370901, by rfl⟩ : syracuseStep 11655737 = 8741803) B8741803
theorem B7770491 : Blo 2301435 7770491 := bstep (se 1 (by rfl) ⟨5827868, by rfl⟩ : syracuseStep 7770491 = 11655737) B11655737
theorem B5180327 : Blo 2301435 5180327 := bstep (se 1 (by rfl) ⟨3885245, by rfl⟩ : syracuseStep 5180327 = 7770491) B7770491
theorem B3453551 : Blo 2301435 3453551 := bstep (se 1 (by rfl) ⟨2590163, by rfl⟩ : syracuseStep 3453551 = 5180327) B5180327
theorem B2302367 : Blo 2301435 2302367 := bstep (se 1 (by rfl) ⟨1726775, by rfl⟩ : syracuseStep 2302367 = 3453551) B3453551
theorem B3453557 : Blo 2301435 3453557 := bbase (se 5 (by rfl) ⟨161885, by rfl⟩ : syracuseStep 3453557 = 323771) (by norm_num)
theorem B2302371 : Blo 2301435 2302371 := bstep (se 1 (by rfl) ⟨1726778, by rfl⟩ : syracuseStep 2302371 = 3453557) B3453557
theorem B4370917 : Blo 2301435 4370917 := bbase (se 4 (by rfl) ⟨409773, by rfl⟩ : syracuseStep 4370917 = 819547) (by norm_num)
theorem B5827889 : Blo 2301435 5827889 := bstep (se 2 (by rfl) ⟨2185458, by rfl⟩ : syracuseStep 5827889 = 4370917) B4370917
theorem B3885259 : Blo 2301435 3885259 := bstep (se 1 (by rfl) ⟨2913944, by rfl⟩ : syracuseStep 3885259 = 5827889) B5827889
theorem B5180345 : Blo 2301435 5180345 := bstep (se 2 (by rfl) ⟨1942629, by rfl⟩ : syracuseStep 5180345 = 3885259) B3885259
theorem B3453563 : Blo 2301435 3453563 := bstep (se 1 (by rfl) ⟨2590172, by rfl⟩ : syracuseStep 3453563 = 5180345) B5180345
theorem B2302375 : Blo 2301435 2302375 := bstep (se 1 (by rfl) ⟨1726781, by rfl⟩ : syracuseStep 2302375 = 3453563) B3453563
theorem B2590177 : Blo 2301435 2590177 := bbase (se 2 (by rfl) ⟨971316, by rfl⟩ : syracuseStep 2590177 = 1942633) (by norm_num)
theorem B3453569 : Blo 2301435 3453569 := bstep (se 2 (by rfl) ⟨1295088, by rfl⟩ : syracuseStep 3453569 = 2590177) B2590177
theorem B2302379 : Blo 2301435 2302379 := bstep (se 1 (by rfl) ⟨1726784, by rfl⟩ : syracuseStep 2302379 = 3453569) B3453569
theorem B5827909 : Blo 2301435 5827909 := bbase (se 4 (by rfl) ⟨546366, by rfl⟩ : syracuseStep 5827909 = 1092733) (by norm_num)
theorem B7770545 : Blo 2301435 7770545 := bstep (se 2 (by rfl) ⟨2913954, by rfl⟩ : syracuseStep 7770545 = 5827909) B5827909
theorem B5180363 : Blo 2301435 5180363 := bstep (se 1 (by rfl) ⟨3885272, by rfl⟩ : syracuseStep 5180363 = 7770545) B7770545
theorem B3453575 : Blo 2301435 3453575 := bstep (se 1 (by rfl) ⟨2590181, by rfl⟩ : syracuseStep 3453575 = 5180363) B5180363
theorem B2302383 : Blo 2301435 2302383 := bstep (se 1 (by rfl) ⟨1726787, by rfl⟩ : syracuseStep 2302383 = 3453575) B3453575
theorem B3453581 : Blo 2301435 3453581 := bbase (se 3 (by rfl) ⟨647546, by rfl⟩ : syracuseStep 3453581 = 1295093) (by norm_num)
theorem B2302387 : Blo 2301435 2302387 := bstep (se 1 (by rfl) ⟨1726790, by rfl⟩ : syracuseStep 2302387 = 3453581) B3453581
theorem B5180381 : Blo 2301435 5180381 := bbase (se 3 (by rfl) ⟨971321, by rfl⟩ : syracuseStep 5180381 = 1942643) (by norm_num)
theorem B3453587 : Blo 2301435 3453587 := bstep (se 1 (by rfl) ⟨2590190, by rfl⟩ : syracuseStep 3453587 = 5180381) B5180381
theorem B2302391 : Blo 2301435 2302391 := bstep (se 1 (by rfl) ⟨1726793, by rfl⟩ : syracuseStep 2302391 = 3453587) B3453587
theorem B3885293 : Blo 2301435 3885293 := bbase (se 3 (by rfl) ⟨728492, by rfl⟩ : syracuseStep 3885293 = 1456985) (by norm_num)
theorem B2590195 : Blo 2301435 2590195 := bstep (se 1 (by rfl) ⟨1942646, by rfl⟩ : syracuseStep 2590195 = 3885293) B3885293
theorem B3453593 : Blo 2301435 3453593 := bstep (se 2 (by rfl) ⟨1295097, by rfl⟩ : syracuseStep 3453593 = 2590195) B2590195
theorem B2302395 : Blo 2301435 2302395 := bstep (se 1 (by rfl) ⟨1726796, by rfl⟩ : syracuseStep 2302395 = 3453593) B3453593
theorem B10104853 : Blo 2301435 10104853 := bbase (se 6 (by rfl) ⟨236832, by rfl⟩ : syracuseStep 10104853 = 473665) (by norm_num)
theorem B13473137 : Blo 2301435 13473137 := bstep (se 2 (by rfl) ⟨5052426, by rfl⟩ : syracuseStep 13473137 = 10104853) B10104853
theorem B8982091 : Blo 2301435 8982091 := bstep (se 1 (by rfl) ⟨6736568, by rfl⟩ : syracuseStep 8982091 = 13473137) B13473137
theorem B11976121 : Blo 2301435 11976121 := bstep (se 2 (by rfl) ⟨4491045, by rfl⟩ : syracuseStep 11976121 = 8982091) B8982091
theorem B15968161 : Blo 2301435 15968161 := bstep (se 2 (by rfl) ⟨5988060, by rfl⟩ : syracuseStep 15968161 = 11976121) B11976121
theorem B21290881 : Blo 2301435 21290881 := bstep (se 2 (by rfl) ⟨7984080, by rfl⟩ : syracuseStep 21290881 = 15968161) B15968161
theorem B28387841 : Blo 2301435 28387841 := bstep (se 2 (by rfl) ⟨10645440, by rfl⟩ : syracuseStep 28387841 = 21290881) B21290881
theorem B75700909 : Blo 2301435 75700909 := bstep (se 3 (by rfl) ⟨14193920, by rfl⟩ : syracuseStep 75700909 = 28387841) B28387841
theorem B100934545 : Blo 2301435 100934545 := bstep (se 2 (by rfl) ⟨37850454, by rfl⟩ : syracuseStep 100934545 = 75700909) B75700909
theorem B134579393 : Blo 2301435 134579393 := bstep (se 2 (by rfl) ⟨50467272, by rfl⟩ : syracuseStep 134579393 = 100934545) B100934545
theorem B89719595 : Blo 2301435 89719595 := bstep (se 1 (by rfl) ⟨67289696, by rfl⟩ : syracuseStep 89719595 = 134579393) B134579393
theorem B59813063 : Blo 2301435 59813063 := bstep (se 1 (by rfl) ⟨44859797, by rfl⟩ : syracuseStep 59813063 = 89719595) B89719595
theorem B39875375 : Blo 2301435 39875375 := bstep (se 1 (by rfl) ⟨29906531, by rfl⟩ : syracuseStep 39875375 = 59813063) B59813063
theorem B106334333 : Blo 2301435 106334333 := bstep (se 3 (by rfl) ⟨19937687, by rfl⟩ : syracuseStep 106334333 = 39875375) B39875375
theorem B70889555 : Blo 2301435 70889555 := bstep (se 1 (by rfl) ⟨53167166, by rfl⟩ : syracuseStep 70889555 = 106334333) B106334333
theorem B47259703 : Blo 2301435 47259703 := bstep (se 1 (by rfl) ⟨35444777, by rfl⟩ : syracuseStep 47259703 = 70889555) B70889555
theorem B63012937 : Blo 2301435 63012937 := bstep (se 2 (by rfl) ⟨23629851, by rfl⟩ : syracuseStep 63012937 = 47259703) B47259703
theorem B84017249 : Blo 2301435 84017249 := bstep (se 2 (by rfl) ⟨31506468, by rfl⟩ : syracuseStep 84017249 = 63012937) B63012937
theorem B56011499 : Blo 2301435 56011499 := bstep (se 1 (by rfl) ⟨42008624, by rfl⟩ : syracuseStep 56011499 = 84017249) B84017249
theorem B37340999 : Blo 2301435 37340999 := bstep (se 1 (by rfl) ⟨28005749, by rfl⟩ : syracuseStep 37340999 = 56011499) B56011499
theorem B24893999 : Blo 2301435 24893999 := bstep (se 1 (by rfl) ⟨18670499, by rfl⟩ : syracuseStep 24893999 = 37340999) B37340999
theorem B16595999 : Blo 2301435 16595999 := bstep (se 1 (by rfl) ⟨12446999, by rfl⟩ : syracuseStep 16595999 = 24893999) B24893999
theorem B11063999 : Blo 2301435 11063999 := bstep (se 1 (by rfl) ⟨8297999, by rfl⟩ : syracuseStep 11063999 = 16595999) B16595999
theorem B29503997 : Blo 2301435 29503997 := bstep (se 3 (by rfl) ⟨5531999, by rfl⟩ : syracuseStep 29503997 = 11063999) B11063999
theorem B19669331 : Blo 2301435 19669331 := bstep (se 1 (by rfl) ⟨14751998, by rfl⟩ : syracuseStep 19669331 = 29503997) B29503997
theorem B13112887 : Blo 2301435 13112887 := bstep (se 1 (by rfl) ⟨9834665, by rfl⟩ : syracuseStep 13112887 = 19669331) B19669331
theorem B17483849 : Blo 2301435 17483849 := bstep (se 2 (by rfl) ⟨6556443, by rfl⟩ : syracuseStep 17483849 = 13112887) B13112887
theorem B11655899 : Blo 2301435 11655899 := bstep (se 1 (by rfl) ⟨8741924, by rfl⟩ : syracuseStep 11655899 = 17483849) B17483849
theorem B7770599 : Blo 2301435 7770599 := bstep (se 1 (by rfl) ⟨5827949, by rfl⟩ : syracuseStep 7770599 = 11655899) B11655899
theorem B5180399 : Blo 2301435 5180399 := bstep (se 1 (by rfl) ⟨3885299, by rfl⟩ : syracuseStep 5180399 = 7770599) B7770599
theorem B3453599 : Blo 2301435 3453599 := bstep (se 1 (by rfl) ⟨2590199, by rfl⟩ : syracuseStep 3453599 = 5180399) B5180399
theorem B2302399 : Blo 2301435 2302399 := bstep (se 1 (by rfl) ⟨1726799, by rfl⟩ : syracuseStep 2302399 = 3453599) B3453599
theorem B3453605 : Blo 2301435 3453605 := bbase (se 4 (by rfl) ⟨323775, by rfl⟩ : syracuseStep 3453605 = 647551) (by norm_num)
theorem B2302403 : Blo 2301435 2302403 := bstep (se 1 (by rfl) ⟨1726802, by rfl⟩ : syracuseStep 2302403 = 3453605) B3453605
theorem B2913985 : Blo 2301435 2913985 := bbase (se 2 (by rfl) ⟨1092744, by rfl⟩ : syracuseStep 2913985 = 2185489) (by norm_num)
theorem B3885313 : Blo 2301435 3885313 := bstep (se 2 (by rfl) ⟨1456992, by rfl⟩ : syracuseStep 3885313 = 2913985) B2913985
theorem B5180417 : Blo 2301435 5180417 := bstep (se 2 (by rfl) ⟨1942656, by rfl⟩ : syracuseStep 5180417 = 3885313) B3885313
theorem B3453611 : Blo 2301435 3453611 := bstep (se 1 (by rfl) ⟨2590208, by rfl⟩ : syracuseStep 3453611 = 5180417) B5180417
theorem B2302407 : Blo 2301435 2302407 := bstep (se 1 (by rfl) ⟨1726805, by rfl⟩ : syracuseStep 2302407 = 3453611) B3453611
theorem B2590213 : Blo 2301435 2590213 := bbase (se 4 (by rfl) ⟨242832, by rfl⟩ : syracuseStep 2590213 = 485665) (by norm_num)
theorem B3453617 : Blo 2301435 3453617 := bstep (se 2 (by rfl) ⟨1295106, by rfl⟩ : syracuseStep 3453617 = 2590213) B2590213
theorem B2302411 : Blo 2301435 2302411 := bstep (se 1 (by rfl) ⟨1726808, by rfl⟩ : syracuseStep 2302411 = 3453617) B3453617
theorem B3278245 : Blo 2301435 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B4370993 : Blo 2301435 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B2913995 : Blo 2301435 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B7770653 : Blo 2301435 7770653 := bstep (se 3 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 7770653 = 2913995) B2913995
theorem B5180435 : Blo 2301435 5180435 := bstep (se 1 (by rfl) ⟨3885326, by rfl⟩ : syracuseStep 5180435 = 7770653) B7770653
theorem B3453623 : Blo 2301435 3453623 := bstep (se 1 (by rfl) ⟨2590217, by rfl⟩ : syracuseStep 3453623 = 5180435) B5180435
theorem B2302415 : Blo 2301435 2302415 := bstep (se 1 (by rfl) ⟨1726811, by rfl⟩ : syracuseStep 2302415 = 3453623) B3453623
theorem B3453629 : Blo 2301435 3453629 := bbase (se 3 (by rfl) ⟨647555, by rfl⟩ : syracuseStep 3453629 = 1295111) (by norm_num)
theorem B2302419 : Blo 2301435 2302419 := bstep (se 1 (by rfl) ⟨1726814, by rfl⟩ : syracuseStep 2302419 = 3453629) B3453629
theorem B5180453 : Blo 2301435 5180453 := bbase (se 4 (by rfl) ⟨485667, by rfl⟩ : syracuseStep 5180453 = 971335) (by norm_num)
theorem B3453635 : Blo 2301435 3453635 := bstep (se 1 (by rfl) ⟨2590226, by rfl⟩ : syracuseStep 3453635 = 5180453) B5180453
theorem B2302423 : Blo 2301435 2302423 := bstep (se 1 (by rfl) ⟨1726817, by rfl⟩ : syracuseStep 2302423 = 3453635) B3453635
theorem B5828021 : Blo 2301435 5828021 := bbase (se 5 (by rfl) ⟨273188, by rfl⟩ : syracuseStep 5828021 = 546377) (by norm_num)
theorem B3885347 : Blo 2301435 3885347 := bstep (se 1 (by rfl) ⟨2914010, by rfl⟩ : syracuseStep 3885347 = 5828021) B5828021
theorem B2590231 : Blo 2301435 2590231 := bstep (se 1 (by rfl) ⟨1942673, by rfl⟩ : syracuseStep 2590231 = 3885347) B3885347
theorem B3453641 : Blo 2301435 3453641 := bstep (se 2 (by rfl) ⟨1295115, by rfl⟩ : syracuseStep 3453641 = 2590231) B2590231
theorem B2302427 : Blo 2301435 2302427 := bstep (se 1 (by rfl) ⟨1726820, by rfl⟩ : syracuseStep 2302427 = 3453641) B3453641
theorem B5532077 : Blo 2301435 5532077 := bbase (se 3 (by rfl) ⟨1037264, by rfl⟩ : syracuseStep 5532077 = 2074529) (by norm_num)
theorem B14752205 : Blo 2301435 14752205 := bstep (se 3 (by rfl) ⟨2766038, by rfl⟩ : syracuseStep 14752205 = 5532077) B5532077
theorem B9834803 : Blo 2301435 9834803 := bstep (se 1 (by rfl) ⟨7376102, by rfl⟩ : syracuseStep 9834803 = 14752205) B14752205
theorem B6556535 : Blo 2301435 6556535 := bstep (se 1 (by rfl) ⟨4917401, by rfl⟩ : syracuseStep 6556535 = 9834803) B9834803
theorem B4371023 : Blo 2301435 4371023 := bstep (se 1 (by rfl) ⟨3278267, by rfl⟩ : syracuseStep 4371023 = 6556535) B6556535
theorem B11656061 : Blo 2301435 11656061 := bstep (se 3 (by rfl) ⟨2185511, by rfl⟩ : syracuseStep 11656061 = 4371023) B4371023
theorem B7770707 : Blo 2301435 7770707 := bstep (se 1 (by rfl) ⟨5828030, by rfl⟩ : syracuseStep 7770707 = 11656061) B11656061
theorem B5180471 : Blo 2301435 5180471 := bstep (se 1 (by rfl) ⟨3885353, by rfl⟩ : syracuseStep 5180471 = 7770707) B7770707
theorem B3453647 : Blo 2301435 3453647 := bstep (se 1 (by rfl) ⟨2590235, by rfl⟩ : syracuseStep 3453647 = 5180471) B5180471
theorem B2302431 : Blo 2301435 2302431 := bstep (se 1 (by rfl) ⟨1726823, by rfl⟩ : syracuseStep 2302431 = 3453647) B3453647
theorem B3453653 : Blo 2301435 3453653 := bbase (se 7 (by rfl) ⟨40472, by rfl⟩ : syracuseStep 3453653 = 80945) (by norm_num)
theorem B2302435 : Blo 2301435 2302435 := bstep (se 1 (by rfl) ⟨1726826, by rfl⟩ : syracuseStep 2302435 = 3453653) B3453653
theorem B3111805 : Blo 2301435 3111805 := bbase (se 3 (by rfl) ⟨583463, by rfl⟩ : syracuseStep 3111805 = 1166927) (by norm_num)
theorem B4149073 : Blo 2301435 4149073 := bstep (se 2 (by rfl) ⟨1555902, by rfl⟩ : syracuseStep 4149073 = 3111805) B3111805
theorem B5532097 : Blo 2301435 5532097 := bstep (se 2 (by rfl) ⟨2074536, by rfl⟩ : syracuseStep 5532097 = 4149073) B4149073
theorem B7376129 : Blo 2301435 7376129 := bstep (se 2 (by rfl) ⟨2766048, by rfl⟩ : syracuseStep 7376129 = 5532097) B5532097
theorem B4917419 : Blo 2301435 4917419 := bstep (se 1 (by rfl) ⟨3688064, by rfl⟩ : syracuseStep 4917419 = 7376129) B7376129
theorem B3278279 : Blo 2301435 3278279 := bstep (se 1 (by rfl) ⟨2458709, by rfl⟩ : syracuseStep 3278279 = 4917419) B4917419
theorem B8742077 : Blo 2301435 8742077 := bstep (se 3 (by rfl) ⟨1639139, by rfl⟩ : syracuseStep 8742077 = 3278279) B3278279
theorem B5828051 : Blo 2301435 5828051 := bstep (se 1 (by rfl) ⟨4371038, by rfl⟩ : syracuseStep 5828051 = 8742077) B8742077
theorem B3885367 : Blo 2301435 3885367 := bstep (se 1 (by rfl) ⟨2914025, by rfl⟩ : syracuseStep 3885367 = 5828051) B5828051
theorem B5180489 : Blo 2301435 5180489 := bstep (se 2 (by rfl) ⟨1942683, by rfl⟩ : syracuseStep 5180489 = 3885367) B3885367
theorem B3453659 : Blo 2301435 3453659 := bstep (se 1 (by rfl) ⟨2590244, by rfl⟩ : syracuseStep 3453659 = 5180489) B5180489
theorem B2302439 : Blo 2301435 2302439 := bstep (se 1 (by rfl) ⟨1726829, by rfl⟩ : syracuseStep 2302439 = 3453659) B3453659
theorem B2590249 : Blo 2301435 2590249 := bbase (se 2 (by rfl) ⟨971343, by rfl⟩ : syracuseStep 2590249 = 1942687) (by norm_num)
theorem B3453665 : Blo 2301435 3453665 := bstep (se 2 (by rfl) ⟨1295124, by rfl⟩ : syracuseStep 3453665 = 2590249) B2590249
theorem B2302443 : Blo 2301435 2302443 := bstep (se 1 (by rfl) ⟨1726832, by rfl⟩ : syracuseStep 2302443 = 3453665) B3453665
theorem B5251189 : Blo 2301435 5251189 := bbase (se 5 (by rfl) ⟨246149, by rfl⟩ : syracuseStep 5251189 = 492299) (by norm_num)
theorem B7001585 : Blo 2301435 7001585 := bstep (se 2 (by rfl) ⟨2625594, by rfl⟩ : syracuseStep 7001585 = 5251189) B5251189
theorem B4667723 : Blo 2301435 4667723 := bstep (se 1 (by rfl) ⟨3500792, by rfl⟩ : syracuseStep 4667723 = 7001585) B7001585
theorem B3111815 : Blo 2301435 3111815 := bstep (se 1 (by rfl) ⟨2333861, by rfl⟩ : syracuseStep 3111815 = 4667723) B4667723
theorem B8298173 : Blo 2301435 8298173 := bstep (se 3 (by rfl) ⟨1555907, by rfl⟩ : syracuseStep 8298173 = 3111815) B3111815
theorem B22128461 : Blo 2301435 22128461 := bstep (se 3 (by rfl) ⟨4149086, by rfl⟩ : syracuseStep 22128461 = 8298173) B8298173
theorem B14752307 : Blo 2301435 14752307 := bstep (se 1 (by rfl) ⟨11064230, by rfl⟩ : syracuseStep 14752307 = 22128461) B22128461
theorem B9834871 : Blo 2301435 9834871 := bstep (se 1 (by rfl) ⟨7376153, by rfl⟩ : syracuseStep 9834871 = 14752307) B14752307
theorem B13113161 : Blo 2301435 13113161 := bstep (se 2 (by rfl) ⟨4917435, by rfl⟩ : syracuseStep 13113161 = 9834871) B9834871
theorem B8742107 : Blo 2301435 8742107 := bstep (se 1 (by rfl) ⟨6556580, by rfl⟩ : syracuseStep 8742107 = 13113161) B13113161
theorem B5828071 : Blo 2301435 5828071 := bstep (se 1 (by rfl) ⟨4371053, by rfl⟩ : syracuseStep 5828071 = 8742107) B8742107
theorem B7770761 : Blo 2301435 7770761 := bstep (se 2 (by rfl) ⟨2914035, by rfl⟩ : syracuseStep 7770761 = 5828071) B5828071
theorem B5180507 : Blo 2301435 5180507 := bstep (se 1 (by rfl) ⟨3885380, by rfl⟩ : syracuseStep 5180507 = 7770761) B7770761
theorem B3453671 : Blo 2301435 3453671 := bstep (se 1 (by rfl) ⟨2590253, by rfl⟩ : syracuseStep 3453671 = 5180507) B5180507
theorem B2302447 : Blo 2301435 2302447 := bstep (se 1 (by rfl) ⟨1726835, by rfl⟩ : syracuseStep 2302447 = 3453671) B3453671
theorem B3453677 : Blo 2301435 3453677 := bbase (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) (by norm_num)
theorem B2302451 : Blo 2301435 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B5180525 : Blo 2301435 5180525 := bbase (se 3 (by rfl) ⟨971348, by rfl⟩ : syracuseStep 5180525 = 1942697) (by norm_num)
theorem B3453683 : Blo 2301435 3453683 := bstep (se 1 (by rfl) ⟨2590262, by rfl⟩ : syracuseStep 3453683 = 5180525) B5180525
theorem B2302455 : Blo 2301435 2302455 := bstep (se 1 (by rfl) ⟨1726841, by rfl⟩ : syracuseStep 2302455 = 3453683) B3453683
theorem B4371077 : Blo 2301435 4371077 := bbase (se 4 (by rfl) ⟨409788, by rfl⟩ : syracuseStep 4371077 = 819577) (by norm_num)
theorem B2914051 : Blo 2301435 2914051 := bstep (se 1 (by rfl) ⟨2185538, by rfl⟩ : syracuseStep 2914051 = 4371077) B4371077
theorem B3885401 : Blo 2301435 3885401 := bstep (se 2 (by rfl) ⟨1457025, by rfl⟩ : syracuseStep 3885401 = 2914051) B2914051
theorem B2590267 : Blo 2301435 2590267 := bstep (se 1 (by rfl) ⟨1942700, by rfl⟩ : syracuseStep 2590267 = 3885401) B3885401
theorem B3453689 : Blo 2301435 3453689 := bstep (se 2 (by rfl) ⟨1295133, by rfl⟩ : syracuseStep 3453689 = 2590267) B2590267
theorem B2302459 : Blo 2301435 2302459 := bstep (se 1 (by rfl) ⟨1726844, by rfl⟩ : syracuseStep 2302459 = 3453689) B3453689
theorem B5395493 : Blo 2301435 5395493 := bbase (se 4 (by rfl) ⟨505827, by rfl⟩ : syracuseStep 5395493 = 1011655) (by norm_num)
theorem B3596995 : Blo 2301435 3596995 := bstep (se 1 (by rfl) ⟨2697746, by rfl⟩ : syracuseStep 3596995 = 5395493) B5395493
theorem B4795993 : Blo 2301435 4795993 := bstep (se 2 (by rfl) ⟨1798497, by rfl⟩ : syracuseStep 4795993 = 3596995) B3596995
theorem B25578629 : Blo 2301435 25578629 := bstep (se 4 (by rfl) ⟨2397996, by rfl⟩ : syracuseStep 25578629 = 4795993) B4795993
theorem B17052419 : Blo 2301435 17052419 := bstep (se 1 (by rfl) ⟨12789314, by rfl⟩ : syracuseStep 17052419 = 25578629) B25578629
theorem B11368279 : Blo 2301435 11368279 := bstep (se 1 (by rfl) ⟨8526209, by rfl⟩ : syracuseStep 11368279 = 17052419) B17052419
theorem B15157705 : Blo 2301435 15157705 := bstep (se 2 (by rfl) ⟨5684139, by rfl⟩ : syracuseStep 15157705 = 11368279) B11368279
theorem B20210273 : Blo 2301435 20210273 := bstep (se 2 (by rfl) ⟨7578852, by rfl⟩ : syracuseStep 20210273 = 15157705) B15157705
theorem B13473515 : Blo 2301435 13473515 := bstep (se 1 (by rfl) ⟨10105136, by rfl⟩ : syracuseStep 13473515 = 20210273) B20210273
theorem B8982343 : Blo 2301435 8982343 := bstep (se 1 (by rfl) ⟨6736757, by rfl⟩ : syracuseStep 8982343 = 13473515) B13473515
theorem B11976457 : Blo 2301435 11976457 := bstep (se 2 (by rfl) ⟨4491171, by rfl⟩ : syracuseStep 11976457 = 8982343) B8982343
theorem B15968609 : Blo 2301435 15968609 := bstep (se 2 (by rfl) ⟨5988228, by rfl⟩ : syracuseStep 15968609 = 11976457) B11976457
theorem B10645739 : Blo 2301435 10645739 := bstep (se 1 (by rfl) ⟨7984304, by rfl⟩ : syracuseStep 10645739 = 15968609) B15968609
theorem B7097159 : Blo 2301435 7097159 := bstep (se 1 (by rfl) ⟨5322869, by rfl⟩ : syracuseStep 7097159 = 10645739) B10645739
theorem B4731439 : Blo 2301435 4731439 := bstep (se 1 (by rfl) ⟨3548579, by rfl⟩ : syracuseStep 4731439 = 7097159) B7097159
theorem B6308585 : Blo 2301435 6308585 := bstep (se 2 (by rfl) ⟨2365719, by rfl⟩ : syracuseStep 6308585 = 4731439) B4731439
theorem B4205723 : Blo 2301435 4205723 := bstep (se 1 (by rfl) ⟨3154292, by rfl⟩ : syracuseStep 4205723 = 6308585) B6308585
theorem B11215261 : Blo 2301435 11215261 := bstep (se 3 (by rfl) ⟨2102861, by rfl⟩ : syracuseStep 11215261 = 4205723) B4205723
theorem B14953681 : Blo 2301435 14953681 := bstep (se 2 (by rfl) ⟨5607630, by rfl⟩ : syracuseStep 14953681 = 11215261) B11215261
theorem B19938241 : Blo 2301435 19938241 := bstep (se 2 (by rfl) ⟨7476840, by rfl⟩ : syracuseStep 19938241 = 14953681) B14953681
theorem B106337285 : Blo 2301435 106337285 := bstep (se 4 (by rfl) ⟨9969120, by rfl⟩ : syracuseStep 106337285 = 19938241) B19938241
theorem B70891523 : Blo 2301435 70891523 := bstep (se 1 (by rfl) ⟨53168642, by rfl⟩ : syracuseStep 70891523 = 106337285) B106337285
theorem B47261015 : Blo 2301435 47261015 := bstep (se 1 (by rfl) ⟨35445761, by rfl⟩ : syracuseStep 47261015 = 70891523) B70891523
theorem B31507343 : Blo 2301435 31507343 := bstep (se 1 (by rfl) ⟨23630507, by rfl⟩ : syracuseStep 31507343 = 47261015) B47261015
theorem B21004895 : Blo 2301435 21004895 := bstep (se 1 (by rfl) ⟨15753671, by rfl⟩ : syracuseStep 21004895 = 31507343) B31507343
theorem B14003263 : Blo 2301435 14003263 := bstep (se 1 (by rfl) ⟨10502447, by rfl⟩ : syracuseStep 14003263 = 21004895) B21004895
theorem B74684069 : Blo 2301435 74684069 := bstep (se 4 (by rfl) ⟨7001631, by rfl⟩ : syracuseStep 74684069 = 14003263) B14003263
theorem B49789379 : Blo 2301435 49789379 := bstep (se 1 (by rfl) ⟨37342034, by rfl⟩ : syracuseStep 49789379 = 74684069) B74684069
theorem B33192919 : Blo 2301435 33192919 := bstep (se 1 (by rfl) ⟨24894689, by rfl⟩ : syracuseStep 33192919 = 49789379) B49789379
theorem B44257225 : Blo 2301435 44257225 := bstep (se 2 (by rfl) ⟨16596459, by rfl⟩ : syracuseStep 44257225 = 33192919) B33192919
theorem B59009633 : Blo 2301435 59009633 := bstep (se 2 (by rfl) ⟨22128612, by rfl⟩ : syracuseStep 59009633 = 44257225) B44257225
theorem B39339755 : Blo 2301435 39339755 := bstep (se 1 (by rfl) ⟨29504816, by rfl⟩ : syracuseStep 39339755 = 59009633) B59009633
theorem B26226503 : Blo 2301435 26226503 := bstep (se 1 (by rfl) ⟨19669877, by rfl⟩ : syracuseStep 26226503 = 39339755) B39339755
theorem B17484335 : Blo 2301435 17484335 := bstep (se 1 (by rfl) ⟨13113251, by rfl⟩ : syracuseStep 17484335 = 26226503) B26226503
theorem B11656223 : Blo 2301435 11656223 := bstep (se 1 (by rfl) ⟨8742167, by rfl⟩ : syracuseStep 11656223 = 17484335) B17484335
theorem B7770815 : Blo 2301435 7770815 := bstep (se 1 (by rfl) ⟨5828111, by rfl⟩ : syracuseStep 7770815 = 11656223) B11656223
theorem B5180543 : Blo 2301435 5180543 := bstep (se 1 (by rfl) ⟨3885407, by rfl⟩ : syracuseStep 5180543 = 7770815) B7770815
theorem B3453695 : Blo 2301435 3453695 := bstep (se 1 (by rfl) ⟨2590271, by rfl⟩ : syracuseStep 3453695 = 5180543) B5180543
theorem B2302463 : Blo 2301435 2302463 := bstep (se 1 (by rfl) ⟨1726847, by rfl⟩ : syracuseStep 2302463 = 3453695) B3453695
theorem B3453701 : Blo 2301435 3453701 := bbase (se 4 (by rfl) ⟨323784, by rfl⟩ : syracuseStep 3453701 = 647569) (by norm_num)
theorem B2302467 : Blo 2301435 2302467 := bstep (se 1 (by rfl) ⟨1726850, by rfl⟩ : syracuseStep 2302467 = 3453701) B3453701
theorem B3885421 : Blo 2301435 3885421 := bbase (se 3 (by rfl) ⟨728516, by rfl⟩ : syracuseStep 3885421 = 1457033) (by norm_num)
theorem B5180561 : Blo 2301435 5180561 := bstep (se 2 (by rfl) ⟨1942710, by rfl⟩ : syracuseStep 5180561 = 3885421) B3885421
theorem B3453707 : Blo 2301435 3453707 := bstep (se 1 (by rfl) ⟨2590280, by rfl⟩ : syracuseStep 3453707 = 5180561) B5180561
theorem B2302471 : Blo 2301435 2302471 := bstep (se 1 (by rfl) ⟨1726853, by rfl⟩ : syracuseStep 2302471 = 3453707) B3453707
theorem B2590285 : Blo 2301435 2590285 := bbase (se 3 (by rfl) ⟨485678, by rfl⟩ : syracuseStep 2590285 = 971357) (by norm_num)
theorem B3453713 : Blo 2301435 3453713 := bstep (se 2 (by rfl) ⟨1295142, by rfl⟩ : syracuseStep 3453713 = 2590285) B2590285
theorem B2302475 : Blo 2301435 2302475 := bstep (se 1 (by rfl) ⟨1726856, by rfl⟩ : syracuseStep 2302475 = 3453713) B3453713
theorem B7770869 : Blo 2301435 7770869 := bbase (se 5 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 7770869 = 728519) (by norm_num)
theorem B5180579 : Blo 2301435 5180579 := bstep (se 1 (by rfl) ⟨3885434, by rfl⟩ : syracuseStep 5180579 = 7770869) B7770869
theorem B3453719 : Blo 2301435 3453719 := bstep (se 1 (by rfl) ⟨2590289, by rfl⟩ : syracuseStep 3453719 = 5180579) B5180579
theorem B2302479 : Blo 2301435 2302479 := bstep (se 1 (by rfl) ⟨1726859, by rfl⟩ : syracuseStep 2302479 = 3453719) B3453719
theorem B3453725 : Blo 2301435 3453725 := bbase (se 3 (by rfl) ⟨647573, by rfl⟩ : syracuseStep 3453725 = 1295147) (by norm_num)
theorem B2302483 : Blo 2301435 2302483 := bstep (se 1 (by rfl) ⟨1726862, by rfl⟩ : syracuseStep 2302483 = 3453725) B3453725
theorem B5180597 : Blo 2301435 5180597 := bbase (se 5 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 5180597 = 485681) (by norm_num)
theorem B3453731 : Blo 2301435 3453731 := bstep (se 1 (by rfl) ⟨2590298, by rfl⟩ : syracuseStep 3453731 = 5180597) B5180597
theorem B2302487 : Blo 2301435 2302487 := bstep (se 1 (by rfl) ⟨1726865, by rfl⟩ : syracuseStep 2302487 = 3453731) B3453731
theorem B2458765 : Blo 2301435 2458765 := bbase (se 3 (by rfl) ⟨461018, by rfl⟩ : syracuseStep 2458765 = 922037) (by norm_num)
theorem B13113413 : Blo 2301435 13113413 := bstep (se 4 (by rfl) ⟨1229382, by rfl⟩ : syracuseStep 13113413 = 2458765) B2458765
theorem B8742275 : Blo 2301435 8742275 := bstep (se 1 (by rfl) ⟨6556706, by rfl⟩ : syracuseStep 8742275 = 13113413) B13113413
theorem B5828183 : Blo 2301435 5828183 := bstep (se 1 (by rfl) ⟨4371137, by rfl⟩ : syracuseStep 5828183 = 8742275) B8742275
theorem B3885455 : Blo 2301435 3885455 := bstep (se 1 (by rfl) ⟨2914091, by rfl⟩ : syracuseStep 3885455 = 5828183) B5828183
theorem B2590303 : Blo 2301435 2590303 := bstep (se 1 (by rfl) ⟨1942727, by rfl⟩ : syracuseStep 2590303 = 3885455) B3885455
theorem B3453737 : Blo 2301435 3453737 := bstep (se 2 (by rfl) ⟨1295151, by rfl⟩ : syracuseStep 3453737 = 2590303) B2590303
theorem B2302491 : Blo 2301435 2302491 := bstep (se 1 (by rfl) ⟨1726868, by rfl⟩ : syracuseStep 2302491 = 3453737) B3453737
theorem B2458769 : Blo 2301435 2458769 := bbase (se 2 (by rfl) ⟨922038, by rfl⟩ : syracuseStep 2458769 = 1844077) (by norm_num)
theorem B6556717 : Blo 2301435 6556717 := bstep (se 3 (by rfl) ⟨1229384, by rfl⟩ : syracuseStep 6556717 = 2458769) B2458769
theorem B8742289 : Blo 2301435 8742289 := bstep (se 2 (by rfl) ⟨3278358, by rfl⟩ : syracuseStep 8742289 = 6556717) B6556717
theorem B11656385 : Blo 2301435 11656385 := bstep (se 2 (by rfl) ⟨4371144, by rfl⟩ : syracuseStep 11656385 = 8742289) B8742289
theorem B7770923 : Blo 2301435 7770923 := bstep (se 1 (by rfl) ⟨5828192, by rfl⟩ : syracuseStep 7770923 = 11656385) B11656385
theorem B5180615 : Blo 2301435 5180615 := bstep (se 1 (by rfl) ⟨3885461, by rfl⟩ : syracuseStep 5180615 = 7770923) B7770923
theorem B3453743 : Blo 2301435 3453743 := bstep (se 1 (by rfl) ⟨2590307, by rfl⟩ : syracuseStep 3453743 = 5180615) B5180615
theorem B2302495 : Blo 2301435 2302495 := bstep (se 1 (by rfl) ⟨1726871, by rfl⟩ : syracuseStep 2302495 = 3453743) B3453743
theorem B3453749 : Blo 2301435 3453749 := bbase (se 5 (by rfl) ⟨161894, by rfl⟩ : syracuseStep 3453749 = 323789) (by norm_num)
theorem B2302499 : Blo 2301435 2302499 := bstep (se 1 (by rfl) ⟨1726874, by rfl⟩ : syracuseStep 2302499 = 3453749) B3453749
theorem B5828213 : Blo 2301435 5828213 := bbase (se 5 (by rfl) ⟨273197, by rfl⟩ : syracuseStep 5828213 = 546395) (by norm_num)
theorem B3885475 : Blo 2301435 3885475 := bstep (se 1 (by rfl) ⟨2914106, by rfl⟩ : syracuseStep 3885475 = 5828213) B5828213
theorem B5180633 : Blo 2301435 5180633 := bstep (se 2 (by rfl) ⟨1942737, by rfl⟩ : syracuseStep 5180633 = 3885475) B3885475
theorem B3453755 : Blo 2301435 3453755 := bstep (se 1 (by rfl) ⟨2590316, by rfl⟩ : syracuseStep 3453755 = 5180633) B5180633
theorem B2302503 : Blo 2301435 2302503 := bstep (se 1 (by rfl) ⟨1726877, by rfl⟩ : syracuseStep 2302503 = 3453755) B3453755
theorem B2590321 : Blo 2301435 2590321 := bbase (se 2 (by rfl) ⟨971370, by rfl⟩ : syracuseStep 2590321 = 1942741) (by norm_num)
theorem B3453761 : Blo 2301435 3453761 := bstep (se 2 (by rfl) ⟨1295160, by rfl⟩ : syracuseStep 3453761 = 2590321) B2590321
theorem B2302507 : Blo 2301435 2302507 := bstep (se 1 (by rfl) ⟨1726880, by rfl⟩ : syracuseStep 2302507 = 3453761) B3453761
theorem B3938501 : Blo 2301435 3938501 := bbase (se 4 (by rfl) ⟨369234, by rfl⟩ : syracuseStep 3938501 = 738469) (by norm_num)
theorem B10502669 : Blo 2301435 10502669 := bstep (se 3 (by rfl) ⟨1969250, by rfl⟩ : syracuseStep 10502669 = 3938501) B3938501
theorem B28007117 : Blo 2301435 28007117 := bstep (se 3 (by rfl) ⟨5251334, by rfl⟩ : syracuseStep 28007117 = 10502669) B10502669
theorem B18671411 : Blo 2301435 18671411 := bstep (se 1 (by rfl) ⟨14003558, by rfl⟩ : syracuseStep 18671411 = 28007117) B28007117
theorem B12447607 : Blo 2301435 12447607 := bstep (se 1 (by rfl) ⟨9335705, by rfl⟩ : syracuseStep 12447607 = 18671411) B18671411
theorem B16596809 : Blo 2301435 16596809 := bstep (se 2 (by rfl) ⟨6223803, by rfl⟩ : syracuseStep 16596809 = 12447607) B12447607
theorem B11064539 : Blo 2301435 11064539 := bstep (se 1 (by rfl) ⟨8298404, by rfl⟩ : syracuseStep 11064539 = 16596809) B16596809
theorem B7376359 : Blo 2301435 7376359 := bstep (se 1 (by rfl) ⟨5532269, by rfl⟩ : syracuseStep 7376359 = 11064539) B11064539
theorem B9835145 : Blo 2301435 9835145 := bstep (se 2 (by rfl) ⟨3688179, by rfl⟩ : syracuseStep 9835145 = 7376359) B7376359
theorem B6556763 : Blo 2301435 6556763 := bstep (se 1 (by rfl) ⟨4917572, by rfl⟩ : syracuseStep 6556763 = 9835145) B9835145
theorem B4371175 : Blo 2301435 4371175 := bstep (se 1 (by rfl) ⟨3278381, by rfl⟩ : syracuseStep 4371175 = 6556763) B6556763
theorem B5828233 : Blo 2301435 5828233 := bstep (se 2 (by rfl) ⟨2185587, by rfl⟩ : syracuseStep 5828233 = 4371175) B4371175
theorem B7770977 : Blo 2301435 7770977 := bstep (se 2 (by rfl) ⟨2914116, by rfl⟩ : syracuseStep 7770977 = 5828233) B5828233
theorem B5180651 : Blo 2301435 5180651 := bstep (se 1 (by rfl) ⟨3885488, by rfl⟩ : syracuseStep 5180651 = 7770977) B7770977
theorem B3453767 : Blo 2301435 3453767 := bstep (se 1 (by rfl) ⟨2590325, by rfl⟩ : syracuseStep 3453767 = 5180651) B5180651
theorem B2302511 : Blo 2301435 2302511 := bstep (se 1 (by rfl) ⟨1726883, by rfl⟩ : syracuseStep 2302511 = 3453767) B3453767
theorem B3453773 : Blo 2301435 3453773 := bbase (se 3 (by rfl) ⟨647582, by rfl⟩ : syracuseStep 3453773 = 1295165) (by norm_num)
theorem B2302515 : Blo 2301435 2302515 := bstep (se 1 (by rfl) ⟨1726886, by rfl⟩ : syracuseStep 2302515 = 3453773) B3453773
theorem B5180669 : Blo 2301435 5180669 := bbase (se 3 (by rfl) ⟨971375, by rfl⟩ : syracuseStep 5180669 = 1942751) (by norm_num)
theorem B3453779 : Blo 2301435 3453779 := bstep (se 1 (by rfl) ⟨2590334, by rfl⟩ : syracuseStep 3453779 = 5180669) B5180669
theorem B2302519 : Blo 2301435 2302519 := bstep (se 1 (by rfl) ⟨1726889, by rfl⟩ : syracuseStep 2302519 = 3453779) B3453779
theorem B3885509 : Blo 2301435 3885509 := bbase (se 4 (by rfl) ⟨364266, by rfl⟩ : syracuseStep 3885509 = 728533) (by norm_num)
theorem B2590339 : Blo 2301435 2590339 := bstep (se 1 (by rfl) ⟨1942754, by rfl⟩ : syracuseStep 2590339 = 3885509) B3885509
theorem B3453785 : Blo 2301435 3453785 := bstep (se 2 (by rfl) ⟨1295169, by rfl⟩ : syracuseStep 3453785 = 2590339) B2590339
theorem B2302523 : Blo 2301435 2302523 := bstep (se 1 (by rfl) ⟨1726892, by rfl⟩ : syracuseStep 2302523 = 3453785) B3453785
theorem B17484821 : Blo 2301435 17484821 := bbase (se 6 (by rfl) ⟨409800, by rfl⟩ : syracuseStep 17484821 = 819601) (by norm_num)
theorem B11656547 : Blo 2301435 11656547 := bstep (se 1 (by rfl) ⟨8742410, by rfl⟩ : syracuseStep 11656547 = 17484821) B17484821
theorem B7771031 : Blo 2301435 7771031 := bstep (se 1 (by rfl) ⟨5828273, by rfl⟩ : syracuseStep 7771031 = 11656547) B11656547
theorem B5180687 : Blo 2301435 5180687 := bstep (se 1 (by rfl) ⟨3885515, by rfl⟩ : syracuseStep 5180687 = 7771031) B7771031
theorem B3453791 : Blo 2301435 3453791 := bstep (se 1 (by rfl) ⟨2590343, by rfl⟩ : syracuseStep 3453791 = 5180687) B5180687
theorem B2302527 : Blo 2301435 2302527 := bstep (se 1 (by rfl) ⟨1726895, by rfl⟩ : syracuseStep 2302527 = 3453791) B3453791
theorem B3453797 : Blo 2301435 3453797 := bbase (se 4 (by rfl) ⟨323793, by rfl⟩ : syracuseStep 3453797 = 647587) (by norm_num)
theorem B2302531 : Blo 2301435 2302531 := bstep (se 1 (by rfl) ⟨1726898, by rfl⟩ : syracuseStep 2302531 = 3453797) B3453797
theorem B4371221 : Blo 2301435 4371221 := bbase (se 6 (by rfl) ⟨102450, by rfl⟩ : syracuseStep 4371221 = 204901) (by norm_num)
theorem B2914147 : Blo 2301435 2914147 := bstep (se 1 (by rfl) ⟨2185610, by rfl⟩ : syracuseStep 2914147 = 4371221) B4371221
theorem B3885529 : Blo 2301435 3885529 := bstep (se 2 (by rfl) ⟨1457073, by rfl⟩ : syracuseStep 3885529 = 2914147) B2914147
theorem B5180705 : Blo 2301435 5180705 := bstep (se 2 (by rfl) ⟨1942764, by rfl⟩ : syracuseStep 5180705 = 3885529) B3885529
theorem B3453803 : Blo 2301435 3453803 := bstep (se 1 (by rfl) ⟨2590352, by rfl⟩ : syracuseStep 3453803 = 5180705) B5180705
theorem B2302535 : Blo 2301435 2302535 := bstep (se 1 (by rfl) ⟨1726901, by rfl⟩ : syracuseStep 2302535 = 3453803) B3453803
theorem B2590357 : Blo 2301435 2590357 := bbase (se 6 (by rfl) ⟨60711, by rfl⟩ : syracuseStep 2590357 = 121423) (by norm_num)
theorem B3453809 : Blo 2301435 3453809 := bstep (se 2 (by rfl) ⟨1295178, by rfl⟩ : syracuseStep 3453809 = 2590357) B2590357
theorem B2302539 : Blo 2301435 2302539 := bstep (se 1 (by rfl) ⟨1726904, by rfl⟩ : syracuseStep 2302539 = 3453809) B3453809
theorem B2914157 : Blo 2301435 2914157 := bbase (se 3 (by rfl) ⟨546404, by rfl⟩ : syracuseStep 2914157 = 1092809) (by norm_num)
theorem B7771085 : Blo 2301435 7771085 := bstep (se 3 (by rfl) ⟨1457078, by rfl⟩ : syracuseStep 7771085 = 2914157) B2914157
theorem B5180723 : Blo 2301435 5180723 := bstep (se 1 (by rfl) ⟨3885542, by rfl⟩ : syracuseStep 5180723 = 7771085) B7771085
theorem B3453815 : Blo 2301435 3453815 := bstep (se 1 (by rfl) ⟨2590361, by rfl⟩ : syracuseStep 3453815 = 5180723) B5180723
theorem B2302543 : Blo 2301435 2302543 := bstep (se 1 (by rfl) ⟨1726907, by rfl⟩ : syracuseStep 2302543 = 3453815) B3453815
theorem B3453821 : Blo 2301435 3453821 := bbase (se 3 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 3453821 = 1295183) (by norm_num)
theorem B2302547 : Blo 2301435 2302547 := bstep (se 1 (by rfl) ⟨1726910, by rfl⟩ : syracuseStep 2302547 = 3453821) B3453821
theorem B5180741 : Blo 2301435 5180741 := bbase (se 4 (by rfl) ⟨485694, by rfl⟩ : syracuseStep 5180741 = 971389) (by norm_num)
theorem B3453827 : Blo 2301435 3453827 := bstep (se 1 (by rfl) ⟨2590370, by rfl⟩ : syracuseStep 3453827 = 5180741) B5180741
theorem B2302551 : Blo 2301435 2302551 := bstep (se 1 (by rfl) ⟨1726913, by rfl⟩ : syracuseStep 2302551 = 3453827) B3453827
theorem B7376501 : Blo 2301435 7376501 := bbase (se 5 (by rfl) ⟨345773, by rfl⟩ : syracuseStep 7376501 = 691547) (by norm_num)
theorem B4917667 : Blo 2301435 4917667 := bstep (se 1 (by rfl) ⟨3688250, by rfl⟩ : syracuseStep 4917667 = 7376501) B7376501
theorem B6556889 : Blo 2301435 6556889 := bstep (se 2 (by rfl) ⟨2458833, by rfl⟩ : syracuseStep 6556889 = 4917667) B4917667
theorem B4371259 : Blo 2301435 4371259 := bstep (se 1 (by rfl) ⟨3278444, by rfl⟩ : syracuseStep 4371259 = 6556889) B6556889
theorem B5828345 : Blo 2301435 5828345 := bstep (se 2 (by rfl) ⟨2185629, by rfl⟩ : syracuseStep 5828345 = 4371259) B4371259
theorem B3885563 : Blo 2301435 3885563 := bstep (se 1 (by rfl) ⟨2914172, by rfl⟩ : syracuseStep 3885563 = 5828345) B5828345
theorem B2590375 : Blo 2301435 2590375 := bstep (se 1 (by rfl) ⟨1942781, by rfl⟩ : syracuseStep 2590375 = 3885563) B3885563
theorem B3453833 : Blo 2301435 3453833 := bstep (se 2 (by rfl) ⟨1295187, by rfl⟩ : syracuseStep 3453833 = 2590375) B2590375
theorem B2302555 : Blo 2301435 2302555 := bstep (se 1 (by rfl) ⟨1726916, by rfl⟩ : syracuseStep 2302555 = 3453833) B3453833
theorem B11656709 : Blo 2301435 11656709 := bbase (se 4 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 11656709 = 2185633) (by norm_num)
theorem B7771139 : Blo 2301435 7771139 := bstep (se 1 (by rfl) ⟨5828354, by rfl⟩ : syracuseStep 7771139 = 11656709) B11656709
theorem B5180759 : Blo 2301435 5180759 := bstep (se 1 (by rfl) ⟨3885569, by rfl⟩ : syracuseStep 5180759 = 7771139) B7771139
theorem B3453839 : Blo 2301435 3453839 := bstep (se 1 (by rfl) ⟨2590379, by rfl⟩ : syracuseStep 3453839 = 5180759) B5180759
theorem B2302559 : Blo 2301435 2302559 := bstep (se 1 (by rfl) ⟨1726919, by rfl⟩ : syracuseStep 2302559 = 3453839) B3453839
theorem B3453845 : Blo 2301435 3453845 := bbase (se 6 (by rfl) ⟨80949, by rfl⟩ : syracuseStep 3453845 = 161899) (by norm_num)
theorem B2302563 : Blo 2301435 2302563 := bstep (se 1 (by rfl) ⟨1726922, by rfl⟩ : syracuseStep 2302563 = 3453845) B3453845
theorem B13113845 : Blo 2301435 13113845 := bbase (se 5 (by rfl) ⟨614711, by rfl⟩ : syracuseStep 13113845 = 1229423) (by norm_num)
theorem B8742563 : Blo 2301435 8742563 := bstep (se 1 (by rfl) ⟨6556922, by rfl⟩ : syracuseStep 8742563 = 13113845) B13113845
theorem B5828375 : Blo 2301435 5828375 := bstep (se 1 (by rfl) ⟨4371281, by rfl⟩ : syracuseStep 5828375 = 8742563) B8742563
theorem B3885583 : Blo 2301435 3885583 := bstep (se 1 (by rfl) ⟨2914187, by rfl⟩ : syracuseStep 3885583 = 5828375) B5828375
theorem B5180777 : Blo 2301435 5180777 := bstep (se 2 (by rfl) ⟨1942791, by rfl⟩ : syracuseStep 5180777 = 3885583) B3885583
theorem B3453851 : Blo 2301435 3453851 := bstep (se 1 (by rfl) ⟨2590388, by rfl⟩ : syracuseStep 3453851 = 5180777) B5180777
theorem B2302567 : Blo 2301435 2302567 := bstep (se 1 (by rfl) ⟨1726925, by rfl⟩ : syracuseStep 2302567 = 3453851) B3453851
theorem B2590393 : Blo 2301435 2590393 := bbase (se 2 (by rfl) ⟨971397, by rfl⟩ : syracuseStep 2590393 = 1942795) (by norm_num)
theorem B3453857 : Blo 2301435 3453857 := bstep (se 2 (by rfl) ⟨1295196, by rfl⟩ : syracuseStep 3453857 = 2590393) B2590393
theorem B2302571 : Blo 2301435 2302571 := bstep (se 1 (by rfl) ⟨1726928, by rfl⟩ : syracuseStep 2302571 = 3453857) B3453857
theorem B4917709 : Blo 2301435 4917709 := bbase (se 3 (by rfl) ⟨922070, by rfl⟩ : syracuseStep 4917709 = 1844141) (by norm_num)
theorem B6556945 : Blo 2301435 6556945 := bstep (se 2 (by rfl) ⟨2458854, by rfl⟩ : syracuseStep 6556945 = 4917709) B4917709
theorem B8742593 : Blo 2301435 8742593 := bstep (se 2 (by rfl) ⟨3278472, by rfl⟩ : syracuseStep 8742593 = 6556945) B6556945
theorem B5828395 : Blo 2301435 5828395 := bstep (se 1 (by rfl) ⟨4371296, by rfl⟩ : syracuseStep 5828395 = 8742593) B8742593
theorem B7771193 : Blo 2301435 7771193 := bstep (se 2 (by rfl) ⟨2914197, by rfl⟩ : syracuseStep 7771193 = 5828395) B5828395
theorem B5180795 : Blo 2301435 5180795 := bstep (se 1 (by rfl) ⟨3885596, by rfl⟩ : syracuseStep 5180795 = 7771193) B7771193
theorem B3453863 : Blo 2301435 3453863 := bstep (se 1 (by rfl) ⟨2590397, by rfl⟩ : syracuseStep 3453863 = 5180795) B5180795
theorem B2302575 : Blo 2301435 2302575 := bstep (se 1 (by rfl) ⟨1726931, by rfl⟩ : syracuseStep 2302575 = 3453863) B3453863
theorem B3453869 : Blo 2301435 3453869 := bbase (se 3 (by rfl) ⟨647600, by rfl⟩ : syracuseStep 3453869 = 1295201) (by norm_num)
theorem B2302579 : Blo 2301435 2302579 := bstep (se 1 (by rfl) ⟨1726934, by rfl⟩ : syracuseStep 2302579 = 3453869) B3453869
theorem B5180813 : Blo 2301435 5180813 := bbase (se 3 (by rfl) ⟨971402, by rfl⟩ : syracuseStep 5180813 = 1942805) (by norm_num)
theorem B3453875 : Blo 2301435 3453875 := bstep (se 1 (by rfl) ⟨2590406, by rfl⟩ : syracuseStep 3453875 = 5180813) B5180813
theorem B2302583 : Blo 2301435 2302583 := bstep (se 1 (by rfl) ⟨1726937, by rfl⟩ : syracuseStep 2302583 = 3453875) B3453875
theorem B2914213 : Blo 2301435 2914213 := bbase (se 4 (by rfl) ⟨273207, by rfl⟩ : syracuseStep 2914213 = 546415) (by norm_num)
theorem B3885617 : Blo 2301435 3885617 := bstep (se 2 (by rfl) ⟨1457106, by rfl⟩ : syracuseStep 3885617 = 2914213) B2914213
theorem B2590411 : Blo 2301435 2590411 := bstep (se 1 (by rfl) ⟨1942808, by rfl⟩ : syracuseStep 2590411 = 3885617) B3885617
theorem B3453881 : Blo 2301435 3453881 := bstep (se 2 (by rfl) ⟨1295205, by rfl⟩ : syracuseStep 3453881 = 2590411) B2590411
theorem B2302587 : Blo 2301435 2302587 := bstep (se 1 (by rfl) ⟨1726940, by rfl⟩ : syracuseStep 2302587 = 3453881) B3453881
theorem B5251517 : Blo 2301435 5251517 := bbase (se 3 (by rfl) ⟨984659, by rfl⟩ : syracuseStep 5251517 = 1969319) (by norm_num)
theorem B3501011 : Blo 2301435 3501011 := bstep (se 1 (by rfl) ⟨2625758, by rfl⟩ : syracuseStep 3501011 = 5251517) B5251517
theorem B2334007 : Blo 2301435 2334007 := bstep (se 1 (by rfl) ⟨1750505, by rfl⟩ : syracuseStep 2334007 = 3501011) B3501011
theorem B12448037 : Blo 2301435 12448037 := bstep (se 4 (by rfl) ⟨1167003, by rfl⟩ : syracuseStep 12448037 = 2334007) B2334007
theorem B33194765 : Blo 2301435 33194765 := bstep (se 3 (by rfl) ⟨6224018, by rfl⟩ : syracuseStep 33194765 = 12448037) B12448037
theorem B22129843 : Blo 2301435 22129843 := bstep (se 1 (by rfl) ⟨16597382, by rfl⟩ : syracuseStep 22129843 = 33194765) B33194765
theorem B29506457 : Blo 2301435 29506457 := bstep (se 2 (by rfl) ⟨11064921, by rfl⟩ : syracuseStep 29506457 = 22129843) B22129843
theorem B19670971 : Blo 2301435 19670971 := bstep (se 1 (by rfl) ⟨14753228, by rfl⟩ : syracuseStep 19670971 = 29506457) B29506457
theorem B26227961 : Blo 2301435 26227961 := bstep (se 2 (by rfl) ⟨9835485, by rfl⟩ : syracuseStep 26227961 = 19670971) B19670971
theorem B17485307 : Blo 2301435 17485307 := bstep (se 1 (by rfl) ⟨13113980, by rfl⟩ : syracuseStep 17485307 = 26227961) B26227961
theorem B11656871 : Blo 2301435 11656871 := bstep (se 1 (by rfl) ⟨8742653, by rfl⟩ : syracuseStep 11656871 = 17485307) B17485307
theorem B7771247 : Blo 2301435 7771247 := bstep (se 1 (by rfl) ⟨5828435, by rfl⟩ : syracuseStep 7771247 = 11656871) B11656871
theorem B5180831 : Blo 2301435 5180831 := bstep (se 1 (by rfl) ⟨3885623, by rfl⟩ : syracuseStep 5180831 = 7771247) B7771247
theorem B3453887 : Blo 2301435 3453887 := bstep (se 1 (by rfl) ⟨2590415, by rfl⟩ : syracuseStep 3453887 = 5180831) B5180831
theorem B2302591 : Blo 2301435 2302591 := bstep (se 1 (by rfl) ⟨1726943, by rfl⟩ : syracuseStep 2302591 = 3453887) B3453887
theorem B3453893 : Blo 2301435 3453893 := bbase (se 4 (by rfl) ⟨323802, by rfl⟩ : syracuseStep 3453893 = 647605) (by norm_num)
theorem B2302595 : Blo 2301435 2302595 := bstep (se 1 (by rfl) ⟨1726946, by rfl⟩ : syracuseStep 2302595 = 3453893) B3453893
theorem B3885637 : Blo 2301435 3885637 := bbase (se 4 (by rfl) ⟨364278, by rfl⟩ : syracuseStep 3885637 = 728557) (by norm_num)
theorem B5180849 : Blo 2301435 5180849 := bstep (se 2 (by rfl) ⟨1942818, by rfl⟩ : syracuseStep 5180849 = 3885637) B3885637
theorem B3453899 : Blo 2301435 3453899 := bstep (se 1 (by rfl) ⟨2590424, by rfl⟩ : syracuseStep 3453899 = 5180849) B5180849
theorem B2302599 : Blo 2301435 2302599 := bstep (se 1 (by rfl) ⟨1726949, by rfl⟩ : syracuseStep 2302599 = 3453899) B3453899
theorem B2590429 : Blo 2301435 2590429 := bbase (se 3 (by rfl) ⟨485705, by rfl⟩ : syracuseStep 2590429 = 971411) (by norm_num)
theorem B3453905 : Blo 2301435 3453905 := bstep (se 2 (by rfl) ⟨1295214, by rfl⟩ : syracuseStep 3453905 = 2590429) B2590429
theorem B2302603 : Blo 2301435 2302603 := bstep (se 1 (by rfl) ⟨1726952, by rfl⟩ : syracuseStep 2302603 = 3453905) B3453905
theorem B7771301 : Blo 2301435 7771301 := bbase (se 4 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 7771301 = 1457119) (by norm_num)
theorem B5180867 : Blo 2301435 5180867 := bstep (se 1 (by rfl) ⟨3885650, by rfl⟩ : syracuseStep 5180867 = 7771301) B7771301
theorem B3453911 : Blo 2301435 3453911 := bstep (se 1 (by rfl) ⟨2590433, by rfl⟩ : syracuseStep 3453911 = 5180867) B5180867
theorem B2302607 : Blo 2301435 2302607 := bstep (se 1 (by rfl) ⟨1726955, by rfl⟩ : syracuseStep 2302607 = 3453911) B3453911
theorem B3453917 : Blo 2301435 3453917 := bbase (se 3 (by rfl) ⟨647609, by rfl⟩ : syracuseStep 3453917 = 1295219) (by norm_num)
theorem B2302611 : Blo 2301435 2302611 := bstep (se 1 (by rfl) ⟨1726958, by rfl⟩ : syracuseStep 2302611 = 3453917) B3453917
theorem B5180885 : Blo 2301435 5180885 := bbase (se 7 (by rfl) ⟨60713, by rfl⟩ : syracuseStep 5180885 = 121427) (by norm_num)
theorem B3453923 : Blo 2301435 3453923 := bstep (se 1 (by rfl) ⟨2590442, by rfl⟩ : syracuseStep 3453923 = 5180885) B5180885
theorem B2302615 : Blo 2301435 2302615 := bstep (se 1 (by rfl) ⟨1726961, by rfl⟩ : syracuseStep 2302615 = 3453923) B3453923
theorem B4149397 : Blo 2301435 4149397 := bbase (se 6 (by rfl) ⟨97251, by rfl⟩ : syracuseStep 4149397 = 194503) (by norm_num)
theorem B22130117 : Blo 2301435 22130117 := bstep (se 4 (by rfl) ⟨2074698, by rfl⟩ : syracuseStep 22130117 = 4149397) B4149397
theorem B14753411 : Blo 2301435 14753411 := bstep (se 1 (by rfl) ⟨11065058, by rfl⟩ : syracuseStep 14753411 = 22130117) B22130117
theorem B9835607 : Blo 2301435 9835607 := bstep (se 1 (by rfl) ⟨7376705, by rfl⟩ : syracuseStep 9835607 = 14753411) B14753411
theorem B6557071 : Blo 2301435 6557071 := bstep (se 1 (by rfl) ⟨4917803, by rfl⟩ : syracuseStep 6557071 = 9835607) B9835607
theorem B8742761 : Blo 2301435 8742761 := bstep (se 2 (by rfl) ⟨3278535, by rfl⟩ : syracuseStep 8742761 = 6557071) B6557071
theorem B5828507 : Blo 2301435 5828507 := bstep (se 1 (by rfl) ⟨4371380, by rfl⟩ : syracuseStep 5828507 = 8742761) B8742761
theorem B3885671 : Blo 2301435 3885671 := bstep (se 1 (by rfl) ⟨2914253, by rfl⟩ : syracuseStep 3885671 = 5828507) B5828507
theorem B2590447 : Blo 2301435 2590447 := bstep (se 1 (by rfl) ⟨1942835, by rfl⟩ : syracuseStep 2590447 = 3885671) B3885671
theorem B3453929 : Blo 2301435 3453929 := bstep (se 2 (by rfl) ⟨1295223, by rfl⟩ : syracuseStep 3453929 = 2590447) B2590447
theorem B2302619 : Blo 2301435 2302619 := bstep (se 1 (by rfl) ⟨1726964, by rfl⟩ : syracuseStep 2302619 = 3453929) B3453929
theorem B2766269 : Blo 2301435 2766269 := bbase (se 3 (by rfl) ⟨518675, by rfl⟩ : syracuseStep 2766269 = 1037351) (by norm_num)
theorem B7376717 : Blo 2301435 7376717 := bstep (se 3 (by rfl) ⟨1383134, by rfl⟩ : syracuseStep 7376717 = 2766269) B2766269
theorem B19671245 : Blo 2301435 19671245 := bstep (se 3 (by rfl) ⟨3688358, by rfl⟩ : syracuseStep 19671245 = 7376717) B7376717
theorem B13114163 : Blo 2301435 13114163 := bstep (se 1 (by rfl) ⟨9835622, by rfl⟩ : syracuseStep 13114163 = 19671245) B19671245
theorem B8742775 : Blo 2301435 8742775 := bstep (se 1 (by rfl) ⟨6557081, by rfl⟩ : syracuseStep 8742775 = 13114163) B13114163
theorem B11657033 : Blo 2301435 11657033 := bstep (se 2 (by rfl) ⟨4371387, by rfl⟩ : syracuseStep 11657033 = 8742775) B8742775
theorem B7771355 : Blo 2301435 7771355 := bstep (se 1 (by rfl) ⟨5828516, by rfl⟩ : syracuseStep 7771355 = 11657033) B11657033
theorem B5180903 : Blo 2301435 5180903 := bstep (se 1 (by rfl) ⟨3885677, by rfl⟩ : syracuseStep 5180903 = 7771355) B7771355
theorem B3453935 : Blo 2301435 3453935 := bstep (se 1 (by rfl) ⟨2590451, by rfl⟩ : syracuseStep 3453935 = 5180903) B5180903
theorem B2302623 : Blo 2301435 2302623 := bstep (se 1 (by rfl) ⟨1726967, by rfl⟩ : syracuseStep 2302623 = 3453935) B3453935
theorem B3453941 : Blo 2301435 3453941 := bbase (se 5 (by rfl) ⟨161903, by rfl⟩ : syracuseStep 3453941 = 323807) (by norm_num)
theorem B2302627 : Blo 2301435 2302627 := bstep (se 1 (by rfl) ⟨1726970, by rfl⟩ : syracuseStep 2302627 = 3453941) B3453941
theorem B4917829 : Blo 2301435 4917829 := bbase (se 4 (by rfl) ⟨461046, by rfl⟩ : syracuseStep 4917829 = 922093) (by norm_num)
theorem B6557105 : Blo 2301435 6557105 := bstep (se 2 (by rfl) ⟨2458914, by rfl⟩ : syracuseStep 6557105 = 4917829) B4917829
theorem B4371403 : Blo 2301435 4371403 := bstep (se 1 (by rfl) ⟨3278552, by rfl⟩ : syracuseStep 4371403 = 6557105) B6557105
theorem B5828537 : Blo 2301435 5828537 := bstep (se 2 (by rfl) ⟨2185701, by rfl⟩ : syracuseStep 5828537 = 4371403) B4371403
theorem B3885691 : Blo 2301435 3885691 := bstep (se 1 (by rfl) ⟨2914268, by rfl⟩ : syracuseStep 3885691 = 5828537) B5828537
theorem B5180921 : Blo 2301435 5180921 := bstep (se 2 (by rfl) ⟨1942845, by rfl⟩ : syracuseStep 5180921 = 3885691) B3885691
theorem B3453947 : Blo 2301435 3453947 := bstep (se 1 (by rfl) ⟨2590460, by rfl⟩ : syracuseStep 3453947 = 5180921) B5180921
theorem B2302631 : Blo 2301435 2302631 := bstep (se 1 (by rfl) ⟨1726973, by rfl⟩ : syracuseStep 2302631 = 3453947) B3453947
theorem B2590465 : Blo 2301435 2590465 := bbase (se 2 (by rfl) ⟨971424, by rfl⟩ : syracuseStep 2590465 = 1942849) (by norm_num)
theorem B3453953 : Blo 2301435 3453953 := bstep (se 2 (by rfl) ⟨1295232, by rfl⟩ : syracuseStep 3453953 = 2590465) B2590465
theorem B2302635 : Blo 2301435 2302635 := bstep (se 1 (by rfl) ⟨1726976, by rfl⟩ : syracuseStep 2302635 = 3453953) B3453953
theorem B5828557 : Blo 2301435 5828557 := bbase (se 3 (by rfl) ⟨1092854, by rfl⟩ : syracuseStep 5828557 = 2185709) (by norm_num)
theorem B7771409 : Blo 2301435 7771409 := bstep (se 2 (by rfl) ⟨2914278, by rfl⟩ : syracuseStep 7771409 = 5828557) B5828557
theorem B5180939 : Blo 2301435 5180939 := bstep (se 1 (by rfl) ⟨3885704, by rfl⟩ : syracuseStep 5180939 = 7771409) B7771409
theorem B3453959 : Blo 2301435 3453959 := bstep (se 1 (by rfl) ⟨2590469, by rfl⟩ : syracuseStep 3453959 = 5180939) B5180939
theorem B2302639 : Blo 2301435 2302639 := bstep (se 1 (by rfl) ⟨1726979, by rfl⟩ : syracuseStep 2302639 = 3453959) B3453959
theorem B3453965 : Blo 2301435 3453965 := bbase (se 3 (by rfl) ⟨647618, by rfl⟩ : syracuseStep 3453965 = 1295237) (by norm_num)
theorem B2302643 : Blo 2301435 2302643 := bstep (se 1 (by rfl) ⟨1726982, by rfl⟩ : syracuseStep 2302643 = 3453965) B3453965
theorem B5180957 : Blo 2301435 5180957 := bbase (se 3 (by rfl) ⟨971429, by rfl⟩ : syracuseStep 5180957 = 1942859) (by norm_num)
theorem B3453971 : Blo 2301435 3453971 := bstep (se 1 (by rfl) ⟨2590478, by rfl⟩ : syracuseStep 3453971 = 5180957) B5180957
theorem B2302647 : Blo 2301435 2302647 := bstep (se 1 (by rfl) ⟨1726985, by rfl⟩ : syracuseStep 2302647 = 3453971) B3453971
theorem B3885725 : Blo 2301435 3885725 := bbase (se 3 (by rfl) ⟨728573, by rfl⟩ : syracuseStep 3885725 = 1457147) (by norm_num)
theorem B2590483 : Blo 2301435 2590483 := bstep (se 1 (by rfl) ⟨1942862, by rfl⟩ : syracuseStep 2590483 = 3885725) B3885725
theorem B3453977 : Blo 2301435 3453977 := bstep (se 2 (by rfl) ⟨1295241, by rfl⟩ : syracuseStep 3453977 = 2590483) B2590483
theorem B2302651 : Blo 2301435 2302651 := bstep (se 1 (by rfl) ⟨1726988, by rfl⟩ : syracuseStep 2302651 = 3453977) B3453977
theorem B28390997 : Blo 2301435 28390997 := bbase (se 8 (by rfl) ⟨166353, by rfl⟩ : syracuseStep 28390997 = 332707) (by norm_num)
theorem B75709325 : Blo 2301435 75709325 := bstep (se 3 (by rfl) ⟨14195498, by rfl⟩ : syracuseStep 75709325 = 28390997) B28390997
theorem B50472883 : Blo 2301435 50472883 := bstep (se 1 (by rfl) ⟨37854662, by rfl⟩ : syracuseStep 50472883 = 75709325) B75709325
theorem B67297177 : Blo 2301435 67297177 := bstep (se 2 (by rfl) ⟨25236441, by rfl⟩ : syracuseStep 67297177 = 50472883) B50472883
theorem B89729569 : Blo 2301435 89729569 := bstep (se 2 (by rfl) ⟨33648588, by rfl⟩ : syracuseStep 89729569 = 67297177) B67297177
theorem B119639425 : Blo 2301435 119639425 := bstep (se 2 (by rfl) ⟨44864784, by rfl⟩ : syracuseStep 119639425 = 89729569) B89729569
theorem B159519233 : Blo 2301435 159519233 := bstep (se 2 (by rfl) ⟨59819712, by rfl⟩ : syracuseStep 159519233 = 119639425) B119639425
theorem B425384621 : Blo 2301435 425384621 := bstep (se 3 (by rfl) ⟨79759616, by rfl⟩ : syracuseStep 425384621 = 159519233) B159519233
theorem B283589747 : Blo 2301435 283589747 := bstep (se 1 (by rfl) ⟨212692310, by rfl⟩ : syracuseStep 283589747 = 425384621) B425384621
theorem B189059831 : Blo 2301435 189059831 := bstep (se 1 (by rfl) ⟨141794873, by rfl⟩ : syracuseStep 189059831 = 283589747) B283589747
theorem B126039887 : Blo 2301435 126039887 := bstep (se 1 (by rfl) ⟨94529915, by rfl⟩ : syracuseStep 126039887 = 189059831) B189059831
theorem B84026591 : Blo 2301435 84026591 := bstep (se 1 (by rfl) ⟨63019943, by rfl⟩ : syracuseStep 84026591 = 126039887) B126039887
theorem B56017727 : Blo 2301435 56017727 := bstep (se 1 (by rfl) ⟨42013295, by rfl⟩ : syracuseStep 56017727 = 84026591) B84026591
theorem B37345151 : Blo 2301435 37345151 := bstep (se 1 (by rfl) ⟨28008863, by rfl⟩ : syracuseStep 37345151 = 56017727) B56017727
theorem B24896767 : Blo 2301435 24896767 := bstep (se 1 (by rfl) ⟨18672575, by rfl⟩ : syracuseStep 24896767 = 37345151) B37345151
theorem B33195689 : Blo 2301435 33195689 := bstep (se 2 (by rfl) ⟨12448383, by rfl⟩ : syracuseStep 33195689 = 24896767) B24896767
theorem B22130459 : Blo 2301435 22130459 := bstep (se 1 (by rfl) ⟨16597844, by rfl⟩ : syracuseStep 22130459 = 33195689) B33195689
theorem B14753639 : Blo 2301435 14753639 := bstep (se 1 (by rfl) ⟨11065229, by rfl⟩ : syracuseStep 14753639 = 22130459) B22130459
theorem B9835759 : Blo 2301435 9835759 := bstep (se 1 (by rfl) ⟨7376819, by rfl⟩ : syracuseStep 9835759 = 14753639) B14753639
theorem B13114345 : Blo 2301435 13114345 := bstep (se 2 (by rfl) ⟨4917879, by rfl⟩ : syracuseStep 13114345 = 9835759) B9835759
theorem B17485793 : Blo 2301435 17485793 := bstep (se 2 (by rfl) ⟨6557172, by rfl⟩ : syracuseStep 17485793 = 13114345) B13114345
theorem B11657195 : Blo 2301435 11657195 := bstep (se 1 (by rfl) ⟨8742896, by rfl⟩ : syracuseStep 11657195 = 17485793) B17485793
theorem B7771463 : Blo 2301435 7771463 := bstep (se 1 (by rfl) ⟨5828597, by rfl⟩ : syracuseStep 7771463 = 11657195) B11657195
theorem B5180975 : Blo 2301435 5180975 := bstep (se 1 (by rfl) ⟨3885731, by rfl⟩ : syracuseStep 5180975 = 7771463) B7771463
theorem B3453983 : Blo 2301435 3453983 := bstep (se 1 (by rfl) ⟨2590487, by rfl⟩ : syracuseStep 3453983 = 5180975) B5180975
theorem B2302655 : Blo 2301435 2302655 := bstep (se 1 (by rfl) ⟨1726991, by rfl⟩ : syracuseStep 2302655 = 3453983) B3453983
theorem B3453989 : Blo 2301435 3453989 := bbase (se 4 (by rfl) ⟨323811, by rfl⟩ : syracuseStep 3453989 = 647623) (by norm_num)
theorem B2302659 : Blo 2301435 2302659 := bstep (se 1 (by rfl) ⟨1726994, by rfl⟩ : syracuseStep 2302659 = 3453989) B3453989
theorem B2914309 : Blo 2301435 2914309 := bbase (se 4 (by rfl) ⟨273216, by rfl⟩ : syracuseStep 2914309 = 546433) (by norm_num)
theorem B3885745 : Blo 2301435 3885745 := bstep (se 2 (by rfl) ⟨1457154, by rfl⟩ : syracuseStep 3885745 = 2914309) B2914309
theorem B5180993 : Blo 2301435 5180993 := bstep (se 2 (by rfl) ⟨1942872, by rfl⟩ : syracuseStep 5180993 = 3885745) B3885745
theorem B3453995 : Blo 2301435 3453995 := bstep (se 1 (by rfl) ⟨2590496, by rfl⟩ : syracuseStep 3453995 = 5180993) B5180993
theorem B2302663 : Blo 2301435 2302663 := bstep (se 1 (by rfl) ⟨1726997, by rfl⟩ : syracuseStep 2302663 = 3453995) B3453995
theorem B2590501 : Blo 2301435 2590501 := bbase (se 4 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 2590501 = 485719) (by norm_num)
theorem B3454001 : Blo 2301435 3454001 := bstep (se 2 (by rfl) ⟨1295250, by rfl⟩ : syracuseStep 3454001 = 2590501) B2590501
theorem B2302667 : Blo 2301435 2302667 := bstep (se 1 (by rfl) ⟨1727000, by rfl⟩ : syracuseStep 2302667 = 3454001) B3454001
theorem B9835829 : Blo 2301435 9835829 := bbase (se 5 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 9835829 = 922109) (by norm_num)
theorem B6557219 : Blo 2301435 6557219 := bstep (se 1 (by rfl) ⟨4917914, by rfl⟩ : syracuseStep 6557219 = 9835829) B9835829
theorem B4371479 : Blo 2301435 4371479 := bstep (se 1 (by rfl) ⟨3278609, by rfl⟩ : syracuseStep 4371479 = 6557219) B6557219
theorem B2914319 : Blo 2301435 2914319 := bstep (se 1 (by rfl) ⟨2185739, by rfl⟩ : syracuseStep 2914319 = 4371479) B4371479
theorem B7771517 : Blo 2301435 7771517 := bstep (se 3 (by rfl) ⟨1457159, by rfl⟩ : syracuseStep 7771517 = 2914319) B2914319
theorem B5181011 : Blo 2301435 5181011 := bstep (se 1 (by rfl) ⟨3885758, by rfl⟩ : syracuseStep 5181011 = 7771517) B7771517
theorem B3454007 : Blo 2301435 3454007 := bstep (se 1 (by rfl) ⟨2590505, by rfl⟩ : syracuseStep 3454007 = 5181011) B5181011
theorem B2302671 : Blo 2301435 2302671 := bstep (se 1 (by rfl) ⟨1727003, by rfl⟩ : syracuseStep 2302671 = 3454007) B3454007
theorem B3454013 : Blo 2301435 3454013 := bbase (se 3 (by rfl) ⟨647627, by rfl⟩ : syracuseStep 3454013 = 1295255) (by norm_num)
theorem B2302675 : Blo 2301435 2302675 := bstep (se 1 (by rfl) ⟨1727006, by rfl⟩ : syracuseStep 2302675 = 3454013) B3454013
theorem B5181029 : Blo 2301435 5181029 := bbase (se 4 (by rfl) ⟨485721, by rfl⟩ : syracuseStep 5181029 = 971443) (by norm_num)
theorem B3454019 : Blo 2301435 3454019 := bstep (se 1 (by rfl) ⟨2590514, by rfl⟩ : syracuseStep 3454019 = 5181029) B5181029
theorem B2302679 : Blo 2301435 2302679 := bstep (se 1 (by rfl) ⟨1727009, by rfl⟩ : syracuseStep 2302679 = 3454019) B3454019
theorem B5828669 : Blo 2301435 5828669 := bbase (se 3 (by rfl) ⟨1092875, by rfl⟩ : syracuseStep 5828669 = 2185751) (by norm_num)
theorem B3885779 : Blo 2301435 3885779 := bstep (se 1 (by rfl) ⟨2914334, by rfl⟩ : syracuseStep 3885779 = 5828669) B5828669
theorem B2590519 : Blo 2301435 2590519 := bstep (se 1 (by rfl) ⟨1942889, by rfl⟩ : syracuseStep 2590519 = 3885779) B3885779
theorem B3454025 : Blo 2301435 3454025 := bstep (se 2 (by rfl) ⟨1295259, by rfl⟩ : syracuseStep 3454025 = 2590519) B2590519
theorem B2302683 : Blo 2301435 2302683 := bstep (se 1 (by rfl) ⟨1727012, by rfl⟩ : syracuseStep 2302683 = 3454025) B3454025
theorem B4371509 : Blo 2301435 4371509 := bbase (se 5 (by rfl) ⟨204914, by rfl⟩ : syracuseStep 4371509 = 409829) (by norm_num)
theorem B11657357 : Blo 2301435 11657357 := bstep (se 3 (by rfl) ⟨2185754, by rfl⟩ : syracuseStep 11657357 = 4371509) B4371509
theorem B7771571 : Blo 2301435 7771571 := bstep (se 1 (by rfl) ⟨5828678, by rfl⟩ : syracuseStep 7771571 = 11657357) B11657357
theorem B5181047 : Blo 2301435 5181047 := bstep (se 1 (by rfl) ⟨3885785, by rfl⟩ : syracuseStep 5181047 = 7771571) B7771571
theorem B3454031 : Blo 2301435 3454031 := bstep (se 1 (by rfl) ⟨2590523, by rfl⟩ : syracuseStep 3454031 = 5181047) B5181047
theorem B2302687 : Blo 2301435 2302687 := bstep (se 1 (by rfl) ⟨1727015, by rfl⟩ : syracuseStep 2302687 = 3454031) B3454031
theorem B3454037 : Blo 2301435 3454037 := bbase (se 8 (by rfl) ⟨20238, by rfl⟩ : syracuseStep 3454037 = 40477) (by norm_num)
theorem B2302691 : Blo 2301435 2302691 := bstep (se 1 (by rfl) ⟨1727018, by rfl⟩ : syracuseStep 2302691 = 3454037) B3454037
theorem B2625877 : Blo 2301435 2625877 := bbase (se 10 (by rfl) ⟨3846, by rfl⟩ : syracuseStep 2625877 = 7693) (by norm_num)
theorem B14004677 : Blo 2301435 14004677 := bstep (se 4 (by rfl) ⟨1312938, by rfl⟩ : syracuseStep 14004677 = 2625877) B2625877
theorem B37345805 : Blo 2301435 37345805 := bstep (se 3 (by rfl) ⟨7002338, by rfl⟩ : syracuseStep 37345805 = 14004677) B14004677
theorem B24897203 : Blo 2301435 24897203 := bstep (se 1 (by rfl) ⟨18672902, by rfl⟩ : syracuseStep 24897203 = 37345805) B37345805
theorem B16598135 : Blo 2301435 16598135 := bstep (se 1 (by rfl) ⟨12448601, by rfl⟩ : syracuseStep 16598135 = 24897203) B24897203
theorem B11065423 : Blo 2301435 11065423 := bstep (se 1 (by rfl) ⟨8299067, by rfl⟩ : syracuseStep 11065423 = 16598135) B16598135
theorem B14753897 : Blo 2301435 14753897 := bstep (se 2 (by rfl) ⟨5532711, by rfl⟩ : syracuseStep 14753897 = 11065423) B11065423
theorem B9835931 : Blo 2301435 9835931 := bstep (se 1 (by rfl) ⟨7376948, by rfl⟩ : syracuseStep 9835931 = 14753897) B14753897
theorem B6557287 : Blo 2301435 6557287 := bstep (se 1 (by rfl) ⟨4917965, by rfl⟩ : syracuseStep 6557287 = 9835931) B9835931
theorem B8743049 : Blo 2301435 8743049 := bstep (se 2 (by rfl) ⟨3278643, by rfl⟩ : syracuseStep 8743049 = 6557287) B6557287
theorem B5828699 : Blo 2301435 5828699 := bstep (se 1 (by rfl) ⟨4371524, by rfl⟩ : syracuseStep 5828699 = 8743049) B8743049
theorem B3885799 : Blo 2301435 3885799 := bstep (se 1 (by rfl) ⟨2914349, by rfl⟩ : syracuseStep 3885799 = 5828699) B5828699
theorem B5181065 : Blo 2301435 5181065 := bstep (se 2 (by rfl) ⟨1942899, by rfl⟩ : syracuseStep 5181065 = 3885799) B3885799
theorem B3454043 : Blo 2301435 3454043 := bstep (se 1 (by rfl) ⟨2590532, by rfl⟩ : syracuseStep 3454043 = 5181065) B5181065
theorem B2302695 : Blo 2301435 2302695 := bstep (se 1 (by rfl) ⟨1727021, by rfl⟩ : syracuseStep 2302695 = 3454043) B3454043
theorem B2590537 : Blo 2301435 2590537 := bbase (se 2 (by rfl) ⟨971451, by rfl⟩ : syracuseStep 2590537 = 1942903) (by norm_num)
theorem B3454049 : Blo 2301435 3454049 := bstep (se 2 (by rfl) ⟨1295268, by rfl⟩ : syracuseStep 3454049 = 2590537) B2590537
theorem B2302699 : Blo 2301435 2302699 := bstep (se 1 (by rfl) ⟨1727024, by rfl⟩ : syracuseStep 2302699 = 3454049) B3454049
theorem B7985141 : Blo 2301435 7985141 := bbase (se 5 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 7985141 = 748607) (by norm_num)
theorem B5323427 : Blo 2301435 5323427 := bstep (se 1 (by rfl) ⟨3992570, by rfl⟩ : syracuseStep 5323427 = 7985141) B7985141
theorem B3548951 : Blo 2301435 3548951 := bstep (se 1 (by rfl) ⟨2661713, by rfl⟩ : syracuseStep 3548951 = 5323427) B5323427
theorem B2365967 : Blo 2301435 2365967 := bstep (se 1 (by rfl) ⟨1774475, by rfl⟩ : syracuseStep 2365967 = 3548951) B3548951
theorem B6309245 : Blo 2301435 6309245 := bstep (se 3 (by rfl) ⟨1182983, by rfl⟩ : syracuseStep 6309245 = 2365967) B2365967
theorem B4206163 : Blo 2301435 4206163 := bstep (se 1 (by rfl) ⟨3154622, by rfl⟩ : syracuseStep 4206163 = 6309245) B6309245
theorem B5608217 : Blo 2301435 5608217 := bstep (se 2 (by rfl) ⟨2103081, by rfl⟩ : syracuseStep 5608217 = 4206163) B4206163
theorem B3738811 : Blo 2301435 3738811 := bstep (se 1 (by rfl) ⟨2804108, by rfl⟩ : syracuseStep 3738811 = 5608217) B5608217
theorem B4985081 : Blo 2301435 4985081 := bstep (se 2 (by rfl) ⟨1869405, by rfl⟩ : syracuseStep 4985081 = 3738811) B3738811
theorem B3323387 : Blo 2301435 3323387 := bstep (se 1 (by rfl) ⟨2492540, by rfl⟩ : syracuseStep 3323387 = 4985081) B4985081
theorem B8862365 : Blo 2301435 8862365 := bstep (se 3 (by rfl) ⟨1661693, by rfl⟩ : syracuseStep 8862365 = 3323387) B3323387
theorem B23632973 : Blo 2301435 23632973 := bstep (se 3 (by rfl) ⟨4431182, by rfl⟩ : syracuseStep 23632973 = 8862365) B8862365
theorem B15755315 : Blo 2301435 15755315 := bstep (se 1 (by rfl) ⟨11816486, by rfl⟩ : syracuseStep 15755315 = 23632973) B23632973
theorem B42014173 : Blo 2301435 42014173 := bstep (se 3 (by rfl) ⟨7877657, by rfl⟩ : syracuseStep 42014173 = 15755315) B15755315
theorem B56018897 : Blo 2301435 56018897 := bstep (se 2 (by rfl) ⟨21007086, by rfl⟩ : syracuseStep 56018897 = 42014173) B42014173
theorem B37345931 : Blo 2301435 37345931 := bstep (se 1 (by rfl) ⟨28009448, by rfl⟩ : syracuseStep 37345931 = 56018897) B56018897
theorem B24897287 : Blo 2301435 24897287 := bstep (se 1 (by rfl) ⟨18672965, by rfl⟩ : syracuseStep 24897287 = 37345931) B37345931
theorem B16598191 : Blo 2301435 16598191 := bstep (se 1 (by rfl) ⟨12448643, by rfl⟩ : syracuseStep 16598191 = 24897287) B24897287
theorem B22130921 : Blo 2301435 22130921 := bstep (se 2 (by rfl) ⟨8299095, by rfl⟩ : syracuseStep 22130921 = 16598191) B16598191
theorem B14753947 : Blo 2301435 14753947 := bstep (se 1 (by rfl) ⟨11065460, by rfl⟩ : syracuseStep 14753947 = 22130921) B22130921
theorem B19671929 : Blo 2301435 19671929 := bstep (se 2 (by rfl) ⟨7376973, by rfl⟩ : syracuseStep 19671929 = 14753947) B14753947
theorem B13114619 : Blo 2301435 13114619 := bstep (se 1 (by rfl) ⟨9835964, by rfl⟩ : syracuseStep 13114619 = 19671929) B19671929
theorem B8743079 : Blo 2301435 8743079 := bstep (se 1 (by rfl) ⟨6557309, by rfl⟩ : syracuseStep 8743079 = 13114619) B13114619
theorem B5828719 : Blo 2301435 5828719 := bstep (se 1 (by rfl) ⟨4371539, by rfl⟩ : syracuseStep 5828719 = 8743079) B8743079
theorem B7771625 : Blo 2301435 7771625 := bstep (se 2 (by rfl) ⟨2914359, by rfl⟩ : syracuseStep 7771625 = 5828719) B5828719
theorem B5181083 : Blo 2301435 5181083 := bstep (se 1 (by rfl) ⟨3885812, by rfl⟩ : syracuseStep 5181083 = 7771625) B7771625
theorem B3454055 : Blo 2301435 3454055 := bstep (se 1 (by rfl) ⟨2590541, by rfl⟩ : syracuseStep 3454055 = 5181083) B5181083
theorem B2302703 : Blo 2301435 2302703 := bstep (se 1 (by rfl) ⟨1727027, by rfl⟩ : syracuseStep 2302703 = 3454055) B3454055
theorem B3454061 : Blo 2301435 3454061 := bbase (se 3 (by rfl) ⟨647636, by rfl⟩ : syracuseStep 3454061 = 1295273) (by norm_num)
theorem B2302707 : Blo 2301435 2302707 := bstep (se 1 (by rfl) ⟨1727030, by rfl⟩ : syracuseStep 2302707 = 3454061) B3454061
theorem B5181101 : Blo 2301435 5181101 := bbase (se 3 (by rfl) ⟨971456, by rfl⟩ : syracuseStep 5181101 = 1942913) (by norm_num)
theorem B3454067 : Blo 2301435 3454067 := bstep (se 1 (by rfl) ⟨2590550, by rfl⟩ : syracuseStep 3454067 = 5181101) B5181101
theorem B2302711 : Blo 2301435 2302711 := bstep (se 1 (by rfl) ⟨1727033, by rfl⟩ : syracuseStep 2302711 = 3454067) B3454067
theorem B6224357 : Blo 2301435 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B4149571 : Blo 2301435 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B5532761 : Blo 2301435 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B3688507 : Blo 2301435 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B4918009 : Blo 2301435 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B6557345 : Blo 2301435 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B4371563 : Blo 2301435 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B2914375 : Blo 2301435 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B3885833 : Blo 2301435 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B2590555 : Blo 2301435 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B3454073 : Blo 2301435 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B2302715 : Blo 2301435 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B14004821 : Blo 2301435 14004821 := bbase (se 8 (by rfl) ⟨82059, by rfl⟩ : syracuseStep 14004821 = 164119) (by norm_num)
theorem B9336547 : Blo 2301435 9336547 := bstep (se 1 (by rfl) ⟨7002410, by rfl⟩ : syracuseStep 9336547 = 14004821) B14004821
theorem B12448729 : Blo 2301435 12448729 := bstep (se 2 (by rfl) ⟨4668273, by rfl⟩ : syracuseStep 12448729 = 9336547) B9336547
theorem B16598305 : Blo 2301435 16598305 := bstep (se 2 (by rfl) ⟨6224364, by rfl⟩ : syracuseStep 16598305 = 12448729) B12448729
theorem B22131073 : Blo 2301435 22131073 := bstep (se 2 (by rfl) ⟨8299152, by rfl⟩ : syracuseStep 22131073 = 16598305) B16598305
theorem B29508097 : Blo 2301435 29508097 := bstep (se 2 (by rfl) ⟨11065536, by rfl⟩ : syracuseStep 29508097 = 22131073) B22131073
theorem B39344129 : Blo 2301435 39344129 := bstep (se 2 (by rfl) ⟨14754048, by rfl⟩ : syracuseStep 39344129 = 29508097) B29508097
theorem B26229419 : Blo 2301435 26229419 := bstep (se 1 (by rfl) ⟨19672064, by rfl⟩ : syracuseStep 26229419 = 39344129) B39344129
theorem B17486279 : Blo 2301435 17486279 := bstep (se 1 (by rfl) ⟨13114709, by rfl⟩ : syracuseStep 17486279 = 26229419) B26229419
theorem B11657519 : Blo 2301435 11657519 := bstep (se 1 (by rfl) ⟨8743139, by rfl⟩ : syracuseStep 11657519 = 17486279) B17486279
theorem B7771679 : Blo 2301435 7771679 := bstep (se 1 (by rfl) ⟨5828759, by rfl⟩ : syracuseStep 7771679 = 11657519) B11657519
theorem B5181119 : Blo 2301435 5181119 := bstep (se 1 (by rfl) ⟨3885839, by rfl⟩ : syracuseStep 5181119 = 7771679) B7771679
theorem B3454079 : Blo 2301435 3454079 := bstep (se 1 (by rfl) ⟨2590559, by rfl⟩ : syracuseStep 3454079 = 5181119) B5181119
theorem B2302719 : Blo 2301435 2302719 := bstep (se 1 (by rfl) ⟨1727039, by rfl⟩ : syracuseStep 2302719 = 3454079) B3454079
theorem B3454085 : Blo 2301435 3454085 := bbase (se 4 (by rfl) ⟨323820, by rfl⟩ : syracuseStep 3454085 = 647641) (by norm_num)
theorem B2302723 : Blo 2301435 2302723 := bstep (se 1 (by rfl) ⟨1727042, by rfl⟩ : syracuseStep 2302723 = 3454085) B3454085
theorem B3885853 : Blo 2301435 3885853 := bbase (se 3 (by rfl) ⟨728597, by rfl⟩ : syracuseStep 3885853 = 1457195) (by norm_num)
theorem B5181137 : Blo 2301435 5181137 := bstep (se 2 (by rfl) ⟨1942926, by rfl⟩ : syracuseStep 5181137 = 3885853) B3885853
theorem B3454091 : Blo 2301435 3454091 := bstep (se 1 (by rfl) ⟨2590568, by rfl⟩ : syracuseStep 3454091 = 5181137) B5181137
theorem B2302727 : Blo 2301435 2302727 := bstep (se 1 (by rfl) ⟨1727045, by rfl⟩ : syracuseStep 2302727 = 3454091) B3454091
theorem B2590573 : Blo 2301435 2590573 := bbase (se 3 (by rfl) ⟨485732, by rfl⟩ : syracuseStep 2590573 = 971465) (by norm_num)
theorem B3454097 : Blo 2301435 3454097 := bstep (se 2 (by rfl) ⟨1295286, by rfl⟩ : syracuseStep 3454097 = 2590573) B2590573
theorem B2302731 : Blo 2301435 2302731 := bstep (se 1 (by rfl) ⟨1727048, by rfl⟩ : syracuseStep 2302731 = 3454097) B3454097
theorem B7771733 : Blo 2301435 7771733 := bbase (se 8 (by rfl) ⟨45537, by rfl⟩ : syracuseStep 7771733 = 91075) (by norm_num)
theorem B5181155 : Blo 2301435 5181155 := bstep (se 1 (by rfl) ⟨3885866, by rfl⟩ : syracuseStep 5181155 = 7771733) B7771733
theorem B3454103 : Blo 2301435 3454103 := bstep (se 1 (by rfl) ⟨2590577, by rfl⟩ : syracuseStep 3454103 = 5181155) B5181155
theorem B2302735 : Blo 2301435 2302735 := bstep (se 1 (by rfl) ⟨1727051, by rfl⟩ : syracuseStep 2302735 = 3454103) B3454103
theorem B3454109 : Blo 2301435 3454109 := bbase (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) (by norm_num)
theorem B2302739 : Blo 2301435 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B5181173 : Blo 2301435 5181173 := bbase (se 5 (by rfl) ⟨242867, by rfl⟩ : syracuseStep 5181173 = 485735) (by norm_num)
theorem B3454115 : Blo 2301435 3454115 := bstep (se 1 (by rfl) ⟨2590586, by rfl⟩ : syracuseStep 3454115 = 5181173) B5181173
theorem B2302743 : Blo 2301435 2302743 := bstep (se 1 (by rfl) ⟨1727057, by rfl⟩ : syracuseStep 2302743 = 3454115) B3454115
theorem B4431269 : Blo 2301435 4431269 := bbase (se 4 (by rfl) ⟨415431, by rfl⟩ : syracuseStep 4431269 = 830863) (by norm_num)
theorem B2954179 : Blo 2301435 2954179 := bstep (se 1 (by rfl) ⟨2215634, by rfl⟩ : syracuseStep 2954179 = 4431269) B4431269
theorem B3938905 : Blo 2301435 3938905 := bstep (se 2 (by rfl) ⟨1477089, by rfl⟩ : syracuseStep 3938905 = 2954179) B2954179
theorem B5251873 : Blo 2301435 5251873 := bstep (se 2 (by rfl) ⟨1969452, by rfl⟩ : syracuseStep 5251873 = 3938905) B3938905
theorem B7002497 : Blo 2301435 7002497 := bstep (se 2 (by rfl) ⟨2625936, by rfl⟩ : syracuseStep 7002497 = 5251873) B5251873
theorem B18673325 : Blo 2301435 18673325 := bstep (se 3 (by rfl) ⟨3501248, by rfl⟩ : syracuseStep 18673325 = 7002497) B7002497
theorem B12448883 : Blo 2301435 12448883 := bstep (se 1 (by rfl) ⟨9336662, by rfl⟩ : syracuseStep 12448883 = 18673325) B18673325
theorem B8299255 : Blo 2301435 8299255 := bstep (se 1 (by rfl) ⟨6224441, by rfl⟩ : syracuseStep 8299255 = 12448883) B12448883
theorem B11065673 : Blo 2301435 11065673 := bstep (se 2 (by rfl) ⟨4149627, by rfl⟩ : syracuseStep 11065673 = 8299255) B8299255
theorem B29508461 : Blo 2301435 29508461 := bstep (se 3 (by rfl) ⟨5532836, by rfl⟩ : syracuseStep 29508461 = 11065673) B11065673
theorem B19672307 : Blo 2301435 19672307 := bstep (se 1 (by rfl) ⟨14754230, by rfl⟩ : syracuseStep 19672307 = 29508461) B29508461
theorem B13114871 : Blo 2301435 13114871 := bstep (se 1 (by rfl) ⟨9836153, by rfl⟩ : syracuseStep 13114871 = 19672307) B19672307
theorem B8743247 : Blo 2301435 8743247 := bstep (se 1 (by rfl) ⟨6557435, by rfl⟩ : syracuseStep 8743247 = 13114871) B13114871
theorem B5828831 : Blo 2301435 5828831 := bstep (se 1 (by rfl) ⟨4371623, by rfl⟩ : syracuseStep 5828831 = 8743247) B8743247
theorem B3885887 : Blo 2301435 3885887 := bstep (se 1 (by rfl) ⟨2914415, by rfl⟩ : syracuseStep 3885887 = 5828831) B5828831
theorem B2590591 : Blo 2301435 2590591 := bstep (se 1 (by rfl) ⟨1942943, by rfl⟩ : syracuseStep 2590591 = 3885887) B3885887
theorem B3454121 : Blo 2301435 3454121 := bstep (se 2 (by rfl) ⟨1295295, by rfl⟩ : syracuseStep 3454121 = 2590591) B2590591
theorem B2302747 : Blo 2301435 2302747 := bstep (se 1 (by rfl) ⟨1727060, by rfl⟩ : syracuseStep 2302747 = 3454121) B3454121
theorem B4918085 : Blo 2301435 4918085 := bbase (se 4 (by rfl) ⟨461070, by rfl⟩ : syracuseStep 4918085 = 922141) (by norm_num)
theorem B3278723 : Blo 2301435 3278723 := bstep (se 1 (by rfl) ⟨2459042, by rfl⟩ : syracuseStep 3278723 = 4918085) B4918085
theorem B8743261 : Blo 2301435 8743261 := bstep (se 3 (by rfl) ⟨1639361, by rfl⟩ : syracuseStep 8743261 = 3278723) B3278723
theorem B11657681 : Blo 2301435 11657681 := bstep (se 2 (by rfl) ⟨4371630, by rfl⟩ : syracuseStep 11657681 = 8743261) B8743261
theorem B7771787 : Blo 2301435 7771787 := bstep (se 1 (by rfl) ⟨5828840, by rfl⟩ : syracuseStep 7771787 = 11657681) B11657681
theorem B5181191 : Blo 2301435 5181191 := bstep (se 1 (by rfl) ⟨3885893, by rfl⟩ : syracuseStep 5181191 = 7771787) B7771787
theorem B3454127 : Blo 2301435 3454127 := bstep (se 1 (by rfl) ⟨2590595, by rfl⟩ : syracuseStep 3454127 = 5181191) B5181191
theorem B2302751 : Blo 2301435 2302751 := bstep (se 1 (by rfl) ⟨1727063, by rfl⟩ : syracuseStep 2302751 = 3454127) B3454127
theorem B3454133 : Blo 2301435 3454133 := bbase (se 5 (by rfl) ⟨161912, by rfl⟩ : syracuseStep 3454133 = 323825) (by norm_num)
theorem B2302755 : Blo 2301435 2302755 := bstep (se 1 (by rfl) ⟨1727066, by rfl⟩ : syracuseStep 2302755 = 3454133) B3454133
theorem B5828861 : Blo 2301435 5828861 := bbase (se 3 (by rfl) ⟨1092911, by rfl⟩ : syracuseStep 5828861 = 2185823) (by norm_num)
theorem B3885907 : Blo 2301435 3885907 := bstep (se 1 (by rfl) ⟨2914430, by rfl⟩ : syracuseStep 3885907 = 5828861) B5828861
theorem B5181209 : Blo 2301435 5181209 := bstep (se 2 (by rfl) ⟨1942953, by rfl⟩ : syracuseStep 5181209 = 3885907) B3885907
theorem B3454139 : Blo 2301435 3454139 := bstep (se 1 (by rfl) ⟨2590604, by rfl⟩ : syracuseStep 3454139 = 5181209) B5181209
theorem B2302759 : Blo 2301435 2302759 := bstep (se 1 (by rfl) ⟨1727069, by rfl⟩ : syracuseStep 2302759 = 3454139) B3454139
theorem B2590609 : Blo 2301435 2590609 := bbase (se 2 (by rfl) ⟨971478, by rfl⟩ : syracuseStep 2590609 = 1942957) (by norm_num)
theorem B3454145 : Blo 2301435 3454145 := bstep (se 2 (by rfl) ⟨1295304, by rfl⟩ : syracuseStep 3454145 = 2590609) B2590609
theorem B2302763 : Blo 2301435 2302763 := bstep (se 1 (by rfl) ⟨1727072, by rfl⟩ : syracuseStep 2302763 = 3454145) B3454145
theorem B4371661 : Blo 2301435 4371661 := bbase (se 3 (by rfl) ⟨819686, by rfl⟩ : syracuseStep 4371661 = 1639373) (by norm_num)
theorem B5828881 : Blo 2301435 5828881 := bstep (se 2 (by rfl) ⟨2185830, by rfl⟩ : syracuseStep 5828881 = 4371661) B4371661
theorem B7771841 : Blo 2301435 7771841 := bstep (se 2 (by rfl) ⟨2914440, by rfl⟩ : syracuseStep 7771841 = 5828881) B5828881
theorem B5181227 : Blo 2301435 5181227 := bstep (se 1 (by rfl) ⟨3885920, by rfl⟩ : syracuseStep 5181227 = 7771841) B7771841
theorem B3454151 : Blo 2301435 3454151 := bstep (se 1 (by rfl) ⟨2590613, by rfl⟩ : syracuseStep 3454151 = 5181227) B5181227
theorem B2302767 : Blo 2301435 2302767 := bstep (se 1 (by rfl) ⟨1727075, by rfl⟩ : syracuseStep 2302767 = 3454151) B3454151
theorem B3454157 : Blo 2301435 3454157 := bbase (se 3 (by rfl) ⟨647654, by rfl⟩ : syracuseStep 3454157 = 1295309) (by norm_num)
theorem B2302771 : Blo 2301435 2302771 := bstep (se 1 (by rfl) ⟨1727078, by rfl⟩ : syracuseStep 2302771 = 3454157) B3454157
theorem B5181245 : Blo 2301435 5181245 := bbase (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) (by norm_num)
theorem B3454163 : Blo 2301435 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B2302775 : Blo 2301435 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B3885941 : Blo 2301435 3885941 := bbase (se 5 (by rfl) ⟨182153, by rfl⟩ : syracuseStep 3885941 = 364307) (by norm_num)
theorem B2590627 : Blo 2301435 2590627 := bstep (se 1 (by rfl) ⟨1942970, by rfl⟩ : syracuseStep 2590627 = 3885941) B3885941
theorem B3454169 : Blo 2301435 3454169 := bstep (se 2 (by rfl) ⟨1295313, by rfl⟩ : syracuseStep 3454169 = 2590627) B2590627
theorem B2302779 : Blo 2301435 2302779 := bstep (se 1 (by rfl) ⟨1727084, by rfl⟩ : syracuseStep 2302779 = 3454169) B3454169
theorem B11369861 : Blo 2301435 11369861 := bbase (se 4 (by rfl) ⟨1065924, by rfl⟩ : syracuseStep 11369861 = 2131849) (by norm_num)
theorem B7579907 : Blo 2301435 7579907 := bstep (se 1 (by rfl) ⟨5684930, by rfl⟩ : syracuseStep 7579907 = 11369861) B11369861
theorem B5053271 : Blo 2301435 5053271 := bstep (se 1 (by rfl) ⟨3789953, by rfl⟩ : syracuseStep 5053271 = 7579907) B7579907
theorem B13475389 : Blo 2301435 13475389 := bstep (se 3 (by rfl) ⟨2526635, by rfl⟩ : syracuseStep 13475389 = 5053271) B5053271
theorem B17967185 : Blo 2301435 17967185 := bstep (se 2 (by rfl) ⟨6737694, by rfl⟩ : syracuseStep 17967185 = 13475389) B13475389
theorem B11978123 : Blo 2301435 11978123 := bstep (se 1 (by rfl) ⟨8983592, by rfl⟩ : syracuseStep 11978123 = 17967185) B17967185
theorem B127766645 : Blo 2301435 127766645 := bstep (se 5 (by rfl) ⟨5989061, by rfl⟩ : syracuseStep 127766645 = 11978123) B11978123
theorem B85177763 : Blo 2301435 85177763 := bstep (se 1 (by rfl) ⟨63883322, by rfl⟩ : syracuseStep 85177763 = 127766645) B127766645
theorem B56785175 : Blo 2301435 56785175 := bstep (se 1 (by rfl) ⟨42588881, by rfl⟩ : syracuseStep 56785175 = 85177763) B85177763
theorem B37856783 : Blo 2301435 37856783 := bstep (se 1 (by rfl) ⟨28392587, by rfl⟩ : syracuseStep 37856783 = 56785175) B56785175
theorem B25237855 : Blo 2301435 25237855 := bstep (se 1 (by rfl) ⟨18928391, by rfl⟩ : syracuseStep 25237855 = 37856783) B37856783
theorem B33650473 : Blo 2301435 33650473 := bstep (se 2 (by rfl) ⟨12618927, by rfl⟩ : syracuseStep 33650473 = 25237855) B25237855
theorem B44867297 : Blo 2301435 44867297 := bstep (se 2 (by rfl) ⟨16825236, by rfl⟩ : syracuseStep 44867297 = 33650473) B33650473
theorem B29911531 : Blo 2301435 29911531 := bstep (se 1 (by rfl) ⟨22433648, by rfl⟩ : syracuseStep 29911531 = 44867297) B44867297
theorem B39882041 : Blo 2301435 39882041 := bstep (se 2 (by rfl) ⟨14955765, by rfl⟩ : syracuseStep 39882041 = 29911531) B29911531
theorem B26588027 : Blo 2301435 26588027 := bstep (se 1 (by rfl) ⟨19941020, by rfl⟩ : syracuseStep 26588027 = 39882041) B39882041
theorem B17725351 : Blo 2301435 17725351 := bstep (se 1 (by rfl) ⟨13294013, by rfl⟩ : syracuseStep 17725351 = 26588027) B26588027
theorem B23633801 : Blo 2301435 23633801 := bstep (se 2 (by rfl) ⟨8862675, by rfl⟩ : syracuseStep 23633801 = 17725351) B17725351
theorem B15755867 : Blo 2301435 15755867 := bstep (se 1 (by rfl) ⟨11816900, by rfl⟩ : syracuseStep 15755867 = 23633801) B23633801
theorem B10503911 : Blo 2301435 10503911 := bstep (se 1 (by rfl) ⟨7877933, by rfl⟩ : syracuseStep 10503911 = 15755867) B15755867
theorem B7002607 : Blo 2301435 7002607 := bstep (se 1 (by rfl) ⟨5251955, by rfl⟩ : syracuseStep 7002607 = 10503911) B10503911
theorem B9336809 : Blo 2301435 9336809 := bstep (se 2 (by rfl) ⟨3501303, by rfl⟩ : syracuseStep 9336809 = 7002607) B7002607
theorem B6224539 : Blo 2301435 6224539 := bstep (se 1 (by rfl) ⟨4668404, by rfl⟩ : syracuseStep 6224539 = 9336809) B9336809
theorem B8299385 : Blo 2301435 8299385 := bstep (se 2 (by rfl) ⟨3112269, by rfl⟩ : syracuseStep 8299385 = 6224539) B6224539
theorem B5532923 : Blo 2301435 5532923 := bstep (se 1 (by rfl) ⟨4149692, by rfl⟩ : syracuseStep 5532923 = 8299385) B8299385
theorem B3688615 : Blo 2301435 3688615 := bstep (se 1 (by rfl) ⟨2766461, by rfl⟩ : syracuseStep 3688615 = 5532923) B5532923
theorem B4918153 : Blo 2301435 4918153 := bstep (se 2 (by rfl) ⟨1844307, by rfl⟩ : syracuseStep 4918153 = 3688615) B3688615
theorem B6557537 : Blo 2301435 6557537 := bstep (se 2 (by rfl) ⟨2459076, by rfl⟩ : syracuseStep 6557537 = 4918153) B4918153
theorem B17486765 : Blo 2301435 17486765 := bstep (se 3 (by rfl) ⟨3278768, by rfl⟩ : syracuseStep 17486765 = 6557537) B6557537
theorem B11657843 : Blo 2301435 11657843 := bstep (se 1 (by rfl) ⟨8743382, by rfl⟩ : syracuseStep 11657843 = 17486765) B17486765
theorem B7771895 : Blo 2301435 7771895 := bstep (se 1 (by rfl) ⟨5828921, by rfl⟩ : syracuseStep 7771895 = 11657843) B11657843
theorem B5181263 : Blo 2301435 5181263 := bstep (se 1 (by rfl) ⟨3885947, by rfl⟩ : syracuseStep 5181263 = 7771895) B7771895
theorem B3454175 : Blo 2301435 3454175 := bstep (se 1 (by rfl) ⟨2590631, by rfl⟩ : syracuseStep 3454175 = 5181263) B5181263
theorem B2302783 : Blo 2301435 2302783 := bstep (se 1 (by rfl) ⟨1727087, by rfl⟩ : syracuseStep 2302783 = 3454175) B3454175
theorem B3454181 : Blo 2301435 3454181 := bbase (se 4 (by rfl) ⟨323829, by rfl⟩ : syracuseStep 3454181 = 647659) (by norm_num)
theorem B2302787 : Blo 2301435 2302787 := bstep (se 1 (by rfl) ⟨1727090, by rfl⟩ : syracuseStep 2302787 = 3454181) B3454181
theorem B18673685 : Blo 2301435 18673685 := bbase (se 6 (by rfl) ⟨437664, by rfl⟩ : syracuseStep 18673685 = 875329) (by norm_num)
theorem B12449123 : Blo 2301435 12449123 := bstep (se 1 (by rfl) ⟨9336842, by rfl⟩ : syracuseStep 12449123 = 18673685) B18673685
theorem B8299415 : Blo 2301435 8299415 := bstep (se 1 (by rfl) ⟨6224561, by rfl⟩ : syracuseStep 8299415 = 12449123) B12449123
theorem B5532943 : Blo 2301435 5532943 := bstep (se 1 (by rfl) ⟨4149707, by rfl⟩ : syracuseStep 5532943 = 8299415) B8299415
theorem B7377257 : Blo 2301435 7377257 := bstep (se 2 (by rfl) ⟨2766471, by rfl⟩ : syracuseStep 7377257 = 5532943) B5532943
theorem B4918171 : Blo 2301435 4918171 := bstep (se 1 (by rfl) ⟨3688628, by rfl⟩ : syracuseStep 4918171 = 7377257) B7377257
theorem B6557561 : Blo 2301435 6557561 := bstep (se 2 (by rfl) ⟨2459085, by rfl⟩ : syracuseStep 6557561 = 4918171) B4918171
theorem B4371707 : Blo 2301435 4371707 := bstep (se 1 (by rfl) ⟨3278780, by rfl⟩ : syracuseStep 4371707 = 6557561) B6557561
theorem B2914471 : Blo 2301435 2914471 := bstep (se 1 (by rfl) ⟨2185853, by rfl⟩ : syracuseStep 2914471 = 4371707) B4371707
theorem B3885961 : Blo 2301435 3885961 := bstep (se 2 (by rfl) ⟨1457235, by rfl⟩ : syracuseStep 3885961 = 2914471) B2914471
theorem B5181281 : Blo 2301435 5181281 := bstep (se 2 (by rfl) ⟨1942980, by rfl⟩ : syracuseStep 5181281 = 3885961) B3885961
theorem B3454187 : Blo 2301435 3454187 := bstep (se 1 (by rfl) ⟨2590640, by rfl⟩ : syracuseStep 3454187 = 5181281) B5181281
theorem B2302791 : Blo 2301435 2302791 := bstep (se 1 (by rfl) ⟨1727093, by rfl⟩ : syracuseStep 2302791 = 3454187) B3454187
theorem B2590645 : Blo 2301435 2590645 := bbase (se 5 (by rfl) ⟨121436, by rfl⟩ : syracuseStep 2590645 = 242873) (by norm_num)
theorem B3454193 : Blo 2301435 3454193 := bstep (se 2 (by rfl) ⟨1295322, by rfl⟩ : syracuseStep 3454193 = 2590645) B2590645
theorem B2302795 : Blo 2301435 2302795 := bstep (se 1 (by rfl) ⟨1727096, by rfl⟩ : syracuseStep 2302795 = 3454193) B3454193
theorem B2914481 : Blo 2301435 2914481 := bbase (se 2 (by rfl) ⟨1092930, by rfl⟩ : syracuseStep 2914481 = 2185861) (by norm_num)
theorem B7771949 : Blo 2301435 7771949 := bstep (se 3 (by rfl) ⟨1457240, by rfl⟩ : syracuseStep 7771949 = 2914481) B2914481
theorem B5181299 : Blo 2301435 5181299 := bstep (se 1 (by rfl) ⟨3885974, by rfl⟩ : syracuseStep 5181299 = 7771949) B7771949
theorem B3454199 : Blo 2301435 3454199 := bstep (se 1 (by rfl) ⟨2590649, by rfl⟩ : syracuseStep 3454199 = 5181299) B5181299
theorem B2302799 : Blo 2301435 2302799 := bstep (se 1 (by rfl) ⟨1727099, by rfl⟩ : syracuseStep 2302799 = 3454199) B3454199
theorem B3454205 : Blo 2301435 3454205 := bbase (se 3 (by rfl) ⟨647663, by rfl⟩ : syracuseStep 3454205 = 1295327) (by norm_num)
theorem B2302803 : Blo 2301435 2302803 := bstep (se 1 (by rfl) ⟨1727102, by rfl⟩ : syracuseStep 2302803 = 3454205) B3454205
theorem B5181317 : Blo 2301435 5181317 := bbase (se 4 (by rfl) ⟨485748, by rfl⟩ : syracuseStep 5181317 = 971497) (by norm_num)
theorem B3454211 : Blo 2301435 3454211 := bstep (se 1 (by rfl) ⟨2590658, by rfl⟩ : syracuseStep 3454211 = 5181317) B5181317
theorem B2302807 : Blo 2301435 2302807 := bstep (se 1 (by rfl) ⟨1727105, by rfl⟩ : syracuseStep 2302807 = 3454211) B3454211
theorem B3688661 : Blo 2301435 3688661 := bbase (se 7 (by rfl) ⟨43226, by rfl⟩ : syracuseStep 3688661 = 86453) (by norm_num)
theorem B2459107 : Blo 2301435 2459107 := bstep (se 1 (by rfl) ⟨1844330, by rfl⟩ : syracuseStep 2459107 = 3688661) B3688661
theorem B3278809 : Blo 2301435 3278809 := bstep (se 2 (by rfl) ⟨1229553, by rfl⟩ : syracuseStep 3278809 = 2459107) B2459107
theorem B4371745 : Blo 2301435 4371745 := bstep (se 2 (by rfl) ⟨1639404, by rfl⟩ : syracuseStep 4371745 = 3278809) B3278809
theorem B5828993 : Blo 2301435 5828993 := bstep (se 2 (by rfl) ⟨2185872, by rfl⟩ : syracuseStep 5828993 = 4371745) B4371745
theorem B3885995 : Blo 2301435 3885995 := bstep (se 1 (by rfl) ⟨2914496, by rfl⟩ : syracuseStep 3885995 = 5828993) B5828993
theorem B2590663 : Blo 2301435 2590663 := bstep (se 1 (by rfl) ⟨1942997, by rfl⟩ : syracuseStep 2590663 = 3885995) B3885995
theorem B3454217 : Blo 2301435 3454217 := bstep (se 2 (by rfl) ⟨1295331, by rfl⟩ : syracuseStep 3454217 = 2590663) B2590663
theorem B2302811 : Blo 2301435 2302811 := bstep (se 1 (by rfl) ⟨1727108, by rfl⟩ : syracuseStep 2302811 = 3454217) B3454217
theorem B11658005 : Blo 2301435 11658005 := bbase (se 6 (by rfl) ⟨273234, by rfl⟩ : syracuseStep 11658005 = 546469) (by norm_num)
theorem B7772003 : Blo 2301435 7772003 := bstep (se 1 (by rfl) ⟨5829002, by rfl⟩ : syracuseStep 7772003 = 11658005) B11658005
theorem B5181335 : Blo 2301435 5181335 := bstep (se 1 (by rfl) ⟨3886001, by rfl⟩ : syracuseStep 5181335 = 7772003) B7772003
theorem B3454223 : Blo 2301435 3454223 := bstep (se 1 (by rfl) ⟨2590667, by rfl⟩ : syracuseStep 3454223 = 5181335) B5181335
theorem B2302815 : Blo 2301435 2302815 := bstep (se 1 (by rfl) ⟨1727111, by rfl⟩ : syracuseStep 2302815 = 3454223) B3454223
theorem B3454229 : Blo 2301435 3454229 := bbase (se 6 (by rfl) ⟨80958, by rfl⟩ : syracuseStep 3454229 = 161917) (by norm_num)
theorem B2302819 : Blo 2301435 2302819 := bstep (se 1 (by rfl) ⟨1727114, by rfl⟩ : syracuseStep 2302819 = 3454229) B3454229
theorem B23956661 : Blo 2301435 23956661 := bbase (se 5 (by rfl) ⟨1122968, by rfl⟩ : syracuseStep 23956661 = 2245937) (by norm_num)
theorem B15971107 : Blo 2301435 15971107 := bstep (se 1 (by rfl) ⟨11978330, by rfl⟩ : syracuseStep 15971107 = 23956661) B23956661
theorem B21294809 : Blo 2301435 21294809 := bstep (se 2 (by rfl) ⟨7985553, by rfl⟩ : syracuseStep 21294809 = 15971107) B15971107
theorem B14196539 : Blo 2301435 14196539 := bstep (se 1 (by rfl) ⟨10647404, by rfl⟩ : syracuseStep 14196539 = 21294809) B21294809
theorem B9464359 : Blo 2301435 9464359 := bstep (se 1 (by rfl) ⟨7098269, by rfl⟩ : syracuseStep 9464359 = 14196539) B14196539
theorem B12619145 : Blo 2301435 12619145 := bstep (se 2 (by rfl) ⟨4732179, by rfl⟩ : syracuseStep 12619145 = 9464359) B9464359
theorem B8412763 : Blo 2301435 8412763 := bstep (se 1 (by rfl) ⟨6309572, by rfl⟩ : syracuseStep 8412763 = 12619145) B12619145
theorem B11217017 : Blo 2301435 11217017 := bstep (se 2 (by rfl) ⟨4206381, by rfl⟩ : syracuseStep 11217017 = 8412763) B8412763
theorem B7478011 : Blo 2301435 7478011 := bstep (se 1 (by rfl) ⟨5608508, by rfl⟩ : syracuseStep 7478011 = 11217017) B11217017
theorem B39882725 : Blo 2301435 39882725 := bstep (se 4 (by rfl) ⟨3739005, by rfl⟩ : syracuseStep 39882725 = 7478011) B7478011
theorem B26588483 : Blo 2301435 26588483 := bstep (se 1 (by rfl) ⟨19941362, by rfl⟩ : syracuseStep 26588483 = 39882725) B39882725
theorem B17725655 : Blo 2301435 17725655 := bstep (se 1 (by rfl) ⟨13294241, by rfl⟩ : syracuseStep 17725655 = 26588483) B26588483
theorem B11817103 : Blo 2301435 11817103 := bstep (se 1 (by rfl) ⟨8862827, by rfl⟩ : syracuseStep 11817103 = 17725655) B17725655
theorem B15756137 : Blo 2301435 15756137 := bstep (se 2 (by rfl) ⟨5908551, by rfl⟩ : syracuseStep 15756137 = 11817103) B11817103
theorem B10504091 : Blo 2301435 10504091 := bstep (se 1 (by rfl) ⟨7878068, by rfl⟩ : syracuseStep 10504091 = 15756137) B15756137
theorem B28010909 : Blo 2301435 28010909 := bstep (se 3 (by rfl) ⟨5252045, by rfl⟩ : syracuseStep 28010909 = 10504091) B10504091
theorem B18673939 : Blo 2301435 18673939 := bstep (se 1 (by rfl) ⟨14005454, by rfl⟩ : syracuseStep 18673939 = 28010909) B28010909
theorem B24898585 : Blo 2301435 24898585 := bstep (se 2 (by rfl) ⟨9336969, by rfl⟩ : syracuseStep 24898585 = 18673939) B18673939
theorem B33198113 : Blo 2301435 33198113 := bstep (se 2 (by rfl) ⟨12449292, by rfl⟩ : syracuseStep 33198113 = 24898585) B24898585
theorem B22132075 : Blo 2301435 22132075 := bstep (se 1 (by rfl) ⟨16599056, by rfl⟩ : syracuseStep 22132075 = 33198113) B33198113
theorem B29509433 : Blo 2301435 29509433 := bstep (se 2 (by rfl) ⟨11066037, by rfl⟩ : syracuseStep 29509433 = 22132075) B22132075
theorem B19672955 : Blo 2301435 19672955 := bstep (se 1 (by rfl) ⟨14754716, by rfl⟩ : syracuseStep 19672955 = 29509433) B29509433
theorem B13115303 : Blo 2301435 13115303 := bstep (se 1 (by rfl) ⟨9836477, by rfl⟩ : syracuseStep 13115303 = 19672955) B19672955
theorem B8743535 : Blo 2301435 8743535 := bstep (se 1 (by rfl) ⟨6557651, by rfl⟩ : syracuseStep 8743535 = 13115303) B13115303
theorem B5829023 : Blo 2301435 5829023 := bstep (se 1 (by rfl) ⟨4371767, by rfl⟩ : syracuseStep 5829023 = 8743535) B8743535
theorem B3886015 : Blo 2301435 3886015 := bstep (se 1 (by rfl) ⟨2914511, by rfl⟩ : syracuseStep 3886015 = 5829023) B5829023
theorem B5181353 : Blo 2301435 5181353 := bstep (se 2 (by rfl) ⟨1943007, by rfl⟩ : syracuseStep 5181353 = 3886015) B3886015
theorem B3454235 : Blo 2301435 3454235 := bstep (se 1 (by rfl) ⟨2590676, by rfl⟩ : syracuseStep 3454235 = 5181353) B5181353
theorem B2302823 : Blo 2301435 2302823 := bstep (se 1 (by rfl) ⟨1727117, by rfl⟩ : syracuseStep 2302823 = 3454235) B3454235
theorem B2590681 : Blo 2301435 2590681 := bbase (se 2 (by rfl) ⟨971505, by rfl⟩ : syracuseStep 2590681 = 1943011) (by norm_num)
theorem B3454241 : Blo 2301435 3454241 := bstep (se 2 (by rfl) ⟨1295340, by rfl⟩ : syracuseStep 3454241 = 2590681) B2590681
theorem B2302827 : Blo 2301435 2302827 := bstep (se 1 (by rfl) ⟨1727120, by rfl⟩ : syracuseStep 2302827 = 3454241) B3454241
theorem B3278837 : Blo 2301435 3278837 := bbase (se 5 (by rfl) ⟨153695, by rfl⟩ : syracuseStep 3278837 = 307391) (by norm_num)
theorem B8743565 : Blo 2301435 8743565 := bstep (se 3 (by rfl) ⟨1639418, by rfl⟩ : syracuseStep 8743565 = 3278837) B3278837
theorem B5829043 : Blo 2301435 5829043 := bstep (se 1 (by rfl) ⟨4371782, by rfl⟩ : syracuseStep 5829043 = 8743565) B8743565
theorem B7772057 : Blo 2301435 7772057 := bstep (se 2 (by rfl) ⟨2914521, by rfl⟩ : syracuseStep 7772057 = 5829043) B5829043
theorem B5181371 : Blo 2301435 5181371 := bstep (se 1 (by rfl) ⟨3886028, by rfl⟩ : syracuseStep 5181371 = 7772057) B7772057
theorem B3454247 : Blo 2301435 3454247 := bstep (se 1 (by rfl) ⟨2590685, by rfl⟩ : syracuseStep 3454247 = 5181371) B5181371
theorem B2302831 : Blo 2301435 2302831 := bstep (se 1 (by rfl) ⟨1727123, by rfl⟩ : syracuseStep 2302831 = 3454247) B3454247
theorem B3454253 : Blo 2301435 3454253 := bbase (se 3 (by rfl) ⟨647672, by rfl⟩ : syracuseStep 3454253 = 1295345) (by norm_num)
theorem B2302835 : Blo 2301435 2302835 := bstep (se 1 (by rfl) ⟨1727126, by rfl⟩ : syracuseStep 2302835 = 3454253) B3454253
theorem B5181389 : Blo 2301435 5181389 := bbase (se 3 (by rfl) ⟨971510, by rfl⟩ : syracuseStep 5181389 = 1943021) (by norm_num)
theorem B3454259 : Blo 2301435 3454259 := bstep (se 1 (by rfl) ⟨2590694, by rfl⟩ : syracuseStep 3454259 = 5181389) B5181389
theorem B2302839 : Blo 2301435 2302839 := bstep (se 1 (by rfl) ⟨1727129, by rfl⟩ : syracuseStep 2302839 = 3454259) B3454259
theorem B2914537 : Blo 2301435 2914537 := bbase (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) (by norm_num)
theorem B3886049 : Blo 2301435 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B2590699 : Blo 2301435 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B3454265 : Blo 2301435 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B2302843 : Blo 2301435 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B14754869 : Blo 2301435 14754869 := bbase (se 5 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 14754869 = 1383269) (by norm_num)
theorem B9836579 : Blo 2301435 9836579 := bstep (se 1 (by rfl) ⟨7377434, by rfl⟩ : syracuseStep 9836579 = 14754869) B14754869
theorem B26230877 : Blo 2301435 26230877 := bstep (se 3 (by rfl) ⟨4918289, by rfl⟩ : syracuseStep 26230877 = 9836579) B9836579
theorem B17487251 : Blo 2301435 17487251 := bstep (se 1 (by rfl) ⟨13115438, by rfl⟩ : syracuseStep 17487251 = 26230877) B26230877
theorem B11658167 : Blo 2301435 11658167 := bstep (se 1 (by rfl) ⟨8743625, by rfl⟩ : syracuseStep 11658167 = 17487251) B17487251
theorem B7772111 : Blo 2301435 7772111 := bstep (se 1 (by rfl) ⟨5829083, by rfl⟩ : syracuseStep 7772111 = 11658167) B11658167
theorem B5181407 : Blo 2301435 5181407 := bstep (se 1 (by rfl) ⟨3886055, by rfl⟩ : syracuseStep 5181407 = 7772111) B7772111
theorem B3454271 : Blo 2301435 3454271 := bstep (se 1 (by rfl) ⟨2590703, by rfl⟩ : syracuseStep 3454271 = 5181407) B5181407
theorem B2302847 : Blo 2301435 2302847 := bstep (se 1 (by rfl) ⟨1727135, by rfl⟩ : syracuseStep 2302847 = 3454271) B3454271
theorem B3454277 : Blo 2301435 3454277 := bbase (se 4 (by rfl) ⟨323838, by rfl⟩ : syracuseStep 3454277 = 647677) (by norm_num)
theorem B2302851 : Blo 2301435 2302851 := bstep (se 1 (by rfl) ⟨1727138, by rfl⟩ : syracuseStep 2302851 = 3454277) B3454277
theorem B3886069 : Blo 2301435 3886069 := bbase (se 5 (by rfl) ⟨182159, by rfl⟩ : syracuseStep 3886069 = 364319) (by norm_num)
theorem B5181425 : Blo 2301435 5181425 := bstep (se 2 (by rfl) ⟨1943034, by rfl⟩ : syracuseStep 5181425 = 3886069) B3886069
theorem B3454283 : Blo 2301435 3454283 := bstep (se 1 (by rfl) ⟨2590712, by rfl⟩ : syracuseStep 3454283 = 5181425) B5181425
theorem B2302855 : Blo 2301435 2302855 := bstep (se 1 (by rfl) ⟨1727141, by rfl⟩ : syracuseStep 2302855 = 3454283) B3454283
theorem B2590717 : Blo 2301435 2590717 := bbase (se 3 (by rfl) ⟨485759, by rfl⟩ : syracuseStep 2590717 = 971519) (by norm_num)
theorem B3454289 : Blo 2301435 3454289 := bstep (se 2 (by rfl) ⟨1295358, by rfl⟩ : syracuseStep 3454289 = 2590717) B2590717
theorem B2302859 : Blo 2301435 2302859 := bstep (se 1 (by rfl) ⟨1727144, by rfl⟩ : syracuseStep 2302859 = 3454289) B3454289
theorem B7772165 : Blo 2301435 7772165 := bbase (se 4 (by rfl) ⟨728640, by rfl⟩ : syracuseStep 7772165 = 1457281) (by norm_num)
theorem B5181443 : Blo 2301435 5181443 := bstep (se 1 (by rfl) ⟨3886082, by rfl⟩ : syracuseStep 5181443 = 7772165) B7772165
theorem B3454295 : Blo 2301435 3454295 := bstep (se 1 (by rfl) ⟨2590721, by rfl⟩ : syracuseStep 3454295 = 5181443) B5181443
theorem B2302863 : Blo 2301435 2302863 := bstep (se 1 (by rfl) ⟨1727147, by rfl⟩ : syracuseStep 2302863 = 3454295) B3454295
theorem B3454301 : Blo 2301435 3454301 := bbase (se 3 (by rfl) ⟨647681, by rfl⟩ : syracuseStep 3454301 = 1295363) (by norm_num)
theorem B2302867 : Blo 2301435 2302867 := bstep (se 1 (by rfl) ⟨1727150, by rfl⟩ : syracuseStep 2302867 = 3454301) B3454301
theorem B5181461 : Blo 2301435 5181461 := bbase (se 6 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 5181461 = 242881) (by norm_num)
theorem B3454307 : Blo 2301435 3454307 := bstep (se 1 (by rfl) ⟨2590730, by rfl⟩ : syracuseStep 3454307 = 5181461) B5181461
theorem B2302871 : Blo 2301435 2302871 := bstep (se 1 (by rfl) ⟨1727153, by rfl⟩ : syracuseStep 2302871 = 3454307) B3454307
theorem B8743733 : Blo 2301435 8743733 := bbase (se 5 (by rfl) ⟨409862, by rfl⟩ : syracuseStep 8743733 = 819725) (by norm_num)
theorem B5829155 : Blo 2301435 5829155 := bstep (se 1 (by rfl) ⟨4371866, by rfl⟩ : syracuseStep 5829155 = 8743733) B8743733
theorem B3886103 : Blo 2301435 3886103 := bstep (se 1 (by rfl) ⟨2914577, by rfl⟩ : syracuseStep 3886103 = 5829155) B5829155
theorem B2590735 : Blo 2301435 2590735 := bstep (se 1 (by rfl) ⟨1943051, by rfl⟩ : syracuseStep 2590735 = 3886103) B3886103
theorem B3454313 : Blo 2301435 3454313 := bstep (se 2 (by rfl) ⟨1295367, by rfl⟩ : syracuseStep 3454313 = 2590735) B2590735
theorem B2302875 : Blo 2301435 2302875 := bstep (se 1 (by rfl) ⟨1727156, by rfl⟩ : syracuseStep 2302875 = 3454313) B3454313
theorem B2766577 : Blo 2301435 2766577 := bbase (se 2 (by rfl) ⟨1037466, by rfl⟩ : syracuseStep 2766577 = 2074933) (by norm_num)
theorem B3688769 : Blo 2301435 3688769 := bstep (se 2 (by rfl) ⟨1383288, by rfl⟩ : syracuseStep 3688769 = 2766577) B2766577
theorem B2459179 : Blo 2301435 2459179 := bstep (se 1 (by rfl) ⟨1844384, by rfl⟩ : syracuseStep 2459179 = 3688769) B3688769
theorem B13115621 : Blo 2301435 13115621 := bstep (se 4 (by rfl) ⟨1229589, by rfl⟩ : syracuseStep 13115621 = 2459179) B2459179
theorem B8743747 : Blo 2301435 8743747 := bstep (se 1 (by rfl) ⟨6557810, by rfl⟩ : syracuseStep 8743747 = 13115621) B13115621
theorem B11658329 : Blo 2301435 11658329 := bstep (se 2 (by rfl) ⟨4371873, by rfl⟩ : syracuseStep 11658329 = 8743747) B8743747
theorem B7772219 : Blo 2301435 7772219 := bstep (se 1 (by rfl) ⟨5829164, by rfl⟩ : syracuseStep 7772219 = 11658329) B11658329
theorem B5181479 : Blo 2301435 5181479 := bstep (se 1 (by rfl) ⟨3886109, by rfl⟩ : syracuseStep 5181479 = 7772219) B7772219
theorem B3454319 : Blo 2301435 3454319 := bstep (se 1 (by rfl) ⟨2590739, by rfl⟩ : syracuseStep 3454319 = 5181479) B5181479
theorem B2302879 : Blo 2301435 2302879 := bstep (se 1 (by rfl) ⟨1727159, by rfl⟩ : syracuseStep 2302879 = 3454319) B3454319
theorem B3454325 : Blo 2301435 3454325 := bbase (se 5 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 3454325 = 323843) (by norm_num)
theorem B2302883 : Blo 2301435 2302883 := bstep (se 1 (by rfl) ⟨1727162, by rfl⟩ : syracuseStep 2302883 = 3454325) B3454325
theorem B3278917 : Blo 2301435 3278917 := bbase (se 4 (by rfl) ⟨307398, by rfl⟩ : syracuseStep 3278917 = 614797) (by norm_num)
theorem B4371889 : Blo 2301435 4371889 := bstep (se 2 (by rfl) ⟨1639458, by rfl⟩ : syracuseStep 4371889 = 3278917) B3278917
theorem B5829185 : Blo 2301435 5829185 := bstep (se 2 (by rfl) ⟨2185944, by rfl⟩ : syracuseStep 5829185 = 4371889) B4371889
theorem B3886123 : Blo 2301435 3886123 := bstep (se 1 (by rfl) ⟨2914592, by rfl⟩ : syracuseStep 3886123 = 5829185) B5829185
theorem B5181497 : Blo 2301435 5181497 := bstep (se 2 (by rfl) ⟨1943061, by rfl⟩ : syracuseStep 5181497 = 3886123) B3886123
theorem B3454331 : Blo 2301435 3454331 := bstep (se 1 (by rfl) ⟨2590748, by rfl⟩ : syracuseStep 3454331 = 5181497) B5181497
theorem B2302887 : Blo 2301435 2302887 := bstep (se 1 (by rfl) ⟨1727165, by rfl⟩ : syracuseStep 2302887 = 3454331) B3454331
theorem B2590753 : Blo 2301435 2590753 := bbase (se 2 (by rfl) ⟨971532, by rfl⟩ : syracuseStep 2590753 = 1943065) (by norm_num)
theorem B3454337 : Blo 2301435 3454337 := bstep (se 2 (by rfl) ⟨1295376, by rfl⟩ : syracuseStep 3454337 = 2590753) B2590753
theorem B2302891 : Blo 2301435 2302891 := bstep (se 1 (by rfl) ⟨1727168, by rfl⟩ : syracuseStep 2302891 = 3454337) B3454337
theorem B5829205 : Blo 2301435 5829205 := bbase (se 8 (by rfl) ⟨34155, by rfl⟩ : syracuseStep 5829205 = 68311) (by norm_num)
theorem B7772273 : Blo 2301435 7772273 := bstep (se 2 (by rfl) ⟨2914602, by rfl⟩ : syracuseStep 7772273 = 5829205) B5829205
theorem B5181515 : Blo 2301435 5181515 := bstep (se 1 (by rfl) ⟨3886136, by rfl⟩ : syracuseStep 5181515 = 7772273) B7772273
theorem B3454343 : Blo 2301435 3454343 := bstep (se 1 (by rfl) ⟨2590757, by rfl⟩ : syracuseStep 3454343 = 5181515) B5181515
theorem B2302895 : Blo 2301435 2302895 := bstep (se 1 (by rfl) ⟨1727171, by rfl⟩ : syracuseStep 2302895 = 3454343) B3454343
theorem B3454349 : Blo 2301435 3454349 := bbase (se 3 (by rfl) ⟨647690, by rfl⟩ : syracuseStep 3454349 = 1295381) (by norm_num)
theorem B2302899 : Blo 2301435 2302899 := bstep (se 1 (by rfl) ⟨1727174, by rfl⟩ : syracuseStep 2302899 = 3454349) B3454349
theorem B5181533 : Blo 2301435 5181533 := bbase (se 3 (by rfl) ⟨971537, by rfl⟩ : syracuseStep 5181533 = 1943075) (by norm_num)
theorem B3454355 : Blo 2301435 3454355 := bstep (se 1 (by rfl) ⟨2590766, by rfl⟩ : syracuseStep 3454355 = 5181533) B5181533
theorem B2302903 : Blo 2301435 2302903 := bstep (se 1 (by rfl) ⟨1727177, by rfl⟩ : syracuseStep 2302903 = 3454355) B3454355
theorem B3886157 : Blo 2301435 3886157 := bbase (se 3 (by rfl) ⟨728654, by rfl⟩ : syracuseStep 3886157 = 1457309) (by norm_num)
theorem B2590771 : Blo 2301435 2590771 := bstep (se 1 (by rfl) ⟨1943078, by rfl⟩ : syracuseStep 2590771 = 3886157) B3886157
theorem B3454361 : Blo 2301435 3454361 := bstep (se 2 (by rfl) ⟨1295385, by rfl⟩ : syracuseStep 3454361 = 2590771) B2590771
theorem B2302907 : Blo 2301435 2302907 := bstep (se 1 (by rfl) ⟨1727180, by rfl⟩ : syracuseStep 2302907 = 3454361) B3454361
theorem B7985861 : Blo 2301435 7985861 := bbase (se 4 (by rfl) ⟨748674, by rfl⟩ : syracuseStep 7985861 = 1497349) (by norm_num)
theorem B5323907 : Blo 2301435 5323907 := bstep (se 1 (by rfl) ⟨3992930, by rfl⟩ : syracuseStep 5323907 = 7985861) B7985861
theorem B3549271 : Blo 2301435 3549271 := bstep (se 1 (by rfl) ⟨2661953, by rfl⟩ : syracuseStep 3549271 = 5323907) B5323907
theorem B4732361 : Blo 2301435 4732361 := bstep (se 2 (by rfl) ⟨1774635, by rfl⟩ : syracuseStep 4732361 = 3549271) B3549271
theorem B3154907 : Blo 2301435 3154907 := bstep (se 1 (by rfl) ⟨2366180, by rfl⟩ : syracuseStep 3154907 = 4732361) B4732361
theorem B8413085 : Blo 2301435 8413085 := bstep (se 3 (by rfl) ⟨1577453, by rfl⟩ : syracuseStep 8413085 = 3154907) B3154907
theorem B5608723 : Blo 2301435 5608723 := bstep (se 1 (by rfl) ⟨4206542, by rfl⟩ : syracuseStep 5608723 = 8413085) B8413085
theorem B7478297 : Blo 2301435 7478297 := bstep (se 2 (by rfl) ⟨2804361, by rfl⟩ : syracuseStep 7478297 = 5608723) B5608723
theorem B4985531 : Blo 2301435 4985531 := bstep (se 1 (by rfl) ⟨3739148, by rfl⟩ : syracuseStep 4985531 = 7478297) B7478297
theorem B3323687 : Blo 2301435 3323687 := bstep (se 1 (by rfl) ⟨2492765, by rfl⟩ : syracuseStep 3323687 = 4985531) B4985531
theorem B8863165 : Blo 2301435 8863165 := bstep (se 3 (by rfl) ⟨1661843, by rfl⟩ : syracuseStep 8863165 = 3323687) B3323687
theorem B47270213 : Blo 2301435 47270213 := bstep (se 4 (by rfl) ⟨4431582, by rfl⟩ : syracuseStep 47270213 = 8863165) B8863165
theorem B31513475 : Blo 2301435 31513475 := bstep (se 1 (by rfl) ⟨23635106, by rfl⟩ : syracuseStep 31513475 = 47270213) B47270213
theorem B21008983 : Blo 2301435 21008983 := bstep (se 1 (by rfl) ⟨15756737, by rfl⟩ : syracuseStep 21008983 = 31513475) B31513475
theorem B28011977 : Blo 2301435 28011977 := bstep (se 2 (by rfl) ⟨10504491, by rfl⟩ : syracuseStep 28011977 = 21008983) B21008983
theorem B18674651 : Blo 2301435 18674651 := bstep (se 1 (by rfl) ⟨14005988, by rfl⟩ : syracuseStep 18674651 = 28011977) B28011977
theorem B49799069 : Blo 2301435 49799069 := bstep (se 3 (by rfl) ⟨9337325, by rfl⟩ : syracuseStep 49799069 = 18674651) B18674651
theorem B33199379 : Blo 2301435 33199379 := bstep (se 1 (by rfl) ⟨24899534, by rfl⟩ : syracuseStep 33199379 = 49799069) B49799069
theorem B22132919 : Blo 2301435 22132919 := bstep (se 1 (by rfl) ⟨16599689, by rfl⟩ : syracuseStep 22132919 = 33199379) B33199379
theorem B14755279 : Blo 2301435 14755279 := bstep (se 1 (by rfl) ⟨11066459, by rfl⟩ : syracuseStep 14755279 = 22132919) B22132919
theorem B19673705 : Blo 2301435 19673705 := bstep (se 2 (by rfl) ⟨7377639, by rfl⟩ : syracuseStep 19673705 = 14755279) B14755279
theorem B13115803 : Blo 2301435 13115803 := bstep (se 1 (by rfl) ⟨9836852, by rfl⟩ : syracuseStep 13115803 = 19673705) B19673705
theorem B17487737 : Blo 2301435 17487737 := bstep (se 2 (by rfl) ⟨6557901, by rfl⟩ : syracuseStep 17487737 = 13115803) B13115803
theorem B11658491 : Blo 2301435 11658491 := bstep (se 1 (by rfl) ⟨8743868, by rfl⟩ : syracuseStep 11658491 = 17487737) B17487737
theorem B7772327 : Blo 2301435 7772327 := bstep (se 1 (by rfl) ⟨5829245, by rfl⟩ : syracuseStep 7772327 = 11658491) B11658491
theorem B5181551 : Blo 2301435 5181551 := bstep (se 1 (by rfl) ⟨3886163, by rfl⟩ : syracuseStep 5181551 = 7772327) B7772327
theorem B3454367 : Blo 2301435 3454367 := bstep (se 1 (by rfl) ⟨2590775, by rfl⟩ : syracuseStep 3454367 = 5181551) B5181551
theorem B2302911 : Blo 2301435 2302911 := bstep (se 1 (by rfl) ⟨1727183, by rfl⟩ : syracuseStep 2302911 = 3454367) B3454367
theorem B3454373 : Blo 2301435 3454373 := bbase (se 4 (by rfl) ⟨323847, by rfl⟩ : syracuseStep 3454373 = 647695) (by norm_num)
theorem B2302915 : Blo 2301435 2302915 := bstep (se 1 (by rfl) ⟨1727186, by rfl⟩ : syracuseStep 2302915 = 3454373) B3454373
theorem B2914633 : Blo 2301435 2914633 := bbase (se 2 (by rfl) ⟨1092987, by rfl⟩ : syracuseStep 2914633 = 2185975) (by norm_num)
theorem B3886177 : Blo 2301435 3886177 := bstep (se 2 (by rfl) ⟨1457316, by rfl⟩ : syracuseStep 3886177 = 2914633) B2914633
theorem B5181569 : Blo 2301435 5181569 := bstep (se 2 (by rfl) ⟨1943088, by rfl⟩ : syracuseStep 5181569 = 3886177) B3886177
theorem B3454379 : Blo 2301435 3454379 := bstep (se 1 (by rfl) ⟨2590784, by rfl⟩ : syracuseStep 3454379 = 5181569) B5181569
theorem B2302919 : Blo 2301435 2302919 := bstep (se 1 (by rfl) ⟨1727189, by rfl⟩ : syracuseStep 2302919 = 3454379) B3454379
theorem B2590789 : Blo 2301435 2590789 := bbase (se 4 (by rfl) ⟨242886, by rfl⟩ : syracuseStep 2590789 = 485773) (by norm_num)
theorem B3454385 : Blo 2301435 3454385 := bstep (se 2 (by rfl) ⟨1295394, by rfl⟩ : syracuseStep 3454385 = 2590789) B2590789
theorem B2302923 : Blo 2301435 2302923 := bstep (se 1 (by rfl) ⟨1727192, by rfl⟩ : syracuseStep 2302923 = 3454385) B3454385
theorem B4371965 : Blo 2301435 4371965 := bbase (se 3 (by rfl) ⟨819743, by rfl⟩ : syracuseStep 4371965 = 1639487) (by norm_num)
theorem B2914643 : Blo 2301435 2914643 := bstep (se 1 (by rfl) ⟨2185982, by rfl⟩ : syracuseStep 2914643 = 4371965) B4371965
theorem B7772381 : Blo 2301435 7772381 := bstep (se 3 (by rfl) ⟨1457321, by rfl⟩ : syracuseStep 7772381 = 2914643) B2914643
theorem B5181587 : Blo 2301435 5181587 := bstep (se 1 (by rfl) ⟨3886190, by rfl⟩ : syracuseStep 5181587 = 7772381) B7772381
theorem B3454391 : Blo 2301435 3454391 := bstep (se 1 (by rfl) ⟨2590793, by rfl⟩ : syracuseStep 3454391 = 5181587) B5181587
theorem B2302927 : Blo 2301435 2302927 := bstep (se 1 (by rfl) ⟨1727195, by rfl⟩ : syracuseStep 2302927 = 3454391) B3454391
theorem B3454397 : Blo 2301435 3454397 := bbase (se 3 (by rfl) ⟨647699, by rfl⟩ : syracuseStep 3454397 = 1295399) (by norm_num)
theorem B2302931 : Blo 2301435 2302931 := bstep (se 1 (by rfl) ⟨1727198, by rfl⟩ : syracuseStep 2302931 = 3454397) B3454397
theorem B5181605 : Blo 2301435 5181605 := bbase (se 4 (by rfl) ⟨485775, by rfl⟩ : syracuseStep 5181605 = 971551) (by norm_num)
theorem B3454403 : Blo 2301435 3454403 := bstep (se 1 (by rfl) ⟨2590802, by rfl⟩ : syracuseStep 3454403 = 5181605) B5181605
theorem B2302935 : Blo 2301435 2302935 := bstep (se 1 (by rfl) ⟨1727201, by rfl⟩ : syracuseStep 2302935 = 3454403) B3454403
theorem B5829317 : Blo 2301435 5829317 := bbase (se 4 (by rfl) ⟨546498, by rfl⟩ : syracuseStep 5829317 = 1092997) (by norm_num)
theorem B3886211 : Blo 2301435 3886211 := bstep (se 1 (by rfl) ⟨2914658, by rfl⟩ : syracuseStep 3886211 = 5829317) B5829317
theorem B2590807 : Blo 2301435 2590807 := bstep (se 1 (by rfl) ⟨1943105, by rfl⟩ : syracuseStep 2590807 = 3886211) B3886211
theorem B3454409 : Blo 2301435 3454409 := bstep (se 2 (by rfl) ⟨1295403, by rfl⟩ : syracuseStep 3454409 = 2590807) B2590807
theorem B2302939 : Blo 2301435 2302939 := bstep (se 1 (by rfl) ⟨1727204, by rfl⟩ : syracuseStep 2302939 = 3454409) B3454409
theorem B7003093 : Blo 2301435 7003093 := bbase (se 7 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 7003093 = 164135) (by norm_num)
theorem B9337457 : Blo 2301435 9337457 := bstep (se 2 (by rfl) ⟨3501546, by rfl⟩ : syracuseStep 9337457 = 7003093) B7003093
theorem B24899885 : Blo 2301435 24899885 := bstep (se 3 (by rfl) ⟨4668728, by rfl⟩ : syracuseStep 24899885 = 9337457) B9337457
theorem B16599923 : Blo 2301435 16599923 := bstep (se 1 (by rfl) ⟨12449942, by rfl⟩ : syracuseStep 16599923 = 24899885) B24899885
theorem B11066615 : Blo 2301435 11066615 := bstep (se 1 (by rfl) ⟨8299961, by rfl⟩ : syracuseStep 11066615 = 16599923) B16599923
theorem B7377743 : Blo 2301435 7377743 := bstep (se 1 (by rfl) ⟨5533307, by rfl⟩ : syracuseStep 7377743 = 11066615) B11066615
theorem B4918495 : Blo 2301435 4918495 := bstep (se 1 (by rfl) ⟨3688871, by rfl⟩ : syracuseStep 4918495 = 7377743) B7377743
theorem B6557993 : Blo 2301435 6557993 := bstep (se 2 (by rfl) ⟨2459247, by rfl⟩ : syracuseStep 6557993 = 4918495) B4918495
theorem B4371995 : Blo 2301435 4371995 := bstep (se 1 (by rfl) ⟨3278996, by rfl⟩ : syracuseStep 4371995 = 6557993) B6557993
theorem B11658653 : Blo 2301435 11658653 := bstep (se 3 (by rfl) ⟨2185997, by rfl⟩ : syracuseStep 11658653 = 4371995) B4371995
theorem B7772435 : Blo 2301435 7772435 := bstep (se 1 (by rfl) ⟨5829326, by rfl⟩ : syracuseStep 7772435 = 11658653) B11658653
theorem B5181623 : Blo 2301435 5181623 := bstep (se 1 (by rfl) ⟨3886217, by rfl⟩ : syracuseStep 5181623 = 7772435) B7772435
theorem B3454415 : Blo 2301435 3454415 := bstep (se 1 (by rfl) ⟨2590811, by rfl⟩ : syracuseStep 3454415 = 5181623) B5181623
theorem B2302943 : Blo 2301435 2302943 := bstep (se 1 (by rfl) ⟨1727207, by rfl⟩ : syracuseStep 2302943 = 3454415) B3454415
theorem B3454421 : Blo 2301435 3454421 := bbase (se 7 (by rfl) ⟨40481, by rfl⟩ : syracuseStep 3454421 = 80963) (by norm_num)
theorem B2302947 : Blo 2301435 2302947 := bstep (se 1 (by rfl) ⟨1727210, by rfl⟩ : syracuseStep 2302947 = 3454421) B3454421
theorem B8744021 : Blo 2301435 8744021 := bbase (se 8 (by rfl) ⟨51234, by rfl⟩ : syracuseStep 8744021 = 102469) (by norm_num)
theorem B5829347 : Blo 2301435 5829347 := bstep (se 1 (by rfl) ⟨4372010, by rfl⟩ : syracuseStep 5829347 = 8744021) B8744021
theorem B3886231 : Blo 2301435 3886231 := bstep (se 1 (by rfl) ⟨2914673, by rfl⟩ : syracuseStep 3886231 = 5829347) B5829347
theorem B5181641 : Blo 2301435 5181641 := bstep (se 2 (by rfl) ⟨1943115, by rfl⟩ : syracuseStep 5181641 = 3886231) B3886231
theorem B3454427 : Blo 2301435 3454427 := bstep (se 1 (by rfl) ⟨2590820, by rfl⟩ : syracuseStep 3454427 = 5181641) B5181641
theorem B2302951 : Blo 2301435 2302951 := bstep (se 1 (by rfl) ⟨1727213, by rfl⟩ : syracuseStep 2302951 = 3454427) B3454427
theorem B2590825 : Blo 2301435 2590825 := bbase (se 2 (by rfl) ⟨971559, by rfl⟩ : syracuseStep 2590825 = 1943119) (by norm_num)
theorem B3454433 : Blo 2301435 3454433 := bstep (se 2 (by rfl) ⟨1295412, by rfl⟩ : syracuseStep 3454433 = 2590825) B2590825
theorem B2302955 : Blo 2301435 2302955 := bstep (se 1 (by rfl) ⟨1727216, by rfl⟩ : syracuseStep 2302955 = 3454433) B3454433
theorem B2766673 : Blo 2301435 2766673 := bbase (se 2 (by rfl) ⟨1037502, by rfl⟩ : syracuseStep 2766673 = 2075005) (by norm_num)
theorem B3688897 : Blo 2301435 3688897 := bstep (se 2 (by rfl) ⟨1383336, by rfl⟩ : syracuseStep 3688897 = 2766673) B2766673
theorem B4918529 : Blo 2301435 4918529 := bstep (se 2 (by rfl) ⟨1844448, by rfl⟩ : syracuseStep 4918529 = 3688897) B3688897
theorem B13116077 : Blo 2301435 13116077 := bstep (se 3 (by rfl) ⟨2459264, by rfl⟩ : syracuseStep 13116077 = 4918529) B4918529
theorem B8744051 : Blo 2301435 8744051 := bstep (se 1 (by rfl) ⟨6558038, by rfl⟩ : syracuseStep 8744051 = 13116077) B13116077
theorem B5829367 : Blo 2301435 5829367 := bstep (se 1 (by rfl) ⟨4372025, by rfl⟩ : syracuseStep 5829367 = 8744051) B8744051
theorem B7772489 : Blo 2301435 7772489 := bstep (se 2 (by rfl) ⟨2914683, by rfl⟩ : syracuseStep 7772489 = 5829367) B5829367
theorem B5181659 : Blo 2301435 5181659 := bstep (se 1 (by rfl) ⟨3886244, by rfl⟩ : syracuseStep 5181659 = 7772489) B7772489
theorem B3454439 : Blo 2301435 3454439 := bstep (se 1 (by rfl) ⟨2590829, by rfl⟩ : syracuseStep 3454439 = 5181659) B5181659
theorem B2302959 : Blo 2301435 2302959 := bstep (se 1 (by rfl) ⟨1727219, by rfl⟩ : syracuseStep 2302959 = 3454439) B3454439
theorem B3454445 : Blo 2301435 3454445 := bbase (se 3 (by rfl) ⟨647708, by rfl⟩ : syracuseStep 3454445 = 1295417) (by norm_num)
theorem B2302963 : Blo 2301435 2302963 := bstep (se 1 (by rfl) ⟨1727222, by rfl⟩ : syracuseStep 2302963 = 3454445) B3454445
theorem B5181677 : Blo 2301435 5181677 := bbase (se 3 (by rfl) ⟨971564, by rfl⟩ : syracuseStep 5181677 = 1943129) (by norm_num)
theorem B3454451 : Blo 2301435 3454451 := bstep (se 1 (by rfl) ⟨2590838, by rfl⟩ : syracuseStep 3454451 = 5181677) B5181677
theorem B2302967 : Blo 2301435 2302967 := bstep (se 1 (by rfl) ⟨1727225, by rfl⟩ : syracuseStep 2302967 = 3454451) B3454451
theorem B3279037 : Blo 2301435 3279037 := bbase (se 3 (by rfl) ⟨614819, by rfl⟩ : syracuseStep 3279037 = 1229639) (by norm_num)
theorem B4372049 : Blo 2301435 4372049 := bstep (se 2 (by rfl) ⟨1639518, by rfl⟩ : syracuseStep 4372049 = 3279037) B3279037
theorem B2914699 : Blo 2301435 2914699 := bstep (se 1 (by rfl) ⟨2186024, by rfl⟩ : syracuseStep 2914699 = 4372049) B4372049
theorem B3886265 : Blo 2301435 3886265 := bstep (se 2 (by rfl) ⟨1457349, by rfl⟩ : syracuseStep 3886265 = 2914699) B2914699
theorem B2590843 : Blo 2301435 2590843 := bstep (se 1 (by rfl) ⟨1943132, by rfl⟩ : syracuseStep 2590843 = 3886265) B3886265
theorem B3454457 : Blo 2301435 3454457 := bstep (se 2 (by rfl) ⟨1295421, by rfl⟩ : syracuseStep 3454457 = 2590843) B2590843
theorem B2302971 : Blo 2301435 2302971 := bstep (se 1 (by rfl) ⟨1727228, by rfl⟩ : syracuseStep 2302971 = 3454457) B3454457
theorem B7003189 : Blo 2301435 7003189 := bbase (se 5 (by rfl) ⟨328274, by rfl⟩ : syracuseStep 7003189 = 656549) (by norm_num)
theorem B9337585 : Blo 2301435 9337585 := bstep (se 2 (by rfl) ⟨3501594, by rfl⟩ : syracuseStep 9337585 = 7003189) B7003189
theorem B12450113 : Blo 2301435 12450113 := bstep (se 2 (by rfl) ⟨4668792, by rfl⟩ : syracuseStep 12450113 = 9337585) B9337585
theorem B8300075 : Blo 2301435 8300075 := bstep (se 1 (by rfl) ⟨6225056, by rfl⟩ : syracuseStep 8300075 = 12450113) B12450113
theorem B88534133 : Blo 2301435 88534133 := bstep (se 5 (by rfl) ⟨4150037, by rfl⟩ : syracuseStep 88534133 = 8300075) B8300075
theorem B59022755 : Blo 2301435 59022755 := bstep (se 1 (by rfl) ⟨44267066, by rfl⟩ : syracuseStep 59022755 = 88534133) B88534133
theorem B39348503 : Blo 2301435 39348503 := bstep (se 1 (by rfl) ⟨29511377, by rfl⟩ : syracuseStep 39348503 = 59022755) B59022755
theorem B26232335 : Blo 2301435 26232335 := bstep (se 1 (by rfl) ⟨19674251, by rfl⟩ : syracuseStep 26232335 = 39348503) B39348503
theorem B17488223 : Blo 2301435 17488223 := bstep (se 1 (by rfl) ⟨13116167, by rfl⟩ : syracuseStep 17488223 = 26232335) B26232335
theorem B11658815 : Blo 2301435 11658815 := bstep (se 1 (by rfl) ⟨8744111, by rfl⟩ : syracuseStep 11658815 = 17488223) B17488223
theorem B7772543 : Blo 2301435 7772543 := bstep (se 1 (by rfl) ⟨5829407, by rfl⟩ : syracuseStep 7772543 = 11658815) B11658815
theorem B5181695 : Blo 2301435 5181695 := bstep (se 1 (by rfl) ⟨3886271, by rfl⟩ : syracuseStep 5181695 = 7772543) B7772543
theorem B3454463 : Blo 2301435 3454463 := bstep (se 1 (by rfl) ⟨2590847, by rfl⟩ : syracuseStep 3454463 = 5181695) B5181695
theorem B2302975 : Blo 2301435 2302975 := bstep (se 1 (by rfl) ⟨1727231, by rfl⟩ : syracuseStep 2302975 = 3454463) B3454463
theorem B3454469 : Blo 2301435 3454469 := bbase (se 4 (by rfl) ⟨323856, by rfl⟩ : syracuseStep 3454469 = 647713) (by norm_num)
theorem B2302979 : Blo 2301435 2302979 := bstep (se 1 (by rfl) ⟨1727234, by rfl⟩ : syracuseStep 2302979 = 3454469) B3454469
theorem B3886285 : Blo 2301435 3886285 := bbase (se 3 (by rfl) ⟨728678, by rfl⟩ : syracuseStep 3886285 = 1457357) (by norm_num)
theorem B5181713 : Blo 2301435 5181713 := bstep (se 2 (by rfl) ⟨1943142, by rfl⟩ : syracuseStep 5181713 = 3886285) B3886285
theorem B3454475 : Blo 2301435 3454475 := bstep (se 1 (by rfl) ⟨2590856, by rfl⟩ : syracuseStep 3454475 = 5181713) B5181713
theorem B2302983 : Blo 2301435 2302983 := bstep (se 1 (by rfl) ⟨1727237, by rfl⟩ : syracuseStep 2302983 = 3454475) B3454475
theorem B2590861 : Blo 2301435 2590861 := bbase (se 3 (by rfl) ⟨485786, by rfl⟩ : syracuseStep 2590861 = 971573) (by norm_num)
theorem B3454481 : Blo 2301435 3454481 := bstep (se 2 (by rfl) ⟨1295430, by rfl⟩ : syracuseStep 3454481 = 2590861) B2590861
theorem B2302987 : Blo 2301435 2302987 := bstep (se 1 (by rfl) ⟨1727240, by rfl⟩ : syracuseStep 2302987 = 3454481) B3454481
theorem B7772597 : Blo 2301435 7772597 := bbase (se 5 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 7772597 = 728681) (by norm_num)
theorem B5181731 : Blo 2301435 5181731 := bstep (se 1 (by rfl) ⟨3886298, by rfl⟩ : syracuseStep 5181731 = 7772597) B7772597
theorem B3454487 : Blo 2301435 3454487 := bstep (se 1 (by rfl) ⟨2590865, by rfl⟩ : syracuseStep 3454487 = 5181731) B5181731
theorem B2302991 : Blo 2301435 2302991 := bstep (se 1 (by rfl) ⟨1727243, by rfl⟩ : syracuseStep 2302991 = 3454487) B3454487
theorem B3454493 : Blo 2301435 3454493 := bbase (se 3 (by rfl) ⟨647717, by rfl⟩ : syracuseStep 3454493 = 1295435) (by norm_num)
theorem B2302995 : Blo 2301435 2302995 := bstep (se 1 (by rfl) ⟨1727246, by rfl⟩ : syracuseStep 2302995 = 3454493) B3454493
theorem B5181749 : Blo 2301435 5181749 := bbase (se 5 (by rfl) ⟨242894, by rfl⟩ : syracuseStep 5181749 = 485789) (by norm_num)
theorem B3454499 : Blo 2301435 3454499 := bstep (se 1 (by rfl) ⟨2590874, by rfl⟩ : syracuseStep 3454499 = 5181749) B5181749
theorem B2302999 : Blo 2301435 2302999 := bstep (se 1 (by rfl) ⟨1727249, by rfl⟩ : syracuseStep 2302999 = 3454499) B3454499
theorem B9971461 : Blo 2301435 9971461 := bbase (se 4 (by rfl) ⟨934824, by rfl⟩ : syracuseStep 9971461 = 1869649) (by norm_num)
theorem B13295281 : Blo 2301435 13295281 := bstep (se 2 (by rfl) ⟨4985730, by rfl⟩ : syracuseStep 13295281 = 9971461) B9971461
theorem B17727041 : Blo 2301435 17727041 := bstep (se 2 (by rfl) ⟨6647640, by rfl⟩ : syracuseStep 17727041 = 13295281) B13295281
theorem B11818027 : Blo 2301435 11818027 := bstep (se 1 (by rfl) ⟨8863520, by rfl⟩ : syracuseStep 11818027 = 17727041) B17727041
theorem B63029477 : Blo 2301435 63029477 := bstep (se 4 (by rfl) ⟨5909013, by rfl⟩ : syracuseStep 63029477 = 11818027) B11818027
theorem B42019651 : Blo 2301435 42019651 := bstep (se 1 (by rfl) ⟨31514738, by rfl⟩ : syracuseStep 42019651 = 63029477) B63029477
theorem B56026201 : Blo 2301435 56026201 := bstep (se 2 (by rfl) ⟨21009825, by rfl⟩ : syracuseStep 56026201 = 42019651) B42019651
theorem B74701601 : Blo 2301435 74701601 := bstep (se 2 (by rfl) ⟨28013100, by rfl⟩ : syracuseStep 74701601 = 56026201) B56026201
theorem B49801067 : Blo 2301435 49801067 := bstep (se 1 (by rfl) ⟨37350800, by rfl⟩ : syracuseStep 49801067 = 74701601) B74701601
theorem B33200711 : Blo 2301435 33200711 := bstep (se 1 (by rfl) ⟨24900533, by rfl⟩ : syracuseStep 33200711 = 49801067) B49801067
theorem B22133807 : Blo 2301435 22133807 := bstep (se 1 (by rfl) ⟨16600355, by rfl⟩ : syracuseStep 22133807 = 33200711) B33200711
theorem B14755871 : Blo 2301435 14755871 := bstep (se 1 (by rfl) ⟨11066903, by rfl⟩ : syracuseStep 14755871 = 22133807) B22133807
theorem B9837247 : Blo 2301435 9837247 := bstep (se 1 (by rfl) ⟨7377935, by rfl⟩ : syracuseStep 9837247 = 14755871) B14755871
theorem B13116329 : Blo 2301435 13116329 := bstep (se 2 (by rfl) ⟨4918623, by rfl⟩ : syracuseStep 13116329 = 9837247) B9837247
theorem B8744219 : Blo 2301435 8744219 := bstep (se 1 (by rfl) ⟨6558164, by rfl⟩ : syracuseStep 8744219 = 13116329) B13116329
theorem B5829479 : Blo 2301435 5829479 := bstep (se 1 (by rfl) ⟨4372109, by rfl⟩ : syracuseStep 5829479 = 8744219) B8744219
theorem B3886319 : Blo 2301435 3886319 := bstep (se 1 (by rfl) ⟨2914739, by rfl⟩ : syracuseStep 3886319 = 5829479) B5829479
theorem B2590879 : Blo 2301435 2590879 := bstep (se 1 (by rfl) ⟨1943159, by rfl⟩ : syracuseStep 2590879 = 3886319) B3886319
theorem B3454505 : Blo 2301435 3454505 := bstep (se 2 (by rfl) ⟨1295439, by rfl⟩ : syracuseStep 3454505 = 2590879) B2590879
theorem B2303003 : Blo 2301435 2303003 := bstep (se 1 (by rfl) ⟨1727252, by rfl⟩ : syracuseStep 2303003 = 3454505) B3454505
theorem B10940789 : Blo 2301435 10940789 := bbase (se 5 (by rfl) ⟨512849, by rfl⟩ : syracuseStep 10940789 = 1025699) (by norm_num)
theorem B29175437 : Blo 2301435 29175437 := bstep (se 3 (by rfl) ⟨5470394, by rfl⟩ : syracuseStep 29175437 = 10940789) B10940789
theorem B19450291 : Blo 2301435 19450291 := bstep (se 1 (by rfl) ⟨14587718, by rfl⟩ : syracuseStep 19450291 = 29175437) B29175437
theorem B25933721 : Blo 2301435 25933721 := bstep (se 2 (by rfl) ⟨9725145, by rfl⟩ : syracuseStep 25933721 = 19450291) B19450291
theorem B69156589 : Blo 2301435 69156589 := bstep (se 3 (by rfl) ⟨12966860, by rfl⟩ : syracuseStep 69156589 = 25933721) B25933721
theorem B92208785 : Blo 2301435 92208785 := bstep (se 2 (by rfl) ⟨34578294, by rfl⟩ : syracuseStep 92208785 = 69156589) B69156589
theorem B245890093 : Blo 2301435 245890093 := bstep (se 3 (by rfl) ⟨46104392, by rfl⟩ : syracuseStep 245890093 = 92208785) B92208785
theorem B327853457 : Blo 2301435 327853457 := bstep (se 2 (by rfl) ⟨122945046, by rfl⟩ : syracuseStep 327853457 = 245890093) B245890093
theorem B218568971 : Blo 2301435 218568971 := bstep (se 1 (by rfl) ⟨163926728, by rfl⟩ : syracuseStep 218568971 = 327853457) B327853457
theorem B145712647 : Blo 2301435 145712647 := bstep (se 1 (by rfl) ⟨109284485, by rfl⟩ : syracuseStep 145712647 = 218568971) B218568971
theorem B194283529 : Blo 2301435 194283529 := bstep (se 2 (by rfl) ⟨72856323, by rfl⟩ : syracuseStep 194283529 = 145712647) B145712647
theorem B1036178821 : Blo 2301435 1036178821 := bstep (se 4 (by rfl) ⟨97141764, by rfl⟩ : syracuseStep 1036178821 = 194283529) B194283529
theorem B1381571761 : Blo 2301435 1381571761 := bstep (se 2 (by rfl) ⟨518089410, by rfl⟩ : syracuseStep 1381571761 = 1036178821) B1036178821
theorem B1842095681 : Blo 2301435 1842095681 := bstep (se 2 (by rfl) ⟨690785880, by rfl⟩ : syracuseStep 1842095681 = 1381571761) B1381571761
theorem B1228063787 : Blo 2301435 1228063787 := bstep (se 1 (by rfl) ⟨921047840, by rfl⟩ : syracuseStep 1228063787 = 1842095681) B1842095681
theorem B818709191 : Blo 2301435 818709191 := bstep (se 1 (by rfl) ⟨614031893, by rfl⟩ : syracuseStep 818709191 = 1228063787) B1228063787
theorem B545806127 : Blo 2301435 545806127 := bstep (se 1 (by rfl) ⟨409354595, by rfl⟩ : syracuseStep 545806127 = 818709191) B818709191
theorem B1455483005 : Blo 2301435 1455483005 := bstep (se 3 (by rfl) ⟨272903063, by rfl⟩ : syracuseStep 1455483005 = 545806127) B545806127
theorem B970322003 : Blo 2301435 970322003 := bstep (se 1 (by rfl) ⟨727741502, by rfl⟩ : syracuseStep 970322003 = 1455483005) B1455483005
theorem B646881335 : Blo 2301435 646881335 := bstep (se 1 (by rfl) ⟨485161001, by rfl⟩ : syracuseStep 646881335 = 970322003) B970322003
theorem B431254223 : Blo 2301435 431254223 := bstep (se 1 (by rfl) ⟨323440667, by rfl⟩ : syracuseStep 431254223 = 646881335) B646881335
theorem B287502815 : Blo 2301435 287502815 := bstep (se 1 (by rfl) ⟨215627111, by rfl⟩ : syracuseStep 287502815 = 431254223) B431254223
theorem B766674173 : Blo 2301435 766674173 := bstep (se 3 (by rfl) ⟨143751407, by rfl⟩ : syracuseStep 766674173 = 287502815) B287502815
theorem B511116115 : Blo 2301435 511116115 := bstep (se 1 (by rfl) ⟨383337086, by rfl⟩ : syracuseStep 511116115 = 766674173) B766674173
theorem B681488153 : Blo 2301435 681488153 := bstep (se 2 (by rfl) ⟨255558057, by rfl⟩ : syracuseStep 681488153 = 511116115) B511116115
theorem B454325435 : Blo 2301435 454325435 := bstep (se 1 (by rfl) ⟨340744076, by rfl⟩ : syracuseStep 454325435 = 681488153) B681488153
theorem B302883623 : Blo 2301435 302883623 := bstep (se 1 (by rfl) ⟨227162717, by rfl⟩ : syracuseStep 302883623 = 454325435) B454325435
theorem B201922415 : Blo 2301435 201922415 := bstep (se 1 (by rfl) ⟨151441811, by rfl⟩ : syracuseStep 201922415 = 302883623) B302883623
theorem B134614943 : Blo 2301435 134614943 := bstep (se 1 (by rfl) ⟨100961207, by rfl⟩ : syracuseStep 134614943 = 201922415) B201922415
theorem B89743295 : Blo 2301435 89743295 := bstep (se 1 (by rfl) ⟨67307471, by rfl⟩ : syracuseStep 89743295 = 134614943) B134614943
theorem B59828863 : Blo 2301435 59828863 := bstep (se 1 (by rfl) ⟨44871647, by rfl⟩ : syracuseStep 59828863 = 89743295) B89743295
theorem B79771817 : Blo 2301435 79771817 := bstep (se 2 (by rfl) ⟨29914431, by rfl⟩ : syracuseStep 79771817 = 59828863) B59828863
theorem B53181211 : Blo 2301435 53181211 := bstep (se 1 (by rfl) ⟨39885908, by rfl⟩ : syracuseStep 53181211 = 79771817) B79771817
theorem B70908281 : Blo 2301435 70908281 := bstep (se 2 (by rfl) ⟨26590605, by rfl⟩ : syracuseStep 70908281 = 53181211) B53181211
theorem B47272187 : Blo 2301435 47272187 := bstep (se 1 (by rfl) ⟨35454140, by rfl⟩ : syracuseStep 47272187 = 70908281) B70908281
theorem B31514791 : Blo 2301435 31514791 := bstep (se 1 (by rfl) ⟨23636093, by rfl⟩ : syracuseStep 31514791 = 47272187) B47272187
theorem B42019721 : Blo 2301435 42019721 := bstep (se 2 (by rfl) ⟨15757395, by rfl⟩ : syracuseStep 42019721 = 31514791) B31514791
theorem B28013147 : Blo 2301435 28013147 := bstep (se 1 (by rfl) ⟨21009860, by rfl⟩ : syracuseStep 28013147 = 42019721) B42019721
theorem B18675431 : Blo 2301435 18675431 := bstep (se 1 (by rfl) ⟨14006573, by rfl⟩ : syracuseStep 18675431 = 28013147) B28013147
theorem B12450287 : Blo 2301435 12450287 := bstep (se 1 (by rfl) ⟨9337715, by rfl⟩ : syracuseStep 12450287 = 18675431) B18675431
theorem B33200765 : Blo 2301435 33200765 := bstep (se 3 (by rfl) ⟨6225143, by rfl⟩ : syracuseStep 33200765 = 12450287) B12450287
theorem B22133843 : Blo 2301435 22133843 := bstep (se 1 (by rfl) ⟨16600382, by rfl⟩ : syracuseStep 22133843 = 33200765) B33200765
theorem B14755895 : Blo 2301435 14755895 := bstep (se 1 (by rfl) ⟨11066921, by rfl⟩ : syracuseStep 14755895 = 22133843) B22133843
theorem B9837263 : Blo 2301435 9837263 := bstep (se 1 (by rfl) ⟨7377947, by rfl⟩ : syracuseStep 9837263 = 14755895) B14755895
theorem B6558175 : Blo 2301435 6558175 := bstep (se 1 (by rfl) ⟨4918631, by rfl⟩ : syracuseStep 6558175 = 9837263) B9837263
theorem B8744233 : Blo 2301435 8744233 := bstep (se 2 (by rfl) ⟨3279087, by rfl⟩ : syracuseStep 8744233 = 6558175) B6558175
theorem B11658977 : Blo 2301435 11658977 := bstep (se 2 (by rfl) ⟨4372116, by rfl⟩ : syracuseStep 11658977 = 8744233) B8744233
theorem B7772651 : Blo 2301435 7772651 := bstep (se 1 (by rfl) ⟨5829488, by rfl⟩ : syracuseStep 7772651 = 11658977) B11658977
theorem B5181767 : Blo 2301435 5181767 := bstep (se 1 (by rfl) ⟨3886325, by rfl⟩ : syracuseStep 5181767 = 7772651) B7772651
theorem B3454511 : Blo 2301435 3454511 := bstep (se 1 (by rfl) ⟨2590883, by rfl⟩ : syracuseStep 3454511 = 5181767) B5181767
theorem B2303007 : Blo 2301435 2303007 := bstep (se 1 (by rfl) ⟨1727255, by rfl⟩ : syracuseStep 2303007 = 3454511) B3454511
theorem B3454517 : Blo 2301435 3454517 := bbase (se 5 (by rfl) ⟨161930, by rfl⟩ : syracuseStep 3454517 = 323861) (by norm_num)
theorem B2303011 : Blo 2301435 2303011 := bstep (se 1 (by rfl) ⟨1727258, by rfl⟩ : syracuseStep 2303011 = 3454517) B3454517
theorem B5829509 : Blo 2301435 5829509 := bbase (se 4 (by rfl) ⟨546516, by rfl⟩ : syracuseStep 5829509 = 1093033) (by norm_num)
theorem B3886339 : Blo 2301435 3886339 := bstep (se 1 (by rfl) ⟨2914754, by rfl⟩ : syracuseStep 3886339 = 5829509) B5829509
theorem B5181785 : Blo 2301435 5181785 := bstep (se 2 (by rfl) ⟨1943169, by rfl⟩ : syracuseStep 5181785 = 3886339) B3886339
theorem B3454523 : Blo 2301435 3454523 := bstep (se 1 (by rfl) ⟨2590892, by rfl⟩ : syracuseStep 3454523 = 5181785) B5181785
theorem B2303015 : Blo 2301435 2303015 := bstep (se 1 (by rfl) ⟨1727261, by rfl⟩ : syracuseStep 2303015 = 3454523) B3454523
theorem B2590897 : Blo 2301435 2590897 := bbase (se 2 (by rfl) ⟨971586, by rfl⟩ : syracuseStep 2590897 = 1943173) (by norm_num)
theorem B3454529 : Blo 2301435 3454529 := bstep (se 2 (by rfl) ⟨1295448, by rfl⟩ : syracuseStep 3454529 = 2590897) B2590897
theorem B2303019 : Blo 2301435 2303019 := bstep (se 1 (by rfl) ⟨1727264, by rfl⟩ : syracuseStep 2303019 = 3454529) B3454529
theorem B2459333 : Blo 2301435 2459333 := bbase (se 4 (by rfl) ⟨230562, by rfl⟩ : syracuseStep 2459333 = 461125) (by norm_num)
theorem B6558221 : Blo 2301435 6558221 := bstep (se 3 (by rfl) ⟨1229666, by rfl⟩ : syracuseStep 6558221 = 2459333) B2459333
theorem B4372147 : Blo 2301435 4372147 := bstep (se 1 (by rfl) ⟨3279110, by rfl⟩ : syracuseStep 4372147 = 6558221) B6558221
theorem B5829529 : Blo 2301435 5829529 := bstep (se 2 (by rfl) ⟨2186073, by rfl⟩ : syracuseStep 5829529 = 4372147) B4372147
theorem B7772705 : Blo 2301435 7772705 := bstep (se 2 (by rfl) ⟨2914764, by rfl⟩ : syracuseStep 7772705 = 5829529) B5829529
theorem B5181803 : Blo 2301435 5181803 := bstep (se 1 (by rfl) ⟨3886352, by rfl⟩ : syracuseStep 5181803 = 7772705) B7772705
theorem B3454535 : Blo 2301435 3454535 := bstep (se 1 (by rfl) ⟨2590901, by rfl⟩ : syracuseStep 3454535 = 5181803) B5181803
theorem B2303023 : Blo 2301435 2303023 := bstep (se 1 (by rfl) ⟨1727267, by rfl⟩ : syracuseStep 2303023 = 3454535) B3454535
theorem B3454541 : Blo 2301435 3454541 := bbase (se 3 (by rfl) ⟨647726, by rfl⟩ : syracuseStep 3454541 = 1295453) (by norm_num)
theorem B2303027 : Blo 2301435 2303027 := bstep (se 1 (by rfl) ⟨1727270, by rfl⟩ : syracuseStep 2303027 = 3454541) B3454541
theorem B5181821 : Blo 2301435 5181821 := bbase (se 3 (by rfl) ⟨971591, by rfl⟩ : syracuseStep 5181821 = 1943183) (by norm_num)
theorem B3454547 : Blo 2301435 3454547 := bstep (se 1 (by rfl) ⟨2590910, by rfl⟩ : syracuseStep 3454547 = 5181821) B5181821
theorem B2303031 : Blo 2301435 2303031 := bstep (se 1 (by rfl) ⟨1727273, by rfl⟩ : syracuseStep 2303031 = 3454547) B3454547
theorem B3886373 : Blo 2301435 3886373 := bbase (se 4 (by rfl) ⟨364347, by rfl⟩ : syracuseStep 3886373 = 728695) (by norm_num)
theorem B2590915 : Blo 2301435 2590915 := bstep (se 1 (by rfl) ⟨1943186, by rfl⟩ : syracuseStep 2590915 = 3886373) B3886373
theorem B3454553 : Blo 2301435 3454553 := bstep (se 2 (by rfl) ⟨1295457, by rfl⟩ : syracuseStep 3454553 = 2590915) B2590915
theorem B2303035 : Blo 2301435 2303035 := bstep (se 1 (by rfl) ⟨1727276, by rfl⟩ : syracuseStep 2303035 = 3454553) B3454553
theorem B3279133 : Blo 2301435 3279133 := bbase (se 3 (by rfl) ⟨614837, by rfl⟩ : syracuseStep 3279133 = 1229675) (by norm_num)
theorem B17488709 : Blo 2301435 17488709 := bstep (se 4 (by rfl) ⟨1639566, by rfl⟩ : syracuseStep 17488709 = 3279133) B3279133
theorem B11659139 : Blo 2301435 11659139 := bstep (se 1 (by rfl) ⟨8744354, by rfl⟩ : syracuseStep 11659139 = 17488709) B17488709
theorem B7772759 : Blo 2301435 7772759 := bstep (se 1 (by rfl) ⟨5829569, by rfl⟩ : syracuseStep 7772759 = 11659139) B11659139
theorem B5181839 : Blo 2301435 5181839 := bstep (se 1 (by rfl) ⟨3886379, by rfl⟩ : syracuseStep 5181839 = 7772759) B7772759
theorem B3454559 : Blo 2301435 3454559 := bstep (se 1 (by rfl) ⟨2590919, by rfl⟩ : syracuseStep 3454559 = 5181839) B5181839
theorem B2303039 : Blo 2301435 2303039 := bstep (se 1 (by rfl) ⟨1727279, by rfl⟩ : syracuseStep 2303039 = 3454559) B3454559
theorem B3454565 : Blo 2301435 3454565 := bbase (se 4 (by rfl) ⟨323865, by rfl⟩ : syracuseStep 3454565 = 647731) (by norm_num)
theorem B2303043 : Blo 2301435 2303043 := bstep (se 1 (by rfl) ⟨1727282, by rfl⟩ : syracuseStep 2303043 = 3454565) B3454565
theorem B4668941 : Blo 2301435 4668941 := bbase (se 3 (by rfl) ⟨875426, by rfl⟩ : syracuseStep 4668941 = 1750853) (by norm_num)
theorem B12450509 : Blo 2301435 12450509 := bstep (se 3 (by rfl) ⟨2334470, by rfl⟩ : syracuseStep 12450509 = 4668941) B4668941
theorem B8300339 : Blo 2301435 8300339 := bstep (se 1 (by rfl) ⟨6225254, by rfl⟩ : syracuseStep 8300339 = 12450509) B12450509
theorem B5533559 : Blo 2301435 5533559 := bstep (se 1 (by rfl) ⟨4150169, by rfl⟩ : syracuseStep 5533559 = 8300339) B8300339
theorem B3689039 : Blo 2301435 3689039 := bstep (se 1 (by rfl) ⟨2766779, by rfl⟩ : syracuseStep 3689039 = 5533559) B5533559
theorem B2459359 : Blo 2301435 2459359 := bstep (se 1 (by rfl) ⟨1844519, by rfl⟩ : syracuseStep 2459359 = 3689039) B3689039
theorem B3279145 : Blo 2301435 3279145 := bstep (se 2 (by rfl) ⟨1229679, by rfl⟩ : syracuseStep 3279145 = 2459359) B2459359
theorem B4372193 : Blo 2301435 4372193 := bstep (se 2 (by rfl) ⟨1639572, by rfl⟩ : syracuseStep 4372193 = 3279145) B3279145
theorem B2914795 : Blo 2301435 2914795 := bstep (se 1 (by rfl) ⟨2186096, by rfl⟩ : syracuseStep 2914795 = 4372193) B4372193
theorem B3886393 : Blo 2301435 3886393 := bstep (se 2 (by rfl) ⟨1457397, by rfl⟩ : syracuseStep 3886393 = 2914795) B2914795
theorem B5181857 : Blo 2301435 5181857 := bstep (se 2 (by rfl) ⟨1943196, by rfl⟩ : syracuseStep 5181857 = 3886393) B3886393
theorem B3454571 : Blo 2301435 3454571 := bstep (se 1 (by rfl) ⟨2590928, by rfl⟩ : syracuseStep 3454571 = 5181857) B5181857
theorem B2303047 : Blo 2301435 2303047 := bstep (se 1 (by rfl) ⟨1727285, by rfl⟩ : syracuseStep 2303047 = 3454571) B3454571
theorem B2590933 : Blo 2301435 2590933 := bbase (se 7 (by rfl) ⟨30362, by rfl⟩ : syracuseStep 2590933 = 60725) (by norm_num)
theorem B3454577 : Blo 2301435 3454577 := bstep (se 2 (by rfl) ⟨1295466, by rfl⟩ : syracuseStep 3454577 = 2590933) B2590933
theorem B2303051 : Blo 2301435 2303051 := bstep (se 1 (by rfl) ⟨1727288, by rfl⟩ : syracuseStep 2303051 = 3454577) B3454577
theorem B2914805 : Blo 2301435 2914805 := bbase (se 5 (by rfl) ⟨136631, by rfl⟩ : syracuseStep 2914805 = 273263) (by norm_num)
theorem B7772813 : Blo 2301435 7772813 := bstep (se 3 (by rfl) ⟨1457402, by rfl⟩ : syracuseStep 7772813 = 2914805) B2914805
theorem B5181875 : Blo 2301435 5181875 := bstep (se 1 (by rfl) ⟨3886406, by rfl⟩ : syracuseStep 5181875 = 7772813) B7772813
theorem B3454583 : Blo 2301435 3454583 := bstep (se 1 (by rfl) ⟨2590937, by rfl⟩ : syracuseStep 3454583 = 5181875) B5181875
theorem B2303055 : Blo 2301435 2303055 := bstep (se 1 (by rfl) ⟨1727291, by rfl⟩ : syracuseStep 2303055 = 3454583) B3454583
theorem B3454589 : Blo 2301435 3454589 := bbase (se 3 (by rfl) ⟨647735, by rfl⟩ : syracuseStep 3454589 = 1295471) (by norm_num)
theorem B2303059 : Blo 2301435 2303059 := bstep (se 1 (by rfl) ⟨1727294, by rfl⟩ : syracuseStep 2303059 = 3454589) B3454589
theorem B5181893 : Blo 2301435 5181893 := bbase (se 4 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 5181893 = 971605) (by norm_num)
theorem B3454595 : Blo 2301435 3454595 := bstep (se 1 (by rfl) ⟨2590946, by rfl⟩ : syracuseStep 3454595 = 5181893) B5181893
theorem B2303063 : Blo 2301435 2303063 := bstep (se 1 (by rfl) ⟨1727297, by rfl⟩ : syracuseStep 2303063 = 3454595) B3454595
theorem B4150205 : Blo 2301435 4150205 := bbase (se 3 (by rfl) ⟨778163, by rfl⟩ : syracuseStep 4150205 = 1556327) (by norm_num)
theorem B2766803 : Blo 2301435 2766803 := bstep (se 1 (by rfl) ⟨2075102, by rfl⟩ : syracuseStep 2766803 = 4150205) B4150205
theorem B7378141 : Blo 2301435 7378141 := bstep (se 3 (by rfl) ⟨1383401, by rfl⟩ : syracuseStep 7378141 = 2766803) B2766803
theorem B9837521 : Blo 2301435 9837521 := bstep (se 2 (by rfl) ⟨3689070, by rfl⟩ : syracuseStep 9837521 = 7378141) B7378141
theorem B6558347 : Blo 2301435 6558347 := bstep (se 1 (by rfl) ⟨4918760, by rfl⟩ : syracuseStep 6558347 = 9837521) B9837521
theorem B4372231 : Blo 2301435 4372231 := bstep (se 1 (by rfl) ⟨3279173, by rfl⟩ : syracuseStep 4372231 = 6558347) B6558347
theorem B5829641 : Blo 2301435 5829641 := bstep (se 2 (by rfl) ⟨2186115, by rfl⟩ : syracuseStep 5829641 = 4372231) B4372231
theorem B3886427 : Blo 2301435 3886427 := bstep (se 1 (by rfl) ⟨2914820, by rfl⟩ : syracuseStep 3886427 = 5829641) B5829641
theorem B2590951 : Blo 2301435 2590951 := bstep (se 1 (by rfl) ⟨1943213, by rfl⟩ : syracuseStep 2590951 = 3886427) B3886427
theorem B3454601 : Blo 2301435 3454601 := bstep (se 2 (by rfl) ⟨1295475, by rfl⟩ : syracuseStep 3454601 = 2590951) B2590951
theorem B2303067 : Blo 2301435 2303067 := bstep (se 1 (by rfl) ⟨1727300, by rfl⟩ : syracuseStep 2303067 = 3454601) B3454601
theorem B11659301 : Blo 2301435 11659301 := bbase (se 4 (by rfl) ⟨1093059, by rfl⟩ : syracuseStep 11659301 = 2186119) (by norm_num)
theorem B7772867 : Blo 2301435 7772867 := bstep (se 1 (by rfl) ⟨5829650, by rfl⟩ : syracuseStep 7772867 = 11659301) B11659301
theorem B5181911 : Blo 2301435 5181911 := bstep (se 1 (by rfl) ⟨3886433, by rfl⟩ : syracuseStep 5181911 = 7772867) B7772867
theorem B3454607 : Blo 2301435 3454607 := bstep (se 1 (by rfl) ⟨2590955, by rfl⟩ : syracuseStep 3454607 = 5181911) B5181911
theorem B2303071 : Blo 2301435 2303071 := bstep (se 1 (by rfl) ⟨1727303, by rfl⟩ : syracuseStep 2303071 = 3454607) B3454607
theorem B3454613 : Blo 2301435 3454613 := bbase (se 6 (by rfl) ⟨80967, by rfl⟩ : syracuseStep 3454613 = 161935) (by norm_num)
theorem B2303075 : Blo 2301435 2303075 := bstep (se 1 (by rfl) ⟨1727306, by rfl⟩ : syracuseStep 2303075 = 3454613) B3454613
theorem B2766817 : Blo 2301435 2766817 := bbase (se 2 (by rfl) ⟨1037556, by rfl⟩ : syracuseStep 2766817 = 2075113) (by norm_num)
theorem B14756357 : Blo 2301435 14756357 := bstep (se 4 (by rfl) ⟨1383408, by rfl⟩ : syracuseStep 14756357 = 2766817) B2766817
theorem B9837571 : Blo 2301435 9837571 := bstep (se 1 (by rfl) ⟨7378178, by rfl⟩ : syracuseStep 9837571 = 14756357) B14756357
theorem B13116761 : Blo 2301435 13116761 := bstep (se 2 (by rfl) ⟨4918785, by rfl⟩ : syracuseStep 13116761 = 9837571) B9837571
theorem B8744507 : Blo 2301435 8744507 := bstep (se 1 (by rfl) ⟨6558380, by rfl⟩ : syracuseStep 8744507 = 13116761) B13116761
theorem B5829671 : Blo 2301435 5829671 := bstep (se 1 (by rfl) ⟨4372253, by rfl⟩ : syracuseStep 5829671 = 8744507) B8744507
theorem B3886447 : Blo 2301435 3886447 := bstep (se 1 (by rfl) ⟨2914835, by rfl⟩ : syracuseStep 3886447 = 5829671) B5829671
theorem B5181929 : Blo 2301435 5181929 := bstep (se 2 (by rfl) ⟨1943223, by rfl⟩ : syracuseStep 5181929 = 3886447) B3886447
theorem B3454619 : Blo 2301435 3454619 := bstep (se 1 (by rfl) ⟨2590964, by rfl⟩ : syracuseStep 3454619 = 5181929) B5181929
theorem B2303079 : Blo 2301435 2303079 := bstep (se 1 (by rfl) ⟨1727309, by rfl⟩ : syracuseStep 2303079 = 3454619) B3454619
theorem B2590969 : Blo 2301435 2590969 := bbase (se 2 (by rfl) ⟨971613, by rfl⟩ : syracuseStep 2590969 = 1943227) (by norm_num)
theorem B3454625 : Blo 2301435 3454625 := bstep (se 2 (by rfl) ⟨1295484, by rfl⟩ : syracuseStep 3454625 = 2590969) B2590969
theorem B2303083 : Blo 2301435 2303083 := bstep (se 1 (by rfl) ⟨1727312, by rfl⟩ : syracuseStep 2303083 = 3454625) B3454625
theorem B9837605 : Blo 2301435 9837605 := bbase (se 4 (by rfl) ⟨922275, by rfl⟩ : syracuseStep 9837605 = 1844551) (by norm_num)
theorem B6558403 : Blo 2301435 6558403 := bstep (se 1 (by rfl) ⟨4918802, by rfl⟩ : syracuseStep 6558403 = 9837605) B9837605
theorem B8744537 : Blo 2301435 8744537 := bstep (se 2 (by rfl) ⟨3279201, by rfl⟩ : syracuseStep 8744537 = 6558403) B6558403
theorem B5829691 : Blo 2301435 5829691 := bstep (se 1 (by rfl) ⟨4372268, by rfl⟩ : syracuseStep 5829691 = 8744537) B8744537
theorem B7772921 : Blo 2301435 7772921 := bstep (se 2 (by rfl) ⟨2914845, by rfl⟩ : syracuseStep 7772921 = 5829691) B5829691
theorem B5181947 : Blo 2301435 5181947 := bstep (se 1 (by rfl) ⟨3886460, by rfl⟩ : syracuseStep 5181947 = 7772921) B7772921
theorem B3454631 : Blo 2301435 3454631 := bstep (se 1 (by rfl) ⟨2590973, by rfl⟩ : syracuseStep 3454631 = 5181947) B5181947
theorem B2303087 : Blo 2301435 2303087 := bstep (se 1 (by rfl) ⟨1727315, by rfl⟩ : syracuseStep 2303087 = 3454631) B3454631
theorem B3454637 : Blo 2301435 3454637 := bbase (se 3 (by rfl) ⟨647744, by rfl⟩ : syracuseStep 3454637 = 1295489) (by norm_num)
theorem B2303091 : Blo 2301435 2303091 := bstep (se 1 (by rfl) ⟨1727318, by rfl⟩ : syracuseStep 2303091 = 3454637) B3454637
theorem B5181965 : Blo 2301435 5181965 := bbase (se 3 (by rfl) ⟨971618, by rfl⟩ : syracuseStep 5181965 = 1943237) (by norm_num)
theorem B3454643 : Blo 2301435 3454643 := bstep (se 1 (by rfl) ⟨2590982, by rfl⟩ : syracuseStep 3454643 = 5181965) B5181965
theorem B2303095 : Blo 2301435 2303095 := bstep (se 1 (by rfl) ⟨1727321, by rfl⟩ : syracuseStep 2303095 = 3454643) B3454643
theorem B2914861 : Blo 2301435 2914861 := bbase (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) (by norm_num)
theorem B3886481 : Blo 2301435 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B2590987 : Blo 2301435 2590987 := bstep (se 1 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 2590987 = 3886481) B3886481
theorem B3454649 : Blo 2301435 3454649 := bstep (se 2 (by rfl) ⟨1295493, by rfl⟩ : syracuseStep 3454649 = 2590987) B2590987
theorem B2303099 : Blo 2301435 2303099 := bstep (se 1 (by rfl) ⟨1727324, by rfl⟩ : syracuseStep 2303099 = 3454649) B3454649
theorem B3323965 : Blo 2301435 3323965 := bbase (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) (by norm_num)
theorem B4431953 : Blo 2301435 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B11818541 : Blo 2301435 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B7879027 : Blo 2301435 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B10505369 : Blo 2301435 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B7003579 : Blo 2301435 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B9338105 : Blo 2301435 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B6225403 : Blo 2301435 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B8300537 : Blo 2301435 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B5533691 : Blo 2301435 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B14756509 : Blo 2301435 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B19675345 : Blo 2301435 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B26233793 : Blo 2301435 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B17489195 : Blo 2301435 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B11659463 : Blo 2301435 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B7772975 : Blo 2301435 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B5181983 : Blo 2301435 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B3454655 : Blo 2301435 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B2303103 : Blo 2301435 2303103 := bstep (se 1 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 2303103 = 3454655) B3454655
theorem B3454661 : Blo 2301435 3454661 := bbase (se 4 (by rfl) ⟨323874, by rfl⟩ : syracuseStep 3454661 = 647749) (by norm_num)
theorem B2303107 : Blo 2301435 2303107 := bstep (se 1 (by rfl) ⟨1727330, by rfl⟩ : syracuseStep 2303107 = 3454661) B3454661
theorem B3886501 : Blo 2301435 3886501 := bbase (se 4 (by rfl) ⟨364359, by rfl⟩ : syracuseStep 3886501 = 728719) (by norm_num)
theorem B5182001 : Blo 2301435 5182001 := bstep (se 2 (by rfl) ⟨1943250, by rfl⟩ : syracuseStep 5182001 = 3886501) B3886501
theorem B3454667 : Blo 2301435 3454667 := bstep (se 1 (by rfl) ⟨2591000, by rfl⟩ : syracuseStep 3454667 = 5182001) B5182001
theorem B2303111 : Blo 2301435 2303111 := bstep (se 1 (by rfl) ⟨1727333, by rfl⟩ : syracuseStep 2303111 = 3454667) B3454667
theorem B2591005 : Blo 2301435 2591005 := bbase (se 3 (by rfl) ⟨485813, by rfl⟩ : syracuseStep 2591005 = 971627) (by norm_num)
theorem B3454673 : Blo 2301435 3454673 := bstep (se 2 (by rfl) ⟨1295502, by rfl⟩ : syracuseStep 3454673 = 2591005) B2591005
theorem B2303115 : Blo 2301435 2303115 := bstep (se 1 (by rfl) ⟨1727336, by rfl⟩ : syracuseStep 2303115 = 3454673) B3454673
theorem B7773029 : Blo 2301435 7773029 := bbase (se 4 (by rfl) ⟨728721, by rfl⟩ : syracuseStep 7773029 = 1457443) (by norm_num)
theorem B5182019 : Blo 2301435 5182019 := bstep (se 1 (by rfl) ⟨3886514, by rfl⟩ : syracuseStep 5182019 = 7773029) B7773029
theorem B3454679 : Blo 2301435 3454679 := bstep (se 1 (by rfl) ⟨2591009, by rfl⟩ : syracuseStep 3454679 = 5182019) B5182019
theorem B2303119 : Blo 2301435 2303119 := bstep (se 1 (by rfl) ⟨1727339, by rfl⟩ : syracuseStep 2303119 = 3454679) B3454679
theorem B3454685 : Blo 2301435 3454685 := bbase (se 3 (by rfl) ⟨647753, by rfl⟩ : syracuseStep 3454685 = 1295507) (by norm_num)
theorem B2303123 : Blo 2301435 2303123 := bstep (se 1 (by rfl) ⟨1727342, by rfl⟩ : syracuseStep 2303123 = 3454685) B3454685
theorem B5182037 : Blo 2301435 5182037 := bbase (se 8 (by rfl) ⟨30363, by rfl⟩ : syracuseStep 5182037 = 60727) (by norm_num)
theorem B3454691 : Blo 2301435 3454691 := bstep (se 1 (by rfl) ⟨2591018, by rfl⟩ : syracuseStep 3454691 = 5182037) B5182037
theorem B2303127 : Blo 2301435 2303127 := bstep (se 1 (by rfl) ⟨1727345, by rfl⟩ : syracuseStep 2303127 = 3454691) B3454691
theorem B3689173 : Blo 2301435 3689173 := bbase (se 7 (by rfl) ⟨43232, by rfl⟩ : syracuseStep 3689173 = 86465) (by norm_num)
theorem B4918897 : Blo 2301435 4918897 := bstep (se 2 (by rfl) ⟨1844586, by rfl⟩ : syracuseStep 4918897 = 3689173) B3689173
theorem B6558529 : Blo 2301435 6558529 := bstep (se 2 (by rfl) ⟨2459448, by rfl⟩ : syracuseStep 6558529 = 4918897) B4918897
theorem B8744705 : Blo 2301435 8744705 := bstep (se 2 (by rfl) ⟨3279264, by rfl⟩ : syracuseStep 8744705 = 6558529) B6558529
theorem B5829803 : Blo 2301435 5829803 := bstep (se 1 (by rfl) ⟨4372352, by rfl⟩ : syracuseStep 5829803 = 8744705) B8744705
theorem B3886535 : Blo 2301435 3886535 := bstep (se 1 (by rfl) ⟨2914901, by rfl⟩ : syracuseStep 3886535 = 5829803) B5829803
theorem B2591023 : Blo 2301435 2591023 := bstep (se 1 (by rfl) ⟨1943267, by rfl⟩ : syracuseStep 2591023 = 3886535) B3886535
theorem B3454697 : Blo 2301435 3454697 := bstep (se 2 (by rfl) ⟨1295511, by rfl⟩ : syracuseStep 3454697 = 2591023) B2591023
theorem B2303131 : Blo 2301435 2303131 := bstep (se 1 (by rfl) ⟨1727348, by rfl⟩ : syracuseStep 2303131 = 3454697) B3454697
theorem B29513429 : Blo 2301435 29513429 := bbase (se 7 (by rfl) ⟨345860, by rfl⟩ : syracuseStep 29513429 = 691721) (by norm_num)
theorem B19675619 : Blo 2301435 19675619 := bstep (se 1 (by rfl) ⟨14756714, by rfl⟩ : syracuseStep 19675619 = 29513429) B29513429
theorem B13117079 : Blo 2301435 13117079 := bstep (se 1 (by rfl) ⟨9837809, by rfl⟩ : syracuseStep 13117079 = 19675619) B19675619
theorem B8744719 : Blo 2301435 8744719 := bstep (se 1 (by rfl) ⟨6558539, by rfl⟩ : syracuseStep 8744719 = 13117079) B13117079
theorem B11659625 : Blo 2301435 11659625 := bstep (se 2 (by rfl) ⟨4372359, by rfl⟩ : syracuseStep 11659625 = 8744719) B8744719
theorem B7773083 : Blo 2301435 7773083 := bstep (se 1 (by rfl) ⟨5829812, by rfl⟩ : syracuseStep 7773083 = 11659625) B11659625
theorem B5182055 : Blo 2301435 5182055 := bstep (se 1 (by rfl) ⟨3886541, by rfl⟩ : syracuseStep 5182055 = 7773083) B7773083
theorem B3454703 : Blo 2301435 3454703 := bstep (se 1 (by rfl) ⟨2591027, by rfl⟩ : syracuseStep 3454703 = 5182055) B5182055
theorem B2303135 : Blo 2301435 2303135 := bstep (se 1 (by rfl) ⟨1727351, by rfl⟩ : syracuseStep 2303135 = 3454703) B3454703
theorem B3454709 : Blo 2301435 3454709 := bbase (se 5 (by rfl) ⟨161939, by rfl⟩ : syracuseStep 3454709 = 323879) (by norm_num)
theorem B2303139 : Blo 2301435 2303139 := bstep (se 1 (by rfl) ⟨1727354, by rfl⟩ : syracuseStep 2303139 = 3454709) B3454709
theorem B9837845 : Blo 2301435 9837845 := bbase (se 6 (by rfl) ⟨230574, by rfl⟩ : syracuseStep 9837845 = 461149) (by norm_num)
theorem B6558563 : Blo 2301435 6558563 := bstep (se 1 (by rfl) ⟨4918922, by rfl⟩ : syracuseStep 6558563 = 9837845) B9837845
theorem B4372375 : Blo 2301435 4372375 := bstep (se 1 (by rfl) ⟨3279281, by rfl⟩ : syracuseStep 4372375 = 6558563) B6558563
theorem B5829833 : Blo 2301435 5829833 := bstep (se 2 (by rfl) ⟨2186187, by rfl⟩ : syracuseStep 5829833 = 4372375) B4372375
theorem B3886555 : Blo 2301435 3886555 := bstep (se 1 (by rfl) ⟨2914916, by rfl⟩ : syracuseStep 3886555 = 5829833) B5829833
theorem B5182073 : Blo 2301435 5182073 := bstep (se 2 (by rfl) ⟨1943277, by rfl⟩ : syracuseStep 5182073 = 3886555) B3886555
theorem B3454715 : Blo 2301435 3454715 := bstep (se 1 (by rfl) ⟨2591036, by rfl⟩ : syracuseStep 3454715 = 5182073) B5182073
theorem B2303143 : Blo 2301435 2303143 := bstep (se 1 (by rfl) ⟨1727357, by rfl⟩ : syracuseStep 2303143 = 3454715) B3454715
theorem B2591041 : Blo 2301435 2591041 := bbase (se 2 (by rfl) ⟨971640, by rfl⟩ : syracuseStep 2591041 = 1943281) (by norm_num)
theorem B3454721 : Blo 2301435 3454721 := bstep (se 2 (by rfl) ⟨1295520, by rfl⟩ : syracuseStep 3454721 = 2591041) B2591041
theorem B2303147 : Blo 2301435 2303147 := bstep (se 1 (by rfl) ⟨1727360, by rfl⟩ : syracuseStep 2303147 = 3454721) B3454721
theorem B5829853 : Blo 2301435 5829853 := bbase (se 3 (by rfl) ⟨1093097, by rfl⟩ : syracuseStep 5829853 = 2186195) (by norm_num)
theorem B7773137 : Blo 2301435 7773137 := bstep (se 2 (by rfl) ⟨2914926, by rfl⟩ : syracuseStep 7773137 = 5829853) B5829853
theorem B5182091 : Blo 2301435 5182091 := bstep (se 1 (by rfl) ⟨3886568, by rfl⟩ : syracuseStep 5182091 = 7773137) B7773137
theorem B3454727 : Blo 2301435 3454727 := bstep (se 1 (by rfl) ⟨2591045, by rfl⟩ : syracuseStep 3454727 = 5182091) B5182091
theorem B2303151 : Blo 2301435 2303151 := bstep (se 1 (by rfl) ⟨1727363, by rfl⟩ : syracuseStep 2303151 = 3454727) B3454727
theorem B3454733 : Blo 2301435 3454733 := bbase (se 3 (by rfl) ⟨647762, by rfl⟩ : syracuseStep 3454733 = 1295525) (by norm_num)
theorem B2303155 : Blo 2301435 2303155 := bstep (se 1 (by rfl) ⟨1727366, by rfl⟩ : syracuseStep 2303155 = 3454733) B3454733
theorem B5182109 : Blo 2301435 5182109 := bbase (se 3 (by rfl) ⟨971645, by rfl⟩ : syracuseStep 5182109 = 1943291) (by norm_num)
theorem B3454739 : Blo 2301435 3454739 := bstep (se 1 (by rfl) ⟨2591054, by rfl⟩ : syracuseStep 3454739 = 5182109) B5182109
theorem B2303159 : Blo 2301435 2303159 := bstep (se 1 (by rfl) ⟨1727369, by rfl⟩ : syracuseStep 2303159 = 3454739) B3454739
theorem B3886589 : Blo 2301435 3886589 := bbase (se 3 (by rfl) ⟨728735, by rfl⟩ : syracuseStep 3886589 = 1457471) (by norm_num)
theorem B2591059 : Blo 2301435 2591059 := bstep (se 1 (by rfl) ⟨1943294, by rfl⟩ : syracuseStep 2591059 = 3886589) B3886589
theorem B3454745 : Blo 2301435 3454745 := bstep (se 2 (by rfl) ⟨1295529, by rfl⟩ : syracuseStep 3454745 = 2591059) B2591059
theorem B2303163 : Blo 2301435 2303163 := bstep (se 1 (by rfl) ⟨1727372, by rfl⟩ : syracuseStep 2303163 = 3454745) B3454745
theorem B4918973 : Blo 2301435 4918973 := bbase (se 3 (by rfl) ⟨922307, by rfl⟩ : syracuseStep 4918973 = 1844615) (by norm_num)
theorem B13117261 : Blo 2301435 13117261 := bstep (se 3 (by rfl) ⟨2459486, by rfl⟩ : syracuseStep 13117261 = 4918973) B4918973
theorem B17489681 : Blo 2301435 17489681 := bstep (se 2 (by rfl) ⟨6558630, by rfl⟩ : syracuseStep 17489681 = 13117261) B13117261
theorem B11659787 : Blo 2301435 11659787 := bstep (se 1 (by rfl) ⟨8744840, by rfl⟩ : syracuseStep 11659787 = 17489681) B17489681
theorem B7773191 : Blo 2301435 7773191 := bstep (se 1 (by rfl) ⟨5829893, by rfl⟩ : syracuseStep 7773191 = 11659787) B11659787
theorem B5182127 : Blo 2301435 5182127 := bstep (se 1 (by rfl) ⟨3886595, by rfl⟩ : syracuseStep 5182127 = 7773191) B7773191
theorem B3454751 : Blo 2301435 3454751 := bstep (se 1 (by rfl) ⟨2591063, by rfl⟩ : syracuseStep 3454751 = 5182127) B5182127
theorem B2303167 : Blo 2301435 2303167 := bstep (se 1 (by rfl) ⟨1727375, by rfl⟩ : syracuseStep 2303167 = 3454751) B3454751
theorem B3454757 : Blo 2301435 3454757 := bbase (se 4 (by rfl) ⟨323883, by rfl⟩ : syracuseStep 3454757 = 647767) (by norm_num)
theorem B2303171 : Blo 2301435 2303171 := bstep (se 1 (by rfl) ⟨1727378, by rfl⟩ : syracuseStep 2303171 = 3454757) B3454757
theorem B2914957 : Blo 2301435 2914957 := bbase (se 3 (by rfl) ⟨546554, by rfl⟩ : syracuseStep 2914957 = 1093109) (by norm_num)
theorem B3886609 : Blo 2301435 3886609 := bstep (se 2 (by rfl) ⟨1457478, by rfl⟩ : syracuseStep 3886609 = 2914957) B2914957
theorem B5182145 : Blo 2301435 5182145 := bstep (se 2 (by rfl) ⟨1943304, by rfl⟩ : syracuseStep 5182145 = 3886609) B3886609
theorem B3454763 : Blo 2301435 3454763 := bstep (se 1 (by rfl) ⟨2591072, by rfl⟩ : syracuseStep 3454763 = 5182145) B5182145
theorem B2303175 : Blo 2301435 2303175 := bstep (se 1 (by rfl) ⟨1727381, by rfl⟩ : syracuseStep 2303175 = 3454763) B3454763
theorem B2591077 : Blo 2301435 2591077 := bbase (se 4 (by rfl) ⟨242913, by rfl⟩ : syracuseStep 2591077 = 485827) (by norm_num)
theorem B3454769 : Blo 2301435 3454769 := bstep (se 2 (by rfl) ⟨1295538, by rfl⟩ : syracuseStep 3454769 = 2591077) B2591077
theorem B2303179 : Blo 2301435 2303179 := bstep (se 1 (by rfl) ⟨1727384, by rfl⟩ : syracuseStep 2303179 = 3454769) B3454769
theorem B6558677 : Blo 2301435 6558677 := bbase (se 7 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 6558677 = 153719) (by norm_num)
theorem B4372451 : Blo 2301435 4372451 := bstep (se 1 (by rfl) ⟨3279338, by rfl⟩ : syracuseStep 4372451 = 6558677) B6558677
theorem B2914967 : Blo 2301435 2914967 := bstep (se 1 (by rfl) ⟨2186225, by rfl⟩ : syracuseStep 2914967 = 4372451) B4372451
theorem B7773245 : Blo 2301435 7773245 := bstep (se 3 (by rfl) ⟨1457483, by rfl⟩ : syracuseStep 7773245 = 2914967) B2914967
theorem B5182163 : Blo 2301435 5182163 := bstep (se 1 (by rfl) ⟨3886622, by rfl⟩ : syracuseStep 5182163 = 7773245) B7773245
theorem B3454775 : Blo 2301435 3454775 := bstep (se 1 (by rfl) ⟨2591081, by rfl⟩ : syracuseStep 3454775 = 5182163) B5182163
theorem B2303183 : Blo 2301435 2303183 := bstep (se 1 (by rfl) ⟨1727387, by rfl⟩ : syracuseStep 2303183 = 3454775) B3454775
theorem B3454781 : Blo 2301435 3454781 := bbase (se 3 (by rfl) ⟨647771, by rfl⟩ : syracuseStep 3454781 = 1295543) (by norm_num)
theorem B2303187 : Blo 2301435 2303187 := bstep (se 1 (by rfl) ⟨1727390, by rfl⟩ : syracuseStep 2303187 = 3454781) B3454781
theorem B5182181 : Blo 2301435 5182181 := bbase (se 4 (by rfl) ⟨485829, by rfl⟩ : syracuseStep 5182181 = 971659) (by norm_num)
theorem B3454787 : Blo 2301435 3454787 := bstep (se 1 (by rfl) ⟨2591090, by rfl⟩ : syracuseStep 3454787 = 5182181) B5182181
theorem B2303191 : Blo 2301435 2303191 := bstep (se 1 (by rfl) ⟨1727393, by rfl⟩ : syracuseStep 2303191 = 3454787) B3454787
theorem B5829965 : Blo 2301435 5829965 := bbase (se 3 (by rfl) ⟨1093118, by rfl⟩ : syracuseStep 5829965 = 2186237) (by norm_num)
theorem B3886643 : Blo 2301435 3886643 := bstep (se 1 (by rfl) ⟨2914982, by rfl⟩ : syracuseStep 3886643 = 5829965) B5829965
theorem B2591095 : Blo 2301435 2591095 := bstep (se 1 (by rfl) ⟨1943321, by rfl⟩ : syracuseStep 2591095 = 3886643) B3886643
theorem B3454793 : Blo 2301435 3454793 := bstep (se 2 (by rfl) ⟨1295547, by rfl⟩ : syracuseStep 3454793 = 2591095) B2591095
theorem B2303195 : Blo 2301435 2303195 := bstep (se 1 (by rfl) ⟨1727396, by rfl⟩ : syracuseStep 2303195 = 3454793) B3454793
theorem B2459521 : Blo 2301435 2459521 := bbase (se 2 (by rfl) ⟨922320, by rfl⟩ : syracuseStep 2459521 = 1844641) (by norm_num)
theorem B3279361 : Blo 2301435 3279361 := bstep (se 2 (by rfl) ⟨1229760, by rfl⟩ : syracuseStep 3279361 = 2459521) B2459521
theorem B4372481 : Blo 2301435 4372481 := bstep (se 2 (by rfl) ⟨1639680, by rfl⟩ : syracuseStep 4372481 = 3279361) B3279361
theorem B11659949 : Blo 2301435 11659949 := bstep (se 3 (by rfl) ⟨2186240, by rfl⟩ : syracuseStep 11659949 = 4372481) B4372481
theorem B7773299 : Blo 2301435 7773299 := bstep (se 1 (by rfl) ⟨5829974, by rfl⟩ : syracuseStep 7773299 = 11659949) B11659949
theorem B5182199 : Blo 2301435 5182199 := bstep (se 1 (by rfl) ⟨3886649, by rfl⟩ : syracuseStep 5182199 = 7773299) B7773299
theorem B3454799 : Blo 2301435 3454799 := bstep (se 1 (by rfl) ⟨2591099, by rfl⟩ : syracuseStep 3454799 = 5182199) B5182199
theorem B2303199 : Blo 2301435 2303199 := bstep (se 1 (by rfl) ⟨1727399, by rfl⟩ : syracuseStep 2303199 = 3454799) B3454799
theorem B3454805 : Blo 2301435 3454805 := bbase (se 9 (by rfl) ⟨10121, by rfl⟩ : syracuseStep 3454805 = 20243) (by norm_num)
theorem B2303203 : Blo 2301435 2303203 := bstep (se 1 (by rfl) ⟨1727402, by rfl⟩ : syracuseStep 2303203 = 3454805) B3454805
theorem B3501949 : Blo 2301435 3501949 := bbase (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) (by norm_num)
theorem B4669265 : Blo 2301435 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B3112843 : Blo 2301435 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B4150457 : Blo 2301435 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B2766971 : Blo 2301435 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B7378589 : Blo 2301435 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B4919059 : Blo 2301435 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B6558745 : Blo 2301435 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B8744993 : Blo 2301435 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B5829995 : Blo 2301435 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B3886663 : Blo 2301435 3886663 := bstep (se 1 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 3886663 = 5829995) B5829995
theorem B5182217 : Blo 2301435 5182217 := bstep (se 2 (by rfl) ⟨1943331, by rfl⟩ : syracuseStep 5182217 = 3886663) B3886663
theorem B3454811 : Blo 2301435 3454811 := bstep (se 1 (by rfl) ⟨2591108, by rfl⟩ : syracuseStep 3454811 = 5182217) B5182217
theorem B2303207 : Blo 2301435 2303207 := bstep (se 1 (by rfl) ⟨1727405, by rfl⟩ : syracuseStep 2303207 = 3454811) B3454811
theorem B2591113 : Blo 2301435 2591113 := bbase (se 2 (by rfl) ⟨971667, by rfl⟩ : syracuseStep 2591113 = 1943335) (by norm_num)
theorem B3454817 : Blo 2301435 3454817 := bstep (se 2 (by rfl) ⟨1295556, by rfl⟩ : syracuseStep 3454817 = 2591113) B2591113
theorem B2303211 : Blo 2301435 2303211 := bstep (se 1 (by rfl) ⟨1727408, by rfl⟩ : syracuseStep 2303211 = 3454817) B3454817
theorem B23638229 : Blo 2301435 23638229 := bbase (se 7 (by rfl) ⟨277010, by rfl⟩ : syracuseStep 23638229 = 554021) (by norm_num)
theorem B15758819 : Blo 2301435 15758819 := bstep (se 1 (by rfl) ⟨11819114, by rfl⟩ : syracuseStep 15758819 = 23638229) B23638229
theorem B10505879 : Blo 2301435 10505879 := bstep (se 1 (by rfl) ⟨7879409, by rfl⟩ : syracuseStep 10505879 = 15758819) B15758819
theorem B7003919 : Blo 2301435 7003919 := bstep (se 1 (by rfl) ⟨5252939, by rfl⟩ : syracuseStep 7003919 = 10505879) B10505879
theorem B18677117 : Blo 2301435 18677117 := bstep (se 3 (by rfl) ⟨3501959, by rfl⟩ : syracuseStep 18677117 = 7003919) B7003919
theorem B12451411 : Blo 2301435 12451411 := bstep (se 1 (by rfl) ⟨9338558, by rfl⟩ : syracuseStep 12451411 = 18677117) B18677117
theorem B66407525 : Blo 2301435 66407525 := bstep (se 4 (by rfl) ⟨6225705, by rfl⟩ : syracuseStep 66407525 = 12451411) B12451411
theorem B44271683 : Blo 2301435 44271683 := bstep (se 1 (by rfl) ⟨33203762, by rfl⟩ : syracuseStep 44271683 = 66407525) B66407525
theorem B29514455 : Blo 2301435 29514455 := bstep (se 1 (by rfl) ⟨22135841, by rfl⟩ : syracuseStep 29514455 = 44271683) B44271683
theorem B19676303 : Blo 2301435 19676303 := bstep (se 1 (by rfl) ⟨14757227, by rfl⟩ : syracuseStep 19676303 = 29514455) B29514455
theorem B13117535 : Blo 2301435 13117535 := bstep (se 1 (by rfl) ⟨9838151, by rfl⟩ : syracuseStep 13117535 = 19676303) B19676303
theorem B8745023 : Blo 2301435 8745023 := bstep (se 1 (by rfl) ⟨6558767, by rfl⟩ : syracuseStep 8745023 = 13117535) B13117535
theorem B5830015 : Blo 2301435 5830015 := bstep (se 1 (by rfl) ⟨4372511, by rfl⟩ : syracuseStep 5830015 = 8745023) B8745023
theorem B7773353 : Blo 2301435 7773353 := bstep (se 2 (by rfl) ⟨2915007, by rfl⟩ : syracuseStep 7773353 = 5830015) B5830015
theorem B5182235 : Blo 2301435 5182235 := bstep (se 1 (by rfl) ⟨3886676, by rfl⟩ : syracuseStep 5182235 = 7773353) B7773353
theorem B3454823 : Blo 2301435 3454823 := bstep (se 1 (by rfl) ⟨2591117, by rfl⟩ : syracuseStep 3454823 = 5182235) B5182235
theorem B2303215 : Blo 2301435 2303215 := bstep (se 1 (by rfl) ⟨1727411, by rfl⟩ : syracuseStep 2303215 = 3454823) B3454823
theorem B3454829 : Blo 2301435 3454829 := bbase (se 3 (by rfl) ⟨647780, by rfl⟩ : syracuseStep 3454829 = 1295561) (by norm_num)
theorem B2303219 : Blo 2301435 2303219 := bstep (se 1 (by rfl) ⟨1727414, by rfl⟩ : syracuseStep 2303219 = 3454829) B3454829
theorem B5182253 : Blo 2301435 5182253 := bbase (se 3 (by rfl) ⟨971672, by rfl⟩ : syracuseStep 5182253 = 1943345) (by norm_num)
theorem B3454835 : Blo 2301435 3454835 := bstep (se 1 (by rfl) ⟨2591126, by rfl⟩ : syracuseStep 3454835 = 5182253) B5182253
theorem B2303223 : Blo 2301435 2303223 := bstep (se 1 (by rfl) ⟨1727417, by rfl⟩ : syracuseStep 2303223 = 3454835) B3454835
theorem B2493109 : Blo 2301435 2493109 := bbase (se 5 (by rfl) ⟨116864, by rfl⟩ : syracuseStep 2493109 = 233729) (by norm_num)
theorem B13296581 : Blo 2301435 13296581 := bstep (se 4 (by rfl) ⟨1246554, by rfl⟩ : syracuseStep 13296581 = 2493109) B2493109
theorem B8864387 : Blo 2301435 8864387 := bstep (se 1 (by rfl) ⟨6648290, by rfl⟩ : syracuseStep 8864387 = 13296581) B13296581
theorem B5909591 : Blo 2301435 5909591 := bstep (se 1 (by rfl) ⟨4432193, by rfl⟩ : syracuseStep 5909591 = 8864387) B8864387
theorem B3939727 : Blo 2301435 3939727 := bstep (se 1 (by rfl) ⟨2954795, by rfl⟩ : syracuseStep 3939727 = 5909591) B5909591
theorem B5252969 : Blo 2301435 5252969 := bstep (se 2 (by rfl) ⟨1969863, by rfl⟩ : syracuseStep 5252969 = 3939727) B3939727
theorem B14007917 : Blo 2301435 14007917 := bstep (se 3 (by rfl) ⟨2626484, by rfl⟩ : syracuseStep 14007917 = 5252969) B5252969
theorem B9338611 : Blo 2301435 9338611 := bstep (se 1 (by rfl) ⟨7003958, by rfl⟩ : syracuseStep 9338611 = 14007917) B14007917
theorem B12451481 : Blo 2301435 12451481 := bstep (se 2 (by rfl) ⟨4669305, by rfl⟩ : syracuseStep 12451481 = 9338611) B9338611
theorem B8300987 : Blo 2301435 8300987 := bstep (se 1 (by rfl) ⟨6225740, by rfl⟩ : syracuseStep 8300987 = 12451481) B12451481
theorem B5533991 : Blo 2301435 5533991 := bstep (se 1 (by rfl) ⟨4150493, by rfl⟩ : syracuseStep 5533991 = 8300987) B8300987
theorem B3689327 : Blo 2301435 3689327 := bstep (se 1 (by rfl) ⟨2766995, by rfl⟩ : syracuseStep 3689327 = 5533991) B5533991
theorem B9838205 : Blo 2301435 9838205 := bstep (se 3 (by rfl) ⟨1844663, by rfl⟩ : syracuseStep 9838205 = 3689327) B3689327
theorem B6558803 : Blo 2301435 6558803 := bstep (se 1 (by rfl) ⟨4919102, by rfl⟩ : syracuseStep 6558803 = 9838205) B9838205
theorem B4372535 : Blo 2301435 4372535 := bstep (se 1 (by rfl) ⟨3279401, by rfl⟩ : syracuseStep 4372535 = 6558803) B6558803
theorem B2915023 : Blo 2301435 2915023 := bstep (se 1 (by rfl) ⟨2186267, by rfl⟩ : syracuseStep 2915023 = 4372535) B4372535
theorem B3886697 : Blo 2301435 3886697 := bstep (se 2 (by rfl) ⟨1457511, by rfl⟩ : syracuseStep 3886697 = 2915023) B2915023
theorem B2591131 : Blo 2301435 2591131 := bstep (se 1 (by rfl) ⟨1943348, by rfl⟩ : syracuseStep 2591131 = 3886697) B3886697
theorem B3454841 : Blo 2301435 3454841 := bstep (se 2 (by rfl) ⟨1295565, by rfl⟩ : syracuseStep 3454841 = 2591131) B2591131
theorem B2303227 : Blo 2301435 2303227 := bstep (se 1 (by rfl) ⟨1727420, by rfl⟩ : syracuseStep 2303227 = 3454841) B3454841
theorem B6225749 : Blo 2301435 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B4150499 : Blo 2301435 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B11067997 : Blo 2301435 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B14757329 : Blo 2301435 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B39352877 : Blo 2301435 39352877 := bstep (se 3 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 39352877 = 14757329) B14757329
theorem B26235251 : Blo 2301435 26235251 := bstep (se 1 (by rfl) ⟨19676438, by rfl⟩ : syracuseStep 26235251 = 39352877) B39352877
theorem B17490167 : Blo 2301435 17490167 := bstep (se 1 (by rfl) ⟨13117625, by rfl⟩ : syracuseStep 17490167 = 26235251) B26235251
theorem B11660111 : Blo 2301435 11660111 := bstep (se 1 (by rfl) ⟨8745083, by rfl⟩ : syracuseStep 11660111 = 17490167) B17490167
theorem B7773407 : Blo 2301435 7773407 := bstep (se 1 (by rfl) ⟨5830055, by rfl⟩ : syracuseStep 7773407 = 11660111) B11660111
theorem B5182271 : Blo 2301435 5182271 := bstep (se 1 (by rfl) ⟨3886703, by rfl⟩ : syracuseStep 5182271 = 7773407) B7773407
theorem B3454847 : Blo 2301435 3454847 := bstep (se 1 (by rfl) ⟨2591135, by rfl⟩ : syracuseStep 3454847 = 5182271) B5182271
theorem B2303231 : Blo 2301435 2303231 := bstep (se 1 (by rfl) ⟨1727423, by rfl⟩ : syracuseStep 2303231 = 3454847) B3454847
theorem B3454853 : Blo 2301435 3454853 := bbase (se 4 (by rfl) ⟨323892, by rfl⟩ : syracuseStep 3454853 = 647785) (by norm_num)
theorem B2303235 : Blo 2301435 2303235 := bstep (se 1 (by rfl) ⟨1727426, by rfl⟩ : syracuseStep 2303235 = 3454853) B3454853
theorem B3886717 : Blo 2301435 3886717 := bbase (se 3 (by rfl) ⟨728759, by rfl⟩ : syracuseStep 3886717 = 1457519) (by norm_num)
theorem B5182289 : Blo 2301435 5182289 := bstep (se 2 (by rfl) ⟨1943358, by rfl⟩ : syracuseStep 5182289 = 3886717) B3886717
theorem B3454859 : Blo 2301435 3454859 := bstep (se 1 (by rfl) ⟨2591144, by rfl⟩ : syracuseStep 3454859 = 5182289) B5182289
theorem B2303239 : Blo 2301435 2303239 := bstep (se 1 (by rfl) ⟨1727429, by rfl⟩ : syracuseStep 2303239 = 3454859) B3454859
theorem B2591149 : Blo 2301435 2591149 := bbase (se 3 (by rfl) ⟨485840, by rfl⟩ : syracuseStep 2591149 = 971681) (by norm_num)
theorem B3454865 : Blo 2301435 3454865 := bstep (se 2 (by rfl) ⟨1295574, by rfl⟩ : syracuseStep 3454865 = 2591149) B2591149
theorem B2303243 : Blo 2301435 2303243 := bstep (se 1 (by rfl) ⟨1727432, by rfl⟩ : syracuseStep 2303243 = 3454865) B3454865
theorem B7773461 : Blo 2301435 7773461 := bbase (se 6 (by rfl) ⟨182190, by rfl⟩ : syracuseStep 7773461 = 364381) (by norm_num)
theorem B5182307 : Blo 2301435 5182307 := bstep (se 1 (by rfl) ⟨3886730, by rfl⟩ : syracuseStep 5182307 = 7773461) B7773461
theorem B3454871 : Blo 2301435 3454871 := bstep (se 1 (by rfl) ⟨2591153, by rfl⟩ : syracuseStep 3454871 = 5182307) B5182307
theorem B2303247 : Blo 2301435 2303247 := bstep (se 1 (by rfl) ⟨1727435, by rfl⟩ : syracuseStep 2303247 = 3454871) B3454871
theorem B3454877 : Blo 2301435 3454877 := bbase (se 3 (by rfl) ⟨647789, by rfl⟩ : syracuseStep 3454877 = 1295579) (by norm_num)
theorem B2303251 : Blo 2301435 2303251 := bstep (se 1 (by rfl) ⟨1727438, by rfl⟩ : syracuseStep 2303251 = 3454877) B3454877
theorem B5182325 : Blo 2301435 5182325 := bbase (se 5 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 5182325 = 485843) (by norm_num)
theorem B3454883 : Blo 2301435 3454883 := bstep (se 1 (by rfl) ⟨2591162, by rfl⟩ : syracuseStep 3454883 = 5182325) B5182325
theorem B2303255 : Blo 2301435 2303255 := bstep (se 1 (by rfl) ⟨1727441, by rfl⟩ : syracuseStep 2303255 = 3454883) B3454883
theorem B3939781 : Blo 2301435 3939781 := bbase (se 4 (by rfl) ⟨369354, by rfl⟩ : syracuseStep 3939781 = 738709) (by norm_num)
theorem B5253041 : Blo 2301435 5253041 := bstep (se 2 (by rfl) ⟨1969890, by rfl⟩ : syracuseStep 5253041 = 3939781) B3939781
theorem B3502027 : Blo 2301435 3502027 := bstep (se 1 (by rfl) ⟨2626520, by rfl⟩ : syracuseStep 3502027 = 5253041) B5253041
theorem B4669369 : Blo 2301435 4669369 := bstep (se 2 (by rfl) ⟨1751013, by rfl⟩ : syracuseStep 4669369 = 3502027) B3502027
theorem B24903301 : Blo 2301435 24903301 := bstep (se 4 (by rfl) ⟨2334684, by rfl⟩ : syracuseStep 24903301 = 4669369) B4669369
theorem B33204401 : Blo 2301435 33204401 := bstep (se 2 (by rfl) ⟨12451650, by rfl⟩ : syracuseStep 33204401 = 24903301) B24903301
theorem B22136267 : Blo 2301435 22136267 := bstep (se 1 (by rfl) ⟨16602200, by rfl⟩ : syracuseStep 22136267 = 33204401) B33204401
theorem B14757511 : Blo 2301435 14757511 := bstep (se 1 (by rfl) ⟨11068133, by rfl⟩ : syracuseStep 14757511 = 22136267) B22136267
theorem B19676681 : Blo 2301435 19676681 := bstep (se 2 (by rfl) ⟨7378755, by rfl⟩ : syracuseStep 19676681 = 14757511) B14757511
theorem B13117787 : Blo 2301435 13117787 := bstep (se 1 (by rfl) ⟨9838340, by rfl⟩ : syracuseStep 13117787 = 19676681) B19676681
theorem B8745191 : Blo 2301435 8745191 := bstep (se 1 (by rfl) ⟨6558893, by rfl⟩ : syracuseStep 8745191 = 13117787) B13117787
theorem B5830127 : Blo 2301435 5830127 := bstep (se 1 (by rfl) ⟨4372595, by rfl⟩ : syracuseStep 5830127 = 8745191) B8745191
theorem B3886751 : Blo 2301435 3886751 := bstep (se 1 (by rfl) ⟨2915063, by rfl⟩ : syracuseStep 3886751 = 5830127) B5830127
theorem B2591167 : Blo 2301435 2591167 := bstep (se 1 (by rfl) ⟨1943375, by rfl⟩ : syracuseStep 2591167 = 3886751) B3886751
theorem B3454889 : Blo 2301435 3454889 := bstep (se 2 (by rfl) ⟨1295583, by rfl⟩ : syracuseStep 3454889 = 2591167) B2591167
theorem B2303259 : Blo 2301435 2303259 := bstep (se 1 (by rfl) ⟨1727444, by rfl⟩ : syracuseStep 2303259 = 3454889) B3454889
theorem B8745205 : Blo 2301435 8745205 := bbase (se 5 (by rfl) ⟨409931, by rfl⟩ : syracuseStep 8745205 = 819863) (by norm_num)
theorem B11660273 : Blo 2301435 11660273 := bstep (se 2 (by rfl) ⟨4372602, by rfl⟩ : syracuseStep 11660273 = 8745205) B8745205
theorem B7773515 : Blo 2301435 7773515 := bstep (se 1 (by rfl) ⟨5830136, by rfl⟩ : syracuseStep 7773515 = 11660273) B11660273
theorem B5182343 : Blo 2301435 5182343 := bstep (se 1 (by rfl) ⟨3886757, by rfl⟩ : syracuseStep 5182343 = 7773515) B7773515
theorem B3454895 : Blo 2301435 3454895 := bstep (se 1 (by rfl) ⟨2591171, by rfl⟩ : syracuseStep 3454895 = 5182343) B5182343
theorem B2303263 : Blo 2301435 2303263 := bstep (se 1 (by rfl) ⟨1727447, by rfl⟩ : syracuseStep 2303263 = 3454895) B3454895
theorem B3454901 : Blo 2301435 3454901 := bbase (se 5 (by rfl) ⟨161948, by rfl⟩ : syracuseStep 3454901 = 323897) (by norm_num)
theorem B2303267 : Blo 2301435 2303267 := bstep (se 1 (by rfl) ⟨1727450, by rfl⟩ : syracuseStep 2303267 = 3454901) B3454901
theorem B5830157 : Blo 2301435 5830157 := bbase (se 3 (by rfl) ⟨1093154, by rfl⟩ : syracuseStep 5830157 = 2186309) (by norm_num)
theorem B3886771 : Blo 2301435 3886771 := bstep (se 1 (by rfl) ⟨2915078, by rfl⟩ : syracuseStep 3886771 = 5830157) B5830157
theorem B5182361 : Blo 2301435 5182361 := bstep (se 2 (by rfl) ⟨1943385, by rfl⟩ : syracuseStep 5182361 = 3886771) B3886771
theorem B3454907 : Blo 2301435 3454907 := bstep (se 1 (by rfl) ⟨2591180, by rfl⟩ : syracuseStep 3454907 = 5182361) B5182361
theorem B2303271 : Blo 2301435 2303271 := bstep (se 1 (by rfl) ⟨1727453, by rfl⟩ : syracuseStep 2303271 = 3454907) B3454907
theorem B2591185 : Blo 2301435 2591185 := bbase (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) (by norm_num)
theorem B3454913 : Blo 2301435 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B2303275 : Blo 2301435 2303275 := bstep (se 1 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 2303275 = 3454913) B3454913
theorem B4919213 : Blo 2301435 4919213 := bbase (se 3 (by rfl) ⟨922352, by rfl⟩ : syracuseStep 4919213 = 1844705) (by norm_num)
theorem B3279475 : Blo 2301435 3279475 := bstep (se 1 (by rfl) ⟨2459606, by rfl⟩ : syracuseStep 3279475 = 4919213) B4919213
theorem B4372633 : Blo 2301435 4372633 := bstep (se 2 (by rfl) ⟨1639737, by rfl⟩ : syracuseStep 4372633 = 3279475) B3279475
theorem B5830177 : Blo 2301435 5830177 := bstep (se 2 (by rfl) ⟨2186316, by rfl⟩ : syracuseStep 5830177 = 4372633) B4372633
theorem B7773569 : Blo 2301435 7773569 := bstep (se 2 (by rfl) ⟨2915088, by rfl⟩ : syracuseStep 7773569 = 5830177) B5830177
theorem B5182379 : Blo 2301435 5182379 := bstep (se 1 (by rfl) ⟨3886784, by rfl⟩ : syracuseStep 5182379 = 7773569) B7773569
theorem B3454919 : Blo 2301435 3454919 := bstep (se 1 (by rfl) ⟨2591189, by rfl⟩ : syracuseStep 3454919 = 5182379) B5182379
theorem B2303279 : Blo 2301435 2303279 := bstep (se 1 (by rfl) ⟨1727459, by rfl⟩ : syracuseStep 2303279 = 3454919) B3454919
theorem B3454925 : Blo 2301435 3454925 := bbase (se 3 (by rfl) ⟨647798, by rfl⟩ : syracuseStep 3454925 = 1295597) (by norm_num)
theorem B2303283 : Blo 2301435 2303283 := bstep (se 1 (by rfl) ⟨1727462, by rfl⟩ : syracuseStep 2303283 = 3454925) B3454925
theorem B5182397 : Blo 2301435 5182397 := bbase (se 3 (by rfl) ⟨971699, by rfl⟩ : syracuseStep 5182397 = 1943399) (by norm_num)
theorem B3454931 : Blo 2301435 3454931 := bstep (se 1 (by rfl) ⟨2591198, by rfl⟩ : syracuseStep 3454931 = 5182397) B5182397
theorem B2303287 : Blo 2301435 2303287 := bstep (se 1 (by rfl) ⟨1727465, by rfl⟩ : syracuseStep 2303287 = 3454931) B3454931
theorem B3886805 : Blo 2301435 3886805 := bbase (se 7 (by rfl) ⟨45548, by rfl⟩ : syracuseStep 3886805 = 91097) (by norm_num)
theorem B2591203 : Blo 2301435 2591203 := bstep (se 1 (by rfl) ⟨1943402, by rfl⟩ : syracuseStep 2591203 = 3886805) B3886805
theorem B3454937 : Blo 2301435 3454937 := bstep (se 2 (by rfl) ⟨1295601, by rfl⟩ : syracuseStep 3454937 = 2591203) B2591203
theorem B2303291 : Blo 2301435 2303291 := bstep (se 1 (by rfl) ⟨1727468, by rfl⟩ : syracuseStep 2303291 = 3454937) B3454937
theorem B9338885 : Blo 2301435 9338885 := bbase (se 4 (by rfl) ⟨875520, by rfl⟩ : syracuseStep 9338885 = 1751041) (by norm_num)
theorem B6225923 : Blo 2301435 6225923 := bstep (se 1 (by rfl) ⟨4669442, by rfl⟩ : syracuseStep 6225923 = 9338885) B9338885
theorem B4150615 : Blo 2301435 4150615 := bstep (se 1 (by rfl) ⟨3112961, by rfl⟩ : syracuseStep 4150615 = 6225923) B6225923
theorem B5534153 : Blo 2301435 5534153 := bstep (se 2 (by rfl) ⟨2075307, by rfl⟩ : syracuseStep 5534153 = 4150615) B4150615
theorem B3689435 : Blo 2301435 3689435 := bstep (se 1 (by rfl) ⟨2767076, by rfl⟩ : syracuseStep 3689435 = 5534153) B5534153
theorem B9838493 : Blo 2301435 9838493 := bstep (se 3 (by rfl) ⟨1844717, by rfl⟩ : syracuseStep 9838493 = 3689435) B3689435
theorem B6558995 : Blo 2301435 6558995 := bstep (se 1 (by rfl) ⟨4919246, by rfl⟩ : syracuseStep 6558995 = 9838493) B9838493
theorem B17490653 : Blo 2301435 17490653 := bstep (se 3 (by rfl) ⟨3279497, by rfl⟩ : syracuseStep 17490653 = 6558995) B6558995
theorem B11660435 : Blo 2301435 11660435 := bstep (se 1 (by rfl) ⟨8745326, by rfl⟩ : syracuseStep 11660435 = 17490653) B17490653
theorem B7773623 : Blo 2301435 7773623 := bstep (se 1 (by rfl) ⟨5830217, by rfl⟩ : syracuseStep 7773623 = 11660435) B11660435
theorem B5182415 : Blo 2301435 5182415 := bstep (se 1 (by rfl) ⟨3886811, by rfl⟩ : syracuseStep 5182415 = 7773623) B7773623
theorem B3454943 : Blo 2301435 3454943 := bstep (se 1 (by rfl) ⟨2591207, by rfl⟩ : syracuseStep 3454943 = 5182415) B5182415
theorem B2303295 : Blo 2301435 2303295 := bstep (se 1 (by rfl) ⟨1727471, by rfl⟩ : syracuseStep 2303295 = 3454943) B3454943
theorem B3454949 : Blo 2301435 3454949 := bbase (se 4 (by rfl) ⟨323901, by rfl⟩ : syracuseStep 3454949 = 647803) (by norm_num)
theorem B2303299 : Blo 2301435 2303299 := bstep (se 1 (by rfl) ⟨1727474, by rfl⟩ : syracuseStep 2303299 = 3454949) B3454949
theorem B5534173 : Blo 2301435 5534173 := bbase (se 3 (by rfl) ⟨1037657, by rfl⟩ : syracuseStep 5534173 = 2075315) (by norm_num)
theorem B7378897 : Blo 2301435 7378897 := bstep (se 2 (by rfl) ⟨2767086, by rfl⟩ : syracuseStep 7378897 = 5534173) B5534173
theorem B9838529 : Blo 2301435 9838529 := bstep (se 2 (by rfl) ⟨3689448, by rfl⟩ : syracuseStep 9838529 = 7378897) B7378897
theorem B6559019 : Blo 2301435 6559019 := bstep (se 1 (by rfl) ⟨4919264, by rfl⟩ : syracuseStep 6559019 = 9838529) B9838529
theorem B4372679 : Blo 2301435 4372679 := bstep (se 1 (by rfl) ⟨3279509, by rfl⟩ : syracuseStep 4372679 = 6559019) B6559019
theorem B2915119 : Blo 2301435 2915119 := bstep (se 1 (by rfl) ⟨2186339, by rfl⟩ : syracuseStep 2915119 = 4372679) B4372679
theorem B3886825 : Blo 2301435 3886825 := bstep (se 2 (by rfl) ⟨1457559, by rfl⟩ : syracuseStep 3886825 = 2915119) B2915119
theorem B5182433 : Blo 2301435 5182433 := bstep (se 2 (by rfl) ⟨1943412, by rfl⟩ : syracuseStep 5182433 = 3886825) B3886825
theorem B3454955 : Blo 2301435 3454955 := bstep (se 1 (by rfl) ⟨2591216, by rfl⟩ : syracuseStep 3454955 = 5182433) B5182433
theorem B2303303 : Blo 2301435 2303303 := bstep (se 1 (by rfl) ⟨1727477, by rfl⟩ : syracuseStep 2303303 = 3454955) B3454955
theorem B2591221 : Blo 2301435 2591221 := bbase (se 5 (by rfl) ⟨121463, by rfl⟩ : syracuseStep 2591221 = 242927) (by norm_num)
theorem B3454961 : Blo 2301435 3454961 := bstep (se 2 (by rfl) ⟨1295610, by rfl⟩ : syracuseStep 3454961 = 2591221) B2591221
theorem B2303307 : Blo 2301435 2303307 := bstep (se 1 (by rfl) ⟨1727480, by rfl⟩ : syracuseStep 2303307 = 3454961) B3454961
theorem B2915129 : Blo 2301435 2915129 := bbase (se 2 (by rfl) ⟨1093173, by rfl⟩ : syracuseStep 2915129 = 2186347) (by norm_num)
theorem B7773677 : Blo 2301435 7773677 := bstep (se 3 (by rfl) ⟨1457564, by rfl⟩ : syracuseStep 7773677 = 2915129) B2915129
theorem B5182451 : Blo 2301435 5182451 := bstep (se 1 (by rfl) ⟨3886838, by rfl⟩ : syracuseStep 5182451 = 7773677) B7773677
theorem B3454967 : Blo 2301435 3454967 := bstep (se 1 (by rfl) ⟨2591225, by rfl⟩ : syracuseStep 3454967 = 5182451) B5182451
theorem B2303311 : Blo 2301435 2303311 := bstep (se 1 (by rfl) ⟨1727483, by rfl⟩ : syracuseStep 2303311 = 3454967) B3454967
theorem B3454973 : Blo 2301435 3454973 := bbase (se 3 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 3454973 = 1295615) (by norm_num)
theorem B2303315 : Blo 2301435 2303315 := bstep (se 1 (by rfl) ⟨1727486, by rfl⟩ : syracuseStep 2303315 = 3454973) B3454973
theorem B5182469 : Blo 2301435 5182469 := bbase (se 4 (by rfl) ⟨485856, by rfl⟩ : syracuseStep 5182469 = 971713) (by norm_num)
theorem B3454979 : Blo 2301435 3454979 := bstep (se 1 (by rfl) ⟨2591234, by rfl⟩ : syracuseStep 3454979 = 5182469) B5182469
theorem B2303319 : Blo 2301435 2303319 := bstep (se 1 (by rfl) ⟨1727489, by rfl⟩ : syracuseStep 2303319 = 3454979) B3454979
theorem B4372717 : Blo 2301435 4372717 := bbase (se 3 (by rfl) ⟨819884, by rfl⟩ : syracuseStep 4372717 = 1639769) (by norm_num)
theorem B5830289 : Blo 2301435 5830289 := bstep (se 2 (by rfl) ⟨2186358, by rfl⟩ : syracuseStep 5830289 = 4372717) B4372717
theorem B3886859 : Blo 2301435 3886859 := bstep (se 1 (by rfl) ⟨2915144, by rfl⟩ : syracuseStep 3886859 = 5830289) B5830289
theorem B2591239 : Blo 2301435 2591239 := bstep (se 1 (by rfl) ⟨1943429, by rfl⟩ : syracuseStep 2591239 = 3886859) B3886859
theorem B3454985 : Blo 2301435 3454985 := bstep (se 2 (by rfl) ⟨1295619, by rfl⟩ : syracuseStep 3454985 = 2591239) B2591239
theorem B2303323 : Blo 2301435 2303323 := bstep (se 1 (by rfl) ⟨1727492, by rfl⟩ : syracuseStep 2303323 = 3454985) B3454985
theorem B11660597 : Blo 2301435 11660597 := bbase (se 5 (by rfl) ⟨546590, by rfl⟩ : syracuseStep 11660597 = 1093181) (by norm_num)
theorem B7773731 : Blo 2301435 7773731 := bstep (se 1 (by rfl) ⟨5830298, by rfl⟩ : syracuseStep 7773731 = 11660597) B11660597
theorem B5182487 : Blo 2301435 5182487 := bstep (se 1 (by rfl) ⟨3886865, by rfl⟩ : syracuseStep 5182487 = 7773731) B7773731
theorem B3454991 : Blo 2301435 3454991 := bstep (se 1 (by rfl) ⟨2591243, by rfl⟩ : syracuseStep 3454991 = 5182487) B5182487
theorem B2303327 : Blo 2301435 2303327 := bstep (se 1 (by rfl) ⟨1727495, by rfl⟩ : syracuseStep 2303327 = 3454991) B3454991
theorem B3454997 : Blo 2301435 3454997 := bbase (se 6 (by rfl) ⟨80976, by rfl⟩ : syracuseStep 3454997 = 161953) (by norm_num)
theorem B2303331 : Blo 2301435 2303331 := bstep (se 1 (by rfl) ⟨1727498, by rfl⟩ : syracuseStep 2303331 = 3454997) B3454997
theorem B15163445 : Blo 2301435 15163445 := bbase (se 5 (by rfl) ⟨710786, by rfl⟩ : syracuseStep 15163445 = 1421573) (by norm_num)
theorem B40435853 : Blo 2301435 40435853 := bstep (se 3 (by rfl) ⟨7581722, by rfl⟩ : syracuseStep 40435853 = 15163445) B15163445
theorem B431315765 : Blo 2301435 431315765 := bstep (se 5 (by rfl) ⟨20217926, by rfl⟩ : syracuseStep 431315765 = 40435853) B40435853
theorem B287543843 : Blo 2301435 287543843 := bstep (se 1 (by rfl) ⟨215657882, by rfl⟩ : syracuseStep 287543843 = 431315765) B431315765
theorem B191695895 : Blo 2301435 191695895 := bstep (se 1 (by rfl) ⟨143771921, by rfl⟩ : syracuseStep 191695895 = 287543843) B287543843
theorem B127797263 : Blo 2301435 127797263 := bstep (se 1 (by rfl) ⟨95847947, by rfl⟩ : syracuseStep 127797263 = 191695895) B191695895
theorem B85198175 : Blo 2301435 85198175 := bstep (se 1 (by rfl) ⟨63898631, by rfl⟩ : syracuseStep 85198175 = 127797263) B127797263
theorem B56798783 : Blo 2301435 56798783 := bstep (se 1 (by rfl) ⟨42599087, by rfl⟩ : syracuseStep 56798783 = 85198175) B85198175
theorem B37865855 : Blo 2301435 37865855 := bstep (se 1 (by rfl) ⟨28399391, by rfl⟩ : syracuseStep 37865855 = 56798783) B56798783
theorem B25243903 : Blo 2301435 25243903 := bstep (se 1 (by rfl) ⟨18932927, by rfl⟩ : syracuseStep 25243903 = 37865855) B37865855
theorem B134634149 : Blo 2301435 134634149 := bstep (se 4 (by rfl) ⟨12621951, by rfl⟩ : syracuseStep 134634149 = 25243903) B25243903
theorem B89756099 : Blo 2301435 89756099 := bstep (se 1 (by rfl) ⟨67317074, by rfl⟩ : syracuseStep 89756099 = 134634149) B134634149
theorem B59837399 : Blo 2301435 59837399 := bstep (se 1 (by rfl) ⟨44878049, by rfl⟩ : syracuseStep 59837399 = 89756099) B89756099
theorem B39891599 : Blo 2301435 39891599 := bstep (se 1 (by rfl) ⟨29918699, by rfl⟩ : syracuseStep 39891599 = 59837399) B59837399
theorem B26594399 : Blo 2301435 26594399 := bstep (se 1 (by rfl) ⟨19945799, by rfl⟩ : syracuseStep 26594399 = 39891599) B39891599
theorem B17729599 : Blo 2301435 17729599 := bstep (se 1 (by rfl) ⟨13297199, by rfl⟩ : syracuseStep 17729599 = 26594399) B26594399
theorem B23639465 : Blo 2301435 23639465 := bstep (se 2 (by rfl) ⟨8864799, by rfl⟩ : syracuseStep 23639465 = 17729599) B17729599
theorem B15759643 : Blo 2301435 15759643 := bstep (se 1 (by rfl) ⟨11819732, by rfl⟩ : syracuseStep 15759643 = 23639465) B23639465
theorem B21012857 : Blo 2301435 21012857 := bstep (se 2 (by rfl) ⟨7879821, by rfl⟩ : syracuseStep 21012857 = 15759643) B15759643
theorem B14008571 : Blo 2301435 14008571 := bstep (se 1 (by rfl) ⟨10506428, by rfl⟩ : syracuseStep 14008571 = 21012857) B21012857
theorem B9339047 : Blo 2301435 9339047 := bstep (se 1 (by rfl) ⟨7004285, by rfl⟩ : syracuseStep 9339047 = 14008571) B14008571
theorem B6226031 : Blo 2301435 6226031 := bstep (se 1 (by rfl) ⟨4669523, by rfl⟩ : syracuseStep 6226031 = 9339047) B9339047
theorem B4150687 : Blo 2301435 4150687 := bstep (se 1 (by rfl) ⟨3113015, by rfl⟩ : syracuseStep 4150687 = 6226031) B6226031
theorem B5534249 : Blo 2301435 5534249 := bstep (se 2 (by rfl) ⟨2075343, by rfl⟩ : syracuseStep 5534249 = 4150687) B4150687
theorem B14757997 : Blo 2301435 14757997 := bstep (se 3 (by rfl) ⟨2767124, by rfl⟩ : syracuseStep 14757997 = 5534249) B5534249
theorem B19677329 : Blo 2301435 19677329 := bstep (se 2 (by rfl) ⟨7378998, by rfl⟩ : syracuseStep 19677329 = 14757997) B14757997
theorem B13118219 : Blo 2301435 13118219 := bstep (se 1 (by rfl) ⟨9838664, by rfl⟩ : syracuseStep 13118219 = 19677329) B19677329
theorem B8745479 : Blo 2301435 8745479 := bstep (se 1 (by rfl) ⟨6559109, by rfl⟩ : syracuseStep 8745479 = 13118219) B13118219
theorem B5830319 : Blo 2301435 5830319 := bstep (se 1 (by rfl) ⟨4372739, by rfl⟩ : syracuseStep 5830319 = 8745479) B8745479
theorem B3886879 : Blo 2301435 3886879 := bstep (se 1 (by rfl) ⟨2915159, by rfl⟩ : syracuseStep 3886879 = 5830319) B5830319
theorem B5182505 : Blo 2301435 5182505 := bstep (se 2 (by rfl) ⟨1943439, by rfl⟩ : syracuseStep 5182505 = 3886879) B3886879
theorem B3455003 : Blo 2301435 3455003 := bstep (se 1 (by rfl) ⟨2591252, by rfl⟩ : syracuseStep 3455003 = 5182505) B5182505
theorem B2303335 : Blo 2301435 2303335 := bstep (se 1 (by rfl) ⟨1727501, by rfl⟩ : syracuseStep 2303335 = 3455003) B3455003
theorem B2591257 : Blo 2301435 2591257 := bbase (se 2 (by rfl) ⟨971721, by rfl⟩ : syracuseStep 2591257 = 1943443) (by norm_num)
theorem B3455009 : Blo 2301435 3455009 := bstep (se 2 (by rfl) ⟨1295628, by rfl⟩ : syracuseStep 3455009 = 2591257) B2591257
theorem B2303339 : Blo 2301435 2303339 := bstep (se 1 (by rfl) ⟨1727504, by rfl⟩ : syracuseStep 2303339 = 3455009) B3455009
theorem B8745509 : Blo 2301435 8745509 := bbase (se 4 (by rfl) ⟨819891, by rfl⟩ : syracuseStep 8745509 = 1639783) (by norm_num)
theorem B5830339 : Blo 2301435 5830339 := bstep (se 1 (by rfl) ⟨4372754, by rfl⟩ : syracuseStep 5830339 = 8745509) B8745509
theorem B7773785 : Blo 2301435 7773785 := bstep (se 2 (by rfl) ⟨2915169, by rfl⟩ : syracuseStep 7773785 = 5830339) B5830339
theorem B5182523 : Blo 2301435 5182523 := bstep (se 1 (by rfl) ⟨3886892, by rfl⟩ : syracuseStep 5182523 = 7773785) B7773785
theorem B3455015 : Blo 2301435 3455015 := bstep (se 1 (by rfl) ⟨2591261, by rfl⟩ : syracuseStep 3455015 = 5182523) B5182523
theorem B2303343 : Blo 2301435 2303343 := bstep (se 1 (by rfl) ⟨1727507, by rfl⟩ : syracuseStep 2303343 = 3455015) B3455015
theorem B3455021 : Blo 2301435 3455021 := bbase (se 3 (by rfl) ⟨647816, by rfl⟩ : syracuseStep 3455021 = 1295633) (by norm_num)
theorem B2303347 : Blo 2301435 2303347 := bstep (se 1 (by rfl) ⟨1727510, by rfl⟩ : syracuseStep 2303347 = 3455021) B3455021
theorem B5182541 : Blo 2301435 5182541 := bbase (se 3 (by rfl) ⟨971726, by rfl⟩ : syracuseStep 5182541 = 1943453) (by norm_num)
theorem B3455027 : Blo 2301435 3455027 := bstep (se 1 (by rfl) ⟨2591270, by rfl⟩ : syracuseStep 3455027 = 5182541) B5182541
theorem B2303351 : Blo 2301435 2303351 := bstep (se 1 (by rfl) ⟨1727513, by rfl⟩ : syracuseStep 2303351 = 3455027) B3455027
theorem B2915185 : Blo 2301435 2915185 := bbase (se 2 (by rfl) ⟨1093194, by rfl⟩ : syracuseStep 2915185 = 2186389) (by norm_num)
theorem B3886913 : Blo 2301435 3886913 := bstep (se 2 (by rfl) ⟨1457592, by rfl⟩ : syracuseStep 3886913 = 2915185) B2915185
theorem B2591275 : Blo 2301435 2591275 := bstep (se 1 (by rfl) ⟨1943456, by rfl⟩ : syracuseStep 2591275 = 3886913) B3886913
theorem B3455033 : Blo 2301435 3455033 := bstep (se 2 (by rfl) ⟨1295637, by rfl⟩ : syracuseStep 3455033 = 2591275) B2591275
theorem B2303355 : Blo 2301435 2303355 := bstep (se 1 (by rfl) ⟨1727516, by rfl⟩ : syracuseStep 2303355 = 3455033) B3455033
theorem B11068613 : Blo 2301435 11068613 := bbase (se 4 (by rfl) ⟨1037682, by rfl⟩ : syracuseStep 11068613 = 2075365) (by norm_num)
theorem B7379075 : Blo 2301435 7379075 := bstep (se 1 (by rfl) ⟨5534306, by rfl⟩ : syracuseStep 7379075 = 11068613) B11068613
theorem B4919383 : Blo 2301435 4919383 := bstep (se 1 (by rfl) ⟨3689537, by rfl⟩ : syracuseStep 4919383 = 7379075) B7379075
theorem B26236709 : Blo 2301435 26236709 := bstep (se 4 (by rfl) ⟨2459691, by rfl⟩ : syracuseStep 26236709 = 4919383) B4919383
theorem B17491139 : Blo 2301435 17491139 := bstep (se 1 (by rfl) ⟨13118354, by rfl⟩ : syracuseStep 17491139 = 26236709) B26236709
theorem B11660759 : Blo 2301435 11660759 := bstep (se 1 (by rfl) ⟨8745569, by rfl⟩ : syracuseStep 11660759 = 17491139) B17491139
theorem B7773839 : Blo 2301435 7773839 := bstep (se 1 (by rfl) ⟨5830379, by rfl⟩ : syracuseStep 7773839 = 11660759) B11660759
theorem B5182559 : Blo 2301435 5182559 := bstep (se 1 (by rfl) ⟨3886919, by rfl⟩ : syracuseStep 5182559 = 7773839) B7773839
theorem B3455039 : Blo 2301435 3455039 := bstep (se 1 (by rfl) ⟨2591279, by rfl⟩ : syracuseStep 3455039 = 5182559) B5182559
theorem B2303359 : Blo 2301435 2303359 := bstep (se 1 (by rfl) ⟨1727519, by rfl⟩ : syracuseStep 2303359 = 3455039) B3455039
theorem B3455045 : Blo 2301435 3455045 := bbase (se 4 (by rfl) ⟨323910, by rfl⟩ : syracuseStep 3455045 = 647821) (by norm_num)
theorem B2303363 : Blo 2301435 2303363 := bstep (se 1 (by rfl) ⟨1727522, by rfl⟩ : syracuseStep 2303363 = 3455045) B3455045
theorem B3886933 : Blo 2301435 3886933 := bbase (se 9 (by rfl) ⟨11387, by rfl⟩ : syracuseStep 3886933 = 22775) (by norm_num)
theorem B5182577 : Blo 2301435 5182577 := bstep (se 2 (by rfl) ⟨1943466, by rfl⟩ : syracuseStep 5182577 = 3886933) B3886933
theorem B3455051 : Blo 2301435 3455051 := bstep (se 1 (by rfl) ⟨2591288, by rfl⟩ : syracuseStep 3455051 = 5182577) B5182577
theorem B2303367 : Blo 2301435 2303367 := bstep (se 1 (by rfl) ⟨1727525, by rfl⟩ : syracuseStep 2303367 = 3455051) B3455051
theorem B2591293 : Blo 2301435 2591293 := bbase (se 3 (by rfl) ⟨485867, by rfl⟩ : syracuseStep 2591293 = 971735) (by norm_num)
theorem B3455057 : Blo 2301435 3455057 := bstep (se 2 (by rfl) ⟨1295646, by rfl⟩ : syracuseStep 3455057 = 2591293) B2591293
theorem B2303371 : Blo 2301435 2303371 := bstep (se 1 (by rfl) ⟨1727528, by rfl⟩ : syracuseStep 2303371 = 3455057) B3455057
theorem B7773893 : Blo 2301435 7773893 := bbase (se 4 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 7773893 = 1457605) (by norm_num)
theorem B5182595 : Blo 2301435 5182595 := bstep (se 1 (by rfl) ⟨3886946, by rfl⟩ : syracuseStep 5182595 = 7773893) B7773893
theorem B3455063 : Blo 2301435 3455063 := bstep (se 1 (by rfl) ⟨2591297, by rfl⟩ : syracuseStep 3455063 = 5182595) B5182595
theorem B2303375 : Blo 2301435 2303375 := bstep (se 1 (by rfl) ⟨1727531, by rfl⟩ : syracuseStep 2303375 = 3455063) B3455063
theorem B3455069 : Blo 2301435 3455069 := bbase (se 3 (by rfl) ⟨647825, by rfl⟩ : syracuseStep 3455069 = 1295651) (by norm_num)
theorem B2303379 : Blo 2301435 2303379 := bstep (se 1 (by rfl) ⟨1727534, by rfl⟩ : syracuseStep 2303379 = 3455069) B3455069
theorem B5182613 : Blo 2301435 5182613 := bbase (se 6 (by rfl) ⟨121467, by rfl⟩ : syracuseStep 5182613 = 242935) (by norm_num)
theorem B3455075 : Blo 2301435 3455075 := bstep (se 1 (by rfl) ⟨2591306, by rfl⟩ : syracuseStep 3455075 = 5182613) B5182613
theorem B2303383 : Blo 2301435 2303383 := bstep (se 1 (by rfl) ⟨1727537, by rfl⟩ : syracuseStep 2303383 = 3455075) B3455075
theorem B3279629 : Blo 2301435 3279629 := bbase (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) (by norm_num)
theorem B8745677 : Blo 2301435 8745677 := bstep (se 3 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 8745677 = 3279629) B3279629
theorem B5830451 : Blo 2301435 5830451 := bstep (se 1 (by rfl) ⟨4372838, by rfl⟩ : syracuseStep 5830451 = 8745677) B8745677
theorem B3886967 : Blo 2301435 3886967 := bstep (se 1 (by rfl) ⟨2915225, by rfl⟩ : syracuseStep 3886967 = 5830451) B5830451
theorem B2591311 : Blo 2301435 2591311 := bstep (se 1 (by rfl) ⟨1943483, by rfl⟩ : syracuseStep 2591311 = 3886967) B3886967
theorem B3455081 : Blo 2301435 3455081 := bstep (se 2 (by rfl) ⟨1295655, by rfl⟩ : syracuseStep 3455081 = 2591311) B2591311
theorem B2303387 : Blo 2301435 2303387 := bstep (se 1 (by rfl) ⟨1727540, by rfl⟩ : syracuseStep 2303387 = 3455081) B3455081
theorem B5253341 : Blo 2301435 5253341 := bbase (se 3 (by rfl) ⟨985001, by rfl⟩ : syracuseStep 5253341 = 1970003) (by norm_num)
theorem B14008909 : Blo 2301435 14008909 := bstep (se 3 (by rfl) ⟨2626670, by rfl⟩ : syracuseStep 14008909 = 5253341) B5253341
theorem B18678545 : Blo 2301435 18678545 := bstep (se 2 (by rfl) ⟨7004454, by rfl⟩ : syracuseStep 18678545 = 14008909) B14008909
theorem B12452363 : Blo 2301435 12452363 := bstep (se 1 (by rfl) ⟨9339272, by rfl⟩ : syracuseStep 12452363 = 18678545) B18678545
theorem B8301575 : Blo 2301435 8301575 := bstep (se 1 (by rfl) ⟨6226181, by rfl⟩ : syracuseStep 8301575 = 12452363) B12452363
theorem B22137533 : Blo 2301435 22137533 := bstep (se 3 (by rfl) ⟨4150787, by rfl⟩ : syracuseStep 22137533 = 8301575) B8301575
theorem B14758355 : Blo 2301435 14758355 := bstep (se 1 (by rfl) ⟨11068766, by rfl⟩ : syracuseStep 14758355 = 22137533) B22137533
theorem B9838903 : Blo 2301435 9838903 := bstep (se 1 (by rfl) ⟨7379177, by rfl⟩ : syracuseStep 9838903 = 14758355) B14758355
theorem B13118537 : Blo 2301435 13118537 := bstep (se 2 (by rfl) ⟨4919451, by rfl⟩ : syracuseStep 13118537 = 9838903) B9838903
theorem B8745691 : Blo 2301435 8745691 := bstep (se 1 (by rfl) ⟨6559268, by rfl⟩ : syracuseStep 8745691 = 13118537) B13118537
theorem B11660921 : Blo 2301435 11660921 := bstep (se 2 (by rfl) ⟨4372845, by rfl⟩ : syracuseStep 11660921 = 8745691) B8745691
theorem B7773947 : Blo 2301435 7773947 := bstep (se 1 (by rfl) ⟨5830460, by rfl⟩ : syracuseStep 7773947 = 11660921) B11660921
theorem B5182631 : Blo 2301435 5182631 := bstep (se 1 (by rfl) ⟨3886973, by rfl⟩ : syracuseStep 5182631 = 7773947) B7773947
theorem B3455087 : Blo 2301435 3455087 := bstep (se 1 (by rfl) ⟨2591315, by rfl⟩ : syracuseStep 3455087 = 5182631) B5182631
theorem B2303391 : Blo 2301435 2303391 := bstep (se 1 (by rfl) ⟨1727543, by rfl⟩ : syracuseStep 2303391 = 3455087) B3455087
theorem B3455093 : Blo 2301435 3455093 := bbase (se 5 (by rfl) ⟨161957, by rfl⟩ : syracuseStep 3455093 = 323915) (by norm_num)
theorem B2303395 : Blo 2301435 2303395 := bstep (se 1 (by rfl) ⟨1727546, by rfl⟩ : syracuseStep 2303395 = 3455093) B3455093
theorem B4372861 : Blo 2301435 4372861 := bbase (se 3 (by rfl) ⟨819911, by rfl⟩ : syracuseStep 4372861 = 1639823) (by norm_num)
theorem B5830481 : Blo 2301435 5830481 := bstep (se 2 (by rfl) ⟨2186430, by rfl⟩ : syracuseStep 5830481 = 4372861) B4372861
theorem B3886987 : Blo 2301435 3886987 := bstep (se 1 (by rfl) ⟨2915240, by rfl⟩ : syracuseStep 3886987 = 5830481) B5830481
theorem B5182649 : Blo 2301435 5182649 := bstep (se 2 (by rfl) ⟨1943493, by rfl⟩ : syracuseStep 5182649 = 3886987) B3886987
theorem B3455099 : Blo 2301435 3455099 := bstep (se 1 (by rfl) ⟨2591324, by rfl⟩ : syracuseStep 3455099 = 5182649) B5182649
theorem B2303399 : Blo 2301435 2303399 := bstep (se 1 (by rfl) ⟨1727549, by rfl⟩ : syracuseStep 2303399 = 3455099) B3455099
theorem B2591329 : Blo 2301435 2591329 := bbase (se 2 (by rfl) ⟨971748, by rfl⟩ : syracuseStep 2591329 = 1943497) (by norm_num)
theorem B3455105 : Blo 2301435 3455105 := bstep (se 2 (by rfl) ⟨1295664, by rfl⟩ : syracuseStep 3455105 = 2591329) B2591329
theorem B2303403 : Blo 2301435 2303403 := bstep (se 1 (by rfl) ⟨1727552, by rfl⟩ : syracuseStep 2303403 = 3455105) B3455105
theorem B5830501 : Blo 2301435 5830501 := bbase (se 4 (by rfl) ⟨546609, by rfl⟩ : syracuseStep 5830501 = 1093219) (by norm_num)
theorem B7774001 : Blo 2301435 7774001 := bstep (se 2 (by rfl) ⟨2915250, by rfl⟩ : syracuseStep 7774001 = 5830501) B5830501
theorem B5182667 : Blo 2301435 5182667 := bstep (se 1 (by rfl) ⟨3887000, by rfl⟩ : syracuseStep 5182667 = 7774001) B7774001
theorem B3455111 : Blo 2301435 3455111 := bstep (se 1 (by rfl) ⟨2591333, by rfl⟩ : syracuseStep 3455111 = 5182667) B5182667
theorem B2303407 : Blo 2301435 2303407 := bstep (se 1 (by rfl) ⟨1727555, by rfl⟩ : syracuseStep 2303407 = 3455111) B3455111
theorem B3455117 : Blo 2301435 3455117 := bbase (se 3 (by rfl) ⟨647834, by rfl⟩ : syracuseStep 3455117 = 1295669) (by norm_num)
theorem B2303411 : Blo 2301435 2303411 := bstep (se 1 (by rfl) ⟨1727558, by rfl⟩ : syracuseStep 2303411 = 3455117) B3455117
theorem B5182685 : Blo 2301435 5182685 := bbase (se 3 (by rfl) ⟨971753, by rfl⟩ : syracuseStep 5182685 = 1943507) (by norm_num)
theorem B3455123 : Blo 2301435 3455123 := bstep (se 1 (by rfl) ⟨2591342, by rfl⟩ : syracuseStep 3455123 = 5182685) B5182685
theorem B2303415 : Blo 2301435 2303415 := bstep (se 1 (by rfl) ⟨1727561, by rfl⟩ : syracuseStep 2303415 = 3455123) B3455123
theorem B3887021 : Blo 2301435 3887021 := bbase (se 3 (by rfl) ⟨728816, by rfl⟩ : syracuseStep 3887021 = 1457633) (by norm_num)
theorem B2591347 : Blo 2301435 2591347 := bstep (se 1 (by rfl) ⟨1943510, by rfl⟩ : syracuseStep 2591347 = 3887021) B3887021
theorem B3455129 : Blo 2301435 3455129 := bstep (se 2 (by rfl) ⟨1295673, by rfl⟩ : syracuseStep 3455129 = 2591347) B2591347
theorem B2303419 : Blo 2301435 2303419 := bstep (se 1 (by rfl) ⟨1727564, by rfl⟩ : syracuseStep 2303419 = 3455129) B3455129
theorem B7100117 : Blo 2301435 7100117 := bbase (se 7 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 7100117 = 166409) (by norm_num)
theorem B4733411 : Blo 2301435 4733411 := bstep (se 1 (by rfl) ⟨3550058, by rfl⟩ : syracuseStep 4733411 = 7100117) B7100117
theorem B12622429 : Blo 2301435 12622429 := bstep (se 3 (by rfl) ⟨2366705, by rfl⟩ : syracuseStep 12622429 = 4733411) B4733411
theorem B16829905 : Blo 2301435 16829905 := bstep (se 2 (by rfl) ⟨6311214, by rfl⟩ : syracuseStep 16829905 = 12622429) B12622429
theorem B22439873 : Blo 2301435 22439873 := bstep (se 2 (by rfl) ⟨8414952, by rfl⟩ : syracuseStep 22439873 = 16829905) B16829905
theorem B59839661 : Blo 2301435 59839661 := bstep (se 3 (by rfl) ⟨11219936, by rfl⟩ : syracuseStep 59839661 = 22439873) B22439873
theorem B159572429 : Blo 2301435 159572429 := bstep (se 3 (by rfl) ⟨29919830, by rfl⟩ : syracuseStep 159572429 = 59839661) B59839661
theorem B106381619 : Blo 2301435 106381619 := bstep (se 1 (by rfl) ⟨79786214, by rfl⟩ : syracuseStep 106381619 = 159572429) B159572429
theorem B70921079 : Blo 2301435 70921079 := bstep (se 1 (by rfl) ⟨53190809, by rfl⟩ : syracuseStep 70921079 = 106381619) B106381619
theorem B47280719 : Blo 2301435 47280719 := bstep (se 1 (by rfl) ⟨35460539, by rfl⟩ : syracuseStep 47280719 = 70921079) B70921079
theorem B126081917 : Blo 2301435 126081917 := bstep (se 3 (by rfl) ⟨23640359, by rfl⟩ : syracuseStep 126081917 = 47280719) B47280719
theorem B84054611 : Blo 2301435 84054611 := bstep (se 1 (by rfl) ⟨63040958, by rfl⟩ : syracuseStep 84054611 = 126081917) B126081917
theorem B224145629 : Blo 2301435 224145629 := bstep (se 3 (by rfl) ⟨42027305, by rfl⟩ : syracuseStep 224145629 = 84054611) B84054611
theorem B149430419 : Blo 2301435 149430419 := bstep (se 1 (by rfl) ⟨112072814, by rfl⟩ : syracuseStep 149430419 = 224145629) B224145629
theorem B99620279 : Blo 2301435 99620279 := bstep (se 1 (by rfl) ⟨74715209, by rfl⟩ : syracuseStep 99620279 = 149430419) B149430419
theorem B66413519 : Blo 2301435 66413519 := bstep (se 1 (by rfl) ⟨49810139, by rfl⟩ : syracuseStep 66413519 = 99620279) B99620279
theorem B44275679 : Blo 2301435 44275679 := bstep (se 1 (by rfl) ⟨33206759, by rfl⟩ : syracuseStep 44275679 = 66413519) B66413519
theorem B29517119 : Blo 2301435 29517119 := bstep (se 1 (by rfl) ⟨22137839, by rfl⟩ : syracuseStep 29517119 = 44275679) B44275679
theorem B19678079 : Blo 2301435 19678079 := bstep (se 1 (by rfl) ⟨14758559, by rfl⟩ : syracuseStep 19678079 = 29517119) B29517119
theorem B13118719 : Blo 2301435 13118719 := bstep (se 1 (by rfl) ⟨9839039, by rfl⟩ : syracuseStep 13118719 = 19678079) B19678079
theorem B17491625 : Blo 2301435 17491625 := bstep (se 2 (by rfl) ⟨6559359, by rfl⟩ : syracuseStep 17491625 = 13118719) B13118719
theorem B11661083 : Blo 2301435 11661083 := bstep (se 1 (by rfl) ⟨8745812, by rfl⟩ : syracuseStep 11661083 = 17491625) B17491625
theorem B7774055 : Blo 2301435 7774055 := bstep (se 1 (by rfl) ⟨5830541, by rfl⟩ : syracuseStep 7774055 = 11661083) B11661083
theorem B5182703 : Blo 2301435 5182703 := bstep (se 1 (by rfl) ⟨3887027, by rfl⟩ : syracuseStep 5182703 = 7774055) B7774055
theorem B3455135 : Blo 2301435 3455135 := bstep (se 1 (by rfl) ⟨2591351, by rfl⟩ : syracuseStep 3455135 = 5182703) B5182703
theorem B2303423 : Blo 2301435 2303423 := bstep (se 1 (by rfl) ⟨1727567, by rfl⟩ : syracuseStep 2303423 = 3455135) B3455135
theorem B3455141 : Blo 2301435 3455141 := bbase (se 4 (by rfl) ⟨323919, by rfl⟩ : syracuseStep 3455141 = 647839) (by norm_num)
theorem B2303427 : Blo 2301435 2303427 := bstep (se 1 (by rfl) ⟨1727570, by rfl⟩ : syracuseStep 2303427 = 3455141) B3455141
theorem B2915281 : Blo 2301435 2915281 := bbase (se 2 (by rfl) ⟨1093230, by rfl⟩ : syracuseStep 2915281 = 2186461) (by norm_num)
theorem B3887041 : Blo 2301435 3887041 := bstep (se 2 (by rfl) ⟨1457640, by rfl⟩ : syracuseStep 3887041 = 2915281) B2915281
theorem B5182721 : Blo 2301435 5182721 := bstep (se 2 (by rfl) ⟨1943520, by rfl⟩ : syracuseStep 5182721 = 3887041) B3887041
theorem B3455147 : Blo 2301435 3455147 := bstep (se 1 (by rfl) ⟨2591360, by rfl⟩ : syracuseStep 3455147 = 5182721) B5182721
theorem B2303431 : Blo 2301435 2303431 := bstep (se 1 (by rfl) ⟨1727573, by rfl⟩ : syracuseStep 2303431 = 3455147) B3455147
theorem B2591365 : Blo 2301435 2591365 := bbase (se 4 (by rfl) ⟨242940, by rfl⟩ : syracuseStep 2591365 = 485881) (by norm_num)
theorem B3455153 : Blo 2301435 3455153 := bstep (se 2 (by rfl) ⟨1295682, by rfl⟩ : syracuseStep 3455153 = 2591365) B2591365
theorem B2303435 : Blo 2301435 2303435 := bstep (se 1 (by rfl) ⟨1727576, by rfl⟩ : syracuseStep 2303435 = 3455153) B3455153
theorem C0 (j : ℕ) (h1 : 575358 ≤ j) (h2 : j ≤ 575858) : Blo 2301435 (4 * j + 3) := by
  interval_cases j
  · exact B2301435
  · exact B2301439
  · exact B2301443
  · exact B2301447
  · exact B2301451
  · exact B2301455
  · exact B2301459
  · exact B2301463
  · exact B2301467
  · exact B2301471
  · exact B2301475
  · exact B2301479
  · exact B2301483
  · exact B2301487
  · exact B2301491
  · exact B2301495
  · exact B2301499
  · exact B2301503
  · exact B2301507
  · exact B2301511
  · exact B2301515
  · exact B2301519
  · exact B2301523
  · exact B2301527
  · exact B2301531
  · exact B2301535
  · exact B2301539
  · exact B2301543
  · exact B2301547
  · exact B2301551
  · exact B2301555
  · exact B2301559
  · exact B2301563
  · exact B2301567
  · exact B2301571
  · exact B2301575
  · exact B2301579
  · exact B2301583
  · exact B2301587
  · exact B2301591
  · exact B2301595
  · exact B2301599
  · exact B2301603
  · exact B2301607
  · exact B2301611
  · exact B2301615
  · exact B2301619
  · exact B2301623
  · exact B2301627
  · exact B2301631
  · exact B2301635
  · exact B2301639
  · exact B2301643
  · exact B2301647
  · exact B2301651
  · exact B2301655
  · exact B2301659
  · exact B2301663
  · exact B2301667
  · exact B2301671
  · exact B2301675
  · exact B2301679
  · exact B2301683
  · exact B2301687
  · exact B2301691
  · exact B2301695
  · exact B2301699
  · exact B2301703
  · exact B2301707
  · exact B2301711
  · exact B2301715
  · exact B2301719
  · exact B2301723
  · exact B2301727
  · exact B2301731
  · exact B2301735
  · exact B2301739
  · exact B2301743
  · exact B2301747
  · exact B2301751
  · exact B2301755
  · exact B2301759
  · exact B2301763
  · exact B2301767
  · exact B2301771
  · exact B2301775
  · exact B2301779
  · exact B2301783
  · exact B2301787
  · exact B2301791
  · exact B2301795
  · exact B2301799
  · exact B2301803
  · exact B2301807
  · exact B2301811
  · exact B2301815
  · exact B2301819
  · exact B2301823
  · exact B2301827
  · exact B2301831
  · exact B2301835
  · exact B2301839
  · exact B2301843
  · exact B2301847
  · exact B2301851
  · exact B2301855
  · exact B2301859
  · exact B2301863
  · exact B2301867
  · exact B2301871
  · exact B2301875
  · exact B2301879
  · exact B2301883
  · exact B2301887
  · exact B2301891
  · exact B2301895
  · exact B2301899
  · exact B2301903
  · exact B2301907
  · exact B2301911
  · exact B2301915
  · exact B2301919
  · exact B2301923
  · exact B2301927
  · exact B2301931
  · exact B2301935
  · exact B2301939
  · exact B2301943
  · exact B2301947
  · exact B2301951
  · exact B2301955
  · exact B2301959
  · exact B2301963
  · exact B2301967
  · exact B2301971
  · exact B2301975
  · exact B2301979
  · exact B2301983
  · exact B2301987
  · exact B2301991
  · exact B2301995
  · exact B2301999
  · exact B2302003
  · exact B2302007
  · exact B2302011
  · exact B2302015
  · exact B2302019
  · exact B2302023
  · exact B2302027
  · exact B2302031
  · exact B2302035
  · exact B2302039
  · exact B2302043
  · exact B2302047
  · exact B2302051
  · exact B2302055
  · exact B2302059
  · exact B2302063
  · exact B2302067
  · exact B2302071
  · exact B2302075
  · exact B2302079
  · exact B2302083
  · exact B2302087
  · exact B2302091
  · exact B2302095
  · exact B2302099
  · exact B2302103
  · exact B2302107
  · exact B2302111
  · exact B2302115
  · exact B2302119
  · exact B2302123
  · exact B2302127
  · exact B2302131
  · exact B2302135
  · exact B2302139
  · exact B2302143
  · exact B2302147
  · exact B2302151
  · exact B2302155
  · exact B2302159
  · exact B2302163
  · exact B2302167
  · exact B2302171
  · exact B2302175
  · exact B2302179
  · exact B2302183
  · exact B2302187
  · exact B2302191
  · exact B2302195
  · exact B2302199
  · exact B2302203
  · exact B2302207
  · exact B2302211
  · exact B2302215
  · exact B2302219
  · exact B2302223
  · exact B2302227
  · exact B2302231
  · exact B2302235
  · exact B2302239
  · exact B2302243
  · exact B2302247
  · exact B2302251
  · exact B2302255
  · exact B2302259
  · exact B2302263
  · exact B2302267
  · exact B2302271
  · exact B2302275
  · exact B2302279
  · exact B2302283
  · exact B2302287
  · exact B2302291
  · exact B2302295
  · exact B2302299
  · exact B2302303
  · exact B2302307
  · exact B2302311
  · exact B2302315
  · exact B2302319
  · exact B2302323
  · exact B2302327
  · exact B2302331
  · exact B2302335
  · exact B2302339
  · exact B2302343
  · exact B2302347
  · exact B2302351
  · exact B2302355
  · exact B2302359
  · exact B2302363
  · exact B2302367
  · exact B2302371
  · exact B2302375
  · exact B2302379
  · exact B2302383
  · exact B2302387
  · exact B2302391
  · exact B2302395
  · exact B2302399
  · exact B2302403
  · exact B2302407
  · exact B2302411
  · exact B2302415
  · exact B2302419
  · exact B2302423
  · exact B2302427
  · exact B2302431
  · exact B2302435
  · exact B2302439
  · exact B2302443
  · exact B2302447
  · exact B2302451
  · exact B2302455
  · exact B2302459
  · exact B2302463
  · exact B2302467
  · exact B2302471
  · exact B2302475
  · exact B2302479
  · exact B2302483
  · exact B2302487
  · exact B2302491
  · exact B2302495
  · exact B2302499
  · exact B2302503
  · exact B2302507
  · exact B2302511
  · exact B2302515
  · exact B2302519
  · exact B2302523
  · exact B2302527
  · exact B2302531
  · exact B2302535
  · exact B2302539
  · exact B2302543
  · exact B2302547
  · exact B2302551
  · exact B2302555
  · exact B2302559
  · exact B2302563
  · exact B2302567
  · exact B2302571
  · exact B2302575
  · exact B2302579
  · exact B2302583
  · exact B2302587
  · exact B2302591
  · exact B2302595
  · exact B2302599
  · exact B2302603
  · exact B2302607
  · exact B2302611
  · exact B2302615
  · exact B2302619
  · exact B2302623
  · exact B2302627
  · exact B2302631
  · exact B2302635
  · exact B2302639
  · exact B2302643
  · exact B2302647
  · exact B2302651
  · exact B2302655
  · exact B2302659
  · exact B2302663
  · exact B2302667
  · exact B2302671
  · exact B2302675
  · exact B2302679
  · exact B2302683
  · exact B2302687
  · exact B2302691
  · exact B2302695
  · exact B2302699
  · exact B2302703
  · exact B2302707
  · exact B2302711
  · exact B2302715
  · exact B2302719
  · exact B2302723
  · exact B2302727
  · exact B2302731
  · exact B2302735
  · exact B2302739
  · exact B2302743
  · exact B2302747
  · exact B2302751
  · exact B2302755
  · exact B2302759
  · exact B2302763
  · exact B2302767
  · exact B2302771
  · exact B2302775
  · exact B2302779
  · exact B2302783
  · exact B2302787
  · exact B2302791
  · exact B2302795
  · exact B2302799
  · exact B2302803
  · exact B2302807
  · exact B2302811
  · exact B2302815
  · exact B2302819
  · exact B2302823
  · exact B2302827
  · exact B2302831
  · exact B2302835
  · exact B2302839
  · exact B2302843
  · exact B2302847
  · exact B2302851
  · exact B2302855
  · exact B2302859
  · exact B2302863
  · exact B2302867
  · exact B2302871
  · exact B2302875
  · exact B2302879
  · exact B2302883
  · exact B2302887
  · exact B2302891
  · exact B2302895
  · exact B2302899
  · exact B2302903
  · exact B2302907
  · exact B2302911
  · exact B2302915
  · exact B2302919
  · exact B2302923
  · exact B2302927
  · exact B2302931
  · exact B2302935
  · exact B2302939
  · exact B2302943
  · exact B2302947
  · exact B2302951
  · exact B2302955
  · exact B2302959
  · exact B2302963
  · exact B2302967
  · exact B2302971
  · exact B2302975
  · exact B2302979
  · exact B2302983
  · exact B2302987
  · exact B2302991
  · exact B2302995
  · exact B2302999
  · exact B2303003
  · exact B2303007
  · exact B2303011
  · exact B2303015
  · exact B2303019
  · exact B2303023
  · exact B2303027
  · exact B2303031
  · exact B2303035
  · exact B2303039
  · exact B2303043
  · exact B2303047
  · exact B2303051
  · exact B2303055
  · exact B2303059
  · exact B2303063
  · exact B2303067
  · exact B2303071
  · exact B2303075
  · exact B2303079
  · exact B2303083
  · exact B2303087
  · exact B2303091
  · exact B2303095
  · exact B2303099
  · exact B2303103
  · exact B2303107
  · exact B2303111
  · exact B2303115
  · exact B2303119
  · exact B2303123
  · exact B2303127
  · exact B2303131
  · exact B2303135
  · exact B2303139
  · exact B2303143
  · exact B2303147
  · exact B2303151
  · exact B2303155
  · exact B2303159
  · exact B2303163
  · exact B2303167
  · exact B2303171
  · exact B2303175
  · exact B2303179
  · exact B2303183
  · exact B2303187
  · exact B2303191
  · exact B2303195
  · exact B2303199
  · exact B2303203
  · exact B2303207
  · exact B2303211
  · exact B2303215
  · exact B2303219
  · exact B2303223
  · exact B2303227
  · exact B2303231
  · exact B2303235
  · exact B2303239
  · exact B2303243
  · exact B2303247
  · exact B2303251
  · exact B2303255
  · exact B2303259
  · exact B2303263
  · exact B2303267
  · exact B2303271
  · exact B2303275
  · exact B2303279
  · exact B2303283
  · exact B2303287
  · exact B2303291
  · exact B2303295
  · exact B2303299
  · exact B2303303
  · exact B2303307
  · exact B2303311
  · exact B2303315
  · exact B2303319
  · exact B2303323
  · exact B2303327
  · exact B2303331
  · exact B2303335
  · exact B2303339
  · exact B2303343
  · exact B2303347
  · exact B2303351
  · exact B2303355
  · exact B2303359
  · exact B2303363
  · exact B2303367
  · exact B2303371
  · exact B2303375
  · exact B2303379
  · exact B2303383
  · exact B2303387
  · exact B2303391
  · exact B2303395
  · exact B2303399
  · exact B2303403
  · exact B2303407
  · exact B2303411
  · exact B2303415
  · exact B2303419
  · exact B2303423
  · exact B2303427
  · exact B2303431
  · exact B2303435
theorem solution (m : ℕ) (hlo : 2301435 ≤ m) (hhi : m ≤ 2303435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 575358 ≤ j := by omega
    have hj2 : j ≤ 575858 := by omega
    have hb : Blo 2301435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
