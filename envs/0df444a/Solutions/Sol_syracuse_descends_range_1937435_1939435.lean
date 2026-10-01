-- Prove2me | solution 1 for syracuse_descends_range_1937435_1939435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:28.279303+00:00
-- url     : https://prove2.me/submissions/e3afe428-c7d6-44b6-a416-b52961cd7de9

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

theorem B2327549 : Blo 1937435 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B6206797 : Blo 1937435 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B8275729 : Blo 1937435 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B11034305 : Blo 1937435 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B7356203 : Blo 1937435 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B4904135 : Blo 1937435 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B3269423 : Blo 1937435 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B2179615 : Blo 1937435 2179615 := bstep (se 1 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 2179615 = 3269423) B3269423
theorem B2906153 : Blo 1937435 2906153 := bstep (se 2 (by rfl) ⟨1089807, by rfl⟩ : syracuseStep 2906153 = 2179615) B2179615
theorem B1937435 : Blo 1937435 1937435 := bstep (se 1 (by rfl) ⟨1453076, by rfl⟩ : syracuseStep 1937435 = 2906153) B2906153
theorem B6982661 : Blo 1937435 6982661 := bbase (se 4 (by rfl) ⟨654624, by rfl⟩ : syracuseStep 6982661 = 1309249) (by norm_num)
theorem B4655107 : Blo 1937435 4655107 := bstep (se 1 (by rfl) ⟨3491330, by rfl⟩ : syracuseStep 4655107 = 6982661) B6982661
theorem B6206809 : Blo 1937435 6206809 := bstep (se 2 (by rfl) ⟨2327553, by rfl⟩ : syracuseStep 6206809 = 4655107) B4655107
theorem B8275745 : Blo 1937435 8275745 := bstep (se 2 (by rfl) ⟨3103404, by rfl⟩ : syracuseStep 8275745 = 6206809) B6206809
theorem B5517163 : Blo 1937435 5517163 := bstep (se 1 (by rfl) ⟨4137872, by rfl⟩ : syracuseStep 5517163 = 8275745) B8275745
theorem B7356217 : Blo 1937435 7356217 := bstep (se 2 (by rfl) ⟨2758581, by rfl⟩ : syracuseStep 7356217 = 5517163) B5517163
theorem B9808289 : Blo 1937435 9808289 := bstep (se 2 (by rfl) ⟨3678108, by rfl⟩ : syracuseStep 9808289 = 7356217) B7356217
theorem B6538859 : Blo 1937435 6538859 := bstep (se 1 (by rfl) ⟨4904144, by rfl⟩ : syracuseStep 6538859 = 9808289) B9808289
theorem B4359239 : Blo 1937435 4359239 := bstep (se 1 (by rfl) ⟨3269429, by rfl⟩ : syracuseStep 4359239 = 6538859) B6538859
theorem B2906159 : Blo 1937435 2906159 := bstep (se 1 (by rfl) ⟨2179619, by rfl⟩ : syracuseStep 2906159 = 4359239) B4359239
theorem B1937439 : Blo 1937435 1937439 := bstep (se 1 (by rfl) ⟨1453079, by rfl⟩ : syracuseStep 1937439 = 2906159) B2906159
theorem B2906165 : Blo 1937435 2906165 := bbase (se 5 (by rfl) ⟨136226, by rfl⟩ : syracuseStep 2906165 = 272453) (by norm_num)
theorem B1937443 : Blo 1937435 1937443 := bstep (se 1 (by rfl) ⟨1453082, by rfl⟩ : syracuseStep 1937443 = 2906165) B2906165
theorem B4904165 : Blo 1937435 4904165 := bbase (se 4 (by rfl) ⟨459765, by rfl⟩ : syracuseStep 4904165 = 919531) (by norm_num)
theorem B3269443 : Blo 1937435 3269443 := bstep (se 1 (by rfl) ⟨2452082, by rfl⟩ : syracuseStep 3269443 = 4904165) B4904165
theorem B4359257 : Blo 1937435 4359257 := bstep (se 2 (by rfl) ⟨1634721, by rfl⟩ : syracuseStep 4359257 = 3269443) B3269443
theorem B2906171 : Blo 1937435 2906171 := bstep (se 1 (by rfl) ⟨2179628, by rfl⟩ : syracuseStep 2906171 = 4359257) B4359257
theorem B1937447 : Blo 1937435 1937447 := bstep (se 1 (by rfl) ⟨1453085, by rfl⟩ : syracuseStep 1937447 = 2906171) B2906171
theorem B2179633 : Blo 1937435 2179633 := bbase (se 2 (by rfl) ⟨817362, by rfl⟩ : syracuseStep 2179633 = 1634725) (by norm_num)
theorem B2906177 : Blo 1937435 2906177 := bstep (se 2 (by rfl) ⟨1089816, by rfl⟩ : syracuseStep 2906177 = 2179633) B2179633
theorem B1937451 : Blo 1937435 1937451 := bstep (se 1 (by rfl) ⟨1453088, by rfl⟩ : syracuseStep 1937451 = 2906177) B2906177
theorem B2327573 : Blo 1937435 2327573 := bbase (se 6 (by rfl) ⟨54552, by rfl⟩ : syracuseStep 2327573 = 109105) (by norm_num)
theorem B6206861 : Blo 1937435 6206861 := bstep (se 3 (by rfl) ⟨1163786, by rfl⟩ : syracuseStep 6206861 = 2327573) B2327573
theorem B4137907 : Blo 1937435 4137907 := bstep (se 1 (by rfl) ⟨3103430, by rfl⟩ : syracuseStep 4137907 = 6206861) B6206861
theorem B5517209 : Blo 1937435 5517209 := bstep (se 2 (by rfl) ⟨2068953, by rfl⟩ : syracuseStep 5517209 = 4137907) B4137907
theorem B3678139 : Blo 1937435 3678139 := bstep (se 1 (by rfl) ⟨2758604, by rfl⟩ : syracuseStep 3678139 = 5517209) B5517209
theorem B4904185 : Blo 1937435 4904185 := bstep (se 2 (by rfl) ⟨1839069, by rfl⟩ : syracuseStep 4904185 = 3678139) B3678139
theorem B6538913 : Blo 1937435 6538913 := bstep (se 2 (by rfl) ⟨2452092, by rfl⟩ : syracuseStep 6538913 = 4904185) B4904185
theorem B4359275 : Blo 1937435 4359275 := bstep (se 1 (by rfl) ⟨3269456, by rfl⟩ : syracuseStep 4359275 = 6538913) B6538913
theorem B2906183 : Blo 1937435 2906183 := bstep (se 1 (by rfl) ⟨2179637, by rfl⟩ : syracuseStep 2906183 = 4359275) B4359275
theorem B1937455 : Blo 1937435 1937455 := bstep (se 1 (by rfl) ⟨1453091, by rfl⟩ : syracuseStep 1937455 = 2906183) B2906183
theorem B2906189 : Blo 1937435 2906189 := bbase (se 3 (by rfl) ⟨544910, by rfl⟩ : syracuseStep 2906189 = 1089821) (by norm_num)
theorem B1937459 : Blo 1937435 1937459 := bstep (se 1 (by rfl) ⟨1453094, by rfl⟩ : syracuseStep 1937459 = 2906189) B2906189
theorem B4359293 : Blo 1937435 4359293 := bbase (se 3 (by rfl) ⟨817367, by rfl⟩ : syracuseStep 4359293 = 1634735) (by norm_num)
theorem B2906195 : Blo 1937435 2906195 := bstep (se 1 (by rfl) ⟨2179646, by rfl⟩ : syracuseStep 2906195 = 4359293) B4359293
theorem B1937463 : Blo 1937435 1937463 := bstep (se 1 (by rfl) ⟨1453097, by rfl⟩ : syracuseStep 1937463 = 2906195) B2906195
theorem B3269477 : Blo 1937435 3269477 := bbase (se 4 (by rfl) ⟨306513, by rfl⟩ : syracuseStep 3269477 = 613027) (by norm_num)
theorem B2179651 : Blo 1937435 2179651 := bstep (se 1 (by rfl) ⟨1634738, by rfl⟩ : syracuseStep 2179651 = 3269477) B3269477
theorem B2906201 : Blo 1937435 2906201 := bstep (se 2 (by rfl) ⟨1089825, by rfl⟩ : syracuseStep 2906201 = 2179651) B2179651
theorem B1937467 : Blo 1937435 1937467 := bstep (se 1 (by rfl) ⟨1453100, by rfl⟩ : syracuseStep 1937467 = 2906201) B2906201
theorem B4137941 : Blo 1937435 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B2758627 : Blo 1937435 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B14712677 : Blo 1937435 14712677 := bstep (se 4 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 14712677 = 2758627) B2758627
theorem B9808451 : Blo 1937435 9808451 := bstep (se 1 (by rfl) ⟨7356338, by rfl⟩ : syracuseStep 9808451 = 14712677) B14712677
theorem B6538967 : Blo 1937435 6538967 := bstep (se 1 (by rfl) ⟨4904225, by rfl⟩ : syracuseStep 6538967 = 9808451) B9808451
theorem B4359311 : Blo 1937435 4359311 := bstep (se 1 (by rfl) ⟨3269483, by rfl⟩ : syracuseStep 4359311 = 6538967) B6538967
theorem B2906207 : Blo 1937435 2906207 := bstep (se 1 (by rfl) ⟨2179655, by rfl⟩ : syracuseStep 2906207 = 4359311) B4359311
theorem B1937471 : Blo 1937435 1937471 := bstep (se 1 (by rfl) ⟨1453103, by rfl⟩ : syracuseStep 1937471 = 2906207) B2906207
theorem B2906213 : Blo 1937435 2906213 := bbase (se 4 (by rfl) ⟨272457, by rfl⟩ : syracuseStep 2906213 = 544915) (by norm_num)
theorem B1937475 : Blo 1937435 1937475 := bstep (se 1 (by rfl) ⟨1453106, by rfl⟩ : syracuseStep 1937475 = 2906213) B2906213
theorem B15711317 : Blo 1937435 15711317 := bbase (se 8 (by rfl) ⟨92058, by rfl⟩ : syracuseStep 15711317 = 184117) (by norm_num)
theorem B10474211 : Blo 1937435 10474211 := bstep (se 1 (by rfl) ⟨7855658, by rfl⟩ : syracuseStep 10474211 = 15711317) B15711317
theorem B6982807 : Blo 1937435 6982807 := bstep (se 1 (by rfl) ⟨5237105, by rfl⟩ : syracuseStep 6982807 = 10474211) B10474211
theorem B9310409 : Blo 1937435 9310409 := bstep (se 2 (by rfl) ⟨3491403, by rfl⟩ : syracuseStep 9310409 = 6982807) B6982807
theorem B6206939 : Blo 1937435 6206939 := bstep (se 1 (by rfl) ⟨4655204, by rfl⟩ : syracuseStep 6206939 = 9310409) B9310409
theorem B4137959 : Blo 1937435 4137959 := bstep (se 1 (by rfl) ⟨3103469, by rfl⟩ : syracuseStep 4137959 = 6206939) B6206939
theorem B2758639 : Blo 1937435 2758639 := bstep (se 1 (by rfl) ⟨2068979, by rfl⟩ : syracuseStep 2758639 = 4137959) B4137959
theorem B3678185 : Blo 1937435 3678185 := bstep (se 2 (by rfl) ⟨1379319, by rfl⟩ : syracuseStep 3678185 = 2758639) B2758639
theorem B2452123 : Blo 1937435 2452123 := bstep (se 1 (by rfl) ⟨1839092, by rfl⟩ : syracuseStep 2452123 = 3678185) B3678185
theorem B3269497 : Blo 1937435 3269497 := bstep (se 2 (by rfl) ⟨1226061, by rfl⟩ : syracuseStep 3269497 = 2452123) B2452123
theorem B4359329 : Blo 1937435 4359329 := bstep (se 2 (by rfl) ⟨1634748, by rfl⟩ : syracuseStep 4359329 = 3269497) B3269497
theorem B2906219 : Blo 1937435 2906219 := bstep (se 1 (by rfl) ⟨2179664, by rfl⟩ : syracuseStep 2906219 = 4359329) B4359329
theorem B1937479 : Blo 1937435 1937479 := bstep (se 1 (by rfl) ⟨1453109, by rfl⟩ : syracuseStep 1937479 = 2906219) B2906219
theorem B2179669 : Blo 1937435 2179669 := bbase (se 8 (by rfl) ⟨12771, by rfl⟩ : syracuseStep 2179669 = 25543) (by norm_num)
theorem B2906225 : Blo 1937435 2906225 := bstep (se 2 (by rfl) ⟨1089834, by rfl⟩ : syracuseStep 2906225 = 2179669) B2179669
theorem B1937483 : Blo 1937435 1937483 := bstep (se 1 (by rfl) ⟨1453112, by rfl⟩ : syracuseStep 1937483 = 2906225) B2906225
theorem B2452133 : Blo 1937435 2452133 := bbase (se 4 (by rfl) ⟨229887, by rfl⟩ : syracuseStep 2452133 = 459775) (by norm_num)
theorem B6539021 : Blo 1937435 6539021 := bstep (se 3 (by rfl) ⟨1226066, by rfl⟩ : syracuseStep 6539021 = 2452133) B2452133
theorem B4359347 : Blo 1937435 4359347 := bstep (se 1 (by rfl) ⟨3269510, by rfl⟩ : syracuseStep 4359347 = 6539021) B6539021
theorem B2906231 : Blo 1937435 2906231 := bstep (se 1 (by rfl) ⟨2179673, by rfl⟩ : syracuseStep 2906231 = 4359347) B4359347
theorem B1937487 : Blo 1937435 1937487 := bstep (se 1 (by rfl) ⟨1453115, by rfl⟩ : syracuseStep 1937487 = 2906231) B2906231
theorem B2906237 : Blo 1937435 2906237 := bbase (se 3 (by rfl) ⟨544919, by rfl⟩ : syracuseStep 2906237 = 1089839) (by norm_num)
theorem B1937491 : Blo 1937435 1937491 := bstep (se 1 (by rfl) ⟨1453118, by rfl⟩ : syracuseStep 1937491 = 2906237) B2906237
theorem B4359365 : Blo 1937435 4359365 := bbase (se 4 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 4359365 = 817381) (by norm_num)
theorem B2906243 : Blo 1937435 2906243 := bstep (se 1 (by rfl) ⟨2179682, by rfl⟩ : syracuseStep 2906243 = 4359365) B4359365
theorem B1937495 : Blo 1937435 1937495 := bstep (se 1 (by rfl) ⟨1453121, by rfl⟩ : syracuseStep 1937495 = 2906243) B2906243
theorem B12414005 : Blo 1937435 12414005 := bbase (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) (by norm_num)
theorem B8276003 : Blo 1937435 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B5517335 : Blo 1937435 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B3678223 : Blo 1937435 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B4904297 : Blo 1937435 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B3269531 : Blo 1937435 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B2179687 : Blo 1937435 2179687 := bstep (se 1 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 2179687 = 3269531) B3269531
theorem B2906249 : Blo 1937435 2906249 := bstep (se 2 (by rfl) ⟨1089843, by rfl⟩ : syracuseStep 2906249 = 2179687) B2179687
theorem B1937499 : Blo 1937435 1937499 := bstep (se 1 (by rfl) ⟨1453124, by rfl⟩ : syracuseStep 1937499 = 2906249) B2906249
theorem B9808613 : Blo 1937435 9808613 := bbase (se 4 (by rfl) ⟨919557, by rfl⟩ : syracuseStep 9808613 = 1839115) (by norm_num)
theorem B6539075 : Blo 1937435 6539075 := bstep (se 1 (by rfl) ⟨4904306, by rfl⟩ : syracuseStep 6539075 = 9808613) B9808613
theorem B4359383 : Blo 1937435 4359383 := bstep (se 1 (by rfl) ⟨3269537, by rfl⟩ : syracuseStep 4359383 = 6539075) B6539075
theorem B2906255 : Blo 1937435 2906255 := bstep (se 1 (by rfl) ⟨2179691, by rfl⟩ : syracuseStep 2906255 = 4359383) B4359383
theorem B1937503 : Blo 1937435 1937503 := bstep (se 1 (by rfl) ⟨1453127, by rfl⟩ : syracuseStep 1937503 = 2906255) B2906255
theorem B2906261 : Blo 1937435 2906261 := bbase (se 6 (by rfl) ⟨68115, by rfl⟩ : syracuseStep 2906261 = 136231) (by norm_num)
theorem B1937507 : Blo 1937435 1937507 := bstep (se 1 (by rfl) ⟨1453130, by rfl⟩ : syracuseStep 1937507 = 2906261) B2906261
theorem B8276053 : Blo 1937435 8276053 := bbase (se 8 (by rfl) ⟨48492, by rfl⟩ : syracuseStep 8276053 = 96985) (by norm_num)
theorem B11034737 : Blo 1937435 11034737 := bstep (se 2 (by rfl) ⟨4138026, by rfl⟩ : syracuseStep 11034737 = 8276053) B8276053
theorem B7356491 : Blo 1937435 7356491 := bstep (se 1 (by rfl) ⟨5517368, by rfl⟩ : syracuseStep 7356491 = 11034737) B11034737
theorem B4904327 : Blo 1937435 4904327 := bstep (se 1 (by rfl) ⟨3678245, by rfl⟩ : syracuseStep 4904327 = 7356491) B7356491
theorem B3269551 : Blo 1937435 3269551 := bstep (se 1 (by rfl) ⟨2452163, by rfl⟩ : syracuseStep 3269551 = 4904327) B4904327
theorem B4359401 : Blo 1937435 4359401 := bstep (se 2 (by rfl) ⟨1634775, by rfl⟩ : syracuseStep 4359401 = 3269551) B3269551
theorem B2906267 : Blo 1937435 2906267 := bstep (se 1 (by rfl) ⟨2179700, by rfl⟩ : syracuseStep 2906267 = 4359401) B4359401
theorem B1937511 : Blo 1937435 1937511 := bstep (se 1 (by rfl) ⟨1453133, by rfl⟩ : syracuseStep 1937511 = 2906267) B2906267
theorem B2179705 : Blo 1937435 2179705 := bbase (se 2 (by rfl) ⟨817389, by rfl⟩ : syracuseStep 2179705 = 1634779) (by norm_num)
theorem B2906273 : Blo 1937435 2906273 := bstep (se 2 (by rfl) ⟨1089852, by rfl⟩ : syracuseStep 2906273 = 2179705) B2179705
theorem B1937515 : Blo 1937435 1937515 := bstep (se 1 (by rfl) ⟨1453136, by rfl⟩ : syracuseStep 1937515 = 2906273) B2906273
theorem B6982949 : Blo 1937435 6982949 := bbase (se 4 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 6982949 = 1309303) (by norm_num)
theorem B18621197 : Blo 1937435 18621197 := bstep (se 3 (by rfl) ⟨3491474, by rfl⟩ : syracuseStep 18621197 = 6982949) B6982949
theorem B12414131 : Blo 1937435 12414131 := bstep (se 1 (by rfl) ⟨9310598, by rfl⟩ : syracuseStep 12414131 = 18621197) B18621197
theorem B8276087 : Blo 1937435 8276087 := bstep (se 1 (by rfl) ⟨6207065, by rfl⟩ : syracuseStep 8276087 = 12414131) B12414131
theorem B5517391 : Blo 1937435 5517391 := bstep (se 1 (by rfl) ⟨4138043, by rfl⟩ : syracuseStep 5517391 = 8276087) B8276087
theorem B7356521 : Blo 1937435 7356521 := bstep (se 2 (by rfl) ⟨2758695, by rfl⟩ : syracuseStep 7356521 = 5517391) B5517391
theorem B4904347 : Blo 1937435 4904347 := bstep (se 1 (by rfl) ⟨3678260, by rfl⟩ : syracuseStep 4904347 = 7356521) B7356521
theorem B6539129 : Blo 1937435 6539129 := bstep (se 2 (by rfl) ⟨2452173, by rfl⟩ : syracuseStep 6539129 = 4904347) B4904347
theorem B4359419 : Blo 1937435 4359419 := bstep (se 1 (by rfl) ⟨3269564, by rfl⟩ : syracuseStep 4359419 = 6539129) B6539129
theorem B2906279 : Blo 1937435 2906279 := bstep (se 1 (by rfl) ⟨2179709, by rfl⟩ : syracuseStep 2906279 = 4359419) B4359419
theorem B1937519 : Blo 1937435 1937519 := bstep (se 1 (by rfl) ⟨1453139, by rfl⟩ : syracuseStep 1937519 = 2906279) B2906279
theorem B2906285 : Blo 1937435 2906285 := bbase (se 3 (by rfl) ⟨544928, by rfl⟩ : syracuseStep 2906285 = 1089857) (by norm_num)
theorem B1937523 : Blo 1937435 1937523 := bstep (se 1 (by rfl) ⟨1453142, by rfl⟩ : syracuseStep 1937523 = 2906285) B2906285
theorem B4359437 : Blo 1937435 4359437 := bbase (se 3 (by rfl) ⟨817394, by rfl⟩ : syracuseStep 4359437 = 1634789) (by norm_num)
theorem B2906291 : Blo 1937435 2906291 := bstep (se 1 (by rfl) ⟨2179718, by rfl⟩ : syracuseStep 2906291 = 4359437) B4359437
theorem B1937527 : Blo 1937435 1937527 := bstep (se 1 (by rfl) ⟨1453145, by rfl⟩ : syracuseStep 1937527 = 2906291) B2906291
theorem B2452189 : Blo 1937435 2452189 := bbase (se 3 (by rfl) ⟨459785, by rfl⟩ : syracuseStep 2452189 = 919571) (by norm_num)
theorem B3269585 : Blo 1937435 3269585 := bstep (se 2 (by rfl) ⟨1226094, by rfl⟩ : syracuseStep 3269585 = 2452189) B2452189
theorem B2179723 : Blo 1937435 2179723 := bstep (se 1 (by rfl) ⟨1634792, by rfl⟩ : syracuseStep 2179723 = 3269585) B3269585
theorem B2906297 : Blo 1937435 2906297 := bstep (se 2 (by rfl) ⟨1089861, by rfl⟩ : syracuseStep 2906297 = 2179723) B2179723
theorem B1937531 : Blo 1937435 1937531 := bstep (se 1 (by rfl) ⟨1453148, by rfl⟩ : syracuseStep 1937531 = 2906297) B2906297
theorem B16552309 : Blo 1937435 16552309 := bbase (se 5 (by rfl) ⟨775889, by rfl⟩ : syracuseStep 16552309 = 1551779) (by norm_num)
theorem B22069745 : Blo 1937435 22069745 := bstep (se 2 (by rfl) ⟨8276154, by rfl⟩ : syracuseStep 22069745 = 16552309) B16552309
theorem B14713163 : Blo 1937435 14713163 := bstep (se 1 (by rfl) ⟨11034872, by rfl⟩ : syracuseStep 14713163 = 22069745) B22069745
theorem B9808775 : Blo 1937435 9808775 := bstep (se 1 (by rfl) ⟨7356581, by rfl⟩ : syracuseStep 9808775 = 14713163) B14713163
theorem B6539183 : Blo 1937435 6539183 := bstep (se 1 (by rfl) ⟨4904387, by rfl⟩ : syracuseStep 6539183 = 9808775) B9808775
theorem B4359455 : Blo 1937435 4359455 := bstep (se 1 (by rfl) ⟨3269591, by rfl⟩ : syracuseStep 4359455 = 6539183) B6539183
theorem B2906303 : Blo 1937435 2906303 := bstep (se 1 (by rfl) ⟨2179727, by rfl⟩ : syracuseStep 2906303 = 4359455) B4359455
theorem B1937535 : Blo 1937435 1937535 := bstep (se 1 (by rfl) ⟨1453151, by rfl⟩ : syracuseStep 1937535 = 2906303) B2906303
theorem B2906309 : Blo 1937435 2906309 := bbase (se 4 (by rfl) ⟨272466, by rfl⟩ : syracuseStep 2906309 = 544933) (by norm_num)
theorem B1937539 : Blo 1937435 1937539 := bstep (se 1 (by rfl) ⟨1453154, by rfl⟩ : syracuseStep 1937539 = 2906309) B2906309
theorem B3269605 : Blo 1937435 3269605 := bbase (se 4 (by rfl) ⟨306525, by rfl⟩ : syracuseStep 3269605 = 613051) (by norm_num)
theorem B4359473 : Blo 1937435 4359473 := bstep (se 2 (by rfl) ⟨1634802, by rfl⟩ : syracuseStep 4359473 = 3269605) B3269605
theorem B2906315 : Blo 1937435 2906315 := bstep (se 1 (by rfl) ⟨2179736, by rfl⟩ : syracuseStep 2906315 = 4359473) B4359473
theorem B1937543 : Blo 1937435 1937543 := bstep (se 1 (by rfl) ⟨1453157, by rfl⟩ : syracuseStep 1937543 = 2906315) B2906315
theorem B2179741 : Blo 1937435 2179741 := bbase (se 3 (by rfl) ⟨408701, by rfl⟩ : syracuseStep 2179741 = 817403) (by norm_num)
theorem B2906321 : Blo 1937435 2906321 := bstep (se 2 (by rfl) ⟨1089870, by rfl⟩ : syracuseStep 2906321 = 2179741) B2179741
theorem B1937547 : Blo 1937435 1937547 := bstep (se 1 (by rfl) ⟨1453160, by rfl⟩ : syracuseStep 1937547 = 2906321) B2906321
theorem B6539237 : Blo 1937435 6539237 := bbase (se 4 (by rfl) ⟨613053, by rfl⟩ : syracuseStep 6539237 = 1226107) (by norm_num)
theorem B4359491 : Blo 1937435 4359491 := bstep (se 1 (by rfl) ⟨3269618, by rfl⟩ : syracuseStep 4359491 = 6539237) B6539237
theorem B2906327 : Blo 1937435 2906327 := bstep (se 1 (by rfl) ⟨2179745, by rfl⟩ : syracuseStep 2906327 = 4359491) B4359491
theorem B1937551 : Blo 1937435 1937551 := bstep (se 1 (by rfl) ⟨1453163, by rfl⟩ : syracuseStep 1937551 = 2906327) B2906327
theorem B2906333 : Blo 1937435 2906333 := bbase (se 3 (by rfl) ⟨544937, by rfl⟩ : syracuseStep 2906333 = 1089875) (by norm_num)
theorem B1937555 : Blo 1937435 1937555 := bstep (se 1 (by rfl) ⟨1453166, by rfl⟩ : syracuseStep 1937555 = 2906333) B2906333
theorem B4359509 : Blo 1937435 4359509 := bbase (se 12 (by rfl) ⟨1596, by rfl⟩ : syracuseStep 4359509 = 3193) (by norm_num)
theorem B2906339 : Blo 1937435 2906339 := bstep (se 1 (by rfl) ⟨2179754, by rfl⟩ : syracuseStep 2906339 = 4359509) B4359509
theorem B1937559 : Blo 1937435 1937559 := bstep (se 1 (by rfl) ⟨1453169, by rfl⟩ : syracuseStep 1937559 = 2906339) B2906339
theorem B2069069 : Blo 1937435 2069069 := bbase (se 3 (by rfl) ⟨387950, by rfl⟩ : syracuseStep 2069069 = 775901) (by norm_num)
theorem B5517517 : Blo 1937435 5517517 := bstep (se 3 (by rfl) ⟨1034534, by rfl⟩ : syracuseStep 5517517 = 2069069) B2069069
theorem B7356689 : Blo 1937435 7356689 := bstep (se 2 (by rfl) ⟨2758758, by rfl⟩ : syracuseStep 7356689 = 5517517) B5517517
theorem B4904459 : Blo 1937435 4904459 := bstep (se 1 (by rfl) ⟨3678344, by rfl⟩ : syracuseStep 4904459 = 7356689) B7356689
theorem B3269639 : Blo 1937435 3269639 := bstep (se 1 (by rfl) ⟨2452229, by rfl⟩ : syracuseStep 3269639 = 4904459) B4904459
theorem B2179759 : Blo 1937435 2179759 := bstep (se 1 (by rfl) ⟨1634819, by rfl⟩ : syracuseStep 2179759 = 3269639) B3269639
theorem B2906345 : Blo 1937435 2906345 := bstep (se 2 (by rfl) ⟨1089879, by rfl⟩ : syracuseStep 2906345 = 2179759) B2179759
theorem B1937563 : Blo 1937435 1937563 := bstep (se 1 (by rfl) ⟨1453172, by rfl⟩ : syracuseStep 1937563 = 2906345) B2906345
theorem B2946005 : Blo 1937435 2946005 := bbase (se 7 (by rfl) ⟨34523, by rfl⟩ : syracuseStep 2946005 = 69047) (by norm_num)
theorem B1964003 : Blo 1937435 1964003 := bstep (se 1 (by rfl) ⟨1473002, by rfl⟩ : syracuseStep 1964003 = 2946005) B2946005
theorem B5237341 : Blo 1937435 5237341 := bstep (se 3 (by rfl) ⟨982001, by rfl⟩ : syracuseStep 5237341 = 1964003) B1964003
theorem B27932485 : Blo 1937435 27932485 := bstep (se 4 (by rfl) ⟨2618670, by rfl⟩ : syracuseStep 27932485 = 5237341) B5237341
theorem B37243313 : Blo 1937435 37243313 := bstep (se 2 (by rfl) ⟨13966242, by rfl⟩ : syracuseStep 37243313 = 27932485) B27932485
theorem B24828875 : Blo 1937435 24828875 := bstep (se 1 (by rfl) ⟨18621656, by rfl⟩ : syracuseStep 24828875 = 37243313) B37243313
theorem B16552583 : Blo 1937435 16552583 := bstep (se 1 (by rfl) ⟨12414437, by rfl⟩ : syracuseStep 16552583 = 24828875) B24828875
theorem B11035055 : Blo 1937435 11035055 := bstep (se 1 (by rfl) ⟨8276291, by rfl⟩ : syracuseStep 11035055 = 16552583) B16552583
theorem B7356703 : Blo 1937435 7356703 := bstep (se 1 (by rfl) ⟨5517527, by rfl⟩ : syracuseStep 7356703 = 11035055) B11035055
theorem B9808937 : Blo 1937435 9808937 := bstep (se 2 (by rfl) ⟨3678351, by rfl⟩ : syracuseStep 9808937 = 7356703) B7356703
theorem B6539291 : Blo 1937435 6539291 := bstep (se 1 (by rfl) ⟨4904468, by rfl⟩ : syracuseStep 6539291 = 9808937) B9808937
theorem B4359527 : Blo 1937435 4359527 := bstep (se 1 (by rfl) ⟨3269645, by rfl⟩ : syracuseStep 4359527 = 6539291) B6539291
theorem B2906351 : Blo 1937435 2906351 := bstep (se 1 (by rfl) ⟨2179763, by rfl⟩ : syracuseStep 2906351 = 4359527) B4359527
theorem B1937567 : Blo 1937435 1937567 := bstep (se 1 (by rfl) ⟨1453175, by rfl⟩ : syracuseStep 1937567 = 2906351) B2906351
theorem B2906357 : Blo 1937435 2906357 := bbase (se 5 (by rfl) ⟨136235, by rfl⟩ : syracuseStep 2906357 = 272471) (by norm_num)
theorem B1937571 : Blo 1937435 1937571 := bstep (se 1 (by rfl) ⟨1453178, by rfl⟩ : syracuseStep 1937571 = 2906357) B2906357
theorem B4479317 : Blo 1937435 4479317 := bbase (se 10 (by rfl) ⟨6561, by rfl⟩ : syracuseStep 4479317 = 13123) (by norm_num)
theorem B2986211 : Blo 1937435 2986211 := bstep (se 1 (by rfl) ⟨2239658, by rfl⟩ : syracuseStep 2986211 = 4479317) B4479317
theorem B7963229 : Blo 1937435 7963229 := bstep (se 3 (by rfl) ⟨1493105, by rfl⟩ : syracuseStep 7963229 = 2986211) B2986211
theorem B21235277 : Blo 1937435 21235277 := bstep (se 3 (by rfl) ⟨3981614, by rfl⟩ : syracuseStep 21235277 = 7963229) B7963229
theorem B14156851 : Blo 1937435 14156851 := bstep (se 1 (by rfl) ⟨10617638, by rfl⟩ : syracuseStep 14156851 = 21235277) B21235277
theorem B18875801 : Blo 1937435 18875801 := bstep (se 2 (by rfl) ⟨7078425, by rfl⟩ : syracuseStep 18875801 = 14156851) B14156851
theorem B50335469 : Blo 1937435 50335469 := bstep (se 3 (by rfl) ⟨9437900, by rfl⟩ : syracuseStep 50335469 = 18875801) B18875801
theorem B33556979 : Blo 1937435 33556979 := bstep (se 1 (by rfl) ⟨25167734, by rfl⟩ : syracuseStep 33556979 = 50335469) B50335469
theorem B22371319 : Blo 1937435 22371319 := bstep (se 1 (by rfl) ⟨16778489, by rfl⟩ : syracuseStep 22371319 = 33556979) B33556979
theorem B29828425 : Blo 1937435 29828425 := bstep (se 2 (by rfl) ⟨11185659, by rfl⟩ : syracuseStep 29828425 = 22371319) B22371319
theorem B39771233 : Blo 1937435 39771233 := bstep (se 2 (by rfl) ⟨14914212, by rfl⟩ : syracuseStep 39771233 = 29828425) B29828425
theorem B26514155 : Blo 1937435 26514155 := bstep (se 1 (by rfl) ⟨19885616, by rfl⟩ : syracuseStep 26514155 = 39771233) B39771233
theorem B70704413 : Blo 1937435 70704413 := bstep (se 3 (by rfl) ⟨13257077, by rfl⟩ : syracuseStep 70704413 = 26514155) B26514155
theorem B47136275 : Blo 1937435 47136275 := bstep (se 1 (by rfl) ⟨35352206, by rfl⟩ : syracuseStep 47136275 = 70704413) B70704413
theorem B31424183 : Blo 1937435 31424183 := bstep (se 1 (by rfl) ⟨23568137, by rfl⟩ : syracuseStep 31424183 = 47136275) B47136275
theorem B20949455 : Blo 1937435 20949455 := bstep (se 1 (by rfl) ⟨15712091, by rfl⟩ : syracuseStep 20949455 = 31424183) B31424183
theorem B13966303 : Blo 1937435 13966303 := bstep (se 1 (by rfl) ⟨10474727, by rfl⟩ : syracuseStep 13966303 = 20949455) B20949455
theorem B18621737 : Blo 1937435 18621737 := bstep (se 2 (by rfl) ⟨6983151, by rfl⟩ : syracuseStep 18621737 = 13966303) B13966303
theorem B12414491 : Blo 1937435 12414491 := bstep (se 1 (by rfl) ⟨9310868, by rfl⟩ : syracuseStep 12414491 = 18621737) B18621737
theorem B8276327 : Blo 1937435 8276327 := bstep (se 1 (by rfl) ⟨6207245, by rfl⟩ : syracuseStep 8276327 = 12414491) B12414491
theorem B5517551 : Blo 1937435 5517551 := bstep (se 1 (by rfl) ⟨4138163, by rfl⟩ : syracuseStep 5517551 = 8276327) B8276327
theorem B3678367 : Blo 1937435 3678367 := bstep (se 1 (by rfl) ⟨2758775, by rfl⟩ : syracuseStep 3678367 = 5517551) B5517551
theorem B4904489 : Blo 1937435 4904489 := bstep (se 2 (by rfl) ⟨1839183, by rfl⟩ : syracuseStep 4904489 = 3678367) B3678367
theorem B3269659 : Blo 1937435 3269659 := bstep (se 1 (by rfl) ⟨2452244, by rfl⟩ : syracuseStep 3269659 = 4904489) B4904489
theorem B4359545 : Blo 1937435 4359545 := bstep (se 2 (by rfl) ⟨1634829, by rfl⟩ : syracuseStep 4359545 = 3269659) B3269659
theorem B2906363 : Blo 1937435 2906363 := bstep (se 1 (by rfl) ⟨2179772, by rfl⟩ : syracuseStep 2906363 = 4359545) B4359545
theorem B1937575 : Blo 1937435 1937575 := bstep (se 1 (by rfl) ⟨1453181, by rfl⟩ : syracuseStep 1937575 = 2906363) B2906363
theorem B2179777 : Blo 1937435 2179777 := bbase (se 2 (by rfl) ⟨817416, by rfl⟩ : syracuseStep 2179777 = 1634833) (by norm_num)
theorem B2906369 : Blo 1937435 2906369 := bstep (se 2 (by rfl) ⟨1089888, by rfl⟩ : syracuseStep 2906369 = 2179777) B2179777
theorem B1937579 : Blo 1937435 1937579 := bstep (se 1 (by rfl) ⟨1453184, by rfl⟩ : syracuseStep 1937579 = 2906369) B2906369
theorem B4904509 : Blo 1937435 4904509 := bbase (se 3 (by rfl) ⟨919595, by rfl⟩ : syracuseStep 4904509 = 1839191) (by norm_num)
theorem B6539345 : Blo 1937435 6539345 := bstep (se 2 (by rfl) ⟨2452254, by rfl⟩ : syracuseStep 6539345 = 4904509) B4904509
theorem B4359563 : Blo 1937435 4359563 := bstep (se 1 (by rfl) ⟨3269672, by rfl⟩ : syracuseStep 4359563 = 6539345) B6539345
theorem B2906375 : Blo 1937435 2906375 := bstep (se 1 (by rfl) ⟨2179781, by rfl⟩ : syracuseStep 2906375 = 4359563) B4359563
theorem B1937583 : Blo 1937435 1937583 := bstep (se 1 (by rfl) ⟨1453187, by rfl⟩ : syracuseStep 1937583 = 2906375) B2906375
theorem B2906381 : Blo 1937435 2906381 := bbase (se 3 (by rfl) ⟨544946, by rfl⟩ : syracuseStep 2906381 = 1089893) (by norm_num)
theorem B1937587 : Blo 1937435 1937587 := bstep (se 1 (by rfl) ⟨1453190, by rfl⟩ : syracuseStep 1937587 = 2906381) B2906381
theorem B4359581 : Blo 1937435 4359581 := bbase (se 3 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 4359581 = 1634843) (by norm_num)
theorem B2906387 : Blo 1937435 2906387 := bstep (se 1 (by rfl) ⟨2179790, by rfl⟩ : syracuseStep 2906387 = 4359581) B4359581
theorem B1937591 : Blo 1937435 1937591 := bstep (se 1 (by rfl) ⟨1453193, by rfl⟩ : syracuseStep 1937591 = 2906387) B2906387
theorem B3269693 : Blo 1937435 3269693 := bbase (se 3 (by rfl) ⟨613067, by rfl⟩ : syracuseStep 3269693 = 1226135) (by norm_num)
theorem B2179795 : Blo 1937435 2179795 := bstep (se 1 (by rfl) ⟨1634846, by rfl⟩ : syracuseStep 2179795 = 3269693) B3269693
theorem B2906393 : Blo 1937435 2906393 := bstep (se 2 (by rfl) ⟨1089897, by rfl⟩ : syracuseStep 2906393 = 2179795) B2179795
theorem B1937595 : Blo 1937435 1937595 := bstep (se 1 (by rfl) ⟨1453196, by rfl⟩ : syracuseStep 1937595 = 2906393) B2906393
theorem B3103661 : Blo 1937435 3103661 := bbase (se 3 (by rfl) ⟨581936, by rfl⟩ : syracuseStep 3103661 = 1163873) (by norm_num)
theorem B2069107 : Blo 1937435 2069107 := bstep (se 1 (by rfl) ⟨1551830, by rfl⟩ : syracuseStep 2069107 = 3103661) B3103661
theorem B11035237 : Blo 1937435 11035237 := bstep (se 4 (by rfl) ⟨1034553, by rfl⟩ : syracuseStep 11035237 = 2069107) B2069107
theorem B14713649 : Blo 1937435 14713649 := bstep (se 2 (by rfl) ⟨5517618, by rfl⟩ : syracuseStep 14713649 = 11035237) B11035237
theorem B9809099 : Blo 1937435 9809099 := bstep (se 1 (by rfl) ⟨7356824, by rfl⟩ : syracuseStep 9809099 = 14713649) B14713649
theorem B6539399 : Blo 1937435 6539399 := bstep (se 1 (by rfl) ⟨4904549, by rfl⟩ : syracuseStep 6539399 = 9809099) B9809099
theorem B4359599 : Blo 1937435 4359599 := bstep (se 1 (by rfl) ⟨3269699, by rfl⟩ : syracuseStep 4359599 = 6539399) B6539399
theorem B2906399 : Blo 1937435 2906399 := bstep (se 1 (by rfl) ⟨2179799, by rfl⟩ : syracuseStep 2906399 = 4359599) B4359599
theorem B1937599 : Blo 1937435 1937599 := bstep (se 1 (by rfl) ⟨1453199, by rfl⟩ : syracuseStep 1937599 = 2906399) B2906399
theorem B2906405 : Blo 1937435 2906405 := bbase (se 4 (by rfl) ⟨272475, by rfl⟩ : syracuseStep 2906405 = 544951) (by norm_num)
theorem B1937603 : Blo 1937435 1937603 := bstep (se 1 (by rfl) ⟨1453202, by rfl⟩ : syracuseStep 1937603 = 2906405) B2906405
theorem B2452285 : Blo 1937435 2452285 := bbase (se 3 (by rfl) ⟨459803, by rfl⟩ : syracuseStep 2452285 = 919607) (by norm_num)
theorem B3269713 : Blo 1937435 3269713 := bstep (se 2 (by rfl) ⟨1226142, by rfl⟩ : syracuseStep 3269713 = 2452285) B2452285
theorem B4359617 : Blo 1937435 4359617 := bstep (se 2 (by rfl) ⟨1634856, by rfl⟩ : syracuseStep 4359617 = 3269713) B3269713
theorem B2906411 : Blo 1937435 2906411 := bstep (se 1 (by rfl) ⟨2179808, by rfl⟩ : syracuseStep 2906411 = 4359617) B4359617
theorem B1937607 : Blo 1937435 1937607 := bstep (se 1 (by rfl) ⟨1453205, by rfl⟩ : syracuseStep 1937607 = 2906411) B2906411
theorem B2179813 : Blo 1937435 2179813 := bbase (se 4 (by rfl) ⟨204357, by rfl⟩ : syracuseStep 2179813 = 408715) (by norm_num)
theorem B2906417 : Blo 1937435 2906417 := bstep (se 2 (by rfl) ⟨1089906, by rfl⟩ : syracuseStep 2906417 = 2179813) B2179813
theorem B1937611 : Blo 1937435 1937611 := bstep (se 1 (by rfl) ⟨1453208, by rfl⟩ : syracuseStep 1937611 = 2906417) B2906417
theorem B5972549 : Blo 1937435 5972549 := bbase (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) (by norm_num)
theorem B15926797 : Blo 1937435 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B21235729 : Blo 1937435 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B28314305 : Blo 1937435 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B18876203 : Blo 1937435 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B12584135 : Blo 1937435 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B8389423 : Blo 1937435 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B11185897 : Blo 1937435 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B14914529 : Blo 1937435 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B9943019 : Blo 1937435 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B6628679 : Blo 1937435 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B4419119 : Blo 1937435 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B2946079 : Blo 1937435 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B3928105 : Blo 1937435 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B5237473 : Blo 1937435 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B6983297 : Blo 1937435 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B4655531 : Blo 1937435 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B3103687 : Blo 1937435 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B4138249 : Blo 1937435 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B5517665 : Blo 1937435 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B3678443 : Blo 1937435 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B2452295 : Blo 1937435 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B6539453 : Blo 1937435 6539453 := bstep (se 3 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 6539453 = 2452295) B2452295
theorem B4359635 : Blo 1937435 4359635 := bstep (se 1 (by rfl) ⟨3269726, by rfl⟩ : syracuseStep 4359635 = 6539453) B6539453
theorem B2906423 : Blo 1937435 2906423 := bstep (se 1 (by rfl) ⟨2179817, by rfl⟩ : syracuseStep 2906423 = 4359635) B4359635
theorem B1937615 : Blo 1937435 1937615 := bstep (se 1 (by rfl) ⟨1453211, by rfl⟩ : syracuseStep 1937615 = 2906423) B2906423
theorem B2906429 : Blo 1937435 2906429 := bbase (se 3 (by rfl) ⟨544955, by rfl⟩ : syracuseStep 2906429 = 1089911) (by norm_num)
theorem B1937619 : Blo 1937435 1937619 := bstep (se 1 (by rfl) ⟨1453214, by rfl⟩ : syracuseStep 1937619 = 2906429) B2906429
theorem B4359653 : Blo 1937435 4359653 := bbase (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) (by norm_num)
theorem B2906435 : Blo 1937435 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B1937623 : Blo 1937435 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B4904621 : Blo 1937435 4904621 := bbase (se 3 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 4904621 = 1839233) (by norm_num)
theorem B3269747 : Blo 1937435 3269747 := bstep (se 1 (by rfl) ⟨2452310, by rfl⟩ : syracuseStep 3269747 = 4904621) B4904621
theorem B2179831 : Blo 1937435 2179831 := bstep (se 1 (by rfl) ⟨1634873, by rfl⟩ : syracuseStep 2179831 = 3269747) B3269747
theorem B2906441 : Blo 1937435 2906441 := bstep (se 2 (by rfl) ⟨1089915, by rfl⟩ : syracuseStep 2906441 = 2179831) B2179831
theorem B1937627 : Blo 1937435 1937627 := bstep (se 1 (by rfl) ⟨1453220, by rfl⟩ : syracuseStep 1937627 = 2906441) B2906441
theorem B3491677 : Blo 1937435 3491677 := bbase (se 3 (by rfl) ⟨654689, by rfl⟩ : syracuseStep 3491677 = 1309379) (by norm_num)
theorem B4655569 : Blo 1937435 4655569 := bstep (se 2 (by rfl) ⟨1745838, by rfl⟩ : syracuseStep 4655569 = 3491677) B3491677
theorem B6207425 : Blo 1937435 6207425 := bstep (se 2 (by rfl) ⟨2327784, by rfl⟩ : syracuseStep 6207425 = 4655569) B4655569
theorem B4138283 : Blo 1937435 4138283 := bstep (se 1 (by rfl) ⟨3103712, by rfl⟩ : syracuseStep 4138283 = 6207425) B6207425
theorem B2758855 : Blo 1937435 2758855 := bstep (se 1 (by rfl) ⟨2069141, by rfl⟩ : syracuseStep 2758855 = 4138283) B4138283
theorem B3678473 : Blo 1937435 3678473 := bstep (se 2 (by rfl) ⟨1379427, by rfl⟩ : syracuseStep 3678473 = 2758855) B2758855
theorem B9809261 : Blo 1937435 9809261 := bstep (se 3 (by rfl) ⟨1839236, by rfl⟩ : syracuseStep 9809261 = 3678473) B3678473
theorem B6539507 : Blo 1937435 6539507 := bstep (se 1 (by rfl) ⟨4904630, by rfl⟩ : syracuseStep 6539507 = 9809261) B9809261
theorem B4359671 : Blo 1937435 4359671 := bstep (se 1 (by rfl) ⟨3269753, by rfl⟩ : syracuseStep 4359671 = 6539507) B6539507
theorem B2906447 : Blo 1937435 2906447 := bstep (se 1 (by rfl) ⟨2179835, by rfl⟩ : syracuseStep 2906447 = 4359671) B4359671
theorem B1937631 : Blo 1937435 1937631 := bstep (se 1 (by rfl) ⟨1453223, by rfl⟩ : syracuseStep 1937631 = 2906447) B2906447
theorem B2906453 : Blo 1937435 2906453 := bbase (se 10 (by rfl) ⟨4257, by rfl⟩ : syracuseStep 2906453 = 8515) (by norm_num)
theorem B1937635 : Blo 1937435 1937635 := bstep (se 1 (by rfl) ⟨1453226, by rfl⟩ : syracuseStep 1937635 = 2906453) B2906453
theorem B5517733 : Blo 1937435 5517733 := bbase (se 4 (by rfl) ⟨517287, by rfl⟩ : syracuseStep 5517733 = 1034575) (by norm_num)
theorem B7356977 : Blo 1937435 7356977 := bstep (se 2 (by rfl) ⟨2758866, by rfl⟩ : syracuseStep 7356977 = 5517733) B5517733
theorem B4904651 : Blo 1937435 4904651 := bstep (se 1 (by rfl) ⟨3678488, by rfl⟩ : syracuseStep 4904651 = 7356977) B7356977
theorem B3269767 : Blo 1937435 3269767 := bstep (se 1 (by rfl) ⟨2452325, by rfl⟩ : syracuseStep 3269767 = 4904651) B4904651
theorem B4359689 : Blo 1937435 4359689 := bstep (se 2 (by rfl) ⟨1634883, by rfl⟩ : syracuseStep 4359689 = 3269767) B3269767
theorem B2906459 : Blo 1937435 2906459 := bstep (se 1 (by rfl) ⟨2179844, by rfl⟩ : syracuseStep 2906459 = 4359689) B4359689
theorem B1937639 : Blo 1937435 1937639 := bstep (se 1 (by rfl) ⟨1453229, by rfl⟩ : syracuseStep 1937639 = 2906459) B2906459
theorem B2179849 : Blo 1937435 2179849 := bbase (se 2 (by rfl) ⟨817443, by rfl⟩ : syracuseStep 2179849 = 1634887) (by norm_num)
theorem B2906465 : Blo 1937435 2906465 := bstep (se 2 (by rfl) ⟨1089924, by rfl⟩ : syracuseStep 2906465 = 2179849) B2179849
theorem B1937643 : Blo 1937435 1937643 := bstep (se 1 (by rfl) ⟨1453232, by rfl⟩ : syracuseStep 1937643 = 2906465) B2906465
theorem B3728693 : Blo 1937435 3728693 := bbase (se 5 (by rfl) ⟨174782, by rfl⟩ : syracuseStep 3728693 = 349565) (by norm_num)
theorem B9943181 : Blo 1937435 9943181 := bstep (se 3 (by rfl) ⟨1864346, by rfl⟩ : syracuseStep 9943181 = 3728693) B3728693
theorem B6628787 : Blo 1937435 6628787 := bstep (se 1 (by rfl) ⟨4971590, by rfl⟩ : syracuseStep 6628787 = 9943181) B9943181
theorem B4419191 : Blo 1937435 4419191 := bstep (se 1 (by rfl) ⟨3314393, by rfl⟩ : syracuseStep 4419191 = 6628787) B6628787
theorem B2946127 : Blo 1937435 2946127 := bstep (se 1 (by rfl) ⟨2209595, by rfl⟩ : syracuseStep 2946127 = 4419191) B4419191
theorem B3928169 : Blo 1937435 3928169 := bstep (se 2 (by rfl) ⟨1473063, by rfl⟩ : syracuseStep 3928169 = 2946127) B2946127
theorem B2618779 : Blo 1937435 2618779 := bstep (se 1 (by rfl) ⟨1964084, by rfl⟩ : syracuseStep 2618779 = 3928169) B3928169
theorem B3491705 : Blo 1937435 3491705 := bstep (se 2 (by rfl) ⟨1309389, by rfl⟩ : syracuseStep 3491705 = 2618779) B2618779
theorem B9311213 : Blo 1937435 9311213 := bstep (se 3 (by rfl) ⟨1745852, by rfl⟩ : syracuseStep 9311213 = 3491705) B3491705
theorem B24829901 : Blo 1937435 24829901 := bstep (se 3 (by rfl) ⟨4655606, by rfl⟩ : syracuseStep 24829901 = 9311213) B9311213
theorem B16553267 : Blo 1937435 16553267 := bstep (se 1 (by rfl) ⟨12414950, by rfl⟩ : syracuseStep 16553267 = 24829901) B24829901
theorem B11035511 : Blo 1937435 11035511 := bstep (se 1 (by rfl) ⟨8276633, by rfl⟩ : syracuseStep 11035511 = 16553267) B16553267
theorem B7357007 : Blo 1937435 7357007 := bstep (se 1 (by rfl) ⟨5517755, by rfl⟩ : syracuseStep 7357007 = 11035511) B11035511
theorem B4904671 : Blo 1937435 4904671 := bstep (se 1 (by rfl) ⟨3678503, by rfl⟩ : syracuseStep 4904671 = 7357007) B7357007
theorem B6539561 : Blo 1937435 6539561 := bstep (se 2 (by rfl) ⟨2452335, by rfl⟩ : syracuseStep 6539561 = 4904671) B4904671
theorem B4359707 : Blo 1937435 4359707 := bstep (se 1 (by rfl) ⟨3269780, by rfl⟩ : syracuseStep 4359707 = 6539561) B6539561
theorem B2906471 : Blo 1937435 2906471 := bstep (se 1 (by rfl) ⟨2179853, by rfl⟩ : syracuseStep 2906471 = 4359707) B4359707
theorem B1937647 : Blo 1937435 1937647 := bstep (se 1 (by rfl) ⟨1453235, by rfl⟩ : syracuseStep 1937647 = 2906471) B2906471
theorem B2906477 : Blo 1937435 2906477 := bbase (se 3 (by rfl) ⟨544964, by rfl⟩ : syracuseStep 2906477 = 1089929) (by norm_num)
theorem B1937651 : Blo 1937435 1937651 := bstep (se 1 (by rfl) ⟨1453238, by rfl⟩ : syracuseStep 1937651 = 2906477) B2906477
theorem B4359725 : Blo 1937435 4359725 := bbase (se 3 (by rfl) ⟨817448, by rfl⟩ : syracuseStep 4359725 = 1634897) (by norm_num)
theorem B2906483 : Blo 1937435 2906483 := bstep (se 1 (by rfl) ⟨2179862, by rfl⟩ : syracuseStep 2906483 = 4359725) B4359725
theorem B1937655 : Blo 1937435 1937655 := bstep (se 1 (by rfl) ⟨1453241, by rfl⟩ : syracuseStep 1937655 = 2906483) B2906483
theorem B16779221 : Blo 1937435 16779221 := bbase (se 7 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 16779221 = 393263) (by norm_num)
theorem B11186147 : Blo 1937435 11186147 := bstep (se 1 (by rfl) ⟨8389610, by rfl⟩ : syracuseStep 11186147 = 16779221) B16779221
theorem B7457431 : Blo 1937435 7457431 := bstep (se 1 (by rfl) ⟨5593073, by rfl⟩ : syracuseStep 7457431 = 11186147) B11186147
theorem B9943241 : Blo 1937435 9943241 := bstep (se 2 (by rfl) ⟨3728715, by rfl⟩ : syracuseStep 9943241 = 7457431) B7457431
theorem B26515309 : Blo 1937435 26515309 := bstep (se 3 (by rfl) ⟨4971620, by rfl⟩ : syracuseStep 26515309 = 9943241) B9943241
theorem B35353745 : Blo 1937435 35353745 := bstep (se 2 (by rfl) ⟨13257654, by rfl⟩ : syracuseStep 35353745 = 26515309) B26515309
theorem B23569163 : Blo 1937435 23569163 := bstep (se 1 (by rfl) ⟨17676872, by rfl⟩ : syracuseStep 23569163 = 35353745) B35353745
theorem B15712775 : Blo 1937435 15712775 := bstep (se 1 (by rfl) ⟨11784581, by rfl⟩ : syracuseStep 15712775 = 23569163) B23569163
theorem B10475183 : Blo 1937435 10475183 := bstep (se 1 (by rfl) ⟨7856387, by rfl⟩ : syracuseStep 10475183 = 15712775) B15712775
theorem B27933821 : Blo 1937435 27933821 := bstep (se 3 (by rfl) ⟨5237591, by rfl⟩ : syracuseStep 27933821 = 10475183) B10475183
theorem B18622547 : Blo 1937435 18622547 := bstep (se 1 (by rfl) ⟨13966910, by rfl⟩ : syracuseStep 18622547 = 27933821) B27933821
theorem B12415031 : Blo 1937435 12415031 := bstep (se 1 (by rfl) ⟨9311273, by rfl⟩ : syracuseStep 12415031 = 18622547) B18622547
theorem B8276687 : Blo 1937435 8276687 := bstep (se 1 (by rfl) ⟨6207515, by rfl⟩ : syracuseStep 8276687 = 12415031) B12415031
theorem B5517791 : Blo 1937435 5517791 := bstep (se 1 (by rfl) ⟨4138343, by rfl⟩ : syracuseStep 5517791 = 8276687) B8276687
theorem B3678527 : Blo 1937435 3678527 := bstep (se 1 (by rfl) ⟨2758895, by rfl⟩ : syracuseStep 3678527 = 5517791) B5517791
theorem B2452351 : Blo 1937435 2452351 := bstep (se 1 (by rfl) ⟨1839263, by rfl⟩ : syracuseStep 2452351 = 3678527) B3678527
theorem B3269801 : Blo 1937435 3269801 := bstep (se 2 (by rfl) ⟨1226175, by rfl⟩ : syracuseStep 3269801 = 2452351) B2452351
theorem B2179867 : Blo 1937435 2179867 := bstep (se 1 (by rfl) ⟨1634900, by rfl⟩ : syracuseStep 2179867 = 3269801) B3269801
theorem B2906489 : Blo 1937435 2906489 := bstep (se 2 (by rfl) ⟨1089933, by rfl⟩ : syracuseStep 2906489 = 2179867) B2179867
theorem B1937659 : Blo 1937435 1937659 := bstep (se 1 (by rfl) ⟨1453244, by rfl⟩ : syracuseStep 1937659 = 2906489) B2906489
theorem B4655645 : Blo 1937435 4655645 := bbase (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) (by norm_num)
theorem B3103763 : Blo 1937435 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B33106805 : Blo 1937435 33106805 := bstep (se 5 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 33106805 = 3103763) B3103763
theorem B22071203 : Blo 1937435 22071203 := bstep (se 1 (by rfl) ⟨16553402, by rfl⟩ : syracuseStep 22071203 = 33106805) B33106805
theorem B14714135 : Blo 1937435 14714135 := bstep (se 1 (by rfl) ⟨11035601, by rfl⟩ : syracuseStep 14714135 = 22071203) B22071203
theorem B9809423 : Blo 1937435 9809423 := bstep (se 1 (by rfl) ⟨7357067, by rfl⟩ : syracuseStep 9809423 = 14714135) B14714135
theorem B6539615 : Blo 1937435 6539615 := bstep (se 1 (by rfl) ⟨4904711, by rfl⟩ : syracuseStep 6539615 = 9809423) B9809423
theorem B4359743 : Blo 1937435 4359743 := bstep (se 1 (by rfl) ⟨3269807, by rfl⟩ : syracuseStep 4359743 = 6539615) B6539615
theorem B2906495 : Blo 1937435 2906495 := bstep (se 1 (by rfl) ⟨2179871, by rfl⟩ : syracuseStep 2906495 = 4359743) B4359743
theorem B1937663 : Blo 1937435 1937663 := bstep (se 1 (by rfl) ⟨1453247, by rfl⟩ : syracuseStep 1937663 = 2906495) B2906495
theorem B2906501 : Blo 1937435 2906501 := bbase (se 4 (by rfl) ⟨272484, by rfl⟩ : syracuseStep 2906501 = 544969) (by norm_num)
theorem B1937667 : Blo 1937435 1937667 := bstep (se 1 (by rfl) ⟨1453250, by rfl⟩ : syracuseStep 1937667 = 2906501) B2906501
theorem B3269821 : Blo 1937435 3269821 := bbase (se 3 (by rfl) ⟨613091, by rfl⟩ : syracuseStep 3269821 = 1226183) (by norm_num)
theorem B4359761 : Blo 1937435 4359761 := bstep (se 2 (by rfl) ⟨1634910, by rfl⟩ : syracuseStep 4359761 = 3269821) B3269821
theorem B2906507 : Blo 1937435 2906507 := bstep (se 1 (by rfl) ⟨2179880, by rfl⟩ : syracuseStep 2906507 = 4359761) B4359761
theorem B1937671 : Blo 1937435 1937671 := bstep (se 1 (by rfl) ⟨1453253, by rfl⟩ : syracuseStep 1937671 = 2906507) B2906507
theorem B2179885 : Blo 1937435 2179885 := bbase (se 3 (by rfl) ⟨408728, by rfl⟩ : syracuseStep 2179885 = 817457) (by norm_num)
theorem B2906513 : Blo 1937435 2906513 := bstep (se 2 (by rfl) ⟨1089942, by rfl⟩ : syracuseStep 2906513 = 2179885) B2179885
theorem B1937675 : Blo 1937435 1937675 := bstep (se 1 (by rfl) ⟨1453256, by rfl⟩ : syracuseStep 1937675 = 2906513) B2906513
theorem B6539669 : Blo 1937435 6539669 := bbase (se 6 (by rfl) ⟨153273, by rfl⟩ : syracuseStep 6539669 = 306547) (by norm_num)
theorem B4359779 : Blo 1937435 4359779 := bstep (se 1 (by rfl) ⟨3269834, by rfl⟩ : syracuseStep 4359779 = 6539669) B6539669
theorem B2906519 : Blo 1937435 2906519 := bstep (se 1 (by rfl) ⟨2179889, by rfl⟩ : syracuseStep 2906519 = 4359779) B4359779
theorem B1937679 : Blo 1937435 1937679 := bstep (se 1 (by rfl) ⟨1453259, by rfl⟩ : syracuseStep 1937679 = 2906519) B2906519
theorem B2906525 : Blo 1937435 2906525 := bbase (se 3 (by rfl) ⟨544973, by rfl⟩ : syracuseStep 2906525 = 1089947) (by norm_num)
theorem B1937683 : Blo 1937435 1937683 := bstep (se 1 (by rfl) ⟨1453262, by rfl⟩ : syracuseStep 1937683 = 2906525) B2906525
theorem B4359797 : Blo 1937435 4359797 := bbase (se 5 (by rfl) ⟨204365, by rfl⟩ : syracuseStep 4359797 = 408731) (by norm_num)
theorem B2906531 : Blo 1937435 2906531 := bstep (se 1 (by rfl) ⟨2179898, by rfl⟩ : syracuseStep 2906531 = 4359797) B4359797
theorem B1937687 : Blo 1937435 1937687 := bstep (se 1 (by rfl) ⟨1453265, by rfl⟩ : syracuseStep 1937687 = 2906531) B2906531
theorem B5892389 : Blo 1937435 5892389 := bbase (se 4 (by rfl) ⟨552411, by rfl⟩ : syracuseStep 5892389 = 1104823) (by norm_num)
theorem B3928259 : Blo 1937435 3928259 := bstep (se 1 (by rfl) ⟨2946194, by rfl⟩ : syracuseStep 3928259 = 5892389) B5892389
theorem B2618839 : Blo 1937435 2618839 := bstep (se 1 (by rfl) ⟨1964129, by rfl⟩ : syracuseStep 2618839 = 3928259) B3928259
theorem B3491785 : Blo 1937435 3491785 := bstep (se 2 (by rfl) ⟨1309419, by rfl⟩ : syracuseStep 3491785 = 2618839) B2618839
theorem B4655713 : Blo 1937435 4655713 := bstep (se 2 (by rfl) ⟨1745892, by rfl⟩ : syracuseStep 4655713 = 3491785) B3491785
theorem B6207617 : Blo 1937435 6207617 := bstep (se 2 (by rfl) ⟨2327856, by rfl⟩ : syracuseStep 6207617 = 4655713) B4655713
theorem B16553645 : Blo 1937435 16553645 := bstep (se 3 (by rfl) ⟨3103808, by rfl⟩ : syracuseStep 16553645 = 6207617) B6207617
theorem B11035763 : Blo 1937435 11035763 := bstep (se 1 (by rfl) ⟨8276822, by rfl⟩ : syracuseStep 11035763 = 16553645) B16553645
theorem B7357175 : Blo 1937435 7357175 := bstep (se 1 (by rfl) ⟨5517881, by rfl⟩ : syracuseStep 7357175 = 11035763) B11035763
theorem B4904783 : Blo 1937435 4904783 := bstep (se 1 (by rfl) ⟨3678587, by rfl⟩ : syracuseStep 4904783 = 7357175) B7357175
theorem B3269855 : Blo 1937435 3269855 := bstep (se 1 (by rfl) ⟨2452391, by rfl⟩ : syracuseStep 3269855 = 4904783) B4904783
theorem B2179903 : Blo 1937435 2179903 := bstep (se 1 (by rfl) ⟨1634927, by rfl⟩ : syracuseStep 2179903 = 3269855) B3269855
theorem B2906537 : Blo 1937435 2906537 := bstep (se 2 (by rfl) ⟨1089951, by rfl⟩ : syracuseStep 2906537 = 2179903) B2179903
theorem B1937691 : Blo 1937435 1937691 := bstep (se 1 (by rfl) ⟨1453268, by rfl⟩ : syracuseStep 1937691 = 2906537) B2906537
theorem B7357189 : Blo 1937435 7357189 := bbase (se 4 (by rfl) ⟨689736, by rfl⟩ : syracuseStep 7357189 = 1379473) (by norm_num)
theorem B9809585 : Blo 1937435 9809585 := bstep (se 2 (by rfl) ⟨3678594, by rfl⟩ : syracuseStep 9809585 = 7357189) B7357189
theorem B6539723 : Blo 1937435 6539723 := bstep (se 1 (by rfl) ⟨4904792, by rfl⟩ : syracuseStep 6539723 = 9809585) B9809585
theorem B4359815 : Blo 1937435 4359815 := bstep (se 1 (by rfl) ⟨3269861, by rfl⟩ : syracuseStep 4359815 = 6539723) B6539723
theorem B2906543 : Blo 1937435 2906543 := bstep (se 1 (by rfl) ⟨2179907, by rfl⟩ : syracuseStep 2906543 = 4359815) B4359815
theorem B1937695 : Blo 1937435 1937695 := bstep (se 1 (by rfl) ⟨1453271, by rfl⟩ : syracuseStep 1937695 = 2906543) B2906543
theorem B2906549 : Blo 1937435 2906549 := bbase (se 5 (by rfl) ⟨136244, by rfl⟩ : syracuseStep 2906549 = 272489) (by norm_num)
theorem B1937699 : Blo 1937435 1937699 := bstep (se 1 (by rfl) ⟨1453274, by rfl⟩ : syracuseStep 1937699 = 2906549) B2906549
theorem B4904813 : Blo 1937435 4904813 := bbase (se 3 (by rfl) ⟨919652, by rfl⟩ : syracuseStep 4904813 = 1839305) (by norm_num)
theorem B3269875 : Blo 1937435 3269875 := bstep (se 1 (by rfl) ⟨2452406, by rfl⟩ : syracuseStep 3269875 = 4904813) B4904813
theorem B4359833 : Blo 1937435 4359833 := bstep (se 2 (by rfl) ⟨1634937, by rfl⟩ : syracuseStep 4359833 = 3269875) B3269875
theorem B2906555 : Blo 1937435 2906555 := bstep (se 1 (by rfl) ⟨2179916, by rfl⟩ : syracuseStep 2906555 = 4359833) B4359833
theorem B1937703 : Blo 1937435 1937703 := bstep (se 1 (by rfl) ⟨1453277, by rfl⟩ : syracuseStep 1937703 = 2906555) B2906555
theorem B2179921 : Blo 1937435 2179921 := bbase (se 2 (by rfl) ⟨817470, by rfl⟩ : syracuseStep 2179921 = 1634941) (by norm_num)
theorem B2906561 : Blo 1937435 2906561 := bstep (se 2 (by rfl) ⟨1089960, by rfl⟩ : syracuseStep 2906561 = 2179921) B2179921
theorem B1937707 : Blo 1937435 1937707 := bstep (se 1 (by rfl) ⟨1453280, by rfl⟩ : syracuseStep 1937707 = 2906561) B2906561
theorem B2327881 : Blo 1937435 2327881 := bbase (se 2 (by rfl) ⟨872955, by rfl⟩ : syracuseStep 2327881 = 1745911) (by norm_num)
theorem B3103841 : Blo 1937435 3103841 := bstep (se 2 (by rfl) ⟨1163940, by rfl⟩ : syracuseStep 3103841 = 2327881) B2327881
theorem B2069227 : Blo 1937435 2069227 := bstep (se 1 (by rfl) ⟨1551920, by rfl⟩ : syracuseStep 2069227 = 3103841) B3103841
theorem B2758969 : Blo 1937435 2758969 := bstep (se 2 (by rfl) ⟨1034613, by rfl⟩ : syracuseStep 2758969 = 2069227) B2069227
theorem B3678625 : Blo 1937435 3678625 := bstep (se 2 (by rfl) ⟨1379484, by rfl⟩ : syracuseStep 3678625 = 2758969) B2758969
theorem B4904833 : Blo 1937435 4904833 := bstep (se 2 (by rfl) ⟨1839312, by rfl⟩ : syracuseStep 4904833 = 3678625) B3678625
theorem B6539777 : Blo 1937435 6539777 := bstep (se 2 (by rfl) ⟨2452416, by rfl⟩ : syracuseStep 6539777 = 4904833) B4904833
theorem B4359851 : Blo 1937435 4359851 := bstep (se 1 (by rfl) ⟨3269888, by rfl⟩ : syracuseStep 4359851 = 6539777) B6539777
theorem B2906567 : Blo 1937435 2906567 := bstep (se 1 (by rfl) ⟨2179925, by rfl⟩ : syracuseStep 2906567 = 4359851) B4359851
theorem B1937711 : Blo 1937435 1937711 := bstep (se 1 (by rfl) ⟨1453283, by rfl⟩ : syracuseStep 1937711 = 2906567) B2906567
theorem B2906573 : Blo 1937435 2906573 := bbase (se 3 (by rfl) ⟨544982, by rfl⟩ : syracuseStep 2906573 = 1089965) (by norm_num)
theorem B1937715 : Blo 1937435 1937715 := bstep (se 1 (by rfl) ⟨1453286, by rfl⟩ : syracuseStep 1937715 = 2906573) B2906573
theorem B4359869 : Blo 1937435 4359869 := bbase (se 3 (by rfl) ⟨817475, by rfl⟩ : syracuseStep 4359869 = 1634951) (by norm_num)
theorem B2906579 : Blo 1937435 2906579 := bstep (se 1 (by rfl) ⟨2179934, by rfl⟩ : syracuseStep 2906579 = 4359869) B4359869
theorem B1937719 : Blo 1937435 1937719 := bstep (se 1 (by rfl) ⟨1453289, by rfl⟩ : syracuseStep 1937719 = 2906579) B2906579
theorem B3269909 : Blo 1937435 3269909 := bbase (se 6 (by rfl) ⟨76638, by rfl⟩ : syracuseStep 3269909 = 153277) (by norm_num)
theorem B2179939 : Blo 1937435 2179939 := bstep (se 1 (by rfl) ⟨1634954, by rfl⟩ : syracuseStep 2179939 = 3269909) B3269909
theorem B2906585 : Blo 1937435 2906585 := bstep (se 2 (by rfl) ⟨1089969, by rfl⟩ : syracuseStep 2906585 = 2179939) B2179939
theorem B1937723 : Blo 1937435 1937723 := bstep (se 1 (by rfl) ⟨1453292, by rfl⟩ : syracuseStep 1937723 = 2906585) B2906585
theorem B2519813 : Blo 1937435 2519813 := bbase (se 4 (by rfl) ⟨236232, by rfl⟩ : syracuseStep 2519813 = 472465) (by norm_num)
theorem B6719501 : Blo 1937435 6719501 := bstep (se 3 (by rfl) ⟨1259906, by rfl⟩ : syracuseStep 6719501 = 2519813) B2519813
theorem B4479667 : Blo 1937435 4479667 := bstep (se 1 (by rfl) ⟨3359750, by rfl⟩ : syracuseStep 4479667 = 6719501) B6719501
theorem B95566229 : Blo 1937435 95566229 := bstep (se 6 (by rfl) ⟨2239833, by rfl⟩ : syracuseStep 95566229 = 4479667) B4479667
theorem B63710819 : Blo 1937435 63710819 := bstep (se 1 (by rfl) ⟨47783114, by rfl⟩ : syracuseStep 63710819 = 95566229) B95566229
theorem B42473879 : Blo 1937435 42473879 := bstep (se 1 (by rfl) ⟨31855409, by rfl⟩ : syracuseStep 42473879 = 63710819) B63710819
theorem B28315919 : Blo 1937435 28315919 := bstep (se 1 (by rfl) ⟨21236939, by rfl⟩ : syracuseStep 28315919 = 42473879) B42473879
theorem B18877279 : Blo 1937435 18877279 := bstep (se 1 (by rfl) ⟨14157959, by rfl⟩ : syracuseStep 18877279 = 28315919) B28315919
theorem B25169705 : Blo 1937435 25169705 := bstep (se 2 (by rfl) ⟨9438639, by rfl⟩ : syracuseStep 25169705 = 18877279) B18877279
theorem B16779803 : Blo 1937435 16779803 := bstep (se 1 (by rfl) ⟨12584852, by rfl⟩ : syracuseStep 16779803 = 25169705) B25169705
theorem B44746141 : Blo 1937435 44746141 := bstep (se 3 (by rfl) ⟨8389901, by rfl⟩ : syracuseStep 44746141 = 16779803) B16779803
theorem B59661521 : Blo 1937435 59661521 := bstep (se 2 (by rfl) ⟨22373070, by rfl⟩ : syracuseStep 59661521 = 44746141) B44746141
theorem B39774347 : Blo 1937435 39774347 := bstep (se 1 (by rfl) ⟨29830760, by rfl⟩ : syracuseStep 39774347 = 59661521) B59661521
theorem B26516231 : Blo 1937435 26516231 := bstep (se 1 (by rfl) ⟨19887173, by rfl⟩ : syracuseStep 26516231 = 39774347) B39774347
theorem B17677487 : Blo 1937435 17677487 := bstep (se 1 (by rfl) ⟨13258115, by rfl⟩ : syracuseStep 17677487 = 26516231) B26516231
theorem B47139965 : Blo 1937435 47139965 := bstep (se 3 (by rfl) ⟨8838743, by rfl⟩ : syracuseStep 47139965 = 17677487) B17677487
theorem B31426643 : Blo 1937435 31426643 := bstep (se 1 (by rfl) ⟨23569982, by rfl⟩ : syracuseStep 31426643 = 47139965) B47139965
theorem B20951095 : Blo 1937435 20951095 := bstep (se 1 (by rfl) ⟨15713321, by rfl⟩ : syracuseStep 20951095 = 31426643) B31426643
theorem B27934793 : Blo 1937435 27934793 := bstep (se 2 (by rfl) ⟨10475547, by rfl⟩ : syracuseStep 27934793 = 20951095) B20951095
theorem B18623195 : Blo 1937435 18623195 := bstep (se 1 (by rfl) ⟨13967396, by rfl⟩ : syracuseStep 18623195 = 27934793) B27934793
theorem B12415463 : Blo 1937435 12415463 := bstep (se 1 (by rfl) ⟨9311597, by rfl⟩ : syracuseStep 12415463 = 18623195) B18623195
theorem B8276975 : Blo 1937435 8276975 := bstep (se 1 (by rfl) ⟨6207731, by rfl⟩ : syracuseStep 8276975 = 12415463) B12415463
theorem B5517983 : Blo 1937435 5517983 := bstep (se 1 (by rfl) ⟨4138487, by rfl⟩ : syracuseStep 5517983 = 8276975) B8276975
theorem B14714621 : Blo 1937435 14714621 := bstep (se 3 (by rfl) ⟨2758991, by rfl⟩ : syracuseStep 14714621 = 5517983) B5517983
theorem B9809747 : Blo 1937435 9809747 := bstep (se 1 (by rfl) ⟨7357310, by rfl⟩ : syracuseStep 9809747 = 14714621) B14714621
theorem B6539831 : Blo 1937435 6539831 := bstep (se 1 (by rfl) ⟨4904873, by rfl⟩ : syracuseStep 6539831 = 9809747) B9809747
theorem B4359887 : Blo 1937435 4359887 := bstep (se 1 (by rfl) ⟨3269915, by rfl⟩ : syracuseStep 4359887 = 6539831) B6539831
theorem B2906591 : Blo 1937435 2906591 := bstep (se 1 (by rfl) ⟨2179943, by rfl⟩ : syracuseStep 2906591 = 4359887) B4359887
theorem B1937727 : Blo 1937435 1937727 := bstep (se 1 (by rfl) ⟨1453295, by rfl⟩ : syracuseStep 1937727 = 2906591) B2906591
theorem B2906597 : Blo 1937435 2906597 := bbase (se 4 (by rfl) ⟨272493, by rfl⟩ : syracuseStep 2906597 = 544987) (by norm_num)
theorem B1937731 : Blo 1937435 1937731 := bstep (se 1 (by rfl) ⟨1453298, by rfl⟩ : syracuseStep 1937731 = 2906597) B2906597
theorem B5237797 : Blo 1937435 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B6983729 : Blo 1937435 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B4655819 : Blo 1937435 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B12415517 : Blo 1937435 12415517 := bstep (se 3 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 12415517 = 4655819) B4655819
theorem B8277011 : Blo 1937435 8277011 := bstep (se 1 (by rfl) ⟨6207758, by rfl⟩ : syracuseStep 8277011 = 12415517) B12415517
theorem B5518007 : Blo 1937435 5518007 := bstep (se 1 (by rfl) ⟨4138505, by rfl⟩ : syracuseStep 5518007 = 8277011) B8277011
theorem B3678671 : Blo 1937435 3678671 := bstep (se 1 (by rfl) ⟨2759003, by rfl⟩ : syracuseStep 3678671 = 5518007) B5518007
theorem B2452447 : Blo 1937435 2452447 := bstep (se 1 (by rfl) ⟨1839335, by rfl⟩ : syracuseStep 2452447 = 3678671) B3678671
theorem B3269929 : Blo 1937435 3269929 := bstep (se 2 (by rfl) ⟨1226223, by rfl⟩ : syracuseStep 3269929 = 2452447) B2452447
theorem B4359905 : Blo 1937435 4359905 := bstep (se 2 (by rfl) ⟨1634964, by rfl⟩ : syracuseStep 4359905 = 3269929) B3269929
theorem B2906603 : Blo 1937435 2906603 := bstep (se 1 (by rfl) ⟨2179952, by rfl⟩ : syracuseStep 2906603 = 4359905) B4359905
theorem B1937735 : Blo 1937435 1937735 := bstep (se 1 (by rfl) ⟨1453301, by rfl⟩ : syracuseStep 1937735 = 2906603) B2906603
theorem B2179957 : Blo 1937435 2179957 := bbase (se 5 (by rfl) ⟨102185, by rfl⟩ : syracuseStep 2179957 = 204371) (by norm_num)
theorem B2906609 : Blo 1937435 2906609 := bstep (se 2 (by rfl) ⟨1089978, by rfl⟩ : syracuseStep 2906609 = 2179957) B2179957
theorem B1937739 : Blo 1937435 1937739 := bstep (se 1 (by rfl) ⟨1453304, by rfl⟩ : syracuseStep 1937739 = 2906609) B2906609
theorem B2452457 : Blo 1937435 2452457 := bbase (se 2 (by rfl) ⟨919671, by rfl⟩ : syracuseStep 2452457 = 1839343) (by norm_num)
theorem B6539885 : Blo 1937435 6539885 := bstep (se 3 (by rfl) ⟨1226228, by rfl⟩ : syracuseStep 6539885 = 2452457) B2452457
theorem B4359923 : Blo 1937435 4359923 := bstep (se 1 (by rfl) ⟨3269942, by rfl⟩ : syracuseStep 4359923 = 6539885) B6539885
theorem B2906615 : Blo 1937435 2906615 := bstep (se 1 (by rfl) ⟨2179961, by rfl⟩ : syracuseStep 2906615 = 4359923) B4359923
theorem B1937743 : Blo 1937435 1937743 := bstep (se 1 (by rfl) ⟨1453307, by rfl⟩ : syracuseStep 1937743 = 2906615) B2906615
theorem B2906621 : Blo 1937435 2906621 := bbase (se 3 (by rfl) ⟨544991, by rfl⟩ : syracuseStep 2906621 = 1089983) (by norm_num)
theorem B1937747 : Blo 1937435 1937747 := bstep (se 1 (by rfl) ⟨1453310, by rfl⟩ : syracuseStep 1937747 = 2906621) B2906621
theorem B4359941 : Blo 1937435 4359941 := bbase (se 4 (by rfl) ⟨408744, by rfl⟩ : syracuseStep 4359941 = 817489) (by norm_num)
theorem B2906627 : Blo 1937435 2906627 := bstep (se 1 (by rfl) ⟨2179970, by rfl⟩ : syracuseStep 2906627 = 4359941) B4359941
theorem B1937751 : Blo 1937435 1937751 := bstep (se 1 (by rfl) ⟨1453313, by rfl⟩ : syracuseStep 1937751 = 2906627) B2906627
theorem B3678709 : Blo 1937435 3678709 := bbase (se 5 (by rfl) ⟨172439, by rfl⟩ : syracuseStep 3678709 = 344879) (by norm_num)
theorem B4904945 : Blo 1937435 4904945 := bstep (se 2 (by rfl) ⟨1839354, by rfl⟩ : syracuseStep 4904945 = 3678709) B3678709
theorem B3269963 : Blo 1937435 3269963 := bstep (se 1 (by rfl) ⟨2452472, by rfl⟩ : syracuseStep 3269963 = 4904945) B4904945
theorem B2179975 : Blo 1937435 2179975 := bstep (se 1 (by rfl) ⟨1634981, by rfl⟩ : syracuseStep 2179975 = 3269963) B3269963
theorem B2906633 : Blo 1937435 2906633 := bstep (se 2 (by rfl) ⟨1089987, by rfl⟩ : syracuseStep 2906633 = 2179975) B2179975
theorem B1937755 : Blo 1937435 1937755 := bstep (se 1 (by rfl) ⟨1453316, by rfl⟩ : syracuseStep 1937755 = 2906633) B2906633
theorem B9809909 : Blo 1937435 9809909 := bbase (se 5 (by rfl) ⟨459839, by rfl⟩ : syracuseStep 9809909 = 919679) (by norm_num)
theorem B6539939 : Blo 1937435 6539939 := bstep (se 1 (by rfl) ⟨4904954, by rfl⟩ : syracuseStep 6539939 = 9809909) B9809909
theorem B4359959 : Blo 1937435 4359959 := bstep (se 1 (by rfl) ⟨3269969, by rfl⟩ : syracuseStep 4359959 = 6539939) B6539939
theorem B2906639 : Blo 1937435 2906639 := bstep (se 1 (by rfl) ⟨2179979, by rfl⟩ : syracuseStep 2906639 = 4359959) B4359959
theorem B1937759 : Blo 1937435 1937759 := bstep (se 1 (by rfl) ⟨1453319, by rfl⟩ : syracuseStep 1937759 = 2906639) B2906639
theorem B2906645 : Blo 1937435 2906645 := bbase (se 6 (by rfl) ⟨68124, by rfl⟩ : syracuseStep 2906645 = 136249) (by norm_num)
theorem B1937763 : Blo 1937435 1937763 := bstep (se 1 (by rfl) ⟨1453322, by rfl⟩ : syracuseStep 1937763 = 2906645) B2906645
theorem B16554293 : Blo 1937435 16554293 := bbase (se 5 (by rfl) ⟨775982, by rfl⟩ : syracuseStep 16554293 = 1551965) (by norm_num)
theorem B11036195 : Blo 1937435 11036195 := bstep (se 1 (by rfl) ⟨8277146, by rfl⟩ : syracuseStep 11036195 = 16554293) B16554293
theorem B7357463 : Blo 1937435 7357463 := bstep (se 1 (by rfl) ⟨5518097, by rfl⟩ : syracuseStep 7357463 = 11036195) B11036195
theorem B4904975 : Blo 1937435 4904975 := bstep (se 1 (by rfl) ⟨3678731, by rfl⟩ : syracuseStep 4904975 = 7357463) B7357463
theorem B3269983 : Blo 1937435 3269983 := bstep (se 1 (by rfl) ⟨2452487, by rfl⟩ : syracuseStep 3269983 = 4904975) B4904975
theorem B4359977 : Blo 1937435 4359977 := bstep (se 2 (by rfl) ⟨1634991, by rfl⟩ : syracuseStep 4359977 = 3269983) B3269983
theorem B2906651 : Blo 1937435 2906651 := bstep (se 1 (by rfl) ⟨2179988, by rfl⟩ : syracuseStep 2906651 = 4359977) B4359977
theorem B1937767 : Blo 1937435 1937767 := bstep (se 1 (by rfl) ⟨1453325, by rfl⟩ : syracuseStep 1937767 = 2906651) B2906651
theorem B2179993 : Blo 1937435 2179993 := bbase (se 2 (by rfl) ⟨817497, by rfl⟩ : syracuseStep 2179993 = 1634995) (by norm_num)
theorem B2906657 : Blo 1937435 2906657 := bstep (se 2 (by rfl) ⟨1089996, by rfl⟩ : syracuseStep 2906657 = 2179993) B2179993
theorem B1937771 : Blo 1937435 1937771 := bstep (se 1 (by rfl) ⟨1453328, by rfl⟩ : syracuseStep 1937771 = 2906657) B2906657
theorem B7357493 : Blo 1937435 7357493 := bbase (se 5 (by rfl) ⟨344882, by rfl⟩ : syracuseStep 7357493 = 689765) (by norm_num)
theorem B4904995 : Blo 1937435 4904995 := bstep (se 1 (by rfl) ⟨3678746, by rfl⟩ : syracuseStep 4904995 = 7357493) B7357493
theorem B6539993 : Blo 1937435 6539993 := bstep (se 2 (by rfl) ⟨2452497, by rfl⟩ : syracuseStep 6539993 = 4904995) B4904995
theorem B4359995 : Blo 1937435 4359995 := bstep (se 1 (by rfl) ⟨3269996, by rfl⟩ : syracuseStep 4359995 = 6539993) B6539993
theorem B2906663 : Blo 1937435 2906663 := bstep (se 1 (by rfl) ⟨2179997, by rfl⟩ : syracuseStep 2906663 = 4359995) B4359995
theorem B1937775 : Blo 1937435 1937775 := bstep (se 1 (by rfl) ⟨1453331, by rfl⟩ : syracuseStep 1937775 = 2906663) B2906663
theorem B2906669 : Blo 1937435 2906669 := bbase (se 3 (by rfl) ⟨545000, by rfl⟩ : syracuseStep 2906669 = 1090001) (by norm_num)
theorem B1937779 : Blo 1937435 1937779 := bstep (se 1 (by rfl) ⟨1453334, by rfl⟩ : syracuseStep 1937779 = 2906669) B2906669
theorem B4360013 : Blo 1937435 4360013 := bbase (se 3 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 4360013 = 1635005) (by norm_num)
theorem B2906675 : Blo 1937435 2906675 := bstep (se 1 (by rfl) ⟨2180006, by rfl⟩ : syracuseStep 2906675 = 4360013) B4360013
theorem B1937783 : Blo 1937435 1937783 := bstep (se 1 (by rfl) ⟨1453337, by rfl⟩ : syracuseStep 1937783 = 2906675) B2906675
theorem B2452513 : Blo 1937435 2452513 := bbase (se 2 (by rfl) ⟨919692, by rfl⟩ : syracuseStep 2452513 = 1839385) (by norm_num)
theorem B3270017 : Blo 1937435 3270017 := bstep (se 2 (by rfl) ⟨1226256, by rfl⟩ : syracuseStep 3270017 = 2452513) B2452513
theorem B2180011 : Blo 1937435 2180011 := bstep (se 1 (by rfl) ⟨1635008, by rfl⟩ : syracuseStep 2180011 = 3270017) B3270017
theorem B2906681 : Blo 1937435 2906681 := bstep (se 2 (by rfl) ⟨1090005, by rfl⟩ : syracuseStep 2906681 = 2180011) B2180011
theorem B1937787 : Blo 1937435 1937787 := bstep (se 1 (by rfl) ⟨1453340, by rfl⟩ : syracuseStep 1937787 = 2906681) B2906681
theorem B22072661 : Blo 1937435 22072661 := bbase (se 11 (by rfl) ⟨16166, by rfl⟩ : syracuseStep 22072661 = 32333) (by norm_num)
theorem B14715107 : Blo 1937435 14715107 := bstep (se 1 (by rfl) ⟨11036330, by rfl⟩ : syracuseStep 14715107 = 22072661) B22072661
theorem B9810071 : Blo 1937435 9810071 := bstep (se 1 (by rfl) ⟨7357553, by rfl⟩ : syracuseStep 9810071 = 14715107) B14715107
theorem B6540047 : Blo 1937435 6540047 := bstep (se 1 (by rfl) ⟨4905035, by rfl⟩ : syracuseStep 6540047 = 9810071) B9810071
theorem B4360031 : Blo 1937435 4360031 := bstep (se 1 (by rfl) ⟨3270023, by rfl⟩ : syracuseStep 4360031 = 6540047) B6540047
theorem B2906687 : Blo 1937435 2906687 := bstep (se 1 (by rfl) ⟨2180015, by rfl⟩ : syracuseStep 2906687 = 4360031) B4360031
theorem B1937791 : Blo 1937435 1937791 := bstep (se 1 (by rfl) ⟨1453343, by rfl⟩ : syracuseStep 1937791 = 2906687) B2906687
theorem B2906693 : Blo 1937435 2906693 := bbase (se 4 (by rfl) ⟨272502, by rfl⟩ : syracuseStep 2906693 = 545005) (by norm_num)
theorem B1937795 : Blo 1937435 1937795 := bstep (se 1 (by rfl) ⟨1453346, by rfl⟩ : syracuseStep 1937795 = 2906693) B2906693
theorem B3270037 : Blo 1937435 3270037 := bbase (se 6 (by rfl) ⟨76641, by rfl⟩ : syracuseStep 3270037 = 153283) (by norm_num)
theorem B4360049 : Blo 1937435 4360049 := bstep (se 2 (by rfl) ⟨1635018, by rfl⟩ : syracuseStep 4360049 = 3270037) B3270037
theorem B2906699 : Blo 1937435 2906699 := bstep (se 1 (by rfl) ⟨2180024, by rfl⟩ : syracuseStep 2906699 = 4360049) B4360049
theorem B1937799 : Blo 1937435 1937799 := bstep (se 1 (by rfl) ⟨1453349, by rfl⟩ : syracuseStep 1937799 = 2906699) B2906699
theorem B2180029 : Blo 1937435 2180029 := bbase (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) (by norm_num)
theorem B2906705 : Blo 1937435 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B1937803 : Blo 1937435 1937803 := bstep (se 1 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 1937803 = 2906705) B2906705
theorem B6540101 : Blo 1937435 6540101 := bbase (se 4 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 6540101 = 1226269) (by norm_num)
theorem B4360067 : Blo 1937435 4360067 := bstep (se 1 (by rfl) ⟨3270050, by rfl⟩ : syracuseStep 4360067 = 6540101) B6540101
theorem B2906711 : Blo 1937435 2906711 := bstep (se 1 (by rfl) ⟨2180033, by rfl⟩ : syracuseStep 2906711 = 4360067) B4360067
theorem B1937807 : Blo 1937435 1937807 := bstep (se 1 (by rfl) ⟨1453355, by rfl⟩ : syracuseStep 1937807 = 2906711) B2906711
theorem B2906717 : Blo 1937435 2906717 := bbase (se 3 (by rfl) ⟨545009, by rfl⟩ : syracuseStep 2906717 = 1090019) (by norm_num)
theorem B1937811 : Blo 1937435 1937811 := bstep (se 1 (by rfl) ⟨1453358, by rfl⟩ : syracuseStep 1937811 = 2906717) B2906717
theorem B4360085 : Blo 1937435 4360085 := bbase (se 6 (by rfl) ⟨102189, by rfl⟩ : syracuseStep 4360085 = 204379) (by norm_num)
theorem B2906723 : Blo 1937435 2906723 := bstep (se 1 (by rfl) ⟨2180042, by rfl⟩ : syracuseStep 2906723 = 4360085) B4360085
theorem B1937815 : Blo 1937435 1937815 := bstep (se 1 (by rfl) ⟨1453361, by rfl⟩ : syracuseStep 1937815 = 2906723) B2906723
theorem B4138685 : Blo 1937435 4138685 := bbase (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) (by norm_num)
theorem B2759123 : Blo 1937435 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B7357661 : Blo 1937435 7357661 := bstep (se 3 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 7357661 = 2759123) B2759123
theorem B4905107 : Blo 1937435 4905107 := bstep (se 1 (by rfl) ⟨3678830, by rfl⟩ : syracuseStep 4905107 = 7357661) B7357661
theorem B3270071 : Blo 1937435 3270071 := bstep (se 1 (by rfl) ⟨2452553, by rfl⟩ : syracuseStep 3270071 = 4905107) B4905107
theorem B2180047 : Blo 1937435 2180047 := bstep (se 1 (by rfl) ⟨1635035, by rfl⟩ : syracuseStep 2180047 = 3270071) B3270071
theorem B2906729 : Blo 1937435 2906729 := bstep (se 2 (by rfl) ⟨1090023, by rfl⟩ : syracuseStep 2906729 = 2180047) B2180047
theorem B1937819 : Blo 1937435 1937819 := bstep (se 1 (by rfl) ⟨1453364, by rfl⟩ : syracuseStep 1937819 = 2906729) B2906729
theorem B15714101 : Blo 1937435 15714101 := bbase (se 5 (by rfl) ⟨736598, by rfl⟩ : syracuseStep 15714101 = 1473197) (by norm_num)
theorem B10476067 : Blo 1937435 10476067 := bstep (se 1 (by rfl) ⟨7857050, by rfl⟩ : syracuseStep 10476067 = 15714101) B15714101
theorem B13968089 : Blo 1937435 13968089 := bstep (se 2 (by rfl) ⟨5238033, by rfl⟩ : syracuseStep 13968089 = 10476067) B10476067
theorem B9312059 : Blo 1937435 9312059 := bstep (se 1 (by rfl) ⟨6984044, by rfl⟩ : syracuseStep 9312059 = 13968089) B13968089
theorem B6208039 : Blo 1937435 6208039 := bstep (se 1 (by rfl) ⟨4656029, by rfl⟩ : syracuseStep 6208039 = 9312059) B9312059
theorem B8277385 : Blo 1937435 8277385 := bstep (se 2 (by rfl) ⟨3104019, by rfl⟩ : syracuseStep 8277385 = 6208039) B6208039
theorem B11036513 : Blo 1937435 11036513 := bstep (se 2 (by rfl) ⟨4138692, by rfl⟩ : syracuseStep 11036513 = 8277385) B8277385
theorem B7357675 : Blo 1937435 7357675 := bstep (se 1 (by rfl) ⟨5518256, by rfl⟩ : syracuseStep 7357675 = 11036513) B11036513
theorem B9810233 : Blo 1937435 9810233 := bstep (se 2 (by rfl) ⟨3678837, by rfl⟩ : syracuseStep 9810233 = 7357675) B7357675
theorem B6540155 : Blo 1937435 6540155 := bstep (se 1 (by rfl) ⟨4905116, by rfl⟩ : syracuseStep 6540155 = 9810233) B9810233
theorem B4360103 : Blo 1937435 4360103 := bstep (se 1 (by rfl) ⟨3270077, by rfl⟩ : syracuseStep 4360103 = 6540155) B6540155
theorem B2906735 : Blo 1937435 2906735 := bstep (se 1 (by rfl) ⟨2180051, by rfl⟩ : syracuseStep 2906735 = 4360103) B4360103
theorem B1937823 : Blo 1937435 1937823 := bstep (se 1 (by rfl) ⟨1453367, by rfl⟩ : syracuseStep 1937823 = 2906735) B2906735
theorem B2906741 : Blo 1937435 2906741 := bbase (se 5 (by rfl) ⟨136253, by rfl⟩ : syracuseStep 2906741 = 272507) (by norm_num)
theorem B1937827 : Blo 1937435 1937827 := bstep (se 1 (by rfl) ⟨1453370, by rfl⟩ : syracuseStep 1937827 = 2906741) B2906741
theorem B3678853 : Blo 1937435 3678853 := bbase (se 4 (by rfl) ⟨344892, by rfl⟩ : syracuseStep 3678853 = 689785) (by norm_num)
theorem B4905137 : Blo 1937435 4905137 := bstep (se 2 (by rfl) ⟨1839426, by rfl⟩ : syracuseStep 4905137 = 3678853) B3678853
theorem B3270091 : Blo 1937435 3270091 := bstep (se 1 (by rfl) ⟨2452568, by rfl⟩ : syracuseStep 3270091 = 4905137) B4905137
theorem B4360121 : Blo 1937435 4360121 := bstep (se 2 (by rfl) ⟨1635045, by rfl⟩ : syracuseStep 4360121 = 3270091) B3270091
theorem B2906747 : Blo 1937435 2906747 := bstep (se 1 (by rfl) ⟨2180060, by rfl⟩ : syracuseStep 2906747 = 4360121) B4360121
theorem B1937831 : Blo 1937435 1937831 := bstep (se 1 (by rfl) ⟨1453373, by rfl⟩ : syracuseStep 1937831 = 2906747) B2906747
theorem B2180065 : Blo 1937435 2180065 := bbase (se 2 (by rfl) ⟨817524, by rfl⟩ : syracuseStep 2180065 = 1635049) (by norm_num)
theorem B2906753 : Blo 1937435 2906753 := bstep (se 2 (by rfl) ⟨1090032, by rfl⟩ : syracuseStep 2906753 = 2180065) B2180065
theorem B1937835 : Blo 1937435 1937835 := bstep (se 1 (by rfl) ⟨1453376, by rfl⟩ : syracuseStep 1937835 = 2906753) B2906753
theorem B4905157 : Blo 1937435 4905157 := bbase (se 4 (by rfl) ⟨459858, by rfl⟩ : syracuseStep 4905157 = 919717) (by norm_num)
theorem B6540209 : Blo 1937435 6540209 := bstep (se 2 (by rfl) ⟨2452578, by rfl⟩ : syracuseStep 6540209 = 4905157) B4905157
theorem B4360139 : Blo 1937435 4360139 := bstep (se 1 (by rfl) ⟨3270104, by rfl⟩ : syracuseStep 4360139 = 6540209) B6540209
theorem B2906759 : Blo 1937435 2906759 := bstep (se 1 (by rfl) ⟨2180069, by rfl⟩ : syracuseStep 2906759 = 4360139) B4360139
theorem B1937839 : Blo 1937435 1937839 := bstep (se 1 (by rfl) ⟨1453379, by rfl⟩ : syracuseStep 1937839 = 2906759) B2906759
theorem B2906765 : Blo 1937435 2906765 := bbase (se 3 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 2906765 = 1090037) (by norm_num)
theorem B1937843 : Blo 1937435 1937843 := bstep (se 1 (by rfl) ⟨1453382, by rfl⟩ : syracuseStep 1937843 = 2906765) B2906765
theorem B4360157 : Blo 1937435 4360157 := bbase (se 3 (by rfl) ⟨817529, by rfl⟩ : syracuseStep 4360157 = 1635059) (by norm_num)
theorem B2906771 : Blo 1937435 2906771 := bstep (se 1 (by rfl) ⟨2180078, by rfl⟩ : syracuseStep 2906771 = 4360157) B4360157
theorem B1937847 : Blo 1937435 1937847 := bstep (se 1 (by rfl) ⟨1453385, by rfl⟩ : syracuseStep 1937847 = 2906771) B2906771
theorem B3270125 : Blo 1937435 3270125 := bbase (se 3 (by rfl) ⟨613148, by rfl⟩ : syracuseStep 3270125 = 1226297) (by norm_num)
theorem B2180083 : Blo 1937435 2180083 := bstep (se 1 (by rfl) ⟨1635062, by rfl⟩ : syracuseStep 2180083 = 3270125) B3270125
theorem B2906777 : Blo 1937435 2906777 := bstep (se 2 (by rfl) ⟨1090041, by rfl⟩ : syracuseStep 2906777 = 2180083) B2180083
theorem B1937851 : Blo 1937435 1937851 := bstep (se 1 (by rfl) ⟨1453388, by rfl⟩ : syracuseStep 1937851 = 2906777) B2906777
theorem B2328053 : Blo 1937435 2328053 := bbase (se 5 (by rfl) ⟨109127, by rfl⟩ : syracuseStep 2328053 = 218255) (by norm_num)
theorem B24832565 : Blo 1937435 24832565 := bstep (se 5 (by rfl) ⟨1164026, by rfl⟩ : syracuseStep 24832565 = 2328053) B2328053
theorem B16555043 : Blo 1937435 16555043 := bstep (se 1 (by rfl) ⟨12416282, by rfl⟩ : syracuseStep 16555043 = 24832565) B24832565
theorem B11036695 : Blo 1937435 11036695 := bstep (se 1 (by rfl) ⟨8277521, by rfl⟩ : syracuseStep 11036695 = 16555043) B16555043
theorem B14715593 : Blo 1937435 14715593 := bstep (se 2 (by rfl) ⟨5518347, by rfl⟩ : syracuseStep 14715593 = 11036695) B11036695
theorem B9810395 : Blo 1937435 9810395 := bstep (se 1 (by rfl) ⟨7357796, by rfl⟩ : syracuseStep 9810395 = 14715593) B14715593
theorem B6540263 : Blo 1937435 6540263 := bstep (se 1 (by rfl) ⟨4905197, by rfl⟩ : syracuseStep 6540263 = 9810395) B9810395
theorem B4360175 : Blo 1937435 4360175 := bstep (se 1 (by rfl) ⟨3270131, by rfl⟩ : syracuseStep 4360175 = 6540263) B6540263
theorem B2906783 : Blo 1937435 2906783 := bstep (se 1 (by rfl) ⟨2180087, by rfl⟩ : syracuseStep 2906783 = 4360175) B4360175
theorem B1937855 : Blo 1937435 1937855 := bstep (se 1 (by rfl) ⟨1453391, by rfl⟩ : syracuseStep 1937855 = 2906783) B2906783
theorem B2906789 : Blo 1937435 2906789 := bbase (se 4 (by rfl) ⟨272511, by rfl⟩ : syracuseStep 2906789 = 545023) (by norm_num)
theorem B1937859 : Blo 1937435 1937859 := bstep (se 1 (by rfl) ⟨1453394, by rfl⟩ : syracuseStep 1937859 = 2906789) B2906789
theorem B2452609 : Blo 1937435 2452609 := bbase (se 2 (by rfl) ⟨919728, by rfl⟩ : syracuseStep 2452609 = 1839457) (by norm_num)
theorem B3270145 : Blo 1937435 3270145 := bstep (se 2 (by rfl) ⟨1226304, by rfl⟩ : syracuseStep 3270145 = 2452609) B2452609
theorem B4360193 : Blo 1937435 4360193 := bstep (se 2 (by rfl) ⟨1635072, by rfl⟩ : syracuseStep 4360193 = 3270145) B3270145
theorem B2906795 : Blo 1937435 2906795 := bstep (se 1 (by rfl) ⟨2180096, by rfl⟩ : syracuseStep 2906795 = 4360193) B4360193
theorem B1937863 : Blo 1937435 1937863 := bstep (se 1 (by rfl) ⟨1453397, by rfl⟩ : syracuseStep 1937863 = 2906795) B2906795
theorem B2180101 : Blo 1937435 2180101 := bbase (se 4 (by rfl) ⟨204384, by rfl⟩ : syracuseStep 2180101 = 408769) (by norm_num)
theorem B2906801 : Blo 1937435 2906801 := bstep (se 2 (by rfl) ⟨1090050, by rfl⟩ : syracuseStep 2906801 = 2180101) B2180101
theorem B1937867 : Blo 1937435 1937867 := bstep (se 1 (by rfl) ⟨1453400, by rfl⟩ : syracuseStep 1937867 = 2906801) B2906801
theorem B2759197 : Blo 1937435 2759197 := bbase (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) (by norm_num)
theorem B3678929 : Blo 1937435 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B2452619 : Blo 1937435 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B6540317 : Blo 1937435 6540317 := bstep (se 3 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 6540317 = 2452619) B2452619
theorem B4360211 : Blo 1937435 4360211 := bstep (se 1 (by rfl) ⟨3270158, by rfl⟩ : syracuseStep 4360211 = 6540317) B6540317
theorem B2906807 : Blo 1937435 2906807 := bstep (se 1 (by rfl) ⟨2180105, by rfl⟩ : syracuseStep 2906807 = 4360211) B4360211
theorem B1937871 : Blo 1937435 1937871 := bstep (se 1 (by rfl) ⟨1453403, by rfl⟩ : syracuseStep 1937871 = 2906807) B2906807
theorem B2906813 : Blo 1937435 2906813 := bbase (se 3 (by rfl) ⟨545027, by rfl⟩ : syracuseStep 2906813 = 1090055) (by norm_num)
theorem B1937875 : Blo 1937435 1937875 := bstep (se 1 (by rfl) ⟨1453406, by rfl⟩ : syracuseStep 1937875 = 2906813) B2906813
theorem B4360229 : Blo 1937435 4360229 := bbase (se 4 (by rfl) ⟨408771, by rfl⟩ : syracuseStep 4360229 = 817543) (by norm_num)
theorem B2906819 : Blo 1937435 2906819 := bstep (se 1 (by rfl) ⟨2180114, by rfl⟩ : syracuseStep 2906819 = 4360229) B4360229
theorem B1937879 : Blo 1937435 1937879 := bstep (se 1 (by rfl) ⟨1453409, by rfl⟩ : syracuseStep 1937879 = 2906819) B2906819
theorem B4905269 : Blo 1937435 4905269 := bbase (se 5 (by rfl) ⟨229934, by rfl⟩ : syracuseStep 4905269 = 459869) (by norm_num)
theorem B3270179 : Blo 1937435 3270179 := bstep (se 1 (by rfl) ⟨2452634, by rfl⟩ : syracuseStep 3270179 = 4905269) B4905269
theorem B2180119 : Blo 1937435 2180119 := bstep (se 1 (by rfl) ⟨1635089, by rfl⟩ : syracuseStep 2180119 = 3270179) B3270179
theorem B2906825 : Blo 1937435 2906825 := bstep (se 2 (by rfl) ⟨1090059, by rfl⟩ : syracuseStep 2906825 = 2180119) B2180119
theorem B1937883 : Blo 1937435 1937883 := bstep (se 1 (by rfl) ⟨1453412, by rfl⟩ : syracuseStep 1937883 = 2906825) B2906825
theorem B2097649 : Blo 1937435 2097649 := bbase (se 2 (by rfl) ⟨786618, by rfl⟩ : syracuseStep 2097649 = 1573237) (by norm_num)
theorem B2796865 : Blo 1937435 2796865 := bstep (se 2 (by rfl) ⟨1048824, by rfl⟩ : syracuseStep 2796865 = 2097649) B2097649
theorem B59666453 : Blo 1937435 59666453 := bstep (se 6 (by rfl) ⟨1398432, by rfl⟩ : syracuseStep 59666453 = 2796865) B2796865
theorem B39777635 : Blo 1937435 39777635 := bstep (se 1 (by rfl) ⟨29833226, by rfl⟩ : syracuseStep 39777635 = 59666453) B59666453
theorem B26518423 : Blo 1937435 26518423 := bstep (se 1 (by rfl) ⟨19888817, by rfl⟩ : syracuseStep 26518423 = 39777635) B39777635
theorem B35357897 : Blo 1937435 35357897 := bstep (se 2 (by rfl) ⟨13259211, by rfl⟩ : syracuseStep 35357897 = 26518423) B26518423
theorem B23571931 : Blo 1937435 23571931 := bstep (se 1 (by rfl) ⟨17678948, by rfl⟩ : syracuseStep 23571931 = 35357897) B35357897
theorem B31429241 : Blo 1937435 31429241 := bstep (se 2 (by rfl) ⟨11785965, by rfl⟩ : syracuseStep 31429241 = 23571931) B23571931
theorem B20952827 : Blo 1937435 20952827 := bstep (se 1 (by rfl) ⟨15714620, by rfl⟩ : syracuseStep 20952827 = 31429241) B31429241
theorem B13968551 : Blo 1937435 13968551 := bstep (se 1 (by rfl) ⟨10476413, by rfl⟩ : syracuseStep 13968551 = 20952827) B20952827
theorem B9312367 : Blo 1937435 9312367 := bstep (se 1 (by rfl) ⟨6984275, by rfl⟩ : syracuseStep 9312367 = 13968551) B13968551
theorem B12416489 : Blo 1937435 12416489 := bstep (se 2 (by rfl) ⟨4656183, by rfl⟩ : syracuseStep 12416489 = 9312367) B9312367
theorem B8277659 : Blo 1937435 8277659 := bstep (se 1 (by rfl) ⟨6208244, by rfl⟩ : syracuseStep 8277659 = 12416489) B12416489
theorem B5518439 : Blo 1937435 5518439 := bstep (se 1 (by rfl) ⟨4138829, by rfl⟩ : syracuseStep 5518439 = 8277659) B8277659
theorem B3678959 : Blo 1937435 3678959 := bstep (se 1 (by rfl) ⟨2759219, by rfl⟩ : syracuseStep 3678959 = 5518439) B5518439
theorem B9810557 : Blo 1937435 9810557 := bstep (se 3 (by rfl) ⟨1839479, by rfl⟩ : syracuseStep 9810557 = 3678959) B3678959
theorem B6540371 : Blo 1937435 6540371 := bstep (se 1 (by rfl) ⟨4905278, by rfl⟩ : syracuseStep 6540371 = 9810557) B9810557
theorem B4360247 : Blo 1937435 4360247 := bstep (se 1 (by rfl) ⟨3270185, by rfl⟩ : syracuseStep 4360247 = 6540371) B6540371
theorem B2906831 : Blo 1937435 2906831 := bstep (se 1 (by rfl) ⟨2180123, by rfl⟩ : syracuseStep 2906831 = 4360247) B4360247
theorem B1937887 : Blo 1937435 1937887 := bstep (se 1 (by rfl) ⟨1453415, by rfl⟩ : syracuseStep 1937887 = 2906831) B2906831
theorem B2906837 : Blo 1937435 2906837 := bbase (se 7 (by rfl) ⟨34064, by rfl⟩ : syracuseStep 2906837 = 68129) (by norm_num)
theorem B1937891 : Blo 1937435 1937891 := bstep (se 1 (by rfl) ⟨1453418, by rfl⟩ : syracuseStep 1937891 = 2906837) B2906837
theorem B20952917 : Blo 1937435 20952917 := bbase (se 9 (by rfl) ⟨61385, by rfl⟩ : syracuseStep 20952917 = 122771) (by norm_num)
theorem B13968611 : Blo 1937435 13968611 := bstep (se 1 (by rfl) ⟨10476458, by rfl⟩ : syracuseStep 13968611 = 20952917) B20952917
theorem B9312407 : Blo 1937435 9312407 := bstep (se 1 (by rfl) ⟨6984305, by rfl⟩ : syracuseStep 9312407 = 13968611) B13968611
theorem B6208271 : Blo 1937435 6208271 := bstep (se 1 (by rfl) ⟨4656203, by rfl⟩ : syracuseStep 6208271 = 9312407) B9312407
theorem B4138847 : Blo 1937435 4138847 := bstep (se 1 (by rfl) ⟨3104135, by rfl⟩ : syracuseStep 4138847 = 6208271) B6208271
theorem B2759231 : Blo 1937435 2759231 := bstep (se 1 (by rfl) ⟨2069423, by rfl⟩ : syracuseStep 2759231 = 4138847) B4138847
theorem B7357949 : Blo 1937435 7357949 := bstep (se 3 (by rfl) ⟨1379615, by rfl⟩ : syracuseStep 7357949 = 2759231) B2759231
theorem B4905299 : Blo 1937435 4905299 := bstep (se 1 (by rfl) ⟨3678974, by rfl⟩ : syracuseStep 4905299 = 7357949) B7357949
theorem B3270199 : Blo 1937435 3270199 := bstep (se 1 (by rfl) ⟨2452649, by rfl⟩ : syracuseStep 3270199 = 4905299) B4905299
theorem B4360265 : Blo 1937435 4360265 := bstep (se 2 (by rfl) ⟨1635099, by rfl⟩ : syracuseStep 4360265 = 3270199) B3270199
theorem B2906843 : Blo 1937435 2906843 := bstep (se 1 (by rfl) ⟨2180132, by rfl⟩ : syracuseStep 2906843 = 4360265) B4360265
theorem B1937895 : Blo 1937435 1937895 := bstep (se 1 (by rfl) ⟨1453421, by rfl⟩ : syracuseStep 1937895 = 2906843) B2906843
theorem B2180137 : Blo 1937435 2180137 := bbase (se 2 (by rfl) ⟨817551, by rfl⟩ : syracuseStep 2180137 = 1635103) (by norm_num)
theorem B2906849 : Blo 1937435 2906849 := bstep (se 2 (by rfl) ⟨1090068, by rfl⟩ : syracuseStep 2906849 = 2180137) B2180137
theorem B1937899 : Blo 1937435 1937899 := bstep (se 1 (by rfl) ⟨1453424, by rfl⟩ : syracuseStep 1937899 = 2906849) B2906849
theorem B2986717 : Blo 1937435 2986717 := bbase (se 3 (by rfl) ⟨560009, by rfl⟩ : syracuseStep 2986717 = 1120019) (by norm_num)
theorem B3982289 : Blo 1937435 3982289 := bstep (se 2 (by rfl) ⟨1493358, by rfl⟩ : syracuseStep 3982289 = 2986717) B2986717
theorem B10619437 : Blo 1937435 10619437 := bstep (se 3 (by rfl) ⟨1991144, by rfl⟩ : syracuseStep 10619437 = 3982289) B3982289
theorem B14159249 : Blo 1937435 14159249 := bstep (se 2 (by rfl) ⟨5309718, by rfl⟩ : syracuseStep 14159249 = 10619437) B10619437
theorem B9439499 : Blo 1937435 9439499 := bstep (se 1 (by rfl) ⟨7079624, by rfl⟩ : syracuseStep 9439499 = 14159249) B14159249
theorem B6292999 : Blo 1937435 6292999 := bstep (se 1 (by rfl) ⟨4719749, by rfl⟩ : syracuseStep 6292999 = 9439499) B9439499
theorem B8390665 : Blo 1937435 8390665 := bstep (se 2 (by rfl) ⟨3146499, by rfl⟩ : syracuseStep 8390665 = 6292999) B6292999
theorem B11187553 : Blo 1937435 11187553 := bstep (se 2 (by rfl) ⟨4195332, by rfl⟩ : syracuseStep 11187553 = 8390665) B8390665
theorem B14916737 : Blo 1937435 14916737 := bstep (se 2 (by rfl) ⟨5593776, by rfl⟩ : syracuseStep 14916737 = 11187553) B11187553
theorem B9944491 : Blo 1937435 9944491 := bstep (se 1 (by rfl) ⟨7458368, by rfl⟩ : syracuseStep 9944491 = 14916737) B14916737
theorem B13259321 : Blo 1937435 13259321 := bstep (se 2 (by rfl) ⟨4972245, by rfl⟩ : syracuseStep 13259321 = 9944491) B9944491
theorem B8839547 : Blo 1937435 8839547 := bstep (se 1 (by rfl) ⟨6629660, by rfl⟩ : syracuseStep 8839547 = 13259321) B13259321
theorem B5893031 : Blo 1937435 5893031 := bstep (se 1 (by rfl) ⟨4419773, by rfl⟩ : syracuseStep 5893031 = 8839547) B8839547
theorem B15714749 : Blo 1937435 15714749 := bstep (se 3 (by rfl) ⟨2946515, by rfl⟩ : syracuseStep 15714749 = 5893031) B5893031
theorem B41905997 : Blo 1937435 41905997 := bstep (se 3 (by rfl) ⟨7857374, by rfl⟩ : syracuseStep 41905997 = 15714749) B15714749
theorem B27937331 : Blo 1937435 27937331 := bstep (se 1 (by rfl) ⟨20952998, by rfl⟩ : syracuseStep 27937331 = 41905997) B41905997
theorem B18624887 : Blo 1937435 18624887 := bstep (se 1 (by rfl) ⟨13968665, by rfl⟩ : syracuseStep 18624887 = 27937331) B27937331
theorem B12416591 : Blo 1937435 12416591 := bstep (se 1 (by rfl) ⟨9312443, by rfl⟩ : syracuseStep 12416591 = 18624887) B18624887
theorem B8277727 : Blo 1937435 8277727 := bstep (se 1 (by rfl) ⟨6208295, by rfl⟩ : syracuseStep 8277727 = 12416591) B12416591
theorem B11036969 : Blo 1937435 11036969 := bstep (se 2 (by rfl) ⟨4138863, by rfl⟩ : syracuseStep 11036969 = 8277727) B8277727
theorem B7357979 : Blo 1937435 7357979 := bstep (se 1 (by rfl) ⟨5518484, by rfl⟩ : syracuseStep 7357979 = 11036969) B11036969
theorem B4905319 : Blo 1937435 4905319 := bstep (se 1 (by rfl) ⟨3678989, by rfl⟩ : syracuseStep 4905319 = 7357979) B7357979
theorem B6540425 : Blo 1937435 6540425 := bstep (se 2 (by rfl) ⟨2452659, by rfl⟩ : syracuseStep 6540425 = 4905319) B4905319
theorem B4360283 : Blo 1937435 4360283 := bstep (se 1 (by rfl) ⟨3270212, by rfl⟩ : syracuseStep 4360283 = 6540425) B6540425
theorem B2906855 : Blo 1937435 2906855 := bstep (se 1 (by rfl) ⟨2180141, by rfl⟩ : syracuseStep 2906855 = 4360283) B4360283
theorem B1937903 : Blo 1937435 1937903 := bstep (se 1 (by rfl) ⟨1453427, by rfl⟩ : syracuseStep 1937903 = 2906855) B2906855
theorem B2906861 : Blo 1937435 2906861 := bbase (se 3 (by rfl) ⟨545036, by rfl⟩ : syracuseStep 2906861 = 1090073) (by norm_num)
theorem B1937907 : Blo 1937435 1937907 := bstep (se 1 (by rfl) ⟨1453430, by rfl⟩ : syracuseStep 1937907 = 2906861) B2906861
theorem B4360301 : Blo 1937435 4360301 := bbase (se 3 (by rfl) ⟨817556, by rfl⟩ : syracuseStep 4360301 = 1635113) (by norm_num)
theorem B2906867 : Blo 1937435 2906867 := bstep (se 1 (by rfl) ⟨2180150, by rfl⟩ : syracuseStep 2906867 = 4360301) B4360301
theorem B1937911 : Blo 1937435 1937911 := bstep (se 1 (by rfl) ⟨1453433, by rfl⟩ : syracuseStep 1937911 = 2906867) B2906867
theorem B3679013 : Blo 1937435 3679013 := bbase (se 4 (by rfl) ⟨344907, by rfl⟩ : syracuseStep 3679013 = 689815) (by norm_num)
theorem B2452675 : Blo 1937435 2452675 := bstep (se 1 (by rfl) ⟨1839506, by rfl⟩ : syracuseStep 2452675 = 3679013) B3679013
theorem B3270233 : Blo 1937435 3270233 := bstep (se 2 (by rfl) ⟨1226337, by rfl⟩ : syracuseStep 3270233 = 2452675) B2452675
theorem B2180155 : Blo 1937435 2180155 := bstep (se 1 (by rfl) ⟨1635116, by rfl⟩ : syracuseStep 2180155 = 3270233) B3270233
theorem B2906873 : Blo 1937435 2906873 := bstep (se 2 (by rfl) ⟨1090077, by rfl⟩ : syracuseStep 2906873 = 2180155) B2180155
theorem B1937915 : Blo 1937435 1937915 := bstep (se 1 (by rfl) ⟨1453436, by rfl⟩ : syracuseStep 1937915 = 2906873) B2906873
theorem B1991161 : Blo 1937435 1991161 := bbase (se 2 (by rfl) ⟨746685, by rfl⟩ : syracuseStep 1991161 = 1493371) (by norm_num)
theorem B10619525 : Blo 1937435 10619525 := bstep (se 4 (by rfl) ⟨995580, by rfl⟩ : syracuseStep 10619525 = 1991161) B1991161
theorem B28318733 : Blo 1937435 28318733 := bstep (se 3 (by rfl) ⟨5309762, by rfl⟩ : syracuseStep 28318733 = 10619525) B10619525
theorem B18879155 : Blo 1937435 18879155 := bstep (se 1 (by rfl) ⟨14159366, by rfl⟩ : syracuseStep 18879155 = 28318733) B28318733
theorem B12586103 : Blo 1937435 12586103 := bstep (se 1 (by rfl) ⟨9439577, by rfl⟩ : syracuseStep 12586103 = 18879155) B18879155
theorem B8390735 : Blo 1937435 8390735 := bstep (se 1 (by rfl) ⟨6293051, by rfl⟩ : syracuseStep 8390735 = 12586103) B12586103
theorem B5593823 : Blo 1937435 5593823 := bstep (se 1 (by rfl) ⟨4195367, by rfl⟩ : syracuseStep 5593823 = 8390735) B8390735
theorem B3729215 : Blo 1937435 3729215 := bstep (se 1 (by rfl) ⟨2796911, by rfl⟩ : syracuseStep 3729215 = 5593823) B5593823
theorem B2486143 : Blo 1937435 2486143 := bstep (se 1 (by rfl) ⟨1864607, by rfl⟩ : syracuseStep 2486143 = 3729215) B3729215
theorem B13259429 : Blo 1937435 13259429 := bstep (se 4 (by rfl) ⟨1243071, by rfl⟩ : syracuseStep 13259429 = 2486143) B2486143
theorem B8839619 : Blo 1937435 8839619 := bstep (se 1 (by rfl) ⟨6629714, by rfl⟩ : syracuseStep 8839619 = 13259429) B13259429
theorem B5893079 : Blo 1937435 5893079 := bstep (se 1 (by rfl) ⟨4419809, by rfl⟩ : syracuseStep 5893079 = 8839619) B8839619
theorem B15714877 : Blo 1937435 15714877 := bstep (se 3 (by rfl) ⟨2946539, by rfl⟩ : syracuseStep 15714877 = 5893079) B5893079
theorem B20953169 : Blo 1937435 20953169 := bstep (se 2 (by rfl) ⟨7857438, by rfl⟩ : syracuseStep 20953169 = 15714877) B15714877
theorem B13968779 : Blo 1937435 13968779 := bstep (se 1 (by rfl) ⟨10476584, by rfl⟩ : syracuseStep 13968779 = 20953169) B20953169
theorem B37250077 : Blo 1937435 37250077 := bstep (se 3 (by rfl) ⟨6984389, by rfl⟩ : syracuseStep 37250077 = 13968779) B13968779
theorem B49666769 : Blo 1937435 49666769 := bstep (se 2 (by rfl) ⟨18625038, by rfl⟩ : syracuseStep 49666769 = 37250077) B37250077
theorem B33111179 : Blo 1937435 33111179 := bstep (se 1 (by rfl) ⟨24833384, by rfl⟩ : syracuseStep 33111179 = 49666769) B49666769
theorem B22074119 : Blo 1937435 22074119 := bstep (se 1 (by rfl) ⟨16555589, by rfl⟩ : syracuseStep 22074119 = 33111179) B33111179
theorem B14716079 : Blo 1937435 14716079 := bstep (se 1 (by rfl) ⟨11037059, by rfl⟩ : syracuseStep 14716079 = 22074119) B22074119
theorem B9810719 : Blo 1937435 9810719 := bstep (se 1 (by rfl) ⟨7358039, by rfl⟩ : syracuseStep 9810719 = 14716079) B14716079
theorem B6540479 : Blo 1937435 6540479 := bstep (se 1 (by rfl) ⟨4905359, by rfl⟩ : syracuseStep 6540479 = 9810719) B9810719
theorem B4360319 : Blo 1937435 4360319 := bstep (se 1 (by rfl) ⟨3270239, by rfl⟩ : syracuseStep 4360319 = 6540479) B6540479
theorem B2906879 : Blo 1937435 2906879 := bstep (se 1 (by rfl) ⟨2180159, by rfl⟩ : syracuseStep 2906879 = 4360319) B4360319
theorem B1937919 : Blo 1937435 1937919 := bstep (se 1 (by rfl) ⟨1453439, by rfl⟩ : syracuseStep 1937919 = 2906879) B2906879
theorem B2906885 : Blo 1937435 2906885 := bbase (se 4 (by rfl) ⟨272520, by rfl⟩ : syracuseStep 2906885 = 545041) (by norm_num)
theorem B1937923 : Blo 1937435 1937923 := bstep (se 1 (by rfl) ⟨1453442, by rfl⟩ : syracuseStep 1937923 = 2906885) B2906885
theorem B3270253 : Blo 1937435 3270253 := bbase (se 3 (by rfl) ⟨613172, by rfl⟩ : syracuseStep 3270253 = 1226345) (by norm_num)
theorem B4360337 : Blo 1937435 4360337 := bstep (se 2 (by rfl) ⟨1635126, by rfl⟩ : syracuseStep 4360337 = 3270253) B3270253
theorem B2906891 : Blo 1937435 2906891 := bstep (se 1 (by rfl) ⟨2180168, by rfl⟩ : syracuseStep 2906891 = 4360337) B4360337
theorem B1937927 : Blo 1937435 1937927 := bstep (se 1 (by rfl) ⟨1453445, by rfl⟩ : syracuseStep 1937927 = 2906891) B2906891
theorem B2180173 : Blo 1937435 2180173 := bbase (se 3 (by rfl) ⟨408782, by rfl⟩ : syracuseStep 2180173 = 817565) (by norm_num)
theorem B2906897 : Blo 1937435 2906897 := bstep (se 2 (by rfl) ⟨1090086, by rfl⟩ : syracuseStep 2906897 = 2180173) B2180173
theorem B1937931 : Blo 1937435 1937931 := bstep (se 1 (by rfl) ⟨1453448, by rfl⟩ : syracuseStep 1937931 = 2906897) B2906897
theorem B6540533 : Blo 1937435 6540533 := bbase (se 5 (by rfl) ⟨306587, by rfl⟩ : syracuseStep 6540533 = 613175) (by norm_num)
theorem B4360355 : Blo 1937435 4360355 := bstep (se 1 (by rfl) ⟨3270266, by rfl⟩ : syracuseStep 4360355 = 6540533) B6540533
theorem B2906903 : Blo 1937435 2906903 := bstep (se 1 (by rfl) ⟨2180177, by rfl⟩ : syracuseStep 2906903 = 4360355) B4360355
theorem B1937935 : Blo 1937435 1937935 := bstep (se 1 (by rfl) ⟨1453451, by rfl⟩ : syracuseStep 1937935 = 2906903) B2906903
theorem B2906909 : Blo 1937435 2906909 := bbase (se 3 (by rfl) ⟨545045, by rfl⟩ : syracuseStep 2906909 = 1090091) (by norm_num)
theorem B1937939 : Blo 1937435 1937939 := bstep (se 1 (by rfl) ⟨1453454, by rfl⟩ : syracuseStep 1937939 = 2906909) B2906909
theorem B4360373 : Blo 1937435 4360373 := bbase (se 5 (by rfl) ⟨204392, by rfl⟩ : syracuseStep 4360373 = 408785) (by norm_num)
theorem B2906915 : Blo 1937435 2906915 := bstep (se 1 (by rfl) ⟨2180186, by rfl⟩ : syracuseStep 2906915 = 4360373) B4360373
theorem B1937943 : Blo 1937435 1937943 := bstep (se 1 (by rfl) ⟨1453457, by rfl⟩ : syracuseStep 1937943 = 2906915) B2906915
theorem B7857557 : Blo 1937435 7857557 := bbase (se 6 (by rfl) ⟨184161, by rfl⟩ : syracuseStep 7857557 = 368323) (by norm_num)
theorem B5238371 : Blo 1937435 5238371 := bstep (se 1 (by rfl) ⟨3928778, by rfl⟩ : syracuseStep 5238371 = 7857557) B7857557
theorem B3492247 : Blo 1937435 3492247 := bstep (se 1 (by rfl) ⟨2619185, by rfl⟩ : syracuseStep 3492247 = 5238371) B5238371
theorem B4656329 : Blo 1937435 4656329 := bstep (se 2 (by rfl) ⟨1746123, by rfl⟩ : syracuseStep 4656329 = 3492247) B3492247
theorem B3104219 : Blo 1937435 3104219 := bstep (se 1 (by rfl) ⟨2328164, by rfl⟩ : syracuseStep 3104219 = 4656329) B4656329
theorem B2069479 : Blo 1937435 2069479 := bstep (se 1 (by rfl) ⟨1552109, by rfl⟩ : syracuseStep 2069479 = 3104219) B3104219
theorem B11037221 : Blo 1937435 11037221 := bstep (se 4 (by rfl) ⟨1034739, by rfl⟩ : syracuseStep 11037221 = 2069479) B2069479
theorem B7358147 : Blo 1937435 7358147 := bstep (se 1 (by rfl) ⟨5518610, by rfl⟩ : syracuseStep 7358147 = 11037221) B11037221
theorem B4905431 : Blo 1937435 4905431 := bstep (se 1 (by rfl) ⟨3679073, by rfl⟩ : syracuseStep 4905431 = 7358147) B7358147
theorem B3270287 : Blo 1937435 3270287 := bstep (se 1 (by rfl) ⟨2452715, by rfl⟩ : syracuseStep 3270287 = 4905431) B4905431
theorem B2180191 : Blo 1937435 2180191 := bstep (se 1 (by rfl) ⟨1635143, by rfl⟩ : syracuseStep 2180191 = 3270287) B3270287
theorem B2906921 : Blo 1937435 2906921 := bstep (se 2 (by rfl) ⟨1090095, by rfl⟩ : syracuseStep 2906921 = 2180191) B2180191
theorem B1937947 : Blo 1937435 1937947 := bstep (se 1 (by rfl) ⟨1453460, by rfl⟩ : syracuseStep 1937947 = 2906921) B2906921
theorem B2328169 : Blo 1937435 2328169 := bbase (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) (by norm_num)
theorem B3104225 : Blo 1937435 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B2069483 : Blo 1937435 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B5518621 : Blo 1937435 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B7358161 : Blo 1937435 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B9810881 : Blo 1937435 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B6540587 : Blo 1937435 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B4360391 : Blo 1937435 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B2906927 : Blo 1937435 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B1937951 : Blo 1937435 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B2906933 : Blo 1937435 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B1937955 : Blo 1937435 1937955 := bstep (se 1 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 1937955 = 2906933) B2906933
theorem B4905461 : Blo 1937435 4905461 := bbase (se 5 (by rfl) ⟨229943, by rfl⟩ : syracuseStep 4905461 = 459887) (by norm_num)
theorem B3270307 : Blo 1937435 3270307 := bstep (se 1 (by rfl) ⟨2452730, by rfl⟩ : syracuseStep 3270307 = 4905461) B4905461
theorem B4360409 : Blo 1937435 4360409 := bstep (se 2 (by rfl) ⟨1635153, by rfl⟩ : syracuseStep 4360409 = 3270307) B3270307
theorem B2906939 : Blo 1937435 2906939 := bstep (se 1 (by rfl) ⟨2180204, by rfl⟩ : syracuseStep 2906939 = 4360409) B4360409
theorem B1937959 : Blo 1937435 1937959 := bstep (se 1 (by rfl) ⟨1453469, by rfl⟩ : syracuseStep 1937959 = 2906939) B2906939
theorem B2180209 : Blo 1937435 2180209 := bbase (se 2 (by rfl) ⟨817578, by rfl⟩ : syracuseStep 2180209 = 1635157) (by norm_num)
theorem B2906945 : Blo 1937435 2906945 := bstep (se 2 (by rfl) ⟨1090104, by rfl⟩ : syracuseStep 2906945 = 2180209) B2180209
theorem B1937963 : Blo 1937435 1937963 := bstep (se 1 (by rfl) ⟨1453472, by rfl⟩ : syracuseStep 1937963 = 2906945) B2906945
theorem B6208501 : Blo 1937435 6208501 := bbase (se 5 (by rfl) ⟨291023, by rfl⟩ : syracuseStep 6208501 = 582047) (by norm_num)
theorem B8278001 : Blo 1937435 8278001 := bstep (se 2 (by rfl) ⟨3104250, by rfl⟩ : syracuseStep 8278001 = 6208501) B6208501
theorem B5518667 : Blo 1937435 5518667 := bstep (se 1 (by rfl) ⟨4139000, by rfl⟩ : syracuseStep 5518667 = 8278001) B8278001
theorem B3679111 : Blo 1937435 3679111 := bstep (se 1 (by rfl) ⟨2759333, by rfl⟩ : syracuseStep 3679111 = 5518667) B5518667
theorem B4905481 : Blo 1937435 4905481 := bstep (se 2 (by rfl) ⟨1839555, by rfl⟩ : syracuseStep 4905481 = 3679111) B3679111
theorem B6540641 : Blo 1937435 6540641 := bstep (se 2 (by rfl) ⟨2452740, by rfl⟩ : syracuseStep 6540641 = 4905481) B4905481
theorem B4360427 : Blo 1937435 4360427 := bstep (se 1 (by rfl) ⟨3270320, by rfl⟩ : syracuseStep 4360427 = 6540641) B6540641
theorem B2906951 : Blo 1937435 2906951 := bstep (se 1 (by rfl) ⟨2180213, by rfl⟩ : syracuseStep 2906951 = 4360427) B4360427
theorem B1937967 : Blo 1937435 1937967 := bstep (se 1 (by rfl) ⟨1453475, by rfl⟩ : syracuseStep 1937967 = 2906951) B2906951
theorem B2906957 : Blo 1937435 2906957 := bbase (se 3 (by rfl) ⟨545054, by rfl⟩ : syracuseStep 2906957 = 1090109) (by norm_num)
theorem B1937971 : Blo 1937435 1937971 := bstep (se 1 (by rfl) ⟨1453478, by rfl⟩ : syracuseStep 1937971 = 2906957) B2906957
theorem B4360445 : Blo 1937435 4360445 := bbase (se 3 (by rfl) ⟨817583, by rfl⟩ : syracuseStep 4360445 = 1635167) (by norm_num)
theorem B2906963 : Blo 1937435 2906963 := bstep (se 1 (by rfl) ⟨2180222, by rfl⟩ : syracuseStep 2906963 = 4360445) B4360445
theorem B1937975 : Blo 1937435 1937975 := bstep (se 1 (by rfl) ⟨1453481, by rfl⟩ : syracuseStep 1937975 = 2906963) B2906963
theorem B3270341 : Blo 1937435 3270341 := bbase (se 4 (by rfl) ⟨306594, by rfl⟩ : syracuseStep 3270341 = 613189) (by norm_num)
theorem B2180227 : Blo 1937435 2180227 := bstep (se 1 (by rfl) ⟨1635170, by rfl⟩ : syracuseStep 2180227 = 3270341) B3270341
theorem B2906969 : Blo 1937435 2906969 := bstep (se 2 (by rfl) ⟨1090113, by rfl⟩ : syracuseStep 2906969 = 2180227) B2180227
theorem B1937979 : Blo 1937435 1937979 := bstep (se 1 (by rfl) ⟨1453484, by rfl⟩ : syracuseStep 1937979 = 2906969) B2906969
theorem B14716565 : Blo 1937435 14716565 := bbase (se 6 (by rfl) ⟨344919, by rfl⟩ : syracuseStep 14716565 = 689839) (by norm_num)
theorem B9811043 : Blo 1937435 9811043 := bstep (se 1 (by rfl) ⟨7358282, by rfl⟩ : syracuseStep 9811043 = 14716565) B14716565
theorem B6540695 : Blo 1937435 6540695 := bstep (se 1 (by rfl) ⟨4905521, by rfl⟩ : syracuseStep 6540695 = 9811043) B9811043
theorem B4360463 : Blo 1937435 4360463 := bstep (se 1 (by rfl) ⟨3270347, by rfl⟩ : syracuseStep 4360463 = 6540695) B6540695
theorem B2906975 : Blo 1937435 2906975 := bstep (se 1 (by rfl) ⟨2180231, by rfl⟩ : syracuseStep 2906975 = 4360463) B4360463
theorem B1937983 : Blo 1937435 1937983 := bstep (se 1 (by rfl) ⟨1453487, by rfl⟩ : syracuseStep 1937983 = 2906975) B2906975
theorem B2906981 : Blo 1937435 2906981 := bbase (se 4 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 2906981 = 545059) (by norm_num)
theorem B1937987 : Blo 1937435 1937987 := bstep (se 1 (by rfl) ⟨1453490, by rfl⟩ : syracuseStep 1937987 = 2906981) B2906981
theorem B3679157 : Blo 1937435 3679157 := bbase (se 5 (by rfl) ⟨172460, by rfl⟩ : syracuseStep 3679157 = 344921) (by norm_num)
theorem B2452771 : Blo 1937435 2452771 := bstep (se 1 (by rfl) ⟨1839578, by rfl⟩ : syracuseStep 2452771 = 3679157) B3679157
theorem B3270361 : Blo 1937435 3270361 := bstep (se 2 (by rfl) ⟨1226385, by rfl⟩ : syracuseStep 3270361 = 2452771) B2452771
theorem B4360481 : Blo 1937435 4360481 := bstep (se 2 (by rfl) ⟨1635180, by rfl⟩ : syracuseStep 4360481 = 3270361) B3270361
theorem B2906987 : Blo 1937435 2906987 := bstep (se 1 (by rfl) ⟨2180240, by rfl⟩ : syracuseStep 2906987 = 4360481) B4360481
theorem B1937991 : Blo 1937435 1937991 := bstep (se 1 (by rfl) ⟨1453493, by rfl⟩ : syracuseStep 1937991 = 2906987) B2906987
theorem B2180245 : Blo 1937435 2180245 := bbase (se 6 (by rfl) ⟨51099, by rfl⟩ : syracuseStep 2180245 = 102199) (by norm_num)
theorem B2906993 : Blo 1937435 2906993 := bstep (se 2 (by rfl) ⟨1090122, by rfl⟩ : syracuseStep 2906993 = 2180245) B2180245
theorem B1937995 : Blo 1937435 1937995 := bstep (se 1 (by rfl) ⟨1453496, by rfl⟩ : syracuseStep 1937995 = 2906993) B2906993
theorem B2452781 : Blo 1937435 2452781 := bbase (se 3 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 2452781 = 919793) (by norm_num)
theorem B6540749 : Blo 1937435 6540749 := bstep (se 3 (by rfl) ⟨1226390, by rfl⟩ : syracuseStep 6540749 = 2452781) B2452781
theorem B4360499 : Blo 1937435 4360499 := bstep (se 1 (by rfl) ⟨3270374, by rfl⟩ : syracuseStep 4360499 = 6540749) B6540749
theorem B2906999 : Blo 1937435 2906999 := bstep (se 1 (by rfl) ⟨2180249, by rfl⟩ : syracuseStep 2906999 = 4360499) B4360499
theorem B1937999 : Blo 1937435 1937999 := bstep (se 1 (by rfl) ⟨1453499, by rfl⟩ : syracuseStep 1937999 = 2906999) B2906999
theorem B2907005 : Blo 1937435 2907005 := bbase (se 3 (by rfl) ⟨545063, by rfl⟩ : syracuseStep 2907005 = 1090127) (by norm_num)
theorem B1938003 : Blo 1937435 1938003 := bstep (se 1 (by rfl) ⟨1453502, by rfl⟩ : syracuseStep 1938003 = 2907005) B2907005
theorem B4360517 : Blo 1937435 4360517 := bbase (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) (by norm_num)
theorem B2907011 : Blo 1937435 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B1938007 : Blo 1937435 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B9312965 : Blo 1937435 9312965 := bbase (se 4 (by rfl) ⟨873090, by rfl⟩ : syracuseStep 9312965 = 1746181) (by norm_num)
theorem B6208643 : Blo 1937435 6208643 := bstep (se 1 (by rfl) ⟨4656482, by rfl⟩ : syracuseStep 6208643 = 9312965) B9312965
theorem B4139095 : Blo 1937435 4139095 := bstep (se 1 (by rfl) ⟨3104321, by rfl⟩ : syracuseStep 4139095 = 6208643) B6208643
theorem B5518793 : Blo 1937435 5518793 := bstep (se 2 (by rfl) ⟨2069547, by rfl⟩ : syracuseStep 5518793 = 4139095) B4139095
theorem B3679195 : Blo 1937435 3679195 := bstep (se 1 (by rfl) ⟨2759396, by rfl⟩ : syracuseStep 3679195 = 5518793) B5518793
theorem B4905593 : Blo 1937435 4905593 := bstep (se 2 (by rfl) ⟨1839597, by rfl⟩ : syracuseStep 4905593 = 3679195) B3679195
theorem B3270395 : Blo 1937435 3270395 := bstep (se 1 (by rfl) ⟨2452796, by rfl⟩ : syracuseStep 3270395 = 4905593) B4905593
theorem B2180263 : Blo 1937435 2180263 := bstep (se 1 (by rfl) ⟨1635197, by rfl⟩ : syracuseStep 2180263 = 3270395) B3270395
theorem B2907017 : Blo 1937435 2907017 := bstep (se 2 (by rfl) ⟨1090131, by rfl⟩ : syracuseStep 2907017 = 2180263) B2180263
theorem B1938011 : Blo 1937435 1938011 := bstep (se 1 (by rfl) ⟨1453508, by rfl⟩ : syracuseStep 1938011 = 2907017) B2907017
theorem B9811205 : Blo 1937435 9811205 := bbase (se 4 (by rfl) ⟨919800, by rfl⟩ : syracuseStep 9811205 = 1839601) (by norm_num)
theorem B6540803 : Blo 1937435 6540803 := bstep (se 1 (by rfl) ⟨4905602, by rfl⟩ : syracuseStep 6540803 = 9811205) B9811205
theorem B4360535 : Blo 1937435 4360535 := bstep (se 1 (by rfl) ⟨3270401, by rfl⟩ : syracuseStep 4360535 = 6540803) B6540803
theorem B2907023 : Blo 1937435 2907023 := bstep (se 1 (by rfl) ⟨2180267, by rfl⟩ : syracuseStep 2907023 = 4360535) B4360535
theorem B1938015 : Blo 1937435 1938015 := bstep (se 1 (by rfl) ⟨1453511, by rfl⟩ : syracuseStep 1938015 = 2907023) B2907023
theorem B2907029 : Blo 1937435 2907029 := bbase (se 6 (by rfl) ⟨68133, by rfl⟩ : syracuseStep 2907029 = 136267) (by norm_num)
theorem B1938019 : Blo 1937435 1938019 := bstep (se 1 (by rfl) ⟨1453514, by rfl⟩ : syracuseStep 1938019 = 2907029) B2907029
theorem B11037653 : Blo 1937435 11037653 := bbase (se 7 (by rfl) ⟨129347, by rfl⟩ : syracuseStep 11037653 = 258695) (by norm_num)
theorem B7358435 : Blo 1937435 7358435 := bstep (se 1 (by rfl) ⟨5518826, by rfl⟩ : syracuseStep 7358435 = 11037653) B11037653
theorem B4905623 : Blo 1937435 4905623 := bstep (se 1 (by rfl) ⟨3679217, by rfl⟩ : syracuseStep 4905623 = 7358435) B7358435
theorem B3270415 : Blo 1937435 3270415 := bstep (se 1 (by rfl) ⟨2452811, by rfl⟩ : syracuseStep 3270415 = 4905623) B4905623
theorem B4360553 : Blo 1937435 4360553 := bstep (se 2 (by rfl) ⟨1635207, by rfl⟩ : syracuseStep 4360553 = 3270415) B3270415
theorem B2907035 : Blo 1937435 2907035 := bstep (se 1 (by rfl) ⟨2180276, by rfl⟩ : syracuseStep 2907035 = 4360553) B4360553
theorem B1938023 : Blo 1937435 1938023 := bstep (se 1 (by rfl) ⟨1453517, by rfl⟩ : syracuseStep 1938023 = 2907035) B2907035
theorem B2180281 : Blo 1937435 2180281 := bbase (se 2 (by rfl) ⟨817605, by rfl⟩ : syracuseStep 2180281 = 1635211) (by norm_num)
theorem B2907041 : Blo 1937435 2907041 := bstep (se 2 (by rfl) ⟨1090140, by rfl⟩ : syracuseStep 2907041 = 2180281) B2180281
theorem B1938027 : Blo 1937435 1938027 := bstep (se 1 (by rfl) ⟨1453520, by rfl⟩ : syracuseStep 1938027 = 2907041) B2907041
theorem B2328265 : Blo 1937435 2328265 := bbase (se 2 (by rfl) ⟨873099, by rfl⟩ : syracuseStep 2328265 = 1746199) (by norm_num)
theorem B3104353 : Blo 1937435 3104353 := bstep (se 2 (by rfl) ⟨1164132, by rfl⟩ : syracuseStep 3104353 = 2328265) B2328265
theorem B4139137 : Blo 1937435 4139137 := bstep (se 2 (by rfl) ⟨1552176, by rfl⟩ : syracuseStep 4139137 = 3104353) B3104353
theorem B5518849 : Blo 1937435 5518849 := bstep (se 2 (by rfl) ⟨2069568, by rfl⟩ : syracuseStep 5518849 = 4139137) B4139137
theorem B7358465 : Blo 1937435 7358465 := bstep (se 2 (by rfl) ⟨2759424, by rfl⟩ : syracuseStep 7358465 = 5518849) B5518849
theorem B4905643 : Blo 1937435 4905643 := bstep (se 1 (by rfl) ⟨3679232, by rfl⟩ : syracuseStep 4905643 = 7358465) B7358465
theorem B6540857 : Blo 1937435 6540857 := bstep (se 2 (by rfl) ⟨2452821, by rfl⟩ : syracuseStep 6540857 = 4905643) B4905643
theorem B4360571 : Blo 1937435 4360571 := bstep (se 1 (by rfl) ⟨3270428, by rfl⟩ : syracuseStep 4360571 = 6540857) B6540857
theorem B2907047 : Blo 1937435 2907047 := bstep (se 1 (by rfl) ⟨2180285, by rfl⟩ : syracuseStep 2907047 = 4360571) B4360571
theorem B1938031 : Blo 1937435 1938031 := bstep (se 1 (by rfl) ⟨1453523, by rfl⟩ : syracuseStep 1938031 = 2907047) B2907047
theorem B2907053 : Blo 1937435 2907053 := bbase (se 3 (by rfl) ⟨545072, by rfl⟩ : syracuseStep 2907053 = 1090145) (by norm_num)
theorem B1938035 : Blo 1937435 1938035 := bstep (se 1 (by rfl) ⟨1453526, by rfl⟩ : syracuseStep 1938035 = 2907053) B2907053
theorem B4360589 : Blo 1937435 4360589 := bbase (se 3 (by rfl) ⟨817610, by rfl⟩ : syracuseStep 4360589 = 1635221) (by norm_num)
theorem B2907059 : Blo 1937435 2907059 := bstep (se 1 (by rfl) ⟨2180294, by rfl⟩ : syracuseStep 2907059 = 4360589) B4360589
theorem B1938039 : Blo 1937435 1938039 := bstep (se 1 (by rfl) ⟨1453529, by rfl⟩ : syracuseStep 1938039 = 2907059) B2907059
theorem B2452837 : Blo 1937435 2452837 := bbase (se 4 (by rfl) ⟨229953, by rfl⟩ : syracuseStep 2452837 = 459907) (by norm_num)
theorem B3270449 : Blo 1937435 3270449 := bstep (se 2 (by rfl) ⟨1226418, by rfl⟩ : syracuseStep 3270449 = 2452837) B2452837
theorem B2180299 : Blo 1937435 2180299 := bstep (se 1 (by rfl) ⟨1635224, by rfl⟩ : syracuseStep 2180299 = 3270449) B3270449
theorem B2907065 : Blo 1937435 2907065 := bstep (se 2 (by rfl) ⟨1090149, by rfl⟩ : syracuseStep 2907065 = 2180299) B2180299
theorem B1938043 : Blo 1937435 1938043 := bstep (se 1 (by rfl) ⟨1453532, by rfl⟩ : syracuseStep 1938043 = 2907065) B2907065
theorem B3315077 : Blo 1937435 3315077 := bbase (se 4 (by rfl) ⟨310788, by rfl⟩ : syracuseStep 3315077 = 621577) (by norm_num)
theorem B2210051 : Blo 1937435 2210051 := bstep (se 1 (by rfl) ⟨1657538, by rfl⟩ : syracuseStep 2210051 = 3315077) B3315077
theorem B5893469 : Blo 1937435 5893469 := bstep (se 3 (by rfl) ⟨1105025, by rfl⟩ : syracuseStep 5893469 = 2210051) B2210051
theorem B3928979 : Blo 1937435 3928979 := bstep (se 1 (by rfl) ⟨2946734, by rfl⟩ : syracuseStep 3928979 = 5893469) B5893469
theorem B10477277 : Blo 1937435 10477277 := bstep (se 3 (by rfl) ⟨1964489, by rfl⟩ : syracuseStep 10477277 = 3928979) B3928979
theorem B6984851 : Blo 1937435 6984851 := bstep (se 1 (by rfl) ⟨5238638, by rfl⟩ : syracuseStep 6984851 = 10477277) B10477277
theorem B18626269 : Blo 1937435 18626269 := bstep (se 3 (by rfl) ⟨3492425, by rfl⟩ : syracuseStep 18626269 = 6984851) B6984851
theorem B24835025 : Blo 1937435 24835025 := bstep (se 2 (by rfl) ⟨9313134, by rfl⟩ : syracuseStep 24835025 = 18626269) B18626269
theorem B16556683 : Blo 1937435 16556683 := bstep (se 1 (by rfl) ⟨12417512, by rfl⟩ : syracuseStep 16556683 = 24835025) B24835025
theorem B22075577 : Blo 1937435 22075577 := bstep (se 2 (by rfl) ⟨8278341, by rfl⟩ : syracuseStep 22075577 = 16556683) B16556683
theorem B14717051 : Blo 1937435 14717051 := bstep (se 1 (by rfl) ⟨11037788, by rfl⟩ : syracuseStep 14717051 = 22075577) B22075577
theorem B9811367 : Blo 1937435 9811367 := bstep (se 1 (by rfl) ⟨7358525, by rfl⟩ : syracuseStep 9811367 = 14717051) B14717051
theorem B6540911 : Blo 1937435 6540911 := bstep (se 1 (by rfl) ⟨4905683, by rfl⟩ : syracuseStep 6540911 = 9811367) B9811367
theorem B4360607 : Blo 1937435 4360607 := bstep (se 1 (by rfl) ⟨3270455, by rfl⟩ : syracuseStep 4360607 = 6540911) B6540911
theorem B2907071 : Blo 1937435 2907071 := bstep (se 1 (by rfl) ⟨2180303, by rfl⟩ : syracuseStep 2907071 = 4360607) B4360607
theorem B1938047 : Blo 1937435 1938047 := bstep (se 1 (by rfl) ⟨1453535, by rfl⟩ : syracuseStep 1938047 = 2907071) B2907071
theorem B2907077 : Blo 1937435 2907077 := bbase (se 4 (by rfl) ⟨272538, by rfl⟩ : syracuseStep 2907077 = 545077) (by norm_num)
theorem B1938051 : Blo 1937435 1938051 := bstep (se 1 (by rfl) ⟨1453538, by rfl⟩ : syracuseStep 1938051 = 2907077) B2907077
theorem B3270469 : Blo 1937435 3270469 := bbase (se 4 (by rfl) ⟨306606, by rfl⟩ : syracuseStep 3270469 = 613213) (by norm_num)
theorem B4360625 : Blo 1937435 4360625 := bstep (se 2 (by rfl) ⟨1635234, by rfl⟩ : syracuseStep 4360625 = 3270469) B3270469
theorem B2907083 : Blo 1937435 2907083 := bstep (se 1 (by rfl) ⟨2180312, by rfl⟩ : syracuseStep 2907083 = 4360625) B4360625
theorem B1938055 : Blo 1937435 1938055 := bstep (se 1 (by rfl) ⟨1453541, by rfl⟩ : syracuseStep 1938055 = 2907083) B2907083
theorem B2180317 : Blo 1937435 2180317 := bbase (se 3 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 2180317 = 817619) (by norm_num)
theorem B2907089 : Blo 1937435 2907089 := bstep (se 2 (by rfl) ⟨1090158, by rfl⟩ : syracuseStep 2907089 = 2180317) B2180317
theorem B1938059 : Blo 1937435 1938059 := bstep (se 1 (by rfl) ⟨1453544, by rfl⟩ : syracuseStep 1938059 = 2907089) B2907089
theorem B6540965 : Blo 1937435 6540965 := bbase (se 4 (by rfl) ⟨613215, by rfl⟩ : syracuseStep 6540965 = 1226431) (by norm_num)
theorem B4360643 : Blo 1937435 4360643 := bstep (se 1 (by rfl) ⟨3270482, by rfl⟩ : syracuseStep 4360643 = 6540965) B6540965
theorem B2907095 : Blo 1937435 2907095 := bstep (se 1 (by rfl) ⟨2180321, by rfl⟩ : syracuseStep 2907095 = 4360643) B4360643
theorem B1938063 : Blo 1937435 1938063 := bstep (se 1 (by rfl) ⟨1453547, by rfl⟩ : syracuseStep 1938063 = 2907095) B2907095
theorem B2907101 : Blo 1937435 2907101 := bbase (se 3 (by rfl) ⟨545081, by rfl⟩ : syracuseStep 2907101 = 1090163) (by norm_num)
theorem B1938067 : Blo 1937435 1938067 := bstep (se 1 (by rfl) ⟨1453550, by rfl⟩ : syracuseStep 1938067 = 2907101) B2907101
theorem B4360661 : Blo 1937435 4360661 := bbase (se 7 (by rfl) ⟨51101, by rfl⟩ : syracuseStep 4360661 = 102203) (by norm_num)
theorem B2907107 : Blo 1937435 2907107 := bstep (se 1 (by rfl) ⟨2180330, by rfl⟩ : syracuseStep 2907107 = 4360661) B4360661
theorem B1938071 : Blo 1937435 1938071 := bstep (se 1 (by rfl) ⟨1453553, by rfl⟩ : syracuseStep 1938071 = 2907107) B2907107
theorem B2392285 : Blo 1937435 2392285 := bbase (se 3 (by rfl) ⟨448553, by rfl⟩ : syracuseStep 2392285 = 897107) (by norm_num)
theorem B3189713 : Blo 1937435 3189713 := bstep (se 2 (by rfl) ⟨1196142, by rfl⟩ : syracuseStep 3189713 = 2392285) B2392285
theorem B8505901 : Blo 1937435 8505901 := bstep (se 3 (by rfl) ⟨1594856, by rfl⟩ : syracuseStep 8505901 = 3189713) B3189713
theorem B45364805 : Blo 1937435 45364805 := bstep (se 4 (by rfl) ⟨4252950, by rfl⟩ : syracuseStep 45364805 = 8505901) B8505901
theorem B30243203 : Blo 1937435 30243203 := bstep (se 1 (by rfl) ⟨22682402, by rfl⟩ : syracuseStep 30243203 = 45364805) B45364805
theorem B20162135 : Blo 1937435 20162135 := bstep (se 1 (by rfl) ⟨15121601, by rfl⟩ : syracuseStep 20162135 = 30243203) B30243203
theorem B13441423 : Blo 1937435 13441423 := bstep (se 1 (by rfl) ⟨10081067, by rfl⟩ : syracuseStep 13441423 = 20162135) B20162135
theorem B17921897 : Blo 1937435 17921897 := bstep (se 2 (by rfl) ⟨6720711, by rfl⟩ : syracuseStep 17921897 = 13441423) B13441423
theorem B11947931 : Blo 1937435 11947931 := bstep (se 1 (by rfl) ⟨8960948, by rfl⟩ : syracuseStep 11947931 = 17921897) B17921897
theorem B7965287 : Blo 1937435 7965287 := bstep (se 1 (by rfl) ⟨5973965, by rfl⟩ : syracuseStep 7965287 = 11947931) B11947931
theorem B5310191 : Blo 1937435 5310191 := bstep (se 1 (by rfl) ⟨3982643, by rfl⟩ : syracuseStep 5310191 = 7965287) B7965287
theorem B3540127 : Blo 1937435 3540127 := bstep (se 1 (by rfl) ⟨2655095, by rfl⟩ : syracuseStep 3540127 = 5310191) B5310191
theorem B4720169 : Blo 1937435 4720169 := bstep (se 2 (by rfl) ⟨1770063, by rfl⟩ : syracuseStep 4720169 = 3540127) B3540127
theorem B3146779 : Blo 1937435 3146779 := bstep (se 1 (by rfl) ⟨2360084, by rfl⟩ : syracuseStep 3146779 = 4720169) B4720169
theorem B16782821 : Blo 1937435 16782821 := bstep (se 4 (by rfl) ⟨1573389, by rfl⟩ : syracuseStep 16782821 = 3146779) B3146779
theorem B11188547 : Blo 1937435 11188547 := bstep (se 1 (by rfl) ⟨8391410, by rfl⟩ : syracuseStep 11188547 = 16782821) B16782821
theorem B7459031 : Blo 1937435 7459031 := bstep (se 1 (by rfl) ⟨5594273, by rfl⟩ : syracuseStep 7459031 = 11188547) B11188547
theorem B4972687 : Blo 1937435 4972687 := bstep (se 1 (by rfl) ⟨3729515, by rfl⟩ : syracuseStep 4972687 = 7459031) B7459031
theorem B106083989 : Blo 1937435 106083989 := bstep (se 6 (by rfl) ⟨2486343, by rfl⟩ : syracuseStep 106083989 = 4972687) B4972687
theorem B70722659 : Blo 1937435 70722659 := bstep (se 1 (by rfl) ⟨53041994, by rfl⟩ : syracuseStep 70722659 = 106083989) B106083989
theorem B47148439 : Blo 1937435 47148439 := bstep (se 1 (by rfl) ⟨35361329, by rfl⟩ : syracuseStep 47148439 = 70722659) B70722659
theorem B62864585 : Blo 1937435 62864585 := bstep (se 2 (by rfl) ⟨23574219, by rfl⟩ : syracuseStep 62864585 = 47148439) B47148439
theorem B41909723 : Blo 1937435 41909723 := bstep (se 1 (by rfl) ⟨31432292, by rfl⟩ : syracuseStep 41909723 = 62864585) B62864585
theorem B27939815 : Blo 1937435 27939815 := bstep (se 1 (by rfl) ⟨20954861, by rfl⟩ : syracuseStep 27939815 = 41909723) B41909723
theorem B18626543 : Blo 1937435 18626543 := bstep (se 1 (by rfl) ⟨13969907, by rfl⟩ : syracuseStep 18626543 = 27939815) B27939815
theorem B12417695 : Blo 1937435 12417695 := bstep (se 1 (by rfl) ⟨9313271, by rfl⟩ : syracuseStep 12417695 = 18626543) B18626543
theorem B8278463 : Blo 1937435 8278463 := bstep (se 1 (by rfl) ⟨6208847, by rfl⟩ : syracuseStep 8278463 = 12417695) B12417695
theorem B5518975 : Blo 1937435 5518975 := bstep (se 1 (by rfl) ⟨4139231, by rfl⟩ : syracuseStep 5518975 = 8278463) B8278463
theorem B7358633 : Blo 1937435 7358633 := bstep (se 2 (by rfl) ⟨2759487, by rfl⟩ : syracuseStep 7358633 = 5518975) B5518975
theorem B4905755 : Blo 1937435 4905755 := bstep (se 1 (by rfl) ⟨3679316, by rfl⟩ : syracuseStep 4905755 = 7358633) B7358633
theorem B3270503 : Blo 1937435 3270503 := bstep (se 1 (by rfl) ⟨2452877, by rfl⟩ : syracuseStep 3270503 = 4905755) B4905755
theorem B2180335 : Blo 1937435 2180335 := bstep (se 1 (by rfl) ⟨1635251, by rfl⟩ : syracuseStep 2180335 = 3270503) B3270503
theorem B2907113 : Blo 1937435 2907113 := bstep (se 2 (by rfl) ⟨1090167, by rfl⟩ : syracuseStep 2907113 = 2180335) B2180335
theorem B1938075 : Blo 1937435 1938075 := bstep (se 1 (by rfl) ⟨1453556, by rfl⟩ : syracuseStep 1938075 = 2907113) B2907113
theorem B2097857 : Blo 1937435 2097857 := bbase (se 2 (by rfl) ⟨786696, by rfl⟩ : syracuseStep 2097857 = 1573393) (by norm_num)
theorem B5594285 : Blo 1937435 5594285 := bstep (se 3 (by rfl) ⟨1048928, by rfl⟩ : syracuseStep 5594285 = 2097857) B2097857
theorem B14918093 : Blo 1937435 14918093 := bstep (se 3 (by rfl) ⟨2797142, by rfl⟩ : syracuseStep 14918093 = 5594285) B5594285
theorem B9945395 : Blo 1937435 9945395 := bstep (se 1 (by rfl) ⟨7459046, by rfl⟩ : syracuseStep 9945395 = 14918093) B14918093
theorem B6630263 : Blo 1937435 6630263 := bstep (se 1 (by rfl) ⟨4972697, by rfl⟩ : syracuseStep 6630263 = 9945395) B9945395
theorem B4420175 : Blo 1937435 4420175 := bstep (se 1 (by rfl) ⟨3315131, by rfl⟩ : syracuseStep 4420175 = 6630263) B6630263
theorem B11787133 : Blo 1937435 11787133 := bstep (se 3 (by rfl) ⟨2210087, by rfl⟩ : syracuseStep 11787133 = 4420175) B4420175
theorem B15716177 : Blo 1937435 15716177 := bstep (se 2 (by rfl) ⟨5893566, by rfl⟩ : syracuseStep 15716177 = 11787133) B11787133
theorem B10477451 : Blo 1937435 10477451 := bstep (se 1 (by rfl) ⟨7858088, by rfl⟩ : syracuseStep 10477451 = 15716177) B15716177
theorem B6984967 : Blo 1937435 6984967 := bstep (se 1 (by rfl) ⟨5238725, by rfl⟩ : syracuseStep 6984967 = 10477451) B10477451
theorem B9313289 : Blo 1937435 9313289 := bstep (se 2 (by rfl) ⟨3492483, by rfl⟩ : syracuseStep 9313289 = 6984967) B6984967
theorem B6208859 : Blo 1937435 6208859 := bstep (se 1 (by rfl) ⟨4656644, by rfl⟩ : syracuseStep 6208859 = 9313289) B9313289
theorem B16556957 : Blo 1937435 16556957 := bstep (se 3 (by rfl) ⟨3104429, by rfl⟩ : syracuseStep 16556957 = 6208859) B6208859
theorem B11037971 : Blo 1937435 11037971 := bstep (se 1 (by rfl) ⟨8278478, by rfl⟩ : syracuseStep 11037971 = 16556957) B16556957
theorem B7358647 : Blo 1937435 7358647 := bstep (se 1 (by rfl) ⟨5518985, by rfl⟩ : syracuseStep 7358647 = 11037971) B11037971
theorem B9811529 : Blo 1937435 9811529 := bstep (se 2 (by rfl) ⟨3679323, by rfl⟩ : syracuseStep 9811529 = 7358647) B7358647
theorem B6541019 : Blo 1937435 6541019 := bstep (se 1 (by rfl) ⟨4905764, by rfl⟩ : syracuseStep 6541019 = 9811529) B9811529
theorem B4360679 : Blo 1937435 4360679 := bstep (se 1 (by rfl) ⟨3270509, by rfl⟩ : syracuseStep 4360679 = 6541019) B6541019
theorem B2907119 : Blo 1937435 2907119 := bstep (se 1 (by rfl) ⟨2180339, by rfl⟩ : syracuseStep 2907119 = 4360679) B4360679
theorem B1938079 : Blo 1937435 1938079 := bstep (se 1 (by rfl) ⟨1453559, by rfl⟩ : syracuseStep 1938079 = 2907119) B2907119
theorem B2907125 : Blo 1937435 2907125 := bbase (se 5 (by rfl) ⟨136271, by rfl⟩ : syracuseStep 2907125 = 272543) (by norm_num)
theorem B1938083 : Blo 1937435 1938083 := bstep (se 1 (by rfl) ⟨1453562, by rfl⟩ : syracuseStep 1938083 = 2907125) B2907125
theorem B2946797 : Blo 1937435 2946797 := bbase (se 3 (by rfl) ⟨552524, by rfl⟩ : syracuseStep 2946797 = 1105049) (by norm_num)
theorem B1964531 : Blo 1937435 1964531 := bstep (se 1 (by rfl) ⟨1473398, by rfl⟩ : syracuseStep 1964531 = 2946797) B2946797
theorem B5238749 : Blo 1937435 5238749 := bstep (se 3 (by rfl) ⟨982265, by rfl⟩ : syracuseStep 5238749 = 1964531) B1964531
theorem B3492499 : Blo 1937435 3492499 := bstep (se 1 (by rfl) ⟨2619374, by rfl⟩ : syracuseStep 3492499 = 5238749) B5238749
theorem B4656665 : Blo 1937435 4656665 := bstep (se 2 (by rfl) ⟨1746249, by rfl⟩ : syracuseStep 4656665 = 3492499) B3492499
theorem B3104443 : Blo 1937435 3104443 := bstep (se 1 (by rfl) ⟨2328332, by rfl⟩ : syracuseStep 3104443 = 4656665) B4656665
theorem B4139257 : Blo 1937435 4139257 := bstep (se 2 (by rfl) ⟨1552221, by rfl⟩ : syracuseStep 4139257 = 3104443) B3104443
theorem B5519009 : Blo 1937435 5519009 := bstep (se 2 (by rfl) ⟨2069628, by rfl⟩ : syracuseStep 5519009 = 4139257) B4139257
theorem B3679339 : Blo 1937435 3679339 := bstep (se 1 (by rfl) ⟨2759504, by rfl⟩ : syracuseStep 3679339 = 5519009) B5519009
theorem B4905785 : Blo 1937435 4905785 := bstep (se 2 (by rfl) ⟨1839669, by rfl⟩ : syracuseStep 4905785 = 3679339) B3679339
theorem B3270523 : Blo 1937435 3270523 := bstep (se 1 (by rfl) ⟨2452892, by rfl⟩ : syracuseStep 3270523 = 4905785) B4905785
theorem B4360697 : Blo 1937435 4360697 := bstep (se 2 (by rfl) ⟨1635261, by rfl⟩ : syracuseStep 4360697 = 3270523) B3270523
theorem B2907131 : Blo 1937435 2907131 := bstep (se 1 (by rfl) ⟨2180348, by rfl⟩ : syracuseStep 2907131 = 4360697) B4360697
theorem B1938087 : Blo 1937435 1938087 := bstep (se 1 (by rfl) ⟨1453565, by rfl⟩ : syracuseStep 1938087 = 2907131) B2907131
theorem B2180353 : Blo 1937435 2180353 := bbase (se 2 (by rfl) ⟨817632, by rfl⟩ : syracuseStep 2180353 = 1635265) (by norm_num)
theorem B2907137 : Blo 1937435 2907137 := bstep (se 2 (by rfl) ⟨1090176, by rfl⟩ : syracuseStep 2907137 = 2180353) B2180353
theorem B1938091 : Blo 1937435 1938091 := bstep (se 1 (by rfl) ⟨1453568, by rfl⟩ : syracuseStep 1938091 = 2907137) B2907137
theorem B4905805 : Blo 1937435 4905805 := bbase (se 3 (by rfl) ⟨919838, by rfl⟩ : syracuseStep 4905805 = 1839677) (by norm_num)
theorem B6541073 : Blo 1937435 6541073 := bstep (se 2 (by rfl) ⟨2452902, by rfl⟩ : syracuseStep 6541073 = 4905805) B4905805
theorem B4360715 : Blo 1937435 4360715 := bstep (se 1 (by rfl) ⟨3270536, by rfl⟩ : syracuseStep 4360715 = 6541073) B6541073
theorem B2907143 : Blo 1937435 2907143 := bstep (se 1 (by rfl) ⟨2180357, by rfl⟩ : syracuseStep 2907143 = 4360715) B4360715
theorem B1938095 : Blo 1937435 1938095 := bstep (se 1 (by rfl) ⟨1453571, by rfl⟩ : syracuseStep 1938095 = 2907143) B2907143
theorem B2907149 : Blo 1937435 2907149 := bbase (se 3 (by rfl) ⟨545090, by rfl⟩ : syracuseStep 2907149 = 1090181) (by norm_num)
theorem B1938099 : Blo 1937435 1938099 := bstep (se 1 (by rfl) ⟨1453574, by rfl⟩ : syracuseStep 1938099 = 2907149) B2907149
theorem B4360733 : Blo 1937435 4360733 := bbase (se 3 (by rfl) ⟨817637, by rfl⟩ : syracuseStep 4360733 = 1635275) (by norm_num)
theorem B2907155 : Blo 1937435 2907155 := bstep (se 1 (by rfl) ⟨2180366, by rfl⟩ : syracuseStep 2907155 = 4360733) B4360733
theorem B1938103 : Blo 1937435 1938103 := bstep (se 1 (by rfl) ⟨1453577, by rfl⟩ : syracuseStep 1938103 = 2907155) B2907155
theorem B3270557 : Blo 1937435 3270557 := bbase (se 3 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 3270557 = 1226459) (by norm_num)
theorem B2180371 : Blo 1937435 2180371 := bstep (se 1 (by rfl) ⟨1635278, by rfl⟩ : syracuseStep 2180371 = 3270557) B3270557
theorem B2907161 : Blo 1937435 2907161 := bstep (se 2 (by rfl) ⟨1090185, by rfl⟩ : syracuseStep 2907161 = 2180371) B2180371
theorem B1938107 : Blo 1937435 1938107 := bstep (se 1 (by rfl) ⟨1453580, by rfl⟩ : syracuseStep 1938107 = 2907161) B2907161
theorem B3492541 : Blo 1937435 3492541 := bbase (se 3 (by rfl) ⟨654851, by rfl⟩ : syracuseStep 3492541 = 1309703) (by norm_num)
theorem B18626885 : Blo 1937435 18626885 := bstep (se 4 (by rfl) ⟨1746270, by rfl⟩ : syracuseStep 18626885 = 3492541) B3492541
theorem B12417923 : Blo 1937435 12417923 := bstep (se 1 (by rfl) ⟨9313442, by rfl⟩ : syracuseStep 12417923 = 18626885) B18626885
theorem B8278615 : Blo 1937435 8278615 := bstep (se 1 (by rfl) ⟨6208961, by rfl⟩ : syracuseStep 8278615 = 12417923) B12417923
theorem B11038153 : Blo 1937435 11038153 := bstep (se 2 (by rfl) ⟨4139307, by rfl⟩ : syracuseStep 11038153 = 8278615) B8278615
theorem B14717537 : Blo 1937435 14717537 := bstep (se 2 (by rfl) ⟨5519076, by rfl⟩ : syracuseStep 14717537 = 11038153) B11038153
theorem B9811691 : Blo 1937435 9811691 := bstep (se 1 (by rfl) ⟨7358768, by rfl⟩ : syracuseStep 9811691 = 14717537) B14717537
theorem B6541127 : Blo 1937435 6541127 := bstep (se 1 (by rfl) ⟨4905845, by rfl⟩ : syracuseStep 6541127 = 9811691) B9811691
theorem B4360751 : Blo 1937435 4360751 := bstep (se 1 (by rfl) ⟨3270563, by rfl⟩ : syracuseStep 4360751 = 6541127) B6541127
theorem B2907167 : Blo 1937435 2907167 := bstep (se 1 (by rfl) ⟨2180375, by rfl⟩ : syracuseStep 2907167 = 4360751) B4360751
theorem B1938111 : Blo 1937435 1938111 := bstep (se 1 (by rfl) ⟨1453583, by rfl⟩ : syracuseStep 1938111 = 2907167) B2907167
theorem B2907173 : Blo 1937435 2907173 := bbase (se 4 (by rfl) ⟨272547, by rfl⟩ : syracuseStep 2907173 = 545095) (by norm_num)
theorem B1938115 : Blo 1937435 1938115 := bstep (se 1 (by rfl) ⟨1453586, by rfl⟩ : syracuseStep 1938115 = 2907173) B2907173
theorem B2452933 : Blo 1937435 2452933 := bbase (se 4 (by rfl) ⟨229962, by rfl⟩ : syracuseStep 2452933 = 459925) (by norm_num)
theorem B3270577 : Blo 1937435 3270577 := bstep (se 2 (by rfl) ⟨1226466, by rfl⟩ : syracuseStep 3270577 = 2452933) B2452933
theorem B4360769 : Blo 1937435 4360769 := bstep (se 2 (by rfl) ⟨1635288, by rfl⟩ : syracuseStep 4360769 = 3270577) B3270577
theorem B2907179 : Blo 1937435 2907179 := bstep (se 1 (by rfl) ⟨2180384, by rfl⟩ : syracuseStep 2907179 = 4360769) B4360769
theorem B1938119 : Blo 1937435 1938119 := bstep (se 1 (by rfl) ⟨1453589, by rfl⟩ : syracuseStep 1938119 = 2907179) B2907179
theorem B2180389 : Blo 1937435 2180389 := bbase (se 4 (by rfl) ⟨204411, by rfl⟩ : syracuseStep 2180389 = 408823) (by norm_num)
theorem B2907185 : Blo 1937435 2907185 := bstep (se 2 (by rfl) ⟨1090194, by rfl⟩ : syracuseStep 2907185 = 2180389) B2180389
theorem B1938123 : Blo 1937435 1938123 := bstep (se 1 (by rfl) ⟨1453592, by rfl⟩ : syracuseStep 1938123 = 2907185) B2907185
theorem B11188853 : Blo 1937435 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B7459235 : Blo 1937435 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4972823 : Blo 1937435 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B3315215 : Blo 1937435 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B8840573 : Blo 1937435 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B5893715 : Blo 1937435 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3929143 : Blo 1937435 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B5238857 : Blo 1937435 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B3492571 : Blo 1937435 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B4656761 : Blo 1937435 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B3104507 : Blo 1937435 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B8278685 : Blo 1937435 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B5519123 : Blo 1937435 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B3679415 : Blo 1937435 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B2452943 : Blo 1937435 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B6541181 : Blo 1937435 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B4360787 : Blo 1937435 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B2907191 : Blo 1937435 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B1938127 : Blo 1937435 1938127 := bstep (se 1 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 1938127 = 2907191) B2907191
theorem B2907197 : Blo 1937435 2907197 := bbase (se 3 (by rfl) ⟨545099, by rfl⟩ : syracuseStep 2907197 = 1090199) (by norm_num)
theorem B1938131 : Blo 1937435 1938131 := bstep (se 1 (by rfl) ⟨1453598, by rfl⟩ : syracuseStep 1938131 = 2907197) B2907197
theorem B4360805 : Blo 1937435 4360805 := bbase (se 4 (by rfl) ⟨408825, by rfl⟩ : syracuseStep 4360805 = 817651) (by norm_num)
theorem B2907203 : Blo 1937435 2907203 := bstep (se 1 (by rfl) ⟨2180402, by rfl⟩ : syracuseStep 2907203 = 4360805) B4360805
theorem B1938135 : Blo 1937435 1938135 := bstep (se 1 (by rfl) ⟨1453601, by rfl⟩ : syracuseStep 1938135 = 2907203) B2907203
theorem B4905917 : Blo 1937435 4905917 := bbase (se 3 (by rfl) ⟨919859, by rfl⟩ : syracuseStep 4905917 = 1839719) (by norm_num)
theorem B3270611 : Blo 1937435 3270611 := bstep (se 1 (by rfl) ⟨2452958, by rfl⟩ : syracuseStep 3270611 = 4905917) B4905917
theorem B2180407 : Blo 1937435 2180407 := bstep (se 1 (by rfl) ⟨1635305, by rfl⟩ : syracuseStep 2180407 = 3270611) B3270611
theorem B2907209 : Blo 1937435 2907209 := bstep (se 2 (by rfl) ⟨1090203, by rfl⟩ : syracuseStep 2907209 = 2180407) B2180407
theorem B1938139 : Blo 1937435 1938139 := bstep (se 1 (by rfl) ⟨1453604, by rfl⟩ : syracuseStep 1938139 = 2907209) B2907209
theorem B3679445 : Blo 1937435 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B9811853 : Blo 1937435 9811853 := bstep (se 3 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 9811853 = 3679445) B3679445
theorem B6541235 : Blo 1937435 6541235 := bstep (se 1 (by rfl) ⟨4905926, by rfl⟩ : syracuseStep 6541235 = 9811853) B9811853
theorem B4360823 : Blo 1937435 4360823 := bstep (se 1 (by rfl) ⟨3270617, by rfl⟩ : syracuseStep 4360823 = 6541235) B6541235
theorem B2907215 : Blo 1937435 2907215 := bstep (se 1 (by rfl) ⟨2180411, by rfl⟩ : syracuseStep 2907215 = 4360823) B4360823
theorem B1938143 : Blo 1937435 1938143 := bstep (se 1 (by rfl) ⟨1453607, by rfl⟩ : syracuseStep 1938143 = 2907215) B2907215
theorem B2907221 : Blo 1937435 2907221 := bbase (se 8 (by rfl) ⟨17034, by rfl⟩ : syracuseStep 2907221 = 34069) (by norm_num)
theorem B1938147 : Blo 1937435 1938147 := bstep (se 1 (by rfl) ⟨1453610, by rfl⟩ : syracuseStep 1938147 = 2907221) B2907221
theorem B2328409 : Blo 1937435 2328409 := bbase (se 2 (by rfl) ⟨873153, by rfl⟩ : syracuseStep 2328409 = 1746307) (by norm_num)
theorem B12418181 : Blo 1937435 12418181 := bstep (se 4 (by rfl) ⟨1164204, by rfl⟩ : syracuseStep 12418181 = 2328409) B2328409
theorem B8278787 : Blo 1937435 8278787 := bstep (se 1 (by rfl) ⟨6209090, by rfl⟩ : syracuseStep 8278787 = 12418181) B12418181
theorem B5519191 : Blo 1937435 5519191 := bstep (se 1 (by rfl) ⟨4139393, by rfl⟩ : syracuseStep 5519191 = 8278787) B8278787
theorem B7358921 : Blo 1937435 7358921 := bstep (se 2 (by rfl) ⟨2759595, by rfl⟩ : syracuseStep 7358921 = 5519191) B5519191
theorem B4905947 : Blo 1937435 4905947 := bstep (se 1 (by rfl) ⟨3679460, by rfl⟩ : syracuseStep 4905947 = 7358921) B7358921
theorem B3270631 : Blo 1937435 3270631 := bstep (se 1 (by rfl) ⟨2452973, by rfl⟩ : syracuseStep 3270631 = 4905947) B4905947
theorem B4360841 : Blo 1937435 4360841 := bstep (se 2 (by rfl) ⟨1635315, by rfl⟩ : syracuseStep 4360841 = 3270631) B3270631
theorem B2907227 : Blo 1937435 2907227 := bstep (se 1 (by rfl) ⟨2180420, by rfl⟩ : syracuseStep 2907227 = 4360841) B4360841
theorem B1938151 : Blo 1937435 1938151 := bstep (se 1 (by rfl) ⟨1453613, by rfl⟩ : syracuseStep 1938151 = 2907227) B2907227
theorem B2180425 : Blo 1937435 2180425 := bbase (se 2 (by rfl) ⟨817659, by rfl⟩ : syracuseStep 2180425 = 1635319) (by norm_num)
theorem B2907233 : Blo 1937435 2907233 := bstep (se 2 (by rfl) ⟨1090212, by rfl⟩ : syracuseStep 2907233 = 2180425) B2180425
theorem B1938155 : Blo 1937435 1938155 := bstep (se 1 (by rfl) ⟨1453616, by rfl⟩ : syracuseStep 1938155 = 2907233) B2907233
theorem B17681429 : Blo 1937435 17681429 := bbase (se 6 (by rfl) ⟨414408, by rfl⟩ : syracuseStep 17681429 = 828817) (by norm_num)
theorem B11787619 : Blo 1937435 11787619 := bstep (se 1 (by rfl) ⟨8840714, by rfl⟩ : syracuseStep 11787619 = 17681429) B17681429
theorem B15716825 : Blo 1937435 15716825 := bstep (se 2 (by rfl) ⟨5893809, by rfl⟩ : syracuseStep 15716825 = 11787619) B11787619
theorem B10477883 : Blo 1937435 10477883 := bstep (se 1 (by rfl) ⟨7858412, by rfl⟩ : syracuseStep 10477883 = 15716825) B15716825
theorem B27941021 : Blo 1937435 27941021 := bstep (se 3 (by rfl) ⟨5238941, by rfl⟩ : syracuseStep 27941021 = 10477883) B10477883
theorem B18627347 : Blo 1937435 18627347 := bstep (se 1 (by rfl) ⟨13970510, by rfl⟩ : syracuseStep 18627347 = 27941021) B27941021
theorem B12418231 : Blo 1937435 12418231 := bstep (se 1 (by rfl) ⟨9313673, by rfl⟩ : syracuseStep 12418231 = 18627347) B18627347
theorem B16557641 : Blo 1937435 16557641 := bstep (se 2 (by rfl) ⟨6209115, by rfl⟩ : syracuseStep 16557641 = 12418231) B12418231
theorem B11038427 : Blo 1937435 11038427 := bstep (se 1 (by rfl) ⟨8278820, by rfl⟩ : syracuseStep 11038427 = 16557641) B16557641
theorem B7358951 : Blo 1937435 7358951 := bstep (se 1 (by rfl) ⟨5519213, by rfl⟩ : syracuseStep 7358951 = 11038427) B11038427
theorem B4905967 : Blo 1937435 4905967 := bstep (se 1 (by rfl) ⟨3679475, by rfl⟩ : syracuseStep 4905967 = 7358951) B7358951
theorem B6541289 : Blo 1937435 6541289 := bstep (se 2 (by rfl) ⟨2452983, by rfl⟩ : syracuseStep 6541289 = 4905967) B4905967
theorem B4360859 : Blo 1937435 4360859 := bstep (se 1 (by rfl) ⟨3270644, by rfl⟩ : syracuseStep 4360859 = 6541289) B6541289
theorem B2907239 : Blo 1937435 2907239 := bstep (se 1 (by rfl) ⟨2180429, by rfl⟩ : syracuseStep 2907239 = 4360859) B4360859
theorem B1938159 : Blo 1937435 1938159 := bstep (se 1 (by rfl) ⟨1453619, by rfl⟩ : syracuseStep 1938159 = 2907239) B2907239
theorem B2907245 : Blo 1937435 2907245 := bbase (se 3 (by rfl) ⟨545108, by rfl⟩ : syracuseStep 2907245 = 1090217) (by norm_num)
theorem B1938163 : Blo 1937435 1938163 := bstep (se 1 (by rfl) ⟨1453622, by rfl⟩ : syracuseStep 1938163 = 2907245) B2907245
theorem B4360877 : Blo 1937435 4360877 := bbase (se 3 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 4360877 = 1635329) (by norm_num)
theorem B2907251 : Blo 1937435 2907251 := bstep (se 1 (by rfl) ⟨2180438, by rfl⟩ : syracuseStep 2907251 = 4360877) B4360877
theorem B1938167 : Blo 1937435 1938167 := bstep (se 1 (by rfl) ⟨1453625, by rfl⟩ : syracuseStep 1938167 = 2907251) B2907251
theorem B4139437 : Blo 1937435 4139437 := bbase (se 3 (by rfl) ⟨776144, by rfl⟩ : syracuseStep 4139437 = 1552289) (by norm_num)
theorem B5519249 : Blo 1937435 5519249 := bstep (se 2 (by rfl) ⟨2069718, by rfl⟩ : syracuseStep 5519249 = 4139437) B4139437
theorem B3679499 : Blo 1937435 3679499 := bstep (se 1 (by rfl) ⟨2759624, by rfl⟩ : syracuseStep 3679499 = 5519249) B5519249
theorem B2452999 : Blo 1937435 2452999 := bstep (se 1 (by rfl) ⟨1839749, by rfl⟩ : syracuseStep 2452999 = 3679499) B3679499
theorem B3270665 : Blo 1937435 3270665 := bstep (se 2 (by rfl) ⟨1226499, by rfl⟩ : syracuseStep 3270665 = 2452999) B2452999
theorem B2180443 : Blo 1937435 2180443 := bstep (se 1 (by rfl) ⟨1635332, by rfl⟩ : syracuseStep 2180443 = 3270665) B3270665
theorem B2907257 : Blo 1937435 2907257 := bstep (se 2 (by rfl) ⟨1090221, by rfl⟩ : syracuseStep 2907257 = 2180443) B2180443
theorem B1938171 : Blo 1937435 1938171 := bstep (se 1 (by rfl) ⟨1453628, by rfl⟩ : syracuseStep 1938171 = 2907257) B2907257
theorem B3146941 : Blo 1937435 3146941 := bbase (se 3 (by rfl) ⟨590051, by rfl⟩ : syracuseStep 3146941 = 1180103) (by norm_num)
theorem B16783685 : Blo 1937435 16783685 := bstep (se 4 (by rfl) ⟨1573470, by rfl⟩ : syracuseStep 16783685 = 3146941) B3146941
theorem B11189123 : Blo 1937435 11189123 := bstep (se 1 (by rfl) ⟨8391842, by rfl⟩ : syracuseStep 11189123 = 16783685) B16783685
theorem B7459415 : Blo 1937435 7459415 := bstep (se 1 (by rfl) ⟨5594561, by rfl⟩ : syracuseStep 7459415 = 11189123) B11189123
theorem B4972943 : Blo 1937435 4972943 := bstep (se 1 (by rfl) ⟨3729707, by rfl⟩ : syracuseStep 4972943 = 7459415) B7459415
theorem B3315295 : Blo 1937435 3315295 := bstep (se 1 (by rfl) ⟨2486471, by rfl⟩ : syracuseStep 3315295 = 4972943) B4972943
theorem B17681573 : Blo 1937435 17681573 := bstep (se 4 (by rfl) ⟨1657647, by rfl⟩ : syracuseStep 17681573 = 3315295) B3315295
theorem B11787715 : Blo 1937435 11787715 := bstep (se 1 (by rfl) ⟨8840786, by rfl⟩ : syracuseStep 11787715 = 17681573) B17681573
theorem B15716953 : Blo 1937435 15716953 := bstep (se 2 (by rfl) ⟨5893857, by rfl⟩ : syracuseStep 15716953 = 11787715) B11787715
theorem B20955937 : Blo 1937435 20955937 := bstep (se 2 (by rfl) ⟨7858476, by rfl⟩ : syracuseStep 20955937 = 15716953) B15716953
theorem B27941249 : Blo 1937435 27941249 := bstep (se 2 (by rfl) ⟨10477968, by rfl⟩ : syracuseStep 27941249 = 20955937) B20955937
theorem B18627499 : Blo 1937435 18627499 := bstep (se 1 (by rfl) ⟨13970624, by rfl⟩ : syracuseStep 18627499 = 27941249) B27941249
theorem B24836665 : Blo 1937435 24836665 := bstep (se 2 (by rfl) ⟨9313749, by rfl⟩ : syracuseStep 24836665 = 18627499) B18627499
theorem B33115553 : Blo 1937435 33115553 := bstep (se 2 (by rfl) ⟨12418332, by rfl⟩ : syracuseStep 33115553 = 24836665) B24836665
theorem B22077035 : Blo 1937435 22077035 := bstep (se 1 (by rfl) ⟨16557776, by rfl⟩ : syracuseStep 22077035 = 33115553) B33115553
theorem B14718023 : Blo 1937435 14718023 := bstep (se 1 (by rfl) ⟨11038517, by rfl⟩ : syracuseStep 14718023 = 22077035) B22077035
theorem B9812015 : Blo 1937435 9812015 := bstep (se 1 (by rfl) ⟨7359011, by rfl⟩ : syracuseStep 9812015 = 14718023) B14718023
theorem B6541343 : Blo 1937435 6541343 := bstep (se 1 (by rfl) ⟨4906007, by rfl⟩ : syracuseStep 6541343 = 9812015) B9812015
theorem B4360895 : Blo 1937435 4360895 := bstep (se 1 (by rfl) ⟨3270671, by rfl⟩ : syracuseStep 4360895 = 6541343) B6541343
theorem B2907263 : Blo 1937435 2907263 := bstep (se 1 (by rfl) ⟨2180447, by rfl⟩ : syracuseStep 2907263 = 4360895) B4360895
theorem B1938175 : Blo 1937435 1938175 := bstep (se 1 (by rfl) ⟨1453631, by rfl⟩ : syracuseStep 1938175 = 2907263) B2907263
theorem B2907269 : Blo 1937435 2907269 := bbase (se 4 (by rfl) ⟨272556, by rfl⟩ : syracuseStep 2907269 = 545113) (by norm_num)
theorem B1938179 : Blo 1937435 1938179 := bstep (se 1 (by rfl) ⟨1453634, by rfl⟩ : syracuseStep 1938179 = 2907269) B2907269
theorem B3270685 : Blo 1937435 3270685 := bbase (se 3 (by rfl) ⟨613253, by rfl⟩ : syracuseStep 3270685 = 1226507) (by norm_num)
theorem B4360913 : Blo 1937435 4360913 := bstep (se 2 (by rfl) ⟨1635342, by rfl⟩ : syracuseStep 4360913 = 3270685) B3270685
theorem B2907275 : Blo 1937435 2907275 := bstep (se 1 (by rfl) ⟨2180456, by rfl⟩ : syracuseStep 2907275 = 4360913) B4360913
theorem B1938183 : Blo 1937435 1938183 := bstep (se 1 (by rfl) ⟨1453637, by rfl⟩ : syracuseStep 1938183 = 2907275) B2907275
theorem B2180461 : Blo 1937435 2180461 := bbase (se 3 (by rfl) ⟨408836, by rfl⟩ : syracuseStep 2180461 = 817673) (by norm_num)
theorem B2907281 : Blo 1937435 2907281 := bstep (se 2 (by rfl) ⟨1090230, by rfl⟩ : syracuseStep 2907281 = 2180461) B2180461
theorem B1938187 : Blo 1937435 1938187 := bstep (se 1 (by rfl) ⟨1453640, by rfl⟩ : syracuseStep 1938187 = 2907281) B2907281
theorem B6541397 : Blo 1937435 6541397 := bbase (se 8 (by rfl) ⟨38328, by rfl⟩ : syracuseStep 6541397 = 76657) (by norm_num)
theorem B4360931 : Blo 1937435 4360931 := bstep (se 1 (by rfl) ⟨3270698, by rfl⟩ : syracuseStep 4360931 = 6541397) B6541397
theorem B2907287 : Blo 1937435 2907287 := bstep (se 1 (by rfl) ⟨2180465, by rfl⟩ : syracuseStep 2907287 = 4360931) B4360931
theorem B1938191 : Blo 1937435 1938191 := bstep (se 1 (by rfl) ⟨1453643, by rfl⟩ : syracuseStep 1938191 = 2907287) B2907287
theorem B2907293 : Blo 1937435 2907293 := bbase (se 3 (by rfl) ⟨545117, by rfl⟩ : syracuseStep 2907293 = 1090235) (by norm_num)
theorem B1938195 : Blo 1937435 1938195 := bstep (se 1 (by rfl) ⟨1453646, by rfl⟩ : syracuseStep 1938195 = 2907293) B2907293
theorem B4360949 : Blo 1937435 4360949 := bbase (se 5 (by rfl) ⟨204419, by rfl⟩ : syracuseStep 4360949 = 408839) (by norm_num)
theorem B2907299 : Blo 1937435 2907299 := bstep (se 1 (by rfl) ⟨2180474, by rfl⟩ : syracuseStep 2907299 = 4360949) B4360949
theorem B1938199 : Blo 1937435 1938199 := bstep (se 1 (by rfl) ⟨1453649, by rfl⟩ : syracuseStep 1938199 = 2907299) B2907299
theorem B8840917 : Blo 1937435 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B11787889 : Blo 1937435 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B15717185 : Blo 1937435 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B10478123 : Blo 1937435 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B6985415 : Blo 1937435 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B4656943 : Blo 1937435 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B24837029 : Blo 1937435 24837029 := bstep (se 4 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 24837029 = 4656943) B4656943
theorem B16558019 : Blo 1937435 16558019 := bstep (se 1 (by rfl) ⟨12418514, by rfl⟩ : syracuseStep 16558019 = 24837029) B24837029
theorem B11038679 : Blo 1937435 11038679 := bstep (se 1 (by rfl) ⟨8279009, by rfl⟩ : syracuseStep 11038679 = 16558019) B16558019
theorem B7359119 : Blo 1937435 7359119 := bstep (se 1 (by rfl) ⟨5519339, by rfl⟩ : syracuseStep 7359119 = 11038679) B11038679
theorem B4906079 : Blo 1937435 4906079 := bstep (se 1 (by rfl) ⟨3679559, by rfl⟩ : syracuseStep 4906079 = 7359119) B7359119
theorem B3270719 : Blo 1937435 3270719 := bstep (se 1 (by rfl) ⟨2453039, by rfl⟩ : syracuseStep 3270719 = 4906079) B4906079
theorem B2180479 : Blo 1937435 2180479 := bstep (se 1 (by rfl) ⟨1635359, by rfl⟩ : syracuseStep 2180479 = 3270719) B3270719
theorem B2907305 : Blo 1937435 2907305 := bstep (se 2 (by rfl) ⟨1090239, by rfl⟩ : syracuseStep 2907305 = 2180479) B2180479
theorem B1938203 : Blo 1937435 1938203 := bstep (se 1 (by rfl) ⟨1453652, by rfl⟩ : syracuseStep 1938203 = 2907305) B2907305
theorem B4420469 : Blo 1937435 4420469 := bbase (se 5 (by rfl) ⟨207209, by rfl⟩ : syracuseStep 4420469 = 414419) (by norm_num)
theorem B2946979 : Blo 1937435 2946979 := bstep (se 1 (by rfl) ⟨2210234, by rfl⟩ : syracuseStep 2946979 = 4420469) B4420469
theorem B3929305 : Blo 1937435 3929305 := bstep (se 2 (by rfl) ⟨1473489, by rfl⟩ : syracuseStep 3929305 = 2946979) B2946979
theorem B5239073 : Blo 1937435 5239073 := bstep (se 2 (by rfl) ⟨1964652, by rfl⟩ : syracuseStep 5239073 = 3929305) B3929305
theorem B3492715 : Blo 1937435 3492715 := bstep (se 1 (by rfl) ⟨2619536, by rfl⟩ : syracuseStep 3492715 = 5239073) B5239073
theorem B4656953 : Blo 1937435 4656953 := bstep (se 2 (by rfl) ⟨1746357, by rfl⟩ : syracuseStep 4656953 = 3492715) B3492715
theorem B3104635 : Blo 1937435 3104635 := bstep (se 1 (by rfl) ⟨2328476, by rfl⟩ : syracuseStep 3104635 = 4656953) B4656953
theorem B4139513 : Blo 1937435 4139513 := bstep (se 2 (by rfl) ⟨1552317, by rfl⟩ : syracuseStep 4139513 = 3104635) B3104635
theorem B2759675 : Blo 1937435 2759675 := bstep (se 1 (by rfl) ⟨2069756, by rfl⟩ : syracuseStep 2759675 = 4139513) B4139513
theorem B7359133 : Blo 1937435 7359133 := bstep (se 3 (by rfl) ⟨1379837, by rfl⟩ : syracuseStep 7359133 = 2759675) B2759675
theorem B9812177 : Blo 1937435 9812177 := bstep (se 2 (by rfl) ⟨3679566, by rfl⟩ : syracuseStep 9812177 = 7359133) B7359133
theorem B6541451 : Blo 1937435 6541451 := bstep (se 1 (by rfl) ⟨4906088, by rfl⟩ : syracuseStep 6541451 = 9812177) B9812177
theorem B4360967 : Blo 1937435 4360967 := bstep (se 1 (by rfl) ⟨3270725, by rfl⟩ : syracuseStep 4360967 = 6541451) B6541451
theorem B2907311 : Blo 1937435 2907311 := bstep (se 1 (by rfl) ⟨2180483, by rfl⟩ : syracuseStep 2907311 = 4360967) B4360967
theorem B1938207 : Blo 1937435 1938207 := bstep (se 1 (by rfl) ⟨1453655, by rfl⟩ : syracuseStep 1938207 = 2907311) B2907311
theorem B2907317 : Blo 1937435 2907317 := bbase (se 5 (by rfl) ⟨136280, by rfl⟩ : syracuseStep 2907317 = 272561) (by norm_num)
theorem B1938211 : Blo 1937435 1938211 := bstep (se 1 (by rfl) ⟨1453658, by rfl⟩ : syracuseStep 1938211 = 2907317) B2907317
theorem B4906109 : Blo 1937435 4906109 := bbase (se 3 (by rfl) ⟨919895, by rfl⟩ : syracuseStep 4906109 = 1839791) (by norm_num)
theorem B3270739 : Blo 1937435 3270739 := bstep (se 1 (by rfl) ⟨2453054, by rfl⟩ : syracuseStep 3270739 = 4906109) B4906109
theorem B4360985 : Blo 1937435 4360985 := bstep (se 2 (by rfl) ⟨1635369, by rfl⟩ : syracuseStep 4360985 = 3270739) B3270739
theorem B2907323 : Blo 1937435 2907323 := bstep (se 1 (by rfl) ⟨2180492, by rfl⟩ : syracuseStep 2907323 = 4360985) B4360985
theorem B1938215 : Blo 1937435 1938215 := bstep (se 1 (by rfl) ⟨1453661, by rfl⟩ : syracuseStep 1938215 = 2907323) B2907323
theorem B2180497 : Blo 1937435 2180497 := bbase (se 2 (by rfl) ⟨817686, by rfl⟩ : syracuseStep 2180497 = 1635373) (by norm_num)
theorem B2907329 : Blo 1937435 2907329 := bstep (se 2 (by rfl) ⟨1090248, by rfl⟩ : syracuseStep 2907329 = 2180497) B2180497
theorem B1938219 : Blo 1937435 1938219 := bstep (se 1 (by rfl) ⟨1453664, by rfl⟩ : syracuseStep 1938219 = 2907329) B2907329
theorem B3679597 : Blo 1937435 3679597 := bbase (se 3 (by rfl) ⟨689924, by rfl⟩ : syracuseStep 3679597 = 1379849) (by norm_num)
theorem B4906129 : Blo 1937435 4906129 := bstep (se 2 (by rfl) ⟨1839798, by rfl⟩ : syracuseStep 4906129 = 3679597) B3679597
theorem B6541505 : Blo 1937435 6541505 := bstep (se 2 (by rfl) ⟨2453064, by rfl⟩ : syracuseStep 6541505 = 4906129) B4906129
theorem B4361003 : Blo 1937435 4361003 := bstep (se 1 (by rfl) ⟨3270752, by rfl⟩ : syracuseStep 4361003 = 6541505) B6541505
theorem B2907335 : Blo 1937435 2907335 := bstep (se 1 (by rfl) ⟨2180501, by rfl⟩ : syracuseStep 2907335 = 4361003) B4361003
theorem B1938223 : Blo 1937435 1938223 := bstep (se 1 (by rfl) ⟨1453667, by rfl⟩ : syracuseStep 1938223 = 2907335) B2907335
theorem B2907341 : Blo 1937435 2907341 := bbase (se 3 (by rfl) ⟨545126, by rfl⟩ : syracuseStep 2907341 = 1090253) (by norm_num)
theorem B1938227 : Blo 1937435 1938227 := bstep (se 1 (by rfl) ⟨1453670, by rfl⟩ : syracuseStep 1938227 = 2907341) B2907341
theorem B4361021 : Blo 1937435 4361021 := bbase (se 3 (by rfl) ⟨817691, by rfl⟩ : syracuseStep 4361021 = 1635383) (by norm_num)
theorem B2907347 : Blo 1937435 2907347 := bstep (se 1 (by rfl) ⟨2180510, by rfl⟩ : syracuseStep 2907347 = 4361021) B4361021
theorem B1938231 : Blo 1937435 1938231 := bstep (se 1 (by rfl) ⟨1453673, by rfl⟩ : syracuseStep 1938231 = 2907347) B2907347
theorem B3270773 : Blo 1937435 3270773 := bbase (se 5 (by rfl) ⟨153317, by rfl⟩ : syracuseStep 3270773 = 306635) (by norm_num)
theorem B2180515 : Blo 1937435 2180515 := bstep (se 1 (by rfl) ⟨1635386, by rfl⟩ : syracuseStep 2180515 = 3270773) B3270773
theorem B2907353 : Blo 1937435 2907353 := bstep (se 2 (by rfl) ⟨1090257, by rfl⟩ : syracuseStep 2907353 = 2180515) B2180515
theorem B1938235 : Blo 1937435 1938235 := bstep (se 1 (by rfl) ⟨1453676, by rfl⟩ : syracuseStep 1938235 = 2907353) B2907353
theorem B4139581 : Blo 1937435 4139581 := bbase (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) (by norm_num)
theorem B5519441 : Blo 1937435 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B14718509 : Blo 1937435 14718509 := bstep (se 3 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 14718509 = 5519441) B5519441
theorem B9812339 : Blo 1937435 9812339 := bstep (se 1 (by rfl) ⟨7359254, by rfl⟩ : syracuseStep 9812339 = 14718509) B14718509
theorem B6541559 : Blo 1937435 6541559 := bstep (se 1 (by rfl) ⟨4906169, by rfl⟩ : syracuseStep 6541559 = 9812339) B9812339
theorem B4361039 : Blo 1937435 4361039 := bstep (se 1 (by rfl) ⟨3270779, by rfl⟩ : syracuseStep 4361039 = 6541559) B6541559
theorem B2907359 : Blo 1937435 2907359 := bstep (se 1 (by rfl) ⟨2180519, by rfl⟩ : syracuseStep 2907359 = 4361039) B4361039
theorem B1938239 : Blo 1937435 1938239 := bstep (se 1 (by rfl) ⟨1453679, by rfl⟩ : syracuseStep 1938239 = 2907359) B2907359
theorem B2907365 : Blo 1937435 2907365 := bbase (se 4 (by rfl) ⟨272565, by rfl⟩ : syracuseStep 2907365 = 545131) (by norm_num)
theorem B1938243 : Blo 1937435 1938243 := bstep (se 1 (by rfl) ⟨1453682, by rfl⟩ : syracuseStep 1938243 = 2907365) B2907365
theorem B1964693 : Blo 1937435 1964693 := bbase (se 6 (by rfl) ⟨46047, by rfl⟩ : syracuseStep 1964693 = 92095) (by norm_num)
theorem B5239181 : Blo 1937435 5239181 := bstep (se 3 (by rfl) ⟨982346, by rfl⟩ : syracuseStep 5239181 = 1964693) B1964693
theorem B13971149 : Blo 1937435 13971149 := bstep (se 3 (by rfl) ⟨2619590, by rfl⟩ : syracuseStep 13971149 = 5239181) B5239181
theorem B9314099 : Blo 1937435 9314099 := bstep (se 1 (by rfl) ⟨6985574, by rfl⟩ : syracuseStep 9314099 = 13971149) B13971149
theorem B6209399 : Blo 1937435 6209399 := bstep (se 1 (by rfl) ⟨4657049, by rfl⟩ : syracuseStep 6209399 = 9314099) B9314099
theorem B4139599 : Blo 1937435 4139599 := bstep (se 1 (by rfl) ⟨3104699, by rfl⟩ : syracuseStep 4139599 = 6209399) B6209399
theorem B5519465 : Blo 1937435 5519465 := bstep (se 2 (by rfl) ⟨2069799, by rfl⟩ : syracuseStep 5519465 = 4139599) B4139599
theorem B3679643 : Blo 1937435 3679643 := bstep (se 1 (by rfl) ⟨2759732, by rfl⟩ : syracuseStep 3679643 = 5519465) B5519465
theorem B2453095 : Blo 1937435 2453095 := bstep (se 1 (by rfl) ⟨1839821, by rfl⟩ : syracuseStep 2453095 = 3679643) B3679643
theorem B3270793 : Blo 1937435 3270793 := bstep (se 2 (by rfl) ⟨1226547, by rfl⟩ : syracuseStep 3270793 = 2453095) B2453095
theorem B4361057 : Blo 1937435 4361057 := bstep (se 2 (by rfl) ⟨1635396, by rfl⟩ : syracuseStep 4361057 = 3270793) B3270793
theorem B2907371 : Blo 1937435 2907371 := bstep (se 1 (by rfl) ⟨2180528, by rfl⟩ : syracuseStep 2907371 = 4361057) B4361057
theorem B1938247 : Blo 1937435 1938247 := bstep (se 1 (by rfl) ⟨1453685, by rfl⟩ : syracuseStep 1938247 = 2907371) B2907371
theorem B2180533 : Blo 1937435 2180533 := bbase (se 5 (by rfl) ⟨102212, by rfl⟩ : syracuseStep 2180533 = 204425) (by norm_num)
theorem B2907377 : Blo 1937435 2907377 := bstep (se 2 (by rfl) ⟨1090266, by rfl⟩ : syracuseStep 2907377 = 2180533) B2180533
theorem B1938251 : Blo 1937435 1938251 := bstep (se 1 (by rfl) ⟨1453688, by rfl⟩ : syracuseStep 1938251 = 2907377) B2907377
theorem B2453105 : Blo 1937435 2453105 := bbase (se 2 (by rfl) ⟨919914, by rfl⟩ : syracuseStep 2453105 = 1839829) (by norm_num)
theorem B6541613 : Blo 1937435 6541613 := bstep (se 3 (by rfl) ⟨1226552, by rfl⟩ : syracuseStep 6541613 = 2453105) B2453105
theorem B4361075 : Blo 1937435 4361075 := bstep (se 1 (by rfl) ⟨3270806, by rfl⟩ : syracuseStep 4361075 = 6541613) B6541613
theorem B2907383 : Blo 1937435 2907383 := bstep (se 1 (by rfl) ⟨2180537, by rfl⟩ : syracuseStep 2907383 = 4361075) B4361075
theorem B1938255 : Blo 1937435 1938255 := bstep (se 1 (by rfl) ⟨1453691, by rfl⟩ : syracuseStep 1938255 = 2907383) B2907383
theorem B2907389 : Blo 1937435 2907389 := bbase (se 3 (by rfl) ⟨545135, by rfl⟩ : syracuseStep 2907389 = 1090271) (by norm_num)
theorem B1938259 : Blo 1937435 1938259 := bstep (se 1 (by rfl) ⟨1453694, by rfl⟩ : syracuseStep 1938259 = 2907389) B2907389
theorem B4361093 : Blo 1937435 4361093 := bbase (se 4 (by rfl) ⟨408852, by rfl⟩ : syracuseStep 4361093 = 817705) (by norm_num)
theorem B2907395 : Blo 1937435 2907395 := bstep (se 1 (by rfl) ⟨2180546, by rfl⟩ : syracuseStep 2907395 = 4361093) B4361093
theorem B1938263 : Blo 1937435 1938263 := bstep (se 1 (by rfl) ⟨1453697, by rfl⟩ : syracuseStep 1938263 = 2907395) B2907395
theorem B2069821 : Blo 1937435 2069821 := bbase (se 3 (by rfl) ⟨388091, by rfl⟩ : syracuseStep 2069821 = 776183) (by norm_num)
theorem B2759761 : Blo 1937435 2759761 := bstep (se 2 (by rfl) ⟨1034910, by rfl⟩ : syracuseStep 2759761 = 2069821) B2069821
theorem B3679681 : Blo 1937435 3679681 := bstep (se 2 (by rfl) ⟨1379880, by rfl⟩ : syracuseStep 3679681 = 2759761) B2759761
theorem B4906241 : Blo 1937435 4906241 := bstep (se 2 (by rfl) ⟨1839840, by rfl⟩ : syracuseStep 4906241 = 3679681) B3679681
theorem B3270827 : Blo 1937435 3270827 := bstep (se 1 (by rfl) ⟨2453120, by rfl⟩ : syracuseStep 3270827 = 4906241) B4906241
theorem B2180551 : Blo 1937435 2180551 := bstep (se 1 (by rfl) ⟨1635413, by rfl⟩ : syracuseStep 2180551 = 3270827) B3270827
theorem B2907401 : Blo 1937435 2907401 := bstep (se 2 (by rfl) ⟨1090275, by rfl⟩ : syracuseStep 2907401 = 2180551) B2180551
theorem B1938267 : Blo 1937435 1938267 := bstep (se 1 (by rfl) ⟨1453700, by rfl⟩ : syracuseStep 1938267 = 2907401) B2907401
theorem B9812501 : Blo 1937435 9812501 := bbase (se 6 (by rfl) ⟨229980, by rfl⟩ : syracuseStep 9812501 = 459961) (by norm_num)
theorem B6541667 : Blo 1937435 6541667 := bstep (se 1 (by rfl) ⟨4906250, by rfl⟩ : syracuseStep 6541667 = 9812501) B9812501
theorem B4361111 : Blo 1937435 4361111 := bstep (se 1 (by rfl) ⟨3270833, by rfl⟩ : syracuseStep 4361111 = 6541667) B6541667
theorem B2907407 : Blo 1937435 2907407 := bstep (se 1 (by rfl) ⟨2180555, by rfl⟩ : syracuseStep 2907407 = 4361111) B4361111
theorem B1938271 : Blo 1937435 1938271 := bstep (se 1 (by rfl) ⟨1453703, by rfl⟩ : syracuseStep 1938271 = 2907407) B2907407
theorem B2907413 : Blo 1937435 2907413 := bbase (se 6 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 2907413 = 136285) (by norm_num)
theorem B1938275 : Blo 1937435 1938275 := bstep (se 1 (by rfl) ⟨1453706, by rfl⟩ : syracuseStep 1938275 = 2907413) B2907413
theorem B18628501 : Blo 1937435 18628501 := bbase (se 6 (by rfl) ⟨436605, by rfl⟩ : syracuseStep 18628501 = 873211) (by norm_num)
theorem B24838001 : Blo 1937435 24838001 := bstep (se 2 (by rfl) ⟨9314250, by rfl⟩ : syracuseStep 24838001 = 18628501) B18628501
theorem B16558667 : Blo 1937435 16558667 := bstep (se 1 (by rfl) ⟨12419000, by rfl⟩ : syracuseStep 16558667 = 24838001) B24838001
theorem B11039111 : Blo 1937435 11039111 := bstep (se 1 (by rfl) ⟨8279333, by rfl⟩ : syracuseStep 11039111 = 16558667) B16558667
theorem B7359407 : Blo 1937435 7359407 := bstep (se 1 (by rfl) ⟨5519555, by rfl⟩ : syracuseStep 7359407 = 11039111) B11039111
theorem B4906271 : Blo 1937435 4906271 := bstep (se 1 (by rfl) ⟨3679703, by rfl⟩ : syracuseStep 4906271 = 7359407) B7359407
theorem B3270847 : Blo 1937435 3270847 := bstep (se 1 (by rfl) ⟨2453135, by rfl⟩ : syracuseStep 3270847 = 4906271) B4906271
theorem B4361129 : Blo 1937435 4361129 := bstep (se 2 (by rfl) ⟨1635423, by rfl⟩ : syracuseStep 4361129 = 3270847) B3270847
theorem B2907419 : Blo 1937435 2907419 := bstep (se 1 (by rfl) ⟨2180564, by rfl⟩ : syracuseStep 2907419 = 4361129) B4361129
theorem B1938279 : Blo 1937435 1938279 := bstep (se 1 (by rfl) ⟨1453709, by rfl⟩ : syracuseStep 1938279 = 2907419) B2907419
theorem B2180569 : Blo 1937435 2180569 := bbase (se 2 (by rfl) ⟨817713, by rfl⟩ : syracuseStep 2180569 = 1635427) (by norm_num)
theorem B2907425 : Blo 1937435 2907425 := bstep (se 2 (by rfl) ⟨1090284, by rfl⟩ : syracuseStep 2907425 = 2180569) B2180569
theorem B1938283 : Blo 1937435 1938283 := bstep (se 1 (by rfl) ⟨1453712, by rfl⟩ : syracuseStep 1938283 = 2907425) B2907425
theorem B2759789 : Blo 1937435 2759789 := bbase (se 3 (by rfl) ⟨517460, by rfl⟩ : syracuseStep 2759789 = 1034921) (by norm_num)
theorem B7359437 : Blo 1937435 7359437 := bstep (se 3 (by rfl) ⟨1379894, by rfl⟩ : syracuseStep 7359437 = 2759789) B2759789
theorem B4906291 : Blo 1937435 4906291 := bstep (se 1 (by rfl) ⟨3679718, by rfl⟩ : syracuseStep 4906291 = 7359437) B7359437
theorem B6541721 : Blo 1937435 6541721 := bstep (se 2 (by rfl) ⟨2453145, by rfl⟩ : syracuseStep 6541721 = 4906291) B4906291
theorem B4361147 : Blo 1937435 4361147 := bstep (se 1 (by rfl) ⟨3270860, by rfl⟩ : syracuseStep 4361147 = 6541721) B6541721
theorem B2907431 : Blo 1937435 2907431 := bstep (se 1 (by rfl) ⟨2180573, by rfl⟩ : syracuseStep 2907431 = 4361147) B4361147
theorem B1938287 : Blo 1937435 1938287 := bstep (se 1 (by rfl) ⟨1453715, by rfl⟩ : syracuseStep 1938287 = 2907431) B2907431
theorem B2907437 : Blo 1937435 2907437 := bbase (se 3 (by rfl) ⟨545144, by rfl⟩ : syracuseStep 2907437 = 1090289) (by norm_num)
theorem B1938291 : Blo 1937435 1938291 := bstep (se 1 (by rfl) ⟨1453718, by rfl⟩ : syracuseStep 1938291 = 2907437) B2907437
theorem B4361165 : Blo 1937435 4361165 := bbase (se 3 (by rfl) ⟨817718, by rfl⟩ : syracuseStep 4361165 = 1635437) (by norm_num)
theorem B2907443 : Blo 1937435 2907443 := bstep (se 1 (by rfl) ⟨2180582, by rfl⟩ : syracuseStep 2907443 = 4361165) B4361165
theorem B1938295 : Blo 1937435 1938295 := bstep (se 1 (by rfl) ⟨1453721, by rfl⟩ : syracuseStep 1938295 = 2907443) B2907443
theorem B2453161 : Blo 1937435 2453161 := bbase (se 2 (by rfl) ⟨919935, by rfl⟩ : syracuseStep 2453161 = 1839871) (by norm_num)
theorem B3270881 : Blo 1937435 3270881 := bstep (se 2 (by rfl) ⟨1226580, by rfl⟩ : syracuseStep 3270881 = 2453161) B2453161
theorem B2180587 : Blo 1937435 2180587 := bstep (se 1 (by rfl) ⟨1635440, by rfl⟩ : syracuseStep 2180587 = 3270881) B3270881
theorem B2907449 : Blo 1937435 2907449 := bstep (se 2 (by rfl) ⟨1090293, by rfl⟩ : syracuseStep 2907449 = 2180587) B2180587
theorem B1938299 : Blo 1937435 1938299 := bstep (se 1 (by rfl) ⟨1453724, by rfl⟩ : syracuseStep 1938299 = 2907449) B2907449
theorem B7858997 : Blo 1937435 7858997 := bbase (se 5 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 7858997 = 736781) (by norm_num)
theorem B5239331 : Blo 1937435 5239331 := bstep (se 1 (by rfl) ⟨3929498, by rfl⟩ : syracuseStep 5239331 = 7858997) B7858997
theorem B3492887 : Blo 1937435 3492887 := bstep (se 1 (by rfl) ⟨2619665, by rfl⟩ : syracuseStep 3492887 = 5239331) B5239331
theorem B9314365 : Blo 1937435 9314365 := bstep (se 3 (by rfl) ⟨1746443, by rfl⟩ : syracuseStep 9314365 = 3492887) B3492887
theorem B12419153 : Blo 1937435 12419153 := bstep (se 2 (by rfl) ⟨4657182, by rfl⟩ : syracuseStep 12419153 = 9314365) B9314365
theorem B8279435 : Blo 1937435 8279435 := bstep (se 1 (by rfl) ⟨6209576, by rfl⟩ : syracuseStep 8279435 = 12419153) B12419153
theorem B22078493 : Blo 1937435 22078493 := bstep (se 3 (by rfl) ⟨4139717, by rfl⟩ : syracuseStep 22078493 = 8279435) B8279435
theorem B14718995 : Blo 1937435 14718995 := bstep (se 1 (by rfl) ⟨11039246, by rfl⟩ : syracuseStep 14718995 = 22078493) B22078493
theorem B9812663 : Blo 1937435 9812663 := bstep (se 1 (by rfl) ⟨7359497, by rfl⟩ : syracuseStep 9812663 = 14718995) B14718995
theorem B6541775 : Blo 1937435 6541775 := bstep (se 1 (by rfl) ⟨4906331, by rfl⟩ : syracuseStep 6541775 = 9812663) B9812663
theorem B4361183 : Blo 1937435 4361183 := bstep (se 1 (by rfl) ⟨3270887, by rfl⟩ : syracuseStep 4361183 = 6541775) B6541775
theorem B2907455 : Blo 1937435 2907455 := bstep (se 1 (by rfl) ⟨2180591, by rfl⟩ : syracuseStep 2907455 = 4361183) B4361183
theorem B1938303 : Blo 1937435 1938303 := bstep (se 1 (by rfl) ⟨1453727, by rfl⟩ : syracuseStep 1938303 = 2907455) B2907455
theorem B2907461 : Blo 1937435 2907461 := bbase (se 4 (by rfl) ⟨272574, by rfl⟩ : syracuseStep 2907461 = 545149) (by norm_num)
theorem B1938307 : Blo 1937435 1938307 := bstep (se 1 (by rfl) ⟨1453730, by rfl⟩ : syracuseStep 1938307 = 2907461) B2907461
theorem B3270901 : Blo 1937435 3270901 := bbase (se 5 (by rfl) ⟨153323, by rfl⟩ : syracuseStep 3270901 = 306647) (by norm_num)
theorem B4361201 : Blo 1937435 4361201 := bstep (se 2 (by rfl) ⟨1635450, by rfl⟩ : syracuseStep 4361201 = 3270901) B3270901
theorem B2907467 : Blo 1937435 2907467 := bstep (se 1 (by rfl) ⟨2180600, by rfl⟩ : syracuseStep 2907467 = 4361201) B4361201
theorem B1938311 : Blo 1937435 1938311 := bstep (se 1 (by rfl) ⟨1453733, by rfl⟩ : syracuseStep 1938311 = 2907467) B2907467
theorem B2180605 : Blo 1937435 2180605 := bbase (se 3 (by rfl) ⟨408863, by rfl⟩ : syracuseStep 2180605 = 817727) (by norm_num)
theorem B2907473 : Blo 1937435 2907473 := bstep (se 2 (by rfl) ⟨1090302, by rfl⟩ : syracuseStep 2907473 = 2180605) B2180605
theorem B1938315 : Blo 1937435 1938315 := bstep (se 1 (by rfl) ⟨1453736, by rfl⟩ : syracuseStep 1938315 = 2907473) B2907473
theorem B6541829 : Blo 1937435 6541829 := bbase (se 4 (by rfl) ⟨613296, by rfl⟩ : syracuseStep 6541829 = 1226593) (by norm_num)
theorem B4361219 : Blo 1937435 4361219 := bstep (se 1 (by rfl) ⟨3270914, by rfl⟩ : syracuseStep 4361219 = 6541829) B6541829
theorem B2907479 : Blo 1937435 2907479 := bstep (se 1 (by rfl) ⟨2180609, by rfl⟩ : syracuseStep 2907479 = 4361219) B4361219
theorem B1938319 : Blo 1937435 1938319 := bstep (se 1 (by rfl) ⟨1453739, by rfl⟩ : syracuseStep 1938319 = 2907479) B2907479
theorem B2907485 : Blo 1937435 2907485 := bbase (se 3 (by rfl) ⟨545153, by rfl⟩ : syracuseStep 2907485 = 1090307) (by norm_num)
theorem B1938323 : Blo 1937435 1938323 := bstep (se 1 (by rfl) ⟨1453742, by rfl⟩ : syracuseStep 1938323 = 2907485) B2907485
theorem B4361237 : Blo 1937435 4361237 := bbase (se 6 (by rfl) ⟨102216, by rfl⟩ : syracuseStep 4361237 = 204433) (by norm_num)
theorem B2907491 : Blo 1937435 2907491 := bstep (se 1 (by rfl) ⟨2180618, by rfl⟩ : syracuseStep 2907491 = 4361237) B4361237
theorem B1938327 : Blo 1937435 1938327 := bstep (se 1 (by rfl) ⟨1453745, by rfl⟩ : syracuseStep 1938327 = 2907491) B2907491
theorem B7359605 : Blo 1937435 7359605 := bbase (se 5 (by rfl) ⟨344981, by rfl⟩ : syracuseStep 7359605 = 689963) (by norm_num)
theorem B4906403 : Blo 1937435 4906403 := bstep (se 1 (by rfl) ⟨3679802, by rfl⟩ : syracuseStep 4906403 = 7359605) B7359605
theorem B3270935 : Blo 1937435 3270935 := bstep (se 1 (by rfl) ⟨2453201, by rfl⟩ : syracuseStep 3270935 = 4906403) B4906403
theorem B2180623 : Blo 1937435 2180623 := bstep (se 1 (by rfl) ⟨1635467, by rfl⟩ : syracuseStep 2180623 = 3270935) B3270935
theorem B2907497 : Blo 1937435 2907497 := bstep (se 2 (by rfl) ⟨1090311, by rfl⟩ : syracuseStep 2907497 = 2180623) B2180623
theorem B1938331 : Blo 1937435 1938331 := bstep (se 1 (by rfl) ⟨1453748, by rfl⟩ : syracuseStep 1938331 = 2907497) B2907497
theorem B2069893 : Blo 1937435 2069893 := bbase (se 4 (by rfl) ⟨194052, by rfl⟩ : syracuseStep 2069893 = 388105) (by norm_num)
theorem B11039429 : Blo 1937435 11039429 := bstep (se 4 (by rfl) ⟨1034946, by rfl⟩ : syracuseStep 11039429 = 2069893) B2069893
theorem B7359619 : Blo 1937435 7359619 := bstep (se 1 (by rfl) ⟨5519714, by rfl⟩ : syracuseStep 7359619 = 11039429) B11039429
theorem B9812825 : Blo 1937435 9812825 := bstep (se 2 (by rfl) ⟨3679809, by rfl⟩ : syracuseStep 9812825 = 7359619) B7359619
theorem B6541883 : Blo 1937435 6541883 := bstep (se 1 (by rfl) ⟨4906412, by rfl⟩ : syracuseStep 6541883 = 9812825) B9812825
theorem B4361255 : Blo 1937435 4361255 := bstep (se 1 (by rfl) ⟨3270941, by rfl⟩ : syracuseStep 4361255 = 6541883) B6541883
theorem B2907503 : Blo 1937435 2907503 := bstep (se 1 (by rfl) ⟨2180627, by rfl⟩ : syracuseStep 2907503 = 4361255) B4361255
theorem B1938335 : Blo 1937435 1938335 := bstep (se 1 (by rfl) ⟨1453751, by rfl⟩ : syracuseStep 1938335 = 2907503) B2907503
theorem B2907509 : Blo 1937435 2907509 := bbase (se 5 (by rfl) ⟨136289, by rfl⟩ : syracuseStep 2907509 = 272579) (by norm_num)
theorem B1938339 : Blo 1937435 1938339 := bstep (se 1 (by rfl) ⟨1453754, by rfl⟩ : syracuseStep 1938339 = 2907509) B2907509
theorem B2759869 : Blo 1937435 2759869 := bbase (se 3 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 2759869 = 1034951) (by norm_num)
theorem B3679825 : Blo 1937435 3679825 := bstep (se 2 (by rfl) ⟨1379934, by rfl⟩ : syracuseStep 3679825 = 2759869) B2759869
theorem B4906433 : Blo 1937435 4906433 := bstep (se 2 (by rfl) ⟨1839912, by rfl⟩ : syracuseStep 4906433 = 3679825) B3679825
theorem B3270955 : Blo 1937435 3270955 := bstep (se 1 (by rfl) ⟨2453216, by rfl⟩ : syracuseStep 3270955 = 4906433) B4906433
theorem B4361273 : Blo 1937435 4361273 := bstep (se 2 (by rfl) ⟨1635477, by rfl⟩ : syracuseStep 4361273 = 3270955) B3270955
theorem B2907515 : Blo 1937435 2907515 := bstep (se 1 (by rfl) ⟨2180636, by rfl⟩ : syracuseStep 2907515 = 4361273) B4361273
theorem B1938343 : Blo 1937435 1938343 := bstep (se 1 (by rfl) ⟨1453757, by rfl⟩ : syracuseStep 1938343 = 2907515) B2907515
theorem B2180641 : Blo 1937435 2180641 := bbase (se 2 (by rfl) ⟨817740, by rfl⟩ : syracuseStep 2180641 = 1635481) (by norm_num)
theorem B2907521 : Blo 1937435 2907521 := bstep (se 2 (by rfl) ⟨1090320, by rfl⟩ : syracuseStep 2907521 = 2180641) B2180641
theorem B1938347 : Blo 1937435 1938347 := bstep (se 1 (by rfl) ⟨1453760, by rfl⟩ : syracuseStep 1938347 = 2907521) B2907521
theorem B4906453 : Blo 1937435 4906453 := bbase (se 7 (by rfl) ⟨57497, by rfl⟩ : syracuseStep 4906453 = 114995) (by norm_num)
theorem B6541937 : Blo 1937435 6541937 := bstep (se 2 (by rfl) ⟨2453226, by rfl⟩ : syracuseStep 6541937 = 4906453) B4906453
theorem B4361291 : Blo 1937435 4361291 := bstep (se 1 (by rfl) ⟨3270968, by rfl⟩ : syracuseStep 4361291 = 6541937) B6541937
theorem B2907527 : Blo 1937435 2907527 := bstep (se 1 (by rfl) ⟨2180645, by rfl⟩ : syracuseStep 2907527 = 4361291) B4361291
theorem B1938351 : Blo 1937435 1938351 := bstep (se 1 (by rfl) ⟨1453763, by rfl⟩ : syracuseStep 1938351 = 2907527) B2907527
theorem B2907533 : Blo 1937435 2907533 := bbase (se 3 (by rfl) ⟨545162, by rfl⟩ : syracuseStep 2907533 = 1090325) (by norm_num)
theorem B1938355 : Blo 1937435 1938355 := bstep (se 1 (by rfl) ⟨1453766, by rfl⟩ : syracuseStep 1938355 = 2907533) B2907533
theorem B4361309 : Blo 1937435 4361309 := bbase (se 3 (by rfl) ⟨817745, by rfl⟩ : syracuseStep 4361309 = 1635491) (by norm_num)
theorem B2907539 : Blo 1937435 2907539 := bstep (se 1 (by rfl) ⟨2180654, by rfl⟩ : syracuseStep 2907539 = 4361309) B4361309
theorem B1938359 : Blo 1937435 1938359 := bstep (se 1 (by rfl) ⟨1453769, by rfl⟩ : syracuseStep 1938359 = 2907539) B2907539
theorem B3270989 : Blo 1937435 3270989 := bbase (se 3 (by rfl) ⟨613310, by rfl⟩ : syracuseStep 3270989 = 1226621) (by norm_num)
theorem B2180659 : Blo 1937435 2180659 := bstep (se 1 (by rfl) ⟨1635494, by rfl⟩ : syracuseStep 2180659 = 3270989) B3270989
theorem B2907545 : Blo 1937435 2907545 := bstep (se 2 (by rfl) ⟨1090329, by rfl⟩ : syracuseStep 2907545 = 2180659) B2180659
theorem B1938363 : Blo 1937435 1938363 := bstep (se 1 (by rfl) ⟨1453772, by rfl⟩ : syracuseStep 1938363 = 2907545) B2907545
theorem B2392645 : Blo 1937435 2392645 := bbase (se 4 (by rfl) ⟨224310, by rfl⟩ : syracuseStep 2392645 = 448621) (by norm_num)
theorem B3190193 : Blo 1937435 3190193 := bstep (se 2 (by rfl) ⟨1196322, by rfl⟩ : syracuseStep 3190193 = 2392645) B2392645
theorem B2126795 : Blo 1937435 2126795 := bstep (se 1 (by rfl) ⟨1595096, by rfl⟩ : syracuseStep 2126795 = 3190193) B3190193
theorem B5671453 : Blo 1937435 5671453 := bstep (se 3 (by rfl) ⟨1063397, by rfl⟩ : syracuseStep 5671453 = 2126795) B2126795
theorem B7561937 : Blo 1937435 7561937 := bstep (se 2 (by rfl) ⟨2835726, by rfl⟩ : syracuseStep 7561937 = 5671453) B5671453
theorem B5041291 : Blo 1937435 5041291 := bstep (se 1 (by rfl) ⟨3780968, by rfl⟩ : syracuseStep 5041291 = 7561937) B7561937
theorem B6721721 : Blo 1937435 6721721 := bstep (se 2 (by rfl) ⟨2520645, by rfl⟩ : syracuseStep 6721721 = 5041291) B5041291
theorem B4481147 : Blo 1937435 4481147 := bstep (se 1 (by rfl) ⟨3360860, by rfl⟩ : syracuseStep 4481147 = 6721721) B6721721
theorem B2987431 : Blo 1937435 2987431 := bstep (se 1 (by rfl) ⟨2240573, by rfl⟩ : syracuseStep 2987431 = 4481147) B4481147
theorem B15932965 : Blo 1937435 15932965 := bstep (se 4 (by rfl) ⟨1493715, by rfl⟩ : syracuseStep 15932965 = 2987431) B2987431
theorem B21243953 : Blo 1937435 21243953 := bstep (se 2 (by rfl) ⟨7966482, by rfl⟩ : syracuseStep 21243953 = 15932965) B15932965
theorem B14162635 : Blo 1937435 14162635 := bstep (se 1 (by rfl) ⟨10621976, by rfl⟩ : syracuseStep 14162635 = 21243953) B21243953
theorem B18883513 : Blo 1937435 18883513 := bstep (se 2 (by rfl) ⟨7081317, by rfl⟩ : syracuseStep 18883513 = 14162635) B14162635
theorem B100712069 : Blo 1937435 100712069 := bstep (se 4 (by rfl) ⟨9441756, by rfl⟩ : syracuseStep 100712069 = 18883513) B18883513
theorem B67141379 : Blo 1937435 67141379 := bstep (se 1 (by rfl) ⟨50356034, by rfl⟩ : syracuseStep 67141379 = 100712069) B100712069
theorem B44760919 : Blo 1937435 44760919 := bstep (se 1 (by rfl) ⟨33570689, by rfl⟩ : syracuseStep 44760919 = 67141379) B67141379
theorem B59681225 : Blo 1937435 59681225 := bstep (se 2 (by rfl) ⟨22380459, by rfl⟩ : syracuseStep 59681225 = 44760919) B44760919
theorem B39787483 : Blo 1937435 39787483 := bstep (se 1 (by rfl) ⟨29840612, by rfl⟩ : syracuseStep 39787483 = 59681225) B59681225
theorem B53049977 : Blo 1937435 53049977 := bstep (se 2 (by rfl) ⟨19893741, by rfl⟩ : syracuseStep 53049977 = 39787483) B39787483
theorem B35366651 : Blo 1937435 35366651 := bstep (se 1 (by rfl) ⟨26524988, by rfl⟩ : syracuseStep 35366651 = 53049977) B53049977
theorem B23577767 : Blo 1937435 23577767 := bstep (se 1 (by rfl) ⟨17683325, by rfl⟩ : syracuseStep 23577767 = 35366651) B35366651
theorem B15718511 : Blo 1937435 15718511 := bstep (se 1 (by rfl) ⟨11788883, by rfl⟩ : syracuseStep 15718511 = 23577767) B23577767
theorem B10479007 : Blo 1937435 10479007 := bstep (se 1 (by rfl) ⟨7859255, by rfl⟩ : syracuseStep 10479007 = 15718511) B15718511
theorem B13972009 : Blo 1937435 13972009 := bstep (se 2 (by rfl) ⟨5239503, by rfl⟩ : syracuseStep 13972009 = 10479007) B10479007
theorem B18629345 : Blo 1937435 18629345 := bstep (se 2 (by rfl) ⟨6986004, by rfl⟩ : syracuseStep 18629345 = 13972009) B13972009
theorem B12419563 : Blo 1937435 12419563 := bstep (se 1 (by rfl) ⟨9314672, by rfl⟩ : syracuseStep 12419563 = 18629345) B18629345
theorem B16559417 : Blo 1937435 16559417 := bstep (se 2 (by rfl) ⟨6209781, by rfl⟩ : syracuseStep 16559417 = 12419563) B12419563
theorem B11039611 : Blo 1937435 11039611 := bstep (se 1 (by rfl) ⟨8279708, by rfl⟩ : syracuseStep 11039611 = 16559417) B16559417
theorem B14719481 : Blo 1937435 14719481 := bstep (se 2 (by rfl) ⟨5519805, by rfl⟩ : syracuseStep 14719481 = 11039611) B11039611
theorem B9812987 : Blo 1937435 9812987 := bstep (se 1 (by rfl) ⟨7359740, by rfl⟩ : syracuseStep 9812987 = 14719481) B14719481
theorem B6541991 : Blo 1937435 6541991 := bstep (se 1 (by rfl) ⟨4906493, by rfl⟩ : syracuseStep 6541991 = 9812987) B9812987
theorem B4361327 : Blo 1937435 4361327 := bstep (se 1 (by rfl) ⟨3270995, by rfl⟩ : syracuseStep 4361327 = 6541991) B6541991
theorem B2907551 : Blo 1937435 2907551 := bstep (se 1 (by rfl) ⟨2180663, by rfl⟩ : syracuseStep 2907551 = 4361327) B4361327
theorem B1938367 : Blo 1937435 1938367 := bstep (se 1 (by rfl) ⟨1453775, by rfl⟩ : syracuseStep 1938367 = 2907551) B2907551
theorem B2907557 : Blo 1937435 2907557 := bbase (se 4 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 2907557 = 545167) (by norm_num)
theorem B1938371 : Blo 1937435 1938371 := bstep (se 1 (by rfl) ⟨1453778, by rfl⟩ : syracuseStep 1938371 = 2907557) B2907557
theorem B2453257 : Blo 1937435 2453257 := bbase (se 2 (by rfl) ⟨919971, by rfl⟩ : syracuseStep 2453257 = 1839943) (by norm_num)
theorem B3271009 : Blo 1937435 3271009 := bstep (se 2 (by rfl) ⟨1226628, by rfl⟩ : syracuseStep 3271009 = 2453257) B2453257
theorem B4361345 : Blo 1937435 4361345 := bstep (se 2 (by rfl) ⟨1635504, by rfl⟩ : syracuseStep 4361345 = 3271009) B3271009
theorem B2907563 : Blo 1937435 2907563 := bstep (se 1 (by rfl) ⟨2180672, by rfl⟩ : syracuseStep 2907563 = 4361345) B4361345
theorem B1938375 : Blo 1937435 1938375 := bstep (se 1 (by rfl) ⟨1453781, by rfl⟩ : syracuseStep 1938375 = 2907563) B2907563
theorem B2180677 : Blo 1937435 2180677 := bbase (se 4 (by rfl) ⟨204438, by rfl⟩ : syracuseStep 2180677 = 408877) (by norm_num)
theorem B2907569 : Blo 1937435 2907569 := bstep (se 2 (by rfl) ⟨1090338, by rfl⟩ : syracuseStep 2907569 = 2180677) B2180677
theorem B1938379 : Blo 1937435 1938379 := bstep (se 1 (by rfl) ⟨1453784, by rfl⟩ : syracuseStep 1938379 = 2907569) B2907569
theorem B3679901 : Blo 1937435 3679901 := bbase (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) (by norm_num)
theorem B2453267 : Blo 1937435 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B6542045 : Blo 1937435 6542045 := bstep (se 3 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 6542045 = 2453267) B2453267
theorem B4361363 : Blo 1937435 4361363 := bstep (se 1 (by rfl) ⟨3271022, by rfl⟩ : syracuseStep 4361363 = 6542045) B6542045
theorem B2907575 : Blo 1937435 2907575 := bstep (se 1 (by rfl) ⟨2180681, by rfl⟩ : syracuseStep 2907575 = 4361363) B4361363
theorem B1938383 : Blo 1937435 1938383 := bstep (se 1 (by rfl) ⟨1453787, by rfl⟩ : syracuseStep 1938383 = 2907575) B2907575
theorem B2907581 : Blo 1937435 2907581 := bbase (se 3 (by rfl) ⟨545171, by rfl⟩ : syracuseStep 2907581 = 1090343) (by norm_num)
theorem B1938387 : Blo 1937435 1938387 := bstep (se 1 (by rfl) ⟨1453790, by rfl⟩ : syracuseStep 1938387 = 2907581) B2907581
theorem B4361381 : Blo 1937435 4361381 := bbase (se 4 (by rfl) ⟨408879, by rfl⟩ : syracuseStep 4361381 = 817759) (by norm_num)
theorem B2907587 : Blo 1937435 2907587 := bstep (se 1 (by rfl) ⟨2180690, by rfl⟩ : syracuseStep 2907587 = 4361381) B4361381
theorem B1938391 : Blo 1937435 1938391 := bstep (se 1 (by rfl) ⟨1453793, by rfl⟩ : syracuseStep 1938391 = 2907587) B2907587
theorem B4906565 : Blo 1937435 4906565 := bbase (se 4 (by rfl) ⟨459990, by rfl⟩ : syracuseStep 4906565 = 919981) (by norm_num)
theorem B3271043 : Blo 1937435 3271043 := bstep (se 1 (by rfl) ⟨2453282, by rfl⟩ : syracuseStep 3271043 = 4906565) B4906565
theorem B2180695 : Blo 1937435 2180695 := bstep (se 1 (by rfl) ⟨1635521, by rfl⟩ : syracuseStep 2180695 = 3271043) B3271043
theorem B2907593 : Blo 1937435 2907593 := bstep (se 2 (by rfl) ⟨1090347, by rfl⟩ : syracuseStep 2907593 = 2180695) B2180695
theorem B1938395 : Blo 1937435 1938395 := bstep (se 1 (by rfl) ⟨1453796, by rfl⟩ : syracuseStep 1938395 = 2907593) B2907593
theorem B3493061 : Blo 1937435 3493061 := bbase (se 4 (by rfl) ⟨327474, by rfl⟩ : syracuseStep 3493061 = 654949) (by norm_num)
theorem B2328707 : Blo 1937435 2328707 := bstep (se 1 (by rfl) ⟨1746530, by rfl⟩ : syracuseStep 2328707 = 3493061) B3493061
theorem B6209885 : Blo 1937435 6209885 := bstep (se 3 (by rfl) ⟨1164353, by rfl⟩ : syracuseStep 6209885 = 2328707) B2328707
theorem B4139923 : Blo 1937435 4139923 := bstep (se 1 (by rfl) ⟨3104942, by rfl⟩ : syracuseStep 4139923 = 6209885) B6209885
theorem B5519897 : Blo 1937435 5519897 := bstep (se 2 (by rfl) ⟨2069961, by rfl⟩ : syracuseStep 5519897 = 4139923) B4139923
theorem B3679931 : Blo 1937435 3679931 := bstep (se 1 (by rfl) ⟨2759948, by rfl⟩ : syracuseStep 3679931 = 5519897) B5519897
theorem B9813149 : Blo 1937435 9813149 := bstep (se 3 (by rfl) ⟨1839965, by rfl⟩ : syracuseStep 9813149 = 3679931) B3679931
theorem B6542099 : Blo 1937435 6542099 := bstep (se 1 (by rfl) ⟨4906574, by rfl⟩ : syracuseStep 6542099 = 9813149) B9813149
theorem B4361399 : Blo 1937435 4361399 := bstep (se 1 (by rfl) ⟨3271049, by rfl⟩ : syracuseStep 4361399 = 6542099) B6542099
theorem B2907599 : Blo 1937435 2907599 := bstep (se 1 (by rfl) ⟨2180699, by rfl⟩ : syracuseStep 2907599 = 4361399) B4361399
theorem B1938399 : Blo 1937435 1938399 := bstep (se 1 (by rfl) ⟨1453799, by rfl⟩ : syracuseStep 1938399 = 2907599) B2907599
theorem B2907605 : Blo 1937435 2907605 := bbase (se 7 (by rfl) ⟨34073, by rfl⟩ : syracuseStep 2907605 = 68147) (by norm_num)
theorem B1938403 : Blo 1937435 1938403 := bstep (se 1 (by rfl) ⟨1453802, by rfl⟩ : syracuseStep 1938403 = 2907605) B2907605
theorem B7359893 : Blo 1937435 7359893 := bbase (se 6 (by rfl) ⟨172497, by rfl⟩ : syracuseStep 7359893 = 344995) (by norm_num)
theorem B4906595 : Blo 1937435 4906595 := bstep (se 1 (by rfl) ⟨3679946, by rfl⟩ : syracuseStep 4906595 = 7359893) B7359893
theorem B3271063 : Blo 1937435 3271063 := bstep (se 1 (by rfl) ⟨2453297, by rfl⟩ : syracuseStep 3271063 = 4906595) B4906595
theorem B4361417 : Blo 1937435 4361417 := bstep (se 2 (by rfl) ⟨1635531, by rfl⟩ : syracuseStep 4361417 = 3271063) B3271063
theorem B2907611 : Blo 1937435 2907611 := bstep (se 1 (by rfl) ⟨2180708, by rfl⟩ : syracuseStep 2907611 = 4361417) B4361417
theorem B1938407 : Blo 1937435 1938407 := bstep (se 1 (by rfl) ⟨1453805, by rfl⟩ : syracuseStep 1938407 = 2907611) B2907611
theorem B2180713 : Blo 1937435 2180713 := bbase (se 2 (by rfl) ⟨817767, by rfl⟩ : syracuseStep 2180713 = 1635535) (by norm_num)
theorem B2907617 : Blo 1937435 2907617 := bstep (se 2 (by rfl) ⟨1090356, by rfl⟩ : syracuseStep 2907617 = 2180713) B2180713
theorem B1938411 : Blo 1937435 1938411 := bstep (se 1 (by rfl) ⟨1453808, by rfl⟩ : syracuseStep 1938411 = 2907617) B2907617
theorem B4139957 : Blo 1937435 4139957 := bbase (se 5 (by rfl) ⟨194060, by rfl⟩ : syracuseStep 4139957 = 388121) (by norm_num)
theorem B11039885 : Blo 1937435 11039885 := bstep (se 3 (by rfl) ⟨2069978, by rfl⟩ : syracuseStep 11039885 = 4139957) B4139957
theorem B7359923 : Blo 1937435 7359923 := bstep (se 1 (by rfl) ⟨5519942, by rfl⟩ : syracuseStep 7359923 = 11039885) B11039885
theorem B4906615 : Blo 1937435 4906615 := bstep (se 1 (by rfl) ⟨3679961, by rfl⟩ : syracuseStep 4906615 = 7359923) B7359923
theorem B6542153 : Blo 1937435 6542153 := bstep (se 2 (by rfl) ⟨2453307, by rfl⟩ : syracuseStep 6542153 = 4906615) B4906615
theorem B4361435 : Blo 1937435 4361435 := bstep (se 1 (by rfl) ⟨3271076, by rfl⟩ : syracuseStep 4361435 = 6542153) B6542153
theorem B2907623 : Blo 1937435 2907623 := bstep (se 1 (by rfl) ⟨2180717, by rfl⟩ : syracuseStep 2907623 = 4361435) B4361435
theorem B1938415 : Blo 1937435 1938415 := bstep (se 1 (by rfl) ⟨1453811, by rfl⟩ : syracuseStep 1938415 = 2907623) B2907623
theorem B2907629 : Blo 1937435 2907629 := bbase (se 3 (by rfl) ⟨545180, by rfl⟩ : syracuseStep 2907629 = 1090361) (by norm_num)
theorem B1938419 : Blo 1937435 1938419 := bstep (se 1 (by rfl) ⟨1453814, by rfl⟩ : syracuseStep 1938419 = 2907629) B2907629
theorem B4361453 : Blo 1937435 4361453 := bbase (se 3 (by rfl) ⟨817772, by rfl⟩ : syracuseStep 4361453 = 1635545) (by norm_num)
theorem B2907635 : Blo 1937435 2907635 := bstep (se 1 (by rfl) ⟨2180726, by rfl⟩ : syracuseStep 2907635 = 4361453) B4361453
theorem B1938423 : Blo 1937435 1938423 := bstep (se 1 (by rfl) ⟨1453817, by rfl⟩ : syracuseStep 1938423 = 2907635) B2907635
theorem B2759989 : Blo 1937435 2759989 := bbase (se 5 (by rfl) ⟨129374, by rfl⟩ : syracuseStep 2759989 = 258749) (by norm_num)
theorem B3679985 : Blo 1937435 3679985 := bstep (se 2 (by rfl) ⟨1379994, by rfl⟩ : syracuseStep 3679985 = 2759989) B2759989
theorem B2453323 : Blo 1937435 2453323 := bstep (se 1 (by rfl) ⟨1839992, by rfl⟩ : syracuseStep 2453323 = 3679985) B3679985
theorem B3271097 : Blo 1937435 3271097 := bstep (se 2 (by rfl) ⟨1226661, by rfl⟩ : syracuseStep 3271097 = 2453323) B2453323
theorem B2180731 : Blo 1937435 2180731 := bstep (se 1 (by rfl) ⟨1635548, by rfl⟩ : syracuseStep 2180731 = 3271097) B3271097
theorem B2907641 : Blo 1937435 2907641 := bstep (se 2 (by rfl) ⟨1090365, by rfl⟩ : syracuseStep 2907641 = 2180731) B2180731
theorem B1938427 : Blo 1937435 1938427 := bstep (se 1 (by rfl) ⟨1453820, by rfl⟩ : syracuseStep 1938427 = 2907641) B2907641
theorem B8392949 : Blo 1937435 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B5595299 : Blo 1937435 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B59683189 : Blo 1937435 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B79577585 : Blo 1937435 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B53051723 : Blo 1937435 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B35367815 : Blo 1937435 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B23578543 : Blo 1937435 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B31438057 : Blo 1937435 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B41917409 : Blo 1937435 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B27944939 : Blo 1937435 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B74519837 : Blo 1937435 74519837 := bstep (se 3 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 74519837 = 27944939) B27944939
theorem B49679891 : Blo 1937435 49679891 := bstep (se 1 (by rfl) ⟨37259918, by rfl⟩ : syracuseStep 49679891 = 74519837) B74519837
theorem B33119927 : Blo 1937435 33119927 := bstep (se 1 (by rfl) ⟨24839945, by rfl⟩ : syracuseStep 33119927 = 49679891) B49679891
theorem B22079951 : Blo 1937435 22079951 := bstep (se 1 (by rfl) ⟨16559963, by rfl⟩ : syracuseStep 22079951 = 33119927) B33119927
theorem B14719967 : Blo 1937435 14719967 := bstep (se 1 (by rfl) ⟨11039975, by rfl⟩ : syracuseStep 14719967 = 22079951) B22079951
theorem B9813311 : Blo 1937435 9813311 := bstep (se 1 (by rfl) ⟨7359983, by rfl⟩ : syracuseStep 9813311 = 14719967) B14719967
theorem B6542207 : Blo 1937435 6542207 := bstep (se 1 (by rfl) ⟨4906655, by rfl⟩ : syracuseStep 6542207 = 9813311) B9813311
theorem B4361471 : Blo 1937435 4361471 := bstep (se 1 (by rfl) ⟨3271103, by rfl⟩ : syracuseStep 4361471 = 6542207) B6542207
theorem B2907647 : Blo 1937435 2907647 := bstep (se 1 (by rfl) ⟨2180735, by rfl⟩ : syracuseStep 2907647 = 4361471) B4361471
theorem B1938431 : Blo 1937435 1938431 := bstep (se 1 (by rfl) ⟨1453823, by rfl⟩ : syracuseStep 1938431 = 2907647) B2907647
theorem B2907653 : Blo 1937435 2907653 := bbase (se 4 (by rfl) ⟨272592, by rfl⟩ : syracuseStep 2907653 = 545185) (by norm_num)
theorem B1938435 : Blo 1937435 1938435 := bstep (se 1 (by rfl) ⟨1453826, by rfl⟩ : syracuseStep 1938435 = 2907653) B2907653
theorem B3271117 : Blo 1937435 3271117 := bbase (se 3 (by rfl) ⟨613334, by rfl⟩ : syracuseStep 3271117 = 1226669) (by norm_num)
theorem B4361489 : Blo 1937435 4361489 := bstep (se 2 (by rfl) ⟨1635558, by rfl⟩ : syracuseStep 4361489 = 3271117) B3271117
theorem B2907659 : Blo 1937435 2907659 := bstep (se 1 (by rfl) ⟨2180744, by rfl⟩ : syracuseStep 2907659 = 4361489) B4361489
theorem B1938439 : Blo 1937435 1938439 := bstep (se 1 (by rfl) ⟨1453829, by rfl⟩ : syracuseStep 1938439 = 2907659) B2907659
theorem B2180749 : Blo 1937435 2180749 := bbase (se 3 (by rfl) ⟨408890, by rfl⟩ : syracuseStep 2180749 = 817781) (by norm_num)
theorem B2907665 : Blo 1937435 2907665 := bstep (se 2 (by rfl) ⟨1090374, by rfl⟩ : syracuseStep 2907665 = 2180749) B2180749
theorem B1938443 : Blo 1937435 1938443 := bstep (se 1 (by rfl) ⟨1453832, by rfl⟩ : syracuseStep 1938443 = 2907665) B2907665
theorem B6542261 : Blo 1937435 6542261 := bbase (se 5 (by rfl) ⟨306668, by rfl⟩ : syracuseStep 6542261 = 613337) (by norm_num)
theorem B4361507 : Blo 1937435 4361507 := bstep (se 1 (by rfl) ⟨3271130, by rfl⟩ : syracuseStep 4361507 = 6542261) B6542261
theorem B2907671 : Blo 1937435 2907671 := bstep (se 1 (by rfl) ⟨2180753, by rfl⟩ : syracuseStep 2907671 = 4361507) B4361507
theorem B1938447 : Blo 1937435 1938447 := bstep (se 1 (by rfl) ⟨1453835, by rfl⟩ : syracuseStep 1938447 = 2907671) B2907671
theorem B2907677 : Blo 1937435 2907677 := bbase (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) (by norm_num)
theorem B1938451 : Blo 1937435 1938451 := bstep (se 1 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 1938451 = 2907677) B2907677
theorem B4361525 : Blo 1937435 4361525 := bbase (se 5 (by rfl) ⟨204446, by rfl⟩ : syracuseStep 4361525 = 408893) (by norm_num)
theorem B2907683 : Blo 1937435 2907683 := bstep (se 1 (by rfl) ⟨2180762, by rfl⟩ : syracuseStep 2907683 = 4361525) B4361525
theorem B1938455 : Blo 1937435 1938455 := bstep (se 1 (by rfl) ⟨1453841, by rfl⟩ : syracuseStep 1938455 = 2907683) B2907683
theorem B8842085 : Blo 1937435 8842085 := bbase (se 4 (by rfl) ⟨828945, by rfl⟩ : syracuseStep 8842085 = 1657891) (by norm_num)
theorem B5894723 : Blo 1937435 5894723 := bstep (se 1 (by rfl) ⟨4421042, by rfl⟩ : syracuseStep 5894723 = 8842085) B8842085
theorem B3929815 : Blo 1937435 3929815 := bstep (se 1 (by rfl) ⟨2947361, by rfl⟩ : syracuseStep 3929815 = 5894723) B5894723
theorem B20959013 : Blo 1937435 20959013 := bstep (se 4 (by rfl) ⟨1964907, by rfl⟩ : syracuseStep 20959013 = 3929815) B3929815
theorem B13972675 : Blo 1937435 13972675 := bstep (se 1 (by rfl) ⟨10479506, by rfl⟩ : syracuseStep 13972675 = 20959013) B20959013
theorem B18630233 : Blo 1937435 18630233 := bstep (se 2 (by rfl) ⟨6986337, by rfl⟩ : syracuseStep 18630233 = 13972675) B13972675
theorem B12420155 : Blo 1937435 12420155 := bstep (se 1 (by rfl) ⟨9315116, by rfl⟩ : syracuseStep 12420155 = 18630233) B18630233
theorem B8280103 : Blo 1937435 8280103 := bstep (se 1 (by rfl) ⟨6210077, by rfl⟩ : syracuseStep 8280103 = 12420155) B12420155
theorem B11040137 : Blo 1937435 11040137 := bstep (se 2 (by rfl) ⟨4140051, by rfl⟩ : syracuseStep 11040137 = 8280103) B8280103
theorem B7360091 : Blo 1937435 7360091 := bstep (se 1 (by rfl) ⟨5520068, by rfl⟩ : syracuseStep 7360091 = 11040137) B11040137
theorem B4906727 : Blo 1937435 4906727 := bstep (se 1 (by rfl) ⟨3680045, by rfl⟩ : syracuseStep 4906727 = 7360091) B7360091
theorem B3271151 : Blo 1937435 3271151 := bstep (se 1 (by rfl) ⟨2453363, by rfl⟩ : syracuseStep 3271151 = 4906727) B4906727
theorem B2180767 : Blo 1937435 2180767 := bstep (se 1 (by rfl) ⟨1635575, by rfl⟩ : syracuseStep 2180767 = 3271151) B3271151
theorem B2907689 : Blo 1937435 2907689 := bstep (se 2 (by rfl) ⟨1090383, by rfl⟩ : syracuseStep 2907689 = 2180767) B2180767
theorem B1938459 : Blo 1937435 1938459 := bstep (se 1 (by rfl) ⟨1453844, by rfl⟩ : syracuseStep 1938459 = 2907689) B2907689
theorem B5311253 : Blo 1937435 5311253 := bbase (se 6 (by rfl) ⟨124482, by rfl⟩ : syracuseStep 5311253 = 248965) (by norm_num)
theorem B3540835 : Blo 1937435 3540835 := bstep (se 1 (by rfl) ⟨2655626, by rfl⟩ : syracuseStep 3540835 = 5311253) B5311253
theorem B4721113 : Blo 1937435 4721113 := bstep (se 2 (by rfl) ⟨1770417, by rfl⟩ : syracuseStep 4721113 = 3540835) B3540835
theorem B6294817 : Blo 1937435 6294817 := bstep (se 2 (by rfl) ⟨2360556, by rfl⟩ : syracuseStep 6294817 = 4721113) B4721113
theorem B33572357 : Blo 1937435 33572357 := bstep (se 4 (by rfl) ⟨3147408, by rfl⟩ : syracuseStep 33572357 = 6294817) B6294817
theorem B22381571 : Blo 1937435 22381571 := bstep (se 1 (by rfl) ⟨16786178, by rfl⟩ : syracuseStep 22381571 = 33572357) B33572357
theorem B14921047 : Blo 1937435 14921047 := bstep (se 1 (by rfl) ⟨11190785, by rfl⟩ : syracuseStep 14921047 = 22381571) B22381571
theorem B19894729 : Blo 1937435 19894729 := bstep (se 2 (by rfl) ⟨7460523, by rfl⟩ : syracuseStep 19894729 = 14921047) B14921047
theorem B26526305 : Blo 1937435 26526305 := bstep (se 2 (by rfl) ⟨9947364, by rfl⟩ : syracuseStep 26526305 = 19894729) B19894729
theorem B17684203 : Blo 1937435 17684203 := bstep (se 1 (by rfl) ⟨13263152, by rfl⟩ : syracuseStep 17684203 = 26526305) B26526305
theorem B23578937 : Blo 1937435 23578937 := bstep (se 2 (by rfl) ⟨8842101, by rfl⟩ : syracuseStep 23578937 = 17684203) B17684203
theorem B15719291 : Blo 1937435 15719291 := bstep (se 1 (by rfl) ⟨11789468, by rfl⟩ : syracuseStep 15719291 = 23578937) B23578937
theorem B10479527 : Blo 1937435 10479527 := bstep (se 1 (by rfl) ⟨7859645, by rfl⟩ : syracuseStep 10479527 = 15719291) B15719291
theorem B6986351 : Blo 1937435 6986351 := bstep (se 1 (by rfl) ⟨5239763, by rfl⟩ : syracuseStep 6986351 = 10479527) B10479527
theorem B18630269 : Blo 1937435 18630269 := bstep (se 3 (by rfl) ⟨3493175, by rfl⟩ : syracuseStep 18630269 = 6986351) B6986351
theorem B12420179 : Blo 1937435 12420179 := bstep (se 1 (by rfl) ⟨9315134, by rfl⟩ : syracuseStep 12420179 = 18630269) B18630269
theorem B8280119 : Blo 1937435 8280119 := bstep (se 1 (by rfl) ⟨6210089, by rfl⟩ : syracuseStep 8280119 = 12420179) B12420179
theorem B5520079 : Blo 1937435 5520079 := bstep (se 1 (by rfl) ⟨4140059, by rfl⟩ : syracuseStep 5520079 = 8280119) B8280119
theorem B7360105 : Blo 1937435 7360105 := bstep (se 2 (by rfl) ⟨2760039, by rfl⟩ : syracuseStep 7360105 = 5520079) B5520079
theorem B9813473 : Blo 1937435 9813473 := bstep (se 2 (by rfl) ⟨3680052, by rfl⟩ : syracuseStep 9813473 = 7360105) B7360105
theorem B6542315 : Blo 1937435 6542315 := bstep (se 1 (by rfl) ⟨4906736, by rfl⟩ : syracuseStep 6542315 = 9813473) B9813473
theorem B4361543 : Blo 1937435 4361543 := bstep (se 1 (by rfl) ⟨3271157, by rfl⟩ : syracuseStep 4361543 = 6542315) B6542315
theorem B2907695 : Blo 1937435 2907695 := bstep (se 1 (by rfl) ⟨2180771, by rfl⟩ : syracuseStep 2907695 = 4361543) B4361543
theorem B1938463 : Blo 1937435 1938463 := bstep (se 1 (by rfl) ⟨1453847, by rfl⟩ : syracuseStep 1938463 = 2907695) B2907695
theorem B2907701 : Blo 1937435 2907701 := bbase (se 5 (by rfl) ⟨136298, by rfl⟩ : syracuseStep 2907701 = 272597) (by norm_num)
theorem B1938467 : Blo 1937435 1938467 := bstep (se 1 (by rfl) ⟨1453850, by rfl⟩ : syracuseStep 1938467 = 2907701) B2907701
theorem B4906757 : Blo 1937435 4906757 := bbase (se 4 (by rfl) ⟨460008, by rfl⟩ : syracuseStep 4906757 = 920017) (by norm_num)
theorem B3271171 : Blo 1937435 3271171 := bstep (se 1 (by rfl) ⟨2453378, by rfl⟩ : syracuseStep 3271171 = 4906757) B4906757
theorem B4361561 : Blo 1937435 4361561 := bstep (se 2 (by rfl) ⟨1635585, by rfl⟩ : syracuseStep 4361561 = 3271171) B3271171
theorem B2907707 : Blo 1937435 2907707 := bstep (se 1 (by rfl) ⟨2180780, by rfl⟩ : syracuseStep 2907707 = 4361561) B4361561
theorem B1938471 : Blo 1937435 1938471 := bstep (se 1 (by rfl) ⟨1453853, by rfl⟩ : syracuseStep 1938471 = 2907707) B2907707
theorem B2180785 : Blo 1937435 2180785 := bbase (se 2 (by rfl) ⟨817794, by rfl⟩ : syracuseStep 2180785 = 1635589) (by norm_num)
theorem B2907713 : Blo 1937435 2907713 := bstep (se 2 (by rfl) ⟨1090392, by rfl⟩ : syracuseStep 2907713 = 2180785) B2180785
theorem B1938475 : Blo 1937435 1938475 := bstep (se 1 (by rfl) ⟨1453856, by rfl⟩ : syracuseStep 1938475 = 2907713) B2907713
theorem B3147437 : Blo 1937435 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B8393165 : Blo 1937435 8393165 := bstep (se 3 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 8393165 = 3147437) B3147437
theorem B5595443 : Blo 1937435 5595443 := bstep (se 1 (by rfl) ⟨4196582, by rfl⟩ : syracuseStep 5595443 = 8393165) B8393165
theorem B3730295 : Blo 1937435 3730295 := bstep (se 1 (by rfl) ⟨2797721, by rfl⟩ : syracuseStep 3730295 = 5595443) B5595443
theorem B2486863 : Blo 1937435 2486863 := bstep (se 1 (by rfl) ⟨1865147, by rfl⟩ : syracuseStep 2486863 = 3730295) B3730295
theorem B3315817 : Blo 1937435 3315817 := bstep (se 2 (by rfl) ⟨1243431, by rfl⟩ : syracuseStep 3315817 = 2486863) B2486863
theorem B4421089 : Blo 1937435 4421089 := bstep (se 2 (by rfl) ⟨1657908, by rfl⟩ : syracuseStep 4421089 = 3315817) B3315817
theorem B5894785 : Blo 1937435 5894785 := bstep (se 2 (by rfl) ⟨2210544, by rfl⟩ : syracuseStep 5894785 = 4421089) B4421089
theorem B7859713 : Blo 1937435 7859713 := bstep (se 2 (by rfl) ⟨2947392, by rfl⟩ : syracuseStep 7859713 = 5894785) B5894785
theorem B10479617 : Blo 1937435 10479617 := bstep (se 2 (by rfl) ⟨3929856, by rfl⟩ : syracuseStep 10479617 = 7859713) B7859713
theorem B6986411 : Blo 1937435 6986411 := bstep (se 1 (by rfl) ⟨5239808, by rfl⟩ : syracuseStep 6986411 = 10479617) B10479617
theorem B4657607 : Blo 1937435 4657607 := bstep (se 1 (by rfl) ⟨3493205, by rfl⟩ : syracuseStep 4657607 = 6986411) B6986411
theorem B3105071 : Blo 1937435 3105071 := bstep (se 1 (by rfl) ⟨2328803, by rfl⟩ : syracuseStep 3105071 = 4657607) B4657607
theorem B2070047 : Blo 1937435 2070047 := bstep (se 1 (by rfl) ⟨1552535, by rfl⟩ : syracuseStep 2070047 = 3105071) B3105071
theorem B5520125 : Blo 1937435 5520125 := bstep (se 3 (by rfl) ⟨1035023, by rfl⟩ : syracuseStep 5520125 = 2070047) B2070047
theorem B3680083 : Blo 1937435 3680083 := bstep (se 1 (by rfl) ⟨2760062, by rfl⟩ : syracuseStep 3680083 = 5520125) B5520125
theorem B4906777 : Blo 1937435 4906777 := bstep (se 2 (by rfl) ⟨1840041, by rfl⟩ : syracuseStep 4906777 = 3680083) B3680083
theorem B6542369 : Blo 1937435 6542369 := bstep (se 2 (by rfl) ⟨2453388, by rfl⟩ : syracuseStep 6542369 = 4906777) B4906777
theorem B4361579 : Blo 1937435 4361579 := bstep (se 1 (by rfl) ⟨3271184, by rfl⟩ : syracuseStep 4361579 = 6542369) B6542369
theorem B2907719 : Blo 1937435 2907719 := bstep (se 1 (by rfl) ⟨2180789, by rfl⟩ : syracuseStep 2907719 = 4361579) B4361579
theorem B1938479 : Blo 1937435 1938479 := bstep (se 1 (by rfl) ⟨1453859, by rfl⟩ : syracuseStep 1938479 = 2907719) B2907719
theorem B2907725 : Blo 1937435 2907725 := bbase (se 3 (by rfl) ⟨545198, by rfl⟩ : syracuseStep 2907725 = 1090397) (by norm_num)
theorem B1938483 : Blo 1937435 1938483 := bstep (se 1 (by rfl) ⟨1453862, by rfl⟩ : syracuseStep 1938483 = 2907725) B2907725
theorem B4361597 : Blo 1937435 4361597 := bbase (se 3 (by rfl) ⟨817799, by rfl⟩ : syracuseStep 4361597 = 1635599) (by norm_num)
theorem B2907731 : Blo 1937435 2907731 := bstep (se 1 (by rfl) ⟨2180798, by rfl⟩ : syracuseStep 2907731 = 4361597) B4361597
theorem B1938487 : Blo 1937435 1938487 := bstep (se 1 (by rfl) ⟨1453865, by rfl⟩ : syracuseStep 1938487 = 2907731) B2907731
theorem B3271205 : Blo 1937435 3271205 := bbase (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) (by norm_num)
theorem B2180803 : Blo 1937435 2180803 := bstep (se 1 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 2180803 = 3271205) B3271205
theorem B2907737 : Blo 1937435 2907737 := bstep (se 2 (by rfl) ⟨1090401, by rfl⟩ : syracuseStep 2907737 = 2180803) B2180803
theorem B1938491 : Blo 1937435 1938491 := bstep (se 1 (by rfl) ⟨1453868, by rfl⟩ : syracuseStep 1938491 = 2907737) B2907737
theorem B2760085 : Blo 1937435 2760085 := bbase (se 6 (by rfl) ⟨64689, by rfl⟩ : syracuseStep 2760085 = 129379) (by norm_num)
theorem B14720453 : Blo 1937435 14720453 := bstep (se 4 (by rfl) ⟨1380042, by rfl⟩ : syracuseStep 14720453 = 2760085) B2760085
theorem B9813635 : Blo 1937435 9813635 := bstep (se 1 (by rfl) ⟨7360226, by rfl⟩ : syracuseStep 9813635 = 14720453) B14720453
theorem B6542423 : Blo 1937435 6542423 := bstep (se 1 (by rfl) ⟨4906817, by rfl⟩ : syracuseStep 6542423 = 9813635) B9813635
theorem B4361615 : Blo 1937435 4361615 := bstep (se 1 (by rfl) ⟨3271211, by rfl⟩ : syracuseStep 4361615 = 6542423) B6542423
theorem B2907743 : Blo 1937435 2907743 := bstep (se 1 (by rfl) ⟨2180807, by rfl⟩ : syracuseStep 2907743 = 4361615) B4361615
theorem B1938495 : Blo 1937435 1938495 := bstep (se 1 (by rfl) ⟨1453871, by rfl⟩ : syracuseStep 1938495 = 2907743) B2907743
theorem B2907749 : Blo 1937435 2907749 := bbase (se 4 (by rfl) ⟨272601, by rfl⟩ : syracuseStep 2907749 = 545203) (by norm_num)
theorem B1938499 : Blo 1937435 1938499 := bstep (se 1 (by rfl) ⟨1453874, by rfl⟩ : syracuseStep 1938499 = 2907749) B2907749
theorem B2070073 : Blo 1937435 2070073 := bbase (se 2 (by rfl) ⟨776277, by rfl⟩ : syracuseStep 2070073 = 1552555) (by norm_num)
theorem B2760097 : Blo 1937435 2760097 := bstep (se 2 (by rfl) ⟨1035036, by rfl⟩ : syracuseStep 2760097 = 2070073) B2070073
theorem B3680129 : Blo 1937435 3680129 := bstep (se 2 (by rfl) ⟨1380048, by rfl⟩ : syracuseStep 3680129 = 2760097) B2760097
theorem B2453419 : Blo 1937435 2453419 := bstep (se 1 (by rfl) ⟨1840064, by rfl⟩ : syracuseStep 2453419 = 3680129) B3680129
theorem B3271225 : Blo 1937435 3271225 := bstep (se 2 (by rfl) ⟨1226709, by rfl⟩ : syracuseStep 3271225 = 2453419) B2453419
theorem B4361633 : Blo 1937435 4361633 := bstep (se 2 (by rfl) ⟨1635612, by rfl⟩ : syracuseStep 4361633 = 3271225) B3271225
theorem B2907755 : Blo 1937435 2907755 := bstep (se 1 (by rfl) ⟨2180816, by rfl⟩ : syracuseStep 2907755 = 4361633) B4361633
theorem B1938503 : Blo 1937435 1938503 := bstep (se 1 (by rfl) ⟨1453877, by rfl⟩ : syracuseStep 1938503 = 2907755) B2907755
theorem B2180821 : Blo 1937435 2180821 := bbase (se 7 (by rfl) ⟨25556, by rfl⟩ : syracuseStep 2180821 = 51113) (by norm_num)
theorem B2907761 : Blo 1937435 2907761 := bstep (se 2 (by rfl) ⟨1090410, by rfl⟩ : syracuseStep 2907761 = 2180821) B2180821
theorem B1938507 : Blo 1937435 1938507 := bstep (se 1 (by rfl) ⟨1453880, by rfl⟩ : syracuseStep 1938507 = 2907761) B2907761
theorem B2453429 : Blo 1937435 2453429 := bbase (se 5 (by rfl) ⟨115004, by rfl⟩ : syracuseStep 2453429 = 230009) (by norm_num)
theorem B6542477 : Blo 1937435 6542477 := bstep (se 3 (by rfl) ⟨1226714, by rfl⟩ : syracuseStep 6542477 = 2453429) B2453429
theorem B4361651 : Blo 1937435 4361651 := bstep (se 1 (by rfl) ⟨3271238, by rfl⟩ : syracuseStep 4361651 = 6542477) B6542477
theorem B2907767 : Blo 1937435 2907767 := bstep (se 1 (by rfl) ⟨2180825, by rfl⟩ : syracuseStep 2907767 = 4361651) B4361651
theorem B1938511 : Blo 1937435 1938511 := bstep (se 1 (by rfl) ⟨1453883, by rfl⟩ : syracuseStep 1938511 = 2907767) B2907767
theorem B2907773 : Blo 1937435 2907773 := bbase (se 3 (by rfl) ⟨545207, by rfl⟩ : syracuseStep 2907773 = 1090415) (by norm_num)
theorem B1938515 : Blo 1937435 1938515 := bstep (se 1 (by rfl) ⟨1453886, by rfl⟩ : syracuseStep 1938515 = 2907773) B2907773
theorem B4361669 : Blo 1937435 4361669 := bbase (se 4 (by rfl) ⟨408906, by rfl⟩ : syracuseStep 4361669 = 817813) (by norm_num)
theorem B2907779 : Blo 1937435 2907779 := bstep (se 1 (by rfl) ⟨2180834, by rfl⟩ : syracuseStep 2907779 = 4361669) B4361669
theorem B1938519 : Blo 1937435 1938519 := bstep (se 1 (by rfl) ⟨1453889, by rfl⟩ : syracuseStep 1938519 = 2907779) B2907779
theorem B4421189 : Blo 1937435 4421189 := bbase (se 4 (by rfl) ⟨414486, by rfl⟩ : syracuseStep 4421189 = 828973) (by norm_num)
theorem B11789837 : Blo 1937435 11789837 := bstep (se 3 (by rfl) ⟨2210594, by rfl⟩ : syracuseStep 11789837 = 4421189) B4421189
theorem B7859891 : Blo 1937435 7859891 := bstep (se 1 (by rfl) ⟨5894918, by rfl⟩ : syracuseStep 7859891 = 11789837) B11789837
theorem B5239927 : Blo 1937435 5239927 := bstep (se 1 (by rfl) ⟨3929945, by rfl⟩ : syracuseStep 5239927 = 7859891) B7859891
theorem B6986569 : Blo 1937435 6986569 := bstep (se 2 (by rfl) ⟨2619963, by rfl⟩ : syracuseStep 6986569 = 5239927) B5239927
theorem B9315425 : Blo 1937435 9315425 := bstep (se 2 (by rfl) ⟨3493284, by rfl⟩ : syracuseStep 9315425 = 6986569) B6986569
theorem B6210283 : Blo 1937435 6210283 := bstep (se 1 (by rfl) ⟨4657712, by rfl⟩ : syracuseStep 6210283 = 9315425) B9315425
theorem B8280377 : Blo 1937435 8280377 := bstep (se 2 (by rfl) ⟨3105141, by rfl⟩ : syracuseStep 8280377 = 6210283) B6210283
theorem B5520251 : Blo 1937435 5520251 := bstep (se 1 (by rfl) ⟨4140188, by rfl⟩ : syracuseStep 5520251 = 8280377) B8280377
theorem B3680167 : Blo 1937435 3680167 := bstep (se 1 (by rfl) ⟨2760125, by rfl⟩ : syracuseStep 3680167 = 5520251) B5520251
theorem B4906889 : Blo 1937435 4906889 := bstep (se 2 (by rfl) ⟨1840083, by rfl⟩ : syracuseStep 4906889 = 3680167) B3680167
theorem B3271259 : Blo 1937435 3271259 := bstep (se 1 (by rfl) ⟨2453444, by rfl⟩ : syracuseStep 3271259 = 4906889) B4906889
theorem B2180839 : Blo 1937435 2180839 := bstep (se 1 (by rfl) ⟨1635629, by rfl⟩ : syracuseStep 2180839 = 3271259) B3271259
theorem B2907785 : Blo 1937435 2907785 := bstep (se 2 (by rfl) ⟨1090419, by rfl⟩ : syracuseStep 2907785 = 2180839) B2180839
theorem B1938523 : Blo 1937435 1938523 := bstep (se 1 (by rfl) ⟨1453892, by rfl⟩ : syracuseStep 1938523 = 2907785) B2907785
theorem B9813797 : Blo 1937435 9813797 := bbase (se 4 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 9813797 = 1840087) (by norm_num)
theorem B6542531 : Blo 1937435 6542531 := bstep (se 1 (by rfl) ⟨4906898, by rfl⟩ : syracuseStep 6542531 = 9813797) B9813797
theorem B4361687 : Blo 1937435 4361687 := bstep (se 1 (by rfl) ⟨3271265, by rfl⟩ : syracuseStep 4361687 = 6542531) B6542531
theorem B2907791 : Blo 1937435 2907791 := bstep (se 1 (by rfl) ⟨2180843, by rfl⟩ : syracuseStep 2907791 = 4361687) B4361687
theorem B1938527 : Blo 1937435 1938527 := bstep (se 1 (by rfl) ⟨1453895, by rfl⟩ : syracuseStep 1938527 = 2907791) B2907791
theorem B2907797 : Blo 1937435 2907797 := bbase (se 6 (by rfl) ⟨68151, by rfl⟩ : syracuseStep 2907797 = 136303) (by norm_num)
theorem B1938531 : Blo 1937435 1938531 := bstep (se 1 (by rfl) ⟨1453898, by rfl⟩ : syracuseStep 1938531 = 2907797) B2907797
theorem B2947477 : Blo 1937435 2947477 := bbase (se 6 (by rfl) ⟨69081, by rfl⟩ : syracuseStep 2947477 = 138163) (by norm_num)
theorem B3929969 : Blo 1937435 3929969 := bstep (se 2 (by rfl) ⟨1473738, by rfl⟩ : syracuseStep 3929969 = 2947477) B2947477
theorem B10479917 : Blo 1937435 10479917 := bstep (se 3 (by rfl) ⟨1964984, by rfl⟩ : syracuseStep 10479917 = 3929969) B3929969
theorem B6986611 : Blo 1937435 6986611 := bstep (se 1 (by rfl) ⟨5239958, by rfl⟩ : syracuseStep 6986611 = 10479917) B10479917
theorem B9315481 : Blo 1937435 9315481 := bstep (se 2 (by rfl) ⟨3493305, by rfl⟩ : syracuseStep 9315481 = 6986611) B6986611
theorem B12420641 : Blo 1937435 12420641 := bstep (se 2 (by rfl) ⟨4657740, by rfl⟩ : syracuseStep 12420641 = 9315481) B9315481
theorem B8280427 : Blo 1937435 8280427 := bstep (se 1 (by rfl) ⟨6210320, by rfl⟩ : syracuseStep 8280427 = 12420641) B12420641
theorem B11040569 : Blo 1937435 11040569 := bstep (se 2 (by rfl) ⟨4140213, by rfl⟩ : syracuseStep 11040569 = 8280427) B8280427
theorem B7360379 : Blo 1937435 7360379 := bstep (se 1 (by rfl) ⟨5520284, by rfl⟩ : syracuseStep 7360379 = 11040569) B11040569
theorem B4906919 : Blo 1937435 4906919 := bstep (se 1 (by rfl) ⟨3680189, by rfl⟩ : syracuseStep 4906919 = 7360379) B7360379
theorem B3271279 : Blo 1937435 3271279 := bstep (se 1 (by rfl) ⟨2453459, by rfl⟩ : syracuseStep 3271279 = 4906919) B4906919
theorem B4361705 : Blo 1937435 4361705 := bstep (se 2 (by rfl) ⟨1635639, by rfl⟩ : syracuseStep 4361705 = 3271279) B3271279
theorem B2907803 : Blo 1937435 2907803 := bstep (se 1 (by rfl) ⟨2180852, by rfl⟩ : syracuseStep 2907803 = 4361705) B4361705
theorem B1938535 : Blo 1937435 1938535 := bstep (se 1 (by rfl) ⟨1453901, by rfl⟩ : syracuseStep 1938535 = 2907803) B2907803
theorem B2180857 : Blo 1937435 2180857 := bbase (se 2 (by rfl) ⟨817821, by rfl⟩ : syracuseStep 2180857 = 1635643) (by norm_num)
theorem B2907809 : Blo 1937435 2907809 := bstep (se 2 (by rfl) ⟨1090428, by rfl⟩ : syracuseStep 2907809 = 2180857) B2180857
theorem B1938539 : Blo 1937435 1938539 := bstep (se 1 (by rfl) ⟨1453904, by rfl⟩ : syracuseStep 1938539 = 2907809) B2907809
theorem B3105173 : Blo 1937435 3105173 := bbase (se 6 (by rfl) ⟨72777, by rfl⟩ : syracuseStep 3105173 = 145555) (by norm_num)
theorem B8280461 : Blo 1937435 8280461 := bstep (se 3 (by rfl) ⟨1552586, by rfl⟩ : syracuseStep 8280461 = 3105173) B3105173
theorem B5520307 : Blo 1937435 5520307 := bstep (se 1 (by rfl) ⟨4140230, by rfl⟩ : syracuseStep 5520307 = 8280461) B8280461
theorem B7360409 : Blo 1937435 7360409 := bstep (se 2 (by rfl) ⟨2760153, by rfl⟩ : syracuseStep 7360409 = 5520307) B5520307
theorem B4906939 : Blo 1937435 4906939 := bstep (se 1 (by rfl) ⟨3680204, by rfl⟩ : syracuseStep 4906939 = 7360409) B7360409
theorem B6542585 : Blo 1937435 6542585 := bstep (se 2 (by rfl) ⟨2453469, by rfl⟩ : syracuseStep 6542585 = 4906939) B4906939
theorem B4361723 : Blo 1937435 4361723 := bstep (se 1 (by rfl) ⟨3271292, by rfl⟩ : syracuseStep 4361723 = 6542585) B6542585
theorem B2907815 : Blo 1937435 2907815 := bstep (se 1 (by rfl) ⟨2180861, by rfl⟩ : syracuseStep 2907815 = 4361723) B4361723
theorem B1938543 : Blo 1937435 1938543 := bstep (se 1 (by rfl) ⟨1453907, by rfl⟩ : syracuseStep 1938543 = 2907815) B2907815
theorem B2907821 : Blo 1937435 2907821 := bbase (se 3 (by rfl) ⟨545216, by rfl⟩ : syracuseStep 2907821 = 1090433) (by norm_num)
theorem B1938547 : Blo 1937435 1938547 := bstep (se 1 (by rfl) ⟨1453910, by rfl⟩ : syracuseStep 1938547 = 2907821) B2907821
theorem B4361741 : Blo 1937435 4361741 := bbase (se 3 (by rfl) ⟨817826, by rfl⟩ : syracuseStep 4361741 = 1635653) (by norm_num)
theorem B2907827 : Blo 1937435 2907827 := bstep (se 1 (by rfl) ⟨2180870, by rfl⟩ : syracuseStep 2907827 = 4361741) B4361741
theorem B1938551 : Blo 1937435 1938551 := bstep (se 1 (by rfl) ⟨1453913, by rfl⟩ : syracuseStep 1938551 = 2907827) B2907827
theorem B2453485 : Blo 1937435 2453485 := bbase (se 3 (by rfl) ⟨460028, by rfl⟩ : syracuseStep 2453485 = 920057) (by norm_num)
theorem B3271313 : Blo 1937435 3271313 := bstep (se 2 (by rfl) ⟨1226742, by rfl⟩ : syracuseStep 3271313 = 2453485) B2453485
theorem B2180875 : Blo 1937435 2180875 := bstep (se 1 (by rfl) ⟨1635656, by rfl⟩ : syracuseStep 2180875 = 3271313) B3271313
theorem B2907833 : Blo 1937435 2907833 := bstep (se 2 (by rfl) ⟨1090437, by rfl⟩ : syracuseStep 2907833 = 2180875) B2180875
theorem B1938555 : Blo 1937435 1938555 := bstep (se 1 (by rfl) ⟨1453916, by rfl⟩ : syracuseStep 1938555 = 2907833) B2907833
theorem B2486965 : Blo 1937435 2486965 := bbase (se 5 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 2486965 = 233153) (by norm_num)
theorem B3315953 : Blo 1937435 3315953 := bstep (se 2 (by rfl) ⟨1243482, by rfl⟩ : syracuseStep 3315953 = 2486965) B2486965
theorem B2210635 : Blo 1937435 2210635 := bstep (se 1 (by rfl) ⟨1657976, by rfl⟩ : syracuseStep 2210635 = 3315953) B3315953
theorem B2947513 : Blo 1937435 2947513 := bstep (se 2 (by rfl) ⟨1105317, by rfl⟩ : syracuseStep 2947513 = 2210635) B2210635
theorem B3930017 : Blo 1937435 3930017 := bstep (se 2 (by rfl) ⟨1473756, by rfl⟩ : syracuseStep 3930017 = 2947513) B2947513
theorem B10480045 : Blo 1937435 10480045 := bstep (se 3 (by rfl) ⟨1965008, by rfl⟩ : syracuseStep 10480045 = 3930017) B3930017
theorem B13973393 : Blo 1937435 13973393 := bstep (se 2 (by rfl) ⟨5240022, by rfl⟩ : syracuseStep 13973393 = 10480045) B10480045
theorem B9315595 : Blo 1937435 9315595 := bstep (se 1 (by rfl) ⟨6986696, by rfl⟩ : syracuseStep 9315595 = 13973393) B13973393
theorem B12420793 : Blo 1937435 12420793 := bstep (se 2 (by rfl) ⟨4657797, by rfl⟩ : syracuseStep 12420793 = 9315595) B9315595
theorem B16561057 : Blo 1937435 16561057 := bstep (se 2 (by rfl) ⟨6210396, by rfl⟩ : syracuseStep 16561057 = 12420793) B12420793
theorem B22081409 : Blo 1937435 22081409 := bstep (se 2 (by rfl) ⟨8280528, by rfl⟩ : syracuseStep 22081409 = 16561057) B16561057
theorem B14720939 : Blo 1937435 14720939 := bstep (se 1 (by rfl) ⟨11040704, by rfl⟩ : syracuseStep 14720939 = 22081409) B22081409
theorem B9813959 : Blo 1937435 9813959 := bstep (se 1 (by rfl) ⟨7360469, by rfl⟩ : syracuseStep 9813959 = 14720939) B14720939
theorem B6542639 : Blo 1937435 6542639 := bstep (se 1 (by rfl) ⟨4906979, by rfl⟩ : syracuseStep 6542639 = 9813959) B9813959
theorem B4361759 : Blo 1937435 4361759 := bstep (se 1 (by rfl) ⟨3271319, by rfl⟩ : syracuseStep 4361759 = 6542639) B6542639
theorem B2907839 : Blo 1937435 2907839 := bstep (se 1 (by rfl) ⟨2180879, by rfl⟩ : syracuseStep 2907839 = 4361759) B4361759
theorem B1938559 : Blo 1937435 1938559 := bstep (se 1 (by rfl) ⟨1453919, by rfl⟩ : syracuseStep 1938559 = 2907839) B2907839
theorem B2907845 : Blo 1937435 2907845 := bbase (se 4 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 2907845 = 545221) (by norm_num)
theorem B1938563 : Blo 1937435 1938563 := bstep (se 1 (by rfl) ⟨1453922, by rfl⟩ : syracuseStep 1938563 = 2907845) B2907845
theorem B3271333 : Blo 1937435 3271333 := bbase (se 4 (by rfl) ⟨306687, by rfl⟩ : syracuseStep 3271333 = 613375) (by norm_num)
theorem B4361777 : Blo 1937435 4361777 := bstep (se 2 (by rfl) ⟨1635666, by rfl⟩ : syracuseStep 4361777 = 3271333) B3271333
theorem B2907851 : Blo 1937435 2907851 := bstep (se 1 (by rfl) ⟨2180888, by rfl⟩ : syracuseStep 2907851 = 4361777) B4361777
theorem B1938567 : Blo 1937435 1938567 := bstep (se 1 (by rfl) ⟨1453925, by rfl⟩ : syracuseStep 1938567 = 2907851) B2907851
theorem B2180893 : Blo 1937435 2180893 := bbase (se 3 (by rfl) ⟨408917, by rfl⟩ : syracuseStep 2180893 = 817835) (by norm_num)
theorem B2907857 : Blo 1937435 2907857 := bstep (se 2 (by rfl) ⟨1090446, by rfl⟩ : syracuseStep 2907857 = 2180893) B2180893
theorem B1938571 : Blo 1937435 1938571 := bstep (se 1 (by rfl) ⟨1453928, by rfl⟩ : syracuseStep 1938571 = 2907857) B2907857
theorem B6542693 : Blo 1937435 6542693 := bbase (se 4 (by rfl) ⟨613377, by rfl⟩ : syracuseStep 6542693 = 1226755) (by norm_num)
theorem B4361795 : Blo 1937435 4361795 := bstep (se 1 (by rfl) ⟨3271346, by rfl⟩ : syracuseStep 4361795 = 6542693) B6542693
theorem B2907863 : Blo 1937435 2907863 := bstep (se 1 (by rfl) ⟨2180897, by rfl⟩ : syracuseStep 2907863 = 4361795) B4361795
theorem B1938575 : Blo 1937435 1938575 := bstep (se 1 (by rfl) ⟨1453931, by rfl⟩ : syracuseStep 1938575 = 2907863) B2907863
theorem B2907869 : Blo 1937435 2907869 := bbase (se 3 (by rfl) ⟨545225, by rfl⟩ : syracuseStep 2907869 = 1090451) (by norm_num)
theorem B1938579 : Blo 1937435 1938579 := bstep (se 1 (by rfl) ⟨1453934, by rfl⟩ : syracuseStep 1938579 = 2907869) B2907869
theorem B4361813 : Blo 1937435 4361813 := bbase (se 8 (by rfl) ⟨25557, by rfl⟩ : syracuseStep 4361813 = 51115) (by norm_num)
theorem B2907875 : Blo 1937435 2907875 := bstep (se 1 (by rfl) ⟨2180906, by rfl⟩ : syracuseStep 2907875 = 4361813) B4361813
theorem B1938583 : Blo 1937435 1938583 := bstep (se 1 (by rfl) ⟨1453937, by rfl⟩ : syracuseStep 1938583 = 2907875) B2907875
theorem B4140325 : Blo 1937435 4140325 := bbase (se 4 (by rfl) ⟨388155, by rfl⟩ : syracuseStep 4140325 = 776311) (by norm_num)
theorem B5520433 : Blo 1937435 5520433 := bstep (se 2 (by rfl) ⟨2070162, by rfl⟩ : syracuseStep 5520433 = 4140325) B4140325
theorem B7360577 : Blo 1937435 7360577 := bstep (se 2 (by rfl) ⟨2760216, by rfl⟩ : syracuseStep 7360577 = 5520433) B5520433
theorem B4907051 : Blo 1937435 4907051 := bstep (se 1 (by rfl) ⟨3680288, by rfl⟩ : syracuseStep 4907051 = 7360577) B7360577
theorem B3271367 : Blo 1937435 3271367 := bstep (se 1 (by rfl) ⟨2453525, by rfl⟩ : syracuseStep 3271367 = 4907051) B4907051
theorem B2180911 : Blo 1937435 2180911 := bstep (se 1 (by rfl) ⟨1635683, by rfl⟩ : syracuseStep 2180911 = 3271367) B3271367
theorem B2907881 : Blo 1937435 2907881 := bstep (se 2 (by rfl) ⟨1090455, by rfl⟩ : syracuseStep 2907881 = 2180911) B2180911
theorem B1938587 : Blo 1937435 1938587 := bstep (se 1 (by rfl) ⟨1453940, by rfl⟩ : syracuseStep 1938587 = 2907881) B2907881
theorem B9315749 : Blo 1937435 9315749 := bbase (se 4 (by rfl) ⟨873351, by rfl⟩ : syracuseStep 9315749 = 1746703) (by norm_num)
theorem B24841997 : Blo 1937435 24841997 := bstep (se 3 (by rfl) ⟨4657874, by rfl⟩ : syracuseStep 24841997 = 9315749) B9315749
theorem B16561331 : Blo 1937435 16561331 := bstep (se 1 (by rfl) ⟨12420998, by rfl⟩ : syracuseStep 16561331 = 24841997) B24841997
theorem B11040887 : Blo 1937435 11040887 := bstep (se 1 (by rfl) ⟨8280665, by rfl⟩ : syracuseStep 11040887 = 16561331) B16561331
theorem B7360591 : Blo 1937435 7360591 := bstep (se 1 (by rfl) ⟨5520443, by rfl⟩ : syracuseStep 7360591 = 11040887) B11040887
theorem B9814121 : Blo 1937435 9814121 := bstep (se 2 (by rfl) ⟨3680295, by rfl⟩ : syracuseStep 9814121 = 7360591) B7360591
theorem B6542747 : Blo 1937435 6542747 := bstep (se 1 (by rfl) ⟨4907060, by rfl⟩ : syracuseStep 6542747 = 9814121) B9814121
theorem B4361831 : Blo 1937435 4361831 := bstep (se 1 (by rfl) ⟨3271373, by rfl⟩ : syracuseStep 4361831 = 6542747) B6542747
theorem B2907887 : Blo 1937435 2907887 := bstep (se 1 (by rfl) ⟨2180915, by rfl⟩ : syracuseStep 2907887 = 4361831) B4361831
theorem B1938591 : Blo 1937435 1938591 := bstep (se 1 (by rfl) ⟨1453943, by rfl⟩ : syracuseStep 1938591 = 2907887) B2907887
theorem B2907893 : Blo 1937435 2907893 := bbase (se 5 (by rfl) ⟨136307, by rfl⟩ : syracuseStep 2907893 = 272615) (by norm_num)
theorem B1938595 : Blo 1937435 1938595 := bstep (se 1 (by rfl) ⟨1453946, by rfl⟩ : syracuseStep 1938595 = 2907893) B2907893
theorem B3541085 : Blo 1937435 3541085 := bbase (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) (by norm_num)
theorem B2360723 : Blo 1937435 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B6295261 : Blo 1937435 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B8393681 : Blo 1937435 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B5595787 : Blo 1937435 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B29844197 : Blo 1937435 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B19896131 : Blo 1937435 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B13264087 : Blo 1937435 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B17685449 : Blo 1937435 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B11790299 : Blo 1937435 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B7860199 : Blo 1937435 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B10480265 : Blo 1937435 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B6986843 : Blo 1937435 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B4657895 : Blo 1937435 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B3105263 : Blo 1937435 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B8280701 : Blo 1937435 8280701 := bstep (se 3 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 8280701 = 3105263) B3105263
theorem B5520467 : Blo 1937435 5520467 := bstep (se 1 (by rfl) ⟨4140350, by rfl⟩ : syracuseStep 5520467 = 8280701) B8280701
theorem B3680311 : Blo 1937435 3680311 := bstep (se 1 (by rfl) ⟨2760233, by rfl⟩ : syracuseStep 3680311 = 5520467) B5520467
theorem B4907081 : Blo 1937435 4907081 := bstep (se 2 (by rfl) ⟨1840155, by rfl⟩ : syracuseStep 4907081 = 3680311) B3680311
theorem B3271387 : Blo 1937435 3271387 := bstep (se 1 (by rfl) ⟨2453540, by rfl⟩ : syracuseStep 3271387 = 4907081) B4907081
theorem B4361849 : Blo 1937435 4361849 := bstep (se 2 (by rfl) ⟨1635693, by rfl⟩ : syracuseStep 4361849 = 3271387) B3271387
theorem B2907899 : Blo 1937435 2907899 := bstep (se 1 (by rfl) ⟨2180924, by rfl⟩ : syracuseStep 2907899 = 4361849) B4361849
theorem B1938599 : Blo 1937435 1938599 := bstep (se 1 (by rfl) ⟨1453949, by rfl⟩ : syracuseStep 1938599 = 2907899) B2907899
theorem B2180929 : Blo 1937435 2180929 := bbase (se 2 (by rfl) ⟨817848, by rfl⟩ : syracuseStep 2180929 = 1635697) (by norm_num)
theorem B2907905 : Blo 1937435 2907905 := bstep (se 2 (by rfl) ⟨1090464, by rfl⟩ : syracuseStep 2907905 = 2180929) B2180929
theorem B1938603 : Blo 1937435 1938603 := bstep (se 1 (by rfl) ⟨1453952, by rfl⟩ : syracuseStep 1938603 = 2907905) B2907905
theorem B4907101 : Blo 1937435 4907101 := bbase (se 3 (by rfl) ⟨920081, by rfl⟩ : syracuseStep 4907101 = 1840163) (by norm_num)
theorem B6542801 : Blo 1937435 6542801 := bstep (se 2 (by rfl) ⟨2453550, by rfl⟩ : syracuseStep 6542801 = 4907101) B4907101
theorem B4361867 : Blo 1937435 4361867 := bstep (se 1 (by rfl) ⟨3271400, by rfl⟩ : syracuseStep 4361867 = 6542801) B6542801
theorem B2907911 : Blo 1937435 2907911 := bstep (se 1 (by rfl) ⟨2180933, by rfl⟩ : syracuseStep 2907911 = 4361867) B4361867
theorem B1938607 : Blo 1937435 1938607 := bstep (se 1 (by rfl) ⟨1453955, by rfl⟩ : syracuseStep 1938607 = 2907911) B2907911
theorem B2907917 : Blo 1937435 2907917 := bbase (se 3 (by rfl) ⟨545234, by rfl⟩ : syracuseStep 2907917 = 1090469) (by norm_num)
theorem B1938611 : Blo 1937435 1938611 := bstep (se 1 (by rfl) ⟨1453958, by rfl⟩ : syracuseStep 1938611 = 2907917) B2907917
theorem B4361885 : Blo 1937435 4361885 := bbase (se 3 (by rfl) ⟨817853, by rfl⟩ : syracuseStep 4361885 = 1635707) (by norm_num)
theorem B2907923 : Blo 1937435 2907923 := bstep (se 1 (by rfl) ⟨2180942, by rfl⟩ : syracuseStep 2907923 = 4361885) B4361885
theorem B1938615 : Blo 1937435 1938615 := bstep (se 1 (by rfl) ⟨1453961, by rfl⟩ : syracuseStep 1938615 = 2907923) B2907923
theorem B3271421 : Blo 1937435 3271421 := bbase (se 3 (by rfl) ⟨613391, by rfl⟩ : syracuseStep 3271421 = 1226783) (by norm_num)
theorem B2180947 : Blo 1937435 2180947 := bstep (se 1 (by rfl) ⟨1635710, by rfl⟩ : syracuseStep 2180947 = 3271421) B3271421
theorem B2907929 : Blo 1937435 2907929 := bstep (se 2 (by rfl) ⟨1090473, by rfl⟩ : syracuseStep 2907929 = 2180947) B2180947
theorem B1938619 : Blo 1937435 1938619 := bstep (se 1 (by rfl) ⟨1453964, by rfl⟩ : syracuseStep 1938619 = 2907929) B2907929
theorem B3105301 : Blo 1937435 3105301 := bbase (se 6 (by rfl) ⟨72780, by rfl⟩ : syracuseStep 3105301 = 145561) (by norm_num)
theorem B4140401 : Blo 1937435 4140401 := bstep (se 2 (by rfl) ⟨1552650, by rfl⟩ : syracuseStep 4140401 = 3105301) B3105301
theorem B11041069 : Blo 1937435 11041069 := bstep (se 3 (by rfl) ⟨2070200, by rfl⟩ : syracuseStep 11041069 = 4140401) B4140401
theorem B14721425 : Blo 1937435 14721425 := bstep (se 2 (by rfl) ⟨5520534, by rfl⟩ : syracuseStep 14721425 = 11041069) B11041069
theorem B9814283 : Blo 1937435 9814283 := bstep (se 1 (by rfl) ⟨7360712, by rfl⟩ : syracuseStep 9814283 = 14721425) B14721425
theorem B6542855 : Blo 1937435 6542855 := bstep (se 1 (by rfl) ⟨4907141, by rfl⟩ : syracuseStep 6542855 = 9814283) B9814283
theorem B4361903 : Blo 1937435 4361903 := bstep (se 1 (by rfl) ⟨3271427, by rfl⟩ : syracuseStep 4361903 = 6542855) B6542855
theorem B2907935 : Blo 1937435 2907935 := bstep (se 1 (by rfl) ⟨2180951, by rfl⟩ : syracuseStep 2907935 = 4361903) B4361903
theorem B1938623 : Blo 1937435 1938623 := bstep (se 1 (by rfl) ⟨1453967, by rfl⟩ : syracuseStep 1938623 = 2907935) B2907935
theorem B2907941 : Blo 1937435 2907941 := bbase (se 4 (by rfl) ⟨272619, by rfl⟩ : syracuseStep 2907941 = 545239) (by norm_num)
theorem B1938627 : Blo 1937435 1938627 := bstep (se 1 (by rfl) ⟨1453970, by rfl⟩ : syracuseStep 1938627 = 2907941) B2907941
theorem B2453581 : Blo 1937435 2453581 := bbase (se 3 (by rfl) ⟨460046, by rfl⟩ : syracuseStep 2453581 = 920093) (by norm_num)
theorem B3271441 : Blo 1937435 3271441 := bstep (se 2 (by rfl) ⟨1226790, by rfl⟩ : syracuseStep 3271441 = 2453581) B2453581
theorem B4361921 : Blo 1937435 4361921 := bstep (se 2 (by rfl) ⟨1635720, by rfl⟩ : syracuseStep 4361921 = 3271441) B3271441
theorem B2907947 : Blo 1937435 2907947 := bstep (se 1 (by rfl) ⟨2180960, by rfl⟩ : syracuseStep 2907947 = 4361921) B4361921
theorem B1938631 : Blo 1937435 1938631 := bstep (se 1 (by rfl) ⟨1453973, by rfl⟩ : syracuseStep 1938631 = 2907947) B2907947
theorem B2180965 : Blo 1937435 2180965 := bbase (se 4 (by rfl) ⟨204465, by rfl⟩ : syracuseStep 2180965 = 408931) (by norm_num)
theorem B2907953 : Blo 1937435 2907953 := bstep (se 2 (by rfl) ⟨1090482, by rfl⟩ : syracuseStep 2907953 = 2180965) B2180965
theorem B1938635 : Blo 1937435 1938635 := bstep (se 1 (by rfl) ⟨1453976, by rfl⟩ : syracuseStep 1938635 = 2907953) B2907953
theorem B5520581 : Blo 1937435 5520581 := bbase (se 4 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 5520581 = 1035109) (by norm_num)
theorem B3680387 : Blo 1937435 3680387 := bstep (se 1 (by rfl) ⟨2760290, by rfl⟩ : syracuseStep 3680387 = 5520581) B5520581
theorem B2453591 : Blo 1937435 2453591 := bstep (se 1 (by rfl) ⟨1840193, by rfl⟩ : syracuseStep 2453591 = 3680387) B3680387
theorem B6542909 : Blo 1937435 6542909 := bstep (se 3 (by rfl) ⟨1226795, by rfl⟩ : syracuseStep 6542909 = 2453591) B2453591
theorem B4361939 : Blo 1937435 4361939 := bstep (se 1 (by rfl) ⟨3271454, by rfl⟩ : syracuseStep 4361939 = 6542909) B6542909
theorem B2907959 : Blo 1937435 2907959 := bstep (se 1 (by rfl) ⟨2180969, by rfl⟩ : syracuseStep 2907959 = 4361939) B4361939
theorem B1938639 : Blo 1937435 1938639 := bstep (se 1 (by rfl) ⟨1453979, by rfl⟩ : syracuseStep 1938639 = 2907959) B2907959
theorem B2907965 : Blo 1937435 2907965 := bbase (se 3 (by rfl) ⟨545243, by rfl⟩ : syracuseStep 2907965 = 1090487) (by norm_num)
theorem B1938643 : Blo 1937435 1938643 := bstep (se 1 (by rfl) ⟨1453982, by rfl⟩ : syracuseStep 1938643 = 2907965) B2907965
theorem B4361957 : Blo 1937435 4361957 := bbase (se 4 (by rfl) ⟨408933, by rfl⟩ : syracuseStep 4361957 = 817867) (by norm_num)
theorem B2907971 : Blo 1937435 2907971 := bstep (se 1 (by rfl) ⟨2180978, by rfl⟩ : syracuseStep 2907971 = 4361957) B4361957
theorem B1938647 : Blo 1937435 1938647 := bstep (se 1 (by rfl) ⟨1453985, by rfl⟩ : syracuseStep 1938647 = 2907971) B2907971
theorem B4907213 : Blo 1937435 4907213 := bbase (se 3 (by rfl) ⟨920102, by rfl⟩ : syracuseStep 4907213 = 1840205) (by norm_num)
theorem B3271475 : Blo 1937435 3271475 := bstep (se 1 (by rfl) ⟨2453606, by rfl⟩ : syracuseStep 3271475 = 4907213) B4907213
theorem B2180983 : Blo 1937435 2180983 := bstep (se 1 (by rfl) ⟨1635737, by rfl⟩ : syracuseStep 2180983 = 3271475) B3271475
theorem B2907977 : Blo 1937435 2907977 := bstep (se 2 (by rfl) ⟨1090491, by rfl⟩ : syracuseStep 2907977 = 2180983) B2180983
theorem B1938651 : Blo 1937435 1938651 := bstep (se 1 (by rfl) ⟨1453988, by rfl⟩ : syracuseStep 1938651 = 2907977) B2907977
theorem B2947661 : Blo 1937435 2947661 := bbase (se 3 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 2947661 = 1105373) (by norm_num)
theorem B1965107 : Blo 1937435 1965107 := bstep (se 1 (by rfl) ⟨1473830, by rfl⟩ : syracuseStep 1965107 = 2947661) B2947661
theorem B5240285 : Blo 1937435 5240285 := bstep (se 3 (by rfl) ⟨982553, by rfl⟩ : syracuseStep 5240285 = 1965107) B1965107
theorem B3493523 : Blo 1937435 3493523 := bstep (se 1 (by rfl) ⟨2620142, by rfl⟩ : syracuseStep 3493523 = 5240285) B5240285
theorem B2329015 : Blo 1937435 2329015 := bstep (se 1 (by rfl) ⟨1746761, by rfl⟩ : syracuseStep 2329015 = 3493523) B3493523
theorem B3105353 : Blo 1937435 3105353 := bstep (se 2 (by rfl) ⟨1164507, by rfl⟩ : syracuseStep 3105353 = 2329015) B2329015
theorem B2070235 : Blo 1937435 2070235 := bstep (se 1 (by rfl) ⟨1552676, by rfl⟩ : syracuseStep 2070235 = 3105353) B3105353
theorem B2760313 : Blo 1937435 2760313 := bstep (se 2 (by rfl) ⟨1035117, by rfl⟩ : syracuseStep 2760313 = 2070235) B2070235
theorem B3680417 : Blo 1937435 3680417 := bstep (se 2 (by rfl) ⟨1380156, by rfl⟩ : syracuseStep 3680417 = 2760313) B2760313
theorem B9814445 : Blo 1937435 9814445 := bstep (se 3 (by rfl) ⟨1840208, by rfl⟩ : syracuseStep 9814445 = 3680417) B3680417
theorem B6542963 : Blo 1937435 6542963 := bstep (se 1 (by rfl) ⟨4907222, by rfl⟩ : syracuseStep 6542963 = 9814445) B9814445
theorem B4361975 : Blo 1937435 4361975 := bstep (se 1 (by rfl) ⟨3271481, by rfl⟩ : syracuseStep 4361975 = 6542963) B6542963
theorem B2907983 : Blo 1937435 2907983 := bstep (se 1 (by rfl) ⟨2180987, by rfl⟩ : syracuseStep 2907983 = 4361975) B4361975
theorem B1938655 : Blo 1937435 1938655 := bstep (se 1 (by rfl) ⟨1453991, by rfl⟩ : syracuseStep 1938655 = 2907983) B2907983
theorem B2907989 : Blo 1937435 2907989 := bbase (se 9 (by rfl) ⟨8519, by rfl⟩ : syracuseStep 2907989 = 17039) (by norm_num)
theorem B1938659 : Blo 1937435 1938659 := bstep (se 1 (by rfl) ⟨1453994, by rfl⟩ : syracuseStep 1938659 = 2907989) B2907989
theorem B3930229 : Blo 1937435 3930229 := bbase (se 5 (by rfl) ⟨184229, by rfl⟩ : syracuseStep 3930229 = 368459) (by norm_num)
theorem B5240305 : Blo 1937435 5240305 := bstep (se 2 (by rfl) ⟨1965114, by rfl⟩ : syracuseStep 5240305 = 3930229) B3930229
theorem B6987073 : Blo 1937435 6987073 := bstep (se 2 (by rfl) ⟨2620152, by rfl⟩ : syracuseStep 6987073 = 5240305) B5240305
theorem B9316097 : Blo 1937435 9316097 := bstep (se 2 (by rfl) ⟨3493536, by rfl⟩ : syracuseStep 9316097 = 6987073) B6987073
theorem B6210731 : Blo 1937435 6210731 := bstep (se 1 (by rfl) ⟨4658048, by rfl⟩ : syracuseStep 6210731 = 9316097) B9316097
theorem B4140487 : Blo 1937435 4140487 := bstep (se 1 (by rfl) ⟨3105365, by rfl⟩ : syracuseStep 4140487 = 6210731) B6210731
theorem B5520649 : Blo 1937435 5520649 := bstep (se 2 (by rfl) ⟨2070243, by rfl⟩ : syracuseStep 5520649 = 4140487) B4140487
theorem B7360865 : Blo 1937435 7360865 := bstep (se 2 (by rfl) ⟨2760324, by rfl⟩ : syracuseStep 7360865 = 5520649) B5520649
theorem B4907243 : Blo 1937435 4907243 := bstep (se 1 (by rfl) ⟨3680432, by rfl⟩ : syracuseStep 4907243 = 7360865) B7360865
theorem B3271495 : Blo 1937435 3271495 := bstep (se 1 (by rfl) ⟨2453621, by rfl⟩ : syracuseStep 3271495 = 4907243) B4907243
theorem B4361993 : Blo 1937435 4361993 := bstep (se 2 (by rfl) ⟨1635747, by rfl⟩ : syracuseStep 4361993 = 3271495) B3271495
theorem B2907995 : Blo 1937435 2907995 := bstep (se 1 (by rfl) ⟨2180996, by rfl⟩ : syracuseStep 2907995 = 4361993) B4361993
theorem B1938663 : Blo 1937435 1938663 := bstep (se 1 (by rfl) ⟨1453997, by rfl⟩ : syracuseStep 1938663 = 2907995) B2907995
theorem B2181001 : Blo 1937435 2181001 := bbase (se 2 (by rfl) ⟨817875, by rfl⟩ : syracuseStep 2181001 = 1635751) (by norm_num)
theorem B2908001 : Blo 1937435 2908001 := bstep (se 2 (by rfl) ⟨1090500, by rfl⟩ : syracuseStep 2908001 = 2181001) B2181001
theorem B1938667 : Blo 1937435 1938667 := bstep (se 1 (by rfl) ⟨1454000, by rfl⟩ : syracuseStep 1938667 = 2908001) B2908001
theorem B83845205 : Blo 1937435 83845205 := bbase (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) (by norm_num)
theorem B55896803 : Blo 1937435 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B37264535 : Blo 1937435 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B24843023 : Blo 1937435 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B16562015 : Blo 1937435 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B11041343 : Blo 1937435 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B7360895 : Blo 1937435 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B4907263 : Blo 1937435 4907263 := bstep (se 1 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 4907263 = 7360895) B7360895
theorem B6543017 : Blo 1937435 6543017 := bstep (se 2 (by rfl) ⟨2453631, by rfl⟩ : syracuseStep 6543017 = 4907263) B4907263
theorem B4362011 : Blo 1937435 4362011 := bstep (se 1 (by rfl) ⟨3271508, by rfl⟩ : syracuseStep 4362011 = 6543017) B6543017
theorem B2908007 : Blo 1937435 2908007 := bstep (se 1 (by rfl) ⟨2181005, by rfl⟩ : syracuseStep 2908007 = 4362011) B4362011
theorem B1938671 : Blo 1937435 1938671 := bstep (se 1 (by rfl) ⟨1454003, by rfl⟩ : syracuseStep 1938671 = 2908007) B2908007
theorem B2908013 : Blo 1937435 2908013 := bbase (se 3 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 2908013 = 1090505) (by norm_num)
theorem B1938675 : Blo 1937435 1938675 := bstep (se 1 (by rfl) ⟨1454006, by rfl⟩ : syracuseStep 1938675 = 2908013) B2908013
theorem B4362029 : Blo 1937435 4362029 := bbase (se 3 (by rfl) ⟨817880, by rfl⟩ : syracuseStep 4362029 = 1635761) (by norm_num)
theorem B2908019 : Blo 1937435 2908019 := bstep (se 1 (by rfl) ⟨2181014, by rfl⟩ : syracuseStep 2908019 = 4362029) B4362029
theorem B1938679 : Blo 1937435 1938679 := bstep (se 1 (by rfl) ⟨1454009, by rfl⟩ : syracuseStep 1938679 = 2908019) B2908019
theorem B8281061 : Blo 1937435 8281061 := bbase (se 4 (by rfl) ⟨776349, by rfl⟩ : syracuseStep 8281061 = 1552699) (by norm_num)
theorem B5520707 : Blo 1937435 5520707 := bstep (se 1 (by rfl) ⟨4140530, by rfl⟩ : syracuseStep 5520707 = 8281061) B8281061
theorem B3680471 : Blo 1937435 3680471 := bstep (se 1 (by rfl) ⟨2760353, by rfl⟩ : syracuseStep 3680471 = 5520707) B5520707
theorem B2453647 : Blo 1937435 2453647 := bstep (se 1 (by rfl) ⟨1840235, by rfl⟩ : syracuseStep 2453647 = 3680471) B3680471
theorem B3271529 : Blo 1937435 3271529 := bstep (se 2 (by rfl) ⟨1226823, by rfl⟩ : syracuseStep 3271529 = 2453647) B2453647
theorem B2181019 : Blo 1937435 2181019 := bstep (se 1 (by rfl) ⟨1635764, by rfl⟩ : syracuseStep 2181019 = 3271529) B3271529
theorem B2908025 : Blo 1937435 2908025 := bstep (se 2 (by rfl) ⟨1090509, by rfl⟩ : syracuseStep 2908025 = 2181019) B2181019
theorem B1938683 : Blo 1937435 1938683 := bstep (se 1 (by rfl) ⟨1454012, by rfl⟩ : syracuseStep 1938683 = 2908025) B2908025
theorem B3930277 : Blo 1937435 3930277 := bbase (se 4 (by rfl) ⟨368463, by rfl⟩ : syracuseStep 3930277 = 736927) (by norm_num)
theorem B5240369 : Blo 1937435 5240369 := bstep (se 2 (by rfl) ⟨1965138, by rfl⟩ : syracuseStep 5240369 = 3930277) B3930277
theorem B3493579 : Blo 1937435 3493579 := bstep (se 1 (by rfl) ⟨2620184, by rfl⟩ : syracuseStep 3493579 = 5240369) B5240369
theorem B4658105 : Blo 1937435 4658105 := bstep (se 2 (by rfl) ⟨1746789, by rfl⟩ : syracuseStep 4658105 = 3493579) B3493579
theorem B12421613 : Blo 1937435 12421613 := bstep (se 3 (by rfl) ⟨2329052, by rfl⟩ : syracuseStep 12421613 = 4658105) B4658105
theorem B33124301 : Blo 1937435 33124301 := bstep (se 3 (by rfl) ⟨6210806, by rfl⟩ : syracuseStep 33124301 = 12421613) B12421613
theorem B22082867 : Blo 1937435 22082867 := bstep (se 1 (by rfl) ⟨16562150, by rfl⟩ : syracuseStep 22082867 = 33124301) B33124301
theorem B14721911 : Blo 1937435 14721911 := bstep (se 1 (by rfl) ⟨11041433, by rfl⟩ : syracuseStep 14721911 = 22082867) B22082867
theorem B9814607 : Blo 1937435 9814607 := bstep (se 1 (by rfl) ⟨7360955, by rfl⟩ : syracuseStep 9814607 = 14721911) B14721911
theorem B6543071 : Blo 1937435 6543071 := bstep (se 1 (by rfl) ⟨4907303, by rfl⟩ : syracuseStep 6543071 = 9814607) B9814607
theorem B4362047 : Blo 1937435 4362047 := bstep (se 1 (by rfl) ⟨3271535, by rfl⟩ : syracuseStep 4362047 = 6543071) B6543071
theorem B2908031 : Blo 1937435 2908031 := bstep (se 1 (by rfl) ⟨2181023, by rfl⟩ : syracuseStep 2908031 = 4362047) B4362047
theorem B1938687 : Blo 1937435 1938687 := bstep (se 1 (by rfl) ⟨1454015, by rfl⟩ : syracuseStep 1938687 = 2908031) B2908031
theorem B2908037 : Blo 1937435 2908037 := bbase (se 4 (by rfl) ⟨272628, by rfl⟩ : syracuseStep 2908037 = 545257) (by norm_num)
theorem B1938691 : Blo 1937435 1938691 := bstep (se 1 (by rfl) ⟨1454018, by rfl⟩ : syracuseStep 1938691 = 2908037) B2908037
theorem B3271549 : Blo 1937435 3271549 := bbase (se 3 (by rfl) ⟨613415, by rfl⟩ : syracuseStep 3271549 = 1226831) (by norm_num)
theorem B4362065 : Blo 1937435 4362065 := bstep (se 2 (by rfl) ⟨1635774, by rfl⟩ : syracuseStep 4362065 = 3271549) B3271549
theorem B2908043 : Blo 1937435 2908043 := bstep (se 1 (by rfl) ⟨2181032, by rfl⟩ : syracuseStep 2908043 = 4362065) B4362065
theorem B1938695 : Blo 1937435 1938695 := bstep (se 1 (by rfl) ⟨1454021, by rfl⟩ : syracuseStep 1938695 = 2908043) B2908043
theorem B2181037 : Blo 1937435 2181037 := bbase (se 3 (by rfl) ⟨408944, by rfl⟩ : syracuseStep 2181037 = 817889) (by norm_num)
theorem B2908049 : Blo 1937435 2908049 := bstep (se 2 (by rfl) ⟨1090518, by rfl⟩ : syracuseStep 2908049 = 2181037) B2181037
theorem B1938699 : Blo 1937435 1938699 := bstep (se 1 (by rfl) ⟨1454024, by rfl⟩ : syracuseStep 1938699 = 2908049) B2908049
theorem B6543125 : Blo 1937435 6543125 := bbase (se 6 (by rfl) ⟨153354, by rfl⟩ : syracuseStep 6543125 = 306709) (by norm_num)
theorem B4362083 : Blo 1937435 4362083 := bstep (se 1 (by rfl) ⟨3271562, by rfl⟩ : syracuseStep 4362083 = 6543125) B6543125
theorem B2908055 : Blo 1937435 2908055 := bstep (se 1 (by rfl) ⟨2181041, by rfl⟩ : syracuseStep 2908055 = 4362083) B4362083
theorem B1938703 : Blo 1937435 1938703 := bstep (se 1 (by rfl) ⟨1454027, by rfl⟩ : syracuseStep 1938703 = 2908055) B2908055
theorem B2908061 : Blo 1937435 2908061 := bbase (se 3 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 2908061 = 1090523) (by norm_num)
theorem B1938707 : Blo 1937435 1938707 := bstep (se 1 (by rfl) ⟨1454030, by rfl⟩ : syracuseStep 1938707 = 2908061) B2908061
theorem B4362101 : Blo 1937435 4362101 := bbase (se 5 (by rfl) ⟨204473, by rfl⟩ : syracuseStep 4362101 = 408947) (by norm_num)
theorem B2908067 : Blo 1937435 2908067 := bstep (se 1 (by rfl) ⟨2181050, by rfl⟩ : syracuseStep 2908067 = 4362101) B4362101
theorem B1938711 : Blo 1937435 1938711 := bstep (se 1 (by rfl) ⟨1454033, by rfl⟩ : syracuseStep 1938711 = 2908067) B2908067
theorem B18632693 : Blo 1937435 18632693 := bbase (se 5 (by rfl) ⟨873407, by rfl⟩ : syracuseStep 18632693 = 1746815) (by norm_num)
theorem B12421795 : Blo 1937435 12421795 := bstep (se 1 (by rfl) ⟨9316346, by rfl⟩ : syracuseStep 12421795 = 18632693) B18632693
theorem B16562393 : Blo 1937435 16562393 := bstep (se 2 (by rfl) ⟨6210897, by rfl⟩ : syracuseStep 16562393 = 12421795) B12421795
theorem B11041595 : Blo 1937435 11041595 := bstep (se 1 (by rfl) ⟨8281196, by rfl⟩ : syracuseStep 11041595 = 16562393) B16562393
theorem B7361063 : Blo 1937435 7361063 := bstep (se 1 (by rfl) ⟨5520797, by rfl⟩ : syracuseStep 7361063 = 11041595) B11041595
theorem B4907375 : Blo 1937435 4907375 := bstep (se 1 (by rfl) ⟨3680531, by rfl⟩ : syracuseStep 4907375 = 7361063) B7361063
theorem B3271583 : Blo 1937435 3271583 := bstep (se 1 (by rfl) ⟨2453687, by rfl⟩ : syracuseStep 3271583 = 4907375) B4907375
theorem B2181055 : Blo 1937435 2181055 := bstep (se 1 (by rfl) ⟨1635791, by rfl⟩ : syracuseStep 2181055 = 3271583) B3271583
theorem B2908073 : Blo 1937435 2908073 := bstep (se 2 (by rfl) ⟨1090527, by rfl⟩ : syracuseStep 2908073 = 2181055) B2181055
theorem B1938715 : Blo 1937435 1938715 := bstep (se 1 (by rfl) ⟨1454036, by rfl⟩ : syracuseStep 1938715 = 2908073) B2908073
theorem B7361077 : Blo 1937435 7361077 := bbase (se 5 (by rfl) ⟨345050, by rfl⟩ : syracuseStep 7361077 = 690101) (by norm_num)
theorem B9814769 : Blo 1937435 9814769 := bstep (se 2 (by rfl) ⟨3680538, by rfl⟩ : syracuseStep 9814769 = 7361077) B7361077
theorem B6543179 : Blo 1937435 6543179 := bstep (se 1 (by rfl) ⟨4907384, by rfl⟩ : syracuseStep 6543179 = 9814769) B9814769
theorem B4362119 : Blo 1937435 4362119 := bstep (se 1 (by rfl) ⟨3271589, by rfl⟩ : syracuseStep 4362119 = 6543179) B6543179
theorem B2908079 : Blo 1937435 2908079 := bstep (se 1 (by rfl) ⟨2181059, by rfl⟩ : syracuseStep 2908079 = 4362119) B4362119
theorem B1938719 : Blo 1937435 1938719 := bstep (se 1 (by rfl) ⟨1454039, by rfl⟩ : syracuseStep 1938719 = 2908079) B2908079
theorem B2908085 : Blo 1937435 2908085 := bbase (se 5 (by rfl) ⟨136316, by rfl⟩ : syracuseStep 2908085 = 272633) (by norm_num)
theorem B1938723 : Blo 1937435 1938723 := bstep (se 1 (by rfl) ⟨1454042, by rfl⟩ : syracuseStep 1938723 = 2908085) B2908085
theorem B4907405 : Blo 1937435 4907405 := bbase (se 3 (by rfl) ⟨920138, by rfl⟩ : syracuseStep 4907405 = 1840277) (by norm_num)
theorem B3271603 : Blo 1937435 3271603 := bstep (se 1 (by rfl) ⟨2453702, by rfl⟩ : syracuseStep 3271603 = 4907405) B4907405
theorem B4362137 : Blo 1937435 4362137 := bstep (se 2 (by rfl) ⟨1635801, by rfl⟩ : syracuseStep 4362137 = 3271603) B3271603
theorem B2908091 : Blo 1937435 2908091 := bstep (se 1 (by rfl) ⟨2181068, by rfl⟩ : syracuseStep 2908091 = 4362137) B4362137
theorem B1938727 : Blo 1937435 1938727 := bstep (se 1 (by rfl) ⟨1454045, by rfl⟩ : syracuseStep 1938727 = 2908091) B2908091
theorem B2181073 : Blo 1937435 2181073 := bbase (se 2 (by rfl) ⟨817902, by rfl⟩ : syracuseStep 2181073 = 1635805) (by norm_num)
theorem B2908097 : Blo 1937435 2908097 := bstep (se 2 (by rfl) ⟨1090536, by rfl⟩ : syracuseStep 2908097 = 2181073) B2181073
theorem B1938731 : Blo 1937435 1938731 := bstep (se 1 (by rfl) ⟨1454048, by rfl⟩ : syracuseStep 1938731 = 2908097) B2908097
theorem B5240501 : Blo 1937435 5240501 := bbase (se 5 (by rfl) ⟨245648, by rfl⟩ : syracuseStep 5240501 = 491297) (by norm_num)
theorem B3493667 : Blo 1937435 3493667 := bstep (se 1 (by rfl) ⟨2620250, by rfl⟩ : syracuseStep 3493667 = 5240501) B5240501
theorem B2329111 : Blo 1937435 2329111 := bstep (se 1 (by rfl) ⟨1746833, by rfl⟩ : syracuseStep 2329111 = 3493667) B3493667
theorem B3105481 : Blo 1937435 3105481 := bstep (se 2 (by rfl) ⟨1164555, by rfl⟩ : syracuseStep 3105481 = 2329111) B2329111
theorem B4140641 : Blo 1937435 4140641 := bstep (se 2 (by rfl) ⟨1552740, by rfl⟩ : syracuseStep 4140641 = 3105481) B3105481
theorem B2760427 : Blo 1937435 2760427 := bstep (se 1 (by rfl) ⟨2070320, by rfl⟩ : syracuseStep 2760427 = 4140641) B4140641
theorem B3680569 : Blo 1937435 3680569 := bstep (se 2 (by rfl) ⟨1380213, by rfl⟩ : syracuseStep 3680569 = 2760427) B2760427
theorem B4907425 : Blo 1937435 4907425 := bstep (se 2 (by rfl) ⟨1840284, by rfl⟩ : syracuseStep 4907425 = 3680569) B3680569
theorem B6543233 : Blo 1937435 6543233 := bstep (se 2 (by rfl) ⟨2453712, by rfl⟩ : syracuseStep 6543233 = 4907425) B4907425
theorem B4362155 : Blo 1937435 4362155 := bstep (se 1 (by rfl) ⟨3271616, by rfl⟩ : syracuseStep 4362155 = 6543233) B6543233
theorem B2908103 : Blo 1937435 2908103 := bstep (se 1 (by rfl) ⟨2181077, by rfl⟩ : syracuseStep 2908103 = 4362155) B4362155
theorem B1938735 : Blo 1937435 1938735 := bstep (se 1 (by rfl) ⟨1454051, by rfl⟩ : syracuseStep 1938735 = 2908103) B2908103
theorem B2908109 : Blo 1937435 2908109 := bbase (se 3 (by rfl) ⟨545270, by rfl⟩ : syracuseStep 2908109 = 1090541) (by norm_num)
theorem B1938739 : Blo 1937435 1938739 := bstep (se 1 (by rfl) ⟨1454054, by rfl⟩ : syracuseStep 1938739 = 2908109) B2908109
theorem B4362173 : Blo 1937435 4362173 := bbase (se 3 (by rfl) ⟨817907, by rfl⟩ : syracuseStep 4362173 = 1635815) (by norm_num)
theorem B2908115 : Blo 1937435 2908115 := bstep (se 1 (by rfl) ⟨2181086, by rfl⟩ : syracuseStep 2908115 = 4362173) B4362173
theorem B1938743 : Blo 1937435 1938743 := bstep (se 1 (by rfl) ⟨1454057, by rfl⟩ : syracuseStep 1938743 = 2908115) B2908115
theorem B3271637 : Blo 1937435 3271637 := bbase (se 7 (by rfl) ⟨38339, by rfl⟩ : syracuseStep 3271637 = 76679) (by norm_num)
theorem B2181091 : Blo 1937435 2181091 := bstep (se 1 (by rfl) ⟨1635818, by rfl⟩ : syracuseStep 2181091 = 3271637) B3271637
theorem B2908121 : Blo 1937435 2908121 := bstep (se 2 (by rfl) ⟨1090545, by rfl⟩ : syracuseStep 2908121 = 2181091) B2181091
theorem B1938747 : Blo 1937435 1938747 := bstep (se 1 (by rfl) ⟨1454060, by rfl⟩ : syracuseStep 1938747 = 2908121) B2908121
theorem B8281349 : Blo 1937435 8281349 := bbase (se 4 (by rfl) ⟨776376, by rfl⟩ : syracuseStep 8281349 = 1552753) (by norm_num)
theorem B5520899 : Blo 1937435 5520899 := bstep (se 1 (by rfl) ⟨4140674, by rfl⟩ : syracuseStep 5520899 = 8281349) B8281349
theorem B14722397 : Blo 1937435 14722397 := bstep (se 3 (by rfl) ⟨2760449, by rfl⟩ : syracuseStep 14722397 = 5520899) B5520899
theorem B9814931 : Blo 1937435 9814931 := bstep (se 1 (by rfl) ⟨7361198, by rfl⟩ : syracuseStep 9814931 = 14722397) B14722397
theorem B6543287 : Blo 1937435 6543287 := bstep (se 1 (by rfl) ⟨4907465, by rfl⟩ : syracuseStep 6543287 = 9814931) B9814931
theorem B4362191 : Blo 1937435 4362191 := bstep (se 1 (by rfl) ⟨3271643, by rfl⟩ : syracuseStep 4362191 = 6543287) B6543287
theorem B2908127 : Blo 1937435 2908127 := bstep (se 1 (by rfl) ⟨2181095, by rfl⟩ : syracuseStep 2908127 = 4362191) B4362191
theorem B1938751 : Blo 1937435 1938751 := bstep (se 1 (by rfl) ⟨1454063, by rfl⟩ : syracuseStep 1938751 = 2908127) B2908127
theorem B2908133 : Blo 1937435 2908133 := bbase (se 4 (by rfl) ⟨272637, by rfl⟩ : syracuseStep 2908133 = 545275) (by norm_num)
theorem B1938755 : Blo 1937435 1938755 := bstep (se 1 (by rfl) ⟨1454066, by rfl⟩ : syracuseStep 1938755 = 2908133) B2908133
theorem B3361541 : Blo 1937435 3361541 := bbase (se 4 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 3361541 = 630289) (by norm_num)
theorem B8964109 : Blo 1937435 8964109 := bstep (se 3 (by rfl) ⟨1680770, by rfl⟩ : syracuseStep 8964109 = 3361541) B3361541
theorem B11952145 : Blo 1937435 11952145 := bstep (se 2 (by rfl) ⟨4482054, by rfl⟩ : syracuseStep 11952145 = 8964109) B8964109
theorem B15936193 : Blo 1937435 15936193 := bstep (se 2 (by rfl) ⟨5976072, by rfl⟩ : syracuseStep 15936193 = 11952145) B11952145
theorem B21248257 : Blo 1937435 21248257 := bstep (se 2 (by rfl) ⟨7968096, by rfl⟩ : syracuseStep 21248257 = 15936193) B15936193
theorem B28331009 : Blo 1937435 28331009 := bstep (se 2 (by rfl) ⟨10624128, by rfl⟩ : syracuseStep 28331009 = 21248257) B21248257
theorem B18887339 : Blo 1937435 18887339 := bstep (se 1 (by rfl) ⟨14165504, by rfl⟩ : syracuseStep 18887339 = 28331009) B28331009
theorem B12591559 : Blo 1937435 12591559 := bstep (se 1 (by rfl) ⟨9443669, by rfl⟩ : syracuseStep 12591559 = 18887339) B18887339
theorem B16788745 : Blo 1937435 16788745 := bstep (se 2 (by rfl) ⟨6295779, by rfl⟩ : syracuseStep 16788745 = 12591559) B12591559
theorem B22384993 : Blo 1937435 22384993 := bstep (se 2 (by rfl) ⟨8394372, by rfl⟩ : syracuseStep 22384993 = 16788745) B16788745
theorem B29846657 : Blo 1937435 29846657 := bstep (se 2 (by rfl) ⟨11192496, by rfl⟩ : syracuseStep 29846657 = 22384993) B22384993
theorem B19897771 : Blo 1937435 19897771 := bstep (se 1 (by rfl) ⟨14923328, by rfl⟩ : syracuseStep 19897771 = 29846657) B29846657
theorem B26530361 : Blo 1937435 26530361 := bstep (se 2 (by rfl) ⟨9948885, by rfl⟩ : syracuseStep 26530361 = 19897771) B19897771
theorem B17686907 : Blo 1937435 17686907 := bstep (se 1 (by rfl) ⟨13265180, by rfl⟩ : syracuseStep 17686907 = 26530361) B26530361
theorem B11791271 : Blo 1937435 11791271 := bstep (se 1 (by rfl) ⟨8843453, by rfl⟩ : syracuseStep 11791271 = 17686907) B17686907
theorem B31443389 : Blo 1937435 31443389 := bstep (se 3 (by rfl) ⟨5895635, by rfl⟩ : syracuseStep 31443389 = 11791271) B11791271
theorem B20962259 : Blo 1937435 20962259 := bstep (se 1 (by rfl) ⟨15721694, by rfl⟩ : syracuseStep 20962259 = 31443389) B31443389
theorem B13974839 : Blo 1937435 13974839 := bstep (se 1 (by rfl) ⟨10481129, by rfl⟩ : syracuseStep 13974839 = 20962259) B20962259
theorem B9316559 : Blo 1937435 9316559 := bstep (se 1 (by rfl) ⟨6987419, by rfl⟩ : syracuseStep 9316559 = 13974839) B13974839
theorem B6211039 : Blo 1937435 6211039 := bstep (se 1 (by rfl) ⟨4658279, by rfl⟩ : syracuseStep 6211039 = 9316559) B9316559
theorem B8281385 : Blo 1937435 8281385 := bstep (se 2 (by rfl) ⟨3105519, by rfl⟩ : syracuseStep 8281385 = 6211039) B6211039
theorem B5520923 : Blo 1937435 5520923 := bstep (se 1 (by rfl) ⟨4140692, by rfl⟩ : syracuseStep 5520923 = 8281385) B8281385
theorem B3680615 : Blo 1937435 3680615 := bstep (se 1 (by rfl) ⟨2760461, by rfl⟩ : syracuseStep 3680615 = 5520923) B5520923
theorem B2453743 : Blo 1937435 2453743 := bstep (se 1 (by rfl) ⟨1840307, by rfl⟩ : syracuseStep 2453743 = 3680615) B3680615
theorem B3271657 : Blo 1937435 3271657 := bstep (se 2 (by rfl) ⟨1226871, by rfl⟩ : syracuseStep 3271657 = 2453743) B2453743
theorem B4362209 : Blo 1937435 4362209 := bstep (se 2 (by rfl) ⟨1635828, by rfl⟩ : syracuseStep 4362209 = 3271657) B3271657
theorem B2908139 : Blo 1937435 2908139 := bstep (se 1 (by rfl) ⟨2181104, by rfl⟩ : syracuseStep 2908139 = 4362209) B4362209
theorem B1938759 : Blo 1937435 1938759 := bstep (se 1 (by rfl) ⟨1454069, by rfl⟩ : syracuseStep 1938759 = 2908139) B2908139
theorem B2181109 : Blo 1937435 2181109 := bbase (se 5 (by rfl) ⟨102239, by rfl⟩ : syracuseStep 2181109 = 204479) (by norm_num)
theorem B2908145 : Blo 1937435 2908145 := bstep (se 2 (by rfl) ⟨1090554, by rfl⟩ : syracuseStep 2908145 = 2181109) B2181109
theorem B1938763 : Blo 1937435 1938763 := bstep (se 1 (by rfl) ⟨1454072, by rfl⟩ : syracuseStep 1938763 = 2908145) B2908145
theorem B2453753 : Blo 1937435 2453753 := bbase (se 2 (by rfl) ⟨920157, by rfl⟩ : syracuseStep 2453753 = 1840315) (by norm_num)
theorem B6543341 : Blo 1937435 6543341 := bstep (se 3 (by rfl) ⟨1226876, by rfl⟩ : syracuseStep 6543341 = 2453753) B2453753
theorem B4362227 : Blo 1937435 4362227 := bstep (se 1 (by rfl) ⟨3271670, by rfl⟩ : syracuseStep 4362227 = 6543341) B6543341
theorem B2908151 : Blo 1937435 2908151 := bstep (se 1 (by rfl) ⟨2181113, by rfl⟩ : syracuseStep 2908151 = 4362227) B4362227
theorem B1938767 : Blo 1937435 1938767 := bstep (se 1 (by rfl) ⟨1454075, by rfl⟩ : syracuseStep 1938767 = 2908151) B2908151
theorem B2908157 : Blo 1937435 2908157 := bbase (se 3 (by rfl) ⟨545279, by rfl⟩ : syracuseStep 2908157 = 1090559) (by norm_num)
theorem B1938771 : Blo 1937435 1938771 := bstep (se 1 (by rfl) ⟨1454078, by rfl⟩ : syracuseStep 1938771 = 2908157) B2908157
theorem B4362245 : Blo 1937435 4362245 := bbase (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) (by norm_num)
theorem B2908163 : Blo 1937435 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B1938775 : Blo 1937435 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B3680653 : Blo 1937435 3680653 := bbase (se 3 (by rfl) ⟨690122, by rfl⟩ : syracuseStep 3680653 = 1380245) (by norm_num)
theorem B4907537 : Blo 1937435 4907537 := bstep (se 2 (by rfl) ⟨1840326, by rfl⟩ : syracuseStep 4907537 = 3680653) B3680653
theorem B3271691 : Blo 1937435 3271691 := bstep (se 1 (by rfl) ⟨2453768, by rfl⟩ : syracuseStep 3271691 = 4907537) B4907537
theorem B2181127 : Blo 1937435 2181127 := bstep (se 1 (by rfl) ⟨1635845, by rfl⟩ : syracuseStep 2181127 = 3271691) B3271691
theorem B2908169 : Blo 1937435 2908169 := bstep (se 2 (by rfl) ⟨1090563, by rfl⟩ : syracuseStep 2908169 = 2181127) B2181127
theorem B1938779 : Blo 1937435 1938779 := bstep (se 1 (by rfl) ⟨1454084, by rfl⟩ : syracuseStep 1938779 = 2908169) B2908169
theorem B9815093 : Blo 1937435 9815093 := bbase (se 5 (by rfl) ⟨460082, by rfl⟩ : syracuseStep 9815093 = 920165) (by norm_num)
theorem B6543395 : Blo 1937435 6543395 := bstep (se 1 (by rfl) ⟨4907546, by rfl⟩ : syracuseStep 6543395 = 9815093) B9815093
theorem B4362263 : Blo 1937435 4362263 := bstep (se 1 (by rfl) ⟨3271697, by rfl⟩ : syracuseStep 4362263 = 6543395) B6543395
theorem B2908175 : Blo 1937435 2908175 := bstep (se 1 (by rfl) ⟨2181131, by rfl⟩ : syracuseStep 2908175 = 4362263) B4362263
theorem B1938783 : Blo 1937435 1938783 := bstep (se 1 (by rfl) ⟨1454087, by rfl⟩ : syracuseStep 1938783 = 2908175) B2908175
theorem B2908181 : Blo 1937435 2908181 := bbase (se 6 (by rfl) ⟨68160, by rfl⟩ : syracuseStep 2908181 = 136321) (by norm_num)
theorem B1938787 : Blo 1937435 1938787 := bstep (se 1 (by rfl) ⟨1454090, by rfl⟩ : syracuseStep 1938787 = 2908181) B2908181
theorem B5672693 : Blo 1937435 5672693 := bbase (se 5 (by rfl) ⟨265907, by rfl⟩ : syracuseStep 5672693 = 531815) (by norm_num)
theorem B15127181 : Blo 1937435 15127181 := bstep (se 3 (by rfl) ⟨2836346, by rfl⟩ : syracuseStep 15127181 = 5672693) B5672693
theorem B10084787 : Blo 1937435 10084787 := bstep (se 1 (by rfl) ⟨7563590, by rfl⟩ : syracuseStep 10084787 = 15127181) B15127181
theorem B6723191 : Blo 1937435 6723191 := bstep (se 1 (by rfl) ⟨5042393, by rfl⟩ : syracuseStep 6723191 = 10084787) B10084787
theorem B4482127 : Blo 1937435 4482127 := bstep (se 1 (by rfl) ⟨3361595, by rfl⟩ : syracuseStep 4482127 = 6723191) B6723191
theorem B23904677 : Blo 1937435 23904677 := bstep (se 4 (by rfl) ⟨2241063, by rfl⟩ : syracuseStep 23904677 = 4482127) B4482127
theorem B63745805 : Blo 1937435 63745805 := bstep (se 3 (by rfl) ⟨11952338, by rfl⟩ : syracuseStep 63745805 = 23904677) B23904677
theorem B169988813 : Blo 1937435 169988813 := bstep (se 3 (by rfl) ⟨31872902, by rfl⟩ : syracuseStep 169988813 = 63745805) B63745805
theorem B113325875 : Blo 1937435 113325875 := bstep (se 1 (by rfl) ⟨84994406, by rfl⟩ : syracuseStep 113325875 = 169988813) B169988813
theorem B75550583 : Blo 1937435 75550583 := bstep (se 1 (by rfl) ⟨56662937, by rfl⟩ : syracuseStep 75550583 = 113325875) B113325875
theorem B50367055 : Blo 1937435 50367055 := bstep (se 1 (by rfl) ⟨37775291, by rfl⟩ : syracuseStep 50367055 = 75550583) B75550583
theorem B67156073 : Blo 1937435 67156073 := bstep (se 2 (by rfl) ⟨25183527, by rfl⟩ : syracuseStep 67156073 = 50367055) B50367055
theorem B44770715 : Blo 1937435 44770715 := bstep (se 1 (by rfl) ⟨33578036, by rfl⟩ : syracuseStep 44770715 = 67156073) B67156073
theorem B29847143 : Blo 1937435 29847143 := bstep (se 1 (by rfl) ⟨22385357, by rfl⟩ : syracuseStep 29847143 = 44770715) B44770715
theorem B79592381 : Blo 1937435 79592381 := bstep (se 3 (by rfl) ⟨14923571, by rfl⟩ : syracuseStep 79592381 = 29847143) B29847143
theorem B53061587 : Blo 1937435 53061587 := bstep (se 1 (by rfl) ⟨39796190, by rfl⟩ : syracuseStep 53061587 = 79592381) B79592381
theorem B35374391 : Blo 1937435 35374391 := bstep (se 1 (by rfl) ⟨26530793, by rfl⟩ : syracuseStep 35374391 = 53061587) B53061587
theorem B23582927 : Blo 1937435 23582927 := bstep (se 1 (by rfl) ⟨17687195, by rfl⟩ : syracuseStep 23582927 = 35374391) B35374391
theorem B15721951 : Blo 1937435 15721951 := bstep (se 1 (by rfl) ⟨11791463, by rfl⟩ : syracuseStep 15721951 = 23582927) B23582927
theorem B20962601 : Blo 1937435 20962601 := bstep (se 2 (by rfl) ⟨7860975, by rfl⟩ : syracuseStep 20962601 = 15721951) B15721951
theorem B13975067 : Blo 1937435 13975067 := bstep (se 1 (by rfl) ⟨10481300, by rfl⟩ : syracuseStep 13975067 = 20962601) B20962601
theorem B9316711 : Blo 1937435 9316711 := bstep (se 1 (by rfl) ⟨6987533, by rfl⟩ : syracuseStep 9316711 = 13975067) B13975067
theorem B12422281 : Blo 1937435 12422281 := bstep (se 2 (by rfl) ⟨4658355, by rfl⟩ : syracuseStep 12422281 = 9316711) B9316711
theorem B16563041 : Blo 1937435 16563041 := bstep (se 2 (by rfl) ⟨6211140, by rfl⟩ : syracuseStep 16563041 = 12422281) B12422281
theorem B11042027 : Blo 1937435 11042027 := bstep (se 1 (by rfl) ⟨8281520, by rfl⟩ : syracuseStep 11042027 = 16563041) B16563041
theorem B7361351 : Blo 1937435 7361351 := bstep (se 1 (by rfl) ⟨5521013, by rfl⟩ : syracuseStep 7361351 = 11042027) B11042027
theorem B4907567 : Blo 1937435 4907567 := bstep (se 1 (by rfl) ⟨3680675, by rfl⟩ : syracuseStep 4907567 = 7361351) B7361351
theorem B3271711 : Blo 1937435 3271711 := bstep (se 1 (by rfl) ⟨2453783, by rfl⟩ : syracuseStep 3271711 = 4907567) B4907567
theorem B4362281 : Blo 1937435 4362281 := bstep (se 2 (by rfl) ⟨1635855, by rfl⟩ : syracuseStep 4362281 = 3271711) B3271711
theorem B2908187 : Blo 1937435 2908187 := bstep (se 1 (by rfl) ⟨2181140, by rfl⟩ : syracuseStep 2908187 = 4362281) B4362281
theorem B1938791 : Blo 1937435 1938791 := bstep (se 1 (by rfl) ⟨1454093, by rfl⟩ : syracuseStep 1938791 = 2908187) B2908187
theorem B2181145 : Blo 1937435 2181145 := bbase (se 2 (by rfl) ⟨817929, by rfl⟩ : syracuseStep 2181145 = 1635859) (by norm_num)
theorem B2908193 : Blo 1937435 2908193 := bstep (se 2 (by rfl) ⟨1090572, by rfl⟩ : syracuseStep 2908193 = 2181145) B2181145
theorem B1938795 : Blo 1937435 1938795 := bstep (se 1 (by rfl) ⟨1454096, by rfl⟩ : syracuseStep 1938795 = 2908193) B2908193
theorem B7361381 : Blo 1937435 7361381 := bbase (se 4 (by rfl) ⟨690129, by rfl⟩ : syracuseStep 7361381 = 1380259) (by norm_num)
theorem B4907587 : Blo 1937435 4907587 := bstep (se 1 (by rfl) ⟨3680690, by rfl⟩ : syracuseStep 4907587 = 7361381) B7361381
theorem B6543449 : Blo 1937435 6543449 := bstep (se 2 (by rfl) ⟨2453793, by rfl⟩ : syracuseStep 6543449 = 4907587) B4907587
theorem B4362299 : Blo 1937435 4362299 := bstep (se 1 (by rfl) ⟨3271724, by rfl⟩ : syracuseStep 4362299 = 6543449) B6543449
theorem B2908199 : Blo 1937435 2908199 := bstep (se 1 (by rfl) ⟨2181149, by rfl⟩ : syracuseStep 2908199 = 4362299) B4362299
theorem B1938799 : Blo 1937435 1938799 := bstep (se 1 (by rfl) ⟨1454099, by rfl⟩ : syracuseStep 1938799 = 2908199) B2908199
theorem B2908205 : Blo 1937435 2908205 := bbase (se 3 (by rfl) ⟨545288, by rfl⟩ : syracuseStep 2908205 = 1090577) (by norm_num)
theorem B1938803 : Blo 1937435 1938803 := bstep (se 1 (by rfl) ⟨1454102, by rfl⟩ : syracuseStep 1938803 = 2908205) B2908205
theorem B4362317 : Blo 1937435 4362317 := bbase (se 3 (by rfl) ⟨817934, by rfl⟩ : syracuseStep 4362317 = 1635869) (by norm_num)
theorem B2908211 : Blo 1937435 2908211 := bstep (se 1 (by rfl) ⟨2181158, by rfl⟩ : syracuseStep 2908211 = 4362317) B4362317
theorem B1938807 : Blo 1937435 1938807 := bstep (se 1 (by rfl) ⟨1454105, by rfl⟩ : syracuseStep 1938807 = 2908211) B2908211
theorem B2453809 : Blo 1937435 2453809 := bbase (se 2 (by rfl) ⟨920178, by rfl⟩ : syracuseStep 2453809 = 1840357) (by norm_num)
theorem B3271745 : Blo 1937435 3271745 := bstep (se 2 (by rfl) ⟨1226904, by rfl⟩ : syracuseStep 3271745 = 2453809) B2453809
theorem B2181163 : Blo 1937435 2181163 := bstep (se 1 (by rfl) ⟨1635872, by rfl⟩ : syracuseStep 2181163 = 3271745) B3271745
theorem B2908217 : Blo 1937435 2908217 := bstep (se 2 (by rfl) ⟨1090581, by rfl⟩ : syracuseStep 2908217 = 2181163) B2181163
theorem B1938811 : Blo 1937435 1938811 := bstep (se 1 (by rfl) ⟨1454108, by rfl⟩ : syracuseStep 1938811 = 2908217) B2908217
theorem B4658413 : Blo 1937435 4658413 := bbase (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) (by norm_num)
theorem B6211217 : Blo 1937435 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B4140811 : Blo 1937435 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B22084325 : Blo 1937435 22084325 := bstep (se 4 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 22084325 = 4140811) B4140811
theorem B14722883 : Blo 1937435 14722883 := bstep (se 1 (by rfl) ⟨11042162, by rfl⟩ : syracuseStep 14722883 = 22084325) B22084325
theorem B9815255 : Blo 1937435 9815255 := bstep (se 1 (by rfl) ⟨7361441, by rfl⟩ : syracuseStep 9815255 = 14722883) B14722883
theorem B6543503 : Blo 1937435 6543503 := bstep (se 1 (by rfl) ⟨4907627, by rfl⟩ : syracuseStep 6543503 = 9815255) B9815255
theorem B4362335 : Blo 1937435 4362335 := bstep (se 1 (by rfl) ⟨3271751, by rfl⟩ : syracuseStep 4362335 = 6543503) B6543503
theorem B2908223 : Blo 1937435 2908223 := bstep (se 1 (by rfl) ⟨2181167, by rfl⟩ : syracuseStep 2908223 = 4362335) B4362335
theorem B1938815 : Blo 1937435 1938815 := bstep (se 1 (by rfl) ⟨1454111, by rfl⟩ : syracuseStep 1938815 = 2908223) B2908223
theorem B2908229 : Blo 1937435 2908229 := bbase (se 4 (by rfl) ⟨272646, by rfl⟩ : syracuseStep 2908229 = 545293) (by norm_num)
theorem B1938819 : Blo 1937435 1938819 := bstep (se 1 (by rfl) ⟨1454114, by rfl⟩ : syracuseStep 1938819 = 2908229) B2908229
theorem B3271765 : Blo 1937435 3271765 := bbase (se 8 (by rfl) ⟨19170, by rfl⟩ : syracuseStep 3271765 = 38341) (by norm_num)
theorem B4362353 : Blo 1937435 4362353 := bstep (se 2 (by rfl) ⟨1635882, by rfl⟩ : syracuseStep 4362353 = 3271765) B3271765
theorem B2908235 : Blo 1937435 2908235 := bstep (se 1 (by rfl) ⟨2181176, by rfl⟩ : syracuseStep 2908235 = 4362353) B4362353
theorem B1938823 : Blo 1937435 1938823 := bstep (se 1 (by rfl) ⟨1454117, by rfl⟩ : syracuseStep 1938823 = 2908235) B2908235
theorem B2181181 : Blo 1937435 2181181 := bbase (se 3 (by rfl) ⟨408971, by rfl⟩ : syracuseStep 2181181 = 817943) (by norm_num)
theorem B2908241 : Blo 1937435 2908241 := bstep (se 2 (by rfl) ⟨1090590, by rfl⟩ : syracuseStep 2908241 = 2181181) B2181181
theorem B1938827 : Blo 1937435 1938827 := bstep (se 1 (by rfl) ⟨1454120, by rfl⟩ : syracuseStep 1938827 = 2908241) B2908241
theorem B6543557 : Blo 1937435 6543557 := bbase (se 4 (by rfl) ⟨613458, by rfl⟩ : syracuseStep 6543557 = 1226917) (by norm_num)
theorem B4362371 : Blo 1937435 4362371 := bstep (se 1 (by rfl) ⟨3271778, by rfl⟩ : syracuseStep 4362371 = 6543557) B6543557
theorem B2908247 : Blo 1937435 2908247 := bstep (se 1 (by rfl) ⟨2181185, by rfl⟩ : syracuseStep 2908247 = 4362371) B4362371
theorem B1938831 : Blo 1937435 1938831 := bstep (se 1 (by rfl) ⟨1454123, by rfl⟩ : syracuseStep 1938831 = 2908247) B2908247
theorem B2908253 : Blo 1937435 2908253 := bbase (se 3 (by rfl) ⟨545297, by rfl⟩ : syracuseStep 2908253 = 1090595) (by norm_num)
theorem B1938835 : Blo 1937435 1938835 := bstep (se 1 (by rfl) ⟨1454126, by rfl⟩ : syracuseStep 1938835 = 2908253) B2908253
theorem B4362389 : Blo 1937435 4362389 := bbase (se 6 (by rfl) ⟨102243, by rfl⟩ : syracuseStep 4362389 = 204487) (by norm_num)
theorem B2908259 : Blo 1937435 2908259 := bstep (se 1 (by rfl) ⟨2181194, by rfl⟩ : syracuseStep 2908259 = 4362389) B4362389
theorem B1938839 : Blo 1937435 1938839 := bstep (se 1 (by rfl) ⟨1454129, by rfl⟩ : syracuseStep 1938839 = 2908259) B2908259
theorem B2760581 : Blo 1937435 2760581 := bbase (se 4 (by rfl) ⟨258804, by rfl⟩ : syracuseStep 2760581 = 517609) (by norm_num)
theorem B7361549 : Blo 1937435 7361549 := bstep (se 3 (by rfl) ⟨1380290, by rfl⟩ : syracuseStep 7361549 = 2760581) B2760581
theorem B4907699 : Blo 1937435 4907699 := bstep (se 1 (by rfl) ⟨3680774, by rfl⟩ : syracuseStep 4907699 = 7361549) B7361549
theorem B3271799 : Blo 1937435 3271799 := bstep (se 1 (by rfl) ⟨2453849, by rfl⟩ : syracuseStep 3271799 = 4907699) B4907699
theorem B2181199 : Blo 1937435 2181199 := bstep (se 1 (by rfl) ⟨1635899, by rfl⟩ : syracuseStep 2181199 = 3271799) B3271799
theorem B2908265 : Blo 1937435 2908265 := bstep (se 2 (by rfl) ⟨1090599, by rfl⟩ : syracuseStep 2908265 = 2181199) B2181199
theorem B1938843 : Blo 1937435 1938843 := bstep (se 1 (by rfl) ⟨1454132, by rfl⟩ : syracuseStep 1938843 = 2908265) B2908265
theorem B3234517 : Blo 1937435 3234517 := bbase (se 7 (by rfl) ⟨37904, by rfl⟩ : syracuseStep 3234517 = 75809) (by norm_num)
theorem B17250757 : Blo 1937435 17250757 := bstep (se 4 (by rfl) ⟨1617258, by rfl⟩ : syracuseStep 17250757 = 3234517) B3234517
theorem B368016149 : Blo 1937435 368016149 := bstep (se 6 (by rfl) ⟨8625378, by rfl⟩ : syracuseStep 368016149 = 17250757) B17250757
theorem B245344099 : Blo 1937435 245344099 := bstep (se 1 (by rfl) ⟨184008074, by rfl⟩ : syracuseStep 245344099 = 368016149) B368016149
theorem B327125465 : Blo 1937435 327125465 := bstep (se 2 (by rfl) ⟨122672049, by rfl⟩ : syracuseStep 327125465 = 245344099) B245344099
theorem B218083643 : Blo 1937435 218083643 := bstep (se 1 (by rfl) ⟨163562732, by rfl⟩ : syracuseStep 218083643 = 327125465) B327125465
theorem B145389095 : Blo 1937435 145389095 := bstep (se 1 (by rfl) ⟨109041821, by rfl⟩ : syracuseStep 145389095 = 218083643) B218083643
theorem B96926063 : Blo 1937435 96926063 := bstep (se 1 (by rfl) ⟨72694547, by rfl⟩ : syracuseStep 96926063 = 145389095) B145389095
theorem B258469501 : Blo 1937435 258469501 := bstep (se 3 (by rfl) ⟨48463031, by rfl⟩ : syracuseStep 258469501 = 96926063) B96926063
theorem B344626001 : Blo 1937435 344626001 := bstep (se 2 (by rfl) ⟨129234750, by rfl⟩ : syracuseStep 344626001 = 258469501) B258469501
theorem B229750667 : Blo 1937435 229750667 := bstep (se 1 (by rfl) ⟨172313000, by rfl⟩ : syracuseStep 229750667 = 344626001) B344626001
theorem B153167111 : Blo 1937435 153167111 := bstep (se 1 (by rfl) ⟨114875333, by rfl⟩ : syracuseStep 153167111 = 229750667) B229750667
theorem B102111407 : Blo 1937435 102111407 := bstep (se 1 (by rfl) ⟨76583555, by rfl⟩ : syracuseStep 102111407 = 153167111) B153167111
theorem B68074271 : Blo 1937435 68074271 := bstep (se 1 (by rfl) ⟨51055703, by rfl⟩ : syracuseStep 68074271 = 102111407) B102111407
theorem B45382847 : Blo 1937435 45382847 := bstep (se 1 (by rfl) ⟨34037135, by rfl⟩ : syracuseStep 45382847 = 68074271) B68074271
theorem B121020925 : Blo 1937435 121020925 := bstep (se 3 (by rfl) ⟨22691423, by rfl⟩ : syracuseStep 121020925 = 45382847) B45382847
theorem B161361233 : Blo 1937435 161361233 := bstep (se 2 (by rfl) ⟨60510462, by rfl⟩ : syracuseStep 161361233 = 121020925) B121020925
theorem B107574155 : Blo 1937435 107574155 := bstep (se 1 (by rfl) ⟨80680616, by rfl⟩ : syracuseStep 107574155 = 161361233) B161361233
theorem B71716103 : Blo 1937435 71716103 := bstep (se 1 (by rfl) ⟨53787077, by rfl⟩ : syracuseStep 71716103 = 107574155) B107574155
theorem B47810735 : Blo 1937435 47810735 := bstep (se 1 (by rfl) ⟨35858051, by rfl⟩ : syracuseStep 47810735 = 71716103) B71716103
theorem B31873823 : Blo 1937435 31873823 := bstep (se 1 (by rfl) ⟨23905367, by rfl⟩ : syracuseStep 31873823 = 47810735) B47810735
theorem B21249215 : Blo 1937435 21249215 := bstep (se 1 (by rfl) ⟨15936911, by rfl⟩ : syracuseStep 21249215 = 31873823) B31873823
theorem B14166143 : Blo 1937435 14166143 := bstep (se 1 (by rfl) ⟨10624607, by rfl⟩ : syracuseStep 14166143 = 21249215) B21249215
theorem B9444095 : Blo 1937435 9444095 := bstep (se 1 (by rfl) ⟨7083071, by rfl⟩ : syracuseStep 9444095 = 14166143) B14166143
theorem B6296063 : Blo 1937435 6296063 := bstep (se 1 (by rfl) ⟨4722047, by rfl⟩ : syracuseStep 6296063 = 9444095) B9444095
theorem B16789501 : Blo 1937435 16789501 := bstep (se 3 (by rfl) ⟨3148031, by rfl⟩ : syracuseStep 16789501 = 6296063) B6296063
theorem B89544005 : Blo 1937435 89544005 := bstep (se 4 (by rfl) ⟨8394750, by rfl⟩ : syracuseStep 89544005 = 16789501) B16789501
theorem B59696003 : Blo 1937435 59696003 := bstep (se 1 (by rfl) ⟨44772002, by rfl⟩ : syracuseStep 59696003 = 89544005) B89544005
theorem B39797335 : Blo 1937435 39797335 := bstep (se 1 (by rfl) ⟨29848001, by rfl⟩ : syracuseStep 39797335 = 59696003) B59696003
theorem B53063113 : Blo 1937435 53063113 := bstep (se 2 (by rfl) ⟨19898667, by rfl⟩ : syracuseStep 53063113 = 39797335) B39797335
theorem B70750817 : Blo 1937435 70750817 := bstep (se 2 (by rfl) ⟨26531556, by rfl⟩ : syracuseStep 70750817 = 53063113) B53063113
theorem B47167211 : Blo 1937435 47167211 := bstep (se 1 (by rfl) ⟨35375408, by rfl⟩ : syracuseStep 47167211 = 70750817) B70750817
theorem B31444807 : Blo 1937435 31444807 := bstep (se 1 (by rfl) ⟨23583605, by rfl⟩ : syracuseStep 31444807 = 47167211) B47167211
theorem B41926409 : Blo 1937435 41926409 := bstep (se 2 (by rfl) ⟨15722403, by rfl⟩ : syracuseStep 41926409 = 31444807) B31444807
theorem B27950939 : Blo 1937435 27950939 := bstep (se 1 (by rfl) ⟨20963204, by rfl⟩ : syracuseStep 27950939 = 41926409) B41926409
theorem B18633959 : Blo 1937435 18633959 := bstep (se 1 (by rfl) ⟨13975469, by rfl⟩ : syracuseStep 18633959 = 27950939) B27950939
theorem B12422639 : Blo 1937435 12422639 := bstep (se 1 (by rfl) ⟨9316979, by rfl⟩ : syracuseStep 12422639 = 18633959) B18633959
theorem B8281759 : Blo 1937435 8281759 := bstep (se 1 (by rfl) ⟨6211319, by rfl⟩ : syracuseStep 8281759 = 12422639) B12422639
theorem B11042345 : Blo 1937435 11042345 := bstep (se 2 (by rfl) ⟨4140879, by rfl⟩ : syracuseStep 11042345 = 8281759) B8281759
theorem B7361563 : Blo 1937435 7361563 := bstep (se 1 (by rfl) ⟨5521172, by rfl⟩ : syracuseStep 7361563 = 11042345) B11042345
theorem B9815417 : Blo 1937435 9815417 := bstep (se 2 (by rfl) ⟨3680781, by rfl⟩ : syracuseStep 9815417 = 7361563) B7361563
theorem B6543611 : Blo 1937435 6543611 := bstep (se 1 (by rfl) ⟨4907708, by rfl⟩ : syracuseStep 6543611 = 9815417) B9815417
theorem B4362407 : Blo 1937435 4362407 := bstep (se 1 (by rfl) ⟨3271805, by rfl⟩ : syracuseStep 4362407 = 6543611) B6543611
theorem B2908271 : Blo 1937435 2908271 := bstep (se 1 (by rfl) ⟨2181203, by rfl⟩ : syracuseStep 2908271 = 4362407) B4362407
theorem B1938847 : Blo 1937435 1938847 := bstep (se 1 (by rfl) ⟨1454135, by rfl⟩ : syracuseStep 1938847 = 2908271) B2908271
theorem B2908277 : Blo 1937435 2908277 := bbase (se 5 (by rfl) ⟨136325, by rfl⟩ : syracuseStep 2908277 = 272651) (by norm_num)
theorem B1938851 : Blo 1937435 1938851 := bstep (se 1 (by rfl) ⟨1454138, by rfl⟩ : syracuseStep 1938851 = 2908277) B2908277
theorem B3680797 : Blo 1937435 3680797 := bbase (se 3 (by rfl) ⟨690149, by rfl⟩ : syracuseStep 3680797 = 1380299) (by norm_num)
theorem B4907729 : Blo 1937435 4907729 := bstep (se 2 (by rfl) ⟨1840398, by rfl⟩ : syracuseStep 4907729 = 3680797) B3680797
theorem B3271819 : Blo 1937435 3271819 := bstep (se 1 (by rfl) ⟨2453864, by rfl⟩ : syracuseStep 3271819 = 4907729) B4907729
theorem B4362425 : Blo 1937435 4362425 := bstep (se 2 (by rfl) ⟨1635909, by rfl⟩ : syracuseStep 4362425 = 3271819) B3271819
theorem B2908283 : Blo 1937435 2908283 := bstep (se 1 (by rfl) ⟨2181212, by rfl⟩ : syracuseStep 2908283 = 4362425) B4362425
theorem B1938855 : Blo 1937435 1938855 := bstep (se 1 (by rfl) ⟨1454141, by rfl⟩ : syracuseStep 1938855 = 2908283) B2908283
theorem B2181217 : Blo 1937435 2181217 := bbase (se 2 (by rfl) ⟨817956, by rfl⟩ : syracuseStep 2181217 = 1635913) (by norm_num)
theorem B2908289 : Blo 1937435 2908289 := bstep (se 2 (by rfl) ⟨1090608, by rfl⟩ : syracuseStep 2908289 = 2181217) B2181217
theorem B1938859 : Blo 1937435 1938859 := bstep (se 1 (by rfl) ⟨1454144, by rfl⟩ : syracuseStep 1938859 = 2908289) B2908289
theorem B4907749 : Blo 1937435 4907749 := bbase (se 4 (by rfl) ⟨460101, by rfl⟩ : syracuseStep 4907749 = 920203) (by norm_num)
theorem B6543665 : Blo 1937435 6543665 := bstep (se 2 (by rfl) ⟨2453874, by rfl⟩ : syracuseStep 6543665 = 4907749) B4907749
theorem B4362443 : Blo 1937435 4362443 := bstep (se 1 (by rfl) ⟨3271832, by rfl⟩ : syracuseStep 4362443 = 6543665) B6543665
theorem B2908295 : Blo 1937435 2908295 := bstep (se 1 (by rfl) ⟨2181221, by rfl⟩ : syracuseStep 2908295 = 4362443) B4362443
theorem B1938863 : Blo 1937435 1938863 := bstep (se 1 (by rfl) ⟨1454147, by rfl⟩ : syracuseStep 1938863 = 2908295) B2908295
theorem B2908301 : Blo 1937435 2908301 := bbase (se 3 (by rfl) ⟨545306, by rfl⟩ : syracuseStep 2908301 = 1090613) (by norm_num)
theorem B1938867 : Blo 1937435 1938867 := bstep (se 1 (by rfl) ⟨1454150, by rfl⟩ : syracuseStep 1938867 = 2908301) B2908301
theorem B4362461 : Blo 1937435 4362461 := bbase (se 3 (by rfl) ⟨817961, by rfl⟩ : syracuseStep 4362461 = 1635923) (by norm_num)
theorem B2908307 : Blo 1937435 2908307 := bstep (se 1 (by rfl) ⟨2181230, by rfl⟩ : syracuseStep 2908307 = 4362461) B4362461
theorem B1938871 : Blo 1937435 1938871 := bstep (se 1 (by rfl) ⟨1454153, by rfl⟩ : syracuseStep 1938871 = 2908307) B2908307
theorem B3271853 : Blo 1937435 3271853 := bbase (se 3 (by rfl) ⟨613472, by rfl⟩ : syracuseStep 3271853 = 1226945) (by norm_num)
theorem B2181235 : Blo 1937435 2181235 := bstep (se 1 (by rfl) ⟨1635926, by rfl⟩ : syracuseStep 2181235 = 3271853) B3271853
theorem B2908313 : Blo 1937435 2908313 := bstep (se 2 (by rfl) ⟨1090617, by rfl⟩ : syracuseStep 2908313 = 2181235) B2181235
theorem B1938875 : Blo 1937435 1938875 := bstep (se 1 (by rfl) ⟨1454156, by rfl⟩ : syracuseStep 1938875 = 2908313) B2908313
theorem B16789781 : Blo 1937435 16789781 := bbase (se 6 (by rfl) ⟨393510, by rfl⟩ : syracuseStep 16789781 = 787021) (by norm_num)
theorem B11193187 : Blo 1937435 11193187 := bstep (se 1 (by rfl) ⟨8394890, by rfl⟩ : syracuseStep 11193187 = 16789781) B16789781
theorem B14924249 : Blo 1937435 14924249 := bstep (se 2 (by rfl) ⟨5596593, by rfl⟩ : syracuseStep 14924249 = 11193187) B11193187
theorem B9949499 : Blo 1937435 9949499 := bstep (se 1 (by rfl) ⟨7462124, by rfl⟩ : syracuseStep 9949499 = 14924249) B14924249
theorem B6632999 : Blo 1937435 6632999 := bstep (se 1 (by rfl) ⟨4974749, by rfl⟩ : syracuseStep 6632999 = 9949499) B9949499
theorem B4421999 : Blo 1937435 4421999 := bstep (se 1 (by rfl) ⟨3316499, by rfl⟩ : syracuseStep 4421999 = 6632999) B6632999
theorem B11791997 : Blo 1937435 11791997 := bstep (se 3 (by rfl) ⟨2210999, by rfl⟩ : syracuseStep 11791997 = 4421999) B4421999
theorem B7861331 : Blo 1937435 7861331 := bstep (se 1 (by rfl) ⟨5895998, by rfl⟩ : syracuseStep 7861331 = 11791997) B11791997
theorem B20963549 : Blo 1937435 20963549 := bstep (se 3 (by rfl) ⟨3930665, by rfl⟩ : syracuseStep 20963549 = 7861331) B7861331
theorem B55902797 : Blo 1937435 55902797 := bstep (se 3 (by rfl) ⟨10481774, by rfl⟩ : syracuseStep 55902797 = 20963549) B20963549
theorem B37268531 : Blo 1937435 37268531 := bstep (se 1 (by rfl) ⟨27951398, by rfl⟩ : syracuseStep 37268531 = 55902797) B55902797
theorem B24845687 : Blo 1937435 24845687 := bstep (se 1 (by rfl) ⟨18634265, by rfl⟩ : syracuseStep 24845687 = 37268531) B37268531
theorem B16563791 : Blo 1937435 16563791 := bstep (se 1 (by rfl) ⟨12422843, by rfl⟩ : syracuseStep 16563791 = 24845687) B24845687
theorem B11042527 : Blo 1937435 11042527 := bstep (se 1 (by rfl) ⟨8281895, by rfl⟩ : syracuseStep 11042527 = 16563791) B16563791
theorem B14723369 : Blo 1937435 14723369 := bstep (se 2 (by rfl) ⟨5521263, by rfl⟩ : syracuseStep 14723369 = 11042527) B11042527
theorem B9815579 : Blo 1937435 9815579 := bstep (se 1 (by rfl) ⟨7361684, by rfl⟩ : syracuseStep 9815579 = 14723369) B14723369
theorem B6543719 : Blo 1937435 6543719 := bstep (se 1 (by rfl) ⟨4907789, by rfl⟩ : syracuseStep 6543719 = 9815579) B9815579
theorem B4362479 : Blo 1937435 4362479 := bstep (se 1 (by rfl) ⟨3271859, by rfl⟩ : syracuseStep 4362479 = 6543719) B6543719
theorem B2908319 : Blo 1937435 2908319 := bstep (se 1 (by rfl) ⟨2181239, by rfl⟩ : syracuseStep 2908319 = 4362479) B4362479
theorem B1938879 : Blo 1937435 1938879 := bstep (se 1 (by rfl) ⟨1454159, by rfl⟩ : syracuseStep 1938879 = 2908319) B2908319
theorem B2908325 : Blo 1937435 2908325 := bbase (se 4 (by rfl) ⟨272655, by rfl⟩ : syracuseStep 2908325 = 545311) (by norm_num)
theorem B1938883 : Blo 1937435 1938883 := bstep (se 1 (by rfl) ⟨1454162, by rfl⟩ : syracuseStep 1938883 = 2908325) B2908325
theorem B2453905 : Blo 1937435 2453905 := bbase (se 2 (by rfl) ⟨920214, by rfl⟩ : syracuseStep 2453905 = 1840429) (by norm_num)
theorem B3271873 : Blo 1937435 3271873 := bstep (se 2 (by rfl) ⟨1226952, by rfl⟩ : syracuseStep 3271873 = 2453905) B2453905
theorem B4362497 : Blo 1937435 4362497 := bstep (se 2 (by rfl) ⟨1635936, by rfl⟩ : syracuseStep 4362497 = 3271873) B3271873
theorem B2908331 : Blo 1937435 2908331 := bstep (se 1 (by rfl) ⟨2181248, by rfl⟩ : syracuseStep 2908331 = 4362497) B4362497
theorem B1938887 : Blo 1937435 1938887 := bstep (se 1 (by rfl) ⟨1454165, by rfl⟩ : syracuseStep 1938887 = 2908331) B2908331
theorem B2181253 : Blo 1937435 2181253 := bbase (se 4 (by rfl) ⟨204492, by rfl⟩ : syracuseStep 2181253 = 408985) (by norm_num)
theorem B2908337 : Blo 1937435 2908337 := bstep (se 2 (by rfl) ⟨1090626, by rfl⟩ : syracuseStep 2908337 = 2181253) B2181253
theorem B1938891 : Blo 1937435 1938891 := bstep (se 1 (by rfl) ⟨1454168, by rfl⟩ : syracuseStep 1938891 = 2908337) B2908337
theorem B5240933 : Blo 1937435 5240933 := bbase (se 4 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 5240933 = 982675) (by norm_num)
theorem B3493955 : Blo 1937435 3493955 := bstep (se 1 (by rfl) ⟨2620466, by rfl⟩ : syracuseStep 3493955 = 5240933) B5240933
theorem B9317213 : Blo 1937435 9317213 := bstep (se 3 (by rfl) ⟨1746977, by rfl⟩ : syracuseStep 9317213 = 3493955) B3493955
theorem B6211475 : Blo 1937435 6211475 := bstep (se 1 (by rfl) ⟨4658606, by rfl⟩ : syracuseStep 6211475 = 9317213) B9317213
theorem B4140983 : Blo 1937435 4140983 := bstep (se 1 (by rfl) ⟨3105737, by rfl⟩ : syracuseStep 4140983 = 6211475) B6211475
theorem B2760655 : Blo 1937435 2760655 := bstep (se 1 (by rfl) ⟨2070491, by rfl⟩ : syracuseStep 2760655 = 4140983) B4140983
theorem B3680873 : Blo 1937435 3680873 := bstep (se 2 (by rfl) ⟨1380327, by rfl⟩ : syracuseStep 3680873 = 2760655) B2760655
theorem B2453915 : Blo 1937435 2453915 := bstep (se 1 (by rfl) ⟨1840436, by rfl⟩ : syracuseStep 2453915 = 3680873) B3680873
theorem B6543773 : Blo 1937435 6543773 := bstep (se 3 (by rfl) ⟨1226957, by rfl⟩ : syracuseStep 6543773 = 2453915) B2453915
theorem B4362515 : Blo 1937435 4362515 := bstep (se 1 (by rfl) ⟨3271886, by rfl⟩ : syracuseStep 4362515 = 6543773) B6543773
theorem B2908343 : Blo 1937435 2908343 := bstep (se 1 (by rfl) ⟨2181257, by rfl⟩ : syracuseStep 2908343 = 4362515) B4362515
theorem B1938895 : Blo 1937435 1938895 := bstep (se 1 (by rfl) ⟨1454171, by rfl⟩ : syracuseStep 1938895 = 2908343) B2908343
theorem B2908349 : Blo 1937435 2908349 := bbase (se 3 (by rfl) ⟨545315, by rfl⟩ : syracuseStep 2908349 = 1090631) (by norm_num)
theorem B1938899 : Blo 1937435 1938899 := bstep (se 1 (by rfl) ⟨1454174, by rfl⟩ : syracuseStep 1938899 = 2908349) B2908349
theorem B4362533 : Blo 1937435 4362533 := bbase (se 4 (by rfl) ⟨408987, by rfl⟩ : syracuseStep 4362533 = 817975) (by norm_num)
theorem B2908355 : Blo 1937435 2908355 := bstep (se 1 (by rfl) ⟨2181266, by rfl⟩ : syracuseStep 2908355 = 4362533) B4362533
theorem B1938903 : Blo 1937435 1938903 := bstep (se 1 (by rfl) ⟨1454177, by rfl⟩ : syracuseStep 1938903 = 2908355) B2908355
theorem B4907861 : Blo 1937435 4907861 := bbase (se 9 (by rfl) ⟨14378, by rfl⟩ : syracuseStep 4907861 = 28757) (by norm_num)
theorem B3271907 : Blo 1937435 3271907 := bstep (se 1 (by rfl) ⟨2453930, by rfl⟩ : syracuseStep 3271907 = 4907861) B4907861
theorem B2181271 : Blo 1937435 2181271 := bstep (se 1 (by rfl) ⟨1635953, by rfl⟩ : syracuseStep 2181271 = 3271907) B3271907
theorem B2908361 : Blo 1937435 2908361 := bstep (se 2 (by rfl) ⟨1090635, by rfl⟩ : syracuseStep 2908361 = 2181271) B2181271
theorem B1938907 : Blo 1937435 1938907 := bstep (se 1 (by rfl) ⟨1454180, by rfl⟩ : syracuseStep 1938907 = 2908361) B2908361
theorem B6211525 : Blo 1937435 6211525 := bbase (se 4 (by rfl) ⟨582330, by rfl⟩ : syracuseStep 6211525 = 1164661) (by norm_num)
theorem B8282033 : Blo 1937435 8282033 := bstep (se 2 (by rfl) ⟨3105762, by rfl⟩ : syracuseStep 8282033 = 6211525) B6211525
theorem B5521355 : Blo 1937435 5521355 := bstep (se 1 (by rfl) ⟨4141016, by rfl⟩ : syracuseStep 5521355 = 8282033) B8282033
theorem B3680903 : Blo 1937435 3680903 := bstep (se 1 (by rfl) ⟨2760677, by rfl⟩ : syracuseStep 3680903 = 5521355) B5521355
theorem B9815741 : Blo 1937435 9815741 := bstep (se 3 (by rfl) ⟨1840451, by rfl⟩ : syracuseStep 9815741 = 3680903) B3680903
theorem B6543827 : Blo 1937435 6543827 := bstep (se 1 (by rfl) ⟨4907870, by rfl⟩ : syracuseStep 6543827 = 9815741) B9815741
theorem B4362551 : Blo 1937435 4362551 := bstep (se 1 (by rfl) ⟨3271913, by rfl⟩ : syracuseStep 4362551 = 6543827) B6543827
theorem B2908367 : Blo 1937435 2908367 := bstep (se 1 (by rfl) ⟨2181275, by rfl⟩ : syracuseStep 2908367 = 4362551) B4362551
theorem B1938911 : Blo 1937435 1938911 := bstep (se 1 (by rfl) ⟨1454183, by rfl⟩ : syracuseStep 1938911 = 2908367) B2908367
theorem B2908373 : Blo 1937435 2908373 := bbase (se 7 (by rfl) ⟨34082, by rfl⟩ : syracuseStep 2908373 = 68165) (by norm_num)
theorem B1938915 : Blo 1937435 1938915 := bstep (se 1 (by rfl) ⟨1454186, by rfl⟩ : syracuseStep 1938915 = 2908373) B2908373
theorem B2070517 : Blo 1937435 2070517 := bbase (se 5 (by rfl) ⟨97055, by rfl⟩ : syracuseStep 2070517 = 194111) (by norm_num)
theorem B2760689 : Blo 1937435 2760689 := bstep (se 2 (by rfl) ⟨1035258, by rfl⟩ : syracuseStep 2760689 = 2070517) B2070517
theorem B7361837 : Blo 1937435 7361837 := bstep (se 3 (by rfl) ⟨1380344, by rfl⟩ : syracuseStep 7361837 = 2760689) B2760689
theorem B4907891 : Blo 1937435 4907891 := bstep (se 1 (by rfl) ⟨3680918, by rfl⟩ : syracuseStep 4907891 = 7361837) B7361837
theorem B3271927 : Blo 1937435 3271927 := bstep (se 1 (by rfl) ⟨2453945, by rfl⟩ : syracuseStep 3271927 = 4907891) B4907891
theorem B4362569 : Blo 1937435 4362569 := bstep (se 2 (by rfl) ⟨1635963, by rfl⟩ : syracuseStep 4362569 = 3271927) B3271927
theorem B2908379 : Blo 1937435 2908379 := bstep (se 1 (by rfl) ⟨2181284, by rfl⟩ : syracuseStep 2908379 = 4362569) B4362569
theorem B1938919 : Blo 1937435 1938919 := bstep (se 1 (by rfl) ⟨1454189, by rfl⟩ : syracuseStep 1938919 = 2908379) B2908379
theorem B2181289 : Blo 1937435 2181289 := bbase (se 2 (by rfl) ⟨817983, by rfl⟩ : syracuseStep 2181289 = 1635967) (by norm_num)
theorem B2908385 : Blo 1937435 2908385 := bstep (se 2 (by rfl) ⟨1090644, by rfl⟩ : syracuseStep 2908385 = 2181289) B2181289
theorem B1938923 : Blo 1937435 1938923 := bstep (se 1 (by rfl) ⟨1454192, by rfl⟩ : syracuseStep 1938923 = 2908385) B2908385
theorem B8282101 : Blo 1937435 8282101 := bbase (se 5 (by rfl) ⟨388223, by rfl⟩ : syracuseStep 8282101 = 776447) (by norm_num)
theorem B11042801 : Blo 1937435 11042801 := bstep (se 2 (by rfl) ⟨4141050, by rfl⟩ : syracuseStep 11042801 = 8282101) B8282101
theorem B7361867 : Blo 1937435 7361867 := bstep (se 1 (by rfl) ⟨5521400, by rfl⟩ : syracuseStep 7361867 = 11042801) B11042801
theorem B4907911 : Blo 1937435 4907911 := bstep (se 1 (by rfl) ⟨3680933, by rfl⟩ : syracuseStep 4907911 = 7361867) B7361867
theorem B6543881 : Blo 1937435 6543881 := bstep (se 2 (by rfl) ⟨2453955, by rfl⟩ : syracuseStep 6543881 = 4907911) B4907911
theorem B4362587 : Blo 1937435 4362587 := bstep (se 1 (by rfl) ⟨3271940, by rfl⟩ : syracuseStep 4362587 = 6543881) B6543881
theorem B2908391 : Blo 1937435 2908391 := bstep (se 1 (by rfl) ⟨2181293, by rfl⟩ : syracuseStep 2908391 = 4362587) B4362587
theorem B1938927 : Blo 1937435 1938927 := bstep (se 1 (by rfl) ⟨1454195, by rfl⟩ : syracuseStep 1938927 = 2908391) B2908391
theorem B2908397 : Blo 1937435 2908397 := bbase (se 3 (by rfl) ⟨545324, by rfl⟩ : syracuseStep 2908397 = 1090649) (by norm_num)
theorem B1938931 : Blo 1937435 1938931 := bstep (se 1 (by rfl) ⟨1454198, by rfl⟩ : syracuseStep 1938931 = 2908397) B2908397
theorem B4362605 : Blo 1937435 4362605 := bbase (se 3 (by rfl) ⟨817988, by rfl⟩ : syracuseStep 4362605 = 1635977) (by norm_num)
theorem B2908403 : Blo 1937435 2908403 := bstep (se 1 (by rfl) ⟨2181302, by rfl⟩ : syracuseStep 2908403 = 4362605) B4362605
theorem B1938935 : Blo 1937435 1938935 := bstep (se 1 (by rfl) ⟨1454201, by rfl⟩ : syracuseStep 1938935 = 2908403) B2908403
theorem B3680957 : Blo 1937435 3680957 := bbase (se 3 (by rfl) ⟨690179, by rfl⟩ : syracuseStep 3680957 = 1380359) (by norm_num)
theorem B2453971 : Blo 1937435 2453971 := bstep (se 1 (by rfl) ⟨1840478, by rfl⟩ : syracuseStep 2453971 = 3680957) B3680957
theorem B3271961 : Blo 1937435 3271961 := bstep (se 2 (by rfl) ⟨1226985, by rfl⟩ : syracuseStep 3271961 = 2453971) B2453971
theorem B2181307 : Blo 1937435 2181307 := bstep (se 1 (by rfl) ⟨1635980, by rfl⟩ : syracuseStep 2181307 = 3271961) B3271961
theorem B2908409 : Blo 1937435 2908409 := bstep (se 2 (by rfl) ⟨1090653, by rfl⟩ : syracuseStep 2908409 = 2181307) B2181307
theorem B1938939 : Blo 1937435 1938939 := bstep (se 1 (by rfl) ⟨1454204, by rfl⟩ : syracuseStep 1938939 = 2908409) B2908409
theorem B49693013 : Blo 1937435 49693013 := bbase (se 10 (by rfl) ⟨72792, by rfl⟩ : syracuseStep 49693013 = 145585) (by norm_num)
theorem B33128675 : Blo 1937435 33128675 := bstep (se 1 (by rfl) ⟨24846506, by rfl⟩ : syracuseStep 33128675 = 49693013) B49693013
theorem B22085783 : Blo 1937435 22085783 := bstep (se 1 (by rfl) ⟨16564337, by rfl⟩ : syracuseStep 22085783 = 33128675) B33128675
theorem B14723855 : Blo 1937435 14723855 := bstep (se 1 (by rfl) ⟨11042891, by rfl⟩ : syracuseStep 14723855 = 22085783) B22085783
theorem B9815903 : Blo 1937435 9815903 := bstep (se 1 (by rfl) ⟨7361927, by rfl⟩ : syracuseStep 9815903 = 14723855) B14723855
theorem B6543935 : Blo 1937435 6543935 := bstep (se 1 (by rfl) ⟨4907951, by rfl⟩ : syracuseStep 6543935 = 9815903) B9815903
theorem B4362623 : Blo 1937435 4362623 := bstep (se 1 (by rfl) ⟨3271967, by rfl⟩ : syracuseStep 4362623 = 6543935) B6543935
theorem B2908415 : Blo 1937435 2908415 := bstep (se 1 (by rfl) ⟨2181311, by rfl⟩ : syracuseStep 2908415 = 4362623) B4362623
theorem B1938943 : Blo 1937435 1938943 := bstep (se 1 (by rfl) ⟨1454207, by rfl⟩ : syracuseStep 1938943 = 2908415) B2908415
theorem B2908421 : Blo 1937435 2908421 := bbase (se 4 (by rfl) ⟨272664, by rfl⟩ : syracuseStep 2908421 = 545329) (by norm_num)
theorem B1938947 : Blo 1937435 1938947 := bstep (se 1 (by rfl) ⟨1454210, by rfl⟩ : syracuseStep 1938947 = 2908421) B2908421
theorem B3271981 : Blo 1937435 3271981 := bbase (se 3 (by rfl) ⟨613496, by rfl⟩ : syracuseStep 3271981 = 1226993) (by norm_num)
theorem B4362641 : Blo 1937435 4362641 := bstep (se 2 (by rfl) ⟨1635990, by rfl⟩ : syracuseStep 4362641 = 3271981) B3271981
theorem B2908427 : Blo 1937435 2908427 := bstep (se 1 (by rfl) ⟨2181320, by rfl⟩ : syracuseStep 2908427 = 4362641) B4362641
theorem B1938951 : Blo 1937435 1938951 := bstep (se 1 (by rfl) ⟨1454213, by rfl⟩ : syracuseStep 1938951 = 2908427) B2908427
theorem B2181325 : Blo 1937435 2181325 := bbase (se 3 (by rfl) ⟨408998, by rfl⟩ : syracuseStep 2181325 = 817997) (by norm_num)
theorem B2908433 : Blo 1937435 2908433 := bstep (se 2 (by rfl) ⟨1090662, by rfl⟩ : syracuseStep 2908433 = 2181325) B2181325
theorem B1938955 : Blo 1937435 1938955 := bstep (se 1 (by rfl) ⟨1454216, by rfl⟩ : syracuseStep 1938955 = 2908433) B2908433
theorem B6543989 : Blo 1937435 6543989 := bbase (se 5 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 6543989 = 613499) (by norm_num)
theorem B4362659 : Blo 1937435 4362659 := bstep (se 1 (by rfl) ⟨3271994, by rfl⟩ : syracuseStep 4362659 = 6543989) B6543989
theorem B2908439 : Blo 1937435 2908439 := bstep (se 1 (by rfl) ⟨2181329, by rfl⟩ : syracuseStep 2908439 = 4362659) B4362659
theorem B1938959 : Blo 1937435 1938959 := bstep (se 1 (by rfl) ⟨1454219, by rfl⟩ : syracuseStep 1938959 = 2908439) B2908439
theorem B2908445 : Blo 1937435 2908445 := bbase (se 3 (by rfl) ⟨545333, by rfl⟩ : syracuseStep 2908445 = 1090667) (by norm_num)
theorem B1938963 : Blo 1937435 1938963 := bstep (se 1 (by rfl) ⟨1454222, by rfl⟩ : syracuseStep 1938963 = 2908445) B2908445
theorem B4362677 : Blo 1937435 4362677 := bbase (se 5 (by rfl) ⟨204500, by rfl⟩ : syracuseStep 4362677 = 409001) (by norm_num)
theorem B2908451 : Blo 1937435 2908451 := bstep (se 1 (by rfl) ⟨2181338, by rfl⟩ : syracuseStep 2908451 = 4362677) B4362677
theorem B1938967 : Blo 1937435 1938967 := bstep (se 1 (by rfl) ⟨1454225, by rfl⟩ : syracuseStep 1938967 = 2908451) B2908451
theorem B4658789 : Blo 1937435 4658789 := bbase (se 4 (by rfl) ⟨436761, by rfl⟩ : syracuseStep 4658789 = 873523) (by norm_num)
theorem B3105859 : Blo 1937435 3105859 := bstep (se 1 (by rfl) ⟨2329394, by rfl⟩ : syracuseStep 3105859 = 4658789) B4658789
theorem B4141145 : Blo 1937435 4141145 := bstep (se 2 (by rfl) ⟨1552929, by rfl⟩ : syracuseStep 4141145 = 3105859) B3105859
theorem B11043053 : Blo 1937435 11043053 := bstep (se 3 (by rfl) ⟨2070572, by rfl⟩ : syracuseStep 11043053 = 4141145) B4141145
theorem B7362035 : Blo 1937435 7362035 := bstep (se 1 (by rfl) ⟨5521526, by rfl⟩ : syracuseStep 7362035 = 11043053) B11043053
theorem B4908023 : Blo 1937435 4908023 := bstep (se 1 (by rfl) ⟨3681017, by rfl⟩ : syracuseStep 4908023 = 7362035) B7362035
theorem B3272015 : Blo 1937435 3272015 := bstep (se 1 (by rfl) ⟨2454011, by rfl⟩ : syracuseStep 3272015 = 4908023) B4908023
theorem B2181343 : Blo 1937435 2181343 := bstep (se 1 (by rfl) ⟨1636007, by rfl⟩ : syracuseStep 2181343 = 3272015) B3272015
theorem B2908457 : Blo 1937435 2908457 := bstep (se 2 (by rfl) ⟨1090671, by rfl⟩ : syracuseStep 2908457 = 2181343) B2181343
theorem B1938971 : Blo 1937435 1938971 := bstep (se 1 (by rfl) ⟨1454228, by rfl⟩ : syracuseStep 1938971 = 2908457) B2908457
theorem B4422221 : Blo 1937435 4422221 := bbase (se 3 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 4422221 = 1658333) (by norm_num)
theorem B2948147 : Blo 1937435 2948147 := bstep (se 1 (by rfl) ⟨2211110, by rfl⟩ : syracuseStep 2948147 = 4422221) B4422221
theorem B1965431 : Blo 1937435 1965431 := bstep (se 1 (by rfl) ⟨1474073, by rfl⟩ : syracuseStep 1965431 = 2948147) B2948147
theorem B5241149 : Blo 1937435 5241149 := bstep (se 3 (by rfl) ⟨982715, by rfl⟩ : syracuseStep 5241149 = 1965431) B1965431
theorem B3494099 : Blo 1937435 3494099 := bstep (se 1 (by rfl) ⟨2620574, by rfl⟩ : syracuseStep 3494099 = 5241149) B5241149
theorem B2329399 : Blo 1937435 2329399 := bstep (se 1 (by rfl) ⟨1747049, by rfl⟩ : syracuseStep 2329399 = 3494099) B3494099
theorem B3105865 : Blo 1937435 3105865 := bstep (se 2 (by rfl) ⟨1164699, by rfl⟩ : syracuseStep 3105865 = 2329399) B2329399
theorem B4141153 : Blo 1937435 4141153 := bstep (se 2 (by rfl) ⟨1552932, by rfl⟩ : syracuseStep 4141153 = 3105865) B3105865
theorem B5521537 : Blo 1937435 5521537 := bstep (se 2 (by rfl) ⟨2070576, by rfl⟩ : syracuseStep 5521537 = 4141153) B4141153
theorem B7362049 : Blo 1937435 7362049 := bstep (se 2 (by rfl) ⟨2760768, by rfl⟩ : syracuseStep 7362049 = 5521537) B5521537
theorem B9816065 : Blo 1937435 9816065 := bstep (se 2 (by rfl) ⟨3681024, by rfl⟩ : syracuseStep 9816065 = 7362049) B7362049
theorem B6544043 : Blo 1937435 6544043 := bstep (se 1 (by rfl) ⟨4908032, by rfl⟩ : syracuseStep 6544043 = 9816065) B9816065
theorem B4362695 : Blo 1937435 4362695 := bstep (se 1 (by rfl) ⟨3272021, by rfl⟩ : syracuseStep 4362695 = 6544043) B6544043
theorem B2908463 : Blo 1937435 2908463 := bstep (se 1 (by rfl) ⟨2181347, by rfl⟩ : syracuseStep 2908463 = 4362695) B4362695
theorem B1938975 : Blo 1937435 1938975 := bstep (se 1 (by rfl) ⟨1454231, by rfl⟩ : syracuseStep 1938975 = 2908463) B2908463
theorem B2908469 : Blo 1937435 2908469 := bbase (se 5 (by rfl) ⟨136334, by rfl⟩ : syracuseStep 2908469 = 272669) (by norm_num)
theorem B1938979 : Blo 1937435 1938979 := bstep (se 1 (by rfl) ⟨1454234, by rfl⟩ : syracuseStep 1938979 = 2908469) B2908469
theorem B4908053 : Blo 1937435 4908053 := bbase (se 6 (by rfl) ⟨115032, by rfl⟩ : syracuseStep 4908053 = 230065) (by norm_num)
theorem B3272035 : Blo 1937435 3272035 := bstep (se 1 (by rfl) ⟨2454026, by rfl⟩ : syracuseStep 3272035 = 4908053) B4908053
theorem B4362713 : Blo 1937435 4362713 := bstep (se 2 (by rfl) ⟨1636017, by rfl⟩ : syracuseStep 4362713 = 3272035) B3272035
theorem B2908475 : Blo 1937435 2908475 := bstep (se 1 (by rfl) ⟨2181356, by rfl⟩ : syracuseStep 2908475 = 4362713) B4362713
theorem B1938983 : Blo 1937435 1938983 := bstep (se 1 (by rfl) ⟨1454237, by rfl⟩ : syracuseStep 1938983 = 2908475) B2908475
theorem B2181361 : Blo 1937435 2181361 := bbase (se 2 (by rfl) ⟨818010, by rfl⟩ : syracuseStep 2181361 = 1636021) (by norm_num)
theorem B2908481 : Blo 1937435 2908481 := bstep (se 2 (by rfl) ⟨1090680, by rfl⟩ : syracuseStep 2908481 = 2181361) B2181361
theorem B1938987 : Blo 1937435 1938987 := bstep (se 1 (by rfl) ⟨1454240, by rfl⟩ : syracuseStep 1938987 = 2908481) B2908481
theorem B4786829 : Blo 1937435 4786829 := bbase (se 3 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 4786829 = 1795061) (by norm_num)
theorem B204238037 : Blo 1937435 204238037 := bstep (se 7 (by rfl) ⟨2393414, by rfl⟩ : syracuseStep 204238037 = 4786829) B4786829
theorem B136158691 : Blo 1937435 136158691 := bstep (se 1 (by rfl) ⟨102119018, by rfl⟩ : syracuseStep 136158691 = 204238037) B204238037
theorem B181544921 : Blo 1937435 181544921 := bstep (se 2 (by rfl) ⟨68079345, by rfl⟩ : syracuseStep 181544921 = 136158691) B136158691
theorem B121029947 : Blo 1937435 121029947 := bstep (se 1 (by rfl) ⟨90772460, by rfl⟩ : syracuseStep 121029947 = 181544921) B181544921
theorem B80686631 : Blo 1937435 80686631 := bstep (se 1 (by rfl) ⟨60514973, by rfl⟩ : syracuseStep 80686631 = 121029947) B121029947
theorem B53791087 : Blo 1937435 53791087 := bstep (se 1 (by rfl) ⟨40343315, by rfl⟩ : syracuseStep 53791087 = 80686631) B80686631
theorem B71721449 : Blo 1937435 71721449 := bstep (se 2 (by rfl) ⟨26895543, by rfl⟩ : syracuseStep 71721449 = 53791087) B53791087
theorem B47814299 : Blo 1937435 47814299 := bstep (se 1 (by rfl) ⟨35860724, by rfl⟩ : syracuseStep 47814299 = 71721449) B71721449
theorem B31876199 : Blo 1937435 31876199 := bstep (se 1 (by rfl) ⟨23907149, by rfl⟩ : syracuseStep 31876199 = 47814299) B47814299
theorem B21250799 : Blo 1937435 21250799 := bstep (se 1 (by rfl) ⟨15938099, by rfl⟩ : syracuseStep 21250799 = 31876199) B31876199
theorem B14167199 : Blo 1937435 14167199 := bstep (se 1 (by rfl) ⟨10625399, by rfl⟩ : syracuseStep 14167199 = 21250799) B21250799
theorem B9444799 : Blo 1937435 9444799 := bstep (se 1 (by rfl) ⟨7083599, by rfl⟩ : syracuseStep 9444799 = 14167199) B14167199
theorem B12593065 : Blo 1937435 12593065 := bstep (se 2 (by rfl) ⟨4722399, by rfl⟩ : syracuseStep 12593065 = 9444799) B9444799
theorem B16790753 : Blo 1937435 16790753 := bstep (se 2 (by rfl) ⟨6296532, by rfl⟩ : syracuseStep 16790753 = 12593065) B12593065
theorem B44775341 : Blo 1937435 44775341 := bstep (se 3 (by rfl) ⟨8395376, by rfl⟩ : syracuseStep 44775341 = 16790753) B16790753
theorem B29850227 : Blo 1937435 29850227 := bstep (se 1 (by rfl) ⟨22387670, by rfl⟩ : syracuseStep 29850227 = 44775341) B44775341
theorem B19900151 : Blo 1937435 19900151 := bstep (se 1 (by rfl) ⟨14925113, by rfl⟩ : syracuseStep 19900151 = 29850227) B29850227
theorem B13266767 : Blo 1937435 13266767 := bstep (se 1 (by rfl) ⟨9950075, by rfl⟩ : syracuseStep 13266767 = 19900151) B19900151
theorem B8844511 : Blo 1937435 8844511 := bstep (se 1 (by rfl) ⟨6633383, by rfl⟩ : syracuseStep 8844511 = 13266767) B13266767
theorem B11792681 : Blo 1937435 11792681 := bstep (se 2 (by rfl) ⟨4422255, by rfl⟩ : syracuseStep 11792681 = 8844511) B8844511
theorem B7861787 : Blo 1937435 7861787 := bstep (se 1 (by rfl) ⟨5896340, by rfl⟩ : syracuseStep 7861787 = 11792681) B11792681
theorem B5241191 : Blo 1937435 5241191 := bstep (se 1 (by rfl) ⟨3930893, by rfl⟩ : syracuseStep 5241191 = 7861787) B7861787
theorem B13976509 : Blo 1937435 13976509 := bstep (se 3 (by rfl) ⟨2620595, by rfl⟩ : syracuseStep 13976509 = 5241191) B5241191
theorem B18635345 : Blo 1937435 18635345 := bstep (se 2 (by rfl) ⟨6988254, by rfl⟩ : syracuseStep 18635345 = 13976509) B13976509
theorem B12423563 : Blo 1937435 12423563 := bstep (se 1 (by rfl) ⟨9317672, by rfl⟩ : syracuseStep 12423563 = 18635345) B18635345
theorem B8282375 : Blo 1937435 8282375 := bstep (se 1 (by rfl) ⟨6211781, by rfl⟩ : syracuseStep 8282375 = 12423563) B12423563
theorem B5521583 : Blo 1937435 5521583 := bstep (se 1 (by rfl) ⟨4141187, by rfl⟩ : syracuseStep 5521583 = 8282375) B8282375
theorem B3681055 : Blo 1937435 3681055 := bstep (se 1 (by rfl) ⟨2760791, by rfl⟩ : syracuseStep 3681055 = 5521583) B5521583
theorem B4908073 : Blo 1937435 4908073 := bstep (se 2 (by rfl) ⟨1840527, by rfl⟩ : syracuseStep 4908073 = 3681055) B3681055
theorem B6544097 : Blo 1937435 6544097 := bstep (se 2 (by rfl) ⟨2454036, by rfl⟩ : syracuseStep 6544097 = 4908073) B4908073
theorem B4362731 : Blo 1937435 4362731 := bstep (se 1 (by rfl) ⟨3272048, by rfl⟩ : syracuseStep 4362731 = 6544097) B6544097
theorem B2908487 : Blo 1937435 2908487 := bstep (se 1 (by rfl) ⟨2181365, by rfl⟩ : syracuseStep 2908487 = 4362731) B4362731
theorem B1938991 : Blo 1937435 1938991 := bstep (se 1 (by rfl) ⟨1454243, by rfl⟩ : syracuseStep 1938991 = 2908487) B2908487
theorem B2908493 : Blo 1937435 2908493 := bbase (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) (by norm_num)
theorem B1938995 : Blo 1937435 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B4362749 : Blo 1937435 4362749 := bbase (se 3 (by rfl) ⟨818015, by rfl⟩ : syracuseStep 4362749 = 1636031) (by norm_num)
theorem B2908499 : Blo 1937435 2908499 := bstep (se 1 (by rfl) ⟨2181374, by rfl⟩ : syracuseStep 2908499 = 4362749) B4362749
theorem B1938999 : Blo 1937435 1938999 := bstep (se 1 (by rfl) ⟨1454249, by rfl⟩ : syracuseStep 1938999 = 2908499) B2908499
theorem B3272069 : Blo 1937435 3272069 := bbase (se 4 (by rfl) ⟨306756, by rfl⟩ : syracuseStep 3272069 = 613513) (by norm_num)
theorem B2181379 : Blo 1937435 2181379 := bstep (se 1 (by rfl) ⟨1636034, by rfl⟩ : syracuseStep 2181379 = 3272069) B3272069
theorem B2908505 : Blo 1937435 2908505 := bstep (se 2 (by rfl) ⟨1090689, by rfl⟩ : syracuseStep 2908505 = 2181379) B2181379
theorem B1939003 : Blo 1937435 1939003 := bstep (se 1 (by rfl) ⟨1454252, by rfl⟩ : syracuseStep 1939003 = 2908505) B2908505
theorem B14724341 : Blo 1937435 14724341 := bbase (se 5 (by rfl) ⟨690203, by rfl⟩ : syracuseStep 14724341 = 1380407) (by norm_num)
theorem B9816227 : Blo 1937435 9816227 := bstep (se 1 (by rfl) ⟨7362170, by rfl⟩ : syracuseStep 9816227 = 14724341) B14724341
theorem B6544151 : Blo 1937435 6544151 := bstep (se 1 (by rfl) ⟨4908113, by rfl⟩ : syracuseStep 6544151 = 9816227) B9816227
theorem B4362767 : Blo 1937435 4362767 := bstep (se 1 (by rfl) ⟨3272075, by rfl⟩ : syracuseStep 4362767 = 6544151) B6544151
theorem B2908511 : Blo 1937435 2908511 := bstep (se 1 (by rfl) ⟨2181383, by rfl⟩ : syracuseStep 2908511 = 4362767) B4362767
theorem B1939007 : Blo 1937435 1939007 := bstep (se 1 (by rfl) ⟨1454255, by rfl⟩ : syracuseStep 1939007 = 2908511) B2908511
theorem B2908517 : Blo 1937435 2908517 := bbase (se 4 (by rfl) ⟨272673, by rfl⟩ : syracuseStep 2908517 = 545347) (by norm_num)
theorem B1939011 : Blo 1937435 1939011 := bstep (se 1 (by rfl) ⟨1454258, by rfl⟩ : syracuseStep 1939011 = 2908517) B2908517
theorem B3681101 : Blo 1937435 3681101 := bbase (se 3 (by rfl) ⟨690206, by rfl⟩ : syracuseStep 3681101 = 1380413) (by norm_num)
theorem B2454067 : Blo 1937435 2454067 := bstep (se 1 (by rfl) ⟨1840550, by rfl⟩ : syracuseStep 2454067 = 3681101) B3681101
theorem B3272089 : Blo 1937435 3272089 := bstep (se 2 (by rfl) ⟨1227033, by rfl⟩ : syracuseStep 3272089 = 2454067) B2454067
theorem B4362785 : Blo 1937435 4362785 := bstep (se 2 (by rfl) ⟨1636044, by rfl⟩ : syracuseStep 4362785 = 3272089) B3272089
theorem B2908523 : Blo 1937435 2908523 := bstep (se 1 (by rfl) ⟨2181392, by rfl⟩ : syracuseStep 2908523 = 4362785) B4362785
theorem B1939015 : Blo 1937435 1939015 := bstep (se 1 (by rfl) ⟨1454261, by rfl⟩ : syracuseStep 1939015 = 2908523) B2908523
theorem B2181397 : Blo 1937435 2181397 := bbase (se 6 (by rfl) ⟨51126, by rfl⟩ : syracuseStep 2181397 = 102253) (by norm_num)
theorem B2908529 : Blo 1937435 2908529 := bstep (se 2 (by rfl) ⟨1090698, by rfl⟩ : syracuseStep 2908529 = 2181397) B2181397
theorem B1939019 : Blo 1937435 1939019 := bstep (se 1 (by rfl) ⟨1454264, by rfl⟩ : syracuseStep 1939019 = 2908529) B2908529
theorem B2454077 : Blo 1937435 2454077 := bbase (se 3 (by rfl) ⟨460139, by rfl⟩ : syracuseStep 2454077 = 920279) (by norm_num)
theorem B6544205 : Blo 1937435 6544205 := bstep (se 3 (by rfl) ⟨1227038, by rfl⟩ : syracuseStep 6544205 = 2454077) B2454077
theorem B4362803 : Blo 1937435 4362803 := bstep (se 1 (by rfl) ⟨3272102, by rfl⟩ : syracuseStep 4362803 = 6544205) B6544205
theorem B2908535 : Blo 1937435 2908535 := bstep (se 1 (by rfl) ⟨2181401, by rfl⟩ : syracuseStep 2908535 = 4362803) B4362803
theorem B1939023 : Blo 1937435 1939023 := bstep (se 1 (by rfl) ⟨1454267, by rfl⟩ : syracuseStep 1939023 = 2908535) B2908535
theorem B2908541 : Blo 1937435 2908541 := bbase (se 3 (by rfl) ⟨545351, by rfl⟩ : syracuseStep 2908541 = 1090703) (by norm_num)
theorem B1939027 : Blo 1937435 1939027 := bstep (se 1 (by rfl) ⟨1454270, by rfl⟩ : syracuseStep 1939027 = 2908541) B2908541
theorem B4362821 : Blo 1937435 4362821 := bbase (se 4 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 4362821 = 818029) (by norm_num)
theorem B2908547 : Blo 1937435 2908547 := bstep (se 1 (by rfl) ⟨2181410, by rfl⟩ : syracuseStep 2908547 = 4362821) B4362821
theorem B1939031 : Blo 1937435 1939031 := bstep (se 1 (by rfl) ⟨1454273, by rfl⟩ : syracuseStep 1939031 = 2908547) B2908547
theorem B2070641 : Blo 1937435 2070641 := bbase (se 2 (by rfl) ⟨776490, by rfl⟩ : syracuseStep 2070641 = 1552981) (by norm_num)
theorem B5521709 : Blo 1937435 5521709 := bstep (se 3 (by rfl) ⟨1035320, by rfl⟩ : syracuseStep 5521709 = 2070641) B2070641
theorem B3681139 : Blo 1937435 3681139 := bstep (se 1 (by rfl) ⟨2760854, by rfl⟩ : syracuseStep 3681139 = 5521709) B5521709
theorem B4908185 : Blo 1937435 4908185 := bstep (se 2 (by rfl) ⟨1840569, by rfl⟩ : syracuseStep 4908185 = 3681139) B3681139
theorem B3272123 : Blo 1937435 3272123 := bstep (se 1 (by rfl) ⟨2454092, by rfl⟩ : syracuseStep 3272123 = 4908185) B4908185
theorem B2181415 : Blo 1937435 2181415 := bstep (se 1 (by rfl) ⟨1636061, by rfl⟩ : syracuseStep 2181415 = 3272123) B3272123
theorem B2908553 : Blo 1937435 2908553 := bstep (se 2 (by rfl) ⟨1090707, by rfl⟩ : syracuseStep 2908553 = 2181415) B2181415
theorem B1939035 : Blo 1937435 1939035 := bstep (se 1 (by rfl) ⟨1454276, by rfl⟩ : syracuseStep 1939035 = 2908553) B2908553
theorem B9816389 : Blo 1937435 9816389 := bbase (se 4 (by rfl) ⟨920286, by rfl⟩ : syracuseStep 9816389 = 1840573) (by norm_num)
theorem B6544259 : Blo 1937435 6544259 := bstep (se 1 (by rfl) ⟨4908194, by rfl⟩ : syracuseStep 6544259 = 9816389) B9816389
theorem B4362839 : Blo 1937435 4362839 := bstep (se 1 (by rfl) ⟨3272129, by rfl⟩ : syracuseStep 4362839 = 6544259) B6544259
theorem B2908559 : Blo 1937435 2908559 := bstep (se 1 (by rfl) ⟨2181419, by rfl⟩ : syracuseStep 2908559 = 4362839) B4362839
theorem B1939039 : Blo 1937435 1939039 := bstep (se 1 (by rfl) ⟨1454279, by rfl⟩ : syracuseStep 1939039 = 2908559) B2908559
theorem B2908565 : Blo 1937435 2908565 := bbase (se 6 (by rfl) ⟨68169, by rfl⟩ : syracuseStep 2908565 = 136339) (by norm_num)
theorem B1939043 : Blo 1937435 1939043 := bstep (se 1 (by rfl) ⟨1454282, by rfl⟩ : syracuseStep 1939043 = 2908565) B2908565
theorem B2692669 : Blo 1937435 2692669 := bbase (se 3 (by rfl) ⟨504875, by rfl⟩ : syracuseStep 2692669 = 1009751) (by norm_num)
theorem B229774421 : Blo 1937435 229774421 := bstep (se 8 (by rfl) ⟨1346334, by rfl⟩ : syracuseStep 229774421 = 2692669) B2692669
theorem B612731789 : Blo 1937435 612731789 := bstep (se 3 (by rfl) ⟨114887210, by rfl⟩ : syracuseStep 612731789 = 229774421) B229774421
theorem B408487859 : Blo 1937435 408487859 := bstep (se 1 (by rfl) ⟨306365894, by rfl⟩ : syracuseStep 408487859 = 612731789) B612731789
theorem B272325239 : Blo 1937435 272325239 := bstep (se 1 (by rfl) ⟨204243929, by rfl⟩ : syracuseStep 272325239 = 408487859) B408487859
theorem B181550159 : Blo 1937435 181550159 := bstep (se 1 (by rfl) ⟨136162619, by rfl⟩ : syracuseStep 181550159 = 272325239) B272325239
theorem B121033439 : Blo 1937435 121033439 := bstep (se 1 (by rfl) ⟨90775079, by rfl⟩ : syracuseStep 121033439 = 181550159) B181550159
theorem B80688959 : Blo 1937435 80688959 := bstep (se 1 (by rfl) ⟨60516719, by rfl⟩ : syracuseStep 80688959 = 121033439) B121033439
theorem B53792639 : Blo 1937435 53792639 := bstep (se 1 (by rfl) ⟨40344479, by rfl⟩ : syracuseStep 53792639 = 80688959) B80688959
theorem B35861759 : Blo 1937435 35861759 := bstep (se 1 (by rfl) ⟨26896319, by rfl⟩ : syracuseStep 35861759 = 53792639) B53792639
theorem B23907839 : Blo 1937435 23907839 := bstep (se 1 (by rfl) ⟨17930879, by rfl⟩ : syracuseStep 23907839 = 35861759) B35861759
theorem B63754237 : Blo 1937435 63754237 := bstep (se 3 (by rfl) ⟨11953919, by rfl⟩ : syracuseStep 63754237 = 23907839) B23907839
theorem B85005649 : Blo 1937435 85005649 := bstep (se 2 (by rfl) ⟨31877118, by rfl⟩ : syracuseStep 85005649 = 63754237) B63754237
theorem B113340865 : Blo 1937435 113340865 := bstep (se 2 (by rfl) ⟨42502824, by rfl⟩ : syracuseStep 113340865 = 85005649) B85005649
theorem B151121153 : Blo 1937435 151121153 := bstep (se 2 (by rfl) ⟨56670432, by rfl⟩ : syracuseStep 151121153 = 113340865) B113340865
theorem B100747435 : Blo 1937435 100747435 := bstep (se 1 (by rfl) ⟨75560576, by rfl⟩ : syracuseStep 100747435 = 151121153) B151121153
theorem B134329913 : Blo 1937435 134329913 := bstep (se 2 (by rfl) ⟨50373717, by rfl⟩ : syracuseStep 134329913 = 100747435) B100747435
theorem B89553275 : Blo 1937435 89553275 := bstep (se 1 (by rfl) ⟨67164956, by rfl⟩ : syracuseStep 89553275 = 134329913) B134329913
theorem B59702183 : Blo 1937435 59702183 := bstep (se 1 (by rfl) ⟨44776637, by rfl⟩ : syracuseStep 59702183 = 89553275) B89553275
theorem B39801455 : Blo 1937435 39801455 := bstep (se 1 (by rfl) ⟨29851091, by rfl⟩ : syracuseStep 39801455 = 59702183) B59702183
theorem B26534303 : Blo 1937435 26534303 := bstep (se 1 (by rfl) ⟨19900727, by rfl⟩ : syracuseStep 26534303 = 39801455) B39801455
theorem B17689535 : Blo 1937435 17689535 := bstep (se 1 (by rfl) ⟨13267151, by rfl⟩ : syracuseStep 17689535 = 26534303) B26534303
theorem B11793023 : Blo 1937435 11793023 := bstep (se 1 (by rfl) ⟨8844767, by rfl⟩ : syracuseStep 11793023 = 17689535) B17689535
theorem B7862015 : Blo 1937435 7862015 := bstep (se 1 (by rfl) ⟨5896511, by rfl⟩ : syracuseStep 7862015 = 11793023) B11793023
theorem B5241343 : Blo 1937435 5241343 := bstep (se 1 (by rfl) ⟨3931007, by rfl⟩ : syracuseStep 5241343 = 7862015) B7862015
theorem B6988457 : Blo 1937435 6988457 := bstep (se 2 (by rfl) ⟨2620671, by rfl⟩ : syracuseStep 6988457 = 5241343) B5241343
theorem B4658971 : Blo 1937435 4658971 := bstep (se 1 (by rfl) ⟨3494228, by rfl⟩ : syracuseStep 4658971 = 6988457) B6988457
theorem B6211961 : Blo 1937435 6211961 := bstep (se 2 (by rfl) ⟨2329485, by rfl⟩ : syracuseStep 6211961 = 4658971) B4658971
theorem B4141307 : Blo 1937435 4141307 := bstep (se 1 (by rfl) ⟨3105980, by rfl⟩ : syracuseStep 4141307 = 6211961) B6211961
theorem B11043485 : Blo 1937435 11043485 := bstep (se 3 (by rfl) ⟨2070653, by rfl⟩ : syracuseStep 11043485 = 4141307) B4141307
theorem B7362323 : Blo 1937435 7362323 := bstep (se 1 (by rfl) ⟨5521742, by rfl⟩ : syracuseStep 7362323 = 11043485) B11043485
theorem B4908215 : Blo 1937435 4908215 := bstep (se 1 (by rfl) ⟨3681161, by rfl⟩ : syracuseStep 4908215 = 7362323) B7362323
theorem B3272143 : Blo 1937435 3272143 := bstep (se 1 (by rfl) ⟨2454107, by rfl⟩ : syracuseStep 3272143 = 4908215) B4908215
theorem B4362857 : Blo 1937435 4362857 := bstep (se 2 (by rfl) ⟨1636071, by rfl⟩ : syracuseStep 4362857 = 3272143) B3272143
theorem B2908571 : Blo 1937435 2908571 := bstep (se 1 (by rfl) ⟨2181428, by rfl⟩ : syracuseStep 2908571 = 4362857) B4362857
theorem B1939047 : Blo 1937435 1939047 := bstep (se 1 (by rfl) ⟨1454285, by rfl⟩ : syracuseStep 1939047 = 2908571) B2908571
theorem B2181433 : Blo 1937435 2181433 := bbase (se 2 (by rfl) ⟨818037, by rfl⟩ : syracuseStep 2181433 = 1636075) (by norm_num)
theorem B2908577 : Blo 1937435 2908577 := bstep (se 2 (by rfl) ⟨1090716, by rfl⟩ : syracuseStep 2908577 = 2181433) B2181433
theorem B1939051 : Blo 1937435 1939051 := bstep (se 1 (by rfl) ⟨1454288, by rfl⟩ : syracuseStep 1939051 = 2908577) B2908577
theorem B5521765 : Blo 1937435 5521765 := bbase (se 4 (by rfl) ⟨517665, by rfl⟩ : syracuseStep 5521765 = 1035331) (by norm_num)
theorem B7362353 : Blo 1937435 7362353 := bstep (se 2 (by rfl) ⟨2760882, by rfl⟩ : syracuseStep 7362353 = 5521765) B5521765
theorem B4908235 : Blo 1937435 4908235 := bstep (se 1 (by rfl) ⟨3681176, by rfl⟩ : syracuseStep 4908235 = 7362353) B7362353
theorem B6544313 : Blo 1937435 6544313 := bstep (se 2 (by rfl) ⟨2454117, by rfl⟩ : syracuseStep 6544313 = 4908235) B4908235
theorem B4362875 : Blo 1937435 4362875 := bstep (se 1 (by rfl) ⟨3272156, by rfl⟩ : syracuseStep 4362875 = 6544313) B6544313
theorem B2908583 : Blo 1937435 2908583 := bstep (se 1 (by rfl) ⟨2181437, by rfl⟩ : syracuseStep 2908583 = 4362875) B4362875
theorem B1939055 : Blo 1937435 1939055 := bstep (se 1 (by rfl) ⟨1454291, by rfl⟩ : syracuseStep 1939055 = 2908583) B2908583
theorem B2908589 : Blo 1937435 2908589 := bbase (se 3 (by rfl) ⟨545360, by rfl⟩ : syracuseStep 2908589 = 1090721) (by norm_num)
theorem B1939059 : Blo 1937435 1939059 := bstep (se 1 (by rfl) ⟨1454294, by rfl⟩ : syracuseStep 1939059 = 2908589) B2908589
theorem B4362893 : Blo 1937435 4362893 := bbase (se 3 (by rfl) ⟨818042, by rfl⟩ : syracuseStep 4362893 = 1636085) (by norm_num)
theorem B2908595 : Blo 1937435 2908595 := bstep (se 1 (by rfl) ⟨2181446, by rfl⟩ : syracuseStep 2908595 = 4362893) B4362893
theorem B1939063 : Blo 1937435 1939063 := bstep (se 1 (by rfl) ⟨1454297, by rfl⟩ : syracuseStep 1939063 = 2908595) B2908595
theorem B2454133 : Blo 1937435 2454133 := bbase (se 5 (by rfl) ⟨115037, by rfl⟩ : syracuseStep 2454133 = 230075) (by norm_num)
theorem B3272177 : Blo 1937435 3272177 := bstep (se 2 (by rfl) ⟨1227066, by rfl⟩ : syracuseStep 3272177 = 2454133) B2454133
theorem B2181451 : Blo 1937435 2181451 := bstep (se 1 (by rfl) ⟨1636088, by rfl⟩ : syracuseStep 2181451 = 3272177) B3272177
theorem B2908601 : Blo 1937435 2908601 := bstep (se 2 (by rfl) ⟨1090725, by rfl⟩ : syracuseStep 2908601 = 2181451) B2181451
theorem B1939067 : Blo 1937435 1939067 := bstep (se 1 (by rfl) ⟨1454300, by rfl⟩ : syracuseStep 1939067 = 2908601) B2908601
theorem B2988517 : Blo 1937435 2988517 := bbase (se 4 (by rfl) ⟨280173, by rfl⟩ : syracuseStep 2988517 = 560347) (by norm_num)
theorem B3984689 : Blo 1937435 3984689 := bstep (se 2 (by rfl) ⟨1494258, by rfl⟩ : syracuseStep 3984689 = 2988517) B2988517
theorem B2656459 : Blo 1937435 2656459 := bstep (se 1 (by rfl) ⟨1992344, by rfl⟩ : syracuseStep 2656459 = 3984689) B3984689
theorem B14167781 : Blo 1937435 14167781 := bstep (se 4 (by rfl) ⟨1328229, by rfl⟩ : syracuseStep 14167781 = 2656459) B2656459
theorem B9445187 : Blo 1937435 9445187 := bstep (se 1 (by rfl) ⟨7083890, by rfl⟩ : syracuseStep 9445187 = 14167781) B14167781
theorem B6296791 : Blo 1937435 6296791 := bstep (se 1 (by rfl) ⟨4722593, by rfl⟩ : syracuseStep 6296791 = 9445187) B9445187
theorem B8395721 : Blo 1937435 8395721 := bstep (se 2 (by rfl) ⟨3148395, by rfl⟩ : syracuseStep 8395721 = 6296791) B6296791
theorem B5597147 : Blo 1937435 5597147 := bstep (se 1 (by rfl) ⟨4197860, by rfl⟩ : syracuseStep 5597147 = 8395721) B8395721
theorem B14925725 : Blo 1937435 14925725 := bstep (se 3 (by rfl) ⟨2798573, by rfl⟩ : syracuseStep 14925725 = 5597147) B5597147
theorem B9950483 : Blo 1937435 9950483 := bstep (se 1 (by rfl) ⟨7462862, by rfl⟩ : syracuseStep 9950483 = 14925725) B14925725
theorem B26534621 : Blo 1937435 26534621 := bstep (se 3 (by rfl) ⟨4975241, by rfl⟩ : syracuseStep 26534621 = 9950483) B9950483
theorem B17689747 : Blo 1937435 17689747 := bstep (se 1 (by rfl) ⟨13267310, by rfl⟩ : syracuseStep 17689747 = 26534621) B26534621
theorem B23586329 : Blo 1937435 23586329 := bstep (se 2 (by rfl) ⟨8844873, by rfl⟩ : syracuseStep 23586329 = 17689747) B17689747
theorem B15724219 : Blo 1937435 15724219 := bstep (se 1 (by rfl) ⟨11793164, by rfl⟩ : syracuseStep 15724219 = 23586329) B23586329
theorem B20965625 : Blo 1937435 20965625 := bstep (se 2 (by rfl) ⟨7862109, by rfl⟩ : syracuseStep 20965625 = 15724219) B15724219
theorem B13977083 : Blo 1937435 13977083 := bstep (se 1 (by rfl) ⟨10482812, by rfl⟩ : syracuseStep 13977083 = 20965625) B20965625
theorem B37272221 : Blo 1937435 37272221 := bstep (se 3 (by rfl) ⟨6988541, by rfl⟩ : syracuseStep 37272221 = 13977083) B13977083
theorem B24848147 : Blo 1937435 24848147 := bstep (se 1 (by rfl) ⟨18636110, by rfl⟩ : syracuseStep 24848147 = 37272221) B37272221
theorem B16565431 : Blo 1937435 16565431 := bstep (se 1 (by rfl) ⟨12424073, by rfl⟩ : syracuseStep 16565431 = 24848147) B24848147
theorem B22087241 : Blo 1937435 22087241 := bstep (se 2 (by rfl) ⟨8282715, by rfl⟩ : syracuseStep 22087241 = 16565431) B16565431
theorem B14724827 : Blo 1937435 14724827 := bstep (se 1 (by rfl) ⟨11043620, by rfl⟩ : syracuseStep 14724827 = 22087241) B22087241
theorem B9816551 : Blo 1937435 9816551 := bstep (se 1 (by rfl) ⟨7362413, by rfl⟩ : syracuseStep 9816551 = 14724827) B14724827
theorem B6544367 : Blo 1937435 6544367 := bstep (se 1 (by rfl) ⟨4908275, by rfl⟩ : syracuseStep 6544367 = 9816551) B9816551
theorem B4362911 : Blo 1937435 4362911 := bstep (se 1 (by rfl) ⟨3272183, by rfl⟩ : syracuseStep 4362911 = 6544367) B6544367
theorem B2908607 : Blo 1937435 2908607 := bstep (se 1 (by rfl) ⟨2181455, by rfl⟩ : syracuseStep 2908607 = 4362911) B4362911
theorem B1939071 : Blo 1937435 1939071 := bstep (se 1 (by rfl) ⟨1454303, by rfl⟩ : syracuseStep 1939071 = 2908607) B2908607
theorem B2908613 : Blo 1937435 2908613 := bbase (se 4 (by rfl) ⟨272682, by rfl⟩ : syracuseStep 2908613 = 545365) (by norm_num)
theorem B1939075 : Blo 1937435 1939075 := bstep (se 1 (by rfl) ⟨1454306, by rfl⟩ : syracuseStep 1939075 = 2908613) B2908613
theorem B3272197 : Blo 1937435 3272197 := bbase (se 4 (by rfl) ⟨306768, by rfl⟩ : syracuseStep 3272197 = 613537) (by norm_num)
theorem B4362929 : Blo 1937435 4362929 := bstep (se 2 (by rfl) ⟨1636098, by rfl⟩ : syracuseStep 4362929 = 3272197) B3272197
theorem B2908619 : Blo 1937435 2908619 := bstep (se 1 (by rfl) ⟨2181464, by rfl⟩ : syracuseStep 2908619 = 4362929) B4362929
theorem B1939079 : Blo 1937435 1939079 := bstep (se 1 (by rfl) ⟨1454309, by rfl⟩ : syracuseStep 1939079 = 2908619) B2908619
theorem B2181469 : Blo 1937435 2181469 := bbase (se 3 (by rfl) ⟨409025, by rfl⟩ : syracuseStep 2181469 = 818051) (by norm_num)
theorem B2908625 : Blo 1937435 2908625 := bstep (se 2 (by rfl) ⟨1090734, by rfl⟩ : syracuseStep 2908625 = 2181469) B2181469
theorem B1939083 : Blo 1937435 1939083 := bstep (se 1 (by rfl) ⟨1454312, by rfl⟩ : syracuseStep 1939083 = 2908625) B2908625
theorem B6544421 : Blo 1937435 6544421 := bbase (se 4 (by rfl) ⟨613539, by rfl⟩ : syracuseStep 6544421 = 1227079) (by norm_num)
theorem B4362947 : Blo 1937435 4362947 := bstep (se 1 (by rfl) ⟨3272210, by rfl⟩ : syracuseStep 4362947 = 6544421) B6544421
theorem B2908631 : Blo 1937435 2908631 := bstep (se 1 (by rfl) ⟨2181473, by rfl⟩ : syracuseStep 2908631 = 4362947) B4362947
theorem B1939087 : Blo 1937435 1939087 := bstep (se 1 (by rfl) ⟨1454315, by rfl⟩ : syracuseStep 1939087 = 2908631) B2908631
theorem B2908637 : Blo 1937435 2908637 := bbase (se 3 (by rfl) ⟨545369, by rfl⟩ : syracuseStep 2908637 = 1090739) (by norm_num)
theorem B1939091 : Blo 1937435 1939091 := bstep (se 1 (by rfl) ⟨1454318, by rfl⟩ : syracuseStep 1939091 = 2908637) B2908637
theorem B4362965 : Blo 1937435 4362965 := bbase (se 7 (by rfl) ⟨51128, by rfl⟩ : syracuseStep 4362965 = 102257) (by norm_num)
theorem B2908643 : Blo 1937435 2908643 := bstep (se 1 (by rfl) ⟨2181482, by rfl⟩ : syracuseStep 2908643 = 4362965) B4362965
theorem B1939095 : Blo 1937435 1939095 := bstep (se 1 (by rfl) ⟨1454321, by rfl⟩ : syracuseStep 1939095 = 2908643) B2908643
theorem B8282837 : Blo 1937435 8282837 := bbase (se 7 (by rfl) ⟨97064, by rfl⟩ : syracuseStep 8282837 = 194129) (by norm_num)
theorem B5521891 : Blo 1937435 5521891 := bstep (se 1 (by rfl) ⟨4141418, by rfl⟩ : syracuseStep 5521891 = 8282837) B8282837
theorem B7362521 : Blo 1937435 7362521 := bstep (se 2 (by rfl) ⟨2760945, by rfl⟩ : syracuseStep 7362521 = 5521891) B5521891
theorem B4908347 : Blo 1937435 4908347 := bstep (se 1 (by rfl) ⟨3681260, by rfl⟩ : syracuseStep 4908347 = 7362521) B7362521
theorem B3272231 : Blo 1937435 3272231 := bstep (se 1 (by rfl) ⟨2454173, by rfl⟩ : syracuseStep 3272231 = 4908347) B4908347
theorem B2181487 : Blo 1937435 2181487 := bstep (se 1 (by rfl) ⟨1636115, by rfl⟩ : syracuseStep 2181487 = 3272231) B3272231
theorem B2908649 : Blo 1937435 2908649 := bstep (se 2 (by rfl) ⟨1090743, by rfl⟩ : syracuseStep 2908649 = 2181487) B2181487
theorem B1939099 : Blo 1937435 1939099 := bstep (se 1 (by rfl) ⟨1454324, by rfl⟩ : syracuseStep 1939099 = 2908649) B2908649
theorem B5241493 : Blo 1937435 5241493 := bbase (se 6 (by rfl) ⟨122847, by rfl⟩ : syracuseStep 5241493 = 245695) (by norm_num)
theorem B27954629 : Blo 1937435 27954629 := bstep (se 4 (by rfl) ⟨2620746, by rfl⟩ : syracuseStep 27954629 = 5241493) B5241493
theorem B18636419 : Blo 1937435 18636419 := bstep (se 1 (by rfl) ⟨13977314, by rfl⟩ : syracuseStep 18636419 = 27954629) B27954629
theorem B12424279 : Blo 1937435 12424279 := bstep (se 1 (by rfl) ⟨9318209, by rfl⟩ : syracuseStep 12424279 = 18636419) B18636419
theorem B16565705 : Blo 1937435 16565705 := bstep (se 2 (by rfl) ⟨6212139, by rfl⟩ : syracuseStep 16565705 = 12424279) B12424279
theorem B11043803 : Blo 1937435 11043803 := bstep (se 1 (by rfl) ⟨8282852, by rfl⟩ : syracuseStep 11043803 = 16565705) B16565705
theorem B7362535 : Blo 1937435 7362535 := bstep (se 1 (by rfl) ⟨5521901, by rfl⟩ : syracuseStep 7362535 = 11043803) B11043803
theorem B9816713 : Blo 1937435 9816713 := bstep (se 2 (by rfl) ⟨3681267, by rfl⟩ : syracuseStep 9816713 = 7362535) B7362535
theorem B6544475 : Blo 1937435 6544475 := bstep (se 1 (by rfl) ⟨4908356, by rfl⟩ : syracuseStep 6544475 = 9816713) B9816713
theorem B4362983 : Blo 1937435 4362983 := bstep (se 1 (by rfl) ⟨3272237, by rfl⟩ : syracuseStep 4362983 = 6544475) B6544475
theorem B2908655 : Blo 1937435 2908655 := bstep (se 1 (by rfl) ⟨2181491, by rfl⟩ : syracuseStep 2908655 = 4362983) B4362983
theorem B1939103 : Blo 1937435 1939103 := bstep (se 1 (by rfl) ⟨1454327, by rfl⟩ : syracuseStep 1939103 = 2908655) B2908655
theorem B2908661 : Blo 1937435 2908661 := bbase (se 5 (by rfl) ⟨136343, by rfl⟩ : syracuseStep 2908661 = 272687) (by norm_num)
theorem B1939107 : Blo 1937435 1939107 := bstep (se 1 (by rfl) ⟨1454330, by rfl⟩ : syracuseStep 1939107 = 2908661) B2908661
theorem B5521925 : Blo 1937435 5521925 := bbase (se 4 (by rfl) ⟨517680, by rfl⟩ : syracuseStep 5521925 = 1035361) (by norm_num)
theorem B3681283 : Blo 1937435 3681283 := bstep (se 1 (by rfl) ⟨2760962, by rfl⟩ : syracuseStep 3681283 = 5521925) B5521925
theorem B4908377 : Blo 1937435 4908377 := bstep (se 2 (by rfl) ⟨1840641, by rfl⟩ : syracuseStep 4908377 = 3681283) B3681283
theorem B3272251 : Blo 1937435 3272251 := bstep (se 1 (by rfl) ⟨2454188, by rfl⟩ : syracuseStep 3272251 = 4908377) B4908377
theorem B4363001 : Blo 1937435 4363001 := bstep (se 2 (by rfl) ⟨1636125, by rfl⟩ : syracuseStep 4363001 = 3272251) B3272251
theorem B2908667 : Blo 1937435 2908667 := bstep (se 1 (by rfl) ⟨2181500, by rfl⟩ : syracuseStep 2908667 = 4363001) B4363001
theorem B1939111 : Blo 1937435 1939111 := bstep (se 1 (by rfl) ⟨1454333, by rfl⟩ : syracuseStep 1939111 = 2908667) B2908667
theorem B2181505 : Blo 1937435 2181505 := bbase (se 2 (by rfl) ⟨818064, by rfl⟩ : syracuseStep 2181505 = 1636129) (by norm_num)
theorem B2908673 : Blo 1937435 2908673 := bstep (se 2 (by rfl) ⟨1090752, by rfl⟩ : syracuseStep 2908673 = 2181505) B2181505
theorem B1939115 : Blo 1937435 1939115 := bstep (se 1 (by rfl) ⟨1454336, by rfl⟩ : syracuseStep 1939115 = 2908673) B2908673
theorem B4908397 : Blo 1937435 4908397 := bbase (se 3 (by rfl) ⟨920324, by rfl⟩ : syracuseStep 4908397 = 1840649) (by norm_num)
theorem B6544529 : Blo 1937435 6544529 := bstep (se 2 (by rfl) ⟨2454198, by rfl⟩ : syracuseStep 6544529 = 4908397) B4908397
theorem B4363019 : Blo 1937435 4363019 := bstep (se 1 (by rfl) ⟨3272264, by rfl⟩ : syracuseStep 4363019 = 6544529) B6544529
theorem B2908679 : Blo 1937435 2908679 := bstep (se 1 (by rfl) ⟨2181509, by rfl⟩ : syracuseStep 2908679 = 4363019) B4363019
theorem B1939119 : Blo 1937435 1939119 := bstep (se 1 (by rfl) ⟨1454339, by rfl⟩ : syracuseStep 1939119 = 2908679) B2908679
theorem B2908685 : Blo 1937435 2908685 := bbase (se 3 (by rfl) ⟨545378, by rfl⟩ : syracuseStep 2908685 = 1090757) (by norm_num)
theorem B1939123 : Blo 1937435 1939123 := bstep (se 1 (by rfl) ⟨1454342, by rfl⟩ : syracuseStep 1939123 = 2908685) B2908685
theorem B4363037 : Blo 1937435 4363037 := bbase (se 3 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 4363037 = 1636139) (by norm_num)
theorem B2908691 : Blo 1937435 2908691 := bstep (se 1 (by rfl) ⟨2181518, by rfl⟩ : syracuseStep 2908691 = 4363037) B4363037
theorem B1939127 : Blo 1937435 1939127 := bstep (se 1 (by rfl) ⟨1454345, by rfl⟩ : syracuseStep 1939127 = 2908691) B2908691
theorem B3272285 : Blo 1937435 3272285 := bbase (se 3 (by rfl) ⟨613553, by rfl⟩ : syracuseStep 3272285 = 1227107) (by norm_num)
theorem B2181523 : Blo 1937435 2181523 := bstep (se 1 (by rfl) ⟨1636142, by rfl⟩ : syracuseStep 2181523 = 3272285) B3272285
theorem B2908697 : Blo 1937435 2908697 := bstep (se 2 (by rfl) ⟨1090761, by rfl⟩ : syracuseStep 2908697 = 2181523) B2181523
theorem B1939131 : Blo 1937435 1939131 := bstep (se 1 (by rfl) ⟨1454348, by rfl⟩ : syracuseStep 1939131 = 2908697) B2908697
theorem B1965593 : Blo 1937435 1965593 := bbase (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) (by norm_num)
theorem B5241581 : Blo 1937435 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B3494387 : Blo 1937435 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B2329591 : Blo 1937435 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B3106121 : Blo 1937435 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B8282989 : Blo 1937435 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B11043985 : Blo 1937435 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B14725313 : Blo 1937435 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B9816875 : Blo 1937435 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B6544583 : Blo 1937435 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B4363055 : Blo 1937435 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B2908703 : Blo 1937435 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B1939135 : Blo 1937435 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B2908709 : Blo 1937435 2908709 := bbase (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) (by norm_num)
theorem B1939139 : Blo 1937435 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B2454229 : Blo 1937435 2454229 := bbase (se 7 (by rfl) ⟨28760, by rfl⟩ : syracuseStep 2454229 = 57521) (by norm_num)
theorem B3272305 : Blo 1937435 3272305 := bstep (se 2 (by rfl) ⟨1227114, by rfl⟩ : syracuseStep 3272305 = 2454229) B2454229
theorem B4363073 : Blo 1937435 4363073 := bstep (se 2 (by rfl) ⟨1636152, by rfl⟩ : syracuseStep 4363073 = 3272305) B3272305
theorem B2908715 : Blo 1937435 2908715 := bstep (se 1 (by rfl) ⟨2181536, by rfl⟩ : syracuseStep 2908715 = 4363073) B4363073
theorem B1939143 : Blo 1937435 1939143 := bstep (se 1 (by rfl) ⟨1454357, by rfl⟩ : syracuseStep 1939143 = 2908715) B2908715
theorem B2181541 : Blo 1937435 2181541 := bbase (se 4 (by rfl) ⟨204519, by rfl⟩ : syracuseStep 2181541 = 409039) (by norm_num)
theorem B2908721 : Blo 1937435 2908721 := bstep (se 2 (by rfl) ⟨1090770, by rfl⟩ : syracuseStep 2908721 = 2181541) B2181541
theorem B1939147 : Blo 1937435 1939147 := bstep (se 1 (by rfl) ⟨1454360, by rfl⟩ : syracuseStep 1939147 = 2908721) B2908721
theorem B4659221 : Blo 1937435 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B12424589 : Blo 1937435 12424589 := bstep (se 3 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 12424589 = 4659221) B4659221
theorem B8283059 : Blo 1937435 8283059 := bstep (se 1 (by rfl) ⟨6212294, by rfl⟩ : syracuseStep 8283059 = 12424589) B12424589
theorem B5522039 : Blo 1937435 5522039 := bstep (se 1 (by rfl) ⟨4141529, by rfl⟩ : syracuseStep 5522039 = 8283059) B8283059
theorem B3681359 : Blo 1937435 3681359 := bstep (se 1 (by rfl) ⟨2761019, by rfl⟩ : syracuseStep 3681359 = 5522039) B5522039
theorem B2454239 : Blo 1937435 2454239 := bstep (se 1 (by rfl) ⟨1840679, by rfl⟩ : syracuseStep 2454239 = 3681359) B3681359
theorem B6544637 : Blo 1937435 6544637 := bstep (se 3 (by rfl) ⟨1227119, by rfl⟩ : syracuseStep 6544637 = 2454239) B2454239
theorem B4363091 : Blo 1937435 4363091 := bstep (se 1 (by rfl) ⟨3272318, by rfl⟩ : syracuseStep 4363091 = 6544637) B6544637
theorem B2908727 : Blo 1937435 2908727 := bstep (se 1 (by rfl) ⟨2181545, by rfl⟩ : syracuseStep 2908727 = 4363091) B4363091
theorem B1939151 : Blo 1937435 1939151 := bstep (se 1 (by rfl) ⟨1454363, by rfl⟩ : syracuseStep 1939151 = 2908727) B2908727
theorem B2908733 : Blo 1937435 2908733 := bbase (se 3 (by rfl) ⟨545387, by rfl⟩ : syracuseStep 2908733 = 1090775) (by norm_num)
theorem B1939155 : Blo 1937435 1939155 := bstep (se 1 (by rfl) ⟨1454366, by rfl⟩ : syracuseStep 1939155 = 2908733) B2908733
theorem B4363109 : Blo 1937435 4363109 := bbase (se 4 (by rfl) ⟨409041, by rfl⟩ : syracuseStep 4363109 = 818083) (by norm_num)
theorem B2908739 : Blo 1937435 2908739 := bstep (se 1 (by rfl) ⟨2181554, by rfl⟩ : syracuseStep 2908739 = 4363109) B4363109
theorem B1939159 : Blo 1937435 1939159 := bstep (se 1 (by rfl) ⟨1454369, by rfl⟩ : syracuseStep 1939159 = 2908739) B2908739
theorem B4908509 : Blo 1937435 4908509 := bbase (se 3 (by rfl) ⟨920345, by rfl⟩ : syracuseStep 4908509 = 1840691) (by norm_num)
theorem B3272339 : Blo 1937435 3272339 := bstep (se 1 (by rfl) ⟨2454254, by rfl⟩ : syracuseStep 3272339 = 4908509) B4908509
theorem B2181559 : Blo 1937435 2181559 := bstep (se 1 (by rfl) ⟨1636169, by rfl⟩ : syracuseStep 2181559 = 3272339) B3272339
theorem B2908745 : Blo 1937435 2908745 := bstep (se 2 (by rfl) ⟨1090779, by rfl⟩ : syracuseStep 2908745 = 2181559) B2181559
theorem B1939163 : Blo 1937435 1939163 := bstep (se 1 (by rfl) ⟨1454372, by rfl⟩ : syracuseStep 1939163 = 2908745) B2908745
theorem B3681389 : Blo 1937435 3681389 := bbase (se 3 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 3681389 = 1380521) (by norm_num)
theorem B9817037 : Blo 1937435 9817037 := bstep (se 3 (by rfl) ⟨1840694, by rfl⟩ : syracuseStep 9817037 = 3681389) B3681389
theorem B6544691 : Blo 1937435 6544691 := bstep (se 1 (by rfl) ⟨4908518, by rfl⟩ : syracuseStep 6544691 = 9817037) B9817037
theorem B4363127 : Blo 1937435 4363127 := bstep (se 1 (by rfl) ⟨3272345, by rfl⟩ : syracuseStep 4363127 = 6544691) B6544691
theorem B2908751 : Blo 1937435 2908751 := bstep (se 1 (by rfl) ⟨2181563, by rfl⟩ : syracuseStep 2908751 = 4363127) B4363127
theorem B1939167 : Blo 1937435 1939167 := bstep (se 1 (by rfl) ⟨1454375, by rfl⟩ : syracuseStep 1939167 = 2908751) B2908751
theorem B2908757 : Blo 1937435 2908757 := bbase (se 8 (by rfl) ⟨17043, by rfl⟩ : syracuseStep 2908757 = 34087) (by norm_num)
theorem B1939171 : Blo 1937435 1939171 := bstep (se 1 (by rfl) ⟨1454378, by rfl⟩ : syracuseStep 1939171 = 2908757) B2908757
theorem B5896901 : Blo 1937435 5896901 := bbase (se 4 (by rfl) ⟨552834, by rfl⟩ : syracuseStep 5896901 = 1105669) (by norm_num)
theorem B3931267 : Blo 1937435 3931267 := bstep (se 1 (by rfl) ⟨2948450, by rfl⟩ : syracuseStep 3931267 = 5896901) B5896901
theorem B5241689 : Blo 1937435 5241689 := bstep (se 2 (by rfl) ⟨1965633, by rfl⟩ : syracuseStep 5241689 = 3931267) B3931267
theorem B3494459 : Blo 1937435 3494459 := bstep (se 1 (by rfl) ⟨2620844, by rfl⟩ : syracuseStep 3494459 = 5241689) B5241689
theorem B9318557 : Blo 1937435 9318557 := bstep (se 3 (by rfl) ⟨1747229, by rfl⟩ : syracuseStep 9318557 = 3494459) B3494459
theorem B6212371 : Blo 1937435 6212371 := bstep (se 1 (by rfl) ⟨4659278, by rfl⟩ : syracuseStep 6212371 = 9318557) B9318557
theorem B8283161 : Blo 1937435 8283161 := bstep (se 2 (by rfl) ⟨3106185, by rfl⟩ : syracuseStep 8283161 = 6212371) B6212371
theorem B5522107 : Blo 1937435 5522107 := bstep (se 1 (by rfl) ⟨4141580, by rfl⟩ : syracuseStep 5522107 = 8283161) B8283161
theorem B7362809 : Blo 1937435 7362809 := bstep (se 2 (by rfl) ⟨2761053, by rfl⟩ : syracuseStep 7362809 = 5522107) B5522107
theorem B4908539 : Blo 1937435 4908539 := bstep (se 1 (by rfl) ⟨3681404, by rfl⟩ : syracuseStep 4908539 = 7362809) B7362809
theorem B3272359 : Blo 1937435 3272359 := bstep (se 1 (by rfl) ⟨2454269, by rfl⟩ : syracuseStep 3272359 = 4908539) B4908539
theorem B4363145 : Blo 1937435 4363145 := bstep (se 2 (by rfl) ⟨1636179, by rfl⟩ : syracuseStep 4363145 = 3272359) B3272359
theorem B2908763 : Blo 1937435 2908763 := bstep (se 1 (by rfl) ⟨2181572, by rfl⟩ : syracuseStep 2908763 = 4363145) B4363145
theorem B1939175 : Blo 1937435 1939175 := bstep (se 1 (by rfl) ⟨1454381, by rfl⟩ : syracuseStep 1939175 = 2908763) B2908763
theorem B2181577 : Blo 1937435 2181577 := bbase (se 2 (by rfl) ⟨818091, by rfl⟩ : syracuseStep 2181577 = 1636183) (by norm_num)
theorem B2908769 : Blo 1937435 2908769 := bstep (se 2 (by rfl) ⟨1090788, by rfl⟩ : syracuseStep 2908769 = 2181577) B2181577
theorem B1939179 : Blo 1937435 1939179 := bstep (se 1 (by rfl) ⟨1454384, by rfl⟩ : syracuseStep 1939179 = 2908769) B2908769
theorem B16566389 : Blo 1937435 16566389 := bbase (se 5 (by rfl) ⟨776549, by rfl⟩ : syracuseStep 16566389 = 1553099) (by norm_num)
theorem B11044259 : Blo 1937435 11044259 := bstep (se 1 (by rfl) ⟨8283194, by rfl⟩ : syracuseStep 11044259 = 16566389) B16566389
theorem B7362839 : Blo 1937435 7362839 := bstep (se 1 (by rfl) ⟨5522129, by rfl⟩ : syracuseStep 7362839 = 11044259) B11044259
theorem B4908559 : Blo 1937435 4908559 := bstep (se 1 (by rfl) ⟨3681419, by rfl⟩ : syracuseStep 4908559 = 7362839) B7362839
theorem B6544745 : Blo 1937435 6544745 := bstep (se 2 (by rfl) ⟨2454279, by rfl⟩ : syracuseStep 6544745 = 4908559) B4908559
theorem B4363163 : Blo 1937435 4363163 := bstep (se 1 (by rfl) ⟨3272372, by rfl⟩ : syracuseStep 4363163 = 6544745) B6544745
theorem B2908775 : Blo 1937435 2908775 := bstep (se 1 (by rfl) ⟨2181581, by rfl⟩ : syracuseStep 2908775 = 4363163) B4363163
theorem B1939183 : Blo 1937435 1939183 := bstep (se 1 (by rfl) ⟨1454387, by rfl⟩ : syracuseStep 1939183 = 2908775) B2908775
theorem B2908781 : Blo 1937435 2908781 := bbase (se 3 (by rfl) ⟨545396, by rfl⟩ : syracuseStep 2908781 = 1090793) (by norm_num)
theorem B1939187 : Blo 1937435 1939187 := bstep (se 1 (by rfl) ⟨1454390, by rfl⟩ : syracuseStep 1939187 = 2908781) B2908781
theorem B4363181 : Blo 1937435 4363181 := bbase (se 3 (by rfl) ⟨818096, by rfl⟩ : syracuseStep 4363181 = 1636193) (by norm_num)
theorem B2908787 : Blo 1937435 2908787 := bstep (se 1 (by rfl) ⟨2181590, by rfl⟩ : syracuseStep 2908787 = 4363181) B4363181
theorem B1939191 : Blo 1937435 1939191 := bstep (se 1 (by rfl) ⟨1454393, by rfl⟩ : syracuseStep 1939191 = 2908787) B2908787
theorem B5522165 : Blo 1937435 5522165 := bbase (se 5 (by rfl) ⟨258851, by rfl⟩ : syracuseStep 5522165 = 517703) (by norm_num)
theorem B3681443 : Blo 1937435 3681443 := bstep (se 1 (by rfl) ⟨2761082, by rfl⟩ : syracuseStep 3681443 = 5522165) B5522165
theorem B2454295 : Blo 1937435 2454295 := bstep (se 1 (by rfl) ⟨1840721, by rfl⟩ : syracuseStep 2454295 = 3681443) B3681443
theorem B3272393 : Blo 1937435 3272393 := bstep (se 2 (by rfl) ⟨1227147, by rfl⟩ : syracuseStep 3272393 = 2454295) B2454295
theorem B2181595 : Blo 1937435 2181595 := bstep (se 1 (by rfl) ⟨1636196, by rfl⟩ : syracuseStep 2181595 = 3272393) B3272393
theorem B2908793 : Blo 1937435 2908793 := bstep (se 2 (by rfl) ⟨1090797, by rfl⟩ : syracuseStep 2908793 = 2181595) B2181595
theorem B1939195 : Blo 1937435 1939195 := bstep (se 1 (by rfl) ⟨1454396, by rfl⟩ : syracuseStep 1939195 = 2908793) B2908793
theorem B2487785 : Blo 1937435 2487785 := bbase (se 2 (by rfl) ⟨932919, by rfl⟩ : syracuseStep 2487785 = 1865839) (by norm_num)
theorem B6634093 : Blo 1937435 6634093 := bstep (se 3 (by rfl) ⟨1243892, by rfl⟩ : syracuseStep 6634093 = 2487785) B2487785
theorem B8845457 : Blo 1937435 8845457 := bstep (se 2 (by rfl) ⟨3317046, by rfl⟩ : syracuseStep 8845457 = 6634093) B6634093
theorem B23587885 : Blo 1937435 23587885 := bstep (se 3 (by rfl) ⟨4422728, by rfl⟩ : syracuseStep 23587885 = 8845457) B8845457
theorem B31450513 : Blo 1937435 31450513 := bstep (se 2 (by rfl) ⟨11793942, by rfl⟩ : syracuseStep 31450513 = 23587885) B23587885
theorem B41934017 : Blo 1937435 41934017 := bstep (se 2 (by rfl) ⟨15725256, by rfl⟩ : syracuseStep 41934017 = 31450513) B31450513
theorem B27956011 : Blo 1937435 27956011 := bstep (se 1 (by rfl) ⟨20967008, by rfl⟩ : syracuseStep 27956011 = 41934017) B41934017
theorem B37274681 : Blo 1937435 37274681 := bstep (se 2 (by rfl) ⟨13978005, by rfl⟩ : syracuseStep 37274681 = 27956011) B27956011
theorem B24849787 : Blo 1937435 24849787 := bstep (se 1 (by rfl) ⟨18637340, by rfl⟩ : syracuseStep 24849787 = 37274681) B37274681
theorem B33133049 : Blo 1937435 33133049 := bstep (se 2 (by rfl) ⟨12424893, by rfl⟩ : syracuseStep 33133049 = 24849787) B24849787
theorem B22088699 : Blo 1937435 22088699 := bstep (se 1 (by rfl) ⟨16566524, by rfl⟩ : syracuseStep 22088699 = 33133049) B33133049
theorem B14725799 : Blo 1937435 14725799 := bstep (se 1 (by rfl) ⟨11044349, by rfl⟩ : syracuseStep 14725799 = 22088699) B22088699
theorem B9817199 : Blo 1937435 9817199 := bstep (se 1 (by rfl) ⟨7362899, by rfl⟩ : syracuseStep 9817199 = 14725799) B14725799
theorem B6544799 : Blo 1937435 6544799 := bstep (se 1 (by rfl) ⟨4908599, by rfl⟩ : syracuseStep 6544799 = 9817199) B9817199
theorem B4363199 : Blo 1937435 4363199 := bstep (se 1 (by rfl) ⟨3272399, by rfl⟩ : syracuseStep 4363199 = 6544799) B6544799
theorem B2908799 : Blo 1937435 2908799 := bstep (se 1 (by rfl) ⟨2181599, by rfl⟩ : syracuseStep 2908799 = 4363199) B4363199
theorem B1939199 : Blo 1937435 1939199 := bstep (se 1 (by rfl) ⟨1454399, by rfl⟩ : syracuseStep 1939199 = 2908799) B2908799
theorem B2908805 : Blo 1937435 2908805 := bbase (se 4 (by rfl) ⟨272700, by rfl⟩ : syracuseStep 2908805 = 545401) (by norm_num)
theorem B1939203 : Blo 1937435 1939203 := bstep (se 1 (by rfl) ⟨1454402, by rfl⟩ : syracuseStep 1939203 = 2908805) B2908805
theorem B3272413 : Blo 1937435 3272413 := bbase (se 3 (by rfl) ⟨613577, by rfl⟩ : syracuseStep 3272413 = 1227155) (by norm_num)
theorem B4363217 : Blo 1937435 4363217 := bstep (se 2 (by rfl) ⟨1636206, by rfl⟩ : syracuseStep 4363217 = 3272413) B3272413
theorem B2908811 : Blo 1937435 2908811 := bstep (se 1 (by rfl) ⟨2181608, by rfl⟩ : syracuseStep 2908811 = 4363217) B4363217
theorem B1939207 : Blo 1937435 1939207 := bstep (se 1 (by rfl) ⟨1454405, by rfl⟩ : syracuseStep 1939207 = 2908811) B2908811
theorem B2181613 : Blo 1937435 2181613 := bbase (se 3 (by rfl) ⟨409052, by rfl⟩ : syracuseStep 2181613 = 818105) (by norm_num)
theorem B2908817 : Blo 1937435 2908817 := bstep (se 2 (by rfl) ⟨1090806, by rfl⟩ : syracuseStep 2908817 = 2181613) B2181613
theorem B1939211 : Blo 1937435 1939211 := bstep (se 1 (by rfl) ⟨1454408, by rfl⟩ : syracuseStep 1939211 = 2908817) B2908817
theorem B6544853 : Blo 1937435 6544853 := bbase (se 7 (by rfl) ⟨76697, by rfl⟩ : syracuseStep 6544853 = 153395) (by norm_num)
theorem B4363235 : Blo 1937435 4363235 := bstep (se 1 (by rfl) ⟨3272426, by rfl⟩ : syracuseStep 4363235 = 6544853) B6544853
theorem B2908823 : Blo 1937435 2908823 := bstep (se 1 (by rfl) ⟨2181617, by rfl⟩ : syracuseStep 2908823 = 4363235) B4363235
theorem B1939215 : Blo 1937435 1939215 := bstep (se 1 (by rfl) ⟨1454411, by rfl⟩ : syracuseStep 1939215 = 2908823) B2908823
theorem B2908829 : Blo 1937435 2908829 := bbase (se 3 (by rfl) ⟨545405, by rfl⟩ : syracuseStep 2908829 = 1090811) (by norm_num)
theorem B1939219 : Blo 1937435 1939219 := bstep (se 1 (by rfl) ⟨1454414, by rfl⟩ : syracuseStep 1939219 = 2908829) B2908829
theorem B4363253 : Blo 1937435 4363253 := bbase (se 5 (by rfl) ⟨204527, by rfl⟩ : syracuseStep 4363253 = 409055) (by norm_num)
theorem B2908835 : Blo 1937435 2908835 := bstep (se 1 (by rfl) ⟨2181626, by rfl⟩ : syracuseStep 2908835 = 4363253) B4363253
theorem B1939223 : Blo 1937435 1939223 := bstep (se 1 (by rfl) ⟨1454417, by rfl⟩ : syracuseStep 1939223 = 2908835) B2908835
theorem B18891893 : Blo 1937435 18891893 := bbase (se 5 (by rfl) ⟨885557, by rfl⟩ : syracuseStep 18891893 = 1771115) (by norm_num)
theorem B50378381 : Blo 1937435 50378381 := bstep (se 3 (by rfl) ⟨9445946, by rfl⟩ : syracuseStep 50378381 = 18891893) B18891893
theorem B33585587 : Blo 1937435 33585587 := bstep (se 1 (by rfl) ⟨25189190, by rfl⟩ : syracuseStep 33585587 = 50378381) B50378381
theorem B22390391 : Blo 1937435 22390391 := bstep (se 1 (by rfl) ⟨16792793, by rfl⟩ : syracuseStep 22390391 = 33585587) B33585587
theorem B59707709 : Blo 1937435 59707709 := bstep (se 3 (by rfl) ⟨11195195, by rfl⟩ : syracuseStep 59707709 = 22390391) B22390391
theorem B39805139 : Blo 1937435 39805139 := bstep (se 1 (by rfl) ⟨29853854, by rfl⟩ : syracuseStep 39805139 = 59707709) B59707709
theorem B106147037 : Blo 1937435 106147037 := bstep (se 3 (by rfl) ⟨19902569, by rfl⟩ : syracuseStep 106147037 = 39805139) B39805139
theorem B70764691 : Blo 1937435 70764691 := bstep (se 1 (by rfl) ⟨53073518, by rfl⟩ : syracuseStep 70764691 = 106147037) B106147037
theorem B94352921 : Blo 1937435 94352921 := bstep (se 2 (by rfl) ⟨35382345, by rfl⟩ : syracuseStep 94352921 = 70764691) B70764691
theorem B62901947 : Blo 1937435 62901947 := bstep (se 1 (by rfl) ⟨47176460, by rfl⟩ : syracuseStep 62901947 = 94352921) B94352921
theorem B41934631 : Blo 1937435 41934631 := bstep (se 1 (by rfl) ⟨31450973, by rfl⟩ : syracuseStep 41934631 = 62901947) B62901947
theorem B55912841 : Blo 1937435 55912841 := bstep (se 2 (by rfl) ⟨20967315, by rfl⟩ : syracuseStep 55912841 = 41934631) B41934631
theorem B37275227 : Blo 1937435 37275227 := bstep (se 1 (by rfl) ⟨27956420, by rfl⟩ : syracuseStep 37275227 = 55912841) B55912841
theorem B24850151 : Blo 1937435 24850151 := bstep (se 1 (by rfl) ⟨18637613, by rfl⟩ : syracuseStep 24850151 = 37275227) B37275227
theorem B16566767 : Blo 1937435 16566767 := bstep (se 1 (by rfl) ⟨12425075, by rfl⟩ : syracuseStep 16566767 = 24850151) B24850151
theorem B11044511 : Blo 1937435 11044511 := bstep (se 1 (by rfl) ⟨8283383, by rfl⟩ : syracuseStep 11044511 = 16566767) B16566767
theorem B7363007 : Blo 1937435 7363007 := bstep (se 1 (by rfl) ⟨5522255, by rfl⟩ : syracuseStep 7363007 = 11044511) B11044511
theorem B4908671 : Blo 1937435 4908671 := bstep (se 1 (by rfl) ⟨3681503, by rfl⟩ : syracuseStep 4908671 = 7363007) B7363007
theorem B3272447 : Blo 1937435 3272447 := bstep (se 1 (by rfl) ⟨2454335, by rfl⟩ : syracuseStep 3272447 = 4908671) B4908671
theorem B2181631 : Blo 1937435 2181631 := bstep (se 1 (by rfl) ⟨1636223, by rfl⟩ : syracuseStep 2181631 = 3272447) B3272447
theorem B2908841 : Blo 1937435 2908841 := bstep (se 2 (by rfl) ⟨1090815, by rfl⟩ : syracuseStep 2908841 = 2181631) B2181631
theorem B1939227 : Blo 1937435 1939227 := bstep (se 1 (by rfl) ⟨1454420, by rfl⟩ : syracuseStep 1939227 = 2908841) B2908841
theorem B2761133 : Blo 1937435 2761133 := bbase (se 3 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 2761133 = 1035425) (by norm_num)
theorem B7363021 : Blo 1937435 7363021 := bstep (se 3 (by rfl) ⟨1380566, by rfl⟩ : syracuseStep 7363021 = 2761133) B2761133
theorem B9817361 : Blo 1937435 9817361 := bstep (se 2 (by rfl) ⟨3681510, by rfl⟩ : syracuseStep 9817361 = 7363021) B7363021
theorem B6544907 : Blo 1937435 6544907 := bstep (se 1 (by rfl) ⟨4908680, by rfl⟩ : syracuseStep 6544907 = 9817361) B9817361
theorem B4363271 : Blo 1937435 4363271 := bstep (se 1 (by rfl) ⟨3272453, by rfl⟩ : syracuseStep 4363271 = 6544907) B6544907
theorem B2908847 : Blo 1937435 2908847 := bstep (se 1 (by rfl) ⟨2181635, by rfl⟩ : syracuseStep 2908847 = 4363271) B4363271
theorem B1939231 : Blo 1937435 1939231 := bstep (se 1 (by rfl) ⟨1454423, by rfl⟩ : syracuseStep 1939231 = 2908847) B2908847
theorem B2908853 : Blo 1937435 2908853 := bbase (se 5 (by rfl) ⟨136352, by rfl⟩ : syracuseStep 2908853 = 272705) (by norm_num)
theorem B1939235 : Blo 1937435 1939235 := bstep (se 1 (by rfl) ⟨1454426, by rfl⟩ : syracuseStep 1939235 = 2908853) B2908853
theorem B4908701 : Blo 1937435 4908701 := bbase (se 3 (by rfl) ⟨920381, by rfl⟩ : syracuseStep 4908701 = 1840763) (by norm_num)
theorem B3272467 : Blo 1937435 3272467 := bstep (se 1 (by rfl) ⟨2454350, by rfl⟩ : syracuseStep 3272467 = 4908701) B4908701
theorem B4363289 : Blo 1937435 4363289 := bstep (se 2 (by rfl) ⟨1636233, by rfl⟩ : syracuseStep 4363289 = 3272467) B3272467
theorem B2908859 : Blo 1937435 2908859 := bstep (se 1 (by rfl) ⟨2181644, by rfl⟩ : syracuseStep 2908859 = 4363289) B4363289
theorem B1939239 : Blo 1937435 1939239 := bstep (se 1 (by rfl) ⟨1454429, by rfl⟩ : syracuseStep 1939239 = 2908859) B2908859
theorem B2181649 : Blo 1937435 2181649 := bbase (se 2 (by rfl) ⟨818118, by rfl⟩ : syracuseStep 2181649 = 1636237) (by norm_num)
theorem B2908865 : Blo 1937435 2908865 := bstep (se 2 (by rfl) ⟨1090824, by rfl⟩ : syracuseStep 2908865 = 2181649) B2181649
theorem B1939243 : Blo 1937435 1939243 := bstep (se 1 (by rfl) ⟨1454432, by rfl⟩ : syracuseStep 1939243 = 2908865) B2908865
theorem B3681541 : Blo 1937435 3681541 := bbase (se 4 (by rfl) ⟨345144, by rfl⟩ : syracuseStep 3681541 = 690289) (by norm_num)
theorem B4908721 : Blo 1937435 4908721 := bstep (se 2 (by rfl) ⟨1840770, by rfl⟩ : syracuseStep 4908721 = 3681541) B3681541
theorem B6544961 : Blo 1937435 6544961 := bstep (se 2 (by rfl) ⟨2454360, by rfl⟩ : syracuseStep 6544961 = 4908721) B4908721
theorem B4363307 : Blo 1937435 4363307 := bstep (se 1 (by rfl) ⟨3272480, by rfl⟩ : syracuseStep 4363307 = 6544961) B6544961
theorem B2908871 : Blo 1937435 2908871 := bstep (se 1 (by rfl) ⟨2181653, by rfl⟩ : syracuseStep 2908871 = 4363307) B4363307
theorem B1939247 : Blo 1937435 1939247 := bstep (se 1 (by rfl) ⟨1454435, by rfl⟩ : syracuseStep 1939247 = 2908871) B2908871
theorem B2908877 : Blo 1937435 2908877 := bbase (se 3 (by rfl) ⟨545414, by rfl⟩ : syracuseStep 2908877 = 1090829) (by norm_num)
theorem B1939251 : Blo 1937435 1939251 := bstep (se 1 (by rfl) ⟨1454438, by rfl⟩ : syracuseStep 1939251 = 2908877) B2908877
theorem B4363325 : Blo 1937435 4363325 := bbase (se 3 (by rfl) ⟨818123, by rfl⟩ : syracuseStep 4363325 = 1636247) (by norm_num)
theorem B2908883 : Blo 1937435 2908883 := bstep (se 1 (by rfl) ⟨2181662, by rfl⟩ : syracuseStep 2908883 = 4363325) B4363325
theorem B1939255 : Blo 1937435 1939255 := bstep (se 1 (by rfl) ⟨1454441, by rfl⟩ : syracuseStep 1939255 = 2908883) B2908883
theorem B3272501 : Blo 1937435 3272501 := bbase (se 5 (by rfl) ⟨153398, by rfl⟩ : syracuseStep 3272501 = 306797) (by norm_num)
theorem B2181667 : Blo 1937435 2181667 := bstep (se 1 (by rfl) ⟨1636250, by rfl⟩ : syracuseStep 2181667 = 3272501) B3272501
theorem B2908889 : Blo 1937435 2908889 := bstep (se 2 (by rfl) ⟨1090833, by rfl⟩ : syracuseStep 2908889 = 2181667) B2181667
theorem B1939259 : Blo 1937435 1939259 := bstep (se 1 (by rfl) ⟨1454444, by rfl⟩ : syracuseStep 1939259 = 2908889) B2908889
theorem B5522357 : Blo 1937435 5522357 := bbase (se 5 (by rfl) ⟨258860, by rfl⟩ : syracuseStep 5522357 = 517721) (by norm_num)
theorem B14726285 : Blo 1937435 14726285 := bstep (se 3 (by rfl) ⟨2761178, by rfl⟩ : syracuseStep 14726285 = 5522357) B5522357
theorem B9817523 : Blo 1937435 9817523 := bstep (se 1 (by rfl) ⟨7363142, by rfl⟩ : syracuseStep 9817523 = 14726285) B14726285
theorem B6545015 : Blo 1937435 6545015 := bstep (se 1 (by rfl) ⟨4908761, by rfl⟩ : syracuseStep 6545015 = 9817523) B9817523
theorem B4363343 : Blo 1937435 4363343 := bstep (se 1 (by rfl) ⟨3272507, by rfl⟩ : syracuseStep 4363343 = 6545015) B6545015
theorem B2908895 : Blo 1937435 2908895 := bstep (se 1 (by rfl) ⟨2181671, by rfl⟩ : syracuseStep 2908895 = 4363343) B4363343
theorem B1939263 : Blo 1937435 1939263 := bstep (se 1 (by rfl) ⟨1454447, by rfl⟩ : syracuseStep 1939263 = 2908895) B2908895
theorem B2908901 : Blo 1937435 2908901 := bbase (se 4 (by rfl) ⟨272709, by rfl⟩ : syracuseStep 2908901 = 545419) (by norm_num)
theorem B1939267 : Blo 1937435 1939267 := bstep (se 1 (by rfl) ⟨1454450, by rfl⟩ : syracuseStep 1939267 = 2908901) B2908901
theorem B2070893 : Blo 1937435 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B5522381 : Blo 1937435 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B3681587 : Blo 1937435 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B2454391 : Blo 1937435 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B3272521 : Blo 1937435 3272521 := bstep (se 2 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 3272521 = 2454391) B2454391
theorem B4363361 : Blo 1937435 4363361 := bstep (se 2 (by rfl) ⟨1636260, by rfl⟩ : syracuseStep 4363361 = 3272521) B3272521
theorem B2908907 : Blo 1937435 2908907 := bstep (se 1 (by rfl) ⟨2181680, by rfl⟩ : syracuseStep 2908907 = 4363361) B4363361
theorem B1939271 : Blo 1937435 1939271 := bstep (se 1 (by rfl) ⟨1454453, by rfl⟩ : syracuseStep 1939271 = 2908907) B2908907
theorem B2181685 : Blo 1937435 2181685 := bbase (se 5 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 2181685 = 204533) (by norm_num)
theorem B2908913 : Blo 1937435 2908913 := bstep (se 2 (by rfl) ⟨1090842, by rfl⟩ : syracuseStep 2908913 = 2181685) B2181685
theorem B1939275 : Blo 1937435 1939275 := bstep (se 1 (by rfl) ⟨1454456, by rfl⟩ : syracuseStep 1939275 = 2908913) B2908913
theorem B2454401 : Blo 1937435 2454401 := bbase (se 2 (by rfl) ⟨920400, by rfl⟩ : syracuseStep 2454401 = 1840801) (by norm_num)
theorem B6545069 : Blo 1937435 6545069 := bstep (se 3 (by rfl) ⟨1227200, by rfl⟩ : syracuseStep 6545069 = 2454401) B2454401
theorem B4363379 : Blo 1937435 4363379 := bstep (se 1 (by rfl) ⟨3272534, by rfl⟩ : syracuseStep 4363379 = 6545069) B6545069
theorem B2908919 : Blo 1937435 2908919 := bstep (se 1 (by rfl) ⟨2181689, by rfl⟩ : syracuseStep 2908919 = 4363379) B4363379
theorem B1939279 : Blo 1937435 1939279 := bstep (se 1 (by rfl) ⟨1454459, by rfl⟩ : syracuseStep 1939279 = 2908919) B2908919
theorem B2908925 : Blo 1937435 2908925 := bbase (se 3 (by rfl) ⟨545423, by rfl⟩ : syracuseStep 2908925 = 1090847) (by norm_num)
theorem B1939283 : Blo 1937435 1939283 := bstep (se 1 (by rfl) ⟨1454462, by rfl⟩ : syracuseStep 1939283 = 2908925) B2908925
theorem B4363397 : Blo 1937435 4363397 := bbase (se 4 (by rfl) ⟨409068, by rfl⟩ : syracuseStep 4363397 = 818137) (by norm_num)
theorem B2908931 : Blo 1937435 2908931 := bstep (se 1 (by rfl) ⟨2181698, by rfl⟩ : syracuseStep 2908931 = 4363397) B4363397
theorem B1939287 : Blo 1937435 1939287 := bstep (se 1 (by rfl) ⟨1454465, by rfl⟩ : syracuseStep 1939287 = 2908931) B2908931
theorem B4141829 : Blo 1937435 4141829 := bbase (se 4 (by rfl) ⟨388296, by rfl⟩ : syracuseStep 4141829 = 776593) (by norm_num)
theorem B2761219 : Blo 1937435 2761219 := bstep (se 1 (by rfl) ⟨2070914, by rfl⟩ : syracuseStep 2761219 = 4141829) B4141829
theorem B3681625 : Blo 1937435 3681625 := bstep (se 2 (by rfl) ⟨1380609, by rfl⟩ : syracuseStep 3681625 = 2761219) B2761219
theorem B4908833 : Blo 1937435 4908833 := bstep (se 2 (by rfl) ⟨1840812, by rfl⟩ : syracuseStep 4908833 = 3681625) B3681625
theorem B3272555 : Blo 1937435 3272555 := bstep (se 1 (by rfl) ⟨2454416, by rfl⟩ : syracuseStep 3272555 = 4908833) B4908833
theorem B2181703 : Blo 1937435 2181703 := bstep (se 1 (by rfl) ⟨1636277, by rfl⟩ : syracuseStep 2181703 = 3272555) B3272555
theorem B2908937 : Blo 1937435 2908937 := bstep (se 2 (by rfl) ⟨1090851, by rfl⟩ : syracuseStep 2908937 = 2181703) B2181703
theorem B1939291 : Blo 1937435 1939291 := bstep (se 1 (by rfl) ⟨1454468, by rfl⟩ : syracuseStep 1939291 = 2908937) B2908937
theorem B9817685 : Blo 1937435 9817685 := bbase (se 8 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 9817685 = 115051) (by norm_num)
theorem B6545123 : Blo 1937435 6545123 := bstep (se 1 (by rfl) ⟨4908842, by rfl⟩ : syracuseStep 6545123 = 9817685) B9817685
theorem B4363415 : Blo 1937435 4363415 := bstep (se 1 (by rfl) ⟨3272561, by rfl⟩ : syracuseStep 4363415 = 6545123) B6545123
theorem B2908943 : Blo 1937435 2908943 := bstep (se 1 (by rfl) ⟨2181707, by rfl⟩ : syracuseStep 2908943 = 4363415) B4363415
theorem B1939295 : Blo 1937435 1939295 := bstep (se 1 (by rfl) ⟨1454471, by rfl⟩ : syracuseStep 1939295 = 2908943) B2908943
theorem B2908949 : Blo 1937435 2908949 := bbase (se 6 (by rfl) ⟨68178, by rfl⟩ : syracuseStep 2908949 = 136357) (by norm_num)
theorem B1939299 : Blo 1937435 1939299 := bstep (se 1 (by rfl) ⟨1454474, by rfl⟩ : syracuseStep 1939299 = 2908949) B2908949
theorem B2948645 : Blo 1937435 2948645 := bbase (se 4 (by rfl) ⟨276435, by rfl⟩ : syracuseStep 2948645 = 552871) (by norm_num)
theorem B1965763 : Blo 1937435 1965763 := bstep (se 1 (by rfl) ⟨1474322, by rfl⟩ : syracuseStep 1965763 = 2948645) B2948645
theorem B2621017 : Blo 1937435 2621017 := bstep (se 2 (by rfl) ⟨982881, by rfl⟩ : syracuseStep 2621017 = 1965763) B1965763
theorem B13978757 : Blo 1937435 13978757 := bstep (se 4 (by rfl) ⟨1310508, by rfl⟩ : syracuseStep 13978757 = 2621017) B2621017
theorem B37276685 : Blo 1937435 37276685 := bstep (se 3 (by rfl) ⟨6989378, by rfl⟩ : syracuseStep 37276685 = 13978757) B13978757
theorem B24851123 : Blo 1937435 24851123 := bstep (se 1 (by rfl) ⟨18638342, by rfl⟩ : syracuseStep 24851123 = 37276685) B37276685
theorem B16567415 : Blo 1937435 16567415 := bstep (se 1 (by rfl) ⟨12425561, by rfl⟩ : syracuseStep 16567415 = 24851123) B24851123
theorem B11044943 : Blo 1937435 11044943 := bstep (se 1 (by rfl) ⟨8283707, by rfl⟩ : syracuseStep 11044943 = 16567415) B16567415
theorem B7363295 : Blo 1937435 7363295 := bstep (se 1 (by rfl) ⟨5522471, by rfl⟩ : syracuseStep 7363295 = 11044943) B11044943
theorem B4908863 : Blo 1937435 4908863 := bstep (se 1 (by rfl) ⟨3681647, by rfl⟩ : syracuseStep 4908863 = 7363295) B7363295
theorem B3272575 : Blo 1937435 3272575 := bstep (se 1 (by rfl) ⟨2454431, by rfl⟩ : syracuseStep 3272575 = 4908863) B4908863
theorem B4363433 : Blo 1937435 4363433 := bstep (se 2 (by rfl) ⟨1636287, by rfl⟩ : syracuseStep 4363433 = 3272575) B3272575
theorem B2908955 : Blo 1937435 2908955 := bstep (se 1 (by rfl) ⟨2181716, by rfl⟩ : syracuseStep 2908955 = 4363433) B4363433
theorem B1939303 : Blo 1937435 1939303 := bstep (se 1 (by rfl) ⟨1454477, by rfl⟩ : syracuseStep 1939303 = 2908955) B2908955
theorem B2181721 : Blo 1937435 2181721 := bbase (se 2 (by rfl) ⟨818145, by rfl⟩ : syracuseStep 2181721 = 1636291) (by norm_num)
theorem B2908961 : Blo 1937435 2908961 := bstep (se 2 (by rfl) ⟨1090860, by rfl⟩ : syracuseStep 2908961 = 2181721) B2181721
theorem B1939307 : Blo 1937435 1939307 := bstep (se 1 (by rfl) ⟨1454480, by rfl⟩ : syracuseStep 1939307 = 2908961) B2908961
theorem B2211493 : Blo 1937435 2211493 := bbase (se 4 (by rfl) ⟨207327, by rfl⟩ : syracuseStep 2211493 = 414655) (by norm_num)
theorem B2948657 : Blo 1937435 2948657 := bstep (se 2 (by rfl) ⟨1105746, by rfl⟩ : syracuseStep 2948657 = 2211493) B2211493
theorem B7863085 : Blo 1937435 7863085 := bstep (se 3 (by rfl) ⟨1474328, by rfl⟩ : syracuseStep 7863085 = 2948657) B2948657
theorem B10484113 : Blo 1937435 10484113 := bstep (se 2 (by rfl) ⟨3931542, by rfl⟩ : syracuseStep 10484113 = 7863085) B7863085
theorem B13978817 : Blo 1937435 13978817 := bstep (se 2 (by rfl) ⟨5242056, by rfl⟩ : syracuseStep 13978817 = 10484113) B10484113
theorem B9319211 : Blo 1937435 9319211 := bstep (se 1 (by rfl) ⟨6989408, by rfl⟩ : syracuseStep 9319211 = 13978817) B13978817
theorem B6212807 : Blo 1937435 6212807 := bstep (se 1 (by rfl) ⟨4659605, by rfl⟩ : syracuseStep 6212807 = 9319211) B9319211
theorem B4141871 : Blo 1937435 4141871 := bstep (se 1 (by rfl) ⟨3106403, by rfl⟩ : syracuseStep 4141871 = 6212807) B6212807
theorem B2761247 : Blo 1937435 2761247 := bstep (se 1 (by rfl) ⟨2070935, by rfl⟩ : syracuseStep 2761247 = 4141871) B4141871
theorem B7363325 : Blo 1937435 7363325 := bstep (se 3 (by rfl) ⟨1380623, by rfl⟩ : syracuseStep 7363325 = 2761247) B2761247
theorem B4908883 : Blo 1937435 4908883 := bstep (se 1 (by rfl) ⟨3681662, by rfl⟩ : syracuseStep 4908883 = 7363325) B7363325
theorem B6545177 : Blo 1937435 6545177 := bstep (se 2 (by rfl) ⟨2454441, by rfl⟩ : syracuseStep 6545177 = 4908883) B4908883
theorem B4363451 : Blo 1937435 4363451 := bstep (se 1 (by rfl) ⟨3272588, by rfl⟩ : syracuseStep 4363451 = 6545177) B6545177
theorem B2908967 : Blo 1937435 2908967 := bstep (se 1 (by rfl) ⟨2181725, by rfl⟩ : syracuseStep 2908967 = 4363451) B4363451
theorem B1939311 : Blo 1937435 1939311 := bstep (se 1 (by rfl) ⟨1454483, by rfl⟩ : syracuseStep 1939311 = 2908967) B2908967
theorem B2908973 : Blo 1937435 2908973 := bbase (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) (by norm_num)
theorem B1939315 : Blo 1937435 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B4363469 : Blo 1937435 4363469 := bbase (se 3 (by rfl) ⟨818150, by rfl⟩ : syracuseStep 4363469 = 1636301) (by norm_num)
theorem B2908979 : Blo 1937435 2908979 := bstep (se 1 (by rfl) ⟨2181734, by rfl⟩ : syracuseStep 2908979 = 4363469) B4363469
theorem B1939319 : Blo 1937435 1939319 := bstep (se 1 (by rfl) ⟨1454489, by rfl⟩ : syracuseStep 1939319 = 2908979) B2908979
theorem B2454457 : Blo 1937435 2454457 := bbase (se 2 (by rfl) ⟨920421, by rfl⟩ : syracuseStep 2454457 = 1840843) (by norm_num)
theorem B3272609 : Blo 1937435 3272609 := bstep (se 2 (by rfl) ⟨1227228, by rfl⟩ : syracuseStep 3272609 = 2454457) B2454457
theorem B2181739 : Blo 1937435 2181739 := bstep (se 1 (by rfl) ⟨1636304, by rfl⟩ : syracuseStep 2181739 = 3272609) B3272609
theorem B2908985 : Blo 1937435 2908985 := bstep (se 2 (by rfl) ⟨1090869, by rfl⟩ : syracuseStep 2908985 = 2181739) B2181739
theorem B1939323 : Blo 1937435 1939323 := bstep (se 1 (by rfl) ⟨1454492, by rfl⟩ : syracuseStep 1939323 = 2908985) B2908985
theorem B4975901 : Blo 1937435 4975901 := bbase (se 3 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 4975901 = 1865963) (by norm_num)
theorem B3317267 : Blo 1937435 3317267 := bstep (se 1 (by rfl) ⟨2487950, by rfl⟩ : syracuseStep 3317267 = 4975901) B4975901
theorem B2211511 : Blo 1937435 2211511 := bstep (se 1 (by rfl) ⟨1658633, by rfl⟩ : syracuseStep 2211511 = 3317267) B3317267
theorem B2948681 : Blo 1937435 2948681 := bstep (se 2 (by rfl) ⟨1105755, by rfl⟩ : syracuseStep 2948681 = 2211511) B2211511
theorem B7863149 : Blo 1937435 7863149 := bstep (se 3 (by rfl) ⟨1474340, by rfl⟩ : syracuseStep 7863149 = 2948681) B2948681
theorem B5242099 : Blo 1937435 5242099 := bstep (se 1 (by rfl) ⟨3931574, by rfl⟩ : syracuseStep 5242099 = 7863149) B7863149
theorem B6989465 : Blo 1937435 6989465 := bstep (se 2 (by rfl) ⟨2621049, by rfl⟩ : syracuseStep 6989465 = 5242099) B5242099
theorem B4659643 : Blo 1937435 4659643 := bstep (se 1 (by rfl) ⟨3494732, by rfl⟩ : syracuseStep 4659643 = 6989465) B6989465
theorem B6212857 : Blo 1937435 6212857 := bstep (se 2 (by rfl) ⟨2329821, by rfl⟩ : syracuseStep 6212857 = 4659643) B4659643
theorem B8283809 : Blo 1937435 8283809 := bstep (se 2 (by rfl) ⟨3106428, by rfl⟩ : syracuseStep 8283809 = 6212857) B6212857
theorem B22090157 : Blo 1937435 22090157 := bstep (se 3 (by rfl) ⟨4141904, by rfl⟩ : syracuseStep 22090157 = 8283809) B8283809
theorem B14726771 : Blo 1937435 14726771 := bstep (se 1 (by rfl) ⟨11045078, by rfl⟩ : syracuseStep 14726771 = 22090157) B22090157
theorem B9817847 : Blo 1937435 9817847 := bstep (se 1 (by rfl) ⟨7363385, by rfl⟩ : syracuseStep 9817847 = 14726771) B14726771
theorem B6545231 : Blo 1937435 6545231 := bstep (se 1 (by rfl) ⟨4908923, by rfl⟩ : syracuseStep 6545231 = 9817847) B9817847
theorem B4363487 : Blo 1937435 4363487 := bstep (se 1 (by rfl) ⟨3272615, by rfl⟩ : syracuseStep 4363487 = 6545231) B6545231
theorem B2908991 : Blo 1937435 2908991 := bstep (se 1 (by rfl) ⟨2181743, by rfl⟩ : syracuseStep 2908991 = 4363487) B4363487
theorem B1939327 : Blo 1937435 1939327 := bstep (se 1 (by rfl) ⟨1454495, by rfl⟩ : syracuseStep 1939327 = 2908991) B2908991
theorem B2908997 : Blo 1937435 2908997 := bbase (se 4 (by rfl) ⟨272718, by rfl⟩ : syracuseStep 2908997 = 545437) (by norm_num)
theorem B1939331 : Blo 1937435 1939331 := bstep (se 1 (by rfl) ⟨1454498, by rfl⟩ : syracuseStep 1939331 = 2908997) B2908997
theorem B3272629 : Blo 1937435 3272629 := bbase (se 5 (by rfl) ⟨153404, by rfl⟩ : syracuseStep 3272629 = 306809) (by norm_num)
theorem B4363505 : Blo 1937435 4363505 := bstep (se 2 (by rfl) ⟨1636314, by rfl⟩ : syracuseStep 4363505 = 3272629) B3272629
theorem B2909003 : Blo 1937435 2909003 := bstep (se 1 (by rfl) ⟨2181752, by rfl⟩ : syracuseStep 2909003 = 4363505) B4363505
theorem B1939335 : Blo 1937435 1939335 := bstep (se 1 (by rfl) ⟨1454501, by rfl⟩ : syracuseStep 1939335 = 2909003) B2909003
theorem B2181757 : Blo 1937435 2181757 := bbase (se 3 (by rfl) ⟨409079, by rfl⟩ : syracuseStep 2181757 = 818159) (by norm_num)
theorem B2909009 : Blo 1937435 2909009 := bstep (se 2 (by rfl) ⟨1090878, by rfl⟩ : syracuseStep 2909009 = 2181757) B2181757
theorem B1939339 : Blo 1937435 1939339 := bstep (se 1 (by rfl) ⟨1454504, by rfl⟩ : syracuseStep 1939339 = 2909009) B2909009
theorem B6545285 : Blo 1937435 6545285 := bbase (se 4 (by rfl) ⟨613620, by rfl⟩ : syracuseStep 6545285 = 1227241) (by norm_num)
theorem B4363523 : Blo 1937435 4363523 := bstep (se 1 (by rfl) ⟨3272642, by rfl⟩ : syracuseStep 4363523 = 6545285) B6545285
theorem B2909015 : Blo 1937435 2909015 := bstep (se 1 (by rfl) ⟨2181761, by rfl⟩ : syracuseStep 2909015 = 4363523) B4363523
theorem B1939343 : Blo 1937435 1939343 := bstep (se 1 (by rfl) ⟨1454507, by rfl⟩ : syracuseStep 1939343 = 2909015) B2909015
theorem B2909021 : Blo 1937435 2909021 := bbase (se 3 (by rfl) ⟨545441, by rfl⟩ : syracuseStep 2909021 = 1090883) (by norm_num)
theorem B1939347 : Blo 1937435 1939347 := bstep (se 1 (by rfl) ⟨1454510, by rfl⟩ : syracuseStep 1939347 = 2909021) B2909021
theorem B4363541 : Blo 1937435 4363541 := bbase (se 6 (by rfl) ⟨102270, by rfl⟩ : syracuseStep 4363541 = 204541) (by norm_num)
theorem B2909027 : Blo 1937435 2909027 := bstep (se 1 (by rfl) ⟨2181770, by rfl⟩ : syracuseStep 2909027 = 4363541) B4363541
theorem B1939351 : Blo 1937435 1939351 := bstep (se 1 (by rfl) ⟨1454513, by rfl⟩ : syracuseStep 1939351 = 2909027) B2909027
theorem B7363493 : Blo 1937435 7363493 := bbase (se 4 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 7363493 = 1380655) (by norm_num)
theorem B4908995 : Blo 1937435 4908995 := bstep (se 1 (by rfl) ⟨3681746, by rfl⟩ : syracuseStep 4908995 = 7363493) B7363493
theorem B3272663 : Blo 1937435 3272663 := bstep (se 1 (by rfl) ⟨2454497, by rfl⟩ : syracuseStep 3272663 = 4908995) B4908995
theorem B2181775 : Blo 1937435 2181775 := bstep (se 1 (by rfl) ⟨1636331, by rfl⟩ : syracuseStep 2181775 = 3272663) B3272663
theorem B2909033 : Blo 1937435 2909033 := bstep (se 2 (by rfl) ⟨1090887, by rfl⟩ : syracuseStep 2909033 = 2181775) B2181775
theorem B1939355 : Blo 1937435 1939355 := bstep (se 1 (by rfl) ⟨1454516, by rfl⟩ : syracuseStep 1939355 = 2909033) B2909033
theorem B4141973 : Blo 1937435 4141973 := bbase (se 6 (by rfl) ⟨97077, by rfl⟩ : syracuseStep 4141973 = 194155) (by norm_num)
theorem B11045261 : Blo 1937435 11045261 := bstep (se 3 (by rfl) ⟨2070986, by rfl⟩ : syracuseStep 11045261 = 4141973) B4141973
theorem B7363507 : Blo 1937435 7363507 := bstep (se 1 (by rfl) ⟨5522630, by rfl⟩ : syracuseStep 7363507 = 11045261) B11045261
theorem B9818009 : Blo 1937435 9818009 := bstep (se 2 (by rfl) ⟨3681753, by rfl⟩ : syracuseStep 9818009 = 7363507) B7363507
theorem B6545339 : Blo 1937435 6545339 := bstep (se 1 (by rfl) ⟨4909004, by rfl⟩ : syracuseStep 6545339 = 9818009) B9818009
theorem B4363559 : Blo 1937435 4363559 := bstep (se 1 (by rfl) ⟨3272669, by rfl⟩ : syracuseStep 4363559 = 6545339) B6545339
theorem B2909039 : Blo 1937435 2909039 := bstep (se 1 (by rfl) ⟨2181779, by rfl⟩ : syracuseStep 2909039 = 4363559) B4363559
theorem B1939359 : Blo 1937435 1939359 := bstep (se 1 (by rfl) ⟨1454519, by rfl⟩ : syracuseStep 1939359 = 2909039) B2909039
theorem B2909045 : Blo 1937435 2909045 := bbase (se 5 (by rfl) ⟨136361, by rfl⟩ : syracuseStep 2909045 = 272723) (by norm_num)
theorem B1939363 : Blo 1937435 1939363 := bstep (se 1 (by rfl) ⟨1454522, by rfl⟩ : syracuseStep 1939363 = 2909045) B2909045
theorem B2211557 : Blo 1937435 2211557 := bbase (se 4 (by rfl) ⟨207333, by rfl⟩ : syracuseStep 2211557 = 414667) (by norm_num)
theorem B5897485 : Blo 1937435 5897485 := bstep (se 3 (by rfl) ⟨1105778, by rfl⟩ : syracuseStep 5897485 = 2211557) B2211557
theorem B7863313 : Blo 1937435 7863313 := bstep (se 2 (by rfl) ⟨2948742, by rfl⟩ : syracuseStep 7863313 = 5897485) B5897485
theorem B10484417 : Blo 1937435 10484417 := bstep (se 2 (by rfl) ⟨3931656, by rfl⟩ : syracuseStep 10484417 = 7863313) B7863313
theorem B6989611 : Blo 1937435 6989611 := bstep (se 1 (by rfl) ⟨5242208, by rfl⟩ : syracuseStep 6989611 = 10484417) B10484417
theorem B9319481 : Blo 1937435 9319481 := bstep (se 2 (by rfl) ⟨3494805, by rfl⟩ : syracuseStep 9319481 = 6989611) B6989611
theorem B6212987 : Blo 1937435 6212987 := bstep (se 1 (by rfl) ⟨4659740, by rfl⟩ : syracuseStep 6212987 = 9319481) B9319481
theorem B4141991 : Blo 1937435 4141991 := bstep (se 1 (by rfl) ⟨3106493, by rfl⟩ : syracuseStep 4141991 = 6212987) B6212987
theorem B2761327 : Blo 1937435 2761327 := bstep (se 1 (by rfl) ⟨2070995, by rfl⟩ : syracuseStep 2761327 = 4141991) B4141991
theorem B3681769 : Blo 1937435 3681769 := bstep (se 2 (by rfl) ⟨1380663, by rfl⟩ : syracuseStep 3681769 = 2761327) B2761327
theorem B4909025 : Blo 1937435 4909025 := bstep (se 2 (by rfl) ⟨1840884, by rfl⟩ : syracuseStep 4909025 = 3681769) B3681769
theorem B3272683 : Blo 1937435 3272683 := bstep (se 1 (by rfl) ⟨2454512, by rfl⟩ : syracuseStep 3272683 = 4909025) B4909025
theorem B4363577 : Blo 1937435 4363577 := bstep (se 2 (by rfl) ⟨1636341, by rfl⟩ : syracuseStep 4363577 = 3272683) B3272683
theorem B2909051 : Blo 1937435 2909051 := bstep (se 1 (by rfl) ⟨2181788, by rfl⟩ : syracuseStep 2909051 = 4363577) B4363577
theorem B1939367 : Blo 1937435 1939367 := bstep (se 1 (by rfl) ⟨1454525, by rfl⟩ : syracuseStep 1939367 = 2909051) B2909051
theorem B2181793 : Blo 1937435 2181793 := bbase (se 2 (by rfl) ⟨818172, by rfl⟩ : syracuseStep 2181793 = 1636345) (by norm_num)
theorem B2909057 : Blo 1937435 2909057 := bstep (se 2 (by rfl) ⟨1090896, by rfl⟩ : syracuseStep 2909057 = 2181793) B2181793
theorem B1939371 : Blo 1937435 1939371 := bstep (se 1 (by rfl) ⟨1454528, by rfl⟩ : syracuseStep 1939371 = 2909057) B2909057
theorem B4909045 : Blo 1937435 4909045 := bbase (se 5 (by rfl) ⟨230111, by rfl⟩ : syracuseStep 4909045 = 460223) (by norm_num)
theorem B6545393 : Blo 1937435 6545393 := bstep (se 2 (by rfl) ⟨2454522, by rfl⟩ : syracuseStep 6545393 = 4909045) B4909045
theorem B4363595 : Blo 1937435 4363595 := bstep (se 1 (by rfl) ⟨3272696, by rfl⟩ : syracuseStep 4363595 = 6545393) B6545393
theorem B2909063 : Blo 1937435 2909063 := bstep (se 1 (by rfl) ⟨2181797, by rfl⟩ : syracuseStep 2909063 = 4363595) B4363595
theorem B1939375 : Blo 1937435 1939375 := bstep (se 1 (by rfl) ⟨1454531, by rfl⟩ : syracuseStep 1939375 = 2909063) B2909063
theorem B2909069 : Blo 1937435 2909069 := bbase (se 3 (by rfl) ⟨545450, by rfl⟩ : syracuseStep 2909069 = 1090901) (by norm_num)
theorem B1939379 : Blo 1937435 1939379 := bstep (se 1 (by rfl) ⟨1454534, by rfl⟩ : syracuseStep 1939379 = 2909069) B2909069
theorem B4363613 : Blo 1937435 4363613 := bbase (se 3 (by rfl) ⟨818177, by rfl⟩ : syracuseStep 4363613 = 1636355) (by norm_num)
theorem B2909075 : Blo 1937435 2909075 := bstep (se 1 (by rfl) ⟨2181806, by rfl⟩ : syracuseStep 2909075 = 4363613) B4363613
theorem B1939383 : Blo 1937435 1939383 := bstep (se 1 (by rfl) ⟨1454537, by rfl⟩ : syracuseStep 1939383 = 2909075) B2909075
theorem B3272717 : Blo 1937435 3272717 := bbase (se 3 (by rfl) ⟨613634, by rfl⟩ : syracuseStep 3272717 = 1227269) (by norm_num)
theorem B2181811 : Blo 1937435 2181811 := bstep (se 1 (by rfl) ⟨1636358, by rfl⟩ : syracuseStep 2181811 = 3272717) B3272717
theorem B2909081 : Blo 1937435 2909081 := bstep (se 2 (by rfl) ⟨1090905, by rfl⟩ : syracuseStep 2909081 = 2181811) B2181811
theorem B1939387 : Blo 1937435 1939387 := bstep (se 1 (by rfl) ⟨1454540, by rfl⟩ : syracuseStep 1939387 = 2909081) B2909081
theorem B4659797 : Blo 1937435 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B3106531 : Blo 1937435 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B16568165 : Blo 1937435 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B11045443 : Blo 1937435 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B14727257 : Blo 1937435 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B9818171 : Blo 1937435 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B6545447 : Blo 1937435 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B4363631 : Blo 1937435 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B2909087 : Blo 1937435 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B1939391 : Blo 1937435 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B2909093 : Blo 1937435 2909093 := bbase (se 4 (by rfl) ⟨272727, by rfl⟩ : syracuseStep 2909093 = 545455) (by norm_num)
theorem B1939395 : Blo 1937435 1939395 := bstep (se 1 (by rfl) ⟨1454546, by rfl⟩ : syracuseStep 1939395 = 2909093) B2909093
theorem B2454553 : Blo 1937435 2454553 := bbase (se 2 (by rfl) ⟨920457, by rfl⟩ : syracuseStep 2454553 = 1840915) (by norm_num)
theorem B3272737 : Blo 1937435 3272737 := bstep (se 2 (by rfl) ⟨1227276, by rfl⟩ : syracuseStep 3272737 = 2454553) B2454553
theorem B4363649 : Blo 1937435 4363649 := bstep (se 2 (by rfl) ⟨1636368, by rfl⟩ : syracuseStep 4363649 = 3272737) B3272737
theorem B2909099 : Blo 1937435 2909099 := bstep (se 1 (by rfl) ⟨2181824, by rfl⟩ : syracuseStep 2909099 = 4363649) B4363649
theorem B1939399 : Blo 1937435 1939399 := bstep (se 1 (by rfl) ⟨1454549, by rfl⟩ : syracuseStep 1939399 = 2909099) B2909099
theorem B2181829 : Blo 1937435 2181829 := bbase (se 4 (by rfl) ⟨204546, by rfl⟩ : syracuseStep 2181829 = 409093) (by norm_num)
theorem B2909105 : Blo 1937435 2909105 := bstep (se 2 (by rfl) ⟨1090914, by rfl⟩ : syracuseStep 2909105 = 2181829) B2181829
theorem B1939403 : Blo 1937435 1939403 := bstep (se 1 (by rfl) ⟨1454552, by rfl⟩ : syracuseStep 1939403 = 2909105) B2909105
theorem B3681845 : Blo 1937435 3681845 := bbase (se 5 (by rfl) ⟨172586, by rfl⟩ : syracuseStep 3681845 = 345173) (by norm_num)
theorem B2454563 : Blo 1937435 2454563 := bstep (se 1 (by rfl) ⟨1840922, by rfl⟩ : syracuseStep 2454563 = 3681845) B3681845
theorem B6545501 : Blo 1937435 6545501 := bstep (se 3 (by rfl) ⟨1227281, by rfl⟩ : syracuseStep 6545501 = 2454563) B2454563
theorem B4363667 : Blo 1937435 4363667 := bstep (se 1 (by rfl) ⟨3272750, by rfl⟩ : syracuseStep 4363667 = 6545501) B6545501
theorem B2909111 : Blo 1937435 2909111 := bstep (se 1 (by rfl) ⟨2181833, by rfl⟩ : syracuseStep 2909111 = 4363667) B4363667
theorem B1939407 : Blo 1937435 1939407 := bstep (se 1 (by rfl) ⟨1454555, by rfl⟩ : syracuseStep 1939407 = 2909111) B2909111
theorem B2909117 : Blo 1937435 2909117 := bbase (se 3 (by rfl) ⟨545459, by rfl⟩ : syracuseStep 2909117 = 1090919) (by norm_num)
theorem B1939411 : Blo 1937435 1939411 := bstep (se 1 (by rfl) ⟨1454558, by rfl⟩ : syracuseStep 1939411 = 2909117) B2909117
theorem B4363685 : Blo 1937435 4363685 := bbase (se 4 (by rfl) ⟨409095, by rfl⟩ : syracuseStep 4363685 = 818191) (by norm_num)
theorem B2909123 : Blo 1937435 2909123 := bstep (se 1 (by rfl) ⟨2181842, by rfl⟩ : syracuseStep 2909123 = 4363685) B4363685
theorem B1939415 : Blo 1937435 1939415 := bstep (se 1 (by rfl) ⟨1454561, by rfl⟩ : syracuseStep 1939415 = 2909123) B2909123
theorem B4909157 : Blo 1937435 4909157 := bbase (se 4 (by rfl) ⟨460233, by rfl⟩ : syracuseStep 4909157 = 920467) (by norm_num)
theorem B3272771 : Blo 1937435 3272771 := bstep (se 1 (by rfl) ⟨2454578, by rfl⟩ : syracuseStep 3272771 = 4909157) B4909157
theorem B2181847 : Blo 1937435 2181847 := bstep (se 1 (by rfl) ⟨1636385, by rfl⟩ : syracuseStep 2181847 = 3272771) B3272771
theorem B2909129 : Blo 1937435 2909129 := bstep (se 2 (by rfl) ⟨1090923, by rfl⟩ : syracuseStep 2909129 = 2181847) B2181847
theorem B1939419 : Blo 1937435 1939419 := bstep (se 1 (by rfl) ⟨1454564, by rfl⟩ : syracuseStep 1939419 = 2909129) B2909129
theorem B6989813 : Blo 1937435 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B4659875 : Blo 1937435 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B3106583 : Blo 1937435 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B2071055 : Blo 1937435 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B5522813 : Blo 1937435 5522813 := bstep (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) B2071055
theorem B3681875 : Blo 1937435 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B9818333 : Blo 1937435 9818333 := bstep (se 3 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 9818333 = 3681875) B3681875
theorem B6545555 : Blo 1937435 6545555 := bstep (se 1 (by rfl) ⟨4909166, by rfl⟩ : syracuseStep 6545555 = 9818333) B9818333
theorem B4363703 : Blo 1937435 4363703 := bstep (se 1 (by rfl) ⟨3272777, by rfl⟩ : syracuseStep 4363703 = 6545555) B6545555
theorem B2909135 : Blo 1937435 2909135 := bstep (se 1 (by rfl) ⟨2181851, by rfl⟩ : syracuseStep 2909135 = 4363703) B4363703
theorem B1939423 : Blo 1937435 1939423 := bstep (se 1 (by rfl) ⟨1454567, by rfl⟩ : syracuseStep 1939423 = 2909135) B2909135
theorem B2909141 : Blo 1937435 2909141 := bbase (se 7 (by rfl) ⟨34091, by rfl⟩ : syracuseStep 2909141 = 68183) (by norm_num)
theorem B1939427 : Blo 1937435 1939427 := bstep (se 1 (by rfl) ⟨1454570, by rfl⟩ : syracuseStep 1939427 = 2909141) B2909141
theorem B7363781 : Blo 1937435 7363781 := bbase (se 4 (by rfl) ⟨690354, by rfl⟩ : syracuseStep 7363781 = 1380709) (by norm_num)
theorem B4909187 : Blo 1937435 4909187 := bstep (se 1 (by rfl) ⟨3681890, by rfl⟩ : syracuseStep 4909187 = 7363781) B7363781
theorem B3272791 : Blo 1937435 3272791 := bstep (se 1 (by rfl) ⟨2454593, by rfl⟩ : syracuseStep 3272791 = 4909187) B4909187
theorem B4363721 : Blo 1937435 4363721 := bstep (se 2 (by rfl) ⟨1636395, by rfl⟩ : syracuseStep 4363721 = 3272791) B3272791
theorem B2909147 : Blo 1937435 2909147 := bstep (se 1 (by rfl) ⟨2181860, by rfl⟩ : syracuseStep 2909147 = 4363721) B4363721
theorem B1939431 : Blo 1937435 1939431 := bstep (se 1 (by rfl) ⟨1454573, by rfl⟩ : syracuseStep 1939431 = 2909147) B2909147
theorem B2181865 : Blo 1937435 2181865 := bbase (se 2 (by rfl) ⟨818199, by rfl⟩ : syracuseStep 2181865 = 1636399) (by norm_num)
theorem B2909153 : Blo 1937435 2909153 := bstep (se 2 (by rfl) ⟨1090932, by rfl⟩ : syracuseStep 2909153 = 2181865) B2181865
theorem B1939435 : Blo 1937435 1939435 := bstep (se 1 (by rfl) ⟨1454576, by rfl⟩ : syracuseStep 1939435 = 2909153) B2909153
theorem C0 (j : ℕ) (h1 : 484358 ≤ j) (h2 : j ≤ 484858) : Blo 1937435 (4 * j + 3) := by
  interval_cases j
  · exact B1937435
  · exact B1937439
  · exact B1937443
  · exact B1937447
  · exact B1937451
  · exact B1937455
  · exact B1937459
  · exact B1937463
  · exact B1937467
  · exact B1937471
  · exact B1937475
  · exact B1937479
  · exact B1937483
  · exact B1937487
  · exact B1937491
  · exact B1937495
  · exact B1937499
  · exact B1937503
  · exact B1937507
  · exact B1937511
  · exact B1937515
  · exact B1937519
  · exact B1937523
  · exact B1937527
  · exact B1937531
  · exact B1937535
  · exact B1937539
  · exact B1937543
  · exact B1937547
  · exact B1937551
  · exact B1937555
  · exact B1937559
  · exact B1937563
  · exact B1937567
  · exact B1937571
  · exact B1937575
  · exact B1937579
  · exact B1937583
  · exact B1937587
  · exact B1937591
  · exact B1937595
  · exact B1937599
  · exact B1937603
  · exact B1937607
  · exact B1937611
  · exact B1937615
  · exact B1937619
  · exact B1937623
  · exact B1937627
  · exact B1937631
  · exact B1937635
  · exact B1937639
  · exact B1937643
  · exact B1937647
  · exact B1937651
  · exact B1937655
  · exact B1937659
  · exact B1937663
  · exact B1937667
  · exact B1937671
  · exact B1937675
  · exact B1937679
  · exact B1937683
  · exact B1937687
  · exact B1937691
  · exact B1937695
  · exact B1937699
  · exact B1937703
  · exact B1937707
  · exact B1937711
  · exact B1937715
  · exact B1937719
  · exact B1937723
  · exact B1937727
  · exact B1937731
  · exact B1937735
  · exact B1937739
  · exact B1937743
  · exact B1937747
  · exact B1937751
  · exact B1937755
  · exact B1937759
  · exact B1937763
  · exact B1937767
  · exact B1937771
  · exact B1937775
  · exact B1937779
  · exact B1937783
  · exact B1937787
  · exact B1937791
  · exact B1937795
  · exact B1937799
  · exact B1937803
  · exact B1937807
  · exact B1937811
  · exact B1937815
  · exact B1937819
  · exact B1937823
  · exact B1937827
  · exact B1937831
  · exact B1937835
  · exact B1937839
  · exact B1937843
  · exact B1937847
  · exact B1937851
  · exact B1937855
  · exact B1937859
  · exact B1937863
  · exact B1937867
  · exact B1937871
  · exact B1937875
  · exact B1937879
  · exact B1937883
  · exact B1937887
  · exact B1937891
  · exact B1937895
  · exact B1937899
  · exact B1937903
  · exact B1937907
  · exact B1937911
  · exact B1937915
  · exact B1937919
  · exact B1937923
  · exact B1937927
  · exact B1937931
  · exact B1937935
  · exact B1937939
  · exact B1937943
  · exact B1937947
  · exact B1937951
  · exact B1937955
  · exact B1937959
  · exact B1937963
  · exact B1937967
  · exact B1937971
  · exact B1937975
  · exact B1937979
  · exact B1937983
  · exact B1937987
  · exact B1937991
  · exact B1937995
  · exact B1937999
  · exact B1938003
  · exact B1938007
  · exact B1938011
  · exact B1938015
  · exact B1938019
  · exact B1938023
  · exact B1938027
  · exact B1938031
  · exact B1938035
  · exact B1938039
  · exact B1938043
  · exact B1938047
  · exact B1938051
  · exact B1938055
  · exact B1938059
  · exact B1938063
  · exact B1938067
  · exact B1938071
  · exact B1938075
  · exact B1938079
  · exact B1938083
  · exact B1938087
  · exact B1938091
  · exact B1938095
  · exact B1938099
  · exact B1938103
  · exact B1938107
  · exact B1938111
  · exact B1938115
  · exact B1938119
  · exact B1938123
  · exact B1938127
  · exact B1938131
  · exact B1938135
  · exact B1938139
  · exact B1938143
  · exact B1938147
  · exact B1938151
  · exact B1938155
  · exact B1938159
  · exact B1938163
  · exact B1938167
  · exact B1938171
  · exact B1938175
  · exact B1938179
  · exact B1938183
  · exact B1938187
  · exact B1938191
  · exact B1938195
  · exact B1938199
  · exact B1938203
  · exact B1938207
  · exact B1938211
  · exact B1938215
  · exact B1938219
  · exact B1938223
  · exact B1938227
  · exact B1938231
  · exact B1938235
  · exact B1938239
  · exact B1938243
  · exact B1938247
  · exact B1938251
  · exact B1938255
  · exact B1938259
  · exact B1938263
  · exact B1938267
  · exact B1938271
  · exact B1938275
  · exact B1938279
  · exact B1938283
  · exact B1938287
  · exact B1938291
  · exact B1938295
  · exact B1938299
  · exact B1938303
  · exact B1938307
  · exact B1938311
  · exact B1938315
  · exact B1938319
  · exact B1938323
  · exact B1938327
  · exact B1938331
  · exact B1938335
  · exact B1938339
  · exact B1938343
  · exact B1938347
  · exact B1938351
  · exact B1938355
  · exact B1938359
  · exact B1938363
  · exact B1938367
  · exact B1938371
  · exact B1938375
  · exact B1938379
  · exact B1938383
  · exact B1938387
  · exact B1938391
  · exact B1938395
  · exact B1938399
  · exact B1938403
  · exact B1938407
  · exact B1938411
  · exact B1938415
  · exact B1938419
  · exact B1938423
  · exact B1938427
  · exact B1938431
  · exact B1938435
  · exact B1938439
  · exact B1938443
  · exact B1938447
  · exact B1938451
  · exact B1938455
  · exact B1938459
  · exact B1938463
  · exact B1938467
  · exact B1938471
  · exact B1938475
  · exact B1938479
  · exact B1938483
  · exact B1938487
  · exact B1938491
  · exact B1938495
  · exact B1938499
  · exact B1938503
  · exact B1938507
  · exact B1938511
  · exact B1938515
  · exact B1938519
  · exact B1938523
  · exact B1938527
  · exact B1938531
  · exact B1938535
  · exact B1938539
  · exact B1938543
  · exact B1938547
  · exact B1938551
  · exact B1938555
  · exact B1938559
  · exact B1938563
  · exact B1938567
  · exact B1938571
  · exact B1938575
  · exact B1938579
  · exact B1938583
  · exact B1938587
  · exact B1938591
  · exact B1938595
  · exact B1938599
  · exact B1938603
  · exact B1938607
  · exact B1938611
  · exact B1938615
  · exact B1938619
  · exact B1938623
  · exact B1938627
  · exact B1938631
  · exact B1938635
  · exact B1938639
  · exact B1938643
  · exact B1938647
  · exact B1938651
  · exact B1938655
  · exact B1938659
  · exact B1938663
  · exact B1938667
  · exact B1938671
  · exact B1938675
  · exact B1938679
  · exact B1938683
  · exact B1938687
  · exact B1938691
  · exact B1938695
  · exact B1938699
  · exact B1938703
  · exact B1938707
  · exact B1938711
  · exact B1938715
  · exact B1938719
  · exact B1938723
  · exact B1938727
  · exact B1938731
  · exact B1938735
  · exact B1938739
  · exact B1938743
  · exact B1938747
  · exact B1938751
  · exact B1938755
  · exact B1938759
  · exact B1938763
  · exact B1938767
  · exact B1938771
  · exact B1938775
  · exact B1938779
  · exact B1938783
  · exact B1938787
  · exact B1938791
  · exact B1938795
  · exact B1938799
  · exact B1938803
  · exact B1938807
  · exact B1938811
  · exact B1938815
  · exact B1938819
  · exact B1938823
  · exact B1938827
  · exact B1938831
  · exact B1938835
  · exact B1938839
  · exact B1938843
  · exact B1938847
  · exact B1938851
  · exact B1938855
  · exact B1938859
  · exact B1938863
  · exact B1938867
  · exact B1938871
  · exact B1938875
  · exact B1938879
  · exact B1938883
  · exact B1938887
  · exact B1938891
  · exact B1938895
  · exact B1938899
  · exact B1938903
  · exact B1938907
  · exact B1938911
  · exact B1938915
  · exact B1938919
  · exact B1938923
  · exact B1938927
  · exact B1938931
  · exact B1938935
  · exact B1938939
  · exact B1938943
  · exact B1938947
  · exact B1938951
  · exact B1938955
  · exact B1938959
  · exact B1938963
  · exact B1938967
  · exact B1938971
  · exact B1938975
  · exact B1938979
  · exact B1938983
  · exact B1938987
  · exact B1938991
  · exact B1938995
  · exact B1938999
  · exact B1939003
  · exact B1939007
  · exact B1939011
  · exact B1939015
  · exact B1939019
  · exact B1939023
  · exact B1939027
  · exact B1939031
  · exact B1939035
  · exact B1939039
  · exact B1939043
  · exact B1939047
  · exact B1939051
  · exact B1939055
  · exact B1939059
  · exact B1939063
  · exact B1939067
  · exact B1939071
  · exact B1939075
  · exact B1939079
  · exact B1939083
  · exact B1939087
  · exact B1939091
  · exact B1939095
  · exact B1939099
  · exact B1939103
  · exact B1939107
  · exact B1939111
  · exact B1939115
  · exact B1939119
  · exact B1939123
  · exact B1939127
  · exact B1939131
  · exact B1939135
  · exact B1939139
  · exact B1939143
  · exact B1939147
  · exact B1939151
  · exact B1939155
  · exact B1939159
  · exact B1939163
  · exact B1939167
  · exact B1939171
  · exact B1939175
  · exact B1939179
  · exact B1939183
  · exact B1939187
  · exact B1939191
  · exact B1939195
  · exact B1939199
  · exact B1939203
  · exact B1939207
  · exact B1939211
  · exact B1939215
  · exact B1939219
  · exact B1939223
  · exact B1939227
  · exact B1939231
  · exact B1939235
  · exact B1939239
  · exact B1939243
  · exact B1939247
  · exact B1939251
  · exact B1939255
  · exact B1939259
  · exact B1939263
  · exact B1939267
  · exact B1939271
  · exact B1939275
  · exact B1939279
  · exact B1939283
  · exact B1939287
  · exact B1939291
  · exact B1939295
  · exact B1939299
  · exact B1939303
  · exact B1939307
  · exact B1939311
  · exact B1939315
  · exact B1939319
  · exact B1939323
  · exact B1939327
  · exact B1939331
  · exact B1939335
  · exact B1939339
  · exact B1939343
  · exact B1939347
  · exact B1939351
  · exact B1939355
  · exact B1939359
  · exact B1939363
  · exact B1939367
  · exact B1939371
  · exact B1939375
  · exact B1939379
  · exact B1939383
  · exact B1939387
  · exact B1939391
  · exact B1939395
  · exact B1939399
  · exact B1939403
  · exact B1939407
  · exact B1939411
  · exact B1939415
  · exact B1939419
  · exact B1939423
  · exact B1939427
  · exact B1939431
  · exact B1939435
theorem solution (m : ℕ) (hlo : 1937435 ≤ m) (hhi : m ≤ 1939435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 484358 ≤ j := by omega
    have hj2 : j ≤ 484858 := by omega
    have hb : Blo 1937435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
