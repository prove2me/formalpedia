-- Prove2me | solution 1 for syracuse_descends_range_2303435_2305435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:50:02.276719+00:00
-- url     : https://prove2.me/submissions/0d978b64-c51e-4892-bd50-53b5dd2c3ffb

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

theorem B2591365 : Blo 2303435 2591365 := bbase (se 4 (by rfl) ⟨242940, by rfl⟩ : syracuseStep 2591365 = 485881) (by norm_num)
theorem B3455153 : Blo 2303435 3455153 := bstep (se 2 (by rfl) ⟨1295682, by rfl⟩ : syracuseStep 3455153 = 2591365) B2591365
theorem B2303435 : Blo 2303435 2303435 := bstep (se 1 (by rfl) ⟨1727576, by rfl⟩ : syracuseStep 2303435 = 3455153) B3455153
theorem B7379333 : Blo 2303435 7379333 := bbase (se 4 (by rfl) ⟨691812, by rfl⟩ : syracuseStep 7379333 = 1383625) (by norm_num)
theorem B4919555 : Blo 2303435 4919555 := bstep (se 1 (by rfl) ⟨3689666, by rfl⟩ : syracuseStep 4919555 = 7379333) B7379333
theorem B3279703 : Blo 2303435 3279703 := bstep (se 1 (by rfl) ⟨2459777, by rfl⟩ : syracuseStep 3279703 = 4919555) B4919555
theorem B4372937 : Blo 2303435 4372937 := bstep (se 2 (by rfl) ⟨1639851, by rfl⟩ : syracuseStep 4372937 = 3279703) B3279703
theorem B2915291 : Blo 2303435 2915291 := bstep (se 1 (by rfl) ⟨2186468, by rfl⟩ : syracuseStep 2915291 = 4372937) B4372937
theorem B7774109 : Blo 2303435 7774109 := bstep (se 3 (by rfl) ⟨1457645, by rfl⟩ : syracuseStep 7774109 = 2915291) B2915291
theorem B5182739 : Blo 2303435 5182739 := bstep (se 1 (by rfl) ⟨3887054, by rfl⟩ : syracuseStep 5182739 = 7774109) B7774109
theorem B3455159 : Blo 2303435 3455159 := bstep (se 1 (by rfl) ⟨2591369, by rfl⟩ : syracuseStep 3455159 = 5182739) B5182739
theorem B2303439 : Blo 2303435 2303439 := bstep (se 1 (by rfl) ⟨1727579, by rfl⟩ : syracuseStep 2303439 = 3455159) B3455159
theorem B3455165 : Blo 2303435 3455165 := bbase (se 3 (by rfl) ⟨647843, by rfl⟩ : syracuseStep 3455165 = 1295687) (by norm_num)
theorem B2303443 : Blo 2303435 2303443 := bstep (se 1 (by rfl) ⟨1727582, by rfl⟩ : syracuseStep 2303443 = 3455165) B3455165
theorem B5182757 : Blo 2303435 5182757 := bbase (se 4 (by rfl) ⟨485883, by rfl⟩ : syracuseStep 5182757 = 971767) (by norm_num)
theorem B3455171 : Blo 2303435 3455171 := bstep (se 1 (by rfl) ⟨2591378, by rfl⟩ : syracuseStep 3455171 = 5182757) B5182757
theorem B2303447 : Blo 2303435 2303447 := bstep (se 1 (by rfl) ⟨1727585, by rfl⟩ : syracuseStep 2303447 = 3455171) B3455171
theorem B5830613 : Blo 2303435 5830613 := bbase (se 7 (by rfl) ⟨68327, by rfl⟩ : syracuseStep 5830613 = 136655) (by norm_num)
theorem B3887075 : Blo 2303435 3887075 := bstep (se 1 (by rfl) ⟨2915306, by rfl⟩ : syracuseStep 3887075 = 5830613) B5830613
theorem B2591383 : Blo 2303435 2591383 := bstep (se 1 (by rfl) ⟨1943537, by rfl⟩ : syracuseStep 2591383 = 3887075) B3887075
theorem B3455177 : Blo 2303435 3455177 := bstep (se 2 (by rfl) ⟨1295691, by rfl⟩ : syracuseStep 3455177 = 2591383) B2591383
theorem B2303451 : Blo 2303435 2303451 := bstep (se 1 (by rfl) ⟨1727588, by rfl⟩ : syracuseStep 2303451 = 3455177) B3455177
theorem B3502325 : Blo 2303435 3502325 := bbase (se 5 (by rfl) ⟨164171, by rfl⟩ : syracuseStep 3502325 = 328343) (by norm_num)
theorem B9339533 : Blo 2303435 9339533 := bstep (se 3 (by rfl) ⟨1751162, by rfl⟩ : syracuseStep 9339533 = 3502325) B3502325
theorem B6226355 : Blo 2303435 6226355 := bstep (se 1 (by rfl) ⟨4669766, by rfl⟩ : syracuseStep 6226355 = 9339533) B9339533
theorem B16603613 : Blo 2303435 16603613 := bstep (se 3 (by rfl) ⟨3113177, by rfl⟩ : syracuseStep 16603613 = 6226355) B6226355
theorem B11069075 : Blo 2303435 11069075 := bstep (se 1 (by rfl) ⟨8301806, by rfl⟩ : syracuseStep 11069075 = 16603613) B16603613
theorem B7379383 : Blo 2303435 7379383 := bstep (se 1 (by rfl) ⟨5534537, by rfl⟩ : syracuseStep 7379383 = 11069075) B11069075
theorem B9839177 : Blo 2303435 9839177 := bstep (se 2 (by rfl) ⟨3689691, by rfl⟩ : syracuseStep 9839177 = 7379383) B7379383
theorem B6559451 : Blo 2303435 6559451 := bstep (se 1 (by rfl) ⟨4919588, by rfl⟩ : syracuseStep 6559451 = 9839177) B9839177
theorem B4372967 : Blo 2303435 4372967 := bstep (se 1 (by rfl) ⟨3279725, by rfl⟩ : syracuseStep 4372967 = 6559451) B6559451
theorem B11661245 : Blo 2303435 11661245 := bstep (se 3 (by rfl) ⟨2186483, by rfl⟩ : syracuseStep 11661245 = 4372967) B4372967
theorem B7774163 : Blo 2303435 7774163 := bstep (se 1 (by rfl) ⟨5830622, by rfl⟩ : syracuseStep 7774163 = 11661245) B11661245
theorem B5182775 : Blo 2303435 5182775 := bstep (se 1 (by rfl) ⟨3887081, by rfl⟩ : syracuseStep 5182775 = 7774163) B7774163
theorem B3455183 : Blo 2303435 3455183 := bstep (se 1 (by rfl) ⟨2591387, by rfl⟩ : syracuseStep 3455183 = 5182775) B5182775
theorem B2303455 : Blo 2303435 2303455 := bstep (se 1 (by rfl) ⟨1727591, by rfl⟩ : syracuseStep 2303455 = 3455183) B3455183
theorem B3455189 : Blo 2303435 3455189 := bbase (se 7 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 3455189 = 80981) (by norm_num)
theorem B2303459 : Blo 2303435 2303459 := bstep (se 1 (by rfl) ⟨1727594, by rfl⟩ : syracuseStep 2303459 = 3455189) B3455189
theorem B7004677 : Blo 2303435 7004677 := bbase (se 4 (by rfl) ⟨656688, by rfl⟩ : syracuseStep 7004677 = 1313377) (by norm_num)
theorem B9339569 : Blo 2303435 9339569 := bstep (se 2 (by rfl) ⟨3502338, by rfl⟩ : syracuseStep 9339569 = 7004677) B7004677
theorem B6226379 : Blo 2303435 6226379 := bstep (se 1 (by rfl) ⟨4669784, by rfl⟩ : syracuseStep 6226379 = 9339569) B9339569
theorem B4150919 : Blo 2303435 4150919 := bstep (se 1 (by rfl) ⟨3113189, by rfl⟩ : syracuseStep 4150919 = 6226379) B6226379
theorem B2767279 : Blo 2303435 2767279 := bstep (se 1 (by rfl) ⟨2075459, by rfl⟩ : syracuseStep 2767279 = 4150919) B4150919
theorem B3689705 : Blo 2303435 3689705 := bstep (se 2 (by rfl) ⟨1383639, by rfl⟩ : syracuseStep 3689705 = 2767279) B2767279
theorem B2459803 : Blo 2303435 2459803 := bstep (se 1 (by rfl) ⟨1844852, by rfl⟩ : syracuseStep 2459803 = 3689705) B3689705
theorem B3279737 : Blo 2303435 3279737 := bstep (se 2 (by rfl) ⟨1229901, by rfl⟩ : syracuseStep 3279737 = 2459803) B2459803
theorem B8745965 : Blo 2303435 8745965 := bstep (se 3 (by rfl) ⟨1639868, by rfl⟩ : syracuseStep 8745965 = 3279737) B3279737
theorem B5830643 : Blo 2303435 5830643 := bstep (se 1 (by rfl) ⟨4372982, by rfl⟩ : syracuseStep 5830643 = 8745965) B8745965
theorem B3887095 : Blo 2303435 3887095 := bstep (se 1 (by rfl) ⟨2915321, by rfl⟩ : syracuseStep 3887095 = 5830643) B5830643
theorem B5182793 : Blo 2303435 5182793 := bstep (se 2 (by rfl) ⟨1943547, by rfl⟩ : syracuseStep 5182793 = 3887095) B3887095
theorem B3455195 : Blo 2303435 3455195 := bstep (se 1 (by rfl) ⟨2591396, by rfl⟩ : syracuseStep 3455195 = 5182793) B5182793
theorem B2303463 : Blo 2303435 2303463 := bstep (se 1 (by rfl) ⟨1727597, by rfl⟩ : syracuseStep 2303463 = 3455195) B3455195
theorem B2591401 : Blo 2303435 2591401 := bbase (se 2 (by rfl) ⟨971775, by rfl⟩ : syracuseStep 2591401 = 1943551) (by norm_num)
theorem B3455201 : Blo 2303435 3455201 := bstep (se 2 (by rfl) ⟨1295700, by rfl⟩ : syracuseStep 3455201 = 2591401) B2591401
theorem B2303467 : Blo 2303435 2303467 := bstep (se 1 (by rfl) ⟨1727600, by rfl⟩ : syracuseStep 2303467 = 3455201) B3455201
theorem B3689717 : Blo 2303435 3689717 := bbase (se 5 (by rfl) ⟨172955, by rfl⟩ : syracuseStep 3689717 = 345911) (by norm_num)
theorem B9839245 : Blo 2303435 9839245 := bstep (se 3 (by rfl) ⟨1844858, by rfl⟩ : syracuseStep 9839245 = 3689717) B3689717
theorem B13118993 : Blo 2303435 13118993 := bstep (se 2 (by rfl) ⟨4919622, by rfl⟩ : syracuseStep 13118993 = 9839245) B9839245
theorem B8745995 : Blo 2303435 8745995 := bstep (se 1 (by rfl) ⟨6559496, by rfl⟩ : syracuseStep 8745995 = 13118993) B13118993
theorem B5830663 : Blo 2303435 5830663 := bstep (se 1 (by rfl) ⟨4372997, by rfl⟩ : syracuseStep 5830663 = 8745995) B8745995
theorem B7774217 : Blo 2303435 7774217 := bstep (se 2 (by rfl) ⟨2915331, by rfl⟩ : syracuseStep 7774217 = 5830663) B5830663
theorem B5182811 : Blo 2303435 5182811 := bstep (se 1 (by rfl) ⟨3887108, by rfl⟩ : syracuseStep 5182811 = 7774217) B7774217
theorem B3455207 : Blo 2303435 3455207 := bstep (se 1 (by rfl) ⟨2591405, by rfl⟩ : syracuseStep 3455207 = 5182811) B5182811
theorem B2303471 : Blo 2303435 2303471 := bstep (se 1 (by rfl) ⟨1727603, by rfl⟩ : syracuseStep 2303471 = 3455207) B3455207
theorem B3455213 : Blo 2303435 3455213 := bbase (se 3 (by rfl) ⟨647852, by rfl⟩ : syracuseStep 3455213 = 1295705) (by norm_num)
theorem B2303475 : Blo 2303435 2303475 := bstep (se 1 (by rfl) ⟨1727606, by rfl⟩ : syracuseStep 2303475 = 3455213) B3455213
theorem B5182829 : Blo 2303435 5182829 := bbase (se 3 (by rfl) ⟨971780, by rfl⟩ : syracuseStep 5182829 = 1943561) (by norm_num)
theorem B3455219 : Blo 2303435 3455219 := bstep (se 1 (by rfl) ⟨2591414, by rfl⟩ : syracuseStep 3455219 = 5182829) B5182829
theorem B2303479 : Blo 2303435 2303479 := bstep (se 1 (by rfl) ⟨1727609, by rfl⟩ : syracuseStep 2303479 = 3455219) B3455219
theorem B4373021 : Blo 2303435 4373021 := bbase (se 3 (by rfl) ⟨819941, by rfl⟩ : syracuseStep 4373021 = 1639883) (by norm_num)
theorem B2915347 : Blo 2303435 2915347 := bstep (se 1 (by rfl) ⟨2186510, by rfl⟩ : syracuseStep 2915347 = 4373021) B4373021
theorem B3887129 : Blo 2303435 3887129 := bstep (se 2 (by rfl) ⟨1457673, by rfl⟩ : syracuseStep 3887129 = 2915347) B2915347
theorem B2591419 : Blo 2303435 2591419 := bstep (se 1 (by rfl) ⟨1943564, by rfl⟩ : syracuseStep 2591419 = 3887129) B3887129
theorem B3455225 : Blo 2303435 3455225 := bstep (se 2 (by rfl) ⟨1295709, by rfl⟩ : syracuseStep 3455225 = 2591419) B2591419
theorem B2303483 : Blo 2303435 2303483 := bstep (se 1 (by rfl) ⟨1727612, by rfl⟩ : syracuseStep 2303483 = 3455225) B3455225
theorem B3502373 : Blo 2303435 3502373 := bbase (se 4 (by rfl) ⟨328347, by rfl⟩ : syracuseStep 3502373 = 656695) (by norm_num)
theorem B9339661 : Blo 2303435 9339661 := bstep (se 3 (by rfl) ⟨1751186, by rfl⟩ : syracuseStep 9339661 = 3502373) B3502373
theorem B12452881 : Blo 2303435 12452881 := bstep (se 2 (by rfl) ⟨4669830, by rfl⟩ : syracuseStep 12452881 = 9339661) B9339661
theorem B16603841 : Blo 2303435 16603841 := bstep (se 2 (by rfl) ⟨6226440, by rfl⟩ : syracuseStep 16603841 = 12452881) B12452881
theorem B11069227 : Blo 2303435 11069227 := bstep (se 1 (by rfl) ⟨8301920, by rfl⟩ : syracuseStep 11069227 = 16603841) B16603841
theorem B59035877 : Blo 2303435 59035877 := bstep (se 4 (by rfl) ⟨5534613, by rfl⟩ : syracuseStep 59035877 = 11069227) B11069227
theorem B39357251 : Blo 2303435 39357251 := bstep (se 1 (by rfl) ⟨29517938, by rfl⟩ : syracuseStep 39357251 = 59035877) B59035877
theorem B26238167 : Blo 2303435 26238167 := bstep (se 1 (by rfl) ⟨19678625, by rfl⟩ : syracuseStep 26238167 = 39357251) B39357251
theorem B17492111 : Blo 2303435 17492111 := bstep (se 1 (by rfl) ⟨13119083, by rfl⟩ : syracuseStep 17492111 = 26238167) B26238167
theorem B11661407 : Blo 2303435 11661407 := bstep (se 1 (by rfl) ⟨8746055, by rfl⟩ : syracuseStep 11661407 = 17492111) B17492111
theorem B7774271 : Blo 2303435 7774271 := bstep (se 1 (by rfl) ⟨5830703, by rfl⟩ : syracuseStep 7774271 = 11661407) B11661407
theorem B5182847 : Blo 2303435 5182847 := bstep (se 1 (by rfl) ⟨3887135, by rfl⟩ : syracuseStep 5182847 = 7774271) B7774271
theorem B3455231 : Blo 2303435 3455231 := bstep (se 1 (by rfl) ⟨2591423, by rfl⟩ : syracuseStep 3455231 = 5182847) B5182847
theorem B2303487 : Blo 2303435 2303487 := bstep (se 1 (by rfl) ⟨1727615, by rfl⟩ : syracuseStep 2303487 = 3455231) B3455231
theorem B3455237 : Blo 2303435 3455237 := bbase (se 4 (by rfl) ⟨323928, by rfl⟩ : syracuseStep 3455237 = 647857) (by norm_num)
theorem B2303491 : Blo 2303435 2303491 := bstep (se 1 (by rfl) ⟨1727618, by rfl⟩ : syracuseStep 2303491 = 3455237) B3455237
theorem B3887149 : Blo 2303435 3887149 := bbase (se 3 (by rfl) ⟨728840, by rfl⟩ : syracuseStep 3887149 = 1457681) (by norm_num)
theorem B5182865 : Blo 2303435 5182865 := bstep (se 2 (by rfl) ⟨1943574, by rfl⟩ : syracuseStep 5182865 = 3887149) B3887149
theorem B3455243 : Blo 2303435 3455243 := bstep (se 1 (by rfl) ⟨2591432, by rfl⟩ : syracuseStep 3455243 = 5182865) B5182865
theorem B2303495 : Blo 2303435 2303495 := bstep (se 1 (by rfl) ⟨1727621, by rfl⟩ : syracuseStep 2303495 = 3455243) B3455243
theorem B2591437 : Blo 2303435 2591437 := bbase (se 3 (by rfl) ⟨485894, by rfl⟩ : syracuseStep 2591437 = 971789) (by norm_num)
theorem B3455249 : Blo 2303435 3455249 := bstep (se 2 (by rfl) ⟨1295718, by rfl⟩ : syracuseStep 3455249 = 2591437) B2591437
theorem B2303499 : Blo 2303435 2303499 := bstep (se 1 (by rfl) ⟨1727624, by rfl⟩ : syracuseStep 2303499 = 3455249) B3455249
theorem B7774325 : Blo 2303435 7774325 := bbase (se 5 (by rfl) ⟨364421, by rfl⟩ : syracuseStep 7774325 = 728843) (by norm_num)
theorem B5182883 : Blo 2303435 5182883 := bstep (se 1 (by rfl) ⟨3887162, by rfl⟩ : syracuseStep 5182883 = 7774325) B7774325
theorem B3455255 : Blo 2303435 3455255 := bstep (se 1 (by rfl) ⟨2591441, by rfl⟩ : syracuseStep 3455255 = 5182883) B5182883
theorem B2303503 : Blo 2303435 2303503 := bstep (se 1 (by rfl) ⟨1727627, by rfl⟩ : syracuseStep 2303503 = 3455255) B3455255
theorem B3455261 : Blo 2303435 3455261 := bbase (se 3 (by rfl) ⟨647861, by rfl⟩ : syracuseStep 3455261 = 1295723) (by norm_num)
theorem B2303507 : Blo 2303435 2303507 := bstep (se 1 (by rfl) ⟨1727630, by rfl⟩ : syracuseStep 2303507 = 3455261) B3455261
theorem B5182901 : Blo 2303435 5182901 := bbase (se 5 (by rfl) ⟨242948, by rfl⟩ : syracuseStep 5182901 = 485897) (by norm_num)
theorem B3455267 : Blo 2303435 3455267 := bstep (se 1 (by rfl) ⟨2591450, by rfl⟩ : syracuseStep 3455267 = 5182901) B5182901
theorem B2303511 : Blo 2303435 2303511 := bstep (se 1 (by rfl) ⟨1727633, by rfl⟩ : syracuseStep 2303511 = 3455267) B3455267
theorem B4919717 : Blo 2303435 4919717 := bbase (se 4 (by rfl) ⟨461223, by rfl⟩ : syracuseStep 4919717 = 922447) (by norm_num)
theorem B13119245 : Blo 2303435 13119245 := bstep (se 3 (by rfl) ⟨2459858, by rfl⟩ : syracuseStep 13119245 = 4919717) B4919717
theorem B8746163 : Blo 2303435 8746163 := bstep (se 1 (by rfl) ⟨6559622, by rfl⟩ : syracuseStep 8746163 = 13119245) B13119245
theorem B5830775 : Blo 2303435 5830775 := bstep (se 1 (by rfl) ⟨4373081, by rfl⟩ : syracuseStep 5830775 = 8746163) B8746163
theorem B3887183 : Blo 2303435 3887183 := bstep (se 1 (by rfl) ⟨2915387, by rfl⟩ : syracuseStep 3887183 = 5830775) B5830775
theorem B2591455 : Blo 2303435 2591455 := bstep (se 1 (by rfl) ⟨1943591, by rfl⟩ : syracuseStep 2591455 = 3887183) B3887183
theorem B3455273 : Blo 2303435 3455273 := bstep (se 2 (by rfl) ⟨1295727, by rfl⟩ : syracuseStep 3455273 = 2591455) B2591455
theorem B2303515 : Blo 2303435 2303515 := bstep (se 1 (by rfl) ⟨1727636, by rfl⟩ : syracuseStep 2303515 = 3455273) B3455273
theorem B4919725 : Blo 2303435 4919725 := bbase (se 3 (by rfl) ⟨922448, by rfl⟩ : syracuseStep 4919725 = 1844897) (by norm_num)
theorem B6559633 : Blo 2303435 6559633 := bstep (se 2 (by rfl) ⟨2459862, by rfl⟩ : syracuseStep 6559633 = 4919725) B4919725
theorem B8746177 : Blo 2303435 8746177 := bstep (se 2 (by rfl) ⟨3279816, by rfl⟩ : syracuseStep 8746177 = 6559633) B6559633
theorem B11661569 : Blo 2303435 11661569 := bstep (se 2 (by rfl) ⟨4373088, by rfl⟩ : syracuseStep 11661569 = 8746177) B8746177
theorem B7774379 : Blo 2303435 7774379 := bstep (se 1 (by rfl) ⟨5830784, by rfl⟩ : syracuseStep 7774379 = 11661569) B11661569
theorem B5182919 : Blo 2303435 5182919 := bstep (se 1 (by rfl) ⟨3887189, by rfl⟩ : syracuseStep 5182919 = 7774379) B7774379
theorem B3455279 : Blo 2303435 3455279 := bstep (se 1 (by rfl) ⟨2591459, by rfl⟩ : syracuseStep 3455279 = 5182919) B5182919
theorem B2303519 : Blo 2303435 2303519 := bstep (se 1 (by rfl) ⟨1727639, by rfl⟩ : syracuseStep 2303519 = 3455279) B3455279
theorem B3455285 : Blo 2303435 3455285 := bbase (se 5 (by rfl) ⟨161966, by rfl⟩ : syracuseStep 3455285 = 323933) (by norm_num)
theorem B2303523 : Blo 2303435 2303523 := bstep (se 1 (by rfl) ⟨1727642, by rfl⟩ : syracuseStep 2303523 = 3455285) B3455285
theorem B5830805 : Blo 2303435 5830805 := bbase (se 6 (by rfl) ⟨136659, by rfl⟩ : syracuseStep 5830805 = 273319) (by norm_num)
theorem B3887203 : Blo 2303435 3887203 := bstep (se 1 (by rfl) ⟨2915402, by rfl⟩ : syracuseStep 3887203 = 5830805) B5830805
theorem B5182937 : Blo 2303435 5182937 := bstep (se 2 (by rfl) ⟨1943601, by rfl⟩ : syracuseStep 5182937 = 3887203) B3887203
theorem B3455291 : Blo 2303435 3455291 := bstep (se 1 (by rfl) ⟨2591468, by rfl⟩ : syracuseStep 3455291 = 5182937) B5182937
theorem B2303527 : Blo 2303435 2303527 := bstep (se 1 (by rfl) ⟨1727645, by rfl⟩ : syracuseStep 2303527 = 3455291) B3455291
theorem B2591473 : Blo 2303435 2591473 := bbase (se 2 (by rfl) ⟨971802, by rfl⟩ : syracuseStep 2591473 = 1943605) (by norm_num)
theorem B3455297 : Blo 2303435 3455297 := bstep (se 2 (by rfl) ⟨1295736, by rfl⟩ : syracuseStep 3455297 = 2591473) B2591473
theorem B2303531 : Blo 2303435 2303531 := bstep (se 1 (by rfl) ⟨1727648, by rfl⟩ : syracuseStep 2303531 = 3455297) B3455297
theorem B11820757 : Blo 2303435 11820757 := bbase (se 7 (by rfl) ⟨138524, by rfl⟩ : syracuseStep 11820757 = 277049) (by norm_num)
theorem B15761009 : Blo 2303435 15761009 := bstep (se 2 (by rfl) ⟨5910378, by rfl⟩ : syracuseStep 15761009 = 11820757) B11820757
theorem B10507339 : Blo 2303435 10507339 := bstep (se 1 (by rfl) ⟨7880504, by rfl⟩ : syracuseStep 10507339 = 15761009) B15761009
theorem B56039141 : Blo 2303435 56039141 := bstep (se 4 (by rfl) ⟨5253669, by rfl⟩ : syracuseStep 56039141 = 10507339) B10507339
theorem B37359427 : Blo 2303435 37359427 := bstep (se 1 (by rfl) ⟨28019570, by rfl⟩ : syracuseStep 37359427 = 56039141) B56039141
theorem B49812569 : Blo 2303435 49812569 := bstep (se 2 (by rfl) ⟨18679713, by rfl⟩ : syracuseStep 49812569 = 37359427) B37359427
theorem B33208379 : Blo 2303435 33208379 := bstep (se 1 (by rfl) ⟨24906284, by rfl⟩ : syracuseStep 33208379 = 49812569) B49812569
theorem B22138919 : Blo 2303435 22138919 := bstep (se 1 (by rfl) ⟨16604189, by rfl⟩ : syracuseStep 22138919 = 33208379) B33208379
theorem B14759279 : Blo 2303435 14759279 := bstep (se 1 (by rfl) ⟨11069459, by rfl⟩ : syracuseStep 14759279 = 22138919) B22138919
theorem B9839519 : Blo 2303435 9839519 := bstep (se 1 (by rfl) ⟨7379639, by rfl⟩ : syracuseStep 9839519 = 14759279) B14759279
theorem B6559679 : Blo 2303435 6559679 := bstep (se 1 (by rfl) ⟨4919759, by rfl⟩ : syracuseStep 6559679 = 9839519) B9839519
theorem B4373119 : Blo 2303435 4373119 := bstep (se 1 (by rfl) ⟨3279839, by rfl⟩ : syracuseStep 4373119 = 6559679) B6559679
theorem B5830825 : Blo 2303435 5830825 := bstep (se 2 (by rfl) ⟨2186559, by rfl⟩ : syracuseStep 5830825 = 4373119) B4373119
theorem B7774433 : Blo 2303435 7774433 := bstep (se 2 (by rfl) ⟨2915412, by rfl⟩ : syracuseStep 7774433 = 5830825) B5830825
theorem B5182955 : Blo 2303435 5182955 := bstep (se 1 (by rfl) ⟨3887216, by rfl⟩ : syracuseStep 5182955 = 7774433) B7774433
theorem B3455303 : Blo 2303435 3455303 := bstep (se 1 (by rfl) ⟨2591477, by rfl⟩ : syracuseStep 3455303 = 5182955) B5182955
theorem B2303535 : Blo 2303435 2303535 := bstep (se 1 (by rfl) ⟨1727651, by rfl⟩ : syracuseStep 2303535 = 3455303) B3455303
theorem B3455309 : Blo 2303435 3455309 := bbase (se 3 (by rfl) ⟨647870, by rfl⟩ : syracuseStep 3455309 = 1295741) (by norm_num)
theorem B2303539 : Blo 2303435 2303539 := bstep (se 1 (by rfl) ⟨1727654, by rfl⟩ : syracuseStep 2303539 = 3455309) B3455309
theorem B5182973 : Blo 2303435 5182973 := bbase (se 3 (by rfl) ⟨971807, by rfl⟩ : syracuseStep 5182973 = 1943615) (by norm_num)
theorem B3455315 : Blo 2303435 3455315 := bstep (se 1 (by rfl) ⟨2591486, by rfl⟩ : syracuseStep 3455315 = 5182973) B5182973
theorem B2303543 : Blo 2303435 2303543 := bstep (se 1 (by rfl) ⟨1727657, by rfl⟩ : syracuseStep 2303543 = 3455315) B3455315
theorem B3887237 : Blo 2303435 3887237 := bbase (se 4 (by rfl) ⟨364428, by rfl⟩ : syracuseStep 3887237 = 728857) (by norm_num)
theorem B2591491 : Blo 2303435 2591491 := bstep (se 1 (by rfl) ⟨1943618, by rfl⟩ : syracuseStep 2591491 = 3887237) B3887237
theorem B3455321 : Blo 2303435 3455321 := bstep (se 2 (by rfl) ⟨1295745, by rfl⟩ : syracuseStep 3455321 = 2591491) B2591491
theorem B2303547 : Blo 2303435 2303547 := bstep (se 1 (by rfl) ⟨1727660, by rfl⟩ : syracuseStep 2303547 = 3455321) B3455321
theorem B17492597 : Blo 2303435 17492597 := bbase (se 5 (by rfl) ⟨819965, by rfl⟩ : syracuseStep 17492597 = 1639931) (by norm_num)
theorem B11661731 : Blo 2303435 11661731 := bstep (se 1 (by rfl) ⟨8746298, by rfl⟩ : syracuseStep 11661731 = 17492597) B17492597
theorem B7774487 : Blo 2303435 7774487 := bstep (se 1 (by rfl) ⟨5830865, by rfl⟩ : syracuseStep 7774487 = 11661731) B11661731
theorem B5182991 : Blo 2303435 5182991 := bstep (se 1 (by rfl) ⟨3887243, by rfl⟩ : syracuseStep 5182991 = 7774487) B7774487
theorem B3455327 : Blo 2303435 3455327 := bstep (se 1 (by rfl) ⟨2591495, by rfl⟩ : syracuseStep 3455327 = 5182991) B5182991
theorem B2303551 : Blo 2303435 2303551 := bstep (se 1 (by rfl) ⟨1727663, by rfl⟩ : syracuseStep 2303551 = 3455327) B3455327
theorem B3455333 : Blo 2303435 3455333 := bbase (se 4 (by rfl) ⟨323937, by rfl⟩ : syracuseStep 3455333 = 647875) (by norm_num)
theorem B2303555 : Blo 2303435 2303555 := bstep (se 1 (by rfl) ⟨1727666, by rfl⟩ : syracuseStep 2303555 = 3455333) B3455333
theorem B4373165 : Blo 2303435 4373165 := bbase (se 3 (by rfl) ⟨819968, by rfl⟩ : syracuseStep 4373165 = 1639937) (by norm_num)
theorem B2915443 : Blo 2303435 2915443 := bstep (se 1 (by rfl) ⟨2186582, by rfl⟩ : syracuseStep 2915443 = 4373165) B4373165
theorem B3887257 : Blo 2303435 3887257 := bstep (se 2 (by rfl) ⟨1457721, by rfl⟩ : syracuseStep 3887257 = 2915443) B2915443
theorem B5183009 : Blo 2303435 5183009 := bstep (se 2 (by rfl) ⟨1943628, by rfl⟩ : syracuseStep 5183009 = 3887257) B3887257
theorem B3455339 : Blo 2303435 3455339 := bstep (se 1 (by rfl) ⟨2591504, by rfl⟩ : syracuseStep 3455339 = 5183009) B5183009
theorem B2303559 : Blo 2303435 2303559 := bstep (se 1 (by rfl) ⟨1727669, by rfl⟩ : syracuseStep 2303559 = 3455339) B3455339
theorem B2591509 : Blo 2303435 2591509 := bbase (se 6 (by rfl) ⟨60738, by rfl⟩ : syracuseStep 2591509 = 121477) (by norm_num)
theorem B3455345 : Blo 2303435 3455345 := bstep (se 2 (by rfl) ⟨1295754, by rfl⟩ : syracuseStep 3455345 = 2591509) B2591509
theorem B2303563 : Blo 2303435 2303563 := bstep (se 1 (by rfl) ⟨1727672, by rfl⟩ : syracuseStep 2303563 = 3455345) B3455345
theorem B2915453 : Blo 2303435 2915453 := bbase (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) (by norm_num)
theorem B7774541 : Blo 2303435 7774541 := bstep (se 3 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 7774541 = 2915453) B2915453
theorem B5183027 : Blo 2303435 5183027 := bstep (se 1 (by rfl) ⟨3887270, by rfl⟩ : syracuseStep 5183027 = 7774541) B7774541
theorem B3455351 : Blo 2303435 3455351 := bstep (se 1 (by rfl) ⟨2591513, by rfl⟩ : syracuseStep 3455351 = 5183027) B5183027
theorem B2303567 : Blo 2303435 2303567 := bstep (se 1 (by rfl) ⟨1727675, by rfl⟩ : syracuseStep 2303567 = 3455351) B3455351
theorem B3455357 : Blo 2303435 3455357 := bbase (se 3 (by rfl) ⟨647879, by rfl⟩ : syracuseStep 3455357 = 1295759) (by norm_num)
theorem B2303571 : Blo 2303435 2303571 := bstep (se 1 (by rfl) ⟨1727678, by rfl⟩ : syracuseStep 2303571 = 3455357) B3455357
theorem B5183045 : Blo 2303435 5183045 := bbase (se 4 (by rfl) ⟨485910, by rfl⟩ : syracuseStep 5183045 = 971821) (by norm_num)
theorem B3455363 : Blo 2303435 3455363 := bstep (se 1 (by rfl) ⟨2591522, by rfl⟩ : syracuseStep 3455363 = 5183045) B5183045
theorem B2303575 : Blo 2303435 2303575 := bstep (se 1 (by rfl) ⟨1727681, by rfl⟩ : syracuseStep 2303575 = 3455363) B3455363
theorem B5534837 : Blo 2303435 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B3689891 : Blo 2303435 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B2459927 : Blo 2303435 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B6559805 : Blo 2303435 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B4373203 : Blo 2303435 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B5830937 : Blo 2303435 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B3887291 : Blo 2303435 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B2591527 : Blo 2303435 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B3455369 : Blo 2303435 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B2303579 : Blo 2303435 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B11661893 : Blo 2303435 11661893 := bbase (se 4 (by rfl) ⟨1093302, by rfl⟩ : syracuseStep 11661893 = 2186605) (by norm_num)
theorem B7774595 : Blo 2303435 7774595 := bstep (se 1 (by rfl) ⟨5830946, by rfl⟩ : syracuseStep 7774595 = 11661893) B11661893
theorem B5183063 : Blo 2303435 5183063 := bstep (se 1 (by rfl) ⟨3887297, by rfl⟩ : syracuseStep 5183063 = 7774595) B7774595
theorem B3455375 : Blo 2303435 3455375 := bstep (se 1 (by rfl) ⟨2591531, by rfl⟩ : syracuseStep 3455375 = 5183063) B5183063
theorem B2303583 : Blo 2303435 2303583 := bstep (se 1 (by rfl) ⟨1727687, by rfl⟩ : syracuseStep 2303583 = 3455375) B3455375
theorem B3455381 : Blo 2303435 3455381 := bbase (se 6 (by rfl) ⟨80985, by rfl⟩ : syracuseStep 3455381 = 161971) (by norm_num)
theorem B2303587 : Blo 2303435 2303587 := bstep (se 1 (by rfl) ⟨1727690, by rfl⟩ : syracuseStep 2303587 = 3455381) B3455381
theorem B9340085 : Blo 2303435 9340085 := bbase (se 5 (by rfl) ⟨437816, by rfl⟩ : syracuseStep 9340085 = 875633) (by norm_num)
theorem B6226723 : Blo 2303435 6226723 := bstep (se 1 (by rfl) ⟨4670042, by rfl⟩ : syracuseStep 6226723 = 9340085) B9340085
theorem B8302297 : Blo 2303435 8302297 := bstep (se 2 (by rfl) ⟨3113361, by rfl⟩ : syracuseStep 8302297 = 6226723) B6226723
theorem B11069729 : Blo 2303435 11069729 := bstep (se 2 (by rfl) ⟨4151148, by rfl⟩ : syracuseStep 11069729 = 8302297) B8302297
theorem B7379819 : Blo 2303435 7379819 := bstep (se 1 (by rfl) ⟨5534864, by rfl⟩ : syracuseStep 7379819 = 11069729) B11069729
theorem B4919879 : Blo 2303435 4919879 := bstep (se 1 (by rfl) ⟨3689909, by rfl⟩ : syracuseStep 4919879 = 7379819) B7379819
theorem B13119677 : Blo 2303435 13119677 := bstep (se 3 (by rfl) ⟨2459939, by rfl⟩ : syracuseStep 13119677 = 4919879) B4919879
theorem B8746451 : Blo 2303435 8746451 := bstep (se 1 (by rfl) ⟨6559838, by rfl⟩ : syracuseStep 8746451 = 13119677) B13119677
theorem B5830967 : Blo 2303435 5830967 := bstep (se 1 (by rfl) ⟨4373225, by rfl⟩ : syracuseStep 5830967 = 8746451) B8746451
theorem B3887311 : Blo 2303435 3887311 := bstep (se 1 (by rfl) ⟨2915483, by rfl⟩ : syracuseStep 3887311 = 5830967) B5830967
theorem B5183081 : Blo 2303435 5183081 := bstep (se 2 (by rfl) ⟨1943655, by rfl⟩ : syracuseStep 5183081 = 3887311) B3887311
theorem B3455387 : Blo 2303435 3455387 := bstep (se 1 (by rfl) ⟨2591540, by rfl⟩ : syracuseStep 3455387 = 5183081) B5183081
theorem B2303591 : Blo 2303435 2303591 := bstep (se 1 (by rfl) ⟨1727693, by rfl⟩ : syracuseStep 2303591 = 3455387) B3455387
theorem B2591545 : Blo 2303435 2591545 := bbase (se 2 (by rfl) ⟨971829, by rfl⟩ : syracuseStep 2591545 = 1943659) (by norm_num)
theorem B3455393 : Blo 2303435 3455393 := bstep (se 2 (by rfl) ⟨1295772, by rfl⟩ : syracuseStep 3455393 = 2591545) B2591545
theorem B2303595 : Blo 2303435 2303595 := bstep (se 1 (by rfl) ⟨1727696, by rfl⟩ : syracuseStep 2303595 = 3455393) B3455393
theorem B6559861 : Blo 2303435 6559861 := bbase (se 5 (by rfl) ⟨307493, by rfl⟩ : syracuseStep 6559861 = 614987) (by norm_num)
theorem B8746481 : Blo 2303435 8746481 := bstep (se 2 (by rfl) ⟨3279930, by rfl⟩ : syracuseStep 8746481 = 6559861) B6559861
theorem B5830987 : Blo 2303435 5830987 := bstep (se 1 (by rfl) ⟨4373240, by rfl⟩ : syracuseStep 5830987 = 8746481) B8746481
theorem B7774649 : Blo 2303435 7774649 := bstep (se 2 (by rfl) ⟨2915493, by rfl⟩ : syracuseStep 7774649 = 5830987) B5830987
theorem B5183099 : Blo 2303435 5183099 := bstep (se 1 (by rfl) ⟨3887324, by rfl⟩ : syracuseStep 5183099 = 7774649) B7774649
theorem B3455399 : Blo 2303435 3455399 := bstep (se 1 (by rfl) ⟨2591549, by rfl⟩ : syracuseStep 3455399 = 5183099) B5183099
theorem B2303599 : Blo 2303435 2303599 := bstep (se 1 (by rfl) ⟨1727699, by rfl⟩ : syracuseStep 2303599 = 3455399) B3455399
theorem B3455405 : Blo 2303435 3455405 := bbase (se 3 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 3455405 = 1295777) (by norm_num)
theorem B2303603 : Blo 2303435 2303603 := bstep (se 1 (by rfl) ⟨1727702, by rfl⟩ : syracuseStep 2303603 = 3455405) B3455405
theorem B5183117 : Blo 2303435 5183117 := bbase (se 3 (by rfl) ⟨971834, by rfl⟩ : syracuseStep 5183117 = 1943669) (by norm_num)
theorem B3455411 : Blo 2303435 3455411 := bstep (se 1 (by rfl) ⟨2591558, by rfl⟩ : syracuseStep 3455411 = 5183117) B5183117
theorem B2303607 : Blo 2303435 2303607 := bstep (se 1 (by rfl) ⟨1727705, by rfl⟩ : syracuseStep 2303607 = 3455411) B3455411
theorem B2915509 : Blo 2303435 2915509 := bbase (se 5 (by rfl) ⟨136664, by rfl⟩ : syracuseStep 2915509 = 273329) (by norm_num)
theorem B3887345 : Blo 2303435 3887345 := bstep (se 2 (by rfl) ⟨1457754, by rfl⟩ : syracuseStep 3887345 = 2915509) B2915509
theorem B2591563 : Blo 2303435 2591563 := bstep (se 1 (by rfl) ⟨1943672, by rfl⟩ : syracuseStep 2591563 = 3887345) B3887345
theorem B3455417 : Blo 2303435 3455417 := bstep (se 2 (by rfl) ⟨1295781, by rfl⟩ : syracuseStep 3455417 = 2591563) B2591563
theorem B2303611 : Blo 2303435 2303611 := bstep (se 1 (by rfl) ⟨1727708, by rfl⟩ : syracuseStep 2303611 = 3455417) B3455417
theorem B9596789 : Blo 2303435 9596789 := bbase (se 5 (by rfl) ⟨449849, by rfl⟩ : syracuseStep 9596789 = 899699) (by norm_num)
theorem B6397859 : Blo 2303435 6397859 := bstep (se 1 (by rfl) ⟨4798394, by rfl⟩ : syracuseStep 6397859 = 9596789) B9596789
theorem B4265239 : Blo 2303435 4265239 := bstep (se 1 (by rfl) ⟨3198929, by rfl⟩ : syracuseStep 4265239 = 6397859) B6397859
theorem B5686985 : Blo 2303435 5686985 := bstep (se 2 (by rfl) ⟨2132619, by rfl⟩ : syracuseStep 5686985 = 4265239) B4265239
theorem B3791323 : Blo 2303435 3791323 := bstep (se 1 (by rfl) ⟨2843492, by rfl⟩ : syracuseStep 3791323 = 5686985) B5686985
theorem B5055097 : Blo 2303435 5055097 := bstep (se 2 (by rfl) ⟨1895661, by rfl⟩ : syracuseStep 5055097 = 3791323) B3791323
theorem B6740129 : Blo 2303435 6740129 := bstep (se 2 (by rfl) ⟨2527548, by rfl⟩ : syracuseStep 6740129 = 5055097) B5055097
theorem B17973677 : Blo 2303435 17973677 := bstep (se 3 (by rfl) ⟨3370064, by rfl⟩ : syracuseStep 17973677 = 6740129) B6740129
theorem B11982451 : Blo 2303435 11982451 := bstep (se 1 (by rfl) ⟨8986838, by rfl⟩ : syracuseStep 11982451 = 17973677) B17973677
theorem B15976601 : Blo 2303435 15976601 := bstep (se 2 (by rfl) ⟨5991225, by rfl⟩ : syracuseStep 15976601 = 11982451) B11982451
theorem B10651067 : Blo 2303435 10651067 := bstep (se 1 (by rfl) ⟨7988300, by rfl⟩ : syracuseStep 10651067 = 15976601) B15976601
theorem B7100711 : Blo 2303435 7100711 := bstep (se 1 (by rfl) ⟨5325533, by rfl⟩ : syracuseStep 7100711 = 10651067) B10651067
theorem B4733807 : Blo 2303435 4733807 := bstep (se 1 (by rfl) ⟨3550355, by rfl⟩ : syracuseStep 4733807 = 7100711) B7100711
theorem B12623485 : Blo 2303435 12623485 := bstep (se 3 (by rfl) ⟨2366903, by rfl⟩ : syracuseStep 12623485 = 4733807) B4733807
theorem B16831313 : Blo 2303435 16831313 := bstep (se 2 (by rfl) ⟨6311742, by rfl⟩ : syracuseStep 16831313 = 12623485) B12623485
theorem B11220875 : Blo 2303435 11220875 := bstep (se 1 (by rfl) ⟨8415656, by rfl⟩ : syracuseStep 11220875 = 16831313) B16831313
theorem B7480583 : Blo 2303435 7480583 := bstep (se 1 (by rfl) ⟨5610437, by rfl⟩ : syracuseStep 7480583 = 11220875) B11220875
theorem B4987055 : Blo 2303435 4987055 := bstep (se 1 (by rfl) ⟨3740291, by rfl⟩ : syracuseStep 4987055 = 7480583) B7480583
theorem B3324703 : Blo 2303435 3324703 := bstep (se 1 (by rfl) ⟨2493527, by rfl⟩ : syracuseStep 3324703 = 4987055) B4987055
theorem B4432937 : Blo 2303435 4432937 := bstep (se 2 (by rfl) ⟨1662351, by rfl⟩ : syracuseStep 4432937 = 3324703) B3324703
theorem B47284661 : Blo 2303435 47284661 := bstep (se 5 (by rfl) ⟨2216468, by rfl⟩ : syracuseStep 47284661 = 4432937) B4432937
theorem B31523107 : Blo 2303435 31523107 := bstep (se 1 (by rfl) ⟨23642330, by rfl⟩ : syracuseStep 31523107 = 47284661) B47284661
theorem B42030809 : Blo 2303435 42030809 := bstep (se 2 (by rfl) ⟨15761553, by rfl⟩ : syracuseStep 42030809 = 31523107) B31523107
theorem B28020539 : Blo 2303435 28020539 := bstep (se 1 (by rfl) ⟨21015404, by rfl⟩ : syracuseStep 28020539 = 42030809) B42030809
theorem B74721437 : Blo 2303435 74721437 := bstep (se 3 (by rfl) ⟨14010269, by rfl⟩ : syracuseStep 74721437 = 28020539) B28020539
theorem B49814291 : Blo 2303435 49814291 := bstep (se 1 (by rfl) ⟨37360718, by rfl⟩ : syracuseStep 49814291 = 74721437) B74721437
theorem B33209527 : Blo 2303435 33209527 := bstep (se 1 (by rfl) ⟨24907145, by rfl⟩ : syracuseStep 33209527 = 49814291) B49814291
theorem B44279369 : Blo 2303435 44279369 := bstep (se 2 (by rfl) ⟨16604763, by rfl⟩ : syracuseStep 44279369 = 33209527) B33209527
theorem B29519579 : Blo 2303435 29519579 := bstep (se 1 (by rfl) ⟨22139684, by rfl⟩ : syracuseStep 29519579 = 44279369) B44279369
theorem B19679719 : Blo 2303435 19679719 := bstep (se 1 (by rfl) ⟨14759789, by rfl⟩ : syracuseStep 19679719 = 29519579) B29519579
theorem B26239625 : Blo 2303435 26239625 := bstep (se 2 (by rfl) ⟨9839859, by rfl⟩ : syracuseStep 26239625 = 19679719) B19679719
theorem B17493083 : Blo 2303435 17493083 := bstep (se 1 (by rfl) ⟨13119812, by rfl⟩ : syracuseStep 17493083 = 26239625) B26239625
theorem B11662055 : Blo 2303435 11662055 := bstep (se 1 (by rfl) ⟨8746541, by rfl⟩ : syracuseStep 11662055 = 17493083) B17493083
theorem B7774703 : Blo 2303435 7774703 := bstep (se 1 (by rfl) ⟨5831027, by rfl⟩ : syracuseStep 7774703 = 11662055) B11662055
theorem B5183135 : Blo 2303435 5183135 := bstep (se 1 (by rfl) ⟨3887351, by rfl⟩ : syracuseStep 5183135 = 7774703) B7774703
theorem B3455423 : Blo 2303435 3455423 := bstep (se 1 (by rfl) ⟨2591567, by rfl⟩ : syracuseStep 3455423 = 5183135) B5183135
theorem B2303615 : Blo 2303435 2303615 := bstep (se 1 (by rfl) ⟨1727711, by rfl⟩ : syracuseStep 2303615 = 3455423) B3455423
theorem B3455429 : Blo 2303435 3455429 := bbase (se 4 (by rfl) ⟨323946, by rfl⟩ : syracuseStep 3455429 = 647893) (by norm_num)
theorem B2303619 : Blo 2303435 2303619 := bstep (se 1 (by rfl) ⟨1727714, by rfl⟩ : syracuseStep 2303619 = 3455429) B3455429
theorem B3887365 : Blo 2303435 3887365 := bbase (se 4 (by rfl) ⟨364440, by rfl⟩ : syracuseStep 3887365 = 728881) (by norm_num)
theorem B5183153 : Blo 2303435 5183153 := bstep (se 2 (by rfl) ⟨1943682, by rfl⟩ : syracuseStep 5183153 = 3887365) B3887365
theorem B3455435 : Blo 2303435 3455435 := bstep (se 1 (by rfl) ⟨2591576, by rfl⟩ : syracuseStep 3455435 = 5183153) B5183153
theorem B2303623 : Blo 2303435 2303623 := bstep (se 1 (by rfl) ⟨1727717, by rfl⟩ : syracuseStep 2303623 = 3455435) B3455435
theorem B2591581 : Blo 2303435 2591581 := bbase (se 3 (by rfl) ⟨485921, by rfl⟩ : syracuseStep 2591581 = 971843) (by norm_num)
theorem B3455441 : Blo 2303435 3455441 := bstep (se 2 (by rfl) ⟨1295790, by rfl⟩ : syracuseStep 3455441 = 2591581) B2591581
theorem B2303627 : Blo 2303435 2303627 := bstep (se 1 (by rfl) ⟨1727720, by rfl⟩ : syracuseStep 2303627 = 3455441) B3455441
theorem B7774757 : Blo 2303435 7774757 := bbase (se 4 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 7774757 = 1457767) (by norm_num)
theorem B5183171 : Blo 2303435 5183171 := bstep (se 1 (by rfl) ⟨3887378, by rfl⟩ : syracuseStep 5183171 = 7774757) B7774757
theorem B3455447 : Blo 2303435 3455447 := bstep (se 1 (by rfl) ⟨2591585, by rfl⟩ : syracuseStep 3455447 = 5183171) B5183171
theorem B2303631 : Blo 2303435 2303631 := bstep (se 1 (by rfl) ⟨1727723, by rfl⟩ : syracuseStep 2303631 = 3455447) B3455447
theorem B3455453 : Blo 2303435 3455453 := bbase (se 3 (by rfl) ⟨647897, by rfl⟩ : syracuseStep 3455453 = 1295795) (by norm_num)
theorem B2303635 : Blo 2303435 2303635 := bstep (se 1 (by rfl) ⟨1727726, by rfl⟩ : syracuseStep 2303635 = 3455453) B3455453
theorem B5183189 : Blo 2303435 5183189 := bbase (se 7 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 5183189 = 121481) (by norm_num)
theorem B3455459 : Blo 2303435 3455459 := bstep (se 1 (by rfl) ⟨2591594, by rfl⟩ : syracuseStep 3455459 = 5183189) B5183189
theorem B2303639 : Blo 2303435 2303639 := bstep (se 1 (by rfl) ⟨1727729, by rfl⟩ : syracuseStep 2303639 = 3455459) B3455459
theorem B4670149 : Blo 2303435 4670149 := bbase (se 4 (by rfl) ⟨437826, by rfl⟩ : syracuseStep 4670149 = 875653) (by norm_num)
theorem B6226865 : Blo 2303435 6226865 := bstep (se 2 (by rfl) ⟨2335074, by rfl⟩ : syracuseStep 6226865 = 4670149) B4670149
theorem B4151243 : Blo 2303435 4151243 := bstep (se 1 (by rfl) ⟨3113432, by rfl⟩ : syracuseStep 4151243 = 6226865) B6226865
theorem B2767495 : Blo 2303435 2767495 := bstep (se 1 (by rfl) ⟨2075621, by rfl⟩ : syracuseStep 2767495 = 4151243) B4151243
theorem B3689993 : Blo 2303435 3689993 := bstep (se 2 (by rfl) ⟨1383747, by rfl⟩ : syracuseStep 3689993 = 2767495) B2767495
theorem B9839981 : Blo 2303435 9839981 := bstep (se 3 (by rfl) ⟨1844996, by rfl⟩ : syracuseStep 9839981 = 3689993) B3689993
theorem B6559987 : Blo 2303435 6559987 := bstep (se 1 (by rfl) ⟨4919990, by rfl⟩ : syracuseStep 6559987 = 9839981) B9839981
theorem B8746649 : Blo 2303435 8746649 := bstep (se 2 (by rfl) ⟨3279993, by rfl⟩ : syracuseStep 8746649 = 6559987) B6559987
theorem B5831099 : Blo 2303435 5831099 := bstep (se 1 (by rfl) ⟨4373324, by rfl⟩ : syracuseStep 5831099 = 8746649) B8746649
theorem B3887399 : Blo 2303435 3887399 := bstep (se 1 (by rfl) ⟨2915549, by rfl⟩ : syracuseStep 3887399 = 5831099) B5831099
theorem B2591599 : Blo 2303435 2591599 := bstep (se 1 (by rfl) ⟨1943699, by rfl⟩ : syracuseStep 2591599 = 3887399) B3887399
theorem B3455465 : Blo 2303435 3455465 := bstep (se 2 (by rfl) ⟨1295799, by rfl⟩ : syracuseStep 3455465 = 2591599) B2591599
theorem B2303643 : Blo 2303435 2303643 := bstep (se 1 (by rfl) ⟨1727732, by rfl⟩ : syracuseStep 2303643 = 3455465) B3455465
theorem B5253925 : Blo 2303435 5253925 := bbase (se 4 (by rfl) ⟨492555, by rfl⟩ : syracuseStep 5253925 = 985111) (by norm_num)
theorem B7005233 : Blo 2303435 7005233 := bstep (se 2 (by rfl) ⟨2626962, by rfl⟩ : syracuseStep 7005233 = 5253925) B5253925
theorem B4670155 : Blo 2303435 4670155 := bstep (se 1 (by rfl) ⟨3502616, by rfl⟩ : syracuseStep 4670155 = 7005233) B7005233
theorem B24907493 : Blo 2303435 24907493 := bstep (se 4 (by rfl) ⟨2335077, by rfl⟩ : syracuseStep 24907493 = 4670155) B4670155
theorem B16604995 : Blo 2303435 16604995 := bstep (se 1 (by rfl) ⟨12453746, by rfl⟩ : syracuseStep 16604995 = 24907493) B24907493
theorem B22139993 : Blo 2303435 22139993 := bstep (se 2 (by rfl) ⟨8302497, by rfl⟩ : syracuseStep 22139993 = 16604995) B16604995
theorem B14759995 : Blo 2303435 14759995 := bstep (se 1 (by rfl) ⟨11069996, by rfl⟩ : syracuseStep 14759995 = 22139993) B22139993
theorem B19679993 : Blo 2303435 19679993 := bstep (se 2 (by rfl) ⟨7379997, by rfl⟩ : syracuseStep 19679993 = 14759995) B14759995
theorem B13119995 : Blo 2303435 13119995 := bstep (se 1 (by rfl) ⟨9839996, by rfl⟩ : syracuseStep 13119995 = 19679993) B19679993
theorem B8746663 : Blo 2303435 8746663 := bstep (se 1 (by rfl) ⟨6559997, by rfl⟩ : syracuseStep 8746663 = 13119995) B13119995
theorem B11662217 : Blo 2303435 11662217 := bstep (se 2 (by rfl) ⟨4373331, by rfl⟩ : syracuseStep 11662217 = 8746663) B8746663
theorem B7774811 : Blo 2303435 7774811 := bstep (se 1 (by rfl) ⟨5831108, by rfl⟩ : syracuseStep 7774811 = 11662217) B11662217
theorem B5183207 : Blo 2303435 5183207 := bstep (se 1 (by rfl) ⟨3887405, by rfl⟩ : syracuseStep 5183207 = 7774811) B7774811
theorem B3455471 : Blo 2303435 3455471 := bstep (se 1 (by rfl) ⟨2591603, by rfl⟩ : syracuseStep 3455471 = 5183207) B5183207
theorem B2303647 : Blo 2303435 2303647 := bstep (se 1 (by rfl) ⟨1727735, by rfl⟩ : syracuseStep 2303647 = 3455471) B3455471
theorem B3455477 : Blo 2303435 3455477 := bbase (se 5 (by rfl) ⟨161975, by rfl⟩ : syracuseStep 3455477 = 323951) (by norm_num)
theorem B2303651 : Blo 2303435 2303651 := bstep (se 1 (by rfl) ⟨1727738, by rfl⟩ : syracuseStep 2303651 = 3455477) B3455477
theorem B6560021 : Blo 2303435 6560021 := bbase (se 6 (by rfl) ⟨153750, by rfl⟩ : syracuseStep 6560021 = 307501) (by norm_num)
theorem B4373347 : Blo 2303435 4373347 := bstep (se 1 (by rfl) ⟨3280010, by rfl⟩ : syracuseStep 4373347 = 6560021) B6560021
theorem B5831129 : Blo 2303435 5831129 := bstep (se 2 (by rfl) ⟨2186673, by rfl⟩ : syracuseStep 5831129 = 4373347) B4373347
theorem B3887419 : Blo 2303435 3887419 := bstep (se 1 (by rfl) ⟨2915564, by rfl⟩ : syracuseStep 3887419 = 5831129) B5831129
theorem B5183225 : Blo 2303435 5183225 := bstep (se 2 (by rfl) ⟨1943709, by rfl⟩ : syracuseStep 5183225 = 3887419) B3887419
theorem B3455483 : Blo 2303435 3455483 := bstep (se 1 (by rfl) ⟨2591612, by rfl⟩ : syracuseStep 3455483 = 5183225) B5183225
theorem B2303655 : Blo 2303435 2303655 := bstep (se 1 (by rfl) ⟨1727741, by rfl⟩ : syracuseStep 2303655 = 3455483) B3455483
theorem B2591617 : Blo 2303435 2591617 := bbase (se 2 (by rfl) ⟨971856, by rfl⟩ : syracuseStep 2591617 = 1943713) (by norm_num)
theorem B3455489 : Blo 2303435 3455489 := bstep (se 2 (by rfl) ⟨1295808, by rfl⟩ : syracuseStep 3455489 = 2591617) B2591617
theorem B2303659 : Blo 2303435 2303659 := bstep (se 1 (by rfl) ⟨1727744, by rfl⟩ : syracuseStep 2303659 = 3455489) B3455489
theorem B5831149 : Blo 2303435 5831149 := bbase (se 3 (by rfl) ⟨1093340, by rfl⟩ : syracuseStep 5831149 = 2186681) (by norm_num)
theorem B7774865 : Blo 2303435 7774865 := bstep (se 2 (by rfl) ⟨2915574, by rfl⟩ : syracuseStep 7774865 = 5831149) B5831149
theorem B5183243 : Blo 2303435 5183243 := bstep (se 1 (by rfl) ⟨3887432, by rfl⟩ : syracuseStep 5183243 = 7774865) B7774865
theorem B3455495 : Blo 2303435 3455495 := bstep (se 1 (by rfl) ⟨2591621, by rfl⟩ : syracuseStep 3455495 = 5183243) B5183243
theorem B2303663 : Blo 2303435 2303663 := bstep (se 1 (by rfl) ⟨1727747, by rfl⟩ : syracuseStep 2303663 = 3455495) B3455495
theorem B3455501 : Blo 2303435 3455501 := bbase (se 3 (by rfl) ⟨647906, by rfl⟩ : syracuseStep 3455501 = 1295813) (by norm_num)
theorem B2303667 : Blo 2303435 2303667 := bstep (se 1 (by rfl) ⟨1727750, by rfl⟩ : syracuseStep 2303667 = 3455501) B3455501
theorem B5183261 : Blo 2303435 5183261 := bbase (se 3 (by rfl) ⟨971861, by rfl⟩ : syracuseStep 5183261 = 1943723) (by norm_num)
theorem B3455507 : Blo 2303435 3455507 := bstep (se 1 (by rfl) ⟨2591630, by rfl⟩ : syracuseStep 3455507 = 5183261) B5183261
theorem B2303671 : Blo 2303435 2303671 := bstep (se 1 (by rfl) ⟨1727753, by rfl⟩ : syracuseStep 2303671 = 3455507) B3455507
theorem B3887453 : Blo 2303435 3887453 := bbase (se 3 (by rfl) ⟨728897, by rfl⟩ : syracuseStep 3887453 = 1457795) (by norm_num)
theorem B2591635 : Blo 2303435 2591635 := bstep (se 1 (by rfl) ⟨1943726, by rfl⟩ : syracuseStep 2591635 = 3887453) B3887453
theorem B3455513 : Blo 2303435 3455513 := bstep (se 2 (by rfl) ⟨1295817, by rfl⟩ : syracuseStep 3455513 = 2591635) B2591635
theorem B2303675 : Blo 2303435 2303675 := bstep (se 1 (by rfl) ⟨1727756, by rfl⟩ : syracuseStep 2303675 = 3455513) B3455513
theorem B9840133 : Blo 2303435 9840133 := bbase (se 4 (by rfl) ⟨922512, by rfl⟩ : syracuseStep 9840133 = 1845025) (by norm_num)
theorem B13120177 : Blo 2303435 13120177 := bstep (se 2 (by rfl) ⟨4920066, by rfl⟩ : syracuseStep 13120177 = 9840133) B9840133
theorem B17493569 : Blo 2303435 17493569 := bstep (se 2 (by rfl) ⟨6560088, by rfl⟩ : syracuseStep 17493569 = 13120177) B13120177
theorem B11662379 : Blo 2303435 11662379 := bstep (se 1 (by rfl) ⟨8746784, by rfl⟩ : syracuseStep 11662379 = 17493569) B17493569
theorem B7774919 : Blo 2303435 7774919 := bstep (se 1 (by rfl) ⟨5831189, by rfl⟩ : syracuseStep 7774919 = 11662379) B11662379
theorem B5183279 : Blo 2303435 5183279 := bstep (se 1 (by rfl) ⟨3887459, by rfl⟩ : syracuseStep 5183279 = 7774919) B7774919
theorem B3455519 : Blo 2303435 3455519 := bstep (se 1 (by rfl) ⟨2591639, by rfl⟩ : syracuseStep 3455519 = 5183279) B5183279
theorem B2303679 : Blo 2303435 2303679 := bstep (se 1 (by rfl) ⟨1727759, by rfl⟩ : syracuseStep 2303679 = 3455519) B3455519
theorem B3455525 : Blo 2303435 3455525 := bbase (se 4 (by rfl) ⟨323955, by rfl⟩ : syracuseStep 3455525 = 647911) (by norm_num)
theorem B2303683 : Blo 2303435 2303683 := bstep (se 1 (by rfl) ⟨1727762, by rfl⟩ : syracuseStep 2303683 = 3455525) B3455525
theorem B2915605 : Blo 2303435 2915605 := bbase (se 6 (by rfl) ⟨68334, by rfl⟩ : syracuseStep 2915605 = 136669) (by norm_num)
theorem B3887473 : Blo 2303435 3887473 := bstep (se 2 (by rfl) ⟨1457802, by rfl⟩ : syracuseStep 3887473 = 2915605) B2915605
theorem B5183297 : Blo 2303435 5183297 := bstep (se 2 (by rfl) ⟨1943736, by rfl⟩ : syracuseStep 5183297 = 3887473) B3887473
theorem B3455531 : Blo 2303435 3455531 := bstep (se 1 (by rfl) ⟨2591648, by rfl⟩ : syracuseStep 3455531 = 5183297) B5183297
theorem B2303687 : Blo 2303435 2303687 := bstep (se 1 (by rfl) ⟨1727765, by rfl⟩ : syracuseStep 2303687 = 3455531) B3455531
theorem B2591653 : Blo 2303435 2591653 := bbase (se 4 (by rfl) ⟨242967, by rfl⟩ : syracuseStep 2591653 = 485935) (by norm_num)
theorem B3455537 : Blo 2303435 3455537 := bstep (se 2 (by rfl) ⟨1295826, by rfl⟩ : syracuseStep 3455537 = 2591653) B2591653
theorem B2303691 : Blo 2303435 2303691 := bstep (se 1 (by rfl) ⟨1727768, by rfl⟩ : syracuseStep 2303691 = 3455537) B3455537
theorem B11070229 : Blo 2303435 11070229 := bbase (se 6 (by rfl) ⟨259458, by rfl⟩ : syracuseStep 11070229 = 518917) (by norm_num)
theorem B14760305 : Blo 2303435 14760305 := bstep (se 2 (by rfl) ⟨5535114, by rfl⟩ : syracuseStep 14760305 = 11070229) B11070229
theorem B9840203 : Blo 2303435 9840203 := bstep (se 1 (by rfl) ⟨7380152, by rfl⟩ : syracuseStep 9840203 = 14760305) B14760305
theorem B6560135 : Blo 2303435 6560135 := bstep (se 1 (by rfl) ⟨4920101, by rfl⟩ : syracuseStep 6560135 = 9840203) B9840203
theorem B4373423 : Blo 2303435 4373423 := bstep (se 1 (by rfl) ⟨3280067, by rfl⟩ : syracuseStep 4373423 = 6560135) B6560135
theorem B2915615 : Blo 2303435 2915615 := bstep (se 1 (by rfl) ⟨2186711, by rfl⟩ : syracuseStep 2915615 = 4373423) B4373423
theorem B7774973 : Blo 2303435 7774973 := bstep (se 3 (by rfl) ⟨1457807, by rfl⟩ : syracuseStep 7774973 = 2915615) B2915615
theorem B5183315 : Blo 2303435 5183315 := bstep (se 1 (by rfl) ⟨3887486, by rfl⟩ : syracuseStep 5183315 = 7774973) B7774973
theorem B3455543 : Blo 2303435 3455543 := bstep (se 1 (by rfl) ⟨2591657, by rfl⟩ : syracuseStep 3455543 = 5183315) B5183315
theorem B2303695 : Blo 2303435 2303695 := bstep (se 1 (by rfl) ⟨1727771, by rfl⟩ : syracuseStep 2303695 = 3455543) B3455543
theorem B3455549 : Blo 2303435 3455549 := bbase (se 3 (by rfl) ⟨647915, by rfl⟩ : syracuseStep 3455549 = 1295831) (by norm_num)
theorem B2303699 : Blo 2303435 2303699 := bstep (se 1 (by rfl) ⟨1727774, by rfl⟩ : syracuseStep 2303699 = 3455549) B3455549
theorem B5183333 : Blo 2303435 5183333 := bbase (se 4 (by rfl) ⟨485937, by rfl⟩ : syracuseStep 5183333 = 971875) (by norm_num)
theorem B3455555 : Blo 2303435 3455555 := bstep (se 1 (by rfl) ⟨2591666, by rfl⟩ : syracuseStep 3455555 = 5183333) B5183333
theorem B2303703 : Blo 2303435 2303703 := bstep (se 1 (by rfl) ⟨1727777, by rfl⟩ : syracuseStep 2303703 = 3455555) B3455555
theorem B5831261 : Blo 2303435 5831261 := bbase (se 3 (by rfl) ⟨1093361, by rfl⟩ : syracuseStep 5831261 = 2186723) (by norm_num)
theorem B3887507 : Blo 2303435 3887507 := bstep (se 1 (by rfl) ⟨2915630, by rfl⟩ : syracuseStep 3887507 = 5831261) B5831261
theorem B2591671 : Blo 2303435 2591671 := bstep (se 1 (by rfl) ⟨1943753, by rfl⟩ : syracuseStep 2591671 = 3887507) B3887507
theorem B3455561 : Blo 2303435 3455561 := bstep (se 2 (by rfl) ⟨1295835, by rfl⟩ : syracuseStep 3455561 = 2591671) B2591671
theorem B2303707 : Blo 2303435 2303707 := bstep (se 1 (by rfl) ⟨1727780, by rfl⟩ : syracuseStep 2303707 = 3455561) B3455561
theorem B4373453 : Blo 2303435 4373453 := bbase (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) (by norm_num)
theorem B11662541 : Blo 2303435 11662541 := bstep (se 3 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 11662541 = 4373453) B4373453
theorem B7775027 : Blo 2303435 7775027 := bstep (se 1 (by rfl) ⟨5831270, by rfl⟩ : syracuseStep 7775027 = 11662541) B11662541
theorem B5183351 : Blo 2303435 5183351 := bstep (se 1 (by rfl) ⟨3887513, by rfl⟩ : syracuseStep 5183351 = 7775027) B7775027
theorem B3455567 : Blo 2303435 3455567 := bstep (se 1 (by rfl) ⟨2591675, by rfl⟩ : syracuseStep 3455567 = 5183351) B5183351
theorem B2303711 : Blo 2303435 2303711 := bstep (se 1 (by rfl) ⟨1727783, by rfl⟩ : syracuseStep 2303711 = 3455567) B3455567
theorem B3455573 : Blo 2303435 3455573 := bbase (se 8 (by rfl) ⟨20247, by rfl⟩ : syracuseStep 3455573 = 40495) (by norm_num)
theorem B2303715 : Blo 2303435 2303715 := bstep (se 1 (by rfl) ⟨1727786, by rfl⟩ : syracuseStep 2303715 = 3455573) B3455573
theorem B7380229 : Blo 2303435 7380229 := bbase (se 4 (by rfl) ⟨691896, by rfl⟩ : syracuseStep 7380229 = 1383793) (by norm_num)
theorem B9840305 : Blo 2303435 9840305 := bstep (se 2 (by rfl) ⟨3690114, by rfl⟩ : syracuseStep 9840305 = 7380229) B7380229
theorem B6560203 : Blo 2303435 6560203 := bstep (se 1 (by rfl) ⟨4920152, by rfl⟩ : syracuseStep 6560203 = 9840305) B9840305
theorem B8746937 : Blo 2303435 8746937 := bstep (se 2 (by rfl) ⟨3280101, by rfl⟩ : syracuseStep 8746937 = 6560203) B6560203
theorem B5831291 : Blo 2303435 5831291 := bstep (se 1 (by rfl) ⟨4373468, by rfl⟩ : syracuseStep 5831291 = 8746937) B8746937
theorem B3887527 : Blo 2303435 3887527 := bstep (se 1 (by rfl) ⟨2915645, by rfl⟩ : syracuseStep 3887527 = 5831291) B5831291
theorem B5183369 : Blo 2303435 5183369 := bstep (se 2 (by rfl) ⟨1943763, by rfl⟩ : syracuseStep 5183369 = 3887527) B3887527
theorem B3455579 : Blo 2303435 3455579 := bstep (se 1 (by rfl) ⟨2591684, by rfl⟩ : syracuseStep 3455579 = 5183369) B5183369
theorem B2303719 : Blo 2303435 2303719 := bstep (se 1 (by rfl) ⟨1727789, by rfl⟩ : syracuseStep 2303719 = 3455579) B3455579
theorem B2591689 : Blo 2303435 2591689 := bbase (se 2 (by rfl) ⟨971883, by rfl⟩ : syracuseStep 2591689 = 1943767) (by norm_num)
theorem B3455585 : Blo 2303435 3455585 := bstep (se 2 (by rfl) ⟨1295844, by rfl⟩ : syracuseStep 3455585 = 2591689) B2591689
theorem B2303723 : Blo 2303435 2303723 := bstep (se 1 (by rfl) ⟨1727792, by rfl⟩ : syracuseStep 2303723 = 3455585) B3455585
theorem B5254109 : Blo 2303435 5254109 := bbase (se 3 (by rfl) ⟨985145, by rfl⟩ : syracuseStep 5254109 = 1970291) (by norm_num)
theorem B3502739 : Blo 2303435 3502739 := bstep (se 1 (by rfl) ⟨2627054, by rfl⟩ : syracuseStep 3502739 = 5254109) B5254109
theorem B2335159 : Blo 2303435 2335159 := bstep (se 1 (by rfl) ⟨1751369, by rfl⟩ : syracuseStep 2335159 = 3502739) B3502739
theorem B12454181 : Blo 2303435 12454181 := bstep (se 4 (by rfl) ⟨1167579, by rfl⟩ : syracuseStep 12454181 = 2335159) B2335159
theorem B8302787 : Blo 2303435 8302787 := bstep (se 1 (by rfl) ⟨6227090, by rfl⟩ : syracuseStep 8302787 = 12454181) B12454181
theorem B5535191 : Blo 2303435 5535191 := bstep (se 1 (by rfl) ⟨4151393, by rfl⟩ : syracuseStep 5535191 = 8302787) B8302787
theorem B3690127 : Blo 2303435 3690127 := bstep (se 1 (by rfl) ⟨2767595, by rfl⟩ : syracuseStep 3690127 = 5535191) B5535191
theorem B19680677 : Blo 2303435 19680677 := bstep (se 4 (by rfl) ⟨1845063, by rfl⟩ : syracuseStep 19680677 = 3690127) B3690127
theorem B13120451 : Blo 2303435 13120451 := bstep (se 1 (by rfl) ⟨9840338, by rfl⟩ : syracuseStep 13120451 = 19680677) B19680677
theorem B8746967 : Blo 2303435 8746967 := bstep (se 1 (by rfl) ⟨6560225, by rfl⟩ : syracuseStep 8746967 = 13120451) B13120451
theorem B5831311 : Blo 2303435 5831311 := bstep (se 1 (by rfl) ⟨4373483, by rfl⟩ : syracuseStep 5831311 = 8746967) B8746967
theorem B7775081 : Blo 2303435 7775081 := bstep (se 2 (by rfl) ⟨2915655, by rfl⟩ : syracuseStep 7775081 = 5831311) B5831311
theorem B5183387 : Blo 2303435 5183387 := bstep (se 1 (by rfl) ⟨3887540, by rfl⟩ : syracuseStep 5183387 = 7775081) B7775081
theorem B3455591 : Blo 2303435 3455591 := bstep (se 1 (by rfl) ⟨2591693, by rfl⟩ : syracuseStep 3455591 = 5183387) B5183387
theorem B2303727 : Blo 2303435 2303727 := bstep (se 1 (by rfl) ⟨1727795, by rfl⟩ : syracuseStep 2303727 = 3455591) B3455591
theorem B3455597 : Blo 2303435 3455597 := bbase (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) (by norm_num)
theorem B2303731 : Blo 2303435 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B5183405 : Blo 2303435 5183405 := bbase (se 3 (by rfl) ⟨971888, by rfl⟩ : syracuseStep 5183405 = 1943777) (by norm_num)
theorem B3455603 : Blo 2303435 3455603 := bstep (se 1 (by rfl) ⟨2591702, by rfl⟩ : syracuseStep 3455603 = 5183405) B5183405
theorem B2303735 : Blo 2303435 2303735 := bstep (se 1 (by rfl) ⟨1727801, by rfl⟩ : syracuseStep 2303735 = 3455603) B3455603
theorem B6560261 : Blo 2303435 6560261 := bbase (se 4 (by rfl) ⟨615024, by rfl⟩ : syracuseStep 6560261 = 1230049) (by norm_num)
theorem B4373507 : Blo 2303435 4373507 := bstep (se 1 (by rfl) ⟨3280130, by rfl⟩ : syracuseStep 4373507 = 6560261) B6560261
theorem B2915671 : Blo 2303435 2915671 := bstep (se 1 (by rfl) ⟨2186753, by rfl⟩ : syracuseStep 2915671 = 4373507) B4373507
theorem B3887561 : Blo 2303435 3887561 := bstep (se 2 (by rfl) ⟨1457835, by rfl⟩ : syracuseStep 3887561 = 2915671) B2915671
theorem B2591707 : Blo 2303435 2591707 := bstep (se 1 (by rfl) ⟨1943780, by rfl⟩ : syracuseStep 2591707 = 3887561) B3887561
theorem B3455609 : Blo 2303435 3455609 := bstep (se 2 (by rfl) ⟨1295853, by rfl⟩ : syracuseStep 3455609 = 2591707) B2591707
theorem B2303739 : Blo 2303435 2303739 := bstep (se 1 (by rfl) ⟨1727804, by rfl⟩ : syracuseStep 2303739 = 3455609) B3455609
theorem B2699245 : Blo 2303435 2699245 := bbase (se 3 (by rfl) ⟨506108, by rfl⟩ : syracuseStep 2699245 = 1012217) (by norm_num)
theorem B14395973 : Blo 2303435 14395973 := bstep (se 4 (by rfl) ⟨1349622, by rfl⟩ : syracuseStep 14395973 = 2699245) B2699245
theorem B38389261 : Blo 2303435 38389261 := bstep (se 3 (by rfl) ⟨7197986, by rfl⟩ : syracuseStep 38389261 = 14395973) B14395973
theorem B51185681 : Blo 2303435 51185681 := bstep (se 2 (by rfl) ⟨19194630, by rfl⟩ : syracuseStep 51185681 = 38389261) B38389261
theorem B34123787 : Blo 2303435 34123787 := bstep (se 1 (by rfl) ⟨25592840, by rfl⟩ : syracuseStep 34123787 = 51185681) B51185681
theorem B22749191 : Blo 2303435 22749191 := bstep (se 1 (by rfl) ⟨17061893, by rfl⟩ : syracuseStep 22749191 = 34123787) B34123787
theorem B15166127 : Blo 2303435 15166127 := bstep (se 1 (by rfl) ⟨11374595, by rfl⟩ : syracuseStep 15166127 = 22749191) B22749191
theorem B40443005 : Blo 2303435 40443005 := bstep (se 3 (by rfl) ⟨7583063, by rfl⟩ : syracuseStep 40443005 = 15166127) B15166127
theorem B26962003 : Blo 2303435 26962003 := bstep (se 1 (by rfl) ⟨20221502, by rfl⟩ : syracuseStep 26962003 = 40443005) B40443005
theorem B143797349 : Blo 2303435 143797349 := bstep (se 4 (by rfl) ⟨13481001, by rfl⟩ : syracuseStep 143797349 = 26962003) B26962003
theorem B95864899 : Blo 2303435 95864899 := bstep (se 1 (by rfl) ⟨71898674, by rfl⟩ : syracuseStep 95864899 = 143797349) B143797349
theorem B127819865 : Blo 2303435 127819865 := bstep (se 2 (by rfl) ⟨47932449, by rfl⟩ : syracuseStep 127819865 = 95864899) B95864899
theorem B85213243 : Blo 2303435 85213243 := bstep (se 1 (by rfl) ⟨63909932, by rfl⟩ : syracuseStep 85213243 = 127819865) B127819865
theorem B113617657 : Blo 2303435 113617657 := bstep (se 2 (by rfl) ⟨42606621, by rfl⟩ : syracuseStep 113617657 = 85213243) B85213243
theorem B605960837 : Blo 2303435 605960837 := bstep (se 4 (by rfl) ⟨56808828, by rfl⟩ : syracuseStep 605960837 = 113617657) B113617657
theorem B403973891 : Blo 2303435 403973891 := bstep (se 1 (by rfl) ⟨302980418, by rfl⟩ : syracuseStep 403973891 = 605960837) B605960837
theorem B269315927 : Blo 2303435 269315927 := bstep (se 1 (by rfl) ⟨201986945, by rfl⟩ : syracuseStep 269315927 = 403973891) B403973891
theorem B179543951 : Blo 2303435 179543951 := bstep (se 1 (by rfl) ⟨134657963, by rfl⟩ : syracuseStep 179543951 = 269315927) B269315927
theorem B119695967 : Blo 2303435 119695967 := bstep (se 1 (by rfl) ⟨89771975, by rfl⟩ : syracuseStep 119695967 = 179543951) B179543951
theorem B79797311 : Blo 2303435 79797311 := bstep (se 1 (by rfl) ⟨59847983, by rfl⟩ : syracuseStep 79797311 = 119695967) B119695967
theorem B53198207 : Blo 2303435 53198207 := bstep (se 1 (by rfl) ⟨39898655, by rfl⟩ : syracuseStep 53198207 = 79797311) B79797311
theorem B35465471 : Blo 2303435 35465471 := bstep (se 1 (by rfl) ⟨26599103, by rfl⟩ : syracuseStep 35465471 = 53198207) B53198207
theorem B23643647 : Blo 2303435 23643647 := bstep (se 1 (by rfl) ⟨17732735, by rfl⟩ : syracuseStep 23643647 = 35465471) B35465471
theorem B15762431 : Blo 2303435 15762431 := bstep (se 1 (by rfl) ⟨11821823, by rfl⟩ : syracuseStep 15762431 = 23643647) B23643647
theorem B10508287 : Blo 2303435 10508287 := bstep (se 1 (by rfl) ⟨7881215, by rfl⟩ : syracuseStep 10508287 = 15762431) B15762431
theorem B14011049 : Blo 2303435 14011049 := bstep (se 2 (by rfl) ⟨5254143, by rfl⟩ : syracuseStep 14011049 = 10508287) B10508287
theorem B9340699 : Blo 2303435 9340699 := bstep (se 1 (by rfl) ⟨7005524, by rfl⟩ : syracuseStep 9340699 = 14011049) B14011049
theorem B12454265 : Blo 2303435 12454265 := bstep (se 2 (by rfl) ⟨4670349, by rfl⟩ : syracuseStep 12454265 = 9340699) B9340699
theorem B8302843 : Blo 2303435 8302843 := bstep (se 1 (by rfl) ⟨6227132, by rfl⟩ : syracuseStep 8302843 = 12454265) B12454265
theorem B44281829 : Blo 2303435 44281829 := bstep (se 4 (by rfl) ⟨4151421, by rfl⟩ : syracuseStep 44281829 = 8302843) B8302843
theorem B29521219 : Blo 2303435 29521219 := bstep (se 1 (by rfl) ⟨22140914, by rfl⟩ : syracuseStep 29521219 = 44281829) B44281829
theorem B39361625 : Blo 2303435 39361625 := bstep (se 2 (by rfl) ⟨14760609, by rfl⟩ : syracuseStep 39361625 = 29521219) B29521219
theorem B26241083 : Blo 2303435 26241083 := bstep (se 1 (by rfl) ⟨19680812, by rfl⟩ : syracuseStep 26241083 = 39361625) B39361625
theorem B17494055 : Blo 2303435 17494055 := bstep (se 1 (by rfl) ⟨13120541, by rfl⟩ : syracuseStep 17494055 = 26241083) B26241083
theorem B11662703 : Blo 2303435 11662703 := bstep (se 1 (by rfl) ⟨8747027, by rfl⟩ : syracuseStep 11662703 = 17494055) B17494055
theorem B7775135 : Blo 2303435 7775135 := bstep (se 1 (by rfl) ⟨5831351, by rfl⟩ : syracuseStep 7775135 = 11662703) B11662703
theorem B5183423 : Blo 2303435 5183423 := bstep (se 1 (by rfl) ⟨3887567, by rfl⟩ : syracuseStep 5183423 = 7775135) B7775135
theorem B3455615 : Blo 2303435 3455615 := bstep (se 1 (by rfl) ⟨2591711, by rfl⟩ : syracuseStep 3455615 = 5183423) B5183423
theorem B2303743 : Blo 2303435 2303743 := bstep (se 1 (by rfl) ⟨1727807, by rfl⟩ : syracuseStep 2303743 = 3455615) B3455615
theorem B3455621 : Blo 2303435 3455621 := bbase (se 4 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 3455621 = 647929) (by norm_num)
theorem B2303747 : Blo 2303435 2303747 := bstep (se 1 (by rfl) ⟨1727810, by rfl⟩ : syracuseStep 2303747 = 3455621) B3455621
theorem B3887581 : Blo 2303435 3887581 := bbase (se 3 (by rfl) ⟨728921, by rfl⟩ : syracuseStep 3887581 = 1457843) (by norm_num)
theorem B5183441 : Blo 2303435 5183441 := bstep (se 2 (by rfl) ⟨1943790, by rfl⟩ : syracuseStep 5183441 = 3887581) B3887581
theorem B3455627 : Blo 2303435 3455627 := bstep (se 1 (by rfl) ⟨2591720, by rfl⟩ : syracuseStep 3455627 = 5183441) B5183441
theorem B2303751 : Blo 2303435 2303751 := bstep (se 1 (by rfl) ⟨1727813, by rfl⟩ : syracuseStep 2303751 = 3455627) B3455627
theorem B2591725 : Blo 2303435 2591725 := bbase (se 3 (by rfl) ⟨485948, by rfl⟩ : syracuseStep 2591725 = 971897) (by norm_num)
theorem B3455633 : Blo 2303435 3455633 := bstep (se 2 (by rfl) ⟨1295862, by rfl⟩ : syracuseStep 3455633 = 2591725) B2591725
theorem B2303755 : Blo 2303435 2303755 := bstep (se 1 (by rfl) ⟨1727816, by rfl⟩ : syracuseStep 2303755 = 3455633) B3455633
theorem B7775189 : Blo 2303435 7775189 := bbase (se 7 (by rfl) ⟨91115, by rfl⟩ : syracuseStep 7775189 = 182231) (by norm_num)
theorem B5183459 : Blo 2303435 5183459 := bstep (se 1 (by rfl) ⟨3887594, by rfl⟩ : syracuseStep 5183459 = 7775189) B7775189
theorem B3455639 : Blo 2303435 3455639 := bstep (se 1 (by rfl) ⟨2591729, by rfl⟩ : syracuseStep 3455639 = 5183459) B5183459
theorem B2303759 : Blo 2303435 2303759 := bstep (se 1 (by rfl) ⟨1727819, by rfl⟩ : syracuseStep 2303759 = 3455639) B3455639
theorem B3455645 : Blo 2303435 3455645 := bbase (se 3 (by rfl) ⟨647933, by rfl⟩ : syracuseStep 3455645 = 1295867) (by norm_num)
theorem B2303763 : Blo 2303435 2303763 := bstep (se 1 (by rfl) ⟨1727822, by rfl⟩ : syracuseStep 2303763 = 3455645) B3455645
theorem B5183477 : Blo 2303435 5183477 := bbase (se 5 (by rfl) ⟨242975, by rfl⟩ : syracuseStep 5183477 = 485951) (by norm_num)
theorem B3455651 : Blo 2303435 3455651 := bstep (se 1 (by rfl) ⟨2591738, by rfl⟩ : syracuseStep 3455651 = 5183477) B5183477
theorem B2303767 : Blo 2303435 2303767 := bstep (se 1 (by rfl) ⟨1727825, by rfl⟩ : syracuseStep 2303767 = 3455651) B3455651
theorem B13327541 : Blo 2303435 13327541 := bbase (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) (by norm_num)
theorem B8885027 : Blo 2303435 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B5923351 : Blo 2303435 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B31591205 : Blo 2303435 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B21060803 : Blo 2303435 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B14040535 : Blo 2303435 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B18720713 : Blo 2303435 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B12480475 : Blo 2303435 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B16640633 : Blo 2303435 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B11093755 : Blo 2303435 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B14791673 : Blo 2303435 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B9861115 : Blo 2303435 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B13148153 : Blo 2303435 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B8765435 : Blo 2303435 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B5843623 : Blo 2303435 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B7791497 : Blo 2303435 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B5194331 : Blo 2303435 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B3462887 : Blo 2303435 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B2308591 : Blo 2303435 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B12312485 : Blo 2303435 12312485 := bstep (se 4 (by rfl) ⟨1154295, by rfl⟩ : syracuseStep 12312485 = 2308591) B2308591
theorem B8208323 : Blo 2303435 8208323 := bstep (se 1 (by rfl) ⟨6156242, by rfl⟩ : syracuseStep 8208323 = 12312485) B12312485
theorem B5472215 : Blo 2303435 5472215 := bstep (se 1 (by rfl) ⟨4104161, by rfl⟩ : syracuseStep 5472215 = 8208323) B8208323
theorem B3648143 : Blo 2303435 3648143 := bstep (se 1 (by rfl) ⟨2736107, by rfl⟩ : syracuseStep 3648143 = 5472215) B5472215
theorem B9728381 : Blo 2303435 9728381 := bstep (se 3 (by rfl) ⟨1824071, by rfl⟩ : syracuseStep 9728381 = 3648143) B3648143
theorem B25942349 : Blo 2303435 25942349 := bstep (se 3 (by rfl) ⟨4864190, by rfl⟩ : syracuseStep 25942349 = 9728381) B9728381
theorem B17294899 : Blo 2303435 17294899 := bstep (se 1 (by rfl) ⟨12971174, by rfl⟩ : syracuseStep 17294899 = 25942349) B25942349
theorem B23059865 : Blo 2303435 23059865 := bstep (se 2 (by rfl) ⟨8647449, by rfl⟩ : syracuseStep 23059865 = 17294899) B17294899
theorem B15373243 : Blo 2303435 15373243 := bstep (se 1 (by rfl) ⟨11529932, by rfl⟩ : syracuseStep 15373243 = 23059865) B23059865
theorem B20497657 : Blo 2303435 20497657 := bstep (se 2 (by rfl) ⟨7686621, by rfl⟩ : syracuseStep 20497657 = 15373243) B15373243
theorem B27330209 : Blo 2303435 27330209 := bstep (se 2 (by rfl) ⟨10248828, by rfl⟩ : syracuseStep 27330209 = 20497657) B20497657
theorem B18220139 : Blo 2303435 18220139 := bstep (se 1 (by rfl) ⟨13665104, by rfl⟩ : syracuseStep 18220139 = 27330209) B27330209
theorem B12146759 : Blo 2303435 12146759 := bstep (se 1 (by rfl) ⟨9110069, by rfl⟩ : syracuseStep 12146759 = 18220139) B18220139
theorem B8097839 : Blo 2303435 8097839 := bstep (se 1 (by rfl) ⟨6073379, by rfl⟩ : syracuseStep 8097839 = 12146759) B12146759
theorem B5398559 : Blo 2303435 5398559 := bstep (se 1 (by rfl) ⟨4048919, by rfl⟩ : syracuseStep 5398559 = 8097839) B8097839
theorem B3599039 : Blo 2303435 3599039 := bstep (se 1 (by rfl) ⟨2699279, by rfl⟩ : syracuseStep 3599039 = 5398559) B5398559
theorem B9597437 : Blo 2303435 9597437 := bstep (se 3 (by rfl) ⟨1799519, by rfl⟩ : syracuseStep 9597437 = 3599039) B3599039
theorem B6398291 : Blo 2303435 6398291 := bstep (se 1 (by rfl) ⟨4798718, by rfl⟩ : syracuseStep 6398291 = 9597437) B9597437
theorem B17062109 : Blo 2303435 17062109 := bstep (se 3 (by rfl) ⟨3199145, by rfl⟩ : syracuseStep 17062109 = 6398291) B6398291
theorem B11374739 : Blo 2303435 11374739 := bstep (se 1 (by rfl) ⟨8531054, by rfl⟩ : syracuseStep 11374739 = 17062109) B17062109
theorem B7583159 : Blo 2303435 7583159 := bstep (se 1 (by rfl) ⟨5687369, by rfl⟩ : syracuseStep 7583159 = 11374739) B11374739
theorem B5055439 : Blo 2303435 5055439 := bstep (se 1 (by rfl) ⟨3791579, by rfl⟩ : syracuseStep 5055439 = 7583159) B7583159
theorem B6740585 : Blo 2303435 6740585 := bstep (se 2 (by rfl) ⟨2527719, by rfl⟩ : syracuseStep 6740585 = 5055439) B5055439
theorem B4493723 : Blo 2303435 4493723 := bstep (se 1 (by rfl) ⟨3370292, by rfl⟩ : syracuseStep 4493723 = 6740585) B6740585
theorem B11983261 : Blo 2303435 11983261 := bstep (se 3 (by rfl) ⟨2246861, by rfl⟩ : syracuseStep 11983261 = 4493723) B4493723
theorem B15977681 : Blo 2303435 15977681 := bstep (se 2 (by rfl) ⟨5991630, by rfl⟩ : syracuseStep 15977681 = 11983261) B11983261
theorem B10651787 : Blo 2303435 10651787 := bstep (se 1 (by rfl) ⟨7988840, by rfl⟩ : syracuseStep 10651787 = 15977681) B15977681
theorem B7101191 : Blo 2303435 7101191 := bstep (se 1 (by rfl) ⟨5325893, by rfl⟩ : syracuseStep 7101191 = 10651787) B10651787
theorem B4734127 : Blo 2303435 4734127 := bstep (se 1 (by rfl) ⟨3550595, by rfl⟩ : syracuseStep 4734127 = 7101191) B7101191
theorem B6312169 : Blo 2303435 6312169 := bstep (se 2 (by rfl) ⟨2367063, by rfl⟩ : syracuseStep 6312169 = 4734127) B4734127
theorem B33664901 : Blo 2303435 33664901 := bstep (se 4 (by rfl) ⟨3156084, by rfl⟩ : syracuseStep 33664901 = 6312169) B6312169
theorem B359092277 : Blo 2303435 359092277 := bstep (se 5 (by rfl) ⟨16832450, by rfl⟩ : syracuseStep 359092277 = 33664901) B33664901
theorem B239394851 : Blo 2303435 239394851 := bstep (se 1 (by rfl) ⟨179546138, by rfl⟩ : syracuseStep 239394851 = 359092277) B359092277
theorem B159596567 : Blo 2303435 159596567 := bstep (se 1 (by rfl) ⟨119697425, by rfl⟩ : syracuseStep 159596567 = 239394851) B239394851
theorem B106397711 : Blo 2303435 106397711 := bstep (se 1 (by rfl) ⟨79798283, by rfl⟩ : syracuseStep 106397711 = 159596567) B159596567
theorem B70931807 : Blo 2303435 70931807 := bstep (se 1 (by rfl) ⟨53198855, by rfl⟩ : syracuseStep 70931807 = 106397711) B106397711
theorem B47287871 : Blo 2303435 47287871 := bstep (se 1 (by rfl) ⟨35465903, by rfl⟩ : syracuseStep 47287871 = 70931807) B70931807
theorem B31525247 : Blo 2303435 31525247 := bstep (se 1 (by rfl) ⟨23643935, by rfl⟩ : syracuseStep 31525247 = 47287871) B47287871
theorem B21016831 : Blo 2303435 21016831 := bstep (se 1 (by rfl) ⟨15762623, by rfl⟩ : syracuseStep 21016831 = 31525247) B31525247
theorem B28022441 : Blo 2303435 28022441 := bstep (se 2 (by rfl) ⟨10508415, by rfl⟩ : syracuseStep 28022441 = 21016831) B21016831
theorem B74726509 : Blo 2303435 74726509 := bstep (se 3 (by rfl) ⟨14011220, by rfl⟩ : syracuseStep 74726509 = 28022441) B28022441
theorem B99635345 : Blo 2303435 99635345 := bstep (se 2 (by rfl) ⟨37363254, by rfl⟩ : syracuseStep 99635345 = 74726509) B74726509
theorem B66423563 : Blo 2303435 66423563 := bstep (se 1 (by rfl) ⟨49817672, by rfl⟩ : syracuseStep 66423563 = 99635345) B99635345
theorem B44282375 : Blo 2303435 44282375 := bstep (se 1 (by rfl) ⟨33211781, by rfl⟩ : syracuseStep 44282375 = 66423563) B66423563
theorem B29521583 : Blo 2303435 29521583 := bstep (se 1 (by rfl) ⟨22141187, by rfl⟩ : syracuseStep 29521583 = 44282375) B44282375
theorem B19681055 : Blo 2303435 19681055 := bstep (se 1 (by rfl) ⟨14760791, by rfl⟩ : syracuseStep 19681055 = 29521583) B29521583
theorem B13120703 : Blo 2303435 13120703 := bstep (se 1 (by rfl) ⟨9840527, by rfl⟩ : syracuseStep 13120703 = 19681055) B19681055
theorem B8747135 : Blo 2303435 8747135 := bstep (se 1 (by rfl) ⟨6560351, by rfl⟩ : syracuseStep 8747135 = 13120703) B13120703
theorem B5831423 : Blo 2303435 5831423 := bstep (se 1 (by rfl) ⟨4373567, by rfl⟩ : syracuseStep 5831423 = 8747135) B8747135
theorem B3887615 : Blo 2303435 3887615 := bstep (se 1 (by rfl) ⟨2915711, by rfl⟩ : syracuseStep 3887615 = 5831423) B5831423
theorem B2591743 : Blo 2303435 2591743 := bstep (se 1 (by rfl) ⟨1943807, by rfl⟩ : syracuseStep 2591743 = 3887615) B3887615
theorem B3455657 : Blo 2303435 3455657 := bstep (se 2 (by rfl) ⟨1295871, by rfl⟩ : syracuseStep 3455657 = 2591743) B2591743
theorem B2303771 : Blo 2303435 2303771 := bstep (se 1 (by rfl) ⟨1727828, by rfl⟩ : syracuseStep 2303771 = 3455657) B3455657
theorem B3280181 : Blo 2303435 3280181 := bbase (se 5 (by rfl) ⟨153758, by rfl⟩ : syracuseStep 3280181 = 307517) (by norm_num)
theorem B8747149 : Blo 2303435 8747149 := bstep (se 3 (by rfl) ⟨1640090, by rfl⟩ : syracuseStep 8747149 = 3280181) B3280181
theorem B11662865 : Blo 2303435 11662865 := bstep (se 2 (by rfl) ⟨4373574, by rfl⟩ : syracuseStep 11662865 = 8747149) B8747149
theorem B7775243 : Blo 2303435 7775243 := bstep (se 1 (by rfl) ⟨5831432, by rfl⟩ : syracuseStep 7775243 = 11662865) B11662865
theorem B5183495 : Blo 2303435 5183495 := bstep (se 1 (by rfl) ⟨3887621, by rfl⟩ : syracuseStep 5183495 = 7775243) B7775243
theorem B3455663 : Blo 2303435 3455663 := bstep (se 1 (by rfl) ⟨2591747, by rfl⟩ : syracuseStep 3455663 = 5183495) B5183495
theorem B2303775 : Blo 2303435 2303775 := bstep (se 1 (by rfl) ⟨1727831, by rfl⟩ : syracuseStep 2303775 = 3455663) B3455663
theorem B3455669 : Blo 2303435 3455669 := bbase (se 5 (by rfl) ⟨161984, by rfl⟩ : syracuseStep 3455669 = 323969) (by norm_num)
theorem B2303779 : Blo 2303435 2303779 := bstep (se 1 (by rfl) ⟨1727834, by rfl⟩ : syracuseStep 2303779 = 3455669) B3455669
theorem B5831453 : Blo 2303435 5831453 := bbase (se 3 (by rfl) ⟨1093397, by rfl⟩ : syracuseStep 5831453 = 2186795) (by norm_num)
theorem B3887635 : Blo 2303435 3887635 := bstep (se 1 (by rfl) ⟨2915726, by rfl⟩ : syracuseStep 3887635 = 5831453) B5831453
theorem B5183513 : Blo 2303435 5183513 := bstep (se 2 (by rfl) ⟨1943817, by rfl⟩ : syracuseStep 5183513 = 3887635) B3887635
theorem B3455675 : Blo 2303435 3455675 := bstep (se 1 (by rfl) ⟨2591756, by rfl⟩ : syracuseStep 3455675 = 5183513) B5183513
theorem B2303783 : Blo 2303435 2303783 := bstep (se 1 (by rfl) ⟨1727837, by rfl⟩ : syracuseStep 2303783 = 3455675) B3455675
theorem B2591761 : Blo 2303435 2591761 := bbase (se 2 (by rfl) ⟨971910, by rfl⟩ : syracuseStep 2591761 = 1943821) (by norm_num)
theorem B3455681 : Blo 2303435 3455681 := bstep (se 2 (by rfl) ⟨1295880, by rfl⟩ : syracuseStep 3455681 = 2591761) B2591761
theorem B2303787 : Blo 2303435 2303787 := bstep (se 1 (by rfl) ⟨1727840, by rfl⟩ : syracuseStep 2303787 = 3455681) B3455681
theorem B4373605 : Blo 2303435 4373605 := bbase (se 4 (by rfl) ⟨410025, by rfl⟩ : syracuseStep 4373605 = 820051) (by norm_num)
theorem B5831473 : Blo 2303435 5831473 := bstep (se 2 (by rfl) ⟨2186802, by rfl⟩ : syracuseStep 5831473 = 4373605) B4373605
theorem B7775297 : Blo 2303435 7775297 := bstep (se 2 (by rfl) ⟨2915736, by rfl⟩ : syracuseStep 7775297 = 5831473) B5831473
theorem B5183531 : Blo 2303435 5183531 := bstep (se 1 (by rfl) ⟨3887648, by rfl⟩ : syracuseStep 5183531 = 7775297) B7775297
theorem B3455687 : Blo 2303435 3455687 := bstep (se 1 (by rfl) ⟨2591765, by rfl⟩ : syracuseStep 3455687 = 5183531) B5183531
theorem B2303791 : Blo 2303435 2303791 := bstep (se 1 (by rfl) ⟨1727843, by rfl⟩ : syracuseStep 2303791 = 3455687) B3455687
theorem B3455693 : Blo 2303435 3455693 := bbase (se 3 (by rfl) ⟨647942, by rfl⟩ : syracuseStep 3455693 = 1295885) (by norm_num)
theorem B2303795 : Blo 2303435 2303795 := bstep (se 1 (by rfl) ⟨1727846, by rfl⟩ : syracuseStep 2303795 = 3455693) B3455693
theorem B5183549 : Blo 2303435 5183549 := bbase (se 3 (by rfl) ⟨971915, by rfl⟩ : syracuseStep 5183549 = 1943831) (by norm_num)
theorem B3455699 : Blo 2303435 3455699 := bstep (se 1 (by rfl) ⟨2591774, by rfl⟩ : syracuseStep 3455699 = 5183549) B5183549
theorem B2303799 : Blo 2303435 2303799 := bstep (se 1 (by rfl) ⟨1727849, by rfl⟩ : syracuseStep 2303799 = 3455699) B3455699
theorem B3887669 : Blo 2303435 3887669 := bbase (se 5 (by rfl) ⟨182234, by rfl⟩ : syracuseStep 3887669 = 364469) (by norm_num)
theorem B2591779 : Blo 2303435 2591779 := bstep (se 1 (by rfl) ⟨1943834, by rfl⟩ : syracuseStep 2591779 = 3887669) B3887669
theorem B3455705 : Blo 2303435 3455705 := bstep (se 2 (by rfl) ⟨1295889, by rfl⟩ : syracuseStep 3455705 = 2591779) B2591779
theorem B2303803 : Blo 2303435 2303803 := bstep (se 1 (by rfl) ⟨1727852, by rfl⟩ : syracuseStep 2303803 = 3455705) B3455705
theorem B6560453 : Blo 2303435 6560453 := bbase (se 4 (by rfl) ⟨615042, by rfl⟩ : syracuseStep 6560453 = 1230085) (by norm_num)
theorem B17494541 : Blo 2303435 17494541 := bstep (se 3 (by rfl) ⟨3280226, by rfl⟩ : syracuseStep 17494541 = 6560453) B6560453
theorem B11663027 : Blo 2303435 11663027 := bstep (se 1 (by rfl) ⟨8747270, by rfl⟩ : syracuseStep 11663027 = 17494541) B17494541
theorem B7775351 : Blo 2303435 7775351 := bstep (se 1 (by rfl) ⟨5831513, by rfl⟩ : syracuseStep 7775351 = 11663027) B11663027
theorem B5183567 : Blo 2303435 5183567 := bstep (se 1 (by rfl) ⟨3887675, by rfl⟩ : syracuseStep 5183567 = 7775351) B7775351
theorem B3455711 : Blo 2303435 3455711 := bstep (se 1 (by rfl) ⟨2591783, by rfl⟩ : syracuseStep 3455711 = 5183567) B5183567
theorem B2303807 : Blo 2303435 2303807 := bstep (se 1 (by rfl) ⟨1727855, by rfl⟩ : syracuseStep 2303807 = 3455711) B3455711
theorem B3455717 : Blo 2303435 3455717 := bbase (se 4 (by rfl) ⟨323973, by rfl⟩ : syracuseStep 3455717 = 647947) (by norm_num)
theorem B2303811 : Blo 2303435 2303811 := bstep (se 1 (by rfl) ⟨1727858, by rfl⟩ : syracuseStep 2303811 = 3455717) B3455717
theorem B3690269 : Blo 2303435 3690269 := bbase (se 3 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 3690269 = 1383851) (by norm_num)
theorem B2460179 : Blo 2303435 2460179 := bstep (se 1 (by rfl) ⟨1845134, by rfl⟩ : syracuseStep 2460179 = 3690269) B3690269
theorem B6560477 : Blo 2303435 6560477 := bstep (se 3 (by rfl) ⟨1230089, by rfl⟩ : syracuseStep 6560477 = 2460179) B2460179
theorem B4373651 : Blo 2303435 4373651 := bstep (se 1 (by rfl) ⟨3280238, by rfl⟩ : syracuseStep 4373651 = 6560477) B6560477
theorem B2915767 : Blo 2303435 2915767 := bstep (se 1 (by rfl) ⟨2186825, by rfl⟩ : syracuseStep 2915767 = 4373651) B4373651
theorem B3887689 : Blo 2303435 3887689 := bstep (se 2 (by rfl) ⟨1457883, by rfl⟩ : syracuseStep 3887689 = 2915767) B2915767
theorem B5183585 : Blo 2303435 5183585 := bstep (se 2 (by rfl) ⟨1943844, by rfl⟩ : syracuseStep 5183585 = 3887689) B3887689
theorem B3455723 : Blo 2303435 3455723 := bstep (se 1 (by rfl) ⟨2591792, by rfl⟩ : syracuseStep 3455723 = 5183585) B5183585
theorem B2303815 : Blo 2303435 2303815 := bstep (se 1 (by rfl) ⟨1727861, by rfl⟩ : syracuseStep 2303815 = 3455723) B3455723
theorem B2591797 : Blo 2303435 2591797 := bbase (se 5 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 2591797 = 242981) (by norm_num)
theorem B3455729 : Blo 2303435 3455729 := bstep (se 2 (by rfl) ⟨1295898, by rfl⟩ : syracuseStep 3455729 = 2591797) B2591797
theorem B2303819 : Blo 2303435 2303819 := bstep (se 1 (by rfl) ⟨1727864, by rfl⟩ : syracuseStep 2303819 = 3455729) B3455729
theorem B2915777 : Blo 2303435 2915777 := bbase (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) (by norm_num)
theorem B7775405 : Blo 2303435 7775405 := bstep (se 3 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 7775405 = 2915777) B2915777
theorem B5183603 : Blo 2303435 5183603 := bstep (se 1 (by rfl) ⟨3887702, by rfl⟩ : syracuseStep 5183603 = 7775405) B7775405
theorem B3455735 : Blo 2303435 3455735 := bstep (se 1 (by rfl) ⟨2591801, by rfl⟩ : syracuseStep 3455735 = 5183603) B5183603
theorem B2303823 : Blo 2303435 2303823 := bstep (se 1 (by rfl) ⟨1727867, by rfl⟩ : syracuseStep 2303823 = 3455735) B3455735
theorem B3455741 : Blo 2303435 3455741 := bbase (se 3 (by rfl) ⟨647951, by rfl⟩ : syracuseStep 3455741 = 1295903) (by norm_num)
theorem B2303827 : Blo 2303435 2303827 := bstep (se 1 (by rfl) ⟨1727870, by rfl⟩ : syracuseStep 2303827 = 3455741) B3455741
theorem B5183621 : Blo 2303435 5183621 := bbase (se 4 (by rfl) ⟨485964, by rfl⟩ : syracuseStep 5183621 = 971929) (by norm_num)
theorem B3455747 : Blo 2303435 3455747 := bstep (se 1 (by rfl) ⟨2591810, by rfl⟩ : syracuseStep 3455747 = 5183621) B5183621
theorem B2303831 : Blo 2303435 2303831 := bstep (se 1 (by rfl) ⟨1727873, by rfl⟩ : syracuseStep 2303831 = 3455747) B3455747
theorem B3690301 : Blo 2303435 3690301 := bbase (se 3 (by rfl) ⟨691931, by rfl⟩ : syracuseStep 3690301 = 1383863) (by norm_num)
theorem B4920401 : Blo 2303435 4920401 := bstep (se 2 (by rfl) ⟨1845150, by rfl⟩ : syracuseStep 4920401 = 3690301) B3690301
theorem B3280267 : Blo 2303435 3280267 := bstep (se 1 (by rfl) ⟨2460200, by rfl⟩ : syracuseStep 3280267 = 4920401) B4920401
theorem B4373689 : Blo 2303435 4373689 := bstep (se 2 (by rfl) ⟨1640133, by rfl⟩ : syracuseStep 4373689 = 3280267) B3280267
theorem B5831585 : Blo 2303435 5831585 := bstep (se 2 (by rfl) ⟨2186844, by rfl⟩ : syracuseStep 5831585 = 4373689) B4373689
theorem B3887723 : Blo 2303435 3887723 := bstep (se 1 (by rfl) ⟨2915792, by rfl⟩ : syracuseStep 3887723 = 5831585) B5831585
theorem B2591815 : Blo 2303435 2591815 := bstep (se 1 (by rfl) ⟨1943861, by rfl⟩ : syracuseStep 2591815 = 3887723) B3887723
theorem B3455753 : Blo 2303435 3455753 := bstep (se 2 (by rfl) ⟨1295907, by rfl⟩ : syracuseStep 3455753 = 2591815) B2591815
theorem B2303835 : Blo 2303435 2303835 := bstep (se 1 (by rfl) ⟨1727876, by rfl⟩ : syracuseStep 2303835 = 3455753) B3455753
theorem B11663189 : Blo 2303435 11663189 := bbase (se 9 (by rfl) ⟨34169, by rfl⟩ : syracuseStep 11663189 = 68339) (by norm_num)
theorem B7775459 : Blo 2303435 7775459 := bstep (se 1 (by rfl) ⟨5831594, by rfl⟩ : syracuseStep 7775459 = 11663189) B11663189
theorem B5183639 : Blo 2303435 5183639 := bstep (se 1 (by rfl) ⟨3887729, by rfl⟩ : syracuseStep 5183639 = 7775459) B7775459
theorem B3455759 : Blo 2303435 3455759 := bstep (se 1 (by rfl) ⟨2591819, by rfl⟩ : syracuseStep 3455759 = 5183639) B5183639
theorem B2303839 : Blo 2303435 2303839 := bstep (se 1 (by rfl) ⟨1727879, by rfl⟩ : syracuseStep 2303839 = 3455759) B3455759
theorem B3455765 : Blo 2303435 3455765 := bbase (se 6 (by rfl) ⟨80994, by rfl⟩ : syracuseStep 3455765 = 161989) (by norm_num)
theorem B2303843 : Blo 2303435 2303843 := bstep (se 1 (by rfl) ⟨1727882, by rfl⟩ : syracuseStep 2303843 = 3455765) B3455765
theorem B5254381 : Blo 2303435 5254381 := bbase (se 3 (by rfl) ⟨985196, by rfl⟩ : syracuseStep 5254381 = 1970393) (by norm_num)
theorem B7005841 : Blo 2303435 7005841 := bstep (se 2 (by rfl) ⟨2627190, by rfl⟩ : syracuseStep 7005841 = 5254381) B5254381
theorem B37364485 : Blo 2303435 37364485 := bstep (se 4 (by rfl) ⟨3502920, by rfl⟩ : syracuseStep 37364485 = 7005841) B7005841
theorem B49819313 : Blo 2303435 49819313 := bstep (se 2 (by rfl) ⟨18682242, by rfl⟩ : syracuseStep 49819313 = 37364485) B37364485
theorem B33212875 : Blo 2303435 33212875 := bstep (se 1 (by rfl) ⟨24909656, by rfl⟩ : syracuseStep 33212875 = 49819313) B49819313
theorem B44283833 : Blo 2303435 44283833 := bstep (se 2 (by rfl) ⟨16606437, by rfl⟩ : syracuseStep 44283833 = 33212875) B33212875
theorem B29522555 : Blo 2303435 29522555 := bstep (se 1 (by rfl) ⟨22141916, by rfl⟩ : syracuseStep 29522555 = 44283833) B44283833
theorem B19681703 : Blo 2303435 19681703 := bstep (se 1 (by rfl) ⟨14761277, by rfl⟩ : syracuseStep 19681703 = 29522555) B29522555
theorem B13121135 : Blo 2303435 13121135 := bstep (se 1 (by rfl) ⟨9840851, by rfl⟩ : syracuseStep 13121135 = 19681703) B19681703
theorem B8747423 : Blo 2303435 8747423 := bstep (se 1 (by rfl) ⟨6560567, by rfl⟩ : syracuseStep 8747423 = 13121135) B13121135
theorem B5831615 : Blo 2303435 5831615 := bstep (se 1 (by rfl) ⟨4373711, by rfl⟩ : syracuseStep 5831615 = 8747423) B8747423
theorem B3887743 : Blo 2303435 3887743 := bstep (se 1 (by rfl) ⟨2915807, by rfl⟩ : syracuseStep 3887743 = 5831615) B5831615
theorem B5183657 : Blo 2303435 5183657 := bstep (se 2 (by rfl) ⟨1943871, by rfl⟩ : syracuseStep 5183657 = 3887743) B3887743
theorem B3455771 : Blo 2303435 3455771 := bstep (se 1 (by rfl) ⟨2591828, by rfl⟩ : syracuseStep 3455771 = 5183657) B5183657
theorem B2303847 : Blo 2303435 2303847 := bstep (se 1 (by rfl) ⟨1727885, by rfl⟩ : syracuseStep 2303847 = 3455771) B3455771
theorem B2591833 : Blo 2303435 2591833 := bbase (se 2 (by rfl) ⟨971937, by rfl⟩ : syracuseStep 2591833 = 1943875) (by norm_num)
theorem B3455777 : Blo 2303435 3455777 := bstep (se 2 (by rfl) ⟨1295916, by rfl⟩ : syracuseStep 3455777 = 2591833) B2591833
theorem B2303851 : Blo 2303435 2303851 := bstep (se 1 (by rfl) ⟨1727888, by rfl⟩ : syracuseStep 2303851 = 3455777) B3455777
theorem B2335289 : Blo 2303435 2335289 := bbase (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) (by norm_num)
theorem B6227437 : Blo 2303435 6227437 := bstep (se 3 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 6227437 = 2335289) B2335289
theorem B8303249 : Blo 2303435 8303249 := bstep (se 2 (by rfl) ⟨3113718, by rfl⟩ : syracuseStep 8303249 = 6227437) B6227437
theorem B5535499 : Blo 2303435 5535499 := bstep (se 1 (by rfl) ⟨4151624, by rfl⟩ : syracuseStep 5535499 = 8303249) B8303249
theorem B7380665 : Blo 2303435 7380665 := bstep (se 2 (by rfl) ⟨2767749, by rfl⟩ : syracuseStep 7380665 = 5535499) B5535499
theorem B4920443 : Blo 2303435 4920443 := bstep (se 1 (by rfl) ⟨3690332, by rfl⟩ : syracuseStep 4920443 = 7380665) B7380665
theorem B3280295 : Blo 2303435 3280295 := bstep (se 1 (by rfl) ⟨2460221, by rfl⟩ : syracuseStep 3280295 = 4920443) B4920443
theorem B8747453 : Blo 2303435 8747453 := bstep (se 3 (by rfl) ⟨1640147, by rfl⟩ : syracuseStep 8747453 = 3280295) B3280295
theorem B5831635 : Blo 2303435 5831635 := bstep (se 1 (by rfl) ⟨4373726, by rfl⟩ : syracuseStep 5831635 = 8747453) B8747453
theorem B7775513 : Blo 2303435 7775513 := bstep (se 2 (by rfl) ⟨2915817, by rfl⟩ : syracuseStep 7775513 = 5831635) B5831635
theorem B5183675 : Blo 2303435 5183675 := bstep (se 1 (by rfl) ⟨3887756, by rfl⟩ : syracuseStep 5183675 = 7775513) B7775513
theorem B3455783 : Blo 2303435 3455783 := bstep (se 1 (by rfl) ⟨2591837, by rfl⟩ : syracuseStep 3455783 = 5183675) B5183675
theorem B2303855 : Blo 2303435 2303855 := bstep (se 1 (by rfl) ⟨1727891, by rfl⟩ : syracuseStep 2303855 = 3455783) B3455783
theorem B3455789 : Blo 2303435 3455789 := bbase (se 3 (by rfl) ⟨647960, by rfl⟩ : syracuseStep 3455789 = 1295921) (by norm_num)
theorem B2303859 : Blo 2303435 2303859 := bstep (se 1 (by rfl) ⟨1727894, by rfl⟩ : syracuseStep 2303859 = 3455789) B3455789
theorem B5183693 : Blo 2303435 5183693 := bbase (se 3 (by rfl) ⟨971942, by rfl⟩ : syracuseStep 5183693 = 1943885) (by norm_num)
theorem B3455795 : Blo 2303435 3455795 := bstep (se 1 (by rfl) ⟨2591846, by rfl⟩ : syracuseStep 3455795 = 5183693) B5183693
theorem B2303863 : Blo 2303435 2303863 := bstep (se 1 (by rfl) ⟨1727897, by rfl⟩ : syracuseStep 2303863 = 3455795) B3455795
theorem B2915833 : Blo 2303435 2915833 := bbase (se 2 (by rfl) ⟨1093437, by rfl⟩ : syracuseStep 2915833 = 2186875) (by norm_num)
theorem B3887777 : Blo 2303435 3887777 := bstep (se 2 (by rfl) ⟨1457916, by rfl⟩ : syracuseStep 3887777 = 2915833) B2915833
theorem B2591851 : Blo 2303435 2591851 := bstep (se 1 (by rfl) ⟨1943888, by rfl⟩ : syracuseStep 2591851 = 3887777) B3887777
theorem B3455801 : Blo 2303435 3455801 := bstep (se 2 (by rfl) ⟨1295925, by rfl⟩ : syracuseStep 3455801 = 2591851) B2591851
theorem B2303867 : Blo 2303435 2303867 := bstep (se 1 (by rfl) ⟨1727900, by rfl⟩ : syracuseStep 2303867 = 3455801) B3455801
theorem B14011829 : Blo 2303435 14011829 := bbase (se 5 (by rfl) ⟨656804, by rfl⟩ : syracuseStep 14011829 = 1313609) (by norm_num)
theorem B9341219 : Blo 2303435 9341219 := bstep (se 1 (by rfl) ⟨7005914, by rfl⟩ : syracuseStep 9341219 = 14011829) B14011829
theorem B6227479 : Blo 2303435 6227479 := bstep (se 1 (by rfl) ⟨4670609, by rfl⟩ : syracuseStep 6227479 = 9341219) B9341219
theorem B8303305 : Blo 2303435 8303305 := bstep (se 2 (by rfl) ⟨3113739, by rfl⟩ : syracuseStep 8303305 = 6227479) B6227479
theorem B11071073 : Blo 2303435 11071073 := bstep (se 2 (by rfl) ⟨4151652, by rfl⟩ : syracuseStep 11071073 = 8303305) B8303305
theorem B7380715 : Blo 2303435 7380715 := bstep (se 1 (by rfl) ⟨5535536, by rfl⟩ : syracuseStep 7380715 = 11071073) B11071073
theorem B9840953 : Blo 2303435 9840953 := bstep (se 2 (by rfl) ⟨3690357, by rfl⟩ : syracuseStep 9840953 = 7380715) B7380715
theorem B26242541 : Blo 2303435 26242541 := bstep (se 3 (by rfl) ⟨4920476, by rfl⟩ : syracuseStep 26242541 = 9840953) B9840953
theorem B17495027 : Blo 2303435 17495027 := bstep (se 1 (by rfl) ⟨13121270, by rfl⟩ : syracuseStep 17495027 = 26242541) B26242541
theorem B11663351 : Blo 2303435 11663351 := bstep (se 1 (by rfl) ⟨8747513, by rfl⟩ : syracuseStep 11663351 = 17495027) B17495027
theorem B7775567 : Blo 2303435 7775567 := bstep (se 1 (by rfl) ⟨5831675, by rfl⟩ : syracuseStep 7775567 = 11663351) B11663351
theorem B5183711 : Blo 2303435 5183711 := bstep (se 1 (by rfl) ⟨3887783, by rfl⟩ : syracuseStep 5183711 = 7775567) B7775567
theorem B3455807 : Blo 2303435 3455807 := bstep (se 1 (by rfl) ⟨2591855, by rfl⟩ : syracuseStep 3455807 = 5183711) B5183711
theorem B2303871 : Blo 2303435 2303871 := bstep (se 1 (by rfl) ⟨1727903, by rfl⟩ : syracuseStep 2303871 = 3455807) B3455807
theorem B3455813 : Blo 2303435 3455813 := bbase (se 4 (by rfl) ⟨323982, by rfl⟩ : syracuseStep 3455813 = 647965) (by norm_num)
theorem B2303875 : Blo 2303435 2303875 := bstep (se 1 (by rfl) ⟨1727906, by rfl⟩ : syracuseStep 2303875 = 3455813) B3455813
theorem B3887797 : Blo 2303435 3887797 := bbase (se 5 (by rfl) ⟨182240, by rfl⟩ : syracuseStep 3887797 = 364481) (by norm_num)
theorem B5183729 : Blo 2303435 5183729 := bstep (se 2 (by rfl) ⟨1943898, by rfl⟩ : syracuseStep 5183729 = 3887797) B3887797
theorem B3455819 : Blo 2303435 3455819 := bstep (se 1 (by rfl) ⟨2591864, by rfl⟩ : syracuseStep 3455819 = 5183729) B5183729
theorem B2303879 : Blo 2303435 2303879 := bstep (se 1 (by rfl) ⟨1727909, by rfl⟩ : syracuseStep 2303879 = 3455819) B3455819
theorem B2591869 : Blo 2303435 2591869 := bbase (se 3 (by rfl) ⟨485975, by rfl⟩ : syracuseStep 2591869 = 971951) (by norm_num)
theorem B3455825 : Blo 2303435 3455825 := bstep (se 2 (by rfl) ⟨1295934, by rfl⟩ : syracuseStep 3455825 = 2591869) B2591869
theorem B2303883 : Blo 2303435 2303883 := bstep (se 1 (by rfl) ⟨1727912, by rfl⟩ : syracuseStep 2303883 = 3455825) B3455825
theorem B7775621 : Blo 2303435 7775621 := bbase (se 4 (by rfl) ⟨728964, by rfl⟩ : syracuseStep 7775621 = 1457929) (by norm_num)
theorem B5183747 : Blo 2303435 5183747 := bstep (se 1 (by rfl) ⟨3887810, by rfl⟩ : syracuseStep 5183747 = 7775621) B7775621
theorem B3455831 : Blo 2303435 3455831 := bstep (se 1 (by rfl) ⟨2591873, by rfl⟩ : syracuseStep 3455831 = 5183747) B5183747
theorem B2303887 : Blo 2303435 2303887 := bstep (se 1 (by rfl) ⟨1727915, by rfl⟩ : syracuseStep 2303887 = 3455831) B3455831
theorem B3455837 : Blo 2303435 3455837 := bbase (se 3 (by rfl) ⟨647969, by rfl⟩ : syracuseStep 3455837 = 1295939) (by norm_num)
theorem B2303891 : Blo 2303435 2303891 := bstep (se 1 (by rfl) ⟨1727918, by rfl⟩ : syracuseStep 2303891 = 3455837) B3455837
theorem B5183765 : Blo 2303435 5183765 := bbase (se 6 (by rfl) ⟨121494, by rfl⟩ : syracuseStep 5183765 = 242989) (by norm_num)
theorem B3455843 : Blo 2303435 3455843 := bstep (se 1 (by rfl) ⟨2591882, by rfl⟩ : syracuseStep 3455843 = 5183765) B5183765
theorem B2303895 : Blo 2303435 2303895 := bstep (se 1 (by rfl) ⟨1727921, by rfl⟩ : syracuseStep 2303895 = 3455843) B3455843
theorem B8747621 : Blo 2303435 8747621 := bbase (se 4 (by rfl) ⟨820089, by rfl⟩ : syracuseStep 8747621 = 1640179) (by norm_num)
theorem B5831747 : Blo 2303435 5831747 := bstep (se 1 (by rfl) ⟨4373810, by rfl⟩ : syracuseStep 5831747 = 8747621) B8747621
theorem B3887831 : Blo 2303435 3887831 := bstep (se 1 (by rfl) ⟨2915873, by rfl⟩ : syracuseStep 3887831 = 5831747) B5831747
theorem B2591887 : Blo 2303435 2591887 := bstep (se 1 (by rfl) ⟨1943915, by rfl⟩ : syracuseStep 2591887 = 3887831) B3887831
theorem B3455849 : Blo 2303435 3455849 := bstep (se 2 (by rfl) ⟨1295943, by rfl⟩ : syracuseStep 3455849 = 2591887) B2591887
theorem B2303899 : Blo 2303435 2303899 := bstep (se 1 (by rfl) ⟨1727924, by rfl⟩ : syracuseStep 2303899 = 3455849) B3455849
theorem B17733973 : Blo 2303435 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B23645297 : Blo 2303435 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B15763531 : Blo 2303435 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B21018041 : Blo 2303435 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B14012027 : Blo 2303435 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B9341351 : Blo 2303435 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B6227567 : Blo 2303435 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B4151711 : Blo 2303435 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B2767807 : Blo 2303435 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B3690409 : Blo 2303435 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B4920545 : Blo 2303435 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B13121453 : Blo 2303435 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B8747635 : Blo 2303435 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B11663513 : Blo 2303435 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B7775675 : Blo 2303435 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B5183783 : Blo 2303435 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B3455855 : Blo 2303435 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B2303903 : Blo 2303435 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B3455861 : Blo 2303435 3455861 := bbase (se 5 (by rfl) ⟨161993, by rfl⟩ : syracuseStep 3455861 = 323987) (by norm_num)
theorem B2303907 : Blo 2303435 2303907 := bstep (se 1 (by rfl) ⟨1727930, by rfl⟩ : syracuseStep 2303907 = 3455861) B3455861
theorem B2767817 : Blo 2303435 2767817 := bbase (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) (by norm_num)
theorem B7380845 : Blo 2303435 7380845 := bstep (se 3 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 7380845 = 2767817) B2767817
theorem B4920563 : Blo 2303435 4920563 := bstep (se 1 (by rfl) ⟨3690422, by rfl⟩ : syracuseStep 4920563 = 7380845) B7380845
theorem B3280375 : Blo 2303435 3280375 := bstep (se 1 (by rfl) ⟨2460281, by rfl⟩ : syracuseStep 3280375 = 4920563) B4920563
theorem B4373833 : Blo 2303435 4373833 := bstep (se 2 (by rfl) ⟨1640187, by rfl⟩ : syracuseStep 4373833 = 3280375) B3280375
theorem B5831777 : Blo 2303435 5831777 := bstep (se 2 (by rfl) ⟨2186916, by rfl⟩ : syracuseStep 5831777 = 4373833) B4373833
theorem B3887851 : Blo 2303435 3887851 := bstep (se 1 (by rfl) ⟨2915888, by rfl⟩ : syracuseStep 3887851 = 5831777) B5831777
theorem B5183801 : Blo 2303435 5183801 := bstep (se 2 (by rfl) ⟨1943925, by rfl⟩ : syracuseStep 5183801 = 3887851) B3887851
theorem B3455867 : Blo 2303435 3455867 := bstep (se 1 (by rfl) ⟨2591900, by rfl⟩ : syracuseStep 3455867 = 5183801) B5183801
theorem B2303911 : Blo 2303435 2303911 := bstep (se 1 (by rfl) ⟨1727933, by rfl⟩ : syracuseStep 2303911 = 3455867) B3455867
theorem B2591905 : Blo 2303435 2591905 := bbase (se 2 (by rfl) ⟨971964, by rfl⟩ : syracuseStep 2591905 = 1943929) (by norm_num)
theorem B3455873 : Blo 2303435 3455873 := bstep (se 2 (by rfl) ⟨1295952, by rfl⟩ : syracuseStep 3455873 = 2591905) B2591905
theorem B2303915 : Blo 2303435 2303915 := bstep (se 1 (by rfl) ⟨1727936, by rfl⟩ : syracuseStep 2303915 = 3455873) B3455873
theorem B5831797 : Blo 2303435 5831797 := bbase (se 5 (by rfl) ⟨273365, by rfl⟩ : syracuseStep 5831797 = 546731) (by norm_num)
theorem B7775729 : Blo 2303435 7775729 := bstep (se 2 (by rfl) ⟨2915898, by rfl⟩ : syracuseStep 7775729 = 5831797) B5831797
theorem B5183819 : Blo 2303435 5183819 := bstep (se 1 (by rfl) ⟨3887864, by rfl⟩ : syracuseStep 5183819 = 7775729) B7775729
theorem B3455879 : Blo 2303435 3455879 := bstep (se 1 (by rfl) ⟨2591909, by rfl⟩ : syracuseStep 3455879 = 5183819) B5183819
theorem B2303919 : Blo 2303435 2303919 := bstep (se 1 (by rfl) ⟨1727939, by rfl⟩ : syracuseStep 2303919 = 3455879) B3455879
theorem B3455885 : Blo 2303435 3455885 := bbase (se 3 (by rfl) ⟨647978, by rfl⟩ : syracuseStep 3455885 = 1295957) (by norm_num)
theorem B2303923 : Blo 2303435 2303923 := bstep (se 1 (by rfl) ⟨1727942, by rfl⟩ : syracuseStep 2303923 = 3455885) B3455885
theorem B5183837 : Blo 2303435 5183837 := bbase (se 3 (by rfl) ⟨971969, by rfl⟩ : syracuseStep 5183837 = 1943939) (by norm_num)
theorem B3455891 : Blo 2303435 3455891 := bstep (se 1 (by rfl) ⟨2591918, by rfl⟩ : syracuseStep 3455891 = 5183837) B5183837
theorem B2303927 : Blo 2303435 2303927 := bstep (se 1 (by rfl) ⟨1727945, by rfl⟩ : syracuseStep 2303927 = 3455891) B3455891
theorem B3887885 : Blo 2303435 3887885 := bbase (se 3 (by rfl) ⟨728978, by rfl⟩ : syracuseStep 3887885 = 1457957) (by norm_num)
theorem B2591923 : Blo 2303435 2591923 := bstep (se 1 (by rfl) ⟨1943942, by rfl⟩ : syracuseStep 2591923 = 3887885) B3887885
theorem B3455897 : Blo 2303435 3455897 := bstep (se 2 (by rfl) ⟨1295961, by rfl⟩ : syracuseStep 3455897 = 2591923) B2591923
theorem B2303931 : Blo 2303435 2303931 := bstep (se 1 (by rfl) ⟨1727948, by rfl⟩ : syracuseStep 2303931 = 3455897) B3455897
theorem B19682453 : Blo 2303435 19682453 := bbase (se 6 (by rfl) ⟨461307, by rfl⟩ : syracuseStep 19682453 = 922615) (by norm_num)
theorem B13121635 : Blo 2303435 13121635 := bstep (se 1 (by rfl) ⟨9841226, by rfl⟩ : syracuseStep 13121635 = 19682453) B19682453
theorem B17495513 : Blo 2303435 17495513 := bstep (se 2 (by rfl) ⟨6560817, by rfl⟩ : syracuseStep 17495513 = 13121635) B13121635
theorem B11663675 : Blo 2303435 11663675 := bstep (se 1 (by rfl) ⟨8747756, by rfl⟩ : syracuseStep 11663675 = 17495513) B17495513
theorem B7775783 : Blo 2303435 7775783 := bstep (se 1 (by rfl) ⟨5831837, by rfl⟩ : syracuseStep 7775783 = 11663675) B11663675
theorem B5183855 : Blo 2303435 5183855 := bstep (se 1 (by rfl) ⟨3887891, by rfl⟩ : syracuseStep 5183855 = 7775783) B7775783
theorem B3455903 : Blo 2303435 3455903 := bstep (se 1 (by rfl) ⟨2591927, by rfl⟩ : syracuseStep 3455903 = 5183855) B5183855
theorem B2303935 : Blo 2303435 2303935 := bstep (se 1 (by rfl) ⟨1727951, by rfl⟩ : syracuseStep 2303935 = 3455903) B3455903
theorem B3455909 : Blo 2303435 3455909 := bbase (se 4 (by rfl) ⟨323991, by rfl⟩ : syracuseStep 3455909 = 647983) (by norm_num)
theorem B2303939 : Blo 2303435 2303939 := bstep (se 1 (by rfl) ⟨1727954, by rfl⟩ : syracuseStep 2303939 = 3455909) B3455909
theorem B2915929 : Blo 2303435 2915929 := bbase (se 2 (by rfl) ⟨1093473, by rfl⟩ : syracuseStep 2915929 = 2186947) (by norm_num)
theorem B3887905 : Blo 2303435 3887905 := bstep (se 2 (by rfl) ⟨1457964, by rfl⟩ : syracuseStep 3887905 = 2915929) B2915929
theorem B5183873 : Blo 2303435 5183873 := bstep (se 2 (by rfl) ⟨1943952, by rfl⟩ : syracuseStep 5183873 = 3887905) B3887905
theorem B3455915 : Blo 2303435 3455915 := bstep (se 1 (by rfl) ⟨2591936, by rfl⟩ : syracuseStep 3455915 = 5183873) B5183873
theorem B2303943 : Blo 2303435 2303943 := bstep (se 1 (by rfl) ⟨1727957, by rfl⟩ : syracuseStep 2303943 = 3455915) B3455915
theorem B2591941 : Blo 2303435 2591941 := bbase (se 4 (by rfl) ⟨242994, by rfl⟩ : syracuseStep 2591941 = 485989) (by norm_num)
theorem B3455921 : Blo 2303435 3455921 := bstep (se 2 (by rfl) ⟨1295970, by rfl⟩ : syracuseStep 3455921 = 2591941) B2591941
theorem B2303947 : Blo 2303435 2303947 := bstep (se 1 (by rfl) ⟨1727960, by rfl⟩ : syracuseStep 2303947 = 3455921) B3455921
theorem B4373909 : Blo 2303435 4373909 := bbase (se 6 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 4373909 = 205027) (by norm_num)
theorem B2915939 : Blo 2303435 2915939 := bstep (se 1 (by rfl) ⟨2186954, by rfl⟩ : syracuseStep 2915939 = 4373909) B4373909
theorem B7775837 : Blo 2303435 7775837 := bstep (se 3 (by rfl) ⟨1457969, by rfl⟩ : syracuseStep 7775837 = 2915939) B2915939
theorem B5183891 : Blo 2303435 5183891 := bstep (se 1 (by rfl) ⟨3887918, by rfl⟩ : syracuseStep 5183891 = 7775837) B7775837
theorem B3455927 : Blo 2303435 3455927 := bstep (se 1 (by rfl) ⟨2591945, by rfl⟩ : syracuseStep 3455927 = 5183891) B5183891
theorem B2303951 : Blo 2303435 2303951 := bstep (se 1 (by rfl) ⟨1727963, by rfl⟩ : syracuseStep 2303951 = 3455927) B3455927
theorem B3455933 : Blo 2303435 3455933 := bbase (se 3 (by rfl) ⟨647987, by rfl⟩ : syracuseStep 3455933 = 1295975) (by norm_num)
theorem B2303955 : Blo 2303435 2303955 := bstep (se 1 (by rfl) ⟨1727966, by rfl⟩ : syracuseStep 2303955 = 3455933) B3455933
theorem B5183909 : Blo 2303435 5183909 := bbase (se 4 (by rfl) ⟨485991, by rfl⟩ : syracuseStep 5183909 = 971983) (by norm_num)
theorem B3455939 : Blo 2303435 3455939 := bstep (se 1 (by rfl) ⟨2591954, by rfl⟩ : syracuseStep 3455939 = 5183909) B5183909
theorem B2303959 : Blo 2303435 2303959 := bstep (se 1 (by rfl) ⟨1727969, by rfl⟩ : syracuseStep 2303959 = 3455939) B3455939
theorem B5831909 : Blo 2303435 5831909 := bbase (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) (by norm_num)
theorem B3887939 : Blo 2303435 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B2591959 : Blo 2303435 2591959 := bstep (se 1 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 2591959 = 3887939) B3887939
theorem B3455945 : Blo 2303435 3455945 := bstep (se 2 (by rfl) ⟨1295979, by rfl⟩ : syracuseStep 3455945 = 2591959) B2591959
theorem B2303963 : Blo 2303435 2303963 := bstep (se 1 (by rfl) ⟨1727972, by rfl⟩ : syracuseStep 2303963 = 3455945) B3455945
theorem B2460341 : Blo 2303435 2460341 := bbase (se 5 (by rfl) ⟨115328, by rfl⟩ : syracuseStep 2460341 = 230657) (by norm_num)
theorem B6560909 : Blo 2303435 6560909 := bstep (se 3 (by rfl) ⟨1230170, by rfl⟩ : syracuseStep 6560909 = 2460341) B2460341
theorem B4373939 : Blo 2303435 4373939 := bstep (se 1 (by rfl) ⟨3280454, by rfl⟩ : syracuseStep 4373939 = 6560909) B6560909
theorem B11663837 : Blo 2303435 11663837 := bstep (se 3 (by rfl) ⟨2186969, by rfl⟩ : syracuseStep 11663837 = 4373939) B4373939
theorem B7775891 : Blo 2303435 7775891 := bstep (se 1 (by rfl) ⟨5831918, by rfl⟩ : syracuseStep 7775891 = 11663837) B11663837
theorem B5183927 : Blo 2303435 5183927 := bstep (se 1 (by rfl) ⟨3887945, by rfl⟩ : syracuseStep 5183927 = 7775891) B7775891
theorem B3455951 : Blo 2303435 3455951 := bstep (se 1 (by rfl) ⟨2591963, by rfl⟩ : syracuseStep 3455951 = 5183927) B5183927
theorem B2303967 : Blo 2303435 2303967 := bstep (se 1 (by rfl) ⟨1727975, by rfl⟩ : syracuseStep 2303967 = 3455951) B3455951
theorem B3455957 : Blo 2303435 3455957 := bbase (se 7 (by rfl) ⟨40499, by rfl⟩ : syracuseStep 3455957 = 80999) (by norm_num)
theorem B2303971 : Blo 2303435 2303971 := bstep (se 1 (by rfl) ⟨1727978, by rfl⟩ : syracuseStep 2303971 = 3455957) B3455957
theorem B8747909 : Blo 2303435 8747909 := bbase (se 4 (by rfl) ⟨820116, by rfl⟩ : syracuseStep 8747909 = 1640233) (by norm_num)
theorem B5831939 : Blo 2303435 5831939 := bstep (se 1 (by rfl) ⟨4373954, by rfl⟩ : syracuseStep 5831939 = 8747909) B8747909
theorem B3887959 : Blo 2303435 3887959 := bstep (se 1 (by rfl) ⟨2915969, by rfl⟩ : syracuseStep 3887959 = 5831939) B5831939
theorem B5183945 : Blo 2303435 5183945 := bstep (se 2 (by rfl) ⟨1943979, by rfl⟩ : syracuseStep 5183945 = 3887959) B3887959
theorem B3455963 : Blo 2303435 3455963 := bstep (se 1 (by rfl) ⟨2591972, by rfl⟩ : syracuseStep 3455963 = 5183945) B5183945
theorem B2303975 : Blo 2303435 2303975 := bstep (se 1 (by rfl) ⟨1727981, by rfl⟩ : syracuseStep 2303975 = 3455963) B3455963
theorem B2591977 : Blo 2303435 2591977 := bbase (se 2 (by rfl) ⟨971991, by rfl⟩ : syracuseStep 2591977 = 1943983) (by norm_num)
theorem B3455969 : Blo 2303435 3455969 := bstep (se 2 (by rfl) ⟨1295988, by rfl⟩ : syracuseStep 3455969 = 2591977) B2591977
theorem B2303979 : Blo 2303435 2303979 := bstep (se 1 (by rfl) ⟨1727984, by rfl⟩ : syracuseStep 2303979 = 3455969) B3455969
theorem B13121909 : Blo 2303435 13121909 := bbase (se 5 (by rfl) ⟨615089, by rfl⟩ : syracuseStep 13121909 = 1230179) (by norm_num)
theorem B8747939 : Blo 2303435 8747939 := bstep (se 1 (by rfl) ⟨6560954, by rfl⟩ : syracuseStep 8747939 = 13121909) B13121909
theorem B5831959 : Blo 2303435 5831959 := bstep (se 1 (by rfl) ⟨4373969, by rfl⟩ : syracuseStep 5831959 = 8747939) B8747939
theorem B7775945 : Blo 2303435 7775945 := bstep (se 2 (by rfl) ⟨2915979, by rfl⟩ : syracuseStep 7775945 = 5831959) B5831959
theorem B5183963 : Blo 2303435 5183963 := bstep (se 1 (by rfl) ⟨3887972, by rfl⟩ : syracuseStep 5183963 = 7775945) B7775945
theorem B3455975 : Blo 2303435 3455975 := bstep (se 1 (by rfl) ⟨2591981, by rfl⟩ : syracuseStep 3455975 = 5183963) B5183963
theorem B2303983 : Blo 2303435 2303983 := bstep (se 1 (by rfl) ⟨1727987, by rfl⟩ : syracuseStep 2303983 = 3455975) B3455975
theorem B3455981 : Blo 2303435 3455981 := bbase (se 3 (by rfl) ⟨647996, by rfl⟩ : syracuseStep 3455981 = 1295993) (by norm_num)
theorem B2303987 : Blo 2303435 2303987 := bstep (se 1 (by rfl) ⟨1727990, by rfl⟩ : syracuseStep 2303987 = 3455981) B3455981
theorem B5183981 : Blo 2303435 5183981 := bbase (se 3 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 5183981 = 1943993) (by norm_num)
theorem B3455987 : Blo 2303435 3455987 := bstep (se 1 (by rfl) ⟨2591990, by rfl⟩ : syracuseStep 3455987 = 5183981) B5183981
theorem B2303991 : Blo 2303435 2303991 := bstep (se 1 (by rfl) ⟨1727993, by rfl⟩ : syracuseStep 2303991 = 3455987) B3455987
theorem B2955781 : Blo 2303435 2955781 := bbase (se 4 (by rfl) ⟨277104, by rfl⟩ : syracuseStep 2955781 = 554209) (by norm_num)
theorem B3941041 : Blo 2303435 3941041 := bstep (se 2 (by rfl) ⟨1477890, by rfl⟩ : syracuseStep 3941041 = 2955781) B2955781
theorem B5254721 : Blo 2303435 5254721 := bstep (se 2 (by rfl) ⟨1970520, by rfl⟩ : syracuseStep 5254721 = 3941041) B3941041
theorem B3503147 : Blo 2303435 3503147 := bstep (se 1 (by rfl) ⟨2627360, by rfl⟩ : syracuseStep 3503147 = 5254721) B5254721
theorem B9341725 : Blo 2303435 9341725 := bstep (se 3 (by rfl) ⟨1751573, by rfl⟩ : syracuseStep 9341725 = 3503147) B3503147
theorem B12455633 : Blo 2303435 12455633 := bstep (se 2 (by rfl) ⟨4670862, by rfl⟩ : syracuseStep 12455633 = 9341725) B9341725
theorem B8303755 : Blo 2303435 8303755 := bstep (se 1 (by rfl) ⟨6227816, by rfl⟩ : syracuseStep 8303755 = 12455633) B12455633
theorem B11071673 : Blo 2303435 11071673 := bstep (se 2 (by rfl) ⟨4151877, by rfl⟩ : syracuseStep 11071673 = 8303755) B8303755
theorem B7381115 : Blo 2303435 7381115 := bstep (se 1 (by rfl) ⟨5535836, by rfl⟩ : syracuseStep 7381115 = 11071673) B11071673
theorem B4920743 : Blo 2303435 4920743 := bstep (se 1 (by rfl) ⟨3690557, by rfl⟩ : syracuseStep 4920743 = 7381115) B7381115
theorem B3280495 : Blo 2303435 3280495 := bstep (se 1 (by rfl) ⟨2460371, by rfl⟩ : syracuseStep 3280495 = 4920743) B4920743
theorem B4373993 : Blo 2303435 4373993 := bstep (se 2 (by rfl) ⟨1640247, by rfl⟩ : syracuseStep 4373993 = 3280495) B3280495
theorem B2915995 : Blo 2303435 2915995 := bstep (se 1 (by rfl) ⟨2186996, by rfl⟩ : syracuseStep 2915995 = 4373993) B4373993
theorem B3887993 : Blo 2303435 3887993 := bstep (se 2 (by rfl) ⟨1457997, by rfl⟩ : syracuseStep 3887993 = 2915995) B2915995
theorem B2591995 : Blo 2303435 2591995 := bstep (se 1 (by rfl) ⟨1943996, by rfl⟩ : syracuseStep 2591995 = 3887993) B3887993
theorem B3455993 : Blo 2303435 3455993 := bstep (se 2 (by rfl) ⟨1295997, by rfl⟩ : syracuseStep 3455993 = 2591995) B2591995
theorem B2303995 : Blo 2303435 2303995 := bstep (se 1 (by rfl) ⟨1727996, by rfl⟩ : syracuseStep 2303995 = 3455993) B3455993
theorem B9469189 : Blo 2303435 9469189 := bbase (se 4 (by rfl) ⟨887736, by rfl⟩ : syracuseStep 9469189 = 1775473) (by norm_num)
theorem B50502341 : Blo 2303435 50502341 := bstep (se 4 (by rfl) ⟨4734594, by rfl⟩ : syracuseStep 50502341 = 9469189) B9469189
theorem B33668227 : Blo 2303435 33668227 := bstep (se 1 (by rfl) ⟨25251170, by rfl⟩ : syracuseStep 33668227 = 50502341) B50502341
theorem B179563877 : Blo 2303435 179563877 := bstep (se 4 (by rfl) ⟨16834113, by rfl⟩ : syracuseStep 179563877 = 33668227) B33668227
theorem B119709251 : Blo 2303435 119709251 := bstep (se 1 (by rfl) ⟨89781938, by rfl⟩ : syracuseStep 119709251 = 179563877) B179563877
theorem B79806167 : Blo 2303435 79806167 := bstep (se 1 (by rfl) ⟨59854625, by rfl⟩ : syracuseStep 79806167 = 119709251) B119709251
theorem B53204111 : Blo 2303435 53204111 := bstep (se 1 (by rfl) ⟨39903083, by rfl⟩ : syracuseStep 53204111 = 79806167) B79806167
theorem B35469407 : Blo 2303435 35469407 := bstep (se 1 (by rfl) ⟨26602055, by rfl⟩ : syracuseStep 35469407 = 53204111) B53204111
theorem B23646271 : Blo 2303435 23646271 := bstep (se 1 (by rfl) ⟨17734703, by rfl⟩ : syracuseStep 23646271 = 35469407) B35469407
theorem B31528361 : Blo 2303435 31528361 := bstep (se 2 (by rfl) ⟨11823135, by rfl⟩ : syracuseStep 31528361 = 23646271) B23646271
theorem B21018907 : Blo 2303435 21018907 := bstep (se 1 (by rfl) ⟨15764180, by rfl⟩ : syracuseStep 21018907 = 31528361) B31528361
theorem B28025209 : Blo 2303435 28025209 := bstep (se 2 (by rfl) ⟨10509453, by rfl⟩ : syracuseStep 28025209 = 21018907) B21018907
theorem B149467781 : Blo 2303435 149467781 := bstep (se 4 (by rfl) ⟨14012604, by rfl⟩ : syracuseStep 149467781 = 28025209) B28025209
theorem B99645187 : Blo 2303435 99645187 := bstep (se 1 (by rfl) ⟨74733890, by rfl⟩ : syracuseStep 99645187 = 149467781) B149467781
theorem B132860249 : Blo 2303435 132860249 := bstep (se 2 (by rfl) ⟨49822593, by rfl⟩ : syracuseStep 132860249 = 99645187) B99645187
theorem B88573499 : Blo 2303435 88573499 := bstep (se 1 (by rfl) ⟨66430124, by rfl⟩ : syracuseStep 88573499 = 132860249) B132860249
theorem B59048999 : Blo 2303435 59048999 := bstep (se 1 (by rfl) ⟨44286749, by rfl⟩ : syracuseStep 59048999 = 88573499) B88573499
theorem B39365999 : Blo 2303435 39365999 := bstep (se 1 (by rfl) ⟨29524499, by rfl⟩ : syracuseStep 39365999 = 59048999) B59048999
theorem B26243999 : Blo 2303435 26243999 := bstep (se 1 (by rfl) ⟨19682999, by rfl⟩ : syracuseStep 26243999 = 39365999) B39365999
theorem B17495999 : Blo 2303435 17495999 := bstep (se 1 (by rfl) ⟨13121999, by rfl⟩ : syracuseStep 17495999 = 26243999) B26243999
theorem B11663999 : Blo 2303435 11663999 := bstep (se 1 (by rfl) ⟨8747999, by rfl⟩ : syracuseStep 11663999 = 17495999) B17495999
theorem B7775999 : Blo 2303435 7775999 := bstep (se 1 (by rfl) ⟨5831999, by rfl⟩ : syracuseStep 7775999 = 11663999) B11663999
theorem B5183999 : Blo 2303435 5183999 := bstep (se 1 (by rfl) ⟨3887999, by rfl⟩ : syracuseStep 5183999 = 7775999) B7775999
theorem B3455999 : Blo 2303435 3455999 := bstep (se 1 (by rfl) ⟨2591999, by rfl⟩ : syracuseStep 3455999 = 5183999) B5183999
theorem B2303999 : Blo 2303435 2303999 := bstep (se 1 (by rfl) ⟨1727999, by rfl⟩ : syracuseStep 2303999 = 3455999) B3455999
theorem B3456005 : Blo 2303435 3456005 := bbase (se 4 (by rfl) ⟨324000, by rfl⟩ : syracuseStep 3456005 = 648001) (by norm_num)
theorem B2304003 : Blo 2303435 2304003 := bstep (se 1 (by rfl) ⟨1728002, by rfl⟩ : syracuseStep 2304003 = 3456005) B3456005
theorem B3888013 : Blo 2303435 3888013 := bbase (se 3 (by rfl) ⟨729002, by rfl⟩ : syracuseStep 3888013 = 1458005) (by norm_num)
theorem B5184017 : Blo 2303435 5184017 := bstep (se 2 (by rfl) ⟨1944006, by rfl⟩ : syracuseStep 5184017 = 3888013) B3888013
theorem B3456011 : Blo 2303435 3456011 := bstep (se 1 (by rfl) ⟨2592008, by rfl⟩ : syracuseStep 3456011 = 5184017) B5184017
theorem B2304007 : Blo 2303435 2304007 := bstep (se 1 (by rfl) ⟨1728005, by rfl⟩ : syracuseStep 2304007 = 3456011) B3456011
theorem B2592013 : Blo 2303435 2592013 := bbase (se 3 (by rfl) ⟨486002, by rfl⟩ : syracuseStep 2592013 = 972005) (by norm_num)
theorem B3456017 : Blo 2303435 3456017 := bstep (se 2 (by rfl) ⟨1296006, by rfl⟩ : syracuseStep 3456017 = 2592013) B2592013
theorem B2304011 : Blo 2303435 2304011 := bstep (se 1 (by rfl) ⟨1728008, by rfl⟩ : syracuseStep 2304011 = 3456017) B3456017
theorem B7776053 : Blo 2303435 7776053 := bbase (se 5 (by rfl) ⟨364502, by rfl⟩ : syracuseStep 7776053 = 729005) (by norm_num)
theorem B5184035 : Blo 2303435 5184035 := bstep (se 1 (by rfl) ⟨3888026, by rfl⟩ : syracuseStep 5184035 = 7776053) B7776053
theorem B3456023 : Blo 2303435 3456023 := bstep (se 1 (by rfl) ⟨2592017, by rfl⟩ : syracuseStep 3456023 = 5184035) B5184035
theorem B2304015 : Blo 2303435 2304015 := bstep (se 1 (by rfl) ⟨1728011, by rfl⟩ : syracuseStep 2304015 = 3456023) B3456023
theorem B3456029 : Blo 2303435 3456029 := bbase (se 3 (by rfl) ⟨648005, by rfl⟩ : syracuseStep 3456029 = 1296011) (by norm_num)
theorem B2304019 : Blo 2303435 2304019 := bstep (se 1 (by rfl) ⟨1728014, by rfl⟩ : syracuseStep 2304019 = 3456029) B3456029
theorem B5184053 : Blo 2303435 5184053 := bbase (se 5 (by rfl) ⟨243002, by rfl⟩ : syracuseStep 5184053 = 486005) (by norm_num)
theorem B3456035 : Blo 2303435 3456035 := bstep (se 1 (by rfl) ⟨2592026, by rfl⟩ : syracuseStep 3456035 = 5184053) B5184053
theorem B2304023 : Blo 2303435 2304023 := bstep (se 1 (by rfl) ⟨1728017, by rfl⟩ : syracuseStep 2304023 = 3456035) B3456035
theorem B9841621 : Blo 2303435 9841621 := bbase (se 7 (by rfl) ⟨115331, by rfl⟩ : syracuseStep 9841621 = 230663) (by norm_num)
theorem B13122161 : Blo 2303435 13122161 := bstep (se 2 (by rfl) ⟨4920810, by rfl⟩ : syracuseStep 13122161 = 9841621) B9841621
theorem B8748107 : Blo 2303435 8748107 := bstep (se 1 (by rfl) ⟨6561080, by rfl⟩ : syracuseStep 8748107 = 13122161) B13122161
theorem B5832071 : Blo 2303435 5832071 := bstep (se 1 (by rfl) ⟨4374053, by rfl⟩ : syracuseStep 5832071 = 8748107) B8748107
theorem B3888047 : Blo 2303435 3888047 := bstep (se 1 (by rfl) ⟨2916035, by rfl⟩ : syracuseStep 3888047 = 5832071) B5832071
theorem B2592031 : Blo 2303435 2592031 := bstep (se 1 (by rfl) ⟨1944023, by rfl⟩ : syracuseStep 2592031 = 3888047) B3888047
theorem B3456041 : Blo 2303435 3456041 := bstep (se 2 (by rfl) ⟨1296015, by rfl⟩ : syracuseStep 3456041 = 2592031) B2592031
theorem B2304027 : Blo 2303435 2304027 := bstep (se 1 (by rfl) ⟨1728020, by rfl⟩ : syracuseStep 2304027 = 3456041) B3456041
theorem B9841637 : Blo 2303435 9841637 := bbase (se 4 (by rfl) ⟨922653, by rfl⟩ : syracuseStep 9841637 = 1845307) (by norm_num)
theorem B6561091 : Blo 2303435 6561091 := bstep (se 1 (by rfl) ⟨4920818, by rfl⟩ : syracuseStep 6561091 = 9841637) B9841637
theorem B8748121 : Blo 2303435 8748121 := bstep (se 2 (by rfl) ⟨3280545, by rfl⟩ : syracuseStep 8748121 = 6561091) B6561091
theorem B11664161 : Blo 2303435 11664161 := bstep (se 2 (by rfl) ⟨4374060, by rfl⟩ : syracuseStep 11664161 = 8748121) B8748121
theorem B7776107 : Blo 2303435 7776107 := bstep (se 1 (by rfl) ⟨5832080, by rfl⟩ : syracuseStep 7776107 = 11664161) B11664161
theorem B5184071 : Blo 2303435 5184071 := bstep (se 1 (by rfl) ⟨3888053, by rfl⟩ : syracuseStep 5184071 = 7776107) B7776107
theorem B3456047 : Blo 2303435 3456047 := bstep (se 1 (by rfl) ⟨2592035, by rfl⟩ : syracuseStep 3456047 = 5184071) B5184071
theorem B2304031 : Blo 2303435 2304031 := bstep (se 1 (by rfl) ⟨1728023, by rfl⟩ : syracuseStep 2304031 = 3456047) B3456047
theorem B3456053 : Blo 2303435 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B2304035 : Blo 2303435 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B5832101 : Blo 2303435 5832101 := bbase (se 4 (by rfl) ⟨546759, by rfl⟩ : syracuseStep 5832101 = 1093519) (by norm_num)
theorem B3888067 : Blo 2303435 3888067 := bstep (se 1 (by rfl) ⟨2916050, by rfl⟩ : syracuseStep 3888067 = 5832101) B5832101
theorem B5184089 : Blo 2303435 5184089 := bstep (se 2 (by rfl) ⟨1944033, by rfl⟩ : syracuseStep 5184089 = 3888067) B3888067
theorem B3456059 : Blo 2303435 3456059 := bstep (se 1 (by rfl) ⟨2592044, by rfl⟩ : syracuseStep 3456059 = 5184089) B5184089
theorem B2304039 : Blo 2303435 2304039 := bstep (se 1 (by rfl) ⟨1728029, by rfl⟩ : syracuseStep 2304039 = 3456059) B3456059
theorem B2592049 : Blo 2303435 2592049 := bbase (se 2 (by rfl) ⟨972018, by rfl⟩ : syracuseStep 2592049 = 1944037) (by norm_num)
theorem B3456065 : Blo 2303435 3456065 := bstep (se 2 (by rfl) ⟨1296024, by rfl⟩ : syracuseStep 3456065 = 2592049) B2592049
theorem B2304043 : Blo 2303435 2304043 := bstep (se 1 (by rfl) ⟨1728032, by rfl⟩ : syracuseStep 2304043 = 3456065) B3456065
theorem B4920853 : Blo 2303435 4920853 := bbase (se 6 (by rfl) ⟨115332, by rfl⟩ : syracuseStep 4920853 = 230665) (by norm_num)
theorem B6561137 : Blo 2303435 6561137 := bstep (se 2 (by rfl) ⟨2460426, by rfl⟩ : syracuseStep 6561137 = 4920853) B4920853
theorem B4374091 : Blo 2303435 4374091 := bstep (se 1 (by rfl) ⟨3280568, by rfl⟩ : syracuseStep 4374091 = 6561137) B6561137
theorem B5832121 : Blo 2303435 5832121 := bstep (se 2 (by rfl) ⟨2187045, by rfl⟩ : syracuseStep 5832121 = 4374091) B4374091
theorem B7776161 : Blo 2303435 7776161 := bstep (se 2 (by rfl) ⟨2916060, by rfl⟩ : syracuseStep 7776161 = 5832121) B5832121
theorem B5184107 : Blo 2303435 5184107 := bstep (se 1 (by rfl) ⟨3888080, by rfl⟩ : syracuseStep 5184107 = 7776161) B7776161
theorem B3456071 : Blo 2303435 3456071 := bstep (se 1 (by rfl) ⟨2592053, by rfl⟩ : syracuseStep 3456071 = 5184107) B5184107
theorem B2304047 : Blo 2303435 2304047 := bstep (se 1 (by rfl) ⟨1728035, by rfl⟩ : syracuseStep 2304047 = 3456071) B3456071
theorem B3456077 : Blo 2303435 3456077 := bbase (se 3 (by rfl) ⟨648014, by rfl⟩ : syracuseStep 3456077 = 1296029) (by norm_num)
theorem B2304051 : Blo 2303435 2304051 := bstep (se 1 (by rfl) ⟨1728038, by rfl⟩ : syracuseStep 2304051 = 3456077) B3456077
theorem B5184125 : Blo 2303435 5184125 := bbase (se 3 (by rfl) ⟨972023, by rfl⟩ : syracuseStep 5184125 = 1944047) (by norm_num)
theorem B3456083 : Blo 2303435 3456083 := bstep (se 1 (by rfl) ⟨2592062, by rfl⟩ : syracuseStep 3456083 = 5184125) B5184125
theorem B2304055 : Blo 2303435 2304055 := bstep (se 1 (by rfl) ⟨1728041, by rfl⟩ : syracuseStep 2304055 = 3456083) B3456083
theorem B3888101 : Blo 2303435 3888101 := bbase (se 4 (by rfl) ⟨364509, by rfl⟩ : syracuseStep 3888101 = 729019) (by norm_num)
theorem B2592067 : Blo 2303435 2592067 := bstep (se 1 (by rfl) ⟨1944050, by rfl⟩ : syracuseStep 2592067 = 3888101) B3888101
theorem B3456089 : Blo 2303435 3456089 := bstep (se 2 (by rfl) ⟨1296033, by rfl⟩ : syracuseStep 3456089 = 2592067) B2592067
theorem B2304059 : Blo 2303435 2304059 := bstep (se 1 (by rfl) ⟨1728044, by rfl⟩ : syracuseStep 2304059 = 3456089) B3456089
theorem B2494013 : Blo 2303435 2494013 := bbase (se 3 (by rfl) ⟨467627, by rfl⟩ : syracuseStep 2494013 = 935255) (by norm_num)
theorem B26602805 : Blo 2303435 26602805 := bstep (se 5 (by rfl) ⟨1247006, by rfl⟩ : syracuseStep 26602805 = 2494013) B2494013
theorem B17735203 : Blo 2303435 17735203 := bstep (se 1 (by rfl) ⟨13301402, by rfl⟩ : syracuseStep 17735203 = 26602805) B26602805
theorem B23646937 : Blo 2303435 23646937 := bstep (se 2 (by rfl) ⟨8867601, by rfl⟩ : syracuseStep 23646937 = 17735203) B17735203
theorem B31529249 : Blo 2303435 31529249 := bstep (se 2 (by rfl) ⟨11823468, by rfl⟩ : syracuseStep 31529249 = 23646937) B23646937
theorem B21019499 : Blo 2303435 21019499 := bstep (se 1 (by rfl) ⟨15764624, by rfl⟩ : syracuseStep 21019499 = 31529249) B31529249
theorem B14012999 : Blo 2303435 14012999 := bstep (se 1 (by rfl) ⟨10509749, by rfl⟩ : syracuseStep 14012999 = 21019499) B21019499
theorem B9341999 : Blo 2303435 9341999 := bstep (se 1 (by rfl) ⟨7006499, by rfl⟩ : syracuseStep 9341999 = 14012999) B14012999
theorem B6227999 : Blo 2303435 6227999 := bstep (se 1 (by rfl) ⟨4670999, by rfl⟩ : syracuseStep 6227999 = 9341999) B9341999
theorem B4151999 : Blo 2303435 4151999 := bstep (se 1 (by rfl) ⟨3113999, by rfl⟩ : syracuseStep 4151999 = 6227999) B6227999
theorem B11071997 : Blo 2303435 11071997 := bstep (se 3 (by rfl) ⟨2075999, by rfl⟩ : syracuseStep 11071997 = 4151999) B4151999
theorem B7381331 : Blo 2303435 7381331 := bstep (se 1 (by rfl) ⟨5535998, by rfl⟩ : syracuseStep 7381331 = 11071997) B11071997
theorem B4920887 : Blo 2303435 4920887 := bstep (se 1 (by rfl) ⟨3690665, by rfl⟩ : syracuseStep 4920887 = 7381331) B7381331
theorem B3280591 : Blo 2303435 3280591 := bstep (se 1 (by rfl) ⟨2460443, by rfl⟩ : syracuseStep 3280591 = 4920887) B4920887
theorem B17496485 : Blo 2303435 17496485 := bstep (se 4 (by rfl) ⟨1640295, by rfl⟩ : syracuseStep 17496485 = 3280591) B3280591
theorem B11664323 : Blo 2303435 11664323 := bstep (se 1 (by rfl) ⟨8748242, by rfl⟩ : syracuseStep 11664323 = 17496485) B17496485
theorem B7776215 : Blo 2303435 7776215 := bstep (se 1 (by rfl) ⟨5832161, by rfl⟩ : syracuseStep 7776215 = 11664323) B11664323
theorem B5184143 : Blo 2303435 5184143 := bstep (se 1 (by rfl) ⟨3888107, by rfl⟩ : syracuseStep 5184143 = 7776215) B7776215
theorem B3456095 : Blo 2303435 3456095 := bstep (se 1 (by rfl) ⟨2592071, by rfl⟩ : syracuseStep 3456095 = 5184143) B5184143
theorem B2304063 : Blo 2303435 2304063 := bstep (se 1 (by rfl) ⟨1728047, by rfl⟩ : syracuseStep 2304063 = 3456095) B3456095
theorem B3456101 : Blo 2303435 3456101 := bbase (se 4 (by rfl) ⟨324009, by rfl⟩ : syracuseStep 3456101 = 648019) (by norm_num)
theorem B2304067 : Blo 2303435 2304067 := bstep (se 1 (by rfl) ⟨1728050, by rfl⟩ : syracuseStep 2304067 = 3456101) B3456101
theorem B3599509 : Blo 2303435 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B4799345 : Blo 2303435 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B12798253 : Blo 2303435 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B68257349 : Blo 2303435 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B45504899 : Blo 2303435 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B30336599 : Blo 2303435 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B20224399 : Blo 2303435 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B26965865 : Blo 2303435 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B17977243 : Blo 2303435 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B23969657 : Blo 2303435 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B15979771 : Blo 2303435 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B85225445 : Blo 2303435 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B56816963 : Blo 2303435 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B37877975 : Blo 2303435 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B25251983 : Blo 2303435 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B16834655 : Blo 2303435 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B44892413 : Blo 2303435 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B29928275 : Blo 2303435 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B19952183 : Blo 2303435 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B13301455 : Blo 2303435 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B17735273 : Blo 2303435 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B11823515 : Blo 2303435 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B7882343 : Blo 2303435 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B5254895 : Blo 2303435 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B3503263 : Blo 2303435 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B4671017 : Blo 2303435 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B3114011 : Blo 2303435 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B8304029 : Blo 2303435 8304029 := bstep (se 3 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 8304029 = 3114011) B3114011
theorem B5536019 : Blo 2303435 5536019 := bstep (se 1 (by rfl) ⟨4152014, by rfl⟩ : syracuseStep 5536019 = 8304029) B8304029
theorem B3690679 : Blo 2303435 3690679 := bstep (se 1 (by rfl) ⟨2768009, by rfl⟩ : syracuseStep 3690679 = 5536019) B5536019
theorem B4920905 : Blo 2303435 4920905 := bstep (se 2 (by rfl) ⟨1845339, by rfl⟩ : syracuseStep 4920905 = 3690679) B3690679
theorem B3280603 : Blo 2303435 3280603 := bstep (se 1 (by rfl) ⟨2460452, by rfl⟩ : syracuseStep 3280603 = 4920905) B4920905
theorem B4374137 : Blo 2303435 4374137 := bstep (se 2 (by rfl) ⟨1640301, by rfl⟩ : syracuseStep 4374137 = 3280603) B3280603
theorem B2916091 : Blo 2303435 2916091 := bstep (se 1 (by rfl) ⟨2187068, by rfl⟩ : syracuseStep 2916091 = 4374137) B4374137
theorem B3888121 : Blo 2303435 3888121 := bstep (se 2 (by rfl) ⟨1458045, by rfl⟩ : syracuseStep 3888121 = 2916091) B2916091
theorem B5184161 : Blo 2303435 5184161 := bstep (se 2 (by rfl) ⟨1944060, by rfl⟩ : syracuseStep 5184161 = 3888121) B3888121
theorem B3456107 : Blo 2303435 3456107 := bstep (se 1 (by rfl) ⟨2592080, by rfl⟩ : syracuseStep 3456107 = 5184161) B5184161
theorem B2304071 : Blo 2303435 2304071 := bstep (se 1 (by rfl) ⟨1728053, by rfl⟩ : syracuseStep 2304071 = 3456107) B3456107
theorem B2592085 : Blo 2303435 2592085 := bbase (se 11 (by rfl) ⟨1898, by rfl⟩ : syracuseStep 2592085 = 3797) (by norm_num)
theorem B3456113 : Blo 2303435 3456113 := bstep (se 2 (by rfl) ⟨1296042, by rfl⟩ : syracuseStep 3456113 = 2592085) B2592085
theorem B2304075 : Blo 2303435 2304075 := bstep (se 1 (by rfl) ⟨1728056, by rfl⟩ : syracuseStep 2304075 = 3456113) B3456113
theorem B2916101 : Blo 2303435 2916101 := bbase (se 4 (by rfl) ⟨273384, by rfl⟩ : syracuseStep 2916101 = 546769) (by norm_num)
theorem B7776269 : Blo 2303435 7776269 := bstep (se 3 (by rfl) ⟨1458050, by rfl⟩ : syracuseStep 7776269 = 2916101) B2916101
theorem B5184179 : Blo 2303435 5184179 := bstep (se 1 (by rfl) ⟨3888134, by rfl⟩ : syracuseStep 5184179 = 7776269) B7776269
theorem B3456119 : Blo 2303435 3456119 := bstep (se 1 (by rfl) ⟨2592089, by rfl⟩ : syracuseStep 3456119 = 5184179) B5184179
theorem B2304079 : Blo 2303435 2304079 := bstep (se 1 (by rfl) ⟨1728059, by rfl⟩ : syracuseStep 2304079 = 3456119) B3456119
theorem B3456125 : Blo 2303435 3456125 := bbase (se 3 (by rfl) ⟨648023, by rfl⟩ : syracuseStep 3456125 = 1296047) (by norm_num)
theorem B2304083 : Blo 2303435 2304083 := bstep (se 1 (by rfl) ⟨1728062, by rfl⟩ : syracuseStep 2304083 = 3456125) B3456125
theorem B5184197 : Blo 2303435 5184197 := bbase (se 4 (by rfl) ⟨486018, by rfl⟩ : syracuseStep 5184197 = 972037) (by norm_num)
theorem B3456131 : Blo 2303435 3456131 := bstep (se 1 (by rfl) ⟨2592098, by rfl⟩ : syracuseStep 3456131 = 5184197) B5184197
theorem B2304087 : Blo 2303435 2304087 := bstep (se 1 (by rfl) ⟨1728065, by rfl⟩ : syracuseStep 2304087 = 3456131) B3456131
theorem B22446389 : Blo 2303435 22446389 := bbase (se 5 (by rfl) ⟨1052174, by rfl⟩ : syracuseStep 22446389 = 2104349) (by norm_num)
theorem B14964259 : Blo 2303435 14964259 := bstep (se 1 (by rfl) ⟨11223194, by rfl⟩ : syracuseStep 14964259 = 22446389) B22446389
theorem B19952345 : Blo 2303435 19952345 := bstep (se 2 (by rfl) ⟨7482129, by rfl⟩ : syracuseStep 19952345 = 14964259) B14964259
theorem B53206253 : Blo 2303435 53206253 := bstep (se 3 (by rfl) ⟨9976172, by rfl⟩ : syracuseStep 53206253 = 19952345) B19952345
theorem B35470835 : Blo 2303435 35470835 := bstep (se 1 (by rfl) ⟨26603126, by rfl⟩ : syracuseStep 35470835 = 53206253) B53206253
theorem B23647223 : Blo 2303435 23647223 := bstep (se 1 (by rfl) ⟨17735417, by rfl⟩ : syracuseStep 23647223 = 35470835) B35470835
theorem B15764815 : Blo 2303435 15764815 := bstep (se 1 (by rfl) ⟨11823611, by rfl⟩ : syracuseStep 15764815 = 23647223) B23647223
theorem B21019753 : Blo 2303435 21019753 := bstep (se 2 (by rfl) ⟨7882407, by rfl⟩ : syracuseStep 21019753 = 15764815) B15764815
theorem B28026337 : Blo 2303435 28026337 := bstep (se 2 (by rfl) ⟨10509876, by rfl⟩ : syracuseStep 28026337 = 21019753) B21019753
theorem B37368449 : Blo 2303435 37368449 := bstep (se 2 (by rfl) ⟨14013168, by rfl⟩ : syracuseStep 37368449 = 28026337) B28026337
theorem B24912299 : Blo 2303435 24912299 := bstep (se 1 (by rfl) ⟨18684224, by rfl⟩ : syracuseStep 24912299 = 37368449) B37368449
theorem B16608199 : Blo 2303435 16608199 := bstep (se 1 (by rfl) ⟨12456149, by rfl⟩ : syracuseStep 16608199 = 24912299) B24912299
theorem B22144265 : Blo 2303435 22144265 := bstep (se 2 (by rfl) ⟨8304099, by rfl⟩ : syracuseStep 22144265 = 16608199) B16608199
theorem B14762843 : Blo 2303435 14762843 := bstep (se 1 (by rfl) ⟨11072132, by rfl⟩ : syracuseStep 14762843 = 22144265) B22144265
theorem B9841895 : Blo 2303435 9841895 := bstep (se 1 (by rfl) ⟨7381421, by rfl⟩ : syracuseStep 9841895 = 14762843) B14762843
theorem B6561263 : Blo 2303435 6561263 := bstep (se 1 (by rfl) ⟨4920947, by rfl⟩ : syracuseStep 6561263 = 9841895) B9841895
theorem B4374175 : Blo 2303435 4374175 := bstep (se 1 (by rfl) ⟨3280631, by rfl⟩ : syracuseStep 4374175 = 6561263) B6561263
theorem B5832233 : Blo 2303435 5832233 := bstep (se 2 (by rfl) ⟨2187087, by rfl⟩ : syracuseStep 5832233 = 4374175) B4374175
theorem B3888155 : Blo 2303435 3888155 := bstep (se 1 (by rfl) ⟨2916116, by rfl⟩ : syracuseStep 3888155 = 5832233) B5832233
theorem B2592103 : Blo 2303435 2592103 := bstep (se 1 (by rfl) ⟨1944077, by rfl⟩ : syracuseStep 2592103 = 3888155) B3888155
theorem B3456137 : Blo 2303435 3456137 := bstep (se 2 (by rfl) ⟨1296051, by rfl⟩ : syracuseStep 3456137 = 2592103) B2592103
theorem B2304091 : Blo 2303435 2304091 := bstep (se 1 (by rfl) ⟨1728068, by rfl⟩ : syracuseStep 2304091 = 3456137) B3456137
theorem B11664485 : Blo 2303435 11664485 := bbase (se 4 (by rfl) ⟨1093545, by rfl⟩ : syracuseStep 11664485 = 2187091) (by norm_num)
theorem B7776323 : Blo 2303435 7776323 := bstep (se 1 (by rfl) ⟨5832242, by rfl⟩ : syracuseStep 7776323 = 11664485) B11664485
theorem B5184215 : Blo 2303435 5184215 := bstep (se 1 (by rfl) ⟨3888161, by rfl⟩ : syracuseStep 5184215 = 7776323) B7776323
theorem B3456143 : Blo 2303435 3456143 := bstep (se 1 (by rfl) ⟨2592107, by rfl⟩ : syracuseStep 3456143 = 5184215) B5184215
theorem B2304095 : Blo 2303435 2304095 := bstep (se 1 (by rfl) ⟨1728071, by rfl⟩ : syracuseStep 2304095 = 3456143) B3456143
theorem B3456149 : Blo 2303435 3456149 := bbase (se 6 (by rfl) ⟨81003, by rfl⟩ : syracuseStep 3456149 = 162007) (by norm_num)
theorem B2304099 : Blo 2303435 2304099 := bstep (se 1 (by rfl) ⟨1728074, by rfl⟩ : syracuseStep 2304099 = 3456149) B3456149
theorem B9976229 : Blo 2303435 9976229 := bbase (se 4 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 9976229 = 1870543) (by norm_num)
theorem B6650819 : Blo 2303435 6650819 := bstep (se 1 (by rfl) ⟨4988114, by rfl⟩ : syracuseStep 6650819 = 9976229) B9976229
theorem B4433879 : Blo 2303435 4433879 := bstep (se 1 (by rfl) ⟨3325409, by rfl⟩ : syracuseStep 4433879 = 6650819) B6650819
theorem B2955919 : Blo 2303435 2955919 := bstep (se 1 (by rfl) ⟨2216939, by rfl⟩ : syracuseStep 2955919 = 4433879) B4433879
theorem B3941225 : Blo 2303435 3941225 := bstep (se 2 (by rfl) ⟨1477959, by rfl⟩ : syracuseStep 3941225 = 2955919) B2955919
theorem B2627483 : Blo 2303435 2627483 := bstep (se 1 (by rfl) ⟨1970612, by rfl⟩ : syracuseStep 2627483 = 3941225) B3941225
theorem B7006621 : Blo 2303435 7006621 := bstep (se 3 (by rfl) ⟨1313741, by rfl⟩ : syracuseStep 7006621 = 2627483) B2627483
theorem B9342161 : Blo 2303435 9342161 := bstep (se 2 (by rfl) ⟨3503310, by rfl⟩ : syracuseStep 9342161 = 7006621) B7006621
theorem B6228107 : Blo 2303435 6228107 := bstep (se 1 (by rfl) ⟨4671080, by rfl⟩ : syracuseStep 6228107 = 9342161) B9342161
theorem B4152071 : Blo 2303435 4152071 := bstep (se 1 (by rfl) ⟨3114053, by rfl⟩ : syracuseStep 4152071 = 6228107) B6228107
theorem B11072189 : Blo 2303435 11072189 := bstep (se 3 (by rfl) ⟨2076035, by rfl⟩ : syracuseStep 11072189 = 4152071) B4152071
theorem B7381459 : Blo 2303435 7381459 := bstep (se 1 (by rfl) ⟨5536094, by rfl⟩ : syracuseStep 7381459 = 11072189) B11072189
theorem B9841945 : Blo 2303435 9841945 := bstep (se 2 (by rfl) ⟨3690729, by rfl⟩ : syracuseStep 9841945 = 7381459) B7381459
theorem B13122593 : Blo 2303435 13122593 := bstep (se 2 (by rfl) ⟨4920972, by rfl⟩ : syracuseStep 13122593 = 9841945) B9841945
theorem B8748395 : Blo 2303435 8748395 := bstep (se 1 (by rfl) ⟨6561296, by rfl⟩ : syracuseStep 8748395 = 13122593) B13122593
theorem B5832263 : Blo 2303435 5832263 := bstep (se 1 (by rfl) ⟨4374197, by rfl⟩ : syracuseStep 5832263 = 8748395) B8748395
theorem B3888175 : Blo 2303435 3888175 := bstep (se 1 (by rfl) ⟨2916131, by rfl⟩ : syracuseStep 3888175 = 5832263) B5832263
theorem B5184233 : Blo 2303435 5184233 := bstep (se 2 (by rfl) ⟨1944087, by rfl⟩ : syracuseStep 5184233 = 3888175) B3888175
theorem B3456155 : Blo 2303435 3456155 := bstep (se 1 (by rfl) ⟨2592116, by rfl⟩ : syracuseStep 3456155 = 5184233) B5184233
theorem B2304103 : Blo 2303435 2304103 := bstep (se 1 (by rfl) ⟨1728077, by rfl⟩ : syracuseStep 2304103 = 3456155) B3456155
theorem B2592121 : Blo 2303435 2592121 := bbase (se 2 (by rfl) ⟨972045, by rfl⟩ : syracuseStep 2592121 = 1944091) (by norm_num)
theorem B3456161 : Blo 2303435 3456161 := bstep (se 2 (by rfl) ⟨1296060, by rfl⟩ : syracuseStep 3456161 = 2592121) B2592121
theorem B2304107 : Blo 2303435 2304107 := bstep (se 1 (by rfl) ⟨1728080, by rfl⟩ : syracuseStep 2304107 = 3456161) B3456161
theorem B16608341 : Blo 2303435 16608341 := bbase (se 8 (by rfl) ⟨97314, by rfl⟩ : syracuseStep 16608341 = 194629) (by norm_num)
theorem B11072227 : Blo 2303435 11072227 := bstep (se 1 (by rfl) ⟨8304170, by rfl⟩ : syracuseStep 11072227 = 16608341) B16608341
theorem B14762969 : Blo 2303435 14762969 := bstep (se 2 (by rfl) ⟨5536113, by rfl⟩ : syracuseStep 14762969 = 11072227) B11072227
theorem B9841979 : Blo 2303435 9841979 := bstep (se 1 (by rfl) ⟨7381484, by rfl⟩ : syracuseStep 9841979 = 14762969) B14762969
theorem B6561319 : Blo 2303435 6561319 := bstep (se 1 (by rfl) ⟨4920989, by rfl⟩ : syracuseStep 6561319 = 9841979) B9841979
theorem B8748425 : Blo 2303435 8748425 := bstep (se 2 (by rfl) ⟨3280659, by rfl⟩ : syracuseStep 8748425 = 6561319) B6561319
theorem B5832283 : Blo 2303435 5832283 := bstep (se 1 (by rfl) ⟨4374212, by rfl⟩ : syracuseStep 5832283 = 8748425) B8748425
theorem B7776377 : Blo 2303435 7776377 := bstep (se 2 (by rfl) ⟨2916141, by rfl⟩ : syracuseStep 7776377 = 5832283) B5832283
theorem B5184251 : Blo 2303435 5184251 := bstep (se 1 (by rfl) ⟨3888188, by rfl⟩ : syracuseStep 5184251 = 7776377) B7776377
theorem B3456167 : Blo 2303435 3456167 := bstep (se 1 (by rfl) ⟨2592125, by rfl⟩ : syracuseStep 3456167 = 5184251) B5184251
theorem B2304111 : Blo 2303435 2304111 := bstep (se 1 (by rfl) ⟨1728083, by rfl⟩ : syracuseStep 2304111 = 3456167) B3456167
theorem B3456173 : Blo 2303435 3456173 := bbase (se 3 (by rfl) ⟨648032, by rfl⟩ : syracuseStep 3456173 = 1296065) (by norm_num)
theorem B2304115 : Blo 2303435 2304115 := bstep (se 1 (by rfl) ⟨1728086, by rfl⟩ : syracuseStep 2304115 = 3456173) B3456173
theorem B5184269 : Blo 2303435 5184269 := bbase (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) (by norm_num)
theorem B3456179 : Blo 2303435 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B2304119 : Blo 2303435 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B2916157 : Blo 2303435 2916157 := bbase (se 3 (by rfl) ⟨546779, by rfl⟩ : syracuseStep 2916157 = 1093559) (by norm_num)
theorem B3888209 : Blo 2303435 3888209 := bstep (se 2 (by rfl) ⟨1458078, by rfl⟩ : syracuseStep 3888209 = 2916157) B2916157
theorem B2592139 : Blo 2303435 2592139 := bstep (se 1 (by rfl) ⟨1944104, by rfl⟩ : syracuseStep 2592139 = 3888209) B3888209
theorem B3456185 : Blo 2303435 3456185 := bstep (se 2 (by rfl) ⟨1296069, by rfl⟩ : syracuseStep 3456185 = 2592139) B2592139
theorem B2304123 : Blo 2303435 2304123 := bstep (se 1 (by rfl) ⟨1728092, by rfl⟩ : syracuseStep 2304123 = 3456185) B3456185
theorem B6650885 : Blo 2303435 6650885 := bbase (se 4 (by rfl) ⟨623520, by rfl⟩ : syracuseStep 6650885 = 1247041) (by norm_num)
theorem B4433923 : Blo 2303435 4433923 := bstep (se 1 (by rfl) ⟨3325442, by rfl⟩ : syracuseStep 4433923 = 6650885) B6650885
theorem B5911897 : Blo 2303435 5911897 := bstep (se 2 (by rfl) ⟨2216961, by rfl⟩ : syracuseStep 5911897 = 4433923) B4433923
theorem B7882529 : Blo 2303435 7882529 := bstep (se 2 (by rfl) ⟨2955948, by rfl⟩ : syracuseStep 7882529 = 5911897) B5911897
theorem B21020077 : Blo 2303435 21020077 := bstep (se 3 (by rfl) ⟨3941264, by rfl⟩ : syracuseStep 21020077 = 7882529) B7882529
theorem B28026769 : Blo 2303435 28026769 := bstep (se 2 (by rfl) ⟨10510038, by rfl⟩ : syracuseStep 28026769 = 21020077) B21020077
theorem B37369025 : Blo 2303435 37369025 := bstep (se 2 (by rfl) ⟨14013384, by rfl⟩ : syracuseStep 37369025 = 28026769) B28026769
theorem B24912683 : Blo 2303435 24912683 := bstep (se 1 (by rfl) ⟨18684512, by rfl⟩ : syracuseStep 24912683 = 37369025) B37369025
theorem B16608455 : Blo 2303435 16608455 := bstep (se 1 (by rfl) ⟨12456341, by rfl⟩ : syracuseStep 16608455 = 24912683) B24912683
theorem B11072303 : Blo 2303435 11072303 := bstep (se 1 (by rfl) ⟨8304227, by rfl⟩ : syracuseStep 11072303 = 16608455) B16608455
theorem B7381535 : Blo 2303435 7381535 := bstep (se 1 (by rfl) ⟨5536151, by rfl⟩ : syracuseStep 7381535 = 11072303) B11072303
theorem B19684093 : Blo 2303435 19684093 := bstep (se 3 (by rfl) ⟨3690767, by rfl⟩ : syracuseStep 19684093 = 7381535) B7381535
theorem B26245457 : Blo 2303435 26245457 := bstep (se 2 (by rfl) ⟨9842046, by rfl⟩ : syracuseStep 26245457 = 19684093) B19684093
theorem B17496971 : Blo 2303435 17496971 := bstep (se 1 (by rfl) ⟨13122728, by rfl⟩ : syracuseStep 17496971 = 26245457) B26245457
theorem B11664647 : Blo 2303435 11664647 := bstep (se 1 (by rfl) ⟨8748485, by rfl⟩ : syracuseStep 11664647 = 17496971) B17496971
theorem B7776431 : Blo 2303435 7776431 := bstep (se 1 (by rfl) ⟨5832323, by rfl⟩ : syracuseStep 7776431 = 11664647) B11664647
theorem B5184287 : Blo 2303435 5184287 := bstep (se 1 (by rfl) ⟨3888215, by rfl⟩ : syracuseStep 5184287 = 7776431) B7776431
theorem B3456191 : Blo 2303435 3456191 := bstep (se 1 (by rfl) ⟨2592143, by rfl⟩ : syracuseStep 3456191 = 5184287) B5184287
theorem B2304127 : Blo 2303435 2304127 := bstep (se 1 (by rfl) ⟨1728095, by rfl⟩ : syracuseStep 2304127 = 3456191) B3456191
theorem B3456197 : Blo 2303435 3456197 := bbase (se 4 (by rfl) ⟨324018, by rfl⟩ : syracuseStep 3456197 = 648037) (by norm_num)
theorem B2304131 : Blo 2303435 2304131 := bstep (se 1 (by rfl) ⟨1728098, by rfl⟩ : syracuseStep 2304131 = 3456197) B3456197
theorem B3888229 : Blo 2303435 3888229 := bbase (se 4 (by rfl) ⟨364521, by rfl⟩ : syracuseStep 3888229 = 729043) (by norm_num)
theorem B5184305 : Blo 2303435 5184305 := bstep (se 2 (by rfl) ⟨1944114, by rfl⟩ : syracuseStep 5184305 = 3888229) B3888229
theorem B3456203 : Blo 2303435 3456203 := bstep (se 1 (by rfl) ⟨2592152, by rfl⟩ : syracuseStep 3456203 = 5184305) B5184305
theorem B2304135 : Blo 2303435 2304135 := bstep (se 1 (by rfl) ⟨1728101, by rfl⟩ : syracuseStep 2304135 = 3456203) B3456203
theorem B2592157 : Blo 2303435 2592157 := bbase (se 3 (by rfl) ⟨486029, by rfl⟩ : syracuseStep 2592157 = 972059) (by norm_num)
theorem B3456209 : Blo 2303435 3456209 := bstep (se 2 (by rfl) ⟨1296078, by rfl⟩ : syracuseStep 3456209 = 2592157) B2592157
theorem B2304139 : Blo 2303435 2304139 := bstep (se 1 (by rfl) ⟨1728104, by rfl⟩ : syracuseStep 2304139 = 3456209) B3456209
theorem B7776485 : Blo 2303435 7776485 := bbase (se 4 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 7776485 = 1458091) (by norm_num)
theorem B5184323 : Blo 2303435 5184323 := bstep (se 1 (by rfl) ⟨3888242, by rfl⟩ : syracuseStep 5184323 = 7776485) B7776485
theorem B3456215 : Blo 2303435 3456215 := bstep (se 1 (by rfl) ⟨2592161, by rfl⟩ : syracuseStep 3456215 = 5184323) B5184323
theorem B2304143 : Blo 2303435 2304143 := bstep (se 1 (by rfl) ⟨1728107, by rfl⟩ : syracuseStep 2304143 = 3456215) B3456215
theorem B3456221 : Blo 2303435 3456221 := bbase (se 3 (by rfl) ⟨648041, by rfl⟩ : syracuseStep 3456221 = 1296083) (by norm_num)
theorem B2304147 : Blo 2303435 2304147 := bstep (se 1 (by rfl) ⟨1728110, by rfl⟩ : syracuseStep 2304147 = 3456221) B3456221
theorem B5184341 : Blo 2303435 5184341 := bbase (se 9 (by rfl) ⟨15188, by rfl⟩ : syracuseStep 5184341 = 30377) (by norm_num)
theorem B3456227 : Blo 2303435 3456227 := bstep (se 1 (by rfl) ⟨2592170, by rfl⟩ : syracuseStep 3456227 = 5184341) B5184341
theorem B2304151 : Blo 2303435 2304151 := bstep (se 1 (by rfl) ⟨1728113, by rfl⟩ : syracuseStep 2304151 = 3456227) B3456227
theorem B6561445 : Blo 2303435 6561445 := bbase (se 4 (by rfl) ⟨615135, by rfl⟩ : syracuseStep 6561445 = 1230271) (by norm_num)
theorem B8748593 : Blo 2303435 8748593 := bstep (se 2 (by rfl) ⟨3280722, by rfl⟩ : syracuseStep 8748593 = 6561445) B6561445
theorem B5832395 : Blo 2303435 5832395 := bstep (se 1 (by rfl) ⟨4374296, by rfl⟩ : syracuseStep 5832395 = 8748593) B8748593
theorem B3888263 : Blo 2303435 3888263 := bstep (se 1 (by rfl) ⟨2916197, by rfl⟩ : syracuseStep 3888263 = 5832395) B5832395
theorem B2592175 : Blo 2303435 2592175 := bstep (se 1 (by rfl) ⟨1944131, by rfl⟩ : syracuseStep 2592175 = 3888263) B3888263
theorem B3456233 : Blo 2303435 3456233 := bstep (se 2 (by rfl) ⟨1296087, by rfl⟩ : syracuseStep 3456233 = 2592175) B2592175
theorem B2304155 : Blo 2303435 2304155 := bstep (se 1 (by rfl) ⟨1728116, by rfl⟩ : syracuseStep 2304155 = 3456233) B3456233
theorem B5255093 : Blo 2303435 5255093 := bbase (se 5 (by rfl) ⟨246332, by rfl⟩ : syracuseStep 5255093 = 492665) (by norm_num)
theorem B3503395 : Blo 2303435 3503395 := bstep (se 1 (by rfl) ⟨2627546, by rfl⟩ : syracuseStep 3503395 = 5255093) B5255093
theorem B4671193 : Blo 2303435 4671193 := bstep (se 2 (by rfl) ⟨1751697, by rfl⟩ : syracuseStep 4671193 = 3503395) B3503395
theorem B6228257 : Blo 2303435 6228257 := bstep (se 2 (by rfl) ⟨2335596, by rfl⟩ : syracuseStep 6228257 = 4671193) B4671193
theorem B66434741 : Blo 2303435 66434741 := bstep (se 5 (by rfl) ⟨3114128, by rfl⟩ : syracuseStep 66434741 = 6228257) B6228257
theorem B44289827 : Blo 2303435 44289827 := bstep (se 1 (by rfl) ⟨33217370, by rfl⟩ : syracuseStep 44289827 = 66434741) B66434741
theorem B29526551 : Blo 2303435 29526551 := bstep (se 1 (by rfl) ⟨22144913, by rfl⟩ : syracuseStep 29526551 = 44289827) B44289827
theorem B19684367 : Blo 2303435 19684367 := bstep (se 1 (by rfl) ⟨14763275, by rfl⟩ : syracuseStep 19684367 = 29526551) B29526551
theorem B13122911 : Blo 2303435 13122911 := bstep (se 1 (by rfl) ⟨9842183, by rfl⟩ : syracuseStep 13122911 = 19684367) B19684367
theorem B8748607 : Blo 2303435 8748607 := bstep (se 1 (by rfl) ⟨6561455, by rfl⟩ : syracuseStep 8748607 = 13122911) B13122911
theorem B11664809 : Blo 2303435 11664809 := bstep (se 2 (by rfl) ⟨4374303, by rfl⟩ : syracuseStep 11664809 = 8748607) B8748607
theorem B7776539 : Blo 2303435 7776539 := bstep (se 1 (by rfl) ⟨5832404, by rfl⟩ : syracuseStep 7776539 = 11664809) B11664809
theorem B5184359 : Blo 2303435 5184359 := bstep (se 1 (by rfl) ⟨3888269, by rfl⟩ : syracuseStep 5184359 = 7776539) B7776539
theorem B3456239 : Blo 2303435 3456239 := bstep (se 1 (by rfl) ⟨2592179, by rfl⟩ : syracuseStep 3456239 = 5184359) B5184359
theorem B2304159 : Blo 2303435 2304159 := bstep (se 1 (by rfl) ⟨1728119, by rfl⟩ : syracuseStep 2304159 = 3456239) B3456239
theorem B3456245 : Blo 2303435 3456245 := bbase (se 5 (by rfl) ⟨162011, by rfl⟩ : syracuseStep 3456245 = 324023) (by norm_num)
theorem B2304163 : Blo 2303435 2304163 := bstep (se 1 (by rfl) ⟨1728122, by rfl⟩ : syracuseStep 2304163 = 3456245) B3456245
theorem B8304373 : Blo 2303435 8304373 := bbase (se 5 (by rfl) ⟨389267, by rfl⟩ : syracuseStep 8304373 = 778535) (by norm_num)
theorem B11072497 : Blo 2303435 11072497 := bstep (se 2 (by rfl) ⟨4152186, by rfl⟩ : syracuseStep 11072497 = 8304373) B8304373
theorem B14763329 : Blo 2303435 14763329 := bstep (se 2 (by rfl) ⟨5536248, by rfl⟩ : syracuseStep 14763329 = 11072497) B11072497
theorem B9842219 : Blo 2303435 9842219 := bstep (se 1 (by rfl) ⟨7381664, by rfl⟩ : syracuseStep 9842219 = 14763329) B14763329
theorem B6561479 : Blo 2303435 6561479 := bstep (se 1 (by rfl) ⟨4921109, by rfl⟩ : syracuseStep 6561479 = 9842219) B9842219
theorem B4374319 : Blo 2303435 4374319 := bstep (se 1 (by rfl) ⟨3280739, by rfl⟩ : syracuseStep 4374319 = 6561479) B6561479
theorem B5832425 : Blo 2303435 5832425 := bstep (se 2 (by rfl) ⟨2187159, by rfl⟩ : syracuseStep 5832425 = 4374319) B4374319
theorem B3888283 : Blo 2303435 3888283 := bstep (se 1 (by rfl) ⟨2916212, by rfl⟩ : syracuseStep 3888283 = 5832425) B5832425
theorem B5184377 : Blo 2303435 5184377 := bstep (se 2 (by rfl) ⟨1944141, by rfl⟩ : syracuseStep 5184377 = 3888283) B3888283
theorem B3456251 : Blo 2303435 3456251 := bstep (se 1 (by rfl) ⟨2592188, by rfl⟩ : syracuseStep 3456251 = 5184377) B5184377
theorem B2304167 : Blo 2303435 2304167 := bstep (se 1 (by rfl) ⟨1728125, by rfl⟩ : syracuseStep 2304167 = 3456251) B3456251
theorem B2592193 : Blo 2303435 2592193 := bbase (se 2 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 2592193 = 1944145) (by norm_num)
theorem B3456257 : Blo 2303435 3456257 := bstep (se 2 (by rfl) ⟨1296096, by rfl⟩ : syracuseStep 3456257 = 2592193) B2592193
theorem B2304171 : Blo 2303435 2304171 := bstep (se 1 (by rfl) ⟨1728128, by rfl⟩ : syracuseStep 2304171 = 3456257) B3456257
theorem B5832445 : Blo 2303435 5832445 := bbase (se 3 (by rfl) ⟨1093583, by rfl⟩ : syracuseStep 5832445 = 2187167) (by norm_num)
theorem B7776593 : Blo 2303435 7776593 := bstep (se 2 (by rfl) ⟨2916222, by rfl⟩ : syracuseStep 7776593 = 5832445) B5832445
theorem B5184395 : Blo 2303435 5184395 := bstep (se 1 (by rfl) ⟨3888296, by rfl⟩ : syracuseStep 5184395 = 7776593) B7776593
theorem B3456263 : Blo 2303435 3456263 := bstep (se 1 (by rfl) ⟨2592197, by rfl⟩ : syracuseStep 3456263 = 5184395) B5184395
theorem B2304175 : Blo 2303435 2304175 := bstep (se 1 (by rfl) ⟨1728131, by rfl⟩ : syracuseStep 2304175 = 3456263) B3456263
theorem B3456269 : Blo 2303435 3456269 := bbase (se 3 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 3456269 = 1296101) (by norm_num)
theorem B2304179 : Blo 2303435 2304179 := bstep (se 1 (by rfl) ⟨1728134, by rfl⟩ : syracuseStep 2304179 = 3456269) B3456269
theorem B5184413 : Blo 2303435 5184413 := bbase (se 3 (by rfl) ⟨972077, by rfl⟩ : syracuseStep 5184413 = 1944155) (by norm_num)
theorem B3456275 : Blo 2303435 3456275 := bstep (se 1 (by rfl) ⟨2592206, by rfl⟩ : syracuseStep 3456275 = 5184413) B5184413
theorem B2304183 : Blo 2303435 2304183 := bstep (se 1 (by rfl) ⟨1728137, by rfl⟩ : syracuseStep 2304183 = 3456275) B3456275
theorem B3888317 : Blo 2303435 3888317 := bbase (se 3 (by rfl) ⟨729059, by rfl⟩ : syracuseStep 3888317 = 1458119) (by norm_num)
theorem B2592211 : Blo 2303435 2592211 := bstep (se 1 (by rfl) ⟨1944158, by rfl⟩ : syracuseStep 2592211 = 3888317) B3888317
theorem B3456281 : Blo 2303435 3456281 := bstep (se 2 (by rfl) ⟨1296105, by rfl⟩ : syracuseStep 3456281 = 2592211) B2592211
theorem B2304187 : Blo 2303435 2304187 := bstep (se 1 (by rfl) ⟨1728140, by rfl⟩ : syracuseStep 2304187 = 3456281) B3456281
theorem B13123093 : Blo 2303435 13123093 := bbase (se 6 (by rfl) ⟨307572, by rfl⟩ : syracuseStep 13123093 = 615145) (by norm_num)
theorem B17497457 : Blo 2303435 17497457 := bstep (se 2 (by rfl) ⟨6561546, by rfl⟩ : syracuseStep 17497457 = 13123093) B13123093
theorem B11664971 : Blo 2303435 11664971 := bstep (se 1 (by rfl) ⟨8748728, by rfl⟩ : syracuseStep 11664971 = 17497457) B17497457
theorem B7776647 : Blo 2303435 7776647 := bstep (se 1 (by rfl) ⟨5832485, by rfl⟩ : syracuseStep 7776647 = 11664971) B11664971
theorem B5184431 : Blo 2303435 5184431 := bstep (se 1 (by rfl) ⟨3888323, by rfl⟩ : syracuseStep 5184431 = 7776647) B7776647
theorem B3456287 : Blo 2303435 3456287 := bstep (se 1 (by rfl) ⟨2592215, by rfl⟩ : syracuseStep 3456287 = 5184431) B5184431
theorem B2304191 : Blo 2303435 2304191 := bstep (se 1 (by rfl) ⟨1728143, by rfl⟩ : syracuseStep 2304191 = 3456287) B3456287
theorem B3456293 : Blo 2303435 3456293 := bbase (se 4 (by rfl) ⟨324027, by rfl⟩ : syracuseStep 3456293 = 648055) (by norm_num)
theorem B2304195 : Blo 2303435 2304195 := bstep (se 1 (by rfl) ⟨1728146, by rfl⟩ : syracuseStep 2304195 = 3456293) B3456293
theorem B2916253 : Blo 2303435 2916253 := bbase (se 3 (by rfl) ⟨546797, by rfl⟩ : syracuseStep 2916253 = 1093595) (by norm_num)
theorem B3888337 : Blo 2303435 3888337 := bstep (se 2 (by rfl) ⟨1458126, by rfl⟩ : syracuseStep 3888337 = 2916253) B2916253
theorem B5184449 : Blo 2303435 5184449 := bstep (se 2 (by rfl) ⟨1944168, by rfl⟩ : syracuseStep 5184449 = 3888337) B3888337
theorem B3456299 : Blo 2303435 3456299 := bstep (se 1 (by rfl) ⟨2592224, by rfl⟩ : syracuseStep 3456299 = 5184449) B5184449
theorem B2304199 : Blo 2303435 2304199 := bstep (se 1 (by rfl) ⟨1728149, by rfl⟩ : syracuseStep 2304199 = 3456299) B3456299
theorem B2592229 : Blo 2303435 2592229 := bbase (se 4 (by rfl) ⟨243021, by rfl⟩ : syracuseStep 2592229 = 486043) (by norm_num)
theorem B3456305 : Blo 2303435 3456305 := bstep (se 2 (by rfl) ⟨1296114, by rfl⟩ : syracuseStep 3456305 = 2592229) B2592229
theorem B2304203 : Blo 2303435 2304203 := bstep (se 1 (by rfl) ⟨1728152, by rfl⟩ : syracuseStep 2304203 = 3456305) B3456305
theorem B6228389 : Blo 2303435 6228389 := bbase (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) (by norm_num)
theorem B4152259 : Blo 2303435 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B5536345 : Blo 2303435 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B7381793 : Blo 2303435 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B4921195 : Blo 2303435 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B6561593 : Blo 2303435 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B4374395 : Blo 2303435 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B2916263 : Blo 2303435 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B7776701 : Blo 2303435 7776701 := bstep (se 3 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 7776701 = 2916263) B2916263
theorem B5184467 : Blo 2303435 5184467 := bstep (se 1 (by rfl) ⟨3888350, by rfl⟩ : syracuseStep 5184467 = 7776701) B7776701
theorem B3456311 : Blo 2303435 3456311 := bstep (se 1 (by rfl) ⟨2592233, by rfl⟩ : syracuseStep 3456311 = 5184467) B5184467
theorem B2304207 : Blo 2303435 2304207 := bstep (se 1 (by rfl) ⟨1728155, by rfl⟩ : syracuseStep 2304207 = 3456311) B3456311
theorem B3456317 : Blo 2303435 3456317 := bbase (se 3 (by rfl) ⟨648059, by rfl⟩ : syracuseStep 3456317 = 1296119) (by norm_num)
theorem B2304211 : Blo 2303435 2304211 := bstep (se 1 (by rfl) ⟨1728158, by rfl⟩ : syracuseStep 2304211 = 3456317) B3456317
theorem B5184485 : Blo 2303435 5184485 := bbase (se 4 (by rfl) ⟨486045, by rfl⟩ : syracuseStep 5184485 = 972091) (by norm_num)
theorem B3456323 : Blo 2303435 3456323 := bstep (se 1 (by rfl) ⟨2592242, by rfl⟩ : syracuseStep 3456323 = 5184485) B5184485
theorem B2304215 : Blo 2303435 2304215 := bstep (se 1 (by rfl) ⟨1728161, by rfl⟩ : syracuseStep 2304215 = 3456323) B3456323
theorem B5832557 : Blo 2303435 5832557 := bbase (se 3 (by rfl) ⟨1093604, by rfl⟩ : syracuseStep 5832557 = 2187209) (by norm_num)
theorem B3888371 : Blo 2303435 3888371 := bstep (se 1 (by rfl) ⟨2916278, by rfl⟩ : syracuseStep 3888371 = 5832557) B5832557
theorem B2592247 : Blo 2303435 2592247 := bstep (se 1 (by rfl) ⟨1944185, by rfl⟩ : syracuseStep 2592247 = 3888371) B3888371
theorem B3456329 : Blo 2303435 3456329 := bstep (se 2 (by rfl) ⟨1296123, by rfl⟩ : syracuseStep 3456329 = 2592247) B2592247
theorem B2304219 : Blo 2303435 2304219 := bstep (se 1 (by rfl) ⟨1728164, by rfl⟩ : syracuseStep 2304219 = 3456329) B3456329
theorem B4921229 : Blo 2303435 4921229 := bbase (se 3 (by rfl) ⟨922730, by rfl⟩ : syracuseStep 4921229 = 1845461) (by norm_num)
theorem B3280819 : Blo 2303435 3280819 := bstep (se 1 (by rfl) ⟨2460614, by rfl⟩ : syracuseStep 3280819 = 4921229) B4921229
theorem B4374425 : Blo 2303435 4374425 := bstep (se 2 (by rfl) ⟨1640409, by rfl⟩ : syracuseStep 4374425 = 3280819) B3280819
theorem B11665133 : Blo 2303435 11665133 := bstep (se 3 (by rfl) ⟨2187212, by rfl⟩ : syracuseStep 11665133 = 4374425) B4374425
theorem B7776755 : Blo 2303435 7776755 := bstep (se 1 (by rfl) ⟨5832566, by rfl⟩ : syracuseStep 7776755 = 11665133) B11665133
theorem B5184503 : Blo 2303435 5184503 := bstep (se 1 (by rfl) ⟨3888377, by rfl⟩ : syracuseStep 5184503 = 7776755) B7776755
theorem B3456335 : Blo 2303435 3456335 := bstep (se 1 (by rfl) ⟨2592251, by rfl⟩ : syracuseStep 3456335 = 5184503) B5184503
theorem B2304223 : Blo 2303435 2304223 := bstep (se 1 (by rfl) ⟨1728167, by rfl⟩ : syracuseStep 2304223 = 3456335) B3456335
theorem B3456341 : Blo 2303435 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B2304227 : Blo 2303435 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B4671341 : Blo 2303435 4671341 := bbase (se 3 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 4671341 = 1751753) (by norm_num)
theorem B3114227 : Blo 2303435 3114227 := bstep (se 1 (by rfl) ⟨2335670, by rfl⟩ : syracuseStep 3114227 = 4671341) B4671341
theorem B8304605 : Blo 2303435 8304605 := bstep (se 3 (by rfl) ⟨1557113, by rfl⟩ : syracuseStep 8304605 = 3114227) B3114227
theorem B5536403 : Blo 2303435 5536403 := bstep (se 1 (by rfl) ⟨4152302, by rfl⟩ : syracuseStep 5536403 = 8304605) B8304605
theorem B3690935 : Blo 2303435 3690935 := bstep (se 1 (by rfl) ⟨2768201, by rfl⟩ : syracuseStep 3690935 = 5536403) B5536403
theorem B2460623 : Blo 2303435 2460623 := bstep (se 1 (by rfl) ⟨1845467, by rfl⟩ : syracuseStep 2460623 = 3690935) B3690935
theorem B6561661 : Blo 2303435 6561661 := bstep (se 3 (by rfl) ⟨1230311, by rfl⟩ : syracuseStep 6561661 = 2460623) B2460623
theorem B8748881 : Blo 2303435 8748881 := bstep (se 2 (by rfl) ⟨3280830, by rfl⟩ : syracuseStep 8748881 = 6561661) B6561661
theorem B5832587 : Blo 2303435 5832587 := bstep (se 1 (by rfl) ⟨4374440, by rfl⟩ : syracuseStep 5832587 = 8748881) B8748881
theorem B3888391 : Blo 2303435 3888391 := bstep (se 1 (by rfl) ⟨2916293, by rfl⟩ : syracuseStep 3888391 = 5832587) B5832587
theorem B5184521 : Blo 2303435 5184521 := bstep (se 2 (by rfl) ⟨1944195, by rfl⟩ : syracuseStep 5184521 = 3888391) B3888391
theorem B3456347 : Blo 2303435 3456347 := bstep (se 1 (by rfl) ⟨2592260, by rfl⟩ : syracuseStep 3456347 = 5184521) B5184521
theorem B2304231 : Blo 2303435 2304231 := bstep (se 1 (by rfl) ⟨1728173, by rfl⟩ : syracuseStep 2304231 = 3456347) B3456347
theorem B2592265 : Blo 2303435 2592265 := bbase (se 2 (by rfl) ⟨972099, by rfl⟩ : syracuseStep 2592265 = 1944199) (by norm_num)
theorem B3456353 : Blo 2303435 3456353 := bstep (se 2 (by rfl) ⟨1296132, by rfl⟩ : syracuseStep 3456353 = 2592265) B2592265
theorem B2304235 : Blo 2303435 2304235 := bstep (se 1 (by rfl) ⟨1728176, by rfl⟩ : syracuseStep 2304235 = 3456353) B3456353
theorem B2663489 : Blo 2303435 2663489 := bbase (se 2 (by rfl) ⟨998808, by rfl⟩ : syracuseStep 2663489 = 1997617) (by norm_num)
theorem B7102637 : Blo 2303435 7102637 := bstep (se 3 (by rfl) ⟨1331744, by rfl⟩ : syracuseStep 7102637 = 2663489) B2663489
theorem B4735091 : Blo 2303435 4735091 := bstep (se 1 (by rfl) ⟨3551318, by rfl⟩ : syracuseStep 4735091 = 7102637) B7102637
theorem B3156727 : Blo 2303435 3156727 := bstep (se 1 (by rfl) ⟨2367545, by rfl⟩ : syracuseStep 3156727 = 4735091) B4735091
theorem B4208969 : Blo 2303435 4208969 := bstep (se 2 (by rfl) ⟨1578363, by rfl⟩ : syracuseStep 4208969 = 3156727) B3156727
theorem B11223917 : Blo 2303435 11223917 := bstep (se 3 (by rfl) ⟨2104484, by rfl⟩ : syracuseStep 11223917 = 4208969) B4208969
theorem B7482611 : Blo 2303435 7482611 := bstep (se 1 (by rfl) ⟨5611958, by rfl⟩ : syracuseStep 7482611 = 11223917) B11223917
theorem B4988407 : Blo 2303435 4988407 := bstep (se 1 (by rfl) ⟨3741305, by rfl⟩ : syracuseStep 4988407 = 7482611) B7482611
theorem B6651209 : Blo 2303435 6651209 := bstep (se 2 (by rfl) ⟨2494203, by rfl⟩ : syracuseStep 6651209 = 4988407) B4988407
theorem B4434139 : Blo 2303435 4434139 := bstep (se 1 (by rfl) ⟨3325604, by rfl⟩ : syracuseStep 4434139 = 6651209) B6651209
theorem B5912185 : Blo 2303435 5912185 := bstep (se 2 (by rfl) ⟨2217069, by rfl⟩ : syracuseStep 5912185 = 4434139) B4434139
theorem B7882913 : Blo 2303435 7882913 := bstep (se 2 (by rfl) ⟨2956092, by rfl⟩ : syracuseStep 7882913 = 5912185) B5912185
theorem B5255275 : Blo 2303435 5255275 := bstep (se 1 (by rfl) ⟨3941456, by rfl⟩ : syracuseStep 5255275 = 7882913) B7882913
theorem B7007033 : Blo 2303435 7007033 := bstep (se 2 (by rfl) ⟨2627637, by rfl⟩ : syracuseStep 7007033 = 5255275) B5255275
theorem B18685421 : Blo 2303435 18685421 := bstep (se 3 (by rfl) ⟨3503516, by rfl⟩ : syracuseStep 18685421 = 7007033) B7007033
theorem B12456947 : Blo 2303435 12456947 := bstep (se 1 (by rfl) ⟨9342710, by rfl⟩ : syracuseStep 12456947 = 18685421) B18685421
theorem B33218525 : Blo 2303435 33218525 := bstep (se 3 (by rfl) ⟨6228473, by rfl⟩ : syracuseStep 33218525 = 12456947) B12456947
theorem B22145683 : Blo 2303435 22145683 := bstep (se 1 (by rfl) ⟨16609262, by rfl⟩ : syracuseStep 22145683 = 33218525) B33218525
theorem B29527577 : Blo 2303435 29527577 := bstep (se 2 (by rfl) ⟨11072841, by rfl⟩ : syracuseStep 29527577 = 22145683) B22145683
theorem B19685051 : Blo 2303435 19685051 := bstep (se 1 (by rfl) ⟨14763788, by rfl⟩ : syracuseStep 19685051 = 29527577) B29527577
theorem B13123367 : Blo 2303435 13123367 := bstep (se 1 (by rfl) ⟨9842525, by rfl⟩ : syracuseStep 13123367 = 19685051) B19685051
theorem B8748911 : Blo 2303435 8748911 := bstep (se 1 (by rfl) ⟨6561683, by rfl⟩ : syracuseStep 8748911 = 13123367) B13123367
theorem B5832607 : Blo 2303435 5832607 := bstep (se 1 (by rfl) ⟨4374455, by rfl⟩ : syracuseStep 5832607 = 8748911) B8748911
theorem B7776809 : Blo 2303435 7776809 := bstep (se 2 (by rfl) ⟨2916303, by rfl⟩ : syracuseStep 7776809 = 5832607) B5832607
theorem B5184539 : Blo 2303435 5184539 := bstep (se 1 (by rfl) ⟨3888404, by rfl⟩ : syracuseStep 5184539 = 7776809) B7776809
theorem B3456359 : Blo 2303435 3456359 := bstep (se 1 (by rfl) ⟨2592269, by rfl⟩ : syracuseStep 3456359 = 5184539) B5184539
theorem B2304239 : Blo 2303435 2304239 := bstep (se 1 (by rfl) ⟨1728179, by rfl⟩ : syracuseStep 2304239 = 3456359) B3456359
theorem B3456365 : Blo 2303435 3456365 := bbase (se 3 (by rfl) ⟨648068, by rfl⟩ : syracuseStep 3456365 = 1296137) (by norm_num)
theorem B2304243 : Blo 2303435 2304243 := bstep (se 1 (by rfl) ⟨1728182, by rfl⟩ : syracuseStep 2304243 = 3456365) B3456365
theorem B5184557 : Blo 2303435 5184557 := bbase (se 3 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 5184557 = 1944209) (by norm_num)
theorem B3456371 : Blo 2303435 3456371 := bstep (se 1 (by rfl) ⟨2592278, by rfl⟩ : syracuseStep 3456371 = 5184557) B5184557
theorem B2304247 : Blo 2303435 2304247 := bstep (se 1 (by rfl) ⟨1728185, by rfl⟩ : syracuseStep 2304247 = 3456371) B3456371
theorem B8304677 : Blo 2303435 8304677 := bbase (se 4 (by rfl) ⟨778563, by rfl⟩ : syracuseStep 8304677 = 1557127) (by norm_num)
theorem B5536451 : Blo 2303435 5536451 := bstep (se 1 (by rfl) ⟨4152338, by rfl⟩ : syracuseStep 5536451 = 8304677) B8304677
theorem B14763869 : Blo 2303435 14763869 := bstep (se 3 (by rfl) ⟨2768225, by rfl⟩ : syracuseStep 14763869 = 5536451) B5536451
theorem B9842579 : Blo 2303435 9842579 := bstep (se 1 (by rfl) ⟨7381934, by rfl⟩ : syracuseStep 9842579 = 14763869) B14763869
theorem B6561719 : Blo 2303435 6561719 := bstep (se 1 (by rfl) ⟨4921289, by rfl⟩ : syracuseStep 6561719 = 9842579) B9842579
theorem B4374479 : Blo 2303435 4374479 := bstep (se 1 (by rfl) ⟨3280859, by rfl⟩ : syracuseStep 4374479 = 6561719) B6561719
theorem B2916319 : Blo 2303435 2916319 := bstep (se 1 (by rfl) ⟨2187239, by rfl⟩ : syracuseStep 2916319 = 4374479) B4374479
theorem B3888425 : Blo 2303435 3888425 := bstep (se 2 (by rfl) ⟨1458159, by rfl⟩ : syracuseStep 3888425 = 2916319) B2916319
theorem B2592283 : Blo 2303435 2592283 := bstep (se 1 (by rfl) ⟨1944212, by rfl⟩ : syracuseStep 2592283 = 3888425) B3888425
theorem B3456377 : Blo 2303435 3456377 := bstep (se 2 (by rfl) ⟨1296141, by rfl⟩ : syracuseStep 3456377 = 2592283) B2592283
theorem B2304251 : Blo 2303435 2304251 := bstep (se 1 (by rfl) ⟨1728188, by rfl⟩ : syracuseStep 2304251 = 3456377) B3456377
theorem B6228517 : Blo 2303435 6228517 := bbase (se 4 (by rfl) ⟨583923, by rfl⟩ : syracuseStep 6228517 = 1167847) (by norm_num)
theorem B8304689 : Blo 2303435 8304689 := bstep (se 2 (by rfl) ⟨3114258, by rfl⟩ : syracuseStep 8304689 = 6228517) B6228517
theorem B5536459 : Blo 2303435 5536459 := bstep (se 1 (by rfl) ⟨4152344, by rfl⟩ : syracuseStep 5536459 = 8304689) B8304689
theorem B7381945 : Blo 2303435 7381945 := bstep (se 2 (by rfl) ⟨2768229, by rfl⟩ : syracuseStep 7381945 = 5536459) B5536459
theorem B39370373 : Blo 2303435 39370373 := bstep (se 4 (by rfl) ⟨3690972, by rfl⟩ : syracuseStep 39370373 = 7381945) B7381945
theorem B26246915 : Blo 2303435 26246915 := bstep (se 1 (by rfl) ⟨19685186, by rfl⟩ : syracuseStep 26246915 = 39370373) B39370373
theorem B17497943 : Blo 2303435 17497943 := bstep (se 1 (by rfl) ⟨13123457, by rfl⟩ : syracuseStep 17497943 = 26246915) B26246915
theorem B11665295 : Blo 2303435 11665295 := bstep (se 1 (by rfl) ⟨8748971, by rfl⟩ : syracuseStep 11665295 = 17497943) B17497943
theorem B7776863 : Blo 2303435 7776863 := bstep (se 1 (by rfl) ⟨5832647, by rfl⟩ : syracuseStep 7776863 = 11665295) B11665295
theorem B5184575 : Blo 2303435 5184575 := bstep (se 1 (by rfl) ⟨3888431, by rfl⟩ : syracuseStep 5184575 = 7776863) B7776863
theorem B3456383 : Blo 2303435 3456383 := bstep (se 1 (by rfl) ⟨2592287, by rfl⟩ : syracuseStep 3456383 = 5184575) B5184575
theorem B2304255 : Blo 2303435 2304255 := bstep (se 1 (by rfl) ⟨1728191, by rfl⟩ : syracuseStep 2304255 = 3456383) B3456383
theorem B3456389 : Blo 2303435 3456389 := bbase (se 4 (by rfl) ⟨324036, by rfl⟩ : syracuseStep 3456389 = 648073) (by norm_num)
theorem B2304259 : Blo 2303435 2304259 := bstep (se 1 (by rfl) ⟨1728194, by rfl⟩ : syracuseStep 2304259 = 3456389) B3456389
theorem B3888445 : Blo 2303435 3888445 := bbase (se 3 (by rfl) ⟨729083, by rfl⟩ : syracuseStep 3888445 = 1458167) (by norm_num)
theorem B5184593 : Blo 2303435 5184593 := bstep (se 2 (by rfl) ⟨1944222, by rfl⟩ : syracuseStep 5184593 = 3888445) B3888445
theorem B3456395 : Blo 2303435 3456395 := bstep (se 1 (by rfl) ⟨2592296, by rfl⟩ : syracuseStep 3456395 = 5184593) B5184593
theorem B2304263 : Blo 2303435 2304263 := bstep (se 1 (by rfl) ⟨1728197, by rfl⟩ : syracuseStep 2304263 = 3456395) B3456395
theorem B2592301 : Blo 2303435 2592301 := bbase (se 3 (by rfl) ⟨486056, by rfl⟩ : syracuseStep 2592301 = 972113) (by norm_num)
theorem B3456401 : Blo 2303435 3456401 := bstep (se 2 (by rfl) ⟨1296150, by rfl⟩ : syracuseStep 3456401 = 2592301) B2592301
theorem B2304267 : Blo 2303435 2304267 := bstep (se 1 (by rfl) ⟨1728200, by rfl⟩ : syracuseStep 2304267 = 3456401) B3456401
theorem B7776917 : Blo 2303435 7776917 := bbase (se 6 (by rfl) ⟨182271, by rfl⟩ : syracuseStep 7776917 = 364543) (by norm_num)
theorem B5184611 : Blo 2303435 5184611 := bstep (se 1 (by rfl) ⟨3888458, by rfl⟩ : syracuseStep 5184611 = 7776917) B7776917
theorem B3456407 : Blo 2303435 3456407 := bstep (se 1 (by rfl) ⟨2592305, by rfl⟩ : syracuseStep 3456407 = 5184611) B5184611
theorem B2304271 : Blo 2303435 2304271 := bstep (se 1 (by rfl) ⟨1728203, by rfl⟩ : syracuseStep 2304271 = 3456407) B3456407
theorem B3456413 : Blo 2303435 3456413 := bbase (se 3 (by rfl) ⟨648077, by rfl⟩ : syracuseStep 3456413 = 1296155) (by norm_num)
theorem B2304275 : Blo 2303435 2304275 := bstep (se 1 (by rfl) ⟨1728206, by rfl⟩ : syracuseStep 2304275 = 3456413) B3456413
theorem B5184629 : Blo 2303435 5184629 := bbase (se 5 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 5184629 = 486059) (by norm_num)
theorem B3456419 : Blo 2303435 3456419 := bstep (se 1 (by rfl) ⟨2592314, by rfl⟩ : syracuseStep 3456419 = 5184629) B5184629
theorem B2304279 : Blo 2303435 2304279 := bstep (se 1 (by rfl) ⟨1728209, by rfl⟩ : syracuseStep 2304279 = 3456419) B3456419
theorem B19685429 : Blo 2303435 19685429 := bbase (se 5 (by rfl) ⟨922754, by rfl⟩ : syracuseStep 19685429 = 1845509) (by norm_num)
theorem B13123619 : Blo 2303435 13123619 := bstep (se 1 (by rfl) ⟨9842714, by rfl⟩ : syracuseStep 13123619 = 19685429) B19685429
theorem B8749079 : Blo 2303435 8749079 := bstep (se 1 (by rfl) ⟨6561809, by rfl⟩ : syracuseStep 8749079 = 13123619) B13123619
theorem B5832719 : Blo 2303435 5832719 := bstep (se 1 (by rfl) ⟨4374539, by rfl⟩ : syracuseStep 5832719 = 8749079) B8749079
theorem B3888479 : Blo 2303435 3888479 := bstep (se 1 (by rfl) ⟨2916359, by rfl⟩ : syracuseStep 3888479 = 5832719) B5832719
theorem B2592319 : Blo 2303435 2592319 := bstep (se 1 (by rfl) ⟨1944239, by rfl⟩ : syracuseStep 2592319 = 3888479) B3888479
theorem B3456425 : Blo 2303435 3456425 := bstep (se 2 (by rfl) ⟨1296159, by rfl⟩ : syracuseStep 3456425 = 2592319) B2592319
theorem B2304283 : Blo 2303435 2304283 := bstep (se 1 (by rfl) ⟨1728212, by rfl⟩ : syracuseStep 2304283 = 3456425) B3456425
theorem B8749093 : Blo 2303435 8749093 := bbase (se 4 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 8749093 = 1640455) (by norm_num)
theorem B11665457 : Blo 2303435 11665457 := bstep (se 2 (by rfl) ⟨4374546, by rfl⟩ : syracuseStep 11665457 = 8749093) B8749093
theorem B7776971 : Blo 2303435 7776971 := bstep (se 1 (by rfl) ⟨5832728, by rfl⟩ : syracuseStep 7776971 = 11665457) B11665457
theorem B5184647 : Blo 2303435 5184647 := bstep (se 1 (by rfl) ⟨3888485, by rfl⟩ : syracuseStep 5184647 = 7776971) B7776971
theorem B3456431 : Blo 2303435 3456431 := bstep (se 1 (by rfl) ⟨2592323, by rfl⟩ : syracuseStep 3456431 = 5184647) B5184647
theorem B2304287 : Blo 2303435 2304287 := bstep (se 1 (by rfl) ⟨1728215, by rfl⟩ : syracuseStep 2304287 = 3456431) B3456431
theorem B3456437 : Blo 2303435 3456437 := bbase (se 5 (by rfl) ⟨162020, by rfl⟩ : syracuseStep 3456437 = 324041) (by norm_num)
theorem B2304291 : Blo 2303435 2304291 := bstep (se 1 (by rfl) ⟨1728218, by rfl⟩ : syracuseStep 2304291 = 3456437) B3456437
theorem B5832749 : Blo 2303435 5832749 := bbase (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) (by norm_num)
theorem B3888499 : Blo 2303435 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B5184665 : Blo 2303435 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B3456443 : Blo 2303435 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B2304295 : Blo 2303435 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B2592337 : Blo 2303435 2592337 := bbase (se 2 (by rfl) ⟨972126, by rfl⟩ : syracuseStep 2592337 = 1944253) (by norm_num)
theorem B3456449 : Blo 2303435 3456449 := bstep (se 2 (by rfl) ⟨1296168, by rfl⟩ : syracuseStep 3456449 = 2592337) B2592337
theorem B2304299 : Blo 2303435 2304299 := bstep (se 1 (by rfl) ⟨1728224, by rfl⟩ : syracuseStep 2304299 = 3456449) B3456449
theorem B3280933 : Blo 2303435 3280933 := bbase (se 4 (by rfl) ⟨307587, by rfl⟩ : syracuseStep 3280933 = 615175) (by norm_num)
theorem B4374577 : Blo 2303435 4374577 := bstep (se 2 (by rfl) ⟨1640466, by rfl⟩ : syracuseStep 4374577 = 3280933) B3280933
theorem B5832769 : Blo 2303435 5832769 := bstep (se 2 (by rfl) ⟨2187288, by rfl⟩ : syracuseStep 5832769 = 4374577) B4374577
theorem B7777025 : Blo 2303435 7777025 := bstep (se 2 (by rfl) ⟨2916384, by rfl⟩ : syracuseStep 7777025 = 5832769) B5832769
theorem B5184683 : Blo 2303435 5184683 := bstep (se 1 (by rfl) ⟨3888512, by rfl⟩ : syracuseStep 5184683 = 7777025) B7777025
theorem B3456455 : Blo 2303435 3456455 := bstep (se 1 (by rfl) ⟨2592341, by rfl⟩ : syracuseStep 3456455 = 5184683) B5184683
theorem B2304303 : Blo 2303435 2304303 := bstep (se 1 (by rfl) ⟨1728227, by rfl⟩ : syracuseStep 2304303 = 3456455) B3456455
theorem B3456461 : Blo 2303435 3456461 := bbase (se 3 (by rfl) ⟨648086, by rfl⟩ : syracuseStep 3456461 = 1296173) (by norm_num)
theorem B2304307 : Blo 2303435 2304307 := bstep (se 1 (by rfl) ⟨1728230, by rfl⟩ : syracuseStep 2304307 = 3456461) B3456461
theorem B5184701 : Blo 2303435 5184701 := bbase (se 3 (by rfl) ⟨972131, by rfl⟩ : syracuseStep 5184701 = 1944263) (by norm_num)
theorem B3456467 : Blo 2303435 3456467 := bstep (se 1 (by rfl) ⟨2592350, by rfl⟩ : syracuseStep 3456467 = 5184701) B5184701
theorem B2304311 : Blo 2303435 2304311 := bstep (se 1 (by rfl) ⟨1728233, by rfl⟩ : syracuseStep 2304311 = 3456467) B3456467
theorem B3888533 : Blo 2303435 3888533 := bbase (se 6 (by rfl) ⟨91137, by rfl⟩ : syracuseStep 3888533 = 182275) (by norm_num)
theorem B2592355 : Blo 2303435 2592355 := bstep (se 1 (by rfl) ⟨1944266, by rfl⟩ : syracuseStep 2592355 = 3888533) B3888533
theorem B3456473 : Blo 2303435 3456473 := bstep (se 2 (by rfl) ⟨1296177, by rfl⟩ : syracuseStep 3456473 = 2592355) B2592355
theorem B2304315 : Blo 2303435 2304315 := bstep (se 1 (by rfl) ⟨1728236, by rfl⟩ : syracuseStep 2304315 = 3456473) B3456473
theorem B5536613 : Blo 2303435 5536613 := bbase (se 4 (by rfl) ⟨519057, by rfl⟩ : syracuseStep 5536613 = 1038115) (by norm_num)
theorem B14764301 : Blo 2303435 14764301 := bstep (se 3 (by rfl) ⟨2768306, by rfl⟩ : syracuseStep 14764301 = 5536613) B5536613
theorem B9842867 : Blo 2303435 9842867 := bstep (se 1 (by rfl) ⟨7382150, by rfl⟩ : syracuseStep 9842867 = 14764301) B14764301
theorem B6561911 : Blo 2303435 6561911 := bstep (se 1 (by rfl) ⟨4921433, by rfl⟩ : syracuseStep 6561911 = 9842867) B9842867
theorem B17498429 : Blo 2303435 17498429 := bstep (se 3 (by rfl) ⟨3280955, by rfl⟩ : syracuseStep 17498429 = 6561911) B6561911
theorem B11665619 : Blo 2303435 11665619 := bstep (se 1 (by rfl) ⟨8749214, by rfl⟩ : syracuseStep 11665619 = 17498429) B17498429
theorem B7777079 : Blo 2303435 7777079 := bstep (se 1 (by rfl) ⟨5832809, by rfl⟩ : syracuseStep 7777079 = 11665619) B11665619
theorem B5184719 : Blo 2303435 5184719 := bstep (se 1 (by rfl) ⟨3888539, by rfl⟩ : syracuseStep 5184719 = 7777079) B7777079
theorem B3456479 : Blo 2303435 3456479 := bstep (se 1 (by rfl) ⟨2592359, by rfl⟩ : syracuseStep 3456479 = 5184719) B5184719
theorem B2304319 : Blo 2303435 2304319 := bstep (se 1 (by rfl) ⟨1728239, by rfl⟩ : syracuseStep 2304319 = 3456479) B3456479
theorem B3456485 : Blo 2303435 3456485 := bbase (se 4 (by rfl) ⟨324045, by rfl⟩ : syracuseStep 3456485 = 648091) (by norm_num)
theorem B2304323 : Blo 2303435 2304323 := bstep (se 1 (by rfl) ⟨1728242, by rfl⟩ : syracuseStep 2304323 = 3456485) B3456485
theorem B11377493 : Blo 2303435 11377493 := bbase (se 9 (by rfl) ⟨33332, by rfl⟩ : syracuseStep 11377493 = 66665) (by norm_num)
theorem B7584995 : Blo 2303435 7584995 := bstep (se 1 (by rfl) ⟨5688746, by rfl⟩ : syracuseStep 7584995 = 11377493) B11377493
theorem B5056663 : Blo 2303435 5056663 := bstep (se 1 (by rfl) ⟨3792497, by rfl⟩ : syracuseStep 5056663 = 7584995) B7584995
theorem B6742217 : Blo 2303435 6742217 := bstep (se 2 (by rfl) ⟨2528331, by rfl⟩ : syracuseStep 6742217 = 5056663) B5056663
theorem B17979245 : Blo 2303435 17979245 := bstep (se 3 (by rfl) ⟨3371108, by rfl⟩ : syracuseStep 17979245 = 6742217) B6742217
theorem B11986163 : Blo 2303435 11986163 := bstep (se 1 (by rfl) ⟨8989622, by rfl⟩ : syracuseStep 11986163 = 17979245) B17979245
theorem B7990775 : Blo 2303435 7990775 := bstep (se 1 (by rfl) ⟨5993081, by rfl⟩ : syracuseStep 7990775 = 11986163) B11986163
theorem B5327183 : Blo 2303435 5327183 := bstep (se 1 (by rfl) ⟨3995387, by rfl⟩ : syracuseStep 5327183 = 7990775) B7990775
theorem B3551455 : Blo 2303435 3551455 := bstep (se 1 (by rfl) ⟨2663591, by rfl⟩ : syracuseStep 3551455 = 5327183) B5327183
theorem B4735273 : Blo 2303435 4735273 := bstep (se 2 (by rfl) ⟨1775727, by rfl⟩ : syracuseStep 4735273 = 3551455) B3551455
theorem B6313697 : Blo 2303435 6313697 := bstep (se 2 (by rfl) ⟨2367636, by rfl⟩ : syracuseStep 6313697 = 4735273) B4735273
theorem B4209131 : Blo 2303435 4209131 := bstep (se 1 (by rfl) ⟨3156848, by rfl⟩ : syracuseStep 4209131 = 6313697) B6313697
theorem B2806087 : Blo 2303435 2806087 := bstep (se 1 (by rfl) ⟨2104565, by rfl⟩ : syracuseStep 2806087 = 4209131) B4209131
theorem B3741449 : Blo 2303435 3741449 := bstep (se 2 (by rfl) ⟨1403043, by rfl⟩ : syracuseStep 3741449 = 2806087) B2806087
theorem B9977197 : Blo 2303435 9977197 := bstep (se 3 (by rfl) ⟨1870724, by rfl⟩ : syracuseStep 9977197 = 3741449) B3741449
theorem B13302929 : Blo 2303435 13302929 := bstep (se 2 (by rfl) ⟨4988598, by rfl⟩ : syracuseStep 13302929 = 9977197) B9977197
theorem B8868619 : Blo 2303435 8868619 := bstep (se 1 (by rfl) ⟨6651464, by rfl⟩ : syracuseStep 8868619 = 13302929) B13302929
theorem B11824825 : Blo 2303435 11824825 := bstep (se 2 (by rfl) ⟨4434309, by rfl⟩ : syracuseStep 11824825 = 8868619) B8868619
theorem B15766433 : Blo 2303435 15766433 := bstep (se 2 (by rfl) ⟨5912412, by rfl⟩ : syracuseStep 15766433 = 11824825) B11824825
theorem B10510955 : Blo 2303435 10510955 := bstep (se 1 (by rfl) ⟨7883216, by rfl⟩ : syracuseStep 10510955 = 15766433) B15766433
theorem B7007303 : Blo 2303435 7007303 := bstep (se 1 (by rfl) ⟨5255477, by rfl⟩ : syracuseStep 7007303 = 10510955) B10510955
theorem B4671535 : Blo 2303435 4671535 := bstep (se 1 (by rfl) ⟨3503651, by rfl⟩ : syracuseStep 4671535 = 7007303) B7007303
theorem B6228713 : Blo 2303435 6228713 := bstep (se 2 (by rfl) ⟨2335767, by rfl⟩ : syracuseStep 6228713 = 4671535) B4671535
theorem B4152475 : Blo 2303435 4152475 := bstep (se 1 (by rfl) ⟨3114356, by rfl⟩ : syracuseStep 4152475 = 6228713) B6228713
theorem B22146533 : Blo 2303435 22146533 := bstep (se 4 (by rfl) ⟨2076237, by rfl⟩ : syracuseStep 22146533 = 4152475) B4152475
theorem B14764355 : Blo 2303435 14764355 := bstep (se 1 (by rfl) ⟨11073266, by rfl⟩ : syracuseStep 14764355 = 22146533) B22146533
theorem B9842903 : Blo 2303435 9842903 := bstep (se 1 (by rfl) ⟨7382177, by rfl⟩ : syracuseStep 9842903 = 14764355) B14764355
theorem B6561935 : Blo 2303435 6561935 := bstep (se 1 (by rfl) ⟨4921451, by rfl⟩ : syracuseStep 6561935 = 9842903) B9842903
theorem B4374623 : Blo 2303435 4374623 := bstep (se 1 (by rfl) ⟨3280967, by rfl⟩ : syracuseStep 4374623 = 6561935) B6561935
theorem B2916415 : Blo 2303435 2916415 := bstep (se 1 (by rfl) ⟨2187311, by rfl⟩ : syracuseStep 2916415 = 4374623) B4374623
theorem B3888553 : Blo 2303435 3888553 := bstep (se 2 (by rfl) ⟨1458207, by rfl⟩ : syracuseStep 3888553 = 2916415) B2916415
theorem B5184737 : Blo 2303435 5184737 := bstep (se 2 (by rfl) ⟨1944276, by rfl⟩ : syracuseStep 5184737 = 3888553) B3888553
theorem B3456491 : Blo 2303435 3456491 := bstep (se 1 (by rfl) ⟨2592368, by rfl⟩ : syracuseStep 3456491 = 5184737) B5184737
theorem B2304327 : Blo 2303435 2304327 := bstep (se 1 (by rfl) ⟨1728245, by rfl⟩ : syracuseStep 2304327 = 3456491) B3456491
theorem B2592373 : Blo 2303435 2592373 := bbase (se 5 (by rfl) ⟨121517, by rfl⟩ : syracuseStep 2592373 = 243035) (by norm_num)
theorem B3456497 : Blo 2303435 3456497 := bstep (se 2 (by rfl) ⟨1296186, by rfl⟩ : syracuseStep 3456497 = 2592373) B2592373
theorem B2304331 : Blo 2303435 2304331 := bstep (se 1 (by rfl) ⟨1728248, by rfl⟩ : syracuseStep 2304331 = 3456497) B3456497
theorem B2916425 : Blo 2303435 2916425 := bbase (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) (by norm_num)
theorem B7777133 : Blo 2303435 7777133 := bstep (se 3 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 7777133 = 2916425) B2916425
theorem B5184755 : Blo 2303435 5184755 := bstep (se 1 (by rfl) ⟨3888566, by rfl⟩ : syracuseStep 5184755 = 7777133) B7777133
theorem B3456503 : Blo 2303435 3456503 := bstep (se 1 (by rfl) ⟨2592377, by rfl⟩ : syracuseStep 3456503 = 5184755) B5184755
theorem B2304335 : Blo 2303435 2304335 := bstep (se 1 (by rfl) ⟨1728251, by rfl⟩ : syracuseStep 2304335 = 3456503) B3456503
theorem B3456509 : Blo 2303435 3456509 := bbase (se 3 (by rfl) ⟨648095, by rfl⟩ : syracuseStep 3456509 = 1296191) (by norm_num)
theorem B2304339 : Blo 2303435 2304339 := bstep (se 1 (by rfl) ⟨1728254, by rfl⟩ : syracuseStep 2304339 = 3456509) B3456509
theorem B5184773 : Blo 2303435 5184773 := bbase (se 4 (by rfl) ⟨486072, by rfl⟩ : syracuseStep 5184773 = 972145) (by norm_num)
theorem B3456515 : Blo 2303435 3456515 := bstep (se 1 (by rfl) ⟨2592386, by rfl⟩ : syracuseStep 3456515 = 5184773) B5184773
theorem B2304343 : Blo 2303435 2304343 := bstep (se 1 (by rfl) ⟨1728257, by rfl⟩ : syracuseStep 2304343 = 3456515) B3456515
theorem B4374661 : Blo 2303435 4374661 := bbase (se 4 (by rfl) ⟨410124, by rfl⟩ : syracuseStep 4374661 = 820249) (by norm_num)
theorem B5832881 : Blo 2303435 5832881 := bstep (se 2 (by rfl) ⟨2187330, by rfl⟩ : syracuseStep 5832881 = 4374661) B4374661
theorem B3888587 : Blo 2303435 3888587 := bstep (se 1 (by rfl) ⟨2916440, by rfl⟩ : syracuseStep 3888587 = 5832881) B5832881
theorem B2592391 : Blo 2303435 2592391 := bstep (se 1 (by rfl) ⟨1944293, by rfl⟩ : syracuseStep 2592391 = 3888587) B3888587
theorem B3456521 : Blo 2303435 3456521 := bstep (se 2 (by rfl) ⟨1296195, by rfl⟩ : syracuseStep 3456521 = 2592391) B2592391
theorem B2304347 : Blo 2303435 2304347 := bstep (se 1 (by rfl) ⟨1728260, by rfl⟩ : syracuseStep 2304347 = 3456521) B3456521
theorem B11665781 : Blo 2303435 11665781 := bbase (se 5 (by rfl) ⟨546833, by rfl⟩ : syracuseStep 11665781 = 1093667) (by norm_num)
theorem B7777187 : Blo 2303435 7777187 := bstep (se 1 (by rfl) ⟨5832890, by rfl⟩ : syracuseStep 7777187 = 11665781) B11665781
theorem B5184791 : Blo 2303435 5184791 := bstep (se 1 (by rfl) ⟨3888593, by rfl⟩ : syracuseStep 5184791 = 7777187) B7777187
theorem B3456527 : Blo 2303435 3456527 := bstep (se 1 (by rfl) ⟨2592395, by rfl⟩ : syracuseStep 3456527 = 5184791) B5184791
theorem B2304351 : Blo 2303435 2304351 := bstep (se 1 (by rfl) ⟨1728263, by rfl⟩ : syracuseStep 2304351 = 3456527) B3456527
theorem B3456533 : Blo 2303435 3456533 := bbase (se 6 (by rfl) ⟨81012, by rfl⟩ : syracuseStep 3456533 = 162025) (by norm_num)
theorem B2304355 : Blo 2303435 2304355 := bstep (se 1 (by rfl) ⟨1728266, by rfl⟩ : syracuseStep 2304355 = 3456533) B3456533
theorem B2528365 : Blo 2303435 2528365 := bbase (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) (by norm_num)
theorem B3371153 : Blo 2303435 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B8989741 : Blo 2303435 8989741 := bstep (se 3 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 8989741 = 3371153) B3371153
theorem B11986321 : Blo 2303435 11986321 := bstep (se 2 (by rfl) ⟨4494870, by rfl⟩ : syracuseStep 11986321 = 8989741) B8989741
theorem B15981761 : Blo 2303435 15981761 := bstep (se 2 (by rfl) ⟨5993160, by rfl⟩ : syracuseStep 15981761 = 11986321) B11986321
theorem B10654507 : Blo 2303435 10654507 := bstep (se 1 (by rfl) ⟨7990880, by rfl⟩ : syracuseStep 10654507 = 15981761) B15981761
theorem B56824037 : Blo 2303435 56824037 := bstep (se 4 (by rfl) ⟨5327253, by rfl⟩ : syracuseStep 56824037 = 10654507) B10654507
theorem B37882691 : Blo 2303435 37882691 := bstep (se 1 (by rfl) ⟨28412018, by rfl⟩ : syracuseStep 37882691 = 56824037) B56824037
theorem B25255127 : Blo 2303435 25255127 := bstep (se 1 (by rfl) ⟨18941345, by rfl⟩ : syracuseStep 25255127 = 37882691) B37882691
theorem B16836751 : Blo 2303435 16836751 := bstep (se 1 (by rfl) ⟨12627563, by rfl⟩ : syracuseStep 16836751 = 25255127) B25255127
theorem B22449001 : Blo 2303435 22449001 := bstep (se 2 (by rfl) ⟨8418375, by rfl⟩ : syracuseStep 22449001 = 16836751) B16836751
theorem B29932001 : Blo 2303435 29932001 := bstep (se 2 (by rfl) ⟨11224500, by rfl⟩ : syracuseStep 29932001 = 22449001) B22449001
theorem B19954667 : Blo 2303435 19954667 := bstep (se 1 (by rfl) ⟨14966000, by rfl⟩ : syracuseStep 19954667 = 29932001) B29932001
theorem B13303111 : Blo 2303435 13303111 := bstep (se 1 (by rfl) ⟨9977333, by rfl⟩ : syracuseStep 13303111 = 19954667) B19954667
theorem B17737481 : Blo 2303435 17737481 := bstep (se 2 (by rfl) ⟨6651555, by rfl⟩ : syracuseStep 17737481 = 13303111) B13303111
theorem B11824987 : Blo 2303435 11824987 := bstep (se 1 (by rfl) ⟨8868740, by rfl⟩ : syracuseStep 11824987 = 17737481) B17737481
theorem B15766649 : Blo 2303435 15766649 := bstep (se 2 (by rfl) ⟨5912493, by rfl⟩ : syracuseStep 15766649 = 11824987) B11824987
theorem B10511099 : Blo 2303435 10511099 := bstep (se 1 (by rfl) ⟨7883324, by rfl⟩ : syracuseStep 10511099 = 15766649) B15766649
theorem B7007399 : Blo 2303435 7007399 := bstep (se 1 (by rfl) ⟨5255549, by rfl⟩ : syracuseStep 7007399 = 10511099) B10511099
theorem B4671599 : Blo 2303435 4671599 := bstep (se 1 (by rfl) ⟨3503699, by rfl⟩ : syracuseStep 4671599 = 7007399) B7007399
theorem B12457597 : Blo 2303435 12457597 := bstep (se 3 (by rfl) ⟨2335799, by rfl⟩ : syracuseStep 12457597 = 4671599) B4671599
theorem B16610129 : Blo 2303435 16610129 := bstep (se 2 (by rfl) ⟨6228798, by rfl⟩ : syracuseStep 16610129 = 12457597) B12457597
theorem B11073419 : Blo 2303435 11073419 := bstep (se 1 (by rfl) ⟨8305064, by rfl⟩ : syracuseStep 11073419 = 16610129) B16610129
theorem B7382279 : Blo 2303435 7382279 := bstep (se 1 (by rfl) ⟨5536709, by rfl⟩ : syracuseStep 7382279 = 11073419) B11073419
theorem B19686077 : Blo 2303435 19686077 := bstep (se 3 (by rfl) ⟨3691139, by rfl⟩ : syracuseStep 19686077 = 7382279) B7382279
theorem B13124051 : Blo 2303435 13124051 := bstep (se 1 (by rfl) ⟨9843038, by rfl⟩ : syracuseStep 13124051 = 19686077) B19686077
theorem B8749367 : Blo 2303435 8749367 := bstep (se 1 (by rfl) ⟨6562025, by rfl⟩ : syracuseStep 8749367 = 13124051) B13124051
theorem B5832911 : Blo 2303435 5832911 := bstep (se 1 (by rfl) ⟨4374683, by rfl⟩ : syracuseStep 5832911 = 8749367) B8749367
theorem B3888607 : Blo 2303435 3888607 := bstep (se 1 (by rfl) ⟨2916455, by rfl⟩ : syracuseStep 3888607 = 5832911) B5832911
theorem B5184809 : Blo 2303435 5184809 := bstep (se 2 (by rfl) ⟨1944303, by rfl⟩ : syracuseStep 5184809 = 3888607) B3888607
theorem B3456539 : Blo 2303435 3456539 := bstep (se 1 (by rfl) ⟨2592404, by rfl⟩ : syracuseStep 3456539 = 5184809) B5184809
theorem B2304359 : Blo 2303435 2304359 := bstep (se 1 (by rfl) ⟨1728269, by rfl⟩ : syracuseStep 2304359 = 3456539) B3456539
theorem B2592409 : Blo 2303435 2592409 := bbase (se 2 (by rfl) ⟨972153, by rfl⟩ : syracuseStep 2592409 = 1944307) (by norm_num)
theorem B3456545 : Blo 2303435 3456545 := bstep (se 2 (by rfl) ⟨1296204, by rfl⟩ : syracuseStep 3456545 = 2592409) B2592409
theorem B2304363 : Blo 2303435 2304363 := bstep (se 1 (by rfl) ⟨1728272, by rfl⟩ : syracuseStep 2304363 = 3456545) B3456545
theorem B8749397 : Blo 2303435 8749397 := bbase (se 10 (by rfl) ⟨12816, by rfl⟩ : syracuseStep 8749397 = 25633) (by norm_num)
theorem B5832931 : Blo 2303435 5832931 := bstep (se 1 (by rfl) ⟨4374698, by rfl⟩ : syracuseStep 5832931 = 8749397) B8749397
theorem B7777241 : Blo 2303435 7777241 := bstep (se 2 (by rfl) ⟨2916465, by rfl⟩ : syracuseStep 7777241 = 5832931) B5832931
theorem B5184827 : Blo 2303435 5184827 := bstep (se 1 (by rfl) ⟨3888620, by rfl⟩ : syracuseStep 5184827 = 7777241) B7777241
theorem B3456551 : Blo 2303435 3456551 := bstep (se 1 (by rfl) ⟨2592413, by rfl⟩ : syracuseStep 3456551 = 5184827) B5184827
theorem B2304367 : Blo 2303435 2304367 := bstep (se 1 (by rfl) ⟨1728275, by rfl⟩ : syracuseStep 2304367 = 3456551) B3456551
theorem B3456557 : Blo 2303435 3456557 := bbase (se 3 (by rfl) ⟨648104, by rfl⟩ : syracuseStep 3456557 = 1296209) (by norm_num)
theorem B2304371 : Blo 2303435 2304371 := bstep (se 1 (by rfl) ⟨1728278, by rfl⟩ : syracuseStep 2304371 = 3456557) B3456557
theorem B5184845 : Blo 2303435 5184845 := bbase (se 3 (by rfl) ⟨972158, by rfl⟩ : syracuseStep 5184845 = 1944317) (by norm_num)
theorem B3456563 : Blo 2303435 3456563 := bstep (se 1 (by rfl) ⟨2592422, by rfl⟩ : syracuseStep 3456563 = 5184845) B5184845
theorem B2304375 : Blo 2303435 2304375 := bstep (se 1 (by rfl) ⟨1728281, by rfl⟩ : syracuseStep 2304375 = 3456563) B3456563
theorem B2916481 : Blo 2303435 2916481 := bbase (se 2 (by rfl) ⟨1093680, by rfl⟩ : syracuseStep 2916481 = 2187361) (by norm_num)
theorem B3888641 : Blo 2303435 3888641 := bstep (se 2 (by rfl) ⟨1458240, by rfl⟩ : syracuseStep 3888641 = 2916481) B2916481
theorem B2592427 : Blo 2303435 2592427 := bstep (se 1 (by rfl) ⟨1944320, by rfl⟩ : syracuseStep 2592427 = 3888641) B3888641
theorem B3456569 : Blo 2303435 3456569 := bstep (se 2 (by rfl) ⟨1296213, by rfl⟩ : syracuseStep 3456569 = 2592427) B2592427
theorem B2304379 : Blo 2303435 2304379 := bstep (se 1 (by rfl) ⟨1728284, by rfl⟩ : syracuseStep 2304379 = 3456569) B3456569
theorem B2460785 : Blo 2303435 2460785 := bbase (se 2 (by rfl) ⟨922794, by rfl⟩ : syracuseStep 2460785 = 1845589) (by norm_num)
theorem B26248373 : Blo 2303435 26248373 := bstep (se 5 (by rfl) ⟨1230392, by rfl⟩ : syracuseStep 26248373 = 2460785) B2460785
theorem B17498915 : Blo 2303435 17498915 := bstep (se 1 (by rfl) ⟨13124186, by rfl⟩ : syracuseStep 17498915 = 26248373) B26248373
theorem B11665943 : Blo 2303435 11665943 := bstep (se 1 (by rfl) ⟨8749457, by rfl⟩ : syracuseStep 11665943 = 17498915) B17498915
theorem B7777295 : Blo 2303435 7777295 := bstep (se 1 (by rfl) ⟨5832971, by rfl⟩ : syracuseStep 7777295 = 11665943) B11665943
theorem B5184863 : Blo 2303435 5184863 := bstep (se 1 (by rfl) ⟨3888647, by rfl⟩ : syracuseStep 5184863 = 7777295) B7777295
theorem B3456575 : Blo 2303435 3456575 := bstep (se 1 (by rfl) ⟨2592431, by rfl⟩ : syracuseStep 3456575 = 5184863) B5184863
theorem B2304383 : Blo 2303435 2304383 := bstep (se 1 (by rfl) ⟨1728287, by rfl⟩ : syracuseStep 2304383 = 3456575) B3456575
theorem B3456581 : Blo 2303435 3456581 := bbase (se 4 (by rfl) ⟨324054, by rfl⟩ : syracuseStep 3456581 = 648109) (by norm_num)
theorem B2304387 : Blo 2303435 2304387 := bstep (se 1 (by rfl) ⟨1728290, by rfl⟩ : syracuseStep 2304387 = 3456581) B3456581
theorem B3888661 : Blo 2303435 3888661 := bbase (se 6 (by rfl) ⟨91140, by rfl⟩ : syracuseStep 3888661 = 182281) (by norm_num)
theorem B5184881 : Blo 2303435 5184881 := bstep (se 2 (by rfl) ⟨1944330, by rfl⟩ : syracuseStep 5184881 = 3888661) B3888661
theorem B3456587 : Blo 2303435 3456587 := bstep (se 1 (by rfl) ⟨2592440, by rfl⟩ : syracuseStep 3456587 = 5184881) B5184881
theorem B2304391 : Blo 2303435 2304391 := bstep (se 1 (by rfl) ⟨1728293, by rfl⟩ : syracuseStep 2304391 = 3456587) B3456587
theorem B2592445 : Blo 2303435 2592445 := bbase (se 3 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 2592445 = 972167) (by norm_num)
theorem B3456593 : Blo 2303435 3456593 := bstep (se 2 (by rfl) ⟨1296222, by rfl⟩ : syracuseStep 3456593 = 2592445) B2592445
theorem B2304395 : Blo 2303435 2304395 := bstep (se 1 (by rfl) ⟨1728296, by rfl⟩ : syracuseStep 2304395 = 3456593) B3456593
theorem B7777349 : Blo 2303435 7777349 := bbase (se 4 (by rfl) ⟨729126, by rfl⟩ : syracuseStep 7777349 = 1458253) (by norm_num)
theorem B5184899 : Blo 2303435 5184899 := bstep (se 1 (by rfl) ⟨3888674, by rfl⟩ : syracuseStep 5184899 = 7777349) B7777349
theorem B3456599 : Blo 2303435 3456599 := bstep (se 1 (by rfl) ⟨2592449, by rfl⟩ : syracuseStep 3456599 = 5184899) B5184899
theorem B2304399 : Blo 2303435 2304399 := bstep (se 1 (by rfl) ⟨1728299, by rfl⟩ : syracuseStep 2304399 = 3456599) B3456599
theorem B3456605 : Blo 2303435 3456605 := bbase (se 3 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 3456605 = 1296227) (by norm_num)
theorem B2304403 : Blo 2303435 2304403 := bstep (se 1 (by rfl) ⟨1728302, by rfl⟩ : syracuseStep 2304403 = 3456605) B3456605
theorem B5184917 : Blo 2303435 5184917 := bbase (se 6 (by rfl) ⟨121521, by rfl⟩ : syracuseStep 5184917 = 243043) (by norm_num)
theorem B3456611 : Blo 2303435 3456611 := bstep (se 1 (by rfl) ⟨2592458, by rfl⟩ : syracuseStep 3456611 = 5184917) B5184917
theorem B2304407 : Blo 2303435 2304407 := bstep (se 1 (by rfl) ⟨1728305, by rfl⟩ : syracuseStep 2304407 = 3456611) B3456611
theorem B5255669 : Blo 2303435 5255669 := bbase (se 5 (by rfl) ⟨246359, by rfl⟩ : syracuseStep 5255669 = 492719) (by norm_num)
theorem B3503779 : Blo 2303435 3503779 := bstep (se 1 (by rfl) ⟨2627834, by rfl⟩ : syracuseStep 3503779 = 5255669) B5255669
theorem B18686821 : Blo 2303435 18686821 := bstep (se 4 (by rfl) ⟨1751889, by rfl⟩ : syracuseStep 18686821 = 3503779) B3503779
theorem B24915761 : Blo 2303435 24915761 := bstep (se 2 (by rfl) ⟨9343410, by rfl⟩ : syracuseStep 24915761 = 18686821) B18686821
theorem B16610507 : Blo 2303435 16610507 := bstep (se 1 (by rfl) ⟨12457880, by rfl⟩ : syracuseStep 16610507 = 24915761) B24915761
theorem B11073671 : Blo 2303435 11073671 := bstep (se 1 (by rfl) ⟨8305253, by rfl⟩ : syracuseStep 11073671 = 16610507) B16610507
theorem B7382447 : Blo 2303435 7382447 := bstep (se 1 (by rfl) ⟨5536835, by rfl⟩ : syracuseStep 7382447 = 11073671) B11073671
theorem B4921631 : Blo 2303435 4921631 := bstep (se 1 (by rfl) ⟨3691223, by rfl⟩ : syracuseStep 4921631 = 7382447) B7382447
theorem B3281087 : Blo 2303435 3281087 := bstep (se 1 (by rfl) ⟨2460815, by rfl⟩ : syracuseStep 3281087 = 4921631) B4921631
theorem B8749565 : Blo 2303435 8749565 := bstep (se 3 (by rfl) ⟨1640543, by rfl⟩ : syracuseStep 8749565 = 3281087) B3281087
theorem B5833043 : Blo 2303435 5833043 := bstep (se 1 (by rfl) ⟨4374782, by rfl⟩ : syracuseStep 5833043 = 8749565) B8749565
theorem B3888695 : Blo 2303435 3888695 := bstep (se 1 (by rfl) ⟨2916521, by rfl⟩ : syracuseStep 3888695 = 5833043) B5833043
theorem B2592463 : Blo 2303435 2592463 := bstep (se 1 (by rfl) ⟨1944347, by rfl⟩ : syracuseStep 2592463 = 3888695) B3888695
theorem B3456617 : Blo 2303435 3456617 := bstep (se 2 (by rfl) ⟨1296231, by rfl⟩ : syracuseStep 3456617 = 2592463) B2592463
theorem B2304411 : Blo 2303435 2304411 := bstep (se 1 (by rfl) ⟨1728308, by rfl⟩ : syracuseStep 2304411 = 3456617) B3456617
theorem B3691229 : Blo 2303435 3691229 := bbase (se 3 (by rfl) ⟨692105, by rfl⟩ : syracuseStep 3691229 = 1384211) (by norm_num)
theorem B9843277 : Blo 2303435 9843277 := bstep (se 3 (by rfl) ⟨1845614, by rfl⟩ : syracuseStep 9843277 = 3691229) B3691229
theorem B13124369 : Blo 2303435 13124369 := bstep (se 2 (by rfl) ⟨4921638, by rfl⟩ : syracuseStep 13124369 = 9843277) B9843277
theorem B8749579 : Blo 2303435 8749579 := bstep (se 1 (by rfl) ⟨6562184, by rfl⟩ : syracuseStep 8749579 = 13124369) B13124369
theorem B11666105 : Blo 2303435 11666105 := bstep (se 2 (by rfl) ⟨4374789, by rfl⟩ : syracuseStep 11666105 = 8749579) B8749579
theorem B7777403 : Blo 2303435 7777403 := bstep (se 1 (by rfl) ⟨5833052, by rfl⟩ : syracuseStep 7777403 = 11666105) B11666105
theorem B5184935 : Blo 2303435 5184935 := bstep (se 1 (by rfl) ⟨3888701, by rfl⟩ : syracuseStep 5184935 = 7777403) B7777403
theorem B3456623 : Blo 2303435 3456623 := bstep (se 1 (by rfl) ⟨2592467, by rfl⟩ : syracuseStep 3456623 = 5184935) B5184935
theorem B2304415 : Blo 2303435 2304415 := bstep (se 1 (by rfl) ⟨1728311, by rfl⟩ : syracuseStep 2304415 = 3456623) B3456623
theorem B3456629 : Blo 2303435 3456629 := bbase (se 5 (by rfl) ⟨162029, by rfl⟩ : syracuseStep 3456629 = 324059) (by norm_num)
theorem B2304419 : Blo 2303435 2304419 := bstep (se 1 (by rfl) ⟨1728314, by rfl⟩ : syracuseStep 2304419 = 3456629) B3456629
theorem B4374805 : Blo 2303435 4374805 := bbase (se 6 (by rfl) ⟨102534, by rfl⟩ : syracuseStep 4374805 = 205069) (by norm_num)
theorem B5833073 : Blo 2303435 5833073 := bstep (se 2 (by rfl) ⟨2187402, by rfl⟩ : syracuseStep 5833073 = 4374805) B4374805
theorem B3888715 : Blo 2303435 3888715 := bstep (se 1 (by rfl) ⟨2916536, by rfl⟩ : syracuseStep 3888715 = 5833073) B5833073
theorem B5184953 : Blo 2303435 5184953 := bstep (se 2 (by rfl) ⟨1944357, by rfl⟩ : syracuseStep 5184953 = 3888715) B3888715
theorem B3456635 : Blo 2303435 3456635 := bstep (se 1 (by rfl) ⟨2592476, by rfl⟩ : syracuseStep 3456635 = 5184953) B5184953
theorem B2304423 : Blo 2303435 2304423 := bstep (se 1 (by rfl) ⟨1728317, by rfl⟩ : syracuseStep 2304423 = 3456635) B3456635
theorem B2592481 : Blo 2303435 2592481 := bbase (se 2 (by rfl) ⟨972180, by rfl⟩ : syracuseStep 2592481 = 1944361) (by norm_num)
theorem B3456641 : Blo 2303435 3456641 := bstep (se 2 (by rfl) ⟨1296240, by rfl⟩ : syracuseStep 3456641 = 2592481) B2592481
theorem B2304427 : Blo 2303435 2304427 := bstep (se 1 (by rfl) ⟨1728320, by rfl⟩ : syracuseStep 2304427 = 3456641) B3456641
theorem B5833093 : Blo 2303435 5833093 := bbase (se 4 (by rfl) ⟨546852, by rfl⟩ : syracuseStep 5833093 = 1093705) (by norm_num)
theorem B7777457 : Blo 2303435 7777457 := bstep (se 2 (by rfl) ⟨2916546, by rfl⟩ : syracuseStep 7777457 = 5833093) B5833093
theorem B5184971 : Blo 2303435 5184971 := bstep (se 1 (by rfl) ⟨3888728, by rfl⟩ : syracuseStep 5184971 = 7777457) B7777457
theorem B3456647 : Blo 2303435 3456647 := bstep (se 1 (by rfl) ⟨2592485, by rfl⟩ : syracuseStep 3456647 = 5184971) B5184971
theorem B2304431 : Blo 2303435 2304431 := bstep (se 1 (by rfl) ⟨1728323, by rfl⟩ : syracuseStep 2304431 = 3456647) B3456647
theorem B3456653 : Blo 2303435 3456653 := bbase (se 3 (by rfl) ⟨648122, by rfl⟩ : syracuseStep 3456653 = 1296245) (by norm_num)
theorem B2304435 : Blo 2303435 2304435 := bstep (se 1 (by rfl) ⟨1728326, by rfl⟩ : syracuseStep 2304435 = 3456653) B3456653
theorem B5184989 : Blo 2303435 5184989 := bbase (se 3 (by rfl) ⟨972185, by rfl⟩ : syracuseStep 5184989 = 1944371) (by norm_num)
theorem B3456659 : Blo 2303435 3456659 := bstep (se 1 (by rfl) ⟨2592494, by rfl⟩ : syracuseStep 3456659 = 5184989) B5184989
theorem B2304439 : Blo 2303435 2304439 := bstep (se 1 (by rfl) ⟨1728329, by rfl⟩ : syracuseStep 2304439 = 3456659) B3456659
theorem B3888749 : Blo 2303435 3888749 := bbase (se 3 (by rfl) ⟨729140, by rfl⟩ : syracuseStep 3888749 = 1458281) (by norm_num)
theorem B2592499 : Blo 2303435 2592499 := bstep (se 1 (by rfl) ⟨1944374, by rfl⟩ : syracuseStep 2592499 = 3888749) B3888749
theorem B3456665 : Blo 2303435 3456665 := bstep (se 2 (by rfl) ⟨1296249, by rfl⟩ : syracuseStep 3456665 = 2592499) B2592499
theorem B2304443 : Blo 2303435 2304443 := bstep (se 1 (by rfl) ⟨1728332, by rfl⟩ : syracuseStep 2304443 = 3456665) B3456665
theorem B5255749 : Blo 2303435 5255749 := bbase (se 4 (by rfl) ⟨492726, by rfl⟩ : syracuseStep 5255749 = 985453) (by norm_num)
theorem B28030661 : Blo 2303435 28030661 := bstep (se 4 (by rfl) ⟨2627874, by rfl⟩ : syracuseStep 28030661 = 5255749) B5255749
theorem B18687107 : Blo 2303435 18687107 := bstep (se 1 (by rfl) ⟨14015330, by rfl⟩ : syracuseStep 18687107 = 28030661) B28030661
theorem B12458071 : Blo 2303435 12458071 := bstep (se 1 (by rfl) ⟨9343553, by rfl⟩ : syracuseStep 12458071 = 18687107) B18687107
theorem B16610761 : Blo 2303435 16610761 := bstep (se 2 (by rfl) ⟨6229035, by rfl⟩ : syracuseStep 16610761 = 12458071) B12458071
theorem B22147681 : Blo 2303435 22147681 := bstep (se 2 (by rfl) ⟨8305380, by rfl⟩ : syracuseStep 22147681 = 16610761) B16610761
theorem B29530241 : Blo 2303435 29530241 := bstep (se 2 (by rfl) ⟨11073840, by rfl⟩ : syracuseStep 29530241 = 22147681) B22147681
theorem B19686827 : Blo 2303435 19686827 := bstep (se 1 (by rfl) ⟨14765120, by rfl⟩ : syracuseStep 19686827 = 29530241) B29530241
theorem B13124551 : Blo 2303435 13124551 := bstep (se 1 (by rfl) ⟨9843413, by rfl⟩ : syracuseStep 13124551 = 19686827) B19686827
theorem B17499401 : Blo 2303435 17499401 := bstep (se 2 (by rfl) ⟨6562275, by rfl⟩ : syracuseStep 17499401 = 13124551) B13124551
theorem B11666267 : Blo 2303435 11666267 := bstep (se 1 (by rfl) ⟨8749700, by rfl⟩ : syracuseStep 11666267 = 17499401) B17499401
theorem B7777511 : Blo 2303435 7777511 := bstep (se 1 (by rfl) ⟨5833133, by rfl⟩ : syracuseStep 7777511 = 11666267) B11666267
theorem B5185007 : Blo 2303435 5185007 := bstep (se 1 (by rfl) ⟨3888755, by rfl⟩ : syracuseStep 5185007 = 7777511) B7777511
theorem B3456671 : Blo 2303435 3456671 := bstep (se 1 (by rfl) ⟨2592503, by rfl⟩ : syracuseStep 3456671 = 5185007) B5185007
theorem B2304447 : Blo 2303435 2304447 := bstep (se 1 (by rfl) ⟨1728335, by rfl⟩ : syracuseStep 2304447 = 3456671) B3456671
theorem B3456677 : Blo 2303435 3456677 := bbase (se 4 (by rfl) ⟨324063, by rfl⟩ : syracuseStep 3456677 = 648127) (by norm_num)
theorem B2304451 : Blo 2303435 2304451 := bstep (se 1 (by rfl) ⟨1728338, by rfl⟩ : syracuseStep 2304451 = 3456677) B3456677
theorem B2916577 : Blo 2303435 2916577 := bbase (se 2 (by rfl) ⟨1093716, by rfl⟩ : syracuseStep 2916577 = 2187433) (by norm_num)
theorem B3888769 : Blo 2303435 3888769 := bstep (se 2 (by rfl) ⟨1458288, by rfl⟩ : syracuseStep 3888769 = 2916577) B2916577
theorem B5185025 : Blo 2303435 5185025 := bstep (se 2 (by rfl) ⟨1944384, by rfl⟩ : syracuseStep 5185025 = 3888769) B3888769
theorem B3456683 : Blo 2303435 3456683 := bstep (se 1 (by rfl) ⟨2592512, by rfl⟩ : syracuseStep 3456683 = 5185025) B5185025
theorem B2304455 : Blo 2303435 2304455 := bstep (se 1 (by rfl) ⟨1728341, by rfl⟩ : syracuseStep 2304455 = 3456683) B3456683
theorem B2592517 : Blo 2303435 2592517 := bbase (se 4 (by rfl) ⟨243048, by rfl⟩ : syracuseStep 2592517 = 486097) (by norm_num)
theorem B3456689 : Blo 2303435 3456689 := bstep (se 2 (by rfl) ⟨1296258, by rfl⟩ : syracuseStep 3456689 = 2592517) B2592517
theorem B2304459 : Blo 2303435 2304459 := bstep (se 1 (by rfl) ⟨1728344, by rfl⟩ : syracuseStep 2304459 = 3456689) B3456689
theorem B3114541 : Blo 2303435 3114541 := bbase (se 3 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 3114541 = 1167953) (by norm_num)
theorem B4152721 : Blo 2303435 4152721 := bstep (se 2 (by rfl) ⟨1557270, by rfl⟩ : syracuseStep 4152721 = 3114541) B3114541
theorem B5536961 : Blo 2303435 5536961 := bstep (se 2 (by rfl) ⟨2076360, by rfl⟩ : syracuseStep 5536961 = 4152721) B4152721
theorem B3691307 : Blo 2303435 3691307 := bstep (se 1 (by rfl) ⟨2768480, by rfl⟩ : syracuseStep 3691307 = 5536961) B5536961
theorem B2460871 : Blo 2303435 2460871 := bstep (se 1 (by rfl) ⟨1845653, by rfl⟩ : syracuseStep 2460871 = 3691307) B3691307
theorem B3281161 : Blo 2303435 3281161 := bstep (se 2 (by rfl) ⟨1230435, by rfl⟩ : syracuseStep 3281161 = 2460871) B2460871
theorem B4374881 : Blo 2303435 4374881 := bstep (se 2 (by rfl) ⟨1640580, by rfl⟩ : syracuseStep 4374881 = 3281161) B3281161
theorem B2916587 : Blo 2303435 2916587 := bstep (se 1 (by rfl) ⟨2187440, by rfl⟩ : syracuseStep 2916587 = 4374881) B4374881
theorem B7777565 : Blo 2303435 7777565 := bstep (se 3 (by rfl) ⟨1458293, by rfl⟩ : syracuseStep 7777565 = 2916587) B2916587
theorem B5185043 : Blo 2303435 5185043 := bstep (se 1 (by rfl) ⟨3888782, by rfl⟩ : syracuseStep 5185043 = 7777565) B7777565
theorem B3456695 : Blo 2303435 3456695 := bstep (se 1 (by rfl) ⟨2592521, by rfl⟩ : syracuseStep 3456695 = 5185043) B5185043
theorem B2304463 : Blo 2303435 2304463 := bstep (se 1 (by rfl) ⟨1728347, by rfl⟩ : syracuseStep 2304463 = 3456695) B3456695
theorem B3456701 : Blo 2303435 3456701 := bbase (se 3 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 3456701 = 1296263) (by norm_num)
theorem B2304467 : Blo 2303435 2304467 := bstep (se 1 (by rfl) ⟨1728350, by rfl⟩ : syracuseStep 2304467 = 3456701) B3456701
theorem B5185061 : Blo 2303435 5185061 := bbase (se 4 (by rfl) ⟨486099, by rfl⟩ : syracuseStep 5185061 = 972199) (by norm_num)
theorem B3456707 : Blo 2303435 3456707 := bstep (se 1 (by rfl) ⟨2592530, by rfl⟩ : syracuseStep 3456707 = 5185061) B5185061
theorem B2304471 : Blo 2303435 2304471 := bstep (se 1 (by rfl) ⟨1728353, by rfl⟩ : syracuseStep 2304471 = 3456707) B3456707
theorem B5833205 : Blo 2303435 5833205 := bbase (se 5 (by rfl) ⟨273431, by rfl⟩ : syracuseStep 5833205 = 546863) (by norm_num)
theorem B3888803 : Blo 2303435 3888803 := bstep (se 1 (by rfl) ⟨2916602, by rfl⟩ : syracuseStep 3888803 = 5833205) B5833205
theorem B2592535 : Blo 2303435 2592535 := bstep (se 1 (by rfl) ⟨1944401, by rfl⟩ : syracuseStep 2592535 = 3888803) B3888803
theorem B3456713 : Blo 2303435 3456713 := bstep (se 2 (by rfl) ⟨1296267, by rfl⟩ : syracuseStep 3456713 = 2592535) B2592535
theorem B2304475 : Blo 2303435 2304475 := bstep (se 1 (by rfl) ⟨1728356, by rfl⟩ : syracuseStep 2304475 = 3456713) B3456713
theorem B2335921 : Blo 2303435 2335921 := bbase (se 2 (by rfl) ⟨875970, by rfl⟩ : syracuseStep 2335921 = 1751941) (by norm_num)
theorem B49832981 : Blo 2303435 49832981 := bstep (se 6 (by rfl) ⟨1167960, by rfl⟩ : syracuseStep 49832981 = 2335921) B2335921
theorem B33221987 : Blo 2303435 33221987 := bstep (se 1 (by rfl) ⟨24916490, by rfl⟩ : syracuseStep 33221987 = 49832981) B49832981
theorem B22147991 : Blo 2303435 22147991 := bstep (se 1 (by rfl) ⟨16610993, by rfl⟩ : syracuseStep 22147991 = 33221987) B33221987
theorem B14765327 : Blo 2303435 14765327 := bstep (se 1 (by rfl) ⟨11073995, by rfl⟩ : syracuseStep 14765327 = 22147991) B22147991
theorem B9843551 : Blo 2303435 9843551 := bstep (se 1 (by rfl) ⟨7382663, by rfl⟩ : syracuseStep 9843551 = 14765327) B14765327
theorem B6562367 : Blo 2303435 6562367 := bstep (se 1 (by rfl) ⟨4921775, by rfl⟩ : syracuseStep 6562367 = 9843551) B9843551
theorem B4374911 : Blo 2303435 4374911 := bstep (se 1 (by rfl) ⟨3281183, by rfl⟩ : syracuseStep 4374911 = 6562367) B6562367
theorem B11666429 : Blo 2303435 11666429 := bstep (se 3 (by rfl) ⟨2187455, by rfl⟩ : syracuseStep 11666429 = 4374911) B4374911
theorem B7777619 : Blo 2303435 7777619 := bstep (se 1 (by rfl) ⟨5833214, by rfl⟩ : syracuseStep 7777619 = 11666429) B11666429
theorem B5185079 : Blo 2303435 5185079 := bstep (se 1 (by rfl) ⟨3888809, by rfl⟩ : syracuseStep 5185079 = 7777619) B7777619
theorem B3456719 : Blo 2303435 3456719 := bstep (se 1 (by rfl) ⟨2592539, by rfl⟩ : syracuseStep 3456719 = 5185079) B5185079
theorem B2304479 : Blo 2303435 2304479 := bstep (se 1 (by rfl) ⟨1728359, by rfl⟩ : syracuseStep 2304479 = 3456719) B3456719
theorem B3456725 : Blo 2303435 3456725 := bbase (se 7 (by rfl) ⟨40508, by rfl⟩ : syracuseStep 3456725 = 81017) (by norm_num)
theorem B2304483 : Blo 2303435 2304483 := bstep (se 1 (by rfl) ⟨1728362, by rfl⟩ : syracuseStep 2304483 = 3456725) B3456725
theorem B2768509 : Blo 2303435 2768509 := bbase (se 3 (by rfl) ⟨519095, by rfl⟩ : syracuseStep 2768509 = 1038191) (by norm_num)
theorem B3691345 : Blo 2303435 3691345 := bstep (se 2 (by rfl) ⟨1384254, by rfl⟩ : syracuseStep 3691345 = 2768509) B2768509
theorem B4921793 : Blo 2303435 4921793 := bstep (se 2 (by rfl) ⟨1845672, by rfl⟩ : syracuseStep 4921793 = 3691345) B3691345
theorem B3281195 : Blo 2303435 3281195 := bstep (se 1 (by rfl) ⟨2460896, by rfl⟩ : syracuseStep 3281195 = 4921793) B4921793
theorem B8749853 : Blo 2303435 8749853 := bstep (se 3 (by rfl) ⟨1640597, by rfl⟩ : syracuseStep 8749853 = 3281195) B3281195
theorem B5833235 : Blo 2303435 5833235 := bstep (se 1 (by rfl) ⟨4374926, by rfl⟩ : syracuseStep 5833235 = 8749853) B8749853
theorem B3888823 : Blo 2303435 3888823 := bstep (se 1 (by rfl) ⟨2916617, by rfl⟩ : syracuseStep 3888823 = 5833235) B5833235
theorem B5185097 : Blo 2303435 5185097 := bstep (se 2 (by rfl) ⟨1944411, by rfl⟩ : syracuseStep 5185097 = 3888823) B3888823
theorem B3456731 : Blo 2303435 3456731 := bstep (se 1 (by rfl) ⟨2592548, by rfl⟩ : syracuseStep 3456731 = 5185097) B5185097
theorem B2304487 : Blo 2303435 2304487 := bstep (se 1 (by rfl) ⟨1728365, by rfl⟩ : syracuseStep 2304487 = 3456731) B3456731
theorem B2592553 : Blo 2303435 2592553 := bbase (se 2 (by rfl) ⟨972207, by rfl⟩ : syracuseStep 2592553 = 1944415) (by norm_num)
theorem B3456737 : Blo 2303435 3456737 := bstep (se 2 (by rfl) ⟨1296276, by rfl⟩ : syracuseStep 3456737 = 2592553) B2592553
theorem B2304491 : Blo 2303435 2304491 := bstep (se 1 (by rfl) ⟨1728368, by rfl⟩ : syracuseStep 2304491 = 3456737) B3456737
theorem B14765429 : Blo 2303435 14765429 := bbase (se 5 (by rfl) ⟨692129, by rfl⟩ : syracuseStep 14765429 = 1384259) (by norm_num)
theorem B9843619 : Blo 2303435 9843619 := bstep (se 1 (by rfl) ⟨7382714, by rfl⟩ : syracuseStep 9843619 = 14765429) B14765429
theorem B13124825 : Blo 2303435 13124825 := bstep (se 2 (by rfl) ⟨4921809, by rfl⟩ : syracuseStep 13124825 = 9843619) B9843619
theorem B8749883 : Blo 2303435 8749883 := bstep (se 1 (by rfl) ⟨6562412, by rfl⟩ : syracuseStep 8749883 = 13124825) B13124825
theorem B5833255 : Blo 2303435 5833255 := bstep (se 1 (by rfl) ⟨4374941, by rfl⟩ : syracuseStep 5833255 = 8749883) B8749883
theorem B7777673 : Blo 2303435 7777673 := bstep (se 2 (by rfl) ⟨2916627, by rfl⟩ : syracuseStep 7777673 = 5833255) B5833255
theorem B5185115 : Blo 2303435 5185115 := bstep (se 1 (by rfl) ⟨3888836, by rfl⟩ : syracuseStep 5185115 = 7777673) B7777673
theorem B3456743 : Blo 2303435 3456743 := bstep (se 1 (by rfl) ⟨2592557, by rfl⟩ : syracuseStep 3456743 = 5185115) B5185115
theorem B2304495 : Blo 2303435 2304495 := bstep (se 1 (by rfl) ⟨1728371, by rfl⟩ : syracuseStep 2304495 = 3456743) B3456743
theorem B3456749 : Blo 2303435 3456749 := bbase (se 3 (by rfl) ⟨648140, by rfl⟩ : syracuseStep 3456749 = 1296281) (by norm_num)
theorem B2304499 : Blo 2303435 2304499 := bstep (se 1 (by rfl) ⟨1728374, by rfl⟩ : syracuseStep 2304499 = 3456749) B3456749
theorem B5185133 : Blo 2303435 5185133 := bbase (se 3 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 5185133 = 1944425) (by norm_num)
theorem B3456755 : Blo 2303435 3456755 := bstep (se 1 (by rfl) ⟨2592566, by rfl⟩ : syracuseStep 3456755 = 5185133) B5185133
theorem B2304503 : Blo 2303435 2304503 := bstep (se 1 (by rfl) ⟨1728377, by rfl⟩ : syracuseStep 2304503 = 3456755) B3456755
theorem B4374965 : Blo 2303435 4374965 := bbase (se 5 (by rfl) ⟨205076, by rfl⟩ : syracuseStep 4374965 = 410153) (by norm_num)
theorem B2916643 : Blo 2303435 2916643 := bstep (se 1 (by rfl) ⟨2187482, by rfl⟩ : syracuseStep 2916643 = 4374965) B4374965
theorem B3888857 : Blo 2303435 3888857 := bstep (se 2 (by rfl) ⟨1458321, by rfl⟩ : syracuseStep 3888857 = 2916643) B2916643
theorem B2592571 : Blo 2303435 2592571 := bstep (se 1 (by rfl) ⟨1944428, by rfl⟩ : syracuseStep 2592571 = 3888857) B3888857
theorem B3456761 : Blo 2303435 3456761 := bstep (se 2 (by rfl) ⟨1296285, by rfl⟩ : syracuseStep 3456761 = 2592571) B2592571
theorem B2304507 : Blo 2303435 2304507 := bstep (se 1 (by rfl) ⟨1728380, by rfl⟩ : syracuseStep 2304507 = 3456761) B3456761
theorem B2956441 : Blo 2303435 2956441 := bbase (se 2 (by rfl) ⟨1108665, by rfl⟩ : syracuseStep 2956441 = 2217331) (by norm_num)
theorem B3941921 : Blo 2303435 3941921 := bstep (se 2 (by rfl) ⟨1478220, by rfl⟩ : syracuseStep 3941921 = 2956441) B2956441
theorem B10511789 : Blo 2303435 10511789 := bstep (se 3 (by rfl) ⟨1970960, by rfl⟩ : syracuseStep 10511789 = 3941921) B3941921
theorem B28031437 : Blo 2303435 28031437 := bstep (se 3 (by rfl) ⟨5255894, by rfl⟩ : syracuseStep 28031437 = 10511789) B10511789
theorem B149500997 : Blo 2303435 149500997 := bstep (se 4 (by rfl) ⟨14015718, by rfl⟩ : syracuseStep 149500997 = 28031437) B28031437
theorem B99667331 : Blo 2303435 99667331 := bstep (se 1 (by rfl) ⟨74750498, by rfl⟩ : syracuseStep 99667331 = 149500997) B149500997
theorem B66444887 : Blo 2303435 66444887 := bstep (se 1 (by rfl) ⟨49833665, by rfl⟩ : syracuseStep 66444887 = 99667331) B99667331
theorem B44296591 : Blo 2303435 44296591 := bstep (se 1 (by rfl) ⟨33222443, by rfl⟩ : syracuseStep 44296591 = 66444887) B66444887
theorem B59062121 : Blo 2303435 59062121 := bstep (se 2 (by rfl) ⟨22148295, by rfl⟩ : syracuseStep 59062121 = 44296591) B44296591
theorem B39374747 : Blo 2303435 39374747 := bstep (se 1 (by rfl) ⟨29531060, by rfl⟩ : syracuseStep 39374747 = 59062121) B59062121
theorem B26249831 : Blo 2303435 26249831 := bstep (se 1 (by rfl) ⟨19687373, by rfl⟩ : syracuseStep 26249831 = 39374747) B39374747
theorem B17499887 : Blo 2303435 17499887 := bstep (se 1 (by rfl) ⟨13124915, by rfl⟩ : syracuseStep 17499887 = 26249831) B26249831
theorem B11666591 : Blo 2303435 11666591 := bstep (se 1 (by rfl) ⟨8749943, by rfl⟩ : syracuseStep 11666591 = 17499887) B17499887
theorem B7777727 : Blo 2303435 7777727 := bstep (se 1 (by rfl) ⟨5833295, by rfl⟩ : syracuseStep 7777727 = 11666591) B11666591
theorem B5185151 : Blo 2303435 5185151 := bstep (se 1 (by rfl) ⟨3888863, by rfl⟩ : syracuseStep 5185151 = 7777727) B7777727
theorem B3456767 : Blo 2303435 3456767 := bstep (se 1 (by rfl) ⟨2592575, by rfl⟩ : syracuseStep 3456767 = 5185151) B5185151
theorem B2304511 : Blo 2303435 2304511 := bstep (se 1 (by rfl) ⟨1728383, by rfl⟩ : syracuseStep 2304511 = 3456767) B3456767
theorem B3456773 : Blo 2303435 3456773 := bbase (se 4 (by rfl) ⟨324072, by rfl⟩ : syracuseStep 3456773 = 648145) (by norm_num)
theorem B2304515 : Blo 2303435 2304515 := bstep (se 1 (by rfl) ⟨1728386, by rfl⟩ : syracuseStep 2304515 = 3456773) B3456773
theorem B3888877 : Blo 2303435 3888877 := bbase (se 3 (by rfl) ⟨729164, by rfl⟩ : syracuseStep 3888877 = 1458329) (by norm_num)
theorem B5185169 : Blo 2303435 5185169 := bstep (se 2 (by rfl) ⟨1944438, by rfl⟩ : syracuseStep 5185169 = 3888877) B3888877
theorem B3456779 : Blo 2303435 3456779 := bstep (se 1 (by rfl) ⟨2592584, by rfl⟩ : syracuseStep 3456779 = 5185169) B5185169
theorem B2304519 : Blo 2303435 2304519 := bstep (se 1 (by rfl) ⟨1728389, by rfl⟩ : syracuseStep 2304519 = 3456779) B3456779
theorem B2592589 : Blo 2303435 2592589 := bbase (se 3 (by rfl) ⟨486110, by rfl⟩ : syracuseStep 2592589 = 972221) (by norm_num)
theorem B3456785 : Blo 2303435 3456785 := bstep (se 2 (by rfl) ⟨1296294, by rfl⟩ : syracuseStep 3456785 = 2592589) B2592589
theorem B2304523 : Blo 2303435 2304523 := bstep (se 1 (by rfl) ⟨1728392, by rfl⟩ : syracuseStep 2304523 = 3456785) B3456785
theorem B7777781 : Blo 2303435 7777781 := bbase (se 5 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 7777781 = 729167) (by norm_num)
theorem B5185187 : Blo 2303435 5185187 := bstep (se 1 (by rfl) ⟨3888890, by rfl⟩ : syracuseStep 5185187 = 7777781) B7777781
theorem B3456791 : Blo 2303435 3456791 := bstep (se 1 (by rfl) ⟨2592593, by rfl⟩ : syracuseStep 3456791 = 5185187) B5185187
theorem B2304527 : Blo 2303435 2304527 := bstep (se 1 (by rfl) ⟨1728395, by rfl⟩ : syracuseStep 2304527 = 3456791) B3456791
theorem B3456797 : Blo 2303435 3456797 := bbase (se 3 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 3456797 = 1296299) (by norm_num)
theorem B2304531 : Blo 2303435 2304531 := bstep (se 1 (by rfl) ⟨1728398, by rfl⟩ : syracuseStep 2304531 = 3456797) B3456797
theorem B5185205 : Blo 2303435 5185205 := bbase (se 5 (by rfl) ⟨243056, by rfl⟩ : syracuseStep 5185205 = 486113) (by norm_num)
theorem B3456803 : Blo 2303435 3456803 := bstep (se 1 (by rfl) ⟨2592602, by rfl⟩ : syracuseStep 3456803 = 5185205) B5185205
theorem B2304535 : Blo 2303435 2304535 := bstep (se 1 (by rfl) ⟨1728401, by rfl⟩ : syracuseStep 2304535 = 3456803) B3456803
theorem B13125077 : Blo 2303435 13125077 := bbase (se 7 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 13125077 = 307619) (by norm_num)
theorem B8750051 : Blo 2303435 8750051 := bstep (se 1 (by rfl) ⟨6562538, by rfl⟩ : syracuseStep 8750051 = 13125077) B13125077
theorem B5833367 : Blo 2303435 5833367 := bstep (se 1 (by rfl) ⟨4375025, by rfl⟩ : syracuseStep 5833367 = 8750051) B8750051
theorem B3888911 : Blo 2303435 3888911 := bstep (se 1 (by rfl) ⟨2916683, by rfl⟩ : syracuseStep 3888911 = 5833367) B5833367
theorem B2592607 : Blo 2303435 2592607 := bstep (se 1 (by rfl) ⟨1944455, by rfl⟩ : syracuseStep 2592607 = 3888911) B3888911
theorem B3456809 : Blo 2303435 3456809 := bstep (se 2 (by rfl) ⟨1296303, by rfl⟩ : syracuseStep 3456809 = 2592607) B2592607
theorem B2304539 : Blo 2303435 2304539 := bstep (se 1 (by rfl) ⟨1728404, by rfl⟩ : syracuseStep 2304539 = 3456809) B3456809
theorem B6562549 : Blo 2303435 6562549 := bbase (se 5 (by rfl) ⟨307619, by rfl⟩ : syracuseStep 6562549 = 615239) (by norm_num)
theorem B8750065 : Blo 2303435 8750065 := bstep (se 2 (by rfl) ⟨3281274, by rfl⟩ : syracuseStep 8750065 = 6562549) B6562549
theorem B11666753 : Blo 2303435 11666753 := bstep (se 2 (by rfl) ⟨4375032, by rfl⟩ : syracuseStep 11666753 = 8750065) B8750065
theorem B7777835 : Blo 2303435 7777835 := bstep (se 1 (by rfl) ⟨5833376, by rfl⟩ : syracuseStep 7777835 = 11666753) B11666753
theorem B5185223 : Blo 2303435 5185223 := bstep (se 1 (by rfl) ⟨3888917, by rfl⟩ : syracuseStep 5185223 = 7777835) B7777835
theorem B3456815 : Blo 2303435 3456815 := bstep (se 1 (by rfl) ⟨2592611, by rfl⟩ : syracuseStep 3456815 = 5185223) B5185223
theorem B2304543 : Blo 2303435 2304543 := bstep (se 1 (by rfl) ⟨1728407, by rfl⟩ : syracuseStep 2304543 = 3456815) B3456815
theorem B3456821 : Blo 2303435 3456821 := bbase (se 5 (by rfl) ⟨162038, by rfl⟩ : syracuseStep 3456821 = 324077) (by norm_num)
theorem B2304547 : Blo 2303435 2304547 := bstep (se 1 (by rfl) ⟨1728410, by rfl⟩ : syracuseStep 2304547 = 3456821) B3456821
theorem B5833397 : Blo 2303435 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B3888931 : Blo 2303435 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B5185241 : Blo 2303435 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B3456827 : Blo 2303435 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B2304551 : Blo 2303435 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B2592625 : Blo 2303435 2592625 := bbase (se 2 (by rfl) ⟨972234, by rfl⟩ : syracuseStep 2592625 = 1944469) (by norm_num)
theorem B3456833 : Blo 2303435 3456833 := bstep (se 2 (by rfl) ⟨1296312, by rfl⟩ : syracuseStep 3456833 = 2592625) B2592625
theorem B2304555 : Blo 2303435 2304555 := bstep (se 1 (by rfl) ⟨1728416, by rfl⟩ : syracuseStep 2304555 = 3456833) B3456833
theorem B9843893 : Blo 2303435 9843893 := bbase (se 5 (by rfl) ⟨461432, by rfl⟩ : syracuseStep 9843893 = 922865) (by norm_num)
theorem B6562595 : Blo 2303435 6562595 := bstep (se 1 (by rfl) ⟨4921946, by rfl⟩ : syracuseStep 6562595 = 9843893) B9843893
theorem B4375063 : Blo 2303435 4375063 := bstep (se 1 (by rfl) ⟨3281297, by rfl⟩ : syracuseStep 4375063 = 6562595) B6562595
theorem B5833417 : Blo 2303435 5833417 := bstep (se 2 (by rfl) ⟨2187531, by rfl⟩ : syracuseStep 5833417 = 4375063) B4375063
theorem B7777889 : Blo 2303435 7777889 := bstep (se 2 (by rfl) ⟨2916708, by rfl⟩ : syracuseStep 7777889 = 5833417) B5833417
theorem B5185259 : Blo 2303435 5185259 := bstep (se 1 (by rfl) ⟨3888944, by rfl⟩ : syracuseStep 5185259 = 7777889) B7777889
theorem B3456839 : Blo 2303435 3456839 := bstep (se 1 (by rfl) ⟨2592629, by rfl⟩ : syracuseStep 3456839 = 5185259) B5185259
theorem B2304559 : Blo 2303435 2304559 := bstep (se 1 (by rfl) ⟨1728419, by rfl⟩ : syracuseStep 2304559 = 3456839) B3456839
theorem B3456845 : Blo 2303435 3456845 := bbase (se 3 (by rfl) ⟨648158, by rfl⟩ : syracuseStep 3456845 = 1296317) (by norm_num)
theorem B2304563 : Blo 2303435 2304563 := bstep (se 1 (by rfl) ⟨1728422, by rfl⟩ : syracuseStep 2304563 = 3456845) B3456845
theorem B5185277 : Blo 2303435 5185277 := bbase (se 3 (by rfl) ⟨972239, by rfl⟩ : syracuseStep 5185277 = 1944479) (by norm_num)
theorem B3456851 : Blo 2303435 3456851 := bstep (se 1 (by rfl) ⟨2592638, by rfl⟩ : syracuseStep 3456851 = 5185277) B5185277
theorem B2304567 : Blo 2303435 2304567 := bstep (se 1 (by rfl) ⟨1728425, by rfl⟩ : syracuseStep 2304567 = 3456851) B3456851
theorem B3888965 : Blo 2303435 3888965 := bbase (se 4 (by rfl) ⟨364590, by rfl⟩ : syracuseStep 3888965 = 729181) (by norm_num)
theorem B2592643 : Blo 2303435 2592643 := bstep (se 1 (by rfl) ⟨1944482, by rfl⟩ : syracuseStep 2592643 = 3888965) B3888965
theorem B3456857 : Blo 2303435 3456857 := bstep (se 2 (by rfl) ⟨1296321, by rfl⟩ : syracuseStep 3456857 = 2592643) B2592643
theorem B2304571 : Blo 2303435 2304571 := bstep (se 1 (by rfl) ⟨1728428, by rfl⟩ : syracuseStep 2304571 = 3456857) B3456857
theorem B17500373 : Blo 2303435 17500373 := bbase (se 7 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 17500373 = 410165) (by norm_num)
theorem B11666915 : Blo 2303435 11666915 := bstep (se 1 (by rfl) ⟨8750186, by rfl⟩ : syracuseStep 11666915 = 17500373) B17500373
theorem B7777943 : Blo 2303435 7777943 := bstep (se 1 (by rfl) ⟨5833457, by rfl⟩ : syracuseStep 7777943 = 11666915) B11666915
theorem B5185295 : Blo 2303435 5185295 := bstep (se 1 (by rfl) ⟨3888971, by rfl⟩ : syracuseStep 5185295 = 7777943) B7777943
theorem B3456863 : Blo 2303435 3456863 := bstep (se 1 (by rfl) ⟨2592647, by rfl⟩ : syracuseStep 3456863 = 5185295) B5185295
theorem B2304575 : Blo 2303435 2304575 := bstep (se 1 (by rfl) ⟨1728431, by rfl⟩ : syracuseStep 2304575 = 3456863) B3456863
theorem B3456869 : Blo 2303435 3456869 := bbase (se 4 (by rfl) ⟨324081, by rfl⟩ : syracuseStep 3456869 = 648163) (by norm_num)
theorem B2304579 : Blo 2303435 2304579 := bstep (se 1 (by rfl) ⟨1728434, by rfl⟩ : syracuseStep 2304579 = 3456869) B3456869
theorem B4375109 : Blo 2303435 4375109 := bbase (se 4 (by rfl) ⟨410166, by rfl⟩ : syracuseStep 4375109 = 820333) (by norm_num)
theorem B2916739 : Blo 2303435 2916739 := bstep (se 1 (by rfl) ⟨2187554, by rfl⟩ : syracuseStep 2916739 = 4375109) B4375109
theorem B3888985 : Blo 2303435 3888985 := bstep (se 2 (by rfl) ⟨1458369, by rfl⟩ : syracuseStep 3888985 = 2916739) B2916739
theorem B5185313 : Blo 2303435 5185313 := bstep (se 2 (by rfl) ⟨1944492, by rfl⟩ : syracuseStep 5185313 = 3888985) B3888985
theorem B3456875 : Blo 2303435 3456875 := bstep (se 1 (by rfl) ⟨2592656, by rfl⟩ : syracuseStep 3456875 = 5185313) B5185313
theorem B2304583 : Blo 2303435 2304583 := bstep (se 1 (by rfl) ⟨1728437, by rfl⟩ : syracuseStep 2304583 = 3456875) B3456875
theorem B2592661 : Blo 2303435 2592661 := bbase (se 6 (by rfl) ⟨60765, by rfl⟩ : syracuseStep 2592661 = 121531) (by norm_num)
theorem B3456881 : Blo 2303435 3456881 := bstep (se 2 (by rfl) ⟨1296330, by rfl⟩ : syracuseStep 3456881 = 2592661) B2592661
theorem B2304587 : Blo 2303435 2304587 := bstep (se 1 (by rfl) ⟨1728440, by rfl⟩ : syracuseStep 2304587 = 3456881) B3456881
theorem B2916749 : Blo 2303435 2916749 := bbase (se 3 (by rfl) ⟨546890, by rfl⟩ : syracuseStep 2916749 = 1093781) (by norm_num)
theorem B7777997 : Blo 2303435 7777997 := bstep (se 3 (by rfl) ⟨1458374, by rfl⟩ : syracuseStep 7777997 = 2916749) B2916749
theorem B5185331 : Blo 2303435 5185331 := bstep (se 1 (by rfl) ⟨3888998, by rfl⟩ : syracuseStep 5185331 = 7777997) B7777997
theorem B3456887 : Blo 2303435 3456887 := bstep (se 1 (by rfl) ⟨2592665, by rfl⟩ : syracuseStep 3456887 = 5185331) B5185331
theorem B2304591 : Blo 2303435 2304591 := bstep (se 1 (by rfl) ⟨1728443, by rfl⟩ : syracuseStep 2304591 = 3456887) B3456887
theorem B3456893 : Blo 2303435 3456893 := bbase (se 3 (by rfl) ⟨648167, by rfl⟩ : syracuseStep 3456893 = 1296335) (by norm_num)
theorem B2304595 : Blo 2303435 2304595 := bstep (se 1 (by rfl) ⟨1728446, by rfl⟩ : syracuseStep 2304595 = 3456893) B3456893
theorem B5185349 : Blo 2303435 5185349 := bbase (se 4 (by rfl) ⟨486126, by rfl⟩ : syracuseStep 5185349 = 972253) (by norm_num)
theorem B3456899 : Blo 2303435 3456899 := bstep (se 1 (by rfl) ⟨2592674, by rfl⟩ : syracuseStep 3456899 = 5185349) B5185349
theorem B2304599 : Blo 2303435 2304599 := bstep (se 1 (by rfl) ⟨1728449, by rfl⟩ : syracuseStep 2304599 = 3456899) B3456899
theorem B4152973 : Blo 2303435 4152973 := bbase (se 3 (by rfl) ⟨778682, by rfl⟩ : syracuseStep 4152973 = 1557365) (by norm_num)
theorem B5537297 : Blo 2303435 5537297 := bstep (se 2 (by rfl) ⟨2076486, by rfl⟩ : syracuseStep 5537297 = 4152973) B4152973
theorem B3691531 : Blo 2303435 3691531 := bstep (se 1 (by rfl) ⟨2768648, by rfl⟩ : syracuseStep 3691531 = 5537297) B5537297
theorem B4922041 : Blo 2303435 4922041 := bstep (se 2 (by rfl) ⟨1845765, by rfl⟩ : syracuseStep 4922041 = 3691531) B3691531
theorem B6562721 : Blo 2303435 6562721 := bstep (se 2 (by rfl) ⟨2461020, by rfl⟩ : syracuseStep 6562721 = 4922041) B4922041
theorem B4375147 : Blo 2303435 4375147 := bstep (se 1 (by rfl) ⟨3281360, by rfl⟩ : syracuseStep 4375147 = 6562721) B6562721
theorem B5833529 : Blo 2303435 5833529 := bstep (se 2 (by rfl) ⟨2187573, by rfl⟩ : syracuseStep 5833529 = 4375147) B4375147
theorem B3889019 : Blo 2303435 3889019 := bstep (se 1 (by rfl) ⟨2916764, by rfl⟩ : syracuseStep 3889019 = 5833529) B5833529
theorem B2592679 : Blo 2303435 2592679 := bstep (se 1 (by rfl) ⟨1944509, by rfl⟩ : syracuseStep 2592679 = 3889019) B3889019
theorem B3456905 : Blo 2303435 3456905 := bstep (se 2 (by rfl) ⟨1296339, by rfl⟩ : syracuseStep 3456905 = 2592679) B2592679
theorem B2304603 : Blo 2303435 2304603 := bstep (se 1 (by rfl) ⟨1728452, by rfl⟩ : syracuseStep 2304603 = 3456905) B3456905
theorem B11667077 : Blo 2303435 11667077 := bbase (se 4 (by rfl) ⟨1093788, by rfl⟩ : syracuseStep 11667077 = 2187577) (by norm_num)
theorem B7778051 : Blo 2303435 7778051 := bstep (se 1 (by rfl) ⟨5833538, by rfl⟩ : syracuseStep 7778051 = 11667077) B11667077
theorem B5185367 : Blo 2303435 5185367 := bstep (se 1 (by rfl) ⟨3889025, by rfl⟩ : syracuseStep 5185367 = 7778051) B7778051
theorem B3456911 : Blo 2303435 3456911 := bstep (se 1 (by rfl) ⟨2592683, by rfl⟩ : syracuseStep 3456911 = 5185367) B5185367
theorem B2304607 : Blo 2303435 2304607 := bstep (se 1 (by rfl) ⟨1728455, by rfl⟩ : syracuseStep 2304607 = 3456911) B3456911
theorem B3456917 : Blo 2303435 3456917 := bbase (se 6 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 3456917 = 162043) (by norm_num)
theorem B2304611 : Blo 2303435 2304611 := bstep (se 1 (by rfl) ⟨1728458, by rfl⟩ : syracuseStep 2304611 = 3456917) B3456917
theorem B2461033 : Blo 2303435 2461033 := bbase (se 2 (by rfl) ⟨922887, by rfl⟩ : syracuseStep 2461033 = 1845775) (by norm_num)
theorem B13125509 : Blo 2303435 13125509 := bstep (se 4 (by rfl) ⟨1230516, by rfl⟩ : syracuseStep 13125509 = 2461033) B2461033
theorem B8750339 : Blo 2303435 8750339 := bstep (se 1 (by rfl) ⟨6562754, by rfl⟩ : syracuseStep 8750339 = 13125509) B13125509
theorem B5833559 : Blo 2303435 5833559 := bstep (se 1 (by rfl) ⟨4375169, by rfl⟩ : syracuseStep 5833559 = 8750339) B8750339
theorem B3889039 : Blo 2303435 3889039 := bstep (se 1 (by rfl) ⟨2916779, by rfl⟩ : syracuseStep 3889039 = 5833559) B5833559
theorem B5185385 : Blo 2303435 5185385 := bstep (se 2 (by rfl) ⟨1944519, by rfl⟩ : syracuseStep 5185385 = 3889039) B3889039
theorem B3456923 : Blo 2303435 3456923 := bstep (se 1 (by rfl) ⟨2592692, by rfl⟩ : syracuseStep 3456923 = 5185385) B5185385
theorem B2304615 : Blo 2303435 2304615 := bstep (se 1 (by rfl) ⟨1728461, by rfl⟩ : syracuseStep 2304615 = 3456923) B3456923
theorem B2592697 : Blo 2303435 2592697 := bbase (se 2 (by rfl) ⟨972261, by rfl⟩ : syracuseStep 2592697 = 1944523) (by norm_num)
theorem B3456929 : Blo 2303435 3456929 := bstep (se 2 (by rfl) ⟨1296348, by rfl⟩ : syracuseStep 3456929 = 2592697) B2592697
theorem B2304619 : Blo 2303435 2304619 := bstep (se 1 (by rfl) ⟨1728464, by rfl⟩ : syracuseStep 2304619 = 3456929) B3456929
theorem B7383125 : Blo 2303435 7383125 := bbase (se 8 (by rfl) ⟨43260, by rfl⟩ : syracuseStep 7383125 = 86521) (by norm_num)
theorem B4922083 : Blo 2303435 4922083 := bstep (se 1 (by rfl) ⟨3691562, by rfl⟩ : syracuseStep 4922083 = 7383125) B7383125
theorem B6562777 : Blo 2303435 6562777 := bstep (se 2 (by rfl) ⟨2461041, by rfl⟩ : syracuseStep 6562777 = 4922083) B4922083
theorem B8750369 : Blo 2303435 8750369 := bstep (se 2 (by rfl) ⟨3281388, by rfl⟩ : syracuseStep 8750369 = 6562777) B6562777
theorem B5833579 : Blo 2303435 5833579 := bstep (se 1 (by rfl) ⟨4375184, by rfl⟩ : syracuseStep 5833579 = 8750369) B8750369
theorem B7778105 : Blo 2303435 7778105 := bstep (se 2 (by rfl) ⟨2916789, by rfl⟩ : syracuseStep 7778105 = 5833579) B5833579
theorem B5185403 : Blo 2303435 5185403 := bstep (se 1 (by rfl) ⟨3889052, by rfl⟩ : syracuseStep 5185403 = 7778105) B7778105
theorem B3456935 : Blo 2303435 3456935 := bstep (se 1 (by rfl) ⟨2592701, by rfl⟩ : syracuseStep 3456935 = 5185403) B5185403
theorem B2304623 : Blo 2303435 2304623 := bstep (se 1 (by rfl) ⟨1728467, by rfl⟩ : syracuseStep 2304623 = 3456935) B3456935
theorem B3456941 : Blo 2303435 3456941 := bbase (se 3 (by rfl) ⟨648176, by rfl⟩ : syracuseStep 3456941 = 1296353) (by norm_num)
theorem B2304627 : Blo 2303435 2304627 := bstep (se 1 (by rfl) ⟨1728470, by rfl⟩ : syracuseStep 2304627 = 3456941) B3456941
theorem B5185421 : Blo 2303435 5185421 := bbase (se 3 (by rfl) ⟨972266, by rfl⟩ : syracuseStep 5185421 = 1944533) (by norm_num)
theorem B3456947 : Blo 2303435 3456947 := bstep (se 1 (by rfl) ⟨2592710, by rfl⟩ : syracuseStep 3456947 = 5185421) B5185421
theorem B2304631 : Blo 2303435 2304631 := bstep (se 1 (by rfl) ⟨1728473, by rfl⟩ : syracuseStep 2304631 = 3456947) B3456947
theorem B2916805 : Blo 2303435 2916805 := bbase (se 4 (by rfl) ⟨273450, by rfl⟩ : syracuseStep 2916805 = 546901) (by norm_num)
theorem B3889073 : Blo 2303435 3889073 := bstep (se 2 (by rfl) ⟨1458402, by rfl⟩ : syracuseStep 3889073 = 2916805) B2916805
theorem B2592715 : Blo 2303435 2592715 := bstep (se 1 (by rfl) ⟨1944536, by rfl⟩ : syracuseStep 2592715 = 3889073) B3889073
theorem B3456953 : Blo 2303435 3456953 := bstep (se 2 (by rfl) ⟨1296357, by rfl⟩ : syracuseStep 3456953 = 2592715) B2592715
theorem B2304635 : Blo 2303435 2304635 := bstep (se 1 (by rfl) ⟨1728476, by rfl⟩ : syracuseStep 2304635 = 3456953) B3456953
theorem B3504125 : Blo 2303435 3504125 := bbase (se 3 (by rfl) ⟨657023, by rfl⟩ : syracuseStep 3504125 = 1314047) (by norm_num)
theorem B2336083 : Blo 2303435 2336083 := bstep (se 1 (by rfl) ⟨1752062, by rfl⟩ : syracuseStep 2336083 = 3504125) B3504125
theorem B12459109 : Blo 2303435 12459109 := bstep (se 4 (by rfl) ⟨1168041, by rfl⟩ : syracuseStep 12459109 = 2336083) B2336083
theorem B16612145 : Blo 2303435 16612145 := bstep (se 2 (by rfl) ⟨6229554, by rfl⟩ : syracuseStep 16612145 = 12459109) B12459109
theorem B11074763 : Blo 2303435 11074763 := bstep (se 1 (by rfl) ⟨8306072, by rfl⟩ : syracuseStep 11074763 = 16612145) B16612145
theorem B29532701 : Blo 2303435 29532701 := bstep (se 3 (by rfl) ⟨5537381, by rfl⟩ : syracuseStep 29532701 = 11074763) B11074763
theorem B19688467 : Blo 2303435 19688467 := bstep (se 1 (by rfl) ⟨14766350, by rfl⟩ : syracuseStep 19688467 = 29532701) B29532701
theorem B26251289 : Blo 2303435 26251289 := bstep (se 2 (by rfl) ⟨9844233, by rfl⟩ : syracuseStep 26251289 = 19688467) B19688467
theorem B17500859 : Blo 2303435 17500859 := bstep (se 1 (by rfl) ⟨13125644, by rfl⟩ : syracuseStep 17500859 = 26251289) B26251289
theorem B11667239 : Blo 2303435 11667239 := bstep (se 1 (by rfl) ⟨8750429, by rfl⟩ : syracuseStep 11667239 = 17500859) B17500859
theorem B7778159 : Blo 2303435 7778159 := bstep (se 1 (by rfl) ⟨5833619, by rfl⟩ : syracuseStep 7778159 = 11667239) B11667239
theorem B5185439 : Blo 2303435 5185439 := bstep (se 1 (by rfl) ⟨3889079, by rfl⟩ : syracuseStep 5185439 = 7778159) B7778159
theorem B3456959 : Blo 2303435 3456959 := bstep (se 1 (by rfl) ⟨2592719, by rfl⟩ : syracuseStep 3456959 = 5185439) B5185439
theorem B2304639 : Blo 2303435 2304639 := bstep (se 1 (by rfl) ⟨1728479, by rfl⟩ : syracuseStep 2304639 = 3456959) B3456959
theorem B3456965 : Blo 2303435 3456965 := bbase (se 4 (by rfl) ⟨324090, by rfl⟩ : syracuseStep 3456965 = 648181) (by norm_num)
theorem B2304643 : Blo 2303435 2304643 := bstep (se 1 (by rfl) ⟨1728482, by rfl⟩ : syracuseStep 2304643 = 3456965) B3456965
theorem B3889093 : Blo 2303435 3889093 := bbase (se 4 (by rfl) ⟨364602, by rfl⟩ : syracuseStep 3889093 = 729205) (by norm_num)
theorem B5185457 : Blo 2303435 5185457 := bstep (se 2 (by rfl) ⟨1944546, by rfl⟩ : syracuseStep 5185457 = 3889093) B3889093
theorem B3456971 : Blo 2303435 3456971 := bstep (se 1 (by rfl) ⟨2592728, by rfl⟩ : syracuseStep 3456971 = 5185457) B5185457
theorem B2304647 : Blo 2303435 2304647 := bstep (se 1 (by rfl) ⟨1728485, by rfl⟩ : syracuseStep 2304647 = 3456971) B3456971
theorem B2592733 : Blo 2303435 2592733 := bbase (se 3 (by rfl) ⟨486137, by rfl⟩ : syracuseStep 2592733 = 972275) (by norm_num)
theorem B3456977 : Blo 2303435 3456977 := bstep (se 2 (by rfl) ⟨1296366, by rfl⟩ : syracuseStep 3456977 = 2592733) B2592733
theorem B2304651 : Blo 2303435 2304651 := bstep (se 1 (by rfl) ⟨1728488, by rfl⟩ : syracuseStep 2304651 = 3456977) B3456977
theorem B7778213 : Blo 2303435 7778213 := bbase (se 4 (by rfl) ⟨729207, by rfl⟩ : syracuseStep 7778213 = 1458415) (by norm_num)
theorem B5185475 : Blo 2303435 5185475 := bstep (se 1 (by rfl) ⟨3889106, by rfl⟩ : syracuseStep 5185475 = 7778213) B7778213
theorem B3456983 : Blo 2303435 3456983 := bstep (se 1 (by rfl) ⟨2592737, by rfl⟩ : syracuseStep 3456983 = 5185475) B5185475
theorem B2304655 : Blo 2303435 2304655 := bstep (se 1 (by rfl) ⟨1728491, by rfl⟩ : syracuseStep 2304655 = 3456983) B3456983
theorem B3456989 : Blo 2303435 3456989 := bbase (se 3 (by rfl) ⟨648185, by rfl⟩ : syracuseStep 3456989 = 1296371) (by norm_num)
theorem B2304659 : Blo 2303435 2304659 := bstep (se 1 (by rfl) ⟨1728494, by rfl⟩ : syracuseStep 2304659 = 3456989) B3456989
theorem B5185493 : Blo 2303435 5185493 := bbase (se 7 (by rfl) ⟨60767, by rfl⟩ : syracuseStep 5185493 = 121535) (by norm_num)
theorem B3456995 : Blo 2303435 3456995 := bstep (se 1 (by rfl) ⟨2592746, by rfl⟩ : syracuseStep 3456995 = 5185493) B5185493
theorem B2304663 : Blo 2303435 2304663 := bstep (se 1 (by rfl) ⟨1728497, by rfl⟩ : syracuseStep 2304663 = 3456995) B3456995
theorem B2768725 : Blo 2303435 2768725 := bbase (se 9 (by rfl) ⟨8111, by rfl⟩ : syracuseStep 2768725 = 16223) (by norm_num)
theorem B14766533 : Blo 2303435 14766533 := bstep (se 4 (by rfl) ⟨1384362, by rfl⟩ : syracuseStep 14766533 = 2768725) B2768725
theorem B9844355 : Blo 2303435 9844355 := bstep (se 1 (by rfl) ⟨7383266, by rfl⟩ : syracuseStep 9844355 = 14766533) B14766533
theorem B6562903 : Blo 2303435 6562903 := bstep (se 1 (by rfl) ⟨4922177, by rfl⟩ : syracuseStep 6562903 = 9844355) B9844355
theorem B8750537 : Blo 2303435 8750537 := bstep (se 2 (by rfl) ⟨3281451, by rfl⟩ : syracuseStep 8750537 = 6562903) B6562903
theorem B5833691 : Blo 2303435 5833691 := bstep (se 1 (by rfl) ⟨4375268, by rfl⟩ : syracuseStep 5833691 = 8750537) B8750537
theorem B3889127 : Blo 2303435 3889127 := bstep (se 1 (by rfl) ⟨2916845, by rfl⟩ : syracuseStep 3889127 = 5833691) B5833691
theorem B2592751 : Blo 2303435 2592751 := bstep (se 1 (by rfl) ⟨1944563, by rfl⟩ : syracuseStep 2592751 = 3889127) B3889127
theorem B3457001 : Blo 2303435 3457001 := bstep (se 2 (by rfl) ⟨1296375, by rfl⟩ : syracuseStep 3457001 = 2592751) B2592751
theorem B2304667 : Blo 2303435 2304667 := bstep (se 1 (by rfl) ⟨1728500, by rfl⟩ : syracuseStep 2304667 = 3457001) B3457001
theorem B3114821 : Blo 2303435 3114821 := bbase (se 4 (by rfl) ⟨292014, by rfl⟩ : syracuseStep 3114821 = 584029) (by norm_num)
theorem B8306189 : Blo 2303435 8306189 := bstep (se 3 (by rfl) ⟨1557410, by rfl⟩ : syracuseStep 8306189 = 3114821) B3114821
theorem B5537459 : Blo 2303435 5537459 := bstep (se 1 (by rfl) ⟨4153094, by rfl⟩ : syracuseStep 5537459 = 8306189) B8306189
theorem B3691639 : Blo 2303435 3691639 := bstep (se 1 (by rfl) ⟨2768729, by rfl⟩ : syracuseStep 3691639 = 5537459) B5537459
theorem B19688741 : Blo 2303435 19688741 := bstep (se 4 (by rfl) ⟨1845819, by rfl⟩ : syracuseStep 19688741 = 3691639) B3691639
theorem B13125827 : Blo 2303435 13125827 := bstep (se 1 (by rfl) ⟨9844370, by rfl⟩ : syracuseStep 13125827 = 19688741) B19688741
theorem B8750551 : Blo 2303435 8750551 := bstep (se 1 (by rfl) ⟨6562913, by rfl⟩ : syracuseStep 8750551 = 13125827) B13125827
theorem B11667401 : Blo 2303435 11667401 := bstep (se 2 (by rfl) ⟨4375275, by rfl⟩ : syracuseStep 11667401 = 8750551) B8750551
theorem B7778267 : Blo 2303435 7778267 := bstep (se 1 (by rfl) ⟨5833700, by rfl⟩ : syracuseStep 7778267 = 11667401) B11667401
theorem B5185511 : Blo 2303435 5185511 := bstep (se 1 (by rfl) ⟨3889133, by rfl⟩ : syracuseStep 5185511 = 7778267) B7778267
theorem B3457007 : Blo 2303435 3457007 := bstep (se 1 (by rfl) ⟨2592755, by rfl⟩ : syracuseStep 3457007 = 5185511) B5185511
theorem B2304671 : Blo 2303435 2304671 := bstep (se 1 (by rfl) ⟨1728503, by rfl⟩ : syracuseStep 2304671 = 3457007) B3457007
theorem B3457013 : Blo 2303435 3457013 := bbase (se 5 (by rfl) ⟨162047, by rfl⟩ : syracuseStep 3457013 = 324095) (by norm_num)
theorem B2304675 : Blo 2303435 2304675 := bstep (se 1 (by rfl) ⟨1728506, by rfl⟩ : syracuseStep 2304675 = 3457013) B3457013
theorem B7008373 : Blo 2303435 7008373 := bbase (se 5 (by rfl) ⟨328517, by rfl⟩ : syracuseStep 7008373 = 657035) (by norm_num)
theorem B9344497 : Blo 2303435 9344497 := bstep (se 2 (by rfl) ⟨3504186, by rfl⟩ : syracuseStep 9344497 = 7008373) B7008373
theorem B12459329 : Blo 2303435 12459329 := bstep (se 2 (by rfl) ⟨4672248, by rfl⟩ : syracuseStep 12459329 = 9344497) B9344497
theorem B8306219 : Blo 2303435 8306219 := bstep (se 1 (by rfl) ⟨6229664, by rfl⟩ : syracuseStep 8306219 = 12459329) B12459329
theorem B5537479 : Blo 2303435 5537479 := bstep (se 1 (by rfl) ⟨4153109, by rfl⟩ : syracuseStep 5537479 = 8306219) B8306219
theorem B7383305 : Blo 2303435 7383305 := bstep (se 2 (by rfl) ⟨2768739, by rfl⟩ : syracuseStep 7383305 = 5537479) B5537479
theorem B4922203 : Blo 2303435 4922203 := bstep (se 1 (by rfl) ⟨3691652, by rfl⟩ : syracuseStep 4922203 = 7383305) B7383305
theorem B6562937 : Blo 2303435 6562937 := bstep (se 2 (by rfl) ⟨2461101, by rfl⟩ : syracuseStep 6562937 = 4922203) B4922203
theorem B4375291 : Blo 2303435 4375291 := bstep (se 1 (by rfl) ⟨3281468, by rfl⟩ : syracuseStep 4375291 = 6562937) B6562937
theorem B5833721 : Blo 2303435 5833721 := bstep (se 2 (by rfl) ⟨2187645, by rfl⟩ : syracuseStep 5833721 = 4375291) B4375291
theorem B3889147 : Blo 2303435 3889147 := bstep (se 1 (by rfl) ⟨2916860, by rfl⟩ : syracuseStep 3889147 = 5833721) B5833721
theorem B5185529 : Blo 2303435 5185529 := bstep (se 2 (by rfl) ⟨1944573, by rfl⟩ : syracuseStep 5185529 = 3889147) B3889147
theorem B3457019 : Blo 2303435 3457019 := bstep (se 1 (by rfl) ⟨2592764, by rfl⟩ : syracuseStep 3457019 = 5185529) B5185529
theorem B2304679 : Blo 2303435 2304679 := bstep (se 1 (by rfl) ⟨1728509, by rfl⟩ : syracuseStep 2304679 = 3457019) B3457019
theorem B2592769 : Blo 2303435 2592769 := bbase (se 2 (by rfl) ⟨972288, by rfl⟩ : syracuseStep 2592769 = 1944577) (by norm_num)
theorem B3457025 : Blo 2303435 3457025 := bstep (se 2 (by rfl) ⟨1296384, by rfl⟩ : syracuseStep 3457025 = 2592769) B2592769
theorem B2304683 : Blo 2303435 2304683 := bstep (se 1 (by rfl) ⟨1728512, by rfl⟩ : syracuseStep 2304683 = 3457025) B3457025
theorem B5833741 : Blo 2303435 5833741 := bbase (se 3 (by rfl) ⟨1093826, by rfl⟩ : syracuseStep 5833741 = 2187653) (by norm_num)
theorem B7778321 : Blo 2303435 7778321 := bstep (se 2 (by rfl) ⟨2916870, by rfl⟩ : syracuseStep 7778321 = 5833741) B5833741
theorem B5185547 : Blo 2303435 5185547 := bstep (se 1 (by rfl) ⟨3889160, by rfl⟩ : syracuseStep 5185547 = 7778321) B7778321
theorem B3457031 : Blo 2303435 3457031 := bstep (se 1 (by rfl) ⟨2592773, by rfl⟩ : syracuseStep 3457031 = 5185547) B5185547
theorem B2304687 : Blo 2303435 2304687 := bstep (se 1 (by rfl) ⟨1728515, by rfl⟩ : syracuseStep 2304687 = 3457031) B3457031
theorem B3457037 : Blo 2303435 3457037 := bbase (se 3 (by rfl) ⟨648194, by rfl⟩ : syracuseStep 3457037 = 1296389) (by norm_num)
theorem B2304691 : Blo 2303435 2304691 := bstep (se 1 (by rfl) ⟨1728518, by rfl⟩ : syracuseStep 2304691 = 3457037) B3457037
theorem B5185565 : Blo 2303435 5185565 := bbase (se 3 (by rfl) ⟨972293, by rfl⟩ : syracuseStep 5185565 = 1944587) (by norm_num)
theorem B3457043 : Blo 2303435 3457043 := bstep (se 1 (by rfl) ⟨2592782, by rfl⟩ : syracuseStep 3457043 = 5185565) B5185565
theorem B2304695 : Blo 2303435 2304695 := bstep (se 1 (by rfl) ⟨1728521, by rfl⟩ : syracuseStep 2304695 = 3457043) B3457043
theorem B3889181 : Blo 2303435 3889181 := bbase (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) (by norm_num)
theorem B2592787 : Blo 2303435 2592787 := bstep (se 1 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 2592787 = 3889181) B3889181
theorem B3457049 : Blo 2303435 3457049 := bstep (se 2 (by rfl) ⟨1296393, by rfl⟩ : syracuseStep 3457049 = 2592787) B2592787
theorem B2304699 : Blo 2303435 2304699 := bstep (se 1 (by rfl) ⟨1728524, by rfl⟩ : syracuseStep 2304699 = 3457049) B3457049
theorem B5994053 : Blo 2303435 5994053 := bbase (se 4 (by rfl) ⟨561942, by rfl⟩ : syracuseStep 5994053 = 1123885) (by norm_num)
theorem B3996035 : Blo 2303435 3996035 := bstep (se 1 (by rfl) ⟨2997026, by rfl⟩ : syracuseStep 3996035 = 5994053) B5994053
theorem B170497493 : Blo 2303435 170497493 := bstep (se 7 (by rfl) ⟨1998017, by rfl⟩ : syracuseStep 170497493 = 3996035) B3996035
theorem B113664995 : Blo 2303435 113664995 := bstep (se 1 (by rfl) ⟨85248746, by rfl⟩ : syracuseStep 113664995 = 170497493) B170497493
theorem B75776663 : Blo 2303435 75776663 := bstep (se 1 (by rfl) ⟨56832497, by rfl⟩ : syracuseStep 75776663 = 113664995) B113664995
theorem B50517775 : Blo 2303435 50517775 := bstep (se 1 (by rfl) ⟨37888331, by rfl⟩ : syracuseStep 50517775 = 75776663) B75776663
theorem B269428133 : Blo 2303435 269428133 := bstep (se 4 (by rfl) ⟨25258887, by rfl⟩ : syracuseStep 269428133 = 50517775) B50517775
theorem B179618755 : Blo 2303435 179618755 := bstep (se 1 (by rfl) ⟨134714066, by rfl⟩ : syracuseStep 179618755 = 269428133) B269428133
theorem B239491673 : Blo 2303435 239491673 := bstep (se 2 (by rfl) ⟨89809377, by rfl⟩ : syracuseStep 239491673 = 179618755) B179618755
theorem B159661115 : Blo 2303435 159661115 := bstep (se 1 (by rfl) ⟨119745836, by rfl⟩ : syracuseStep 159661115 = 239491673) B239491673
theorem B106440743 : Blo 2303435 106440743 := bstep (se 1 (by rfl) ⟨79830557, by rfl⟩ : syracuseStep 106440743 = 159661115) B159661115
theorem B283841981 : Blo 2303435 283841981 := bstep (se 3 (by rfl) ⟨53220371, by rfl⟩ : syracuseStep 283841981 = 106440743) B106440743
theorem B189227987 : Blo 2303435 189227987 := bstep (se 1 (by rfl) ⟨141920990, by rfl⟩ : syracuseStep 189227987 = 283841981) B283841981
theorem B126151991 : Blo 2303435 126151991 := bstep (se 1 (by rfl) ⟨94613993, by rfl⟩ : syracuseStep 126151991 = 189227987) B189227987
theorem B84101327 : Blo 2303435 84101327 := bstep (se 1 (by rfl) ⟨63075995, by rfl⟩ : syracuseStep 84101327 = 126151991) B126151991
theorem B56067551 : Blo 2303435 56067551 := bstep (se 1 (by rfl) ⟨42050663, by rfl⟩ : syracuseStep 56067551 = 84101327) B84101327
theorem B37378367 : Blo 2303435 37378367 := bstep (se 1 (by rfl) ⟨28033775, by rfl⟩ : syracuseStep 37378367 = 56067551) B56067551
theorem B24918911 : Blo 2303435 24918911 := bstep (se 1 (by rfl) ⟨18689183, by rfl⟩ : syracuseStep 24918911 = 37378367) B37378367
theorem B16612607 : Blo 2303435 16612607 := bstep (se 1 (by rfl) ⟨12459455, by rfl⟩ : syracuseStep 16612607 = 24918911) B24918911
theorem B11075071 : Blo 2303435 11075071 := bstep (se 1 (by rfl) ⟨8306303, by rfl⟩ : syracuseStep 11075071 = 16612607) B16612607
theorem B14766761 : Blo 2303435 14766761 := bstep (se 2 (by rfl) ⟨5537535, by rfl⟩ : syracuseStep 14766761 = 11075071) B11075071
theorem B9844507 : Blo 2303435 9844507 := bstep (se 1 (by rfl) ⟨7383380, by rfl⟩ : syracuseStep 9844507 = 14766761) B14766761
theorem B13126009 : Blo 2303435 13126009 := bstep (se 2 (by rfl) ⟨4922253, by rfl⟩ : syracuseStep 13126009 = 9844507) B9844507
theorem B17501345 : Blo 2303435 17501345 := bstep (se 2 (by rfl) ⟨6563004, by rfl⟩ : syracuseStep 17501345 = 13126009) B13126009
theorem B11667563 : Blo 2303435 11667563 := bstep (se 1 (by rfl) ⟨8750672, by rfl⟩ : syracuseStep 11667563 = 17501345) B17501345
theorem B7778375 : Blo 2303435 7778375 := bstep (se 1 (by rfl) ⟨5833781, by rfl⟩ : syracuseStep 7778375 = 11667563) B11667563
theorem B5185583 : Blo 2303435 5185583 := bstep (se 1 (by rfl) ⟨3889187, by rfl⟩ : syracuseStep 5185583 = 7778375) B7778375
theorem B3457055 : Blo 2303435 3457055 := bstep (se 1 (by rfl) ⟨2592791, by rfl⟩ : syracuseStep 3457055 = 5185583) B5185583
theorem B2304703 : Blo 2303435 2304703 := bstep (se 1 (by rfl) ⟨1728527, by rfl⟩ : syracuseStep 2304703 = 3457055) B3457055
theorem B3457061 : Blo 2303435 3457061 := bbase (se 4 (by rfl) ⟨324099, by rfl⟩ : syracuseStep 3457061 = 648199) (by norm_num)
theorem B2304707 : Blo 2303435 2304707 := bstep (se 1 (by rfl) ⟨1728530, by rfl⟩ : syracuseStep 2304707 = 3457061) B3457061
theorem B2916901 : Blo 2303435 2916901 := bbase (se 4 (by rfl) ⟨273459, by rfl⟩ : syracuseStep 2916901 = 546919) (by norm_num)
theorem B3889201 : Blo 2303435 3889201 := bstep (se 2 (by rfl) ⟨1458450, by rfl⟩ : syracuseStep 3889201 = 2916901) B2916901
theorem B5185601 : Blo 2303435 5185601 := bstep (se 2 (by rfl) ⟨1944600, by rfl⟩ : syracuseStep 5185601 = 3889201) B3889201
theorem B3457067 : Blo 2303435 3457067 := bstep (se 1 (by rfl) ⟨2592800, by rfl⟩ : syracuseStep 3457067 = 5185601) B5185601
theorem B2304711 : Blo 2303435 2304711 := bstep (se 1 (by rfl) ⟨1728533, by rfl⟩ : syracuseStep 2304711 = 3457067) B3457067
theorem B2592805 : Blo 2303435 2592805 := bbase (se 4 (by rfl) ⟨243075, by rfl⟩ : syracuseStep 2592805 = 486151) (by norm_num)
theorem B3457073 : Blo 2303435 3457073 := bstep (se 2 (by rfl) ⟨1296402, by rfl⟩ : syracuseStep 3457073 = 2592805) B2592805
theorem B2304715 : Blo 2303435 2304715 := bstep (se 1 (by rfl) ⟨1728536, by rfl⟩ : syracuseStep 2304715 = 3457073) B3457073
theorem B2956709 : Blo 2303435 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B7884557 : Blo 2303435 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B5256371 : Blo 2303435 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B14016989 : Blo 2303435 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B9344659 : Blo 2303435 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B12459545 : Blo 2303435 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B8306363 : Blo 2303435 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B5537575 : Blo 2303435 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B7383433 : Blo 2303435 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B9844577 : Blo 2303435 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B6563051 : Blo 2303435 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B4375367 : Blo 2303435 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B2916911 : Blo 2303435 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B7778429 : Blo 2303435 7778429 := bstep (se 3 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 7778429 = 2916911) B2916911
theorem B5185619 : Blo 2303435 5185619 := bstep (se 1 (by rfl) ⟨3889214, by rfl⟩ : syracuseStep 5185619 = 7778429) B7778429
theorem B3457079 : Blo 2303435 3457079 := bstep (se 1 (by rfl) ⟨2592809, by rfl⟩ : syracuseStep 3457079 = 5185619) B5185619
theorem B2304719 : Blo 2303435 2304719 := bstep (se 1 (by rfl) ⟨1728539, by rfl⟩ : syracuseStep 2304719 = 3457079) B3457079
theorem B3457085 : Blo 2303435 3457085 := bbase (se 3 (by rfl) ⟨648203, by rfl⟩ : syracuseStep 3457085 = 1296407) (by norm_num)
theorem B2304723 : Blo 2303435 2304723 := bstep (se 1 (by rfl) ⟨1728542, by rfl⟩ : syracuseStep 2304723 = 3457085) B3457085
theorem B5185637 : Blo 2303435 5185637 := bbase (se 4 (by rfl) ⟨486153, by rfl⟩ : syracuseStep 5185637 = 972307) (by norm_num)
theorem B3457091 : Blo 2303435 3457091 := bstep (se 1 (by rfl) ⟨2592818, by rfl⟩ : syracuseStep 3457091 = 5185637) B5185637
theorem B2304727 : Blo 2303435 2304727 := bstep (se 1 (by rfl) ⟨1728545, by rfl⟩ : syracuseStep 2304727 = 3457091) B3457091
theorem B5833853 : Blo 2303435 5833853 := bbase (se 3 (by rfl) ⟨1093847, by rfl⟩ : syracuseStep 5833853 = 2187695) (by norm_num)
theorem B3889235 : Blo 2303435 3889235 := bstep (se 1 (by rfl) ⟨2916926, by rfl⟩ : syracuseStep 3889235 = 5833853) B5833853
theorem B2592823 : Blo 2303435 2592823 := bstep (se 1 (by rfl) ⟨1944617, by rfl⟩ : syracuseStep 2592823 = 3889235) B3889235
theorem B3457097 : Blo 2303435 3457097 := bstep (se 2 (by rfl) ⟨1296411, by rfl⟩ : syracuseStep 3457097 = 2592823) B2592823
theorem B2304731 : Blo 2303435 2304731 := bstep (se 1 (by rfl) ⟨1728548, by rfl⟩ : syracuseStep 2304731 = 3457097) B3457097
theorem B4375397 : Blo 2303435 4375397 := bbase (se 4 (by rfl) ⟨410193, by rfl⟩ : syracuseStep 4375397 = 820387) (by norm_num)
theorem B11667725 : Blo 2303435 11667725 := bstep (se 3 (by rfl) ⟨2187698, by rfl⟩ : syracuseStep 11667725 = 4375397) B4375397
theorem B7778483 : Blo 2303435 7778483 := bstep (se 1 (by rfl) ⟨5833862, by rfl⟩ : syracuseStep 7778483 = 11667725) B11667725
theorem B5185655 : Blo 2303435 5185655 := bstep (se 1 (by rfl) ⟨3889241, by rfl⟩ : syracuseStep 5185655 = 7778483) B7778483
theorem B3457103 : Blo 2303435 3457103 := bstep (se 1 (by rfl) ⟨2592827, by rfl⟩ : syracuseStep 3457103 = 5185655) B5185655
theorem B2304735 : Blo 2303435 2304735 := bstep (se 1 (by rfl) ⟨1728551, by rfl⟩ : syracuseStep 2304735 = 3457103) B3457103
theorem B3457109 : Blo 2303435 3457109 := bbase (se 8 (by rfl) ⟨20256, by rfl⟩ : syracuseStep 3457109 = 40513) (by norm_num)
theorem B2304739 : Blo 2303435 2304739 := bstep (se 1 (by rfl) ⟨1728554, by rfl⟩ : syracuseStep 2304739 = 3457109) B3457109
theorem B9978997 : Blo 2303435 9978997 := bbase (se 5 (by rfl) ⟨467765, by rfl⟩ : syracuseStep 9978997 = 935531) (by norm_num)
theorem B13305329 : Blo 2303435 13305329 := bstep (se 2 (by rfl) ⟨4989498, by rfl⟩ : syracuseStep 13305329 = 9978997) B9978997
theorem B8870219 : Blo 2303435 8870219 := bstep (se 1 (by rfl) ⟨6652664, by rfl⟩ : syracuseStep 8870219 = 13305329) B13305329
theorem B5913479 : Blo 2303435 5913479 := bstep (se 1 (by rfl) ⟨4435109, by rfl⟩ : syracuseStep 5913479 = 8870219) B8870219
theorem B3942319 : Blo 2303435 3942319 := bstep (se 1 (by rfl) ⟨2956739, by rfl⟩ : syracuseStep 3942319 = 5913479) B5913479
theorem B5256425 : Blo 2303435 5256425 := bstep (se 2 (by rfl) ⟨1971159, by rfl⟩ : syracuseStep 5256425 = 3942319) B3942319
theorem B14017133 : Blo 2303435 14017133 := bstep (se 3 (by rfl) ⟨2628212, by rfl⟩ : syracuseStep 14017133 = 5256425) B5256425
theorem B9344755 : Blo 2303435 9344755 := bstep (se 1 (by rfl) ⟨7008566, by rfl⟩ : syracuseStep 9344755 = 14017133) B14017133
theorem B12459673 : Blo 2303435 12459673 := bstep (se 2 (by rfl) ⟨4672377, by rfl⟩ : syracuseStep 12459673 = 9344755) B9344755
theorem B16612897 : Blo 2303435 16612897 := bstep (se 2 (by rfl) ⟨6229836, by rfl⟩ : syracuseStep 16612897 = 12459673) B12459673
theorem B22150529 : Blo 2303435 22150529 := bstep (se 2 (by rfl) ⟨8306448, by rfl⟩ : syracuseStep 22150529 = 16612897) B16612897
theorem B14767019 : Blo 2303435 14767019 := bstep (se 1 (by rfl) ⟨11075264, by rfl⟩ : syracuseStep 14767019 = 22150529) B22150529
theorem B9844679 : Blo 2303435 9844679 := bstep (se 1 (by rfl) ⟨7383509, by rfl⟩ : syracuseStep 9844679 = 14767019) B14767019
theorem B6563119 : Blo 2303435 6563119 := bstep (se 1 (by rfl) ⟨4922339, by rfl⟩ : syracuseStep 6563119 = 9844679) B9844679
theorem B8750825 : Blo 2303435 8750825 := bstep (se 2 (by rfl) ⟨3281559, by rfl⟩ : syracuseStep 8750825 = 6563119) B6563119
theorem B5833883 : Blo 2303435 5833883 := bstep (se 1 (by rfl) ⟨4375412, by rfl⟩ : syracuseStep 5833883 = 8750825) B8750825
theorem B3889255 : Blo 2303435 3889255 := bstep (se 1 (by rfl) ⟨2916941, by rfl⟩ : syracuseStep 3889255 = 5833883) B5833883
theorem B5185673 : Blo 2303435 5185673 := bstep (se 2 (by rfl) ⟨1944627, by rfl⟩ : syracuseStep 5185673 = 3889255) B3889255
theorem B3457115 : Blo 2303435 3457115 := bstep (se 1 (by rfl) ⟨2592836, by rfl⟩ : syracuseStep 3457115 = 5185673) B5185673
theorem B2304743 : Blo 2303435 2304743 := bstep (se 1 (by rfl) ⟨1728557, by rfl⟩ : syracuseStep 2304743 = 3457115) B3457115
theorem B2592841 : Blo 2303435 2592841 := bbase (se 2 (by rfl) ⟨972315, by rfl⟩ : syracuseStep 2592841 = 1944631) (by norm_num)
theorem B3457121 : Blo 2303435 3457121 := bstep (se 2 (by rfl) ⟨1296420, by rfl⟩ : syracuseStep 3457121 = 2592841) B2592841
theorem B2304747 : Blo 2303435 2304747 := bstep (se 1 (by rfl) ⟨1728560, by rfl⟩ : syracuseStep 2304747 = 3457121) B3457121
theorem B2336197 : Blo 2303435 2336197 := bbase (se 4 (by rfl) ⟨219018, by rfl⟩ : syracuseStep 2336197 = 438037) (by norm_num)
theorem B3114929 : Blo 2303435 3114929 := bstep (se 2 (by rfl) ⟨1168098, by rfl⟩ : syracuseStep 3114929 = 2336197) B2336197
theorem B8306477 : Blo 2303435 8306477 := bstep (se 3 (by rfl) ⟨1557464, by rfl⟩ : syracuseStep 8306477 = 3114929) B3114929
theorem B5537651 : Blo 2303435 5537651 := bstep (se 1 (by rfl) ⟨4153238, by rfl⟩ : syracuseStep 5537651 = 8306477) B8306477
theorem B14767069 : Blo 2303435 14767069 := bstep (se 3 (by rfl) ⟨2768825, by rfl⟩ : syracuseStep 14767069 = 5537651) B5537651
theorem B19689425 : Blo 2303435 19689425 := bstep (se 2 (by rfl) ⟨7383534, by rfl⟩ : syracuseStep 19689425 = 14767069) B14767069
theorem B13126283 : Blo 2303435 13126283 := bstep (se 1 (by rfl) ⟨9844712, by rfl⟩ : syracuseStep 13126283 = 19689425) B19689425
theorem B8750855 : Blo 2303435 8750855 := bstep (se 1 (by rfl) ⟨6563141, by rfl⟩ : syracuseStep 8750855 = 13126283) B13126283
theorem B5833903 : Blo 2303435 5833903 := bstep (se 1 (by rfl) ⟨4375427, by rfl⟩ : syracuseStep 5833903 = 8750855) B8750855
theorem B7778537 : Blo 2303435 7778537 := bstep (se 2 (by rfl) ⟨2916951, by rfl⟩ : syracuseStep 7778537 = 5833903) B5833903
theorem B5185691 : Blo 2303435 5185691 := bstep (se 1 (by rfl) ⟨3889268, by rfl⟩ : syracuseStep 5185691 = 7778537) B7778537
theorem B3457127 : Blo 2303435 3457127 := bstep (se 1 (by rfl) ⟨2592845, by rfl⟩ : syracuseStep 3457127 = 5185691) B5185691
theorem B2304751 : Blo 2303435 2304751 := bstep (se 1 (by rfl) ⟨1728563, by rfl⟩ : syracuseStep 2304751 = 3457127) B3457127
theorem B3457133 : Blo 2303435 3457133 := bbase (se 3 (by rfl) ⟨648212, by rfl⟩ : syracuseStep 3457133 = 1296425) (by norm_num)
theorem B2304755 : Blo 2303435 2304755 := bstep (se 1 (by rfl) ⟨1728566, by rfl⟩ : syracuseStep 2304755 = 3457133) B3457133
theorem B5185709 : Blo 2303435 5185709 := bbase (se 3 (by rfl) ⟨972320, by rfl⟩ : syracuseStep 5185709 = 1944641) (by norm_num)
theorem B3457139 : Blo 2303435 3457139 := bstep (se 1 (by rfl) ⟨2592854, by rfl⟩ : syracuseStep 3457139 = 5185709) B5185709
theorem B2304759 : Blo 2303435 2304759 := bstep (se 1 (by rfl) ⟨1728569, by rfl⟩ : syracuseStep 2304759 = 3457139) B3457139
theorem B16613045 : Blo 2303435 16613045 := bbase (se 5 (by rfl) ⟨778736, by rfl⟩ : syracuseStep 16613045 = 1557473) (by norm_num)
theorem B11075363 : Blo 2303435 11075363 := bstep (se 1 (by rfl) ⟨8306522, by rfl⟩ : syracuseStep 11075363 = 16613045) B16613045
theorem B7383575 : Blo 2303435 7383575 := bstep (se 1 (by rfl) ⟨5537681, by rfl⟩ : syracuseStep 7383575 = 11075363) B11075363
theorem B4922383 : Blo 2303435 4922383 := bstep (se 1 (by rfl) ⟨3691787, by rfl⟩ : syracuseStep 4922383 = 7383575) B7383575
theorem B6563177 : Blo 2303435 6563177 := bstep (se 2 (by rfl) ⟨2461191, by rfl⟩ : syracuseStep 6563177 = 4922383) B4922383
theorem B4375451 : Blo 2303435 4375451 := bstep (se 1 (by rfl) ⟨3281588, by rfl⟩ : syracuseStep 4375451 = 6563177) B6563177
theorem B2916967 : Blo 2303435 2916967 := bstep (se 1 (by rfl) ⟨2187725, by rfl⟩ : syracuseStep 2916967 = 4375451) B4375451
theorem B3889289 : Blo 2303435 3889289 := bstep (se 2 (by rfl) ⟨1458483, by rfl⟩ : syracuseStep 3889289 = 2916967) B2916967
theorem B2592859 : Blo 2303435 2592859 := bstep (se 1 (by rfl) ⟨1944644, by rfl⟩ : syracuseStep 2592859 = 3889289) B3889289
theorem B3457145 : Blo 2303435 3457145 := bstep (se 2 (by rfl) ⟨1296429, by rfl⟩ : syracuseStep 3457145 = 2592859) B2592859
theorem B2304763 : Blo 2303435 2304763 := bstep (se 1 (by rfl) ⟨1728572, by rfl⟩ : syracuseStep 2304763 = 3457145) B3457145
theorem B2336213 : Blo 2303435 2336213 := bbase (se 7 (by rfl) ⟨27377, by rfl⟩ : syracuseStep 2336213 = 54755) (by norm_num)
theorem B6229901 : Blo 2303435 6229901 := bstep (se 3 (by rfl) ⟨1168106, by rfl⟩ : syracuseStep 6229901 = 2336213) B2336213
theorem B4153267 : Blo 2303435 4153267 := bstep (se 1 (by rfl) ⟨3114950, by rfl⟩ : syracuseStep 4153267 = 6229901) B6229901
theorem B5537689 : Blo 2303435 5537689 := bstep (se 2 (by rfl) ⟨2076633, by rfl⟩ : syracuseStep 5537689 = 4153267) B4153267
theorem B29534341 : Blo 2303435 29534341 := bstep (se 4 (by rfl) ⟨2768844, by rfl⟩ : syracuseStep 29534341 = 5537689) B5537689
theorem B39379121 : Blo 2303435 39379121 := bstep (se 2 (by rfl) ⟨14767170, by rfl⟩ : syracuseStep 39379121 = 29534341) B29534341
theorem B26252747 : Blo 2303435 26252747 := bstep (se 1 (by rfl) ⟨19689560, by rfl⟩ : syracuseStep 26252747 = 39379121) B39379121
theorem B17501831 : Blo 2303435 17501831 := bstep (se 1 (by rfl) ⟨13126373, by rfl⟩ : syracuseStep 17501831 = 26252747) B26252747
theorem B11667887 : Blo 2303435 11667887 := bstep (se 1 (by rfl) ⟨8750915, by rfl⟩ : syracuseStep 11667887 = 17501831) B17501831
theorem B7778591 : Blo 2303435 7778591 := bstep (se 1 (by rfl) ⟨5833943, by rfl⟩ : syracuseStep 7778591 = 11667887) B11667887
theorem B5185727 : Blo 2303435 5185727 := bstep (se 1 (by rfl) ⟨3889295, by rfl⟩ : syracuseStep 5185727 = 7778591) B7778591
theorem B3457151 : Blo 2303435 3457151 := bstep (se 1 (by rfl) ⟨2592863, by rfl⟩ : syracuseStep 3457151 = 5185727) B5185727
theorem B2304767 : Blo 2303435 2304767 := bstep (se 1 (by rfl) ⟨1728575, by rfl⟩ : syracuseStep 2304767 = 3457151) B3457151
theorem B3457157 : Blo 2303435 3457157 := bbase (se 4 (by rfl) ⟨324108, by rfl⟩ : syracuseStep 3457157 = 648217) (by norm_num)
theorem B2304771 : Blo 2303435 2304771 := bstep (se 1 (by rfl) ⟨1728578, by rfl⟩ : syracuseStep 2304771 = 3457157) B3457157
theorem B3889309 : Blo 2303435 3889309 := bbase (se 3 (by rfl) ⟨729245, by rfl⟩ : syracuseStep 3889309 = 1458491) (by norm_num)
theorem B5185745 : Blo 2303435 5185745 := bstep (se 2 (by rfl) ⟨1944654, by rfl⟩ : syracuseStep 5185745 = 3889309) B3889309
theorem B3457163 : Blo 2303435 3457163 := bstep (se 1 (by rfl) ⟨2592872, by rfl⟩ : syracuseStep 3457163 = 5185745) B5185745
theorem B2304775 : Blo 2303435 2304775 := bstep (se 1 (by rfl) ⟨1728581, by rfl⟩ : syracuseStep 2304775 = 3457163) B3457163
theorem B2592877 : Blo 2303435 2592877 := bbase (se 3 (by rfl) ⟨486164, by rfl⟩ : syracuseStep 2592877 = 972329) (by norm_num)
theorem B3457169 : Blo 2303435 3457169 := bstep (se 2 (by rfl) ⟨1296438, by rfl⟩ : syracuseStep 3457169 = 2592877) B2592877
theorem B2304779 : Blo 2303435 2304779 := bstep (se 1 (by rfl) ⟨1728584, by rfl⟩ : syracuseStep 2304779 = 3457169) B3457169
theorem B7778645 : Blo 2303435 7778645 := bbase (se 10 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 7778645 = 22789) (by norm_num)
theorem B5185763 : Blo 2303435 5185763 := bstep (se 1 (by rfl) ⟨3889322, by rfl⟩ : syracuseStep 5185763 = 7778645) B7778645
theorem B3457175 : Blo 2303435 3457175 := bstep (se 1 (by rfl) ⟨2592881, by rfl⟩ : syracuseStep 3457175 = 5185763) B5185763
theorem B2304783 : Blo 2303435 2304783 := bstep (se 1 (by rfl) ⟨1728587, by rfl⟩ : syracuseStep 2304783 = 3457175) B3457175
theorem B3457181 : Blo 2303435 3457181 := bbase (se 3 (by rfl) ⟨648221, by rfl⟩ : syracuseStep 3457181 = 1296443) (by norm_num)
theorem B2304787 : Blo 2303435 2304787 := bstep (se 1 (by rfl) ⟨1728590, by rfl⟩ : syracuseStep 2304787 = 3457181) B3457181
theorem B5185781 : Blo 2303435 5185781 := bbase (se 5 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 5185781 = 486167) (by norm_num)
theorem B3457187 : Blo 2303435 3457187 := bstep (se 1 (by rfl) ⟨2592890, by rfl⟩ : syracuseStep 3457187 = 5185781) B5185781
theorem B2304791 : Blo 2303435 2304791 := bstep (se 1 (by rfl) ⟨1728593, by rfl⟩ : syracuseStep 2304791 = 3457187) B3457187
theorem B22151029 : Blo 2303435 22151029 := bbase (se 5 (by rfl) ⟨1038329, by rfl⟩ : syracuseStep 22151029 = 2076659) (by norm_num)
theorem B29534705 : Blo 2303435 29534705 := bstep (se 2 (by rfl) ⟨11075514, by rfl⟩ : syracuseStep 29534705 = 22151029) B22151029
theorem B19689803 : Blo 2303435 19689803 := bstep (se 1 (by rfl) ⟨14767352, by rfl⟩ : syracuseStep 19689803 = 29534705) B29534705
theorem B13126535 : Blo 2303435 13126535 := bstep (se 1 (by rfl) ⟨9844901, by rfl⟩ : syracuseStep 13126535 = 19689803) B19689803
theorem B8751023 : Blo 2303435 8751023 := bstep (se 1 (by rfl) ⟨6563267, by rfl⟩ : syracuseStep 8751023 = 13126535) B13126535
theorem B5834015 : Blo 2303435 5834015 := bstep (se 1 (by rfl) ⟨4375511, by rfl⟩ : syracuseStep 5834015 = 8751023) B8751023
theorem B3889343 : Blo 2303435 3889343 := bstep (se 1 (by rfl) ⟨2917007, by rfl⟩ : syracuseStep 3889343 = 5834015) B5834015
theorem B2592895 : Blo 2303435 2592895 := bstep (se 1 (by rfl) ⟨1944671, by rfl⟩ : syracuseStep 2592895 = 3889343) B3889343
theorem B3457193 : Blo 2303435 3457193 := bstep (se 2 (by rfl) ⟨1296447, by rfl⟩ : syracuseStep 3457193 = 2592895) B2592895
theorem B2304795 : Blo 2303435 2304795 := bstep (se 1 (by rfl) ⟨1728596, by rfl⟩ : syracuseStep 2304795 = 3457193) B3457193
theorem B13305653 : Blo 2303435 13305653 := bbase (se 5 (by rfl) ⟨623702, by rfl⟩ : syracuseStep 13305653 = 1247405) (by norm_num)
theorem B8870435 : Blo 2303435 8870435 := bstep (se 1 (by rfl) ⟨6652826, by rfl⟩ : syracuseStep 8870435 = 13305653) B13305653
theorem B5913623 : Blo 2303435 5913623 := bstep (se 1 (by rfl) ⟨4435217, by rfl⟩ : syracuseStep 5913623 = 8870435) B8870435
theorem B3942415 : Blo 2303435 3942415 := bstep (se 1 (by rfl) ⟨2956811, by rfl⟩ : syracuseStep 3942415 = 5913623) B5913623
theorem B21026213 : Blo 2303435 21026213 := bstep (se 4 (by rfl) ⟨1971207, by rfl⟩ : syracuseStep 21026213 = 3942415) B3942415
theorem B14017475 : Blo 2303435 14017475 := bstep (se 1 (by rfl) ⟨10513106, by rfl⟩ : syracuseStep 14017475 = 21026213) B21026213
theorem B9344983 : Blo 2303435 9344983 := bstep (se 1 (by rfl) ⟨7008737, by rfl⟩ : syracuseStep 9344983 = 14017475) B14017475
theorem B12459977 : Blo 2303435 12459977 := bstep (se 2 (by rfl) ⟨4672491, by rfl⟩ : syracuseStep 12459977 = 9344983) B9344983
theorem B8306651 : Blo 2303435 8306651 := bstep (se 1 (by rfl) ⟨6229988, by rfl⟩ : syracuseStep 8306651 = 12459977) B12459977
theorem B5537767 : Blo 2303435 5537767 := bstep (se 1 (by rfl) ⟨4153325, by rfl⟩ : syracuseStep 5537767 = 8306651) B8306651
theorem B7383689 : Blo 2303435 7383689 := bstep (se 2 (by rfl) ⟨2768883, by rfl⟩ : syracuseStep 7383689 = 5537767) B5537767
theorem B4922459 : Blo 2303435 4922459 := bstep (se 1 (by rfl) ⟨3691844, by rfl⟩ : syracuseStep 4922459 = 7383689) B7383689
theorem B3281639 : Blo 2303435 3281639 := bstep (se 1 (by rfl) ⟨2461229, by rfl⟩ : syracuseStep 3281639 = 4922459) B4922459
theorem B8751037 : Blo 2303435 8751037 := bstep (se 3 (by rfl) ⟨1640819, by rfl⟩ : syracuseStep 8751037 = 3281639) B3281639
theorem B11668049 : Blo 2303435 11668049 := bstep (se 2 (by rfl) ⟨4375518, by rfl⟩ : syracuseStep 11668049 = 8751037) B8751037
theorem B7778699 : Blo 2303435 7778699 := bstep (se 1 (by rfl) ⟨5834024, by rfl⟩ : syracuseStep 7778699 = 11668049) B11668049
theorem B5185799 : Blo 2303435 5185799 := bstep (se 1 (by rfl) ⟨3889349, by rfl⟩ : syracuseStep 5185799 = 7778699) B7778699
theorem B3457199 : Blo 2303435 3457199 := bstep (se 1 (by rfl) ⟨2592899, by rfl⟩ : syracuseStep 3457199 = 5185799) B5185799
theorem B2304799 : Blo 2303435 2304799 := bstep (se 1 (by rfl) ⟨1728599, by rfl⟩ : syracuseStep 2304799 = 3457199) B3457199
theorem B3457205 : Blo 2303435 3457205 := bbase (se 5 (by rfl) ⟨162056, by rfl⟩ : syracuseStep 3457205 = 324113) (by norm_num)
theorem B2304803 : Blo 2303435 2304803 := bstep (se 1 (by rfl) ⟨1728602, by rfl⟩ : syracuseStep 2304803 = 3457205) B3457205
theorem B5834045 : Blo 2303435 5834045 := bbase (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) (by norm_num)
theorem B3889363 : Blo 2303435 3889363 := bstep (se 1 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 3889363 = 5834045) B5834045
theorem B5185817 : Blo 2303435 5185817 := bstep (se 2 (by rfl) ⟨1944681, by rfl⟩ : syracuseStep 5185817 = 3889363) B3889363
theorem B3457211 : Blo 2303435 3457211 := bstep (se 1 (by rfl) ⟨2592908, by rfl⟩ : syracuseStep 3457211 = 5185817) B5185817
theorem B2304807 : Blo 2303435 2304807 := bstep (se 1 (by rfl) ⟨1728605, by rfl⟩ : syracuseStep 2304807 = 3457211) B3457211
theorem B2592913 : Blo 2303435 2592913 := bbase (se 2 (by rfl) ⟨972342, by rfl⟩ : syracuseStep 2592913 = 1944685) (by norm_num)
theorem B3457217 : Blo 2303435 3457217 := bstep (se 2 (by rfl) ⟨1296456, by rfl⟩ : syracuseStep 3457217 = 2592913) B2592913
theorem B2304811 : Blo 2303435 2304811 := bstep (se 1 (by rfl) ⟨1728608, by rfl⟩ : syracuseStep 2304811 = 3457217) B3457217
theorem B4375549 : Blo 2303435 4375549 := bbase (se 3 (by rfl) ⟨820415, by rfl⟩ : syracuseStep 4375549 = 1640831) (by norm_num)
theorem B5834065 : Blo 2303435 5834065 := bstep (se 2 (by rfl) ⟨2187774, by rfl⟩ : syracuseStep 5834065 = 4375549) B4375549
theorem B7778753 : Blo 2303435 7778753 := bstep (se 2 (by rfl) ⟨2917032, by rfl⟩ : syracuseStep 7778753 = 5834065) B5834065
theorem B5185835 : Blo 2303435 5185835 := bstep (se 1 (by rfl) ⟨3889376, by rfl⟩ : syracuseStep 5185835 = 7778753) B7778753
theorem B3457223 : Blo 2303435 3457223 := bstep (se 1 (by rfl) ⟨2592917, by rfl⟩ : syracuseStep 3457223 = 5185835) B5185835
theorem B2304815 : Blo 2303435 2304815 := bstep (se 1 (by rfl) ⟨1728611, by rfl⟩ : syracuseStep 2304815 = 3457223) B3457223
theorem B3457229 : Blo 2303435 3457229 := bbase (se 3 (by rfl) ⟨648230, by rfl⟩ : syracuseStep 3457229 = 1296461) (by norm_num)
theorem B2304819 : Blo 2303435 2304819 := bstep (se 1 (by rfl) ⟨1728614, by rfl⟩ : syracuseStep 2304819 = 3457229) B3457229
theorem B5185853 : Blo 2303435 5185853 := bbase (se 3 (by rfl) ⟨972347, by rfl⟩ : syracuseStep 5185853 = 1944695) (by norm_num)
theorem B3457235 : Blo 2303435 3457235 := bstep (se 1 (by rfl) ⟨2592926, by rfl⟩ : syracuseStep 3457235 = 5185853) B5185853
theorem B2304823 : Blo 2303435 2304823 := bstep (se 1 (by rfl) ⟨1728617, by rfl⟩ : syracuseStep 2304823 = 3457235) B3457235
theorem B3889397 : Blo 2303435 3889397 := bbase (se 5 (by rfl) ⟨182315, by rfl⟩ : syracuseStep 3889397 = 364631) (by norm_num)
theorem B2592931 : Blo 2303435 2592931 := bstep (se 1 (by rfl) ⟨1944698, by rfl⟩ : syracuseStep 2592931 = 3889397) B3889397
theorem B3457241 : Blo 2303435 3457241 := bstep (se 2 (by rfl) ⟨1296465, by rfl⟩ : syracuseStep 3457241 = 2592931) B2592931
theorem B2304827 : Blo 2303435 2304827 := bstep (se 1 (by rfl) ⟨1728620, by rfl⟩ : syracuseStep 2304827 = 3457241) B3457241
theorem B26974741 : Blo 2303435 26974741 := bbase (se 6 (by rfl) ⟨632220, by rfl⟩ : syracuseStep 26974741 = 1264441) (by norm_num)
theorem B35966321 : Blo 2303435 35966321 := bstep (se 2 (by rfl) ⟨13487370, by rfl⟩ : syracuseStep 35966321 = 26974741) B26974741
theorem B23977547 : Blo 2303435 23977547 := bstep (se 1 (by rfl) ⟨17983160, by rfl⟩ : syracuseStep 23977547 = 35966321) B35966321
theorem B15985031 : Blo 2303435 15985031 := bstep (se 1 (by rfl) ⟨11988773, by rfl⟩ : syracuseStep 15985031 = 23977547) B23977547
theorem B42626749 : Blo 2303435 42626749 := bstep (se 3 (by rfl) ⟨7992515, by rfl⟩ : syracuseStep 42626749 = 15985031) B15985031
theorem B56835665 : Blo 2303435 56835665 := bstep (se 2 (by rfl) ⟨21313374, by rfl⟩ : syracuseStep 56835665 = 42626749) B42626749
theorem B37890443 : Blo 2303435 37890443 := bstep (se 1 (by rfl) ⟨28417832, by rfl⟩ : syracuseStep 37890443 = 56835665) B56835665
theorem B25260295 : Blo 2303435 25260295 := bstep (se 1 (by rfl) ⟨18945221, by rfl⟩ : syracuseStep 25260295 = 37890443) B37890443
theorem B33680393 : Blo 2303435 33680393 := bstep (se 2 (by rfl) ⟨12630147, by rfl⟩ : syracuseStep 33680393 = 25260295) B25260295
theorem B22453595 : Blo 2303435 22453595 := bstep (se 1 (by rfl) ⟨16840196, by rfl⟩ : syracuseStep 22453595 = 33680393) B33680393
theorem B14969063 : Blo 2303435 14969063 := bstep (se 1 (by rfl) ⟨11226797, by rfl⟩ : syracuseStep 14969063 = 22453595) B22453595
theorem B39917501 : Blo 2303435 39917501 := bstep (se 3 (by rfl) ⟨7484531, by rfl⟩ : syracuseStep 39917501 = 14969063) B14969063
theorem B26611667 : Blo 2303435 26611667 := bstep (se 1 (by rfl) ⟨19958750, by rfl⟩ : syracuseStep 26611667 = 39917501) B39917501
theorem B17741111 : Blo 2303435 17741111 := bstep (se 1 (by rfl) ⟨13305833, by rfl⟩ : syracuseStep 17741111 = 26611667) B26611667
theorem B47309629 : Blo 2303435 47309629 := bstep (se 3 (by rfl) ⟨8870555, by rfl⟩ : syracuseStep 47309629 = 17741111) B17741111
theorem B63079505 : Blo 2303435 63079505 := bstep (se 2 (by rfl) ⟨23654814, by rfl⟩ : syracuseStep 63079505 = 47309629) B47309629
theorem B42053003 : Blo 2303435 42053003 := bstep (se 1 (by rfl) ⟨31539752, by rfl⟩ : syracuseStep 42053003 = 63079505) B63079505
theorem B28035335 : Blo 2303435 28035335 := bstep (se 1 (by rfl) ⟨21026501, by rfl⟩ : syracuseStep 28035335 = 42053003) B42053003
theorem B18690223 : Blo 2303435 18690223 := bstep (se 1 (by rfl) ⟨14017667, by rfl⟩ : syracuseStep 18690223 = 28035335) B28035335
theorem B24920297 : Blo 2303435 24920297 := bstep (se 2 (by rfl) ⟨9345111, by rfl⟩ : syracuseStep 24920297 = 18690223) B18690223
theorem B16613531 : Blo 2303435 16613531 := bstep (se 1 (by rfl) ⟨12460148, by rfl⟩ : syracuseStep 16613531 = 24920297) B24920297
theorem B11075687 : Blo 2303435 11075687 := bstep (se 1 (by rfl) ⟨8306765, by rfl⟩ : syracuseStep 11075687 = 16613531) B16613531
theorem B7383791 : Blo 2303435 7383791 := bstep (se 1 (by rfl) ⟨5537843, by rfl⟩ : syracuseStep 7383791 = 11075687) B11075687
theorem B4922527 : Blo 2303435 4922527 := bstep (se 1 (by rfl) ⟨3691895, by rfl⟩ : syracuseStep 4922527 = 7383791) B7383791
theorem B6563369 : Blo 2303435 6563369 := bstep (se 2 (by rfl) ⟨2461263, by rfl⟩ : syracuseStep 6563369 = 4922527) B4922527
theorem B17502317 : Blo 2303435 17502317 := bstep (se 3 (by rfl) ⟨3281684, by rfl⟩ : syracuseStep 17502317 = 6563369) B6563369
theorem B11668211 : Blo 2303435 11668211 := bstep (se 1 (by rfl) ⟨8751158, by rfl⟩ : syracuseStep 11668211 = 17502317) B17502317
theorem B7778807 : Blo 2303435 7778807 := bstep (se 1 (by rfl) ⟨5834105, by rfl⟩ : syracuseStep 7778807 = 11668211) B11668211
theorem B5185871 : Blo 2303435 5185871 := bstep (se 1 (by rfl) ⟨3889403, by rfl⟩ : syracuseStep 5185871 = 7778807) B7778807
theorem B3457247 : Blo 2303435 3457247 := bstep (se 1 (by rfl) ⟨2592935, by rfl⟩ : syracuseStep 3457247 = 5185871) B5185871
theorem B2304831 : Blo 2303435 2304831 := bstep (se 1 (by rfl) ⟨1728623, by rfl⟩ : syracuseStep 2304831 = 3457247) B3457247
theorem B3457253 : Blo 2303435 3457253 := bbase (se 4 (by rfl) ⟨324117, by rfl⟩ : syracuseStep 3457253 = 648235) (by norm_num)
theorem B2304835 : Blo 2303435 2304835 := bstep (se 1 (by rfl) ⟨1728626, by rfl⟩ : syracuseStep 2304835 = 3457253) B3457253
theorem B3691909 : Blo 2303435 3691909 := bbase (se 4 (by rfl) ⟨346116, by rfl⟩ : syracuseStep 3691909 = 692233) (by norm_num)
theorem B4922545 : Blo 2303435 4922545 := bstep (se 2 (by rfl) ⟨1845954, by rfl⟩ : syracuseStep 4922545 = 3691909) B3691909
theorem B6563393 : Blo 2303435 6563393 := bstep (se 2 (by rfl) ⟨2461272, by rfl⟩ : syracuseStep 6563393 = 4922545) B4922545
theorem B4375595 : Blo 2303435 4375595 := bstep (se 1 (by rfl) ⟨3281696, by rfl⟩ : syracuseStep 4375595 = 6563393) B6563393
theorem B2917063 : Blo 2303435 2917063 := bstep (se 1 (by rfl) ⟨2187797, by rfl⟩ : syracuseStep 2917063 = 4375595) B4375595
theorem B3889417 : Blo 2303435 3889417 := bstep (se 2 (by rfl) ⟨1458531, by rfl⟩ : syracuseStep 3889417 = 2917063) B2917063
theorem B5185889 : Blo 2303435 5185889 := bstep (se 2 (by rfl) ⟨1944708, by rfl⟩ : syracuseStep 5185889 = 3889417) B3889417
theorem B3457259 : Blo 2303435 3457259 := bstep (se 1 (by rfl) ⟨2592944, by rfl⟩ : syracuseStep 3457259 = 5185889) B5185889
theorem B2304839 : Blo 2303435 2304839 := bstep (se 1 (by rfl) ⟨1728629, by rfl⟩ : syracuseStep 2304839 = 3457259) B3457259
theorem B2592949 : Blo 2303435 2592949 := bbase (se 5 (by rfl) ⟨121544, by rfl⟩ : syracuseStep 2592949 = 243089) (by norm_num)
theorem B3457265 : Blo 2303435 3457265 := bstep (se 2 (by rfl) ⟨1296474, by rfl⟩ : syracuseStep 3457265 = 2592949) B2592949
theorem B2304843 : Blo 2303435 2304843 := bstep (se 1 (by rfl) ⟨1728632, by rfl⟩ : syracuseStep 2304843 = 3457265) B3457265
theorem B2917073 : Blo 2303435 2917073 := bbase (se 2 (by rfl) ⟨1093902, by rfl⟩ : syracuseStep 2917073 = 2187805) (by norm_num)
theorem B7778861 : Blo 2303435 7778861 := bstep (se 3 (by rfl) ⟨1458536, by rfl⟩ : syracuseStep 7778861 = 2917073) B2917073
theorem B5185907 : Blo 2303435 5185907 := bstep (se 1 (by rfl) ⟨3889430, by rfl⟩ : syracuseStep 5185907 = 7778861) B7778861
theorem B3457271 : Blo 2303435 3457271 := bstep (se 1 (by rfl) ⟨2592953, by rfl⟩ : syracuseStep 3457271 = 5185907) B5185907
theorem B2304847 : Blo 2303435 2304847 := bstep (se 1 (by rfl) ⟨1728635, by rfl⟩ : syracuseStep 2304847 = 3457271) B3457271
theorem B3457277 : Blo 2303435 3457277 := bbase (se 3 (by rfl) ⟨648239, by rfl⟩ : syracuseStep 3457277 = 1296479) (by norm_num)
theorem B2304851 : Blo 2303435 2304851 := bstep (se 1 (by rfl) ⟨1728638, by rfl⟩ : syracuseStep 2304851 = 3457277) B3457277
theorem B5185925 : Blo 2303435 5185925 := bbase (se 4 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 5185925 = 972361) (by norm_num)
theorem B3457283 : Blo 2303435 3457283 := bstep (se 1 (by rfl) ⟨2592962, by rfl⟩ : syracuseStep 3457283 = 5185925) B5185925
theorem B2304855 : Blo 2303435 2304855 := bstep (se 1 (by rfl) ⟨1728641, by rfl⟩ : syracuseStep 2304855 = 3457283) B3457283
theorem B3281725 : Blo 2303435 3281725 := bbase (se 3 (by rfl) ⟨615323, by rfl⟩ : syracuseStep 3281725 = 1230647) (by norm_num)
theorem B4375633 : Blo 2303435 4375633 := bstep (se 2 (by rfl) ⟨1640862, by rfl⟩ : syracuseStep 4375633 = 3281725) B3281725
theorem B5834177 : Blo 2303435 5834177 := bstep (se 2 (by rfl) ⟨2187816, by rfl⟩ : syracuseStep 5834177 = 4375633) B4375633
theorem B3889451 : Blo 2303435 3889451 := bstep (se 1 (by rfl) ⟨2917088, by rfl⟩ : syracuseStep 3889451 = 5834177) B5834177
theorem B2592967 : Blo 2303435 2592967 := bstep (se 1 (by rfl) ⟨1944725, by rfl⟩ : syracuseStep 2592967 = 3889451) B3889451
theorem B3457289 : Blo 2303435 3457289 := bstep (se 2 (by rfl) ⟨1296483, by rfl⟩ : syracuseStep 3457289 = 2592967) B2592967
theorem B2304859 : Blo 2303435 2304859 := bstep (se 1 (by rfl) ⟨1728644, by rfl⟩ : syracuseStep 2304859 = 3457289) B3457289
theorem B11668373 : Blo 2303435 11668373 := bbase (se 6 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 11668373 = 546955) (by norm_num)
theorem B7778915 : Blo 2303435 7778915 := bstep (se 1 (by rfl) ⟨5834186, by rfl⟩ : syracuseStep 7778915 = 11668373) B11668373
theorem B5185943 : Blo 2303435 5185943 := bstep (se 1 (by rfl) ⟨3889457, by rfl⟩ : syracuseStep 5185943 = 7778915) B7778915
theorem B3457295 : Blo 2303435 3457295 := bstep (se 1 (by rfl) ⟨2592971, by rfl⟩ : syracuseStep 3457295 = 5185943) B5185943
theorem B2304863 : Blo 2303435 2304863 := bstep (se 1 (by rfl) ⟨1728647, by rfl⟩ : syracuseStep 2304863 = 3457295) B3457295
theorem B3457301 : Blo 2303435 3457301 := bbase (se 6 (by rfl) ⟨81030, by rfl⟩ : syracuseStep 3457301 = 162061) (by norm_num)
theorem B2304867 : Blo 2303435 2304867 := bstep (se 1 (by rfl) ⟨1728650, by rfl⟩ : syracuseStep 2304867 = 3457301) B3457301
theorem B4736389 : Blo 2303435 4736389 := bbase (se 4 (by rfl) ⟨444036, by rfl⟩ : syracuseStep 4736389 = 888073) (by norm_num)
theorem B6315185 : Blo 2303435 6315185 := bstep (se 2 (by rfl) ⟨2368194, by rfl⟩ : syracuseStep 6315185 = 4736389) B4736389
theorem B16840493 : Blo 2303435 16840493 := bstep (se 3 (by rfl) ⟨3157592, by rfl⟩ : syracuseStep 16840493 = 6315185) B6315185
theorem B11226995 : Blo 2303435 11226995 := bstep (se 1 (by rfl) ⟨8420246, by rfl⟩ : syracuseStep 11226995 = 16840493) B16840493
theorem B7484663 : Blo 2303435 7484663 := bstep (se 1 (by rfl) ⟨5613497, by rfl⟩ : syracuseStep 7484663 = 11226995) B11226995
theorem B4989775 : Blo 2303435 4989775 := bstep (se 1 (by rfl) ⟨3742331, by rfl⟩ : syracuseStep 4989775 = 7484663) B7484663
theorem B6653033 : Blo 2303435 6653033 := bstep (se 2 (by rfl) ⟨2494887, by rfl⟩ : syracuseStep 6653033 = 4989775) B4989775
theorem B4435355 : Blo 2303435 4435355 := bstep (se 1 (by rfl) ⟨3326516, by rfl⟩ : syracuseStep 4435355 = 6653033) B6653033
theorem B11827613 : Blo 2303435 11827613 := bstep (se 3 (by rfl) ⟨2217677, by rfl⟩ : syracuseStep 11827613 = 4435355) B4435355
theorem B7885075 : Blo 2303435 7885075 := bstep (se 1 (by rfl) ⟨5913806, by rfl⟩ : syracuseStep 7885075 = 11827613) B11827613
theorem B10513433 : Blo 2303435 10513433 := bstep (se 2 (by rfl) ⟨3942537, by rfl⟩ : syracuseStep 10513433 = 7885075) B7885075
theorem B28035821 : Blo 2303435 28035821 := bstep (se 3 (by rfl) ⟨5256716, by rfl⟩ : syracuseStep 28035821 = 10513433) B10513433
theorem B18690547 : Blo 2303435 18690547 := bstep (se 1 (by rfl) ⟨14017910, by rfl⟩ : syracuseStep 18690547 = 28035821) B28035821
theorem B24920729 : Blo 2303435 24920729 := bstep (se 2 (by rfl) ⟨9345273, by rfl⟩ : syracuseStep 24920729 = 18690547) B18690547
theorem B16613819 : Blo 2303435 16613819 := bstep (se 1 (by rfl) ⟨12460364, by rfl⟩ : syracuseStep 16613819 = 24920729) B24920729
theorem B11075879 : Blo 2303435 11075879 := bstep (se 1 (by rfl) ⟨8306909, by rfl⟩ : syracuseStep 11075879 = 16613819) B16613819
theorem B29535677 : Blo 2303435 29535677 := bstep (se 3 (by rfl) ⟨5537939, by rfl⟩ : syracuseStep 29535677 = 11075879) B11075879
theorem B19690451 : Blo 2303435 19690451 := bstep (se 1 (by rfl) ⟨14767838, by rfl⟩ : syracuseStep 19690451 = 29535677) B29535677
theorem B13126967 : Blo 2303435 13126967 := bstep (se 1 (by rfl) ⟨9845225, by rfl⟩ : syracuseStep 13126967 = 19690451) B19690451
theorem B8751311 : Blo 2303435 8751311 := bstep (se 1 (by rfl) ⟨6563483, by rfl⟩ : syracuseStep 8751311 = 13126967) B13126967
theorem B5834207 : Blo 2303435 5834207 := bstep (se 1 (by rfl) ⟨4375655, by rfl⟩ : syracuseStep 5834207 = 8751311) B8751311
theorem B3889471 : Blo 2303435 3889471 := bstep (se 1 (by rfl) ⟨2917103, by rfl⟩ : syracuseStep 3889471 = 5834207) B5834207
theorem B5185961 : Blo 2303435 5185961 := bstep (se 2 (by rfl) ⟨1944735, by rfl⟩ : syracuseStep 5185961 = 3889471) B3889471
theorem B3457307 : Blo 2303435 3457307 := bstep (se 1 (by rfl) ⟨2592980, by rfl⟩ : syracuseStep 3457307 = 5185961) B5185961
theorem B2304871 : Blo 2303435 2304871 := bstep (se 1 (by rfl) ⟨1728653, by rfl⟩ : syracuseStep 2304871 = 3457307) B3457307
theorem B2592985 : Blo 2303435 2592985 := bbase (se 2 (by rfl) ⟨972369, by rfl⟩ : syracuseStep 2592985 = 1944739) (by norm_num)
theorem B3457313 : Blo 2303435 3457313 := bstep (se 2 (by rfl) ⟨1296492, by rfl⟩ : syracuseStep 3457313 = 2592985) B2592985
theorem B2304875 : Blo 2303435 2304875 := bstep (se 1 (by rfl) ⟨1728656, by rfl⟩ : syracuseStep 2304875 = 3457313) B3457313
theorem B3691973 : Blo 2303435 3691973 := bbase (se 4 (by rfl) ⟨346122, by rfl⟩ : syracuseStep 3691973 = 692245) (by norm_num)
theorem B2461315 : Blo 2303435 2461315 := bstep (se 1 (by rfl) ⟨1845986, by rfl⟩ : syracuseStep 2461315 = 3691973) B3691973
theorem B3281753 : Blo 2303435 3281753 := bstep (se 2 (by rfl) ⟨1230657, by rfl⟩ : syracuseStep 3281753 = 2461315) B2461315
theorem B8751341 : Blo 2303435 8751341 := bstep (se 3 (by rfl) ⟨1640876, by rfl⟩ : syracuseStep 8751341 = 3281753) B3281753
theorem B5834227 : Blo 2303435 5834227 := bstep (se 1 (by rfl) ⟨4375670, by rfl⟩ : syracuseStep 5834227 = 8751341) B8751341
theorem B7778969 : Blo 2303435 7778969 := bstep (se 2 (by rfl) ⟨2917113, by rfl⟩ : syracuseStep 7778969 = 5834227) B5834227
theorem B5185979 : Blo 2303435 5185979 := bstep (se 1 (by rfl) ⟨3889484, by rfl⟩ : syracuseStep 5185979 = 7778969) B7778969
theorem B3457319 : Blo 2303435 3457319 := bstep (se 1 (by rfl) ⟨2592989, by rfl⟩ : syracuseStep 3457319 = 5185979) B5185979
theorem B2304879 : Blo 2303435 2304879 := bstep (se 1 (by rfl) ⟨1728659, by rfl⟩ : syracuseStep 2304879 = 3457319) B3457319
theorem B3457325 : Blo 2303435 3457325 := bbase (se 3 (by rfl) ⟨648248, by rfl⟩ : syracuseStep 3457325 = 1296497) (by norm_num)
theorem B2304883 : Blo 2303435 2304883 := bstep (se 1 (by rfl) ⟨1728662, by rfl⟩ : syracuseStep 2304883 = 3457325) B3457325
theorem B5185997 : Blo 2303435 5185997 := bbase (se 3 (by rfl) ⟨972374, by rfl⟩ : syracuseStep 5185997 = 1944749) (by norm_num)
theorem B3457331 : Blo 2303435 3457331 := bstep (se 1 (by rfl) ⟨2592998, by rfl⟩ : syracuseStep 3457331 = 5185997) B5185997
theorem B2304887 : Blo 2303435 2304887 := bstep (se 1 (by rfl) ⟨1728665, by rfl⟩ : syracuseStep 2304887 = 3457331) B3457331
theorem B2917129 : Blo 2303435 2917129 := bbase (se 2 (by rfl) ⟨1093923, by rfl⟩ : syracuseStep 2917129 = 2187847) (by norm_num)
theorem B3889505 : Blo 2303435 3889505 := bstep (se 2 (by rfl) ⟨1458564, by rfl⟩ : syracuseStep 3889505 = 2917129) B2917129
theorem B2593003 : Blo 2303435 2593003 := bstep (se 1 (by rfl) ⟨1944752, by rfl⟩ : syracuseStep 2593003 = 3889505) B3889505
theorem B3457337 : Blo 2303435 3457337 := bstep (se 2 (by rfl) ⟨1296501, by rfl⟩ : syracuseStep 3457337 = 2593003) B2593003
theorem B2304891 : Blo 2303435 2304891 := bstep (se 1 (by rfl) ⟨1728668, by rfl⟩ : syracuseStep 2304891 = 3457337) B3457337
theorem B4672685 : Blo 2303435 4672685 := bbase (se 3 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 4672685 = 1752257) (by norm_num)
theorem B12460493 : Blo 2303435 12460493 := bstep (se 3 (by rfl) ⟨2336342, by rfl⟩ : syracuseStep 12460493 = 4672685) B4672685
theorem B33227981 : Blo 2303435 33227981 := bstep (se 3 (by rfl) ⟨6230246, by rfl⟩ : syracuseStep 33227981 = 12460493) B12460493
theorem B22151987 : Blo 2303435 22151987 := bstep (se 1 (by rfl) ⟨16613990, by rfl⟩ : syracuseStep 22151987 = 33227981) B33227981
theorem B14767991 : Blo 2303435 14767991 := bstep (se 1 (by rfl) ⟨11075993, by rfl⟩ : syracuseStep 14767991 = 22151987) B22151987
theorem B9845327 : Blo 2303435 9845327 := bstep (se 1 (by rfl) ⟨7383995, by rfl⟩ : syracuseStep 9845327 = 14767991) B14767991
theorem B26254205 : Blo 2303435 26254205 := bstep (se 3 (by rfl) ⟨4922663, by rfl⟩ : syracuseStep 26254205 = 9845327) B9845327
theorem B17502803 : Blo 2303435 17502803 := bstep (se 1 (by rfl) ⟨13127102, by rfl⟩ : syracuseStep 17502803 = 26254205) B26254205
theorem B11668535 : Blo 2303435 11668535 := bstep (se 1 (by rfl) ⟨8751401, by rfl⟩ : syracuseStep 11668535 = 17502803) B17502803
theorem B7779023 : Blo 2303435 7779023 := bstep (se 1 (by rfl) ⟨5834267, by rfl⟩ : syracuseStep 7779023 = 11668535) B11668535
theorem B5186015 : Blo 2303435 5186015 := bstep (se 1 (by rfl) ⟨3889511, by rfl⟩ : syracuseStep 5186015 = 7779023) B7779023
theorem B3457343 : Blo 2303435 3457343 := bstep (se 1 (by rfl) ⟨2593007, by rfl⟩ : syracuseStep 3457343 = 5186015) B5186015
theorem B2304895 : Blo 2303435 2304895 := bstep (se 1 (by rfl) ⟨1728671, by rfl⟩ : syracuseStep 2304895 = 3457343) B3457343
theorem B3457349 : Blo 2303435 3457349 := bbase (se 4 (by rfl) ⟨324126, by rfl⟩ : syracuseStep 3457349 = 648253) (by norm_num)
theorem B2304899 : Blo 2303435 2304899 := bstep (se 1 (by rfl) ⟨1728674, by rfl⟩ : syracuseStep 2304899 = 3457349) B3457349
theorem B3889525 : Blo 2303435 3889525 := bbase (se 5 (by rfl) ⟨182321, by rfl⟩ : syracuseStep 3889525 = 364643) (by norm_num)
theorem B5186033 : Blo 2303435 5186033 := bstep (se 2 (by rfl) ⟨1944762, by rfl⟩ : syracuseStep 5186033 = 3889525) B3889525
theorem B3457355 : Blo 2303435 3457355 := bstep (se 1 (by rfl) ⟨2593016, by rfl⟩ : syracuseStep 3457355 = 5186033) B5186033
theorem B2304903 : Blo 2303435 2304903 := bstep (se 1 (by rfl) ⟨1728677, by rfl⟩ : syracuseStep 2304903 = 3457355) B3457355
theorem B2593021 : Blo 2303435 2593021 := bbase (se 3 (by rfl) ⟨486191, by rfl⟩ : syracuseStep 2593021 = 972383) (by norm_num)
theorem B3457361 : Blo 2303435 3457361 := bstep (se 2 (by rfl) ⟨1296510, by rfl⟩ : syracuseStep 3457361 = 2593021) B2593021
theorem B2304907 : Blo 2303435 2304907 := bstep (se 1 (by rfl) ⟨1728680, by rfl⟩ : syracuseStep 2304907 = 3457361) B3457361
theorem B7779077 : Blo 2303435 7779077 := bbase (se 4 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 7779077 = 1458577) (by norm_num)
theorem B5186051 : Blo 2303435 5186051 := bstep (se 1 (by rfl) ⟨3889538, by rfl⟩ : syracuseStep 5186051 = 7779077) B7779077
theorem B3457367 : Blo 2303435 3457367 := bstep (se 1 (by rfl) ⟨2593025, by rfl⟩ : syracuseStep 3457367 = 5186051) B5186051
theorem B2304911 : Blo 2303435 2304911 := bstep (se 1 (by rfl) ⟨1728683, by rfl⟩ : syracuseStep 2304911 = 3457367) B3457367
theorem B3457373 : Blo 2303435 3457373 := bbase (se 3 (by rfl) ⟨648257, by rfl⟩ : syracuseStep 3457373 = 1296515) (by norm_num)
theorem B2304915 : Blo 2303435 2304915 := bstep (se 1 (by rfl) ⟨1728686, by rfl⟩ : syracuseStep 2304915 = 3457373) B3457373
theorem B5186069 : Blo 2303435 5186069 := bbase (se 6 (by rfl) ⟨121548, by rfl⟩ : syracuseStep 5186069 = 243097) (by norm_num)
theorem B3457379 : Blo 2303435 3457379 := bstep (se 1 (by rfl) ⟨2593034, by rfl⟩ : syracuseStep 3457379 = 5186069) B5186069
theorem B2304919 : Blo 2303435 2304919 := bstep (se 1 (by rfl) ⟨1728689, by rfl⟩ : syracuseStep 2304919 = 3457379) B3457379
theorem B8751509 : Blo 2303435 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B5834339 : Blo 2303435 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B3889559 : Blo 2303435 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B2593039 : Blo 2303435 2593039 := bstep (se 1 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 2593039 = 3889559) B3889559
theorem B3457385 : Blo 2303435 3457385 := bstep (se 2 (by rfl) ⟨1296519, by rfl⟩ : syracuseStep 3457385 = 2593039) B2593039
theorem B2304923 : Blo 2303435 2304923 := bstep (se 1 (by rfl) ⟨1728692, by rfl⟩ : syracuseStep 2304923 = 3457385) B3457385
theorem B13127285 : Blo 2303435 13127285 := bbase (se 5 (by rfl) ⟨615341, by rfl⟩ : syracuseStep 13127285 = 1230683) (by norm_num)
theorem B8751523 : Blo 2303435 8751523 := bstep (se 1 (by rfl) ⟨6563642, by rfl⟩ : syracuseStep 8751523 = 13127285) B13127285
theorem B11668697 : Blo 2303435 11668697 := bstep (se 2 (by rfl) ⟨4375761, by rfl⟩ : syracuseStep 11668697 = 8751523) B8751523
theorem B7779131 : Blo 2303435 7779131 := bstep (se 1 (by rfl) ⟨5834348, by rfl⟩ : syracuseStep 7779131 = 11668697) B11668697
theorem B5186087 : Blo 2303435 5186087 := bstep (se 1 (by rfl) ⟨3889565, by rfl⟩ : syracuseStep 5186087 = 7779131) B7779131
theorem B3457391 : Blo 2303435 3457391 := bstep (se 1 (by rfl) ⟨2593043, by rfl⟩ : syracuseStep 3457391 = 5186087) B5186087
theorem B2304927 : Blo 2303435 2304927 := bstep (se 1 (by rfl) ⟨1728695, by rfl⟩ : syracuseStep 2304927 = 3457391) B3457391
theorem B3457397 : Blo 2303435 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B2304931 : Blo 2303435 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B5913973 : Blo 2303435 5913973 := bbase (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) (by norm_num)
theorem B7885297 : Blo 2303435 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B10513729 : Blo 2303435 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B14018305 : Blo 2303435 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B18691073 : Blo 2303435 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B12460715 : Blo 2303435 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B8307143 : Blo 2303435 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B5538095 : Blo 2303435 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B3692063 : Blo 2303435 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B2461375 : Blo 2303435 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B3281833 : Blo 2303435 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B4375777 : Blo 2303435 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B5834369 : Blo 2303435 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B3889579 : Blo 2303435 3889579 := bstep (se 1 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 3889579 = 5834369) B5834369
theorem B5186105 : Blo 2303435 5186105 := bstep (se 2 (by rfl) ⟨1944789, by rfl⟩ : syracuseStep 5186105 = 3889579) B3889579
theorem B3457403 : Blo 2303435 3457403 := bstep (se 1 (by rfl) ⟨2593052, by rfl⟩ : syracuseStep 3457403 = 5186105) B5186105
theorem B2304935 : Blo 2303435 2304935 := bstep (se 1 (by rfl) ⟨1728701, by rfl⟩ : syracuseStep 2304935 = 3457403) B3457403
theorem B2593057 : Blo 2303435 2593057 := bbase (se 2 (by rfl) ⟨972396, by rfl⟩ : syracuseStep 2593057 = 1944793) (by norm_num)
theorem B3457409 : Blo 2303435 3457409 := bstep (se 2 (by rfl) ⟨1296528, by rfl⟩ : syracuseStep 3457409 = 2593057) B2593057
theorem B2304939 : Blo 2303435 2304939 := bstep (se 1 (by rfl) ⟨1728704, by rfl⟩ : syracuseStep 2304939 = 3457409) B3457409
theorem B5834389 : Blo 2303435 5834389 := bbase (se 6 (by rfl) ⟨136743, by rfl⟩ : syracuseStep 5834389 = 273487) (by norm_num)
theorem B7779185 : Blo 2303435 7779185 := bstep (se 2 (by rfl) ⟨2917194, by rfl⟩ : syracuseStep 7779185 = 5834389) B5834389
theorem B5186123 : Blo 2303435 5186123 := bstep (se 1 (by rfl) ⟨3889592, by rfl⟩ : syracuseStep 5186123 = 7779185) B7779185
theorem B3457415 : Blo 2303435 3457415 := bstep (se 1 (by rfl) ⟨2593061, by rfl⟩ : syracuseStep 3457415 = 5186123) B5186123
theorem B2304943 : Blo 2303435 2304943 := bstep (se 1 (by rfl) ⟨1728707, by rfl⟩ : syracuseStep 2304943 = 3457415) B3457415
theorem B3457421 : Blo 2303435 3457421 := bbase (se 3 (by rfl) ⟨648266, by rfl⟩ : syracuseStep 3457421 = 1296533) (by norm_num)
theorem B2304947 : Blo 2303435 2304947 := bstep (se 1 (by rfl) ⟨1728710, by rfl⟩ : syracuseStep 2304947 = 3457421) B3457421
theorem B5186141 : Blo 2303435 5186141 := bbase (se 3 (by rfl) ⟨972401, by rfl⟩ : syracuseStep 5186141 = 1944803) (by norm_num)
theorem B3457427 : Blo 2303435 3457427 := bstep (se 1 (by rfl) ⟨2593070, by rfl⟩ : syracuseStep 3457427 = 5186141) B5186141
theorem B2304951 : Blo 2303435 2304951 := bstep (se 1 (by rfl) ⟨1728713, by rfl⟩ : syracuseStep 2304951 = 3457427) B3457427
theorem B3889613 : Blo 2303435 3889613 := bbase (se 3 (by rfl) ⟨729302, by rfl⟩ : syracuseStep 3889613 = 1458605) (by norm_num)
theorem B2593075 : Blo 2303435 2593075 := bstep (se 1 (by rfl) ⟨1944806, by rfl⟩ : syracuseStep 2593075 = 3889613) B3889613
theorem B3457433 : Blo 2303435 3457433 := bstep (se 2 (by rfl) ⟨1296537, by rfl⟩ : syracuseStep 3457433 = 2593075) B2593075
theorem B2304955 : Blo 2303435 2304955 := bstep (se 1 (by rfl) ⟨1728716, by rfl⟩ : syracuseStep 2304955 = 3457433) B3457433
theorem B4153613 : Blo 2303435 4153613 := bbase (se 3 (by rfl) ⟨778802, by rfl⟩ : syracuseStep 4153613 = 1557605) (by norm_num)
theorem B11076301 : Blo 2303435 11076301 := bstep (se 3 (by rfl) ⟨2076806, by rfl⟩ : syracuseStep 11076301 = 4153613) B4153613
theorem B14768401 : Blo 2303435 14768401 := bstep (se 2 (by rfl) ⟨5538150, by rfl⟩ : syracuseStep 14768401 = 11076301) B11076301
theorem B19691201 : Blo 2303435 19691201 := bstep (se 2 (by rfl) ⟨7384200, by rfl⟩ : syracuseStep 19691201 = 14768401) B14768401
theorem B13127467 : Blo 2303435 13127467 := bstep (se 1 (by rfl) ⟨9845600, by rfl⟩ : syracuseStep 13127467 = 19691201) B19691201
theorem B17503289 : Blo 2303435 17503289 := bstep (se 2 (by rfl) ⟨6563733, by rfl⟩ : syracuseStep 17503289 = 13127467) B13127467
theorem B11668859 : Blo 2303435 11668859 := bstep (se 1 (by rfl) ⟨8751644, by rfl⟩ : syracuseStep 11668859 = 17503289) B17503289
theorem B7779239 : Blo 2303435 7779239 := bstep (se 1 (by rfl) ⟨5834429, by rfl⟩ : syracuseStep 7779239 = 11668859) B11668859
theorem B5186159 : Blo 2303435 5186159 := bstep (se 1 (by rfl) ⟨3889619, by rfl⟩ : syracuseStep 5186159 = 7779239) B7779239
theorem B3457439 : Blo 2303435 3457439 := bstep (se 1 (by rfl) ⟨2593079, by rfl⟩ : syracuseStep 3457439 = 5186159) B5186159
theorem B2304959 : Blo 2303435 2304959 := bstep (se 1 (by rfl) ⟨1728719, by rfl⟩ : syracuseStep 2304959 = 3457439) B3457439
theorem B3457445 : Blo 2303435 3457445 := bbase (se 4 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 3457445 = 648271) (by norm_num)
theorem B2304963 : Blo 2303435 2304963 := bstep (se 1 (by rfl) ⟨1728722, by rfl⟩ : syracuseStep 2304963 = 3457445) B3457445
theorem B2917225 : Blo 2303435 2917225 := bbase (se 2 (by rfl) ⟨1093959, by rfl⟩ : syracuseStep 2917225 = 2187919) (by norm_num)
theorem B3889633 : Blo 2303435 3889633 := bstep (se 2 (by rfl) ⟨1458612, by rfl⟩ : syracuseStep 3889633 = 2917225) B2917225
theorem B5186177 : Blo 2303435 5186177 := bstep (se 2 (by rfl) ⟨1944816, by rfl⟩ : syracuseStep 5186177 = 3889633) B3889633
theorem B3457451 : Blo 2303435 3457451 := bstep (se 1 (by rfl) ⟨2593088, by rfl⟩ : syracuseStep 3457451 = 5186177) B5186177
theorem B2304967 : Blo 2303435 2304967 := bstep (se 1 (by rfl) ⟨1728725, by rfl⟩ : syracuseStep 2304967 = 3457451) B3457451
theorem B2593093 : Blo 2303435 2593093 := bbase (se 4 (by rfl) ⟨243102, by rfl⟩ : syracuseStep 2593093 = 486205) (by norm_num)
theorem B3457457 : Blo 2303435 3457457 := bstep (se 2 (by rfl) ⟨1296546, by rfl⟩ : syracuseStep 3457457 = 2593093) B2593093
theorem B2304971 : Blo 2303435 2304971 := bstep (se 1 (by rfl) ⟨1728728, by rfl⟩ : syracuseStep 2304971 = 3457457) B3457457
theorem B4375853 : Blo 2303435 4375853 := bbase (se 3 (by rfl) ⟨820472, by rfl⟩ : syracuseStep 4375853 = 1640945) (by norm_num)
theorem B2917235 : Blo 2303435 2917235 := bstep (se 1 (by rfl) ⟨2187926, by rfl⟩ : syracuseStep 2917235 = 4375853) B4375853
theorem B7779293 : Blo 2303435 7779293 := bstep (se 3 (by rfl) ⟨1458617, by rfl⟩ : syracuseStep 7779293 = 2917235) B2917235
theorem B5186195 : Blo 2303435 5186195 := bstep (se 1 (by rfl) ⟨3889646, by rfl⟩ : syracuseStep 5186195 = 7779293) B7779293
theorem B3457463 : Blo 2303435 3457463 := bstep (se 1 (by rfl) ⟨2593097, by rfl⟩ : syracuseStep 3457463 = 5186195) B5186195
theorem B2304975 : Blo 2303435 2304975 := bstep (se 1 (by rfl) ⟨1728731, by rfl⟩ : syracuseStep 2304975 = 3457463) B3457463
theorem B3457469 : Blo 2303435 3457469 := bbase (se 3 (by rfl) ⟨648275, by rfl⟩ : syracuseStep 3457469 = 1296551) (by norm_num)
theorem B2304979 : Blo 2303435 2304979 := bstep (se 1 (by rfl) ⟨1728734, by rfl⟩ : syracuseStep 2304979 = 3457469) B3457469
theorem B5186213 : Blo 2303435 5186213 := bbase (se 4 (by rfl) ⟨486207, by rfl⟩ : syracuseStep 5186213 = 972415) (by norm_num)
theorem B3457475 : Blo 2303435 3457475 := bstep (se 1 (by rfl) ⟨2593106, by rfl⟩ : syracuseStep 3457475 = 5186213) B5186213
theorem B2304983 : Blo 2303435 2304983 := bstep (se 1 (by rfl) ⟨1728737, by rfl⟩ : syracuseStep 2304983 = 3457475) B3457475
theorem B5834501 : Blo 2303435 5834501 := bbase (se 4 (by rfl) ⟨546984, by rfl⟩ : syracuseStep 5834501 = 1093969) (by norm_num)
theorem B3889667 : Blo 2303435 3889667 := bstep (se 1 (by rfl) ⟨2917250, by rfl⟩ : syracuseStep 3889667 = 5834501) B5834501
theorem B2593111 : Blo 2303435 2593111 := bstep (se 1 (by rfl) ⟨1944833, by rfl⟩ : syracuseStep 2593111 = 3889667) B3889667
theorem B3457481 : Blo 2303435 3457481 := bstep (se 2 (by rfl) ⟨1296555, by rfl⟩ : syracuseStep 3457481 = 2593111) B2593111
theorem B2304987 : Blo 2303435 2304987 := bstep (se 1 (by rfl) ⟨1728740, by rfl⟩ : syracuseStep 2304987 = 3457481) B3457481
theorem B4922869 : Blo 2303435 4922869 := bbase (se 5 (by rfl) ⟨230759, by rfl⟩ : syracuseStep 4922869 = 461519) (by norm_num)
theorem B6563825 : Blo 2303435 6563825 := bstep (se 2 (by rfl) ⟨2461434, by rfl⟩ : syracuseStep 6563825 = 4922869) B4922869
theorem B4375883 : Blo 2303435 4375883 := bstep (se 1 (by rfl) ⟨3281912, by rfl⟩ : syracuseStep 4375883 = 6563825) B6563825
theorem B11669021 : Blo 2303435 11669021 := bstep (se 3 (by rfl) ⟨2187941, by rfl⟩ : syracuseStep 11669021 = 4375883) B4375883
theorem B7779347 : Blo 2303435 7779347 := bstep (se 1 (by rfl) ⟨5834510, by rfl⟩ : syracuseStep 7779347 = 11669021) B11669021
theorem B5186231 : Blo 2303435 5186231 := bstep (se 1 (by rfl) ⟨3889673, by rfl⟩ : syracuseStep 5186231 = 7779347) B7779347
theorem B3457487 : Blo 2303435 3457487 := bstep (se 1 (by rfl) ⟨2593115, by rfl⟩ : syracuseStep 3457487 = 5186231) B5186231
theorem B2304991 : Blo 2303435 2304991 := bstep (se 1 (by rfl) ⟨1728743, by rfl⟩ : syracuseStep 2304991 = 3457487) B3457487
theorem B3457493 : Blo 2303435 3457493 := bbase (se 7 (by rfl) ⟨40517, by rfl⟩ : syracuseStep 3457493 = 81035) (by norm_num)
theorem B2304995 : Blo 2303435 2304995 := bstep (se 1 (by rfl) ⟨1728746, by rfl⟩ : syracuseStep 2304995 = 3457493) B3457493
theorem B8751797 : Blo 2303435 8751797 := bbase (se 5 (by rfl) ⟨410240, by rfl⟩ : syracuseStep 8751797 = 820481) (by norm_num)
theorem B5834531 : Blo 2303435 5834531 := bstep (se 1 (by rfl) ⟨4375898, by rfl⟩ : syracuseStep 5834531 = 8751797) B8751797
theorem B3889687 : Blo 2303435 3889687 := bstep (se 1 (by rfl) ⟨2917265, by rfl⟩ : syracuseStep 3889687 = 5834531) B5834531
theorem B5186249 : Blo 2303435 5186249 := bstep (se 2 (by rfl) ⟨1944843, by rfl⟩ : syracuseStep 5186249 = 3889687) B3889687
theorem B3457499 : Blo 2303435 3457499 := bstep (se 1 (by rfl) ⟨2593124, by rfl⟩ : syracuseStep 3457499 = 5186249) B5186249
theorem B2304999 : Blo 2303435 2304999 := bstep (se 1 (by rfl) ⟨1728749, by rfl⟩ : syracuseStep 2304999 = 3457499) B3457499
theorem B2593129 : Blo 2303435 2593129 := bbase (se 2 (by rfl) ⟨972423, by rfl⟩ : syracuseStep 2593129 = 1944847) (by norm_num)
theorem B3457505 : Blo 2303435 3457505 := bstep (se 2 (by rfl) ⟨1296564, by rfl⟩ : syracuseStep 3457505 = 2593129) B2593129
theorem B2305003 : Blo 2303435 2305003 := bstep (se 1 (by rfl) ⟨1728752, by rfl⟩ : syracuseStep 2305003 = 3457505) B3457505
theorem B11076533 : Blo 2303435 11076533 := bbase (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) (by norm_num)
theorem B7384355 : Blo 2303435 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B4922903 : Blo 2303435 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B13127741 : Blo 2303435 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B8751827 : Blo 2303435 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B5834551 : Blo 2303435 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B7779401 : Blo 2303435 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B5186267 : Blo 2303435 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B3457511 : Blo 2303435 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B2305007 : Blo 2303435 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B3457517 : Blo 2303435 3457517 := bbase (se 3 (by rfl) ⟨648284, by rfl⟩ : syracuseStep 3457517 = 1296569) (by norm_num)
theorem B2305011 : Blo 2303435 2305011 := bstep (se 1 (by rfl) ⟨1728758, by rfl⟩ : syracuseStep 2305011 = 3457517) B3457517
theorem B5186285 : Blo 2303435 5186285 := bbase (se 3 (by rfl) ⟨972428, by rfl⟩ : syracuseStep 5186285 = 1944857) (by norm_num)
theorem B3457523 : Blo 2303435 3457523 := bstep (se 1 (by rfl) ⟨2593142, by rfl⟩ : syracuseStep 3457523 = 5186285) B5186285
theorem B2305015 : Blo 2303435 2305015 := bstep (se 1 (by rfl) ⟨1728761, by rfl⟩ : syracuseStep 2305015 = 3457523) B3457523
theorem B2461465 : Blo 2303435 2461465 := bbase (se 2 (by rfl) ⟨923049, by rfl⟩ : syracuseStep 2461465 = 1846099) (by norm_num)
theorem B3281953 : Blo 2303435 3281953 := bstep (se 2 (by rfl) ⟨1230732, by rfl⟩ : syracuseStep 3281953 = 2461465) B2461465
theorem B4375937 : Blo 2303435 4375937 := bstep (se 2 (by rfl) ⟨1640976, by rfl⟩ : syracuseStep 4375937 = 3281953) B3281953
theorem B2917291 : Blo 2303435 2917291 := bstep (se 1 (by rfl) ⟨2187968, by rfl⟩ : syracuseStep 2917291 = 4375937) B4375937
theorem B3889721 : Blo 2303435 3889721 := bstep (se 2 (by rfl) ⟨1458645, by rfl⟩ : syracuseStep 3889721 = 2917291) B2917291
theorem B2593147 : Blo 2303435 2593147 := bstep (se 1 (by rfl) ⟨1944860, by rfl⟩ : syracuseStep 2593147 = 3889721) B3889721
theorem B3457529 : Blo 2303435 3457529 := bstep (se 2 (by rfl) ⟨1296573, by rfl⟩ : syracuseStep 3457529 = 2593147) B2593147
theorem B2305019 : Blo 2303435 2305019 := bstep (se 1 (by rfl) ⟨1728764, by rfl⟩ : syracuseStep 2305019 = 3457529) B3457529
theorem B11227733 : Blo 2303435 11227733 := bbase (se 8 (by rfl) ⟨65787, by rfl⟩ : syracuseStep 11227733 = 131575) (by norm_num)
theorem B7485155 : Blo 2303435 7485155 := bstep (se 1 (by rfl) ⟨5613866, by rfl⟩ : syracuseStep 7485155 = 11227733) B11227733
theorem B4990103 : Blo 2303435 4990103 := bstep (se 1 (by rfl) ⟨3742577, by rfl⟩ : syracuseStep 4990103 = 7485155) B7485155
theorem B3326735 : Blo 2303435 3326735 := bstep (se 1 (by rfl) ⟨2495051, by rfl⟩ : syracuseStep 3326735 = 4990103) B4990103
theorem B8871293 : Blo 2303435 8871293 := bstep (se 3 (by rfl) ⟨1663367, by rfl⟩ : syracuseStep 8871293 = 3326735) B3326735
theorem B23656781 : Blo 2303435 23656781 := bstep (se 3 (by rfl) ⟨4435646, by rfl⟩ : syracuseStep 23656781 = 8871293) B8871293
theorem B15771187 : Blo 2303435 15771187 := bstep (se 1 (by rfl) ⟨11828390, by rfl⟩ : syracuseStep 15771187 = 23656781) B23656781
theorem B21028249 : Blo 2303435 21028249 := bstep (se 2 (by rfl) ⟨7885593, by rfl⟩ : syracuseStep 21028249 = 15771187) B15771187
theorem B28037665 : Blo 2303435 28037665 := bstep (se 2 (by rfl) ⟨10514124, by rfl⟩ : syracuseStep 28037665 = 21028249) B21028249
theorem B37383553 : Blo 2303435 37383553 := bstep (se 2 (by rfl) ⟨14018832, by rfl⟩ : syracuseStep 37383553 = 28037665) B28037665
theorem B49844737 : Blo 2303435 49844737 := bstep (se 2 (by rfl) ⟨18691776, by rfl⟩ : syracuseStep 49844737 = 37383553) B37383553
theorem B66459649 : Blo 2303435 66459649 := bstep (se 2 (by rfl) ⟨24922368, by rfl⟩ : syracuseStep 66459649 = 49844737) B49844737
theorem B88612865 : Blo 2303435 88612865 := bstep (se 2 (by rfl) ⟨33229824, by rfl⟩ : syracuseStep 88612865 = 66459649) B66459649
theorem B59075243 : Blo 2303435 59075243 := bstep (se 1 (by rfl) ⟨44306432, by rfl⟩ : syracuseStep 59075243 = 88612865) B88612865
theorem B39383495 : Blo 2303435 39383495 := bstep (se 1 (by rfl) ⟨29537621, by rfl⟩ : syracuseStep 39383495 = 59075243) B59075243
theorem B26255663 : Blo 2303435 26255663 := bstep (se 1 (by rfl) ⟨19691747, by rfl⟩ : syracuseStep 26255663 = 39383495) B39383495
theorem B17503775 : Blo 2303435 17503775 := bstep (se 1 (by rfl) ⟨13127831, by rfl⟩ : syracuseStep 17503775 = 26255663) B26255663
theorem B11669183 : Blo 2303435 11669183 := bstep (se 1 (by rfl) ⟨8751887, by rfl⟩ : syracuseStep 11669183 = 17503775) B17503775
theorem B7779455 : Blo 2303435 7779455 := bstep (se 1 (by rfl) ⟨5834591, by rfl⟩ : syracuseStep 7779455 = 11669183) B11669183
theorem B5186303 : Blo 2303435 5186303 := bstep (se 1 (by rfl) ⟨3889727, by rfl⟩ : syracuseStep 5186303 = 7779455) B7779455
theorem B3457535 : Blo 2303435 3457535 := bstep (se 1 (by rfl) ⟨2593151, by rfl⟩ : syracuseStep 3457535 = 5186303) B5186303
theorem B2305023 : Blo 2303435 2305023 := bstep (se 1 (by rfl) ⟨1728767, by rfl⟩ : syracuseStep 2305023 = 3457535) B3457535
theorem B3457541 : Blo 2303435 3457541 := bbase (se 4 (by rfl) ⟨324144, by rfl⟩ : syracuseStep 3457541 = 648289) (by norm_num)
theorem B2305027 : Blo 2303435 2305027 := bstep (se 1 (by rfl) ⟨1728770, by rfl⟩ : syracuseStep 2305027 = 3457541) B3457541
theorem B3889741 : Blo 2303435 3889741 := bbase (se 3 (by rfl) ⟨729326, by rfl⟩ : syracuseStep 3889741 = 1458653) (by norm_num)
theorem B5186321 : Blo 2303435 5186321 := bstep (se 2 (by rfl) ⟨1944870, by rfl⟩ : syracuseStep 5186321 = 3889741) B3889741
theorem B3457547 : Blo 2303435 3457547 := bstep (se 1 (by rfl) ⟨2593160, by rfl⟩ : syracuseStep 3457547 = 5186321) B5186321
theorem B2305031 : Blo 2303435 2305031 := bstep (se 1 (by rfl) ⟨1728773, by rfl⟩ : syracuseStep 2305031 = 3457547) B3457547
theorem B2593165 : Blo 2303435 2593165 := bbase (se 3 (by rfl) ⟨486218, by rfl⟩ : syracuseStep 2593165 = 972437) (by norm_num)
theorem B3457553 : Blo 2303435 3457553 := bstep (se 2 (by rfl) ⟨1296582, by rfl⟩ : syracuseStep 3457553 = 2593165) B2593165
theorem B2305035 : Blo 2303435 2305035 := bstep (se 1 (by rfl) ⟨1728776, by rfl⟩ : syracuseStep 2305035 = 3457553) B3457553
theorem B7779509 : Blo 2303435 7779509 := bbase (se 5 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 7779509 = 729329) (by norm_num)
theorem B5186339 : Blo 2303435 5186339 := bstep (se 1 (by rfl) ⟨3889754, by rfl⟩ : syracuseStep 5186339 = 7779509) B7779509
theorem B3457559 : Blo 2303435 3457559 := bstep (se 1 (by rfl) ⟨2593169, by rfl⟩ : syracuseStep 3457559 = 5186339) B5186339
theorem B2305039 : Blo 2303435 2305039 := bstep (se 1 (by rfl) ⟨1728779, by rfl⟩ : syracuseStep 2305039 = 3457559) B3457559
theorem B3457565 : Blo 2303435 3457565 := bbase (se 3 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 3457565 = 1296587) (by norm_num)
theorem B2305043 : Blo 2303435 2305043 := bstep (se 1 (by rfl) ⟨1728782, by rfl⟩ : syracuseStep 2305043 = 3457565) B3457565
theorem B5186357 : Blo 2303435 5186357 := bbase (se 5 (by rfl) ⟨243110, by rfl⟩ : syracuseStep 5186357 = 486221) (by norm_num)
theorem B3457571 : Blo 2303435 3457571 := bstep (se 1 (by rfl) ⟨2593178, by rfl⟩ : syracuseStep 3457571 = 5186357) B5186357
theorem B2305047 : Blo 2303435 2305047 := bstep (se 1 (by rfl) ⟨1728785, by rfl⟩ : syracuseStep 2305047 = 3457571) B3457571
theorem B5000597 : Blo 2303435 5000597 := bbase (se 6 (by rfl) ⟨117201, by rfl⟩ : syracuseStep 5000597 = 234403) (by norm_num)
theorem B3333731 : Blo 2303435 3333731 := bstep (se 1 (by rfl) ⟨2500298, by rfl⟩ : syracuseStep 3333731 = 5000597) B5000597
theorem B8889949 : Blo 2303435 8889949 := bstep (se 3 (by rfl) ⟨1666865, by rfl⟩ : syracuseStep 8889949 = 3333731) B3333731
theorem B11853265 : Blo 2303435 11853265 := bstep (se 2 (by rfl) ⟨4444974, by rfl⟩ : syracuseStep 11853265 = 8889949) B8889949
theorem B15804353 : Blo 2303435 15804353 := bstep (se 2 (by rfl) ⟨5926632, by rfl⟩ : syracuseStep 15804353 = 11853265) B11853265
theorem B10536235 : Blo 2303435 10536235 := bstep (se 1 (by rfl) ⟨7902176, by rfl⟩ : syracuseStep 10536235 = 15804353) B15804353
theorem B224773013 : Blo 2303435 224773013 := bstep (se 6 (by rfl) ⟨5268117, by rfl⟩ : syracuseStep 224773013 = 10536235) B10536235
theorem B599394701 : Blo 2303435 599394701 := bstep (se 3 (by rfl) ⟨112386506, by rfl⟩ : syracuseStep 599394701 = 224773013) B224773013
theorem B1598385869 : Blo 2303435 1598385869 := bstep (se 3 (by rfl) ⟨299697350, by rfl⟩ : syracuseStep 1598385869 = 599394701) B599394701
theorem B1065590579 : Blo 2303435 1065590579 := bstep (se 1 (by rfl) ⟨799192934, by rfl⟩ : syracuseStep 1065590579 = 1598385869) B1598385869
theorem B2841574877 : Blo 2303435 2841574877 := bstep (se 3 (by rfl) ⟨532795289, by rfl⟩ : syracuseStep 2841574877 = 1065590579) B1065590579
theorem B1894383251 : Blo 2303435 1894383251 := bstep (se 1 (by rfl) ⟨1420787438, by rfl⟩ : syracuseStep 1894383251 = 2841574877) B2841574877
theorem B1262922167 : Blo 2303435 1262922167 := bstep (se 1 (by rfl) ⟨947191625, by rfl⟩ : syracuseStep 1262922167 = 1894383251) B1894383251
theorem B841948111 : Blo 2303435 841948111 := bstep (se 1 (by rfl) ⟨631461083, by rfl⟩ : syracuseStep 841948111 = 1262922167) B1262922167
theorem B1122597481 : Blo 2303435 1122597481 := bstep (se 2 (by rfl) ⟨420974055, by rfl⟩ : syracuseStep 1122597481 = 841948111) B841948111
theorem B1496796641 : Blo 2303435 1496796641 := bstep (se 2 (by rfl) ⟨561298740, by rfl⟩ : syracuseStep 1496796641 = 1122597481) B1122597481
theorem B997864427 : Blo 2303435 997864427 := bstep (se 1 (by rfl) ⟨748398320, by rfl⟩ : syracuseStep 997864427 = 1496796641) B1496796641
theorem B665242951 : Blo 2303435 665242951 := bstep (se 1 (by rfl) ⟨498932213, by rfl⟩ : syracuseStep 665242951 = 997864427) B997864427
theorem B886990601 : Blo 2303435 886990601 := bstep (se 2 (by rfl) ⟨332621475, by rfl⟩ : syracuseStep 886990601 = 665242951) B665242951
theorem B591327067 : Blo 2303435 591327067 := bstep (se 1 (by rfl) ⟨443495300, by rfl⟩ : syracuseStep 591327067 = 886990601) B886990601
theorem B788436089 : Blo 2303435 788436089 := bstep (se 2 (by rfl) ⟨295663533, by rfl⟩ : syracuseStep 788436089 = 591327067) B591327067
theorem B525624059 : Blo 2303435 525624059 := bstep (se 1 (by rfl) ⟨394218044, by rfl⟩ : syracuseStep 525624059 = 788436089) B788436089
theorem B350416039 : Blo 2303435 350416039 := bstep (se 1 (by rfl) ⟨262812029, by rfl⟩ : syracuseStep 350416039 = 525624059) B525624059
theorem B467221385 : Blo 2303435 467221385 := bstep (se 2 (by rfl) ⟨175208019, by rfl⟩ : syracuseStep 467221385 = 350416039) B350416039
theorem B311480923 : Blo 2303435 311480923 := bstep (se 1 (by rfl) ⟨233610692, by rfl⟩ : syracuseStep 311480923 = 467221385) B467221385
theorem B415307897 : Blo 2303435 415307897 := bstep (se 2 (by rfl) ⟨155740461, by rfl⟩ : syracuseStep 415307897 = 311480923) B311480923
theorem B276871931 : Blo 2303435 276871931 := bstep (se 1 (by rfl) ⟨207653948, by rfl⟩ : syracuseStep 276871931 = 415307897) B415307897
theorem B184581287 : Blo 2303435 184581287 := bstep (se 1 (by rfl) ⟨138435965, by rfl⟩ : syracuseStep 184581287 = 276871931) B276871931
theorem B123054191 : Blo 2303435 123054191 := bstep (se 1 (by rfl) ⟨92290643, by rfl⟩ : syracuseStep 123054191 = 184581287) B184581287
theorem B82036127 : Blo 2303435 82036127 := bstep (se 1 (by rfl) ⟨61527095, by rfl⟩ : syracuseStep 82036127 = 123054191) B123054191
theorem B54690751 : Blo 2303435 54690751 := bstep (se 1 (by rfl) ⟨41018063, by rfl⟩ : syracuseStep 54690751 = 82036127) B82036127
theorem B72921001 : Blo 2303435 72921001 := bstep (se 2 (by rfl) ⟨27345375, by rfl⟩ : syracuseStep 72921001 = 54690751) B54690751
theorem B97228001 : Blo 2303435 97228001 := bstep (se 2 (by rfl) ⟨36460500, by rfl⟩ : syracuseStep 97228001 = 72921001) B72921001
theorem B64818667 : Blo 2303435 64818667 := bstep (se 1 (by rfl) ⟨48614000, by rfl⟩ : syracuseStep 64818667 = 97228001) B97228001
theorem B86424889 : Blo 2303435 86424889 := bstep (se 2 (by rfl) ⟨32409333, by rfl⟩ : syracuseStep 86424889 = 64818667) B64818667
theorem B115233185 : Blo 2303435 115233185 := bstep (se 2 (by rfl) ⟨43212444, by rfl⟩ : syracuseStep 115233185 = 86424889) B86424889
theorem B76822123 : Blo 2303435 76822123 := bstep (se 1 (by rfl) ⟨57616592, by rfl⟩ : syracuseStep 76822123 = 115233185) B115233185
theorem B102429497 : Blo 2303435 102429497 := bstep (se 2 (by rfl) ⟨38411061, by rfl⟩ : syracuseStep 102429497 = 76822123) B76822123
theorem B68286331 : Blo 2303435 68286331 := bstep (se 1 (by rfl) ⟨51214748, by rfl⟩ : syracuseStep 68286331 = 102429497) B102429497
theorem B364193765 : Blo 2303435 364193765 := bstep (se 4 (by rfl) ⟨34143165, by rfl⟩ : syracuseStep 364193765 = 68286331) B68286331
theorem B242795843 : Blo 2303435 242795843 := bstep (se 1 (by rfl) ⟨182096882, by rfl⟩ : syracuseStep 242795843 = 364193765) B364193765
theorem B161863895 : Blo 2303435 161863895 := bstep (se 1 (by rfl) ⟨121397921, by rfl⟩ : syracuseStep 161863895 = 242795843) B242795843
theorem B107909263 : Blo 2303435 107909263 := bstep (se 1 (by rfl) ⟨80931947, by rfl⟩ : syracuseStep 107909263 = 161863895) B161863895
theorem B143879017 : Blo 2303435 143879017 := bstep (se 2 (by rfl) ⟨53954631, by rfl⟩ : syracuseStep 143879017 = 107909263) B107909263
theorem B191838689 : Blo 2303435 191838689 := bstep (se 2 (by rfl) ⟨71939508, by rfl⟩ : syracuseStep 191838689 = 143879017) B143879017
theorem B127892459 : Blo 2303435 127892459 := bstep (se 1 (by rfl) ⟨95919344, by rfl⟩ : syracuseStep 127892459 = 191838689) B191838689
theorem B341046557 : Blo 2303435 341046557 := bstep (se 3 (by rfl) ⟨63946229, by rfl⟩ : syracuseStep 341046557 = 127892459) B127892459
theorem B227364371 : Blo 2303435 227364371 := bstep (se 1 (by rfl) ⟨170523278, by rfl⟩ : syracuseStep 227364371 = 341046557) B341046557
theorem B151576247 : Blo 2303435 151576247 := bstep (se 1 (by rfl) ⟨113682185, by rfl⟩ : syracuseStep 151576247 = 227364371) B227364371
theorem B101050831 : Blo 2303435 101050831 := bstep (se 1 (by rfl) ⟨75788123, by rfl⟩ : syracuseStep 101050831 = 151576247) B151576247
theorem B134734441 : Blo 2303435 134734441 := bstep (se 2 (by rfl) ⟨50525415, by rfl⟩ : syracuseStep 134734441 = 101050831) B101050831
theorem B179645921 : Blo 2303435 179645921 := bstep (se 2 (by rfl) ⟨67367220, by rfl⟩ : syracuseStep 179645921 = 134734441) B134734441
theorem B119763947 : Blo 2303435 119763947 := bstep (se 1 (by rfl) ⟨89822960, by rfl⟩ : syracuseStep 119763947 = 179645921) B179645921
theorem B79842631 : Blo 2303435 79842631 := bstep (se 1 (by rfl) ⟨59881973, by rfl⟩ : syracuseStep 79842631 = 119763947) B119763947
theorem B106456841 : Blo 2303435 106456841 := bstep (se 2 (by rfl) ⟨39921315, by rfl⟩ : syracuseStep 106456841 = 79842631) B79842631
theorem B70971227 : Blo 2303435 70971227 := bstep (se 1 (by rfl) ⟨53228420, by rfl⟩ : syracuseStep 70971227 = 106456841) B106456841
theorem B47314151 : Blo 2303435 47314151 := bstep (se 1 (by rfl) ⟨35485613, by rfl⟩ : syracuseStep 47314151 = 70971227) B70971227
theorem B31542767 : Blo 2303435 31542767 := bstep (se 1 (by rfl) ⟨23657075, by rfl⟩ : syracuseStep 31542767 = 47314151) B47314151
theorem B21028511 : Blo 2303435 21028511 := bstep (se 1 (by rfl) ⟨15771383, by rfl⟩ : syracuseStep 21028511 = 31542767) B31542767
theorem B14019007 : Blo 2303435 14019007 := bstep (se 1 (by rfl) ⟨10514255, by rfl⟩ : syracuseStep 14019007 = 21028511) B21028511
theorem B18692009 : Blo 2303435 18692009 := bstep (se 2 (by rfl) ⟨7009503, by rfl⟩ : syracuseStep 18692009 = 14019007) B14019007
theorem B12461339 : Blo 2303435 12461339 := bstep (se 1 (by rfl) ⟨9346004, by rfl⟩ : syracuseStep 12461339 = 18692009) B18692009
theorem B8307559 : Blo 2303435 8307559 := bstep (se 1 (by rfl) ⟨6230669, by rfl⟩ : syracuseStep 8307559 = 12461339) B12461339
theorem B11076745 : Blo 2303435 11076745 := bstep (se 2 (by rfl) ⟨4153779, by rfl⟩ : syracuseStep 11076745 = 8307559) B8307559
theorem B14768993 : Blo 2303435 14768993 := bstep (se 2 (by rfl) ⟨5538372, by rfl⟩ : syracuseStep 14768993 = 11076745) B11076745
theorem B9845995 : Blo 2303435 9845995 := bstep (se 1 (by rfl) ⟨7384496, by rfl⟩ : syracuseStep 9845995 = 14768993) B14768993
theorem B13127993 : Blo 2303435 13127993 := bstep (se 2 (by rfl) ⟨4922997, by rfl⟩ : syracuseStep 13127993 = 9845995) B9845995
theorem B8751995 : Blo 2303435 8751995 := bstep (se 1 (by rfl) ⟨6563996, by rfl⟩ : syracuseStep 8751995 = 13127993) B13127993
theorem B5834663 : Blo 2303435 5834663 := bstep (se 1 (by rfl) ⟨4375997, by rfl⟩ : syracuseStep 5834663 = 8751995) B8751995
theorem B3889775 : Blo 2303435 3889775 := bstep (se 1 (by rfl) ⟨2917331, by rfl⟩ : syracuseStep 3889775 = 5834663) B5834663
theorem B2593183 : Blo 2303435 2593183 := bstep (se 1 (by rfl) ⟨1944887, by rfl⟩ : syracuseStep 2593183 = 3889775) B3889775
theorem B3457577 : Blo 2303435 3457577 := bstep (se 2 (by rfl) ⟨1296591, by rfl⟩ : syracuseStep 3457577 = 2593183) B2593183
theorem B2305051 : Blo 2303435 2305051 := bstep (se 1 (by rfl) ⟨1728788, by rfl⟩ : syracuseStep 2305051 = 3457577) B3457577
theorem B8420917 : Blo 2303435 8420917 := bbase (se 5 (by rfl) ⟨394730, by rfl⟩ : syracuseStep 8420917 = 789461) (by norm_num)
theorem B11227889 : Blo 2303435 11227889 := bstep (se 2 (by rfl) ⟨4210458, by rfl⟩ : syracuseStep 11227889 = 8420917) B8420917
theorem B7485259 : Blo 2303435 7485259 := bstep (se 1 (by rfl) ⟨5613944, by rfl⟩ : syracuseStep 7485259 = 11227889) B11227889
theorem B9980345 : Blo 2303435 9980345 := bstep (se 2 (by rfl) ⟨3742629, by rfl⟩ : syracuseStep 9980345 = 7485259) B7485259
theorem B26614253 : Blo 2303435 26614253 := bstep (se 3 (by rfl) ⟨4990172, by rfl⟩ : syracuseStep 26614253 = 9980345) B9980345
theorem B17742835 : Blo 2303435 17742835 := bstep (se 1 (by rfl) ⟨13307126, by rfl⟩ : syracuseStep 17742835 = 26614253) B26614253
theorem B23657113 : Blo 2303435 23657113 := bstep (se 2 (by rfl) ⟨8871417, by rfl⟩ : syracuseStep 23657113 = 17742835) B17742835
theorem B31542817 : Blo 2303435 31542817 := bstep (se 2 (by rfl) ⟨11828556, by rfl⟩ : syracuseStep 31542817 = 23657113) B23657113
theorem B42057089 : Blo 2303435 42057089 := bstep (se 2 (by rfl) ⟨15771408, by rfl⟩ : syracuseStep 42057089 = 31542817) B31542817
theorem B28038059 : Blo 2303435 28038059 := bstep (se 1 (by rfl) ⟨21028544, by rfl⟩ : syracuseStep 28038059 = 42057089) B42057089
theorem B18692039 : Blo 2303435 18692039 := bstep (se 1 (by rfl) ⟨14019029, by rfl⟩ : syracuseStep 18692039 = 28038059) B28038059
theorem B12461359 : Blo 2303435 12461359 := bstep (se 1 (by rfl) ⟨9346019, by rfl⟩ : syracuseStep 12461359 = 18692039) B18692039
theorem B16615145 : Blo 2303435 16615145 := bstep (se 2 (by rfl) ⟨6230679, by rfl⟩ : syracuseStep 16615145 = 12461359) B12461359
theorem B11076763 : Blo 2303435 11076763 := bstep (se 1 (by rfl) ⟨8307572, by rfl⟩ : syracuseStep 11076763 = 16615145) B16615145
theorem B14769017 : Blo 2303435 14769017 := bstep (se 2 (by rfl) ⟨5538381, by rfl⟩ : syracuseStep 14769017 = 11076763) B11076763
theorem B9846011 : Blo 2303435 9846011 := bstep (se 1 (by rfl) ⟨7384508, by rfl⟩ : syracuseStep 9846011 = 14769017) B14769017
theorem B6564007 : Blo 2303435 6564007 := bstep (se 1 (by rfl) ⟨4923005, by rfl⟩ : syracuseStep 6564007 = 9846011) B9846011
theorem B8752009 : Blo 2303435 8752009 := bstep (se 2 (by rfl) ⟨3282003, by rfl⟩ : syracuseStep 8752009 = 6564007) B6564007
theorem B11669345 : Blo 2303435 11669345 := bstep (se 2 (by rfl) ⟨4376004, by rfl⟩ : syracuseStep 11669345 = 8752009) B8752009
theorem B7779563 : Blo 2303435 7779563 := bstep (se 1 (by rfl) ⟨5834672, by rfl⟩ : syracuseStep 7779563 = 11669345) B11669345
theorem B5186375 : Blo 2303435 5186375 := bstep (se 1 (by rfl) ⟨3889781, by rfl⟩ : syracuseStep 5186375 = 7779563) B7779563
theorem B3457583 : Blo 2303435 3457583 := bstep (se 1 (by rfl) ⟨2593187, by rfl⟩ : syracuseStep 3457583 = 5186375) B5186375
theorem B2305055 : Blo 2303435 2305055 := bstep (se 1 (by rfl) ⟨1728791, by rfl⟩ : syracuseStep 2305055 = 3457583) B3457583
theorem B3457589 : Blo 2303435 3457589 := bbase (se 5 (by rfl) ⟨162074, by rfl⟩ : syracuseStep 3457589 = 324149) (by norm_num)
theorem B2305059 : Blo 2303435 2305059 := bstep (se 1 (by rfl) ⟨1728794, by rfl⟩ : syracuseStep 2305059 = 3457589) B3457589
theorem B5834693 : Blo 2303435 5834693 := bbase (se 4 (by rfl) ⟨547002, by rfl⟩ : syracuseStep 5834693 = 1094005) (by norm_num)
theorem B3889795 : Blo 2303435 3889795 := bstep (se 1 (by rfl) ⟨2917346, by rfl⟩ : syracuseStep 3889795 = 5834693) B5834693
theorem B5186393 : Blo 2303435 5186393 := bstep (se 2 (by rfl) ⟨1944897, by rfl⟩ : syracuseStep 5186393 = 3889795) B3889795
theorem B3457595 : Blo 2303435 3457595 := bstep (se 1 (by rfl) ⟨2593196, by rfl⟩ : syracuseStep 3457595 = 5186393) B5186393
theorem B2305063 : Blo 2303435 2305063 := bstep (se 1 (by rfl) ⟨1728797, by rfl⟩ : syracuseStep 2305063 = 3457595) B3457595
theorem B2593201 : Blo 2303435 2593201 := bbase (se 2 (by rfl) ⟨972450, by rfl⟩ : syracuseStep 2593201 = 1944901) (by norm_num)
theorem B3457601 : Blo 2303435 3457601 := bstep (se 2 (by rfl) ⟨1296600, by rfl⟩ : syracuseStep 3457601 = 2593201) B2593201
theorem B2305067 : Blo 2303435 2305067 := bstep (se 1 (by rfl) ⟨1728800, by rfl⟩ : syracuseStep 2305067 = 3457601) B3457601
theorem B6564053 : Blo 2303435 6564053 := bbase (se 7 (by rfl) ⟨76922, by rfl⟩ : syracuseStep 6564053 = 153845) (by norm_num)
theorem B4376035 : Blo 2303435 4376035 := bstep (se 1 (by rfl) ⟨3282026, by rfl⟩ : syracuseStep 4376035 = 6564053) B6564053
theorem B5834713 : Blo 2303435 5834713 := bstep (se 2 (by rfl) ⟨2188017, by rfl⟩ : syracuseStep 5834713 = 4376035) B4376035
theorem B7779617 : Blo 2303435 7779617 := bstep (se 2 (by rfl) ⟨2917356, by rfl⟩ : syracuseStep 7779617 = 5834713) B5834713
theorem B5186411 : Blo 2303435 5186411 := bstep (se 1 (by rfl) ⟨3889808, by rfl⟩ : syracuseStep 5186411 = 7779617) B7779617
theorem B3457607 : Blo 2303435 3457607 := bstep (se 1 (by rfl) ⟨2593205, by rfl⟩ : syracuseStep 3457607 = 5186411) B5186411
theorem B2305071 : Blo 2303435 2305071 := bstep (se 1 (by rfl) ⟨1728803, by rfl⟩ : syracuseStep 2305071 = 3457607) B3457607
theorem B3457613 : Blo 2303435 3457613 := bbase (se 3 (by rfl) ⟨648302, by rfl⟩ : syracuseStep 3457613 = 1296605) (by norm_num)
theorem B2305075 : Blo 2303435 2305075 := bstep (se 1 (by rfl) ⟨1728806, by rfl⟩ : syracuseStep 2305075 = 3457613) B3457613
theorem B5186429 : Blo 2303435 5186429 := bbase (se 3 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 5186429 = 1944911) (by norm_num)
theorem B3457619 : Blo 2303435 3457619 := bstep (se 1 (by rfl) ⟨2593214, by rfl⟩ : syracuseStep 3457619 = 5186429) B5186429
theorem B2305079 : Blo 2303435 2305079 := bstep (se 1 (by rfl) ⟨1728809, by rfl⟩ : syracuseStep 2305079 = 3457619) B3457619
theorem B3889829 : Blo 2303435 3889829 := bbase (se 4 (by rfl) ⟨364671, by rfl⟩ : syracuseStep 3889829 = 729343) (by norm_num)
theorem B2593219 : Blo 2303435 2593219 := bstep (se 1 (by rfl) ⟨1944914, by rfl⟩ : syracuseStep 2593219 = 3889829) B3889829
theorem B3457625 : Blo 2303435 3457625 := bstep (se 2 (by rfl) ⟨1296609, by rfl⟩ : syracuseStep 3457625 = 2593219) B2593219
theorem B2305083 : Blo 2303435 2305083 := bstep (se 1 (by rfl) ⟨1728812, by rfl⟩ : syracuseStep 2305083 = 3457625) B3457625
theorem B2461537 : Blo 2303435 2461537 := bbase (se 2 (by rfl) ⟨923076, by rfl⟩ : syracuseStep 2461537 = 1846153) (by norm_num)
theorem B3282049 : Blo 2303435 3282049 := bstep (se 2 (by rfl) ⟨1230768, by rfl⟩ : syracuseStep 3282049 = 2461537) B2461537
theorem B17504261 : Blo 2303435 17504261 := bstep (se 4 (by rfl) ⟨1641024, by rfl⟩ : syracuseStep 17504261 = 3282049) B3282049
theorem B11669507 : Blo 2303435 11669507 := bstep (se 1 (by rfl) ⟨8752130, by rfl⟩ : syracuseStep 11669507 = 17504261) B17504261
theorem B7779671 : Blo 2303435 7779671 := bstep (se 1 (by rfl) ⟨5834753, by rfl⟩ : syracuseStep 7779671 = 11669507) B11669507
theorem B5186447 : Blo 2303435 5186447 := bstep (se 1 (by rfl) ⟨3889835, by rfl⟩ : syracuseStep 5186447 = 7779671) B7779671
theorem B3457631 : Blo 2303435 3457631 := bstep (se 1 (by rfl) ⟨2593223, by rfl⟩ : syracuseStep 3457631 = 5186447) B5186447
theorem B2305087 : Blo 2303435 2305087 := bstep (se 1 (by rfl) ⟨1728815, by rfl⟩ : syracuseStep 2305087 = 3457631) B3457631
theorem B3457637 : Blo 2303435 3457637 := bbase (se 4 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 3457637 = 648307) (by norm_num)
theorem B2305091 : Blo 2303435 2305091 := bstep (se 1 (by rfl) ⟨1728818, by rfl⟩ : syracuseStep 2305091 = 3457637) B3457637
theorem B3282061 : Blo 2303435 3282061 := bbase (se 3 (by rfl) ⟨615386, by rfl⟩ : syracuseStep 3282061 = 1230773) (by norm_num)
theorem B4376081 : Blo 2303435 4376081 := bstep (se 2 (by rfl) ⟨1641030, by rfl⟩ : syracuseStep 4376081 = 3282061) B3282061
theorem B2917387 : Blo 2303435 2917387 := bstep (se 1 (by rfl) ⟨2188040, by rfl⟩ : syracuseStep 2917387 = 4376081) B4376081
theorem B3889849 : Blo 2303435 3889849 := bstep (se 2 (by rfl) ⟨1458693, by rfl⟩ : syracuseStep 3889849 = 2917387) B2917387
theorem B5186465 : Blo 2303435 5186465 := bstep (se 2 (by rfl) ⟨1944924, by rfl⟩ : syracuseStep 5186465 = 3889849) B3889849
theorem B3457643 : Blo 2303435 3457643 := bstep (se 1 (by rfl) ⟨2593232, by rfl⟩ : syracuseStep 3457643 = 5186465) B5186465
theorem B2305095 : Blo 2303435 2305095 := bstep (se 1 (by rfl) ⟨1728821, by rfl⟩ : syracuseStep 2305095 = 3457643) B3457643
theorem B2593237 : Blo 2303435 2593237 := bbase (se 7 (by rfl) ⟨30389, by rfl⟩ : syracuseStep 2593237 = 60779) (by norm_num)
theorem B3457649 : Blo 2303435 3457649 := bstep (se 2 (by rfl) ⟨1296618, by rfl⟩ : syracuseStep 3457649 = 2593237) B2593237
theorem B2305099 : Blo 2303435 2305099 := bstep (se 1 (by rfl) ⟨1728824, by rfl⟩ : syracuseStep 2305099 = 3457649) B3457649
theorem B2917397 : Blo 2303435 2917397 := bbase (se 6 (by rfl) ⟨68376, by rfl⟩ : syracuseStep 2917397 = 136753) (by norm_num)
theorem B7779725 : Blo 2303435 7779725 := bstep (se 3 (by rfl) ⟨1458698, by rfl⟩ : syracuseStep 7779725 = 2917397) B2917397
theorem B5186483 : Blo 2303435 5186483 := bstep (se 1 (by rfl) ⟨3889862, by rfl⟩ : syracuseStep 5186483 = 7779725) B7779725
theorem B3457655 : Blo 2303435 3457655 := bstep (se 1 (by rfl) ⟨2593241, by rfl⟩ : syracuseStep 3457655 = 5186483) B5186483
theorem B2305103 : Blo 2303435 2305103 := bstep (se 1 (by rfl) ⟨1728827, by rfl⟩ : syracuseStep 2305103 = 3457655) B3457655
theorem B3457661 : Blo 2303435 3457661 := bbase (se 3 (by rfl) ⟨648311, by rfl⟩ : syracuseStep 3457661 = 1296623) (by norm_num)
theorem B2305107 : Blo 2303435 2305107 := bstep (se 1 (by rfl) ⟨1728830, by rfl⟩ : syracuseStep 2305107 = 3457661) B3457661
theorem B5186501 : Blo 2303435 5186501 := bbase (se 4 (by rfl) ⟨486234, by rfl⟩ : syracuseStep 5186501 = 972469) (by norm_num)
theorem B3457667 : Blo 2303435 3457667 := bstep (se 1 (by rfl) ⟨2593250, by rfl⟩ : syracuseStep 3457667 = 5186501) B5186501
theorem B2305111 : Blo 2303435 2305111 := bstep (se 1 (by rfl) ⟨1728833, by rfl⟩ : syracuseStep 2305111 = 3457667) B3457667
theorem B10514549 : Blo 2303435 10514549 := bbase (se 5 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 10514549 = 985739) (by norm_num)
theorem B28038797 : Blo 2303435 28038797 := bstep (se 3 (by rfl) ⟨5257274, by rfl⟩ : syracuseStep 28038797 = 10514549) B10514549
theorem B18692531 : Blo 2303435 18692531 := bstep (se 1 (by rfl) ⟨14019398, by rfl⟩ : syracuseStep 18692531 = 28038797) B28038797
theorem B12461687 : Blo 2303435 12461687 := bstep (se 1 (by rfl) ⟨9346265, by rfl⟩ : syracuseStep 12461687 = 18692531) B18692531
theorem B8307791 : Blo 2303435 8307791 := bstep (se 1 (by rfl) ⟨6230843, by rfl⟩ : syracuseStep 8307791 = 12461687) B12461687
theorem B5538527 : Blo 2303435 5538527 := bstep (se 1 (by rfl) ⟨4153895, by rfl⟩ : syracuseStep 5538527 = 8307791) B8307791
theorem B3692351 : Blo 2303435 3692351 := bstep (se 1 (by rfl) ⟨2769263, by rfl⟩ : syracuseStep 3692351 = 5538527) B5538527
theorem B9846269 : Blo 2303435 9846269 := bstep (se 3 (by rfl) ⟨1846175, by rfl⟩ : syracuseStep 9846269 = 3692351) B3692351
theorem B6564179 : Blo 2303435 6564179 := bstep (se 1 (by rfl) ⟨4923134, by rfl⟩ : syracuseStep 6564179 = 9846269) B9846269
theorem B4376119 : Blo 2303435 4376119 := bstep (se 1 (by rfl) ⟨3282089, by rfl⟩ : syracuseStep 4376119 = 6564179) B6564179
theorem B5834825 : Blo 2303435 5834825 := bstep (se 2 (by rfl) ⟨2188059, by rfl⟩ : syracuseStep 5834825 = 4376119) B4376119
theorem B3889883 : Blo 2303435 3889883 := bstep (se 1 (by rfl) ⟨2917412, by rfl⟩ : syracuseStep 3889883 = 5834825) B5834825
theorem B2593255 : Blo 2303435 2593255 := bstep (se 1 (by rfl) ⟨1944941, by rfl⟩ : syracuseStep 2593255 = 3889883) B3889883
theorem B3457673 : Blo 2303435 3457673 := bstep (se 2 (by rfl) ⟨1296627, by rfl⟩ : syracuseStep 3457673 = 2593255) B2593255
theorem B2305115 : Blo 2303435 2305115 := bstep (se 1 (by rfl) ⟨1728836, by rfl⟩ : syracuseStep 2305115 = 3457673) B3457673
theorem B11669669 : Blo 2303435 11669669 := bbase (se 4 (by rfl) ⟨1094031, by rfl⟩ : syracuseStep 11669669 = 2188063) (by norm_num)
theorem B7779779 : Blo 2303435 7779779 := bstep (se 1 (by rfl) ⟨5834834, by rfl⟩ : syracuseStep 7779779 = 11669669) B11669669
theorem B5186519 : Blo 2303435 5186519 := bstep (se 1 (by rfl) ⟨3889889, by rfl⟩ : syracuseStep 5186519 = 7779779) B7779779
theorem B3457679 : Blo 2303435 3457679 := bstep (se 1 (by rfl) ⟨2593259, by rfl⟩ : syracuseStep 3457679 = 5186519) B5186519
theorem B2305119 : Blo 2303435 2305119 := bstep (se 1 (by rfl) ⟨1728839, by rfl⟩ : syracuseStep 2305119 = 3457679) B3457679
theorem B3457685 : Blo 2303435 3457685 := bbase (se 6 (by rfl) ⟨81039, by rfl⟩ : syracuseStep 3457685 = 162079) (by norm_num)
theorem B2305123 : Blo 2303435 2305123 := bstep (se 1 (by rfl) ⟨1728842, by rfl⟩ : syracuseStep 2305123 = 3457685) B3457685
theorem B29941973 : Blo 2303435 29941973 := bbase (se 7 (by rfl) ⟨350882, by rfl⟩ : syracuseStep 29941973 = 701765) (by norm_num)
theorem B19961315 : Blo 2303435 19961315 := bstep (se 1 (by rfl) ⟨14970986, by rfl⟩ : syracuseStep 19961315 = 29941973) B29941973
theorem B13307543 : Blo 2303435 13307543 := bstep (se 1 (by rfl) ⟨9980657, by rfl⟩ : syracuseStep 13307543 = 19961315) B19961315
theorem B8871695 : Blo 2303435 8871695 := bstep (se 1 (by rfl) ⟨6653771, by rfl⟩ : syracuseStep 8871695 = 13307543) B13307543
theorem B5914463 : Blo 2303435 5914463 := bstep (se 1 (by rfl) ⟨4435847, by rfl⟩ : syracuseStep 5914463 = 8871695) B8871695
theorem B63087605 : Blo 2303435 63087605 := bstep (se 5 (by rfl) ⟨2957231, by rfl⟩ : syracuseStep 63087605 = 5914463) B5914463
theorem B42058403 : Blo 2303435 42058403 := bstep (se 1 (by rfl) ⟨31543802, by rfl⟩ : syracuseStep 42058403 = 63087605) B63087605
theorem B28038935 : Blo 2303435 28038935 := bstep (se 1 (by rfl) ⟨21029201, by rfl⟩ : syracuseStep 28038935 = 42058403) B42058403
theorem B18692623 : Blo 2303435 18692623 := bstep (se 1 (by rfl) ⟨14019467, by rfl⟩ : syracuseStep 18692623 = 28038935) B28038935
theorem B24923497 : Blo 2303435 24923497 := bstep (se 2 (by rfl) ⟨9346311, by rfl⟩ : syracuseStep 24923497 = 18692623) B18692623
theorem B33231329 : Blo 2303435 33231329 := bstep (se 2 (by rfl) ⟨12461748, by rfl⟩ : syracuseStep 33231329 = 24923497) B24923497
theorem B22154219 : Blo 2303435 22154219 := bstep (se 1 (by rfl) ⟨16615664, by rfl⟩ : syracuseStep 22154219 = 33231329) B33231329
theorem B14769479 : Blo 2303435 14769479 := bstep (se 1 (by rfl) ⟨11077109, by rfl⟩ : syracuseStep 14769479 = 22154219) B22154219
theorem B9846319 : Blo 2303435 9846319 := bstep (se 1 (by rfl) ⟨7384739, by rfl⟩ : syracuseStep 9846319 = 14769479) B14769479
theorem B13128425 : Blo 2303435 13128425 := bstep (se 2 (by rfl) ⟨4923159, by rfl⟩ : syracuseStep 13128425 = 9846319) B9846319
theorem B8752283 : Blo 2303435 8752283 := bstep (se 1 (by rfl) ⟨6564212, by rfl⟩ : syracuseStep 8752283 = 13128425) B13128425
theorem B5834855 : Blo 2303435 5834855 := bstep (se 1 (by rfl) ⟨4376141, by rfl⟩ : syracuseStep 5834855 = 8752283) B8752283
theorem B3889903 : Blo 2303435 3889903 := bstep (se 1 (by rfl) ⟨2917427, by rfl⟩ : syracuseStep 3889903 = 5834855) B5834855
theorem B5186537 : Blo 2303435 5186537 := bstep (se 2 (by rfl) ⟨1944951, by rfl⟩ : syracuseStep 5186537 = 3889903) B3889903
theorem B3457691 : Blo 2303435 3457691 := bstep (se 1 (by rfl) ⟨2593268, by rfl⟩ : syracuseStep 3457691 = 5186537) B5186537
theorem B2305127 : Blo 2303435 2305127 := bstep (se 1 (by rfl) ⟨1728845, by rfl⟩ : syracuseStep 2305127 = 3457691) B3457691
theorem B2593273 : Blo 2303435 2593273 := bbase (se 2 (by rfl) ⟨972477, by rfl⟩ : syracuseStep 2593273 = 1944955) (by norm_num)
theorem B3457697 : Blo 2303435 3457697 := bstep (se 2 (by rfl) ⟨1296636, by rfl⟩ : syracuseStep 3457697 = 2593273) B2593273
theorem B2305131 : Blo 2303435 2305131 := bstep (se 1 (by rfl) ⟨1728848, by rfl⟩ : syracuseStep 2305131 = 3457697) B3457697
theorem B4673173 : Blo 2303435 4673173 := bbase (se 6 (by rfl) ⟨109527, by rfl⟩ : syracuseStep 4673173 = 219055) (by norm_num)
theorem B6230897 : Blo 2303435 6230897 := bstep (se 2 (by rfl) ⟨2336586, by rfl⟩ : syracuseStep 6230897 = 4673173) B4673173
theorem B4153931 : Blo 2303435 4153931 := bstep (se 1 (by rfl) ⟨3115448, by rfl⟩ : syracuseStep 4153931 = 6230897) B6230897
theorem B2769287 : Blo 2303435 2769287 := bstep (se 1 (by rfl) ⟨2076965, by rfl⟩ : syracuseStep 2769287 = 4153931) B4153931
theorem B7384765 : Blo 2303435 7384765 := bstep (se 3 (by rfl) ⟨1384643, by rfl⟩ : syracuseStep 7384765 = 2769287) B2769287
theorem B9846353 : Blo 2303435 9846353 := bstep (se 2 (by rfl) ⟨3692382, by rfl⟩ : syracuseStep 9846353 = 7384765) B7384765
theorem B6564235 : Blo 2303435 6564235 := bstep (se 1 (by rfl) ⟨4923176, by rfl⟩ : syracuseStep 6564235 = 9846353) B9846353
theorem B8752313 : Blo 2303435 8752313 := bstep (se 2 (by rfl) ⟨3282117, by rfl⟩ : syracuseStep 8752313 = 6564235) B6564235
theorem B5834875 : Blo 2303435 5834875 := bstep (se 1 (by rfl) ⟨4376156, by rfl⟩ : syracuseStep 5834875 = 8752313) B8752313
theorem B7779833 : Blo 2303435 7779833 := bstep (se 2 (by rfl) ⟨2917437, by rfl⟩ : syracuseStep 7779833 = 5834875) B5834875
theorem B5186555 : Blo 2303435 5186555 := bstep (se 1 (by rfl) ⟨3889916, by rfl⟩ : syracuseStep 5186555 = 7779833) B7779833
theorem B3457703 : Blo 2303435 3457703 := bstep (se 1 (by rfl) ⟨2593277, by rfl⟩ : syracuseStep 3457703 = 5186555) B5186555
theorem B2305135 : Blo 2303435 2305135 := bstep (se 1 (by rfl) ⟨1728851, by rfl⟩ : syracuseStep 2305135 = 3457703) B3457703
theorem B3457709 : Blo 2303435 3457709 := bbase (se 3 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 3457709 = 1296641) (by norm_num)
theorem B2305139 : Blo 2303435 2305139 := bstep (se 1 (by rfl) ⟨1728854, by rfl⟩ : syracuseStep 2305139 = 3457709) B3457709
theorem B5186573 : Blo 2303435 5186573 := bbase (se 3 (by rfl) ⟨972482, by rfl⟩ : syracuseStep 5186573 = 1944965) (by norm_num)
theorem B3457715 : Blo 2303435 3457715 := bstep (se 1 (by rfl) ⟨2593286, by rfl⟩ : syracuseStep 3457715 = 5186573) B5186573
theorem B2305143 : Blo 2303435 2305143 := bstep (se 1 (by rfl) ⟨1728857, by rfl⟩ : syracuseStep 2305143 = 3457715) B3457715
theorem B2917453 : Blo 2303435 2917453 := bbase (se 3 (by rfl) ⟨547022, by rfl⟩ : syracuseStep 2917453 = 1094045) (by norm_num)
theorem B3889937 : Blo 2303435 3889937 := bstep (se 2 (by rfl) ⟨1458726, by rfl⟩ : syracuseStep 3889937 = 2917453) B2917453
theorem B2593291 : Blo 2303435 2593291 := bstep (se 1 (by rfl) ⟨1944968, by rfl⟩ : syracuseStep 2593291 = 3889937) B3889937
theorem B3457721 : Blo 2303435 3457721 := bstep (se 2 (by rfl) ⟨1296645, by rfl⟩ : syracuseStep 3457721 = 2593291) B2593291
theorem B2305147 : Blo 2303435 2305147 := bstep (se 1 (by rfl) ⟨1728860, by rfl⟩ : syracuseStep 2305147 = 3457721) B3457721
theorem B2368481 : Blo 2303435 2368481 := bbase (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) (by norm_num)
theorem B25263797 : Blo 2303435 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B67370125 : Blo 2303435 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B89826833 : Blo 2303435 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B59884555 : Blo 2303435 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B79846073 : Blo 2303435 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B53230715 : Blo 2303435 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B35487143 : Blo 2303435 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B23658095 : Blo 2303435 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B63088253 : Blo 2303435 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B42058835 : Blo 2303435 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B28039223 : Blo 2303435 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B74771261 : Blo 2303435 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B49847507 : Blo 2303435 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B33231671 : Blo 2303435 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B22154447 : Blo 2303435 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B14769631 : Blo 2303435 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B19692841 : Blo 2303435 19692841 := bstep (se 2 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 19692841 = 14769631) B14769631
theorem B26257121 : Blo 2303435 26257121 := bstep (se 2 (by rfl) ⟨9846420, by rfl⟩ : syracuseStep 26257121 = 19692841) B19692841
theorem B17504747 : Blo 2303435 17504747 := bstep (se 1 (by rfl) ⟨13128560, by rfl⟩ : syracuseStep 17504747 = 26257121) B26257121
theorem B11669831 : Blo 2303435 11669831 := bstep (se 1 (by rfl) ⟨8752373, by rfl⟩ : syracuseStep 11669831 = 17504747) B17504747
theorem B7779887 : Blo 2303435 7779887 := bstep (se 1 (by rfl) ⟨5834915, by rfl⟩ : syracuseStep 7779887 = 11669831) B11669831
theorem B5186591 : Blo 2303435 5186591 := bstep (se 1 (by rfl) ⟨3889943, by rfl⟩ : syracuseStep 5186591 = 7779887) B7779887
theorem B3457727 : Blo 2303435 3457727 := bstep (se 1 (by rfl) ⟨2593295, by rfl⟩ : syracuseStep 3457727 = 5186591) B5186591
theorem B2305151 : Blo 2303435 2305151 := bstep (se 1 (by rfl) ⟨1728863, by rfl⟩ : syracuseStep 2305151 = 3457727) B3457727
theorem B3457733 : Blo 2303435 3457733 := bbase (se 4 (by rfl) ⟨324162, by rfl⟩ : syracuseStep 3457733 = 648325) (by norm_num)
theorem B2305155 : Blo 2303435 2305155 := bstep (se 1 (by rfl) ⟨1728866, by rfl⟩ : syracuseStep 2305155 = 3457733) B3457733
theorem B3889957 : Blo 2303435 3889957 := bbase (se 4 (by rfl) ⟨364683, by rfl⟩ : syracuseStep 3889957 = 729367) (by norm_num)
theorem B5186609 : Blo 2303435 5186609 := bstep (se 2 (by rfl) ⟨1944978, by rfl⟩ : syracuseStep 5186609 = 3889957) B3889957
theorem B3457739 : Blo 2303435 3457739 := bstep (se 1 (by rfl) ⟨2593304, by rfl⟩ : syracuseStep 3457739 = 5186609) B5186609
theorem B2305159 : Blo 2303435 2305159 := bstep (se 1 (by rfl) ⟨1728869, by rfl⟩ : syracuseStep 2305159 = 3457739) B3457739
theorem B2593309 : Blo 2303435 2593309 := bbase (se 3 (by rfl) ⟨486245, by rfl⟩ : syracuseStep 2593309 = 972491) (by norm_num)
theorem B3457745 : Blo 2303435 3457745 := bstep (se 2 (by rfl) ⟨1296654, by rfl⟩ : syracuseStep 3457745 = 2593309) B2593309
theorem B2305163 : Blo 2303435 2305163 := bstep (se 1 (by rfl) ⟨1728872, by rfl⟩ : syracuseStep 2305163 = 3457745) B3457745
theorem B7779941 : Blo 2303435 7779941 := bbase (se 4 (by rfl) ⟨729369, by rfl⟩ : syracuseStep 7779941 = 1458739) (by norm_num)
theorem B5186627 : Blo 2303435 5186627 := bstep (se 1 (by rfl) ⟨3889970, by rfl⟩ : syracuseStep 5186627 = 7779941) B7779941
theorem B3457751 : Blo 2303435 3457751 := bstep (se 1 (by rfl) ⟨2593313, by rfl⟩ : syracuseStep 3457751 = 5186627) B5186627
theorem B2305167 : Blo 2303435 2305167 := bstep (se 1 (by rfl) ⟨1728875, by rfl⟩ : syracuseStep 2305167 = 3457751) B3457751
theorem B3457757 : Blo 2303435 3457757 := bbase (se 3 (by rfl) ⟨648329, by rfl⟩ : syracuseStep 3457757 = 1296659) (by norm_num)
theorem B2305171 : Blo 2303435 2305171 := bstep (se 1 (by rfl) ⟨1728878, by rfl⟩ : syracuseStep 2305171 = 3457757) B3457757
theorem B5186645 : Blo 2303435 5186645 := bbase (se 8 (by rfl) ⟨30390, by rfl⟩ : syracuseStep 5186645 = 60781) (by norm_num)
theorem B3457763 : Blo 2303435 3457763 := bstep (se 1 (by rfl) ⟨2593322, by rfl⟩ : syracuseStep 3457763 = 5186645) B5186645
theorem B2305175 : Blo 2303435 2305175 := bstep (se 1 (by rfl) ⟨1728881, by rfl⟩ : syracuseStep 2305175 = 3457763) B3457763
theorem B8308021 : Blo 2303435 8308021 := bbase (se 5 (by rfl) ⟨389438, by rfl⟩ : syracuseStep 8308021 = 778877) (by norm_num)
theorem B11077361 : Blo 2303435 11077361 := bstep (se 2 (by rfl) ⟨4154010, by rfl⟩ : syracuseStep 11077361 = 8308021) B8308021
theorem B7384907 : Blo 2303435 7384907 := bstep (se 1 (by rfl) ⟨5538680, by rfl⟩ : syracuseStep 7384907 = 11077361) B11077361
theorem B4923271 : Blo 2303435 4923271 := bstep (se 1 (by rfl) ⟨3692453, by rfl⟩ : syracuseStep 4923271 = 7384907) B7384907
theorem B6564361 : Blo 2303435 6564361 := bstep (se 2 (by rfl) ⟨2461635, by rfl⟩ : syracuseStep 6564361 = 4923271) B4923271
theorem B8752481 : Blo 2303435 8752481 := bstep (se 2 (by rfl) ⟨3282180, by rfl⟩ : syracuseStep 8752481 = 6564361) B6564361
theorem B5834987 : Blo 2303435 5834987 := bstep (se 1 (by rfl) ⟨4376240, by rfl⟩ : syracuseStep 5834987 = 8752481) B8752481
theorem B3889991 : Blo 2303435 3889991 := bstep (se 1 (by rfl) ⟨2917493, by rfl⟩ : syracuseStep 3889991 = 5834987) B5834987
theorem B2593327 : Blo 2303435 2593327 := bstep (se 1 (by rfl) ⟨1944995, by rfl⟩ : syracuseStep 2593327 = 3889991) B3889991
theorem B3457769 : Blo 2303435 3457769 := bstep (se 2 (by rfl) ⟨1296663, by rfl⟩ : syracuseStep 3457769 = 2593327) B2593327
theorem B2305179 : Blo 2303435 2305179 := bstep (se 1 (by rfl) ⟨1728884, by rfl⟩ : syracuseStep 2305179 = 3457769) B3457769
theorem B4673269 : Blo 2303435 4673269 := bbase (se 5 (by rfl) ⟨219059, by rfl⟩ : syracuseStep 4673269 = 438119) (by norm_num)
theorem B6231025 : Blo 2303435 6231025 := bstep (se 2 (by rfl) ⟨2336634, by rfl⟩ : syracuseStep 6231025 = 4673269) B4673269
theorem B33232133 : Blo 2303435 33232133 := bstep (se 4 (by rfl) ⟨3115512, by rfl⟩ : syracuseStep 33232133 = 6231025) B6231025
theorem B22154755 : Blo 2303435 22154755 := bstep (se 1 (by rfl) ⟨16616066, by rfl⟩ : syracuseStep 22154755 = 33232133) B33232133
theorem B29539673 : Blo 2303435 29539673 := bstep (se 2 (by rfl) ⟨11077377, by rfl⟩ : syracuseStep 29539673 = 22154755) B22154755
theorem B19693115 : Blo 2303435 19693115 := bstep (se 1 (by rfl) ⟨14769836, by rfl⟩ : syracuseStep 19693115 = 29539673) B29539673
theorem B13128743 : Blo 2303435 13128743 := bstep (se 1 (by rfl) ⟨9846557, by rfl⟩ : syracuseStep 13128743 = 19693115) B19693115
theorem B8752495 : Blo 2303435 8752495 := bstep (se 1 (by rfl) ⟨6564371, by rfl⟩ : syracuseStep 8752495 = 13128743) B13128743
theorem B11669993 : Blo 2303435 11669993 := bstep (se 2 (by rfl) ⟨4376247, by rfl⟩ : syracuseStep 11669993 = 8752495) B8752495
theorem B7779995 : Blo 2303435 7779995 := bstep (se 1 (by rfl) ⟨5834996, by rfl⟩ : syracuseStep 7779995 = 11669993) B11669993
theorem B5186663 : Blo 2303435 5186663 := bstep (se 1 (by rfl) ⟨3889997, by rfl⟩ : syracuseStep 5186663 = 7779995) B7779995
theorem B3457775 : Blo 2303435 3457775 := bstep (se 1 (by rfl) ⟨2593331, by rfl⟩ : syracuseStep 3457775 = 5186663) B5186663
theorem B2305183 : Blo 2303435 2305183 := bstep (se 1 (by rfl) ⟨1728887, by rfl⟩ : syracuseStep 2305183 = 3457775) B3457775
theorem B3457781 : Blo 2303435 3457781 := bbase (se 5 (by rfl) ⟨162083, by rfl⟩ : syracuseStep 3457781 = 324167) (by norm_num)
theorem B2305187 : Blo 2303435 2305187 := bstep (se 1 (by rfl) ⟨1728890, by rfl⟩ : syracuseStep 2305187 = 3457781) B3457781
theorem B5538709 : Blo 2303435 5538709 := bbase (se 6 (by rfl) ⟨129813, by rfl⟩ : syracuseStep 5538709 = 259627) (by norm_num)
theorem B7384945 : Blo 2303435 7384945 := bstep (se 2 (by rfl) ⟨2769354, by rfl⟩ : syracuseStep 7384945 = 5538709) B5538709
theorem B9846593 : Blo 2303435 9846593 := bstep (se 2 (by rfl) ⟨3692472, by rfl⟩ : syracuseStep 9846593 = 7384945) B7384945
theorem B6564395 : Blo 2303435 6564395 := bstep (se 1 (by rfl) ⟨4923296, by rfl⟩ : syracuseStep 6564395 = 9846593) B9846593
theorem B4376263 : Blo 2303435 4376263 := bstep (se 1 (by rfl) ⟨3282197, by rfl⟩ : syracuseStep 4376263 = 6564395) B6564395
theorem B5835017 : Blo 2303435 5835017 := bstep (se 2 (by rfl) ⟨2188131, by rfl⟩ : syracuseStep 5835017 = 4376263) B4376263
theorem B3890011 : Blo 2303435 3890011 := bstep (se 1 (by rfl) ⟨2917508, by rfl⟩ : syracuseStep 3890011 = 5835017) B5835017
theorem B5186681 : Blo 2303435 5186681 := bstep (se 2 (by rfl) ⟨1945005, by rfl⟩ : syracuseStep 5186681 = 3890011) B3890011
theorem B3457787 : Blo 2303435 3457787 := bstep (se 1 (by rfl) ⟨2593340, by rfl⟩ : syracuseStep 3457787 = 5186681) B5186681
theorem B2305191 : Blo 2303435 2305191 := bstep (se 1 (by rfl) ⟨1728893, by rfl⟩ : syracuseStep 2305191 = 3457787) B3457787
theorem B2593345 : Blo 2303435 2593345 := bbase (se 2 (by rfl) ⟨972504, by rfl⟩ : syracuseStep 2593345 = 1945009) (by norm_num)
theorem B3457793 : Blo 2303435 3457793 := bstep (se 2 (by rfl) ⟨1296672, by rfl⟩ : syracuseStep 3457793 = 2593345) B2593345
theorem B2305195 : Blo 2303435 2305195 := bstep (se 1 (by rfl) ⟨1728896, by rfl⟩ : syracuseStep 2305195 = 3457793) B3457793
theorem B5835037 : Blo 2303435 5835037 := bbase (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) (by norm_num)
theorem B7780049 : Blo 2303435 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B5186699 : Blo 2303435 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B3457799 : Blo 2303435 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B2305199 : Blo 2303435 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B3457805 : Blo 2303435 3457805 := bbase (se 3 (by rfl) ⟨648338, by rfl⟩ : syracuseStep 3457805 = 1296677) (by norm_num)
theorem B2305203 : Blo 2303435 2305203 := bstep (se 1 (by rfl) ⟨1728902, by rfl⟩ : syracuseStep 2305203 = 3457805) B3457805
theorem B5186717 : Blo 2303435 5186717 := bbase (se 3 (by rfl) ⟨972509, by rfl⟩ : syracuseStep 5186717 = 1945019) (by norm_num)
theorem B3457811 : Blo 2303435 3457811 := bstep (se 1 (by rfl) ⟨2593358, by rfl⟩ : syracuseStep 3457811 = 5186717) B5186717
theorem B2305207 : Blo 2303435 2305207 := bstep (se 1 (by rfl) ⟨1728905, by rfl⟩ : syracuseStep 2305207 = 3457811) B3457811
theorem B3890045 : Blo 2303435 3890045 := bbase (se 3 (by rfl) ⟨729383, by rfl⟩ : syracuseStep 3890045 = 1458767) (by norm_num)
theorem B2593363 : Blo 2303435 2593363 := bstep (se 1 (by rfl) ⟨1945022, by rfl⟩ : syracuseStep 2593363 = 3890045) B3890045
theorem B3457817 : Blo 2303435 3457817 := bstep (se 2 (by rfl) ⟨1296681, by rfl⟩ : syracuseStep 3457817 = 2593363) B2593363
theorem B2305211 : Blo 2303435 2305211 := bstep (se 1 (by rfl) ⟨1728908, by rfl⟩ : syracuseStep 2305211 = 3457817) B3457817
theorem B8872037 : Blo 2303435 8872037 := bbase (se 4 (by rfl) ⟨831753, by rfl⟩ : syracuseStep 8872037 = 1663507) (by norm_num)
theorem B5914691 : Blo 2303435 5914691 := bstep (se 1 (by rfl) ⟨4436018, by rfl⟩ : syracuseStep 5914691 = 8872037) B8872037
theorem B3943127 : Blo 2303435 3943127 := bstep (se 1 (by rfl) ⟨2957345, by rfl⟩ : syracuseStep 3943127 = 5914691) B5914691
theorem B10515005 : Blo 2303435 10515005 := bstep (se 3 (by rfl) ⟨1971563, by rfl⟩ : syracuseStep 10515005 = 3943127) B3943127
theorem B7010003 : Blo 2303435 7010003 := bstep (se 1 (by rfl) ⟨5257502, by rfl⟩ : syracuseStep 7010003 = 10515005) B10515005
theorem B4673335 : Blo 2303435 4673335 := bstep (se 1 (by rfl) ⟨3505001, by rfl⟩ : syracuseStep 4673335 = 7010003) B7010003
theorem B6231113 : Blo 2303435 6231113 := bstep (se 2 (by rfl) ⟨2336667, by rfl⟩ : syracuseStep 6231113 = 4673335) B4673335
theorem B4154075 : Blo 2303435 4154075 := bstep (se 1 (by rfl) ⟨3115556, by rfl⟩ : syracuseStep 4154075 = 6231113) B6231113
theorem B2769383 : Blo 2303435 2769383 := bstep (se 1 (by rfl) ⟨2077037, by rfl⟩ : syracuseStep 2769383 = 4154075) B4154075
theorem B7385021 : Blo 2303435 7385021 := bstep (se 3 (by rfl) ⟨1384691, by rfl⟩ : syracuseStep 7385021 = 2769383) B2769383
theorem B4923347 : Blo 2303435 4923347 := bstep (se 1 (by rfl) ⟨3692510, by rfl⟩ : syracuseStep 4923347 = 7385021) B7385021
theorem B13128925 : Blo 2303435 13128925 := bstep (se 3 (by rfl) ⟨2461673, by rfl⟩ : syracuseStep 13128925 = 4923347) B4923347
theorem B17505233 : Blo 2303435 17505233 := bstep (se 2 (by rfl) ⟨6564462, by rfl⟩ : syracuseStep 17505233 = 13128925) B13128925
theorem B11670155 : Blo 2303435 11670155 := bstep (se 1 (by rfl) ⟨8752616, by rfl⟩ : syracuseStep 11670155 = 17505233) B17505233
theorem B7780103 : Blo 2303435 7780103 := bstep (se 1 (by rfl) ⟨5835077, by rfl⟩ : syracuseStep 7780103 = 11670155) B11670155
theorem B5186735 : Blo 2303435 5186735 := bstep (se 1 (by rfl) ⟨3890051, by rfl⟩ : syracuseStep 5186735 = 7780103) B7780103
theorem B3457823 : Blo 2303435 3457823 := bstep (se 1 (by rfl) ⟨2593367, by rfl⟩ : syracuseStep 3457823 = 5186735) B5186735
theorem B2305215 : Blo 2303435 2305215 := bstep (se 1 (by rfl) ⟨1728911, by rfl⟩ : syracuseStep 2305215 = 3457823) B3457823
theorem B3457829 : Blo 2303435 3457829 := bbase (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) (by norm_num)
theorem B2305219 : Blo 2303435 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B2917549 : Blo 2303435 2917549 := bbase (se 3 (by rfl) ⟨547040, by rfl⟩ : syracuseStep 2917549 = 1094081) (by norm_num)
theorem B3890065 : Blo 2303435 3890065 := bstep (se 2 (by rfl) ⟨1458774, by rfl⟩ : syracuseStep 3890065 = 2917549) B2917549
theorem B5186753 : Blo 2303435 5186753 := bstep (se 2 (by rfl) ⟨1945032, by rfl⟩ : syracuseStep 5186753 = 3890065) B3890065
theorem B3457835 : Blo 2303435 3457835 := bstep (se 1 (by rfl) ⟨2593376, by rfl⟩ : syracuseStep 3457835 = 5186753) B5186753
theorem B2305223 : Blo 2303435 2305223 := bstep (se 1 (by rfl) ⟨1728917, by rfl⟩ : syracuseStep 2305223 = 3457835) B3457835
theorem B2593381 : Blo 2303435 2593381 := bbase (se 4 (by rfl) ⟨243129, by rfl⟩ : syracuseStep 2593381 = 486259) (by norm_num)
theorem B3457841 : Blo 2303435 3457841 := bstep (se 2 (by rfl) ⟨1296690, by rfl⟩ : syracuseStep 3457841 = 2593381) B2593381
theorem B2305227 : Blo 2303435 2305227 := bstep (se 1 (by rfl) ⟨1728920, by rfl⟩ : syracuseStep 2305227 = 3457841) B3457841
theorem B5257541 : Blo 2303435 5257541 := bbase (se 4 (by rfl) ⟨492894, by rfl⟩ : syracuseStep 5257541 = 985789) (by norm_num)
theorem B3505027 : Blo 2303435 3505027 := bstep (se 1 (by rfl) ⟨2628770, by rfl⟩ : syracuseStep 3505027 = 5257541) B5257541
theorem B4673369 : Blo 2303435 4673369 := bstep (se 2 (by rfl) ⟨1752513, by rfl⟩ : syracuseStep 4673369 = 3505027) B3505027
theorem B3115579 : Blo 2303435 3115579 := bstep (se 1 (by rfl) ⟨2336684, by rfl⟩ : syracuseStep 3115579 = 4673369) B4673369
theorem B4154105 : Blo 2303435 4154105 := bstep (se 2 (by rfl) ⟨1557789, by rfl⟩ : syracuseStep 4154105 = 3115579) B3115579
theorem B2769403 : Blo 2303435 2769403 := bstep (se 1 (by rfl) ⟨2077052, by rfl⟩ : syracuseStep 2769403 = 4154105) B4154105
theorem B3692537 : Blo 2303435 3692537 := bstep (se 2 (by rfl) ⟨1384701, by rfl⟩ : syracuseStep 3692537 = 2769403) B2769403
theorem B2461691 : Blo 2303435 2461691 := bstep (se 1 (by rfl) ⟨1846268, by rfl⟩ : syracuseStep 2461691 = 3692537) B3692537
theorem B6564509 : Blo 2303435 6564509 := bstep (se 3 (by rfl) ⟨1230845, by rfl⟩ : syracuseStep 6564509 = 2461691) B2461691
theorem B4376339 : Blo 2303435 4376339 := bstep (se 1 (by rfl) ⟨3282254, by rfl⟩ : syracuseStep 4376339 = 6564509) B6564509
theorem B2917559 : Blo 2303435 2917559 := bstep (se 1 (by rfl) ⟨2188169, by rfl⟩ : syracuseStep 2917559 = 4376339) B4376339
theorem B7780157 : Blo 2303435 7780157 := bstep (se 3 (by rfl) ⟨1458779, by rfl⟩ : syracuseStep 7780157 = 2917559) B2917559
theorem B5186771 : Blo 2303435 5186771 := bstep (se 1 (by rfl) ⟨3890078, by rfl⟩ : syracuseStep 5186771 = 7780157) B7780157
theorem B3457847 : Blo 2303435 3457847 := bstep (se 1 (by rfl) ⟨2593385, by rfl⟩ : syracuseStep 3457847 = 5186771) B5186771
theorem B2305231 : Blo 2303435 2305231 := bstep (se 1 (by rfl) ⟨1728923, by rfl⟩ : syracuseStep 2305231 = 3457847) B3457847
theorem B3457853 : Blo 2303435 3457853 := bbase (se 3 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 3457853 = 1296695) (by norm_num)
theorem B2305235 : Blo 2303435 2305235 := bstep (se 1 (by rfl) ⟨1728926, by rfl⟩ : syracuseStep 2305235 = 3457853) B3457853
theorem B5186789 : Blo 2303435 5186789 := bbase (se 4 (by rfl) ⟨486261, by rfl⟩ : syracuseStep 5186789 = 972523) (by norm_num)
theorem B3457859 : Blo 2303435 3457859 := bstep (se 1 (by rfl) ⟨2593394, by rfl⟩ : syracuseStep 3457859 = 5186789) B5186789
theorem B2305239 : Blo 2303435 2305239 := bstep (se 1 (by rfl) ⟨1728929, by rfl⟩ : syracuseStep 2305239 = 3457859) B3457859
theorem B5835149 : Blo 2303435 5835149 := bbase (se 3 (by rfl) ⟨1094090, by rfl⟩ : syracuseStep 5835149 = 2188181) (by norm_num)
theorem B3890099 : Blo 2303435 3890099 := bstep (se 1 (by rfl) ⟨2917574, by rfl⟩ : syracuseStep 3890099 = 5835149) B5835149
theorem B2593399 : Blo 2303435 2593399 := bstep (se 1 (by rfl) ⟨1945049, by rfl⟩ : syracuseStep 2593399 = 3890099) B3890099
theorem B3457865 : Blo 2303435 3457865 := bstep (se 2 (by rfl) ⟨1296699, by rfl⟩ : syracuseStep 3457865 = 2593399) B2593399
theorem B2305243 : Blo 2303435 2305243 := bstep (se 1 (by rfl) ⟨1728932, by rfl⟩ : syracuseStep 2305243 = 3457865) B3457865
theorem B3282277 : Blo 2303435 3282277 := bbase (se 4 (by rfl) ⟨307713, by rfl⟩ : syracuseStep 3282277 = 615427) (by norm_num)
theorem B4376369 : Blo 2303435 4376369 := bstep (se 2 (by rfl) ⟨1641138, by rfl⟩ : syracuseStep 4376369 = 3282277) B3282277
theorem B11670317 : Blo 2303435 11670317 := bstep (se 3 (by rfl) ⟨2188184, by rfl⟩ : syracuseStep 11670317 = 4376369) B4376369
theorem B7780211 : Blo 2303435 7780211 := bstep (se 1 (by rfl) ⟨5835158, by rfl⟩ : syracuseStep 7780211 = 11670317) B11670317
theorem B5186807 : Blo 2303435 5186807 := bstep (se 1 (by rfl) ⟨3890105, by rfl⟩ : syracuseStep 5186807 = 7780211) B7780211
theorem B3457871 : Blo 2303435 3457871 := bstep (se 1 (by rfl) ⟨2593403, by rfl⟩ : syracuseStep 3457871 = 5186807) B5186807
theorem B2305247 : Blo 2303435 2305247 := bstep (se 1 (by rfl) ⟨1728935, by rfl⟩ : syracuseStep 2305247 = 3457871) B3457871
theorem B3457877 : Blo 2303435 3457877 := bbase (se 9 (by rfl) ⟨10130, by rfl⟩ : syracuseStep 3457877 = 20261) (by norm_num)
theorem B2305251 : Blo 2303435 2305251 := bstep (se 1 (by rfl) ⟨1728938, by rfl⟩ : syracuseStep 2305251 = 3457877) B3457877
theorem B37897429 : Blo 2303435 37897429 := bbase (se 7 (by rfl) ⟨444110, by rfl⟩ : syracuseStep 37897429 = 888221) (by norm_num)
theorem B50529905 : Blo 2303435 50529905 := bstep (se 2 (by rfl) ⟨18948714, by rfl⟩ : syracuseStep 50529905 = 37897429) B37897429
theorem B33686603 : Blo 2303435 33686603 := bstep (se 1 (by rfl) ⟨25264952, by rfl⟩ : syracuseStep 33686603 = 50529905) B50529905
theorem B22457735 : Blo 2303435 22457735 := bstep (se 1 (by rfl) ⟨16843301, by rfl⟩ : syracuseStep 22457735 = 33686603) B33686603
theorem B14971823 : Blo 2303435 14971823 := bstep (se 1 (by rfl) ⟨11228867, by rfl⟩ : syracuseStep 14971823 = 22457735) B22457735
theorem B9981215 : Blo 2303435 9981215 := bstep (se 1 (by rfl) ⟨7485911, by rfl⟩ : syracuseStep 9981215 = 14971823) B14971823
theorem B6654143 : Blo 2303435 6654143 := bstep (se 1 (by rfl) ⟨4990607, by rfl⟩ : syracuseStep 6654143 = 9981215) B9981215
theorem B4436095 : Blo 2303435 4436095 := bstep (se 1 (by rfl) ⟨3327071, by rfl⟩ : syracuseStep 4436095 = 6654143) B6654143
theorem B5914793 : Blo 2303435 5914793 := bstep (se 2 (by rfl) ⟨2218047, by rfl⟩ : syracuseStep 5914793 = 4436095) B4436095
theorem B15772781 : Blo 2303435 15772781 := bstep (se 3 (by rfl) ⟨2957396, by rfl⟩ : syracuseStep 15772781 = 5914793) B5914793
theorem B10515187 : Blo 2303435 10515187 := bstep (se 1 (by rfl) ⟨7886390, by rfl⟩ : syracuseStep 10515187 = 15772781) B15772781
theorem B14020249 : Blo 2303435 14020249 := bstep (se 2 (by rfl) ⟨5257593, by rfl⟩ : syracuseStep 14020249 = 10515187) B10515187
theorem B18693665 : Blo 2303435 18693665 := bstep (se 2 (by rfl) ⟨7010124, by rfl⟩ : syracuseStep 18693665 = 14020249) B14020249
theorem B12462443 : Blo 2303435 12462443 := bstep (se 1 (by rfl) ⟨9346832, by rfl⟩ : syracuseStep 12462443 = 18693665) B18693665
theorem B8308295 : Blo 2303435 8308295 := bstep (se 1 (by rfl) ⟨6231221, by rfl⟩ : syracuseStep 8308295 = 12462443) B12462443
theorem B5538863 : Blo 2303435 5538863 := bstep (se 1 (by rfl) ⟨4154147, by rfl⟩ : syracuseStep 5538863 = 8308295) B8308295
theorem B3692575 : Blo 2303435 3692575 := bstep (se 1 (by rfl) ⟨2769431, by rfl⟩ : syracuseStep 3692575 = 5538863) B5538863
theorem B4923433 : Blo 2303435 4923433 := bstep (se 2 (by rfl) ⟨1846287, by rfl⟩ : syracuseStep 4923433 = 3692575) B3692575
theorem B6564577 : Blo 2303435 6564577 := bstep (se 2 (by rfl) ⟨2461716, by rfl⟩ : syracuseStep 6564577 = 4923433) B4923433
theorem B8752769 : Blo 2303435 8752769 := bstep (se 2 (by rfl) ⟨3282288, by rfl⟩ : syracuseStep 8752769 = 6564577) B6564577
theorem B5835179 : Blo 2303435 5835179 := bstep (se 1 (by rfl) ⟨4376384, by rfl⟩ : syracuseStep 5835179 = 8752769) B8752769
theorem B3890119 : Blo 2303435 3890119 := bstep (se 1 (by rfl) ⟨2917589, by rfl⟩ : syracuseStep 3890119 = 5835179) B5835179
theorem B5186825 : Blo 2303435 5186825 := bstep (se 2 (by rfl) ⟨1945059, by rfl⟩ : syracuseStep 5186825 = 3890119) B3890119
theorem B3457883 : Blo 2303435 3457883 := bstep (se 1 (by rfl) ⟨2593412, by rfl⟩ : syracuseStep 3457883 = 5186825) B5186825
theorem B2305255 : Blo 2303435 2305255 := bstep (se 1 (by rfl) ⟨1728941, by rfl⟩ : syracuseStep 2305255 = 3457883) B3457883
theorem B2593417 : Blo 2303435 2593417 := bbase (se 2 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 2593417 = 1945063) (by norm_num)
theorem B3457889 : Blo 2303435 3457889 := bstep (se 2 (by rfl) ⟨1296708, by rfl⟩ : syracuseStep 3457889 = 2593417) B2593417
theorem B2305259 : Blo 2303435 2305259 := bstep (se 1 (by rfl) ⟨1728944, by rfl⟩ : syracuseStep 2305259 = 3457889) B3457889
theorem B2628805 : Blo 2303435 2628805 := bbase (se 4 (by rfl) ⟨246450, by rfl⟩ : syracuseStep 2628805 = 492901) (by norm_num)
theorem B56081173 : Blo 2303435 56081173 := bstep (se 6 (by rfl) ⟨1314402, by rfl⟩ : syracuseStep 56081173 = 2628805) B2628805
theorem B74774897 : Blo 2303435 74774897 := bstep (se 2 (by rfl) ⟨28040586, by rfl⟩ : syracuseStep 74774897 = 56081173) B56081173
theorem B49849931 : Blo 2303435 49849931 := bstep (se 1 (by rfl) ⟨37387448, by rfl⟩ : syracuseStep 49849931 = 74774897) B74774897
theorem B33233287 : Blo 2303435 33233287 := bstep (se 1 (by rfl) ⟨24924965, by rfl⟩ : syracuseStep 33233287 = 49849931) B49849931
theorem B44311049 : Blo 2303435 44311049 := bstep (se 2 (by rfl) ⟨16616643, by rfl⟩ : syracuseStep 44311049 = 33233287) B33233287
theorem B29540699 : Blo 2303435 29540699 := bstep (se 1 (by rfl) ⟨22155524, by rfl⟩ : syracuseStep 29540699 = 44311049) B44311049
theorem B19693799 : Blo 2303435 19693799 := bstep (se 1 (by rfl) ⟨14770349, by rfl⟩ : syracuseStep 19693799 = 29540699) B29540699
theorem B13129199 : Blo 2303435 13129199 := bstep (se 1 (by rfl) ⟨9846899, by rfl⟩ : syracuseStep 13129199 = 19693799) B19693799
theorem B8752799 : Blo 2303435 8752799 := bstep (se 1 (by rfl) ⟨6564599, by rfl⟩ : syracuseStep 8752799 = 13129199) B13129199
theorem B5835199 : Blo 2303435 5835199 := bstep (se 1 (by rfl) ⟨4376399, by rfl⟩ : syracuseStep 5835199 = 8752799) B8752799
theorem B7780265 : Blo 2303435 7780265 := bstep (se 2 (by rfl) ⟨2917599, by rfl⟩ : syracuseStep 7780265 = 5835199) B5835199
theorem B5186843 : Blo 2303435 5186843 := bstep (se 1 (by rfl) ⟨3890132, by rfl⟩ : syracuseStep 5186843 = 7780265) B7780265
theorem B3457895 : Blo 2303435 3457895 := bstep (se 1 (by rfl) ⟨2593421, by rfl⟩ : syracuseStep 3457895 = 5186843) B5186843
theorem B2305263 : Blo 2303435 2305263 := bstep (se 1 (by rfl) ⟨1728947, by rfl⟩ : syracuseStep 2305263 = 3457895) B3457895
theorem B3457901 : Blo 2303435 3457901 := bbase (se 3 (by rfl) ⟨648356, by rfl⟩ : syracuseStep 3457901 = 1296713) (by norm_num)
theorem B2305267 : Blo 2303435 2305267 := bstep (se 1 (by rfl) ⟨1728950, by rfl⟩ : syracuseStep 2305267 = 3457901) B3457901
theorem B5186861 : Blo 2303435 5186861 := bbase (se 3 (by rfl) ⟨972536, by rfl⟩ : syracuseStep 5186861 = 1945073) (by norm_num)
theorem B3457907 : Blo 2303435 3457907 := bstep (se 1 (by rfl) ⟨2593430, by rfl⟩ : syracuseStep 3457907 = 5186861) B5186861
theorem B2305271 : Blo 2303435 2305271 := bstep (se 1 (by rfl) ⟨1728953, by rfl⟩ : syracuseStep 2305271 = 3457907) B3457907
theorem B63091669 : Blo 2303435 63091669 := bbase (se 7 (by rfl) ⟨739355, by rfl⟩ : syracuseStep 63091669 = 1478711) (by norm_num)
theorem B84122225 : Blo 2303435 84122225 := bstep (se 2 (by rfl) ⟨31545834, by rfl⟩ : syracuseStep 84122225 = 63091669) B63091669
theorem B56081483 : Blo 2303435 56081483 := bstep (se 1 (by rfl) ⟨42061112, by rfl⟩ : syracuseStep 56081483 = 84122225) B84122225
theorem B37387655 : Blo 2303435 37387655 := bstep (se 1 (by rfl) ⟨28040741, by rfl⟩ : syracuseStep 37387655 = 56081483) B56081483
theorem B24925103 : Blo 2303435 24925103 := bstep (se 1 (by rfl) ⟨18693827, by rfl⟩ : syracuseStep 24925103 = 37387655) B37387655
theorem B16616735 : Blo 2303435 16616735 := bstep (se 1 (by rfl) ⟨12462551, by rfl⟩ : syracuseStep 16616735 = 24925103) B24925103
theorem B11077823 : Blo 2303435 11077823 := bstep (se 1 (by rfl) ⟨8308367, by rfl⟩ : syracuseStep 11077823 = 16616735) B16616735
theorem B7385215 : Blo 2303435 7385215 := bstep (se 1 (by rfl) ⟨5538911, by rfl⟩ : syracuseStep 7385215 = 11077823) B11077823
theorem B9846953 : Blo 2303435 9846953 := bstep (se 2 (by rfl) ⟨3692607, by rfl⟩ : syracuseStep 9846953 = 7385215) B7385215
theorem B6564635 : Blo 2303435 6564635 := bstep (se 1 (by rfl) ⟨4923476, by rfl⟩ : syracuseStep 6564635 = 9846953) B9846953
theorem B4376423 : Blo 2303435 4376423 := bstep (se 1 (by rfl) ⟨3282317, by rfl⟩ : syracuseStep 4376423 = 6564635) B6564635
theorem B2917615 : Blo 2303435 2917615 := bstep (se 1 (by rfl) ⟨2188211, by rfl⟩ : syracuseStep 2917615 = 4376423) B4376423
theorem B3890153 : Blo 2303435 3890153 := bstep (se 2 (by rfl) ⟨1458807, by rfl⟩ : syracuseStep 3890153 = 2917615) B2917615
theorem B2593435 : Blo 2303435 2593435 := bstep (se 1 (by rfl) ⟨1945076, by rfl⟩ : syracuseStep 2593435 = 3890153) B3890153
theorem B3457913 : Blo 2303435 3457913 := bstep (se 2 (by rfl) ⟨1296717, by rfl⟩ : syracuseStep 3457913 = 2593435) B2593435
theorem B2305275 : Blo 2303435 2305275 := bstep (se 1 (by rfl) ⟨1728956, by rfl⟩ : syracuseStep 2305275 = 3457913) B3457913
theorem B2807245 : Blo 2303435 2807245 := bbase (se 3 (by rfl) ⟨526358, by rfl⟩ : syracuseStep 2807245 = 1052717) (by norm_num)
theorem B3742993 : Blo 2303435 3742993 := bstep (se 2 (by rfl) ⟨1403622, by rfl⟩ : syracuseStep 3742993 = 2807245) B2807245
theorem B19962629 : Blo 2303435 19962629 := bstep (se 4 (by rfl) ⟨1871496, by rfl⟩ : syracuseStep 19962629 = 3742993) B3742993
theorem B13308419 : Blo 2303435 13308419 := bstep (se 1 (by rfl) ⟨9981314, by rfl⟩ : syracuseStep 13308419 = 19962629) B19962629
theorem B35489117 : Blo 2303435 35489117 := bstep (se 3 (by rfl) ⟨6654209, by rfl⟩ : syracuseStep 35489117 = 13308419) B13308419
theorem B23659411 : Blo 2303435 23659411 := bstep (se 1 (by rfl) ⟨17744558, by rfl⟩ : syracuseStep 23659411 = 35489117) B35489117
theorem B31545881 : Blo 2303435 31545881 := bstep (se 2 (by rfl) ⟨11829705, by rfl⟩ : syracuseStep 31545881 = 23659411) B23659411
theorem B21030587 : Blo 2303435 21030587 := bstep (se 1 (by rfl) ⟨15772940, by rfl⟩ : syracuseStep 21030587 = 31545881) B31545881
theorem B14020391 : Blo 2303435 14020391 := bstep (se 1 (by rfl) ⟨10515293, by rfl⟩ : syracuseStep 14020391 = 21030587) B21030587
theorem B9346927 : Blo 2303435 9346927 := bstep (se 1 (by rfl) ⟨7010195, by rfl⟩ : syracuseStep 9346927 = 14020391) B14020391
theorem B12462569 : Blo 2303435 12462569 := bstep (se 2 (by rfl) ⟨4673463, by rfl⟩ : syracuseStep 12462569 = 9346927) B9346927
theorem B8308379 : Blo 2303435 8308379 := bstep (se 1 (by rfl) ⟨6231284, by rfl⟩ : syracuseStep 8308379 = 12462569) B12462569
theorem B22155677 : Blo 2303435 22155677 := bstep (se 3 (by rfl) ⟨4154189, by rfl⟩ : syracuseStep 22155677 = 8308379) B8308379
theorem B14770451 : Blo 2303435 14770451 := bstep (se 1 (by rfl) ⟨11077838, by rfl⟩ : syracuseStep 14770451 = 22155677) B22155677
theorem B39387869 : Blo 2303435 39387869 := bstep (se 3 (by rfl) ⟨7385225, by rfl⟩ : syracuseStep 39387869 = 14770451) B14770451
theorem B26258579 : Blo 2303435 26258579 := bstep (se 1 (by rfl) ⟨19693934, by rfl⟩ : syracuseStep 26258579 = 39387869) B39387869
theorem B17505719 : Blo 2303435 17505719 := bstep (se 1 (by rfl) ⟨13129289, by rfl⟩ : syracuseStep 17505719 = 26258579) B26258579
theorem B11670479 : Blo 2303435 11670479 := bstep (se 1 (by rfl) ⟨8752859, by rfl⟩ : syracuseStep 11670479 = 17505719) B17505719
theorem B7780319 : Blo 2303435 7780319 := bstep (se 1 (by rfl) ⟨5835239, by rfl⟩ : syracuseStep 7780319 = 11670479) B11670479
theorem B5186879 : Blo 2303435 5186879 := bstep (se 1 (by rfl) ⟨3890159, by rfl⟩ : syracuseStep 5186879 = 7780319) B7780319
theorem B3457919 : Blo 2303435 3457919 := bstep (se 1 (by rfl) ⟨2593439, by rfl⟩ : syracuseStep 3457919 = 5186879) B5186879
theorem B2305279 : Blo 2303435 2305279 := bstep (se 1 (by rfl) ⟨1728959, by rfl⟩ : syracuseStep 2305279 = 3457919) B3457919
theorem B3457925 : Blo 2303435 3457925 := bbase (se 4 (by rfl) ⟨324180, by rfl⟩ : syracuseStep 3457925 = 648361) (by norm_num)
theorem B2305283 : Blo 2303435 2305283 := bstep (se 1 (by rfl) ⟨1728962, by rfl⟩ : syracuseStep 2305283 = 3457925) B3457925
theorem B3890173 : Blo 2303435 3890173 := bbase (se 3 (by rfl) ⟨729407, by rfl⟩ : syracuseStep 3890173 = 1458815) (by norm_num)
theorem B5186897 : Blo 2303435 5186897 := bstep (se 2 (by rfl) ⟨1945086, by rfl⟩ : syracuseStep 5186897 = 3890173) B3890173
theorem B3457931 : Blo 2303435 3457931 := bstep (se 1 (by rfl) ⟨2593448, by rfl⟩ : syracuseStep 3457931 = 5186897) B5186897
theorem B2305287 : Blo 2303435 2305287 := bstep (se 1 (by rfl) ⟨1728965, by rfl⟩ : syracuseStep 2305287 = 3457931) B3457931
theorem B2593453 : Blo 2303435 2593453 := bbase (se 3 (by rfl) ⟨486272, by rfl⟩ : syracuseStep 2593453 = 972545) (by norm_num)
theorem B3457937 : Blo 2303435 3457937 := bstep (se 2 (by rfl) ⟨1296726, by rfl⟩ : syracuseStep 3457937 = 2593453) B2593453
theorem B2305291 : Blo 2303435 2305291 := bstep (se 1 (by rfl) ⟨1728968, by rfl⟩ : syracuseStep 2305291 = 3457937) B3457937
theorem B7780373 : Blo 2303435 7780373 := bbase (se 6 (by rfl) ⟨182352, by rfl⟩ : syracuseStep 7780373 = 364705) (by norm_num)
theorem B5186915 : Blo 2303435 5186915 := bstep (se 1 (by rfl) ⟨3890186, by rfl⟩ : syracuseStep 5186915 = 7780373) B7780373
theorem B3457943 : Blo 2303435 3457943 := bstep (se 1 (by rfl) ⟨2593457, by rfl⟩ : syracuseStep 3457943 = 5186915) B5186915
theorem B2305295 : Blo 2303435 2305295 := bstep (se 1 (by rfl) ⟨1728971, by rfl⟩ : syracuseStep 2305295 = 3457943) B3457943
theorem B3457949 : Blo 2303435 3457949 := bbase (se 3 (by rfl) ⟨648365, by rfl⟩ : syracuseStep 3457949 = 1296731) (by norm_num)
theorem B2305299 : Blo 2303435 2305299 := bstep (se 1 (by rfl) ⟨1728974, by rfl⟩ : syracuseStep 2305299 = 3457949) B3457949
theorem B5186933 : Blo 2303435 5186933 := bbase (se 5 (by rfl) ⟨243137, by rfl⟩ : syracuseStep 5186933 = 486275) (by norm_num)
theorem B3457955 : Blo 2303435 3457955 := bstep (se 1 (by rfl) ⟨2593466, by rfl⟩ : syracuseStep 3457955 = 5186933) B5186933
theorem B2305303 : Blo 2303435 2305303 := bstep (se 1 (by rfl) ⟨1728977, by rfl⟩ : syracuseStep 2305303 = 3457955) B3457955
theorem B3505141 : Blo 2303435 3505141 := bbase (se 5 (by rfl) ⟨164303, by rfl⟩ : syracuseStep 3505141 = 328607) (by norm_num)
theorem B4673521 : Blo 2303435 4673521 := bstep (se 2 (by rfl) ⟨1752570, by rfl⟩ : syracuseStep 4673521 = 3505141) B3505141
theorem B24925445 : Blo 2303435 24925445 := bstep (se 4 (by rfl) ⟨2336760, by rfl⟩ : syracuseStep 24925445 = 4673521) B4673521
theorem B16616963 : Blo 2303435 16616963 := bstep (se 1 (by rfl) ⟨12462722, by rfl⟩ : syracuseStep 16616963 = 24925445) B24925445
theorem B11077975 : Blo 2303435 11077975 := bstep (se 1 (by rfl) ⟨8308481, by rfl⟩ : syracuseStep 11077975 = 16616963) B16616963
theorem B14770633 : Blo 2303435 14770633 := bstep (se 2 (by rfl) ⟨5538987, by rfl⟩ : syracuseStep 14770633 = 11077975) B11077975
theorem B19694177 : Blo 2303435 19694177 := bstep (se 2 (by rfl) ⟨7385316, by rfl⟩ : syracuseStep 19694177 = 14770633) B14770633
theorem B13129451 : Blo 2303435 13129451 := bstep (se 1 (by rfl) ⟨9847088, by rfl⟩ : syracuseStep 13129451 = 19694177) B19694177
theorem B8752967 : Blo 2303435 8752967 := bstep (se 1 (by rfl) ⟨6564725, by rfl⟩ : syracuseStep 8752967 = 13129451) B13129451
theorem B5835311 : Blo 2303435 5835311 := bstep (se 1 (by rfl) ⟨4376483, by rfl⟩ : syracuseStep 5835311 = 8752967) B8752967
theorem B3890207 : Blo 2303435 3890207 := bstep (se 1 (by rfl) ⟨2917655, by rfl⟩ : syracuseStep 3890207 = 5835311) B5835311
theorem B2593471 : Blo 2303435 2593471 := bstep (se 1 (by rfl) ⟨1945103, by rfl⟩ : syracuseStep 2593471 = 3890207) B3890207
theorem B3457961 : Blo 2303435 3457961 := bstep (se 2 (by rfl) ⟨1296735, by rfl⟩ : syracuseStep 3457961 = 2593471) B2593471
theorem B2305307 : Blo 2303435 2305307 := bstep (se 1 (by rfl) ⟨1728980, by rfl⟩ : syracuseStep 2305307 = 3457961) B3457961
theorem B8752981 : Blo 2303435 8752981 := bbase (se 9 (by rfl) ⟨25643, by rfl⟩ : syracuseStep 8752981 = 51287) (by norm_num)
theorem B11670641 : Blo 2303435 11670641 := bstep (se 2 (by rfl) ⟨4376490, by rfl⟩ : syracuseStep 11670641 = 8752981) B8752981
theorem B7780427 : Blo 2303435 7780427 := bstep (se 1 (by rfl) ⟨5835320, by rfl⟩ : syracuseStep 7780427 = 11670641) B11670641
theorem B5186951 : Blo 2303435 5186951 := bstep (se 1 (by rfl) ⟨3890213, by rfl⟩ : syracuseStep 5186951 = 7780427) B7780427
theorem B3457967 : Blo 2303435 3457967 := bstep (se 1 (by rfl) ⟨2593475, by rfl⟩ : syracuseStep 3457967 = 5186951) B5186951
theorem B2305311 : Blo 2303435 2305311 := bstep (se 1 (by rfl) ⟨1728983, by rfl⟩ : syracuseStep 2305311 = 3457967) B3457967
theorem B3457973 : Blo 2303435 3457973 := bbase (se 5 (by rfl) ⟨162092, by rfl⟩ : syracuseStep 3457973 = 324185) (by norm_num)
theorem B2305315 : Blo 2303435 2305315 := bstep (se 1 (by rfl) ⟨1728986, by rfl⟩ : syracuseStep 2305315 = 3457973) B3457973
theorem B5835341 : Blo 2303435 5835341 := bbase (se 3 (by rfl) ⟨1094126, by rfl⟩ : syracuseStep 5835341 = 2188253) (by norm_num)
theorem B3890227 : Blo 2303435 3890227 := bstep (se 1 (by rfl) ⟨2917670, by rfl⟩ : syracuseStep 3890227 = 5835341) B5835341
theorem B5186969 : Blo 2303435 5186969 := bstep (se 2 (by rfl) ⟨1945113, by rfl⟩ : syracuseStep 5186969 = 3890227) B3890227
theorem B3457979 : Blo 2303435 3457979 := bstep (se 1 (by rfl) ⟨2593484, by rfl⟩ : syracuseStep 3457979 = 5186969) B5186969
theorem B2305319 : Blo 2303435 2305319 := bstep (se 1 (by rfl) ⟨1728989, by rfl⟩ : syracuseStep 2305319 = 3457979) B3457979
theorem B2593489 : Blo 2303435 2593489 := bbase (se 2 (by rfl) ⟨972558, by rfl⟩ : syracuseStep 2593489 = 1945117) (by norm_num)
theorem B3457985 : Blo 2303435 3457985 := bstep (se 2 (by rfl) ⟨1296744, by rfl⟩ : syracuseStep 3457985 = 2593489) B2593489
theorem B2305323 : Blo 2303435 2305323 := bstep (se 1 (by rfl) ⟨1728992, by rfl⟩ : syracuseStep 2305323 = 3457985) B3457985
theorem B7385381 : Blo 2303435 7385381 := bbase (se 4 (by rfl) ⟨692379, by rfl⟩ : syracuseStep 7385381 = 1384759) (by norm_num)
theorem B4923587 : Blo 2303435 4923587 := bstep (se 1 (by rfl) ⟨3692690, by rfl⟩ : syracuseStep 4923587 = 7385381) B7385381
theorem B3282391 : Blo 2303435 3282391 := bstep (se 1 (by rfl) ⟨2461793, by rfl⟩ : syracuseStep 3282391 = 4923587) B4923587
theorem B4376521 : Blo 2303435 4376521 := bstep (se 2 (by rfl) ⟨1641195, by rfl⟩ : syracuseStep 4376521 = 3282391) B3282391
theorem B5835361 : Blo 2303435 5835361 := bstep (se 2 (by rfl) ⟨2188260, by rfl⟩ : syracuseStep 5835361 = 4376521) B4376521
theorem B7780481 : Blo 2303435 7780481 := bstep (se 2 (by rfl) ⟨2917680, by rfl⟩ : syracuseStep 7780481 = 5835361) B5835361
theorem B5186987 : Blo 2303435 5186987 := bstep (se 1 (by rfl) ⟨3890240, by rfl⟩ : syracuseStep 5186987 = 7780481) B7780481
theorem B3457991 : Blo 2303435 3457991 := bstep (se 1 (by rfl) ⟨2593493, by rfl⟩ : syracuseStep 3457991 = 5186987) B5186987
theorem B2305327 : Blo 2303435 2305327 := bstep (se 1 (by rfl) ⟨1728995, by rfl⟩ : syracuseStep 2305327 = 3457991) B3457991
theorem B3457997 : Blo 2303435 3457997 := bbase (se 3 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 3457997 = 1296749) (by norm_num)
theorem B2305331 : Blo 2303435 2305331 := bstep (se 1 (by rfl) ⟨1728998, by rfl⟩ : syracuseStep 2305331 = 3457997) B3457997
theorem B5187005 : Blo 2303435 5187005 := bbase (se 3 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 5187005 = 1945127) (by norm_num)
theorem B3458003 : Blo 2303435 3458003 := bstep (se 1 (by rfl) ⟨2593502, by rfl⟩ : syracuseStep 3458003 = 5187005) B5187005
theorem B2305335 : Blo 2303435 2305335 := bstep (se 1 (by rfl) ⟨1729001, by rfl⟩ : syracuseStep 2305335 = 3458003) B3458003
theorem B3890261 : Blo 2303435 3890261 := bbase (se 8 (by rfl) ⟨22794, by rfl⟩ : syracuseStep 3890261 = 45589) (by norm_num)
theorem B2593507 : Blo 2303435 2593507 := bstep (se 1 (by rfl) ⟨1945130, by rfl⟩ : syracuseStep 2593507 = 3890261) B3890261
theorem B3458009 : Blo 2303435 3458009 := bstep (se 2 (by rfl) ⟨1296753, by rfl⟩ : syracuseStep 3458009 = 2593507) B2593507
theorem B2305339 : Blo 2303435 2305339 := bstep (se 1 (by rfl) ⟨1729004, by rfl⟩ : syracuseStep 2305339 = 3458009) B3458009
theorem B2336797 : Blo 2303435 2336797 := bbase (se 3 (by rfl) ⟨438149, by rfl⟩ : syracuseStep 2336797 = 876299) (by norm_num)
theorem B3115729 : Blo 2303435 3115729 := bstep (se 2 (by rfl) ⟨1168398, by rfl⟩ : syracuseStep 3115729 = 2336797) B2336797
theorem B16617221 : Blo 2303435 16617221 := bstep (se 4 (by rfl) ⟨1557864, by rfl⟩ : syracuseStep 16617221 = 3115729) B3115729
theorem B11078147 : Blo 2303435 11078147 := bstep (se 1 (by rfl) ⟨8308610, by rfl⟩ : syracuseStep 11078147 = 16617221) B16617221
theorem B7385431 : Blo 2303435 7385431 := bstep (se 1 (by rfl) ⟨5539073, by rfl⟩ : syracuseStep 7385431 = 11078147) B11078147
theorem B9847241 : Blo 2303435 9847241 := bstep (se 2 (by rfl) ⟨3692715, by rfl⟩ : syracuseStep 9847241 = 7385431) B7385431
theorem B6564827 : Blo 2303435 6564827 := bstep (se 1 (by rfl) ⟨4923620, by rfl⟩ : syracuseStep 6564827 = 9847241) B9847241
theorem B17506205 : Blo 2303435 17506205 := bstep (se 3 (by rfl) ⟨3282413, by rfl⟩ : syracuseStep 17506205 = 6564827) B6564827
theorem B11670803 : Blo 2303435 11670803 := bstep (se 1 (by rfl) ⟨8753102, by rfl⟩ : syracuseStep 11670803 = 17506205) B17506205
theorem B7780535 : Blo 2303435 7780535 := bstep (se 1 (by rfl) ⟨5835401, by rfl⟩ : syracuseStep 7780535 = 11670803) B11670803
theorem B5187023 : Blo 2303435 5187023 := bstep (se 1 (by rfl) ⟨3890267, by rfl⟩ : syracuseStep 5187023 = 7780535) B7780535
theorem B3458015 : Blo 2303435 3458015 := bstep (se 1 (by rfl) ⟨2593511, by rfl⟩ : syracuseStep 3458015 = 5187023) B5187023
theorem B2305343 : Blo 2303435 2305343 := bstep (se 1 (by rfl) ⟨1729007, by rfl⟩ : syracuseStep 2305343 = 3458015) B3458015
theorem B3458021 : Blo 2303435 3458021 := bbase (se 4 (by rfl) ⟨324189, by rfl⟩ : syracuseStep 3458021 = 648379) (by norm_num)
theorem B2305347 : Blo 2303435 2305347 := bstep (se 1 (by rfl) ⟨1729010, by rfl⟩ : syracuseStep 2305347 = 3458021) B3458021
theorem B3115741 : Blo 2303435 3115741 := bbase (se 3 (by rfl) ⟨584201, by rfl⟩ : syracuseStep 3115741 = 1168403) (by norm_num)
theorem B4154321 : Blo 2303435 4154321 := bstep (se 2 (by rfl) ⟨1557870, by rfl⟩ : syracuseStep 4154321 = 3115741) B3115741
theorem B2769547 : Blo 2303435 2769547 := bstep (se 1 (by rfl) ⟨2077160, by rfl⟩ : syracuseStep 2769547 = 4154321) B4154321
theorem B3692729 : Blo 2303435 3692729 := bstep (se 2 (by rfl) ⟨1384773, by rfl⟩ : syracuseStep 3692729 = 2769547) B2769547
theorem B9847277 : Blo 2303435 9847277 := bstep (se 3 (by rfl) ⟨1846364, by rfl⟩ : syracuseStep 9847277 = 3692729) B3692729
theorem B6564851 : Blo 2303435 6564851 := bstep (se 1 (by rfl) ⟨4923638, by rfl⟩ : syracuseStep 6564851 = 9847277) B9847277
theorem B4376567 : Blo 2303435 4376567 := bstep (se 1 (by rfl) ⟨3282425, by rfl⟩ : syracuseStep 4376567 = 6564851) B6564851
theorem B2917711 : Blo 2303435 2917711 := bstep (se 1 (by rfl) ⟨2188283, by rfl⟩ : syracuseStep 2917711 = 4376567) B4376567
theorem B3890281 : Blo 2303435 3890281 := bstep (se 2 (by rfl) ⟨1458855, by rfl⟩ : syracuseStep 3890281 = 2917711) B2917711
theorem B5187041 : Blo 2303435 5187041 := bstep (se 2 (by rfl) ⟨1945140, by rfl⟩ : syracuseStep 5187041 = 3890281) B3890281
theorem B3458027 : Blo 2303435 3458027 := bstep (se 1 (by rfl) ⟨2593520, by rfl⟩ : syracuseStep 3458027 = 5187041) B5187041
theorem B2305351 : Blo 2303435 2305351 := bstep (se 1 (by rfl) ⟨1729013, by rfl⟩ : syracuseStep 2305351 = 3458027) B3458027
theorem B2593525 : Blo 2303435 2593525 := bbase (se 5 (by rfl) ⟨121571, by rfl⟩ : syracuseStep 2593525 = 243143) (by norm_num)
theorem B3458033 : Blo 2303435 3458033 := bstep (se 2 (by rfl) ⟨1296762, by rfl⟩ : syracuseStep 3458033 = 2593525) B2593525
theorem B2305355 : Blo 2303435 2305355 := bstep (se 1 (by rfl) ⟨1729016, by rfl⟩ : syracuseStep 2305355 = 3458033) B3458033
theorem B2917721 : Blo 2303435 2917721 := bbase (se 2 (by rfl) ⟨1094145, by rfl⟩ : syracuseStep 2917721 = 2188291) (by norm_num)
theorem B7780589 : Blo 2303435 7780589 := bstep (se 3 (by rfl) ⟨1458860, by rfl⟩ : syracuseStep 7780589 = 2917721) B2917721
theorem B5187059 : Blo 2303435 5187059 := bstep (se 1 (by rfl) ⟨3890294, by rfl⟩ : syracuseStep 5187059 = 7780589) B7780589
theorem B3458039 : Blo 2303435 3458039 := bstep (se 1 (by rfl) ⟨2593529, by rfl⟩ : syracuseStep 3458039 = 5187059) B5187059
theorem B2305359 : Blo 2303435 2305359 := bstep (se 1 (by rfl) ⟨1729019, by rfl⟩ : syracuseStep 2305359 = 3458039) B3458039
theorem B3458045 : Blo 2303435 3458045 := bbase (se 3 (by rfl) ⟨648383, by rfl⟩ : syracuseStep 3458045 = 1296767) (by norm_num)
theorem B2305363 : Blo 2303435 2305363 := bstep (se 1 (by rfl) ⟨1729022, by rfl⟩ : syracuseStep 2305363 = 3458045) B3458045
theorem B5187077 : Blo 2303435 5187077 := bbase (se 4 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 5187077 = 972577) (by norm_num)
theorem B3458051 : Blo 2303435 3458051 := bstep (se 1 (by rfl) ⟨2593538, by rfl⟩ : syracuseStep 3458051 = 5187077) B5187077
theorem B2305367 : Blo 2303435 2305367 := bstep (se 1 (by rfl) ⟨1729025, by rfl⟩ : syracuseStep 2305367 = 3458051) B3458051
theorem B4376605 : Blo 2303435 4376605 := bbase (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) (by norm_num)
theorem B5835473 : Blo 2303435 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B3890315 : Blo 2303435 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B2593543 : Blo 2303435 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B3458057 : Blo 2303435 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B2305371 : Blo 2303435 2305371 := bstep (se 1 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 2305371 = 3458057) B3458057
theorem B11670965 : Blo 2303435 11670965 := bbase (se 5 (by rfl) ⟨547076, by rfl⟩ : syracuseStep 11670965 = 1094153) (by norm_num)
theorem B7780643 : Blo 2303435 7780643 := bstep (se 1 (by rfl) ⟨5835482, by rfl⟩ : syracuseStep 7780643 = 11670965) B11670965
theorem B5187095 : Blo 2303435 5187095 := bstep (se 1 (by rfl) ⟨3890321, by rfl⟩ : syracuseStep 5187095 = 7780643) B7780643
theorem B3458063 : Blo 2303435 3458063 := bstep (se 1 (by rfl) ⟨2593547, by rfl⟩ : syracuseStep 3458063 = 5187095) B5187095
theorem B2305375 : Blo 2303435 2305375 := bstep (se 1 (by rfl) ⟨1729031, by rfl⟩ : syracuseStep 2305375 = 3458063) B3458063
theorem B3458069 : Blo 2303435 3458069 := bbase (se 6 (by rfl) ⟨81048, by rfl⟩ : syracuseStep 3458069 = 162097) (by norm_num)
theorem B2305379 : Blo 2303435 2305379 := bstep (se 1 (by rfl) ⟨1729034, by rfl⟩ : syracuseStep 2305379 = 3458069) B3458069
theorem B37389397 : Blo 2303435 37389397 := bbase (se 8 (by rfl) ⟨219078, by rfl⟩ : syracuseStep 37389397 = 438157) (by norm_num)
theorem B49852529 : Blo 2303435 49852529 := bstep (se 2 (by rfl) ⟨18694698, by rfl⟩ : syracuseStep 49852529 = 37389397) B37389397
theorem B33235019 : Blo 2303435 33235019 := bstep (se 1 (by rfl) ⟨24926264, by rfl⟩ : syracuseStep 33235019 = 49852529) B49852529
theorem B22156679 : Blo 2303435 22156679 := bstep (se 1 (by rfl) ⟨16617509, by rfl⟩ : syracuseStep 22156679 = 33235019) B33235019
theorem B14771119 : Blo 2303435 14771119 := bstep (se 1 (by rfl) ⟨11078339, by rfl⟩ : syracuseStep 14771119 = 22156679) B22156679
theorem B19694825 : Blo 2303435 19694825 := bstep (se 2 (by rfl) ⟨7385559, by rfl⟩ : syracuseStep 19694825 = 14771119) B14771119
theorem B13129883 : Blo 2303435 13129883 := bstep (se 1 (by rfl) ⟨9847412, by rfl⟩ : syracuseStep 13129883 = 19694825) B19694825
theorem B8753255 : Blo 2303435 8753255 := bstep (se 1 (by rfl) ⟨6564941, by rfl⟩ : syracuseStep 8753255 = 13129883) B13129883
theorem B5835503 : Blo 2303435 5835503 := bstep (se 1 (by rfl) ⟨4376627, by rfl⟩ : syracuseStep 5835503 = 8753255) B8753255
theorem B3890335 : Blo 2303435 3890335 := bstep (se 1 (by rfl) ⟨2917751, by rfl⟩ : syracuseStep 3890335 = 5835503) B5835503
theorem B5187113 : Blo 2303435 5187113 := bstep (se 2 (by rfl) ⟨1945167, by rfl⟩ : syracuseStep 5187113 = 3890335) B3890335
theorem B3458075 : Blo 2303435 3458075 := bstep (se 1 (by rfl) ⟨2593556, by rfl⟩ : syracuseStep 3458075 = 5187113) B5187113
theorem B2305383 : Blo 2303435 2305383 := bstep (se 1 (by rfl) ⟨1729037, by rfl⟩ : syracuseStep 2305383 = 3458075) B3458075
theorem B2593561 : Blo 2303435 2593561 := bbase (se 2 (by rfl) ⟨972585, by rfl⟩ : syracuseStep 2593561 = 1945171) (by norm_num)
theorem B3458081 : Blo 2303435 3458081 := bstep (se 2 (by rfl) ⟨1296780, by rfl⟩ : syracuseStep 3458081 = 2593561) B2593561
theorem B2305387 : Blo 2303435 2305387 := bstep (se 1 (by rfl) ⟨1729040, by rfl⟩ : syracuseStep 2305387 = 3458081) B3458081
theorem B8753285 : Blo 2303435 8753285 := bbase (se 4 (by rfl) ⟨820620, by rfl⟩ : syracuseStep 8753285 = 1641241) (by norm_num)
theorem B5835523 : Blo 2303435 5835523 := bstep (se 1 (by rfl) ⟨4376642, by rfl⟩ : syracuseStep 5835523 = 8753285) B8753285
theorem B7780697 : Blo 2303435 7780697 := bstep (se 2 (by rfl) ⟨2917761, by rfl⟩ : syracuseStep 7780697 = 5835523) B5835523
theorem B5187131 : Blo 2303435 5187131 := bstep (se 1 (by rfl) ⟨3890348, by rfl⟩ : syracuseStep 5187131 = 7780697) B7780697
theorem B3458087 : Blo 2303435 3458087 := bstep (se 1 (by rfl) ⟨2593565, by rfl⟩ : syracuseStep 3458087 = 5187131) B5187131
theorem B2305391 : Blo 2303435 2305391 := bstep (se 1 (by rfl) ⟨1729043, by rfl⟩ : syracuseStep 2305391 = 3458087) B3458087
theorem B3458093 : Blo 2303435 3458093 := bbase (se 3 (by rfl) ⟨648392, by rfl⟩ : syracuseStep 3458093 = 1296785) (by norm_num)
theorem B2305395 : Blo 2303435 2305395 := bstep (se 1 (by rfl) ⟨1729046, by rfl⟩ : syracuseStep 2305395 = 3458093) B3458093
theorem B5187149 : Blo 2303435 5187149 := bbase (se 3 (by rfl) ⟨972590, by rfl⟩ : syracuseStep 5187149 = 1945181) (by norm_num)
theorem B3458099 : Blo 2303435 3458099 := bstep (se 1 (by rfl) ⟨2593574, by rfl⟩ : syracuseStep 3458099 = 5187149) B5187149
theorem B2305399 : Blo 2303435 2305399 := bstep (se 1 (by rfl) ⟨1729049, by rfl⟩ : syracuseStep 2305399 = 3458099) B3458099
theorem B2917777 : Blo 2303435 2917777 := bbase (se 2 (by rfl) ⟨1094166, by rfl⟩ : syracuseStep 2917777 = 2188333) (by norm_num)
theorem B3890369 : Blo 2303435 3890369 := bstep (se 2 (by rfl) ⟨1458888, by rfl⟩ : syracuseStep 3890369 = 2917777) B2917777
theorem B2593579 : Blo 2303435 2593579 := bstep (se 1 (by rfl) ⟨1945184, by rfl⟩ : syracuseStep 2593579 = 3890369) B3890369
theorem B3458105 : Blo 2303435 3458105 := bstep (se 2 (by rfl) ⟨1296789, by rfl⟩ : syracuseStep 3458105 = 2593579) B2593579
theorem B2305403 : Blo 2303435 2305403 := bstep (se 1 (by rfl) ⟨1729052, by rfl⟩ : syracuseStep 2305403 = 3458105) B3458105
theorem B4923757 : Blo 2303435 4923757 := bbase (se 3 (by rfl) ⟨923204, by rfl⟩ : syracuseStep 4923757 = 1846409) (by norm_num)
theorem B26260037 : Blo 2303435 26260037 := bstep (se 4 (by rfl) ⟨2461878, by rfl⟩ : syracuseStep 26260037 = 4923757) B4923757
theorem B17506691 : Blo 2303435 17506691 := bstep (se 1 (by rfl) ⟨13130018, by rfl⟩ : syracuseStep 17506691 = 26260037) B26260037
theorem B11671127 : Blo 2303435 11671127 := bstep (se 1 (by rfl) ⟨8753345, by rfl⟩ : syracuseStep 11671127 = 17506691) B17506691
theorem B7780751 : Blo 2303435 7780751 := bstep (se 1 (by rfl) ⟨5835563, by rfl⟩ : syracuseStep 7780751 = 11671127) B11671127
theorem B5187167 : Blo 2303435 5187167 := bstep (se 1 (by rfl) ⟨3890375, by rfl⟩ : syracuseStep 5187167 = 7780751) B7780751
theorem B3458111 : Blo 2303435 3458111 := bstep (se 1 (by rfl) ⟨2593583, by rfl⟩ : syracuseStep 3458111 = 5187167) B5187167
theorem B2305407 : Blo 2303435 2305407 := bstep (se 1 (by rfl) ⟨1729055, by rfl⟩ : syracuseStep 2305407 = 3458111) B3458111
theorem B3458117 : Blo 2303435 3458117 := bbase (se 4 (by rfl) ⟨324198, by rfl⟩ : syracuseStep 3458117 = 648397) (by norm_num)
theorem B2305411 : Blo 2303435 2305411 := bstep (se 1 (by rfl) ⟨1729058, by rfl⟩ : syracuseStep 2305411 = 3458117) B3458117
theorem B3890389 : Blo 2303435 3890389 := bbase (se 7 (by rfl) ⟨45590, by rfl⟩ : syracuseStep 3890389 = 91181) (by norm_num)
theorem B5187185 : Blo 2303435 5187185 := bstep (se 2 (by rfl) ⟨1945194, by rfl⟩ : syracuseStep 5187185 = 3890389) B3890389
theorem B3458123 : Blo 2303435 3458123 := bstep (se 1 (by rfl) ⟨2593592, by rfl⟩ : syracuseStep 3458123 = 5187185) B5187185
theorem B2305415 : Blo 2303435 2305415 := bstep (se 1 (by rfl) ⟨1729061, by rfl⟩ : syracuseStep 2305415 = 3458123) B3458123
theorem B2593597 : Blo 2303435 2593597 := bbase (se 3 (by rfl) ⟨486299, by rfl⟩ : syracuseStep 2593597 = 972599) (by norm_num)
theorem B3458129 : Blo 2303435 3458129 := bstep (se 2 (by rfl) ⟨1296798, by rfl⟩ : syracuseStep 3458129 = 2593597) B2593597
theorem B2305419 : Blo 2303435 2305419 := bstep (se 1 (by rfl) ⟨1729064, by rfl⟩ : syracuseStep 2305419 = 3458129) B3458129
theorem B7780805 : Blo 2303435 7780805 := bbase (se 4 (by rfl) ⟨729450, by rfl⟩ : syracuseStep 7780805 = 1458901) (by norm_num)
theorem B5187203 : Blo 2303435 5187203 := bstep (se 1 (by rfl) ⟨3890402, by rfl⟩ : syracuseStep 5187203 = 7780805) B7780805
theorem B3458135 : Blo 2303435 3458135 := bstep (se 1 (by rfl) ⟨2593601, by rfl⟩ : syracuseStep 3458135 = 5187203) B5187203
theorem B2305423 : Blo 2303435 2305423 := bstep (se 1 (by rfl) ⟨1729067, by rfl⟩ : syracuseStep 2305423 = 3458135) B3458135
theorem B3458141 : Blo 2303435 3458141 := bbase (se 3 (by rfl) ⟨648401, by rfl⟩ : syracuseStep 3458141 = 1296803) (by norm_num)
theorem B2305427 : Blo 2303435 2305427 := bstep (se 1 (by rfl) ⟨1729070, by rfl⟩ : syracuseStep 2305427 = 3458141) B3458141
theorem B5187221 : Blo 2303435 5187221 := bbase (se 6 (by rfl) ⟨121575, by rfl⟩ : syracuseStep 5187221 = 243151) (by norm_num)
theorem B3458147 : Blo 2303435 3458147 := bstep (se 1 (by rfl) ⟨2593610, by rfl⟩ : syracuseStep 3458147 = 5187221) B5187221
theorem B2305431 : Blo 2303435 2305431 := bstep (se 1 (by rfl) ⟨1729073, by rfl⟩ : syracuseStep 2305431 = 3458147) B3458147
theorem B2461909 : Blo 2303435 2461909 := bbase (se 7 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 2461909 = 57701) (by norm_num)
theorem B3282545 : Blo 2303435 3282545 := bstep (se 2 (by rfl) ⟨1230954, by rfl⟩ : syracuseStep 3282545 = 2461909) B2461909
theorem B8753453 : Blo 2303435 8753453 := bstep (se 3 (by rfl) ⟨1641272, by rfl⟩ : syracuseStep 8753453 = 3282545) B3282545
theorem B5835635 : Blo 2303435 5835635 := bstep (se 1 (by rfl) ⟨4376726, by rfl⟩ : syracuseStep 5835635 = 8753453) B8753453
theorem B3890423 : Blo 2303435 3890423 := bstep (se 1 (by rfl) ⟨2917817, by rfl⟩ : syracuseStep 3890423 = 5835635) B5835635
theorem B2593615 : Blo 2303435 2593615 := bstep (se 1 (by rfl) ⟨1945211, by rfl⟩ : syracuseStep 2593615 = 3890423) B3890423
theorem B3458153 : Blo 2303435 3458153 := bstep (se 2 (by rfl) ⟨1296807, by rfl⟩ : syracuseStep 3458153 = 2593615) B2593615
theorem B2305435 : Blo 2303435 2305435 := bstep (se 1 (by rfl) ⟨1729076, by rfl⟩ : syracuseStep 2305435 = 3458153) B3458153
theorem C0 (j : ℕ) (h1 : 575858 ≤ j) (h2 : j ≤ 576358) : Blo 2303435 (4 * j + 3) := by
  interval_cases j
  · exact B2303435
  · exact B2303439
  · exact B2303443
  · exact B2303447
  · exact B2303451
  · exact B2303455
  · exact B2303459
  · exact B2303463
  · exact B2303467
  · exact B2303471
  · exact B2303475
  · exact B2303479
  · exact B2303483
  · exact B2303487
  · exact B2303491
  · exact B2303495
  · exact B2303499
  · exact B2303503
  · exact B2303507
  · exact B2303511
  · exact B2303515
  · exact B2303519
  · exact B2303523
  · exact B2303527
  · exact B2303531
  · exact B2303535
  · exact B2303539
  · exact B2303543
  · exact B2303547
  · exact B2303551
  · exact B2303555
  · exact B2303559
  · exact B2303563
  · exact B2303567
  · exact B2303571
  · exact B2303575
  · exact B2303579
  · exact B2303583
  · exact B2303587
  · exact B2303591
  · exact B2303595
  · exact B2303599
  · exact B2303603
  · exact B2303607
  · exact B2303611
  · exact B2303615
  · exact B2303619
  · exact B2303623
  · exact B2303627
  · exact B2303631
  · exact B2303635
  · exact B2303639
  · exact B2303643
  · exact B2303647
  · exact B2303651
  · exact B2303655
  · exact B2303659
  · exact B2303663
  · exact B2303667
  · exact B2303671
  · exact B2303675
  · exact B2303679
  · exact B2303683
  · exact B2303687
  · exact B2303691
  · exact B2303695
  · exact B2303699
  · exact B2303703
  · exact B2303707
  · exact B2303711
  · exact B2303715
  · exact B2303719
  · exact B2303723
  · exact B2303727
  · exact B2303731
  · exact B2303735
  · exact B2303739
  · exact B2303743
  · exact B2303747
  · exact B2303751
  · exact B2303755
  · exact B2303759
  · exact B2303763
  · exact B2303767
  · exact B2303771
  · exact B2303775
  · exact B2303779
  · exact B2303783
  · exact B2303787
  · exact B2303791
  · exact B2303795
  · exact B2303799
  · exact B2303803
  · exact B2303807
  · exact B2303811
  · exact B2303815
  · exact B2303819
  · exact B2303823
  · exact B2303827
  · exact B2303831
  · exact B2303835
  · exact B2303839
  · exact B2303843
  · exact B2303847
  · exact B2303851
  · exact B2303855
  · exact B2303859
  · exact B2303863
  · exact B2303867
  · exact B2303871
  · exact B2303875
  · exact B2303879
  · exact B2303883
  · exact B2303887
  · exact B2303891
  · exact B2303895
  · exact B2303899
  · exact B2303903
  · exact B2303907
  · exact B2303911
  · exact B2303915
  · exact B2303919
  · exact B2303923
  · exact B2303927
  · exact B2303931
  · exact B2303935
  · exact B2303939
  · exact B2303943
  · exact B2303947
  · exact B2303951
  · exact B2303955
  · exact B2303959
  · exact B2303963
  · exact B2303967
  · exact B2303971
  · exact B2303975
  · exact B2303979
  · exact B2303983
  · exact B2303987
  · exact B2303991
  · exact B2303995
  · exact B2303999
  · exact B2304003
  · exact B2304007
  · exact B2304011
  · exact B2304015
  · exact B2304019
  · exact B2304023
  · exact B2304027
  · exact B2304031
  · exact B2304035
  · exact B2304039
  · exact B2304043
  · exact B2304047
  · exact B2304051
  · exact B2304055
  · exact B2304059
  · exact B2304063
  · exact B2304067
  · exact B2304071
  · exact B2304075
  · exact B2304079
  · exact B2304083
  · exact B2304087
  · exact B2304091
  · exact B2304095
  · exact B2304099
  · exact B2304103
  · exact B2304107
  · exact B2304111
  · exact B2304115
  · exact B2304119
  · exact B2304123
  · exact B2304127
  · exact B2304131
  · exact B2304135
  · exact B2304139
  · exact B2304143
  · exact B2304147
  · exact B2304151
  · exact B2304155
  · exact B2304159
  · exact B2304163
  · exact B2304167
  · exact B2304171
  · exact B2304175
  · exact B2304179
  · exact B2304183
  · exact B2304187
  · exact B2304191
  · exact B2304195
  · exact B2304199
  · exact B2304203
  · exact B2304207
  · exact B2304211
  · exact B2304215
  · exact B2304219
  · exact B2304223
  · exact B2304227
  · exact B2304231
  · exact B2304235
  · exact B2304239
  · exact B2304243
  · exact B2304247
  · exact B2304251
  · exact B2304255
  · exact B2304259
  · exact B2304263
  · exact B2304267
  · exact B2304271
  · exact B2304275
  · exact B2304279
  · exact B2304283
  · exact B2304287
  · exact B2304291
  · exact B2304295
  · exact B2304299
  · exact B2304303
  · exact B2304307
  · exact B2304311
  · exact B2304315
  · exact B2304319
  · exact B2304323
  · exact B2304327
  · exact B2304331
  · exact B2304335
  · exact B2304339
  · exact B2304343
  · exact B2304347
  · exact B2304351
  · exact B2304355
  · exact B2304359
  · exact B2304363
  · exact B2304367
  · exact B2304371
  · exact B2304375
  · exact B2304379
  · exact B2304383
  · exact B2304387
  · exact B2304391
  · exact B2304395
  · exact B2304399
  · exact B2304403
  · exact B2304407
  · exact B2304411
  · exact B2304415
  · exact B2304419
  · exact B2304423
  · exact B2304427
  · exact B2304431
  · exact B2304435
  · exact B2304439
  · exact B2304443
  · exact B2304447
  · exact B2304451
  · exact B2304455
  · exact B2304459
  · exact B2304463
  · exact B2304467
  · exact B2304471
  · exact B2304475
  · exact B2304479
  · exact B2304483
  · exact B2304487
  · exact B2304491
  · exact B2304495
  · exact B2304499
  · exact B2304503
  · exact B2304507
  · exact B2304511
  · exact B2304515
  · exact B2304519
  · exact B2304523
  · exact B2304527
  · exact B2304531
  · exact B2304535
  · exact B2304539
  · exact B2304543
  · exact B2304547
  · exact B2304551
  · exact B2304555
  · exact B2304559
  · exact B2304563
  · exact B2304567
  · exact B2304571
  · exact B2304575
  · exact B2304579
  · exact B2304583
  · exact B2304587
  · exact B2304591
  · exact B2304595
  · exact B2304599
  · exact B2304603
  · exact B2304607
  · exact B2304611
  · exact B2304615
  · exact B2304619
  · exact B2304623
  · exact B2304627
  · exact B2304631
  · exact B2304635
  · exact B2304639
  · exact B2304643
  · exact B2304647
  · exact B2304651
  · exact B2304655
  · exact B2304659
  · exact B2304663
  · exact B2304667
  · exact B2304671
  · exact B2304675
  · exact B2304679
  · exact B2304683
  · exact B2304687
  · exact B2304691
  · exact B2304695
  · exact B2304699
  · exact B2304703
  · exact B2304707
  · exact B2304711
  · exact B2304715
  · exact B2304719
  · exact B2304723
  · exact B2304727
  · exact B2304731
  · exact B2304735
  · exact B2304739
  · exact B2304743
  · exact B2304747
  · exact B2304751
  · exact B2304755
  · exact B2304759
  · exact B2304763
  · exact B2304767
  · exact B2304771
  · exact B2304775
  · exact B2304779
  · exact B2304783
  · exact B2304787
  · exact B2304791
  · exact B2304795
  · exact B2304799
  · exact B2304803
  · exact B2304807
  · exact B2304811
  · exact B2304815
  · exact B2304819
  · exact B2304823
  · exact B2304827
  · exact B2304831
  · exact B2304835
  · exact B2304839
  · exact B2304843
  · exact B2304847
  · exact B2304851
  · exact B2304855
  · exact B2304859
  · exact B2304863
  · exact B2304867
  · exact B2304871
  · exact B2304875
  · exact B2304879
  · exact B2304883
  · exact B2304887
  · exact B2304891
  · exact B2304895
  · exact B2304899
  · exact B2304903
  · exact B2304907
  · exact B2304911
  · exact B2304915
  · exact B2304919
  · exact B2304923
  · exact B2304927
  · exact B2304931
  · exact B2304935
  · exact B2304939
  · exact B2304943
  · exact B2304947
  · exact B2304951
  · exact B2304955
  · exact B2304959
  · exact B2304963
  · exact B2304967
  · exact B2304971
  · exact B2304975
  · exact B2304979
  · exact B2304983
  · exact B2304987
  · exact B2304991
  · exact B2304995
  · exact B2304999
  · exact B2305003
  · exact B2305007
  · exact B2305011
  · exact B2305015
  · exact B2305019
  · exact B2305023
  · exact B2305027
  · exact B2305031
  · exact B2305035
  · exact B2305039
  · exact B2305043
  · exact B2305047
  · exact B2305051
  · exact B2305055
  · exact B2305059
  · exact B2305063
  · exact B2305067
  · exact B2305071
  · exact B2305075
  · exact B2305079
  · exact B2305083
  · exact B2305087
  · exact B2305091
  · exact B2305095
  · exact B2305099
  · exact B2305103
  · exact B2305107
  · exact B2305111
  · exact B2305115
  · exact B2305119
  · exact B2305123
  · exact B2305127
  · exact B2305131
  · exact B2305135
  · exact B2305139
  · exact B2305143
  · exact B2305147
  · exact B2305151
  · exact B2305155
  · exact B2305159
  · exact B2305163
  · exact B2305167
  · exact B2305171
  · exact B2305175
  · exact B2305179
  · exact B2305183
  · exact B2305187
  · exact B2305191
  · exact B2305195
  · exact B2305199
  · exact B2305203
  · exact B2305207
  · exact B2305211
  · exact B2305215
  · exact B2305219
  · exact B2305223
  · exact B2305227
  · exact B2305231
  · exact B2305235
  · exact B2305239
  · exact B2305243
  · exact B2305247
  · exact B2305251
  · exact B2305255
  · exact B2305259
  · exact B2305263
  · exact B2305267
  · exact B2305271
  · exact B2305275
  · exact B2305279
  · exact B2305283
  · exact B2305287
  · exact B2305291
  · exact B2305295
  · exact B2305299
  · exact B2305303
  · exact B2305307
  · exact B2305311
  · exact B2305315
  · exact B2305319
  · exact B2305323
  · exact B2305327
  · exact B2305331
  · exact B2305335
  · exact B2305339
  · exact B2305343
  · exact B2305347
  · exact B2305351
  · exact B2305355
  · exact B2305359
  · exact B2305363
  · exact B2305367
  · exact B2305371
  · exact B2305375
  · exact B2305379
  · exact B2305383
  · exact B2305387
  · exact B2305391
  · exact B2305395
  · exact B2305399
  · exact B2305403
  · exact B2305407
  · exact B2305411
  · exact B2305415
  · exact B2305419
  · exact B2305423
  · exact B2305427
  · exact B2305431
  · exact B2305435
theorem solution (m : ℕ) (hlo : 2303435 ≤ m) (hhi : m ≤ 2305435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 575858 ≤ j := by omega
    have hj2 : j ≤ 576358 := by omega
    have hb : Blo 2303435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
