-- Prove2me | solution 1 for syracuse_descends_range_2105435_2107435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:39.726059+00:00
-- url     : https://prove2.me/submissions/7719fecf-42a1-45f5-b150-80ddd5b33319

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

theorem B2845549 : Blo 2105435 2845549 := bbase (se 3 (by rfl) ⟨533540, by rfl⟩ : syracuseStep 2845549 = 1067081) (by norm_num)
theorem B15176261 : Blo 2105435 15176261 := bstep (se 4 (by rfl) ⟨1422774, by rfl⟩ : syracuseStep 15176261 = 2845549) B2845549
theorem B10117507 : Blo 2105435 10117507 := bstep (se 1 (by rfl) ⟨7588130, by rfl⟩ : syracuseStep 10117507 = 15176261) B15176261
theorem B13490009 : Blo 2105435 13490009 := bstep (se 2 (by rfl) ⟨5058753, by rfl⟩ : syracuseStep 13490009 = 10117507) B10117507
theorem B8993339 : Blo 2105435 8993339 := bstep (se 1 (by rfl) ⟨6745004, by rfl⟩ : syracuseStep 8993339 = 13490009) B13490009
theorem B5995559 : Blo 2105435 5995559 := bstep (se 1 (by rfl) ⟨4496669, by rfl⟩ : syracuseStep 5995559 = 8993339) B8993339
theorem B3997039 : Blo 2105435 3997039 := bstep (se 1 (by rfl) ⟨2997779, by rfl⟩ : syracuseStep 3997039 = 5995559) B5995559
theorem B5329385 : Blo 2105435 5329385 := bstep (se 2 (by rfl) ⟨1998519, by rfl⟩ : syracuseStep 5329385 = 3997039) B3997039
theorem B3552923 : Blo 2105435 3552923 := bstep (se 1 (by rfl) ⟨2664692, by rfl⟩ : syracuseStep 3552923 = 5329385) B5329385
theorem B2368615 : Blo 2105435 2368615 := bstep (se 1 (by rfl) ⟨1776461, by rfl⟩ : syracuseStep 2368615 = 3552923) B3552923
theorem B3158153 : Blo 2105435 3158153 := bstep (se 2 (by rfl) ⟨1184307, by rfl⟩ : syracuseStep 3158153 = 2368615) B2368615
theorem B2105435 : Blo 2105435 2105435 := bstep (se 1 (by rfl) ⟨1579076, by rfl⟩ : syracuseStep 2105435 = 3158153) B3158153
theorem B10658789 : Blo 2105435 10658789 := bbase (se 4 (by rfl) ⟨999261, by rfl⟩ : syracuseStep 10658789 = 1998523) (by norm_num)
theorem B7105859 : Blo 2105435 7105859 := bstep (se 1 (by rfl) ⟨5329394, by rfl⟩ : syracuseStep 7105859 = 10658789) B10658789
theorem B4737239 : Blo 2105435 4737239 := bstep (se 1 (by rfl) ⟨3552929, by rfl⟩ : syracuseStep 4737239 = 7105859) B7105859
theorem B3158159 : Blo 2105435 3158159 := bstep (se 1 (by rfl) ⟨2368619, by rfl⟩ : syracuseStep 3158159 = 4737239) B4737239
theorem B2105439 : Blo 2105435 2105439 := bstep (se 1 (by rfl) ⟨1579079, by rfl⟩ : syracuseStep 2105439 = 3158159) B3158159
theorem B3158165 : Blo 2105435 3158165 := bbase (se 6 (by rfl) ⟨74019, by rfl⟩ : syracuseStep 3158165 = 148039) (by norm_num)
theorem B2105443 : Blo 2105435 2105443 := bstep (se 1 (by rfl) ⟨1579082, by rfl⟩ : syracuseStep 2105443 = 3158165) B3158165
theorem B16206389 : Blo 2105435 16206389 := bbase (se 5 (by rfl) ⟨759674, by rfl⟩ : syracuseStep 16206389 = 1519349) (by norm_num)
theorem B10804259 : Blo 2105435 10804259 := bstep (se 1 (by rfl) ⟨8103194, by rfl⟩ : syracuseStep 10804259 = 16206389) B16206389
theorem B7202839 : Blo 2105435 7202839 := bstep (se 1 (by rfl) ⟨5402129, by rfl⟩ : syracuseStep 7202839 = 10804259) B10804259
theorem B9603785 : Blo 2105435 9603785 := bstep (se 2 (by rfl) ⟨3601419, by rfl⟩ : syracuseStep 9603785 = 7202839) B7202839
theorem B6402523 : Blo 2105435 6402523 := bstep (se 1 (by rfl) ⟨4801892, by rfl⟩ : syracuseStep 6402523 = 9603785) B9603785
theorem B8536697 : Blo 2105435 8536697 := bstep (se 2 (by rfl) ⟨3201261, by rfl⟩ : syracuseStep 8536697 = 6402523) B6402523
theorem B5691131 : Blo 2105435 5691131 := bstep (se 1 (by rfl) ⟨4268348, by rfl⟩ : syracuseStep 5691131 = 8536697) B8536697
theorem B3794087 : Blo 2105435 3794087 := bstep (se 1 (by rfl) ⟨2845565, by rfl⟩ : syracuseStep 3794087 = 5691131) B5691131
theorem B2529391 : Blo 2105435 2529391 := bstep (se 1 (by rfl) ⟨1897043, by rfl⟩ : syracuseStep 2529391 = 3794087) B3794087
theorem B3372521 : Blo 2105435 3372521 := bstep (se 2 (by rfl) ⟨1264695, by rfl⟩ : syracuseStep 3372521 = 2529391) B2529391
theorem B8993389 : Blo 2105435 8993389 := bstep (se 3 (by rfl) ⟨1686260, by rfl⟩ : syracuseStep 8993389 = 3372521) B3372521
theorem B11991185 : Blo 2105435 11991185 := bstep (se 2 (by rfl) ⟨4496694, by rfl⟩ : syracuseStep 11991185 = 8993389) B8993389
theorem B7994123 : Blo 2105435 7994123 := bstep (se 1 (by rfl) ⟨5995592, by rfl⟩ : syracuseStep 7994123 = 11991185) B11991185
theorem B5329415 : Blo 2105435 5329415 := bstep (se 1 (by rfl) ⟨3997061, by rfl⟩ : syracuseStep 5329415 = 7994123) B7994123
theorem B3552943 : Blo 2105435 3552943 := bstep (se 1 (by rfl) ⟨2664707, by rfl⟩ : syracuseStep 3552943 = 5329415) B5329415
theorem B4737257 : Blo 2105435 4737257 := bstep (se 2 (by rfl) ⟨1776471, by rfl⟩ : syracuseStep 4737257 = 3552943) B3552943
theorem B3158171 : Blo 2105435 3158171 := bstep (se 1 (by rfl) ⟨2368628, by rfl⟩ : syracuseStep 3158171 = 4737257) B4737257
theorem B2105447 : Blo 2105435 2105447 := bstep (se 1 (by rfl) ⟨1579085, by rfl⟩ : syracuseStep 2105447 = 3158171) B3158171
theorem B2368633 : Blo 2105435 2368633 := bbase (se 2 (by rfl) ⟨888237, by rfl⟩ : syracuseStep 2368633 = 1776475) (by norm_num)
theorem B3158177 : Blo 2105435 3158177 := bstep (se 2 (by rfl) ⟨1184316, by rfl⟩ : syracuseStep 3158177 = 2368633) B2368633
theorem B2105451 : Blo 2105435 2105451 := bstep (se 1 (by rfl) ⟨1579088, by rfl⟩ : syracuseStep 2105451 = 3158177) B3158177
theorem B19207637 : Blo 2105435 19207637 := bbase (se 7 (by rfl) ⟨225089, by rfl⟩ : syracuseStep 19207637 = 450179) (by norm_num)
theorem B12805091 : Blo 2105435 12805091 := bstep (se 1 (by rfl) ⟨9603818, by rfl⟩ : syracuseStep 12805091 = 19207637) B19207637
theorem B8536727 : Blo 2105435 8536727 := bstep (se 1 (by rfl) ⟨6402545, by rfl⟩ : syracuseStep 8536727 = 12805091) B12805091
theorem B5691151 : Blo 2105435 5691151 := bstep (se 1 (by rfl) ⟨4268363, by rfl⟩ : syracuseStep 5691151 = 8536727) B8536727
theorem B30352805 : Blo 2105435 30352805 := bstep (se 4 (by rfl) ⟨2845575, by rfl⟩ : syracuseStep 30352805 = 5691151) B5691151
theorem B20235203 : Blo 2105435 20235203 := bstep (se 1 (by rfl) ⟨15176402, by rfl⟩ : syracuseStep 20235203 = 30352805) B30352805
theorem B13490135 : Blo 2105435 13490135 := bstep (se 1 (by rfl) ⟨10117601, by rfl⟩ : syracuseStep 13490135 = 20235203) B20235203
theorem B8993423 : Blo 2105435 8993423 := bstep (se 1 (by rfl) ⟨6745067, by rfl⟩ : syracuseStep 8993423 = 13490135) B13490135
theorem B5995615 : Blo 2105435 5995615 := bstep (se 1 (by rfl) ⟨4496711, by rfl⟩ : syracuseStep 5995615 = 8993423) B8993423
theorem B7994153 : Blo 2105435 7994153 := bstep (se 2 (by rfl) ⟨2997807, by rfl⟩ : syracuseStep 7994153 = 5995615) B5995615
theorem B5329435 : Blo 2105435 5329435 := bstep (se 1 (by rfl) ⟨3997076, by rfl⟩ : syracuseStep 5329435 = 7994153) B7994153
theorem B7105913 : Blo 2105435 7105913 := bstep (se 2 (by rfl) ⟨2664717, by rfl⟩ : syracuseStep 7105913 = 5329435) B5329435
theorem B4737275 : Blo 2105435 4737275 := bstep (se 1 (by rfl) ⟨3552956, by rfl⟩ : syracuseStep 4737275 = 7105913) B7105913
theorem B3158183 : Blo 2105435 3158183 := bstep (se 1 (by rfl) ⟨2368637, by rfl⟩ : syracuseStep 3158183 = 4737275) B4737275
theorem B2105455 : Blo 2105435 2105455 := bstep (se 1 (by rfl) ⟨1579091, by rfl⟩ : syracuseStep 2105455 = 3158183) B3158183
theorem B3158189 : Blo 2105435 3158189 := bbase (se 3 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 3158189 = 1184321) (by norm_num)
theorem B2105459 : Blo 2105435 2105459 := bstep (se 1 (by rfl) ⟨1579094, by rfl⟩ : syracuseStep 2105459 = 3158189) B3158189
theorem B4737293 : Blo 2105435 4737293 := bbase (se 3 (by rfl) ⟨888242, by rfl⟩ : syracuseStep 4737293 = 1776485) (by norm_num)
theorem B3158195 : Blo 2105435 3158195 := bstep (se 1 (by rfl) ⟨2368646, by rfl⟩ : syracuseStep 3158195 = 4737293) B4737293
theorem B2105463 : Blo 2105435 2105463 := bstep (se 1 (by rfl) ⟨1579097, by rfl⟩ : syracuseStep 2105463 = 3158195) B3158195
theorem B2664733 : Blo 2105435 2664733 := bbase (se 3 (by rfl) ⟨499637, by rfl⟩ : syracuseStep 2664733 = 999275) (by norm_num)
theorem B3552977 : Blo 2105435 3552977 := bstep (se 2 (by rfl) ⟨1332366, by rfl⟩ : syracuseStep 3552977 = 2664733) B2664733
theorem B2368651 : Blo 2105435 2368651 := bstep (se 1 (by rfl) ⟨1776488, by rfl⟩ : syracuseStep 2368651 = 3552977) B3552977
theorem B3158201 : Blo 2105435 3158201 := bstep (se 2 (by rfl) ⟨1184325, by rfl⟩ : syracuseStep 3158201 = 2368651) B2368651
theorem B2105467 : Blo 2105435 2105467 := bstep (se 1 (by rfl) ⟨1579100, by rfl⟩ : syracuseStep 2105467 = 3158201) B3158201
theorem B11382389 : Blo 2105435 11382389 := bbase (se 5 (by rfl) ⟨533549, by rfl⟩ : syracuseStep 11382389 = 1067099) (by norm_num)
theorem B7588259 : Blo 2105435 7588259 := bstep (se 1 (by rfl) ⟨5691194, by rfl⟩ : syracuseStep 7588259 = 11382389) B11382389
theorem B5058839 : Blo 2105435 5058839 := bstep (se 1 (by rfl) ⟨3794129, by rfl⟩ : syracuseStep 5058839 = 7588259) B7588259
theorem B3372559 : Blo 2105435 3372559 := bstep (se 1 (by rfl) ⟨2529419, by rfl⟩ : syracuseStep 3372559 = 5058839) B5058839
theorem B17986981 : Blo 2105435 17986981 := bstep (se 4 (by rfl) ⟨1686279, by rfl⟩ : syracuseStep 17986981 = 3372559) B3372559
theorem B23982641 : Blo 2105435 23982641 := bstep (se 2 (by rfl) ⟨8993490, by rfl⟩ : syracuseStep 23982641 = 17986981) B17986981
theorem B15988427 : Blo 2105435 15988427 := bstep (se 1 (by rfl) ⟨11991320, by rfl⟩ : syracuseStep 15988427 = 23982641) B23982641
theorem B10658951 : Blo 2105435 10658951 := bstep (se 1 (by rfl) ⟨7994213, by rfl⟩ : syracuseStep 10658951 = 15988427) B15988427
theorem B7105967 : Blo 2105435 7105967 := bstep (se 1 (by rfl) ⟨5329475, by rfl⟩ : syracuseStep 7105967 = 10658951) B10658951
theorem B4737311 : Blo 2105435 4737311 := bstep (se 1 (by rfl) ⟨3552983, by rfl⟩ : syracuseStep 4737311 = 7105967) B7105967
theorem B3158207 : Blo 2105435 3158207 := bstep (se 1 (by rfl) ⟨2368655, by rfl⟩ : syracuseStep 3158207 = 4737311) B4737311
theorem B2105471 : Blo 2105435 2105471 := bstep (se 1 (by rfl) ⟨1579103, by rfl⟩ : syracuseStep 2105471 = 3158207) B3158207
theorem B3158213 : Blo 2105435 3158213 := bbase (se 4 (by rfl) ⟨296082, by rfl⟩ : syracuseStep 3158213 = 592165) (by norm_num)
theorem B2105475 : Blo 2105435 2105475 := bstep (se 1 (by rfl) ⟨1579106, by rfl⟩ : syracuseStep 2105475 = 3158213) B3158213
theorem B3552997 : Blo 2105435 3552997 := bbase (se 4 (by rfl) ⟨333093, by rfl⟩ : syracuseStep 3552997 = 666187) (by norm_num)
theorem B4737329 : Blo 2105435 4737329 := bstep (se 2 (by rfl) ⟨1776498, by rfl⟩ : syracuseStep 4737329 = 3552997) B3552997
theorem B3158219 : Blo 2105435 3158219 := bstep (se 1 (by rfl) ⟨2368664, by rfl⟩ : syracuseStep 3158219 = 4737329) B4737329
theorem B2105479 : Blo 2105435 2105479 := bstep (se 1 (by rfl) ⟨1579109, by rfl⟩ : syracuseStep 2105479 = 3158219) B3158219
theorem B2368669 : Blo 2105435 2368669 := bbase (se 3 (by rfl) ⟨444125, by rfl⟩ : syracuseStep 2368669 = 888251) (by norm_num)
theorem B3158225 : Blo 2105435 3158225 := bstep (se 2 (by rfl) ⟨1184334, by rfl⟩ : syracuseStep 3158225 = 2368669) B2368669
theorem B2105483 : Blo 2105435 2105483 := bstep (se 1 (by rfl) ⟨1579112, by rfl⟩ : syracuseStep 2105483 = 3158225) B3158225
theorem B7106021 : Blo 2105435 7106021 := bbase (se 4 (by rfl) ⟨666189, by rfl⟩ : syracuseStep 7106021 = 1332379) (by norm_num)
theorem B4737347 : Blo 2105435 4737347 := bstep (se 1 (by rfl) ⟨3553010, by rfl⟩ : syracuseStep 4737347 = 7106021) B7106021
theorem B3158231 : Blo 2105435 3158231 := bstep (se 1 (by rfl) ⟨2368673, by rfl⟩ : syracuseStep 3158231 = 4737347) B4737347
theorem B2105487 : Blo 2105435 2105487 := bstep (se 1 (by rfl) ⟨1579115, by rfl⟩ : syracuseStep 2105487 = 3158231) B3158231
theorem B3158237 : Blo 2105435 3158237 := bbase (se 3 (by rfl) ⟨592169, by rfl⟩ : syracuseStep 3158237 = 1184339) (by norm_num)
theorem B2105491 : Blo 2105435 2105491 := bstep (se 1 (by rfl) ⟨1579118, by rfl⟩ : syracuseStep 2105491 = 3158237) B3158237
theorem B4737365 : Blo 2105435 4737365 := bbase (se 10 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 4737365 = 13879) (by norm_num)
theorem B3158243 : Blo 2105435 3158243 := bstep (se 1 (by rfl) ⟨2368682, by rfl⟩ : syracuseStep 3158243 = 4737365) B4737365
theorem B2105495 : Blo 2105435 2105495 := bstep (se 1 (by rfl) ⟨1579121, by rfl⟩ : syracuseStep 2105495 = 3158243) B3158243
theorem B3372605 : Blo 2105435 3372605 := bbase (se 3 (by rfl) ⟨632363, by rfl⟩ : syracuseStep 3372605 = 1264727) (by norm_num)
theorem B2248403 : Blo 2105435 2248403 := bstep (se 1 (by rfl) ⟨1686302, by rfl⟩ : syracuseStep 2248403 = 3372605) B3372605
theorem B5995741 : Blo 2105435 5995741 := bstep (se 3 (by rfl) ⟨1124201, by rfl⟩ : syracuseStep 5995741 = 2248403) B2248403
theorem B7994321 : Blo 2105435 7994321 := bstep (se 2 (by rfl) ⟨2997870, by rfl⟩ : syracuseStep 7994321 = 5995741) B5995741
theorem B5329547 : Blo 2105435 5329547 := bstep (se 1 (by rfl) ⟨3997160, by rfl⟩ : syracuseStep 5329547 = 7994321) B7994321
theorem B3553031 : Blo 2105435 3553031 := bstep (se 1 (by rfl) ⟨2664773, by rfl⟩ : syracuseStep 3553031 = 5329547) B5329547
theorem B2368687 : Blo 2105435 2368687 := bstep (se 1 (by rfl) ⟨1776515, by rfl⟩ : syracuseStep 2368687 = 3553031) B3553031
theorem B3158249 : Blo 2105435 3158249 := bstep (se 2 (by rfl) ⟨1184343, by rfl⟩ : syracuseStep 3158249 = 2368687) B2368687
theorem B2105499 : Blo 2105435 2105499 := bstep (se 1 (by rfl) ⟨1579124, by rfl⟩ : syracuseStep 2105499 = 3158249) B3158249
theorem B2401009 : Blo 2105435 2401009 := bbase (se 2 (by rfl) ⟨900378, by rfl⟩ : syracuseStep 2401009 = 1800757) (by norm_num)
theorem B12805381 : Blo 2105435 12805381 := bstep (se 4 (by rfl) ⟨1200504, by rfl⟩ : syracuseStep 12805381 = 2401009) B2401009
theorem B17073841 : Blo 2105435 17073841 := bstep (se 2 (by rfl) ⟨6402690, by rfl⟩ : syracuseStep 17073841 = 12805381) B12805381
theorem B22765121 : Blo 2105435 22765121 := bstep (se 2 (by rfl) ⟨8536920, by rfl⟩ : syracuseStep 22765121 = 17073841) B17073841
theorem B15176747 : Blo 2105435 15176747 := bstep (se 1 (by rfl) ⟨11382560, by rfl⟩ : syracuseStep 15176747 = 22765121) B22765121
theorem B40471325 : Blo 2105435 40471325 := bstep (se 3 (by rfl) ⟨7588373, by rfl⟩ : syracuseStep 40471325 = 15176747) B15176747
theorem B26980883 : Blo 2105435 26980883 := bstep (se 1 (by rfl) ⟨20235662, by rfl⟩ : syracuseStep 26980883 = 40471325) B40471325
theorem B17987255 : Blo 2105435 17987255 := bstep (se 1 (by rfl) ⟨13490441, by rfl⟩ : syracuseStep 17987255 = 26980883) B26980883
theorem B11991503 : Blo 2105435 11991503 := bstep (se 1 (by rfl) ⟨8993627, by rfl⟩ : syracuseStep 11991503 = 17987255) B17987255
theorem B7994335 : Blo 2105435 7994335 := bstep (se 1 (by rfl) ⟨5995751, by rfl⟩ : syracuseStep 7994335 = 11991503) B11991503
theorem B10659113 : Blo 2105435 10659113 := bstep (se 2 (by rfl) ⟨3997167, by rfl⟩ : syracuseStep 10659113 = 7994335) B7994335
theorem B7106075 : Blo 2105435 7106075 := bstep (se 1 (by rfl) ⟨5329556, by rfl⟩ : syracuseStep 7106075 = 10659113) B10659113
theorem B4737383 : Blo 2105435 4737383 := bstep (se 1 (by rfl) ⟨3553037, by rfl⟩ : syracuseStep 4737383 = 7106075) B7106075
theorem B3158255 : Blo 2105435 3158255 := bstep (se 1 (by rfl) ⟨2368691, by rfl⟩ : syracuseStep 3158255 = 4737383) B4737383
theorem B2105503 : Blo 2105435 2105503 := bstep (se 1 (by rfl) ⟨1579127, by rfl⟩ : syracuseStep 2105503 = 3158255) B3158255
theorem B3158261 : Blo 2105435 3158261 := bbase (se 5 (by rfl) ⟨148043, by rfl⟩ : syracuseStep 3158261 = 296087) (by norm_num)
theorem B2105507 : Blo 2105435 2105507 := bstep (se 1 (by rfl) ⟨1579130, by rfl⟩ : syracuseStep 2105507 = 3158261) B3158261
theorem B5475997 : Blo 2105435 5475997 := bbase (se 3 (by rfl) ⟨1026749, by rfl⟩ : syracuseStep 5475997 = 2053499) (by norm_num)
theorem B7301329 : Blo 2105435 7301329 := bstep (se 2 (by rfl) ⟨2737998, by rfl⟩ : syracuseStep 7301329 = 5475997) B5475997
theorem B38940421 : Blo 2105435 38940421 := bstep (se 4 (by rfl) ⟨3650664, by rfl⟩ : syracuseStep 38940421 = 7301329) B7301329
theorem B51920561 : Blo 2105435 51920561 := bstep (se 2 (by rfl) ⟨19470210, by rfl⟩ : syracuseStep 51920561 = 38940421) B38940421
theorem B138454829 : Blo 2105435 138454829 := bstep (se 3 (by rfl) ⟨25960280, by rfl⟩ : syracuseStep 138454829 = 51920561) B51920561
theorem B92303219 : Blo 2105435 92303219 := bstep (se 1 (by rfl) ⟨69227414, by rfl⟩ : syracuseStep 92303219 = 138454829) B138454829
theorem B61535479 : Blo 2105435 61535479 := bstep (se 1 (by rfl) ⟨46151609, by rfl⟩ : syracuseStep 61535479 = 92303219) B92303219
theorem B82047305 : Blo 2105435 82047305 := bstep (se 2 (by rfl) ⟨30767739, by rfl⟩ : syracuseStep 82047305 = 61535479) B61535479
theorem B54698203 : Blo 2105435 54698203 := bstep (se 1 (by rfl) ⟨41023652, by rfl⟩ : syracuseStep 54698203 = 82047305) B82047305
theorem B72930937 : Blo 2105435 72930937 := bstep (se 2 (by rfl) ⟨27349101, by rfl⟩ : syracuseStep 72930937 = 54698203) B54698203
theorem B97241249 : Blo 2105435 97241249 := bstep (se 2 (by rfl) ⟨36465468, by rfl⟩ : syracuseStep 97241249 = 72930937) B72930937
theorem B64827499 : Blo 2105435 64827499 := bstep (se 1 (by rfl) ⟨48620624, by rfl⟩ : syracuseStep 64827499 = 97241249) B97241249
theorem B86436665 : Blo 2105435 86436665 := bstep (se 2 (by rfl) ⟨32413749, by rfl⟩ : syracuseStep 86436665 = 64827499) B64827499
theorem B57624443 : Blo 2105435 57624443 := bstep (se 1 (by rfl) ⟨43218332, by rfl⟩ : syracuseStep 57624443 = 86436665) B86436665
theorem B38416295 : Blo 2105435 38416295 := bstep (se 1 (by rfl) ⟨28812221, by rfl⟩ : syracuseStep 38416295 = 57624443) B57624443
theorem B102443453 : Blo 2105435 102443453 := bstep (se 3 (by rfl) ⟨19208147, by rfl⟩ : syracuseStep 102443453 = 38416295) B38416295
theorem B68295635 : Blo 2105435 68295635 := bstep (se 1 (by rfl) ⟨51221726, by rfl⟩ : syracuseStep 68295635 = 102443453) B102443453
theorem B45530423 : Blo 2105435 45530423 := bstep (se 1 (by rfl) ⟨34147817, by rfl⟩ : syracuseStep 45530423 = 68295635) B68295635
theorem B30353615 : Blo 2105435 30353615 := bstep (se 1 (by rfl) ⟨22765211, by rfl⟩ : syracuseStep 30353615 = 45530423) B45530423
theorem B20235743 : Blo 2105435 20235743 := bstep (se 1 (by rfl) ⟨15176807, by rfl⟩ : syracuseStep 20235743 = 30353615) B30353615
theorem B13490495 : Blo 2105435 13490495 := bstep (se 1 (by rfl) ⟨10117871, by rfl⟩ : syracuseStep 13490495 = 20235743) B20235743
theorem B8993663 : Blo 2105435 8993663 := bstep (se 1 (by rfl) ⟨6745247, by rfl⟩ : syracuseStep 8993663 = 13490495) B13490495
theorem B5995775 : Blo 2105435 5995775 := bstep (se 1 (by rfl) ⟨4496831, by rfl⟩ : syracuseStep 5995775 = 8993663) B8993663
theorem B3997183 : Blo 2105435 3997183 := bstep (se 1 (by rfl) ⟨2997887, by rfl⟩ : syracuseStep 3997183 = 5995775) B5995775
theorem B5329577 : Blo 2105435 5329577 := bstep (se 2 (by rfl) ⟨1998591, by rfl⟩ : syracuseStep 5329577 = 3997183) B3997183
theorem B3553051 : Blo 2105435 3553051 := bstep (se 1 (by rfl) ⟨2664788, by rfl⟩ : syracuseStep 3553051 = 5329577) B5329577
theorem B4737401 : Blo 2105435 4737401 := bstep (se 2 (by rfl) ⟨1776525, by rfl⟩ : syracuseStep 4737401 = 3553051) B3553051
theorem B3158267 : Blo 2105435 3158267 := bstep (se 1 (by rfl) ⟨2368700, by rfl⟩ : syracuseStep 3158267 = 4737401) B4737401
theorem B2105511 : Blo 2105435 2105511 := bstep (se 1 (by rfl) ⟨1579133, by rfl⟩ : syracuseStep 2105511 = 3158267) B3158267
theorem B2368705 : Blo 2105435 2368705 := bbase (se 2 (by rfl) ⟨888264, by rfl⟩ : syracuseStep 2368705 = 1776529) (by norm_num)
theorem B3158273 : Blo 2105435 3158273 := bstep (se 2 (by rfl) ⟨1184352, by rfl⟩ : syracuseStep 3158273 = 2368705) B2368705
theorem B2105515 : Blo 2105435 2105515 := bstep (se 1 (by rfl) ⟨1579136, by rfl⟩ : syracuseStep 2105515 = 3158273) B3158273
theorem B5329597 : Blo 2105435 5329597 := bbase (se 3 (by rfl) ⟨999299, by rfl⟩ : syracuseStep 5329597 = 1998599) (by norm_num)
theorem B7106129 : Blo 2105435 7106129 := bstep (se 2 (by rfl) ⟨2664798, by rfl⟩ : syracuseStep 7106129 = 5329597) B5329597
theorem B4737419 : Blo 2105435 4737419 := bstep (se 1 (by rfl) ⟨3553064, by rfl⟩ : syracuseStep 4737419 = 7106129) B7106129
theorem B3158279 : Blo 2105435 3158279 := bstep (se 1 (by rfl) ⟨2368709, by rfl⟩ : syracuseStep 3158279 = 4737419) B4737419
theorem B2105519 : Blo 2105435 2105519 := bstep (se 1 (by rfl) ⟨1579139, by rfl⟩ : syracuseStep 2105519 = 3158279) B3158279
theorem B3158285 : Blo 2105435 3158285 := bbase (se 3 (by rfl) ⟨592178, by rfl⟩ : syracuseStep 3158285 = 1184357) (by norm_num)
theorem B2105523 : Blo 2105435 2105523 := bstep (se 1 (by rfl) ⟨1579142, by rfl⟩ : syracuseStep 2105523 = 3158285) B3158285
theorem B4737437 : Blo 2105435 4737437 := bbase (se 3 (by rfl) ⟨888269, by rfl⟩ : syracuseStep 4737437 = 1776539) (by norm_num)
theorem B3158291 : Blo 2105435 3158291 := bstep (se 1 (by rfl) ⟨2368718, by rfl⟩ : syracuseStep 3158291 = 4737437) B4737437
theorem B2105527 : Blo 2105435 2105527 := bstep (se 1 (by rfl) ⟨1579145, by rfl⟩ : syracuseStep 2105527 = 3158291) B3158291
theorem B3553085 : Blo 2105435 3553085 := bbase (se 3 (by rfl) ⟨666203, by rfl⟩ : syracuseStep 3553085 = 1332407) (by norm_num)
theorem B2368723 : Blo 2105435 2368723 := bstep (se 1 (by rfl) ⟨1776542, by rfl⟩ : syracuseStep 2368723 = 3553085) B3553085
theorem B3158297 : Blo 2105435 3158297 := bstep (se 2 (by rfl) ⟨1184361, by rfl⟩ : syracuseStep 3158297 = 2368723) B2368723
theorem B2105531 : Blo 2105435 2105531 := bstep (se 1 (by rfl) ⟨1579148, by rfl⟩ : syracuseStep 2105531 = 3158297) B3158297
theorem B2248441 : Blo 2105435 2248441 := bbase (se 2 (by rfl) ⟨843165, by rfl⟩ : syracuseStep 2248441 = 1686331) (by norm_num)
theorem B11991685 : Blo 2105435 11991685 := bstep (se 4 (by rfl) ⟨1124220, by rfl⟩ : syracuseStep 11991685 = 2248441) B2248441
theorem B15988913 : Blo 2105435 15988913 := bstep (se 2 (by rfl) ⟨5995842, by rfl⟩ : syracuseStep 15988913 = 11991685) B11991685
theorem B10659275 : Blo 2105435 10659275 := bstep (se 1 (by rfl) ⟨7994456, by rfl⟩ : syracuseStep 10659275 = 15988913) B15988913
theorem B7106183 : Blo 2105435 7106183 := bstep (se 1 (by rfl) ⟨5329637, by rfl⟩ : syracuseStep 7106183 = 10659275) B10659275
theorem B4737455 : Blo 2105435 4737455 := bstep (se 1 (by rfl) ⟨3553091, by rfl⟩ : syracuseStep 4737455 = 7106183) B7106183
theorem B3158303 : Blo 2105435 3158303 := bstep (se 1 (by rfl) ⟨2368727, by rfl⟩ : syracuseStep 3158303 = 4737455) B4737455
theorem B2105535 : Blo 2105435 2105535 := bstep (se 1 (by rfl) ⟨1579151, by rfl⟩ : syracuseStep 2105535 = 3158303) B3158303
theorem B3158309 : Blo 2105435 3158309 := bbase (se 4 (by rfl) ⟨296091, by rfl⟩ : syracuseStep 3158309 = 592183) (by norm_num)
theorem B2105539 : Blo 2105435 2105539 := bstep (se 1 (by rfl) ⟨1579154, by rfl⟩ : syracuseStep 2105539 = 3158309) B3158309
theorem B2664829 : Blo 2105435 2664829 := bbase (se 3 (by rfl) ⟨499655, by rfl⟩ : syracuseStep 2664829 = 999311) (by norm_num)
theorem B3553105 : Blo 2105435 3553105 := bstep (se 2 (by rfl) ⟨1332414, by rfl⟩ : syracuseStep 3553105 = 2664829) B2664829
theorem B4737473 : Blo 2105435 4737473 := bstep (se 2 (by rfl) ⟨1776552, by rfl⟩ : syracuseStep 4737473 = 3553105) B3553105
theorem B3158315 : Blo 2105435 3158315 := bstep (se 1 (by rfl) ⟨2368736, by rfl⟩ : syracuseStep 3158315 = 4737473) B4737473
theorem B2105543 : Blo 2105435 2105543 := bstep (se 1 (by rfl) ⟨1579157, by rfl⟩ : syracuseStep 2105543 = 3158315) B3158315
theorem B2368741 : Blo 2105435 2368741 := bbase (se 4 (by rfl) ⟨222069, by rfl⟩ : syracuseStep 2368741 = 444139) (by norm_num)
theorem B3158321 : Blo 2105435 3158321 := bstep (se 2 (by rfl) ⟨1184370, by rfl⟩ : syracuseStep 3158321 = 2368741) B2368741
theorem B2105547 : Blo 2105435 2105547 := bstep (se 1 (by rfl) ⟨1579160, by rfl⟩ : syracuseStep 2105547 = 3158321) B3158321
theorem B4496917 : Blo 2105435 4496917 := bbase (se 6 (by rfl) ⟨105396, by rfl⟩ : syracuseStep 4496917 = 210793) (by norm_num)
theorem B5995889 : Blo 2105435 5995889 := bstep (se 2 (by rfl) ⟨2248458, by rfl⟩ : syracuseStep 5995889 = 4496917) B4496917
theorem B3997259 : Blo 2105435 3997259 := bstep (se 1 (by rfl) ⟨2997944, by rfl⟩ : syracuseStep 3997259 = 5995889) B5995889
theorem B2664839 : Blo 2105435 2664839 := bstep (se 1 (by rfl) ⟨1998629, by rfl⟩ : syracuseStep 2664839 = 3997259) B3997259
theorem B7106237 : Blo 2105435 7106237 := bstep (se 3 (by rfl) ⟨1332419, by rfl⟩ : syracuseStep 7106237 = 2664839) B2664839
theorem B4737491 : Blo 2105435 4737491 := bstep (se 1 (by rfl) ⟨3553118, by rfl⟩ : syracuseStep 4737491 = 7106237) B7106237
theorem B3158327 : Blo 2105435 3158327 := bstep (se 1 (by rfl) ⟨2368745, by rfl⟩ : syracuseStep 3158327 = 4737491) B4737491
theorem B2105551 : Blo 2105435 2105551 := bstep (se 1 (by rfl) ⟨1579163, by rfl⟩ : syracuseStep 2105551 = 3158327) B3158327
theorem B3158333 : Blo 2105435 3158333 := bbase (se 3 (by rfl) ⟨592187, by rfl⟩ : syracuseStep 3158333 = 1184375) (by norm_num)
theorem B2105555 : Blo 2105435 2105555 := bstep (se 1 (by rfl) ⟨1579166, by rfl⟩ : syracuseStep 2105555 = 3158333) B3158333
theorem B4737509 : Blo 2105435 4737509 := bbase (se 4 (by rfl) ⟨444141, by rfl⟩ : syracuseStep 4737509 = 888283) (by norm_num)
theorem B3158339 : Blo 2105435 3158339 := bstep (se 1 (by rfl) ⟨2368754, by rfl⟩ : syracuseStep 3158339 = 4737509) B4737509
theorem B2105559 : Blo 2105435 2105559 := bstep (se 1 (by rfl) ⟨1579169, by rfl⟩ : syracuseStep 2105559 = 3158339) B3158339
theorem B5329709 : Blo 2105435 5329709 := bbase (se 3 (by rfl) ⟨999320, by rfl⟩ : syracuseStep 5329709 = 1998641) (by norm_num)
theorem B3553139 : Blo 2105435 3553139 := bstep (se 1 (by rfl) ⟨2664854, by rfl⟩ : syracuseStep 3553139 = 5329709) B5329709
theorem B2368759 : Blo 2105435 2368759 := bstep (se 1 (by rfl) ⟨1776569, by rfl⟩ : syracuseStep 2368759 = 3553139) B3553139
theorem B3158345 : Blo 2105435 3158345 := bstep (se 2 (by rfl) ⟨1184379, by rfl⟩ : syracuseStep 3158345 = 2368759) B2368759
theorem B2105563 : Blo 2105435 2105563 := bstep (se 1 (by rfl) ⟨1579172, by rfl⟩ : syracuseStep 2105563 = 3158345) B3158345
theorem B25960981 : Blo 2105435 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B34614641 : Blo 2105435 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B23076427 : Blo 2105435 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B30768569 : Blo 2105435 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B20512379 : Blo 2105435 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B13674919 : Blo 2105435 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B18233225 : Blo 2105435 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B12155483 : Blo 2105435 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B8103655 : Blo 2105435 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B43219493 : Blo 2105435 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B28812995 : Blo 2105435 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B19208663 : Blo 2105435 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B12805775 : Blo 2105435 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B8537183 : Blo 2105435 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B5691455 : Blo 2105435 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B3794303 : Blo 2105435 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B10118141 : Blo 2105435 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B6745427 : Blo 2105435 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B4496951 : Blo 2105435 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B2997967 : Blo 2105435 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B3997289 : Blo 2105435 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B10659437 : Blo 2105435 10659437 := bstep (se 3 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 10659437 = 3997289) B3997289
theorem B7106291 : Blo 2105435 7106291 := bstep (se 1 (by rfl) ⟨5329718, by rfl⟩ : syracuseStep 7106291 = 10659437) B10659437
theorem B4737527 : Blo 2105435 4737527 := bstep (se 1 (by rfl) ⟨3553145, by rfl⟩ : syracuseStep 4737527 = 7106291) B7106291
theorem B3158351 : Blo 2105435 3158351 := bstep (se 1 (by rfl) ⟨2368763, by rfl⟩ : syracuseStep 3158351 = 4737527) B4737527
theorem B2105567 : Blo 2105435 2105567 := bstep (se 1 (by rfl) ⟨1579175, by rfl⟩ : syracuseStep 2105567 = 3158351) B3158351
theorem B3158357 : Blo 2105435 3158357 := bbase (se 10 (by rfl) ⟨4626, by rfl⟩ : syracuseStep 3158357 = 9253) (by norm_num)
theorem B2105571 : Blo 2105435 2105571 := bstep (se 1 (by rfl) ⟨1579178, by rfl⟩ : syracuseStep 2105571 = 3158357) B3158357
theorem B5995957 : Blo 2105435 5995957 := bbase (se 5 (by rfl) ⟨281060, by rfl⟩ : syracuseStep 5995957 = 562121) (by norm_num)
theorem B7994609 : Blo 2105435 7994609 := bstep (se 2 (by rfl) ⟨2997978, by rfl⟩ : syracuseStep 7994609 = 5995957) B5995957
theorem B5329739 : Blo 2105435 5329739 := bstep (se 1 (by rfl) ⟨3997304, by rfl⟩ : syracuseStep 5329739 = 7994609) B7994609
theorem B3553159 : Blo 2105435 3553159 := bstep (se 1 (by rfl) ⟨2664869, by rfl⟩ : syracuseStep 3553159 = 5329739) B5329739
theorem B4737545 : Blo 2105435 4737545 := bstep (se 2 (by rfl) ⟨1776579, by rfl⟩ : syracuseStep 4737545 = 3553159) B3553159
theorem B3158363 : Blo 2105435 3158363 := bstep (se 1 (by rfl) ⟨2368772, by rfl⟩ : syracuseStep 3158363 = 4737545) B4737545
theorem B2105575 : Blo 2105435 2105575 := bstep (se 1 (by rfl) ⟨1579181, by rfl⟩ : syracuseStep 2105575 = 3158363) B3158363
theorem B2368777 : Blo 2105435 2368777 := bbase (se 2 (by rfl) ⟨888291, by rfl⟩ : syracuseStep 2368777 = 1776583) (by norm_num)
theorem B3158369 : Blo 2105435 3158369 := bstep (se 2 (by rfl) ⟨1184388, by rfl⟩ : syracuseStep 3158369 = 2368777) B2368777
theorem B2105579 : Blo 2105435 2105579 := bstep (se 1 (by rfl) ⟨1579184, by rfl⟩ : syracuseStep 2105579 = 3158369) B3158369
theorem B26981909 : Blo 2105435 26981909 := bbase (se 6 (by rfl) ⟨632388, by rfl⟩ : syracuseStep 26981909 = 1264777) (by norm_num)
theorem B17987939 : Blo 2105435 17987939 := bstep (se 1 (by rfl) ⟨13490954, by rfl⟩ : syracuseStep 17987939 = 26981909) B26981909
theorem B11991959 : Blo 2105435 11991959 := bstep (se 1 (by rfl) ⟨8993969, by rfl⟩ : syracuseStep 11991959 = 17987939) B17987939
theorem B7994639 : Blo 2105435 7994639 := bstep (se 1 (by rfl) ⟨5995979, by rfl⟩ : syracuseStep 7994639 = 11991959) B11991959
theorem B5329759 : Blo 2105435 5329759 := bstep (se 1 (by rfl) ⟨3997319, by rfl⟩ : syracuseStep 5329759 = 7994639) B7994639
theorem B7106345 : Blo 2105435 7106345 := bstep (se 2 (by rfl) ⟨2664879, by rfl⟩ : syracuseStep 7106345 = 5329759) B5329759
theorem B4737563 : Blo 2105435 4737563 := bstep (se 1 (by rfl) ⟨3553172, by rfl⟩ : syracuseStep 4737563 = 7106345) B7106345
theorem B3158375 : Blo 2105435 3158375 := bstep (se 1 (by rfl) ⟨2368781, by rfl⟩ : syracuseStep 3158375 = 4737563) B4737563
theorem B2105583 : Blo 2105435 2105583 := bstep (se 1 (by rfl) ⟨1579187, by rfl⟩ : syracuseStep 2105583 = 3158375) B3158375
theorem B3158381 : Blo 2105435 3158381 := bbase (se 3 (by rfl) ⟨592196, by rfl⟩ : syracuseStep 3158381 = 1184393) (by norm_num)
theorem B2105587 : Blo 2105435 2105587 := bstep (se 1 (by rfl) ⟨1579190, by rfl⟩ : syracuseStep 2105587 = 3158381) B3158381
theorem B4737581 : Blo 2105435 4737581 := bbase (se 3 (by rfl) ⟨888296, by rfl⟩ : syracuseStep 4737581 = 1776593) (by norm_num)
theorem B3158387 : Blo 2105435 3158387 := bstep (se 1 (by rfl) ⟨2368790, by rfl⟩ : syracuseStep 3158387 = 4737581) B4737581
theorem B2105591 : Blo 2105435 2105591 := bstep (se 1 (by rfl) ⟨1579193, by rfl⟩ : syracuseStep 2105591 = 3158387) B3158387
theorem B19208917 : Blo 2105435 19208917 := bbase (se 7 (by rfl) ⟨225104, by rfl⟩ : syracuseStep 19208917 = 450209) (by norm_num)
theorem B25611889 : Blo 2105435 25611889 := bstep (se 2 (by rfl) ⟨9604458, by rfl⟩ : syracuseStep 25611889 = 19208917) B19208917
theorem B34149185 : Blo 2105435 34149185 := bstep (se 2 (by rfl) ⟨12805944, by rfl⟩ : syracuseStep 34149185 = 25611889) B25611889
theorem B22766123 : Blo 2105435 22766123 := bstep (se 1 (by rfl) ⟨17074592, by rfl⟩ : syracuseStep 22766123 = 34149185) B34149185
theorem B15177415 : Blo 2105435 15177415 := bstep (se 1 (by rfl) ⟨11383061, by rfl⟩ : syracuseStep 15177415 = 22766123) B22766123
theorem B20236553 : Blo 2105435 20236553 := bstep (se 2 (by rfl) ⟨7588707, by rfl⟩ : syracuseStep 20236553 = 15177415) B15177415
theorem B13491035 : Blo 2105435 13491035 := bstep (se 1 (by rfl) ⟨10118276, by rfl⟩ : syracuseStep 13491035 = 20236553) B20236553
theorem B8994023 : Blo 2105435 8994023 := bstep (se 1 (by rfl) ⟨6745517, by rfl⟩ : syracuseStep 8994023 = 13491035) B13491035
theorem B5996015 : Blo 2105435 5996015 := bstep (se 1 (by rfl) ⟨4497011, by rfl⟩ : syracuseStep 5996015 = 8994023) B8994023
theorem B3997343 : Blo 2105435 3997343 := bstep (se 1 (by rfl) ⟨2998007, by rfl⟩ : syracuseStep 3997343 = 5996015) B5996015
theorem B2664895 : Blo 2105435 2664895 := bstep (se 1 (by rfl) ⟨1998671, by rfl⟩ : syracuseStep 2664895 = 3997343) B3997343
theorem B3553193 : Blo 2105435 3553193 := bstep (se 2 (by rfl) ⟨1332447, by rfl⟩ : syracuseStep 3553193 = 2664895) B2664895
theorem B2368795 : Blo 2105435 2368795 := bstep (se 1 (by rfl) ⟨1776596, by rfl⟩ : syracuseStep 2368795 = 3553193) B3553193
theorem B3158393 : Blo 2105435 3158393 := bstep (se 2 (by rfl) ⟨1184397, by rfl⟩ : syracuseStep 3158393 = 2368795) B2368795
theorem B2105595 : Blo 2105435 2105595 := bstep (se 1 (by rfl) ⟨1579196, by rfl⟩ : syracuseStep 2105595 = 3158393) B3158393
theorem B35976149 : Blo 2105435 35976149 := bbase (se 7 (by rfl) ⟨421595, by rfl⟩ : syracuseStep 35976149 = 843191) (by norm_num)
theorem B23984099 : Blo 2105435 23984099 := bstep (se 1 (by rfl) ⟨17988074, by rfl⟩ : syracuseStep 23984099 = 35976149) B35976149
theorem B15989399 : Blo 2105435 15989399 := bstep (se 1 (by rfl) ⟨11992049, by rfl⟩ : syracuseStep 15989399 = 23984099) B23984099
theorem B10659599 : Blo 2105435 10659599 := bstep (se 1 (by rfl) ⟨7994699, by rfl⟩ : syracuseStep 10659599 = 15989399) B15989399
theorem B7106399 : Blo 2105435 7106399 := bstep (se 1 (by rfl) ⟨5329799, by rfl⟩ : syracuseStep 7106399 = 10659599) B10659599
theorem B4737599 : Blo 2105435 4737599 := bstep (se 1 (by rfl) ⟨3553199, by rfl⟩ : syracuseStep 4737599 = 7106399) B7106399
theorem B3158399 : Blo 2105435 3158399 := bstep (se 1 (by rfl) ⟨2368799, by rfl⟩ : syracuseStep 3158399 = 4737599) B4737599
theorem B2105599 : Blo 2105435 2105599 := bstep (se 1 (by rfl) ⟨1579199, by rfl⟩ : syracuseStep 2105599 = 3158399) B3158399
theorem B3158405 : Blo 2105435 3158405 := bbase (se 4 (by rfl) ⟨296100, by rfl⟩ : syracuseStep 3158405 = 592201) (by norm_num)
theorem B2105603 : Blo 2105435 2105603 := bstep (se 1 (by rfl) ⟨1579202, by rfl⟩ : syracuseStep 2105603 = 3158405) B3158405
theorem B3553213 : Blo 2105435 3553213 := bbase (se 3 (by rfl) ⟨666227, by rfl⟩ : syracuseStep 3553213 = 1332455) (by norm_num)
theorem B4737617 : Blo 2105435 4737617 := bstep (se 2 (by rfl) ⟨1776606, by rfl⟩ : syracuseStep 4737617 = 3553213) B3553213
theorem B3158411 : Blo 2105435 3158411 := bstep (se 1 (by rfl) ⟨2368808, by rfl⟩ : syracuseStep 3158411 = 4737617) B4737617
theorem B2105607 : Blo 2105435 2105607 := bstep (se 1 (by rfl) ⟨1579205, by rfl⟩ : syracuseStep 2105607 = 3158411) B3158411
theorem B2368813 : Blo 2105435 2368813 := bbase (se 3 (by rfl) ⟨444152, by rfl⟩ : syracuseStep 2368813 = 888305) (by norm_num)
theorem B3158417 : Blo 2105435 3158417 := bstep (se 2 (by rfl) ⟨1184406, by rfl⟩ : syracuseStep 3158417 = 2368813) B2368813
theorem B2105611 : Blo 2105435 2105611 := bstep (se 1 (by rfl) ⟨1579208, by rfl⟩ : syracuseStep 2105611 = 3158417) B3158417
theorem B7106453 : Blo 2105435 7106453 := bbase (se 6 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 7106453 = 333115) (by norm_num)
theorem B4737635 : Blo 2105435 4737635 := bstep (se 1 (by rfl) ⟨3553226, by rfl⟩ : syracuseStep 4737635 = 7106453) B7106453
theorem B3158423 : Blo 2105435 3158423 := bstep (se 1 (by rfl) ⟨2368817, by rfl⟩ : syracuseStep 3158423 = 4737635) B4737635
theorem B2105615 : Blo 2105435 2105615 := bstep (se 1 (by rfl) ⟨1579211, by rfl⟩ : syracuseStep 2105615 = 3158423) B3158423
theorem B3158429 : Blo 2105435 3158429 := bbase (se 3 (by rfl) ⟨592205, by rfl⟩ : syracuseStep 3158429 = 1184411) (by norm_num)
theorem B2105619 : Blo 2105435 2105619 := bstep (se 1 (by rfl) ⟨1579214, by rfl⟩ : syracuseStep 2105619 = 3158429) B3158429
theorem B4737653 : Blo 2105435 4737653 := bbase (se 5 (by rfl) ⟨222077, by rfl⟩ : syracuseStep 4737653 = 444155) (by norm_num)
theorem B3158435 : Blo 2105435 3158435 := bstep (se 1 (by rfl) ⟨2368826, by rfl⟩ : syracuseStep 3158435 = 4737653) B4737653
theorem B2105623 : Blo 2105435 2105623 := bstep (se 1 (by rfl) ⟨1579217, by rfl⟩ : syracuseStep 2105623 = 3158435) B3158435
theorem B6668741 : Blo 2105435 6668741 := bbase (se 4 (by rfl) ⟨625194, by rfl⟩ : syracuseStep 6668741 = 1250389) (by norm_num)
theorem B17783309 : Blo 2105435 17783309 := bstep (se 3 (by rfl) ⟨3334370, by rfl⟩ : syracuseStep 17783309 = 6668741) B6668741
theorem B47422157 : Blo 2105435 47422157 := bstep (se 3 (by rfl) ⟨8891654, by rfl⟩ : syracuseStep 47422157 = 17783309) B17783309
theorem B126459085 : Blo 2105435 126459085 := bstep (se 3 (by rfl) ⟨23711078, by rfl⟩ : syracuseStep 126459085 = 47422157) B47422157
theorem B168612113 : Blo 2105435 168612113 := bstep (se 2 (by rfl) ⟨63229542, by rfl⟩ : syracuseStep 168612113 = 126459085) B126459085
theorem B449632301 : Blo 2105435 449632301 := bstep (se 3 (by rfl) ⟨84306056, by rfl⟩ : syracuseStep 449632301 = 168612113) B168612113
theorem B1199019469 : Blo 2105435 1199019469 := bstep (se 3 (by rfl) ⟨224816150, by rfl⟩ : syracuseStep 1199019469 = 449632301) B449632301
theorem B1598692625 : Blo 2105435 1598692625 := bstep (se 2 (by rfl) ⟨599509734, by rfl⟩ : syracuseStep 1598692625 = 1199019469) B1199019469
theorem B1065795083 : Blo 2105435 1065795083 := bstep (se 1 (by rfl) ⟨799346312, by rfl⟩ : syracuseStep 1065795083 = 1598692625) B1598692625
theorem B710530055 : Blo 2105435 710530055 := bstep (se 1 (by rfl) ⟨532897541, by rfl⟩ : syracuseStep 710530055 = 1065795083) B1065795083
theorem B473686703 : Blo 2105435 473686703 := bstep (se 1 (by rfl) ⟨355265027, by rfl⟩ : syracuseStep 473686703 = 710530055) B710530055
theorem B315791135 : Blo 2105435 315791135 := bstep (se 1 (by rfl) ⟨236843351, by rfl⟩ : syracuseStep 315791135 = 473686703) B473686703
theorem B210527423 : Blo 2105435 210527423 := bstep (se 1 (by rfl) ⟨157895567, by rfl⟩ : syracuseStep 210527423 = 315791135) B315791135
theorem B140351615 : Blo 2105435 140351615 := bstep (se 1 (by rfl) ⟨105263711, by rfl⟩ : syracuseStep 140351615 = 210527423) B210527423
theorem B93567743 : Blo 2105435 93567743 := bstep (se 1 (by rfl) ⟨70175807, by rfl⟩ : syracuseStep 93567743 = 140351615) B140351615
theorem B62378495 : Blo 2105435 62378495 := bstep (se 1 (by rfl) ⟨46783871, by rfl⟩ : syracuseStep 62378495 = 93567743) B93567743
theorem B41585663 : Blo 2105435 41585663 := bstep (se 1 (by rfl) ⟨31189247, by rfl⟩ : syracuseStep 41585663 = 62378495) B62378495
theorem B110895101 : Blo 2105435 110895101 := bstep (se 3 (by rfl) ⟨20792831, by rfl⟩ : syracuseStep 110895101 = 41585663) B41585663
theorem B73930067 : Blo 2105435 73930067 := bstep (se 1 (by rfl) ⟨55447550, by rfl⟩ : syracuseStep 73930067 = 110895101) B110895101
theorem B49286711 : Blo 2105435 49286711 := bstep (se 1 (by rfl) ⟨36965033, by rfl⟩ : syracuseStep 49286711 = 73930067) B73930067
theorem B32857807 : Blo 2105435 32857807 := bstep (se 1 (by rfl) ⟨24643355, by rfl⟩ : syracuseStep 32857807 = 49286711) B49286711
theorem B43810409 : Blo 2105435 43810409 := bstep (se 2 (by rfl) ⟨16428903, by rfl⟩ : syracuseStep 43810409 = 32857807) B32857807
theorem B116827757 : Blo 2105435 116827757 := bstep (se 3 (by rfl) ⟨21905204, by rfl⟩ : syracuseStep 116827757 = 43810409) B43810409
theorem B77885171 : Blo 2105435 77885171 := bstep (se 1 (by rfl) ⟨58413878, by rfl⟩ : syracuseStep 77885171 = 116827757) B116827757
theorem B51923447 : Blo 2105435 51923447 := bstep (se 1 (by rfl) ⟨38942585, by rfl⟩ : syracuseStep 51923447 = 77885171) B77885171
theorem B34615631 : Blo 2105435 34615631 := bstep (se 1 (by rfl) ⟨25961723, by rfl⟩ : syracuseStep 34615631 = 51923447) B51923447
theorem B92308349 : Blo 2105435 92308349 := bstep (se 3 (by rfl) ⟨17307815, by rfl⟩ : syracuseStep 92308349 = 34615631) B34615631
theorem B61538899 : Blo 2105435 61538899 := bstep (se 1 (by rfl) ⟨46154174, by rfl⟩ : syracuseStep 61538899 = 92308349) B92308349
theorem B82051865 : Blo 2105435 82051865 := bstep (se 2 (by rfl) ⟨30769449, by rfl⟩ : syracuseStep 82051865 = 61538899) B61538899
theorem B54701243 : Blo 2105435 54701243 := bstep (se 1 (by rfl) ⟨41025932, by rfl⟩ : syracuseStep 54701243 = 82051865) B82051865
theorem B36467495 : Blo 2105435 36467495 := bstep (se 1 (by rfl) ⟨27350621, by rfl⟩ : syracuseStep 36467495 = 54701243) B54701243
theorem B24311663 : Blo 2105435 24311663 := bstep (se 1 (by rfl) ⟨18233747, by rfl⟩ : syracuseStep 24311663 = 36467495) B36467495
theorem B16207775 : Blo 2105435 16207775 := bstep (se 1 (by rfl) ⟨12155831, by rfl⟩ : syracuseStep 16207775 = 24311663) B24311663
theorem B10805183 : Blo 2105435 10805183 := bstep (se 1 (by rfl) ⟨8103887, by rfl⟩ : syracuseStep 10805183 = 16207775) B16207775
theorem B7203455 : Blo 2105435 7203455 := bstep (se 1 (by rfl) ⟨5402591, by rfl⟩ : syracuseStep 7203455 = 10805183) B10805183
theorem B4802303 : Blo 2105435 4802303 := bstep (se 1 (by rfl) ⟨3601727, by rfl⟩ : syracuseStep 4802303 = 7203455) B7203455
theorem B3201535 : Blo 2105435 3201535 := bstep (se 1 (by rfl) ⟨2401151, by rfl⟩ : syracuseStep 3201535 = 4802303) B4802303
theorem B4268713 : Blo 2105435 4268713 := bstep (se 2 (by rfl) ⟨1600767, by rfl⟩ : syracuseStep 4268713 = 3201535) B3201535
theorem B5691617 : Blo 2105435 5691617 := bstep (se 2 (by rfl) ⟨2134356, by rfl⟩ : syracuseStep 5691617 = 4268713) B4268713
theorem B3794411 : Blo 2105435 3794411 := bstep (se 1 (by rfl) ⟨2845808, by rfl⟩ : syracuseStep 3794411 = 5691617) B5691617
theorem B10118429 : Blo 2105435 10118429 := bstep (se 3 (by rfl) ⟨1897205, by rfl⟩ : syracuseStep 10118429 = 3794411) B3794411
theorem B6745619 : Blo 2105435 6745619 := bstep (se 1 (by rfl) ⟨5059214, by rfl⟩ : syracuseStep 6745619 = 10118429) B10118429
theorem B17988317 : Blo 2105435 17988317 := bstep (se 3 (by rfl) ⟨3372809, by rfl⟩ : syracuseStep 17988317 = 6745619) B6745619
theorem B11992211 : Blo 2105435 11992211 := bstep (se 1 (by rfl) ⟨8994158, by rfl⟩ : syracuseStep 11992211 = 17988317) B17988317
theorem B7994807 : Blo 2105435 7994807 := bstep (se 1 (by rfl) ⟨5996105, by rfl⟩ : syracuseStep 7994807 = 11992211) B11992211
theorem B5329871 : Blo 2105435 5329871 := bstep (se 1 (by rfl) ⟨3997403, by rfl⟩ : syracuseStep 5329871 = 7994807) B7994807
theorem B3553247 : Blo 2105435 3553247 := bstep (se 1 (by rfl) ⟨2664935, by rfl⟩ : syracuseStep 3553247 = 5329871) B5329871
theorem B2368831 : Blo 2105435 2368831 := bstep (se 1 (by rfl) ⟨1776623, by rfl⟩ : syracuseStep 2368831 = 3553247) B3553247
theorem B3158441 : Blo 2105435 3158441 := bstep (se 2 (by rfl) ⟨1184415, by rfl⟩ : syracuseStep 3158441 = 2368831) B2368831
theorem B2105627 : Blo 2105435 2105627 := bstep (se 1 (by rfl) ⟨1579220, by rfl⟩ : syracuseStep 2105627 = 3158441) B3158441
theorem B7994821 : Blo 2105435 7994821 := bbase (se 4 (by rfl) ⟨749514, by rfl⟩ : syracuseStep 7994821 = 1499029) (by norm_num)
theorem B10659761 : Blo 2105435 10659761 := bstep (se 2 (by rfl) ⟨3997410, by rfl⟩ : syracuseStep 10659761 = 7994821) B7994821
theorem B7106507 : Blo 2105435 7106507 := bstep (se 1 (by rfl) ⟨5329880, by rfl⟩ : syracuseStep 7106507 = 10659761) B10659761
theorem B4737671 : Blo 2105435 4737671 := bstep (se 1 (by rfl) ⟨3553253, by rfl⟩ : syracuseStep 4737671 = 7106507) B7106507
theorem B3158447 : Blo 2105435 3158447 := bstep (se 1 (by rfl) ⟨2368835, by rfl⟩ : syracuseStep 3158447 = 4737671) B4737671
theorem B2105631 : Blo 2105435 2105631 := bstep (se 1 (by rfl) ⟨1579223, by rfl⟩ : syracuseStep 2105631 = 3158447) B3158447
theorem B3158453 : Blo 2105435 3158453 := bbase (se 5 (by rfl) ⟨148052, by rfl⟩ : syracuseStep 3158453 = 296105) (by norm_num)
theorem B2105635 : Blo 2105435 2105635 := bstep (se 1 (by rfl) ⟨1579226, by rfl⟩ : syracuseStep 2105635 = 3158453) B3158453
theorem B5329901 : Blo 2105435 5329901 := bbase (se 3 (by rfl) ⟨999356, by rfl⟩ : syracuseStep 5329901 = 1998713) (by norm_num)
theorem B3553267 : Blo 2105435 3553267 := bstep (se 1 (by rfl) ⟨2664950, by rfl⟩ : syracuseStep 3553267 = 5329901) B5329901
theorem B4737689 : Blo 2105435 4737689 := bstep (se 2 (by rfl) ⟨1776633, by rfl⟩ : syracuseStep 4737689 = 3553267) B3553267
theorem B3158459 : Blo 2105435 3158459 := bstep (se 1 (by rfl) ⟨2368844, by rfl⟩ : syracuseStep 3158459 = 4737689) B4737689
theorem B2105639 : Blo 2105435 2105639 := bstep (se 1 (by rfl) ⟨1579229, by rfl⟩ : syracuseStep 2105639 = 3158459) B3158459
theorem B2368849 : Blo 2105435 2368849 := bbase (se 2 (by rfl) ⟨888318, by rfl⟩ : syracuseStep 2368849 = 1776637) (by norm_num)
theorem B3158465 : Blo 2105435 3158465 := bstep (se 2 (by rfl) ⟨1184424, by rfl⟩ : syracuseStep 3158465 = 2368849) B2368849
theorem B2105643 : Blo 2105435 2105643 := bstep (se 1 (by rfl) ⟨1579232, by rfl⟩ : syracuseStep 2105643 = 3158465) B3158465
theorem B2248561 : Blo 2105435 2248561 := bbase (se 2 (by rfl) ⟨843210, by rfl⟩ : syracuseStep 2248561 = 1686421) (by norm_num)
theorem B2998081 : Blo 2105435 2998081 := bstep (se 2 (by rfl) ⟨1124280, by rfl⟩ : syracuseStep 2998081 = 2248561) B2248561
theorem B3997441 : Blo 2105435 3997441 := bstep (se 2 (by rfl) ⟨1499040, by rfl⟩ : syracuseStep 3997441 = 2998081) B2998081
theorem B5329921 : Blo 2105435 5329921 := bstep (se 2 (by rfl) ⟨1998720, by rfl⟩ : syracuseStep 5329921 = 3997441) B3997441
theorem B7106561 : Blo 2105435 7106561 := bstep (se 2 (by rfl) ⟨2664960, by rfl⟩ : syracuseStep 7106561 = 5329921) B5329921
theorem B4737707 : Blo 2105435 4737707 := bstep (se 1 (by rfl) ⟨3553280, by rfl⟩ : syracuseStep 4737707 = 7106561) B7106561
theorem B3158471 : Blo 2105435 3158471 := bstep (se 1 (by rfl) ⟨2368853, by rfl⟩ : syracuseStep 3158471 = 4737707) B4737707
theorem B2105647 : Blo 2105435 2105647 := bstep (se 1 (by rfl) ⟨1579235, by rfl⟩ : syracuseStep 2105647 = 3158471) B3158471
theorem B3158477 : Blo 2105435 3158477 := bbase (se 3 (by rfl) ⟨592214, by rfl⟩ : syracuseStep 3158477 = 1184429) (by norm_num)
theorem B2105651 : Blo 2105435 2105651 := bstep (se 1 (by rfl) ⟨1579238, by rfl⟩ : syracuseStep 2105651 = 3158477) B3158477
theorem B4737725 : Blo 2105435 4737725 := bbase (se 3 (by rfl) ⟨888323, by rfl⟩ : syracuseStep 4737725 = 1776647) (by norm_num)
theorem B3158483 : Blo 2105435 3158483 := bstep (se 1 (by rfl) ⟨2368862, by rfl⟩ : syracuseStep 3158483 = 4737725) B4737725
theorem B2105655 : Blo 2105435 2105655 := bstep (se 1 (by rfl) ⟨1579241, by rfl⟩ : syracuseStep 2105655 = 3158483) B3158483
theorem B3553301 : Blo 2105435 3553301 := bbase (se 6 (by rfl) ⟨83280, by rfl⟩ : syracuseStep 3553301 = 166561) (by norm_num)
theorem B2368867 : Blo 2105435 2368867 := bstep (se 1 (by rfl) ⟨1776650, by rfl⟩ : syracuseStep 2368867 = 3553301) B3553301
theorem B3158489 : Blo 2105435 3158489 := bstep (se 2 (by rfl) ⟨1184433, by rfl⟩ : syracuseStep 3158489 = 2368867) B2368867
theorem B2105659 : Blo 2105435 2105659 := bstep (se 1 (by rfl) ⟨1579244, by rfl⟩ : syracuseStep 2105659 = 3158489) B3158489
theorem B3201589 : Blo 2105435 3201589 := bbase (se 5 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 3201589 = 300149) (by norm_num)
theorem B4268785 : Blo 2105435 4268785 := bstep (se 2 (by rfl) ⟨1600794, by rfl⟩ : syracuseStep 4268785 = 3201589) B3201589
theorem B5691713 : Blo 2105435 5691713 := bstep (se 2 (by rfl) ⟨2134392, by rfl⟩ : syracuseStep 5691713 = 4268785) B4268785
theorem B15177901 : Blo 2105435 15177901 := bstep (se 3 (by rfl) ⟨2845856, by rfl⟩ : syracuseStep 15177901 = 5691713) B5691713
theorem B20237201 : Blo 2105435 20237201 := bstep (se 2 (by rfl) ⟨7588950, by rfl⟩ : syracuseStep 20237201 = 15177901) B15177901
theorem B13491467 : Blo 2105435 13491467 := bstep (se 1 (by rfl) ⟨10118600, by rfl⟩ : syracuseStep 13491467 = 20237201) B20237201
theorem B8994311 : Blo 2105435 8994311 := bstep (se 1 (by rfl) ⟨6745733, by rfl⟩ : syracuseStep 8994311 = 13491467) B13491467
theorem B5996207 : Blo 2105435 5996207 := bstep (se 1 (by rfl) ⟨4497155, by rfl⟩ : syracuseStep 5996207 = 8994311) B8994311
theorem B15989885 : Blo 2105435 15989885 := bstep (se 3 (by rfl) ⟨2998103, by rfl⟩ : syracuseStep 15989885 = 5996207) B5996207
theorem B10659923 : Blo 2105435 10659923 := bstep (se 1 (by rfl) ⟨7994942, by rfl⟩ : syracuseStep 10659923 = 15989885) B15989885
theorem B7106615 : Blo 2105435 7106615 := bstep (se 1 (by rfl) ⟨5329961, by rfl⟩ : syracuseStep 7106615 = 10659923) B10659923
theorem B4737743 : Blo 2105435 4737743 := bstep (se 1 (by rfl) ⟨3553307, by rfl⟩ : syracuseStep 4737743 = 7106615) B7106615
theorem B3158495 : Blo 2105435 3158495 := bstep (se 1 (by rfl) ⟨2368871, by rfl⟩ : syracuseStep 3158495 = 4737743) B4737743
theorem B2105663 : Blo 2105435 2105663 := bstep (se 1 (by rfl) ⟨1579247, by rfl⟩ : syracuseStep 2105663 = 3158495) B3158495
theorem B3158501 : Blo 2105435 3158501 := bbase (se 4 (by rfl) ⟨296109, by rfl⟩ : syracuseStep 3158501 = 592219) (by norm_num)
theorem B2105667 : Blo 2105435 2105667 := bstep (se 1 (by rfl) ⟨1579250, by rfl⟩ : syracuseStep 2105667 = 3158501) B3158501
theorem B7588981 : Blo 2105435 7588981 := bbase (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) (by norm_num)
theorem B10118641 : Blo 2105435 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B13491521 : Blo 2105435 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B8994347 : Blo 2105435 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B5996231 : Blo 2105435 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B3997487 : Blo 2105435 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B2664991 : Blo 2105435 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B3553321 : Blo 2105435 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B4737761 : Blo 2105435 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B3158507 : Blo 2105435 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B2105671 : Blo 2105435 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B2368885 : Blo 2105435 2368885 := bbase (se 5 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 2368885 = 222083) (by norm_num)
theorem B3158513 : Blo 2105435 3158513 := bstep (se 2 (by rfl) ⟨1184442, by rfl⟩ : syracuseStep 3158513 = 2368885) B2368885
theorem B2105675 : Blo 2105435 2105675 := bstep (se 1 (by rfl) ⟨1579256, by rfl⟩ : syracuseStep 2105675 = 3158513) B3158513
theorem B2665001 : Blo 2105435 2665001 := bbase (se 2 (by rfl) ⟨999375, by rfl⟩ : syracuseStep 2665001 = 1998751) (by norm_num)
theorem B7106669 : Blo 2105435 7106669 := bstep (se 3 (by rfl) ⟨1332500, by rfl⟩ : syracuseStep 7106669 = 2665001) B2665001
theorem B4737779 : Blo 2105435 4737779 := bstep (se 1 (by rfl) ⟨3553334, by rfl⟩ : syracuseStep 4737779 = 7106669) B7106669
theorem B3158519 : Blo 2105435 3158519 := bstep (se 1 (by rfl) ⟨2368889, by rfl⟩ : syracuseStep 3158519 = 4737779) B4737779
theorem B2105679 : Blo 2105435 2105679 := bstep (se 1 (by rfl) ⟨1579259, by rfl⟩ : syracuseStep 2105679 = 3158519) B3158519
theorem B3158525 : Blo 2105435 3158525 := bbase (se 3 (by rfl) ⟨592223, by rfl⟩ : syracuseStep 3158525 = 1184447) (by norm_num)
theorem B2105683 : Blo 2105435 2105683 := bstep (se 1 (by rfl) ⟨1579262, by rfl⟩ : syracuseStep 2105683 = 3158525) B3158525
theorem B4737797 : Blo 2105435 4737797 := bbase (se 4 (by rfl) ⟨444168, by rfl⟩ : syracuseStep 4737797 = 888337) (by norm_num)
theorem B3158531 : Blo 2105435 3158531 := bstep (se 1 (by rfl) ⟨2368898, by rfl⟩ : syracuseStep 3158531 = 4737797) B4737797
theorem B2105687 : Blo 2105435 2105687 := bstep (se 1 (by rfl) ⟨1579265, by rfl⟩ : syracuseStep 2105687 = 3158531) B3158531
theorem B3997525 : Blo 2105435 3997525 := bbase (se 9 (by rfl) ⟨11711, by rfl⟩ : syracuseStep 3997525 = 23423) (by norm_num)
theorem B5330033 : Blo 2105435 5330033 := bstep (se 2 (by rfl) ⟨1998762, by rfl⟩ : syracuseStep 5330033 = 3997525) B3997525
theorem B3553355 : Blo 2105435 3553355 := bstep (se 1 (by rfl) ⟨2665016, by rfl⟩ : syracuseStep 3553355 = 5330033) B5330033
theorem B2368903 : Blo 2105435 2368903 := bstep (se 1 (by rfl) ⟨1776677, by rfl⟩ : syracuseStep 2368903 = 3553355) B3553355
theorem B3158537 : Blo 2105435 3158537 := bstep (se 2 (by rfl) ⟨1184451, by rfl⟩ : syracuseStep 3158537 = 2368903) B2368903
theorem B2105691 : Blo 2105435 2105691 := bstep (se 1 (by rfl) ⟨1579268, by rfl⟩ : syracuseStep 2105691 = 3158537) B3158537
theorem B10660085 : Blo 2105435 10660085 := bbase (se 5 (by rfl) ⟨499691, by rfl⟩ : syracuseStep 10660085 = 999383) (by norm_num)
theorem B7106723 : Blo 2105435 7106723 := bstep (se 1 (by rfl) ⟨5330042, by rfl⟩ : syracuseStep 7106723 = 10660085) B10660085
theorem B4737815 : Blo 2105435 4737815 := bstep (se 1 (by rfl) ⟨3553361, by rfl⟩ : syracuseStep 4737815 = 7106723) B7106723
theorem B3158543 : Blo 2105435 3158543 := bstep (se 1 (by rfl) ⟨2368907, by rfl⟩ : syracuseStep 3158543 = 4737815) B4737815
theorem B2105695 : Blo 2105435 2105695 := bstep (se 1 (by rfl) ⟨1579271, by rfl⟩ : syracuseStep 2105695 = 3158543) B3158543
theorem B3158549 : Blo 2105435 3158549 := bbase (se 6 (by rfl) ⟨74028, by rfl⟩ : syracuseStep 3158549 = 148057) (by norm_num)
theorem B2105699 : Blo 2105435 2105699 := bstep (se 1 (by rfl) ⟨1579274, by rfl⟩ : syracuseStep 2105699 = 3158549) B3158549
theorem B5059397 : Blo 2105435 5059397 := bbase (se 4 (by rfl) ⟨474318, by rfl⟩ : syracuseStep 5059397 = 948637) (by norm_num)
theorem B3372931 : Blo 2105435 3372931 := bstep (se 1 (by rfl) ⟨2529698, by rfl⟩ : syracuseStep 3372931 = 5059397) B5059397
theorem B17988965 : Blo 2105435 17988965 := bstep (se 4 (by rfl) ⟨1686465, by rfl⟩ : syracuseStep 17988965 = 3372931) B3372931
theorem B11992643 : Blo 2105435 11992643 := bstep (se 1 (by rfl) ⟨8994482, by rfl⟩ : syracuseStep 11992643 = 17988965) B17988965
theorem B7995095 : Blo 2105435 7995095 := bstep (se 1 (by rfl) ⟨5996321, by rfl⟩ : syracuseStep 7995095 = 11992643) B11992643
theorem B5330063 : Blo 2105435 5330063 := bstep (se 1 (by rfl) ⟨3997547, by rfl⟩ : syracuseStep 5330063 = 7995095) B7995095
theorem B3553375 : Blo 2105435 3553375 := bstep (se 1 (by rfl) ⟨2665031, by rfl⟩ : syracuseStep 3553375 = 5330063) B5330063
theorem B4737833 : Blo 2105435 4737833 := bstep (se 2 (by rfl) ⟨1776687, by rfl⟩ : syracuseStep 4737833 = 3553375) B3553375
theorem B3158555 : Blo 2105435 3158555 := bstep (se 1 (by rfl) ⟨2368916, by rfl⟩ : syracuseStep 3158555 = 4737833) B4737833
theorem B2105703 : Blo 2105435 2105703 := bstep (se 1 (by rfl) ⟨1579277, by rfl⟩ : syracuseStep 2105703 = 3158555) B3158555
theorem B2368921 : Blo 2105435 2368921 := bbase (se 2 (by rfl) ⟨888345, by rfl⟩ : syracuseStep 2368921 = 1776691) (by norm_num)
theorem B3158561 : Blo 2105435 3158561 := bstep (se 2 (by rfl) ⟨1184460, by rfl⟩ : syracuseStep 3158561 = 2368921) B2368921
theorem B2105707 : Blo 2105435 2105707 := bstep (se 1 (by rfl) ⟨1579280, by rfl⟩ : syracuseStep 2105707 = 3158561) B3158561
theorem B7995125 : Blo 2105435 7995125 := bbase (se 5 (by rfl) ⟨374771, by rfl⟩ : syracuseStep 7995125 = 749543) (by norm_num)
theorem B5330083 : Blo 2105435 5330083 := bstep (se 1 (by rfl) ⟨3997562, by rfl⟩ : syracuseStep 5330083 = 7995125) B7995125
theorem B7106777 : Blo 2105435 7106777 := bstep (se 2 (by rfl) ⟨2665041, by rfl⟩ : syracuseStep 7106777 = 5330083) B5330083
theorem B4737851 : Blo 2105435 4737851 := bstep (se 1 (by rfl) ⟨3553388, by rfl⟩ : syracuseStep 4737851 = 7106777) B7106777
theorem B3158567 : Blo 2105435 3158567 := bstep (se 1 (by rfl) ⟨2368925, by rfl⟩ : syracuseStep 3158567 = 4737851) B4737851
theorem B2105711 : Blo 2105435 2105711 := bstep (se 1 (by rfl) ⟨1579283, by rfl⟩ : syracuseStep 2105711 = 3158567) B3158567
theorem B3158573 : Blo 2105435 3158573 := bbase (se 3 (by rfl) ⟨592232, by rfl⟩ : syracuseStep 3158573 = 1184465) (by norm_num)
theorem B2105715 : Blo 2105435 2105715 := bstep (se 1 (by rfl) ⟨1579286, by rfl⟩ : syracuseStep 2105715 = 3158573) B3158573
theorem B4737869 : Blo 2105435 4737869 := bbase (se 3 (by rfl) ⟨888350, by rfl⟩ : syracuseStep 4737869 = 1776701) (by norm_num)
theorem B3158579 : Blo 2105435 3158579 := bstep (se 1 (by rfl) ⟨2368934, by rfl⟩ : syracuseStep 3158579 = 4737869) B4737869
theorem B2105719 : Blo 2105435 2105719 := bstep (se 1 (by rfl) ⟨1579289, by rfl⟩ : syracuseStep 2105719 = 3158579) B3158579
theorem B2665057 : Blo 2105435 2665057 := bbase (se 2 (by rfl) ⟨999396, by rfl⟩ : syracuseStep 2665057 = 1998793) (by norm_num)
theorem B3553409 : Blo 2105435 3553409 := bstep (se 2 (by rfl) ⟨1332528, by rfl⟩ : syracuseStep 3553409 = 2665057) B2665057
theorem B2368939 : Blo 2105435 2368939 := bstep (se 1 (by rfl) ⟨1776704, by rfl⟩ : syracuseStep 2368939 = 3553409) B3553409
theorem B3158585 : Blo 2105435 3158585 := bstep (se 2 (by rfl) ⟨1184469, by rfl⟩ : syracuseStep 3158585 = 2368939) B2368939
theorem B2105723 : Blo 2105435 2105723 := bstep (se 1 (by rfl) ⟨1579292, by rfl⟩ : syracuseStep 2105723 = 3158585) B3158585
theorem B23985557 : Blo 2105435 23985557 := bbase (se 6 (by rfl) ⟨562161, by rfl⟩ : syracuseStep 23985557 = 1124323) (by norm_num)
theorem B15990371 : Blo 2105435 15990371 := bstep (se 1 (by rfl) ⟨11992778, by rfl⟩ : syracuseStep 15990371 = 23985557) B23985557
theorem B10660247 : Blo 2105435 10660247 := bstep (se 1 (by rfl) ⟨7995185, by rfl⟩ : syracuseStep 10660247 = 15990371) B15990371
theorem B7106831 : Blo 2105435 7106831 := bstep (se 1 (by rfl) ⟨5330123, by rfl⟩ : syracuseStep 7106831 = 10660247) B10660247
theorem B4737887 : Blo 2105435 4737887 := bstep (se 1 (by rfl) ⟨3553415, by rfl⟩ : syracuseStep 4737887 = 7106831) B7106831
theorem B3158591 : Blo 2105435 3158591 := bstep (se 1 (by rfl) ⟨2368943, by rfl⟩ : syracuseStep 3158591 = 4737887) B4737887
theorem B2105727 : Blo 2105435 2105727 := bstep (se 1 (by rfl) ⟨1579295, by rfl⟩ : syracuseStep 2105727 = 3158591) B3158591
theorem B3158597 : Blo 2105435 3158597 := bbase (se 4 (by rfl) ⟨296118, by rfl⟩ : syracuseStep 3158597 = 592237) (by norm_num)
theorem B2105731 : Blo 2105435 2105731 := bstep (se 1 (by rfl) ⟨1579298, by rfl⟩ : syracuseStep 2105731 = 3158597) B3158597
theorem B3553429 : Blo 2105435 3553429 := bbase (se 6 (by rfl) ⟨83283, by rfl⟩ : syracuseStep 3553429 = 166567) (by norm_num)
theorem B4737905 : Blo 2105435 4737905 := bstep (se 2 (by rfl) ⟨1776714, by rfl⟩ : syracuseStep 4737905 = 3553429) B3553429
theorem B3158603 : Blo 2105435 3158603 := bstep (se 1 (by rfl) ⟨2368952, by rfl⟩ : syracuseStep 3158603 = 4737905) B4737905
theorem B2105735 : Blo 2105435 2105735 := bstep (se 1 (by rfl) ⟨1579301, by rfl⟩ : syracuseStep 2105735 = 3158603) B3158603
theorem B2368957 : Blo 2105435 2368957 := bbase (se 3 (by rfl) ⟨444179, by rfl⟩ : syracuseStep 2368957 = 888359) (by norm_num)
theorem B3158609 : Blo 2105435 3158609 := bstep (se 2 (by rfl) ⟨1184478, by rfl⟩ : syracuseStep 3158609 = 2368957) B2368957
theorem B2105739 : Blo 2105435 2105739 := bstep (se 1 (by rfl) ⟨1579304, by rfl⟩ : syracuseStep 2105739 = 3158609) B3158609
theorem B7106885 : Blo 2105435 7106885 := bbase (se 4 (by rfl) ⟨666270, by rfl⟩ : syracuseStep 7106885 = 1332541) (by norm_num)
theorem B4737923 : Blo 2105435 4737923 := bstep (se 1 (by rfl) ⟨3553442, by rfl⟩ : syracuseStep 4737923 = 7106885) B7106885
theorem B3158615 : Blo 2105435 3158615 := bstep (se 1 (by rfl) ⟨2368961, by rfl⟩ : syracuseStep 3158615 = 4737923) B4737923
theorem B2105743 : Blo 2105435 2105743 := bstep (se 1 (by rfl) ⟨1579307, by rfl⟩ : syracuseStep 2105743 = 3158615) B3158615
theorem B3158621 : Blo 2105435 3158621 := bbase (se 3 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 3158621 = 1184483) (by norm_num)
theorem B2105747 : Blo 2105435 2105747 := bstep (se 1 (by rfl) ⟨1579310, by rfl⟩ : syracuseStep 2105747 = 3158621) B3158621
theorem B4737941 : Blo 2105435 4737941 := bbase (se 6 (by rfl) ⟨111045, by rfl⟩ : syracuseStep 4737941 = 222091) (by norm_num)
theorem B3158627 : Blo 2105435 3158627 := bstep (se 1 (by rfl) ⟨2368970, by rfl⟩ : syracuseStep 3158627 = 4737941) B4737941
theorem B2105751 : Blo 2105435 2105751 := bstep (se 1 (by rfl) ⟨1579313, by rfl⟩ : syracuseStep 2105751 = 3158627) B3158627
theorem B7589285 : Blo 2105435 7589285 := bbase (se 4 (by rfl) ⟨711495, by rfl⟩ : syracuseStep 7589285 = 1422991) (by norm_num)
theorem B5059523 : Blo 2105435 5059523 := bstep (se 1 (by rfl) ⟨3794642, by rfl⟩ : syracuseStep 5059523 = 7589285) B7589285
theorem B3373015 : Blo 2105435 3373015 := bstep (se 1 (by rfl) ⟨2529761, by rfl⟩ : syracuseStep 3373015 = 5059523) B5059523
theorem B4497353 : Blo 2105435 4497353 := bstep (se 2 (by rfl) ⟨1686507, by rfl⟩ : syracuseStep 4497353 = 3373015) B3373015
theorem B2998235 : Blo 2105435 2998235 := bstep (se 1 (by rfl) ⟨2248676, by rfl⟩ : syracuseStep 2998235 = 4497353) B4497353
theorem B7995293 : Blo 2105435 7995293 := bstep (se 3 (by rfl) ⟨1499117, by rfl⟩ : syracuseStep 7995293 = 2998235) B2998235
theorem B5330195 : Blo 2105435 5330195 := bstep (se 1 (by rfl) ⟨3997646, by rfl⟩ : syracuseStep 5330195 = 7995293) B7995293
theorem B3553463 : Blo 2105435 3553463 := bstep (se 1 (by rfl) ⟨2665097, by rfl⟩ : syracuseStep 3553463 = 5330195) B5330195
theorem B2368975 : Blo 2105435 2368975 := bstep (se 1 (by rfl) ⟨1776731, by rfl⟩ : syracuseStep 2368975 = 3553463) B3553463
theorem B3158633 : Blo 2105435 3158633 := bstep (se 2 (by rfl) ⟨1184487, by rfl⟩ : syracuseStep 3158633 = 2368975) B2368975
theorem B2105755 : Blo 2105435 2105755 := bstep (se 1 (by rfl) ⟨1579316, by rfl⟩ : syracuseStep 2105755 = 3158633) B3158633
theorem B5691973 : Blo 2105435 5691973 := bbase (se 4 (by rfl) ⟨533622, by rfl⟩ : syracuseStep 5691973 = 1067245) (by norm_num)
theorem B7589297 : Blo 2105435 7589297 := bstep (se 2 (by rfl) ⟨2845986, by rfl⟩ : syracuseStep 7589297 = 5691973) B5691973
theorem B5059531 : Blo 2105435 5059531 := bstep (se 1 (by rfl) ⟨3794648, by rfl⟩ : syracuseStep 5059531 = 7589297) B7589297
theorem B6746041 : Blo 2105435 6746041 := bstep (se 2 (by rfl) ⟨2529765, by rfl⟩ : syracuseStep 6746041 = 5059531) B5059531
theorem B8994721 : Blo 2105435 8994721 := bstep (se 2 (by rfl) ⟨3373020, by rfl⟩ : syracuseStep 8994721 = 6746041) B6746041
theorem B11992961 : Blo 2105435 11992961 := bstep (se 2 (by rfl) ⟨4497360, by rfl⟩ : syracuseStep 11992961 = 8994721) B8994721
theorem B7995307 : Blo 2105435 7995307 := bstep (se 1 (by rfl) ⟨5996480, by rfl⟩ : syracuseStep 7995307 = 11992961) B11992961
theorem B10660409 : Blo 2105435 10660409 := bstep (se 2 (by rfl) ⟨3997653, by rfl⟩ : syracuseStep 10660409 = 7995307) B7995307
theorem B7106939 : Blo 2105435 7106939 := bstep (se 1 (by rfl) ⟨5330204, by rfl⟩ : syracuseStep 7106939 = 10660409) B10660409
theorem B4737959 : Blo 2105435 4737959 := bstep (se 1 (by rfl) ⟨3553469, by rfl⟩ : syracuseStep 4737959 = 7106939) B7106939
theorem B3158639 : Blo 2105435 3158639 := bstep (se 1 (by rfl) ⟨2368979, by rfl⟩ : syracuseStep 3158639 = 4737959) B4737959
theorem B2105759 : Blo 2105435 2105759 := bstep (se 1 (by rfl) ⟨1579319, by rfl⟩ : syracuseStep 2105759 = 3158639) B3158639
theorem B3158645 : Blo 2105435 3158645 := bbase (se 5 (by rfl) ⟨148061, by rfl⟩ : syracuseStep 3158645 = 296123) (by norm_num)
theorem B2105763 : Blo 2105435 2105763 := bstep (se 1 (by rfl) ⟨1579322, by rfl⟩ : syracuseStep 2105763 = 3158645) B3158645
theorem B3997669 : Blo 2105435 3997669 := bbase (se 4 (by rfl) ⟨374781, by rfl⟩ : syracuseStep 3997669 = 749563) (by norm_num)
theorem B5330225 : Blo 2105435 5330225 := bstep (se 2 (by rfl) ⟨1998834, by rfl⟩ : syracuseStep 5330225 = 3997669) B3997669
theorem B3553483 : Blo 2105435 3553483 := bstep (se 1 (by rfl) ⟨2665112, by rfl⟩ : syracuseStep 3553483 = 5330225) B5330225
theorem B4737977 : Blo 2105435 4737977 := bstep (se 2 (by rfl) ⟨1776741, by rfl⟩ : syracuseStep 4737977 = 3553483) B3553483
theorem B3158651 : Blo 2105435 3158651 := bstep (se 1 (by rfl) ⟨2368988, by rfl⟩ : syracuseStep 3158651 = 4737977) B4737977
theorem B2105767 : Blo 2105435 2105767 := bstep (se 1 (by rfl) ⟨1579325, by rfl⟩ : syracuseStep 2105767 = 3158651) B3158651
theorem B2368993 : Blo 2105435 2368993 := bbase (se 2 (by rfl) ⟨888372, by rfl⟩ : syracuseStep 2368993 = 1776745) (by norm_num)
theorem B3158657 : Blo 2105435 3158657 := bstep (se 2 (by rfl) ⟨1184496, by rfl⟩ : syracuseStep 3158657 = 2368993) B2368993
theorem B2105771 : Blo 2105435 2105771 := bstep (se 1 (by rfl) ⟨1579328, by rfl⟩ : syracuseStep 2105771 = 3158657) B3158657
theorem B5330245 : Blo 2105435 5330245 := bbase (se 4 (by rfl) ⟨499710, by rfl⟩ : syracuseStep 5330245 = 999421) (by norm_num)
theorem B7106993 : Blo 2105435 7106993 := bstep (se 2 (by rfl) ⟨2665122, by rfl⟩ : syracuseStep 7106993 = 5330245) B5330245
theorem B4737995 : Blo 2105435 4737995 := bstep (se 1 (by rfl) ⟨3553496, by rfl⟩ : syracuseStep 4737995 = 7106993) B7106993
theorem B3158663 : Blo 2105435 3158663 := bstep (se 1 (by rfl) ⟨2368997, by rfl⟩ : syracuseStep 3158663 = 4737995) B4737995
theorem B2105775 : Blo 2105435 2105775 := bstep (se 1 (by rfl) ⟨1579331, by rfl⟩ : syracuseStep 2105775 = 3158663) B3158663
theorem B3158669 : Blo 2105435 3158669 := bbase (se 3 (by rfl) ⟨592250, by rfl⟩ : syracuseStep 3158669 = 1184501) (by norm_num)
theorem B2105779 : Blo 2105435 2105779 := bstep (se 1 (by rfl) ⟨1579334, by rfl⟩ : syracuseStep 2105779 = 3158669) B3158669
theorem B4738013 : Blo 2105435 4738013 := bbase (se 3 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 4738013 = 1776755) (by norm_num)
theorem B3158675 : Blo 2105435 3158675 := bstep (se 1 (by rfl) ⟨2369006, by rfl⟩ : syracuseStep 3158675 = 4738013) B4738013
theorem B2105783 : Blo 2105435 2105783 := bstep (se 1 (by rfl) ⟨1579337, by rfl⟩ : syracuseStep 2105783 = 3158675) B3158675
theorem B3553517 : Blo 2105435 3553517 := bbase (se 3 (by rfl) ⟨666284, by rfl⟩ : syracuseStep 3553517 = 1332569) (by norm_num)
theorem B2369011 : Blo 2105435 2369011 := bstep (se 1 (by rfl) ⟨1776758, by rfl⟩ : syracuseStep 2369011 = 3553517) B3553517
theorem B3158681 : Blo 2105435 3158681 := bstep (se 2 (by rfl) ⟨1184505, by rfl⟩ : syracuseStep 3158681 = 2369011) B2369011
theorem B2105787 : Blo 2105435 2105787 := bstep (se 1 (by rfl) ⟨1579340, by rfl⟩ : syracuseStep 2105787 = 3158681) B3158681
theorem B3419093 : Blo 2105435 3419093 := bbase (se 7 (by rfl) ⟨40067, by rfl⟩ : syracuseStep 3419093 = 80135) (by norm_num)
theorem B2279395 : Blo 2105435 2279395 := bstep (se 1 (by rfl) ⟨1709546, by rfl⟩ : syracuseStep 2279395 = 3419093) B3419093
theorem B3039193 : Blo 2105435 3039193 := bstep (se 2 (by rfl) ⟨1139697, by rfl⟩ : syracuseStep 3039193 = 2279395) B2279395
theorem B4052257 : Blo 2105435 4052257 := bstep (se 2 (by rfl) ⟨1519596, by rfl⟩ : syracuseStep 4052257 = 3039193) B3039193
theorem B21612037 : Blo 2105435 21612037 := bstep (se 4 (by rfl) ⟨2026128, by rfl⟩ : syracuseStep 21612037 = 4052257) B4052257
theorem B28816049 : Blo 2105435 28816049 := bstep (se 2 (by rfl) ⟨10806018, by rfl⟩ : syracuseStep 28816049 = 21612037) B21612037
theorem B19210699 : Blo 2105435 19210699 := bstep (se 1 (by rfl) ⟨14408024, by rfl⟩ : syracuseStep 19210699 = 28816049) B28816049
theorem B25614265 : Blo 2105435 25614265 := bstep (se 2 (by rfl) ⟨9605349, by rfl⟩ : syracuseStep 25614265 = 19210699) B19210699
theorem B34152353 : Blo 2105435 34152353 := bstep (se 2 (by rfl) ⟨12807132, by rfl⟩ : syracuseStep 34152353 = 25614265) B25614265
theorem B22768235 : Blo 2105435 22768235 := bstep (se 1 (by rfl) ⟨17076176, by rfl⟩ : syracuseStep 22768235 = 34152353) B34152353
theorem B15178823 : Blo 2105435 15178823 := bstep (se 1 (by rfl) ⟨11384117, by rfl⟩ : syracuseStep 15178823 = 22768235) B22768235
theorem B10119215 : Blo 2105435 10119215 := bstep (se 1 (by rfl) ⟨7589411, by rfl⟩ : syracuseStep 10119215 = 15178823) B15178823
theorem B26984573 : Blo 2105435 26984573 := bstep (se 3 (by rfl) ⟨5059607, by rfl⟩ : syracuseStep 26984573 = 10119215) B10119215
theorem B17989715 : Blo 2105435 17989715 := bstep (se 1 (by rfl) ⟨13492286, by rfl⟩ : syracuseStep 17989715 = 26984573) B26984573
theorem B11993143 : Blo 2105435 11993143 := bstep (se 1 (by rfl) ⟨8994857, by rfl⟩ : syracuseStep 11993143 = 17989715) B17989715
theorem B15990857 : Blo 2105435 15990857 := bstep (se 2 (by rfl) ⟨5996571, by rfl⟩ : syracuseStep 15990857 = 11993143) B11993143
theorem B10660571 : Blo 2105435 10660571 := bstep (se 1 (by rfl) ⟨7995428, by rfl⟩ : syracuseStep 10660571 = 15990857) B15990857
theorem B7107047 : Blo 2105435 7107047 := bstep (se 1 (by rfl) ⟨5330285, by rfl⟩ : syracuseStep 7107047 = 10660571) B10660571
theorem B4738031 : Blo 2105435 4738031 := bstep (se 1 (by rfl) ⟨3553523, by rfl⟩ : syracuseStep 4738031 = 7107047) B7107047
theorem B3158687 : Blo 2105435 3158687 := bstep (se 1 (by rfl) ⟨2369015, by rfl⟩ : syracuseStep 3158687 = 4738031) B4738031
theorem B2105791 : Blo 2105435 2105791 := bstep (se 1 (by rfl) ⟨1579343, by rfl⟩ : syracuseStep 2105791 = 3158687) B3158687
theorem B3158693 : Blo 2105435 3158693 := bbase (se 4 (by rfl) ⟨296127, by rfl⟩ : syracuseStep 3158693 = 592255) (by norm_num)
theorem B2105795 : Blo 2105435 2105795 := bstep (se 1 (by rfl) ⟨1579346, by rfl⟩ : syracuseStep 2105795 = 3158693) B3158693
theorem B2665153 : Blo 2105435 2665153 := bbase (se 2 (by rfl) ⟨999432, by rfl⟩ : syracuseStep 2665153 = 1998865) (by norm_num)
theorem B3553537 : Blo 2105435 3553537 := bstep (se 2 (by rfl) ⟨1332576, by rfl⟩ : syracuseStep 3553537 = 2665153) B2665153
theorem B4738049 : Blo 2105435 4738049 := bstep (se 2 (by rfl) ⟨1776768, by rfl⟩ : syracuseStep 4738049 = 3553537) B3553537
theorem B3158699 : Blo 2105435 3158699 := bstep (se 1 (by rfl) ⟨2369024, by rfl⟩ : syracuseStep 3158699 = 4738049) B4738049
theorem B2105799 : Blo 2105435 2105799 := bstep (se 1 (by rfl) ⟨1579349, by rfl⟩ : syracuseStep 2105799 = 3158699) B3158699
theorem B2369029 : Blo 2105435 2369029 := bbase (se 4 (by rfl) ⟨222096, by rfl⟩ : syracuseStep 2369029 = 444193) (by norm_num)
theorem B3158705 : Blo 2105435 3158705 := bstep (se 2 (by rfl) ⟨1184514, by rfl⟩ : syracuseStep 3158705 = 2369029) B2369029
theorem B2105803 : Blo 2105435 2105803 := bstep (se 1 (by rfl) ⟨1579352, by rfl⟩ : syracuseStep 2105803 = 3158705) B3158705
theorem B2998309 : Blo 2105435 2998309 := bbase (se 4 (by rfl) ⟨281091, by rfl⟩ : syracuseStep 2998309 = 562183) (by norm_num)
theorem B3997745 : Blo 2105435 3997745 := bstep (se 2 (by rfl) ⟨1499154, by rfl⟩ : syracuseStep 3997745 = 2998309) B2998309
theorem B2665163 : Blo 2105435 2665163 := bstep (se 1 (by rfl) ⟨1998872, by rfl⟩ : syracuseStep 2665163 = 3997745) B3997745
theorem B7107101 : Blo 2105435 7107101 := bstep (se 3 (by rfl) ⟨1332581, by rfl⟩ : syracuseStep 7107101 = 2665163) B2665163
theorem B4738067 : Blo 2105435 4738067 := bstep (se 1 (by rfl) ⟨3553550, by rfl⟩ : syracuseStep 4738067 = 7107101) B7107101
theorem B3158711 : Blo 2105435 3158711 := bstep (se 1 (by rfl) ⟨2369033, by rfl⟩ : syracuseStep 3158711 = 4738067) B4738067
theorem B2105807 : Blo 2105435 2105807 := bstep (se 1 (by rfl) ⟨1579355, by rfl⟩ : syracuseStep 2105807 = 3158711) B3158711
theorem B3158717 : Blo 2105435 3158717 := bbase (se 3 (by rfl) ⟨592259, by rfl⟩ : syracuseStep 3158717 = 1184519) (by norm_num)
theorem B2105811 : Blo 2105435 2105811 := bstep (se 1 (by rfl) ⟨1579358, by rfl⟩ : syracuseStep 2105811 = 3158717) B3158717
theorem B4738085 : Blo 2105435 4738085 := bbase (se 4 (by rfl) ⟨444195, by rfl⟩ : syracuseStep 4738085 = 888391) (by norm_num)
theorem B3158723 : Blo 2105435 3158723 := bstep (se 1 (by rfl) ⟨2369042, by rfl⟩ : syracuseStep 3158723 = 4738085) B4738085
theorem B2105815 : Blo 2105435 2105815 := bstep (se 1 (by rfl) ⟨1579361, by rfl⟩ : syracuseStep 2105815 = 3158723) B3158723
theorem B5330357 : Blo 2105435 5330357 := bbase (se 5 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 5330357 = 499721) (by norm_num)
theorem B3553571 : Blo 2105435 3553571 := bstep (se 1 (by rfl) ⟨2665178, by rfl⟩ : syracuseStep 3553571 = 5330357) B5330357
theorem B2369047 : Blo 2105435 2369047 := bstep (se 1 (by rfl) ⟨1776785, by rfl⟩ : syracuseStep 2369047 = 3553571) B3553571
theorem B3158729 : Blo 2105435 3158729 := bstep (se 2 (by rfl) ⟨1184523, by rfl⟩ : syracuseStep 3158729 = 2369047) B2369047
theorem B2105819 : Blo 2105435 2105819 := bstep (se 1 (by rfl) ⟨1579364, by rfl⟩ : syracuseStep 2105819 = 3158729) B3158729
theorem B5059685 : Blo 2105435 5059685 := bbase (se 4 (by rfl) ⟨474345, by rfl⟩ : syracuseStep 5059685 = 948691) (by norm_num)
theorem B13492493 : Blo 2105435 13492493 := bstep (se 3 (by rfl) ⟨2529842, by rfl⟩ : syracuseStep 13492493 = 5059685) B5059685
theorem B8994995 : Blo 2105435 8994995 := bstep (se 1 (by rfl) ⟨6746246, by rfl⟩ : syracuseStep 8994995 = 13492493) B13492493
theorem B5996663 : Blo 2105435 5996663 := bstep (se 1 (by rfl) ⟨4497497, by rfl⟩ : syracuseStep 5996663 = 8994995) B8994995
theorem B3997775 : Blo 2105435 3997775 := bstep (se 1 (by rfl) ⟨2998331, by rfl⟩ : syracuseStep 3997775 = 5996663) B5996663
theorem B10660733 : Blo 2105435 10660733 := bstep (se 3 (by rfl) ⟨1998887, by rfl⟩ : syracuseStep 10660733 = 3997775) B3997775
theorem B7107155 : Blo 2105435 7107155 := bstep (se 1 (by rfl) ⟨5330366, by rfl⟩ : syracuseStep 7107155 = 10660733) B10660733
theorem B4738103 : Blo 2105435 4738103 := bstep (se 1 (by rfl) ⟨3553577, by rfl⟩ : syracuseStep 4738103 = 7107155) B7107155
theorem B3158735 : Blo 2105435 3158735 := bstep (se 1 (by rfl) ⟨2369051, by rfl⟩ : syracuseStep 3158735 = 4738103) B4738103
theorem B2105823 : Blo 2105435 2105823 := bstep (se 1 (by rfl) ⟨1579367, by rfl⟩ : syracuseStep 2105823 = 3158735) B3158735
theorem B3158741 : Blo 2105435 3158741 := bbase (se 7 (by rfl) ⟨37016, by rfl⟩ : syracuseStep 3158741 = 74033) (by norm_num)
theorem B2105827 : Blo 2105435 2105827 := bstep (se 1 (by rfl) ⟨1579370, by rfl⟩ : syracuseStep 2105827 = 3158741) B3158741
theorem B10397429 : Blo 2105435 10397429 := bbase (se 5 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 10397429 = 974759) (by norm_num)
theorem B6931619 : Blo 2105435 6931619 := bstep (se 1 (by rfl) ⟨5198714, by rfl⟩ : syracuseStep 6931619 = 10397429) B10397429
theorem B4621079 : Blo 2105435 4621079 := bstep (se 1 (by rfl) ⟨3465809, by rfl⟩ : syracuseStep 4621079 = 6931619) B6931619
theorem B3080719 : Blo 2105435 3080719 := bstep (se 1 (by rfl) ⟨2310539, by rfl⟩ : syracuseStep 3080719 = 4621079) B4621079
theorem B16430501 : Blo 2105435 16430501 := bstep (se 4 (by rfl) ⟨1540359, by rfl⟩ : syracuseStep 16430501 = 3080719) B3080719
theorem B10953667 : Blo 2105435 10953667 := bstep (se 1 (by rfl) ⟨8215250, by rfl⟩ : syracuseStep 10953667 = 16430501) B16430501
theorem B14604889 : Blo 2105435 14604889 := bstep (se 2 (by rfl) ⟨5476833, by rfl⟩ : syracuseStep 14604889 = 10953667) B10953667
theorem B19473185 : Blo 2105435 19473185 := bstep (se 2 (by rfl) ⟨7302444, by rfl⟩ : syracuseStep 19473185 = 14604889) B14604889
theorem B12982123 : Blo 2105435 12982123 := bstep (se 1 (by rfl) ⟨9736592, by rfl⟩ : syracuseStep 12982123 = 19473185) B19473185
theorem B17309497 : Blo 2105435 17309497 := bstep (se 2 (by rfl) ⟨6491061, by rfl⟩ : syracuseStep 17309497 = 12982123) B12982123
theorem B23079329 : Blo 2105435 23079329 := bstep (se 2 (by rfl) ⟨8654748, by rfl⟩ : syracuseStep 23079329 = 17309497) B17309497
theorem B15386219 : Blo 2105435 15386219 := bstep (se 1 (by rfl) ⟨11539664, by rfl⟩ : syracuseStep 15386219 = 23079329) B23079329
theorem B10257479 : Blo 2105435 10257479 := bstep (se 1 (by rfl) ⟨7693109, by rfl⟩ : syracuseStep 10257479 = 15386219) B15386219
theorem B6838319 : Blo 2105435 6838319 := bstep (se 1 (by rfl) ⟨5128739, by rfl⟩ : syracuseStep 6838319 = 10257479) B10257479
theorem B4558879 : Blo 2105435 4558879 := bstep (se 1 (by rfl) ⟨3419159, by rfl⟩ : syracuseStep 4558879 = 6838319) B6838319
theorem B6078505 : Blo 2105435 6078505 := bstep (se 2 (by rfl) ⟨2279439, by rfl⟩ : syracuseStep 6078505 = 4558879) B4558879
theorem B8104673 : Blo 2105435 8104673 := bstep (se 2 (by rfl) ⟨3039252, by rfl⟩ : syracuseStep 8104673 = 6078505) B6078505
theorem B5403115 : Blo 2105435 5403115 := bstep (se 1 (by rfl) ⟨4052336, by rfl⟩ : syracuseStep 5403115 = 8104673) B8104673
theorem B7204153 : Blo 2105435 7204153 := bstep (se 2 (by rfl) ⟨2701557, by rfl⟩ : syracuseStep 7204153 = 5403115) B5403115
theorem B9605537 : Blo 2105435 9605537 := bstep (se 2 (by rfl) ⟨3602076, by rfl⟩ : syracuseStep 9605537 = 7204153) B7204153
theorem B6403691 : Blo 2105435 6403691 := bstep (se 1 (by rfl) ⟨4802768, by rfl⟩ : syracuseStep 6403691 = 9605537) B9605537
theorem B4269127 : Blo 2105435 4269127 := bstep (se 1 (by rfl) ⟨3201845, by rfl⟩ : syracuseStep 4269127 = 6403691) B6403691
theorem B5692169 : Blo 2105435 5692169 := bstep (se 2 (by rfl) ⟨2134563, by rfl⟩ : syracuseStep 5692169 = 4269127) B4269127
theorem B3794779 : Blo 2105435 3794779 := bstep (se 1 (by rfl) ⟨2846084, by rfl⟩ : syracuseStep 3794779 = 5692169) B5692169
theorem B5059705 : Blo 2105435 5059705 := bstep (se 2 (by rfl) ⟨1897389, by rfl⟩ : syracuseStep 5059705 = 3794779) B3794779
theorem B6746273 : Blo 2105435 6746273 := bstep (se 2 (by rfl) ⟨2529852, by rfl⟩ : syracuseStep 6746273 = 5059705) B5059705
theorem B4497515 : Blo 2105435 4497515 := bstep (se 1 (by rfl) ⟨3373136, by rfl⟩ : syracuseStep 4497515 = 6746273) B6746273
theorem B2998343 : Blo 2105435 2998343 := bstep (se 1 (by rfl) ⟨2248757, by rfl⟩ : syracuseStep 2998343 = 4497515) B4497515
theorem B7995581 : Blo 2105435 7995581 := bstep (se 3 (by rfl) ⟨1499171, by rfl⟩ : syracuseStep 7995581 = 2998343) B2998343
theorem B5330387 : Blo 2105435 5330387 := bstep (se 1 (by rfl) ⟨3997790, by rfl⟩ : syracuseStep 5330387 = 7995581) B7995581
theorem B3553591 : Blo 2105435 3553591 := bstep (se 1 (by rfl) ⟨2665193, by rfl⟩ : syracuseStep 3553591 = 5330387) B5330387
theorem B4738121 : Blo 2105435 4738121 := bstep (se 2 (by rfl) ⟨1776795, by rfl⟩ : syracuseStep 4738121 = 3553591) B3553591
theorem B3158747 : Blo 2105435 3158747 := bstep (se 1 (by rfl) ⟨2369060, by rfl⟩ : syracuseStep 3158747 = 4738121) B4738121
theorem B2105831 : Blo 2105435 2105831 := bstep (se 1 (by rfl) ⟨1579373, by rfl⟩ : syracuseStep 2105831 = 3158747) B3158747
theorem B2369065 : Blo 2105435 2369065 := bbase (se 2 (by rfl) ⟨888399, by rfl⟩ : syracuseStep 2369065 = 1776799) (by norm_num)
theorem B3158753 : Blo 2105435 3158753 := bstep (se 2 (by rfl) ⟨1184532, by rfl⟩ : syracuseStep 3158753 = 2369065) B2369065
theorem B2105835 : Blo 2105435 2105835 := bstep (se 1 (by rfl) ⟨1579376, by rfl⟩ : syracuseStep 2105835 = 3158753) B3158753
theorem B2401393 : Blo 2105435 2401393 := bbase (se 2 (by rfl) ⟨900522, by rfl⟩ : syracuseStep 2401393 = 1801045) (by norm_num)
theorem B3201857 : Blo 2105435 3201857 := bstep (se 2 (by rfl) ⟨1200696, by rfl⟩ : syracuseStep 3201857 = 2401393) B2401393
theorem B2134571 : Blo 2105435 2134571 := bstep (se 1 (by rfl) ⟨1600928, by rfl⟩ : syracuseStep 2134571 = 3201857) B3201857
theorem B5692189 : Blo 2105435 5692189 := bstep (se 3 (by rfl) ⟨1067285, by rfl⟩ : syracuseStep 5692189 = 2134571) B2134571
theorem B7589585 : Blo 2105435 7589585 := bstep (se 2 (by rfl) ⟨2846094, by rfl⟩ : syracuseStep 7589585 = 5692189) B5692189
theorem B20238893 : Blo 2105435 20238893 := bstep (se 3 (by rfl) ⟨3794792, by rfl⟩ : syracuseStep 20238893 = 7589585) B7589585
theorem B13492595 : Blo 2105435 13492595 := bstep (se 1 (by rfl) ⟨10119446, by rfl⟩ : syracuseStep 13492595 = 20238893) B20238893
theorem B8995063 : Blo 2105435 8995063 := bstep (se 1 (by rfl) ⟨6746297, by rfl⟩ : syracuseStep 8995063 = 13492595) B13492595
theorem B11993417 : Blo 2105435 11993417 := bstep (se 2 (by rfl) ⟨4497531, by rfl⟩ : syracuseStep 11993417 = 8995063) B8995063
theorem B7995611 : Blo 2105435 7995611 := bstep (se 1 (by rfl) ⟨5996708, by rfl⟩ : syracuseStep 7995611 = 11993417) B11993417
theorem B5330407 : Blo 2105435 5330407 := bstep (se 1 (by rfl) ⟨3997805, by rfl⟩ : syracuseStep 5330407 = 7995611) B7995611
theorem B7107209 : Blo 2105435 7107209 := bstep (se 2 (by rfl) ⟨2665203, by rfl⟩ : syracuseStep 7107209 = 5330407) B5330407
theorem B4738139 : Blo 2105435 4738139 := bstep (se 1 (by rfl) ⟨3553604, by rfl⟩ : syracuseStep 4738139 = 7107209) B7107209
theorem B3158759 : Blo 2105435 3158759 := bstep (se 1 (by rfl) ⟨2369069, by rfl⟩ : syracuseStep 3158759 = 4738139) B4738139
theorem B2105839 : Blo 2105435 2105839 := bstep (se 1 (by rfl) ⟨1579379, by rfl⟩ : syracuseStep 2105839 = 3158759) B3158759
theorem B3158765 : Blo 2105435 3158765 := bbase (se 3 (by rfl) ⟨592268, by rfl⟩ : syracuseStep 3158765 = 1184537) (by norm_num)
theorem B2105843 : Blo 2105435 2105843 := bstep (se 1 (by rfl) ⟨1579382, by rfl⟩ : syracuseStep 2105843 = 3158765) B3158765
theorem B4738157 : Blo 2105435 4738157 := bbase (se 3 (by rfl) ⟨888404, by rfl⟩ : syracuseStep 4738157 = 1776809) (by norm_num)
theorem B3158771 : Blo 2105435 3158771 := bstep (se 1 (by rfl) ⟨2369078, by rfl⟩ : syracuseStep 3158771 = 4738157) B4738157
theorem B2105847 : Blo 2105435 2105847 := bstep (se 1 (by rfl) ⟨1579385, by rfl⟩ : syracuseStep 2105847 = 3158771) B3158771
theorem B3997829 : Blo 2105435 3997829 := bbase (se 4 (by rfl) ⟨374796, by rfl⟩ : syracuseStep 3997829 = 749593) (by norm_num)
theorem B2665219 : Blo 2105435 2665219 := bstep (se 1 (by rfl) ⟨1998914, by rfl⟩ : syracuseStep 2665219 = 3997829) B3997829
theorem B3553625 : Blo 2105435 3553625 := bstep (se 2 (by rfl) ⟨1332609, by rfl⟩ : syracuseStep 3553625 = 2665219) B2665219
theorem B2369083 : Blo 2105435 2369083 := bstep (se 1 (by rfl) ⟨1776812, by rfl⟩ : syracuseStep 2369083 = 3553625) B3553625
theorem B3158777 : Blo 2105435 3158777 := bstep (se 2 (by rfl) ⟨1184541, by rfl⟩ : syracuseStep 3158777 = 2369083) B2369083
theorem B2105851 : Blo 2105435 2105851 := bstep (se 1 (by rfl) ⟨1579388, by rfl⟩ : syracuseStep 2105851 = 3158777) B3158777
theorem B5403173 : Blo 2105435 5403173 := bbase (se 4 (by rfl) ⟨506547, by rfl⟩ : syracuseStep 5403173 = 1013095) (by norm_num)
theorem B14408461 : Blo 2105435 14408461 := bstep (se 3 (by rfl) ⟨2701586, by rfl⟩ : syracuseStep 14408461 = 5403173) B5403173
theorem B76845125 : Blo 2105435 76845125 := bstep (se 4 (by rfl) ⟨7204230, by rfl⟩ : syracuseStep 76845125 = 14408461) B14408461
theorem B51230083 : Blo 2105435 51230083 := bstep (se 1 (by rfl) ⟨38422562, by rfl⟩ : syracuseStep 51230083 = 76845125) B76845125
theorem B68306777 : Blo 2105435 68306777 := bstep (se 2 (by rfl) ⟨25615041, by rfl⟩ : syracuseStep 68306777 = 51230083) B51230083
theorem B45537851 : Blo 2105435 45537851 := bstep (se 1 (by rfl) ⟨34153388, by rfl⟩ : syracuseStep 45537851 = 68306777) B68306777
theorem B30358567 : Blo 2105435 30358567 := bstep (se 1 (by rfl) ⟨22768925, by rfl⟩ : syracuseStep 30358567 = 45537851) B45537851
theorem B40478089 : Blo 2105435 40478089 := bstep (se 2 (by rfl) ⟨15179283, by rfl⟩ : syracuseStep 40478089 = 30358567) B30358567
theorem B53970785 : Blo 2105435 53970785 := bstep (se 2 (by rfl) ⟨20239044, by rfl⟩ : syracuseStep 53970785 = 40478089) B40478089
theorem B35980523 : Blo 2105435 35980523 := bstep (se 1 (by rfl) ⟨26985392, by rfl⟩ : syracuseStep 35980523 = 53970785) B53970785
theorem B23987015 : Blo 2105435 23987015 := bstep (se 1 (by rfl) ⟨17990261, by rfl⟩ : syracuseStep 23987015 = 35980523) B35980523
theorem B15991343 : Blo 2105435 15991343 := bstep (se 1 (by rfl) ⟨11993507, by rfl⟩ : syracuseStep 15991343 = 23987015) B23987015
theorem B10660895 : Blo 2105435 10660895 := bstep (se 1 (by rfl) ⟨7995671, by rfl⟩ : syracuseStep 10660895 = 15991343) B15991343
theorem B7107263 : Blo 2105435 7107263 := bstep (se 1 (by rfl) ⟨5330447, by rfl⟩ : syracuseStep 7107263 = 10660895) B10660895
theorem B4738175 : Blo 2105435 4738175 := bstep (se 1 (by rfl) ⟨3553631, by rfl⟩ : syracuseStep 4738175 = 7107263) B7107263
theorem B3158783 : Blo 2105435 3158783 := bstep (se 1 (by rfl) ⟨2369087, by rfl⟩ : syracuseStep 3158783 = 4738175) B4738175
theorem B2105855 : Blo 2105435 2105855 := bstep (se 1 (by rfl) ⟨1579391, by rfl⟩ : syracuseStep 2105855 = 3158783) B3158783
theorem B3158789 : Blo 2105435 3158789 := bbase (se 4 (by rfl) ⟨296136, by rfl⟩ : syracuseStep 3158789 = 592273) (by norm_num)
theorem B2105859 : Blo 2105435 2105859 := bstep (se 1 (by rfl) ⟨1579394, by rfl⟩ : syracuseStep 2105859 = 3158789) B3158789
theorem B3553645 : Blo 2105435 3553645 := bbase (se 3 (by rfl) ⟨666308, by rfl⟩ : syracuseStep 3553645 = 1332617) (by norm_num)
theorem B4738193 : Blo 2105435 4738193 := bstep (se 2 (by rfl) ⟨1776822, by rfl⟩ : syracuseStep 4738193 = 3553645) B3553645
theorem B3158795 : Blo 2105435 3158795 := bstep (se 1 (by rfl) ⟨2369096, by rfl⟩ : syracuseStep 3158795 = 4738193) B4738193
theorem B2105863 : Blo 2105435 2105863 := bstep (se 1 (by rfl) ⟨1579397, by rfl⟩ : syracuseStep 2105863 = 3158795) B3158795
theorem B2369101 : Blo 2105435 2369101 := bbase (se 3 (by rfl) ⟨444206, by rfl⟩ : syracuseStep 2369101 = 888413) (by norm_num)
theorem B3158801 : Blo 2105435 3158801 := bstep (se 2 (by rfl) ⟨1184550, by rfl⟩ : syracuseStep 3158801 = 2369101) B2369101
theorem B2105867 : Blo 2105435 2105867 := bstep (se 1 (by rfl) ⟨1579400, by rfl⟩ : syracuseStep 2105867 = 3158801) B3158801
theorem B7107317 : Blo 2105435 7107317 := bbase (se 5 (by rfl) ⟨333155, by rfl⟩ : syracuseStep 7107317 = 666311) (by norm_num)
theorem B4738211 : Blo 2105435 4738211 := bstep (se 1 (by rfl) ⟨3553658, by rfl⟩ : syracuseStep 4738211 = 7107317) B7107317
theorem B3158807 : Blo 2105435 3158807 := bstep (se 1 (by rfl) ⟨2369105, by rfl⟩ : syracuseStep 3158807 = 4738211) B4738211
theorem B2105871 : Blo 2105435 2105871 := bstep (se 1 (by rfl) ⟨1579403, by rfl⟩ : syracuseStep 2105871 = 3158807) B3158807
theorem B3158813 : Blo 2105435 3158813 := bbase (se 3 (by rfl) ⟨592277, by rfl⟩ : syracuseStep 3158813 = 1184555) (by norm_num)
theorem B2105875 : Blo 2105435 2105875 := bstep (se 1 (by rfl) ⟨1579406, by rfl⟩ : syracuseStep 2105875 = 3158813) B3158813
theorem B4738229 : Blo 2105435 4738229 := bbase (se 5 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 4738229 = 444209) (by norm_num)
theorem B3158819 : Blo 2105435 3158819 := bstep (se 1 (by rfl) ⟨2369114, by rfl⟩ : syracuseStep 3158819 = 4738229) B4738229
theorem B2105879 : Blo 2105435 2105879 := bstep (se 1 (by rfl) ⟨1579409, by rfl⟩ : syracuseStep 2105879 = 3158819) B3158819
theorem B2248813 : Blo 2105435 2248813 := bbase (se 3 (by rfl) ⟨421652, by rfl⟩ : syracuseStep 2248813 = 843305) (by norm_num)
theorem B11993669 : Blo 2105435 11993669 := bstep (se 4 (by rfl) ⟨1124406, by rfl⟩ : syracuseStep 11993669 = 2248813) B2248813
theorem B7995779 : Blo 2105435 7995779 := bstep (se 1 (by rfl) ⟨5996834, by rfl⟩ : syracuseStep 7995779 = 11993669) B11993669
theorem B5330519 : Blo 2105435 5330519 := bstep (se 1 (by rfl) ⟨3997889, by rfl⟩ : syracuseStep 5330519 = 7995779) B7995779
theorem B3553679 : Blo 2105435 3553679 := bstep (se 1 (by rfl) ⟨2665259, by rfl⟩ : syracuseStep 3553679 = 5330519) B5330519
theorem B2369119 : Blo 2105435 2369119 := bstep (se 1 (by rfl) ⟨1776839, by rfl⟩ : syracuseStep 2369119 = 3553679) B3553679
theorem B3158825 : Blo 2105435 3158825 := bstep (se 2 (by rfl) ⟨1184559, by rfl⟩ : syracuseStep 3158825 = 2369119) B2369119
theorem B2105883 : Blo 2105435 2105883 := bstep (se 1 (by rfl) ⟨1579412, by rfl⟩ : syracuseStep 2105883 = 3158825) B3158825
theorem B2248817 : Blo 2105435 2248817 := bbase (se 2 (by rfl) ⟨843306, by rfl⟩ : syracuseStep 2248817 = 1686613) (by norm_num)
theorem B5996845 : Blo 2105435 5996845 := bstep (se 3 (by rfl) ⟨1124408, by rfl⟩ : syracuseStep 5996845 = 2248817) B2248817
theorem B7995793 : Blo 2105435 7995793 := bstep (se 2 (by rfl) ⟨2998422, by rfl⟩ : syracuseStep 7995793 = 5996845) B5996845
theorem B10661057 : Blo 2105435 10661057 := bstep (se 2 (by rfl) ⟨3997896, by rfl⟩ : syracuseStep 10661057 = 7995793) B7995793
theorem B7107371 : Blo 2105435 7107371 := bstep (se 1 (by rfl) ⟨5330528, by rfl⟩ : syracuseStep 7107371 = 10661057) B10661057
theorem B4738247 : Blo 2105435 4738247 := bstep (se 1 (by rfl) ⟨3553685, by rfl⟩ : syracuseStep 4738247 = 7107371) B7107371
theorem B3158831 : Blo 2105435 3158831 := bstep (se 1 (by rfl) ⟨2369123, by rfl⟩ : syracuseStep 3158831 = 4738247) B4738247
theorem B2105887 : Blo 2105435 2105887 := bstep (se 1 (by rfl) ⟨1579415, by rfl⟩ : syracuseStep 2105887 = 3158831) B3158831
theorem B3158837 : Blo 2105435 3158837 := bbase (se 5 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 3158837 = 296141) (by norm_num)
theorem B2105891 : Blo 2105435 2105891 := bstep (se 1 (by rfl) ⟨1579418, by rfl⟩ : syracuseStep 2105891 = 3158837) B3158837
theorem B5330549 : Blo 2105435 5330549 := bbase (se 5 (by rfl) ⟨249869, by rfl⟩ : syracuseStep 5330549 = 499739) (by norm_num)
theorem B3553699 : Blo 2105435 3553699 := bstep (se 1 (by rfl) ⟨2665274, by rfl⟩ : syracuseStep 3553699 = 5330549) B5330549
theorem B4738265 : Blo 2105435 4738265 := bstep (se 2 (by rfl) ⟨1776849, by rfl⟩ : syracuseStep 4738265 = 3553699) B3553699
theorem B3158843 : Blo 2105435 3158843 := bstep (se 1 (by rfl) ⟨2369132, by rfl⟩ : syracuseStep 3158843 = 4738265) B4738265
theorem B2105895 : Blo 2105435 2105895 := bstep (se 1 (by rfl) ⟨1579421, by rfl⟩ : syracuseStep 2105895 = 3158843) B3158843
theorem B2369137 : Blo 2105435 2369137 := bbase (se 2 (by rfl) ⟨888426, by rfl⟩ : syracuseStep 2369137 = 1776853) (by norm_num)
theorem B3158849 : Blo 2105435 3158849 := bstep (se 2 (by rfl) ⟨1184568, by rfl⟩ : syracuseStep 3158849 = 2369137) B2369137
theorem B2105899 : Blo 2105435 2105899 := bstep (se 1 (by rfl) ⟨1579424, by rfl⟩ : syracuseStep 2105899 = 3158849) B3158849
theorem B11384725 : Blo 2105435 11384725 := bbase (se 6 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 11384725 = 533659) (by norm_num)
theorem B15179633 : Blo 2105435 15179633 := bstep (se 2 (by rfl) ⟨5692362, by rfl⟩ : syracuseStep 15179633 = 11384725) B11384725
theorem B10119755 : Blo 2105435 10119755 := bstep (se 1 (by rfl) ⟨7589816, by rfl⟩ : syracuseStep 10119755 = 15179633) B15179633
theorem B6746503 : Blo 2105435 6746503 := bstep (se 1 (by rfl) ⟨5059877, by rfl⟩ : syracuseStep 6746503 = 10119755) B10119755
theorem B8995337 : Blo 2105435 8995337 := bstep (se 2 (by rfl) ⟨3373251, by rfl⟩ : syracuseStep 8995337 = 6746503) B6746503
theorem B5996891 : Blo 2105435 5996891 := bstep (se 1 (by rfl) ⟨4497668, by rfl⟩ : syracuseStep 5996891 = 8995337) B8995337
theorem B3997927 : Blo 2105435 3997927 := bstep (se 1 (by rfl) ⟨2998445, by rfl⟩ : syracuseStep 3997927 = 5996891) B5996891
theorem B5330569 : Blo 2105435 5330569 := bstep (se 2 (by rfl) ⟨1998963, by rfl⟩ : syracuseStep 5330569 = 3997927) B3997927
theorem B7107425 : Blo 2105435 7107425 := bstep (se 2 (by rfl) ⟨2665284, by rfl⟩ : syracuseStep 7107425 = 5330569) B5330569
theorem B4738283 : Blo 2105435 4738283 := bstep (se 1 (by rfl) ⟨3553712, by rfl⟩ : syracuseStep 4738283 = 7107425) B7107425
theorem B3158855 : Blo 2105435 3158855 := bstep (se 1 (by rfl) ⟨2369141, by rfl⟩ : syracuseStep 3158855 = 4738283) B4738283
theorem B2105903 : Blo 2105435 2105903 := bstep (se 1 (by rfl) ⟨1579427, by rfl⟩ : syracuseStep 2105903 = 3158855) B3158855
theorem B3158861 : Blo 2105435 3158861 := bbase (se 3 (by rfl) ⟨592286, by rfl⟩ : syracuseStep 3158861 = 1184573) (by norm_num)
theorem B2105907 : Blo 2105435 2105907 := bstep (se 1 (by rfl) ⟨1579430, by rfl⟩ : syracuseStep 2105907 = 3158861) B3158861
theorem B4738301 : Blo 2105435 4738301 := bbase (se 3 (by rfl) ⟨888431, by rfl⟩ : syracuseStep 4738301 = 1776863) (by norm_num)
theorem B3158867 : Blo 2105435 3158867 := bstep (se 1 (by rfl) ⟨2369150, by rfl⟩ : syracuseStep 3158867 = 4738301) B4738301
theorem B2105911 : Blo 2105435 2105911 := bstep (se 1 (by rfl) ⟨1579433, by rfl⟩ : syracuseStep 2105911 = 3158867) B3158867
theorem B3553733 : Blo 2105435 3553733 := bbase (se 4 (by rfl) ⟨333162, by rfl⟩ : syracuseStep 3553733 = 666325) (by norm_num)
theorem B2369155 : Blo 2105435 2369155 := bstep (se 1 (by rfl) ⟨1776866, by rfl⟩ : syracuseStep 2369155 = 3553733) B3553733
theorem B3158873 : Blo 2105435 3158873 := bstep (se 2 (by rfl) ⟨1184577, by rfl⟩ : syracuseStep 3158873 = 2369155) B2369155
theorem B2105915 : Blo 2105435 2105915 := bstep (se 1 (by rfl) ⟨1579436, by rfl⟩ : syracuseStep 2105915 = 3158873) B3158873
theorem B15991829 : Blo 2105435 15991829 := bbase (se 6 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 15991829 = 749617) (by norm_num)
theorem B10661219 : Blo 2105435 10661219 := bstep (se 1 (by rfl) ⟨7995914, by rfl⟩ : syracuseStep 10661219 = 15991829) B15991829
theorem B7107479 : Blo 2105435 7107479 := bstep (se 1 (by rfl) ⟨5330609, by rfl⟩ : syracuseStep 7107479 = 10661219) B10661219
theorem B4738319 : Blo 2105435 4738319 := bstep (se 1 (by rfl) ⟨3553739, by rfl⟩ : syracuseStep 4738319 = 7107479) B7107479
theorem B3158879 : Blo 2105435 3158879 := bstep (se 1 (by rfl) ⟨2369159, by rfl⟩ : syracuseStep 3158879 = 4738319) B4738319
theorem B2105919 : Blo 2105435 2105919 := bstep (se 1 (by rfl) ⟨1579439, by rfl⟩ : syracuseStep 2105919 = 3158879) B3158879
theorem B3158885 : Blo 2105435 3158885 := bbase (se 4 (by rfl) ⟨296145, by rfl⟩ : syracuseStep 3158885 = 592291) (by norm_num)
theorem B2105923 : Blo 2105435 2105923 := bstep (se 1 (by rfl) ⟨1579442, by rfl⟩ : syracuseStep 2105923 = 3158885) B3158885
theorem B3997973 : Blo 2105435 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B2665315 : Blo 2105435 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B3553753 : Blo 2105435 3553753 := bstep (se 2 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 3553753 = 2665315) B2665315
theorem B4738337 : Blo 2105435 4738337 := bstep (se 2 (by rfl) ⟨1776876, by rfl⟩ : syracuseStep 4738337 = 3553753) B3553753
theorem B3158891 : Blo 2105435 3158891 := bstep (se 1 (by rfl) ⟨2369168, by rfl⟩ : syracuseStep 3158891 = 4738337) B4738337
theorem B2105927 : Blo 2105435 2105927 := bstep (se 1 (by rfl) ⟨1579445, by rfl⟩ : syracuseStep 2105927 = 3158891) B3158891
theorem B2369173 : Blo 2105435 2369173 := bbase (se 6 (by rfl) ⟨55527, by rfl⟩ : syracuseStep 2369173 = 111055) (by norm_num)
theorem B3158897 : Blo 2105435 3158897 := bstep (se 2 (by rfl) ⟨1184586, by rfl⟩ : syracuseStep 3158897 = 2369173) B2369173
theorem B2105931 : Blo 2105435 2105931 := bstep (se 1 (by rfl) ⟨1579448, by rfl⟩ : syracuseStep 2105931 = 3158897) B3158897
theorem B2665325 : Blo 2105435 2665325 := bbase (se 3 (by rfl) ⟨499748, by rfl⟩ : syracuseStep 2665325 = 999497) (by norm_num)
theorem B7107533 : Blo 2105435 7107533 := bstep (se 3 (by rfl) ⟨1332662, by rfl⟩ : syracuseStep 7107533 = 2665325) B2665325
theorem B4738355 : Blo 2105435 4738355 := bstep (se 1 (by rfl) ⟨3553766, by rfl⟩ : syracuseStep 4738355 = 7107533) B7107533
theorem B3158903 : Blo 2105435 3158903 := bstep (se 1 (by rfl) ⟨2369177, by rfl⟩ : syracuseStep 3158903 = 4738355) B4738355
theorem B2105935 : Blo 2105435 2105935 := bstep (se 1 (by rfl) ⟨1579451, by rfl⟩ : syracuseStep 2105935 = 3158903) B3158903
theorem B3158909 : Blo 2105435 3158909 := bbase (se 3 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 3158909 = 1184591) (by norm_num)
theorem B2105939 : Blo 2105435 2105939 := bstep (se 1 (by rfl) ⟨1579454, by rfl⟩ : syracuseStep 2105939 = 3158909) B3158909
theorem B4738373 : Blo 2105435 4738373 := bbase (se 4 (by rfl) ⟨444222, by rfl⟩ : syracuseStep 4738373 = 888445) (by norm_num)
theorem B3158915 : Blo 2105435 3158915 := bstep (se 1 (by rfl) ⟨2369186, by rfl⟩ : syracuseStep 3158915 = 4738373) B4738373
theorem B2105943 : Blo 2105435 2105943 := bstep (se 1 (by rfl) ⟨1579457, by rfl⟩ : syracuseStep 2105943 = 3158915) B3158915
theorem B6746645 : Blo 2105435 6746645 := bbase (se 6 (by rfl) ⟨158124, by rfl⟩ : syracuseStep 6746645 = 316249) (by norm_num)
theorem B4497763 : Blo 2105435 4497763 := bstep (se 1 (by rfl) ⟨3373322, by rfl⟩ : syracuseStep 4497763 = 6746645) B6746645
theorem B5997017 : Blo 2105435 5997017 := bstep (se 2 (by rfl) ⟨2248881, by rfl⟩ : syracuseStep 5997017 = 4497763) B4497763
theorem B3998011 : Blo 2105435 3998011 := bstep (se 1 (by rfl) ⟨2998508, by rfl⟩ : syracuseStep 3998011 = 5997017) B5997017
theorem B5330681 : Blo 2105435 5330681 := bstep (se 2 (by rfl) ⟨1999005, by rfl⟩ : syracuseStep 5330681 = 3998011) B3998011
theorem B3553787 : Blo 2105435 3553787 := bstep (se 1 (by rfl) ⟨2665340, by rfl⟩ : syracuseStep 3553787 = 5330681) B5330681
theorem B2369191 : Blo 2105435 2369191 := bstep (se 1 (by rfl) ⟨1776893, by rfl⟩ : syracuseStep 2369191 = 3553787) B3553787
theorem B3158921 : Blo 2105435 3158921 := bstep (se 2 (by rfl) ⟨1184595, by rfl⟩ : syracuseStep 3158921 = 2369191) B2369191
theorem B2105947 : Blo 2105435 2105947 := bstep (se 1 (by rfl) ⟨1579460, by rfl⟩ : syracuseStep 2105947 = 3158921) B3158921
theorem B10661381 : Blo 2105435 10661381 := bbase (se 4 (by rfl) ⟨999504, by rfl⟩ : syracuseStep 10661381 = 1999009) (by norm_num)
theorem B7107587 : Blo 2105435 7107587 := bstep (se 1 (by rfl) ⟨5330690, by rfl⟩ : syracuseStep 7107587 = 10661381) B10661381
theorem B4738391 : Blo 2105435 4738391 := bstep (se 1 (by rfl) ⟨3553793, by rfl⟩ : syracuseStep 4738391 = 7107587) B7107587
theorem B3158927 : Blo 2105435 3158927 := bstep (se 1 (by rfl) ⟨2369195, by rfl⟩ : syracuseStep 3158927 = 4738391) B4738391
theorem B2105951 : Blo 2105435 2105951 := bstep (se 1 (by rfl) ⟨1579463, by rfl⟩ : syracuseStep 2105951 = 3158927) B3158927
theorem B3158933 : Blo 2105435 3158933 := bbase (se 6 (by rfl) ⟨74037, by rfl⟩ : syracuseStep 3158933 = 148075) (by norm_num)
theorem B2105955 : Blo 2105435 2105955 := bstep (se 1 (by rfl) ⟨1579466, by rfl⟩ : syracuseStep 2105955 = 3158933) B3158933
theorem B11994101 : Blo 2105435 11994101 := bbase (se 5 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 11994101 = 1124447) (by norm_num)
theorem B7996067 : Blo 2105435 7996067 := bstep (se 1 (by rfl) ⟨5997050, by rfl⟩ : syracuseStep 7996067 = 11994101) B11994101
theorem B5330711 : Blo 2105435 5330711 := bstep (se 1 (by rfl) ⟨3998033, by rfl⟩ : syracuseStep 5330711 = 7996067) B7996067
theorem B3553807 : Blo 2105435 3553807 := bstep (se 1 (by rfl) ⟨2665355, by rfl⟩ : syracuseStep 3553807 = 5330711) B5330711
theorem B4738409 : Blo 2105435 4738409 := bstep (se 2 (by rfl) ⟨1776903, by rfl⟩ : syracuseStep 4738409 = 3553807) B3553807
theorem B3158939 : Blo 2105435 3158939 := bstep (se 1 (by rfl) ⟨2369204, by rfl⟩ : syracuseStep 3158939 = 4738409) B4738409
theorem B2105959 : Blo 2105435 2105959 := bstep (se 1 (by rfl) ⟨1579469, by rfl⟩ : syracuseStep 2105959 = 3158939) B3158939
theorem B2369209 : Blo 2105435 2369209 := bbase (se 2 (by rfl) ⟨888453, by rfl⟩ : syracuseStep 2369209 = 1776907) (by norm_num)
theorem B3158945 : Blo 2105435 3158945 := bstep (se 2 (by rfl) ⟨1184604, by rfl⟩ : syracuseStep 3158945 = 2369209) B2369209
theorem B2105963 : Blo 2105435 2105963 := bstep (se 1 (by rfl) ⟨1579472, by rfl⟩ : syracuseStep 2105963 = 3158945) B3158945
theorem B4497805 : Blo 2105435 4497805 := bbase (se 3 (by rfl) ⟨843338, by rfl⟩ : syracuseStep 4497805 = 1686677) (by norm_num)
theorem B5997073 : Blo 2105435 5997073 := bstep (se 2 (by rfl) ⟨2248902, by rfl⟩ : syracuseStep 5997073 = 4497805) B4497805
theorem B7996097 : Blo 2105435 7996097 := bstep (se 2 (by rfl) ⟨2998536, by rfl⟩ : syracuseStep 7996097 = 5997073) B5997073
theorem B5330731 : Blo 2105435 5330731 := bstep (se 1 (by rfl) ⟨3998048, by rfl⟩ : syracuseStep 5330731 = 7996097) B7996097
theorem B7107641 : Blo 2105435 7107641 := bstep (se 2 (by rfl) ⟨2665365, by rfl⟩ : syracuseStep 7107641 = 5330731) B5330731
theorem B4738427 : Blo 2105435 4738427 := bstep (se 1 (by rfl) ⟨3553820, by rfl⟩ : syracuseStep 4738427 = 7107641) B7107641
theorem B3158951 : Blo 2105435 3158951 := bstep (se 1 (by rfl) ⟨2369213, by rfl⟩ : syracuseStep 3158951 = 4738427) B4738427
theorem B2105967 : Blo 2105435 2105967 := bstep (se 1 (by rfl) ⟨1579475, by rfl⟩ : syracuseStep 2105967 = 3158951) B3158951
theorem B3158957 : Blo 2105435 3158957 := bbase (se 3 (by rfl) ⟨592304, by rfl⟩ : syracuseStep 3158957 = 1184609) (by norm_num)
theorem B2105971 : Blo 2105435 2105971 := bstep (se 1 (by rfl) ⟨1579478, by rfl⟩ : syracuseStep 2105971 = 3158957) B3158957
theorem B4738445 : Blo 2105435 4738445 := bbase (se 3 (by rfl) ⟨888458, by rfl⟩ : syracuseStep 4738445 = 1776917) (by norm_num)
theorem B3158963 : Blo 2105435 3158963 := bstep (se 1 (by rfl) ⟨2369222, by rfl⟩ : syracuseStep 3158963 = 4738445) B4738445
theorem B2105975 : Blo 2105435 2105975 := bstep (se 1 (by rfl) ⟨1579481, by rfl⟩ : syracuseStep 2105975 = 3158963) B3158963
theorem B2665381 : Blo 2105435 2665381 := bbase (se 4 (by rfl) ⟨249879, by rfl⟩ : syracuseStep 2665381 = 499759) (by norm_num)
theorem B3553841 : Blo 2105435 3553841 := bstep (se 2 (by rfl) ⟨1332690, by rfl⟩ : syracuseStep 3553841 = 2665381) B2665381
theorem B2369227 : Blo 2105435 2369227 := bstep (se 1 (by rfl) ⟨1776920, by rfl⟩ : syracuseStep 2369227 = 3553841) B3553841
theorem B3158969 : Blo 2105435 3158969 := bstep (se 2 (by rfl) ⟨1184613, by rfl⟩ : syracuseStep 3158969 = 2369227) B2369227
theorem B2105979 : Blo 2105435 2105979 := bstep (se 1 (by rfl) ⟨1579484, by rfl⟩ : syracuseStep 2105979 = 3158969) B3158969
theorem B4327685 : Blo 2105435 4327685 := bbase (se 4 (by rfl) ⟨405720, by rfl⟩ : syracuseStep 4327685 = 811441) (by norm_num)
theorem B2885123 : Blo 2105435 2885123 := bstep (se 1 (by rfl) ⟨2163842, by rfl⟩ : syracuseStep 2885123 = 4327685) B4327685
theorem B7693661 : Blo 2105435 7693661 := bstep (se 3 (by rfl) ⟨1442561, by rfl⟩ : syracuseStep 7693661 = 2885123) B2885123
theorem B20516429 : Blo 2105435 20516429 := bstep (se 3 (by rfl) ⟨3846830, by rfl⟩ : syracuseStep 20516429 = 7693661) B7693661
theorem B13677619 : Blo 2105435 13677619 := bstep (se 1 (by rfl) ⟨10258214, by rfl⟩ : syracuseStep 13677619 = 20516429) B20516429
theorem B18236825 : Blo 2105435 18236825 := bstep (se 2 (by rfl) ⟨6838809, by rfl⟩ : syracuseStep 18236825 = 13677619) B13677619
theorem B12157883 : Blo 2105435 12157883 := bstep (se 1 (by rfl) ⟨9118412, by rfl⟩ : syracuseStep 12157883 = 18236825) B18236825
theorem B8105255 : Blo 2105435 8105255 := bstep (se 1 (by rfl) ⟨6078941, by rfl⟩ : syracuseStep 8105255 = 12157883) B12157883
theorem B5403503 : Blo 2105435 5403503 := bstep (se 1 (by rfl) ⟨4052627, by rfl⟩ : syracuseStep 5403503 = 8105255) B8105255
theorem B3602335 : Blo 2105435 3602335 := bstep (se 1 (by rfl) ⟨2701751, by rfl⟩ : syracuseStep 3602335 = 5403503) B5403503
theorem B4803113 : Blo 2105435 4803113 := bstep (se 2 (by rfl) ⟨1801167, by rfl⟩ : syracuseStep 4803113 = 3602335) B3602335
theorem B3202075 : Blo 2105435 3202075 := bstep (se 1 (by rfl) ⟨2401556, by rfl⟩ : syracuseStep 3202075 = 4803113) B4803113
theorem B17077733 : Blo 2105435 17077733 := bstep (se 4 (by rfl) ⟨1601037, by rfl⟩ : syracuseStep 17077733 = 3202075) B3202075
theorem B11385155 : Blo 2105435 11385155 := bstep (se 1 (by rfl) ⟨8538866, by rfl⟩ : syracuseStep 11385155 = 17077733) B17077733
theorem B30360413 : Blo 2105435 30360413 := bstep (se 3 (by rfl) ⟨5692577, by rfl⟩ : syracuseStep 30360413 = 11385155) B11385155
theorem B20240275 : Blo 2105435 20240275 := bstep (se 1 (by rfl) ⟨15180206, by rfl⟩ : syracuseStep 20240275 = 30360413) B30360413
theorem B26987033 : Blo 2105435 26987033 := bstep (se 2 (by rfl) ⟨10120137, by rfl⟩ : syracuseStep 26987033 = 20240275) B20240275
theorem B17991355 : Blo 2105435 17991355 := bstep (se 1 (by rfl) ⟨13493516, by rfl⟩ : syracuseStep 17991355 = 26987033) B26987033
theorem B23988473 : Blo 2105435 23988473 := bstep (se 2 (by rfl) ⟨8995677, by rfl⟩ : syracuseStep 23988473 = 17991355) B17991355
theorem B15992315 : Blo 2105435 15992315 := bstep (se 1 (by rfl) ⟨11994236, by rfl⟩ : syracuseStep 15992315 = 23988473) B23988473
theorem B10661543 : Blo 2105435 10661543 := bstep (se 1 (by rfl) ⟨7996157, by rfl⟩ : syracuseStep 10661543 = 15992315) B15992315
theorem B7107695 : Blo 2105435 7107695 := bstep (se 1 (by rfl) ⟨5330771, by rfl⟩ : syracuseStep 7107695 = 10661543) B10661543
theorem B4738463 : Blo 2105435 4738463 := bstep (se 1 (by rfl) ⟨3553847, by rfl⟩ : syracuseStep 4738463 = 7107695) B7107695
theorem B3158975 : Blo 2105435 3158975 := bstep (se 1 (by rfl) ⟨2369231, by rfl⟩ : syracuseStep 3158975 = 4738463) B4738463
theorem B2105983 : Blo 2105435 2105983 := bstep (se 1 (by rfl) ⟨1579487, by rfl⟩ : syracuseStep 2105983 = 3158975) B3158975
theorem B3158981 : Blo 2105435 3158981 := bbase (se 4 (by rfl) ⟨296154, by rfl⟩ : syracuseStep 3158981 = 592309) (by norm_num)
theorem B2105987 : Blo 2105435 2105987 := bstep (se 1 (by rfl) ⟨1579490, by rfl⟩ : syracuseStep 2105987 = 3158981) B3158981
theorem B3553861 : Blo 2105435 3553861 := bbase (se 4 (by rfl) ⟨333174, by rfl⟩ : syracuseStep 3553861 = 666349) (by norm_num)
theorem B4738481 : Blo 2105435 4738481 := bstep (se 2 (by rfl) ⟨1776930, by rfl⟩ : syracuseStep 4738481 = 3553861) B3553861
theorem B3158987 : Blo 2105435 3158987 := bstep (se 1 (by rfl) ⟨2369240, by rfl⟩ : syracuseStep 3158987 = 4738481) B4738481
theorem B2105991 : Blo 2105435 2105991 := bstep (se 1 (by rfl) ⟨1579493, by rfl⟩ : syracuseStep 2105991 = 3158987) B3158987
theorem B2369245 : Blo 2105435 2369245 := bbase (se 3 (by rfl) ⟨444233, by rfl⟩ : syracuseStep 2369245 = 888467) (by norm_num)
theorem B3158993 : Blo 2105435 3158993 := bstep (se 2 (by rfl) ⟨1184622, by rfl⟩ : syracuseStep 3158993 = 2369245) B2369245
theorem B2105995 : Blo 2105435 2105995 := bstep (se 1 (by rfl) ⟨1579496, by rfl⟩ : syracuseStep 2105995 = 3158993) B3158993
theorem B7107749 : Blo 2105435 7107749 := bbase (se 4 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 7107749 = 1332703) (by norm_num)
theorem B4738499 : Blo 2105435 4738499 := bstep (se 1 (by rfl) ⟨3553874, by rfl⟩ : syracuseStep 4738499 = 7107749) B7107749
theorem B3158999 : Blo 2105435 3158999 := bstep (se 1 (by rfl) ⟨2369249, by rfl⟩ : syracuseStep 3158999 = 4738499) B4738499
theorem B2105999 : Blo 2105435 2105999 := bstep (se 1 (by rfl) ⟨1579499, by rfl⟩ : syracuseStep 2105999 = 3158999) B3158999
theorem B3159005 : Blo 2105435 3159005 := bbase (se 3 (by rfl) ⟨592313, by rfl⟩ : syracuseStep 3159005 = 1184627) (by norm_num)
theorem B2106003 : Blo 2105435 2106003 := bstep (se 1 (by rfl) ⟨1579502, by rfl⟩ : syracuseStep 2106003 = 3159005) B3159005
theorem B4738517 : Blo 2105435 4738517 := bbase (se 7 (by rfl) ⟨55529, by rfl⟩ : syracuseStep 4738517 = 111059) (by norm_num)
theorem B3159011 : Blo 2105435 3159011 := bstep (se 1 (by rfl) ⟨2369258, by rfl⟩ : syracuseStep 3159011 = 4738517) B4738517
theorem B2106007 : Blo 2105435 2106007 := bstep (se 1 (by rfl) ⟨1579505, by rfl⟩ : syracuseStep 2106007 = 3159011) B3159011
theorem B3651533 : Blo 2105435 3651533 := bbase (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) (by norm_num)
theorem B2434355 : Blo 2105435 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B25966453 : Blo 2105435 25966453 := bstep (se 5 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 25966453 = 2434355) B2434355
theorem B34621937 : Blo 2105435 34621937 := bstep (se 2 (by rfl) ⟨12983226, by rfl⟩ : syracuseStep 34621937 = 25966453) B25966453
theorem B23081291 : Blo 2105435 23081291 := bstep (se 1 (by rfl) ⟨17310968, by rfl⟩ : syracuseStep 23081291 = 34621937) B34621937
theorem B15387527 : Blo 2105435 15387527 := bstep (se 1 (by rfl) ⟨11540645, by rfl⟩ : syracuseStep 15387527 = 23081291) B23081291
theorem B41033405 : Blo 2105435 41033405 := bstep (se 3 (by rfl) ⟨7693763, by rfl⟩ : syracuseStep 41033405 = 15387527) B15387527
theorem B109422413 : Blo 2105435 109422413 := bstep (se 3 (by rfl) ⟨20516702, by rfl⟩ : syracuseStep 109422413 = 41033405) B41033405
theorem B72948275 : Blo 2105435 72948275 := bstep (se 1 (by rfl) ⟨54711206, by rfl⟩ : syracuseStep 72948275 = 109422413) B109422413
theorem B48632183 : Blo 2105435 48632183 := bstep (se 1 (by rfl) ⟨36474137, by rfl⟩ : syracuseStep 48632183 = 72948275) B72948275
theorem B32421455 : Blo 2105435 32421455 := bstep (se 1 (by rfl) ⟨24316091, by rfl⟩ : syracuseStep 32421455 = 48632183) B48632183
theorem B21614303 : Blo 2105435 21614303 := bstep (se 1 (by rfl) ⟨16210727, by rfl⟩ : syracuseStep 21614303 = 32421455) B32421455
theorem B14409535 : Blo 2105435 14409535 := bstep (se 1 (by rfl) ⟨10807151, by rfl⟩ : syracuseStep 14409535 = 21614303) B21614303
theorem B19212713 : Blo 2105435 19212713 := bstep (se 2 (by rfl) ⟨7204767, by rfl⟩ : syracuseStep 19212713 = 14409535) B14409535
theorem B12808475 : Blo 2105435 12808475 := bstep (se 1 (by rfl) ⟨9606356, by rfl⟩ : syracuseStep 12808475 = 19212713) B19212713
theorem B8538983 : Blo 2105435 8538983 := bstep (se 1 (by rfl) ⟨6404237, by rfl⟩ : syracuseStep 8538983 = 12808475) B12808475
theorem B5692655 : Blo 2105435 5692655 := bstep (se 1 (by rfl) ⟨4269491, by rfl⟩ : syracuseStep 5692655 = 8538983) B8538983
theorem B3795103 : Blo 2105435 3795103 := bstep (se 1 (by rfl) ⟨2846327, by rfl⟩ : syracuseStep 3795103 = 5692655) B5692655
theorem B20240549 : Blo 2105435 20240549 := bstep (se 4 (by rfl) ⟨1897551, by rfl⟩ : syracuseStep 20240549 = 3795103) B3795103
theorem B13493699 : Blo 2105435 13493699 := bstep (se 1 (by rfl) ⟨10120274, by rfl⟩ : syracuseStep 13493699 = 20240549) B20240549
theorem B8995799 : Blo 2105435 8995799 := bstep (se 1 (by rfl) ⟨6746849, by rfl⟩ : syracuseStep 8995799 = 13493699) B13493699
theorem B5997199 : Blo 2105435 5997199 := bstep (se 1 (by rfl) ⟨4497899, by rfl⟩ : syracuseStep 5997199 = 8995799) B8995799
theorem B7996265 : Blo 2105435 7996265 := bstep (se 2 (by rfl) ⟨2998599, by rfl⟩ : syracuseStep 7996265 = 5997199) B5997199
theorem B5330843 : Blo 2105435 5330843 := bstep (se 1 (by rfl) ⟨3998132, by rfl⟩ : syracuseStep 5330843 = 7996265) B7996265
theorem B3553895 : Blo 2105435 3553895 := bstep (se 1 (by rfl) ⟨2665421, by rfl⟩ : syracuseStep 3553895 = 5330843) B5330843
theorem B2369263 : Blo 2105435 2369263 := bstep (se 1 (by rfl) ⟨1776947, by rfl⟩ : syracuseStep 2369263 = 3553895) B3553895
theorem B3159017 : Blo 2105435 3159017 := bstep (se 2 (by rfl) ⟨1184631, by rfl⟩ : syracuseStep 3159017 = 2369263) B2369263
theorem B2106011 : Blo 2105435 2106011 := bstep (se 1 (by rfl) ⟨1579508, by rfl⟩ : syracuseStep 2106011 = 3159017) B3159017
theorem B2530073 : Blo 2105435 2530073 := bbase (se 2 (by rfl) ⟨948777, by rfl⟩ : syracuseStep 2530073 = 1897555) (by norm_num)
theorem B6746861 : Blo 2105435 6746861 := bstep (se 3 (by rfl) ⟨1265036, by rfl⟩ : syracuseStep 6746861 = 2530073) B2530073
theorem B17991629 : Blo 2105435 17991629 := bstep (se 3 (by rfl) ⟨3373430, by rfl⟩ : syracuseStep 17991629 = 6746861) B6746861
theorem B11994419 : Blo 2105435 11994419 := bstep (se 1 (by rfl) ⟨8995814, by rfl⟩ : syracuseStep 11994419 = 17991629) B17991629
theorem B7996279 : Blo 2105435 7996279 := bstep (se 1 (by rfl) ⟨5997209, by rfl⟩ : syracuseStep 7996279 = 11994419) B11994419
theorem B10661705 : Blo 2105435 10661705 := bstep (se 2 (by rfl) ⟨3998139, by rfl⟩ : syracuseStep 10661705 = 7996279) B7996279
theorem B7107803 : Blo 2105435 7107803 := bstep (se 1 (by rfl) ⟨5330852, by rfl⟩ : syracuseStep 7107803 = 10661705) B10661705
theorem B4738535 : Blo 2105435 4738535 := bstep (se 1 (by rfl) ⟨3553901, by rfl⟩ : syracuseStep 4738535 = 7107803) B7107803
theorem B3159023 : Blo 2105435 3159023 := bstep (se 1 (by rfl) ⟨2369267, by rfl⟩ : syracuseStep 3159023 = 4738535) B4738535
theorem B2106015 : Blo 2105435 2106015 := bstep (se 1 (by rfl) ⟨1579511, by rfl⟩ : syracuseStep 2106015 = 3159023) B3159023
theorem B3159029 : Blo 2105435 3159029 := bbase (se 5 (by rfl) ⟨148079, by rfl⟩ : syracuseStep 3159029 = 296159) (by norm_num)
theorem B2106019 : Blo 2105435 2106019 := bstep (se 1 (by rfl) ⟨1579514, by rfl⟩ : syracuseStep 2106019 = 3159029) B3159029
theorem B4497925 : Blo 2105435 4497925 := bbase (se 4 (by rfl) ⟨421680, by rfl⟩ : syracuseStep 4497925 = 843361) (by norm_num)
theorem B5997233 : Blo 2105435 5997233 := bstep (se 2 (by rfl) ⟨2248962, by rfl⟩ : syracuseStep 5997233 = 4497925) B4497925
theorem B3998155 : Blo 2105435 3998155 := bstep (se 1 (by rfl) ⟨2998616, by rfl⟩ : syracuseStep 3998155 = 5997233) B5997233
theorem B5330873 : Blo 2105435 5330873 := bstep (se 2 (by rfl) ⟨1999077, by rfl⟩ : syracuseStep 5330873 = 3998155) B3998155
theorem B3553915 : Blo 2105435 3553915 := bstep (se 1 (by rfl) ⟨2665436, by rfl⟩ : syracuseStep 3553915 = 5330873) B5330873
theorem B4738553 : Blo 2105435 4738553 := bstep (se 2 (by rfl) ⟨1776957, by rfl⟩ : syracuseStep 4738553 = 3553915) B3553915
theorem B3159035 : Blo 2105435 3159035 := bstep (se 1 (by rfl) ⟨2369276, by rfl⟩ : syracuseStep 3159035 = 4738553) B4738553
theorem B2106023 : Blo 2105435 2106023 := bstep (se 1 (by rfl) ⟨1579517, by rfl⟩ : syracuseStep 2106023 = 3159035) B3159035
theorem B2369281 : Blo 2105435 2369281 := bbase (se 2 (by rfl) ⟨888480, by rfl⟩ : syracuseStep 2369281 = 1776961) (by norm_num)
theorem B3159041 : Blo 2105435 3159041 := bstep (se 2 (by rfl) ⟨1184640, by rfl⟩ : syracuseStep 3159041 = 2369281) B2369281
theorem B2106027 : Blo 2105435 2106027 := bstep (se 1 (by rfl) ⟨1579520, by rfl⟩ : syracuseStep 2106027 = 3159041) B3159041
theorem B5330893 : Blo 2105435 5330893 := bbase (se 3 (by rfl) ⟨999542, by rfl⟩ : syracuseStep 5330893 = 1999085) (by norm_num)
theorem B7107857 : Blo 2105435 7107857 := bstep (se 2 (by rfl) ⟨2665446, by rfl⟩ : syracuseStep 7107857 = 5330893) B5330893
theorem B4738571 : Blo 2105435 4738571 := bstep (se 1 (by rfl) ⟨3553928, by rfl⟩ : syracuseStep 4738571 = 7107857) B7107857
theorem B3159047 : Blo 2105435 3159047 := bstep (se 1 (by rfl) ⟨2369285, by rfl⟩ : syracuseStep 3159047 = 4738571) B4738571
theorem B2106031 : Blo 2105435 2106031 := bstep (se 1 (by rfl) ⟨1579523, by rfl⟩ : syracuseStep 2106031 = 3159047) B3159047
theorem B3159053 : Blo 2105435 3159053 := bbase (se 3 (by rfl) ⟨592322, by rfl⟩ : syracuseStep 3159053 = 1184645) (by norm_num)
theorem B2106035 : Blo 2105435 2106035 := bstep (se 1 (by rfl) ⟨1579526, by rfl⟩ : syracuseStep 2106035 = 3159053) B3159053
theorem B4738589 : Blo 2105435 4738589 := bbase (se 3 (by rfl) ⟨888485, by rfl⟩ : syracuseStep 4738589 = 1776971) (by norm_num)
theorem B3159059 : Blo 2105435 3159059 := bstep (se 1 (by rfl) ⟨2369294, by rfl⟩ : syracuseStep 3159059 = 4738589) B4738589
theorem B2106039 : Blo 2105435 2106039 := bstep (se 1 (by rfl) ⟨1579529, by rfl⟩ : syracuseStep 2106039 = 3159059) B3159059
theorem B3553949 : Blo 2105435 3553949 := bbase (se 3 (by rfl) ⟨666365, by rfl⟩ : syracuseStep 3553949 = 1332731) (by norm_num)
theorem B2369299 : Blo 2105435 2369299 := bstep (se 1 (by rfl) ⟨1776974, by rfl⟩ : syracuseStep 2369299 = 3553949) B3553949
theorem B3159065 : Blo 2105435 3159065 := bstep (se 2 (by rfl) ⟨1184649, by rfl⟩ : syracuseStep 3159065 = 2369299) B2369299
theorem B2106043 : Blo 2105435 2106043 := bstep (se 1 (by rfl) ⟨1579532, by rfl⟩ : syracuseStep 2106043 = 3159065) B3159065
theorem B38426069 : Blo 2105435 38426069 := bbase (se 7 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 38426069 = 900611) (by norm_num)
theorem B25617379 : Blo 2105435 25617379 := bstep (se 1 (by rfl) ⟨19213034, by rfl⟩ : syracuseStep 25617379 = 38426069) B38426069
theorem B34156505 : Blo 2105435 34156505 := bstep (se 2 (by rfl) ⟨12808689, by rfl⟩ : syracuseStep 34156505 = 25617379) B25617379
theorem B22771003 : Blo 2105435 22771003 := bstep (se 1 (by rfl) ⟨17078252, by rfl⟩ : syracuseStep 22771003 = 34156505) B34156505
theorem B30361337 : Blo 2105435 30361337 := bstep (se 2 (by rfl) ⟨11385501, by rfl⟩ : syracuseStep 30361337 = 22771003) B22771003
theorem B20240891 : Blo 2105435 20240891 := bstep (se 1 (by rfl) ⟨15180668, by rfl⟩ : syracuseStep 20240891 = 30361337) B30361337
theorem B13493927 : Blo 2105435 13493927 := bstep (se 1 (by rfl) ⟨10120445, by rfl⟩ : syracuseStep 13493927 = 20240891) B20240891
theorem B8995951 : Blo 2105435 8995951 := bstep (se 1 (by rfl) ⟨6746963, by rfl⟩ : syracuseStep 8995951 = 13493927) B13493927
theorem B11994601 : Blo 2105435 11994601 := bstep (se 2 (by rfl) ⟨4497975, by rfl⟩ : syracuseStep 11994601 = 8995951) B8995951
theorem B15992801 : Blo 2105435 15992801 := bstep (se 2 (by rfl) ⟨5997300, by rfl⟩ : syracuseStep 15992801 = 11994601) B11994601
theorem B10661867 : Blo 2105435 10661867 := bstep (se 1 (by rfl) ⟨7996400, by rfl⟩ : syracuseStep 10661867 = 15992801) B15992801
theorem B7107911 : Blo 2105435 7107911 := bstep (se 1 (by rfl) ⟨5330933, by rfl⟩ : syracuseStep 7107911 = 10661867) B10661867
theorem B4738607 : Blo 2105435 4738607 := bstep (se 1 (by rfl) ⟨3553955, by rfl⟩ : syracuseStep 4738607 = 7107911) B7107911
theorem B3159071 : Blo 2105435 3159071 := bstep (se 1 (by rfl) ⟨2369303, by rfl⟩ : syracuseStep 3159071 = 4738607) B4738607
theorem B2106047 : Blo 2105435 2106047 := bstep (se 1 (by rfl) ⟨1579535, by rfl⟩ : syracuseStep 2106047 = 3159071) B3159071
theorem B3159077 : Blo 2105435 3159077 := bbase (se 4 (by rfl) ⟨296163, by rfl⟩ : syracuseStep 3159077 = 592327) (by norm_num)
theorem B2106051 : Blo 2105435 2106051 := bstep (se 1 (by rfl) ⟨1579538, by rfl⟩ : syracuseStep 2106051 = 3159077) B3159077
theorem B2665477 : Blo 2105435 2665477 := bbase (se 4 (by rfl) ⟨249888, by rfl⟩ : syracuseStep 2665477 = 499777) (by norm_num)
theorem B3553969 : Blo 2105435 3553969 := bstep (se 2 (by rfl) ⟨1332738, by rfl⟩ : syracuseStep 3553969 = 2665477) B2665477
theorem B4738625 : Blo 2105435 4738625 := bstep (se 2 (by rfl) ⟨1776984, by rfl⟩ : syracuseStep 4738625 = 3553969) B3553969
theorem B3159083 : Blo 2105435 3159083 := bstep (se 1 (by rfl) ⟨2369312, by rfl⟩ : syracuseStep 3159083 = 4738625) B4738625
theorem B2106055 : Blo 2105435 2106055 := bstep (se 1 (by rfl) ⟨1579541, by rfl⟩ : syracuseStep 2106055 = 3159083) B3159083
theorem B2369317 : Blo 2105435 2369317 := bbase (se 4 (by rfl) ⟨222123, by rfl⟩ : syracuseStep 2369317 = 444247) (by norm_num)
theorem B3159089 : Blo 2105435 3159089 := bstep (se 2 (by rfl) ⟨1184658, by rfl⟩ : syracuseStep 3159089 = 2369317) B2369317
theorem B2106059 : Blo 2105435 2106059 := bstep (se 1 (by rfl) ⟨1579544, by rfl⟩ : syracuseStep 2106059 = 3159089) B3159089
theorem B8996021 : Blo 2105435 8996021 := bbase (se 5 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 8996021 = 843377) (by norm_num)
theorem B5997347 : Blo 2105435 5997347 := bstep (se 1 (by rfl) ⟨4498010, by rfl⟩ : syracuseStep 5997347 = 8996021) B8996021
theorem B3998231 : Blo 2105435 3998231 := bstep (se 1 (by rfl) ⟨2998673, by rfl⟩ : syracuseStep 3998231 = 5997347) B5997347
theorem B2665487 : Blo 2105435 2665487 := bstep (se 1 (by rfl) ⟨1999115, by rfl⟩ : syracuseStep 2665487 = 3998231) B3998231
theorem B7107965 : Blo 2105435 7107965 := bstep (se 3 (by rfl) ⟨1332743, by rfl⟩ : syracuseStep 7107965 = 2665487) B2665487
theorem B4738643 : Blo 2105435 4738643 := bstep (se 1 (by rfl) ⟨3553982, by rfl⟩ : syracuseStep 4738643 = 7107965) B7107965
theorem B3159095 : Blo 2105435 3159095 := bstep (se 1 (by rfl) ⟨2369321, by rfl⟩ : syracuseStep 3159095 = 4738643) B4738643
theorem B2106063 : Blo 2105435 2106063 := bstep (se 1 (by rfl) ⟨1579547, by rfl⟩ : syracuseStep 2106063 = 3159095) B3159095
theorem B3159101 : Blo 2105435 3159101 := bbase (se 3 (by rfl) ⟨592331, by rfl⟩ : syracuseStep 3159101 = 1184663) (by norm_num)
theorem B2106067 : Blo 2105435 2106067 := bstep (se 1 (by rfl) ⟨1579550, by rfl⟩ : syracuseStep 2106067 = 3159101) B3159101
theorem B4738661 : Blo 2105435 4738661 := bbase (se 4 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 4738661 = 888499) (by norm_num)
theorem B3159107 : Blo 2105435 3159107 := bstep (se 1 (by rfl) ⟨2369330, by rfl⟩ : syracuseStep 3159107 = 4738661) B4738661
theorem B2106071 : Blo 2105435 2106071 := bstep (se 1 (by rfl) ⟨1579553, by rfl⟩ : syracuseStep 2106071 = 3159107) B3159107
theorem B5331005 : Blo 2105435 5331005 := bbase (se 3 (by rfl) ⟨999563, by rfl⟩ : syracuseStep 5331005 = 1999127) (by norm_num)
theorem B3554003 : Blo 2105435 3554003 := bstep (se 1 (by rfl) ⟨2665502, by rfl⟩ : syracuseStep 3554003 = 5331005) B5331005
theorem B2369335 : Blo 2105435 2369335 := bstep (se 1 (by rfl) ⟨1777001, by rfl⟩ : syracuseStep 2369335 = 3554003) B3554003
theorem B3159113 : Blo 2105435 3159113 := bstep (se 2 (by rfl) ⟨1184667, by rfl⟩ : syracuseStep 3159113 = 2369335) B2369335
theorem B2106075 : Blo 2105435 2106075 := bstep (se 1 (by rfl) ⟨1579556, by rfl⟩ : syracuseStep 2106075 = 3159113) B3159113
theorem B3998261 : Blo 2105435 3998261 := bbase (se 5 (by rfl) ⟨187418, by rfl⟩ : syracuseStep 3998261 = 374837) (by norm_num)
theorem B10662029 : Blo 2105435 10662029 := bstep (se 3 (by rfl) ⟨1999130, by rfl⟩ : syracuseStep 10662029 = 3998261) B3998261
theorem B7108019 : Blo 2105435 7108019 := bstep (se 1 (by rfl) ⟨5331014, by rfl⟩ : syracuseStep 7108019 = 10662029) B10662029
theorem B4738679 : Blo 2105435 4738679 := bstep (se 1 (by rfl) ⟨3554009, by rfl⟩ : syracuseStep 4738679 = 7108019) B7108019
theorem B3159119 : Blo 2105435 3159119 := bstep (se 1 (by rfl) ⟨2369339, by rfl⟩ : syracuseStep 3159119 = 4738679) B4738679
theorem B2106079 : Blo 2105435 2106079 := bstep (se 1 (by rfl) ⟨1579559, by rfl⟩ : syracuseStep 2106079 = 3159119) B3159119
theorem B3159125 : Blo 2105435 3159125 := bbase (se 8 (by rfl) ⟨18510, by rfl⟩ : syracuseStep 3159125 = 37021) (by norm_num)
theorem B2106083 : Blo 2105435 2106083 := bstep (se 1 (by rfl) ⟨1579562, by rfl⟩ : syracuseStep 2106083 = 3159125) B3159125
theorem B3419573 : Blo 2105435 3419573 := bbase (se 5 (by rfl) ⟨160292, by rfl⟩ : syracuseStep 3419573 = 320585) (by norm_num)
theorem B9118861 : Blo 2105435 9118861 := bstep (se 3 (by rfl) ⟨1709786, by rfl⟩ : syracuseStep 9118861 = 3419573) B3419573
theorem B194535701 : Blo 2105435 194535701 := bstep (se 6 (by rfl) ⟨4559430, by rfl⟩ : syracuseStep 194535701 = 9118861) B9118861
theorem B129690467 : Blo 2105435 129690467 := bstep (se 1 (by rfl) ⟨97267850, by rfl⟩ : syracuseStep 129690467 = 194535701) B194535701
theorem B86460311 : Blo 2105435 86460311 := bstep (se 1 (by rfl) ⟨64845233, by rfl⟩ : syracuseStep 86460311 = 129690467) B129690467
theorem B57640207 : Blo 2105435 57640207 := bstep (se 1 (by rfl) ⟨43230155, by rfl⟩ : syracuseStep 57640207 = 86460311) B86460311
theorem B76853609 : Blo 2105435 76853609 := bstep (se 2 (by rfl) ⟨28820103, by rfl⟩ : syracuseStep 76853609 = 57640207) B57640207
theorem B51235739 : Blo 2105435 51235739 := bstep (se 1 (by rfl) ⟨38426804, by rfl⟩ : syracuseStep 51235739 = 76853609) B76853609
theorem B34157159 : Blo 2105435 34157159 := bstep (se 1 (by rfl) ⟨25617869, by rfl⟩ : syracuseStep 34157159 = 51235739) B51235739
theorem B22771439 : Blo 2105435 22771439 := bstep (se 1 (by rfl) ⟨17078579, by rfl⟩ : syracuseStep 22771439 = 34157159) B34157159
theorem B15180959 : Blo 2105435 15180959 := bstep (se 1 (by rfl) ⟨11385719, by rfl⟩ : syracuseStep 15180959 = 22771439) B22771439
theorem B10120639 : Blo 2105435 10120639 := bstep (se 1 (by rfl) ⟨7590479, by rfl⟩ : syracuseStep 10120639 = 15180959) B15180959
theorem B13494185 : Blo 2105435 13494185 := bstep (se 2 (by rfl) ⟨5060319, by rfl⟩ : syracuseStep 13494185 = 10120639) B10120639
theorem B8996123 : Blo 2105435 8996123 := bstep (se 1 (by rfl) ⟨6747092, by rfl⟩ : syracuseStep 8996123 = 13494185) B13494185
theorem B5997415 : Blo 2105435 5997415 := bstep (se 1 (by rfl) ⟨4498061, by rfl⟩ : syracuseStep 5997415 = 8996123) B8996123
theorem B7996553 : Blo 2105435 7996553 := bstep (se 2 (by rfl) ⟨2998707, by rfl⟩ : syracuseStep 7996553 = 5997415) B5997415
theorem B5331035 : Blo 2105435 5331035 := bstep (se 1 (by rfl) ⟨3998276, by rfl⟩ : syracuseStep 5331035 = 7996553) B7996553
theorem B3554023 : Blo 2105435 3554023 := bstep (se 1 (by rfl) ⟨2665517, by rfl⟩ : syracuseStep 3554023 = 5331035) B5331035
theorem B4738697 : Blo 2105435 4738697 := bstep (se 2 (by rfl) ⟨1777011, by rfl⟩ : syracuseStep 4738697 = 3554023) B3554023
theorem B3159131 : Blo 2105435 3159131 := bstep (se 1 (by rfl) ⟨2369348, by rfl⟩ : syracuseStep 3159131 = 4738697) B4738697
theorem B2106087 : Blo 2105435 2106087 := bstep (se 1 (by rfl) ⟨1579565, by rfl⟩ : syracuseStep 2106087 = 3159131) B3159131
theorem B2369353 : Blo 2105435 2369353 := bbase (se 2 (by rfl) ⟨888507, by rfl⟩ : syracuseStep 2369353 = 1777015) (by norm_num)
theorem B3159137 : Blo 2105435 3159137 := bstep (se 2 (by rfl) ⟨1184676, by rfl⟩ : syracuseStep 3159137 = 2369353) B2369353
theorem B2106091 : Blo 2105435 2106091 := bstep (se 1 (by rfl) ⟨1579568, by rfl⟩ : syracuseStep 2106091 = 3159137) B3159137
theorem B5129381 : Blo 2105435 5129381 := bbase (se 4 (by rfl) ⟨480879, by rfl⟩ : syracuseStep 5129381 = 961759) (by norm_num)
theorem B3419587 : Blo 2105435 3419587 := bstep (se 1 (by rfl) ⟨2564690, by rfl⟩ : syracuseStep 3419587 = 5129381) B5129381
theorem B4559449 : Blo 2105435 4559449 := bstep (se 2 (by rfl) ⟨1709793, by rfl⟩ : syracuseStep 4559449 = 3419587) B3419587
theorem B6079265 : Blo 2105435 6079265 := bstep (se 2 (by rfl) ⟨2279724, by rfl⟩ : syracuseStep 6079265 = 4559449) B4559449
theorem B4052843 : Blo 2105435 4052843 := bstep (se 1 (by rfl) ⟨3039632, by rfl⟩ : syracuseStep 4052843 = 6079265) B6079265
theorem B2701895 : Blo 2105435 2701895 := bstep (se 1 (by rfl) ⟨2026421, by rfl⟩ : syracuseStep 2701895 = 4052843) B4052843
theorem B7205053 : Blo 2105435 7205053 := bstep (se 3 (by rfl) ⟨1350947, by rfl⟩ : syracuseStep 7205053 = 2701895) B2701895
theorem B9606737 : Blo 2105435 9606737 := bstep (se 2 (by rfl) ⟨3602526, by rfl⟩ : syracuseStep 9606737 = 7205053) B7205053
theorem B6404491 : Blo 2105435 6404491 := bstep (se 1 (by rfl) ⟨4803368, by rfl⟩ : syracuseStep 6404491 = 9606737) B9606737
theorem B34157285 : Blo 2105435 34157285 := bstep (se 4 (by rfl) ⟨3202245, by rfl⟩ : syracuseStep 34157285 = 6404491) B6404491
theorem B22771523 : Blo 2105435 22771523 := bstep (se 1 (by rfl) ⟨17078642, by rfl⟩ : syracuseStep 22771523 = 34157285) B34157285
theorem B15181015 : Blo 2105435 15181015 := bstep (se 1 (by rfl) ⟨11385761, by rfl⟩ : syracuseStep 15181015 = 22771523) B22771523
theorem B20241353 : Blo 2105435 20241353 := bstep (se 2 (by rfl) ⟨7590507, by rfl⟩ : syracuseStep 20241353 = 15181015) B15181015
theorem B13494235 : Blo 2105435 13494235 := bstep (se 1 (by rfl) ⟨10120676, by rfl⟩ : syracuseStep 13494235 = 20241353) B20241353
theorem B17992313 : Blo 2105435 17992313 := bstep (se 2 (by rfl) ⟨6747117, by rfl⟩ : syracuseStep 17992313 = 13494235) B13494235
theorem B11994875 : Blo 2105435 11994875 := bstep (se 1 (by rfl) ⟨8996156, by rfl⟩ : syracuseStep 11994875 = 17992313) B17992313
theorem B7996583 : Blo 2105435 7996583 := bstep (se 1 (by rfl) ⟨5997437, by rfl⟩ : syracuseStep 7996583 = 11994875) B11994875
theorem B5331055 : Blo 2105435 5331055 := bstep (se 1 (by rfl) ⟨3998291, by rfl⟩ : syracuseStep 5331055 = 7996583) B7996583
theorem B7108073 : Blo 2105435 7108073 := bstep (se 2 (by rfl) ⟨2665527, by rfl⟩ : syracuseStep 7108073 = 5331055) B5331055
theorem B4738715 : Blo 2105435 4738715 := bstep (se 1 (by rfl) ⟨3554036, by rfl⟩ : syracuseStep 4738715 = 7108073) B7108073
theorem B3159143 : Blo 2105435 3159143 := bstep (se 1 (by rfl) ⟨2369357, by rfl⟩ : syracuseStep 3159143 = 4738715) B4738715
theorem B2106095 : Blo 2105435 2106095 := bstep (se 1 (by rfl) ⟨1579571, by rfl⟩ : syracuseStep 2106095 = 3159143) B3159143
theorem B3159149 : Blo 2105435 3159149 := bbase (se 3 (by rfl) ⟨592340, by rfl⟩ : syracuseStep 3159149 = 1184681) (by norm_num)
theorem B2106099 : Blo 2105435 2106099 := bstep (se 1 (by rfl) ⟨1579574, by rfl⟩ : syracuseStep 2106099 = 3159149) B3159149
theorem B4738733 : Blo 2105435 4738733 := bbase (se 3 (by rfl) ⟨888512, by rfl⟩ : syracuseStep 4738733 = 1777025) (by norm_num)
theorem B3159155 : Blo 2105435 3159155 := bstep (se 1 (by rfl) ⟨2369366, by rfl⟩ : syracuseStep 3159155 = 4738733) B4738733
theorem B2106103 : Blo 2105435 2106103 := bstep (se 1 (by rfl) ⟨1579577, by rfl⟩ : syracuseStep 2106103 = 3159155) B3159155
theorem B3795277 : Blo 2105435 3795277 := bbase (se 3 (by rfl) ⟨711614, by rfl⟩ : syracuseStep 3795277 = 1423229) (by norm_num)
theorem B5060369 : Blo 2105435 5060369 := bstep (se 2 (by rfl) ⟨1897638, by rfl⟩ : syracuseStep 5060369 = 3795277) B3795277
theorem B3373579 : Blo 2105435 3373579 := bstep (se 1 (by rfl) ⟨2530184, by rfl⟩ : syracuseStep 3373579 = 5060369) B5060369
theorem B4498105 : Blo 2105435 4498105 := bstep (se 2 (by rfl) ⟨1686789, by rfl⟩ : syracuseStep 4498105 = 3373579) B3373579
theorem B5997473 : Blo 2105435 5997473 := bstep (se 2 (by rfl) ⟨2249052, by rfl⟩ : syracuseStep 5997473 = 4498105) B4498105
theorem B3998315 : Blo 2105435 3998315 := bstep (se 1 (by rfl) ⟨2998736, by rfl⟩ : syracuseStep 3998315 = 5997473) B5997473
theorem B2665543 : Blo 2105435 2665543 := bstep (se 1 (by rfl) ⟨1999157, by rfl⟩ : syracuseStep 2665543 = 3998315) B3998315
theorem B3554057 : Blo 2105435 3554057 := bstep (se 2 (by rfl) ⟨1332771, by rfl⟩ : syracuseStep 3554057 = 2665543) B2665543
theorem B2369371 : Blo 2105435 2369371 := bstep (se 1 (by rfl) ⟨1777028, by rfl⟩ : syracuseStep 2369371 = 3554057) B3554057
theorem B3159161 : Blo 2105435 3159161 := bstep (se 2 (by rfl) ⟨1184685, by rfl⟩ : syracuseStep 3159161 = 2369371) B2369371
theorem B2106107 : Blo 2105435 2106107 := bstep (se 1 (by rfl) ⟨1579580, by rfl⟩ : syracuseStep 2106107 = 3159161) B3159161
theorem B5770597 : Blo 2105435 5770597 := bbase (se 4 (by rfl) ⟨540993, by rfl⟩ : syracuseStep 5770597 = 1081987) (by norm_num)
theorem B7694129 : Blo 2105435 7694129 := bstep (se 2 (by rfl) ⟨2885298, by rfl⟩ : syracuseStep 7694129 = 5770597) B5770597
theorem B5129419 : Blo 2105435 5129419 := bstep (se 1 (by rfl) ⟨3847064, by rfl⟩ : syracuseStep 5129419 = 7694129) B7694129
theorem B6839225 : Blo 2105435 6839225 := bstep (se 2 (by rfl) ⟨2564709, by rfl⟩ : syracuseStep 6839225 = 5129419) B5129419
theorem B4559483 : Blo 2105435 4559483 := bstep (se 1 (by rfl) ⟨3419612, by rfl⟩ : syracuseStep 4559483 = 6839225) B6839225
theorem B3039655 : Blo 2105435 3039655 := bstep (se 1 (by rfl) ⟨2279741, by rfl⟩ : syracuseStep 3039655 = 4559483) B4559483
theorem B4052873 : Blo 2105435 4052873 := bstep (se 2 (by rfl) ⟨1519827, by rfl⟩ : syracuseStep 4052873 = 3039655) B3039655
theorem B10807661 : Blo 2105435 10807661 := bstep (se 3 (by rfl) ⟨2026436, by rfl⟩ : syracuseStep 10807661 = 4052873) B4052873
theorem B7205107 : Blo 2105435 7205107 := bstep (se 1 (by rfl) ⟨5403830, by rfl⟩ : syracuseStep 7205107 = 10807661) B10807661
theorem B9606809 : Blo 2105435 9606809 := bstep (se 2 (by rfl) ⟨3602553, by rfl⟩ : syracuseStep 9606809 = 7205107) B7205107
theorem B25618157 : Blo 2105435 25618157 := bstep (se 3 (by rfl) ⟨4803404, by rfl⟩ : syracuseStep 25618157 = 9606809) B9606809
theorem B17078771 : Blo 2105435 17078771 := bstep (se 1 (by rfl) ⟨12809078, by rfl⟩ : syracuseStep 17078771 = 25618157) B25618157
theorem B11385847 : Blo 2105435 11385847 := bstep (se 1 (by rfl) ⟨8539385, by rfl⟩ : syracuseStep 11385847 = 17078771) B17078771
theorem B15181129 : Blo 2105435 15181129 := bstep (se 2 (by rfl) ⟨5692923, by rfl⟩ : syracuseStep 15181129 = 11385847) B11385847
theorem B20241505 : Blo 2105435 20241505 := bstep (se 2 (by rfl) ⟨7590564, by rfl⟩ : syracuseStep 20241505 = 15181129) B15181129
theorem B26988673 : Blo 2105435 26988673 := bstep (se 2 (by rfl) ⟨10120752, by rfl⟩ : syracuseStep 26988673 = 20241505) B20241505
theorem B35984897 : Blo 2105435 35984897 := bstep (se 2 (by rfl) ⟨13494336, by rfl⟩ : syracuseStep 35984897 = 26988673) B26988673
theorem B23989931 : Blo 2105435 23989931 := bstep (se 1 (by rfl) ⟨17992448, by rfl⟩ : syracuseStep 23989931 = 35984897) B35984897
theorem B15993287 : Blo 2105435 15993287 := bstep (se 1 (by rfl) ⟨11994965, by rfl⟩ : syracuseStep 15993287 = 23989931) B23989931
theorem B10662191 : Blo 2105435 10662191 := bstep (se 1 (by rfl) ⟨7996643, by rfl⟩ : syracuseStep 10662191 = 15993287) B15993287
theorem B7108127 : Blo 2105435 7108127 := bstep (se 1 (by rfl) ⟨5331095, by rfl⟩ : syracuseStep 7108127 = 10662191) B10662191
theorem B4738751 : Blo 2105435 4738751 := bstep (se 1 (by rfl) ⟨3554063, by rfl⟩ : syracuseStep 4738751 = 7108127) B7108127
theorem B3159167 : Blo 2105435 3159167 := bstep (se 1 (by rfl) ⟨2369375, by rfl⟩ : syracuseStep 3159167 = 4738751) B4738751
theorem B2106111 : Blo 2105435 2106111 := bstep (se 1 (by rfl) ⟨1579583, by rfl⟩ : syracuseStep 2106111 = 3159167) B3159167
theorem B3159173 : Blo 2105435 3159173 := bbase (se 4 (by rfl) ⟨296172, by rfl⟩ : syracuseStep 3159173 = 592345) (by norm_num)
theorem B2106115 : Blo 2105435 2106115 := bstep (se 1 (by rfl) ⟨1579586, by rfl⟩ : syracuseStep 2106115 = 3159173) B3159173
theorem B3554077 : Blo 2105435 3554077 := bbase (se 3 (by rfl) ⟨666389, by rfl⟩ : syracuseStep 3554077 = 1332779) (by norm_num)
theorem B4738769 : Blo 2105435 4738769 := bstep (se 2 (by rfl) ⟨1777038, by rfl⟩ : syracuseStep 4738769 = 3554077) B3554077
theorem B3159179 : Blo 2105435 3159179 := bstep (se 1 (by rfl) ⟨2369384, by rfl⟩ : syracuseStep 3159179 = 4738769) B4738769
theorem B2106119 : Blo 2105435 2106119 := bstep (se 1 (by rfl) ⟨1579589, by rfl⟩ : syracuseStep 2106119 = 3159179) B3159179
theorem B2369389 : Blo 2105435 2369389 := bbase (se 3 (by rfl) ⟨444260, by rfl⟩ : syracuseStep 2369389 = 888521) (by norm_num)
theorem B3159185 : Blo 2105435 3159185 := bstep (se 2 (by rfl) ⟨1184694, by rfl⟩ : syracuseStep 3159185 = 2369389) B2369389
theorem B2106123 : Blo 2105435 2106123 := bstep (se 1 (by rfl) ⟨1579592, by rfl⟩ : syracuseStep 2106123 = 3159185) B3159185
theorem B7108181 : Blo 2105435 7108181 := bbase (se 8 (by rfl) ⟨41649, by rfl⟩ : syracuseStep 7108181 = 83299) (by norm_num)
theorem B4738787 : Blo 2105435 4738787 := bstep (se 1 (by rfl) ⟨3554090, by rfl⟩ : syracuseStep 4738787 = 7108181) B7108181
theorem B3159191 : Blo 2105435 3159191 := bstep (se 1 (by rfl) ⟨2369393, by rfl⟩ : syracuseStep 3159191 = 4738787) B4738787
theorem B2106127 : Blo 2105435 2106127 := bstep (se 1 (by rfl) ⟨1579595, by rfl⟩ : syracuseStep 2106127 = 3159191) B3159191
theorem B3159197 : Blo 2105435 3159197 := bbase (se 3 (by rfl) ⟨592349, by rfl⟩ : syracuseStep 3159197 = 1184699) (by norm_num)
theorem B2106131 : Blo 2105435 2106131 := bstep (se 1 (by rfl) ⟨1579598, by rfl⟩ : syracuseStep 2106131 = 3159197) B3159197
theorem B4738805 : Blo 2105435 4738805 := bbase (se 5 (by rfl) ⟨222131, by rfl⟩ : syracuseStep 4738805 = 444263) (by norm_num)
theorem B3159203 : Blo 2105435 3159203 := bstep (se 1 (by rfl) ⟨2369402, by rfl⟩ : syracuseStep 3159203 = 4738805) B4738805
theorem B2106135 : Blo 2105435 2106135 := bstep (se 1 (by rfl) ⟨1579601, by rfl⟩ : syracuseStep 2106135 = 3159203) B3159203
theorem B2279773 : Blo 2105435 2279773 := bbase (se 3 (by rfl) ⟨427457, by rfl⟩ : syracuseStep 2279773 = 854915) (by norm_num)
theorem B3039697 : Blo 2105435 3039697 := bstep (se 2 (by rfl) ⟨1139886, by rfl⟩ : syracuseStep 3039697 = 2279773) B2279773
theorem B4052929 : Blo 2105435 4052929 := bstep (se 2 (by rfl) ⟨1519848, by rfl⟩ : syracuseStep 4052929 = 3039697) B3039697
theorem B5403905 : Blo 2105435 5403905 := bstep (se 2 (by rfl) ⟨2026464, by rfl⟩ : syracuseStep 5403905 = 4052929) B4052929
theorem B3602603 : Blo 2105435 3602603 := bstep (se 1 (by rfl) ⟨2701952, by rfl⟩ : syracuseStep 3602603 = 5403905) B5403905
theorem B2401735 : Blo 2105435 2401735 := bstep (se 1 (by rfl) ⟨1801301, by rfl⟩ : syracuseStep 2401735 = 3602603) B3602603
theorem B3202313 : Blo 2105435 3202313 := bstep (se 2 (by rfl) ⟨1200867, by rfl⟩ : syracuseStep 3202313 = 2401735) B2401735
theorem B8539501 : Blo 2105435 8539501 := bstep (se 3 (by rfl) ⟨1601156, by rfl⟩ : syracuseStep 8539501 = 3202313) B3202313
theorem B11386001 : Blo 2105435 11386001 := bstep (se 2 (by rfl) ⟨4269750, by rfl⟩ : syracuseStep 11386001 = 8539501) B8539501
theorem B7590667 : Blo 2105435 7590667 := bstep (se 1 (by rfl) ⟨5693000, by rfl⟩ : syracuseStep 7590667 = 11386001) B11386001
theorem B10120889 : Blo 2105435 10120889 := bstep (se 2 (by rfl) ⟨3795333, by rfl⟩ : syracuseStep 10120889 = 7590667) B7590667
theorem B26989037 : Blo 2105435 26989037 := bstep (se 3 (by rfl) ⟨5060444, by rfl⟩ : syracuseStep 26989037 = 10120889) B10120889
theorem B17992691 : Blo 2105435 17992691 := bstep (se 1 (by rfl) ⟨13494518, by rfl⟩ : syracuseStep 17992691 = 26989037) B26989037
theorem B11995127 : Blo 2105435 11995127 := bstep (se 1 (by rfl) ⟨8996345, by rfl⟩ : syracuseStep 11995127 = 17992691) B17992691
theorem B7996751 : Blo 2105435 7996751 := bstep (se 1 (by rfl) ⟨5997563, by rfl⟩ : syracuseStep 7996751 = 11995127) B11995127
theorem B5331167 : Blo 2105435 5331167 := bstep (se 1 (by rfl) ⟨3998375, by rfl⟩ : syracuseStep 5331167 = 7996751) B7996751
theorem B3554111 : Blo 2105435 3554111 := bstep (se 1 (by rfl) ⟨2665583, by rfl⟩ : syracuseStep 3554111 = 5331167) B5331167
theorem B2369407 : Blo 2105435 2369407 := bstep (se 1 (by rfl) ⟨1777055, by rfl⟩ : syracuseStep 2369407 = 3554111) B3554111
theorem B3159209 : Blo 2105435 3159209 := bstep (se 2 (by rfl) ⟨1184703, by rfl⟩ : syracuseStep 3159209 = 2369407) B2369407
theorem B2106139 : Blo 2105435 2106139 := bstep (se 1 (by rfl) ⟨1579604, by rfl⟩ : syracuseStep 2106139 = 3159209) B3159209
theorem B4498181 : Blo 2105435 4498181 := bbase (se 4 (by rfl) ⟨421704, by rfl⟩ : syracuseStep 4498181 = 843409) (by norm_num)
theorem B2998787 : Blo 2105435 2998787 := bstep (se 1 (by rfl) ⟨2249090, by rfl⟩ : syracuseStep 2998787 = 4498181) B4498181
theorem B7996765 : Blo 2105435 7996765 := bstep (se 3 (by rfl) ⟨1499393, by rfl⟩ : syracuseStep 7996765 = 2998787) B2998787
theorem B10662353 : Blo 2105435 10662353 := bstep (se 2 (by rfl) ⟨3998382, by rfl⟩ : syracuseStep 10662353 = 7996765) B7996765
theorem B7108235 : Blo 2105435 7108235 := bstep (se 1 (by rfl) ⟨5331176, by rfl⟩ : syracuseStep 7108235 = 10662353) B10662353
theorem B4738823 : Blo 2105435 4738823 := bstep (se 1 (by rfl) ⟨3554117, by rfl⟩ : syracuseStep 4738823 = 7108235) B7108235
theorem B3159215 : Blo 2105435 3159215 := bstep (se 1 (by rfl) ⟨2369411, by rfl⟩ : syracuseStep 3159215 = 4738823) B4738823
theorem B2106143 : Blo 2105435 2106143 := bstep (se 1 (by rfl) ⟨1579607, by rfl⟩ : syracuseStep 2106143 = 3159215) B3159215
theorem B3159221 : Blo 2105435 3159221 := bbase (se 5 (by rfl) ⟨148088, by rfl⟩ : syracuseStep 3159221 = 296177) (by norm_num)
theorem B2106147 : Blo 2105435 2106147 := bstep (se 1 (by rfl) ⟨1579610, by rfl⟩ : syracuseStep 2106147 = 3159221) B3159221
theorem B5331197 : Blo 2105435 5331197 := bbase (se 3 (by rfl) ⟨999599, by rfl⟩ : syracuseStep 5331197 = 1999199) (by norm_num)
theorem B3554131 : Blo 2105435 3554131 := bstep (se 1 (by rfl) ⟨2665598, by rfl⟩ : syracuseStep 3554131 = 5331197) B5331197
theorem B4738841 : Blo 2105435 4738841 := bstep (se 2 (by rfl) ⟨1777065, by rfl⟩ : syracuseStep 4738841 = 3554131) B3554131
theorem B3159227 : Blo 2105435 3159227 := bstep (se 1 (by rfl) ⟨2369420, by rfl⟩ : syracuseStep 3159227 = 4738841) B4738841
theorem B2106151 : Blo 2105435 2106151 := bstep (se 1 (by rfl) ⟨1579613, by rfl⟩ : syracuseStep 2106151 = 3159227) B3159227
theorem B2369425 : Blo 2105435 2369425 := bbase (se 2 (by rfl) ⟨888534, by rfl⟩ : syracuseStep 2369425 = 1777069) (by norm_num)
theorem B3159233 : Blo 2105435 3159233 := bstep (se 2 (by rfl) ⟨1184712, by rfl⟩ : syracuseStep 3159233 = 2369425) B2369425
theorem B2106155 : Blo 2105435 2106155 := bstep (se 1 (by rfl) ⟨1579616, by rfl⟩ : syracuseStep 2106155 = 3159233) B3159233
theorem B3998413 : Blo 2105435 3998413 := bbase (se 3 (by rfl) ⟨749702, by rfl⟩ : syracuseStep 3998413 = 1499405) (by norm_num)
theorem B5331217 : Blo 2105435 5331217 := bstep (se 2 (by rfl) ⟨1999206, by rfl⟩ : syracuseStep 5331217 = 3998413) B3998413
theorem B7108289 : Blo 2105435 7108289 := bstep (se 2 (by rfl) ⟨2665608, by rfl⟩ : syracuseStep 7108289 = 5331217) B5331217
theorem B4738859 : Blo 2105435 4738859 := bstep (se 1 (by rfl) ⟨3554144, by rfl⟩ : syracuseStep 4738859 = 7108289) B7108289
theorem B3159239 : Blo 2105435 3159239 := bstep (se 1 (by rfl) ⟨2369429, by rfl⟩ : syracuseStep 3159239 = 4738859) B4738859
theorem B2106159 : Blo 2105435 2106159 := bstep (se 1 (by rfl) ⟨1579619, by rfl⟩ : syracuseStep 2106159 = 3159239) B3159239
theorem B3159245 : Blo 2105435 3159245 := bbase (se 3 (by rfl) ⟨592358, by rfl⟩ : syracuseStep 3159245 = 1184717) (by norm_num)
theorem B2106163 : Blo 2105435 2106163 := bstep (se 1 (by rfl) ⟨1579622, by rfl⟩ : syracuseStep 2106163 = 3159245) B3159245
theorem B4738877 : Blo 2105435 4738877 := bbase (se 3 (by rfl) ⟨888539, by rfl⟩ : syracuseStep 4738877 = 1777079) (by norm_num)
theorem B3159251 : Blo 2105435 3159251 := bstep (se 1 (by rfl) ⟨2369438, by rfl⟩ : syracuseStep 3159251 = 4738877) B4738877
theorem B2106167 : Blo 2105435 2106167 := bstep (se 1 (by rfl) ⟨1579625, by rfl⟩ : syracuseStep 2106167 = 3159251) B3159251
theorem B3554165 : Blo 2105435 3554165 := bbase (se 5 (by rfl) ⟨166601, by rfl⟩ : syracuseStep 3554165 = 333203) (by norm_num)
theorem B2369443 : Blo 2105435 2369443 := bstep (se 1 (by rfl) ⟨1777082, by rfl⟩ : syracuseStep 2369443 = 3554165) B3554165
theorem B3159257 : Blo 2105435 3159257 := bstep (se 2 (by rfl) ⟨1184721, by rfl⟩ : syracuseStep 3159257 = 2369443) B2369443
theorem B2106171 : Blo 2105435 2106171 := bstep (se 1 (by rfl) ⟨1579628, by rfl⟩ : syracuseStep 2106171 = 3159257) B3159257
theorem B2846549 : Blo 2105435 2846549 := bbase (se 9 (by rfl) ⟨8339, by rfl⟩ : syracuseStep 2846549 = 16679) (by norm_num)
theorem B7590797 : Blo 2105435 7590797 := bstep (se 3 (by rfl) ⟨1423274, by rfl⟩ : syracuseStep 7590797 = 2846549) B2846549
theorem B5060531 : Blo 2105435 5060531 := bstep (se 1 (by rfl) ⟨3795398, by rfl⟩ : syracuseStep 5060531 = 7590797) B7590797
theorem B3373687 : Blo 2105435 3373687 := bstep (se 1 (by rfl) ⟨2530265, by rfl⟩ : syracuseStep 3373687 = 5060531) B5060531
theorem B4498249 : Blo 2105435 4498249 := bstep (se 2 (by rfl) ⟨1686843, by rfl⟩ : syracuseStep 4498249 = 3373687) B3373687
theorem B5997665 : Blo 2105435 5997665 := bstep (se 2 (by rfl) ⟨2249124, by rfl⟩ : syracuseStep 5997665 = 4498249) B4498249
theorem B15993773 : Blo 2105435 15993773 := bstep (se 3 (by rfl) ⟨2998832, by rfl⟩ : syracuseStep 15993773 = 5997665) B5997665
theorem B10662515 : Blo 2105435 10662515 := bstep (se 1 (by rfl) ⟨7996886, by rfl⟩ : syracuseStep 10662515 = 15993773) B15993773
theorem B7108343 : Blo 2105435 7108343 := bstep (se 1 (by rfl) ⟨5331257, by rfl⟩ : syracuseStep 7108343 = 10662515) B10662515
theorem B4738895 : Blo 2105435 4738895 := bstep (se 1 (by rfl) ⟨3554171, by rfl⟩ : syracuseStep 4738895 = 7108343) B7108343
theorem B3159263 : Blo 2105435 3159263 := bstep (se 1 (by rfl) ⟨2369447, by rfl⟩ : syracuseStep 3159263 = 4738895) B4738895
theorem B2106175 : Blo 2105435 2106175 := bstep (se 1 (by rfl) ⟨1579631, by rfl⟩ : syracuseStep 2106175 = 3159263) B3159263
theorem B3159269 : Blo 2105435 3159269 := bbase (se 4 (by rfl) ⟨296181, by rfl⟩ : syracuseStep 3159269 = 592363) (by norm_num)
theorem B2106179 : Blo 2105435 2106179 := bstep (se 1 (by rfl) ⟨1579634, by rfl⟩ : syracuseStep 2106179 = 3159269) B3159269
theorem B2702009 : Blo 2105435 2702009 := bbase (se 2 (by rfl) ⟨1013253, by rfl⟩ : syracuseStep 2702009 = 2026507) (by norm_num)
theorem B7205357 : Blo 2105435 7205357 := bstep (se 3 (by rfl) ⟨1351004, by rfl⟩ : syracuseStep 7205357 = 2702009) B2702009
theorem B4803571 : Blo 2105435 4803571 := bstep (se 1 (by rfl) ⟨3602678, by rfl⟩ : syracuseStep 4803571 = 7205357) B7205357
theorem B6404761 : Blo 2105435 6404761 := bstep (se 2 (by rfl) ⟨2401785, by rfl⟩ : syracuseStep 6404761 = 4803571) B4803571
theorem B8539681 : Blo 2105435 8539681 := bstep (se 2 (by rfl) ⟨3202380, by rfl⟩ : syracuseStep 8539681 = 6404761) B6404761
theorem B11386241 : Blo 2105435 11386241 := bstep (se 2 (by rfl) ⟨4269840, by rfl⟩ : syracuseStep 11386241 = 8539681) B8539681
theorem B7590827 : Blo 2105435 7590827 := bstep (se 1 (by rfl) ⟨5693120, by rfl⟩ : syracuseStep 7590827 = 11386241) B11386241
theorem B5060551 : Blo 2105435 5060551 := bstep (se 1 (by rfl) ⟨3795413, by rfl⟩ : syracuseStep 5060551 = 7590827) B7590827
theorem B6747401 : Blo 2105435 6747401 := bstep (se 2 (by rfl) ⟨2530275, by rfl⟩ : syracuseStep 6747401 = 5060551) B5060551
theorem B4498267 : Blo 2105435 4498267 := bstep (se 1 (by rfl) ⟨3373700, by rfl⟩ : syracuseStep 4498267 = 6747401) B6747401
theorem B5997689 : Blo 2105435 5997689 := bstep (se 2 (by rfl) ⟨2249133, by rfl⟩ : syracuseStep 5997689 = 4498267) B4498267
theorem B3998459 : Blo 2105435 3998459 := bstep (se 1 (by rfl) ⟨2998844, by rfl⟩ : syracuseStep 3998459 = 5997689) B5997689
theorem B2665639 : Blo 2105435 2665639 := bstep (se 1 (by rfl) ⟨1999229, by rfl⟩ : syracuseStep 2665639 = 3998459) B3998459
theorem B3554185 : Blo 2105435 3554185 := bstep (se 2 (by rfl) ⟨1332819, by rfl⟩ : syracuseStep 3554185 = 2665639) B2665639
theorem B4738913 : Blo 2105435 4738913 := bstep (se 2 (by rfl) ⟨1777092, by rfl⟩ : syracuseStep 4738913 = 3554185) B3554185
theorem B3159275 : Blo 2105435 3159275 := bstep (se 1 (by rfl) ⟨2369456, by rfl⟩ : syracuseStep 3159275 = 4738913) B4738913
theorem B2106183 : Blo 2105435 2106183 := bstep (se 1 (by rfl) ⟨1579637, by rfl⟩ : syracuseStep 2106183 = 3159275) B3159275
theorem B2369461 : Blo 2105435 2369461 := bbase (se 5 (by rfl) ⟨111068, by rfl⟩ : syracuseStep 2369461 = 222137) (by norm_num)
theorem B3159281 : Blo 2105435 3159281 := bstep (se 2 (by rfl) ⟨1184730, by rfl⟩ : syracuseStep 3159281 = 2369461) B2369461
theorem B2106187 : Blo 2105435 2106187 := bstep (se 1 (by rfl) ⟨1579640, by rfl⟩ : syracuseStep 2106187 = 3159281) B3159281
theorem B2665649 : Blo 2105435 2665649 := bbase (se 2 (by rfl) ⟨999618, by rfl⟩ : syracuseStep 2665649 = 1999237) (by norm_num)
theorem B7108397 : Blo 2105435 7108397 := bstep (se 3 (by rfl) ⟨1332824, by rfl⟩ : syracuseStep 7108397 = 2665649) B2665649
theorem B4738931 : Blo 2105435 4738931 := bstep (se 1 (by rfl) ⟨3554198, by rfl⟩ : syracuseStep 4738931 = 7108397) B7108397
theorem B3159287 : Blo 2105435 3159287 := bstep (se 1 (by rfl) ⟨2369465, by rfl⟩ : syracuseStep 3159287 = 4738931) B4738931
theorem B2106191 : Blo 2105435 2106191 := bstep (se 1 (by rfl) ⟨1579643, by rfl⟩ : syracuseStep 2106191 = 3159287) B3159287
theorem B3159293 : Blo 2105435 3159293 := bbase (se 3 (by rfl) ⟨592367, by rfl⟩ : syracuseStep 3159293 = 1184735) (by norm_num)
theorem B2106195 : Blo 2105435 2106195 := bstep (se 1 (by rfl) ⟨1579646, by rfl⟩ : syracuseStep 2106195 = 3159293) B3159293
theorem B4738949 : Blo 2105435 4738949 := bbase (se 4 (by rfl) ⟨444276, by rfl⟩ : syracuseStep 4738949 = 888553) (by norm_num)
theorem B3159299 : Blo 2105435 3159299 := bstep (se 1 (by rfl) ⟨2369474, by rfl⟩ : syracuseStep 3159299 = 4738949) B4738949
theorem B2106199 : Blo 2105435 2106199 := bstep (se 1 (by rfl) ⟨1579649, by rfl⟩ : syracuseStep 2106199 = 3159299) B3159299
theorem B3373733 : Blo 2105435 3373733 := bbase (se 4 (by rfl) ⟨316287, by rfl⟩ : syracuseStep 3373733 = 632575) (by norm_num)
theorem B2249155 : Blo 2105435 2249155 := bstep (se 1 (by rfl) ⟨1686866, by rfl⟩ : syracuseStep 2249155 = 3373733) B3373733
theorem B2998873 : Blo 2105435 2998873 := bstep (se 2 (by rfl) ⟨1124577, by rfl⟩ : syracuseStep 2998873 = 2249155) B2249155
theorem B3998497 : Blo 2105435 3998497 := bstep (se 2 (by rfl) ⟨1499436, by rfl⟩ : syracuseStep 3998497 = 2998873) B2998873
theorem B5331329 : Blo 2105435 5331329 := bstep (se 2 (by rfl) ⟨1999248, by rfl⟩ : syracuseStep 5331329 = 3998497) B3998497
theorem B3554219 : Blo 2105435 3554219 := bstep (se 1 (by rfl) ⟨2665664, by rfl⟩ : syracuseStep 3554219 = 5331329) B5331329
theorem B2369479 : Blo 2105435 2369479 := bstep (se 1 (by rfl) ⟨1777109, by rfl⟩ : syracuseStep 2369479 = 3554219) B3554219
theorem B3159305 : Blo 2105435 3159305 := bstep (se 2 (by rfl) ⟨1184739, by rfl⟩ : syracuseStep 3159305 = 2369479) B2369479
theorem B2106203 : Blo 2105435 2106203 := bstep (se 1 (by rfl) ⟨1579652, by rfl⟩ : syracuseStep 2106203 = 3159305) B3159305
theorem B10662677 : Blo 2105435 10662677 := bbase (se 6 (by rfl) ⟨249906, by rfl⟩ : syracuseStep 10662677 = 499813) (by norm_num)
theorem B7108451 : Blo 2105435 7108451 := bstep (se 1 (by rfl) ⟨5331338, by rfl⟩ : syracuseStep 7108451 = 10662677) B10662677
theorem B4738967 : Blo 2105435 4738967 := bstep (se 1 (by rfl) ⟨3554225, by rfl⟩ : syracuseStep 4738967 = 7108451) B7108451
theorem B3159311 : Blo 2105435 3159311 := bstep (se 1 (by rfl) ⟨2369483, by rfl⟩ : syracuseStep 3159311 = 4738967) B4738967
theorem B2106207 : Blo 2105435 2106207 := bstep (se 1 (by rfl) ⟨1579655, by rfl⟩ : syracuseStep 2106207 = 3159311) B3159311
theorem B3159317 : Blo 2105435 3159317 := bbase (se 6 (by rfl) ⟨74046, by rfl⟩ : syracuseStep 3159317 = 148093) (by norm_num)
theorem B2106211 : Blo 2105435 2106211 := bstep (se 1 (by rfl) ⟨1579658, by rfl⟩ : syracuseStep 2106211 = 3159317) B3159317
theorem B22772821 : Blo 2105435 22772821 := bbase (se 8 (by rfl) ⟨133434, by rfl⟩ : syracuseStep 22772821 = 266869) (by norm_num)
theorem B30363761 : Blo 2105435 30363761 := bstep (se 2 (by rfl) ⟨11386410, by rfl⟩ : syracuseStep 30363761 = 22772821) B22772821
theorem B20242507 : Blo 2105435 20242507 := bstep (se 1 (by rfl) ⟨15181880, by rfl⟩ : syracuseStep 20242507 = 30363761) B30363761
theorem B26990009 : Blo 2105435 26990009 := bstep (se 2 (by rfl) ⟨10121253, by rfl⟩ : syracuseStep 26990009 = 20242507) B20242507
theorem B17993339 : Blo 2105435 17993339 := bstep (se 1 (by rfl) ⟨13495004, by rfl⟩ : syracuseStep 17993339 = 26990009) B26990009
theorem B11995559 : Blo 2105435 11995559 := bstep (se 1 (by rfl) ⟨8996669, by rfl⟩ : syracuseStep 11995559 = 17993339) B17993339
theorem B7997039 : Blo 2105435 7997039 := bstep (se 1 (by rfl) ⟨5997779, by rfl⟩ : syracuseStep 7997039 = 11995559) B11995559
theorem B5331359 : Blo 2105435 5331359 := bstep (se 1 (by rfl) ⟨3998519, by rfl⟩ : syracuseStep 5331359 = 7997039) B7997039
theorem B3554239 : Blo 2105435 3554239 := bstep (se 1 (by rfl) ⟨2665679, by rfl⟩ : syracuseStep 3554239 = 5331359) B5331359
theorem B4738985 : Blo 2105435 4738985 := bstep (se 2 (by rfl) ⟨1777119, by rfl⟩ : syracuseStep 4738985 = 3554239) B3554239
theorem B3159323 : Blo 2105435 3159323 := bstep (se 1 (by rfl) ⟨2369492, by rfl⟩ : syracuseStep 3159323 = 4738985) B4738985
theorem B2106215 : Blo 2105435 2106215 := bstep (se 1 (by rfl) ⟨1579661, by rfl⟩ : syracuseStep 2106215 = 3159323) B3159323
theorem B2369497 : Blo 2105435 2369497 := bbase (se 2 (by rfl) ⟨888561, by rfl⟩ : syracuseStep 2369497 = 1777123) (by norm_num)
theorem B3159329 : Blo 2105435 3159329 := bstep (se 2 (by rfl) ⟨1184748, by rfl⟩ : syracuseStep 3159329 = 2369497) B2369497
theorem B2106219 : Blo 2105435 2106219 := bstep (se 1 (by rfl) ⟨1579664, by rfl⟩ : syracuseStep 2106219 = 3159329) B3159329
theorem B2998901 : Blo 2105435 2998901 := bbase (se 5 (by rfl) ⟨140573, by rfl⟩ : syracuseStep 2998901 = 281147) (by norm_num)
theorem B7997069 : Blo 2105435 7997069 := bstep (se 3 (by rfl) ⟨1499450, by rfl⟩ : syracuseStep 7997069 = 2998901) B2998901
theorem B5331379 : Blo 2105435 5331379 := bstep (se 1 (by rfl) ⟨3998534, by rfl⟩ : syracuseStep 5331379 = 7997069) B7997069
theorem B7108505 : Blo 2105435 7108505 := bstep (se 2 (by rfl) ⟨2665689, by rfl⟩ : syracuseStep 7108505 = 5331379) B5331379
theorem B4739003 : Blo 2105435 4739003 := bstep (se 1 (by rfl) ⟨3554252, by rfl⟩ : syracuseStep 4739003 = 7108505) B7108505
theorem B3159335 : Blo 2105435 3159335 := bstep (se 1 (by rfl) ⟨2369501, by rfl⟩ : syracuseStep 3159335 = 4739003) B4739003
theorem B2106223 : Blo 2105435 2106223 := bstep (se 1 (by rfl) ⟨1579667, by rfl⟩ : syracuseStep 2106223 = 3159335) B3159335
theorem B3159341 : Blo 2105435 3159341 := bbase (se 3 (by rfl) ⟨592376, by rfl⟩ : syracuseStep 3159341 = 1184753) (by norm_num)
theorem B2106227 : Blo 2105435 2106227 := bstep (se 1 (by rfl) ⟨1579670, by rfl⟩ : syracuseStep 2106227 = 3159341) B3159341
theorem B4739021 : Blo 2105435 4739021 := bbase (se 3 (by rfl) ⟨888566, by rfl⟩ : syracuseStep 4739021 = 1777133) (by norm_num)
theorem B3159347 : Blo 2105435 3159347 := bstep (se 1 (by rfl) ⟨2369510, by rfl⟩ : syracuseStep 3159347 = 4739021) B4739021
theorem B2106231 : Blo 2105435 2106231 := bstep (se 1 (by rfl) ⟨1579673, by rfl⟩ : syracuseStep 2106231 = 3159347) B3159347
theorem B2665705 : Blo 2105435 2665705 := bbase (se 2 (by rfl) ⟨999639, by rfl⟩ : syracuseStep 2665705 = 1999279) (by norm_num)
theorem B3554273 : Blo 2105435 3554273 := bstep (se 2 (by rfl) ⟨1332852, by rfl⟩ : syracuseStep 3554273 = 2665705) B2665705
theorem B2369515 : Blo 2105435 2369515 := bstep (se 1 (by rfl) ⟨1777136, by rfl⟩ : syracuseStep 2369515 = 3554273) B3554273
theorem B3159353 : Blo 2105435 3159353 := bstep (se 2 (by rfl) ⟨1184757, by rfl⟩ : syracuseStep 3159353 = 2369515) B2369515
theorem B2106235 : Blo 2105435 2106235 := bstep (se 1 (by rfl) ⟨1579676, by rfl⟩ : syracuseStep 2106235 = 3159353) B3159353
theorem B13495157 : Blo 2105435 13495157 := bbase (se 5 (by rfl) ⟨632585, by rfl⟩ : syracuseStep 13495157 = 1265171) (by norm_num)
theorem B8996771 : Blo 2105435 8996771 := bstep (se 1 (by rfl) ⟨6747578, by rfl⟩ : syracuseStep 8996771 = 13495157) B13495157
theorem B23991389 : Blo 2105435 23991389 := bstep (se 3 (by rfl) ⟨4498385, by rfl⟩ : syracuseStep 23991389 = 8996771) B8996771
theorem B15994259 : Blo 2105435 15994259 := bstep (se 1 (by rfl) ⟨11995694, by rfl⟩ : syracuseStep 15994259 = 23991389) B23991389
theorem B10662839 : Blo 2105435 10662839 := bstep (se 1 (by rfl) ⟨7997129, by rfl⟩ : syracuseStep 10662839 = 15994259) B15994259
theorem B7108559 : Blo 2105435 7108559 := bstep (se 1 (by rfl) ⟨5331419, by rfl⟩ : syracuseStep 7108559 = 10662839) B10662839
theorem B4739039 : Blo 2105435 4739039 := bstep (se 1 (by rfl) ⟨3554279, by rfl⟩ : syracuseStep 4739039 = 7108559) B7108559
theorem B3159359 : Blo 2105435 3159359 := bstep (se 1 (by rfl) ⟨2369519, by rfl⟩ : syracuseStep 3159359 = 4739039) B4739039
theorem B2106239 : Blo 2105435 2106239 := bstep (se 1 (by rfl) ⟨1579679, by rfl⟩ : syracuseStep 2106239 = 3159359) B3159359
theorem B3159365 : Blo 2105435 3159365 := bbase (se 4 (by rfl) ⟨296190, by rfl⟩ : syracuseStep 3159365 = 592381) (by norm_num)
theorem B2106243 : Blo 2105435 2106243 := bstep (se 1 (by rfl) ⟨1579682, by rfl⟩ : syracuseStep 2106243 = 3159365) B3159365
theorem B3554293 : Blo 2105435 3554293 := bbase (se 5 (by rfl) ⟨166607, by rfl⟩ : syracuseStep 3554293 = 333215) (by norm_num)
theorem B4739057 : Blo 2105435 4739057 := bstep (se 2 (by rfl) ⟨1777146, by rfl⟩ : syracuseStep 4739057 = 3554293) B3554293
theorem B3159371 : Blo 2105435 3159371 := bstep (se 1 (by rfl) ⟨2369528, by rfl⟩ : syracuseStep 3159371 = 4739057) B4739057
theorem B2106247 : Blo 2105435 2106247 := bstep (se 1 (by rfl) ⟨1579685, by rfl⟩ : syracuseStep 2106247 = 3159371) B3159371
theorem B2369533 : Blo 2105435 2369533 := bbase (se 3 (by rfl) ⟨444287, by rfl⟩ : syracuseStep 2369533 = 888575) (by norm_num)
theorem B3159377 : Blo 2105435 3159377 := bstep (se 2 (by rfl) ⟨1184766, by rfl⟩ : syracuseStep 3159377 = 2369533) B2369533
theorem B2106251 : Blo 2105435 2106251 := bstep (se 1 (by rfl) ⟨1579688, by rfl⟩ : syracuseStep 2106251 = 3159377) B3159377
theorem B7108613 : Blo 2105435 7108613 := bbase (se 4 (by rfl) ⟨666432, by rfl⟩ : syracuseStep 7108613 = 1332865) (by norm_num)
theorem B4739075 : Blo 2105435 4739075 := bstep (se 1 (by rfl) ⟨3554306, by rfl⟩ : syracuseStep 4739075 = 7108613) B7108613
theorem B3159383 : Blo 2105435 3159383 := bstep (se 1 (by rfl) ⟨2369537, by rfl⟩ : syracuseStep 3159383 = 4739075) B4739075
theorem B2106255 : Blo 2105435 2106255 := bstep (se 1 (by rfl) ⟨1579691, by rfl⟩ : syracuseStep 2106255 = 3159383) B3159383
theorem B3159389 : Blo 2105435 3159389 := bbase (se 3 (by rfl) ⟨592385, by rfl⟩ : syracuseStep 3159389 = 1184771) (by norm_num)
theorem B2106259 : Blo 2105435 2106259 := bstep (se 1 (by rfl) ⟨1579694, by rfl⟩ : syracuseStep 2106259 = 3159389) B3159389
theorem B4739093 : Blo 2105435 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B3159395 : Blo 2105435 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B2106263 : Blo 2105435 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B7997237 : Blo 2105435 7997237 := bbase (se 5 (by rfl) ⟨374870, by rfl⟩ : syracuseStep 7997237 = 749741) (by norm_num)
theorem B5331491 : Blo 2105435 5331491 := bstep (se 1 (by rfl) ⟨3998618, by rfl⟩ : syracuseStep 5331491 = 7997237) B7997237
theorem B3554327 : Blo 2105435 3554327 := bstep (se 1 (by rfl) ⟨2665745, by rfl⟩ : syracuseStep 3554327 = 5331491) B5331491
theorem B2369551 : Blo 2105435 2369551 := bstep (se 1 (by rfl) ⟨1777163, by rfl⟩ : syracuseStep 2369551 = 3554327) B3554327
theorem B3159401 : Blo 2105435 3159401 := bstep (se 2 (by rfl) ⟨1184775, by rfl⟩ : syracuseStep 3159401 = 2369551) B2369551
theorem B2106267 : Blo 2105435 2106267 := bstep (se 1 (by rfl) ⟨1579700, by rfl⟩ : syracuseStep 2106267 = 3159401) B3159401
theorem B2530381 : Blo 2105435 2530381 := bbase (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) (by norm_num)
theorem B3373841 : Blo 2105435 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B2249227 : Blo 2105435 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B11995877 : Blo 2105435 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B7997251 : Blo 2105435 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B10663001 : Blo 2105435 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B7108667 : Blo 2105435 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B4739111 : Blo 2105435 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B3159407 : Blo 2105435 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B2106271 : Blo 2105435 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B3159413 : Blo 2105435 3159413 := bbase (se 5 (by rfl) ⟨148097, by rfl⟩ : syracuseStep 3159413 = 296195) (by norm_num)
theorem B2106275 : Blo 2105435 2106275 := bstep (se 1 (by rfl) ⟨1579706, by rfl⟩ : syracuseStep 2106275 = 3159413) B3159413
theorem B2998981 : Blo 2105435 2998981 := bbase (se 4 (by rfl) ⟨281154, by rfl⟩ : syracuseStep 2998981 = 562309) (by norm_num)
theorem B3998641 : Blo 2105435 3998641 := bstep (se 2 (by rfl) ⟨1499490, by rfl⟩ : syracuseStep 3998641 = 2998981) B2998981
theorem B5331521 : Blo 2105435 5331521 := bstep (se 2 (by rfl) ⟨1999320, by rfl⟩ : syracuseStep 5331521 = 3998641) B3998641
theorem B3554347 : Blo 2105435 3554347 := bstep (se 1 (by rfl) ⟨2665760, by rfl⟩ : syracuseStep 3554347 = 5331521) B5331521
theorem B4739129 : Blo 2105435 4739129 := bstep (se 2 (by rfl) ⟨1777173, by rfl⟩ : syracuseStep 4739129 = 3554347) B3554347
theorem B3159419 : Blo 2105435 3159419 := bstep (se 1 (by rfl) ⟨2369564, by rfl⟩ : syracuseStep 3159419 = 4739129) B4739129
theorem B2106279 : Blo 2105435 2106279 := bstep (se 1 (by rfl) ⟨1579709, by rfl⟩ : syracuseStep 2106279 = 3159419) B3159419
theorem B2369569 : Blo 2105435 2369569 := bbase (se 2 (by rfl) ⟨888588, by rfl⟩ : syracuseStep 2369569 = 1777177) (by norm_num)
theorem B3159425 : Blo 2105435 3159425 := bstep (se 2 (by rfl) ⟨1184784, by rfl⟩ : syracuseStep 3159425 = 2369569) B2369569
theorem B2106283 : Blo 2105435 2106283 := bstep (se 1 (by rfl) ⟨1579712, by rfl⟩ : syracuseStep 2106283 = 3159425) B3159425
theorem B5331541 : Blo 2105435 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B7108721 : Blo 2105435 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B4739147 : Blo 2105435 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B3159431 : Blo 2105435 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B2106287 : Blo 2105435 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B3159437 : Blo 2105435 3159437 := bbase (se 3 (by rfl) ⟨592394, by rfl⟩ : syracuseStep 3159437 = 1184789) (by norm_num)
theorem B2106291 : Blo 2105435 2106291 := bstep (se 1 (by rfl) ⟨1579718, by rfl⟩ : syracuseStep 2106291 = 3159437) B3159437
theorem B4739165 : Blo 2105435 4739165 := bbase (se 3 (by rfl) ⟨888593, by rfl⟩ : syracuseStep 4739165 = 1777187) (by norm_num)
theorem B3159443 : Blo 2105435 3159443 := bstep (se 1 (by rfl) ⟨2369582, by rfl⟩ : syracuseStep 3159443 = 4739165) B4739165
theorem B2106295 : Blo 2105435 2106295 := bstep (se 1 (by rfl) ⟨1579721, by rfl⟩ : syracuseStep 2106295 = 3159443) B3159443
theorem B3554381 : Blo 2105435 3554381 := bbase (se 3 (by rfl) ⟨666446, by rfl⟩ : syracuseStep 3554381 = 1332893) (by norm_num)
theorem B2369587 : Blo 2105435 2369587 := bstep (se 1 (by rfl) ⟨1777190, by rfl⟩ : syracuseStep 2369587 = 3554381) B3554381
theorem B3159449 : Blo 2105435 3159449 := bstep (se 2 (by rfl) ⟨1184793, by rfl⟩ : syracuseStep 3159449 = 2369587) B2369587
theorem B2106299 : Blo 2105435 2106299 := bstep (se 1 (by rfl) ⟨1579724, by rfl⟩ : syracuseStep 2106299 = 3159449) B3159449
theorem B2135041 : Blo 2105435 2135041 := bbase (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) (by norm_num)
theorem B45547541 : Blo 2105435 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B30365027 : Blo 2105435 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B20243351 : Blo 2105435 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B13495567 : Blo 2105435 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B17994089 : Blo 2105435 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B11996059 : Blo 2105435 11996059 := bstep (se 1 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 11996059 = 17994089) B17994089
theorem B15994745 : Blo 2105435 15994745 := bstep (se 2 (by rfl) ⟨5998029, by rfl⟩ : syracuseStep 15994745 = 11996059) B11996059
theorem B10663163 : Blo 2105435 10663163 := bstep (se 1 (by rfl) ⟨7997372, by rfl⟩ : syracuseStep 10663163 = 15994745) B15994745
theorem B7108775 : Blo 2105435 7108775 := bstep (se 1 (by rfl) ⟨5331581, by rfl⟩ : syracuseStep 7108775 = 10663163) B10663163
theorem B4739183 : Blo 2105435 4739183 := bstep (se 1 (by rfl) ⟨3554387, by rfl⟩ : syracuseStep 4739183 = 7108775) B7108775
theorem B3159455 : Blo 2105435 3159455 := bstep (se 1 (by rfl) ⟨2369591, by rfl⟩ : syracuseStep 3159455 = 4739183) B4739183
theorem B2106303 : Blo 2105435 2106303 := bstep (se 1 (by rfl) ⟨1579727, by rfl⟩ : syracuseStep 2106303 = 3159455) B3159455
theorem B3159461 : Blo 2105435 3159461 := bbase (se 4 (by rfl) ⟨296199, by rfl⟩ : syracuseStep 3159461 = 592399) (by norm_num)
theorem B2106307 : Blo 2105435 2106307 := bstep (se 1 (by rfl) ⟨1579730, by rfl⟩ : syracuseStep 2106307 = 3159461) B3159461
theorem B2665801 : Blo 2105435 2665801 := bbase (se 2 (by rfl) ⟨999675, by rfl⟩ : syracuseStep 2665801 = 1999351) (by norm_num)
theorem B3554401 : Blo 2105435 3554401 := bstep (se 2 (by rfl) ⟨1332900, by rfl⟩ : syracuseStep 3554401 = 2665801) B2665801
theorem B4739201 : Blo 2105435 4739201 := bstep (se 2 (by rfl) ⟨1777200, by rfl⟩ : syracuseStep 4739201 = 3554401) B3554401
theorem B3159467 : Blo 2105435 3159467 := bstep (se 1 (by rfl) ⟨2369600, by rfl⟩ : syracuseStep 3159467 = 4739201) B4739201
theorem B2106311 : Blo 2105435 2106311 := bstep (se 1 (by rfl) ⟨1579733, by rfl⟩ : syracuseStep 2106311 = 3159467) B3159467
theorem B2369605 : Blo 2105435 2369605 := bbase (se 4 (by rfl) ⟨222150, by rfl⟩ : syracuseStep 2369605 = 444301) (by norm_num)
theorem B3159473 : Blo 2105435 3159473 := bstep (se 2 (by rfl) ⟨1184802, by rfl⟩ : syracuseStep 3159473 = 2369605) B2369605
theorem B2106315 : Blo 2105435 2106315 := bstep (se 1 (by rfl) ⟨1579736, by rfl⟩ : syracuseStep 2106315 = 3159473) B3159473
theorem B3998717 : Blo 2105435 3998717 := bbase (se 3 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 3998717 = 1499519) (by norm_num)
theorem B2665811 : Blo 2105435 2665811 := bstep (se 1 (by rfl) ⟨1999358, by rfl⟩ : syracuseStep 2665811 = 3998717) B3998717
theorem B7108829 : Blo 2105435 7108829 := bstep (se 3 (by rfl) ⟨1332905, by rfl⟩ : syracuseStep 7108829 = 2665811) B2665811
theorem B4739219 : Blo 2105435 4739219 := bstep (se 1 (by rfl) ⟨3554414, by rfl⟩ : syracuseStep 4739219 = 7108829) B7108829
theorem B3159479 : Blo 2105435 3159479 := bstep (se 1 (by rfl) ⟨2369609, by rfl⟩ : syracuseStep 3159479 = 4739219) B4739219
theorem B2106319 : Blo 2105435 2106319 := bstep (se 1 (by rfl) ⟨1579739, by rfl⟩ : syracuseStep 2106319 = 3159479) B3159479
theorem B3159485 : Blo 2105435 3159485 := bbase (se 3 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 3159485 = 1184807) (by norm_num)
theorem B2106323 : Blo 2105435 2106323 := bstep (se 1 (by rfl) ⟨1579742, by rfl⟩ : syracuseStep 2106323 = 3159485) B3159485
theorem B4739237 : Blo 2105435 4739237 := bbase (se 4 (by rfl) ⟨444303, by rfl⟩ : syracuseStep 4739237 = 888607) (by norm_num)
theorem B3159491 : Blo 2105435 3159491 := bstep (se 1 (by rfl) ⟨2369618, by rfl⟩ : syracuseStep 3159491 = 4739237) B4739237
theorem B2106327 : Blo 2105435 2106327 := bstep (se 1 (by rfl) ⟨1579745, by rfl⟩ : syracuseStep 2106327 = 3159491) B3159491
theorem B5331653 : Blo 2105435 5331653 := bbase (se 4 (by rfl) ⟨499842, by rfl⟩ : syracuseStep 5331653 = 999685) (by norm_num)
theorem B3554435 : Blo 2105435 3554435 := bstep (se 1 (by rfl) ⟨2665826, by rfl⟩ : syracuseStep 3554435 = 5331653) B5331653
theorem B2369623 : Blo 2105435 2369623 := bstep (se 1 (by rfl) ⟨1777217, by rfl⟩ : syracuseStep 2369623 = 3554435) B3554435
theorem B3159497 : Blo 2105435 3159497 := bstep (se 2 (by rfl) ⟨1184811, by rfl⟩ : syracuseStep 3159497 = 2369623) B2369623
theorem B2106331 : Blo 2105435 2106331 := bstep (se 1 (by rfl) ⟨1579748, by rfl⟩ : syracuseStep 2106331 = 3159497) B3159497
theorem B2164205 : Blo 2105435 2164205 := bbase (se 3 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 2164205 = 811577) (by norm_num)
theorem B5771213 : Blo 2105435 5771213 := bstep (se 3 (by rfl) ⟨1082102, by rfl⟩ : syracuseStep 5771213 = 2164205) B2164205
theorem B3847475 : Blo 2105435 3847475 := bstep (se 1 (by rfl) ⟨2885606, by rfl⟩ : syracuseStep 3847475 = 5771213) B5771213
theorem B2564983 : Blo 2105435 2564983 := bstep (se 1 (by rfl) ⟨1923737, by rfl⟩ : syracuseStep 2564983 = 3847475) B3847475
theorem B3419977 : Blo 2105435 3419977 := bstep (se 2 (by rfl) ⟨1282491, by rfl⟩ : syracuseStep 3419977 = 2564983) B2564983
theorem B4559969 : Blo 2105435 4559969 := bstep (se 2 (by rfl) ⟨1709988, by rfl⟩ : syracuseStep 4559969 = 3419977) B3419977
theorem B3039979 : Blo 2105435 3039979 := bstep (se 1 (by rfl) ⟨2279984, by rfl⟩ : syracuseStep 3039979 = 4559969) B4559969
theorem B4053305 : Blo 2105435 4053305 := bstep (se 2 (by rfl) ⟨1519989, by rfl⟩ : syracuseStep 4053305 = 3039979) B3039979
theorem B2702203 : Blo 2105435 2702203 := bstep (se 1 (by rfl) ⟨2026652, by rfl⟩ : syracuseStep 2702203 = 4053305) B4053305
theorem B57646997 : Blo 2105435 57646997 := bstep (se 6 (by rfl) ⟨1351101, by rfl⟩ : syracuseStep 57646997 = 2702203) B2702203
theorem B38431331 : Blo 2105435 38431331 := bstep (se 1 (by rfl) ⟨28823498, by rfl⟩ : syracuseStep 38431331 = 57646997) B57646997
theorem B25620887 : Blo 2105435 25620887 := bstep (se 1 (by rfl) ⟨19215665, by rfl⟩ : syracuseStep 25620887 = 38431331) B38431331
theorem B17080591 : Blo 2105435 17080591 := bstep (se 1 (by rfl) ⟨12810443, by rfl⟩ : syracuseStep 17080591 = 25620887) B25620887
theorem B22774121 : Blo 2105435 22774121 := bstep (se 2 (by rfl) ⟨8540295, by rfl⟩ : syracuseStep 22774121 = 17080591) B17080591
theorem B15182747 : Blo 2105435 15182747 := bstep (se 1 (by rfl) ⟨11387060, by rfl⟩ : syracuseStep 15182747 = 22774121) B22774121
theorem B10121831 : Blo 2105435 10121831 := bstep (se 1 (by rfl) ⟨7591373, by rfl⟩ : syracuseStep 10121831 = 15182747) B15182747
theorem B6747887 : Blo 2105435 6747887 := bstep (se 1 (by rfl) ⟨5060915, by rfl⟩ : syracuseStep 6747887 = 10121831) B10121831
theorem B4498591 : Blo 2105435 4498591 := bstep (se 1 (by rfl) ⟨3373943, by rfl⟩ : syracuseStep 4498591 = 6747887) B6747887
theorem B5998121 : Blo 2105435 5998121 := bstep (se 2 (by rfl) ⟨2249295, by rfl⟩ : syracuseStep 5998121 = 4498591) B4498591
theorem B3998747 : Blo 2105435 3998747 := bstep (se 1 (by rfl) ⟨2999060, by rfl⟩ : syracuseStep 3998747 = 5998121) B5998121
theorem B10663325 : Blo 2105435 10663325 := bstep (se 3 (by rfl) ⟨1999373, by rfl⟩ : syracuseStep 10663325 = 3998747) B3998747
theorem B7108883 : Blo 2105435 7108883 := bstep (se 1 (by rfl) ⟨5331662, by rfl⟩ : syracuseStep 7108883 = 10663325) B10663325
theorem B4739255 : Blo 2105435 4739255 := bstep (se 1 (by rfl) ⟨3554441, by rfl⟩ : syracuseStep 4739255 = 7108883) B7108883
theorem B3159503 : Blo 2105435 3159503 := bstep (se 1 (by rfl) ⟨2369627, by rfl⟩ : syracuseStep 3159503 = 4739255) B4739255
theorem B2106335 : Blo 2105435 2106335 := bstep (se 1 (by rfl) ⟨1579751, by rfl⟩ : syracuseStep 2106335 = 3159503) B3159503
theorem B3159509 : Blo 2105435 3159509 := bbase (se 7 (by rfl) ⟨37025, by rfl⟩ : syracuseStep 3159509 = 74051) (by norm_num)
theorem B2106339 : Blo 2105435 2106339 := bstep (se 1 (by rfl) ⟨1579754, by rfl⟩ : syracuseStep 2106339 = 3159509) B3159509
theorem B7997525 : Blo 2105435 7997525 := bbase (se 8 (by rfl) ⟨46860, by rfl⟩ : syracuseStep 7997525 = 93721) (by norm_num)
theorem B5331683 : Blo 2105435 5331683 := bstep (se 1 (by rfl) ⟨3998762, by rfl⟩ : syracuseStep 5331683 = 7997525) B7997525
theorem B3554455 : Blo 2105435 3554455 := bstep (se 1 (by rfl) ⟨2665841, by rfl⟩ : syracuseStep 3554455 = 5331683) B5331683
theorem B4739273 : Blo 2105435 4739273 := bstep (se 2 (by rfl) ⟨1777227, by rfl⟩ : syracuseStep 4739273 = 3554455) B3554455
theorem B3159515 : Blo 2105435 3159515 := bstep (se 1 (by rfl) ⟨2369636, by rfl⟩ : syracuseStep 3159515 = 4739273) B4739273
theorem B2106343 : Blo 2105435 2106343 := bstep (se 1 (by rfl) ⟨1579757, by rfl⟩ : syracuseStep 2106343 = 3159515) B3159515
theorem B2369641 : Blo 2105435 2369641 := bbase (se 2 (by rfl) ⟨888615, by rfl⟩ : syracuseStep 2369641 = 1777231) (by norm_num)
theorem B3159521 : Blo 2105435 3159521 := bstep (se 2 (by rfl) ⟨1184820, by rfl⟩ : syracuseStep 3159521 = 2369641) B2369641
theorem B2106347 : Blo 2105435 2106347 := bstep (se 1 (by rfl) ⟨1579760, by rfl⟩ : syracuseStep 2106347 = 3159521) B3159521
theorem B2530477 : Blo 2105435 2530477 := bbase (se 3 (by rfl) ⟨474464, by rfl⟩ : syracuseStep 2530477 = 948929) (by norm_num)
theorem B3373969 : Blo 2105435 3373969 := bstep (se 2 (by rfl) ⟨1265238, by rfl⟩ : syracuseStep 3373969 = 2530477) B2530477
theorem B4498625 : Blo 2105435 4498625 := bstep (se 2 (by rfl) ⟨1686984, by rfl⟩ : syracuseStep 4498625 = 3373969) B3373969
theorem B11996333 : Blo 2105435 11996333 := bstep (se 3 (by rfl) ⟨2249312, by rfl⟩ : syracuseStep 11996333 = 4498625) B4498625
theorem B7997555 : Blo 2105435 7997555 := bstep (se 1 (by rfl) ⟨5998166, by rfl⟩ : syracuseStep 7997555 = 11996333) B11996333
theorem B5331703 : Blo 2105435 5331703 := bstep (se 1 (by rfl) ⟨3998777, by rfl⟩ : syracuseStep 5331703 = 7997555) B7997555
theorem B7108937 : Blo 2105435 7108937 := bstep (se 2 (by rfl) ⟨2665851, by rfl⟩ : syracuseStep 7108937 = 5331703) B5331703
theorem B4739291 : Blo 2105435 4739291 := bstep (se 1 (by rfl) ⟨3554468, by rfl⟩ : syracuseStep 4739291 = 7108937) B7108937
theorem B3159527 : Blo 2105435 3159527 := bstep (se 1 (by rfl) ⟨2369645, by rfl⟩ : syracuseStep 3159527 = 4739291) B4739291
theorem B2106351 : Blo 2105435 2106351 := bstep (se 1 (by rfl) ⟨1579763, by rfl⟩ : syracuseStep 2106351 = 3159527) B3159527
theorem B3159533 : Blo 2105435 3159533 := bbase (se 3 (by rfl) ⟨592412, by rfl⟩ : syracuseStep 3159533 = 1184825) (by norm_num)
theorem B2106355 : Blo 2105435 2106355 := bstep (se 1 (by rfl) ⟨1579766, by rfl⟩ : syracuseStep 2106355 = 3159533) B3159533
theorem B4739309 : Blo 2105435 4739309 := bbase (se 3 (by rfl) ⟨888620, by rfl⟩ : syracuseStep 4739309 = 1777241) (by norm_num)
theorem B3159539 : Blo 2105435 3159539 := bstep (se 1 (by rfl) ⟨2369654, by rfl⟩ : syracuseStep 3159539 = 4739309) B4739309
theorem B2106359 : Blo 2105435 2106359 := bstep (se 1 (by rfl) ⟨1579769, by rfl⟩ : syracuseStep 2106359 = 3159539) B3159539
theorem B2999101 : Blo 2105435 2999101 := bbase (se 3 (by rfl) ⟨562331, by rfl⟩ : syracuseStep 2999101 = 1124663) (by norm_num)
theorem B3998801 : Blo 2105435 3998801 := bstep (se 2 (by rfl) ⟨1499550, by rfl⟩ : syracuseStep 3998801 = 2999101) B2999101
theorem B2665867 : Blo 2105435 2665867 := bstep (se 1 (by rfl) ⟨1999400, by rfl⟩ : syracuseStep 2665867 = 3998801) B3998801
theorem B3554489 : Blo 2105435 3554489 := bstep (se 2 (by rfl) ⟨1332933, by rfl⟩ : syracuseStep 3554489 = 2665867) B2665867
theorem B2369659 : Blo 2105435 2369659 := bstep (se 1 (by rfl) ⟨1777244, by rfl⟩ : syracuseStep 2369659 = 3554489) B3554489
theorem B3159545 : Blo 2105435 3159545 := bstep (se 2 (by rfl) ⟨1184829, by rfl⟩ : syracuseStep 3159545 = 2369659) B2369659
theorem B2106363 : Blo 2105435 2106363 := bstep (se 1 (by rfl) ⟨1579772, by rfl⟩ : syracuseStep 2106363 = 3159545) B3159545
theorem B4869533 : Blo 2105435 4869533 := bbase (se 3 (by rfl) ⟨913037, by rfl⟩ : syracuseStep 4869533 = 1826075) (by norm_num)
theorem B3246355 : Blo 2105435 3246355 := bstep (se 1 (by rfl) ⟨2434766, by rfl⟩ : syracuseStep 3246355 = 4869533) B4869533
theorem B4328473 : Blo 2105435 4328473 := bstep (se 2 (by rfl) ⟨1623177, by rfl⟩ : syracuseStep 4328473 = 3246355) B3246355
theorem B5771297 : Blo 2105435 5771297 := bstep (se 2 (by rfl) ⟨2164236, by rfl⟩ : syracuseStep 5771297 = 4328473) B4328473
theorem B15390125 : Blo 2105435 15390125 := bstep (se 3 (by rfl) ⟨2885648, by rfl⟩ : syracuseStep 15390125 = 5771297) B5771297
theorem B10260083 : Blo 2105435 10260083 := bstep (se 1 (by rfl) ⟨7695062, by rfl⟩ : syracuseStep 10260083 = 15390125) B15390125
theorem B6840055 : Blo 2105435 6840055 := bstep (se 1 (by rfl) ⟨5130041, by rfl⟩ : syracuseStep 6840055 = 10260083) B10260083
theorem B9120073 : Blo 2105435 9120073 := bstep (se 2 (by rfl) ⟨3420027, by rfl⟩ : syracuseStep 9120073 = 6840055) B6840055
theorem B12160097 : Blo 2105435 12160097 := bstep (se 2 (by rfl) ⟨4560036, by rfl⟩ : syracuseStep 12160097 = 9120073) B9120073
theorem B8106731 : Blo 2105435 8106731 := bstep (se 1 (by rfl) ⟨6080048, by rfl⟩ : syracuseStep 8106731 = 12160097) B12160097
theorem B5404487 : Blo 2105435 5404487 := bstep (se 1 (by rfl) ⟨4053365, by rfl⟩ : syracuseStep 5404487 = 8106731) B8106731
theorem B57647861 : Blo 2105435 57647861 := bstep (se 5 (by rfl) ⟨2702243, by rfl⟩ : syracuseStep 57647861 = 5404487) B5404487
theorem B38431907 : Blo 2105435 38431907 := bstep (se 1 (by rfl) ⟨28823930, by rfl⟩ : syracuseStep 38431907 = 57647861) B57647861
theorem B25621271 : Blo 2105435 25621271 := bstep (se 1 (by rfl) ⟨19215953, by rfl⟩ : syracuseStep 25621271 = 38431907) B38431907
theorem B17080847 : Blo 2105435 17080847 := bstep (se 1 (by rfl) ⟨12810635, by rfl⟩ : syracuseStep 17080847 = 25621271) B25621271
theorem B11387231 : Blo 2105435 11387231 := bstep (se 1 (by rfl) ⟨8540423, by rfl⟩ : syracuseStep 11387231 = 17080847) B17080847
theorem B7591487 : Blo 2105435 7591487 := bstep (se 1 (by rfl) ⟨5693615, by rfl⟩ : syracuseStep 7591487 = 11387231) B11387231
theorem B80975861 : Blo 2105435 80975861 := bstep (se 5 (by rfl) ⟨3795743, by rfl⟩ : syracuseStep 80975861 = 7591487) B7591487
theorem B53983907 : Blo 2105435 53983907 := bstep (se 1 (by rfl) ⟨40487930, by rfl⟩ : syracuseStep 53983907 = 80975861) B80975861
theorem B35989271 : Blo 2105435 35989271 := bstep (se 1 (by rfl) ⟨26991953, by rfl⟩ : syracuseStep 35989271 = 53983907) B53983907
theorem B23992847 : Blo 2105435 23992847 := bstep (se 1 (by rfl) ⟨17994635, by rfl⟩ : syracuseStep 23992847 = 35989271) B35989271
theorem B15995231 : Blo 2105435 15995231 := bstep (se 1 (by rfl) ⟨11996423, by rfl⟩ : syracuseStep 15995231 = 23992847) B23992847
theorem B10663487 : Blo 2105435 10663487 := bstep (se 1 (by rfl) ⟨7997615, by rfl⟩ : syracuseStep 10663487 = 15995231) B15995231
theorem B7108991 : Blo 2105435 7108991 := bstep (se 1 (by rfl) ⟨5331743, by rfl⟩ : syracuseStep 7108991 = 10663487) B10663487
theorem B4739327 : Blo 2105435 4739327 := bstep (se 1 (by rfl) ⟨3554495, by rfl⟩ : syracuseStep 4739327 = 7108991) B7108991
theorem B3159551 : Blo 2105435 3159551 := bstep (se 1 (by rfl) ⟨2369663, by rfl⟩ : syracuseStep 3159551 = 4739327) B4739327
theorem B2106367 : Blo 2105435 2106367 := bstep (se 1 (by rfl) ⟨1579775, by rfl⟩ : syracuseStep 2106367 = 3159551) B3159551
theorem B3159557 : Blo 2105435 3159557 := bbase (se 4 (by rfl) ⟨296208, by rfl⟩ : syracuseStep 3159557 = 592417) (by norm_num)
theorem B2106371 : Blo 2105435 2106371 := bstep (se 1 (by rfl) ⟨1579778, by rfl⟩ : syracuseStep 2106371 = 3159557) B3159557
theorem B3554509 : Blo 2105435 3554509 := bbase (se 3 (by rfl) ⟨666470, by rfl⟩ : syracuseStep 3554509 = 1332941) (by norm_num)
theorem B4739345 : Blo 2105435 4739345 := bstep (se 2 (by rfl) ⟨1777254, by rfl⟩ : syracuseStep 4739345 = 3554509) B3554509
theorem B3159563 : Blo 2105435 3159563 := bstep (se 1 (by rfl) ⟨2369672, by rfl⟩ : syracuseStep 3159563 = 4739345) B4739345
theorem B2106375 : Blo 2105435 2106375 := bstep (se 1 (by rfl) ⟨1579781, by rfl⟩ : syracuseStep 2106375 = 3159563) B3159563
theorem B2369677 : Blo 2105435 2369677 := bbase (se 3 (by rfl) ⟨444314, by rfl⟩ : syracuseStep 2369677 = 888629) (by norm_num)
theorem B3159569 : Blo 2105435 3159569 := bstep (se 2 (by rfl) ⟨1184838, by rfl⟩ : syracuseStep 3159569 = 2369677) B2369677
theorem B2106379 : Blo 2105435 2106379 := bstep (se 1 (by rfl) ⟨1579784, by rfl⟩ : syracuseStep 2106379 = 3159569) B3159569
theorem B7109045 : Blo 2105435 7109045 := bbase (se 5 (by rfl) ⟨333236, by rfl⟩ : syracuseStep 7109045 = 666473) (by norm_num)
theorem B4739363 : Blo 2105435 4739363 := bstep (se 1 (by rfl) ⟨3554522, by rfl⟩ : syracuseStep 4739363 = 7109045) B7109045
theorem B3159575 : Blo 2105435 3159575 := bstep (se 1 (by rfl) ⟨2369681, by rfl⟩ : syracuseStep 3159575 = 4739363) B4739363
theorem B2106383 : Blo 2105435 2106383 := bstep (se 1 (by rfl) ⟨1579787, by rfl⟩ : syracuseStep 2106383 = 3159575) B3159575
theorem B3159581 : Blo 2105435 3159581 := bbase (se 3 (by rfl) ⟨592421, by rfl⟩ : syracuseStep 3159581 = 1184843) (by norm_num)
theorem B2106387 : Blo 2105435 2106387 := bstep (se 1 (by rfl) ⟨1579790, by rfl⟩ : syracuseStep 2106387 = 3159581) B3159581
theorem B4739381 : Blo 2105435 4739381 := bbase (se 5 (by rfl) ⟨222158, by rfl⟩ : syracuseStep 4739381 = 444317) (by norm_num)
theorem B3159587 : Blo 2105435 3159587 := bstep (se 1 (by rfl) ⟨2369690, by rfl⟩ : syracuseStep 3159587 = 4739381) B4739381
theorem B2106391 : Blo 2105435 2106391 := bstep (se 1 (by rfl) ⟨1579793, by rfl⟩ : syracuseStep 2106391 = 3159587) B3159587
theorem B68324309 : Blo 2105435 68324309 := bbase (se 7 (by rfl) ⟨800675, by rfl⟩ : syracuseStep 68324309 = 1601351) (by norm_num)
theorem B45549539 : Blo 2105435 45549539 := bstep (se 1 (by rfl) ⟨34162154, by rfl⟩ : syracuseStep 45549539 = 68324309) B68324309
theorem B30366359 : Blo 2105435 30366359 := bstep (se 1 (by rfl) ⟨22774769, by rfl⟩ : syracuseStep 30366359 = 45549539) B45549539
theorem B20244239 : Blo 2105435 20244239 := bstep (se 1 (by rfl) ⟨15183179, by rfl⟩ : syracuseStep 20244239 = 30366359) B30366359
theorem B13496159 : Blo 2105435 13496159 := bstep (se 1 (by rfl) ⟨10122119, by rfl⟩ : syracuseStep 13496159 = 20244239) B20244239
theorem B8997439 : Blo 2105435 8997439 := bstep (se 1 (by rfl) ⟨6748079, by rfl⟩ : syracuseStep 8997439 = 13496159) B13496159
theorem B11996585 : Blo 2105435 11996585 := bstep (se 2 (by rfl) ⟨4498719, by rfl⟩ : syracuseStep 11996585 = 8997439) B8997439
theorem B7997723 : Blo 2105435 7997723 := bstep (se 1 (by rfl) ⟨5998292, by rfl⟩ : syracuseStep 7997723 = 11996585) B11996585
theorem B5331815 : Blo 2105435 5331815 := bstep (se 1 (by rfl) ⟨3998861, by rfl⟩ : syracuseStep 5331815 = 7997723) B7997723
theorem B3554543 : Blo 2105435 3554543 := bstep (se 1 (by rfl) ⟨2665907, by rfl⟩ : syracuseStep 3554543 = 5331815) B5331815
theorem B2369695 : Blo 2105435 2369695 := bstep (se 1 (by rfl) ⟨1777271, by rfl⟩ : syracuseStep 2369695 = 3554543) B3554543
theorem B3159593 : Blo 2105435 3159593 := bstep (se 2 (by rfl) ⟨1184847, by rfl⟩ : syracuseStep 3159593 = 2369695) B2369695
theorem B2106395 : Blo 2105435 2106395 := bstep (se 1 (by rfl) ⟨1579796, by rfl⟩ : syracuseStep 2106395 = 3159593) B3159593
theorem B4270277 : Blo 2105435 4270277 := bbase (se 4 (by rfl) ⟨400338, by rfl⟩ : syracuseStep 4270277 = 800677) (by norm_num)
theorem B11387405 : Blo 2105435 11387405 := bstep (se 3 (by rfl) ⟨2135138, by rfl⟩ : syracuseStep 11387405 = 4270277) B4270277
theorem B30366413 : Blo 2105435 30366413 := bstep (se 3 (by rfl) ⟨5693702, by rfl⟩ : syracuseStep 30366413 = 11387405) B11387405
theorem B20244275 : Blo 2105435 20244275 := bstep (se 1 (by rfl) ⟨15183206, by rfl⟩ : syracuseStep 20244275 = 30366413) B30366413
theorem B13496183 : Blo 2105435 13496183 := bstep (se 1 (by rfl) ⟨10122137, by rfl⟩ : syracuseStep 13496183 = 20244275) B20244275
theorem B8997455 : Blo 2105435 8997455 := bstep (se 1 (by rfl) ⟨6748091, by rfl⟩ : syracuseStep 8997455 = 13496183) B13496183
theorem B5998303 : Blo 2105435 5998303 := bstep (se 1 (by rfl) ⟨4498727, by rfl⟩ : syracuseStep 5998303 = 8997455) B8997455
theorem B7997737 : Blo 2105435 7997737 := bstep (se 2 (by rfl) ⟨2999151, by rfl⟩ : syracuseStep 7997737 = 5998303) B5998303
theorem B10663649 : Blo 2105435 10663649 := bstep (se 2 (by rfl) ⟨3998868, by rfl⟩ : syracuseStep 10663649 = 7997737) B7997737
theorem B7109099 : Blo 2105435 7109099 := bstep (se 1 (by rfl) ⟨5331824, by rfl⟩ : syracuseStep 7109099 = 10663649) B10663649
theorem B4739399 : Blo 2105435 4739399 := bstep (se 1 (by rfl) ⟨3554549, by rfl⟩ : syracuseStep 4739399 = 7109099) B7109099
theorem B3159599 : Blo 2105435 3159599 := bstep (se 1 (by rfl) ⟨2369699, by rfl⟩ : syracuseStep 3159599 = 4739399) B4739399
theorem B2106399 : Blo 2105435 2106399 := bstep (se 1 (by rfl) ⟨1579799, by rfl⟩ : syracuseStep 2106399 = 3159599) B3159599
theorem B3159605 : Blo 2105435 3159605 := bbase (se 5 (by rfl) ⟨148106, by rfl⟩ : syracuseStep 3159605 = 296213) (by norm_num)
theorem B2106403 : Blo 2105435 2106403 := bstep (se 1 (by rfl) ⟨1579802, by rfl⟩ : syracuseStep 2106403 = 3159605) B3159605
theorem B5331845 : Blo 2105435 5331845 := bbase (se 4 (by rfl) ⟨499860, by rfl⟩ : syracuseStep 5331845 = 999721) (by norm_num)
theorem B3554563 : Blo 2105435 3554563 := bstep (se 1 (by rfl) ⟨2665922, by rfl⟩ : syracuseStep 3554563 = 5331845) B5331845
theorem B4739417 : Blo 2105435 4739417 := bstep (se 2 (by rfl) ⟨1777281, by rfl⟩ : syracuseStep 4739417 = 3554563) B3554563
theorem B3159611 : Blo 2105435 3159611 := bstep (se 1 (by rfl) ⟨2369708, by rfl⟩ : syracuseStep 3159611 = 4739417) B4739417
theorem B2106407 : Blo 2105435 2106407 := bstep (se 1 (by rfl) ⟨1579805, by rfl⟩ : syracuseStep 2106407 = 3159611) B3159611
theorem B2369713 : Blo 2105435 2369713 := bbase (se 2 (by rfl) ⟨888642, by rfl⟩ : syracuseStep 2369713 = 1777285) (by norm_num)
theorem B3159617 : Blo 2105435 3159617 := bstep (se 2 (by rfl) ⟨1184856, by rfl⟩ : syracuseStep 3159617 = 2369713) B2369713
theorem B2106411 : Blo 2105435 2106411 := bstep (se 1 (by rfl) ⟨1579808, by rfl⟩ : syracuseStep 2106411 = 3159617) B3159617
theorem B2249381 : Blo 2105435 2249381 := bbase (se 4 (by rfl) ⟨210879, by rfl⟩ : syracuseStep 2249381 = 421759) (by norm_num)
theorem B5998349 : Blo 2105435 5998349 := bstep (se 3 (by rfl) ⟨1124690, by rfl⟩ : syracuseStep 5998349 = 2249381) B2249381
theorem B3998899 : Blo 2105435 3998899 := bstep (se 1 (by rfl) ⟨2999174, by rfl⟩ : syracuseStep 3998899 = 5998349) B5998349
theorem B5331865 : Blo 2105435 5331865 := bstep (se 2 (by rfl) ⟨1999449, by rfl⟩ : syracuseStep 5331865 = 3998899) B3998899
theorem B7109153 : Blo 2105435 7109153 := bstep (se 2 (by rfl) ⟨2665932, by rfl⟩ : syracuseStep 7109153 = 5331865) B5331865
theorem B4739435 : Blo 2105435 4739435 := bstep (se 1 (by rfl) ⟨3554576, by rfl⟩ : syracuseStep 4739435 = 7109153) B7109153
theorem B3159623 : Blo 2105435 3159623 := bstep (se 1 (by rfl) ⟨2369717, by rfl⟩ : syracuseStep 3159623 = 4739435) B4739435
theorem B2106415 : Blo 2105435 2106415 := bstep (se 1 (by rfl) ⟨1579811, by rfl⟩ : syracuseStep 2106415 = 3159623) B3159623
theorem B3159629 : Blo 2105435 3159629 := bbase (se 3 (by rfl) ⟨592430, by rfl⟩ : syracuseStep 3159629 = 1184861) (by norm_num)
theorem B2106419 : Blo 2105435 2106419 := bstep (se 1 (by rfl) ⟨1579814, by rfl⟩ : syracuseStep 2106419 = 3159629) B3159629
theorem B4739453 : Blo 2105435 4739453 := bbase (se 3 (by rfl) ⟨888647, by rfl⟩ : syracuseStep 4739453 = 1777295) (by norm_num)
theorem B3159635 : Blo 2105435 3159635 := bstep (se 1 (by rfl) ⟨2369726, by rfl⟩ : syracuseStep 3159635 = 4739453) B4739453
theorem B2106423 : Blo 2105435 2106423 := bstep (se 1 (by rfl) ⟨1579817, by rfl⟩ : syracuseStep 2106423 = 3159635) B3159635
theorem B3554597 : Blo 2105435 3554597 := bbase (se 4 (by rfl) ⟨333243, by rfl⟩ : syracuseStep 3554597 = 666487) (by norm_num)
theorem B2369731 : Blo 2105435 2369731 := bstep (se 1 (by rfl) ⟨1777298, by rfl⟩ : syracuseStep 2369731 = 3554597) B3554597
theorem B3159641 : Blo 2105435 3159641 := bstep (se 2 (by rfl) ⟨1184865, by rfl⟩ : syracuseStep 3159641 = 2369731) B2369731
theorem B2106427 : Blo 2105435 2106427 := bstep (se 1 (by rfl) ⟨1579820, by rfl⟩ : syracuseStep 2106427 = 3159641) B3159641
theorem B2999197 : Blo 2105435 2999197 := bbase (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) (by norm_num)
theorem B15995717 : Blo 2105435 15995717 := bstep (se 4 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 15995717 = 2999197) B2999197
theorem B10663811 : Blo 2105435 10663811 := bstep (se 1 (by rfl) ⟨7997858, by rfl⟩ : syracuseStep 10663811 = 15995717) B15995717
theorem B7109207 : Blo 2105435 7109207 := bstep (se 1 (by rfl) ⟨5331905, by rfl⟩ : syracuseStep 7109207 = 10663811) B10663811
theorem B4739471 : Blo 2105435 4739471 := bstep (se 1 (by rfl) ⟨3554603, by rfl⟩ : syracuseStep 4739471 = 7109207) B7109207
theorem B3159647 : Blo 2105435 3159647 := bstep (se 1 (by rfl) ⟨2369735, by rfl⟩ : syracuseStep 3159647 = 4739471) B4739471
theorem B2106431 : Blo 2105435 2106431 := bstep (se 1 (by rfl) ⟨1579823, by rfl⟩ : syracuseStep 2106431 = 3159647) B3159647
theorem B3159653 : Blo 2105435 3159653 := bbase (se 4 (by rfl) ⟨296217, by rfl⟩ : syracuseStep 3159653 = 592435) (by norm_num)
theorem B2106435 : Blo 2105435 2106435 := bstep (se 1 (by rfl) ⟨1579826, by rfl⟩ : syracuseStep 2106435 = 3159653) B3159653
theorem B8107013 : Blo 2105435 8107013 := bbase (se 4 (by rfl) ⟨760032, by rfl⟩ : syracuseStep 8107013 = 1520065) (by norm_num)
theorem B21618701 : Blo 2105435 21618701 := bstep (se 3 (by rfl) ⟨4053506, by rfl⟩ : syracuseStep 21618701 = 8107013) B8107013
theorem B14412467 : Blo 2105435 14412467 := bstep (se 1 (by rfl) ⟨10809350, by rfl⟩ : syracuseStep 14412467 = 21618701) B21618701
theorem B9608311 : Blo 2105435 9608311 := bstep (se 1 (by rfl) ⟨7206233, by rfl⟩ : syracuseStep 9608311 = 14412467) B14412467
theorem B12811081 : Blo 2105435 12811081 := bstep (se 2 (by rfl) ⟨4804155, by rfl⟩ : syracuseStep 12811081 = 9608311) B9608311
theorem B17081441 : Blo 2105435 17081441 := bstep (se 2 (by rfl) ⟨6405540, by rfl⟩ : syracuseStep 17081441 = 12811081) B12811081
theorem B11387627 : Blo 2105435 11387627 := bstep (se 1 (by rfl) ⟨8540720, by rfl⟩ : syracuseStep 11387627 = 17081441) B17081441
theorem B7591751 : Blo 2105435 7591751 := bstep (se 1 (by rfl) ⟨5693813, by rfl⟩ : syracuseStep 7591751 = 11387627) B11387627
theorem B5061167 : Blo 2105435 5061167 := bstep (se 1 (by rfl) ⟨3795875, by rfl⟩ : syracuseStep 5061167 = 7591751) B7591751
theorem B3374111 : Blo 2105435 3374111 := bstep (se 1 (by rfl) ⟨2530583, by rfl⟩ : syracuseStep 3374111 = 5061167) B5061167
theorem B2249407 : Blo 2105435 2249407 := bstep (se 1 (by rfl) ⟨1687055, by rfl⟩ : syracuseStep 2249407 = 3374111) B3374111
theorem B2999209 : Blo 2105435 2999209 := bstep (se 2 (by rfl) ⟨1124703, by rfl⟩ : syracuseStep 2999209 = 2249407) B2249407
theorem B3998945 : Blo 2105435 3998945 := bstep (se 2 (by rfl) ⟨1499604, by rfl⟩ : syracuseStep 3998945 = 2999209) B2999209
theorem B2665963 : Blo 2105435 2665963 := bstep (se 1 (by rfl) ⟨1999472, by rfl⟩ : syracuseStep 2665963 = 3998945) B3998945
theorem B3554617 : Blo 2105435 3554617 := bstep (se 2 (by rfl) ⟨1332981, by rfl⟩ : syracuseStep 3554617 = 2665963) B2665963
theorem B4739489 : Blo 2105435 4739489 := bstep (se 2 (by rfl) ⟨1777308, by rfl⟩ : syracuseStep 4739489 = 3554617) B3554617
theorem B3159659 : Blo 2105435 3159659 := bstep (se 1 (by rfl) ⟨2369744, by rfl⟩ : syracuseStep 3159659 = 4739489) B4739489
theorem B2106439 : Blo 2105435 2106439 := bstep (se 1 (by rfl) ⟨1579829, by rfl⟩ : syracuseStep 2106439 = 3159659) B3159659
theorem B2369749 : Blo 2105435 2369749 := bbase (se 7 (by rfl) ⟨27770, by rfl⟩ : syracuseStep 2369749 = 55541) (by norm_num)
theorem B3159665 : Blo 2105435 3159665 := bstep (se 2 (by rfl) ⟨1184874, by rfl⟩ : syracuseStep 3159665 = 2369749) B2369749
theorem B2106443 : Blo 2105435 2106443 := bstep (se 1 (by rfl) ⟨1579832, by rfl⟩ : syracuseStep 2106443 = 3159665) B3159665
theorem B2665973 : Blo 2105435 2665973 := bbase (se 5 (by rfl) ⟨124967, by rfl⟩ : syracuseStep 2665973 = 249935) (by norm_num)
theorem B7109261 : Blo 2105435 7109261 := bstep (se 3 (by rfl) ⟨1332986, by rfl⟩ : syracuseStep 7109261 = 2665973) B2665973
theorem B4739507 : Blo 2105435 4739507 := bstep (se 1 (by rfl) ⟨3554630, by rfl⟩ : syracuseStep 4739507 = 7109261) B7109261
theorem B3159671 : Blo 2105435 3159671 := bstep (se 1 (by rfl) ⟨2369753, by rfl⟩ : syracuseStep 3159671 = 4739507) B4739507
theorem B2106447 : Blo 2105435 2106447 := bstep (se 1 (by rfl) ⟨1579835, by rfl⟩ : syracuseStep 2106447 = 3159671) B3159671
theorem B3159677 : Blo 2105435 3159677 := bbase (se 3 (by rfl) ⟨592439, by rfl⟩ : syracuseStep 3159677 = 1184879) (by norm_num)
theorem B2106451 : Blo 2105435 2106451 := bstep (se 1 (by rfl) ⟨1579838, by rfl⟩ : syracuseStep 2106451 = 3159677) B3159677
theorem B4739525 : Blo 2105435 4739525 := bbase (se 4 (by rfl) ⟨444330, by rfl⟩ : syracuseStep 4739525 = 888661) (by norm_num)
theorem B3159683 : Blo 2105435 3159683 := bstep (se 1 (by rfl) ⟨2369762, by rfl⟩ : syracuseStep 3159683 = 4739525) B4739525
theorem B2106455 : Blo 2105435 2106455 := bstep (se 1 (by rfl) ⟨1579841, by rfl⟩ : syracuseStep 2106455 = 3159683) B3159683
theorem B4869749 : Blo 2105435 4869749 := bbase (se 5 (by rfl) ⟨228269, by rfl⟩ : syracuseStep 4869749 = 456539) (by norm_num)
theorem B3246499 : Blo 2105435 3246499 := bstep (se 1 (by rfl) ⟨2434874, by rfl⟩ : syracuseStep 3246499 = 4869749) B4869749
theorem B17314661 : Blo 2105435 17314661 := bstep (se 4 (by rfl) ⟨1623249, by rfl⟩ : syracuseStep 17314661 = 3246499) B3246499
theorem B11543107 : Blo 2105435 11543107 := bstep (se 1 (by rfl) ⟨8657330, by rfl⟩ : syracuseStep 11543107 = 17314661) B17314661
theorem B15390809 : Blo 2105435 15390809 := bstep (se 2 (by rfl) ⟨5771553, by rfl⟩ : syracuseStep 15390809 = 11543107) B11543107
theorem B10260539 : Blo 2105435 10260539 := bstep (se 1 (by rfl) ⟨7695404, by rfl⟩ : syracuseStep 10260539 = 15390809) B15390809
theorem B6840359 : Blo 2105435 6840359 := bstep (se 1 (by rfl) ⟨5130269, by rfl⟩ : syracuseStep 6840359 = 10260539) B10260539
theorem B4560239 : Blo 2105435 4560239 := bstep (se 1 (by rfl) ⟨3420179, by rfl⟩ : syracuseStep 4560239 = 6840359) B6840359
theorem B12160637 : Blo 2105435 12160637 := bstep (se 3 (by rfl) ⟨2280119, by rfl⟩ : syracuseStep 12160637 = 4560239) B4560239
theorem B8107091 : Blo 2105435 8107091 := bstep (se 1 (by rfl) ⟨6080318, by rfl⟩ : syracuseStep 8107091 = 12160637) B12160637
theorem B5404727 : Blo 2105435 5404727 := bstep (se 1 (by rfl) ⟨4053545, by rfl⟩ : syracuseStep 5404727 = 8107091) B8107091
theorem B3603151 : Blo 2105435 3603151 := bstep (se 1 (by rfl) ⟨2702363, by rfl⟩ : syracuseStep 3603151 = 5404727) B5404727
theorem B4804201 : Blo 2105435 4804201 := bstep (se 2 (by rfl) ⟨1801575, by rfl⟩ : syracuseStep 4804201 = 3603151) B3603151
theorem B6405601 : Blo 2105435 6405601 := bstep (se 2 (by rfl) ⟨2402100, by rfl⟩ : syracuseStep 6405601 = 4804201) B4804201
theorem B8540801 : Blo 2105435 8540801 := bstep (se 2 (by rfl) ⟨3202800, by rfl⟩ : syracuseStep 8540801 = 6405601) B6405601
theorem B5693867 : Blo 2105435 5693867 := bstep (se 1 (by rfl) ⟨4270400, by rfl⟩ : syracuseStep 5693867 = 8540801) B8540801
theorem B3795911 : Blo 2105435 3795911 := bstep (se 1 (by rfl) ⟨2846933, by rfl⟩ : syracuseStep 3795911 = 5693867) B5693867
theorem B2530607 : Blo 2105435 2530607 := bstep (se 1 (by rfl) ⟨1897955, by rfl⟩ : syracuseStep 2530607 = 3795911) B3795911
theorem B6748285 : Blo 2105435 6748285 := bstep (se 3 (by rfl) ⟨1265303, by rfl⟩ : syracuseStep 6748285 = 2530607) B2530607
theorem B8997713 : Blo 2105435 8997713 := bstep (se 2 (by rfl) ⟨3374142, by rfl⟩ : syracuseStep 8997713 = 6748285) B6748285
theorem B5998475 : Blo 2105435 5998475 := bstep (se 1 (by rfl) ⟨4498856, by rfl⟩ : syracuseStep 5998475 = 8997713) B8997713
theorem B3998983 : Blo 2105435 3998983 := bstep (se 1 (by rfl) ⟨2999237, by rfl⟩ : syracuseStep 3998983 = 5998475) B5998475
theorem B5331977 : Blo 2105435 5331977 := bstep (se 2 (by rfl) ⟨1999491, by rfl⟩ : syracuseStep 5331977 = 3998983) B3998983
theorem B3554651 : Blo 2105435 3554651 := bstep (se 1 (by rfl) ⟨2665988, by rfl⟩ : syracuseStep 3554651 = 5331977) B5331977
theorem B2369767 : Blo 2105435 2369767 := bstep (se 1 (by rfl) ⟨1777325, by rfl⟩ : syracuseStep 2369767 = 3554651) B3554651
theorem B3159689 : Blo 2105435 3159689 := bstep (se 2 (by rfl) ⟨1184883, by rfl⟩ : syracuseStep 3159689 = 2369767) B2369767
theorem B2106459 : Blo 2105435 2106459 := bstep (se 1 (by rfl) ⟨1579844, by rfl⟩ : syracuseStep 2106459 = 3159689) B3159689
theorem B10663973 : Blo 2105435 10663973 := bbase (se 4 (by rfl) ⟨999747, by rfl⟩ : syracuseStep 10663973 = 1999495) (by norm_num)
theorem B7109315 : Blo 2105435 7109315 := bstep (se 1 (by rfl) ⟨5331986, by rfl⟩ : syracuseStep 7109315 = 10663973) B10663973
theorem B4739543 : Blo 2105435 4739543 := bstep (se 1 (by rfl) ⟨3554657, by rfl⟩ : syracuseStep 4739543 = 7109315) B7109315
theorem B3159695 : Blo 2105435 3159695 := bstep (se 1 (by rfl) ⟨2369771, by rfl⟩ : syracuseStep 3159695 = 4739543) B4739543
theorem B2106463 : Blo 2105435 2106463 := bstep (se 1 (by rfl) ⟨1579847, by rfl⟩ : syracuseStep 2106463 = 3159695) B3159695
theorem B3159701 : Blo 2105435 3159701 := bbase (se 6 (by rfl) ⟨74055, by rfl⟩ : syracuseStep 3159701 = 148111) (by norm_num)
theorem B2106467 : Blo 2105435 2106467 := bstep (se 1 (by rfl) ⟨1579850, by rfl⟩ : syracuseStep 2106467 = 3159701) B3159701
theorem B2530621 : Blo 2105435 2530621 := bbase (se 3 (by rfl) ⟨474491, by rfl⟩ : syracuseStep 2530621 = 948983) (by norm_num)
theorem B13496645 : Blo 2105435 13496645 := bstep (se 4 (by rfl) ⟨1265310, by rfl⟩ : syracuseStep 13496645 = 2530621) B2530621
theorem B8997763 : Blo 2105435 8997763 := bstep (se 1 (by rfl) ⟨6748322, by rfl⟩ : syracuseStep 8997763 = 13496645) B13496645
theorem B11997017 : Blo 2105435 11997017 := bstep (se 2 (by rfl) ⟨4498881, by rfl⟩ : syracuseStep 11997017 = 8997763) B8997763
theorem B7998011 : Blo 2105435 7998011 := bstep (se 1 (by rfl) ⟨5998508, by rfl⟩ : syracuseStep 7998011 = 11997017) B11997017
theorem B5332007 : Blo 2105435 5332007 := bstep (se 1 (by rfl) ⟨3999005, by rfl⟩ : syracuseStep 5332007 = 7998011) B7998011
theorem B3554671 : Blo 2105435 3554671 := bstep (se 1 (by rfl) ⟨2666003, by rfl⟩ : syracuseStep 3554671 = 5332007) B5332007
theorem B4739561 : Blo 2105435 4739561 := bstep (se 2 (by rfl) ⟨1777335, by rfl⟩ : syracuseStep 4739561 = 3554671) B3554671
theorem B3159707 : Blo 2105435 3159707 := bstep (se 1 (by rfl) ⟨2369780, by rfl⟩ : syracuseStep 3159707 = 4739561) B4739561
theorem B2106471 : Blo 2105435 2106471 := bstep (se 1 (by rfl) ⟨1579853, by rfl⟩ : syracuseStep 2106471 = 3159707) B3159707
theorem B2369785 : Blo 2105435 2369785 := bbase (se 2 (by rfl) ⟨888669, by rfl⟩ : syracuseStep 2369785 = 1777339) (by norm_num)
theorem B3159713 : Blo 2105435 3159713 := bstep (se 2 (by rfl) ⟨1184892, by rfl⟩ : syracuseStep 3159713 = 2369785) B2369785
theorem B2106475 : Blo 2105435 2106475 := bstep (se 1 (by rfl) ⟨1579856, by rfl⟩ : syracuseStep 2106475 = 3159713) B3159713
theorem B8997797 : Blo 2105435 8997797 := bbase (se 4 (by rfl) ⟨843543, by rfl⟩ : syracuseStep 8997797 = 1687087) (by norm_num)
theorem B5998531 : Blo 2105435 5998531 := bstep (se 1 (by rfl) ⟨4498898, by rfl⟩ : syracuseStep 5998531 = 8997797) B8997797
theorem B7998041 : Blo 2105435 7998041 := bstep (se 2 (by rfl) ⟨2999265, by rfl⟩ : syracuseStep 7998041 = 5998531) B5998531
theorem B5332027 : Blo 2105435 5332027 := bstep (se 1 (by rfl) ⟨3999020, by rfl⟩ : syracuseStep 5332027 = 7998041) B7998041
theorem B7109369 : Blo 2105435 7109369 := bstep (se 2 (by rfl) ⟨2666013, by rfl⟩ : syracuseStep 7109369 = 5332027) B5332027
theorem B4739579 : Blo 2105435 4739579 := bstep (se 1 (by rfl) ⟨3554684, by rfl⟩ : syracuseStep 4739579 = 7109369) B7109369
theorem B3159719 : Blo 2105435 3159719 := bstep (se 1 (by rfl) ⟨2369789, by rfl⟩ : syracuseStep 3159719 = 4739579) B4739579
theorem B2106479 : Blo 2105435 2106479 := bstep (se 1 (by rfl) ⟨1579859, by rfl⟩ : syracuseStep 2106479 = 3159719) B3159719
theorem B3159725 : Blo 2105435 3159725 := bbase (se 3 (by rfl) ⟨592448, by rfl⟩ : syracuseStep 3159725 = 1184897) (by norm_num)
theorem B2106483 : Blo 2105435 2106483 := bstep (se 1 (by rfl) ⟨1579862, by rfl⟩ : syracuseStep 2106483 = 3159725) B3159725
theorem B4739597 : Blo 2105435 4739597 := bbase (se 3 (by rfl) ⟨888674, by rfl⟩ : syracuseStep 4739597 = 1777349) (by norm_num)
theorem B3159731 : Blo 2105435 3159731 := bstep (se 1 (by rfl) ⟨2369798, by rfl⟩ : syracuseStep 3159731 = 4739597) B4739597
theorem B2106487 : Blo 2105435 2106487 := bstep (se 1 (by rfl) ⟨1579865, by rfl⟩ : syracuseStep 2106487 = 3159731) B3159731
theorem B2666029 : Blo 2105435 2666029 := bbase (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) (by norm_num)
theorem B3554705 : Blo 2105435 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B2369803 : Blo 2105435 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B3159737 : Blo 2105435 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B2106491 : Blo 2105435 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B2846981 : Blo 2105435 2846981 := bbase (se 4 (by rfl) ⟨266904, by rfl⟩ : syracuseStep 2846981 = 533809) (by norm_num)
theorem B7591949 : Blo 2105435 7591949 := bstep (se 3 (by rfl) ⟨1423490, by rfl⟩ : syracuseStep 7591949 = 2846981) B2846981
theorem B5061299 : Blo 2105435 5061299 := bstep (se 1 (by rfl) ⟨3795974, by rfl⟩ : syracuseStep 5061299 = 7591949) B7591949
theorem B13496797 : Blo 2105435 13496797 := bstep (se 3 (by rfl) ⟨2530649, by rfl⟩ : syracuseStep 13496797 = 5061299) B5061299
theorem B17995729 : Blo 2105435 17995729 := bstep (se 2 (by rfl) ⟨6748398, by rfl⟩ : syracuseStep 17995729 = 13496797) B13496797
theorem B23994305 : Blo 2105435 23994305 := bstep (se 2 (by rfl) ⟨8997864, by rfl⟩ : syracuseStep 23994305 = 17995729) B17995729
theorem B15996203 : Blo 2105435 15996203 := bstep (se 1 (by rfl) ⟨11997152, by rfl⟩ : syracuseStep 15996203 = 23994305) B23994305
theorem B10664135 : Blo 2105435 10664135 := bstep (se 1 (by rfl) ⟨7998101, by rfl⟩ : syracuseStep 10664135 = 15996203) B15996203
theorem B7109423 : Blo 2105435 7109423 := bstep (se 1 (by rfl) ⟨5332067, by rfl⟩ : syracuseStep 7109423 = 10664135) B10664135
theorem B4739615 : Blo 2105435 4739615 := bstep (se 1 (by rfl) ⟨3554711, by rfl⟩ : syracuseStep 4739615 = 7109423) B7109423
theorem B3159743 : Blo 2105435 3159743 := bstep (se 1 (by rfl) ⟨2369807, by rfl⟩ : syracuseStep 3159743 = 4739615) B4739615
theorem B2106495 : Blo 2105435 2106495 := bstep (se 1 (by rfl) ⟨1579871, by rfl⟩ : syracuseStep 2106495 = 3159743) B3159743
theorem B3159749 : Blo 2105435 3159749 := bbase (se 4 (by rfl) ⟨296226, by rfl⟩ : syracuseStep 3159749 = 592453) (by norm_num)
theorem B2106499 : Blo 2105435 2106499 := bstep (se 1 (by rfl) ⟨1579874, by rfl⟩ : syracuseStep 2106499 = 3159749) B3159749
theorem B3554725 : Blo 2105435 3554725 := bbase (se 4 (by rfl) ⟨333255, by rfl⟩ : syracuseStep 3554725 = 666511) (by norm_num)
theorem B4739633 : Blo 2105435 4739633 := bstep (se 2 (by rfl) ⟨1777362, by rfl⟩ : syracuseStep 4739633 = 3554725) B3554725
theorem B3159755 : Blo 2105435 3159755 := bstep (se 1 (by rfl) ⟨2369816, by rfl⟩ : syracuseStep 3159755 = 4739633) B4739633
theorem B2106503 : Blo 2105435 2106503 := bstep (se 1 (by rfl) ⟨1579877, by rfl⟩ : syracuseStep 2106503 = 3159755) B3159755
theorem B2369821 : Blo 2105435 2369821 := bbase (se 3 (by rfl) ⟨444341, by rfl⟩ : syracuseStep 2369821 = 888683) (by norm_num)
theorem B3159761 : Blo 2105435 3159761 := bstep (se 2 (by rfl) ⟨1184910, by rfl⟩ : syracuseStep 3159761 = 2369821) B2369821
theorem B2106507 : Blo 2105435 2106507 := bstep (se 1 (by rfl) ⟨1579880, by rfl⟩ : syracuseStep 2106507 = 3159761) B3159761
theorem B7109477 : Blo 2105435 7109477 := bbase (se 4 (by rfl) ⟨666513, by rfl⟩ : syracuseStep 7109477 = 1333027) (by norm_num)
theorem B4739651 : Blo 2105435 4739651 := bstep (se 1 (by rfl) ⟨3554738, by rfl⟩ : syracuseStep 4739651 = 7109477) B7109477
theorem B3159767 : Blo 2105435 3159767 := bstep (se 1 (by rfl) ⟨2369825, by rfl⟩ : syracuseStep 3159767 = 4739651) B4739651
theorem B2106511 : Blo 2105435 2106511 := bstep (se 1 (by rfl) ⟨1579883, by rfl⟩ : syracuseStep 2106511 = 3159767) B3159767
theorem B3159773 : Blo 2105435 3159773 := bbase (se 3 (by rfl) ⟨592457, by rfl⟩ : syracuseStep 3159773 = 1184915) (by norm_num)
theorem B2106515 : Blo 2105435 2106515 := bstep (se 1 (by rfl) ⟨1579886, by rfl⟩ : syracuseStep 2106515 = 3159773) B3159773
theorem B4739669 : Blo 2105435 4739669 := bbase (se 8 (by rfl) ⟨27771, by rfl⟩ : syracuseStep 4739669 = 55543) (by norm_num)
theorem B3159779 : Blo 2105435 3159779 := bstep (se 1 (by rfl) ⟨2369834, by rfl⟩ : syracuseStep 3159779 = 4739669) B4739669
theorem B2106519 : Blo 2105435 2106519 := bstep (se 1 (by rfl) ⟨1579889, by rfl⟩ : syracuseStep 2106519 = 3159779) B3159779
theorem B3374245 : Blo 2105435 3374245 := bbase (se 4 (by rfl) ⟨316335, by rfl⟩ : syracuseStep 3374245 = 632671) (by norm_num)
theorem B4498993 : Blo 2105435 4498993 := bstep (se 2 (by rfl) ⟨1687122, by rfl⟩ : syracuseStep 4498993 = 3374245) B3374245
theorem B5998657 : Blo 2105435 5998657 := bstep (se 2 (by rfl) ⟨2249496, by rfl⟩ : syracuseStep 5998657 = 4498993) B4498993
theorem B7998209 : Blo 2105435 7998209 := bstep (se 2 (by rfl) ⟨2999328, by rfl⟩ : syracuseStep 7998209 = 5998657) B5998657
theorem B5332139 : Blo 2105435 5332139 := bstep (se 1 (by rfl) ⟨3999104, by rfl⟩ : syracuseStep 5332139 = 7998209) B7998209
theorem B3554759 : Blo 2105435 3554759 := bstep (se 1 (by rfl) ⟨2666069, by rfl⟩ : syracuseStep 3554759 = 5332139) B5332139
theorem B2369839 : Blo 2105435 2369839 := bstep (se 1 (by rfl) ⟨1777379, by rfl⟩ : syracuseStep 2369839 = 3554759) B3554759
theorem B3159785 : Blo 2105435 3159785 := bstep (se 2 (by rfl) ⟨1184919, by rfl⟩ : syracuseStep 3159785 = 2369839) B2369839
theorem B2106523 : Blo 2105435 2106523 := bstep (se 1 (by rfl) ⟨1579892, by rfl⟩ : syracuseStep 2106523 = 3159785) B3159785
theorem B26994005 : Blo 2105435 26994005 := bbase (se 12 (by rfl) ⟨9885, by rfl⟩ : syracuseStep 26994005 = 19771) (by norm_num)
theorem B17996003 : Blo 2105435 17996003 := bstep (se 1 (by rfl) ⟨13497002, by rfl⟩ : syracuseStep 17996003 = 26994005) B26994005
theorem B11997335 : Blo 2105435 11997335 := bstep (se 1 (by rfl) ⟨8998001, by rfl⟩ : syracuseStep 11997335 = 17996003) B17996003
theorem B7998223 : Blo 2105435 7998223 := bstep (se 1 (by rfl) ⟨5998667, by rfl⟩ : syracuseStep 7998223 = 11997335) B11997335
theorem B10664297 : Blo 2105435 10664297 := bstep (se 2 (by rfl) ⟨3999111, by rfl⟩ : syracuseStep 10664297 = 7998223) B7998223
theorem B7109531 : Blo 2105435 7109531 := bstep (se 1 (by rfl) ⟨5332148, by rfl⟩ : syracuseStep 7109531 = 10664297) B10664297
theorem B4739687 : Blo 2105435 4739687 := bstep (se 1 (by rfl) ⟨3554765, by rfl⟩ : syracuseStep 4739687 = 7109531) B7109531
theorem B3159791 : Blo 2105435 3159791 := bstep (se 1 (by rfl) ⟨2369843, by rfl⟩ : syracuseStep 3159791 = 4739687) B4739687
theorem B2106527 : Blo 2105435 2106527 := bstep (se 1 (by rfl) ⟨1579895, by rfl⟩ : syracuseStep 2106527 = 3159791) B3159791
theorem B3159797 : Blo 2105435 3159797 := bbase (se 5 (by rfl) ⟨148115, by rfl⟩ : syracuseStep 3159797 = 296231) (by norm_num)
theorem B2106531 : Blo 2105435 2106531 := bstep (se 1 (by rfl) ⟨1579898, by rfl⟩ : syracuseStep 2106531 = 3159797) B3159797
theorem B8998037 : Blo 2105435 8998037 := bbase (se 6 (by rfl) ⟨210891, by rfl⟩ : syracuseStep 8998037 = 421783) (by norm_num)
theorem B5998691 : Blo 2105435 5998691 := bstep (se 1 (by rfl) ⟨4499018, by rfl⟩ : syracuseStep 5998691 = 8998037) B8998037
theorem B3999127 : Blo 2105435 3999127 := bstep (se 1 (by rfl) ⟨2999345, by rfl⟩ : syracuseStep 3999127 = 5998691) B5998691
theorem B5332169 : Blo 2105435 5332169 := bstep (se 2 (by rfl) ⟨1999563, by rfl⟩ : syracuseStep 5332169 = 3999127) B3999127
theorem B3554779 : Blo 2105435 3554779 := bstep (se 1 (by rfl) ⟨2666084, by rfl⟩ : syracuseStep 3554779 = 5332169) B5332169
theorem B4739705 : Blo 2105435 4739705 := bstep (se 2 (by rfl) ⟨1777389, by rfl⟩ : syracuseStep 4739705 = 3554779) B3554779
theorem B3159803 : Blo 2105435 3159803 := bstep (se 1 (by rfl) ⟨2369852, by rfl⟩ : syracuseStep 3159803 = 4739705) B4739705
theorem B2106535 : Blo 2105435 2106535 := bstep (se 1 (by rfl) ⟨1579901, by rfl⟩ : syracuseStep 2106535 = 3159803) B3159803
theorem B2369857 : Blo 2105435 2369857 := bbase (se 2 (by rfl) ⟨888696, by rfl⟩ : syracuseStep 2369857 = 1777393) (by norm_num)
theorem B3159809 : Blo 2105435 3159809 := bstep (se 2 (by rfl) ⟨1184928, by rfl⟩ : syracuseStep 3159809 = 2369857) B2369857
theorem B2106539 : Blo 2105435 2106539 := bstep (se 1 (by rfl) ⟨1579904, by rfl⟩ : syracuseStep 2106539 = 3159809) B3159809
theorem B5332189 : Blo 2105435 5332189 := bbase (se 3 (by rfl) ⟨999785, by rfl⟩ : syracuseStep 5332189 = 1999571) (by norm_num)
theorem B7109585 : Blo 2105435 7109585 := bstep (se 2 (by rfl) ⟨2666094, by rfl⟩ : syracuseStep 7109585 = 5332189) B5332189
theorem B4739723 : Blo 2105435 4739723 := bstep (se 1 (by rfl) ⟨3554792, by rfl⟩ : syracuseStep 4739723 = 7109585) B7109585
theorem B3159815 : Blo 2105435 3159815 := bstep (se 1 (by rfl) ⟨2369861, by rfl⟩ : syracuseStep 3159815 = 4739723) B4739723
theorem B2106543 : Blo 2105435 2106543 := bstep (se 1 (by rfl) ⟨1579907, by rfl⟩ : syracuseStep 2106543 = 3159815) B3159815
theorem B3159821 : Blo 2105435 3159821 := bbase (se 3 (by rfl) ⟨592466, by rfl⟩ : syracuseStep 3159821 = 1184933) (by norm_num)
theorem B2106547 : Blo 2105435 2106547 := bstep (se 1 (by rfl) ⟨1579910, by rfl⟩ : syracuseStep 2106547 = 3159821) B3159821
theorem B4739741 : Blo 2105435 4739741 := bbase (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) (by norm_num)
theorem B3159827 : Blo 2105435 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B2106551 : Blo 2105435 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B3554813 : Blo 2105435 3554813 := bbase (se 3 (by rfl) ⟨666527, by rfl⟩ : syracuseStep 3554813 = 1333055) (by norm_num)
theorem B2369875 : Blo 2105435 2369875 := bstep (se 1 (by rfl) ⟨1777406, by rfl⟩ : syracuseStep 2369875 = 3554813) B3554813
theorem B3159833 : Blo 2105435 3159833 := bstep (se 2 (by rfl) ⟨1184937, by rfl⟩ : syracuseStep 3159833 = 2369875) B2369875
theorem B2106555 : Blo 2105435 2106555 := bstep (se 1 (by rfl) ⟨1579916, by rfl⟩ : syracuseStep 2106555 = 3159833) B3159833
theorem B4499069 : Blo 2105435 4499069 := bbase (se 3 (by rfl) ⟨843575, by rfl⟩ : syracuseStep 4499069 = 1687151) (by norm_num)
theorem B11997517 : Blo 2105435 11997517 := bstep (se 3 (by rfl) ⟨2249534, by rfl⟩ : syracuseStep 11997517 = 4499069) B4499069
theorem B15996689 : Blo 2105435 15996689 := bstep (se 2 (by rfl) ⟨5998758, by rfl⟩ : syracuseStep 15996689 = 11997517) B11997517
theorem B10664459 : Blo 2105435 10664459 := bstep (se 1 (by rfl) ⟨7998344, by rfl⟩ : syracuseStep 10664459 = 15996689) B15996689
theorem B7109639 : Blo 2105435 7109639 := bstep (se 1 (by rfl) ⟨5332229, by rfl⟩ : syracuseStep 7109639 = 10664459) B10664459
theorem B4739759 : Blo 2105435 4739759 := bstep (se 1 (by rfl) ⟨3554819, by rfl⟩ : syracuseStep 4739759 = 7109639) B7109639
theorem B3159839 : Blo 2105435 3159839 := bstep (se 1 (by rfl) ⟨2369879, by rfl⟩ : syracuseStep 3159839 = 4739759) B4739759
theorem B2106559 : Blo 2105435 2106559 := bstep (se 1 (by rfl) ⟨1579919, by rfl⟩ : syracuseStep 2106559 = 3159839) B3159839
theorem B3159845 : Blo 2105435 3159845 := bbase (se 4 (by rfl) ⟨296235, by rfl⟩ : syracuseStep 3159845 = 592471) (by norm_num)
theorem B2106563 : Blo 2105435 2106563 := bstep (se 1 (by rfl) ⟨1579922, by rfl⟩ : syracuseStep 2106563 = 3159845) B3159845
theorem B2666125 : Blo 2105435 2666125 := bbase (se 3 (by rfl) ⟨499898, by rfl⟩ : syracuseStep 2666125 = 999797) (by norm_num)
theorem B3554833 : Blo 2105435 3554833 := bstep (se 2 (by rfl) ⟨1333062, by rfl⟩ : syracuseStep 3554833 = 2666125) B2666125
theorem B4739777 : Blo 2105435 4739777 := bstep (se 2 (by rfl) ⟨1777416, by rfl⟩ : syracuseStep 4739777 = 3554833) B3554833
theorem B3159851 : Blo 2105435 3159851 := bstep (se 1 (by rfl) ⟨2369888, by rfl⟩ : syracuseStep 3159851 = 4739777) B4739777
theorem B2106567 : Blo 2105435 2106567 := bstep (se 1 (by rfl) ⟨1579925, by rfl⟩ : syracuseStep 2106567 = 3159851) B3159851
theorem B2369893 : Blo 2105435 2369893 := bbase (se 4 (by rfl) ⟨222177, by rfl⟩ : syracuseStep 2369893 = 444355) (by norm_num)
theorem B3159857 : Blo 2105435 3159857 := bstep (se 2 (by rfl) ⟨1184946, by rfl⟩ : syracuseStep 3159857 = 2369893) B2369893
theorem B2106571 : Blo 2105435 2106571 := bstep (se 1 (by rfl) ⟨1579928, by rfl⟩ : syracuseStep 2106571 = 3159857) B3159857
theorem B5998805 : Blo 2105435 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B3999203 : Blo 2105435 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B2666135 : Blo 2105435 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B7109693 : Blo 2105435 7109693 := bstep (se 3 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 7109693 = 2666135) B2666135
theorem B4739795 : Blo 2105435 4739795 := bstep (se 1 (by rfl) ⟨3554846, by rfl⟩ : syracuseStep 4739795 = 7109693) B7109693
theorem B3159863 : Blo 2105435 3159863 := bstep (se 1 (by rfl) ⟨2369897, by rfl⟩ : syracuseStep 3159863 = 4739795) B4739795
theorem B2106575 : Blo 2105435 2106575 := bstep (se 1 (by rfl) ⟨1579931, by rfl⟩ : syracuseStep 2106575 = 3159863) B3159863
theorem B3159869 : Blo 2105435 3159869 := bbase (se 3 (by rfl) ⟨592475, by rfl⟩ : syracuseStep 3159869 = 1184951) (by norm_num)
theorem B2106579 : Blo 2105435 2106579 := bstep (se 1 (by rfl) ⟨1579934, by rfl⟩ : syracuseStep 2106579 = 3159869) B3159869
theorem B4739813 : Blo 2105435 4739813 := bbase (se 4 (by rfl) ⟨444357, by rfl⟩ : syracuseStep 4739813 = 888715) (by norm_num)
theorem B3159875 : Blo 2105435 3159875 := bstep (se 1 (by rfl) ⟨2369906, by rfl⟩ : syracuseStep 3159875 = 4739813) B4739813
theorem B2106583 : Blo 2105435 2106583 := bstep (se 1 (by rfl) ⟨1579937, by rfl⟩ : syracuseStep 2106583 = 3159875) B3159875
theorem B5332301 : Blo 2105435 5332301 := bbase (se 3 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 5332301 = 1999613) (by norm_num)
theorem B3554867 : Blo 2105435 3554867 := bstep (se 1 (by rfl) ⟨2666150, by rfl⟩ : syracuseStep 3554867 = 5332301) B5332301
theorem B2369911 : Blo 2105435 2369911 := bstep (se 1 (by rfl) ⟨1777433, by rfl⟩ : syracuseStep 2369911 = 3554867) B3554867
theorem B3159881 : Blo 2105435 3159881 := bstep (se 2 (by rfl) ⟨1184955, by rfl⟩ : syracuseStep 3159881 = 2369911) B2369911
theorem B2106587 : Blo 2105435 2106587 := bstep (se 1 (by rfl) ⟨1579940, by rfl⟩ : syracuseStep 2106587 = 3159881) B3159881
theorem B2249569 : Blo 2105435 2249569 := bbase (se 2 (by rfl) ⟨843588, by rfl⟩ : syracuseStep 2249569 = 1687177) (by norm_num)
theorem B2999425 : Blo 2105435 2999425 := bstep (se 2 (by rfl) ⟨1124784, by rfl⟩ : syracuseStep 2999425 = 2249569) B2249569
theorem B3999233 : Blo 2105435 3999233 := bstep (se 2 (by rfl) ⟨1499712, by rfl⟩ : syracuseStep 3999233 = 2999425) B2999425
theorem B10664621 : Blo 2105435 10664621 := bstep (se 3 (by rfl) ⟨1999616, by rfl⟩ : syracuseStep 10664621 = 3999233) B3999233
theorem B7109747 : Blo 2105435 7109747 := bstep (se 1 (by rfl) ⟨5332310, by rfl⟩ : syracuseStep 7109747 = 10664621) B10664621
theorem B4739831 : Blo 2105435 4739831 := bstep (se 1 (by rfl) ⟨3554873, by rfl⟩ : syracuseStep 4739831 = 7109747) B7109747
theorem B3159887 : Blo 2105435 3159887 := bstep (se 1 (by rfl) ⟨2369915, by rfl⟩ : syracuseStep 3159887 = 4739831) B4739831
theorem B2106591 : Blo 2105435 2106591 := bstep (se 1 (by rfl) ⟨1579943, by rfl⟩ : syracuseStep 2106591 = 3159887) B3159887
theorem B3159893 : Blo 2105435 3159893 := bbase (se 9 (by rfl) ⟨9257, by rfl⟩ : syracuseStep 3159893 = 18515) (by norm_num)
theorem B2106595 : Blo 2105435 2106595 := bstep (se 1 (by rfl) ⟨1579946, by rfl⟩ : syracuseStep 2106595 = 3159893) B3159893
theorem B5694245 : Blo 2105435 5694245 := bbase (se 4 (by rfl) ⟨533835, by rfl⟩ : syracuseStep 5694245 = 1067671) (by norm_num)
theorem B3796163 : Blo 2105435 3796163 := bstep (se 1 (by rfl) ⟨2847122, by rfl⟩ : syracuseStep 3796163 = 5694245) B5694245
theorem B2530775 : Blo 2105435 2530775 := bstep (se 1 (by rfl) ⟨1898081, by rfl⟩ : syracuseStep 2530775 = 3796163) B3796163
theorem B6748733 : Blo 2105435 6748733 := bstep (se 3 (by rfl) ⟨1265387, by rfl⟩ : syracuseStep 6748733 = 2530775) B2530775
theorem B4499155 : Blo 2105435 4499155 := bstep (se 1 (by rfl) ⟨3374366, by rfl⟩ : syracuseStep 4499155 = 6748733) B6748733
theorem B5998873 : Blo 2105435 5998873 := bstep (se 2 (by rfl) ⟨2249577, by rfl⟩ : syracuseStep 5998873 = 4499155) B4499155
theorem B7998497 : Blo 2105435 7998497 := bstep (se 2 (by rfl) ⟨2999436, by rfl⟩ : syracuseStep 7998497 = 5998873) B5998873
theorem B5332331 : Blo 2105435 5332331 := bstep (se 1 (by rfl) ⟨3999248, by rfl⟩ : syracuseStep 5332331 = 7998497) B7998497
theorem B3554887 : Blo 2105435 3554887 := bstep (se 1 (by rfl) ⟨2666165, by rfl⟩ : syracuseStep 3554887 = 5332331) B5332331
theorem B4739849 : Blo 2105435 4739849 := bstep (se 2 (by rfl) ⟨1777443, by rfl⟩ : syracuseStep 4739849 = 3554887) B3554887
theorem B3159899 : Blo 2105435 3159899 := bstep (se 1 (by rfl) ⟨2369924, by rfl⟩ : syracuseStep 3159899 = 4739849) B4739849
theorem B2106599 : Blo 2105435 2106599 := bstep (se 1 (by rfl) ⟨1579949, by rfl⟩ : syracuseStep 2106599 = 3159899) B3159899
theorem B2369929 : Blo 2105435 2369929 := bbase (se 2 (by rfl) ⟨888723, by rfl⟩ : syracuseStep 2369929 = 1777447) (by norm_num)
theorem B3159905 : Blo 2105435 3159905 := bstep (se 2 (by rfl) ⟨1184964, by rfl⟩ : syracuseStep 3159905 = 2369929) B2369929
theorem B2106603 : Blo 2105435 2106603 := bstep (se 1 (by rfl) ⟨1579952, by rfl⟩ : syracuseStep 2106603 = 3159905) B3159905
theorem B8541397 : Blo 2105435 8541397 := bbase (se 7 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 8541397 = 200189) (by norm_num)
theorem B11388529 : Blo 2105435 11388529 := bstep (se 2 (by rfl) ⟨4270698, by rfl⟩ : syracuseStep 11388529 = 8541397) B8541397
theorem B60738821 : Blo 2105435 60738821 := bstep (se 4 (by rfl) ⟨5694264, by rfl⟩ : syracuseStep 60738821 = 11388529) B11388529
theorem B40492547 : Blo 2105435 40492547 := bstep (se 1 (by rfl) ⟨30369410, by rfl⟩ : syracuseStep 40492547 = 60738821) B60738821
theorem B26995031 : Blo 2105435 26995031 := bstep (se 1 (by rfl) ⟨20246273, by rfl⟩ : syracuseStep 26995031 = 40492547) B40492547
theorem B17996687 : Blo 2105435 17996687 := bstep (se 1 (by rfl) ⟨13497515, by rfl⟩ : syracuseStep 17996687 = 26995031) B26995031
theorem B11997791 : Blo 2105435 11997791 := bstep (se 1 (by rfl) ⟨8998343, by rfl⟩ : syracuseStep 11997791 = 17996687) B17996687
theorem B7998527 : Blo 2105435 7998527 := bstep (se 1 (by rfl) ⟨5998895, by rfl⟩ : syracuseStep 7998527 = 11997791) B11997791
theorem B5332351 : Blo 2105435 5332351 := bstep (se 1 (by rfl) ⟨3999263, by rfl⟩ : syracuseStep 5332351 = 7998527) B7998527
theorem B7109801 : Blo 2105435 7109801 := bstep (se 2 (by rfl) ⟨2666175, by rfl⟩ : syracuseStep 7109801 = 5332351) B5332351
theorem B4739867 : Blo 2105435 4739867 := bstep (se 1 (by rfl) ⟨3554900, by rfl⟩ : syracuseStep 4739867 = 7109801) B7109801
theorem B3159911 : Blo 2105435 3159911 := bstep (se 1 (by rfl) ⟨2369933, by rfl⟩ : syracuseStep 3159911 = 4739867) B4739867
theorem B2106607 : Blo 2105435 2106607 := bstep (se 1 (by rfl) ⟨1579955, by rfl⟩ : syracuseStep 2106607 = 3159911) B3159911
theorem B3159917 : Blo 2105435 3159917 := bbase (se 3 (by rfl) ⟨592484, by rfl⟩ : syracuseStep 3159917 = 1184969) (by norm_num)
theorem B2106611 : Blo 2105435 2106611 := bstep (se 1 (by rfl) ⟨1579958, by rfl⟩ : syracuseStep 2106611 = 3159917) B3159917
theorem B4739885 : Blo 2105435 4739885 := bbase (se 3 (by rfl) ⟨888728, by rfl⟩ : syracuseStep 4739885 = 1777457) (by norm_num)
theorem B3159923 : Blo 2105435 3159923 := bstep (se 1 (by rfl) ⟨2369942, by rfl⟩ : syracuseStep 3159923 = 4739885) B4739885
theorem B2106615 : Blo 2105435 2106615 := bstep (se 1 (by rfl) ⟨1579961, by rfl⟩ : syracuseStep 2106615 = 3159923) B3159923
theorem B2565329 : Blo 2105435 2565329 := bbase (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) (by norm_num)
theorem B6840877 : Blo 2105435 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B9121169 : Blo 2105435 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B6080779 : Blo 2105435 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B8107705 : Blo 2105435 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B10810273 : Blo 2105435 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B14413697 : Blo 2105435 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B9609131 : Blo 2105435 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B25624349 : Blo 2105435 25624349 := bstep (se 3 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 25624349 = 9609131) B9609131
theorem B17082899 : Blo 2105435 17082899 := bstep (se 1 (by rfl) ⟨12812174, by rfl⟩ : syracuseStep 17082899 = 25624349) B25624349
theorem B11388599 : Blo 2105435 11388599 := bstep (se 1 (by rfl) ⟨8541449, by rfl⟩ : syracuseStep 11388599 = 17082899) B17082899
theorem B7592399 : Blo 2105435 7592399 := bstep (se 1 (by rfl) ⟨5694299, by rfl⟩ : syracuseStep 7592399 = 11388599) B11388599
theorem B5061599 : Blo 2105435 5061599 := bstep (se 1 (by rfl) ⟨3796199, by rfl⟩ : syracuseStep 5061599 = 7592399) B7592399
theorem B3374399 : Blo 2105435 3374399 := bstep (se 1 (by rfl) ⟨2530799, by rfl⟩ : syracuseStep 3374399 = 5061599) B5061599
theorem B8998397 : Blo 2105435 8998397 := bstep (se 3 (by rfl) ⟨1687199, by rfl⟩ : syracuseStep 8998397 = 3374399) B3374399
theorem B5998931 : Blo 2105435 5998931 := bstep (se 1 (by rfl) ⟨4499198, by rfl⟩ : syracuseStep 5998931 = 8998397) B8998397
theorem B3999287 : Blo 2105435 3999287 := bstep (se 1 (by rfl) ⟨2999465, by rfl⟩ : syracuseStep 3999287 = 5998931) B5998931
theorem B2666191 : Blo 2105435 2666191 := bstep (se 1 (by rfl) ⟨1999643, by rfl⟩ : syracuseStep 2666191 = 3999287) B3999287
theorem B3554921 : Blo 2105435 3554921 := bstep (se 2 (by rfl) ⟨1333095, by rfl⟩ : syracuseStep 3554921 = 2666191) B2666191
theorem B2369947 : Blo 2105435 2369947 := bstep (se 1 (by rfl) ⟨1777460, by rfl⟩ : syracuseStep 2369947 = 3554921) B3554921
theorem B3159929 : Blo 2105435 3159929 := bstep (se 2 (by rfl) ⟨1184973, by rfl⟩ : syracuseStep 3159929 = 2369947) B2369947
theorem B2106619 : Blo 2105435 2106619 := bstep (se 1 (by rfl) ⟨1579964, by rfl⟩ : syracuseStep 2106619 = 3159929) B3159929
theorem B3796205 : Blo 2105435 3796205 := bbase (se 3 (by rfl) ⟨711788, by rfl⟩ : syracuseStep 3796205 = 1423577) (by norm_num)
theorem B10123213 : Blo 2105435 10123213 := bstep (se 3 (by rfl) ⟨1898102, by rfl⟩ : syracuseStep 10123213 = 3796205) B3796205
theorem B13497617 : Blo 2105435 13497617 := bstep (se 2 (by rfl) ⟨5061606, by rfl⟩ : syracuseStep 13497617 = 10123213) B10123213
theorem B35993645 : Blo 2105435 35993645 := bstep (se 3 (by rfl) ⟨6748808, by rfl⟩ : syracuseStep 35993645 = 13497617) B13497617
theorem B23995763 : Blo 2105435 23995763 := bstep (se 1 (by rfl) ⟨17996822, by rfl⟩ : syracuseStep 23995763 = 35993645) B35993645
theorem B15997175 : Blo 2105435 15997175 := bstep (se 1 (by rfl) ⟨11997881, by rfl⟩ : syracuseStep 15997175 = 23995763) B23995763
theorem B10664783 : Blo 2105435 10664783 := bstep (se 1 (by rfl) ⟨7998587, by rfl⟩ : syracuseStep 10664783 = 15997175) B15997175
theorem B7109855 : Blo 2105435 7109855 := bstep (se 1 (by rfl) ⟨5332391, by rfl⟩ : syracuseStep 7109855 = 10664783) B10664783
theorem B4739903 : Blo 2105435 4739903 := bstep (se 1 (by rfl) ⟨3554927, by rfl⟩ : syracuseStep 4739903 = 7109855) B7109855
theorem B3159935 : Blo 2105435 3159935 := bstep (se 1 (by rfl) ⟨2369951, by rfl⟩ : syracuseStep 3159935 = 4739903) B4739903
theorem B2106623 : Blo 2105435 2106623 := bstep (se 1 (by rfl) ⟨1579967, by rfl⟩ : syracuseStep 2106623 = 3159935) B3159935
theorem B3159941 : Blo 2105435 3159941 := bbase (se 4 (by rfl) ⟨296244, by rfl⟩ : syracuseStep 3159941 = 592489) (by norm_num)
theorem B2106627 : Blo 2105435 2106627 := bstep (se 1 (by rfl) ⟨1579970, by rfl⟩ : syracuseStep 2106627 = 3159941) B3159941
theorem B3554941 : Blo 2105435 3554941 := bbase (se 3 (by rfl) ⟨666551, by rfl⟩ : syracuseStep 3554941 = 1333103) (by norm_num)
theorem B4739921 : Blo 2105435 4739921 := bstep (se 2 (by rfl) ⟨1777470, by rfl⟩ : syracuseStep 4739921 = 3554941) B3554941
theorem B3159947 : Blo 2105435 3159947 := bstep (se 1 (by rfl) ⟨2369960, by rfl⟩ : syracuseStep 3159947 = 4739921) B4739921
theorem B2106631 : Blo 2105435 2106631 := bstep (se 1 (by rfl) ⟨1579973, by rfl⟩ : syracuseStep 2106631 = 3159947) B3159947
theorem B2369965 : Blo 2105435 2369965 := bbase (se 3 (by rfl) ⟨444368, by rfl⟩ : syracuseStep 2369965 = 888737) (by norm_num)
theorem B3159953 : Blo 2105435 3159953 := bstep (se 2 (by rfl) ⟨1184982, by rfl⟩ : syracuseStep 3159953 = 2369965) B2369965
theorem B2106635 : Blo 2105435 2106635 := bstep (se 1 (by rfl) ⟨1579976, by rfl⟩ : syracuseStep 2106635 = 3159953) B3159953
theorem B7109909 : Blo 2105435 7109909 := bbase (se 6 (by rfl) ⟨166638, by rfl⟩ : syracuseStep 7109909 = 333277) (by norm_num)
theorem B4739939 : Blo 2105435 4739939 := bstep (se 1 (by rfl) ⟨3554954, by rfl⟩ : syracuseStep 4739939 = 7109909) B7109909
theorem B3159959 : Blo 2105435 3159959 := bstep (se 1 (by rfl) ⟨2369969, by rfl⟩ : syracuseStep 3159959 = 4739939) B4739939
theorem B2106639 : Blo 2105435 2106639 := bstep (se 1 (by rfl) ⟨1579979, by rfl⟩ : syracuseStep 2106639 = 3159959) B3159959
theorem B3159965 : Blo 2105435 3159965 := bbase (se 3 (by rfl) ⟨592493, by rfl⟩ : syracuseStep 3159965 = 1184987) (by norm_num)
theorem B2106643 : Blo 2105435 2106643 := bstep (se 1 (by rfl) ⟨1579982, by rfl⟩ : syracuseStep 2106643 = 3159965) B3159965
theorem B4739957 : Blo 2105435 4739957 := bbase (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) (by norm_num)
theorem B3159971 : Blo 2105435 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B2106647 : Blo 2105435 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B4804637 : Blo 2105435 4804637 := bbase (se 3 (by rfl) ⟨900869, by rfl⟩ : syracuseStep 4804637 = 1801739) (by norm_num)
theorem B12812365 : Blo 2105435 12812365 := bstep (se 3 (by rfl) ⟨2402318, by rfl⟩ : syracuseStep 12812365 = 4804637) B4804637
theorem B17083153 : Blo 2105435 17083153 := bstep (se 2 (by rfl) ⟨6406182, by rfl⟩ : syracuseStep 17083153 = 12812365) B12812365
theorem B22777537 : Blo 2105435 22777537 := bstep (se 2 (by rfl) ⟨8541576, by rfl⟩ : syracuseStep 22777537 = 17083153) B17083153
theorem B30370049 : Blo 2105435 30370049 := bstep (se 2 (by rfl) ⟨11388768, by rfl⟩ : syracuseStep 30370049 = 22777537) B22777537
theorem B20246699 : Blo 2105435 20246699 := bstep (se 1 (by rfl) ⟨15185024, by rfl⟩ : syracuseStep 20246699 = 30370049) B30370049
theorem B13497799 : Blo 2105435 13497799 := bstep (se 1 (by rfl) ⟨10123349, by rfl⟩ : syracuseStep 13497799 = 20246699) B20246699
theorem B17997065 : Blo 2105435 17997065 := bstep (se 2 (by rfl) ⟨6748899, by rfl⟩ : syracuseStep 17997065 = 13497799) B13497799
theorem B11998043 : Blo 2105435 11998043 := bstep (se 1 (by rfl) ⟨8998532, by rfl⟩ : syracuseStep 11998043 = 17997065) B17997065
theorem B7998695 : Blo 2105435 7998695 := bstep (se 1 (by rfl) ⟨5999021, by rfl⟩ : syracuseStep 7998695 = 11998043) B11998043
theorem B5332463 : Blo 2105435 5332463 := bstep (se 1 (by rfl) ⟨3999347, by rfl⟩ : syracuseStep 5332463 = 7998695) B7998695
theorem B3554975 : Blo 2105435 3554975 := bstep (se 1 (by rfl) ⟨2666231, by rfl⟩ : syracuseStep 3554975 = 5332463) B5332463
theorem B2369983 : Blo 2105435 2369983 := bstep (se 1 (by rfl) ⟨1777487, by rfl⟩ : syracuseStep 2369983 = 3554975) B3554975
theorem B3159977 : Blo 2105435 3159977 := bstep (se 2 (by rfl) ⟨1184991, by rfl⟩ : syracuseStep 3159977 = 2369983) B2369983
theorem B2106651 : Blo 2105435 2106651 := bstep (se 1 (by rfl) ⟨1579988, by rfl⟩ : syracuseStep 2106651 = 3159977) B3159977
theorem B7998709 : Blo 2105435 7998709 := bbase (se 5 (by rfl) ⟨374939, by rfl⟩ : syracuseStep 7998709 = 749879) (by norm_num)
theorem B10664945 : Blo 2105435 10664945 := bstep (se 2 (by rfl) ⟨3999354, by rfl⟩ : syracuseStep 10664945 = 7998709) B7998709
theorem B7109963 : Blo 2105435 7109963 := bstep (se 1 (by rfl) ⟨5332472, by rfl⟩ : syracuseStep 7109963 = 10664945) B10664945
theorem B4739975 : Blo 2105435 4739975 := bstep (se 1 (by rfl) ⟨3554981, by rfl⟩ : syracuseStep 4739975 = 7109963) B7109963
theorem B3159983 : Blo 2105435 3159983 := bstep (se 1 (by rfl) ⟨2369987, by rfl⟩ : syracuseStep 3159983 = 4739975) B4739975
theorem B2106655 : Blo 2105435 2106655 := bstep (se 1 (by rfl) ⟨1579991, by rfl⟩ : syracuseStep 2106655 = 3159983) B3159983
theorem B3159989 : Blo 2105435 3159989 := bbase (se 5 (by rfl) ⟨148124, by rfl⟩ : syracuseStep 3159989 = 296249) (by norm_num)
theorem B2106659 : Blo 2105435 2106659 := bstep (se 1 (by rfl) ⟨1579994, by rfl⟩ : syracuseStep 2106659 = 3159989) B3159989
theorem B5332493 : Blo 2105435 5332493 := bbase (se 3 (by rfl) ⟨999842, by rfl⟩ : syracuseStep 5332493 = 1999685) (by norm_num)
theorem B3554995 : Blo 2105435 3554995 := bstep (se 1 (by rfl) ⟨2666246, by rfl⟩ : syracuseStep 3554995 = 5332493) B5332493
theorem B4739993 : Blo 2105435 4739993 := bstep (se 2 (by rfl) ⟨1777497, by rfl⟩ : syracuseStep 4739993 = 3554995) B3554995
theorem B3159995 : Blo 2105435 3159995 := bstep (se 1 (by rfl) ⟨2369996, by rfl⟩ : syracuseStep 3159995 = 4739993) B4739993
theorem B2106663 : Blo 2105435 2106663 := bstep (se 1 (by rfl) ⟨1579997, by rfl⟩ : syracuseStep 2106663 = 3159995) B3159995
theorem B2370001 : Blo 2105435 2370001 := bbase (se 2 (by rfl) ⟨888750, by rfl⟩ : syracuseStep 2370001 = 1777501) (by norm_num)
theorem B3160001 : Blo 2105435 3160001 := bstep (se 2 (by rfl) ⟨1185000, by rfl⟩ : syracuseStep 3160001 = 2370001) B2370001
theorem B2106667 : Blo 2105435 2106667 := bstep (se 1 (by rfl) ⟨1580000, by rfl⟩ : syracuseStep 2106667 = 3160001) B3160001
theorem B4499309 : Blo 2105435 4499309 := bbase (se 3 (by rfl) ⟨843620, by rfl⟩ : syracuseStep 4499309 = 1687241) (by norm_num)
theorem B2999539 : Blo 2105435 2999539 := bstep (se 1 (by rfl) ⟨2249654, by rfl⟩ : syracuseStep 2999539 = 4499309) B4499309
theorem B3999385 : Blo 2105435 3999385 := bstep (se 2 (by rfl) ⟨1499769, by rfl⟩ : syracuseStep 3999385 = 2999539) B2999539
theorem B5332513 : Blo 2105435 5332513 := bstep (se 2 (by rfl) ⟨1999692, by rfl⟩ : syracuseStep 5332513 = 3999385) B3999385
theorem B7110017 : Blo 2105435 7110017 := bstep (se 2 (by rfl) ⟨2666256, by rfl⟩ : syracuseStep 7110017 = 5332513) B5332513
theorem B4740011 : Blo 2105435 4740011 := bstep (se 1 (by rfl) ⟨3555008, by rfl⟩ : syracuseStep 4740011 = 7110017) B7110017
theorem B3160007 : Blo 2105435 3160007 := bstep (se 1 (by rfl) ⟨2370005, by rfl⟩ : syracuseStep 3160007 = 4740011) B4740011
theorem B2106671 : Blo 2105435 2106671 := bstep (se 1 (by rfl) ⟨1580003, by rfl⟩ : syracuseStep 2106671 = 3160007) B3160007
theorem B3160013 : Blo 2105435 3160013 := bbase (se 3 (by rfl) ⟨592502, by rfl⟩ : syracuseStep 3160013 = 1185005) (by norm_num)
theorem B2106675 : Blo 2105435 2106675 := bstep (se 1 (by rfl) ⟨1580006, by rfl⟩ : syracuseStep 2106675 = 3160013) B3160013
theorem B4740029 : Blo 2105435 4740029 := bbase (se 3 (by rfl) ⟨888755, by rfl⟩ : syracuseStep 4740029 = 1777511) (by norm_num)
theorem B3160019 : Blo 2105435 3160019 := bstep (se 1 (by rfl) ⟨2370014, by rfl⟩ : syracuseStep 3160019 = 4740029) B4740029
theorem B2106679 : Blo 2105435 2106679 := bstep (se 1 (by rfl) ⟨1580009, by rfl⟩ : syracuseStep 2106679 = 3160019) B3160019
theorem B3555029 : Blo 2105435 3555029 := bbase (se 7 (by rfl) ⟨41660, by rfl⟩ : syracuseStep 3555029 = 83321) (by norm_num)
theorem B2370019 : Blo 2105435 2370019 := bstep (se 1 (by rfl) ⟨1777514, by rfl⟩ : syracuseStep 2370019 = 3555029) B3555029
theorem B3160025 : Blo 2105435 3160025 := bstep (se 2 (by rfl) ⟨1185009, by rfl⟩ : syracuseStep 3160025 = 2370019) B2370019
theorem B2106683 : Blo 2105435 2106683 := bstep (se 1 (by rfl) ⟨1580012, by rfl⟩ : syracuseStep 2106683 = 3160025) B3160025
theorem B3603541 : Blo 2105435 3603541 := bbase (se 8 (by rfl) ⟨21114, by rfl⟩ : syracuseStep 3603541 = 42229) (by norm_num)
theorem B4804721 : Blo 2105435 4804721 := bstep (se 2 (by rfl) ⟨1801770, by rfl⟩ : syracuseStep 4804721 = 3603541) B3603541
theorem B3203147 : Blo 2105435 3203147 := bstep (se 1 (by rfl) ⟨2402360, by rfl⟩ : syracuseStep 3203147 = 4804721) B4804721
theorem B2135431 : Blo 2105435 2135431 := bstep (se 1 (by rfl) ⟨1601573, by rfl⟩ : syracuseStep 2135431 = 3203147) B3203147
theorem B2847241 : Blo 2105435 2847241 := bstep (se 2 (by rfl) ⟨1067715, by rfl⟩ : syracuseStep 2847241 = 2135431) B2135431
theorem B3796321 : Blo 2105435 3796321 := bstep (se 2 (by rfl) ⟨1423620, by rfl⟩ : syracuseStep 3796321 = 2847241) B2847241
theorem B5061761 : Blo 2105435 5061761 := bstep (se 2 (by rfl) ⟨1898160, by rfl⟩ : syracuseStep 5061761 = 3796321) B3796321
theorem B3374507 : Blo 2105435 3374507 := bstep (se 1 (by rfl) ⟨2530880, by rfl⟩ : syracuseStep 3374507 = 5061761) B5061761
theorem B8998685 : Blo 2105435 8998685 := bstep (se 3 (by rfl) ⟨1687253, by rfl⟩ : syracuseStep 8998685 = 3374507) B3374507
theorem B5999123 : Blo 2105435 5999123 := bstep (se 1 (by rfl) ⟨4499342, by rfl⟩ : syracuseStep 5999123 = 8998685) B8998685
theorem B15997661 : Blo 2105435 15997661 := bstep (se 3 (by rfl) ⟨2999561, by rfl⟩ : syracuseStep 15997661 = 5999123) B5999123
theorem B10665107 : Blo 2105435 10665107 := bstep (se 1 (by rfl) ⟨7998830, by rfl⟩ : syracuseStep 10665107 = 15997661) B15997661
theorem B7110071 : Blo 2105435 7110071 := bstep (se 1 (by rfl) ⟨5332553, by rfl⟩ : syracuseStep 7110071 = 10665107) B10665107
theorem B4740047 : Blo 2105435 4740047 := bstep (se 1 (by rfl) ⟨3555035, by rfl⟩ : syracuseStep 4740047 = 7110071) B7110071
theorem B3160031 : Blo 2105435 3160031 := bstep (se 1 (by rfl) ⟨2370023, by rfl⟩ : syracuseStep 3160031 = 4740047) B4740047
theorem B2106687 : Blo 2105435 2106687 := bstep (se 1 (by rfl) ⟨1580015, by rfl⟩ : syracuseStep 2106687 = 3160031) B3160031
theorem B3160037 : Blo 2105435 3160037 := bbase (se 4 (by rfl) ⟨296253, by rfl⟩ : syracuseStep 3160037 = 592507) (by norm_num)
theorem B2106691 : Blo 2105435 2106691 := bstep (se 1 (by rfl) ⟨1580018, by rfl⟩ : syracuseStep 2106691 = 3160037) B3160037
theorem B5061781 : Blo 2105435 5061781 := bbase (se 6 (by rfl) ⟨118635, by rfl⟩ : syracuseStep 5061781 = 237271) (by norm_num)
theorem B6749041 : Blo 2105435 6749041 := bstep (se 2 (by rfl) ⟨2530890, by rfl⟩ : syracuseStep 6749041 = 5061781) B5061781
theorem B8998721 : Blo 2105435 8998721 := bstep (se 2 (by rfl) ⟨3374520, by rfl⟩ : syracuseStep 8998721 = 6749041) B6749041
theorem B5999147 : Blo 2105435 5999147 := bstep (se 1 (by rfl) ⟨4499360, by rfl⟩ : syracuseStep 5999147 = 8998721) B8998721
theorem B3999431 : Blo 2105435 3999431 := bstep (se 1 (by rfl) ⟨2999573, by rfl⟩ : syracuseStep 3999431 = 5999147) B5999147
theorem B2666287 : Blo 2105435 2666287 := bstep (se 1 (by rfl) ⟨1999715, by rfl⟩ : syracuseStep 2666287 = 3999431) B3999431
theorem B3555049 : Blo 2105435 3555049 := bstep (se 2 (by rfl) ⟨1333143, by rfl⟩ : syracuseStep 3555049 = 2666287) B2666287
theorem B4740065 : Blo 2105435 4740065 := bstep (se 2 (by rfl) ⟨1777524, by rfl⟩ : syracuseStep 4740065 = 3555049) B3555049
theorem B3160043 : Blo 2105435 3160043 := bstep (se 1 (by rfl) ⟨2370032, by rfl⟩ : syracuseStep 3160043 = 4740065) B4740065
theorem B2106695 : Blo 2105435 2106695 := bstep (se 1 (by rfl) ⟨1580021, by rfl⟩ : syracuseStep 2106695 = 3160043) B3160043
theorem B2370037 : Blo 2105435 2370037 := bbase (se 5 (by rfl) ⟨111095, by rfl⟩ : syracuseStep 2370037 = 222191) (by norm_num)
theorem B3160049 : Blo 2105435 3160049 := bstep (se 2 (by rfl) ⟨1185018, by rfl⟩ : syracuseStep 3160049 = 2370037) B2370037
theorem B2106699 : Blo 2105435 2106699 := bstep (se 1 (by rfl) ⟨1580024, by rfl⟩ : syracuseStep 2106699 = 3160049) B3160049
theorem B2666297 : Blo 2105435 2666297 := bbase (se 2 (by rfl) ⟨999861, by rfl⟩ : syracuseStep 2666297 = 1999723) (by norm_num)
theorem B7110125 : Blo 2105435 7110125 := bstep (se 3 (by rfl) ⟨1333148, by rfl⟩ : syracuseStep 7110125 = 2666297) B2666297
theorem B4740083 : Blo 2105435 4740083 := bstep (se 1 (by rfl) ⟨3555062, by rfl⟩ : syracuseStep 4740083 = 7110125) B7110125
theorem B3160055 : Blo 2105435 3160055 := bstep (se 1 (by rfl) ⟨2370041, by rfl⟩ : syracuseStep 3160055 = 4740083) B4740083
theorem B2106703 : Blo 2105435 2106703 := bstep (se 1 (by rfl) ⟨1580027, by rfl⟩ : syracuseStep 2106703 = 3160055) B3160055
theorem B3160061 : Blo 2105435 3160061 := bbase (se 3 (by rfl) ⟨592511, by rfl⟩ : syracuseStep 3160061 = 1185023) (by norm_num)
theorem B2106707 : Blo 2105435 2106707 := bstep (se 1 (by rfl) ⟨1580030, by rfl⟩ : syracuseStep 2106707 = 3160061) B3160061
theorem B4740101 : Blo 2105435 4740101 := bbase (se 4 (by rfl) ⟨444384, by rfl⟩ : syracuseStep 4740101 = 888769) (by norm_num)
theorem B3160067 : Blo 2105435 3160067 := bstep (se 1 (by rfl) ⟨2370050, by rfl⟩ : syracuseStep 3160067 = 4740101) B4740101
theorem B2106711 : Blo 2105435 2106711 := bstep (se 1 (by rfl) ⟨1580033, by rfl⟩ : syracuseStep 2106711 = 3160067) B3160067
theorem B3999469 : Blo 2105435 3999469 := bbase (se 3 (by rfl) ⟨749900, by rfl⟩ : syracuseStep 3999469 = 1499801) (by norm_num)
theorem B5332625 : Blo 2105435 5332625 := bstep (se 2 (by rfl) ⟨1999734, by rfl⟩ : syracuseStep 5332625 = 3999469) B3999469
theorem B3555083 : Blo 2105435 3555083 := bstep (se 1 (by rfl) ⟨2666312, by rfl⟩ : syracuseStep 3555083 = 5332625) B5332625
theorem B2370055 : Blo 2105435 2370055 := bstep (se 1 (by rfl) ⟨1777541, by rfl⟩ : syracuseStep 2370055 = 3555083) B3555083
theorem B3160073 : Blo 2105435 3160073 := bstep (se 2 (by rfl) ⟨1185027, by rfl⟩ : syracuseStep 3160073 = 2370055) B2370055
theorem B2106715 : Blo 2105435 2106715 := bstep (se 1 (by rfl) ⟨1580036, by rfl⟩ : syracuseStep 2106715 = 3160073) B3160073
theorem B10665269 : Blo 2105435 10665269 := bbase (se 5 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 10665269 = 999869) (by norm_num)
theorem B7110179 : Blo 2105435 7110179 := bstep (se 1 (by rfl) ⟨5332634, by rfl⟩ : syracuseStep 7110179 = 10665269) B10665269
theorem B4740119 : Blo 2105435 4740119 := bstep (se 1 (by rfl) ⟨3555089, by rfl⟩ : syracuseStep 4740119 = 7110179) B7110179
theorem B3160079 : Blo 2105435 3160079 := bstep (se 1 (by rfl) ⟨2370059, by rfl⟩ : syracuseStep 3160079 = 4740119) B4740119
theorem B2106719 : Blo 2105435 2106719 := bstep (se 1 (by rfl) ⟨1580039, by rfl⟩ : syracuseStep 2106719 = 3160079) B3160079
theorem B3160085 : Blo 2105435 3160085 := bbase (se 6 (by rfl) ⟨74064, by rfl⟩ : syracuseStep 3160085 = 148129) (by norm_num)
theorem B2106723 : Blo 2105435 2106723 := bstep (se 1 (by rfl) ⟨1580042, by rfl⟩ : syracuseStep 2106723 = 3160085) B3160085
theorem B21621653 : Blo 2105435 21621653 := bbase (se 6 (by rfl) ⟨506757, by rfl⟩ : syracuseStep 21621653 = 1013515) (by norm_num)
theorem B14414435 : Blo 2105435 14414435 := bstep (se 1 (by rfl) ⟨10810826, by rfl⟩ : syracuseStep 14414435 = 21621653) B21621653
theorem B9609623 : Blo 2105435 9609623 := bstep (se 1 (by rfl) ⟨7207217, by rfl⟩ : syracuseStep 9609623 = 14414435) B14414435
theorem B6406415 : Blo 2105435 6406415 := bstep (se 1 (by rfl) ⟨4804811, by rfl⟩ : syracuseStep 6406415 = 9609623) B9609623
theorem B4270943 : Blo 2105435 4270943 := bstep (se 1 (by rfl) ⟨3203207, by rfl⟩ : syracuseStep 4270943 = 6406415) B6406415
theorem B2847295 : Blo 2105435 2847295 := bstep (se 1 (by rfl) ⟨2135471, by rfl⟩ : syracuseStep 2847295 = 4270943) B4270943
theorem B3796393 : Blo 2105435 3796393 := bstep (se 2 (by rfl) ⟨1423647, by rfl⟩ : syracuseStep 3796393 = 2847295) B2847295
theorem B5061857 : Blo 2105435 5061857 := bstep (se 2 (by rfl) ⟨1898196, by rfl⟩ : syracuseStep 5061857 = 3796393) B3796393
theorem B13498285 : Blo 2105435 13498285 := bstep (se 3 (by rfl) ⟨2530928, by rfl⟩ : syracuseStep 13498285 = 5061857) B5061857
theorem B17997713 : Blo 2105435 17997713 := bstep (se 2 (by rfl) ⟨6749142, by rfl⟩ : syracuseStep 17997713 = 13498285) B13498285
theorem B11998475 : Blo 2105435 11998475 := bstep (se 1 (by rfl) ⟨8998856, by rfl⟩ : syracuseStep 11998475 = 17997713) B17997713
theorem B7998983 : Blo 2105435 7998983 := bstep (se 1 (by rfl) ⟨5999237, by rfl⟩ : syracuseStep 7998983 = 11998475) B11998475
theorem B5332655 : Blo 2105435 5332655 := bstep (se 1 (by rfl) ⟨3999491, by rfl⟩ : syracuseStep 5332655 = 7998983) B7998983
theorem B3555103 : Blo 2105435 3555103 := bstep (se 1 (by rfl) ⟨2666327, by rfl⟩ : syracuseStep 3555103 = 5332655) B5332655
theorem B4740137 : Blo 2105435 4740137 := bstep (se 2 (by rfl) ⟨1777551, by rfl⟩ : syracuseStep 4740137 = 3555103) B3555103
theorem B3160091 : Blo 2105435 3160091 := bstep (se 1 (by rfl) ⟨2370068, by rfl⟩ : syracuseStep 3160091 = 4740137) B4740137
theorem B2106727 : Blo 2105435 2106727 := bstep (se 1 (by rfl) ⟨1580045, by rfl⟩ : syracuseStep 2106727 = 3160091) B3160091
theorem B2370073 : Blo 2105435 2370073 := bbase (se 2 (by rfl) ⟨888777, by rfl⟩ : syracuseStep 2370073 = 1777555) (by norm_num)
theorem B3160097 : Blo 2105435 3160097 := bstep (se 2 (by rfl) ⟨1185036, by rfl⟩ : syracuseStep 3160097 = 2370073) B2370073
theorem B2106731 : Blo 2105435 2106731 := bstep (se 1 (by rfl) ⟨1580048, by rfl⟩ : syracuseStep 2106731 = 3160097) B3160097
theorem B7999013 : Blo 2105435 7999013 := bbase (se 4 (by rfl) ⟨749907, by rfl⟩ : syracuseStep 7999013 = 1499815) (by norm_num)
theorem B5332675 : Blo 2105435 5332675 := bstep (se 1 (by rfl) ⟨3999506, by rfl⟩ : syracuseStep 5332675 = 7999013) B7999013
theorem B7110233 : Blo 2105435 7110233 := bstep (se 2 (by rfl) ⟨2666337, by rfl⟩ : syracuseStep 7110233 = 5332675) B5332675
theorem B4740155 : Blo 2105435 4740155 := bstep (se 1 (by rfl) ⟨3555116, by rfl⟩ : syracuseStep 4740155 = 7110233) B7110233
theorem B3160103 : Blo 2105435 3160103 := bstep (se 1 (by rfl) ⟨2370077, by rfl⟩ : syracuseStep 3160103 = 4740155) B4740155
theorem B2106735 : Blo 2105435 2106735 := bstep (se 1 (by rfl) ⟨1580051, by rfl⟩ : syracuseStep 2106735 = 3160103) B3160103
theorem B3160109 : Blo 2105435 3160109 := bbase (se 3 (by rfl) ⟨592520, by rfl⟩ : syracuseStep 3160109 = 1185041) (by norm_num)
theorem B2106739 : Blo 2105435 2106739 := bstep (se 1 (by rfl) ⟨1580054, by rfl⟩ : syracuseStep 2106739 = 3160109) B3160109
theorem B4740173 : Blo 2105435 4740173 := bbase (se 3 (by rfl) ⟨888782, by rfl⟩ : syracuseStep 4740173 = 1777565) (by norm_num)
theorem B3160115 : Blo 2105435 3160115 := bstep (se 1 (by rfl) ⟨2370086, by rfl⟩ : syracuseStep 3160115 = 4740173) B4740173
theorem B2106743 : Blo 2105435 2106743 := bstep (se 1 (by rfl) ⟨1580057, by rfl⟩ : syracuseStep 2106743 = 3160115) B3160115
theorem B2666353 : Blo 2105435 2666353 := bbase (se 2 (by rfl) ⟨999882, by rfl⟩ : syracuseStep 2666353 = 1999765) (by norm_num)
theorem B3555137 : Blo 2105435 3555137 := bstep (se 2 (by rfl) ⟨1333176, by rfl⟩ : syracuseStep 3555137 = 2666353) B2666353
theorem B2370091 : Blo 2105435 2370091 := bstep (se 1 (by rfl) ⟨1777568, by rfl⟩ : syracuseStep 2370091 = 3555137) B3555137
theorem B3160121 : Blo 2105435 3160121 := bstep (se 2 (by rfl) ⟨1185045, by rfl⟩ : syracuseStep 3160121 = 2370091) B2370091
theorem B2106747 : Blo 2105435 2106747 := bstep (se 1 (by rfl) ⟨1580060, by rfl⟩ : syracuseStep 2106747 = 3160121) B3160121
theorem B10123829 : Blo 2105435 10123829 := bbase (se 5 (by rfl) ⟨474554, by rfl⟩ : syracuseStep 10123829 = 949109) (by norm_num)
theorem B6749219 : Blo 2105435 6749219 := bstep (se 1 (by rfl) ⟨5061914, by rfl⟩ : syracuseStep 6749219 = 10123829) B10123829
theorem B4499479 : Blo 2105435 4499479 := bstep (se 1 (by rfl) ⟨3374609, by rfl⟩ : syracuseStep 4499479 = 6749219) B6749219
theorem B23997221 : Blo 2105435 23997221 := bstep (se 4 (by rfl) ⟨2249739, by rfl⟩ : syracuseStep 23997221 = 4499479) B4499479
theorem B15998147 : Blo 2105435 15998147 := bstep (se 1 (by rfl) ⟨11998610, by rfl⟩ : syracuseStep 15998147 = 23997221) B23997221
theorem B10665431 : Blo 2105435 10665431 := bstep (se 1 (by rfl) ⟨7999073, by rfl⟩ : syracuseStep 10665431 = 15998147) B15998147
theorem B7110287 : Blo 2105435 7110287 := bstep (se 1 (by rfl) ⟨5332715, by rfl⟩ : syracuseStep 7110287 = 10665431) B10665431
theorem B4740191 : Blo 2105435 4740191 := bstep (se 1 (by rfl) ⟨3555143, by rfl⟩ : syracuseStep 4740191 = 7110287) B7110287
theorem B3160127 : Blo 2105435 3160127 := bstep (se 1 (by rfl) ⟨2370095, by rfl⟩ : syracuseStep 3160127 = 4740191) B4740191
theorem B2106751 : Blo 2105435 2106751 := bstep (se 1 (by rfl) ⟨1580063, by rfl⟩ : syracuseStep 2106751 = 3160127) B3160127
theorem B3160133 : Blo 2105435 3160133 := bbase (se 4 (by rfl) ⟨296262, by rfl⟩ : syracuseStep 3160133 = 592525) (by norm_num)
theorem B2106755 : Blo 2105435 2106755 := bstep (se 1 (by rfl) ⟨1580066, by rfl⟩ : syracuseStep 2106755 = 3160133) B3160133
theorem B3555157 : Blo 2105435 3555157 := bbase (se 9 (by rfl) ⟨10415, by rfl⟩ : syracuseStep 3555157 = 20831) (by norm_num)
theorem B4740209 : Blo 2105435 4740209 := bstep (se 2 (by rfl) ⟨1777578, by rfl⟩ : syracuseStep 4740209 = 3555157) B3555157
theorem B3160139 : Blo 2105435 3160139 := bstep (se 1 (by rfl) ⟨2370104, by rfl⟩ : syracuseStep 3160139 = 4740209) B4740209
theorem B2106759 : Blo 2105435 2106759 := bstep (se 1 (by rfl) ⟨1580069, by rfl⟩ : syracuseStep 2106759 = 3160139) B3160139
theorem B2370109 : Blo 2105435 2370109 := bbase (se 3 (by rfl) ⟨444395, by rfl⟩ : syracuseStep 2370109 = 888791) (by norm_num)
theorem B3160145 : Blo 2105435 3160145 := bstep (se 2 (by rfl) ⟨1185054, by rfl⟩ : syracuseStep 3160145 = 2370109) B2370109
theorem B2106763 : Blo 2105435 2106763 := bstep (se 1 (by rfl) ⟨1580072, by rfl⟩ : syracuseStep 2106763 = 3160145) B3160145
theorem B7110341 : Blo 2105435 7110341 := bbase (se 4 (by rfl) ⟨666594, by rfl⟩ : syracuseStep 7110341 = 1333189) (by norm_num)
theorem B4740227 : Blo 2105435 4740227 := bstep (se 1 (by rfl) ⟨3555170, by rfl⟩ : syracuseStep 4740227 = 7110341) B7110341
theorem B3160151 : Blo 2105435 3160151 := bstep (se 1 (by rfl) ⟨2370113, by rfl⟩ : syracuseStep 3160151 = 4740227) B4740227
theorem B2106767 : Blo 2105435 2106767 := bstep (se 1 (by rfl) ⟨1580075, by rfl⟩ : syracuseStep 2106767 = 3160151) B3160151
theorem B3160157 : Blo 2105435 3160157 := bbase (se 3 (by rfl) ⟨592529, by rfl⟩ : syracuseStep 3160157 = 1185059) (by norm_num)
theorem B2106771 : Blo 2105435 2106771 := bstep (se 1 (by rfl) ⟨1580078, by rfl⟩ : syracuseStep 2106771 = 3160157) B3160157
theorem B4740245 : Blo 2105435 4740245 := bbase (se 6 (by rfl) ⟨111099, by rfl⟩ : syracuseStep 4740245 = 222199) (by norm_num)
theorem B3160163 : Blo 2105435 3160163 := bstep (se 1 (by rfl) ⟨2370122, by rfl⟩ : syracuseStep 3160163 = 4740245) B4740245
theorem B2106775 : Blo 2105435 2106775 := bstep (se 1 (by rfl) ⟨1580081, by rfl⟩ : syracuseStep 2106775 = 3160163) B3160163
theorem B2999693 : Blo 2105435 2999693 := bbase (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) (by norm_num)
theorem B7999181 : Blo 2105435 7999181 := bstep (se 3 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 7999181 = 2999693) B2999693
theorem B5332787 : Blo 2105435 5332787 := bstep (se 1 (by rfl) ⟨3999590, by rfl⟩ : syracuseStep 5332787 = 7999181) B7999181
theorem B3555191 : Blo 2105435 3555191 := bstep (se 1 (by rfl) ⟨2666393, by rfl⟩ : syracuseStep 3555191 = 5332787) B5332787
theorem B2370127 : Blo 2105435 2370127 := bstep (se 1 (by rfl) ⟨1777595, by rfl⟩ : syracuseStep 2370127 = 3555191) B3555191
theorem B3160169 : Blo 2105435 3160169 := bstep (se 2 (by rfl) ⟨1185063, by rfl⟩ : syracuseStep 3160169 = 2370127) B2370127
theorem B2106779 : Blo 2105435 2106779 := bstep (se 1 (by rfl) ⟨1580084, by rfl⟩ : syracuseStep 2106779 = 3160169) B3160169
theorem B4750181 : Blo 2105435 4750181 := bbase (se 4 (by rfl) ⟨445329, by rfl⟩ : syracuseStep 4750181 = 890659) (by norm_num)
theorem B3166787 : Blo 2105435 3166787 := bstep (se 1 (by rfl) ⟨2375090, by rfl⟩ : syracuseStep 3166787 = 4750181) B4750181
theorem B8444765 : Blo 2105435 8444765 := bstep (se 3 (by rfl) ⟨1583393, by rfl⟩ : syracuseStep 8444765 = 3166787) B3166787
theorem B5629843 : Blo 2105435 5629843 := bstep (se 1 (by rfl) ⟨4222382, by rfl⟩ : syracuseStep 5629843 = 8444765) B8444765
theorem B30025829 : Blo 2105435 30025829 := bstep (se 4 (by rfl) ⟨2814921, by rfl⟩ : syracuseStep 30025829 = 5629843) B5629843
theorem B20017219 : Blo 2105435 20017219 := bstep (se 1 (by rfl) ⟨15012914, by rfl⟩ : syracuseStep 20017219 = 30025829) B30025829
theorem B26689625 : Blo 2105435 26689625 := bstep (se 2 (by rfl) ⟨10008609, by rfl⟩ : syracuseStep 26689625 = 20017219) B20017219
theorem B17793083 : Blo 2105435 17793083 := bstep (se 1 (by rfl) ⟨13344812, by rfl⟩ : syracuseStep 17793083 = 26689625) B26689625
theorem B11862055 : Blo 2105435 11862055 := bstep (se 1 (by rfl) ⟨8896541, by rfl⟩ : syracuseStep 11862055 = 17793083) B17793083
theorem B15816073 : Blo 2105435 15816073 := bstep (se 2 (by rfl) ⟨5931027, by rfl⟩ : syracuseStep 15816073 = 11862055) B11862055
theorem B21088097 : Blo 2105435 21088097 := bstep (se 2 (by rfl) ⟨7908036, by rfl⟩ : syracuseStep 21088097 = 15816073) B15816073
theorem B14058731 : Blo 2105435 14058731 := bstep (se 1 (by rfl) ⟨10544048, by rfl⟩ : syracuseStep 14058731 = 21088097) B21088097
theorem B37489949 : Blo 2105435 37489949 := bstep (se 3 (by rfl) ⟨7029365, by rfl⟩ : syracuseStep 37489949 = 14058731) B14058731
theorem B24993299 : Blo 2105435 24993299 := bstep (se 1 (by rfl) ⟨18744974, by rfl⟩ : syracuseStep 24993299 = 37489949) B37489949
theorem B16662199 : Blo 2105435 16662199 := bstep (se 1 (by rfl) ⟨12496649, by rfl⟩ : syracuseStep 16662199 = 24993299) B24993299
theorem B22216265 : Blo 2105435 22216265 := bstep (se 2 (by rfl) ⟨8331099, by rfl⟩ : syracuseStep 22216265 = 16662199) B16662199
theorem B14810843 : Blo 2105435 14810843 := bstep (se 1 (by rfl) ⟨11108132, by rfl⟩ : syracuseStep 14810843 = 22216265) B22216265
theorem B9873895 : Blo 2105435 9873895 := bstep (se 1 (by rfl) ⟨7405421, by rfl⟩ : syracuseStep 9873895 = 14810843) B14810843
theorem B13165193 : Blo 2105435 13165193 := bstep (se 2 (by rfl) ⟨4936947, by rfl⟩ : syracuseStep 13165193 = 9873895) B9873895
theorem B8776795 : Blo 2105435 8776795 := bstep (se 1 (by rfl) ⟨6582596, by rfl⟩ : syracuseStep 8776795 = 13165193) B13165193
theorem B11702393 : Blo 2105435 11702393 := bstep (se 2 (by rfl) ⟨4388397, by rfl⟩ : syracuseStep 11702393 = 8776795) B8776795
theorem B7801595 : Blo 2105435 7801595 := bstep (se 1 (by rfl) ⟨5851196, by rfl⟩ : syracuseStep 7801595 = 11702393) B11702393
theorem B5201063 : Blo 2105435 5201063 := bstep (se 1 (by rfl) ⟨3900797, by rfl⟩ : syracuseStep 5201063 = 7801595) B7801595
theorem B3467375 : Blo 2105435 3467375 := bstep (se 1 (by rfl) ⟨2600531, by rfl⟩ : syracuseStep 3467375 = 5201063) B5201063
theorem B2311583 : Blo 2105435 2311583 := bstep (se 1 (by rfl) ⟨1733687, by rfl⟩ : syracuseStep 2311583 = 3467375) B3467375
theorem B6164221 : Blo 2105435 6164221 := bstep (se 3 (by rfl) ⟨1155791, by rfl⟩ : syracuseStep 6164221 = 2311583) B2311583
theorem B8218961 : Blo 2105435 8218961 := bstep (se 2 (by rfl) ⟨3082110, by rfl⟩ : syracuseStep 8218961 = 6164221) B6164221
theorem B5479307 : Blo 2105435 5479307 := bstep (se 1 (by rfl) ⟨4109480, by rfl⟩ : syracuseStep 5479307 = 8218961) B8218961
theorem B3652871 : Blo 2105435 3652871 := bstep (se 1 (by rfl) ⟨2739653, by rfl⟩ : syracuseStep 3652871 = 5479307) B5479307
theorem B9740989 : Blo 2105435 9740989 := bstep (se 3 (by rfl) ⟨1826435, by rfl⟩ : syracuseStep 9740989 = 3652871) B3652871
theorem B12987985 : Blo 2105435 12987985 := bstep (se 2 (by rfl) ⟨4870494, by rfl⟩ : syracuseStep 12987985 = 9740989) B9740989
theorem B17317313 : Blo 2105435 17317313 := bstep (se 2 (by rfl) ⟨6493992, by rfl⟩ : syracuseStep 17317313 = 12987985) B12987985
theorem B11544875 : Blo 2105435 11544875 := bstep (se 1 (by rfl) ⟨8658656, by rfl⟩ : syracuseStep 11544875 = 17317313) B17317313
theorem B7696583 : Blo 2105435 7696583 := bstep (se 1 (by rfl) ⟨5772437, by rfl⟩ : syracuseStep 7696583 = 11544875) B11544875
theorem B5131055 : Blo 2105435 5131055 := bstep (se 1 (by rfl) ⟨3848291, by rfl⟩ : syracuseStep 5131055 = 7696583) B7696583
theorem B3420703 : Blo 2105435 3420703 := bstep (se 1 (by rfl) ⟨2565527, by rfl⟩ : syracuseStep 3420703 = 5131055) B5131055
theorem B18243749 : Blo 2105435 18243749 := bstep (se 4 (by rfl) ⟨1710351, by rfl⟩ : syracuseStep 18243749 = 3420703) B3420703
theorem B48649997 : Blo 2105435 48649997 := bstep (se 3 (by rfl) ⟨9121874, by rfl⟩ : syracuseStep 48649997 = 18243749) B18243749
theorem B32433331 : Blo 2105435 32433331 := bstep (se 1 (by rfl) ⟨24324998, by rfl⟩ : syracuseStep 32433331 = 48649997) B48649997
theorem B43244441 : Blo 2105435 43244441 := bstep (se 2 (by rfl) ⟨16216665, by rfl⟩ : syracuseStep 43244441 = 32433331) B32433331
theorem B28829627 : Blo 2105435 28829627 := bstep (se 1 (by rfl) ⟨21622220, by rfl⟩ : syracuseStep 28829627 = 43244441) B43244441
theorem B19219751 : Blo 2105435 19219751 := bstep (se 1 (by rfl) ⟨14414813, by rfl⟩ : syracuseStep 19219751 = 28829627) B28829627
theorem B12813167 : Blo 2105435 12813167 := bstep (se 1 (by rfl) ⟨9609875, by rfl⟩ : syracuseStep 12813167 = 19219751) B19219751
theorem B8542111 : Blo 2105435 8542111 := bstep (se 1 (by rfl) ⟨6406583, by rfl⟩ : syracuseStep 8542111 = 12813167) B12813167
theorem B11389481 : Blo 2105435 11389481 := bstep (se 2 (by rfl) ⟨4271055, by rfl⟩ : syracuseStep 11389481 = 8542111) B8542111
theorem B7592987 : Blo 2105435 7592987 := bstep (se 1 (by rfl) ⟨5694740, by rfl⟩ : syracuseStep 7592987 = 11389481) B11389481
theorem B20247965 : Blo 2105435 20247965 := bstep (se 3 (by rfl) ⟨3796493, by rfl⟩ : syracuseStep 20247965 = 7592987) B7592987
theorem B13498643 : Blo 2105435 13498643 := bstep (se 1 (by rfl) ⟨10123982, by rfl⟩ : syracuseStep 13498643 = 20247965) B20247965
theorem B8999095 : Blo 2105435 8999095 := bstep (se 1 (by rfl) ⟨6749321, by rfl⟩ : syracuseStep 8999095 = 13498643) B13498643
theorem B11998793 : Blo 2105435 11998793 := bstep (se 2 (by rfl) ⟨4499547, by rfl⟩ : syracuseStep 11998793 = 8999095) B8999095
theorem B7999195 : Blo 2105435 7999195 := bstep (se 1 (by rfl) ⟨5999396, by rfl⟩ : syracuseStep 7999195 = 11998793) B11998793
theorem B10665593 : Blo 2105435 10665593 := bstep (se 2 (by rfl) ⟨3999597, by rfl⟩ : syracuseStep 10665593 = 7999195) B7999195
theorem B7110395 : Blo 2105435 7110395 := bstep (se 1 (by rfl) ⟨5332796, by rfl⟩ : syracuseStep 7110395 = 10665593) B10665593
theorem B4740263 : Blo 2105435 4740263 := bstep (se 1 (by rfl) ⟨3555197, by rfl⟩ : syracuseStep 4740263 = 7110395) B7110395
theorem B3160175 : Blo 2105435 3160175 := bstep (se 1 (by rfl) ⟨2370131, by rfl⟩ : syracuseStep 3160175 = 4740263) B4740263
theorem B2106783 : Blo 2105435 2106783 := bstep (se 1 (by rfl) ⟨1580087, by rfl⟩ : syracuseStep 2106783 = 3160175) B3160175
theorem B3160181 : Blo 2105435 3160181 := bbase (se 5 (by rfl) ⟨148133, by rfl⟩ : syracuseStep 3160181 = 296267) (by norm_num)
theorem B2106787 : Blo 2105435 2106787 := bstep (se 1 (by rfl) ⟨1580090, by rfl⟩ : syracuseStep 2106787 = 3160181) B3160181
theorem B3999613 : Blo 2105435 3999613 := bbase (se 3 (by rfl) ⟨749927, by rfl⟩ : syracuseStep 3999613 = 1499855) (by norm_num)
theorem B5332817 : Blo 2105435 5332817 := bstep (se 2 (by rfl) ⟨1999806, by rfl⟩ : syracuseStep 5332817 = 3999613) B3999613
theorem B3555211 : Blo 2105435 3555211 := bstep (se 1 (by rfl) ⟨2666408, by rfl⟩ : syracuseStep 3555211 = 5332817) B5332817
theorem B4740281 : Blo 2105435 4740281 := bstep (se 2 (by rfl) ⟨1777605, by rfl⟩ : syracuseStep 4740281 = 3555211) B3555211
theorem B3160187 : Blo 2105435 3160187 := bstep (se 1 (by rfl) ⟨2370140, by rfl⟩ : syracuseStep 3160187 = 4740281) B4740281
theorem B2106791 : Blo 2105435 2106791 := bstep (se 1 (by rfl) ⟨1580093, by rfl⟩ : syracuseStep 2106791 = 3160187) B3160187
theorem B2370145 : Blo 2105435 2370145 := bbase (se 2 (by rfl) ⟨888804, by rfl⟩ : syracuseStep 2370145 = 1777609) (by norm_num)
theorem B3160193 : Blo 2105435 3160193 := bstep (se 2 (by rfl) ⟨1185072, by rfl⟩ : syracuseStep 3160193 = 2370145) B2370145
theorem B2106795 : Blo 2105435 2106795 := bstep (se 1 (by rfl) ⟨1580096, by rfl⟩ : syracuseStep 2106795 = 3160193) B3160193
theorem B5332837 : Blo 2105435 5332837 := bbase (se 4 (by rfl) ⟨499953, by rfl⟩ : syracuseStep 5332837 = 999907) (by norm_num)
theorem B7110449 : Blo 2105435 7110449 := bstep (se 2 (by rfl) ⟨2666418, by rfl⟩ : syracuseStep 7110449 = 5332837) B5332837
theorem B4740299 : Blo 2105435 4740299 := bstep (se 1 (by rfl) ⟨3555224, by rfl⟩ : syracuseStep 4740299 = 7110449) B7110449
theorem B3160199 : Blo 2105435 3160199 := bstep (se 1 (by rfl) ⟨2370149, by rfl⟩ : syracuseStep 3160199 = 4740299) B4740299
theorem B2106799 : Blo 2105435 2106799 := bstep (se 1 (by rfl) ⟨1580099, by rfl⟩ : syracuseStep 2106799 = 3160199) B3160199
theorem B3160205 : Blo 2105435 3160205 := bbase (se 3 (by rfl) ⟨592538, by rfl⟩ : syracuseStep 3160205 = 1185077) (by norm_num)
theorem B2106803 : Blo 2105435 2106803 := bstep (se 1 (by rfl) ⟨1580102, by rfl⟩ : syracuseStep 2106803 = 3160205) B3160205
theorem B4740317 : Blo 2105435 4740317 := bbase (se 3 (by rfl) ⟨888809, by rfl⟩ : syracuseStep 4740317 = 1777619) (by norm_num)
theorem B3160211 : Blo 2105435 3160211 := bstep (se 1 (by rfl) ⟨2370158, by rfl⟩ : syracuseStep 3160211 = 4740317) B4740317
theorem B2106807 : Blo 2105435 2106807 := bstep (se 1 (by rfl) ⟨1580105, by rfl⟩ : syracuseStep 2106807 = 3160211) B3160211
theorem B3555245 : Blo 2105435 3555245 := bbase (se 3 (by rfl) ⟨666608, by rfl⟩ : syracuseStep 3555245 = 1333217) (by norm_num)
theorem B2370163 : Blo 2105435 2370163 := bstep (se 1 (by rfl) ⟨1777622, by rfl⟩ : syracuseStep 2370163 = 3555245) B3555245
theorem B3160217 : Blo 2105435 3160217 := bstep (se 2 (by rfl) ⟨1185081, by rfl⟩ : syracuseStep 3160217 = 2370163) B2370163
theorem B2106811 : Blo 2105435 2106811 := bstep (se 1 (by rfl) ⟨1580108, by rfl⟩ : syracuseStep 2106811 = 3160217) B3160217
theorem B9246469 : Blo 2105435 9246469 := bbase (se 4 (by rfl) ⟨866856, by rfl⟩ : syracuseStep 9246469 = 1733713) (by norm_num)
theorem B12328625 : Blo 2105435 12328625 := bstep (se 2 (by rfl) ⟨4623234, by rfl⟩ : syracuseStep 12328625 = 9246469) B9246469
theorem B8219083 : Blo 2105435 8219083 := bstep (se 1 (by rfl) ⟨6164312, by rfl⟩ : syracuseStep 8219083 = 12328625) B12328625
theorem B10958777 : Blo 2105435 10958777 := bstep (se 2 (by rfl) ⟨4109541, by rfl⟩ : syracuseStep 10958777 = 8219083) B8219083
theorem B7305851 : Blo 2105435 7305851 := bstep (se 1 (by rfl) ⟨5479388, by rfl⟩ : syracuseStep 7305851 = 10958777) B10958777
theorem B4870567 : Blo 2105435 4870567 := bstep (se 1 (by rfl) ⟨3652925, by rfl⟩ : syracuseStep 4870567 = 7305851) B7305851
theorem B6494089 : Blo 2105435 6494089 := bstep (se 2 (by rfl) ⟨2435283, by rfl⟩ : syracuseStep 6494089 = 4870567) B4870567
theorem B8658785 : Blo 2105435 8658785 := bstep (se 2 (by rfl) ⟨3247044, by rfl⟩ : syracuseStep 8658785 = 6494089) B6494089
theorem B23090093 : Blo 2105435 23090093 := bstep (se 3 (by rfl) ⟨4329392, by rfl⟩ : syracuseStep 23090093 = 8658785) B8658785
theorem B15393395 : Blo 2105435 15393395 := bstep (se 1 (by rfl) ⟨11545046, by rfl⟩ : syracuseStep 15393395 = 23090093) B23090093
theorem B10262263 : Blo 2105435 10262263 := bstep (se 1 (by rfl) ⟨7696697, by rfl⟩ : syracuseStep 10262263 = 15393395) B15393395
theorem B13683017 : Blo 2105435 13683017 := bstep (se 2 (by rfl) ⟨5131131, by rfl⟩ : syracuseStep 13683017 = 10262263) B10262263
theorem B9122011 : Blo 2105435 9122011 := bstep (se 1 (by rfl) ⟨6841508, by rfl⟩ : syracuseStep 9122011 = 13683017) B13683017
theorem B48650725 : Blo 2105435 48650725 := bstep (se 4 (by rfl) ⟨4561005, by rfl⟩ : syracuseStep 48650725 = 9122011) B9122011
theorem B259470533 : Blo 2105435 259470533 := bstep (se 4 (by rfl) ⟨24325362, by rfl⟩ : syracuseStep 259470533 = 48650725) B48650725
theorem B172980355 : Blo 2105435 172980355 := bstep (se 1 (by rfl) ⟨129735266, by rfl⟩ : syracuseStep 172980355 = 259470533) B259470533
theorem B230640473 : Blo 2105435 230640473 := bstep (se 2 (by rfl) ⟨86490177, by rfl⟩ : syracuseStep 230640473 = 172980355) B172980355
theorem B153760315 : Blo 2105435 153760315 := bstep (se 1 (by rfl) ⟨115320236, by rfl⟩ : syracuseStep 153760315 = 230640473) B230640473
theorem B205013753 : Blo 2105435 205013753 := bstep (se 2 (by rfl) ⟨76880157, by rfl⟩ : syracuseStep 205013753 = 153760315) B153760315
theorem B136675835 : Blo 2105435 136675835 := bstep (se 1 (by rfl) ⟨102506876, by rfl⟩ : syracuseStep 136675835 = 205013753) B205013753
theorem B91117223 : Blo 2105435 91117223 := bstep (se 1 (by rfl) ⟨68337917, by rfl⟩ : syracuseStep 91117223 = 136675835) B136675835
theorem B60744815 : Blo 2105435 60744815 := bstep (se 1 (by rfl) ⟨45558611, by rfl⟩ : syracuseStep 60744815 = 91117223) B91117223
theorem B40496543 : Blo 2105435 40496543 := bstep (se 1 (by rfl) ⟨30372407, by rfl⟩ : syracuseStep 40496543 = 60744815) B60744815
theorem B26997695 : Blo 2105435 26997695 := bstep (se 1 (by rfl) ⟨20248271, by rfl⟩ : syracuseStep 26997695 = 40496543) B40496543
theorem B17998463 : Blo 2105435 17998463 := bstep (se 1 (by rfl) ⟨13498847, by rfl⟩ : syracuseStep 17998463 = 26997695) B26997695
theorem B11998975 : Blo 2105435 11998975 := bstep (se 1 (by rfl) ⟨8999231, by rfl⟩ : syracuseStep 11998975 = 17998463) B17998463
theorem B15998633 : Blo 2105435 15998633 := bstep (se 2 (by rfl) ⟨5999487, by rfl⟩ : syracuseStep 15998633 = 11998975) B11998975
theorem B10665755 : Blo 2105435 10665755 := bstep (se 1 (by rfl) ⟨7999316, by rfl⟩ : syracuseStep 10665755 = 15998633) B15998633
theorem B7110503 : Blo 2105435 7110503 := bstep (se 1 (by rfl) ⟨5332877, by rfl⟩ : syracuseStep 7110503 = 10665755) B10665755
theorem B4740335 : Blo 2105435 4740335 := bstep (se 1 (by rfl) ⟨3555251, by rfl⟩ : syracuseStep 4740335 = 7110503) B7110503
theorem B3160223 : Blo 2105435 3160223 := bstep (se 1 (by rfl) ⟨2370167, by rfl⟩ : syracuseStep 3160223 = 4740335) B4740335
theorem B2106815 : Blo 2105435 2106815 := bstep (se 1 (by rfl) ⟨1580111, by rfl⟩ : syracuseStep 2106815 = 3160223) B3160223
theorem B3160229 : Blo 2105435 3160229 := bbase (se 4 (by rfl) ⟨296271, by rfl⟩ : syracuseStep 3160229 = 592543) (by norm_num)
theorem B2106819 : Blo 2105435 2106819 := bstep (se 1 (by rfl) ⟨1580114, by rfl⟩ : syracuseStep 2106819 = 3160229) B3160229
theorem B2666449 : Blo 2105435 2666449 := bbase (se 2 (by rfl) ⟨999918, by rfl⟩ : syracuseStep 2666449 = 1999837) (by norm_num)
theorem B3555265 : Blo 2105435 3555265 := bstep (se 2 (by rfl) ⟨1333224, by rfl⟩ : syracuseStep 3555265 = 2666449) B2666449
theorem B4740353 : Blo 2105435 4740353 := bstep (se 2 (by rfl) ⟨1777632, by rfl⟩ : syracuseStep 4740353 = 3555265) B3555265
theorem B3160235 : Blo 2105435 3160235 := bstep (se 1 (by rfl) ⟨2370176, by rfl⟩ : syracuseStep 3160235 = 4740353) B4740353
theorem B2106823 : Blo 2105435 2106823 := bstep (se 1 (by rfl) ⟨1580117, by rfl⟩ : syracuseStep 2106823 = 3160235) B3160235
theorem B2370181 : Blo 2105435 2370181 := bbase (se 4 (by rfl) ⟨222204, by rfl⟩ : syracuseStep 2370181 = 444409) (by norm_num)
theorem B3160241 : Blo 2105435 3160241 := bstep (se 2 (by rfl) ⟨1185090, by rfl⟩ : syracuseStep 3160241 = 2370181) B2370181
theorem B2106827 : Blo 2105435 2106827 := bstep (se 1 (by rfl) ⟨1580120, by rfl⟩ : syracuseStep 2106827 = 3160241) B3160241
theorem B6749477 : Blo 2105435 6749477 := bbase (se 4 (by rfl) ⟨632763, by rfl⟩ : syracuseStep 6749477 = 1265527) (by norm_num)
theorem B4499651 : Blo 2105435 4499651 := bstep (se 1 (by rfl) ⟨3374738, by rfl⟩ : syracuseStep 4499651 = 6749477) B6749477
theorem B2999767 : Blo 2105435 2999767 := bstep (se 1 (by rfl) ⟨2249825, by rfl⟩ : syracuseStep 2999767 = 4499651) B4499651
theorem B3999689 : Blo 2105435 3999689 := bstep (se 2 (by rfl) ⟨1499883, by rfl⟩ : syracuseStep 3999689 = 2999767) B2999767
theorem B2666459 : Blo 2105435 2666459 := bstep (se 1 (by rfl) ⟨1999844, by rfl⟩ : syracuseStep 2666459 = 3999689) B3999689
theorem B7110557 : Blo 2105435 7110557 := bstep (se 3 (by rfl) ⟨1333229, by rfl⟩ : syracuseStep 7110557 = 2666459) B2666459
theorem B4740371 : Blo 2105435 4740371 := bstep (se 1 (by rfl) ⟨3555278, by rfl⟩ : syracuseStep 4740371 = 7110557) B7110557
theorem B3160247 : Blo 2105435 3160247 := bstep (se 1 (by rfl) ⟨2370185, by rfl⟩ : syracuseStep 3160247 = 4740371) B4740371
theorem B2106831 : Blo 2105435 2106831 := bstep (se 1 (by rfl) ⟨1580123, by rfl⟩ : syracuseStep 2106831 = 3160247) B3160247
theorem B3160253 : Blo 2105435 3160253 := bbase (se 3 (by rfl) ⟨592547, by rfl⟩ : syracuseStep 3160253 = 1185095) (by norm_num)
theorem B2106835 : Blo 2105435 2106835 := bstep (se 1 (by rfl) ⟨1580126, by rfl⟩ : syracuseStep 2106835 = 3160253) B3160253
theorem B4740389 : Blo 2105435 4740389 := bbase (se 4 (by rfl) ⟨444411, by rfl⟩ : syracuseStep 4740389 = 888823) (by norm_num)
theorem B3160259 : Blo 2105435 3160259 := bstep (se 1 (by rfl) ⟨2370194, by rfl⟩ : syracuseStep 3160259 = 4740389) B4740389
theorem B2106839 : Blo 2105435 2106839 := bstep (se 1 (by rfl) ⟨1580129, by rfl⟩ : syracuseStep 2106839 = 3160259) B3160259
theorem B5332949 : Blo 2105435 5332949 := bbase (se 7 (by rfl) ⟨62495, by rfl⟩ : syracuseStep 5332949 = 124991) (by norm_num)
theorem B3555299 : Blo 2105435 3555299 := bstep (se 1 (by rfl) ⟨2666474, by rfl⟩ : syracuseStep 3555299 = 5332949) B5332949
theorem B2370199 : Blo 2105435 2370199 := bstep (se 1 (by rfl) ⟨1777649, by rfl⟩ : syracuseStep 2370199 = 3555299) B3555299
theorem B3160265 : Blo 2105435 3160265 := bstep (se 2 (by rfl) ⟨1185099, by rfl⟩ : syracuseStep 3160265 = 2370199) B2370199
theorem B2106843 : Blo 2105435 2106843 := bstep (se 1 (by rfl) ⟨1580132, by rfl⟩ : syracuseStep 2106843 = 3160265) B3160265
theorem B2135593 : Blo 2105435 2135593 := bbase (se 2 (by rfl) ⟨800847, by rfl⟩ : syracuseStep 2135593 = 1601695) (by norm_num)
theorem B2847457 : Blo 2105435 2847457 := bstep (se 2 (by rfl) ⟨1067796, by rfl⟩ : syracuseStep 2847457 = 2135593) B2135593
theorem B15186437 : Blo 2105435 15186437 := bstep (se 4 (by rfl) ⟨1423728, by rfl⟩ : syracuseStep 15186437 = 2847457) B2847457
theorem B10124291 : Blo 2105435 10124291 := bstep (se 1 (by rfl) ⟨7593218, by rfl⟩ : syracuseStep 10124291 = 15186437) B15186437
theorem B6749527 : Blo 2105435 6749527 := bstep (se 1 (by rfl) ⟨5062145, by rfl⟩ : syracuseStep 6749527 = 10124291) B10124291
theorem B8999369 : Blo 2105435 8999369 := bstep (se 2 (by rfl) ⟨3374763, by rfl⟩ : syracuseStep 8999369 = 6749527) B6749527
theorem B5999579 : Blo 2105435 5999579 := bstep (se 1 (by rfl) ⟨4499684, by rfl⟩ : syracuseStep 5999579 = 8999369) B8999369
theorem B3999719 : Blo 2105435 3999719 := bstep (se 1 (by rfl) ⟨2999789, by rfl⟩ : syracuseStep 3999719 = 5999579) B5999579
theorem B10665917 : Blo 2105435 10665917 := bstep (se 3 (by rfl) ⟨1999859, by rfl⟩ : syracuseStep 10665917 = 3999719) B3999719
theorem B7110611 : Blo 2105435 7110611 := bstep (se 1 (by rfl) ⟨5332958, by rfl⟩ : syracuseStep 7110611 = 10665917) B10665917
theorem B4740407 : Blo 2105435 4740407 := bstep (se 1 (by rfl) ⟨3555305, by rfl⟩ : syracuseStep 4740407 = 7110611) B7110611
theorem B3160271 : Blo 2105435 3160271 := bstep (se 1 (by rfl) ⟨2370203, by rfl⟩ : syracuseStep 3160271 = 4740407) B4740407
theorem B2106847 : Blo 2105435 2106847 := bstep (se 1 (by rfl) ⟨1580135, by rfl⟩ : syracuseStep 2106847 = 3160271) B3160271
theorem B3160277 : Blo 2105435 3160277 := bbase (se 7 (by rfl) ⟨37034, by rfl⟩ : syracuseStep 3160277 = 74069) (by norm_num)
theorem B2106851 : Blo 2105435 2106851 := bstep (se 1 (by rfl) ⟨1580138, by rfl⟩ : syracuseStep 2106851 = 3160277) B3160277
theorem B2847469 : Blo 2105435 2847469 := bbase (se 3 (by rfl) ⟨533900, by rfl⟩ : syracuseStep 2847469 = 1067801) (by norm_num)
theorem B3796625 : Blo 2105435 3796625 := bstep (se 2 (by rfl) ⟨1423734, by rfl⟩ : syracuseStep 3796625 = 2847469) B2847469
theorem B2531083 : Blo 2105435 2531083 := bstep (se 1 (by rfl) ⟨1898312, by rfl⟩ : syracuseStep 2531083 = 3796625) B3796625
theorem B3374777 : Blo 2105435 3374777 := bstep (se 2 (by rfl) ⟨1265541, by rfl⟩ : syracuseStep 3374777 = 2531083) B2531083
theorem B2249851 : Blo 2105435 2249851 := bstep (se 1 (by rfl) ⟨1687388, by rfl⟩ : syracuseStep 2249851 = 3374777) B3374777
theorem B2999801 : Blo 2105435 2999801 := bstep (se 2 (by rfl) ⟨1124925, by rfl⟩ : syracuseStep 2999801 = 2249851) B2249851
theorem B7999469 : Blo 2105435 7999469 := bstep (se 3 (by rfl) ⟨1499900, by rfl⟩ : syracuseStep 7999469 = 2999801) B2999801
theorem B5332979 : Blo 2105435 5332979 := bstep (se 1 (by rfl) ⟨3999734, by rfl⟩ : syracuseStep 5332979 = 7999469) B7999469
theorem B3555319 : Blo 2105435 3555319 := bstep (se 1 (by rfl) ⟨2666489, by rfl⟩ : syracuseStep 3555319 = 5332979) B5332979
theorem B4740425 : Blo 2105435 4740425 := bstep (se 2 (by rfl) ⟨1777659, by rfl⟩ : syracuseStep 4740425 = 3555319) B3555319
theorem B3160283 : Blo 2105435 3160283 := bstep (se 1 (by rfl) ⟨2370212, by rfl⟩ : syracuseStep 3160283 = 4740425) B4740425
theorem B2106855 : Blo 2105435 2106855 := bstep (se 1 (by rfl) ⟨1580141, by rfl⟩ : syracuseStep 2106855 = 3160283) B3160283
theorem B2370217 : Blo 2105435 2370217 := bbase (se 2 (by rfl) ⟨888831, by rfl⟩ : syracuseStep 2370217 = 1777663) (by norm_num)
theorem B3160289 : Blo 2105435 3160289 := bstep (se 2 (by rfl) ⟨1185108, by rfl⟩ : syracuseStep 3160289 = 2370217) B2370217
theorem B2106859 : Blo 2105435 2106859 := bstep (se 1 (by rfl) ⟨1580144, by rfl⟩ : syracuseStep 2106859 = 3160289) B3160289
theorem B3374789 : Blo 2105435 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B8999437 : Blo 2105435 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B11999249 : Blo 2105435 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B7999499 : Blo 2105435 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B5332999 : Blo 2105435 5332999 := bstep (se 1 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 5332999 = 7999499) B7999499
theorem B7110665 : Blo 2105435 7110665 := bstep (se 2 (by rfl) ⟨2666499, by rfl⟩ : syracuseStep 7110665 = 5332999) B5332999
theorem B4740443 : Blo 2105435 4740443 := bstep (se 1 (by rfl) ⟨3555332, by rfl⟩ : syracuseStep 4740443 = 7110665) B7110665
theorem B3160295 : Blo 2105435 3160295 := bstep (se 1 (by rfl) ⟨2370221, by rfl⟩ : syracuseStep 3160295 = 4740443) B4740443
theorem B2106863 : Blo 2105435 2106863 := bstep (se 1 (by rfl) ⟨1580147, by rfl⟩ : syracuseStep 2106863 = 3160295) B3160295
theorem B3160301 : Blo 2105435 3160301 := bbase (se 3 (by rfl) ⟨592556, by rfl⟩ : syracuseStep 3160301 = 1185113) (by norm_num)
theorem B2106867 : Blo 2105435 2106867 := bstep (se 1 (by rfl) ⟨1580150, by rfl⟩ : syracuseStep 2106867 = 3160301) B3160301
theorem B4740461 : Blo 2105435 4740461 := bbase (se 3 (by rfl) ⟨888836, by rfl⟩ : syracuseStep 4740461 = 1777673) (by norm_num)
theorem B3160307 : Blo 2105435 3160307 := bstep (se 1 (by rfl) ⟨2370230, by rfl⟩ : syracuseStep 3160307 = 4740461) B4740461
theorem B2106871 : Blo 2105435 2106871 := bstep (se 1 (by rfl) ⟨1580153, by rfl⟩ : syracuseStep 2106871 = 3160307) B3160307
theorem B3999773 : Blo 2105435 3999773 := bbase (se 3 (by rfl) ⟨749957, by rfl⟩ : syracuseStep 3999773 = 1499915) (by norm_num)
theorem B2666515 : Blo 2105435 2666515 := bstep (se 1 (by rfl) ⟨1999886, by rfl⟩ : syracuseStep 2666515 = 3999773) B3999773
theorem B3555353 : Blo 2105435 3555353 := bstep (se 2 (by rfl) ⟨1333257, by rfl⟩ : syracuseStep 3555353 = 2666515) B2666515
theorem B2370235 : Blo 2105435 2370235 := bstep (se 1 (by rfl) ⟨1777676, by rfl⟩ : syracuseStep 2370235 = 3555353) B3555353
theorem B3160313 : Blo 2105435 3160313 := bstep (se 2 (by rfl) ⟨1185117, by rfl⟩ : syracuseStep 3160313 = 2370235) B2370235
theorem B2106875 : Blo 2105435 2106875 := bstep (se 1 (by rfl) ⟨1580156, by rfl⟩ : syracuseStep 2106875 = 3160313) B3160313
theorem B9246757 : Blo 2105435 9246757 := bbase (se 4 (by rfl) ⟨866883, by rfl⟩ : syracuseStep 9246757 = 1733767) (by norm_num)
theorem B12329009 : Blo 2105435 12329009 := bstep (se 2 (by rfl) ⟨4623378, by rfl⟩ : syracuseStep 12329009 = 9246757) B9246757
theorem B8219339 : Blo 2105435 8219339 := bstep (se 1 (by rfl) ⟨6164504, by rfl⟩ : syracuseStep 8219339 = 12329009) B12329009
theorem B5479559 : Blo 2105435 5479559 := bstep (se 1 (by rfl) ⟨4109669, by rfl⟩ : syracuseStep 5479559 = 8219339) B8219339
theorem B3653039 : Blo 2105435 3653039 := bstep (se 1 (by rfl) ⟨2739779, by rfl⟩ : syracuseStep 3653039 = 5479559) B5479559
theorem B2435359 : Blo 2105435 2435359 := bstep (se 1 (by rfl) ⟨1826519, by rfl⟩ : syracuseStep 2435359 = 3653039) B3653039
theorem B3247145 : Blo 2105435 3247145 := bstep (se 2 (by rfl) ⟨1217679, by rfl⟩ : syracuseStep 3247145 = 2435359) B2435359
theorem B2164763 : Blo 2105435 2164763 := bstep (se 1 (by rfl) ⟨1623572, by rfl⟩ : syracuseStep 2164763 = 3247145) B3247145
theorem B5772701 : Blo 2105435 5772701 := bstep (se 3 (by rfl) ⟨1082381, by rfl⟩ : syracuseStep 5772701 = 2164763) B2164763
theorem B3848467 : Blo 2105435 3848467 := bstep (se 1 (by rfl) ⟨2886350, by rfl⟩ : syracuseStep 3848467 = 5772701) B5772701
theorem B5131289 : Blo 2105435 5131289 := bstep (se 2 (by rfl) ⟨1924233, by rfl⟩ : syracuseStep 5131289 = 3848467) B3848467
theorem B3420859 : Blo 2105435 3420859 := bstep (se 1 (by rfl) ⟨2565644, by rfl⟩ : syracuseStep 3420859 = 5131289) B5131289
theorem B4561145 : Blo 2105435 4561145 := bstep (se 2 (by rfl) ⟨1710429, by rfl⟩ : syracuseStep 4561145 = 3420859) B3420859
theorem B3040763 : Blo 2105435 3040763 := bstep (se 1 (by rfl) ⟨2280572, by rfl⟩ : syracuseStep 3040763 = 4561145) B4561145
theorem B32434805 : Blo 2105435 32434805 := bstep (se 5 (by rfl) ⟨1520381, by rfl⟩ : syracuseStep 32434805 = 3040763) B3040763
theorem B21623203 : Blo 2105435 21623203 := bstep (se 1 (by rfl) ⟨16217402, by rfl⟩ : syracuseStep 21623203 = 32434805) B32434805
theorem B28830937 : Blo 2105435 28830937 := bstep (se 2 (by rfl) ⟨10811601, by rfl⟩ : syracuseStep 28830937 = 21623203) B21623203
theorem B38441249 : Blo 2105435 38441249 := bstep (se 2 (by rfl) ⟨14415468, by rfl⟩ : syracuseStep 38441249 = 28830937) B28830937
theorem B25627499 : Blo 2105435 25627499 := bstep (se 1 (by rfl) ⟨19220624, by rfl⟩ : syracuseStep 25627499 = 38441249) B38441249
theorem B17084999 : Blo 2105435 17084999 := bstep (se 1 (by rfl) ⟨12813749, by rfl⟩ : syracuseStep 17084999 = 25627499) B25627499
theorem B11389999 : Blo 2105435 11389999 := bstep (se 1 (by rfl) ⟨8542499, by rfl⟩ : syracuseStep 11389999 = 17084999) B17084999
theorem B15186665 : Blo 2105435 15186665 := bstep (se 2 (by rfl) ⟨5694999, by rfl⟩ : syracuseStep 15186665 = 11389999) B11389999
theorem B10124443 : Blo 2105435 10124443 := bstep (se 1 (by rfl) ⟨7593332, by rfl⟩ : syracuseStep 10124443 = 15186665) B15186665
theorem B53997029 : Blo 2105435 53997029 := bstep (se 4 (by rfl) ⟨5062221, by rfl⟩ : syracuseStep 53997029 = 10124443) B10124443
theorem B35998019 : Blo 2105435 35998019 := bstep (se 1 (by rfl) ⟨26998514, by rfl⟩ : syracuseStep 35998019 = 53997029) B53997029
theorem B23998679 : Blo 2105435 23998679 := bstep (se 1 (by rfl) ⟨17999009, by rfl⟩ : syracuseStep 23998679 = 35998019) B35998019
theorem B15999119 : Blo 2105435 15999119 := bstep (se 1 (by rfl) ⟨11999339, by rfl⟩ : syracuseStep 15999119 = 23998679) B23998679
theorem B10666079 : Blo 2105435 10666079 := bstep (se 1 (by rfl) ⟨7999559, by rfl⟩ : syracuseStep 10666079 = 15999119) B15999119
theorem B7110719 : Blo 2105435 7110719 := bstep (se 1 (by rfl) ⟨5333039, by rfl⟩ : syracuseStep 7110719 = 10666079) B10666079
theorem B4740479 : Blo 2105435 4740479 := bstep (se 1 (by rfl) ⟨3555359, by rfl⟩ : syracuseStep 4740479 = 7110719) B7110719
theorem B3160319 : Blo 2105435 3160319 := bstep (se 1 (by rfl) ⟨2370239, by rfl⟩ : syracuseStep 3160319 = 4740479) B4740479
theorem B2106879 : Blo 2105435 2106879 := bstep (se 1 (by rfl) ⟨1580159, by rfl⟩ : syracuseStep 2106879 = 3160319) B3160319
theorem B3160325 : Blo 2105435 3160325 := bbase (se 4 (by rfl) ⟨296280, by rfl⟩ : syracuseStep 3160325 = 592561) (by norm_num)
theorem B2106883 : Blo 2105435 2106883 := bstep (se 1 (by rfl) ⟨1580162, by rfl⟩ : syracuseStep 2106883 = 3160325) B3160325
theorem B3555373 : Blo 2105435 3555373 := bbase (se 3 (by rfl) ⟨666632, by rfl⟩ : syracuseStep 3555373 = 1333265) (by norm_num)
theorem B4740497 : Blo 2105435 4740497 := bstep (se 2 (by rfl) ⟨1777686, by rfl⟩ : syracuseStep 4740497 = 3555373) B3555373
theorem B3160331 : Blo 2105435 3160331 := bstep (se 1 (by rfl) ⟨2370248, by rfl⟩ : syracuseStep 3160331 = 4740497) B4740497
theorem B2106887 : Blo 2105435 2106887 := bstep (se 1 (by rfl) ⟨1580165, by rfl⟩ : syracuseStep 2106887 = 3160331) B3160331
theorem B2370253 : Blo 2105435 2370253 := bbase (se 3 (by rfl) ⟨444422, by rfl⟩ : syracuseStep 2370253 = 888845) (by norm_num)
theorem B3160337 : Blo 2105435 3160337 := bstep (se 2 (by rfl) ⟨1185126, by rfl⟩ : syracuseStep 3160337 = 2370253) B2370253
theorem B2106891 : Blo 2105435 2106891 := bstep (se 1 (by rfl) ⟨1580168, by rfl⟩ : syracuseStep 2106891 = 3160337) B3160337
theorem B7110773 : Blo 2105435 7110773 := bbase (se 5 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 7110773 = 666635) (by norm_num)
theorem B4740515 : Blo 2105435 4740515 := bstep (se 1 (by rfl) ⟨3555386, by rfl⟩ : syracuseStep 4740515 = 7110773) B7110773
theorem B3160343 : Blo 2105435 3160343 := bstep (se 1 (by rfl) ⟨2370257, by rfl⟩ : syracuseStep 3160343 = 4740515) B4740515
theorem B2106895 : Blo 2105435 2106895 := bstep (se 1 (by rfl) ⟨1580171, by rfl⟩ : syracuseStep 2106895 = 3160343) B3160343
theorem B3160349 : Blo 2105435 3160349 := bbase (se 3 (by rfl) ⟨592565, by rfl⟩ : syracuseStep 3160349 = 1185131) (by norm_num)
theorem B2106899 : Blo 2105435 2106899 := bstep (se 1 (by rfl) ⟨1580174, by rfl⟩ : syracuseStep 2106899 = 3160349) B3160349
theorem B4740533 : Blo 2105435 4740533 := bbase (se 5 (by rfl) ⟨222212, by rfl⟩ : syracuseStep 4740533 = 444425) (by norm_num)
theorem B3160355 : Blo 2105435 3160355 := bstep (se 1 (by rfl) ⟨2370266, by rfl⟩ : syracuseStep 3160355 = 4740533) B4740533
theorem B2106903 : Blo 2105435 2106903 := bstep (se 1 (by rfl) ⟨1580177, by rfl⟩ : syracuseStep 2106903 = 3160355) B3160355
theorem B4499813 : Blo 2105435 4499813 := bbase (se 4 (by rfl) ⟨421857, by rfl⟩ : syracuseStep 4499813 = 843715) (by norm_num)
theorem B11999501 : Blo 2105435 11999501 := bstep (se 3 (by rfl) ⟨2249906, by rfl⟩ : syracuseStep 11999501 = 4499813) B4499813
theorem B7999667 : Blo 2105435 7999667 := bstep (se 1 (by rfl) ⟨5999750, by rfl⟩ : syracuseStep 7999667 = 11999501) B11999501
theorem B5333111 : Blo 2105435 5333111 := bstep (se 1 (by rfl) ⟨3999833, by rfl⟩ : syracuseStep 5333111 = 7999667) B7999667
theorem B3555407 : Blo 2105435 3555407 := bstep (se 1 (by rfl) ⟨2666555, by rfl⟩ : syracuseStep 3555407 = 5333111) B5333111
theorem B2370271 : Blo 2105435 2370271 := bstep (se 1 (by rfl) ⟨1777703, by rfl⟩ : syracuseStep 2370271 = 3555407) B3555407
theorem B3160361 : Blo 2105435 3160361 := bstep (se 2 (by rfl) ⟨1185135, by rfl⟩ : syracuseStep 3160361 = 2370271) B2370271
theorem B2106907 : Blo 2105435 2106907 := bstep (se 1 (by rfl) ⟨1580180, by rfl⟩ : syracuseStep 2106907 = 3160361) B3160361
theorem B4499821 : Blo 2105435 4499821 := bbase (se 3 (by rfl) ⟨843716, by rfl⟩ : syracuseStep 4499821 = 1687433) (by norm_num)
theorem B5999761 : Blo 2105435 5999761 := bstep (se 2 (by rfl) ⟨2249910, by rfl⟩ : syracuseStep 5999761 = 4499821) B4499821
theorem B7999681 : Blo 2105435 7999681 := bstep (se 2 (by rfl) ⟨2999880, by rfl⟩ : syracuseStep 7999681 = 5999761) B5999761
theorem B10666241 : Blo 2105435 10666241 := bstep (se 2 (by rfl) ⟨3999840, by rfl⟩ : syracuseStep 10666241 = 7999681) B7999681
theorem B7110827 : Blo 2105435 7110827 := bstep (se 1 (by rfl) ⟨5333120, by rfl⟩ : syracuseStep 7110827 = 10666241) B10666241
theorem B4740551 : Blo 2105435 4740551 := bstep (se 1 (by rfl) ⟨3555413, by rfl⟩ : syracuseStep 4740551 = 7110827) B7110827
theorem B3160367 : Blo 2105435 3160367 := bstep (se 1 (by rfl) ⟨2370275, by rfl⟩ : syracuseStep 3160367 = 4740551) B4740551
theorem B2106911 : Blo 2105435 2106911 := bstep (se 1 (by rfl) ⟨1580183, by rfl⟩ : syracuseStep 2106911 = 3160367) B3160367
theorem B3160373 : Blo 2105435 3160373 := bbase (se 5 (by rfl) ⟨148142, by rfl⟩ : syracuseStep 3160373 = 296285) (by norm_num)
theorem B2106915 : Blo 2105435 2106915 := bstep (se 1 (by rfl) ⟨1580186, by rfl⟩ : syracuseStep 2106915 = 3160373) B3160373
theorem B5333141 : Blo 2105435 5333141 := bbase (se 6 (by rfl) ⟨124995, by rfl⟩ : syracuseStep 5333141 = 249991) (by norm_num)
theorem B3555427 : Blo 2105435 3555427 := bstep (se 1 (by rfl) ⟨2666570, by rfl⟩ : syracuseStep 3555427 = 5333141) B5333141
theorem B4740569 : Blo 2105435 4740569 := bstep (se 2 (by rfl) ⟨1777713, by rfl⟩ : syracuseStep 4740569 = 3555427) B3555427
theorem B3160379 : Blo 2105435 3160379 := bstep (se 1 (by rfl) ⟨2370284, by rfl⟩ : syracuseStep 3160379 = 4740569) B4740569
theorem B2106919 : Blo 2105435 2106919 := bstep (se 1 (by rfl) ⟨1580189, by rfl⟩ : syracuseStep 2106919 = 3160379) B3160379
theorem B2370289 : Blo 2105435 2370289 := bbase (se 2 (by rfl) ⟨888858, by rfl⟩ : syracuseStep 2370289 = 1777717) (by norm_num)
theorem B3160385 : Blo 2105435 3160385 := bstep (se 2 (by rfl) ⟨1185144, by rfl⟩ : syracuseStep 3160385 = 2370289) B2370289
theorem B2106923 : Blo 2105435 2106923 := bstep (se 1 (by rfl) ⟨1580192, by rfl⟩ : syracuseStep 2106923 = 3160385) B3160385
theorem B4870829 : Blo 2105435 4870829 := bbase (se 3 (by rfl) ⟨913280, by rfl⟩ : syracuseStep 4870829 = 1826561) (by norm_num)
theorem B3247219 : Blo 2105435 3247219 := bstep (se 1 (by rfl) ⟨2435414, by rfl⟩ : syracuseStep 3247219 = 4870829) B4870829
theorem B4329625 : Blo 2105435 4329625 := bstep (se 2 (by rfl) ⟨1623609, by rfl⟩ : syracuseStep 4329625 = 3247219) B3247219
theorem B5772833 : Blo 2105435 5772833 := bstep (se 2 (by rfl) ⟨2164812, by rfl⟩ : syracuseStep 5772833 = 4329625) B4329625
theorem B3848555 : Blo 2105435 3848555 := bstep (se 1 (by rfl) ⟨2886416, by rfl⟩ : syracuseStep 3848555 = 5772833) B5772833
theorem B2565703 : Blo 2105435 2565703 := bstep (se 1 (by rfl) ⟨1924277, by rfl⟩ : syracuseStep 2565703 = 3848555) B3848555
theorem B3420937 : Blo 2105435 3420937 := bstep (se 2 (by rfl) ⟨1282851, by rfl⟩ : syracuseStep 3420937 = 2565703) B2565703
theorem B18244997 : Blo 2105435 18244997 := bstep (se 4 (by rfl) ⟨1710468, by rfl⟩ : syracuseStep 18244997 = 3420937) B3420937
theorem B12163331 : Blo 2105435 12163331 := bstep (se 1 (by rfl) ⟨9122498, by rfl⟩ : syracuseStep 12163331 = 18244997) B18244997
theorem B32435549 : Blo 2105435 32435549 := bstep (se 3 (by rfl) ⟨6081665, by rfl⟩ : syracuseStep 32435549 = 12163331) B12163331
theorem B21623699 : Blo 2105435 21623699 := bstep (se 1 (by rfl) ⟨16217774, by rfl⟩ : syracuseStep 21623699 = 32435549) B32435549
theorem B14415799 : Blo 2105435 14415799 := bstep (se 1 (by rfl) ⟨10811849, by rfl⟩ : syracuseStep 14415799 = 21623699) B21623699
theorem B19221065 : Blo 2105435 19221065 := bstep (se 2 (by rfl) ⟨7207899, by rfl⟩ : syracuseStep 19221065 = 14415799) B14415799
theorem B12814043 : Blo 2105435 12814043 := bstep (se 1 (by rfl) ⟨9610532, by rfl⟩ : syracuseStep 12814043 = 19221065) B19221065
theorem B34170781 : Blo 2105435 34170781 := bstep (se 3 (by rfl) ⟨6407021, by rfl⟩ : syracuseStep 34170781 = 12814043) B12814043
theorem B45561041 : Blo 2105435 45561041 := bstep (se 2 (by rfl) ⟨17085390, by rfl⟩ : syracuseStep 45561041 = 34170781) B34170781
theorem B30374027 : Blo 2105435 30374027 := bstep (se 1 (by rfl) ⟨22780520, by rfl⟩ : syracuseStep 30374027 = 45561041) B45561041
theorem B20249351 : Blo 2105435 20249351 := bstep (se 1 (by rfl) ⟨15187013, by rfl⟩ : syracuseStep 20249351 = 30374027) B30374027
theorem B13499567 : Blo 2105435 13499567 := bstep (se 1 (by rfl) ⟨10124675, by rfl⟩ : syracuseStep 13499567 = 20249351) B20249351
theorem B8999711 : Blo 2105435 8999711 := bstep (se 1 (by rfl) ⟨6749783, by rfl⟩ : syracuseStep 8999711 = 13499567) B13499567
theorem B5999807 : Blo 2105435 5999807 := bstep (se 1 (by rfl) ⟨4499855, by rfl⟩ : syracuseStep 5999807 = 8999711) B8999711
theorem B3999871 : Blo 2105435 3999871 := bstep (se 1 (by rfl) ⟨2999903, by rfl⟩ : syracuseStep 3999871 = 5999807) B5999807
theorem B5333161 : Blo 2105435 5333161 := bstep (se 2 (by rfl) ⟨1999935, by rfl⟩ : syracuseStep 5333161 = 3999871) B3999871
theorem B7110881 : Blo 2105435 7110881 := bstep (se 2 (by rfl) ⟨2666580, by rfl⟩ : syracuseStep 7110881 = 5333161) B5333161
theorem B4740587 : Blo 2105435 4740587 := bstep (se 1 (by rfl) ⟨3555440, by rfl⟩ : syracuseStep 4740587 = 7110881) B7110881
theorem B3160391 : Blo 2105435 3160391 := bstep (se 1 (by rfl) ⟨2370293, by rfl⟩ : syracuseStep 3160391 = 4740587) B4740587
theorem B2106927 : Blo 2105435 2106927 := bstep (se 1 (by rfl) ⟨1580195, by rfl⟩ : syracuseStep 2106927 = 3160391) B3160391
theorem B3160397 : Blo 2105435 3160397 := bbase (se 3 (by rfl) ⟨592574, by rfl⟩ : syracuseStep 3160397 = 1185149) (by norm_num)
theorem B2106931 : Blo 2105435 2106931 := bstep (se 1 (by rfl) ⟨1580198, by rfl⟩ : syracuseStep 2106931 = 3160397) B3160397
theorem B4740605 : Blo 2105435 4740605 := bbase (se 3 (by rfl) ⟨888863, by rfl⟩ : syracuseStep 4740605 = 1777727) (by norm_num)
theorem B3160403 : Blo 2105435 3160403 := bstep (se 1 (by rfl) ⟨2370302, by rfl⟩ : syracuseStep 3160403 = 4740605) B4740605
theorem B2106935 : Blo 2105435 2106935 := bstep (se 1 (by rfl) ⟨1580201, by rfl⟩ : syracuseStep 2106935 = 3160403) B3160403
theorem B3555461 : Blo 2105435 3555461 := bbase (se 4 (by rfl) ⟨333324, by rfl⟩ : syracuseStep 3555461 = 666649) (by norm_num)
theorem B2370307 : Blo 2105435 2370307 := bstep (se 1 (by rfl) ⟨1777730, by rfl⟩ : syracuseStep 2370307 = 3555461) B3555461
theorem B3160409 : Blo 2105435 3160409 := bstep (se 2 (by rfl) ⟨1185153, by rfl⟩ : syracuseStep 3160409 = 2370307) B2370307
theorem B2106939 : Blo 2105435 2106939 := bstep (se 1 (by rfl) ⟨1580204, by rfl⟩ : syracuseStep 2106939 = 3160409) B3160409
theorem B15999605 : Blo 2105435 15999605 := bbase (se 5 (by rfl) ⟨749981, by rfl⟩ : syracuseStep 15999605 = 1499963) (by norm_num)
theorem B10666403 : Blo 2105435 10666403 := bstep (se 1 (by rfl) ⟨7999802, by rfl⟩ : syracuseStep 10666403 = 15999605) B15999605
theorem B7110935 : Blo 2105435 7110935 := bstep (se 1 (by rfl) ⟨5333201, by rfl⟩ : syracuseStep 7110935 = 10666403) B10666403
theorem B4740623 : Blo 2105435 4740623 := bstep (se 1 (by rfl) ⟨3555467, by rfl⟩ : syracuseStep 4740623 = 7110935) B7110935
theorem B3160415 : Blo 2105435 3160415 := bstep (se 1 (by rfl) ⟨2370311, by rfl⟩ : syracuseStep 3160415 = 4740623) B4740623
theorem B2106943 : Blo 2105435 2106943 := bstep (se 1 (by rfl) ⟨1580207, by rfl⟩ : syracuseStep 2106943 = 3160415) B3160415
theorem B3160421 : Blo 2105435 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B2106947 : Blo 2105435 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B3999917 : Blo 2105435 3999917 := bbase (se 3 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 3999917 = 1499969) (by norm_num)
theorem B2666611 : Blo 2105435 2666611 := bstep (se 1 (by rfl) ⟨1999958, by rfl⟩ : syracuseStep 2666611 = 3999917) B3999917
theorem B3555481 : Blo 2105435 3555481 := bstep (se 2 (by rfl) ⟨1333305, by rfl⟩ : syracuseStep 3555481 = 2666611) B2666611
theorem B4740641 : Blo 2105435 4740641 := bstep (se 2 (by rfl) ⟨1777740, by rfl⟩ : syracuseStep 4740641 = 3555481) B3555481
theorem B3160427 : Blo 2105435 3160427 := bstep (se 1 (by rfl) ⟨2370320, by rfl⟩ : syracuseStep 3160427 = 4740641) B4740641
theorem B2106951 : Blo 2105435 2106951 := bstep (se 1 (by rfl) ⟨1580213, by rfl⟩ : syracuseStep 2106951 = 3160427) B3160427
theorem B2370325 : Blo 2105435 2370325 := bbase (se 6 (by rfl) ⟨55554, by rfl⟩ : syracuseStep 2370325 = 111109) (by norm_num)
theorem B3160433 : Blo 2105435 3160433 := bstep (se 2 (by rfl) ⟨1185162, by rfl⟩ : syracuseStep 3160433 = 2370325) B2370325
theorem B2106955 : Blo 2105435 2106955 := bstep (se 1 (by rfl) ⟨1580216, by rfl⟩ : syracuseStep 2106955 = 3160433) B3160433
theorem B2666621 : Blo 2105435 2666621 := bbase (se 3 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 2666621 = 999983) (by norm_num)
theorem B7110989 : Blo 2105435 7110989 := bstep (se 3 (by rfl) ⟨1333310, by rfl⟩ : syracuseStep 7110989 = 2666621) B2666621
theorem B4740659 : Blo 2105435 4740659 := bstep (se 1 (by rfl) ⟨3555494, by rfl⟩ : syracuseStep 4740659 = 7110989) B7110989
theorem B3160439 : Blo 2105435 3160439 := bstep (se 1 (by rfl) ⟨2370329, by rfl⟩ : syracuseStep 3160439 = 4740659) B4740659
theorem B2106959 : Blo 2105435 2106959 := bstep (se 1 (by rfl) ⟨1580219, by rfl⟩ : syracuseStep 2106959 = 3160439) B3160439
theorem B3160445 : Blo 2105435 3160445 := bbase (se 3 (by rfl) ⟨592583, by rfl⟩ : syracuseStep 3160445 = 1185167) (by norm_num)
theorem B2106963 : Blo 2105435 2106963 := bstep (se 1 (by rfl) ⟨1580222, by rfl⟩ : syracuseStep 2106963 = 3160445) B3160445
theorem B4740677 : Blo 2105435 4740677 := bbase (se 4 (by rfl) ⟨444438, by rfl⟩ : syracuseStep 4740677 = 888877) (by norm_num)
theorem B3160451 : Blo 2105435 3160451 := bstep (se 1 (by rfl) ⟨2370338, by rfl⟩ : syracuseStep 3160451 = 4740677) B4740677
theorem B2106967 : Blo 2105435 2106967 := bstep (se 1 (by rfl) ⟨1580225, by rfl⟩ : syracuseStep 2106967 = 3160451) B3160451
theorem B5062445 : Blo 2105435 5062445 := bbase (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) (by norm_num)
theorem B3374963 : Blo 2105435 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B2249975 : Blo 2105435 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B5999933 : Blo 2105435 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B3999955 : Blo 2105435 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B5333273 : Blo 2105435 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B3555515 : Blo 2105435 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B2370343 : Blo 2105435 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B3160457 : Blo 2105435 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B2106971 : Blo 2105435 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B10666565 : Blo 2105435 10666565 := bbase (se 4 (by rfl) ⟨999990, by rfl⟩ : syracuseStep 10666565 = 1999981) (by norm_num)
theorem B7111043 : Blo 2105435 7111043 := bstep (se 1 (by rfl) ⟨5333282, by rfl⟩ : syracuseStep 7111043 = 10666565) B10666565
theorem B4740695 : Blo 2105435 4740695 := bstep (se 1 (by rfl) ⟨3555521, by rfl⟩ : syracuseStep 4740695 = 7111043) B7111043
theorem B3160463 : Blo 2105435 3160463 := bstep (se 1 (by rfl) ⟨2370347, by rfl⟩ : syracuseStep 3160463 = 4740695) B4740695
theorem B2106975 : Blo 2105435 2106975 := bstep (se 1 (by rfl) ⟨1580231, by rfl⟩ : syracuseStep 2106975 = 3160463) B3160463
theorem B3160469 : Blo 2105435 3160469 := bbase (se 6 (by rfl) ⟨74073, by rfl⟩ : syracuseStep 3160469 = 148147) (by norm_num)
theorem B2106979 : Blo 2105435 2106979 := bstep (se 1 (by rfl) ⟨1580234, by rfl⟩ : syracuseStep 2106979 = 3160469) B3160469
theorem B3203597 : Blo 2105435 3203597 := bbase (se 3 (by rfl) ⟨600674, by rfl⟩ : syracuseStep 3203597 = 1201349) (by norm_num)
theorem B2135731 : Blo 2105435 2135731 := bstep (se 1 (by rfl) ⟨1601798, by rfl⟩ : syracuseStep 2135731 = 3203597) B3203597
theorem B2847641 : Blo 2105435 2847641 := bstep (se 2 (by rfl) ⟨1067865, by rfl⟩ : syracuseStep 2847641 = 2135731) B2135731
theorem B7593709 : Blo 2105435 7593709 := bstep (se 3 (by rfl) ⟨1423820, by rfl⟩ : syracuseStep 7593709 = 2847641) B2847641
theorem B10124945 : Blo 2105435 10124945 := bstep (se 2 (by rfl) ⟨3796854, by rfl⟩ : syracuseStep 10124945 = 7593709) B7593709
theorem B6749963 : Blo 2105435 6749963 := bstep (se 1 (by rfl) ⟨5062472, by rfl⟩ : syracuseStep 6749963 = 10124945) B10124945
theorem B4499975 : Blo 2105435 4499975 := bstep (se 1 (by rfl) ⟨3374981, by rfl⟩ : syracuseStep 4499975 = 6749963) B6749963
theorem B11999933 : Blo 2105435 11999933 := bstep (se 3 (by rfl) ⟨2249987, by rfl⟩ : syracuseStep 11999933 = 4499975) B4499975
theorem B7999955 : Blo 2105435 7999955 := bstep (se 1 (by rfl) ⟨5999966, by rfl⟩ : syracuseStep 7999955 = 11999933) B11999933
theorem B5333303 : Blo 2105435 5333303 := bstep (se 1 (by rfl) ⟨3999977, by rfl⟩ : syracuseStep 5333303 = 7999955) B7999955
theorem B3555535 : Blo 2105435 3555535 := bstep (se 1 (by rfl) ⟨2666651, by rfl⟩ : syracuseStep 3555535 = 5333303) B5333303
theorem B4740713 : Blo 2105435 4740713 := bstep (se 2 (by rfl) ⟨1777767, by rfl⟩ : syracuseStep 4740713 = 3555535) B3555535
theorem B3160475 : Blo 2105435 3160475 := bstep (se 1 (by rfl) ⟨2370356, by rfl⟩ : syracuseStep 3160475 = 4740713) B4740713
theorem B2106983 : Blo 2105435 2106983 := bstep (se 1 (by rfl) ⟨1580237, by rfl⟩ : syracuseStep 2106983 = 3160475) B3160475
theorem B2370361 : Blo 2105435 2370361 := bbase (se 2 (by rfl) ⟨888885, by rfl⟩ : syracuseStep 2370361 = 1777771) (by norm_num)
theorem B3160481 : Blo 2105435 3160481 := bstep (se 2 (by rfl) ⟨1185180, by rfl⟩ : syracuseStep 3160481 = 2370361) B2370361
theorem B2106987 : Blo 2105435 2106987 := bstep (se 1 (by rfl) ⟨1580240, by rfl⟩ : syracuseStep 2106987 = 3160481) B3160481
theorem B5999989 : Blo 2105435 5999989 := bbase (se 5 (by rfl) ⟨281249, by rfl⟩ : syracuseStep 5999989 = 562499) (by norm_num)
theorem B7999985 : Blo 2105435 7999985 := bstep (se 2 (by rfl) ⟨2999994, by rfl⟩ : syracuseStep 7999985 = 5999989) B5999989
theorem B5333323 : Blo 2105435 5333323 := bstep (se 1 (by rfl) ⟨3999992, by rfl⟩ : syracuseStep 5333323 = 7999985) B7999985
theorem B7111097 : Blo 2105435 7111097 := bstep (se 2 (by rfl) ⟨2666661, by rfl⟩ : syracuseStep 7111097 = 5333323) B5333323
theorem B4740731 : Blo 2105435 4740731 := bstep (se 1 (by rfl) ⟨3555548, by rfl⟩ : syracuseStep 4740731 = 7111097) B7111097
theorem B3160487 : Blo 2105435 3160487 := bstep (se 1 (by rfl) ⟨2370365, by rfl⟩ : syracuseStep 3160487 = 4740731) B4740731
theorem B2106991 : Blo 2105435 2106991 := bstep (se 1 (by rfl) ⟨1580243, by rfl⟩ : syracuseStep 2106991 = 3160487) B3160487
theorem B3160493 : Blo 2105435 3160493 := bbase (se 3 (by rfl) ⟨592592, by rfl⟩ : syracuseStep 3160493 = 1185185) (by norm_num)
theorem B2106995 : Blo 2105435 2106995 := bstep (se 1 (by rfl) ⟨1580246, by rfl⟩ : syracuseStep 2106995 = 3160493) B3160493
theorem B4740749 : Blo 2105435 4740749 := bbase (se 3 (by rfl) ⟨888890, by rfl⟩ : syracuseStep 4740749 = 1777781) (by norm_num)
theorem B3160499 : Blo 2105435 3160499 := bstep (se 1 (by rfl) ⟨2370374, by rfl⟩ : syracuseStep 3160499 = 4740749) B4740749
theorem B2106999 : Blo 2105435 2106999 := bstep (se 1 (by rfl) ⟨1580249, by rfl⟩ : syracuseStep 2106999 = 3160499) B3160499
theorem B2666677 : Blo 2105435 2666677 := bbase (se 5 (by rfl) ⟨125000, by rfl⟩ : syracuseStep 2666677 = 250001) (by norm_num)
theorem B3555569 : Blo 2105435 3555569 := bstep (se 2 (by rfl) ⟨1333338, by rfl⟩ : syracuseStep 3555569 = 2666677) B2666677
theorem B2370379 : Blo 2105435 2370379 := bstep (se 1 (by rfl) ⟨1777784, by rfl⟩ : syracuseStep 2370379 = 3555569) B3555569
theorem B3160505 : Blo 2105435 3160505 := bstep (se 2 (by rfl) ⟨1185189, by rfl⟩ : syracuseStep 3160505 = 2370379) B2370379
theorem B2107003 : Blo 2105435 2107003 := bstep (se 1 (by rfl) ⟨1580252, by rfl⟩ : syracuseStep 2107003 = 3160505) B3160505
theorem B72982741 : Blo 2105435 72982741 := bbase (se 7 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 72982741 = 1710533) (by norm_num)
theorem B97310321 : Blo 2105435 97310321 := bstep (se 2 (by rfl) ⟨36491370, by rfl⟩ : syracuseStep 97310321 = 72982741) B72982741
theorem B64873547 : Blo 2105435 64873547 := bstep (se 1 (by rfl) ⟨48655160, by rfl⟩ : syracuseStep 64873547 = 97310321) B97310321
theorem B43249031 : Blo 2105435 43249031 := bstep (se 1 (by rfl) ⟨32436773, by rfl⟩ : syracuseStep 43249031 = 64873547) B64873547
theorem B28832687 : Blo 2105435 28832687 := bstep (se 1 (by rfl) ⟨21624515, by rfl⟩ : syracuseStep 28832687 = 43249031) B43249031
theorem B19221791 : Blo 2105435 19221791 := bstep (se 1 (by rfl) ⟨14416343, by rfl⟩ : syracuseStep 19221791 = 28832687) B28832687
theorem B51258109 : Blo 2105435 51258109 := bstep (se 3 (by rfl) ⟨9610895, by rfl⟩ : syracuseStep 51258109 = 19221791) B19221791
theorem B68344145 : Blo 2105435 68344145 := bstep (se 2 (by rfl) ⟨25629054, by rfl⟩ : syracuseStep 68344145 = 51258109) B51258109
theorem B45562763 : Blo 2105435 45562763 := bstep (se 1 (by rfl) ⟨34172072, by rfl⟩ : syracuseStep 45562763 = 68344145) B68344145
theorem B30375175 : Blo 2105435 30375175 := bstep (se 1 (by rfl) ⟨22781381, by rfl⟩ : syracuseStep 30375175 = 45562763) B45562763
theorem B40500233 : Blo 2105435 40500233 := bstep (se 2 (by rfl) ⟨15187587, by rfl⟩ : syracuseStep 40500233 = 30375175) B30375175
theorem B27000155 : Blo 2105435 27000155 := bstep (se 1 (by rfl) ⟨20250116, by rfl⟩ : syracuseStep 27000155 = 40500233) B40500233
theorem B18000103 : Blo 2105435 18000103 := bstep (se 1 (by rfl) ⟨13500077, by rfl⟩ : syracuseStep 18000103 = 27000155) B27000155
theorem B24000137 : Blo 2105435 24000137 := bstep (se 2 (by rfl) ⟨9000051, by rfl⟩ : syracuseStep 24000137 = 18000103) B18000103
theorem B16000091 : Blo 2105435 16000091 := bstep (se 1 (by rfl) ⟨12000068, by rfl⟩ : syracuseStep 16000091 = 24000137) B24000137
theorem B10666727 : Blo 2105435 10666727 := bstep (se 1 (by rfl) ⟨8000045, by rfl⟩ : syracuseStep 10666727 = 16000091) B16000091
theorem B7111151 : Blo 2105435 7111151 := bstep (se 1 (by rfl) ⟨5333363, by rfl⟩ : syracuseStep 7111151 = 10666727) B10666727
theorem B4740767 : Blo 2105435 4740767 := bstep (se 1 (by rfl) ⟨3555575, by rfl⟩ : syracuseStep 4740767 = 7111151) B7111151
theorem B3160511 : Blo 2105435 3160511 := bstep (se 1 (by rfl) ⟨2370383, by rfl⟩ : syracuseStep 3160511 = 4740767) B4740767
theorem B2107007 : Blo 2105435 2107007 := bstep (se 1 (by rfl) ⟨1580255, by rfl⟩ : syracuseStep 2107007 = 3160511) B3160511
theorem B3160517 : Blo 2105435 3160517 := bbase (se 4 (by rfl) ⟨296298, by rfl⟩ : syracuseStep 3160517 = 592597) (by norm_num)
theorem B2107011 : Blo 2105435 2107011 := bstep (se 1 (by rfl) ⟨1580258, by rfl⟩ : syracuseStep 2107011 = 3160517) B3160517
theorem B3555589 : Blo 2105435 3555589 := bbase (se 4 (by rfl) ⟨333336, by rfl⟩ : syracuseStep 3555589 = 666673) (by norm_num)
theorem B4740785 : Blo 2105435 4740785 := bstep (se 2 (by rfl) ⟨1777794, by rfl⟩ : syracuseStep 4740785 = 3555589) B3555589
theorem B3160523 : Blo 2105435 3160523 := bstep (se 1 (by rfl) ⟨2370392, by rfl⟩ : syracuseStep 3160523 = 4740785) B4740785
theorem B2107015 : Blo 2105435 2107015 := bstep (se 1 (by rfl) ⟨1580261, by rfl⟩ : syracuseStep 2107015 = 3160523) B3160523
theorem B2370397 : Blo 2105435 2370397 := bbase (se 3 (by rfl) ⟨444449, by rfl⟩ : syracuseStep 2370397 = 888899) (by norm_num)
theorem B3160529 : Blo 2105435 3160529 := bstep (se 2 (by rfl) ⟨1185198, by rfl⟩ : syracuseStep 3160529 = 2370397) B2370397
theorem B2107019 : Blo 2105435 2107019 := bstep (se 1 (by rfl) ⟨1580264, by rfl⟩ : syracuseStep 2107019 = 3160529) B3160529
theorem B7111205 : Blo 2105435 7111205 := bbase (se 4 (by rfl) ⟨666675, by rfl⟩ : syracuseStep 7111205 = 1333351) (by norm_num)
theorem B4740803 : Blo 2105435 4740803 := bstep (se 1 (by rfl) ⟨3555602, by rfl⟩ : syracuseStep 4740803 = 7111205) B7111205
theorem B3160535 : Blo 2105435 3160535 := bstep (se 1 (by rfl) ⟨2370401, by rfl⟩ : syracuseStep 3160535 = 4740803) B4740803
theorem B2107023 : Blo 2105435 2107023 := bstep (se 1 (by rfl) ⟨1580267, by rfl⟩ : syracuseStep 2107023 = 3160535) B3160535
theorem B3160541 : Blo 2105435 3160541 := bbase (se 3 (by rfl) ⟨592601, by rfl⟩ : syracuseStep 3160541 = 1185203) (by norm_num)
theorem B2107027 : Blo 2105435 2107027 := bstep (se 1 (by rfl) ⟨1580270, by rfl⟩ : syracuseStep 2107027 = 3160541) B3160541
theorem B4740821 : Blo 2105435 4740821 := bbase (se 7 (by rfl) ⟨55556, by rfl⟩ : syracuseStep 4740821 = 111113) (by norm_num)
theorem B3160547 : Blo 2105435 3160547 := bstep (se 1 (by rfl) ⟨2370410, by rfl⟩ : syracuseStep 3160547 = 4740821) B4740821
theorem B2107031 : Blo 2105435 2107031 := bstep (se 1 (by rfl) ⟨1580273, by rfl⟩ : syracuseStep 2107031 = 3160547) B3160547
theorem B3796949 : Blo 2105435 3796949 := bbase (se 7 (by rfl) ⟨44495, by rfl⟩ : syracuseStep 3796949 = 88991) (by norm_num)
theorem B2531299 : Blo 2105435 2531299 := bstep (se 1 (by rfl) ⟨1898474, by rfl⟩ : syracuseStep 2531299 = 3796949) B3796949
theorem B3375065 : Blo 2105435 3375065 := bstep (se 2 (by rfl) ⟨1265649, by rfl⟩ : syracuseStep 3375065 = 2531299) B2531299
theorem B9000173 : Blo 2105435 9000173 := bstep (se 3 (by rfl) ⟨1687532, by rfl⟩ : syracuseStep 9000173 = 3375065) B3375065
theorem B6000115 : Blo 2105435 6000115 := bstep (se 1 (by rfl) ⟨4500086, by rfl⟩ : syracuseStep 6000115 = 9000173) B9000173
theorem B8000153 : Blo 2105435 8000153 := bstep (se 2 (by rfl) ⟨3000057, by rfl⟩ : syracuseStep 8000153 = 6000115) B6000115
theorem B5333435 : Blo 2105435 5333435 := bstep (se 1 (by rfl) ⟨4000076, by rfl⟩ : syracuseStep 5333435 = 8000153) B8000153
theorem B3555623 : Blo 2105435 3555623 := bstep (se 1 (by rfl) ⟨2666717, by rfl⟩ : syracuseStep 3555623 = 5333435) B5333435
theorem B2370415 : Blo 2105435 2370415 := bstep (se 1 (by rfl) ⟨1777811, by rfl⟩ : syracuseStep 2370415 = 3555623) B3555623
theorem B3160553 : Blo 2105435 3160553 := bstep (se 2 (by rfl) ⟨1185207, by rfl⟩ : syracuseStep 3160553 = 2370415) B2370415
theorem B2107035 : Blo 2105435 2107035 := bstep (se 1 (by rfl) ⟨1580276, by rfl⟩ : syracuseStep 2107035 = 3160553) B3160553
theorem B3604141 : Blo 2105435 3604141 := bbase (se 3 (by rfl) ⟨675776, by rfl⟩ : syracuseStep 3604141 = 1351553) (by norm_num)
theorem B19222085 : Blo 2105435 19222085 := bstep (se 4 (by rfl) ⟨1802070, by rfl⟩ : syracuseStep 19222085 = 3604141) B3604141
theorem B12814723 : Blo 2105435 12814723 := bstep (se 1 (by rfl) ⟨9611042, by rfl⟩ : syracuseStep 12814723 = 19222085) B19222085
theorem B17086297 : Blo 2105435 17086297 := bstep (se 2 (by rfl) ⟨6407361, by rfl⟩ : syracuseStep 17086297 = 12814723) B12814723
theorem B22781729 : Blo 2105435 22781729 := bstep (se 2 (by rfl) ⟨8543148, by rfl⟩ : syracuseStep 22781729 = 17086297) B17086297
theorem B15187819 : Blo 2105435 15187819 := bstep (se 1 (by rfl) ⟨11390864, by rfl⟩ : syracuseStep 15187819 = 22781729) B22781729
theorem B20250425 : Blo 2105435 20250425 := bstep (se 2 (by rfl) ⟨7593909, by rfl⟩ : syracuseStep 20250425 = 15187819) B15187819
theorem B13500283 : Blo 2105435 13500283 := bstep (se 1 (by rfl) ⟨10125212, by rfl⟩ : syracuseStep 13500283 = 20250425) B20250425
theorem B18000377 : Blo 2105435 18000377 := bstep (se 2 (by rfl) ⟨6750141, by rfl⟩ : syracuseStep 18000377 = 13500283) B13500283
theorem B12000251 : Blo 2105435 12000251 := bstep (se 1 (by rfl) ⟨9000188, by rfl⟩ : syracuseStep 12000251 = 18000377) B18000377
theorem B8000167 : Blo 2105435 8000167 := bstep (se 1 (by rfl) ⟨6000125, by rfl⟩ : syracuseStep 8000167 = 12000251) B12000251
theorem B10666889 : Blo 2105435 10666889 := bstep (se 2 (by rfl) ⟨4000083, by rfl⟩ : syracuseStep 10666889 = 8000167) B8000167
theorem B7111259 : Blo 2105435 7111259 := bstep (se 1 (by rfl) ⟨5333444, by rfl⟩ : syracuseStep 7111259 = 10666889) B10666889
theorem B4740839 : Blo 2105435 4740839 := bstep (se 1 (by rfl) ⟨3555629, by rfl⟩ : syracuseStep 4740839 = 7111259) B7111259
theorem B3160559 : Blo 2105435 3160559 := bstep (se 1 (by rfl) ⟨2370419, by rfl⟩ : syracuseStep 3160559 = 4740839) B4740839
theorem B2107039 : Blo 2105435 2107039 := bstep (se 1 (by rfl) ⟨1580279, by rfl⟩ : syracuseStep 2107039 = 3160559) B3160559
theorem B3160565 : Blo 2105435 3160565 := bbase (se 5 (by rfl) ⟨148151, by rfl⟩ : syracuseStep 3160565 = 296303) (by norm_num)
theorem B2107043 : Blo 2105435 2107043 := bstep (se 1 (by rfl) ⟨1580282, by rfl⟩ : syracuseStep 2107043 = 3160565) B3160565
theorem B6000149 : Blo 2105435 6000149 := bbase (se 6 (by rfl) ⟨140628, by rfl⟩ : syracuseStep 6000149 = 281257) (by norm_num)
theorem B4000099 : Blo 2105435 4000099 := bstep (se 1 (by rfl) ⟨3000074, by rfl⟩ : syracuseStep 4000099 = 6000149) B6000149
theorem B5333465 : Blo 2105435 5333465 := bstep (se 2 (by rfl) ⟨2000049, by rfl⟩ : syracuseStep 5333465 = 4000099) B4000099
theorem B3555643 : Blo 2105435 3555643 := bstep (se 1 (by rfl) ⟨2666732, by rfl⟩ : syracuseStep 3555643 = 5333465) B5333465
theorem B4740857 : Blo 2105435 4740857 := bstep (se 2 (by rfl) ⟨1777821, by rfl⟩ : syracuseStep 4740857 = 3555643) B3555643
theorem B3160571 : Blo 2105435 3160571 := bstep (se 1 (by rfl) ⟨2370428, by rfl⟩ : syracuseStep 3160571 = 4740857) B4740857
theorem B2107047 : Blo 2105435 2107047 := bstep (se 1 (by rfl) ⟨1580285, by rfl⟩ : syracuseStep 2107047 = 3160571) B3160571
theorem B2370433 : Blo 2105435 2370433 := bbase (se 2 (by rfl) ⟨888912, by rfl⟩ : syracuseStep 2370433 = 1777825) (by norm_num)
theorem B3160577 : Blo 2105435 3160577 := bstep (se 2 (by rfl) ⟨1185216, by rfl⟩ : syracuseStep 3160577 = 2370433) B2370433
theorem B2107051 : Blo 2105435 2107051 := bstep (se 1 (by rfl) ⟨1580288, by rfl⟩ : syracuseStep 2107051 = 3160577) B3160577
theorem B5333485 : Blo 2105435 5333485 := bbase (se 3 (by rfl) ⟨1000028, by rfl⟩ : syracuseStep 5333485 = 2000057) (by norm_num)
theorem B7111313 : Blo 2105435 7111313 := bstep (se 2 (by rfl) ⟨2666742, by rfl⟩ : syracuseStep 7111313 = 5333485) B5333485
theorem B4740875 : Blo 2105435 4740875 := bstep (se 1 (by rfl) ⟨3555656, by rfl⟩ : syracuseStep 4740875 = 7111313) B7111313
theorem B3160583 : Blo 2105435 3160583 := bstep (se 1 (by rfl) ⟨2370437, by rfl⟩ : syracuseStep 3160583 = 4740875) B4740875
theorem B2107055 : Blo 2105435 2107055 := bstep (se 1 (by rfl) ⟨1580291, by rfl⟩ : syracuseStep 2107055 = 3160583) B3160583
theorem B3160589 : Blo 2105435 3160589 := bbase (se 3 (by rfl) ⟨592610, by rfl⟩ : syracuseStep 3160589 = 1185221) (by norm_num)
theorem B2107059 : Blo 2105435 2107059 := bstep (se 1 (by rfl) ⟨1580294, by rfl⟩ : syracuseStep 2107059 = 3160589) B3160589
theorem B4740893 : Blo 2105435 4740893 := bbase (se 3 (by rfl) ⟨888917, by rfl⟩ : syracuseStep 4740893 = 1777835) (by norm_num)
theorem B3160595 : Blo 2105435 3160595 := bstep (se 1 (by rfl) ⟨2370446, by rfl⟩ : syracuseStep 3160595 = 4740893) B4740893
theorem B2107063 : Blo 2105435 2107063 := bstep (se 1 (by rfl) ⟨1580297, by rfl⟩ : syracuseStep 2107063 = 3160595) B3160595
theorem B3555677 : Blo 2105435 3555677 := bbase (se 3 (by rfl) ⟨666689, by rfl⟩ : syracuseStep 3555677 = 1333379) (by norm_num)
theorem B2370451 : Blo 2105435 2370451 := bstep (se 1 (by rfl) ⟨1777838, by rfl⟩ : syracuseStep 2370451 = 3555677) B3555677
theorem B3160601 : Blo 2105435 3160601 := bstep (se 2 (by rfl) ⟨1185225, by rfl⟩ : syracuseStep 3160601 = 2370451) B2370451
theorem B2107067 : Blo 2105435 2107067 := bstep (se 1 (by rfl) ⟨1580300, by rfl⟩ : syracuseStep 2107067 = 3160601) B3160601
theorem B9000325 : Blo 2105435 9000325 := bbase (se 4 (by rfl) ⟨843780, by rfl⟩ : syracuseStep 9000325 = 1687561) (by norm_num)
theorem B12000433 : Blo 2105435 12000433 := bstep (se 2 (by rfl) ⟨4500162, by rfl⟩ : syracuseStep 12000433 = 9000325) B9000325
theorem B16000577 : Blo 2105435 16000577 := bstep (se 2 (by rfl) ⟨6000216, by rfl⟩ : syracuseStep 16000577 = 12000433) B12000433
theorem B10667051 : Blo 2105435 10667051 := bstep (se 1 (by rfl) ⟨8000288, by rfl⟩ : syracuseStep 10667051 = 16000577) B16000577
theorem B7111367 : Blo 2105435 7111367 := bstep (se 1 (by rfl) ⟨5333525, by rfl⟩ : syracuseStep 7111367 = 10667051) B10667051
theorem B4740911 : Blo 2105435 4740911 := bstep (se 1 (by rfl) ⟨3555683, by rfl⟩ : syracuseStep 4740911 = 7111367) B7111367
theorem B3160607 : Blo 2105435 3160607 := bstep (se 1 (by rfl) ⟨2370455, by rfl⟩ : syracuseStep 3160607 = 4740911) B4740911
theorem B2107071 : Blo 2105435 2107071 := bstep (se 1 (by rfl) ⟨1580303, by rfl⟩ : syracuseStep 2107071 = 3160607) B3160607
theorem B3160613 : Blo 2105435 3160613 := bbase (se 4 (by rfl) ⟨296307, by rfl⟩ : syracuseStep 3160613 = 592615) (by norm_num)
theorem B2107075 : Blo 2105435 2107075 := bstep (se 1 (by rfl) ⟨1580306, by rfl⟩ : syracuseStep 2107075 = 3160613) B3160613
theorem B2666773 : Blo 2105435 2666773 := bbase (se 6 (by rfl) ⟨62502, by rfl⟩ : syracuseStep 2666773 = 125005) (by norm_num)
theorem B3555697 : Blo 2105435 3555697 := bstep (se 2 (by rfl) ⟨1333386, by rfl⟩ : syracuseStep 3555697 = 2666773) B2666773
theorem B4740929 : Blo 2105435 4740929 := bstep (se 2 (by rfl) ⟨1777848, by rfl⟩ : syracuseStep 4740929 = 3555697) B3555697
theorem B3160619 : Blo 2105435 3160619 := bstep (se 1 (by rfl) ⟨2370464, by rfl⟩ : syracuseStep 3160619 = 4740929) B4740929
theorem B2107079 : Blo 2105435 2107079 := bstep (se 1 (by rfl) ⟨1580309, by rfl⟩ : syracuseStep 2107079 = 3160619) B3160619
theorem B2370469 : Blo 2105435 2370469 := bbase (se 4 (by rfl) ⟨222231, by rfl⟩ : syracuseStep 2370469 = 444463) (by norm_num)
theorem B3160625 : Blo 2105435 3160625 := bstep (se 2 (by rfl) ⟨1185234, by rfl⟩ : syracuseStep 3160625 = 2370469) B2370469
theorem B2107083 : Blo 2105435 2107083 := bstep (se 1 (by rfl) ⟨1580312, by rfl⟩ : syracuseStep 2107083 = 3160625) B3160625
theorem B10125445 : Blo 2105435 10125445 := bbase (se 4 (by rfl) ⟨949260, by rfl⟩ : syracuseStep 10125445 = 1898521) (by norm_num)
theorem B13500593 : Blo 2105435 13500593 := bstep (se 2 (by rfl) ⟨5062722, by rfl⟩ : syracuseStep 13500593 = 10125445) B10125445
theorem B9000395 : Blo 2105435 9000395 := bstep (se 1 (by rfl) ⟨6750296, by rfl⟩ : syracuseStep 9000395 = 13500593) B13500593
theorem B6000263 : Blo 2105435 6000263 := bstep (se 1 (by rfl) ⟨4500197, by rfl⟩ : syracuseStep 6000263 = 9000395) B9000395
theorem B4000175 : Blo 2105435 4000175 := bstep (se 1 (by rfl) ⟨3000131, by rfl⟩ : syracuseStep 4000175 = 6000263) B6000263
theorem B2666783 : Blo 2105435 2666783 := bstep (se 1 (by rfl) ⟨2000087, by rfl⟩ : syracuseStep 2666783 = 4000175) B4000175
theorem B7111421 : Blo 2105435 7111421 := bstep (se 3 (by rfl) ⟨1333391, by rfl⟩ : syracuseStep 7111421 = 2666783) B2666783
theorem B4740947 : Blo 2105435 4740947 := bstep (se 1 (by rfl) ⟨3555710, by rfl⟩ : syracuseStep 4740947 = 7111421) B7111421
theorem B3160631 : Blo 2105435 3160631 := bstep (se 1 (by rfl) ⟨2370473, by rfl⟩ : syracuseStep 3160631 = 4740947) B4740947
theorem B2107087 : Blo 2105435 2107087 := bstep (se 1 (by rfl) ⟨1580315, by rfl⟩ : syracuseStep 2107087 = 3160631) B3160631
theorem B3160637 : Blo 2105435 3160637 := bbase (se 3 (by rfl) ⟨592619, by rfl⟩ : syracuseStep 3160637 = 1185239) (by norm_num)
theorem B2107091 : Blo 2105435 2107091 := bstep (se 1 (by rfl) ⟨1580318, by rfl⟩ : syracuseStep 2107091 = 3160637) B3160637
theorem B4740965 : Blo 2105435 4740965 := bbase (se 4 (by rfl) ⟨444465, by rfl⟩ : syracuseStep 4740965 = 888931) (by norm_num)
theorem B3160643 : Blo 2105435 3160643 := bstep (se 1 (by rfl) ⟨2370482, by rfl⟩ : syracuseStep 3160643 = 4740965) B4740965
theorem B2107095 : Blo 2105435 2107095 := bstep (se 1 (by rfl) ⟨1580321, by rfl⟩ : syracuseStep 2107095 = 3160643) B3160643
theorem B5333597 : Blo 2105435 5333597 := bbase (se 3 (by rfl) ⟨1000049, by rfl⟩ : syracuseStep 5333597 = 2000099) (by norm_num)
theorem B3555731 : Blo 2105435 3555731 := bstep (se 1 (by rfl) ⟨2666798, by rfl⟩ : syracuseStep 3555731 = 5333597) B5333597
theorem B2370487 : Blo 2105435 2370487 := bstep (se 1 (by rfl) ⟨1777865, by rfl⟩ : syracuseStep 2370487 = 3555731) B3555731
theorem B3160649 : Blo 2105435 3160649 := bstep (se 2 (by rfl) ⟨1185243, by rfl⟩ : syracuseStep 3160649 = 2370487) B2370487
theorem B2107099 : Blo 2105435 2107099 := bstep (se 1 (by rfl) ⟨1580324, by rfl⟩ : syracuseStep 2107099 = 3160649) B3160649
theorem B4000205 : Blo 2105435 4000205 := bbase (se 3 (by rfl) ⟨750038, by rfl⟩ : syracuseStep 4000205 = 1500077) (by norm_num)
theorem B10667213 : Blo 2105435 10667213 := bstep (se 3 (by rfl) ⟨2000102, by rfl⟩ : syracuseStep 10667213 = 4000205) B4000205
theorem B7111475 : Blo 2105435 7111475 := bstep (se 1 (by rfl) ⟨5333606, by rfl⟩ : syracuseStep 7111475 = 10667213) B10667213
theorem B4740983 : Blo 2105435 4740983 := bstep (se 1 (by rfl) ⟨3555737, by rfl⟩ : syracuseStep 4740983 = 7111475) B7111475
theorem B3160655 : Blo 2105435 3160655 := bstep (se 1 (by rfl) ⟨2370491, by rfl⟩ : syracuseStep 3160655 = 4740983) B4740983
theorem B2107103 : Blo 2105435 2107103 := bstep (se 1 (by rfl) ⟨1580327, by rfl⟩ : syracuseStep 2107103 = 3160655) B3160655
theorem B3160661 : Blo 2105435 3160661 := bbase (se 8 (by rfl) ⟨18519, by rfl⟩ : syracuseStep 3160661 = 37039) (by norm_num)
theorem B2107107 : Blo 2105435 2107107 := bstep (se 1 (by rfl) ⟨1580330, by rfl⟩ : syracuseStep 2107107 = 3160661) B3160661
theorem B6750373 : Blo 2105435 6750373 := bbase (se 4 (by rfl) ⟨632847, by rfl⟩ : syracuseStep 6750373 = 1265695) (by norm_num)
theorem B9000497 : Blo 2105435 9000497 := bstep (se 2 (by rfl) ⟨3375186, by rfl⟩ : syracuseStep 9000497 = 6750373) B6750373
theorem B6000331 : Blo 2105435 6000331 := bstep (se 1 (by rfl) ⟨4500248, by rfl⟩ : syracuseStep 6000331 = 9000497) B9000497
theorem B8000441 : Blo 2105435 8000441 := bstep (se 2 (by rfl) ⟨3000165, by rfl⟩ : syracuseStep 8000441 = 6000331) B6000331
theorem B5333627 : Blo 2105435 5333627 := bstep (se 1 (by rfl) ⟨4000220, by rfl⟩ : syracuseStep 5333627 = 8000441) B8000441
theorem B3555751 : Blo 2105435 3555751 := bstep (se 1 (by rfl) ⟨2666813, by rfl⟩ : syracuseStep 3555751 = 5333627) B5333627
theorem B4741001 : Blo 2105435 4741001 := bstep (se 2 (by rfl) ⟨1777875, by rfl⟩ : syracuseStep 4741001 = 3555751) B3555751
theorem B3160667 : Blo 2105435 3160667 := bstep (se 1 (by rfl) ⟨2370500, by rfl⟩ : syracuseStep 3160667 = 4741001) B4741001
theorem B2107111 : Blo 2105435 2107111 := bstep (se 1 (by rfl) ⟨1580333, by rfl⟩ : syracuseStep 2107111 = 3160667) B3160667
theorem B2370505 : Blo 2105435 2370505 := bbase (se 2 (by rfl) ⟨888939, by rfl⟩ : syracuseStep 2370505 = 1777879) (by norm_num)
theorem B3160673 : Blo 2105435 3160673 := bstep (se 2 (by rfl) ⟨1185252, by rfl⟩ : syracuseStep 3160673 = 2370505) B2370505
theorem B2107115 : Blo 2105435 2107115 := bstep (se 1 (by rfl) ⟨1580336, by rfl⟩ : syracuseStep 2107115 = 3160673) B3160673
theorem B6842501 : Blo 2105435 6842501 := bbase (se 4 (by rfl) ⟨641484, by rfl⟩ : syracuseStep 6842501 = 1282969) (by norm_num)
theorem B4561667 : Blo 2105435 4561667 := bstep (se 1 (by rfl) ⟨3421250, by rfl⟩ : syracuseStep 4561667 = 6842501) B6842501
theorem B3041111 : Blo 2105435 3041111 := bstep (se 1 (by rfl) ⟨2280833, by rfl⟩ : syracuseStep 3041111 = 4561667) B4561667
theorem B8109629 : Blo 2105435 8109629 := bstep (se 3 (by rfl) ⟨1520555, by rfl⟩ : syracuseStep 8109629 = 3041111) B3041111
theorem B5406419 : Blo 2105435 5406419 := bstep (se 1 (by rfl) ⟨4054814, by rfl⟩ : syracuseStep 5406419 = 8109629) B8109629
theorem B3604279 : Blo 2105435 3604279 := bstep (se 1 (by rfl) ⟨2703209, by rfl⟩ : syracuseStep 3604279 = 5406419) B5406419
theorem B4805705 : Blo 2105435 4805705 := bstep (se 2 (by rfl) ⟨1802139, by rfl⟩ : syracuseStep 4805705 = 3604279) B3604279
theorem B3203803 : Blo 2105435 3203803 := bstep (se 1 (by rfl) ⟨2402852, by rfl⟩ : syracuseStep 3203803 = 4805705) B4805705
theorem B17086949 : Blo 2105435 17086949 := bstep (se 4 (by rfl) ⟨1601901, by rfl⟩ : syracuseStep 17086949 = 3203803) B3203803
theorem B11391299 : Blo 2105435 11391299 := bstep (se 1 (by rfl) ⟨8543474, by rfl⟩ : syracuseStep 11391299 = 17086949) B17086949
theorem B7594199 : Blo 2105435 7594199 := bstep (se 1 (by rfl) ⟨5695649, by rfl⟩ : syracuseStep 7594199 = 11391299) B11391299
theorem B5062799 : Blo 2105435 5062799 := bstep (se 1 (by rfl) ⟨3797099, by rfl⟩ : syracuseStep 5062799 = 7594199) B7594199
theorem B3375199 : Blo 2105435 3375199 := bstep (se 1 (by rfl) ⟨2531399, by rfl⟩ : syracuseStep 3375199 = 5062799) B5062799
theorem B18001061 : Blo 2105435 18001061 := bstep (se 4 (by rfl) ⟨1687599, by rfl⟩ : syracuseStep 18001061 = 3375199) B3375199
theorem B12000707 : Blo 2105435 12000707 := bstep (se 1 (by rfl) ⟨9000530, by rfl⟩ : syracuseStep 12000707 = 18001061) B18001061
theorem B8000471 : Blo 2105435 8000471 := bstep (se 1 (by rfl) ⟨6000353, by rfl⟩ : syracuseStep 8000471 = 12000707) B12000707
theorem B5333647 : Blo 2105435 5333647 := bstep (se 1 (by rfl) ⟨4000235, by rfl⟩ : syracuseStep 5333647 = 8000471) B8000471
theorem B7111529 : Blo 2105435 7111529 := bstep (se 2 (by rfl) ⟨2666823, by rfl⟩ : syracuseStep 7111529 = 5333647) B5333647
theorem B4741019 : Blo 2105435 4741019 := bstep (se 1 (by rfl) ⟨3555764, by rfl⟩ : syracuseStep 4741019 = 7111529) B7111529
theorem B3160679 : Blo 2105435 3160679 := bstep (se 1 (by rfl) ⟨2370509, by rfl⟩ : syracuseStep 3160679 = 4741019) B4741019
theorem B2107119 : Blo 2105435 2107119 := bstep (se 1 (by rfl) ⟨1580339, by rfl⟩ : syracuseStep 2107119 = 3160679) B3160679
theorem B3160685 : Blo 2105435 3160685 := bbase (se 3 (by rfl) ⟨592628, by rfl⟩ : syracuseStep 3160685 = 1185257) (by norm_num)
theorem B2107123 : Blo 2105435 2107123 := bstep (se 1 (by rfl) ⟨1580342, by rfl⟩ : syracuseStep 2107123 = 3160685) B3160685
theorem B4741037 : Blo 2105435 4741037 := bbase (se 3 (by rfl) ⟨888944, by rfl⟩ : syracuseStep 4741037 = 1777889) (by norm_num)
theorem B3160691 : Blo 2105435 3160691 := bstep (se 1 (by rfl) ⟨2370518, by rfl⟩ : syracuseStep 3160691 = 4741037) B4741037
theorem B2107127 : Blo 2105435 2107127 := bstep (se 1 (by rfl) ⟨1580345, by rfl⟩ : syracuseStep 2107127 = 3160691) B3160691
theorem B6000389 : Blo 2105435 6000389 := bbase (se 4 (by rfl) ⟨562536, by rfl⟩ : syracuseStep 6000389 = 1125073) (by norm_num)
theorem B4000259 : Blo 2105435 4000259 := bstep (se 1 (by rfl) ⟨3000194, by rfl⟩ : syracuseStep 4000259 = 6000389) B6000389
theorem B2666839 : Blo 2105435 2666839 := bstep (se 1 (by rfl) ⟨2000129, by rfl⟩ : syracuseStep 2666839 = 4000259) B4000259
theorem B3555785 : Blo 2105435 3555785 := bstep (se 2 (by rfl) ⟨1333419, by rfl⟩ : syracuseStep 3555785 = 2666839) B2666839
theorem B2370523 : Blo 2105435 2370523 := bstep (se 1 (by rfl) ⟨1777892, by rfl⟩ : syracuseStep 2370523 = 3555785) B3555785
theorem B3160697 : Blo 2105435 3160697 := bstep (se 2 (by rfl) ⟨1185261, by rfl⟩ : syracuseStep 3160697 = 2370523) B2370523
theorem B2107131 : Blo 2105435 2107131 := bstep (se 1 (by rfl) ⟨1580348, by rfl⟩ : syracuseStep 2107131 = 3160697) B3160697
theorem B25630613 : Blo 2105435 25630613 := bbase (se 6 (by rfl) ⟨600717, by rfl⟩ : syracuseStep 25630613 = 1201435) (by norm_num)
theorem B17087075 : Blo 2105435 17087075 := bstep (se 1 (by rfl) ⟨12815306, by rfl⟩ : syracuseStep 17087075 = 25630613) B25630613
theorem B11391383 : Blo 2105435 11391383 := bstep (se 1 (by rfl) ⟨8543537, by rfl⟩ : syracuseStep 11391383 = 17087075) B17087075
theorem B7594255 : Blo 2105435 7594255 := bstep (se 1 (by rfl) ⟨5695691, by rfl⟩ : syracuseStep 7594255 = 11391383) B11391383
theorem B40502693 : Blo 2105435 40502693 := bstep (se 4 (by rfl) ⟨3797127, by rfl⟩ : syracuseStep 40502693 = 7594255) B7594255
theorem B27001795 : Blo 2105435 27001795 := bstep (se 1 (by rfl) ⟨20251346, by rfl⟩ : syracuseStep 27001795 = 40502693) B40502693
theorem B36002393 : Blo 2105435 36002393 := bstep (se 2 (by rfl) ⟨13500897, by rfl⟩ : syracuseStep 36002393 = 27001795) B27001795
theorem B24001595 : Blo 2105435 24001595 := bstep (se 1 (by rfl) ⟨18001196, by rfl⟩ : syracuseStep 24001595 = 36002393) B36002393
theorem B16001063 : Blo 2105435 16001063 := bstep (se 1 (by rfl) ⟨12000797, by rfl⟩ : syracuseStep 16001063 = 24001595) B24001595
theorem B10667375 : Blo 2105435 10667375 := bstep (se 1 (by rfl) ⟨8000531, by rfl⟩ : syracuseStep 10667375 = 16001063) B16001063
theorem B7111583 : Blo 2105435 7111583 := bstep (se 1 (by rfl) ⟨5333687, by rfl⟩ : syracuseStep 7111583 = 10667375) B10667375
theorem B4741055 : Blo 2105435 4741055 := bstep (se 1 (by rfl) ⟨3555791, by rfl⟩ : syracuseStep 4741055 = 7111583) B7111583
theorem B3160703 : Blo 2105435 3160703 := bstep (se 1 (by rfl) ⟨2370527, by rfl⟩ : syracuseStep 3160703 = 4741055) B4741055
theorem B2107135 : Blo 2105435 2107135 := bstep (se 1 (by rfl) ⟨1580351, by rfl⟩ : syracuseStep 2107135 = 3160703) B3160703
theorem B3160709 : Blo 2105435 3160709 := bbase (se 4 (by rfl) ⟨296316, by rfl⟩ : syracuseStep 3160709 = 592633) (by norm_num)
theorem B2107139 : Blo 2105435 2107139 := bstep (se 1 (by rfl) ⟨1580354, by rfl⟩ : syracuseStep 2107139 = 3160709) B3160709
theorem B3555805 : Blo 2105435 3555805 := bbase (se 3 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 3555805 = 1333427) (by norm_num)
theorem B4741073 : Blo 2105435 4741073 := bstep (se 2 (by rfl) ⟨1777902, by rfl⟩ : syracuseStep 4741073 = 3555805) B3555805
theorem B3160715 : Blo 2105435 3160715 := bstep (se 1 (by rfl) ⟨2370536, by rfl⟩ : syracuseStep 3160715 = 4741073) B4741073
theorem B2107143 : Blo 2105435 2107143 := bstep (se 1 (by rfl) ⟨1580357, by rfl⟩ : syracuseStep 2107143 = 3160715) B3160715
theorem B2370541 : Blo 2105435 2370541 := bbase (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) (by norm_num)
theorem B3160721 : Blo 2105435 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B2107147 : Blo 2105435 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B7111637 : Blo 2105435 7111637 := bbase (se 7 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 7111637 = 166679) (by norm_num)
theorem B4741091 : Blo 2105435 4741091 := bstep (se 1 (by rfl) ⟨3555818, by rfl⟩ : syracuseStep 4741091 = 7111637) B7111637
theorem B3160727 : Blo 2105435 3160727 := bstep (se 1 (by rfl) ⟨2370545, by rfl⟩ : syracuseStep 3160727 = 4741091) B4741091
theorem B2107151 : Blo 2105435 2107151 := bstep (se 1 (by rfl) ⟨1580363, by rfl⟩ : syracuseStep 2107151 = 3160727) B3160727
theorem B3160733 : Blo 2105435 3160733 := bbase (se 3 (by rfl) ⟨592637, by rfl⟩ : syracuseStep 3160733 = 1185275) (by norm_num)
theorem B2107155 : Blo 2105435 2107155 := bstep (se 1 (by rfl) ⟨1580366, by rfl⟩ : syracuseStep 2107155 = 3160733) B3160733
theorem B4741109 : Blo 2105435 4741109 := bbase (se 5 (by rfl) ⟨222239, by rfl⟩ : syracuseStep 4741109 = 444479) (by norm_num)
theorem B3160739 : Blo 2105435 3160739 := bstep (se 1 (by rfl) ⟨2370554, by rfl⟩ : syracuseStep 3160739 = 4741109) B4741109
theorem B2107159 : Blo 2105435 2107159 := bstep (se 1 (by rfl) ⟨1580369, by rfl⟩ : syracuseStep 2107159 = 3160739) B3160739
theorem B2703265 : Blo 2105435 2703265 := bbase (se 2 (by rfl) ⟨1013724, by rfl⟩ : syracuseStep 2703265 = 2027449) (by norm_num)
theorem B57669653 : Blo 2105435 57669653 := bstep (se 6 (by rfl) ⟨1351632, by rfl⟩ : syracuseStep 57669653 = 2703265) B2703265
theorem B38446435 : Blo 2105435 38446435 := bstep (se 1 (by rfl) ⟨28834826, by rfl⟩ : syracuseStep 38446435 = 57669653) B57669653
theorem B51261913 : Blo 2105435 51261913 := bstep (se 2 (by rfl) ⟨19223217, by rfl⟩ : syracuseStep 51261913 = 38446435) B38446435
theorem B68349217 : Blo 2105435 68349217 := bstep (se 2 (by rfl) ⟨25630956, by rfl⟩ : syracuseStep 68349217 = 51261913) B51261913
theorem B91132289 : Blo 2105435 91132289 := bstep (se 2 (by rfl) ⟨34174608, by rfl⟩ : syracuseStep 91132289 = 68349217) B68349217
theorem B60754859 : Blo 2105435 60754859 := bstep (se 1 (by rfl) ⟨45566144, by rfl⟩ : syracuseStep 60754859 = 91132289) B91132289
theorem B40503239 : Blo 2105435 40503239 := bstep (se 1 (by rfl) ⟨30377429, by rfl⟩ : syracuseStep 40503239 = 60754859) B60754859
theorem B27002159 : Blo 2105435 27002159 := bstep (se 1 (by rfl) ⟨20251619, by rfl⟩ : syracuseStep 27002159 = 40503239) B40503239
theorem B18001439 : Blo 2105435 18001439 := bstep (se 1 (by rfl) ⟨13501079, by rfl⟩ : syracuseStep 18001439 = 27002159) B27002159
theorem B12000959 : Blo 2105435 12000959 := bstep (se 1 (by rfl) ⟨9000719, by rfl⟩ : syracuseStep 12000959 = 18001439) B18001439
theorem B8000639 : Blo 2105435 8000639 := bstep (se 1 (by rfl) ⟨6000479, by rfl⟩ : syracuseStep 8000639 = 12000959) B12000959
theorem B5333759 : Blo 2105435 5333759 := bstep (se 1 (by rfl) ⟨4000319, by rfl⟩ : syracuseStep 5333759 = 8000639) B8000639
theorem B3555839 : Blo 2105435 3555839 := bstep (se 1 (by rfl) ⟨2666879, by rfl⟩ : syracuseStep 3555839 = 5333759) B5333759
theorem B2370559 : Blo 2105435 2370559 := bstep (se 1 (by rfl) ⟨1777919, by rfl⟩ : syracuseStep 2370559 = 3555839) B3555839
theorem B3160745 : Blo 2105435 3160745 := bstep (se 2 (by rfl) ⟨1185279, by rfl⟩ : syracuseStep 3160745 = 2370559) B2370559
theorem B2107163 : Blo 2105435 2107163 := bstep (se 1 (by rfl) ⟨1580372, by rfl⟩ : syracuseStep 2107163 = 3160745) B3160745
theorem B3000245 : Blo 2105435 3000245 := bbase (se 5 (by rfl) ⟨140636, by rfl⟩ : syracuseStep 3000245 = 281273) (by norm_num)
theorem B8000653 : Blo 2105435 8000653 := bstep (se 3 (by rfl) ⟨1500122, by rfl⟩ : syracuseStep 8000653 = 3000245) B3000245
theorem B10667537 : Blo 2105435 10667537 := bstep (se 2 (by rfl) ⟨4000326, by rfl⟩ : syracuseStep 10667537 = 8000653) B8000653
theorem B7111691 : Blo 2105435 7111691 := bstep (se 1 (by rfl) ⟨5333768, by rfl⟩ : syracuseStep 7111691 = 10667537) B10667537
theorem B4741127 : Blo 2105435 4741127 := bstep (se 1 (by rfl) ⟨3555845, by rfl⟩ : syracuseStep 4741127 = 7111691) B7111691
theorem B3160751 : Blo 2105435 3160751 := bstep (se 1 (by rfl) ⟨2370563, by rfl⟩ : syracuseStep 3160751 = 4741127) B4741127
theorem B2107167 : Blo 2105435 2107167 := bstep (se 1 (by rfl) ⟨1580375, by rfl⟩ : syracuseStep 2107167 = 3160751) B3160751
theorem B3160757 : Blo 2105435 3160757 := bbase (se 5 (by rfl) ⟨148160, by rfl⟩ : syracuseStep 3160757 = 296321) (by norm_num)
theorem B2107171 : Blo 2105435 2107171 := bstep (se 1 (by rfl) ⟨1580378, by rfl⟩ : syracuseStep 2107171 = 3160757) B3160757
theorem B5333789 : Blo 2105435 5333789 := bbase (se 3 (by rfl) ⟨1000085, by rfl⟩ : syracuseStep 5333789 = 2000171) (by norm_num)
theorem B3555859 : Blo 2105435 3555859 := bstep (se 1 (by rfl) ⟨2666894, by rfl⟩ : syracuseStep 3555859 = 5333789) B5333789
theorem B4741145 : Blo 2105435 4741145 := bstep (se 2 (by rfl) ⟨1777929, by rfl⟩ : syracuseStep 4741145 = 3555859) B3555859
theorem B3160763 : Blo 2105435 3160763 := bstep (se 1 (by rfl) ⟨2370572, by rfl⟩ : syracuseStep 3160763 = 4741145) B4741145
theorem B2107175 : Blo 2105435 2107175 := bstep (se 1 (by rfl) ⟨1580381, by rfl⟩ : syracuseStep 2107175 = 3160763) B3160763
theorem B2370577 : Blo 2105435 2370577 := bbase (se 2 (by rfl) ⟨888966, by rfl⟩ : syracuseStep 2370577 = 1777933) (by norm_num)
theorem B3160769 : Blo 2105435 3160769 := bstep (se 2 (by rfl) ⟨1185288, by rfl⟩ : syracuseStep 3160769 = 2370577) B2370577
theorem B2107179 : Blo 2105435 2107179 := bstep (se 1 (by rfl) ⟨1580384, by rfl⟩ : syracuseStep 2107179 = 3160769) B3160769
theorem B4000357 : Blo 2105435 4000357 := bbase (se 4 (by rfl) ⟨375033, by rfl⟩ : syracuseStep 4000357 = 750067) (by norm_num)
theorem B5333809 : Blo 2105435 5333809 := bstep (se 2 (by rfl) ⟨2000178, by rfl⟩ : syracuseStep 5333809 = 4000357) B4000357
theorem B7111745 : Blo 2105435 7111745 := bstep (se 2 (by rfl) ⟨2666904, by rfl⟩ : syracuseStep 7111745 = 5333809) B5333809
theorem B4741163 : Blo 2105435 4741163 := bstep (se 1 (by rfl) ⟨3555872, by rfl⟩ : syracuseStep 4741163 = 7111745) B7111745
theorem B3160775 : Blo 2105435 3160775 := bstep (se 1 (by rfl) ⟨2370581, by rfl⟩ : syracuseStep 3160775 = 4741163) B4741163
theorem B2107183 : Blo 2105435 2107183 := bstep (se 1 (by rfl) ⟨1580387, by rfl⟩ : syracuseStep 2107183 = 3160775) B3160775
theorem B3160781 : Blo 2105435 3160781 := bbase (se 3 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 3160781 = 1185293) (by norm_num)
theorem B2107187 : Blo 2105435 2107187 := bstep (se 1 (by rfl) ⟨1580390, by rfl⟩ : syracuseStep 2107187 = 3160781) B3160781
theorem B4741181 : Blo 2105435 4741181 := bbase (se 3 (by rfl) ⟨888971, by rfl⟩ : syracuseStep 4741181 = 1777943) (by norm_num)
theorem B3160787 : Blo 2105435 3160787 := bstep (se 1 (by rfl) ⟨2370590, by rfl⟩ : syracuseStep 3160787 = 4741181) B4741181
theorem B2107191 : Blo 2105435 2107191 := bstep (se 1 (by rfl) ⟨1580393, by rfl⟩ : syracuseStep 2107191 = 3160787) B3160787
theorem B3555893 : Blo 2105435 3555893 := bbase (se 5 (by rfl) ⟨166682, by rfl⟩ : syracuseStep 3555893 = 333365) (by norm_num)
theorem B2370595 : Blo 2105435 2370595 := bstep (se 1 (by rfl) ⟨1777946, by rfl⟩ : syracuseStep 2370595 = 3555893) B3555893
theorem B3160793 : Blo 2105435 3160793 := bstep (se 2 (by rfl) ⟨1185297, by rfl⟩ : syracuseStep 3160793 = 2370595) B2370595
theorem B2107195 : Blo 2105435 2107195 := bstep (se 1 (by rfl) ⟨1580396, by rfl⟩ : syracuseStep 2107195 = 3160793) B3160793
theorem B6000581 : Blo 2105435 6000581 := bbase (se 4 (by rfl) ⟨562554, by rfl⟩ : syracuseStep 6000581 = 1125109) (by norm_num)
theorem B16001549 : Blo 2105435 16001549 := bstep (se 3 (by rfl) ⟨3000290, by rfl⟩ : syracuseStep 16001549 = 6000581) B6000581
theorem B10667699 : Blo 2105435 10667699 := bstep (se 1 (by rfl) ⟨8000774, by rfl⟩ : syracuseStep 10667699 = 16001549) B16001549
theorem B7111799 : Blo 2105435 7111799 := bstep (se 1 (by rfl) ⟨5333849, by rfl⟩ : syracuseStep 7111799 = 10667699) B10667699
theorem B4741199 : Blo 2105435 4741199 := bstep (se 1 (by rfl) ⟨3555899, by rfl⟩ : syracuseStep 4741199 = 7111799) B7111799
theorem B3160799 : Blo 2105435 3160799 := bstep (se 1 (by rfl) ⟨2370599, by rfl⟩ : syracuseStep 3160799 = 4741199) B4741199
theorem B2107199 : Blo 2105435 2107199 := bstep (se 1 (by rfl) ⟨1580399, by rfl⟩ : syracuseStep 2107199 = 3160799) B3160799
theorem B3160805 : Blo 2105435 3160805 := bbase (se 4 (by rfl) ⟨296325, by rfl⟩ : syracuseStep 3160805 = 592651) (by norm_num)
theorem B2107203 : Blo 2105435 2107203 := bstep (se 1 (by rfl) ⟨1580402, by rfl⟩ : syracuseStep 2107203 = 3160805) B3160805
theorem B3375341 : Blo 2105435 3375341 := bbase (se 3 (by rfl) ⟨632876, by rfl⟩ : syracuseStep 3375341 = 1265753) (by norm_num)
theorem B2250227 : Blo 2105435 2250227 := bstep (se 1 (by rfl) ⟨1687670, by rfl⟩ : syracuseStep 2250227 = 3375341) B3375341
theorem B6000605 : Blo 2105435 6000605 := bstep (se 3 (by rfl) ⟨1125113, by rfl⟩ : syracuseStep 6000605 = 2250227) B2250227
theorem B4000403 : Blo 2105435 4000403 := bstep (se 1 (by rfl) ⟨3000302, by rfl⟩ : syracuseStep 4000403 = 6000605) B6000605
theorem B2666935 : Blo 2105435 2666935 := bstep (se 1 (by rfl) ⟨2000201, by rfl⟩ : syracuseStep 2666935 = 4000403) B4000403
theorem B3555913 : Blo 2105435 3555913 := bstep (se 2 (by rfl) ⟨1333467, by rfl⟩ : syracuseStep 3555913 = 2666935) B2666935
theorem B4741217 : Blo 2105435 4741217 := bstep (se 2 (by rfl) ⟨1777956, by rfl⟩ : syracuseStep 4741217 = 3555913) B3555913
theorem B3160811 : Blo 2105435 3160811 := bstep (se 1 (by rfl) ⟨2370608, by rfl⟩ : syracuseStep 3160811 = 4741217) B4741217
theorem B2107207 : Blo 2105435 2107207 := bstep (se 1 (by rfl) ⟨1580405, by rfl⟩ : syracuseStep 2107207 = 3160811) B3160811
theorem B2370613 : Blo 2105435 2370613 := bbase (se 5 (by rfl) ⟨111122, by rfl⟩ : syracuseStep 2370613 = 222245) (by norm_num)
theorem B3160817 : Blo 2105435 3160817 := bstep (se 2 (by rfl) ⟨1185306, by rfl⟩ : syracuseStep 3160817 = 2370613) B2370613
theorem B2107211 : Blo 2105435 2107211 := bstep (se 1 (by rfl) ⟨1580408, by rfl⟩ : syracuseStep 2107211 = 3160817) B3160817
theorem B2666945 : Blo 2105435 2666945 := bbase (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) (by norm_num)
theorem B7111853 : Blo 2105435 7111853 := bstep (se 3 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 7111853 = 2666945) B2666945
theorem B4741235 : Blo 2105435 4741235 := bstep (se 1 (by rfl) ⟨3555926, by rfl⟩ : syracuseStep 4741235 = 7111853) B7111853
theorem B3160823 : Blo 2105435 3160823 := bstep (se 1 (by rfl) ⟨2370617, by rfl⟩ : syracuseStep 3160823 = 4741235) B4741235
theorem B2107215 : Blo 2105435 2107215 := bstep (se 1 (by rfl) ⟨1580411, by rfl⟩ : syracuseStep 2107215 = 3160823) B3160823
theorem B3160829 : Blo 2105435 3160829 := bbase (se 3 (by rfl) ⟨592655, by rfl⟩ : syracuseStep 3160829 = 1185311) (by norm_num)
theorem B2107219 : Blo 2105435 2107219 := bstep (se 1 (by rfl) ⟨1580414, by rfl⟩ : syracuseStep 2107219 = 3160829) B3160829
theorem B4741253 : Blo 2105435 4741253 := bbase (se 4 (by rfl) ⟨444492, by rfl⟩ : syracuseStep 4741253 = 888985) (by norm_num)
theorem B3160835 : Blo 2105435 3160835 := bstep (se 1 (by rfl) ⟨2370626, by rfl⟩ : syracuseStep 3160835 = 4741253) B4741253
theorem B2107223 : Blo 2105435 2107223 := bstep (se 1 (by rfl) ⟨1580417, by rfl⟩ : syracuseStep 2107223 = 3160835) B3160835
theorem B3375373 : Blo 2105435 3375373 := bbase (se 3 (by rfl) ⟨632882, by rfl⟩ : syracuseStep 3375373 = 1265765) (by norm_num)
theorem B4500497 : Blo 2105435 4500497 := bstep (se 2 (by rfl) ⟨1687686, by rfl⟩ : syracuseStep 4500497 = 3375373) B3375373
theorem B3000331 : Blo 2105435 3000331 := bstep (se 1 (by rfl) ⟨2250248, by rfl⟩ : syracuseStep 3000331 = 4500497) B4500497
theorem B4000441 : Blo 2105435 4000441 := bstep (se 2 (by rfl) ⟨1500165, by rfl⟩ : syracuseStep 4000441 = 3000331) B3000331
theorem B5333921 : Blo 2105435 5333921 := bstep (se 2 (by rfl) ⟨2000220, by rfl⟩ : syracuseStep 5333921 = 4000441) B4000441
theorem B3555947 : Blo 2105435 3555947 := bstep (se 1 (by rfl) ⟨2666960, by rfl⟩ : syracuseStep 3555947 = 5333921) B5333921
theorem B2370631 : Blo 2105435 2370631 := bstep (se 1 (by rfl) ⟨1777973, by rfl⟩ : syracuseStep 2370631 = 3555947) B3555947
theorem B3160841 : Blo 2105435 3160841 := bstep (se 2 (by rfl) ⟨1185315, by rfl⟩ : syracuseStep 3160841 = 2370631) B2370631
theorem B2107227 : Blo 2105435 2107227 := bstep (se 1 (by rfl) ⟨1580420, by rfl⟩ : syracuseStep 2107227 = 3160841) B3160841
theorem B10667861 : Blo 2105435 10667861 := bbase (se 9 (by rfl) ⟨31253, by rfl⟩ : syracuseStep 10667861 = 62507) (by norm_num)
theorem B7111907 : Blo 2105435 7111907 := bstep (se 1 (by rfl) ⟨5333930, by rfl⟩ : syracuseStep 7111907 = 10667861) B10667861
theorem B4741271 : Blo 2105435 4741271 := bstep (se 1 (by rfl) ⟨3555953, by rfl⟩ : syracuseStep 4741271 = 7111907) B7111907
theorem B3160847 : Blo 2105435 3160847 := bstep (se 1 (by rfl) ⟨2370635, by rfl⟩ : syracuseStep 3160847 = 4741271) B4741271
theorem B2107231 : Blo 2105435 2107231 := bstep (se 1 (by rfl) ⟨1580423, by rfl⟩ : syracuseStep 2107231 = 3160847) B3160847
theorem B3160853 : Blo 2105435 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B2107235 : Blo 2105435 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B5132165 : Blo 2105435 5132165 := bbase (se 4 (by rfl) ⟨481140, by rfl⟩ : syracuseStep 5132165 = 962281) (by norm_num)
theorem B13685773 : Blo 2105435 13685773 := bstep (se 3 (by rfl) ⟨2566082, by rfl⟩ : syracuseStep 13685773 = 5132165) B5132165
theorem B18247697 : Blo 2105435 18247697 := bstep (se 2 (by rfl) ⟨6842886, by rfl⟩ : syracuseStep 18247697 = 13685773) B13685773
theorem B12165131 : Blo 2105435 12165131 := bstep (se 1 (by rfl) ⟨9123848, by rfl⟩ : syracuseStep 12165131 = 18247697) B18247697
theorem B8110087 : Blo 2105435 8110087 := bstep (se 1 (by rfl) ⟨6082565, by rfl⟩ : syracuseStep 8110087 = 12165131) B12165131
theorem B173015189 : Blo 2105435 173015189 := bstep (se 6 (by rfl) ⟨4055043, by rfl⟩ : syracuseStep 173015189 = 8110087) B8110087
theorem B115343459 : Blo 2105435 115343459 := bstep (se 1 (by rfl) ⟨86507594, by rfl⟩ : syracuseStep 115343459 = 173015189) B173015189
theorem B76895639 : Blo 2105435 76895639 := bstep (se 1 (by rfl) ⟨57671729, by rfl⟩ : syracuseStep 76895639 = 115343459) B115343459
theorem B51263759 : Blo 2105435 51263759 := bstep (se 1 (by rfl) ⟨38447819, by rfl⟩ : syracuseStep 51263759 = 76895639) B76895639
theorem B34175839 : Blo 2105435 34175839 := bstep (se 1 (by rfl) ⟨25631879, by rfl⟩ : syracuseStep 34175839 = 51263759) B51263759
theorem B45567785 : Blo 2105435 45567785 := bstep (se 2 (by rfl) ⟨17087919, by rfl⟩ : syracuseStep 45567785 = 34175839) B34175839
theorem B30378523 : Blo 2105435 30378523 := bstep (se 1 (by rfl) ⟨22783892, by rfl⟩ : syracuseStep 30378523 = 45567785) B45567785
theorem B40504697 : Blo 2105435 40504697 := bstep (se 2 (by rfl) ⟨15189261, by rfl⟩ : syracuseStep 40504697 = 30378523) B30378523
theorem B27003131 : Blo 2105435 27003131 := bstep (se 1 (by rfl) ⟨20252348, by rfl⟩ : syracuseStep 27003131 = 40504697) B40504697
theorem B18002087 : Blo 2105435 18002087 := bstep (se 1 (by rfl) ⟨13501565, by rfl⟩ : syracuseStep 18002087 = 27003131) B27003131
theorem B12001391 : Blo 2105435 12001391 := bstep (se 1 (by rfl) ⟨9001043, by rfl⟩ : syracuseStep 12001391 = 18002087) B18002087
theorem B8000927 : Blo 2105435 8000927 := bstep (se 1 (by rfl) ⟨6000695, by rfl⟩ : syracuseStep 8000927 = 12001391) B12001391
theorem B5333951 : Blo 2105435 5333951 := bstep (se 1 (by rfl) ⟨4000463, by rfl⟩ : syracuseStep 5333951 = 8000927) B8000927
theorem B3555967 : Blo 2105435 3555967 := bstep (se 1 (by rfl) ⟨2666975, by rfl⟩ : syracuseStep 3555967 = 5333951) B5333951
theorem B4741289 : Blo 2105435 4741289 := bstep (se 2 (by rfl) ⟨1777983, by rfl⟩ : syracuseStep 4741289 = 3555967) B3555967
theorem B3160859 : Blo 2105435 3160859 := bstep (se 1 (by rfl) ⟨2370644, by rfl⟩ : syracuseStep 3160859 = 4741289) B4741289
theorem B2107239 : Blo 2105435 2107239 := bstep (se 1 (by rfl) ⟨1580429, by rfl⟩ : syracuseStep 2107239 = 3160859) B3160859
theorem B2370649 : Blo 2105435 2370649 := bbase (se 2 (by rfl) ⟨888993, by rfl⟩ : syracuseStep 2370649 = 1777987) (by norm_num)
theorem B3160865 : Blo 2105435 3160865 := bstep (se 2 (by rfl) ⟨1185324, by rfl⟩ : syracuseStep 3160865 = 2370649) B2370649
theorem B2107243 : Blo 2105435 2107243 := bstep (se 1 (by rfl) ⟨1580432, by rfl⟩ : syracuseStep 2107243 = 3160865) B3160865
theorem B7594661 : Blo 2105435 7594661 := bbase (se 4 (by rfl) ⟨711999, by rfl⟩ : syracuseStep 7594661 = 1423999) (by norm_num)
theorem B5063107 : Blo 2105435 5063107 := bstep (se 1 (by rfl) ⟨3797330, by rfl⟩ : syracuseStep 5063107 = 7594661) B7594661
theorem B6750809 : Blo 2105435 6750809 := bstep (se 2 (by rfl) ⟨2531553, by rfl⟩ : syracuseStep 6750809 = 5063107) B5063107
theorem B4500539 : Blo 2105435 4500539 := bstep (se 1 (by rfl) ⟨3375404, by rfl⟩ : syracuseStep 4500539 = 6750809) B6750809
theorem B3000359 : Blo 2105435 3000359 := bstep (se 1 (by rfl) ⟨2250269, by rfl⟩ : syracuseStep 3000359 = 4500539) B4500539
theorem B8000957 : Blo 2105435 8000957 := bstep (se 3 (by rfl) ⟨1500179, by rfl⟩ : syracuseStep 8000957 = 3000359) B3000359
theorem B5333971 : Blo 2105435 5333971 := bstep (se 1 (by rfl) ⟨4000478, by rfl⟩ : syracuseStep 5333971 = 8000957) B8000957
theorem B7111961 : Blo 2105435 7111961 := bstep (se 2 (by rfl) ⟨2666985, by rfl⟩ : syracuseStep 7111961 = 5333971) B5333971
theorem B4741307 : Blo 2105435 4741307 := bstep (se 1 (by rfl) ⟨3555980, by rfl⟩ : syracuseStep 4741307 = 7111961) B7111961
theorem B3160871 : Blo 2105435 3160871 := bstep (se 1 (by rfl) ⟨2370653, by rfl⟩ : syracuseStep 3160871 = 4741307) B4741307
theorem B2107247 : Blo 2105435 2107247 := bstep (se 1 (by rfl) ⟨1580435, by rfl⟩ : syracuseStep 2107247 = 3160871) B3160871
theorem B3160877 : Blo 2105435 3160877 := bbase (se 3 (by rfl) ⟨592664, by rfl⟩ : syracuseStep 3160877 = 1185329) (by norm_num)
theorem B2107251 : Blo 2105435 2107251 := bstep (se 1 (by rfl) ⟨1580438, by rfl⟩ : syracuseStep 2107251 = 3160877) B3160877
theorem B4741325 : Blo 2105435 4741325 := bbase (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) (by norm_num)
theorem B3160883 : Blo 2105435 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B2107255 : Blo 2105435 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B2667001 : Blo 2105435 2667001 := bbase (se 2 (by rfl) ⟨1000125, by rfl⟩ : syracuseStep 2667001 = 2000251) (by norm_num)
theorem B3556001 : Blo 2105435 3556001 := bstep (se 2 (by rfl) ⟨1333500, by rfl⟩ : syracuseStep 3556001 = 2667001) B2667001
theorem B2370667 : Blo 2105435 2370667 := bstep (se 1 (by rfl) ⟨1778000, by rfl⟩ : syracuseStep 2370667 = 3556001) B3556001
theorem B3160889 : Blo 2105435 3160889 := bstep (se 2 (by rfl) ⟨1185333, by rfl⟩ : syracuseStep 3160889 = 2370667) B2370667
theorem B2107259 : Blo 2105435 2107259 := bstep (se 1 (by rfl) ⟨1580444, by rfl⟩ : syracuseStep 2107259 = 3160889) B3160889
theorem B4272029 : Blo 2105435 4272029 := bbase (se 3 (by rfl) ⟨801005, by rfl⟩ : syracuseStep 4272029 = 1602011) (by norm_num)
theorem B2848019 : Blo 2105435 2848019 := bstep (se 1 (by rfl) ⟨2136014, by rfl⟩ : syracuseStep 2848019 = 4272029) B4272029
theorem B7594717 : Blo 2105435 7594717 := bstep (se 3 (by rfl) ⟨1424009, by rfl⟩ : syracuseStep 7594717 = 2848019) B2848019
theorem B10126289 : Blo 2105435 10126289 := bstep (se 2 (by rfl) ⟨3797358, by rfl⟩ : syracuseStep 10126289 = 7594717) B7594717
theorem B6750859 : Blo 2105435 6750859 := bstep (se 1 (by rfl) ⟨5063144, by rfl⟩ : syracuseStep 6750859 = 10126289) B10126289
theorem B9001145 : Blo 2105435 9001145 := bstep (se 2 (by rfl) ⟨3375429, by rfl⟩ : syracuseStep 9001145 = 6750859) B6750859
theorem B24003053 : Blo 2105435 24003053 := bstep (se 3 (by rfl) ⟨4500572, by rfl⟩ : syracuseStep 24003053 = 9001145) B9001145
theorem B16002035 : Blo 2105435 16002035 := bstep (se 1 (by rfl) ⟨12001526, by rfl⟩ : syracuseStep 16002035 = 24003053) B24003053
theorem B10668023 : Blo 2105435 10668023 := bstep (se 1 (by rfl) ⟨8001017, by rfl⟩ : syracuseStep 10668023 = 16002035) B16002035
theorem B7112015 : Blo 2105435 7112015 := bstep (se 1 (by rfl) ⟨5334011, by rfl⟩ : syracuseStep 7112015 = 10668023) B10668023
theorem B4741343 : Blo 2105435 4741343 := bstep (se 1 (by rfl) ⟨3556007, by rfl⟩ : syracuseStep 4741343 = 7112015) B7112015
theorem B3160895 : Blo 2105435 3160895 := bstep (se 1 (by rfl) ⟨2370671, by rfl⟩ : syracuseStep 3160895 = 4741343) B4741343
theorem B2107263 : Blo 2105435 2107263 := bstep (se 1 (by rfl) ⟨1580447, by rfl⟩ : syracuseStep 2107263 = 3160895) B3160895
theorem B3160901 : Blo 2105435 3160901 := bbase (se 4 (by rfl) ⟨296334, by rfl⟩ : syracuseStep 3160901 = 592669) (by norm_num)
theorem B2107267 : Blo 2105435 2107267 := bstep (se 1 (by rfl) ⟨1580450, by rfl⟩ : syracuseStep 2107267 = 3160901) B3160901
theorem B3556021 : Blo 2105435 3556021 := bbase (se 5 (by rfl) ⟨166688, by rfl⟩ : syracuseStep 3556021 = 333377) (by norm_num)
theorem B4741361 : Blo 2105435 4741361 := bstep (se 2 (by rfl) ⟨1778010, by rfl⟩ : syracuseStep 4741361 = 3556021) B3556021
theorem B3160907 : Blo 2105435 3160907 := bstep (se 1 (by rfl) ⟨2370680, by rfl⟩ : syracuseStep 3160907 = 4741361) B4741361
theorem B2107271 : Blo 2105435 2107271 := bstep (se 1 (by rfl) ⟨1580453, by rfl⟩ : syracuseStep 2107271 = 3160907) B3160907
theorem B2370685 : Blo 2105435 2370685 := bbase (se 3 (by rfl) ⟨444503, by rfl⟩ : syracuseStep 2370685 = 889007) (by norm_num)
theorem B3160913 : Blo 2105435 3160913 := bstep (se 2 (by rfl) ⟨1185342, by rfl⟩ : syracuseStep 3160913 = 2370685) B2370685
theorem B2107275 : Blo 2105435 2107275 := bstep (se 1 (by rfl) ⟨1580456, by rfl⟩ : syracuseStep 2107275 = 3160913) B3160913
theorem B7112069 : Blo 2105435 7112069 := bbase (se 4 (by rfl) ⟨666756, by rfl⟩ : syracuseStep 7112069 = 1333513) (by norm_num)
theorem B4741379 : Blo 2105435 4741379 := bstep (se 1 (by rfl) ⟨3556034, by rfl⟩ : syracuseStep 4741379 = 7112069) B7112069
theorem B3160919 : Blo 2105435 3160919 := bstep (se 1 (by rfl) ⟨2370689, by rfl⟩ : syracuseStep 3160919 = 4741379) B4741379
theorem B2107279 : Blo 2105435 2107279 := bstep (se 1 (by rfl) ⟨1580459, by rfl⟩ : syracuseStep 2107279 = 3160919) B3160919
theorem B3160925 : Blo 2105435 3160925 := bbase (se 3 (by rfl) ⟨592673, by rfl⟩ : syracuseStep 3160925 = 1185347) (by norm_num)
theorem B2107283 : Blo 2105435 2107283 := bstep (se 1 (by rfl) ⟨1580462, by rfl⟩ : syracuseStep 2107283 = 3160925) B3160925
theorem B4741397 : Blo 2105435 4741397 := bbase (se 6 (by rfl) ⟨111126, by rfl⟩ : syracuseStep 4741397 = 222253) (by norm_num)
theorem B3160931 : Blo 2105435 3160931 := bstep (se 1 (by rfl) ⟨2370698, by rfl⟩ : syracuseStep 3160931 = 4741397) B4741397
theorem B2107287 : Blo 2105435 2107287 := bstep (se 1 (by rfl) ⟨1580465, by rfl⟩ : syracuseStep 2107287 = 3160931) B3160931
theorem B8001125 : Blo 2105435 8001125 := bbase (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) (by norm_num)
theorem B5334083 : Blo 2105435 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B3556055 : Blo 2105435 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B2370703 : Blo 2105435 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B3160937 : Blo 2105435 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B2107291 : Blo 2105435 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B12165461 : Blo 2105435 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B8110307 : Blo 2105435 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B21627485 : Blo 2105435 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B14418323 : Blo 2105435 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B9612215 : Blo 2105435 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B6408143 : Blo 2105435 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B4272095 : Blo 2105435 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B2848063 : Blo 2105435 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B3797417 : Blo 2105435 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B2531611 : Blo 2105435 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B3375481 : Blo 2105435 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B4500641 : Blo 2105435 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B12001709 : Blo 2105435 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B8001139 : Blo 2105435 8001139 := bstep (se 1 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 8001139 = 12001709) B12001709
theorem B10668185 : Blo 2105435 10668185 := bstep (se 2 (by rfl) ⟨4000569, by rfl⟩ : syracuseStep 10668185 = 8001139) B8001139
theorem B7112123 : Blo 2105435 7112123 := bstep (se 1 (by rfl) ⟨5334092, by rfl⟩ : syracuseStep 7112123 = 10668185) B10668185
theorem B4741415 : Blo 2105435 4741415 := bstep (se 1 (by rfl) ⟨3556061, by rfl⟩ : syracuseStep 4741415 = 7112123) B7112123
theorem B3160943 : Blo 2105435 3160943 := bstep (se 1 (by rfl) ⟨2370707, by rfl⟩ : syracuseStep 3160943 = 4741415) B4741415
theorem B2107295 : Blo 2105435 2107295 := bstep (se 1 (by rfl) ⟨1580471, by rfl⟩ : syracuseStep 2107295 = 3160943) B3160943
theorem B3160949 : Blo 2105435 3160949 := bbase (se 5 (by rfl) ⟨148169, by rfl⟩ : syracuseStep 3160949 = 296339) (by norm_num)
theorem B2107299 : Blo 2105435 2107299 := bstep (se 1 (by rfl) ⟨1580474, by rfl⟩ : syracuseStep 2107299 = 3160949) B3160949
theorem B2531621 : Blo 2105435 2531621 := bbase (se 4 (by rfl) ⟨237339, by rfl⟩ : syracuseStep 2531621 = 474679) (by norm_num)
theorem B6750989 : Blo 2105435 6750989 := bstep (se 3 (by rfl) ⟨1265810, by rfl⟩ : syracuseStep 6750989 = 2531621) B2531621
theorem B4500659 : Blo 2105435 4500659 := bstep (se 1 (by rfl) ⟨3375494, by rfl⟩ : syracuseStep 4500659 = 6750989) B6750989
theorem B3000439 : Blo 2105435 3000439 := bstep (se 1 (by rfl) ⟨2250329, by rfl⟩ : syracuseStep 3000439 = 4500659) B4500659
theorem B4000585 : Blo 2105435 4000585 := bstep (se 2 (by rfl) ⟨1500219, by rfl⟩ : syracuseStep 4000585 = 3000439) B3000439
theorem B5334113 : Blo 2105435 5334113 := bstep (se 2 (by rfl) ⟨2000292, by rfl⟩ : syracuseStep 5334113 = 4000585) B4000585
theorem B3556075 : Blo 2105435 3556075 := bstep (se 1 (by rfl) ⟨2667056, by rfl⟩ : syracuseStep 3556075 = 5334113) B5334113
theorem B4741433 : Blo 2105435 4741433 := bstep (se 2 (by rfl) ⟨1778037, by rfl⟩ : syracuseStep 4741433 = 3556075) B3556075
theorem B3160955 : Blo 2105435 3160955 := bstep (se 1 (by rfl) ⟨2370716, by rfl⟩ : syracuseStep 3160955 = 4741433) B4741433
theorem B2107303 : Blo 2105435 2107303 := bstep (se 1 (by rfl) ⟨1580477, by rfl⟩ : syracuseStep 2107303 = 3160955) B3160955
theorem B2370721 : Blo 2105435 2370721 := bbase (se 2 (by rfl) ⟨889020, by rfl⟩ : syracuseStep 2370721 = 1778041) (by norm_num)
theorem B3160961 : Blo 2105435 3160961 := bstep (se 2 (by rfl) ⟨1185360, by rfl⟩ : syracuseStep 3160961 = 2370721) B2370721
theorem B2107307 : Blo 2105435 2107307 := bstep (se 1 (by rfl) ⟨1580480, by rfl⟩ : syracuseStep 2107307 = 3160961) B3160961
theorem B5334133 : Blo 2105435 5334133 := bbase (se 5 (by rfl) ⟨250037, by rfl⟩ : syracuseStep 5334133 = 500075) (by norm_num)
theorem B7112177 : Blo 2105435 7112177 := bstep (se 2 (by rfl) ⟨2667066, by rfl⟩ : syracuseStep 7112177 = 5334133) B5334133
theorem B4741451 : Blo 2105435 4741451 := bstep (se 1 (by rfl) ⟨3556088, by rfl⟩ : syracuseStep 4741451 = 7112177) B7112177
theorem B3160967 : Blo 2105435 3160967 := bstep (se 1 (by rfl) ⟨2370725, by rfl⟩ : syracuseStep 3160967 = 4741451) B4741451
theorem B2107311 : Blo 2105435 2107311 := bstep (se 1 (by rfl) ⟨1580483, by rfl⟩ : syracuseStep 2107311 = 3160967) B3160967
theorem B3160973 : Blo 2105435 3160973 := bbase (se 3 (by rfl) ⟨592682, by rfl⟩ : syracuseStep 3160973 = 1185365) (by norm_num)
theorem B2107315 : Blo 2105435 2107315 := bstep (se 1 (by rfl) ⟨1580486, by rfl⟩ : syracuseStep 2107315 = 3160973) B3160973
theorem B4741469 : Blo 2105435 4741469 := bbase (se 3 (by rfl) ⟨889025, by rfl⟩ : syracuseStep 4741469 = 1778051) (by norm_num)
theorem B3160979 : Blo 2105435 3160979 := bstep (se 1 (by rfl) ⟨2370734, by rfl⟩ : syracuseStep 3160979 = 4741469) B4741469
theorem B2107319 : Blo 2105435 2107319 := bstep (se 1 (by rfl) ⟨1580489, by rfl⟩ : syracuseStep 2107319 = 3160979) B3160979
theorem B3556109 : Blo 2105435 3556109 := bbase (se 3 (by rfl) ⟨666770, by rfl⟩ : syracuseStep 3556109 = 1333541) (by norm_num)
theorem B2370739 : Blo 2105435 2370739 := bstep (se 1 (by rfl) ⟨1778054, by rfl⟩ : syracuseStep 2370739 = 3556109) B3556109
theorem B3160985 : Blo 2105435 3160985 := bstep (se 2 (by rfl) ⟨1185369, by rfl⟩ : syracuseStep 3160985 = 2370739) B2370739
theorem B2107323 : Blo 2105435 2107323 := bstep (se 1 (by rfl) ⟨1580492, by rfl⟩ : syracuseStep 2107323 = 3160985) B3160985
theorem B18002837 : Blo 2105435 18002837 := bbase (se 6 (by rfl) ⟨421941, by rfl⟩ : syracuseStep 18002837 = 843883) (by norm_num)
theorem B12001891 : Blo 2105435 12001891 := bstep (se 1 (by rfl) ⟨9001418, by rfl⟩ : syracuseStep 12001891 = 18002837) B18002837
theorem B16002521 : Blo 2105435 16002521 := bstep (se 2 (by rfl) ⟨6000945, by rfl⟩ : syracuseStep 16002521 = 12001891) B12001891
theorem B10668347 : Blo 2105435 10668347 := bstep (se 1 (by rfl) ⟨8001260, by rfl⟩ : syracuseStep 10668347 = 16002521) B16002521
theorem B7112231 : Blo 2105435 7112231 := bstep (se 1 (by rfl) ⟨5334173, by rfl⟩ : syracuseStep 7112231 = 10668347) B10668347
theorem B4741487 : Blo 2105435 4741487 := bstep (se 1 (by rfl) ⟨3556115, by rfl⟩ : syracuseStep 4741487 = 7112231) B7112231
theorem B3160991 : Blo 2105435 3160991 := bstep (se 1 (by rfl) ⟨2370743, by rfl⟩ : syracuseStep 3160991 = 4741487) B4741487
theorem B2107327 : Blo 2105435 2107327 := bstep (se 1 (by rfl) ⟨1580495, by rfl⟩ : syracuseStep 2107327 = 3160991) B3160991
theorem B3160997 : Blo 2105435 3160997 := bbase (se 4 (by rfl) ⟨296343, by rfl⟩ : syracuseStep 3160997 = 592687) (by norm_num)
theorem B2107331 : Blo 2105435 2107331 := bstep (se 1 (by rfl) ⟨1580498, by rfl⟩ : syracuseStep 2107331 = 3160997) B3160997
theorem B2667097 : Blo 2105435 2667097 := bbase (se 2 (by rfl) ⟨1000161, by rfl⟩ : syracuseStep 2667097 = 2000323) (by norm_num)
theorem B3556129 : Blo 2105435 3556129 := bstep (se 2 (by rfl) ⟨1333548, by rfl⟩ : syracuseStep 3556129 = 2667097) B2667097
theorem B4741505 : Blo 2105435 4741505 := bstep (se 2 (by rfl) ⟨1778064, by rfl⟩ : syracuseStep 4741505 = 3556129) B3556129
theorem B3161003 : Blo 2105435 3161003 := bstep (se 1 (by rfl) ⟨2370752, by rfl⟩ : syracuseStep 3161003 = 4741505) B4741505
theorem B2107335 : Blo 2105435 2107335 := bstep (se 1 (by rfl) ⟨1580501, by rfl⟩ : syracuseStep 2107335 = 3161003) B3161003
theorem B2370757 : Blo 2105435 2370757 := bbase (se 4 (by rfl) ⟨222258, by rfl⟩ : syracuseStep 2370757 = 444517) (by norm_num)
theorem B3161009 : Blo 2105435 3161009 := bstep (se 2 (by rfl) ⟨1185378, by rfl⟩ : syracuseStep 3161009 = 2370757) B2370757
theorem B2107339 : Blo 2105435 2107339 := bstep (se 1 (by rfl) ⟨1580504, by rfl⟩ : syracuseStep 2107339 = 3161009) B3161009
theorem B4000661 : Blo 2105435 4000661 := bbase (se 6 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 4000661 = 187531) (by norm_num)
theorem B2667107 : Blo 2105435 2667107 := bstep (se 1 (by rfl) ⟨2000330, by rfl⟩ : syracuseStep 2667107 = 4000661) B4000661
theorem B7112285 : Blo 2105435 7112285 := bstep (se 3 (by rfl) ⟨1333553, by rfl⟩ : syracuseStep 7112285 = 2667107) B2667107
theorem B4741523 : Blo 2105435 4741523 := bstep (se 1 (by rfl) ⟨3556142, by rfl⟩ : syracuseStep 4741523 = 7112285) B7112285
theorem B3161015 : Blo 2105435 3161015 := bstep (se 1 (by rfl) ⟨2370761, by rfl⟩ : syracuseStep 3161015 = 4741523) B4741523
theorem B2107343 : Blo 2105435 2107343 := bstep (se 1 (by rfl) ⟨1580507, by rfl⟩ : syracuseStep 2107343 = 3161015) B3161015
theorem B3161021 : Blo 2105435 3161021 := bbase (se 3 (by rfl) ⟨592691, by rfl⟩ : syracuseStep 3161021 = 1185383) (by norm_num)
theorem B2107347 : Blo 2105435 2107347 := bstep (se 1 (by rfl) ⟨1580510, by rfl⟩ : syracuseStep 2107347 = 3161021) B3161021
theorem B4741541 : Blo 2105435 4741541 := bbase (se 4 (by rfl) ⟨444519, by rfl⟩ : syracuseStep 4741541 = 889039) (by norm_num)
theorem B3161027 : Blo 2105435 3161027 := bstep (se 1 (by rfl) ⟨2370770, by rfl⟩ : syracuseStep 3161027 = 4741541) B4741541
theorem B2107351 : Blo 2105435 2107351 := bstep (se 1 (by rfl) ⟨1580513, by rfl⟩ : syracuseStep 2107351 = 3161027) B3161027
theorem B5334245 : Blo 2105435 5334245 := bbase (se 4 (by rfl) ⟨500085, by rfl⟩ : syracuseStep 5334245 = 1000171) (by norm_num)
theorem B3556163 : Blo 2105435 3556163 := bstep (se 1 (by rfl) ⟨2667122, by rfl⟩ : syracuseStep 3556163 = 5334245) B5334245
theorem B2370775 : Blo 2105435 2370775 := bstep (se 1 (by rfl) ⟨1778081, by rfl⟩ : syracuseStep 2370775 = 3556163) B3556163
theorem B3161033 : Blo 2105435 3161033 := bstep (se 2 (by rfl) ⟨1185387, by rfl⟩ : syracuseStep 3161033 = 2370775) B2370775
theorem B2107355 : Blo 2105435 2107355 := bstep (se 1 (by rfl) ⟨1580516, by rfl⟩ : syracuseStep 2107355 = 3161033) B3161033
theorem B2250389 : Blo 2105435 2250389 := bbase (se 6 (by rfl) ⟨52743, by rfl⟩ : syracuseStep 2250389 = 105487) (by norm_num)
theorem B6001037 : Blo 2105435 6001037 := bstep (se 3 (by rfl) ⟨1125194, by rfl⟩ : syracuseStep 6001037 = 2250389) B2250389
theorem B4000691 : Blo 2105435 4000691 := bstep (se 1 (by rfl) ⟨3000518, by rfl⟩ : syracuseStep 4000691 = 6001037) B6001037
theorem B10668509 : Blo 2105435 10668509 := bstep (se 3 (by rfl) ⟨2000345, by rfl⟩ : syracuseStep 10668509 = 4000691) B4000691
theorem B7112339 : Blo 2105435 7112339 := bstep (se 1 (by rfl) ⟨5334254, by rfl⟩ : syracuseStep 7112339 = 10668509) B10668509
theorem B4741559 : Blo 2105435 4741559 := bstep (se 1 (by rfl) ⟨3556169, by rfl⟩ : syracuseStep 4741559 = 7112339) B7112339
theorem B3161039 : Blo 2105435 3161039 := bstep (se 1 (by rfl) ⟨2370779, by rfl⟩ : syracuseStep 3161039 = 4741559) B4741559
theorem B2107359 : Blo 2105435 2107359 := bstep (se 1 (by rfl) ⟨1580519, by rfl⟩ : syracuseStep 2107359 = 3161039) B3161039
theorem B3161045 : Blo 2105435 3161045 := bbase (se 7 (by rfl) ⟨37043, by rfl⟩ : syracuseStep 3161045 = 74087) (by norm_num)
theorem B2107363 : Blo 2105435 2107363 := bstep (se 1 (by rfl) ⟨1580522, by rfl⟩ : syracuseStep 2107363 = 3161045) B3161045
theorem B8001413 : Blo 2105435 8001413 := bbase (se 4 (by rfl) ⟨750132, by rfl⟩ : syracuseStep 8001413 = 1500265) (by norm_num)
theorem B5334275 : Blo 2105435 5334275 := bstep (se 1 (by rfl) ⟨4000706, by rfl⟩ : syracuseStep 5334275 = 8001413) B8001413
theorem B3556183 : Blo 2105435 3556183 := bstep (se 1 (by rfl) ⟨2667137, by rfl⟩ : syracuseStep 3556183 = 5334275) B5334275
theorem B4741577 : Blo 2105435 4741577 := bstep (se 2 (by rfl) ⟨1778091, by rfl⟩ : syracuseStep 4741577 = 3556183) B3556183
theorem B3161051 : Blo 2105435 3161051 := bstep (se 1 (by rfl) ⟨2370788, by rfl⟩ : syracuseStep 3161051 = 4741577) B4741577
theorem B2107367 : Blo 2105435 2107367 := bstep (se 1 (by rfl) ⟨1580525, by rfl⟩ : syracuseStep 2107367 = 3161051) B3161051
theorem B2370793 : Blo 2105435 2370793 := bbase (se 2 (by rfl) ⟨889047, by rfl⟩ : syracuseStep 2370793 = 1778095) (by norm_num)
theorem B3161057 : Blo 2105435 3161057 := bstep (se 2 (by rfl) ⟨1185396, by rfl⟩ : syracuseStep 3161057 = 2370793) B2370793
theorem B2107371 : Blo 2105435 2107371 := bstep (se 1 (by rfl) ⟨1580528, by rfl⟩ : syracuseStep 2107371 = 3161057) B3161057
theorem B12002165 : Blo 2105435 12002165 := bbase (se 5 (by rfl) ⟨562601, by rfl⟩ : syracuseStep 12002165 = 1125203) (by norm_num)
theorem B8001443 : Blo 2105435 8001443 := bstep (se 1 (by rfl) ⟨6001082, by rfl⟩ : syracuseStep 8001443 = 12002165) B12002165
theorem B5334295 : Blo 2105435 5334295 := bstep (se 1 (by rfl) ⟨4000721, by rfl⟩ : syracuseStep 5334295 = 8001443) B8001443
theorem B7112393 : Blo 2105435 7112393 := bstep (se 2 (by rfl) ⟨2667147, by rfl⟩ : syracuseStep 7112393 = 5334295) B5334295
theorem B4741595 : Blo 2105435 4741595 := bstep (se 1 (by rfl) ⟨3556196, by rfl⟩ : syracuseStep 4741595 = 7112393) B7112393
theorem B3161063 : Blo 2105435 3161063 := bstep (se 1 (by rfl) ⟨2370797, by rfl⟩ : syracuseStep 3161063 = 4741595) B4741595
theorem B2107375 : Blo 2105435 2107375 := bstep (se 1 (by rfl) ⟨1580531, by rfl⟩ : syracuseStep 2107375 = 3161063) B3161063
theorem B3161069 : Blo 2105435 3161069 := bbase (se 3 (by rfl) ⟨592700, by rfl⟩ : syracuseStep 3161069 = 1185401) (by norm_num)
theorem B2107379 : Blo 2105435 2107379 := bstep (se 1 (by rfl) ⟨1580534, by rfl⟩ : syracuseStep 2107379 = 3161069) B3161069
theorem B4741613 : Blo 2105435 4741613 := bbase (se 3 (by rfl) ⟨889052, by rfl⟩ : syracuseStep 4741613 = 1778105) (by norm_num)
theorem B3161075 : Blo 2105435 3161075 := bstep (se 1 (by rfl) ⟨2370806, by rfl⟩ : syracuseStep 3161075 = 4741613) B4741613
theorem B2107383 : Blo 2105435 2107383 := bstep (se 1 (by rfl) ⟨1580537, by rfl⟩ : syracuseStep 2107383 = 3161075) B3161075
theorem B3421685 : Blo 2105435 3421685 := bbase (se 5 (by rfl) ⟨160391, by rfl⟩ : syracuseStep 3421685 = 320783) (by norm_num)
theorem B9124493 : Blo 2105435 9124493 := bstep (se 3 (by rfl) ⟨1710842, by rfl⟩ : syracuseStep 9124493 = 3421685) B3421685
theorem B97327925 : Blo 2105435 97327925 := bstep (se 5 (by rfl) ⟨4562246, by rfl⟩ : syracuseStep 97327925 = 9124493) B9124493
theorem B64885283 : Blo 2105435 64885283 := bstep (se 1 (by rfl) ⟨48663962, by rfl⟩ : syracuseStep 64885283 = 97327925) B97327925
theorem B43256855 : Blo 2105435 43256855 := bstep (se 1 (by rfl) ⟨32442641, by rfl⟩ : syracuseStep 43256855 = 64885283) B64885283
theorem B28837903 : Blo 2105435 28837903 := bstep (se 1 (by rfl) ⟨21628427, by rfl⟩ : syracuseStep 28837903 = 43256855) B43256855
theorem B38450537 : Blo 2105435 38450537 := bstep (se 2 (by rfl) ⟨14418951, by rfl⟩ : syracuseStep 38450537 = 28837903) B28837903
theorem B25633691 : Blo 2105435 25633691 := bstep (se 1 (by rfl) ⟨19225268, by rfl⟩ : syracuseStep 25633691 = 38450537) B38450537
theorem B17089127 : Blo 2105435 17089127 := bstep (se 1 (by rfl) ⟨12816845, by rfl⟩ : syracuseStep 17089127 = 25633691) B25633691
theorem B11392751 : Blo 2105435 11392751 := bstep (se 1 (by rfl) ⟨8544563, by rfl⟩ : syracuseStep 11392751 = 17089127) B17089127
theorem B7595167 : Blo 2105435 7595167 := bstep (se 1 (by rfl) ⟨5696375, by rfl⟩ : syracuseStep 7595167 = 11392751) B11392751
theorem B10126889 : Blo 2105435 10126889 := bstep (se 2 (by rfl) ⟨3797583, by rfl⟩ : syracuseStep 10126889 = 7595167) B7595167
theorem B6751259 : Blo 2105435 6751259 := bstep (se 1 (by rfl) ⟨5063444, by rfl⟩ : syracuseStep 6751259 = 10126889) B10126889
theorem B4500839 : Blo 2105435 4500839 := bstep (se 1 (by rfl) ⟨3375629, by rfl⟩ : syracuseStep 4500839 = 6751259) B6751259
theorem B3000559 : Blo 2105435 3000559 := bstep (se 1 (by rfl) ⟨2250419, by rfl⟩ : syracuseStep 3000559 = 4500839) B4500839
theorem B4000745 : Blo 2105435 4000745 := bstep (se 2 (by rfl) ⟨1500279, by rfl⟩ : syracuseStep 4000745 = 3000559) B3000559
theorem B2667163 : Blo 2105435 2667163 := bstep (se 1 (by rfl) ⟨2000372, by rfl⟩ : syracuseStep 2667163 = 4000745) B4000745
theorem B3556217 : Blo 2105435 3556217 := bstep (se 2 (by rfl) ⟨1333581, by rfl⟩ : syracuseStep 3556217 = 2667163) B2667163
theorem B2370811 : Blo 2105435 2370811 := bstep (se 1 (by rfl) ⟨1778108, by rfl⟩ : syracuseStep 2370811 = 3556217) B3556217
theorem B3161081 : Blo 2105435 3161081 := bstep (se 2 (by rfl) ⟨1185405, by rfl⟩ : syracuseStep 3161081 = 2370811) B2370811
theorem B2107387 : Blo 2105435 2107387 := bstep (se 1 (by rfl) ⟨1580540, by rfl⟩ : syracuseStep 2107387 = 3161081) B3161081
theorem B3247933 : Blo 2105435 3247933 := bbase (se 3 (by rfl) ⟨608987, by rfl⟩ : syracuseStep 3247933 = 1217975) (by norm_num)
theorem B4330577 : Blo 2105435 4330577 := bstep (se 2 (by rfl) ⟨1623966, by rfl⟩ : syracuseStep 4330577 = 3247933) B3247933
theorem B2887051 : Blo 2105435 2887051 := bstep (se 1 (by rfl) ⟨2165288, by rfl⟩ : syracuseStep 2887051 = 4330577) B4330577
theorem B3849401 : Blo 2105435 3849401 := bstep (se 2 (by rfl) ⟨1443525, by rfl⟩ : syracuseStep 3849401 = 2887051) B2887051
theorem B2566267 : Blo 2105435 2566267 := bstep (se 1 (by rfl) ⟨1924700, by rfl⟩ : syracuseStep 2566267 = 3849401) B3849401
theorem B54747029 : Blo 2105435 54747029 := bstep (se 6 (by rfl) ⟨1283133, by rfl⟩ : syracuseStep 54747029 = 2566267) B2566267
theorem B145992077 : Blo 2105435 145992077 := bstep (se 3 (by rfl) ⟨27373514, by rfl⟩ : syracuseStep 145992077 = 54747029) B54747029
theorem B97328051 : Blo 2105435 97328051 := bstep (se 1 (by rfl) ⟨72996038, by rfl⟩ : syracuseStep 97328051 = 145992077) B145992077
theorem B64885367 : Blo 2105435 64885367 := bstep (se 1 (by rfl) ⟨48664025, by rfl⟩ : syracuseStep 64885367 = 97328051) B97328051
theorem B43256911 : Blo 2105435 43256911 := bstep (se 1 (by rfl) ⟨32442683, by rfl⟩ : syracuseStep 43256911 = 64885367) B64885367
theorem B57675881 : Blo 2105435 57675881 := bstep (se 2 (by rfl) ⟨21628455, by rfl⟩ : syracuseStep 57675881 = 43256911) B43256911
theorem B38450587 : Blo 2105435 38450587 := bstep (se 1 (by rfl) ⟨28837940, by rfl⟩ : syracuseStep 38450587 = 57675881) B57675881
theorem B51267449 : Blo 2105435 51267449 := bstep (se 2 (by rfl) ⟨19225293, by rfl⟩ : syracuseStep 51267449 = 38450587) B38450587
theorem B136713197 : Blo 2105435 136713197 := bstep (se 3 (by rfl) ⟨25633724, by rfl⟩ : syracuseStep 136713197 = 51267449) B51267449
theorem B91142131 : Blo 2105435 91142131 := bstep (se 1 (by rfl) ⟨68356598, by rfl⟩ : syracuseStep 91142131 = 136713197) B136713197
theorem B121522841 : Blo 2105435 121522841 := bstep (se 2 (by rfl) ⟨45571065, by rfl⟩ : syracuseStep 121522841 = 91142131) B91142131
theorem B81015227 : Blo 2105435 81015227 := bstep (se 1 (by rfl) ⟨60761420, by rfl⟩ : syracuseStep 81015227 = 121522841) B121522841
theorem B54010151 : Blo 2105435 54010151 := bstep (se 1 (by rfl) ⟨40507613, by rfl⟩ : syracuseStep 54010151 = 81015227) B81015227
theorem B36006767 : Blo 2105435 36006767 := bstep (se 1 (by rfl) ⟨27005075, by rfl⟩ : syracuseStep 36006767 = 54010151) B54010151
theorem B24004511 : Blo 2105435 24004511 := bstep (se 1 (by rfl) ⟨18003383, by rfl⟩ : syracuseStep 24004511 = 36006767) B36006767
theorem B16003007 : Blo 2105435 16003007 := bstep (se 1 (by rfl) ⟨12002255, by rfl⟩ : syracuseStep 16003007 = 24004511) B24004511
theorem B10668671 : Blo 2105435 10668671 := bstep (se 1 (by rfl) ⟨8001503, by rfl⟩ : syracuseStep 10668671 = 16003007) B16003007
theorem B7112447 : Blo 2105435 7112447 := bstep (se 1 (by rfl) ⟨5334335, by rfl⟩ : syracuseStep 7112447 = 10668671) B10668671
theorem B4741631 : Blo 2105435 4741631 := bstep (se 1 (by rfl) ⟨3556223, by rfl⟩ : syracuseStep 4741631 = 7112447) B7112447
theorem B3161087 : Blo 2105435 3161087 := bstep (se 1 (by rfl) ⟨2370815, by rfl⟩ : syracuseStep 3161087 = 4741631) B4741631
theorem B2107391 : Blo 2105435 2107391 := bstep (se 1 (by rfl) ⟨1580543, by rfl⟩ : syracuseStep 2107391 = 3161087) B3161087
theorem B3161093 : Blo 2105435 3161093 := bbase (se 4 (by rfl) ⟨296352, by rfl⟩ : syracuseStep 3161093 = 592705) (by norm_num)
theorem B2107395 : Blo 2105435 2107395 := bstep (se 1 (by rfl) ⟨1580546, by rfl⟩ : syracuseStep 2107395 = 3161093) B3161093
theorem B3556237 : Blo 2105435 3556237 := bbase (se 3 (by rfl) ⟨666794, by rfl⟩ : syracuseStep 3556237 = 1333589) (by norm_num)
theorem B4741649 : Blo 2105435 4741649 := bstep (se 2 (by rfl) ⟨1778118, by rfl⟩ : syracuseStep 4741649 = 3556237) B3556237
theorem B3161099 : Blo 2105435 3161099 := bstep (se 1 (by rfl) ⟨2370824, by rfl⟩ : syracuseStep 3161099 = 4741649) B4741649
theorem B2107399 : Blo 2105435 2107399 := bstep (se 1 (by rfl) ⟨1580549, by rfl⟩ : syracuseStep 2107399 = 3161099) B3161099
theorem B2370829 : Blo 2105435 2370829 := bbase (se 3 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 2370829 = 889061) (by norm_num)
theorem B3161105 : Blo 2105435 3161105 := bstep (se 2 (by rfl) ⟨1185414, by rfl⟩ : syracuseStep 3161105 = 2370829) B2370829
theorem B2107403 : Blo 2105435 2107403 := bstep (se 1 (by rfl) ⟨1580552, by rfl⟩ : syracuseStep 2107403 = 3161105) B3161105
theorem B7112501 : Blo 2105435 7112501 := bbase (se 5 (by rfl) ⟨333398, by rfl⟩ : syracuseStep 7112501 = 666797) (by norm_num)
theorem B4741667 : Blo 2105435 4741667 := bstep (se 1 (by rfl) ⟨3556250, by rfl⟩ : syracuseStep 4741667 = 7112501) B7112501
theorem B3161111 : Blo 2105435 3161111 := bstep (se 1 (by rfl) ⟨2370833, by rfl⟩ : syracuseStep 3161111 = 4741667) B4741667
theorem B2107407 : Blo 2105435 2107407 := bstep (se 1 (by rfl) ⟨1580555, by rfl⟩ : syracuseStep 2107407 = 3161111) B3161111
theorem B3161117 : Blo 2105435 3161117 := bbase (se 3 (by rfl) ⟨592709, by rfl⟩ : syracuseStep 3161117 = 1185419) (by norm_num)
theorem B2107411 : Blo 2105435 2107411 := bstep (se 1 (by rfl) ⟨1580558, by rfl⟩ : syracuseStep 2107411 = 3161117) B3161117
theorem B4741685 : Blo 2105435 4741685 := bbase (se 5 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 4741685 = 444533) (by norm_num)
theorem B3161123 : Blo 2105435 3161123 := bstep (se 1 (by rfl) ⟨2370842, by rfl⟩ : syracuseStep 3161123 = 4741685) B4741685
theorem B2107415 : Blo 2105435 2107415 := bstep (se 1 (by rfl) ⟨1580561, by rfl⟩ : syracuseStep 2107415 = 3161123) B3161123
theorem B9001813 : Blo 2105435 9001813 := bbase (se 9 (by rfl) ⟨26372, by rfl⟩ : syracuseStep 9001813 = 52745) (by norm_num)
theorem B12002417 : Blo 2105435 12002417 := bstep (se 2 (by rfl) ⟨4500906, by rfl⟩ : syracuseStep 12002417 = 9001813) B9001813
theorem B8001611 : Blo 2105435 8001611 := bstep (se 1 (by rfl) ⟨6001208, by rfl⟩ : syracuseStep 8001611 = 12002417) B12002417
theorem B5334407 : Blo 2105435 5334407 := bstep (se 1 (by rfl) ⟨4000805, by rfl⟩ : syracuseStep 5334407 = 8001611) B8001611
theorem B3556271 : Blo 2105435 3556271 := bstep (se 1 (by rfl) ⟨2667203, by rfl⟩ : syracuseStep 3556271 = 5334407) B5334407
theorem B2370847 : Blo 2105435 2370847 := bstep (se 1 (by rfl) ⟨1778135, by rfl⟩ : syracuseStep 2370847 = 3556271) B3556271
theorem B3161129 : Blo 2105435 3161129 := bstep (se 2 (by rfl) ⟨1185423, by rfl⟩ : syracuseStep 3161129 = 2370847) B2370847
theorem B2107419 : Blo 2105435 2107419 := bstep (se 1 (by rfl) ⟨1580564, by rfl⟩ : syracuseStep 2107419 = 3161129) B3161129
theorem B9001829 : Blo 2105435 9001829 := bbase (se 4 (by rfl) ⟨843921, by rfl⟩ : syracuseStep 9001829 = 1687843) (by norm_num)
theorem B6001219 : Blo 2105435 6001219 := bstep (se 1 (by rfl) ⟨4500914, by rfl⟩ : syracuseStep 6001219 = 9001829) B9001829
theorem B8001625 : Blo 2105435 8001625 := bstep (se 2 (by rfl) ⟨3000609, by rfl⟩ : syracuseStep 8001625 = 6001219) B6001219
theorem B10668833 : Blo 2105435 10668833 := bstep (se 2 (by rfl) ⟨4000812, by rfl⟩ : syracuseStep 10668833 = 8001625) B8001625
theorem B7112555 : Blo 2105435 7112555 := bstep (se 1 (by rfl) ⟨5334416, by rfl⟩ : syracuseStep 7112555 = 10668833) B10668833
theorem B4741703 : Blo 2105435 4741703 := bstep (se 1 (by rfl) ⟨3556277, by rfl⟩ : syracuseStep 4741703 = 7112555) B7112555
theorem B3161135 : Blo 2105435 3161135 := bstep (se 1 (by rfl) ⟨2370851, by rfl⟩ : syracuseStep 3161135 = 4741703) B4741703
theorem B2107423 : Blo 2105435 2107423 := bstep (se 1 (by rfl) ⟨1580567, by rfl⟩ : syracuseStep 2107423 = 3161135) B3161135
theorem B3161141 : Blo 2105435 3161141 := bbase (se 5 (by rfl) ⟨148178, by rfl⟩ : syracuseStep 3161141 = 296357) (by norm_num)
theorem B2107427 : Blo 2105435 2107427 := bstep (se 1 (by rfl) ⟨1580570, by rfl⟩ : syracuseStep 2107427 = 3161141) B3161141
theorem B5334437 : Blo 2105435 5334437 := bbase (se 4 (by rfl) ⟨500103, by rfl⟩ : syracuseStep 5334437 = 1000207) (by norm_num)
theorem B3556291 : Blo 2105435 3556291 := bstep (se 1 (by rfl) ⟨2667218, by rfl⟩ : syracuseStep 3556291 = 5334437) B5334437
theorem B4741721 : Blo 2105435 4741721 := bstep (se 2 (by rfl) ⟨1778145, by rfl⟩ : syracuseStep 4741721 = 3556291) B3556291
theorem B3161147 : Blo 2105435 3161147 := bstep (se 1 (by rfl) ⟨2370860, by rfl⟩ : syracuseStep 3161147 = 4741721) B4741721
theorem B2107431 : Blo 2105435 2107431 := bstep (se 1 (by rfl) ⟨1580573, by rfl⟩ : syracuseStep 2107431 = 3161147) B3161147
theorem B2370865 : Blo 2105435 2370865 := bbase (se 2 (by rfl) ⟨889074, by rfl⟩ : syracuseStep 2370865 = 1778149) (by norm_num)
theorem B3161153 : Blo 2105435 3161153 := bstep (se 2 (by rfl) ⟨1185432, by rfl⟩ : syracuseStep 3161153 = 2370865) B2370865
theorem B2107435 : Blo 2105435 2107435 := bstep (se 1 (by rfl) ⟨1580576, by rfl⟩ : syracuseStep 2107435 = 3161153) B3161153
theorem C0 (j : ℕ) (h1 : 526358 ≤ j) (h2 : j ≤ 526858) : Blo 2105435 (4 * j + 3) := by
  interval_cases j
  · exact B2105435
  · exact B2105439
  · exact B2105443
  · exact B2105447
  · exact B2105451
  · exact B2105455
  · exact B2105459
  · exact B2105463
  · exact B2105467
  · exact B2105471
  · exact B2105475
  · exact B2105479
  · exact B2105483
  · exact B2105487
  · exact B2105491
  · exact B2105495
  · exact B2105499
  · exact B2105503
  · exact B2105507
  · exact B2105511
  · exact B2105515
  · exact B2105519
  · exact B2105523
  · exact B2105527
  · exact B2105531
  · exact B2105535
  · exact B2105539
  · exact B2105543
  · exact B2105547
  · exact B2105551
  · exact B2105555
  · exact B2105559
  · exact B2105563
  · exact B2105567
  · exact B2105571
  · exact B2105575
  · exact B2105579
  · exact B2105583
  · exact B2105587
  · exact B2105591
  · exact B2105595
  · exact B2105599
  · exact B2105603
  · exact B2105607
  · exact B2105611
  · exact B2105615
  · exact B2105619
  · exact B2105623
  · exact B2105627
  · exact B2105631
  · exact B2105635
  · exact B2105639
  · exact B2105643
  · exact B2105647
  · exact B2105651
  · exact B2105655
  · exact B2105659
  · exact B2105663
  · exact B2105667
  · exact B2105671
  · exact B2105675
  · exact B2105679
  · exact B2105683
  · exact B2105687
  · exact B2105691
  · exact B2105695
  · exact B2105699
  · exact B2105703
  · exact B2105707
  · exact B2105711
  · exact B2105715
  · exact B2105719
  · exact B2105723
  · exact B2105727
  · exact B2105731
  · exact B2105735
  · exact B2105739
  · exact B2105743
  · exact B2105747
  · exact B2105751
  · exact B2105755
  · exact B2105759
  · exact B2105763
  · exact B2105767
  · exact B2105771
  · exact B2105775
  · exact B2105779
  · exact B2105783
  · exact B2105787
  · exact B2105791
  · exact B2105795
  · exact B2105799
  · exact B2105803
  · exact B2105807
  · exact B2105811
  · exact B2105815
  · exact B2105819
  · exact B2105823
  · exact B2105827
  · exact B2105831
  · exact B2105835
  · exact B2105839
  · exact B2105843
  · exact B2105847
  · exact B2105851
  · exact B2105855
  · exact B2105859
  · exact B2105863
  · exact B2105867
  · exact B2105871
  · exact B2105875
  · exact B2105879
  · exact B2105883
  · exact B2105887
  · exact B2105891
  · exact B2105895
  · exact B2105899
  · exact B2105903
  · exact B2105907
  · exact B2105911
  · exact B2105915
  · exact B2105919
  · exact B2105923
  · exact B2105927
  · exact B2105931
  · exact B2105935
  · exact B2105939
  · exact B2105943
  · exact B2105947
  · exact B2105951
  · exact B2105955
  · exact B2105959
  · exact B2105963
  · exact B2105967
  · exact B2105971
  · exact B2105975
  · exact B2105979
  · exact B2105983
  · exact B2105987
  · exact B2105991
  · exact B2105995
  · exact B2105999
  · exact B2106003
  · exact B2106007
  · exact B2106011
  · exact B2106015
  · exact B2106019
  · exact B2106023
  · exact B2106027
  · exact B2106031
  · exact B2106035
  · exact B2106039
  · exact B2106043
  · exact B2106047
  · exact B2106051
  · exact B2106055
  · exact B2106059
  · exact B2106063
  · exact B2106067
  · exact B2106071
  · exact B2106075
  · exact B2106079
  · exact B2106083
  · exact B2106087
  · exact B2106091
  · exact B2106095
  · exact B2106099
  · exact B2106103
  · exact B2106107
  · exact B2106111
  · exact B2106115
  · exact B2106119
  · exact B2106123
  · exact B2106127
  · exact B2106131
  · exact B2106135
  · exact B2106139
  · exact B2106143
  · exact B2106147
  · exact B2106151
  · exact B2106155
  · exact B2106159
  · exact B2106163
  · exact B2106167
  · exact B2106171
  · exact B2106175
  · exact B2106179
  · exact B2106183
  · exact B2106187
  · exact B2106191
  · exact B2106195
  · exact B2106199
  · exact B2106203
  · exact B2106207
  · exact B2106211
  · exact B2106215
  · exact B2106219
  · exact B2106223
  · exact B2106227
  · exact B2106231
  · exact B2106235
  · exact B2106239
  · exact B2106243
  · exact B2106247
  · exact B2106251
  · exact B2106255
  · exact B2106259
  · exact B2106263
  · exact B2106267
  · exact B2106271
  · exact B2106275
  · exact B2106279
  · exact B2106283
  · exact B2106287
  · exact B2106291
  · exact B2106295
  · exact B2106299
  · exact B2106303
  · exact B2106307
  · exact B2106311
  · exact B2106315
  · exact B2106319
  · exact B2106323
  · exact B2106327
  · exact B2106331
  · exact B2106335
  · exact B2106339
  · exact B2106343
  · exact B2106347
  · exact B2106351
  · exact B2106355
  · exact B2106359
  · exact B2106363
  · exact B2106367
  · exact B2106371
  · exact B2106375
  · exact B2106379
  · exact B2106383
  · exact B2106387
  · exact B2106391
  · exact B2106395
  · exact B2106399
  · exact B2106403
  · exact B2106407
  · exact B2106411
  · exact B2106415
  · exact B2106419
  · exact B2106423
  · exact B2106427
  · exact B2106431
  · exact B2106435
  · exact B2106439
  · exact B2106443
  · exact B2106447
  · exact B2106451
  · exact B2106455
  · exact B2106459
  · exact B2106463
  · exact B2106467
  · exact B2106471
  · exact B2106475
  · exact B2106479
  · exact B2106483
  · exact B2106487
  · exact B2106491
  · exact B2106495
  · exact B2106499
  · exact B2106503
  · exact B2106507
  · exact B2106511
  · exact B2106515
  · exact B2106519
  · exact B2106523
  · exact B2106527
  · exact B2106531
  · exact B2106535
  · exact B2106539
  · exact B2106543
  · exact B2106547
  · exact B2106551
  · exact B2106555
  · exact B2106559
  · exact B2106563
  · exact B2106567
  · exact B2106571
  · exact B2106575
  · exact B2106579
  · exact B2106583
  · exact B2106587
  · exact B2106591
  · exact B2106595
  · exact B2106599
  · exact B2106603
  · exact B2106607
  · exact B2106611
  · exact B2106615
  · exact B2106619
  · exact B2106623
  · exact B2106627
  · exact B2106631
  · exact B2106635
  · exact B2106639
  · exact B2106643
  · exact B2106647
  · exact B2106651
  · exact B2106655
  · exact B2106659
  · exact B2106663
  · exact B2106667
  · exact B2106671
  · exact B2106675
  · exact B2106679
  · exact B2106683
  · exact B2106687
  · exact B2106691
  · exact B2106695
  · exact B2106699
  · exact B2106703
  · exact B2106707
  · exact B2106711
  · exact B2106715
  · exact B2106719
  · exact B2106723
  · exact B2106727
  · exact B2106731
  · exact B2106735
  · exact B2106739
  · exact B2106743
  · exact B2106747
  · exact B2106751
  · exact B2106755
  · exact B2106759
  · exact B2106763
  · exact B2106767
  · exact B2106771
  · exact B2106775
  · exact B2106779
  · exact B2106783
  · exact B2106787
  · exact B2106791
  · exact B2106795
  · exact B2106799
  · exact B2106803
  · exact B2106807
  · exact B2106811
  · exact B2106815
  · exact B2106819
  · exact B2106823
  · exact B2106827
  · exact B2106831
  · exact B2106835
  · exact B2106839
  · exact B2106843
  · exact B2106847
  · exact B2106851
  · exact B2106855
  · exact B2106859
  · exact B2106863
  · exact B2106867
  · exact B2106871
  · exact B2106875
  · exact B2106879
  · exact B2106883
  · exact B2106887
  · exact B2106891
  · exact B2106895
  · exact B2106899
  · exact B2106903
  · exact B2106907
  · exact B2106911
  · exact B2106915
  · exact B2106919
  · exact B2106923
  · exact B2106927
  · exact B2106931
  · exact B2106935
  · exact B2106939
  · exact B2106943
  · exact B2106947
  · exact B2106951
  · exact B2106955
  · exact B2106959
  · exact B2106963
  · exact B2106967
  · exact B2106971
  · exact B2106975
  · exact B2106979
  · exact B2106983
  · exact B2106987
  · exact B2106991
  · exact B2106995
  · exact B2106999
  · exact B2107003
  · exact B2107007
  · exact B2107011
  · exact B2107015
  · exact B2107019
  · exact B2107023
  · exact B2107027
  · exact B2107031
  · exact B2107035
  · exact B2107039
  · exact B2107043
  · exact B2107047
  · exact B2107051
  · exact B2107055
  · exact B2107059
  · exact B2107063
  · exact B2107067
  · exact B2107071
  · exact B2107075
  · exact B2107079
  · exact B2107083
  · exact B2107087
  · exact B2107091
  · exact B2107095
  · exact B2107099
  · exact B2107103
  · exact B2107107
  · exact B2107111
  · exact B2107115
  · exact B2107119
  · exact B2107123
  · exact B2107127
  · exact B2107131
  · exact B2107135
  · exact B2107139
  · exact B2107143
  · exact B2107147
  · exact B2107151
  · exact B2107155
  · exact B2107159
  · exact B2107163
  · exact B2107167
  · exact B2107171
  · exact B2107175
  · exact B2107179
  · exact B2107183
  · exact B2107187
  · exact B2107191
  · exact B2107195
  · exact B2107199
  · exact B2107203
  · exact B2107207
  · exact B2107211
  · exact B2107215
  · exact B2107219
  · exact B2107223
  · exact B2107227
  · exact B2107231
  · exact B2107235
  · exact B2107239
  · exact B2107243
  · exact B2107247
  · exact B2107251
  · exact B2107255
  · exact B2107259
  · exact B2107263
  · exact B2107267
  · exact B2107271
  · exact B2107275
  · exact B2107279
  · exact B2107283
  · exact B2107287
  · exact B2107291
  · exact B2107295
  · exact B2107299
  · exact B2107303
  · exact B2107307
  · exact B2107311
  · exact B2107315
  · exact B2107319
  · exact B2107323
  · exact B2107327
  · exact B2107331
  · exact B2107335
  · exact B2107339
  · exact B2107343
  · exact B2107347
  · exact B2107351
  · exact B2107355
  · exact B2107359
  · exact B2107363
  · exact B2107367
  · exact B2107371
  · exact B2107375
  · exact B2107379
  · exact B2107383
  · exact B2107387
  · exact B2107391
  · exact B2107395
  · exact B2107399
  · exact B2107403
  · exact B2107407
  · exact B2107411
  · exact B2107415
  · exact B2107419
  · exact B2107423
  · exact B2107427
  · exact B2107431
  · exact B2107435
theorem solution (m : ℕ) (hlo : 2105435 ≤ m) (hhi : m ≤ 2107435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 526358 ≤ j := by omega
    have hj2 : j ≤ 526858 := by omega
    have hb : Blo 2105435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
