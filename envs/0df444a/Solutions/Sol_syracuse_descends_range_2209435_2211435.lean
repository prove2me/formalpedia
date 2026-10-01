-- Prove2me | solution 1 for syracuse_descends_range_2209435_2211435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:27.970069+00:00
-- url     : https://prove2.me/submissions/41bc85f3-a279-4661-a660-4da545c55356

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

theorem B9437573 : Blo 2209435 9437573 := bbase (se 4 (by rfl) ⟨884772, by rfl⟩ : syracuseStep 9437573 = 1769545) (by norm_num)
theorem B6291715 : Blo 2209435 6291715 := bstep (se 1 (by rfl) ⟨4718786, by rfl⟩ : syracuseStep 6291715 = 9437573) B9437573
theorem B8388953 : Blo 2209435 8388953 := bstep (se 2 (by rfl) ⟨3145857, by rfl⟩ : syracuseStep 8388953 = 6291715) B6291715
theorem B5592635 : Blo 2209435 5592635 := bstep (se 1 (by rfl) ⟨4194476, by rfl⟩ : syracuseStep 5592635 = 8388953) B8388953
theorem B3728423 : Blo 2209435 3728423 := bstep (se 1 (by rfl) ⟨2796317, by rfl⟩ : syracuseStep 3728423 = 5592635) B5592635
theorem B2485615 : Blo 2209435 2485615 := bstep (se 1 (by rfl) ⟨1864211, by rfl⟩ : syracuseStep 2485615 = 3728423) B3728423
theorem B3314153 : Blo 2209435 3314153 := bstep (se 2 (by rfl) ⟨1242807, by rfl⟩ : syracuseStep 3314153 = 2485615) B2485615
theorem B2209435 : Blo 2209435 2209435 := bstep (se 1 (by rfl) ⟨1657076, by rfl⟩ : syracuseStep 2209435 = 3314153) B3314153
theorem B7558597 : Blo 2209435 7558597 := bbase (se 4 (by rfl) ⟨708618, by rfl⟩ : syracuseStep 7558597 = 1417237) (by norm_num)
theorem B10078129 : Blo 2209435 10078129 := bstep (se 2 (by rfl) ⟨3779298, by rfl⟩ : syracuseStep 10078129 = 7558597) B7558597
theorem B13437505 : Blo 2209435 13437505 := bstep (se 2 (by rfl) ⟨5039064, by rfl⟩ : syracuseStep 13437505 = 10078129) B10078129
theorem B71666693 : Blo 2209435 71666693 := bstep (se 4 (by rfl) ⟨6718752, by rfl⟩ : syracuseStep 71666693 = 13437505) B13437505
theorem B47777795 : Blo 2209435 47777795 := bstep (se 1 (by rfl) ⟨35833346, by rfl⟩ : syracuseStep 47777795 = 71666693) B71666693
theorem B31851863 : Blo 2209435 31851863 := bstep (se 1 (by rfl) ⟨23888897, by rfl⟩ : syracuseStep 31851863 = 47777795) B47777795
theorem B21234575 : Blo 2209435 21234575 := bstep (se 1 (by rfl) ⟨15925931, by rfl⟩ : syracuseStep 21234575 = 31851863) B31851863
theorem B14156383 : Blo 2209435 14156383 := bstep (se 1 (by rfl) ⟨10617287, by rfl⟩ : syracuseStep 14156383 = 21234575) B21234575
theorem B18875177 : Blo 2209435 18875177 := bstep (se 2 (by rfl) ⟨7078191, by rfl⟩ : syracuseStep 18875177 = 14156383) B14156383
theorem B12583451 : Blo 2209435 12583451 := bstep (se 1 (by rfl) ⟨9437588, by rfl⟩ : syracuseStep 12583451 = 18875177) B18875177
theorem B8388967 : Blo 2209435 8388967 := bstep (se 1 (by rfl) ⟨6291725, by rfl⟩ : syracuseStep 8388967 = 12583451) B12583451
theorem B11185289 : Blo 2209435 11185289 := bstep (se 2 (by rfl) ⟨4194483, by rfl⟩ : syracuseStep 11185289 = 8388967) B8388967
theorem B7456859 : Blo 2209435 7456859 := bstep (se 1 (by rfl) ⟨5592644, by rfl⟩ : syracuseStep 7456859 = 11185289) B11185289
theorem B4971239 : Blo 2209435 4971239 := bstep (se 1 (by rfl) ⟨3728429, by rfl⟩ : syracuseStep 4971239 = 7456859) B7456859
theorem B3314159 : Blo 2209435 3314159 := bstep (se 1 (by rfl) ⟨2485619, by rfl⟩ : syracuseStep 3314159 = 4971239) B4971239
theorem B2209439 : Blo 2209435 2209439 := bstep (se 1 (by rfl) ⟨1657079, by rfl⟩ : syracuseStep 2209439 = 3314159) B3314159
theorem B3314165 : Blo 2209435 3314165 := bbase (se 5 (by rfl) ⟨155351, by rfl⟩ : syracuseStep 3314165 = 310703) (by norm_num)
theorem B2209443 : Blo 2209435 2209443 := bstep (se 1 (by rfl) ⟨1657082, by rfl⟩ : syracuseStep 2209443 = 3314165) B3314165
theorem B6291749 : Blo 2209435 6291749 := bbase (se 4 (by rfl) ⟨589851, by rfl⟩ : syracuseStep 6291749 = 1179703) (by norm_num)
theorem B4194499 : Blo 2209435 4194499 := bstep (se 1 (by rfl) ⟨3145874, by rfl⟩ : syracuseStep 4194499 = 6291749) B6291749
theorem B5592665 : Blo 2209435 5592665 := bstep (se 2 (by rfl) ⟨2097249, by rfl⟩ : syracuseStep 5592665 = 4194499) B4194499
theorem B3728443 : Blo 2209435 3728443 := bstep (se 1 (by rfl) ⟨2796332, by rfl⟩ : syracuseStep 3728443 = 5592665) B5592665
theorem B4971257 : Blo 2209435 4971257 := bstep (se 2 (by rfl) ⟨1864221, by rfl⟩ : syracuseStep 4971257 = 3728443) B3728443
theorem B3314171 : Blo 2209435 3314171 := bstep (se 1 (by rfl) ⟨2485628, by rfl⟩ : syracuseStep 3314171 = 4971257) B4971257
theorem B2209447 : Blo 2209435 2209447 := bstep (se 1 (by rfl) ⟨1657085, by rfl⟩ : syracuseStep 2209447 = 3314171) B3314171
theorem B2485633 : Blo 2209435 2485633 := bbase (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) (by norm_num)
theorem B3314177 : Blo 2209435 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B2209451 : Blo 2209435 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B5592685 : Blo 2209435 5592685 := bbase (se 3 (by rfl) ⟨1048628, by rfl⟩ : syracuseStep 5592685 = 2097257) (by norm_num)
theorem B7456913 : Blo 2209435 7456913 := bstep (se 2 (by rfl) ⟨2796342, by rfl⟩ : syracuseStep 7456913 = 5592685) B5592685
theorem B4971275 : Blo 2209435 4971275 := bstep (se 1 (by rfl) ⟨3728456, by rfl⟩ : syracuseStep 4971275 = 7456913) B7456913
theorem B3314183 : Blo 2209435 3314183 := bstep (se 1 (by rfl) ⟨2485637, by rfl⟩ : syracuseStep 3314183 = 4971275) B4971275
theorem B2209455 : Blo 2209435 2209455 := bstep (se 1 (by rfl) ⟨1657091, by rfl⟩ : syracuseStep 2209455 = 3314183) B3314183
theorem B3314189 : Blo 2209435 3314189 := bbase (se 3 (by rfl) ⟨621410, by rfl⟩ : syracuseStep 3314189 = 1242821) (by norm_num)
theorem B2209459 : Blo 2209435 2209459 := bstep (se 1 (by rfl) ⟨1657094, by rfl⟩ : syracuseStep 2209459 = 3314189) B3314189
theorem B4971293 : Blo 2209435 4971293 := bbase (se 3 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 4971293 = 1864235) (by norm_num)
theorem B3314195 : Blo 2209435 3314195 := bstep (se 1 (by rfl) ⟨2485646, by rfl⟩ : syracuseStep 3314195 = 4971293) B4971293
theorem B2209463 : Blo 2209435 2209463 := bstep (se 1 (by rfl) ⟨1657097, by rfl⟩ : syracuseStep 2209463 = 3314195) B3314195
theorem B3728477 : Blo 2209435 3728477 := bbase (se 3 (by rfl) ⟨699089, by rfl⟩ : syracuseStep 3728477 = 1398179) (by norm_num)
theorem B2485651 : Blo 2209435 2485651 := bstep (se 1 (by rfl) ⟨1864238, by rfl⟩ : syracuseStep 2485651 = 3728477) B3728477
theorem B3314201 : Blo 2209435 3314201 := bstep (se 2 (by rfl) ⟨1242825, by rfl⟩ : syracuseStep 3314201 = 2485651) B2485651
theorem B2209467 : Blo 2209435 2209467 := bstep (se 1 (by rfl) ⟨1657100, by rfl⟩ : syracuseStep 2209467 = 3314201) B3314201
theorem B3981541 : Blo 2209435 3981541 := bbase (se 4 (by rfl) ⟨373269, by rfl⟩ : syracuseStep 3981541 = 746539) (by norm_num)
theorem B5308721 : Blo 2209435 5308721 := bstep (se 2 (by rfl) ⟨1990770, by rfl⟩ : syracuseStep 5308721 = 3981541) B3981541
theorem B3539147 : Blo 2209435 3539147 := bstep (se 1 (by rfl) ⟨2654360, by rfl⟩ : syracuseStep 3539147 = 5308721) B5308721
theorem B9437725 : Blo 2209435 9437725 := bstep (se 3 (by rfl) ⟨1769573, by rfl⟩ : syracuseStep 9437725 = 3539147) B3539147
theorem B12583633 : Blo 2209435 12583633 := bstep (se 2 (by rfl) ⟨4718862, by rfl⟩ : syracuseStep 12583633 = 9437725) B9437725
theorem B16778177 : Blo 2209435 16778177 := bstep (se 2 (by rfl) ⟨6291816, by rfl⟩ : syracuseStep 16778177 = 12583633) B12583633
theorem B11185451 : Blo 2209435 11185451 := bstep (se 1 (by rfl) ⟨8389088, by rfl⟩ : syracuseStep 11185451 = 16778177) B16778177
theorem B7456967 : Blo 2209435 7456967 := bstep (se 1 (by rfl) ⟨5592725, by rfl⟩ : syracuseStep 7456967 = 11185451) B11185451
theorem B4971311 : Blo 2209435 4971311 := bstep (se 1 (by rfl) ⟨3728483, by rfl⟩ : syracuseStep 4971311 = 7456967) B7456967
theorem B3314207 : Blo 2209435 3314207 := bstep (se 1 (by rfl) ⟨2485655, by rfl⟩ : syracuseStep 3314207 = 4971311) B4971311
theorem B2209471 : Blo 2209435 2209471 := bstep (se 1 (by rfl) ⟨1657103, by rfl⟩ : syracuseStep 2209471 = 3314207) B3314207
theorem B3314213 : Blo 2209435 3314213 := bbase (se 4 (by rfl) ⟨310707, by rfl⟩ : syracuseStep 3314213 = 621415) (by norm_num)
theorem B2209475 : Blo 2209435 2209475 := bstep (se 1 (by rfl) ⟨1657106, by rfl⟩ : syracuseStep 2209475 = 3314213) B3314213
theorem B2796373 : Blo 2209435 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B3728497 : Blo 2209435 3728497 := bstep (se 2 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 3728497 = 2796373) B2796373
theorem B4971329 : Blo 2209435 4971329 := bstep (se 2 (by rfl) ⟨1864248, by rfl⟩ : syracuseStep 4971329 = 3728497) B3728497
theorem B3314219 : Blo 2209435 3314219 := bstep (se 1 (by rfl) ⟨2485664, by rfl⟩ : syracuseStep 3314219 = 4971329) B4971329
theorem B2209479 : Blo 2209435 2209479 := bstep (se 1 (by rfl) ⟨1657109, by rfl⟩ : syracuseStep 2209479 = 3314219) B3314219
theorem B2485669 : Blo 2209435 2485669 := bbase (se 4 (by rfl) ⟨233031, by rfl⟩ : syracuseStep 2485669 = 466063) (by norm_num)
theorem B3314225 : Blo 2209435 3314225 := bstep (se 2 (by rfl) ⟨1242834, by rfl⟩ : syracuseStep 3314225 = 2485669) B2485669
theorem B2209483 : Blo 2209435 2209483 := bstep (se 1 (by rfl) ⟨1657112, by rfl⟩ : syracuseStep 2209483 = 3314225) B3314225
theorem B14156693 : Blo 2209435 14156693 := bbase (se 6 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 14156693 = 663595) (by norm_num)
theorem B9437795 : Blo 2209435 9437795 := bstep (se 1 (by rfl) ⟨7078346, by rfl⟩ : syracuseStep 9437795 = 14156693) B14156693
theorem B6291863 : Blo 2209435 6291863 := bstep (se 1 (by rfl) ⟨4718897, by rfl⟩ : syracuseStep 6291863 = 9437795) B9437795
theorem B4194575 : Blo 2209435 4194575 := bstep (se 1 (by rfl) ⟨3145931, by rfl⟩ : syracuseStep 4194575 = 6291863) B6291863
theorem B2796383 : Blo 2209435 2796383 := bstep (se 1 (by rfl) ⟨2097287, by rfl⟩ : syracuseStep 2796383 = 4194575) B4194575
theorem B7457021 : Blo 2209435 7457021 := bstep (se 3 (by rfl) ⟨1398191, by rfl⟩ : syracuseStep 7457021 = 2796383) B2796383
theorem B4971347 : Blo 2209435 4971347 := bstep (se 1 (by rfl) ⟨3728510, by rfl⟩ : syracuseStep 4971347 = 7457021) B7457021
theorem B3314231 : Blo 2209435 3314231 := bstep (se 1 (by rfl) ⟨2485673, by rfl⟩ : syracuseStep 3314231 = 4971347) B4971347
theorem B2209487 : Blo 2209435 2209487 := bstep (se 1 (by rfl) ⟨1657115, by rfl⟩ : syracuseStep 2209487 = 3314231) B3314231
theorem B3314237 : Blo 2209435 3314237 := bbase (se 3 (by rfl) ⟨621419, by rfl⟩ : syracuseStep 3314237 = 1242839) (by norm_num)
theorem B2209491 : Blo 2209435 2209491 := bstep (se 1 (by rfl) ⟨1657118, by rfl⟩ : syracuseStep 2209491 = 3314237) B3314237
theorem B4971365 : Blo 2209435 4971365 := bbase (se 4 (by rfl) ⟨466065, by rfl⟩ : syracuseStep 4971365 = 932131) (by norm_num)
theorem B3314243 : Blo 2209435 3314243 := bstep (se 1 (by rfl) ⟨2485682, by rfl⟩ : syracuseStep 3314243 = 4971365) B4971365
theorem B2209495 : Blo 2209435 2209495 := bstep (se 1 (by rfl) ⟨1657121, by rfl⟩ : syracuseStep 2209495 = 3314243) B3314243
theorem B5592797 : Blo 2209435 5592797 := bbase (se 3 (by rfl) ⟨1048649, by rfl⟩ : syracuseStep 5592797 = 2097299) (by norm_num)
theorem B3728531 : Blo 2209435 3728531 := bstep (se 1 (by rfl) ⟨2796398, by rfl⟩ : syracuseStep 3728531 = 5592797) B5592797
theorem B2485687 : Blo 2209435 2485687 := bstep (se 1 (by rfl) ⟨1864265, by rfl⟩ : syracuseStep 2485687 = 3728531) B3728531
theorem B3314249 : Blo 2209435 3314249 := bstep (se 2 (by rfl) ⟨1242843, by rfl⟩ : syracuseStep 3314249 = 2485687) B2485687
theorem B2209499 : Blo 2209435 2209499 := bstep (se 1 (by rfl) ⟨1657124, by rfl⟩ : syracuseStep 2209499 = 3314249) B3314249
theorem B4194605 : Blo 2209435 4194605 := bbase (se 3 (by rfl) ⟨786488, by rfl⟩ : syracuseStep 4194605 = 1572977) (by norm_num)
theorem B11185613 : Blo 2209435 11185613 := bstep (se 3 (by rfl) ⟨2097302, by rfl⟩ : syracuseStep 11185613 = 4194605) B4194605
theorem B7457075 : Blo 2209435 7457075 := bstep (se 1 (by rfl) ⟨5592806, by rfl⟩ : syracuseStep 7457075 = 11185613) B11185613
theorem B4971383 : Blo 2209435 4971383 := bstep (se 1 (by rfl) ⟨3728537, by rfl⟩ : syracuseStep 4971383 = 7457075) B7457075
theorem B3314255 : Blo 2209435 3314255 := bstep (se 1 (by rfl) ⟨2485691, by rfl⟩ : syracuseStep 3314255 = 4971383) B4971383
theorem B2209503 : Blo 2209435 2209503 := bstep (se 1 (by rfl) ⟨1657127, by rfl⟩ : syracuseStep 2209503 = 3314255) B3314255
theorem B3314261 : Blo 2209435 3314261 := bbase (se 8 (by rfl) ⟨19419, by rfl⟩ : syracuseStep 3314261 = 38839) (by norm_num)
theorem B2209507 : Blo 2209435 2209507 := bstep (se 1 (by rfl) ⟨1657130, by rfl⟩ : syracuseStep 2209507 = 3314261) B3314261
theorem B15926453 : Blo 2209435 15926453 := bbase (se 5 (by rfl) ⟨746552, by rfl⟩ : syracuseStep 15926453 = 1493105) (by norm_num)
theorem B10617635 : Blo 2209435 10617635 := bstep (se 1 (by rfl) ⟨7963226, by rfl⟩ : syracuseStep 10617635 = 15926453) B15926453
theorem B7078423 : Blo 2209435 7078423 := bstep (se 1 (by rfl) ⟨5308817, by rfl⟩ : syracuseStep 7078423 = 10617635) B10617635
theorem B9437897 : Blo 2209435 9437897 := bstep (se 2 (by rfl) ⟨3539211, by rfl⟩ : syracuseStep 9437897 = 7078423) B7078423
theorem B6291931 : Blo 2209435 6291931 := bstep (se 1 (by rfl) ⟨4718948, by rfl⟩ : syracuseStep 6291931 = 9437897) B9437897
theorem B8389241 : Blo 2209435 8389241 := bstep (se 2 (by rfl) ⟨3145965, by rfl⟩ : syracuseStep 8389241 = 6291931) B6291931
theorem B5592827 : Blo 2209435 5592827 := bstep (se 1 (by rfl) ⟨4194620, by rfl⟩ : syracuseStep 5592827 = 8389241) B8389241
theorem B3728551 : Blo 2209435 3728551 := bstep (se 1 (by rfl) ⟨2796413, by rfl⟩ : syracuseStep 3728551 = 5592827) B5592827
theorem B4971401 : Blo 2209435 4971401 := bstep (se 2 (by rfl) ⟨1864275, by rfl⟩ : syracuseStep 4971401 = 3728551) B3728551
theorem B3314267 : Blo 2209435 3314267 := bstep (se 1 (by rfl) ⟨2485700, by rfl⟩ : syracuseStep 3314267 = 4971401) B4971401
theorem B2209511 : Blo 2209435 2209511 := bstep (se 1 (by rfl) ⟨1657133, by rfl⟩ : syracuseStep 2209511 = 3314267) B3314267
theorem B2485705 : Blo 2209435 2485705 := bbase (se 2 (by rfl) ⟨932139, by rfl⟩ : syracuseStep 2485705 = 1864279) (by norm_num)
theorem B3314273 : Blo 2209435 3314273 := bstep (se 2 (by rfl) ⟨1242852, by rfl⟩ : syracuseStep 3314273 = 2485705) B2485705
theorem B2209515 : Blo 2209435 2209515 := bstep (se 1 (by rfl) ⟨1657136, by rfl⟩ : syracuseStep 2209515 = 3314273) B3314273
theorem B18875861 : Blo 2209435 18875861 := bbase (se 7 (by rfl) ⟨221201, by rfl⟩ : syracuseStep 18875861 = 442403) (by norm_num)
theorem B12583907 : Blo 2209435 12583907 := bstep (se 1 (by rfl) ⟨9437930, by rfl⟩ : syracuseStep 12583907 = 18875861) B18875861
theorem B8389271 : Blo 2209435 8389271 := bstep (se 1 (by rfl) ⟨6291953, by rfl⟩ : syracuseStep 8389271 = 12583907) B12583907
theorem B5592847 : Blo 2209435 5592847 := bstep (se 1 (by rfl) ⟨4194635, by rfl⟩ : syracuseStep 5592847 = 8389271) B8389271
theorem B7457129 : Blo 2209435 7457129 := bstep (se 2 (by rfl) ⟨2796423, by rfl⟩ : syracuseStep 7457129 = 5592847) B5592847
theorem B4971419 : Blo 2209435 4971419 := bstep (se 1 (by rfl) ⟨3728564, by rfl⟩ : syracuseStep 4971419 = 7457129) B7457129
theorem B3314279 : Blo 2209435 3314279 := bstep (se 1 (by rfl) ⟨2485709, by rfl⟩ : syracuseStep 3314279 = 4971419) B4971419
theorem B2209519 : Blo 2209435 2209519 := bstep (se 1 (by rfl) ⟨1657139, by rfl⟩ : syracuseStep 2209519 = 3314279) B3314279
theorem B3314285 : Blo 2209435 3314285 := bbase (se 3 (by rfl) ⟨621428, by rfl⟩ : syracuseStep 3314285 = 1242857) (by norm_num)
theorem B2209523 : Blo 2209435 2209523 := bstep (se 1 (by rfl) ⟨1657142, by rfl⟩ : syracuseStep 2209523 = 3314285) B3314285
theorem B4971437 : Blo 2209435 4971437 := bbase (se 3 (by rfl) ⟨932144, by rfl⟩ : syracuseStep 4971437 = 1864289) (by norm_num)
theorem B3314291 : Blo 2209435 3314291 := bstep (se 1 (by rfl) ⟨2485718, by rfl⟩ : syracuseStep 3314291 = 4971437) B4971437
theorem B2209527 : Blo 2209435 2209527 := bstep (se 1 (by rfl) ⟨1657145, by rfl⟩ : syracuseStep 2209527 = 3314291) B3314291
theorem B6291989 : Blo 2209435 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B4194659 : Blo 2209435 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B2796439 : Blo 2209435 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B3728585 : Blo 2209435 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B2485723 : Blo 2209435 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B3314297 : Blo 2209435 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B2209531 : Blo 2209435 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B2834597 : Blo 2209435 2834597 := bbase (se 4 (by rfl) ⟨265743, by rfl⟩ : syracuseStep 2834597 = 531487) (by norm_num)
theorem B7558925 : Blo 2209435 7558925 := bstep (se 3 (by rfl) ⟨1417298, by rfl⟩ : syracuseStep 7558925 = 2834597) B2834597
theorem B20157133 : Blo 2209435 20157133 := bstep (se 3 (by rfl) ⟨3779462, by rfl⟩ : syracuseStep 20157133 = 7558925) B7558925
theorem B26876177 : Blo 2209435 26876177 := bstep (se 2 (by rfl) ⟨10078566, by rfl⟩ : syracuseStep 26876177 = 20157133) B20157133
theorem B17917451 : Blo 2209435 17917451 := bstep (se 1 (by rfl) ⟨13438088, by rfl⟩ : syracuseStep 17917451 = 26876177) B26876177
theorem B11944967 : Blo 2209435 11944967 := bstep (se 1 (by rfl) ⟨8958725, by rfl⟩ : syracuseStep 11944967 = 17917451) B17917451
theorem B31853245 : Blo 2209435 31853245 := bstep (se 3 (by rfl) ⟨5972483, by rfl⟩ : syracuseStep 31853245 = 11944967) B11944967
theorem B42470993 : Blo 2209435 42470993 := bstep (se 2 (by rfl) ⟨15926622, by rfl⟩ : syracuseStep 42470993 = 31853245) B31853245
theorem B28313995 : Blo 2209435 28313995 := bstep (se 1 (by rfl) ⟨21235496, by rfl⟩ : syracuseStep 28313995 = 42470993) B42470993
theorem B37751993 : Blo 2209435 37751993 := bstep (se 2 (by rfl) ⟨14156997, by rfl⟩ : syracuseStep 37751993 = 28313995) B28313995
theorem B25167995 : Blo 2209435 25167995 := bstep (se 1 (by rfl) ⟨18875996, by rfl⟩ : syracuseStep 25167995 = 37751993) B37751993
theorem B16778663 : Blo 2209435 16778663 := bstep (se 1 (by rfl) ⟨12583997, by rfl⟩ : syracuseStep 16778663 = 25167995) B25167995
theorem B11185775 : Blo 2209435 11185775 := bstep (se 1 (by rfl) ⟨8389331, by rfl⟩ : syracuseStep 11185775 = 16778663) B16778663
theorem B7457183 : Blo 2209435 7457183 := bstep (se 1 (by rfl) ⟨5592887, by rfl⟩ : syracuseStep 7457183 = 11185775) B11185775
theorem B4971455 : Blo 2209435 4971455 := bstep (se 1 (by rfl) ⟨3728591, by rfl⟩ : syracuseStep 4971455 = 7457183) B7457183
theorem B3314303 : Blo 2209435 3314303 := bstep (se 1 (by rfl) ⟨2485727, by rfl⟩ : syracuseStep 3314303 = 4971455) B4971455
theorem B2209535 : Blo 2209435 2209535 := bstep (se 1 (by rfl) ⟨1657151, by rfl⟩ : syracuseStep 2209535 = 3314303) B3314303
theorem B3314309 : Blo 2209435 3314309 := bbase (se 4 (by rfl) ⟨310716, by rfl⟩ : syracuseStep 3314309 = 621433) (by norm_num)
theorem B2209539 : Blo 2209435 2209539 := bstep (se 1 (by rfl) ⟨1657154, by rfl⟩ : syracuseStep 2209539 = 3314309) B3314309
theorem B3728605 : Blo 2209435 3728605 := bbase (se 3 (by rfl) ⟨699113, by rfl⟩ : syracuseStep 3728605 = 1398227) (by norm_num)
theorem B4971473 : Blo 2209435 4971473 := bstep (se 2 (by rfl) ⟨1864302, by rfl⟩ : syracuseStep 4971473 = 3728605) B3728605
theorem B3314315 : Blo 2209435 3314315 := bstep (se 1 (by rfl) ⟨2485736, by rfl⟩ : syracuseStep 3314315 = 4971473) B4971473
theorem B2209543 : Blo 2209435 2209543 := bstep (se 1 (by rfl) ⟨1657157, by rfl⟩ : syracuseStep 2209543 = 3314315) B3314315
theorem B2485741 : Blo 2209435 2485741 := bbase (se 3 (by rfl) ⟨466076, by rfl⟩ : syracuseStep 2485741 = 932153) (by norm_num)
theorem B3314321 : Blo 2209435 3314321 := bstep (se 2 (by rfl) ⟨1242870, by rfl⟩ : syracuseStep 3314321 = 2485741) B2485741
theorem B2209547 : Blo 2209435 2209547 := bstep (se 1 (by rfl) ⟨1657160, by rfl⟩ : syracuseStep 2209547 = 3314321) B3314321
theorem B7457237 : Blo 2209435 7457237 := bbase (se 7 (by rfl) ⟨87389, by rfl⟩ : syracuseStep 7457237 = 174779) (by norm_num)
theorem B4971491 : Blo 2209435 4971491 := bstep (se 1 (by rfl) ⟨3728618, by rfl⟩ : syracuseStep 4971491 = 7457237) B7457237
theorem B3314327 : Blo 2209435 3314327 := bstep (se 1 (by rfl) ⟨2485745, by rfl⟩ : syracuseStep 3314327 = 4971491) B4971491
theorem B2209551 : Blo 2209435 2209551 := bstep (se 1 (by rfl) ⟨1657163, by rfl⟩ : syracuseStep 2209551 = 3314327) B3314327
theorem B3314333 : Blo 2209435 3314333 := bbase (se 3 (by rfl) ⟨621437, by rfl⟩ : syracuseStep 3314333 = 1242875) (by norm_num)
theorem B2209555 : Blo 2209435 2209555 := bstep (se 1 (by rfl) ⟨1657166, by rfl⟩ : syracuseStep 2209555 = 3314333) B3314333
theorem B4971509 : Blo 2209435 4971509 := bbase (se 5 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 4971509 = 466079) (by norm_num)
theorem B3314339 : Blo 2209435 3314339 := bstep (se 1 (by rfl) ⟨2485754, by rfl⟩ : syracuseStep 3314339 = 4971509) B4971509
theorem B2209559 : Blo 2209435 2209559 := bstep (se 1 (by rfl) ⟨1657169, by rfl⟩ : syracuseStep 2209559 = 3314339) B3314339
theorem B13438261 : Blo 2209435 13438261 := bbase (se 5 (by rfl) ⟨629918, by rfl⟩ : syracuseStep 13438261 = 1259837) (by norm_num)
theorem B17917681 : Blo 2209435 17917681 := bstep (se 2 (by rfl) ⟨6719130, by rfl⟩ : syracuseStep 17917681 = 13438261) B13438261
theorem B23890241 : Blo 2209435 23890241 := bstep (se 2 (by rfl) ⟨8958840, by rfl⟩ : syracuseStep 23890241 = 17917681) B17917681
theorem B63707309 : Blo 2209435 63707309 := bstep (se 3 (by rfl) ⟨11945120, by rfl⟩ : syracuseStep 63707309 = 23890241) B23890241
theorem B42471539 : Blo 2209435 42471539 := bstep (se 1 (by rfl) ⟨31853654, by rfl⟩ : syracuseStep 42471539 = 63707309) B63707309
theorem B28314359 : Blo 2209435 28314359 := bstep (se 1 (by rfl) ⟨21235769, by rfl⟩ : syracuseStep 28314359 = 42471539) B42471539
theorem B18876239 : Blo 2209435 18876239 := bstep (se 1 (by rfl) ⟨14157179, by rfl⟩ : syracuseStep 18876239 = 28314359) B28314359
theorem B12584159 : Blo 2209435 12584159 := bstep (se 1 (by rfl) ⟨9438119, by rfl⟩ : syracuseStep 12584159 = 18876239) B18876239
theorem B8389439 : Blo 2209435 8389439 := bstep (se 1 (by rfl) ⟨6292079, by rfl⟩ : syracuseStep 8389439 = 12584159) B12584159
theorem B5592959 : Blo 2209435 5592959 := bstep (se 1 (by rfl) ⟨4194719, by rfl⟩ : syracuseStep 5592959 = 8389439) B8389439
theorem B3728639 : Blo 2209435 3728639 := bstep (se 1 (by rfl) ⟨2796479, by rfl⟩ : syracuseStep 3728639 = 5592959) B5592959
theorem B2485759 : Blo 2209435 2485759 := bstep (se 1 (by rfl) ⟨1864319, by rfl⟩ : syracuseStep 2485759 = 3728639) B3728639
theorem B3314345 : Blo 2209435 3314345 := bstep (se 2 (by rfl) ⟨1242879, by rfl⟩ : syracuseStep 3314345 = 2485759) B2485759
theorem B2209563 : Blo 2209435 2209563 := bstep (se 1 (by rfl) ⟨1657172, by rfl⟩ : syracuseStep 2209563 = 3314345) B3314345
theorem B3146045 : Blo 2209435 3146045 := bbase (se 3 (by rfl) ⟨589883, by rfl⟩ : syracuseStep 3146045 = 1179767) (by norm_num)
theorem B8389453 : Blo 2209435 8389453 := bstep (se 3 (by rfl) ⟨1573022, by rfl⟩ : syracuseStep 8389453 = 3146045) B3146045
theorem B11185937 : Blo 2209435 11185937 := bstep (se 2 (by rfl) ⟨4194726, by rfl⟩ : syracuseStep 11185937 = 8389453) B8389453
theorem B7457291 : Blo 2209435 7457291 := bstep (se 1 (by rfl) ⟨5592968, by rfl⟩ : syracuseStep 7457291 = 11185937) B11185937
theorem B4971527 : Blo 2209435 4971527 := bstep (se 1 (by rfl) ⟨3728645, by rfl⟩ : syracuseStep 4971527 = 7457291) B7457291
theorem B3314351 : Blo 2209435 3314351 := bstep (se 1 (by rfl) ⟨2485763, by rfl⟩ : syracuseStep 3314351 = 4971527) B4971527
theorem B2209567 : Blo 2209435 2209567 := bstep (se 1 (by rfl) ⟨1657175, by rfl⟩ : syracuseStep 2209567 = 3314351) B3314351
theorem B3314357 : Blo 2209435 3314357 := bbase (se 5 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 3314357 = 310721) (by norm_num)
theorem B2209571 : Blo 2209435 2209571 := bstep (se 1 (by rfl) ⟨1657178, by rfl⟩ : syracuseStep 2209571 = 3314357) B3314357
theorem B5592989 : Blo 2209435 5592989 := bbase (se 3 (by rfl) ⟨1048685, by rfl⟩ : syracuseStep 5592989 = 2097371) (by norm_num)
theorem B3728659 : Blo 2209435 3728659 := bstep (se 1 (by rfl) ⟨2796494, by rfl⟩ : syracuseStep 3728659 = 5592989) B5592989
theorem B4971545 : Blo 2209435 4971545 := bstep (se 2 (by rfl) ⟨1864329, by rfl⟩ : syracuseStep 4971545 = 3728659) B3728659
theorem B3314363 : Blo 2209435 3314363 := bstep (se 1 (by rfl) ⟨2485772, by rfl⟩ : syracuseStep 3314363 = 4971545) B4971545
theorem B2209575 : Blo 2209435 2209575 := bstep (se 1 (by rfl) ⟨1657181, by rfl⟩ : syracuseStep 2209575 = 3314363) B3314363
theorem B2485777 : Blo 2209435 2485777 := bbase (se 2 (by rfl) ⟨932166, by rfl⟩ : syracuseStep 2485777 = 1864333) (by norm_num)
theorem B3314369 : Blo 2209435 3314369 := bstep (se 2 (by rfl) ⟨1242888, by rfl⟩ : syracuseStep 3314369 = 2485777) B2485777
theorem B2209579 : Blo 2209435 2209579 := bstep (se 1 (by rfl) ⟨1657184, by rfl⟩ : syracuseStep 2209579 = 3314369) B3314369
theorem B4194757 : Blo 2209435 4194757 := bbase (se 4 (by rfl) ⟨393258, by rfl⟩ : syracuseStep 4194757 = 786517) (by norm_num)
theorem B5593009 : Blo 2209435 5593009 := bstep (se 2 (by rfl) ⟨2097378, by rfl⟩ : syracuseStep 5593009 = 4194757) B4194757
theorem B7457345 : Blo 2209435 7457345 := bstep (se 2 (by rfl) ⟨2796504, by rfl⟩ : syracuseStep 7457345 = 5593009) B5593009
theorem B4971563 : Blo 2209435 4971563 := bstep (se 1 (by rfl) ⟨3728672, by rfl⟩ : syracuseStep 4971563 = 7457345) B7457345
theorem B3314375 : Blo 2209435 3314375 := bstep (se 1 (by rfl) ⟨2485781, by rfl⟩ : syracuseStep 3314375 = 4971563) B4971563
theorem B2209583 : Blo 2209435 2209583 := bstep (se 1 (by rfl) ⟨1657187, by rfl⟩ : syracuseStep 2209583 = 3314375) B3314375
theorem B3314381 : Blo 2209435 3314381 := bbase (se 3 (by rfl) ⟨621446, by rfl⟩ : syracuseStep 3314381 = 1242893) (by norm_num)
theorem B2209587 : Blo 2209435 2209587 := bstep (se 1 (by rfl) ⟨1657190, by rfl⟩ : syracuseStep 2209587 = 3314381) B3314381
theorem B4971581 : Blo 2209435 4971581 := bbase (se 3 (by rfl) ⟨932171, by rfl⟩ : syracuseStep 4971581 = 1864343) (by norm_num)
theorem B3314387 : Blo 2209435 3314387 := bstep (se 1 (by rfl) ⟨2485790, by rfl⟩ : syracuseStep 3314387 = 4971581) B4971581
theorem B2209591 : Blo 2209435 2209591 := bstep (se 1 (by rfl) ⟨1657193, by rfl⟩ : syracuseStep 2209591 = 3314387) B3314387
theorem B3728693 : Blo 2209435 3728693 := bbase (se 5 (by rfl) ⟨174782, by rfl⟩ : syracuseStep 3728693 = 349565) (by norm_num)
theorem B2485795 : Blo 2209435 2485795 := bstep (se 1 (by rfl) ⟨1864346, by rfl⟩ : syracuseStep 2485795 = 3728693) B3728693
theorem B3314393 : Blo 2209435 3314393 := bstep (se 2 (by rfl) ⟨1242897, by rfl⟩ : syracuseStep 3314393 = 2485795) B2485795
theorem B2209595 : Blo 2209435 2209595 := bstep (se 1 (by rfl) ⟨1657196, by rfl⟩ : syracuseStep 2209595 = 3314393) B3314393
theorem B6292181 : Blo 2209435 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B16779149 : Blo 2209435 16779149 := bstep (se 3 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 16779149 = 6292181) B6292181
theorem B11186099 : Blo 2209435 11186099 := bstep (se 1 (by rfl) ⟨8389574, by rfl⟩ : syracuseStep 11186099 = 16779149) B16779149
theorem B7457399 : Blo 2209435 7457399 := bstep (se 1 (by rfl) ⟨5593049, by rfl⟩ : syracuseStep 7457399 = 11186099) B11186099
theorem B4971599 : Blo 2209435 4971599 := bstep (se 1 (by rfl) ⟨3728699, by rfl⟩ : syracuseStep 4971599 = 7457399) B7457399
theorem B3314399 : Blo 2209435 3314399 := bstep (se 1 (by rfl) ⟨2485799, by rfl⟩ : syracuseStep 3314399 = 4971599) B4971599
theorem B2209599 : Blo 2209435 2209599 := bstep (se 1 (by rfl) ⟨1657199, by rfl⟩ : syracuseStep 2209599 = 3314399) B3314399
theorem B3314405 : Blo 2209435 3314405 := bbase (se 4 (by rfl) ⟨310725, by rfl⟩ : syracuseStep 3314405 = 621451) (by norm_num)
theorem B2209603 : Blo 2209435 2209603 := bstep (se 1 (by rfl) ⟨1657202, by rfl⟩ : syracuseStep 2209603 = 3314405) B3314405
theorem B2359577 : Blo 2209435 2359577 := bbase (se 2 (by rfl) ⟨884841, by rfl⟩ : syracuseStep 2359577 = 1769683) (by norm_num)
theorem B6292205 : Blo 2209435 6292205 := bstep (se 3 (by rfl) ⟨1179788, by rfl⟩ : syracuseStep 6292205 = 2359577) B2359577
theorem B4194803 : Blo 2209435 4194803 := bstep (se 1 (by rfl) ⟨3146102, by rfl⟩ : syracuseStep 4194803 = 6292205) B6292205
theorem B2796535 : Blo 2209435 2796535 := bstep (se 1 (by rfl) ⟨2097401, by rfl⟩ : syracuseStep 2796535 = 4194803) B4194803
theorem B3728713 : Blo 2209435 3728713 := bstep (se 2 (by rfl) ⟨1398267, by rfl⟩ : syracuseStep 3728713 = 2796535) B2796535
theorem B4971617 : Blo 2209435 4971617 := bstep (se 2 (by rfl) ⟨1864356, by rfl⟩ : syracuseStep 4971617 = 3728713) B3728713
theorem B3314411 : Blo 2209435 3314411 := bstep (se 1 (by rfl) ⟨2485808, by rfl⟩ : syracuseStep 3314411 = 4971617) B4971617
theorem B2209607 : Blo 2209435 2209607 := bstep (se 1 (by rfl) ⟨1657205, by rfl⟩ : syracuseStep 2209607 = 3314411) B3314411
theorem B2485813 : Blo 2209435 2485813 := bbase (se 5 (by rfl) ⟨116522, by rfl⟩ : syracuseStep 2485813 = 233045) (by norm_num)
theorem B3314417 : Blo 2209435 3314417 := bstep (se 2 (by rfl) ⟨1242906, by rfl⟩ : syracuseStep 3314417 = 2485813) B2485813
theorem B2209611 : Blo 2209435 2209611 := bstep (se 1 (by rfl) ⟨1657208, by rfl⟩ : syracuseStep 2209611 = 3314417) B3314417
theorem B2796545 : Blo 2209435 2796545 := bbase (se 2 (by rfl) ⟨1048704, by rfl⟩ : syracuseStep 2796545 = 2097409) (by norm_num)
theorem B7457453 : Blo 2209435 7457453 := bstep (se 3 (by rfl) ⟨1398272, by rfl⟩ : syracuseStep 7457453 = 2796545) B2796545
theorem B4971635 : Blo 2209435 4971635 := bstep (se 1 (by rfl) ⟨3728726, by rfl⟩ : syracuseStep 4971635 = 7457453) B7457453
theorem B3314423 : Blo 2209435 3314423 := bstep (se 1 (by rfl) ⟨2485817, by rfl⟩ : syracuseStep 3314423 = 4971635) B4971635
theorem B2209615 : Blo 2209435 2209615 := bstep (se 1 (by rfl) ⟨1657211, by rfl⟩ : syracuseStep 2209615 = 3314423) B3314423
theorem B3314429 : Blo 2209435 3314429 := bbase (se 3 (by rfl) ⟨621455, by rfl⟩ : syracuseStep 3314429 = 1242911) (by norm_num)
theorem B2209619 : Blo 2209435 2209619 := bstep (se 1 (by rfl) ⟨1657214, by rfl⟩ : syracuseStep 2209619 = 3314429) B3314429
theorem B4971653 : Blo 2209435 4971653 := bbase (se 4 (by rfl) ⟨466092, by rfl⟩ : syracuseStep 4971653 = 932185) (by norm_num)
theorem B3314435 : Blo 2209435 3314435 := bstep (se 1 (by rfl) ⟨2485826, by rfl⟩ : syracuseStep 3314435 = 4971653) B4971653
theorem B2209623 : Blo 2209435 2209623 := bstep (se 1 (by rfl) ⟨1657217, by rfl⟩ : syracuseStep 2209623 = 3314435) B3314435
theorem B4719197 : Blo 2209435 4719197 := bbase (se 3 (by rfl) ⟨884849, by rfl⟩ : syracuseStep 4719197 = 1769699) (by norm_num)
theorem B3146131 : Blo 2209435 3146131 := bstep (se 1 (by rfl) ⟨2359598, by rfl⟩ : syracuseStep 3146131 = 4719197) B4719197
theorem B4194841 : Blo 2209435 4194841 := bstep (se 2 (by rfl) ⟨1573065, by rfl⟩ : syracuseStep 4194841 = 3146131) B3146131
theorem B5593121 : Blo 2209435 5593121 := bstep (se 2 (by rfl) ⟨2097420, by rfl⟩ : syracuseStep 5593121 = 4194841) B4194841
theorem B3728747 : Blo 2209435 3728747 := bstep (se 1 (by rfl) ⟨2796560, by rfl⟩ : syracuseStep 3728747 = 5593121) B5593121
theorem B2485831 : Blo 2209435 2485831 := bstep (se 1 (by rfl) ⟨1864373, by rfl⟩ : syracuseStep 2485831 = 3728747) B3728747
theorem B3314441 : Blo 2209435 3314441 := bstep (se 2 (by rfl) ⟨1242915, by rfl⟩ : syracuseStep 3314441 = 2485831) B2485831
theorem B2209627 : Blo 2209435 2209627 := bstep (se 1 (by rfl) ⟨1657220, by rfl⟩ : syracuseStep 2209627 = 3314441) B3314441
theorem B11186261 : Blo 2209435 11186261 := bbase (se 8 (by rfl) ⟨65544, by rfl⟩ : syracuseStep 11186261 = 131089) (by norm_num)
theorem B7457507 : Blo 2209435 7457507 := bstep (se 1 (by rfl) ⟨5593130, by rfl⟩ : syracuseStep 7457507 = 11186261) B11186261
theorem B4971671 : Blo 2209435 4971671 := bstep (se 1 (by rfl) ⟨3728753, by rfl⟩ : syracuseStep 4971671 = 7457507) B7457507
theorem B3314447 : Blo 2209435 3314447 := bstep (se 1 (by rfl) ⟨2485835, by rfl⟩ : syracuseStep 3314447 = 4971671) B4971671
theorem B2209631 : Blo 2209435 2209631 := bstep (se 1 (by rfl) ⟨1657223, by rfl⟩ : syracuseStep 2209631 = 3314447) B3314447
theorem B3314453 : Blo 2209435 3314453 := bbase (se 6 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 3314453 = 155365) (by norm_num)
theorem B2209635 : Blo 2209435 2209635 := bstep (se 1 (by rfl) ⟨1657226, by rfl⟩ : syracuseStep 2209635 = 3314453) B3314453
theorem B2391805 : Blo 2209435 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B3189073 : Blo 2209435 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B4252097 : Blo 2209435 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B2834731 : Blo 2209435 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B3779641 : Blo 2209435 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B20158085 : Blo 2209435 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B13438723 : Blo 2209435 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B17918297 : Blo 2209435 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B11945531 : Blo 2209435 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B7963687 : Blo 2209435 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B42472997 : Blo 2209435 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B28315331 : Blo 2209435 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B18876887 : Blo 2209435 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B12584591 : Blo 2209435 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B8389727 : Blo 2209435 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B5593151 : Blo 2209435 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B3728767 : Blo 2209435 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B4971689 : Blo 2209435 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B3314459 : Blo 2209435 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B2209639 : Blo 2209435 2209639 := bstep (se 1 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 2209639 = 3314459) B3314459
theorem B2485849 : Blo 2209435 2485849 := bbase (se 2 (by rfl) ⟨932193, by rfl⟩ : syracuseStep 2485849 = 1864387) (by norm_num)
theorem B3314465 : Blo 2209435 3314465 := bstep (se 2 (by rfl) ⟨1242924, by rfl⟩ : syracuseStep 3314465 = 2485849) B2485849
theorem B2209643 : Blo 2209435 2209643 := bstep (se 1 (by rfl) ⟨1657232, by rfl⟩ : syracuseStep 2209643 = 3314465) B3314465
theorem B7963717 : Blo 2209435 7963717 := bbase (se 4 (by rfl) ⟨746598, by rfl⟩ : syracuseStep 7963717 = 1493197) (by norm_num)
theorem B10618289 : Blo 2209435 10618289 := bstep (se 2 (by rfl) ⟨3981858, by rfl⟩ : syracuseStep 10618289 = 7963717) B7963717
theorem B7078859 : Blo 2209435 7078859 := bstep (se 1 (by rfl) ⟨5309144, by rfl⟩ : syracuseStep 7078859 = 10618289) B10618289
theorem B4719239 : Blo 2209435 4719239 := bstep (se 1 (by rfl) ⟨3539429, by rfl⟩ : syracuseStep 4719239 = 7078859) B7078859
theorem B3146159 : Blo 2209435 3146159 := bstep (se 1 (by rfl) ⟨2359619, by rfl⟩ : syracuseStep 3146159 = 4719239) B4719239
theorem B8389757 : Blo 2209435 8389757 := bstep (se 3 (by rfl) ⟨1573079, by rfl⟩ : syracuseStep 8389757 = 3146159) B3146159
theorem B5593171 : Blo 2209435 5593171 := bstep (se 1 (by rfl) ⟨4194878, by rfl⟩ : syracuseStep 5593171 = 8389757) B8389757
theorem B7457561 : Blo 2209435 7457561 := bstep (se 2 (by rfl) ⟨2796585, by rfl⟩ : syracuseStep 7457561 = 5593171) B5593171
theorem B4971707 : Blo 2209435 4971707 := bstep (se 1 (by rfl) ⟨3728780, by rfl⟩ : syracuseStep 4971707 = 7457561) B7457561
theorem B3314471 : Blo 2209435 3314471 := bstep (se 1 (by rfl) ⟨2485853, by rfl⟩ : syracuseStep 3314471 = 4971707) B4971707
theorem B2209647 : Blo 2209435 2209647 := bstep (se 1 (by rfl) ⟨1657235, by rfl⟩ : syracuseStep 2209647 = 3314471) B3314471
theorem B3314477 : Blo 2209435 3314477 := bbase (se 3 (by rfl) ⟨621464, by rfl⟩ : syracuseStep 3314477 = 1242929) (by norm_num)
theorem B2209651 : Blo 2209435 2209651 := bstep (se 1 (by rfl) ⟨1657238, by rfl⟩ : syracuseStep 2209651 = 3314477) B3314477
theorem B4971725 : Blo 2209435 4971725 := bbase (se 3 (by rfl) ⟨932198, by rfl⟩ : syracuseStep 4971725 = 1864397) (by norm_num)
theorem B3314483 : Blo 2209435 3314483 := bstep (se 1 (by rfl) ⟨2485862, by rfl⟩ : syracuseStep 3314483 = 4971725) B4971725
theorem B2209655 : Blo 2209435 2209655 := bstep (se 1 (by rfl) ⟨1657241, by rfl⟩ : syracuseStep 2209655 = 3314483) B3314483
theorem B2796601 : Blo 2209435 2796601 := bbase (se 2 (by rfl) ⟨1048725, by rfl⟩ : syracuseStep 2796601 = 2097451) (by norm_num)
theorem B3728801 : Blo 2209435 3728801 := bstep (se 2 (by rfl) ⟨1398300, by rfl⟩ : syracuseStep 3728801 = 2796601) B2796601
theorem B2485867 : Blo 2209435 2485867 := bstep (se 1 (by rfl) ⟨1864400, by rfl⟩ : syracuseStep 2485867 = 3728801) B3728801
theorem B3314489 : Blo 2209435 3314489 := bstep (se 2 (by rfl) ⟨1242933, by rfl⟩ : syracuseStep 3314489 = 2485867) B2485867
theorem B2209659 : Blo 2209435 2209659 := bstep (se 1 (by rfl) ⟨1657244, by rfl⟩ : syracuseStep 2209659 = 3314489) B3314489
theorem B30237461 : Blo 2209435 30237461 := bbase (se 6 (by rfl) ⟨708690, by rfl⟩ : syracuseStep 30237461 = 1417381) (by norm_num)
theorem B20158307 : Blo 2209435 20158307 := bstep (se 1 (by rfl) ⟨15118730, by rfl⟩ : syracuseStep 20158307 = 30237461) B30237461
theorem B13438871 : Blo 2209435 13438871 := bstep (se 1 (by rfl) ⟨10079153, by rfl⟩ : syracuseStep 13438871 = 20158307) B20158307
theorem B8959247 : Blo 2209435 8959247 := bstep (se 1 (by rfl) ⟨6719435, by rfl⟩ : syracuseStep 8959247 = 13438871) B13438871
theorem B5972831 : Blo 2209435 5972831 := bstep (se 1 (by rfl) ⟨4479623, by rfl⟩ : syracuseStep 5972831 = 8959247) B8959247
theorem B3981887 : Blo 2209435 3981887 := bstep (se 1 (by rfl) ⟨2986415, by rfl⟩ : syracuseStep 3981887 = 5972831) B5972831
theorem B2654591 : Blo 2209435 2654591 := bstep (se 1 (by rfl) ⟨1990943, by rfl⟩ : syracuseStep 2654591 = 3981887) B3981887
theorem B7078909 : Blo 2209435 7078909 := bstep (se 3 (by rfl) ⟨1327295, by rfl⟩ : syracuseStep 7078909 = 2654591) B2654591
theorem B9438545 : Blo 2209435 9438545 := bstep (se 2 (by rfl) ⟨3539454, by rfl⟩ : syracuseStep 9438545 = 7078909) B7078909
theorem B25169453 : Blo 2209435 25169453 := bstep (se 3 (by rfl) ⟨4719272, by rfl⟩ : syracuseStep 25169453 = 9438545) B9438545
theorem B16779635 : Blo 2209435 16779635 := bstep (se 1 (by rfl) ⟨12584726, by rfl⟩ : syracuseStep 16779635 = 25169453) B25169453
theorem B11186423 : Blo 2209435 11186423 := bstep (se 1 (by rfl) ⟨8389817, by rfl⟩ : syracuseStep 11186423 = 16779635) B16779635
theorem B7457615 : Blo 2209435 7457615 := bstep (se 1 (by rfl) ⟨5593211, by rfl⟩ : syracuseStep 7457615 = 11186423) B11186423
theorem B4971743 : Blo 2209435 4971743 := bstep (se 1 (by rfl) ⟨3728807, by rfl⟩ : syracuseStep 4971743 = 7457615) B7457615
theorem B3314495 : Blo 2209435 3314495 := bstep (se 1 (by rfl) ⟨2485871, by rfl⟩ : syracuseStep 3314495 = 4971743) B4971743
theorem B2209663 : Blo 2209435 2209663 := bstep (se 1 (by rfl) ⟨1657247, by rfl⟩ : syracuseStep 2209663 = 3314495) B3314495
theorem B3314501 : Blo 2209435 3314501 := bbase (se 4 (by rfl) ⟨310734, by rfl⟩ : syracuseStep 3314501 = 621469) (by norm_num)
theorem B2209667 : Blo 2209435 2209667 := bstep (se 1 (by rfl) ⟨1657250, by rfl⟩ : syracuseStep 2209667 = 3314501) B3314501
theorem B3728821 : Blo 2209435 3728821 := bbase (se 5 (by rfl) ⟨174788, by rfl⟩ : syracuseStep 3728821 = 349577) (by norm_num)
theorem B4971761 : Blo 2209435 4971761 := bstep (se 2 (by rfl) ⟨1864410, by rfl⟩ : syracuseStep 4971761 = 3728821) B3728821
theorem B3314507 : Blo 2209435 3314507 := bstep (se 1 (by rfl) ⟨2485880, by rfl⟩ : syracuseStep 3314507 = 4971761) B4971761
theorem B2209671 : Blo 2209435 2209671 := bstep (se 1 (by rfl) ⟨1657253, by rfl⟩ : syracuseStep 2209671 = 3314507) B3314507
theorem B2485885 : Blo 2209435 2485885 := bbase (se 3 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 2485885 = 932207) (by norm_num)
theorem B3314513 : Blo 2209435 3314513 := bstep (se 2 (by rfl) ⟨1242942, by rfl⟩ : syracuseStep 3314513 = 2485885) B2485885
theorem B2209675 : Blo 2209435 2209675 := bstep (se 1 (by rfl) ⟨1657256, by rfl⟩ : syracuseStep 2209675 = 3314513) B3314513
theorem B7457669 : Blo 2209435 7457669 := bbase (se 4 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 7457669 = 1398313) (by norm_num)
theorem B4971779 : Blo 2209435 4971779 := bstep (se 1 (by rfl) ⟨3728834, by rfl⟩ : syracuseStep 4971779 = 7457669) B7457669
theorem B3314519 : Blo 2209435 3314519 := bstep (se 1 (by rfl) ⟨2485889, by rfl⟩ : syracuseStep 3314519 = 4971779) B4971779
theorem B2209679 : Blo 2209435 2209679 := bstep (se 1 (by rfl) ⟨1657259, by rfl⟩ : syracuseStep 2209679 = 3314519) B3314519
theorem B3314525 : Blo 2209435 3314525 := bbase (se 3 (by rfl) ⟨621473, by rfl⟩ : syracuseStep 3314525 = 1242947) (by norm_num)
theorem B2209683 : Blo 2209435 2209683 := bstep (se 1 (by rfl) ⟨1657262, by rfl⟩ : syracuseStep 2209683 = 3314525) B3314525
theorem B4971797 : Blo 2209435 4971797 := bbase (se 6 (by rfl) ⟨116526, by rfl⟩ : syracuseStep 4971797 = 233053) (by norm_num)
theorem B3314531 : Blo 2209435 3314531 := bstep (se 1 (by rfl) ⟨2485898, by rfl⟩ : syracuseStep 3314531 = 4971797) B4971797
theorem B2209687 : Blo 2209435 2209687 := bstep (se 1 (by rfl) ⟨1657265, by rfl⟩ : syracuseStep 2209687 = 3314531) B3314531
theorem B8389925 : Blo 2209435 8389925 := bbase (se 4 (by rfl) ⟨786555, by rfl⟩ : syracuseStep 8389925 = 1573111) (by norm_num)
theorem B5593283 : Blo 2209435 5593283 := bstep (se 1 (by rfl) ⟨4194962, by rfl⟩ : syracuseStep 5593283 = 8389925) B8389925
theorem B3728855 : Blo 2209435 3728855 := bstep (se 1 (by rfl) ⟨2796641, by rfl⟩ : syracuseStep 3728855 = 5593283) B5593283
theorem B2485903 : Blo 2209435 2485903 := bstep (se 1 (by rfl) ⟨1864427, by rfl⟩ : syracuseStep 2485903 = 3728855) B3728855
theorem B3314537 : Blo 2209435 3314537 := bstep (se 2 (by rfl) ⟨1242951, by rfl⟩ : syracuseStep 3314537 = 2485903) B2485903
theorem B2209691 : Blo 2209435 2209691 := bstep (se 1 (by rfl) ⟨1657268, by rfl⟩ : syracuseStep 2209691 = 3314537) B3314537
theorem B4719341 : Blo 2209435 4719341 := bbase (se 3 (by rfl) ⟨884876, by rfl⟩ : syracuseStep 4719341 = 1769753) (by norm_num)
theorem B12584909 : Blo 2209435 12584909 := bstep (se 3 (by rfl) ⟨2359670, by rfl⟩ : syracuseStep 12584909 = 4719341) B4719341
theorem B8389939 : Blo 2209435 8389939 := bstep (se 1 (by rfl) ⟨6292454, by rfl⟩ : syracuseStep 8389939 = 12584909) B12584909
theorem B11186585 : Blo 2209435 11186585 := bstep (se 2 (by rfl) ⟨4194969, by rfl⟩ : syracuseStep 11186585 = 8389939) B8389939
theorem B7457723 : Blo 2209435 7457723 := bstep (se 1 (by rfl) ⟨5593292, by rfl⟩ : syracuseStep 7457723 = 11186585) B11186585
theorem B4971815 : Blo 2209435 4971815 := bstep (se 1 (by rfl) ⟨3728861, by rfl⟩ : syracuseStep 4971815 = 7457723) B7457723
theorem B3314543 : Blo 2209435 3314543 := bstep (se 1 (by rfl) ⟨2485907, by rfl⟩ : syracuseStep 3314543 = 4971815) B4971815
theorem B2209695 : Blo 2209435 2209695 := bstep (se 1 (by rfl) ⟨1657271, by rfl⟩ : syracuseStep 2209695 = 3314543) B3314543
theorem B3314549 : Blo 2209435 3314549 := bbase (se 5 (by rfl) ⟨155369, by rfl⟩ : syracuseStep 3314549 = 310739) (by norm_num)
theorem B2209699 : Blo 2209435 2209699 := bstep (se 1 (by rfl) ⟨1657274, by rfl⟩ : syracuseStep 2209699 = 3314549) B3314549
theorem B45357013 : Blo 2209435 45357013 := bbase (se 7 (by rfl) ⟨531527, by rfl⟩ : syracuseStep 45357013 = 1063055) (by norm_num)
theorem B60476017 : Blo 2209435 60476017 := bstep (se 2 (by rfl) ⟨22678506, by rfl⟩ : syracuseStep 60476017 = 45357013) B45357013
theorem B80634689 : Blo 2209435 80634689 := bstep (se 2 (by rfl) ⟨30238008, by rfl⟩ : syracuseStep 80634689 = 60476017) B60476017
theorem B53756459 : Blo 2209435 53756459 := bstep (se 1 (by rfl) ⟨40317344, by rfl⟩ : syracuseStep 53756459 = 80634689) B80634689
theorem B35837639 : Blo 2209435 35837639 := bstep (se 1 (by rfl) ⟨26878229, by rfl⟩ : syracuseStep 35837639 = 53756459) B53756459
theorem B23891759 : Blo 2209435 23891759 := bstep (se 1 (by rfl) ⟨17918819, by rfl⟩ : syracuseStep 23891759 = 35837639) B35837639
theorem B15927839 : Blo 2209435 15927839 := bstep (se 1 (by rfl) ⟨11945879, by rfl⟩ : syracuseStep 15927839 = 23891759) B23891759
theorem B10618559 : Blo 2209435 10618559 := bstep (se 1 (by rfl) ⟨7963919, by rfl⟩ : syracuseStep 10618559 = 15927839) B15927839
theorem B7079039 : Blo 2209435 7079039 := bstep (se 1 (by rfl) ⟨5309279, by rfl⟩ : syracuseStep 7079039 = 10618559) B10618559
theorem B4719359 : Blo 2209435 4719359 := bstep (se 1 (by rfl) ⟨3539519, by rfl⟩ : syracuseStep 4719359 = 7079039) B7079039
theorem B3146239 : Blo 2209435 3146239 := bstep (se 1 (by rfl) ⟨2359679, by rfl⟩ : syracuseStep 3146239 = 4719359) B4719359
theorem B4194985 : Blo 2209435 4194985 := bstep (se 2 (by rfl) ⟨1573119, by rfl⟩ : syracuseStep 4194985 = 3146239) B3146239
theorem B5593313 : Blo 2209435 5593313 := bstep (se 2 (by rfl) ⟨2097492, by rfl⟩ : syracuseStep 5593313 = 4194985) B4194985
theorem B3728875 : Blo 2209435 3728875 := bstep (se 1 (by rfl) ⟨2796656, by rfl⟩ : syracuseStep 3728875 = 5593313) B5593313
theorem B4971833 : Blo 2209435 4971833 := bstep (se 2 (by rfl) ⟨1864437, by rfl⟩ : syracuseStep 4971833 = 3728875) B3728875
theorem B3314555 : Blo 2209435 3314555 := bstep (se 1 (by rfl) ⟨2485916, by rfl⟩ : syracuseStep 3314555 = 4971833) B4971833
theorem B2209703 : Blo 2209435 2209703 := bstep (se 1 (by rfl) ⟨1657277, by rfl⟩ : syracuseStep 2209703 = 3314555) B3314555
theorem B2485921 : Blo 2209435 2485921 := bbase (se 2 (by rfl) ⟨932220, by rfl⟩ : syracuseStep 2485921 = 1864441) (by norm_num)
theorem B3314561 : Blo 2209435 3314561 := bstep (se 2 (by rfl) ⟨1242960, by rfl⟩ : syracuseStep 3314561 = 2485921) B2485921
theorem B2209707 : Blo 2209435 2209707 := bstep (se 1 (by rfl) ⟨1657280, by rfl⟩ : syracuseStep 2209707 = 3314561) B3314561
theorem B5593333 : Blo 2209435 5593333 := bbase (se 5 (by rfl) ⟨262187, by rfl⟩ : syracuseStep 5593333 = 524375) (by norm_num)
theorem B7457777 : Blo 2209435 7457777 := bstep (se 2 (by rfl) ⟨2796666, by rfl⟩ : syracuseStep 7457777 = 5593333) B5593333
theorem B4971851 : Blo 2209435 4971851 := bstep (se 1 (by rfl) ⟨3728888, by rfl⟩ : syracuseStep 4971851 = 7457777) B7457777
theorem B3314567 : Blo 2209435 3314567 := bstep (se 1 (by rfl) ⟨2485925, by rfl⟩ : syracuseStep 3314567 = 4971851) B4971851
theorem B2209711 : Blo 2209435 2209711 := bstep (se 1 (by rfl) ⟨1657283, by rfl⟩ : syracuseStep 2209711 = 3314567) B3314567
theorem B3314573 : Blo 2209435 3314573 := bbase (se 3 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 3314573 = 1242965) (by norm_num)
theorem B2209715 : Blo 2209435 2209715 := bstep (se 1 (by rfl) ⟨1657286, by rfl⟩ : syracuseStep 2209715 = 3314573) B3314573
theorem B4971869 : Blo 2209435 4971869 := bbase (se 3 (by rfl) ⟨932225, by rfl⟩ : syracuseStep 4971869 = 1864451) (by norm_num)
theorem B3314579 : Blo 2209435 3314579 := bstep (se 1 (by rfl) ⟨2485934, by rfl⟩ : syracuseStep 3314579 = 4971869) B4971869
theorem B2209719 : Blo 2209435 2209719 := bstep (se 1 (by rfl) ⟨1657289, by rfl⟩ : syracuseStep 2209719 = 3314579) B3314579
theorem B3728909 : Blo 2209435 3728909 := bbase (se 3 (by rfl) ⟨699170, by rfl⟩ : syracuseStep 3728909 = 1398341) (by norm_num)
theorem B2485939 : Blo 2209435 2485939 := bstep (se 1 (by rfl) ⟨1864454, by rfl⟩ : syracuseStep 2485939 = 3728909) B3728909
theorem B3314585 : Blo 2209435 3314585 := bstep (se 2 (by rfl) ⟨1242969, by rfl⟩ : syracuseStep 3314585 = 2485939) B2485939
theorem B2209723 : Blo 2209435 2209723 := bstep (se 1 (by rfl) ⟨1657292, by rfl⟩ : syracuseStep 2209723 = 3314585) B3314585
theorem B3539557 : Blo 2209435 3539557 := bbase (se 4 (by rfl) ⟨331833, by rfl⟩ : syracuseStep 3539557 = 663667) (by norm_num)
theorem B18877637 : Blo 2209435 18877637 := bstep (se 4 (by rfl) ⟨1769778, by rfl⟩ : syracuseStep 18877637 = 3539557) B3539557
theorem B12585091 : Blo 2209435 12585091 := bstep (se 1 (by rfl) ⟨9438818, by rfl⟩ : syracuseStep 12585091 = 18877637) B18877637
theorem B16780121 : Blo 2209435 16780121 := bstep (se 2 (by rfl) ⟨6292545, by rfl⟩ : syracuseStep 16780121 = 12585091) B12585091
theorem B11186747 : Blo 2209435 11186747 := bstep (se 1 (by rfl) ⟨8390060, by rfl⟩ : syracuseStep 11186747 = 16780121) B16780121
theorem B7457831 : Blo 2209435 7457831 := bstep (se 1 (by rfl) ⟨5593373, by rfl⟩ : syracuseStep 7457831 = 11186747) B11186747
theorem B4971887 : Blo 2209435 4971887 := bstep (se 1 (by rfl) ⟨3728915, by rfl⟩ : syracuseStep 4971887 = 7457831) B7457831
theorem B3314591 : Blo 2209435 3314591 := bstep (se 1 (by rfl) ⟨2485943, by rfl⟩ : syracuseStep 3314591 = 4971887) B4971887
theorem B2209727 : Blo 2209435 2209727 := bstep (se 1 (by rfl) ⟨1657295, by rfl⟩ : syracuseStep 2209727 = 3314591) B3314591
theorem B3314597 : Blo 2209435 3314597 := bbase (se 4 (by rfl) ⟨310743, by rfl⟩ : syracuseStep 3314597 = 621487) (by norm_num)
theorem B2209731 : Blo 2209435 2209731 := bstep (se 1 (by rfl) ⟨1657298, by rfl⟩ : syracuseStep 2209731 = 3314597) B3314597
theorem B2796697 : Blo 2209435 2796697 := bbase (se 2 (by rfl) ⟨1048761, by rfl⟩ : syracuseStep 2796697 = 2097523) (by norm_num)
theorem B3728929 : Blo 2209435 3728929 := bstep (se 2 (by rfl) ⟨1398348, by rfl⟩ : syracuseStep 3728929 = 2796697) B2796697
theorem B4971905 : Blo 2209435 4971905 := bstep (se 2 (by rfl) ⟨1864464, by rfl⟩ : syracuseStep 4971905 = 3728929) B3728929
theorem B3314603 : Blo 2209435 3314603 := bstep (se 1 (by rfl) ⟨2485952, by rfl⟩ : syracuseStep 3314603 = 4971905) B4971905
theorem B2209735 : Blo 2209435 2209735 := bstep (se 1 (by rfl) ⟨1657301, by rfl⟩ : syracuseStep 2209735 = 3314603) B3314603
theorem B2485957 : Blo 2209435 2485957 := bbase (se 4 (by rfl) ⟨233058, by rfl⟩ : syracuseStep 2485957 = 466117) (by norm_num)
theorem B3314609 : Blo 2209435 3314609 := bstep (se 2 (by rfl) ⟨1242978, by rfl⟩ : syracuseStep 3314609 = 2485957) B2485957
theorem B2209739 : Blo 2209435 2209739 := bstep (se 1 (by rfl) ⟨1657304, by rfl⟩ : syracuseStep 2209739 = 3314609) B3314609
theorem B4195061 : Blo 2209435 4195061 := bbase (se 5 (by rfl) ⟨196643, by rfl⟩ : syracuseStep 4195061 = 393287) (by norm_num)
theorem B2796707 : Blo 2209435 2796707 := bstep (se 1 (by rfl) ⟨2097530, by rfl⟩ : syracuseStep 2796707 = 4195061) B4195061
theorem B7457885 : Blo 2209435 7457885 := bstep (se 3 (by rfl) ⟨1398353, by rfl⟩ : syracuseStep 7457885 = 2796707) B2796707
theorem B4971923 : Blo 2209435 4971923 := bstep (se 1 (by rfl) ⟨3728942, by rfl⟩ : syracuseStep 4971923 = 7457885) B7457885
theorem B3314615 : Blo 2209435 3314615 := bstep (se 1 (by rfl) ⟨2485961, by rfl⟩ : syracuseStep 3314615 = 4971923) B4971923
theorem B2209743 : Blo 2209435 2209743 := bstep (se 1 (by rfl) ⟨1657307, by rfl⟩ : syracuseStep 2209743 = 3314615) B3314615
theorem B3314621 : Blo 2209435 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B2209747 : Blo 2209435 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B4971941 : Blo 2209435 4971941 := bbase (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) (by norm_num)
theorem B3314627 : Blo 2209435 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B2209751 : Blo 2209435 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B5593445 : Blo 2209435 5593445 := bbase (se 4 (by rfl) ⟨524385, by rfl⟩ : syracuseStep 5593445 = 1048771) (by norm_num)
theorem B3728963 : Blo 2209435 3728963 := bstep (se 1 (by rfl) ⟨2796722, by rfl⟩ : syracuseStep 3728963 = 5593445) B5593445
theorem B2485975 : Blo 2209435 2485975 := bstep (se 1 (by rfl) ⟨1864481, by rfl⟩ : syracuseStep 2485975 = 3728963) B3728963
theorem B3314633 : Blo 2209435 3314633 := bstep (se 2 (by rfl) ⟨1242987, by rfl⟩ : syracuseStep 3314633 = 2485975) B2485975
theorem B2209755 : Blo 2209435 2209755 := bstep (se 1 (by rfl) ⟨1657316, by rfl⟩ : syracuseStep 2209755 = 3314633) B3314633
theorem B3982061 : Blo 2209435 3982061 := bbase (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) (by norm_num)
theorem B2654707 : Blo 2209435 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B3539609 : Blo 2209435 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B2359739 : Blo 2209435 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B6292637 : Blo 2209435 6292637 := bstep (se 3 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 6292637 = 2359739) B2359739
theorem B4195091 : Blo 2209435 4195091 := bstep (se 1 (by rfl) ⟨3146318, by rfl⟩ : syracuseStep 4195091 = 6292637) B6292637
theorem B11186909 : Blo 2209435 11186909 := bstep (se 3 (by rfl) ⟨2097545, by rfl⟩ : syracuseStep 11186909 = 4195091) B4195091
theorem B7457939 : Blo 2209435 7457939 := bstep (se 1 (by rfl) ⟨5593454, by rfl⟩ : syracuseStep 7457939 = 11186909) B11186909
theorem B4971959 : Blo 2209435 4971959 := bstep (se 1 (by rfl) ⟨3728969, by rfl⟩ : syracuseStep 4971959 = 7457939) B7457939
theorem B3314639 : Blo 2209435 3314639 := bstep (se 1 (by rfl) ⟨2485979, by rfl⟩ : syracuseStep 3314639 = 4971959) B4971959
theorem B2209759 : Blo 2209435 2209759 := bstep (se 1 (by rfl) ⟨1657319, by rfl⟩ : syracuseStep 2209759 = 3314639) B3314639
theorem B3314645 : Blo 2209435 3314645 := bbase (se 7 (by rfl) ⟨38843, by rfl⟩ : syracuseStep 3314645 = 77687) (by norm_num)
theorem B2209763 : Blo 2209435 2209763 := bstep (se 1 (by rfl) ⟨1657322, by rfl⟩ : syracuseStep 2209763 = 3314645) B3314645
theorem B8390213 : Blo 2209435 8390213 := bbase (se 4 (by rfl) ⟨786582, by rfl⟩ : syracuseStep 8390213 = 1573165) (by norm_num)
theorem B5593475 : Blo 2209435 5593475 := bstep (se 1 (by rfl) ⟨4195106, by rfl⟩ : syracuseStep 5593475 = 8390213) B8390213
theorem B3728983 : Blo 2209435 3728983 := bstep (se 1 (by rfl) ⟨2796737, by rfl⟩ : syracuseStep 3728983 = 5593475) B5593475
theorem B4971977 : Blo 2209435 4971977 := bstep (se 2 (by rfl) ⟨1864491, by rfl⟩ : syracuseStep 4971977 = 3728983) B3728983
theorem B3314651 : Blo 2209435 3314651 := bstep (se 1 (by rfl) ⟨2485988, by rfl⟩ : syracuseStep 3314651 = 4971977) B4971977
theorem B2209767 : Blo 2209435 2209767 := bstep (se 1 (by rfl) ⟨1657325, by rfl⟩ : syracuseStep 2209767 = 3314651) B3314651
theorem B2485993 : Blo 2209435 2485993 := bbase (se 2 (by rfl) ⟨932247, by rfl⟩ : syracuseStep 2485993 = 1864495) (by norm_num)
theorem B3314657 : Blo 2209435 3314657 := bstep (se 2 (by rfl) ⟨1242996, by rfl⟩ : syracuseStep 3314657 = 2485993) B2485993
theorem B2209771 : Blo 2209435 2209771 := bstep (se 1 (by rfl) ⟨1657328, by rfl⟩ : syracuseStep 2209771 = 3314657) B3314657
theorem B12585365 : Blo 2209435 12585365 := bbase (se 6 (by rfl) ⟨294969, by rfl⟩ : syracuseStep 12585365 = 589939) (by norm_num)
theorem B8390243 : Blo 2209435 8390243 := bstep (se 1 (by rfl) ⟨6292682, by rfl⟩ : syracuseStep 8390243 = 12585365) B12585365
theorem B5593495 : Blo 2209435 5593495 := bstep (se 1 (by rfl) ⟨4195121, by rfl⟩ : syracuseStep 5593495 = 8390243) B8390243
theorem B7457993 : Blo 2209435 7457993 := bstep (se 2 (by rfl) ⟨2796747, by rfl⟩ : syracuseStep 7457993 = 5593495) B5593495
theorem B4971995 : Blo 2209435 4971995 := bstep (se 1 (by rfl) ⟨3728996, by rfl⟩ : syracuseStep 4971995 = 7457993) B7457993
theorem B3314663 : Blo 2209435 3314663 := bstep (se 1 (by rfl) ⟨2485997, by rfl⟩ : syracuseStep 3314663 = 4971995) B4971995
theorem B2209775 : Blo 2209435 2209775 := bstep (se 1 (by rfl) ⟨1657331, by rfl⟩ : syracuseStep 2209775 = 3314663) B3314663
theorem B3314669 : Blo 2209435 3314669 := bbase (se 3 (by rfl) ⟨621500, by rfl⟩ : syracuseStep 3314669 = 1243001) (by norm_num)
theorem B2209779 : Blo 2209435 2209779 := bstep (se 1 (by rfl) ⟨1657334, by rfl⟩ : syracuseStep 2209779 = 3314669) B3314669
theorem B4972013 : Blo 2209435 4972013 := bbase (se 3 (by rfl) ⟨932252, by rfl⟩ : syracuseStep 4972013 = 1864505) (by norm_num)
theorem B3314675 : Blo 2209435 3314675 := bstep (se 1 (by rfl) ⟨2486006, by rfl⟩ : syracuseStep 3314675 = 4972013) B4972013
theorem B2209783 : Blo 2209435 2209783 := bstep (se 1 (by rfl) ⟨1657337, by rfl⟩ : syracuseStep 2209783 = 3314675) B3314675
theorem B2654741 : Blo 2209435 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B7079309 : Blo 2209435 7079309 := bstep (se 3 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 7079309 = 2654741) B2654741
theorem B4719539 : Blo 2209435 4719539 := bstep (se 1 (by rfl) ⟨3539654, by rfl⟩ : syracuseStep 4719539 = 7079309) B7079309
theorem B3146359 : Blo 2209435 3146359 := bstep (se 1 (by rfl) ⟨2359769, by rfl⟩ : syracuseStep 3146359 = 4719539) B4719539
theorem B4195145 : Blo 2209435 4195145 := bstep (se 2 (by rfl) ⟨1573179, by rfl⟩ : syracuseStep 4195145 = 3146359) B3146359
theorem B2796763 : Blo 2209435 2796763 := bstep (se 1 (by rfl) ⟨2097572, by rfl⟩ : syracuseStep 2796763 = 4195145) B4195145
theorem B3729017 : Blo 2209435 3729017 := bstep (se 2 (by rfl) ⟨1398381, by rfl⟩ : syracuseStep 3729017 = 2796763) B2796763
theorem B2486011 : Blo 2209435 2486011 := bstep (se 1 (by rfl) ⟨1864508, by rfl⟩ : syracuseStep 2486011 = 3729017) B3729017
theorem B3314681 : Blo 2209435 3314681 := bstep (se 2 (by rfl) ⟨1243005, by rfl⟩ : syracuseStep 3314681 = 2486011) B2486011
theorem B2209787 : Blo 2209435 2209787 := bstep (se 1 (by rfl) ⟨1657340, by rfl⟩ : syracuseStep 2209787 = 3314681) B3314681
theorem B5108629 : Blo 2209435 5108629 := bbase (se 6 (by rfl) ⟨119733, by rfl⟩ : syracuseStep 5108629 = 239467) (by norm_num)
theorem B6811505 : Blo 2209435 6811505 := bstep (se 2 (by rfl) ⟨2554314, by rfl⟩ : syracuseStep 6811505 = 5108629) B5108629
theorem B4541003 : Blo 2209435 4541003 := bstep (se 1 (by rfl) ⟨3405752, by rfl⟩ : syracuseStep 4541003 = 6811505) B6811505
theorem B3027335 : Blo 2209435 3027335 := bstep (se 1 (by rfl) ⟨2270501, by rfl⟩ : syracuseStep 3027335 = 4541003) B4541003
theorem B8072893 : Blo 2209435 8072893 := bstep (se 3 (by rfl) ⟨1513667, by rfl⟩ : syracuseStep 8072893 = 3027335) B3027335
theorem B10763857 : Blo 2209435 10763857 := bstep (se 2 (by rfl) ⟨4036446, by rfl⟩ : syracuseStep 10763857 = 8072893) B8072893
theorem B57407237 : Blo 2209435 57407237 := bstep (se 4 (by rfl) ⟨5381928, by rfl⟩ : syracuseStep 57407237 = 10763857) B10763857
theorem B38271491 : Blo 2209435 38271491 := bstep (se 1 (by rfl) ⟨28703618, by rfl⟩ : syracuseStep 38271491 = 57407237) B57407237
theorem B25514327 : Blo 2209435 25514327 := bstep (se 1 (by rfl) ⟨19135745, by rfl⟩ : syracuseStep 25514327 = 38271491) B38271491
theorem B17009551 : Blo 2209435 17009551 := bstep (se 1 (by rfl) ⟨12757163, by rfl⟩ : syracuseStep 17009551 = 25514327) B25514327
theorem B22679401 : Blo 2209435 22679401 := bstep (se 2 (by rfl) ⟨8504775, by rfl⟩ : syracuseStep 22679401 = 17009551) B17009551
theorem B30239201 : Blo 2209435 30239201 := bstep (se 2 (by rfl) ⟨11339700, by rfl⟩ : syracuseStep 30239201 = 22679401) B22679401
theorem B80637869 : Blo 2209435 80637869 := bstep (se 3 (by rfl) ⟨15119600, by rfl⟩ : syracuseStep 80637869 = 30239201) B30239201
theorem B53758579 : Blo 2209435 53758579 := bstep (se 1 (by rfl) ⟨40318934, by rfl⟩ : syracuseStep 53758579 = 80637869) B80637869
theorem B71678105 : Blo 2209435 71678105 := bstep (se 2 (by rfl) ⟨26879289, by rfl⟩ : syracuseStep 71678105 = 53758579) B53758579
theorem B47785403 : Blo 2209435 47785403 := bstep (se 1 (by rfl) ⟨35839052, by rfl⟩ : syracuseStep 47785403 = 71678105) B71678105
theorem B127427741 : Blo 2209435 127427741 := bstep (se 3 (by rfl) ⟨23892701, by rfl⟩ : syracuseStep 127427741 = 47785403) B47785403
theorem B84951827 : Blo 2209435 84951827 := bstep (se 1 (by rfl) ⟨63713870, by rfl⟩ : syracuseStep 84951827 = 127427741) B127427741
theorem B56634551 : Blo 2209435 56634551 := bstep (se 1 (by rfl) ⟨42475913, by rfl⟩ : syracuseStep 56634551 = 84951827) B84951827
theorem B37756367 : Blo 2209435 37756367 := bstep (se 1 (by rfl) ⟨28317275, by rfl⟩ : syracuseStep 37756367 = 56634551) B56634551
theorem B25170911 : Blo 2209435 25170911 := bstep (se 1 (by rfl) ⟨18878183, by rfl⟩ : syracuseStep 25170911 = 37756367) B37756367
theorem B16780607 : Blo 2209435 16780607 := bstep (se 1 (by rfl) ⟨12585455, by rfl⟩ : syracuseStep 16780607 = 25170911) B25170911
theorem B11187071 : Blo 2209435 11187071 := bstep (se 1 (by rfl) ⟨8390303, by rfl⟩ : syracuseStep 11187071 = 16780607) B16780607
theorem B7458047 : Blo 2209435 7458047 := bstep (se 1 (by rfl) ⟨5593535, by rfl⟩ : syracuseStep 7458047 = 11187071) B11187071
theorem B4972031 : Blo 2209435 4972031 := bstep (se 1 (by rfl) ⟨3729023, by rfl⟩ : syracuseStep 4972031 = 7458047) B7458047
theorem B3314687 : Blo 2209435 3314687 := bstep (se 1 (by rfl) ⟨2486015, by rfl⟩ : syracuseStep 3314687 = 4972031) B4972031
theorem B2209791 : Blo 2209435 2209791 := bstep (se 1 (by rfl) ⟨1657343, by rfl⟩ : syracuseStep 2209791 = 3314687) B3314687
theorem B3314693 : Blo 2209435 3314693 := bbase (se 4 (by rfl) ⟨310752, by rfl⟩ : syracuseStep 3314693 = 621505) (by norm_num)
theorem B2209795 : Blo 2209435 2209795 := bstep (se 1 (by rfl) ⟨1657346, by rfl⟩ : syracuseStep 2209795 = 3314693) B3314693
theorem B3729037 : Blo 2209435 3729037 := bbase (se 3 (by rfl) ⟨699194, by rfl⟩ : syracuseStep 3729037 = 1398389) (by norm_num)
theorem B4972049 : Blo 2209435 4972049 := bstep (se 2 (by rfl) ⟨1864518, by rfl⟩ : syracuseStep 4972049 = 3729037) B3729037
theorem B3314699 : Blo 2209435 3314699 := bstep (se 1 (by rfl) ⟨2486024, by rfl⟩ : syracuseStep 3314699 = 4972049) B4972049
theorem B2209799 : Blo 2209435 2209799 := bstep (se 1 (by rfl) ⟨1657349, by rfl⟩ : syracuseStep 2209799 = 3314699) B3314699
theorem B2486029 : Blo 2209435 2486029 := bbase (se 3 (by rfl) ⟨466130, by rfl⟩ : syracuseStep 2486029 = 932261) (by norm_num)
theorem B3314705 : Blo 2209435 3314705 := bstep (se 2 (by rfl) ⟨1243014, by rfl⟩ : syracuseStep 3314705 = 2486029) B2486029
theorem B2209803 : Blo 2209435 2209803 := bstep (se 1 (by rfl) ⟨1657352, by rfl⟩ : syracuseStep 2209803 = 3314705) B3314705
theorem B7458101 : Blo 2209435 7458101 := bbase (se 5 (by rfl) ⟨349598, by rfl⟩ : syracuseStep 7458101 = 699197) (by norm_num)
theorem B4972067 : Blo 2209435 4972067 := bstep (se 1 (by rfl) ⟨3729050, by rfl⟩ : syracuseStep 4972067 = 7458101) B7458101
theorem B3314711 : Blo 2209435 3314711 := bstep (se 1 (by rfl) ⟨2486033, by rfl⟩ : syracuseStep 3314711 = 4972067) B4972067
theorem B2209807 : Blo 2209435 2209807 := bstep (se 1 (by rfl) ⟨1657355, by rfl⟩ : syracuseStep 2209807 = 3314711) B3314711
theorem B3314717 : Blo 2209435 3314717 := bbase (se 3 (by rfl) ⟨621509, by rfl⟩ : syracuseStep 3314717 = 1243019) (by norm_num)
theorem B2209811 : Blo 2209435 2209811 := bstep (se 1 (by rfl) ⟨1657358, by rfl⟩ : syracuseStep 2209811 = 3314717) B3314717
theorem B4972085 : Blo 2209435 4972085 := bbase (se 5 (by rfl) ⟨233066, by rfl⟩ : syracuseStep 4972085 = 466133) (by norm_num)
theorem B3314723 : Blo 2209435 3314723 := bstep (se 1 (by rfl) ⟨2486042, by rfl⟩ : syracuseStep 3314723 = 4972085) B4972085
theorem B2209815 : Blo 2209435 2209815 := bstep (se 1 (by rfl) ⟨1657361, by rfl⟩ : syracuseStep 2209815 = 3314723) B3314723
theorem B4479941 : Blo 2209435 4479941 := bbase (se 4 (by rfl) ⟨419994, by rfl⟩ : syracuseStep 4479941 = 839989) (by norm_num)
theorem B2986627 : Blo 2209435 2986627 := bstep (se 1 (by rfl) ⟨2239970, by rfl⟩ : syracuseStep 2986627 = 4479941) B4479941
theorem B3982169 : Blo 2209435 3982169 := bstep (se 2 (by rfl) ⟨1493313, by rfl⟩ : syracuseStep 3982169 = 2986627) B2986627
theorem B2654779 : Blo 2209435 2654779 := bstep (se 1 (by rfl) ⟨1991084, by rfl⟩ : syracuseStep 2654779 = 3982169) B3982169
theorem B3539705 : Blo 2209435 3539705 := bstep (se 2 (by rfl) ⟨1327389, by rfl⟩ : syracuseStep 3539705 = 2654779) B2654779
theorem B9439213 : Blo 2209435 9439213 := bstep (se 3 (by rfl) ⟨1769852, by rfl⟩ : syracuseStep 9439213 = 3539705) B3539705
theorem B12585617 : Blo 2209435 12585617 := bstep (se 2 (by rfl) ⟨4719606, by rfl⟩ : syracuseStep 12585617 = 9439213) B9439213
theorem B8390411 : Blo 2209435 8390411 := bstep (se 1 (by rfl) ⟨6292808, by rfl⟩ : syracuseStep 8390411 = 12585617) B12585617
theorem B5593607 : Blo 2209435 5593607 := bstep (se 1 (by rfl) ⟨4195205, by rfl⟩ : syracuseStep 5593607 = 8390411) B8390411
theorem B3729071 : Blo 2209435 3729071 := bstep (se 1 (by rfl) ⟨2796803, by rfl⟩ : syracuseStep 3729071 = 5593607) B5593607
theorem B2486047 : Blo 2209435 2486047 := bstep (se 1 (by rfl) ⟨1864535, by rfl⟩ : syracuseStep 2486047 = 3729071) B3729071
theorem B3314729 : Blo 2209435 3314729 := bstep (se 2 (by rfl) ⟨1243023, by rfl⟩ : syracuseStep 3314729 = 2486047) B2486047
theorem B2209819 : Blo 2209435 2209819 := bstep (se 1 (by rfl) ⟨1657364, by rfl⟩ : syracuseStep 2209819 = 3314729) B3314729
theorem B34019605 : Blo 2209435 34019605 := bbase (se 6 (by rfl) ⟨797334, by rfl⟩ : syracuseStep 34019605 = 1594669) (by norm_num)
theorem B45359473 : Blo 2209435 45359473 := bstep (se 2 (by rfl) ⟨17009802, by rfl⟩ : syracuseStep 45359473 = 34019605) B34019605
theorem B60479297 : Blo 2209435 60479297 := bstep (se 2 (by rfl) ⟨22679736, by rfl⟩ : syracuseStep 60479297 = 45359473) B45359473
theorem B40319531 : Blo 2209435 40319531 := bstep (se 1 (by rfl) ⟨30239648, by rfl⟩ : syracuseStep 40319531 = 60479297) B60479297
theorem B26879687 : Blo 2209435 26879687 := bstep (se 1 (by rfl) ⟨20159765, by rfl⟩ : syracuseStep 26879687 = 40319531) B40319531
theorem B17919791 : Blo 2209435 17919791 := bstep (se 1 (by rfl) ⟨13439843, by rfl⟩ : syracuseStep 17919791 = 26879687) B26879687
theorem B11946527 : Blo 2209435 11946527 := bstep (se 1 (by rfl) ⟨8959895, by rfl⟩ : syracuseStep 11946527 = 17919791) B17919791
theorem B7964351 : Blo 2209435 7964351 := bstep (se 1 (by rfl) ⟨5973263, by rfl⟩ : syracuseStep 7964351 = 11946527) B11946527
theorem B5309567 : Blo 2209435 5309567 := bstep (se 1 (by rfl) ⟨3982175, by rfl⟩ : syracuseStep 5309567 = 7964351) B7964351
theorem B3539711 : Blo 2209435 3539711 := bstep (se 1 (by rfl) ⟨2654783, by rfl⟩ : syracuseStep 3539711 = 5309567) B5309567
theorem B9439229 : Blo 2209435 9439229 := bstep (se 3 (by rfl) ⟨1769855, by rfl⟩ : syracuseStep 9439229 = 3539711) B3539711
theorem B6292819 : Blo 2209435 6292819 := bstep (se 1 (by rfl) ⟨4719614, by rfl⟩ : syracuseStep 6292819 = 9439229) B9439229
theorem B8390425 : Blo 2209435 8390425 := bstep (se 2 (by rfl) ⟨3146409, by rfl⟩ : syracuseStep 8390425 = 6292819) B6292819
theorem B11187233 : Blo 2209435 11187233 := bstep (se 2 (by rfl) ⟨4195212, by rfl⟩ : syracuseStep 11187233 = 8390425) B8390425
theorem B7458155 : Blo 2209435 7458155 := bstep (se 1 (by rfl) ⟨5593616, by rfl⟩ : syracuseStep 7458155 = 11187233) B11187233
theorem B4972103 : Blo 2209435 4972103 := bstep (se 1 (by rfl) ⟨3729077, by rfl⟩ : syracuseStep 4972103 = 7458155) B7458155
theorem B3314735 : Blo 2209435 3314735 := bstep (se 1 (by rfl) ⟨2486051, by rfl⟩ : syracuseStep 3314735 = 4972103) B4972103
theorem B2209823 : Blo 2209435 2209823 := bstep (se 1 (by rfl) ⟨1657367, by rfl⟩ : syracuseStep 2209823 = 3314735) B3314735
theorem B3314741 : Blo 2209435 3314741 := bbase (se 5 (by rfl) ⟨155378, by rfl⟩ : syracuseStep 3314741 = 310757) (by norm_num)
theorem B2209827 : Blo 2209435 2209827 := bstep (se 1 (by rfl) ⟨1657370, by rfl⟩ : syracuseStep 2209827 = 3314741) B3314741
theorem B5593637 : Blo 2209435 5593637 := bbase (se 4 (by rfl) ⟨524403, by rfl⟩ : syracuseStep 5593637 = 1048807) (by norm_num)
theorem B3729091 : Blo 2209435 3729091 := bstep (se 1 (by rfl) ⟨2796818, by rfl⟩ : syracuseStep 3729091 = 5593637) B5593637
theorem B4972121 : Blo 2209435 4972121 := bstep (se 2 (by rfl) ⟨1864545, by rfl⟩ : syracuseStep 4972121 = 3729091) B3729091
theorem B3314747 : Blo 2209435 3314747 := bstep (se 1 (by rfl) ⟨2486060, by rfl⟩ : syracuseStep 3314747 = 4972121) B4972121
theorem B2209831 : Blo 2209435 2209831 := bstep (se 1 (by rfl) ⟨1657373, by rfl⟩ : syracuseStep 2209831 = 3314747) B3314747
theorem B2486065 : Blo 2209435 2486065 := bbase (se 2 (by rfl) ⟨932274, by rfl⟩ : syracuseStep 2486065 = 1864549) (by norm_num)
theorem B3314753 : Blo 2209435 3314753 := bstep (se 2 (by rfl) ⟨1243032, by rfl⟩ : syracuseStep 3314753 = 2486065) B2486065
theorem B2209835 : Blo 2209435 2209835 := bstep (se 1 (by rfl) ⟨1657376, by rfl⟩ : syracuseStep 2209835 = 3314753) B3314753
theorem B3982205 : Blo 2209435 3982205 := bbase (se 3 (by rfl) ⟨746663, by rfl⟩ : syracuseStep 3982205 = 1493327) (by norm_num)
theorem B2654803 : Blo 2209435 2654803 := bstep (se 1 (by rfl) ⟨1991102, by rfl⟩ : syracuseStep 2654803 = 3982205) B3982205
theorem B3539737 : Blo 2209435 3539737 := bstep (se 2 (by rfl) ⟨1327401, by rfl⟩ : syracuseStep 3539737 = 2654803) B2654803
theorem B4719649 : Blo 2209435 4719649 := bstep (se 2 (by rfl) ⟨1769868, by rfl⟩ : syracuseStep 4719649 = 3539737) B3539737
theorem B6292865 : Blo 2209435 6292865 := bstep (se 2 (by rfl) ⟨2359824, by rfl⟩ : syracuseStep 6292865 = 4719649) B4719649
theorem B4195243 : Blo 2209435 4195243 := bstep (se 1 (by rfl) ⟨3146432, by rfl⟩ : syracuseStep 4195243 = 6292865) B6292865
theorem B5593657 : Blo 2209435 5593657 := bstep (se 2 (by rfl) ⟨2097621, by rfl⟩ : syracuseStep 5593657 = 4195243) B4195243
theorem B7458209 : Blo 2209435 7458209 := bstep (se 2 (by rfl) ⟨2796828, by rfl⟩ : syracuseStep 7458209 = 5593657) B5593657
theorem B4972139 : Blo 2209435 4972139 := bstep (se 1 (by rfl) ⟨3729104, by rfl⟩ : syracuseStep 4972139 = 7458209) B7458209
theorem B3314759 : Blo 2209435 3314759 := bstep (se 1 (by rfl) ⟨2486069, by rfl⟩ : syracuseStep 3314759 = 4972139) B4972139
theorem B2209839 : Blo 2209435 2209839 := bstep (se 1 (by rfl) ⟨1657379, by rfl⟩ : syracuseStep 2209839 = 3314759) B3314759
theorem B3314765 : Blo 2209435 3314765 := bbase (se 3 (by rfl) ⟨621518, by rfl⟩ : syracuseStep 3314765 = 1243037) (by norm_num)
theorem B2209843 : Blo 2209435 2209843 := bstep (se 1 (by rfl) ⟨1657382, by rfl⟩ : syracuseStep 2209843 = 3314765) B3314765
theorem B4972157 : Blo 2209435 4972157 := bbase (se 3 (by rfl) ⟨932279, by rfl⟩ : syracuseStep 4972157 = 1864559) (by norm_num)
theorem B3314771 : Blo 2209435 3314771 := bstep (se 1 (by rfl) ⟨2486078, by rfl⟩ : syracuseStep 3314771 = 4972157) B4972157
theorem B2209847 : Blo 2209435 2209847 := bstep (se 1 (by rfl) ⟨1657385, by rfl⟩ : syracuseStep 2209847 = 3314771) B3314771
theorem B3729125 : Blo 2209435 3729125 := bbase (se 4 (by rfl) ⟨349605, by rfl⟩ : syracuseStep 3729125 = 699211) (by norm_num)
theorem B2486083 : Blo 2209435 2486083 := bstep (se 1 (by rfl) ⟨1864562, by rfl⟩ : syracuseStep 2486083 = 3729125) B3729125
theorem B3314777 : Blo 2209435 3314777 := bstep (se 2 (by rfl) ⟨1243041, by rfl⟩ : syracuseStep 3314777 = 2486083) B2486083
theorem B2209851 : Blo 2209435 2209851 := bstep (se 1 (by rfl) ⟨1657388, by rfl⟩ : syracuseStep 2209851 = 3314777) B3314777
theorem B7079525 : Blo 2209435 7079525 := bbase (se 4 (by rfl) ⟨663705, by rfl⟩ : syracuseStep 7079525 = 1327411) (by norm_num)
theorem B4719683 : Blo 2209435 4719683 := bstep (se 1 (by rfl) ⟨3539762, by rfl⟩ : syracuseStep 4719683 = 7079525) B7079525
theorem B3146455 : Blo 2209435 3146455 := bstep (se 1 (by rfl) ⟨2359841, by rfl⟩ : syracuseStep 3146455 = 4719683) B4719683
theorem B16781093 : Blo 2209435 16781093 := bstep (se 4 (by rfl) ⟨1573227, by rfl⟩ : syracuseStep 16781093 = 3146455) B3146455
theorem B11187395 : Blo 2209435 11187395 := bstep (se 1 (by rfl) ⟨8390546, by rfl⟩ : syracuseStep 11187395 = 16781093) B16781093
theorem B7458263 : Blo 2209435 7458263 := bstep (se 1 (by rfl) ⟨5593697, by rfl⟩ : syracuseStep 7458263 = 11187395) B11187395
theorem B4972175 : Blo 2209435 4972175 := bstep (se 1 (by rfl) ⟨3729131, by rfl⟩ : syracuseStep 4972175 = 7458263) B7458263
theorem B3314783 : Blo 2209435 3314783 := bstep (se 1 (by rfl) ⟨2486087, by rfl⟩ : syracuseStep 3314783 = 4972175) B4972175
theorem B2209855 : Blo 2209435 2209855 := bstep (se 1 (by rfl) ⟨1657391, by rfl⟩ : syracuseStep 2209855 = 3314783) B3314783
theorem B3314789 : Blo 2209435 3314789 := bbase (se 4 (by rfl) ⟨310761, by rfl⟩ : syracuseStep 3314789 = 621523) (by norm_num)
theorem B2209859 : Blo 2209435 2209859 := bstep (se 1 (by rfl) ⟨1657394, by rfl⟩ : syracuseStep 2209859 = 3314789) B3314789
theorem B4719701 : Blo 2209435 4719701 := bbase (se 8 (by rfl) ⟨27654, by rfl⟩ : syracuseStep 4719701 = 55309) (by norm_num)
theorem B3146467 : Blo 2209435 3146467 := bstep (se 1 (by rfl) ⟨2359850, by rfl⟩ : syracuseStep 3146467 = 4719701) B4719701
theorem B4195289 : Blo 2209435 4195289 := bstep (se 2 (by rfl) ⟨1573233, by rfl⟩ : syracuseStep 4195289 = 3146467) B3146467
theorem B2796859 : Blo 2209435 2796859 := bstep (se 1 (by rfl) ⟨2097644, by rfl⟩ : syracuseStep 2796859 = 4195289) B4195289
theorem B3729145 : Blo 2209435 3729145 := bstep (se 2 (by rfl) ⟨1398429, by rfl⟩ : syracuseStep 3729145 = 2796859) B2796859
theorem B4972193 : Blo 2209435 4972193 := bstep (se 2 (by rfl) ⟨1864572, by rfl⟩ : syracuseStep 4972193 = 3729145) B3729145
theorem B3314795 : Blo 2209435 3314795 := bstep (se 1 (by rfl) ⟨2486096, by rfl⟩ : syracuseStep 3314795 = 4972193) B4972193
theorem B2209863 : Blo 2209435 2209863 := bstep (se 1 (by rfl) ⟨1657397, by rfl⟩ : syracuseStep 2209863 = 3314795) B3314795
theorem B2486101 : Blo 2209435 2486101 := bbase (se 9 (by rfl) ⟨7283, by rfl⟩ : syracuseStep 2486101 = 14567) (by norm_num)
theorem B3314801 : Blo 2209435 3314801 := bstep (se 2 (by rfl) ⟨1243050, by rfl⟩ : syracuseStep 3314801 = 2486101) B2486101
theorem B2209867 : Blo 2209435 2209867 := bstep (se 1 (by rfl) ⟨1657400, by rfl⟩ : syracuseStep 2209867 = 3314801) B3314801
theorem B2796869 : Blo 2209435 2796869 := bbase (se 4 (by rfl) ⟨262206, by rfl⟩ : syracuseStep 2796869 = 524413) (by norm_num)
theorem B7458317 : Blo 2209435 7458317 := bstep (se 3 (by rfl) ⟨1398434, by rfl⟩ : syracuseStep 7458317 = 2796869) B2796869
theorem B4972211 : Blo 2209435 4972211 := bstep (se 1 (by rfl) ⟨3729158, by rfl⟩ : syracuseStep 4972211 = 7458317) B7458317
theorem B3314807 : Blo 2209435 3314807 := bstep (se 1 (by rfl) ⟨2486105, by rfl⟩ : syracuseStep 3314807 = 4972211) B4972211
theorem B2209871 : Blo 2209435 2209871 := bstep (se 1 (by rfl) ⟨1657403, by rfl⟩ : syracuseStep 2209871 = 3314807) B3314807
theorem B3314813 : Blo 2209435 3314813 := bbase (se 3 (by rfl) ⟨621527, by rfl⟩ : syracuseStep 3314813 = 1243055) (by norm_num)
theorem B2209875 : Blo 2209435 2209875 := bstep (se 1 (by rfl) ⟨1657406, by rfl⟩ : syracuseStep 2209875 = 3314813) B3314813
theorem B4972229 : Blo 2209435 4972229 := bbase (se 4 (by rfl) ⟨466146, by rfl⟩ : syracuseStep 4972229 = 932293) (by norm_num)
theorem B3314819 : Blo 2209435 3314819 := bstep (se 1 (by rfl) ⟨2486114, by rfl⟩ : syracuseStep 3314819 = 4972229) B4972229
theorem B2209879 : Blo 2209435 2209879 := bstep (se 1 (by rfl) ⟨1657409, by rfl⟩ : syracuseStep 2209879 = 3314819) B3314819
theorem B30240469 : Blo 2209435 30240469 := bbase (se 7 (by rfl) ⟨354380, by rfl⟩ : syracuseStep 30240469 = 708761) (by norm_num)
theorem B161282501 : Blo 2209435 161282501 := bstep (se 4 (by rfl) ⟨15120234, by rfl⟩ : syracuseStep 161282501 = 30240469) B30240469
theorem B107521667 : Blo 2209435 107521667 := bstep (se 1 (by rfl) ⟨80641250, by rfl⟩ : syracuseStep 107521667 = 161282501) B161282501
theorem B71681111 : Blo 2209435 71681111 := bstep (se 1 (by rfl) ⟨53760833, by rfl⟩ : syracuseStep 71681111 = 107521667) B107521667
theorem B47787407 : Blo 2209435 47787407 := bstep (se 1 (by rfl) ⟨35840555, by rfl⟩ : syracuseStep 47787407 = 71681111) B71681111
theorem B31858271 : Blo 2209435 31858271 := bstep (se 1 (by rfl) ⟨23893703, by rfl⟩ : syracuseStep 31858271 = 47787407) B47787407
theorem B21238847 : Blo 2209435 21238847 := bstep (se 1 (by rfl) ⟨15929135, by rfl⟩ : syracuseStep 21238847 = 31858271) B31858271
theorem B14159231 : Blo 2209435 14159231 := bstep (se 1 (by rfl) ⟨10619423, by rfl⟩ : syracuseStep 14159231 = 21238847) B21238847
theorem B9439487 : Blo 2209435 9439487 := bstep (se 1 (by rfl) ⟨7079615, by rfl⟩ : syracuseStep 9439487 = 14159231) B14159231
theorem B6292991 : Blo 2209435 6292991 := bstep (se 1 (by rfl) ⟨4719743, by rfl⟩ : syracuseStep 6292991 = 9439487) B9439487
theorem B4195327 : Blo 2209435 4195327 := bstep (se 1 (by rfl) ⟨3146495, by rfl⟩ : syracuseStep 4195327 = 6292991) B6292991
theorem B5593769 : Blo 2209435 5593769 := bstep (se 2 (by rfl) ⟨2097663, by rfl⟩ : syracuseStep 5593769 = 4195327) B4195327
theorem B3729179 : Blo 2209435 3729179 := bstep (se 1 (by rfl) ⟨2796884, by rfl⟩ : syracuseStep 3729179 = 5593769) B5593769
theorem B2486119 : Blo 2209435 2486119 := bstep (se 1 (by rfl) ⟨1864589, by rfl⟩ : syracuseStep 2486119 = 3729179) B3729179
theorem B3314825 : Blo 2209435 3314825 := bstep (se 2 (by rfl) ⟨1243059, by rfl⟩ : syracuseStep 3314825 = 2486119) B2486119
theorem B2209883 : Blo 2209435 2209883 := bstep (se 1 (by rfl) ⟨1657412, by rfl⟩ : syracuseStep 2209883 = 3314825) B3314825
theorem B11187557 : Blo 2209435 11187557 := bbase (se 4 (by rfl) ⟨1048833, by rfl⟩ : syracuseStep 11187557 = 2097667) (by norm_num)
theorem B7458371 : Blo 2209435 7458371 := bstep (se 1 (by rfl) ⟨5593778, by rfl⟩ : syracuseStep 7458371 = 11187557) B11187557
theorem B4972247 : Blo 2209435 4972247 := bstep (se 1 (by rfl) ⟨3729185, by rfl⟩ : syracuseStep 4972247 = 7458371) B7458371
theorem B3314831 : Blo 2209435 3314831 := bstep (se 1 (by rfl) ⟨2486123, by rfl⟩ : syracuseStep 3314831 = 4972247) B4972247
theorem B2209887 : Blo 2209435 2209887 := bstep (se 1 (by rfl) ⟨1657415, by rfl⟩ : syracuseStep 2209887 = 3314831) B3314831
theorem B3314837 : Blo 2209435 3314837 := bbase (se 6 (by rfl) ⟨77691, by rfl⟩ : syracuseStep 3314837 = 155383) (by norm_num)
theorem B2209891 : Blo 2209435 2209891 := bstep (se 1 (by rfl) ⟨1657418, by rfl⟩ : syracuseStep 2209891 = 3314837) B3314837
theorem B7079653 : Blo 2209435 7079653 := bbase (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) (by norm_num)
theorem B9439537 : Blo 2209435 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B12586049 : Blo 2209435 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B8390699 : Blo 2209435 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B5593799 : Blo 2209435 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B3729199 : Blo 2209435 3729199 := bstep (se 1 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 3729199 = 5593799) B5593799
theorem B4972265 : Blo 2209435 4972265 := bstep (se 2 (by rfl) ⟨1864599, by rfl⟩ : syracuseStep 4972265 = 3729199) B3729199
theorem B3314843 : Blo 2209435 3314843 := bstep (se 1 (by rfl) ⟨2486132, by rfl⟩ : syracuseStep 3314843 = 4972265) B4972265
theorem B2209895 : Blo 2209435 2209895 := bstep (se 1 (by rfl) ⟨1657421, by rfl⟩ : syracuseStep 2209895 = 3314843) B3314843
theorem B2486137 : Blo 2209435 2486137 := bbase (se 2 (by rfl) ⟨932301, by rfl⟩ : syracuseStep 2486137 = 1864603) (by norm_num)
theorem B3314849 : Blo 2209435 3314849 := bstep (se 2 (by rfl) ⟨1243068, by rfl⟩ : syracuseStep 3314849 = 2486137) B2486137
theorem B2209899 : Blo 2209435 2209899 := bstep (se 1 (by rfl) ⟨1657424, by rfl⟩ : syracuseStep 2209899 = 3314849) B3314849
theorem B9082469 : Blo 2209435 9082469 := bbase (se 4 (by rfl) ⟨851481, by rfl⟩ : syracuseStep 9082469 = 1702963) (by norm_num)
theorem B24219917 : Blo 2209435 24219917 := bstep (se 3 (by rfl) ⟨4541234, by rfl⟩ : syracuseStep 24219917 = 9082469) B9082469
theorem B16146611 : Blo 2209435 16146611 := bstep (se 1 (by rfl) ⟨12109958, by rfl⟩ : syracuseStep 16146611 = 24219917) B24219917
theorem B10764407 : Blo 2209435 10764407 := bstep (se 1 (by rfl) ⟨8073305, by rfl⟩ : syracuseStep 10764407 = 16146611) B16146611
theorem B7176271 : Blo 2209435 7176271 := bstep (se 1 (by rfl) ⟨5382203, by rfl⟩ : syracuseStep 7176271 = 10764407) B10764407
theorem B9568361 : Blo 2209435 9568361 := bstep (se 2 (by rfl) ⟨3588135, by rfl⟩ : syracuseStep 9568361 = 7176271) B7176271
theorem B6378907 : Blo 2209435 6378907 := bstep (se 1 (by rfl) ⟨4784180, by rfl⟩ : syracuseStep 6378907 = 9568361) B9568361
theorem B8505209 : Blo 2209435 8505209 := bstep (se 2 (by rfl) ⟨3189453, by rfl⟩ : syracuseStep 8505209 = 6378907) B6378907
theorem B22680557 : Blo 2209435 22680557 := bstep (se 3 (by rfl) ⟨4252604, by rfl⟩ : syracuseStep 22680557 = 8505209) B8505209
theorem B15120371 : Blo 2209435 15120371 := bstep (se 1 (by rfl) ⟨11340278, by rfl⟩ : syracuseStep 15120371 = 22680557) B22680557
theorem B40320989 : Blo 2209435 40320989 := bstep (se 3 (by rfl) ⟨7560185, by rfl⟩ : syracuseStep 40320989 = 15120371) B15120371
theorem B26880659 : Blo 2209435 26880659 := bstep (se 1 (by rfl) ⟨20160494, by rfl⟩ : syracuseStep 26880659 = 40320989) B40320989
theorem B17920439 : Blo 2209435 17920439 := bstep (se 1 (by rfl) ⟨13440329, by rfl⟩ : syracuseStep 17920439 = 26880659) B26880659
theorem B11946959 : Blo 2209435 11946959 := bstep (se 1 (by rfl) ⟨8960219, by rfl⟩ : syracuseStep 11946959 = 17920439) B17920439
theorem B7964639 : Blo 2209435 7964639 := bstep (se 1 (by rfl) ⟨5973479, by rfl⟩ : syracuseStep 7964639 = 11946959) B11946959
theorem B5309759 : Blo 2209435 5309759 := bstep (se 1 (by rfl) ⟨3982319, by rfl⟩ : syracuseStep 5309759 = 7964639) B7964639
theorem B14159357 : Blo 2209435 14159357 := bstep (se 3 (by rfl) ⟨2654879, by rfl⟩ : syracuseStep 14159357 = 5309759) B5309759
theorem B9439571 : Blo 2209435 9439571 := bstep (se 1 (by rfl) ⟨7079678, by rfl⟩ : syracuseStep 9439571 = 14159357) B14159357
theorem B6293047 : Blo 2209435 6293047 := bstep (se 1 (by rfl) ⟨4719785, by rfl⟩ : syracuseStep 6293047 = 9439571) B9439571
theorem B8390729 : Blo 2209435 8390729 := bstep (se 2 (by rfl) ⟨3146523, by rfl⟩ : syracuseStep 8390729 = 6293047) B6293047
theorem B5593819 : Blo 2209435 5593819 := bstep (se 1 (by rfl) ⟨4195364, by rfl⟩ : syracuseStep 5593819 = 8390729) B8390729
theorem B7458425 : Blo 2209435 7458425 := bstep (se 2 (by rfl) ⟨2796909, by rfl⟩ : syracuseStep 7458425 = 5593819) B5593819
theorem B4972283 : Blo 2209435 4972283 := bstep (se 1 (by rfl) ⟨3729212, by rfl⟩ : syracuseStep 4972283 = 7458425) B7458425
theorem B3314855 : Blo 2209435 3314855 := bstep (se 1 (by rfl) ⟨2486141, by rfl⟩ : syracuseStep 3314855 = 4972283) B4972283
theorem B2209903 : Blo 2209435 2209903 := bstep (se 1 (by rfl) ⟨1657427, by rfl⟩ : syracuseStep 2209903 = 3314855) B3314855
theorem B3314861 : Blo 2209435 3314861 := bbase (se 3 (by rfl) ⟨621536, by rfl⟩ : syracuseStep 3314861 = 1243073) (by norm_num)
theorem B2209907 : Blo 2209435 2209907 := bstep (se 1 (by rfl) ⟨1657430, by rfl⟩ : syracuseStep 2209907 = 3314861) B3314861
theorem B4972301 : Blo 2209435 4972301 := bbase (se 3 (by rfl) ⟨932306, by rfl⟩ : syracuseStep 4972301 = 1864613) (by norm_num)
theorem B3314867 : Blo 2209435 3314867 := bstep (se 1 (by rfl) ⟨2486150, by rfl⟩ : syracuseStep 3314867 = 4972301) B4972301
theorem B2209911 : Blo 2209435 2209911 := bstep (se 1 (by rfl) ⟨1657433, by rfl⟩ : syracuseStep 2209911 = 3314867) B3314867
theorem B2796925 : Blo 2209435 2796925 := bbase (se 3 (by rfl) ⟨524423, by rfl⟩ : syracuseStep 2796925 = 1048847) (by norm_num)
theorem B3729233 : Blo 2209435 3729233 := bstep (se 2 (by rfl) ⟨1398462, by rfl⟩ : syracuseStep 3729233 = 2796925) B2796925
theorem B2486155 : Blo 2209435 2486155 := bstep (se 1 (by rfl) ⟨1864616, by rfl⟩ : syracuseStep 2486155 = 3729233) B3729233
theorem B3314873 : Blo 2209435 3314873 := bstep (se 2 (by rfl) ⟨1243077, by rfl⟩ : syracuseStep 3314873 = 2486155) B2486155
theorem B2209915 : Blo 2209435 2209915 := bstep (se 1 (by rfl) ⟨1657436, by rfl⟩ : syracuseStep 2209915 = 3314873) B3314873
theorem B5309797 : Blo 2209435 5309797 := bbase (se 4 (by rfl) ⟨497793, by rfl⟩ : syracuseStep 5309797 = 995587) (by norm_num)
theorem B7079729 : Blo 2209435 7079729 := bstep (se 2 (by rfl) ⟨2654898, by rfl⟩ : syracuseStep 7079729 = 5309797) B5309797
theorem B18879277 : Blo 2209435 18879277 := bstep (se 3 (by rfl) ⟨3539864, by rfl⟩ : syracuseStep 18879277 = 7079729) B7079729
theorem B25172369 : Blo 2209435 25172369 := bstep (se 2 (by rfl) ⟨9439638, by rfl⟩ : syracuseStep 25172369 = 18879277) B18879277
theorem B16781579 : Blo 2209435 16781579 := bstep (se 1 (by rfl) ⟨12586184, by rfl⟩ : syracuseStep 16781579 = 25172369) B25172369
theorem B11187719 : Blo 2209435 11187719 := bstep (se 1 (by rfl) ⟨8390789, by rfl⟩ : syracuseStep 11187719 = 16781579) B16781579
theorem B7458479 : Blo 2209435 7458479 := bstep (se 1 (by rfl) ⟨5593859, by rfl⟩ : syracuseStep 7458479 = 11187719) B11187719
theorem B4972319 : Blo 2209435 4972319 := bstep (se 1 (by rfl) ⟨3729239, by rfl⟩ : syracuseStep 4972319 = 7458479) B7458479
theorem B3314879 : Blo 2209435 3314879 := bstep (se 1 (by rfl) ⟨2486159, by rfl⟩ : syracuseStep 3314879 = 4972319) B4972319
theorem B2209919 : Blo 2209435 2209919 := bstep (se 1 (by rfl) ⟨1657439, by rfl⟩ : syracuseStep 2209919 = 3314879) B3314879
theorem B3314885 : Blo 2209435 3314885 := bbase (se 4 (by rfl) ⟨310770, by rfl⟩ : syracuseStep 3314885 = 621541) (by norm_num)
theorem B2209923 : Blo 2209435 2209923 := bstep (se 1 (by rfl) ⟨1657442, by rfl⟩ : syracuseStep 2209923 = 3314885) B3314885
theorem B3729253 : Blo 2209435 3729253 := bbase (se 4 (by rfl) ⟨349617, by rfl⟩ : syracuseStep 3729253 = 699235) (by norm_num)
theorem B4972337 : Blo 2209435 4972337 := bstep (se 2 (by rfl) ⟨1864626, by rfl⟩ : syracuseStep 4972337 = 3729253) B3729253
theorem B3314891 : Blo 2209435 3314891 := bstep (se 1 (by rfl) ⟨2486168, by rfl⟩ : syracuseStep 3314891 = 4972337) B4972337
theorem B2209927 : Blo 2209435 2209927 := bstep (se 1 (by rfl) ⟨1657445, by rfl⟩ : syracuseStep 2209927 = 3314891) B3314891
theorem B2486173 : Blo 2209435 2486173 := bbase (se 3 (by rfl) ⟨466157, by rfl⟩ : syracuseStep 2486173 = 932315) (by norm_num)
theorem B3314897 : Blo 2209435 3314897 := bstep (se 2 (by rfl) ⟨1243086, by rfl⟩ : syracuseStep 3314897 = 2486173) B2486173
theorem B2209931 : Blo 2209435 2209931 := bstep (se 1 (by rfl) ⟨1657448, by rfl⟩ : syracuseStep 2209931 = 3314897) B3314897
theorem B7458533 : Blo 2209435 7458533 := bbase (se 4 (by rfl) ⟨699237, by rfl⟩ : syracuseStep 7458533 = 1398475) (by norm_num)
theorem B4972355 : Blo 2209435 4972355 := bstep (se 1 (by rfl) ⟨3729266, by rfl⟩ : syracuseStep 4972355 = 7458533) B7458533
theorem B3314903 : Blo 2209435 3314903 := bstep (se 1 (by rfl) ⟨2486177, by rfl⟩ : syracuseStep 3314903 = 4972355) B4972355
theorem B2209935 : Blo 2209435 2209935 := bstep (se 1 (by rfl) ⟨1657451, by rfl⟩ : syracuseStep 2209935 = 3314903) B3314903
theorem B3314909 : Blo 2209435 3314909 := bbase (se 3 (by rfl) ⟨621545, by rfl⟩ : syracuseStep 3314909 = 1243091) (by norm_num)
theorem B2209939 : Blo 2209435 2209939 := bstep (se 1 (by rfl) ⟨1657454, by rfl⟩ : syracuseStep 2209939 = 3314909) B3314909
theorem B4972373 : Blo 2209435 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B3314915 : Blo 2209435 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B2209943 : Blo 2209435 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B6293173 : Blo 2209435 6293173 := bbase (se 5 (by rfl) ⟨294992, by rfl⟩ : syracuseStep 6293173 = 589985) (by norm_num)
theorem B8390897 : Blo 2209435 8390897 := bstep (se 2 (by rfl) ⟨3146586, by rfl⟩ : syracuseStep 8390897 = 6293173) B6293173
theorem B5593931 : Blo 2209435 5593931 := bstep (se 1 (by rfl) ⟨4195448, by rfl⟩ : syracuseStep 5593931 = 8390897) B8390897
theorem B3729287 : Blo 2209435 3729287 := bstep (se 1 (by rfl) ⟨2796965, by rfl⟩ : syracuseStep 3729287 = 5593931) B5593931
theorem B2486191 : Blo 2209435 2486191 := bstep (se 1 (by rfl) ⟨1864643, by rfl⟩ : syracuseStep 2486191 = 3729287) B3729287
theorem B3314921 : Blo 2209435 3314921 := bstep (se 2 (by rfl) ⟨1243095, by rfl⟩ : syracuseStep 3314921 = 2486191) B2486191
theorem B2209947 : Blo 2209435 2209947 := bstep (se 1 (by rfl) ⟨1657460, by rfl⟩ : syracuseStep 2209947 = 3314921) B3314921
theorem B26881237 : Blo 2209435 26881237 := bbase (se 7 (by rfl) ⟨315014, by rfl⟩ : syracuseStep 26881237 = 630029) (by norm_num)
theorem B143366597 : Blo 2209435 143366597 := bstep (se 4 (by rfl) ⟨13440618, by rfl⟩ : syracuseStep 143366597 = 26881237) B26881237
theorem B95577731 : Blo 2209435 95577731 := bstep (se 1 (by rfl) ⟨71683298, by rfl⟩ : syracuseStep 95577731 = 143366597) B143366597
theorem B63718487 : Blo 2209435 63718487 := bstep (se 1 (by rfl) ⟨47788865, by rfl⟩ : syracuseStep 63718487 = 95577731) B95577731
theorem B42478991 : Blo 2209435 42478991 := bstep (se 1 (by rfl) ⟨31859243, by rfl⟩ : syracuseStep 42478991 = 63718487) B63718487
theorem B28319327 : Blo 2209435 28319327 := bstep (se 1 (by rfl) ⟨21239495, by rfl⟩ : syracuseStep 28319327 = 42478991) B42478991
theorem B18879551 : Blo 2209435 18879551 := bstep (se 1 (by rfl) ⟨14159663, by rfl⟩ : syracuseStep 18879551 = 28319327) B28319327
theorem B12586367 : Blo 2209435 12586367 := bstep (se 1 (by rfl) ⟨9439775, by rfl⟩ : syracuseStep 12586367 = 18879551) B18879551
theorem B8390911 : Blo 2209435 8390911 := bstep (se 1 (by rfl) ⟨6293183, by rfl⟩ : syracuseStep 8390911 = 12586367) B12586367
theorem B11187881 : Blo 2209435 11187881 := bstep (se 2 (by rfl) ⟨4195455, by rfl⟩ : syracuseStep 11187881 = 8390911) B8390911
theorem B7458587 : Blo 2209435 7458587 := bstep (se 1 (by rfl) ⟨5593940, by rfl⟩ : syracuseStep 7458587 = 11187881) B11187881
theorem B4972391 : Blo 2209435 4972391 := bstep (se 1 (by rfl) ⟨3729293, by rfl⟩ : syracuseStep 4972391 = 7458587) B7458587
theorem B3314927 : Blo 2209435 3314927 := bstep (se 1 (by rfl) ⟨2486195, by rfl⟩ : syracuseStep 3314927 = 4972391) B4972391
theorem B2209951 : Blo 2209435 2209951 := bstep (se 1 (by rfl) ⟨1657463, by rfl⟩ : syracuseStep 2209951 = 3314927) B3314927
theorem B3314933 : Blo 2209435 3314933 := bbase (se 5 (by rfl) ⟨155387, by rfl⟩ : syracuseStep 3314933 = 310775) (by norm_num)
theorem B2209955 : Blo 2209435 2209955 := bstep (se 1 (by rfl) ⟨1657466, by rfl⟩ : syracuseStep 2209955 = 3314933) B3314933
theorem B3982421 : Blo 2209435 3982421 := bbase (se 8 (by rfl) ⟨23334, by rfl⟩ : syracuseStep 3982421 = 46669) (by norm_num)
theorem B2654947 : Blo 2209435 2654947 := bstep (se 1 (by rfl) ⟨1991210, by rfl⟩ : syracuseStep 2654947 = 3982421) B3982421
theorem B14159717 : Blo 2209435 14159717 := bstep (se 4 (by rfl) ⟨1327473, by rfl⟩ : syracuseStep 14159717 = 2654947) B2654947
theorem B9439811 : Blo 2209435 9439811 := bstep (se 1 (by rfl) ⟨7079858, by rfl⟩ : syracuseStep 9439811 = 14159717) B14159717
theorem B6293207 : Blo 2209435 6293207 := bstep (se 1 (by rfl) ⟨4719905, by rfl⟩ : syracuseStep 6293207 = 9439811) B9439811
theorem B4195471 : Blo 2209435 4195471 := bstep (se 1 (by rfl) ⟨3146603, by rfl⟩ : syracuseStep 4195471 = 6293207) B6293207
theorem B5593961 : Blo 2209435 5593961 := bstep (se 2 (by rfl) ⟨2097735, by rfl⟩ : syracuseStep 5593961 = 4195471) B4195471
theorem B3729307 : Blo 2209435 3729307 := bstep (se 1 (by rfl) ⟨2796980, by rfl⟩ : syracuseStep 3729307 = 5593961) B5593961
theorem B4972409 : Blo 2209435 4972409 := bstep (se 2 (by rfl) ⟨1864653, by rfl⟩ : syracuseStep 4972409 = 3729307) B3729307
theorem B3314939 : Blo 2209435 3314939 := bstep (se 1 (by rfl) ⟨2486204, by rfl⟩ : syracuseStep 3314939 = 4972409) B4972409
theorem B2209959 : Blo 2209435 2209959 := bstep (se 1 (by rfl) ⟨1657469, by rfl⟩ : syracuseStep 2209959 = 3314939) B3314939
theorem B2486209 : Blo 2209435 2486209 := bbase (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) (by norm_num)
theorem B3314945 : Blo 2209435 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B2209963 : Blo 2209435 2209963 := bstep (se 1 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 2209963 = 3314945) B3314945
theorem B5593981 : Blo 2209435 5593981 := bbase (se 3 (by rfl) ⟨1048871, by rfl⟩ : syracuseStep 5593981 = 2097743) (by norm_num)
theorem B7458641 : Blo 2209435 7458641 := bstep (se 2 (by rfl) ⟨2796990, by rfl⟩ : syracuseStep 7458641 = 5593981) B5593981
theorem B4972427 : Blo 2209435 4972427 := bstep (se 1 (by rfl) ⟨3729320, by rfl⟩ : syracuseStep 4972427 = 7458641) B7458641
theorem B3314951 : Blo 2209435 3314951 := bstep (se 1 (by rfl) ⟨2486213, by rfl⟩ : syracuseStep 3314951 = 4972427) B4972427
theorem B2209967 : Blo 2209435 2209967 := bstep (se 1 (by rfl) ⟨1657475, by rfl⟩ : syracuseStep 2209967 = 3314951) B3314951
theorem B3314957 : Blo 2209435 3314957 := bbase (se 3 (by rfl) ⟨621554, by rfl⟩ : syracuseStep 3314957 = 1243109) (by norm_num)
theorem B2209971 : Blo 2209435 2209971 := bstep (se 1 (by rfl) ⟨1657478, by rfl⟩ : syracuseStep 2209971 = 3314957) B3314957
theorem B4972445 : Blo 2209435 4972445 := bbase (se 3 (by rfl) ⟨932333, by rfl⟩ : syracuseStep 4972445 = 1864667) (by norm_num)
theorem B3314963 : Blo 2209435 3314963 := bstep (se 1 (by rfl) ⟨2486222, by rfl⟩ : syracuseStep 3314963 = 4972445) B4972445
theorem B2209975 : Blo 2209435 2209975 := bstep (se 1 (by rfl) ⟨1657481, by rfl⟩ : syracuseStep 2209975 = 3314963) B3314963
theorem B3729341 : Blo 2209435 3729341 := bbase (se 3 (by rfl) ⟨699251, by rfl⟩ : syracuseStep 3729341 = 1398503) (by norm_num)
theorem B2486227 : Blo 2209435 2486227 := bstep (se 1 (by rfl) ⟨1864670, by rfl⟩ : syracuseStep 2486227 = 3729341) B3729341
theorem B3314969 : Blo 2209435 3314969 := bstep (se 2 (by rfl) ⟨1243113, by rfl⟩ : syracuseStep 3314969 = 2486227) B2486227
theorem B2209979 : Blo 2209435 2209979 := bstep (se 1 (by rfl) ⟨1657484, by rfl⟩ : syracuseStep 2209979 = 3314969) B3314969
theorem B12586549 : Blo 2209435 12586549 := bbase (se 5 (by rfl) ⟨589994, by rfl⟩ : syracuseStep 12586549 = 1179989) (by norm_num)
theorem B16782065 : Blo 2209435 16782065 := bstep (se 2 (by rfl) ⟨6293274, by rfl⟩ : syracuseStep 16782065 = 12586549) B12586549
theorem B11188043 : Blo 2209435 11188043 := bstep (se 1 (by rfl) ⟨8391032, by rfl⟩ : syracuseStep 11188043 = 16782065) B16782065
theorem B7458695 : Blo 2209435 7458695 := bstep (se 1 (by rfl) ⟨5594021, by rfl⟩ : syracuseStep 7458695 = 11188043) B11188043
theorem B4972463 : Blo 2209435 4972463 := bstep (se 1 (by rfl) ⟨3729347, by rfl⟩ : syracuseStep 4972463 = 7458695) B7458695
theorem B3314975 : Blo 2209435 3314975 := bstep (se 1 (by rfl) ⟨2486231, by rfl⟩ : syracuseStep 3314975 = 4972463) B4972463
theorem B2209983 : Blo 2209435 2209983 := bstep (se 1 (by rfl) ⟨1657487, by rfl⟩ : syracuseStep 2209983 = 3314975) B3314975
theorem B3314981 : Blo 2209435 3314981 := bbase (se 4 (by rfl) ⟨310779, by rfl⟩ : syracuseStep 3314981 = 621559) (by norm_num)
theorem B2209987 : Blo 2209435 2209987 := bstep (se 1 (by rfl) ⟨1657490, by rfl⟩ : syracuseStep 2209987 = 3314981) B3314981
theorem B2797021 : Blo 2209435 2797021 := bbase (se 3 (by rfl) ⟨524441, by rfl⟩ : syracuseStep 2797021 = 1048883) (by norm_num)
theorem B3729361 : Blo 2209435 3729361 := bstep (se 2 (by rfl) ⟨1398510, by rfl⟩ : syracuseStep 3729361 = 2797021) B2797021
theorem B4972481 : Blo 2209435 4972481 := bstep (se 2 (by rfl) ⟨1864680, by rfl⟩ : syracuseStep 4972481 = 3729361) B3729361
theorem B3314987 : Blo 2209435 3314987 := bstep (se 1 (by rfl) ⟨2486240, by rfl⟩ : syracuseStep 3314987 = 4972481) B4972481
theorem B2209991 : Blo 2209435 2209991 := bstep (se 1 (by rfl) ⟨1657493, by rfl⟩ : syracuseStep 2209991 = 3314987) B3314987
theorem B2486245 : Blo 2209435 2486245 := bbase (se 4 (by rfl) ⟨233085, by rfl⟩ : syracuseStep 2486245 = 466171) (by norm_num)
theorem B3314993 : Blo 2209435 3314993 := bstep (se 2 (by rfl) ⟨1243122, by rfl⟩ : syracuseStep 3314993 = 2486245) B2486245
theorem B2209995 : Blo 2209435 2209995 := bstep (se 1 (by rfl) ⟨1657496, by rfl⟩ : syracuseStep 2209995 = 3314993) B3314993
theorem B3982493 : Blo 2209435 3982493 := bbase (se 3 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 3982493 = 1493435) (by norm_num)
theorem B10619981 : Blo 2209435 10619981 := bstep (se 3 (by rfl) ⟨1991246, by rfl⟩ : syracuseStep 10619981 = 3982493) B3982493
theorem B7079987 : Blo 2209435 7079987 := bstep (se 1 (by rfl) ⟨5309990, by rfl⟩ : syracuseStep 7079987 = 10619981) B10619981
theorem B4719991 : Blo 2209435 4719991 := bstep (se 1 (by rfl) ⟨3539993, by rfl⟩ : syracuseStep 4719991 = 7079987) B7079987
theorem B6293321 : Blo 2209435 6293321 := bstep (se 2 (by rfl) ⟨2359995, by rfl⟩ : syracuseStep 6293321 = 4719991) B4719991
theorem B4195547 : Blo 2209435 4195547 := bstep (se 1 (by rfl) ⟨3146660, by rfl⟩ : syracuseStep 4195547 = 6293321) B6293321
theorem B2797031 : Blo 2209435 2797031 := bstep (se 1 (by rfl) ⟨2097773, by rfl⟩ : syracuseStep 2797031 = 4195547) B4195547
theorem B7458749 : Blo 2209435 7458749 := bstep (se 3 (by rfl) ⟨1398515, by rfl⟩ : syracuseStep 7458749 = 2797031) B2797031
theorem B4972499 : Blo 2209435 4972499 := bstep (se 1 (by rfl) ⟨3729374, by rfl⟩ : syracuseStep 4972499 = 7458749) B7458749
theorem B3314999 : Blo 2209435 3314999 := bstep (se 1 (by rfl) ⟨2486249, by rfl⟩ : syracuseStep 3314999 = 4972499) B4972499
theorem B2209999 : Blo 2209435 2209999 := bstep (se 1 (by rfl) ⟨1657499, by rfl⟩ : syracuseStep 2209999 = 3314999) B3314999
theorem B3315005 : Blo 2209435 3315005 := bbase (se 3 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 3315005 = 1243127) (by norm_num)
theorem B2210003 : Blo 2209435 2210003 := bstep (se 1 (by rfl) ⟨1657502, by rfl⟩ : syracuseStep 2210003 = 3315005) B3315005
theorem B4972517 : Blo 2209435 4972517 := bbase (se 4 (by rfl) ⟨466173, by rfl⟩ : syracuseStep 4972517 = 932347) (by norm_num)
theorem B3315011 : Blo 2209435 3315011 := bstep (se 1 (by rfl) ⟨2486258, by rfl⟩ : syracuseStep 3315011 = 4972517) B4972517
theorem B2210007 : Blo 2209435 2210007 := bstep (se 1 (by rfl) ⟨1657505, by rfl⟩ : syracuseStep 2210007 = 3315011) B3315011
theorem B5594093 : Blo 2209435 5594093 := bbase (se 3 (by rfl) ⟨1048892, by rfl⟩ : syracuseStep 5594093 = 2097785) (by norm_num)
theorem B3729395 : Blo 2209435 3729395 := bstep (se 1 (by rfl) ⟨2797046, by rfl⟩ : syracuseStep 3729395 = 5594093) B5594093
theorem B2486263 : Blo 2209435 2486263 := bstep (se 1 (by rfl) ⟨1864697, by rfl⟩ : syracuseStep 2486263 = 3729395) B3729395
theorem B3315017 : Blo 2209435 3315017 := bstep (se 2 (by rfl) ⟨1243131, by rfl⟩ : syracuseStep 3315017 = 2486263) B2486263
theorem B2210011 : Blo 2209435 2210011 := bstep (se 1 (by rfl) ⟨1657508, by rfl⟩ : syracuseStep 2210011 = 3315017) B3315017
theorem B5310029 : Blo 2209435 5310029 := bbase (se 3 (by rfl) ⟨995630, by rfl⟩ : syracuseStep 5310029 = 1991261) (by norm_num)
theorem B3540019 : Blo 2209435 3540019 := bstep (se 1 (by rfl) ⟨2655014, by rfl⟩ : syracuseStep 3540019 = 5310029) B5310029
theorem B4720025 : Blo 2209435 4720025 := bstep (se 2 (by rfl) ⟨1770009, by rfl⟩ : syracuseStep 4720025 = 3540019) B3540019
theorem B3146683 : Blo 2209435 3146683 := bstep (se 1 (by rfl) ⟨2360012, by rfl⟩ : syracuseStep 3146683 = 4720025) B4720025
theorem B4195577 : Blo 2209435 4195577 := bstep (se 2 (by rfl) ⟨1573341, by rfl⟩ : syracuseStep 4195577 = 3146683) B3146683
theorem B11188205 : Blo 2209435 11188205 := bstep (se 3 (by rfl) ⟨2097788, by rfl⟩ : syracuseStep 11188205 = 4195577) B4195577
theorem B7458803 : Blo 2209435 7458803 := bstep (se 1 (by rfl) ⟨5594102, by rfl⟩ : syracuseStep 7458803 = 11188205) B11188205
theorem B4972535 : Blo 2209435 4972535 := bstep (se 1 (by rfl) ⟨3729401, by rfl⟩ : syracuseStep 4972535 = 7458803) B7458803
theorem B3315023 : Blo 2209435 3315023 := bstep (se 1 (by rfl) ⟨2486267, by rfl⟩ : syracuseStep 3315023 = 4972535) B4972535
theorem B2210015 : Blo 2209435 2210015 := bstep (se 1 (by rfl) ⟨1657511, by rfl⟩ : syracuseStep 2210015 = 3315023) B3315023
theorem B3315029 : Blo 2209435 3315029 := bbase (se 14 (by rfl) ⟨303, by rfl⟩ : syracuseStep 3315029 = 607) (by norm_num)
theorem B2210019 : Blo 2209435 2210019 := bstep (se 1 (by rfl) ⟨1657514, by rfl⟩ : syracuseStep 2210019 = 3315029) B3315029
theorem B2360021 : Blo 2209435 2360021 := bbase (se 7 (by rfl) ⟨27656, by rfl⟩ : syracuseStep 2360021 = 55313) (by norm_num)
theorem B6293389 : Blo 2209435 6293389 := bstep (se 3 (by rfl) ⟨1180010, by rfl⟩ : syracuseStep 6293389 = 2360021) B2360021
theorem B8391185 : Blo 2209435 8391185 := bstep (se 2 (by rfl) ⟨3146694, by rfl⟩ : syracuseStep 8391185 = 6293389) B6293389
theorem B5594123 : Blo 2209435 5594123 := bstep (se 1 (by rfl) ⟨4195592, by rfl⟩ : syracuseStep 5594123 = 8391185) B8391185
theorem B3729415 : Blo 2209435 3729415 := bstep (se 1 (by rfl) ⟨2797061, by rfl⟩ : syracuseStep 3729415 = 5594123) B5594123
theorem B4972553 : Blo 2209435 4972553 := bstep (se 2 (by rfl) ⟨1864707, by rfl⟩ : syracuseStep 4972553 = 3729415) B3729415
theorem B3315035 : Blo 2209435 3315035 := bstep (se 1 (by rfl) ⟨2486276, by rfl⟩ : syracuseStep 3315035 = 4972553) B4972553
theorem B2210023 : Blo 2209435 2210023 := bstep (se 1 (by rfl) ⟨1657517, by rfl⟩ : syracuseStep 2210023 = 3315035) B3315035
theorem B2486281 : Blo 2209435 2486281 := bbase (se 2 (by rfl) ⟨932355, by rfl⟩ : syracuseStep 2486281 = 1864711) (by norm_num)
theorem B3315041 : Blo 2209435 3315041 := bstep (se 2 (by rfl) ⟨1243140, by rfl⟩ : syracuseStep 3315041 = 2486281) B2486281
theorem B2210027 : Blo 2209435 2210027 := bstep (se 1 (by rfl) ⟨1657520, by rfl⟩ : syracuseStep 2210027 = 3315041) B3315041
theorem B2270749 : Blo 2209435 2270749 := bbase (se 3 (by rfl) ⟨425765, by rfl⟩ : syracuseStep 2270749 = 851531) (by norm_num)
theorem B3027665 : Blo 2209435 3027665 := bstep (se 2 (by rfl) ⟨1135374, by rfl⟩ : syracuseStep 3027665 = 2270749) B2270749
theorem B8073773 : Blo 2209435 8073773 := bstep (se 3 (by rfl) ⟨1513832, by rfl⟩ : syracuseStep 8073773 = 3027665) B3027665
theorem B5382515 : Blo 2209435 5382515 := bstep (se 1 (by rfl) ⟨4036886, by rfl⟩ : syracuseStep 5382515 = 8073773) B8073773
theorem B3588343 : Blo 2209435 3588343 := bstep (se 1 (by rfl) ⟨2691257, by rfl⟩ : syracuseStep 3588343 = 5382515) B5382515
theorem B19137829 : Blo 2209435 19137829 := bstep (se 4 (by rfl) ⟨1794171, by rfl⟩ : syracuseStep 19137829 = 3588343) B3588343
theorem B25517105 : Blo 2209435 25517105 := bstep (se 2 (by rfl) ⟨9568914, by rfl⟩ : syracuseStep 25517105 = 19137829) B19137829
theorem B17011403 : Blo 2209435 17011403 := bstep (se 1 (by rfl) ⟨12758552, by rfl⟩ : syracuseStep 17011403 = 25517105) B25517105
theorem B11340935 : Blo 2209435 11340935 := bstep (se 1 (by rfl) ⟨8505701, by rfl⟩ : syracuseStep 11340935 = 17011403) B17011403
theorem B7560623 : Blo 2209435 7560623 := bstep (se 1 (by rfl) ⟨5670467, by rfl⟩ : syracuseStep 7560623 = 11340935) B11340935
theorem B5040415 : Blo 2209435 5040415 := bstep (se 1 (by rfl) ⟨3780311, by rfl⟩ : syracuseStep 5040415 = 7560623) B7560623
theorem B6720553 : Blo 2209435 6720553 := bstep (se 2 (by rfl) ⟨2520207, by rfl⟩ : syracuseStep 6720553 = 5040415) B5040415
theorem B35842949 : Blo 2209435 35842949 := bstep (se 4 (by rfl) ⟨3360276, by rfl⟩ : syracuseStep 35842949 = 6720553) B6720553
theorem B23895299 : Blo 2209435 23895299 := bstep (se 1 (by rfl) ⟨17921474, by rfl⟩ : syracuseStep 23895299 = 35842949) B35842949
theorem B15930199 : Blo 2209435 15930199 := bstep (se 1 (by rfl) ⟨11947649, by rfl⟩ : syracuseStep 15930199 = 23895299) B23895299
theorem B21240265 : Blo 2209435 21240265 := bstep (se 2 (by rfl) ⟨7965099, by rfl⟩ : syracuseStep 21240265 = 15930199) B15930199
theorem B28320353 : Blo 2209435 28320353 := bstep (se 2 (by rfl) ⟨10620132, by rfl⟩ : syracuseStep 28320353 = 21240265) B21240265
theorem B18880235 : Blo 2209435 18880235 := bstep (se 1 (by rfl) ⟨14160176, by rfl⟩ : syracuseStep 18880235 = 28320353) B28320353
theorem B12586823 : Blo 2209435 12586823 := bstep (se 1 (by rfl) ⟨9440117, by rfl⟩ : syracuseStep 12586823 = 18880235) B18880235
theorem B8391215 : Blo 2209435 8391215 := bstep (se 1 (by rfl) ⟨6293411, by rfl⟩ : syracuseStep 8391215 = 12586823) B12586823
theorem B5594143 : Blo 2209435 5594143 := bstep (se 1 (by rfl) ⟨4195607, by rfl⟩ : syracuseStep 5594143 = 8391215) B8391215
theorem B7458857 : Blo 2209435 7458857 := bstep (se 2 (by rfl) ⟨2797071, by rfl⟩ : syracuseStep 7458857 = 5594143) B5594143
theorem B4972571 : Blo 2209435 4972571 := bstep (se 1 (by rfl) ⟨3729428, by rfl⟩ : syracuseStep 4972571 = 7458857) B7458857
theorem B3315047 : Blo 2209435 3315047 := bstep (se 1 (by rfl) ⟨2486285, by rfl⟩ : syracuseStep 3315047 = 4972571) B4972571
theorem B2210031 : Blo 2209435 2210031 := bstep (se 1 (by rfl) ⟨1657523, by rfl⟩ : syracuseStep 2210031 = 3315047) B3315047
theorem B3315053 : Blo 2209435 3315053 := bbase (se 3 (by rfl) ⟨621572, by rfl⟩ : syracuseStep 3315053 = 1243145) (by norm_num)
theorem B2210035 : Blo 2209435 2210035 := bstep (se 1 (by rfl) ⟨1657526, by rfl⟩ : syracuseStep 2210035 = 3315053) B3315053
theorem B4972589 : Blo 2209435 4972589 := bbase (se 3 (by rfl) ⟨932360, by rfl⟩ : syracuseStep 4972589 = 1864721) (by norm_num)
theorem B3315059 : Blo 2209435 3315059 := bstep (se 1 (by rfl) ⟨2486294, by rfl⟩ : syracuseStep 3315059 = 4972589) B4972589
theorem B2210039 : Blo 2209435 2210039 := bstep (se 1 (by rfl) ⟨1657529, by rfl⟩ : syracuseStep 2210039 = 3315059) B3315059
theorem B8960789 : Blo 2209435 8960789 := bbase (se 6 (by rfl) ⟨210018, by rfl⟩ : syracuseStep 8960789 = 420037) (by norm_num)
theorem B5973859 : Blo 2209435 5973859 := bstep (se 1 (by rfl) ⟨4480394, by rfl⟩ : syracuseStep 5973859 = 8960789) B8960789
theorem B7965145 : Blo 2209435 7965145 := bstep (se 2 (by rfl) ⟨2986929, by rfl⟩ : syracuseStep 7965145 = 5973859) B5973859
theorem B10620193 : Blo 2209435 10620193 := bstep (se 2 (by rfl) ⟨3982572, by rfl⟩ : syracuseStep 10620193 = 7965145) B7965145
theorem B14160257 : Blo 2209435 14160257 := bstep (se 2 (by rfl) ⟨5310096, by rfl⟩ : syracuseStep 14160257 = 10620193) B10620193
theorem B9440171 : Blo 2209435 9440171 := bstep (se 1 (by rfl) ⟨7080128, by rfl⟩ : syracuseStep 9440171 = 14160257) B14160257
theorem B6293447 : Blo 2209435 6293447 := bstep (se 1 (by rfl) ⟨4720085, by rfl⟩ : syracuseStep 6293447 = 9440171) B9440171
theorem B4195631 : Blo 2209435 4195631 := bstep (se 1 (by rfl) ⟨3146723, by rfl⟩ : syracuseStep 4195631 = 6293447) B6293447
theorem B2797087 : Blo 2209435 2797087 := bstep (se 1 (by rfl) ⟨2097815, by rfl⟩ : syracuseStep 2797087 = 4195631) B4195631
theorem B3729449 : Blo 2209435 3729449 := bstep (se 2 (by rfl) ⟨1398543, by rfl⟩ : syracuseStep 3729449 = 2797087) B2797087
theorem B2486299 : Blo 2209435 2486299 := bstep (se 1 (by rfl) ⟨1864724, by rfl⟩ : syracuseStep 2486299 = 3729449) B3729449
theorem B3315065 : Blo 2209435 3315065 := bstep (se 2 (by rfl) ⟨1243149, by rfl⟩ : syracuseStep 3315065 = 2486299) B2486299
theorem B2210043 : Blo 2209435 2210043 := bstep (se 1 (by rfl) ⟨1657532, by rfl⟩ : syracuseStep 2210043 = 3315065) B3315065
theorem B7965157 : Blo 2209435 7965157 := bbase (se 4 (by rfl) ⟨746733, by rfl⟩ : syracuseStep 7965157 = 1493467) (by norm_num)
theorem B10620209 : Blo 2209435 10620209 := bstep (se 2 (by rfl) ⟨3982578, by rfl⟩ : syracuseStep 10620209 = 7965157) B7965157
theorem B7080139 : Blo 2209435 7080139 := bstep (se 1 (by rfl) ⟨5310104, by rfl⟩ : syracuseStep 7080139 = 10620209) B10620209
theorem B37760741 : Blo 2209435 37760741 := bstep (se 4 (by rfl) ⟨3540069, by rfl⟩ : syracuseStep 37760741 = 7080139) B7080139
theorem B25173827 : Blo 2209435 25173827 := bstep (se 1 (by rfl) ⟨18880370, by rfl⟩ : syracuseStep 25173827 = 37760741) B37760741
theorem B16782551 : Blo 2209435 16782551 := bstep (se 1 (by rfl) ⟨12586913, by rfl⟩ : syracuseStep 16782551 = 25173827) B25173827
theorem B11188367 : Blo 2209435 11188367 := bstep (se 1 (by rfl) ⟨8391275, by rfl⟩ : syracuseStep 11188367 = 16782551) B16782551
theorem B7458911 : Blo 2209435 7458911 := bstep (se 1 (by rfl) ⟨5594183, by rfl⟩ : syracuseStep 7458911 = 11188367) B11188367
theorem B4972607 : Blo 2209435 4972607 := bstep (se 1 (by rfl) ⟨3729455, by rfl⟩ : syracuseStep 4972607 = 7458911) B7458911
theorem B3315071 : Blo 2209435 3315071 := bstep (se 1 (by rfl) ⟨2486303, by rfl⟩ : syracuseStep 3315071 = 4972607) B4972607
theorem B2210047 : Blo 2209435 2210047 := bstep (se 1 (by rfl) ⟨1657535, by rfl⟩ : syracuseStep 2210047 = 3315071) B3315071
theorem B3315077 : Blo 2209435 3315077 := bbase (se 4 (by rfl) ⟨310788, by rfl⟩ : syracuseStep 3315077 = 621577) (by norm_num)
theorem B2210051 : Blo 2209435 2210051 := bstep (se 1 (by rfl) ⟨1657538, by rfl⟩ : syracuseStep 2210051 = 3315077) B3315077
theorem B3729469 : Blo 2209435 3729469 := bbase (se 3 (by rfl) ⟨699275, by rfl⟩ : syracuseStep 3729469 = 1398551) (by norm_num)
theorem B4972625 : Blo 2209435 4972625 := bstep (se 2 (by rfl) ⟨1864734, by rfl⟩ : syracuseStep 4972625 = 3729469) B3729469
theorem B3315083 : Blo 2209435 3315083 := bstep (se 1 (by rfl) ⟨2486312, by rfl⟩ : syracuseStep 3315083 = 4972625) B4972625
theorem B2210055 : Blo 2209435 2210055 := bstep (se 1 (by rfl) ⟨1657541, by rfl⟩ : syracuseStep 2210055 = 3315083) B3315083
theorem B2486317 : Blo 2209435 2486317 := bbase (se 3 (by rfl) ⟨466184, by rfl⟩ : syracuseStep 2486317 = 932369) (by norm_num)
theorem B3315089 : Blo 2209435 3315089 := bstep (se 2 (by rfl) ⟨1243158, by rfl⟩ : syracuseStep 3315089 = 2486317) B2486317
theorem B2210059 : Blo 2209435 2210059 := bstep (se 1 (by rfl) ⟨1657544, by rfl⟩ : syracuseStep 2210059 = 3315089) B3315089
theorem B7458965 : Blo 2209435 7458965 := bbase (se 6 (by rfl) ⟨174819, by rfl⟩ : syracuseStep 7458965 = 349639) (by norm_num)
theorem B4972643 : Blo 2209435 4972643 := bstep (se 1 (by rfl) ⟨3729482, by rfl⟩ : syracuseStep 4972643 = 7458965) B7458965
theorem B3315095 : Blo 2209435 3315095 := bstep (se 1 (by rfl) ⟨2486321, by rfl⟩ : syracuseStep 3315095 = 4972643) B4972643
theorem B2210063 : Blo 2209435 2210063 := bstep (se 1 (by rfl) ⟨1657547, by rfl⟩ : syracuseStep 2210063 = 3315095) B3315095
theorem B3315101 : Blo 2209435 3315101 := bbase (se 3 (by rfl) ⟨621581, by rfl⟩ : syracuseStep 3315101 = 1243163) (by norm_num)
theorem B2210067 : Blo 2209435 2210067 := bstep (se 1 (by rfl) ⟨1657550, by rfl⟩ : syracuseStep 2210067 = 3315101) B3315101
theorem B4972661 : Blo 2209435 4972661 := bbase (se 5 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 4972661 = 466187) (by norm_num)
theorem B3315107 : Blo 2209435 3315107 := bstep (se 1 (by rfl) ⟨2486330, by rfl⟩ : syracuseStep 3315107 = 4972661) B4972661
theorem B2210071 : Blo 2209435 2210071 := bstep (se 1 (by rfl) ⟨1657553, by rfl⟩ : syracuseStep 2210071 = 3315107) B3315107
theorem B5310173 : Blo 2209435 5310173 := bbase (se 3 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 5310173 = 1991315) (by norm_num)
theorem B3540115 : Blo 2209435 3540115 := bstep (se 1 (by rfl) ⟨2655086, by rfl⟩ : syracuseStep 3540115 = 5310173) B5310173
theorem B18880613 : Blo 2209435 18880613 := bstep (se 4 (by rfl) ⟨1770057, by rfl⟩ : syracuseStep 18880613 = 3540115) B3540115
theorem B12587075 : Blo 2209435 12587075 := bstep (se 1 (by rfl) ⟨9440306, by rfl⟩ : syracuseStep 12587075 = 18880613) B18880613
theorem B8391383 : Blo 2209435 8391383 := bstep (se 1 (by rfl) ⟨6293537, by rfl⟩ : syracuseStep 8391383 = 12587075) B12587075
theorem B5594255 : Blo 2209435 5594255 := bstep (se 1 (by rfl) ⟨4195691, by rfl⟩ : syracuseStep 5594255 = 8391383) B8391383
theorem B3729503 : Blo 2209435 3729503 := bstep (se 1 (by rfl) ⟨2797127, by rfl⟩ : syracuseStep 3729503 = 5594255) B5594255
theorem B2486335 : Blo 2209435 2486335 := bstep (se 1 (by rfl) ⟨1864751, by rfl⟩ : syracuseStep 2486335 = 3729503) B3729503
theorem B3315113 : Blo 2209435 3315113 := bstep (se 2 (by rfl) ⟨1243167, by rfl⟩ : syracuseStep 3315113 = 2486335) B2486335
theorem B2210075 : Blo 2209435 2210075 := bstep (se 1 (by rfl) ⟨1657556, by rfl⟩ : syracuseStep 2210075 = 3315113) B3315113
theorem B8391397 : Blo 2209435 8391397 := bbase (se 4 (by rfl) ⟨786693, by rfl⟩ : syracuseStep 8391397 = 1573387) (by norm_num)
theorem B11188529 : Blo 2209435 11188529 := bstep (se 2 (by rfl) ⟨4195698, by rfl⟩ : syracuseStep 11188529 = 8391397) B8391397
theorem B7459019 : Blo 2209435 7459019 := bstep (se 1 (by rfl) ⟨5594264, by rfl⟩ : syracuseStep 7459019 = 11188529) B11188529
theorem B4972679 : Blo 2209435 4972679 := bstep (se 1 (by rfl) ⟨3729509, by rfl⟩ : syracuseStep 4972679 = 7459019) B7459019
theorem B3315119 : Blo 2209435 3315119 := bstep (se 1 (by rfl) ⟨2486339, by rfl⟩ : syracuseStep 3315119 = 4972679) B4972679
theorem B2210079 : Blo 2209435 2210079 := bstep (se 1 (by rfl) ⟨1657559, by rfl⟩ : syracuseStep 2210079 = 3315119) B3315119
theorem B3315125 : Blo 2209435 3315125 := bbase (se 5 (by rfl) ⟨155396, by rfl⟩ : syracuseStep 3315125 = 310793) (by norm_num)
theorem B2210083 : Blo 2209435 2210083 := bstep (se 1 (by rfl) ⟨1657562, by rfl⟩ : syracuseStep 2210083 = 3315125) B3315125
theorem B5594285 : Blo 2209435 5594285 := bbase (se 3 (by rfl) ⟨1048928, by rfl⟩ : syracuseStep 5594285 = 2097857) (by norm_num)
theorem B3729523 : Blo 2209435 3729523 := bstep (se 1 (by rfl) ⟨2797142, by rfl⟩ : syracuseStep 3729523 = 5594285) B5594285
theorem B4972697 : Blo 2209435 4972697 := bstep (se 2 (by rfl) ⟨1864761, by rfl⟩ : syracuseStep 4972697 = 3729523) B3729523
theorem B3315131 : Blo 2209435 3315131 := bstep (se 1 (by rfl) ⟨2486348, by rfl⟩ : syracuseStep 3315131 = 4972697) B4972697
theorem B2210087 : Blo 2209435 2210087 := bstep (se 1 (by rfl) ⟨1657565, by rfl⟩ : syracuseStep 2210087 = 3315131) B3315131
theorem B2486353 : Blo 2209435 2486353 := bbase (se 2 (by rfl) ⟨932382, by rfl⟩ : syracuseStep 2486353 = 1864765) (by norm_num)
theorem B3315137 : Blo 2209435 3315137 := bstep (se 2 (by rfl) ⟨1243176, by rfl⟩ : syracuseStep 3315137 = 2486353) B2486353
theorem B2210091 : Blo 2209435 2210091 := bstep (se 1 (by rfl) ⟨1657568, by rfl⟩ : syracuseStep 2210091 = 3315137) B3315137
theorem B3146797 : Blo 2209435 3146797 := bbase (se 3 (by rfl) ⟨590024, by rfl⟩ : syracuseStep 3146797 = 1180049) (by norm_num)
theorem B4195729 : Blo 2209435 4195729 := bstep (se 2 (by rfl) ⟨1573398, by rfl⟩ : syracuseStep 4195729 = 3146797) B3146797
theorem B5594305 : Blo 2209435 5594305 := bstep (se 2 (by rfl) ⟨2097864, by rfl⟩ : syracuseStep 5594305 = 4195729) B4195729
theorem B7459073 : Blo 2209435 7459073 := bstep (se 2 (by rfl) ⟨2797152, by rfl⟩ : syracuseStep 7459073 = 5594305) B5594305
theorem B4972715 : Blo 2209435 4972715 := bstep (se 1 (by rfl) ⟨3729536, by rfl⟩ : syracuseStep 4972715 = 7459073) B7459073
theorem B3315143 : Blo 2209435 3315143 := bstep (se 1 (by rfl) ⟨2486357, by rfl⟩ : syracuseStep 3315143 = 4972715) B4972715
theorem B2210095 : Blo 2209435 2210095 := bstep (se 1 (by rfl) ⟨1657571, by rfl⟩ : syracuseStep 2210095 = 3315143) B3315143
theorem B3315149 : Blo 2209435 3315149 := bbase (se 3 (by rfl) ⟨621590, by rfl⟩ : syracuseStep 3315149 = 1243181) (by norm_num)
theorem B2210099 : Blo 2209435 2210099 := bstep (se 1 (by rfl) ⟨1657574, by rfl⟩ : syracuseStep 2210099 = 3315149) B3315149
theorem B4972733 : Blo 2209435 4972733 := bbase (se 3 (by rfl) ⟨932387, by rfl⟩ : syracuseStep 4972733 = 1864775) (by norm_num)
theorem B3315155 : Blo 2209435 3315155 := bstep (se 1 (by rfl) ⟨2486366, by rfl⟩ : syracuseStep 3315155 = 4972733) B4972733
theorem B2210103 : Blo 2209435 2210103 := bstep (se 1 (by rfl) ⟨1657577, by rfl⟩ : syracuseStep 2210103 = 3315155) B3315155
theorem B3729557 : Blo 2209435 3729557 := bbase (se 6 (by rfl) ⟨87411, by rfl⟩ : syracuseStep 3729557 = 174823) (by norm_num)
theorem B2486371 : Blo 2209435 2486371 := bstep (se 1 (by rfl) ⟨1864778, by rfl⟩ : syracuseStep 2486371 = 3729557) B3729557
theorem B3315161 : Blo 2209435 3315161 := bstep (se 2 (by rfl) ⟨1243185, by rfl⟩ : syracuseStep 3315161 = 2486371) B2486371
theorem B2210107 : Blo 2209435 2210107 := bstep (se 1 (by rfl) ⟨1657580, by rfl⟩ : syracuseStep 2210107 = 3315161) B3315161
theorem B10620517 : Blo 2209435 10620517 := bbase (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) (by norm_num)
theorem B14160689 : Blo 2209435 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B9440459 : Blo 2209435 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B6293639 : Blo 2209435 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B16783037 : Blo 2209435 16783037 := bstep (se 3 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 16783037 = 6293639) B6293639
theorem B11188691 : Blo 2209435 11188691 := bstep (se 1 (by rfl) ⟨8391518, by rfl⟩ : syracuseStep 11188691 = 16783037) B16783037
theorem B7459127 : Blo 2209435 7459127 := bstep (se 1 (by rfl) ⟨5594345, by rfl⟩ : syracuseStep 7459127 = 11188691) B11188691
theorem B4972751 : Blo 2209435 4972751 := bstep (se 1 (by rfl) ⟨3729563, by rfl⟩ : syracuseStep 4972751 = 7459127) B7459127
theorem B3315167 : Blo 2209435 3315167 := bstep (se 1 (by rfl) ⟨2486375, by rfl⟩ : syracuseStep 3315167 = 4972751) B4972751
theorem B2210111 : Blo 2209435 2210111 := bstep (se 1 (by rfl) ⟨1657583, by rfl⟩ : syracuseStep 2210111 = 3315167) B3315167
theorem B3315173 : Blo 2209435 3315173 := bbase (se 4 (by rfl) ⟨310797, by rfl⟩ : syracuseStep 3315173 = 621595) (by norm_num)
theorem B2210115 : Blo 2209435 2210115 := bstep (se 1 (by rfl) ⟨1657586, by rfl⟩ : syracuseStep 2210115 = 3315173) B3315173
theorem B5748061 : Blo 2209435 5748061 := bbase (se 3 (by rfl) ⟨1077761, by rfl⟩ : syracuseStep 5748061 = 2155523) (by norm_num)
theorem B7664081 : Blo 2209435 7664081 := bstep (se 2 (by rfl) ⟨2874030, by rfl⟩ : syracuseStep 7664081 = 5748061) B5748061
theorem B81750197 : Blo 2209435 81750197 := bstep (se 5 (by rfl) ⟨3832040, by rfl⟩ : syracuseStep 81750197 = 7664081) B7664081
theorem B54500131 : Blo 2209435 54500131 := bstep (se 1 (by rfl) ⟨40875098, by rfl⟩ : syracuseStep 54500131 = 81750197) B81750197
theorem B72666841 : Blo 2209435 72666841 := bstep (se 2 (by rfl) ⟨27250065, by rfl⟩ : syracuseStep 72666841 = 54500131) B54500131
theorem B96889121 : Blo 2209435 96889121 := bstep (se 2 (by rfl) ⟨36333420, by rfl⟩ : syracuseStep 96889121 = 72666841) B72666841
theorem B64592747 : Blo 2209435 64592747 := bstep (se 1 (by rfl) ⟨48444560, by rfl⟩ : syracuseStep 64592747 = 96889121) B96889121
theorem B43061831 : Blo 2209435 43061831 := bstep (se 1 (by rfl) ⟨32296373, by rfl⟩ : syracuseStep 43061831 = 64592747) B64592747
theorem B28707887 : Blo 2209435 28707887 := bstep (se 1 (by rfl) ⟨21530915, by rfl⟩ : syracuseStep 28707887 = 43061831) B43061831
theorem B19138591 : Blo 2209435 19138591 := bstep (se 1 (by rfl) ⟨14353943, by rfl⟩ : syracuseStep 19138591 = 28707887) B28707887
theorem B25518121 : Blo 2209435 25518121 := bstep (se 2 (by rfl) ⟨9569295, by rfl⟩ : syracuseStep 25518121 = 19138591) B19138591
theorem B136096645 : Blo 2209435 136096645 := bstep (se 4 (by rfl) ⟨12759060, by rfl⟩ : syracuseStep 136096645 = 25518121) B25518121
theorem B181462193 : Blo 2209435 181462193 := bstep (se 2 (by rfl) ⟨68048322, by rfl⟩ : syracuseStep 181462193 = 136096645) B136096645
theorem B120974795 : Blo 2209435 120974795 := bstep (se 1 (by rfl) ⟨90731096, by rfl⟩ : syracuseStep 120974795 = 181462193) B181462193
theorem B80649863 : Blo 2209435 80649863 := bstep (se 1 (by rfl) ⟨60487397, by rfl⟩ : syracuseStep 80649863 = 120974795) B120974795
theorem B53766575 : Blo 2209435 53766575 := bstep (se 1 (by rfl) ⟨40324931, by rfl⟩ : syracuseStep 53766575 = 80649863) B80649863
theorem B35844383 : Blo 2209435 35844383 := bstep (se 1 (by rfl) ⟨26883287, by rfl⟩ : syracuseStep 35844383 = 53766575) B53766575
theorem B23896255 : Blo 2209435 23896255 := bstep (se 1 (by rfl) ⟨17922191, by rfl⟩ : syracuseStep 23896255 = 35844383) B35844383
theorem B31861673 : Blo 2209435 31861673 := bstep (se 2 (by rfl) ⟨11948127, by rfl⟩ : syracuseStep 31861673 = 23896255) B23896255
theorem B21241115 : Blo 2209435 21241115 := bstep (se 1 (by rfl) ⟨15930836, by rfl⟩ : syracuseStep 21241115 = 31861673) B31861673
theorem B14160743 : Blo 2209435 14160743 := bstep (se 1 (by rfl) ⟨10620557, by rfl⟩ : syracuseStep 14160743 = 21241115) B21241115
theorem B9440495 : Blo 2209435 9440495 := bstep (se 1 (by rfl) ⟨7080371, by rfl⟩ : syracuseStep 9440495 = 14160743) B14160743
theorem B6293663 : Blo 2209435 6293663 := bstep (se 1 (by rfl) ⟨4720247, by rfl⟩ : syracuseStep 6293663 = 9440495) B9440495
theorem B4195775 : Blo 2209435 4195775 := bstep (se 1 (by rfl) ⟨3146831, by rfl⟩ : syracuseStep 4195775 = 6293663) B6293663
theorem B2797183 : Blo 2209435 2797183 := bstep (se 1 (by rfl) ⟨2097887, by rfl⟩ : syracuseStep 2797183 = 4195775) B4195775
theorem B3729577 : Blo 2209435 3729577 := bstep (se 2 (by rfl) ⟨1398591, by rfl⟩ : syracuseStep 3729577 = 2797183) B2797183
theorem B4972769 : Blo 2209435 4972769 := bstep (se 2 (by rfl) ⟨1864788, by rfl⟩ : syracuseStep 4972769 = 3729577) B3729577
theorem B3315179 : Blo 2209435 3315179 := bstep (se 1 (by rfl) ⟨2486384, by rfl⟩ : syracuseStep 3315179 = 4972769) B4972769
theorem B2210119 : Blo 2209435 2210119 := bstep (se 1 (by rfl) ⟨1657589, by rfl⟩ : syracuseStep 2210119 = 3315179) B3315179
theorem B2486389 : Blo 2209435 2486389 := bbase (se 5 (by rfl) ⟨116549, by rfl⟩ : syracuseStep 2486389 = 233099) (by norm_num)
theorem B3315185 : Blo 2209435 3315185 := bstep (se 2 (by rfl) ⟨1243194, by rfl⟩ : syracuseStep 3315185 = 2486389) B2486389
theorem B2210123 : Blo 2209435 2210123 := bstep (se 1 (by rfl) ⟨1657592, by rfl⟩ : syracuseStep 2210123 = 3315185) B3315185
theorem B2797193 : Blo 2209435 2797193 := bbase (se 2 (by rfl) ⟨1048947, by rfl⟩ : syracuseStep 2797193 = 2097895) (by norm_num)
theorem B7459181 : Blo 2209435 7459181 := bstep (se 3 (by rfl) ⟨1398596, by rfl⟩ : syracuseStep 7459181 = 2797193) B2797193
theorem B4972787 : Blo 2209435 4972787 := bstep (se 1 (by rfl) ⟨3729590, by rfl⟩ : syracuseStep 4972787 = 7459181) B7459181
theorem B3315191 : Blo 2209435 3315191 := bstep (se 1 (by rfl) ⟨2486393, by rfl⟩ : syracuseStep 3315191 = 4972787) B4972787
theorem B2210127 : Blo 2209435 2210127 := bstep (se 1 (by rfl) ⟨1657595, by rfl⟩ : syracuseStep 2210127 = 3315191) B3315191
theorem B3315197 : Blo 2209435 3315197 := bbase (se 3 (by rfl) ⟨621599, by rfl⟩ : syracuseStep 3315197 = 1243199) (by norm_num)
theorem B2210131 : Blo 2209435 2210131 := bstep (se 1 (by rfl) ⟨1657598, by rfl⟩ : syracuseStep 2210131 = 3315197) B3315197
theorem B4972805 : Blo 2209435 4972805 := bbase (se 4 (by rfl) ⟨466200, by rfl⟩ : syracuseStep 4972805 = 932401) (by norm_num)
theorem B3315203 : Blo 2209435 3315203 := bstep (se 1 (by rfl) ⟨2486402, by rfl⟩ : syracuseStep 3315203 = 4972805) B4972805
theorem B2210135 : Blo 2209435 2210135 := bstep (se 1 (by rfl) ⟨1657601, by rfl⟩ : syracuseStep 2210135 = 3315203) B3315203
theorem B4195813 : Blo 2209435 4195813 := bbase (se 4 (by rfl) ⟨393357, by rfl⟩ : syracuseStep 4195813 = 786715) (by norm_num)
theorem B5594417 : Blo 2209435 5594417 := bstep (se 2 (by rfl) ⟨2097906, by rfl⟩ : syracuseStep 5594417 = 4195813) B4195813
theorem B3729611 : Blo 2209435 3729611 := bstep (se 1 (by rfl) ⟨2797208, by rfl⟩ : syracuseStep 3729611 = 5594417) B5594417
theorem B2486407 : Blo 2209435 2486407 := bstep (se 1 (by rfl) ⟨1864805, by rfl⟩ : syracuseStep 2486407 = 3729611) B3729611
theorem B3315209 : Blo 2209435 3315209 := bstep (se 2 (by rfl) ⟨1243203, by rfl⟩ : syracuseStep 3315209 = 2486407) B2486407
theorem B2210139 : Blo 2209435 2210139 := bstep (se 1 (by rfl) ⟨1657604, by rfl⟩ : syracuseStep 2210139 = 3315209) B3315209
theorem B11188853 : Blo 2209435 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B7459235 : Blo 2209435 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4972823 : Blo 2209435 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B3315215 : Blo 2209435 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B2210143 : Blo 2209435 2210143 := bstep (se 1 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 2210143 = 3315215) B3315215
theorem B3315221 : Blo 2209435 3315221 := bbase (se 6 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 3315221 = 155401) (by norm_num)
theorem B2210147 : Blo 2209435 2210147 := bstep (se 1 (by rfl) ⟨1657610, by rfl⟩ : syracuseStep 2210147 = 3315221) B3315221
theorem B4480613 : Blo 2209435 4480613 := bbase (se 4 (by rfl) ⟨420057, by rfl⟩ : syracuseStep 4480613 = 840115) (by norm_num)
theorem B2987075 : Blo 2209435 2987075 := bstep (se 1 (by rfl) ⟨2240306, by rfl⟩ : syracuseStep 2987075 = 4480613) B4480613
theorem B7965533 : Blo 2209435 7965533 := bstep (se 3 (by rfl) ⟨1493537, by rfl⟩ : syracuseStep 7965533 = 2987075) B2987075
theorem B5310355 : Blo 2209435 5310355 := bstep (se 1 (by rfl) ⟨3982766, by rfl⟩ : syracuseStep 5310355 = 7965533) B7965533
theorem B7080473 : Blo 2209435 7080473 := bstep (se 2 (by rfl) ⟨2655177, by rfl⟩ : syracuseStep 7080473 = 5310355) B5310355
theorem B18881261 : Blo 2209435 18881261 := bstep (se 3 (by rfl) ⟨3540236, by rfl⟩ : syracuseStep 18881261 = 7080473) B7080473
theorem B12587507 : Blo 2209435 12587507 := bstep (se 1 (by rfl) ⟨9440630, by rfl⟩ : syracuseStep 12587507 = 18881261) B18881261
theorem B8391671 : Blo 2209435 8391671 := bstep (se 1 (by rfl) ⟨6293753, by rfl⟩ : syracuseStep 8391671 = 12587507) B12587507
theorem B5594447 : Blo 2209435 5594447 := bstep (se 1 (by rfl) ⟨4195835, by rfl⟩ : syracuseStep 5594447 = 8391671) B8391671
theorem B3729631 : Blo 2209435 3729631 := bstep (se 1 (by rfl) ⟨2797223, by rfl⟩ : syracuseStep 3729631 = 5594447) B5594447
theorem B4972841 : Blo 2209435 4972841 := bstep (se 2 (by rfl) ⟨1864815, by rfl⟩ : syracuseStep 4972841 = 3729631) B3729631
theorem B3315227 : Blo 2209435 3315227 := bstep (se 1 (by rfl) ⟨2486420, by rfl⟩ : syracuseStep 3315227 = 4972841) B4972841
theorem B2210151 : Blo 2209435 2210151 := bstep (se 1 (by rfl) ⟨1657613, by rfl⟩ : syracuseStep 2210151 = 3315227) B3315227
theorem B2486425 : Blo 2209435 2486425 := bbase (se 2 (by rfl) ⟨932409, by rfl⟩ : syracuseStep 2486425 = 1864819) (by norm_num)
theorem B3315233 : Blo 2209435 3315233 := bstep (se 2 (by rfl) ⟨1243212, by rfl⟩ : syracuseStep 3315233 = 2486425) B2486425
theorem B2210155 : Blo 2209435 2210155 := bstep (se 1 (by rfl) ⟨1657616, by rfl⟩ : syracuseStep 2210155 = 3315233) B3315233
theorem B8391701 : Blo 2209435 8391701 := bbase (se 6 (by rfl) ⟨196680, by rfl⟩ : syracuseStep 8391701 = 393361) (by norm_num)
theorem B5594467 : Blo 2209435 5594467 := bstep (se 1 (by rfl) ⟨4195850, by rfl⟩ : syracuseStep 5594467 = 8391701) B8391701
theorem B7459289 : Blo 2209435 7459289 := bstep (se 2 (by rfl) ⟨2797233, by rfl⟩ : syracuseStep 7459289 = 5594467) B5594467
theorem B4972859 : Blo 2209435 4972859 := bstep (se 1 (by rfl) ⟨3729644, by rfl⟩ : syracuseStep 4972859 = 7459289) B7459289
theorem B3315239 : Blo 2209435 3315239 := bstep (se 1 (by rfl) ⟨2486429, by rfl⟩ : syracuseStep 3315239 = 4972859) B4972859
theorem B2210159 : Blo 2209435 2210159 := bstep (se 1 (by rfl) ⟨1657619, by rfl⟩ : syracuseStep 2210159 = 3315239) B3315239
theorem B3315245 : Blo 2209435 3315245 := bbase (se 3 (by rfl) ⟨621608, by rfl⟩ : syracuseStep 3315245 = 1243217) (by norm_num)
theorem B2210163 : Blo 2209435 2210163 := bstep (se 1 (by rfl) ⟨1657622, by rfl⟩ : syracuseStep 2210163 = 3315245) B3315245
theorem B4972877 : Blo 2209435 4972877 := bbase (se 3 (by rfl) ⟨932414, by rfl⟩ : syracuseStep 4972877 = 1864829) (by norm_num)
theorem B3315251 : Blo 2209435 3315251 := bstep (se 1 (by rfl) ⟨2486438, by rfl⟩ : syracuseStep 3315251 = 4972877) B4972877
theorem B2210167 : Blo 2209435 2210167 := bstep (se 1 (by rfl) ⟨1657625, by rfl⟩ : syracuseStep 2210167 = 3315251) B3315251
theorem B2797249 : Blo 2209435 2797249 := bbase (se 2 (by rfl) ⟨1048968, by rfl⟩ : syracuseStep 2797249 = 2097937) (by norm_num)
theorem B3729665 : Blo 2209435 3729665 := bstep (se 2 (by rfl) ⟨1398624, by rfl⟩ : syracuseStep 3729665 = 2797249) B2797249
theorem B2486443 : Blo 2209435 2486443 := bstep (se 1 (by rfl) ⟨1864832, by rfl⟩ : syracuseStep 2486443 = 3729665) B3729665
theorem B3315257 : Blo 2209435 3315257 := bstep (se 2 (by rfl) ⟨1243221, by rfl⟩ : syracuseStep 3315257 = 2486443) B2486443
theorem B2210171 : Blo 2209435 2210171 := bstep (se 1 (by rfl) ⟨1657628, by rfl⟩ : syracuseStep 2210171 = 3315257) B3315257
theorem B5310413 : Blo 2209435 5310413 := bbase (se 3 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 5310413 = 1991405) (by norm_num)
theorem B3540275 : Blo 2209435 3540275 := bstep (se 1 (by rfl) ⟨2655206, by rfl⟩ : syracuseStep 3540275 = 5310413) B5310413
theorem B2360183 : Blo 2209435 2360183 := bstep (se 1 (by rfl) ⟨1770137, by rfl⟩ : syracuseStep 2360183 = 3540275) B3540275
theorem B25175285 : Blo 2209435 25175285 := bstep (se 5 (by rfl) ⟨1180091, by rfl⟩ : syracuseStep 25175285 = 2360183) B2360183
theorem B16783523 : Blo 2209435 16783523 := bstep (se 1 (by rfl) ⟨12587642, by rfl⟩ : syracuseStep 16783523 = 25175285) B25175285
theorem B11189015 : Blo 2209435 11189015 := bstep (se 1 (by rfl) ⟨8391761, by rfl⟩ : syracuseStep 11189015 = 16783523) B16783523
theorem B7459343 : Blo 2209435 7459343 := bstep (se 1 (by rfl) ⟨5594507, by rfl⟩ : syracuseStep 7459343 = 11189015) B11189015
theorem B4972895 : Blo 2209435 4972895 := bstep (se 1 (by rfl) ⟨3729671, by rfl⟩ : syracuseStep 4972895 = 7459343) B7459343
theorem B3315263 : Blo 2209435 3315263 := bstep (se 1 (by rfl) ⟨2486447, by rfl⟩ : syracuseStep 3315263 = 4972895) B4972895
theorem B2210175 : Blo 2209435 2210175 := bstep (se 1 (by rfl) ⟨1657631, by rfl⟩ : syracuseStep 2210175 = 3315263) B3315263
theorem B3315269 : Blo 2209435 3315269 := bbase (se 4 (by rfl) ⟨310806, by rfl⟩ : syracuseStep 3315269 = 621613) (by norm_num)
theorem B2210179 : Blo 2209435 2210179 := bstep (se 1 (by rfl) ⟨1657634, by rfl⟩ : syracuseStep 2210179 = 3315269) B3315269
theorem B3729685 : Blo 2209435 3729685 := bbase (se 6 (by rfl) ⟨87414, by rfl⟩ : syracuseStep 3729685 = 174829) (by norm_num)
theorem B4972913 : Blo 2209435 4972913 := bstep (se 2 (by rfl) ⟨1864842, by rfl⟩ : syracuseStep 4972913 = 3729685) B3729685
theorem B3315275 : Blo 2209435 3315275 := bstep (se 1 (by rfl) ⟨2486456, by rfl⟩ : syracuseStep 3315275 = 4972913) B4972913
theorem B2210183 : Blo 2209435 2210183 := bstep (se 1 (by rfl) ⟨1657637, by rfl⟩ : syracuseStep 2210183 = 3315275) B3315275
theorem B2486461 : Blo 2209435 2486461 := bbase (se 3 (by rfl) ⟨466211, by rfl⟩ : syracuseStep 2486461 = 932423) (by norm_num)
theorem B3315281 : Blo 2209435 3315281 := bstep (se 2 (by rfl) ⟨1243230, by rfl⟩ : syracuseStep 3315281 = 2486461) B2486461
theorem B2210187 : Blo 2209435 2210187 := bstep (se 1 (by rfl) ⟨1657640, by rfl⟩ : syracuseStep 2210187 = 3315281) B3315281
theorem B7459397 : Blo 2209435 7459397 := bbase (se 4 (by rfl) ⟨699318, by rfl⟩ : syracuseStep 7459397 = 1398637) (by norm_num)
theorem B4972931 : Blo 2209435 4972931 := bstep (se 1 (by rfl) ⟨3729698, by rfl⟩ : syracuseStep 4972931 = 7459397) B7459397
theorem B3315287 : Blo 2209435 3315287 := bstep (se 1 (by rfl) ⟨2486465, by rfl⟩ : syracuseStep 3315287 = 4972931) B4972931
theorem B2210191 : Blo 2209435 2210191 := bstep (se 1 (by rfl) ⟨1657643, by rfl⟩ : syracuseStep 2210191 = 3315287) B3315287
theorem B3315293 : Blo 2209435 3315293 := bbase (se 3 (by rfl) ⟨621617, by rfl⟩ : syracuseStep 3315293 = 1243235) (by norm_num)
theorem B2210195 : Blo 2209435 2210195 := bstep (se 1 (by rfl) ⟨1657646, by rfl⟩ : syracuseStep 2210195 = 3315293) B3315293
theorem B4972949 : Blo 2209435 4972949 := bbase (se 6 (by rfl) ⟨116553, by rfl⟩ : syracuseStep 4972949 = 233107) (by norm_num)
theorem B3315299 : Blo 2209435 3315299 := bstep (se 1 (by rfl) ⟨2486474, by rfl⟩ : syracuseStep 3315299 = 4972949) B4972949
theorem B2210199 : Blo 2209435 2210199 := bstep (se 1 (by rfl) ⟨1657649, by rfl⟩ : syracuseStep 2210199 = 3315299) B3315299
theorem B3982861 : Blo 2209435 3982861 := bbase (se 3 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 3982861 = 1493573) (by norm_num)
theorem B5310481 : Blo 2209435 5310481 := bstep (se 2 (by rfl) ⟨1991430, by rfl⟩ : syracuseStep 5310481 = 3982861) B3982861
theorem B7080641 : Blo 2209435 7080641 := bstep (se 2 (by rfl) ⟨2655240, by rfl⟩ : syracuseStep 7080641 = 5310481) B5310481
theorem B4720427 : Blo 2209435 4720427 := bstep (se 1 (by rfl) ⟨3540320, by rfl⟩ : syracuseStep 4720427 = 7080641) B7080641
theorem B3146951 : Blo 2209435 3146951 := bstep (se 1 (by rfl) ⟨2360213, by rfl⟩ : syracuseStep 3146951 = 4720427) B4720427
theorem B8391869 : Blo 2209435 8391869 := bstep (se 3 (by rfl) ⟨1573475, by rfl⟩ : syracuseStep 8391869 = 3146951) B3146951
theorem B5594579 : Blo 2209435 5594579 := bstep (se 1 (by rfl) ⟨4195934, by rfl⟩ : syracuseStep 5594579 = 8391869) B8391869
theorem B3729719 : Blo 2209435 3729719 := bstep (se 1 (by rfl) ⟨2797289, by rfl⟩ : syracuseStep 3729719 = 5594579) B5594579
theorem B2486479 : Blo 2209435 2486479 := bstep (se 1 (by rfl) ⟨1864859, by rfl⟩ : syracuseStep 2486479 = 3729719) B3729719
theorem B3315305 : Blo 2209435 3315305 := bstep (se 2 (by rfl) ⟨1243239, by rfl⟩ : syracuseStep 3315305 = 2486479) B2486479
theorem B2210203 : Blo 2209435 2210203 := bstep (se 1 (by rfl) ⟨1657652, by rfl⟩ : syracuseStep 2210203 = 3315305) B3315305
theorem B9440869 : Blo 2209435 9440869 := bbase (se 4 (by rfl) ⟨885081, by rfl⟩ : syracuseStep 9440869 = 1770163) (by norm_num)
theorem B12587825 : Blo 2209435 12587825 := bstep (se 2 (by rfl) ⟨4720434, by rfl⟩ : syracuseStep 12587825 = 9440869) B9440869
theorem B8391883 : Blo 2209435 8391883 := bstep (se 1 (by rfl) ⟨6293912, by rfl⟩ : syracuseStep 8391883 = 12587825) B12587825
theorem B11189177 : Blo 2209435 11189177 := bstep (se 2 (by rfl) ⟨4195941, by rfl⟩ : syracuseStep 11189177 = 8391883) B8391883
theorem B7459451 : Blo 2209435 7459451 := bstep (se 1 (by rfl) ⟨5594588, by rfl⟩ : syracuseStep 7459451 = 11189177) B11189177
theorem B4972967 : Blo 2209435 4972967 := bstep (se 1 (by rfl) ⟨3729725, by rfl⟩ : syracuseStep 4972967 = 7459451) B7459451
theorem B3315311 : Blo 2209435 3315311 := bstep (se 1 (by rfl) ⟨2486483, by rfl⟩ : syracuseStep 3315311 = 4972967) B4972967
theorem B2210207 : Blo 2209435 2210207 := bstep (se 1 (by rfl) ⟨1657655, by rfl⟩ : syracuseStep 2210207 = 3315311) B3315311
theorem B3315317 : Blo 2209435 3315317 := bbase (se 5 (by rfl) ⟨155405, by rfl⟩ : syracuseStep 3315317 = 310811) (by norm_num)
theorem B2210211 : Blo 2209435 2210211 := bstep (se 1 (by rfl) ⟨1657658, by rfl⟩ : syracuseStep 2210211 = 3315317) B3315317
theorem B4195957 : Blo 2209435 4195957 := bbase (se 5 (by rfl) ⟨196685, by rfl⟩ : syracuseStep 4195957 = 393371) (by norm_num)
theorem B5594609 : Blo 2209435 5594609 := bstep (se 2 (by rfl) ⟨2097978, by rfl⟩ : syracuseStep 5594609 = 4195957) B4195957
theorem B3729739 : Blo 2209435 3729739 := bstep (se 1 (by rfl) ⟨2797304, by rfl⟩ : syracuseStep 3729739 = 5594609) B5594609
theorem B4972985 : Blo 2209435 4972985 := bstep (se 2 (by rfl) ⟨1864869, by rfl⟩ : syracuseStep 4972985 = 3729739) B3729739
theorem B3315323 : Blo 2209435 3315323 := bstep (se 1 (by rfl) ⟨2486492, by rfl⟩ : syracuseStep 3315323 = 4972985) B4972985
theorem B2210215 : Blo 2209435 2210215 := bstep (se 1 (by rfl) ⟨1657661, by rfl⟩ : syracuseStep 2210215 = 3315323) B3315323
theorem B2486497 : Blo 2209435 2486497 := bbase (se 2 (by rfl) ⟨932436, by rfl⟩ : syracuseStep 2486497 = 1864873) (by norm_num)
theorem B3315329 : Blo 2209435 3315329 := bstep (se 2 (by rfl) ⟨1243248, by rfl⟩ : syracuseStep 3315329 = 2486497) B2486497
theorem B2210219 : Blo 2209435 2210219 := bstep (se 1 (by rfl) ⟨1657664, by rfl⟩ : syracuseStep 2210219 = 3315329) B3315329
theorem B5594629 : Blo 2209435 5594629 := bbase (se 4 (by rfl) ⟨524496, by rfl⟩ : syracuseStep 5594629 = 1048993) (by norm_num)
theorem B7459505 : Blo 2209435 7459505 := bstep (se 2 (by rfl) ⟨2797314, by rfl⟩ : syracuseStep 7459505 = 5594629) B5594629
theorem B4973003 : Blo 2209435 4973003 := bstep (se 1 (by rfl) ⟨3729752, by rfl⟩ : syracuseStep 4973003 = 7459505) B7459505
theorem B3315335 : Blo 2209435 3315335 := bstep (se 1 (by rfl) ⟨2486501, by rfl⟩ : syracuseStep 3315335 = 4973003) B4973003
theorem B2210223 : Blo 2209435 2210223 := bstep (se 1 (by rfl) ⟨1657667, by rfl⟩ : syracuseStep 2210223 = 3315335) B3315335
theorem B3315341 : Blo 2209435 3315341 := bbase (se 3 (by rfl) ⟨621626, by rfl⟩ : syracuseStep 3315341 = 1243253) (by norm_num)
theorem B2210227 : Blo 2209435 2210227 := bstep (se 1 (by rfl) ⟨1657670, by rfl⟩ : syracuseStep 2210227 = 3315341) B3315341
theorem B4973021 : Blo 2209435 4973021 := bbase (se 3 (by rfl) ⟨932441, by rfl⟩ : syracuseStep 4973021 = 1864883) (by norm_num)
theorem B3315347 : Blo 2209435 3315347 := bstep (se 1 (by rfl) ⟨2486510, by rfl⟩ : syracuseStep 3315347 = 4973021) B4973021
theorem B2210231 : Blo 2209435 2210231 := bstep (se 1 (by rfl) ⟨1657673, by rfl⟩ : syracuseStep 2210231 = 3315347) B3315347
theorem B3729773 : Blo 2209435 3729773 := bbase (se 3 (by rfl) ⟨699332, by rfl⟩ : syracuseStep 3729773 = 1398665) (by norm_num)
theorem B2486515 : Blo 2209435 2486515 := bstep (se 1 (by rfl) ⟨1864886, by rfl⟩ : syracuseStep 2486515 = 3729773) B3729773
theorem B3315353 : Blo 2209435 3315353 := bstep (se 2 (by rfl) ⟨1243257, by rfl⟩ : syracuseStep 3315353 = 2486515) B2486515
theorem B2210235 : Blo 2209435 2210235 := bstep (se 1 (by rfl) ⟨1657676, by rfl⟩ : syracuseStep 2210235 = 3315353) B3315353
theorem B2520445 : Blo 2209435 2520445 := bbase (se 3 (by rfl) ⟨472583, by rfl⟩ : syracuseStep 2520445 = 945167) (by norm_num)
theorem B3360593 : Blo 2209435 3360593 := bstep (se 2 (by rfl) ⟨1260222, by rfl⟩ : syracuseStep 3360593 = 2520445) B2520445
theorem B2240395 : Blo 2209435 2240395 := bstep (se 1 (by rfl) ⟨1680296, by rfl⟩ : syracuseStep 2240395 = 3360593) B3360593
theorem B47795093 : Blo 2209435 47795093 := bstep (se 6 (by rfl) ⟨1120197, by rfl⟩ : syracuseStep 47795093 = 2240395) B2240395
theorem B31863395 : Blo 2209435 31863395 := bstep (se 1 (by rfl) ⟨23897546, by rfl⟩ : syracuseStep 31863395 = 47795093) B47795093
theorem B21242263 : Blo 2209435 21242263 := bstep (se 1 (by rfl) ⟨15931697, by rfl⟩ : syracuseStep 21242263 = 31863395) B31863395
theorem B28323017 : Blo 2209435 28323017 := bstep (se 2 (by rfl) ⟨10621131, by rfl⟩ : syracuseStep 28323017 = 21242263) B21242263
theorem B18882011 : Blo 2209435 18882011 := bstep (se 1 (by rfl) ⟨14161508, by rfl⟩ : syracuseStep 18882011 = 28323017) B28323017
theorem B12588007 : Blo 2209435 12588007 := bstep (se 1 (by rfl) ⟨9441005, by rfl⟩ : syracuseStep 12588007 = 18882011) B18882011
theorem B16784009 : Blo 2209435 16784009 := bstep (se 2 (by rfl) ⟨6294003, by rfl⟩ : syracuseStep 16784009 = 12588007) B12588007
theorem B11189339 : Blo 2209435 11189339 := bstep (se 1 (by rfl) ⟨8392004, by rfl⟩ : syracuseStep 11189339 = 16784009) B16784009
theorem B7459559 : Blo 2209435 7459559 := bstep (se 1 (by rfl) ⟨5594669, by rfl⟩ : syracuseStep 7459559 = 11189339) B11189339
theorem B4973039 : Blo 2209435 4973039 := bstep (se 1 (by rfl) ⟨3729779, by rfl⟩ : syracuseStep 4973039 = 7459559) B7459559
theorem B3315359 : Blo 2209435 3315359 := bstep (se 1 (by rfl) ⟨2486519, by rfl⟩ : syracuseStep 3315359 = 4973039) B4973039
theorem B2210239 : Blo 2209435 2210239 := bstep (se 1 (by rfl) ⟨1657679, by rfl⟩ : syracuseStep 2210239 = 3315359) B3315359
theorem B3315365 : Blo 2209435 3315365 := bbase (se 4 (by rfl) ⟨310815, by rfl⟩ : syracuseStep 3315365 = 621631) (by norm_num)
theorem B2210243 : Blo 2209435 2210243 := bstep (se 1 (by rfl) ⟨1657682, by rfl⟩ : syracuseStep 2210243 = 3315365) B3315365
theorem B2797345 : Blo 2209435 2797345 := bbase (se 2 (by rfl) ⟨1049004, by rfl⟩ : syracuseStep 2797345 = 2098009) (by norm_num)
theorem B3729793 : Blo 2209435 3729793 := bstep (se 2 (by rfl) ⟨1398672, by rfl⟩ : syracuseStep 3729793 = 2797345) B2797345
theorem B4973057 : Blo 2209435 4973057 := bstep (se 2 (by rfl) ⟨1864896, by rfl⟩ : syracuseStep 4973057 = 3729793) B3729793
theorem B3315371 : Blo 2209435 3315371 := bstep (se 1 (by rfl) ⟨2486528, by rfl⟩ : syracuseStep 3315371 = 4973057) B4973057
theorem B2210247 : Blo 2209435 2210247 := bstep (se 1 (by rfl) ⟨1657685, by rfl⟩ : syracuseStep 2210247 = 3315371) B3315371
theorem B2486533 : Blo 2209435 2486533 := bbase (se 4 (by rfl) ⟨233112, by rfl⟩ : syracuseStep 2486533 = 466225) (by norm_num)
theorem B3315377 : Blo 2209435 3315377 := bstep (se 2 (by rfl) ⟨1243266, by rfl⟩ : syracuseStep 3315377 = 2486533) B2486533
theorem B2210251 : Blo 2209435 2210251 := bstep (se 1 (by rfl) ⟨1657688, by rfl⟩ : syracuseStep 2210251 = 3315377) B3315377
theorem B2360269 : Blo 2209435 2360269 := bbase (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) (by norm_num)
theorem B3147025 : Blo 2209435 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B4196033 : Blo 2209435 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B2797355 : Blo 2209435 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B7459613 : Blo 2209435 7459613 := bstep (se 3 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 7459613 = 2797355) B2797355
theorem B4973075 : Blo 2209435 4973075 := bstep (se 1 (by rfl) ⟨3729806, by rfl⟩ : syracuseStep 4973075 = 7459613) B7459613
theorem B3315383 : Blo 2209435 3315383 := bstep (se 1 (by rfl) ⟨2486537, by rfl⟩ : syracuseStep 3315383 = 4973075) B4973075
theorem B2210255 : Blo 2209435 2210255 := bstep (se 1 (by rfl) ⟨1657691, by rfl⟩ : syracuseStep 2210255 = 3315383) B3315383
theorem B3315389 : Blo 2209435 3315389 := bbase (se 3 (by rfl) ⟨621635, by rfl⟩ : syracuseStep 3315389 = 1243271) (by norm_num)
theorem B2210259 : Blo 2209435 2210259 := bstep (se 1 (by rfl) ⟨1657694, by rfl⟩ : syracuseStep 2210259 = 3315389) B3315389
theorem B4973093 : Blo 2209435 4973093 := bbase (se 4 (by rfl) ⟨466227, by rfl⟩ : syracuseStep 4973093 = 932455) (by norm_num)
theorem B3315395 : Blo 2209435 3315395 := bstep (se 1 (by rfl) ⟨2486546, by rfl⟩ : syracuseStep 3315395 = 4973093) B4973093
theorem B2210263 : Blo 2209435 2210263 := bstep (se 1 (by rfl) ⟨1657697, by rfl⟩ : syracuseStep 2210263 = 3315395) B3315395
theorem B5594741 : Blo 2209435 5594741 := bbase (se 5 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 5594741 = 524507) (by norm_num)
theorem B3729827 : Blo 2209435 3729827 := bstep (se 1 (by rfl) ⟨2797370, by rfl⟩ : syracuseStep 3729827 = 5594741) B5594741
theorem B2486551 : Blo 2209435 2486551 := bstep (se 1 (by rfl) ⟨1864913, by rfl⟩ : syracuseStep 2486551 = 3729827) B3729827
theorem B3315401 : Blo 2209435 3315401 := bstep (se 2 (by rfl) ⟨1243275, by rfl⟩ : syracuseStep 3315401 = 2486551) B2486551
theorem B2210267 : Blo 2209435 2210267 := bstep (se 1 (by rfl) ⟨1657700, by rfl⟩ : syracuseStep 2210267 = 3315401) B3315401
theorem B2987237 : Blo 2209435 2987237 := bbase (se 4 (by rfl) ⟨280053, by rfl⟩ : syracuseStep 2987237 = 560107) (by norm_num)
theorem B7965965 : Blo 2209435 7965965 := bstep (se 3 (by rfl) ⟨1493618, by rfl⟩ : syracuseStep 7965965 = 2987237) B2987237
theorem B21242573 : Blo 2209435 21242573 := bstep (se 3 (by rfl) ⟨3982982, by rfl⟩ : syracuseStep 21242573 = 7965965) B7965965
theorem B14161715 : Blo 2209435 14161715 := bstep (se 1 (by rfl) ⟨10621286, by rfl⟩ : syracuseStep 14161715 = 21242573) B21242573
theorem B9441143 : Blo 2209435 9441143 := bstep (se 1 (by rfl) ⟨7080857, by rfl⟩ : syracuseStep 9441143 = 14161715) B14161715
theorem B6294095 : Blo 2209435 6294095 := bstep (se 1 (by rfl) ⟨4720571, by rfl⟩ : syracuseStep 6294095 = 9441143) B9441143
theorem B4196063 : Blo 2209435 4196063 := bstep (se 1 (by rfl) ⟨3147047, by rfl⟩ : syracuseStep 4196063 = 6294095) B6294095
theorem B11189501 : Blo 2209435 11189501 := bstep (se 3 (by rfl) ⟨2098031, by rfl⟩ : syracuseStep 11189501 = 4196063) B4196063
theorem B7459667 : Blo 2209435 7459667 := bstep (se 1 (by rfl) ⟨5594750, by rfl⟩ : syracuseStep 7459667 = 11189501) B11189501
theorem B4973111 : Blo 2209435 4973111 := bstep (se 1 (by rfl) ⟨3729833, by rfl⟩ : syracuseStep 4973111 = 7459667) B7459667
theorem B3315407 : Blo 2209435 3315407 := bstep (se 1 (by rfl) ⟨2486555, by rfl⟩ : syracuseStep 3315407 = 4973111) B4973111
theorem B2210271 : Blo 2209435 2210271 := bstep (se 1 (by rfl) ⟨1657703, by rfl⟩ : syracuseStep 2210271 = 3315407) B3315407
theorem B3315413 : Blo 2209435 3315413 := bbase (se 7 (by rfl) ⟨38852, by rfl⟩ : syracuseStep 3315413 = 77705) (by norm_num)
theorem B2210275 : Blo 2209435 2210275 := bstep (se 1 (by rfl) ⟨1657706, by rfl⟩ : syracuseStep 2210275 = 3315413) B3315413
theorem B4720589 : Blo 2209435 4720589 := bbase (se 3 (by rfl) ⟨885110, by rfl⟩ : syracuseStep 4720589 = 1770221) (by norm_num)
theorem B3147059 : Blo 2209435 3147059 := bstep (se 1 (by rfl) ⟨2360294, by rfl⟩ : syracuseStep 3147059 = 4720589) B4720589
theorem B8392157 : Blo 2209435 8392157 := bstep (se 3 (by rfl) ⟨1573529, by rfl⟩ : syracuseStep 8392157 = 3147059) B3147059
theorem B5594771 : Blo 2209435 5594771 := bstep (se 1 (by rfl) ⟨4196078, by rfl⟩ : syracuseStep 5594771 = 8392157) B8392157
theorem B3729847 : Blo 2209435 3729847 := bstep (se 1 (by rfl) ⟨2797385, by rfl⟩ : syracuseStep 3729847 = 5594771) B5594771
theorem B4973129 : Blo 2209435 4973129 := bstep (se 2 (by rfl) ⟨1864923, by rfl⟩ : syracuseStep 4973129 = 3729847) B3729847
theorem B3315419 : Blo 2209435 3315419 := bstep (se 1 (by rfl) ⟨2486564, by rfl⟩ : syracuseStep 3315419 = 4973129) B4973129
theorem B2210279 : Blo 2209435 2210279 := bstep (se 1 (by rfl) ⟨1657709, by rfl⟩ : syracuseStep 2210279 = 3315419) B3315419
theorem B2486569 : Blo 2209435 2486569 := bbase (se 2 (by rfl) ⟨932463, by rfl⟩ : syracuseStep 2486569 = 1864927) (by norm_num)
theorem B3315425 : Blo 2209435 3315425 := bstep (se 2 (by rfl) ⟨1243284, by rfl⟩ : syracuseStep 3315425 = 2486569) B2486569
theorem B2210283 : Blo 2209435 2210283 := bstep (se 1 (by rfl) ⟨1657712, by rfl⟩ : syracuseStep 2210283 = 3315425) B3315425
theorem B5974517 : Blo 2209435 5974517 := bbase (se 5 (by rfl) ⟨280055, by rfl⟩ : syracuseStep 5974517 = 560111) (by norm_num)
theorem B15932045 : Blo 2209435 15932045 := bstep (se 3 (by rfl) ⟨2987258, by rfl⟩ : syracuseStep 15932045 = 5974517) B5974517
theorem B10621363 : Blo 2209435 10621363 := bstep (se 1 (by rfl) ⟨7966022, by rfl⟩ : syracuseStep 10621363 = 15932045) B15932045
theorem B14161817 : Blo 2209435 14161817 := bstep (se 2 (by rfl) ⟨5310681, by rfl⟩ : syracuseStep 14161817 = 10621363) B10621363
theorem B9441211 : Blo 2209435 9441211 := bstep (se 1 (by rfl) ⟨7080908, by rfl⟩ : syracuseStep 9441211 = 14161817) B14161817
theorem B12588281 : Blo 2209435 12588281 := bstep (se 2 (by rfl) ⟨4720605, by rfl⟩ : syracuseStep 12588281 = 9441211) B9441211
theorem B8392187 : Blo 2209435 8392187 := bstep (se 1 (by rfl) ⟨6294140, by rfl⟩ : syracuseStep 8392187 = 12588281) B12588281
theorem B5594791 : Blo 2209435 5594791 := bstep (se 1 (by rfl) ⟨4196093, by rfl⟩ : syracuseStep 5594791 = 8392187) B8392187
theorem B7459721 : Blo 2209435 7459721 := bstep (se 2 (by rfl) ⟨2797395, by rfl⟩ : syracuseStep 7459721 = 5594791) B5594791
theorem B4973147 : Blo 2209435 4973147 := bstep (se 1 (by rfl) ⟨3729860, by rfl⟩ : syracuseStep 4973147 = 7459721) B7459721
theorem B3315431 : Blo 2209435 3315431 := bstep (se 1 (by rfl) ⟨2486573, by rfl⟩ : syracuseStep 3315431 = 4973147) B4973147
theorem B2210287 : Blo 2209435 2210287 := bstep (se 1 (by rfl) ⟨1657715, by rfl⟩ : syracuseStep 2210287 = 3315431) B3315431
theorem B3315437 : Blo 2209435 3315437 := bbase (se 3 (by rfl) ⟨621644, by rfl⟩ : syracuseStep 3315437 = 1243289) (by norm_num)
theorem B2210291 : Blo 2209435 2210291 := bstep (se 1 (by rfl) ⟨1657718, by rfl⟩ : syracuseStep 2210291 = 3315437) B3315437
theorem B4973165 : Blo 2209435 4973165 := bbase (se 3 (by rfl) ⟨932468, by rfl⟩ : syracuseStep 4973165 = 1864937) (by norm_num)
theorem B3315443 : Blo 2209435 3315443 := bstep (se 1 (by rfl) ⟨2486582, by rfl⟩ : syracuseStep 3315443 = 4973165) B4973165
theorem B2210295 : Blo 2209435 2210295 := bstep (se 1 (by rfl) ⟨1657721, by rfl⟩ : syracuseStep 2210295 = 3315443) B3315443
theorem B4196117 : Blo 2209435 4196117 := bbase (se 6 (by rfl) ⟨98346, by rfl⟩ : syracuseStep 4196117 = 196693) (by norm_num)
theorem B2797411 : Blo 2209435 2797411 := bstep (se 1 (by rfl) ⟨2098058, by rfl⟩ : syracuseStep 2797411 = 4196117) B4196117
theorem B3729881 : Blo 2209435 3729881 := bstep (se 2 (by rfl) ⟨1398705, by rfl⟩ : syracuseStep 3729881 = 2797411) B2797411
theorem B2486587 : Blo 2209435 2486587 := bstep (se 1 (by rfl) ⟨1864940, by rfl⟩ : syracuseStep 2486587 = 3729881) B3729881
theorem B3315449 : Blo 2209435 3315449 := bstep (se 2 (by rfl) ⟨1243293, by rfl⟩ : syracuseStep 3315449 = 2486587) B2486587
theorem B2210299 : Blo 2209435 2210299 := bstep (se 1 (by rfl) ⟨1657724, by rfl⟩ : syracuseStep 2210299 = 3315449) B3315449
theorem B5456621 : Blo 2209435 5456621 := bbase (se 3 (by rfl) ⟨1023116, by rfl⟩ : syracuseStep 5456621 = 2046233) (by norm_num)
theorem B3637747 : Blo 2209435 3637747 := bstep (se 1 (by rfl) ⟨2728310, by rfl⟩ : syracuseStep 3637747 = 5456621) B5456621
theorem B4850329 : Blo 2209435 4850329 := bstep (se 2 (by rfl) ⟨1818873, by rfl⟩ : syracuseStep 4850329 = 3637747) B3637747
theorem B6467105 : Blo 2209435 6467105 := bstep (se 2 (by rfl) ⟨2425164, by rfl⟩ : syracuseStep 6467105 = 4850329) B4850329
theorem B4311403 : Blo 2209435 4311403 := bstep (se 1 (by rfl) ⟨3233552, by rfl⟩ : syracuseStep 4311403 = 6467105) B6467105
theorem B91976597 : Blo 2209435 91976597 := bstep (se 6 (by rfl) ⟨2155701, by rfl⟩ : syracuseStep 91976597 = 4311403) B4311403
theorem B61317731 : Blo 2209435 61317731 := bstep (se 1 (by rfl) ⟨45988298, by rfl⟩ : syracuseStep 61317731 = 91976597) B91976597
theorem B40878487 : Blo 2209435 40878487 := bstep (se 1 (by rfl) ⟨30658865, by rfl⟩ : syracuseStep 40878487 = 61317731) B61317731
theorem B54504649 : Blo 2209435 54504649 := bstep (se 2 (by rfl) ⟨20439243, by rfl⟩ : syracuseStep 54504649 = 40878487) B40878487
theorem B290691461 : Blo 2209435 290691461 := bstep (se 4 (by rfl) ⟨27252324, by rfl⟩ : syracuseStep 290691461 = 54504649) B54504649
theorem B775177229 : Blo 2209435 775177229 := bstep (se 3 (by rfl) ⟨145345730, by rfl⟩ : syracuseStep 775177229 = 290691461) B290691461
theorem B516784819 : Blo 2209435 516784819 := bstep (se 1 (by rfl) ⟨387588614, by rfl⟩ : syracuseStep 516784819 = 775177229) B775177229
theorem B689046425 : Blo 2209435 689046425 := bstep (se 2 (by rfl) ⟨258392409, by rfl⟩ : syracuseStep 689046425 = 516784819) B516784819
theorem B459364283 : Blo 2209435 459364283 := bstep (se 1 (by rfl) ⟨344523212, by rfl⟩ : syracuseStep 459364283 = 689046425) B689046425
theorem B306242855 : Blo 2209435 306242855 := bstep (se 1 (by rfl) ⟨229682141, by rfl⟩ : syracuseStep 306242855 = 459364283) B459364283
theorem B204161903 : Blo 2209435 204161903 := bstep (se 1 (by rfl) ⟨153121427, by rfl⟩ : syracuseStep 204161903 = 306242855) B306242855
theorem B136107935 : Blo 2209435 136107935 := bstep (se 1 (by rfl) ⟨102080951, by rfl⟩ : syracuseStep 136107935 = 204161903) B204161903
theorem B90738623 : Blo 2209435 90738623 := bstep (se 1 (by rfl) ⟨68053967, by rfl⟩ : syracuseStep 90738623 = 136107935) B136107935
theorem B60492415 : Blo 2209435 60492415 := bstep (se 1 (by rfl) ⟨45369311, by rfl⟩ : syracuseStep 60492415 = 90738623) B90738623
theorem B80656553 : Blo 2209435 80656553 := bstep (se 2 (by rfl) ⟨30246207, by rfl⟩ : syracuseStep 80656553 = 60492415) B60492415
theorem B53771035 : Blo 2209435 53771035 := bstep (se 1 (by rfl) ⟨40328276, by rfl⟩ : syracuseStep 53771035 = 80656553) B80656553
theorem B71694713 : Blo 2209435 71694713 := bstep (se 2 (by rfl) ⟨26885517, by rfl⟩ : syracuseStep 71694713 = 53771035) B53771035
theorem B47796475 : Blo 2209435 47796475 := bstep (se 1 (by rfl) ⟨35847356, by rfl⟩ : syracuseStep 47796475 = 71694713) B71694713
theorem B63728633 : Blo 2209435 63728633 := bstep (se 2 (by rfl) ⟨23898237, by rfl⟩ : syracuseStep 63728633 = 47796475) B47796475
theorem B42485755 : Blo 2209435 42485755 := bstep (se 1 (by rfl) ⟨31864316, by rfl⟩ : syracuseStep 42485755 = 63728633) B63728633
theorem B56647673 : Blo 2209435 56647673 := bstep (se 2 (by rfl) ⟨21242877, by rfl⟩ : syracuseStep 56647673 = 42485755) B42485755
theorem B37765115 : Blo 2209435 37765115 := bstep (se 1 (by rfl) ⟨28323836, by rfl⟩ : syracuseStep 37765115 = 56647673) B56647673
theorem B25176743 : Blo 2209435 25176743 := bstep (se 1 (by rfl) ⟨18882557, by rfl⟩ : syracuseStep 25176743 = 37765115) B37765115
theorem B16784495 : Blo 2209435 16784495 := bstep (se 1 (by rfl) ⟨12588371, by rfl⟩ : syracuseStep 16784495 = 25176743) B25176743
theorem B11189663 : Blo 2209435 11189663 := bstep (se 1 (by rfl) ⟨8392247, by rfl⟩ : syracuseStep 11189663 = 16784495) B16784495
theorem B7459775 : Blo 2209435 7459775 := bstep (se 1 (by rfl) ⟨5594831, by rfl⟩ : syracuseStep 7459775 = 11189663) B11189663
theorem B4973183 : Blo 2209435 4973183 := bstep (se 1 (by rfl) ⟨3729887, by rfl⟩ : syracuseStep 4973183 = 7459775) B7459775
theorem B3315455 : Blo 2209435 3315455 := bstep (se 1 (by rfl) ⟨2486591, by rfl⟩ : syracuseStep 3315455 = 4973183) B4973183
theorem B2210303 : Blo 2209435 2210303 := bstep (se 1 (by rfl) ⟨1657727, by rfl⟩ : syracuseStep 2210303 = 3315455) B3315455
theorem B3315461 : Blo 2209435 3315461 := bbase (se 4 (by rfl) ⟨310824, by rfl⟩ : syracuseStep 3315461 = 621649) (by norm_num)
theorem B2210307 : Blo 2209435 2210307 := bstep (se 1 (by rfl) ⟨1657730, by rfl⟩ : syracuseStep 2210307 = 3315461) B3315461
theorem B3729901 : Blo 2209435 3729901 := bbase (se 3 (by rfl) ⟨699356, by rfl⟩ : syracuseStep 3729901 = 1398713) (by norm_num)
theorem B4973201 : Blo 2209435 4973201 := bstep (se 2 (by rfl) ⟨1864950, by rfl⟩ : syracuseStep 4973201 = 3729901) B3729901
theorem B3315467 : Blo 2209435 3315467 := bstep (se 1 (by rfl) ⟨2486600, by rfl⟩ : syracuseStep 3315467 = 4973201) B4973201
theorem B2210311 : Blo 2209435 2210311 := bstep (se 1 (by rfl) ⟨1657733, by rfl⟩ : syracuseStep 2210311 = 3315467) B3315467
theorem B2486605 : Blo 2209435 2486605 := bbase (se 3 (by rfl) ⟨466238, by rfl⟩ : syracuseStep 2486605 = 932477) (by norm_num)
theorem B3315473 : Blo 2209435 3315473 := bstep (se 2 (by rfl) ⟨1243302, by rfl⟩ : syracuseStep 3315473 = 2486605) B2486605
theorem B2210315 : Blo 2209435 2210315 := bstep (se 1 (by rfl) ⟨1657736, by rfl⟩ : syracuseStep 2210315 = 3315473) B3315473
theorem B7459829 : Blo 2209435 7459829 := bbase (se 5 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 7459829 = 699359) (by norm_num)
theorem B4973219 : Blo 2209435 4973219 := bstep (se 1 (by rfl) ⟨3729914, by rfl⟩ : syracuseStep 4973219 = 7459829) B7459829
theorem B3315479 : Blo 2209435 3315479 := bstep (se 1 (by rfl) ⟨2486609, by rfl⟩ : syracuseStep 3315479 = 4973219) B4973219
theorem B2210319 : Blo 2209435 2210319 := bstep (se 1 (by rfl) ⟨1657739, by rfl⟩ : syracuseStep 2210319 = 3315479) B3315479
theorem B3315485 : Blo 2209435 3315485 := bbase (se 3 (by rfl) ⟨621653, by rfl⟩ : syracuseStep 3315485 = 1243307) (by norm_num)
theorem B2210323 : Blo 2209435 2210323 := bstep (se 1 (by rfl) ⟨1657742, by rfl⟩ : syracuseStep 2210323 = 3315485) B3315485
theorem B4973237 : Blo 2209435 4973237 := bbase (se 5 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 4973237 = 466241) (by norm_num)
theorem B3315491 : Blo 2209435 3315491 := bstep (se 1 (by rfl) ⟨2486618, by rfl⟩ : syracuseStep 3315491 = 4973237) B4973237
theorem B2210327 : Blo 2209435 2210327 := bstep (se 1 (by rfl) ⟨1657745, by rfl⟩ : syracuseStep 2210327 = 3315491) B3315491
theorem B12588533 : Blo 2209435 12588533 := bbase (se 5 (by rfl) ⟨590087, by rfl⟩ : syracuseStep 12588533 = 1180175) (by norm_num)
theorem B8392355 : Blo 2209435 8392355 := bstep (se 1 (by rfl) ⟨6294266, by rfl⟩ : syracuseStep 8392355 = 12588533) B12588533
theorem B5594903 : Blo 2209435 5594903 := bstep (se 1 (by rfl) ⟨4196177, by rfl⟩ : syracuseStep 5594903 = 8392355) B8392355
theorem B3729935 : Blo 2209435 3729935 := bstep (se 1 (by rfl) ⟨2797451, by rfl⟩ : syracuseStep 3729935 = 5594903) B5594903
theorem B2486623 : Blo 2209435 2486623 := bstep (se 1 (by rfl) ⟨1864967, by rfl⟩ : syracuseStep 2486623 = 3729935) B3729935
theorem B3315497 : Blo 2209435 3315497 := bstep (se 2 (by rfl) ⟨1243311, by rfl⟩ : syracuseStep 3315497 = 2486623) B2486623
theorem B2210331 : Blo 2209435 2210331 := bstep (se 1 (by rfl) ⟨1657748, by rfl⟩ : syracuseStep 2210331 = 3315497) B3315497
theorem B6294277 : Blo 2209435 6294277 := bbase (se 4 (by rfl) ⟨590088, by rfl⟩ : syracuseStep 6294277 = 1180177) (by norm_num)
theorem B8392369 : Blo 2209435 8392369 := bstep (se 2 (by rfl) ⟨3147138, by rfl⟩ : syracuseStep 8392369 = 6294277) B6294277
theorem B11189825 : Blo 2209435 11189825 := bstep (se 2 (by rfl) ⟨4196184, by rfl⟩ : syracuseStep 11189825 = 8392369) B8392369
theorem B7459883 : Blo 2209435 7459883 := bstep (se 1 (by rfl) ⟨5594912, by rfl⟩ : syracuseStep 7459883 = 11189825) B11189825
theorem B4973255 : Blo 2209435 4973255 := bstep (se 1 (by rfl) ⟨3729941, by rfl⟩ : syracuseStep 4973255 = 7459883) B7459883
theorem B3315503 : Blo 2209435 3315503 := bstep (se 1 (by rfl) ⟨2486627, by rfl⟩ : syracuseStep 3315503 = 4973255) B4973255
theorem B2210335 : Blo 2209435 2210335 := bstep (se 1 (by rfl) ⟨1657751, by rfl⟩ : syracuseStep 2210335 = 3315503) B3315503
theorem B3315509 : Blo 2209435 3315509 := bbase (se 5 (by rfl) ⟨155414, by rfl⟩ : syracuseStep 3315509 = 310829) (by norm_num)
theorem B2210339 : Blo 2209435 2210339 := bstep (se 1 (by rfl) ⟨1657754, by rfl⟩ : syracuseStep 2210339 = 3315509) B3315509
theorem B5594933 : Blo 2209435 5594933 := bbase (se 5 (by rfl) ⟨262262, by rfl⟩ : syracuseStep 5594933 = 524525) (by norm_num)
theorem B3729955 : Blo 2209435 3729955 := bstep (se 1 (by rfl) ⟨2797466, by rfl⟩ : syracuseStep 3729955 = 5594933) B5594933
theorem B4973273 : Blo 2209435 4973273 := bstep (se 2 (by rfl) ⟨1864977, by rfl⟩ : syracuseStep 4973273 = 3729955) B3729955
theorem B3315515 : Blo 2209435 3315515 := bstep (se 1 (by rfl) ⟨2486636, by rfl⟩ : syracuseStep 3315515 = 4973273) B4973273
theorem B2210343 : Blo 2209435 2210343 := bstep (se 1 (by rfl) ⟨1657757, by rfl⟩ : syracuseStep 2210343 = 3315515) B3315515
theorem B2486641 : Blo 2209435 2486641 := bbase (se 2 (by rfl) ⟨932490, by rfl⟩ : syracuseStep 2486641 = 1864981) (by norm_num)
theorem B3315521 : Blo 2209435 3315521 := bstep (se 2 (by rfl) ⟨1243320, by rfl⟩ : syracuseStep 3315521 = 2486641) B2486641
theorem B2210347 : Blo 2209435 2210347 := bstep (se 1 (by rfl) ⟨1657760, by rfl⟩ : syracuseStep 2210347 = 3315521) B3315521
theorem B3540557 : Blo 2209435 3540557 := bbase (se 3 (by rfl) ⟨663854, by rfl⟩ : syracuseStep 3540557 = 1327709) (by norm_num)
theorem B9441485 : Blo 2209435 9441485 := bstep (se 3 (by rfl) ⟨1770278, by rfl⟩ : syracuseStep 9441485 = 3540557) B3540557
theorem B6294323 : Blo 2209435 6294323 := bstep (se 1 (by rfl) ⟨4720742, by rfl⟩ : syracuseStep 6294323 = 9441485) B9441485
theorem B4196215 : Blo 2209435 4196215 := bstep (se 1 (by rfl) ⟨3147161, by rfl⟩ : syracuseStep 4196215 = 6294323) B6294323
theorem B5594953 : Blo 2209435 5594953 := bstep (se 2 (by rfl) ⟨2098107, by rfl⟩ : syracuseStep 5594953 = 4196215) B4196215
theorem B7459937 : Blo 2209435 7459937 := bstep (se 2 (by rfl) ⟨2797476, by rfl⟩ : syracuseStep 7459937 = 5594953) B5594953
theorem B4973291 : Blo 2209435 4973291 := bstep (se 1 (by rfl) ⟨3729968, by rfl⟩ : syracuseStep 4973291 = 7459937) B7459937
theorem B3315527 : Blo 2209435 3315527 := bstep (se 1 (by rfl) ⟨2486645, by rfl⟩ : syracuseStep 3315527 = 4973291) B4973291
theorem B2210351 : Blo 2209435 2210351 := bstep (se 1 (by rfl) ⟨1657763, by rfl⟩ : syracuseStep 2210351 = 3315527) B3315527
theorem B3315533 : Blo 2209435 3315533 := bbase (se 3 (by rfl) ⟨621662, by rfl⟩ : syracuseStep 3315533 = 1243325) (by norm_num)
theorem B2210355 : Blo 2209435 2210355 := bstep (se 1 (by rfl) ⟨1657766, by rfl⟩ : syracuseStep 2210355 = 3315533) B3315533
theorem B4973309 : Blo 2209435 4973309 := bbase (se 3 (by rfl) ⟨932495, by rfl⟩ : syracuseStep 4973309 = 1864991) (by norm_num)
theorem B3315539 : Blo 2209435 3315539 := bstep (se 1 (by rfl) ⟨2486654, by rfl⟩ : syracuseStep 3315539 = 4973309) B4973309
theorem B2210359 : Blo 2209435 2210359 := bstep (se 1 (by rfl) ⟨1657769, by rfl⟩ : syracuseStep 2210359 = 3315539) B3315539
theorem B3729989 : Blo 2209435 3729989 := bbase (se 4 (by rfl) ⟨349686, by rfl⟩ : syracuseStep 3729989 = 699373) (by norm_num)
theorem B2486659 : Blo 2209435 2486659 := bstep (se 1 (by rfl) ⟨1864994, by rfl⟩ : syracuseStep 2486659 = 3729989) B3729989
theorem B3315545 : Blo 2209435 3315545 := bstep (se 2 (by rfl) ⟨1243329, by rfl⟩ : syracuseStep 3315545 = 2486659) B2486659
theorem B2210363 : Blo 2209435 2210363 := bstep (se 1 (by rfl) ⟨1657772, by rfl⟩ : syracuseStep 2210363 = 3315545) B3315545
theorem B16784981 : Blo 2209435 16784981 := bbase (se 8 (by rfl) ⟨98349, by rfl⟩ : syracuseStep 16784981 = 196699) (by norm_num)
theorem B11189987 : Blo 2209435 11189987 := bstep (se 1 (by rfl) ⟨8392490, by rfl⟩ : syracuseStep 11189987 = 16784981) B16784981
theorem B7459991 : Blo 2209435 7459991 := bstep (se 1 (by rfl) ⟨5594993, by rfl⟩ : syracuseStep 7459991 = 11189987) B11189987
theorem B4973327 : Blo 2209435 4973327 := bstep (se 1 (by rfl) ⟨3729995, by rfl⟩ : syracuseStep 4973327 = 7459991) B7459991
theorem B3315551 : Blo 2209435 3315551 := bstep (se 1 (by rfl) ⟨2486663, by rfl⟩ : syracuseStep 3315551 = 4973327) B4973327
theorem B2210367 : Blo 2209435 2210367 := bstep (se 1 (by rfl) ⟨1657775, by rfl⟩ : syracuseStep 2210367 = 3315551) B3315551
theorem B3315557 : Blo 2209435 3315557 := bbase (se 4 (by rfl) ⟨310833, by rfl⟩ : syracuseStep 3315557 = 621667) (by norm_num)
theorem B2210371 : Blo 2209435 2210371 := bstep (se 1 (by rfl) ⟨1657778, by rfl⟩ : syracuseStep 2210371 = 3315557) B3315557
theorem B4196261 : Blo 2209435 4196261 := bbase (se 4 (by rfl) ⟨393399, by rfl⟩ : syracuseStep 4196261 = 786799) (by norm_num)
theorem B2797507 : Blo 2209435 2797507 := bstep (se 1 (by rfl) ⟨2098130, by rfl⟩ : syracuseStep 2797507 = 4196261) B4196261
theorem B3730009 : Blo 2209435 3730009 := bstep (se 2 (by rfl) ⟨1398753, by rfl⟩ : syracuseStep 3730009 = 2797507) B2797507
theorem B4973345 : Blo 2209435 4973345 := bstep (se 2 (by rfl) ⟨1865004, by rfl⟩ : syracuseStep 4973345 = 3730009) B3730009
theorem B3315563 : Blo 2209435 3315563 := bstep (se 1 (by rfl) ⟨2486672, by rfl⟩ : syracuseStep 3315563 = 4973345) B4973345
theorem B2210375 : Blo 2209435 2210375 := bstep (se 1 (by rfl) ⟨1657781, by rfl⟩ : syracuseStep 2210375 = 3315563) B3315563
theorem B2486677 : Blo 2209435 2486677 := bbase (se 6 (by rfl) ⟨58281, by rfl⟩ : syracuseStep 2486677 = 116563) (by norm_num)
theorem B3315569 : Blo 2209435 3315569 := bstep (se 2 (by rfl) ⟨1243338, by rfl⟩ : syracuseStep 3315569 = 2486677) B2486677
theorem B2210379 : Blo 2209435 2210379 := bstep (se 1 (by rfl) ⟨1657784, by rfl⟩ : syracuseStep 2210379 = 3315569) B3315569
theorem B2797517 : Blo 2209435 2797517 := bbase (se 3 (by rfl) ⟨524534, by rfl⟩ : syracuseStep 2797517 = 1049069) (by norm_num)
theorem B7460045 : Blo 2209435 7460045 := bstep (se 3 (by rfl) ⟨1398758, by rfl⟩ : syracuseStep 7460045 = 2797517) B2797517
theorem B4973363 : Blo 2209435 4973363 := bstep (se 1 (by rfl) ⟨3730022, by rfl⟩ : syracuseStep 4973363 = 7460045) B7460045
theorem B3315575 : Blo 2209435 3315575 := bstep (se 1 (by rfl) ⟨2486681, by rfl⟩ : syracuseStep 3315575 = 4973363) B4973363
theorem B2210383 : Blo 2209435 2210383 := bstep (se 1 (by rfl) ⟨1657787, by rfl⟩ : syracuseStep 2210383 = 3315575) B3315575
theorem B3315581 : Blo 2209435 3315581 := bbase (se 3 (by rfl) ⟨621671, by rfl⟩ : syracuseStep 3315581 = 1243343) (by norm_num)
theorem B2210387 : Blo 2209435 2210387 := bstep (se 1 (by rfl) ⟨1657790, by rfl⟩ : syracuseStep 2210387 = 3315581) B3315581
theorem B4973381 : Blo 2209435 4973381 := bbase (se 4 (by rfl) ⟨466254, by rfl⟩ : syracuseStep 4973381 = 932509) (by norm_num)
theorem B3315587 : Blo 2209435 3315587 := bstep (se 1 (by rfl) ⟨2486690, by rfl⟩ : syracuseStep 3315587 = 4973381) B4973381
theorem B2210391 : Blo 2209435 2210391 := bstep (se 1 (by rfl) ⟨1657793, by rfl⟩ : syracuseStep 2210391 = 3315587) B3315587
theorem B4720837 : Blo 2209435 4720837 := bbase (se 4 (by rfl) ⟨442578, by rfl⟩ : syracuseStep 4720837 = 885157) (by norm_num)
theorem B6294449 : Blo 2209435 6294449 := bstep (se 2 (by rfl) ⟨2360418, by rfl⟩ : syracuseStep 6294449 = 4720837) B4720837
theorem B4196299 : Blo 2209435 4196299 := bstep (se 1 (by rfl) ⟨3147224, by rfl⟩ : syracuseStep 4196299 = 6294449) B6294449
theorem B5595065 : Blo 2209435 5595065 := bstep (se 2 (by rfl) ⟨2098149, by rfl⟩ : syracuseStep 5595065 = 4196299) B4196299
theorem B3730043 : Blo 2209435 3730043 := bstep (se 1 (by rfl) ⟨2797532, by rfl⟩ : syracuseStep 3730043 = 5595065) B5595065
theorem B2486695 : Blo 2209435 2486695 := bstep (se 1 (by rfl) ⟨1865021, by rfl⟩ : syracuseStep 2486695 = 3730043) B3730043
theorem B3315593 : Blo 2209435 3315593 := bstep (se 2 (by rfl) ⟨1243347, by rfl⟩ : syracuseStep 3315593 = 2486695) B2486695
theorem B2210395 : Blo 2209435 2210395 := bstep (se 1 (by rfl) ⟨1657796, by rfl⟩ : syracuseStep 2210395 = 3315593) B3315593
theorem B11190149 : Blo 2209435 11190149 := bbase (se 4 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 11190149 = 2098153) (by norm_num)
theorem B7460099 : Blo 2209435 7460099 := bstep (se 1 (by rfl) ⟨5595074, by rfl⟩ : syracuseStep 7460099 = 11190149) B11190149
theorem B4973399 : Blo 2209435 4973399 := bstep (se 1 (by rfl) ⟨3730049, by rfl⟩ : syracuseStep 4973399 = 7460099) B7460099
theorem B3315599 : Blo 2209435 3315599 := bstep (se 1 (by rfl) ⟨2486699, by rfl⟩ : syracuseStep 3315599 = 4973399) B4973399
theorem B2210399 : Blo 2209435 2210399 := bstep (se 1 (by rfl) ⟨1657799, by rfl⟩ : syracuseStep 2210399 = 3315599) B3315599
theorem B3315605 : Blo 2209435 3315605 := bbase (se 6 (by rfl) ⟨77709, by rfl⟩ : syracuseStep 3315605 = 155419) (by norm_num)
theorem B2210403 : Blo 2209435 2210403 := bstep (se 1 (by rfl) ⟨1657802, by rfl⟩ : syracuseStep 2210403 = 3315605) B3315605
theorem B10082549 : Blo 2209435 10082549 := bbase (se 5 (by rfl) ⟨472619, by rfl⟩ : syracuseStep 10082549 = 945239) (by norm_num)
theorem B6721699 : Blo 2209435 6721699 := bstep (se 1 (by rfl) ⟨5041274, by rfl⟩ : syracuseStep 6721699 = 10082549) B10082549
theorem B8962265 : Blo 2209435 8962265 := bstep (se 2 (by rfl) ⟨3360849, by rfl⟩ : syracuseStep 8962265 = 6721699) B6721699
theorem B5974843 : Blo 2209435 5974843 := bstep (se 1 (by rfl) ⟨4481132, by rfl⟩ : syracuseStep 5974843 = 8962265) B8962265
theorem B7966457 : Blo 2209435 7966457 := bstep (se 2 (by rfl) ⟨2987421, by rfl⟩ : syracuseStep 7966457 = 5974843) B5974843
theorem B5310971 : Blo 2209435 5310971 := bstep (se 1 (by rfl) ⟨3983228, by rfl⟩ : syracuseStep 5310971 = 7966457) B7966457
theorem B3540647 : Blo 2209435 3540647 := bstep (se 1 (by rfl) ⟨2655485, by rfl⟩ : syracuseStep 3540647 = 5310971) B5310971
theorem B2360431 : Blo 2209435 2360431 := bstep (se 1 (by rfl) ⟨1770323, by rfl⟩ : syracuseStep 2360431 = 3540647) B3540647
theorem B12588965 : Blo 2209435 12588965 := bstep (se 4 (by rfl) ⟨1180215, by rfl⟩ : syracuseStep 12588965 = 2360431) B2360431
theorem B8392643 : Blo 2209435 8392643 := bstep (se 1 (by rfl) ⟨6294482, by rfl⟩ : syracuseStep 8392643 = 12588965) B12588965
theorem B5595095 : Blo 2209435 5595095 := bstep (se 1 (by rfl) ⟨4196321, by rfl⟩ : syracuseStep 5595095 = 8392643) B8392643
theorem B3730063 : Blo 2209435 3730063 := bstep (se 1 (by rfl) ⟨2797547, by rfl⟩ : syracuseStep 3730063 = 5595095) B5595095
theorem B4973417 : Blo 2209435 4973417 := bstep (se 2 (by rfl) ⟨1865031, by rfl⟩ : syracuseStep 4973417 = 3730063) B3730063
theorem B3315611 : Blo 2209435 3315611 := bstep (se 1 (by rfl) ⟨2486708, by rfl⟩ : syracuseStep 3315611 = 4973417) B4973417
theorem B2210407 : Blo 2209435 2210407 := bstep (se 1 (by rfl) ⟨1657805, by rfl⟩ : syracuseStep 2210407 = 3315611) B3315611
theorem B2486713 : Blo 2209435 2486713 := bbase (se 2 (by rfl) ⟨932517, by rfl⟩ : syracuseStep 2486713 = 1865035) (by norm_num)
theorem B3315617 : Blo 2209435 3315617 := bstep (se 2 (by rfl) ⟨1243356, by rfl⟩ : syracuseStep 3315617 = 2486713) B2486713
theorem B2210411 : Blo 2209435 2210411 := bstep (se 1 (by rfl) ⟨1657808, by rfl⟩ : syracuseStep 2210411 = 3315617) B3315617
theorem B3277837 : Blo 2209435 3277837 := bbase (se 3 (by rfl) ⟨614594, by rfl⟩ : syracuseStep 3277837 = 1229189) (by norm_num)
theorem B4370449 : Blo 2209435 4370449 := bstep (se 2 (by rfl) ⟨1638918, by rfl⟩ : syracuseStep 4370449 = 3277837) B3277837
theorem B5827265 : Blo 2209435 5827265 := bstep (se 2 (by rfl) ⟨2185224, by rfl⟩ : syracuseStep 5827265 = 4370449) B4370449
theorem B3884843 : Blo 2209435 3884843 := bstep (se 1 (by rfl) ⟨2913632, by rfl⟩ : syracuseStep 3884843 = 5827265) B5827265
theorem B10359581 : Blo 2209435 10359581 := bstep (se 3 (by rfl) ⟨1942421, by rfl⟩ : syracuseStep 10359581 = 3884843) B3884843
theorem B27625549 : Blo 2209435 27625549 := bstep (se 3 (by rfl) ⟨5179790, by rfl⟩ : syracuseStep 27625549 = 10359581) B10359581
theorem B36834065 : Blo 2209435 36834065 := bstep (se 2 (by rfl) ⟨13812774, by rfl⟩ : syracuseStep 36834065 = 27625549) B27625549
theorem B24556043 : Blo 2209435 24556043 := bstep (se 1 (by rfl) ⟨18417032, by rfl⟩ : syracuseStep 24556043 = 36834065) B36834065
theorem B16370695 : Blo 2209435 16370695 := bstep (se 1 (by rfl) ⟨12278021, by rfl⟩ : syracuseStep 16370695 = 24556043) B24556043
theorem B21827593 : Blo 2209435 21827593 := bstep (se 2 (by rfl) ⟨8185347, by rfl⟩ : syracuseStep 21827593 = 16370695) B16370695
theorem B29103457 : Blo 2209435 29103457 := bstep (se 2 (by rfl) ⟨10913796, by rfl⟩ : syracuseStep 29103457 = 21827593) B21827593
theorem B38804609 : Blo 2209435 38804609 := bstep (se 2 (by rfl) ⟨14551728, by rfl⟩ : syracuseStep 38804609 = 29103457) B29103457
theorem B25869739 : Blo 2209435 25869739 := bstep (se 1 (by rfl) ⟨19402304, by rfl⟩ : syracuseStep 25869739 = 38804609) B38804609
theorem B34492985 : Blo 2209435 34492985 := bstep (se 2 (by rfl) ⟨12934869, by rfl⟩ : syracuseStep 34492985 = 25869739) B25869739
theorem B22995323 : Blo 2209435 22995323 := bstep (se 1 (by rfl) ⟨17246492, by rfl⟩ : syracuseStep 22995323 = 34492985) B34492985
theorem B15330215 : Blo 2209435 15330215 := bstep (se 1 (by rfl) ⟨11497661, by rfl⟩ : syracuseStep 15330215 = 22995323) B22995323
theorem B10220143 : Blo 2209435 10220143 := bstep (se 1 (by rfl) ⟨7665107, by rfl⟩ : syracuseStep 10220143 = 15330215) B15330215
theorem B13626857 : Blo 2209435 13626857 := bstep (se 2 (by rfl) ⟨5110071, by rfl⟩ : syracuseStep 13626857 = 10220143) B10220143
theorem B36338285 : Blo 2209435 36338285 := bstep (se 3 (by rfl) ⟨6813428, by rfl⟩ : syracuseStep 36338285 = 13626857) B13626857
theorem B24225523 : Blo 2209435 24225523 := bstep (se 1 (by rfl) ⟨18169142, by rfl⟩ : syracuseStep 24225523 = 36338285) B36338285
theorem B129202789 : Blo 2209435 129202789 := bstep (se 4 (by rfl) ⟨12112761, by rfl⟩ : syracuseStep 129202789 = 24225523) B24225523
theorem B172270385 : Blo 2209435 172270385 := bstep (se 2 (by rfl) ⟨64601394, by rfl⟩ : syracuseStep 172270385 = 129202789) B129202789
theorem B114846923 : Blo 2209435 114846923 := bstep (se 1 (by rfl) ⟨86135192, by rfl⟩ : syracuseStep 114846923 = 172270385) B172270385
theorem B76564615 : Blo 2209435 76564615 := bstep (se 1 (by rfl) ⟨57423461, by rfl⟩ : syracuseStep 76564615 = 114846923) B114846923
theorem B102086153 : Blo 2209435 102086153 := bstep (se 2 (by rfl) ⟨38282307, by rfl⟩ : syracuseStep 102086153 = 76564615) B76564615
theorem B68057435 : Blo 2209435 68057435 := bstep (se 1 (by rfl) ⟨51043076, by rfl⟩ : syracuseStep 68057435 = 102086153) B102086153
theorem B45371623 : Blo 2209435 45371623 := bstep (se 1 (by rfl) ⟨34028717, by rfl⟩ : syracuseStep 45371623 = 68057435) B68057435
theorem B60495497 : Blo 2209435 60495497 := bstep (se 2 (by rfl) ⟨22685811, by rfl⟩ : syracuseStep 60495497 = 45371623) B45371623
theorem B40330331 : Blo 2209435 40330331 := bstep (se 1 (by rfl) ⟨30247748, by rfl⟩ : syracuseStep 40330331 = 60495497) B60495497
theorem B26886887 : Blo 2209435 26886887 := bstep (se 1 (by rfl) ⟨20165165, by rfl⟩ : syracuseStep 26886887 = 40330331) B40330331
theorem B17924591 : Blo 2209435 17924591 := bstep (se 1 (by rfl) ⟨13443443, by rfl⟩ : syracuseStep 17924591 = 26886887) B26886887
theorem B11949727 : Blo 2209435 11949727 := bstep (se 1 (by rfl) ⟨8962295, by rfl⟩ : syracuseStep 11949727 = 17924591) B17924591
theorem B15932969 : Blo 2209435 15932969 := bstep (se 2 (by rfl) ⟨5974863, by rfl⟩ : syracuseStep 15932969 = 11949727) B11949727
theorem B10621979 : Blo 2209435 10621979 := bstep (se 1 (by rfl) ⟨7966484, by rfl⟩ : syracuseStep 10621979 = 15932969) B15932969
theorem B7081319 : Blo 2209435 7081319 := bstep (se 1 (by rfl) ⟨5310989, by rfl⟩ : syracuseStep 7081319 = 10621979) B10621979
theorem B4720879 : Blo 2209435 4720879 := bstep (se 1 (by rfl) ⟨3540659, by rfl⟩ : syracuseStep 4720879 = 7081319) B7081319
theorem B6294505 : Blo 2209435 6294505 := bstep (se 2 (by rfl) ⟨2360439, by rfl⟩ : syracuseStep 6294505 = 4720879) B4720879
theorem B8392673 : Blo 2209435 8392673 := bstep (se 2 (by rfl) ⟨3147252, by rfl⟩ : syracuseStep 8392673 = 6294505) B6294505
theorem B5595115 : Blo 2209435 5595115 := bstep (se 1 (by rfl) ⟨4196336, by rfl⟩ : syracuseStep 5595115 = 8392673) B8392673
theorem B7460153 : Blo 2209435 7460153 := bstep (se 2 (by rfl) ⟨2797557, by rfl⟩ : syracuseStep 7460153 = 5595115) B5595115
theorem B4973435 : Blo 2209435 4973435 := bstep (se 1 (by rfl) ⟨3730076, by rfl⟩ : syracuseStep 4973435 = 7460153) B7460153
theorem B3315623 : Blo 2209435 3315623 := bstep (se 1 (by rfl) ⟨2486717, by rfl⟩ : syracuseStep 3315623 = 4973435) B4973435
theorem B2210415 : Blo 2209435 2210415 := bstep (se 1 (by rfl) ⟨1657811, by rfl⟩ : syracuseStep 2210415 = 3315623) B3315623
theorem B3315629 : Blo 2209435 3315629 := bbase (se 3 (by rfl) ⟨621680, by rfl⟩ : syracuseStep 3315629 = 1243361) (by norm_num)
theorem B2210419 : Blo 2209435 2210419 := bstep (se 1 (by rfl) ⟨1657814, by rfl⟩ : syracuseStep 2210419 = 3315629) B3315629
theorem B4973453 : Blo 2209435 4973453 := bbase (se 3 (by rfl) ⟨932522, by rfl⟩ : syracuseStep 4973453 = 1865045) (by norm_num)
theorem B3315635 : Blo 2209435 3315635 := bstep (se 1 (by rfl) ⟨2486726, by rfl⟩ : syracuseStep 3315635 = 4973453) B4973453
theorem B2210423 : Blo 2209435 2210423 := bstep (se 1 (by rfl) ⟨1657817, by rfl⟩ : syracuseStep 2210423 = 3315635) B3315635
theorem B2797573 : Blo 2209435 2797573 := bbase (se 4 (by rfl) ⟨262272, by rfl⟩ : syracuseStep 2797573 = 524545) (by norm_num)
theorem B3730097 : Blo 2209435 3730097 := bstep (se 2 (by rfl) ⟨1398786, by rfl⟩ : syracuseStep 3730097 = 2797573) B2797573
theorem B2486731 : Blo 2209435 2486731 := bstep (se 1 (by rfl) ⟨1865048, by rfl⟩ : syracuseStep 2486731 = 3730097) B3730097
theorem B3315641 : Blo 2209435 3315641 := bstep (se 2 (by rfl) ⟨1243365, by rfl⟩ : syracuseStep 3315641 = 2486731) B2486731
theorem B2210427 : Blo 2209435 2210427 := bstep (se 1 (by rfl) ⟨1657820, by rfl⟩ : syracuseStep 2210427 = 3315641) B3315641
theorem B2987453 : Blo 2209435 2987453 := bbase (se 3 (by rfl) ⟨560147, by rfl⟩ : syracuseStep 2987453 = 1120295) (by norm_num)
theorem B7966541 : Blo 2209435 7966541 := bstep (se 3 (by rfl) ⟨1493726, by rfl⟩ : syracuseStep 7966541 = 2987453) B2987453
theorem B5311027 : Blo 2209435 5311027 := bstep (se 1 (by rfl) ⟨3983270, by rfl⟩ : syracuseStep 5311027 = 7966541) B7966541
theorem B28325477 : Blo 2209435 28325477 := bstep (se 4 (by rfl) ⟨2655513, by rfl⟩ : syracuseStep 28325477 = 5311027) B5311027
theorem B18883651 : Blo 2209435 18883651 := bstep (se 1 (by rfl) ⟨14162738, by rfl⟩ : syracuseStep 18883651 = 28325477) B28325477
theorem B25178201 : Blo 2209435 25178201 := bstep (se 2 (by rfl) ⟨9441825, by rfl⟩ : syracuseStep 25178201 = 18883651) B18883651
theorem B16785467 : Blo 2209435 16785467 := bstep (se 1 (by rfl) ⟨12589100, by rfl⟩ : syracuseStep 16785467 = 25178201) B25178201
theorem B11190311 : Blo 2209435 11190311 := bstep (se 1 (by rfl) ⟨8392733, by rfl⟩ : syracuseStep 11190311 = 16785467) B16785467
theorem B7460207 : Blo 2209435 7460207 := bstep (se 1 (by rfl) ⟨5595155, by rfl⟩ : syracuseStep 7460207 = 11190311) B11190311
theorem B4973471 : Blo 2209435 4973471 := bstep (se 1 (by rfl) ⟨3730103, by rfl⟩ : syracuseStep 4973471 = 7460207) B7460207
theorem B3315647 : Blo 2209435 3315647 := bstep (se 1 (by rfl) ⟨2486735, by rfl⟩ : syracuseStep 3315647 = 4973471) B4973471
theorem B2210431 : Blo 2209435 2210431 := bstep (se 1 (by rfl) ⟨1657823, by rfl⟩ : syracuseStep 2210431 = 3315647) B3315647
theorem B3315653 : Blo 2209435 3315653 := bbase (se 4 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 3315653 = 621685) (by norm_num)
theorem B2210435 : Blo 2209435 2210435 := bstep (se 1 (by rfl) ⟨1657826, by rfl⟩ : syracuseStep 2210435 = 3315653) B3315653
theorem B3730117 : Blo 2209435 3730117 := bbase (se 4 (by rfl) ⟨349698, by rfl⟩ : syracuseStep 3730117 = 699397) (by norm_num)
theorem B4973489 : Blo 2209435 4973489 := bstep (se 2 (by rfl) ⟨1865058, by rfl⟩ : syracuseStep 4973489 = 3730117) B3730117
theorem B3315659 : Blo 2209435 3315659 := bstep (se 1 (by rfl) ⟨2486744, by rfl⟩ : syracuseStep 3315659 = 4973489) B4973489
theorem B2210439 : Blo 2209435 2210439 := bstep (se 1 (by rfl) ⟨1657829, by rfl⟩ : syracuseStep 2210439 = 3315659) B3315659
theorem B2486749 : Blo 2209435 2486749 := bbase (se 3 (by rfl) ⟨466265, by rfl⟩ : syracuseStep 2486749 = 932531) (by norm_num)
theorem B3315665 : Blo 2209435 3315665 := bstep (se 2 (by rfl) ⟨1243374, by rfl⟩ : syracuseStep 3315665 = 2486749) B2486749
theorem B2210443 : Blo 2209435 2210443 := bstep (se 1 (by rfl) ⟨1657832, by rfl⟩ : syracuseStep 2210443 = 3315665) B3315665
theorem B7460261 : Blo 2209435 7460261 := bbase (se 4 (by rfl) ⟨699399, by rfl⟩ : syracuseStep 7460261 = 1398799) (by norm_num)
theorem B4973507 : Blo 2209435 4973507 := bstep (se 1 (by rfl) ⟨3730130, by rfl⟩ : syracuseStep 4973507 = 7460261) B7460261
theorem B3315671 : Blo 2209435 3315671 := bstep (se 1 (by rfl) ⟨2486753, by rfl⟩ : syracuseStep 3315671 = 4973507) B4973507
theorem B2210447 : Blo 2209435 2210447 := bstep (se 1 (by rfl) ⟨1657835, by rfl⟩ : syracuseStep 2210447 = 3315671) B3315671
theorem B3315677 : Blo 2209435 3315677 := bbase (se 3 (by rfl) ⟨621689, by rfl⟩ : syracuseStep 3315677 = 1243379) (by norm_num)
theorem B2210451 : Blo 2209435 2210451 := bstep (se 1 (by rfl) ⟨1657838, by rfl⟩ : syracuseStep 2210451 = 3315677) B3315677
theorem B4973525 : Blo 2209435 4973525 := bbase (se 7 (by rfl) ⟨58283, by rfl⟩ : syracuseStep 4973525 = 116567) (by norm_num)
theorem B3315683 : Blo 2209435 3315683 := bstep (se 1 (by rfl) ⟨2486762, by rfl⟩ : syracuseStep 3315683 = 4973525) B4973525
theorem B2210455 : Blo 2209435 2210455 := bstep (se 1 (by rfl) ⟨1657841, by rfl⟩ : syracuseStep 2210455 = 3315683) B3315683
theorem B4148597 : Blo 2209435 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B11062925 : Blo 2209435 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B7375283 : Blo 2209435 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B4916855 : Blo 2209435 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B3277903 : Blo 2209435 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B4370537 : Blo 2209435 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B11654765 : Blo 2209435 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B7769843 : Blo 2209435 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B5179895 : Blo 2209435 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B3453263 : Blo 2209435 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B2302175 : Blo 2209435 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B6139133 : Blo 2209435 6139133 := bstep (se 3 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 6139133 = 2302175) B2302175
theorem B4092755 : Blo 2209435 4092755 := bstep (se 1 (by rfl) ⟨3069566, by rfl⟩ : syracuseStep 4092755 = 6139133) B6139133
theorem B10914013 : Blo 2209435 10914013 := bstep (se 3 (by rfl) ⟨2046377, by rfl⟩ : syracuseStep 10914013 = 4092755) B4092755
theorem B14552017 : Blo 2209435 14552017 := bstep (se 2 (by rfl) ⟨5457006, by rfl⟩ : syracuseStep 14552017 = 10914013) B10914013
theorem B77610757 : Blo 2209435 77610757 := bstep (se 4 (by rfl) ⟨7276008, by rfl⟩ : syracuseStep 77610757 = 14552017) B14552017
theorem B103481009 : Blo 2209435 103481009 := bstep (se 2 (by rfl) ⟨38805378, by rfl⟩ : syracuseStep 103481009 = 77610757) B77610757
theorem B68987339 : Blo 2209435 68987339 := bstep (se 1 (by rfl) ⟨51740504, by rfl⟩ : syracuseStep 68987339 = 103481009) B103481009
theorem B45991559 : Blo 2209435 45991559 := bstep (se 1 (by rfl) ⟨34493669, by rfl⟩ : syracuseStep 45991559 = 68987339) B68987339
theorem B30661039 : Blo 2209435 30661039 := bstep (se 1 (by rfl) ⟨22995779, by rfl⟩ : syracuseStep 30661039 = 45991559) B45991559
theorem B40881385 : Blo 2209435 40881385 := bstep (se 2 (by rfl) ⟨15330519, by rfl⟩ : syracuseStep 40881385 = 30661039) B30661039
theorem B54508513 : Blo 2209435 54508513 := bstep (se 2 (by rfl) ⟨20440692, by rfl⟩ : syracuseStep 54508513 = 40881385) B40881385
theorem B72678017 : Blo 2209435 72678017 := bstep (se 2 (by rfl) ⟨27254256, by rfl⟩ : syracuseStep 72678017 = 54508513) B54508513
theorem B193808045 : Blo 2209435 193808045 := bstep (se 3 (by rfl) ⟨36339008, by rfl⟩ : syracuseStep 193808045 = 72678017) B72678017
theorem B129205363 : Blo 2209435 129205363 := bstep (se 1 (by rfl) ⟨96904022, by rfl⟩ : syracuseStep 129205363 = 193808045) B193808045
theorem B172273817 : Blo 2209435 172273817 := bstep (se 2 (by rfl) ⟨64602681, by rfl⟩ : syracuseStep 172273817 = 129205363) B129205363
theorem B459396845 : Blo 2209435 459396845 := bstep (se 3 (by rfl) ⟨86136908, by rfl⟩ : syracuseStep 459396845 = 172273817) B172273817
theorem B306264563 : Blo 2209435 306264563 := bstep (se 1 (by rfl) ⟨229698422, by rfl⟩ : syracuseStep 306264563 = 459396845) B459396845
theorem B204176375 : Blo 2209435 204176375 := bstep (se 1 (by rfl) ⟨153132281, by rfl⟩ : syracuseStep 204176375 = 306264563) B306264563
theorem B136117583 : Blo 2209435 136117583 := bstep (se 1 (by rfl) ⟨102088187, by rfl⟩ : syracuseStep 136117583 = 204176375) B204176375
theorem B90745055 : Blo 2209435 90745055 := bstep (se 1 (by rfl) ⟨68058791, by rfl⟩ : syracuseStep 90745055 = 136117583) B136117583
theorem B60496703 : Blo 2209435 60496703 := bstep (se 1 (by rfl) ⟨45372527, by rfl⟩ : syracuseStep 60496703 = 90745055) B90745055
theorem B40331135 : Blo 2209435 40331135 := bstep (se 1 (by rfl) ⟨30248351, by rfl⟩ : syracuseStep 40331135 = 60496703) B60496703
theorem B26887423 : Blo 2209435 26887423 := bstep (se 1 (by rfl) ⟨20165567, by rfl⟩ : syracuseStep 26887423 = 40331135) B40331135
theorem B35849897 : Blo 2209435 35849897 := bstep (se 2 (by rfl) ⟨13443711, by rfl⟩ : syracuseStep 35849897 = 26887423) B26887423
theorem B23899931 : Blo 2209435 23899931 := bstep (se 1 (by rfl) ⟨17924948, by rfl⟩ : syracuseStep 23899931 = 35849897) B35849897
theorem B15933287 : Blo 2209435 15933287 := bstep (se 1 (by rfl) ⟨11949965, by rfl⟩ : syracuseStep 15933287 = 23899931) B23899931
theorem B10622191 : Blo 2209435 10622191 := bstep (se 1 (by rfl) ⟨7966643, by rfl⟩ : syracuseStep 10622191 = 15933287) B15933287
theorem B14162921 : Blo 2209435 14162921 := bstep (se 2 (by rfl) ⟨5311095, by rfl⟩ : syracuseStep 14162921 = 10622191) B10622191
theorem B9441947 : Blo 2209435 9441947 := bstep (se 1 (by rfl) ⟨7081460, by rfl⟩ : syracuseStep 9441947 = 14162921) B14162921
theorem B6294631 : Blo 2209435 6294631 := bstep (se 1 (by rfl) ⟨4720973, by rfl⟩ : syracuseStep 6294631 = 9441947) B9441947
theorem B8392841 : Blo 2209435 8392841 := bstep (se 2 (by rfl) ⟨3147315, by rfl⟩ : syracuseStep 8392841 = 6294631) B6294631
theorem B5595227 : Blo 2209435 5595227 := bstep (se 1 (by rfl) ⟨4196420, by rfl⟩ : syracuseStep 5595227 = 8392841) B8392841
theorem B3730151 : Blo 2209435 3730151 := bstep (se 1 (by rfl) ⟨2797613, by rfl⟩ : syracuseStep 3730151 = 5595227) B5595227
theorem B2486767 : Blo 2209435 2486767 := bstep (se 1 (by rfl) ⟨1865075, by rfl⟩ : syracuseStep 2486767 = 3730151) B3730151
theorem B3315689 : Blo 2209435 3315689 := bstep (se 2 (by rfl) ⟨1243383, by rfl⟩ : syracuseStep 3315689 = 2486767) B2486767
theorem B2210459 : Blo 2209435 2210459 := bstep (se 1 (by rfl) ⟨1657844, by rfl⟩ : syracuseStep 2210459 = 3315689) B3315689
theorem B18883925 : Blo 2209435 18883925 := bbase (se 12 (by rfl) ⟨6915, by rfl⟩ : syracuseStep 18883925 = 13831) (by norm_num)
theorem B12589283 : Blo 2209435 12589283 := bstep (se 1 (by rfl) ⟨9441962, by rfl⟩ : syracuseStep 12589283 = 18883925) B18883925
theorem B8392855 : Blo 2209435 8392855 := bstep (se 1 (by rfl) ⟨6294641, by rfl⟩ : syracuseStep 8392855 = 12589283) B12589283
theorem B11190473 : Blo 2209435 11190473 := bstep (se 2 (by rfl) ⟨4196427, by rfl⟩ : syracuseStep 11190473 = 8392855) B8392855
theorem B7460315 : Blo 2209435 7460315 := bstep (se 1 (by rfl) ⟨5595236, by rfl⟩ : syracuseStep 7460315 = 11190473) B11190473
theorem B4973543 : Blo 2209435 4973543 := bstep (se 1 (by rfl) ⟨3730157, by rfl⟩ : syracuseStep 4973543 = 7460315) B7460315
theorem B3315695 : Blo 2209435 3315695 := bstep (se 1 (by rfl) ⟨2486771, by rfl⟩ : syracuseStep 3315695 = 4973543) B4973543
theorem B2210463 : Blo 2209435 2210463 := bstep (se 1 (by rfl) ⟨1657847, by rfl⟩ : syracuseStep 2210463 = 3315695) B3315695
theorem B3315701 : Blo 2209435 3315701 := bbase (se 5 (by rfl) ⟨155423, by rfl⟩ : syracuseStep 3315701 = 310847) (by norm_num)
theorem B2210467 : Blo 2209435 2210467 := bstep (se 1 (by rfl) ⟨1657850, by rfl⟩ : syracuseStep 2210467 = 3315701) B3315701
theorem B22686389 : Blo 2209435 22686389 := bbase (se 5 (by rfl) ⟨1063424, by rfl⟩ : syracuseStep 22686389 = 2126849) (by norm_num)
theorem B15124259 : Blo 2209435 15124259 := bstep (se 1 (by rfl) ⟨11343194, by rfl⟩ : syracuseStep 15124259 = 22686389) B22686389
theorem B40331357 : Blo 2209435 40331357 := bstep (se 3 (by rfl) ⟨7562129, by rfl⟩ : syracuseStep 40331357 = 15124259) B15124259
theorem B26887571 : Blo 2209435 26887571 := bstep (se 1 (by rfl) ⟨20165678, by rfl⟩ : syracuseStep 26887571 = 40331357) B40331357
theorem B17925047 : Blo 2209435 17925047 := bstep (se 1 (by rfl) ⟨13443785, by rfl⟩ : syracuseStep 17925047 = 26887571) B26887571
theorem B11950031 : Blo 2209435 11950031 := bstep (se 1 (by rfl) ⟨8962523, by rfl⟩ : syracuseStep 11950031 = 17925047) B17925047
theorem B7966687 : Blo 2209435 7966687 := bstep (se 1 (by rfl) ⟨5975015, by rfl⟩ : syracuseStep 7966687 = 11950031) B11950031
theorem B10622249 : Blo 2209435 10622249 := bstep (se 2 (by rfl) ⟨3983343, by rfl⟩ : syracuseStep 10622249 = 7966687) B7966687
theorem B7081499 : Blo 2209435 7081499 := bstep (se 1 (by rfl) ⟨5311124, by rfl⟩ : syracuseStep 7081499 = 10622249) B10622249
theorem B4720999 : Blo 2209435 4720999 := bstep (se 1 (by rfl) ⟨3540749, by rfl⟩ : syracuseStep 4720999 = 7081499) B7081499
theorem B6294665 : Blo 2209435 6294665 := bstep (se 2 (by rfl) ⟨2360499, by rfl⟩ : syracuseStep 6294665 = 4720999) B4720999
theorem B4196443 : Blo 2209435 4196443 := bstep (se 1 (by rfl) ⟨3147332, by rfl⟩ : syracuseStep 4196443 = 6294665) B6294665
theorem B5595257 : Blo 2209435 5595257 := bstep (se 2 (by rfl) ⟨2098221, by rfl⟩ : syracuseStep 5595257 = 4196443) B4196443
theorem B3730171 : Blo 2209435 3730171 := bstep (se 1 (by rfl) ⟨2797628, by rfl⟩ : syracuseStep 3730171 = 5595257) B5595257
theorem B4973561 : Blo 2209435 4973561 := bstep (se 2 (by rfl) ⟨1865085, by rfl⟩ : syracuseStep 4973561 = 3730171) B3730171
theorem B3315707 : Blo 2209435 3315707 := bstep (se 1 (by rfl) ⟨2486780, by rfl⟩ : syracuseStep 3315707 = 4973561) B4973561
theorem B2210471 : Blo 2209435 2210471 := bstep (se 1 (by rfl) ⟨1657853, by rfl⟩ : syracuseStep 2210471 = 3315707) B3315707
theorem B2486785 : Blo 2209435 2486785 := bbase (se 2 (by rfl) ⟨932544, by rfl⟩ : syracuseStep 2486785 = 1865089) (by norm_num)
theorem B3315713 : Blo 2209435 3315713 := bstep (se 2 (by rfl) ⟨1243392, by rfl⟩ : syracuseStep 3315713 = 2486785) B2486785
theorem B2210475 : Blo 2209435 2210475 := bstep (se 1 (by rfl) ⟨1657856, by rfl⟩ : syracuseStep 2210475 = 3315713) B3315713
theorem B5595277 : Blo 2209435 5595277 := bbase (se 3 (by rfl) ⟨1049114, by rfl⟩ : syracuseStep 5595277 = 2098229) (by norm_num)
theorem B7460369 : Blo 2209435 7460369 := bstep (se 2 (by rfl) ⟨2797638, by rfl⟩ : syracuseStep 7460369 = 5595277) B5595277
theorem B4973579 : Blo 2209435 4973579 := bstep (se 1 (by rfl) ⟨3730184, by rfl⟩ : syracuseStep 4973579 = 7460369) B7460369
theorem B3315719 : Blo 2209435 3315719 := bstep (se 1 (by rfl) ⟨2486789, by rfl⟩ : syracuseStep 3315719 = 4973579) B4973579
theorem B2210479 : Blo 2209435 2210479 := bstep (se 1 (by rfl) ⟨1657859, by rfl⟩ : syracuseStep 2210479 = 3315719) B3315719
theorem B3315725 : Blo 2209435 3315725 := bbase (se 3 (by rfl) ⟨621698, by rfl⟩ : syracuseStep 3315725 = 1243397) (by norm_num)
theorem B2210483 : Blo 2209435 2210483 := bstep (se 1 (by rfl) ⟨1657862, by rfl⟩ : syracuseStep 2210483 = 3315725) B3315725
theorem B4973597 : Blo 2209435 4973597 := bbase (se 3 (by rfl) ⟨932549, by rfl⟩ : syracuseStep 4973597 = 1865099) (by norm_num)
theorem B3315731 : Blo 2209435 3315731 := bstep (se 1 (by rfl) ⟨2486798, by rfl⟩ : syracuseStep 3315731 = 4973597) B4973597
theorem B2210487 : Blo 2209435 2210487 := bstep (se 1 (by rfl) ⟨1657865, by rfl⟩ : syracuseStep 2210487 = 3315731) B3315731
theorem B3730205 : Blo 2209435 3730205 := bbase (se 3 (by rfl) ⟨699413, by rfl⟩ : syracuseStep 3730205 = 1398827) (by norm_num)
theorem B2486803 : Blo 2209435 2486803 := bstep (se 1 (by rfl) ⟨1865102, by rfl⟩ : syracuseStep 2486803 = 3730205) B3730205
theorem B3315737 : Blo 2209435 3315737 := bstep (se 2 (by rfl) ⟨1243401, by rfl⟩ : syracuseStep 3315737 = 2486803) B2486803
theorem B2210491 : Blo 2209435 2210491 := bstep (se 1 (by rfl) ⟨1657868, by rfl⟩ : syracuseStep 2210491 = 3315737) B3315737
theorem B5311181 : Blo 2209435 5311181 := bbase (se 3 (by rfl) ⟨995846, by rfl⟩ : syracuseStep 5311181 = 1991693) (by norm_num)
theorem B14163149 : Blo 2209435 14163149 := bstep (se 3 (by rfl) ⟨2655590, by rfl⟩ : syracuseStep 14163149 = 5311181) B5311181
theorem B9442099 : Blo 2209435 9442099 := bstep (se 1 (by rfl) ⟨7081574, by rfl⟩ : syracuseStep 9442099 = 14163149) B14163149
theorem B12589465 : Blo 2209435 12589465 := bstep (se 2 (by rfl) ⟨4721049, by rfl⟩ : syracuseStep 12589465 = 9442099) B9442099
theorem B16785953 : Blo 2209435 16785953 := bstep (se 2 (by rfl) ⟨6294732, by rfl⟩ : syracuseStep 16785953 = 12589465) B12589465
theorem B11190635 : Blo 2209435 11190635 := bstep (se 1 (by rfl) ⟨8392976, by rfl⟩ : syracuseStep 11190635 = 16785953) B16785953
theorem B7460423 : Blo 2209435 7460423 := bstep (se 1 (by rfl) ⟨5595317, by rfl⟩ : syracuseStep 7460423 = 11190635) B11190635
theorem B4973615 : Blo 2209435 4973615 := bstep (se 1 (by rfl) ⟨3730211, by rfl⟩ : syracuseStep 4973615 = 7460423) B7460423
theorem B3315743 : Blo 2209435 3315743 := bstep (se 1 (by rfl) ⟨2486807, by rfl⟩ : syracuseStep 3315743 = 4973615) B4973615
theorem B2210495 : Blo 2209435 2210495 := bstep (se 1 (by rfl) ⟨1657871, by rfl⟩ : syracuseStep 2210495 = 3315743) B3315743
theorem B3315749 : Blo 2209435 3315749 := bbase (se 4 (by rfl) ⟨310851, by rfl⟩ : syracuseStep 3315749 = 621703) (by norm_num)
theorem B2210499 : Blo 2209435 2210499 := bstep (se 1 (by rfl) ⟨1657874, by rfl⟩ : syracuseStep 2210499 = 3315749) B3315749
theorem B2797669 : Blo 2209435 2797669 := bbase (se 4 (by rfl) ⟨262281, by rfl⟩ : syracuseStep 2797669 = 524563) (by norm_num)
theorem B3730225 : Blo 2209435 3730225 := bstep (se 2 (by rfl) ⟨1398834, by rfl⟩ : syracuseStep 3730225 = 2797669) B2797669
theorem B4973633 : Blo 2209435 4973633 := bstep (se 2 (by rfl) ⟨1865112, by rfl⟩ : syracuseStep 4973633 = 3730225) B3730225
theorem B3315755 : Blo 2209435 3315755 := bstep (se 1 (by rfl) ⟨2486816, by rfl⟩ : syracuseStep 3315755 = 4973633) B4973633
theorem B2210503 : Blo 2209435 2210503 := bstep (se 1 (by rfl) ⟨1657877, by rfl⟩ : syracuseStep 2210503 = 3315755) B3315755
theorem B2486821 : Blo 2209435 2486821 := bbase (se 4 (by rfl) ⟨233139, by rfl⟩ : syracuseStep 2486821 = 466279) (by norm_num)
theorem B3315761 : Blo 2209435 3315761 := bstep (se 2 (by rfl) ⟨1243410, by rfl⟩ : syracuseStep 3315761 = 2486821) B2486821
theorem B2210507 : Blo 2209435 2210507 := bstep (se 1 (by rfl) ⟨1657880, by rfl⟩ : syracuseStep 2210507 = 3315761) B3315761
theorem B28712981 : Blo 2209435 28712981 := bbase (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) (by norm_num)
theorem B76567949 : Blo 2209435 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B51045299 : Blo 2209435 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B34030199 : Blo 2209435 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B22686799 : Blo 2209435 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B30249065 : Blo 2209435 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B20166043 : Blo 2209435 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B26888057 : Blo 2209435 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B17925371 : Blo 2209435 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B11950247 : Blo 2209435 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B7966831 : Blo 2209435 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B10622441 : Blo 2209435 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B7081627 : Blo 2209435 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B9442169 : Blo 2209435 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B6294779 : Blo 2209435 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B4196519 : Blo 2209435 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B2797679 : Blo 2209435 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B7460477 : Blo 2209435 7460477 := bstep (se 3 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 7460477 = 2797679) B2797679
theorem B4973651 : Blo 2209435 4973651 := bstep (se 1 (by rfl) ⟨3730238, by rfl⟩ : syracuseStep 4973651 = 7460477) B7460477
theorem B3315767 : Blo 2209435 3315767 := bstep (se 1 (by rfl) ⟨2486825, by rfl⟩ : syracuseStep 3315767 = 4973651) B4973651
theorem B2210511 : Blo 2209435 2210511 := bstep (se 1 (by rfl) ⟨1657883, by rfl⟩ : syracuseStep 2210511 = 3315767) B3315767
theorem B3315773 : Blo 2209435 3315773 := bbase (se 3 (by rfl) ⟨621707, by rfl⟩ : syracuseStep 3315773 = 1243415) (by norm_num)
theorem B2210515 : Blo 2209435 2210515 := bstep (se 1 (by rfl) ⟨1657886, by rfl⟩ : syracuseStep 2210515 = 3315773) B3315773
theorem B4973669 : Blo 2209435 4973669 := bbase (se 4 (by rfl) ⟨466281, by rfl⟩ : syracuseStep 4973669 = 932563) (by norm_num)
theorem B3315779 : Blo 2209435 3315779 := bstep (se 1 (by rfl) ⟨2486834, by rfl⟩ : syracuseStep 3315779 = 4973669) B4973669
theorem B2210519 : Blo 2209435 2210519 := bstep (se 1 (by rfl) ⟨1657889, by rfl⟩ : syracuseStep 2210519 = 3315779) B3315779
theorem B5595389 : Blo 2209435 5595389 := bbase (se 3 (by rfl) ⟨1049135, by rfl⟩ : syracuseStep 5595389 = 2098271) (by norm_num)
theorem B3730259 : Blo 2209435 3730259 := bstep (se 1 (by rfl) ⟨2797694, by rfl⟩ : syracuseStep 3730259 = 5595389) B5595389
theorem B2486839 : Blo 2209435 2486839 := bstep (se 1 (by rfl) ⟨1865129, by rfl⟩ : syracuseStep 2486839 = 3730259) B3730259
theorem B3315785 : Blo 2209435 3315785 := bstep (se 2 (by rfl) ⟨1243419, by rfl⟩ : syracuseStep 3315785 = 2486839) B2486839
theorem B2210523 : Blo 2209435 2210523 := bstep (se 1 (by rfl) ⟨1657892, by rfl⟩ : syracuseStep 2210523 = 3315785) B3315785
theorem B4196549 : Blo 2209435 4196549 := bbase (se 4 (by rfl) ⟨393426, by rfl⟩ : syracuseStep 4196549 = 786853) (by norm_num)
theorem B11190797 : Blo 2209435 11190797 := bstep (se 3 (by rfl) ⟨2098274, by rfl⟩ : syracuseStep 11190797 = 4196549) B4196549
theorem B7460531 : Blo 2209435 7460531 := bstep (se 1 (by rfl) ⟨5595398, by rfl⟩ : syracuseStep 7460531 = 11190797) B11190797
theorem B4973687 : Blo 2209435 4973687 := bstep (se 1 (by rfl) ⟨3730265, by rfl⟩ : syracuseStep 4973687 = 7460531) B7460531
theorem B3315791 : Blo 2209435 3315791 := bstep (se 1 (by rfl) ⟨2486843, by rfl⟩ : syracuseStep 3315791 = 4973687) B4973687
theorem B2210527 : Blo 2209435 2210527 := bstep (se 1 (by rfl) ⟨1657895, by rfl⟩ : syracuseStep 2210527 = 3315791) B3315791
theorem B3315797 : Blo 2209435 3315797 := bbase (se 8 (by rfl) ⟨19428, by rfl⟩ : syracuseStep 3315797 = 38857) (by norm_num)
theorem B2210531 : Blo 2209435 2210531 := bstep (se 1 (by rfl) ⟨1657898, by rfl⟩ : syracuseStep 2210531 = 3315797) B3315797
theorem B2425421 : Blo 2209435 2425421 := bbase (se 3 (by rfl) ⟨454766, by rfl⟩ : syracuseStep 2425421 = 909533) (by norm_num)
theorem B6467789 : Blo 2209435 6467789 := bstep (se 3 (by rfl) ⟨1212710, by rfl⟩ : syracuseStep 6467789 = 2425421) B2425421
theorem B4311859 : Blo 2209435 4311859 := bstep (se 1 (by rfl) ⟨3233894, by rfl⟩ : syracuseStep 4311859 = 6467789) B6467789
theorem B5749145 : Blo 2209435 5749145 := bstep (se 2 (by rfl) ⟨2155929, by rfl⟩ : syracuseStep 5749145 = 4311859) B4311859
theorem B3832763 : Blo 2209435 3832763 := bstep (se 1 (by rfl) ⟨2874572, by rfl⟩ : syracuseStep 3832763 = 5749145) B5749145
theorem B10220701 : Blo 2209435 10220701 := bstep (se 3 (by rfl) ⟨1916381, by rfl⟩ : syracuseStep 10220701 = 3832763) B3832763
theorem B13627601 : Blo 2209435 13627601 := bstep (se 2 (by rfl) ⟨5110350, by rfl⟩ : syracuseStep 13627601 = 10220701) B10220701
theorem B9085067 : Blo 2209435 9085067 := bstep (se 1 (by rfl) ⟨6813800, by rfl⟩ : syracuseStep 9085067 = 13627601) B13627601
theorem B6056711 : Blo 2209435 6056711 := bstep (se 1 (by rfl) ⟨4542533, by rfl⟩ : syracuseStep 6056711 = 9085067) B9085067
theorem B4037807 : Blo 2209435 4037807 := bstep (se 1 (by rfl) ⟨3028355, by rfl⟩ : syracuseStep 4037807 = 6056711) B6056711
theorem B10767485 : Blo 2209435 10767485 := bstep (se 3 (by rfl) ⟨2018903, by rfl⟩ : syracuseStep 10767485 = 4037807) B4037807
theorem B7178323 : Blo 2209435 7178323 := bstep (se 1 (by rfl) ⟨5383742, by rfl⟩ : syracuseStep 7178323 = 10767485) B10767485
theorem B9571097 : Blo 2209435 9571097 := bstep (se 2 (by rfl) ⟨3589161, by rfl⟩ : syracuseStep 9571097 = 7178323) B7178323
theorem B6380731 : Blo 2209435 6380731 := bstep (se 1 (by rfl) ⟨4785548, by rfl⟩ : syracuseStep 6380731 = 9571097) B9571097
theorem B8507641 : Blo 2209435 8507641 := bstep (se 2 (by rfl) ⟨3190365, by rfl⟩ : syracuseStep 8507641 = 6380731) B6380731
theorem B11343521 : Blo 2209435 11343521 := bstep (se 2 (by rfl) ⟨4253820, by rfl⟩ : syracuseStep 11343521 = 8507641) B8507641
theorem B30249389 : Blo 2209435 30249389 := bstep (se 3 (by rfl) ⟨5671760, by rfl⟩ : syracuseStep 30249389 = 11343521) B11343521
theorem B20166259 : Blo 2209435 20166259 := bstep (se 1 (by rfl) ⟨15124694, by rfl⟩ : syracuseStep 20166259 = 30249389) B30249389
theorem B26888345 : Blo 2209435 26888345 := bstep (se 2 (by rfl) ⟨10083129, by rfl⟩ : syracuseStep 26888345 = 20166259) B20166259
theorem B17925563 : Blo 2209435 17925563 := bstep (se 1 (by rfl) ⟨13444172, by rfl⟩ : syracuseStep 17925563 = 26888345) B26888345
theorem B47801501 : Blo 2209435 47801501 := bstep (se 3 (by rfl) ⟨8962781, by rfl⟩ : syracuseStep 47801501 = 17925563) B17925563
theorem B31867667 : Blo 2209435 31867667 := bstep (se 1 (by rfl) ⟨23900750, by rfl⟩ : syracuseStep 31867667 = 47801501) B47801501
theorem B21245111 : Blo 2209435 21245111 := bstep (se 1 (by rfl) ⟨15933833, by rfl⟩ : syracuseStep 21245111 = 31867667) B31867667
theorem B14163407 : Blo 2209435 14163407 := bstep (se 1 (by rfl) ⟨10622555, by rfl⟩ : syracuseStep 14163407 = 21245111) B21245111
theorem B9442271 : Blo 2209435 9442271 := bstep (se 1 (by rfl) ⟨7081703, by rfl⟩ : syracuseStep 9442271 = 14163407) B14163407
theorem B6294847 : Blo 2209435 6294847 := bstep (se 1 (by rfl) ⟨4721135, by rfl⟩ : syracuseStep 6294847 = 9442271) B9442271
theorem B8393129 : Blo 2209435 8393129 := bstep (se 2 (by rfl) ⟨3147423, by rfl⟩ : syracuseStep 8393129 = 6294847) B6294847
theorem B5595419 : Blo 2209435 5595419 := bstep (se 1 (by rfl) ⟨4196564, by rfl⟩ : syracuseStep 5595419 = 8393129) B8393129
theorem B3730279 : Blo 2209435 3730279 := bstep (se 1 (by rfl) ⟨2797709, by rfl⟩ : syracuseStep 3730279 = 5595419) B5595419
theorem B4973705 : Blo 2209435 4973705 := bstep (se 2 (by rfl) ⟨1865139, by rfl⟩ : syracuseStep 4973705 = 3730279) B3730279
theorem B3315803 : Blo 2209435 3315803 := bstep (se 1 (by rfl) ⟨2486852, by rfl⟩ : syracuseStep 3315803 = 4973705) B4973705
theorem B2210535 : Blo 2209435 2210535 := bstep (se 1 (by rfl) ⟨1657901, by rfl⟩ : syracuseStep 2210535 = 3315803) B3315803
theorem B2486857 : Blo 2209435 2486857 := bbase (se 2 (by rfl) ⟨932571, by rfl⟩ : syracuseStep 2486857 = 1865143) (by norm_num)
theorem B3315809 : Blo 2209435 3315809 := bstep (se 2 (by rfl) ⟨1243428, by rfl⟩ : syracuseStep 3315809 = 2486857) B2486857
theorem B2210539 : Blo 2209435 2210539 := bstep (se 1 (by rfl) ⟨1657904, by rfl⟩ : syracuseStep 2210539 = 3315809) B3315809
theorem B10220741 : Blo 2209435 10220741 := bbase (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) (by norm_num)
theorem B6813827 : Blo 2209435 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B4542551 : Blo 2209435 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B3028367 : Blo 2209435 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B8075645 : Blo 2209435 8075645 := bstep (se 3 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 8075645 = 3028367) B3028367
theorem B5383763 : Blo 2209435 5383763 := bstep (se 1 (by rfl) ⟨4037822, by rfl⟩ : syracuseStep 5383763 = 8075645) B8075645
theorem B3589175 : Blo 2209435 3589175 := bstep (se 1 (by rfl) ⟨2691881, by rfl⟩ : syracuseStep 3589175 = 5383763) B5383763
theorem B2392783 : Blo 2209435 2392783 := bstep (se 1 (by rfl) ⟨1794587, by rfl⟩ : syracuseStep 2392783 = 3589175) B3589175
theorem B51046037 : Blo 2209435 51046037 := bstep (se 6 (by rfl) ⟨1196391, by rfl⟩ : syracuseStep 51046037 = 2392783) B2392783
theorem B34030691 : Blo 2209435 34030691 := bstep (se 1 (by rfl) ⟨25523018, by rfl⟩ : syracuseStep 34030691 = 51046037) B51046037
theorem B22687127 : Blo 2209435 22687127 := bstep (se 1 (by rfl) ⟨17015345, by rfl⟩ : syracuseStep 22687127 = 34030691) B34030691
theorem B15124751 : Blo 2209435 15124751 := bstep (se 1 (by rfl) ⟨11343563, by rfl⟩ : syracuseStep 15124751 = 22687127) B22687127
theorem B10083167 : Blo 2209435 10083167 := bstep (se 1 (by rfl) ⟨7562375, by rfl⟩ : syracuseStep 10083167 = 15124751) B15124751
theorem B6722111 : Blo 2209435 6722111 := bstep (se 1 (by rfl) ⟨5041583, by rfl⟩ : syracuseStep 6722111 = 10083167) B10083167
theorem B4481407 : Blo 2209435 4481407 := bstep (se 1 (by rfl) ⟨3361055, by rfl⟩ : syracuseStep 4481407 = 6722111) B6722111
theorem B5975209 : Blo 2209435 5975209 := bstep (se 2 (by rfl) ⟨2240703, by rfl⟩ : syracuseStep 5975209 = 4481407) B4481407
theorem B7966945 : Blo 2209435 7966945 := bstep (se 2 (by rfl) ⟨2987604, by rfl⟩ : syracuseStep 7966945 = 5975209) B5975209
theorem B10622593 : Blo 2209435 10622593 := bstep (se 2 (by rfl) ⟨3983472, by rfl⟩ : syracuseStep 10622593 = 7966945) B7966945
theorem B14163457 : Blo 2209435 14163457 := bstep (se 2 (by rfl) ⟨5311296, by rfl⟩ : syracuseStep 14163457 = 10622593) B10622593
theorem B18884609 : Blo 2209435 18884609 := bstep (se 2 (by rfl) ⟨7081728, by rfl⟩ : syracuseStep 18884609 = 14163457) B14163457
theorem B12589739 : Blo 2209435 12589739 := bstep (se 1 (by rfl) ⟨9442304, by rfl⟩ : syracuseStep 12589739 = 18884609) B18884609
theorem B8393159 : Blo 2209435 8393159 := bstep (se 1 (by rfl) ⟨6294869, by rfl⟩ : syracuseStep 8393159 = 12589739) B12589739
theorem B5595439 : Blo 2209435 5595439 := bstep (se 1 (by rfl) ⟨4196579, by rfl⟩ : syracuseStep 5595439 = 8393159) B8393159
theorem B7460585 : Blo 2209435 7460585 := bstep (se 2 (by rfl) ⟨2797719, by rfl⟩ : syracuseStep 7460585 = 5595439) B5595439
theorem B4973723 : Blo 2209435 4973723 := bstep (se 1 (by rfl) ⟨3730292, by rfl⟩ : syracuseStep 4973723 = 7460585) B7460585
theorem B3315815 : Blo 2209435 3315815 := bstep (se 1 (by rfl) ⟨2486861, by rfl⟩ : syracuseStep 3315815 = 4973723) B4973723
theorem B2210543 : Blo 2209435 2210543 := bstep (se 1 (by rfl) ⟨1657907, by rfl⟩ : syracuseStep 2210543 = 3315815) B3315815
theorem B3315821 : Blo 2209435 3315821 := bbase (se 3 (by rfl) ⟨621716, by rfl⟩ : syracuseStep 3315821 = 1243433) (by norm_num)
theorem B2210547 : Blo 2209435 2210547 := bstep (se 1 (by rfl) ⟨1657910, by rfl⟩ : syracuseStep 2210547 = 3315821) B3315821
theorem B4973741 : Blo 2209435 4973741 := bbase (se 3 (by rfl) ⟨932576, by rfl⟩ : syracuseStep 4973741 = 1865153) (by norm_num)
theorem B3315827 : Blo 2209435 3315827 := bstep (se 1 (by rfl) ⟨2486870, by rfl⟩ : syracuseStep 3315827 = 4973741) B4973741
theorem B2210551 : Blo 2209435 2210551 := bstep (se 1 (by rfl) ⟨1657913, by rfl⟩ : syracuseStep 2210551 = 3315827) B3315827
theorem B26888597 : Blo 2209435 26888597 := bbase (se 6 (by rfl) ⟨630201, by rfl⟩ : syracuseStep 26888597 = 1260403) (by norm_num)
theorem B17925731 : Blo 2209435 17925731 := bstep (se 1 (by rfl) ⟨13444298, by rfl⟩ : syracuseStep 17925731 = 26888597) B26888597
theorem B11950487 : Blo 2209435 11950487 := bstep (se 1 (by rfl) ⟨8962865, by rfl⟩ : syracuseStep 11950487 = 17925731) B17925731
theorem B7966991 : Blo 2209435 7966991 := bstep (se 1 (by rfl) ⟨5975243, by rfl⟩ : syracuseStep 7966991 = 11950487) B11950487
theorem B5311327 : Blo 2209435 5311327 := bstep (se 1 (by rfl) ⟨3983495, by rfl⟩ : syracuseStep 5311327 = 7966991) B7966991
theorem B7081769 : Blo 2209435 7081769 := bstep (se 2 (by rfl) ⟨2655663, by rfl⟩ : syracuseStep 7081769 = 5311327) B5311327
theorem B4721179 : Blo 2209435 4721179 := bstep (se 1 (by rfl) ⟨3540884, by rfl⟩ : syracuseStep 4721179 = 7081769) B7081769
theorem B6294905 : Blo 2209435 6294905 := bstep (se 2 (by rfl) ⟨2360589, by rfl⟩ : syracuseStep 6294905 = 4721179) B4721179
theorem B4196603 : Blo 2209435 4196603 := bstep (se 1 (by rfl) ⟨3147452, by rfl⟩ : syracuseStep 4196603 = 6294905) B6294905
theorem B2797735 : Blo 2209435 2797735 := bstep (se 1 (by rfl) ⟨2098301, by rfl⟩ : syracuseStep 2797735 = 4196603) B4196603
theorem B3730313 : Blo 2209435 3730313 := bstep (se 2 (by rfl) ⟨1398867, by rfl⟩ : syracuseStep 3730313 = 2797735) B2797735
theorem B2486875 : Blo 2209435 2486875 := bstep (se 1 (by rfl) ⟨1865156, by rfl⟩ : syracuseStep 2486875 = 3730313) B3730313
theorem B3315833 : Blo 2209435 3315833 := bstep (se 2 (by rfl) ⟨1243437, by rfl⟩ : syracuseStep 3315833 = 2486875) B2486875
theorem B2210555 : Blo 2209435 2210555 := bstep (se 1 (by rfl) ⟨1657916, by rfl⟩ : syracuseStep 2210555 = 3315833) B3315833
theorem B3983501 : Blo 2209435 3983501 := bbase (se 3 (by rfl) ⟨746906, by rfl⟩ : syracuseStep 3983501 = 1493813) (by norm_num)
theorem B10622669 : Blo 2209435 10622669 := bstep (se 3 (by rfl) ⟨1991750, by rfl⟩ : syracuseStep 10622669 = 3983501) B3983501
theorem B28327117 : Blo 2209435 28327117 := bstep (se 3 (by rfl) ⟨5311334, by rfl⟩ : syracuseStep 28327117 = 10622669) B10622669
theorem B37769489 : Blo 2209435 37769489 := bstep (se 2 (by rfl) ⟨14163558, by rfl⟩ : syracuseStep 37769489 = 28327117) B28327117
theorem B25179659 : Blo 2209435 25179659 := bstep (se 1 (by rfl) ⟨18884744, by rfl⟩ : syracuseStep 25179659 = 37769489) B37769489
theorem B16786439 : Blo 2209435 16786439 := bstep (se 1 (by rfl) ⟨12589829, by rfl⟩ : syracuseStep 16786439 = 25179659) B25179659
theorem B11190959 : Blo 2209435 11190959 := bstep (se 1 (by rfl) ⟨8393219, by rfl⟩ : syracuseStep 11190959 = 16786439) B16786439
theorem B7460639 : Blo 2209435 7460639 := bstep (se 1 (by rfl) ⟨5595479, by rfl⟩ : syracuseStep 7460639 = 11190959) B11190959
theorem B4973759 : Blo 2209435 4973759 := bstep (se 1 (by rfl) ⟨3730319, by rfl⟩ : syracuseStep 4973759 = 7460639) B7460639
theorem B3315839 : Blo 2209435 3315839 := bstep (se 1 (by rfl) ⟨2486879, by rfl⟩ : syracuseStep 3315839 = 4973759) B4973759
theorem B2210559 : Blo 2209435 2210559 := bstep (se 1 (by rfl) ⟨1657919, by rfl⟩ : syracuseStep 2210559 = 3315839) B3315839
theorem B3315845 : Blo 2209435 3315845 := bbase (se 4 (by rfl) ⟨310860, by rfl⟩ : syracuseStep 3315845 = 621721) (by norm_num)
theorem B2210563 : Blo 2209435 2210563 := bstep (se 1 (by rfl) ⟨1657922, by rfl⟩ : syracuseStep 2210563 = 3315845) B3315845
theorem B3730333 : Blo 2209435 3730333 := bbase (se 3 (by rfl) ⟨699437, by rfl⟩ : syracuseStep 3730333 = 1398875) (by norm_num)
theorem B4973777 : Blo 2209435 4973777 := bstep (se 2 (by rfl) ⟨1865166, by rfl⟩ : syracuseStep 4973777 = 3730333) B3730333
theorem B3315851 : Blo 2209435 3315851 := bstep (se 1 (by rfl) ⟨2486888, by rfl⟩ : syracuseStep 3315851 = 4973777) B4973777
theorem B2210567 : Blo 2209435 2210567 := bstep (se 1 (by rfl) ⟨1657925, by rfl⟩ : syracuseStep 2210567 = 3315851) B3315851
theorem B2486893 : Blo 2209435 2486893 := bbase (se 3 (by rfl) ⟨466292, by rfl⟩ : syracuseStep 2486893 = 932585) (by norm_num)
theorem B3315857 : Blo 2209435 3315857 := bstep (se 2 (by rfl) ⟨1243446, by rfl⟩ : syracuseStep 3315857 = 2486893) B2486893
theorem B2210571 : Blo 2209435 2210571 := bstep (se 1 (by rfl) ⟨1657928, by rfl⟩ : syracuseStep 2210571 = 3315857) B3315857
theorem B7460693 : Blo 2209435 7460693 := bbase (se 9 (by rfl) ⟨21857, by rfl⟩ : syracuseStep 7460693 = 43715) (by norm_num)
theorem B4973795 : Blo 2209435 4973795 := bstep (se 1 (by rfl) ⟨3730346, by rfl⟩ : syracuseStep 4973795 = 7460693) B7460693
theorem B3315863 : Blo 2209435 3315863 := bstep (se 1 (by rfl) ⟨2486897, by rfl⟩ : syracuseStep 3315863 = 4973795) B4973795
theorem B2210575 : Blo 2209435 2210575 := bstep (se 1 (by rfl) ⟨1657931, by rfl⟩ : syracuseStep 2210575 = 3315863) B3315863
theorem B3315869 : Blo 2209435 3315869 := bbase (se 3 (by rfl) ⟨621725, by rfl⟩ : syracuseStep 3315869 = 1243451) (by norm_num)
theorem B2210579 : Blo 2209435 2210579 := bstep (se 1 (by rfl) ⟨1657934, by rfl⟩ : syracuseStep 2210579 = 3315869) B3315869
theorem B4973813 : Blo 2209435 4973813 := bbase (se 5 (by rfl) ⟨233147, by rfl⟩ : syracuseStep 4973813 = 466295) (by norm_num)
theorem B3315875 : Blo 2209435 3315875 := bstep (se 1 (by rfl) ⟨2486906, by rfl⟩ : syracuseStep 3315875 = 4973813) B4973813
theorem B2210583 : Blo 2209435 2210583 := bstep (se 1 (by rfl) ⟨1657937, by rfl⟩ : syracuseStep 2210583 = 3315875) B3315875
theorem B4785661 : Blo 2209435 4785661 := bbase (se 3 (by rfl) ⟨897311, by rfl⟩ : syracuseStep 4785661 = 1794623) (by norm_num)
theorem B25523525 : Blo 2209435 25523525 := bstep (se 4 (by rfl) ⟨2392830, by rfl⟩ : syracuseStep 25523525 = 4785661) B4785661
theorem B17015683 : Blo 2209435 17015683 := bstep (se 1 (by rfl) ⟨12761762, by rfl⟩ : syracuseStep 17015683 = 25523525) B25523525
theorem B22687577 : Blo 2209435 22687577 := bstep (se 2 (by rfl) ⟨8507841, by rfl⟩ : syracuseStep 22687577 = 17015683) B17015683
theorem B15125051 : Blo 2209435 15125051 := bstep (se 1 (by rfl) ⟨11343788, by rfl⟩ : syracuseStep 15125051 = 22687577) B22687577
theorem B10083367 : Blo 2209435 10083367 := bstep (se 1 (by rfl) ⟨7562525, by rfl⟩ : syracuseStep 10083367 = 15125051) B15125051
theorem B13444489 : Blo 2209435 13444489 := bstep (se 2 (by rfl) ⟨5041683, by rfl⟩ : syracuseStep 13444489 = 10083367) B10083367
theorem B17925985 : Blo 2209435 17925985 := bstep (se 2 (by rfl) ⟨6722244, by rfl⟩ : syracuseStep 17925985 = 13444489) B13444489
theorem B23901313 : Blo 2209435 23901313 := bstep (se 2 (by rfl) ⟨8962992, by rfl⟩ : syracuseStep 23901313 = 17925985) B17925985
theorem B31868417 : Blo 2209435 31868417 := bstep (se 2 (by rfl) ⟨11950656, by rfl⟩ : syracuseStep 31868417 = 23901313) B23901313
theorem B21245611 : Blo 2209435 21245611 := bstep (se 1 (by rfl) ⟨15934208, by rfl⟩ : syracuseStep 21245611 = 31868417) B31868417
theorem B28327481 : Blo 2209435 28327481 := bstep (se 2 (by rfl) ⟨10622805, by rfl⟩ : syracuseStep 28327481 = 21245611) B21245611
theorem B18884987 : Blo 2209435 18884987 := bstep (se 1 (by rfl) ⟨14163740, by rfl⟩ : syracuseStep 18884987 = 28327481) B28327481
theorem B12589991 : Blo 2209435 12589991 := bstep (se 1 (by rfl) ⟨9442493, by rfl⟩ : syracuseStep 12589991 = 18884987) B18884987
theorem B8393327 : Blo 2209435 8393327 := bstep (se 1 (by rfl) ⟨6294995, by rfl⟩ : syracuseStep 8393327 = 12589991) B12589991
theorem B5595551 : Blo 2209435 5595551 := bstep (se 1 (by rfl) ⟨4196663, by rfl⟩ : syracuseStep 5595551 = 8393327) B8393327
theorem B3730367 : Blo 2209435 3730367 := bstep (se 1 (by rfl) ⟨2797775, by rfl⟩ : syracuseStep 3730367 = 5595551) B5595551
theorem B2486911 : Blo 2209435 2486911 := bstep (se 1 (by rfl) ⟨1865183, by rfl⟩ : syracuseStep 2486911 = 3730367) B3730367
theorem B3315881 : Blo 2209435 3315881 := bstep (se 2 (by rfl) ⟨1243455, by rfl⟩ : syracuseStep 3315881 = 2486911) B2486911
theorem B2210587 : Blo 2209435 2210587 := bstep (se 1 (by rfl) ⟨1657940, by rfl⟩ : syracuseStep 2210587 = 3315881) B3315881
theorem B5041693 : Blo 2209435 5041693 := bbase (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) (by norm_num)
theorem B26889029 : Blo 2209435 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B17926019 : Blo 2209435 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B11950679 : Blo 2209435 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B7967119 : Blo 2209435 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B10622825 : Blo 2209435 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B7081883 : Blo 2209435 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B4721255 : Blo 2209435 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B3147503 : Blo 2209435 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B8393341 : Blo 2209435 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B11191121 : Blo 2209435 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B7460747 : Blo 2209435 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B4973831 : Blo 2209435 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B3315887 : Blo 2209435 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B2210591 : Blo 2209435 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B3315893 : Blo 2209435 3315893 := bbase (se 5 (by rfl) ⟨155432, by rfl⟩ : syracuseStep 3315893 = 310865) (by norm_num)
theorem B2210595 : Blo 2209435 2210595 := bstep (se 1 (by rfl) ⟨1657946, by rfl⟩ : syracuseStep 2210595 = 3315893) B3315893
theorem B5595581 : Blo 2209435 5595581 := bbase (se 3 (by rfl) ⟨1049171, by rfl⟩ : syracuseStep 5595581 = 2098343) (by norm_num)
theorem B3730387 : Blo 2209435 3730387 := bstep (se 1 (by rfl) ⟨2797790, by rfl⟩ : syracuseStep 3730387 = 5595581) B5595581
theorem B4973849 : Blo 2209435 4973849 := bstep (se 2 (by rfl) ⟨1865193, by rfl⟩ : syracuseStep 4973849 = 3730387) B3730387
theorem B3315899 : Blo 2209435 3315899 := bstep (se 1 (by rfl) ⟨2486924, by rfl⟩ : syracuseStep 3315899 = 4973849) B4973849
theorem B2210599 : Blo 2209435 2210599 := bstep (se 1 (by rfl) ⟨1657949, by rfl⟩ : syracuseStep 2210599 = 3315899) B3315899
theorem B2486929 : Blo 2209435 2486929 := bbase (se 2 (by rfl) ⟨932598, by rfl⟩ : syracuseStep 2486929 = 1865197) (by norm_num)
theorem B3315905 : Blo 2209435 3315905 := bstep (se 2 (by rfl) ⟨1243464, by rfl⟩ : syracuseStep 3315905 = 2486929) B2486929
theorem B2210603 : Blo 2209435 2210603 := bstep (se 1 (by rfl) ⟨1657952, by rfl⟩ : syracuseStep 2210603 = 3315905) B3315905
theorem B4196701 : Blo 2209435 4196701 := bbase (se 3 (by rfl) ⟨786881, by rfl⟩ : syracuseStep 4196701 = 1573763) (by norm_num)
theorem B5595601 : Blo 2209435 5595601 := bstep (se 2 (by rfl) ⟨2098350, by rfl⟩ : syracuseStep 5595601 = 4196701) B4196701
theorem B7460801 : Blo 2209435 7460801 := bstep (se 2 (by rfl) ⟨2797800, by rfl⟩ : syracuseStep 7460801 = 5595601) B5595601
theorem B4973867 : Blo 2209435 4973867 := bstep (se 1 (by rfl) ⟨3730400, by rfl⟩ : syracuseStep 4973867 = 7460801) B7460801
theorem B3315911 : Blo 2209435 3315911 := bstep (se 1 (by rfl) ⟨2486933, by rfl⟩ : syracuseStep 3315911 = 4973867) B4973867
theorem B2210607 : Blo 2209435 2210607 := bstep (se 1 (by rfl) ⟨1657955, by rfl⟩ : syracuseStep 2210607 = 3315911) B3315911
theorem B3315917 : Blo 2209435 3315917 := bbase (se 3 (by rfl) ⟨621734, by rfl⟩ : syracuseStep 3315917 = 1243469) (by norm_num)
theorem B2210611 : Blo 2209435 2210611 := bstep (se 1 (by rfl) ⟨1657958, by rfl⟩ : syracuseStep 2210611 = 3315917) B3315917
theorem B4973885 : Blo 2209435 4973885 := bbase (se 3 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 4973885 = 1865207) (by norm_num)
theorem B3315923 : Blo 2209435 3315923 := bstep (se 1 (by rfl) ⟨2486942, by rfl⟩ : syracuseStep 3315923 = 4973885) B4973885
theorem B2210615 : Blo 2209435 2210615 := bstep (se 1 (by rfl) ⟨1657961, by rfl⟩ : syracuseStep 2210615 = 3315923) B3315923
theorem B3730421 : Blo 2209435 3730421 := bbase (se 5 (by rfl) ⟨174863, by rfl⟩ : syracuseStep 3730421 = 349727) (by norm_num)
theorem B2486947 : Blo 2209435 2486947 := bstep (se 1 (by rfl) ⟨1865210, by rfl⟩ : syracuseStep 2486947 = 3730421) B3730421
theorem B3315929 : Blo 2209435 3315929 := bstep (se 2 (by rfl) ⟨1243473, by rfl⟩ : syracuseStep 3315929 = 2486947) B2486947
theorem B2210619 : Blo 2209435 2210619 := bstep (se 1 (by rfl) ⟨1657964, by rfl⟩ : syracuseStep 2210619 = 3315929) B3315929
theorem B2240785 : Blo 2209435 2240785 := bbase (se 2 (by rfl) ⟨840294, by rfl⟩ : syracuseStep 2240785 = 1680589) (by norm_num)
theorem B2987713 : Blo 2209435 2987713 := bstep (se 2 (by rfl) ⟨1120392, by rfl⟩ : syracuseStep 2987713 = 2240785) B2240785
theorem B3983617 : Blo 2209435 3983617 := bstep (se 2 (by rfl) ⟨1493856, by rfl⟩ : syracuseStep 3983617 = 2987713) B2987713
theorem B5311489 : Blo 2209435 5311489 := bstep (se 2 (by rfl) ⟨1991808, by rfl⟩ : syracuseStep 5311489 = 3983617) B3983617
theorem B7081985 : Blo 2209435 7081985 := bstep (se 2 (by rfl) ⟨2655744, by rfl⟩ : syracuseStep 7081985 = 5311489) B5311489
theorem B4721323 : Blo 2209435 4721323 := bstep (se 1 (by rfl) ⟨3540992, by rfl⟩ : syracuseStep 4721323 = 7081985) B7081985
theorem B6295097 : Blo 2209435 6295097 := bstep (se 2 (by rfl) ⟨2360661, by rfl⟩ : syracuseStep 6295097 = 4721323) B4721323
theorem B16786925 : Blo 2209435 16786925 := bstep (se 3 (by rfl) ⟨3147548, by rfl⟩ : syracuseStep 16786925 = 6295097) B6295097
theorem B11191283 : Blo 2209435 11191283 := bstep (se 1 (by rfl) ⟨8393462, by rfl⟩ : syracuseStep 11191283 = 16786925) B16786925
theorem B7460855 : Blo 2209435 7460855 := bstep (se 1 (by rfl) ⟨5595641, by rfl⟩ : syracuseStep 7460855 = 11191283) B11191283
theorem B4973903 : Blo 2209435 4973903 := bstep (se 1 (by rfl) ⟨3730427, by rfl⟩ : syracuseStep 4973903 = 7460855) B7460855
theorem B3315935 : Blo 2209435 3315935 := bstep (se 1 (by rfl) ⟨2486951, by rfl⟩ : syracuseStep 3315935 = 4973903) B4973903
theorem B2210623 : Blo 2209435 2210623 := bstep (se 1 (by rfl) ⟨1657967, by rfl⟩ : syracuseStep 2210623 = 3315935) B3315935
theorem B3315941 : Blo 2209435 3315941 := bbase (se 4 (by rfl) ⟨310869, by rfl⟩ : syracuseStep 3315941 = 621739) (by norm_num)
theorem B2210627 : Blo 2209435 2210627 := bstep (se 1 (by rfl) ⟨1657970, by rfl⟩ : syracuseStep 2210627 = 3315941) B3315941
theorem B4721341 : Blo 2209435 4721341 := bbase (se 3 (by rfl) ⟨885251, by rfl⟩ : syracuseStep 4721341 = 1770503) (by norm_num)
theorem B6295121 : Blo 2209435 6295121 := bstep (se 2 (by rfl) ⟨2360670, by rfl⟩ : syracuseStep 6295121 = 4721341) B4721341
theorem B4196747 : Blo 2209435 4196747 := bstep (se 1 (by rfl) ⟨3147560, by rfl⟩ : syracuseStep 4196747 = 6295121) B6295121
theorem B2797831 : Blo 2209435 2797831 := bstep (se 1 (by rfl) ⟨2098373, by rfl⟩ : syracuseStep 2797831 = 4196747) B4196747
theorem B3730441 : Blo 2209435 3730441 := bstep (se 2 (by rfl) ⟨1398915, by rfl⟩ : syracuseStep 3730441 = 2797831) B2797831
theorem B4973921 : Blo 2209435 4973921 := bstep (se 2 (by rfl) ⟨1865220, by rfl⟩ : syracuseStep 4973921 = 3730441) B3730441
theorem B3315947 : Blo 2209435 3315947 := bstep (se 1 (by rfl) ⟨2486960, by rfl⟩ : syracuseStep 3315947 = 4973921) B4973921
theorem B2210631 : Blo 2209435 2210631 := bstep (se 1 (by rfl) ⟨1657973, by rfl⟩ : syracuseStep 2210631 = 3315947) B3315947
theorem B2486965 : Blo 2209435 2486965 := bbase (se 5 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 2486965 = 233153) (by norm_num)
theorem B3315953 : Blo 2209435 3315953 := bstep (se 2 (by rfl) ⟨1243482, by rfl⟩ : syracuseStep 3315953 = 2486965) B2486965
theorem B2210635 : Blo 2209435 2210635 := bstep (se 1 (by rfl) ⟨1657976, by rfl⟩ : syracuseStep 2210635 = 3315953) B3315953
theorem B2797841 : Blo 2209435 2797841 := bbase (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) (by norm_num)
theorem B7460909 : Blo 2209435 7460909 := bstep (se 3 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 7460909 = 2797841) B2797841
theorem B4973939 : Blo 2209435 4973939 := bstep (se 1 (by rfl) ⟨3730454, by rfl⟩ : syracuseStep 4973939 = 7460909) B7460909
theorem B3315959 : Blo 2209435 3315959 := bstep (se 1 (by rfl) ⟨2486969, by rfl⟩ : syracuseStep 3315959 = 4973939) B4973939
theorem B2210639 : Blo 2209435 2210639 := bstep (se 1 (by rfl) ⟨1657979, by rfl⟩ : syracuseStep 2210639 = 3315959) B3315959
theorem B3315965 : Blo 2209435 3315965 := bbase (se 3 (by rfl) ⟨621743, by rfl⟩ : syracuseStep 3315965 = 1243487) (by norm_num)
theorem B2210643 : Blo 2209435 2210643 := bstep (se 1 (by rfl) ⟨1657982, by rfl⟩ : syracuseStep 2210643 = 3315965) B3315965
theorem B4973957 : Blo 2209435 4973957 := bbase (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) (by norm_num)
theorem B3315971 : Blo 2209435 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B2210647 : Blo 2209435 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B3147589 : Blo 2209435 3147589 := bbase (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) (by norm_num)
theorem B4196785 : Blo 2209435 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B5595713 : Blo 2209435 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B3730475 : Blo 2209435 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B2486983 : Blo 2209435 2486983 := bstep (se 1 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 2486983 = 3730475) B3730475
theorem B3315977 : Blo 2209435 3315977 := bstep (se 2 (by rfl) ⟨1243491, by rfl⟩ : syracuseStep 3315977 = 2486983) B2486983
theorem B2210651 : Blo 2209435 2210651 := bstep (se 1 (by rfl) ⟨1657988, by rfl⟩ : syracuseStep 2210651 = 3315977) B3315977
theorem B11191445 : Blo 2209435 11191445 := bbase (se 6 (by rfl) ⟨262299, by rfl⟩ : syracuseStep 11191445 = 524599) (by norm_num)
theorem B7460963 : Blo 2209435 7460963 := bstep (se 1 (by rfl) ⟨5595722, by rfl⟩ : syracuseStep 7460963 = 11191445) B11191445
theorem B4973975 : Blo 2209435 4973975 := bstep (se 1 (by rfl) ⟨3730481, by rfl⟩ : syracuseStep 4973975 = 7460963) B7460963
theorem B3315983 : Blo 2209435 3315983 := bstep (se 1 (by rfl) ⟨2486987, by rfl⟩ : syracuseStep 3315983 = 4973975) B4973975
theorem B2210655 : Blo 2209435 2210655 := bstep (se 1 (by rfl) ⟨1657991, by rfl⟩ : syracuseStep 2210655 = 3315983) B3315983
theorem B3315989 : Blo 2209435 3315989 := bbase (se 6 (by rfl) ⟨77718, by rfl⟩ : syracuseStep 3315989 = 155437) (by norm_num)
theorem B2210659 : Blo 2209435 2210659 := bstep (se 1 (by rfl) ⟨1657994, by rfl⟩ : syracuseStep 2210659 = 3315989) B3315989
theorem B2520929 : Blo 2209435 2520929 := bbase (se 2 (by rfl) ⟨945348, by rfl⟩ : syracuseStep 2520929 = 1890697) (by norm_num)
theorem B6722477 : Blo 2209435 6722477 := bstep (se 3 (by rfl) ⟨1260464, by rfl⟩ : syracuseStep 6722477 = 2520929) B2520929
theorem B4481651 : Blo 2209435 4481651 := bstep (se 1 (by rfl) ⟨3361238, by rfl⟩ : syracuseStep 4481651 = 6722477) B6722477
theorem B2987767 : Blo 2209435 2987767 := bstep (se 1 (by rfl) ⟨2240825, by rfl⟩ : syracuseStep 2987767 = 4481651) B4481651
theorem B3983689 : Blo 2209435 3983689 := bstep (se 2 (by rfl) ⟨1493883, by rfl⟩ : syracuseStep 3983689 = 2987767) B2987767
theorem B5311585 : Blo 2209435 5311585 := bstep (se 2 (by rfl) ⟨1991844, by rfl⟩ : syracuseStep 5311585 = 3983689) B3983689
theorem B28328453 : Blo 2209435 28328453 := bstep (se 4 (by rfl) ⟨2655792, by rfl⟩ : syracuseStep 28328453 = 5311585) B5311585
theorem B18885635 : Blo 2209435 18885635 := bstep (se 1 (by rfl) ⟨14164226, by rfl⟩ : syracuseStep 18885635 = 28328453) B28328453
theorem B12590423 : Blo 2209435 12590423 := bstep (se 1 (by rfl) ⟨9442817, by rfl⟩ : syracuseStep 12590423 = 18885635) B18885635
theorem B8393615 : Blo 2209435 8393615 := bstep (se 1 (by rfl) ⟨6295211, by rfl⟩ : syracuseStep 8393615 = 12590423) B12590423
theorem B5595743 : Blo 2209435 5595743 := bstep (se 1 (by rfl) ⟨4196807, by rfl⟩ : syracuseStep 5595743 = 8393615) B8393615
theorem B3730495 : Blo 2209435 3730495 := bstep (se 1 (by rfl) ⟨2797871, by rfl⟩ : syracuseStep 3730495 = 5595743) B5595743
theorem B4973993 : Blo 2209435 4973993 := bstep (se 2 (by rfl) ⟨1865247, by rfl⟩ : syracuseStep 4973993 = 3730495) B3730495
theorem B3315995 : Blo 2209435 3315995 := bstep (se 1 (by rfl) ⟨2486996, by rfl⟩ : syracuseStep 3315995 = 4973993) B4973993
theorem B2210663 : Blo 2209435 2210663 := bstep (se 1 (by rfl) ⟨1657997, by rfl⟩ : syracuseStep 2210663 = 3315995) B3315995
theorem B2487001 : Blo 2209435 2487001 := bbase (se 2 (by rfl) ⟨932625, by rfl⟩ : syracuseStep 2487001 = 1865251) (by norm_num)
theorem B3316001 : Blo 2209435 3316001 := bstep (se 2 (by rfl) ⟨1243500, by rfl⟩ : syracuseStep 3316001 = 2487001) B2487001
theorem B2210667 : Blo 2209435 2210667 := bstep (se 1 (by rfl) ⟨1658000, by rfl⟩ : syracuseStep 2210667 = 3316001) B3316001
theorem B2360713 : Blo 2209435 2360713 := bbase (se 2 (by rfl) ⟨885267, by rfl⟩ : syracuseStep 2360713 = 1770535) (by norm_num)
theorem B3147617 : Blo 2209435 3147617 := bstep (se 2 (by rfl) ⟨1180356, by rfl⟩ : syracuseStep 3147617 = 2360713) B2360713
theorem B8393645 : Blo 2209435 8393645 := bstep (se 3 (by rfl) ⟨1573808, by rfl⟩ : syracuseStep 8393645 = 3147617) B3147617
theorem B5595763 : Blo 2209435 5595763 := bstep (se 1 (by rfl) ⟨4196822, by rfl⟩ : syracuseStep 5595763 = 8393645) B8393645
theorem B7461017 : Blo 2209435 7461017 := bstep (se 2 (by rfl) ⟨2797881, by rfl⟩ : syracuseStep 7461017 = 5595763) B5595763
theorem B4974011 : Blo 2209435 4974011 := bstep (se 1 (by rfl) ⟨3730508, by rfl⟩ : syracuseStep 4974011 = 7461017) B7461017
theorem B3316007 : Blo 2209435 3316007 := bstep (se 1 (by rfl) ⟨2487005, by rfl⟩ : syracuseStep 3316007 = 4974011) B4974011
theorem B2210671 : Blo 2209435 2210671 := bstep (se 1 (by rfl) ⟨1658003, by rfl⟩ : syracuseStep 2210671 = 3316007) B3316007
theorem B3316013 : Blo 2209435 3316013 := bbase (se 3 (by rfl) ⟨621752, by rfl⟩ : syracuseStep 3316013 = 1243505) (by norm_num)
theorem B2210675 : Blo 2209435 2210675 := bstep (se 1 (by rfl) ⟨1658006, by rfl⟩ : syracuseStep 2210675 = 3316013) B3316013
theorem B4974029 : Blo 2209435 4974029 := bbase (se 3 (by rfl) ⟨932630, by rfl⟩ : syracuseStep 4974029 = 1865261) (by norm_num)
theorem B3316019 : Blo 2209435 3316019 := bstep (se 1 (by rfl) ⟨2487014, by rfl⟩ : syracuseStep 3316019 = 4974029) B4974029
theorem B2210679 : Blo 2209435 2210679 := bstep (se 1 (by rfl) ⟨1658009, by rfl⟩ : syracuseStep 2210679 = 3316019) B3316019
theorem B2797897 : Blo 2209435 2797897 := bbase (se 2 (by rfl) ⟨1049211, by rfl⟩ : syracuseStep 2797897 = 2098423) (by norm_num)
theorem B3730529 : Blo 2209435 3730529 := bstep (se 2 (by rfl) ⟨1398948, by rfl⟩ : syracuseStep 3730529 = 2797897) B2797897
theorem B2487019 : Blo 2209435 2487019 := bstep (se 1 (by rfl) ⟨1865264, by rfl⟩ : syracuseStep 2487019 = 3730529) B3730529
theorem B3316025 : Blo 2209435 3316025 := bstep (se 2 (by rfl) ⟨1243509, by rfl⟩ : syracuseStep 3316025 = 2487019) B2487019
theorem B2210683 : Blo 2209435 2210683 := bstep (se 1 (by rfl) ⟨1658012, by rfl⟩ : syracuseStep 2210683 = 3316025) B3316025
theorem B54514133 : Blo 2209435 54514133 := bbase (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) (by norm_num)
theorem B36342755 : Blo 2209435 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B24228503 : Blo 2209435 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B16152335 : Blo 2209435 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B10768223 : Blo 2209435 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B7178815 : Blo 2209435 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B9571753 : Blo 2209435 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B51049349 : Blo 2209435 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B34032899 : Blo 2209435 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B22688599 : Blo 2209435 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B30251465 : Blo 2209435 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B20167643 : Blo 2209435 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B53780381 : Blo 2209435 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B35853587 : Blo 2209435 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B23902391 : Blo 2209435 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B15934927 : Blo 2209435 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B21246569 : Blo 2209435 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B14164379 : Blo 2209435 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B9442919 : Blo 2209435 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B25181117 : Blo 2209435 25181117 := bstep (se 3 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 25181117 = 9442919) B9442919
theorem B16787411 : Blo 2209435 16787411 := bstep (se 1 (by rfl) ⟨12590558, by rfl⟩ : syracuseStep 16787411 = 25181117) B25181117
theorem B11191607 : Blo 2209435 11191607 := bstep (se 1 (by rfl) ⟨8393705, by rfl⟩ : syracuseStep 11191607 = 16787411) B16787411
theorem B7461071 : Blo 2209435 7461071 := bstep (se 1 (by rfl) ⟨5595803, by rfl⟩ : syracuseStep 7461071 = 11191607) B11191607
theorem B4974047 : Blo 2209435 4974047 := bstep (se 1 (by rfl) ⟨3730535, by rfl⟩ : syracuseStep 4974047 = 7461071) B7461071
theorem B3316031 : Blo 2209435 3316031 := bstep (se 1 (by rfl) ⟨2487023, by rfl⟩ : syracuseStep 3316031 = 4974047) B4974047
theorem B2210687 : Blo 2209435 2210687 := bstep (se 1 (by rfl) ⟨1658015, by rfl⟩ : syracuseStep 2210687 = 3316031) B3316031
theorem B3316037 : Blo 2209435 3316037 := bbase (se 4 (by rfl) ⟨310878, by rfl⟩ : syracuseStep 3316037 = 621757) (by norm_num)
theorem B2210691 : Blo 2209435 2210691 := bstep (se 1 (by rfl) ⟨1658018, by rfl⟩ : syracuseStep 2210691 = 3316037) B3316037
theorem B3730549 : Blo 2209435 3730549 := bbase (se 5 (by rfl) ⟨174869, by rfl⟩ : syracuseStep 3730549 = 349739) (by norm_num)
theorem B4974065 : Blo 2209435 4974065 := bstep (se 2 (by rfl) ⟨1865274, by rfl⟩ : syracuseStep 4974065 = 3730549) B3730549
theorem B3316043 : Blo 2209435 3316043 := bstep (se 1 (by rfl) ⟨2487032, by rfl⟩ : syracuseStep 3316043 = 4974065) B4974065
theorem B2210695 : Blo 2209435 2210695 := bstep (se 1 (by rfl) ⟨1658021, by rfl⟩ : syracuseStep 2210695 = 3316043) B3316043
theorem B2487037 : Blo 2209435 2487037 := bbase (se 3 (by rfl) ⟨466319, by rfl⟩ : syracuseStep 2487037 = 932639) (by norm_num)
theorem B3316049 : Blo 2209435 3316049 := bstep (se 2 (by rfl) ⟨1243518, by rfl⟩ : syracuseStep 3316049 = 2487037) B2487037
theorem B2210699 : Blo 2209435 2210699 := bstep (se 1 (by rfl) ⟨1658024, by rfl⟩ : syracuseStep 2210699 = 3316049) B3316049
theorem B7461125 : Blo 2209435 7461125 := bbase (se 4 (by rfl) ⟨699480, by rfl⟩ : syracuseStep 7461125 = 1398961) (by norm_num)
theorem B4974083 : Blo 2209435 4974083 := bstep (se 1 (by rfl) ⟨3730562, by rfl⟩ : syracuseStep 4974083 = 7461125) B7461125
theorem B3316055 : Blo 2209435 3316055 := bstep (se 1 (by rfl) ⟨2487041, by rfl⟩ : syracuseStep 3316055 = 4974083) B4974083
theorem B2210703 : Blo 2209435 2210703 := bstep (se 1 (by rfl) ⟨1658027, by rfl⟩ : syracuseStep 2210703 = 3316055) B3316055
theorem B3316061 : Blo 2209435 3316061 := bbase (se 3 (by rfl) ⟨621761, by rfl⟩ : syracuseStep 3316061 = 1243523) (by norm_num)
theorem B2210707 : Blo 2209435 2210707 := bstep (se 1 (by rfl) ⟨1658030, by rfl⟩ : syracuseStep 2210707 = 3316061) B3316061
theorem B4974101 : Blo 2209435 4974101 := bbase (se 6 (by rfl) ⟨116580, by rfl⟩ : syracuseStep 4974101 = 233161) (by norm_num)
theorem B3316067 : Blo 2209435 3316067 := bstep (se 1 (by rfl) ⟨2487050, by rfl⟩ : syracuseStep 3316067 = 4974101) B4974101
theorem B2210711 : Blo 2209435 2210711 := bstep (se 1 (by rfl) ⟨1658033, by rfl⟩ : syracuseStep 2210711 = 3316067) B3316067
theorem B8393813 : Blo 2209435 8393813 := bbase (se 8 (by rfl) ⟨49182, by rfl⟩ : syracuseStep 8393813 = 98365) (by norm_num)
theorem B5595875 : Blo 2209435 5595875 := bstep (se 1 (by rfl) ⟨4196906, by rfl⟩ : syracuseStep 5595875 = 8393813) B8393813
theorem B3730583 : Blo 2209435 3730583 := bstep (se 1 (by rfl) ⟨2797937, by rfl⟩ : syracuseStep 3730583 = 5595875) B5595875
theorem B2487055 : Blo 2209435 2487055 := bstep (se 1 (by rfl) ⟨1865291, by rfl⟩ : syracuseStep 2487055 = 3730583) B3730583
theorem B3316073 : Blo 2209435 3316073 := bstep (se 2 (by rfl) ⟨1243527, by rfl⟩ : syracuseStep 3316073 = 2487055) B2487055
theorem B2210715 : Blo 2209435 2210715 := bstep (se 1 (by rfl) ⟨1658036, by rfl⟩ : syracuseStep 2210715 = 3316073) B3316073
theorem B12590741 : Blo 2209435 12590741 := bbase (se 6 (by rfl) ⟨295095, by rfl⟩ : syracuseStep 12590741 = 590191) (by norm_num)
theorem B8393827 : Blo 2209435 8393827 := bstep (se 1 (by rfl) ⟨6295370, by rfl⟩ : syracuseStep 8393827 = 12590741) B12590741
theorem B11191769 : Blo 2209435 11191769 := bstep (se 2 (by rfl) ⟨4196913, by rfl⟩ : syracuseStep 11191769 = 8393827) B8393827
theorem B7461179 : Blo 2209435 7461179 := bstep (se 1 (by rfl) ⟨5595884, by rfl⟩ : syracuseStep 7461179 = 11191769) B11191769
theorem B4974119 : Blo 2209435 4974119 := bstep (se 1 (by rfl) ⟨3730589, by rfl⟩ : syracuseStep 4974119 = 7461179) B7461179
theorem B3316079 : Blo 2209435 3316079 := bstep (se 1 (by rfl) ⟨2487059, by rfl⟩ : syracuseStep 3316079 = 4974119) B4974119
theorem B2210719 : Blo 2209435 2210719 := bstep (se 1 (by rfl) ⟨1658039, by rfl⟩ : syracuseStep 2210719 = 3316079) B3316079
theorem B3316085 : Blo 2209435 3316085 := bbase (se 5 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 3316085 = 310883) (by norm_num)
theorem B2210723 : Blo 2209435 2210723 := bstep (se 1 (by rfl) ⟨1658042, by rfl⟩ : syracuseStep 2210723 = 3316085) B3316085
theorem B2360773 : Blo 2209435 2360773 := bbase (se 4 (by rfl) ⟨221322, by rfl⟩ : syracuseStep 2360773 = 442645) (by norm_num)
theorem B3147697 : Blo 2209435 3147697 := bstep (se 2 (by rfl) ⟨1180386, by rfl⟩ : syracuseStep 3147697 = 2360773) B2360773
theorem B4196929 : Blo 2209435 4196929 := bstep (se 2 (by rfl) ⟨1573848, by rfl⟩ : syracuseStep 4196929 = 3147697) B3147697
theorem B5595905 : Blo 2209435 5595905 := bstep (se 2 (by rfl) ⟨2098464, by rfl⟩ : syracuseStep 5595905 = 4196929) B4196929
theorem B3730603 : Blo 2209435 3730603 := bstep (se 1 (by rfl) ⟨2797952, by rfl⟩ : syracuseStep 3730603 = 5595905) B5595905
theorem B4974137 : Blo 2209435 4974137 := bstep (se 2 (by rfl) ⟨1865301, by rfl⟩ : syracuseStep 4974137 = 3730603) B3730603
theorem B3316091 : Blo 2209435 3316091 := bstep (se 1 (by rfl) ⟨2487068, by rfl⟩ : syracuseStep 3316091 = 4974137) B4974137
theorem B2210727 : Blo 2209435 2210727 := bstep (se 1 (by rfl) ⟨1658045, by rfl⟩ : syracuseStep 2210727 = 3316091) B3316091
theorem B2487073 : Blo 2209435 2487073 := bbase (se 2 (by rfl) ⟨932652, by rfl⟩ : syracuseStep 2487073 = 1865305) (by norm_num)
theorem B3316097 : Blo 2209435 3316097 := bstep (se 2 (by rfl) ⟨1243536, by rfl⟩ : syracuseStep 3316097 = 2487073) B2487073
theorem B2210731 : Blo 2209435 2210731 := bstep (se 1 (by rfl) ⟨1658048, by rfl⟩ : syracuseStep 2210731 = 3316097) B3316097
theorem B5595925 : Blo 2209435 5595925 := bbase (se 6 (by rfl) ⟨131154, by rfl⟩ : syracuseStep 5595925 = 262309) (by norm_num)
theorem B7461233 : Blo 2209435 7461233 := bstep (se 2 (by rfl) ⟨2797962, by rfl⟩ : syracuseStep 7461233 = 5595925) B5595925
theorem B4974155 : Blo 2209435 4974155 := bstep (se 1 (by rfl) ⟨3730616, by rfl⟩ : syracuseStep 4974155 = 7461233) B7461233
theorem B3316103 : Blo 2209435 3316103 := bstep (se 1 (by rfl) ⟨2487077, by rfl⟩ : syracuseStep 3316103 = 4974155) B4974155
theorem B2210735 : Blo 2209435 2210735 := bstep (se 1 (by rfl) ⟨1658051, by rfl⟩ : syracuseStep 2210735 = 3316103) B3316103
theorem B3316109 : Blo 2209435 3316109 := bbase (se 3 (by rfl) ⟨621770, by rfl⟩ : syracuseStep 3316109 = 1243541) (by norm_num)
theorem B2210739 : Blo 2209435 2210739 := bstep (se 1 (by rfl) ⟨1658054, by rfl⟩ : syracuseStep 2210739 = 3316109) B3316109
theorem B4974173 : Blo 2209435 4974173 := bbase (se 3 (by rfl) ⟨932657, by rfl⟩ : syracuseStep 4974173 = 1865315) (by norm_num)
theorem B3316115 : Blo 2209435 3316115 := bstep (se 1 (by rfl) ⟨2487086, by rfl⟩ : syracuseStep 3316115 = 4974173) B4974173
theorem B2210743 : Blo 2209435 2210743 := bstep (se 1 (by rfl) ⟨1658057, by rfl⟩ : syracuseStep 2210743 = 3316115) B3316115
theorem B3730637 : Blo 2209435 3730637 := bbase (se 3 (by rfl) ⟨699494, by rfl⟩ : syracuseStep 3730637 = 1398989) (by norm_num)
theorem B2487091 : Blo 2209435 2487091 := bstep (se 1 (by rfl) ⟨1865318, by rfl⟩ : syracuseStep 2487091 = 3730637) B3730637
theorem B3316121 : Blo 2209435 3316121 := bstep (se 2 (by rfl) ⟨1243545, by rfl⟩ : syracuseStep 3316121 = 2487091) B2487091
theorem B2210747 : Blo 2209435 2210747 := bstep (se 1 (by rfl) ⟨1658060, by rfl⟩ : syracuseStep 2210747 = 3316121) B3316121
theorem B14164789 : Blo 2209435 14164789 := bbase (se 5 (by rfl) ⟨663974, by rfl⟩ : syracuseStep 14164789 = 1327949) (by norm_num)
theorem B18886385 : Blo 2209435 18886385 := bstep (se 2 (by rfl) ⟨7082394, by rfl⟩ : syracuseStep 18886385 = 14164789) B14164789
theorem B12590923 : Blo 2209435 12590923 := bstep (se 1 (by rfl) ⟨9443192, by rfl⟩ : syracuseStep 12590923 = 18886385) B18886385
theorem B16787897 : Blo 2209435 16787897 := bstep (se 2 (by rfl) ⟨6295461, by rfl⟩ : syracuseStep 16787897 = 12590923) B12590923
theorem B11191931 : Blo 2209435 11191931 := bstep (se 1 (by rfl) ⟨8393948, by rfl⟩ : syracuseStep 11191931 = 16787897) B16787897
theorem B7461287 : Blo 2209435 7461287 := bstep (se 1 (by rfl) ⟨5595965, by rfl⟩ : syracuseStep 7461287 = 11191931) B11191931
theorem B4974191 : Blo 2209435 4974191 := bstep (se 1 (by rfl) ⟨3730643, by rfl⟩ : syracuseStep 4974191 = 7461287) B7461287
theorem B3316127 : Blo 2209435 3316127 := bstep (se 1 (by rfl) ⟨2487095, by rfl⟩ : syracuseStep 3316127 = 4974191) B4974191
theorem B2210751 : Blo 2209435 2210751 := bstep (se 1 (by rfl) ⟨1658063, by rfl⟩ : syracuseStep 2210751 = 3316127) B3316127
theorem B3316133 : Blo 2209435 3316133 := bbase (se 4 (by rfl) ⟨310887, by rfl⟩ : syracuseStep 3316133 = 621775) (by norm_num)
theorem B2210755 : Blo 2209435 2210755 := bstep (se 1 (by rfl) ⟨1658066, by rfl⟩ : syracuseStep 2210755 = 3316133) B3316133
theorem B2797993 : Blo 2209435 2797993 := bbase (se 2 (by rfl) ⟨1049247, by rfl⟩ : syracuseStep 2797993 = 2098495) (by norm_num)
theorem B3730657 : Blo 2209435 3730657 := bstep (se 2 (by rfl) ⟨1398996, by rfl⟩ : syracuseStep 3730657 = 2797993) B2797993
theorem B4974209 : Blo 2209435 4974209 := bstep (se 2 (by rfl) ⟨1865328, by rfl⟩ : syracuseStep 4974209 = 3730657) B3730657
theorem B3316139 : Blo 2209435 3316139 := bstep (se 1 (by rfl) ⟨2487104, by rfl⟩ : syracuseStep 3316139 = 4974209) B4974209
theorem B2210759 : Blo 2209435 2210759 := bstep (se 1 (by rfl) ⟨1658069, by rfl⟩ : syracuseStep 2210759 = 3316139) B3316139
theorem B2487109 : Blo 2209435 2487109 := bbase (se 4 (by rfl) ⟨233166, by rfl⟩ : syracuseStep 2487109 = 466333) (by norm_num)
theorem B3316145 : Blo 2209435 3316145 := bstep (se 2 (by rfl) ⟨1243554, by rfl⟩ : syracuseStep 3316145 = 2487109) B2487109
theorem B2210763 : Blo 2209435 2210763 := bstep (se 1 (by rfl) ⟨1658072, by rfl⟩ : syracuseStep 2210763 = 3316145) B3316145
theorem B4197005 : Blo 2209435 4197005 := bbase (se 3 (by rfl) ⟨786938, by rfl⟩ : syracuseStep 4197005 = 1573877) (by norm_num)
theorem B2798003 : Blo 2209435 2798003 := bstep (se 1 (by rfl) ⟨2098502, by rfl⟩ : syracuseStep 2798003 = 4197005) B4197005
theorem B7461341 : Blo 2209435 7461341 := bstep (se 3 (by rfl) ⟨1399001, by rfl⟩ : syracuseStep 7461341 = 2798003) B2798003
theorem B4974227 : Blo 2209435 4974227 := bstep (se 1 (by rfl) ⟨3730670, by rfl⟩ : syracuseStep 4974227 = 7461341) B7461341
theorem B3316151 : Blo 2209435 3316151 := bstep (se 1 (by rfl) ⟨2487113, by rfl⟩ : syracuseStep 3316151 = 4974227) B4974227
theorem B2210767 : Blo 2209435 2210767 := bstep (se 1 (by rfl) ⟨1658075, by rfl⟩ : syracuseStep 2210767 = 3316151) B3316151
theorem B3316157 : Blo 2209435 3316157 := bbase (se 3 (by rfl) ⟨621779, by rfl⟩ : syracuseStep 3316157 = 1243559) (by norm_num)
theorem B2210771 : Blo 2209435 2210771 := bstep (se 1 (by rfl) ⟨1658078, by rfl⟩ : syracuseStep 2210771 = 3316157) B3316157
theorem B4974245 : Blo 2209435 4974245 := bbase (se 4 (by rfl) ⟨466335, by rfl⟩ : syracuseStep 4974245 = 932671) (by norm_num)
theorem B3316163 : Blo 2209435 3316163 := bstep (se 1 (by rfl) ⟨2487122, by rfl⟩ : syracuseStep 3316163 = 4974245) B4974245
theorem B2210775 : Blo 2209435 2210775 := bstep (se 1 (by rfl) ⟨1658081, by rfl⟩ : syracuseStep 2210775 = 3316163) B3316163
theorem B5596037 : Blo 2209435 5596037 := bbase (se 4 (by rfl) ⟨524628, by rfl⟩ : syracuseStep 5596037 = 1049257) (by norm_num)
theorem B3730691 : Blo 2209435 3730691 := bstep (se 1 (by rfl) ⟨2798018, by rfl⟩ : syracuseStep 3730691 = 5596037) B5596037
theorem B2487127 : Blo 2209435 2487127 := bstep (se 1 (by rfl) ⟨1865345, by rfl⟩ : syracuseStep 2487127 = 3730691) B3730691
theorem B3316169 : Blo 2209435 3316169 := bstep (se 2 (by rfl) ⟨1243563, by rfl⟩ : syracuseStep 3316169 = 2487127) B2487127
theorem B2210779 : Blo 2209435 2210779 := bstep (se 1 (by rfl) ⟨1658084, by rfl⟩ : syracuseStep 2210779 = 3316169) B3316169
theorem B2655937 : Blo 2209435 2655937 := bbase (se 2 (by rfl) ⟨995976, by rfl⟩ : syracuseStep 2655937 = 1991953) (by norm_num)
theorem B3541249 : Blo 2209435 3541249 := bstep (se 2 (by rfl) ⟨1327968, by rfl⟩ : syracuseStep 3541249 = 2655937) B2655937
theorem B4721665 : Blo 2209435 4721665 := bstep (se 2 (by rfl) ⟨1770624, by rfl⟩ : syracuseStep 4721665 = 3541249) B3541249
theorem B6295553 : Blo 2209435 6295553 := bstep (se 2 (by rfl) ⟨2360832, by rfl⟩ : syracuseStep 6295553 = 4721665) B4721665
theorem B4197035 : Blo 2209435 4197035 := bstep (se 1 (by rfl) ⟨3147776, by rfl⟩ : syracuseStep 4197035 = 6295553) B6295553
theorem B11192093 : Blo 2209435 11192093 := bstep (se 3 (by rfl) ⟨2098517, by rfl⟩ : syracuseStep 11192093 = 4197035) B4197035
theorem B7461395 : Blo 2209435 7461395 := bstep (se 1 (by rfl) ⟨5596046, by rfl⟩ : syracuseStep 7461395 = 11192093) B11192093
theorem B4974263 : Blo 2209435 4974263 := bstep (se 1 (by rfl) ⟨3730697, by rfl⟩ : syracuseStep 4974263 = 7461395) B7461395
theorem B3316175 : Blo 2209435 3316175 := bstep (se 1 (by rfl) ⟨2487131, by rfl⟩ : syracuseStep 3316175 = 4974263) B4974263
theorem B2210783 : Blo 2209435 2210783 := bstep (se 1 (by rfl) ⟨1658087, by rfl⟩ : syracuseStep 2210783 = 3316175) B3316175
theorem B3316181 : Blo 2209435 3316181 := bbase (se 7 (by rfl) ⟨38861, by rfl⟩ : syracuseStep 3316181 = 77723) (by norm_num)
theorem B2210787 : Blo 2209435 2210787 := bstep (se 1 (by rfl) ⟨1658090, by rfl⟩ : syracuseStep 2210787 = 3316181) B3316181
theorem B8394101 : Blo 2209435 8394101 := bbase (se 5 (by rfl) ⟨393473, by rfl⟩ : syracuseStep 8394101 = 786947) (by norm_num)
theorem B5596067 : Blo 2209435 5596067 := bstep (se 1 (by rfl) ⟨4197050, by rfl⟩ : syracuseStep 5596067 = 8394101) B8394101
theorem B3730711 : Blo 2209435 3730711 := bstep (se 1 (by rfl) ⟨2798033, by rfl⟩ : syracuseStep 3730711 = 5596067) B5596067
theorem B4974281 : Blo 2209435 4974281 := bstep (se 2 (by rfl) ⟨1865355, by rfl⟩ : syracuseStep 4974281 = 3730711) B3730711
theorem B3316187 : Blo 2209435 3316187 := bstep (se 1 (by rfl) ⟨2487140, by rfl⟩ : syracuseStep 3316187 = 4974281) B4974281
theorem B2210791 : Blo 2209435 2210791 := bstep (se 1 (by rfl) ⟨1658093, by rfl⟩ : syracuseStep 2210791 = 3316187) B3316187
theorem B2487145 : Blo 2209435 2487145 := bbase (se 2 (by rfl) ⟨932679, by rfl⟩ : syracuseStep 2487145 = 1865359) (by norm_num)
theorem B3316193 : Blo 2209435 3316193 := bstep (se 2 (by rfl) ⟨1243572, by rfl⟩ : syracuseStep 3316193 = 2487145) B2487145
theorem B2210795 : Blo 2209435 2210795 := bstep (se 1 (by rfl) ⟨1658096, by rfl⟩ : syracuseStep 2210795 = 3316193) B3316193
theorem B7082549 : Blo 2209435 7082549 := bbase (se 5 (by rfl) ⟨331994, by rfl⟩ : syracuseStep 7082549 = 663989) (by norm_num)
theorem B4721699 : Blo 2209435 4721699 := bstep (se 1 (by rfl) ⟨3541274, by rfl⟩ : syracuseStep 4721699 = 7082549) B7082549
theorem B12591197 : Blo 2209435 12591197 := bstep (se 3 (by rfl) ⟨2360849, by rfl⟩ : syracuseStep 12591197 = 4721699) B4721699
theorem B8394131 : Blo 2209435 8394131 := bstep (se 1 (by rfl) ⟨6295598, by rfl⟩ : syracuseStep 8394131 = 12591197) B12591197
theorem B5596087 : Blo 2209435 5596087 := bstep (se 1 (by rfl) ⟨4197065, by rfl⟩ : syracuseStep 5596087 = 8394131) B8394131
theorem B7461449 : Blo 2209435 7461449 := bstep (se 2 (by rfl) ⟨2798043, by rfl⟩ : syracuseStep 7461449 = 5596087) B5596087
theorem B4974299 : Blo 2209435 4974299 := bstep (se 1 (by rfl) ⟨3730724, by rfl⟩ : syracuseStep 4974299 = 7461449) B7461449
theorem B3316199 : Blo 2209435 3316199 := bstep (se 1 (by rfl) ⟨2487149, by rfl⟩ : syracuseStep 3316199 = 4974299) B4974299
theorem B2210799 : Blo 2209435 2210799 := bstep (se 1 (by rfl) ⟨1658099, by rfl⟩ : syracuseStep 2210799 = 3316199) B3316199
theorem B3316205 : Blo 2209435 3316205 := bbase (se 3 (by rfl) ⟨621788, by rfl⟩ : syracuseStep 3316205 = 1243577) (by norm_num)
theorem B2210803 : Blo 2209435 2210803 := bstep (se 1 (by rfl) ⟨1658102, by rfl⟩ : syracuseStep 2210803 = 3316205) B3316205
theorem B4974317 : Blo 2209435 4974317 := bbase (se 3 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 4974317 = 1865369) (by norm_num)
theorem B3316211 : Blo 2209435 3316211 := bstep (se 1 (by rfl) ⟨2487158, by rfl⟩ : syracuseStep 3316211 = 4974317) B4974317
theorem B2210807 : Blo 2209435 2210807 := bstep (se 1 (by rfl) ⟨1658105, by rfl⟩ : syracuseStep 2210807 = 3316211) B3316211
theorem B5042197 : Blo 2209435 5042197 := bbase (se 6 (by rfl) ⟨118176, by rfl⟩ : syracuseStep 5042197 = 236353) (by norm_num)
theorem B6722929 : Blo 2209435 6722929 := bstep (se 2 (by rfl) ⟨2521098, by rfl⟩ : syracuseStep 6722929 = 5042197) B5042197
theorem B8963905 : Blo 2209435 8963905 := bstep (se 2 (by rfl) ⟨3361464, by rfl⟩ : syracuseStep 8963905 = 6722929) B6722929
theorem B11951873 : Blo 2209435 11951873 := bstep (se 2 (by rfl) ⟨4481952, by rfl⟩ : syracuseStep 11951873 = 8963905) B8963905
theorem B7967915 : Blo 2209435 7967915 := bstep (se 1 (by rfl) ⟨5975936, by rfl⟩ : syracuseStep 7967915 = 11951873) B11951873
theorem B5311943 : Blo 2209435 5311943 := bstep (se 1 (by rfl) ⟨3983957, by rfl⟩ : syracuseStep 5311943 = 7967915) B7967915
theorem B3541295 : Blo 2209435 3541295 := bstep (se 1 (by rfl) ⟨2655971, by rfl⟩ : syracuseStep 3541295 = 5311943) B5311943
theorem B2360863 : Blo 2209435 2360863 := bstep (se 1 (by rfl) ⟨1770647, by rfl⟩ : syracuseStep 2360863 = 3541295) B3541295
theorem B3147817 : Blo 2209435 3147817 := bstep (se 2 (by rfl) ⟨1180431, by rfl⟩ : syracuseStep 3147817 = 2360863) B2360863
theorem B4197089 : Blo 2209435 4197089 := bstep (se 2 (by rfl) ⟨1573908, by rfl⟩ : syracuseStep 4197089 = 3147817) B3147817
theorem B2798059 : Blo 2209435 2798059 := bstep (se 1 (by rfl) ⟨2098544, by rfl⟩ : syracuseStep 2798059 = 4197089) B4197089
theorem B3730745 : Blo 2209435 3730745 := bstep (se 2 (by rfl) ⟨1399029, by rfl⟩ : syracuseStep 3730745 = 2798059) B2798059
theorem B2487163 : Blo 2209435 2487163 := bstep (se 1 (by rfl) ⟨1865372, by rfl⟩ : syracuseStep 2487163 = 3730745) B3730745
theorem B3316217 : Blo 2209435 3316217 := bstep (se 2 (by rfl) ⟨1243581, by rfl⟩ : syracuseStep 3316217 = 2487163) B2487163
theorem B2210811 : Blo 2209435 2210811 := bstep (se 1 (by rfl) ⟨1658108, by rfl⟩ : syracuseStep 2210811 = 3316217) B3316217
theorem B10084405 : Blo 2209435 10084405 := bbase (se 5 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 10084405 = 945413) (by norm_num)
theorem B13445873 : Blo 2209435 13445873 := bstep (se 2 (by rfl) ⟨5042202, by rfl⟩ : syracuseStep 13445873 = 10084405) B10084405
theorem B8963915 : Blo 2209435 8963915 := bstep (se 1 (by rfl) ⟨6722936, by rfl⟩ : syracuseStep 8963915 = 13445873) B13445873
theorem B95615093 : Blo 2209435 95615093 := bstep (se 5 (by rfl) ⟨4481957, by rfl⟩ : syracuseStep 95615093 = 8963915) B8963915
theorem B63743395 : Blo 2209435 63743395 := bstep (se 1 (by rfl) ⟨47807546, by rfl⟩ : syracuseStep 63743395 = 95615093) B95615093
theorem B84991193 : Blo 2209435 84991193 := bstep (se 2 (by rfl) ⟨31871697, by rfl⟩ : syracuseStep 84991193 = 63743395) B63743395
theorem B56660795 : Blo 2209435 56660795 := bstep (se 1 (by rfl) ⟨42495596, by rfl⟩ : syracuseStep 56660795 = 84991193) B84991193
theorem B37773863 : Blo 2209435 37773863 := bstep (se 1 (by rfl) ⟨28330397, by rfl⟩ : syracuseStep 37773863 = 56660795) B56660795
theorem B25182575 : Blo 2209435 25182575 := bstep (se 1 (by rfl) ⟨18886931, by rfl⟩ : syracuseStep 25182575 = 37773863) B37773863
theorem B16788383 : Blo 2209435 16788383 := bstep (se 1 (by rfl) ⟨12591287, by rfl⟩ : syracuseStep 16788383 = 25182575) B25182575
theorem B11192255 : Blo 2209435 11192255 := bstep (se 1 (by rfl) ⟨8394191, by rfl⟩ : syracuseStep 11192255 = 16788383) B16788383
theorem B7461503 : Blo 2209435 7461503 := bstep (se 1 (by rfl) ⟨5596127, by rfl⟩ : syracuseStep 7461503 = 11192255) B11192255
theorem B4974335 : Blo 2209435 4974335 := bstep (se 1 (by rfl) ⟨3730751, by rfl⟩ : syracuseStep 4974335 = 7461503) B7461503
theorem B3316223 : Blo 2209435 3316223 := bstep (se 1 (by rfl) ⟨2487167, by rfl⟩ : syracuseStep 3316223 = 4974335) B4974335
theorem B2210815 : Blo 2209435 2210815 := bstep (se 1 (by rfl) ⟨1658111, by rfl⟩ : syracuseStep 2210815 = 3316223) B3316223
theorem B3316229 : Blo 2209435 3316229 := bbase (se 4 (by rfl) ⟨310896, by rfl⟩ : syracuseStep 3316229 = 621793) (by norm_num)
theorem B2210819 : Blo 2209435 2210819 := bstep (se 1 (by rfl) ⟨1658114, by rfl⟩ : syracuseStep 2210819 = 3316229) B3316229
theorem B3730765 : Blo 2209435 3730765 := bbase (se 3 (by rfl) ⟨699518, by rfl⟩ : syracuseStep 3730765 = 1399037) (by norm_num)
theorem B4974353 : Blo 2209435 4974353 := bstep (se 2 (by rfl) ⟨1865382, by rfl⟩ : syracuseStep 4974353 = 3730765) B3730765
theorem B3316235 : Blo 2209435 3316235 := bstep (se 1 (by rfl) ⟨2487176, by rfl⟩ : syracuseStep 3316235 = 4974353) B4974353
theorem B2210823 : Blo 2209435 2210823 := bstep (se 1 (by rfl) ⟨1658117, by rfl⟩ : syracuseStep 2210823 = 3316235) B3316235
theorem B2487181 : Blo 2209435 2487181 := bbase (se 3 (by rfl) ⟨466346, by rfl⟩ : syracuseStep 2487181 = 932693) (by norm_num)
theorem B3316241 : Blo 2209435 3316241 := bstep (se 2 (by rfl) ⟨1243590, by rfl⟩ : syracuseStep 3316241 = 2487181) B2487181
theorem B2210827 : Blo 2209435 2210827 := bstep (se 1 (by rfl) ⟨1658120, by rfl⟩ : syracuseStep 2210827 = 3316241) B3316241
theorem B7461557 : Blo 2209435 7461557 := bbase (se 5 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 7461557 = 699521) (by norm_num)
theorem B4974371 : Blo 2209435 4974371 := bstep (se 1 (by rfl) ⟨3730778, by rfl⟩ : syracuseStep 4974371 = 7461557) B7461557
theorem B3316247 : Blo 2209435 3316247 := bstep (se 1 (by rfl) ⟨2487185, by rfl⟩ : syracuseStep 3316247 = 4974371) B4974371
theorem B2210831 : Blo 2209435 2210831 := bstep (se 1 (by rfl) ⟨1658123, by rfl⟩ : syracuseStep 2210831 = 3316247) B3316247
theorem B3316253 : Blo 2209435 3316253 := bbase (se 3 (by rfl) ⟨621797, by rfl⟩ : syracuseStep 3316253 = 1243595) (by norm_num)
theorem B2210835 : Blo 2209435 2210835 := bstep (se 1 (by rfl) ⟨1658126, by rfl⟩ : syracuseStep 2210835 = 3316253) B3316253
theorem B4974389 : Blo 2209435 4974389 := bbase (se 5 (by rfl) ⟨233174, by rfl⟩ : syracuseStep 4974389 = 466349) (by norm_num)
theorem B3316259 : Blo 2209435 3316259 := bstep (se 1 (by rfl) ⟨2487194, by rfl⟩ : syracuseStep 3316259 = 4974389) B4974389
theorem B2210839 : Blo 2209435 2210839 := bstep (se 1 (by rfl) ⟨1658129, by rfl⟩ : syracuseStep 2210839 = 3316259) B3316259
theorem B2656009 : Blo 2209435 2656009 := bbase (se 2 (by rfl) ⟨996003, by rfl⟩ : syracuseStep 2656009 = 1992007) (by norm_num)
theorem B14165381 : Blo 2209435 14165381 := bstep (se 4 (by rfl) ⟨1328004, by rfl⟩ : syracuseStep 14165381 = 2656009) B2656009
theorem B9443587 : Blo 2209435 9443587 := bstep (se 1 (by rfl) ⟨7082690, by rfl⟩ : syracuseStep 9443587 = 14165381) B14165381
theorem B12591449 : Blo 2209435 12591449 := bstep (se 2 (by rfl) ⟨4721793, by rfl⟩ : syracuseStep 12591449 = 9443587) B9443587
theorem B8394299 : Blo 2209435 8394299 := bstep (se 1 (by rfl) ⟨6295724, by rfl⟩ : syracuseStep 8394299 = 12591449) B12591449
theorem B5596199 : Blo 2209435 5596199 := bstep (se 1 (by rfl) ⟨4197149, by rfl⟩ : syracuseStep 5596199 = 8394299) B8394299
theorem B3730799 : Blo 2209435 3730799 := bstep (se 1 (by rfl) ⟨2798099, by rfl⟩ : syracuseStep 3730799 = 5596199) B5596199
theorem B2487199 : Blo 2209435 2487199 := bstep (se 1 (by rfl) ⟨1865399, by rfl⟩ : syracuseStep 2487199 = 3730799) B3730799
theorem B3316265 : Blo 2209435 3316265 := bstep (se 2 (by rfl) ⟨1243599, by rfl⟩ : syracuseStep 3316265 = 2487199) B2487199
theorem B2210843 : Blo 2209435 2210843 := bstep (se 1 (by rfl) ⟨1658132, by rfl⟩ : syracuseStep 2210843 = 3316265) B3316265
theorem B17017685 : Blo 2209435 17017685 := bbase (se 9 (by rfl) ⟨49856, by rfl⟩ : syracuseStep 17017685 = 99713) (by norm_num)
theorem B11345123 : Blo 2209435 11345123 := bstep (se 1 (by rfl) ⟨8508842, by rfl⟩ : syracuseStep 11345123 = 17017685) B17017685
theorem B30253661 : Blo 2209435 30253661 := bstep (se 3 (by rfl) ⟨5672561, by rfl⟩ : syracuseStep 30253661 = 11345123) B11345123
theorem B20169107 : Blo 2209435 20169107 := bstep (se 1 (by rfl) ⟨15126830, by rfl⟩ : syracuseStep 20169107 = 30253661) B30253661
theorem B13446071 : Blo 2209435 13446071 := bstep (se 1 (by rfl) ⟨10084553, by rfl⟩ : syracuseStep 13446071 = 20169107) B20169107
theorem B8964047 : Blo 2209435 8964047 := bstep (se 1 (by rfl) ⟨6723035, by rfl⟩ : syracuseStep 8964047 = 13446071) B13446071
theorem B5976031 : Blo 2209435 5976031 := bstep (se 1 (by rfl) ⟨4482023, by rfl⟩ : syracuseStep 5976031 = 8964047) B8964047
theorem B7968041 : Blo 2209435 7968041 := bstep (se 2 (by rfl) ⟨2988015, by rfl⟩ : syracuseStep 7968041 = 5976031) B5976031
theorem B5312027 : Blo 2209435 5312027 := bstep (se 1 (by rfl) ⟨3984020, by rfl⟩ : syracuseStep 5312027 = 7968041) B7968041
theorem B14165405 : Blo 2209435 14165405 := bstep (se 3 (by rfl) ⟨2656013, by rfl⟩ : syracuseStep 14165405 = 5312027) B5312027
theorem B9443603 : Blo 2209435 9443603 := bstep (se 1 (by rfl) ⟨7082702, by rfl⟩ : syracuseStep 9443603 = 14165405) B14165405
theorem B6295735 : Blo 2209435 6295735 := bstep (se 1 (by rfl) ⟨4721801, by rfl⟩ : syracuseStep 6295735 = 9443603) B9443603
theorem B8394313 : Blo 2209435 8394313 := bstep (se 2 (by rfl) ⟨3147867, by rfl⟩ : syracuseStep 8394313 = 6295735) B6295735
theorem B11192417 : Blo 2209435 11192417 := bstep (se 2 (by rfl) ⟨4197156, by rfl⟩ : syracuseStep 11192417 = 8394313) B8394313
theorem B7461611 : Blo 2209435 7461611 := bstep (se 1 (by rfl) ⟨5596208, by rfl⟩ : syracuseStep 7461611 = 11192417) B11192417
theorem B4974407 : Blo 2209435 4974407 := bstep (se 1 (by rfl) ⟨3730805, by rfl⟩ : syracuseStep 4974407 = 7461611) B7461611
theorem B3316271 : Blo 2209435 3316271 := bstep (se 1 (by rfl) ⟨2487203, by rfl⟩ : syracuseStep 3316271 = 4974407) B4974407
theorem B2210847 : Blo 2209435 2210847 := bstep (se 1 (by rfl) ⟨1658135, by rfl⟩ : syracuseStep 2210847 = 3316271) B3316271
theorem B3316277 : Blo 2209435 3316277 := bbase (se 5 (by rfl) ⟨155450, by rfl⟩ : syracuseStep 3316277 = 310901) (by norm_num)
theorem B2210851 : Blo 2209435 2210851 := bstep (se 1 (by rfl) ⟨1658138, by rfl⟩ : syracuseStep 2210851 = 3316277) B3316277
theorem B5596229 : Blo 2209435 5596229 := bbase (se 4 (by rfl) ⟨524646, by rfl⟩ : syracuseStep 5596229 = 1049293) (by norm_num)
theorem B3730819 : Blo 2209435 3730819 := bstep (se 1 (by rfl) ⟨2798114, by rfl⟩ : syracuseStep 3730819 = 5596229) B5596229
theorem B4974425 : Blo 2209435 4974425 := bstep (se 2 (by rfl) ⟨1865409, by rfl⟩ : syracuseStep 4974425 = 3730819) B3730819
theorem B3316283 : Blo 2209435 3316283 := bstep (se 1 (by rfl) ⟨2487212, by rfl⟩ : syracuseStep 3316283 = 4974425) B4974425
theorem B2210855 : Blo 2209435 2210855 := bstep (se 1 (by rfl) ⟨1658141, by rfl⟩ : syracuseStep 2210855 = 3316283) B3316283
theorem B2487217 : Blo 2209435 2487217 := bbase (se 2 (by rfl) ⟨932706, by rfl⟩ : syracuseStep 2487217 = 1865413) (by norm_num)
theorem B3316289 : Blo 2209435 3316289 := bstep (se 2 (by rfl) ⟨1243608, by rfl⟩ : syracuseStep 3316289 = 2487217) B2487217
theorem B2210859 : Blo 2209435 2210859 := bstep (se 1 (by rfl) ⟨1658144, by rfl⟩ : syracuseStep 2210859 = 3316289) B3316289
theorem B6295781 : Blo 2209435 6295781 := bbase (se 4 (by rfl) ⟨590229, by rfl⟩ : syracuseStep 6295781 = 1180459) (by norm_num)
theorem B4197187 : Blo 2209435 4197187 := bstep (se 1 (by rfl) ⟨3147890, by rfl⟩ : syracuseStep 4197187 = 6295781) B6295781
theorem B5596249 : Blo 2209435 5596249 := bstep (se 2 (by rfl) ⟨2098593, by rfl⟩ : syracuseStep 5596249 = 4197187) B4197187
theorem B7461665 : Blo 2209435 7461665 := bstep (se 2 (by rfl) ⟨2798124, by rfl⟩ : syracuseStep 7461665 = 5596249) B5596249
theorem B4974443 : Blo 2209435 4974443 := bstep (se 1 (by rfl) ⟨3730832, by rfl⟩ : syracuseStep 4974443 = 7461665) B7461665
theorem B3316295 : Blo 2209435 3316295 := bstep (se 1 (by rfl) ⟨2487221, by rfl⟩ : syracuseStep 3316295 = 4974443) B4974443
theorem B2210863 : Blo 2209435 2210863 := bstep (se 1 (by rfl) ⟨1658147, by rfl⟩ : syracuseStep 2210863 = 3316295) B3316295
theorem B3316301 : Blo 2209435 3316301 := bbase (se 3 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 3316301 = 1243613) (by norm_num)
theorem B2210867 : Blo 2209435 2210867 := bstep (se 1 (by rfl) ⟨1658150, by rfl⟩ : syracuseStep 2210867 = 3316301) B3316301
theorem B4974461 : Blo 2209435 4974461 := bbase (se 3 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 4974461 = 1865423) (by norm_num)
theorem B3316307 : Blo 2209435 3316307 := bstep (se 1 (by rfl) ⟨2487230, by rfl⟩ : syracuseStep 3316307 = 4974461) B4974461
theorem B2210871 : Blo 2209435 2210871 := bstep (se 1 (by rfl) ⟨1658153, by rfl⟩ : syracuseStep 2210871 = 3316307) B3316307
theorem B3730853 : Blo 2209435 3730853 := bbase (se 4 (by rfl) ⟨349767, by rfl⟩ : syracuseStep 3730853 = 699535) (by norm_num)
theorem B2487235 : Blo 2209435 2487235 := bstep (se 1 (by rfl) ⟨1865426, by rfl⟩ : syracuseStep 2487235 = 3730853) B3730853
theorem B3316313 : Blo 2209435 3316313 := bstep (se 2 (by rfl) ⟨1243617, by rfl⟩ : syracuseStep 3316313 = 2487235) B2487235
theorem B2210875 : Blo 2209435 2210875 := bstep (se 1 (by rfl) ⟨1658156, by rfl⟩ : syracuseStep 2210875 = 3316313) B3316313
theorem B4038437 : Blo 2209435 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B10769165 : Blo 2209435 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B7179443 : Blo 2209435 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B4786295 : Blo 2209435 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B12763453 : Blo 2209435 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B17017937 : Blo 2209435 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B11345291 : Blo 2209435 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B7563527 : Blo 2209435 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B5042351 : Blo 2209435 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B13446269 : Blo 2209435 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B8964179 : Blo 2209435 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B5976119 : Blo 2209435 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B3984079 : Blo 2209435 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B5312105 : Blo 2209435 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B3541403 : Blo 2209435 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B2360935 : Blo 2209435 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B3147913 : Blo 2209435 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B16788869 : Blo 2209435 16788869 := bstep (se 4 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 16788869 = 3147913) B3147913
theorem B11192579 : Blo 2209435 11192579 := bstep (se 1 (by rfl) ⟨8394434, by rfl⟩ : syracuseStep 11192579 = 16788869) B16788869
theorem B7461719 : Blo 2209435 7461719 := bstep (se 1 (by rfl) ⟨5596289, by rfl⟩ : syracuseStep 7461719 = 11192579) B11192579
theorem B4974479 : Blo 2209435 4974479 := bstep (se 1 (by rfl) ⟨3730859, by rfl⟩ : syracuseStep 4974479 = 7461719) B7461719
theorem B3316319 : Blo 2209435 3316319 := bstep (se 1 (by rfl) ⟨2487239, by rfl⟩ : syracuseStep 3316319 = 4974479) B4974479
theorem B2210879 : Blo 2209435 2210879 := bstep (se 1 (by rfl) ⟨1658159, by rfl⟩ : syracuseStep 2210879 = 3316319) B3316319
theorem B3316325 : Blo 2209435 3316325 := bbase (se 4 (by rfl) ⟨310905, by rfl⟩ : syracuseStep 3316325 = 621811) (by norm_num)
theorem B2210883 : Blo 2209435 2210883 := bstep (se 1 (by rfl) ⟨1658162, by rfl⟩ : syracuseStep 2210883 = 3316325) B3316325
theorem B3147925 : Blo 2209435 3147925 := bbase (se 6 (by rfl) ⟨73779, by rfl⟩ : syracuseStep 3147925 = 147559) (by norm_num)
theorem B4197233 : Blo 2209435 4197233 := bstep (se 2 (by rfl) ⟨1573962, by rfl⟩ : syracuseStep 4197233 = 3147925) B3147925
theorem B2798155 : Blo 2209435 2798155 := bstep (se 1 (by rfl) ⟨2098616, by rfl⟩ : syracuseStep 2798155 = 4197233) B4197233
theorem B3730873 : Blo 2209435 3730873 := bstep (se 2 (by rfl) ⟨1399077, by rfl⟩ : syracuseStep 3730873 = 2798155) B2798155
theorem B4974497 : Blo 2209435 4974497 := bstep (se 2 (by rfl) ⟨1865436, by rfl⟩ : syracuseStep 4974497 = 3730873) B3730873
theorem B3316331 : Blo 2209435 3316331 := bstep (se 1 (by rfl) ⟨2487248, by rfl⟩ : syracuseStep 3316331 = 4974497) B4974497
theorem B2210887 : Blo 2209435 2210887 := bstep (se 1 (by rfl) ⟨1658165, by rfl⟩ : syracuseStep 2210887 = 3316331) B3316331
theorem B2487253 : Blo 2209435 2487253 := bbase (se 7 (by rfl) ⟨29147, by rfl⟩ : syracuseStep 2487253 = 58295) (by norm_num)
theorem B3316337 : Blo 2209435 3316337 := bstep (se 2 (by rfl) ⟨1243626, by rfl⟩ : syracuseStep 3316337 = 2487253) B2487253
theorem B2210891 : Blo 2209435 2210891 := bstep (se 1 (by rfl) ⟨1658168, by rfl⟩ : syracuseStep 2210891 = 3316337) B3316337
theorem B2798165 : Blo 2209435 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B7461773 : Blo 2209435 7461773 := bstep (se 3 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 7461773 = 2798165) B2798165
theorem B4974515 : Blo 2209435 4974515 := bstep (se 1 (by rfl) ⟨3730886, by rfl⟩ : syracuseStep 4974515 = 7461773) B7461773
theorem B3316343 : Blo 2209435 3316343 := bstep (se 1 (by rfl) ⟨2487257, by rfl⟩ : syracuseStep 3316343 = 4974515) B4974515
theorem B2210895 : Blo 2209435 2210895 := bstep (se 1 (by rfl) ⟨1658171, by rfl⟩ : syracuseStep 2210895 = 3316343) B3316343
theorem B3316349 : Blo 2209435 3316349 := bbase (se 3 (by rfl) ⟨621815, by rfl⟩ : syracuseStep 3316349 = 1243631) (by norm_num)
theorem B2210899 : Blo 2209435 2210899 := bstep (se 1 (by rfl) ⟨1658174, by rfl⟩ : syracuseStep 2210899 = 3316349) B3316349
theorem B4974533 : Blo 2209435 4974533 := bbase (se 4 (by rfl) ⟨466362, by rfl⟩ : syracuseStep 4974533 = 932725) (by norm_num)
theorem B3316355 : Blo 2209435 3316355 := bstep (se 1 (by rfl) ⟨2487266, by rfl⟩ : syracuseStep 3316355 = 4974533) B4974533
theorem B2210903 : Blo 2209435 2210903 := bstep (se 1 (by rfl) ⟨1658177, by rfl⟩ : syracuseStep 2210903 = 3316355) B3316355
theorem B9443861 : Blo 2209435 9443861 := bbase (se 6 (by rfl) ⟨221340, by rfl⟩ : syracuseStep 9443861 = 442681) (by norm_num)
theorem B6295907 : Blo 2209435 6295907 := bstep (se 1 (by rfl) ⟨4721930, by rfl⟩ : syracuseStep 6295907 = 9443861) B9443861
theorem B4197271 : Blo 2209435 4197271 := bstep (se 1 (by rfl) ⟨3147953, by rfl⟩ : syracuseStep 4197271 = 6295907) B6295907
theorem B5596361 : Blo 2209435 5596361 := bstep (se 2 (by rfl) ⟨2098635, by rfl⟩ : syracuseStep 5596361 = 4197271) B4197271
theorem B3730907 : Blo 2209435 3730907 := bstep (se 1 (by rfl) ⟨2798180, by rfl⟩ : syracuseStep 3730907 = 5596361) B5596361
theorem B2487271 : Blo 2209435 2487271 := bstep (se 1 (by rfl) ⟨1865453, by rfl⟩ : syracuseStep 2487271 = 3730907) B3730907
theorem B3316361 : Blo 2209435 3316361 := bstep (se 2 (by rfl) ⟨1243635, by rfl⟩ : syracuseStep 3316361 = 2487271) B2487271
theorem B2210907 : Blo 2209435 2210907 := bstep (se 1 (by rfl) ⟨1658180, by rfl⟩ : syracuseStep 2210907 = 3316361) B3316361
theorem B11192741 : Blo 2209435 11192741 := bbase (se 4 (by rfl) ⟨1049319, by rfl⟩ : syracuseStep 11192741 = 2098639) (by norm_num)
theorem B7461827 : Blo 2209435 7461827 := bstep (se 1 (by rfl) ⟨5596370, by rfl⟩ : syracuseStep 7461827 = 11192741) B11192741
theorem B4974551 : Blo 2209435 4974551 := bstep (se 1 (by rfl) ⟨3730913, by rfl⟩ : syracuseStep 4974551 = 7461827) B7461827
theorem B3316367 : Blo 2209435 3316367 := bstep (se 1 (by rfl) ⟨2487275, by rfl⟩ : syracuseStep 3316367 = 4974551) B4974551
theorem B2210911 : Blo 2209435 2210911 := bstep (se 1 (by rfl) ⟨1658183, by rfl⟩ : syracuseStep 2210911 = 3316367) B3316367
theorem B3316373 : Blo 2209435 3316373 := bbase (se 6 (by rfl) ⟨77727, by rfl⟩ : syracuseStep 3316373 = 155455) (by norm_num)
theorem B2210915 : Blo 2209435 2210915 := bstep (se 1 (by rfl) ⟨1658186, by rfl⟩ : syracuseStep 2210915 = 3316373) B3316373
theorem B4786381 : Blo 2209435 4786381 := bbase (se 3 (by rfl) ⟨897446, by rfl⟩ : syracuseStep 4786381 = 1794893) (by norm_num)
theorem B6381841 : Blo 2209435 6381841 := bstep (se 2 (by rfl) ⟨2393190, by rfl⟩ : syracuseStep 6381841 = 4786381) B4786381
theorem B8509121 : Blo 2209435 8509121 := bstep (se 2 (by rfl) ⟨3190920, by rfl⟩ : syracuseStep 8509121 = 6381841) B6381841
theorem B5672747 : Blo 2209435 5672747 := bstep (se 1 (by rfl) ⟨4254560, by rfl⟩ : syracuseStep 5672747 = 8509121) B8509121
theorem B3781831 : Blo 2209435 3781831 := bstep (se 1 (by rfl) ⟨2836373, by rfl⟩ : syracuseStep 3781831 = 5672747) B5672747
theorem B5042441 : Blo 2209435 5042441 := bstep (se 2 (by rfl) ⟨1890915, by rfl⟩ : syracuseStep 5042441 = 3781831) B3781831
theorem B3361627 : Blo 2209435 3361627 := bstep (se 1 (by rfl) ⟨2521220, by rfl⟩ : syracuseStep 3361627 = 5042441) B5042441
theorem B17928677 : Blo 2209435 17928677 := bstep (se 4 (by rfl) ⟨1680813, by rfl⟩ : syracuseStep 17928677 = 3361627) B3361627
theorem B11952451 : Blo 2209435 11952451 := bstep (se 1 (by rfl) ⟨8964338, by rfl⟩ : syracuseStep 11952451 = 17928677) B17928677
theorem B15936601 : Blo 2209435 15936601 := bstep (se 2 (by rfl) ⟨5976225, by rfl⟩ : syracuseStep 15936601 = 11952451) B11952451
theorem B21248801 : Blo 2209435 21248801 := bstep (se 2 (by rfl) ⟨7968300, by rfl⟩ : syracuseStep 21248801 = 15936601) B15936601
theorem B14165867 : Blo 2209435 14165867 := bstep (se 1 (by rfl) ⟨10624400, by rfl⟩ : syracuseStep 14165867 = 21248801) B21248801
theorem B9443911 : Blo 2209435 9443911 := bstep (se 1 (by rfl) ⟨7082933, by rfl⟩ : syracuseStep 9443911 = 14165867) B14165867
theorem B12591881 : Blo 2209435 12591881 := bstep (se 2 (by rfl) ⟨4721955, by rfl⟩ : syracuseStep 12591881 = 9443911) B9443911
theorem B8394587 : Blo 2209435 8394587 := bstep (se 1 (by rfl) ⟨6295940, by rfl⟩ : syracuseStep 8394587 = 12591881) B12591881
theorem B5596391 : Blo 2209435 5596391 := bstep (se 1 (by rfl) ⟨4197293, by rfl⟩ : syracuseStep 5596391 = 8394587) B8394587
theorem B3730927 : Blo 2209435 3730927 := bstep (se 1 (by rfl) ⟨2798195, by rfl⟩ : syracuseStep 3730927 = 5596391) B5596391
theorem B4974569 : Blo 2209435 4974569 := bstep (se 2 (by rfl) ⟨1865463, by rfl⟩ : syracuseStep 4974569 = 3730927) B3730927
theorem B3316379 : Blo 2209435 3316379 := bstep (se 1 (by rfl) ⟨2487284, by rfl⟩ : syracuseStep 3316379 = 4974569) B4974569
theorem B2210919 : Blo 2209435 2210919 := bstep (se 1 (by rfl) ⟨1658189, by rfl⟩ : syracuseStep 2210919 = 3316379) B3316379
theorem B2487289 : Blo 2209435 2487289 := bbase (se 2 (by rfl) ⟨932733, by rfl⟩ : syracuseStep 2487289 = 1865467) (by norm_num)
theorem B3316385 : Blo 2209435 3316385 := bstep (se 2 (by rfl) ⟨1243644, by rfl⟩ : syracuseStep 3316385 = 2487289) B2487289
theorem B2210923 : Blo 2209435 2210923 := bstep (se 1 (by rfl) ⟨1658192, by rfl⟩ : syracuseStep 2210923 = 3316385) B3316385
theorem B5750165 : Blo 2209435 5750165 := bbase (se 6 (by rfl) ⟨134769, by rfl⟩ : syracuseStep 5750165 = 269539) (by norm_num)
theorem B3833443 : Blo 2209435 3833443 := bstep (se 1 (by rfl) ⟨2875082, by rfl⟩ : syracuseStep 3833443 = 5750165) B5750165
theorem B5111257 : Blo 2209435 5111257 := bstep (se 2 (by rfl) ⟨1916721, by rfl⟩ : syracuseStep 5111257 = 3833443) B3833443
theorem B6815009 : Blo 2209435 6815009 := bstep (se 2 (by rfl) ⟨2555628, by rfl⟩ : syracuseStep 6815009 = 5111257) B5111257
theorem B4543339 : Blo 2209435 4543339 := bstep (se 1 (by rfl) ⟨3407504, by rfl⟩ : syracuseStep 4543339 = 6815009) B6815009
theorem B6057785 : Blo 2209435 6057785 := bstep (se 2 (by rfl) ⟨2271669, by rfl⟩ : syracuseStep 6057785 = 4543339) B4543339
theorem B16154093 : Blo 2209435 16154093 := bstep (se 3 (by rfl) ⟨3028892, by rfl⟩ : syracuseStep 16154093 = 6057785) B6057785
theorem B43077581 : Blo 2209435 43077581 := bstep (se 3 (by rfl) ⟨8077046, by rfl⟩ : syracuseStep 43077581 = 16154093) B16154093
theorem B28718387 : Blo 2209435 28718387 := bstep (se 1 (by rfl) ⟨21538790, by rfl⟩ : syracuseStep 28718387 = 43077581) B43077581
theorem B19145591 : Blo 2209435 19145591 := bstep (se 1 (by rfl) ⟨14359193, by rfl⟩ : syracuseStep 19145591 = 28718387) B28718387
theorem B12763727 : Blo 2209435 12763727 := bstep (se 1 (by rfl) ⟨9572795, by rfl⟩ : syracuseStep 12763727 = 19145591) B19145591
theorem B8509151 : Blo 2209435 8509151 := bstep (se 1 (by rfl) ⟨6381863, by rfl⟩ : syracuseStep 8509151 = 12763727) B12763727
theorem B5672767 : Blo 2209435 5672767 := bstep (se 1 (by rfl) ⟨4254575, by rfl⟩ : syracuseStep 5672767 = 8509151) B8509151
theorem B7563689 : Blo 2209435 7563689 := bstep (se 2 (by rfl) ⟨2836383, by rfl⟩ : syracuseStep 7563689 = 5672767) B5672767
theorem B5042459 : Blo 2209435 5042459 := bstep (se 1 (by rfl) ⟨3781844, by rfl⟩ : syracuseStep 5042459 = 7563689) B7563689
theorem B13446557 : Blo 2209435 13446557 := bstep (se 3 (by rfl) ⟨2521229, by rfl⟩ : syracuseStep 13446557 = 5042459) B5042459
theorem B8964371 : Blo 2209435 8964371 := bstep (se 1 (by rfl) ⟨6723278, by rfl⟩ : syracuseStep 8964371 = 13446557) B13446557
theorem B23904989 : Blo 2209435 23904989 := bstep (se 3 (by rfl) ⟨4482185, by rfl⟩ : syracuseStep 23904989 = 8964371) B8964371
theorem B15936659 : Blo 2209435 15936659 := bstep (se 1 (by rfl) ⟨11952494, by rfl⟩ : syracuseStep 15936659 = 23904989) B23904989
theorem B10624439 : Blo 2209435 10624439 := bstep (se 1 (by rfl) ⟨7968329, by rfl⟩ : syracuseStep 10624439 = 15936659) B15936659
theorem B7082959 : Blo 2209435 7082959 := bstep (se 1 (by rfl) ⟨5312219, by rfl⟩ : syracuseStep 7082959 = 10624439) B10624439
theorem B9443945 : Blo 2209435 9443945 := bstep (se 2 (by rfl) ⟨3541479, by rfl⟩ : syracuseStep 9443945 = 7082959) B7082959
theorem B6295963 : Blo 2209435 6295963 := bstep (se 1 (by rfl) ⟨4721972, by rfl⟩ : syracuseStep 6295963 = 9443945) B9443945
theorem B8394617 : Blo 2209435 8394617 := bstep (se 2 (by rfl) ⟨3147981, by rfl⟩ : syracuseStep 8394617 = 6295963) B6295963
theorem B5596411 : Blo 2209435 5596411 := bstep (se 1 (by rfl) ⟨4197308, by rfl⟩ : syracuseStep 5596411 = 8394617) B8394617
theorem B7461881 : Blo 2209435 7461881 := bstep (se 2 (by rfl) ⟨2798205, by rfl⟩ : syracuseStep 7461881 = 5596411) B5596411
theorem B4974587 : Blo 2209435 4974587 := bstep (se 1 (by rfl) ⟨3730940, by rfl⟩ : syracuseStep 4974587 = 7461881) B7461881
theorem B3316391 : Blo 2209435 3316391 := bstep (se 1 (by rfl) ⟨2487293, by rfl⟩ : syracuseStep 3316391 = 4974587) B4974587
theorem B2210927 : Blo 2209435 2210927 := bstep (se 1 (by rfl) ⟨1658195, by rfl⟩ : syracuseStep 2210927 = 3316391) B3316391
theorem B3316397 : Blo 2209435 3316397 := bbase (se 3 (by rfl) ⟨621824, by rfl⟩ : syracuseStep 3316397 = 1243649) (by norm_num)
theorem B2210931 : Blo 2209435 2210931 := bstep (se 1 (by rfl) ⟨1658198, by rfl⟩ : syracuseStep 2210931 = 3316397) B3316397
theorem B4974605 : Blo 2209435 4974605 := bbase (se 3 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 4974605 = 1865477) (by norm_num)
theorem B3316403 : Blo 2209435 3316403 := bstep (se 1 (by rfl) ⟨2487302, by rfl⟩ : syracuseStep 3316403 = 4974605) B4974605
theorem B2210935 : Blo 2209435 2210935 := bstep (se 1 (by rfl) ⟨1658201, by rfl⟩ : syracuseStep 2210935 = 3316403) B3316403
theorem B2798221 : Blo 2209435 2798221 := bbase (se 3 (by rfl) ⟨524666, by rfl⟩ : syracuseStep 2798221 = 1049333) (by norm_num)
theorem B3730961 : Blo 2209435 3730961 := bstep (se 2 (by rfl) ⟨1399110, by rfl⟩ : syracuseStep 3730961 = 2798221) B2798221
theorem B2487307 : Blo 2209435 2487307 := bstep (se 1 (by rfl) ⟨1865480, by rfl⟩ : syracuseStep 2487307 = 3730961) B3730961
theorem B3316409 : Blo 2209435 3316409 := bstep (se 2 (by rfl) ⟨1243653, by rfl⟩ : syracuseStep 3316409 = 2487307) B2487307
theorem B2210939 : Blo 2209435 2210939 := bstep (se 1 (by rfl) ⟨1658204, by rfl⟩ : syracuseStep 2210939 = 3316409) B3316409
theorem B2241109 : Blo 2209435 2241109 := bbase (se 8 (by rfl) ⟨13131, by rfl⟩ : syracuseStep 2241109 = 26263) (by norm_num)
theorem B2988145 : Blo 2209435 2988145 := bstep (se 2 (by rfl) ⟨1120554, by rfl⟩ : syracuseStep 2988145 = 2241109) B2241109
theorem B3984193 : Blo 2209435 3984193 := bstep (se 2 (by rfl) ⟨1494072, by rfl⟩ : syracuseStep 3984193 = 2988145) B2988145
theorem B21249029 : Blo 2209435 21249029 := bstep (se 4 (by rfl) ⟨1992096, by rfl⟩ : syracuseStep 21249029 = 3984193) B3984193
theorem B14166019 : Blo 2209435 14166019 := bstep (se 1 (by rfl) ⟨10624514, by rfl⟩ : syracuseStep 14166019 = 21249029) B21249029
theorem B18888025 : Blo 2209435 18888025 := bstep (se 2 (by rfl) ⟨7083009, by rfl⟩ : syracuseStep 18888025 = 14166019) B14166019
theorem B25184033 : Blo 2209435 25184033 := bstep (se 2 (by rfl) ⟨9444012, by rfl⟩ : syracuseStep 25184033 = 18888025) B18888025
theorem B16789355 : Blo 2209435 16789355 := bstep (se 1 (by rfl) ⟨12592016, by rfl⟩ : syracuseStep 16789355 = 25184033) B25184033
theorem B11192903 : Blo 2209435 11192903 := bstep (se 1 (by rfl) ⟨8394677, by rfl⟩ : syracuseStep 11192903 = 16789355) B16789355
theorem B7461935 : Blo 2209435 7461935 := bstep (se 1 (by rfl) ⟨5596451, by rfl⟩ : syracuseStep 7461935 = 11192903) B11192903
theorem B4974623 : Blo 2209435 4974623 := bstep (se 1 (by rfl) ⟨3730967, by rfl⟩ : syracuseStep 4974623 = 7461935) B7461935
theorem B3316415 : Blo 2209435 3316415 := bstep (se 1 (by rfl) ⟨2487311, by rfl⟩ : syracuseStep 3316415 = 4974623) B4974623
theorem B2210943 : Blo 2209435 2210943 := bstep (se 1 (by rfl) ⟨1658207, by rfl⟩ : syracuseStep 2210943 = 3316415) B3316415
theorem B3316421 : Blo 2209435 3316421 := bbase (se 4 (by rfl) ⟨310914, by rfl⟩ : syracuseStep 3316421 = 621829) (by norm_num)
theorem B2210947 : Blo 2209435 2210947 := bstep (se 1 (by rfl) ⟨1658210, by rfl⟩ : syracuseStep 2210947 = 3316421) B3316421
theorem B3730981 : Blo 2209435 3730981 := bbase (se 4 (by rfl) ⟨349779, by rfl⟩ : syracuseStep 3730981 = 699559) (by norm_num)
theorem B4974641 : Blo 2209435 4974641 := bstep (se 2 (by rfl) ⟨1865490, by rfl⟩ : syracuseStep 4974641 = 3730981) B3730981
theorem B3316427 : Blo 2209435 3316427 := bstep (se 1 (by rfl) ⟨2487320, by rfl⟩ : syracuseStep 3316427 = 4974641) B4974641
theorem B2210951 : Blo 2209435 2210951 := bstep (se 1 (by rfl) ⟨1658213, by rfl⟩ : syracuseStep 2210951 = 3316427) B3316427
theorem B2487325 : Blo 2209435 2487325 := bbase (se 3 (by rfl) ⟨466373, by rfl⟩ : syracuseStep 2487325 = 932747) (by norm_num)
theorem B3316433 : Blo 2209435 3316433 := bstep (se 2 (by rfl) ⟨1243662, by rfl⟩ : syracuseStep 3316433 = 2487325) B2487325
theorem B2210955 : Blo 2209435 2210955 := bstep (se 1 (by rfl) ⟨1658216, by rfl⟩ : syracuseStep 2210955 = 3316433) B3316433
theorem B7461989 : Blo 2209435 7461989 := bbase (se 4 (by rfl) ⟨699561, by rfl⟩ : syracuseStep 7461989 = 1399123) (by norm_num)
theorem B4974659 : Blo 2209435 4974659 := bstep (se 1 (by rfl) ⟨3730994, by rfl⟩ : syracuseStep 4974659 = 7461989) B7461989
theorem B3316439 : Blo 2209435 3316439 := bstep (se 1 (by rfl) ⟨2487329, by rfl⟩ : syracuseStep 3316439 = 4974659) B4974659
theorem B2210959 : Blo 2209435 2210959 := bstep (se 1 (by rfl) ⟨1658219, by rfl⟩ : syracuseStep 2210959 = 3316439) B3316439
theorem B3316445 : Blo 2209435 3316445 := bbase (se 3 (by rfl) ⟨621833, by rfl⟩ : syracuseStep 3316445 = 1243667) (by norm_num)
theorem B2210963 : Blo 2209435 2210963 := bstep (se 1 (by rfl) ⟨1658222, by rfl⟩ : syracuseStep 2210963 = 3316445) B3316445
theorem B4974677 : Blo 2209435 4974677 := bbase (se 8 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 4974677 = 58297) (by norm_num)
theorem B3316451 : Blo 2209435 3316451 := bstep (se 1 (by rfl) ⟨2487338, by rfl⟩ : syracuseStep 3316451 = 4974677) B4974677
theorem B2210967 : Blo 2209435 2210967 := bstep (se 1 (by rfl) ⟨1658225, by rfl⟩ : syracuseStep 2210967 = 3316451) B3316451
theorem B3984245 : Blo 2209435 3984245 := bbase (se 5 (by rfl) ⟨186761, by rfl⟩ : syracuseStep 3984245 = 373523) (by norm_num)
theorem B2656163 : Blo 2209435 2656163 := bstep (se 1 (by rfl) ⟨1992122, by rfl⟩ : syracuseStep 2656163 = 3984245) B3984245
theorem B7083101 : Blo 2209435 7083101 := bstep (se 3 (by rfl) ⟨1328081, by rfl⟩ : syracuseStep 7083101 = 2656163) B2656163
theorem B4722067 : Blo 2209435 4722067 := bstep (se 1 (by rfl) ⟨3541550, by rfl⟩ : syracuseStep 4722067 = 7083101) B7083101
theorem B6296089 : Blo 2209435 6296089 := bstep (se 2 (by rfl) ⟨2361033, by rfl⟩ : syracuseStep 6296089 = 4722067) B4722067
theorem B8394785 : Blo 2209435 8394785 := bstep (se 2 (by rfl) ⟨3148044, by rfl⟩ : syracuseStep 8394785 = 6296089) B6296089
theorem B5596523 : Blo 2209435 5596523 := bstep (se 1 (by rfl) ⟨4197392, by rfl⟩ : syracuseStep 5596523 = 8394785) B8394785
theorem B3731015 : Blo 2209435 3731015 := bstep (se 1 (by rfl) ⟨2798261, by rfl⟩ : syracuseStep 3731015 = 5596523) B5596523
theorem B2487343 : Blo 2209435 2487343 := bstep (se 1 (by rfl) ⟨1865507, by rfl⟩ : syracuseStep 2487343 = 3731015) B3731015
theorem B3316457 : Blo 2209435 3316457 := bstep (se 2 (by rfl) ⟨1243671, by rfl⟩ : syracuseStep 3316457 = 2487343) B2487343
theorem B2210971 : Blo 2209435 2210971 := bstep (se 1 (by rfl) ⟨1658228, by rfl⟩ : syracuseStep 2210971 = 3316457) B3316457
theorem B12115829 : Blo 2209435 12115829 := bbase (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) (by norm_num)
theorem B8077219 : Blo 2209435 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B43078501 : Blo 2209435 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B57438001 : Blo 2209435 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B76584001 : Blo 2209435 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B102112001 : Blo 2209435 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B68074667 : Blo 2209435 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B45383111 : Blo 2209435 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B30255407 : Blo 2209435 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B20170271 : Blo 2209435 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B13446847 : Blo 2209435 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B17929129 : Blo 2209435 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B23905505 : Blo 2209435 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B15937003 : Blo 2209435 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B21249337 : Blo 2209435 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B28332449 : Blo 2209435 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B18888299 : Blo 2209435 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B12592199 : Blo 2209435 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B8394799 : Blo 2209435 8394799 := bstep (se 1 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 8394799 = 12592199) B12592199
theorem B11193065 : Blo 2209435 11193065 := bstep (se 2 (by rfl) ⟨4197399, by rfl⟩ : syracuseStep 11193065 = 8394799) B8394799
theorem B7462043 : Blo 2209435 7462043 := bstep (se 1 (by rfl) ⟨5596532, by rfl⟩ : syracuseStep 7462043 = 11193065) B11193065
theorem B4974695 : Blo 2209435 4974695 := bstep (se 1 (by rfl) ⟨3731021, by rfl⟩ : syracuseStep 4974695 = 7462043) B7462043
theorem B3316463 : Blo 2209435 3316463 := bstep (se 1 (by rfl) ⟨2487347, by rfl⟩ : syracuseStep 3316463 = 4974695) B4974695
theorem B2210975 : Blo 2209435 2210975 := bstep (se 1 (by rfl) ⟨1658231, by rfl⟩ : syracuseStep 2210975 = 3316463) B3316463
theorem B3316469 : Blo 2209435 3316469 := bbase (se 5 (by rfl) ⟨155459, by rfl⟩ : syracuseStep 3316469 = 310919) (by norm_num)
theorem B2210979 : Blo 2209435 2210979 := bstep (se 1 (by rfl) ⟨1658234, by rfl⟩ : syracuseStep 2210979 = 3316469) B3316469
theorem B10624709 : Blo 2209435 10624709 := bbase (se 4 (by rfl) ⟨996066, by rfl⟩ : syracuseStep 10624709 = 1992133) (by norm_num)
theorem B7083139 : Blo 2209435 7083139 := bstep (se 1 (by rfl) ⟨5312354, by rfl⟩ : syracuseStep 7083139 = 10624709) B10624709
theorem B9444185 : Blo 2209435 9444185 := bstep (se 2 (by rfl) ⟨3541569, by rfl⟩ : syracuseStep 9444185 = 7083139) B7083139
theorem B6296123 : Blo 2209435 6296123 := bstep (se 1 (by rfl) ⟨4722092, by rfl⟩ : syracuseStep 6296123 = 9444185) B9444185
theorem B4197415 : Blo 2209435 4197415 := bstep (se 1 (by rfl) ⟨3148061, by rfl⟩ : syracuseStep 4197415 = 6296123) B6296123
theorem B5596553 : Blo 2209435 5596553 := bstep (se 2 (by rfl) ⟨2098707, by rfl⟩ : syracuseStep 5596553 = 4197415) B4197415
theorem B3731035 : Blo 2209435 3731035 := bstep (se 1 (by rfl) ⟨2798276, by rfl⟩ : syracuseStep 3731035 = 5596553) B5596553
theorem B4974713 : Blo 2209435 4974713 := bstep (se 2 (by rfl) ⟨1865517, by rfl⟩ : syracuseStep 4974713 = 3731035) B3731035
theorem B3316475 : Blo 2209435 3316475 := bstep (se 1 (by rfl) ⟨2487356, by rfl⟩ : syracuseStep 3316475 = 4974713) B4974713
theorem B2210983 : Blo 2209435 2210983 := bstep (se 1 (by rfl) ⟨1658237, by rfl⟩ : syracuseStep 2210983 = 3316475) B3316475
theorem B2487361 : Blo 2209435 2487361 := bbase (se 2 (by rfl) ⟨932760, by rfl⟩ : syracuseStep 2487361 = 1865521) (by norm_num)
theorem B3316481 : Blo 2209435 3316481 := bstep (se 2 (by rfl) ⟨1243680, by rfl⟩ : syracuseStep 3316481 = 2487361) B2487361
theorem B2210987 : Blo 2209435 2210987 := bstep (se 1 (by rfl) ⟨1658240, by rfl⟩ : syracuseStep 2210987 = 3316481) B3316481
theorem B5596573 : Blo 2209435 5596573 := bbase (se 3 (by rfl) ⟨1049357, by rfl⟩ : syracuseStep 5596573 = 2098715) (by norm_num)
theorem B7462097 : Blo 2209435 7462097 := bstep (se 2 (by rfl) ⟨2798286, by rfl⟩ : syracuseStep 7462097 = 5596573) B5596573
theorem B4974731 : Blo 2209435 4974731 := bstep (se 1 (by rfl) ⟨3731048, by rfl⟩ : syracuseStep 4974731 = 7462097) B7462097
theorem B3316487 : Blo 2209435 3316487 := bstep (se 1 (by rfl) ⟨2487365, by rfl⟩ : syracuseStep 3316487 = 4974731) B4974731
theorem B2210991 : Blo 2209435 2210991 := bstep (se 1 (by rfl) ⟨1658243, by rfl⟩ : syracuseStep 2210991 = 3316487) B3316487
theorem B3316493 : Blo 2209435 3316493 := bbase (se 3 (by rfl) ⟨621842, by rfl⟩ : syracuseStep 3316493 = 1243685) (by norm_num)
theorem B2210995 : Blo 2209435 2210995 := bstep (se 1 (by rfl) ⟨1658246, by rfl⟩ : syracuseStep 2210995 = 3316493) B3316493
theorem B4974749 : Blo 2209435 4974749 := bbase (se 3 (by rfl) ⟨932765, by rfl⟩ : syracuseStep 4974749 = 1865531) (by norm_num)
theorem B3316499 : Blo 2209435 3316499 := bstep (se 1 (by rfl) ⟨2487374, by rfl⟩ : syracuseStep 3316499 = 4974749) B4974749
theorem B2210999 : Blo 2209435 2210999 := bstep (se 1 (by rfl) ⟨1658249, by rfl⟩ : syracuseStep 2210999 = 3316499) B3316499
theorem B3731069 : Blo 2209435 3731069 := bbase (se 3 (by rfl) ⟨699575, by rfl⟩ : syracuseStep 3731069 = 1399151) (by norm_num)
theorem B2487379 : Blo 2209435 2487379 := bstep (se 1 (by rfl) ⟨1865534, by rfl⟩ : syracuseStep 2487379 = 3731069) B3731069
theorem B3316505 : Blo 2209435 3316505 := bstep (se 2 (by rfl) ⟨1243689, by rfl⟩ : syracuseStep 3316505 = 2487379) B2487379
theorem B2211003 : Blo 2209435 2211003 := bstep (se 1 (by rfl) ⟨1658252, by rfl⟩ : syracuseStep 2211003 = 3316505) B3316505
theorem B3781981 : Blo 2209435 3781981 := bbase (se 3 (by rfl) ⟨709121, by rfl⟩ : syracuseStep 3781981 = 1418243) (by norm_num)
theorem B20170565 : Blo 2209435 20170565 := bstep (se 4 (by rfl) ⟨1890990, by rfl⟩ : syracuseStep 20170565 = 3781981) B3781981
theorem B13447043 : Blo 2209435 13447043 := bstep (se 1 (by rfl) ⟨10085282, by rfl⟩ : syracuseStep 13447043 = 20170565) B20170565
theorem B8964695 : Blo 2209435 8964695 := bstep (se 1 (by rfl) ⟨6723521, by rfl⟩ : syracuseStep 8964695 = 13447043) B13447043
theorem B23905853 : Blo 2209435 23905853 := bstep (se 3 (by rfl) ⟨4482347, by rfl⟩ : syracuseStep 23905853 = 8964695) B8964695
theorem B15937235 : Blo 2209435 15937235 := bstep (se 1 (by rfl) ⟨11952926, by rfl⟩ : syracuseStep 15937235 = 23905853) B23905853
theorem B10624823 : Blo 2209435 10624823 := bstep (se 1 (by rfl) ⟨7968617, by rfl⟩ : syracuseStep 10624823 = 15937235) B15937235
theorem B7083215 : Blo 2209435 7083215 := bstep (se 1 (by rfl) ⟨5312411, by rfl⟩ : syracuseStep 7083215 = 10624823) B10624823
theorem B4722143 : Blo 2209435 4722143 := bstep (se 1 (by rfl) ⟨3541607, by rfl⟩ : syracuseStep 4722143 = 7083215) B7083215
theorem B12592381 : Blo 2209435 12592381 := bstep (se 3 (by rfl) ⟨2361071, by rfl⟩ : syracuseStep 12592381 = 4722143) B4722143
theorem B16789841 : Blo 2209435 16789841 := bstep (se 2 (by rfl) ⟨6296190, by rfl⟩ : syracuseStep 16789841 = 12592381) B12592381
theorem B11193227 : Blo 2209435 11193227 := bstep (se 1 (by rfl) ⟨8394920, by rfl⟩ : syracuseStep 11193227 = 16789841) B16789841
theorem B7462151 : Blo 2209435 7462151 := bstep (se 1 (by rfl) ⟨5596613, by rfl⟩ : syracuseStep 7462151 = 11193227) B11193227
theorem B4974767 : Blo 2209435 4974767 := bstep (se 1 (by rfl) ⟨3731075, by rfl⟩ : syracuseStep 4974767 = 7462151) B7462151
theorem B3316511 : Blo 2209435 3316511 := bstep (se 1 (by rfl) ⟨2487383, by rfl⟩ : syracuseStep 3316511 = 4974767) B4974767
theorem B2211007 : Blo 2209435 2211007 := bstep (se 1 (by rfl) ⟨1658255, by rfl⟩ : syracuseStep 2211007 = 3316511) B3316511
theorem B3316517 : Blo 2209435 3316517 := bbase (se 4 (by rfl) ⟨310923, by rfl⟩ : syracuseStep 3316517 = 621847) (by norm_num)
theorem B2211011 : Blo 2209435 2211011 := bstep (se 1 (by rfl) ⟨1658258, by rfl⟩ : syracuseStep 2211011 = 3316517) B3316517
theorem B2798317 : Blo 2209435 2798317 := bbase (se 3 (by rfl) ⟨524684, by rfl⟩ : syracuseStep 2798317 = 1049369) (by norm_num)
theorem B3731089 : Blo 2209435 3731089 := bstep (se 2 (by rfl) ⟨1399158, by rfl⟩ : syracuseStep 3731089 = 2798317) B2798317
theorem B4974785 : Blo 2209435 4974785 := bstep (se 2 (by rfl) ⟨1865544, by rfl⟩ : syracuseStep 4974785 = 3731089) B3731089
theorem B3316523 : Blo 2209435 3316523 := bstep (se 1 (by rfl) ⟨2487392, by rfl⟩ : syracuseStep 3316523 = 4974785) B4974785
theorem B2211015 : Blo 2209435 2211015 := bstep (se 1 (by rfl) ⟨1658261, by rfl⟩ : syracuseStep 2211015 = 3316523) B3316523
theorem B2487397 : Blo 2209435 2487397 := bbase (se 4 (by rfl) ⟨233193, by rfl⟩ : syracuseStep 2487397 = 466387) (by norm_num)
theorem B3316529 : Blo 2209435 3316529 := bstep (se 2 (by rfl) ⟨1243698, by rfl⟩ : syracuseStep 3316529 = 2487397) B2487397
theorem B2211019 : Blo 2209435 2211019 := bstep (se 1 (by rfl) ⟨1658264, by rfl⟩ : syracuseStep 2211019 = 3316529) B3316529
theorem B2361089 : Blo 2209435 2361089 := bbase (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) (by norm_num)
theorem B6296237 : Blo 2209435 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B4197491 : Blo 2209435 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B2798327 : Blo 2209435 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B7462205 : Blo 2209435 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B4974803 : Blo 2209435 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B3316535 : Blo 2209435 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B2211023 : Blo 2209435 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B3316541 : Blo 2209435 3316541 := bbase (se 3 (by rfl) ⟨621851, by rfl⟩ : syracuseStep 3316541 = 1243703) (by norm_num)
theorem B2211027 : Blo 2209435 2211027 := bstep (se 1 (by rfl) ⟨1658270, by rfl⟩ : syracuseStep 2211027 = 3316541) B3316541
theorem B4974821 : Blo 2209435 4974821 := bbase (se 4 (by rfl) ⟨466389, by rfl⟩ : syracuseStep 4974821 = 932779) (by norm_num)
theorem B3316547 : Blo 2209435 3316547 := bstep (se 1 (by rfl) ⟨2487410, by rfl⟩ : syracuseStep 3316547 = 4974821) B4974821
theorem B2211031 : Blo 2209435 2211031 := bstep (se 1 (by rfl) ⟨1658273, by rfl⟩ : syracuseStep 2211031 = 3316547) B3316547
theorem B5596685 : Blo 2209435 5596685 := bbase (se 3 (by rfl) ⟨1049378, by rfl⟩ : syracuseStep 5596685 = 2098757) (by norm_num)
theorem B3731123 : Blo 2209435 3731123 := bstep (se 1 (by rfl) ⟨2798342, by rfl⟩ : syracuseStep 3731123 = 5596685) B5596685
theorem B2487415 : Blo 2209435 2487415 := bstep (se 1 (by rfl) ⟨1865561, by rfl⟩ : syracuseStep 2487415 = 3731123) B3731123
theorem B3316553 : Blo 2209435 3316553 := bstep (se 2 (by rfl) ⟨1243707, by rfl⟩ : syracuseStep 3316553 = 2487415) B2487415
theorem B2211035 : Blo 2209435 2211035 := bstep (se 1 (by rfl) ⟨1658276, by rfl⟩ : syracuseStep 2211035 = 3316553) B3316553
theorem B3148141 : Blo 2209435 3148141 := bbase (se 3 (by rfl) ⟨590276, by rfl⟩ : syracuseStep 3148141 = 1180553) (by norm_num)
theorem B4197521 : Blo 2209435 4197521 := bstep (se 2 (by rfl) ⟨1574070, by rfl⟩ : syracuseStep 4197521 = 3148141) B3148141
theorem B11193389 : Blo 2209435 11193389 := bstep (se 3 (by rfl) ⟨2098760, by rfl⟩ : syracuseStep 11193389 = 4197521) B4197521
theorem B7462259 : Blo 2209435 7462259 := bstep (se 1 (by rfl) ⟨5596694, by rfl⟩ : syracuseStep 7462259 = 11193389) B11193389
theorem B4974839 : Blo 2209435 4974839 := bstep (se 1 (by rfl) ⟨3731129, by rfl⟩ : syracuseStep 4974839 = 7462259) B7462259
theorem B3316559 : Blo 2209435 3316559 := bstep (se 1 (by rfl) ⟨2487419, by rfl⟩ : syracuseStep 3316559 = 4974839) B4974839
theorem B2211039 : Blo 2209435 2211039 := bstep (se 1 (by rfl) ⟨1658279, by rfl⟩ : syracuseStep 2211039 = 3316559) B3316559
theorem B3316565 : Blo 2209435 3316565 := bbase (se 9 (by rfl) ⟨9716, by rfl⟩ : syracuseStep 3316565 = 19433) (by norm_num)
theorem B2211043 : Blo 2209435 2211043 := bstep (se 1 (by rfl) ⟨1658282, by rfl⟩ : syracuseStep 2211043 = 3316565) B3316565
theorem B4722229 : Blo 2209435 4722229 := bbase (se 5 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 4722229 = 442709) (by norm_num)
theorem B6296305 : Blo 2209435 6296305 := bstep (se 2 (by rfl) ⟨2361114, by rfl⟩ : syracuseStep 6296305 = 4722229) B4722229
theorem B8395073 : Blo 2209435 8395073 := bstep (se 2 (by rfl) ⟨3148152, by rfl⟩ : syracuseStep 8395073 = 6296305) B6296305
theorem B5596715 : Blo 2209435 5596715 := bstep (se 1 (by rfl) ⟨4197536, by rfl⟩ : syracuseStep 5596715 = 8395073) B8395073
theorem B3731143 : Blo 2209435 3731143 := bstep (se 1 (by rfl) ⟨2798357, by rfl⟩ : syracuseStep 3731143 = 5596715) B5596715
theorem B4974857 : Blo 2209435 4974857 := bstep (se 2 (by rfl) ⟨1865571, by rfl⟩ : syracuseStep 4974857 = 3731143) B3731143
theorem B3316571 : Blo 2209435 3316571 := bstep (se 1 (by rfl) ⟨2487428, by rfl⟩ : syracuseStep 3316571 = 4974857) B4974857
theorem B2211047 : Blo 2209435 2211047 := bstep (se 1 (by rfl) ⟨1658285, by rfl⟩ : syracuseStep 2211047 = 3316571) B3316571
theorem B2487433 : Blo 2209435 2487433 := bbase (se 2 (by rfl) ⟨932787, by rfl⟩ : syracuseStep 2487433 = 1865575) (by norm_num)
theorem B3316577 : Blo 2209435 3316577 := bstep (se 2 (by rfl) ⟨1243716, by rfl⟩ : syracuseStep 3316577 = 2487433) B2487433
theorem B2211051 : Blo 2209435 2211051 := bstep (se 1 (by rfl) ⟨1658288, by rfl⟩ : syracuseStep 2211051 = 3316577) B3316577
theorem B4482445 : Blo 2209435 4482445 := bbase (se 3 (by rfl) ⟨840458, by rfl⟩ : syracuseStep 4482445 = 1680917) (by norm_num)
theorem B5976593 : Blo 2209435 5976593 := bstep (se 2 (by rfl) ⟨2241222, by rfl⟩ : syracuseStep 5976593 = 4482445) B4482445
theorem B3984395 : Blo 2209435 3984395 := bstep (se 1 (by rfl) ⟨2988296, by rfl⟩ : syracuseStep 3984395 = 5976593) B5976593
theorem B42500213 : Blo 2209435 42500213 := bstep (se 5 (by rfl) ⟨1992197, by rfl⟩ : syracuseStep 42500213 = 3984395) B3984395
theorem B28333475 : Blo 2209435 28333475 := bstep (se 1 (by rfl) ⟨21250106, by rfl⟩ : syracuseStep 28333475 = 42500213) B42500213
theorem B18888983 : Blo 2209435 18888983 := bstep (se 1 (by rfl) ⟨14166737, by rfl⟩ : syracuseStep 18888983 = 28333475) B28333475
theorem B12592655 : Blo 2209435 12592655 := bstep (se 1 (by rfl) ⟨9444491, by rfl⟩ : syracuseStep 12592655 = 18888983) B18888983
theorem B8395103 : Blo 2209435 8395103 := bstep (se 1 (by rfl) ⟨6296327, by rfl⟩ : syracuseStep 8395103 = 12592655) B12592655
theorem B5596735 : Blo 2209435 5596735 := bstep (se 1 (by rfl) ⟨4197551, by rfl⟩ : syracuseStep 5596735 = 8395103) B8395103
theorem B7462313 : Blo 2209435 7462313 := bstep (se 2 (by rfl) ⟨2798367, by rfl⟩ : syracuseStep 7462313 = 5596735) B5596735
theorem B4974875 : Blo 2209435 4974875 := bstep (se 1 (by rfl) ⟨3731156, by rfl⟩ : syracuseStep 4974875 = 7462313) B7462313
theorem B3316583 : Blo 2209435 3316583 := bstep (se 1 (by rfl) ⟨2487437, by rfl⟩ : syracuseStep 3316583 = 4974875) B4974875
theorem B2211055 : Blo 2209435 2211055 := bstep (se 1 (by rfl) ⟨1658291, by rfl⟩ : syracuseStep 2211055 = 3316583) B3316583
theorem B3316589 : Blo 2209435 3316589 := bbase (se 3 (by rfl) ⟨621860, by rfl⟩ : syracuseStep 3316589 = 1243721) (by norm_num)
theorem B2211059 : Blo 2209435 2211059 := bstep (se 1 (by rfl) ⟨1658294, by rfl⟩ : syracuseStep 2211059 = 3316589) B3316589
theorem B4974893 : Blo 2209435 4974893 := bbase (se 3 (by rfl) ⟨932792, by rfl⟩ : syracuseStep 4974893 = 1865585) (by norm_num)
theorem B3316595 : Blo 2209435 3316595 := bstep (se 1 (by rfl) ⟨2487446, by rfl⟩ : syracuseStep 3316595 = 4974893) B4974893
theorem B2211063 : Blo 2209435 2211063 := bstep (se 1 (by rfl) ⟨1658297, by rfl⟩ : syracuseStep 2211063 = 3316595) B3316595
theorem B5312557 : Blo 2209435 5312557 := bbase (se 3 (by rfl) ⟨996104, by rfl⟩ : syracuseStep 5312557 = 1992209) (by norm_num)
theorem B7083409 : Blo 2209435 7083409 := bstep (se 2 (by rfl) ⟨2656278, by rfl⟩ : syracuseStep 7083409 = 5312557) B5312557
theorem B9444545 : Blo 2209435 9444545 := bstep (se 2 (by rfl) ⟨3541704, by rfl⟩ : syracuseStep 9444545 = 7083409) B7083409
theorem B6296363 : Blo 2209435 6296363 := bstep (se 1 (by rfl) ⟨4722272, by rfl⟩ : syracuseStep 6296363 = 9444545) B9444545
theorem B4197575 : Blo 2209435 4197575 := bstep (se 1 (by rfl) ⟨3148181, by rfl⟩ : syracuseStep 4197575 = 6296363) B6296363
theorem B2798383 : Blo 2209435 2798383 := bstep (se 1 (by rfl) ⟨2098787, by rfl⟩ : syracuseStep 2798383 = 4197575) B4197575
theorem B3731177 : Blo 2209435 3731177 := bstep (se 2 (by rfl) ⟨1399191, by rfl⟩ : syracuseStep 3731177 = 2798383) B2798383
theorem B2487451 : Blo 2209435 2487451 := bstep (se 1 (by rfl) ⟨1865588, by rfl⟩ : syracuseStep 2487451 = 3731177) B3731177
theorem B3316601 : Blo 2209435 3316601 := bstep (se 2 (by rfl) ⟨1243725, by rfl⟩ : syracuseStep 3316601 = 2487451) B2487451
theorem B2211067 : Blo 2209435 2211067 := bstep (se 1 (by rfl) ⟨1658300, by rfl⟩ : syracuseStep 2211067 = 3316601) B3316601
theorem B10085573 : Blo 2209435 10085573 := bbase (se 4 (by rfl) ⟨945522, by rfl⟩ : syracuseStep 10085573 = 1891045) (by norm_num)
theorem B26894861 : Blo 2209435 26894861 := bstep (se 3 (by rfl) ⟨5042786, by rfl⟩ : syracuseStep 26894861 = 10085573) B10085573
theorem B17929907 : Blo 2209435 17929907 := bstep (se 1 (by rfl) ⟨13447430, by rfl⟩ : syracuseStep 17929907 = 26894861) B26894861
theorem B11953271 : Blo 2209435 11953271 := bstep (se 1 (by rfl) ⟨8964953, by rfl⟩ : syracuseStep 11953271 = 17929907) B17929907
theorem B31875389 : Blo 2209435 31875389 := bstep (se 3 (by rfl) ⟨5976635, by rfl⟩ : syracuseStep 31875389 = 11953271) B11953271
theorem B21250259 : Blo 2209435 21250259 := bstep (se 1 (by rfl) ⟨15937694, by rfl⟩ : syracuseStep 21250259 = 31875389) B31875389
theorem B14166839 : Blo 2209435 14166839 := bstep (se 1 (by rfl) ⟨10625129, by rfl⟩ : syracuseStep 14166839 = 21250259) B21250259
theorem B37778237 : Blo 2209435 37778237 := bstep (se 3 (by rfl) ⟨7083419, by rfl⟩ : syracuseStep 37778237 = 14166839) B14166839
theorem B25185491 : Blo 2209435 25185491 := bstep (se 1 (by rfl) ⟨18889118, by rfl⟩ : syracuseStep 25185491 = 37778237) B37778237
theorem B16790327 : Blo 2209435 16790327 := bstep (se 1 (by rfl) ⟨12592745, by rfl⟩ : syracuseStep 16790327 = 25185491) B25185491
theorem B11193551 : Blo 2209435 11193551 := bstep (se 1 (by rfl) ⟨8395163, by rfl⟩ : syracuseStep 11193551 = 16790327) B16790327
theorem B7462367 : Blo 2209435 7462367 := bstep (se 1 (by rfl) ⟨5596775, by rfl⟩ : syracuseStep 7462367 = 11193551) B11193551
theorem B4974911 : Blo 2209435 4974911 := bstep (se 1 (by rfl) ⟨3731183, by rfl⟩ : syracuseStep 4974911 = 7462367) B7462367
theorem B3316607 : Blo 2209435 3316607 := bstep (se 1 (by rfl) ⟨2487455, by rfl⟩ : syracuseStep 3316607 = 4974911) B4974911
theorem B2211071 : Blo 2209435 2211071 := bstep (se 1 (by rfl) ⟨1658303, by rfl⟩ : syracuseStep 2211071 = 3316607) B3316607
theorem B3316613 : Blo 2209435 3316613 := bbase (se 4 (by rfl) ⟨310932, by rfl⟩ : syracuseStep 3316613 = 621865) (by norm_num)
theorem B2211075 : Blo 2209435 2211075 := bstep (se 1 (by rfl) ⟨1658306, by rfl⟩ : syracuseStep 2211075 = 3316613) B3316613
theorem B3731197 : Blo 2209435 3731197 := bbase (se 3 (by rfl) ⟨699599, by rfl⟩ : syracuseStep 3731197 = 1399199) (by norm_num)
theorem B4974929 : Blo 2209435 4974929 := bstep (se 2 (by rfl) ⟨1865598, by rfl⟩ : syracuseStep 4974929 = 3731197) B3731197
theorem B3316619 : Blo 2209435 3316619 := bstep (se 1 (by rfl) ⟨2487464, by rfl⟩ : syracuseStep 3316619 = 4974929) B4974929
theorem B2211079 : Blo 2209435 2211079 := bstep (se 1 (by rfl) ⟨1658309, by rfl⟩ : syracuseStep 2211079 = 3316619) B3316619
theorem B2487469 : Blo 2209435 2487469 := bbase (se 3 (by rfl) ⟨466400, by rfl⟩ : syracuseStep 2487469 = 932801) (by norm_num)
theorem B3316625 : Blo 2209435 3316625 := bstep (se 2 (by rfl) ⟨1243734, by rfl⟩ : syracuseStep 3316625 = 2487469) B2487469
theorem B2211083 : Blo 2209435 2211083 := bstep (se 1 (by rfl) ⟨1658312, by rfl⟩ : syracuseStep 2211083 = 3316625) B3316625
theorem B7462421 : Blo 2209435 7462421 := bbase (se 6 (by rfl) ⟨174900, by rfl⟩ : syracuseStep 7462421 = 349801) (by norm_num)
theorem B4974947 : Blo 2209435 4974947 := bstep (se 1 (by rfl) ⟨3731210, by rfl⟩ : syracuseStep 4974947 = 7462421) B7462421
theorem B3316631 : Blo 2209435 3316631 := bstep (se 1 (by rfl) ⟨2487473, by rfl⟩ : syracuseStep 3316631 = 4974947) B4974947
theorem B2211087 : Blo 2209435 2211087 := bstep (se 1 (by rfl) ⟨1658315, by rfl⟩ : syracuseStep 2211087 = 3316631) B3316631
theorem B3316637 : Blo 2209435 3316637 := bbase (se 3 (by rfl) ⟨621869, by rfl⟩ : syracuseStep 3316637 = 1243739) (by norm_num)
theorem B2211091 : Blo 2209435 2211091 := bstep (se 1 (by rfl) ⟨1658318, by rfl⟩ : syracuseStep 2211091 = 3316637) B3316637
theorem B4974965 : Blo 2209435 4974965 := bbase (se 5 (by rfl) ⟨233201, by rfl⟩ : syracuseStep 4974965 = 466403) (by norm_num)
theorem B3316643 : Blo 2209435 3316643 := bstep (se 1 (by rfl) ⟨2487482, by rfl⟩ : syracuseStep 3316643 = 4974965) B4974965
theorem B2211095 : Blo 2209435 2211095 := bstep (se 1 (by rfl) ⟨1658321, by rfl⟩ : syracuseStep 2211095 = 3316643) B3316643
theorem B2426041 : Blo 2209435 2426041 := bbase (se 2 (by rfl) ⟨909765, by rfl⟩ : syracuseStep 2426041 = 1819531) (by norm_num)
theorem B12938885 : Blo 2209435 12938885 := bstep (se 4 (by rfl) ⟨1213020, by rfl⟩ : syracuseStep 12938885 = 2426041) B2426041
theorem B8625923 : Blo 2209435 8625923 := bstep (se 1 (by rfl) ⟨6469442, by rfl⟩ : syracuseStep 8625923 = 12938885) B12938885
theorem B5750615 : Blo 2209435 5750615 := bstep (se 1 (by rfl) ⟨4312961, by rfl⟩ : syracuseStep 5750615 = 8625923) B8625923
theorem B3833743 : Blo 2209435 3833743 := bstep (se 1 (by rfl) ⟨2875307, by rfl⟩ : syracuseStep 3833743 = 5750615) B5750615
theorem B5111657 : Blo 2209435 5111657 := bstep (se 2 (by rfl) ⟨1916871, by rfl⟩ : syracuseStep 5111657 = 3833743) B3833743
theorem B3407771 : Blo 2209435 3407771 := bstep (se 1 (by rfl) ⟨2555828, by rfl⟩ : syracuseStep 3407771 = 5111657) B5111657
theorem B9087389 : Blo 2209435 9087389 := bstep (se 3 (by rfl) ⟨1703885, by rfl⟩ : syracuseStep 9087389 = 3407771) B3407771
theorem B6058259 : Blo 2209435 6058259 := bstep (se 1 (by rfl) ⟨4543694, by rfl⟩ : syracuseStep 6058259 = 9087389) B9087389
theorem B4038839 : Blo 2209435 4038839 := bstep (se 1 (by rfl) ⟨3029129, by rfl⟩ : syracuseStep 4038839 = 6058259) B6058259
theorem B2692559 : Blo 2209435 2692559 := bstep (se 1 (by rfl) ⟨2019419, by rfl⟩ : syracuseStep 2692559 = 4038839) B4038839
theorem B7180157 : Blo 2209435 7180157 := bstep (se 3 (by rfl) ⟨1346279, by rfl⟩ : syracuseStep 7180157 = 2692559) B2692559
theorem B4786771 : Blo 2209435 4786771 := bstep (se 1 (by rfl) ⟨3590078, by rfl⟩ : syracuseStep 4786771 = 7180157) B7180157
theorem B6382361 : Blo 2209435 6382361 := bstep (se 2 (by rfl) ⟨2393385, by rfl⟩ : syracuseStep 6382361 = 4786771) B4786771
theorem B17019629 : Blo 2209435 17019629 := bstep (se 3 (by rfl) ⟨3191180, by rfl⟩ : syracuseStep 17019629 = 6382361) B6382361
theorem B11346419 : Blo 2209435 11346419 := bstep (se 1 (by rfl) ⟨8509814, by rfl⟩ : syracuseStep 11346419 = 17019629) B17019629
theorem B7564279 : Blo 2209435 7564279 := bstep (se 1 (by rfl) ⟨5673209, by rfl⟩ : syracuseStep 7564279 = 11346419) B11346419
theorem B10085705 : Blo 2209435 10085705 := bstep (se 2 (by rfl) ⟨3782139, by rfl⟩ : syracuseStep 10085705 = 7564279) B7564279
theorem B6723803 : Blo 2209435 6723803 := bstep (se 1 (by rfl) ⟨5042852, by rfl⟩ : syracuseStep 6723803 = 10085705) B10085705
theorem B4482535 : Blo 2209435 4482535 := bstep (se 1 (by rfl) ⟨3361901, by rfl⟩ : syracuseStep 4482535 = 6723803) B6723803
theorem B5976713 : Blo 2209435 5976713 := bstep (se 2 (by rfl) ⟨2241267, by rfl⟩ : syracuseStep 5976713 = 4482535) B4482535
theorem B3984475 : Blo 2209435 3984475 := bstep (se 1 (by rfl) ⟨2988356, by rfl⟩ : syracuseStep 3984475 = 5976713) B5976713
theorem B5312633 : Blo 2209435 5312633 := bstep (se 2 (by rfl) ⟨1992237, by rfl⟩ : syracuseStep 5312633 = 3984475) B3984475
theorem B14167021 : Blo 2209435 14167021 := bstep (se 3 (by rfl) ⟨2656316, by rfl⟩ : syracuseStep 14167021 = 5312633) B5312633
theorem B18889361 : Blo 2209435 18889361 := bstep (se 2 (by rfl) ⟨7083510, by rfl⟩ : syracuseStep 18889361 = 14167021) B14167021
theorem B12592907 : Blo 2209435 12592907 := bstep (se 1 (by rfl) ⟨9444680, by rfl⟩ : syracuseStep 12592907 = 18889361) B18889361
theorem B8395271 : Blo 2209435 8395271 := bstep (se 1 (by rfl) ⟨6296453, by rfl⟩ : syracuseStep 8395271 = 12592907) B12592907
theorem B5596847 : Blo 2209435 5596847 := bstep (se 1 (by rfl) ⟨4197635, by rfl⟩ : syracuseStep 5596847 = 8395271) B8395271
theorem B3731231 : Blo 2209435 3731231 := bstep (se 1 (by rfl) ⟨2798423, by rfl⟩ : syracuseStep 3731231 = 5596847) B5596847
theorem B2487487 : Blo 2209435 2487487 := bstep (se 1 (by rfl) ⟨1865615, by rfl⟩ : syracuseStep 2487487 = 3731231) B3731231
theorem B3316649 : Blo 2209435 3316649 := bstep (se 2 (by rfl) ⟨1243743, by rfl⟩ : syracuseStep 3316649 = 2487487) B2487487
theorem B2211099 : Blo 2209435 2211099 := bstep (se 1 (by rfl) ⟨1658324, by rfl⟩ : syracuseStep 2211099 = 3316649) B3316649
theorem B8395285 : Blo 2209435 8395285 := bbase (se 6 (by rfl) ⟨196764, by rfl⟩ : syracuseStep 8395285 = 393529) (by norm_num)
theorem B11193713 : Blo 2209435 11193713 := bstep (se 2 (by rfl) ⟨4197642, by rfl⟩ : syracuseStep 11193713 = 8395285) B8395285
theorem B7462475 : Blo 2209435 7462475 := bstep (se 1 (by rfl) ⟨5596856, by rfl⟩ : syracuseStep 7462475 = 11193713) B11193713
theorem B4974983 : Blo 2209435 4974983 := bstep (se 1 (by rfl) ⟨3731237, by rfl⟩ : syracuseStep 4974983 = 7462475) B7462475
theorem B3316655 : Blo 2209435 3316655 := bstep (se 1 (by rfl) ⟨2487491, by rfl⟩ : syracuseStep 3316655 = 4974983) B4974983
theorem B2211103 : Blo 2209435 2211103 := bstep (se 1 (by rfl) ⟨1658327, by rfl⟩ : syracuseStep 2211103 = 3316655) B3316655
theorem B3316661 : Blo 2209435 3316661 := bbase (se 5 (by rfl) ⟨155468, by rfl⟩ : syracuseStep 3316661 = 310937) (by norm_num)
theorem B2211107 : Blo 2209435 2211107 := bstep (se 1 (by rfl) ⟨1658330, by rfl⟩ : syracuseStep 2211107 = 3316661) B3316661
theorem B5596877 : Blo 2209435 5596877 := bbase (se 3 (by rfl) ⟨1049414, by rfl⟩ : syracuseStep 5596877 = 2098829) (by norm_num)
theorem B3731251 : Blo 2209435 3731251 := bstep (se 1 (by rfl) ⟨2798438, by rfl⟩ : syracuseStep 3731251 = 5596877) B5596877
theorem B4975001 : Blo 2209435 4975001 := bstep (se 2 (by rfl) ⟨1865625, by rfl⟩ : syracuseStep 4975001 = 3731251) B3731251
theorem B3316667 : Blo 2209435 3316667 := bstep (se 1 (by rfl) ⟨2487500, by rfl⟩ : syracuseStep 3316667 = 4975001) B4975001
theorem B2211111 : Blo 2209435 2211111 := bstep (se 1 (by rfl) ⟨1658333, by rfl⟩ : syracuseStep 2211111 = 3316667) B3316667
theorem B2487505 : Blo 2209435 2487505 := bbase (se 2 (by rfl) ⟨932814, by rfl⟩ : syracuseStep 2487505 = 1865629) (by norm_num)
theorem B3316673 : Blo 2209435 3316673 := bstep (se 2 (by rfl) ⟨1243752, by rfl⟩ : syracuseStep 3316673 = 2487505) B2487505
theorem B2211115 : Blo 2209435 2211115 := bstep (se 1 (by rfl) ⟨1658336, by rfl⟩ : syracuseStep 2211115 = 3316673) B3316673
theorem B3688741 : Blo 2209435 3688741 := bbase (se 4 (by rfl) ⟨345819, by rfl⟩ : syracuseStep 3688741 = 691639) (by norm_num)
theorem B4918321 : Blo 2209435 4918321 := bstep (se 2 (by rfl) ⟨1844370, by rfl⟩ : syracuseStep 4918321 = 3688741) B3688741
theorem B6557761 : Blo 2209435 6557761 := bstep (se 2 (by rfl) ⟨2459160, by rfl⟩ : syracuseStep 6557761 = 4918321) B4918321
theorem B8743681 : Blo 2209435 8743681 := bstep (se 2 (by rfl) ⟨3278880, by rfl⟩ : syracuseStep 8743681 = 6557761) B6557761
theorem B11658241 : Blo 2209435 11658241 := bstep (se 2 (by rfl) ⟨4371840, by rfl⟩ : syracuseStep 11658241 = 8743681) B8743681
theorem B15544321 : Blo 2209435 15544321 := bstep (se 2 (by rfl) ⟨5829120, by rfl⟩ : syracuseStep 15544321 = 11658241) B11658241
theorem B82903045 : Blo 2209435 82903045 := bstep (se 4 (by rfl) ⟨7772160, by rfl⟩ : syracuseStep 82903045 = 15544321) B15544321
theorem B110537393 : Blo 2209435 110537393 := bstep (se 2 (by rfl) ⟨41451522, by rfl⟩ : syracuseStep 110537393 = 82903045) B82903045
theorem B294766381 : Blo 2209435 294766381 := bstep (se 3 (by rfl) ⟨55268696, by rfl⟩ : syracuseStep 294766381 = 110537393) B110537393
theorem B393021841 : Blo 2209435 393021841 := bstep (se 2 (by rfl) ⟨147383190, by rfl⟩ : syracuseStep 393021841 = 294766381) B294766381
theorem B524029121 : Blo 2209435 524029121 := bstep (se 2 (by rfl) ⟨196510920, by rfl⟩ : syracuseStep 524029121 = 393021841) B393021841
theorem B349352747 : Blo 2209435 349352747 := bstep (se 1 (by rfl) ⟨262014560, by rfl⟩ : syracuseStep 349352747 = 524029121) B524029121
theorem B232901831 : Blo 2209435 232901831 := bstep (se 1 (by rfl) ⟨174676373, by rfl⟩ : syracuseStep 232901831 = 349352747) B349352747
theorem B155267887 : Blo 2209435 155267887 := bstep (se 1 (by rfl) ⟨116450915, by rfl⟩ : syracuseStep 155267887 = 232901831) B232901831
theorem B207023849 : Blo 2209435 207023849 := bstep (se 2 (by rfl) ⟨77633943, by rfl⟩ : syracuseStep 207023849 = 155267887) B155267887
theorem B138015899 : Blo 2209435 138015899 := bstep (se 1 (by rfl) ⟨103511924, by rfl⟩ : syracuseStep 138015899 = 207023849) B207023849
theorem B92010599 : Blo 2209435 92010599 := bstep (se 1 (by rfl) ⟨69007949, by rfl⟩ : syracuseStep 92010599 = 138015899) B138015899
theorem B61340399 : Blo 2209435 61340399 := bstep (se 1 (by rfl) ⟨46005299, by rfl⟩ : syracuseStep 61340399 = 92010599) B92010599
theorem B40893599 : Blo 2209435 40893599 := bstep (se 1 (by rfl) ⟨30670199, by rfl⟩ : syracuseStep 40893599 = 61340399) B61340399
theorem B109049597 : Blo 2209435 109049597 := bstep (se 3 (by rfl) ⟨20446799, by rfl⟩ : syracuseStep 109049597 = 40893599) B40893599
theorem B72699731 : Blo 2209435 72699731 := bstep (se 1 (by rfl) ⟨54524798, by rfl⟩ : syracuseStep 72699731 = 109049597) B109049597
theorem B48466487 : Blo 2209435 48466487 := bstep (se 1 (by rfl) ⟨36349865, by rfl⟩ : syracuseStep 48466487 = 72699731) B72699731
theorem B32310991 : Blo 2209435 32310991 := bstep (se 1 (by rfl) ⟨24233243, by rfl⟩ : syracuseStep 32310991 = 48466487) B48466487
theorem B43081321 : Blo 2209435 43081321 := bstep (se 2 (by rfl) ⟨16155495, by rfl⟩ : syracuseStep 43081321 = 32310991) B32310991
theorem B57441761 : Blo 2209435 57441761 := bstep (se 2 (by rfl) ⟨21540660, by rfl⟩ : syracuseStep 57441761 = 43081321) B43081321
theorem B38294507 : Blo 2209435 38294507 := bstep (se 1 (by rfl) ⟨28720880, by rfl⟩ : syracuseStep 38294507 = 57441761) B57441761
theorem B25529671 : Blo 2209435 25529671 := bstep (se 1 (by rfl) ⟨19147253, by rfl⟩ : syracuseStep 25529671 = 38294507) B38294507
theorem B34039561 : Blo 2209435 34039561 := bstep (se 2 (by rfl) ⟨12764835, by rfl⟩ : syracuseStep 34039561 = 25529671) B25529671
theorem B45386081 : Blo 2209435 45386081 := bstep (se 2 (by rfl) ⟨17019780, by rfl⟩ : syracuseStep 45386081 = 34039561) B34039561
theorem B30257387 : Blo 2209435 30257387 := bstep (se 1 (by rfl) ⟨22693040, by rfl⟩ : syracuseStep 30257387 = 45386081) B45386081
theorem B20171591 : Blo 2209435 20171591 := bstep (se 1 (by rfl) ⟨15128693, by rfl⟩ : syracuseStep 20171591 = 30257387) B30257387
theorem B13447727 : Blo 2209435 13447727 := bstep (se 1 (by rfl) ⟨10085795, by rfl⟩ : syracuseStep 13447727 = 20171591) B20171591
theorem B8965151 : Blo 2209435 8965151 := bstep (se 1 (by rfl) ⟨6723863, by rfl⟩ : syracuseStep 8965151 = 13447727) B13447727
theorem B5976767 : Blo 2209435 5976767 := bstep (se 1 (by rfl) ⟨4482575, by rfl⟩ : syracuseStep 5976767 = 8965151) B8965151
theorem B15938045 : Blo 2209435 15938045 := bstep (se 3 (by rfl) ⟨2988383, by rfl⟩ : syracuseStep 15938045 = 5976767) B5976767
theorem B10625363 : Blo 2209435 10625363 := bstep (se 1 (by rfl) ⟨7969022, by rfl⟩ : syracuseStep 10625363 = 15938045) B15938045
theorem B7083575 : Blo 2209435 7083575 := bstep (se 1 (by rfl) ⟨5312681, by rfl⟩ : syracuseStep 7083575 = 10625363) B10625363
theorem B4722383 : Blo 2209435 4722383 := bstep (se 1 (by rfl) ⟨3541787, by rfl⟩ : syracuseStep 4722383 = 7083575) B7083575
theorem B3148255 : Blo 2209435 3148255 := bstep (se 1 (by rfl) ⟨2361191, by rfl⟩ : syracuseStep 3148255 = 4722383) B4722383
theorem B4197673 : Blo 2209435 4197673 := bstep (se 2 (by rfl) ⟨1574127, by rfl⟩ : syracuseStep 4197673 = 3148255) B3148255
theorem B5596897 : Blo 2209435 5596897 := bstep (se 2 (by rfl) ⟨2098836, by rfl⟩ : syracuseStep 5596897 = 4197673) B4197673
theorem B7462529 : Blo 2209435 7462529 := bstep (se 2 (by rfl) ⟨2798448, by rfl⟩ : syracuseStep 7462529 = 5596897) B5596897
theorem B4975019 : Blo 2209435 4975019 := bstep (se 1 (by rfl) ⟨3731264, by rfl⟩ : syracuseStep 4975019 = 7462529) B7462529
theorem B3316679 : Blo 2209435 3316679 := bstep (se 1 (by rfl) ⟨2487509, by rfl⟩ : syracuseStep 3316679 = 4975019) B4975019
theorem B2211119 : Blo 2209435 2211119 := bstep (se 1 (by rfl) ⟨1658339, by rfl⟩ : syracuseStep 2211119 = 3316679) B3316679
theorem B3316685 : Blo 2209435 3316685 := bbase (se 3 (by rfl) ⟨621878, by rfl⟩ : syracuseStep 3316685 = 1243757) (by norm_num)
theorem B2211123 : Blo 2209435 2211123 := bstep (se 1 (by rfl) ⟨1658342, by rfl⟩ : syracuseStep 2211123 = 3316685) B3316685
theorem B4975037 : Blo 2209435 4975037 := bbase (se 3 (by rfl) ⟨932819, by rfl⟩ : syracuseStep 4975037 = 1865639) (by norm_num)
theorem B3316691 : Blo 2209435 3316691 := bstep (se 1 (by rfl) ⟨2487518, by rfl⟩ : syracuseStep 3316691 = 4975037) B4975037
theorem B2211127 : Blo 2209435 2211127 := bstep (se 1 (by rfl) ⟨1658345, by rfl⟩ : syracuseStep 2211127 = 3316691) B3316691
theorem B3731285 : Blo 2209435 3731285 := bbase (se 9 (by rfl) ⟨10931, by rfl⟩ : syracuseStep 3731285 = 21863) (by norm_num)
theorem B2487523 : Blo 2209435 2487523 := bstep (se 1 (by rfl) ⟨1865642, by rfl⟩ : syracuseStep 2487523 = 3731285) B3731285
theorem B3316697 : Blo 2209435 3316697 := bstep (se 2 (by rfl) ⟨1243761, by rfl⟩ : syracuseStep 3316697 = 2487523) B2487523
theorem B2211131 : Blo 2209435 2211131 := bstep (se 1 (by rfl) ⟨1658348, by rfl⟩ : syracuseStep 2211131 = 3316697) B3316697
theorem B11658325 : Blo 2209435 11658325 := bbase (se 8 (by rfl) ⟨68310, by rfl⟩ : syracuseStep 11658325 = 136621) (by norm_num)
theorem B15544433 : Blo 2209435 15544433 := bstep (se 2 (by rfl) ⟨5829162, by rfl⟩ : syracuseStep 15544433 = 11658325) B11658325
theorem B10362955 : Blo 2209435 10362955 := bstep (se 1 (by rfl) ⟨7772216, by rfl⟩ : syracuseStep 10362955 = 15544433) B15544433
theorem B221076373 : Blo 2209435 221076373 := bstep (se 6 (by rfl) ⟨5181477, by rfl⟩ : syracuseStep 221076373 = 10362955) B10362955
theorem B294768497 : Blo 2209435 294768497 := bstep (se 2 (by rfl) ⟨110538186, by rfl⟩ : syracuseStep 294768497 = 221076373) B221076373
theorem B196512331 : Blo 2209435 196512331 := bstep (se 1 (by rfl) ⟨147384248, by rfl⟩ : syracuseStep 196512331 = 294768497) B294768497
theorem B262016441 : Blo 2209435 262016441 := bstep (se 2 (by rfl) ⟨98256165, by rfl⟩ : syracuseStep 262016441 = 196512331) B196512331
theorem B174677627 : Blo 2209435 174677627 := bstep (se 1 (by rfl) ⟨131008220, by rfl⟩ : syracuseStep 174677627 = 262016441) B262016441
theorem B116451751 : Blo 2209435 116451751 := bstep (se 1 (by rfl) ⟨87338813, by rfl⟩ : syracuseStep 116451751 = 174677627) B174677627
theorem B155269001 : Blo 2209435 155269001 := bstep (se 2 (by rfl) ⟨58225875, by rfl⟩ : syracuseStep 155269001 = 116451751) B116451751
theorem B103512667 : Blo 2209435 103512667 := bstep (se 1 (by rfl) ⟨77634500, by rfl⟩ : syracuseStep 103512667 = 155269001) B155269001
theorem B138016889 : Blo 2209435 138016889 := bstep (se 2 (by rfl) ⟨51756333, by rfl⟩ : syracuseStep 138016889 = 103512667) B103512667
theorem B92011259 : Blo 2209435 92011259 := bstep (se 1 (by rfl) ⟨69008444, by rfl⟩ : syracuseStep 92011259 = 138016889) B138016889
theorem B245363357 : Blo 2209435 245363357 := bstep (se 3 (by rfl) ⟨46005629, by rfl⟩ : syracuseStep 245363357 = 92011259) B92011259
theorem B163575571 : Blo 2209435 163575571 := bstep (se 1 (by rfl) ⟨122681678, by rfl⟩ : syracuseStep 163575571 = 245363357) B245363357
theorem B218100761 : Blo 2209435 218100761 := bstep (se 2 (by rfl) ⟨81787785, by rfl⟩ : syracuseStep 218100761 = 163575571) B163575571
theorem B145400507 : Blo 2209435 145400507 := bstep (se 1 (by rfl) ⟨109050380, by rfl⟩ : syracuseStep 145400507 = 218100761) B218100761
theorem B96933671 : Blo 2209435 96933671 := bstep (se 1 (by rfl) ⟨72700253, by rfl⟩ : syracuseStep 96933671 = 145400507) B145400507
theorem B64622447 : Blo 2209435 64622447 := bstep (se 1 (by rfl) ⟨48466835, by rfl⟩ : syracuseStep 64622447 = 96933671) B96933671
theorem B43081631 : Blo 2209435 43081631 := bstep (se 1 (by rfl) ⟨32311223, by rfl⟩ : syracuseStep 43081631 = 64622447) B64622447
theorem B28721087 : Blo 2209435 28721087 := bstep (se 1 (by rfl) ⟨21540815, by rfl⟩ : syracuseStep 28721087 = 43081631) B43081631
theorem B19147391 : Blo 2209435 19147391 := bstep (se 1 (by rfl) ⟨14360543, by rfl⟩ : syracuseStep 19147391 = 28721087) B28721087
theorem B12764927 : Blo 2209435 12764927 := bstep (se 1 (by rfl) ⟨9573695, by rfl⟩ : syracuseStep 12764927 = 19147391) B19147391
theorem B8509951 : Blo 2209435 8509951 := bstep (se 1 (by rfl) ⟨6382463, by rfl⟩ : syracuseStep 8509951 = 12764927) B12764927
theorem B11346601 : Blo 2209435 11346601 := bstep (se 2 (by rfl) ⟨4254975, by rfl⟩ : syracuseStep 11346601 = 8509951) B8509951
theorem B15128801 : Blo 2209435 15128801 := bstep (se 2 (by rfl) ⟨5673300, by rfl⟩ : syracuseStep 15128801 = 11346601) B11346601
theorem B10085867 : Blo 2209435 10085867 := bstep (se 1 (by rfl) ⟨7564400, by rfl⟩ : syracuseStep 10085867 = 15128801) B15128801
theorem B6723911 : Blo 2209435 6723911 := bstep (se 1 (by rfl) ⟨5042933, by rfl⟩ : syracuseStep 6723911 = 10085867) B10085867
theorem B17930429 : Blo 2209435 17930429 := bstep (se 3 (by rfl) ⟨3361955, by rfl⟩ : syracuseStep 17930429 = 6723911) B6723911
theorem B11953619 : Blo 2209435 11953619 := bstep (se 1 (by rfl) ⟨8965214, by rfl⟩ : syracuseStep 11953619 = 17930429) B17930429
theorem B7969079 : Blo 2209435 7969079 := bstep (se 1 (by rfl) ⟨5976809, by rfl⟩ : syracuseStep 7969079 = 11953619) B11953619
theorem B5312719 : Blo 2209435 5312719 := bstep (se 1 (by rfl) ⟨3984539, by rfl⟩ : syracuseStep 5312719 = 7969079) B7969079
theorem B7083625 : Blo 2209435 7083625 := bstep (se 2 (by rfl) ⟨2656359, by rfl⟩ : syracuseStep 7083625 = 5312719) B5312719
theorem B9444833 : Blo 2209435 9444833 := bstep (se 2 (by rfl) ⟨3541812, by rfl⟩ : syracuseStep 9444833 = 7083625) B7083625
theorem B6296555 : Blo 2209435 6296555 := bstep (se 1 (by rfl) ⟨4722416, by rfl⟩ : syracuseStep 6296555 = 9444833) B9444833
theorem B16790813 : Blo 2209435 16790813 := bstep (se 3 (by rfl) ⟨3148277, by rfl⟩ : syracuseStep 16790813 = 6296555) B6296555
theorem B11193875 : Blo 2209435 11193875 := bstep (se 1 (by rfl) ⟨8395406, by rfl⟩ : syracuseStep 11193875 = 16790813) B16790813
theorem B7462583 : Blo 2209435 7462583 := bstep (se 1 (by rfl) ⟨5596937, by rfl⟩ : syracuseStep 7462583 = 11193875) B11193875
theorem B4975055 : Blo 2209435 4975055 := bstep (se 1 (by rfl) ⟨3731291, by rfl⟩ : syracuseStep 4975055 = 7462583) B7462583
theorem B3316703 : Blo 2209435 3316703 := bstep (se 1 (by rfl) ⟨2487527, by rfl⟩ : syracuseStep 3316703 = 4975055) B4975055
theorem B2211135 : Blo 2209435 2211135 := bstep (se 1 (by rfl) ⟨1658351, by rfl⟩ : syracuseStep 2211135 = 3316703) B3316703
theorem B3316709 : Blo 2209435 3316709 := bbase (se 4 (by rfl) ⟨310941, by rfl⟩ : syracuseStep 3316709 = 621883) (by norm_num)
theorem B2211139 : Blo 2209435 2211139 := bstep (se 1 (by rfl) ⟨1658354, by rfl⟩ : syracuseStep 2211139 = 3316709) B3316709
theorem B9444869 : Blo 2209435 9444869 := bbase (se 4 (by rfl) ⟨885456, by rfl⟩ : syracuseStep 9444869 = 1770913) (by norm_num)
theorem B6296579 : Blo 2209435 6296579 := bstep (se 1 (by rfl) ⟨4722434, by rfl⟩ : syracuseStep 6296579 = 9444869) B9444869
theorem B4197719 : Blo 2209435 4197719 := bstep (se 1 (by rfl) ⟨3148289, by rfl⟩ : syracuseStep 4197719 = 6296579) B6296579
theorem B2798479 : Blo 2209435 2798479 := bstep (se 1 (by rfl) ⟨2098859, by rfl⟩ : syracuseStep 2798479 = 4197719) B4197719
theorem B3731305 : Blo 2209435 3731305 := bstep (se 2 (by rfl) ⟨1399239, by rfl⟩ : syracuseStep 3731305 = 2798479) B2798479
theorem B4975073 : Blo 2209435 4975073 := bstep (se 2 (by rfl) ⟨1865652, by rfl⟩ : syracuseStep 4975073 = 3731305) B3731305
theorem B3316715 : Blo 2209435 3316715 := bstep (se 1 (by rfl) ⟨2487536, by rfl⟩ : syracuseStep 3316715 = 4975073) B4975073
theorem B2211143 : Blo 2209435 2211143 := bstep (se 1 (by rfl) ⟨1658357, by rfl⟩ : syracuseStep 2211143 = 3316715) B3316715
theorem B2487541 : Blo 2209435 2487541 := bbase (se 5 (by rfl) ⟨116603, by rfl⟩ : syracuseStep 2487541 = 233207) (by norm_num)
theorem B3316721 : Blo 2209435 3316721 := bstep (se 2 (by rfl) ⟨1243770, by rfl⟩ : syracuseStep 3316721 = 2487541) B2487541
theorem B2211147 : Blo 2209435 2211147 := bstep (se 1 (by rfl) ⟨1658360, by rfl⟩ : syracuseStep 2211147 = 3316721) B3316721
theorem B2798489 : Blo 2209435 2798489 := bbase (se 2 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 2798489 = 2098867) (by norm_num)
theorem B7462637 : Blo 2209435 7462637 := bstep (se 3 (by rfl) ⟨1399244, by rfl⟩ : syracuseStep 7462637 = 2798489) B2798489
theorem B4975091 : Blo 2209435 4975091 := bstep (se 1 (by rfl) ⟨3731318, by rfl⟩ : syracuseStep 4975091 = 7462637) B7462637
theorem B3316727 : Blo 2209435 3316727 := bstep (se 1 (by rfl) ⟨2487545, by rfl⟩ : syracuseStep 3316727 = 4975091) B4975091
theorem B2211151 : Blo 2209435 2211151 := bstep (se 1 (by rfl) ⟨1658363, by rfl⟩ : syracuseStep 2211151 = 3316727) B3316727
theorem B3316733 : Blo 2209435 3316733 := bbase (se 3 (by rfl) ⟨621887, by rfl⟩ : syracuseStep 3316733 = 1243775) (by norm_num)
theorem B2211155 : Blo 2209435 2211155 := bstep (se 1 (by rfl) ⟨1658366, by rfl⟩ : syracuseStep 2211155 = 3316733) B3316733
theorem B4975109 : Blo 2209435 4975109 := bbase (se 4 (by rfl) ⟨466416, by rfl⟩ : syracuseStep 4975109 = 932833) (by norm_num)
theorem B3316739 : Blo 2209435 3316739 := bstep (se 1 (by rfl) ⟨2487554, by rfl⟩ : syracuseStep 3316739 = 4975109) B4975109
theorem B2211159 : Blo 2209435 2211159 := bstep (se 1 (by rfl) ⟨1658369, by rfl⟩ : syracuseStep 2211159 = 3316739) B3316739
theorem B4197757 : Blo 2209435 4197757 := bbase (se 3 (by rfl) ⟨787079, by rfl⟩ : syracuseStep 4197757 = 1574159) (by norm_num)
theorem B5597009 : Blo 2209435 5597009 := bstep (se 2 (by rfl) ⟨2098878, by rfl⟩ : syracuseStep 5597009 = 4197757) B4197757
theorem B3731339 : Blo 2209435 3731339 := bstep (se 1 (by rfl) ⟨2798504, by rfl⟩ : syracuseStep 3731339 = 5597009) B5597009
theorem B2487559 : Blo 2209435 2487559 := bstep (se 1 (by rfl) ⟨1865669, by rfl⟩ : syracuseStep 2487559 = 3731339) B3731339
theorem B3316745 : Blo 2209435 3316745 := bstep (se 2 (by rfl) ⟨1243779, by rfl⟩ : syracuseStep 3316745 = 2487559) B2487559
theorem B2211163 : Blo 2209435 2211163 := bstep (se 1 (by rfl) ⟨1658372, by rfl⟩ : syracuseStep 2211163 = 3316745) B3316745
theorem B11194037 : Blo 2209435 11194037 := bbase (se 5 (by rfl) ⟨524720, by rfl⟩ : syracuseStep 11194037 = 1049441) (by norm_num)
theorem B7462691 : Blo 2209435 7462691 := bstep (se 1 (by rfl) ⟨5597018, by rfl⟩ : syracuseStep 7462691 = 11194037) B11194037
theorem B4975127 : Blo 2209435 4975127 := bstep (se 1 (by rfl) ⟨3731345, by rfl⟩ : syracuseStep 4975127 = 7462691) B7462691
theorem B3316751 : Blo 2209435 3316751 := bstep (se 1 (by rfl) ⟨2487563, by rfl⟩ : syracuseStep 3316751 = 4975127) B4975127
theorem B2211167 : Blo 2209435 2211167 := bstep (se 1 (by rfl) ⟨1658375, by rfl⟩ : syracuseStep 2211167 = 3316751) B3316751
theorem B3316757 : Blo 2209435 3316757 := bbase (se 6 (by rfl) ⟨77736, by rfl⟩ : syracuseStep 3316757 = 155473) (by norm_num)
theorem B2211171 : Blo 2209435 2211171 := bstep (se 1 (by rfl) ⟨1658378, by rfl⟩ : syracuseStep 2211171 = 3316757) B3316757
theorem B2271925 : Blo 2209435 2271925 := bbase (se 5 (by rfl) ⟨106496, by rfl⟩ : syracuseStep 2271925 = 212993) (by norm_num)
theorem B3029233 : Blo 2209435 3029233 := bstep (se 2 (by rfl) ⟨1135962, by rfl⟩ : syracuseStep 3029233 = 2271925) B2271925
theorem B4038977 : Blo 2209435 4038977 := bstep (se 2 (by rfl) ⟨1514616, by rfl⟩ : syracuseStep 4038977 = 3029233) B3029233
theorem B2692651 : Blo 2209435 2692651 := bstep (se 1 (by rfl) ⟨2019488, by rfl⟩ : syracuseStep 2692651 = 4038977) B4038977
theorem B3590201 : Blo 2209435 3590201 := bstep (se 2 (by rfl) ⟨1346325, by rfl⟩ : syracuseStep 3590201 = 2692651) B2692651
theorem B9573869 : Blo 2209435 9573869 := bstep (se 3 (by rfl) ⟨1795100, by rfl⟩ : syracuseStep 9573869 = 3590201) B3590201
theorem B6382579 : Blo 2209435 6382579 := bstep (se 1 (by rfl) ⟨4786934, by rfl⟩ : syracuseStep 6382579 = 9573869) B9573869
theorem B8510105 : Blo 2209435 8510105 := bstep (se 2 (by rfl) ⟨3191289, by rfl⟩ : syracuseStep 8510105 = 6382579) B6382579
theorem B5673403 : Blo 2209435 5673403 := bstep (se 1 (by rfl) ⟨4255052, by rfl⟩ : syracuseStep 5673403 = 8510105) B8510105
theorem B7564537 : Blo 2209435 7564537 := bstep (se 2 (by rfl) ⟨2836701, by rfl⟩ : syracuseStep 7564537 = 5673403) B5673403
theorem B10086049 : Blo 2209435 10086049 := bstep (se 2 (by rfl) ⟨3782268, by rfl⟩ : syracuseStep 10086049 = 7564537) B7564537
theorem B13448065 : Blo 2209435 13448065 := bstep (se 2 (by rfl) ⟨5043024, by rfl⟩ : syracuseStep 13448065 = 10086049) B10086049
theorem B17930753 : Blo 2209435 17930753 := bstep (se 2 (by rfl) ⟨6724032, by rfl⟩ : syracuseStep 17930753 = 13448065) B13448065
theorem B11953835 : Blo 2209435 11953835 := bstep (se 1 (by rfl) ⟨8965376, by rfl⟩ : syracuseStep 11953835 = 17930753) B17930753
theorem B7969223 : Blo 2209435 7969223 := bstep (se 1 (by rfl) ⟨5976917, by rfl⟩ : syracuseStep 7969223 = 11953835) B11953835
theorem B21251261 : Blo 2209435 21251261 := bstep (se 3 (by rfl) ⟨3984611, by rfl⟩ : syracuseStep 21251261 = 7969223) B7969223
theorem B14167507 : Blo 2209435 14167507 := bstep (se 1 (by rfl) ⟨10625630, by rfl⟩ : syracuseStep 14167507 = 21251261) B21251261
theorem B18890009 : Blo 2209435 18890009 := bstep (se 2 (by rfl) ⟨7083753, by rfl⟩ : syracuseStep 18890009 = 14167507) B14167507
theorem B12593339 : Blo 2209435 12593339 := bstep (se 1 (by rfl) ⟨9445004, by rfl⟩ : syracuseStep 12593339 = 18890009) B18890009
theorem B8395559 : Blo 2209435 8395559 := bstep (se 1 (by rfl) ⟨6296669, by rfl⟩ : syracuseStep 8395559 = 12593339) B12593339
theorem B5597039 : Blo 2209435 5597039 := bstep (se 1 (by rfl) ⟨4197779, by rfl⟩ : syracuseStep 5597039 = 8395559) B8395559
theorem B3731359 : Blo 2209435 3731359 := bstep (se 1 (by rfl) ⟨2798519, by rfl⟩ : syracuseStep 3731359 = 5597039) B5597039
theorem B4975145 : Blo 2209435 4975145 := bstep (se 2 (by rfl) ⟨1865679, by rfl⟩ : syracuseStep 4975145 = 3731359) B3731359
theorem B3316763 : Blo 2209435 3316763 := bstep (se 1 (by rfl) ⟨2487572, by rfl⟩ : syracuseStep 3316763 = 4975145) B4975145
theorem B2211175 : Blo 2209435 2211175 := bstep (se 1 (by rfl) ⟨1658381, by rfl⟩ : syracuseStep 2211175 = 3316763) B3316763
theorem B2487577 : Blo 2209435 2487577 := bbase (se 2 (by rfl) ⟨932841, by rfl⟩ : syracuseStep 2487577 = 1865683) (by norm_num)
theorem B3316769 : Blo 2209435 3316769 := bstep (se 2 (by rfl) ⟨1243788, by rfl⟩ : syracuseStep 3316769 = 2487577) B2487577
theorem B2211179 : Blo 2209435 2211179 := bstep (se 1 (by rfl) ⟨1658384, by rfl⟩ : syracuseStep 2211179 = 3316769) B3316769
theorem B8395589 : Blo 2209435 8395589 := bbase (se 4 (by rfl) ⟨787086, by rfl⟩ : syracuseStep 8395589 = 1574173) (by norm_num)
theorem B5597059 : Blo 2209435 5597059 := bstep (se 1 (by rfl) ⟨4197794, by rfl⟩ : syracuseStep 5597059 = 8395589) B8395589
theorem B7462745 : Blo 2209435 7462745 := bstep (se 2 (by rfl) ⟨2798529, by rfl⟩ : syracuseStep 7462745 = 5597059) B5597059
theorem B4975163 : Blo 2209435 4975163 := bstep (se 1 (by rfl) ⟨3731372, by rfl⟩ : syracuseStep 4975163 = 7462745) B7462745
theorem B3316775 : Blo 2209435 3316775 := bstep (se 1 (by rfl) ⟨2487581, by rfl⟩ : syracuseStep 3316775 = 4975163) B4975163
theorem B2211183 : Blo 2209435 2211183 := bstep (se 1 (by rfl) ⟨1658387, by rfl⟩ : syracuseStep 2211183 = 3316775) B3316775
theorem B3316781 : Blo 2209435 3316781 := bbase (se 3 (by rfl) ⟨621896, by rfl⟩ : syracuseStep 3316781 = 1243793) (by norm_num)
theorem B2211187 : Blo 2209435 2211187 := bstep (se 1 (by rfl) ⟨1658390, by rfl⟩ : syracuseStep 2211187 = 3316781) B3316781
theorem B4975181 : Blo 2209435 4975181 := bbase (se 3 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 4975181 = 1865693) (by norm_num)
theorem B3316787 : Blo 2209435 3316787 := bstep (se 1 (by rfl) ⟨2487590, by rfl⟩ : syracuseStep 3316787 = 4975181) B4975181
theorem B2211191 : Blo 2209435 2211191 := bstep (se 1 (by rfl) ⟨1658393, by rfl⟩ : syracuseStep 2211191 = 3316787) B3316787
theorem B2798545 : Blo 2209435 2798545 := bbase (se 2 (by rfl) ⟨1049454, by rfl⟩ : syracuseStep 2798545 = 2098909) (by norm_num)
theorem B3731393 : Blo 2209435 3731393 := bstep (se 2 (by rfl) ⟨1399272, by rfl⟩ : syracuseStep 3731393 = 2798545) B2798545
theorem B2487595 : Blo 2209435 2487595 := bstep (se 1 (by rfl) ⟨1865696, by rfl⟩ : syracuseStep 2487595 = 3731393) B3731393
theorem B3316793 : Blo 2209435 3316793 := bstep (se 2 (by rfl) ⟨1243797, by rfl⟩ : syracuseStep 3316793 = 2487595) B2487595
theorem B2211195 : Blo 2209435 2211195 := bstep (se 1 (by rfl) ⟨1658396, by rfl⟩ : syracuseStep 2211195 = 3316793) B3316793
theorem B13448213 : Blo 2209435 13448213 := bbase (se 6 (by rfl) ⟨315192, by rfl⟩ : syracuseStep 13448213 = 630385) (by norm_num)
theorem B8965475 : Blo 2209435 8965475 := bstep (se 1 (by rfl) ⟨6724106, by rfl⟩ : syracuseStep 8965475 = 13448213) B13448213
theorem B5976983 : Blo 2209435 5976983 := bstep (se 1 (by rfl) ⟨4482737, by rfl⟩ : syracuseStep 5976983 = 8965475) B8965475
theorem B3984655 : Blo 2209435 3984655 := bstep (se 1 (by rfl) ⟨2988491, by rfl⟩ : syracuseStep 3984655 = 5976983) B5976983
theorem B5312873 : Blo 2209435 5312873 := bstep (se 2 (by rfl) ⟨1992327, by rfl⟩ : syracuseStep 5312873 = 3984655) B3984655
theorem B3541915 : Blo 2209435 3541915 := bstep (se 1 (by rfl) ⟨2656436, by rfl⟩ : syracuseStep 3541915 = 5312873) B5312873
theorem B4722553 : Blo 2209435 4722553 := bstep (se 2 (by rfl) ⟨1770957, by rfl⟩ : syracuseStep 4722553 = 3541915) B3541915
theorem B25186949 : Blo 2209435 25186949 := bstep (se 4 (by rfl) ⟨2361276, by rfl⟩ : syracuseStep 25186949 = 4722553) B4722553
theorem B16791299 : Blo 2209435 16791299 := bstep (se 1 (by rfl) ⟨12593474, by rfl⟩ : syracuseStep 16791299 = 25186949) B25186949
theorem B11194199 : Blo 2209435 11194199 := bstep (se 1 (by rfl) ⟨8395649, by rfl⟩ : syracuseStep 11194199 = 16791299) B16791299
theorem B7462799 : Blo 2209435 7462799 := bstep (se 1 (by rfl) ⟨5597099, by rfl⟩ : syracuseStep 7462799 = 11194199) B11194199
theorem B4975199 : Blo 2209435 4975199 := bstep (se 1 (by rfl) ⟨3731399, by rfl⟩ : syracuseStep 4975199 = 7462799) B7462799
theorem B3316799 : Blo 2209435 3316799 := bstep (se 1 (by rfl) ⟨2487599, by rfl⟩ : syracuseStep 3316799 = 4975199) B4975199
theorem B2211199 : Blo 2209435 2211199 := bstep (se 1 (by rfl) ⟨1658399, by rfl⟩ : syracuseStep 2211199 = 3316799) B3316799
theorem B3316805 : Blo 2209435 3316805 := bbase (se 4 (by rfl) ⟨310950, by rfl⟩ : syracuseStep 3316805 = 621901) (by norm_num)
theorem B2211203 : Blo 2209435 2211203 := bstep (se 1 (by rfl) ⟨1658402, by rfl⟩ : syracuseStep 2211203 = 3316805) B3316805
theorem B3731413 : Blo 2209435 3731413 := bbase (se 7 (by rfl) ⟨43727, by rfl⟩ : syracuseStep 3731413 = 87455) (by norm_num)
theorem B4975217 : Blo 2209435 4975217 := bstep (se 2 (by rfl) ⟨1865706, by rfl⟩ : syracuseStep 4975217 = 3731413) B3731413
theorem B3316811 : Blo 2209435 3316811 := bstep (se 1 (by rfl) ⟨2487608, by rfl⟩ : syracuseStep 3316811 = 4975217) B4975217
theorem B2211207 : Blo 2209435 2211207 := bstep (se 1 (by rfl) ⟨1658405, by rfl⟩ : syracuseStep 2211207 = 3316811) B3316811
theorem B2487613 : Blo 2209435 2487613 := bbase (se 3 (by rfl) ⟨466427, by rfl⟩ : syracuseStep 2487613 = 932855) (by norm_num)
theorem B3316817 : Blo 2209435 3316817 := bstep (se 2 (by rfl) ⟨1243806, by rfl⟩ : syracuseStep 3316817 = 2487613) B2487613
theorem B2211211 : Blo 2209435 2211211 := bstep (se 1 (by rfl) ⟨1658408, by rfl⟩ : syracuseStep 2211211 = 3316817) B3316817
theorem B7462853 : Blo 2209435 7462853 := bbase (se 4 (by rfl) ⟨699642, by rfl⟩ : syracuseStep 7462853 = 1399285) (by norm_num)
theorem B4975235 : Blo 2209435 4975235 := bstep (se 1 (by rfl) ⟨3731426, by rfl⟩ : syracuseStep 4975235 = 7462853) B7462853
theorem B3316823 : Blo 2209435 3316823 := bstep (se 1 (by rfl) ⟨2487617, by rfl⟩ : syracuseStep 3316823 = 4975235) B4975235
theorem B2211215 : Blo 2209435 2211215 := bstep (se 1 (by rfl) ⟨1658411, by rfl⟩ : syracuseStep 2211215 = 3316823) B3316823
theorem B3316829 : Blo 2209435 3316829 := bbase (se 3 (by rfl) ⟨621905, by rfl⟩ : syracuseStep 3316829 = 1243811) (by norm_num)
theorem B2211219 : Blo 2209435 2211219 := bstep (se 1 (by rfl) ⟨1658414, by rfl⟩ : syracuseStep 2211219 = 3316829) B3316829
theorem B4975253 : Blo 2209435 4975253 := bbase (se 6 (by rfl) ⟨116607, by rfl⟩ : syracuseStep 4975253 = 233215) (by norm_num)
theorem B3316835 : Blo 2209435 3316835 := bstep (se 1 (by rfl) ⟨2487626, by rfl⟩ : syracuseStep 3316835 = 4975253) B4975253
theorem B2211223 : Blo 2209435 2211223 := bstep (se 1 (by rfl) ⟨1658417, by rfl⟩ : syracuseStep 2211223 = 3316835) B3316835
theorem B5977061 : Blo 2209435 5977061 := bbase (se 4 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 5977061 = 1120699) (by norm_num)
theorem B3984707 : Blo 2209435 3984707 := bstep (se 1 (by rfl) ⟨2988530, by rfl⟩ : syracuseStep 3984707 = 5977061) B5977061
theorem B2656471 : Blo 2209435 2656471 := bstep (se 1 (by rfl) ⟨1992353, by rfl⟩ : syracuseStep 2656471 = 3984707) B3984707
theorem B3541961 : Blo 2209435 3541961 := bstep (se 2 (by rfl) ⟨1328235, by rfl⟩ : syracuseStep 3541961 = 2656471) B2656471
theorem B2361307 : Blo 2209435 2361307 := bstep (se 1 (by rfl) ⟨1770980, by rfl⟩ : syracuseStep 2361307 = 3541961) B3541961
theorem B3148409 : Blo 2209435 3148409 := bstep (se 2 (by rfl) ⟨1180653, by rfl⟩ : syracuseStep 3148409 = 2361307) B2361307
theorem B8395757 : Blo 2209435 8395757 := bstep (se 3 (by rfl) ⟨1574204, by rfl⟩ : syracuseStep 8395757 = 3148409) B3148409
theorem B5597171 : Blo 2209435 5597171 := bstep (se 1 (by rfl) ⟨4197878, by rfl⟩ : syracuseStep 5597171 = 8395757) B8395757
theorem B3731447 : Blo 2209435 3731447 := bstep (se 1 (by rfl) ⟨2798585, by rfl⟩ : syracuseStep 3731447 = 5597171) B5597171
theorem B2487631 : Blo 2209435 2487631 := bstep (se 1 (by rfl) ⟨1865723, by rfl⟩ : syracuseStep 2487631 = 3731447) B3731447
theorem B3316841 : Blo 2209435 3316841 := bstep (se 2 (by rfl) ⟨1243815, by rfl⟩ : syracuseStep 3316841 = 2487631) B2487631
theorem B2211227 : Blo 2209435 2211227 := bstep (se 1 (by rfl) ⟨1658420, by rfl⟩ : syracuseStep 2211227 = 3316841) B3316841
theorem B13448405 : Blo 2209435 13448405 := bbase (se 7 (by rfl) ⟨157598, by rfl⟩ : syracuseStep 13448405 = 315197) (by norm_num)
theorem B8965603 : Blo 2209435 8965603 := bstep (se 1 (by rfl) ⟨6724202, by rfl⟩ : syracuseStep 8965603 = 13448405) B13448405
theorem B11954137 : Blo 2209435 11954137 := bstep (se 2 (by rfl) ⟨4482801, by rfl⟩ : syracuseStep 11954137 = 8965603) B8965603
theorem B15938849 : Blo 2209435 15938849 := bstep (se 2 (by rfl) ⟨5977068, by rfl⟩ : syracuseStep 15938849 = 11954137) B11954137
theorem B10625899 : Blo 2209435 10625899 := bstep (se 1 (by rfl) ⟨7969424, by rfl⟩ : syracuseStep 10625899 = 15938849) B15938849
theorem B14167865 : Blo 2209435 14167865 := bstep (se 2 (by rfl) ⟨5312949, by rfl⟩ : syracuseStep 14167865 = 10625899) B10625899
theorem B9445243 : Blo 2209435 9445243 := bstep (se 1 (by rfl) ⟨7083932, by rfl⟩ : syracuseStep 9445243 = 14167865) B14167865
theorem B12593657 : Blo 2209435 12593657 := bstep (se 2 (by rfl) ⟨4722621, by rfl⟩ : syracuseStep 12593657 = 9445243) B9445243
theorem B8395771 : Blo 2209435 8395771 := bstep (se 1 (by rfl) ⟨6296828, by rfl⟩ : syracuseStep 8395771 = 12593657) B12593657
theorem B11194361 : Blo 2209435 11194361 := bstep (se 2 (by rfl) ⟨4197885, by rfl⟩ : syracuseStep 11194361 = 8395771) B8395771
theorem B7462907 : Blo 2209435 7462907 := bstep (se 1 (by rfl) ⟨5597180, by rfl⟩ : syracuseStep 7462907 = 11194361) B11194361
theorem B4975271 : Blo 2209435 4975271 := bstep (se 1 (by rfl) ⟨3731453, by rfl⟩ : syracuseStep 4975271 = 7462907) B7462907
theorem B3316847 : Blo 2209435 3316847 := bstep (se 1 (by rfl) ⟨2487635, by rfl⟩ : syracuseStep 3316847 = 4975271) B4975271
theorem B2211231 : Blo 2209435 2211231 := bstep (se 1 (by rfl) ⟨1658423, by rfl⟩ : syracuseStep 2211231 = 3316847) B3316847
theorem B3316853 : Blo 2209435 3316853 := bbase (se 5 (by rfl) ⟨155477, by rfl⟩ : syracuseStep 3316853 = 310955) (by norm_num)
theorem B2211235 : Blo 2209435 2211235 := bstep (se 1 (by rfl) ⟨1658426, by rfl⟩ : syracuseStep 2211235 = 3316853) B3316853
theorem B4197901 : Blo 2209435 4197901 := bbase (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) (by norm_num)
theorem B5597201 : Blo 2209435 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B3731467 : Blo 2209435 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B4975289 : Blo 2209435 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B3316859 : Blo 2209435 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B2211239 : Blo 2209435 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B2487649 : Blo 2209435 2487649 := bbase (se 2 (by rfl) ⟨932868, by rfl⟩ : syracuseStep 2487649 = 1865737) (by norm_num)
theorem B3316865 : Blo 2209435 3316865 := bstep (se 2 (by rfl) ⟨1243824, by rfl⟩ : syracuseStep 3316865 = 2487649) B2487649
theorem B2211243 : Blo 2209435 2211243 := bstep (se 1 (by rfl) ⟨1658432, by rfl⟩ : syracuseStep 2211243 = 3316865) B3316865
theorem B5597221 : Blo 2209435 5597221 := bbase (se 4 (by rfl) ⟨524739, by rfl⟩ : syracuseStep 5597221 = 1049479) (by norm_num)
theorem B7462961 : Blo 2209435 7462961 := bstep (se 2 (by rfl) ⟨2798610, by rfl⟩ : syracuseStep 7462961 = 5597221) B5597221
theorem B4975307 : Blo 2209435 4975307 := bstep (se 1 (by rfl) ⟨3731480, by rfl⟩ : syracuseStep 4975307 = 7462961) B7462961
theorem B3316871 : Blo 2209435 3316871 := bstep (se 1 (by rfl) ⟨2487653, by rfl⟩ : syracuseStep 3316871 = 4975307) B4975307
theorem B2211247 : Blo 2209435 2211247 := bstep (se 1 (by rfl) ⟨1658435, by rfl⟩ : syracuseStep 2211247 = 3316871) B3316871
theorem B3316877 : Blo 2209435 3316877 := bbase (se 3 (by rfl) ⟨621914, by rfl⟩ : syracuseStep 3316877 = 1243829) (by norm_num)
theorem B2211251 : Blo 2209435 2211251 := bstep (se 1 (by rfl) ⟨1658438, by rfl⟩ : syracuseStep 2211251 = 3316877) B3316877
theorem B4975325 : Blo 2209435 4975325 := bbase (se 3 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 4975325 = 1865747) (by norm_num)
theorem B3316883 : Blo 2209435 3316883 := bstep (se 1 (by rfl) ⟨2487662, by rfl⟩ : syracuseStep 3316883 = 4975325) B4975325
theorem B2211255 : Blo 2209435 2211255 := bstep (se 1 (by rfl) ⟨1658441, by rfl⟩ : syracuseStep 2211255 = 3316883) B3316883
theorem B3731501 : Blo 2209435 3731501 := bbase (se 3 (by rfl) ⟨699656, by rfl⟩ : syracuseStep 3731501 = 1399313) (by norm_num)
theorem B2487667 : Blo 2209435 2487667 := bstep (se 1 (by rfl) ⟨1865750, by rfl⟩ : syracuseStep 2487667 = 3731501) B3731501
theorem B3316889 : Blo 2209435 3316889 := bstep (se 2 (by rfl) ⟨1243833, by rfl⟩ : syracuseStep 3316889 = 2487667) B2487667
theorem B2211259 : Blo 2209435 2211259 := bstep (se 1 (by rfl) ⟨1658444, by rfl⟩ : syracuseStep 2211259 = 3316889) B3316889
theorem B2241433 : Blo 2209435 2241433 := bbase (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) (by norm_num)
theorem B11954309 : Blo 2209435 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B31878157 : Blo 2209435 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B42504209 : Blo 2209435 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B28336139 : Blo 2209435 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B18890759 : Blo 2209435 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B12593839 : Blo 2209435 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B16791785 : Blo 2209435 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B11194523 : Blo 2209435 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B7463015 : Blo 2209435 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B4975343 : Blo 2209435 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B3316895 : Blo 2209435 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B2211263 : Blo 2209435 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B3316901 : Blo 2209435 3316901 := bbase (se 4 (by rfl) ⟨310959, by rfl⟩ : syracuseStep 3316901 = 621919) (by norm_num)
theorem B2211267 : Blo 2209435 2211267 := bstep (se 1 (by rfl) ⟨1658450, by rfl⟩ : syracuseStep 2211267 = 3316901) B3316901
theorem B2798641 : Blo 2209435 2798641 := bbase (se 2 (by rfl) ⟨1049490, by rfl⟩ : syracuseStep 2798641 = 2098981) (by norm_num)
theorem B3731521 : Blo 2209435 3731521 := bstep (se 2 (by rfl) ⟨1399320, by rfl⟩ : syracuseStep 3731521 = 2798641) B2798641
theorem B4975361 : Blo 2209435 4975361 := bstep (se 2 (by rfl) ⟨1865760, by rfl⟩ : syracuseStep 4975361 = 3731521) B3731521
theorem B3316907 : Blo 2209435 3316907 := bstep (se 1 (by rfl) ⟨2487680, by rfl⟩ : syracuseStep 3316907 = 4975361) B4975361
theorem B2211271 : Blo 2209435 2211271 := bstep (se 1 (by rfl) ⟨1658453, by rfl⟩ : syracuseStep 2211271 = 3316907) B3316907
theorem B2487685 : Blo 2209435 2487685 := bbase (se 4 (by rfl) ⟨233220, by rfl⟩ : syracuseStep 2487685 = 466441) (by norm_num)
theorem B3316913 : Blo 2209435 3316913 := bstep (se 2 (by rfl) ⟨1243842, by rfl⟩ : syracuseStep 3316913 = 2487685) B2487685
theorem B2211275 : Blo 2209435 2211275 := bstep (se 1 (by rfl) ⟨1658456, by rfl⟩ : syracuseStep 2211275 = 3316913) B3316913
theorem B4722725 : Blo 2209435 4722725 := bbase (se 4 (by rfl) ⟨442755, by rfl⟩ : syracuseStep 4722725 = 885511) (by norm_num)
theorem B3148483 : Blo 2209435 3148483 := bstep (se 1 (by rfl) ⟨2361362, by rfl⟩ : syracuseStep 3148483 = 4722725) B4722725
theorem B4197977 : Blo 2209435 4197977 := bstep (se 2 (by rfl) ⟨1574241, by rfl⟩ : syracuseStep 4197977 = 3148483) B3148483
theorem B2798651 : Blo 2209435 2798651 := bstep (se 1 (by rfl) ⟨2098988, by rfl⟩ : syracuseStep 2798651 = 4197977) B4197977
theorem B7463069 : Blo 2209435 7463069 := bstep (se 3 (by rfl) ⟨1399325, by rfl⟩ : syracuseStep 7463069 = 2798651) B2798651
theorem B4975379 : Blo 2209435 4975379 := bstep (se 1 (by rfl) ⟨3731534, by rfl⟩ : syracuseStep 4975379 = 7463069) B7463069
theorem B3316919 : Blo 2209435 3316919 := bstep (se 1 (by rfl) ⟨2487689, by rfl⟩ : syracuseStep 3316919 = 4975379) B4975379
theorem B2211279 : Blo 2209435 2211279 := bstep (se 1 (by rfl) ⟨1658459, by rfl⟩ : syracuseStep 2211279 = 3316919) B3316919
theorem B3316925 : Blo 2209435 3316925 := bbase (se 3 (by rfl) ⟨621923, by rfl⟩ : syracuseStep 3316925 = 1243847) (by norm_num)
theorem B2211283 : Blo 2209435 2211283 := bstep (se 1 (by rfl) ⟨1658462, by rfl⟩ : syracuseStep 2211283 = 3316925) B3316925
theorem B4975397 : Blo 2209435 4975397 := bbase (se 4 (by rfl) ⟨466443, by rfl⟩ : syracuseStep 4975397 = 932887) (by norm_num)
theorem B3316931 : Blo 2209435 3316931 := bstep (se 1 (by rfl) ⟨2487698, by rfl⟩ : syracuseStep 3316931 = 4975397) B4975397
theorem B2211287 : Blo 2209435 2211287 := bstep (se 1 (by rfl) ⟨1658465, by rfl⟩ : syracuseStep 2211287 = 3316931) B3316931
theorem B5597333 : Blo 2209435 5597333 := bbase (se 6 (by rfl) ⟨131187, by rfl⟩ : syracuseStep 5597333 = 262375) (by norm_num)
theorem B3731555 : Blo 2209435 3731555 := bstep (se 1 (by rfl) ⟨2798666, by rfl⟩ : syracuseStep 3731555 = 5597333) B5597333
theorem B2487703 : Blo 2209435 2487703 := bstep (se 1 (by rfl) ⟨1865777, by rfl⟩ : syracuseStep 2487703 = 3731555) B3731555
theorem B3316937 : Blo 2209435 3316937 := bstep (se 2 (by rfl) ⟨1243851, by rfl⟩ : syracuseStep 3316937 = 2487703) B2487703
theorem B2211291 : Blo 2209435 2211291 := bstep (se 1 (by rfl) ⟨1658468, by rfl⟩ : syracuseStep 2211291 = 3316937) B3316937
theorem B3542069 : Blo 2209435 3542069 := bbase (se 5 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 3542069 = 332069) (by norm_num)
theorem B9445517 : Blo 2209435 9445517 := bstep (se 3 (by rfl) ⟨1771034, by rfl⟩ : syracuseStep 9445517 = 3542069) B3542069
theorem B6297011 : Blo 2209435 6297011 := bstep (se 1 (by rfl) ⟨4722758, by rfl⟩ : syracuseStep 6297011 = 9445517) B9445517
theorem B4198007 : Blo 2209435 4198007 := bstep (se 1 (by rfl) ⟨3148505, by rfl⟩ : syracuseStep 4198007 = 6297011) B6297011
theorem B11194685 : Blo 2209435 11194685 := bstep (se 3 (by rfl) ⟨2099003, by rfl⟩ : syracuseStep 11194685 = 4198007) B4198007
theorem B7463123 : Blo 2209435 7463123 := bstep (se 1 (by rfl) ⟨5597342, by rfl⟩ : syracuseStep 7463123 = 11194685) B11194685
theorem B4975415 : Blo 2209435 4975415 := bstep (se 1 (by rfl) ⟨3731561, by rfl⟩ : syracuseStep 4975415 = 7463123) B7463123
theorem B3316943 : Blo 2209435 3316943 := bstep (se 1 (by rfl) ⟨2487707, by rfl⟩ : syracuseStep 3316943 = 4975415) B4975415
theorem B2211295 : Blo 2209435 2211295 := bstep (se 1 (by rfl) ⟨1658471, by rfl⟩ : syracuseStep 2211295 = 3316943) B3316943
theorem B3316949 : Blo 2209435 3316949 := bbase (se 7 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 3316949 = 77741) (by norm_num)
theorem B2211299 : Blo 2209435 2211299 := bstep (se 1 (by rfl) ⟨1658474, by rfl⟩ : syracuseStep 2211299 = 3316949) B3316949
theorem B3148517 : Blo 2209435 3148517 := bbase (se 4 (by rfl) ⟨295173, by rfl⟩ : syracuseStep 3148517 = 590347) (by norm_num)
theorem B8396045 : Blo 2209435 8396045 := bstep (se 3 (by rfl) ⟨1574258, by rfl⟩ : syracuseStep 8396045 = 3148517) B3148517
theorem B5597363 : Blo 2209435 5597363 := bstep (se 1 (by rfl) ⟨4198022, by rfl⟩ : syracuseStep 5597363 = 8396045) B8396045
theorem B3731575 : Blo 2209435 3731575 := bstep (se 1 (by rfl) ⟨2798681, by rfl⟩ : syracuseStep 3731575 = 5597363) B5597363
theorem B4975433 : Blo 2209435 4975433 := bstep (se 2 (by rfl) ⟨1865787, by rfl⟩ : syracuseStep 4975433 = 3731575) B3731575
theorem B3316955 : Blo 2209435 3316955 := bstep (se 1 (by rfl) ⟨2487716, by rfl⟩ : syracuseStep 3316955 = 4975433) B4975433
theorem B2211303 : Blo 2209435 2211303 := bstep (se 1 (by rfl) ⟨1658477, by rfl⟩ : syracuseStep 2211303 = 3316955) B3316955
theorem B2487721 : Blo 2209435 2487721 := bbase (se 2 (by rfl) ⟨932895, by rfl⟩ : syracuseStep 2487721 = 1865791) (by norm_num)
theorem B3316961 : Blo 2209435 3316961 := bstep (se 2 (by rfl) ⟨1243860, by rfl⟩ : syracuseStep 3316961 = 2487721) B2487721
theorem B2211307 : Blo 2209435 2211307 := bstep (se 1 (by rfl) ⟨1658480, by rfl⟩ : syracuseStep 2211307 = 3316961) B3316961
theorem B4482965 : Blo 2209435 4482965 := bbase (se 6 (by rfl) ⟨105069, by rfl⟩ : syracuseStep 4482965 = 210139) (by norm_num)
theorem B2988643 : Blo 2209435 2988643 := bstep (se 1 (by rfl) ⟨2241482, by rfl⟩ : syracuseStep 2988643 = 4482965) B4482965
theorem B3984857 : Blo 2209435 3984857 := bstep (se 2 (by rfl) ⟨1494321, by rfl⟩ : syracuseStep 3984857 = 2988643) B2988643
theorem B2656571 : Blo 2209435 2656571 := bstep (se 1 (by rfl) ⟨1992428, by rfl⟩ : syracuseStep 2656571 = 3984857) B3984857
theorem B7084189 : Blo 2209435 7084189 := bstep (se 3 (by rfl) ⟨1328285, by rfl⟩ : syracuseStep 7084189 = 2656571) B2656571
theorem B9445585 : Blo 2209435 9445585 := bstep (se 2 (by rfl) ⟨3542094, by rfl⟩ : syracuseStep 9445585 = 7084189) B7084189
theorem B12594113 : Blo 2209435 12594113 := bstep (se 2 (by rfl) ⟨4722792, by rfl⟩ : syracuseStep 12594113 = 9445585) B9445585
theorem B8396075 : Blo 2209435 8396075 := bstep (se 1 (by rfl) ⟨6297056, by rfl⟩ : syracuseStep 8396075 = 12594113) B12594113
theorem B5597383 : Blo 2209435 5597383 := bstep (se 1 (by rfl) ⟨4198037, by rfl⟩ : syracuseStep 5597383 = 8396075) B8396075
theorem B7463177 : Blo 2209435 7463177 := bstep (se 2 (by rfl) ⟨2798691, by rfl⟩ : syracuseStep 7463177 = 5597383) B5597383
theorem B4975451 : Blo 2209435 4975451 := bstep (se 1 (by rfl) ⟨3731588, by rfl⟩ : syracuseStep 4975451 = 7463177) B7463177
theorem B3316967 : Blo 2209435 3316967 := bstep (se 1 (by rfl) ⟨2487725, by rfl⟩ : syracuseStep 3316967 = 4975451) B4975451
theorem B2211311 : Blo 2209435 2211311 := bstep (se 1 (by rfl) ⟨1658483, by rfl⟩ : syracuseStep 2211311 = 3316967) B3316967
theorem B3316973 : Blo 2209435 3316973 := bbase (se 3 (by rfl) ⟨621932, by rfl⟩ : syracuseStep 3316973 = 1243865) (by norm_num)
theorem B2211315 : Blo 2209435 2211315 := bstep (se 1 (by rfl) ⟨1658486, by rfl⟩ : syracuseStep 2211315 = 3316973) B3316973
theorem B4975469 : Blo 2209435 4975469 := bbase (se 3 (by rfl) ⟨932900, by rfl⟩ : syracuseStep 4975469 = 1865801) (by norm_num)
theorem B3316979 : Blo 2209435 3316979 := bstep (se 1 (by rfl) ⟨2487734, by rfl⟩ : syracuseStep 3316979 = 4975469) B4975469
theorem B2211319 : Blo 2209435 2211319 := bstep (se 1 (by rfl) ⟨1658489, by rfl⟩ : syracuseStep 2211319 = 3316979) B3316979
theorem B4198061 : Blo 2209435 4198061 := bbase (se 3 (by rfl) ⟨787136, by rfl⟩ : syracuseStep 4198061 = 1574273) (by norm_num)
theorem B2798707 : Blo 2209435 2798707 := bstep (se 1 (by rfl) ⟨2099030, by rfl⟩ : syracuseStep 2798707 = 4198061) B4198061
theorem B3731609 : Blo 2209435 3731609 := bstep (se 2 (by rfl) ⟨1399353, by rfl⟩ : syracuseStep 3731609 = 2798707) B2798707
theorem B2487739 : Blo 2209435 2487739 := bstep (se 1 (by rfl) ⟨1865804, by rfl⟩ : syracuseStep 2487739 = 3731609) B3731609
theorem B3316985 : Blo 2209435 3316985 := bstep (se 2 (by rfl) ⟨1243869, by rfl⟩ : syracuseStep 3316985 = 2487739) B2487739
theorem B2211323 : Blo 2209435 2211323 := bstep (se 1 (by rfl) ⟨1658492, by rfl⟩ : syracuseStep 2211323 = 3316985) B3316985
theorem B86170709 : Blo 2209435 86170709 := bbase (se 8 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 86170709 = 1009813) (by norm_num)
theorem B57447139 : Blo 2209435 57447139 := bstep (se 1 (by rfl) ⟨43085354, by rfl⟩ : syracuseStep 57447139 = 86170709) B86170709
theorem B76596185 : Blo 2209435 76596185 := bstep (se 2 (by rfl) ⟨28723569, by rfl⟩ : syracuseStep 76596185 = 57447139) B57447139
theorem B51064123 : Blo 2209435 51064123 := bstep (se 1 (by rfl) ⟨38298092, by rfl⟩ : syracuseStep 51064123 = 76596185) B76596185
theorem B68085497 : Blo 2209435 68085497 := bstep (se 2 (by rfl) ⟨25532061, by rfl⟩ : syracuseStep 68085497 = 51064123) B51064123
theorem B45390331 : Blo 2209435 45390331 := bstep (se 1 (by rfl) ⟨34042748, by rfl⟩ : syracuseStep 45390331 = 68085497) B68085497
theorem B60520441 : Blo 2209435 60520441 := bstep (se 2 (by rfl) ⟨22695165, by rfl⟩ : syracuseStep 60520441 = 45390331) B45390331
theorem B80693921 : Blo 2209435 80693921 := bstep (se 2 (by rfl) ⟨30260220, by rfl⟩ : syracuseStep 80693921 = 60520441) B60520441
theorem B53795947 : Blo 2209435 53795947 := bstep (se 1 (by rfl) ⟨40346960, by rfl⟩ : syracuseStep 53795947 = 80693921) B80693921
theorem B71727929 : Blo 2209435 71727929 := bstep (se 2 (by rfl) ⟨26897973, by rfl⟩ : syracuseStep 71727929 = 53795947) B53795947
theorem B47818619 : Blo 2209435 47818619 := bstep (se 1 (by rfl) ⟨35863964, by rfl⟩ : syracuseStep 47818619 = 71727929) B71727929
theorem B31879079 : Blo 2209435 31879079 := bstep (se 1 (by rfl) ⟨23909309, by rfl⟩ : syracuseStep 31879079 = 47818619) B47818619
theorem B21252719 : Blo 2209435 21252719 := bstep (se 1 (by rfl) ⟨15939539, by rfl⟩ : syracuseStep 21252719 = 31879079) B31879079
theorem B56673917 : Blo 2209435 56673917 := bstep (se 3 (by rfl) ⟨10626359, by rfl⟩ : syracuseStep 56673917 = 21252719) B21252719
theorem B37782611 : Blo 2209435 37782611 := bstep (se 1 (by rfl) ⟨28336958, by rfl⟩ : syracuseStep 37782611 = 56673917) B56673917
theorem B25188407 : Blo 2209435 25188407 := bstep (se 1 (by rfl) ⟨18891305, by rfl⟩ : syracuseStep 25188407 = 37782611) B37782611
theorem B16792271 : Blo 2209435 16792271 := bstep (se 1 (by rfl) ⟨12594203, by rfl⟩ : syracuseStep 16792271 = 25188407) B25188407
theorem B11194847 : Blo 2209435 11194847 := bstep (se 1 (by rfl) ⟨8396135, by rfl⟩ : syracuseStep 11194847 = 16792271) B16792271
theorem B7463231 : Blo 2209435 7463231 := bstep (se 1 (by rfl) ⟨5597423, by rfl⟩ : syracuseStep 7463231 = 11194847) B11194847
theorem B4975487 : Blo 2209435 4975487 := bstep (se 1 (by rfl) ⟨3731615, by rfl⟩ : syracuseStep 4975487 = 7463231) B7463231
theorem B3316991 : Blo 2209435 3316991 := bstep (se 1 (by rfl) ⟨2487743, by rfl⟩ : syracuseStep 3316991 = 4975487) B4975487
theorem B2211327 : Blo 2209435 2211327 := bstep (se 1 (by rfl) ⟨1658495, by rfl⟩ : syracuseStep 2211327 = 3316991) B3316991
theorem B3316997 : Blo 2209435 3316997 := bbase (se 4 (by rfl) ⟨310968, by rfl⟩ : syracuseStep 3316997 = 621937) (by norm_num)
theorem B2211331 : Blo 2209435 2211331 := bstep (se 1 (by rfl) ⟨1658498, by rfl⟩ : syracuseStep 2211331 = 3316997) B3316997
theorem B3731629 : Blo 2209435 3731629 := bbase (se 3 (by rfl) ⟨699680, by rfl⟩ : syracuseStep 3731629 = 1399361) (by norm_num)
theorem B4975505 : Blo 2209435 4975505 := bstep (se 2 (by rfl) ⟨1865814, by rfl⟩ : syracuseStep 4975505 = 3731629) B3731629
theorem B3317003 : Blo 2209435 3317003 := bstep (se 1 (by rfl) ⟨2487752, by rfl⟩ : syracuseStep 3317003 = 4975505) B4975505
theorem B2211335 : Blo 2209435 2211335 := bstep (se 1 (by rfl) ⟨1658501, by rfl⟩ : syracuseStep 2211335 = 3317003) B3317003
theorem B2487757 : Blo 2209435 2487757 := bbase (se 3 (by rfl) ⟨466454, by rfl⟩ : syracuseStep 2487757 = 932909) (by norm_num)
theorem B3317009 : Blo 2209435 3317009 := bstep (se 2 (by rfl) ⟨1243878, by rfl⟩ : syracuseStep 3317009 = 2487757) B2487757
theorem B2211339 : Blo 2209435 2211339 := bstep (se 1 (by rfl) ⟨1658504, by rfl⟩ : syracuseStep 2211339 = 3317009) B3317009
theorem B7463285 : Blo 2209435 7463285 := bbase (se 5 (by rfl) ⟨349841, by rfl⟩ : syracuseStep 7463285 = 699683) (by norm_num)
theorem B4975523 : Blo 2209435 4975523 := bstep (se 1 (by rfl) ⟨3731642, by rfl⟩ : syracuseStep 4975523 = 7463285) B7463285
theorem B3317015 : Blo 2209435 3317015 := bstep (se 1 (by rfl) ⟨2487761, by rfl⟩ : syracuseStep 3317015 = 4975523) B4975523
theorem B2211343 : Blo 2209435 2211343 := bstep (se 1 (by rfl) ⟨1658507, by rfl⟩ : syracuseStep 2211343 = 3317015) B3317015
theorem B3317021 : Blo 2209435 3317021 := bbase (se 3 (by rfl) ⟨621941, by rfl⟩ : syracuseStep 3317021 = 1243883) (by norm_num)
theorem B2211347 : Blo 2209435 2211347 := bstep (se 1 (by rfl) ⟨1658510, by rfl⟩ : syracuseStep 2211347 = 3317021) B3317021
theorem B4975541 : Blo 2209435 4975541 := bbase (se 5 (by rfl) ⟨233228, by rfl⟩ : syracuseStep 4975541 = 466457) (by norm_num)
theorem B3317027 : Blo 2209435 3317027 := bstep (se 1 (by rfl) ⟨2487770, by rfl⟩ : syracuseStep 3317027 = 4975541) B4975541
theorem B2211351 : Blo 2209435 2211351 := bstep (se 1 (by rfl) ⟨1658513, by rfl⟩ : syracuseStep 2211351 = 3317027) B3317027
theorem B5043437 : Blo 2209435 5043437 := bbase (se 3 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 5043437 = 1891289) (by norm_num)
theorem B3362291 : Blo 2209435 3362291 := bstep (se 1 (by rfl) ⟨2521718, by rfl⟩ : syracuseStep 3362291 = 5043437) B5043437
theorem B2241527 : Blo 2209435 2241527 := bstep (se 1 (by rfl) ⟨1681145, by rfl⟩ : syracuseStep 2241527 = 3362291) B3362291
theorem B5977405 : Blo 2209435 5977405 := bstep (se 3 (by rfl) ⟨1120763, by rfl⟩ : syracuseStep 5977405 = 2241527) B2241527
theorem B7969873 : Blo 2209435 7969873 := bstep (se 2 (by rfl) ⟨2988702, by rfl⟩ : syracuseStep 7969873 = 5977405) B5977405
theorem B10626497 : Blo 2209435 10626497 := bstep (se 2 (by rfl) ⟨3984936, by rfl⟩ : syracuseStep 10626497 = 7969873) B7969873
theorem B7084331 : Blo 2209435 7084331 := bstep (se 1 (by rfl) ⟨5313248, by rfl⟩ : syracuseStep 7084331 = 10626497) B10626497
theorem B4722887 : Blo 2209435 4722887 := bstep (se 1 (by rfl) ⟨3542165, by rfl⟩ : syracuseStep 4722887 = 7084331) B7084331
theorem B12594365 : Blo 2209435 12594365 := bstep (se 3 (by rfl) ⟨2361443, by rfl⟩ : syracuseStep 12594365 = 4722887) B4722887
theorem B8396243 : Blo 2209435 8396243 := bstep (se 1 (by rfl) ⟨6297182, by rfl⟩ : syracuseStep 8396243 = 12594365) B12594365
theorem B5597495 : Blo 2209435 5597495 := bstep (se 1 (by rfl) ⟨4198121, by rfl⟩ : syracuseStep 5597495 = 8396243) B8396243
theorem B3731663 : Blo 2209435 3731663 := bstep (se 1 (by rfl) ⟨2798747, by rfl⟩ : syracuseStep 3731663 = 5597495) B5597495
theorem B2487775 : Blo 2209435 2487775 := bstep (se 1 (by rfl) ⟨1865831, by rfl⟩ : syracuseStep 2487775 = 3731663) B3731663
theorem B3317033 : Blo 2209435 3317033 := bstep (se 2 (by rfl) ⟨1243887, by rfl⟩ : syracuseStep 3317033 = 2487775) B2487775
theorem B2211355 : Blo 2209435 2211355 := bstep (se 1 (by rfl) ⟨1658516, by rfl⟩ : syracuseStep 2211355 = 3317033) B3317033
theorem B9088453 : Blo 2209435 9088453 := bbase (se 4 (by rfl) ⟨852042, by rfl⟩ : syracuseStep 9088453 = 1704085) (by norm_num)
theorem B12117937 : Blo 2209435 12117937 := bstep (se 2 (by rfl) ⟨4544226, by rfl⟩ : syracuseStep 12117937 = 9088453) B9088453
theorem B16157249 : Blo 2209435 16157249 := bstep (se 2 (by rfl) ⟨6058968, by rfl⟩ : syracuseStep 16157249 = 12117937) B12117937
theorem B10771499 : Blo 2209435 10771499 := bstep (se 1 (by rfl) ⟨8078624, by rfl⟩ : syracuseStep 10771499 = 16157249) B16157249
theorem B28723997 : Blo 2209435 28723997 := bstep (se 3 (by rfl) ⟨5385749, by rfl⟩ : syracuseStep 28723997 = 10771499) B10771499
theorem B19149331 : Blo 2209435 19149331 := bstep (se 1 (by rfl) ⟨14361998, by rfl⟩ : syracuseStep 19149331 = 28723997) B28723997
theorem B25532441 : Blo 2209435 25532441 := bstep (se 2 (by rfl) ⟨9574665, by rfl⟩ : syracuseStep 25532441 = 19149331) B19149331
theorem B17021627 : Blo 2209435 17021627 := bstep (se 1 (by rfl) ⟨12766220, by rfl⟩ : syracuseStep 17021627 = 25532441) B25532441
theorem B11347751 : Blo 2209435 11347751 := bstep (se 1 (by rfl) ⟨8510813, by rfl⟩ : syracuseStep 11347751 = 17021627) B17021627
theorem B7565167 : Blo 2209435 7565167 := bstep (se 1 (by rfl) ⟨5673875, by rfl⟩ : syracuseStep 7565167 = 11347751) B11347751
theorem B10086889 : Blo 2209435 10086889 := bstep (se 2 (by rfl) ⟨3782583, by rfl⟩ : syracuseStep 10086889 = 7565167) B7565167
theorem B13449185 : Blo 2209435 13449185 := bstep (se 2 (by rfl) ⟨5043444, by rfl⟩ : syracuseStep 13449185 = 10086889) B10086889
theorem B8966123 : Blo 2209435 8966123 := bstep (se 1 (by rfl) ⟨6724592, by rfl⟩ : syracuseStep 8966123 = 13449185) B13449185
theorem B5977415 : Blo 2209435 5977415 := bstep (se 1 (by rfl) ⟨4483061, by rfl⟩ : syracuseStep 5977415 = 8966123) B8966123
theorem B15939773 : Blo 2209435 15939773 := bstep (se 3 (by rfl) ⟨2988707, by rfl⟩ : syracuseStep 15939773 = 5977415) B5977415
theorem B10626515 : Blo 2209435 10626515 := bstep (se 1 (by rfl) ⟨7969886, by rfl⟩ : syracuseStep 10626515 = 15939773) B15939773
theorem B7084343 : Blo 2209435 7084343 := bstep (se 1 (by rfl) ⟨5313257, by rfl⟩ : syracuseStep 7084343 = 10626515) B10626515
theorem B4722895 : Blo 2209435 4722895 := bstep (se 1 (by rfl) ⟨3542171, by rfl⟩ : syracuseStep 4722895 = 7084343) B7084343
theorem B6297193 : Blo 2209435 6297193 := bstep (se 2 (by rfl) ⟨2361447, by rfl⟩ : syracuseStep 6297193 = 4722895) B4722895
theorem B8396257 : Blo 2209435 8396257 := bstep (se 2 (by rfl) ⟨3148596, by rfl⟩ : syracuseStep 8396257 = 6297193) B6297193
theorem B11195009 : Blo 2209435 11195009 := bstep (se 2 (by rfl) ⟨4198128, by rfl⟩ : syracuseStep 11195009 = 8396257) B8396257
theorem B7463339 : Blo 2209435 7463339 := bstep (se 1 (by rfl) ⟨5597504, by rfl⟩ : syracuseStep 7463339 = 11195009) B11195009
theorem B4975559 : Blo 2209435 4975559 := bstep (se 1 (by rfl) ⟨3731669, by rfl⟩ : syracuseStep 4975559 = 7463339) B7463339
theorem B3317039 : Blo 2209435 3317039 := bstep (se 1 (by rfl) ⟨2487779, by rfl⟩ : syracuseStep 3317039 = 4975559) B4975559
theorem B2211359 : Blo 2209435 2211359 := bstep (se 1 (by rfl) ⟨1658519, by rfl⟩ : syracuseStep 2211359 = 3317039) B3317039
theorem B3317045 : Blo 2209435 3317045 := bbase (se 5 (by rfl) ⟨155486, by rfl⟩ : syracuseStep 3317045 = 310973) (by norm_num)
theorem B2211363 : Blo 2209435 2211363 := bstep (se 1 (by rfl) ⟨1658522, by rfl⟩ : syracuseStep 2211363 = 3317045) B3317045
theorem B5597525 : Blo 2209435 5597525 := bbase (se 10 (by rfl) ⟨8199, by rfl⟩ : syracuseStep 5597525 = 16399) (by norm_num)
theorem B3731683 : Blo 2209435 3731683 := bstep (se 1 (by rfl) ⟨2798762, by rfl⟩ : syracuseStep 3731683 = 5597525) B5597525
theorem B4975577 : Blo 2209435 4975577 := bstep (se 2 (by rfl) ⟨1865841, by rfl⟩ : syracuseStep 4975577 = 3731683) B3731683
theorem B3317051 : Blo 2209435 3317051 := bstep (se 1 (by rfl) ⟨2487788, by rfl⟩ : syracuseStep 3317051 = 4975577) B4975577
theorem B2211367 : Blo 2209435 2211367 := bstep (se 1 (by rfl) ⟨1658525, by rfl⟩ : syracuseStep 2211367 = 3317051) B3317051
theorem B2487793 : Blo 2209435 2487793 := bbase (se 2 (by rfl) ⟨932922, by rfl⟩ : syracuseStep 2487793 = 1865845) (by norm_num)
theorem B3317057 : Blo 2209435 3317057 := bstep (se 2 (by rfl) ⟨1243896, by rfl⟩ : syracuseStep 3317057 = 2487793) B2487793
theorem B2211371 : Blo 2209435 2211371 := bstep (se 1 (by rfl) ⟨1658528, by rfl⟩ : syracuseStep 2211371 = 3317057) B3317057
theorem B14168789 : Blo 2209435 14168789 := bbase (se 7 (by rfl) ⟨166040, by rfl⟩ : syracuseStep 14168789 = 332081) (by norm_num)
theorem B9445859 : Blo 2209435 9445859 := bstep (se 1 (by rfl) ⟨7084394, by rfl⟩ : syracuseStep 9445859 = 14168789) B14168789
theorem B6297239 : Blo 2209435 6297239 := bstep (se 1 (by rfl) ⟨4722929, by rfl⟩ : syracuseStep 6297239 = 9445859) B9445859
theorem B4198159 : Blo 2209435 4198159 := bstep (se 1 (by rfl) ⟨3148619, by rfl⟩ : syracuseStep 4198159 = 6297239) B6297239
theorem B5597545 : Blo 2209435 5597545 := bstep (se 2 (by rfl) ⟨2099079, by rfl⟩ : syracuseStep 5597545 = 4198159) B4198159
theorem B7463393 : Blo 2209435 7463393 := bstep (se 2 (by rfl) ⟨2798772, by rfl⟩ : syracuseStep 7463393 = 5597545) B5597545
theorem B4975595 : Blo 2209435 4975595 := bstep (se 1 (by rfl) ⟨3731696, by rfl⟩ : syracuseStep 4975595 = 7463393) B7463393
theorem B3317063 : Blo 2209435 3317063 := bstep (se 1 (by rfl) ⟨2487797, by rfl⟩ : syracuseStep 3317063 = 4975595) B4975595
theorem B2211375 : Blo 2209435 2211375 := bstep (se 1 (by rfl) ⟨1658531, by rfl⟩ : syracuseStep 2211375 = 3317063) B3317063
theorem B3317069 : Blo 2209435 3317069 := bbase (se 3 (by rfl) ⟨621950, by rfl⟩ : syracuseStep 3317069 = 1243901) (by norm_num)
theorem B2211379 : Blo 2209435 2211379 := bstep (se 1 (by rfl) ⟨1658534, by rfl⟩ : syracuseStep 2211379 = 3317069) B3317069
theorem B4975613 : Blo 2209435 4975613 := bbase (se 3 (by rfl) ⟨932927, by rfl⟩ : syracuseStep 4975613 = 1865855) (by norm_num)
theorem B3317075 : Blo 2209435 3317075 := bstep (se 1 (by rfl) ⟨2487806, by rfl⟩ : syracuseStep 3317075 = 4975613) B4975613
theorem B2211383 : Blo 2209435 2211383 := bstep (se 1 (by rfl) ⟨1658537, by rfl⟩ : syracuseStep 2211383 = 3317075) B3317075
theorem B3731717 : Blo 2209435 3731717 := bbase (se 4 (by rfl) ⟨349848, by rfl⟩ : syracuseStep 3731717 = 699697) (by norm_num)
theorem B2487811 : Blo 2209435 2487811 := bstep (se 1 (by rfl) ⟨1865858, by rfl⟩ : syracuseStep 2487811 = 3731717) B3731717
theorem B3317081 : Blo 2209435 3317081 := bstep (se 2 (by rfl) ⟨1243905, by rfl⟩ : syracuseStep 3317081 = 2487811) B2487811
theorem B2211387 : Blo 2209435 2211387 := bstep (se 1 (by rfl) ⟨1658540, by rfl⟩ : syracuseStep 2211387 = 3317081) B3317081
theorem B16792757 : Blo 2209435 16792757 := bbase (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) (by norm_num)
theorem B11195171 : Blo 2209435 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B7463447 : Blo 2209435 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B4975631 : Blo 2209435 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B3317087 : Blo 2209435 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B2211391 : Blo 2209435 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B3317093 : Blo 2209435 3317093 := bbase (se 4 (by rfl) ⟨310977, by rfl⟩ : syracuseStep 3317093 = 621955) (by norm_num)
theorem B2211395 : Blo 2209435 2211395 := bstep (se 1 (by rfl) ⟨1658546, by rfl⟩ : syracuseStep 2211395 = 3317093) B3317093
theorem B4198205 : Blo 2209435 4198205 := bbase (se 3 (by rfl) ⟨787163, by rfl⟩ : syracuseStep 4198205 = 1574327) (by norm_num)
theorem B2798803 : Blo 2209435 2798803 := bstep (se 1 (by rfl) ⟨2099102, by rfl⟩ : syracuseStep 2798803 = 4198205) B4198205
theorem B3731737 : Blo 2209435 3731737 := bstep (se 2 (by rfl) ⟨1399401, by rfl⟩ : syracuseStep 3731737 = 2798803) B2798803
theorem B4975649 : Blo 2209435 4975649 := bstep (se 2 (by rfl) ⟨1865868, by rfl⟩ : syracuseStep 4975649 = 3731737) B3731737
theorem B3317099 : Blo 2209435 3317099 := bstep (se 1 (by rfl) ⟨2487824, by rfl⟩ : syracuseStep 3317099 = 4975649) B4975649
theorem B2211399 : Blo 2209435 2211399 := bstep (se 1 (by rfl) ⟨1658549, by rfl⟩ : syracuseStep 2211399 = 3317099) B3317099
theorem B2487829 : Blo 2209435 2487829 := bbase (se 6 (by rfl) ⟨58308, by rfl⟩ : syracuseStep 2487829 = 116617) (by norm_num)
theorem B3317105 : Blo 2209435 3317105 := bstep (se 2 (by rfl) ⟨1243914, by rfl⟩ : syracuseStep 3317105 = 2487829) B2487829
theorem B2211403 : Blo 2209435 2211403 := bstep (se 1 (by rfl) ⟨1658552, by rfl⟩ : syracuseStep 2211403 = 3317105) B3317105
theorem B2798813 : Blo 2209435 2798813 := bbase (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) (by norm_num)
theorem B7463501 : Blo 2209435 7463501 := bstep (se 3 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 7463501 = 2798813) B2798813
theorem B4975667 : Blo 2209435 4975667 := bstep (se 1 (by rfl) ⟨3731750, by rfl⟩ : syracuseStep 4975667 = 7463501) B7463501
theorem B3317111 : Blo 2209435 3317111 := bstep (se 1 (by rfl) ⟨2487833, by rfl⟩ : syracuseStep 3317111 = 4975667) B4975667
theorem B2211407 : Blo 2209435 2211407 := bstep (se 1 (by rfl) ⟨1658555, by rfl⟩ : syracuseStep 2211407 = 3317111) B3317111
theorem B3317117 : Blo 2209435 3317117 := bbase (se 3 (by rfl) ⟨621959, by rfl⟩ : syracuseStep 3317117 = 1243919) (by norm_num)
theorem B2211411 : Blo 2209435 2211411 := bstep (se 1 (by rfl) ⟨1658558, by rfl⟩ : syracuseStep 2211411 = 3317117) B3317117
theorem B4975685 : Blo 2209435 4975685 := bbase (se 4 (by rfl) ⟨466470, by rfl⟩ : syracuseStep 4975685 = 932941) (by norm_num)
theorem B3317123 : Blo 2209435 3317123 := bstep (se 1 (by rfl) ⟨2487842, by rfl⟩ : syracuseStep 3317123 = 4975685) B4975685
theorem B2211415 : Blo 2209435 2211415 := bstep (se 1 (by rfl) ⟨1658561, by rfl⟩ : syracuseStep 2211415 = 3317123) B3317123
theorem B6297365 : Blo 2209435 6297365 := bbase (se 6 (by rfl) ⟨147594, by rfl⟩ : syracuseStep 6297365 = 295189) (by norm_num)
theorem B4198243 : Blo 2209435 4198243 := bstep (se 1 (by rfl) ⟨3148682, by rfl⟩ : syracuseStep 4198243 = 6297365) B6297365
theorem B5597657 : Blo 2209435 5597657 := bstep (se 2 (by rfl) ⟨2099121, by rfl⟩ : syracuseStep 5597657 = 4198243) B4198243
theorem B3731771 : Blo 2209435 3731771 := bstep (se 1 (by rfl) ⟨2798828, by rfl⟩ : syracuseStep 3731771 = 5597657) B5597657
theorem B2487847 : Blo 2209435 2487847 := bstep (se 1 (by rfl) ⟨1865885, by rfl⟩ : syracuseStep 2487847 = 3731771) B3731771
theorem B3317129 : Blo 2209435 3317129 := bstep (se 2 (by rfl) ⟨1243923, by rfl⟩ : syracuseStep 3317129 = 2487847) B2487847
theorem B2211419 : Blo 2209435 2211419 := bstep (se 1 (by rfl) ⟨1658564, by rfl⟩ : syracuseStep 2211419 = 3317129) B3317129
theorem B11195333 : Blo 2209435 11195333 := bbase (se 4 (by rfl) ⟨1049562, by rfl⟩ : syracuseStep 11195333 = 2099125) (by norm_num)
theorem B7463555 : Blo 2209435 7463555 := bstep (se 1 (by rfl) ⟨5597666, by rfl⟩ : syracuseStep 7463555 = 11195333) B11195333
theorem B4975703 : Blo 2209435 4975703 := bstep (se 1 (by rfl) ⟨3731777, by rfl⟩ : syracuseStep 4975703 = 7463555) B7463555
theorem B3317135 : Blo 2209435 3317135 := bstep (se 1 (by rfl) ⟨2487851, by rfl⟩ : syracuseStep 3317135 = 4975703) B4975703
theorem B2211423 : Blo 2209435 2211423 := bstep (se 1 (by rfl) ⟨1658567, by rfl⟩ : syracuseStep 2211423 = 3317135) B3317135
theorem B3317141 : Blo 2209435 3317141 := bbase (se 6 (by rfl) ⟨77745, by rfl⟩ : syracuseStep 3317141 = 155491) (by norm_num)
theorem B2211427 : Blo 2209435 2211427 := bstep (se 1 (by rfl) ⟨1658570, by rfl⟩ : syracuseStep 2211427 = 3317141) B3317141
theorem B11955221 : Blo 2209435 11955221 := bbase (se 6 (by rfl) ⟨280200, by rfl⟩ : syracuseStep 11955221 = 560401) (by norm_num)
theorem B7970147 : Blo 2209435 7970147 := bstep (se 1 (by rfl) ⟨5977610, by rfl⟩ : syracuseStep 7970147 = 11955221) B11955221
theorem B5313431 : Blo 2209435 5313431 := bstep (se 1 (by rfl) ⟨3985073, by rfl⟩ : syracuseStep 5313431 = 7970147) B7970147
theorem B3542287 : Blo 2209435 3542287 := bstep (se 1 (by rfl) ⟨2656715, by rfl⟩ : syracuseStep 3542287 = 5313431) B5313431
theorem B4723049 : Blo 2209435 4723049 := bstep (se 2 (by rfl) ⟨1771143, by rfl⟩ : syracuseStep 4723049 = 3542287) B3542287
theorem B12594797 : Blo 2209435 12594797 := bstep (se 3 (by rfl) ⟨2361524, by rfl⟩ : syracuseStep 12594797 = 4723049) B4723049
theorem B8396531 : Blo 2209435 8396531 := bstep (se 1 (by rfl) ⟨6297398, by rfl⟩ : syracuseStep 8396531 = 12594797) B12594797
theorem B5597687 : Blo 2209435 5597687 := bstep (se 1 (by rfl) ⟨4198265, by rfl⟩ : syracuseStep 5597687 = 8396531) B8396531
theorem B3731791 : Blo 2209435 3731791 := bstep (se 1 (by rfl) ⟨2798843, by rfl⟩ : syracuseStep 3731791 = 5597687) B5597687
theorem B4975721 : Blo 2209435 4975721 := bstep (se 2 (by rfl) ⟨1865895, by rfl⟩ : syracuseStep 4975721 = 3731791) B3731791
theorem B3317147 : Blo 2209435 3317147 := bstep (se 1 (by rfl) ⟨2487860, by rfl⟩ : syracuseStep 3317147 = 4975721) B4975721
theorem B2211431 : Blo 2209435 2211431 := bstep (se 1 (by rfl) ⟨1658573, by rfl⟩ : syracuseStep 2211431 = 3317147) B3317147
theorem B2487865 : Blo 2209435 2487865 := bbase (se 2 (by rfl) ⟨932949, by rfl⟩ : syracuseStep 2487865 = 1865899) (by norm_num)
theorem B3317153 : Blo 2209435 3317153 := bstep (se 2 (by rfl) ⟨1243932, by rfl⟩ : syracuseStep 3317153 = 2487865) B2487865
theorem B2211435 : Blo 2209435 2211435 := bstep (se 1 (by rfl) ⟨1658576, by rfl⟩ : syracuseStep 2211435 = 3317153) B3317153
theorem C0 (j : ℕ) (h1 : 552358 ≤ j) (h2 : j ≤ 552858) : Blo 2209435 (4 * j + 3) := by
  interval_cases j
  · exact B2209435
  · exact B2209439
  · exact B2209443
  · exact B2209447
  · exact B2209451
  · exact B2209455
  · exact B2209459
  · exact B2209463
  · exact B2209467
  · exact B2209471
  · exact B2209475
  · exact B2209479
  · exact B2209483
  · exact B2209487
  · exact B2209491
  · exact B2209495
  · exact B2209499
  · exact B2209503
  · exact B2209507
  · exact B2209511
  · exact B2209515
  · exact B2209519
  · exact B2209523
  · exact B2209527
  · exact B2209531
  · exact B2209535
  · exact B2209539
  · exact B2209543
  · exact B2209547
  · exact B2209551
  · exact B2209555
  · exact B2209559
  · exact B2209563
  · exact B2209567
  · exact B2209571
  · exact B2209575
  · exact B2209579
  · exact B2209583
  · exact B2209587
  · exact B2209591
  · exact B2209595
  · exact B2209599
  · exact B2209603
  · exact B2209607
  · exact B2209611
  · exact B2209615
  · exact B2209619
  · exact B2209623
  · exact B2209627
  · exact B2209631
  · exact B2209635
  · exact B2209639
  · exact B2209643
  · exact B2209647
  · exact B2209651
  · exact B2209655
  · exact B2209659
  · exact B2209663
  · exact B2209667
  · exact B2209671
  · exact B2209675
  · exact B2209679
  · exact B2209683
  · exact B2209687
  · exact B2209691
  · exact B2209695
  · exact B2209699
  · exact B2209703
  · exact B2209707
  · exact B2209711
  · exact B2209715
  · exact B2209719
  · exact B2209723
  · exact B2209727
  · exact B2209731
  · exact B2209735
  · exact B2209739
  · exact B2209743
  · exact B2209747
  · exact B2209751
  · exact B2209755
  · exact B2209759
  · exact B2209763
  · exact B2209767
  · exact B2209771
  · exact B2209775
  · exact B2209779
  · exact B2209783
  · exact B2209787
  · exact B2209791
  · exact B2209795
  · exact B2209799
  · exact B2209803
  · exact B2209807
  · exact B2209811
  · exact B2209815
  · exact B2209819
  · exact B2209823
  · exact B2209827
  · exact B2209831
  · exact B2209835
  · exact B2209839
  · exact B2209843
  · exact B2209847
  · exact B2209851
  · exact B2209855
  · exact B2209859
  · exact B2209863
  · exact B2209867
  · exact B2209871
  · exact B2209875
  · exact B2209879
  · exact B2209883
  · exact B2209887
  · exact B2209891
  · exact B2209895
  · exact B2209899
  · exact B2209903
  · exact B2209907
  · exact B2209911
  · exact B2209915
  · exact B2209919
  · exact B2209923
  · exact B2209927
  · exact B2209931
  · exact B2209935
  · exact B2209939
  · exact B2209943
  · exact B2209947
  · exact B2209951
  · exact B2209955
  · exact B2209959
  · exact B2209963
  · exact B2209967
  · exact B2209971
  · exact B2209975
  · exact B2209979
  · exact B2209983
  · exact B2209987
  · exact B2209991
  · exact B2209995
  · exact B2209999
  · exact B2210003
  · exact B2210007
  · exact B2210011
  · exact B2210015
  · exact B2210019
  · exact B2210023
  · exact B2210027
  · exact B2210031
  · exact B2210035
  · exact B2210039
  · exact B2210043
  · exact B2210047
  · exact B2210051
  · exact B2210055
  · exact B2210059
  · exact B2210063
  · exact B2210067
  · exact B2210071
  · exact B2210075
  · exact B2210079
  · exact B2210083
  · exact B2210087
  · exact B2210091
  · exact B2210095
  · exact B2210099
  · exact B2210103
  · exact B2210107
  · exact B2210111
  · exact B2210115
  · exact B2210119
  · exact B2210123
  · exact B2210127
  · exact B2210131
  · exact B2210135
  · exact B2210139
  · exact B2210143
  · exact B2210147
  · exact B2210151
  · exact B2210155
  · exact B2210159
  · exact B2210163
  · exact B2210167
  · exact B2210171
  · exact B2210175
  · exact B2210179
  · exact B2210183
  · exact B2210187
  · exact B2210191
  · exact B2210195
  · exact B2210199
  · exact B2210203
  · exact B2210207
  · exact B2210211
  · exact B2210215
  · exact B2210219
  · exact B2210223
  · exact B2210227
  · exact B2210231
  · exact B2210235
  · exact B2210239
  · exact B2210243
  · exact B2210247
  · exact B2210251
  · exact B2210255
  · exact B2210259
  · exact B2210263
  · exact B2210267
  · exact B2210271
  · exact B2210275
  · exact B2210279
  · exact B2210283
  · exact B2210287
  · exact B2210291
  · exact B2210295
  · exact B2210299
  · exact B2210303
  · exact B2210307
  · exact B2210311
  · exact B2210315
  · exact B2210319
  · exact B2210323
  · exact B2210327
  · exact B2210331
  · exact B2210335
  · exact B2210339
  · exact B2210343
  · exact B2210347
  · exact B2210351
  · exact B2210355
  · exact B2210359
  · exact B2210363
  · exact B2210367
  · exact B2210371
  · exact B2210375
  · exact B2210379
  · exact B2210383
  · exact B2210387
  · exact B2210391
  · exact B2210395
  · exact B2210399
  · exact B2210403
  · exact B2210407
  · exact B2210411
  · exact B2210415
  · exact B2210419
  · exact B2210423
  · exact B2210427
  · exact B2210431
  · exact B2210435
  · exact B2210439
  · exact B2210443
  · exact B2210447
  · exact B2210451
  · exact B2210455
  · exact B2210459
  · exact B2210463
  · exact B2210467
  · exact B2210471
  · exact B2210475
  · exact B2210479
  · exact B2210483
  · exact B2210487
  · exact B2210491
  · exact B2210495
  · exact B2210499
  · exact B2210503
  · exact B2210507
  · exact B2210511
  · exact B2210515
  · exact B2210519
  · exact B2210523
  · exact B2210527
  · exact B2210531
  · exact B2210535
  · exact B2210539
  · exact B2210543
  · exact B2210547
  · exact B2210551
  · exact B2210555
  · exact B2210559
  · exact B2210563
  · exact B2210567
  · exact B2210571
  · exact B2210575
  · exact B2210579
  · exact B2210583
  · exact B2210587
  · exact B2210591
  · exact B2210595
  · exact B2210599
  · exact B2210603
  · exact B2210607
  · exact B2210611
  · exact B2210615
  · exact B2210619
  · exact B2210623
  · exact B2210627
  · exact B2210631
  · exact B2210635
  · exact B2210639
  · exact B2210643
  · exact B2210647
  · exact B2210651
  · exact B2210655
  · exact B2210659
  · exact B2210663
  · exact B2210667
  · exact B2210671
  · exact B2210675
  · exact B2210679
  · exact B2210683
  · exact B2210687
  · exact B2210691
  · exact B2210695
  · exact B2210699
  · exact B2210703
  · exact B2210707
  · exact B2210711
  · exact B2210715
  · exact B2210719
  · exact B2210723
  · exact B2210727
  · exact B2210731
  · exact B2210735
  · exact B2210739
  · exact B2210743
  · exact B2210747
  · exact B2210751
  · exact B2210755
  · exact B2210759
  · exact B2210763
  · exact B2210767
  · exact B2210771
  · exact B2210775
  · exact B2210779
  · exact B2210783
  · exact B2210787
  · exact B2210791
  · exact B2210795
  · exact B2210799
  · exact B2210803
  · exact B2210807
  · exact B2210811
  · exact B2210815
  · exact B2210819
  · exact B2210823
  · exact B2210827
  · exact B2210831
  · exact B2210835
  · exact B2210839
  · exact B2210843
  · exact B2210847
  · exact B2210851
  · exact B2210855
  · exact B2210859
  · exact B2210863
  · exact B2210867
  · exact B2210871
  · exact B2210875
  · exact B2210879
  · exact B2210883
  · exact B2210887
  · exact B2210891
  · exact B2210895
  · exact B2210899
  · exact B2210903
  · exact B2210907
  · exact B2210911
  · exact B2210915
  · exact B2210919
  · exact B2210923
  · exact B2210927
  · exact B2210931
  · exact B2210935
  · exact B2210939
  · exact B2210943
  · exact B2210947
  · exact B2210951
  · exact B2210955
  · exact B2210959
  · exact B2210963
  · exact B2210967
  · exact B2210971
  · exact B2210975
  · exact B2210979
  · exact B2210983
  · exact B2210987
  · exact B2210991
  · exact B2210995
  · exact B2210999
  · exact B2211003
  · exact B2211007
  · exact B2211011
  · exact B2211015
  · exact B2211019
  · exact B2211023
  · exact B2211027
  · exact B2211031
  · exact B2211035
  · exact B2211039
  · exact B2211043
  · exact B2211047
  · exact B2211051
  · exact B2211055
  · exact B2211059
  · exact B2211063
  · exact B2211067
  · exact B2211071
  · exact B2211075
  · exact B2211079
  · exact B2211083
  · exact B2211087
  · exact B2211091
  · exact B2211095
  · exact B2211099
  · exact B2211103
  · exact B2211107
  · exact B2211111
  · exact B2211115
  · exact B2211119
  · exact B2211123
  · exact B2211127
  · exact B2211131
  · exact B2211135
  · exact B2211139
  · exact B2211143
  · exact B2211147
  · exact B2211151
  · exact B2211155
  · exact B2211159
  · exact B2211163
  · exact B2211167
  · exact B2211171
  · exact B2211175
  · exact B2211179
  · exact B2211183
  · exact B2211187
  · exact B2211191
  · exact B2211195
  · exact B2211199
  · exact B2211203
  · exact B2211207
  · exact B2211211
  · exact B2211215
  · exact B2211219
  · exact B2211223
  · exact B2211227
  · exact B2211231
  · exact B2211235
  · exact B2211239
  · exact B2211243
  · exact B2211247
  · exact B2211251
  · exact B2211255
  · exact B2211259
  · exact B2211263
  · exact B2211267
  · exact B2211271
  · exact B2211275
  · exact B2211279
  · exact B2211283
  · exact B2211287
  · exact B2211291
  · exact B2211295
  · exact B2211299
  · exact B2211303
  · exact B2211307
  · exact B2211311
  · exact B2211315
  · exact B2211319
  · exact B2211323
  · exact B2211327
  · exact B2211331
  · exact B2211335
  · exact B2211339
  · exact B2211343
  · exact B2211347
  · exact B2211351
  · exact B2211355
  · exact B2211359
  · exact B2211363
  · exact B2211367
  · exact B2211371
  · exact B2211375
  · exact B2211379
  · exact B2211383
  · exact B2211387
  · exact B2211391
  · exact B2211395
  · exact B2211399
  · exact B2211403
  · exact B2211407
  · exact B2211411
  · exact B2211415
  · exact B2211419
  · exact B2211423
  · exact B2211427
  · exact B2211431
  · exact B2211435
theorem solution (m : ℕ) (hlo : 2209435 ≤ m) (hhi : m ≤ 2211435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 552358 ≤ j := by omega
    have hj2 : j ≤ 552858 := by omega
    have hb : Blo 2209435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
