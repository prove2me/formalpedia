-- Prove2me | solution 1 for syracuse_descends_range_1953435_1955435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:43.704449+00:00
-- url     : https://prove2.me/submissions/787ead8d-a5f3-411b-a99e-7fa56bfb88a8

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

theorem B10560469 : Blo 1953435 10560469 := bbase (se 7 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 10560469 = 247511) (by norm_num)
theorem B14080625 : Blo 1953435 14080625 := bstep (se 2 (by rfl) ⟨5280234, by rfl⟩ : syracuseStep 14080625 = 10560469) B10560469
theorem B9387083 : Blo 1953435 9387083 := bstep (se 1 (by rfl) ⟨7040312, by rfl⟩ : syracuseStep 9387083 = 14080625) B14080625
theorem B6258055 : Blo 1953435 6258055 := bstep (se 1 (by rfl) ⟨4693541, by rfl⟩ : syracuseStep 6258055 = 9387083) B9387083
theorem B8344073 : Blo 1953435 8344073 := bstep (se 2 (by rfl) ⟨3129027, by rfl⟩ : syracuseStep 8344073 = 6258055) B6258055
theorem B5562715 : Blo 1953435 5562715 := bstep (se 1 (by rfl) ⟨4172036, by rfl⟩ : syracuseStep 5562715 = 8344073) B8344073
theorem B7416953 : Blo 1953435 7416953 := bstep (se 2 (by rfl) ⟨2781357, by rfl⟩ : syracuseStep 7416953 = 5562715) B5562715
theorem B4944635 : Blo 1953435 4944635 := bstep (se 1 (by rfl) ⟨3708476, by rfl⟩ : syracuseStep 4944635 = 7416953) B7416953
theorem B3296423 : Blo 1953435 3296423 := bstep (se 1 (by rfl) ⟨2472317, by rfl⟩ : syracuseStep 3296423 = 4944635) B4944635
theorem B2197615 : Blo 1953435 2197615 := bstep (se 1 (by rfl) ⟨1648211, by rfl⟩ : syracuseStep 2197615 = 3296423) B3296423
theorem B2930153 : Blo 1953435 2930153 := bstep (se 2 (by rfl) ⟨1098807, by rfl⟩ : syracuseStep 2930153 = 2197615) B2197615
theorem B1953435 : Blo 1953435 1953435 := bstep (se 1 (by rfl) ⟨1465076, by rfl⟩ : syracuseStep 1953435 = 2930153) B2930153
theorem B5280245 : Blo 1953435 5280245 := bbase (se 5 (by rfl) ⟨247511, by rfl⟩ : syracuseStep 5280245 = 495023) (by norm_num)
theorem B3520163 : Blo 1953435 3520163 := bstep (se 1 (by rfl) ⟨2640122, by rfl⟩ : syracuseStep 3520163 = 5280245) B5280245
theorem B2346775 : Blo 1953435 2346775 := bstep (se 1 (by rfl) ⟨1760081, by rfl⟩ : syracuseStep 2346775 = 3520163) B3520163
theorem B12516133 : Blo 1953435 12516133 := bstep (se 4 (by rfl) ⟨1173387, by rfl⟩ : syracuseStep 12516133 = 2346775) B2346775
theorem B16688177 : Blo 1953435 16688177 := bstep (se 2 (by rfl) ⟨6258066, by rfl⟩ : syracuseStep 16688177 = 12516133) B12516133
theorem B11125451 : Blo 1953435 11125451 := bstep (se 1 (by rfl) ⟨8344088, by rfl⟩ : syracuseStep 11125451 = 16688177) B16688177
theorem B7416967 : Blo 1953435 7416967 := bstep (se 1 (by rfl) ⟨5562725, by rfl⟩ : syracuseStep 7416967 = 11125451) B11125451
theorem B9889289 : Blo 1953435 9889289 := bstep (se 2 (by rfl) ⟨3708483, by rfl⟩ : syracuseStep 9889289 = 7416967) B7416967
theorem B6592859 : Blo 1953435 6592859 := bstep (se 1 (by rfl) ⟨4944644, by rfl⟩ : syracuseStep 6592859 = 9889289) B9889289
theorem B4395239 : Blo 1953435 4395239 := bstep (se 1 (by rfl) ⟨3296429, by rfl⟩ : syracuseStep 4395239 = 6592859) B6592859
theorem B2930159 : Blo 1953435 2930159 := bstep (se 1 (by rfl) ⟨2197619, by rfl⟩ : syracuseStep 2930159 = 4395239) B4395239
theorem B1953439 : Blo 1953435 1953439 := bstep (se 1 (by rfl) ⟨1465079, by rfl⟩ : syracuseStep 1953439 = 2930159) B2930159
theorem B2930165 : Blo 1953435 2930165 := bbase (se 5 (by rfl) ⟨137351, by rfl⟩ : syracuseStep 2930165 = 274703) (by norm_num)
theorem B1953443 : Blo 1953435 1953443 := bstep (se 1 (by rfl) ⟨1465082, by rfl⟩ : syracuseStep 1953443 = 2930165) B2930165
theorem B7040357 : Blo 1953435 7040357 := bbase (se 4 (by rfl) ⟨660033, by rfl⟩ : syracuseStep 7040357 = 1320067) (by norm_num)
theorem B4693571 : Blo 1953435 4693571 := bstep (se 1 (by rfl) ⟨3520178, by rfl⟩ : syracuseStep 4693571 = 7040357) B7040357
theorem B3129047 : Blo 1953435 3129047 := bstep (se 1 (by rfl) ⟨2346785, by rfl⟩ : syracuseStep 3129047 = 4693571) B4693571
theorem B2086031 : Blo 1953435 2086031 := bstep (se 1 (by rfl) ⟨1564523, by rfl⟩ : syracuseStep 2086031 = 3129047) B3129047
theorem B5562749 : Blo 1953435 5562749 := bstep (se 3 (by rfl) ⟨1043015, by rfl⟩ : syracuseStep 5562749 = 2086031) B2086031
theorem B3708499 : Blo 1953435 3708499 := bstep (se 1 (by rfl) ⟨2781374, by rfl⟩ : syracuseStep 3708499 = 5562749) B5562749
theorem B4944665 : Blo 1953435 4944665 := bstep (se 2 (by rfl) ⟨1854249, by rfl⟩ : syracuseStep 4944665 = 3708499) B3708499
theorem B3296443 : Blo 1953435 3296443 := bstep (se 1 (by rfl) ⟨2472332, by rfl⟩ : syracuseStep 3296443 = 4944665) B4944665
theorem B4395257 : Blo 1953435 4395257 := bstep (se 2 (by rfl) ⟨1648221, by rfl⟩ : syracuseStep 4395257 = 3296443) B3296443
theorem B2930171 : Blo 1953435 2930171 := bstep (se 1 (by rfl) ⟨2197628, by rfl⟩ : syracuseStep 2930171 = 4395257) B4395257
theorem B1953447 : Blo 1953435 1953447 := bstep (se 1 (by rfl) ⟨1465085, by rfl⟩ : syracuseStep 1953447 = 2930171) B2930171
theorem B2197633 : Blo 1953435 2197633 := bbase (se 2 (by rfl) ⟨824112, by rfl⟩ : syracuseStep 2197633 = 1648225) (by norm_num)
theorem B2930177 : Blo 1953435 2930177 := bstep (se 2 (by rfl) ⟨1098816, by rfl⟩ : syracuseStep 2930177 = 2197633) B2197633
theorem B1953451 : Blo 1953435 1953451 := bstep (se 1 (by rfl) ⟨1465088, by rfl⟩ : syracuseStep 1953451 = 2930177) B2930177
theorem B4944685 : Blo 1953435 4944685 := bbase (se 3 (by rfl) ⟨927128, by rfl⟩ : syracuseStep 4944685 = 1854257) (by norm_num)
theorem B6592913 : Blo 1953435 6592913 := bstep (se 2 (by rfl) ⟨2472342, by rfl⟩ : syracuseStep 6592913 = 4944685) B4944685
theorem B4395275 : Blo 1953435 4395275 := bstep (se 1 (by rfl) ⟨3296456, by rfl⟩ : syracuseStep 4395275 = 6592913) B6592913
theorem B2930183 : Blo 1953435 2930183 := bstep (se 1 (by rfl) ⟨2197637, by rfl⟩ : syracuseStep 2930183 = 4395275) B4395275
theorem B1953455 : Blo 1953435 1953455 := bstep (se 1 (by rfl) ⟨1465091, by rfl⟩ : syracuseStep 1953455 = 2930183) B2930183
theorem B2930189 : Blo 1953435 2930189 := bbase (se 3 (by rfl) ⟨549410, by rfl⟩ : syracuseStep 2930189 = 1098821) (by norm_num)
theorem B1953459 : Blo 1953435 1953459 := bstep (se 1 (by rfl) ⟨1465094, by rfl⟩ : syracuseStep 1953459 = 2930189) B2930189
theorem B4395293 : Blo 1953435 4395293 := bbase (se 3 (by rfl) ⟨824117, by rfl⟩ : syracuseStep 4395293 = 1648235) (by norm_num)
theorem B2930195 : Blo 1953435 2930195 := bstep (se 1 (by rfl) ⟨2197646, by rfl⟩ : syracuseStep 2930195 = 4395293) B4395293
theorem B1953463 : Blo 1953435 1953463 := bstep (se 1 (by rfl) ⟨1465097, by rfl⟩ : syracuseStep 1953463 = 2930195) B2930195
theorem B3296477 : Blo 1953435 3296477 := bbase (se 3 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 3296477 = 1236179) (by norm_num)
theorem B2197651 : Blo 1953435 2197651 := bstep (se 1 (by rfl) ⟨1648238, by rfl⟩ : syracuseStep 2197651 = 3296477) B3296477
theorem B2930201 : Blo 1953435 2930201 := bstep (se 2 (by rfl) ⟨1098825, by rfl⟩ : syracuseStep 2930201 = 2197651) B2197651
theorem B1953467 : Blo 1953435 1953467 := bstep (se 1 (by rfl) ⟨1465100, by rfl⟩ : syracuseStep 1953467 = 2930201) B2930201
theorem B5940373 : Blo 1953435 5940373 := bbase (se 6 (by rfl) ⟨139227, by rfl⟩ : syracuseStep 5940373 = 278455) (by norm_num)
theorem B7920497 : Blo 1953435 7920497 := bstep (se 2 (by rfl) ⟨2970186, by rfl⟩ : syracuseStep 7920497 = 5940373) B5940373
theorem B5280331 : Blo 1953435 5280331 := bstep (se 1 (by rfl) ⟨3960248, by rfl⟩ : syracuseStep 5280331 = 7920497) B7920497
theorem B7040441 : Blo 1953435 7040441 := bstep (se 2 (by rfl) ⟨2640165, by rfl⟩ : syracuseStep 7040441 = 5280331) B5280331
theorem B4693627 : Blo 1953435 4693627 := bstep (se 1 (by rfl) ⟨3520220, by rfl⟩ : syracuseStep 4693627 = 7040441) B7040441
theorem B6258169 : Blo 1953435 6258169 := bstep (se 2 (by rfl) ⟨2346813, by rfl⟩ : syracuseStep 6258169 = 4693627) B4693627
theorem B8344225 : Blo 1953435 8344225 := bstep (se 2 (by rfl) ⟨3129084, by rfl⟩ : syracuseStep 8344225 = 6258169) B6258169
theorem B11125633 : Blo 1953435 11125633 := bstep (se 2 (by rfl) ⟨4172112, by rfl⟩ : syracuseStep 11125633 = 8344225) B8344225
theorem B14834177 : Blo 1953435 14834177 := bstep (se 2 (by rfl) ⟨5562816, by rfl⟩ : syracuseStep 14834177 = 11125633) B11125633
theorem B9889451 : Blo 1953435 9889451 := bstep (se 1 (by rfl) ⟨7417088, by rfl⟩ : syracuseStep 9889451 = 14834177) B14834177
theorem B6592967 : Blo 1953435 6592967 := bstep (se 1 (by rfl) ⟨4944725, by rfl⟩ : syracuseStep 6592967 = 9889451) B9889451
theorem B4395311 : Blo 1953435 4395311 := bstep (se 1 (by rfl) ⟨3296483, by rfl⟩ : syracuseStep 4395311 = 6592967) B6592967
theorem B2930207 : Blo 1953435 2930207 := bstep (se 1 (by rfl) ⟨2197655, by rfl⟩ : syracuseStep 2930207 = 4395311) B4395311
theorem B1953471 : Blo 1953435 1953471 := bstep (se 1 (by rfl) ⟨1465103, by rfl⟩ : syracuseStep 1953471 = 2930207) B2930207
theorem B2930213 : Blo 1953435 2930213 := bbase (se 4 (by rfl) ⟨274707, by rfl⟩ : syracuseStep 2930213 = 549415) (by norm_num)
theorem B1953475 : Blo 1953435 1953475 := bstep (se 1 (by rfl) ⟨1465106, by rfl⟩ : syracuseStep 1953475 = 2930213) B2930213
theorem B2472373 : Blo 1953435 2472373 := bbase (se 5 (by rfl) ⟨115892, by rfl⟩ : syracuseStep 2472373 = 231785) (by norm_num)
theorem B3296497 : Blo 1953435 3296497 := bstep (se 2 (by rfl) ⟨1236186, by rfl⟩ : syracuseStep 3296497 = 2472373) B2472373
theorem B4395329 : Blo 1953435 4395329 := bstep (se 2 (by rfl) ⟨1648248, by rfl⟩ : syracuseStep 4395329 = 3296497) B3296497
theorem B2930219 : Blo 1953435 2930219 := bstep (se 1 (by rfl) ⟨2197664, by rfl⟩ : syracuseStep 2930219 = 4395329) B4395329
theorem B1953479 : Blo 1953435 1953479 := bstep (se 1 (by rfl) ⟨1465109, by rfl⟩ : syracuseStep 1953479 = 2930219) B2930219
theorem B2197669 : Blo 1953435 2197669 := bbase (se 4 (by rfl) ⟨206031, by rfl⟩ : syracuseStep 2197669 = 412063) (by norm_num)
theorem B2930225 : Blo 1953435 2930225 := bstep (se 2 (by rfl) ⟨1098834, by rfl⟩ : syracuseStep 2930225 = 2197669) B2197669
theorem B1953483 : Blo 1953435 1953483 := bstep (se 1 (by rfl) ⟨1465112, by rfl⟩ : syracuseStep 1953483 = 2930225) B2930225
theorem B8028629 : Blo 1953435 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B5352419 : Blo 1953435 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B3568279 : Blo 1953435 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B4757705 : Blo 1953435 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B3171803 : Blo 1953435 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B8458141 : Blo 1953435 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B11277521 : Blo 1953435 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B7518347 : Blo 1953435 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B5012231 : Blo 1953435 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B53463797 : Blo 1953435 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B35642531 : Blo 1953435 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B23761687 : Blo 1953435 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B31682249 : Blo 1953435 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B21121499 : Blo 1953435 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B14080999 : Blo 1953435 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B18774665 : Blo 1953435 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B12516443 : Blo 1953435 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B8344295 : Blo 1953435 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B5562863 : Blo 1953435 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B3708575 : Blo 1953435 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B2472383 : Blo 1953435 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B6593021 : Blo 1953435 6593021 := bstep (se 3 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 6593021 = 2472383) B2472383
theorem B4395347 : Blo 1953435 4395347 := bstep (se 1 (by rfl) ⟨3296510, by rfl⟩ : syracuseStep 4395347 = 6593021) B6593021
theorem B2930231 : Blo 1953435 2930231 := bstep (se 1 (by rfl) ⟨2197673, by rfl⟩ : syracuseStep 2930231 = 4395347) B4395347
theorem B1953487 : Blo 1953435 1953487 := bstep (se 1 (by rfl) ⟨1465115, by rfl⟩ : syracuseStep 1953487 = 2930231) B2930231
theorem B2930237 : Blo 1953435 2930237 := bbase (se 3 (by rfl) ⟨549419, by rfl⟩ : syracuseStep 2930237 = 1098839) (by norm_num)
theorem B1953491 : Blo 1953435 1953491 := bstep (se 1 (by rfl) ⟨1465118, by rfl⟩ : syracuseStep 1953491 = 2930237) B2930237
theorem B4395365 : Blo 1953435 4395365 := bbase (se 4 (by rfl) ⟨412065, by rfl⟩ : syracuseStep 4395365 = 824131) (by norm_num)
theorem B2930243 : Blo 1953435 2930243 := bstep (se 1 (by rfl) ⟨2197682, by rfl⟩ : syracuseStep 2930243 = 4395365) B4395365
theorem B1953495 : Blo 1953435 1953495 := bstep (se 1 (by rfl) ⟨1465121, by rfl⟩ : syracuseStep 1953495 = 2930243) B2930243
theorem B4944797 : Blo 1953435 4944797 := bbase (se 3 (by rfl) ⟨927149, by rfl⟩ : syracuseStep 4944797 = 1854299) (by norm_num)
theorem B3296531 : Blo 1953435 3296531 := bstep (se 1 (by rfl) ⟨2472398, by rfl⟩ : syracuseStep 3296531 = 4944797) B4944797
theorem B2197687 : Blo 1953435 2197687 := bstep (se 1 (by rfl) ⟨1648265, by rfl⟩ : syracuseStep 2197687 = 3296531) B3296531
theorem B2930249 : Blo 1953435 2930249 := bstep (se 2 (by rfl) ⟨1098843, by rfl⟩ : syracuseStep 2930249 = 2197687) B2197687
theorem B1953499 : Blo 1953435 1953499 := bstep (se 1 (by rfl) ⟨1465124, by rfl⟩ : syracuseStep 1953499 = 2930249) B2930249
theorem B3708605 : Blo 1953435 3708605 := bbase (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) (by norm_num)
theorem B9889613 : Blo 1953435 9889613 := bstep (se 3 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 9889613 = 3708605) B3708605
theorem B6593075 : Blo 1953435 6593075 := bstep (se 1 (by rfl) ⟨4944806, by rfl⟩ : syracuseStep 6593075 = 9889613) B9889613
theorem B4395383 : Blo 1953435 4395383 := bstep (se 1 (by rfl) ⟨3296537, by rfl⟩ : syracuseStep 4395383 = 6593075) B6593075
theorem B2930255 : Blo 1953435 2930255 := bstep (se 1 (by rfl) ⟨2197691, by rfl⟩ : syracuseStep 2930255 = 4395383) B4395383
theorem B1953503 : Blo 1953435 1953503 := bstep (se 1 (by rfl) ⟨1465127, by rfl⟩ : syracuseStep 1953503 = 2930255) B2930255
theorem B2930261 : Blo 1953435 2930261 := bbase (se 8 (by rfl) ⟨17169, by rfl⟩ : syracuseStep 2930261 = 34339) (by norm_num)
theorem B1953507 : Blo 1953435 1953507 := bstep (se 1 (by rfl) ⟨1465130, by rfl⟩ : syracuseStep 1953507 = 2930261) B2930261
theorem B3129149 : Blo 1953435 3129149 := bbase (se 3 (by rfl) ⟨586715, by rfl⟩ : syracuseStep 3129149 = 1173431) (by norm_num)
theorem B8344397 : Blo 1953435 8344397 := bstep (se 3 (by rfl) ⟨1564574, by rfl⟩ : syracuseStep 8344397 = 3129149) B3129149
theorem B5562931 : Blo 1953435 5562931 := bstep (se 1 (by rfl) ⟨4172198, by rfl⟩ : syracuseStep 5562931 = 8344397) B8344397
theorem B7417241 : Blo 1953435 7417241 := bstep (se 2 (by rfl) ⟨2781465, by rfl⟩ : syracuseStep 7417241 = 5562931) B5562931
theorem B4944827 : Blo 1953435 4944827 := bstep (se 1 (by rfl) ⟨3708620, by rfl⟩ : syracuseStep 4944827 = 7417241) B7417241
theorem B3296551 : Blo 1953435 3296551 := bstep (se 1 (by rfl) ⟨2472413, by rfl⟩ : syracuseStep 3296551 = 4944827) B4944827
theorem B4395401 : Blo 1953435 4395401 := bstep (se 2 (by rfl) ⟨1648275, by rfl⟩ : syracuseStep 4395401 = 3296551) B3296551
theorem B2930267 : Blo 1953435 2930267 := bstep (se 1 (by rfl) ⟨2197700, by rfl⟩ : syracuseStep 2930267 = 4395401) B4395401
theorem B1953511 : Blo 1953435 1953511 := bstep (se 1 (by rfl) ⟨1465133, by rfl⟩ : syracuseStep 1953511 = 2930267) B2930267
theorem B2197705 : Blo 1953435 2197705 := bbase (se 2 (by rfl) ⟨824139, by rfl⟩ : syracuseStep 2197705 = 1648279) (by norm_num)
theorem B2930273 : Blo 1953435 2930273 := bstep (se 2 (by rfl) ⟨1098852, by rfl⟩ : syracuseStep 2930273 = 2197705) B2197705
theorem B1953515 : Blo 1953435 1953515 := bstep (se 1 (by rfl) ⟨1465136, by rfl⟩ : syracuseStep 1953515 = 2930273) B2930273
theorem B1980173 : Blo 1953435 1980173 := bbase (se 3 (by rfl) ⟨371282, by rfl⟩ : syracuseStep 1980173 = 742565) (by norm_num)
theorem B5280461 : Blo 1953435 5280461 := bstep (se 3 (by rfl) ⟨990086, by rfl⟩ : syracuseStep 5280461 = 1980173) B1980173
theorem B3520307 : Blo 1953435 3520307 := bstep (se 1 (by rfl) ⟨2640230, by rfl⟩ : syracuseStep 3520307 = 5280461) B5280461
theorem B9387485 : Blo 1953435 9387485 := bstep (se 3 (by rfl) ⟨1760153, by rfl⟩ : syracuseStep 9387485 = 3520307) B3520307
theorem B6258323 : Blo 1953435 6258323 := bstep (se 1 (by rfl) ⟨4693742, by rfl⟩ : syracuseStep 6258323 = 9387485) B9387485
theorem B16688861 : Blo 1953435 16688861 := bstep (se 3 (by rfl) ⟨3129161, by rfl⟩ : syracuseStep 16688861 = 6258323) B6258323
theorem B11125907 : Blo 1953435 11125907 := bstep (se 1 (by rfl) ⟨8344430, by rfl⟩ : syracuseStep 11125907 = 16688861) B16688861
theorem B7417271 : Blo 1953435 7417271 := bstep (se 1 (by rfl) ⟨5562953, by rfl⟩ : syracuseStep 7417271 = 11125907) B11125907
theorem B4944847 : Blo 1953435 4944847 := bstep (se 1 (by rfl) ⟨3708635, by rfl⟩ : syracuseStep 4944847 = 7417271) B7417271
theorem B6593129 : Blo 1953435 6593129 := bstep (se 2 (by rfl) ⟨2472423, by rfl⟩ : syracuseStep 6593129 = 4944847) B4944847
theorem B4395419 : Blo 1953435 4395419 := bstep (se 1 (by rfl) ⟨3296564, by rfl⟩ : syracuseStep 4395419 = 6593129) B6593129
theorem B2930279 : Blo 1953435 2930279 := bstep (se 1 (by rfl) ⟨2197709, by rfl⟩ : syracuseStep 2930279 = 4395419) B4395419
theorem B1953519 : Blo 1953435 1953519 := bstep (se 1 (by rfl) ⟨1465139, by rfl⟩ : syracuseStep 1953519 = 2930279) B2930279
theorem B2930285 : Blo 1953435 2930285 := bbase (se 3 (by rfl) ⟨549428, by rfl⟩ : syracuseStep 2930285 = 1098857) (by norm_num)
theorem B1953523 : Blo 1953435 1953523 := bstep (se 1 (by rfl) ⟨1465142, by rfl⟩ : syracuseStep 1953523 = 2930285) B2930285
theorem B4395437 : Blo 1953435 4395437 := bbase (se 3 (by rfl) ⟨824144, by rfl⟩ : syracuseStep 4395437 = 1648289) (by norm_num)
theorem B2930291 : Blo 1953435 2930291 := bstep (se 1 (by rfl) ⟨2197718, by rfl⟩ : syracuseStep 2930291 = 4395437) B4395437
theorem B1953527 : Blo 1953435 1953527 := bstep (se 1 (by rfl) ⟨1465145, by rfl⟩ : syracuseStep 1953527 = 2930291) B2930291
theorem B2086121 : Blo 1953435 2086121 := bbase (se 2 (by rfl) ⟨782295, by rfl⟩ : syracuseStep 2086121 = 1564591) (by norm_num)
theorem B5562989 : Blo 1953435 5562989 := bstep (se 3 (by rfl) ⟨1043060, by rfl⟩ : syracuseStep 5562989 = 2086121) B2086121
theorem B3708659 : Blo 1953435 3708659 := bstep (se 1 (by rfl) ⟨2781494, by rfl⟩ : syracuseStep 3708659 = 5562989) B5562989
theorem B2472439 : Blo 1953435 2472439 := bstep (se 1 (by rfl) ⟨1854329, by rfl⟩ : syracuseStep 2472439 = 3708659) B3708659
theorem B3296585 : Blo 1953435 3296585 := bstep (se 2 (by rfl) ⟨1236219, by rfl⟩ : syracuseStep 3296585 = 2472439) B2472439
theorem B2197723 : Blo 1953435 2197723 := bstep (se 1 (by rfl) ⟨1648292, by rfl⟩ : syracuseStep 2197723 = 3296585) B3296585
theorem B2930297 : Blo 1953435 2930297 := bstep (se 2 (by rfl) ⟨1098861, by rfl⟩ : syracuseStep 2930297 = 2197723) B2197723
theorem B1953531 : Blo 1953435 1953531 := bstep (se 1 (by rfl) ⟨1465148, by rfl⟩ : syracuseStep 1953531 = 2930297) B2930297
theorem B2506177 : Blo 1953435 2506177 := bbase (se 2 (by rfl) ⟨939816, by rfl⟩ : syracuseStep 2506177 = 1879633) (by norm_num)
theorem B3341569 : Blo 1953435 3341569 := bstep (se 2 (by rfl) ⟨1253088, by rfl⟩ : syracuseStep 3341569 = 2506177) B2506177
theorem B4455425 : Blo 1953435 4455425 := bstep (se 2 (by rfl) ⟨1670784, by rfl⟩ : syracuseStep 4455425 = 3341569) B3341569
theorem B11881133 : Blo 1953435 11881133 := bstep (se 3 (by rfl) ⟨2227712, by rfl⟩ : syracuseStep 11881133 = 4455425) B4455425
theorem B7920755 : Blo 1953435 7920755 := bstep (se 1 (by rfl) ⟨5940566, by rfl⟩ : syracuseStep 7920755 = 11881133) B11881133
theorem B5280503 : Blo 1953435 5280503 := bstep (se 1 (by rfl) ⟨3960377, by rfl⟩ : syracuseStep 5280503 = 7920755) B7920755
theorem B56325365 : Blo 1953435 56325365 := bstep (se 5 (by rfl) ⟨2640251, by rfl⟩ : syracuseStep 56325365 = 5280503) B5280503
theorem B37550243 : Blo 1953435 37550243 := bstep (se 1 (by rfl) ⟨28162682, by rfl⟩ : syracuseStep 37550243 = 56325365) B56325365
theorem B25033495 : Blo 1953435 25033495 := bstep (se 1 (by rfl) ⟨18775121, by rfl⟩ : syracuseStep 25033495 = 37550243) B37550243
theorem B33377993 : Blo 1953435 33377993 := bstep (se 2 (by rfl) ⟨12516747, by rfl⟩ : syracuseStep 33377993 = 25033495) B25033495
theorem B22251995 : Blo 1953435 22251995 := bstep (se 1 (by rfl) ⟨16688996, by rfl⟩ : syracuseStep 22251995 = 33377993) B33377993
theorem B14834663 : Blo 1953435 14834663 := bstep (se 1 (by rfl) ⟨11125997, by rfl⟩ : syracuseStep 14834663 = 22251995) B22251995
theorem B9889775 : Blo 1953435 9889775 := bstep (se 1 (by rfl) ⟨7417331, by rfl⟩ : syracuseStep 9889775 = 14834663) B14834663
theorem B6593183 : Blo 1953435 6593183 := bstep (se 1 (by rfl) ⟨4944887, by rfl⟩ : syracuseStep 6593183 = 9889775) B9889775
theorem B4395455 : Blo 1953435 4395455 := bstep (se 1 (by rfl) ⟨3296591, by rfl⟩ : syracuseStep 4395455 = 6593183) B6593183
theorem B2930303 : Blo 1953435 2930303 := bstep (se 1 (by rfl) ⟨2197727, by rfl⟩ : syracuseStep 2930303 = 4395455) B4395455
theorem B1953535 : Blo 1953435 1953535 := bstep (se 1 (by rfl) ⟨1465151, by rfl⟩ : syracuseStep 1953535 = 2930303) B2930303
theorem B2930309 : Blo 1953435 2930309 := bbase (se 4 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 2930309 = 549433) (by norm_num)
theorem B1953539 : Blo 1953435 1953539 := bstep (se 1 (by rfl) ⟨1465154, by rfl⟩ : syracuseStep 1953539 = 2930309) B2930309
theorem B3296605 : Blo 1953435 3296605 := bbase (se 3 (by rfl) ⟨618113, by rfl⟩ : syracuseStep 3296605 = 1236227) (by norm_num)
theorem B4395473 : Blo 1953435 4395473 := bstep (se 2 (by rfl) ⟨1648302, by rfl⟩ : syracuseStep 4395473 = 3296605) B3296605
theorem B2930315 : Blo 1953435 2930315 := bstep (se 1 (by rfl) ⟨2197736, by rfl⟩ : syracuseStep 2930315 = 4395473) B4395473
theorem B1953543 : Blo 1953435 1953543 := bstep (se 1 (by rfl) ⟨1465157, by rfl⟩ : syracuseStep 1953543 = 2930315) B2930315
theorem B2197741 : Blo 1953435 2197741 := bbase (se 3 (by rfl) ⟨412076, by rfl⟩ : syracuseStep 2197741 = 824153) (by norm_num)
theorem B2930321 : Blo 1953435 2930321 := bstep (se 2 (by rfl) ⟨1098870, by rfl⟩ : syracuseStep 2930321 = 2197741) B2197741
theorem B1953547 : Blo 1953435 1953547 := bstep (se 1 (by rfl) ⟨1465160, by rfl⟩ : syracuseStep 1953547 = 2930321) B2930321
theorem B6593237 : Blo 1953435 6593237 := bbase (se 7 (by rfl) ⟨77264, by rfl⟩ : syracuseStep 6593237 = 154529) (by norm_num)
theorem B4395491 : Blo 1953435 4395491 := bstep (se 1 (by rfl) ⟨3296618, by rfl⟩ : syracuseStep 4395491 = 6593237) B6593237
theorem B2930327 : Blo 1953435 2930327 := bstep (se 1 (by rfl) ⟨2197745, by rfl⟩ : syracuseStep 2930327 = 4395491) B4395491
theorem B1953551 : Blo 1953435 1953551 := bstep (se 1 (by rfl) ⟨1465163, by rfl⟩ : syracuseStep 1953551 = 2930327) B2930327
theorem B2930333 : Blo 1953435 2930333 := bbase (se 3 (by rfl) ⟨549437, by rfl⟩ : syracuseStep 2930333 = 1098875) (by norm_num)
theorem B1953555 : Blo 1953435 1953555 := bstep (se 1 (by rfl) ⟨1465166, by rfl⟩ : syracuseStep 1953555 = 2930333) B2930333
theorem B4395509 : Blo 1953435 4395509 := bbase (se 5 (by rfl) ⟨206039, by rfl⟩ : syracuseStep 4395509 = 412079) (by norm_num)
theorem B2930339 : Blo 1953435 2930339 := bstep (se 1 (by rfl) ⟨2197754, by rfl⟩ : syracuseStep 2930339 = 4395509) B4395509
theorem B1953559 : Blo 1953435 1953559 := bstep (se 1 (by rfl) ⟨1465169, by rfl⟩ : syracuseStep 1953559 = 2930339) B2930339
theorem B7040773 : Blo 1953435 7040773 := bbase (se 4 (by rfl) ⟨660072, by rfl⟩ : syracuseStep 7040773 = 1320145) (by norm_num)
theorem B37550789 : Blo 1953435 37550789 := bstep (se 4 (by rfl) ⟨3520386, by rfl⟩ : syracuseStep 37550789 = 7040773) B7040773
theorem B25033859 : Blo 1953435 25033859 := bstep (se 1 (by rfl) ⟨18775394, by rfl⟩ : syracuseStep 25033859 = 37550789) B37550789
theorem B16689239 : Blo 1953435 16689239 := bstep (se 1 (by rfl) ⟨12516929, by rfl⟩ : syracuseStep 16689239 = 25033859) B25033859
theorem B11126159 : Blo 1953435 11126159 := bstep (se 1 (by rfl) ⟨8344619, by rfl⟩ : syracuseStep 11126159 = 16689239) B16689239
theorem B7417439 : Blo 1953435 7417439 := bstep (se 1 (by rfl) ⟨5563079, by rfl⟩ : syracuseStep 7417439 = 11126159) B11126159
theorem B4944959 : Blo 1953435 4944959 := bstep (se 1 (by rfl) ⟨3708719, by rfl⟩ : syracuseStep 4944959 = 7417439) B7417439
theorem B3296639 : Blo 1953435 3296639 := bstep (se 1 (by rfl) ⟨2472479, by rfl⟩ : syracuseStep 3296639 = 4944959) B4944959
theorem B2197759 : Blo 1953435 2197759 := bstep (se 1 (by rfl) ⟨1648319, by rfl⟩ : syracuseStep 2197759 = 3296639) B3296639
theorem B2930345 : Blo 1953435 2930345 := bstep (se 2 (by rfl) ⟨1098879, by rfl⟩ : syracuseStep 2930345 = 2197759) B2197759
theorem B1953563 : Blo 1953435 1953563 := bstep (se 1 (by rfl) ⟨1465172, by rfl⟩ : syracuseStep 1953563 = 2930345) B2930345
theorem B7040789 : Blo 1953435 7040789 := bbase (se 6 (by rfl) ⟨165018, by rfl⟩ : syracuseStep 7040789 = 330037) (by norm_num)
theorem B4693859 : Blo 1953435 4693859 := bstep (se 1 (by rfl) ⟨3520394, by rfl⟩ : syracuseStep 4693859 = 7040789) B7040789
theorem B3129239 : Blo 1953435 3129239 := bstep (se 1 (by rfl) ⟨2346929, by rfl⟩ : syracuseStep 3129239 = 4693859) B4693859
theorem B2086159 : Blo 1953435 2086159 := bstep (se 1 (by rfl) ⟨1564619, by rfl⟩ : syracuseStep 2086159 = 3129239) B3129239
theorem B2781545 : Blo 1953435 2781545 := bstep (se 2 (by rfl) ⟨1043079, by rfl⟩ : syracuseStep 2781545 = 2086159) B2086159
theorem B7417453 : Blo 1953435 7417453 := bstep (se 3 (by rfl) ⟨1390772, by rfl⟩ : syracuseStep 7417453 = 2781545) B2781545
theorem B9889937 : Blo 1953435 9889937 := bstep (se 2 (by rfl) ⟨3708726, by rfl⟩ : syracuseStep 9889937 = 7417453) B7417453
theorem B6593291 : Blo 1953435 6593291 := bstep (se 1 (by rfl) ⟨4944968, by rfl⟩ : syracuseStep 6593291 = 9889937) B9889937
theorem B4395527 : Blo 1953435 4395527 := bstep (se 1 (by rfl) ⟨3296645, by rfl⟩ : syracuseStep 4395527 = 6593291) B6593291
theorem B2930351 : Blo 1953435 2930351 := bstep (se 1 (by rfl) ⟨2197763, by rfl⟩ : syracuseStep 2930351 = 4395527) B4395527
theorem B1953567 : Blo 1953435 1953567 := bstep (se 1 (by rfl) ⟨1465175, by rfl⟩ : syracuseStep 1953567 = 2930351) B2930351
theorem B2930357 : Blo 1953435 2930357 := bbase (se 5 (by rfl) ⟨137360, by rfl⟩ : syracuseStep 2930357 = 274721) (by norm_num)
theorem B1953571 : Blo 1953435 1953571 := bstep (se 1 (by rfl) ⟨1465178, by rfl⟩ : syracuseStep 1953571 = 2930357) B2930357
theorem B4944989 : Blo 1953435 4944989 := bbase (se 3 (by rfl) ⟨927185, by rfl⟩ : syracuseStep 4944989 = 1854371) (by norm_num)
theorem B3296659 : Blo 1953435 3296659 := bstep (se 1 (by rfl) ⟨2472494, by rfl⟩ : syracuseStep 3296659 = 4944989) B4944989
theorem B4395545 : Blo 1953435 4395545 := bstep (se 2 (by rfl) ⟨1648329, by rfl⟩ : syracuseStep 4395545 = 3296659) B3296659
theorem B2930363 : Blo 1953435 2930363 := bstep (se 1 (by rfl) ⟨2197772, by rfl⟩ : syracuseStep 2930363 = 4395545) B4395545
theorem B1953575 : Blo 1953435 1953575 := bstep (se 1 (by rfl) ⟨1465181, by rfl⟩ : syracuseStep 1953575 = 2930363) B2930363
theorem B2197777 : Blo 1953435 2197777 := bbase (se 2 (by rfl) ⟨824166, by rfl⟩ : syracuseStep 2197777 = 1648333) (by norm_num)
theorem B2930369 : Blo 1953435 2930369 := bstep (se 2 (by rfl) ⟨1098888, by rfl⟩ : syracuseStep 2930369 = 2197777) B2197777
theorem B1953579 : Blo 1953435 1953579 := bstep (se 1 (by rfl) ⟨1465184, by rfl⟩ : syracuseStep 1953579 = 2930369) B2930369
theorem B3708757 : Blo 1953435 3708757 := bbase (se 9 (by rfl) ⟨10865, by rfl⟩ : syracuseStep 3708757 = 21731) (by norm_num)
theorem B4945009 : Blo 1953435 4945009 := bstep (se 2 (by rfl) ⟨1854378, by rfl⟩ : syracuseStep 4945009 = 3708757) B3708757
theorem B6593345 : Blo 1953435 6593345 := bstep (se 2 (by rfl) ⟨2472504, by rfl⟩ : syracuseStep 6593345 = 4945009) B4945009
theorem B4395563 : Blo 1953435 4395563 := bstep (se 1 (by rfl) ⟨3296672, by rfl⟩ : syracuseStep 4395563 = 6593345) B6593345
theorem B2930375 : Blo 1953435 2930375 := bstep (se 1 (by rfl) ⟨2197781, by rfl⟩ : syracuseStep 2930375 = 4395563) B4395563
theorem B1953583 : Blo 1953435 1953583 := bstep (se 1 (by rfl) ⟨1465187, by rfl⟩ : syracuseStep 1953583 = 2930375) B2930375
theorem B2930381 : Blo 1953435 2930381 := bbase (se 3 (by rfl) ⟨549446, by rfl⟩ : syracuseStep 2930381 = 1098893) (by norm_num)
theorem B1953587 : Blo 1953435 1953587 := bstep (se 1 (by rfl) ⟨1465190, by rfl⟩ : syracuseStep 1953587 = 2930381) B2930381
theorem B4395581 : Blo 1953435 4395581 := bbase (se 3 (by rfl) ⟨824171, by rfl⟩ : syracuseStep 4395581 = 1648343) (by norm_num)
theorem B2930387 : Blo 1953435 2930387 := bstep (se 1 (by rfl) ⟨2197790, by rfl⟩ : syracuseStep 2930387 = 4395581) B4395581
theorem B1953591 : Blo 1953435 1953591 := bstep (se 1 (by rfl) ⟨1465193, by rfl⟩ : syracuseStep 1953591 = 2930387) B2930387
theorem B3296693 : Blo 1953435 3296693 := bbase (se 5 (by rfl) ⟨154532, by rfl⟩ : syracuseStep 3296693 = 309065) (by norm_num)
theorem B2197795 : Blo 1953435 2197795 := bstep (se 1 (by rfl) ⟨1648346, by rfl⟩ : syracuseStep 2197795 = 3296693) B3296693
theorem B2930393 : Blo 1953435 2930393 := bstep (se 2 (by rfl) ⟨1098897, by rfl⟩ : syracuseStep 2930393 = 2197795) B2197795
theorem B1953595 : Blo 1953435 1953595 := bstep (se 1 (by rfl) ⟨1465196, by rfl⟩ : syracuseStep 1953595 = 2930393) B2930393
theorem B2086193 : Blo 1953435 2086193 := bbase (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) (by norm_num)
theorem B5563181 : Blo 1953435 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B14835149 : Blo 1953435 14835149 := bstep (se 3 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 14835149 = 5563181) B5563181
theorem B9890099 : Blo 1953435 9890099 := bstep (se 1 (by rfl) ⟨7417574, by rfl⟩ : syracuseStep 9890099 = 14835149) B14835149
theorem B6593399 : Blo 1953435 6593399 := bstep (se 1 (by rfl) ⟨4945049, by rfl⟩ : syracuseStep 6593399 = 9890099) B9890099
theorem B4395599 : Blo 1953435 4395599 := bstep (se 1 (by rfl) ⟨3296699, by rfl⟩ : syracuseStep 4395599 = 6593399) B6593399
theorem B2930399 : Blo 1953435 2930399 := bstep (se 1 (by rfl) ⟨2197799, by rfl⟩ : syracuseStep 2930399 = 4395599) B4395599
theorem B1953599 : Blo 1953435 1953599 := bstep (se 1 (by rfl) ⟨1465199, by rfl⟩ : syracuseStep 1953599 = 2930399) B2930399
theorem B2930405 : Blo 1953435 2930405 := bbase (se 4 (by rfl) ⟨274725, by rfl⟩ : syracuseStep 2930405 = 549451) (by norm_num)
theorem B1953603 : Blo 1953435 1953603 := bstep (se 1 (by rfl) ⟨1465202, by rfl⟩ : syracuseStep 1953603 = 2930405) B2930405
theorem B5563205 : Blo 1953435 5563205 := bbase (se 4 (by rfl) ⟨521550, by rfl⟩ : syracuseStep 5563205 = 1043101) (by norm_num)
theorem B3708803 : Blo 1953435 3708803 := bstep (se 1 (by rfl) ⟨2781602, by rfl⟩ : syracuseStep 3708803 = 5563205) B5563205
theorem B2472535 : Blo 1953435 2472535 := bstep (se 1 (by rfl) ⟨1854401, by rfl⟩ : syracuseStep 2472535 = 3708803) B3708803
theorem B3296713 : Blo 1953435 3296713 := bstep (se 2 (by rfl) ⟨1236267, by rfl⟩ : syracuseStep 3296713 = 2472535) B2472535
theorem B4395617 : Blo 1953435 4395617 := bstep (se 2 (by rfl) ⟨1648356, by rfl⟩ : syracuseStep 4395617 = 3296713) B3296713
theorem B2930411 : Blo 1953435 2930411 := bstep (se 1 (by rfl) ⟨2197808, by rfl⟩ : syracuseStep 2930411 = 4395617) B4395617
theorem B1953607 : Blo 1953435 1953607 := bstep (se 1 (by rfl) ⟨1465205, by rfl⟩ : syracuseStep 1953607 = 2930411) B2930411
theorem B2197813 : Blo 1953435 2197813 := bbase (se 5 (by rfl) ⟨103022, by rfl⟩ : syracuseStep 2197813 = 206045) (by norm_num)
theorem B2930417 : Blo 1953435 2930417 := bstep (se 2 (by rfl) ⟨1098906, by rfl⟩ : syracuseStep 2930417 = 2197813) B2197813
theorem B1953611 : Blo 1953435 1953611 := bstep (se 1 (by rfl) ⟨1465208, by rfl⟩ : syracuseStep 1953611 = 2930417) B2930417
theorem B2472545 : Blo 1953435 2472545 := bbase (se 2 (by rfl) ⟨927204, by rfl⟩ : syracuseStep 2472545 = 1854409) (by norm_num)
theorem B6593453 : Blo 1953435 6593453 := bstep (se 3 (by rfl) ⟨1236272, by rfl⟩ : syracuseStep 6593453 = 2472545) B2472545
theorem B4395635 : Blo 1953435 4395635 := bstep (se 1 (by rfl) ⟨3296726, by rfl⟩ : syracuseStep 4395635 = 6593453) B6593453
theorem B2930423 : Blo 1953435 2930423 := bstep (se 1 (by rfl) ⟨2197817, by rfl⟩ : syracuseStep 2930423 = 4395635) B4395635
theorem B1953615 : Blo 1953435 1953615 := bstep (se 1 (by rfl) ⟨1465211, by rfl⟩ : syracuseStep 1953615 = 2930423) B2930423
theorem B2930429 : Blo 1953435 2930429 := bbase (se 3 (by rfl) ⟨549455, by rfl⟩ : syracuseStep 2930429 = 1098911) (by norm_num)
theorem B1953619 : Blo 1953435 1953619 := bstep (se 1 (by rfl) ⟨1465214, by rfl⟩ : syracuseStep 1953619 = 2930429) B2930429
theorem B4395653 : Blo 1953435 4395653 := bbase (se 4 (by rfl) ⟨412092, by rfl⟩ : syracuseStep 4395653 = 824185) (by norm_num)
theorem B2930435 : Blo 1953435 2930435 := bstep (se 1 (by rfl) ⟨2197826, by rfl⟩ : syracuseStep 2930435 = 4395653) B4395653
theorem B1953623 : Blo 1953435 1953623 := bstep (se 1 (by rfl) ⟨1465217, by rfl⟩ : syracuseStep 1953623 = 2930435) B2930435
theorem B38583701 : Blo 1953435 38583701 := bbase (se 6 (by rfl) ⟨904305, by rfl⟩ : syracuseStep 38583701 = 1808611) (by norm_num)
theorem B25722467 : Blo 1953435 25722467 := bstep (se 1 (by rfl) ⟨19291850, by rfl⟩ : syracuseStep 25722467 = 38583701) B38583701
theorem B17148311 : Blo 1953435 17148311 := bstep (se 1 (by rfl) ⟨12861233, by rfl⟩ : syracuseStep 17148311 = 25722467) B25722467
theorem B11432207 : Blo 1953435 11432207 := bstep (se 1 (by rfl) ⟨8574155, by rfl⟩ : syracuseStep 11432207 = 17148311) B17148311
theorem B7621471 : Blo 1953435 7621471 := bstep (se 1 (by rfl) ⟨5716103, by rfl⟩ : syracuseStep 7621471 = 11432207) B11432207
theorem B40647845 : Blo 1953435 40647845 := bstep (se 4 (by rfl) ⟨3810735, by rfl⟩ : syracuseStep 40647845 = 7621471) B7621471
theorem B27098563 : Blo 1953435 27098563 := bstep (se 1 (by rfl) ⟨20323922, by rfl⟩ : syracuseStep 27098563 = 40647845) B40647845
theorem B36131417 : Blo 1953435 36131417 := bstep (se 2 (by rfl) ⟨13549281, by rfl⟩ : syracuseStep 36131417 = 27098563) B27098563
theorem B24087611 : Blo 1953435 24087611 := bstep (se 1 (by rfl) ⟨18065708, by rfl⟩ : syracuseStep 24087611 = 36131417) B36131417
theorem B16058407 : Blo 1953435 16058407 := bstep (se 1 (by rfl) ⟨12043805, by rfl⟩ : syracuseStep 16058407 = 24087611) B24087611
theorem B21411209 : Blo 1953435 21411209 := bstep (se 2 (by rfl) ⟨8029203, by rfl⟩ : syracuseStep 21411209 = 16058407) B16058407
theorem B14274139 : Blo 1953435 14274139 := bstep (se 1 (by rfl) ⟨10705604, by rfl⟩ : syracuseStep 14274139 = 21411209) B21411209
theorem B19032185 : Blo 1953435 19032185 := bstep (se 2 (by rfl) ⟨7137069, by rfl⟩ : syracuseStep 19032185 = 14274139) B14274139
theorem B50752493 : Blo 1953435 50752493 := bstep (se 3 (by rfl) ⟨9516092, by rfl⟩ : syracuseStep 50752493 = 19032185) B19032185
theorem B33834995 : Blo 1953435 33834995 := bstep (se 1 (by rfl) ⟨25376246, by rfl⟩ : syracuseStep 33834995 = 50752493) B50752493
theorem B22556663 : Blo 1953435 22556663 := bstep (se 1 (by rfl) ⟨16917497, by rfl⟩ : syracuseStep 22556663 = 33834995) B33834995
theorem B15037775 : Blo 1953435 15037775 := bstep (se 1 (by rfl) ⟨11278331, by rfl⟩ : syracuseStep 15037775 = 22556663) B22556663
theorem B10025183 : Blo 1953435 10025183 := bstep (se 1 (by rfl) ⟨7518887, by rfl⟩ : syracuseStep 10025183 = 15037775) B15037775
theorem B6683455 : Blo 1953435 6683455 := bstep (se 1 (by rfl) ⟨5012591, by rfl⟩ : syracuseStep 6683455 = 10025183) B10025183
theorem B35645093 : Blo 1953435 35645093 := bstep (se 4 (by rfl) ⟨3341727, by rfl⟩ : syracuseStep 35645093 = 6683455) B6683455
theorem B23763395 : Blo 1953435 23763395 := bstep (se 1 (by rfl) ⟨17822546, by rfl⟩ : syracuseStep 23763395 = 35645093) B35645093
theorem B15842263 : Blo 1953435 15842263 := bstep (se 1 (by rfl) ⟨11881697, by rfl⟩ : syracuseStep 15842263 = 23763395) B23763395
theorem B21123017 : Blo 1953435 21123017 := bstep (se 2 (by rfl) ⟨7921131, by rfl⟩ : syracuseStep 21123017 = 15842263) B15842263
theorem B14082011 : Blo 1953435 14082011 := bstep (se 1 (by rfl) ⟨10561508, by rfl⟩ : syracuseStep 14082011 = 21123017) B21123017
theorem B9388007 : Blo 1953435 9388007 := bstep (se 1 (by rfl) ⟨7041005, by rfl⟩ : syracuseStep 9388007 = 14082011) B14082011
theorem B6258671 : Blo 1953435 6258671 := bstep (se 1 (by rfl) ⟨4694003, by rfl⟩ : syracuseStep 6258671 = 9388007) B9388007
theorem B4172447 : Blo 1953435 4172447 := bstep (se 1 (by rfl) ⟨3129335, by rfl⟩ : syracuseStep 4172447 = 6258671) B6258671
theorem B2781631 : Blo 1953435 2781631 := bstep (se 1 (by rfl) ⟨2086223, by rfl⟩ : syracuseStep 2781631 = 4172447) B4172447
theorem B3708841 : Blo 1953435 3708841 := bstep (se 2 (by rfl) ⟨1390815, by rfl⟩ : syracuseStep 3708841 = 2781631) B2781631
theorem B4945121 : Blo 1953435 4945121 := bstep (se 2 (by rfl) ⟨1854420, by rfl⟩ : syracuseStep 4945121 = 3708841) B3708841
theorem B3296747 : Blo 1953435 3296747 := bstep (se 1 (by rfl) ⟨2472560, by rfl⟩ : syracuseStep 3296747 = 4945121) B4945121
theorem B2197831 : Blo 1953435 2197831 := bstep (se 1 (by rfl) ⟨1648373, by rfl⟩ : syracuseStep 2197831 = 3296747) B3296747
theorem B2930441 : Blo 1953435 2930441 := bstep (se 2 (by rfl) ⟨1098915, by rfl⟩ : syracuseStep 2930441 = 2197831) B2197831
theorem B1953627 : Blo 1953435 1953627 := bstep (se 1 (by rfl) ⟨1465220, by rfl⟩ : syracuseStep 1953627 = 2930441) B2930441
theorem B9890261 : Blo 1953435 9890261 := bbase (se 7 (by rfl) ⟨115901, by rfl⟩ : syracuseStep 9890261 = 231803) (by norm_num)
theorem B6593507 : Blo 1953435 6593507 := bstep (se 1 (by rfl) ⟨4945130, by rfl⟩ : syracuseStep 6593507 = 9890261) B9890261
theorem B4395671 : Blo 1953435 4395671 := bstep (se 1 (by rfl) ⟨3296753, by rfl⟩ : syracuseStep 4395671 = 6593507) B6593507
theorem B2930447 : Blo 1953435 2930447 := bstep (se 1 (by rfl) ⟨2197835, by rfl⟩ : syracuseStep 2930447 = 4395671) B4395671
theorem B1953631 : Blo 1953435 1953631 := bstep (se 1 (by rfl) ⟨1465223, by rfl⟩ : syracuseStep 1953631 = 2930447) B2930447
theorem B2930453 : Blo 1953435 2930453 := bbase (se 6 (by rfl) ⟨68682, by rfl⟩ : syracuseStep 2930453 = 137365) (by norm_num)
theorem B1953635 : Blo 1953435 1953635 := bstep (se 1 (by rfl) ⟨1465226, by rfl⟩ : syracuseStep 1953635 = 2930453) B2930453
theorem B5012621 : Blo 1953435 5012621 := bbase (se 3 (by rfl) ⟨939866, by rfl⟩ : syracuseStep 5012621 = 1879733) (by norm_num)
theorem B3341747 : Blo 1953435 3341747 := bstep (se 1 (by rfl) ⟨2506310, by rfl⟩ : syracuseStep 3341747 = 5012621) B5012621
theorem B8911325 : Blo 1953435 8911325 := bstep (se 3 (by rfl) ⟨1670873, by rfl⟩ : syracuseStep 8911325 = 3341747) B3341747
theorem B5940883 : Blo 1953435 5940883 := bstep (se 1 (by rfl) ⟨4455662, by rfl⟩ : syracuseStep 5940883 = 8911325) B8911325
theorem B31684709 : Blo 1953435 31684709 := bstep (se 4 (by rfl) ⟨2970441, by rfl⟩ : syracuseStep 31684709 = 5940883) B5940883
theorem B84492557 : Blo 1953435 84492557 := bstep (se 3 (by rfl) ⟨15842354, by rfl⟩ : syracuseStep 84492557 = 31684709) B31684709
theorem B56328371 : Blo 1953435 56328371 := bstep (se 1 (by rfl) ⟨42246278, by rfl⟩ : syracuseStep 56328371 = 84492557) B84492557
theorem B37552247 : Blo 1953435 37552247 := bstep (se 1 (by rfl) ⟨28164185, by rfl⟩ : syracuseStep 37552247 = 56328371) B56328371
theorem B25034831 : Blo 1953435 25034831 := bstep (se 1 (by rfl) ⟨18776123, by rfl⟩ : syracuseStep 25034831 = 37552247) B37552247
theorem B16689887 : Blo 1953435 16689887 := bstep (se 1 (by rfl) ⟨12517415, by rfl⟩ : syracuseStep 16689887 = 25034831) B25034831
theorem B11126591 : Blo 1953435 11126591 := bstep (se 1 (by rfl) ⟨8344943, by rfl⟩ : syracuseStep 11126591 = 16689887) B16689887
theorem B7417727 : Blo 1953435 7417727 := bstep (se 1 (by rfl) ⟨5563295, by rfl⟩ : syracuseStep 7417727 = 11126591) B11126591
theorem B4945151 : Blo 1953435 4945151 := bstep (se 1 (by rfl) ⟨3708863, by rfl⟩ : syracuseStep 4945151 = 7417727) B7417727
theorem B3296767 : Blo 1953435 3296767 := bstep (se 1 (by rfl) ⟨2472575, by rfl⟩ : syracuseStep 3296767 = 4945151) B4945151
theorem B4395689 : Blo 1953435 4395689 := bstep (se 2 (by rfl) ⟨1648383, by rfl⟩ : syracuseStep 4395689 = 3296767) B3296767
theorem B2930459 : Blo 1953435 2930459 := bstep (se 1 (by rfl) ⟨2197844, by rfl⟩ : syracuseStep 2930459 = 4395689) B4395689
theorem B1953639 : Blo 1953435 1953639 := bstep (se 1 (by rfl) ⟨1465229, by rfl⟩ : syracuseStep 1953639 = 2930459) B2930459
theorem B2197849 : Blo 1953435 2197849 := bbase (se 2 (by rfl) ⟨824193, by rfl⟩ : syracuseStep 2197849 = 1648387) (by norm_num)
theorem B2930465 : Blo 1953435 2930465 := bstep (se 2 (by rfl) ⟨1098924, by rfl⟩ : syracuseStep 2930465 = 2197849) B2197849
theorem B1953643 : Blo 1953435 1953643 := bstep (se 1 (by rfl) ⟨1465232, by rfl⟩ : syracuseStep 1953643 = 2930465) B2930465
theorem B7041077 : Blo 1953435 7041077 := bbase (se 5 (by rfl) ⟨330050, by rfl⟩ : syracuseStep 7041077 = 660101) (by norm_num)
theorem B4694051 : Blo 1953435 4694051 := bstep (se 1 (by rfl) ⟨3520538, by rfl⟩ : syracuseStep 4694051 = 7041077) B7041077
theorem B3129367 : Blo 1953435 3129367 := bstep (se 1 (by rfl) ⟨2347025, by rfl⟩ : syracuseStep 3129367 = 4694051) B4694051
theorem B4172489 : Blo 1953435 4172489 := bstep (se 2 (by rfl) ⟨1564683, by rfl⟩ : syracuseStep 4172489 = 3129367) B3129367
theorem B2781659 : Blo 1953435 2781659 := bstep (se 1 (by rfl) ⟨2086244, by rfl⟩ : syracuseStep 2781659 = 4172489) B4172489
theorem B7417757 : Blo 1953435 7417757 := bstep (se 3 (by rfl) ⟨1390829, by rfl⟩ : syracuseStep 7417757 = 2781659) B2781659
theorem B4945171 : Blo 1953435 4945171 := bstep (se 1 (by rfl) ⟨3708878, by rfl⟩ : syracuseStep 4945171 = 7417757) B7417757
theorem B6593561 : Blo 1953435 6593561 := bstep (se 2 (by rfl) ⟨2472585, by rfl⟩ : syracuseStep 6593561 = 4945171) B4945171
theorem B4395707 : Blo 1953435 4395707 := bstep (se 1 (by rfl) ⟨3296780, by rfl⟩ : syracuseStep 4395707 = 6593561) B6593561
theorem B2930471 : Blo 1953435 2930471 := bstep (se 1 (by rfl) ⟨2197853, by rfl⟩ : syracuseStep 2930471 = 4395707) B4395707
theorem B1953647 : Blo 1953435 1953647 := bstep (se 1 (by rfl) ⟨1465235, by rfl⟩ : syracuseStep 1953647 = 2930471) B2930471
theorem B2930477 : Blo 1953435 2930477 := bbase (se 3 (by rfl) ⟨549464, by rfl⟩ : syracuseStep 2930477 = 1098929) (by norm_num)
theorem B1953651 : Blo 1953435 1953651 := bstep (se 1 (by rfl) ⟨1465238, by rfl⟩ : syracuseStep 1953651 = 2930477) B2930477
theorem B4395725 : Blo 1953435 4395725 := bbase (se 3 (by rfl) ⟨824198, by rfl⟩ : syracuseStep 4395725 = 1648397) (by norm_num)
theorem B2930483 : Blo 1953435 2930483 := bstep (se 1 (by rfl) ⟨2197862, by rfl⟩ : syracuseStep 2930483 = 4395725) B4395725
theorem B1953655 : Blo 1953435 1953655 := bstep (se 1 (by rfl) ⟨1465241, by rfl⟩ : syracuseStep 1953655 = 2930483) B2930483
theorem B2472601 : Blo 1953435 2472601 := bbase (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) (by norm_num)
theorem B3296801 : Blo 1953435 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B2197867 : Blo 1953435 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B2930489 : Blo 1953435 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B1953659 : Blo 1953435 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B8345045 : Blo 1953435 8345045 := bbase (se 7 (by rfl) ⟨97793, by rfl⟩ : syracuseStep 8345045 = 195587) (by norm_num)
theorem B22253453 : Blo 1953435 22253453 := bstep (se 3 (by rfl) ⟨4172522, by rfl⟩ : syracuseStep 22253453 = 8345045) B8345045
theorem B14835635 : Blo 1953435 14835635 := bstep (se 1 (by rfl) ⟨11126726, by rfl⟩ : syracuseStep 14835635 = 22253453) B22253453
theorem B9890423 : Blo 1953435 9890423 := bstep (se 1 (by rfl) ⟨7417817, by rfl⟩ : syracuseStep 9890423 = 14835635) B14835635
theorem B6593615 : Blo 1953435 6593615 := bstep (se 1 (by rfl) ⟨4945211, by rfl⟩ : syracuseStep 6593615 = 9890423) B9890423
theorem B4395743 : Blo 1953435 4395743 := bstep (se 1 (by rfl) ⟨3296807, by rfl⟩ : syracuseStep 4395743 = 6593615) B6593615
theorem B2930495 : Blo 1953435 2930495 := bstep (se 1 (by rfl) ⟨2197871, by rfl⟩ : syracuseStep 2930495 = 4395743) B4395743
theorem B1953663 : Blo 1953435 1953663 := bstep (se 1 (by rfl) ⟨1465247, by rfl⟩ : syracuseStep 1953663 = 2930495) B2930495
theorem B2930501 : Blo 1953435 2930501 := bbase (se 4 (by rfl) ⟨274734, by rfl⟩ : syracuseStep 2930501 = 549469) (by norm_num)
theorem B1953667 : Blo 1953435 1953667 := bstep (se 1 (by rfl) ⟨1465250, by rfl⟩ : syracuseStep 1953667 = 2930501) B2930501
theorem B3296821 : Blo 1953435 3296821 := bbase (se 5 (by rfl) ⟨154538, by rfl⟩ : syracuseStep 3296821 = 309077) (by norm_num)
theorem B4395761 : Blo 1953435 4395761 := bstep (se 2 (by rfl) ⟨1648410, by rfl⟩ : syracuseStep 4395761 = 3296821) B3296821
theorem B2930507 : Blo 1953435 2930507 := bstep (se 1 (by rfl) ⟨2197880, by rfl⟩ : syracuseStep 2930507 = 4395761) B4395761
theorem B1953671 : Blo 1953435 1953671 := bstep (se 1 (by rfl) ⟨1465253, by rfl⟩ : syracuseStep 1953671 = 2930507) B2930507
theorem B2197885 : Blo 1953435 2197885 := bbase (se 3 (by rfl) ⟨412103, by rfl⟩ : syracuseStep 2197885 = 824207) (by norm_num)
theorem B2930513 : Blo 1953435 2930513 := bstep (se 2 (by rfl) ⟨1098942, by rfl⟩ : syracuseStep 2930513 = 2197885) B2197885
theorem B1953675 : Blo 1953435 1953675 := bstep (se 1 (by rfl) ⟨1465256, by rfl⟩ : syracuseStep 1953675 = 2930513) B2930513
theorem B6593669 : Blo 1953435 6593669 := bbase (se 4 (by rfl) ⟨618156, by rfl⟩ : syracuseStep 6593669 = 1236313) (by norm_num)
theorem B4395779 : Blo 1953435 4395779 := bstep (se 1 (by rfl) ⟨3296834, by rfl⟩ : syracuseStep 4395779 = 6593669) B6593669
theorem B2930519 : Blo 1953435 2930519 := bstep (se 1 (by rfl) ⟨2197889, by rfl⟩ : syracuseStep 2930519 = 4395779) B4395779
theorem B1953679 : Blo 1953435 1953679 := bstep (se 1 (by rfl) ⟨1465259, by rfl⟩ : syracuseStep 1953679 = 2930519) B2930519
theorem B2930525 : Blo 1953435 2930525 := bbase (se 3 (by rfl) ⟨549473, by rfl⟩ : syracuseStep 2930525 = 1098947) (by norm_num)
theorem B1953683 : Blo 1953435 1953683 := bstep (se 1 (by rfl) ⟨1465262, by rfl⟩ : syracuseStep 1953683 = 2930525) B2930525
theorem B4395797 : Blo 1953435 4395797 := bbase (se 6 (by rfl) ⟨103026, by rfl⟩ : syracuseStep 4395797 = 206053) (by norm_num)
theorem B2930531 : Blo 1953435 2930531 := bstep (se 1 (by rfl) ⟨2197898, by rfl⟩ : syracuseStep 2930531 = 4395797) B4395797
theorem B1953687 : Blo 1953435 1953687 := bstep (se 1 (by rfl) ⟨1465265, by rfl⟩ : syracuseStep 1953687 = 2930531) B2930531
theorem B7417925 : Blo 1953435 7417925 := bbase (se 4 (by rfl) ⟨695430, by rfl⟩ : syracuseStep 7417925 = 1390861) (by norm_num)
theorem B4945283 : Blo 1953435 4945283 := bstep (se 1 (by rfl) ⟨3708962, by rfl⟩ : syracuseStep 4945283 = 7417925) B7417925
theorem B3296855 : Blo 1953435 3296855 := bstep (se 1 (by rfl) ⟨2472641, by rfl⟩ : syracuseStep 3296855 = 4945283) B4945283
theorem B2197903 : Blo 1953435 2197903 := bstep (se 1 (by rfl) ⟨1648427, by rfl⟩ : syracuseStep 2197903 = 3296855) B3296855
theorem B2930537 : Blo 1953435 2930537 := bstep (se 2 (by rfl) ⟨1098951, by rfl⟩ : syracuseStep 2930537 = 2197903) B2197903
theorem B1953691 : Blo 1953435 1953691 := bstep (se 1 (by rfl) ⟨1465268, by rfl⟩ : syracuseStep 1953691 = 2930537) B2930537
theorem B3172141 : Blo 1953435 3172141 := bbase (se 3 (by rfl) ⟨594776, by rfl⟩ : syracuseStep 3172141 = 1189553) (by norm_num)
theorem B16918085 : Blo 1953435 16918085 := bstep (se 4 (by rfl) ⟨1586070, by rfl⟩ : syracuseStep 16918085 = 3172141) B3172141
theorem B11278723 : Blo 1953435 11278723 := bstep (se 1 (by rfl) ⟨8459042, by rfl⟩ : syracuseStep 11278723 = 16918085) B16918085
theorem B15038297 : Blo 1953435 15038297 := bstep (se 2 (by rfl) ⟨5639361, by rfl⟩ : syracuseStep 15038297 = 11278723) B11278723
theorem B10025531 : Blo 1953435 10025531 := bstep (se 1 (by rfl) ⟨7519148, by rfl⟩ : syracuseStep 10025531 = 15038297) B15038297
theorem B6683687 : Blo 1953435 6683687 := bstep (se 1 (by rfl) ⟨5012765, by rfl⟩ : syracuseStep 6683687 = 10025531) B10025531
theorem B4455791 : Blo 1953435 4455791 := bstep (se 1 (by rfl) ⟨3341843, by rfl⟩ : syracuseStep 4455791 = 6683687) B6683687
theorem B2970527 : Blo 1953435 2970527 := bstep (se 1 (by rfl) ⟨2227895, by rfl⟩ : syracuseStep 2970527 = 4455791) B4455791
theorem B7921405 : Blo 1953435 7921405 := bstep (se 3 (by rfl) ⟨1485263, by rfl⟩ : syracuseStep 7921405 = 2970527) B2970527
theorem B10561873 : Blo 1953435 10561873 := bstep (se 2 (by rfl) ⟨3960702, by rfl⟩ : syracuseStep 10561873 = 7921405) B7921405
theorem B14082497 : Blo 1953435 14082497 := bstep (se 2 (by rfl) ⟨5280936, by rfl⟩ : syracuseStep 14082497 = 10561873) B10561873
theorem B9388331 : Blo 1953435 9388331 := bstep (se 1 (by rfl) ⟨7041248, by rfl⟩ : syracuseStep 9388331 = 14082497) B14082497
theorem B6258887 : Blo 1953435 6258887 := bstep (se 1 (by rfl) ⟨4694165, by rfl⟩ : syracuseStep 6258887 = 9388331) B9388331
theorem B4172591 : Blo 1953435 4172591 := bstep (se 1 (by rfl) ⟨3129443, by rfl⟩ : syracuseStep 4172591 = 6258887) B6258887
theorem B11126909 : Blo 1953435 11126909 := bstep (se 3 (by rfl) ⟨2086295, by rfl⟩ : syracuseStep 11126909 = 4172591) B4172591
theorem B7417939 : Blo 1953435 7417939 := bstep (se 1 (by rfl) ⟨5563454, by rfl⟩ : syracuseStep 7417939 = 11126909) B11126909
theorem B9890585 : Blo 1953435 9890585 := bstep (se 2 (by rfl) ⟨3708969, by rfl⟩ : syracuseStep 9890585 = 7417939) B7417939
theorem B6593723 : Blo 1953435 6593723 := bstep (se 1 (by rfl) ⟨4945292, by rfl⟩ : syracuseStep 6593723 = 9890585) B9890585
theorem B4395815 : Blo 1953435 4395815 := bstep (se 1 (by rfl) ⟨3296861, by rfl⟩ : syracuseStep 4395815 = 6593723) B6593723
theorem B2930543 : Blo 1953435 2930543 := bstep (se 1 (by rfl) ⟨2197907, by rfl⟩ : syracuseStep 2930543 = 4395815) B4395815
theorem B1953695 : Blo 1953435 1953695 := bstep (se 1 (by rfl) ⟨1465271, by rfl⟩ : syracuseStep 1953695 = 2930543) B2930543
theorem B2930549 : Blo 1953435 2930549 := bbase (se 5 (by rfl) ⟨137369, by rfl⟩ : syracuseStep 2930549 = 274739) (by norm_num)
theorem B1953699 : Blo 1953435 1953699 := bstep (se 1 (by rfl) ⟨1465274, by rfl⟩ : syracuseStep 1953699 = 2930549) B2930549
theorem B2347093 : Blo 1953435 2347093 := bbase (se 8 (by rfl) ⟨13752, by rfl⟩ : syracuseStep 2347093 = 27505) (by norm_num)
theorem B3129457 : Blo 1953435 3129457 := bstep (se 2 (by rfl) ⟨1173546, by rfl⟩ : syracuseStep 3129457 = 2347093) B2347093
theorem B4172609 : Blo 1953435 4172609 := bstep (se 2 (by rfl) ⟨1564728, by rfl⟩ : syracuseStep 4172609 = 3129457) B3129457
theorem B2781739 : Blo 1953435 2781739 := bstep (se 1 (by rfl) ⟨2086304, by rfl⟩ : syracuseStep 2781739 = 4172609) B4172609
theorem B3708985 : Blo 1953435 3708985 := bstep (se 2 (by rfl) ⟨1390869, by rfl⟩ : syracuseStep 3708985 = 2781739) B2781739
theorem B4945313 : Blo 1953435 4945313 := bstep (se 2 (by rfl) ⟨1854492, by rfl⟩ : syracuseStep 4945313 = 3708985) B3708985
theorem B3296875 : Blo 1953435 3296875 := bstep (se 1 (by rfl) ⟨2472656, by rfl⟩ : syracuseStep 3296875 = 4945313) B4945313
theorem B4395833 : Blo 1953435 4395833 := bstep (se 2 (by rfl) ⟨1648437, by rfl⟩ : syracuseStep 4395833 = 3296875) B3296875
theorem B2930555 : Blo 1953435 2930555 := bstep (se 1 (by rfl) ⟨2197916, by rfl⟩ : syracuseStep 2930555 = 4395833) B4395833
theorem B1953703 : Blo 1953435 1953703 := bstep (se 1 (by rfl) ⟨1465277, by rfl⟩ : syracuseStep 1953703 = 2930555) B2930555
theorem B2197921 : Blo 1953435 2197921 := bbase (se 2 (by rfl) ⟨824220, by rfl⟩ : syracuseStep 2197921 = 1648441) (by norm_num)
theorem B2930561 : Blo 1953435 2930561 := bstep (se 2 (by rfl) ⟨1098960, by rfl⟩ : syracuseStep 2930561 = 2197921) B2197921
theorem B1953707 : Blo 1953435 1953707 := bstep (se 1 (by rfl) ⟨1465280, by rfl⟩ : syracuseStep 1953707 = 2930561) B2930561
theorem B4945333 : Blo 1953435 4945333 := bbase (se 5 (by rfl) ⟨231812, by rfl⟩ : syracuseStep 4945333 = 463625) (by norm_num)
theorem B6593777 : Blo 1953435 6593777 := bstep (se 2 (by rfl) ⟨2472666, by rfl⟩ : syracuseStep 6593777 = 4945333) B4945333
theorem B4395851 : Blo 1953435 4395851 := bstep (se 1 (by rfl) ⟨3296888, by rfl⟩ : syracuseStep 4395851 = 6593777) B6593777
theorem B2930567 : Blo 1953435 2930567 := bstep (se 1 (by rfl) ⟨2197925, by rfl⟩ : syracuseStep 2930567 = 4395851) B4395851
theorem B1953711 : Blo 1953435 1953711 := bstep (se 1 (by rfl) ⟨1465283, by rfl⟩ : syracuseStep 1953711 = 2930567) B2930567
theorem B2930573 : Blo 1953435 2930573 := bbase (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) (by norm_num)
theorem B1953715 : Blo 1953435 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B4395869 : Blo 1953435 4395869 := bbase (se 3 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 4395869 = 1648451) (by norm_num)
theorem B2930579 : Blo 1953435 2930579 := bstep (se 1 (by rfl) ⟨2197934, by rfl⟩ : syracuseStep 2930579 = 4395869) B4395869
theorem B1953719 : Blo 1953435 1953719 := bstep (se 1 (by rfl) ⟨1465289, by rfl⟩ : syracuseStep 1953719 = 2930579) B2930579
theorem B3296909 : Blo 1953435 3296909 := bbase (se 3 (by rfl) ⟨618170, by rfl⟩ : syracuseStep 3296909 = 1236341) (by norm_num)
theorem B2197939 : Blo 1953435 2197939 := bstep (se 1 (by rfl) ⟨1648454, by rfl⟩ : syracuseStep 2197939 = 3296909) B3296909
theorem B2930585 : Blo 1953435 2930585 := bstep (se 2 (by rfl) ⟨1098969, by rfl⟩ : syracuseStep 2930585 = 2197939) B2197939
theorem B1953723 : Blo 1953435 1953723 := bstep (se 1 (by rfl) ⟨1465292, by rfl⟩ : syracuseStep 1953723 = 2930585) B2930585
theorem B2347121 : Blo 1953435 2347121 := bbase (se 2 (by rfl) ⟨880170, by rfl⟩ : syracuseStep 2347121 = 1760341) (by norm_num)
theorem B6258989 : Blo 1953435 6258989 := bstep (se 3 (by rfl) ⟨1173560, by rfl⟩ : syracuseStep 6258989 = 2347121) B2347121
theorem B16690637 : Blo 1953435 16690637 := bstep (se 3 (by rfl) ⟨3129494, by rfl⟩ : syracuseStep 16690637 = 6258989) B6258989
theorem B11127091 : Blo 1953435 11127091 := bstep (se 1 (by rfl) ⟨8345318, by rfl⟩ : syracuseStep 11127091 = 16690637) B16690637
theorem B14836121 : Blo 1953435 14836121 := bstep (se 2 (by rfl) ⟨5563545, by rfl⟩ : syracuseStep 14836121 = 11127091) B11127091
theorem B9890747 : Blo 1953435 9890747 := bstep (se 1 (by rfl) ⟨7418060, by rfl⟩ : syracuseStep 9890747 = 14836121) B14836121
theorem B6593831 : Blo 1953435 6593831 := bstep (se 1 (by rfl) ⟨4945373, by rfl⟩ : syracuseStep 6593831 = 9890747) B9890747
theorem B4395887 : Blo 1953435 4395887 := bstep (se 1 (by rfl) ⟨3296915, by rfl⟩ : syracuseStep 4395887 = 6593831) B6593831
theorem B2930591 : Blo 1953435 2930591 := bstep (se 1 (by rfl) ⟨2197943, by rfl⟩ : syracuseStep 2930591 = 4395887) B4395887
theorem B1953727 : Blo 1953435 1953727 := bstep (se 1 (by rfl) ⟨1465295, by rfl⟩ : syracuseStep 1953727 = 2930591) B2930591
theorem B2930597 : Blo 1953435 2930597 := bbase (se 4 (by rfl) ⟨274743, by rfl⟩ : syracuseStep 2930597 = 549487) (by norm_num)
theorem B1953731 : Blo 1953435 1953731 := bstep (se 1 (by rfl) ⟨1465298, by rfl⟩ : syracuseStep 1953731 = 2930597) B2930597
theorem B2472697 : Blo 1953435 2472697 := bbase (se 2 (by rfl) ⟨927261, by rfl⟩ : syracuseStep 2472697 = 1854523) (by norm_num)
theorem B3296929 : Blo 1953435 3296929 := bstep (se 2 (by rfl) ⟨1236348, by rfl⟩ : syracuseStep 3296929 = 2472697) B2472697
theorem B4395905 : Blo 1953435 4395905 := bstep (se 2 (by rfl) ⟨1648464, by rfl⟩ : syracuseStep 4395905 = 3296929) B3296929
theorem B2930603 : Blo 1953435 2930603 := bstep (se 1 (by rfl) ⟨2197952, by rfl⟩ : syracuseStep 2930603 = 4395905) B4395905
theorem B1953735 : Blo 1953435 1953735 := bstep (se 1 (by rfl) ⟨1465301, by rfl⟩ : syracuseStep 1953735 = 2930603) B2930603
theorem B2197957 : Blo 1953435 2197957 := bbase (se 4 (by rfl) ⟨206058, by rfl⟩ : syracuseStep 2197957 = 412117) (by norm_num)
theorem B2930609 : Blo 1953435 2930609 := bstep (se 2 (by rfl) ⟨1098978, by rfl⟩ : syracuseStep 2930609 = 2197957) B2197957
theorem B1953739 : Blo 1953435 1953739 := bstep (se 1 (by rfl) ⟨1465304, by rfl⟩ : syracuseStep 1953739 = 2930609) B2930609
theorem B3709061 : Blo 1953435 3709061 := bbase (se 4 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 3709061 = 695449) (by norm_num)
theorem B2472707 : Blo 1953435 2472707 := bstep (se 1 (by rfl) ⟨1854530, by rfl⟩ : syracuseStep 2472707 = 3709061) B3709061
theorem B6593885 : Blo 1953435 6593885 := bstep (se 3 (by rfl) ⟨1236353, by rfl⟩ : syracuseStep 6593885 = 2472707) B2472707
theorem B4395923 : Blo 1953435 4395923 := bstep (se 1 (by rfl) ⟨3296942, by rfl⟩ : syracuseStep 4395923 = 6593885) B6593885
theorem B2930615 : Blo 1953435 2930615 := bstep (se 1 (by rfl) ⟨2197961, by rfl⟩ : syracuseStep 2930615 = 4395923) B4395923
theorem B1953743 : Blo 1953435 1953743 := bstep (se 1 (by rfl) ⟨1465307, by rfl⟩ : syracuseStep 1953743 = 2930615) B2930615
theorem B2930621 : Blo 1953435 2930621 := bbase (se 3 (by rfl) ⟨549491, by rfl⟩ : syracuseStep 2930621 = 1098983) (by norm_num)
theorem B1953747 : Blo 1953435 1953747 := bstep (se 1 (by rfl) ⟨1465310, by rfl⟩ : syracuseStep 1953747 = 2930621) B2930621
theorem B4395941 : Blo 1953435 4395941 := bbase (se 4 (by rfl) ⟨412119, by rfl⟩ : syracuseStep 4395941 = 824239) (by norm_num)
theorem B2930627 : Blo 1953435 2930627 := bstep (se 1 (by rfl) ⟨2197970, by rfl⟩ : syracuseStep 2930627 = 4395941) B4395941
theorem B1953751 : Blo 1953435 1953751 := bstep (se 1 (by rfl) ⟨1465313, by rfl⟩ : syracuseStep 1953751 = 2930627) B2930627
theorem B4945445 : Blo 1953435 4945445 := bbase (se 4 (by rfl) ⟨463635, by rfl⟩ : syracuseStep 4945445 = 927271) (by norm_num)
theorem B3296963 : Blo 1953435 3296963 := bstep (se 1 (by rfl) ⟨2472722, by rfl⟩ : syracuseStep 3296963 = 4945445) B4945445
theorem B2197975 : Blo 1953435 2197975 := bstep (se 1 (by rfl) ⟨1648481, by rfl⟩ : syracuseStep 2197975 = 3296963) B3296963
theorem B2930633 : Blo 1953435 2930633 := bstep (se 2 (by rfl) ⟨1098987, by rfl⟩ : syracuseStep 2930633 = 2197975) B2197975
theorem B1953755 : Blo 1953435 1953755 := bstep (se 1 (by rfl) ⟨1465316, by rfl⟩ : syracuseStep 1953755 = 2930633) B2930633
theorem B5563637 : Blo 1953435 5563637 := bbase (se 5 (by rfl) ⟨260795, by rfl⟩ : syracuseStep 5563637 = 521591) (by norm_num)
theorem B3709091 : Blo 1953435 3709091 := bstep (se 1 (by rfl) ⟨2781818, by rfl⟩ : syracuseStep 3709091 = 5563637) B5563637
theorem B9890909 : Blo 1953435 9890909 := bstep (se 3 (by rfl) ⟨1854545, by rfl⟩ : syracuseStep 9890909 = 3709091) B3709091
theorem B6593939 : Blo 1953435 6593939 := bstep (se 1 (by rfl) ⟨4945454, by rfl⟩ : syracuseStep 6593939 = 9890909) B9890909
theorem B4395959 : Blo 1953435 4395959 := bstep (se 1 (by rfl) ⟨3296969, by rfl⟩ : syracuseStep 4395959 = 6593939) B6593939
theorem B2930639 : Blo 1953435 2930639 := bstep (se 1 (by rfl) ⟨2197979, by rfl⟩ : syracuseStep 2930639 = 4395959) B4395959
theorem B1953759 : Blo 1953435 1953759 := bstep (se 1 (by rfl) ⟨1465319, by rfl⟩ : syracuseStep 1953759 = 2930639) B2930639
theorem B2930645 : Blo 1953435 2930645 := bbase (se 7 (by rfl) ⟨34343, by rfl⟩ : syracuseStep 2930645 = 68687) (by norm_num)
theorem B1953763 : Blo 1953435 1953763 := bstep (se 1 (by rfl) ⟨1465322, by rfl⟩ : syracuseStep 1953763 = 2930645) B2930645
theorem B7418213 : Blo 1953435 7418213 := bbase (se 4 (by rfl) ⟨695457, by rfl⟩ : syracuseStep 7418213 = 1390915) (by norm_num)
theorem B4945475 : Blo 1953435 4945475 := bstep (se 1 (by rfl) ⟨3709106, by rfl⟩ : syracuseStep 4945475 = 7418213) B7418213
theorem B3296983 : Blo 1953435 3296983 := bstep (se 1 (by rfl) ⟨2472737, by rfl⟩ : syracuseStep 3296983 = 4945475) B4945475
theorem B4395977 : Blo 1953435 4395977 := bstep (se 2 (by rfl) ⟨1648491, by rfl⟩ : syracuseStep 4395977 = 3296983) B3296983
theorem B2930651 : Blo 1953435 2930651 := bstep (se 1 (by rfl) ⟨2197988, by rfl⟩ : syracuseStep 2930651 = 4395977) B4395977
theorem B1953767 : Blo 1953435 1953767 := bstep (se 1 (by rfl) ⟨1465325, by rfl⟩ : syracuseStep 1953767 = 2930651) B2930651
theorem B2197993 : Blo 1953435 2197993 := bbase (se 2 (by rfl) ⟨824247, by rfl⟩ : syracuseStep 2197993 = 1648495) (by norm_num)
theorem B2930657 : Blo 1953435 2930657 := bstep (se 2 (by rfl) ⟨1098996, by rfl⟩ : syracuseStep 2930657 = 2197993) B2197993
theorem B1953771 : Blo 1953435 1953771 := bstep (se 1 (by rfl) ⟨1465328, by rfl⟩ : syracuseStep 1953771 = 2930657) B2930657
theorem B2086381 : Blo 1953435 2086381 := bbase (se 3 (by rfl) ⟨391196, by rfl⟩ : syracuseStep 2086381 = 782393) (by norm_num)
theorem B11127365 : Blo 1953435 11127365 := bstep (se 4 (by rfl) ⟨1043190, by rfl⟩ : syracuseStep 11127365 = 2086381) B2086381
theorem B7418243 : Blo 1953435 7418243 := bstep (se 1 (by rfl) ⟨5563682, by rfl⟩ : syracuseStep 7418243 = 11127365) B11127365
theorem B4945495 : Blo 1953435 4945495 := bstep (se 1 (by rfl) ⟨3709121, by rfl⟩ : syracuseStep 4945495 = 7418243) B7418243
theorem B6593993 : Blo 1953435 6593993 := bstep (se 2 (by rfl) ⟨2472747, by rfl⟩ : syracuseStep 6593993 = 4945495) B4945495
theorem B4395995 : Blo 1953435 4395995 := bstep (se 1 (by rfl) ⟨3296996, by rfl⟩ : syracuseStep 4395995 = 6593993) B6593993
theorem B2930663 : Blo 1953435 2930663 := bstep (se 1 (by rfl) ⟨2197997, by rfl⟩ : syracuseStep 2930663 = 4395995) B4395995
theorem B1953775 : Blo 1953435 1953775 := bstep (se 1 (by rfl) ⟨1465331, by rfl⟩ : syracuseStep 1953775 = 2930663) B2930663
theorem B2930669 : Blo 1953435 2930669 := bbase (se 3 (by rfl) ⟨549500, by rfl⟩ : syracuseStep 2930669 = 1099001) (by norm_num)
theorem B1953779 : Blo 1953435 1953779 := bstep (se 1 (by rfl) ⟨1465334, by rfl⟩ : syracuseStep 1953779 = 2930669) B2930669
theorem B4396013 : Blo 1953435 4396013 := bbase (se 3 (by rfl) ⟨824252, by rfl⟩ : syracuseStep 4396013 = 1648505) (by norm_num)
theorem B2930675 : Blo 1953435 2930675 := bstep (se 1 (by rfl) ⟨2198006, by rfl⟩ : syracuseStep 2930675 = 4396013) B4396013
theorem B1953783 : Blo 1953435 1953783 := bstep (se 1 (by rfl) ⟨1465337, by rfl⟩ : syracuseStep 1953783 = 2930675) B2930675
theorem B4172789 : Blo 1953435 4172789 := bbase (se 5 (by rfl) ⟨195599, by rfl⟩ : syracuseStep 4172789 = 391199) (by norm_num)
theorem B2781859 : Blo 1953435 2781859 := bstep (se 1 (by rfl) ⟨2086394, by rfl⟩ : syracuseStep 2781859 = 4172789) B4172789
theorem B3709145 : Blo 1953435 3709145 := bstep (se 2 (by rfl) ⟨1390929, by rfl⟩ : syracuseStep 3709145 = 2781859) B2781859
theorem B2472763 : Blo 1953435 2472763 := bstep (se 1 (by rfl) ⟨1854572, by rfl⟩ : syracuseStep 2472763 = 3709145) B3709145
theorem B3297017 : Blo 1953435 3297017 := bstep (se 2 (by rfl) ⟨1236381, by rfl⟩ : syracuseStep 3297017 = 2472763) B2472763
theorem B2198011 : Blo 1953435 2198011 := bstep (se 1 (by rfl) ⟨1648508, by rfl⟩ : syracuseStep 2198011 = 3297017) B3297017
theorem B2930681 : Blo 1953435 2930681 := bstep (se 2 (by rfl) ⟨1099005, by rfl⟩ : syracuseStep 2930681 = 2198011) B2198011
theorem B1953787 : Blo 1953435 1953787 := bstep (se 1 (by rfl) ⟨1465340, by rfl⟩ : syracuseStep 1953787 = 2930681) B2930681
theorem B15039029 : Blo 1953435 15039029 := bbase (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) (by norm_num)
theorem B10026019 : Blo 1953435 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B13368025 : Blo 1953435 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B17824033 : Blo 1953435 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B95061509 : Blo 1953435 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B63374339 : Blo 1953435 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B168998237 : Blo 1953435 168998237 := bstep (se 3 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 168998237 = 63374339) B63374339
theorem B112665491 : Blo 1953435 112665491 := bstep (se 1 (by rfl) ⟨84499118, by rfl⟩ : syracuseStep 112665491 = 168998237) B168998237
theorem B75110327 : Blo 1953435 75110327 := bstep (se 1 (by rfl) ⟨56332745, by rfl⟩ : syracuseStep 75110327 = 112665491) B112665491
theorem B50073551 : Blo 1953435 50073551 := bstep (se 1 (by rfl) ⟨37555163, by rfl⟩ : syracuseStep 50073551 = 75110327) B75110327
theorem B33382367 : Blo 1953435 33382367 := bstep (se 1 (by rfl) ⟨25036775, by rfl⟩ : syracuseStep 33382367 = 50073551) B50073551
theorem B22254911 : Blo 1953435 22254911 := bstep (se 1 (by rfl) ⟨16691183, by rfl⟩ : syracuseStep 22254911 = 33382367) B33382367
theorem B14836607 : Blo 1953435 14836607 := bstep (se 1 (by rfl) ⟨11127455, by rfl⟩ : syracuseStep 14836607 = 22254911) B22254911
theorem B9891071 : Blo 1953435 9891071 := bstep (se 1 (by rfl) ⟨7418303, by rfl⟩ : syracuseStep 9891071 = 14836607) B14836607
theorem B6594047 : Blo 1953435 6594047 := bstep (se 1 (by rfl) ⟨4945535, by rfl⟩ : syracuseStep 6594047 = 9891071) B9891071
theorem B4396031 : Blo 1953435 4396031 := bstep (se 1 (by rfl) ⟨3297023, by rfl⟩ : syracuseStep 4396031 = 6594047) B6594047
theorem B2930687 : Blo 1953435 2930687 := bstep (se 1 (by rfl) ⟨2198015, by rfl⟩ : syracuseStep 2930687 = 4396031) B4396031
theorem B1953791 : Blo 1953435 1953791 := bstep (se 1 (by rfl) ⟨1465343, by rfl⟩ : syracuseStep 1953791 = 2930687) B2930687
theorem B2930693 : Blo 1953435 2930693 := bbase (se 4 (by rfl) ⟨274752, by rfl⟩ : syracuseStep 2930693 = 549505) (by norm_num)
theorem B1953795 : Blo 1953435 1953795 := bstep (se 1 (by rfl) ⟨1465346, by rfl⟩ : syracuseStep 1953795 = 2930693) B2930693
theorem B3297037 : Blo 1953435 3297037 := bbase (se 3 (by rfl) ⟨618194, by rfl⟩ : syracuseStep 3297037 = 1236389) (by norm_num)
theorem B4396049 : Blo 1953435 4396049 := bstep (se 2 (by rfl) ⟨1648518, by rfl⟩ : syracuseStep 4396049 = 3297037) B3297037
theorem B2930699 : Blo 1953435 2930699 := bstep (se 1 (by rfl) ⟨2198024, by rfl⟩ : syracuseStep 2930699 = 4396049) B4396049
theorem B1953799 : Blo 1953435 1953799 := bstep (se 1 (by rfl) ⟨1465349, by rfl⟩ : syracuseStep 1953799 = 2930699) B2930699
theorem B2198029 : Blo 1953435 2198029 := bbase (se 3 (by rfl) ⟨412130, by rfl⟩ : syracuseStep 2198029 = 824261) (by norm_num)
theorem B2930705 : Blo 1953435 2930705 := bstep (se 2 (by rfl) ⟨1099014, by rfl⟩ : syracuseStep 2930705 = 2198029) B2198029
theorem B1953803 : Blo 1953435 1953803 := bstep (se 1 (by rfl) ⟨1465352, by rfl⟩ : syracuseStep 1953803 = 2930705) B2930705
theorem B6594101 : Blo 1953435 6594101 := bbase (se 5 (by rfl) ⟨309098, by rfl⟩ : syracuseStep 6594101 = 618197) (by norm_num)
theorem B4396067 : Blo 1953435 4396067 := bstep (se 1 (by rfl) ⟨3297050, by rfl⟩ : syracuseStep 4396067 = 6594101) B6594101
theorem B2930711 : Blo 1953435 2930711 := bstep (se 1 (by rfl) ⟨2198033, by rfl⟩ : syracuseStep 2930711 = 4396067) B4396067
theorem B1953807 : Blo 1953435 1953807 := bstep (se 1 (by rfl) ⟨1465355, by rfl⟩ : syracuseStep 1953807 = 2930711) B2930711
theorem B2930717 : Blo 1953435 2930717 := bbase (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) (by norm_num)
theorem B1953811 : Blo 1953435 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B4396085 : Blo 1953435 4396085 := bbase (se 5 (by rfl) ⟨206066, by rfl⟩ : syracuseStep 4396085 = 412133) (by norm_num)
theorem B2930723 : Blo 1953435 2930723 := bstep (se 1 (by rfl) ⟨2198042, by rfl⟩ : syracuseStep 2930723 = 4396085) B4396085
theorem B1953815 : Blo 1953435 1953815 := bstep (se 1 (by rfl) ⟨1465361, by rfl⟩ : syracuseStep 1953815 = 2930723) B2930723
theorem B6259285 : Blo 1953435 6259285 := bbase (se 8 (by rfl) ⟨36675, by rfl⟩ : syracuseStep 6259285 = 73351) (by norm_num)
theorem B8345713 : Blo 1953435 8345713 := bstep (se 2 (by rfl) ⟨3129642, by rfl⟩ : syracuseStep 8345713 = 6259285) B6259285
theorem B11127617 : Blo 1953435 11127617 := bstep (se 2 (by rfl) ⟨4172856, by rfl⟩ : syracuseStep 11127617 = 8345713) B8345713
theorem B7418411 : Blo 1953435 7418411 := bstep (se 1 (by rfl) ⟨5563808, by rfl⟩ : syracuseStep 7418411 = 11127617) B11127617
theorem B4945607 : Blo 1953435 4945607 := bstep (se 1 (by rfl) ⟨3709205, by rfl⟩ : syracuseStep 4945607 = 7418411) B7418411
theorem B3297071 : Blo 1953435 3297071 := bstep (se 1 (by rfl) ⟨2472803, by rfl⟩ : syracuseStep 3297071 = 4945607) B4945607
theorem B2198047 : Blo 1953435 2198047 := bstep (se 1 (by rfl) ⟨1648535, by rfl⟩ : syracuseStep 2198047 = 3297071) B3297071
theorem B2930729 : Blo 1953435 2930729 := bstep (se 2 (by rfl) ⟨1099023, by rfl⟩ : syracuseStep 2930729 = 2198047) B2198047
theorem B1953819 : Blo 1953435 1953819 := bstep (se 1 (by rfl) ⟨1465364, by rfl⟩ : syracuseStep 1953819 = 2930729) B2930729
theorem B7921925 : Blo 1953435 7921925 := bbase (se 4 (by rfl) ⟨742680, by rfl⟩ : syracuseStep 7921925 = 1485361) (by norm_num)
theorem B5281283 : Blo 1953435 5281283 := bstep (se 1 (by rfl) ⟨3960962, by rfl⟩ : syracuseStep 5281283 = 7921925) B7921925
theorem B3520855 : Blo 1953435 3520855 := bstep (se 1 (by rfl) ⟨2640641, by rfl⟩ : syracuseStep 3520855 = 5281283) B5281283
theorem B4694473 : Blo 1953435 4694473 := bstep (se 2 (by rfl) ⟨1760427, by rfl⟩ : syracuseStep 4694473 = 3520855) B3520855
theorem B6259297 : Blo 1953435 6259297 := bstep (se 2 (by rfl) ⟨2347236, by rfl⟩ : syracuseStep 6259297 = 4694473) B4694473
theorem B8345729 : Blo 1953435 8345729 := bstep (se 2 (by rfl) ⟨3129648, by rfl⟩ : syracuseStep 8345729 = 6259297) B6259297
theorem B5563819 : Blo 1953435 5563819 := bstep (se 1 (by rfl) ⟨4172864, by rfl⟩ : syracuseStep 5563819 = 8345729) B8345729
theorem B7418425 : Blo 1953435 7418425 := bstep (se 2 (by rfl) ⟨2781909, by rfl⟩ : syracuseStep 7418425 = 5563819) B5563819
theorem B9891233 : Blo 1953435 9891233 := bstep (se 2 (by rfl) ⟨3709212, by rfl⟩ : syracuseStep 9891233 = 7418425) B7418425
theorem B6594155 : Blo 1953435 6594155 := bstep (se 1 (by rfl) ⟨4945616, by rfl⟩ : syracuseStep 6594155 = 9891233) B9891233
theorem B4396103 : Blo 1953435 4396103 := bstep (se 1 (by rfl) ⟨3297077, by rfl⟩ : syracuseStep 4396103 = 6594155) B6594155
theorem B2930735 : Blo 1953435 2930735 := bstep (se 1 (by rfl) ⟨2198051, by rfl⟩ : syracuseStep 2930735 = 4396103) B4396103
theorem B1953823 : Blo 1953435 1953823 := bstep (se 1 (by rfl) ⟨1465367, by rfl⟩ : syracuseStep 1953823 = 2930735) B2930735
theorem B2930741 : Blo 1953435 2930741 := bbase (se 5 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 2930741 = 274757) (by norm_num)
theorem B1953827 : Blo 1953435 1953827 := bstep (se 1 (by rfl) ⟨1465370, by rfl⟩ : syracuseStep 1953827 = 2930741) B2930741
theorem B4945637 : Blo 1953435 4945637 := bbase (se 4 (by rfl) ⟨463653, by rfl⟩ : syracuseStep 4945637 = 927307) (by norm_num)
theorem B3297091 : Blo 1953435 3297091 := bstep (se 1 (by rfl) ⟨2472818, by rfl⟩ : syracuseStep 3297091 = 4945637) B4945637
theorem B4396121 : Blo 1953435 4396121 := bstep (se 2 (by rfl) ⟨1648545, by rfl⟩ : syracuseStep 4396121 = 3297091) B3297091
theorem B2930747 : Blo 1953435 2930747 := bstep (se 1 (by rfl) ⟨2198060, by rfl⟩ : syracuseStep 2930747 = 4396121) B4396121
theorem B1953831 : Blo 1953435 1953831 := bstep (se 1 (by rfl) ⟨1465373, by rfl⟩ : syracuseStep 1953831 = 2930747) B2930747
theorem B2198065 : Blo 1953435 2198065 := bbase (se 2 (by rfl) ⟨824274, by rfl⟩ : syracuseStep 2198065 = 1648549) (by norm_num)
theorem B2930753 : Blo 1953435 2930753 := bstep (se 2 (by rfl) ⟨1099032, by rfl⟩ : syracuseStep 2930753 = 2198065) B2198065
theorem B1953835 : Blo 1953435 1953835 := bstep (se 1 (by rfl) ⟨1465376, by rfl⟩ : syracuseStep 1953835 = 2930753) B2930753
theorem B6259349 : Blo 1953435 6259349 := bbase (se 6 (by rfl) ⟨146703, by rfl⟩ : syracuseStep 6259349 = 293407) (by norm_num)
theorem B4172899 : Blo 1953435 4172899 := bstep (se 1 (by rfl) ⟨3129674, by rfl⟩ : syracuseStep 4172899 = 6259349) B6259349
theorem B5563865 : Blo 1953435 5563865 := bstep (se 2 (by rfl) ⟨2086449, by rfl⟩ : syracuseStep 5563865 = 4172899) B4172899
theorem B3709243 : Blo 1953435 3709243 := bstep (se 1 (by rfl) ⟨2781932, by rfl⟩ : syracuseStep 3709243 = 5563865) B5563865
theorem B4945657 : Blo 1953435 4945657 := bstep (se 2 (by rfl) ⟨1854621, by rfl⟩ : syracuseStep 4945657 = 3709243) B3709243
theorem B6594209 : Blo 1953435 6594209 := bstep (se 2 (by rfl) ⟨2472828, by rfl⟩ : syracuseStep 6594209 = 4945657) B4945657
theorem B4396139 : Blo 1953435 4396139 := bstep (se 1 (by rfl) ⟨3297104, by rfl⟩ : syracuseStep 4396139 = 6594209) B6594209
theorem B2930759 : Blo 1953435 2930759 := bstep (se 1 (by rfl) ⟨2198069, by rfl⟩ : syracuseStep 2930759 = 4396139) B4396139
theorem B1953839 : Blo 1953435 1953839 := bstep (se 1 (by rfl) ⟨1465379, by rfl⟩ : syracuseStep 1953839 = 2930759) B2930759
theorem B2930765 : Blo 1953435 2930765 := bbase (se 3 (by rfl) ⟨549518, by rfl⟩ : syracuseStep 2930765 = 1099037) (by norm_num)
theorem B1953843 : Blo 1953435 1953843 := bstep (se 1 (by rfl) ⟨1465382, by rfl⟩ : syracuseStep 1953843 = 2930765) B2930765
theorem B4396157 : Blo 1953435 4396157 := bbase (se 3 (by rfl) ⟨824279, by rfl⟩ : syracuseStep 4396157 = 1648559) (by norm_num)
theorem B2930771 : Blo 1953435 2930771 := bstep (se 1 (by rfl) ⟨2198078, by rfl⟩ : syracuseStep 2930771 = 4396157) B4396157
theorem B1953847 : Blo 1953435 1953847 := bstep (se 1 (by rfl) ⟨1465385, by rfl⟩ : syracuseStep 1953847 = 2930771) B2930771
theorem B3297125 : Blo 1953435 3297125 := bbase (se 4 (by rfl) ⟨309105, by rfl⟩ : syracuseStep 3297125 = 618211) (by norm_num)
theorem B2198083 : Blo 1953435 2198083 := bstep (se 1 (by rfl) ⟨1648562, by rfl⟩ : syracuseStep 2198083 = 3297125) B3297125
theorem B2930777 : Blo 1953435 2930777 := bstep (se 2 (by rfl) ⟨1099041, by rfl⟩ : syracuseStep 2930777 = 2198083) B2198083
theorem B1953851 : Blo 1953435 1953851 := bstep (se 1 (by rfl) ⟨1465388, by rfl⟩ : syracuseStep 1953851 = 2930777) B2930777
theorem B4172933 : Blo 1953435 4172933 := bbase (se 4 (by rfl) ⟨391212, by rfl⟩ : syracuseStep 4172933 = 782425) (by norm_num)
theorem B2781955 : Blo 1953435 2781955 := bstep (se 1 (by rfl) ⟨2086466, by rfl⟩ : syracuseStep 2781955 = 4172933) B4172933
theorem B14837093 : Blo 1953435 14837093 := bstep (se 4 (by rfl) ⟨1390977, by rfl⟩ : syracuseStep 14837093 = 2781955) B2781955
theorem B9891395 : Blo 1953435 9891395 := bstep (se 1 (by rfl) ⟨7418546, by rfl⟩ : syracuseStep 9891395 = 14837093) B14837093
theorem B6594263 : Blo 1953435 6594263 := bstep (se 1 (by rfl) ⟨4945697, by rfl⟩ : syracuseStep 6594263 = 9891395) B9891395
theorem B4396175 : Blo 1953435 4396175 := bstep (se 1 (by rfl) ⟨3297131, by rfl⟩ : syracuseStep 4396175 = 6594263) B6594263
theorem B2930783 : Blo 1953435 2930783 := bstep (se 1 (by rfl) ⟨2198087, by rfl⟩ : syracuseStep 2930783 = 4396175) B4396175
theorem B1953855 : Blo 1953435 1953855 := bstep (se 1 (by rfl) ⟨1465391, by rfl⟩ : syracuseStep 1953855 = 2930783) B2930783
theorem B2930789 : Blo 1953435 2930789 := bbase (se 4 (by rfl) ⟨274761, by rfl⟩ : syracuseStep 2930789 = 549523) (by norm_num)
theorem B1953859 : Blo 1953435 1953859 := bstep (se 1 (by rfl) ⟨1465394, by rfl⟩ : syracuseStep 1953859 = 2930789) B2930789
theorem B9389141 : Blo 1953435 9389141 := bbase (se 8 (by rfl) ⟨55014, by rfl⟩ : syracuseStep 9389141 = 110029) (by norm_num)
theorem B6259427 : Blo 1953435 6259427 := bstep (se 1 (by rfl) ⟨4694570, by rfl⟩ : syracuseStep 6259427 = 9389141) B9389141
theorem B4172951 : Blo 1953435 4172951 := bstep (se 1 (by rfl) ⟨3129713, by rfl⟩ : syracuseStep 4172951 = 6259427) B6259427
theorem B2781967 : Blo 1953435 2781967 := bstep (se 1 (by rfl) ⟨2086475, by rfl⟩ : syracuseStep 2781967 = 4172951) B4172951
theorem B3709289 : Blo 1953435 3709289 := bstep (se 2 (by rfl) ⟨1390983, by rfl⟩ : syracuseStep 3709289 = 2781967) B2781967
theorem B2472859 : Blo 1953435 2472859 := bstep (se 1 (by rfl) ⟨1854644, by rfl⟩ : syracuseStep 2472859 = 3709289) B3709289
theorem B3297145 : Blo 1953435 3297145 := bstep (se 2 (by rfl) ⟨1236429, by rfl⟩ : syracuseStep 3297145 = 2472859) B2472859
theorem B4396193 : Blo 1953435 4396193 := bstep (se 2 (by rfl) ⟨1648572, by rfl⟩ : syracuseStep 4396193 = 3297145) B3297145
theorem B2930795 : Blo 1953435 2930795 := bstep (se 1 (by rfl) ⟨2198096, by rfl⟩ : syracuseStep 2930795 = 4396193) B4396193
theorem B1953863 : Blo 1953435 1953863 := bstep (se 1 (by rfl) ⟨1465397, by rfl⟩ : syracuseStep 1953863 = 2930795) B2930795
theorem B2198101 : Blo 1953435 2198101 := bbase (se 8 (by rfl) ⟨12879, by rfl⟩ : syracuseStep 2198101 = 25759) (by norm_num)
theorem B2930801 : Blo 1953435 2930801 := bstep (se 2 (by rfl) ⟨1099050, by rfl⟩ : syracuseStep 2930801 = 2198101) B2198101
theorem B1953867 : Blo 1953435 1953867 := bstep (se 1 (by rfl) ⟨1465400, by rfl⟩ : syracuseStep 1953867 = 2930801) B2930801
theorem B2472869 : Blo 1953435 2472869 := bbase (se 4 (by rfl) ⟨231831, by rfl⟩ : syracuseStep 2472869 = 463663) (by norm_num)
theorem B6594317 : Blo 1953435 6594317 := bstep (se 3 (by rfl) ⟨1236434, by rfl⟩ : syracuseStep 6594317 = 2472869) B2472869
theorem B4396211 : Blo 1953435 4396211 := bstep (se 1 (by rfl) ⟨3297158, by rfl⟩ : syracuseStep 4396211 = 6594317) B6594317
theorem B2930807 : Blo 1953435 2930807 := bstep (se 1 (by rfl) ⟨2198105, by rfl⟩ : syracuseStep 2930807 = 4396211) B4396211
theorem B1953871 : Blo 1953435 1953871 := bstep (se 1 (by rfl) ⟨1465403, by rfl⟩ : syracuseStep 1953871 = 2930807) B2930807
theorem B2930813 : Blo 1953435 2930813 := bbase (se 3 (by rfl) ⟨549527, by rfl⟩ : syracuseStep 2930813 = 1099055) (by norm_num)
theorem B1953875 : Blo 1953435 1953875 := bstep (se 1 (by rfl) ⟨1465406, by rfl⟩ : syracuseStep 1953875 = 2930813) B2930813
theorem B4396229 : Blo 1953435 4396229 := bbase (se 4 (by rfl) ⟨412146, by rfl⟩ : syracuseStep 4396229 = 824293) (by norm_num)
theorem B2930819 : Blo 1953435 2930819 := bstep (se 1 (by rfl) ⟨2198114, by rfl⟩ : syracuseStep 2930819 = 4396229) B4396229
theorem B1953879 : Blo 1953435 1953879 := bstep (se 1 (by rfl) ⟨1465409, by rfl⟩ : syracuseStep 1953879 = 2930819) B2930819
theorem B2347309 : Blo 1953435 2347309 := bbase (se 3 (by rfl) ⟨440120, by rfl⟩ : syracuseStep 2347309 = 880241) (by norm_num)
theorem B12518981 : Blo 1953435 12518981 := bstep (se 4 (by rfl) ⟨1173654, by rfl⟩ : syracuseStep 12518981 = 2347309) B2347309
theorem B8345987 : Blo 1953435 8345987 := bstep (se 1 (by rfl) ⟨6259490, by rfl⟩ : syracuseStep 8345987 = 12518981) B12518981
theorem B5563991 : Blo 1953435 5563991 := bstep (se 1 (by rfl) ⟨4172993, by rfl⟩ : syracuseStep 5563991 = 8345987) B8345987
theorem B3709327 : Blo 1953435 3709327 := bstep (se 1 (by rfl) ⟨2781995, by rfl⟩ : syracuseStep 3709327 = 5563991) B5563991
theorem B4945769 : Blo 1953435 4945769 := bstep (se 2 (by rfl) ⟨1854663, by rfl⟩ : syracuseStep 4945769 = 3709327) B3709327
theorem B3297179 : Blo 1953435 3297179 := bstep (se 1 (by rfl) ⟨2472884, by rfl⟩ : syracuseStep 3297179 = 4945769) B4945769
theorem B2198119 : Blo 1953435 2198119 := bstep (se 1 (by rfl) ⟨1648589, by rfl⟩ : syracuseStep 2198119 = 3297179) B3297179
theorem B2930825 : Blo 1953435 2930825 := bstep (se 2 (by rfl) ⟨1099059, by rfl⟩ : syracuseStep 2930825 = 2198119) B2198119
theorem B1953883 : Blo 1953435 1953883 := bstep (se 1 (by rfl) ⟨1465412, by rfl⟩ : syracuseStep 1953883 = 2930825) B2930825
theorem B9891557 : Blo 1953435 9891557 := bbase (se 4 (by rfl) ⟨927333, by rfl⟩ : syracuseStep 9891557 = 1854667) (by norm_num)
theorem B6594371 : Blo 1953435 6594371 := bstep (se 1 (by rfl) ⟨4945778, by rfl⟩ : syracuseStep 6594371 = 9891557) B9891557
theorem B4396247 : Blo 1953435 4396247 := bstep (se 1 (by rfl) ⟨3297185, by rfl⟩ : syracuseStep 4396247 = 6594371) B6594371
theorem B2930831 : Blo 1953435 2930831 := bstep (se 1 (by rfl) ⟨2198123, by rfl⟩ : syracuseStep 2930831 = 4396247) B4396247
theorem B1953887 : Blo 1953435 1953887 := bstep (se 1 (by rfl) ⟨1465415, by rfl⟩ : syracuseStep 1953887 = 2930831) B2930831
theorem B2930837 : Blo 1953435 2930837 := bbase (se 6 (by rfl) ⟨68691, by rfl⟩ : syracuseStep 2930837 = 137383) (by norm_num)
theorem B1953891 : Blo 1953435 1953891 := bstep (se 1 (by rfl) ⟨1465418, by rfl⟩ : syracuseStep 1953891 = 2930837) B2930837
theorem B8346037 : Blo 1953435 8346037 := bbase (se 5 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 8346037 = 782441) (by norm_num)
theorem B11128049 : Blo 1953435 11128049 := bstep (se 2 (by rfl) ⟨4173018, by rfl⟩ : syracuseStep 11128049 = 8346037) B8346037
theorem B7418699 : Blo 1953435 7418699 := bstep (se 1 (by rfl) ⟨5564024, by rfl⟩ : syracuseStep 7418699 = 11128049) B11128049
theorem B4945799 : Blo 1953435 4945799 := bstep (se 1 (by rfl) ⟨3709349, by rfl⟩ : syracuseStep 4945799 = 7418699) B7418699
theorem B3297199 : Blo 1953435 3297199 := bstep (se 1 (by rfl) ⟨2472899, by rfl⟩ : syracuseStep 3297199 = 4945799) B4945799
theorem B4396265 : Blo 1953435 4396265 := bstep (se 2 (by rfl) ⟨1648599, by rfl⟩ : syracuseStep 4396265 = 3297199) B3297199
theorem B2930843 : Blo 1953435 2930843 := bstep (se 1 (by rfl) ⟨2198132, by rfl⟩ : syracuseStep 2930843 = 4396265) B4396265
theorem B1953895 : Blo 1953435 1953895 := bstep (se 1 (by rfl) ⟨1465421, by rfl⟩ : syracuseStep 1953895 = 2930843) B2930843
theorem B2198137 : Blo 1953435 2198137 := bbase (se 2 (by rfl) ⟨824301, by rfl⟩ : syracuseStep 2198137 = 1648603) (by norm_num)
theorem B2930849 : Blo 1953435 2930849 := bstep (se 2 (by rfl) ⟨1099068, by rfl⟩ : syracuseStep 2930849 = 2198137) B2198137
theorem B1953899 : Blo 1953435 1953899 := bstep (se 1 (by rfl) ⟨1465424, by rfl⟩ : syracuseStep 1953899 = 2930849) B2930849
theorem B2819981 : Blo 1953435 2819981 := bbase (se 3 (by rfl) ⟨528746, by rfl⟩ : syracuseStep 2819981 = 1057493) (by norm_num)
theorem B7519949 : Blo 1953435 7519949 := bstep (se 3 (by rfl) ⟨1409990, by rfl⟩ : syracuseStep 7519949 = 2819981) B2819981
theorem B5013299 : Blo 1953435 5013299 := bstep (se 1 (by rfl) ⟨3759974, by rfl⟩ : syracuseStep 5013299 = 7519949) B7519949
theorem B13368797 : Blo 1953435 13368797 := bstep (se 3 (by rfl) ⟨2506649, by rfl⟩ : syracuseStep 13368797 = 5013299) B5013299
theorem B8912531 : Blo 1953435 8912531 := bstep (se 1 (by rfl) ⟨6684398, by rfl⟩ : syracuseStep 8912531 = 13368797) B13368797
theorem B5941687 : Blo 1953435 5941687 := bstep (se 1 (by rfl) ⟨4456265, by rfl⟩ : syracuseStep 5941687 = 8912531) B8912531
theorem B7922249 : Blo 1953435 7922249 := bstep (se 2 (by rfl) ⟨2970843, by rfl⟩ : syracuseStep 7922249 = 5941687) B5941687
theorem B5281499 : Blo 1953435 5281499 := bstep (se 1 (by rfl) ⟨3961124, by rfl⟩ : syracuseStep 5281499 = 7922249) B7922249
theorem B3520999 : Blo 1953435 3520999 := bstep (se 1 (by rfl) ⟨2640749, by rfl⟩ : syracuseStep 3520999 = 5281499) B5281499
theorem B18778661 : Blo 1953435 18778661 := bstep (se 4 (by rfl) ⟨1760499, by rfl⟩ : syracuseStep 18778661 = 3520999) B3520999
theorem B12519107 : Blo 1953435 12519107 := bstep (se 1 (by rfl) ⟨9389330, by rfl⟩ : syracuseStep 12519107 = 18778661) B18778661
theorem B8346071 : Blo 1953435 8346071 := bstep (se 1 (by rfl) ⟨6259553, by rfl⟩ : syracuseStep 8346071 = 12519107) B12519107
theorem B5564047 : Blo 1953435 5564047 := bstep (se 1 (by rfl) ⟨4173035, by rfl⟩ : syracuseStep 5564047 = 8346071) B8346071
theorem B7418729 : Blo 1953435 7418729 := bstep (se 2 (by rfl) ⟨2782023, by rfl⟩ : syracuseStep 7418729 = 5564047) B5564047
theorem B4945819 : Blo 1953435 4945819 := bstep (se 1 (by rfl) ⟨3709364, by rfl⟩ : syracuseStep 4945819 = 7418729) B7418729
theorem B6594425 : Blo 1953435 6594425 := bstep (se 2 (by rfl) ⟨2472909, by rfl⟩ : syracuseStep 6594425 = 4945819) B4945819
theorem B4396283 : Blo 1953435 4396283 := bstep (se 1 (by rfl) ⟨3297212, by rfl⟩ : syracuseStep 4396283 = 6594425) B6594425
theorem B2930855 : Blo 1953435 2930855 := bstep (se 1 (by rfl) ⟨2198141, by rfl⟩ : syracuseStep 2930855 = 4396283) B4396283
theorem B1953903 : Blo 1953435 1953903 := bstep (se 1 (by rfl) ⟨1465427, by rfl⟩ : syracuseStep 1953903 = 2930855) B2930855
theorem B2930861 : Blo 1953435 2930861 := bbase (se 3 (by rfl) ⟨549536, by rfl⟩ : syracuseStep 2930861 = 1099073) (by norm_num)
theorem B1953907 : Blo 1953435 1953907 := bstep (se 1 (by rfl) ⟨1465430, by rfl⟩ : syracuseStep 1953907 = 2930861) B2930861
theorem B4396301 : Blo 1953435 4396301 := bbase (se 3 (by rfl) ⟨824306, by rfl⟩ : syracuseStep 4396301 = 1648613) (by norm_num)
theorem B2930867 : Blo 1953435 2930867 := bstep (se 1 (by rfl) ⟨2198150, by rfl⟩ : syracuseStep 2930867 = 4396301) B4396301
theorem B1953911 : Blo 1953435 1953911 := bstep (se 1 (by rfl) ⟨1465433, by rfl⟩ : syracuseStep 1953911 = 2930867) B2930867
theorem B2472925 : Blo 1953435 2472925 := bbase (se 3 (by rfl) ⟨463673, by rfl⟩ : syracuseStep 2472925 = 927347) (by norm_num)
theorem B3297233 : Blo 1953435 3297233 := bstep (se 2 (by rfl) ⟨1236462, by rfl⟩ : syracuseStep 3297233 = 2472925) B2472925
theorem B2198155 : Blo 1953435 2198155 := bstep (se 1 (by rfl) ⟨1648616, by rfl⟩ : syracuseStep 2198155 = 3297233) B3297233
theorem B2930873 : Blo 1953435 2930873 := bstep (se 2 (by rfl) ⟨1099077, by rfl⟩ : syracuseStep 2930873 = 2198155) B2198155
theorem B1953915 : Blo 1953435 1953915 := bstep (se 1 (by rfl) ⟨1465436, by rfl⟩ : syracuseStep 1953915 = 2930873) B2930873
theorem B16692277 : Blo 1953435 16692277 := bbase (se 5 (by rfl) ⟨782450, by rfl⟩ : syracuseStep 16692277 = 1564901) (by norm_num)
theorem B22256369 : Blo 1953435 22256369 := bstep (se 2 (by rfl) ⟨8346138, by rfl⟩ : syracuseStep 22256369 = 16692277) B16692277
theorem B14837579 : Blo 1953435 14837579 := bstep (se 1 (by rfl) ⟨11128184, by rfl⟩ : syracuseStep 14837579 = 22256369) B22256369
theorem B9891719 : Blo 1953435 9891719 := bstep (se 1 (by rfl) ⟨7418789, by rfl⟩ : syracuseStep 9891719 = 14837579) B14837579
theorem B6594479 : Blo 1953435 6594479 := bstep (se 1 (by rfl) ⟨4945859, by rfl⟩ : syracuseStep 6594479 = 9891719) B9891719
theorem B4396319 : Blo 1953435 4396319 := bstep (se 1 (by rfl) ⟨3297239, by rfl⟩ : syracuseStep 4396319 = 6594479) B6594479
theorem B2930879 : Blo 1953435 2930879 := bstep (se 1 (by rfl) ⟨2198159, by rfl⟩ : syracuseStep 2930879 = 4396319) B4396319
theorem B1953919 : Blo 1953435 1953919 := bstep (se 1 (by rfl) ⟨1465439, by rfl⟩ : syracuseStep 1953919 = 2930879) B2930879
theorem B2930885 : Blo 1953435 2930885 := bbase (se 4 (by rfl) ⟨274770, by rfl⟩ : syracuseStep 2930885 = 549541) (by norm_num)
theorem B1953923 : Blo 1953435 1953923 := bstep (se 1 (by rfl) ⟨1465442, by rfl⟩ : syracuseStep 1953923 = 2930885) B2930885
theorem B3297253 : Blo 1953435 3297253 := bbase (se 4 (by rfl) ⟨309117, by rfl⟩ : syracuseStep 3297253 = 618235) (by norm_num)
theorem B4396337 : Blo 1953435 4396337 := bstep (se 2 (by rfl) ⟨1648626, by rfl⟩ : syracuseStep 4396337 = 3297253) B3297253
theorem B2930891 : Blo 1953435 2930891 := bstep (se 1 (by rfl) ⟨2198168, by rfl⟩ : syracuseStep 2930891 = 4396337) B4396337
theorem B1953927 : Blo 1953435 1953927 := bstep (se 1 (by rfl) ⟨1465445, by rfl⟩ : syracuseStep 1953927 = 2930891) B2930891
theorem B2198173 : Blo 1953435 2198173 := bbase (se 3 (by rfl) ⟨412157, by rfl⟩ : syracuseStep 2198173 = 824315) (by norm_num)
theorem B2930897 : Blo 1953435 2930897 := bstep (se 2 (by rfl) ⟨1099086, by rfl⟩ : syracuseStep 2930897 = 2198173) B2198173
theorem B1953931 : Blo 1953435 1953931 := bstep (se 1 (by rfl) ⟨1465448, by rfl⟩ : syracuseStep 1953931 = 2930897) B2930897
theorem B6594533 : Blo 1953435 6594533 := bbase (se 4 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 6594533 = 1236475) (by norm_num)
theorem B4396355 : Blo 1953435 4396355 := bstep (se 1 (by rfl) ⟨3297266, by rfl⟩ : syracuseStep 4396355 = 6594533) B6594533
theorem B2930903 : Blo 1953435 2930903 := bstep (se 1 (by rfl) ⟨2198177, by rfl⟩ : syracuseStep 2930903 = 4396355) B4396355
theorem B1953935 : Blo 1953435 1953935 := bstep (se 1 (by rfl) ⟨1465451, by rfl⟩ : syracuseStep 1953935 = 2930903) B2930903
theorem B2930909 : Blo 1953435 2930909 := bbase (se 3 (by rfl) ⟨549545, by rfl⟩ : syracuseStep 2930909 = 1099091) (by norm_num)
theorem B1953939 : Blo 1953435 1953939 := bstep (se 1 (by rfl) ⟨1465454, by rfl⟩ : syracuseStep 1953939 = 2930909) B2930909
theorem B4396373 : Blo 1953435 4396373 := bbase (se 14 (by rfl) ⟨402, by rfl⟩ : syracuseStep 4396373 = 805) (by norm_num)
theorem B2930915 : Blo 1953435 2930915 := bstep (se 1 (by rfl) ⟨2198186, by rfl⟩ : syracuseStep 2930915 = 4396373) B4396373
theorem B1953943 : Blo 1953435 1953943 := bstep (se 1 (by rfl) ⟨1465457, by rfl⟩ : syracuseStep 1953943 = 2930915) B2930915
theorem B2086565 : Blo 1953435 2086565 := bbase (se 4 (by rfl) ⟨195615, by rfl⟩ : syracuseStep 2086565 = 391231) (by norm_num)
theorem B5564173 : Blo 1953435 5564173 := bstep (se 3 (by rfl) ⟨1043282, by rfl⟩ : syracuseStep 5564173 = 2086565) B2086565
theorem B7418897 : Blo 1953435 7418897 := bstep (se 2 (by rfl) ⟨2782086, by rfl⟩ : syracuseStep 7418897 = 5564173) B5564173
theorem B4945931 : Blo 1953435 4945931 := bstep (se 1 (by rfl) ⟨3709448, by rfl⟩ : syracuseStep 4945931 = 7418897) B7418897
theorem B3297287 : Blo 1953435 3297287 := bstep (se 1 (by rfl) ⟨2472965, by rfl⟩ : syracuseStep 3297287 = 4945931) B4945931
theorem B2198191 : Blo 1953435 2198191 := bstep (se 1 (by rfl) ⟨1648643, by rfl⟩ : syracuseStep 2198191 = 3297287) B3297287
theorem B2930921 : Blo 1953435 2930921 := bstep (se 2 (by rfl) ⟨1099095, by rfl⟩ : syracuseStep 2930921 = 2198191) B2198191
theorem B1953947 : Blo 1953435 1953947 := bstep (se 1 (by rfl) ⟨1465460, by rfl⟩ : syracuseStep 1953947 = 2930921) B2930921
theorem B2115037 : Blo 1953435 2115037 := bbase (se 3 (by rfl) ⟨396569, by rfl⟩ : syracuseStep 2115037 = 793139) (by norm_num)
theorem B2820049 : Blo 1953435 2820049 := bstep (se 2 (by rfl) ⟨1057518, by rfl⟩ : syracuseStep 2820049 = 2115037) B2115037
theorem B15040261 : Blo 1953435 15040261 := bstep (se 4 (by rfl) ⟨1410024, by rfl⟩ : syracuseStep 15040261 = 2820049) B2820049
theorem B80214725 : Blo 1953435 80214725 := bstep (se 4 (by rfl) ⟨7520130, by rfl⟩ : syracuseStep 80214725 = 15040261) B15040261
theorem B53476483 : Blo 1953435 53476483 := bstep (se 1 (by rfl) ⟨40107362, by rfl⟩ : syracuseStep 53476483 = 80214725) B80214725
theorem B71301977 : Blo 1953435 71301977 := bstep (se 2 (by rfl) ⟨26738241, by rfl⟩ : syracuseStep 71301977 = 53476483) B53476483
theorem B47534651 : Blo 1953435 47534651 := bstep (se 1 (by rfl) ⟨35650988, by rfl⟩ : syracuseStep 47534651 = 71301977) B71301977
theorem B31689767 : Blo 1953435 31689767 := bstep (se 1 (by rfl) ⟨23767325, by rfl⟩ : syracuseStep 31689767 = 47534651) B47534651
theorem B21126511 : Blo 1953435 21126511 := bstep (se 1 (by rfl) ⟨15844883, by rfl⟩ : syracuseStep 21126511 = 31689767) B31689767
theorem B28168681 : Blo 1953435 28168681 := bstep (se 2 (by rfl) ⟨10563255, by rfl⟩ : syracuseStep 28168681 = 21126511) B21126511
theorem B37558241 : Blo 1953435 37558241 := bstep (se 2 (by rfl) ⟨14084340, by rfl⟩ : syracuseStep 37558241 = 28168681) B28168681
theorem B25038827 : Blo 1953435 25038827 := bstep (se 1 (by rfl) ⟨18779120, by rfl⟩ : syracuseStep 25038827 = 37558241) B37558241
theorem B16692551 : Blo 1953435 16692551 := bstep (se 1 (by rfl) ⟨12519413, by rfl⟩ : syracuseStep 16692551 = 25038827) B25038827
theorem B11128367 : Blo 1953435 11128367 := bstep (se 1 (by rfl) ⟨8346275, by rfl⟩ : syracuseStep 11128367 = 16692551) B16692551
theorem B7418911 : Blo 1953435 7418911 := bstep (se 1 (by rfl) ⟨5564183, by rfl⟩ : syracuseStep 7418911 = 11128367) B11128367
theorem B9891881 : Blo 1953435 9891881 := bstep (se 2 (by rfl) ⟨3709455, by rfl⟩ : syracuseStep 9891881 = 7418911) B7418911
theorem B6594587 : Blo 1953435 6594587 := bstep (se 1 (by rfl) ⟨4945940, by rfl⟩ : syracuseStep 6594587 = 9891881) B9891881
theorem B4396391 : Blo 1953435 4396391 := bstep (se 1 (by rfl) ⟨3297293, by rfl⟩ : syracuseStep 4396391 = 6594587) B6594587
theorem B2930927 : Blo 1953435 2930927 := bstep (se 1 (by rfl) ⟨2198195, by rfl⟩ : syracuseStep 2930927 = 4396391) B4396391
theorem B1953951 : Blo 1953435 1953951 := bstep (se 1 (by rfl) ⟨1465463, by rfl⟩ : syracuseStep 1953951 = 2930927) B2930927
theorem B2930933 : Blo 1953435 2930933 := bbase (se 5 (by rfl) ⟨137387, by rfl⟩ : syracuseStep 2930933 = 274775) (by norm_num)
theorem B1953955 : Blo 1953435 1953955 := bstep (se 1 (by rfl) ⟨1465466, by rfl⟩ : syracuseStep 1953955 = 2930933) B2930933
theorem B2228197 : Blo 1953435 2228197 := bbase (se 4 (by rfl) ⟨208893, by rfl⟩ : syracuseStep 2228197 = 417787) (by norm_num)
theorem B2970929 : Blo 1953435 2970929 := bstep (se 2 (by rfl) ⟨1114098, by rfl⟩ : syracuseStep 2970929 = 2228197) B2228197
theorem B1980619 : Blo 1953435 1980619 := bstep (se 1 (by rfl) ⟨1485464, by rfl⟩ : syracuseStep 1980619 = 2970929) B2970929
theorem B10563301 : Blo 1953435 10563301 := bstep (se 4 (by rfl) ⟨990309, by rfl⟩ : syracuseStep 10563301 = 1980619) B1980619
theorem B14084401 : Blo 1953435 14084401 := bstep (se 2 (by rfl) ⟨5281650, by rfl⟩ : syracuseStep 14084401 = 10563301) B10563301
theorem B18779201 : Blo 1953435 18779201 := bstep (se 2 (by rfl) ⟨7042200, by rfl⟩ : syracuseStep 18779201 = 14084401) B14084401
theorem B12519467 : Blo 1953435 12519467 := bstep (se 1 (by rfl) ⟨9389600, by rfl⟩ : syracuseStep 12519467 = 18779201) B18779201
theorem B8346311 : Blo 1953435 8346311 := bstep (se 1 (by rfl) ⟨6259733, by rfl⟩ : syracuseStep 8346311 = 12519467) B12519467
theorem B5564207 : Blo 1953435 5564207 := bstep (se 1 (by rfl) ⟨4173155, by rfl⟩ : syracuseStep 5564207 = 8346311) B8346311
theorem B3709471 : Blo 1953435 3709471 := bstep (se 1 (by rfl) ⟨2782103, by rfl⟩ : syracuseStep 3709471 = 5564207) B5564207
theorem B4945961 : Blo 1953435 4945961 := bstep (se 2 (by rfl) ⟨1854735, by rfl⟩ : syracuseStep 4945961 = 3709471) B3709471
theorem B3297307 : Blo 1953435 3297307 := bstep (se 1 (by rfl) ⟨2472980, by rfl⟩ : syracuseStep 3297307 = 4945961) B4945961
theorem B4396409 : Blo 1953435 4396409 := bstep (se 2 (by rfl) ⟨1648653, by rfl⟩ : syracuseStep 4396409 = 3297307) B3297307
theorem B2930939 : Blo 1953435 2930939 := bstep (se 1 (by rfl) ⟨2198204, by rfl⟩ : syracuseStep 2930939 = 4396409) B4396409
theorem B1953959 : Blo 1953435 1953959 := bstep (se 1 (by rfl) ⟨1465469, by rfl⟩ : syracuseStep 1953959 = 2930939) B2930939
theorem B2198209 : Blo 1953435 2198209 := bbase (se 2 (by rfl) ⟨824328, by rfl⟩ : syracuseStep 2198209 = 1648657) (by norm_num)
theorem B2930945 : Blo 1953435 2930945 := bstep (se 2 (by rfl) ⟨1099104, by rfl⟩ : syracuseStep 2930945 = 2198209) B2198209
theorem B1953963 : Blo 1953435 1953963 := bstep (se 1 (by rfl) ⟨1465472, by rfl⟩ : syracuseStep 1953963 = 2930945) B2930945
theorem B4945981 : Blo 1953435 4945981 := bbase (se 3 (by rfl) ⟨927371, by rfl⟩ : syracuseStep 4945981 = 1854743) (by norm_num)
theorem B6594641 : Blo 1953435 6594641 := bstep (se 2 (by rfl) ⟨2472990, by rfl⟩ : syracuseStep 6594641 = 4945981) B4945981
theorem B4396427 : Blo 1953435 4396427 := bstep (se 1 (by rfl) ⟨3297320, by rfl⟩ : syracuseStep 4396427 = 6594641) B6594641
theorem B2930951 : Blo 1953435 2930951 := bstep (se 1 (by rfl) ⟨2198213, by rfl⟩ : syracuseStep 2930951 = 4396427) B4396427
theorem B1953967 : Blo 1953435 1953967 := bstep (se 1 (by rfl) ⟨1465475, by rfl⟩ : syracuseStep 1953967 = 2930951) B2930951
theorem B2930957 : Blo 1953435 2930957 := bbase (se 3 (by rfl) ⟨549554, by rfl⟩ : syracuseStep 2930957 = 1099109) (by norm_num)
theorem B1953971 : Blo 1953435 1953971 := bstep (se 1 (by rfl) ⟨1465478, by rfl⟩ : syracuseStep 1953971 = 2930957) B2930957
theorem B4396445 : Blo 1953435 4396445 := bbase (se 3 (by rfl) ⟨824333, by rfl⟩ : syracuseStep 4396445 = 1648667) (by norm_num)
theorem B2930963 : Blo 1953435 2930963 := bstep (se 1 (by rfl) ⟨2198222, by rfl⟩ : syracuseStep 2930963 = 4396445) B4396445
theorem B1953975 : Blo 1953435 1953975 := bstep (se 1 (by rfl) ⟨1465481, by rfl⟩ : syracuseStep 1953975 = 2930963) B2930963
theorem B3297341 : Blo 1953435 3297341 := bbase (se 3 (by rfl) ⟨618251, by rfl⟩ : syracuseStep 3297341 = 1236503) (by norm_num)
theorem B2198227 : Blo 1953435 2198227 := bstep (se 1 (by rfl) ⟨1648670, by rfl⟩ : syracuseStep 2198227 = 3297341) B3297341
theorem B2930969 : Blo 1953435 2930969 := bstep (se 2 (by rfl) ⟨1099113, by rfl⟩ : syracuseStep 2930969 = 2198227) B2198227
theorem B1953979 : Blo 1953435 1953979 := bstep (se 1 (by rfl) ⟨1465484, by rfl⟩ : syracuseStep 1953979 = 2930969) B2930969
theorem B2347429 : Blo 1953435 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B3129905 : Blo 1953435 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B2086603 : Blo 1953435 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B11128549 : Blo 1953435 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B14838065 : Blo 1953435 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B9892043 : Blo 1953435 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B6594695 : Blo 1953435 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B4396463 : Blo 1953435 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B2930975 : Blo 1953435 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B1953983 : Blo 1953435 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B2930981 : Blo 1953435 2930981 := bbase (se 4 (by rfl) ⟨274779, by rfl⟩ : syracuseStep 2930981 = 549559) (by norm_num)
theorem B1953987 : Blo 1953435 1953987 := bstep (se 1 (by rfl) ⟨1465490, by rfl⟩ : syracuseStep 1953987 = 2930981) B2930981
theorem B2473021 : Blo 1953435 2473021 := bbase (se 3 (by rfl) ⟨463691, by rfl⟩ : syracuseStep 2473021 = 927383) (by norm_num)
theorem B3297361 : Blo 1953435 3297361 := bstep (se 2 (by rfl) ⟨1236510, by rfl⟩ : syracuseStep 3297361 = 2473021) B2473021
theorem B4396481 : Blo 1953435 4396481 := bstep (se 2 (by rfl) ⟨1648680, by rfl⟩ : syracuseStep 4396481 = 3297361) B3297361
theorem B2930987 : Blo 1953435 2930987 := bstep (se 1 (by rfl) ⟨2198240, by rfl⟩ : syracuseStep 2930987 = 4396481) B4396481
theorem B1953991 : Blo 1953435 1953991 := bstep (se 1 (by rfl) ⟨1465493, by rfl⟩ : syracuseStep 1953991 = 2930987) B2930987
theorem B2198245 : Blo 1953435 2198245 := bbase (se 4 (by rfl) ⟨206085, by rfl⟩ : syracuseStep 2198245 = 412171) (by norm_num)
theorem B2930993 : Blo 1953435 2930993 := bstep (se 2 (by rfl) ⟨1099122, by rfl⟩ : syracuseStep 2930993 = 2198245) B2198245
theorem B1953995 : Blo 1953435 1953995 := bstep (se 1 (by rfl) ⟨1465496, by rfl⟩ : syracuseStep 1953995 = 2930993) B2930993
theorem B3521173 : Blo 1953435 3521173 := bbase (se 6 (by rfl) ⟨82527, by rfl⟩ : syracuseStep 3521173 = 165055) (by norm_num)
theorem B4694897 : Blo 1953435 4694897 := bstep (se 2 (by rfl) ⟨1760586, by rfl⟩ : syracuseStep 4694897 = 3521173) B3521173
theorem B3129931 : Blo 1953435 3129931 := bstep (se 1 (by rfl) ⟨2347448, by rfl⟩ : syracuseStep 3129931 = 4694897) B4694897
theorem B4173241 : Blo 1953435 4173241 := bstep (se 2 (by rfl) ⟨1564965, by rfl⟩ : syracuseStep 4173241 = 3129931) B3129931
theorem B5564321 : Blo 1953435 5564321 := bstep (se 2 (by rfl) ⟨2086620, by rfl⟩ : syracuseStep 5564321 = 4173241) B4173241
theorem B3709547 : Blo 1953435 3709547 := bstep (se 1 (by rfl) ⟨2782160, by rfl⟩ : syracuseStep 3709547 = 5564321) B5564321
theorem B2473031 : Blo 1953435 2473031 := bstep (se 1 (by rfl) ⟨1854773, by rfl⟩ : syracuseStep 2473031 = 3709547) B3709547
theorem B6594749 : Blo 1953435 6594749 := bstep (se 3 (by rfl) ⟨1236515, by rfl⟩ : syracuseStep 6594749 = 2473031) B2473031
theorem B4396499 : Blo 1953435 4396499 := bstep (se 1 (by rfl) ⟨3297374, by rfl⟩ : syracuseStep 4396499 = 6594749) B6594749
theorem B2930999 : Blo 1953435 2930999 := bstep (se 1 (by rfl) ⟨2198249, by rfl⟩ : syracuseStep 2930999 = 4396499) B4396499
theorem B1953999 : Blo 1953435 1953999 := bstep (se 1 (by rfl) ⟨1465499, by rfl⟩ : syracuseStep 1953999 = 2930999) B2930999
theorem B2931005 : Blo 1953435 2931005 := bbase (se 3 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 2931005 = 1099127) (by norm_num)
theorem B1954003 : Blo 1953435 1954003 := bstep (se 1 (by rfl) ⟨1465502, by rfl⟩ : syracuseStep 1954003 = 2931005) B2931005
theorem B4396517 : Blo 1953435 4396517 := bbase (se 4 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 4396517 = 824347) (by norm_num)
theorem B2931011 : Blo 1953435 2931011 := bstep (se 1 (by rfl) ⟨2198258, by rfl⟩ : syracuseStep 2931011 = 4396517) B4396517
theorem B1954007 : Blo 1953435 1954007 := bstep (se 1 (by rfl) ⟨1465505, by rfl⟩ : syracuseStep 1954007 = 2931011) B2931011
theorem B4946093 : Blo 1953435 4946093 := bbase (se 3 (by rfl) ⟨927392, by rfl⟩ : syracuseStep 4946093 = 1854785) (by norm_num)
theorem B3297395 : Blo 1953435 3297395 := bstep (se 1 (by rfl) ⟨2473046, by rfl⟩ : syracuseStep 3297395 = 4946093) B4946093
theorem B2198263 : Blo 1953435 2198263 := bstep (se 1 (by rfl) ⟨1648697, by rfl⟩ : syracuseStep 2198263 = 3297395) B3297395
theorem B2931017 : Blo 1953435 2931017 := bstep (se 2 (by rfl) ⟨1099131, by rfl⟩ : syracuseStep 2931017 = 2198263) B2198263
theorem B1954011 : Blo 1953435 1954011 := bstep (se 1 (by rfl) ⟨1465508, by rfl⟩ : syracuseStep 1954011 = 2931017) B2931017
theorem B10563605 : Blo 1953435 10563605 := bbase (se 6 (by rfl) ⟨247584, by rfl⟩ : syracuseStep 10563605 = 495169) (by norm_num)
theorem B7042403 : Blo 1953435 7042403 := bstep (se 1 (by rfl) ⟨5281802, by rfl⟩ : syracuseStep 7042403 = 10563605) B10563605
theorem B4694935 : Blo 1953435 4694935 := bstep (se 1 (by rfl) ⟨3521201, by rfl⟩ : syracuseStep 4694935 = 7042403) B7042403
theorem B6259913 : Blo 1953435 6259913 := bstep (se 2 (by rfl) ⟨2347467, by rfl⟩ : syracuseStep 6259913 = 4694935) B4694935
theorem B4173275 : Blo 1953435 4173275 := bstep (se 1 (by rfl) ⟨3129956, by rfl⟩ : syracuseStep 4173275 = 6259913) B6259913
theorem B2782183 : Blo 1953435 2782183 := bstep (se 1 (by rfl) ⟨2086637, by rfl⟩ : syracuseStep 2782183 = 4173275) B4173275
theorem B3709577 : Blo 1953435 3709577 := bstep (se 2 (by rfl) ⟨1391091, by rfl⟩ : syracuseStep 3709577 = 2782183) B2782183
theorem B9892205 : Blo 1953435 9892205 := bstep (se 3 (by rfl) ⟨1854788, by rfl⟩ : syracuseStep 9892205 = 3709577) B3709577
theorem B6594803 : Blo 1953435 6594803 := bstep (se 1 (by rfl) ⟨4946102, by rfl⟩ : syracuseStep 6594803 = 9892205) B9892205
theorem B4396535 : Blo 1953435 4396535 := bstep (se 1 (by rfl) ⟨3297401, by rfl⟩ : syracuseStep 4396535 = 6594803) B6594803
theorem B2931023 : Blo 1953435 2931023 := bstep (se 1 (by rfl) ⟨2198267, by rfl⟩ : syracuseStep 2931023 = 4396535) B4396535
theorem B1954015 : Blo 1953435 1954015 := bstep (se 1 (by rfl) ⟨1465511, by rfl⟩ : syracuseStep 1954015 = 2931023) B2931023
theorem B2931029 : Blo 1953435 2931029 := bbase (se 10 (by rfl) ⟨4293, by rfl⟩ : syracuseStep 2931029 = 8587) (by norm_num)
theorem B1954019 : Blo 1953435 1954019 := bstep (se 1 (by rfl) ⟨1465514, by rfl⟩ : syracuseStep 1954019 = 2931029) B2931029
theorem B5564389 : Blo 1953435 5564389 := bbase (se 4 (by rfl) ⟨521661, by rfl⟩ : syracuseStep 5564389 = 1043323) (by norm_num)
theorem B7419185 : Blo 1953435 7419185 := bstep (se 2 (by rfl) ⟨2782194, by rfl⟩ : syracuseStep 7419185 = 5564389) B5564389
theorem B4946123 : Blo 1953435 4946123 := bstep (se 1 (by rfl) ⟨3709592, by rfl⟩ : syracuseStep 4946123 = 7419185) B7419185
theorem B3297415 : Blo 1953435 3297415 := bstep (se 1 (by rfl) ⟨2473061, by rfl⟩ : syracuseStep 3297415 = 4946123) B4946123
theorem B4396553 : Blo 1953435 4396553 := bstep (se 2 (by rfl) ⟨1648707, by rfl⟩ : syracuseStep 4396553 = 3297415) B3297415
theorem B2931035 : Blo 1953435 2931035 := bstep (se 1 (by rfl) ⟨2198276, by rfl⟩ : syracuseStep 2931035 = 4396553) B4396553
theorem B1954023 : Blo 1953435 1954023 := bstep (se 1 (by rfl) ⟨1465517, by rfl⟩ : syracuseStep 1954023 = 2931035) B2931035
theorem B2198281 : Blo 1953435 2198281 := bbase (se 2 (by rfl) ⟨824355, by rfl⟩ : syracuseStep 2198281 = 1648711) (by norm_num)
theorem B2931041 : Blo 1953435 2931041 := bstep (se 2 (by rfl) ⟨1099140, by rfl⟩ : syracuseStep 2931041 = 2198281) B2198281
theorem B1954027 : Blo 1953435 1954027 := bstep (se 1 (by rfl) ⟨1465520, by rfl⟩ : syracuseStep 1954027 = 2931041) B2931041
theorem B10027253 : Blo 1953435 10027253 := bbase (se 5 (by rfl) ⟨470027, by rfl⟩ : syracuseStep 10027253 = 940055) (by norm_num)
theorem B26739341 : Blo 1953435 26739341 := bstep (se 3 (by rfl) ⟨5013626, by rfl⟩ : syracuseStep 26739341 = 10027253) B10027253
theorem B17826227 : Blo 1953435 17826227 := bstep (se 1 (by rfl) ⟨13369670, by rfl⟩ : syracuseStep 17826227 = 26739341) B26739341
theorem B11884151 : Blo 1953435 11884151 := bstep (se 1 (by rfl) ⟨8913113, by rfl⟩ : syracuseStep 11884151 = 17826227) B17826227
theorem B7922767 : Blo 1953435 7922767 := bstep (se 1 (by rfl) ⟨5942075, by rfl⟩ : syracuseStep 7922767 = 11884151) B11884151
theorem B10563689 : Blo 1953435 10563689 := bstep (se 2 (by rfl) ⟨3961383, by rfl⟩ : syracuseStep 10563689 = 7922767) B7922767
theorem B7042459 : Blo 1953435 7042459 := bstep (se 1 (by rfl) ⟨5281844, by rfl⟩ : syracuseStep 7042459 = 10563689) B10563689
theorem B9389945 : Blo 1953435 9389945 := bstep (se 2 (by rfl) ⟨3521229, by rfl⟩ : syracuseStep 9389945 = 7042459) B7042459
theorem B25039853 : Blo 1953435 25039853 := bstep (se 3 (by rfl) ⟨4694972, by rfl⟩ : syracuseStep 25039853 = 9389945) B9389945
theorem B16693235 : Blo 1953435 16693235 := bstep (se 1 (by rfl) ⟨12519926, by rfl⟩ : syracuseStep 16693235 = 25039853) B25039853
theorem B11128823 : Blo 1953435 11128823 := bstep (se 1 (by rfl) ⟨8346617, by rfl⟩ : syracuseStep 11128823 = 16693235) B16693235
theorem B7419215 : Blo 1953435 7419215 := bstep (se 1 (by rfl) ⟨5564411, by rfl⟩ : syracuseStep 7419215 = 11128823) B11128823
theorem B4946143 : Blo 1953435 4946143 := bstep (se 1 (by rfl) ⟨3709607, by rfl⟩ : syracuseStep 4946143 = 7419215) B7419215
theorem B6594857 : Blo 1953435 6594857 := bstep (se 2 (by rfl) ⟨2473071, by rfl⟩ : syracuseStep 6594857 = 4946143) B4946143
theorem B4396571 : Blo 1953435 4396571 := bstep (se 1 (by rfl) ⟨3297428, by rfl⟩ : syracuseStep 4396571 = 6594857) B6594857
theorem B2931047 : Blo 1953435 2931047 := bstep (se 1 (by rfl) ⟨2198285, by rfl⟩ : syracuseStep 2931047 = 4396571) B4396571
theorem B1954031 : Blo 1953435 1954031 := bstep (se 1 (by rfl) ⟨1465523, by rfl⟩ : syracuseStep 1954031 = 2931047) B2931047
theorem B2931053 : Blo 1953435 2931053 := bbase (se 3 (by rfl) ⟨549572, by rfl⟩ : syracuseStep 2931053 = 1099145) (by norm_num)
theorem B1954035 : Blo 1953435 1954035 := bstep (se 1 (by rfl) ⟨1465526, by rfl⟩ : syracuseStep 1954035 = 2931053) B2931053
theorem B4396589 : Blo 1953435 4396589 := bbase (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) (by norm_num)
theorem B2931059 : Blo 1953435 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B1954039 : Blo 1953435 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B3811549 : Blo 1953435 3811549 := bbase (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) (by norm_num)
theorem B5082065 : Blo 1953435 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B3388043 : Blo 1953435 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B2258695 : Blo 1953435 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B12046373 : Blo 1953435 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B8030915 : Blo 1953435 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B5353943 : Blo 1953435 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B14277181 : Blo 1953435 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B19036241 : Blo 1953435 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B12690827 : Blo 1953435 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B8460551 : Blo 1953435 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B5640367 : Blo 1953435 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B7520489 : Blo 1953435 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B5013659 : Blo 1953435 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B3342439 : Blo 1953435 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B4456585 : Blo 1953435 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B23768453 : Blo 1953435 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B15845635 : Blo 1953435 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B21127513 : Blo 1953435 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B28170017 : Blo 1953435 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B18780011 : Blo 1953435 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B12520007 : Blo 1953435 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B8346671 : Blo 1953435 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B5564447 : Blo 1953435 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B3709631 : Blo 1953435 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B2473087 : Blo 1953435 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B3297449 : Blo 1953435 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B2198299 : Blo 1953435 2198299 := bstep (se 1 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 2198299 = 3297449) B3297449
theorem B2931065 : Blo 1953435 2931065 := bstep (se 2 (by rfl) ⟨1099149, by rfl⟩ : syracuseStep 2931065 = 2198299) B2198299
theorem B1954043 : Blo 1953435 1954043 := bstep (se 1 (by rfl) ⟨1465532, by rfl⟩ : syracuseStep 1954043 = 2931065) B2931065
theorem B7042517 : Blo 1953435 7042517 := bbase (se 7 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 7042517 = 165059) (by norm_num)
theorem B4695011 : Blo 1953435 4695011 := bstep (se 1 (by rfl) ⟨3521258, by rfl⟩ : syracuseStep 4695011 = 7042517) B7042517
theorem B3130007 : Blo 1953435 3130007 := bstep (se 1 (by rfl) ⟨2347505, by rfl⟩ : syracuseStep 3130007 = 4695011) B4695011
theorem B33386741 : Blo 1953435 33386741 := bstep (se 5 (by rfl) ⟨1565003, by rfl⟩ : syracuseStep 33386741 = 3130007) B3130007
theorem B22257827 : Blo 1953435 22257827 := bstep (se 1 (by rfl) ⟨16693370, by rfl⟩ : syracuseStep 22257827 = 33386741) B33386741
theorem B14838551 : Blo 1953435 14838551 := bstep (se 1 (by rfl) ⟨11128913, by rfl⟩ : syracuseStep 14838551 = 22257827) B22257827
theorem B9892367 : Blo 1953435 9892367 := bstep (se 1 (by rfl) ⟨7419275, by rfl⟩ : syracuseStep 9892367 = 14838551) B14838551
theorem B6594911 : Blo 1953435 6594911 := bstep (se 1 (by rfl) ⟨4946183, by rfl⟩ : syracuseStep 6594911 = 9892367) B9892367
theorem B4396607 : Blo 1953435 4396607 := bstep (se 1 (by rfl) ⟨3297455, by rfl⟩ : syracuseStep 4396607 = 6594911) B6594911
theorem B2931071 : Blo 1953435 2931071 := bstep (se 1 (by rfl) ⟨2198303, by rfl⟩ : syracuseStep 2931071 = 4396607) B4396607
theorem B1954047 : Blo 1953435 1954047 := bstep (se 1 (by rfl) ⟨1465535, by rfl⟩ : syracuseStep 1954047 = 2931071) B2931071
theorem B2931077 : Blo 1953435 2931077 := bbase (se 4 (by rfl) ⟨274788, by rfl⟩ : syracuseStep 2931077 = 549577) (by norm_num)
theorem B1954051 : Blo 1953435 1954051 := bstep (se 1 (by rfl) ⟨1465538, by rfl⟩ : syracuseStep 1954051 = 2931077) B2931077
theorem B3297469 : Blo 1953435 3297469 := bbase (se 3 (by rfl) ⟨618275, by rfl⟩ : syracuseStep 3297469 = 1236551) (by norm_num)
theorem B4396625 : Blo 1953435 4396625 := bstep (se 2 (by rfl) ⟨1648734, by rfl⟩ : syracuseStep 4396625 = 3297469) B3297469
theorem B2931083 : Blo 1953435 2931083 := bstep (se 1 (by rfl) ⟨2198312, by rfl⟩ : syracuseStep 2931083 = 4396625) B4396625
theorem B1954055 : Blo 1953435 1954055 := bstep (se 1 (by rfl) ⟨1465541, by rfl⟩ : syracuseStep 1954055 = 2931083) B2931083
theorem B2198317 : Blo 1953435 2198317 := bbase (se 3 (by rfl) ⟨412184, by rfl⟩ : syracuseStep 2198317 = 824369) (by norm_num)
theorem B2931089 : Blo 1953435 2931089 := bstep (se 2 (by rfl) ⟨1099158, by rfl⟩ : syracuseStep 2931089 = 2198317) B2198317
theorem B1954059 : Blo 1953435 1954059 := bstep (se 1 (by rfl) ⟨1465544, by rfl⟩ : syracuseStep 1954059 = 2931089) B2931089
theorem B6594965 : Blo 1953435 6594965 := bbase (se 6 (by rfl) ⟨154569, by rfl⟩ : syracuseStep 6594965 = 309139) (by norm_num)
theorem B4396643 : Blo 1953435 4396643 := bstep (se 1 (by rfl) ⟨3297482, by rfl⟩ : syracuseStep 4396643 = 6594965) B6594965
theorem B2931095 : Blo 1953435 2931095 := bstep (se 1 (by rfl) ⟨2198321, by rfl⟩ : syracuseStep 2931095 = 4396643) B4396643
theorem B1954063 : Blo 1953435 1954063 := bstep (se 1 (by rfl) ⟨1465547, by rfl⟩ : syracuseStep 1954063 = 2931095) B2931095
theorem B2931101 : Blo 1953435 2931101 := bbase (se 3 (by rfl) ⟨549581, by rfl⟩ : syracuseStep 2931101 = 1099163) (by norm_num)
theorem B1954067 : Blo 1953435 1954067 := bstep (se 1 (by rfl) ⟨1465550, by rfl⟩ : syracuseStep 1954067 = 2931101) B2931101
theorem B4396661 : Blo 1953435 4396661 := bbase (se 5 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 4396661 = 412187) (by norm_num)
theorem B2931107 : Blo 1953435 2931107 := bstep (se 1 (by rfl) ⟨2198330, by rfl⟩ : syracuseStep 2931107 = 4396661) B4396661
theorem B1954071 : Blo 1953435 1954071 := bstep (se 1 (by rfl) ⟨1465553, by rfl⟩ : syracuseStep 1954071 = 2931107) B2931107
theorem B2228329 : Blo 1953435 2228329 := bbase (se 2 (by rfl) ⟨835623, by rfl⟩ : syracuseStep 2228329 = 1671247) (by norm_num)
theorem B11884421 : Blo 1953435 11884421 := bstep (se 4 (by rfl) ⟨1114164, by rfl⟩ : syracuseStep 11884421 = 2228329) B2228329
theorem B7922947 : Blo 1953435 7922947 := bstep (se 1 (by rfl) ⟨5942210, by rfl⟩ : syracuseStep 7922947 = 11884421) B11884421
theorem B10563929 : Blo 1953435 10563929 := bstep (se 2 (by rfl) ⟨3961473, by rfl⟩ : syracuseStep 10563929 = 7922947) B7922947
theorem B7042619 : Blo 1953435 7042619 := bstep (se 1 (by rfl) ⟨5281964, by rfl⟩ : syracuseStep 7042619 = 10563929) B10563929
theorem B4695079 : Blo 1953435 4695079 := bstep (se 1 (by rfl) ⟨3521309, by rfl⟩ : syracuseStep 4695079 = 7042619) B7042619
theorem B6260105 : Blo 1953435 6260105 := bstep (se 2 (by rfl) ⟨2347539, by rfl⟩ : syracuseStep 6260105 = 4695079) B4695079
theorem B16693613 : Blo 1953435 16693613 := bstep (se 3 (by rfl) ⟨3130052, by rfl⟩ : syracuseStep 16693613 = 6260105) B6260105
theorem B11129075 : Blo 1953435 11129075 := bstep (se 1 (by rfl) ⟨8346806, by rfl⟩ : syracuseStep 11129075 = 16693613) B16693613
theorem B7419383 : Blo 1953435 7419383 := bstep (se 1 (by rfl) ⟨5564537, by rfl⟩ : syracuseStep 7419383 = 11129075) B11129075
theorem B4946255 : Blo 1953435 4946255 := bstep (se 1 (by rfl) ⟨3709691, by rfl⟩ : syracuseStep 4946255 = 7419383) B7419383
theorem B3297503 : Blo 1953435 3297503 := bstep (se 1 (by rfl) ⟨2473127, by rfl⟩ : syracuseStep 3297503 = 4946255) B4946255
theorem B2198335 : Blo 1953435 2198335 := bstep (se 1 (by rfl) ⟨1648751, by rfl⟩ : syracuseStep 2198335 = 3297503) B3297503
theorem B2931113 : Blo 1953435 2931113 := bstep (se 2 (by rfl) ⟨1099167, by rfl⟩ : syracuseStep 2931113 = 2198335) B2198335
theorem B1954075 : Blo 1953435 1954075 := bstep (se 1 (by rfl) ⟨1465556, by rfl⟩ : syracuseStep 1954075 = 2931113) B2931113
theorem B7419397 : Blo 1953435 7419397 := bbase (se 4 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 7419397 = 1391137) (by norm_num)
theorem B9892529 : Blo 1953435 9892529 := bstep (se 2 (by rfl) ⟨3709698, by rfl⟩ : syracuseStep 9892529 = 7419397) B7419397
theorem B6595019 : Blo 1953435 6595019 := bstep (se 1 (by rfl) ⟨4946264, by rfl⟩ : syracuseStep 6595019 = 9892529) B9892529
theorem B4396679 : Blo 1953435 4396679 := bstep (se 1 (by rfl) ⟨3297509, by rfl⟩ : syracuseStep 4396679 = 6595019) B6595019
theorem B2931119 : Blo 1953435 2931119 := bstep (se 1 (by rfl) ⟨2198339, by rfl⟩ : syracuseStep 2931119 = 4396679) B4396679
theorem B1954079 : Blo 1953435 1954079 := bstep (se 1 (by rfl) ⟨1465559, by rfl⟩ : syracuseStep 1954079 = 2931119) B2931119
theorem B2931125 : Blo 1953435 2931125 := bbase (se 5 (by rfl) ⟨137396, by rfl⟩ : syracuseStep 2931125 = 274793) (by norm_num)
theorem B1954083 : Blo 1953435 1954083 := bstep (se 1 (by rfl) ⟨1465562, by rfl⟩ : syracuseStep 1954083 = 2931125) B2931125
theorem B4946285 : Blo 1953435 4946285 := bbase (se 3 (by rfl) ⟨927428, by rfl⟩ : syracuseStep 4946285 = 1854857) (by norm_num)
theorem B3297523 : Blo 1953435 3297523 := bstep (se 1 (by rfl) ⟨2473142, by rfl⟩ : syracuseStep 3297523 = 4946285) B4946285
theorem B4396697 : Blo 1953435 4396697 := bstep (se 2 (by rfl) ⟨1648761, by rfl⟩ : syracuseStep 4396697 = 3297523) B3297523
theorem B2931131 : Blo 1953435 2931131 := bstep (se 1 (by rfl) ⟨2198348, by rfl⟩ : syracuseStep 2931131 = 4396697) B4396697
theorem B1954087 : Blo 1953435 1954087 := bstep (se 1 (by rfl) ⟨1465565, by rfl⟩ : syracuseStep 1954087 = 2931131) B2931131
theorem B2198353 : Blo 1953435 2198353 := bbase (se 2 (by rfl) ⟨824382, by rfl⟩ : syracuseStep 2198353 = 1648765) (by norm_num)
theorem B2931137 : Blo 1953435 2931137 := bstep (se 2 (by rfl) ⟨1099176, by rfl⟩ : syracuseStep 2931137 = 2198353) B2198353
theorem B1954091 : Blo 1953435 1954091 := bstep (se 1 (by rfl) ⟨1465568, by rfl⟩ : syracuseStep 1954091 = 2931137) B2931137
theorem B3130085 : Blo 1953435 3130085 := bbase (se 4 (by rfl) ⟨293445, by rfl⟩ : syracuseStep 3130085 = 586891) (by norm_num)
theorem B2086723 : Blo 1953435 2086723 := bstep (se 1 (by rfl) ⟨1565042, by rfl⟩ : syracuseStep 2086723 = 3130085) B3130085
theorem B2782297 : Blo 1953435 2782297 := bstep (se 2 (by rfl) ⟨1043361, by rfl⟩ : syracuseStep 2782297 = 2086723) B2086723
theorem B3709729 : Blo 1953435 3709729 := bstep (se 2 (by rfl) ⟨1391148, by rfl⟩ : syracuseStep 3709729 = 2782297) B2782297
theorem B4946305 : Blo 1953435 4946305 := bstep (se 2 (by rfl) ⟨1854864, by rfl⟩ : syracuseStep 4946305 = 3709729) B3709729
theorem B6595073 : Blo 1953435 6595073 := bstep (se 2 (by rfl) ⟨2473152, by rfl⟩ : syracuseStep 6595073 = 4946305) B4946305
theorem B4396715 : Blo 1953435 4396715 := bstep (se 1 (by rfl) ⟨3297536, by rfl⟩ : syracuseStep 4396715 = 6595073) B6595073
theorem B2931143 : Blo 1953435 2931143 := bstep (se 1 (by rfl) ⟨2198357, by rfl⟩ : syracuseStep 2931143 = 4396715) B4396715
theorem B1954095 : Blo 1953435 1954095 := bstep (se 1 (by rfl) ⟨1465571, by rfl⟩ : syracuseStep 1954095 = 2931143) B2931143
theorem B2931149 : Blo 1953435 2931149 := bbase (se 3 (by rfl) ⟨549590, by rfl⟩ : syracuseStep 2931149 = 1099181) (by norm_num)
theorem B1954099 : Blo 1953435 1954099 := bstep (se 1 (by rfl) ⟨1465574, by rfl⟩ : syracuseStep 1954099 = 2931149) B2931149
theorem B4396733 : Blo 1953435 4396733 := bbase (se 3 (by rfl) ⟨824387, by rfl⟩ : syracuseStep 4396733 = 1648775) (by norm_num)
theorem B2931155 : Blo 1953435 2931155 := bstep (se 1 (by rfl) ⟨2198366, by rfl⟩ : syracuseStep 2931155 = 4396733) B4396733
theorem B1954103 : Blo 1953435 1954103 := bstep (se 1 (by rfl) ⟨1465577, by rfl⟩ : syracuseStep 1954103 = 2931155) B2931155
theorem B3297557 : Blo 1953435 3297557 := bbase (se 6 (by rfl) ⟨77286, by rfl⟩ : syracuseStep 3297557 = 154573) (by norm_num)
theorem B2198371 : Blo 1953435 2198371 := bstep (se 1 (by rfl) ⟨1648778, by rfl⟩ : syracuseStep 2198371 = 3297557) B3297557
theorem B2931161 : Blo 1953435 2931161 := bstep (se 2 (by rfl) ⟨1099185, by rfl⟩ : syracuseStep 2931161 = 2198371) B2198371
theorem B1954107 : Blo 1953435 1954107 := bstep (se 1 (by rfl) ⟨1465580, by rfl⟩ : syracuseStep 1954107 = 2931161) B2931161
theorem B6685109 : Blo 1953435 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B4456739 : Blo 1953435 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B11884637 : Blo 1953435 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B7923091 : Blo 1953435 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B10564121 : Blo 1953435 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B28170989 : Blo 1953435 28170989 := bstep (se 3 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 28170989 = 10564121) B10564121
theorem B18780659 : Blo 1953435 18780659 := bstep (se 1 (by rfl) ⟨14085494, by rfl⟩ : syracuseStep 18780659 = 28170989) B28170989
theorem B12520439 : Blo 1953435 12520439 := bstep (se 1 (by rfl) ⟨9390329, by rfl⟩ : syracuseStep 12520439 = 18780659) B18780659
theorem B8346959 : Blo 1953435 8346959 := bstep (se 1 (by rfl) ⟨6260219, by rfl⟩ : syracuseStep 8346959 = 12520439) B12520439
theorem B5564639 : Blo 1953435 5564639 := bstep (se 1 (by rfl) ⟨4173479, by rfl⟩ : syracuseStep 5564639 = 8346959) B8346959
theorem B14839037 : Blo 1953435 14839037 := bstep (se 3 (by rfl) ⟨2782319, by rfl⟩ : syracuseStep 14839037 = 5564639) B5564639
theorem B9892691 : Blo 1953435 9892691 := bstep (se 1 (by rfl) ⟨7419518, by rfl⟩ : syracuseStep 9892691 = 14839037) B14839037
theorem B6595127 : Blo 1953435 6595127 := bstep (se 1 (by rfl) ⟨4946345, by rfl⟩ : syracuseStep 6595127 = 9892691) B9892691
theorem B4396751 : Blo 1953435 4396751 := bstep (se 1 (by rfl) ⟨3297563, by rfl⟩ : syracuseStep 4396751 = 6595127) B6595127
theorem B2931167 : Blo 1953435 2931167 := bstep (se 1 (by rfl) ⟨2198375, by rfl⟩ : syracuseStep 2931167 = 4396751) B4396751
theorem B1954111 : Blo 1953435 1954111 := bstep (se 1 (by rfl) ⟨1465583, by rfl⟩ : syracuseStep 1954111 = 2931167) B2931167
theorem B2931173 : Blo 1953435 2931173 := bbase (se 4 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 2931173 = 549595) (by norm_num)
theorem B1954115 : Blo 1953435 1954115 := bstep (se 1 (by rfl) ⟨1465586, by rfl⟩ : syracuseStep 1954115 = 2931173) B2931173
theorem B3521389 : Blo 1953435 3521389 := bbase (se 3 (by rfl) ⟨660260, by rfl⟩ : syracuseStep 3521389 = 1320521) (by norm_num)
theorem B4695185 : Blo 1953435 4695185 := bstep (se 2 (by rfl) ⟨1760694, by rfl⟩ : syracuseStep 4695185 = 3521389) B3521389
theorem B12520493 : Blo 1953435 12520493 := bstep (se 3 (by rfl) ⟨2347592, by rfl⟩ : syracuseStep 12520493 = 4695185) B4695185
theorem B8346995 : Blo 1953435 8346995 := bstep (se 1 (by rfl) ⟨6260246, by rfl⟩ : syracuseStep 8346995 = 12520493) B12520493
theorem B5564663 : Blo 1953435 5564663 := bstep (se 1 (by rfl) ⟨4173497, by rfl⟩ : syracuseStep 5564663 = 8346995) B8346995
theorem B3709775 : Blo 1953435 3709775 := bstep (se 1 (by rfl) ⟨2782331, by rfl⟩ : syracuseStep 3709775 = 5564663) B5564663
theorem B2473183 : Blo 1953435 2473183 := bstep (se 1 (by rfl) ⟨1854887, by rfl⟩ : syracuseStep 2473183 = 3709775) B3709775
theorem B3297577 : Blo 1953435 3297577 := bstep (se 2 (by rfl) ⟨1236591, by rfl⟩ : syracuseStep 3297577 = 2473183) B2473183
theorem B4396769 : Blo 1953435 4396769 := bstep (se 2 (by rfl) ⟨1648788, by rfl⟩ : syracuseStep 4396769 = 3297577) B3297577
theorem B2931179 : Blo 1953435 2931179 := bstep (se 1 (by rfl) ⟨2198384, by rfl⟩ : syracuseStep 2931179 = 4396769) B4396769
theorem B1954119 : Blo 1953435 1954119 := bstep (se 1 (by rfl) ⟨1465589, by rfl⟩ : syracuseStep 1954119 = 2931179) B2931179
theorem B2198389 : Blo 1953435 2198389 := bbase (se 5 (by rfl) ⟨103049, by rfl⟩ : syracuseStep 2198389 = 206099) (by norm_num)
theorem B2931185 : Blo 1953435 2931185 := bstep (se 2 (by rfl) ⟨1099194, by rfl⟩ : syracuseStep 2931185 = 2198389) B2198389
theorem B1954123 : Blo 1953435 1954123 := bstep (se 1 (by rfl) ⟨1465592, by rfl⟩ : syracuseStep 1954123 = 2931185) B2931185
theorem B2473193 : Blo 1953435 2473193 := bbase (se 2 (by rfl) ⟨927447, by rfl⟩ : syracuseStep 2473193 = 1854895) (by norm_num)
theorem B6595181 : Blo 1953435 6595181 := bstep (se 3 (by rfl) ⟨1236596, by rfl⟩ : syracuseStep 6595181 = 2473193) B2473193
theorem B4396787 : Blo 1953435 4396787 := bstep (se 1 (by rfl) ⟨3297590, by rfl⟩ : syracuseStep 4396787 = 6595181) B6595181
theorem B2931191 : Blo 1953435 2931191 := bstep (se 1 (by rfl) ⟨2198393, by rfl⟩ : syracuseStep 2931191 = 4396787) B4396787
theorem B1954127 : Blo 1953435 1954127 := bstep (se 1 (by rfl) ⟨1465595, by rfl⟩ : syracuseStep 1954127 = 2931191) B2931191
theorem B2931197 : Blo 1953435 2931197 := bbase (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) (by norm_num)
theorem B1954131 : Blo 1953435 1954131 := bstep (se 1 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 1954131 = 2931197) B2931197
theorem B4396805 : Blo 1953435 4396805 := bbase (se 4 (by rfl) ⟨412200, by rfl⟩ : syracuseStep 4396805 = 824401) (by norm_num)
theorem B2931203 : Blo 1953435 2931203 := bstep (se 1 (by rfl) ⟨2198402, by rfl⟩ : syracuseStep 2931203 = 4396805) B4396805
theorem B1954135 : Blo 1953435 1954135 := bstep (se 1 (by rfl) ⟨1465601, by rfl⟩ : syracuseStep 1954135 = 2931203) B2931203
theorem B3709813 : Blo 1953435 3709813 := bbase (se 5 (by rfl) ⟨173897, by rfl⟩ : syracuseStep 3709813 = 347795) (by norm_num)
theorem B4946417 : Blo 1953435 4946417 := bstep (se 2 (by rfl) ⟨1854906, by rfl⟩ : syracuseStep 4946417 = 3709813) B3709813
theorem B3297611 : Blo 1953435 3297611 := bstep (se 1 (by rfl) ⟨2473208, by rfl⟩ : syracuseStep 3297611 = 4946417) B4946417
theorem B2198407 : Blo 1953435 2198407 := bstep (se 1 (by rfl) ⟨1648805, by rfl⟩ : syracuseStep 2198407 = 3297611) B3297611
theorem B2931209 : Blo 1953435 2931209 := bstep (se 2 (by rfl) ⟨1099203, by rfl⟩ : syracuseStep 2931209 = 2198407) B2198407
theorem B1954139 : Blo 1953435 1954139 := bstep (se 1 (by rfl) ⟨1465604, by rfl⟩ : syracuseStep 1954139 = 2931209) B2931209
theorem B9892853 : Blo 1953435 9892853 := bbase (se 5 (by rfl) ⟨463727, by rfl⟩ : syracuseStep 9892853 = 927455) (by norm_num)
theorem B6595235 : Blo 1953435 6595235 := bstep (se 1 (by rfl) ⟨4946426, by rfl⟩ : syracuseStep 6595235 = 9892853) B9892853
theorem B4396823 : Blo 1953435 4396823 := bstep (se 1 (by rfl) ⟨3297617, by rfl⟩ : syracuseStep 4396823 = 6595235) B6595235
theorem B2931215 : Blo 1953435 2931215 := bstep (se 1 (by rfl) ⟨2198411, by rfl⟩ : syracuseStep 2931215 = 4396823) B4396823
theorem B1954143 : Blo 1953435 1954143 := bstep (se 1 (by rfl) ⟨1465607, by rfl⟩ : syracuseStep 1954143 = 2931215) B2931215
theorem B2931221 : Blo 1953435 2931221 := bbase (se 6 (by rfl) ⟨68700, by rfl⟩ : syracuseStep 2931221 = 137401) (by norm_num)
theorem B1954147 : Blo 1953435 1954147 := bstep (se 1 (by rfl) ⟨1465610, by rfl⟩ : syracuseStep 1954147 = 2931221) B2931221
theorem B16694261 : Blo 1953435 16694261 := bbase (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) (by norm_num)
theorem B11129507 : Blo 1953435 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B7419671 : Blo 1953435 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B4946447 : Blo 1953435 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B3297631 : Blo 1953435 3297631 := bstep (se 1 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 3297631 = 4946447) B4946447
theorem B4396841 : Blo 1953435 4396841 := bstep (se 2 (by rfl) ⟨1648815, by rfl⟩ : syracuseStep 4396841 = 3297631) B3297631
theorem B2931227 : Blo 1953435 2931227 := bstep (se 1 (by rfl) ⟨2198420, by rfl⟩ : syracuseStep 2931227 = 4396841) B4396841
theorem B1954151 : Blo 1953435 1954151 := bstep (se 1 (by rfl) ⟨1465613, by rfl⟩ : syracuseStep 1954151 = 2931227) B2931227
theorem B2198425 : Blo 1953435 2198425 := bbase (se 2 (by rfl) ⟨824409, by rfl⟩ : syracuseStep 2198425 = 1648819) (by norm_num)
theorem B2931233 : Blo 1953435 2931233 := bstep (se 2 (by rfl) ⟨1099212, by rfl⟩ : syracuseStep 2931233 = 2198425) B2198425
theorem B1954155 : Blo 1953435 1954155 := bstep (se 1 (by rfl) ⟨1465616, by rfl⟩ : syracuseStep 1954155 = 2931233) B2931233
theorem B7419701 : Blo 1953435 7419701 := bbase (se 5 (by rfl) ⟨347798, by rfl⟩ : syracuseStep 7419701 = 695597) (by norm_num)
theorem B4946467 : Blo 1953435 4946467 := bstep (se 1 (by rfl) ⟨3709850, by rfl⟩ : syracuseStep 4946467 = 7419701) B7419701
theorem B6595289 : Blo 1953435 6595289 := bstep (se 2 (by rfl) ⟨2473233, by rfl⟩ : syracuseStep 6595289 = 4946467) B4946467
theorem B4396859 : Blo 1953435 4396859 := bstep (se 1 (by rfl) ⟨3297644, by rfl⟩ : syracuseStep 4396859 = 6595289) B6595289
theorem B2931239 : Blo 1953435 2931239 := bstep (se 1 (by rfl) ⟨2198429, by rfl⟩ : syracuseStep 2931239 = 4396859) B4396859
theorem B1954159 : Blo 1953435 1954159 := bstep (se 1 (by rfl) ⟨1465619, by rfl⟩ : syracuseStep 1954159 = 2931239) B2931239
theorem B2931245 : Blo 1953435 2931245 := bbase (se 3 (by rfl) ⟨549608, by rfl⟩ : syracuseStep 2931245 = 1099217) (by norm_num)
theorem B1954163 : Blo 1953435 1954163 := bstep (se 1 (by rfl) ⟨1465622, by rfl⟩ : syracuseStep 1954163 = 2931245) B2931245
theorem B4396877 : Blo 1953435 4396877 := bbase (se 3 (by rfl) ⟨824414, by rfl⟩ : syracuseStep 4396877 = 1648829) (by norm_num)
theorem B2931251 : Blo 1953435 2931251 := bstep (se 1 (by rfl) ⟨2198438, by rfl⟩ : syracuseStep 2931251 = 4396877) B4396877
theorem B1954167 : Blo 1953435 1954167 := bstep (se 1 (by rfl) ⟨1465625, by rfl⟩ : syracuseStep 1954167 = 2931251) B2931251
theorem B2473249 : Blo 1953435 2473249 := bbase (se 2 (by rfl) ⟨927468, by rfl⟩ : syracuseStep 2473249 = 1854937) (by norm_num)
theorem B3297665 : Blo 1953435 3297665 := bstep (se 2 (by rfl) ⟨1236624, by rfl⟩ : syracuseStep 3297665 = 2473249) B2473249
theorem B2198443 : Blo 1953435 2198443 := bstep (se 1 (by rfl) ⟨1648832, by rfl⟩ : syracuseStep 2198443 = 3297665) B3297665
theorem B2931257 : Blo 1953435 2931257 := bstep (se 2 (by rfl) ⟨1099221, by rfl⟩ : syracuseStep 2931257 = 2198443) B2198443
theorem B1954171 : Blo 1953435 1954171 := bstep (se 1 (by rfl) ⟨1465628, by rfl⟩ : syracuseStep 1954171 = 2931257) B2931257
theorem B22259285 : Blo 1953435 22259285 := bbase (se 8 (by rfl) ⟨130425, by rfl⟩ : syracuseStep 22259285 = 260851) (by norm_num)
theorem B14839523 : Blo 1953435 14839523 := bstep (se 1 (by rfl) ⟨11129642, by rfl⟩ : syracuseStep 14839523 = 22259285) B22259285
theorem B9893015 : Blo 1953435 9893015 := bstep (se 1 (by rfl) ⟨7419761, by rfl⟩ : syracuseStep 9893015 = 14839523) B14839523
theorem B6595343 : Blo 1953435 6595343 := bstep (se 1 (by rfl) ⟨4946507, by rfl⟩ : syracuseStep 6595343 = 9893015) B9893015
theorem B4396895 : Blo 1953435 4396895 := bstep (se 1 (by rfl) ⟨3297671, by rfl⟩ : syracuseStep 4396895 = 6595343) B6595343
theorem B2931263 : Blo 1953435 2931263 := bstep (se 1 (by rfl) ⟨2198447, by rfl⟩ : syracuseStep 2931263 = 4396895) B4396895
theorem B1954175 : Blo 1953435 1954175 := bstep (se 1 (by rfl) ⟨1465631, by rfl⟩ : syracuseStep 1954175 = 2931263) B2931263
theorem B2931269 : Blo 1953435 2931269 := bbase (se 4 (by rfl) ⟨274806, by rfl⟩ : syracuseStep 2931269 = 549613) (by norm_num)
theorem B1954179 : Blo 1953435 1954179 := bstep (se 1 (by rfl) ⟨1465634, by rfl⟩ : syracuseStep 1954179 = 2931269) B2931269
theorem B3297685 : Blo 1953435 3297685 := bbase (se 6 (by rfl) ⟨77289, by rfl⟩ : syracuseStep 3297685 = 154579) (by norm_num)
theorem B4396913 : Blo 1953435 4396913 := bstep (se 2 (by rfl) ⟨1648842, by rfl⟩ : syracuseStep 4396913 = 3297685) B3297685
theorem B2931275 : Blo 1953435 2931275 := bstep (se 1 (by rfl) ⟨2198456, by rfl⟩ : syracuseStep 2931275 = 4396913) B4396913
theorem B1954183 : Blo 1953435 1954183 := bstep (se 1 (by rfl) ⟨1465637, by rfl⟩ : syracuseStep 1954183 = 2931275) B2931275
theorem B2198461 : Blo 1953435 2198461 := bbase (se 3 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 2198461 = 824423) (by norm_num)
theorem B2931281 : Blo 1953435 2931281 := bstep (se 2 (by rfl) ⟨1099230, by rfl⟩ : syracuseStep 2931281 = 2198461) B2198461
theorem B1954187 : Blo 1953435 1954187 := bstep (se 1 (by rfl) ⟨1465640, by rfl⟩ : syracuseStep 1954187 = 2931281) B2931281
theorem B6595397 : Blo 1953435 6595397 := bbase (se 4 (by rfl) ⟨618318, by rfl⟩ : syracuseStep 6595397 = 1236637) (by norm_num)
theorem B4396931 : Blo 1953435 4396931 := bstep (se 1 (by rfl) ⟨3297698, by rfl⟩ : syracuseStep 4396931 = 6595397) B6595397
theorem B2931287 : Blo 1953435 2931287 := bstep (se 1 (by rfl) ⟨2198465, by rfl⟩ : syracuseStep 2931287 = 4396931) B4396931
theorem B1954191 : Blo 1953435 1954191 := bstep (se 1 (by rfl) ⟨1465643, by rfl⟩ : syracuseStep 1954191 = 2931287) B2931287
theorem B2931293 : Blo 1953435 2931293 := bbase (se 3 (by rfl) ⟨549617, by rfl⟩ : syracuseStep 2931293 = 1099235) (by norm_num)
theorem B1954195 : Blo 1953435 1954195 := bstep (se 1 (by rfl) ⟨1465646, by rfl⟩ : syracuseStep 1954195 = 2931293) B2931293
theorem B4396949 : Blo 1953435 4396949 := bbase (se 6 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 4396949 = 206107) (by norm_num)
theorem B2931299 : Blo 1953435 2931299 := bstep (se 1 (by rfl) ⟨2198474, by rfl⟩ : syracuseStep 2931299 = 4396949) B4396949
theorem B1954199 : Blo 1953435 1954199 := bstep (se 1 (by rfl) ⟨1465649, by rfl⟩ : syracuseStep 1954199 = 2931299) B2931299
theorem B4173677 : Blo 1953435 4173677 := bbase (se 3 (by rfl) ⟨782564, by rfl⟩ : syracuseStep 4173677 = 1565129) (by norm_num)
theorem B2782451 : Blo 1953435 2782451 := bstep (se 1 (by rfl) ⟨2086838, by rfl⟩ : syracuseStep 2782451 = 4173677) B4173677
theorem B7419869 : Blo 1953435 7419869 := bstep (se 3 (by rfl) ⟨1391225, by rfl⟩ : syracuseStep 7419869 = 2782451) B2782451
theorem B4946579 : Blo 1953435 4946579 := bstep (se 1 (by rfl) ⟨3709934, by rfl⟩ : syracuseStep 4946579 = 7419869) B7419869
theorem B3297719 : Blo 1953435 3297719 := bstep (se 1 (by rfl) ⟨2473289, by rfl⟩ : syracuseStep 3297719 = 4946579) B4946579
theorem B2198479 : Blo 1953435 2198479 := bstep (se 1 (by rfl) ⟨1648859, by rfl⟩ : syracuseStep 2198479 = 3297719) B3297719
theorem B2931305 : Blo 1953435 2931305 := bstep (se 2 (by rfl) ⟨1099239, by rfl⟩ : syracuseStep 2931305 = 2198479) B2198479
theorem B1954203 : Blo 1953435 1954203 := bstep (se 1 (by rfl) ⟨1465652, by rfl⟩ : syracuseStep 1954203 = 2931305) B2931305
theorem B38075669 : Blo 1953435 38075669 := bbase (se 6 (by rfl) ⟨892398, by rfl⟩ : syracuseStep 38075669 = 1784797) (by norm_num)
theorem B25383779 : Blo 1953435 25383779 := bstep (se 1 (by rfl) ⟨19037834, by rfl⟩ : syracuseStep 25383779 = 38075669) B38075669
theorem B16922519 : Blo 1953435 16922519 := bstep (se 1 (by rfl) ⟨12691889, by rfl⟩ : syracuseStep 16922519 = 25383779) B25383779
theorem B11281679 : Blo 1953435 11281679 := bstep (se 1 (by rfl) ⟨8461259, by rfl⟩ : syracuseStep 11281679 = 16922519) B16922519
theorem B7521119 : Blo 1953435 7521119 := bstep (se 1 (by rfl) ⟨5640839, by rfl⟩ : syracuseStep 7521119 = 11281679) B11281679
theorem B5014079 : Blo 1953435 5014079 := bstep (se 1 (by rfl) ⟨3760559, by rfl⟩ : syracuseStep 5014079 = 7521119) B7521119
theorem B3342719 : Blo 1953435 3342719 := bstep (se 1 (by rfl) ⟨2507039, by rfl⟩ : syracuseStep 3342719 = 5014079) B5014079
theorem B2228479 : Blo 1953435 2228479 := bstep (se 1 (by rfl) ⟨1671359, by rfl⟩ : syracuseStep 2228479 = 3342719) B3342719
theorem B11885221 : Blo 1953435 11885221 := bstep (se 4 (by rfl) ⟨1114239, by rfl⟩ : syracuseStep 11885221 = 2228479) B2228479
theorem B15846961 : Blo 1953435 15846961 := bstep (se 2 (by rfl) ⟨5942610, by rfl⟩ : syracuseStep 15846961 = 11885221) B11885221
theorem B21129281 : Blo 1953435 21129281 := bstep (se 2 (by rfl) ⟨7923480, by rfl⟩ : syracuseStep 21129281 = 15846961) B15846961
theorem B14086187 : Blo 1953435 14086187 := bstep (se 1 (by rfl) ⟨10564640, by rfl⟩ : syracuseStep 14086187 = 21129281) B21129281
theorem B9390791 : Blo 1953435 9390791 := bstep (se 1 (by rfl) ⟨7043093, by rfl⟩ : syracuseStep 9390791 = 14086187) B14086187
theorem B6260527 : Blo 1953435 6260527 := bstep (se 1 (by rfl) ⟨4695395, by rfl⟩ : syracuseStep 6260527 = 9390791) B9390791
theorem B8347369 : Blo 1953435 8347369 := bstep (se 2 (by rfl) ⟨3130263, by rfl⟩ : syracuseStep 8347369 = 6260527) B6260527
theorem B11129825 : Blo 1953435 11129825 := bstep (se 2 (by rfl) ⟨4173684, by rfl⟩ : syracuseStep 11129825 = 8347369) B8347369
theorem B7419883 : Blo 1953435 7419883 := bstep (se 1 (by rfl) ⟨5564912, by rfl⟩ : syracuseStep 7419883 = 11129825) B11129825
theorem B9893177 : Blo 1953435 9893177 := bstep (se 2 (by rfl) ⟨3709941, by rfl⟩ : syracuseStep 9893177 = 7419883) B7419883
theorem B6595451 : Blo 1953435 6595451 := bstep (se 1 (by rfl) ⟨4946588, by rfl⟩ : syracuseStep 6595451 = 9893177) B9893177
theorem B4396967 : Blo 1953435 4396967 := bstep (se 1 (by rfl) ⟨3297725, by rfl⟩ : syracuseStep 4396967 = 6595451) B6595451
theorem B2931311 : Blo 1953435 2931311 := bstep (se 1 (by rfl) ⟨2198483, by rfl⟩ : syracuseStep 2931311 = 4396967) B4396967
theorem B1954207 : Blo 1953435 1954207 := bstep (se 1 (by rfl) ⟨1465655, by rfl⟩ : syracuseStep 1954207 = 2931311) B2931311
theorem B2931317 : Blo 1953435 2931317 := bbase (se 5 (by rfl) ⟨137405, by rfl⟩ : syracuseStep 2931317 = 274811) (by norm_num)
theorem B1954211 : Blo 1953435 1954211 := bstep (se 1 (by rfl) ⟨1465658, by rfl⟩ : syracuseStep 1954211 = 2931317) B2931317
theorem B3709957 : Blo 1953435 3709957 := bbase (se 4 (by rfl) ⟨347808, by rfl⟩ : syracuseStep 3709957 = 695617) (by norm_num)
theorem B4946609 : Blo 1953435 4946609 := bstep (se 2 (by rfl) ⟨1854978, by rfl⟩ : syracuseStep 4946609 = 3709957) B3709957
theorem B3297739 : Blo 1953435 3297739 := bstep (se 1 (by rfl) ⟨2473304, by rfl⟩ : syracuseStep 3297739 = 4946609) B4946609
theorem B4396985 : Blo 1953435 4396985 := bstep (se 2 (by rfl) ⟨1648869, by rfl⟩ : syracuseStep 4396985 = 3297739) B3297739
theorem B2931323 : Blo 1953435 2931323 := bstep (se 1 (by rfl) ⟨2198492, by rfl⟩ : syracuseStep 2931323 = 4396985) B4396985
theorem B1954215 : Blo 1953435 1954215 := bstep (se 1 (by rfl) ⟨1465661, by rfl⟩ : syracuseStep 1954215 = 2931323) B2931323
theorem B2198497 : Blo 1953435 2198497 := bbase (se 2 (by rfl) ⟨824436, by rfl⟩ : syracuseStep 2198497 = 1648873) (by norm_num)
theorem B2931329 : Blo 1953435 2931329 := bstep (se 2 (by rfl) ⟨1099248, by rfl⟩ : syracuseStep 2931329 = 2198497) B2198497
theorem B1954219 : Blo 1953435 1954219 := bstep (se 1 (by rfl) ⟨1465664, by rfl⟩ : syracuseStep 1954219 = 2931329) B2931329
theorem B4946629 : Blo 1953435 4946629 := bbase (se 4 (by rfl) ⟨463746, by rfl⟩ : syracuseStep 4946629 = 927493) (by norm_num)
theorem B6595505 : Blo 1953435 6595505 := bstep (se 2 (by rfl) ⟨2473314, by rfl⟩ : syracuseStep 6595505 = 4946629) B4946629
theorem B4397003 : Blo 1953435 4397003 := bstep (se 1 (by rfl) ⟨3297752, by rfl⟩ : syracuseStep 4397003 = 6595505) B6595505
theorem B2931335 : Blo 1953435 2931335 := bstep (se 1 (by rfl) ⟨2198501, by rfl⟩ : syracuseStep 2931335 = 4397003) B4397003
theorem B1954223 : Blo 1953435 1954223 := bstep (se 1 (by rfl) ⟨1465667, by rfl⟩ : syracuseStep 1954223 = 2931335) B2931335
theorem B2931341 : Blo 1953435 2931341 := bbase (se 3 (by rfl) ⟨549626, by rfl⟩ : syracuseStep 2931341 = 1099253) (by norm_num)
theorem B1954227 : Blo 1953435 1954227 := bstep (se 1 (by rfl) ⟨1465670, by rfl⟩ : syracuseStep 1954227 = 2931341) B2931341
theorem B4397021 : Blo 1953435 4397021 := bbase (se 3 (by rfl) ⟨824441, by rfl⟩ : syracuseStep 4397021 = 1648883) (by norm_num)
theorem B2931347 : Blo 1953435 2931347 := bstep (se 1 (by rfl) ⟨2198510, by rfl⟩ : syracuseStep 2931347 = 4397021) B4397021
theorem B1954231 : Blo 1953435 1954231 := bstep (se 1 (by rfl) ⟨1465673, by rfl⟩ : syracuseStep 1954231 = 2931347) B2931347
theorem B3297773 : Blo 1953435 3297773 := bbase (se 3 (by rfl) ⟨618332, by rfl⟩ : syracuseStep 3297773 = 1236665) (by norm_num)
theorem B2198515 : Blo 1953435 2198515 := bstep (se 1 (by rfl) ⟨1648886, by rfl⟩ : syracuseStep 2198515 = 3297773) B3297773
theorem B2931353 : Blo 1953435 2931353 := bstep (se 2 (by rfl) ⟨1099257, by rfl⟩ : syracuseStep 2931353 = 2198515) B2198515
theorem B1954235 : Blo 1953435 1954235 := bstep (se 1 (by rfl) ⟨1465676, by rfl⟩ : syracuseStep 1954235 = 2931353) B2931353
theorem B25042517 : Blo 1953435 25042517 := bbase (se 8 (by rfl) ⟨146733, by rfl⟩ : syracuseStep 25042517 = 293467) (by norm_num)
theorem B16695011 : Blo 1953435 16695011 := bstep (se 1 (by rfl) ⟨12521258, by rfl⟩ : syracuseStep 16695011 = 25042517) B25042517
theorem B11130007 : Blo 1953435 11130007 := bstep (se 1 (by rfl) ⟨8347505, by rfl⟩ : syracuseStep 11130007 = 16695011) B16695011
theorem B14840009 : Blo 1953435 14840009 := bstep (se 2 (by rfl) ⟨5565003, by rfl⟩ : syracuseStep 14840009 = 11130007) B11130007
theorem B9893339 : Blo 1953435 9893339 := bstep (se 1 (by rfl) ⟨7420004, by rfl⟩ : syracuseStep 9893339 = 14840009) B14840009
theorem B6595559 : Blo 1953435 6595559 := bstep (se 1 (by rfl) ⟨4946669, by rfl⟩ : syracuseStep 6595559 = 9893339) B9893339
theorem B4397039 : Blo 1953435 4397039 := bstep (se 1 (by rfl) ⟨3297779, by rfl⟩ : syracuseStep 4397039 = 6595559) B6595559
theorem B2931359 : Blo 1953435 2931359 := bstep (se 1 (by rfl) ⟨2198519, by rfl⟩ : syracuseStep 2931359 = 4397039) B4397039
theorem B1954239 : Blo 1953435 1954239 := bstep (se 1 (by rfl) ⟨1465679, by rfl⟩ : syracuseStep 1954239 = 2931359) B2931359
theorem B2931365 : Blo 1953435 2931365 := bbase (se 4 (by rfl) ⟨274815, by rfl⟩ : syracuseStep 2931365 = 549631) (by norm_num)
theorem B1954243 : Blo 1953435 1954243 := bstep (se 1 (by rfl) ⟨1465682, by rfl⟩ : syracuseStep 1954243 = 2931365) B2931365
theorem B2473345 : Blo 1953435 2473345 := bbase (se 2 (by rfl) ⟨927504, by rfl⟩ : syracuseStep 2473345 = 1855009) (by norm_num)
theorem B3297793 : Blo 1953435 3297793 := bstep (se 2 (by rfl) ⟨1236672, by rfl⟩ : syracuseStep 3297793 = 2473345) B2473345
theorem B4397057 : Blo 1953435 4397057 := bstep (se 2 (by rfl) ⟨1648896, by rfl⟩ : syracuseStep 4397057 = 3297793) B3297793
theorem B2931371 : Blo 1953435 2931371 := bstep (se 1 (by rfl) ⟨2198528, by rfl⟩ : syracuseStep 2931371 = 4397057) B4397057
theorem B1954247 : Blo 1953435 1954247 := bstep (se 1 (by rfl) ⟨1465685, by rfl⟩ : syracuseStep 1954247 = 2931371) B2931371
theorem B2198533 : Blo 1953435 2198533 := bbase (se 4 (by rfl) ⟨206112, by rfl⟩ : syracuseStep 2198533 = 412225) (by norm_num)
theorem B2931377 : Blo 1953435 2931377 := bstep (se 2 (by rfl) ⟨1099266, by rfl⟩ : syracuseStep 2931377 = 2198533) B2198533
theorem B1954251 : Blo 1953435 1954251 := bstep (se 1 (by rfl) ⟨1465688, by rfl⟩ : syracuseStep 1954251 = 2931377) B2931377
theorem B2782525 : Blo 1953435 2782525 := bbase (se 3 (by rfl) ⟨521723, by rfl⟩ : syracuseStep 2782525 = 1043447) (by norm_num)
theorem B3710033 : Blo 1953435 3710033 := bstep (se 2 (by rfl) ⟨1391262, by rfl⟩ : syracuseStep 3710033 = 2782525) B2782525
theorem B2473355 : Blo 1953435 2473355 := bstep (se 1 (by rfl) ⟨1855016, by rfl⟩ : syracuseStep 2473355 = 3710033) B3710033
theorem B6595613 : Blo 1953435 6595613 := bstep (se 3 (by rfl) ⟨1236677, by rfl⟩ : syracuseStep 6595613 = 2473355) B2473355
theorem B4397075 : Blo 1953435 4397075 := bstep (se 1 (by rfl) ⟨3297806, by rfl⟩ : syracuseStep 4397075 = 6595613) B6595613
theorem B2931383 : Blo 1953435 2931383 := bstep (se 1 (by rfl) ⟨2198537, by rfl⟩ : syracuseStep 2931383 = 4397075) B4397075
theorem B1954255 : Blo 1953435 1954255 := bstep (se 1 (by rfl) ⟨1465691, by rfl⟩ : syracuseStep 1954255 = 2931383) B2931383
theorem B2931389 : Blo 1953435 2931389 := bbase (se 3 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 2931389 = 1099271) (by norm_num)
theorem B1954259 : Blo 1953435 1954259 := bstep (se 1 (by rfl) ⟨1465694, by rfl⟩ : syracuseStep 1954259 = 2931389) B2931389
theorem B4397093 : Blo 1953435 4397093 := bbase (se 4 (by rfl) ⟨412227, by rfl⟩ : syracuseStep 4397093 = 824455) (by norm_num)
theorem B2931395 : Blo 1953435 2931395 := bstep (se 1 (by rfl) ⟨2198546, by rfl⟩ : syracuseStep 2931395 = 4397093) B4397093
theorem B1954263 : Blo 1953435 1954263 := bstep (se 1 (by rfl) ⟨1465697, by rfl⟩ : syracuseStep 1954263 = 2931395) B2931395
theorem B4946741 : Blo 1953435 4946741 := bbase (se 5 (by rfl) ⟨231878, by rfl⟩ : syracuseStep 4946741 = 463757) (by norm_num)
theorem B3297827 : Blo 1953435 3297827 := bstep (se 1 (by rfl) ⟨2473370, by rfl⟩ : syracuseStep 3297827 = 4946741) B4946741
theorem B2198551 : Blo 1953435 2198551 := bstep (se 1 (by rfl) ⟨1648913, by rfl⟩ : syracuseStep 2198551 = 3297827) B3297827
theorem B2931401 : Blo 1953435 2931401 := bstep (se 2 (by rfl) ⟨1099275, by rfl⟩ : syracuseStep 2931401 = 2198551) B2198551
theorem B1954267 : Blo 1953435 1954267 := bstep (se 1 (by rfl) ⟨1465700, by rfl⟩ : syracuseStep 1954267 = 2931401) B2931401
theorem B10028485 : Blo 1953435 10028485 := bbase (se 4 (by rfl) ⟨940170, by rfl⟩ : syracuseStep 10028485 = 1880341) (by norm_num)
theorem B13371313 : Blo 1953435 13371313 := bstep (se 2 (by rfl) ⟨5014242, by rfl⟩ : syracuseStep 13371313 = 10028485) B10028485
theorem B17828417 : Blo 1953435 17828417 := bstep (se 2 (by rfl) ⟨6685656, by rfl⟩ : syracuseStep 17828417 = 13371313) B13371313
theorem B11885611 : Blo 1953435 11885611 := bstep (se 1 (by rfl) ⟨8914208, by rfl⟩ : syracuseStep 11885611 = 17828417) B17828417
theorem B15847481 : Blo 1953435 15847481 := bstep (se 2 (by rfl) ⟨5942805, by rfl⟩ : syracuseStep 15847481 = 11885611) B11885611
theorem B10564987 : Blo 1953435 10564987 := bstep (se 1 (by rfl) ⟨7923740, by rfl⟩ : syracuseStep 10564987 = 15847481) B15847481
theorem B14086649 : Blo 1953435 14086649 := bstep (se 2 (by rfl) ⟨5282493, by rfl⟩ : syracuseStep 14086649 = 10564987) B10564987
theorem B9391099 : Blo 1953435 9391099 := bstep (se 1 (by rfl) ⟨7043324, by rfl⟩ : syracuseStep 9391099 = 14086649) B14086649
theorem B12521465 : Blo 1953435 12521465 := bstep (se 2 (by rfl) ⟨4695549, by rfl⟩ : syracuseStep 12521465 = 9391099) B9391099
theorem B8347643 : Blo 1953435 8347643 := bstep (se 1 (by rfl) ⟨6260732, by rfl⟩ : syracuseStep 8347643 = 12521465) B12521465
theorem B5565095 : Blo 1953435 5565095 := bstep (se 1 (by rfl) ⟨4173821, by rfl⟩ : syracuseStep 5565095 = 8347643) B8347643
theorem B3710063 : Blo 1953435 3710063 := bstep (se 1 (by rfl) ⟨2782547, by rfl⟩ : syracuseStep 3710063 = 5565095) B5565095
theorem B9893501 : Blo 1953435 9893501 := bstep (se 3 (by rfl) ⟨1855031, by rfl⟩ : syracuseStep 9893501 = 3710063) B3710063
theorem B6595667 : Blo 1953435 6595667 := bstep (se 1 (by rfl) ⟨4946750, by rfl⟩ : syracuseStep 6595667 = 9893501) B9893501
theorem B4397111 : Blo 1953435 4397111 := bstep (se 1 (by rfl) ⟨3297833, by rfl⟩ : syracuseStep 4397111 = 6595667) B6595667
theorem B2931407 : Blo 1953435 2931407 := bstep (se 1 (by rfl) ⟨2198555, by rfl⟩ : syracuseStep 2931407 = 4397111) B4397111
theorem B1954271 : Blo 1953435 1954271 := bstep (se 1 (by rfl) ⟨1465703, by rfl⟩ : syracuseStep 1954271 = 2931407) B2931407
theorem B2931413 : Blo 1953435 2931413 := bbase (se 7 (by rfl) ⟨34352, by rfl⟩ : syracuseStep 2931413 = 68705) (by norm_num)
theorem B1954275 : Blo 1953435 1954275 := bstep (se 1 (by rfl) ⟨1465706, by rfl⟩ : syracuseStep 1954275 = 2931413) B2931413
theorem B14086709 : Blo 1953435 14086709 := bbase (se 5 (by rfl) ⟨660314, by rfl⟩ : syracuseStep 14086709 = 1320629) (by norm_num)
theorem B9391139 : Blo 1953435 9391139 := bstep (se 1 (by rfl) ⟨7043354, by rfl⟩ : syracuseStep 9391139 = 14086709) B14086709
theorem B6260759 : Blo 1953435 6260759 := bstep (se 1 (by rfl) ⟨4695569, by rfl⟩ : syracuseStep 6260759 = 9391139) B9391139
theorem B4173839 : Blo 1953435 4173839 := bstep (se 1 (by rfl) ⟨3130379, by rfl⟩ : syracuseStep 4173839 = 6260759) B6260759
theorem B2782559 : Blo 1953435 2782559 := bstep (se 1 (by rfl) ⟨2086919, by rfl⟩ : syracuseStep 2782559 = 4173839) B4173839
theorem B7420157 : Blo 1953435 7420157 := bstep (se 3 (by rfl) ⟨1391279, by rfl⟩ : syracuseStep 7420157 = 2782559) B2782559
theorem B4946771 : Blo 1953435 4946771 := bstep (se 1 (by rfl) ⟨3710078, by rfl⟩ : syracuseStep 4946771 = 7420157) B7420157
theorem B3297847 : Blo 1953435 3297847 := bstep (se 1 (by rfl) ⟨2473385, by rfl⟩ : syracuseStep 3297847 = 4946771) B4946771
theorem B4397129 : Blo 1953435 4397129 := bstep (se 2 (by rfl) ⟨1648923, by rfl⟩ : syracuseStep 4397129 = 3297847) B3297847
theorem B2931419 : Blo 1953435 2931419 := bstep (se 1 (by rfl) ⟨2198564, by rfl⟩ : syracuseStep 2931419 = 4397129) B4397129
theorem B1954279 : Blo 1953435 1954279 := bstep (se 1 (by rfl) ⟨1465709, by rfl⟩ : syracuseStep 1954279 = 2931419) B2931419
theorem B2198569 : Blo 1953435 2198569 := bbase (se 2 (by rfl) ⟨824463, by rfl⟩ : syracuseStep 2198569 = 1648927) (by norm_num)
theorem B2931425 : Blo 1953435 2931425 := bstep (se 2 (by rfl) ⟨1099284, by rfl⟩ : syracuseStep 2931425 = 2198569) B2198569
theorem B1954283 : Blo 1953435 1954283 := bstep (se 1 (by rfl) ⟨1465712, by rfl⟩ : syracuseStep 1954283 = 2931425) B2931425
theorem B2115401 : Blo 1953435 2115401 := bbase (se 2 (by rfl) ⟨793275, by rfl⟩ : syracuseStep 2115401 = 1586551) (by norm_num)
theorem B5641069 : Blo 1953435 5641069 := bstep (se 3 (by rfl) ⟨1057700, by rfl⟩ : syracuseStep 5641069 = 2115401) B2115401
theorem B7521425 : Blo 1953435 7521425 := bstep (se 2 (by rfl) ⟨2820534, by rfl⟩ : syracuseStep 7521425 = 5641069) B5641069
theorem B5014283 : Blo 1953435 5014283 := bstep (se 1 (by rfl) ⟨3760712, by rfl⟩ : syracuseStep 5014283 = 7521425) B7521425
theorem B13371421 : Blo 1953435 13371421 := bstep (se 3 (by rfl) ⟨2507141, by rfl⟩ : syracuseStep 13371421 = 5014283) B5014283
theorem B17828561 : Blo 1953435 17828561 := bstep (se 2 (by rfl) ⟨6685710, by rfl⟩ : syracuseStep 17828561 = 13371421) B13371421
theorem B11885707 : Blo 1953435 11885707 := bstep (se 1 (by rfl) ⟨8914280, by rfl⟩ : syracuseStep 11885707 = 17828561) B17828561
theorem B63390437 : Blo 1953435 63390437 := bstep (se 4 (by rfl) ⟨5942853, by rfl⟩ : syracuseStep 63390437 = 11885707) B11885707
theorem B42260291 : Blo 1953435 42260291 := bstep (se 1 (by rfl) ⟨31695218, by rfl⟩ : syracuseStep 42260291 = 63390437) B63390437
theorem B28173527 : Blo 1953435 28173527 := bstep (se 1 (by rfl) ⟨21130145, by rfl⟩ : syracuseStep 28173527 = 42260291) B42260291
theorem B18782351 : Blo 1953435 18782351 := bstep (se 1 (by rfl) ⟨14086763, by rfl⟩ : syracuseStep 18782351 = 28173527) B28173527
theorem B12521567 : Blo 1953435 12521567 := bstep (se 1 (by rfl) ⟨9391175, by rfl⟩ : syracuseStep 12521567 = 18782351) B18782351
theorem B8347711 : Blo 1953435 8347711 := bstep (se 1 (by rfl) ⟨6260783, by rfl⟩ : syracuseStep 8347711 = 12521567) B12521567
theorem B11130281 : Blo 1953435 11130281 := bstep (se 2 (by rfl) ⟨4173855, by rfl⟩ : syracuseStep 11130281 = 8347711) B8347711
theorem B7420187 : Blo 1953435 7420187 := bstep (se 1 (by rfl) ⟨5565140, by rfl⟩ : syracuseStep 7420187 = 11130281) B11130281
theorem B4946791 : Blo 1953435 4946791 := bstep (se 1 (by rfl) ⟨3710093, by rfl⟩ : syracuseStep 4946791 = 7420187) B7420187
theorem B6595721 : Blo 1953435 6595721 := bstep (se 2 (by rfl) ⟨2473395, by rfl⟩ : syracuseStep 6595721 = 4946791) B4946791
theorem B4397147 : Blo 1953435 4397147 := bstep (se 1 (by rfl) ⟨3297860, by rfl⟩ : syracuseStep 4397147 = 6595721) B6595721
theorem B2931431 : Blo 1953435 2931431 := bstep (se 1 (by rfl) ⟨2198573, by rfl⟩ : syracuseStep 2931431 = 4397147) B4397147
theorem B1954287 : Blo 1953435 1954287 := bstep (se 1 (by rfl) ⟨1465715, by rfl⟩ : syracuseStep 1954287 = 2931431) B2931431
theorem B2931437 : Blo 1953435 2931437 := bbase (se 3 (by rfl) ⟨549644, by rfl⟩ : syracuseStep 2931437 = 1099289) (by norm_num)
theorem B1954291 : Blo 1953435 1954291 := bstep (se 1 (by rfl) ⟨1465718, by rfl⟩ : syracuseStep 1954291 = 2931437) B2931437
theorem B4397165 : Blo 1953435 4397165 := bbase (se 3 (by rfl) ⟨824468, by rfl⟩ : syracuseStep 4397165 = 1648937) (by norm_num)
theorem B2931443 : Blo 1953435 2931443 := bstep (se 1 (by rfl) ⟨2198582, by rfl⟩ : syracuseStep 2931443 = 4397165) B4397165
theorem B1954295 : Blo 1953435 1954295 := bstep (se 1 (by rfl) ⟨1465721, by rfl⟩ : syracuseStep 1954295 = 2931443) B2931443
theorem B3710117 : Blo 1953435 3710117 := bbase (se 4 (by rfl) ⟨347823, by rfl⟩ : syracuseStep 3710117 = 695647) (by norm_num)
theorem B2473411 : Blo 1953435 2473411 := bstep (se 1 (by rfl) ⟨1855058, by rfl⟩ : syracuseStep 2473411 = 3710117) B3710117
theorem B3297881 : Blo 1953435 3297881 := bstep (se 2 (by rfl) ⟨1236705, by rfl⟩ : syracuseStep 3297881 = 2473411) B2473411
theorem B2198587 : Blo 1953435 2198587 := bstep (se 1 (by rfl) ⟨1648940, by rfl⟩ : syracuseStep 2198587 = 3297881) B3297881
theorem B2931449 : Blo 1953435 2931449 := bstep (se 2 (by rfl) ⟨1099293, by rfl⟩ : syracuseStep 2931449 = 2198587) B2198587
theorem B1954299 : Blo 1953435 1954299 := bstep (se 1 (by rfl) ⟨1465724, by rfl⟩ : syracuseStep 1954299 = 2931449) B2931449
theorem B5014325 : Blo 1953435 5014325 := bbase (se 5 (by rfl) ⟨235046, by rfl⟩ : syracuseStep 5014325 = 470093) (by norm_num)
theorem B3342883 : Blo 1953435 3342883 := bstep (se 1 (by rfl) ⟨2507162, by rfl⟩ : syracuseStep 3342883 = 5014325) B5014325
theorem B4457177 : Blo 1953435 4457177 := bstep (se 2 (by rfl) ⟨1671441, by rfl⟩ : syracuseStep 4457177 = 3342883) B3342883
theorem B2971451 : Blo 1953435 2971451 := bstep (se 1 (by rfl) ⟨2228588, by rfl⟩ : syracuseStep 2971451 = 4457177) B4457177
theorem B7923869 : Blo 1953435 7923869 := bstep (se 3 (by rfl) ⟨1485725, by rfl⟩ : syracuseStep 7923869 = 2971451) B2971451
theorem B5282579 : Blo 1953435 5282579 := bstep (se 1 (by rfl) ⟨3961934, by rfl⟩ : syracuseStep 5282579 = 7923869) B7923869
theorem B14086877 : Blo 1953435 14086877 := bstep (se 3 (by rfl) ⟨2641289, by rfl⟩ : syracuseStep 14086877 = 5282579) B5282579
theorem B37565005 : Blo 1953435 37565005 := bstep (se 3 (by rfl) ⟨7043438, by rfl⟩ : syracuseStep 37565005 = 14086877) B14086877
theorem B50086673 : Blo 1953435 50086673 := bstep (se 2 (by rfl) ⟨18782502, by rfl⟩ : syracuseStep 50086673 = 37565005) B37565005
theorem B33391115 : Blo 1953435 33391115 := bstep (se 1 (by rfl) ⟨25043336, by rfl⟩ : syracuseStep 33391115 = 50086673) B50086673
theorem B22260743 : Blo 1953435 22260743 := bstep (se 1 (by rfl) ⟨16695557, by rfl⟩ : syracuseStep 22260743 = 33391115) B33391115
theorem B14840495 : Blo 1953435 14840495 := bstep (se 1 (by rfl) ⟨11130371, by rfl⟩ : syracuseStep 14840495 = 22260743) B22260743
theorem B9893663 : Blo 1953435 9893663 := bstep (se 1 (by rfl) ⟨7420247, by rfl⟩ : syracuseStep 9893663 = 14840495) B14840495
theorem B6595775 : Blo 1953435 6595775 := bstep (se 1 (by rfl) ⟨4946831, by rfl⟩ : syracuseStep 6595775 = 9893663) B9893663
theorem B4397183 : Blo 1953435 4397183 := bstep (se 1 (by rfl) ⟨3297887, by rfl⟩ : syracuseStep 4397183 = 6595775) B6595775
theorem B2931455 : Blo 1953435 2931455 := bstep (se 1 (by rfl) ⟨2198591, by rfl⟩ : syracuseStep 2931455 = 4397183) B4397183
theorem B1954303 : Blo 1953435 1954303 := bstep (se 1 (by rfl) ⟨1465727, by rfl⟩ : syracuseStep 1954303 = 2931455) B2931455
theorem B2931461 : Blo 1953435 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B1954307 : Blo 1953435 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B3297901 : Blo 1953435 3297901 := bbase (se 3 (by rfl) ⟨618356, by rfl⟩ : syracuseStep 3297901 = 1236713) (by norm_num)
theorem B4397201 : Blo 1953435 4397201 := bstep (se 2 (by rfl) ⟨1648950, by rfl⟩ : syracuseStep 4397201 = 3297901) B3297901
theorem B2931467 : Blo 1953435 2931467 := bstep (se 1 (by rfl) ⟨2198600, by rfl⟩ : syracuseStep 2931467 = 4397201) B4397201
theorem B1954311 : Blo 1953435 1954311 := bstep (se 1 (by rfl) ⟨1465733, by rfl⟩ : syracuseStep 1954311 = 2931467) B2931467
theorem B2198605 : Blo 1953435 2198605 := bbase (se 3 (by rfl) ⟨412238, by rfl⟩ : syracuseStep 2198605 = 824477) (by norm_num)
theorem B2931473 : Blo 1953435 2931473 := bstep (se 2 (by rfl) ⟨1099302, by rfl⟩ : syracuseStep 2931473 = 2198605) B2198605
theorem B1954315 : Blo 1953435 1954315 := bstep (se 1 (by rfl) ⟨1465736, by rfl⟩ : syracuseStep 1954315 = 2931473) B2931473
theorem B6595829 : Blo 1953435 6595829 := bbase (se 5 (by rfl) ⟨309179, by rfl⟩ : syracuseStep 6595829 = 618359) (by norm_num)
theorem B4397219 : Blo 1953435 4397219 := bstep (se 1 (by rfl) ⟨3297914, by rfl⟩ : syracuseStep 4397219 = 6595829) B6595829
theorem B2931479 : Blo 1953435 2931479 := bstep (se 1 (by rfl) ⟨2198609, by rfl⟩ : syracuseStep 2931479 = 4397219) B4397219
theorem B1954319 : Blo 1953435 1954319 := bstep (se 1 (by rfl) ⟨1465739, by rfl⟩ : syracuseStep 1954319 = 2931479) B2931479
theorem B2931485 : Blo 1953435 2931485 := bbase (se 3 (by rfl) ⟨549653, by rfl⟩ : syracuseStep 2931485 = 1099307) (by norm_num)
theorem B1954323 : Blo 1953435 1954323 := bstep (se 1 (by rfl) ⟨1465742, by rfl⟩ : syracuseStep 1954323 = 2931485) B2931485
theorem B4397237 : Blo 1953435 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B2931491 : Blo 1953435 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B1954327 : Blo 1953435 1954327 := bstep (se 1 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 1954327 = 2931491) B2931491
theorem B12048149 : Blo 1953435 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B32128397 : Blo 1953435 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B21418931 : Blo 1953435 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B57117149 : Blo 1953435 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B38078099 : Blo 1953435 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B25385399 : Blo 1953435 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B16923599 : Blo 1953435 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B11282399 : Blo 1953435 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B7521599 : Blo 1953435 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B5014399 : Blo 1953435 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B6685865 : Blo 1953435 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B4457243 : Blo 1953435 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B2971495 : Blo 1953435 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B15847973 : Blo 1953435 15847973 := bstep (se 4 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 15847973 = 2971495) B2971495
theorem B10565315 : Blo 1953435 10565315 := bstep (se 1 (by rfl) ⟨7923986, by rfl⟩ : syracuseStep 10565315 = 15847973) B15847973
theorem B7043543 : Blo 1953435 7043543 := bstep (se 1 (by rfl) ⟨5282657, by rfl⟩ : syracuseStep 7043543 = 10565315) B10565315
theorem B4695695 : Blo 1953435 4695695 := bstep (se 1 (by rfl) ⟨3521771, by rfl⟩ : syracuseStep 4695695 = 7043543) B7043543
theorem B3130463 : Blo 1953435 3130463 := bstep (se 1 (by rfl) ⟨2347847, by rfl⟩ : syracuseStep 3130463 = 4695695) B4695695
theorem B2086975 : Blo 1953435 2086975 := bstep (se 1 (by rfl) ⟨1565231, by rfl⟩ : syracuseStep 2086975 = 3130463) B3130463
theorem B11130533 : Blo 1953435 11130533 := bstep (se 4 (by rfl) ⟨1043487, by rfl⟩ : syracuseStep 11130533 = 2086975) B2086975
theorem B7420355 : Blo 1953435 7420355 := bstep (se 1 (by rfl) ⟨5565266, by rfl⟩ : syracuseStep 7420355 = 11130533) B11130533
theorem B4946903 : Blo 1953435 4946903 := bstep (se 1 (by rfl) ⟨3710177, by rfl⟩ : syracuseStep 4946903 = 7420355) B7420355
theorem B3297935 : Blo 1953435 3297935 := bstep (se 1 (by rfl) ⟨2473451, by rfl⟩ : syracuseStep 3297935 = 4946903) B4946903
theorem B2198623 : Blo 1953435 2198623 := bstep (se 1 (by rfl) ⟨1648967, by rfl⟩ : syracuseStep 2198623 = 3297935) B3297935
theorem B2931497 : Blo 1953435 2931497 := bstep (se 2 (by rfl) ⟨1099311, by rfl⟩ : syracuseStep 2931497 = 2198623) B2198623
theorem B1954331 : Blo 1953435 1954331 := bstep (se 1 (by rfl) ⟨1465748, by rfl⟩ : syracuseStep 1954331 = 2931497) B2931497
theorem B3130469 : Blo 1953435 3130469 := bbase (se 4 (by rfl) ⟨293481, by rfl⟩ : syracuseStep 3130469 = 586963) (by norm_num)
theorem B2086979 : Blo 1953435 2086979 := bstep (se 1 (by rfl) ⟨1565234, by rfl⟩ : syracuseStep 2086979 = 3130469) B3130469
theorem B5565277 : Blo 1953435 5565277 := bstep (se 3 (by rfl) ⟨1043489, by rfl⟩ : syracuseStep 5565277 = 2086979) B2086979
theorem B7420369 : Blo 1953435 7420369 := bstep (se 2 (by rfl) ⟨2782638, by rfl⟩ : syracuseStep 7420369 = 5565277) B5565277
theorem B9893825 : Blo 1953435 9893825 := bstep (se 2 (by rfl) ⟨3710184, by rfl⟩ : syracuseStep 9893825 = 7420369) B7420369
theorem B6595883 : Blo 1953435 6595883 := bstep (se 1 (by rfl) ⟨4946912, by rfl⟩ : syracuseStep 6595883 = 9893825) B9893825
theorem B4397255 : Blo 1953435 4397255 := bstep (se 1 (by rfl) ⟨3297941, by rfl⟩ : syracuseStep 4397255 = 6595883) B6595883
theorem B2931503 : Blo 1953435 2931503 := bstep (se 1 (by rfl) ⟨2198627, by rfl⟩ : syracuseStep 2931503 = 4397255) B4397255
theorem B1954335 : Blo 1953435 1954335 := bstep (se 1 (by rfl) ⟨1465751, by rfl⟩ : syracuseStep 1954335 = 2931503) B2931503
theorem B2931509 : Blo 1953435 2931509 := bbase (se 5 (by rfl) ⟨137414, by rfl⟩ : syracuseStep 2931509 = 274829) (by norm_num)
theorem B1954339 : Blo 1953435 1954339 := bstep (se 1 (by rfl) ⟨1465754, by rfl⟩ : syracuseStep 1954339 = 2931509) B2931509
theorem B4946933 : Blo 1953435 4946933 := bbase (se 5 (by rfl) ⟨231887, by rfl⟩ : syracuseStep 4946933 = 463775) (by norm_num)
theorem B3297955 : Blo 1953435 3297955 := bstep (se 1 (by rfl) ⟨2473466, by rfl⟩ : syracuseStep 3297955 = 4946933) B4946933
theorem B4397273 : Blo 1953435 4397273 := bstep (se 2 (by rfl) ⟨1648977, by rfl⟩ : syracuseStep 4397273 = 3297955) B3297955
theorem B2931515 : Blo 1953435 2931515 := bstep (se 1 (by rfl) ⟨2198636, by rfl⟩ : syracuseStep 2931515 = 4397273) B4397273
theorem B1954343 : Blo 1953435 1954343 := bstep (se 1 (by rfl) ⟨1465757, by rfl⟩ : syracuseStep 1954343 = 2931515) B2931515
theorem B2198641 : Blo 1953435 2198641 := bbase (se 2 (by rfl) ⟨824490, by rfl⟩ : syracuseStep 2198641 = 1648981) (by norm_num)
theorem B2931521 : Blo 1953435 2931521 := bstep (se 2 (by rfl) ⟨1099320, by rfl⟩ : syracuseStep 2931521 = 2198641) B2198641
theorem B1954347 : Blo 1953435 1954347 := bstep (se 1 (by rfl) ⟨1465760, by rfl⟩ : syracuseStep 1954347 = 2931521) B2931521
theorem B11886101 : Blo 1953435 11886101 := bbase (se 6 (by rfl) ⟨278580, by rfl⟩ : syracuseStep 11886101 = 557161) (by norm_num)
theorem B7924067 : Blo 1953435 7924067 := bstep (se 1 (by rfl) ⟨5943050, by rfl⟩ : syracuseStep 7924067 = 11886101) B11886101
theorem B5282711 : Blo 1953435 5282711 := bstep (se 1 (by rfl) ⟨3962033, by rfl⟩ : syracuseStep 5282711 = 7924067) B7924067
theorem B3521807 : Blo 1953435 3521807 := bstep (se 1 (by rfl) ⟨2641355, by rfl⟩ : syracuseStep 3521807 = 5282711) B5282711
theorem B2347871 : Blo 1953435 2347871 := bstep (se 1 (by rfl) ⟨1760903, by rfl⟩ : syracuseStep 2347871 = 3521807) B3521807
theorem B6260989 : Blo 1953435 6260989 := bstep (se 3 (by rfl) ⟨1173935, by rfl⟩ : syracuseStep 6260989 = 2347871) B2347871
theorem B8347985 : Blo 1953435 8347985 := bstep (se 2 (by rfl) ⟨3130494, by rfl⟩ : syracuseStep 8347985 = 6260989) B6260989
theorem B5565323 : Blo 1953435 5565323 := bstep (se 1 (by rfl) ⟨4173992, by rfl⟩ : syracuseStep 5565323 = 8347985) B8347985
theorem B3710215 : Blo 1953435 3710215 := bstep (se 1 (by rfl) ⟨2782661, by rfl⟩ : syracuseStep 3710215 = 5565323) B5565323
theorem B4946953 : Blo 1953435 4946953 := bstep (se 2 (by rfl) ⟨1855107, by rfl⟩ : syracuseStep 4946953 = 3710215) B3710215
theorem B6595937 : Blo 1953435 6595937 := bstep (se 2 (by rfl) ⟨2473476, by rfl⟩ : syracuseStep 6595937 = 4946953) B4946953
theorem B4397291 : Blo 1953435 4397291 := bstep (se 1 (by rfl) ⟨3297968, by rfl⟩ : syracuseStep 4397291 = 6595937) B6595937
theorem B2931527 : Blo 1953435 2931527 := bstep (se 1 (by rfl) ⟨2198645, by rfl⟩ : syracuseStep 2931527 = 4397291) B4397291
theorem B1954351 : Blo 1953435 1954351 := bstep (se 1 (by rfl) ⟨1465763, by rfl⟩ : syracuseStep 1954351 = 2931527) B2931527
theorem B2931533 : Blo 1953435 2931533 := bbase (se 3 (by rfl) ⟨549662, by rfl⟩ : syracuseStep 2931533 = 1099325) (by norm_num)
theorem B1954355 : Blo 1953435 1954355 := bstep (se 1 (by rfl) ⟨1465766, by rfl⟩ : syracuseStep 1954355 = 2931533) B2931533
theorem B4397309 : Blo 1953435 4397309 := bbase (se 3 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 4397309 = 1648991) (by norm_num)
theorem B2931539 : Blo 1953435 2931539 := bstep (se 1 (by rfl) ⟨2198654, by rfl⟩ : syracuseStep 2931539 = 4397309) B4397309
theorem B1954359 : Blo 1953435 1954359 := bstep (se 1 (by rfl) ⟨1465769, by rfl⟩ : syracuseStep 1954359 = 2931539) B2931539
theorem B3297989 : Blo 1953435 3297989 := bbase (se 4 (by rfl) ⟨309186, by rfl⟩ : syracuseStep 3297989 = 618373) (by norm_num)
theorem B2198659 : Blo 1953435 2198659 := bstep (se 1 (by rfl) ⟨1648994, by rfl⟩ : syracuseStep 2198659 = 3297989) B3297989
theorem B2931545 : Blo 1953435 2931545 := bstep (se 2 (by rfl) ⟨1099329, by rfl⟩ : syracuseStep 2931545 = 2198659) B2198659
theorem B1954363 : Blo 1953435 1954363 := bstep (se 1 (by rfl) ⟨1465772, by rfl⟩ : syracuseStep 1954363 = 2931545) B2931545
theorem B14840981 : Blo 1953435 14840981 := bbase (se 6 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 14840981 = 695671) (by norm_num)
theorem B9893987 : Blo 1953435 9893987 := bstep (se 1 (by rfl) ⟨7420490, by rfl⟩ : syracuseStep 9893987 = 14840981) B14840981
theorem B6595991 : Blo 1953435 6595991 := bstep (se 1 (by rfl) ⟨4946993, by rfl⟩ : syracuseStep 6595991 = 9893987) B9893987
theorem B4397327 : Blo 1953435 4397327 := bstep (se 1 (by rfl) ⟨3297995, by rfl⟩ : syracuseStep 4397327 = 6595991) B6595991
theorem B2931551 : Blo 1953435 2931551 := bstep (se 1 (by rfl) ⟨2198663, by rfl⟩ : syracuseStep 2931551 = 4397327) B4397327
theorem B1954367 : Blo 1953435 1954367 := bstep (se 1 (by rfl) ⟨1465775, by rfl⟩ : syracuseStep 1954367 = 2931551) B2931551
theorem B2931557 : Blo 1953435 2931557 := bbase (se 4 (by rfl) ⟨274833, by rfl⟩ : syracuseStep 2931557 = 549667) (by norm_num)
theorem B1954371 : Blo 1953435 1954371 := bstep (se 1 (by rfl) ⟨1465778, by rfl⟩ : syracuseStep 1954371 = 2931557) B2931557
theorem B3710261 : Blo 1953435 3710261 := bbase (se 5 (by rfl) ⟨173918, by rfl⟩ : syracuseStep 3710261 = 347837) (by norm_num)
theorem B2473507 : Blo 1953435 2473507 := bstep (se 1 (by rfl) ⟨1855130, by rfl⟩ : syracuseStep 2473507 = 3710261) B3710261
theorem B3298009 : Blo 1953435 3298009 := bstep (se 2 (by rfl) ⟨1236753, by rfl⟩ : syracuseStep 3298009 = 2473507) B2473507
theorem B4397345 : Blo 1953435 4397345 := bstep (se 2 (by rfl) ⟨1649004, by rfl⟩ : syracuseStep 4397345 = 3298009) B3298009
theorem B2931563 : Blo 1953435 2931563 := bstep (se 1 (by rfl) ⟨2198672, by rfl⟩ : syracuseStep 2931563 = 4397345) B4397345
theorem B1954375 : Blo 1953435 1954375 := bstep (se 1 (by rfl) ⟨1465781, by rfl⟩ : syracuseStep 1954375 = 2931563) B2931563
theorem B2198677 : Blo 1953435 2198677 := bbase (se 6 (by rfl) ⟨51531, by rfl⟩ : syracuseStep 2198677 = 103063) (by norm_num)
theorem B2931569 : Blo 1953435 2931569 := bstep (se 2 (by rfl) ⟨1099338, by rfl⟩ : syracuseStep 2931569 = 2198677) B2198677
theorem B1954379 : Blo 1953435 1954379 := bstep (se 1 (by rfl) ⟨1465784, by rfl⟩ : syracuseStep 1954379 = 2931569) B2931569
theorem B2473517 : Blo 1953435 2473517 := bbase (se 3 (by rfl) ⟨463784, by rfl⟩ : syracuseStep 2473517 = 927569) (by norm_num)
theorem B6596045 : Blo 1953435 6596045 := bstep (se 3 (by rfl) ⟨1236758, by rfl⟩ : syracuseStep 6596045 = 2473517) B2473517
theorem B4397363 : Blo 1953435 4397363 := bstep (se 1 (by rfl) ⟨3298022, by rfl⟩ : syracuseStep 4397363 = 6596045) B6596045
theorem B2931575 : Blo 1953435 2931575 := bstep (se 1 (by rfl) ⟨2198681, by rfl⟩ : syracuseStep 2931575 = 4397363) B4397363
theorem B1954383 : Blo 1953435 1954383 := bstep (se 1 (by rfl) ⟨1465787, by rfl⟩ : syracuseStep 1954383 = 2931575) B2931575
theorem B2931581 : Blo 1953435 2931581 := bbase (se 3 (by rfl) ⟨549671, by rfl⟩ : syracuseStep 2931581 = 1099343) (by norm_num)
theorem B1954387 : Blo 1953435 1954387 := bstep (se 1 (by rfl) ⟨1465790, by rfl⟩ : syracuseStep 1954387 = 2931581) B2931581
theorem B4397381 : Blo 1953435 4397381 := bbase (se 4 (by rfl) ⟨412254, by rfl⟩ : syracuseStep 4397381 = 824509) (by norm_num)
theorem B2931587 : Blo 1953435 2931587 := bstep (se 1 (by rfl) ⟨2198690, by rfl⟩ : syracuseStep 2931587 = 4397381) B4397381
theorem B1954391 : Blo 1953435 1954391 := bstep (se 1 (by rfl) ⟨1465793, by rfl⟩ : syracuseStep 1954391 = 2931587) B2931587
theorem B4457389 : Blo 1953435 4457389 := bbase (se 3 (by rfl) ⟨835760, by rfl⟩ : syracuseStep 4457389 = 1671521) (by norm_num)
theorem B5943185 : Blo 1953435 5943185 := bstep (se 2 (by rfl) ⟨2228694, by rfl⟩ : syracuseStep 5943185 = 4457389) B4457389
theorem B3962123 : Blo 1953435 3962123 := bstep (se 1 (by rfl) ⟨2971592, by rfl⟩ : syracuseStep 3962123 = 5943185) B5943185
theorem B2641415 : Blo 1953435 2641415 := bstep (se 1 (by rfl) ⟨1981061, by rfl⟩ : syracuseStep 2641415 = 3962123) B3962123
theorem B7043773 : Blo 1953435 7043773 := bstep (se 3 (by rfl) ⟨1320707, by rfl⟩ : syracuseStep 7043773 = 2641415) B2641415
theorem B9391697 : Blo 1953435 9391697 := bstep (se 2 (by rfl) ⟨3521886, by rfl⟩ : syracuseStep 9391697 = 7043773) B7043773
theorem B6261131 : Blo 1953435 6261131 := bstep (se 1 (by rfl) ⟨4695848, by rfl⟩ : syracuseStep 6261131 = 9391697) B9391697
theorem B4174087 : Blo 1953435 4174087 := bstep (se 1 (by rfl) ⟨3130565, by rfl⟩ : syracuseStep 4174087 = 6261131) B6261131
theorem B5565449 : Blo 1953435 5565449 := bstep (se 2 (by rfl) ⟨2087043, by rfl⟩ : syracuseStep 5565449 = 4174087) B4174087
theorem B3710299 : Blo 1953435 3710299 := bstep (se 1 (by rfl) ⟨2782724, by rfl⟩ : syracuseStep 3710299 = 5565449) B5565449
theorem B4947065 : Blo 1953435 4947065 := bstep (se 2 (by rfl) ⟨1855149, by rfl⟩ : syracuseStep 4947065 = 3710299) B3710299
theorem B3298043 : Blo 1953435 3298043 := bstep (se 1 (by rfl) ⟨2473532, by rfl⟩ : syracuseStep 3298043 = 4947065) B4947065
theorem B2198695 : Blo 1953435 2198695 := bstep (se 1 (by rfl) ⟨1649021, by rfl⟩ : syracuseStep 2198695 = 3298043) B3298043
theorem B2931593 : Blo 1953435 2931593 := bstep (se 2 (by rfl) ⟨1099347, by rfl⟩ : syracuseStep 2931593 = 2198695) B2198695
theorem B1954395 : Blo 1953435 1954395 := bstep (se 1 (by rfl) ⟨1465796, by rfl⟩ : syracuseStep 1954395 = 2931593) B2931593
theorem B9894149 : Blo 1953435 9894149 := bbase (se 4 (by rfl) ⟨927576, by rfl⟩ : syracuseStep 9894149 = 1855153) (by norm_num)
theorem B6596099 : Blo 1953435 6596099 := bstep (se 1 (by rfl) ⟨4947074, by rfl⟩ : syracuseStep 6596099 = 9894149) B9894149
theorem B4397399 : Blo 1953435 4397399 := bstep (se 1 (by rfl) ⟨3298049, by rfl⟩ : syracuseStep 4397399 = 6596099) B6596099
theorem B2931599 : Blo 1953435 2931599 := bstep (se 1 (by rfl) ⟨2198699, by rfl⟩ : syracuseStep 2931599 = 4397399) B4397399
theorem B1954399 : Blo 1953435 1954399 := bstep (se 1 (by rfl) ⟨1465799, by rfl⟩ : syracuseStep 1954399 = 2931599) B2931599
theorem B2931605 : Blo 1953435 2931605 := bbase (se 6 (by rfl) ⟨68709, by rfl⟩ : syracuseStep 2931605 = 137419) (by norm_num)
theorem B1954403 : Blo 1953435 1954403 := bstep (se 1 (by rfl) ⟨1465802, by rfl⟩ : syracuseStep 1954403 = 2931605) B2931605
theorem B11130965 : Blo 1953435 11130965 := bbase (se 8 (by rfl) ⟨65220, by rfl⟩ : syracuseStep 11130965 = 130441) (by norm_num)
theorem B7420643 : Blo 1953435 7420643 := bstep (se 1 (by rfl) ⟨5565482, by rfl⟩ : syracuseStep 7420643 = 11130965) B11130965
theorem B4947095 : Blo 1953435 4947095 := bstep (se 1 (by rfl) ⟨3710321, by rfl⟩ : syracuseStep 4947095 = 7420643) B7420643
theorem B3298063 : Blo 1953435 3298063 := bstep (se 1 (by rfl) ⟨2473547, by rfl⟩ : syracuseStep 3298063 = 4947095) B4947095
theorem B4397417 : Blo 1953435 4397417 := bstep (se 2 (by rfl) ⟨1649031, by rfl⟩ : syracuseStep 4397417 = 3298063) B3298063
theorem B2931611 : Blo 1953435 2931611 := bstep (se 1 (by rfl) ⟨2198708, by rfl⟩ : syracuseStep 2931611 = 4397417) B4397417
theorem B1954407 : Blo 1953435 1954407 := bstep (se 1 (by rfl) ⟨1465805, by rfl⟩ : syracuseStep 1954407 = 2931611) B2931611
theorem B2198713 : Blo 1953435 2198713 := bbase (se 2 (by rfl) ⟨824517, by rfl⟩ : syracuseStep 2198713 = 1649035) (by norm_num)
theorem B2931617 : Blo 1953435 2931617 := bstep (se 2 (by rfl) ⟨1099356, by rfl⟩ : syracuseStep 2931617 = 2198713) B2198713
theorem B1954411 : Blo 1953435 1954411 := bstep (se 1 (by rfl) ⟨1465808, by rfl⟩ : syracuseStep 1954411 = 2931617) B2931617
theorem B3130597 : Blo 1953435 3130597 := bbase (se 4 (by rfl) ⟨293493, by rfl⟩ : syracuseStep 3130597 = 586987) (by norm_num)
theorem B4174129 : Blo 1953435 4174129 := bstep (se 2 (by rfl) ⟨1565298, by rfl⟩ : syracuseStep 4174129 = 3130597) B3130597
theorem B5565505 : Blo 1953435 5565505 := bstep (se 2 (by rfl) ⟨2087064, by rfl⟩ : syracuseStep 5565505 = 4174129) B4174129
theorem B7420673 : Blo 1953435 7420673 := bstep (se 2 (by rfl) ⟨2782752, by rfl⟩ : syracuseStep 7420673 = 5565505) B5565505
theorem B4947115 : Blo 1953435 4947115 := bstep (se 1 (by rfl) ⟨3710336, by rfl⟩ : syracuseStep 4947115 = 7420673) B7420673
theorem B6596153 : Blo 1953435 6596153 := bstep (se 2 (by rfl) ⟨2473557, by rfl⟩ : syracuseStep 6596153 = 4947115) B4947115
theorem B4397435 : Blo 1953435 4397435 := bstep (se 1 (by rfl) ⟨3298076, by rfl⟩ : syracuseStep 4397435 = 6596153) B6596153
theorem B2931623 : Blo 1953435 2931623 := bstep (se 1 (by rfl) ⟨2198717, by rfl⟩ : syracuseStep 2931623 = 4397435) B4397435
theorem B1954415 : Blo 1953435 1954415 := bstep (se 1 (by rfl) ⟨1465811, by rfl⟩ : syracuseStep 1954415 = 2931623) B2931623
theorem B2931629 : Blo 1953435 2931629 := bbase (se 3 (by rfl) ⟨549680, by rfl⟩ : syracuseStep 2931629 = 1099361) (by norm_num)
theorem B1954419 : Blo 1953435 1954419 := bstep (se 1 (by rfl) ⟨1465814, by rfl⟩ : syracuseStep 1954419 = 2931629) B2931629
theorem B4397453 : Blo 1953435 4397453 := bbase (se 3 (by rfl) ⟨824522, by rfl⟩ : syracuseStep 4397453 = 1649045) (by norm_num)
theorem B2931635 : Blo 1953435 2931635 := bstep (se 1 (by rfl) ⟨2198726, by rfl⟩ : syracuseStep 2931635 = 4397453) B4397453
theorem B1954423 : Blo 1953435 1954423 := bstep (se 1 (by rfl) ⟨1465817, by rfl⟩ : syracuseStep 1954423 = 2931635) B2931635
theorem B2473573 : Blo 1953435 2473573 := bbase (se 4 (by rfl) ⟨231897, by rfl⟩ : syracuseStep 2473573 = 463795) (by norm_num)
theorem B3298097 : Blo 1953435 3298097 := bstep (se 2 (by rfl) ⟨1236786, by rfl⟩ : syracuseStep 3298097 = 2473573) B2473573
theorem B2198731 : Blo 1953435 2198731 := bstep (se 1 (by rfl) ⟨1649048, by rfl⟩ : syracuseStep 2198731 = 3298097) B3298097
theorem B2931641 : Blo 1953435 2931641 := bstep (se 2 (by rfl) ⟨1099365, by rfl⟩ : syracuseStep 2931641 = 2198731) B2198731
theorem B1954427 : Blo 1953435 1954427 := bstep (se 1 (by rfl) ⟨1465820, by rfl⟩ : syracuseStep 1954427 = 2931641) B2931641
theorem B18783733 : Blo 1953435 18783733 := bbase (se 5 (by rfl) ⟨880487, by rfl⟩ : syracuseStep 18783733 = 1760975) (by norm_num)
theorem B25044977 : Blo 1953435 25044977 := bstep (se 2 (by rfl) ⟨9391866, by rfl⟩ : syracuseStep 25044977 = 18783733) B18783733
theorem B16696651 : Blo 1953435 16696651 := bstep (se 1 (by rfl) ⟨12522488, by rfl⟩ : syracuseStep 16696651 = 25044977) B25044977
theorem B22262201 : Blo 1953435 22262201 := bstep (se 2 (by rfl) ⟨8348325, by rfl⟩ : syracuseStep 22262201 = 16696651) B16696651
theorem B14841467 : Blo 1953435 14841467 := bstep (se 1 (by rfl) ⟨11131100, by rfl⟩ : syracuseStep 14841467 = 22262201) B22262201
theorem B9894311 : Blo 1953435 9894311 := bstep (se 1 (by rfl) ⟨7420733, by rfl⟩ : syracuseStep 9894311 = 14841467) B14841467
theorem B6596207 : Blo 1953435 6596207 := bstep (se 1 (by rfl) ⟨4947155, by rfl⟩ : syracuseStep 6596207 = 9894311) B9894311
theorem B4397471 : Blo 1953435 4397471 := bstep (se 1 (by rfl) ⟨3298103, by rfl⟩ : syracuseStep 4397471 = 6596207) B6596207
theorem B2931647 : Blo 1953435 2931647 := bstep (se 1 (by rfl) ⟨2198735, by rfl⟩ : syracuseStep 2931647 = 4397471) B4397471
theorem B1954431 : Blo 1953435 1954431 := bstep (se 1 (by rfl) ⟨1465823, by rfl⟩ : syracuseStep 1954431 = 2931647) B2931647
theorem B2931653 : Blo 1953435 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B1954435 : Blo 1953435 1954435 := bstep (se 1 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 1954435 = 2931653) B2931653
theorem B3298117 : Blo 1953435 3298117 := bbase (se 4 (by rfl) ⟨309198, by rfl⟩ : syracuseStep 3298117 = 618397) (by norm_num)
theorem B4397489 : Blo 1953435 4397489 := bstep (se 2 (by rfl) ⟨1649058, by rfl⟩ : syracuseStep 4397489 = 3298117) B3298117
theorem B2931659 : Blo 1953435 2931659 := bstep (se 1 (by rfl) ⟨2198744, by rfl⟩ : syracuseStep 2931659 = 4397489) B4397489
theorem B1954439 : Blo 1953435 1954439 := bstep (se 1 (by rfl) ⟨1465829, by rfl⟩ : syracuseStep 1954439 = 2931659) B2931659
theorem B2198749 : Blo 1953435 2198749 := bbase (se 3 (by rfl) ⟨412265, by rfl⟩ : syracuseStep 2198749 = 824531) (by norm_num)
theorem B2931665 : Blo 1953435 2931665 := bstep (se 2 (by rfl) ⟨1099374, by rfl⟩ : syracuseStep 2931665 = 2198749) B2198749
theorem B1954443 : Blo 1953435 1954443 := bstep (se 1 (by rfl) ⟨1465832, by rfl⟩ : syracuseStep 1954443 = 2931665) B2931665
theorem B6596261 : Blo 1953435 6596261 := bbase (se 4 (by rfl) ⟨618399, by rfl⟩ : syracuseStep 6596261 = 1236799) (by norm_num)
theorem B4397507 : Blo 1953435 4397507 := bstep (se 1 (by rfl) ⟨3298130, by rfl⟩ : syracuseStep 4397507 = 6596261) B6596261
theorem B2931671 : Blo 1953435 2931671 := bstep (se 1 (by rfl) ⟨2198753, by rfl⟩ : syracuseStep 2931671 = 4397507) B4397507
theorem B1954447 : Blo 1953435 1954447 := bstep (se 1 (by rfl) ⟨1465835, by rfl⟩ : syracuseStep 1954447 = 2931671) B2931671
theorem B2931677 : Blo 1953435 2931677 := bbase (se 3 (by rfl) ⟨549689, by rfl⟩ : syracuseStep 2931677 = 1099379) (by norm_num)
theorem B1954451 : Blo 1953435 1954451 := bstep (se 1 (by rfl) ⟨1465838, by rfl⟩ : syracuseStep 1954451 = 2931677) B2931677
theorem B4397525 : Blo 1953435 4397525 := bbase (se 7 (by rfl) ⟨51533, by rfl⟩ : syracuseStep 4397525 = 103067) (by norm_num)
theorem B2931683 : Blo 1953435 2931683 := bstep (se 1 (by rfl) ⟨2198762, by rfl⟩ : syracuseStep 2931683 = 4397525) B4397525
theorem B1954455 : Blo 1953435 1954455 := bstep (se 1 (by rfl) ⟨1465841, by rfl⟩ : syracuseStep 1954455 = 2931683) B2931683
theorem B17830133 : Blo 1953435 17830133 := bbase (se 5 (by rfl) ⟨835787, by rfl⟩ : syracuseStep 17830133 = 1671575) (by norm_num)
theorem B11886755 : Blo 1953435 11886755 := bstep (se 1 (by rfl) ⟨8915066, by rfl⟩ : syracuseStep 11886755 = 17830133) B17830133
theorem B31698013 : Blo 1953435 31698013 := bstep (se 3 (by rfl) ⟨5943377, by rfl⟩ : syracuseStep 31698013 = 11886755) B11886755
theorem B42264017 : Blo 1953435 42264017 := bstep (se 2 (by rfl) ⟨15849006, by rfl⟩ : syracuseStep 42264017 = 31698013) B31698013
theorem B28176011 : Blo 1953435 28176011 := bstep (se 1 (by rfl) ⟨21132008, by rfl⟩ : syracuseStep 28176011 = 42264017) B42264017
theorem B18784007 : Blo 1953435 18784007 := bstep (se 1 (by rfl) ⟨14088005, by rfl⟩ : syracuseStep 18784007 = 28176011) B28176011
theorem B12522671 : Blo 1953435 12522671 := bstep (se 1 (by rfl) ⟨9392003, by rfl⟩ : syracuseStep 12522671 = 18784007) B18784007
theorem B8348447 : Blo 1953435 8348447 := bstep (se 1 (by rfl) ⟨6261335, by rfl⟩ : syracuseStep 8348447 = 12522671) B12522671
theorem B5565631 : Blo 1953435 5565631 := bstep (se 1 (by rfl) ⟨4174223, by rfl⟩ : syracuseStep 5565631 = 8348447) B8348447
theorem B7420841 : Blo 1953435 7420841 := bstep (se 2 (by rfl) ⟨2782815, by rfl⟩ : syracuseStep 7420841 = 5565631) B5565631
theorem B4947227 : Blo 1953435 4947227 := bstep (se 1 (by rfl) ⟨3710420, by rfl⟩ : syracuseStep 4947227 = 7420841) B7420841
theorem B3298151 : Blo 1953435 3298151 := bstep (se 1 (by rfl) ⟨2473613, by rfl⟩ : syracuseStep 3298151 = 4947227) B4947227
theorem B2198767 : Blo 1953435 2198767 := bstep (se 1 (by rfl) ⟨1649075, by rfl⟩ : syracuseStep 2198767 = 3298151) B3298151
theorem B2931689 : Blo 1953435 2931689 := bstep (se 2 (by rfl) ⟨1099383, by rfl⟩ : syracuseStep 2931689 = 2198767) B2198767
theorem B1954459 : Blo 1953435 1954459 := bstep (se 1 (by rfl) ⟨1465844, by rfl⟩ : syracuseStep 1954459 = 2931689) B2931689
theorem B9392021 : Blo 1953435 9392021 := bbase (se 6 (by rfl) ⟨220125, by rfl⟩ : syracuseStep 9392021 = 440251) (by norm_num)
theorem B6261347 : Blo 1953435 6261347 := bstep (se 1 (by rfl) ⟨4696010, by rfl⟩ : syracuseStep 6261347 = 9392021) B9392021
theorem B16696925 : Blo 1953435 16696925 := bstep (se 3 (by rfl) ⟨3130673, by rfl⟩ : syracuseStep 16696925 = 6261347) B6261347
theorem B11131283 : Blo 1953435 11131283 := bstep (se 1 (by rfl) ⟨8348462, by rfl⟩ : syracuseStep 11131283 = 16696925) B16696925
theorem B7420855 : Blo 1953435 7420855 := bstep (se 1 (by rfl) ⟨5565641, by rfl⟩ : syracuseStep 7420855 = 11131283) B11131283
theorem B9894473 : Blo 1953435 9894473 := bstep (se 2 (by rfl) ⟨3710427, by rfl⟩ : syracuseStep 9894473 = 7420855) B7420855
theorem B6596315 : Blo 1953435 6596315 := bstep (se 1 (by rfl) ⟨4947236, by rfl⟩ : syracuseStep 6596315 = 9894473) B9894473
theorem B4397543 : Blo 1953435 4397543 := bstep (se 1 (by rfl) ⟨3298157, by rfl⟩ : syracuseStep 4397543 = 6596315) B6596315
theorem B2931695 : Blo 1953435 2931695 := bstep (se 1 (by rfl) ⟨2198771, by rfl⟩ : syracuseStep 2931695 = 4397543) B4397543
theorem B1954463 : Blo 1953435 1954463 := bstep (se 1 (by rfl) ⟨1465847, by rfl⟩ : syracuseStep 1954463 = 2931695) B2931695
theorem B2931701 : Blo 1953435 2931701 := bbase (se 5 (by rfl) ⟨137423, by rfl⟩ : syracuseStep 2931701 = 274847) (by norm_num)
theorem B1954467 : Blo 1953435 1954467 := bstep (se 1 (by rfl) ⟨1465850, by rfl⟩ : syracuseStep 1954467 = 2931701) B2931701
theorem B5014757 : Blo 1953435 5014757 := bbase (se 4 (by rfl) ⟨470133, by rfl⟩ : syracuseStep 5014757 = 940267) (by norm_num)
theorem B13372685 : Blo 1953435 13372685 := bstep (se 3 (by rfl) ⟨2507378, by rfl⟩ : syracuseStep 13372685 = 5014757) B5014757
theorem B8915123 : Blo 1953435 8915123 := bstep (se 1 (by rfl) ⟨6686342, by rfl⟩ : syracuseStep 8915123 = 13372685) B13372685
theorem B23773661 : Blo 1953435 23773661 := bstep (se 3 (by rfl) ⟨4457561, by rfl⟩ : syracuseStep 23773661 = 8915123) B8915123
theorem B15849107 : Blo 1953435 15849107 := bstep (se 1 (by rfl) ⟨11886830, by rfl⟩ : syracuseStep 15849107 = 23773661) B23773661
theorem B10566071 : Blo 1953435 10566071 := bstep (se 1 (by rfl) ⟨7924553, by rfl⟩ : syracuseStep 10566071 = 15849107) B15849107
theorem B7044047 : Blo 1953435 7044047 := bstep (se 1 (by rfl) ⟨5283035, by rfl⟩ : syracuseStep 7044047 = 10566071) B10566071
theorem B4696031 : Blo 1953435 4696031 := bstep (se 1 (by rfl) ⟨3522023, by rfl⟩ : syracuseStep 4696031 = 7044047) B7044047
theorem B3130687 : Blo 1953435 3130687 := bstep (se 1 (by rfl) ⟨2348015, by rfl⟩ : syracuseStep 3130687 = 4696031) B4696031
theorem B4174249 : Blo 1953435 4174249 := bstep (se 2 (by rfl) ⟨1565343, by rfl⟩ : syracuseStep 4174249 = 3130687) B3130687
theorem B5565665 : Blo 1953435 5565665 := bstep (se 2 (by rfl) ⟨2087124, by rfl⟩ : syracuseStep 5565665 = 4174249) B4174249
theorem B3710443 : Blo 1953435 3710443 := bstep (se 1 (by rfl) ⟨2782832, by rfl⟩ : syracuseStep 3710443 = 5565665) B5565665
theorem B4947257 : Blo 1953435 4947257 := bstep (se 2 (by rfl) ⟨1855221, by rfl⟩ : syracuseStep 4947257 = 3710443) B3710443
theorem B3298171 : Blo 1953435 3298171 := bstep (se 1 (by rfl) ⟨2473628, by rfl⟩ : syracuseStep 3298171 = 4947257) B4947257
theorem B4397561 : Blo 1953435 4397561 := bstep (se 2 (by rfl) ⟨1649085, by rfl⟩ : syracuseStep 4397561 = 3298171) B3298171
theorem B2931707 : Blo 1953435 2931707 := bstep (se 1 (by rfl) ⟨2198780, by rfl⟩ : syracuseStep 2931707 = 4397561) B4397561
theorem B1954471 : Blo 1953435 1954471 := bstep (se 1 (by rfl) ⟨1465853, by rfl⟩ : syracuseStep 1954471 = 2931707) B2931707
theorem B2198785 : Blo 1953435 2198785 := bbase (se 2 (by rfl) ⟨824544, by rfl⟩ : syracuseStep 2198785 = 1649089) (by norm_num)
theorem B2931713 : Blo 1953435 2931713 := bstep (se 2 (by rfl) ⟨1099392, by rfl⟩ : syracuseStep 2931713 = 2198785) B2198785
theorem B1954475 : Blo 1953435 1954475 := bstep (se 1 (by rfl) ⟨1465856, by rfl⟩ : syracuseStep 1954475 = 2931713) B2931713
theorem B4947277 : Blo 1953435 4947277 := bbase (se 3 (by rfl) ⟨927614, by rfl⟩ : syracuseStep 4947277 = 1855229) (by norm_num)
theorem B6596369 : Blo 1953435 6596369 := bstep (se 2 (by rfl) ⟨2473638, by rfl⟩ : syracuseStep 6596369 = 4947277) B4947277
theorem B4397579 : Blo 1953435 4397579 := bstep (se 1 (by rfl) ⟨3298184, by rfl⟩ : syracuseStep 4397579 = 6596369) B6596369
theorem B2931719 : Blo 1953435 2931719 := bstep (se 1 (by rfl) ⟨2198789, by rfl⟩ : syracuseStep 2931719 = 4397579) B4397579
theorem B1954479 : Blo 1953435 1954479 := bstep (se 1 (by rfl) ⟨1465859, by rfl⟩ : syracuseStep 1954479 = 2931719) B2931719
theorem B2931725 : Blo 1953435 2931725 := bbase (se 3 (by rfl) ⟨549698, by rfl⟩ : syracuseStep 2931725 = 1099397) (by norm_num)
theorem B1954483 : Blo 1953435 1954483 := bstep (se 1 (by rfl) ⟨1465862, by rfl⟩ : syracuseStep 1954483 = 2931725) B2931725
theorem B4397597 : Blo 1953435 4397597 := bbase (se 3 (by rfl) ⟨824549, by rfl⟩ : syracuseStep 4397597 = 1649099) (by norm_num)
theorem B2931731 : Blo 1953435 2931731 := bstep (se 1 (by rfl) ⟨2198798, by rfl⟩ : syracuseStep 2931731 = 4397597) B4397597
theorem B1954487 : Blo 1953435 1954487 := bstep (se 1 (by rfl) ⟨1465865, by rfl⟩ : syracuseStep 1954487 = 2931731) B2931731
theorem B3298205 : Blo 1953435 3298205 := bbase (se 3 (by rfl) ⟨618413, by rfl⟩ : syracuseStep 3298205 = 1236827) (by norm_num)
theorem B2198803 : Blo 1953435 2198803 := bstep (se 1 (by rfl) ⟨1649102, by rfl⟩ : syracuseStep 2198803 = 3298205) B3298205
theorem B2931737 : Blo 1953435 2931737 := bstep (se 2 (by rfl) ⟨1099401, by rfl⟩ : syracuseStep 2931737 = 2198803) B2198803
theorem B1954491 : Blo 1953435 1954491 := bstep (se 1 (by rfl) ⟨1465868, by rfl⟩ : syracuseStep 1954491 = 2931737) B2931737
theorem B10566197 : Blo 1953435 10566197 := bbase (se 5 (by rfl) ⟨495290, by rfl⟩ : syracuseStep 10566197 = 990581) (by norm_num)
theorem B7044131 : Blo 1953435 7044131 := bstep (se 1 (by rfl) ⟨5283098, by rfl⟩ : syracuseStep 7044131 = 10566197) B10566197
theorem B18784349 : Blo 1953435 18784349 := bstep (se 3 (by rfl) ⟨3522065, by rfl⟩ : syracuseStep 18784349 = 7044131) B7044131
theorem B12522899 : Blo 1953435 12522899 := bstep (se 1 (by rfl) ⟨9392174, by rfl⟩ : syracuseStep 12522899 = 18784349) B18784349
theorem B8348599 : Blo 1953435 8348599 := bstep (se 1 (by rfl) ⟨6261449, by rfl⟩ : syracuseStep 8348599 = 12522899) B12522899
theorem B11131465 : Blo 1953435 11131465 := bstep (se 2 (by rfl) ⟨4174299, by rfl⟩ : syracuseStep 11131465 = 8348599) B8348599
theorem B14841953 : Blo 1953435 14841953 := bstep (se 2 (by rfl) ⟨5565732, by rfl⟩ : syracuseStep 14841953 = 11131465) B11131465
theorem B9894635 : Blo 1953435 9894635 := bstep (se 1 (by rfl) ⟨7420976, by rfl⟩ : syracuseStep 9894635 = 14841953) B14841953
theorem B6596423 : Blo 1953435 6596423 := bstep (se 1 (by rfl) ⟨4947317, by rfl⟩ : syracuseStep 6596423 = 9894635) B9894635
theorem B4397615 : Blo 1953435 4397615 := bstep (se 1 (by rfl) ⟨3298211, by rfl⟩ : syracuseStep 4397615 = 6596423) B6596423
theorem B2931743 : Blo 1953435 2931743 := bstep (se 1 (by rfl) ⟨2198807, by rfl⟩ : syracuseStep 2931743 = 4397615) B4397615
theorem B1954495 : Blo 1953435 1954495 := bstep (se 1 (by rfl) ⟨1465871, by rfl⟩ : syracuseStep 1954495 = 2931743) B2931743
theorem B2931749 : Blo 1953435 2931749 := bbase (se 4 (by rfl) ⟨274851, by rfl⟩ : syracuseStep 2931749 = 549703) (by norm_num)
theorem B1954499 : Blo 1953435 1954499 := bstep (se 1 (by rfl) ⟨1465874, by rfl⟩ : syracuseStep 1954499 = 2931749) B2931749
theorem B2473669 : Blo 1953435 2473669 := bbase (se 4 (by rfl) ⟨231906, by rfl⟩ : syracuseStep 2473669 = 463813) (by norm_num)
theorem B3298225 : Blo 1953435 3298225 := bstep (se 2 (by rfl) ⟨1236834, by rfl⟩ : syracuseStep 3298225 = 2473669) B2473669
theorem B4397633 : Blo 1953435 4397633 := bstep (se 2 (by rfl) ⟨1649112, by rfl⟩ : syracuseStep 4397633 = 3298225) B3298225
theorem B2931755 : Blo 1953435 2931755 := bstep (se 1 (by rfl) ⟨2198816, by rfl⟩ : syracuseStep 2931755 = 4397633) B4397633
theorem B1954503 : Blo 1953435 1954503 := bstep (se 1 (by rfl) ⟨1465877, by rfl⟩ : syracuseStep 1954503 = 2931755) B2931755
theorem B2198821 : Blo 1953435 2198821 := bbase (se 4 (by rfl) ⟨206139, by rfl⟩ : syracuseStep 2198821 = 412279) (by norm_num)
theorem B2931761 : Blo 1953435 2931761 := bstep (se 2 (by rfl) ⟨1099410, by rfl⟩ : syracuseStep 2931761 = 2198821) B2198821
theorem B1954507 : Blo 1953435 1954507 := bstep (se 1 (by rfl) ⟨1465880, by rfl⟩ : syracuseStep 1954507 = 2931761) B2931761
theorem B22566869 : Blo 1953435 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B15044579 : Blo 1953435 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B10029719 : Blo 1953435 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B6686479 : Blo 1953435 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B35661221 : Blo 1953435 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B23774147 : Blo 1953435 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B15849431 : Blo 1953435 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B10566287 : Blo 1953435 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B7044191 : Blo 1953435 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B4696127 : Blo 1953435 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B3130751 : Blo 1953435 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B8348669 : Blo 1953435 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B5565779 : Blo 1953435 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B3710519 : Blo 1953435 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B2473679 : Blo 1953435 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B6596477 : Blo 1953435 6596477 := bstep (se 3 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 6596477 = 2473679) B2473679
theorem B4397651 : Blo 1953435 4397651 := bstep (se 1 (by rfl) ⟨3298238, by rfl⟩ : syracuseStep 4397651 = 6596477) B6596477
theorem B2931767 : Blo 1953435 2931767 := bstep (se 1 (by rfl) ⟨2198825, by rfl⟩ : syracuseStep 2931767 = 4397651) B4397651
theorem B1954511 : Blo 1953435 1954511 := bstep (se 1 (by rfl) ⟨1465883, by rfl⟩ : syracuseStep 1954511 = 2931767) B2931767
theorem B2931773 : Blo 1953435 2931773 := bbase (se 3 (by rfl) ⟨549707, by rfl⟩ : syracuseStep 2931773 = 1099415) (by norm_num)
theorem B1954515 : Blo 1953435 1954515 := bstep (se 1 (by rfl) ⟨1465886, by rfl⟩ : syracuseStep 1954515 = 2931773) B2931773
theorem B4397669 : Blo 1953435 4397669 := bbase (se 4 (by rfl) ⟨412281, by rfl⟩ : syracuseStep 4397669 = 824563) (by norm_num)
theorem B2931779 : Blo 1953435 2931779 := bstep (se 1 (by rfl) ⟨2198834, by rfl⟩ : syracuseStep 2931779 = 4397669) B4397669
theorem B1954519 : Blo 1953435 1954519 := bstep (se 1 (by rfl) ⟨1465889, by rfl⟩ : syracuseStep 1954519 = 2931779) B2931779
theorem B4947389 : Blo 1953435 4947389 := bbase (se 3 (by rfl) ⟨927635, by rfl⟩ : syracuseStep 4947389 = 1855271) (by norm_num)
theorem B3298259 : Blo 1953435 3298259 := bstep (se 1 (by rfl) ⟨2473694, by rfl⟩ : syracuseStep 3298259 = 4947389) B4947389
theorem B2198839 : Blo 1953435 2198839 := bstep (se 1 (by rfl) ⟨1649129, by rfl⟩ : syracuseStep 2198839 = 3298259) B3298259
theorem B2931785 : Blo 1953435 2931785 := bstep (se 2 (by rfl) ⟨1099419, by rfl⟩ : syracuseStep 2931785 = 2198839) B2198839
theorem B1954523 : Blo 1953435 1954523 := bstep (se 1 (by rfl) ⟨1465892, by rfl⟩ : syracuseStep 1954523 = 2931785) B2931785
theorem B3710549 : Blo 1953435 3710549 := bbase (se 8 (by rfl) ⟨21741, by rfl⟩ : syracuseStep 3710549 = 43483) (by norm_num)
theorem B9894797 : Blo 1953435 9894797 := bstep (se 3 (by rfl) ⟨1855274, by rfl⟩ : syracuseStep 9894797 = 3710549) B3710549
theorem B6596531 : Blo 1953435 6596531 := bstep (se 1 (by rfl) ⟨4947398, by rfl⟩ : syracuseStep 6596531 = 9894797) B9894797
theorem B4397687 : Blo 1953435 4397687 := bstep (se 1 (by rfl) ⟨3298265, by rfl⟩ : syracuseStep 4397687 = 6596531) B6596531
theorem B2931791 : Blo 1953435 2931791 := bstep (se 1 (by rfl) ⟨2198843, by rfl⟩ : syracuseStep 2931791 = 4397687) B4397687
theorem B1954527 : Blo 1953435 1954527 := bstep (se 1 (by rfl) ⟨1465895, by rfl⟩ : syracuseStep 1954527 = 2931791) B2931791
theorem B2931797 : Blo 1953435 2931797 := bbase (se 8 (by rfl) ⟨17178, by rfl⟩ : syracuseStep 2931797 = 34357) (by norm_num)
theorem B1954531 : Blo 1953435 1954531 := bstep (se 1 (by rfl) ⟨1465898, by rfl⟩ : syracuseStep 1954531 = 2931797) B2931797
theorem B12523157 : Blo 1953435 12523157 := bbase (se 6 (by rfl) ⟨293511, by rfl⟩ : syracuseStep 12523157 = 587023) (by norm_num)
theorem B8348771 : Blo 1953435 8348771 := bstep (se 1 (by rfl) ⟨6261578, by rfl⟩ : syracuseStep 8348771 = 12523157) B12523157
theorem B5565847 : Blo 1953435 5565847 := bstep (se 1 (by rfl) ⟨4174385, by rfl⟩ : syracuseStep 5565847 = 8348771) B8348771
theorem B7421129 : Blo 1953435 7421129 := bstep (se 2 (by rfl) ⟨2782923, by rfl⟩ : syracuseStep 7421129 = 5565847) B5565847
theorem B4947419 : Blo 1953435 4947419 := bstep (se 1 (by rfl) ⟨3710564, by rfl⟩ : syracuseStep 4947419 = 7421129) B7421129
theorem B3298279 : Blo 1953435 3298279 := bstep (se 1 (by rfl) ⟨2473709, by rfl⟩ : syracuseStep 3298279 = 4947419) B4947419
theorem B4397705 : Blo 1953435 4397705 := bstep (se 2 (by rfl) ⟨1649139, by rfl⟩ : syracuseStep 4397705 = 3298279) B3298279
theorem B2931803 : Blo 1953435 2931803 := bstep (se 1 (by rfl) ⟨2198852, by rfl⟩ : syracuseStep 2931803 = 4397705) B4397705
theorem B1954535 : Blo 1953435 1954535 := bstep (se 1 (by rfl) ⟨1465901, by rfl⟩ : syracuseStep 1954535 = 2931803) B2931803
theorem B2198857 : Blo 1953435 2198857 := bbase (se 2 (by rfl) ⟨824571, by rfl⟩ : syracuseStep 2198857 = 1649143) (by norm_num)
theorem B2931809 : Blo 1953435 2931809 := bstep (se 2 (by rfl) ⟨1099428, by rfl⟩ : syracuseStep 2931809 = 2198857) B2198857
theorem B1954539 : Blo 1953435 1954539 := bstep (se 1 (by rfl) ⟨1465904, by rfl⟩ : syracuseStep 1954539 = 2931809) B2931809
theorem B15849685 : Blo 1953435 15849685 := bbase (se 7 (by rfl) ⟨185738, by rfl⟩ : syracuseStep 15849685 = 371477) (by norm_num)
theorem B21132913 : Blo 1953435 21132913 := bstep (se 2 (by rfl) ⟨7924842, by rfl⟩ : syracuseStep 21132913 = 15849685) B15849685
theorem B28177217 : Blo 1953435 28177217 := bstep (se 2 (by rfl) ⟨10566456, by rfl⟩ : syracuseStep 28177217 = 21132913) B21132913
theorem B18784811 : Blo 1953435 18784811 := bstep (se 1 (by rfl) ⟨14088608, by rfl⟩ : syracuseStep 18784811 = 28177217) B28177217
theorem B12523207 : Blo 1953435 12523207 := bstep (se 1 (by rfl) ⟨9392405, by rfl⟩ : syracuseStep 12523207 = 18784811) B18784811
theorem B16697609 : Blo 1953435 16697609 := bstep (se 2 (by rfl) ⟨6261603, by rfl⟩ : syracuseStep 16697609 = 12523207) B12523207
theorem B11131739 : Blo 1953435 11131739 := bstep (se 1 (by rfl) ⟨8348804, by rfl⟩ : syracuseStep 11131739 = 16697609) B16697609
theorem B7421159 : Blo 1953435 7421159 := bstep (se 1 (by rfl) ⟨5565869, by rfl⟩ : syracuseStep 7421159 = 11131739) B11131739
theorem B4947439 : Blo 1953435 4947439 := bstep (se 1 (by rfl) ⟨3710579, by rfl⟩ : syracuseStep 4947439 = 7421159) B7421159
theorem B6596585 : Blo 1953435 6596585 := bstep (se 2 (by rfl) ⟨2473719, by rfl⟩ : syracuseStep 6596585 = 4947439) B4947439
theorem B4397723 : Blo 1953435 4397723 := bstep (se 1 (by rfl) ⟨3298292, by rfl⟩ : syracuseStep 4397723 = 6596585) B6596585
theorem B2931815 : Blo 1953435 2931815 := bstep (se 1 (by rfl) ⟨2198861, by rfl⟩ : syracuseStep 2931815 = 4397723) B4397723
theorem B1954543 : Blo 1953435 1954543 := bstep (se 1 (by rfl) ⟨1465907, by rfl⟩ : syracuseStep 1954543 = 2931815) B2931815
theorem B2931821 : Blo 1953435 2931821 := bbase (se 3 (by rfl) ⟨549716, by rfl⟩ : syracuseStep 2931821 = 1099433) (by norm_num)
theorem B1954547 : Blo 1953435 1954547 := bstep (se 1 (by rfl) ⟨1465910, by rfl⟩ : syracuseStep 1954547 = 2931821) B2931821
theorem B4397741 : Blo 1953435 4397741 := bbase (se 3 (by rfl) ⟨824576, by rfl⟩ : syracuseStep 4397741 = 1649153) (by norm_num)
theorem B2931827 : Blo 1953435 2931827 := bstep (se 1 (by rfl) ⟨2198870, by rfl⟩ : syracuseStep 2931827 = 4397741) B4397741
theorem B1954551 : Blo 1953435 1954551 := bstep (se 1 (by rfl) ⟨1465913, by rfl⟩ : syracuseStep 1954551 = 2931827) B2931827
theorem B4174429 : Blo 1953435 4174429 := bbase (se 3 (by rfl) ⟨782705, by rfl⟩ : syracuseStep 4174429 = 1565411) (by norm_num)
theorem B5565905 : Blo 1953435 5565905 := bstep (se 2 (by rfl) ⟨2087214, by rfl⟩ : syracuseStep 5565905 = 4174429) B4174429
theorem B3710603 : Blo 1953435 3710603 := bstep (se 1 (by rfl) ⟨2782952, by rfl⟩ : syracuseStep 3710603 = 5565905) B5565905
theorem B2473735 : Blo 1953435 2473735 := bstep (se 1 (by rfl) ⟨1855301, by rfl⟩ : syracuseStep 2473735 = 3710603) B3710603
theorem B3298313 : Blo 1953435 3298313 := bstep (se 2 (by rfl) ⟨1236867, by rfl⟩ : syracuseStep 3298313 = 2473735) B2473735
theorem B2198875 : Blo 1953435 2198875 := bstep (se 1 (by rfl) ⟨1649156, by rfl⟩ : syracuseStep 2198875 = 3298313) B3298313
theorem B2931833 : Blo 1953435 2931833 := bstep (se 2 (by rfl) ⟨1099437, by rfl⟩ : syracuseStep 2931833 = 2198875) B2198875
theorem B1954555 : Blo 1953435 1954555 := bstep (se 1 (by rfl) ⟨1465916, by rfl⟩ : syracuseStep 1954555 = 2931833) B2931833
theorem B5014981 : Blo 1953435 5014981 := bbase (se 4 (by rfl) ⟨470154, by rfl⟩ : syracuseStep 5014981 = 940309) (by norm_num)
theorem B6686641 : Blo 1953435 6686641 := bstep (se 2 (by rfl) ⟨2507490, by rfl⟩ : syracuseStep 6686641 = 5014981) B5014981
theorem B8915521 : Blo 1953435 8915521 := bstep (se 2 (by rfl) ⟨3343320, by rfl⟩ : syracuseStep 8915521 = 6686641) B6686641
theorem B11887361 : Blo 1953435 11887361 := bstep (se 2 (by rfl) ⟨4457760, by rfl⟩ : syracuseStep 11887361 = 8915521) B8915521
theorem B7924907 : Blo 1953435 7924907 := bstep (se 1 (by rfl) ⟨5943680, by rfl⟩ : syracuseStep 7924907 = 11887361) B11887361
theorem B5283271 : Blo 1953435 5283271 := bstep (se 1 (by rfl) ⟨3962453, by rfl⟩ : syracuseStep 5283271 = 7924907) B7924907
theorem B28177445 : Blo 1953435 28177445 := bstep (se 4 (by rfl) ⟨2641635, by rfl⟩ : syracuseStep 28177445 = 5283271) B5283271
theorem B18784963 : Blo 1953435 18784963 := bstep (se 1 (by rfl) ⟨14088722, by rfl⟩ : syracuseStep 18784963 = 28177445) B28177445
theorem B25046617 : Blo 1953435 25046617 := bstep (se 2 (by rfl) ⟨9392481, by rfl⟩ : syracuseStep 25046617 = 18784963) B18784963
theorem B33395489 : Blo 1953435 33395489 := bstep (se 2 (by rfl) ⟨12523308, by rfl⟩ : syracuseStep 33395489 = 25046617) B25046617
theorem B22263659 : Blo 1953435 22263659 := bstep (se 1 (by rfl) ⟨16697744, by rfl⟩ : syracuseStep 22263659 = 33395489) B33395489
theorem B14842439 : Blo 1953435 14842439 := bstep (se 1 (by rfl) ⟨11131829, by rfl⟩ : syracuseStep 14842439 = 22263659) B22263659
theorem B9894959 : Blo 1953435 9894959 := bstep (se 1 (by rfl) ⟨7421219, by rfl⟩ : syracuseStep 9894959 = 14842439) B14842439
theorem B6596639 : Blo 1953435 6596639 := bstep (se 1 (by rfl) ⟨4947479, by rfl⟩ : syracuseStep 6596639 = 9894959) B9894959
theorem B4397759 : Blo 1953435 4397759 := bstep (se 1 (by rfl) ⟨3298319, by rfl⟩ : syracuseStep 4397759 = 6596639) B6596639
theorem B2931839 : Blo 1953435 2931839 := bstep (se 1 (by rfl) ⟨2198879, by rfl⟩ : syracuseStep 2931839 = 4397759) B4397759
theorem B1954559 : Blo 1953435 1954559 := bstep (se 1 (by rfl) ⟨1465919, by rfl⟩ : syracuseStep 1954559 = 2931839) B2931839
theorem B2931845 : Blo 1953435 2931845 := bbase (se 4 (by rfl) ⟨274860, by rfl⟩ : syracuseStep 2931845 = 549721) (by norm_num)
theorem B1954563 : Blo 1953435 1954563 := bstep (se 1 (by rfl) ⟨1465922, by rfl⟩ : syracuseStep 1954563 = 2931845) B2931845
theorem B3298333 : Blo 1953435 3298333 := bbase (se 3 (by rfl) ⟨618437, by rfl⟩ : syracuseStep 3298333 = 1236875) (by norm_num)
theorem B4397777 : Blo 1953435 4397777 := bstep (se 2 (by rfl) ⟨1649166, by rfl⟩ : syracuseStep 4397777 = 3298333) B3298333
theorem B2931851 : Blo 1953435 2931851 := bstep (se 1 (by rfl) ⟨2198888, by rfl⟩ : syracuseStep 2931851 = 4397777) B4397777
theorem B1954567 : Blo 1953435 1954567 := bstep (se 1 (by rfl) ⟨1465925, by rfl⟩ : syracuseStep 1954567 = 2931851) B2931851
theorem B2198893 : Blo 1953435 2198893 := bbase (se 3 (by rfl) ⟨412292, by rfl⟩ : syracuseStep 2198893 = 824585) (by norm_num)
theorem B2931857 : Blo 1953435 2931857 := bstep (se 2 (by rfl) ⟨1099446, by rfl⟩ : syracuseStep 2931857 = 2198893) B2198893
theorem B1954571 : Blo 1953435 1954571 := bstep (se 1 (by rfl) ⟨1465928, by rfl⟩ : syracuseStep 1954571 = 2931857) B2931857
theorem B6596693 : Blo 1953435 6596693 := bbase (se 8 (by rfl) ⟨38652, by rfl⟩ : syracuseStep 6596693 = 77305) (by norm_num)
theorem B4397795 : Blo 1953435 4397795 := bstep (se 1 (by rfl) ⟨3298346, by rfl⟩ : syracuseStep 4397795 = 6596693) B6596693
theorem B2931863 : Blo 1953435 2931863 := bstep (se 1 (by rfl) ⟨2198897, by rfl⟩ : syracuseStep 2931863 = 4397795) B4397795
theorem B1954575 : Blo 1953435 1954575 := bstep (se 1 (by rfl) ⟨1465931, by rfl⟩ : syracuseStep 1954575 = 2931863) B2931863
theorem B2931869 : Blo 1953435 2931869 := bbase (se 3 (by rfl) ⟨549725, by rfl⟩ : syracuseStep 2931869 = 1099451) (by norm_num)
theorem B1954579 : Blo 1953435 1954579 := bstep (se 1 (by rfl) ⟨1465934, by rfl⟩ : syracuseStep 1954579 = 2931869) B2931869
theorem B4397813 : Blo 1953435 4397813 := bbase (se 5 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 4397813 = 412295) (by norm_num)
theorem B2931875 : Blo 1953435 2931875 := bstep (se 1 (by rfl) ⟨2198906, by rfl⟩ : syracuseStep 2931875 = 4397813) B4397813
theorem B1954583 : Blo 1953435 1954583 := bstep (se 1 (by rfl) ⟨1465937, by rfl⟩ : syracuseStep 1954583 = 2931875) B2931875
theorem B4696309 : Blo 1953435 4696309 := bbase (se 5 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 4696309 = 440279) (by norm_num)
theorem B25046981 : Blo 1953435 25046981 := bstep (se 4 (by rfl) ⟨2348154, by rfl⟩ : syracuseStep 25046981 = 4696309) B4696309
theorem B16697987 : Blo 1953435 16697987 := bstep (se 1 (by rfl) ⟨12523490, by rfl⟩ : syracuseStep 16697987 = 25046981) B25046981
theorem B11131991 : Blo 1953435 11131991 := bstep (se 1 (by rfl) ⟨8348993, by rfl⟩ : syracuseStep 11131991 = 16697987) B16697987
theorem B7421327 : Blo 1953435 7421327 := bstep (se 1 (by rfl) ⟨5565995, by rfl⟩ : syracuseStep 7421327 = 11131991) B11131991
theorem B4947551 : Blo 1953435 4947551 := bstep (se 1 (by rfl) ⟨3710663, by rfl⟩ : syracuseStep 4947551 = 7421327) B7421327
theorem B3298367 : Blo 1953435 3298367 := bstep (se 1 (by rfl) ⟨2473775, by rfl⟩ : syracuseStep 3298367 = 4947551) B4947551
theorem B2198911 : Blo 1953435 2198911 := bstep (se 1 (by rfl) ⟨1649183, by rfl⟩ : syracuseStep 2198911 = 3298367) B3298367
theorem B2931881 : Blo 1953435 2931881 := bstep (se 2 (by rfl) ⟨1099455, by rfl⟩ : syracuseStep 2931881 = 2198911) B2198911
theorem B1954587 : Blo 1953435 1954587 := bstep (se 1 (by rfl) ⟨1465940, by rfl⟩ : syracuseStep 1954587 = 2931881) B2931881
theorem B3012437 : Blo 1953435 3012437 := bbase (se 9 (by rfl) ⟨8825, by rfl⟩ : syracuseStep 3012437 = 17651) (by norm_num)
theorem B8033165 : Blo 1953435 8033165 := bstep (se 3 (by rfl) ⟨1506218, by rfl⟩ : syracuseStep 8033165 = 3012437) B3012437
theorem B5355443 : Blo 1953435 5355443 := bstep (se 1 (by rfl) ⟨4016582, by rfl⟩ : syracuseStep 5355443 = 8033165) B8033165
theorem B14281181 : Blo 1953435 14281181 := bstep (se 3 (by rfl) ⟨2677721, by rfl⟩ : syracuseStep 14281181 = 5355443) B5355443
theorem B9520787 : Blo 1953435 9520787 := bstep (se 1 (by rfl) ⟨7140590, by rfl⟩ : syracuseStep 9520787 = 14281181) B14281181
theorem B25388765 : Blo 1953435 25388765 := bstep (se 3 (by rfl) ⟨4760393, by rfl⟩ : syracuseStep 25388765 = 9520787) B9520787
theorem B16925843 : Blo 1953435 16925843 := bstep (se 1 (by rfl) ⟨12694382, by rfl⟩ : syracuseStep 16925843 = 25388765) B25388765
theorem B11283895 : Blo 1953435 11283895 := bstep (se 1 (by rfl) ⟨8462921, by rfl⟩ : syracuseStep 11283895 = 16925843) B16925843
theorem B15045193 : Blo 1953435 15045193 := bstep (se 2 (by rfl) ⟨5641947, by rfl⟩ : syracuseStep 15045193 = 11283895) B11283895
theorem B80241029 : Blo 1953435 80241029 := bstep (se 4 (by rfl) ⟨7522596, by rfl⟩ : syracuseStep 80241029 = 15045193) B15045193
theorem B53494019 : Blo 1953435 53494019 := bstep (se 1 (by rfl) ⟨40120514, by rfl⟩ : syracuseStep 53494019 = 80241029) B80241029
theorem B35662679 : Blo 1953435 35662679 := bstep (se 1 (by rfl) ⟨26747009, by rfl⟩ : syracuseStep 35662679 = 53494019) B53494019
theorem B23775119 : Blo 1953435 23775119 := bstep (se 1 (by rfl) ⟨17831339, by rfl⟩ : syracuseStep 23775119 = 35662679) B35662679
theorem B15850079 : Blo 1953435 15850079 := bstep (se 1 (by rfl) ⟨11887559, by rfl⟩ : syracuseStep 15850079 = 23775119) B23775119
theorem B10566719 : Blo 1953435 10566719 := bstep (se 1 (by rfl) ⟨7925039, by rfl⟩ : syracuseStep 10566719 = 15850079) B15850079
theorem B7044479 : Blo 1953435 7044479 := bstep (se 1 (by rfl) ⟨5283359, by rfl⟩ : syracuseStep 7044479 = 10566719) B10566719
theorem B4696319 : Blo 1953435 4696319 := bstep (se 1 (by rfl) ⟨3522239, by rfl⟩ : syracuseStep 4696319 = 7044479) B7044479
theorem B3130879 : Blo 1953435 3130879 := bstep (se 1 (by rfl) ⟨2348159, by rfl⟩ : syracuseStep 3130879 = 4696319) B4696319
theorem B4174505 : Blo 1953435 4174505 := bstep (se 2 (by rfl) ⟨1565439, by rfl⟩ : syracuseStep 4174505 = 3130879) B3130879
theorem B2783003 : Blo 1953435 2783003 := bstep (se 1 (by rfl) ⟨2087252, by rfl⟩ : syracuseStep 2783003 = 4174505) B4174505
theorem B7421341 : Blo 1953435 7421341 := bstep (se 3 (by rfl) ⟨1391501, by rfl⟩ : syracuseStep 7421341 = 2783003) B2783003
theorem B9895121 : Blo 1953435 9895121 := bstep (se 2 (by rfl) ⟨3710670, by rfl⟩ : syracuseStep 9895121 = 7421341) B7421341
theorem B6596747 : Blo 1953435 6596747 := bstep (se 1 (by rfl) ⟨4947560, by rfl⟩ : syracuseStep 6596747 = 9895121) B9895121
theorem B4397831 : Blo 1953435 4397831 := bstep (se 1 (by rfl) ⟨3298373, by rfl⟩ : syracuseStep 4397831 = 6596747) B6596747
theorem B2931887 : Blo 1953435 2931887 := bstep (se 1 (by rfl) ⟨2198915, by rfl⟩ : syracuseStep 2931887 = 4397831) B4397831
theorem B1954591 : Blo 1953435 1954591 := bstep (se 1 (by rfl) ⟨1465943, by rfl⟩ : syracuseStep 1954591 = 2931887) B2931887
theorem B2931893 : Blo 1953435 2931893 := bbase (se 5 (by rfl) ⟨137432, by rfl⟩ : syracuseStep 2931893 = 274865) (by norm_num)
theorem B1954595 : Blo 1953435 1954595 := bstep (se 1 (by rfl) ⟨1465946, by rfl⟩ : syracuseStep 1954595 = 2931893) B2931893
theorem B4947581 : Blo 1953435 4947581 := bbase (se 3 (by rfl) ⟨927671, by rfl⟩ : syracuseStep 4947581 = 1855343) (by norm_num)
theorem B3298387 : Blo 1953435 3298387 := bstep (se 1 (by rfl) ⟨2473790, by rfl⟩ : syracuseStep 3298387 = 4947581) B4947581
theorem B4397849 : Blo 1953435 4397849 := bstep (se 2 (by rfl) ⟨1649193, by rfl⟩ : syracuseStep 4397849 = 3298387) B3298387
theorem B2931899 : Blo 1953435 2931899 := bstep (se 1 (by rfl) ⟨2198924, by rfl⟩ : syracuseStep 2931899 = 4397849) B4397849
theorem B1954599 : Blo 1953435 1954599 := bstep (se 1 (by rfl) ⟨1465949, by rfl⟩ : syracuseStep 1954599 = 2931899) B2931899
theorem B2198929 : Blo 1953435 2198929 := bbase (se 2 (by rfl) ⟨824598, by rfl⟩ : syracuseStep 2198929 = 1649197) (by norm_num)
theorem B2931905 : Blo 1953435 2931905 := bstep (se 2 (by rfl) ⟨1099464, by rfl⟩ : syracuseStep 2931905 = 2198929) B2198929
theorem B1954603 : Blo 1953435 1954603 := bstep (se 1 (by rfl) ⟨1465952, by rfl⟩ : syracuseStep 1954603 = 2931905) B2931905
theorem B3710701 : Blo 1953435 3710701 := bbase (se 3 (by rfl) ⟨695756, by rfl⟩ : syracuseStep 3710701 = 1391513) (by norm_num)
theorem B4947601 : Blo 1953435 4947601 := bstep (se 2 (by rfl) ⟨1855350, by rfl⟩ : syracuseStep 4947601 = 3710701) B3710701
theorem B6596801 : Blo 1953435 6596801 := bstep (se 2 (by rfl) ⟨2473800, by rfl⟩ : syracuseStep 6596801 = 4947601) B4947601
theorem B4397867 : Blo 1953435 4397867 := bstep (se 1 (by rfl) ⟨3298400, by rfl⟩ : syracuseStep 4397867 = 6596801) B6596801
theorem B2931911 : Blo 1953435 2931911 := bstep (se 1 (by rfl) ⟨2198933, by rfl⟩ : syracuseStep 2931911 = 4397867) B4397867
theorem B1954607 : Blo 1953435 1954607 := bstep (se 1 (by rfl) ⟨1465955, by rfl⟩ : syracuseStep 1954607 = 2931911) B2931911
theorem B2931917 : Blo 1953435 2931917 := bbase (se 3 (by rfl) ⟨549734, by rfl⟩ : syracuseStep 2931917 = 1099469) (by norm_num)
theorem B1954611 : Blo 1953435 1954611 := bstep (se 1 (by rfl) ⟨1465958, by rfl⟩ : syracuseStep 1954611 = 2931917) B2931917
theorem B4397885 : Blo 1953435 4397885 := bbase (se 3 (by rfl) ⟨824603, by rfl⟩ : syracuseStep 4397885 = 1649207) (by norm_num)
theorem B2931923 : Blo 1953435 2931923 := bstep (se 1 (by rfl) ⟨2198942, by rfl⟩ : syracuseStep 2931923 = 4397885) B4397885
theorem B1954615 : Blo 1953435 1954615 := bstep (se 1 (by rfl) ⟨1465961, by rfl⟩ : syracuseStep 1954615 = 2931923) B2931923
theorem B3298421 : Blo 1953435 3298421 := bbase (se 5 (by rfl) ⟨154613, by rfl⟩ : syracuseStep 3298421 = 309227) (by norm_num)
theorem B2198947 : Blo 1953435 2198947 := bstep (se 1 (by rfl) ⟨1649210, by rfl⟩ : syracuseStep 2198947 = 3298421) B3298421
theorem B2931929 : Blo 1953435 2931929 := bstep (se 2 (by rfl) ⟨1099473, by rfl⟩ : syracuseStep 2931929 = 2198947) B2198947
theorem B1954619 : Blo 1953435 1954619 := bstep (se 1 (by rfl) ⟨1465964, by rfl⟩ : syracuseStep 1954619 = 2931929) B2931929
theorem B4174573 : Blo 1953435 4174573 := bbase (se 3 (by rfl) ⟨782732, by rfl⟩ : syracuseStep 4174573 = 1565465) (by norm_num)
theorem B5566097 : Blo 1953435 5566097 := bstep (se 2 (by rfl) ⟨2087286, by rfl⟩ : syracuseStep 5566097 = 4174573) B4174573
theorem B14842925 : Blo 1953435 14842925 := bstep (se 3 (by rfl) ⟨2783048, by rfl⟩ : syracuseStep 14842925 = 5566097) B5566097
theorem B9895283 : Blo 1953435 9895283 := bstep (se 1 (by rfl) ⟨7421462, by rfl⟩ : syracuseStep 9895283 = 14842925) B14842925
theorem B6596855 : Blo 1953435 6596855 := bstep (se 1 (by rfl) ⟨4947641, by rfl⟩ : syracuseStep 6596855 = 9895283) B9895283
theorem B4397903 : Blo 1953435 4397903 := bstep (se 1 (by rfl) ⟨3298427, by rfl⟩ : syracuseStep 4397903 = 6596855) B6596855
theorem B2931935 : Blo 1953435 2931935 := bstep (se 1 (by rfl) ⟨2198951, by rfl⟩ : syracuseStep 2931935 = 4397903) B4397903
theorem B1954623 : Blo 1953435 1954623 := bstep (se 1 (by rfl) ⟨1465967, by rfl⟩ : syracuseStep 1954623 = 2931935) B2931935
theorem B2931941 : Blo 1953435 2931941 := bbase (se 4 (by rfl) ⟨274869, by rfl⟩ : syracuseStep 2931941 = 549739) (by norm_num)
theorem B1954627 : Blo 1953435 1954627 := bstep (se 1 (by rfl) ⟨1465970, by rfl⟩ : syracuseStep 1954627 = 2931941) B2931941
theorem B38083925 : Blo 1953435 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B25389283 : Blo 1953435 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B33852377 : Blo 1953435 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B90273005 : Blo 1953435 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B60182003 : Blo 1953435 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B40121335 : Blo 1953435 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B53495113 : Blo 1953435 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B71326817 : Blo 1953435 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B47551211 : Blo 1953435 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B31700807 : Blo 1953435 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B21133871 : Blo 1953435 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B14089247 : Blo 1953435 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B9392831 : Blo 1953435 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B6261887 : Blo 1953435 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B4174591 : Blo 1953435 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B5566121 : Blo 1953435 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B3710747 : Blo 1953435 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B2473831 : Blo 1953435 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B3298441 : Blo 1953435 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B4397921 : Blo 1953435 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B2931947 : Blo 1953435 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B1954631 : Blo 1953435 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B2198965 : Blo 1953435 2198965 := bbase (se 5 (by rfl) ⟨103076, by rfl⟩ : syracuseStep 2198965 = 206153) (by norm_num)
theorem B2931953 : Blo 1953435 2931953 := bstep (se 2 (by rfl) ⟨1099482, by rfl⟩ : syracuseStep 2931953 = 2198965) B2198965
theorem B1954635 : Blo 1953435 1954635 := bstep (se 1 (by rfl) ⟨1465976, by rfl⟩ : syracuseStep 1954635 = 2931953) B2931953
theorem B2473841 : Blo 1953435 2473841 := bbase (se 2 (by rfl) ⟨927690, by rfl⟩ : syracuseStep 2473841 = 1855381) (by norm_num)
theorem B6596909 : Blo 1953435 6596909 := bstep (se 3 (by rfl) ⟨1236920, by rfl⟩ : syracuseStep 6596909 = 2473841) B2473841
theorem B4397939 : Blo 1953435 4397939 := bstep (se 1 (by rfl) ⟨3298454, by rfl⟩ : syracuseStep 4397939 = 6596909) B6596909
theorem B2931959 : Blo 1953435 2931959 := bstep (se 1 (by rfl) ⟨2198969, by rfl⟩ : syracuseStep 2931959 = 4397939) B4397939
theorem B1954639 : Blo 1953435 1954639 := bstep (se 1 (by rfl) ⟨1465979, by rfl⟩ : syracuseStep 1954639 = 2931959) B2931959
theorem B2931965 : Blo 1953435 2931965 := bbase (se 3 (by rfl) ⟨549743, by rfl⟩ : syracuseStep 2931965 = 1099487) (by norm_num)
theorem B1954643 : Blo 1953435 1954643 := bstep (se 1 (by rfl) ⟨1465982, by rfl⟩ : syracuseStep 1954643 = 2931965) B2931965
theorem B4397957 : Blo 1953435 4397957 := bbase (se 4 (by rfl) ⟨412308, by rfl⟩ : syracuseStep 4397957 = 824617) (by norm_num)
theorem B2931971 : Blo 1953435 2931971 := bstep (se 1 (by rfl) ⟨2198978, by rfl⟩ : syracuseStep 2931971 = 4397957) B4397957
theorem B1954647 : Blo 1953435 1954647 := bstep (se 1 (by rfl) ⟨1465985, by rfl⟩ : syracuseStep 1954647 = 2931971) B2931971
theorem B2087317 : Blo 1953435 2087317 := bbase (se 6 (by rfl) ⟨48921, by rfl⟩ : syracuseStep 2087317 = 97843) (by norm_num)
theorem B2783089 : Blo 1953435 2783089 := bstep (se 2 (by rfl) ⟨1043658, by rfl⟩ : syracuseStep 2783089 = 2087317) B2087317
theorem B3710785 : Blo 1953435 3710785 := bstep (se 2 (by rfl) ⟨1391544, by rfl⟩ : syracuseStep 3710785 = 2783089) B2783089
theorem B4947713 : Blo 1953435 4947713 := bstep (se 2 (by rfl) ⟨1855392, by rfl⟩ : syracuseStep 4947713 = 3710785) B3710785
theorem B3298475 : Blo 1953435 3298475 := bstep (se 1 (by rfl) ⟨2473856, by rfl⟩ : syracuseStep 3298475 = 4947713) B4947713
theorem B2198983 : Blo 1953435 2198983 := bstep (se 1 (by rfl) ⟨1649237, by rfl⟩ : syracuseStep 2198983 = 3298475) B3298475
theorem B2931977 : Blo 1953435 2931977 := bstep (se 2 (by rfl) ⟨1099491, by rfl⟩ : syracuseStep 2931977 = 2198983) B2198983
theorem B1954651 : Blo 1953435 1954651 := bstep (se 1 (by rfl) ⟨1465988, by rfl⟩ : syracuseStep 1954651 = 2931977) B2931977
theorem B9895445 : Blo 1953435 9895445 := bbase (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) (by norm_num)
theorem B6596963 : Blo 1953435 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B4397975 : Blo 1953435 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B2931983 : Blo 1953435 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B1954655 : Blo 1953435 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B2931989 : Blo 1953435 2931989 := bbase (se 6 (by rfl) ⟨68718, by rfl⟩ : syracuseStep 2931989 = 137437) (by norm_num)
theorem B1954659 : Blo 1953435 1954659 := bstep (se 1 (by rfl) ⟨1465994, by rfl⟩ : syracuseStep 1954659 = 2931989) B2931989
theorem B15045749 : Blo 1953435 15045749 := bbase (se 5 (by rfl) ⟨705269, by rfl⟩ : syracuseStep 15045749 = 1410539) (by norm_num)
theorem B10030499 : Blo 1953435 10030499 := bstep (se 1 (by rfl) ⟨7522874, by rfl⟩ : syracuseStep 10030499 = 15045749) B15045749
theorem B6686999 : Blo 1953435 6686999 := bstep (se 1 (by rfl) ⟨5015249, by rfl⟩ : syracuseStep 6686999 = 10030499) B10030499
theorem B4457999 : Blo 1953435 4457999 := bstep (se 1 (by rfl) ⟨3343499, by rfl⟩ : syracuseStep 4457999 = 6686999) B6686999
theorem B2971999 : Blo 1953435 2971999 := bstep (se 1 (by rfl) ⟨2228999, by rfl⟩ : syracuseStep 2971999 = 4457999) B4457999
theorem B3962665 : Blo 1953435 3962665 := bstep (se 2 (by rfl) ⟨1485999, by rfl⟩ : syracuseStep 3962665 = 2971999) B2971999
theorem B5283553 : Blo 1953435 5283553 := bstep (se 2 (by rfl) ⟨1981332, by rfl⟩ : syracuseStep 5283553 = 3962665) B3962665
theorem B7044737 : Blo 1953435 7044737 := bstep (se 2 (by rfl) ⟨2641776, by rfl⟩ : syracuseStep 7044737 = 5283553) B5283553
theorem B18785965 : Blo 1953435 18785965 := bstep (se 3 (by rfl) ⟨3522368, by rfl⟩ : syracuseStep 18785965 = 7044737) B7044737
theorem B25047953 : Blo 1953435 25047953 := bstep (se 2 (by rfl) ⟨9392982, by rfl⟩ : syracuseStep 25047953 = 18785965) B18785965
theorem B16698635 : Blo 1953435 16698635 := bstep (se 1 (by rfl) ⟨12523976, by rfl⟩ : syracuseStep 16698635 = 25047953) B25047953
theorem B11132423 : Blo 1953435 11132423 := bstep (se 1 (by rfl) ⟨8349317, by rfl⟩ : syracuseStep 11132423 = 16698635) B16698635
theorem B7421615 : Blo 1953435 7421615 := bstep (se 1 (by rfl) ⟨5566211, by rfl⟩ : syracuseStep 7421615 = 11132423) B11132423
theorem B4947743 : Blo 1953435 4947743 := bstep (se 1 (by rfl) ⟨3710807, by rfl⟩ : syracuseStep 4947743 = 7421615) B7421615
theorem B3298495 : Blo 1953435 3298495 := bstep (se 1 (by rfl) ⟨2473871, by rfl⟩ : syracuseStep 3298495 = 4947743) B4947743
theorem B4397993 : Blo 1953435 4397993 := bstep (se 2 (by rfl) ⟨1649247, by rfl⟩ : syracuseStep 4397993 = 3298495) B3298495
theorem B2931995 : Blo 1953435 2931995 := bstep (se 1 (by rfl) ⟨2198996, by rfl⟩ : syracuseStep 2931995 = 4397993) B4397993
theorem B1954663 : Blo 1953435 1954663 := bstep (se 1 (by rfl) ⟨1465997, by rfl⟩ : syracuseStep 1954663 = 2931995) B2931995
theorem B2199001 : Blo 1953435 2199001 := bbase (se 2 (by rfl) ⟨824625, by rfl⟩ : syracuseStep 2199001 = 1649251) (by norm_num)
theorem B2932001 : Blo 1953435 2932001 := bstep (se 2 (by rfl) ⟨1099500, by rfl⟩ : syracuseStep 2932001 = 2199001) B2199001
theorem B1954667 : Blo 1953435 1954667 := bstep (se 1 (by rfl) ⟨1466000, by rfl⟩ : syracuseStep 1954667 = 2932001) B2932001
theorem B2783117 : Blo 1953435 2783117 := bbase (se 3 (by rfl) ⟨521834, by rfl⟩ : syracuseStep 2783117 = 1043669) (by norm_num)
theorem B7421645 : Blo 1953435 7421645 := bstep (se 3 (by rfl) ⟨1391558, by rfl⟩ : syracuseStep 7421645 = 2783117) B2783117
theorem B4947763 : Blo 1953435 4947763 := bstep (se 1 (by rfl) ⟨3710822, by rfl⟩ : syracuseStep 4947763 = 7421645) B7421645
theorem B6597017 : Blo 1953435 6597017 := bstep (se 2 (by rfl) ⟨2473881, by rfl⟩ : syracuseStep 6597017 = 4947763) B4947763
theorem B4398011 : Blo 1953435 4398011 := bstep (se 1 (by rfl) ⟨3298508, by rfl⟩ : syracuseStep 4398011 = 6597017) B6597017
theorem B2932007 : Blo 1953435 2932007 := bstep (se 1 (by rfl) ⟨2199005, by rfl⟩ : syracuseStep 2932007 = 4398011) B4398011
theorem B1954671 : Blo 1953435 1954671 := bstep (se 1 (by rfl) ⟨1466003, by rfl⟩ : syracuseStep 1954671 = 2932007) B2932007
theorem B2932013 : Blo 1953435 2932013 := bbase (se 3 (by rfl) ⟨549752, by rfl⟩ : syracuseStep 2932013 = 1099505) (by norm_num)
theorem B1954675 : Blo 1953435 1954675 := bstep (se 1 (by rfl) ⟨1466006, by rfl⟩ : syracuseStep 1954675 = 2932013) B2932013
theorem B4398029 : Blo 1953435 4398029 := bbase (se 3 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 4398029 = 1649261) (by norm_num)
theorem B2932019 : Blo 1953435 2932019 := bstep (se 1 (by rfl) ⟨2199014, by rfl⟩ : syracuseStep 2932019 = 4398029) B4398029
theorem B1954679 : Blo 1953435 1954679 := bstep (se 1 (by rfl) ⟨1466009, by rfl⟩ : syracuseStep 1954679 = 2932019) B2932019
theorem B2473897 : Blo 1953435 2473897 := bbase (se 2 (by rfl) ⟨927711, by rfl⟩ : syracuseStep 2473897 = 1855423) (by norm_num)
theorem B3298529 : Blo 1953435 3298529 := bstep (se 2 (by rfl) ⟨1236948, by rfl⟩ : syracuseStep 3298529 = 2473897) B2473897
theorem B2199019 : Blo 1953435 2199019 := bstep (se 1 (by rfl) ⟨1649264, by rfl⟩ : syracuseStep 2199019 = 3298529) B3298529
theorem B2932025 : Blo 1953435 2932025 := bstep (se 2 (by rfl) ⟨1099509, by rfl⟩ : syracuseStep 2932025 = 2199019) B2199019
theorem B1954683 : Blo 1953435 1954683 := bstep (se 1 (by rfl) ⟨1466012, by rfl⟩ : syracuseStep 1954683 = 2932025) B2932025
theorem B4458053 : Blo 1953435 4458053 := bbase (se 4 (by rfl) ⟨417942, by rfl⟩ : syracuseStep 4458053 = 835885) (by norm_num)
theorem B2972035 : Blo 1953435 2972035 := bstep (se 1 (by rfl) ⟨2229026, by rfl⟩ : syracuseStep 2972035 = 4458053) B4458053
theorem B15850853 : Blo 1953435 15850853 := bstep (se 4 (by rfl) ⟨1486017, by rfl⟩ : syracuseStep 15850853 = 2972035) B2972035
theorem B10567235 : Blo 1953435 10567235 := bstep (se 1 (by rfl) ⟨7925426, by rfl⟩ : syracuseStep 10567235 = 15850853) B15850853
theorem B7044823 : Blo 1953435 7044823 := bstep (se 1 (by rfl) ⟨5283617, by rfl⟩ : syracuseStep 7044823 = 10567235) B10567235
theorem B9393097 : Blo 1953435 9393097 := bstep (se 2 (by rfl) ⟨3522411, by rfl⟩ : syracuseStep 9393097 = 7044823) B7044823
theorem B12524129 : Blo 1953435 12524129 := bstep (se 2 (by rfl) ⟨4696548, by rfl⟩ : syracuseStep 12524129 = 9393097) B9393097
theorem B8349419 : Blo 1953435 8349419 := bstep (se 1 (by rfl) ⟨6262064, by rfl⟩ : syracuseStep 8349419 = 12524129) B12524129
theorem B22265117 : Blo 1953435 22265117 := bstep (se 3 (by rfl) ⟨4174709, by rfl⟩ : syracuseStep 22265117 = 8349419) B8349419
theorem B14843411 : Blo 1953435 14843411 := bstep (se 1 (by rfl) ⟨11132558, by rfl⟩ : syracuseStep 14843411 = 22265117) B22265117
theorem B9895607 : Blo 1953435 9895607 := bstep (se 1 (by rfl) ⟨7421705, by rfl⟩ : syracuseStep 9895607 = 14843411) B14843411
theorem B6597071 : Blo 1953435 6597071 := bstep (se 1 (by rfl) ⟨4947803, by rfl⟩ : syracuseStep 6597071 = 9895607) B9895607
theorem B4398047 : Blo 1953435 4398047 := bstep (se 1 (by rfl) ⟨3298535, by rfl⟩ : syracuseStep 4398047 = 6597071) B6597071
theorem B2932031 : Blo 1953435 2932031 := bstep (se 1 (by rfl) ⟨2199023, by rfl⟩ : syracuseStep 2932031 = 4398047) B4398047
theorem B1954687 : Blo 1953435 1954687 := bstep (se 1 (by rfl) ⟨1466015, by rfl⟩ : syracuseStep 1954687 = 2932031) B2932031
theorem B2932037 : Blo 1953435 2932037 := bbase (se 4 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 2932037 = 549757) (by norm_num)
theorem B1954691 : Blo 1953435 1954691 := bstep (se 1 (by rfl) ⟨1466018, by rfl⟩ : syracuseStep 1954691 = 2932037) B2932037
theorem B3298549 : Blo 1953435 3298549 := bbase (se 5 (by rfl) ⟨154619, by rfl⟩ : syracuseStep 3298549 = 309239) (by norm_num)
theorem B4398065 : Blo 1953435 4398065 := bstep (se 2 (by rfl) ⟨1649274, by rfl⟩ : syracuseStep 4398065 = 3298549) B3298549
theorem B2932043 : Blo 1953435 2932043 := bstep (se 1 (by rfl) ⟨2199032, by rfl⟩ : syracuseStep 2932043 = 4398065) B4398065
theorem B1954695 : Blo 1953435 1954695 := bstep (se 1 (by rfl) ⟨1466021, by rfl⟩ : syracuseStep 1954695 = 2932043) B2932043
theorem B2199037 : Blo 1953435 2199037 := bbase (se 3 (by rfl) ⟨412319, by rfl⟩ : syracuseStep 2199037 = 824639) (by norm_num)
theorem B2932049 : Blo 1953435 2932049 := bstep (se 2 (by rfl) ⟨1099518, by rfl⟩ : syracuseStep 2932049 = 2199037) B2199037
theorem B1954699 : Blo 1953435 1954699 := bstep (se 1 (by rfl) ⟨1466024, by rfl⟩ : syracuseStep 1954699 = 2932049) B2932049
theorem B6597125 : Blo 1953435 6597125 := bbase (se 4 (by rfl) ⟨618480, by rfl⟩ : syracuseStep 6597125 = 1236961) (by norm_num)
theorem B4398083 : Blo 1953435 4398083 := bstep (se 1 (by rfl) ⟨3298562, by rfl⟩ : syracuseStep 4398083 = 6597125) B6597125
theorem B2932055 : Blo 1953435 2932055 := bstep (se 1 (by rfl) ⟨2199041, by rfl⟩ : syracuseStep 2932055 = 4398083) B4398083
theorem B1954703 : Blo 1953435 1954703 := bstep (se 1 (by rfl) ⟨1466027, by rfl⟩ : syracuseStep 1954703 = 2932055) B2932055
theorem B2932061 : Blo 1953435 2932061 := bbase (se 3 (by rfl) ⟨549761, by rfl⟩ : syracuseStep 2932061 = 1099523) (by norm_num)
theorem B1954707 : Blo 1953435 1954707 := bstep (se 1 (by rfl) ⟨1466030, by rfl⟩ : syracuseStep 1954707 = 2932061) B2932061
theorem B4398101 : Blo 1953435 4398101 := bbase (se 6 (by rfl) ⟨103080, by rfl⟩ : syracuseStep 4398101 = 206161) (by norm_num)
theorem B2932067 : Blo 1953435 2932067 := bstep (se 1 (by rfl) ⟨2199050, by rfl⟩ : syracuseStep 2932067 = 4398101) B4398101
theorem B1954711 : Blo 1953435 1954711 := bstep (se 1 (by rfl) ⟨1466033, by rfl⟩ : syracuseStep 1954711 = 2932067) B2932067
theorem B7421813 : Blo 1953435 7421813 := bbase (se 5 (by rfl) ⟨347897, by rfl⟩ : syracuseStep 7421813 = 695795) (by norm_num)
theorem B4947875 : Blo 1953435 4947875 := bstep (se 1 (by rfl) ⟨3710906, by rfl⟩ : syracuseStep 4947875 = 7421813) B7421813
theorem B3298583 : Blo 1953435 3298583 := bstep (se 1 (by rfl) ⟨2473937, by rfl⟩ : syracuseStep 3298583 = 4947875) B4947875
theorem B2199055 : Blo 1953435 2199055 := bstep (se 1 (by rfl) ⟨1649291, by rfl⟩ : syracuseStep 2199055 = 3298583) B3298583
theorem B2932073 : Blo 1953435 2932073 := bstep (se 2 (by rfl) ⟨1099527, by rfl⟩ : syracuseStep 2932073 = 2199055) B2199055
theorem B1954715 : Blo 1953435 1954715 := bstep (se 1 (by rfl) ⟨1466036, by rfl⟩ : syracuseStep 1954715 = 2932073) B2932073
theorem B2087389 : Blo 1953435 2087389 := bbase (se 3 (by rfl) ⟨391385, by rfl⟩ : syracuseStep 2087389 = 782771) (by norm_num)
theorem B11132741 : Blo 1953435 11132741 := bstep (se 4 (by rfl) ⟨1043694, by rfl⟩ : syracuseStep 11132741 = 2087389) B2087389
theorem B7421827 : Blo 1953435 7421827 := bstep (se 1 (by rfl) ⟨5566370, by rfl⟩ : syracuseStep 7421827 = 11132741) B11132741
theorem B9895769 : Blo 1953435 9895769 := bstep (se 2 (by rfl) ⟨3710913, by rfl⟩ : syracuseStep 9895769 = 7421827) B7421827
theorem B6597179 : Blo 1953435 6597179 := bstep (se 1 (by rfl) ⟨4947884, by rfl⟩ : syracuseStep 6597179 = 9895769) B9895769
theorem B4398119 : Blo 1953435 4398119 := bstep (se 1 (by rfl) ⟨3298589, by rfl⟩ : syracuseStep 4398119 = 6597179) B6597179
theorem B2932079 : Blo 1953435 2932079 := bstep (se 1 (by rfl) ⟨2199059, by rfl⟩ : syracuseStep 2932079 = 4398119) B4398119
theorem B1954719 : Blo 1953435 1954719 := bstep (se 1 (by rfl) ⟨1466039, by rfl⟩ : syracuseStep 1954719 = 2932079) B2932079
theorem B2932085 : Blo 1953435 2932085 := bbase (se 5 (by rfl) ⟨137441, by rfl⟩ : syracuseStep 2932085 = 274883) (by norm_num)
theorem B1954723 : Blo 1953435 1954723 := bstep (se 1 (by rfl) ⟨1466042, by rfl⟩ : syracuseStep 1954723 = 2932085) B2932085
theorem B2783197 : Blo 1953435 2783197 := bbase (se 3 (by rfl) ⟨521849, by rfl⟩ : syracuseStep 2783197 = 1043699) (by norm_num)
theorem B3710929 : Blo 1953435 3710929 := bstep (se 2 (by rfl) ⟨1391598, by rfl⟩ : syracuseStep 3710929 = 2783197) B2783197
theorem B4947905 : Blo 1953435 4947905 := bstep (se 2 (by rfl) ⟨1855464, by rfl⟩ : syracuseStep 4947905 = 3710929) B3710929
theorem B3298603 : Blo 1953435 3298603 := bstep (se 1 (by rfl) ⟨2473952, by rfl⟩ : syracuseStep 3298603 = 4947905) B4947905
theorem B4398137 : Blo 1953435 4398137 := bstep (se 2 (by rfl) ⟨1649301, by rfl⟩ : syracuseStep 4398137 = 3298603) B3298603
theorem B2932091 : Blo 1953435 2932091 := bstep (se 1 (by rfl) ⟨2199068, by rfl⟩ : syracuseStep 2932091 = 4398137) B4398137
theorem B1954727 : Blo 1953435 1954727 := bstep (se 1 (by rfl) ⟨1466045, by rfl⟩ : syracuseStep 1954727 = 2932091) B2932091
theorem B2199073 : Blo 1953435 2199073 := bbase (se 2 (by rfl) ⟨824652, by rfl⟩ : syracuseStep 2199073 = 1649305) (by norm_num)
theorem B2932097 : Blo 1953435 2932097 := bstep (se 2 (by rfl) ⟨1099536, by rfl⟩ : syracuseStep 2932097 = 2199073) B2199073
theorem B1954731 : Blo 1953435 1954731 := bstep (se 1 (by rfl) ⟨1466048, by rfl⟩ : syracuseStep 1954731 = 2932097) B2932097
theorem B4947925 : Blo 1953435 4947925 := bbase (se 7 (by rfl) ⟨57983, by rfl⟩ : syracuseStep 4947925 = 115967) (by norm_num)
theorem B6597233 : Blo 1953435 6597233 := bstep (se 2 (by rfl) ⟨2473962, by rfl⟩ : syracuseStep 6597233 = 4947925) B4947925
theorem B4398155 : Blo 1953435 4398155 := bstep (se 1 (by rfl) ⟨3298616, by rfl⟩ : syracuseStep 4398155 = 6597233) B6597233
theorem B2932103 : Blo 1953435 2932103 := bstep (se 1 (by rfl) ⟨2199077, by rfl⟩ : syracuseStep 2932103 = 4398155) B4398155
theorem B1954735 : Blo 1953435 1954735 := bstep (se 1 (by rfl) ⟨1466051, by rfl⟩ : syracuseStep 1954735 = 2932103) B2932103
theorem B2932109 : Blo 1953435 2932109 := bbase (se 3 (by rfl) ⟨549770, by rfl⟩ : syracuseStep 2932109 = 1099541) (by norm_num)
theorem B1954739 : Blo 1953435 1954739 := bstep (se 1 (by rfl) ⟨1466054, by rfl⟩ : syracuseStep 1954739 = 2932109) B2932109
theorem B4398173 : Blo 1953435 4398173 := bbase (se 3 (by rfl) ⟨824657, by rfl⟩ : syracuseStep 4398173 = 1649315) (by norm_num)
theorem B2932115 : Blo 1953435 2932115 := bstep (se 1 (by rfl) ⟨2199086, by rfl⟩ : syracuseStep 2932115 = 4398173) B4398173
theorem B1954743 : Blo 1953435 1954743 := bstep (se 1 (by rfl) ⟨1466057, by rfl⟩ : syracuseStep 1954743 = 2932115) B2932115
theorem B3298637 : Blo 1953435 3298637 := bbase (se 3 (by rfl) ⟨618494, by rfl⟩ : syracuseStep 3298637 = 1236989) (by norm_num)
theorem B2199091 : Blo 1953435 2199091 := bstep (se 1 (by rfl) ⟨1649318, by rfl⟩ : syracuseStep 2199091 = 3298637) B3298637
theorem B2932121 : Blo 1953435 2932121 := bstep (se 2 (by rfl) ⟨1099545, by rfl⟩ : syracuseStep 2932121 = 2199091) B2199091
theorem B1954747 : Blo 1953435 1954747 := bstep (se 1 (by rfl) ⟨1466060, by rfl⟩ : syracuseStep 1954747 = 2932121) B2932121
theorem B3761605 : Blo 1953435 3761605 := bbase (se 4 (by rfl) ⟨352650, by rfl⟩ : syracuseStep 3761605 = 705301) (by norm_num)
theorem B20061893 : Blo 1953435 20061893 := bstep (se 4 (by rfl) ⟨1880802, by rfl⟩ : syracuseStep 20061893 = 3761605) B3761605
theorem B13374595 : Blo 1953435 13374595 := bstep (se 1 (by rfl) ⟨10030946, by rfl⟩ : syracuseStep 13374595 = 20061893) B20061893
theorem B17832793 : Blo 1953435 17832793 := bstep (se 2 (by rfl) ⟨6687297, by rfl⟩ : syracuseStep 17832793 = 13374595) B13374595
theorem B23777057 : Blo 1953435 23777057 := bstep (se 2 (by rfl) ⟨8916396, by rfl⟩ : syracuseStep 23777057 = 17832793) B17832793
theorem B15851371 : Blo 1953435 15851371 := bstep (se 1 (by rfl) ⟨11888528, by rfl⟩ : syracuseStep 15851371 = 23777057) B23777057
theorem B21135161 : Blo 1953435 21135161 := bstep (se 2 (by rfl) ⟨7925685, by rfl⟩ : syracuseStep 21135161 = 15851371) B15851371
theorem B14090107 : Blo 1953435 14090107 := bstep (se 1 (by rfl) ⟨10567580, by rfl⟩ : syracuseStep 14090107 = 21135161) B21135161
theorem B18786809 : Blo 1953435 18786809 := bstep (se 2 (by rfl) ⟨7045053, by rfl⟩ : syracuseStep 18786809 = 14090107) B14090107
theorem B12524539 : Blo 1953435 12524539 := bstep (se 1 (by rfl) ⟨9393404, by rfl⟩ : syracuseStep 12524539 = 18786809) B18786809
theorem B16699385 : Blo 1953435 16699385 := bstep (se 2 (by rfl) ⟨6262269, by rfl⟩ : syracuseStep 16699385 = 12524539) B12524539
theorem B11132923 : Blo 1953435 11132923 := bstep (se 1 (by rfl) ⟨8349692, by rfl⟩ : syracuseStep 11132923 = 16699385) B16699385
theorem B14843897 : Blo 1953435 14843897 := bstep (se 2 (by rfl) ⟨5566461, by rfl⟩ : syracuseStep 14843897 = 11132923) B11132923
theorem B9895931 : Blo 1953435 9895931 := bstep (se 1 (by rfl) ⟨7421948, by rfl⟩ : syracuseStep 9895931 = 14843897) B14843897
theorem B6597287 : Blo 1953435 6597287 := bstep (se 1 (by rfl) ⟨4947965, by rfl⟩ : syracuseStep 6597287 = 9895931) B9895931
theorem B4398191 : Blo 1953435 4398191 := bstep (se 1 (by rfl) ⟨3298643, by rfl⟩ : syracuseStep 4398191 = 6597287) B6597287
theorem B2932127 : Blo 1953435 2932127 := bstep (se 1 (by rfl) ⟨2199095, by rfl⟩ : syracuseStep 2932127 = 4398191) B4398191
theorem B1954751 : Blo 1953435 1954751 := bstep (se 1 (by rfl) ⟨1466063, by rfl⟩ : syracuseStep 1954751 = 2932127) B2932127
theorem B2932133 : Blo 1953435 2932133 := bbase (se 4 (by rfl) ⟨274887, by rfl⟩ : syracuseStep 2932133 = 549775) (by norm_num)
theorem B1954755 : Blo 1953435 1954755 := bstep (se 1 (by rfl) ⟨1466066, by rfl⟩ : syracuseStep 1954755 = 2932133) B2932133
theorem B2473993 : Blo 1953435 2473993 := bbase (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) (by norm_num)
theorem B3298657 : Blo 1953435 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B4398209 : Blo 1953435 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B2932139 : Blo 1953435 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B1954759 : Blo 1953435 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B2199109 : Blo 1953435 2199109 := bbase (se 4 (by rfl) ⟨206166, by rfl⟩ : syracuseStep 2199109 = 412333) (by norm_num)
theorem B2932145 : Blo 1953435 2932145 := bstep (se 2 (by rfl) ⟨1099554, by rfl⟩ : syracuseStep 2932145 = 2199109) B2199109
theorem B1954763 : Blo 1953435 1954763 := bstep (se 1 (by rfl) ⟨1466072, by rfl⟩ : syracuseStep 1954763 = 2932145) B2932145
theorem B3711005 : Blo 1953435 3711005 := bbase (se 3 (by rfl) ⟨695813, by rfl⟩ : syracuseStep 3711005 = 1391627) (by norm_num)
theorem B2474003 : Blo 1953435 2474003 := bstep (se 1 (by rfl) ⟨1855502, by rfl⟩ : syracuseStep 2474003 = 3711005) B3711005
theorem B6597341 : Blo 1953435 6597341 := bstep (se 3 (by rfl) ⟨1237001, by rfl⟩ : syracuseStep 6597341 = 2474003) B2474003
theorem B4398227 : Blo 1953435 4398227 := bstep (se 1 (by rfl) ⟨3298670, by rfl⟩ : syracuseStep 4398227 = 6597341) B6597341
theorem B2932151 : Blo 1953435 2932151 := bstep (se 1 (by rfl) ⟨2199113, by rfl⟩ : syracuseStep 2932151 = 4398227) B4398227
theorem B1954767 : Blo 1953435 1954767 := bstep (se 1 (by rfl) ⟨1466075, by rfl⟩ : syracuseStep 1954767 = 2932151) B2932151
theorem B2932157 : Blo 1953435 2932157 := bbase (se 3 (by rfl) ⟨549779, by rfl⟩ : syracuseStep 2932157 = 1099559) (by norm_num)
theorem B1954771 : Blo 1953435 1954771 := bstep (se 1 (by rfl) ⟨1466078, by rfl⟩ : syracuseStep 1954771 = 2932157) B2932157
theorem B4398245 : Blo 1953435 4398245 := bbase (se 4 (by rfl) ⟨412335, by rfl⟩ : syracuseStep 4398245 = 824671) (by norm_num)
theorem B2932163 : Blo 1953435 2932163 := bstep (se 1 (by rfl) ⟨2199122, by rfl⟩ : syracuseStep 2932163 = 4398245) B4398245
theorem B1954775 : Blo 1953435 1954775 := bstep (se 1 (by rfl) ⟨1466081, by rfl⟩ : syracuseStep 1954775 = 2932163) B2932163
theorem B4948037 : Blo 1953435 4948037 := bbase (se 4 (by rfl) ⟨463878, by rfl⟩ : syracuseStep 4948037 = 927757) (by norm_num)
theorem B3298691 : Blo 1953435 3298691 := bstep (se 1 (by rfl) ⟨2474018, by rfl⟩ : syracuseStep 3298691 = 4948037) B4948037
theorem B2199127 : Blo 1953435 2199127 := bstep (se 1 (by rfl) ⟨1649345, by rfl⟩ : syracuseStep 2199127 = 3298691) B3298691
theorem B2932169 : Blo 1953435 2932169 := bstep (se 2 (by rfl) ⟨1099563, by rfl⟩ : syracuseStep 2932169 = 2199127) B2199127
theorem B1954779 : Blo 1953435 1954779 := bstep (se 1 (by rfl) ⟨1466084, by rfl⟩ : syracuseStep 1954779 = 2932169) B2932169
theorem B6262373 : Blo 1953435 6262373 := bbase (se 4 (by rfl) ⟨587097, by rfl⟩ : syracuseStep 6262373 = 1174195) (by norm_num)
theorem B4174915 : Blo 1953435 4174915 := bstep (se 1 (by rfl) ⟨3131186, by rfl⟩ : syracuseStep 4174915 = 6262373) B6262373
theorem B5566553 : Blo 1953435 5566553 := bstep (se 2 (by rfl) ⟨2087457, by rfl⟩ : syracuseStep 5566553 = 4174915) B4174915
theorem B3711035 : Blo 1953435 3711035 := bstep (se 1 (by rfl) ⟨2783276, by rfl⟩ : syracuseStep 3711035 = 5566553) B5566553
theorem B9896093 : Blo 1953435 9896093 := bstep (se 3 (by rfl) ⟨1855517, by rfl⟩ : syracuseStep 9896093 = 3711035) B3711035
theorem B6597395 : Blo 1953435 6597395 := bstep (se 1 (by rfl) ⟨4948046, by rfl⟩ : syracuseStep 6597395 = 9896093) B9896093
theorem B4398263 : Blo 1953435 4398263 := bstep (se 1 (by rfl) ⟨3298697, by rfl⟩ : syracuseStep 4398263 = 6597395) B6597395
theorem B2932175 : Blo 1953435 2932175 := bstep (se 1 (by rfl) ⟨2199131, by rfl⟩ : syracuseStep 2932175 = 4398263) B4398263
theorem B1954783 : Blo 1953435 1954783 := bstep (se 1 (by rfl) ⟨1466087, by rfl⟩ : syracuseStep 1954783 = 2932175) B2932175
theorem B2932181 : Blo 1953435 2932181 := bbase (se 7 (by rfl) ⟨34361, by rfl⟩ : syracuseStep 2932181 = 68723) (by norm_num)
theorem B1954787 : Blo 1953435 1954787 := bstep (se 1 (by rfl) ⟨1466090, by rfl⟩ : syracuseStep 1954787 = 2932181) B2932181
theorem B7422101 : Blo 1953435 7422101 := bbase (se 6 (by rfl) ⟨173955, by rfl⟩ : syracuseStep 7422101 = 347911) (by norm_num)
theorem B4948067 : Blo 1953435 4948067 := bstep (se 1 (by rfl) ⟨3711050, by rfl⟩ : syracuseStep 4948067 = 7422101) B7422101
theorem B3298711 : Blo 1953435 3298711 := bstep (se 1 (by rfl) ⟨2474033, by rfl⟩ : syracuseStep 3298711 = 4948067) B4948067
theorem B4398281 : Blo 1953435 4398281 := bstep (se 2 (by rfl) ⟨1649355, by rfl⟩ : syracuseStep 4398281 = 3298711) B3298711
theorem B2932187 : Blo 1953435 2932187 := bstep (se 1 (by rfl) ⟨2199140, by rfl⟩ : syracuseStep 2932187 = 4398281) B4398281
theorem B1954791 : Blo 1953435 1954791 := bstep (se 1 (by rfl) ⟨1466093, by rfl⟩ : syracuseStep 1954791 = 2932187) B2932187
theorem B2199145 : Blo 1953435 2199145 := bbase (se 2 (by rfl) ⟨824679, by rfl⟩ : syracuseStep 2199145 = 1649359) (by norm_num)
theorem B2932193 : Blo 1953435 2932193 := bstep (se 2 (by rfl) ⟨1099572, by rfl⟩ : syracuseStep 2932193 = 2199145) B2199145
theorem B1954795 : Blo 1953435 1954795 := bstep (se 1 (by rfl) ⟨1466096, by rfl⟩ : syracuseStep 1954795 = 2932193) B2932193
theorem B4174949 : Blo 1953435 4174949 := bbase (se 4 (by rfl) ⟨391401, by rfl⟩ : syracuseStep 4174949 = 782803) (by norm_num)
theorem B11133197 : Blo 1953435 11133197 := bstep (se 3 (by rfl) ⟨2087474, by rfl⟩ : syracuseStep 11133197 = 4174949) B4174949
theorem B7422131 : Blo 1953435 7422131 := bstep (se 1 (by rfl) ⟨5566598, by rfl⟩ : syracuseStep 7422131 = 11133197) B11133197
theorem B4948087 : Blo 1953435 4948087 := bstep (se 1 (by rfl) ⟨3711065, by rfl⟩ : syracuseStep 4948087 = 7422131) B7422131
theorem B6597449 : Blo 1953435 6597449 := bstep (se 2 (by rfl) ⟨2474043, by rfl⟩ : syracuseStep 6597449 = 4948087) B4948087
theorem B4398299 : Blo 1953435 4398299 := bstep (se 1 (by rfl) ⟨3298724, by rfl⟩ : syracuseStep 4398299 = 6597449) B6597449
theorem B2932199 : Blo 1953435 2932199 := bstep (se 1 (by rfl) ⟨2199149, by rfl⟩ : syracuseStep 2932199 = 4398299) B4398299
theorem B1954799 : Blo 1953435 1954799 := bstep (se 1 (by rfl) ⟨1466099, by rfl⟩ : syracuseStep 1954799 = 2932199) B2932199
theorem B2932205 : Blo 1953435 2932205 := bbase (se 3 (by rfl) ⟨549788, by rfl⟩ : syracuseStep 2932205 = 1099577) (by norm_num)
theorem B1954803 : Blo 1953435 1954803 := bstep (se 1 (by rfl) ⟨1466102, by rfl⟩ : syracuseStep 1954803 = 2932205) B2932205
theorem B4398317 : Blo 1953435 4398317 := bbase (se 3 (by rfl) ⟨824684, by rfl⟩ : syracuseStep 4398317 = 1649369) (by norm_num)
theorem B2932211 : Blo 1953435 2932211 := bstep (se 1 (by rfl) ⟨2199158, by rfl⟩ : syracuseStep 2932211 = 4398317) B4398317
theorem B1954807 : Blo 1953435 1954807 := bstep (se 1 (by rfl) ⟨1466105, by rfl⟩ : syracuseStep 1954807 = 2932211) B2932211
theorem B2783317 : Blo 1953435 2783317 := bbase (se 8 (by rfl) ⟨16308, by rfl⟩ : syracuseStep 2783317 = 32617) (by norm_num)
theorem B3711089 : Blo 1953435 3711089 := bstep (se 2 (by rfl) ⟨1391658, by rfl⟩ : syracuseStep 3711089 = 2783317) B2783317
theorem B2474059 : Blo 1953435 2474059 := bstep (se 1 (by rfl) ⟨1855544, by rfl⟩ : syracuseStep 2474059 = 3711089) B3711089
theorem B3298745 : Blo 1953435 3298745 := bstep (se 2 (by rfl) ⟨1237029, by rfl⟩ : syracuseStep 3298745 = 2474059) B2474059
theorem B2199163 : Blo 1953435 2199163 := bstep (se 1 (by rfl) ⟨1649372, by rfl⟩ : syracuseStep 2199163 = 3298745) B3298745
theorem B2932217 : Blo 1953435 2932217 := bstep (se 2 (by rfl) ⟨1099581, by rfl⟩ : syracuseStep 2932217 = 2199163) B2199163
theorem B1954811 : Blo 1953435 1954811 := bstep (se 1 (by rfl) ⟨1466108, by rfl⟩ : syracuseStep 1954811 = 2932217) B2932217
theorem B9038341 : Blo 1953435 9038341 := bbase (se 4 (by rfl) ⟨847344, by rfl⟩ : syracuseStep 9038341 = 1694689) (by norm_num)
theorem B48204485 : Blo 1953435 48204485 := bstep (se 4 (by rfl) ⟨4519170, by rfl⟩ : syracuseStep 48204485 = 9038341) B9038341
theorem B32136323 : Blo 1953435 32136323 := bstep (se 1 (by rfl) ⟨24102242, by rfl⟩ : syracuseStep 32136323 = 48204485) B48204485
theorem B85696861 : Blo 1953435 85696861 := bstep (se 3 (by rfl) ⟨16068161, by rfl⟩ : syracuseStep 85696861 = 32136323) B32136323
theorem B114262481 : Blo 1953435 114262481 := bstep (se 2 (by rfl) ⟨42848430, by rfl⟩ : syracuseStep 114262481 = 85696861) B85696861
theorem B76174987 : Blo 1953435 76174987 := bstep (se 1 (by rfl) ⟨57131240, by rfl⟩ : syracuseStep 76174987 = 114262481) B114262481
theorem B101566649 : Blo 1953435 101566649 := bstep (se 2 (by rfl) ⟨38087493, by rfl⟩ : syracuseStep 101566649 = 76174987) B76174987
theorem B67711099 : Blo 1953435 67711099 := bstep (se 1 (by rfl) ⟨50783324, by rfl⟩ : syracuseStep 67711099 = 101566649) B101566649
theorem B90281465 : Blo 1953435 90281465 := bstep (se 2 (by rfl) ⟨33855549, by rfl⟩ : syracuseStep 90281465 = 67711099) B67711099
theorem B60187643 : Blo 1953435 60187643 := bstep (se 1 (by rfl) ⟨45140732, by rfl⟩ : syracuseStep 60187643 = 90281465) B90281465
theorem B40125095 : Blo 1953435 40125095 := bstep (se 1 (by rfl) ⟨30093821, by rfl⟩ : syracuseStep 40125095 = 60187643) B60187643
theorem B26750063 : Blo 1953435 26750063 := bstep (se 1 (by rfl) ⟨20062547, by rfl⟩ : syracuseStep 26750063 = 40125095) B40125095
theorem B17833375 : Blo 1953435 17833375 := bstep (se 1 (by rfl) ⟨13375031, by rfl⟩ : syracuseStep 17833375 = 26750063) B26750063
theorem B95111333 : Blo 1953435 95111333 := bstep (se 4 (by rfl) ⟨8916687, by rfl⟩ : syracuseStep 95111333 = 17833375) B17833375
theorem B63407555 : Blo 1953435 63407555 := bstep (se 1 (by rfl) ⟨47555666, by rfl⟩ : syracuseStep 63407555 = 95111333) B95111333
theorem B42271703 : Blo 1953435 42271703 := bstep (se 1 (by rfl) ⟨31703777, by rfl⟩ : syracuseStep 42271703 = 63407555) B63407555
theorem B28181135 : Blo 1953435 28181135 := bstep (se 1 (by rfl) ⟨21135851, by rfl⟩ : syracuseStep 28181135 = 42271703) B42271703
theorem B75149693 : Blo 1953435 75149693 := bstep (se 3 (by rfl) ⟨14090567, by rfl⟩ : syracuseStep 75149693 = 28181135) B28181135
theorem B50099795 : Blo 1953435 50099795 := bstep (se 1 (by rfl) ⟨37574846, by rfl⟩ : syracuseStep 50099795 = 75149693) B75149693
theorem B33399863 : Blo 1953435 33399863 := bstep (se 1 (by rfl) ⟨25049897, by rfl⟩ : syracuseStep 33399863 = 50099795) B50099795
theorem B22266575 : Blo 1953435 22266575 := bstep (se 1 (by rfl) ⟨16699931, by rfl⟩ : syracuseStep 22266575 = 33399863) B33399863
theorem B14844383 : Blo 1953435 14844383 := bstep (se 1 (by rfl) ⟨11133287, by rfl⟩ : syracuseStep 14844383 = 22266575) B22266575
theorem B9896255 : Blo 1953435 9896255 := bstep (se 1 (by rfl) ⟨7422191, by rfl⟩ : syracuseStep 9896255 = 14844383) B14844383
theorem B6597503 : Blo 1953435 6597503 := bstep (se 1 (by rfl) ⟨4948127, by rfl⟩ : syracuseStep 6597503 = 9896255) B9896255
theorem B4398335 : Blo 1953435 4398335 := bstep (se 1 (by rfl) ⟨3298751, by rfl⟩ : syracuseStep 4398335 = 6597503) B6597503
theorem B2932223 : Blo 1953435 2932223 := bstep (se 1 (by rfl) ⟨2199167, by rfl⟩ : syracuseStep 2932223 = 4398335) B4398335
theorem B1954815 : Blo 1953435 1954815 := bstep (se 1 (by rfl) ⟨1466111, by rfl⟩ : syracuseStep 1954815 = 2932223) B2932223
theorem B2932229 : Blo 1953435 2932229 := bbase (se 4 (by rfl) ⟨274896, by rfl⟩ : syracuseStep 2932229 = 549793) (by norm_num)
theorem B1954819 : Blo 1953435 1954819 := bstep (se 1 (by rfl) ⟨1466114, by rfl⟩ : syracuseStep 1954819 = 2932229) B2932229
theorem B3298765 : Blo 1953435 3298765 := bbase (se 3 (by rfl) ⟨618518, by rfl⟩ : syracuseStep 3298765 = 1237037) (by norm_num)
theorem B4398353 : Blo 1953435 4398353 := bstep (se 2 (by rfl) ⟨1649382, by rfl⟩ : syracuseStep 4398353 = 3298765) B3298765
theorem B2932235 : Blo 1953435 2932235 := bstep (se 1 (by rfl) ⟨2199176, by rfl⟩ : syracuseStep 2932235 = 4398353) B4398353
theorem B1954823 : Blo 1953435 1954823 := bstep (se 1 (by rfl) ⟨1466117, by rfl⟩ : syracuseStep 1954823 = 2932235) B2932235
theorem B2199181 : Blo 1953435 2199181 := bbase (se 3 (by rfl) ⟨412346, by rfl⟩ : syracuseStep 2199181 = 824693) (by norm_num)
theorem B2932241 : Blo 1953435 2932241 := bstep (se 2 (by rfl) ⟨1099590, by rfl⟩ : syracuseStep 2932241 = 2199181) B2199181
theorem B1954827 : Blo 1953435 1954827 := bstep (se 1 (by rfl) ⟨1466120, by rfl⟩ : syracuseStep 1954827 = 2932241) B2932241
theorem B6597557 : Blo 1953435 6597557 := bbase (se 5 (by rfl) ⟨309260, by rfl⟩ : syracuseStep 6597557 = 618521) (by norm_num)
theorem B4398371 : Blo 1953435 4398371 := bstep (se 1 (by rfl) ⟨3298778, by rfl⟩ : syracuseStep 4398371 = 6597557) B6597557
theorem B2932247 : Blo 1953435 2932247 := bstep (se 1 (by rfl) ⟨2199185, by rfl⟩ : syracuseStep 2932247 = 4398371) B4398371
theorem B1954831 : Blo 1953435 1954831 := bstep (se 1 (by rfl) ⟨1466123, by rfl⟩ : syracuseStep 1954831 = 2932247) B2932247
theorem B2932253 : Blo 1953435 2932253 := bbase (se 3 (by rfl) ⟨549797, by rfl⟩ : syracuseStep 2932253 = 1099595) (by norm_num)
theorem B1954835 : Blo 1953435 1954835 := bstep (se 1 (by rfl) ⟨1466126, by rfl⟩ : syracuseStep 1954835 = 2932253) B2932253
theorem B4398389 : Blo 1953435 4398389 := bbase (se 5 (by rfl) ⟨206174, by rfl⟩ : syracuseStep 4398389 = 412349) (by norm_num)
theorem B2932259 : Blo 1953435 2932259 := bstep (se 1 (by rfl) ⟨2199194, by rfl⟩ : syracuseStep 2932259 = 4398389) B4398389
theorem B1954839 : Blo 1953435 1954839 := bstep (se 1 (by rfl) ⟨1466129, by rfl⟩ : syracuseStep 1954839 = 2932259) B2932259
theorem B14090773 : Blo 1953435 14090773 := bbase (se 6 (by rfl) ⟨330252, by rfl⟩ : syracuseStep 14090773 = 660505) (by norm_num)
theorem B18787697 : Blo 1953435 18787697 := bstep (se 2 (by rfl) ⟨7045386, by rfl⟩ : syracuseStep 18787697 = 14090773) B14090773
theorem B12525131 : Blo 1953435 12525131 := bstep (se 1 (by rfl) ⟨9393848, by rfl⟩ : syracuseStep 12525131 = 18787697) B18787697
theorem B8350087 : Blo 1953435 8350087 := bstep (se 1 (by rfl) ⟨6262565, by rfl⟩ : syracuseStep 8350087 = 12525131) B12525131
theorem B11133449 : Blo 1953435 11133449 := bstep (se 2 (by rfl) ⟨4175043, by rfl⟩ : syracuseStep 11133449 = 8350087) B8350087
theorem B7422299 : Blo 1953435 7422299 := bstep (se 1 (by rfl) ⟨5566724, by rfl⟩ : syracuseStep 7422299 = 11133449) B11133449
theorem B4948199 : Blo 1953435 4948199 := bstep (se 1 (by rfl) ⟨3711149, by rfl⟩ : syracuseStep 4948199 = 7422299) B7422299
theorem B3298799 : Blo 1953435 3298799 := bstep (se 1 (by rfl) ⟨2474099, by rfl⟩ : syracuseStep 3298799 = 4948199) B4948199
theorem B2199199 : Blo 1953435 2199199 := bstep (se 1 (by rfl) ⟨1649399, by rfl⟩ : syracuseStep 2199199 = 3298799) B3298799
theorem B2932265 : Blo 1953435 2932265 := bstep (se 2 (by rfl) ⟨1099599, by rfl⟩ : syracuseStep 2932265 = 2199199) B2199199
theorem B1954843 : Blo 1953435 1954843 := bstep (se 1 (by rfl) ⟨1466132, by rfl⟩ : syracuseStep 1954843 = 2932265) B2932265
theorem B18787733 : Blo 1953435 18787733 := bbase (se 6 (by rfl) ⟨440337, by rfl⟩ : syracuseStep 18787733 = 880675) (by norm_num)
theorem B12525155 : Blo 1953435 12525155 := bstep (se 1 (by rfl) ⟨9393866, by rfl⟩ : syracuseStep 12525155 = 18787733) B18787733
theorem B8350103 : Blo 1953435 8350103 := bstep (se 1 (by rfl) ⟨6262577, by rfl⟩ : syracuseStep 8350103 = 12525155) B12525155
theorem B5566735 : Blo 1953435 5566735 := bstep (se 1 (by rfl) ⟨4175051, by rfl⟩ : syracuseStep 5566735 = 8350103) B8350103
theorem B7422313 : Blo 1953435 7422313 := bstep (se 2 (by rfl) ⟨2783367, by rfl⟩ : syracuseStep 7422313 = 5566735) B5566735
theorem B9896417 : Blo 1953435 9896417 := bstep (se 2 (by rfl) ⟨3711156, by rfl⟩ : syracuseStep 9896417 = 7422313) B7422313
theorem B6597611 : Blo 1953435 6597611 := bstep (se 1 (by rfl) ⟨4948208, by rfl⟩ : syracuseStep 6597611 = 9896417) B9896417
theorem B4398407 : Blo 1953435 4398407 := bstep (se 1 (by rfl) ⟨3298805, by rfl⟩ : syracuseStep 4398407 = 6597611) B6597611
theorem B2932271 : Blo 1953435 2932271 := bstep (se 1 (by rfl) ⟨2199203, by rfl⟩ : syracuseStep 2932271 = 4398407) B4398407
theorem B1954847 : Blo 1953435 1954847 := bstep (se 1 (by rfl) ⟨1466135, by rfl⟩ : syracuseStep 1954847 = 2932271) B2932271
theorem B2932277 : Blo 1953435 2932277 := bbase (se 5 (by rfl) ⟨137450, by rfl⟩ : syracuseStep 2932277 = 274901) (by norm_num)
theorem B1954851 : Blo 1953435 1954851 := bstep (se 1 (by rfl) ⟨1466138, by rfl⟩ : syracuseStep 1954851 = 2932277) B2932277
theorem B4948229 : Blo 1953435 4948229 := bbase (se 4 (by rfl) ⟨463896, by rfl⟩ : syracuseStep 4948229 = 927793) (by norm_num)
theorem B3298819 : Blo 1953435 3298819 := bstep (se 1 (by rfl) ⟨2474114, by rfl⟩ : syracuseStep 3298819 = 4948229) B4948229
theorem B4398425 : Blo 1953435 4398425 := bstep (se 2 (by rfl) ⟨1649409, by rfl⟩ : syracuseStep 4398425 = 3298819) B3298819
theorem B2932283 : Blo 1953435 2932283 := bstep (se 1 (by rfl) ⟨2199212, by rfl⟩ : syracuseStep 2932283 = 4398425) B4398425
theorem B1954855 : Blo 1953435 1954855 := bstep (se 1 (by rfl) ⟨1466141, by rfl⟩ : syracuseStep 1954855 = 2932283) B2932283
theorem B2199217 : Blo 1953435 2199217 := bbase (se 2 (by rfl) ⟨824706, by rfl⟩ : syracuseStep 2199217 = 1649413) (by norm_num)
theorem B2932289 : Blo 1953435 2932289 := bstep (se 2 (by rfl) ⟨1099608, by rfl⟩ : syracuseStep 2932289 = 2199217) B2199217
theorem B1954859 : Blo 1953435 1954859 := bstep (se 1 (by rfl) ⟨1466144, by rfl⟩ : syracuseStep 1954859 = 2932289) B2932289
theorem B4696973 : Blo 1953435 4696973 := bbase (se 3 (by rfl) ⟨880682, by rfl⟩ : syracuseStep 4696973 = 1761365) (by norm_num)
theorem B3131315 : Blo 1953435 3131315 := bstep (se 1 (by rfl) ⟨2348486, by rfl⟩ : syracuseStep 3131315 = 4696973) B4696973
theorem B2087543 : Blo 1953435 2087543 := bstep (se 1 (by rfl) ⟨1565657, by rfl⟩ : syracuseStep 2087543 = 3131315) B3131315
theorem B5566781 : Blo 1953435 5566781 := bstep (se 3 (by rfl) ⟨1043771, by rfl⟩ : syracuseStep 5566781 = 2087543) B2087543
theorem B3711187 : Blo 1953435 3711187 := bstep (se 1 (by rfl) ⟨2783390, by rfl⟩ : syracuseStep 3711187 = 5566781) B5566781
theorem B4948249 : Blo 1953435 4948249 := bstep (se 2 (by rfl) ⟨1855593, by rfl⟩ : syracuseStep 4948249 = 3711187) B3711187
theorem B6597665 : Blo 1953435 6597665 := bstep (se 2 (by rfl) ⟨2474124, by rfl⟩ : syracuseStep 6597665 = 4948249) B4948249
theorem B4398443 : Blo 1953435 4398443 := bstep (se 1 (by rfl) ⟨3298832, by rfl⟩ : syracuseStep 4398443 = 6597665) B6597665
theorem B2932295 : Blo 1953435 2932295 := bstep (se 1 (by rfl) ⟨2199221, by rfl⟩ : syracuseStep 2932295 = 4398443) B4398443
theorem B1954863 : Blo 1953435 1954863 := bstep (se 1 (by rfl) ⟨1466147, by rfl⟩ : syracuseStep 1954863 = 2932295) B2932295
theorem B2932301 : Blo 1953435 2932301 := bbase (se 3 (by rfl) ⟨549806, by rfl⟩ : syracuseStep 2932301 = 1099613) (by norm_num)
theorem B1954867 : Blo 1953435 1954867 := bstep (se 1 (by rfl) ⟨1466150, by rfl⟩ : syracuseStep 1954867 = 2932301) B2932301
theorem B4398461 : Blo 1953435 4398461 := bbase (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) (by norm_num)
theorem B2932307 : Blo 1953435 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B1954871 : Blo 1953435 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B3298853 : Blo 1953435 3298853 := bbase (se 4 (by rfl) ⟨309267, by rfl⟩ : syracuseStep 3298853 = 618535) (by norm_num)
theorem B2199235 : Blo 1953435 2199235 := bstep (se 1 (by rfl) ⟨1649426, by rfl⟩ : syracuseStep 2199235 = 3298853) B3298853
theorem B2932313 : Blo 1953435 2932313 := bstep (se 2 (by rfl) ⟨1099617, by rfl⟩ : syracuseStep 2932313 = 2199235) B2199235
theorem B1954875 : Blo 1953435 1954875 := bstep (se 1 (by rfl) ⟨1466156, by rfl⟩ : syracuseStep 1954875 = 2932313) B2932313
theorem B2783413 : Blo 1953435 2783413 := bbase (se 5 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 2783413 = 260945) (by norm_num)
theorem B14844869 : Blo 1953435 14844869 := bstep (se 4 (by rfl) ⟨1391706, by rfl⟩ : syracuseStep 14844869 = 2783413) B2783413
theorem B9896579 : Blo 1953435 9896579 := bstep (se 1 (by rfl) ⟨7422434, by rfl⟩ : syracuseStep 9896579 = 14844869) B14844869
theorem B6597719 : Blo 1953435 6597719 := bstep (se 1 (by rfl) ⟨4948289, by rfl⟩ : syracuseStep 6597719 = 9896579) B9896579
theorem B4398479 : Blo 1953435 4398479 := bstep (se 1 (by rfl) ⟨3298859, by rfl⟩ : syracuseStep 4398479 = 6597719) B6597719
theorem B2932319 : Blo 1953435 2932319 := bstep (se 1 (by rfl) ⟨2199239, by rfl⟩ : syracuseStep 2932319 = 4398479) B4398479
theorem B1954879 : Blo 1953435 1954879 := bstep (se 1 (by rfl) ⟨1466159, by rfl⟩ : syracuseStep 1954879 = 2932319) B2932319
theorem B2932325 : Blo 1953435 2932325 := bbase (se 4 (by rfl) ⟨274905, by rfl⟩ : syracuseStep 2932325 = 549811) (by norm_num)
theorem B1954883 : Blo 1953435 1954883 := bstep (se 1 (by rfl) ⟨1466162, by rfl⟩ : syracuseStep 1954883 = 2932325) B2932325
theorem B2087569 : Blo 1953435 2087569 := bbase (se 2 (by rfl) ⟨782838, by rfl⟩ : syracuseStep 2087569 = 1565677) (by norm_num)
theorem B2783425 : Blo 1953435 2783425 := bstep (se 2 (by rfl) ⟨1043784, by rfl⟩ : syracuseStep 2783425 = 2087569) B2087569
theorem B3711233 : Blo 1953435 3711233 := bstep (se 2 (by rfl) ⟨1391712, by rfl⟩ : syracuseStep 3711233 = 2783425) B2783425
theorem B2474155 : Blo 1953435 2474155 := bstep (se 1 (by rfl) ⟨1855616, by rfl⟩ : syracuseStep 2474155 = 3711233) B3711233
theorem B3298873 : Blo 1953435 3298873 := bstep (se 2 (by rfl) ⟨1237077, by rfl⟩ : syracuseStep 3298873 = 2474155) B2474155
theorem B4398497 : Blo 1953435 4398497 := bstep (se 2 (by rfl) ⟨1649436, by rfl⟩ : syracuseStep 4398497 = 3298873) B3298873
theorem B2932331 : Blo 1953435 2932331 := bstep (se 1 (by rfl) ⟨2199248, by rfl⟩ : syracuseStep 2932331 = 4398497) B4398497
theorem B1954887 : Blo 1953435 1954887 := bstep (se 1 (by rfl) ⟨1466165, by rfl⟩ : syracuseStep 1954887 = 2932331) B2932331
theorem B2199253 : Blo 1953435 2199253 := bbase (se 7 (by rfl) ⟨25772, by rfl⟩ : syracuseStep 2199253 = 51545) (by norm_num)
theorem B2932337 : Blo 1953435 2932337 := bstep (se 2 (by rfl) ⟨1099626, by rfl⟩ : syracuseStep 2932337 = 2199253) B2199253
theorem B1954891 : Blo 1953435 1954891 := bstep (se 1 (by rfl) ⟨1466168, by rfl⟩ : syracuseStep 1954891 = 2932337) B2932337
theorem B2474165 : Blo 1953435 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B6597773 : Blo 1953435 6597773 := bstep (se 3 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 6597773 = 2474165) B2474165
theorem B4398515 : Blo 1953435 4398515 := bstep (se 1 (by rfl) ⟨3298886, by rfl⟩ : syracuseStep 4398515 = 6597773) B6597773
theorem B2932343 : Blo 1953435 2932343 := bstep (se 1 (by rfl) ⟨2199257, by rfl⟩ : syracuseStep 2932343 = 4398515) B4398515
theorem B1954895 : Blo 1953435 1954895 := bstep (se 1 (by rfl) ⟨1466171, by rfl⟩ : syracuseStep 1954895 = 2932343) B2932343
theorem B2932349 : Blo 1953435 2932349 := bbase (se 3 (by rfl) ⟨549815, by rfl⟩ : syracuseStep 2932349 = 1099631) (by norm_num)
theorem B1954899 : Blo 1953435 1954899 := bstep (se 1 (by rfl) ⟨1466174, by rfl⟩ : syracuseStep 1954899 = 2932349) B2932349
theorem B4398533 : Blo 1953435 4398533 := bbase (se 4 (by rfl) ⟨412362, by rfl⟩ : syracuseStep 4398533 = 824725) (by norm_num)
theorem B2932355 : Blo 1953435 2932355 := bstep (se 1 (by rfl) ⟨2199266, by rfl⟩ : syracuseStep 2932355 = 4398533) B4398533
theorem B1954903 : Blo 1953435 1954903 := bstep (se 1 (by rfl) ⟨1466177, by rfl⟩ : syracuseStep 1954903 = 2932355) B2932355
theorem B4458557 : Blo 1953435 4458557 := bbase (se 3 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 4458557 = 1671959) (by norm_num)
theorem B2972371 : Blo 1953435 2972371 := bstep (se 1 (by rfl) ⟨2229278, by rfl⟩ : syracuseStep 2972371 = 4458557) B4458557
theorem B3963161 : Blo 1953435 3963161 := bstep (se 2 (by rfl) ⟨1486185, by rfl⟩ : syracuseStep 3963161 = 2972371) B2972371
theorem B2642107 : Blo 1953435 2642107 := bstep (se 1 (by rfl) ⟨1981580, by rfl⟩ : syracuseStep 2642107 = 3963161) B3963161
theorem B3522809 : Blo 1953435 3522809 := bstep (se 2 (by rfl) ⟨1321053, by rfl⟩ : syracuseStep 3522809 = 2642107) B2642107
theorem B9394157 : Blo 1953435 9394157 := bstep (se 3 (by rfl) ⟨1761404, by rfl⟩ : syracuseStep 9394157 = 3522809) B3522809
theorem B6262771 : Blo 1953435 6262771 := bstep (se 1 (by rfl) ⟨4697078, by rfl⟩ : syracuseStep 6262771 = 9394157) B9394157
theorem B8350361 : Blo 1953435 8350361 := bstep (se 2 (by rfl) ⟨3131385, by rfl⟩ : syracuseStep 8350361 = 6262771) B6262771
theorem B5566907 : Blo 1953435 5566907 := bstep (se 1 (by rfl) ⟨4175180, by rfl⟩ : syracuseStep 5566907 = 8350361) B8350361
theorem B3711271 : Blo 1953435 3711271 := bstep (se 1 (by rfl) ⟨2783453, by rfl⟩ : syracuseStep 3711271 = 5566907) B5566907
theorem B4948361 : Blo 1953435 4948361 := bstep (se 2 (by rfl) ⟨1855635, by rfl⟩ : syracuseStep 4948361 = 3711271) B3711271
theorem B3298907 : Blo 1953435 3298907 := bstep (se 1 (by rfl) ⟨2474180, by rfl⟩ : syracuseStep 3298907 = 4948361) B4948361
theorem B2199271 : Blo 1953435 2199271 := bstep (se 1 (by rfl) ⟨1649453, by rfl⟩ : syracuseStep 2199271 = 3298907) B3298907
theorem B2932361 : Blo 1953435 2932361 := bstep (se 2 (by rfl) ⟨1099635, by rfl⟩ : syracuseStep 2932361 = 2199271) B2199271
theorem B1954907 : Blo 1953435 1954907 := bstep (se 1 (by rfl) ⟨1466180, by rfl⟩ : syracuseStep 1954907 = 2932361) B2932361
theorem B9896741 : Blo 1953435 9896741 := bbase (se 4 (by rfl) ⟨927819, by rfl⟩ : syracuseStep 9896741 = 1855639) (by norm_num)
theorem B6597827 : Blo 1953435 6597827 := bstep (se 1 (by rfl) ⟨4948370, by rfl⟩ : syracuseStep 6597827 = 9896741) B9896741
theorem B4398551 : Blo 1953435 4398551 := bstep (se 1 (by rfl) ⟨3298913, by rfl⟩ : syracuseStep 4398551 = 6597827) B6597827
theorem B2932367 : Blo 1953435 2932367 := bstep (se 1 (by rfl) ⟨2199275, by rfl⟩ : syracuseStep 2932367 = 4398551) B4398551
theorem B1954911 : Blo 1953435 1954911 := bstep (se 1 (by rfl) ⟨1466183, by rfl⟩ : syracuseStep 1954911 = 2932367) B2932367
theorem B2932373 : Blo 1953435 2932373 := bbase (se 6 (by rfl) ⟨68727, by rfl⟩ : syracuseStep 2932373 = 137455) (by norm_num)
theorem B1954915 : Blo 1953435 1954915 := bstep (se 1 (by rfl) ⟨1466186, by rfl⟩ : syracuseStep 1954915 = 2932373) B2932373
theorem B9394213 : Blo 1953435 9394213 := bbase (se 4 (by rfl) ⟨880707, by rfl⟩ : syracuseStep 9394213 = 1761415) (by norm_num)
theorem B12525617 : Blo 1953435 12525617 := bstep (se 2 (by rfl) ⟨4697106, by rfl⟩ : syracuseStep 12525617 = 9394213) B9394213
theorem B8350411 : Blo 1953435 8350411 := bstep (se 1 (by rfl) ⟨6262808, by rfl⟩ : syracuseStep 8350411 = 12525617) B12525617
theorem B11133881 : Blo 1953435 11133881 := bstep (se 2 (by rfl) ⟨4175205, by rfl⟩ : syracuseStep 11133881 = 8350411) B8350411
theorem B7422587 : Blo 1953435 7422587 := bstep (se 1 (by rfl) ⟨5566940, by rfl⟩ : syracuseStep 7422587 = 11133881) B11133881
theorem B4948391 : Blo 1953435 4948391 := bstep (se 1 (by rfl) ⟨3711293, by rfl⟩ : syracuseStep 4948391 = 7422587) B7422587
theorem B3298927 : Blo 1953435 3298927 := bstep (se 1 (by rfl) ⟨2474195, by rfl⟩ : syracuseStep 3298927 = 4948391) B4948391
theorem B4398569 : Blo 1953435 4398569 := bstep (se 2 (by rfl) ⟨1649463, by rfl⟩ : syracuseStep 4398569 = 3298927) B3298927
theorem B2932379 : Blo 1953435 2932379 := bstep (se 1 (by rfl) ⟨2199284, by rfl⟩ : syracuseStep 2932379 = 4398569) B4398569
theorem B1954919 : Blo 1953435 1954919 := bstep (se 1 (by rfl) ⟨1466189, by rfl⟩ : syracuseStep 1954919 = 2932379) B2932379
theorem B2199289 : Blo 1953435 2199289 := bbase (se 2 (by rfl) ⟨824733, by rfl⟩ : syracuseStep 2199289 = 1649467) (by norm_num)
theorem B2932385 : Blo 1953435 2932385 := bstep (se 2 (by rfl) ⟨1099644, by rfl⟩ : syracuseStep 2932385 = 2199289) B2199289
theorem B1954923 : Blo 1953435 1954923 := bstep (se 1 (by rfl) ⟨1466192, by rfl⟩ : syracuseStep 1954923 = 2932385) B2932385
theorem B3522845 : Blo 1953435 3522845 := bbase (se 3 (by rfl) ⟨660533, by rfl⟩ : syracuseStep 3522845 = 1321067) (by norm_num)
theorem B2348563 : Blo 1953435 2348563 := bstep (se 1 (by rfl) ⟨1761422, by rfl⟩ : syracuseStep 2348563 = 3522845) B3522845
theorem B3131417 : Blo 1953435 3131417 := bstep (se 2 (by rfl) ⟨1174281, by rfl⟩ : syracuseStep 3131417 = 2348563) B2348563
theorem B8350445 : Blo 1953435 8350445 := bstep (se 3 (by rfl) ⟨1565708, by rfl⟩ : syracuseStep 8350445 = 3131417) B3131417
theorem B5566963 : Blo 1953435 5566963 := bstep (se 1 (by rfl) ⟨4175222, by rfl⟩ : syracuseStep 5566963 = 8350445) B8350445
theorem B7422617 : Blo 1953435 7422617 := bstep (se 2 (by rfl) ⟨2783481, by rfl⟩ : syracuseStep 7422617 = 5566963) B5566963
theorem B4948411 : Blo 1953435 4948411 := bstep (se 1 (by rfl) ⟨3711308, by rfl⟩ : syracuseStep 4948411 = 7422617) B7422617
theorem B6597881 : Blo 1953435 6597881 := bstep (se 2 (by rfl) ⟨2474205, by rfl⟩ : syracuseStep 6597881 = 4948411) B4948411
theorem B4398587 : Blo 1953435 4398587 := bstep (se 1 (by rfl) ⟨3298940, by rfl⟩ : syracuseStep 4398587 = 6597881) B6597881
theorem B2932391 : Blo 1953435 2932391 := bstep (se 1 (by rfl) ⟨2199293, by rfl⟩ : syracuseStep 2932391 = 4398587) B4398587
theorem B1954927 : Blo 1953435 1954927 := bstep (se 1 (by rfl) ⟨1466195, by rfl⟩ : syracuseStep 1954927 = 2932391) B2932391
theorem B2932397 : Blo 1953435 2932397 := bbase (se 3 (by rfl) ⟨549824, by rfl⟩ : syracuseStep 2932397 = 1099649) (by norm_num)
theorem B1954931 : Blo 1953435 1954931 := bstep (se 1 (by rfl) ⟨1466198, by rfl⟩ : syracuseStep 1954931 = 2932397) B2932397
theorem B4398605 : Blo 1953435 4398605 := bbase (se 3 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 4398605 = 1649477) (by norm_num)
theorem B2932403 : Blo 1953435 2932403 := bstep (se 1 (by rfl) ⟨2199302, by rfl⟩ : syracuseStep 2932403 = 4398605) B4398605
theorem B1954935 : Blo 1953435 1954935 := bstep (se 1 (by rfl) ⟨1466201, by rfl⟩ : syracuseStep 1954935 = 2932403) B2932403
theorem B2474221 : Blo 1953435 2474221 := bbase (se 3 (by rfl) ⟨463916, by rfl⟩ : syracuseStep 2474221 = 927833) (by norm_num)
theorem B3298961 : Blo 1953435 3298961 := bstep (se 2 (by rfl) ⟨1237110, by rfl⟩ : syracuseStep 3298961 = 2474221) B2474221
theorem B2199307 : Blo 1953435 2199307 := bstep (se 1 (by rfl) ⟨1649480, by rfl⟩ : syracuseStep 2199307 = 3298961) B3298961
theorem B2932409 : Blo 1953435 2932409 := bstep (se 2 (by rfl) ⟨1099653, by rfl⟩ : syracuseStep 2932409 = 2199307) B2199307
theorem B1954939 : Blo 1953435 1954939 := bstep (se 1 (by rfl) ⟨1466204, by rfl⟩ : syracuseStep 1954939 = 2932409) B2932409
theorem B21137237 : Blo 1953435 21137237 := bbase (se 9 (by rfl) ⟨61925, by rfl⟩ : syracuseStep 21137237 = 123851) (by norm_num)
theorem B14091491 : Blo 1953435 14091491 := bstep (se 1 (by rfl) ⟨10568618, by rfl⟩ : syracuseStep 14091491 = 21137237) B21137237
theorem B9394327 : Blo 1953435 9394327 := bstep (se 1 (by rfl) ⟨7045745, by rfl⟩ : syracuseStep 9394327 = 14091491) B14091491
theorem B12525769 : Blo 1953435 12525769 := bstep (se 2 (by rfl) ⟨4697163, by rfl⟩ : syracuseStep 12525769 = 9394327) B9394327
theorem B16701025 : Blo 1953435 16701025 := bstep (se 2 (by rfl) ⟨6262884, by rfl⟩ : syracuseStep 16701025 = 12525769) B12525769
theorem B22268033 : Blo 1953435 22268033 := bstep (se 2 (by rfl) ⟨8350512, by rfl⟩ : syracuseStep 22268033 = 16701025) B16701025
theorem B14845355 : Blo 1953435 14845355 := bstep (se 1 (by rfl) ⟨11134016, by rfl⟩ : syracuseStep 14845355 = 22268033) B22268033
theorem B9896903 : Blo 1953435 9896903 := bstep (se 1 (by rfl) ⟨7422677, by rfl⟩ : syracuseStep 9896903 = 14845355) B14845355
theorem B6597935 : Blo 1953435 6597935 := bstep (se 1 (by rfl) ⟨4948451, by rfl⟩ : syracuseStep 6597935 = 9896903) B9896903
theorem B4398623 : Blo 1953435 4398623 := bstep (se 1 (by rfl) ⟨3298967, by rfl⟩ : syracuseStep 4398623 = 6597935) B6597935
theorem B2932415 : Blo 1953435 2932415 := bstep (se 1 (by rfl) ⟨2199311, by rfl⟩ : syracuseStep 2932415 = 4398623) B4398623
theorem B1954943 : Blo 1953435 1954943 := bstep (se 1 (by rfl) ⟨1466207, by rfl⟩ : syracuseStep 1954943 = 2932415) B2932415
theorem B2932421 : Blo 1953435 2932421 := bbase (se 4 (by rfl) ⟨274914, by rfl⟩ : syracuseStep 2932421 = 549829) (by norm_num)
theorem B1954947 : Blo 1953435 1954947 := bstep (se 1 (by rfl) ⟨1466210, by rfl⟩ : syracuseStep 1954947 = 2932421) B2932421
theorem B3298981 : Blo 1953435 3298981 := bbase (se 4 (by rfl) ⟨309279, by rfl⟩ : syracuseStep 3298981 = 618559) (by norm_num)
theorem B4398641 : Blo 1953435 4398641 := bstep (se 2 (by rfl) ⟨1649490, by rfl⟩ : syracuseStep 4398641 = 3298981) B3298981
theorem B2932427 : Blo 1953435 2932427 := bstep (se 1 (by rfl) ⟨2199320, by rfl⟩ : syracuseStep 2932427 = 4398641) B4398641
theorem B1954951 : Blo 1953435 1954951 := bstep (se 1 (by rfl) ⟨1466213, by rfl⟩ : syracuseStep 1954951 = 2932427) B2932427
theorem B2199325 : Blo 1953435 2199325 := bbase (se 3 (by rfl) ⟨412373, by rfl⟩ : syracuseStep 2199325 = 824747) (by norm_num)
theorem B2932433 : Blo 1953435 2932433 := bstep (se 2 (by rfl) ⟨1099662, by rfl⟩ : syracuseStep 2932433 = 2199325) B2199325
theorem B1954955 : Blo 1953435 1954955 := bstep (se 1 (by rfl) ⟨1466216, by rfl⟩ : syracuseStep 1954955 = 2932433) B2932433
theorem B6597989 : Blo 1953435 6597989 := bbase (se 4 (by rfl) ⟨618561, by rfl⟩ : syracuseStep 6597989 = 1237123) (by norm_num)
theorem B4398659 : Blo 1953435 4398659 := bstep (se 1 (by rfl) ⟨3298994, by rfl⟩ : syracuseStep 4398659 = 6597989) B6597989
theorem B2932439 : Blo 1953435 2932439 := bstep (se 1 (by rfl) ⟨2199329, by rfl⟩ : syracuseStep 2932439 = 4398659) B4398659
theorem B1954959 : Blo 1953435 1954959 := bstep (se 1 (by rfl) ⟨1466219, by rfl⟩ : syracuseStep 1954959 = 2932439) B2932439
theorem B2932445 : Blo 1953435 2932445 := bbase (se 3 (by rfl) ⟨549833, by rfl⟩ : syracuseStep 2932445 = 1099667) (by norm_num)
theorem B1954963 : Blo 1953435 1954963 := bstep (se 1 (by rfl) ⟨1466222, by rfl⟩ : syracuseStep 1954963 = 2932445) B2932445
theorem B4398677 : Blo 1953435 4398677 := bbase (se 8 (by rfl) ⟨25773, by rfl⟩ : syracuseStep 4398677 = 51547) (by norm_num)
theorem B2932451 : Blo 1953435 2932451 := bstep (se 1 (by rfl) ⟨2199338, by rfl⟩ : syracuseStep 2932451 = 4398677) B4398677
theorem B1954967 : Blo 1953435 1954967 := bstep (se 1 (by rfl) ⟨1466225, by rfl⟩ : syracuseStep 1954967 = 2932451) B2932451
theorem B4175317 : Blo 1953435 4175317 := bbase (se 7 (by rfl) ⟨48929, by rfl⟩ : syracuseStep 4175317 = 97859) (by norm_num)
theorem B5567089 : Blo 1953435 5567089 := bstep (se 2 (by rfl) ⟨2087658, by rfl⟩ : syracuseStep 5567089 = 4175317) B4175317
theorem B7422785 : Blo 1953435 7422785 := bstep (se 2 (by rfl) ⟨2783544, by rfl⟩ : syracuseStep 7422785 = 5567089) B5567089
theorem B4948523 : Blo 1953435 4948523 := bstep (se 1 (by rfl) ⟨3711392, by rfl⟩ : syracuseStep 4948523 = 7422785) B7422785
theorem B3299015 : Blo 1953435 3299015 := bstep (se 1 (by rfl) ⟨2474261, by rfl⟩ : syracuseStep 3299015 = 4948523) B4948523
theorem B2199343 : Blo 1953435 2199343 := bstep (se 1 (by rfl) ⟨1649507, by rfl⟩ : syracuseStep 2199343 = 3299015) B3299015
theorem B2932457 : Blo 1953435 2932457 := bstep (se 2 (by rfl) ⟨1099671, by rfl⟩ : syracuseStep 2932457 = 2199343) B2199343
theorem B1954971 : Blo 1953435 1954971 := bstep (se 1 (by rfl) ⟨1466228, by rfl⟩ : syracuseStep 1954971 = 2932457) B2932457
theorem B7045861 : Blo 1953435 7045861 := bbase (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) (by norm_num)
theorem B9394481 : Blo 1953435 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B25051949 : Blo 1953435 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B16701299 : Blo 1953435 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B11134199 : Blo 1953435 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B7422799 : Blo 1953435 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B9897065 : Blo 1953435 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B6598043 : Blo 1953435 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B4398695 : Blo 1953435 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B2932463 : Blo 1953435 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B1954975 : Blo 1953435 1954975 := bstep (se 1 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 1954975 = 2932463) B2932463
theorem B2932469 : Blo 1953435 2932469 := bbase (se 5 (by rfl) ⟨137459, by rfl⟩ : syracuseStep 2932469 = 274919) (by norm_num)
theorem B1954979 : Blo 1953435 1954979 := bstep (se 1 (by rfl) ⟨1466234, by rfl⟩ : syracuseStep 1954979 = 2932469) B2932469
theorem B4697261 : Blo 1953435 4697261 := bbase (se 3 (by rfl) ⟨880736, by rfl⟩ : syracuseStep 4697261 = 1761473) (by norm_num)
theorem B3131507 : Blo 1953435 3131507 := bstep (se 1 (by rfl) ⟨2348630, by rfl⟩ : syracuseStep 3131507 = 4697261) B4697261
theorem B8350685 : Blo 1953435 8350685 := bstep (se 3 (by rfl) ⟨1565753, by rfl⟩ : syracuseStep 8350685 = 3131507) B3131507
theorem B5567123 : Blo 1953435 5567123 := bstep (se 1 (by rfl) ⟨4175342, by rfl⟩ : syracuseStep 5567123 = 8350685) B8350685
theorem B3711415 : Blo 1953435 3711415 := bstep (se 1 (by rfl) ⟨2783561, by rfl⟩ : syracuseStep 3711415 = 5567123) B5567123
theorem B4948553 : Blo 1953435 4948553 := bstep (se 2 (by rfl) ⟨1855707, by rfl⟩ : syracuseStep 4948553 = 3711415) B3711415
theorem B3299035 : Blo 1953435 3299035 := bstep (se 1 (by rfl) ⟨2474276, by rfl⟩ : syracuseStep 3299035 = 4948553) B4948553
theorem B4398713 : Blo 1953435 4398713 := bstep (se 2 (by rfl) ⟨1649517, by rfl⟩ : syracuseStep 4398713 = 3299035) B3299035
theorem B2932475 : Blo 1953435 2932475 := bstep (se 1 (by rfl) ⟨2199356, by rfl⟩ : syracuseStep 2932475 = 4398713) B4398713
theorem B1954983 : Blo 1953435 1954983 := bstep (se 1 (by rfl) ⟨1466237, by rfl⟩ : syracuseStep 1954983 = 2932475) B2932475
theorem B2199361 : Blo 1953435 2199361 := bbase (se 2 (by rfl) ⟨824760, by rfl⟩ : syracuseStep 2199361 = 1649521) (by norm_num)
theorem B2932481 : Blo 1953435 2932481 := bstep (se 2 (by rfl) ⟨1099680, by rfl⟩ : syracuseStep 2932481 = 2199361) B2199361
theorem B1954987 : Blo 1953435 1954987 := bstep (se 1 (by rfl) ⟨1466240, by rfl⟩ : syracuseStep 1954987 = 2932481) B2932481
theorem B4948573 : Blo 1953435 4948573 := bbase (se 3 (by rfl) ⟨927857, by rfl⟩ : syracuseStep 4948573 = 1855715) (by norm_num)
theorem B6598097 : Blo 1953435 6598097 := bstep (se 2 (by rfl) ⟨2474286, by rfl⟩ : syracuseStep 6598097 = 4948573) B4948573
theorem B4398731 : Blo 1953435 4398731 := bstep (se 1 (by rfl) ⟨3299048, by rfl⟩ : syracuseStep 4398731 = 6598097) B6598097
theorem B2932487 : Blo 1953435 2932487 := bstep (se 1 (by rfl) ⟨2199365, by rfl⟩ : syracuseStep 2932487 = 4398731) B4398731
theorem B1954991 : Blo 1953435 1954991 := bstep (se 1 (by rfl) ⟨1466243, by rfl⟩ : syracuseStep 1954991 = 2932487) B2932487
theorem B2932493 : Blo 1953435 2932493 := bbase (se 3 (by rfl) ⟨549842, by rfl⟩ : syracuseStep 2932493 = 1099685) (by norm_num)
theorem B1954995 : Blo 1953435 1954995 := bstep (se 1 (by rfl) ⟨1466246, by rfl⟩ : syracuseStep 1954995 = 2932493) B2932493
theorem B4398749 : Blo 1953435 4398749 := bbase (se 3 (by rfl) ⟨824765, by rfl⟩ : syracuseStep 4398749 = 1649531) (by norm_num)
theorem B2932499 : Blo 1953435 2932499 := bstep (se 1 (by rfl) ⟨2199374, by rfl⟩ : syracuseStep 2932499 = 4398749) B4398749
theorem B1954999 : Blo 1953435 1954999 := bstep (se 1 (by rfl) ⟨1466249, by rfl⟩ : syracuseStep 1954999 = 2932499) B2932499
theorem B3299069 : Blo 1953435 3299069 := bbase (se 3 (by rfl) ⟨618575, by rfl⟩ : syracuseStep 3299069 = 1237151) (by norm_num)
theorem B2199379 : Blo 1953435 2199379 := bstep (se 1 (by rfl) ⟨1649534, by rfl⟩ : syracuseStep 2199379 = 3299069) B3299069
theorem B2932505 : Blo 1953435 2932505 := bstep (se 2 (by rfl) ⟨1099689, by rfl⟩ : syracuseStep 2932505 = 2199379) B2199379
theorem B1955003 : Blo 1953435 1955003 := bstep (se 1 (by rfl) ⟨1466252, by rfl⟩ : syracuseStep 1955003 = 2932505) B2932505
theorem B3522989 : Blo 1953435 3522989 := bbase (se 3 (by rfl) ⟨660560, by rfl⟩ : syracuseStep 3522989 = 1321121) (by norm_num)
theorem B2348659 : Blo 1953435 2348659 := bstep (se 1 (by rfl) ⟨1761494, by rfl⟩ : syracuseStep 2348659 = 3522989) B3522989
theorem B3131545 : Blo 1953435 3131545 := bstep (se 2 (by rfl) ⟨1174329, by rfl⟩ : syracuseStep 3131545 = 2348659) B2348659
theorem B4175393 : Blo 1953435 4175393 := bstep (se 2 (by rfl) ⟨1565772, by rfl⟩ : syracuseStep 4175393 = 3131545) B3131545
theorem B11134381 : Blo 1953435 11134381 := bstep (se 3 (by rfl) ⟨2087696, by rfl⟩ : syracuseStep 11134381 = 4175393) B4175393
theorem B14845841 : Blo 1953435 14845841 := bstep (se 2 (by rfl) ⟨5567190, by rfl⟩ : syracuseStep 14845841 = 11134381) B11134381
theorem B9897227 : Blo 1953435 9897227 := bstep (se 1 (by rfl) ⟨7422920, by rfl⟩ : syracuseStep 9897227 = 14845841) B14845841
theorem B6598151 : Blo 1953435 6598151 := bstep (se 1 (by rfl) ⟨4948613, by rfl⟩ : syracuseStep 6598151 = 9897227) B9897227
theorem B4398767 : Blo 1953435 4398767 := bstep (se 1 (by rfl) ⟨3299075, by rfl⟩ : syracuseStep 4398767 = 6598151) B6598151
theorem B2932511 : Blo 1953435 2932511 := bstep (se 1 (by rfl) ⟨2199383, by rfl⟩ : syracuseStep 2932511 = 4398767) B4398767
theorem B1955007 : Blo 1953435 1955007 := bstep (se 1 (by rfl) ⟨1466255, by rfl⟩ : syracuseStep 1955007 = 2932511) B2932511
theorem B2932517 : Blo 1953435 2932517 := bbase (se 4 (by rfl) ⟨274923, by rfl⟩ : syracuseStep 2932517 = 549847) (by norm_num)
theorem B1955011 : Blo 1953435 1955011 := bstep (se 1 (by rfl) ⟨1466258, by rfl⟩ : syracuseStep 1955011 = 2932517) B2932517
theorem B2474317 : Blo 1953435 2474317 := bbase (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) (by norm_num)
theorem B3299089 : Blo 1953435 3299089 := bstep (se 2 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 3299089 = 2474317) B2474317
theorem B4398785 : Blo 1953435 4398785 := bstep (se 2 (by rfl) ⟨1649544, by rfl⟩ : syracuseStep 4398785 = 3299089) B3299089
theorem B2932523 : Blo 1953435 2932523 := bstep (se 1 (by rfl) ⟨2199392, by rfl⟩ : syracuseStep 2932523 = 4398785) B4398785
theorem B1955015 : Blo 1953435 1955015 := bstep (se 1 (by rfl) ⟨1466261, by rfl⟩ : syracuseStep 1955015 = 2932523) B2932523
theorem B2199397 : Blo 1953435 2199397 := bbase (se 4 (by rfl) ⟨206193, by rfl⟩ : syracuseStep 2199397 = 412387) (by norm_num)
theorem B2932529 : Blo 1953435 2932529 := bstep (se 2 (by rfl) ⟨1099698, by rfl⟩ : syracuseStep 2932529 = 2199397) B2199397
theorem B1955019 : Blo 1953435 1955019 := bstep (se 1 (by rfl) ⟨1466264, by rfl⟩ : syracuseStep 1955019 = 2932529) B2932529
theorem B5567237 : Blo 1953435 5567237 := bbase (se 4 (by rfl) ⟨521928, by rfl⟩ : syracuseStep 5567237 = 1043857) (by norm_num)
theorem B3711491 : Blo 1953435 3711491 := bstep (se 1 (by rfl) ⟨2783618, by rfl⟩ : syracuseStep 3711491 = 5567237) B5567237
theorem B2474327 : Blo 1953435 2474327 := bstep (se 1 (by rfl) ⟨1855745, by rfl⟩ : syracuseStep 2474327 = 3711491) B3711491
theorem B6598205 : Blo 1953435 6598205 := bstep (se 3 (by rfl) ⟨1237163, by rfl⟩ : syracuseStep 6598205 = 2474327) B2474327
theorem B4398803 : Blo 1953435 4398803 := bstep (se 1 (by rfl) ⟨3299102, by rfl⟩ : syracuseStep 4398803 = 6598205) B6598205
theorem B2932535 : Blo 1953435 2932535 := bstep (se 1 (by rfl) ⟨2199401, by rfl⟩ : syracuseStep 2932535 = 4398803) B4398803
theorem B1955023 : Blo 1953435 1955023 := bstep (se 1 (by rfl) ⟨1466267, by rfl⟩ : syracuseStep 1955023 = 2932535) B2932535
theorem B2932541 : Blo 1953435 2932541 := bbase (se 3 (by rfl) ⟨549851, by rfl⟩ : syracuseStep 2932541 = 1099703) (by norm_num)
theorem B1955027 : Blo 1953435 1955027 := bstep (se 1 (by rfl) ⟨1466270, by rfl⟩ : syracuseStep 1955027 = 2932541) B2932541
theorem B4398821 : Blo 1953435 4398821 := bbase (se 4 (by rfl) ⟨412389, by rfl⟩ : syracuseStep 4398821 = 824779) (by norm_num)
theorem B2932547 : Blo 1953435 2932547 := bstep (se 1 (by rfl) ⟨2199410, by rfl⟩ : syracuseStep 2932547 = 4398821) B4398821
theorem B1955031 : Blo 1953435 1955031 := bstep (se 1 (by rfl) ⟨1466273, by rfl⟩ : syracuseStep 1955031 = 2932547) B2932547
theorem B4948685 : Blo 1953435 4948685 := bbase (se 3 (by rfl) ⟨927878, by rfl⟩ : syracuseStep 4948685 = 1855757) (by norm_num)
theorem B3299123 : Blo 1953435 3299123 := bstep (se 1 (by rfl) ⟨2474342, by rfl⟩ : syracuseStep 3299123 = 4948685) B4948685
theorem B2199415 : Blo 1953435 2199415 := bstep (se 1 (by rfl) ⟨1649561, by rfl⟩ : syracuseStep 2199415 = 3299123) B3299123
theorem B2932553 : Blo 1953435 2932553 := bstep (se 2 (by rfl) ⟨1099707, by rfl⟩ : syracuseStep 2932553 = 2199415) B2199415
theorem B1955035 : Blo 1953435 1955035 := bstep (se 1 (by rfl) ⟨1466276, by rfl⟩ : syracuseStep 1955035 = 2932553) B2932553
theorem B3131597 : Blo 1953435 3131597 := bbase (se 3 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 3131597 = 1174349) (by norm_num)
theorem B2087731 : Blo 1953435 2087731 := bstep (se 1 (by rfl) ⟨1565798, by rfl⟩ : syracuseStep 2087731 = 3131597) B3131597
theorem B2783641 : Blo 1953435 2783641 := bstep (se 2 (by rfl) ⟨1043865, by rfl⟩ : syracuseStep 2783641 = 2087731) B2087731
theorem B3711521 : Blo 1953435 3711521 := bstep (se 2 (by rfl) ⟨1391820, by rfl⟩ : syracuseStep 3711521 = 2783641) B2783641
theorem B9897389 : Blo 1953435 9897389 := bstep (se 3 (by rfl) ⟨1855760, by rfl⟩ : syracuseStep 9897389 = 3711521) B3711521
theorem B6598259 : Blo 1953435 6598259 := bstep (se 1 (by rfl) ⟨4948694, by rfl⟩ : syracuseStep 6598259 = 9897389) B9897389
theorem B4398839 : Blo 1953435 4398839 := bstep (se 1 (by rfl) ⟨3299129, by rfl⟩ : syracuseStep 4398839 = 6598259) B6598259
theorem B2932559 : Blo 1953435 2932559 := bstep (se 1 (by rfl) ⟨2199419, by rfl⟩ : syracuseStep 2932559 = 4398839) B4398839
theorem B1955039 : Blo 1953435 1955039 := bstep (se 1 (by rfl) ⟨1466279, by rfl⟩ : syracuseStep 1955039 = 2932559) B2932559
theorem B2932565 : Blo 1953435 2932565 := bbase (se 9 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 2932565 = 17183) (by norm_num)
theorem B1955043 : Blo 1953435 1955043 := bstep (se 1 (by rfl) ⟨1466282, by rfl⟩ : syracuseStep 1955043 = 2932565) B2932565
theorem B3523061 : Blo 1953435 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B9394829 : Blo 1953435 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B6263219 : Blo 1953435 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B4175479 : Blo 1953435 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B5567305 : Blo 1953435 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B7423073 : Blo 1953435 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B4948715 : Blo 1953435 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B3299143 : Blo 1953435 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B4398857 : Blo 1953435 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B2932571 : Blo 1953435 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B1955047 : Blo 1953435 1955047 := bstep (se 1 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 1955047 = 2932571) B2932571
theorem B2199433 : Blo 1953435 2199433 := bbase (se 2 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 2199433 = 1649575) (by norm_num)
theorem B2932577 : Blo 1953435 2932577 := bstep (se 2 (by rfl) ⟨1099716, by rfl⟩ : syracuseStep 2932577 = 2199433) B2199433
theorem B1955051 : Blo 1953435 1955051 := bstep (se 1 (by rfl) ⟨1466288, by rfl⟩ : syracuseStep 1955051 = 2932577) B2932577
theorem B20065013 : Blo 1953435 20065013 := bbase (se 5 (by rfl) ⟨940547, by rfl⟩ : syracuseStep 20065013 = 1881095) (by norm_num)
theorem B13376675 : Blo 1953435 13376675 := bstep (se 1 (by rfl) ⟨10032506, by rfl⟩ : syracuseStep 13376675 = 20065013) B20065013
theorem B8917783 : Blo 1953435 8917783 := bstep (se 1 (by rfl) ⟨6688337, by rfl⟩ : syracuseStep 8917783 = 13376675) B13376675
theorem B47561509 : Blo 1953435 47561509 := bstep (se 4 (by rfl) ⟨4458891, by rfl⟩ : syracuseStep 47561509 = 8917783) B8917783
theorem B63415345 : Blo 1953435 63415345 := bstep (se 2 (by rfl) ⟨23780754, by rfl⟩ : syracuseStep 63415345 = 47561509) B47561509
theorem B84553793 : Blo 1953435 84553793 := bstep (se 2 (by rfl) ⟨31707672, by rfl⟩ : syracuseStep 84553793 = 63415345) B63415345
theorem B56369195 : Blo 1953435 56369195 := bstep (se 1 (by rfl) ⟨42276896, by rfl⟩ : syracuseStep 56369195 = 84553793) B84553793
theorem B37579463 : Blo 1953435 37579463 := bstep (se 1 (by rfl) ⟨28184597, by rfl⟩ : syracuseStep 37579463 = 56369195) B56369195
theorem B25052975 : Blo 1953435 25052975 := bstep (se 1 (by rfl) ⟨18789731, by rfl⟩ : syracuseStep 25052975 = 37579463) B37579463
theorem B16701983 : Blo 1953435 16701983 := bstep (se 1 (by rfl) ⟨12526487, by rfl⟩ : syracuseStep 16701983 = 25052975) B25052975
theorem B11134655 : Blo 1953435 11134655 := bstep (se 1 (by rfl) ⟨8350991, by rfl⟩ : syracuseStep 11134655 = 16701983) B16701983
theorem B7423103 : Blo 1953435 7423103 := bstep (se 1 (by rfl) ⟨5567327, by rfl⟩ : syracuseStep 7423103 = 11134655) B11134655
theorem B4948735 : Blo 1953435 4948735 := bstep (se 1 (by rfl) ⟨3711551, by rfl⟩ : syracuseStep 4948735 = 7423103) B7423103
theorem B6598313 : Blo 1953435 6598313 := bstep (se 2 (by rfl) ⟨2474367, by rfl⟩ : syracuseStep 6598313 = 4948735) B4948735
theorem B4398875 : Blo 1953435 4398875 := bstep (se 1 (by rfl) ⟨3299156, by rfl⟩ : syracuseStep 4398875 = 6598313) B6598313
theorem B2932583 : Blo 1953435 2932583 := bstep (se 1 (by rfl) ⟨2199437, by rfl⟩ : syracuseStep 2932583 = 4398875) B4398875
theorem B1955055 : Blo 1953435 1955055 := bstep (se 1 (by rfl) ⟨1466291, by rfl⟩ : syracuseStep 1955055 = 2932583) B2932583
theorem B2932589 : Blo 1953435 2932589 := bbase (se 3 (by rfl) ⟨549860, by rfl⟩ : syracuseStep 2932589 = 1099721) (by norm_num)
theorem B1955059 : Blo 1953435 1955059 := bstep (se 1 (by rfl) ⟨1466294, by rfl⟩ : syracuseStep 1955059 = 2932589) B2932589
theorem B4398893 : Blo 1953435 4398893 := bbase (se 3 (by rfl) ⟨824792, by rfl⟩ : syracuseStep 4398893 = 1649585) (by norm_num)
theorem B2932595 : Blo 1953435 2932595 := bstep (se 1 (by rfl) ⟨2199446, by rfl⟩ : syracuseStep 2932595 = 4398893) B4398893
theorem B1955063 : Blo 1953435 1955063 := bstep (se 1 (by rfl) ⟨1466297, by rfl⟩ : syracuseStep 1955063 = 2932595) B2932595
theorem B8351045 : Blo 1953435 8351045 := bbase (se 4 (by rfl) ⟨782910, by rfl⟩ : syracuseStep 8351045 = 1565821) (by norm_num)
theorem B5567363 : Blo 1953435 5567363 := bstep (se 1 (by rfl) ⟨4175522, by rfl⟩ : syracuseStep 5567363 = 8351045) B8351045
theorem B3711575 : Blo 1953435 3711575 := bstep (se 1 (by rfl) ⟨2783681, by rfl⟩ : syracuseStep 3711575 = 5567363) B5567363
theorem B2474383 : Blo 1953435 2474383 := bstep (se 1 (by rfl) ⟨1855787, by rfl⟩ : syracuseStep 2474383 = 3711575) B3711575
theorem B3299177 : Blo 1953435 3299177 := bstep (se 2 (by rfl) ⟨1237191, by rfl⟩ : syracuseStep 3299177 = 2474383) B2474383
theorem B2199451 : Blo 1953435 2199451 := bstep (se 1 (by rfl) ⟨1649588, by rfl⟩ : syracuseStep 2199451 = 3299177) B3299177
theorem B2932601 : Blo 1953435 2932601 := bstep (se 2 (by rfl) ⟨1099725, by rfl⟩ : syracuseStep 2932601 = 2199451) B2199451
theorem B1955067 : Blo 1953435 1955067 := bstep (se 1 (by rfl) ⟨1466300, by rfl⟩ : syracuseStep 1955067 = 2932601) B2932601
theorem B3762221 : Blo 1953435 3762221 := bbase (se 3 (by rfl) ⟨705416, by rfl⟩ : syracuseStep 3762221 = 1410833) (by norm_num)
theorem B10032589 : Blo 1953435 10032589 := bstep (se 3 (by rfl) ⟨1881110, by rfl⟩ : syracuseStep 10032589 = 3762221) B3762221
theorem B53507141 : Blo 1953435 53507141 := bstep (se 4 (by rfl) ⟨5016294, by rfl⟩ : syracuseStep 53507141 = 10032589) B10032589
theorem B35671427 : Blo 1953435 35671427 := bstep (se 1 (by rfl) ⟨26753570, by rfl⟩ : syracuseStep 35671427 = 53507141) B53507141
theorem B23780951 : Blo 1953435 23780951 := bstep (se 1 (by rfl) ⟨17835713, by rfl⟩ : syracuseStep 23780951 = 35671427) B35671427
theorem B15853967 : Blo 1953435 15853967 := bstep (se 1 (by rfl) ⟨11890475, by rfl⟩ : syracuseStep 15853967 = 23780951) B23780951
theorem B10569311 : Blo 1953435 10569311 := bstep (se 1 (by rfl) ⟨7926983, by rfl⟩ : syracuseStep 10569311 = 15853967) B15853967
theorem B7046207 : Blo 1953435 7046207 := bstep (se 1 (by rfl) ⟨5284655, by rfl⟩ : syracuseStep 7046207 = 10569311) B10569311
theorem B4697471 : Blo 1953435 4697471 := bstep (se 1 (by rfl) ⟨3523103, by rfl⟩ : syracuseStep 4697471 = 7046207) B7046207
theorem B12526589 : Blo 1953435 12526589 := bstep (se 3 (by rfl) ⟨2348735, by rfl⟩ : syracuseStep 12526589 = 4697471) B4697471
theorem B33404237 : Blo 1953435 33404237 := bstep (se 3 (by rfl) ⟨6263294, by rfl⟩ : syracuseStep 33404237 = 12526589) B12526589
theorem B22269491 : Blo 1953435 22269491 := bstep (se 1 (by rfl) ⟨16702118, by rfl⟩ : syracuseStep 22269491 = 33404237) B33404237
theorem B14846327 : Blo 1953435 14846327 := bstep (se 1 (by rfl) ⟨11134745, by rfl⟩ : syracuseStep 14846327 = 22269491) B22269491
theorem B9897551 : Blo 1953435 9897551 := bstep (se 1 (by rfl) ⟨7423163, by rfl⟩ : syracuseStep 9897551 = 14846327) B14846327
theorem B6598367 : Blo 1953435 6598367 := bstep (se 1 (by rfl) ⟨4948775, by rfl⟩ : syracuseStep 6598367 = 9897551) B9897551
theorem B4398911 : Blo 1953435 4398911 := bstep (se 1 (by rfl) ⟨3299183, by rfl⟩ : syracuseStep 4398911 = 6598367) B6598367
theorem B2932607 : Blo 1953435 2932607 := bstep (se 1 (by rfl) ⟨2199455, by rfl⟩ : syracuseStep 2932607 = 4398911) B4398911
theorem B1955071 : Blo 1953435 1955071 := bstep (se 1 (by rfl) ⟨1466303, by rfl⟩ : syracuseStep 1955071 = 2932607) B2932607
theorem B2932613 : Blo 1953435 2932613 := bbase (se 4 (by rfl) ⟨274932, by rfl⟩ : syracuseStep 2932613 = 549865) (by norm_num)
theorem B1955075 : Blo 1953435 1955075 := bstep (se 1 (by rfl) ⟨1466306, by rfl⟩ : syracuseStep 1955075 = 2932613) B2932613
theorem B3299197 : Blo 1953435 3299197 := bbase (se 3 (by rfl) ⟨618599, by rfl⟩ : syracuseStep 3299197 = 1237199) (by norm_num)
theorem B4398929 : Blo 1953435 4398929 := bstep (se 2 (by rfl) ⟨1649598, by rfl⟩ : syracuseStep 4398929 = 3299197) B3299197
theorem B2932619 : Blo 1953435 2932619 := bstep (se 1 (by rfl) ⟨2199464, by rfl⟩ : syracuseStep 2932619 = 4398929) B4398929
theorem B1955079 : Blo 1953435 1955079 := bstep (se 1 (by rfl) ⟨1466309, by rfl⟩ : syracuseStep 1955079 = 2932619) B2932619
theorem B2199469 : Blo 1953435 2199469 := bbase (se 3 (by rfl) ⟨412400, by rfl⟩ : syracuseStep 2199469 = 824801) (by norm_num)
theorem B2932625 : Blo 1953435 2932625 := bstep (se 2 (by rfl) ⟨1099734, by rfl⟩ : syracuseStep 2932625 = 2199469) B2199469
theorem B1955083 : Blo 1953435 1955083 := bstep (se 1 (by rfl) ⟨1466312, by rfl⟩ : syracuseStep 1955083 = 2932625) B2932625
theorem B6598421 : Blo 1953435 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B4398947 : Blo 1953435 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B2932631 : Blo 1953435 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B1955087 : Blo 1953435 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B2932637 : Blo 1953435 2932637 := bbase (se 3 (by rfl) ⟨549869, by rfl⟩ : syracuseStep 2932637 = 1099739) (by norm_num)
theorem B1955091 : Blo 1953435 1955091 := bstep (se 1 (by rfl) ⟨1466318, by rfl⟩ : syracuseStep 1955091 = 2932637) B2932637
theorem B4398965 : Blo 1953435 4398965 := bbase (se 5 (by rfl) ⟨206201, by rfl⟩ : syracuseStep 4398965 = 412403) (by norm_num)
theorem B2932643 : Blo 1953435 2932643 := bstep (se 1 (by rfl) ⟨2199482, by rfl⟩ : syracuseStep 2932643 = 4398965) B4398965
theorem B1955095 : Blo 1953435 1955095 := bstep (se 1 (by rfl) ⟨1466321, by rfl⟩ : syracuseStep 1955095 = 2932643) B2932643
theorem B7046309 : Blo 1953435 7046309 := bbase (se 4 (by rfl) ⟨660591, by rfl⟩ : syracuseStep 7046309 = 1321183) (by norm_num)
theorem B18790157 : Blo 1953435 18790157 := bstep (se 3 (by rfl) ⟨3523154, by rfl⟩ : syracuseStep 18790157 = 7046309) B7046309
theorem B12526771 : Blo 1953435 12526771 := bstep (se 1 (by rfl) ⟨9395078, by rfl⟩ : syracuseStep 12526771 = 18790157) B18790157
theorem B16702361 : Blo 1953435 16702361 := bstep (se 2 (by rfl) ⟨6263385, by rfl⟩ : syracuseStep 16702361 = 12526771) B12526771
theorem B11134907 : Blo 1953435 11134907 := bstep (se 1 (by rfl) ⟨8351180, by rfl⟩ : syracuseStep 11134907 = 16702361) B16702361
theorem B7423271 : Blo 1953435 7423271 := bstep (se 1 (by rfl) ⟨5567453, by rfl⟩ : syracuseStep 7423271 = 11134907) B11134907
theorem B4948847 : Blo 1953435 4948847 := bstep (se 1 (by rfl) ⟨3711635, by rfl⟩ : syracuseStep 4948847 = 7423271) B7423271
theorem B3299231 : Blo 1953435 3299231 := bstep (se 1 (by rfl) ⟨2474423, by rfl⟩ : syracuseStep 3299231 = 4948847) B4948847
theorem B2199487 : Blo 1953435 2199487 := bstep (se 1 (by rfl) ⟨1649615, by rfl⟩ : syracuseStep 2199487 = 3299231) B3299231
theorem B2932649 : Blo 1953435 2932649 := bstep (se 2 (by rfl) ⟨1099743, by rfl⟩ : syracuseStep 2932649 = 2199487) B2199487
theorem B1955099 : Blo 1953435 1955099 := bstep (se 1 (by rfl) ⟨1466324, by rfl⟩ : syracuseStep 1955099 = 2932649) B2932649
theorem B7423285 : Blo 1953435 7423285 := bbase (se 5 (by rfl) ⟨347966, by rfl⟩ : syracuseStep 7423285 = 695933) (by norm_num)
theorem B9897713 : Blo 1953435 9897713 := bstep (se 2 (by rfl) ⟨3711642, by rfl⟩ : syracuseStep 9897713 = 7423285) B7423285
theorem B6598475 : Blo 1953435 6598475 := bstep (se 1 (by rfl) ⟨4948856, by rfl⟩ : syracuseStep 6598475 = 9897713) B9897713
theorem B4398983 : Blo 1953435 4398983 := bstep (se 1 (by rfl) ⟨3299237, by rfl⟩ : syracuseStep 4398983 = 6598475) B6598475
theorem B2932655 : Blo 1953435 2932655 := bstep (se 1 (by rfl) ⟨2199491, by rfl⟩ : syracuseStep 2932655 = 4398983) B4398983
theorem B1955103 : Blo 1953435 1955103 := bstep (se 1 (by rfl) ⟨1466327, by rfl⟩ : syracuseStep 1955103 = 2932655) B2932655
theorem B2932661 : Blo 1953435 2932661 := bbase (se 5 (by rfl) ⟨137468, by rfl⟩ : syracuseStep 2932661 = 274937) (by norm_num)
theorem B1955107 : Blo 1953435 1955107 := bstep (se 1 (by rfl) ⟨1466330, by rfl⟩ : syracuseStep 1955107 = 2932661) B2932661
theorem B4948877 : Blo 1953435 4948877 := bbase (se 3 (by rfl) ⟨927914, by rfl⟩ : syracuseStep 4948877 = 1855829) (by norm_num)
theorem B3299251 : Blo 1953435 3299251 := bstep (se 1 (by rfl) ⟨2474438, by rfl⟩ : syracuseStep 3299251 = 4948877) B4948877
theorem B4399001 : Blo 1953435 4399001 := bstep (se 2 (by rfl) ⟨1649625, by rfl⟩ : syracuseStep 4399001 = 3299251) B3299251
theorem B2932667 : Blo 1953435 2932667 := bstep (se 1 (by rfl) ⟨2199500, by rfl⟩ : syracuseStep 2932667 = 4399001) B4399001
theorem B1955111 : Blo 1953435 1955111 := bstep (se 1 (by rfl) ⟨1466333, by rfl⟩ : syracuseStep 1955111 = 2932667) B2932667
theorem B2199505 : Blo 1953435 2199505 := bbase (se 2 (by rfl) ⟨824814, by rfl⟩ : syracuseStep 2199505 = 1649629) (by norm_num)
theorem B2932673 : Blo 1953435 2932673 := bstep (se 2 (by rfl) ⟨1099752, by rfl⟩ : syracuseStep 2932673 = 2199505) B2199505
theorem B1955115 : Blo 1953435 1955115 := bstep (se 1 (by rfl) ⟨1466336, by rfl⟩ : syracuseStep 1955115 = 2932673) B2932673
theorem B3131725 : Blo 1953435 3131725 := bbase (se 3 (by rfl) ⟨587198, by rfl⟩ : syracuseStep 3131725 = 1174397) (by norm_num)
theorem B4175633 : Blo 1953435 4175633 := bstep (se 2 (by rfl) ⟨1565862, by rfl⟩ : syracuseStep 4175633 = 3131725) B3131725
theorem B2783755 : Blo 1953435 2783755 := bstep (se 1 (by rfl) ⟨2087816, by rfl⟩ : syracuseStep 2783755 = 4175633) B4175633
theorem B3711673 : Blo 1953435 3711673 := bstep (se 2 (by rfl) ⟨1391877, by rfl⟩ : syracuseStep 3711673 = 2783755) B2783755
theorem B4948897 : Blo 1953435 4948897 := bstep (se 2 (by rfl) ⟨1855836, by rfl⟩ : syracuseStep 4948897 = 3711673) B3711673
theorem B6598529 : Blo 1953435 6598529 := bstep (se 2 (by rfl) ⟨2474448, by rfl⟩ : syracuseStep 6598529 = 4948897) B4948897
theorem B4399019 : Blo 1953435 4399019 := bstep (se 1 (by rfl) ⟨3299264, by rfl⟩ : syracuseStep 4399019 = 6598529) B6598529
theorem B2932679 : Blo 1953435 2932679 := bstep (se 1 (by rfl) ⟨2199509, by rfl⟩ : syracuseStep 2932679 = 4399019) B4399019
theorem B1955119 : Blo 1953435 1955119 := bstep (se 1 (by rfl) ⟨1466339, by rfl⟩ : syracuseStep 1955119 = 2932679) B2932679
theorem B2932685 : Blo 1953435 2932685 := bbase (se 3 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 2932685 = 1099757) (by norm_num)
theorem B1955123 : Blo 1953435 1955123 := bstep (se 1 (by rfl) ⟨1466342, by rfl⟩ : syracuseStep 1955123 = 2932685) B2932685
theorem B4399037 : Blo 1953435 4399037 := bbase (se 3 (by rfl) ⟨824819, by rfl⟩ : syracuseStep 4399037 = 1649639) (by norm_num)
theorem B2932691 : Blo 1953435 2932691 := bstep (se 1 (by rfl) ⟨2199518, by rfl⟩ : syracuseStep 2932691 = 4399037) B4399037
theorem B1955127 : Blo 1953435 1955127 := bstep (se 1 (by rfl) ⟨1466345, by rfl⟩ : syracuseStep 1955127 = 2932691) B2932691
theorem B3299285 : Blo 1953435 3299285 := bbase (se 7 (by rfl) ⟨38663, by rfl⟩ : syracuseStep 3299285 = 77327) (by norm_num)
theorem B2199523 : Blo 1953435 2199523 := bstep (se 1 (by rfl) ⟨1649642, by rfl⟩ : syracuseStep 2199523 = 3299285) B3299285
theorem B2932697 : Blo 1953435 2932697 := bstep (se 2 (by rfl) ⟨1099761, by rfl⟩ : syracuseStep 2932697 = 2199523) B2199523
theorem B1955131 : Blo 1953435 1955131 := bstep (se 1 (by rfl) ⟨1466348, by rfl⟩ : syracuseStep 1955131 = 2932697) B2932697
theorem B8351333 : Blo 1953435 8351333 := bbase (se 4 (by rfl) ⟨782937, by rfl⟩ : syracuseStep 8351333 = 1565875) (by norm_num)
theorem B5567555 : Blo 1953435 5567555 := bstep (se 1 (by rfl) ⟨4175666, by rfl⟩ : syracuseStep 5567555 = 8351333) B8351333
theorem B14846813 : Blo 1953435 14846813 := bstep (se 3 (by rfl) ⟨2783777, by rfl⟩ : syracuseStep 14846813 = 5567555) B5567555
theorem B9897875 : Blo 1953435 9897875 := bstep (se 1 (by rfl) ⟨7423406, by rfl⟩ : syracuseStep 9897875 = 14846813) B14846813
theorem B6598583 : Blo 1953435 6598583 := bstep (se 1 (by rfl) ⟨4948937, by rfl⟩ : syracuseStep 6598583 = 9897875) B9897875
theorem B4399055 : Blo 1953435 4399055 := bstep (se 1 (by rfl) ⟨3299291, by rfl⟩ : syracuseStep 4399055 = 6598583) B6598583
theorem B2932703 : Blo 1953435 2932703 := bstep (se 1 (by rfl) ⟨2199527, by rfl⟩ : syracuseStep 2932703 = 4399055) B4399055
theorem B1955135 : Blo 1953435 1955135 := bstep (se 1 (by rfl) ⟨1466351, by rfl⟩ : syracuseStep 1955135 = 2932703) B2932703
theorem B2932709 : Blo 1953435 2932709 := bbase (se 4 (by rfl) ⟨274941, by rfl⟩ : syracuseStep 2932709 = 549883) (by norm_num)
theorem B1955139 : Blo 1953435 1955139 := bstep (se 1 (by rfl) ⟨1466354, by rfl⟩ : syracuseStep 1955139 = 2932709) B2932709
theorem B5643541 : Blo 1953435 5643541 := bbase (se 6 (by rfl) ⟨132270, by rfl⟩ : syracuseStep 5643541 = 264541) (by norm_num)
theorem B7524721 : Blo 1953435 7524721 := bstep (se 2 (by rfl) ⟨2821770, by rfl⟩ : syracuseStep 7524721 = 5643541) B5643541
theorem B40131845 : Blo 1953435 40131845 := bstep (se 4 (by rfl) ⟨3762360, by rfl⟩ : syracuseStep 40131845 = 7524721) B7524721
theorem B26754563 : Blo 1953435 26754563 := bstep (se 1 (by rfl) ⟨20065922, by rfl⟩ : syracuseStep 26754563 = 40131845) B40131845
theorem B17836375 : Blo 1953435 17836375 := bstep (se 1 (by rfl) ⟨13377281, by rfl⟩ : syracuseStep 17836375 = 26754563) B26754563
theorem B23781833 : Blo 1953435 23781833 := bstep (se 2 (by rfl) ⟨8918187, by rfl⟩ : syracuseStep 23781833 = 17836375) B17836375
theorem B15854555 : Blo 1953435 15854555 := bstep (se 1 (by rfl) ⟨11890916, by rfl⟩ : syracuseStep 15854555 = 23781833) B23781833
theorem B10569703 : Blo 1953435 10569703 := bstep (se 1 (by rfl) ⟨7927277, by rfl⟩ : syracuseStep 10569703 = 15854555) B15854555
theorem B14092937 : Blo 1953435 14092937 := bstep (se 2 (by rfl) ⟨5284851, by rfl⟩ : syracuseStep 14092937 = 10569703) B10569703
theorem B9395291 : Blo 1953435 9395291 := bstep (se 1 (by rfl) ⟨7046468, by rfl⟩ : syracuseStep 9395291 = 14092937) B14092937
theorem B6263527 : Blo 1953435 6263527 := bstep (se 1 (by rfl) ⟨4697645, by rfl⟩ : syracuseStep 6263527 = 9395291) B9395291
theorem B8351369 : Blo 1953435 8351369 := bstep (se 2 (by rfl) ⟨3131763, by rfl⟩ : syracuseStep 8351369 = 6263527) B6263527
theorem B5567579 : Blo 1953435 5567579 := bstep (se 1 (by rfl) ⟨4175684, by rfl⟩ : syracuseStep 5567579 = 8351369) B8351369
theorem B3711719 : Blo 1953435 3711719 := bstep (se 1 (by rfl) ⟨2783789, by rfl⟩ : syracuseStep 3711719 = 5567579) B5567579
theorem B2474479 : Blo 1953435 2474479 := bstep (se 1 (by rfl) ⟨1855859, by rfl⟩ : syracuseStep 2474479 = 3711719) B3711719
theorem B3299305 : Blo 1953435 3299305 := bstep (se 2 (by rfl) ⟨1237239, by rfl⟩ : syracuseStep 3299305 = 2474479) B2474479
theorem B4399073 : Blo 1953435 4399073 := bstep (se 2 (by rfl) ⟨1649652, by rfl⟩ : syracuseStep 4399073 = 3299305) B3299305
theorem B2932715 : Blo 1953435 2932715 := bstep (se 1 (by rfl) ⟨2199536, by rfl⟩ : syracuseStep 2932715 = 4399073) B4399073
theorem B1955143 : Blo 1953435 1955143 := bstep (se 1 (by rfl) ⟨1466357, by rfl⟩ : syracuseStep 1955143 = 2932715) B2932715
theorem B2199541 : Blo 1953435 2199541 := bbase (se 5 (by rfl) ⟨103103, by rfl⟩ : syracuseStep 2199541 = 206207) (by norm_num)
theorem B2932721 : Blo 1953435 2932721 := bstep (se 2 (by rfl) ⟨1099770, by rfl⟩ : syracuseStep 2932721 = 2199541) B2199541
theorem B1955147 : Blo 1953435 1955147 := bstep (se 1 (by rfl) ⟨1466360, by rfl⟩ : syracuseStep 1955147 = 2932721) B2932721
theorem B2474489 : Blo 1953435 2474489 := bbase (se 2 (by rfl) ⟨927933, by rfl⟩ : syracuseStep 2474489 = 1855867) (by norm_num)
theorem B6598637 : Blo 1953435 6598637 := bstep (se 3 (by rfl) ⟨1237244, by rfl⟩ : syracuseStep 6598637 = 2474489) B2474489
theorem B4399091 : Blo 1953435 4399091 := bstep (se 1 (by rfl) ⟨3299318, by rfl⟩ : syracuseStep 4399091 = 6598637) B6598637
theorem B2932727 : Blo 1953435 2932727 := bstep (se 1 (by rfl) ⟨2199545, by rfl⟩ : syracuseStep 2932727 = 4399091) B4399091
theorem B1955151 : Blo 1953435 1955151 := bstep (se 1 (by rfl) ⟨1466363, by rfl⟩ : syracuseStep 1955151 = 2932727) B2932727
theorem B2932733 : Blo 1953435 2932733 := bbase (se 3 (by rfl) ⟨549887, by rfl⟩ : syracuseStep 2932733 = 1099775) (by norm_num)
theorem B1955155 : Blo 1953435 1955155 := bstep (se 1 (by rfl) ⟨1466366, by rfl⟩ : syracuseStep 1955155 = 2932733) B2932733
theorem B4399109 : Blo 1953435 4399109 := bbase (se 4 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 4399109 = 824833) (by norm_num)
theorem B2932739 : Blo 1953435 2932739 := bstep (se 1 (by rfl) ⟨2199554, by rfl⟩ : syracuseStep 2932739 = 4399109) B4399109
theorem B1955159 : Blo 1953435 1955159 := bstep (se 1 (by rfl) ⟨1466369, by rfl⟩ : syracuseStep 1955159 = 2932739) B2932739
theorem B3711757 : Blo 1953435 3711757 := bbase (se 3 (by rfl) ⟨695954, by rfl⟩ : syracuseStep 3711757 = 1391909) (by norm_num)
theorem B4949009 : Blo 1953435 4949009 := bstep (se 2 (by rfl) ⟨1855878, by rfl⟩ : syracuseStep 4949009 = 3711757) B3711757
theorem B3299339 : Blo 1953435 3299339 := bstep (se 1 (by rfl) ⟨2474504, by rfl⟩ : syracuseStep 3299339 = 4949009) B4949009
theorem B2199559 : Blo 1953435 2199559 := bstep (se 1 (by rfl) ⟨1649669, by rfl⟩ : syracuseStep 2199559 = 3299339) B3299339
theorem B2932745 : Blo 1953435 2932745 := bstep (se 2 (by rfl) ⟨1099779, by rfl⟩ : syracuseStep 2932745 = 2199559) B2199559
theorem B1955163 : Blo 1953435 1955163 := bstep (se 1 (by rfl) ⟨1466372, by rfl⟩ : syracuseStep 1955163 = 2932745) B2932745
theorem B9898037 : Blo 1953435 9898037 := bbase (se 5 (by rfl) ⟨463970, by rfl⟩ : syracuseStep 9898037 = 927941) (by norm_num)
theorem B6598691 : Blo 1953435 6598691 := bstep (se 1 (by rfl) ⟨4949018, by rfl⟩ : syracuseStep 6598691 = 9898037) B9898037
theorem B4399127 : Blo 1953435 4399127 := bstep (se 1 (by rfl) ⟨3299345, by rfl⟩ : syracuseStep 4399127 = 6598691) B6598691
theorem B2932751 : Blo 1953435 2932751 := bstep (se 1 (by rfl) ⟨2199563, by rfl⟩ : syracuseStep 2932751 = 4399127) B4399127
theorem B1955167 : Blo 1953435 1955167 := bstep (se 1 (by rfl) ⟨1466375, by rfl⟩ : syracuseStep 1955167 = 2932751) B2932751
theorem B2932757 : Blo 1953435 2932757 := bbase (se 6 (by rfl) ⟨68736, by rfl⟩ : syracuseStep 2932757 = 137473) (by norm_num)
theorem B1955171 : Blo 1953435 1955171 := bstep (se 1 (by rfl) ⟨1466378, by rfl⟩ : syracuseStep 1955171 = 2932757) B2932757
theorem B2380909 : Blo 1953435 2380909 := bbase (se 3 (by rfl) ⟨446420, by rfl⟩ : syracuseStep 2380909 = 892841) (by norm_num)
theorem B3174545 : Blo 1953435 3174545 := bstep (se 2 (by rfl) ⟨1190454, by rfl⟩ : syracuseStep 3174545 = 2380909) B2380909
theorem B2116363 : Blo 1953435 2116363 := bstep (se 1 (by rfl) ⟨1587272, by rfl⟩ : syracuseStep 2116363 = 3174545) B3174545
theorem B2821817 : Blo 1953435 2821817 := bstep (se 2 (by rfl) ⟨1058181, by rfl⟩ : syracuseStep 2821817 = 2116363) B2116363
theorem B7524845 : Blo 1953435 7524845 := bstep (se 3 (by rfl) ⟨1410908, by rfl⟩ : syracuseStep 7524845 = 2821817) B2821817
theorem B5016563 : Blo 1953435 5016563 := bstep (se 1 (by rfl) ⟨3762422, by rfl⟩ : syracuseStep 5016563 = 7524845) B7524845
theorem B3344375 : Blo 1953435 3344375 := bstep (se 1 (by rfl) ⟨2508281, by rfl⟩ : syracuseStep 3344375 = 5016563) B5016563
theorem B8918333 : Blo 1953435 8918333 := bstep (se 3 (by rfl) ⟨1672187, by rfl⟩ : syracuseStep 8918333 = 3344375) B3344375
theorem B5945555 : Blo 1953435 5945555 := bstep (se 1 (by rfl) ⟨4459166, by rfl⟩ : syracuseStep 5945555 = 8918333) B8918333
theorem B3963703 : Blo 1953435 3963703 := bstep (se 1 (by rfl) ⟨2972777, by rfl⟩ : syracuseStep 3963703 = 5945555) B5945555
theorem B5284937 : Blo 1953435 5284937 := bstep (se 2 (by rfl) ⟨1981851, by rfl⟩ : syracuseStep 5284937 = 3963703) B3963703
theorem B14093165 : Blo 1953435 14093165 := bstep (se 3 (by rfl) ⟨2642468, by rfl⟩ : syracuseStep 14093165 = 5284937) B5284937
theorem B9395443 : Blo 1953435 9395443 := bstep (se 1 (by rfl) ⟨7046582, by rfl⟩ : syracuseStep 9395443 = 14093165) B14093165
theorem B12527257 : Blo 1953435 12527257 := bstep (se 2 (by rfl) ⟨4697721, by rfl⟩ : syracuseStep 12527257 = 9395443) B9395443
theorem B16703009 : Blo 1953435 16703009 := bstep (se 2 (by rfl) ⟨6263628, by rfl⟩ : syracuseStep 16703009 = 12527257) B12527257
theorem B11135339 : Blo 1953435 11135339 := bstep (se 1 (by rfl) ⟨8351504, by rfl⟩ : syracuseStep 11135339 = 16703009) B16703009
theorem B7423559 : Blo 1953435 7423559 := bstep (se 1 (by rfl) ⟨5567669, by rfl⟩ : syracuseStep 7423559 = 11135339) B11135339
theorem B4949039 : Blo 1953435 4949039 := bstep (se 1 (by rfl) ⟨3711779, by rfl⟩ : syracuseStep 4949039 = 7423559) B7423559
theorem B3299359 : Blo 1953435 3299359 := bstep (se 1 (by rfl) ⟨2474519, by rfl⟩ : syracuseStep 3299359 = 4949039) B4949039
theorem B4399145 : Blo 1953435 4399145 := bstep (se 2 (by rfl) ⟨1649679, by rfl⟩ : syracuseStep 4399145 = 3299359) B3299359
theorem B2932763 : Blo 1953435 2932763 := bstep (se 1 (by rfl) ⟨2199572, by rfl⟩ : syracuseStep 2932763 = 4399145) B4399145
theorem B1955175 : Blo 1953435 1955175 := bstep (se 1 (by rfl) ⟨1466381, by rfl⟩ : syracuseStep 1955175 = 2932763) B2932763
theorem B2199577 : Blo 1953435 2199577 := bbase (se 2 (by rfl) ⟨824841, by rfl⟩ : syracuseStep 2199577 = 1649683) (by norm_num)
theorem B2932769 : Blo 1953435 2932769 := bstep (se 2 (by rfl) ⟨1099788, by rfl⟩ : syracuseStep 2932769 = 2199577) B2199577
theorem B1955179 : Blo 1953435 1955179 := bstep (se 1 (by rfl) ⟨1466384, by rfl⟩ : syracuseStep 1955179 = 2932769) B2932769
theorem B7423589 : Blo 1953435 7423589 := bbase (se 4 (by rfl) ⟨695961, by rfl⟩ : syracuseStep 7423589 = 1391923) (by norm_num)
theorem B4949059 : Blo 1953435 4949059 := bstep (se 1 (by rfl) ⟨3711794, by rfl⟩ : syracuseStep 4949059 = 7423589) B7423589
theorem B6598745 : Blo 1953435 6598745 := bstep (se 2 (by rfl) ⟨2474529, by rfl⟩ : syracuseStep 6598745 = 4949059) B4949059
theorem B4399163 : Blo 1953435 4399163 := bstep (se 1 (by rfl) ⟨3299372, by rfl⟩ : syracuseStep 4399163 = 6598745) B6598745
theorem B2932775 : Blo 1953435 2932775 := bstep (se 1 (by rfl) ⟨2199581, by rfl⟩ : syracuseStep 2932775 = 4399163) B4399163
theorem B1955183 : Blo 1953435 1955183 := bstep (se 1 (by rfl) ⟨1466387, by rfl⟩ : syracuseStep 1955183 = 2932775) B2932775
theorem B2932781 : Blo 1953435 2932781 := bbase (se 3 (by rfl) ⟨549896, by rfl⟩ : syracuseStep 2932781 = 1099793) (by norm_num)
theorem B1955187 : Blo 1953435 1955187 := bstep (se 1 (by rfl) ⟨1466390, by rfl⟩ : syracuseStep 1955187 = 2932781) B2932781
theorem B4399181 : Blo 1953435 4399181 := bbase (se 3 (by rfl) ⟨824846, by rfl⟩ : syracuseStep 4399181 = 1649693) (by norm_num)
theorem B2932787 : Blo 1953435 2932787 := bstep (se 1 (by rfl) ⟨2199590, by rfl⟩ : syracuseStep 2932787 = 4399181) B4399181
theorem B1955191 : Blo 1953435 1955191 := bstep (se 1 (by rfl) ⟨1466393, by rfl⟩ : syracuseStep 1955191 = 2932787) B2932787
theorem B2474545 : Blo 1953435 2474545 := bbase (se 2 (by rfl) ⟨927954, by rfl⟩ : syracuseStep 2474545 = 1855909) (by norm_num)
theorem B3299393 : Blo 1953435 3299393 := bstep (se 2 (by rfl) ⟨1237272, by rfl⟩ : syracuseStep 3299393 = 2474545) B2474545
theorem B2199595 : Blo 1953435 2199595 := bstep (se 1 (by rfl) ⟨1649696, by rfl⟩ : syracuseStep 2199595 = 3299393) B3299393
theorem B2932793 : Blo 1953435 2932793 := bstep (se 2 (by rfl) ⟨1099797, by rfl⟩ : syracuseStep 2932793 = 2199595) B2199595
theorem B1955195 : Blo 1953435 1955195 := bstep (se 1 (by rfl) ⟨1466396, by rfl⟩ : syracuseStep 1955195 = 2932793) B2932793
theorem B2642501 : Blo 1953435 2642501 := bbase (se 4 (by rfl) ⟨247734, by rfl⟩ : syracuseStep 2642501 = 495469) (by norm_num)
theorem B7046669 : Blo 1953435 7046669 := bstep (se 3 (by rfl) ⟨1321250, by rfl⟩ : syracuseStep 7046669 = 2642501) B2642501
theorem B4697779 : Blo 1953435 4697779 := bstep (se 1 (by rfl) ⟨3523334, by rfl⟩ : syracuseStep 4697779 = 7046669) B7046669
theorem B6263705 : Blo 1953435 6263705 := bstep (se 2 (by rfl) ⟨2348889, by rfl⟩ : syracuseStep 6263705 = 4697779) B4697779
theorem B4175803 : Blo 1953435 4175803 := bstep (se 1 (by rfl) ⟨3131852, by rfl⟩ : syracuseStep 4175803 = 6263705) B6263705
theorem B22270949 : Blo 1953435 22270949 := bstep (se 4 (by rfl) ⟨2087901, by rfl⟩ : syracuseStep 22270949 = 4175803) B4175803
theorem B14847299 : Blo 1953435 14847299 := bstep (se 1 (by rfl) ⟨11135474, by rfl⟩ : syracuseStep 14847299 = 22270949) B22270949
theorem B9898199 : Blo 1953435 9898199 := bstep (se 1 (by rfl) ⟨7423649, by rfl⟩ : syracuseStep 9898199 = 14847299) B14847299
theorem B6598799 : Blo 1953435 6598799 := bstep (se 1 (by rfl) ⟨4949099, by rfl⟩ : syracuseStep 6598799 = 9898199) B9898199
theorem B4399199 : Blo 1953435 4399199 := bstep (se 1 (by rfl) ⟨3299399, by rfl⟩ : syracuseStep 4399199 = 6598799) B6598799
theorem B2932799 : Blo 1953435 2932799 := bstep (se 1 (by rfl) ⟨2199599, by rfl⟩ : syracuseStep 2932799 = 4399199) B4399199
theorem B1955199 : Blo 1953435 1955199 := bstep (se 1 (by rfl) ⟨1466399, by rfl⟩ : syracuseStep 1955199 = 2932799) B2932799
theorem B2932805 : Blo 1953435 2932805 := bbase (se 4 (by rfl) ⟨274950, by rfl⟩ : syracuseStep 2932805 = 549901) (by norm_num)
theorem B1955203 : Blo 1953435 1955203 := bstep (se 1 (by rfl) ⟨1466402, by rfl⟩ : syracuseStep 1955203 = 2932805) B2932805
theorem B3299413 : Blo 1953435 3299413 := bbase (se 8 (by rfl) ⟨19332, by rfl⟩ : syracuseStep 3299413 = 38665) (by norm_num)
theorem B4399217 : Blo 1953435 4399217 := bstep (se 2 (by rfl) ⟨1649706, by rfl⟩ : syracuseStep 4399217 = 3299413) B3299413
theorem B2932811 : Blo 1953435 2932811 := bstep (se 1 (by rfl) ⟨2199608, by rfl⟩ : syracuseStep 2932811 = 4399217) B4399217
theorem B1955207 : Blo 1953435 1955207 := bstep (se 1 (by rfl) ⟨1466405, by rfl⟩ : syracuseStep 1955207 = 2932811) B2932811
theorem B2199613 : Blo 1953435 2199613 := bbase (se 3 (by rfl) ⟨412427, by rfl⟩ : syracuseStep 2199613 = 824855) (by norm_num)
theorem B2932817 : Blo 1953435 2932817 := bstep (se 2 (by rfl) ⟨1099806, by rfl⟩ : syracuseStep 2932817 = 2199613) B2199613
theorem B1955211 : Blo 1953435 1955211 := bstep (se 1 (by rfl) ⟨1466408, by rfl⟩ : syracuseStep 1955211 = 2932817) B2932817
theorem B6598853 : Blo 1953435 6598853 := bbase (se 4 (by rfl) ⟨618642, by rfl⟩ : syracuseStep 6598853 = 1237285) (by norm_num)
theorem B4399235 : Blo 1953435 4399235 := bstep (se 1 (by rfl) ⟨3299426, by rfl⟩ : syracuseStep 4399235 = 6598853) B6598853
theorem B2932823 : Blo 1953435 2932823 := bstep (se 1 (by rfl) ⟨2199617, by rfl⟩ : syracuseStep 2932823 = 4399235) B4399235
theorem B1955215 : Blo 1953435 1955215 := bstep (se 1 (by rfl) ⟨1466411, by rfl⟩ : syracuseStep 1955215 = 2932823) B2932823
theorem B2932829 : Blo 1953435 2932829 := bbase (se 3 (by rfl) ⟨549905, by rfl⟩ : syracuseStep 2932829 = 1099811) (by norm_num)
theorem B1955219 : Blo 1953435 1955219 := bstep (se 1 (by rfl) ⟨1466414, by rfl⟩ : syracuseStep 1955219 = 2932829) B2932829
theorem B4399253 : Blo 1953435 4399253 := bbase (se 6 (by rfl) ⟨103107, by rfl⟩ : syracuseStep 4399253 = 206215) (by norm_num)
theorem B2932835 : Blo 1953435 2932835 := bstep (se 1 (by rfl) ⟨2199626, by rfl⟩ : syracuseStep 2932835 = 4399253) B4399253
theorem B1955223 : Blo 1953435 1955223 := bstep (se 1 (by rfl) ⟨1466417, by rfl⟩ : syracuseStep 1955223 = 2932835) B2932835
theorem B2783909 : Blo 1953435 2783909 := bbase (se 4 (by rfl) ⟨260991, by rfl⟩ : syracuseStep 2783909 = 521983) (by norm_num)
theorem B7423757 : Blo 1953435 7423757 := bstep (se 3 (by rfl) ⟨1391954, by rfl⟩ : syracuseStep 7423757 = 2783909) B2783909
theorem B4949171 : Blo 1953435 4949171 := bstep (se 1 (by rfl) ⟨3711878, by rfl⟩ : syracuseStep 4949171 = 7423757) B7423757
theorem B3299447 : Blo 1953435 3299447 := bstep (se 1 (by rfl) ⟨2474585, by rfl⟩ : syracuseStep 3299447 = 4949171) B4949171
theorem B2199631 : Blo 1953435 2199631 := bstep (se 1 (by rfl) ⟨1649723, by rfl⟩ : syracuseStep 2199631 = 3299447) B3299447
theorem B2932841 : Blo 1953435 2932841 := bstep (se 2 (by rfl) ⟨1099815, by rfl⟩ : syracuseStep 2932841 = 2199631) B2199631
theorem B1955227 : Blo 1953435 1955227 := bstep (se 1 (by rfl) ⟨1466420, by rfl⟩ : syracuseStep 1955227 = 2932841) B2932841
theorem B5085149 : Blo 1953435 5085149 := bbase (se 3 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 5085149 = 1906931) (by norm_num)
theorem B54241589 : Blo 1953435 54241589 := bstep (se 5 (by rfl) ⟨2542574, by rfl⟩ : syracuseStep 54241589 = 5085149) B5085149
theorem B144644237 : Blo 1953435 144644237 := bstep (se 3 (by rfl) ⟨27120794, by rfl⟩ : syracuseStep 144644237 = 54241589) B54241589
theorem B96429491 : Blo 1953435 96429491 := bstep (se 1 (by rfl) ⟨72322118, by rfl⟩ : syracuseStep 96429491 = 144644237) B144644237
theorem B64286327 : Blo 1953435 64286327 := bstep (se 1 (by rfl) ⟨48214745, by rfl⟩ : syracuseStep 64286327 = 96429491) B96429491
theorem B42857551 : Blo 1953435 42857551 := bstep (se 1 (by rfl) ⟨32143163, by rfl⟩ : syracuseStep 42857551 = 64286327) B64286327
theorem B228573605 : Blo 1953435 228573605 := bstep (se 4 (by rfl) ⟨21428775, by rfl⟩ : syracuseStep 228573605 = 42857551) B42857551
theorem B152382403 : Blo 1953435 152382403 := bstep (se 1 (by rfl) ⟨114286802, by rfl⟩ : syracuseStep 152382403 = 228573605) B228573605
theorem B812706149 : Blo 1953435 812706149 := bstep (se 4 (by rfl) ⟨76191201, by rfl⟩ : syracuseStep 812706149 = 152382403) B152382403
theorem B541804099 : Blo 1953435 541804099 := bstep (se 1 (by rfl) ⟨406353074, by rfl⟩ : syracuseStep 541804099 = 812706149) B812706149
theorem B722405465 : Blo 1953435 722405465 := bstep (se 2 (by rfl) ⟨270902049, by rfl⟩ : syracuseStep 722405465 = 541804099) B541804099
theorem B481603643 : Blo 1953435 481603643 := bstep (se 1 (by rfl) ⟨361202732, by rfl⟩ : syracuseStep 481603643 = 722405465) B722405465
theorem B321069095 : Blo 1953435 321069095 := bstep (se 1 (by rfl) ⟨240801821, by rfl⟩ : syracuseStep 321069095 = 481603643) B481603643
theorem B214046063 : Blo 1953435 214046063 := bstep (se 1 (by rfl) ⟨160534547, by rfl⟩ : syracuseStep 214046063 = 321069095) B321069095
theorem B142697375 : Blo 1953435 142697375 := bstep (se 1 (by rfl) ⟨107023031, by rfl⟩ : syracuseStep 142697375 = 214046063) B214046063
theorem B95131583 : Blo 1953435 95131583 := bstep (se 1 (by rfl) ⟨71348687, by rfl⟩ : syracuseStep 95131583 = 142697375) B142697375
theorem B63421055 : Blo 1953435 63421055 := bstep (se 1 (by rfl) ⟨47565791, by rfl⟩ : syracuseStep 63421055 = 95131583) B95131583
theorem B42280703 : Blo 1953435 42280703 := bstep (se 1 (by rfl) ⟨31710527, by rfl⟩ : syracuseStep 42280703 = 63421055) B63421055
theorem B28187135 : Blo 1953435 28187135 := bstep (se 1 (by rfl) ⟨21140351, by rfl⟩ : syracuseStep 28187135 = 42280703) B42280703
theorem B18791423 : Blo 1953435 18791423 := bstep (se 1 (by rfl) ⟨14093567, by rfl⟩ : syracuseStep 18791423 = 28187135) B28187135
theorem B12527615 : Blo 1953435 12527615 := bstep (se 1 (by rfl) ⟨9395711, by rfl⟩ : syracuseStep 12527615 = 18791423) B18791423
theorem B8351743 : Blo 1953435 8351743 := bstep (se 1 (by rfl) ⟨6263807, by rfl⟩ : syracuseStep 8351743 = 12527615) B12527615
theorem B11135657 : Blo 1953435 11135657 := bstep (se 2 (by rfl) ⟨4175871, by rfl⟩ : syracuseStep 11135657 = 8351743) B8351743
theorem B7423771 : Blo 1953435 7423771 := bstep (se 1 (by rfl) ⟨5567828, by rfl⟩ : syracuseStep 7423771 = 11135657) B11135657
theorem B9898361 : Blo 1953435 9898361 := bstep (se 2 (by rfl) ⟨3711885, by rfl⟩ : syracuseStep 9898361 = 7423771) B7423771
theorem B6598907 : Blo 1953435 6598907 := bstep (se 1 (by rfl) ⟨4949180, by rfl⟩ : syracuseStep 6598907 = 9898361) B9898361
theorem B4399271 : Blo 1953435 4399271 := bstep (se 1 (by rfl) ⟨3299453, by rfl⟩ : syracuseStep 4399271 = 6598907) B6598907
theorem B2932847 : Blo 1953435 2932847 := bstep (se 1 (by rfl) ⟨2199635, by rfl⟩ : syracuseStep 2932847 = 4399271) B4399271
theorem B1955231 : Blo 1953435 1955231 := bstep (se 1 (by rfl) ⟨1466423, by rfl⟩ : syracuseStep 1955231 = 2932847) B2932847
theorem B2932853 : Blo 1953435 2932853 := bbase (se 5 (by rfl) ⟨137477, by rfl⟩ : syracuseStep 2932853 = 274955) (by norm_num)
theorem B1955235 : Blo 1953435 1955235 := bstep (se 1 (by rfl) ⟨1466426, by rfl⟩ : syracuseStep 1955235 = 2932853) B2932853
theorem B3711901 : Blo 1953435 3711901 := bbase (se 3 (by rfl) ⟨695981, by rfl⟩ : syracuseStep 3711901 = 1391963) (by norm_num)
theorem B4949201 : Blo 1953435 4949201 := bstep (se 2 (by rfl) ⟨1855950, by rfl⟩ : syracuseStep 4949201 = 3711901) B3711901
theorem B3299467 : Blo 1953435 3299467 := bstep (se 1 (by rfl) ⟨2474600, by rfl⟩ : syracuseStep 3299467 = 4949201) B4949201
theorem B4399289 : Blo 1953435 4399289 := bstep (se 2 (by rfl) ⟨1649733, by rfl⟩ : syracuseStep 4399289 = 3299467) B3299467
theorem B2932859 : Blo 1953435 2932859 := bstep (se 1 (by rfl) ⟨2199644, by rfl⟩ : syracuseStep 2932859 = 4399289) B4399289
theorem B1955239 : Blo 1953435 1955239 := bstep (se 1 (by rfl) ⟨1466429, by rfl⟩ : syracuseStep 1955239 = 2932859) B2932859
theorem B2199649 : Blo 1953435 2199649 := bbase (se 2 (by rfl) ⟨824868, by rfl⟩ : syracuseStep 2199649 = 1649737) (by norm_num)
theorem B2932865 : Blo 1953435 2932865 := bstep (se 2 (by rfl) ⟨1099824, by rfl⟩ : syracuseStep 2932865 = 2199649) B2199649
theorem B1955243 : Blo 1953435 1955243 := bstep (se 1 (by rfl) ⟨1466432, by rfl⟩ : syracuseStep 1955243 = 2932865) B2932865
theorem B4949221 : Blo 1953435 4949221 := bbase (se 4 (by rfl) ⟨463989, by rfl⟩ : syracuseStep 4949221 = 927979) (by norm_num)
theorem B6598961 : Blo 1953435 6598961 := bstep (se 2 (by rfl) ⟨2474610, by rfl⟩ : syracuseStep 6598961 = 4949221) B4949221
theorem B4399307 : Blo 1953435 4399307 := bstep (se 1 (by rfl) ⟨3299480, by rfl⟩ : syracuseStep 4399307 = 6598961) B6598961
theorem B2932871 : Blo 1953435 2932871 := bstep (se 1 (by rfl) ⟨2199653, by rfl⟩ : syracuseStep 2932871 = 4399307) B4399307
theorem B1955247 : Blo 1953435 1955247 := bstep (se 1 (by rfl) ⟨1466435, by rfl⟩ : syracuseStep 1955247 = 2932871) B2932871
theorem B2932877 : Blo 1953435 2932877 := bbase (se 3 (by rfl) ⟨549914, by rfl⟩ : syracuseStep 2932877 = 1099829) (by norm_num)
theorem B1955251 : Blo 1953435 1955251 := bstep (se 1 (by rfl) ⟨1466438, by rfl⟩ : syracuseStep 1955251 = 2932877) B2932877
theorem B4399325 : Blo 1953435 4399325 := bbase (se 3 (by rfl) ⟨824873, by rfl⟩ : syracuseStep 4399325 = 1649747) (by norm_num)
theorem B2932883 : Blo 1953435 2932883 := bstep (se 1 (by rfl) ⟨2199662, by rfl⟩ : syracuseStep 2932883 = 4399325) B4399325
theorem B1955255 : Blo 1953435 1955255 := bstep (se 1 (by rfl) ⟨1466441, by rfl⟩ : syracuseStep 1955255 = 2932883) B2932883
theorem B3299501 : Blo 1953435 3299501 := bbase (se 3 (by rfl) ⟨618656, by rfl⟩ : syracuseStep 3299501 = 1237313) (by norm_num)
theorem B2199667 : Blo 1953435 2199667 := bstep (se 1 (by rfl) ⟨1649750, by rfl⟩ : syracuseStep 2199667 = 3299501) B3299501
theorem B2932889 : Blo 1953435 2932889 := bstep (se 2 (by rfl) ⟨1099833, by rfl⟩ : syracuseStep 2932889 = 2199667) B2199667
theorem B1955259 : Blo 1953435 1955259 := bstep (se 1 (by rfl) ⟨1466444, by rfl⟩ : syracuseStep 1955259 = 2932889) B2932889
theorem B3390157 : Blo 1953435 3390157 := bbase (se 3 (by rfl) ⟨635654, by rfl⟩ : syracuseStep 3390157 = 1271309) (by norm_num)
theorem B4520209 : Blo 1953435 4520209 := bstep (se 2 (by rfl) ⟨1695078, by rfl⟩ : syracuseStep 4520209 = 3390157) B3390157
theorem B6026945 : Blo 1953435 6026945 := bstep (se 2 (by rfl) ⟨2260104, by rfl⟩ : syracuseStep 6026945 = 4520209) B4520209
theorem B16071853 : Blo 1953435 16071853 := bstep (se 3 (by rfl) ⟨3013472, by rfl⟩ : syracuseStep 16071853 = 6026945) B6026945
theorem B21429137 : Blo 1953435 21429137 := bstep (se 2 (by rfl) ⟨8035926, by rfl⟩ : syracuseStep 21429137 = 16071853) B16071853
theorem B57144365 : Blo 1953435 57144365 := bstep (se 3 (by rfl) ⟨10714568, by rfl⟩ : syracuseStep 57144365 = 21429137) B21429137
theorem B38096243 : Blo 1953435 38096243 := bstep (se 1 (by rfl) ⟨28572182, by rfl⟩ : syracuseStep 38096243 = 57144365) B57144365
theorem B25397495 : Blo 1953435 25397495 := bstep (se 1 (by rfl) ⟨19048121, by rfl⟩ : syracuseStep 25397495 = 38096243) B38096243
theorem B16931663 : Blo 1953435 16931663 := bstep (se 1 (by rfl) ⟨12698747, by rfl⟩ : syracuseStep 16931663 = 25397495) B25397495
theorem B11287775 : Blo 1953435 11287775 := bstep (se 1 (by rfl) ⟨8465831, by rfl⟩ : syracuseStep 11287775 = 16931663) B16931663
theorem B7525183 : Blo 1953435 7525183 := bstep (se 1 (by rfl) ⟨5643887, by rfl⟩ : syracuseStep 7525183 = 11287775) B11287775
theorem B10033577 : Blo 1953435 10033577 := bstep (se 2 (by rfl) ⟨3762591, by rfl⟩ : syracuseStep 10033577 = 7525183) B7525183
theorem B6689051 : Blo 1953435 6689051 := bstep (se 1 (by rfl) ⟨5016788, by rfl⟩ : syracuseStep 6689051 = 10033577) B10033577
theorem B4459367 : Blo 1953435 4459367 := bstep (se 1 (by rfl) ⟨3344525, by rfl⟩ : syracuseStep 4459367 = 6689051) B6689051
theorem B2972911 : Blo 1953435 2972911 := bstep (se 1 (by rfl) ⟨2229683, by rfl⟩ : syracuseStep 2972911 = 4459367) B4459367
theorem B3963881 : Blo 1953435 3963881 := bstep (se 2 (by rfl) ⟨1486455, by rfl⟩ : syracuseStep 3963881 = 2972911) B2972911
theorem B2642587 : Blo 1953435 2642587 := bstep (se 1 (by rfl) ⟨1981940, by rfl⟩ : syracuseStep 2642587 = 3963881) B3963881
theorem B56375189 : Blo 1953435 56375189 := bstep (se 6 (by rfl) ⟨1321293, by rfl⟩ : syracuseStep 56375189 = 2642587) B2642587
theorem B37583459 : Blo 1953435 37583459 := bstep (se 1 (by rfl) ⟨28187594, by rfl⟩ : syracuseStep 37583459 = 56375189) B56375189
theorem B25055639 : Blo 1953435 25055639 := bstep (se 1 (by rfl) ⟨18791729, by rfl⟩ : syracuseStep 25055639 = 37583459) B37583459
theorem B16703759 : Blo 1953435 16703759 := bstep (se 1 (by rfl) ⟨12527819, by rfl⟩ : syracuseStep 16703759 = 25055639) B25055639
theorem B11135839 : Blo 1953435 11135839 := bstep (se 1 (by rfl) ⟨8351879, by rfl⟩ : syracuseStep 11135839 = 16703759) B16703759
theorem B14847785 : Blo 1953435 14847785 := bstep (se 2 (by rfl) ⟨5567919, by rfl⟩ : syracuseStep 14847785 = 11135839) B11135839
theorem B9898523 : Blo 1953435 9898523 := bstep (se 1 (by rfl) ⟨7423892, by rfl⟩ : syracuseStep 9898523 = 14847785) B14847785
theorem B6599015 : Blo 1953435 6599015 := bstep (se 1 (by rfl) ⟨4949261, by rfl⟩ : syracuseStep 6599015 = 9898523) B9898523
theorem B4399343 : Blo 1953435 4399343 := bstep (se 1 (by rfl) ⟨3299507, by rfl⟩ : syracuseStep 4399343 = 6599015) B6599015
theorem B2932895 : Blo 1953435 2932895 := bstep (se 1 (by rfl) ⟨2199671, by rfl⟩ : syracuseStep 2932895 = 4399343) B4399343
theorem B1955263 : Blo 1953435 1955263 := bstep (se 1 (by rfl) ⟨1466447, by rfl⟩ : syracuseStep 1955263 = 2932895) B2932895
theorem B2932901 : Blo 1953435 2932901 := bbase (se 4 (by rfl) ⟨274959, by rfl⟩ : syracuseStep 2932901 = 549919) (by norm_num)
theorem B1955267 : Blo 1953435 1955267 := bstep (se 1 (by rfl) ⟨1466450, by rfl⟩ : syracuseStep 1955267 = 2932901) B2932901
theorem B2474641 : Blo 1953435 2474641 := bbase (se 2 (by rfl) ⟨927990, by rfl⟩ : syracuseStep 2474641 = 1855981) (by norm_num)
theorem B3299521 : Blo 1953435 3299521 := bstep (se 2 (by rfl) ⟨1237320, by rfl⟩ : syracuseStep 3299521 = 2474641) B2474641
theorem B4399361 : Blo 1953435 4399361 := bstep (se 2 (by rfl) ⟨1649760, by rfl⟩ : syracuseStep 4399361 = 3299521) B3299521
theorem B2932907 : Blo 1953435 2932907 := bstep (se 1 (by rfl) ⟨2199680, by rfl⟩ : syracuseStep 2932907 = 4399361) B4399361
theorem B1955271 : Blo 1953435 1955271 := bstep (se 1 (by rfl) ⟨1466453, by rfl⟩ : syracuseStep 1955271 = 2932907) B2932907
theorem B2199685 : Blo 1953435 2199685 := bbase (se 4 (by rfl) ⟨206220, by rfl⟩ : syracuseStep 2199685 = 412441) (by norm_num)
theorem B2932913 : Blo 1953435 2932913 := bstep (se 2 (by rfl) ⟨1099842, by rfl⟩ : syracuseStep 2932913 = 2199685) B2199685
theorem B1955275 : Blo 1953435 1955275 := bstep (se 1 (by rfl) ⟨1466456, by rfl⟩ : syracuseStep 1955275 = 2932913) B2932913
theorem B2860469 : Blo 1953435 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B30511669 : Blo 1953435 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B40682225 : Blo 1953435 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B27121483 : Blo 1953435 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B36161977 : Blo 1953435 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B48215969 : Blo 1953435 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B32143979 : Blo 1953435 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B21429319 : Blo 1953435 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B28572425 : Blo 1953435 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B19048283 : Blo 1953435 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B12698855 : Blo 1953435 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B8465903 : Blo 1953435 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B5643935 : Blo 1953435 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B3762623 : Blo 1953435 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B2508415 : Blo 1953435 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B13378213 : Blo 1953435 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B17837617 : Blo 1953435 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B23783489 : Blo 1953435 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B15855659 : Blo 1953435 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B10570439 : Blo 1953435 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B7046959 : Blo 1953435 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B9395945 : Blo 1953435 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B6263963 : Blo 1953435 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B4175975 : Blo 1953435 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B2783983 : Blo 1953435 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B3711977 : Blo 1953435 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B2474651 : Blo 1953435 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B6599069 : Blo 1953435 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B4399379 : Blo 1953435 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B2932919 : Blo 1953435 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B1955279 : Blo 1953435 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B2932925 : Blo 1953435 2932925 := bbase (se 3 (by rfl) ⟨549923, by rfl⟩ : syracuseStep 2932925 = 1099847) (by norm_num)
theorem B1955283 : Blo 1953435 1955283 := bstep (se 1 (by rfl) ⟨1466462, by rfl⟩ : syracuseStep 1955283 = 2932925) B2932925
theorem B4399397 : Blo 1953435 4399397 := bbase (se 4 (by rfl) ⟨412443, by rfl⟩ : syracuseStep 4399397 = 824887) (by norm_num)
theorem B2932931 : Blo 1953435 2932931 := bstep (se 1 (by rfl) ⟨2199698, by rfl⟩ : syracuseStep 2932931 = 4399397) B4399397
theorem B1955287 : Blo 1953435 1955287 := bstep (se 1 (by rfl) ⟨1466465, by rfl⟩ : syracuseStep 1955287 = 2932931) B2932931
theorem B4949333 : Blo 1953435 4949333 := bbase (se 12 (by rfl) ⟨1812, by rfl⟩ : syracuseStep 4949333 = 3625) (by norm_num)
theorem B3299555 : Blo 1953435 3299555 := bstep (se 1 (by rfl) ⟨2474666, by rfl⟩ : syracuseStep 3299555 = 4949333) B4949333
theorem B2199703 : Blo 1953435 2199703 := bstep (se 1 (by rfl) ⟨1649777, by rfl⟩ : syracuseStep 2199703 = 3299555) B3299555
theorem B2932937 : Blo 1953435 2932937 := bstep (se 2 (by rfl) ⟨1099851, by rfl⟩ : syracuseStep 2932937 = 2199703) B2199703
theorem B1955291 : Blo 1953435 1955291 := bstep (se 1 (by rfl) ⟨1466468, by rfl⟩ : syracuseStep 1955291 = 2932937) B2932937
theorem B2349005 : Blo 1953435 2349005 := bbase (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) (by norm_num)
theorem B6264013 : Blo 1953435 6264013 := bstep (se 3 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 6264013 = 2349005) B2349005
theorem B8352017 : Blo 1953435 8352017 := bstep (se 2 (by rfl) ⟨3132006, by rfl⟩ : syracuseStep 8352017 = 6264013) B6264013
theorem B5568011 : Blo 1953435 5568011 := bstep (se 1 (by rfl) ⟨4176008, by rfl⟩ : syracuseStep 5568011 = 8352017) B8352017
theorem B3712007 : Blo 1953435 3712007 := bstep (se 1 (by rfl) ⟨2784005, by rfl⟩ : syracuseStep 3712007 = 5568011) B5568011
theorem B9898685 : Blo 1953435 9898685 := bstep (se 3 (by rfl) ⟨1856003, by rfl⟩ : syracuseStep 9898685 = 3712007) B3712007
theorem B6599123 : Blo 1953435 6599123 := bstep (se 1 (by rfl) ⟨4949342, by rfl⟩ : syracuseStep 6599123 = 9898685) B9898685
theorem B4399415 : Blo 1953435 4399415 := bstep (se 1 (by rfl) ⟨3299561, by rfl⟩ : syracuseStep 4399415 = 6599123) B6599123
theorem B2932943 : Blo 1953435 2932943 := bstep (se 1 (by rfl) ⟨2199707, by rfl⟩ : syracuseStep 2932943 = 4399415) B4399415
theorem B1955295 : Blo 1953435 1955295 := bstep (se 1 (by rfl) ⟨1466471, by rfl⟩ : syracuseStep 1955295 = 2932943) B2932943
theorem B2932949 : Blo 1953435 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B1955299 : Blo 1953435 1955299 := bstep (se 1 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 1955299 = 2932949) B2932949
theorem B2088013 : Blo 1953435 2088013 := bbase (se 3 (by rfl) ⟨391502, by rfl⟩ : syracuseStep 2088013 = 783005) (by norm_num)
theorem B2784017 : Blo 1953435 2784017 := bstep (se 2 (by rfl) ⟨1044006, by rfl⟩ : syracuseStep 2784017 = 2088013) B2088013
theorem B7424045 : Blo 1953435 7424045 := bstep (se 3 (by rfl) ⟨1392008, by rfl⟩ : syracuseStep 7424045 = 2784017) B2784017
theorem B4949363 : Blo 1953435 4949363 := bstep (se 1 (by rfl) ⟨3712022, by rfl⟩ : syracuseStep 4949363 = 7424045) B7424045
theorem B3299575 : Blo 1953435 3299575 := bstep (se 1 (by rfl) ⟨2474681, by rfl⟩ : syracuseStep 3299575 = 4949363) B4949363
theorem B4399433 : Blo 1953435 4399433 := bstep (se 2 (by rfl) ⟨1649787, by rfl⟩ : syracuseStep 4399433 = 3299575) B3299575
theorem B2932955 : Blo 1953435 2932955 := bstep (se 1 (by rfl) ⟨2199716, by rfl⟩ : syracuseStep 2932955 = 4399433) B4399433
theorem B1955303 : Blo 1953435 1955303 := bstep (se 1 (by rfl) ⟨1466477, by rfl⟩ : syracuseStep 1955303 = 2932955) B2932955
theorem B2199721 : Blo 1953435 2199721 := bbase (se 2 (by rfl) ⟨824895, by rfl⟩ : syracuseStep 2199721 = 1649791) (by norm_num)
theorem B2932961 : Blo 1953435 2932961 := bstep (se 2 (by rfl) ⟨1099860, by rfl⟩ : syracuseStep 2932961 = 2199721) B2199721
theorem B1955307 : Blo 1953435 1955307 := bstep (se 1 (by rfl) ⟨1466480, by rfl⟩ : syracuseStep 1955307 = 2932961) B2932961
theorem B8352085 : Blo 1953435 8352085 := bbase (se 10 (by rfl) ⟨12234, by rfl⟩ : syracuseStep 8352085 = 24469) (by norm_num)
theorem B11136113 : Blo 1953435 11136113 := bstep (se 2 (by rfl) ⟨4176042, by rfl⟩ : syracuseStep 11136113 = 8352085) B8352085
theorem B7424075 : Blo 1953435 7424075 := bstep (se 1 (by rfl) ⟨5568056, by rfl⟩ : syracuseStep 7424075 = 11136113) B11136113
theorem B4949383 : Blo 1953435 4949383 := bstep (se 1 (by rfl) ⟨3712037, by rfl⟩ : syracuseStep 4949383 = 7424075) B7424075
theorem B6599177 : Blo 1953435 6599177 := bstep (se 2 (by rfl) ⟨2474691, by rfl⟩ : syracuseStep 6599177 = 4949383) B4949383
theorem B4399451 : Blo 1953435 4399451 := bstep (se 1 (by rfl) ⟨3299588, by rfl⟩ : syracuseStep 4399451 = 6599177) B6599177
theorem B2932967 : Blo 1953435 2932967 := bstep (se 1 (by rfl) ⟨2199725, by rfl⟩ : syracuseStep 2932967 = 4399451) B4399451
theorem B1955311 : Blo 1953435 1955311 := bstep (se 1 (by rfl) ⟨1466483, by rfl⟩ : syracuseStep 1955311 = 2932967) B2932967
theorem B2932973 : Blo 1953435 2932973 := bbase (se 3 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 2932973 = 1099865) (by norm_num)
theorem B1955315 : Blo 1953435 1955315 := bstep (se 1 (by rfl) ⟨1466486, by rfl⟩ : syracuseStep 1955315 = 2932973) B2932973
theorem B4399469 : Blo 1953435 4399469 := bbase (se 3 (by rfl) ⟨824900, by rfl⟩ : syracuseStep 4399469 = 1649801) (by norm_num)
theorem B2932979 : Blo 1953435 2932979 := bstep (se 1 (by rfl) ⟨2199734, by rfl⟩ : syracuseStep 2932979 = 4399469) B4399469
theorem B1955319 : Blo 1953435 1955319 := bstep (se 1 (by rfl) ⟨1466489, by rfl⟩ : syracuseStep 1955319 = 2932979) B2932979
theorem B3712061 : Blo 1953435 3712061 := bbase (se 3 (by rfl) ⟨696011, by rfl⟩ : syracuseStep 3712061 = 1392023) (by norm_num)
theorem B2474707 : Blo 1953435 2474707 := bstep (se 1 (by rfl) ⟨1856030, by rfl⟩ : syracuseStep 2474707 = 3712061) B3712061
theorem B3299609 : Blo 1953435 3299609 := bstep (se 2 (by rfl) ⟨1237353, by rfl⟩ : syracuseStep 3299609 = 2474707) B2474707
theorem B2199739 : Blo 1953435 2199739 := bstep (se 1 (by rfl) ⟨1649804, by rfl⟩ : syracuseStep 2199739 = 3299609) B3299609
theorem B2932985 : Blo 1953435 2932985 := bstep (se 2 (by rfl) ⟨1099869, by rfl⟩ : syracuseStep 2932985 = 2199739) B2199739
theorem B1955323 : Blo 1953435 1955323 := bstep (se 1 (by rfl) ⟨1466492, by rfl⟩ : syracuseStep 1955323 = 2932985) B2932985
theorem B3523565 : Blo 1953435 3523565 := bbase (se 3 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 3523565 = 1321337) (by norm_num)
theorem B2349043 : Blo 1953435 2349043 := bstep (se 1 (by rfl) ⟨1761782, by rfl⟩ : syracuseStep 2349043 = 3523565) B3523565
theorem B50112917 : Blo 1953435 50112917 := bstep (se 6 (by rfl) ⟨1174521, by rfl⟩ : syracuseStep 50112917 = 2349043) B2349043
theorem B33408611 : Blo 1953435 33408611 := bstep (se 1 (by rfl) ⟨25056458, by rfl⟩ : syracuseStep 33408611 = 50112917) B50112917
theorem B22272407 : Blo 1953435 22272407 := bstep (se 1 (by rfl) ⟨16704305, by rfl⟩ : syracuseStep 22272407 = 33408611) B33408611
theorem B14848271 : Blo 1953435 14848271 := bstep (se 1 (by rfl) ⟨11136203, by rfl⟩ : syracuseStep 14848271 = 22272407) B22272407
theorem B9898847 : Blo 1953435 9898847 := bstep (se 1 (by rfl) ⟨7424135, by rfl⟩ : syracuseStep 9898847 = 14848271) B14848271
theorem B6599231 : Blo 1953435 6599231 := bstep (se 1 (by rfl) ⟨4949423, by rfl⟩ : syracuseStep 6599231 = 9898847) B9898847
theorem B4399487 : Blo 1953435 4399487 := bstep (se 1 (by rfl) ⟨3299615, by rfl⟩ : syracuseStep 4399487 = 6599231) B6599231
theorem B2932991 : Blo 1953435 2932991 := bstep (se 1 (by rfl) ⟨2199743, by rfl⟩ : syracuseStep 2932991 = 4399487) B4399487
theorem B1955327 : Blo 1953435 1955327 := bstep (se 1 (by rfl) ⟨1466495, by rfl⟩ : syracuseStep 1955327 = 2932991) B2932991
theorem B2932997 : Blo 1953435 2932997 := bbase (se 4 (by rfl) ⟨274968, by rfl⟩ : syracuseStep 2932997 = 549937) (by norm_num)
theorem B1955331 : Blo 1953435 1955331 := bstep (se 1 (by rfl) ⟨1466498, by rfl⟩ : syracuseStep 1955331 = 2932997) B2932997
theorem B3299629 : Blo 1953435 3299629 := bbase (se 3 (by rfl) ⟨618680, by rfl⟩ : syracuseStep 3299629 = 1237361) (by norm_num)
theorem B4399505 : Blo 1953435 4399505 := bstep (se 2 (by rfl) ⟨1649814, by rfl⟩ : syracuseStep 4399505 = 3299629) B3299629
theorem B2933003 : Blo 1953435 2933003 := bstep (se 1 (by rfl) ⟨2199752, by rfl⟩ : syracuseStep 2933003 = 4399505) B4399505
theorem B1955335 : Blo 1953435 1955335 := bstep (se 1 (by rfl) ⟨1466501, by rfl⟩ : syracuseStep 1955335 = 2933003) B2933003
theorem B2199757 : Blo 1953435 2199757 := bbase (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) (by norm_num)
theorem B2933009 : Blo 1953435 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B1955339 : Blo 1953435 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B6599285 : Blo 1953435 6599285 := bbase (se 5 (by rfl) ⟨309341, by rfl⟩ : syracuseStep 6599285 = 618683) (by norm_num)
theorem B4399523 : Blo 1953435 4399523 := bstep (se 1 (by rfl) ⟨3299642, by rfl⟩ : syracuseStep 4399523 = 6599285) B6599285
theorem B2933015 : Blo 1953435 2933015 := bstep (se 1 (by rfl) ⟨2199761, by rfl⟩ : syracuseStep 2933015 = 4399523) B4399523
theorem B1955343 : Blo 1953435 1955343 := bstep (se 1 (by rfl) ⟨1466507, by rfl⟩ : syracuseStep 1955343 = 2933015) B2933015
theorem B2933021 : Blo 1953435 2933021 := bbase (se 3 (by rfl) ⟨549941, by rfl⟩ : syracuseStep 2933021 = 1099883) (by norm_num)
theorem B1955347 : Blo 1953435 1955347 := bstep (se 1 (by rfl) ⟨1466510, by rfl⟩ : syracuseStep 1955347 = 2933021) B2933021
theorem B4399541 : Blo 1953435 4399541 := bbase (se 5 (by rfl) ⟨206228, by rfl⟩ : syracuseStep 4399541 = 412457) (by norm_num)
theorem B2933027 : Blo 1953435 2933027 := bstep (se 1 (by rfl) ⟨2199770, by rfl⟩ : syracuseStep 2933027 = 4399541) B4399541
theorem B1955351 : Blo 1953435 1955351 := bstep (se 1 (by rfl) ⟨1466513, by rfl⟩ : syracuseStep 1955351 = 2933027) B2933027
theorem B3964069 : Blo 1953435 3964069 := bbase (se 4 (by rfl) ⟨371631, by rfl⟩ : syracuseStep 3964069 = 743263) (by norm_num)
theorem B5285425 : Blo 1953435 5285425 := bstep (se 2 (by rfl) ⟨1982034, by rfl⟩ : syracuseStep 5285425 = 3964069) B3964069
theorem B7047233 : Blo 1953435 7047233 := bstep (se 2 (by rfl) ⟨2642712, by rfl⟩ : syracuseStep 7047233 = 5285425) B5285425
theorem B4698155 : Blo 1953435 4698155 := bstep (se 1 (by rfl) ⟨3523616, by rfl⟩ : syracuseStep 4698155 = 7047233) B7047233
theorem B3132103 : Blo 1953435 3132103 := bstep (se 1 (by rfl) ⟨2349077, by rfl⟩ : syracuseStep 3132103 = 4698155) B4698155
theorem B4176137 : Blo 1953435 4176137 := bstep (se 2 (by rfl) ⟨1566051, by rfl⟩ : syracuseStep 4176137 = 3132103) B3132103
theorem B11136365 : Blo 1953435 11136365 := bstep (se 3 (by rfl) ⟨2088068, by rfl⟩ : syracuseStep 11136365 = 4176137) B4176137
theorem B7424243 : Blo 1953435 7424243 := bstep (se 1 (by rfl) ⟨5568182, by rfl⟩ : syracuseStep 7424243 = 11136365) B11136365
theorem B4949495 : Blo 1953435 4949495 := bstep (se 1 (by rfl) ⟨3712121, by rfl⟩ : syracuseStep 4949495 = 7424243) B7424243
theorem B3299663 : Blo 1953435 3299663 := bstep (se 1 (by rfl) ⟨2474747, by rfl⟩ : syracuseStep 3299663 = 4949495) B4949495
theorem B2199775 : Blo 1953435 2199775 := bstep (se 1 (by rfl) ⟨1649831, by rfl⟩ : syracuseStep 2199775 = 3299663) B3299663
theorem B2933033 : Blo 1953435 2933033 := bstep (se 2 (by rfl) ⟨1099887, by rfl⟩ : syracuseStep 2933033 = 2199775) B2199775
theorem B1955355 : Blo 1953435 1955355 := bstep (se 1 (by rfl) ⟨1466516, by rfl⟩ : syracuseStep 1955355 = 2933033) B2933033
theorem B3132109 : Blo 1953435 3132109 := bbase (se 3 (by rfl) ⟨587270, by rfl⟩ : syracuseStep 3132109 = 1174541) (by norm_num)
theorem B4176145 : Blo 1953435 4176145 := bstep (se 2 (by rfl) ⟨1566054, by rfl⟩ : syracuseStep 4176145 = 3132109) B3132109
theorem B5568193 : Blo 1953435 5568193 := bstep (se 2 (by rfl) ⟨2088072, by rfl⟩ : syracuseStep 5568193 = 4176145) B4176145
theorem B7424257 : Blo 1953435 7424257 := bstep (se 2 (by rfl) ⟨2784096, by rfl⟩ : syracuseStep 7424257 = 5568193) B5568193
theorem B9899009 : Blo 1953435 9899009 := bstep (se 2 (by rfl) ⟨3712128, by rfl⟩ : syracuseStep 9899009 = 7424257) B7424257
theorem B6599339 : Blo 1953435 6599339 := bstep (se 1 (by rfl) ⟨4949504, by rfl⟩ : syracuseStep 6599339 = 9899009) B9899009
theorem B4399559 : Blo 1953435 4399559 := bstep (se 1 (by rfl) ⟨3299669, by rfl⟩ : syracuseStep 4399559 = 6599339) B6599339
theorem B2933039 : Blo 1953435 2933039 := bstep (se 1 (by rfl) ⟨2199779, by rfl⟩ : syracuseStep 2933039 = 4399559) B4399559
theorem B1955359 : Blo 1953435 1955359 := bstep (se 1 (by rfl) ⟨1466519, by rfl⟩ : syracuseStep 1955359 = 2933039) B2933039
theorem B2933045 : Blo 1953435 2933045 := bbase (se 5 (by rfl) ⟨137486, by rfl⟩ : syracuseStep 2933045 = 274973) (by norm_num)
theorem B1955363 : Blo 1953435 1955363 := bstep (se 1 (by rfl) ⟨1466522, by rfl⟩ : syracuseStep 1955363 = 2933045) B2933045
theorem B4949525 : Blo 1953435 4949525 := bbase (se 6 (by rfl) ⟨116004, by rfl⟩ : syracuseStep 4949525 = 232009) (by norm_num)
theorem B3299683 : Blo 1953435 3299683 := bstep (se 1 (by rfl) ⟨2474762, by rfl⟩ : syracuseStep 3299683 = 4949525) B4949525
theorem B4399577 : Blo 1953435 4399577 := bstep (se 2 (by rfl) ⟨1649841, by rfl⟩ : syracuseStep 4399577 = 3299683) B3299683
theorem B2933051 : Blo 1953435 2933051 := bstep (se 1 (by rfl) ⟨2199788, by rfl⟩ : syracuseStep 2933051 = 4399577) B4399577
theorem B1955367 : Blo 1953435 1955367 := bstep (se 1 (by rfl) ⟨1466525, by rfl⟩ : syracuseStep 1955367 = 2933051) B2933051
theorem B2199793 : Blo 1953435 2199793 := bbase (se 2 (by rfl) ⟨824922, by rfl⟩ : syracuseStep 2199793 = 1649845) (by norm_num)
theorem B2933057 : Blo 1953435 2933057 := bstep (se 2 (by rfl) ⟨1099896, by rfl⟩ : syracuseStep 2933057 = 2199793) B2199793
theorem B1955371 : Blo 1953435 1955371 := bstep (se 1 (by rfl) ⟨1466528, by rfl⟩ : syracuseStep 1955371 = 2933057) B2933057
theorem B3344717 : Blo 1953435 3344717 := bbase (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) (by norm_num)
theorem B2229811 : Blo 1953435 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B47569301 : Blo 1953435 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B31712867 : Blo 1953435 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B21141911 : Blo 1953435 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B14094607 : Blo 1953435 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B18792809 : Blo 1953435 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B12528539 : Blo 1953435 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B8352359 : Blo 1953435 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B5568239 : Blo 1953435 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B3712159 : Blo 1953435 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B4949545 : Blo 1953435 4949545 := bstep (se 2 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 4949545 = 3712159) B3712159
theorem B6599393 : Blo 1953435 6599393 := bstep (se 2 (by rfl) ⟨2474772, by rfl⟩ : syracuseStep 6599393 = 4949545) B4949545
theorem B4399595 : Blo 1953435 4399595 := bstep (se 1 (by rfl) ⟨3299696, by rfl⟩ : syracuseStep 4399595 = 6599393) B6599393
theorem B2933063 : Blo 1953435 2933063 := bstep (se 1 (by rfl) ⟨2199797, by rfl⟩ : syracuseStep 2933063 = 4399595) B4399595
theorem B1955375 : Blo 1953435 1955375 := bstep (se 1 (by rfl) ⟨1466531, by rfl⟩ : syracuseStep 1955375 = 2933063) B2933063
theorem B2933069 : Blo 1953435 2933069 := bbase (se 3 (by rfl) ⟨549950, by rfl⟩ : syracuseStep 2933069 = 1099901) (by norm_num)
theorem B1955379 : Blo 1953435 1955379 := bstep (se 1 (by rfl) ⟨1466534, by rfl⟩ : syracuseStep 1955379 = 2933069) B2933069
theorem B4399613 : Blo 1953435 4399613 := bbase (se 3 (by rfl) ⟨824927, by rfl⟩ : syracuseStep 4399613 = 1649855) (by norm_num)
theorem B2933075 : Blo 1953435 2933075 := bstep (se 1 (by rfl) ⟨2199806, by rfl⟩ : syracuseStep 2933075 = 4399613) B4399613
theorem B1955383 : Blo 1953435 1955383 := bstep (se 1 (by rfl) ⟨1466537, by rfl⟩ : syracuseStep 1955383 = 2933075) B2933075
theorem B3299717 : Blo 1953435 3299717 := bbase (se 4 (by rfl) ⟨309348, by rfl⟩ : syracuseStep 3299717 = 618697) (by norm_num)
theorem B2199811 : Blo 1953435 2199811 := bstep (se 1 (by rfl) ⟨1649858, by rfl⟩ : syracuseStep 2199811 = 3299717) B3299717
theorem B2933081 : Blo 1953435 2933081 := bstep (se 2 (by rfl) ⟨1099905, by rfl⟩ : syracuseStep 2933081 = 2199811) B2199811
theorem B1955387 : Blo 1953435 1955387 := bstep (se 1 (by rfl) ⟨1466540, by rfl⟩ : syracuseStep 1955387 = 2933081) B2933081
theorem B14848757 : Blo 1953435 14848757 := bbase (se 5 (by rfl) ⟨696035, by rfl⟩ : syracuseStep 14848757 = 1392071) (by norm_num)
theorem B9899171 : Blo 1953435 9899171 := bstep (se 1 (by rfl) ⟨7424378, by rfl⟩ : syracuseStep 9899171 = 14848757) B14848757
theorem B6599447 : Blo 1953435 6599447 := bstep (se 1 (by rfl) ⟨4949585, by rfl⟩ : syracuseStep 6599447 = 9899171) B9899171
theorem B4399631 : Blo 1953435 4399631 := bstep (se 1 (by rfl) ⟨3299723, by rfl⟩ : syracuseStep 4399631 = 6599447) B6599447
theorem B2933087 : Blo 1953435 2933087 := bstep (se 1 (by rfl) ⟨2199815, by rfl⟩ : syracuseStep 2933087 = 4399631) B4399631
theorem B1955391 : Blo 1953435 1955391 := bstep (se 1 (by rfl) ⟨1466543, by rfl⟩ : syracuseStep 1955391 = 2933087) B2933087
theorem B2933093 : Blo 1953435 2933093 := bbase (se 4 (by rfl) ⟨274977, by rfl⟩ : syracuseStep 2933093 = 549955) (by norm_num)
theorem B1955395 : Blo 1953435 1955395 := bstep (se 1 (by rfl) ⟨1466546, by rfl⟩ : syracuseStep 1955395 = 2933093) B2933093
theorem B3712205 : Blo 1953435 3712205 := bbase (se 3 (by rfl) ⟨696038, by rfl⟩ : syracuseStep 3712205 = 1392077) (by norm_num)
theorem B2474803 : Blo 1953435 2474803 := bstep (se 1 (by rfl) ⟨1856102, by rfl⟩ : syracuseStep 2474803 = 3712205) B3712205
theorem B3299737 : Blo 1953435 3299737 := bstep (se 2 (by rfl) ⟨1237401, by rfl⟩ : syracuseStep 3299737 = 2474803) B2474803
theorem B4399649 : Blo 1953435 4399649 := bstep (se 2 (by rfl) ⟨1649868, by rfl⟩ : syracuseStep 4399649 = 3299737) B3299737
theorem B2933099 : Blo 1953435 2933099 := bstep (se 1 (by rfl) ⟨2199824, by rfl⟩ : syracuseStep 2933099 = 4399649) B4399649
theorem B1955399 : Blo 1953435 1955399 := bstep (se 1 (by rfl) ⟨1466549, by rfl⟩ : syracuseStep 1955399 = 2933099) B2933099
theorem B2199829 : Blo 1953435 2199829 := bbase (se 6 (by rfl) ⟨51558, by rfl⟩ : syracuseStep 2199829 = 103117) (by norm_num)
theorem B2933105 : Blo 1953435 2933105 := bstep (se 2 (by rfl) ⟨1099914, by rfl⟩ : syracuseStep 2933105 = 2199829) B2199829
theorem B1955403 : Blo 1953435 1955403 := bstep (se 1 (by rfl) ⟨1466552, by rfl⟩ : syracuseStep 1955403 = 2933105) B2933105
theorem B2474813 : Blo 1953435 2474813 := bbase (se 3 (by rfl) ⟨464027, by rfl⟩ : syracuseStep 2474813 = 928055) (by norm_num)
theorem B6599501 : Blo 1953435 6599501 := bstep (se 3 (by rfl) ⟨1237406, by rfl⟩ : syracuseStep 6599501 = 2474813) B2474813
theorem B4399667 : Blo 1953435 4399667 := bstep (se 1 (by rfl) ⟨3299750, by rfl⟩ : syracuseStep 4399667 = 6599501) B6599501
theorem B2933111 : Blo 1953435 2933111 := bstep (se 1 (by rfl) ⟨2199833, by rfl⟩ : syracuseStep 2933111 = 4399667) B4399667
theorem B1955407 : Blo 1953435 1955407 := bstep (se 1 (by rfl) ⟨1466555, by rfl⟩ : syracuseStep 1955407 = 2933111) B2933111
theorem B2933117 : Blo 1953435 2933117 := bbase (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) (by norm_num)
theorem B1955411 : Blo 1953435 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B4399685 : Blo 1953435 4399685 := bbase (se 4 (by rfl) ⟨412470, by rfl⟩ : syracuseStep 4399685 = 824941) (by norm_num)
theorem B2933123 : Blo 1953435 2933123 := bstep (se 1 (by rfl) ⟨2199842, by rfl⟩ : syracuseStep 2933123 = 4399685) B4399685
theorem B1955415 : Blo 1953435 1955415 := bstep (se 1 (by rfl) ⟨1466561, by rfl⟩ : syracuseStep 1955415 = 2933123) B2933123
theorem B2088137 : Blo 1953435 2088137 := bbase (se 2 (by rfl) ⟨783051, by rfl⟩ : syracuseStep 2088137 = 1566103) (by norm_num)
theorem B5568365 : Blo 1953435 5568365 := bstep (se 3 (by rfl) ⟨1044068, by rfl⟩ : syracuseStep 5568365 = 2088137) B2088137
theorem B3712243 : Blo 1953435 3712243 := bstep (se 1 (by rfl) ⟨2784182, by rfl⟩ : syracuseStep 3712243 = 5568365) B5568365
theorem B4949657 : Blo 1953435 4949657 := bstep (se 2 (by rfl) ⟨1856121, by rfl⟩ : syracuseStep 4949657 = 3712243) B3712243
theorem B3299771 : Blo 1953435 3299771 := bstep (se 1 (by rfl) ⟨2474828, by rfl⟩ : syracuseStep 3299771 = 4949657) B4949657
theorem B2199847 : Blo 1953435 2199847 := bstep (se 1 (by rfl) ⟨1649885, by rfl⟩ : syracuseStep 2199847 = 3299771) B3299771
theorem B2933129 : Blo 1953435 2933129 := bstep (se 2 (by rfl) ⟨1099923, by rfl⟩ : syracuseStep 2933129 = 2199847) B2199847
theorem B1955419 : Blo 1953435 1955419 := bstep (se 1 (by rfl) ⟨1466564, by rfl⟩ : syracuseStep 1955419 = 2933129) B2933129
theorem B9899333 : Blo 1953435 9899333 := bbase (se 4 (by rfl) ⟨928062, by rfl⟩ : syracuseStep 9899333 = 1856125) (by norm_num)
theorem B6599555 : Blo 1953435 6599555 := bstep (se 1 (by rfl) ⟨4949666, by rfl⟩ : syracuseStep 6599555 = 9899333) B9899333
theorem B4399703 : Blo 1953435 4399703 := bstep (se 1 (by rfl) ⟨3299777, by rfl⟩ : syracuseStep 4399703 = 6599555) B6599555
theorem B2933135 : Blo 1953435 2933135 := bstep (se 1 (by rfl) ⟨2199851, by rfl⟩ : syracuseStep 2933135 = 4399703) B4399703
theorem B1955423 : Blo 1953435 1955423 := bstep (se 1 (by rfl) ⟨1466567, by rfl⟩ : syracuseStep 1955423 = 2933135) B2933135
theorem B2933141 : Blo 1953435 2933141 := bbase (se 6 (by rfl) ⟨68745, by rfl⟩ : syracuseStep 2933141 = 137491) (by norm_num)
theorem B1955427 : Blo 1953435 1955427 := bstep (se 1 (by rfl) ⟨1466570, by rfl⟩ : syracuseStep 1955427 = 2933141) B2933141
theorem B3013733 : Blo 1953435 3013733 := bbase (se 4 (by rfl) ⟨282537, by rfl⟩ : syracuseStep 3013733 = 565075) (by norm_num)
theorem B2009155 : Blo 1953435 2009155 := bstep (se 1 (by rfl) ⟨1506866, by rfl⟩ : syracuseStep 2009155 = 3013733) B3013733
theorem B2678873 : Blo 1953435 2678873 := bstep (se 2 (by rfl) ⟨1004577, by rfl⟩ : syracuseStep 2678873 = 2009155) B2009155
theorem B7143661 : Blo 1953435 7143661 := bstep (se 3 (by rfl) ⟨1339436, by rfl⟩ : syracuseStep 7143661 = 2678873) B2678873
theorem B9524881 : Blo 1953435 9524881 := bstep (se 2 (by rfl) ⟨3571830, by rfl⟩ : syracuseStep 9524881 = 7143661) B7143661
theorem B12699841 : Blo 1953435 12699841 := bstep (se 2 (by rfl) ⟨4762440, by rfl⟩ : syracuseStep 12699841 = 9524881) B9524881
theorem B16933121 : Blo 1953435 16933121 := bstep (se 2 (by rfl) ⟨6349920, by rfl⟩ : syracuseStep 16933121 = 12699841) B12699841
theorem B11288747 : Blo 1953435 11288747 := bstep (se 1 (by rfl) ⟨8466560, by rfl⟩ : syracuseStep 11288747 = 16933121) B16933121
theorem B30103325 : Blo 1953435 30103325 := bstep (se 3 (by rfl) ⟨5644373, by rfl⟩ : syracuseStep 30103325 = 11288747) B11288747
theorem B20068883 : Blo 1953435 20068883 := bstep (se 1 (by rfl) ⟨15051662, by rfl⟩ : syracuseStep 20068883 = 30103325) B30103325
theorem B13379255 : Blo 1953435 13379255 := bstep (se 1 (by rfl) ⟨10034441, by rfl⟩ : syracuseStep 13379255 = 20068883) B20068883
theorem B8919503 : Blo 1953435 8919503 := bstep (se 1 (by rfl) ⟨6689627, by rfl⟩ : syracuseStep 8919503 = 13379255) B13379255
theorem B5946335 : Blo 1953435 5946335 := bstep (se 1 (by rfl) ⟨4459751, by rfl⟩ : syracuseStep 5946335 = 8919503) B8919503
theorem B3964223 : Blo 1953435 3964223 := bstep (se 1 (by rfl) ⟨2973167, by rfl⟩ : syracuseStep 3964223 = 5946335) B5946335
theorem B2642815 : Blo 1953435 2642815 := bstep (se 1 (by rfl) ⟨1982111, by rfl⟩ : syracuseStep 2642815 = 3964223) B3964223
theorem B3523753 : Blo 1953435 3523753 := bstep (se 2 (by rfl) ⟨1321407, by rfl⟩ : syracuseStep 3523753 = 2642815) B2642815
theorem B4698337 : Blo 1953435 4698337 := bstep (se 2 (by rfl) ⟨1761876, by rfl⟩ : syracuseStep 4698337 = 3523753) B3523753
theorem B6264449 : Blo 1953435 6264449 := bstep (se 2 (by rfl) ⟨2349168, by rfl⟩ : syracuseStep 6264449 = 4698337) B4698337
theorem B4176299 : Blo 1953435 4176299 := bstep (se 1 (by rfl) ⟨3132224, by rfl⟩ : syracuseStep 4176299 = 6264449) B6264449
theorem B11136797 : Blo 1953435 11136797 := bstep (se 3 (by rfl) ⟨2088149, by rfl⟩ : syracuseStep 11136797 = 4176299) B4176299
theorem B7424531 : Blo 1953435 7424531 := bstep (se 1 (by rfl) ⟨5568398, by rfl⟩ : syracuseStep 7424531 = 11136797) B11136797
theorem B4949687 : Blo 1953435 4949687 := bstep (se 1 (by rfl) ⟨3712265, by rfl⟩ : syracuseStep 4949687 = 7424531) B7424531
theorem B3299791 : Blo 1953435 3299791 := bstep (se 1 (by rfl) ⟨2474843, by rfl⟩ : syracuseStep 3299791 = 4949687) B4949687
theorem B4399721 : Blo 1953435 4399721 := bstep (se 2 (by rfl) ⟨1649895, by rfl⟩ : syracuseStep 4399721 = 3299791) B3299791
theorem B2933147 : Blo 1953435 2933147 := bstep (se 1 (by rfl) ⟨2199860, by rfl⟩ : syracuseStep 2933147 = 4399721) B4399721
theorem B1955431 : Blo 1953435 1955431 := bstep (se 1 (by rfl) ⟨1466573, by rfl⟩ : syracuseStep 1955431 = 2933147) B2933147
theorem B2199865 : Blo 1953435 2199865 := bbase (se 2 (by rfl) ⟨824949, by rfl⟩ : syracuseStep 2199865 = 1649899) (by norm_num)
theorem B2933153 : Blo 1953435 2933153 := bstep (se 2 (by rfl) ⟨1099932, by rfl⟩ : syracuseStep 2933153 = 2199865) B2199865
theorem B1955435 : Blo 1953435 1955435 := bstep (se 1 (by rfl) ⟨1466576, by rfl⟩ : syracuseStep 1955435 = 2933153) B2933153
theorem C0 (j : ℕ) (h1 : 488358 ≤ j) (h2 : j ≤ 488858) : Blo 1953435 (4 * j + 3) := by
  interval_cases j
  · exact B1953435
  · exact B1953439
  · exact B1953443
  · exact B1953447
  · exact B1953451
  · exact B1953455
  · exact B1953459
  · exact B1953463
  · exact B1953467
  · exact B1953471
  · exact B1953475
  · exact B1953479
  · exact B1953483
  · exact B1953487
  · exact B1953491
  · exact B1953495
  · exact B1953499
  · exact B1953503
  · exact B1953507
  · exact B1953511
  · exact B1953515
  · exact B1953519
  · exact B1953523
  · exact B1953527
  · exact B1953531
  · exact B1953535
  · exact B1953539
  · exact B1953543
  · exact B1953547
  · exact B1953551
  · exact B1953555
  · exact B1953559
  · exact B1953563
  · exact B1953567
  · exact B1953571
  · exact B1953575
  · exact B1953579
  · exact B1953583
  · exact B1953587
  · exact B1953591
  · exact B1953595
  · exact B1953599
  · exact B1953603
  · exact B1953607
  · exact B1953611
  · exact B1953615
  · exact B1953619
  · exact B1953623
  · exact B1953627
  · exact B1953631
  · exact B1953635
  · exact B1953639
  · exact B1953643
  · exact B1953647
  · exact B1953651
  · exact B1953655
  · exact B1953659
  · exact B1953663
  · exact B1953667
  · exact B1953671
  · exact B1953675
  · exact B1953679
  · exact B1953683
  · exact B1953687
  · exact B1953691
  · exact B1953695
  · exact B1953699
  · exact B1953703
  · exact B1953707
  · exact B1953711
  · exact B1953715
  · exact B1953719
  · exact B1953723
  · exact B1953727
  · exact B1953731
  · exact B1953735
  · exact B1953739
  · exact B1953743
  · exact B1953747
  · exact B1953751
  · exact B1953755
  · exact B1953759
  · exact B1953763
  · exact B1953767
  · exact B1953771
  · exact B1953775
  · exact B1953779
  · exact B1953783
  · exact B1953787
  · exact B1953791
  · exact B1953795
  · exact B1953799
  · exact B1953803
  · exact B1953807
  · exact B1953811
  · exact B1953815
  · exact B1953819
  · exact B1953823
  · exact B1953827
  · exact B1953831
  · exact B1953835
  · exact B1953839
  · exact B1953843
  · exact B1953847
  · exact B1953851
  · exact B1953855
  · exact B1953859
  · exact B1953863
  · exact B1953867
  · exact B1953871
  · exact B1953875
  · exact B1953879
  · exact B1953883
  · exact B1953887
  · exact B1953891
  · exact B1953895
  · exact B1953899
  · exact B1953903
  · exact B1953907
  · exact B1953911
  · exact B1953915
  · exact B1953919
  · exact B1953923
  · exact B1953927
  · exact B1953931
  · exact B1953935
  · exact B1953939
  · exact B1953943
  · exact B1953947
  · exact B1953951
  · exact B1953955
  · exact B1953959
  · exact B1953963
  · exact B1953967
  · exact B1953971
  · exact B1953975
  · exact B1953979
  · exact B1953983
  · exact B1953987
  · exact B1953991
  · exact B1953995
  · exact B1953999
  · exact B1954003
  · exact B1954007
  · exact B1954011
  · exact B1954015
  · exact B1954019
  · exact B1954023
  · exact B1954027
  · exact B1954031
  · exact B1954035
  · exact B1954039
  · exact B1954043
  · exact B1954047
  · exact B1954051
  · exact B1954055
  · exact B1954059
  · exact B1954063
  · exact B1954067
  · exact B1954071
  · exact B1954075
  · exact B1954079
  · exact B1954083
  · exact B1954087
  · exact B1954091
  · exact B1954095
  · exact B1954099
  · exact B1954103
  · exact B1954107
  · exact B1954111
  · exact B1954115
  · exact B1954119
  · exact B1954123
  · exact B1954127
  · exact B1954131
  · exact B1954135
  · exact B1954139
  · exact B1954143
  · exact B1954147
  · exact B1954151
  · exact B1954155
  · exact B1954159
  · exact B1954163
  · exact B1954167
  · exact B1954171
  · exact B1954175
  · exact B1954179
  · exact B1954183
  · exact B1954187
  · exact B1954191
  · exact B1954195
  · exact B1954199
  · exact B1954203
  · exact B1954207
  · exact B1954211
  · exact B1954215
  · exact B1954219
  · exact B1954223
  · exact B1954227
  · exact B1954231
  · exact B1954235
  · exact B1954239
  · exact B1954243
  · exact B1954247
  · exact B1954251
  · exact B1954255
  · exact B1954259
  · exact B1954263
  · exact B1954267
  · exact B1954271
  · exact B1954275
  · exact B1954279
  · exact B1954283
  · exact B1954287
  · exact B1954291
  · exact B1954295
  · exact B1954299
  · exact B1954303
  · exact B1954307
  · exact B1954311
  · exact B1954315
  · exact B1954319
  · exact B1954323
  · exact B1954327
  · exact B1954331
  · exact B1954335
  · exact B1954339
  · exact B1954343
  · exact B1954347
  · exact B1954351
  · exact B1954355
  · exact B1954359
  · exact B1954363
  · exact B1954367
  · exact B1954371
  · exact B1954375
  · exact B1954379
  · exact B1954383
  · exact B1954387
  · exact B1954391
  · exact B1954395
  · exact B1954399
  · exact B1954403
  · exact B1954407
  · exact B1954411
  · exact B1954415
  · exact B1954419
  · exact B1954423
  · exact B1954427
  · exact B1954431
  · exact B1954435
  · exact B1954439
  · exact B1954443
  · exact B1954447
  · exact B1954451
  · exact B1954455
  · exact B1954459
  · exact B1954463
  · exact B1954467
  · exact B1954471
  · exact B1954475
  · exact B1954479
  · exact B1954483
  · exact B1954487
  · exact B1954491
  · exact B1954495
  · exact B1954499
  · exact B1954503
  · exact B1954507
  · exact B1954511
  · exact B1954515
  · exact B1954519
  · exact B1954523
  · exact B1954527
  · exact B1954531
  · exact B1954535
  · exact B1954539
  · exact B1954543
  · exact B1954547
  · exact B1954551
  · exact B1954555
  · exact B1954559
  · exact B1954563
  · exact B1954567
  · exact B1954571
  · exact B1954575
  · exact B1954579
  · exact B1954583
  · exact B1954587
  · exact B1954591
  · exact B1954595
  · exact B1954599
  · exact B1954603
  · exact B1954607
  · exact B1954611
  · exact B1954615
  · exact B1954619
  · exact B1954623
  · exact B1954627
  · exact B1954631
  · exact B1954635
  · exact B1954639
  · exact B1954643
  · exact B1954647
  · exact B1954651
  · exact B1954655
  · exact B1954659
  · exact B1954663
  · exact B1954667
  · exact B1954671
  · exact B1954675
  · exact B1954679
  · exact B1954683
  · exact B1954687
  · exact B1954691
  · exact B1954695
  · exact B1954699
  · exact B1954703
  · exact B1954707
  · exact B1954711
  · exact B1954715
  · exact B1954719
  · exact B1954723
  · exact B1954727
  · exact B1954731
  · exact B1954735
  · exact B1954739
  · exact B1954743
  · exact B1954747
  · exact B1954751
  · exact B1954755
  · exact B1954759
  · exact B1954763
  · exact B1954767
  · exact B1954771
  · exact B1954775
  · exact B1954779
  · exact B1954783
  · exact B1954787
  · exact B1954791
  · exact B1954795
  · exact B1954799
  · exact B1954803
  · exact B1954807
  · exact B1954811
  · exact B1954815
  · exact B1954819
  · exact B1954823
  · exact B1954827
  · exact B1954831
  · exact B1954835
  · exact B1954839
  · exact B1954843
  · exact B1954847
  · exact B1954851
  · exact B1954855
  · exact B1954859
  · exact B1954863
  · exact B1954867
  · exact B1954871
  · exact B1954875
  · exact B1954879
  · exact B1954883
  · exact B1954887
  · exact B1954891
  · exact B1954895
  · exact B1954899
  · exact B1954903
  · exact B1954907
  · exact B1954911
  · exact B1954915
  · exact B1954919
  · exact B1954923
  · exact B1954927
  · exact B1954931
  · exact B1954935
  · exact B1954939
  · exact B1954943
  · exact B1954947
  · exact B1954951
  · exact B1954955
  · exact B1954959
  · exact B1954963
  · exact B1954967
  · exact B1954971
  · exact B1954975
  · exact B1954979
  · exact B1954983
  · exact B1954987
  · exact B1954991
  · exact B1954995
  · exact B1954999
  · exact B1955003
  · exact B1955007
  · exact B1955011
  · exact B1955015
  · exact B1955019
  · exact B1955023
  · exact B1955027
  · exact B1955031
  · exact B1955035
  · exact B1955039
  · exact B1955043
  · exact B1955047
  · exact B1955051
  · exact B1955055
  · exact B1955059
  · exact B1955063
  · exact B1955067
  · exact B1955071
  · exact B1955075
  · exact B1955079
  · exact B1955083
  · exact B1955087
  · exact B1955091
  · exact B1955095
  · exact B1955099
  · exact B1955103
  · exact B1955107
  · exact B1955111
  · exact B1955115
  · exact B1955119
  · exact B1955123
  · exact B1955127
  · exact B1955131
  · exact B1955135
  · exact B1955139
  · exact B1955143
  · exact B1955147
  · exact B1955151
  · exact B1955155
  · exact B1955159
  · exact B1955163
  · exact B1955167
  · exact B1955171
  · exact B1955175
  · exact B1955179
  · exact B1955183
  · exact B1955187
  · exact B1955191
  · exact B1955195
  · exact B1955199
  · exact B1955203
  · exact B1955207
  · exact B1955211
  · exact B1955215
  · exact B1955219
  · exact B1955223
  · exact B1955227
  · exact B1955231
  · exact B1955235
  · exact B1955239
  · exact B1955243
  · exact B1955247
  · exact B1955251
  · exact B1955255
  · exact B1955259
  · exact B1955263
  · exact B1955267
  · exact B1955271
  · exact B1955275
  · exact B1955279
  · exact B1955283
  · exact B1955287
  · exact B1955291
  · exact B1955295
  · exact B1955299
  · exact B1955303
  · exact B1955307
  · exact B1955311
  · exact B1955315
  · exact B1955319
  · exact B1955323
  · exact B1955327
  · exact B1955331
  · exact B1955335
  · exact B1955339
  · exact B1955343
  · exact B1955347
  · exact B1955351
  · exact B1955355
  · exact B1955359
  · exact B1955363
  · exact B1955367
  · exact B1955371
  · exact B1955375
  · exact B1955379
  · exact B1955383
  · exact B1955387
  · exact B1955391
  · exact B1955395
  · exact B1955399
  · exact B1955403
  · exact B1955407
  · exact B1955411
  · exact B1955415
  · exact B1955419
  · exact B1955423
  · exact B1955427
  · exact B1955431
  · exact B1955435
theorem solution (m : ℕ) (hlo : 1953435 ≤ m) (hhi : m ≤ 1955435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 488358 ≤ j := by omega
    have hj2 : j ≤ 488858 := by omega
    have hb : Blo 1953435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
