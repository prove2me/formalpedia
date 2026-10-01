-- Prove2me | solution 1 for syracuse_descends_range_1957435_1959435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:47.596044+00:00
-- url     : https://prove2.me/submissions/b13fd280-1da4-4cb3-9c0b-48e6954e76a7

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

theorem B3303173 : Blo 1957435 3303173 := bbase (se 4 (by rfl) ⟨309672, by rfl⟩ : syracuseStep 3303173 = 619345) (by norm_num)
theorem B2202115 : Blo 1957435 2202115 := bstep (se 1 (by rfl) ⟨1651586, by rfl⟩ : syracuseStep 2202115 = 3303173) B3303173
theorem B2936153 : Blo 1957435 2936153 := bstep (se 2 (by rfl) ⟨1101057, by rfl⟩ : syracuseStep 2936153 = 2202115) B2202115
theorem B1957435 : Blo 1957435 1957435 := bstep (se 1 (by rfl) ⟨1468076, by rfl⟩ : syracuseStep 1957435 = 2936153) B2936153
theorem B14864309 : Blo 1957435 14864309 := bbase (se 5 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 14864309 = 1393529) (by norm_num)
theorem B9909539 : Blo 1957435 9909539 := bstep (se 1 (by rfl) ⟨7432154, by rfl⟩ : syracuseStep 9909539 = 14864309) B14864309
theorem B6606359 : Blo 1957435 6606359 := bstep (se 1 (by rfl) ⟨4954769, by rfl⟩ : syracuseStep 6606359 = 9909539) B9909539
theorem B4404239 : Blo 1957435 4404239 := bstep (se 1 (by rfl) ⟨3303179, by rfl⟩ : syracuseStep 4404239 = 6606359) B6606359
theorem B2936159 : Blo 1957435 2936159 := bstep (se 1 (by rfl) ⟨2202119, by rfl⟩ : syracuseStep 2936159 = 4404239) B4404239
theorem B1957439 : Blo 1957435 1957439 := bstep (se 1 (by rfl) ⟨1468079, by rfl⟩ : syracuseStep 1957439 = 2936159) B2936159
theorem B2936165 : Blo 1957435 2936165 := bbase (se 4 (by rfl) ⟨275265, by rfl⟩ : syracuseStep 2936165 = 550531) (by norm_num)
theorem B1957443 : Blo 1957435 1957443 := bstep (se 1 (by rfl) ⟨1468082, by rfl⟩ : syracuseStep 1957443 = 2936165) B2936165
theorem B3716093 : Blo 1957435 3716093 := bbase (se 3 (by rfl) ⟨696767, by rfl⟩ : syracuseStep 3716093 = 1393535) (by norm_num)
theorem B2477395 : Blo 1957435 2477395 := bstep (se 1 (by rfl) ⟨1858046, by rfl⟩ : syracuseStep 2477395 = 3716093) B3716093
theorem B3303193 : Blo 1957435 3303193 := bstep (se 2 (by rfl) ⟨1238697, by rfl⟩ : syracuseStep 3303193 = 2477395) B2477395
theorem B4404257 : Blo 1957435 4404257 := bstep (se 2 (by rfl) ⟨1651596, by rfl⟩ : syracuseStep 4404257 = 3303193) B3303193
theorem B2936171 : Blo 1957435 2936171 := bstep (se 1 (by rfl) ⟨2202128, by rfl⟩ : syracuseStep 2936171 = 4404257) B4404257
theorem B1957447 : Blo 1957435 1957447 := bstep (se 1 (by rfl) ⟨1468085, by rfl⟩ : syracuseStep 1957447 = 2936171) B2936171
theorem B2202133 : Blo 1957435 2202133 := bbase (se 6 (by rfl) ⟨51612, by rfl⟩ : syracuseStep 2202133 = 103225) (by norm_num)
theorem B2936177 : Blo 1957435 2936177 := bstep (se 2 (by rfl) ⟨1101066, by rfl⟩ : syracuseStep 2936177 = 2202133) B2202133
theorem B1957451 : Blo 1957435 1957451 := bstep (se 1 (by rfl) ⟨1468088, by rfl⟩ : syracuseStep 1957451 = 2936177) B2936177
theorem B2477405 : Blo 1957435 2477405 := bbase (se 3 (by rfl) ⟨464513, by rfl⟩ : syracuseStep 2477405 = 929027) (by norm_num)
theorem B6606413 : Blo 1957435 6606413 := bstep (se 3 (by rfl) ⟨1238702, by rfl⟩ : syracuseStep 6606413 = 2477405) B2477405
theorem B4404275 : Blo 1957435 4404275 := bstep (se 1 (by rfl) ⟨3303206, by rfl⟩ : syracuseStep 4404275 = 6606413) B6606413
theorem B2936183 : Blo 1957435 2936183 := bstep (se 1 (by rfl) ⟨2202137, by rfl⟩ : syracuseStep 2936183 = 4404275) B4404275
theorem B1957455 : Blo 1957435 1957455 := bstep (se 1 (by rfl) ⟨1468091, by rfl⟩ : syracuseStep 1957455 = 2936183) B2936183
theorem B2936189 : Blo 1957435 2936189 := bbase (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) (by norm_num)
theorem B1957459 : Blo 1957435 1957459 := bstep (se 1 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 1957459 = 2936189) B2936189
theorem B4404293 : Blo 1957435 4404293 := bbase (se 4 (by rfl) ⟨412902, by rfl⟩ : syracuseStep 4404293 = 825805) (by norm_num)
theorem B2936195 : Blo 1957435 2936195 := bstep (se 1 (by rfl) ⟨2202146, by rfl⟩ : syracuseStep 2936195 = 4404293) B4404293
theorem B1957463 : Blo 1957435 1957463 := bstep (se 1 (by rfl) ⟨1468097, by rfl⟩ : syracuseStep 1957463 = 2936195) B2936195
theorem B5574197 : Blo 1957435 5574197 := bbase (se 5 (by rfl) ⟨261290, by rfl⟩ : syracuseStep 5574197 = 522581) (by norm_num)
theorem B3716131 : Blo 1957435 3716131 := bstep (se 1 (by rfl) ⟨2787098, by rfl⟩ : syracuseStep 3716131 = 5574197) B5574197
theorem B4954841 : Blo 1957435 4954841 := bstep (se 2 (by rfl) ⟨1858065, by rfl⟩ : syracuseStep 4954841 = 3716131) B3716131
theorem B3303227 : Blo 1957435 3303227 := bstep (se 1 (by rfl) ⟨2477420, by rfl⟩ : syracuseStep 3303227 = 4954841) B4954841
theorem B2202151 : Blo 1957435 2202151 := bstep (se 1 (by rfl) ⟨1651613, by rfl⟩ : syracuseStep 2202151 = 3303227) B3303227
theorem B2936201 : Blo 1957435 2936201 := bstep (se 2 (by rfl) ⟨1101075, by rfl⟩ : syracuseStep 2936201 = 2202151) B2202151
theorem B1957467 : Blo 1957435 1957467 := bstep (se 1 (by rfl) ⟨1468100, by rfl⟩ : syracuseStep 1957467 = 2936201) B2936201
theorem B9909701 : Blo 1957435 9909701 := bbase (se 4 (by rfl) ⟨929034, by rfl⟩ : syracuseStep 9909701 = 1858069) (by norm_num)
theorem B6606467 : Blo 1957435 6606467 := bstep (se 1 (by rfl) ⟨4954850, by rfl⟩ : syracuseStep 6606467 = 9909701) B9909701
theorem B4404311 : Blo 1957435 4404311 := bstep (se 1 (by rfl) ⟨3303233, by rfl⟩ : syracuseStep 4404311 = 6606467) B6606467
theorem B2936207 : Blo 1957435 2936207 := bstep (se 1 (by rfl) ⟨2202155, by rfl⟩ : syracuseStep 2936207 = 4404311) B4404311
theorem B1957471 : Blo 1957435 1957471 := bstep (se 1 (by rfl) ⟨1468103, by rfl⟩ : syracuseStep 1957471 = 2936207) B2936207
theorem B2936213 : Blo 1957435 2936213 := bbase (se 6 (by rfl) ⟨68817, by rfl⟩ : syracuseStep 2936213 = 137635) (by norm_num)
theorem B1957475 : Blo 1957435 1957475 := bstep (se 1 (by rfl) ⟨1468106, by rfl⟩ : syracuseStep 1957475 = 2936213) B2936213
theorem B2351629 : Blo 1957435 2351629 := bbase (se 3 (by rfl) ⟨440930, by rfl⟩ : syracuseStep 2351629 = 881861) (by norm_num)
theorem B3135505 : Blo 1957435 3135505 := bstep (se 2 (by rfl) ⟨1175814, by rfl⟩ : syracuseStep 3135505 = 2351629) B2351629
theorem B4180673 : Blo 1957435 4180673 := bstep (se 2 (by rfl) ⟨1567752, by rfl⟩ : syracuseStep 4180673 = 3135505) B3135505
theorem B11148461 : Blo 1957435 11148461 := bstep (se 3 (by rfl) ⟨2090336, by rfl⟩ : syracuseStep 11148461 = 4180673) B4180673
theorem B7432307 : Blo 1957435 7432307 := bstep (se 1 (by rfl) ⟨5574230, by rfl⟩ : syracuseStep 7432307 = 11148461) B11148461
theorem B4954871 : Blo 1957435 4954871 := bstep (se 1 (by rfl) ⟨3716153, by rfl⟩ : syracuseStep 4954871 = 7432307) B7432307
theorem B3303247 : Blo 1957435 3303247 := bstep (se 1 (by rfl) ⟨2477435, by rfl⟩ : syracuseStep 3303247 = 4954871) B4954871
theorem B4404329 : Blo 1957435 4404329 := bstep (se 2 (by rfl) ⟨1651623, by rfl⟩ : syracuseStep 4404329 = 3303247) B3303247
theorem B2936219 : Blo 1957435 2936219 := bstep (se 1 (by rfl) ⟨2202164, by rfl⟩ : syracuseStep 2936219 = 4404329) B4404329
theorem B1957479 : Blo 1957435 1957479 := bstep (se 1 (by rfl) ⟨1468109, by rfl⟩ : syracuseStep 1957479 = 2936219) B2936219
theorem B2202169 : Blo 1957435 2202169 := bbase (se 2 (by rfl) ⟨825813, by rfl⟩ : syracuseStep 2202169 = 1651627) (by norm_num)
theorem B2936225 : Blo 1957435 2936225 := bstep (se 2 (by rfl) ⟨1101084, by rfl⟩ : syracuseStep 2936225 = 2202169) B2202169
theorem B1957483 : Blo 1957435 1957483 := bstep (se 1 (by rfl) ⟨1468112, by rfl⟩ : syracuseStep 1957483 = 2936225) B2936225
theorem B2090345 : Blo 1957435 2090345 := bbase (se 2 (by rfl) ⟨783879, by rfl⟩ : syracuseStep 2090345 = 1567759) (by norm_num)
theorem B5574253 : Blo 1957435 5574253 := bstep (se 3 (by rfl) ⟨1045172, by rfl⟩ : syracuseStep 5574253 = 2090345) B2090345
theorem B7432337 : Blo 1957435 7432337 := bstep (se 2 (by rfl) ⟨2787126, by rfl⟩ : syracuseStep 7432337 = 5574253) B5574253
theorem B4954891 : Blo 1957435 4954891 := bstep (se 1 (by rfl) ⟨3716168, by rfl⟩ : syracuseStep 4954891 = 7432337) B7432337
theorem B6606521 : Blo 1957435 6606521 := bstep (se 2 (by rfl) ⟨2477445, by rfl⟩ : syracuseStep 6606521 = 4954891) B4954891
theorem B4404347 : Blo 1957435 4404347 := bstep (se 1 (by rfl) ⟨3303260, by rfl⟩ : syracuseStep 4404347 = 6606521) B6606521
theorem B2936231 : Blo 1957435 2936231 := bstep (se 1 (by rfl) ⟨2202173, by rfl⟩ : syracuseStep 2936231 = 4404347) B4404347
theorem B1957487 : Blo 1957435 1957487 := bstep (se 1 (by rfl) ⟨1468115, by rfl⟩ : syracuseStep 1957487 = 2936231) B2936231
theorem B2936237 : Blo 1957435 2936237 := bbase (se 3 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 2936237 = 1101089) (by norm_num)
theorem B1957491 : Blo 1957435 1957491 := bstep (se 1 (by rfl) ⟨1468118, by rfl⟩ : syracuseStep 1957491 = 2936237) B2936237
theorem B4404365 : Blo 1957435 4404365 := bbase (se 3 (by rfl) ⟨825818, by rfl⟩ : syracuseStep 4404365 = 1651637) (by norm_num)
theorem B2936243 : Blo 1957435 2936243 := bstep (se 1 (by rfl) ⟨2202182, by rfl⟩ : syracuseStep 2936243 = 4404365) B4404365
theorem B1957495 : Blo 1957435 1957495 := bstep (se 1 (by rfl) ⟨1468121, by rfl⟩ : syracuseStep 1957495 = 2936243) B2936243
theorem B2477461 : Blo 1957435 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B3303281 : Blo 1957435 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B2202187 : Blo 1957435 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B2936249 : Blo 1957435 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B1957499 : Blo 1957435 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B8928949 : Blo 1957435 8928949 := bbase (se 5 (by rfl) ⟨418544, by rfl⟩ : syracuseStep 8928949 = 837089) (by norm_num)
theorem B11905265 : Blo 1957435 11905265 := bstep (se 2 (by rfl) ⟨4464474, by rfl⟩ : syracuseStep 11905265 = 8928949) B8928949
theorem B31747373 : Blo 1957435 31747373 := bstep (se 3 (by rfl) ⟨5952632, by rfl⟩ : syracuseStep 31747373 = 11905265) B11905265
theorem B21164915 : Blo 1957435 21164915 := bstep (se 1 (by rfl) ⟨15873686, by rfl⟩ : syracuseStep 21164915 = 31747373) B31747373
theorem B56439773 : Blo 1957435 56439773 := bstep (se 3 (by rfl) ⟨10582457, by rfl⟩ : syracuseStep 56439773 = 21164915) B21164915
theorem B37626515 : Blo 1957435 37626515 := bstep (se 1 (by rfl) ⟨28219886, by rfl⟩ : syracuseStep 37626515 = 56439773) B56439773
theorem B25084343 : Blo 1957435 25084343 := bstep (se 1 (by rfl) ⟨18813257, by rfl⟩ : syracuseStep 25084343 = 37626515) B37626515
theorem B16722895 : Blo 1957435 16722895 := bstep (se 1 (by rfl) ⟨12542171, by rfl⟩ : syracuseStep 16722895 = 25084343) B25084343
theorem B22297193 : Blo 1957435 22297193 := bstep (se 2 (by rfl) ⟨8361447, by rfl⟩ : syracuseStep 22297193 = 16722895) B16722895
theorem B14864795 : Blo 1957435 14864795 := bstep (se 1 (by rfl) ⟨11148596, by rfl⟩ : syracuseStep 14864795 = 22297193) B22297193
theorem B9909863 : Blo 1957435 9909863 := bstep (se 1 (by rfl) ⟨7432397, by rfl⟩ : syracuseStep 9909863 = 14864795) B14864795
theorem B6606575 : Blo 1957435 6606575 := bstep (se 1 (by rfl) ⟨4954931, by rfl⟩ : syracuseStep 6606575 = 9909863) B9909863
theorem B4404383 : Blo 1957435 4404383 := bstep (se 1 (by rfl) ⟨3303287, by rfl⟩ : syracuseStep 4404383 = 6606575) B6606575
theorem B2936255 : Blo 1957435 2936255 := bstep (se 1 (by rfl) ⟨2202191, by rfl⟩ : syracuseStep 2936255 = 4404383) B4404383
theorem B1957503 : Blo 1957435 1957503 := bstep (se 1 (by rfl) ⟨1468127, by rfl⟩ : syracuseStep 1957503 = 2936255) B2936255
theorem B2936261 : Blo 1957435 2936261 := bbase (se 4 (by rfl) ⟨275274, by rfl⟩ : syracuseStep 2936261 = 550549) (by norm_num)
theorem B1957507 : Blo 1957435 1957507 := bstep (se 1 (by rfl) ⟨1468130, by rfl⟩ : syracuseStep 1957507 = 2936261) B2936261
theorem B3303301 : Blo 1957435 3303301 := bbase (se 4 (by rfl) ⟨309684, by rfl⟩ : syracuseStep 3303301 = 619369) (by norm_num)
theorem B4404401 : Blo 1957435 4404401 := bstep (se 2 (by rfl) ⟨1651650, by rfl⟩ : syracuseStep 4404401 = 3303301) B3303301
theorem B2936267 : Blo 1957435 2936267 := bstep (se 1 (by rfl) ⟨2202200, by rfl⟩ : syracuseStep 2936267 = 4404401) B4404401
theorem B1957511 : Blo 1957435 1957511 := bstep (se 1 (by rfl) ⟨1468133, by rfl⟩ : syracuseStep 1957511 = 2936267) B2936267
theorem B2202205 : Blo 1957435 2202205 := bbase (se 3 (by rfl) ⟨412913, by rfl⟩ : syracuseStep 2202205 = 825827) (by norm_num)
theorem B2936273 : Blo 1957435 2936273 := bstep (se 2 (by rfl) ⟨1101102, by rfl⟩ : syracuseStep 2936273 = 2202205) B2202205
theorem B1957515 : Blo 1957435 1957515 := bstep (se 1 (by rfl) ⟨1468136, by rfl⟩ : syracuseStep 1957515 = 2936273) B2936273
theorem B6606629 : Blo 1957435 6606629 := bbase (se 4 (by rfl) ⟨619371, by rfl⟩ : syracuseStep 6606629 = 1238743) (by norm_num)
theorem B4404419 : Blo 1957435 4404419 := bstep (se 1 (by rfl) ⟨3303314, by rfl⟩ : syracuseStep 4404419 = 6606629) B6606629
theorem B2936279 : Blo 1957435 2936279 := bstep (se 1 (by rfl) ⟨2202209, by rfl⟩ : syracuseStep 2936279 = 4404419) B4404419
theorem B1957519 : Blo 1957435 1957519 := bstep (se 1 (by rfl) ⟨1468139, by rfl⟩ : syracuseStep 1957519 = 2936279) B2936279
theorem B2936285 : Blo 1957435 2936285 := bbase (se 3 (by rfl) ⟨550553, by rfl⟩ : syracuseStep 2936285 = 1101107) (by norm_num)
theorem B1957523 : Blo 1957435 1957523 := bstep (se 1 (by rfl) ⟨1468142, by rfl⟩ : syracuseStep 1957523 = 2936285) B2936285
theorem B4404437 : Blo 1957435 4404437 := bbase (se 7 (by rfl) ⟨51614, by rfl⟩ : syracuseStep 4404437 = 103229) (by norm_num)
theorem B2936291 : Blo 1957435 2936291 := bstep (se 1 (by rfl) ⟨2202218, by rfl⟩ : syracuseStep 2936291 = 4404437) B4404437
theorem B1957527 : Blo 1957435 1957527 := bstep (se 1 (by rfl) ⟨1468145, by rfl⟩ : syracuseStep 1957527 = 2936291) B2936291
theorem B10582613 : Blo 1957435 10582613 := bbase (se 8 (by rfl) ⟨62007, by rfl⟩ : syracuseStep 10582613 = 124015) (by norm_num)
theorem B7055075 : Blo 1957435 7055075 := bstep (se 1 (by rfl) ⟨5291306, by rfl⟩ : syracuseStep 7055075 = 10582613) B10582613
theorem B4703383 : Blo 1957435 4703383 := bstep (se 1 (by rfl) ⟨3527537, by rfl⟩ : syracuseStep 4703383 = 7055075) B7055075
theorem B6271177 : Blo 1957435 6271177 := bstep (se 2 (by rfl) ⟨2351691, by rfl⟩ : syracuseStep 6271177 = 4703383) B4703383
theorem B8361569 : Blo 1957435 8361569 := bstep (se 2 (by rfl) ⟨3135588, by rfl⟩ : syracuseStep 8361569 = 6271177) B6271177
theorem B5574379 : Blo 1957435 5574379 := bstep (se 1 (by rfl) ⟨4180784, by rfl⟩ : syracuseStep 5574379 = 8361569) B8361569
theorem B7432505 : Blo 1957435 7432505 := bstep (se 2 (by rfl) ⟨2787189, by rfl⟩ : syracuseStep 7432505 = 5574379) B5574379
theorem B4955003 : Blo 1957435 4955003 := bstep (se 1 (by rfl) ⟨3716252, by rfl⟩ : syracuseStep 4955003 = 7432505) B7432505
theorem B3303335 : Blo 1957435 3303335 := bstep (se 1 (by rfl) ⟨2477501, by rfl⟩ : syracuseStep 3303335 = 4955003) B4955003
theorem B2202223 : Blo 1957435 2202223 := bstep (se 1 (by rfl) ⟨1651667, by rfl⟩ : syracuseStep 2202223 = 3303335) B3303335
theorem B2936297 : Blo 1957435 2936297 := bstep (se 2 (by rfl) ⟨1101111, by rfl⟩ : syracuseStep 2936297 = 2202223) B2202223
theorem B1957531 : Blo 1957435 1957531 := bstep (se 1 (by rfl) ⟨1468148, by rfl⟩ : syracuseStep 1957531 = 2936297) B2936297
theorem B2383781 : Blo 1957435 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B25426997 : Blo 1957435 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B16951331 : Blo 1957435 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B11300887 : Blo 1957435 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B60271397 : Blo 1957435 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B40180931 : Blo 1957435 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B26787287 : Blo 1957435 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B71432765 : Blo 1957435 71432765 := bstep (se 3 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 71432765 = 26787287) B26787287
theorem B47621843 : Blo 1957435 47621843 := bstep (se 1 (by rfl) ⟨35716382, by rfl⟩ : syracuseStep 47621843 = 71432765) B71432765
theorem B31747895 : Blo 1957435 31747895 := bstep (se 1 (by rfl) ⟨23810921, by rfl⟩ : syracuseStep 31747895 = 47621843) B47621843
theorem B21165263 : Blo 1957435 21165263 := bstep (se 1 (by rfl) ⟨15873947, by rfl⟩ : syracuseStep 21165263 = 31747895) B31747895
theorem B14110175 : Blo 1957435 14110175 := bstep (se 1 (by rfl) ⟨10582631, by rfl⟩ : syracuseStep 14110175 = 21165263) B21165263
theorem B9406783 : Blo 1957435 9406783 := bstep (se 1 (by rfl) ⟨7055087, by rfl⟩ : syracuseStep 9406783 = 14110175) B14110175
theorem B12542377 : Blo 1957435 12542377 := bstep (se 2 (by rfl) ⟨4703391, by rfl⟩ : syracuseStep 12542377 = 9406783) B9406783
theorem B16723169 : Blo 1957435 16723169 := bstep (se 2 (by rfl) ⟨6271188, by rfl⟩ : syracuseStep 16723169 = 12542377) B12542377
theorem B11148779 : Blo 1957435 11148779 := bstep (se 1 (by rfl) ⟨8361584, by rfl⟩ : syracuseStep 11148779 = 16723169) B16723169
theorem B7432519 : Blo 1957435 7432519 := bstep (se 1 (by rfl) ⟨5574389, by rfl⟩ : syracuseStep 7432519 = 11148779) B11148779
theorem B9910025 : Blo 1957435 9910025 := bstep (se 2 (by rfl) ⟨3716259, by rfl⟩ : syracuseStep 9910025 = 7432519) B7432519
theorem B6606683 : Blo 1957435 6606683 := bstep (se 1 (by rfl) ⟨4955012, by rfl⟩ : syracuseStep 6606683 = 9910025) B9910025
theorem B4404455 : Blo 1957435 4404455 := bstep (se 1 (by rfl) ⟨3303341, by rfl⟩ : syracuseStep 4404455 = 6606683) B6606683
theorem B2936303 : Blo 1957435 2936303 := bstep (se 1 (by rfl) ⟨2202227, by rfl⟩ : syracuseStep 2936303 = 4404455) B4404455
theorem B1957535 : Blo 1957435 1957535 := bstep (se 1 (by rfl) ⟨1468151, by rfl⟩ : syracuseStep 1957535 = 2936303) B2936303
theorem B2936309 : Blo 1957435 2936309 := bbase (se 5 (by rfl) ⟨137639, by rfl⟩ : syracuseStep 2936309 = 275279) (by norm_num)
theorem B1957539 : Blo 1957435 1957539 := bstep (se 1 (by rfl) ⟨1468154, by rfl⟩ : syracuseStep 1957539 = 2936309) B2936309
theorem B2090405 : Blo 1957435 2090405 := bbase (se 4 (by rfl) ⟨195975, by rfl⟩ : syracuseStep 2090405 = 391951) (by norm_num)
theorem B5574413 : Blo 1957435 5574413 := bstep (se 3 (by rfl) ⟨1045202, by rfl⟩ : syracuseStep 5574413 = 2090405) B2090405
theorem B3716275 : Blo 1957435 3716275 := bstep (se 1 (by rfl) ⟨2787206, by rfl⟩ : syracuseStep 3716275 = 5574413) B5574413
theorem B4955033 : Blo 1957435 4955033 := bstep (se 2 (by rfl) ⟨1858137, by rfl⟩ : syracuseStep 4955033 = 3716275) B3716275
theorem B3303355 : Blo 1957435 3303355 := bstep (se 1 (by rfl) ⟨2477516, by rfl⟩ : syracuseStep 3303355 = 4955033) B4955033
theorem B4404473 : Blo 1957435 4404473 := bstep (se 2 (by rfl) ⟨1651677, by rfl⟩ : syracuseStep 4404473 = 3303355) B3303355
theorem B2936315 : Blo 1957435 2936315 := bstep (se 1 (by rfl) ⟨2202236, by rfl⟩ : syracuseStep 2936315 = 4404473) B4404473
theorem B1957543 : Blo 1957435 1957543 := bstep (se 1 (by rfl) ⟨1468157, by rfl⟩ : syracuseStep 1957543 = 2936315) B2936315
theorem B2202241 : Blo 1957435 2202241 := bbase (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) (by norm_num)
theorem B2936321 : Blo 1957435 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B1957547 : Blo 1957435 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B4955053 : Blo 1957435 4955053 := bbase (se 3 (by rfl) ⟨929072, by rfl⟩ : syracuseStep 4955053 = 1858145) (by norm_num)
theorem B6606737 : Blo 1957435 6606737 := bstep (se 2 (by rfl) ⟨2477526, by rfl⟩ : syracuseStep 6606737 = 4955053) B4955053
theorem B4404491 : Blo 1957435 4404491 := bstep (se 1 (by rfl) ⟨3303368, by rfl⟩ : syracuseStep 4404491 = 6606737) B6606737
theorem B2936327 : Blo 1957435 2936327 := bstep (se 1 (by rfl) ⟨2202245, by rfl⟩ : syracuseStep 2936327 = 4404491) B4404491
theorem B1957551 : Blo 1957435 1957551 := bstep (se 1 (by rfl) ⟨1468163, by rfl⟩ : syracuseStep 1957551 = 2936327) B2936327
theorem B2936333 : Blo 1957435 2936333 := bbase (se 3 (by rfl) ⟨550562, by rfl⟩ : syracuseStep 2936333 = 1101125) (by norm_num)
theorem B1957555 : Blo 1957435 1957555 := bstep (se 1 (by rfl) ⟨1468166, by rfl⟩ : syracuseStep 1957555 = 2936333) B2936333
theorem B4404509 : Blo 1957435 4404509 := bbase (se 3 (by rfl) ⟨825845, by rfl⟩ : syracuseStep 4404509 = 1651691) (by norm_num)
theorem B2936339 : Blo 1957435 2936339 := bstep (se 1 (by rfl) ⟨2202254, by rfl⟩ : syracuseStep 2936339 = 4404509) B4404509
theorem B1957559 : Blo 1957435 1957559 := bstep (se 1 (by rfl) ⟨1468169, by rfl⟩ : syracuseStep 1957559 = 2936339) B2936339
theorem B3303389 : Blo 1957435 3303389 := bbase (se 3 (by rfl) ⟨619385, by rfl⟩ : syracuseStep 3303389 = 1238771) (by norm_num)
theorem B2202259 : Blo 1957435 2202259 := bstep (se 1 (by rfl) ⟨1651694, by rfl⟩ : syracuseStep 2202259 = 3303389) B3303389
theorem B2936345 : Blo 1957435 2936345 := bstep (se 2 (by rfl) ⟨1101129, by rfl⟩ : syracuseStep 2936345 = 2202259) B2202259
theorem B1957563 : Blo 1957435 1957563 := bstep (se 1 (by rfl) ⟨1468172, by rfl⟩ : syracuseStep 1957563 = 2936345) B2936345
theorem B10582805 : Blo 1957435 10582805 := bbase (se 6 (by rfl) ⟨248034, by rfl⟩ : syracuseStep 10582805 = 496069) (by norm_num)
theorem B7055203 : Blo 1957435 7055203 := bstep (se 1 (by rfl) ⟨5291402, by rfl⟩ : syracuseStep 7055203 = 10582805) B10582805
theorem B9406937 : Blo 1957435 9406937 := bstep (se 2 (by rfl) ⟨3527601, by rfl⟩ : syracuseStep 9406937 = 7055203) B7055203
theorem B6271291 : Blo 1957435 6271291 := bstep (se 1 (by rfl) ⟨4703468, by rfl⟩ : syracuseStep 6271291 = 9406937) B9406937
theorem B8361721 : Blo 1957435 8361721 := bstep (se 2 (by rfl) ⟨3135645, by rfl⟩ : syracuseStep 8361721 = 6271291) B6271291
theorem B11148961 : Blo 1957435 11148961 := bstep (se 2 (by rfl) ⟨4180860, by rfl⟩ : syracuseStep 11148961 = 8361721) B8361721
theorem B14865281 : Blo 1957435 14865281 := bstep (se 2 (by rfl) ⟨5574480, by rfl⟩ : syracuseStep 14865281 = 11148961) B11148961
theorem B9910187 : Blo 1957435 9910187 := bstep (se 1 (by rfl) ⟨7432640, by rfl⟩ : syracuseStep 9910187 = 14865281) B14865281
theorem B6606791 : Blo 1957435 6606791 := bstep (se 1 (by rfl) ⟨4955093, by rfl⟩ : syracuseStep 6606791 = 9910187) B9910187
theorem B4404527 : Blo 1957435 4404527 := bstep (se 1 (by rfl) ⟨3303395, by rfl⟩ : syracuseStep 4404527 = 6606791) B6606791
theorem B2936351 : Blo 1957435 2936351 := bstep (se 1 (by rfl) ⟨2202263, by rfl⟩ : syracuseStep 2936351 = 4404527) B4404527
theorem B1957567 : Blo 1957435 1957567 := bstep (se 1 (by rfl) ⟨1468175, by rfl⟩ : syracuseStep 1957567 = 2936351) B2936351
theorem B2936357 : Blo 1957435 2936357 := bbase (se 4 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 2936357 = 550567) (by norm_num)
theorem B1957571 : Blo 1957435 1957571 := bstep (se 1 (by rfl) ⟨1468178, by rfl⟩ : syracuseStep 1957571 = 2936357) B2936357
theorem B2477557 : Blo 1957435 2477557 := bbase (se 5 (by rfl) ⟨116135, by rfl⟩ : syracuseStep 2477557 = 232271) (by norm_num)
theorem B3303409 : Blo 1957435 3303409 := bstep (se 2 (by rfl) ⟨1238778, by rfl⟩ : syracuseStep 3303409 = 2477557) B2477557
theorem B4404545 : Blo 1957435 4404545 := bstep (se 2 (by rfl) ⟨1651704, by rfl⟩ : syracuseStep 4404545 = 3303409) B3303409
theorem B2936363 : Blo 1957435 2936363 := bstep (se 1 (by rfl) ⟨2202272, by rfl⟩ : syracuseStep 2936363 = 4404545) B4404545
theorem B1957575 : Blo 1957435 1957575 := bstep (se 1 (by rfl) ⟨1468181, by rfl⟩ : syracuseStep 1957575 = 2936363) B2936363
theorem B2202277 : Blo 1957435 2202277 := bbase (se 4 (by rfl) ⟨206463, by rfl⟩ : syracuseStep 2202277 = 412927) (by norm_num)
theorem B2936369 : Blo 1957435 2936369 := bstep (se 2 (by rfl) ⟨1101138, by rfl⟩ : syracuseStep 2936369 = 2202277) B2202277
theorem B1957579 : Blo 1957435 1957579 := bstep (se 1 (by rfl) ⟨1468184, by rfl⟩ : syracuseStep 1957579 = 2936369) B2936369
theorem B2232329 : Blo 1957435 2232329 := bbase (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) (by norm_num)
theorem B23811509 : Blo 1957435 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B63497357 : Blo 1957435 63497357 := bstep (se 3 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 63497357 = 23811509) B23811509
theorem B42331571 : Blo 1957435 42331571 := bstep (se 1 (by rfl) ⟨31748678, by rfl⟩ : syracuseStep 42331571 = 63497357) B63497357
theorem B28221047 : Blo 1957435 28221047 := bstep (se 1 (by rfl) ⟨21165785, by rfl⟩ : syracuseStep 28221047 = 42331571) B42331571
theorem B18814031 : Blo 1957435 18814031 := bstep (se 1 (by rfl) ⟨14110523, by rfl⟩ : syracuseStep 18814031 = 28221047) B28221047
theorem B12542687 : Blo 1957435 12542687 := bstep (se 1 (by rfl) ⟨9407015, by rfl⟩ : syracuseStep 12542687 = 18814031) B18814031
theorem B8361791 : Blo 1957435 8361791 := bstep (se 1 (by rfl) ⟨6271343, by rfl⟩ : syracuseStep 8361791 = 12542687) B12542687
theorem B5574527 : Blo 1957435 5574527 := bstep (se 1 (by rfl) ⟨4180895, by rfl⟩ : syracuseStep 5574527 = 8361791) B8361791
theorem B3716351 : Blo 1957435 3716351 := bstep (se 1 (by rfl) ⟨2787263, by rfl⟩ : syracuseStep 3716351 = 5574527) B5574527
theorem B2477567 : Blo 1957435 2477567 := bstep (se 1 (by rfl) ⟨1858175, by rfl⟩ : syracuseStep 2477567 = 3716351) B3716351
theorem B6606845 : Blo 1957435 6606845 := bstep (se 3 (by rfl) ⟨1238783, by rfl⟩ : syracuseStep 6606845 = 2477567) B2477567
theorem B4404563 : Blo 1957435 4404563 := bstep (se 1 (by rfl) ⟨3303422, by rfl⟩ : syracuseStep 4404563 = 6606845) B6606845
theorem B2936375 : Blo 1957435 2936375 := bstep (se 1 (by rfl) ⟨2202281, by rfl⟩ : syracuseStep 2936375 = 4404563) B4404563
theorem B1957583 : Blo 1957435 1957583 := bstep (se 1 (by rfl) ⟨1468187, by rfl⟩ : syracuseStep 1957583 = 2936375) B2936375
theorem B2936381 : Blo 1957435 2936381 := bbase (se 3 (by rfl) ⟨550571, by rfl⟩ : syracuseStep 2936381 = 1101143) (by norm_num)
theorem B1957587 : Blo 1957435 1957587 := bstep (se 1 (by rfl) ⟨1468190, by rfl⟩ : syracuseStep 1957587 = 2936381) B2936381
theorem B4404581 : Blo 1957435 4404581 := bbase (se 4 (by rfl) ⟨412929, by rfl⟩ : syracuseStep 4404581 = 825859) (by norm_num)
theorem B2936387 : Blo 1957435 2936387 := bstep (se 1 (by rfl) ⟨2202290, by rfl⟩ : syracuseStep 2936387 = 4404581) B4404581
theorem B1957591 : Blo 1957435 1957591 := bstep (se 1 (by rfl) ⟨1468193, by rfl⟩ : syracuseStep 1957591 = 2936387) B2936387
theorem B4955165 : Blo 1957435 4955165 := bbase (se 3 (by rfl) ⟨929093, by rfl⟩ : syracuseStep 4955165 = 1858187) (by norm_num)
theorem B3303443 : Blo 1957435 3303443 := bstep (se 1 (by rfl) ⟨2477582, by rfl⟩ : syracuseStep 3303443 = 4955165) B4955165
theorem B2202295 : Blo 1957435 2202295 := bstep (se 1 (by rfl) ⟨1651721, by rfl⟩ : syracuseStep 2202295 = 3303443) B3303443
theorem B2936393 : Blo 1957435 2936393 := bstep (se 2 (by rfl) ⟨1101147, by rfl⟩ : syracuseStep 2936393 = 2202295) B2202295
theorem B1957595 : Blo 1957435 1957595 := bstep (se 1 (by rfl) ⟨1468196, by rfl⟩ : syracuseStep 1957595 = 2936393) B2936393
theorem B3716381 : Blo 1957435 3716381 := bbase (se 3 (by rfl) ⟨696821, by rfl⟩ : syracuseStep 3716381 = 1393643) (by norm_num)
theorem B9910349 : Blo 1957435 9910349 := bstep (se 3 (by rfl) ⟨1858190, by rfl⟩ : syracuseStep 9910349 = 3716381) B3716381
theorem B6606899 : Blo 1957435 6606899 := bstep (se 1 (by rfl) ⟨4955174, by rfl⟩ : syracuseStep 6606899 = 9910349) B9910349
theorem B4404599 : Blo 1957435 4404599 := bstep (se 1 (by rfl) ⟨3303449, by rfl⟩ : syracuseStep 4404599 = 6606899) B6606899
theorem B2936399 : Blo 1957435 2936399 := bstep (se 1 (by rfl) ⟨2202299, by rfl⟩ : syracuseStep 2936399 = 4404599) B4404599
theorem B1957599 : Blo 1957435 1957599 := bstep (se 1 (by rfl) ⟨1468199, by rfl⟩ : syracuseStep 1957599 = 2936399) B2936399
theorem B2936405 : Blo 1957435 2936405 := bbase (se 8 (by rfl) ⟨17205, by rfl⟩ : syracuseStep 2936405 = 34411) (by norm_num)
theorem B1957603 : Blo 1957435 1957603 := bstep (se 1 (by rfl) ⟨1468202, by rfl⟩ : syracuseStep 1957603 = 2936405) B2936405
theorem B8361893 : Blo 1957435 8361893 := bbase (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) (by norm_num)
theorem B5574595 : Blo 1957435 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B7432793 : Blo 1957435 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B4955195 : Blo 1957435 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B3303463 : Blo 1957435 3303463 := bstep (se 1 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 3303463 = 4955195) B4955195
theorem B4404617 : Blo 1957435 4404617 := bstep (se 2 (by rfl) ⟨1651731, by rfl⟩ : syracuseStep 4404617 = 3303463) B3303463
theorem B2936411 : Blo 1957435 2936411 := bstep (se 1 (by rfl) ⟨2202308, by rfl⟩ : syracuseStep 2936411 = 4404617) B4404617
theorem B1957607 : Blo 1957435 1957607 := bstep (se 1 (by rfl) ⟨1468205, by rfl⟩ : syracuseStep 1957607 = 2936411) B2936411
theorem B2202313 : Blo 1957435 2202313 := bbase (se 2 (by rfl) ⟨825867, by rfl⟩ : syracuseStep 2202313 = 1651735) (by norm_num)
theorem B2936417 : Blo 1957435 2936417 := bstep (se 2 (by rfl) ⟨1101156, by rfl⟩ : syracuseStep 2936417 = 2202313) B2202313
theorem B1957611 : Blo 1957435 1957611 := bstep (se 1 (by rfl) ⟨1468208, by rfl⟩ : syracuseStep 1957611 = 2936417) B2936417
theorem B6271445 : Blo 1957435 6271445 := bbase (se 7 (by rfl) ⟨73493, by rfl⟩ : syracuseStep 6271445 = 146987) (by norm_num)
theorem B16723853 : Blo 1957435 16723853 := bstep (se 3 (by rfl) ⟨3135722, by rfl⟩ : syracuseStep 16723853 = 6271445) B6271445
theorem B11149235 : Blo 1957435 11149235 := bstep (se 1 (by rfl) ⟨8361926, by rfl⟩ : syracuseStep 11149235 = 16723853) B16723853
theorem B7432823 : Blo 1957435 7432823 := bstep (se 1 (by rfl) ⟨5574617, by rfl⟩ : syracuseStep 7432823 = 11149235) B11149235
theorem B4955215 : Blo 1957435 4955215 := bstep (se 1 (by rfl) ⟨3716411, by rfl⟩ : syracuseStep 4955215 = 7432823) B7432823
theorem B6606953 : Blo 1957435 6606953 := bstep (se 2 (by rfl) ⟨2477607, by rfl⟩ : syracuseStep 6606953 = 4955215) B4955215
theorem B4404635 : Blo 1957435 4404635 := bstep (se 1 (by rfl) ⟨3303476, by rfl⟩ : syracuseStep 4404635 = 6606953) B6606953
theorem B2936423 : Blo 1957435 2936423 := bstep (se 1 (by rfl) ⟨2202317, by rfl⟩ : syracuseStep 2936423 = 4404635) B4404635
theorem B1957615 : Blo 1957435 1957615 := bstep (se 1 (by rfl) ⟨1468211, by rfl⟩ : syracuseStep 1957615 = 2936423) B2936423
theorem B2936429 : Blo 1957435 2936429 := bbase (se 3 (by rfl) ⟨550580, by rfl⟩ : syracuseStep 2936429 = 1101161) (by norm_num)
theorem B1957619 : Blo 1957435 1957619 := bstep (se 1 (by rfl) ⟨1468214, by rfl⟩ : syracuseStep 1957619 = 2936429) B2936429
theorem B4404653 : Blo 1957435 4404653 := bbase (se 3 (by rfl) ⟨825872, by rfl⟩ : syracuseStep 4404653 = 1651745) (by norm_num)
theorem B2936435 : Blo 1957435 2936435 := bstep (se 1 (by rfl) ⟨2202326, by rfl⟩ : syracuseStep 2936435 = 4404653) B4404653
theorem B1957623 : Blo 1957435 1957623 := bstep (se 1 (by rfl) ⟨1468217, by rfl⟩ : syracuseStep 1957623 = 2936435) B2936435
theorem B33904277 : Blo 1957435 33904277 := bbase (se 6 (by rfl) ⟨794631, by rfl⟩ : syracuseStep 33904277 = 1589263) (by norm_num)
theorem B22602851 : Blo 1957435 22602851 := bstep (se 1 (by rfl) ⟨16952138, by rfl⟩ : syracuseStep 22602851 = 33904277) B33904277
theorem B15068567 : Blo 1957435 15068567 := bstep (se 1 (by rfl) ⟨11301425, by rfl⟩ : syracuseStep 15068567 = 22602851) B22602851
theorem B10045711 : Blo 1957435 10045711 := bstep (se 1 (by rfl) ⟨7534283, by rfl⟩ : syracuseStep 10045711 = 15068567) B15068567
theorem B53577125 : Blo 1957435 53577125 := bstep (se 4 (by rfl) ⟨5022855, by rfl⟩ : syracuseStep 53577125 = 10045711) B10045711
theorem B35718083 : Blo 1957435 35718083 := bstep (se 1 (by rfl) ⟨26788562, by rfl⟩ : syracuseStep 35718083 = 53577125) B53577125
theorem B23812055 : Blo 1957435 23812055 := bstep (se 1 (by rfl) ⟨17859041, by rfl⟩ : syracuseStep 23812055 = 35718083) B35718083
theorem B15874703 : Blo 1957435 15874703 := bstep (se 1 (by rfl) ⟨11906027, by rfl⟩ : syracuseStep 15874703 = 23812055) B23812055
theorem B10583135 : Blo 1957435 10583135 := bstep (se 1 (by rfl) ⟨7937351, by rfl⟩ : syracuseStep 10583135 = 15874703) B15874703
theorem B7055423 : Blo 1957435 7055423 := bstep (se 1 (by rfl) ⟨5291567, by rfl⟩ : syracuseStep 7055423 = 10583135) B10583135
theorem B4703615 : Blo 1957435 4703615 := bstep (se 1 (by rfl) ⟨3527711, by rfl⟩ : syracuseStep 4703615 = 7055423) B7055423
theorem B3135743 : Blo 1957435 3135743 := bstep (se 1 (by rfl) ⟨2351807, by rfl⟩ : syracuseStep 3135743 = 4703615) B4703615
theorem B2090495 : Blo 1957435 2090495 := bstep (se 1 (by rfl) ⟨1567871, by rfl⟩ : syracuseStep 2090495 = 3135743) B3135743
theorem B5574653 : Blo 1957435 5574653 := bstep (se 3 (by rfl) ⟨1045247, by rfl⟩ : syracuseStep 5574653 = 2090495) B2090495
theorem B3716435 : Blo 1957435 3716435 := bstep (se 1 (by rfl) ⟨2787326, by rfl⟩ : syracuseStep 3716435 = 5574653) B5574653
theorem B2477623 : Blo 1957435 2477623 := bstep (se 1 (by rfl) ⟨1858217, by rfl⟩ : syracuseStep 2477623 = 3716435) B3716435
theorem B3303497 : Blo 1957435 3303497 := bstep (se 2 (by rfl) ⟨1238811, by rfl⟩ : syracuseStep 3303497 = 2477623) B2477623
theorem B2202331 : Blo 1957435 2202331 := bstep (se 1 (by rfl) ⟨1651748, by rfl⟩ : syracuseStep 2202331 = 3303497) B3303497
theorem B2936441 : Blo 1957435 2936441 := bstep (se 2 (by rfl) ⟨1101165, by rfl⟩ : syracuseStep 2936441 = 2202331) B2202331
theorem B1957627 : Blo 1957435 1957627 := bstep (se 1 (by rfl) ⟨1468220, by rfl⟩ : syracuseStep 1957627 = 2936441) B2936441
theorem B4767797 : Blo 1957435 4767797 := bbase (se 5 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 4767797 = 446981) (by norm_num)
theorem B3178531 : Blo 1957435 3178531 := bstep (se 1 (by rfl) ⟨2383898, by rfl⟩ : syracuseStep 3178531 = 4767797) B4767797
theorem B4238041 : Blo 1957435 4238041 := bstep (se 2 (by rfl) ⟨1589265, by rfl⟩ : syracuseStep 4238041 = 3178531) B3178531
theorem B5650721 : Blo 1957435 5650721 := bstep (se 2 (by rfl) ⟨2119020, by rfl⟩ : syracuseStep 5650721 = 4238041) B4238041
theorem B3767147 : Blo 1957435 3767147 := bstep (se 1 (by rfl) ⟨2825360, by rfl⟩ : syracuseStep 3767147 = 5650721) B5650721
theorem B2511431 : Blo 1957435 2511431 := bstep (se 1 (by rfl) ⟨1883573, by rfl⟩ : syracuseStep 2511431 = 3767147) B3767147
theorem B107154389 : Blo 1957435 107154389 := bstep (se 7 (by rfl) ⟨1255715, by rfl⟩ : syracuseStep 107154389 = 2511431) B2511431
theorem B71436259 : Blo 1957435 71436259 := bstep (se 1 (by rfl) ⟨53577194, by rfl⟩ : syracuseStep 71436259 = 107154389) B107154389
theorem B95248345 : Blo 1957435 95248345 := bstep (se 2 (by rfl) ⟨35718129, by rfl⟩ : syracuseStep 95248345 = 71436259) B71436259
theorem B126997793 : Blo 1957435 126997793 := bstep (se 2 (by rfl) ⟨47624172, by rfl⟩ : syracuseStep 126997793 = 95248345) B95248345
theorem B84665195 : Blo 1957435 84665195 := bstep (se 1 (by rfl) ⟨63498896, by rfl⟩ : syracuseStep 84665195 = 126997793) B126997793
theorem B56443463 : Blo 1957435 56443463 := bstep (se 1 (by rfl) ⟨42332597, by rfl⟩ : syracuseStep 56443463 = 84665195) B84665195
theorem B37628975 : Blo 1957435 37628975 := bstep (se 1 (by rfl) ⟨28221731, by rfl⟩ : syracuseStep 37628975 = 56443463) B56443463
theorem B25085983 : Blo 1957435 25085983 := bstep (se 1 (by rfl) ⟨18814487, by rfl⟩ : syracuseStep 25085983 = 37628975) B37628975
theorem B33447977 : Blo 1957435 33447977 := bstep (se 2 (by rfl) ⟨12542991, by rfl⟩ : syracuseStep 33447977 = 25085983) B25085983
theorem B22298651 : Blo 1957435 22298651 := bstep (se 1 (by rfl) ⟨16723988, by rfl⟩ : syracuseStep 22298651 = 33447977) B33447977
theorem B14865767 : Blo 1957435 14865767 := bstep (se 1 (by rfl) ⟨11149325, by rfl⟩ : syracuseStep 14865767 = 22298651) B22298651
theorem B9910511 : Blo 1957435 9910511 := bstep (se 1 (by rfl) ⟨7432883, by rfl⟩ : syracuseStep 9910511 = 14865767) B14865767
theorem B6607007 : Blo 1957435 6607007 := bstep (se 1 (by rfl) ⟨4955255, by rfl⟩ : syracuseStep 6607007 = 9910511) B9910511
theorem B4404671 : Blo 1957435 4404671 := bstep (se 1 (by rfl) ⟨3303503, by rfl⟩ : syracuseStep 4404671 = 6607007) B6607007
theorem B2936447 : Blo 1957435 2936447 := bstep (se 1 (by rfl) ⟨2202335, by rfl⟩ : syracuseStep 2936447 = 4404671) B4404671
theorem B1957631 : Blo 1957435 1957631 := bstep (se 1 (by rfl) ⟨1468223, by rfl⟩ : syracuseStep 1957631 = 2936447) B2936447
theorem B2936453 : Blo 1957435 2936453 := bbase (se 4 (by rfl) ⟨275292, by rfl⟩ : syracuseStep 2936453 = 550585) (by norm_num)
theorem B1957635 : Blo 1957435 1957635 := bstep (se 1 (by rfl) ⟨1468226, by rfl⟩ : syracuseStep 1957635 = 2936453) B2936453
theorem B3303517 : Blo 1957435 3303517 := bbase (se 3 (by rfl) ⟨619409, by rfl⟩ : syracuseStep 3303517 = 1238819) (by norm_num)
theorem B4404689 : Blo 1957435 4404689 := bstep (se 2 (by rfl) ⟨1651758, by rfl⟩ : syracuseStep 4404689 = 3303517) B3303517
theorem B2936459 : Blo 1957435 2936459 := bstep (se 1 (by rfl) ⟨2202344, by rfl⟩ : syracuseStep 2936459 = 4404689) B4404689
theorem B1957639 : Blo 1957435 1957639 := bstep (se 1 (by rfl) ⟨1468229, by rfl⟩ : syracuseStep 1957639 = 2936459) B2936459
theorem B2202349 : Blo 1957435 2202349 := bbase (se 3 (by rfl) ⟨412940, by rfl⟩ : syracuseStep 2202349 = 825881) (by norm_num)
theorem B2936465 : Blo 1957435 2936465 := bstep (se 2 (by rfl) ⟨1101174, by rfl⟩ : syracuseStep 2936465 = 2202349) B2202349
theorem B1957643 : Blo 1957435 1957643 := bstep (se 1 (by rfl) ⟨1468232, by rfl⟩ : syracuseStep 1957643 = 2936465) B2936465
theorem B6607061 : Blo 1957435 6607061 := bbase (se 7 (by rfl) ⟨77426, by rfl⟩ : syracuseStep 6607061 = 154853) (by norm_num)
theorem B4404707 : Blo 1957435 4404707 := bstep (se 1 (by rfl) ⟨3303530, by rfl⟩ : syracuseStep 4404707 = 6607061) B6607061
theorem B2936471 : Blo 1957435 2936471 := bstep (se 1 (by rfl) ⟨2202353, by rfl⟩ : syracuseStep 2936471 = 4404707) B4404707
theorem B1957647 : Blo 1957435 1957647 := bstep (se 1 (by rfl) ⟨1468235, by rfl⟩ : syracuseStep 1957647 = 2936471) B2936471
theorem B2936477 : Blo 1957435 2936477 := bbase (se 3 (by rfl) ⟨550589, by rfl⟩ : syracuseStep 2936477 = 1101179) (by norm_num)
theorem B1957651 : Blo 1957435 1957651 := bstep (se 1 (by rfl) ⟨1468238, by rfl⟩ : syracuseStep 1957651 = 2936477) B2936477
theorem B4404725 : Blo 1957435 4404725 := bbase (se 5 (by rfl) ⟨206471, by rfl⟩ : syracuseStep 4404725 = 412943) (by norm_num)
theorem B2936483 : Blo 1957435 2936483 := bstep (se 1 (by rfl) ⟨2202362, by rfl⟩ : syracuseStep 2936483 = 4404725) B4404725
theorem B1957655 : Blo 1957435 1957655 := bstep (se 1 (by rfl) ⟨1468241, by rfl⟩ : syracuseStep 1957655 = 2936483) B2936483
theorem B2718517 : Blo 1957435 2718517 := bbase (se 5 (by rfl) ⟨127430, by rfl⟩ : syracuseStep 2718517 = 254861) (by norm_num)
theorem B3624689 : Blo 1957435 3624689 := bstep (se 2 (by rfl) ⟨1359258, by rfl⟩ : syracuseStep 3624689 = 2718517) B2718517
theorem B2416459 : Blo 1957435 2416459 := bstep (se 1 (by rfl) ⟨1812344, by rfl⟩ : syracuseStep 2416459 = 3624689) B3624689
theorem B3221945 : Blo 1957435 3221945 := bstep (se 2 (by rfl) ⟨1208229, by rfl⟩ : syracuseStep 3221945 = 2416459) B2416459
theorem B2147963 : Blo 1957435 2147963 := bstep (se 1 (by rfl) ⟨1610972, by rfl⟩ : syracuseStep 2147963 = 3221945) B3221945
theorem B22911605 : Blo 1957435 22911605 := bstep (se 5 (by rfl) ⟨1073981, by rfl⟩ : syracuseStep 22911605 = 2147963) B2147963
theorem B15274403 : Blo 1957435 15274403 := bstep (se 1 (by rfl) ⟨11455802, by rfl⟩ : syracuseStep 15274403 = 22911605) B22911605
theorem B10182935 : Blo 1957435 10182935 := bstep (se 1 (by rfl) ⟨7637201, by rfl⟩ : syracuseStep 10182935 = 15274403) B15274403
theorem B6788623 : Blo 1957435 6788623 := bstep (se 1 (by rfl) ⟨5091467, by rfl⟩ : syracuseStep 6788623 = 10182935) B10182935
theorem B9051497 : Blo 1957435 9051497 := bstep (se 2 (by rfl) ⟨3394311, by rfl⟩ : syracuseStep 9051497 = 6788623) B6788623
theorem B6034331 : Blo 1957435 6034331 := bstep (se 1 (by rfl) ⟨4525748, by rfl⟩ : syracuseStep 6034331 = 9051497) B9051497
theorem B4022887 : Blo 1957435 4022887 := bstep (se 1 (by rfl) ⟨3017165, by rfl⟩ : syracuseStep 4022887 = 6034331) B6034331
theorem B5363849 : Blo 1957435 5363849 := bstep (se 2 (by rfl) ⟨2011443, by rfl⟩ : syracuseStep 5363849 = 4022887) B4022887
theorem B3575899 : Blo 1957435 3575899 := bstep (se 1 (by rfl) ⟨2681924, by rfl⟩ : syracuseStep 3575899 = 5363849) B5363849
theorem B4767865 : Blo 1957435 4767865 := bstep (se 2 (by rfl) ⟨1787949, by rfl⟩ : syracuseStep 4767865 = 3575899) B3575899
theorem B25428613 : Blo 1957435 25428613 := bstep (se 4 (by rfl) ⟨2383932, by rfl⟩ : syracuseStep 25428613 = 4767865) B4767865
theorem B33904817 : Blo 1957435 33904817 := bstep (se 2 (by rfl) ⟨12714306, by rfl⟩ : syracuseStep 33904817 = 25428613) B25428613
theorem B22603211 : Blo 1957435 22603211 := bstep (se 1 (by rfl) ⟨16952408, by rfl⟩ : syracuseStep 22603211 = 33904817) B33904817
theorem B15068807 : Blo 1957435 15068807 := bstep (se 1 (by rfl) ⟨11301605, by rfl⟩ : syracuseStep 15068807 = 22603211) B22603211
theorem B10045871 : Blo 1957435 10045871 := bstep (se 1 (by rfl) ⟨7534403, by rfl⟩ : syracuseStep 10045871 = 15068807) B15068807
theorem B6697247 : Blo 1957435 6697247 := bstep (se 1 (by rfl) ⟨5022935, by rfl⟩ : syracuseStep 6697247 = 10045871) B10045871
theorem B17859325 : Blo 1957435 17859325 := bstep (se 3 (by rfl) ⟨3348623, by rfl⟩ : syracuseStep 17859325 = 6697247) B6697247
theorem B23812433 : Blo 1957435 23812433 := bstep (se 2 (by rfl) ⟨8929662, by rfl⟩ : syracuseStep 23812433 = 17859325) B17859325
theorem B15874955 : Blo 1957435 15874955 := bstep (se 1 (by rfl) ⟨11906216, by rfl⟩ : syracuseStep 15874955 = 23812433) B23812433
theorem B10583303 : Blo 1957435 10583303 := bstep (se 1 (by rfl) ⟨7937477, by rfl⟩ : syracuseStep 10583303 = 15874955) B15874955
theorem B28222141 : Blo 1957435 28222141 := bstep (se 3 (by rfl) ⟨5291651, by rfl⟩ : syracuseStep 28222141 = 10583303) B10583303
theorem B37629521 : Blo 1957435 37629521 := bstep (se 2 (by rfl) ⟨14111070, by rfl⟩ : syracuseStep 37629521 = 28222141) B28222141
theorem B25086347 : Blo 1957435 25086347 := bstep (se 1 (by rfl) ⟨18814760, by rfl⟩ : syracuseStep 25086347 = 37629521) B37629521
theorem B16724231 : Blo 1957435 16724231 := bstep (se 1 (by rfl) ⟨12543173, by rfl⟩ : syracuseStep 16724231 = 25086347) B25086347
theorem B11149487 : Blo 1957435 11149487 := bstep (se 1 (by rfl) ⟨8362115, by rfl⟩ : syracuseStep 11149487 = 16724231) B16724231
theorem B7432991 : Blo 1957435 7432991 := bstep (se 1 (by rfl) ⟨5574743, by rfl⟩ : syracuseStep 7432991 = 11149487) B11149487
theorem B4955327 : Blo 1957435 4955327 := bstep (se 1 (by rfl) ⟨3716495, by rfl⟩ : syracuseStep 4955327 = 7432991) B7432991
theorem B3303551 : Blo 1957435 3303551 := bstep (se 1 (by rfl) ⟨2477663, by rfl⟩ : syracuseStep 3303551 = 4955327) B4955327
theorem B2202367 : Blo 1957435 2202367 := bstep (se 1 (by rfl) ⟨1651775, by rfl⟩ : syracuseStep 2202367 = 3303551) B3303551
theorem B2936489 : Blo 1957435 2936489 := bstep (se 2 (by rfl) ⟨1101183, by rfl⟩ : syracuseStep 2936489 = 2202367) B2202367
theorem B1957659 : Blo 1957435 1957659 := bstep (se 1 (by rfl) ⟨1468244, by rfl⟩ : syracuseStep 1957659 = 2936489) B2936489
theorem B2090533 : Blo 1957435 2090533 := bbase (se 4 (by rfl) ⟨195987, by rfl⟩ : syracuseStep 2090533 = 391975) (by norm_num)
theorem B2787377 : Blo 1957435 2787377 := bstep (se 2 (by rfl) ⟨1045266, by rfl⟩ : syracuseStep 2787377 = 2090533) B2090533
theorem B7433005 : Blo 1957435 7433005 := bstep (se 3 (by rfl) ⟨1393688, by rfl⟩ : syracuseStep 7433005 = 2787377) B2787377
theorem B9910673 : Blo 1957435 9910673 := bstep (se 2 (by rfl) ⟨3716502, by rfl⟩ : syracuseStep 9910673 = 7433005) B7433005
theorem B6607115 : Blo 1957435 6607115 := bstep (se 1 (by rfl) ⟨4955336, by rfl⟩ : syracuseStep 6607115 = 9910673) B9910673
theorem B4404743 : Blo 1957435 4404743 := bstep (se 1 (by rfl) ⟨3303557, by rfl⟩ : syracuseStep 4404743 = 6607115) B6607115
theorem B2936495 : Blo 1957435 2936495 := bstep (se 1 (by rfl) ⟨2202371, by rfl⟩ : syracuseStep 2936495 = 4404743) B4404743
theorem B1957663 : Blo 1957435 1957663 := bstep (se 1 (by rfl) ⟨1468247, by rfl⟩ : syracuseStep 1957663 = 2936495) B2936495
theorem B2936501 : Blo 1957435 2936501 := bbase (se 5 (by rfl) ⟨137648, by rfl⟩ : syracuseStep 2936501 = 275297) (by norm_num)
theorem B1957667 : Blo 1957435 1957667 := bstep (se 1 (by rfl) ⟨1468250, by rfl⟩ : syracuseStep 1957667 = 2936501) B2936501
theorem B4955357 : Blo 1957435 4955357 := bbase (se 3 (by rfl) ⟨929129, by rfl⟩ : syracuseStep 4955357 = 1858259) (by norm_num)
theorem B3303571 : Blo 1957435 3303571 := bstep (se 1 (by rfl) ⟨2477678, by rfl⟩ : syracuseStep 3303571 = 4955357) B4955357
theorem B4404761 : Blo 1957435 4404761 := bstep (se 2 (by rfl) ⟨1651785, by rfl⟩ : syracuseStep 4404761 = 3303571) B3303571
theorem B2936507 : Blo 1957435 2936507 := bstep (se 1 (by rfl) ⟨2202380, by rfl⟩ : syracuseStep 2936507 = 4404761) B4404761
theorem B1957671 : Blo 1957435 1957671 := bstep (se 1 (by rfl) ⟨1468253, by rfl⟩ : syracuseStep 1957671 = 2936507) B2936507
theorem B2202385 : Blo 1957435 2202385 := bbase (se 2 (by rfl) ⟨825894, by rfl⟩ : syracuseStep 2202385 = 1651789) (by norm_num)
theorem B2936513 : Blo 1957435 2936513 := bstep (se 2 (by rfl) ⟨1101192, by rfl⟩ : syracuseStep 2936513 = 2202385) B2202385
theorem B1957675 : Blo 1957435 1957675 := bstep (se 1 (by rfl) ⟨1468256, by rfl⟩ : syracuseStep 1957675 = 2936513) B2936513
theorem B3716533 : Blo 1957435 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B4955377 : Blo 1957435 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B6607169 : Blo 1957435 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B4404779 : Blo 1957435 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B2936519 : Blo 1957435 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B1957679 : Blo 1957435 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B2936525 : Blo 1957435 2936525 := bbase (se 3 (by rfl) ⟨550598, by rfl⟩ : syracuseStep 2936525 = 1101197) (by norm_num)
theorem B1957683 : Blo 1957435 1957683 := bstep (se 1 (by rfl) ⟨1468262, by rfl⟩ : syracuseStep 1957683 = 2936525) B2936525
theorem B4404797 : Blo 1957435 4404797 := bbase (se 3 (by rfl) ⟨825899, by rfl⟩ : syracuseStep 4404797 = 1651799) (by norm_num)
theorem B2936531 : Blo 1957435 2936531 := bstep (se 1 (by rfl) ⟨2202398, by rfl⟩ : syracuseStep 2936531 = 4404797) B4404797
theorem B1957687 : Blo 1957435 1957687 := bstep (se 1 (by rfl) ⟨1468265, by rfl⟩ : syracuseStep 1957687 = 2936531) B2936531
theorem B3303605 : Blo 1957435 3303605 := bbase (se 5 (by rfl) ⟨154856, by rfl⟩ : syracuseStep 3303605 = 309713) (by norm_num)
theorem B2202403 : Blo 1957435 2202403 := bstep (se 1 (by rfl) ⟨1651802, by rfl⟩ : syracuseStep 2202403 = 3303605) B3303605
theorem B2936537 : Blo 1957435 2936537 := bstep (se 2 (by rfl) ⟨1101201, by rfl⟩ : syracuseStep 2936537 = 2202403) B2202403
theorem B1957691 : Blo 1957435 1957691 := bstep (se 1 (by rfl) ⟨1468268, by rfl⟩ : syracuseStep 1957691 = 2936537) B2936537
theorem B3968813 : Blo 1957435 3968813 := bbase (se 3 (by rfl) ⟨744152, by rfl⟩ : syracuseStep 3968813 = 1488305) (by norm_num)
theorem B2645875 : Blo 1957435 2645875 := bstep (se 1 (by rfl) ⟨1984406, by rfl⟩ : syracuseStep 2645875 = 3968813) B3968813
theorem B3527833 : Blo 1957435 3527833 := bstep (se 2 (by rfl) ⟨1322937, by rfl⟩ : syracuseStep 3527833 = 2645875) B2645875
theorem B4703777 : Blo 1957435 4703777 := bstep (se 2 (by rfl) ⟨1763916, by rfl⟩ : syracuseStep 4703777 = 3527833) B3527833
theorem B3135851 : Blo 1957435 3135851 := bstep (se 1 (by rfl) ⟨2351888, by rfl⟩ : syracuseStep 3135851 = 4703777) B4703777
theorem B2090567 : Blo 1957435 2090567 := bstep (se 1 (by rfl) ⟨1567925, by rfl⟩ : syracuseStep 2090567 = 3135851) B3135851
theorem B5574845 : Blo 1957435 5574845 := bstep (se 3 (by rfl) ⟨1045283, by rfl⟩ : syracuseStep 5574845 = 2090567) B2090567
theorem B14866253 : Blo 1957435 14866253 := bstep (se 3 (by rfl) ⟨2787422, by rfl⟩ : syracuseStep 14866253 = 5574845) B5574845
theorem B9910835 : Blo 1957435 9910835 := bstep (se 1 (by rfl) ⟨7433126, by rfl⟩ : syracuseStep 9910835 = 14866253) B14866253
theorem B6607223 : Blo 1957435 6607223 := bstep (se 1 (by rfl) ⟨4955417, by rfl⟩ : syracuseStep 6607223 = 9910835) B9910835
theorem B4404815 : Blo 1957435 4404815 := bstep (se 1 (by rfl) ⟨3303611, by rfl⟩ : syracuseStep 4404815 = 6607223) B6607223
theorem B2936543 : Blo 1957435 2936543 := bstep (se 1 (by rfl) ⟨2202407, by rfl⟩ : syracuseStep 2936543 = 4404815) B4404815
theorem B1957695 : Blo 1957435 1957695 := bstep (se 1 (by rfl) ⟨1468271, by rfl⟩ : syracuseStep 1957695 = 2936543) B2936543
theorem B2936549 : Blo 1957435 2936549 := bbase (se 4 (by rfl) ⟨275301, by rfl⟩ : syracuseStep 2936549 = 550603) (by norm_num)
theorem B1957699 : Blo 1957435 1957699 := bstep (se 1 (by rfl) ⟨1468274, by rfl⟩ : syracuseStep 1957699 = 2936549) B2936549
theorem B5574869 : Blo 1957435 5574869 := bbase (se 7 (by rfl) ⟨65330, by rfl⟩ : syracuseStep 5574869 = 130661) (by norm_num)
theorem B3716579 : Blo 1957435 3716579 := bstep (se 1 (by rfl) ⟨2787434, by rfl⟩ : syracuseStep 3716579 = 5574869) B5574869
theorem B2477719 : Blo 1957435 2477719 := bstep (se 1 (by rfl) ⟨1858289, by rfl⟩ : syracuseStep 2477719 = 3716579) B3716579
theorem B3303625 : Blo 1957435 3303625 := bstep (se 2 (by rfl) ⟨1238859, by rfl⟩ : syracuseStep 3303625 = 2477719) B2477719
theorem B4404833 : Blo 1957435 4404833 := bstep (se 2 (by rfl) ⟨1651812, by rfl⟩ : syracuseStep 4404833 = 3303625) B3303625
theorem B2936555 : Blo 1957435 2936555 := bstep (se 1 (by rfl) ⟨2202416, by rfl⟩ : syracuseStep 2936555 = 4404833) B4404833
theorem B1957703 : Blo 1957435 1957703 := bstep (se 1 (by rfl) ⟨1468277, by rfl⟩ : syracuseStep 1957703 = 2936555) B2936555
theorem B2202421 : Blo 1957435 2202421 := bbase (se 5 (by rfl) ⟨103238, by rfl⟩ : syracuseStep 2202421 = 206477) (by norm_num)
theorem B2936561 : Blo 1957435 2936561 := bstep (se 2 (by rfl) ⟨1101210, by rfl⟩ : syracuseStep 2936561 = 2202421) B2202421
theorem B1957707 : Blo 1957435 1957707 := bstep (se 1 (by rfl) ⟨1468280, by rfl⟩ : syracuseStep 1957707 = 2936561) B2936561
theorem B2477729 : Blo 1957435 2477729 := bbase (se 2 (by rfl) ⟨929148, by rfl⟩ : syracuseStep 2477729 = 1858297) (by norm_num)
theorem B6607277 : Blo 1957435 6607277 := bstep (se 3 (by rfl) ⟨1238864, by rfl⟩ : syracuseStep 6607277 = 2477729) B2477729
theorem B4404851 : Blo 1957435 4404851 := bstep (se 1 (by rfl) ⟨3303638, by rfl⟩ : syracuseStep 4404851 = 6607277) B6607277
theorem B2936567 : Blo 1957435 2936567 := bstep (se 1 (by rfl) ⟨2202425, by rfl⟩ : syracuseStep 2936567 = 4404851) B4404851
theorem B1957711 : Blo 1957435 1957711 := bstep (se 1 (by rfl) ⟨1468283, by rfl⟩ : syracuseStep 1957711 = 2936567) B2936567
theorem B2936573 : Blo 1957435 2936573 := bbase (se 3 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 2936573 = 1101215) (by norm_num)
theorem B1957715 : Blo 1957435 1957715 := bstep (se 1 (by rfl) ⟨1468286, by rfl⟩ : syracuseStep 1957715 = 2936573) B2936573
theorem B4404869 : Blo 1957435 4404869 := bbase (se 4 (by rfl) ⟨412956, by rfl⟩ : syracuseStep 4404869 = 825913) (by norm_num)
theorem B2936579 : Blo 1957435 2936579 := bstep (se 1 (by rfl) ⟨2202434, by rfl⟩ : syracuseStep 2936579 = 4404869) B4404869
theorem B1957719 : Blo 1957435 1957719 := bstep (se 1 (by rfl) ⟨1468289, by rfl⟩ : syracuseStep 1957719 = 2936579) B2936579
theorem B4703845 : Blo 1957435 4703845 := bbase (se 4 (by rfl) ⟨440985, by rfl⟩ : syracuseStep 4703845 = 881971) (by norm_num)
theorem B6271793 : Blo 1957435 6271793 := bstep (se 2 (by rfl) ⟨2351922, by rfl⟩ : syracuseStep 6271793 = 4703845) B4703845
theorem B4181195 : Blo 1957435 4181195 := bstep (se 1 (by rfl) ⟨3135896, by rfl⟩ : syracuseStep 4181195 = 6271793) B6271793
theorem B2787463 : Blo 1957435 2787463 := bstep (se 1 (by rfl) ⟨2090597, by rfl⟩ : syracuseStep 2787463 = 4181195) B4181195
theorem B3716617 : Blo 1957435 3716617 := bstep (se 2 (by rfl) ⟨1393731, by rfl⟩ : syracuseStep 3716617 = 2787463) B2787463
theorem B4955489 : Blo 1957435 4955489 := bstep (se 2 (by rfl) ⟨1858308, by rfl⟩ : syracuseStep 4955489 = 3716617) B3716617
theorem B3303659 : Blo 1957435 3303659 := bstep (se 1 (by rfl) ⟨2477744, by rfl⟩ : syracuseStep 3303659 = 4955489) B4955489
theorem B2202439 : Blo 1957435 2202439 := bstep (se 1 (by rfl) ⟨1651829, by rfl⟩ : syracuseStep 2202439 = 3303659) B3303659
theorem B2936585 : Blo 1957435 2936585 := bstep (se 2 (by rfl) ⟨1101219, by rfl⟩ : syracuseStep 2936585 = 2202439) B2202439
theorem B1957723 : Blo 1957435 1957723 := bstep (se 1 (by rfl) ⟨1468292, by rfl⟩ : syracuseStep 1957723 = 2936585) B2936585
theorem B9910997 : Blo 1957435 9910997 := bbase (se 7 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 9910997 = 232289) (by norm_num)
theorem B6607331 : Blo 1957435 6607331 := bstep (se 1 (by rfl) ⟨4955498, by rfl⟩ : syracuseStep 6607331 = 9910997) B9910997
theorem B4404887 : Blo 1957435 4404887 := bstep (se 1 (by rfl) ⟨3303665, by rfl⟩ : syracuseStep 4404887 = 6607331) B6607331
theorem B2936591 : Blo 1957435 2936591 := bstep (se 1 (by rfl) ⟨2202443, by rfl⟩ : syracuseStep 2936591 = 4404887) B4404887
theorem B1957727 : Blo 1957435 1957727 := bstep (se 1 (by rfl) ⟨1468295, by rfl⟩ : syracuseStep 1957727 = 2936591) B2936591
theorem B2936597 : Blo 1957435 2936597 := bbase (se 6 (by rfl) ⟨68826, by rfl⟩ : syracuseStep 2936597 = 137653) (by norm_num)
theorem B1957731 : Blo 1957435 1957731 := bstep (se 1 (by rfl) ⟨1468298, by rfl⟩ : syracuseStep 1957731 = 2936597) B2936597
theorem B10046261 : Blo 1957435 10046261 := bbase (se 5 (by rfl) ⟨470918, by rfl⟩ : syracuseStep 10046261 = 941837) (by norm_num)
theorem B6697507 : Blo 1957435 6697507 := bstep (se 1 (by rfl) ⟨5023130, by rfl⟩ : syracuseStep 6697507 = 10046261) B10046261
theorem B8930009 : Blo 1957435 8930009 := bstep (se 2 (by rfl) ⟨3348753, by rfl⟩ : syracuseStep 8930009 = 6697507) B6697507
theorem B5953339 : Blo 1957435 5953339 := bstep (se 1 (by rfl) ⟨4465004, by rfl⟩ : syracuseStep 5953339 = 8930009) B8930009
theorem B7937785 : Blo 1957435 7937785 := bstep (se 2 (by rfl) ⟨2976669, by rfl⟩ : syracuseStep 7937785 = 5953339) B5953339
theorem B10583713 : Blo 1957435 10583713 := bstep (se 2 (by rfl) ⟨3968892, by rfl⟩ : syracuseStep 10583713 = 7937785) B7937785
theorem B56446469 : Blo 1957435 56446469 := bstep (se 4 (by rfl) ⟨5291856, by rfl⟩ : syracuseStep 56446469 = 10583713) B10583713
theorem B37630979 : Blo 1957435 37630979 := bstep (se 1 (by rfl) ⟨28223234, by rfl⟩ : syracuseStep 37630979 = 56446469) B56446469
theorem B25087319 : Blo 1957435 25087319 := bstep (se 1 (by rfl) ⟨18815489, by rfl⟩ : syracuseStep 25087319 = 37630979) B37630979
theorem B16724879 : Blo 1957435 16724879 := bstep (se 1 (by rfl) ⟨12543659, by rfl⟩ : syracuseStep 16724879 = 25087319) B25087319
theorem B11149919 : Blo 1957435 11149919 := bstep (se 1 (by rfl) ⟨8362439, by rfl⟩ : syracuseStep 11149919 = 16724879) B16724879
theorem B7433279 : Blo 1957435 7433279 := bstep (se 1 (by rfl) ⟨5574959, by rfl⟩ : syracuseStep 7433279 = 11149919) B11149919
theorem B4955519 : Blo 1957435 4955519 := bstep (se 1 (by rfl) ⟨3716639, by rfl⟩ : syracuseStep 4955519 = 7433279) B7433279
theorem B3303679 : Blo 1957435 3303679 := bstep (se 1 (by rfl) ⟨2477759, by rfl⟩ : syracuseStep 3303679 = 4955519) B4955519
theorem B4404905 : Blo 1957435 4404905 := bstep (se 2 (by rfl) ⟨1651839, by rfl⟩ : syracuseStep 4404905 = 3303679) B3303679
theorem B2936603 : Blo 1957435 2936603 := bstep (se 1 (by rfl) ⟨2202452, by rfl⟩ : syracuseStep 2936603 = 4404905) B4404905
theorem B1957735 : Blo 1957435 1957735 := bstep (se 1 (by rfl) ⟨1468301, by rfl⟩ : syracuseStep 1957735 = 2936603) B2936603
theorem B2202457 : Blo 1957435 2202457 := bbase (se 2 (by rfl) ⟨825921, by rfl⟩ : syracuseStep 2202457 = 1651843) (by norm_num)
theorem B2936609 : Blo 1957435 2936609 := bstep (se 2 (by rfl) ⟨1101228, by rfl⟩ : syracuseStep 2936609 = 2202457) B2202457
theorem B1957739 : Blo 1957435 1957739 := bstep (se 1 (by rfl) ⟨1468304, by rfl⟩ : syracuseStep 1957739 = 2936609) B2936609
theorem B4181237 : Blo 1957435 4181237 := bbase (se 5 (by rfl) ⟨195995, by rfl⟩ : syracuseStep 4181237 = 391991) (by norm_num)
theorem B2787491 : Blo 1957435 2787491 := bstep (se 1 (by rfl) ⟨2090618, by rfl⟩ : syracuseStep 2787491 = 4181237) B4181237
theorem B7433309 : Blo 1957435 7433309 := bstep (se 3 (by rfl) ⟨1393745, by rfl⟩ : syracuseStep 7433309 = 2787491) B2787491
theorem B4955539 : Blo 1957435 4955539 := bstep (se 1 (by rfl) ⟨3716654, by rfl⟩ : syracuseStep 4955539 = 7433309) B7433309
theorem B6607385 : Blo 1957435 6607385 := bstep (se 2 (by rfl) ⟨2477769, by rfl⟩ : syracuseStep 6607385 = 4955539) B4955539
theorem B4404923 : Blo 1957435 4404923 := bstep (se 1 (by rfl) ⟨3303692, by rfl⟩ : syracuseStep 4404923 = 6607385) B6607385
theorem B2936615 : Blo 1957435 2936615 := bstep (se 1 (by rfl) ⟨2202461, by rfl⟩ : syracuseStep 2936615 = 4404923) B4404923
theorem B1957743 : Blo 1957435 1957743 := bstep (se 1 (by rfl) ⟨1468307, by rfl⟩ : syracuseStep 1957743 = 2936615) B2936615
theorem B2936621 : Blo 1957435 2936621 := bbase (se 3 (by rfl) ⟨550616, by rfl⟩ : syracuseStep 2936621 = 1101233) (by norm_num)
theorem B1957747 : Blo 1957435 1957747 := bstep (se 1 (by rfl) ⟨1468310, by rfl⟩ : syracuseStep 1957747 = 2936621) B2936621
theorem B4404941 : Blo 1957435 4404941 := bbase (se 3 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 4404941 = 1651853) (by norm_num)
theorem B2936627 : Blo 1957435 2936627 := bstep (se 1 (by rfl) ⟨2202470, by rfl⟩ : syracuseStep 2936627 = 4404941) B4404941
theorem B1957751 : Blo 1957435 1957751 := bstep (se 1 (by rfl) ⟨1468313, by rfl⟩ : syracuseStep 1957751 = 2936627) B2936627
theorem B2477785 : Blo 1957435 2477785 := bbase (se 2 (by rfl) ⟨929169, by rfl⟩ : syracuseStep 2477785 = 1858339) (by norm_num)
theorem B3303713 : Blo 1957435 3303713 := bstep (se 2 (by rfl) ⟨1238892, by rfl⟩ : syracuseStep 3303713 = 2477785) B2477785
theorem B2202475 : Blo 1957435 2202475 := bstep (se 1 (by rfl) ⟨1651856, by rfl⟩ : syracuseStep 2202475 = 3303713) B3303713
theorem B2936633 : Blo 1957435 2936633 := bstep (se 2 (by rfl) ⟨1101237, by rfl⟩ : syracuseStep 2936633 = 2202475) B2202475
theorem B1957755 : Blo 1957435 1957755 := bstep (se 1 (by rfl) ⟨1468316, by rfl⟩ : syracuseStep 1957755 = 2936633) B2936633
theorem B2351965 : Blo 1957435 2351965 := bbase (se 3 (by rfl) ⟨440993, by rfl⟩ : syracuseStep 2351965 = 881987) (by norm_num)
theorem B3135953 : Blo 1957435 3135953 := bstep (se 2 (by rfl) ⟨1175982, by rfl⟩ : syracuseStep 3135953 = 2351965) B2351965
theorem B8362541 : Blo 1957435 8362541 := bstep (se 3 (by rfl) ⟨1567976, by rfl⟩ : syracuseStep 8362541 = 3135953) B3135953
theorem B22300109 : Blo 1957435 22300109 := bstep (se 3 (by rfl) ⟨4181270, by rfl⟩ : syracuseStep 22300109 = 8362541) B8362541
theorem B14866739 : Blo 1957435 14866739 := bstep (se 1 (by rfl) ⟨11150054, by rfl⟩ : syracuseStep 14866739 = 22300109) B22300109
theorem B9911159 : Blo 1957435 9911159 := bstep (se 1 (by rfl) ⟨7433369, by rfl⟩ : syracuseStep 9911159 = 14866739) B14866739
theorem B6607439 : Blo 1957435 6607439 := bstep (se 1 (by rfl) ⟨4955579, by rfl⟩ : syracuseStep 6607439 = 9911159) B9911159
theorem B4404959 : Blo 1957435 4404959 := bstep (se 1 (by rfl) ⟨3303719, by rfl⟩ : syracuseStep 4404959 = 6607439) B6607439
theorem B2936639 : Blo 1957435 2936639 := bstep (se 1 (by rfl) ⟨2202479, by rfl⟩ : syracuseStep 2936639 = 4404959) B4404959
theorem B1957759 : Blo 1957435 1957759 := bstep (se 1 (by rfl) ⟨1468319, by rfl⟩ : syracuseStep 1957759 = 2936639) B2936639
theorem B2936645 : Blo 1957435 2936645 := bbase (se 4 (by rfl) ⟨275310, by rfl⟩ : syracuseStep 2936645 = 550621) (by norm_num)
theorem B1957763 : Blo 1957435 1957763 := bstep (se 1 (by rfl) ⟨1468322, by rfl⟩ : syracuseStep 1957763 = 2936645) B2936645
theorem B3303733 : Blo 1957435 3303733 := bbase (se 5 (by rfl) ⟨154862, by rfl⟩ : syracuseStep 3303733 = 309725) (by norm_num)
theorem B4404977 : Blo 1957435 4404977 := bstep (se 2 (by rfl) ⟨1651866, by rfl⟩ : syracuseStep 4404977 = 3303733) B3303733
theorem B2936651 : Blo 1957435 2936651 := bstep (se 1 (by rfl) ⟨2202488, by rfl⟩ : syracuseStep 2936651 = 4404977) B4404977
theorem B1957767 : Blo 1957435 1957767 := bstep (se 1 (by rfl) ⟨1468325, by rfl⟩ : syracuseStep 1957767 = 2936651) B2936651
theorem B2202493 : Blo 1957435 2202493 := bbase (se 3 (by rfl) ⟨412967, by rfl⟩ : syracuseStep 2202493 = 825935) (by norm_num)
theorem B2936657 : Blo 1957435 2936657 := bstep (se 2 (by rfl) ⟨1101246, by rfl⟩ : syracuseStep 2936657 = 2202493) B2202493
theorem B1957771 : Blo 1957435 1957771 := bstep (se 1 (by rfl) ⟨1468328, by rfl⟩ : syracuseStep 1957771 = 2936657) B2936657
theorem B6607493 : Blo 1957435 6607493 := bbase (se 4 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 6607493 = 1238905) (by norm_num)
theorem B4404995 : Blo 1957435 4404995 := bstep (se 1 (by rfl) ⟨3303746, by rfl⟩ : syracuseStep 4404995 = 6607493) B6607493
theorem B2936663 : Blo 1957435 2936663 := bstep (se 1 (by rfl) ⟨2202497, by rfl⟩ : syracuseStep 2936663 = 4404995) B4404995
theorem B1957775 : Blo 1957435 1957775 := bstep (se 1 (by rfl) ⟨1468331, by rfl⟩ : syracuseStep 1957775 = 2936663) B2936663
theorem B2936669 : Blo 1957435 2936669 := bbase (se 3 (by rfl) ⟨550625, by rfl⟩ : syracuseStep 2936669 = 1101251) (by norm_num)
theorem B1957779 : Blo 1957435 1957779 := bstep (se 1 (by rfl) ⟨1468334, by rfl⟩ : syracuseStep 1957779 = 2936669) B2936669
theorem B4405013 : Blo 1957435 4405013 := bbase (se 6 (by rfl) ⟨103242, by rfl⟩ : syracuseStep 4405013 = 206485) (by norm_num)
theorem B2936675 : Blo 1957435 2936675 := bstep (se 1 (by rfl) ⟨2202506, by rfl⟩ : syracuseStep 2936675 = 4405013) B4405013
theorem B1957783 : Blo 1957435 1957783 := bstep (se 1 (by rfl) ⟨1468337, by rfl⟩ : syracuseStep 1957783 = 2936675) B2936675
theorem B7433477 : Blo 1957435 7433477 := bbase (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) (by norm_num)
theorem B4955651 : Blo 1957435 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B3303767 : Blo 1957435 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B2202511 : Blo 1957435 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B2936681 : Blo 1957435 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B1957787 : Blo 1957435 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B4465133 : Blo 1957435 4465133 := bbase (se 3 (by rfl) ⟨837212, by rfl⟩ : syracuseStep 4465133 = 1674425) (by norm_num)
theorem B2976755 : Blo 1957435 2976755 := bstep (se 1 (by rfl) ⟨2232566, by rfl⟩ : syracuseStep 2976755 = 4465133) B4465133
theorem B7938013 : Blo 1957435 7938013 := bstep (se 3 (by rfl) ⟨1488377, by rfl⟩ : syracuseStep 7938013 = 2976755) B2976755
theorem B10584017 : Blo 1957435 10584017 := bstep (se 2 (by rfl) ⟨3969006, by rfl⟩ : syracuseStep 10584017 = 7938013) B7938013
theorem B7056011 : Blo 1957435 7056011 := bstep (se 1 (by rfl) ⟨5292008, by rfl⟩ : syracuseStep 7056011 = 10584017) B10584017
theorem B4704007 : Blo 1957435 4704007 := bstep (se 1 (by rfl) ⟨3528005, by rfl⟩ : syracuseStep 4704007 = 7056011) B7056011
theorem B6272009 : Blo 1957435 6272009 := bstep (se 2 (by rfl) ⟨2352003, by rfl⟩ : syracuseStep 6272009 = 4704007) B4704007
theorem B4181339 : Blo 1957435 4181339 := bstep (se 1 (by rfl) ⟨3136004, by rfl⟩ : syracuseStep 4181339 = 6272009) B6272009
theorem B11150237 : Blo 1957435 11150237 := bstep (se 3 (by rfl) ⟨2090669, by rfl⟩ : syracuseStep 11150237 = 4181339) B4181339
theorem B7433491 : Blo 1957435 7433491 := bstep (se 1 (by rfl) ⟨5575118, by rfl⟩ : syracuseStep 7433491 = 11150237) B11150237
theorem B9911321 : Blo 1957435 9911321 := bstep (se 2 (by rfl) ⟨3716745, by rfl⟩ : syracuseStep 9911321 = 7433491) B7433491
theorem B6607547 : Blo 1957435 6607547 := bstep (se 1 (by rfl) ⟨4955660, by rfl⟩ : syracuseStep 6607547 = 9911321) B9911321
theorem B4405031 : Blo 1957435 4405031 := bstep (se 1 (by rfl) ⟨3303773, by rfl⟩ : syracuseStep 4405031 = 6607547) B6607547
theorem B2936687 : Blo 1957435 2936687 := bstep (se 1 (by rfl) ⟨2202515, by rfl⟩ : syracuseStep 2936687 = 4405031) B4405031
theorem B1957791 : Blo 1957435 1957791 := bstep (se 1 (by rfl) ⟨1468343, by rfl⟩ : syracuseStep 1957791 = 2936687) B2936687
theorem B2936693 : Blo 1957435 2936693 := bbase (se 5 (by rfl) ⟨137657, by rfl⟩ : syracuseStep 2936693 = 275315) (by norm_num)
theorem B1957795 : Blo 1957435 1957795 := bstep (se 1 (by rfl) ⟨1468346, by rfl⟩ : syracuseStep 1957795 = 2936693) B2936693
theorem B4181357 : Blo 1957435 4181357 := bbase (se 3 (by rfl) ⟨784004, by rfl⟩ : syracuseStep 4181357 = 1568009) (by norm_num)
theorem B2787571 : Blo 1957435 2787571 := bstep (se 1 (by rfl) ⟨2090678, by rfl⟩ : syracuseStep 2787571 = 4181357) B4181357
theorem B3716761 : Blo 1957435 3716761 := bstep (se 2 (by rfl) ⟨1393785, by rfl⟩ : syracuseStep 3716761 = 2787571) B2787571
theorem B4955681 : Blo 1957435 4955681 := bstep (se 2 (by rfl) ⟨1858380, by rfl⟩ : syracuseStep 4955681 = 3716761) B3716761
theorem B3303787 : Blo 1957435 3303787 := bstep (se 1 (by rfl) ⟨2477840, by rfl⟩ : syracuseStep 3303787 = 4955681) B4955681
theorem B4405049 : Blo 1957435 4405049 := bstep (se 2 (by rfl) ⟨1651893, by rfl⟩ : syracuseStep 4405049 = 3303787) B3303787
theorem B2936699 : Blo 1957435 2936699 := bstep (se 1 (by rfl) ⟨2202524, by rfl⟩ : syracuseStep 2936699 = 4405049) B4405049
theorem B1957799 : Blo 1957435 1957799 := bstep (se 1 (by rfl) ⟨1468349, by rfl⟩ : syracuseStep 1957799 = 2936699) B2936699
theorem B2202529 : Blo 1957435 2202529 := bbase (se 2 (by rfl) ⟨825948, by rfl⟩ : syracuseStep 2202529 = 1651897) (by norm_num)
theorem B2936705 : Blo 1957435 2936705 := bstep (se 2 (by rfl) ⟨1101264, by rfl⟩ : syracuseStep 2936705 = 2202529) B2202529
theorem B1957803 : Blo 1957435 1957803 := bstep (se 1 (by rfl) ⟨1468352, by rfl⟩ : syracuseStep 1957803 = 2936705) B2936705
theorem B4955701 : Blo 1957435 4955701 := bbase (se 5 (by rfl) ⟨232298, by rfl⟩ : syracuseStep 4955701 = 464597) (by norm_num)
theorem B6607601 : Blo 1957435 6607601 := bstep (se 2 (by rfl) ⟨2477850, by rfl⟩ : syracuseStep 6607601 = 4955701) B4955701
theorem B4405067 : Blo 1957435 4405067 := bstep (se 1 (by rfl) ⟨3303800, by rfl⟩ : syracuseStep 4405067 = 6607601) B6607601
theorem B2936711 : Blo 1957435 2936711 := bstep (se 1 (by rfl) ⟨2202533, by rfl⟩ : syracuseStep 2936711 = 4405067) B4405067
theorem B1957807 : Blo 1957435 1957807 := bstep (se 1 (by rfl) ⟨1468355, by rfl⟩ : syracuseStep 1957807 = 2936711) B2936711
theorem B2936717 : Blo 1957435 2936717 := bbase (se 3 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 2936717 = 1101269) (by norm_num)
theorem B1957811 : Blo 1957435 1957811 := bstep (se 1 (by rfl) ⟨1468358, by rfl⟩ : syracuseStep 1957811 = 2936717) B2936717
theorem B4405085 : Blo 1957435 4405085 := bbase (se 3 (by rfl) ⟨825953, by rfl⟩ : syracuseStep 4405085 = 1651907) (by norm_num)
theorem B2936723 : Blo 1957435 2936723 := bstep (se 1 (by rfl) ⟨2202542, by rfl⟩ : syracuseStep 2936723 = 4405085) B4405085
theorem B1957815 : Blo 1957435 1957815 := bstep (se 1 (by rfl) ⟨1468361, by rfl⟩ : syracuseStep 1957815 = 2936723) B2936723
theorem B3303821 : Blo 1957435 3303821 := bbase (se 3 (by rfl) ⟨619466, by rfl⟩ : syracuseStep 3303821 = 1238933) (by norm_num)
theorem B2202547 : Blo 1957435 2202547 := bstep (se 1 (by rfl) ⟨1651910, by rfl⟩ : syracuseStep 2202547 = 3303821) B3303821
theorem B2936729 : Blo 1957435 2936729 := bstep (se 2 (by rfl) ⟨1101273, by rfl⟩ : syracuseStep 2936729 = 2202547) B2202547
theorem B1957819 : Blo 1957435 1957819 := bstep (se 1 (by rfl) ⟨1468364, by rfl⟩ : syracuseStep 1957819 = 2936729) B2936729
theorem B6357685 : Blo 1957435 6357685 := bbase (se 5 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 6357685 = 596033) (by norm_num)
theorem B8476913 : Blo 1957435 8476913 := bstep (se 2 (by rfl) ⟨3178842, by rfl⟩ : syracuseStep 8476913 = 6357685) B6357685
theorem B22605101 : Blo 1957435 22605101 := bstep (se 3 (by rfl) ⟨4238456, by rfl⟩ : syracuseStep 22605101 = 8476913) B8476913
theorem B15070067 : Blo 1957435 15070067 := bstep (se 1 (by rfl) ⟨11302550, by rfl⟩ : syracuseStep 15070067 = 22605101) B22605101
theorem B10046711 : Blo 1957435 10046711 := bstep (se 1 (by rfl) ⟨7535033, by rfl⟩ : syracuseStep 10046711 = 15070067) B15070067
theorem B26791229 : Blo 1957435 26791229 := bstep (se 3 (by rfl) ⟨5023355, by rfl⟩ : syracuseStep 26791229 = 10046711) B10046711
theorem B17860819 : Blo 1957435 17860819 := bstep (se 1 (by rfl) ⟨13395614, by rfl⟩ : syracuseStep 17860819 = 26791229) B26791229
theorem B23814425 : Blo 1957435 23814425 := bstep (se 2 (by rfl) ⟨8930409, by rfl⟩ : syracuseStep 23814425 = 17860819) B17860819
theorem B15876283 : Blo 1957435 15876283 := bstep (se 1 (by rfl) ⟨11907212, by rfl⟩ : syracuseStep 15876283 = 23814425) B23814425
theorem B21168377 : Blo 1957435 21168377 := bstep (se 2 (by rfl) ⟨7938141, by rfl⟩ : syracuseStep 21168377 = 15876283) B15876283
theorem B14112251 : Blo 1957435 14112251 := bstep (se 1 (by rfl) ⟨10584188, by rfl⟩ : syracuseStep 14112251 = 21168377) B21168377
theorem B9408167 : Blo 1957435 9408167 := bstep (se 1 (by rfl) ⟨7056125, by rfl⟩ : syracuseStep 9408167 = 14112251) B14112251
theorem B6272111 : Blo 1957435 6272111 := bstep (se 1 (by rfl) ⟨4704083, by rfl⟩ : syracuseStep 6272111 = 9408167) B9408167
theorem B16725629 : Blo 1957435 16725629 := bstep (se 3 (by rfl) ⟨3136055, by rfl⟩ : syracuseStep 16725629 = 6272111) B6272111
theorem B11150419 : Blo 1957435 11150419 := bstep (se 1 (by rfl) ⟨8362814, by rfl⟩ : syracuseStep 11150419 = 16725629) B16725629
theorem B14867225 : Blo 1957435 14867225 := bstep (se 2 (by rfl) ⟨5575209, by rfl⟩ : syracuseStep 14867225 = 11150419) B11150419
theorem B9911483 : Blo 1957435 9911483 := bstep (se 1 (by rfl) ⟨7433612, by rfl⟩ : syracuseStep 9911483 = 14867225) B14867225
theorem B6607655 : Blo 1957435 6607655 := bstep (se 1 (by rfl) ⟨4955741, by rfl⟩ : syracuseStep 6607655 = 9911483) B9911483
theorem B4405103 : Blo 1957435 4405103 := bstep (se 1 (by rfl) ⟨3303827, by rfl⟩ : syracuseStep 4405103 = 6607655) B6607655
theorem B2936735 : Blo 1957435 2936735 := bstep (se 1 (by rfl) ⟨2202551, by rfl⟩ : syracuseStep 2936735 = 4405103) B4405103
theorem B1957823 : Blo 1957435 1957823 := bstep (se 1 (by rfl) ⟨1468367, by rfl⟩ : syracuseStep 1957823 = 2936735) B2936735
theorem B2936741 : Blo 1957435 2936741 := bbase (se 4 (by rfl) ⟨275319, by rfl⟩ : syracuseStep 2936741 = 550639) (by norm_num)
theorem B1957827 : Blo 1957435 1957827 := bstep (se 1 (by rfl) ⟨1468370, by rfl⟩ : syracuseStep 1957827 = 2936741) B2936741
theorem B2477881 : Blo 1957435 2477881 := bbase (se 2 (by rfl) ⟨929205, by rfl⟩ : syracuseStep 2477881 = 1858411) (by norm_num)
theorem B3303841 : Blo 1957435 3303841 := bstep (se 2 (by rfl) ⟨1238940, by rfl⟩ : syracuseStep 3303841 = 2477881) B2477881
theorem B4405121 : Blo 1957435 4405121 := bstep (se 2 (by rfl) ⟨1651920, by rfl⟩ : syracuseStep 4405121 = 3303841) B3303841
theorem B2936747 : Blo 1957435 2936747 := bstep (se 1 (by rfl) ⟨2202560, by rfl⟩ : syracuseStep 2936747 = 4405121) B4405121
theorem B1957831 : Blo 1957435 1957831 := bstep (se 1 (by rfl) ⟨1468373, by rfl⟩ : syracuseStep 1957831 = 2936747) B2936747
theorem B2202565 : Blo 1957435 2202565 := bbase (se 4 (by rfl) ⟨206490, by rfl⟩ : syracuseStep 2202565 = 412981) (by norm_num)
theorem B2936753 : Blo 1957435 2936753 := bstep (se 2 (by rfl) ⟨1101282, by rfl⟩ : syracuseStep 2936753 = 2202565) B2202565
theorem B1957835 : Blo 1957435 1957835 := bstep (se 1 (by rfl) ⟨1468376, by rfl⟩ : syracuseStep 1957835 = 2936753) B2936753
theorem B3716837 : Blo 1957435 3716837 := bbase (se 4 (by rfl) ⟨348453, by rfl⟩ : syracuseStep 3716837 = 696907) (by norm_num)
theorem B2477891 : Blo 1957435 2477891 := bstep (se 1 (by rfl) ⟨1858418, by rfl⟩ : syracuseStep 2477891 = 3716837) B3716837
theorem B6607709 : Blo 1957435 6607709 := bstep (se 3 (by rfl) ⟨1238945, by rfl⟩ : syracuseStep 6607709 = 2477891) B2477891
theorem B4405139 : Blo 1957435 4405139 := bstep (se 1 (by rfl) ⟨3303854, by rfl⟩ : syracuseStep 4405139 = 6607709) B6607709
theorem B2936759 : Blo 1957435 2936759 := bstep (se 1 (by rfl) ⟨2202569, by rfl⟩ : syracuseStep 2936759 = 4405139) B4405139
theorem B1957839 : Blo 1957435 1957839 := bstep (se 1 (by rfl) ⟨1468379, by rfl⟩ : syracuseStep 1957839 = 2936759) B2936759
theorem B2936765 : Blo 1957435 2936765 := bbase (se 3 (by rfl) ⟨550643, by rfl⟩ : syracuseStep 2936765 = 1101287) (by norm_num)
theorem B1957843 : Blo 1957435 1957843 := bstep (se 1 (by rfl) ⟨1468382, by rfl⟩ : syracuseStep 1957843 = 2936765) B2936765
theorem B4405157 : Blo 1957435 4405157 := bbase (se 4 (by rfl) ⟨412983, by rfl⟩ : syracuseStep 4405157 = 825967) (by norm_num)
theorem B2936771 : Blo 1957435 2936771 := bstep (se 1 (by rfl) ⟨2202578, by rfl⟩ : syracuseStep 2936771 = 4405157) B4405157
theorem B1957847 : Blo 1957435 1957847 := bstep (se 1 (by rfl) ⟨1468385, by rfl⟩ : syracuseStep 1957847 = 2936771) B2936771
theorem B4955813 : Blo 1957435 4955813 := bbase (se 4 (by rfl) ⟨464607, by rfl⟩ : syracuseStep 4955813 = 929215) (by norm_num)
theorem B3303875 : Blo 1957435 3303875 := bstep (se 1 (by rfl) ⟨2477906, by rfl⟩ : syracuseStep 3303875 = 4955813) B4955813
theorem B2202583 : Blo 1957435 2202583 := bstep (se 1 (by rfl) ⟨1651937, by rfl⟩ : syracuseStep 2202583 = 3303875) B3303875
theorem B2936777 : Blo 1957435 2936777 := bstep (se 2 (by rfl) ⟨1101291, by rfl⟩ : syracuseStep 2936777 = 2202583) B2202583
theorem B1957851 : Blo 1957435 1957851 := bstep (se 1 (by rfl) ⟨1468388, by rfl⟩ : syracuseStep 1957851 = 2936777) B2936777
theorem B5575301 : Blo 1957435 5575301 := bbase (se 4 (by rfl) ⟨522684, by rfl⟩ : syracuseStep 5575301 = 1045369) (by norm_num)
theorem B3716867 : Blo 1957435 3716867 := bstep (se 1 (by rfl) ⟨2787650, by rfl⟩ : syracuseStep 3716867 = 5575301) B5575301
theorem B9911645 : Blo 1957435 9911645 := bstep (se 3 (by rfl) ⟨1858433, by rfl⟩ : syracuseStep 9911645 = 3716867) B3716867
theorem B6607763 : Blo 1957435 6607763 := bstep (se 1 (by rfl) ⟨4955822, by rfl⟩ : syracuseStep 6607763 = 9911645) B9911645
theorem B4405175 : Blo 1957435 4405175 := bstep (se 1 (by rfl) ⟨3303881, by rfl⟩ : syracuseStep 4405175 = 6607763) B6607763
theorem B2936783 : Blo 1957435 2936783 := bstep (se 1 (by rfl) ⟨2202587, by rfl⟩ : syracuseStep 2936783 = 4405175) B4405175
theorem B1957855 : Blo 1957435 1957855 := bstep (se 1 (by rfl) ⟨1468391, by rfl⟩ : syracuseStep 1957855 = 2936783) B2936783
theorem B2936789 : Blo 1957435 2936789 := bbase (se 7 (by rfl) ⟨34415, by rfl⟩ : syracuseStep 2936789 = 68831) (by norm_num)
theorem B1957859 : Blo 1957435 1957859 := bstep (se 1 (by rfl) ⟨1468394, by rfl⟩ : syracuseStep 1957859 = 2936789) B2936789
theorem B7433765 : Blo 1957435 7433765 := bbase (se 4 (by rfl) ⟨696915, by rfl⟩ : syracuseStep 7433765 = 1393831) (by norm_num)
theorem B4955843 : Blo 1957435 4955843 := bstep (se 1 (by rfl) ⟨3716882, by rfl⟩ : syracuseStep 4955843 = 7433765) B7433765
theorem B3303895 : Blo 1957435 3303895 := bstep (se 1 (by rfl) ⟨2477921, by rfl⟩ : syracuseStep 3303895 = 4955843) B4955843
theorem B4405193 : Blo 1957435 4405193 := bstep (se 2 (by rfl) ⟨1651947, by rfl⟩ : syracuseStep 4405193 = 3303895) B3303895
theorem B2936795 : Blo 1957435 2936795 := bstep (se 1 (by rfl) ⟨2202596, by rfl⟩ : syracuseStep 2936795 = 4405193) B4405193
theorem B1957863 : Blo 1957435 1957863 := bstep (se 1 (by rfl) ⟨1468397, by rfl⟩ : syracuseStep 1957863 = 2936795) B2936795
theorem B2202601 : Blo 1957435 2202601 := bbase (se 2 (by rfl) ⟨825975, by rfl⟩ : syracuseStep 2202601 = 1651951) (by norm_num)
theorem B2936801 : Blo 1957435 2936801 := bstep (se 2 (by rfl) ⟨1101300, by rfl⟩ : syracuseStep 2936801 = 2202601) B2202601
theorem B1957867 : Blo 1957435 1957867 := bstep (se 1 (by rfl) ⟨1468400, by rfl⟩ : syracuseStep 1957867 = 2936801) B2936801
theorem B3136133 : Blo 1957435 3136133 := bbase (se 4 (by rfl) ⟨294012, by rfl⟩ : syracuseStep 3136133 = 588025) (by norm_num)
theorem B2090755 : Blo 1957435 2090755 := bstep (se 1 (by rfl) ⟨1568066, by rfl⟩ : syracuseStep 2090755 = 3136133) B3136133
theorem B11150693 : Blo 1957435 11150693 := bstep (se 4 (by rfl) ⟨1045377, by rfl⟩ : syracuseStep 11150693 = 2090755) B2090755
theorem B7433795 : Blo 1957435 7433795 := bstep (se 1 (by rfl) ⟨5575346, by rfl⟩ : syracuseStep 7433795 = 11150693) B11150693
theorem B4955863 : Blo 1957435 4955863 := bstep (se 1 (by rfl) ⟨3716897, by rfl⟩ : syracuseStep 4955863 = 7433795) B7433795
theorem B6607817 : Blo 1957435 6607817 := bstep (se 2 (by rfl) ⟨2477931, by rfl⟩ : syracuseStep 6607817 = 4955863) B4955863
theorem B4405211 : Blo 1957435 4405211 := bstep (se 1 (by rfl) ⟨3303908, by rfl⟩ : syracuseStep 4405211 = 6607817) B6607817
theorem B2936807 : Blo 1957435 2936807 := bstep (se 1 (by rfl) ⟨2202605, by rfl⟩ : syracuseStep 2936807 = 4405211) B4405211
theorem B1957871 : Blo 1957435 1957871 := bstep (se 1 (by rfl) ⟨1468403, by rfl⟩ : syracuseStep 1957871 = 2936807) B2936807
theorem B2936813 : Blo 1957435 2936813 := bbase (se 3 (by rfl) ⟨550652, by rfl⟩ : syracuseStep 2936813 = 1101305) (by norm_num)
theorem B1957875 : Blo 1957435 1957875 := bstep (se 1 (by rfl) ⟨1468406, by rfl⟩ : syracuseStep 1957875 = 2936813) B2936813
theorem B4405229 : Blo 1957435 4405229 := bbase (se 3 (by rfl) ⟨825980, by rfl⟩ : syracuseStep 4405229 = 1651961) (by norm_num)
theorem B2936819 : Blo 1957435 2936819 := bstep (se 1 (by rfl) ⟨2202614, by rfl⟩ : syracuseStep 2936819 = 4405229) B4405229
theorem B1957879 : Blo 1957435 1957879 := bstep (se 1 (by rfl) ⟨1468409, by rfl⟩ : syracuseStep 1957879 = 2936819) B2936819
theorem B3528173 : Blo 1957435 3528173 := bbase (se 3 (by rfl) ⟨661532, by rfl⟩ : syracuseStep 3528173 = 1323065) (by norm_num)
theorem B2352115 : Blo 1957435 2352115 := bstep (se 1 (by rfl) ⟨1764086, by rfl⟩ : syracuseStep 2352115 = 3528173) B3528173
theorem B3136153 : Blo 1957435 3136153 := bstep (se 2 (by rfl) ⟨1176057, by rfl⟩ : syracuseStep 3136153 = 2352115) B2352115
theorem B4181537 : Blo 1957435 4181537 := bstep (se 2 (by rfl) ⟨1568076, by rfl⟩ : syracuseStep 4181537 = 3136153) B3136153
theorem B2787691 : Blo 1957435 2787691 := bstep (se 1 (by rfl) ⟨2090768, by rfl⟩ : syracuseStep 2787691 = 4181537) B4181537
theorem B3716921 : Blo 1957435 3716921 := bstep (se 2 (by rfl) ⟨1393845, by rfl⟩ : syracuseStep 3716921 = 2787691) B2787691
theorem B2477947 : Blo 1957435 2477947 := bstep (se 1 (by rfl) ⟨1858460, by rfl⟩ : syracuseStep 2477947 = 3716921) B3716921
theorem B3303929 : Blo 1957435 3303929 := bstep (se 2 (by rfl) ⟨1238973, by rfl⟩ : syracuseStep 3303929 = 2477947) B2477947
theorem B2202619 : Blo 1957435 2202619 := bstep (se 1 (by rfl) ⟨1651964, by rfl⟩ : syracuseStep 2202619 = 3303929) B3303929
theorem B2936825 : Blo 1957435 2936825 := bstep (se 2 (by rfl) ⟨1101309, by rfl⟩ : syracuseStep 2936825 = 2202619) B2202619
theorem B1957883 : Blo 1957435 1957883 := bstep (se 1 (by rfl) ⟨1468412, by rfl⟩ : syracuseStep 1957883 = 2936825) B2936825
theorem B2546029 : Blo 1957435 2546029 := bbase (se 3 (by rfl) ⟨477380, by rfl⟩ : syracuseStep 2546029 = 954761) (by norm_num)
theorem B3394705 : Blo 1957435 3394705 := bstep (se 2 (by rfl) ⟨1273014, by rfl⟩ : syracuseStep 3394705 = 2546029) B2546029
theorem B4526273 : Blo 1957435 4526273 := bstep (se 2 (by rfl) ⟨1697352, by rfl⟩ : syracuseStep 4526273 = 3394705) B3394705
theorem B3017515 : Blo 1957435 3017515 := bstep (se 1 (by rfl) ⟨2263136, by rfl⟩ : syracuseStep 3017515 = 4526273) B4526273
theorem B4023353 : Blo 1957435 4023353 := bstep (se 2 (by rfl) ⟨1508757, by rfl⟩ : syracuseStep 4023353 = 3017515) B3017515
theorem B10728941 : Blo 1957435 10728941 := bstep (se 3 (by rfl) ⟨2011676, by rfl⟩ : syracuseStep 10728941 = 4023353) B4023353
theorem B114442037 : Blo 1957435 114442037 := bstep (se 5 (by rfl) ⟨5364470, by rfl⟩ : syracuseStep 114442037 = 10728941) B10728941
theorem B76294691 : Blo 1957435 76294691 := bstep (se 1 (by rfl) ⟨57221018, by rfl⟩ : syracuseStep 76294691 = 114442037) B114442037
theorem B813810037 : Blo 1957435 813810037 := bstep (se 5 (by rfl) ⟨38147345, by rfl⟩ : syracuseStep 813810037 = 76294691) B76294691
theorem B1085080049 : Blo 1957435 1085080049 := bstep (se 2 (by rfl) ⟨406905018, by rfl⟩ : syracuseStep 1085080049 = 813810037) B813810037
theorem B723386699 : Blo 1957435 723386699 := bstep (se 1 (by rfl) ⟨542540024, by rfl⟩ : syracuseStep 723386699 = 1085080049) B1085080049
theorem B482257799 : Blo 1957435 482257799 := bstep (se 1 (by rfl) ⟨361693349, by rfl⟩ : syracuseStep 482257799 = 723386699) B723386699
theorem B321505199 : Blo 1957435 321505199 := bstep (se 1 (by rfl) ⟨241128899, by rfl⟩ : syracuseStep 321505199 = 482257799) B482257799
theorem B214336799 : Blo 1957435 214336799 := bstep (se 1 (by rfl) ⟨160752599, by rfl⟩ : syracuseStep 214336799 = 321505199) B321505199
theorem B142891199 : Blo 1957435 142891199 := bstep (se 1 (by rfl) ⟨107168399, by rfl⟩ : syracuseStep 142891199 = 214336799) B214336799
theorem B95260799 : Blo 1957435 95260799 := bstep (se 1 (by rfl) ⟨71445599, by rfl⟩ : syracuseStep 95260799 = 142891199) B142891199
theorem B254028797 : Blo 1957435 254028797 := bstep (se 3 (by rfl) ⟨47630399, by rfl⟩ : syracuseStep 254028797 = 95260799) B95260799
theorem B169352531 : Blo 1957435 169352531 := bstep (se 1 (by rfl) ⟨127014398, by rfl⟩ : syracuseStep 169352531 = 254028797) B254028797
theorem B112901687 : Blo 1957435 112901687 := bstep (se 1 (by rfl) ⟨84676265, by rfl⟩ : syracuseStep 112901687 = 169352531) B169352531
theorem B75267791 : Blo 1957435 75267791 := bstep (se 1 (by rfl) ⟨56450843, by rfl⟩ : syracuseStep 75267791 = 112901687) B112901687
theorem B50178527 : Blo 1957435 50178527 := bstep (se 1 (by rfl) ⟨37633895, by rfl⟩ : syracuseStep 50178527 = 75267791) B75267791
theorem B33452351 : Blo 1957435 33452351 := bstep (se 1 (by rfl) ⟨25089263, by rfl⟩ : syracuseStep 33452351 = 50178527) B50178527
theorem B22301567 : Blo 1957435 22301567 := bstep (se 1 (by rfl) ⟨16726175, by rfl⟩ : syracuseStep 22301567 = 33452351) B33452351
theorem B14867711 : Blo 1957435 14867711 := bstep (se 1 (by rfl) ⟨11150783, by rfl⟩ : syracuseStep 14867711 = 22301567) B22301567
theorem B9911807 : Blo 1957435 9911807 := bstep (se 1 (by rfl) ⟨7433855, by rfl⟩ : syracuseStep 9911807 = 14867711) B14867711
theorem B6607871 : Blo 1957435 6607871 := bstep (se 1 (by rfl) ⟨4955903, by rfl⟩ : syracuseStep 6607871 = 9911807) B9911807
theorem B4405247 : Blo 1957435 4405247 := bstep (se 1 (by rfl) ⟨3303935, by rfl⟩ : syracuseStep 4405247 = 6607871) B6607871
theorem B2936831 : Blo 1957435 2936831 := bstep (se 1 (by rfl) ⟨2202623, by rfl⟩ : syracuseStep 2936831 = 4405247) B4405247
theorem B1957887 : Blo 1957435 1957887 := bstep (se 1 (by rfl) ⟨1468415, by rfl⟩ : syracuseStep 1957887 = 2936831) B2936831
theorem B2936837 : Blo 1957435 2936837 := bbase (se 4 (by rfl) ⟨275328, by rfl⟩ : syracuseStep 2936837 = 550657) (by norm_num)
theorem B1957891 : Blo 1957435 1957891 := bstep (se 1 (by rfl) ⟨1468418, by rfl⟩ : syracuseStep 1957891 = 2936837) B2936837
theorem B3303949 : Blo 1957435 3303949 := bbase (se 3 (by rfl) ⟨619490, by rfl⟩ : syracuseStep 3303949 = 1238981) (by norm_num)
theorem B4405265 : Blo 1957435 4405265 := bstep (se 2 (by rfl) ⟨1651974, by rfl⟩ : syracuseStep 4405265 = 3303949) B3303949
theorem B2936843 : Blo 1957435 2936843 := bstep (se 1 (by rfl) ⟨2202632, by rfl⟩ : syracuseStep 2936843 = 4405265) B4405265
theorem B1957895 : Blo 1957435 1957895 := bstep (se 1 (by rfl) ⟨1468421, by rfl⟩ : syracuseStep 1957895 = 2936843) B2936843
theorem B2202637 : Blo 1957435 2202637 := bbase (se 3 (by rfl) ⟨412994, by rfl⟩ : syracuseStep 2202637 = 825989) (by norm_num)
theorem B2936849 : Blo 1957435 2936849 := bstep (se 2 (by rfl) ⟨1101318, by rfl⟩ : syracuseStep 2936849 = 2202637) B2202637
theorem B1957899 : Blo 1957435 1957899 := bstep (se 1 (by rfl) ⟨1468424, by rfl⟩ : syracuseStep 1957899 = 2936849) B2936849
theorem B6607925 : Blo 1957435 6607925 := bbase (se 5 (by rfl) ⟨309746, by rfl⟩ : syracuseStep 6607925 = 619493) (by norm_num)
theorem B4405283 : Blo 1957435 4405283 := bstep (se 1 (by rfl) ⟨3303962, by rfl⟩ : syracuseStep 4405283 = 6607925) B6607925
theorem B2936855 : Blo 1957435 2936855 := bstep (se 1 (by rfl) ⟨2202641, by rfl⟩ : syracuseStep 2936855 = 4405283) B4405283
theorem B1957903 : Blo 1957435 1957903 := bstep (se 1 (by rfl) ⟨1468427, by rfl⟩ : syracuseStep 1957903 = 2936855) B2936855
theorem B2936861 : Blo 1957435 2936861 := bbase (se 3 (by rfl) ⟨550661, by rfl⟩ : syracuseStep 2936861 = 1101323) (by norm_num)
theorem B1957907 : Blo 1957435 1957907 := bstep (se 1 (by rfl) ⟨1468430, by rfl⟩ : syracuseStep 1957907 = 2936861) B2936861
theorem B4405301 : Blo 1957435 4405301 := bbase (se 5 (by rfl) ⟨206498, by rfl⟩ : syracuseStep 4405301 = 412997) (by norm_num)
theorem B2936867 : Blo 1957435 2936867 := bstep (se 1 (by rfl) ⟨2202650, by rfl⟩ : syracuseStep 2936867 = 4405301) B4405301
theorem B1957911 : Blo 1957435 1957911 := bstep (se 1 (by rfl) ⟨1468433, by rfl⟩ : syracuseStep 1957911 = 2936867) B2936867
theorem B14112917 : Blo 1957435 14112917 := bbase (se 6 (by rfl) ⟨330771, by rfl⟩ : syracuseStep 14112917 = 661543) (by norm_num)
theorem B9408611 : Blo 1957435 9408611 := bstep (se 1 (by rfl) ⟨7056458, by rfl⟩ : syracuseStep 9408611 = 14112917) B14112917
theorem B6272407 : Blo 1957435 6272407 := bstep (se 1 (by rfl) ⟨4704305, by rfl⟩ : syracuseStep 6272407 = 9408611) B9408611
theorem B8363209 : Blo 1957435 8363209 := bstep (se 2 (by rfl) ⟨3136203, by rfl⟩ : syracuseStep 8363209 = 6272407) B6272407
theorem B11150945 : Blo 1957435 11150945 := bstep (se 2 (by rfl) ⟨4181604, by rfl⟩ : syracuseStep 11150945 = 8363209) B8363209
theorem B7433963 : Blo 1957435 7433963 := bstep (se 1 (by rfl) ⟨5575472, by rfl⟩ : syracuseStep 7433963 = 11150945) B11150945
theorem B4955975 : Blo 1957435 4955975 := bstep (se 1 (by rfl) ⟨3716981, by rfl⟩ : syracuseStep 4955975 = 7433963) B7433963
theorem B3303983 : Blo 1957435 3303983 := bstep (se 1 (by rfl) ⟨2477987, by rfl⟩ : syracuseStep 3303983 = 4955975) B4955975
theorem B2202655 : Blo 1957435 2202655 := bstep (se 1 (by rfl) ⟨1651991, by rfl⟩ : syracuseStep 2202655 = 3303983) B3303983
theorem B2936873 : Blo 1957435 2936873 := bstep (se 2 (by rfl) ⟨1101327, by rfl⟩ : syracuseStep 2936873 = 2202655) B2202655
theorem B1957915 : Blo 1957435 1957915 := bstep (se 1 (by rfl) ⟨1468436, by rfl⟩ : syracuseStep 1957915 = 2936873) B2936873
theorem B9408629 : Blo 1957435 9408629 := bbase (se 5 (by rfl) ⟨441029, by rfl⟩ : syracuseStep 9408629 = 882059) (by norm_num)
theorem B6272419 : Blo 1957435 6272419 := bstep (se 1 (by rfl) ⟨4704314, by rfl⟩ : syracuseStep 6272419 = 9408629) B9408629
theorem B8363225 : Blo 1957435 8363225 := bstep (se 2 (by rfl) ⟨3136209, by rfl⟩ : syracuseStep 8363225 = 6272419) B6272419
theorem B5575483 : Blo 1957435 5575483 := bstep (se 1 (by rfl) ⟨4181612, by rfl⟩ : syracuseStep 5575483 = 8363225) B8363225
theorem B7433977 : Blo 1957435 7433977 := bstep (se 2 (by rfl) ⟨2787741, by rfl⟩ : syracuseStep 7433977 = 5575483) B5575483
theorem B9911969 : Blo 1957435 9911969 := bstep (se 2 (by rfl) ⟨3716988, by rfl⟩ : syracuseStep 9911969 = 7433977) B7433977
theorem B6607979 : Blo 1957435 6607979 := bstep (se 1 (by rfl) ⟨4955984, by rfl⟩ : syracuseStep 6607979 = 9911969) B9911969
theorem B4405319 : Blo 1957435 4405319 := bstep (se 1 (by rfl) ⟨3303989, by rfl⟩ : syracuseStep 4405319 = 6607979) B6607979
theorem B2936879 : Blo 1957435 2936879 := bstep (se 1 (by rfl) ⟨2202659, by rfl⟩ : syracuseStep 2936879 = 4405319) B4405319
theorem B1957919 : Blo 1957435 1957919 := bstep (se 1 (by rfl) ⟨1468439, by rfl⟩ : syracuseStep 1957919 = 2936879) B2936879
theorem B2936885 : Blo 1957435 2936885 := bbase (se 5 (by rfl) ⟨137666, by rfl⟩ : syracuseStep 2936885 = 275333) (by norm_num)
theorem B1957923 : Blo 1957435 1957923 := bstep (se 1 (by rfl) ⟨1468442, by rfl⟩ : syracuseStep 1957923 = 2936885) B2936885
theorem B4956005 : Blo 1957435 4956005 := bbase (se 4 (by rfl) ⟨464625, by rfl⟩ : syracuseStep 4956005 = 929251) (by norm_num)
theorem B3304003 : Blo 1957435 3304003 := bstep (se 1 (by rfl) ⟨2478002, by rfl⟩ : syracuseStep 3304003 = 4956005) B4956005
theorem B4405337 : Blo 1957435 4405337 := bstep (se 2 (by rfl) ⟨1652001, by rfl⟩ : syracuseStep 4405337 = 3304003) B3304003
theorem B2936891 : Blo 1957435 2936891 := bstep (se 1 (by rfl) ⟨2202668, by rfl⟩ : syracuseStep 2936891 = 4405337) B4405337
theorem B1957927 : Blo 1957435 1957927 := bstep (se 1 (by rfl) ⟨1468445, by rfl⟩ : syracuseStep 1957927 = 2936891) B2936891
theorem B2202673 : Blo 1957435 2202673 := bbase (se 2 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 2202673 = 1652005) (by norm_num)
theorem B2936897 : Blo 1957435 2936897 := bstep (se 2 (by rfl) ⟨1101336, by rfl⟩ : syracuseStep 2936897 = 2202673) B2202673
theorem B1957931 : Blo 1957435 1957931 := bstep (se 1 (by rfl) ⟨1468448, by rfl⟩ : syracuseStep 1957931 = 2936897) B2936897
theorem B4768541 : Blo 1957435 4768541 := bbase (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) (by norm_num)
theorem B3179027 : Blo 1957435 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B8477405 : Blo 1957435 8477405 := bstep (se 3 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 8477405 = 3179027) B3179027
theorem B5651603 : Blo 1957435 5651603 := bstep (se 1 (by rfl) ⟨4238702, by rfl⟩ : syracuseStep 5651603 = 8477405) B8477405
theorem B3767735 : Blo 1957435 3767735 := bstep (se 1 (by rfl) ⟨2825801, by rfl⟩ : syracuseStep 3767735 = 5651603) B5651603
theorem B2511823 : Blo 1957435 2511823 := bstep (se 1 (by rfl) ⟨1883867, by rfl⟩ : syracuseStep 2511823 = 3767735) B3767735
theorem B3349097 : Blo 1957435 3349097 := bstep (se 2 (by rfl) ⟨1255911, by rfl⟩ : syracuseStep 3349097 = 2511823) B2511823
theorem B2232731 : Blo 1957435 2232731 := bstep (se 1 (by rfl) ⟨1674548, by rfl⟩ : syracuseStep 2232731 = 3349097) B3349097
theorem B5953949 : Blo 1957435 5953949 := bstep (se 3 (by rfl) ⟨1116365, by rfl⟩ : syracuseStep 5953949 = 2232731) B2232731
theorem B3969299 : Blo 1957435 3969299 := bstep (se 1 (by rfl) ⟨2976974, by rfl⟩ : syracuseStep 3969299 = 5953949) B5953949
theorem B2646199 : Blo 1957435 2646199 := bstep (se 1 (by rfl) ⟨1984649, by rfl⟩ : syracuseStep 2646199 = 3969299) B3969299
theorem B14113061 : Blo 1957435 14113061 := bstep (se 4 (by rfl) ⟨1323099, by rfl⟩ : syracuseStep 14113061 = 2646199) B2646199
theorem B9408707 : Blo 1957435 9408707 := bstep (se 1 (by rfl) ⟨7056530, by rfl⟩ : syracuseStep 9408707 = 14113061) B14113061
theorem B6272471 : Blo 1957435 6272471 := bstep (se 1 (by rfl) ⟨4704353, by rfl⟩ : syracuseStep 6272471 = 9408707) B9408707
theorem B4181647 : Blo 1957435 4181647 := bstep (se 1 (by rfl) ⟨3136235, by rfl⟩ : syracuseStep 4181647 = 6272471) B6272471
theorem B5575529 : Blo 1957435 5575529 := bstep (se 2 (by rfl) ⟨2090823, by rfl⟩ : syracuseStep 5575529 = 4181647) B4181647
theorem B3717019 : Blo 1957435 3717019 := bstep (se 1 (by rfl) ⟨2787764, by rfl⟩ : syracuseStep 3717019 = 5575529) B5575529
theorem B4956025 : Blo 1957435 4956025 := bstep (se 2 (by rfl) ⟨1858509, by rfl⟩ : syracuseStep 4956025 = 3717019) B3717019
theorem B6608033 : Blo 1957435 6608033 := bstep (se 2 (by rfl) ⟨2478012, by rfl⟩ : syracuseStep 6608033 = 4956025) B4956025
theorem B4405355 : Blo 1957435 4405355 := bstep (se 1 (by rfl) ⟨3304016, by rfl⟩ : syracuseStep 4405355 = 6608033) B6608033
theorem B2936903 : Blo 1957435 2936903 := bstep (se 1 (by rfl) ⟨2202677, by rfl⟩ : syracuseStep 2936903 = 4405355) B4405355
theorem B1957935 : Blo 1957435 1957935 := bstep (se 1 (by rfl) ⟨1468451, by rfl⟩ : syracuseStep 1957935 = 2936903) B2936903
theorem B2936909 : Blo 1957435 2936909 := bbase (se 3 (by rfl) ⟨550670, by rfl⟩ : syracuseStep 2936909 = 1101341) (by norm_num)
theorem B1957939 : Blo 1957435 1957939 := bstep (se 1 (by rfl) ⟨1468454, by rfl⟩ : syracuseStep 1957939 = 2936909) B2936909
theorem B4405373 : Blo 1957435 4405373 := bbase (se 3 (by rfl) ⟨826007, by rfl⟩ : syracuseStep 4405373 = 1652015) (by norm_num)
theorem B2936915 : Blo 1957435 2936915 := bstep (se 1 (by rfl) ⟨2202686, by rfl⟩ : syracuseStep 2936915 = 4405373) B4405373
theorem B1957943 : Blo 1957435 1957943 := bstep (se 1 (by rfl) ⟨1468457, by rfl⟩ : syracuseStep 1957943 = 2936915) B2936915
theorem B3304037 : Blo 1957435 3304037 := bbase (se 4 (by rfl) ⟨309753, by rfl⟩ : syracuseStep 3304037 = 619507) (by norm_num)
theorem B2202691 : Blo 1957435 2202691 := bstep (se 1 (by rfl) ⟨1652018, by rfl⟩ : syracuseStep 2202691 = 3304037) B3304037
theorem B2936921 : Blo 1957435 2936921 := bstep (se 2 (by rfl) ⟨1101345, by rfl⟩ : syracuseStep 2936921 = 2202691) B2202691
theorem B1957947 : Blo 1957435 1957947 := bstep (se 1 (by rfl) ⟨1468460, by rfl⟩ : syracuseStep 1957947 = 2936921) B2936921
theorem B3136261 : Blo 1957435 3136261 := bbase (se 4 (by rfl) ⟨294024, by rfl⟩ : syracuseStep 3136261 = 588049) (by norm_num)
theorem B4181681 : Blo 1957435 4181681 := bstep (se 2 (by rfl) ⟨1568130, by rfl⟩ : syracuseStep 4181681 = 3136261) B3136261
theorem B2787787 : Blo 1957435 2787787 := bstep (se 1 (by rfl) ⟨2090840, by rfl⟩ : syracuseStep 2787787 = 4181681) B4181681
theorem B14868197 : Blo 1957435 14868197 := bstep (se 4 (by rfl) ⟨1393893, by rfl⟩ : syracuseStep 14868197 = 2787787) B2787787
theorem B9912131 : Blo 1957435 9912131 := bstep (se 1 (by rfl) ⟨7434098, by rfl⟩ : syracuseStep 9912131 = 14868197) B14868197
theorem B6608087 : Blo 1957435 6608087 := bstep (se 1 (by rfl) ⟨4956065, by rfl⟩ : syracuseStep 6608087 = 9912131) B9912131
theorem B4405391 : Blo 1957435 4405391 := bstep (se 1 (by rfl) ⟨3304043, by rfl⟩ : syracuseStep 4405391 = 6608087) B6608087
theorem B2936927 : Blo 1957435 2936927 := bstep (se 1 (by rfl) ⟨2202695, by rfl⟩ : syracuseStep 2936927 = 4405391) B4405391
theorem B1957951 : Blo 1957435 1957951 := bstep (se 1 (by rfl) ⟨1468463, by rfl⟩ : syracuseStep 1957951 = 2936927) B2936927
theorem B2936933 : Blo 1957435 2936933 := bbase (se 4 (by rfl) ⟨275337, by rfl⟩ : syracuseStep 2936933 = 550675) (by norm_num)
theorem B1957955 : Blo 1957435 1957955 := bstep (se 1 (by rfl) ⟨1468466, by rfl⟩ : syracuseStep 1957955 = 2936933) B2936933
theorem B6272549 : Blo 1957435 6272549 := bbase (se 4 (by rfl) ⟨588051, by rfl⟩ : syracuseStep 6272549 = 1176103) (by norm_num)
theorem B4181699 : Blo 1957435 4181699 := bstep (se 1 (by rfl) ⟨3136274, by rfl⟩ : syracuseStep 4181699 = 6272549) B6272549
theorem B2787799 : Blo 1957435 2787799 := bstep (se 1 (by rfl) ⟨2090849, by rfl⟩ : syracuseStep 2787799 = 4181699) B4181699
theorem B3717065 : Blo 1957435 3717065 := bstep (se 2 (by rfl) ⟨1393899, by rfl⟩ : syracuseStep 3717065 = 2787799) B2787799
theorem B2478043 : Blo 1957435 2478043 := bstep (se 1 (by rfl) ⟨1858532, by rfl⟩ : syracuseStep 2478043 = 3717065) B3717065
theorem B3304057 : Blo 1957435 3304057 := bstep (se 2 (by rfl) ⟨1239021, by rfl⟩ : syracuseStep 3304057 = 2478043) B2478043
theorem B4405409 : Blo 1957435 4405409 := bstep (se 2 (by rfl) ⟨1652028, by rfl⟩ : syracuseStep 4405409 = 3304057) B3304057
theorem B2936939 : Blo 1957435 2936939 := bstep (se 1 (by rfl) ⟨2202704, by rfl⟩ : syracuseStep 2936939 = 4405409) B4405409
theorem B1957959 : Blo 1957435 1957959 := bstep (se 1 (by rfl) ⟨1468469, by rfl⟩ : syracuseStep 1957959 = 2936939) B2936939
theorem B2202709 : Blo 1957435 2202709 := bbase (se 8 (by rfl) ⟨12906, by rfl⟩ : syracuseStep 2202709 = 25813) (by norm_num)
theorem B2936945 : Blo 1957435 2936945 := bstep (se 2 (by rfl) ⟨1101354, by rfl⟩ : syracuseStep 2936945 = 2202709) B2202709
theorem B1957963 : Blo 1957435 1957963 := bstep (se 1 (by rfl) ⟨1468472, by rfl⟩ : syracuseStep 1957963 = 2936945) B2936945
theorem B2478053 : Blo 1957435 2478053 := bbase (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) (by norm_num)
theorem B6608141 : Blo 1957435 6608141 := bstep (se 3 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 6608141 = 2478053) B2478053
theorem B4405427 : Blo 1957435 4405427 := bstep (se 1 (by rfl) ⟨3304070, by rfl⟩ : syracuseStep 4405427 = 6608141) B6608141
theorem B2936951 : Blo 1957435 2936951 := bstep (se 1 (by rfl) ⟨2202713, by rfl⟩ : syracuseStep 2936951 = 4405427) B4405427
theorem B1957967 : Blo 1957435 1957967 := bstep (se 1 (by rfl) ⟨1468475, by rfl⟩ : syracuseStep 1957967 = 2936951) B2936951
theorem B2936957 : Blo 1957435 2936957 := bbase (se 3 (by rfl) ⟨550679, by rfl⟩ : syracuseStep 2936957 = 1101359) (by norm_num)
theorem B1957971 : Blo 1957435 1957971 := bstep (se 1 (by rfl) ⟨1468478, by rfl⟩ : syracuseStep 1957971 = 2936957) B2936957
theorem B4405445 : Blo 1957435 4405445 := bbase (se 4 (by rfl) ⟨413010, by rfl⟩ : syracuseStep 4405445 = 826021) (by norm_num)
theorem B2936963 : Blo 1957435 2936963 := bstep (se 1 (by rfl) ⟨2202722, by rfl⟩ : syracuseStep 2936963 = 4405445) B4405445
theorem B1957975 : Blo 1957435 1957975 := bstep (se 1 (by rfl) ⟨1468481, by rfl⟩ : syracuseStep 1957975 = 2936963) B2936963
theorem B21170069 : Blo 1957435 21170069 := bbase (se 6 (by rfl) ⟨496173, by rfl⟩ : syracuseStep 21170069 = 992347) (by norm_num)
theorem B14113379 : Blo 1957435 14113379 := bstep (se 1 (by rfl) ⟨10585034, by rfl⟩ : syracuseStep 14113379 = 21170069) B21170069
theorem B9408919 : Blo 1957435 9408919 := bstep (se 1 (by rfl) ⟨7056689, by rfl⟩ : syracuseStep 9408919 = 14113379) B14113379
theorem B12545225 : Blo 1957435 12545225 := bstep (se 2 (by rfl) ⟨4704459, by rfl⟩ : syracuseStep 12545225 = 9408919) B9408919
theorem B8363483 : Blo 1957435 8363483 := bstep (se 1 (by rfl) ⟨6272612, by rfl⟩ : syracuseStep 8363483 = 12545225) B12545225
theorem B5575655 : Blo 1957435 5575655 := bstep (se 1 (by rfl) ⟨4181741, by rfl⟩ : syracuseStep 5575655 = 8363483) B8363483
theorem B3717103 : Blo 1957435 3717103 := bstep (se 1 (by rfl) ⟨2787827, by rfl⟩ : syracuseStep 3717103 = 5575655) B5575655
theorem B4956137 : Blo 1957435 4956137 := bstep (se 2 (by rfl) ⟨1858551, by rfl⟩ : syracuseStep 4956137 = 3717103) B3717103
theorem B3304091 : Blo 1957435 3304091 := bstep (se 1 (by rfl) ⟨2478068, by rfl⟩ : syracuseStep 3304091 = 4956137) B4956137
theorem B2202727 : Blo 1957435 2202727 := bstep (se 1 (by rfl) ⟨1652045, by rfl⟩ : syracuseStep 2202727 = 3304091) B3304091
theorem B2936969 : Blo 1957435 2936969 := bstep (se 2 (by rfl) ⟨1101363, by rfl⟩ : syracuseStep 2936969 = 2202727) B2202727
theorem B1957979 : Blo 1957435 1957979 := bstep (se 1 (by rfl) ⟨1468484, by rfl⟩ : syracuseStep 1957979 = 2936969) B2936969
theorem B9912293 : Blo 1957435 9912293 := bbase (se 4 (by rfl) ⟨929277, by rfl⟩ : syracuseStep 9912293 = 1858555) (by norm_num)
theorem B6608195 : Blo 1957435 6608195 := bstep (se 1 (by rfl) ⟨4956146, by rfl⟩ : syracuseStep 6608195 = 9912293) B9912293
theorem B4405463 : Blo 1957435 4405463 := bstep (se 1 (by rfl) ⟨3304097, by rfl⟩ : syracuseStep 4405463 = 6608195) B6608195
theorem B2936975 : Blo 1957435 2936975 := bstep (se 1 (by rfl) ⟨2202731, by rfl⟩ : syracuseStep 2936975 = 4405463) B4405463
theorem B1957983 : Blo 1957435 1957983 := bstep (se 1 (by rfl) ⟨1468487, by rfl⟩ : syracuseStep 1957983 = 2936975) B2936975
theorem B2936981 : Blo 1957435 2936981 := bbase (se 6 (by rfl) ⟨68835, by rfl⟩ : syracuseStep 2936981 = 137671) (by norm_num)
theorem B1957987 : Blo 1957435 1957987 := bstep (se 1 (by rfl) ⟨1468490, by rfl⟩ : syracuseStep 1957987 = 2936981) B2936981
theorem B3136325 : Blo 1957435 3136325 := bbase (se 4 (by rfl) ⟨294030, by rfl⟩ : syracuseStep 3136325 = 588061) (by norm_num)
theorem B8363533 : Blo 1957435 8363533 := bstep (se 3 (by rfl) ⟨1568162, by rfl⟩ : syracuseStep 8363533 = 3136325) B3136325
theorem B11151377 : Blo 1957435 11151377 := bstep (se 2 (by rfl) ⟨4181766, by rfl⟩ : syracuseStep 11151377 = 8363533) B8363533
theorem B7434251 : Blo 1957435 7434251 := bstep (se 1 (by rfl) ⟨5575688, by rfl⟩ : syracuseStep 7434251 = 11151377) B11151377
theorem B4956167 : Blo 1957435 4956167 := bstep (se 1 (by rfl) ⟨3717125, by rfl⟩ : syracuseStep 4956167 = 7434251) B7434251
theorem B3304111 : Blo 1957435 3304111 := bstep (se 1 (by rfl) ⟨2478083, by rfl⟩ : syracuseStep 3304111 = 4956167) B4956167
theorem B4405481 : Blo 1957435 4405481 := bstep (se 2 (by rfl) ⟨1652055, by rfl⟩ : syracuseStep 4405481 = 3304111) B3304111
theorem B2936987 : Blo 1957435 2936987 := bstep (se 1 (by rfl) ⟨2202740, by rfl⟩ : syracuseStep 2936987 = 4405481) B4405481
theorem B1957991 : Blo 1957435 1957991 := bstep (se 1 (by rfl) ⟨1468493, by rfl⟩ : syracuseStep 1957991 = 2936987) B2936987
theorem B2202745 : Blo 1957435 2202745 := bbase (se 2 (by rfl) ⟨826029, by rfl⟩ : syracuseStep 2202745 = 1652059) (by norm_num)
theorem B2936993 : Blo 1957435 2936993 := bstep (se 2 (by rfl) ⟨1101372, by rfl⟩ : syracuseStep 2936993 = 2202745) B2202745
theorem B1957995 : Blo 1957435 1957995 := bstep (se 1 (by rfl) ⟨1468496, by rfl⟩ : syracuseStep 1957995 = 2936993) B2936993
theorem B4526533 : Blo 1957435 4526533 := bbase (se 4 (by rfl) ⟨424362, by rfl⟩ : syracuseStep 4526533 = 848725) (by norm_num)
theorem B24141509 : Blo 1957435 24141509 := bstep (se 4 (by rfl) ⟨2263266, by rfl⟩ : syracuseStep 24141509 = 4526533) B4526533
theorem B16094339 : Blo 1957435 16094339 := bstep (se 1 (by rfl) ⟨12070754, by rfl⟩ : syracuseStep 16094339 = 24141509) B24141509
theorem B10729559 : Blo 1957435 10729559 := bstep (se 1 (by rfl) ⟨8047169, by rfl⟩ : syracuseStep 10729559 = 16094339) B16094339
theorem B7153039 : Blo 1957435 7153039 := bstep (se 1 (by rfl) ⟨5364779, by rfl⟩ : syracuseStep 7153039 = 10729559) B10729559
theorem B38149541 : Blo 1957435 38149541 := bstep (se 4 (by rfl) ⟨3576519, by rfl⟩ : syracuseStep 38149541 = 7153039) B7153039
theorem B25433027 : Blo 1957435 25433027 := bstep (se 1 (by rfl) ⟨19074770, by rfl⟩ : syracuseStep 25433027 = 38149541) B38149541
theorem B16955351 : Blo 1957435 16955351 := bstep (se 1 (by rfl) ⟨12716513, by rfl⟩ : syracuseStep 16955351 = 25433027) B25433027
theorem B11303567 : Blo 1957435 11303567 := bstep (se 1 (by rfl) ⟨8477675, by rfl⟩ : syracuseStep 11303567 = 16955351) B16955351
theorem B7535711 : Blo 1957435 7535711 := bstep (se 1 (by rfl) ⟨5651783, by rfl⟩ : syracuseStep 7535711 = 11303567) B11303567
theorem B20095229 : Blo 1957435 20095229 := bstep (se 3 (by rfl) ⟨3767855, by rfl⟩ : syracuseStep 20095229 = 7535711) B7535711
theorem B53587277 : Blo 1957435 53587277 := bstep (se 3 (by rfl) ⟨10047614, by rfl⟩ : syracuseStep 53587277 = 20095229) B20095229
theorem B35724851 : Blo 1957435 35724851 := bstep (se 1 (by rfl) ⟨26793638, by rfl⟩ : syracuseStep 35724851 = 53587277) B53587277
theorem B23816567 : Blo 1957435 23816567 := bstep (se 1 (by rfl) ⟨17862425, by rfl⟩ : syracuseStep 23816567 = 35724851) B35724851
theorem B15877711 : Blo 1957435 15877711 := bstep (se 1 (by rfl) ⟨11908283, by rfl⟩ : syracuseStep 15877711 = 23816567) B23816567
theorem B21170281 : Blo 1957435 21170281 := bstep (se 2 (by rfl) ⟨7938855, by rfl⟩ : syracuseStep 21170281 = 15877711) B15877711
theorem B28227041 : Blo 1957435 28227041 := bstep (se 2 (by rfl) ⟨10585140, by rfl⟩ : syracuseStep 28227041 = 21170281) B21170281
theorem B18818027 : Blo 1957435 18818027 := bstep (se 1 (by rfl) ⟨14113520, by rfl⟩ : syracuseStep 18818027 = 28227041) B28227041
theorem B12545351 : Blo 1957435 12545351 := bstep (se 1 (by rfl) ⟨9409013, by rfl⟩ : syracuseStep 12545351 = 18818027) B18818027
theorem B8363567 : Blo 1957435 8363567 := bstep (se 1 (by rfl) ⟨6272675, by rfl⟩ : syracuseStep 8363567 = 12545351) B12545351
theorem B5575711 : Blo 1957435 5575711 := bstep (se 1 (by rfl) ⟨4181783, by rfl⟩ : syracuseStep 5575711 = 8363567) B8363567
theorem B7434281 : Blo 1957435 7434281 := bstep (se 2 (by rfl) ⟨2787855, by rfl⟩ : syracuseStep 7434281 = 5575711) B5575711
theorem B4956187 : Blo 1957435 4956187 := bstep (se 1 (by rfl) ⟨3717140, by rfl⟩ : syracuseStep 4956187 = 7434281) B7434281
theorem B6608249 : Blo 1957435 6608249 := bstep (se 2 (by rfl) ⟨2478093, by rfl⟩ : syracuseStep 6608249 = 4956187) B4956187
theorem B4405499 : Blo 1957435 4405499 := bstep (se 1 (by rfl) ⟨3304124, by rfl⟩ : syracuseStep 4405499 = 6608249) B6608249
theorem B2936999 : Blo 1957435 2936999 := bstep (se 1 (by rfl) ⟨2202749, by rfl⟩ : syracuseStep 2936999 = 4405499) B4405499
theorem B1957999 : Blo 1957435 1957999 := bstep (se 1 (by rfl) ⟨1468499, by rfl⟩ : syracuseStep 1957999 = 2936999) B2936999
theorem B2937005 : Blo 1957435 2937005 := bbase (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) (by norm_num)
theorem B1958003 : Blo 1957435 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B4405517 : Blo 1957435 4405517 := bbase (se 3 (by rfl) ⟨826034, by rfl⟩ : syracuseStep 4405517 = 1652069) (by norm_num)
theorem B2937011 : Blo 1957435 2937011 := bstep (se 1 (by rfl) ⟨2202758, by rfl⟩ : syracuseStep 2937011 = 4405517) B4405517
theorem B1958007 : Blo 1957435 1958007 := bstep (se 1 (by rfl) ⟨1468505, by rfl⟩ : syracuseStep 1958007 = 2937011) B2937011
theorem B2478109 : Blo 1957435 2478109 := bbase (se 3 (by rfl) ⟨464645, by rfl⟩ : syracuseStep 2478109 = 929291) (by norm_num)
theorem B3304145 : Blo 1957435 3304145 := bstep (se 2 (by rfl) ⟨1239054, by rfl⟩ : syracuseStep 3304145 = 2478109) B2478109
theorem B2202763 : Blo 1957435 2202763 := bstep (se 1 (by rfl) ⟨1652072, by rfl⟩ : syracuseStep 2202763 = 3304145) B3304145
theorem B2937017 : Blo 1957435 2937017 := bstep (se 2 (by rfl) ⟨1101381, by rfl⟩ : syracuseStep 2937017 = 2202763) B2202763
theorem B1958011 : Blo 1957435 1958011 := bstep (se 1 (by rfl) ⟨1468508, by rfl⟩ : syracuseStep 1958011 = 2937017) B2937017
theorem B3969461 : Blo 1957435 3969461 := bbase (se 5 (by rfl) ⟨186068, by rfl⟩ : syracuseStep 3969461 = 372137) (by norm_num)
theorem B2646307 : Blo 1957435 2646307 := bstep (se 1 (by rfl) ⟨1984730, by rfl⟩ : syracuseStep 2646307 = 3969461) B3969461
theorem B3528409 : Blo 1957435 3528409 := bstep (se 2 (by rfl) ⟨1323153, by rfl⟩ : syracuseStep 3528409 = 2646307) B2646307
theorem B4704545 : Blo 1957435 4704545 := bstep (se 2 (by rfl) ⟨1764204, by rfl⟩ : syracuseStep 4704545 = 3528409) B3528409
theorem B3136363 : Blo 1957435 3136363 := bstep (se 1 (by rfl) ⟨2352272, by rfl⟩ : syracuseStep 3136363 = 4704545) B4704545
theorem B16727269 : Blo 1957435 16727269 := bstep (se 4 (by rfl) ⟨1568181, by rfl⟩ : syracuseStep 16727269 = 3136363) B3136363
theorem B22303025 : Blo 1957435 22303025 := bstep (se 2 (by rfl) ⟨8363634, by rfl⟩ : syracuseStep 22303025 = 16727269) B16727269
theorem B14868683 : Blo 1957435 14868683 := bstep (se 1 (by rfl) ⟨11151512, by rfl⟩ : syracuseStep 14868683 = 22303025) B22303025
theorem B9912455 : Blo 1957435 9912455 := bstep (se 1 (by rfl) ⟨7434341, by rfl⟩ : syracuseStep 9912455 = 14868683) B14868683
theorem B6608303 : Blo 1957435 6608303 := bstep (se 1 (by rfl) ⟨4956227, by rfl⟩ : syracuseStep 6608303 = 9912455) B9912455
theorem B4405535 : Blo 1957435 4405535 := bstep (se 1 (by rfl) ⟨3304151, by rfl⟩ : syracuseStep 4405535 = 6608303) B6608303
theorem B2937023 : Blo 1957435 2937023 := bstep (se 1 (by rfl) ⟨2202767, by rfl⟩ : syracuseStep 2937023 = 4405535) B4405535
theorem B1958015 : Blo 1957435 1958015 := bstep (se 1 (by rfl) ⟨1468511, by rfl⟩ : syracuseStep 1958015 = 2937023) B2937023
theorem B2937029 : Blo 1957435 2937029 := bbase (se 4 (by rfl) ⟨275346, by rfl⟩ : syracuseStep 2937029 = 550693) (by norm_num)
theorem B1958019 : Blo 1957435 1958019 := bstep (se 1 (by rfl) ⟨1468514, by rfl⟩ : syracuseStep 1958019 = 2937029) B2937029
theorem B3304165 : Blo 1957435 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B4405553 : Blo 1957435 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B2937035 : Blo 1957435 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B1958023 : Blo 1957435 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2202781 : Blo 1957435 2202781 := bbase (se 3 (by rfl) ⟨413021, by rfl⟩ : syracuseStep 2202781 = 826043) (by norm_num)
theorem B2937041 : Blo 1957435 2937041 := bstep (se 2 (by rfl) ⟨1101390, by rfl⟩ : syracuseStep 2937041 = 2202781) B2202781
theorem B1958027 : Blo 1957435 1958027 := bstep (se 1 (by rfl) ⟨1468520, by rfl⟩ : syracuseStep 1958027 = 2937041) B2937041
theorem B6608357 : Blo 1957435 6608357 := bbase (se 4 (by rfl) ⟨619533, by rfl⟩ : syracuseStep 6608357 = 1239067) (by norm_num)
theorem B4405571 : Blo 1957435 4405571 := bstep (se 1 (by rfl) ⟨3304178, by rfl⟩ : syracuseStep 4405571 = 6608357) B6608357
theorem B2937047 : Blo 1957435 2937047 := bstep (se 1 (by rfl) ⟨2202785, by rfl⟩ : syracuseStep 2937047 = 4405571) B4405571
theorem B1958031 : Blo 1957435 1958031 := bstep (se 1 (by rfl) ⟨1468523, by rfl⟩ : syracuseStep 1958031 = 2937047) B2937047
theorem B2937053 : Blo 1957435 2937053 := bbase (se 3 (by rfl) ⟨550697, by rfl⟩ : syracuseStep 2937053 = 1101395) (by norm_num)
theorem B1958035 : Blo 1957435 1958035 := bstep (se 1 (by rfl) ⟨1468526, by rfl⟩ : syracuseStep 1958035 = 2937053) B2937053
theorem B4405589 : Blo 1957435 4405589 := bbase (se 10 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 4405589 = 12907) (by norm_num)
theorem B2937059 : Blo 1957435 2937059 := bstep (se 1 (by rfl) ⟨2202794, by rfl⟩ : syracuseStep 2937059 = 4405589) B4405589
theorem B1958039 : Blo 1957435 1958039 := bstep (se 1 (by rfl) ⟨1468529, by rfl⟩ : syracuseStep 1958039 = 2937059) B2937059
theorem B3528461 : Blo 1957435 3528461 := bbase (se 3 (by rfl) ⟨661586, by rfl⟩ : syracuseStep 3528461 = 1323173) (by norm_num)
theorem B2352307 : Blo 1957435 2352307 := bstep (se 1 (by rfl) ⟨1764230, by rfl⟩ : syracuseStep 2352307 = 3528461) B3528461
theorem B3136409 : Blo 1957435 3136409 := bstep (se 2 (by rfl) ⟨1176153, by rfl⟩ : syracuseStep 3136409 = 2352307) B2352307
theorem B2090939 : Blo 1957435 2090939 := bstep (se 1 (by rfl) ⟨1568204, by rfl⟩ : syracuseStep 2090939 = 3136409) B3136409
theorem B5575837 : Blo 1957435 5575837 := bstep (se 3 (by rfl) ⟨1045469, by rfl⟩ : syracuseStep 5575837 = 2090939) B2090939
theorem B7434449 : Blo 1957435 7434449 := bstep (se 2 (by rfl) ⟨2787918, by rfl⟩ : syracuseStep 7434449 = 5575837) B5575837
theorem B4956299 : Blo 1957435 4956299 := bstep (se 1 (by rfl) ⟨3717224, by rfl⟩ : syracuseStep 4956299 = 7434449) B7434449
theorem B3304199 : Blo 1957435 3304199 := bstep (se 1 (by rfl) ⟨2478149, by rfl⟩ : syracuseStep 3304199 = 4956299) B4956299
theorem B2202799 : Blo 1957435 2202799 := bstep (se 1 (by rfl) ⟨1652099, by rfl⟩ : syracuseStep 2202799 = 3304199) B3304199
theorem B2937065 : Blo 1957435 2937065 := bstep (se 2 (by rfl) ⟨1101399, by rfl⟩ : syracuseStep 2937065 = 2202799) B2202799
theorem B1958043 : Blo 1957435 1958043 := bstep (se 1 (by rfl) ⟨1468532, by rfl⟩ : syracuseStep 1958043 = 2937065) B2937065
theorem B2546237 : Blo 1957435 2546237 := bbase (se 3 (by rfl) ⟨477419, by rfl⟩ : syracuseStep 2546237 = 954839) (by norm_num)
theorem B6789965 : Blo 1957435 6789965 := bstep (se 3 (by rfl) ⟨1273118, by rfl⟩ : syracuseStep 6789965 = 2546237) B2546237
theorem B18106573 : Blo 1957435 18106573 := bstep (se 3 (by rfl) ⟨3394982, by rfl⟩ : syracuseStep 18106573 = 6789965) B6789965
theorem B24142097 : Blo 1957435 24142097 := bstep (se 2 (by rfl) ⟨9053286, by rfl⟩ : syracuseStep 24142097 = 18106573) B18106573
theorem B64378925 : Blo 1957435 64378925 := bstep (se 3 (by rfl) ⟨12071048, by rfl⟩ : syracuseStep 64378925 = 24142097) B24142097
theorem B42919283 : Blo 1957435 42919283 := bstep (se 1 (by rfl) ⟨32189462, by rfl⟩ : syracuseStep 42919283 = 64378925) B64378925
theorem B28612855 : Blo 1957435 28612855 := bstep (se 1 (by rfl) ⟨21459641, by rfl⟩ : syracuseStep 28612855 = 42919283) B42919283
theorem B38150473 : Blo 1957435 38150473 := bstep (se 2 (by rfl) ⟨14306427, by rfl⟩ : syracuseStep 38150473 = 28612855) B28612855
theorem B50867297 : Blo 1957435 50867297 := bstep (se 2 (by rfl) ⟨19075236, by rfl⟩ : syracuseStep 50867297 = 38150473) B38150473
theorem B33911531 : Blo 1957435 33911531 := bstep (se 1 (by rfl) ⟨25433648, by rfl⟩ : syracuseStep 33911531 = 50867297) B50867297
theorem B22607687 : Blo 1957435 22607687 := bstep (se 1 (by rfl) ⟨16955765, by rfl⟩ : syracuseStep 22607687 = 33911531) B33911531
theorem B15071791 : Blo 1957435 15071791 := bstep (se 1 (by rfl) ⟨11303843, by rfl⟩ : syracuseStep 15071791 = 22607687) B22607687
theorem B20095721 : Blo 1957435 20095721 := bstep (se 2 (by rfl) ⟨7535895, by rfl⟩ : syracuseStep 20095721 = 15071791) B15071791
theorem B13397147 : Blo 1957435 13397147 := bstep (se 1 (by rfl) ⟨10047860, by rfl⟩ : syracuseStep 13397147 = 20095721) B20095721
theorem B8931431 : Blo 1957435 8931431 := bstep (se 1 (by rfl) ⟨6698573, by rfl⟩ : syracuseStep 8931431 = 13397147) B13397147
theorem B23817149 : Blo 1957435 23817149 := bstep (se 3 (by rfl) ⟨4465715, by rfl⟩ : syracuseStep 23817149 = 8931431) B8931431
theorem B15878099 : Blo 1957435 15878099 := bstep (se 1 (by rfl) ⟨11908574, by rfl⟩ : syracuseStep 15878099 = 23817149) B23817149
theorem B10585399 : Blo 1957435 10585399 := bstep (se 1 (by rfl) ⟨7939049, by rfl⟩ : syracuseStep 10585399 = 15878099) B15878099
theorem B14113865 : Blo 1957435 14113865 := bstep (se 2 (by rfl) ⟨5292699, by rfl⟩ : syracuseStep 14113865 = 10585399) B10585399
theorem B37636973 : Blo 1957435 37636973 := bstep (se 3 (by rfl) ⟨7056932, by rfl⟩ : syracuseStep 37636973 = 14113865) B14113865
theorem B25091315 : Blo 1957435 25091315 := bstep (se 1 (by rfl) ⟨18818486, by rfl⟩ : syracuseStep 25091315 = 37636973) B37636973
theorem B16727543 : Blo 1957435 16727543 := bstep (se 1 (by rfl) ⟨12545657, by rfl⟩ : syracuseStep 16727543 = 25091315) B25091315
theorem B11151695 : Blo 1957435 11151695 := bstep (se 1 (by rfl) ⟨8363771, by rfl⟩ : syracuseStep 11151695 = 16727543) B16727543
theorem B7434463 : Blo 1957435 7434463 := bstep (se 1 (by rfl) ⟨5575847, by rfl⟩ : syracuseStep 7434463 = 11151695) B11151695
theorem B9912617 : Blo 1957435 9912617 := bstep (se 2 (by rfl) ⟨3717231, by rfl⟩ : syracuseStep 9912617 = 7434463) B7434463
theorem B6608411 : Blo 1957435 6608411 := bstep (se 1 (by rfl) ⟨4956308, by rfl⟩ : syracuseStep 6608411 = 9912617) B9912617
theorem B4405607 : Blo 1957435 4405607 := bstep (se 1 (by rfl) ⟨3304205, by rfl⟩ : syracuseStep 4405607 = 6608411) B6608411
theorem B2937071 : Blo 1957435 2937071 := bstep (se 1 (by rfl) ⟨2202803, by rfl⟩ : syracuseStep 2937071 = 4405607) B4405607
theorem B1958047 : Blo 1957435 1958047 := bstep (se 1 (by rfl) ⟨1468535, by rfl⟩ : syracuseStep 1958047 = 2937071) B2937071
theorem B2937077 : Blo 1957435 2937077 := bbase (se 5 (by rfl) ⟨137675, by rfl⟩ : syracuseStep 2937077 = 275351) (by norm_num)
theorem B1958051 : Blo 1957435 1958051 := bstep (se 1 (by rfl) ⟨1468538, by rfl⟩ : syracuseStep 1958051 = 2937077) B2937077
theorem B3349301 : Blo 1957435 3349301 := bbase (se 5 (by rfl) ⟨156998, by rfl⟩ : syracuseStep 3349301 = 313997) (by norm_num)
theorem B8931469 : Blo 1957435 8931469 := bstep (se 3 (by rfl) ⟨1674650, by rfl⟩ : syracuseStep 8931469 = 3349301) B3349301
theorem B11908625 : Blo 1957435 11908625 := bstep (se 2 (by rfl) ⟨4465734, by rfl⟩ : syracuseStep 11908625 = 8931469) B8931469
theorem B31756333 : Blo 1957435 31756333 := bstep (se 3 (by rfl) ⟨5954312, by rfl⟩ : syracuseStep 31756333 = 11908625) B11908625
theorem B42341777 : Blo 1957435 42341777 := bstep (se 2 (by rfl) ⟨15878166, by rfl⟩ : syracuseStep 42341777 = 31756333) B31756333
theorem B28227851 : Blo 1957435 28227851 := bstep (se 1 (by rfl) ⟨21170888, by rfl⟩ : syracuseStep 28227851 = 42341777) B42341777
theorem B18818567 : Blo 1957435 18818567 := bstep (se 1 (by rfl) ⟨14113925, by rfl⟩ : syracuseStep 18818567 = 28227851) B28227851
theorem B12545711 : Blo 1957435 12545711 := bstep (se 1 (by rfl) ⟨9409283, by rfl⟩ : syracuseStep 12545711 = 18818567) B18818567
theorem B8363807 : Blo 1957435 8363807 := bstep (se 1 (by rfl) ⟨6272855, by rfl⟩ : syracuseStep 8363807 = 12545711) B12545711
theorem B5575871 : Blo 1957435 5575871 := bstep (se 1 (by rfl) ⟨4181903, by rfl⟩ : syracuseStep 5575871 = 8363807) B8363807
theorem B3717247 : Blo 1957435 3717247 := bstep (se 1 (by rfl) ⟨2787935, by rfl⟩ : syracuseStep 3717247 = 5575871) B5575871
theorem B4956329 : Blo 1957435 4956329 := bstep (se 2 (by rfl) ⟨1858623, by rfl⟩ : syracuseStep 4956329 = 3717247) B3717247
theorem B3304219 : Blo 1957435 3304219 := bstep (se 1 (by rfl) ⟨2478164, by rfl⟩ : syracuseStep 3304219 = 4956329) B4956329
theorem B4405625 : Blo 1957435 4405625 := bstep (se 2 (by rfl) ⟨1652109, by rfl⟩ : syracuseStep 4405625 = 3304219) B3304219
theorem B2937083 : Blo 1957435 2937083 := bstep (se 1 (by rfl) ⟨2202812, by rfl⟩ : syracuseStep 2937083 = 4405625) B4405625
theorem B1958055 : Blo 1957435 1958055 := bstep (se 1 (by rfl) ⟨1468541, by rfl⟩ : syracuseStep 1958055 = 2937083) B2937083
theorem B2202817 : Blo 1957435 2202817 := bbase (se 2 (by rfl) ⟨826056, by rfl⟩ : syracuseStep 2202817 = 1652113) (by norm_num)
theorem B2937089 : Blo 1957435 2937089 := bstep (se 2 (by rfl) ⟨1101408, by rfl⟩ : syracuseStep 2937089 = 2202817) B2202817
theorem B1958059 : Blo 1957435 1958059 := bstep (se 1 (by rfl) ⟨1468544, by rfl⟩ : syracuseStep 1958059 = 2937089) B2937089
theorem B4956349 : Blo 1957435 4956349 := bbase (se 3 (by rfl) ⟨929315, by rfl⟩ : syracuseStep 4956349 = 1858631) (by norm_num)
theorem B6608465 : Blo 1957435 6608465 := bstep (se 2 (by rfl) ⟨2478174, by rfl⟩ : syracuseStep 6608465 = 4956349) B4956349
theorem B4405643 : Blo 1957435 4405643 := bstep (se 1 (by rfl) ⟨3304232, by rfl⟩ : syracuseStep 4405643 = 6608465) B6608465
theorem B2937095 : Blo 1957435 2937095 := bstep (se 1 (by rfl) ⟨2202821, by rfl⟩ : syracuseStep 2937095 = 4405643) B4405643
theorem B1958063 : Blo 1957435 1958063 := bstep (se 1 (by rfl) ⟨1468547, by rfl⟩ : syracuseStep 1958063 = 2937095) B2937095
theorem B2937101 : Blo 1957435 2937101 := bbase (se 3 (by rfl) ⟨550706, by rfl⟩ : syracuseStep 2937101 = 1101413) (by norm_num)
theorem B1958067 : Blo 1957435 1958067 := bstep (se 1 (by rfl) ⟨1468550, by rfl⟩ : syracuseStep 1958067 = 2937101) B2937101
theorem B4405661 : Blo 1957435 4405661 := bbase (se 3 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 4405661 = 1652123) (by norm_num)
theorem B2937107 : Blo 1957435 2937107 := bstep (se 1 (by rfl) ⟨2202830, by rfl⟩ : syracuseStep 2937107 = 4405661) B4405661
theorem B1958071 : Blo 1957435 1958071 := bstep (se 1 (by rfl) ⟨1468553, by rfl⟩ : syracuseStep 1958071 = 2937107) B2937107
theorem B3304253 : Blo 1957435 3304253 := bbase (se 3 (by rfl) ⟨619547, by rfl⟩ : syracuseStep 3304253 = 1239095) (by norm_num)
theorem B2202835 : Blo 1957435 2202835 := bstep (se 1 (by rfl) ⟨1652126, by rfl⟩ : syracuseStep 2202835 = 3304253) B3304253
theorem B2937113 : Blo 1957435 2937113 := bstep (se 2 (by rfl) ⟨1101417, by rfl⟩ : syracuseStep 2937113 = 2202835) B2202835
theorem B1958075 : Blo 1957435 1958075 := bstep (se 1 (by rfl) ⟨1468556, by rfl⟩ : syracuseStep 1958075 = 2937113) B2937113
theorem B2090977 : Blo 1957435 2090977 := bbase (se 2 (by rfl) ⟨784116, by rfl⟩ : syracuseStep 2090977 = 1568233) (by norm_num)
theorem B11151877 : Blo 1957435 11151877 := bstep (se 4 (by rfl) ⟨1045488, by rfl⟩ : syracuseStep 11151877 = 2090977) B2090977
theorem B14869169 : Blo 1957435 14869169 := bstep (se 2 (by rfl) ⟨5575938, by rfl⟩ : syracuseStep 14869169 = 11151877) B11151877
theorem B9912779 : Blo 1957435 9912779 := bstep (se 1 (by rfl) ⟨7434584, by rfl⟩ : syracuseStep 9912779 = 14869169) B14869169
theorem B6608519 : Blo 1957435 6608519 := bstep (se 1 (by rfl) ⟨4956389, by rfl⟩ : syracuseStep 6608519 = 9912779) B9912779
theorem B4405679 : Blo 1957435 4405679 := bstep (se 1 (by rfl) ⟨3304259, by rfl⟩ : syracuseStep 4405679 = 6608519) B6608519
theorem B2937119 : Blo 1957435 2937119 := bstep (se 1 (by rfl) ⟨2202839, by rfl⟩ : syracuseStep 2937119 = 4405679) B4405679
theorem B1958079 : Blo 1957435 1958079 := bstep (se 1 (by rfl) ⟨1468559, by rfl⟩ : syracuseStep 1958079 = 2937119) B2937119
theorem B2937125 : Blo 1957435 2937125 := bbase (se 4 (by rfl) ⟨275355, by rfl⟩ : syracuseStep 2937125 = 550711) (by norm_num)
theorem B1958083 : Blo 1957435 1958083 := bstep (se 1 (by rfl) ⟨1468562, by rfl⟩ : syracuseStep 1958083 = 2937125) B2937125
theorem B2478205 : Blo 1957435 2478205 := bbase (se 3 (by rfl) ⟨464663, by rfl⟩ : syracuseStep 2478205 = 929327) (by norm_num)
theorem B3304273 : Blo 1957435 3304273 := bstep (se 2 (by rfl) ⟨1239102, by rfl⟩ : syracuseStep 3304273 = 2478205) B2478205
theorem B4405697 : Blo 1957435 4405697 := bstep (se 2 (by rfl) ⟨1652136, by rfl⟩ : syracuseStep 4405697 = 3304273) B3304273
theorem B2937131 : Blo 1957435 2937131 := bstep (se 1 (by rfl) ⟨2202848, by rfl⟩ : syracuseStep 2937131 = 4405697) B4405697
theorem B1958087 : Blo 1957435 1958087 := bstep (se 1 (by rfl) ⟨1468565, by rfl⟩ : syracuseStep 1958087 = 2937131) B2937131
theorem B2202853 : Blo 1957435 2202853 := bbase (se 4 (by rfl) ⟨206517, by rfl⟩ : syracuseStep 2202853 = 413035) (by norm_num)
theorem B2937137 : Blo 1957435 2937137 := bstep (se 2 (by rfl) ⟨1101426, by rfl⟩ : syracuseStep 2937137 = 2202853) B2202853
theorem B1958091 : Blo 1957435 1958091 := bstep (se 1 (by rfl) ⟨1468568, by rfl⟩ : syracuseStep 1958091 = 2937137) B2937137
theorem B4181989 : Blo 1957435 4181989 := bbase (se 4 (by rfl) ⟨392061, by rfl⟩ : syracuseStep 4181989 = 784123) (by norm_num)
theorem B5575985 : Blo 1957435 5575985 := bstep (se 2 (by rfl) ⟨2090994, by rfl⟩ : syracuseStep 5575985 = 4181989) B4181989
theorem B3717323 : Blo 1957435 3717323 := bstep (se 1 (by rfl) ⟨2787992, by rfl⟩ : syracuseStep 3717323 = 5575985) B5575985
theorem B2478215 : Blo 1957435 2478215 := bstep (se 1 (by rfl) ⟨1858661, by rfl⟩ : syracuseStep 2478215 = 3717323) B3717323
theorem B6608573 : Blo 1957435 6608573 := bstep (se 3 (by rfl) ⟨1239107, by rfl⟩ : syracuseStep 6608573 = 2478215) B2478215
theorem B4405715 : Blo 1957435 4405715 := bstep (se 1 (by rfl) ⟨3304286, by rfl⟩ : syracuseStep 4405715 = 6608573) B6608573
theorem B2937143 : Blo 1957435 2937143 := bstep (se 1 (by rfl) ⟨2202857, by rfl⟩ : syracuseStep 2937143 = 4405715) B4405715
theorem B1958095 : Blo 1957435 1958095 := bstep (se 1 (by rfl) ⟨1468571, by rfl⟩ : syracuseStep 1958095 = 2937143) B2937143
theorem B2937149 : Blo 1957435 2937149 := bbase (se 3 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 2937149 = 1101431) (by norm_num)
theorem B1958099 : Blo 1957435 1958099 := bstep (se 1 (by rfl) ⟨1468574, by rfl⟩ : syracuseStep 1958099 = 2937149) B2937149
theorem B4405733 : Blo 1957435 4405733 := bbase (se 4 (by rfl) ⟨413037, by rfl⟩ : syracuseStep 4405733 = 826075) (by norm_num)
theorem B2937155 : Blo 1957435 2937155 := bstep (se 1 (by rfl) ⟨2202866, by rfl⟩ : syracuseStep 2937155 = 4405733) B4405733
theorem B1958103 : Blo 1957435 1958103 := bstep (se 1 (by rfl) ⟨1468577, by rfl⟩ : syracuseStep 1958103 = 2937155) B2937155
theorem B4956461 : Blo 1957435 4956461 := bbase (se 3 (by rfl) ⟨929336, by rfl⟩ : syracuseStep 4956461 = 1858673) (by norm_num)
theorem B3304307 : Blo 1957435 3304307 := bstep (se 1 (by rfl) ⟨2478230, by rfl⟩ : syracuseStep 3304307 = 4956461) B4956461
theorem B2202871 : Blo 1957435 2202871 := bstep (se 1 (by rfl) ⟨1652153, by rfl⟩ : syracuseStep 2202871 = 3304307) B3304307
theorem B2937161 : Blo 1957435 2937161 := bstep (se 2 (by rfl) ⟨1101435, by rfl⟩ : syracuseStep 2937161 = 2202871) B2202871
theorem B1958107 : Blo 1957435 1958107 := bstep (se 1 (by rfl) ⟨1468580, by rfl⟩ : syracuseStep 1958107 = 2937161) B2937161
theorem B2646437 : Blo 1957435 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B7057165 : Blo 1957435 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B9409553 : Blo 1957435 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B6273035 : Blo 1957435 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B4182023 : Blo 1957435 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B2788015 : Blo 1957435 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B3717353 : Blo 1957435 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B9912941 : Blo 1957435 9912941 := bstep (se 3 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 9912941 = 3717353) B3717353
theorem B6608627 : Blo 1957435 6608627 := bstep (se 1 (by rfl) ⟨4956470, by rfl⟩ : syracuseStep 6608627 = 9912941) B9912941
theorem B4405751 : Blo 1957435 4405751 := bstep (se 1 (by rfl) ⟨3304313, by rfl⟩ : syracuseStep 4405751 = 6608627) B6608627
theorem B2937167 : Blo 1957435 2937167 := bstep (se 1 (by rfl) ⟨2202875, by rfl⟩ : syracuseStep 2937167 = 4405751) B4405751
theorem B1958111 : Blo 1957435 1958111 := bstep (se 1 (by rfl) ⟨1468583, by rfl⟩ : syracuseStep 1958111 = 2937167) B2937167
theorem B2937173 : Blo 1957435 2937173 := bbase (se 10 (by rfl) ⟨4302, by rfl⟩ : syracuseStep 2937173 = 8605) (by norm_num)
theorem B1958115 : Blo 1957435 1958115 := bstep (se 1 (by rfl) ⟨1468586, by rfl⟩ : syracuseStep 1958115 = 2937173) B2937173
theorem B5576053 : Blo 1957435 5576053 := bbase (se 5 (by rfl) ⟨261377, by rfl⟩ : syracuseStep 5576053 = 522755) (by norm_num)
theorem B7434737 : Blo 1957435 7434737 := bstep (se 2 (by rfl) ⟨2788026, by rfl⟩ : syracuseStep 7434737 = 5576053) B5576053
theorem B4956491 : Blo 1957435 4956491 := bstep (se 1 (by rfl) ⟨3717368, by rfl⟩ : syracuseStep 4956491 = 7434737) B7434737
theorem B3304327 : Blo 1957435 3304327 := bstep (se 1 (by rfl) ⟨2478245, by rfl⟩ : syracuseStep 3304327 = 4956491) B4956491
theorem B4405769 : Blo 1957435 4405769 := bstep (se 2 (by rfl) ⟨1652163, by rfl⟩ : syracuseStep 4405769 = 3304327) B3304327
theorem B2937179 : Blo 1957435 2937179 := bstep (se 1 (by rfl) ⟨2202884, by rfl⟩ : syracuseStep 2937179 = 4405769) B4405769
theorem B1958119 : Blo 1957435 1958119 := bstep (se 1 (by rfl) ⟨1468589, by rfl⟩ : syracuseStep 1958119 = 2937179) B2937179
theorem B2202889 : Blo 1957435 2202889 := bbase (se 2 (by rfl) ⟨826083, by rfl⟩ : syracuseStep 2202889 = 1652167) (by norm_num)
theorem B2937185 : Blo 1957435 2937185 := bstep (se 2 (by rfl) ⟨1101444, by rfl⟩ : syracuseStep 2937185 = 2202889) B2202889
theorem B1958123 : Blo 1957435 1958123 := bstep (se 1 (by rfl) ⟨1468592, by rfl⟩ : syracuseStep 1958123 = 2937185) B2937185
theorem B5292917 : Blo 1957435 5292917 := bbase (se 5 (by rfl) ⟨248105, by rfl⟩ : syracuseStep 5292917 = 496211) (by norm_num)
theorem B3528611 : Blo 1957435 3528611 := bstep (se 1 (by rfl) ⟨2646458, by rfl⟩ : syracuseStep 3528611 = 5292917) B5292917
theorem B2352407 : Blo 1957435 2352407 := bstep (se 1 (by rfl) ⟨1764305, by rfl⟩ : syracuseStep 2352407 = 3528611) B3528611
theorem B25092341 : Blo 1957435 25092341 := bstep (se 5 (by rfl) ⟨1176203, by rfl⟩ : syracuseStep 25092341 = 2352407) B2352407
theorem B16728227 : Blo 1957435 16728227 := bstep (se 1 (by rfl) ⟨12546170, by rfl⟩ : syracuseStep 16728227 = 25092341) B25092341
theorem B11152151 : Blo 1957435 11152151 := bstep (se 1 (by rfl) ⟨8364113, by rfl⟩ : syracuseStep 11152151 = 16728227) B16728227
theorem B7434767 : Blo 1957435 7434767 := bstep (se 1 (by rfl) ⟨5576075, by rfl⟩ : syracuseStep 7434767 = 11152151) B11152151
theorem B4956511 : Blo 1957435 4956511 := bstep (se 1 (by rfl) ⟨3717383, by rfl⟩ : syracuseStep 4956511 = 7434767) B7434767
theorem B6608681 : Blo 1957435 6608681 := bstep (se 2 (by rfl) ⟨2478255, by rfl⟩ : syracuseStep 6608681 = 4956511) B4956511
theorem B4405787 : Blo 1957435 4405787 := bstep (se 1 (by rfl) ⟨3304340, by rfl⟩ : syracuseStep 4405787 = 6608681) B6608681
theorem B2937191 : Blo 1957435 2937191 := bstep (se 1 (by rfl) ⟨2202893, by rfl⟩ : syracuseStep 2937191 = 4405787) B4405787
theorem B1958127 : Blo 1957435 1958127 := bstep (se 1 (by rfl) ⟨1468595, by rfl⟩ : syracuseStep 1958127 = 2937191) B2937191
theorem B2937197 : Blo 1957435 2937197 := bbase (se 3 (by rfl) ⟨550724, by rfl⟩ : syracuseStep 2937197 = 1101449) (by norm_num)
theorem B1958131 : Blo 1957435 1958131 := bstep (se 1 (by rfl) ⟨1468598, by rfl⟩ : syracuseStep 1958131 = 2937197) B2937197
theorem B4405805 : Blo 1957435 4405805 := bbase (se 3 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 4405805 = 1652177) (by norm_num)
theorem B2937203 : Blo 1957435 2937203 := bstep (se 1 (by rfl) ⟨2202902, by rfl⟩ : syracuseStep 2937203 = 4405805) B4405805
theorem B1958135 : Blo 1957435 1958135 := bstep (se 1 (by rfl) ⟨1468601, by rfl⟩ : syracuseStep 1958135 = 2937203) B2937203
theorem B2977285 : Blo 1957435 2977285 := bbase (se 4 (by rfl) ⟨279120, by rfl⟩ : syracuseStep 2977285 = 558241) (by norm_num)
theorem B3969713 : Blo 1957435 3969713 := bstep (se 2 (by rfl) ⟨1488642, by rfl⟩ : syracuseStep 3969713 = 2977285) B2977285
theorem B2646475 : Blo 1957435 2646475 := bstep (se 1 (by rfl) ⟨1984856, by rfl⟩ : syracuseStep 2646475 = 3969713) B3969713
theorem B14114533 : Blo 1957435 14114533 := bstep (se 4 (by rfl) ⟨1323237, by rfl⟩ : syracuseStep 14114533 = 2646475) B2646475
theorem B18819377 : Blo 1957435 18819377 := bstep (se 2 (by rfl) ⟨7057266, by rfl⟩ : syracuseStep 18819377 = 14114533) B14114533
theorem B12546251 : Blo 1957435 12546251 := bstep (se 1 (by rfl) ⟨9409688, by rfl⟩ : syracuseStep 12546251 = 18819377) B18819377
theorem B8364167 : Blo 1957435 8364167 := bstep (se 1 (by rfl) ⟨6273125, by rfl⟩ : syracuseStep 8364167 = 12546251) B12546251
theorem B5576111 : Blo 1957435 5576111 := bstep (se 1 (by rfl) ⟨4182083, by rfl⟩ : syracuseStep 5576111 = 8364167) B8364167
theorem B3717407 : Blo 1957435 3717407 := bstep (se 1 (by rfl) ⟨2788055, by rfl⟩ : syracuseStep 3717407 = 5576111) B5576111
theorem B2478271 : Blo 1957435 2478271 := bstep (se 1 (by rfl) ⟨1858703, by rfl⟩ : syracuseStep 2478271 = 3717407) B3717407
theorem B3304361 : Blo 1957435 3304361 := bstep (se 2 (by rfl) ⟨1239135, by rfl⟩ : syracuseStep 3304361 = 2478271) B2478271
theorem B2202907 : Blo 1957435 2202907 := bstep (se 1 (by rfl) ⟨1652180, by rfl⟩ : syracuseStep 2202907 = 3304361) B3304361
theorem B2937209 : Blo 1957435 2937209 := bstep (se 2 (by rfl) ⟨1101453, by rfl⟩ : syracuseStep 2937209 = 2202907) B2202907
theorem B1958139 : Blo 1957435 1958139 := bstep (se 1 (by rfl) ⟨1468604, by rfl⟩ : syracuseStep 1958139 = 2937209) B2937209
theorem B33456725 : Blo 1957435 33456725 := bbase (se 8 (by rfl) ⟨196035, by rfl⟩ : syracuseStep 33456725 = 392071) (by norm_num)
theorem B22304483 : Blo 1957435 22304483 := bstep (se 1 (by rfl) ⟨16728362, by rfl⟩ : syracuseStep 22304483 = 33456725) B33456725
theorem B14869655 : Blo 1957435 14869655 := bstep (se 1 (by rfl) ⟨11152241, by rfl⟩ : syracuseStep 14869655 = 22304483) B22304483
theorem B9913103 : Blo 1957435 9913103 := bstep (se 1 (by rfl) ⟨7434827, by rfl⟩ : syracuseStep 9913103 = 14869655) B14869655
theorem B6608735 : Blo 1957435 6608735 := bstep (se 1 (by rfl) ⟨4956551, by rfl⟩ : syracuseStep 6608735 = 9913103) B9913103
theorem B4405823 : Blo 1957435 4405823 := bstep (se 1 (by rfl) ⟨3304367, by rfl⟩ : syracuseStep 4405823 = 6608735) B6608735
theorem B2937215 : Blo 1957435 2937215 := bstep (se 1 (by rfl) ⟨2202911, by rfl⟩ : syracuseStep 2937215 = 4405823) B4405823
theorem B1958143 : Blo 1957435 1958143 := bstep (se 1 (by rfl) ⟨1468607, by rfl⟩ : syracuseStep 1958143 = 2937215) B2937215
theorem B2937221 : Blo 1957435 2937221 := bbase (se 4 (by rfl) ⟨275364, by rfl⟩ : syracuseStep 2937221 = 550729) (by norm_num)
theorem B1958147 : Blo 1957435 1958147 := bstep (se 1 (by rfl) ⟨1468610, by rfl⟩ : syracuseStep 1958147 = 2937221) B2937221
theorem B3304381 : Blo 1957435 3304381 := bbase (se 3 (by rfl) ⟨619571, by rfl⟩ : syracuseStep 3304381 = 1239143) (by norm_num)
theorem B4405841 : Blo 1957435 4405841 := bstep (se 2 (by rfl) ⟨1652190, by rfl⟩ : syracuseStep 4405841 = 3304381) B3304381
theorem B2937227 : Blo 1957435 2937227 := bstep (se 1 (by rfl) ⟨2202920, by rfl⟩ : syracuseStep 2937227 = 4405841) B4405841
theorem B1958151 : Blo 1957435 1958151 := bstep (se 1 (by rfl) ⟨1468613, by rfl⟩ : syracuseStep 1958151 = 2937227) B2937227
theorem B2202925 : Blo 1957435 2202925 := bbase (se 3 (by rfl) ⟨413048, by rfl⟩ : syracuseStep 2202925 = 826097) (by norm_num)
theorem B2937233 : Blo 1957435 2937233 := bstep (se 2 (by rfl) ⟨1101462, by rfl⟩ : syracuseStep 2937233 = 2202925) B2202925
theorem B1958155 : Blo 1957435 1958155 := bstep (se 1 (by rfl) ⟨1468616, by rfl⟩ : syracuseStep 1958155 = 2937233) B2937233
theorem B6608789 : Blo 1957435 6608789 := bbase (se 6 (by rfl) ⟨154893, by rfl⟩ : syracuseStep 6608789 = 309787) (by norm_num)
theorem B4405859 : Blo 1957435 4405859 := bstep (se 1 (by rfl) ⟨3304394, by rfl⟩ : syracuseStep 4405859 = 6608789) B6608789
theorem B2937239 : Blo 1957435 2937239 := bstep (se 1 (by rfl) ⟨2202929, by rfl⟩ : syracuseStep 2937239 = 4405859) B4405859
theorem B1958159 : Blo 1957435 1958159 := bstep (se 1 (by rfl) ⟨1468619, by rfl⟩ : syracuseStep 1958159 = 2937239) B2937239
theorem B2937245 : Blo 1957435 2937245 := bbase (se 3 (by rfl) ⟨550733, by rfl⟩ : syracuseStep 2937245 = 1101467) (by norm_num)
theorem B1958163 : Blo 1957435 1958163 := bstep (se 1 (by rfl) ⟨1468622, by rfl⟩ : syracuseStep 1958163 = 2937245) B2937245
theorem B4405877 : Blo 1957435 4405877 := bbase (se 5 (by rfl) ⟨206525, by rfl⟩ : syracuseStep 4405877 = 413051) (by norm_num)
theorem B2937251 : Blo 1957435 2937251 := bstep (se 1 (by rfl) ⟨2202938, by rfl⟩ : syracuseStep 2937251 = 4405877) B4405877
theorem B1958167 : Blo 1957435 1958167 := bstep (se 1 (by rfl) ⟨1468625, by rfl⟩ : syracuseStep 1958167 = 2937251) B2937251
theorem B7057381 : Blo 1957435 7057381 := bbase (se 4 (by rfl) ⟨661629, by rfl⟩ : syracuseStep 7057381 = 1323259) (by norm_num)
theorem B9409841 : Blo 1957435 9409841 := bstep (se 2 (by rfl) ⟨3528690, by rfl⟩ : syracuseStep 9409841 = 7057381) B7057381
theorem B6273227 : Blo 1957435 6273227 := bstep (se 1 (by rfl) ⟨4704920, by rfl⟩ : syracuseStep 6273227 = 9409841) B9409841
theorem B16728605 : Blo 1957435 16728605 := bstep (se 3 (by rfl) ⟨3136613, by rfl⟩ : syracuseStep 16728605 = 6273227) B6273227
theorem B11152403 : Blo 1957435 11152403 := bstep (se 1 (by rfl) ⟨8364302, by rfl⟩ : syracuseStep 11152403 = 16728605) B16728605
theorem B7434935 : Blo 1957435 7434935 := bstep (se 1 (by rfl) ⟨5576201, by rfl⟩ : syracuseStep 7434935 = 11152403) B11152403
theorem B4956623 : Blo 1957435 4956623 := bstep (se 1 (by rfl) ⟨3717467, by rfl⟩ : syracuseStep 4956623 = 7434935) B7434935
theorem B3304415 : Blo 1957435 3304415 := bstep (se 1 (by rfl) ⟨2478311, by rfl⟩ : syracuseStep 3304415 = 4956623) B4956623
theorem B2202943 : Blo 1957435 2202943 := bstep (se 1 (by rfl) ⟨1652207, by rfl⟩ : syracuseStep 2202943 = 3304415) B3304415
theorem B2937257 : Blo 1957435 2937257 := bstep (se 2 (by rfl) ⟨1101471, by rfl⟩ : syracuseStep 2937257 = 2202943) B2202943
theorem B1958171 : Blo 1957435 1958171 := bstep (se 1 (by rfl) ⟨1468628, by rfl⟩ : syracuseStep 1958171 = 2937257) B2937257
theorem B7434949 : Blo 1957435 7434949 := bbase (se 4 (by rfl) ⟨697026, by rfl⟩ : syracuseStep 7434949 = 1394053) (by norm_num)
theorem B9913265 : Blo 1957435 9913265 := bstep (se 2 (by rfl) ⟨3717474, by rfl⟩ : syracuseStep 9913265 = 7434949) B7434949
theorem B6608843 : Blo 1957435 6608843 := bstep (se 1 (by rfl) ⟨4956632, by rfl⟩ : syracuseStep 6608843 = 9913265) B9913265
theorem B4405895 : Blo 1957435 4405895 := bstep (se 1 (by rfl) ⟨3304421, by rfl⟩ : syracuseStep 4405895 = 6608843) B6608843
theorem B2937263 : Blo 1957435 2937263 := bstep (se 1 (by rfl) ⟨2202947, by rfl⟩ : syracuseStep 2937263 = 4405895) B4405895
theorem B1958175 : Blo 1957435 1958175 := bstep (se 1 (by rfl) ⟨1468631, by rfl⟩ : syracuseStep 1958175 = 2937263) B2937263
theorem B2937269 : Blo 1957435 2937269 := bbase (se 5 (by rfl) ⟨137684, by rfl⟩ : syracuseStep 2937269 = 275369) (by norm_num)
theorem B1958179 : Blo 1957435 1958179 := bstep (se 1 (by rfl) ⟨1468634, by rfl⟩ : syracuseStep 1958179 = 2937269) B2937269
theorem B4956653 : Blo 1957435 4956653 := bbase (se 3 (by rfl) ⟨929372, by rfl⟩ : syracuseStep 4956653 = 1858745) (by norm_num)
theorem B3304435 : Blo 1957435 3304435 := bstep (se 1 (by rfl) ⟨2478326, by rfl⟩ : syracuseStep 3304435 = 4956653) B4956653
theorem B4405913 : Blo 1957435 4405913 := bstep (se 2 (by rfl) ⟨1652217, by rfl⟩ : syracuseStep 4405913 = 3304435) B3304435
theorem B2937275 : Blo 1957435 2937275 := bstep (se 1 (by rfl) ⟨2202956, by rfl⟩ : syracuseStep 2937275 = 4405913) B4405913
theorem B1958183 : Blo 1957435 1958183 := bstep (se 1 (by rfl) ⟨1468637, by rfl⟩ : syracuseStep 1958183 = 2937275) B2937275
theorem B2202961 : Blo 1957435 2202961 := bbase (se 2 (by rfl) ⟨826110, by rfl⟩ : syracuseStep 2202961 = 1652221) (by norm_num)
theorem B2937281 : Blo 1957435 2937281 := bstep (se 2 (by rfl) ⟨1101480, by rfl⟩ : syracuseStep 2937281 = 2202961) B2202961
theorem B1958187 : Blo 1957435 1958187 := bstep (se 1 (by rfl) ⟨1468640, by rfl⟩ : syracuseStep 1958187 = 2937281) B2937281
theorem B2091097 : Blo 1957435 2091097 := bbase (se 2 (by rfl) ⟨784161, by rfl⟩ : syracuseStep 2091097 = 1568323) (by norm_num)
theorem B2788129 : Blo 1957435 2788129 := bstep (se 2 (by rfl) ⟨1045548, by rfl⟩ : syracuseStep 2788129 = 2091097) B2091097
theorem B3717505 : Blo 1957435 3717505 := bstep (se 2 (by rfl) ⟨1394064, by rfl⟩ : syracuseStep 3717505 = 2788129) B2788129
theorem B4956673 : Blo 1957435 4956673 := bstep (se 2 (by rfl) ⟨1858752, by rfl⟩ : syracuseStep 4956673 = 3717505) B3717505
theorem B6608897 : Blo 1957435 6608897 := bstep (se 2 (by rfl) ⟨2478336, by rfl⟩ : syracuseStep 6608897 = 4956673) B4956673
theorem B4405931 : Blo 1957435 4405931 := bstep (se 1 (by rfl) ⟨3304448, by rfl⟩ : syracuseStep 4405931 = 6608897) B6608897
theorem B2937287 : Blo 1957435 2937287 := bstep (se 1 (by rfl) ⟨2202965, by rfl⟩ : syracuseStep 2937287 = 4405931) B4405931
theorem B1958191 : Blo 1957435 1958191 := bstep (se 1 (by rfl) ⟨1468643, by rfl⟩ : syracuseStep 1958191 = 2937287) B2937287
theorem B2937293 : Blo 1957435 2937293 := bbase (se 3 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 2937293 = 1101485) (by norm_num)
theorem B1958195 : Blo 1957435 1958195 := bstep (se 1 (by rfl) ⟨1468646, by rfl⟩ : syracuseStep 1958195 = 2937293) B2937293
theorem B4405949 : Blo 1957435 4405949 := bbase (se 3 (by rfl) ⟨826115, by rfl⟩ : syracuseStep 4405949 = 1652231) (by norm_num)
theorem B2937299 : Blo 1957435 2937299 := bstep (se 1 (by rfl) ⟨2202974, by rfl⟩ : syracuseStep 2937299 = 4405949) B4405949
theorem B1958199 : Blo 1957435 1958199 := bstep (se 1 (by rfl) ⟨1468649, by rfl⟩ : syracuseStep 1958199 = 2937299) B2937299
theorem B3304469 : Blo 1957435 3304469 := bbase (se 6 (by rfl) ⟨77448, by rfl⟩ : syracuseStep 3304469 = 154897) (by norm_num)
theorem B2202979 : Blo 1957435 2202979 := bstep (se 1 (by rfl) ⟨1652234, by rfl⟩ : syracuseStep 2202979 = 3304469) B3304469
theorem B2937305 : Blo 1957435 2937305 := bstep (se 2 (by rfl) ⟨1101489, by rfl⟩ : syracuseStep 2937305 = 2202979) B2202979
theorem B1958203 : Blo 1957435 1958203 := bstep (se 1 (by rfl) ⟨1468652, by rfl⟩ : syracuseStep 1958203 = 2937305) B2937305
theorem B2119645 : Blo 1957435 2119645 := bbase (se 3 (by rfl) ⟨397433, by rfl⟩ : syracuseStep 2119645 = 794867) (by norm_num)
theorem B2826193 : Blo 1957435 2826193 := bstep (se 2 (by rfl) ⟨1059822, by rfl⟩ : syracuseStep 2826193 = 2119645) B2119645
theorem B3768257 : Blo 1957435 3768257 := bstep (se 2 (by rfl) ⟨1413096, by rfl⟩ : syracuseStep 3768257 = 2826193) B2826193
theorem B2512171 : Blo 1957435 2512171 := bstep (se 1 (by rfl) ⟨1884128, by rfl⟩ : syracuseStep 2512171 = 3768257) B3768257
theorem B3349561 : Blo 1957435 3349561 := bstep (se 2 (by rfl) ⟨1256085, by rfl⟩ : syracuseStep 3349561 = 2512171) B2512171
theorem B4466081 : Blo 1957435 4466081 := bstep (se 2 (by rfl) ⟨1674780, by rfl⟩ : syracuseStep 4466081 = 3349561) B3349561
theorem B2977387 : Blo 1957435 2977387 := bstep (se 1 (by rfl) ⟨2233040, by rfl⟩ : syracuseStep 2977387 = 4466081) B4466081
theorem B15879397 : Blo 1957435 15879397 := bstep (se 4 (by rfl) ⟨1488693, by rfl⟩ : syracuseStep 15879397 = 2977387) B2977387
theorem B21172529 : Blo 1957435 21172529 := bstep (se 2 (by rfl) ⟨7939698, by rfl⟩ : syracuseStep 21172529 = 15879397) B15879397
theorem B14115019 : Blo 1957435 14115019 := bstep (se 1 (by rfl) ⟨10586264, by rfl⟩ : syracuseStep 14115019 = 21172529) B21172529
theorem B18820025 : Blo 1957435 18820025 := bstep (se 2 (by rfl) ⟨7057509, by rfl⟩ : syracuseStep 18820025 = 14115019) B14115019
theorem B12546683 : Blo 1957435 12546683 := bstep (se 1 (by rfl) ⟨9410012, by rfl⟩ : syracuseStep 12546683 = 18820025) B18820025
theorem B8364455 : Blo 1957435 8364455 := bstep (se 1 (by rfl) ⟨6273341, by rfl⟩ : syracuseStep 8364455 = 12546683) B12546683
theorem B5576303 : Blo 1957435 5576303 := bstep (se 1 (by rfl) ⟨4182227, by rfl⟩ : syracuseStep 5576303 = 8364455) B8364455
theorem B14870141 : Blo 1957435 14870141 := bstep (se 3 (by rfl) ⟨2788151, by rfl⟩ : syracuseStep 14870141 = 5576303) B5576303
theorem B9913427 : Blo 1957435 9913427 := bstep (se 1 (by rfl) ⟨7435070, by rfl⟩ : syracuseStep 9913427 = 14870141) B14870141
theorem B6608951 : Blo 1957435 6608951 := bstep (se 1 (by rfl) ⟨4956713, by rfl⟩ : syracuseStep 6608951 = 9913427) B9913427
theorem B4405967 : Blo 1957435 4405967 := bstep (se 1 (by rfl) ⟨3304475, by rfl⟩ : syracuseStep 4405967 = 6608951) B6608951
theorem B2937311 : Blo 1957435 2937311 := bstep (se 1 (by rfl) ⟨2202983, by rfl⟩ : syracuseStep 2937311 = 4405967) B4405967
theorem B1958207 : Blo 1957435 1958207 := bstep (se 1 (by rfl) ⟨1468655, by rfl⟩ : syracuseStep 1958207 = 2937311) B2937311
theorem B2937317 : Blo 1957435 2937317 := bbase (se 4 (by rfl) ⟨275373, by rfl⟩ : syracuseStep 2937317 = 550747) (by norm_num)
theorem B1958211 : Blo 1957435 1958211 := bstep (se 1 (by rfl) ⟨1468658, by rfl⟩ : syracuseStep 1958211 = 2937317) B2937317
theorem B9410053 : Blo 1957435 9410053 := bbase (se 4 (by rfl) ⟨882192, by rfl⟩ : syracuseStep 9410053 = 1764385) (by norm_num)
theorem B12546737 : Blo 1957435 12546737 := bstep (se 2 (by rfl) ⟨4705026, by rfl⟩ : syracuseStep 12546737 = 9410053) B9410053
theorem B8364491 : Blo 1957435 8364491 := bstep (se 1 (by rfl) ⟨6273368, by rfl⟩ : syracuseStep 8364491 = 12546737) B12546737
theorem B5576327 : Blo 1957435 5576327 := bstep (se 1 (by rfl) ⟨4182245, by rfl⟩ : syracuseStep 5576327 = 8364491) B8364491
theorem B3717551 : Blo 1957435 3717551 := bstep (se 1 (by rfl) ⟨2788163, by rfl⟩ : syracuseStep 3717551 = 5576327) B5576327
theorem B2478367 : Blo 1957435 2478367 := bstep (se 1 (by rfl) ⟨1858775, by rfl⟩ : syracuseStep 2478367 = 3717551) B3717551
theorem B3304489 : Blo 1957435 3304489 := bstep (se 2 (by rfl) ⟨1239183, by rfl⟩ : syracuseStep 3304489 = 2478367) B2478367
theorem B4405985 : Blo 1957435 4405985 := bstep (se 2 (by rfl) ⟨1652244, by rfl⟩ : syracuseStep 4405985 = 3304489) B3304489
theorem B2937323 : Blo 1957435 2937323 := bstep (se 1 (by rfl) ⟨2202992, by rfl⟩ : syracuseStep 2937323 = 4405985) B4405985
theorem B1958215 : Blo 1957435 1958215 := bstep (se 1 (by rfl) ⟨1468661, by rfl⟩ : syracuseStep 1958215 = 2937323) B2937323
theorem B2202997 : Blo 1957435 2202997 := bbase (se 5 (by rfl) ⟨103265, by rfl⟩ : syracuseStep 2202997 = 206531) (by norm_num)
theorem B2937329 : Blo 1957435 2937329 := bstep (se 2 (by rfl) ⟨1101498, by rfl⟩ : syracuseStep 2937329 = 2202997) B2202997
theorem B1958219 : Blo 1957435 1958219 := bstep (se 1 (by rfl) ⟨1468664, by rfl⟩ : syracuseStep 1958219 = 2937329) B2937329
theorem B2478377 : Blo 1957435 2478377 := bbase (se 2 (by rfl) ⟨929391, by rfl⟩ : syracuseStep 2478377 = 1858783) (by norm_num)
theorem B6609005 : Blo 1957435 6609005 := bstep (se 3 (by rfl) ⟨1239188, by rfl⟩ : syracuseStep 6609005 = 2478377) B2478377
theorem B4406003 : Blo 1957435 4406003 := bstep (se 1 (by rfl) ⟨3304502, by rfl⟩ : syracuseStep 4406003 = 6609005) B6609005
theorem B2937335 : Blo 1957435 2937335 := bstep (se 1 (by rfl) ⟨2203001, by rfl⟩ : syracuseStep 2937335 = 4406003) B4406003
theorem B1958223 : Blo 1957435 1958223 := bstep (se 1 (by rfl) ⟨1468667, by rfl⟩ : syracuseStep 1958223 = 2937335) B2937335
theorem B2937341 : Blo 1957435 2937341 := bbase (se 3 (by rfl) ⟨550751, by rfl⟩ : syracuseStep 2937341 = 1101503) (by norm_num)
theorem B1958227 : Blo 1957435 1958227 := bstep (se 1 (by rfl) ⟨1468670, by rfl⟩ : syracuseStep 1958227 = 2937341) B2937341
theorem B4406021 : Blo 1957435 4406021 := bbase (se 4 (by rfl) ⟨413064, by rfl⟩ : syracuseStep 4406021 = 826129) (by norm_num)
theorem B2937347 : Blo 1957435 2937347 := bstep (se 1 (by rfl) ⟨2203010, by rfl⟩ : syracuseStep 2937347 = 4406021) B4406021
theorem B1958231 : Blo 1957435 1958231 := bstep (se 1 (by rfl) ⟨1468673, by rfl⟩ : syracuseStep 1958231 = 2937347) B2937347
theorem B3717589 : Blo 1957435 3717589 := bbase (se 7 (by rfl) ⟨43565, by rfl⟩ : syracuseStep 3717589 = 87131) (by norm_num)
theorem B4956785 : Blo 1957435 4956785 := bstep (se 2 (by rfl) ⟨1858794, by rfl⟩ : syracuseStep 4956785 = 3717589) B3717589
theorem B3304523 : Blo 1957435 3304523 := bstep (se 1 (by rfl) ⟨2478392, by rfl⟩ : syracuseStep 3304523 = 4956785) B4956785
theorem B2203015 : Blo 1957435 2203015 := bstep (se 1 (by rfl) ⟨1652261, by rfl⟩ : syracuseStep 2203015 = 3304523) B3304523
theorem B2937353 : Blo 1957435 2937353 := bstep (se 2 (by rfl) ⟨1101507, by rfl⟩ : syracuseStep 2937353 = 2203015) B2203015
theorem B1958235 : Blo 1957435 1958235 := bstep (se 1 (by rfl) ⟨1468676, by rfl⟩ : syracuseStep 1958235 = 2937353) B2937353
theorem B9913589 : Blo 1957435 9913589 := bbase (se 5 (by rfl) ⟨464699, by rfl⟩ : syracuseStep 9913589 = 929399) (by norm_num)
theorem B6609059 : Blo 1957435 6609059 := bstep (se 1 (by rfl) ⟨4956794, by rfl⟩ : syracuseStep 6609059 = 9913589) B9913589
theorem B4406039 : Blo 1957435 4406039 := bstep (se 1 (by rfl) ⟨3304529, by rfl⟩ : syracuseStep 4406039 = 6609059) B6609059
theorem B2937359 : Blo 1957435 2937359 := bstep (se 1 (by rfl) ⟨2203019, by rfl⟩ : syracuseStep 2937359 = 4406039) B4406039
theorem B1958239 : Blo 1957435 1958239 := bstep (se 1 (by rfl) ⟨1468679, by rfl⟩ : syracuseStep 1958239 = 2937359) B2937359
theorem B2937365 : Blo 1957435 2937365 := bbase (se 6 (by rfl) ⟨68844, by rfl⟩ : syracuseStep 2937365 = 137689) (by norm_num)
theorem B1958243 : Blo 1957435 1958243 := bstep (se 1 (by rfl) ⟨1468682, by rfl⟩ : syracuseStep 1958243 = 2937365) B2937365
theorem B4466173 : Blo 1957435 4466173 := bbase (se 3 (by rfl) ⟨837407, by rfl⟩ : syracuseStep 4466173 = 1674815) (by norm_num)
theorem B5954897 : Blo 1957435 5954897 := bstep (se 2 (by rfl) ⟨2233086, by rfl⟩ : syracuseStep 5954897 = 4466173) B4466173
theorem B15879725 : Blo 1957435 15879725 := bstep (se 3 (by rfl) ⟨2977448, by rfl⟩ : syracuseStep 15879725 = 5954897) B5954897
theorem B10586483 : Blo 1957435 10586483 := bstep (se 1 (by rfl) ⟨7939862, by rfl⟩ : syracuseStep 10586483 = 15879725) B15879725
theorem B7057655 : Blo 1957435 7057655 := bstep (se 1 (by rfl) ⟨5293241, by rfl⟩ : syracuseStep 7057655 = 10586483) B10586483
theorem B4705103 : Blo 1957435 4705103 := bstep (se 1 (by rfl) ⟨3528827, by rfl⟩ : syracuseStep 4705103 = 7057655) B7057655
theorem B3136735 : Blo 1957435 3136735 := bstep (se 1 (by rfl) ⟨2352551, by rfl⟩ : syracuseStep 3136735 = 4705103) B4705103
theorem B16729253 : Blo 1957435 16729253 := bstep (se 4 (by rfl) ⟨1568367, by rfl⟩ : syracuseStep 16729253 = 3136735) B3136735
theorem B11152835 : Blo 1957435 11152835 := bstep (se 1 (by rfl) ⟨8364626, by rfl⟩ : syracuseStep 11152835 = 16729253) B16729253
theorem B7435223 : Blo 1957435 7435223 := bstep (se 1 (by rfl) ⟨5576417, by rfl⟩ : syracuseStep 7435223 = 11152835) B11152835
theorem B4956815 : Blo 1957435 4956815 := bstep (se 1 (by rfl) ⟨3717611, by rfl⟩ : syracuseStep 4956815 = 7435223) B7435223
theorem B3304543 : Blo 1957435 3304543 := bstep (se 1 (by rfl) ⟨2478407, by rfl⟩ : syracuseStep 3304543 = 4956815) B4956815
theorem B4406057 : Blo 1957435 4406057 := bstep (se 2 (by rfl) ⟨1652271, by rfl⟩ : syracuseStep 4406057 = 3304543) B3304543
theorem B2937371 : Blo 1957435 2937371 := bstep (se 1 (by rfl) ⟨2203028, by rfl⟩ : syracuseStep 2937371 = 4406057) B4406057
theorem B1958247 : Blo 1957435 1958247 := bstep (se 1 (by rfl) ⟨1468685, by rfl⟩ : syracuseStep 1958247 = 2937371) B2937371
theorem B2203033 : Blo 1957435 2203033 := bbase (se 2 (by rfl) ⟨826137, by rfl⟩ : syracuseStep 2203033 = 1652275) (by norm_num)
theorem B2937377 : Blo 1957435 2937377 := bstep (se 2 (by rfl) ⟨1101516, by rfl⟩ : syracuseStep 2937377 = 2203033) B2203033
theorem B1958251 : Blo 1957435 1958251 := bstep (se 1 (by rfl) ⟨1468688, by rfl⟩ : syracuseStep 1958251 = 2937377) B2937377
theorem B7435253 : Blo 1957435 7435253 := bbase (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) (by norm_num)
theorem B4956835 : Blo 1957435 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B6609113 : Blo 1957435 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B4406075 : Blo 1957435 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B2937383 : Blo 1957435 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B1958255 : Blo 1957435 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B2937389 : Blo 1957435 2937389 := bbase (se 3 (by rfl) ⟨550760, by rfl⟩ : syracuseStep 2937389 = 1101521) (by norm_num)
theorem B1958259 : Blo 1957435 1958259 := bstep (se 1 (by rfl) ⟨1468694, by rfl⟩ : syracuseStep 1958259 = 2937389) B2937389
theorem B4406093 : Blo 1957435 4406093 := bbase (se 3 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 4406093 = 1652285) (by norm_num)
theorem B2937395 : Blo 1957435 2937395 := bstep (se 1 (by rfl) ⟨2203046, by rfl⟩ : syracuseStep 2937395 = 4406093) B4406093
theorem B1958263 : Blo 1957435 1958263 := bstep (se 1 (by rfl) ⟨1468697, by rfl⟩ : syracuseStep 1958263 = 2937395) B2937395
theorem B2478433 : Blo 1957435 2478433 := bbase (se 2 (by rfl) ⟨929412, by rfl⟩ : syracuseStep 2478433 = 1858825) (by norm_num)
theorem B3304577 : Blo 1957435 3304577 := bstep (se 2 (by rfl) ⟨1239216, by rfl⟩ : syracuseStep 3304577 = 2478433) B2478433
theorem B2203051 : Blo 1957435 2203051 := bstep (se 1 (by rfl) ⟨1652288, by rfl⟩ : syracuseStep 2203051 = 3304577) B3304577
theorem B2937401 : Blo 1957435 2937401 := bstep (se 2 (by rfl) ⟨1101525, by rfl⟩ : syracuseStep 2937401 = 2203051) B2203051
theorem B1958267 : Blo 1957435 1958267 := bstep (se 1 (by rfl) ⟨1468700, by rfl⟩ : syracuseStep 1958267 = 2937401) B2937401
theorem B22305941 : Blo 1957435 22305941 := bbase (se 6 (by rfl) ⟨522795, by rfl⟩ : syracuseStep 22305941 = 1045591) (by norm_num)
theorem B14870627 : Blo 1957435 14870627 := bstep (se 1 (by rfl) ⟨11152970, by rfl⟩ : syracuseStep 14870627 = 22305941) B22305941
theorem B9913751 : Blo 1957435 9913751 := bstep (se 1 (by rfl) ⟨7435313, by rfl⟩ : syracuseStep 9913751 = 14870627) B14870627
theorem B6609167 : Blo 1957435 6609167 := bstep (se 1 (by rfl) ⟨4956875, by rfl⟩ : syracuseStep 6609167 = 9913751) B9913751
theorem B4406111 : Blo 1957435 4406111 := bstep (se 1 (by rfl) ⟨3304583, by rfl⟩ : syracuseStep 4406111 = 6609167) B6609167
theorem B2937407 : Blo 1957435 2937407 := bstep (se 1 (by rfl) ⟨2203055, by rfl⟩ : syracuseStep 2937407 = 4406111) B4406111
theorem B1958271 : Blo 1957435 1958271 := bstep (se 1 (by rfl) ⟨1468703, by rfl⟩ : syracuseStep 1958271 = 2937407) B2937407
theorem B2937413 : Blo 1957435 2937413 := bbase (se 4 (by rfl) ⟨275382, by rfl⟩ : syracuseStep 2937413 = 550765) (by norm_num)
theorem B1958275 : Blo 1957435 1958275 := bstep (se 1 (by rfl) ⟨1468706, by rfl⟩ : syracuseStep 1958275 = 2937413) B2937413
theorem B3304597 : Blo 1957435 3304597 := bbase (se 6 (by rfl) ⟨77451, by rfl⟩ : syracuseStep 3304597 = 154903) (by norm_num)
theorem B4406129 : Blo 1957435 4406129 := bstep (se 2 (by rfl) ⟨1652298, by rfl⟩ : syracuseStep 4406129 = 3304597) B3304597
theorem B2937419 : Blo 1957435 2937419 := bstep (se 1 (by rfl) ⟨2203064, by rfl⟩ : syracuseStep 2937419 = 4406129) B4406129
theorem B1958279 : Blo 1957435 1958279 := bstep (se 1 (by rfl) ⟨1468709, by rfl⟩ : syracuseStep 1958279 = 2937419) B2937419
theorem B2203069 : Blo 1957435 2203069 := bbase (se 3 (by rfl) ⟨413075, by rfl⟩ : syracuseStep 2203069 = 826151) (by norm_num)
theorem B2937425 : Blo 1957435 2937425 := bstep (se 2 (by rfl) ⟨1101534, by rfl⟩ : syracuseStep 2937425 = 2203069) B2203069
theorem B1958283 : Blo 1957435 1958283 := bstep (se 1 (by rfl) ⟨1468712, by rfl⟩ : syracuseStep 1958283 = 2937425) B2937425
theorem B6609221 : Blo 1957435 6609221 := bbase (se 4 (by rfl) ⟨619614, by rfl⟩ : syracuseStep 6609221 = 1239229) (by norm_num)
theorem B4406147 : Blo 1957435 4406147 := bstep (se 1 (by rfl) ⟨3304610, by rfl⟩ : syracuseStep 4406147 = 6609221) B6609221
theorem B2937431 : Blo 1957435 2937431 := bstep (se 1 (by rfl) ⟨2203073, by rfl⟩ : syracuseStep 2937431 = 4406147) B4406147
theorem B1958287 : Blo 1957435 1958287 := bstep (se 1 (by rfl) ⟨1468715, by rfl⟩ : syracuseStep 1958287 = 2937431) B2937431
theorem B2937437 : Blo 1957435 2937437 := bbase (se 3 (by rfl) ⟨550769, by rfl⟩ : syracuseStep 2937437 = 1101539) (by norm_num)
theorem B1958291 : Blo 1957435 1958291 := bstep (se 1 (by rfl) ⟨1468718, by rfl⟩ : syracuseStep 1958291 = 2937437) B2937437
theorem B4406165 : Blo 1957435 4406165 := bbase (se 6 (by rfl) ⟨103269, by rfl⟩ : syracuseStep 4406165 = 206539) (by norm_num)
theorem B2937443 : Blo 1957435 2937443 := bstep (se 1 (by rfl) ⟨2203082, by rfl⟩ : syracuseStep 2937443 = 4406165) B4406165
theorem B1958295 : Blo 1957435 1958295 := bstep (se 1 (by rfl) ⟨1468721, by rfl⟩ : syracuseStep 1958295 = 2937443) B2937443
theorem B4705229 : Blo 1957435 4705229 := bbase (se 3 (by rfl) ⟨882230, by rfl⟩ : syracuseStep 4705229 = 1764461) (by norm_num)
theorem B3136819 : Blo 1957435 3136819 := bstep (se 1 (by rfl) ⟨2352614, by rfl⟩ : syracuseStep 3136819 = 4705229) B4705229
theorem B4182425 : Blo 1957435 4182425 := bstep (se 2 (by rfl) ⟨1568409, by rfl⟩ : syracuseStep 4182425 = 3136819) B3136819
theorem B2788283 : Blo 1957435 2788283 := bstep (se 1 (by rfl) ⟨2091212, by rfl⟩ : syracuseStep 2788283 = 4182425) B4182425
theorem B7435421 : Blo 1957435 7435421 := bstep (se 3 (by rfl) ⟨1394141, by rfl⟩ : syracuseStep 7435421 = 2788283) B2788283
theorem B4956947 : Blo 1957435 4956947 := bstep (se 1 (by rfl) ⟨3717710, by rfl⟩ : syracuseStep 4956947 = 7435421) B7435421
theorem B3304631 : Blo 1957435 3304631 := bstep (se 1 (by rfl) ⟨2478473, by rfl⟩ : syracuseStep 3304631 = 4956947) B4956947
theorem B2203087 : Blo 1957435 2203087 := bstep (se 1 (by rfl) ⟨1652315, by rfl⟩ : syracuseStep 2203087 = 3304631) B3304631
theorem B2937449 : Blo 1957435 2937449 := bstep (se 2 (by rfl) ⟨1101543, by rfl⟩ : syracuseStep 2937449 = 2203087) B2203087
theorem B1958299 : Blo 1957435 1958299 := bstep (se 1 (by rfl) ⟨1468724, by rfl⟩ : syracuseStep 1958299 = 2937449) B2937449
theorem B4705237 : Blo 1957435 4705237 := bbase (se 7 (by rfl) ⟨55139, by rfl⟩ : syracuseStep 4705237 = 110279) (by norm_num)
theorem B6273649 : Blo 1957435 6273649 := bstep (se 2 (by rfl) ⟨2352618, by rfl⟩ : syracuseStep 6273649 = 4705237) B4705237
theorem B8364865 : Blo 1957435 8364865 := bstep (se 2 (by rfl) ⟨3136824, by rfl⟩ : syracuseStep 8364865 = 6273649) B6273649
theorem B11153153 : Blo 1957435 11153153 := bstep (se 2 (by rfl) ⟨4182432, by rfl⟩ : syracuseStep 11153153 = 8364865) B8364865
theorem B7435435 : Blo 1957435 7435435 := bstep (se 1 (by rfl) ⟨5576576, by rfl⟩ : syracuseStep 7435435 = 11153153) B11153153
theorem B9913913 : Blo 1957435 9913913 := bstep (se 2 (by rfl) ⟨3717717, by rfl⟩ : syracuseStep 9913913 = 7435435) B7435435
theorem B6609275 : Blo 1957435 6609275 := bstep (se 1 (by rfl) ⟨4956956, by rfl⟩ : syracuseStep 6609275 = 9913913) B9913913
theorem B4406183 : Blo 1957435 4406183 := bstep (se 1 (by rfl) ⟨3304637, by rfl⟩ : syracuseStep 4406183 = 6609275) B6609275
theorem B2937455 : Blo 1957435 2937455 := bstep (se 1 (by rfl) ⟨2203091, by rfl⟩ : syracuseStep 2937455 = 4406183) B4406183
theorem B1958303 : Blo 1957435 1958303 := bstep (se 1 (by rfl) ⟨1468727, by rfl⟩ : syracuseStep 1958303 = 2937455) B2937455
theorem B2937461 : Blo 1957435 2937461 := bbase (se 5 (by rfl) ⟨137693, by rfl⟩ : syracuseStep 2937461 = 275387) (by norm_num)
theorem B1958307 : Blo 1957435 1958307 := bstep (se 1 (by rfl) ⟨1468730, by rfl⟩ : syracuseStep 1958307 = 2937461) B2937461
theorem B3717733 : Blo 1957435 3717733 := bbase (se 4 (by rfl) ⟨348537, by rfl⟩ : syracuseStep 3717733 = 697075) (by norm_num)
theorem B4956977 : Blo 1957435 4956977 := bstep (se 2 (by rfl) ⟨1858866, by rfl⟩ : syracuseStep 4956977 = 3717733) B3717733
theorem B3304651 : Blo 1957435 3304651 := bstep (se 1 (by rfl) ⟨2478488, by rfl⟩ : syracuseStep 3304651 = 4956977) B4956977
theorem B4406201 : Blo 1957435 4406201 := bstep (se 2 (by rfl) ⟨1652325, by rfl⟩ : syracuseStep 4406201 = 3304651) B3304651
theorem B2937467 : Blo 1957435 2937467 := bstep (se 1 (by rfl) ⟨2203100, by rfl⟩ : syracuseStep 2937467 = 4406201) B4406201
theorem B1958311 : Blo 1957435 1958311 := bstep (se 1 (by rfl) ⟨1468733, by rfl⟩ : syracuseStep 1958311 = 2937467) B2937467
theorem B2203105 : Blo 1957435 2203105 := bbase (se 2 (by rfl) ⟨826164, by rfl⟩ : syracuseStep 2203105 = 1652329) (by norm_num)
theorem B2937473 : Blo 1957435 2937473 := bstep (se 2 (by rfl) ⟨1101552, by rfl⟩ : syracuseStep 2937473 = 2203105) B2203105
theorem B1958315 : Blo 1957435 1958315 := bstep (se 1 (by rfl) ⟨1468736, by rfl⟩ : syracuseStep 1958315 = 2937473) B2937473
theorem B4956997 : Blo 1957435 4956997 := bbase (se 4 (by rfl) ⟨464718, by rfl⟩ : syracuseStep 4956997 = 929437) (by norm_num)
theorem B6609329 : Blo 1957435 6609329 := bstep (se 2 (by rfl) ⟨2478498, by rfl⟩ : syracuseStep 6609329 = 4956997) B4956997
theorem B4406219 : Blo 1957435 4406219 := bstep (se 1 (by rfl) ⟨3304664, by rfl⟩ : syracuseStep 4406219 = 6609329) B6609329
theorem B2937479 : Blo 1957435 2937479 := bstep (se 1 (by rfl) ⟨2203109, by rfl⟩ : syracuseStep 2937479 = 4406219) B4406219
theorem B1958319 : Blo 1957435 1958319 := bstep (se 1 (by rfl) ⟨1468739, by rfl⟩ : syracuseStep 1958319 = 2937479) B2937479
theorem B2937485 : Blo 1957435 2937485 := bbase (se 3 (by rfl) ⟨550778, by rfl⟩ : syracuseStep 2937485 = 1101557) (by norm_num)
theorem B1958323 : Blo 1957435 1958323 := bstep (se 1 (by rfl) ⟨1468742, by rfl⟩ : syracuseStep 1958323 = 2937485) B2937485
theorem B4406237 : Blo 1957435 4406237 := bbase (se 3 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 4406237 = 1652339) (by norm_num)
theorem B2937491 : Blo 1957435 2937491 := bstep (se 1 (by rfl) ⟨2203118, by rfl⟩ : syracuseStep 2937491 = 4406237) B4406237
theorem B1958327 : Blo 1957435 1958327 := bstep (se 1 (by rfl) ⟨1468745, by rfl⟩ : syracuseStep 1958327 = 2937491) B2937491
theorem B3304685 : Blo 1957435 3304685 := bbase (se 3 (by rfl) ⟨619628, by rfl⟩ : syracuseStep 3304685 = 1239257) (by norm_num)
theorem B2203123 : Blo 1957435 2203123 := bstep (se 1 (by rfl) ⟨1652342, by rfl⟩ : syracuseStep 2203123 = 3304685) B3304685
theorem B2937497 : Blo 1957435 2937497 := bstep (se 2 (by rfl) ⟨1101561, by rfl⟩ : syracuseStep 2937497 = 2203123) B2203123
theorem B1958331 : Blo 1957435 1958331 := bstep (se 1 (by rfl) ⟨1468748, by rfl⟩ : syracuseStep 1958331 = 2937497) B2937497
theorem B3970109 : Blo 1957435 3970109 := bbase (se 3 (by rfl) ⟨744395, by rfl⟩ : syracuseStep 3970109 = 1488791) (by norm_num)
theorem B2646739 : Blo 1957435 2646739 := bstep (se 1 (by rfl) ⟨1985054, by rfl⟩ : syracuseStep 2646739 = 3970109) B3970109
theorem B14115941 : Blo 1957435 14115941 := bstep (se 4 (by rfl) ⟨1323369, by rfl⟩ : syracuseStep 14115941 = 2646739) B2646739
theorem B9410627 : Blo 1957435 9410627 := bstep (se 1 (by rfl) ⟨7057970, by rfl⟩ : syracuseStep 9410627 = 14115941) B14115941
theorem B25095005 : Blo 1957435 25095005 := bstep (se 3 (by rfl) ⟨4705313, by rfl⟩ : syracuseStep 25095005 = 9410627) B9410627
theorem B16730003 : Blo 1957435 16730003 := bstep (se 1 (by rfl) ⟨12547502, by rfl⟩ : syracuseStep 16730003 = 25095005) B25095005
theorem B11153335 : Blo 1957435 11153335 := bstep (se 1 (by rfl) ⟨8365001, by rfl⟩ : syracuseStep 11153335 = 16730003) B16730003
theorem B14871113 : Blo 1957435 14871113 := bstep (se 2 (by rfl) ⟨5576667, by rfl⟩ : syracuseStep 14871113 = 11153335) B11153335
theorem B9914075 : Blo 1957435 9914075 := bstep (se 1 (by rfl) ⟨7435556, by rfl⟩ : syracuseStep 9914075 = 14871113) B14871113
theorem B6609383 : Blo 1957435 6609383 := bstep (se 1 (by rfl) ⟨4957037, by rfl⟩ : syracuseStep 6609383 = 9914075) B9914075
theorem B4406255 : Blo 1957435 4406255 := bstep (se 1 (by rfl) ⟨3304691, by rfl⟩ : syracuseStep 4406255 = 6609383) B6609383
theorem B2937503 : Blo 1957435 2937503 := bstep (se 1 (by rfl) ⟨2203127, by rfl⟩ : syracuseStep 2937503 = 4406255) B4406255
theorem B1958335 : Blo 1957435 1958335 := bstep (se 1 (by rfl) ⟨1468751, by rfl⟩ : syracuseStep 1958335 = 2937503) B2937503
theorem B2937509 : Blo 1957435 2937509 := bbase (se 4 (by rfl) ⟨275391, by rfl⟩ : syracuseStep 2937509 = 550783) (by norm_num)
theorem B1958339 : Blo 1957435 1958339 := bstep (se 1 (by rfl) ⟨1468754, by rfl⟩ : syracuseStep 1958339 = 2937509) B2937509
theorem B2478529 : Blo 1957435 2478529 := bbase (se 2 (by rfl) ⟨929448, by rfl⟩ : syracuseStep 2478529 = 1858897) (by norm_num)
theorem B3304705 : Blo 1957435 3304705 := bstep (se 2 (by rfl) ⟨1239264, by rfl⟩ : syracuseStep 3304705 = 2478529) B2478529
theorem B4406273 : Blo 1957435 4406273 := bstep (se 2 (by rfl) ⟨1652352, by rfl⟩ : syracuseStep 4406273 = 3304705) B3304705
theorem B2937515 : Blo 1957435 2937515 := bstep (se 1 (by rfl) ⟨2203136, by rfl⟩ : syracuseStep 2937515 = 4406273) B4406273
theorem B1958343 : Blo 1957435 1958343 := bstep (se 1 (by rfl) ⟨1468757, by rfl⟩ : syracuseStep 1958343 = 2937515) B2937515
theorem B2203141 : Blo 1957435 2203141 := bbase (se 4 (by rfl) ⟨206544, by rfl⟩ : syracuseStep 2203141 = 413089) (by norm_num)
theorem B2937521 : Blo 1957435 2937521 := bstep (se 2 (by rfl) ⟨1101570, by rfl⟩ : syracuseStep 2937521 = 2203141) B2203141
theorem B1958347 : Blo 1957435 1958347 := bstep (se 1 (by rfl) ⟨1468760, by rfl⟩ : syracuseStep 1958347 = 2937521) B2937521
theorem B2788357 : Blo 1957435 2788357 := bbase (se 4 (by rfl) ⟨261408, by rfl⟩ : syracuseStep 2788357 = 522817) (by norm_num)
theorem B3717809 : Blo 1957435 3717809 := bstep (se 2 (by rfl) ⟨1394178, by rfl⟩ : syracuseStep 3717809 = 2788357) B2788357
theorem B2478539 : Blo 1957435 2478539 := bstep (se 1 (by rfl) ⟨1858904, by rfl⟩ : syracuseStep 2478539 = 3717809) B3717809
theorem B6609437 : Blo 1957435 6609437 := bstep (se 3 (by rfl) ⟨1239269, by rfl⟩ : syracuseStep 6609437 = 2478539) B2478539
theorem B4406291 : Blo 1957435 4406291 := bstep (se 1 (by rfl) ⟨3304718, by rfl⟩ : syracuseStep 4406291 = 6609437) B6609437
theorem B2937527 : Blo 1957435 2937527 := bstep (se 1 (by rfl) ⟨2203145, by rfl⟩ : syracuseStep 2937527 = 4406291) B4406291
theorem B1958351 : Blo 1957435 1958351 := bstep (se 1 (by rfl) ⟨1468763, by rfl⟩ : syracuseStep 1958351 = 2937527) B2937527
theorem B2937533 : Blo 1957435 2937533 := bbase (se 3 (by rfl) ⟨550787, by rfl⟩ : syracuseStep 2937533 = 1101575) (by norm_num)
theorem B1958355 : Blo 1957435 1958355 := bstep (se 1 (by rfl) ⟨1468766, by rfl⟩ : syracuseStep 1958355 = 2937533) B2937533
theorem B4406309 : Blo 1957435 4406309 := bbase (se 4 (by rfl) ⟨413091, by rfl⟩ : syracuseStep 4406309 = 826183) (by norm_num)
theorem B2937539 : Blo 1957435 2937539 := bstep (se 1 (by rfl) ⟨2203154, by rfl⟩ : syracuseStep 2937539 = 4406309) B4406309
theorem B1958359 : Blo 1957435 1958359 := bstep (se 1 (by rfl) ⟨1468769, by rfl⟩ : syracuseStep 1958359 = 2937539) B2937539
theorem B4957109 : Blo 1957435 4957109 := bbase (se 5 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 4957109 = 464729) (by norm_num)
theorem B3304739 : Blo 1957435 3304739 := bstep (se 1 (by rfl) ⟨2478554, by rfl⟩ : syracuseStep 3304739 = 4957109) B4957109
theorem B2203159 : Blo 1957435 2203159 := bstep (se 1 (by rfl) ⟨1652369, by rfl⟩ : syracuseStep 2203159 = 3304739) B3304739
theorem B2937545 : Blo 1957435 2937545 := bstep (se 2 (by rfl) ⟨1101579, by rfl⟩ : syracuseStep 2937545 = 2203159) B2203159
theorem B1958363 : Blo 1957435 1958363 := bstep (se 1 (by rfl) ⟨1468772, by rfl⟩ : syracuseStep 1958363 = 2937545) B2937545
theorem B9054773 : Blo 1957435 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B6036515 : Blo 1957435 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B4024343 : Blo 1957435 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B2682895 : Blo 1957435 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B3577193 : Blo 1957435 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B2384795 : Blo 1957435 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B6359453 : Blo 1957435 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B4239635 : Blo 1957435 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B11305693 : Blo 1957435 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B15074257 : Blo 1957435 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B20099009 : Blo 1957435 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B13399339 : Blo 1957435 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B17865785 : Blo 1957435 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B11910523 : Blo 1957435 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B15880697 : Blo 1957435 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B10587131 : Blo 1957435 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B7058087 : Blo 1957435 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B4705391 : Blo 1957435 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B12547709 : Blo 1957435 12547709 := bstep (se 3 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 12547709 = 4705391) B4705391
theorem B8365139 : Blo 1957435 8365139 := bstep (se 1 (by rfl) ⟨6273854, by rfl⟩ : syracuseStep 8365139 = 12547709) B12547709
theorem B5576759 : Blo 1957435 5576759 := bstep (se 1 (by rfl) ⟨4182569, by rfl⟩ : syracuseStep 5576759 = 8365139) B8365139
theorem B3717839 : Blo 1957435 3717839 := bstep (se 1 (by rfl) ⟨2788379, by rfl⟩ : syracuseStep 3717839 = 5576759) B5576759
theorem B9914237 : Blo 1957435 9914237 := bstep (se 3 (by rfl) ⟨1858919, by rfl⟩ : syracuseStep 9914237 = 3717839) B3717839
theorem B6609491 : Blo 1957435 6609491 := bstep (se 1 (by rfl) ⟨4957118, by rfl⟩ : syracuseStep 6609491 = 9914237) B9914237
theorem B4406327 : Blo 1957435 4406327 := bstep (se 1 (by rfl) ⟨3304745, by rfl⟩ : syracuseStep 4406327 = 6609491) B6609491
theorem B2937551 : Blo 1957435 2937551 := bstep (se 1 (by rfl) ⟨2203163, by rfl⟩ : syracuseStep 2937551 = 4406327) B4406327
theorem B1958367 : Blo 1957435 1958367 := bstep (se 1 (by rfl) ⟨1468775, by rfl⟩ : syracuseStep 1958367 = 2937551) B2937551
theorem B2937557 : Blo 1957435 2937557 := bbase (se 7 (by rfl) ⟨34424, by rfl⟩ : syracuseStep 2937557 = 68849) (by norm_num)
theorem B1958371 : Blo 1957435 1958371 := bstep (se 1 (by rfl) ⟨1468778, by rfl⟩ : syracuseStep 1958371 = 2937557) B2937557
theorem B7058117 : Blo 1957435 7058117 := bbase (se 4 (by rfl) ⟨661698, by rfl⟩ : syracuseStep 7058117 = 1323397) (by norm_num)
theorem B4705411 : Blo 1957435 4705411 := bstep (se 1 (by rfl) ⟨3529058, by rfl⟩ : syracuseStep 4705411 = 7058117) B7058117
theorem B6273881 : Blo 1957435 6273881 := bstep (se 2 (by rfl) ⟨2352705, by rfl⟩ : syracuseStep 6273881 = 4705411) B4705411
theorem B4182587 : Blo 1957435 4182587 := bstep (se 1 (by rfl) ⟨3136940, by rfl⟩ : syracuseStep 4182587 = 6273881) B6273881
theorem B2788391 : Blo 1957435 2788391 := bstep (se 1 (by rfl) ⟨2091293, by rfl⟩ : syracuseStep 2788391 = 4182587) B4182587
theorem B7435709 : Blo 1957435 7435709 := bstep (se 3 (by rfl) ⟨1394195, by rfl⟩ : syracuseStep 7435709 = 2788391) B2788391
theorem B4957139 : Blo 1957435 4957139 := bstep (se 1 (by rfl) ⟨3717854, by rfl⟩ : syracuseStep 4957139 = 7435709) B7435709
theorem B3304759 : Blo 1957435 3304759 := bstep (se 1 (by rfl) ⟨2478569, by rfl⟩ : syracuseStep 3304759 = 4957139) B4957139
theorem B4406345 : Blo 1957435 4406345 := bstep (se 2 (by rfl) ⟨1652379, by rfl⟩ : syracuseStep 4406345 = 3304759) B3304759
theorem B2937563 : Blo 1957435 2937563 := bstep (se 1 (by rfl) ⟨2203172, by rfl⟩ : syracuseStep 2937563 = 4406345) B4406345
theorem B1958375 : Blo 1957435 1958375 := bstep (se 1 (by rfl) ⟨1468781, by rfl⟩ : syracuseStep 1958375 = 2937563) B2937563
theorem B2203177 : Blo 1957435 2203177 := bbase (se 2 (by rfl) ⟨826191, by rfl⟩ : syracuseStep 2203177 = 1652383) (by norm_num)
theorem B2937569 : Blo 1957435 2937569 := bstep (se 2 (by rfl) ⟨1101588, by rfl⟩ : syracuseStep 2937569 = 2203177) B2203177
theorem B1958379 : Blo 1957435 1958379 := bstep (se 1 (by rfl) ⟨1468784, by rfl⟩ : syracuseStep 1958379 = 2937569) B2937569
theorem B18821717 : Blo 1957435 18821717 := bbase (se 8 (by rfl) ⟨110283, by rfl⟩ : syracuseStep 18821717 = 220567) (by norm_num)
theorem B12547811 : Blo 1957435 12547811 := bstep (se 1 (by rfl) ⟨9410858, by rfl⟩ : syracuseStep 12547811 = 18821717) B18821717
theorem B8365207 : Blo 1957435 8365207 := bstep (se 1 (by rfl) ⟨6273905, by rfl⟩ : syracuseStep 8365207 = 12547811) B12547811
theorem B11153609 : Blo 1957435 11153609 := bstep (se 2 (by rfl) ⟨4182603, by rfl⟩ : syracuseStep 11153609 = 8365207) B8365207
theorem B7435739 : Blo 1957435 7435739 := bstep (se 1 (by rfl) ⟨5576804, by rfl⟩ : syracuseStep 7435739 = 11153609) B11153609
theorem B4957159 : Blo 1957435 4957159 := bstep (se 1 (by rfl) ⟨3717869, by rfl⟩ : syracuseStep 4957159 = 7435739) B7435739
theorem B6609545 : Blo 1957435 6609545 := bstep (se 2 (by rfl) ⟨2478579, by rfl⟩ : syracuseStep 6609545 = 4957159) B4957159
theorem B4406363 : Blo 1957435 4406363 := bstep (se 1 (by rfl) ⟨3304772, by rfl⟩ : syracuseStep 4406363 = 6609545) B6609545
theorem B2937575 : Blo 1957435 2937575 := bstep (se 1 (by rfl) ⟨2203181, by rfl⟩ : syracuseStep 2937575 = 4406363) B4406363
theorem B1958383 : Blo 1957435 1958383 := bstep (se 1 (by rfl) ⟨1468787, by rfl⟩ : syracuseStep 1958383 = 2937575) B2937575
theorem B2937581 : Blo 1957435 2937581 := bbase (se 3 (by rfl) ⟨550796, by rfl⟩ : syracuseStep 2937581 = 1101593) (by norm_num)
theorem B1958387 : Blo 1957435 1958387 := bstep (se 1 (by rfl) ⟨1468790, by rfl⟩ : syracuseStep 1958387 = 2937581) B2937581
theorem B4406381 : Blo 1957435 4406381 := bbase (se 3 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 4406381 = 1652393) (by norm_num)
theorem B2937587 : Blo 1957435 2937587 := bstep (se 1 (by rfl) ⟨2203190, by rfl⟩ : syracuseStep 2937587 = 4406381) B4406381
theorem B1958391 : Blo 1957435 1958391 := bstep (se 1 (by rfl) ⟨1468793, by rfl⟩ : syracuseStep 1958391 = 2937587) B2937587
theorem B3717893 : Blo 1957435 3717893 := bbase (se 4 (by rfl) ⟨348552, by rfl⟩ : syracuseStep 3717893 = 697105) (by norm_num)
theorem B2478595 : Blo 1957435 2478595 := bstep (se 1 (by rfl) ⟨1858946, by rfl⟩ : syracuseStep 2478595 = 3717893) B3717893
theorem B3304793 : Blo 1957435 3304793 := bstep (se 2 (by rfl) ⟨1239297, by rfl⟩ : syracuseStep 3304793 = 2478595) B2478595
theorem B2203195 : Blo 1957435 2203195 := bstep (se 1 (by rfl) ⟨1652396, by rfl⟩ : syracuseStep 2203195 = 3304793) B3304793
theorem B2937593 : Blo 1957435 2937593 := bstep (se 2 (by rfl) ⟨1101597, by rfl⟩ : syracuseStep 2937593 = 2203195) B2203195
theorem B1958395 : Blo 1957435 1958395 := bstep (se 1 (by rfl) ⟨1468796, by rfl⟩ : syracuseStep 1958395 = 2937593) B2937593
theorem B10049669 : Blo 1957435 10049669 := bbase (se 4 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 10049669 = 1884313) (by norm_num)
theorem B6699779 : Blo 1957435 6699779 := bstep (se 1 (by rfl) ⟨5024834, by rfl⟩ : syracuseStep 6699779 = 10049669) B10049669
theorem B4466519 : Blo 1957435 4466519 := bstep (se 1 (by rfl) ⟨3349889, by rfl⟩ : syracuseStep 4466519 = 6699779) B6699779
theorem B2977679 : Blo 1957435 2977679 := bstep (se 1 (by rfl) ⟨2233259, by rfl⟩ : syracuseStep 2977679 = 4466519) B4466519
theorem B1985119 : Blo 1957435 1985119 := bstep (se 1 (by rfl) ⟨1488839, by rfl⟩ : syracuseStep 1985119 = 2977679) B2977679
theorem B42349205 : Blo 1957435 42349205 := bstep (se 6 (by rfl) ⟨992559, by rfl⟩ : syracuseStep 42349205 = 1985119) B1985119
theorem B28232803 : Blo 1957435 28232803 := bstep (se 1 (by rfl) ⟨21174602, by rfl⟩ : syracuseStep 28232803 = 42349205) B42349205
theorem B37643737 : Blo 1957435 37643737 := bstep (se 2 (by rfl) ⟨14116401, by rfl⟩ : syracuseStep 37643737 = 28232803) B28232803
theorem B50191649 : Blo 1957435 50191649 := bstep (se 2 (by rfl) ⟨18821868, by rfl⟩ : syracuseStep 50191649 = 37643737) B37643737
theorem B33461099 : Blo 1957435 33461099 := bstep (se 1 (by rfl) ⟨25095824, by rfl⟩ : syracuseStep 33461099 = 50191649) B50191649
theorem B22307399 : Blo 1957435 22307399 := bstep (se 1 (by rfl) ⟨16730549, by rfl⟩ : syracuseStep 22307399 = 33461099) B33461099
theorem B14871599 : Blo 1957435 14871599 := bstep (se 1 (by rfl) ⟨11153699, by rfl⟩ : syracuseStep 14871599 = 22307399) B22307399
theorem B9914399 : Blo 1957435 9914399 := bstep (se 1 (by rfl) ⟨7435799, by rfl⟩ : syracuseStep 9914399 = 14871599) B14871599
theorem B6609599 : Blo 1957435 6609599 := bstep (se 1 (by rfl) ⟨4957199, by rfl⟩ : syracuseStep 6609599 = 9914399) B9914399
theorem B4406399 : Blo 1957435 4406399 := bstep (se 1 (by rfl) ⟨3304799, by rfl⟩ : syracuseStep 4406399 = 6609599) B6609599
theorem B2937599 : Blo 1957435 2937599 := bstep (se 1 (by rfl) ⟨2203199, by rfl⟩ : syracuseStep 2937599 = 4406399) B4406399
theorem B1958399 : Blo 1957435 1958399 := bstep (se 1 (by rfl) ⟨1468799, by rfl⟩ : syracuseStep 1958399 = 2937599) B2937599
theorem B2937605 : Blo 1957435 2937605 := bbase (se 4 (by rfl) ⟨275400, by rfl⟩ : syracuseStep 2937605 = 550801) (by norm_num)
theorem B1958403 : Blo 1957435 1958403 := bstep (se 1 (by rfl) ⟨1468802, by rfl⟩ : syracuseStep 1958403 = 2937605) B2937605
theorem B3304813 : Blo 1957435 3304813 := bbase (se 3 (by rfl) ⟨619652, by rfl⟩ : syracuseStep 3304813 = 1239305) (by norm_num)
theorem B4406417 : Blo 1957435 4406417 := bstep (se 2 (by rfl) ⟨1652406, by rfl⟩ : syracuseStep 4406417 = 3304813) B3304813
theorem B2937611 : Blo 1957435 2937611 := bstep (se 1 (by rfl) ⟨2203208, by rfl⟩ : syracuseStep 2937611 = 4406417) B4406417
theorem B1958407 : Blo 1957435 1958407 := bstep (se 1 (by rfl) ⟨1468805, by rfl⟩ : syracuseStep 1958407 = 2937611) B2937611
theorem B2203213 : Blo 1957435 2203213 := bbase (se 3 (by rfl) ⟨413102, by rfl⟩ : syracuseStep 2203213 = 826205) (by norm_num)
theorem B2937617 : Blo 1957435 2937617 := bstep (se 2 (by rfl) ⟨1101606, by rfl⟩ : syracuseStep 2937617 = 2203213) B2203213
theorem B1958411 : Blo 1957435 1958411 := bstep (se 1 (by rfl) ⟨1468808, by rfl⟩ : syracuseStep 1958411 = 2937617) B2937617
theorem B6609653 : Blo 1957435 6609653 := bbase (se 5 (by rfl) ⟨309827, by rfl⟩ : syracuseStep 6609653 = 619655) (by norm_num)
theorem B4406435 : Blo 1957435 4406435 := bstep (se 1 (by rfl) ⟨3304826, by rfl⟩ : syracuseStep 4406435 = 6609653) B6609653
theorem B2937623 : Blo 1957435 2937623 := bstep (se 1 (by rfl) ⟨2203217, by rfl⟩ : syracuseStep 2937623 = 4406435) B4406435
theorem B1958415 : Blo 1957435 1958415 := bstep (se 1 (by rfl) ⟨1468811, by rfl⟩ : syracuseStep 1958415 = 2937623) B2937623
theorem B2937629 : Blo 1957435 2937629 := bbase (se 3 (by rfl) ⟨550805, by rfl⟩ : syracuseStep 2937629 = 1101611) (by norm_num)
theorem B1958419 : Blo 1957435 1958419 := bstep (se 1 (by rfl) ⟨1468814, by rfl⟩ : syracuseStep 1958419 = 2937629) B2937629
theorem B4406453 : Blo 1957435 4406453 := bbase (se 5 (by rfl) ⟨206552, by rfl⟩ : syracuseStep 4406453 = 413105) (by norm_num)
theorem B2937635 : Blo 1957435 2937635 := bstep (se 1 (by rfl) ⟨2203226, by rfl⟩ : syracuseStep 2937635 = 4406453) B4406453
theorem B1958423 : Blo 1957435 1958423 := bstep (se 1 (by rfl) ⟨1468817, by rfl⟩ : syracuseStep 1958423 = 2937635) B2937635
theorem B2091349 : Blo 1957435 2091349 := bbase (se 10 (by rfl) ⟨3063, by rfl⟩ : syracuseStep 2091349 = 6127) (by norm_num)
theorem B11153861 : Blo 1957435 11153861 := bstep (se 4 (by rfl) ⟨1045674, by rfl⟩ : syracuseStep 11153861 = 2091349) B2091349
theorem B7435907 : Blo 1957435 7435907 := bstep (se 1 (by rfl) ⟨5576930, by rfl⟩ : syracuseStep 7435907 = 11153861) B11153861
theorem B4957271 : Blo 1957435 4957271 := bstep (se 1 (by rfl) ⟨3717953, by rfl⟩ : syracuseStep 4957271 = 7435907) B7435907
theorem B3304847 : Blo 1957435 3304847 := bstep (se 1 (by rfl) ⟨2478635, by rfl⟩ : syracuseStep 3304847 = 4957271) B4957271
theorem B2203231 : Blo 1957435 2203231 := bstep (se 1 (by rfl) ⟨1652423, by rfl⟩ : syracuseStep 2203231 = 3304847) B3304847
theorem B2937641 : Blo 1957435 2937641 := bstep (se 2 (by rfl) ⟨1101615, by rfl⟩ : syracuseStep 2937641 = 2203231) B2203231
theorem B1958427 : Blo 1957435 1958427 := bstep (se 1 (by rfl) ⟨1468820, by rfl⟩ : syracuseStep 1958427 = 2937641) B2937641
theorem B2091353 : Blo 1957435 2091353 := bbase (se 2 (by rfl) ⟨784257, by rfl⟩ : syracuseStep 2091353 = 1568515) (by norm_num)
theorem B5576941 : Blo 1957435 5576941 := bstep (se 3 (by rfl) ⟨1045676, by rfl⟩ : syracuseStep 5576941 = 2091353) B2091353
theorem B7435921 : Blo 1957435 7435921 := bstep (se 2 (by rfl) ⟨2788470, by rfl⟩ : syracuseStep 7435921 = 5576941) B5576941
theorem B9914561 : Blo 1957435 9914561 := bstep (se 2 (by rfl) ⟨3717960, by rfl⟩ : syracuseStep 9914561 = 7435921) B7435921
theorem B6609707 : Blo 1957435 6609707 := bstep (se 1 (by rfl) ⟨4957280, by rfl⟩ : syracuseStep 6609707 = 9914561) B9914561
theorem B4406471 : Blo 1957435 4406471 := bstep (se 1 (by rfl) ⟨3304853, by rfl⟩ : syracuseStep 4406471 = 6609707) B6609707
theorem B2937647 : Blo 1957435 2937647 := bstep (se 1 (by rfl) ⟨2203235, by rfl⟩ : syracuseStep 2937647 = 4406471) B4406471
theorem B1958431 : Blo 1957435 1958431 := bstep (se 1 (by rfl) ⟨1468823, by rfl⟩ : syracuseStep 1958431 = 2937647) B2937647
theorem B2937653 : Blo 1957435 2937653 := bbase (se 5 (by rfl) ⟨137702, by rfl⟩ : syracuseStep 2937653 = 275405) (by norm_num)
theorem B1958435 : Blo 1957435 1958435 := bstep (se 1 (by rfl) ⟨1468826, by rfl⟩ : syracuseStep 1958435 = 2937653) B2937653
theorem B4957301 : Blo 1957435 4957301 := bbase (se 5 (by rfl) ⟨232373, by rfl⟩ : syracuseStep 4957301 = 464747) (by norm_num)
theorem B3304867 : Blo 1957435 3304867 := bstep (se 1 (by rfl) ⟨2478650, by rfl⟩ : syracuseStep 3304867 = 4957301) B4957301
theorem B4406489 : Blo 1957435 4406489 := bstep (se 2 (by rfl) ⟨1652433, by rfl⟩ : syracuseStep 4406489 = 3304867) B3304867
theorem B2937659 : Blo 1957435 2937659 := bstep (se 1 (by rfl) ⟨2203244, by rfl⟩ : syracuseStep 2937659 = 4406489) B4406489
theorem B1958439 : Blo 1957435 1958439 := bstep (se 1 (by rfl) ⟨1468829, by rfl⟩ : syracuseStep 1958439 = 2937659) B2937659
theorem B2203249 : Blo 1957435 2203249 := bbase (se 2 (by rfl) ⟨826218, by rfl⟩ : syracuseStep 2203249 = 1652437) (by norm_num)
theorem B2937665 : Blo 1957435 2937665 := bstep (se 2 (by rfl) ⟨1101624, by rfl⟩ : syracuseStep 2937665 = 2203249) B2203249
theorem B1958443 : Blo 1957435 1958443 := bstep (se 1 (by rfl) ⟨1468832, by rfl⟩ : syracuseStep 1958443 = 2937665) B2937665
theorem B7154677 : Blo 1957435 7154677 := bbase (se 5 (by rfl) ⟨335375, by rfl⟩ : syracuseStep 7154677 = 670751) (by norm_num)
theorem B9539569 : Blo 1957435 9539569 := bstep (se 2 (by rfl) ⟨3577338, by rfl⟩ : syracuseStep 9539569 = 7154677) B7154677
theorem B12719425 : Blo 1957435 12719425 := bstep (se 2 (by rfl) ⟨4769784, by rfl⟩ : syracuseStep 12719425 = 9539569) B9539569
theorem B16959233 : Blo 1957435 16959233 := bstep (se 2 (by rfl) ⟨6359712, by rfl⟩ : syracuseStep 16959233 = 12719425) B12719425
theorem B11306155 : Blo 1957435 11306155 := bstep (se 1 (by rfl) ⟨8479616, by rfl⟩ : syracuseStep 11306155 = 16959233) B16959233
theorem B15074873 : Blo 1957435 15074873 := bstep (se 2 (by rfl) ⟨5653077, by rfl⟩ : syracuseStep 15074873 = 11306155) B11306155
theorem B10049915 : Blo 1957435 10049915 := bstep (se 1 (by rfl) ⟨7537436, by rfl⟩ : syracuseStep 10049915 = 15074873) B15074873
theorem B6699943 : Blo 1957435 6699943 := bstep (se 1 (by rfl) ⟨5024957, by rfl⟩ : syracuseStep 6699943 = 10049915) B10049915
theorem B8933257 : Blo 1957435 8933257 := bstep (se 2 (by rfl) ⟨3349971, by rfl⟩ : syracuseStep 8933257 = 6699943) B6699943
theorem B47644037 : Blo 1957435 47644037 := bstep (se 4 (by rfl) ⟨4466628, by rfl⟩ : syracuseStep 47644037 = 8933257) B8933257
theorem B31762691 : Blo 1957435 31762691 := bstep (se 1 (by rfl) ⟨23822018, by rfl⟩ : syracuseStep 31762691 = 47644037) B47644037
theorem B21175127 : Blo 1957435 21175127 := bstep (se 1 (by rfl) ⟨15881345, by rfl⟩ : syracuseStep 21175127 = 31762691) B31762691
theorem B14116751 : Blo 1957435 14116751 := bstep (se 1 (by rfl) ⟨10587563, by rfl⟩ : syracuseStep 14116751 = 21175127) B21175127
theorem B9411167 : Blo 1957435 9411167 := bstep (se 1 (by rfl) ⟨7058375, by rfl⟩ : syracuseStep 9411167 = 14116751) B14116751
theorem B6274111 : Blo 1957435 6274111 := bstep (se 1 (by rfl) ⟨4705583, by rfl⟩ : syracuseStep 6274111 = 9411167) B9411167
theorem B8365481 : Blo 1957435 8365481 := bstep (se 2 (by rfl) ⟨3137055, by rfl⟩ : syracuseStep 8365481 = 6274111) B6274111
theorem B5576987 : Blo 1957435 5576987 := bstep (se 1 (by rfl) ⟨4182740, by rfl⟩ : syracuseStep 5576987 = 8365481) B8365481
theorem B3717991 : Blo 1957435 3717991 := bstep (se 1 (by rfl) ⟨2788493, by rfl⟩ : syracuseStep 3717991 = 5576987) B5576987
theorem B4957321 : Blo 1957435 4957321 := bstep (se 2 (by rfl) ⟨1858995, by rfl⟩ : syracuseStep 4957321 = 3717991) B3717991
theorem B6609761 : Blo 1957435 6609761 := bstep (se 2 (by rfl) ⟨2478660, by rfl⟩ : syracuseStep 6609761 = 4957321) B4957321
theorem B4406507 : Blo 1957435 4406507 := bstep (se 1 (by rfl) ⟨3304880, by rfl⟩ : syracuseStep 4406507 = 6609761) B6609761
theorem B2937671 : Blo 1957435 2937671 := bstep (se 1 (by rfl) ⟨2203253, by rfl⟩ : syracuseStep 2937671 = 4406507) B4406507
theorem B1958447 : Blo 1957435 1958447 := bstep (se 1 (by rfl) ⟨1468835, by rfl⟩ : syracuseStep 1958447 = 2937671) B2937671
theorem B2937677 : Blo 1957435 2937677 := bbase (se 3 (by rfl) ⟨550814, by rfl⟩ : syracuseStep 2937677 = 1101629) (by norm_num)
theorem B1958451 : Blo 1957435 1958451 := bstep (se 1 (by rfl) ⟨1468838, by rfl⟩ : syracuseStep 1958451 = 2937677) B2937677
theorem B4406525 : Blo 1957435 4406525 := bbase (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) (by norm_num)
theorem B2937683 : Blo 1957435 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B1958455 : Blo 1957435 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B3304901 : Blo 1957435 3304901 := bbase (se 4 (by rfl) ⟨309834, by rfl⟩ : syracuseStep 3304901 = 619669) (by norm_num)
theorem B2203267 : Blo 1957435 2203267 := bstep (se 1 (by rfl) ⟨1652450, by rfl⟩ : syracuseStep 2203267 = 3304901) B3304901
theorem B2937689 : Blo 1957435 2937689 := bstep (se 2 (by rfl) ⟨1101633, by rfl⟩ : syracuseStep 2937689 = 2203267) B2203267
theorem B1958459 : Blo 1957435 1958459 := bstep (se 1 (by rfl) ⟨1468844, by rfl⟩ : syracuseStep 1958459 = 2937689) B2937689
theorem B14872085 : Blo 1957435 14872085 := bbase (se 6 (by rfl) ⟨348564, by rfl⟩ : syracuseStep 14872085 = 697129) (by norm_num)
theorem B9914723 : Blo 1957435 9914723 := bstep (se 1 (by rfl) ⟨7436042, by rfl⟩ : syracuseStep 9914723 = 14872085) B14872085
theorem B6609815 : Blo 1957435 6609815 := bstep (se 1 (by rfl) ⟨4957361, by rfl⟩ : syracuseStep 6609815 = 9914723) B9914723
theorem B4406543 : Blo 1957435 4406543 := bstep (se 1 (by rfl) ⟨3304907, by rfl⟩ : syracuseStep 4406543 = 6609815) B6609815
theorem B2937695 : Blo 1957435 2937695 := bstep (se 1 (by rfl) ⟨2203271, by rfl⟩ : syracuseStep 2937695 = 4406543) B4406543
theorem B1958463 : Blo 1957435 1958463 := bstep (se 1 (by rfl) ⟨1468847, by rfl⟩ : syracuseStep 1958463 = 2937695) B2937695
theorem B2937701 : Blo 1957435 2937701 := bbase (se 4 (by rfl) ⟨275409, by rfl⟩ : syracuseStep 2937701 = 550819) (by norm_num)
theorem B1958467 : Blo 1957435 1958467 := bstep (se 1 (by rfl) ⟨1468850, by rfl⟩ : syracuseStep 1958467 = 2937701) B2937701
theorem B3718037 : Blo 1957435 3718037 := bbase (se 6 (by rfl) ⟨87141, by rfl⟩ : syracuseStep 3718037 = 174283) (by norm_num)
theorem B2478691 : Blo 1957435 2478691 := bstep (se 1 (by rfl) ⟨1859018, by rfl⟩ : syracuseStep 2478691 = 3718037) B3718037
theorem B3304921 : Blo 1957435 3304921 := bstep (se 2 (by rfl) ⟨1239345, by rfl⟩ : syracuseStep 3304921 = 2478691) B2478691
theorem B4406561 : Blo 1957435 4406561 := bstep (se 2 (by rfl) ⟨1652460, by rfl⟩ : syracuseStep 4406561 = 3304921) B3304921
theorem B2937707 : Blo 1957435 2937707 := bstep (se 1 (by rfl) ⟨2203280, by rfl⟩ : syracuseStep 2937707 = 4406561) B4406561
theorem B1958471 : Blo 1957435 1958471 := bstep (se 1 (by rfl) ⟨1468853, by rfl⟩ : syracuseStep 1958471 = 2937707) B2937707
theorem B2203285 : Blo 1957435 2203285 := bbase (se 6 (by rfl) ⟨51639, by rfl⟩ : syracuseStep 2203285 = 103279) (by norm_num)
theorem B2937713 : Blo 1957435 2937713 := bstep (se 2 (by rfl) ⟨1101642, by rfl⟩ : syracuseStep 2937713 = 2203285) B2203285
theorem B1958475 : Blo 1957435 1958475 := bstep (se 1 (by rfl) ⟨1468856, by rfl⟩ : syracuseStep 1958475 = 2937713) B2937713
theorem B2478701 : Blo 1957435 2478701 := bbase (se 3 (by rfl) ⟨464756, by rfl⟩ : syracuseStep 2478701 = 929513) (by norm_num)
theorem B6609869 : Blo 1957435 6609869 := bstep (se 3 (by rfl) ⟨1239350, by rfl⟩ : syracuseStep 6609869 = 2478701) B2478701
theorem B4406579 : Blo 1957435 4406579 := bstep (se 1 (by rfl) ⟨3304934, by rfl⟩ : syracuseStep 4406579 = 6609869) B6609869
theorem B2937719 : Blo 1957435 2937719 := bstep (se 1 (by rfl) ⟨2203289, by rfl⟩ : syracuseStep 2937719 = 4406579) B4406579
theorem B1958479 : Blo 1957435 1958479 := bstep (se 1 (by rfl) ⟨1468859, by rfl⟩ : syracuseStep 1958479 = 2937719) B2937719
theorem B2937725 : Blo 1957435 2937725 := bbase (se 3 (by rfl) ⟨550823, by rfl⟩ : syracuseStep 2937725 = 1101647) (by norm_num)
theorem B1958483 : Blo 1957435 1958483 := bstep (se 1 (by rfl) ⟨1468862, by rfl⟩ : syracuseStep 1958483 = 2937725) B2937725
theorem B4406597 : Blo 1957435 4406597 := bbase (se 4 (by rfl) ⟨413118, by rfl⟩ : syracuseStep 4406597 = 826237) (by norm_num)
theorem B2937731 : Blo 1957435 2937731 := bstep (se 1 (by rfl) ⟨2203298, by rfl⟩ : syracuseStep 2937731 = 4406597) B4406597
theorem B1958487 : Blo 1957435 1958487 := bstep (se 1 (by rfl) ⟨1468865, by rfl⟩ : syracuseStep 1958487 = 2937731) B2937731
theorem B2352845 : Blo 1957435 2352845 := bbase (se 3 (by rfl) ⟨441158, by rfl⟩ : syracuseStep 2352845 = 882317) (by norm_num)
theorem B6274253 : Blo 1957435 6274253 := bstep (se 3 (by rfl) ⟨1176422, by rfl⟩ : syracuseStep 6274253 = 2352845) B2352845
theorem B4182835 : Blo 1957435 4182835 := bstep (se 1 (by rfl) ⟨3137126, by rfl⟩ : syracuseStep 4182835 = 6274253) B6274253
theorem B5577113 : Blo 1957435 5577113 := bstep (se 2 (by rfl) ⟨2091417, by rfl⟩ : syracuseStep 5577113 = 4182835) B4182835
theorem B3718075 : Blo 1957435 3718075 := bstep (se 1 (by rfl) ⟨2788556, by rfl⟩ : syracuseStep 3718075 = 5577113) B5577113
theorem B4957433 : Blo 1957435 4957433 := bstep (se 2 (by rfl) ⟨1859037, by rfl⟩ : syracuseStep 4957433 = 3718075) B3718075
theorem B3304955 : Blo 1957435 3304955 := bstep (se 1 (by rfl) ⟨2478716, by rfl⟩ : syracuseStep 3304955 = 4957433) B4957433
theorem B2203303 : Blo 1957435 2203303 := bstep (se 1 (by rfl) ⟨1652477, by rfl⟩ : syracuseStep 2203303 = 3304955) B3304955
theorem B2937737 : Blo 1957435 2937737 := bstep (se 2 (by rfl) ⟨1101651, by rfl⟩ : syracuseStep 2937737 = 2203303) B2203303
theorem B1958491 : Blo 1957435 1958491 := bstep (se 1 (by rfl) ⟨1468868, by rfl⟩ : syracuseStep 1958491 = 2937737) B2937737
theorem B9914885 : Blo 1957435 9914885 := bbase (se 4 (by rfl) ⟨929520, by rfl⟩ : syracuseStep 9914885 = 1859041) (by norm_num)
theorem B6609923 : Blo 1957435 6609923 := bstep (se 1 (by rfl) ⟨4957442, by rfl⟩ : syracuseStep 6609923 = 9914885) B9914885
theorem B4406615 : Blo 1957435 4406615 := bstep (se 1 (by rfl) ⟨3304961, by rfl⟩ : syracuseStep 4406615 = 6609923) B6609923
theorem B2937743 : Blo 1957435 2937743 := bstep (se 1 (by rfl) ⟨2203307, by rfl⟩ : syracuseStep 2937743 = 4406615) B4406615
theorem B1958495 : Blo 1957435 1958495 := bstep (se 1 (by rfl) ⟨1468871, by rfl⟩ : syracuseStep 1958495 = 2937743) B2937743
theorem B2937749 : Blo 1957435 2937749 := bbase (se 6 (by rfl) ⟨68853, by rfl⟩ : syracuseStep 2937749 = 137707) (by norm_num)
theorem B1958499 : Blo 1957435 1958499 := bstep (se 1 (by rfl) ⟨1468874, by rfl⟩ : syracuseStep 1958499 = 2937749) B2937749
theorem B11154293 : Blo 1957435 11154293 := bbase (se 5 (by rfl) ⟨522857, by rfl⟩ : syracuseStep 11154293 = 1045715) (by norm_num)
theorem B7436195 : Blo 1957435 7436195 := bstep (se 1 (by rfl) ⟨5577146, by rfl⟩ : syracuseStep 7436195 = 11154293) B11154293
theorem B4957463 : Blo 1957435 4957463 := bstep (se 1 (by rfl) ⟨3718097, by rfl⟩ : syracuseStep 4957463 = 7436195) B7436195
theorem B3304975 : Blo 1957435 3304975 := bstep (se 1 (by rfl) ⟨2478731, by rfl⟩ : syracuseStep 3304975 = 4957463) B4957463
theorem B4406633 : Blo 1957435 4406633 := bstep (se 2 (by rfl) ⟨1652487, by rfl⟩ : syracuseStep 4406633 = 3304975) B3304975
theorem B2937755 : Blo 1957435 2937755 := bstep (se 1 (by rfl) ⟨2203316, by rfl⟩ : syracuseStep 2937755 = 4406633) B4406633
theorem B1958503 : Blo 1957435 1958503 := bstep (se 1 (by rfl) ⟨1468877, by rfl⟩ : syracuseStep 1958503 = 2937755) B2937755
theorem B2203321 : Blo 1957435 2203321 := bbase (se 2 (by rfl) ⟨826245, by rfl⟩ : syracuseStep 2203321 = 1652491) (by norm_num)
theorem B2937761 : Blo 1957435 2937761 := bstep (se 2 (by rfl) ⟨1101660, by rfl⟩ : syracuseStep 2937761 = 2203321) B2203321
theorem B1958507 : Blo 1957435 1958507 := bstep (se 1 (by rfl) ⟨1468880, by rfl⟩ : syracuseStep 1958507 = 2937761) B2937761
theorem B4182877 : Blo 1957435 4182877 := bbase (se 3 (by rfl) ⟨784289, by rfl⟩ : syracuseStep 4182877 = 1568579) (by norm_num)
theorem B5577169 : Blo 1957435 5577169 := bstep (se 2 (by rfl) ⟨2091438, by rfl⟩ : syracuseStep 5577169 = 4182877) B4182877
theorem B7436225 : Blo 1957435 7436225 := bstep (se 2 (by rfl) ⟨2788584, by rfl⟩ : syracuseStep 7436225 = 5577169) B5577169
theorem B4957483 : Blo 1957435 4957483 := bstep (se 1 (by rfl) ⟨3718112, by rfl⟩ : syracuseStep 4957483 = 7436225) B7436225
theorem B6609977 : Blo 1957435 6609977 := bstep (se 2 (by rfl) ⟨2478741, by rfl⟩ : syracuseStep 6609977 = 4957483) B4957483
theorem B4406651 : Blo 1957435 4406651 := bstep (se 1 (by rfl) ⟨3304988, by rfl⟩ : syracuseStep 4406651 = 6609977) B6609977
theorem B2937767 : Blo 1957435 2937767 := bstep (se 1 (by rfl) ⟨2203325, by rfl⟩ : syracuseStep 2937767 = 4406651) B4406651
theorem B1958511 : Blo 1957435 1958511 := bstep (se 1 (by rfl) ⟨1468883, by rfl⟩ : syracuseStep 1958511 = 2937767) B2937767
theorem B2937773 : Blo 1957435 2937773 := bbase (se 3 (by rfl) ⟨550832, by rfl⟩ : syracuseStep 2937773 = 1101665) (by norm_num)
theorem B1958515 : Blo 1957435 1958515 := bstep (se 1 (by rfl) ⟨1468886, by rfl⟩ : syracuseStep 1958515 = 2937773) B2937773
theorem B4406669 : Blo 1957435 4406669 := bbase (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) (by norm_num)
theorem B2937779 : Blo 1957435 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B1958519 : Blo 1957435 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B2478757 : Blo 1957435 2478757 := bbase (se 4 (by rfl) ⟨232383, by rfl⟩ : syracuseStep 2478757 = 464767) (by norm_num)
theorem B3305009 : Blo 1957435 3305009 := bstep (se 2 (by rfl) ⟨1239378, by rfl⟩ : syracuseStep 3305009 = 2478757) B2478757
theorem B2203339 : Blo 1957435 2203339 := bstep (se 1 (by rfl) ⟨1652504, by rfl⟩ : syracuseStep 2203339 = 3305009) B3305009
theorem B2937785 : Blo 1957435 2937785 := bstep (se 2 (by rfl) ⟨1101669, by rfl⟩ : syracuseStep 2937785 = 2203339) B2203339
theorem B1958523 : Blo 1957435 1958523 := bstep (se 1 (by rfl) ⟨1468892, by rfl⟩ : syracuseStep 1958523 = 2937785) B2937785
theorem B2233405 : Blo 1957435 2233405 := bbase (se 3 (by rfl) ⟨418763, by rfl⟩ : syracuseStep 2233405 = 837527) (by norm_num)
theorem B11911493 : Blo 1957435 11911493 := bstep (se 4 (by rfl) ⟨1116702, by rfl⟩ : syracuseStep 11911493 = 2233405) B2233405
theorem B31763981 : Blo 1957435 31763981 := bstep (se 3 (by rfl) ⟨5955746, by rfl⟩ : syracuseStep 31763981 = 11911493) B11911493
theorem B21175987 : Blo 1957435 21175987 := bstep (se 1 (by rfl) ⟨15881990, by rfl⟩ : syracuseStep 21175987 = 31763981) B31763981
theorem B28234649 : Blo 1957435 28234649 := bstep (se 2 (by rfl) ⟨10587993, by rfl⟩ : syracuseStep 28234649 = 21175987) B21175987
theorem B18823099 : Blo 1957435 18823099 := bstep (se 1 (by rfl) ⟨14117324, by rfl⟩ : syracuseStep 18823099 = 28234649) B28234649
theorem B25097465 : Blo 1957435 25097465 := bstep (se 2 (by rfl) ⟨9411549, by rfl⟩ : syracuseStep 25097465 = 18823099) B18823099
theorem B16731643 : Blo 1957435 16731643 := bstep (se 1 (by rfl) ⟨12548732, by rfl⟩ : syracuseStep 16731643 = 25097465) B25097465
theorem B22308857 : Blo 1957435 22308857 := bstep (se 2 (by rfl) ⟨8365821, by rfl⟩ : syracuseStep 22308857 = 16731643) B16731643
theorem B14872571 : Blo 1957435 14872571 := bstep (se 1 (by rfl) ⟨11154428, by rfl⟩ : syracuseStep 14872571 = 22308857) B22308857
theorem B9915047 : Blo 1957435 9915047 := bstep (se 1 (by rfl) ⟨7436285, by rfl⟩ : syracuseStep 9915047 = 14872571) B14872571
theorem B6610031 : Blo 1957435 6610031 := bstep (se 1 (by rfl) ⟨4957523, by rfl⟩ : syracuseStep 6610031 = 9915047) B9915047
theorem B4406687 : Blo 1957435 4406687 := bstep (se 1 (by rfl) ⟨3305015, by rfl⟩ : syracuseStep 4406687 = 6610031) B6610031
theorem B2937791 : Blo 1957435 2937791 := bstep (se 1 (by rfl) ⟨2203343, by rfl⟩ : syracuseStep 2937791 = 4406687) B4406687
theorem B1958527 : Blo 1957435 1958527 := bstep (se 1 (by rfl) ⟨1468895, by rfl⟩ : syracuseStep 1958527 = 2937791) B2937791
theorem B2937797 : Blo 1957435 2937797 := bbase (se 4 (by rfl) ⟨275418, by rfl⟩ : syracuseStep 2937797 = 550837) (by norm_num)
theorem B1958531 : Blo 1957435 1958531 := bstep (se 1 (by rfl) ⟨1468898, by rfl⟩ : syracuseStep 1958531 = 2937797) B2937797
theorem B3305029 : Blo 1957435 3305029 := bbase (se 4 (by rfl) ⟨309846, by rfl⟩ : syracuseStep 3305029 = 619693) (by norm_num)
theorem B4406705 : Blo 1957435 4406705 := bstep (se 2 (by rfl) ⟨1652514, by rfl⟩ : syracuseStep 4406705 = 3305029) B3305029
theorem B2937803 : Blo 1957435 2937803 := bstep (se 1 (by rfl) ⟨2203352, by rfl⟩ : syracuseStep 2937803 = 4406705) B4406705
theorem B1958535 : Blo 1957435 1958535 := bstep (se 1 (by rfl) ⟨1468901, by rfl⟩ : syracuseStep 1958535 = 2937803) B2937803
theorem B2203357 : Blo 1957435 2203357 := bbase (se 3 (by rfl) ⟨413129, by rfl⟩ : syracuseStep 2203357 = 826259) (by norm_num)
theorem B2937809 : Blo 1957435 2937809 := bstep (se 2 (by rfl) ⟨1101678, by rfl⟩ : syracuseStep 2937809 = 2203357) B2203357
theorem B1958539 : Blo 1957435 1958539 := bstep (se 1 (by rfl) ⟨1468904, by rfl⟩ : syracuseStep 1958539 = 2937809) B2937809
theorem B6610085 : Blo 1957435 6610085 := bbase (se 4 (by rfl) ⟨619695, by rfl⟩ : syracuseStep 6610085 = 1239391) (by norm_num)
theorem B4406723 : Blo 1957435 4406723 := bstep (se 1 (by rfl) ⟨3305042, by rfl⟩ : syracuseStep 4406723 = 6610085) B6610085
theorem B2937815 : Blo 1957435 2937815 := bstep (se 1 (by rfl) ⟨2203361, by rfl⟩ : syracuseStep 2937815 = 4406723) B4406723
theorem B1958543 : Blo 1957435 1958543 := bstep (se 1 (by rfl) ⟨1468907, by rfl⟩ : syracuseStep 1958543 = 2937815) B2937815
theorem B2937821 : Blo 1957435 2937821 := bbase (se 3 (by rfl) ⟨550841, by rfl⟩ : syracuseStep 2937821 = 1101683) (by norm_num)
theorem B1958547 : Blo 1957435 1958547 := bstep (se 1 (by rfl) ⟨1468910, by rfl⟩ : syracuseStep 1958547 = 2937821) B2937821
theorem B4406741 : Blo 1957435 4406741 := bbase (se 7 (by rfl) ⟨51641, by rfl⟩ : syracuseStep 4406741 = 103283) (by norm_num)
theorem B2937827 : Blo 1957435 2937827 := bstep (se 1 (by rfl) ⟨2203370, by rfl⟩ : syracuseStep 2937827 = 4406741) B4406741
theorem B1958551 : Blo 1957435 1958551 := bstep (se 1 (by rfl) ⟨1468913, by rfl⟩ : syracuseStep 1958551 = 2937827) B2937827
theorem B2647037 : Blo 1957435 2647037 := bbase (se 3 (by rfl) ⟨496319, by rfl⟩ : syracuseStep 2647037 = 992639) (by norm_num)
theorem B7058765 : Blo 1957435 7058765 := bstep (se 3 (by rfl) ⟨1323518, by rfl⟩ : syracuseStep 7058765 = 2647037) B2647037
theorem B18823373 : Blo 1957435 18823373 := bstep (se 3 (by rfl) ⟨3529382, by rfl⟩ : syracuseStep 18823373 = 7058765) B7058765
theorem B12548915 : Blo 1957435 12548915 := bstep (se 1 (by rfl) ⟨9411686, by rfl⟩ : syracuseStep 12548915 = 18823373) B18823373
theorem B8365943 : Blo 1957435 8365943 := bstep (se 1 (by rfl) ⟨6274457, by rfl⟩ : syracuseStep 8365943 = 12548915) B12548915
theorem B5577295 : Blo 1957435 5577295 := bstep (se 1 (by rfl) ⟨4182971, by rfl⟩ : syracuseStep 5577295 = 8365943) B8365943
theorem B7436393 : Blo 1957435 7436393 := bstep (se 2 (by rfl) ⟨2788647, by rfl⟩ : syracuseStep 7436393 = 5577295) B5577295
theorem B4957595 : Blo 1957435 4957595 := bstep (se 1 (by rfl) ⟨3718196, by rfl⟩ : syracuseStep 4957595 = 7436393) B7436393
theorem B3305063 : Blo 1957435 3305063 := bstep (se 1 (by rfl) ⟨2478797, by rfl⟩ : syracuseStep 3305063 = 4957595) B4957595
theorem B2203375 : Blo 1957435 2203375 := bstep (se 1 (by rfl) ⟨1652531, by rfl⟩ : syracuseStep 2203375 = 3305063) B3305063
theorem B2937833 : Blo 1957435 2937833 := bstep (se 2 (by rfl) ⟨1101687, by rfl⟩ : syracuseStep 2937833 = 2203375) B2203375
theorem B1958555 : Blo 1957435 1958555 := bstep (se 1 (by rfl) ⟨1468916, by rfl⟩ : syracuseStep 1958555 = 2937833) B2937833
theorem B6274469 : Blo 1957435 6274469 := bbase (se 4 (by rfl) ⟨588231, by rfl⟩ : syracuseStep 6274469 = 1176463) (by norm_num)
theorem B16731917 : Blo 1957435 16731917 := bstep (se 3 (by rfl) ⟨3137234, by rfl⟩ : syracuseStep 16731917 = 6274469) B6274469
theorem B11154611 : Blo 1957435 11154611 := bstep (se 1 (by rfl) ⟨8365958, by rfl⟩ : syracuseStep 11154611 = 16731917) B16731917
theorem B7436407 : Blo 1957435 7436407 := bstep (se 1 (by rfl) ⟨5577305, by rfl⟩ : syracuseStep 7436407 = 11154611) B11154611
theorem B9915209 : Blo 1957435 9915209 := bstep (se 2 (by rfl) ⟨3718203, by rfl⟩ : syracuseStep 9915209 = 7436407) B7436407
theorem B6610139 : Blo 1957435 6610139 := bstep (se 1 (by rfl) ⟨4957604, by rfl⟩ : syracuseStep 6610139 = 9915209) B9915209
theorem B4406759 : Blo 1957435 4406759 := bstep (se 1 (by rfl) ⟨3305069, by rfl⟩ : syracuseStep 4406759 = 6610139) B6610139
theorem B2937839 : Blo 1957435 2937839 := bstep (se 1 (by rfl) ⟨2203379, by rfl⟩ : syracuseStep 2937839 = 4406759) B4406759
theorem B1958559 : Blo 1957435 1958559 := bstep (se 1 (by rfl) ⟨1468919, by rfl⟩ : syracuseStep 1958559 = 2937839) B2937839
theorem B2937845 : Blo 1957435 2937845 := bbase (se 5 (by rfl) ⟨137711, by rfl⟩ : syracuseStep 2937845 = 275423) (by norm_num)
theorem B1958563 : Blo 1957435 1958563 := bstep (se 1 (by rfl) ⟨1468922, by rfl⟩ : syracuseStep 1958563 = 2937845) B2937845
theorem B4182997 : Blo 1957435 4182997 := bbase (se 7 (by rfl) ⟨49019, by rfl⟩ : syracuseStep 4182997 = 98039) (by norm_num)
theorem B5577329 : Blo 1957435 5577329 := bstep (se 2 (by rfl) ⟨2091498, by rfl⟩ : syracuseStep 5577329 = 4182997) B4182997
theorem B3718219 : Blo 1957435 3718219 := bstep (se 1 (by rfl) ⟨2788664, by rfl⟩ : syracuseStep 3718219 = 5577329) B5577329
theorem B4957625 : Blo 1957435 4957625 := bstep (se 2 (by rfl) ⟨1859109, by rfl⟩ : syracuseStep 4957625 = 3718219) B3718219
theorem B3305083 : Blo 1957435 3305083 := bstep (se 1 (by rfl) ⟨2478812, by rfl⟩ : syracuseStep 3305083 = 4957625) B4957625
theorem B4406777 : Blo 1957435 4406777 := bstep (se 2 (by rfl) ⟨1652541, by rfl⟩ : syracuseStep 4406777 = 3305083) B3305083
theorem B2937851 : Blo 1957435 2937851 := bstep (se 1 (by rfl) ⟨2203388, by rfl⟩ : syracuseStep 2937851 = 4406777) B4406777
theorem B1958567 : Blo 1957435 1958567 := bstep (se 1 (by rfl) ⟨1468925, by rfl⟩ : syracuseStep 1958567 = 2937851) B2937851
theorem B2203393 : Blo 1957435 2203393 := bbase (se 2 (by rfl) ⟨826272, by rfl⟩ : syracuseStep 2203393 = 1652545) (by norm_num)
theorem B2937857 : Blo 1957435 2937857 := bstep (se 2 (by rfl) ⟨1101696, by rfl⟩ : syracuseStep 2937857 = 2203393) B2203393
theorem B1958571 : Blo 1957435 1958571 := bstep (se 1 (by rfl) ⟨1468928, by rfl⟩ : syracuseStep 1958571 = 2937857) B2937857
theorem B4957645 : Blo 1957435 4957645 := bbase (se 3 (by rfl) ⟨929558, by rfl⟩ : syracuseStep 4957645 = 1859117) (by norm_num)
theorem B6610193 : Blo 1957435 6610193 := bstep (se 2 (by rfl) ⟨2478822, by rfl⟩ : syracuseStep 6610193 = 4957645) B4957645
theorem B4406795 : Blo 1957435 4406795 := bstep (se 1 (by rfl) ⟨3305096, by rfl⟩ : syracuseStep 4406795 = 6610193) B6610193
theorem B2937863 : Blo 1957435 2937863 := bstep (se 1 (by rfl) ⟨2203397, by rfl⟩ : syracuseStep 2937863 = 4406795) B4406795
theorem B1958575 : Blo 1957435 1958575 := bstep (se 1 (by rfl) ⟨1468931, by rfl⟩ : syracuseStep 1958575 = 2937863) B2937863
theorem B2937869 : Blo 1957435 2937869 := bbase (se 3 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 2937869 = 1101701) (by norm_num)
theorem B1958579 : Blo 1957435 1958579 := bstep (se 1 (by rfl) ⟨1468934, by rfl⟩ : syracuseStep 1958579 = 2937869) B2937869
theorem B4406813 : Blo 1957435 4406813 := bbase (se 3 (by rfl) ⟨826277, by rfl⟩ : syracuseStep 4406813 = 1652555) (by norm_num)
theorem B2937875 : Blo 1957435 2937875 := bstep (se 1 (by rfl) ⟨2203406, by rfl⟩ : syracuseStep 2937875 = 4406813) B4406813
theorem B1958583 : Blo 1957435 1958583 := bstep (se 1 (by rfl) ⟨1468937, by rfl⟩ : syracuseStep 1958583 = 2937875) B2937875
theorem B3305117 : Blo 1957435 3305117 := bbase (se 3 (by rfl) ⟨619709, by rfl⟩ : syracuseStep 3305117 = 1239419) (by norm_num)
theorem B2203411 : Blo 1957435 2203411 := bstep (se 1 (by rfl) ⟨1652558, by rfl⟩ : syracuseStep 2203411 = 3305117) B3305117
theorem B2937881 : Blo 1957435 2937881 := bstep (se 2 (by rfl) ⟨1101705, by rfl⟩ : syracuseStep 2937881 = 2203411) B2203411
theorem B1958587 : Blo 1957435 1958587 := bstep (se 1 (by rfl) ⟨1468940, by rfl⟩ : syracuseStep 1958587 = 2937881) B2937881
theorem B2647085 : Blo 1957435 2647085 := bbase (se 3 (by rfl) ⟨496328, by rfl⟩ : syracuseStep 2647085 = 992657) (by norm_num)
theorem B28235573 : Blo 1957435 28235573 := bstep (se 5 (by rfl) ⟨1323542, by rfl⟩ : syracuseStep 28235573 = 2647085) B2647085
theorem B18823715 : Blo 1957435 18823715 := bstep (se 1 (by rfl) ⟨14117786, by rfl⟩ : syracuseStep 18823715 = 28235573) B28235573
theorem B12549143 : Blo 1957435 12549143 := bstep (se 1 (by rfl) ⟨9411857, by rfl⟩ : syracuseStep 12549143 = 18823715) B18823715
theorem B8366095 : Blo 1957435 8366095 := bstep (se 1 (by rfl) ⟨6274571, by rfl⟩ : syracuseStep 8366095 = 12549143) B12549143
theorem B11154793 : Blo 1957435 11154793 := bstep (se 2 (by rfl) ⟨4183047, by rfl⟩ : syracuseStep 11154793 = 8366095) B8366095
theorem B14873057 : Blo 1957435 14873057 := bstep (se 2 (by rfl) ⟨5577396, by rfl⟩ : syracuseStep 14873057 = 11154793) B11154793
theorem B9915371 : Blo 1957435 9915371 := bstep (se 1 (by rfl) ⟨7436528, by rfl⟩ : syracuseStep 9915371 = 14873057) B14873057
theorem B6610247 : Blo 1957435 6610247 := bstep (se 1 (by rfl) ⟨4957685, by rfl⟩ : syracuseStep 6610247 = 9915371) B9915371
theorem B4406831 : Blo 1957435 4406831 := bstep (se 1 (by rfl) ⟨3305123, by rfl⟩ : syracuseStep 4406831 = 6610247) B6610247
theorem B2937887 : Blo 1957435 2937887 := bstep (se 1 (by rfl) ⟨2203415, by rfl⟩ : syracuseStep 2937887 = 4406831) B4406831
theorem B1958591 : Blo 1957435 1958591 := bstep (se 1 (by rfl) ⟨1468943, by rfl⟩ : syracuseStep 1958591 = 2937887) B2937887
theorem B2937893 : Blo 1957435 2937893 := bbase (se 4 (by rfl) ⟨275427, by rfl⟩ : syracuseStep 2937893 = 550855) (by norm_num)
theorem B1958595 : Blo 1957435 1958595 := bstep (se 1 (by rfl) ⟨1468946, by rfl⟩ : syracuseStep 1958595 = 2937893) B2937893
theorem B2478853 : Blo 1957435 2478853 := bbase (se 4 (by rfl) ⟨232392, by rfl⟩ : syracuseStep 2478853 = 464785) (by norm_num)
theorem B3305137 : Blo 1957435 3305137 := bstep (se 2 (by rfl) ⟨1239426, by rfl⟩ : syracuseStep 3305137 = 2478853) B2478853
theorem B4406849 : Blo 1957435 4406849 := bstep (se 2 (by rfl) ⟨1652568, by rfl⟩ : syracuseStep 4406849 = 3305137) B3305137
theorem B2937899 : Blo 1957435 2937899 := bstep (se 1 (by rfl) ⟨2203424, by rfl⟩ : syracuseStep 2937899 = 4406849) B4406849
theorem B1958599 : Blo 1957435 1958599 := bstep (se 1 (by rfl) ⟨1468949, by rfl⟩ : syracuseStep 1958599 = 2937899) B2937899
theorem B2203429 : Blo 1957435 2203429 := bbase (se 4 (by rfl) ⟨206571, by rfl⟩ : syracuseStep 2203429 = 413143) (by norm_num)
theorem B2937905 : Blo 1957435 2937905 := bstep (se 2 (by rfl) ⟨1101714, by rfl⟩ : syracuseStep 2937905 = 2203429) B2203429
theorem B1958603 : Blo 1957435 1958603 := bstep (se 1 (by rfl) ⟨1468952, by rfl⟩ : syracuseStep 1958603 = 2937905) B2937905
theorem B8366165 : Blo 1957435 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B5577443 : Blo 1957435 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B3718295 : Blo 1957435 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B2478863 : Blo 1957435 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B6610301 : Blo 1957435 6610301 := bstep (se 3 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 6610301 = 2478863) B2478863
theorem B4406867 : Blo 1957435 4406867 := bstep (se 1 (by rfl) ⟨3305150, by rfl⟩ : syracuseStep 4406867 = 6610301) B6610301
theorem B2937911 : Blo 1957435 2937911 := bstep (se 1 (by rfl) ⟨2203433, by rfl⟩ : syracuseStep 2937911 = 4406867) B4406867
theorem B1958607 : Blo 1957435 1958607 := bstep (se 1 (by rfl) ⟨1468955, by rfl⟩ : syracuseStep 1958607 = 2937911) B2937911
theorem B2937917 : Blo 1957435 2937917 := bbase (se 3 (by rfl) ⟨550859, by rfl⟩ : syracuseStep 2937917 = 1101719) (by norm_num)
theorem B1958611 : Blo 1957435 1958611 := bstep (se 1 (by rfl) ⟨1468958, by rfl⟩ : syracuseStep 1958611 = 2937917) B2937917
theorem B4406885 : Blo 1957435 4406885 := bbase (se 4 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 4406885 = 826291) (by norm_num)
theorem B2937923 : Blo 1957435 2937923 := bstep (se 1 (by rfl) ⟨2203442, by rfl⟩ : syracuseStep 2937923 = 4406885) B4406885
theorem B1958615 : Blo 1957435 1958615 := bstep (se 1 (by rfl) ⟨1468961, by rfl⟩ : syracuseStep 1958615 = 2937923) B2937923
theorem B4957757 : Blo 1957435 4957757 := bbase (se 3 (by rfl) ⟨929579, by rfl⟩ : syracuseStep 4957757 = 1859159) (by norm_num)
theorem B3305171 : Blo 1957435 3305171 := bstep (se 1 (by rfl) ⟨2478878, by rfl⟩ : syracuseStep 3305171 = 4957757) B4957757
theorem B2203447 : Blo 1957435 2203447 := bstep (se 1 (by rfl) ⟨1652585, by rfl⟩ : syracuseStep 2203447 = 3305171) B3305171
theorem B2937929 : Blo 1957435 2937929 := bstep (se 2 (by rfl) ⟨1101723, by rfl⟩ : syracuseStep 2937929 = 2203447) B2203447
theorem B1958619 : Blo 1957435 1958619 := bstep (se 1 (by rfl) ⟨1468964, by rfl⟩ : syracuseStep 1958619 = 2937929) B2937929
theorem B3718325 : Blo 1957435 3718325 := bbase (se 5 (by rfl) ⟨174296, by rfl⟩ : syracuseStep 3718325 = 348593) (by norm_num)
theorem B9915533 : Blo 1957435 9915533 := bstep (se 3 (by rfl) ⟨1859162, by rfl⟩ : syracuseStep 9915533 = 3718325) B3718325
theorem B6610355 : Blo 1957435 6610355 := bstep (se 1 (by rfl) ⟨4957766, by rfl⟩ : syracuseStep 6610355 = 9915533) B9915533
theorem B4406903 : Blo 1957435 4406903 := bstep (se 1 (by rfl) ⟨3305177, by rfl⟩ : syracuseStep 4406903 = 6610355) B6610355
theorem B2937935 : Blo 1957435 2937935 := bstep (se 1 (by rfl) ⟨2203451, by rfl⟩ : syracuseStep 2937935 = 4406903) B4406903
theorem B1958623 : Blo 1957435 1958623 := bstep (se 1 (by rfl) ⟨1468967, by rfl⟩ : syracuseStep 1958623 = 2937935) B2937935
theorem B2937941 : Blo 1957435 2937941 := bbase (se 8 (by rfl) ⟨17214, by rfl⟩ : syracuseStep 2937941 = 34429) (by norm_num)
theorem B1958627 : Blo 1957435 1958627 := bstep (se 1 (by rfl) ⟨1468970, by rfl⟩ : syracuseStep 1958627 = 2937941) B2937941
theorem B2826805 : Blo 1957435 2826805 := bbase (se 5 (by rfl) ⟨132506, by rfl⟩ : syracuseStep 2826805 = 265013) (by norm_num)
theorem B3769073 : Blo 1957435 3769073 := bstep (se 2 (by rfl) ⟨1413402, by rfl⟩ : syracuseStep 3769073 = 2826805) B2826805
theorem B2512715 : Blo 1957435 2512715 := bstep (se 1 (by rfl) ⟨1884536, by rfl⟩ : syracuseStep 2512715 = 3769073) B3769073
theorem B6700573 : Blo 1957435 6700573 := bstep (se 3 (by rfl) ⟨1256357, by rfl⟩ : syracuseStep 6700573 = 2512715) B2512715
theorem B8934097 : Blo 1957435 8934097 := bstep (se 2 (by rfl) ⟨3350286, by rfl⟩ : syracuseStep 8934097 = 6700573) B6700573
theorem B11912129 : Blo 1957435 11912129 := bstep (se 2 (by rfl) ⟨4467048, by rfl⟩ : syracuseStep 11912129 = 8934097) B8934097
theorem B7941419 : Blo 1957435 7941419 := bstep (se 1 (by rfl) ⟨5956064, by rfl⟩ : syracuseStep 7941419 = 11912129) B11912129
theorem B5294279 : Blo 1957435 5294279 := bstep (se 1 (by rfl) ⟨3970709, by rfl⟩ : syracuseStep 5294279 = 7941419) B7941419
theorem B14118077 : Blo 1957435 14118077 := bstep (se 3 (by rfl) ⟨2647139, by rfl⟩ : syracuseStep 14118077 = 5294279) B5294279
theorem B9412051 : Blo 1957435 9412051 := bstep (se 1 (by rfl) ⟨7059038, by rfl⟩ : syracuseStep 9412051 = 14118077) B14118077
theorem B12549401 : Blo 1957435 12549401 := bstep (se 2 (by rfl) ⟨4706025, by rfl⟩ : syracuseStep 12549401 = 9412051) B9412051
theorem B8366267 : Blo 1957435 8366267 := bstep (se 1 (by rfl) ⟨6274700, by rfl⟩ : syracuseStep 8366267 = 12549401) B12549401
theorem B5577511 : Blo 1957435 5577511 := bstep (se 1 (by rfl) ⟨4183133, by rfl⟩ : syracuseStep 5577511 = 8366267) B8366267
theorem B7436681 : Blo 1957435 7436681 := bstep (se 2 (by rfl) ⟨2788755, by rfl⟩ : syracuseStep 7436681 = 5577511) B5577511
theorem B4957787 : Blo 1957435 4957787 := bstep (se 1 (by rfl) ⟨3718340, by rfl⟩ : syracuseStep 4957787 = 7436681) B7436681
theorem B3305191 : Blo 1957435 3305191 := bstep (se 1 (by rfl) ⟨2478893, by rfl⟩ : syracuseStep 3305191 = 4957787) B4957787
theorem B4406921 : Blo 1957435 4406921 := bstep (se 2 (by rfl) ⟨1652595, by rfl⟩ : syracuseStep 4406921 = 3305191) B3305191
theorem B2937947 : Blo 1957435 2937947 := bstep (se 1 (by rfl) ⟨2203460, by rfl⟩ : syracuseStep 2937947 = 4406921) B4406921
theorem B1958631 : Blo 1957435 1958631 := bstep (se 1 (by rfl) ⟨1468973, by rfl⟩ : syracuseStep 1958631 = 2937947) B2937947
theorem B2203465 : Blo 1957435 2203465 := bbase (se 2 (by rfl) ⟨826299, by rfl⟩ : syracuseStep 2203465 = 1652599) (by norm_num)
theorem B2937953 : Blo 1957435 2937953 := bstep (se 2 (by rfl) ⟨1101732, by rfl⟩ : syracuseStep 2937953 = 2203465) B2203465
theorem B1958635 : Blo 1957435 1958635 := bstep (se 1 (by rfl) ⟨1468976, by rfl⟩ : syracuseStep 1958635 = 2937953) B2937953
theorem B14118133 : Blo 1957435 14118133 := bbase (se 5 (by rfl) ⟨661787, by rfl⟩ : syracuseStep 14118133 = 1323575) (by norm_num)
theorem B18824177 : Blo 1957435 18824177 := bstep (se 2 (by rfl) ⟨7059066, by rfl⟩ : syracuseStep 18824177 = 14118133) B14118133
theorem B12549451 : Blo 1957435 12549451 := bstep (se 1 (by rfl) ⟨9412088, by rfl⟩ : syracuseStep 12549451 = 18824177) B18824177
theorem B16732601 : Blo 1957435 16732601 := bstep (se 2 (by rfl) ⟨6274725, by rfl⟩ : syracuseStep 16732601 = 12549451) B12549451
theorem B11155067 : Blo 1957435 11155067 := bstep (se 1 (by rfl) ⟨8366300, by rfl⟩ : syracuseStep 11155067 = 16732601) B16732601
theorem B7436711 : Blo 1957435 7436711 := bstep (se 1 (by rfl) ⟨5577533, by rfl⟩ : syracuseStep 7436711 = 11155067) B11155067
theorem B4957807 : Blo 1957435 4957807 := bstep (se 1 (by rfl) ⟨3718355, by rfl⟩ : syracuseStep 4957807 = 7436711) B7436711
theorem B6610409 : Blo 1957435 6610409 := bstep (se 2 (by rfl) ⟨2478903, by rfl⟩ : syracuseStep 6610409 = 4957807) B4957807
theorem B4406939 : Blo 1957435 4406939 := bstep (se 1 (by rfl) ⟨3305204, by rfl⟩ : syracuseStep 4406939 = 6610409) B6610409
theorem B2937959 : Blo 1957435 2937959 := bstep (se 1 (by rfl) ⟨2203469, by rfl⟩ : syracuseStep 2937959 = 4406939) B4406939
theorem B1958639 : Blo 1957435 1958639 := bstep (se 1 (by rfl) ⟨1468979, by rfl⟩ : syracuseStep 1958639 = 2937959) B2937959
theorem B2937965 : Blo 1957435 2937965 := bbase (se 3 (by rfl) ⟨550868, by rfl⟩ : syracuseStep 2937965 = 1101737) (by norm_num)
theorem B1958643 : Blo 1957435 1958643 := bstep (se 1 (by rfl) ⟨1468982, by rfl⟩ : syracuseStep 1958643 = 2937965) B2937965
theorem B4406957 : Blo 1957435 4406957 := bbase (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) (by norm_num)
theorem B2937971 : Blo 1957435 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B1958647 : Blo 1957435 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B5808997 : Blo 1957435 5808997 := bbase (se 4 (by rfl) ⟨544593, by rfl⟩ : syracuseStep 5808997 = 1089187) (by norm_num)
theorem B7745329 : Blo 1957435 7745329 := bstep (se 2 (by rfl) ⟨2904498, by rfl⟩ : syracuseStep 7745329 = 5808997) B5808997
theorem B10327105 : Blo 1957435 10327105 := bstep (se 2 (by rfl) ⟨3872664, by rfl⟩ : syracuseStep 10327105 = 7745329) B7745329
theorem B13769473 : Blo 1957435 13769473 := bstep (se 2 (by rfl) ⟨5163552, by rfl⟩ : syracuseStep 13769473 = 10327105) B10327105
theorem B18359297 : Blo 1957435 18359297 := bstep (se 2 (by rfl) ⟨6884736, by rfl⟩ : syracuseStep 18359297 = 13769473) B13769473
theorem B12239531 : Blo 1957435 12239531 := bstep (se 1 (by rfl) ⟨9179648, by rfl⟩ : syracuseStep 12239531 = 18359297) B18359297
theorem B8159687 : Blo 1957435 8159687 := bstep (se 1 (by rfl) ⟨6119765, by rfl⟩ : syracuseStep 8159687 = 12239531) B12239531
theorem B5439791 : Blo 1957435 5439791 := bstep (se 1 (by rfl) ⟨4079843, by rfl⟩ : syracuseStep 5439791 = 8159687) B8159687
theorem B3626527 : Blo 1957435 3626527 := bstep (se 1 (by rfl) ⟨2719895, by rfl⟩ : syracuseStep 3626527 = 5439791) B5439791
theorem B4835369 : Blo 1957435 4835369 := bstep (se 2 (by rfl) ⟨1813263, by rfl⟩ : syracuseStep 4835369 = 3626527) B3626527
theorem B3223579 : Blo 1957435 3223579 := bstep (se 1 (by rfl) ⟨2417684, by rfl⟩ : syracuseStep 3223579 = 4835369) B4835369
theorem B4298105 : Blo 1957435 4298105 := bstep (se 2 (by rfl) ⟨1611789, by rfl⟩ : syracuseStep 4298105 = 3223579) B3223579
theorem B2865403 : Blo 1957435 2865403 := bstep (se 1 (by rfl) ⟨2149052, by rfl⟩ : syracuseStep 2865403 = 4298105) B4298105
theorem B3820537 : Blo 1957435 3820537 := bstep (se 2 (by rfl) ⟨1432701, by rfl⟩ : syracuseStep 3820537 = 2865403) B2865403
theorem B20376197 : Blo 1957435 20376197 := bstep (se 4 (by rfl) ⟨1910268, by rfl⟩ : syracuseStep 20376197 = 3820537) B3820537
theorem B13584131 : Blo 1957435 13584131 := bstep (se 1 (by rfl) ⟨10188098, by rfl⟩ : syracuseStep 13584131 = 20376197) B20376197
theorem B9056087 : Blo 1957435 9056087 := bstep (se 1 (by rfl) ⟨6792065, by rfl⟩ : syracuseStep 9056087 = 13584131) B13584131
theorem B6037391 : Blo 1957435 6037391 := bstep (se 1 (by rfl) ⟨4528043, by rfl⟩ : syracuseStep 6037391 = 9056087) B9056087
theorem B4024927 : Blo 1957435 4024927 := bstep (se 1 (by rfl) ⟨3018695, by rfl⟩ : syracuseStep 4024927 = 6037391) B6037391
theorem B5366569 : Blo 1957435 5366569 := bstep (se 2 (by rfl) ⟨2012463, by rfl⟩ : syracuseStep 5366569 = 4024927) B4024927
theorem B7155425 : Blo 1957435 7155425 := bstep (se 2 (by rfl) ⟨2683284, by rfl⟩ : syracuseStep 7155425 = 5366569) B5366569
theorem B4770283 : Blo 1957435 4770283 := bstep (se 1 (by rfl) ⟨3577712, by rfl⟩ : syracuseStep 4770283 = 7155425) B7155425
theorem B6360377 : Blo 1957435 6360377 := bstep (se 2 (by rfl) ⟨2385141, by rfl⟩ : syracuseStep 6360377 = 4770283) B4770283
theorem B16961005 : Blo 1957435 16961005 := bstep (se 3 (by rfl) ⟨3180188, by rfl⟩ : syracuseStep 16961005 = 6360377) B6360377
theorem B90458693 : Blo 1957435 90458693 := bstep (se 4 (by rfl) ⟨8480502, by rfl⟩ : syracuseStep 90458693 = 16961005) B16961005
theorem B60305795 : Blo 1957435 60305795 := bstep (se 1 (by rfl) ⟨45229346, by rfl⟩ : syracuseStep 60305795 = 90458693) B90458693
theorem B40203863 : Blo 1957435 40203863 := bstep (se 1 (by rfl) ⟨30152897, by rfl⟩ : syracuseStep 40203863 = 60305795) B60305795
theorem B26802575 : Blo 1957435 26802575 := bstep (se 1 (by rfl) ⟨20101931, by rfl⟩ : syracuseStep 26802575 = 40203863) B40203863
theorem B17868383 : Blo 1957435 17868383 := bstep (se 1 (by rfl) ⟨13401287, by rfl⟩ : syracuseStep 17868383 = 26802575) B26802575
theorem B11912255 : Blo 1957435 11912255 := bstep (se 1 (by rfl) ⟨8934191, by rfl⟩ : syracuseStep 11912255 = 17868383) B17868383
theorem B7941503 : Blo 1957435 7941503 := bstep (se 1 (by rfl) ⟨5956127, by rfl⟩ : syracuseStep 7941503 = 11912255) B11912255
theorem B5294335 : Blo 1957435 5294335 := bstep (se 1 (by rfl) ⟨3970751, by rfl⟩ : syracuseStep 5294335 = 7941503) B7941503
theorem B7059113 : Blo 1957435 7059113 := bstep (se 2 (by rfl) ⟨2647167, by rfl⟩ : syracuseStep 7059113 = 5294335) B5294335
theorem B4706075 : Blo 1957435 4706075 := bstep (se 1 (by rfl) ⟨3529556, by rfl⟩ : syracuseStep 4706075 = 7059113) B7059113
theorem B3137383 : Blo 1957435 3137383 := bstep (se 1 (by rfl) ⟨2353037, by rfl⟩ : syracuseStep 3137383 = 4706075) B4706075
theorem B4183177 : Blo 1957435 4183177 := bstep (se 2 (by rfl) ⟨1568691, by rfl⟩ : syracuseStep 4183177 = 3137383) B3137383
theorem B5577569 : Blo 1957435 5577569 := bstep (se 2 (by rfl) ⟨2091588, by rfl⟩ : syracuseStep 5577569 = 4183177) B4183177
theorem B3718379 : Blo 1957435 3718379 := bstep (se 1 (by rfl) ⟨2788784, by rfl⟩ : syracuseStep 3718379 = 5577569) B5577569
theorem B2478919 : Blo 1957435 2478919 := bstep (se 1 (by rfl) ⟨1859189, by rfl⟩ : syracuseStep 2478919 = 3718379) B3718379
theorem B3305225 : Blo 1957435 3305225 := bstep (se 2 (by rfl) ⟨1239459, by rfl⟩ : syracuseStep 3305225 = 2478919) B2478919
theorem B2203483 : Blo 1957435 2203483 := bstep (se 1 (by rfl) ⟨1652612, by rfl⟩ : syracuseStep 2203483 = 3305225) B3305225
theorem B2937977 : Blo 1957435 2937977 := bstep (se 2 (by rfl) ⟨1101741, by rfl⟩ : syracuseStep 2937977 = 2203483) B2203483
theorem B1958651 : Blo 1957435 1958651 := bstep (se 1 (by rfl) ⟨1468988, by rfl⟩ : syracuseStep 1958651 = 2937977) B2937977
theorem B2581777 : Blo 1957435 2581777 := bbase (se 2 (by rfl) ⟨968166, by rfl⟩ : syracuseStep 2581777 = 1936333) (by norm_num)
theorem B13769477 : Blo 1957435 13769477 := bstep (se 4 (by rfl) ⟨1290888, by rfl⟩ : syracuseStep 13769477 = 2581777) B2581777
theorem B9179651 : Blo 1957435 9179651 := bstep (se 1 (by rfl) ⟨6884738, by rfl⟩ : syracuseStep 9179651 = 13769477) B13769477
theorem B24479069 : Blo 1957435 24479069 := bstep (se 3 (by rfl) ⟨4589825, by rfl⟩ : syracuseStep 24479069 = 9179651) B9179651
theorem B65277517 : Blo 1957435 65277517 := bstep (se 3 (by rfl) ⟨12239534, by rfl⟩ : syracuseStep 65277517 = 24479069) B24479069
theorem B87036689 : Blo 1957435 87036689 := bstep (se 2 (by rfl) ⟨32638758, by rfl⟩ : syracuseStep 87036689 = 65277517) B65277517
theorem B58024459 : Blo 1957435 58024459 := bstep (se 1 (by rfl) ⟨43518344, by rfl⟩ : syracuseStep 58024459 = 87036689) B87036689
theorem B77365945 : Blo 1957435 77365945 := bstep (se 2 (by rfl) ⟨29012229, by rfl⟩ : syracuseStep 77365945 = 58024459) B58024459
theorem B103154593 : Blo 1957435 103154593 := bstep (se 2 (by rfl) ⟨38682972, by rfl⟩ : syracuseStep 103154593 = 77365945) B77365945
theorem B137539457 : Blo 1957435 137539457 := bstep (se 2 (by rfl) ⟨51577296, by rfl⟩ : syracuseStep 137539457 = 103154593) B103154593
theorem B91692971 : Blo 1957435 91692971 := bstep (se 1 (by rfl) ⟨68769728, by rfl⟩ : syracuseStep 91692971 = 137539457) B137539457
theorem B61128647 : Blo 1957435 61128647 := bstep (se 1 (by rfl) ⟨45846485, by rfl⟩ : syracuseStep 61128647 = 91692971) B91692971
theorem B40752431 : Blo 1957435 40752431 := bstep (se 1 (by rfl) ⟨30564323, by rfl⟩ : syracuseStep 40752431 = 61128647) B61128647
theorem B434692597 : Blo 1957435 434692597 := bstep (se 5 (by rfl) ⟨20376215, by rfl⟩ : syracuseStep 434692597 = 40752431) B40752431
theorem B579590129 : Blo 1957435 579590129 := bstep (se 2 (by rfl) ⟨217346298, by rfl⟩ : syracuseStep 579590129 = 434692597) B434692597
theorem B386393419 : Blo 1957435 386393419 := bstep (se 1 (by rfl) ⟨289795064, by rfl⟩ : syracuseStep 386393419 = 579590129) B579590129
theorem B515191225 : Blo 1957435 515191225 := bstep (se 2 (by rfl) ⟨193196709, by rfl⟩ : syracuseStep 515191225 = 386393419) B386393419
theorem B686921633 : Blo 1957435 686921633 := bstep (se 2 (by rfl) ⟨257595612, by rfl⟩ : syracuseStep 686921633 = 515191225) B515191225
theorem B457947755 : Blo 1957435 457947755 := bstep (se 1 (by rfl) ⟨343460816, by rfl⟩ : syracuseStep 457947755 = 686921633) B686921633
theorem B305298503 : Blo 1957435 305298503 := bstep (se 1 (by rfl) ⟨228973877, by rfl⟩ : syracuseStep 305298503 = 457947755) B457947755
theorem B203532335 : Blo 1957435 203532335 := bstep (se 1 (by rfl) ⟨152649251, by rfl⟩ : syracuseStep 203532335 = 305298503) B305298503
theorem B135688223 : Blo 1957435 135688223 := bstep (se 1 (by rfl) ⟨101766167, by rfl⟩ : syracuseStep 135688223 = 203532335) B203532335
theorem B90458815 : Blo 1957435 90458815 := bstep (se 1 (by rfl) ⟨67844111, by rfl⟩ : syracuseStep 90458815 = 135688223) B135688223
theorem B120611753 : Blo 1957435 120611753 := bstep (se 2 (by rfl) ⟨45229407, by rfl⟩ : syracuseStep 120611753 = 90458815) B90458815
theorem B80407835 : Blo 1957435 80407835 := bstep (se 1 (by rfl) ⟨60305876, by rfl⟩ : syracuseStep 80407835 = 120611753) B120611753
theorem B53605223 : Blo 1957435 53605223 := bstep (se 1 (by rfl) ⟨40203917, by rfl⟩ : syracuseStep 53605223 = 80407835) B80407835
theorem B35736815 : Blo 1957435 35736815 := bstep (se 1 (by rfl) ⟨26802611, by rfl⟩ : syracuseStep 35736815 = 53605223) B53605223
theorem B23824543 : Blo 1957435 23824543 := bstep (se 1 (by rfl) ⟨17868407, by rfl⟩ : syracuseStep 23824543 = 35736815) B35736815
theorem B31766057 : Blo 1957435 31766057 := bstep (se 2 (by rfl) ⟨11912271, by rfl⟩ : syracuseStep 31766057 = 23824543) B23824543
theorem B21177371 : Blo 1957435 21177371 := bstep (se 1 (by rfl) ⟨15883028, by rfl⟩ : syracuseStep 21177371 = 31766057) B31766057
theorem B14118247 : Blo 1957435 14118247 := bstep (se 1 (by rfl) ⟨10588685, by rfl⟩ : syracuseStep 14118247 = 21177371) B21177371
theorem B18824329 : Blo 1957435 18824329 := bstep (se 2 (by rfl) ⟨7059123, by rfl⟩ : syracuseStep 18824329 = 14118247) B14118247
theorem B25099105 : Blo 1957435 25099105 := bstep (se 2 (by rfl) ⟨9412164, by rfl⟩ : syracuseStep 25099105 = 18824329) B18824329
theorem B33465473 : Blo 1957435 33465473 := bstep (se 2 (by rfl) ⟨12549552, by rfl⟩ : syracuseStep 33465473 = 25099105) B25099105
theorem B22310315 : Blo 1957435 22310315 := bstep (se 1 (by rfl) ⟨16732736, by rfl⟩ : syracuseStep 22310315 = 33465473) B33465473
theorem B14873543 : Blo 1957435 14873543 := bstep (se 1 (by rfl) ⟨11155157, by rfl⟩ : syracuseStep 14873543 = 22310315) B22310315
theorem B9915695 : Blo 1957435 9915695 := bstep (se 1 (by rfl) ⟨7436771, by rfl⟩ : syracuseStep 9915695 = 14873543) B14873543
theorem B6610463 : Blo 1957435 6610463 := bstep (se 1 (by rfl) ⟨4957847, by rfl⟩ : syracuseStep 6610463 = 9915695) B9915695
theorem B4406975 : Blo 1957435 4406975 := bstep (se 1 (by rfl) ⟨3305231, by rfl⟩ : syracuseStep 4406975 = 6610463) B6610463
theorem B2937983 : Blo 1957435 2937983 := bstep (se 1 (by rfl) ⟨2203487, by rfl⟩ : syracuseStep 2937983 = 4406975) B4406975
theorem B1958655 : Blo 1957435 1958655 := bstep (se 1 (by rfl) ⟨1468991, by rfl⟩ : syracuseStep 1958655 = 2937983) B2937983
theorem B2937989 : Blo 1957435 2937989 := bbase (se 4 (by rfl) ⟨275436, by rfl⟩ : syracuseStep 2937989 = 550873) (by norm_num)
theorem B1958659 : Blo 1957435 1958659 := bstep (se 1 (by rfl) ⟨1468994, by rfl⟩ : syracuseStep 1958659 = 2937989) B2937989
theorem B3305245 : Blo 1957435 3305245 := bbase (se 3 (by rfl) ⟨619733, by rfl⟩ : syracuseStep 3305245 = 1239467) (by norm_num)
theorem B4406993 : Blo 1957435 4406993 := bstep (se 2 (by rfl) ⟨1652622, by rfl⟩ : syracuseStep 4406993 = 3305245) B3305245
theorem B2937995 : Blo 1957435 2937995 := bstep (se 1 (by rfl) ⟨2203496, by rfl⟩ : syracuseStep 2937995 = 4406993) B4406993
theorem B1958663 : Blo 1957435 1958663 := bstep (se 1 (by rfl) ⟨1468997, by rfl⟩ : syracuseStep 1958663 = 2937995) B2937995
theorem B2203501 : Blo 1957435 2203501 := bbase (se 3 (by rfl) ⟨413156, by rfl⟩ : syracuseStep 2203501 = 826313) (by norm_num)
theorem B2938001 : Blo 1957435 2938001 := bstep (se 2 (by rfl) ⟨1101750, by rfl⟩ : syracuseStep 2938001 = 2203501) B2203501
theorem B1958667 : Blo 1957435 1958667 := bstep (se 1 (by rfl) ⟨1469000, by rfl⟩ : syracuseStep 1958667 = 2938001) B2938001
theorem B6610517 : Blo 1957435 6610517 := bbase (se 8 (by rfl) ⟨38733, by rfl⟩ : syracuseStep 6610517 = 77467) (by norm_num)
theorem B4407011 : Blo 1957435 4407011 := bstep (se 1 (by rfl) ⟨3305258, by rfl⟩ : syracuseStep 4407011 = 6610517) B6610517
theorem B2938007 : Blo 1957435 2938007 := bstep (se 1 (by rfl) ⟨2203505, by rfl⟩ : syracuseStep 2938007 = 4407011) B4407011
theorem B1958671 : Blo 1957435 1958671 := bstep (se 1 (by rfl) ⟨1469003, by rfl⟩ : syracuseStep 1958671 = 2938007) B2938007
theorem B2938013 : Blo 1957435 2938013 := bbase (se 3 (by rfl) ⟨550877, by rfl⟩ : syracuseStep 2938013 = 1101755) (by norm_num)
theorem B1958675 : Blo 1957435 1958675 := bstep (se 1 (by rfl) ⟨1469006, by rfl⟩ : syracuseStep 1958675 = 2938013) B2938013
theorem B4407029 : Blo 1957435 4407029 := bbase (se 5 (by rfl) ⟨206579, by rfl⟩ : syracuseStep 4407029 = 413159) (by norm_num)
theorem B2938019 : Blo 1957435 2938019 := bstep (se 1 (by rfl) ⟨2203514, by rfl⟩ : syracuseStep 2938019 = 4407029) B4407029
theorem B1958679 : Blo 1957435 1958679 := bstep (se 1 (by rfl) ⟨1469009, by rfl⟩ : syracuseStep 1958679 = 2938019) B2938019
theorem B3529613 : Blo 1957435 3529613 := bbase (se 3 (by rfl) ⟨661802, by rfl⟩ : syracuseStep 3529613 = 1323605) (by norm_num)
theorem B9412301 : Blo 1957435 9412301 := bstep (se 3 (by rfl) ⟨1764806, by rfl⟩ : syracuseStep 9412301 = 3529613) B3529613
theorem B25099469 : Blo 1957435 25099469 := bstep (se 3 (by rfl) ⟨4706150, by rfl⟩ : syracuseStep 25099469 = 9412301) B9412301
theorem B16732979 : Blo 1957435 16732979 := bstep (se 1 (by rfl) ⟨12549734, by rfl⟩ : syracuseStep 16732979 = 25099469) B25099469
theorem B11155319 : Blo 1957435 11155319 := bstep (se 1 (by rfl) ⟨8366489, by rfl⟩ : syracuseStep 11155319 = 16732979) B16732979
theorem B7436879 : Blo 1957435 7436879 := bstep (se 1 (by rfl) ⟨5577659, by rfl⟩ : syracuseStep 7436879 = 11155319) B11155319
theorem B4957919 : Blo 1957435 4957919 := bstep (se 1 (by rfl) ⟨3718439, by rfl⟩ : syracuseStep 4957919 = 7436879) B7436879
theorem B3305279 : Blo 1957435 3305279 := bstep (se 1 (by rfl) ⟨2478959, by rfl⟩ : syracuseStep 3305279 = 4957919) B4957919
theorem B2203519 : Blo 1957435 2203519 := bstep (se 1 (by rfl) ⟨1652639, by rfl⟩ : syracuseStep 2203519 = 3305279) B3305279
theorem B2938025 : Blo 1957435 2938025 := bstep (se 2 (by rfl) ⟨1101759, by rfl⟩ : syracuseStep 2938025 = 2203519) B2203519
theorem B1958683 : Blo 1957435 1958683 := bstep (se 1 (by rfl) ⟨1469012, by rfl⟩ : syracuseStep 1958683 = 2938025) B2938025
theorem B4183253 : Blo 1957435 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B2788835 : Blo 1957435 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B7436893 : Blo 1957435 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B9915857 : Blo 1957435 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B6610571 : Blo 1957435 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B4407047 : Blo 1957435 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B2938031 : Blo 1957435 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B1958687 : Blo 1957435 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B2938037 : Blo 1957435 2938037 := bbase (se 5 (by rfl) ⟨137720, by rfl⟩ : syracuseStep 2938037 = 275441) (by norm_num)
theorem B1958691 : Blo 1957435 1958691 := bstep (se 1 (by rfl) ⟨1469018, by rfl⟩ : syracuseStep 1958691 = 2938037) B2938037
theorem B4957949 : Blo 1957435 4957949 := bbase (se 3 (by rfl) ⟨929615, by rfl⟩ : syracuseStep 4957949 = 1859231) (by norm_num)
theorem B3305299 : Blo 1957435 3305299 := bstep (se 1 (by rfl) ⟨2478974, by rfl⟩ : syracuseStep 3305299 = 4957949) B4957949
theorem B4407065 : Blo 1957435 4407065 := bstep (se 2 (by rfl) ⟨1652649, by rfl⟩ : syracuseStep 4407065 = 3305299) B3305299
theorem B2938043 : Blo 1957435 2938043 := bstep (se 1 (by rfl) ⟨2203532, by rfl⟩ : syracuseStep 2938043 = 4407065) B4407065
theorem B1958695 : Blo 1957435 1958695 := bstep (se 1 (by rfl) ⟨1469021, by rfl⟩ : syracuseStep 1958695 = 2938043) B2938043
theorem B2203537 : Blo 1957435 2203537 := bbase (se 2 (by rfl) ⟨826326, by rfl⟩ : syracuseStep 2203537 = 1652653) (by norm_num)
theorem B2938049 : Blo 1957435 2938049 := bstep (se 2 (by rfl) ⟨1101768, by rfl⟩ : syracuseStep 2938049 = 2203537) B2203537
theorem B1958699 : Blo 1957435 1958699 := bstep (se 1 (by rfl) ⟨1469024, by rfl⟩ : syracuseStep 1958699 = 2938049) B2938049
theorem B3718477 : Blo 1957435 3718477 := bbase (se 3 (by rfl) ⟨697214, by rfl⟩ : syracuseStep 3718477 = 1394429) (by norm_num)
theorem B4957969 : Blo 1957435 4957969 := bstep (se 2 (by rfl) ⟨1859238, by rfl⟩ : syracuseStep 4957969 = 3718477) B3718477
theorem B6610625 : Blo 1957435 6610625 := bstep (se 2 (by rfl) ⟨2478984, by rfl⟩ : syracuseStep 6610625 = 4957969) B4957969
theorem B4407083 : Blo 1957435 4407083 := bstep (se 1 (by rfl) ⟨3305312, by rfl⟩ : syracuseStep 4407083 = 6610625) B6610625
theorem B2938055 : Blo 1957435 2938055 := bstep (se 1 (by rfl) ⟨2203541, by rfl⟩ : syracuseStep 2938055 = 4407083) B4407083
theorem B1958703 : Blo 1957435 1958703 := bstep (se 1 (by rfl) ⟨1469027, by rfl⟩ : syracuseStep 1958703 = 2938055) B2938055
theorem B2938061 : Blo 1957435 2938061 := bbase (se 3 (by rfl) ⟨550886, by rfl⟩ : syracuseStep 2938061 = 1101773) (by norm_num)
theorem B1958707 : Blo 1957435 1958707 := bstep (se 1 (by rfl) ⟨1469030, by rfl⟩ : syracuseStep 1958707 = 2938061) B2938061
theorem B4407101 : Blo 1957435 4407101 := bbase (se 3 (by rfl) ⟨826331, by rfl⟩ : syracuseStep 4407101 = 1652663) (by norm_num)
theorem B2938067 : Blo 1957435 2938067 := bstep (se 1 (by rfl) ⟨2203550, by rfl⟩ : syracuseStep 2938067 = 4407101) B4407101
theorem B1958711 : Blo 1957435 1958711 := bstep (se 1 (by rfl) ⟨1469033, by rfl⟩ : syracuseStep 1958711 = 2938067) B2938067
theorem B3305333 : Blo 1957435 3305333 := bbase (se 5 (by rfl) ⟨154937, by rfl⟩ : syracuseStep 3305333 = 309875) (by norm_num)
theorem B2203555 : Blo 1957435 2203555 := bstep (se 1 (by rfl) ⟨1652666, by rfl⟩ : syracuseStep 2203555 = 3305333) B3305333
theorem B2938073 : Blo 1957435 2938073 := bstep (se 2 (by rfl) ⟨1101777, by rfl⟩ : syracuseStep 2938073 = 2203555) B2203555
theorem B1958715 : Blo 1957435 1958715 := bstep (se 1 (by rfl) ⟨1469036, by rfl⟩ : syracuseStep 1958715 = 2938073) B2938073
theorem B4706237 : Blo 1957435 4706237 := bbase (se 3 (by rfl) ⟨882419, by rfl⟩ : syracuseStep 4706237 = 1764839) (by norm_num)
theorem B3137491 : Blo 1957435 3137491 := bstep (se 1 (by rfl) ⟨2353118, by rfl⟩ : syracuseStep 3137491 = 4706237) B4706237
theorem B4183321 : Blo 1957435 4183321 := bstep (se 2 (by rfl) ⟨1568745, by rfl⟩ : syracuseStep 4183321 = 3137491) B3137491
theorem B5577761 : Blo 1957435 5577761 := bstep (se 2 (by rfl) ⟨2091660, by rfl⟩ : syracuseStep 5577761 = 4183321) B4183321
theorem B14874029 : Blo 1957435 14874029 := bstep (se 3 (by rfl) ⟨2788880, by rfl⟩ : syracuseStep 14874029 = 5577761) B5577761
theorem B9916019 : Blo 1957435 9916019 := bstep (se 1 (by rfl) ⟨7437014, by rfl⟩ : syracuseStep 9916019 = 14874029) B14874029
theorem B6610679 : Blo 1957435 6610679 := bstep (se 1 (by rfl) ⟨4958009, by rfl⟩ : syracuseStep 6610679 = 9916019) B9916019
theorem B4407119 : Blo 1957435 4407119 := bstep (se 1 (by rfl) ⟨3305339, by rfl⟩ : syracuseStep 4407119 = 6610679) B6610679
theorem B2938079 : Blo 1957435 2938079 := bstep (se 1 (by rfl) ⟨2203559, by rfl⟩ : syracuseStep 2938079 = 4407119) B4407119
theorem B1958719 : Blo 1957435 1958719 := bstep (se 1 (by rfl) ⟨1469039, by rfl⟩ : syracuseStep 1958719 = 2938079) B2938079
theorem B2938085 : Blo 1957435 2938085 := bbase (se 4 (by rfl) ⟨275445, by rfl⟩ : syracuseStep 2938085 = 550891) (by norm_num)
theorem B1958723 : Blo 1957435 1958723 := bstep (se 1 (by rfl) ⟨1469042, by rfl⟩ : syracuseStep 1958723 = 2938085) B2938085
theorem B3529693 : Blo 1957435 3529693 := bbase (se 3 (by rfl) ⟨661817, by rfl⟩ : syracuseStep 3529693 = 1323635) (by norm_num)
theorem B4706257 : Blo 1957435 4706257 := bstep (se 2 (by rfl) ⟨1764846, by rfl⟩ : syracuseStep 4706257 = 3529693) B3529693
theorem B6275009 : Blo 1957435 6275009 := bstep (se 2 (by rfl) ⟨2353128, by rfl⟩ : syracuseStep 6275009 = 4706257) B4706257
theorem B4183339 : Blo 1957435 4183339 := bstep (se 1 (by rfl) ⟨3137504, by rfl⟩ : syracuseStep 4183339 = 6275009) B6275009
theorem B5577785 : Blo 1957435 5577785 := bstep (se 2 (by rfl) ⟨2091669, by rfl⟩ : syracuseStep 5577785 = 4183339) B4183339
theorem B3718523 : Blo 1957435 3718523 := bstep (se 1 (by rfl) ⟨2788892, by rfl⟩ : syracuseStep 3718523 = 5577785) B5577785
theorem B2479015 : Blo 1957435 2479015 := bstep (se 1 (by rfl) ⟨1859261, by rfl⟩ : syracuseStep 2479015 = 3718523) B3718523
theorem B3305353 : Blo 1957435 3305353 := bstep (se 2 (by rfl) ⟨1239507, by rfl⟩ : syracuseStep 3305353 = 2479015) B2479015
theorem B4407137 : Blo 1957435 4407137 := bstep (se 2 (by rfl) ⟨1652676, by rfl⟩ : syracuseStep 4407137 = 3305353) B3305353
theorem B2938091 : Blo 1957435 2938091 := bstep (se 1 (by rfl) ⟨2203568, by rfl⟩ : syracuseStep 2938091 = 4407137) B4407137
theorem B1958727 : Blo 1957435 1958727 := bstep (se 1 (by rfl) ⟨1469045, by rfl⟩ : syracuseStep 1958727 = 2938091) B2938091
theorem B2203573 : Blo 1957435 2203573 := bbase (se 5 (by rfl) ⟨103292, by rfl⟩ : syracuseStep 2203573 = 206585) (by norm_num)
theorem B2938097 : Blo 1957435 2938097 := bstep (se 2 (by rfl) ⟨1101786, by rfl⟩ : syracuseStep 2938097 = 2203573) B2203573
theorem B1958731 : Blo 1957435 1958731 := bstep (se 1 (by rfl) ⟨1469048, by rfl⟩ : syracuseStep 1958731 = 2938097) B2938097
theorem B2479025 : Blo 1957435 2479025 := bbase (se 2 (by rfl) ⟨929634, by rfl⟩ : syracuseStep 2479025 = 1859269) (by norm_num)
theorem B6610733 : Blo 1957435 6610733 := bstep (se 3 (by rfl) ⟨1239512, by rfl⟩ : syracuseStep 6610733 = 2479025) B2479025
theorem B4407155 : Blo 1957435 4407155 := bstep (se 1 (by rfl) ⟨3305366, by rfl⟩ : syracuseStep 4407155 = 6610733) B6610733
theorem B2938103 : Blo 1957435 2938103 := bstep (se 1 (by rfl) ⟨2203577, by rfl⟩ : syracuseStep 2938103 = 4407155) B4407155
theorem B1958735 : Blo 1957435 1958735 := bstep (se 1 (by rfl) ⟨1469051, by rfl⟩ : syracuseStep 1958735 = 2938103) B2938103
theorem B2938109 : Blo 1957435 2938109 := bbase (se 3 (by rfl) ⟨550895, by rfl⟩ : syracuseStep 2938109 = 1101791) (by norm_num)
theorem B1958739 : Blo 1957435 1958739 := bstep (se 1 (by rfl) ⟨1469054, by rfl⟩ : syracuseStep 1958739 = 2938109) B2938109
theorem B4407173 : Blo 1957435 4407173 := bbase (se 4 (by rfl) ⟨413172, by rfl⟩ : syracuseStep 4407173 = 826345) (by norm_num)
theorem B2938115 : Blo 1957435 2938115 := bstep (se 1 (by rfl) ⟨2203586, by rfl⟩ : syracuseStep 2938115 = 4407173) B4407173
theorem B1958743 : Blo 1957435 1958743 := bstep (se 1 (by rfl) ⟨1469057, by rfl⟩ : syracuseStep 1958743 = 2938115) B2938115
theorem B2353153 : Blo 1957435 2353153 := bbase (se 2 (by rfl) ⟨882432, by rfl⟩ : syracuseStep 2353153 = 1764865) (by norm_num)
theorem B3137537 : Blo 1957435 3137537 := bstep (se 2 (by rfl) ⟨1176576, by rfl⟩ : syracuseStep 3137537 = 2353153) B2353153
theorem B2091691 : Blo 1957435 2091691 := bstep (se 1 (by rfl) ⟨1568768, by rfl⟩ : syracuseStep 2091691 = 3137537) B3137537
theorem B2788921 : Blo 1957435 2788921 := bstep (se 2 (by rfl) ⟨1045845, by rfl⟩ : syracuseStep 2788921 = 2091691) B2091691
theorem B3718561 : Blo 1957435 3718561 := bstep (se 2 (by rfl) ⟨1394460, by rfl⟩ : syracuseStep 3718561 = 2788921) B2788921
theorem B4958081 : Blo 1957435 4958081 := bstep (se 2 (by rfl) ⟨1859280, by rfl⟩ : syracuseStep 4958081 = 3718561) B3718561
theorem B3305387 : Blo 1957435 3305387 := bstep (se 1 (by rfl) ⟨2479040, by rfl⟩ : syracuseStep 3305387 = 4958081) B4958081
theorem B2203591 : Blo 1957435 2203591 := bstep (se 1 (by rfl) ⟨1652693, by rfl⟩ : syracuseStep 2203591 = 3305387) B3305387
theorem B2938121 : Blo 1957435 2938121 := bstep (se 2 (by rfl) ⟨1101795, by rfl⟩ : syracuseStep 2938121 = 2203591) B2203591
theorem B1958747 : Blo 1957435 1958747 := bstep (se 1 (by rfl) ⟨1469060, by rfl⟩ : syracuseStep 1958747 = 2938121) B2938121
theorem B9916181 : Blo 1957435 9916181 := bbase (se 6 (by rfl) ⟨232410, by rfl⟩ : syracuseStep 9916181 = 464821) (by norm_num)
theorem B6610787 : Blo 1957435 6610787 := bstep (se 1 (by rfl) ⟨4958090, by rfl⟩ : syracuseStep 6610787 = 9916181) B9916181
theorem B4407191 : Blo 1957435 4407191 := bstep (se 1 (by rfl) ⟨3305393, by rfl⟩ : syracuseStep 4407191 = 6610787) B6610787
theorem B2938127 : Blo 1957435 2938127 := bstep (se 1 (by rfl) ⟨2203595, by rfl⟩ : syracuseStep 2938127 = 4407191) B4407191
theorem B1958751 : Blo 1957435 1958751 := bstep (se 1 (by rfl) ⟨1469063, by rfl⟩ : syracuseStep 1958751 = 2938127) B2938127
theorem B2938133 : Blo 1957435 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B1958755 : Blo 1957435 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B5956453 : Blo 1957435 5956453 := bbase (se 4 (by rfl) ⟨558417, by rfl⟩ : syracuseStep 5956453 = 1116835) (by norm_num)
theorem B7941937 : Blo 1957435 7941937 := bstep (se 2 (by rfl) ⟨2978226, by rfl⟩ : syracuseStep 7941937 = 5956453) B5956453
theorem B10589249 : Blo 1957435 10589249 := bstep (se 2 (by rfl) ⟨3970968, by rfl⟩ : syracuseStep 10589249 = 7941937) B7941937
theorem B28237997 : Blo 1957435 28237997 := bstep (se 3 (by rfl) ⟨5294624, by rfl⟩ : syracuseStep 28237997 = 10589249) B10589249
theorem B18825331 : Blo 1957435 18825331 := bstep (se 1 (by rfl) ⟨14118998, by rfl⟩ : syracuseStep 18825331 = 28237997) B28237997
theorem B25100441 : Blo 1957435 25100441 := bstep (se 2 (by rfl) ⟨9412665, by rfl⟩ : syracuseStep 25100441 = 18825331) B18825331
theorem B16733627 : Blo 1957435 16733627 := bstep (se 1 (by rfl) ⟨12550220, by rfl⟩ : syracuseStep 16733627 = 25100441) B25100441
theorem B11155751 : Blo 1957435 11155751 := bstep (se 1 (by rfl) ⟨8366813, by rfl⟩ : syracuseStep 11155751 = 16733627) B16733627
theorem B7437167 : Blo 1957435 7437167 := bstep (se 1 (by rfl) ⟨5577875, by rfl⟩ : syracuseStep 7437167 = 11155751) B11155751
theorem B4958111 : Blo 1957435 4958111 := bstep (se 1 (by rfl) ⟨3718583, by rfl⟩ : syracuseStep 4958111 = 7437167) B7437167
theorem B3305407 : Blo 1957435 3305407 := bstep (se 1 (by rfl) ⟨2479055, by rfl⟩ : syracuseStep 3305407 = 4958111) B4958111
theorem B4407209 : Blo 1957435 4407209 := bstep (se 2 (by rfl) ⟨1652703, by rfl⟩ : syracuseStep 4407209 = 3305407) B3305407
theorem B2938139 : Blo 1957435 2938139 := bstep (se 1 (by rfl) ⟨2203604, by rfl⟩ : syracuseStep 2938139 = 4407209) B4407209
theorem B1958759 : Blo 1957435 1958759 := bstep (se 1 (by rfl) ⟨1469069, by rfl⟩ : syracuseStep 1958759 = 2938139) B2938139
theorem B2203609 : Blo 1957435 2203609 := bbase (se 2 (by rfl) ⟨826353, by rfl⟩ : syracuseStep 2203609 = 1652707) (by norm_num)
theorem B2938145 : Blo 1957435 2938145 := bstep (se 2 (by rfl) ⟨1101804, by rfl⟩ : syracuseStep 2938145 = 2203609) B2203609
theorem B1958763 : Blo 1957435 1958763 := bstep (se 1 (by rfl) ⟨1469072, by rfl⟩ : syracuseStep 1958763 = 2938145) B2938145
theorem B2788949 : Blo 1957435 2788949 := bbase (se 8 (by rfl) ⟨16341, by rfl⟩ : syracuseStep 2788949 = 32683) (by norm_num)
theorem B7437197 : Blo 1957435 7437197 := bstep (se 3 (by rfl) ⟨1394474, by rfl⟩ : syracuseStep 7437197 = 2788949) B2788949
theorem B4958131 : Blo 1957435 4958131 := bstep (se 1 (by rfl) ⟨3718598, by rfl⟩ : syracuseStep 4958131 = 7437197) B7437197
theorem B6610841 : Blo 1957435 6610841 := bstep (se 2 (by rfl) ⟨2479065, by rfl⟩ : syracuseStep 6610841 = 4958131) B4958131
theorem B4407227 : Blo 1957435 4407227 := bstep (se 1 (by rfl) ⟨3305420, by rfl⟩ : syracuseStep 4407227 = 6610841) B6610841
theorem B2938151 : Blo 1957435 2938151 := bstep (se 1 (by rfl) ⟨2203613, by rfl⟩ : syracuseStep 2938151 = 4407227) B4407227
theorem B1958767 : Blo 1957435 1958767 := bstep (se 1 (by rfl) ⟨1469075, by rfl⟩ : syracuseStep 1958767 = 2938151) B2938151
theorem B2938157 : Blo 1957435 2938157 := bbase (se 3 (by rfl) ⟨550904, by rfl⟩ : syracuseStep 2938157 = 1101809) (by norm_num)
theorem B1958771 : Blo 1957435 1958771 := bstep (se 1 (by rfl) ⟨1469078, by rfl⟩ : syracuseStep 1958771 = 2938157) B2938157
theorem B4407245 : Blo 1957435 4407245 := bbase (se 3 (by rfl) ⟨826358, by rfl⟩ : syracuseStep 4407245 = 1652717) (by norm_num)
theorem B2938163 : Blo 1957435 2938163 := bstep (se 1 (by rfl) ⟨2203622, by rfl⟩ : syracuseStep 2938163 = 4407245) B4407245
theorem B1958775 : Blo 1957435 1958775 := bstep (se 1 (by rfl) ⟨1469081, by rfl⟩ : syracuseStep 1958775 = 2938163) B2938163
theorem B2479081 : Blo 1957435 2479081 := bbase (se 2 (by rfl) ⟨929655, by rfl⟩ : syracuseStep 2479081 = 1859311) (by norm_num)
theorem B3305441 : Blo 1957435 3305441 := bstep (se 2 (by rfl) ⟨1239540, by rfl⟩ : syracuseStep 3305441 = 2479081) B2479081
theorem B2203627 : Blo 1957435 2203627 := bstep (se 1 (by rfl) ⟨1652720, by rfl⟩ : syracuseStep 2203627 = 3305441) B3305441
theorem B2938169 : Blo 1957435 2938169 := bstep (se 2 (by rfl) ⟨1101813, by rfl⟩ : syracuseStep 2938169 = 2203627) B2203627
theorem B1958779 : Blo 1957435 1958779 := bstep (se 1 (by rfl) ⟨1469084, by rfl⟩ : syracuseStep 1958779 = 2938169) B2938169
theorem B1985509 : Blo 1957435 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B2647345 : Blo 1957435 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B3529793 : Blo 1957435 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B2353195 : Blo 1957435 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B12550373 : Blo 1957435 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B8366915 : Blo 1957435 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B22311773 : Blo 1957435 22311773 := bstep (se 3 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 22311773 = 8366915) B8366915
theorem B14874515 : Blo 1957435 14874515 := bstep (se 1 (by rfl) ⟨11155886, by rfl⟩ : syracuseStep 14874515 = 22311773) B22311773
theorem B9916343 : Blo 1957435 9916343 := bstep (se 1 (by rfl) ⟨7437257, by rfl⟩ : syracuseStep 9916343 = 14874515) B14874515
theorem B6610895 : Blo 1957435 6610895 := bstep (se 1 (by rfl) ⟨4958171, by rfl⟩ : syracuseStep 6610895 = 9916343) B9916343
theorem B4407263 : Blo 1957435 4407263 := bstep (se 1 (by rfl) ⟨3305447, by rfl⟩ : syracuseStep 4407263 = 6610895) B6610895
theorem B2938175 : Blo 1957435 2938175 := bstep (se 1 (by rfl) ⟨2203631, by rfl⟩ : syracuseStep 2938175 = 4407263) B4407263
theorem B1958783 : Blo 1957435 1958783 := bstep (se 1 (by rfl) ⟨1469087, by rfl⟩ : syracuseStep 1958783 = 2938175) B2938175
theorem B2938181 : Blo 1957435 2938181 := bbase (se 4 (by rfl) ⟨275454, by rfl⟩ : syracuseStep 2938181 = 550909) (by norm_num)
theorem B1958787 : Blo 1957435 1958787 := bstep (se 1 (by rfl) ⟨1469090, by rfl⟩ : syracuseStep 1958787 = 2938181) B2938181
theorem B3305461 : Blo 1957435 3305461 := bbase (se 5 (by rfl) ⟨154943, by rfl⟩ : syracuseStep 3305461 = 309887) (by norm_num)
theorem B4407281 : Blo 1957435 4407281 := bstep (se 2 (by rfl) ⟨1652730, by rfl⟩ : syracuseStep 4407281 = 3305461) B3305461
theorem B2938187 : Blo 1957435 2938187 := bstep (se 1 (by rfl) ⟨2203640, by rfl⟩ : syracuseStep 2938187 = 4407281) B4407281
theorem B1958791 : Blo 1957435 1958791 := bstep (se 1 (by rfl) ⟨1469093, by rfl⟩ : syracuseStep 1958791 = 2938187) B2938187
theorem B2203645 : Blo 1957435 2203645 := bbase (se 3 (by rfl) ⟨413183, by rfl⟩ : syracuseStep 2203645 = 826367) (by norm_num)
theorem B2938193 : Blo 1957435 2938193 := bstep (se 2 (by rfl) ⟨1101822, by rfl⟩ : syracuseStep 2938193 = 2203645) B2203645
theorem B1958795 : Blo 1957435 1958795 := bstep (se 1 (by rfl) ⟨1469096, by rfl⟩ : syracuseStep 1958795 = 2938193) B2938193
theorem B6610949 : Blo 1957435 6610949 := bbase (se 4 (by rfl) ⟨619776, by rfl⟩ : syracuseStep 6610949 = 1239553) (by norm_num)
theorem B4407299 : Blo 1957435 4407299 := bstep (se 1 (by rfl) ⟨3305474, by rfl⟩ : syracuseStep 4407299 = 6610949) B6610949
theorem B2938199 : Blo 1957435 2938199 := bstep (se 1 (by rfl) ⟨2203649, by rfl⟩ : syracuseStep 2938199 = 4407299) B4407299
theorem B1958799 : Blo 1957435 1958799 := bstep (se 1 (by rfl) ⟨1469099, by rfl⟩ : syracuseStep 1958799 = 2938199) B2938199
theorem B2938205 : Blo 1957435 2938205 := bbase (se 3 (by rfl) ⟨550913, by rfl⟩ : syracuseStep 2938205 = 1101827) (by norm_num)
theorem B1958803 : Blo 1957435 1958803 := bstep (se 1 (by rfl) ⟨1469102, by rfl⟩ : syracuseStep 1958803 = 2938205) B2938205
theorem B4407317 : Blo 1957435 4407317 := bbase (se 6 (by rfl) ⟨103296, by rfl⟩ : syracuseStep 4407317 = 206593) (by norm_num)
theorem B2938211 : Blo 1957435 2938211 := bstep (se 1 (by rfl) ⟨2203658, by rfl⟩ : syracuseStep 2938211 = 4407317) B4407317
theorem B1958807 : Blo 1957435 1958807 := bstep (se 1 (by rfl) ⟨1469105, by rfl⟩ : syracuseStep 1958807 = 2938211) B2938211
theorem B7437365 : Blo 1957435 7437365 := bbase (se 5 (by rfl) ⟨348626, by rfl⟩ : syracuseStep 7437365 = 697253) (by norm_num)
theorem B4958243 : Blo 1957435 4958243 := bstep (se 1 (by rfl) ⟨3718682, by rfl⟩ : syracuseStep 4958243 = 7437365) B7437365
theorem B3305495 : Blo 1957435 3305495 := bstep (se 1 (by rfl) ⟨2479121, by rfl⟩ : syracuseStep 3305495 = 4958243) B4958243
theorem B2203663 : Blo 1957435 2203663 := bstep (se 1 (by rfl) ⟨1652747, by rfl⟩ : syracuseStep 2203663 = 3305495) B3305495
theorem B2938217 : Blo 1957435 2938217 := bstep (se 2 (by rfl) ⟨1101831, by rfl⟩ : syracuseStep 2938217 = 2203663) B2203663
theorem B1958811 : Blo 1957435 1958811 := bstep (se 1 (by rfl) ⟨1469108, by rfl⟩ : syracuseStep 1958811 = 2938217) B2938217
theorem B3137645 : Blo 1957435 3137645 := bbase (se 3 (by rfl) ⟨588308, by rfl⟩ : syracuseStep 3137645 = 1176617) (by norm_num)
theorem B2091763 : Blo 1957435 2091763 := bstep (se 1 (by rfl) ⟨1568822, by rfl⟩ : syracuseStep 2091763 = 3137645) B3137645
theorem B11156069 : Blo 1957435 11156069 := bstep (se 4 (by rfl) ⟨1045881, by rfl⟩ : syracuseStep 11156069 = 2091763) B2091763
theorem B7437379 : Blo 1957435 7437379 := bstep (se 1 (by rfl) ⟨5578034, by rfl⟩ : syracuseStep 7437379 = 11156069) B11156069
theorem B9916505 : Blo 1957435 9916505 := bstep (se 2 (by rfl) ⟨3718689, by rfl⟩ : syracuseStep 9916505 = 7437379) B7437379
theorem B6611003 : Blo 1957435 6611003 := bstep (se 1 (by rfl) ⟨4958252, by rfl⟩ : syracuseStep 6611003 = 9916505) B9916505
theorem B4407335 : Blo 1957435 4407335 := bstep (se 1 (by rfl) ⟨3305501, by rfl⟩ : syracuseStep 4407335 = 6611003) B6611003
theorem B2938223 : Blo 1957435 2938223 := bstep (se 1 (by rfl) ⟨2203667, by rfl⟩ : syracuseStep 2938223 = 4407335) B4407335
theorem B1958815 : Blo 1957435 1958815 := bstep (se 1 (by rfl) ⟨1469111, by rfl⟩ : syracuseStep 1958815 = 2938223) B2938223
theorem B2938229 : Blo 1957435 2938229 := bbase (se 5 (by rfl) ⟨137729, by rfl⟩ : syracuseStep 2938229 = 275459) (by norm_num)
theorem B1958819 : Blo 1957435 1958819 := bstep (se 1 (by rfl) ⟨1469114, by rfl⟩ : syracuseStep 1958819 = 2938229) B2938229
theorem B2789029 : Blo 1957435 2789029 := bbase (se 4 (by rfl) ⟨261471, by rfl⟩ : syracuseStep 2789029 = 522943) (by norm_num)
theorem B3718705 : Blo 1957435 3718705 := bstep (se 2 (by rfl) ⟨1394514, by rfl⟩ : syracuseStep 3718705 = 2789029) B2789029
theorem B4958273 : Blo 1957435 4958273 := bstep (se 2 (by rfl) ⟨1859352, by rfl⟩ : syracuseStep 4958273 = 3718705) B3718705
theorem B3305515 : Blo 1957435 3305515 := bstep (se 1 (by rfl) ⟨2479136, by rfl⟩ : syracuseStep 3305515 = 4958273) B4958273
theorem B4407353 : Blo 1957435 4407353 := bstep (se 2 (by rfl) ⟨1652757, by rfl⟩ : syracuseStep 4407353 = 3305515) B3305515
theorem B2938235 : Blo 1957435 2938235 := bstep (se 1 (by rfl) ⟨2203676, by rfl⟩ : syracuseStep 2938235 = 4407353) B4407353
theorem B1958823 : Blo 1957435 1958823 := bstep (se 1 (by rfl) ⟨1469117, by rfl⟩ : syracuseStep 1958823 = 2938235) B2938235
theorem B2203681 : Blo 1957435 2203681 := bbase (se 2 (by rfl) ⟨826380, by rfl⟩ : syracuseStep 2203681 = 1652761) (by norm_num)
theorem B2938241 : Blo 1957435 2938241 := bstep (se 2 (by rfl) ⟨1101840, by rfl⟩ : syracuseStep 2938241 = 2203681) B2203681
theorem B1958827 : Blo 1957435 1958827 := bstep (se 1 (by rfl) ⟨1469120, by rfl⟩ : syracuseStep 1958827 = 2938241) B2938241
theorem B4958293 : Blo 1957435 4958293 := bbase (se 8 (by rfl) ⟨29052, by rfl⟩ : syracuseStep 4958293 = 58105) (by norm_num)
theorem B6611057 : Blo 1957435 6611057 := bstep (se 2 (by rfl) ⟨2479146, by rfl⟩ : syracuseStep 6611057 = 4958293) B4958293
theorem B4407371 : Blo 1957435 4407371 := bstep (se 1 (by rfl) ⟨3305528, by rfl⟩ : syracuseStep 4407371 = 6611057) B6611057
theorem B2938247 : Blo 1957435 2938247 := bstep (se 1 (by rfl) ⟨2203685, by rfl⟩ : syracuseStep 2938247 = 4407371) B4407371
theorem B1958831 : Blo 1957435 1958831 := bstep (se 1 (by rfl) ⟨1469123, by rfl⟩ : syracuseStep 1958831 = 2938247) B2938247
theorem B2938253 : Blo 1957435 2938253 := bbase (se 3 (by rfl) ⟨550922, by rfl⟩ : syracuseStep 2938253 = 1101845) (by norm_num)
theorem B1958835 : Blo 1957435 1958835 := bstep (se 1 (by rfl) ⟨1469126, by rfl⟩ : syracuseStep 1958835 = 2938253) B2938253
theorem B4407389 : Blo 1957435 4407389 := bbase (se 3 (by rfl) ⟨826385, by rfl⟩ : syracuseStep 4407389 = 1652771) (by norm_num)
theorem B2938259 : Blo 1957435 2938259 := bstep (se 1 (by rfl) ⟨2203694, by rfl⟩ : syracuseStep 2938259 = 4407389) B4407389
theorem B1958839 : Blo 1957435 1958839 := bstep (se 1 (by rfl) ⟨1469129, by rfl⟩ : syracuseStep 1958839 = 2938259) B2938259
theorem B3305549 : Blo 1957435 3305549 := bbase (se 3 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 3305549 = 1239581) (by norm_num)
theorem B2203699 : Blo 1957435 2203699 := bstep (se 1 (by rfl) ⟨1652774, by rfl⟩ : syracuseStep 2203699 = 3305549) B3305549
theorem B2938265 : Blo 1957435 2938265 := bstep (se 2 (by rfl) ⟨1101849, by rfl⟩ : syracuseStep 2938265 = 2203699) B2203699
theorem B1958843 : Blo 1957435 1958843 := bstep (se 1 (by rfl) ⟨1469132, by rfl⟩ : syracuseStep 1958843 = 2938265) B2938265
theorem B4528493 : Blo 1957435 4528493 := bbase (se 3 (by rfl) ⟨849092, by rfl⟩ : syracuseStep 4528493 = 1698185) (by norm_num)
theorem B3018995 : Blo 1957435 3018995 := bstep (se 1 (by rfl) ⟨2264246, by rfl⟩ : syracuseStep 3018995 = 4528493) B4528493
theorem B2012663 : Blo 1957435 2012663 := bstep (se 1 (by rfl) ⟨1509497, by rfl⟩ : syracuseStep 2012663 = 3018995) B3018995
theorem B85873621 : Blo 1957435 85873621 := bstep (se 7 (by rfl) ⟨1006331, by rfl⟩ : syracuseStep 85873621 = 2012663) B2012663
theorem B114498161 : Blo 1957435 114498161 := bstep (se 2 (by rfl) ⟨42936810, by rfl⟩ : syracuseStep 114498161 = 85873621) B85873621
theorem B76332107 : Blo 1957435 76332107 := bstep (se 1 (by rfl) ⟨57249080, by rfl⟩ : syracuseStep 76332107 = 114498161) B114498161
theorem B50888071 : Blo 1957435 50888071 := bstep (se 1 (by rfl) ⟨38166053, by rfl⟩ : syracuseStep 50888071 = 76332107) B76332107
theorem B271403045 : Blo 1957435 271403045 := bstep (se 4 (by rfl) ⟨25444035, by rfl⟩ : syracuseStep 271403045 = 50888071) B50888071
theorem B180935363 : Blo 1957435 180935363 := bstep (se 1 (by rfl) ⟨135701522, by rfl⟩ : syracuseStep 180935363 = 271403045) B271403045
theorem B120623575 : Blo 1957435 120623575 := bstep (se 1 (by rfl) ⟨90467681, by rfl⟩ : syracuseStep 120623575 = 180935363) B180935363
theorem B160831433 : Blo 1957435 160831433 := bstep (se 2 (by rfl) ⟨60311787, by rfl⟩ : syracuseStep 160831433 = 120623575) B120623575
theorem B107220955 : Blo 1957435 107220955 := bstep (se 1 (by rfl) ⟨80415716, by rfl⟩ : syracuseStep 107220955 = 160831433) B160831433
theorem B142961273 : Blo 1957435 142961273 := bstep (se 2 (by rfl) ⟨53610477, by rfl⟩ : syracuseStep 142961273 = 107220955) B107220955
theorem B95307515 : Blo 1957435 95307515 := bstep (se 1 (by rfl) ⟨71480636, by rfl⟩ : syracuseStep 95307515 = 142961273) B142961273
theorem B63538343 : Blo 1957435 63538343 := bstep (se 1 (by rfl) ⟨47653757, by rfl⟩ : syracuseStep 63538343 = 95307515) B95307515
theorem B42358895 : Blo 1957435 42358895 := bstep (se 1 (by rfl) ⟨31769171, by rfl⟩ : syracuseStep 42358895 = 63538343) B63538343
theorem B28239263 : Blo 1957435 28239263 := bstep (se 1 (by rfl) ⟨21179447, by rfl⟩ : syracuseStep 28239263 = 42358895) B42358895
theorem B18826175 : Blo 1957435 18826175 := bstep (se 1 (by rfl) ⟨14119631, by rfl⟩ : syracuseStep 18826175 = 28239263) B28239263
theorem B12550783 : Blo 1957435 12550783 := bstep (se 1 (by rfl) ⟨9413087, by rfl⟩ : syracuseStep 12550783 = 18826175) B18826175
theorem B16734377 : Blo 1957435 16734377 := bstep (se 2 (by rfl) ⟨6275391, by rfl⟩ : syracuseStep 16734377 = 12550783) B12550783
theorem B11156251 : Blo 1957435 11156251 := bstep (se 1 (by rfl) ⟨8367188, by rfl⟩ : syracuseStep 11156251 = 16734377) B16734377
theorem B14875001 : Blo 1957435 14875001 := bstep (se 2 (by rfl) ⟨5578125, by rfl⟩ : syracuseStep 14875001 = 11156251) B11156251
theorem B9916667 : Blo 1957435 9916667 := bstep (se 1 (by rfl) ⟨7437500, by rfl⟩ : syracuseStep 9916667 = 14875001) B14875001
theorem B6611111 : Blo 1957435 6611111 := bstep (se 1 (by rfl) ⟨4958333, by rfl⟩ : syracuseStep 6611111 = 9916667) B9916667
theorem B4407407 : Blo 1957435 4407407 := bstep (se 1 (by rfl) ⟨3305555, by rfl⟩ : syracuseStep 4407407 = 6611111) B6611111
theorem B2938271 : Blo 1957435 2938271 := bstep (se 1 (by rfl) ⟨2203703, by rfl⟩ : syracuseStep 2938271 = 4407407) B4407407
theorem B1958847 : Blo 1957435 1958847 := bstep (se 1 (by rfl) ⟨1469135, by rfl⟩ : syracuseStep 1958847 = 2938271) B2938271
theorem B2938277 : Blo 1957435 2938277 := bbase (se 4 (by rfl) ⟨275463, by rfl⟩ : syracuseStep 2938277 = 550927) (by norm_num)
theorem B1958851 : Blo 1957435 1958851 := bstep (se 1 (by rfl) ⟨1469138, by rfl⟩ : syracuseStep 1958851 = 2938277) B2938277
theorem B2479177 : Blo 1957435 2479177 := bbase (se 2 (by rfl) ⟨929691, by rfl⟩ : syracuseStep 2479177 = 1859383) (by norm_num)
theorem B3305569 : Blo 1957435 3305569 := bstep (se 2 (by rfl) ⟨1239588, by rfl⟩ : syracuseStep 3305569 = 2479177) B2479177
theorem B4407425 : Blo 1957435 4407425 := bstep (se 2 (by rfl) ⟨1652784, by rfl⟩ : syracuseStep 4407425 = 3305569) B3305569
theorem B2938283 : Blo 1957435 2938283 := bstep (se 1 (by rfl) ⟨2203712, by rfl⟩ : syracuseStep 2938283 = 4407425) B4407425
theorem B1958855 : Blo 1957435 1958855 := bstep (se 1 (by rfl) ⟨1469141, by rfl⟩ : syracuseStep 1958855 = 2938283) B2938283
theorem B2203717 : Blo 1957435 2203717 := bbase (se 4 (by rfl) ⟨206598, by rfl⟩ : syracuseStep 2203717 = 413197) (by norm_num)
theorem B2938289 : Blo 1957435 2938289 := bstep (se 2 (by rfl) ⟨1101858, by rfl⟩ : syracuseStep 2938289 = 2203717) B2203717
theorem B1958859 : Blo 1957435 1958859 := bstep (se 1 (by rfl) ⟨1469144, by rfl⟩ : syracuseStep 1958859 = 2938289) B2938289
theorem B3718781 : Blo 1957435 3718781 := bbase (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) (by norm_num)
theorem B2479187 : Blo 1957435 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B6611165 : Blo 1957435 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B4407443 : Blo 1957435 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B2938295 : Blo 1957435 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B1958863 : Blo 1957435 1958863 := bstep (se 1 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 1958863 = 2938295) B2938295
theorem B2938301 : Blo 1957435 2938301 := bbase (se 3 (by rfl) ⟨550931, by rfl⟩ : syracuseStep 2938301 = 1101863) (by norm_num)
theorem B1958867 : Blo 1957435 1958867 := bstep (se 1 (by rfl) ⟨1469150, by rfl⟩ : syracuseStep 1958867 = 2938301) B2938301
theorem B4407461 : Blo 1957435 4407461 := bbase (se 4 (by rfl) ⟨413199, by rfl⟩ : syracuseStep 4407461 = 826399) (by norm_num)
theorem B2938307 : Blo 1957435 2938307 := bstep (se 1 (by rfl) ⟨2203730, by rfl⟩ : syracuseStep 2938307 = 4407461) B4407461
theorem B1958871 : Blo 1957435 1958871 := bstep (se 1 (by rfl) ⟨1469153, by rfl⟩ : syracuseStep 1958871 = 2938307) B2938307
theorem B4958405 : Blo 1957435 4958405 := bbase (se 4 (by rfl) ⟨464850, by rfl⟩ : syracuseStep 4958405 = 929701) (by norm_num)
theorem B3305603 : Blo 1957435 3305603 := bstep (se 1 (by rfl) ⟨2479202, by rfl⟩ : syracuseStep 3305603 = 4958405) B4958405
theorem B2203735 : Blo 1957435 2203735 := bstep (se 1 (by rfl) ⟨1652801, by rfl⟩ : syracuseStep 2203735 = 3305603) B3305603
theorem B2938313 : Blo 1957435 2938313 := bstep (se 2 (by rfl) ⟨1101867, by rfl⟩ : syracuseStep 2938313 = 2203735) B2203735
theorem B1958875 : Blo 1957435 1958875 := bstep (se 1 (by rfl) ⟨1469156, by rfl⟩ : syracuseStep 1958875 = 2938313) B2938313
theorem B10734389 : Blo 1957435 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B7156259 : Blo 1957435 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B4770839 : Blo 1957435 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B3180559 : Blo 1957435 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B4240745 : Blo 1957435 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B2827163 : Blo 1957435 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B7539101 : Blo 1957435 7539101 := bstep (se 3 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 7539101 = 2827163) B2827163
theorem B5026067 : Blo 1957435 5026067 := bstep (se 1 (by rfl) ⟨3769550, by rfl⟩ : syracuseStep 5026067 = 7539101) B7539101
theorem B3350711 : Blo 1957435 3350711 := bstep (se 1 (by rfl) ⟨2513033, by rfl⟩ : syracuseStep 3350711 = 5026067) B5026067
theorem B2233807 : Blo 1957435 2233807 := bstep (se 1 (by rfl) ⟨1675355, by rfl⟩ : syracuseStep 2233807 = 3350711) B3350711
theorem B11913637 : Blo 1957435 11913637 := bstep (se 4 (by rfl) ⟨1116903, by rfl⟩ : syracuseStep 11913637 = 2233807) B2233807
theorem B15884849 : Blo 1957435 15884849 := bstep (se 2 (by rfl) ⟨5956818, by rfl⟩ : syracuseStep 15884849 = 11913637) B11913637
theorem B10589899 : Blo 1957435 10589899 := bstep (se 1 (by rfl) ⟨7942424, by rfl⟩ : syracuseStep 10589899 = 15884849) B15884849
theorem B14119865 : Blo 1957435 14119865 := bstep (se 2 (by rfl) ⟨5294949, by rfl⟩ : syracuseStep 14119865 = 10589899) B10589899
theorem B9413243 : Blo 1957435 9413243 := bstep (se 1 (by rfl) ⟨7059932, by rfl⟩ : syracuseStep 9413243 = 14119865) B14119865
theorem B6275495 : Blo 1957435 6275495 := bstep (se 1 (by rfl) ⟨4706621, by rfl⟩ : syracuseStep 6275495 = 9413243) B9413243
theorem B4183663 : Blo 1957435 4183663 := bstep (se 1 (by rfl) ⟨3137747, by rfl⟩ : syracuseStep 4183663 = 6275495) B6275495
theorem B5578217 : Blo 1957435 5578217 := bstep (se 2 (by rfl) ⟨2091831, by rfl⟩ : syracuseStep 5578217 = 4183663) B4183663
theorem B3718811 : Blo 1957435 3718811 := bstep (se 1 (by rfl) ⟨2789108, by rfl⟩ : syracuseStep 3718811 = 5578217) B5578217
theorem B9916829 : Blo 1957435 9916829 := bstep (se 3 (by rfl) ⟨1859405, by rfl⟩ : syracuseStep 9916829 = 3718811) B3718811
theorem B6611219 : Blo 1957435 6611219 := bstep (se 1 (by rfl) ⟨4958414, by rfl⟩ : syracuseStep 6611219 = 9916829) B9916829
theorem B4407479 : Blo 1957435 4407479 := bstep (se 1 (by rfl) ⟨3305609, by rfl⟩ : syracuseStep 4407479 = 6611219) B6611219
theorem B2938319 : Blo 1957435 2938319 := bstep (se 1 (by rfl) ⟨2203739, by rfl⟩ : syracuseStep 2938319 = 4407479) B4407479
theorem B1958879 : Blo 1957435 1958879 := bstep (se 1 (by rfl) ⟨1469159, by rfl⟩ : syracuseStep 1958879 = 2938319) B2938319
theorem B2938325 : Blo 1957435 2938325 := bbase (se 7 (by rfl) ⟨34433, by rfl⟩ : syracuseStep 2938325 = 68867) (by norm_num)
theorem B1958883 : Blo 1957435 1958883 := bstep (se 1 (by rfl) ⟨1469162, by rfl⟩ : syracuseStep 1958883 = 2938325) B2938325
theorem B7437653 : Blo 1957435 7437653 := bbase (se 11 (by rfl) ⟨5447, by rfl⟩ : syracuseStep 7437653 = 10895) (by norm_num)
theorem B4958435 : Blo 1957435 4958435 := bstep (se 1 (by rfl) ⟨3718826, by rfl⟩ : syracuseStep 4958435 = 7437653) B7437653
theorem B3305623 : Blo 1957435 3305623 := bstep (se 1 (by rfl) ⟨2479217, by rfl⟩ : syracuseStep 3305623 = 4958435) B4958435
theorem B4407497 : Blo 1957435 4407497 := bstep (se 2 (by rfl) ⟨1652811, by rfl⟩ : syracuseStep 4407497 = 3305623) B3305623
theorem B2938331 : Blo 1957435 2938331 := bstep (se 1 (by rfl) ⟨2203748, by rfl⟩ : syracuseStep 2938331 = 4407497) B4407497
theorem B1958887 : Blo 1957435 1958887 := bstep (se 1 (by rfl) ⟨1469165, by rfl⟩ : syracuseStep 1958887 = 2938331) B2938331
theorem B2203753 : Blo 1957435 2203753 := bbase (se 2 (by rfl) ⟨826407, by rfl⟩ : syracuseStep 2203753 = 1652815) (by norm_num)
theorem B2938337 : Blo 1957435 2938337 := bstep (se 2 (by rfl) ⟨1101876, by rfl⟩ : syracuseStep 2938337 = 2203753) B2203753
theorem B1958891 : Blo 1957435 1958891 := bstep (se 1 (by rfl) ⟨1469168, by rfl⟩ : syracuseStep 1958891 = 2938337) B2938337
theorem B3137773 : Blo 1957435 3137773 := bbase (se 3 (by rfl) ⟨588332, by rfl⟩ : syracuseStep 3137773 = 1176665) (by norm_num)
theorem B4183697 : Blo 1957435 4183697 := bstep (se 2 (by rfl) ⟨1568886, by rfl⟩ : syracuseStep 4183697 = 3137773) B3137773
theorem B11156525 : Blo 1957435 11156525 := bstep (se 3 (by rfl) ⟨2091848, by rfl⟩ : syracuseStep 11156525 = 4183697) B4183697
theorem B7437683 : Blo 1957435 7437683 := bstep (se 1 (by rfl) ⟨5578262, by rfl⟩ : syracuseStep 7437683 = 11156525) B11156525
theorem B4958455 : Blo 1957435 4958455 := bstep (se 1 (by rfl) ⟨3718841, by rfl⟩ : syracuseStep 4958455 = 7437683) B7437683
theorem B6611273 : Blo 1957435 6611273 := bstep (se 2 (by rfl) ⟨2479227, by rfl⟩ : syracuseStep 6611273 = 4958455) B4958455
theorem B4407515 : Blo 1957435 4407515 := bstep (se 1 (by rfl) ⟨3305636, by rfl⟩ : syracuseStep 4407515 = 6611273) B6611273
theorem B2938343 : Blo 1957435 2938343 := bstep (se 1 (by rfl) ⟨2203757, by rfl⟩ : syracuseStep 2938343 = 4407515) B4407515
theorem B1958895 : Blo 1957435 1958895 := bstep (se 1 (by rfl) ⟨1469171, by rfl⟩ : syracuseStep 1958895 = 2938343) B2938343
theorem B2938349 : Blo 1957435 2938349 := bbase (se 3 (by rfl) ⟨550940, by rfl⟩ : syracuseStep 2938349 = 1101881) (by norm_num)
theorem B1958899 : Blo 1957435 1958899 := bstep (se 1 (by rfl) ⟨1469174, by rfl⟩ : syracuseStep 1958899 = 2938349) B2938349
theorem B4407533 : Blo 1957435 4407533 := bbase (se 3 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 4407533 = 1652825) (by norm_num)
theorem B2938355 : Blo 1957435 2938355 := bstep (se 1 (by rfl) ⟨2203766, by rfl⟩ : syracuseStep 2938355 = 4407533) B4407533
theorem B1958903 : Blo 1957435 1958903 := bstep (se 1 (by rfl) ⟨1469177, by rfl⟩ : syracuseStep 1958903 = 2938355) B2938355
theorem B2789149 : Blo 1957435 2789149 := bbase (se 3 (by rfl) ⟨522965, by rfl⟩ : syracuseStep 2789149 = 1045931) (by norm_num)
theorem B3718865 : Blo 1957435 3718865 := bstep (se 2 (by rfl) ⟨1394574, by rfl⟩ : syracuseStep 3718865 = 2789149) B2789149
theorem B2479243 : Blo 1957435 2479243 := bstep (se 1 (by rfl) ⟨1859432, by rfl⟩ : syracuseStep 2479243 = 3718865) B3718865
theorem B3305657 : Blo 1957435 3305657 := bstep (se 2 (by rfl) ⟨1239621, by rfl⟩ : syracuseStep 3305657 = 2479243) B2479243
theorem B2203771 : Blo 1957435 2203771 := bstep (se 1 (by rfl) ⟨1652828, by rfl⟩ : syracuseStep 2203771 = 3305657) B3305657
theorem B2938361 : Blo 1957435 2938361 := bstep (se 2 (by rfl) ⟨1101885, by rfl⟩ : syracuseStep 2938361 = 2203771) B2203771
theorem B1958907 : Blo 1957435 1958907 := bstep (se 1 (by rfl) ⟨1469180, by rfl⟩ : syracuseStep 1958907 = 2938361) B2938361
theorem B3350765 : Blo 1957435 3350765 := bbase (se 3 (by rfl) ⟨628268, by rfl⟩ : syracuseStep 3350765 = 1256537) (by norm_num)
theorem B8935373 : Blo 1957435 8935373 := bstep (se 3 (by rfl) ⟨1675382, by rfl⟩ : syracuseStep 8935373 = 3350765) B3350765
theorem B5956915 : Blo 1957435 5956915 := bstep (se 1 (by rfl) ⟨4467686, by rfl⟩ : syracuseStep 5956915 = 8935373) B8935373
theorem B7942553 : Blo 1957435 7942553 := bstep (se 2 (by rfl) ⟨2978457, by rfl⟩ : syracuseStep 7942553 = 5956915) B5956915
theorem B5295035 : Blo 1957435 5295035 := bstep (se 1 (by rfl) ⟨3971276, by rfl⟩ : syracuseStep 5295035 = 7942553) B7942553
theorem B3530023 : Blo 1957435 3530023 := bstep (se 1 (by rfl) ⟨2647517, by rfl⟩ : syracuseStep 3530023 = 5295035) B5295035
theorem B75307157 : Blo 1957435 75307157 := bstep (se 6 (by rfl) ⟨1765011, by rfl⟩ : syracuseStep 75307157 = 3530023) B3530023
theorem B50204771 : Blo 1957435 50204771 := bstep (se 1 (by rfl) ⟨37653578, by rfl⟩ : syracuseStep 50204771 = 75307157) B75307157
theorem B33469847 : Blo 1957435 33469847 := bstep (se 1 (by rfl) ⟨25102385, by rfl⟩ : syracuseStep 33469847 = 50204771) B50204771
theorem B22313231 : Blo 1957435 22313231 := bstep (se 1 (by rfl) ⟨16734923, by rfl⟩ : syracuseStep 22313231 = 33469847) B33469847
theorem B14875487 : Blo 1957435 14875487 := bstep (se 1 (by rfl) ⟨11156615, by rfl⟩ : syracuseStep 14875487 = 22313231) B22313231
theorem B9916991 : Blo 1957435 9916991 := bstep (se 1 (by rfl) ⟨7437743, by rfl⟩ : syracuseStep 9916991 = 14875487) B14875487
theorem B6611327 : Blo 1957435 6611327 := bstep (se 1 (by rfl) ⟨4958495, by rfl⟩ : syracuseStep 6611327 = 9916991) B9916991
theorem B4407551 : Blo 1957435 4407551 := bstep (se 1 (by rfl) ⟨3305663, by rfl⟩ : syracuseStep 4407551 = 6611327) B6611327
theorem B2938367 : Blo 1957435 2938367 := bstep (se 1 (by rfl) ⟨2203775, by rfl⟩ : syracuseStep 2938367 = 4407551) B4407551
theorem B1958911 : Blo 1957435 1958911 := bstep (se 1 (by rfl) ⟨1469183, by rfl⟩ : syracuseStep 1958911 = 2938367) B2938367
theorem B2938373 : Blo 1957435 2938373 := bbase (se 4 (by rfl) ⟨275472, by rfl⟩ : syracuseStep 2938373 = 550945) (by norm_num)
theorem B1958915 : Blo 1957435 1958915 := bstep (se 1 (by rfl) ⟨1469186, by rfl⟩ : syracuseStep 1958915 = 2938373) B2938373
theorem B3305677 : Blo 1957435 3305677 := bbase (se 3 (by rfl) ⟨619814, by rfl⟩ : syracuseStep 3305677 = 1239629) (by norm_num)
theorem B4407569 : Blo 1957435 4407569 := bstep (se 2 (by rfl) ⟨1652838, by rfl⟩ : syracuseStep 4407569 = 3305677) B3305677
theorem B2938379 : Blo 1957435 2938379 := bstep (se 1 (by rfl) ⟨2203784, by rfl⟩ : syracuseStep 2938379 = 4407569) B4407569
theorem B1958919 : Blo 1957435 1958919 := bstep (se 1 (by rfl) ⟨1469189, by rfl⟩ : syracuseStep 1958919 = 2938379) B2938379
theorem B2203789 : Blo 1957435 2203789 := bbase (se 3 (by rfl) ⟨413210, by rfl⟩ : syracuseStep 2203789 = 826421) (by norm_num)
theorem B2938385 : Blo 1957435 2938385 := bstep (se 2 (by rfl) ⟨1101894, by rfl⟩ : syracuseStep 2938385 = 2203789) B2203789
theorem B1958923 : Blo 1957435 1958923 := bstep (se 1 (by rfl) ⟨1469192, by rfl⟩ : syracuseStep 1958923 = 2938385) B2938385
theorem B6611381 : Blo 1957435 6611381 := bbase (se 5 (by rfl) ⟨309908, by rfl⟩ : syracuseStep 6611381 = 619817) (by norm_num)
theorem B4407587 : Blo 1957435 4407587 := bstep (se 1 (by rfl) ⟨3305690, by rfl⟩ : syracuseStep 4407587 = 6611381) B6611381
theorem B2938391 : Blo 1957435 2938391 := bstep (se 1 (by rfl) ⟨2203793, by rfl⟩ : syracuseStep 2938391 = 4407587) B4407587
theorem B1958927 : Blo 1957435 1958927 := bstep (se 1 (by rfl) ⟨1469195, by rfl⟩ : syracuseStep 1958927 = 2938391) B2938391
theorem B2938397 : Blo 1957435 2938397 := bbase (se 3 (by rfl) ⟨550949, by rfl⟩ : syracuseStep 2938397 = 1101899) (by norm_num)
theorem B1958931 : Blo 1957435 1958931 := bstep (se 1 (by rfl) ⟨1469198, by rfl⟩ : syracuseStep 1958931 = 2938397) B2938397
theorem B4407605 : Blo 1957435 4407605 := bbase (se 5 (by rfl) ⟨206606, by rfl⟩ : syracuseStep 4407605 = 413213) (by norm_num)
theorem B2938403 : Blo 1957435 2938403 := bstep (se 1 (by rfl) ⟨2203802, by rfl⟩ : syracuseStep 2938403 = 4407605) B4407605
theorem B1958935 : Blo 1957435 1958935 := bstep (se 1 (by rfl) ⟨1469201, by rfl⟩ : syracuseStep 1958935 = 2938403) B2938403
theorem B3350813 : Blo 1957435 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B35742005 : Blo 1957435 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B23828003 : Blo 1957435 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B15885335 : Blo 1957435 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B42360893 : Blo 1957435 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B28240595 : Blo 1957435 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B18827063 : Blo 1957435 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B12551375 : Blo 1957435 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B8367583 : Blo 1957435 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B11156777 : Blo 1957435 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B7437851 : Blo 1957435 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B4958567 : Blo 1957435 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B3305711 : Blo 1957435 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B2203807 : Blo 1957435 2203807 := bstep (se 1 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 2203807 = 3305711) B3305711
theorem B2938409 : Blo 1957435 2938409 := bstep (se 2 (by rfl) ⟨1101903, by rfl⟩ : syracuseStep 2938409 = 2203807) B2203807
theorem B1958939 : Blo 1957435 1958939 := bstep (se 1 (by rfl) ⟨1469204, by rfl⟩ : syracuseStep 1958939 = 2938409) B2938409
theorem B5367365 : Blo 1957435 5367365 := bbase (se 4 (by rfl) ⟨503190, by rfl⟩ : syracuseStep 5367365 = 1006381) (by norm_num)
theorem B229007573 : Blo 1957435 229007573 := bstep (se 7 (by rfl) ⟨2683682, by rfl⟩ : syracuseStep 229007573 = 5367365) B5367365
theorem B152671715 : Blo 1957435 152671715 := bstep (se 1 (by rfl) ⟨114503786, by rfl⟩ : syracuseStep 152671715 = 229007573) B229007573
theorem B101781143 : Blo 1957435 101781143 := bstep (se 1 (by rfl) ⟨76335857, by rfl⟩ : syracuseStep 101781143 = 152671715) B152671715
theorem B67854095 : Blo 1957435 67854095 := bstep (se 1 (by rfl) ⟨50890571, by rfl⟩ : syracuseStep 67854095 = 101781143) B101781143
theorem B45236063 : Blo 1957435 45236063 := bstep (se 1 (by rfl) ⟨33927047, by rfl⟩ : syracuseStep 45236063 = 67854095) B67854095
theorem B30157375 : Blo 1957435 30157375 := bstep (se 1 (by rfl) ⟨22618031, by rfl⟩ : syracuseStep 30157375 = 45236063) B45236063
theorem B40209833 : Blo 1957435 40209833 := bstep (se 2 (by rfl) ⟨15078687, by rfl⟩ : syracuseStep 40209833 = 30157375) B30157375
theorem B26806555 : Blo 1957435 26806555 := bstep (se 1 (by rfl) ⟨20104916, by rfl⟩ : syracuseStep 26806555 = 40209833) B40209833
theorem B35742073 : Blo 1957435 35742073 := bstep (se 2 (by rfl) ⟨13403277, by rfl⟩ : syracuseStep 35742073 = 26806555) B26806555
theorem B47656097 : Blo 1957435 47656097 := bstep (se 2 (by rfl) ⟨17871036, by rfl⟩ : syracuseStep 47656097 = 35742073) B35742073
theorem B31770731 : Blo 1957435 31770731 := bstep (se 1 (by rfl) ⟨23828048, by rfl⟩ : syracuseStep 31770731 = 47656097) B47656097
theorem B21180487 : Blo 1957435 21180487 := bstep (se 1 (by rfl) ⟨15885365, by rfl⟩ : syracuseStep 21180487 = 31770731) B31770731
theorem B28240649 : Blo 1957435 28240649 := bstep (se 2 (by rfl) ⟨10590243, by rfl⟩ : syracuseStep 28240649 = 21180487) B21180487
theorem B18827099 : Blo 1957435 18827099 := bstep (se 1 (by rfl) ⟨14120324, by rfl⟩ : syracuseStep 18827099 = 28240649) B28240649
theorem B12551399 : Blo 1957435 12551399 := bstep (se 1 (by rfl) ⟨9413549, by rfl⟩ : syracuseStep 12551399 = 18827099) B18827099
theorem B8367599 : Blo 1957435 8367599 := bstep (se 1 (by rfl) ⟨6275699, by rfl⟩ : syracuseStep 8367599 = 12551399) B12551399
theorem B5578399 : Blo 1957435 5578399 := bstep (se 1 (by rfl) ⟨4183799, by rfl⟩ : syracuseStep 5578399 = 8367599) B8367599
theorem B7437865 : Blo 1957435 7437865 := bstep (se 2 (by rfl) ⟨2789199, by rfl⟩ : syracuseStep 7437865 = 5578399) B5578399
theorem B9917153 : Blo 1957435 9917153 := bstep (se 2 (by rfl) ⟨3718932, by rfl⟩ : syracuseStep 9917153 = 7437865) B7437865
theorem B6611435 : Blo 1957435 6611435 := bstep (se 1 (by rfl) ⟨4958576, by rfl⟩ : syracuseStep 6611435 = 9917153) B9917153
theorem B4407623 : Blo 1957435 4407623 := bstep (se 1 (by rfl) ⟨3305717, by rfl⟩ : syracuseStep 4407623 = 6611435) B6611435
theorem B2938415 : Blo 1957435 2938415 := bstep (se 1 (by rfl) ⟨2203811, by rfl⟩ : syracuseStep 2938415 = 4407623) B4407623
theorem B1958943 : Blo 1957435 1958943 := bstep (se 1 (by rfl) ⟨1469207, by rfl⟩ : syracuseStep 1958943 = 2938415) B2938415
theorem B2938421 : Blo 1957435 2938421 := bbase (se 5 (by rfl) ⟨137738, by rfl⟩ : syracuseStep 2938421 = 275477) (by norm_num)
theorem B1958947 : Blo 1957435 1958947 := bstep (se 1 (by rfl) ⟨1469210, by rfl⟩ : syracuseStep 1958947 = 2938421) B2938421
theorem B4958597 : Blo 1957435 4958597 := bbase (se 4 (by rfl) ⟨464868, by rfl⟩ : syracuseStep 4958597 = 929737) (by norm_num)
theorem B3305731 : Blo 1957435 3305731 := bstep (se 1 (by rfl) ⟨2479298, by rfl⟩ : syracuseStep 3305731 = 4958597) B4958597
theorem B4407641 : Blo 1957435 4407641 := bstep (se 2 (by rfl) ⟨1652865, by rfl⟩ : syracuseStep 4407641 = 3305731) B3305731
theorem B2938427 : Blo 1957435 2938427 := bstep (se 1 (by rfl) ⟨2203820, by rfl⟩ : syracuseStep 2938427 = 4407641) B4407641
theorem B1958951 : Blo 1957435 1958951 := bstep (se 1 (by rfl) ⟨1469213, by rfl⟩ : syracuseStep 1958951 = 2938427) B2938427
theorem B2203825 : Blo 1957435 2203825 := bbase (se 2 (by rfl) ⟨826434, by rfl⟩ : syracuseStep 2203825 = 1652869) (by norm_num)
theorem B2938433 : Blo 1957435 2938433 := bstep (se 2 (by rfl) ⟨1101912, by rfl⟩ : syracuseStep 2938433 = 2203825) B2203825
theorem B1958955 : Blo 1957435 1958955 := bstep (se 1 (by rfl) ⟨1469216, by rfl⟩ : syracuseStep 1958955 = 2938433) B2938433
theorem B2091917 : Blo 1957435 2091917 := bbase (se 3 (by rfl) ⟨392234, by rfl⟩ : syracuseStep 2091917 = 784469) (by norm_num)
theorem B5578445 : Blo 1957435 5578445 := bstep (se 3 (by rfl) ⟨1045958, by rfl⟩ : syracuseStep 5578445 = 2091917) B2091917
theorem B3718963 : Blo 1957435 3718963 := bstep (se 1 (by rfl) ⟨2789222, by rfl⟩ : syracuseStep 3718963 = 5578445) B5578445
theorem B4958617 : Blo 1957435 4958617 := bstep (se 2 (by rfl) ⟨1859481, by rfl⟩ : syracuseStep 4958617 = 3718963) B3718963
theorem B6611489 : Blo 1957435 6611489 := bstep (se 2 (by rfl) ⟨2479308, by rfl⟩ : syracuseStep 6611489 = 4958617) B4958617
theorem B4407659 : Blo 1957435 4407659 := bstep (se 1 (by rfl) ⟨3305744, by rfl⟩ : syracuseStep 4407659 = 6611489) B6611489
theorem B2938439 : Blo 1957435 2938439 := bstep (se 1 (by rfl) ⟨2203829, by rfl⟩ : syracuseStep 2938439 = 4407659) B4407659
theorem B1958959 : Blo 1957435 1958959 := bstep (se 1 (by rfl) ⟨1469219, by rfl⟩ : syracuseStep 1958959 = 2938439) B2938439
theorem B2938445 : Blo 1957435 2938445 := bbase (se 3 (by rfl) ⟨550958, by rfl⟩ : syracuseStep 2938445 = 1101917) (by norm_num)
theorem B1958963 : Blo 1957435 1958963 := bstep (se 1 (by rfl) ⟨1469222, by rfl⟩ : syracuseStep 1958963 = 2938445) B2938445
theorem B4407677 : Blo 1957435 4407677 := bbase (se 3 (by rfl) ⟨826439, by rfl⟩ : syracuseStep 4407677 = 1652879) (by norm_num)
theorem B2938451 : Blo 1957435 2938451 := bstep (se 1 (by rfl) ⟨2203838, by rfl⟩ : syracuseStep 2938451 = 4407677) B4407677
theorem B1958967 : Blo 1957435 1958967 := bstep (se 1 (by rfl) ⟨1469225, by rfl⟩ : syracuseStep 1958967 = 2938451) B2938451
theorem B3305765 : Blo 1957435 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B2203843 : Blo 1957435 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B2938457 : Blo 1957435 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B1958971 : Blo 1957435 1958971 := bstep (se 1 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 1958971 = 2938457) B2938457
theorem B2789245 : Blo 1957435 2789245 := bbase (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) (by norm_num)
theorem B14875973 : Blo 1957435 14875973 := bstep (se 4 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 14875973 = 2789245) B2789245
theorem B9917315 : Blo 1957435 9917315 := bstep (se 1 (by rfl) ⟨7437986, by rfl⟩ : syracuseStep 9917315 = 14875973) B14875973
theorem B6611543 : Blo 1957435 6611543 := bstep (se 1 (by rfl) ⟨4958657, by rfl⟩ : syracuseStep 6611543 = 9917315) B9917315
theorem B4407695 : Blo 1957435 4407695 := bstep (se 1 (by rfl) ⟨3305771, by rfl⟩ : syracuseStep 4407695 = 6611543) B6611543
theorem B2938463 : Blo 1957435 2938463 := bstep (se 1 (by rfl) ⟨2203847, by rfl⟩ : syracuseStep 2938463 = 4407695) B4407695
theorem B1958975 : Blo 1957435 1958975 := bstep (se 1 (by rfl) ⟨1469231, by rfl⟩ : syracuseStep 1958975 = 2938463) B2938463
theorem B2938469 : Blo 1957435 2938469 := bbase (se 4 (by rfl) ⟨275481, by rfl⟩ : syracuseStep 2938469 = 550963) (by norm_num)
theorem B1958979 : Blo 1957435 1958979 := bstep (se 1 (by rfl) ⟨1469234, by rfl⟩ : syracuseStep 1958979 = 2938469) B2938469
theorem B4240973 : Blo 1957435 4240973 := bbase (se 3 (by rfl) ⟨795182, by rfl⟩ : syracuseStep 4240973 = 1590365) (by norm_num)
theorem B2827315 : Blo 1957435 2827315 := bstep (se 1 (by rfl) ⟨2120486, by rfl⟩ : syracuseStep 2827315 = 4240973) B4240973
theorem B3769753 : Blo 1957435 3769753 := bstep (se 2 (by rfl) ⟨1413657, by rfl⟩ : syracuseStep 3769753 = 2827315) B2827315
theorem B5026337 : Blo 1957435 5026337 := bstep (se 2 (by rfl) ⟨1884876, by rfl⟩ : syracuseStep 5026337 = 3769753) B3769753
theorem B3350891 : Blo 1957435 3350891 := bstep (se 1 (by rfl) ⟨2513168, by rfl⟩ : syracuseStep 3350891 = 5026337) B5026337
theorem B2233927 : Blo 1957435 2233927 := bstep (se 1 (by rfl) ⟨1675445, by rfl⟩ : syracuseStep 2233927 = 3350891) B3350891
theorem B2978569 : Blo 1957435 2978569 := bstep (se 2 (by rfl) ⟨1116963, by rfl⟩ : syracuseStep 2978569 = 2233927) B2233927
theorem B3971425 : Blo 1957435 3971425 := bstep (se 2 (by rfl) ⟨1489284, by rfl⟩ : syracuseStep 3971425 = 2978569) B2978569
theorem B5295233 : Blo 1957435 5295233 := bstep (se 2 (by rfl) ⟨1985712, by rfl⟩ : syracuseStep 5295233 = 3971425) B3971425
theorem B3530155 : Blo 1957435 3530155 := bstep (se 1 (by rfl) ⟨2647616, by rfl⟩ : syracuseStep 3530155 = 5295233) B5295233
theorem B4706873 : Blo 1957435 4706873 := bstep (se 2 (by rfl) ⟨1765077, by rfl⟩ : syracuseStep 4706873 = 3530155) B3530155
theorem B3137915 : Blo 1957435 3137915 := bstep (se 1 (by rfl) ⟨2353436, by rfl⟩ : syracuseStep 3137915 = 4706873) B4706873
theorem B2091943 : Blo 1957435 2091943 := bstep (se 1 (by rfl) ⟨1568957, by rfl⟩ : syracuseStep 2091943 = 3137915) B3137915
theorem B2789257 : Blo 1957435 2789257 := bstep (se 2 (by rfl) ⟨1045971, by rfl⟩ : syracuseStep 2789257 = 2091943) B2091943
theorem B3719009 : Blo 1957435 3719009 := bstep (se 2 (by rfl) ⟨1394628, by rfl⟩ : syracuseStep 3719009 = 2789257) B2789257
theorem B2479339 : Blo 1957435 2479339 := bstep (se 1 (by rfl) ⟨1859504, by rfl⟩ : syracuseStep 2479339 = 3719009) B3719009
theorem B3305785 : Blo 1957435 3305785 := bstep (se 2 (by rfl) ⟨1239669, by rfl⟩ : syracuseStep 3305785 = 2479339) B2479339
theorem B4407713 : Blo 1957435 4407713 := bstep (se 2 (by rfl) ⟨1652892, by rfl⟩ : syracuseStep 4407713 = 3305785) B3305785
theorem B2938475 : Blo 1957435 2938475 := bstep (se 1 (by rfl) ⟨2203856, by rfl⟩ : syracuseStep 2938475 = 4407713) B4407713
theorem B1958983 : Blo 1957435 1958983 := bstep (se 1 (by rfl) ⟨1469237, by rfl⟩ : syracuseStep 1958983 = 2938475) B2938475
theorem B2203861 : Blo 1957435 2203861 := bbase (se 7 (by rfl) ⟨25826, by rfl⟩ : syracuseStep 2203861 = 51653) (by norm_num)
theorem B2938481 : Blo 1957435 2938481 := bstep (se 2 (by rfl) ⟨1101930, by rfl⟩ : syracuseStep 2938481 = 2203861) B2203861
theorem B1958987 : Blo 1957435 1958987 := bstep (se 1 (by rfl) ⟨1469240, by rfl⟩ : syracuseStep 1958987 = 2938481) B2938481
theorem B2479349 : Blo 1957435 2479349 := bbase (se 5 (by rfl) ⟨116219, by rfl⟩ : syracuseStep 2479349 = 232439) (by norm_num)
theorem B6611597 : Blo 1957435 6611597 := bstep (se 3 (by rfl) ⟨1239674, by rfl⟩ : syracuseStep 6611597 = 2479349) B2479349
theorem B4407731 : Blo 1957435 4407731 := bstep (se 1 (by rfl) ⟨3305798, by rfl⟩ : syracuseStep 4407731 = 6611597) B6611597
theorem B2938487 : Blo 1957435 2938487 := bstep (se 1 (by rfl) ⟨2203865, by rfl⟩ : syracuseStep 2938487 = 4407731) B4407731
theorem B1958991 : Blo 1957435 1958991 := bstep (se 1 (by rfl) ⟨1469243, by rfl⟩ : syracuseStep 1958991 = 2938487) B2938487
theorem B2938493 : Blo 1957435 2938493 := bbase (se 3 (by rfl) ⟨550967, by rfl⟩ : syracuseStep 2938493 = 1101935) (by norm_num)
theorem B1958995 : Blo 1957435 1958995 := bstep (se 1 (by rfl) ⟨1469246, by rfl⟩ : syracuseStep 1958995 = 2938493) B2938493
theorem B4407749 : Blo 1957435 4407749 := bbase (se 4 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 4407749 = 826453) (by norm_num)
theorem B2938499 : Blo 1957435 2938499 := bstep (se 1 (by rfl) ⟨2203874, by rfl⟩ : syracuseStep 2938499 = 4407749) B4407749
theorem B1958999 : Blo 1957435 1958999 := bstep (se 1 (by rfl) ⟨1469249, by rfl⟩ : syracuseStep 1958999 = 2938499) B2938499
theorem B6275893 : Blo 1957435 6275893 := bbase (se 5 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 6275893 = 588365) (by norm_num)
theorem B8367857 : Blo 1957435 8367857 := bstep (se 2 (by rfl) ⟨3137946, by rfl⟩ : syracuseStep 8367857 = 6275893) B6275893
theorem B5578571 : Blo 1957435 5578571 := bstep (se 1 (by rfl) ⟨4183928, by rfl⟩ : syracuseStep 5578571 = 8367857) B8367857
theorem B3719047 : Blo 1957435 3719047 := bstep (se 1 (by rfl) ⟨2789285, by rfl⟩ : syracuseStep 3719047 = 5578571) B5578571
theorem B4958729 : Blo 1957435 4958729 := bstep (se 2 (by rfl) ⟨1859523, by rfl⟩ : syracuseStep 4958729 = 3719047) B3719047
theorem B3305819 : Blo 1957435 3305819 := bstep (se 1 (by rfl) ⟨2479364, by rfl⟩ : syracuseStep 3305819 = 4958729) B4958729
theorem B2203879 : Blo 1957435 2203879 := bstep (se 1 (by rfl) ⟨1652909, by rfl⟩ : syracuseStep 2203879 = 3305819) B3305819
theorem B2938505 : Blo 1957435 2938505 := bstep (se 2 (by rfl) ⟨1101939, by rfl⟩ : syracuseStep 2938505 = 2203879) B2203879
theorem B1959003 : Blo 1957435 1959003 := bstep (se 1 (by rfl) ⟨1469252, by rfl⟩ : syracuseStep 1959003 = 2938505) B2938505
theorem B9917477 : Blo 1957435 9917477 := bbase (se 4 (by rfl) ⟨929763, by rfl⟩ : syracuseStep 9917477 = 1859527) (by norm_num)
theorem B6611651 : Blo 1957435 6611651 := bstep (se 1 (by rfl) ⟨4958738, by rfl⟩ : syracuseStep 6611651 = 9917477) B9917477
theorem B4407767 : Blo 1957435 4407767 := bstep (se 1 (by rfl) ⟨3305825, by rfl⟩ : syracuseStep 4407767 = 6611651) B6611651
theorem B2938511 : Blo 1957435 2938511 := bstep (se 1 (by rfl) ⟨2203883, by rfl⟩ : syracuseStep 2938511 = 4407767) B4407767
theorem B1959007 : Blo 1957435 1959007 := bstep (se 1 (by rfl) ⟨1469255, by rfl⟩ : syracuseStep 1959007 = 2938511) B2938511
theorem B2938517 : Blo 1957435 2938517 := bbase (se 6 (by rfl) ⟨68871, by rfl⟩ : syracuseStep 2938517 = 137743) (by norm_num)
theorem B1959011 : Blo 1957435 1959011 := bstep (se 1 (by rfl) ⟨1469258, by rfl⟩ : syracuseStep 1959011 = 2938517) B2938517
theorem B12551861 : Blo 1957435 12551861 := bbase (se 5 (by rfl) ⟨588368, by rfl⟩ : syracuseStep 12551861 = 1176737) (by norm_num)
theorem B8367907 : Blo 1957435 8367907 := bstep (se 1 (by rfl) ⟨6275930, by rfl⟩ : syracuseStep 8367907 = 12551861) B12551861
theorem B11157209 : Blo 1957435 11157209 := bstep (se 2 (by rfl) ⟨4183953, by rfl⟩ : syracuseStep 11157209 = 8367907) B8367907
theorem B7438139 : Blo 1957435 7438139 := bstep (se 1 (by rfl) ⟨5578604, by rfl⟩ : syracuseStep 7438139 = 11157209) B11157209
theorem B4958759 : Blo 1957435 4958759 := bstep (se 1 (by rfl) ⟨3719069, by rfl⟩ : syracuseStep 4958759 = 7438139) B7438139
theorem B3305839 : Blo 1957435 3305839 := bstep (se 1 (by rfl) ⟨2479379, by rfl⟩ : syracuseStep 3305839 = 4958759) B4958759
theorem B4407785 : Blo 1957435 4407785 := bstep (se 2 (by rfl) ⟨1652919, by rfl⟩ : syracuseStep 4407785 = 3305839) B3305839
theorem B2938523 : Blo 1957435 2938523 := bstep (se 1 (by rfl) ⟨2203892, by rfl⟩ : syracuseStep 2938523 = 4407785) B4407785
theorem B1959015 : Blo 1957435 1959015 := bstep (se 1 (by rfl) ⟨1469261, by rfl⟩ : syracuseStep 1959015 = 2938523) B2938523
theorem B2203897 : Blo 1957435 2203897 := bbase (se 2 (by rfl) ⟨826461, by rfl⟩ : syracuseStep 2203897 = 1652923) (by norm_num)
theorem B2938529 : Blo 1957435 2938529 := bstep (se 2 (by rfl) ⟨1101948, by rfl⟩ : syracuseStep 2938529 = 2203897) B2203897
theorem B1959019 : Blo 1957435 1959019 := bstep (se 1 (by rfl) ⟨1469264, by rfl⟩ : syracuseStep 1959019 = 2938529) B2938529
theorem B8367941 : Blo 1957435 8367941 := bbase (se 4 (by rfl) ⟨784494, by rfl⟩ : syracuseStep 8367941 = 1568989) (by norm_num)
theorem B5578627 : Blo 1957435 5578627 := bstep (se 1 (by rfl) ⟨4183970, by rfl⟩ : syracuseStep 5578627 = 8367941) B8367941
theorem B7438169 : Blo 1957435 7438169 := bstep (se 2 (by rfl) ⟨2789313, by rfl⟩ : syracuseStep 7438169 = 5578627) B5578627
theorem B4958779 : Blo 1957435 4958779 := bstep (se 1 (by rfl) ⟨3719084, by rfl⟩ : syracuseStep 4958779 = 7438169) B7438169
theorem B6611705 : Blo 1957435 6611705 := bstep (se 2 (by rfl) ⟨2479389, by rfl⟩ : syracuseStep 6611705 = 4958779) B4958779
theorem B4407803 : Blo 1957435 4407803 := bstep (se 1 (by rfl) ⟨3305852, by rfl⟩ : syracuseStep 4407803 = 6611705) B6611705
theorem B2938535 : Blo 1957435 2938535 := bstep (se 1 (by rfl) ⟨2203901, by rfl⟩ : syracuseStep 2938535 = 4407803) B4407803
theorem B1959023 : Blo 1957435 1959023 := bstep (se 1 (by rfl) ⟨1469267, by rfl⟩ : syracuseStep 1959023 = 2938535) B2938535
theorem B2938541 : Blo 1957435 2938541 := bbase (se 3 (by rfl) ⟨550976, by rfl⟩ : syracuseStep 2938541 = 1101953) (by norm_num)
theorem B1959027 : Blo 1957435 1959027 := bstep (se 1 (by rfl) ⟨1469270, by rfl⟩ : syracuseStep 1959027 = 2938541) B2938541
theorem B4407821 : Blo 1957435 4407821 := bbase (se 3 (by rfl) ⟨826466, by rfl⟩ : syracuseStep 4407821 = 1652933) (by norm_num)
theorem B2938547 : Blo 1957435 2938547 := bstep (se 1 (by rfl) ⟨2203910, by rfl⟩ : syracuseStep 2938547 = 4407821) B4407821
theorem B1959031 : Blo 1957435 1959031 := bstep (se 1 (by rfl) ⟨1469273, by rfl⟩ : syracuseStep 1959031 = 2938547) B2938547
theorem B2479405 : Blo 1957435 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B3305873 : Blo 1957435 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B2203915 : Blo 1957435 2203915 := bstep (se 1 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 2203915 = 3305873) B3305873
theorem B2938553 : Blo 1957435 2938553 := bstep (se 2 (by rfl) ⟨1101957, by rfl⟩ : syracuseStep 2938553 = 2203915) B2203915
theorem B1959035 : Blo 1957435 1959035 := bstep (se 1 (by rfl) ⟨1469276, by rfl⟩ : syracuseStep 1959035 = 2938553) B2938553
theorem B4707005 : Blo 1957435 4707005 := bbase (se 3 (by rfl) ⟨882563, by rfl⟩ : syracuseStep 4707005 = 1765127) (by norm_num)
theorem B12552013 : Blo 1957435 12552013 := bstep (se 3 (by rfl) ⟨2353502, by rfl⟩ : syracuseStep 12552013 = 4707005) B4707005
theorem B16736017 : Blo 1957435 16736017 := bstep (se 2 (by rfl) ⟨6276006, by rfl⟩ : syracuseStep 16736017 = 12552013) B12552013
theorem B22314689 : Blo 1957435 22314689 := bstep (se 2 (by rfl) ⟨8368008, by rfl⟩ : syracuseStep 22314689 = 16736017) B16736017
theorem B14876459 : Blo 1957435 14876459 := bstep (se 1 (by rfl) ⟨11157344, by rfl⟩ : syracuseStep 14876459 = 22314689) B22314689
theorem B9917639 : Blo 1957435 9917639 := bstep (se 1 (by rfl) ⟨7438229, by rfl⟩ : syracuseStep 9917639 = 14876459) B14876459
theorem B6611759 : Blo 1957435 6611759 := bstep (se 1 (by rfl) ⟨4958819, by rfl⟩ : syracuseStep 6611759 = 9917639) B9917639
theorem B4407839 : Blo 1957435 4407839 := bstep (se 1 (by rfl) ⟨3305879, by rfl⟩ : syracuseStep 4407839 = 6611759) B6611759
theorem B2938559 : Blo 1957435 2938559 := bstep (se 1 (by rfl) ⟨2203919, by rfl⟩ : syracuseStep 2938559 = 4407839) B4407839
theorem B1959039 : Blo 1957435 1959039 := bstep (se 1 (by rfl) ⟨1469279, by rfl⟩ : syracuseStep 1959039 = 2938559) B2938559
theorem B2938565 : Blo 1957435 2938565 := bbase (se 4 (by rfl) ⟨275490, by rfl⟩ : syracuseStep 2938565 = 550981) (by norm_num)
theorem B1959043 : Blo 1957435 1959043 := bstep (se 1 (by rfl) ⟨1469282, by rfl⟩ : syracuseStep 1959043 = 2938565) B2938565
theorem B3305893 : Blo 1957435 3305893 := bbase (se 4 (by rfl) ⟨309927, by rfl⟩ : syracuseStep 3305893 = 619855) (by norm_num)
theorem B4407857 : Blo 1957435 4407857 := bstep (se 2 (by rfl) ⟨1652946, by rfl⟩ : syracuseStep 4407857 = 3305893) B3305893
theorem B2938571 : Blo 1957435 2938571 := bstep (se 1 (by rfl) ⟨2203928, by rfl⟩ : syracuseStep 2938571 = 4407857) B4407857
theorem B1959047 : Blo 1957435 1959047 := bstep (se 1 (by rfl) ⟨1469285, by rfl⟩ : syracuseStep 1959047 = 2938571) B2938571
theorem B2203933 : Blo 1957435 2203933 := bbase (se 3 (by rfl) ⟨413237, by rfl⟩ : syracuseStep 2203933 = 826475) (by norm_num)
theorem B2938577 : Blo 1957435 2938577 := bstep (se 2 (by rfl) ⟨1101966, by rfl⟩ : syracuseStep 2938577 = 2203933) B2203933
theorem B1959051 : Blo 1957435 1959051 := bstep (se 1 (by rfl) ⟨1469288, by rfl⟩ : syracuseStep 1959051 = 2938577) B2938577
theorem B6611813 : Blo 1957435 6611813 := bbase (se 4 (by rfl) ⟨619857, by rfl⟩ : syracuseStep 6611813 = 1239715) (by norm_num)
theorem B4407875 : Blo 1957435 4407875 := bstep (se 1 (by rfl) ⟨3305906, by rfl⟩ : syracuseStep 4407875 = 6611813) B6611813
theorem B2938583 : Blo 1957435 2938583 := bstep (se 1 (by rfl) ⟨2203937, by rfl⟩ : syracuseStep 2938583 = 4407875) B4407875
theorem B1959055 : Blo 1957435 1959055 := bstep (se 1 (by rfl) ⟨1469291, by rfl⟩ : syracuseStep 1959055 = 2938583) B2938583
theorem B2938589 : Blo 1957435 2938589 := bbase (se 3 (by rfl) ⟨550985, by rfl⟩ : syracuseStep 2938589 = 1101971) (by norm_num)
theorem B1959059 : Blo 1957435 1959059 := bstep (se 1 (by rfl) ⟨1469294, by rfl⟩ : syracuseStep 1959059 = 2938589) B2938589
theorem B4407893 : Blo 1957435 4407893 := bbase (se 8 (by rfl) ⟨25827, by rfl⟩ : syracuseStep 4407893 = 51655) (by norm_num)
theorem B2938595 : Blo 1957435 2938595 := bstep (se 1 (by rfl) ⟨2203946, by rfl⟩ : syracuseStep 2938595 = 4407893) B4407893
theorem B1959063 : Blo 1957435 1959063 := bstep (se 1 (by rfl) ⟨1469297, by rfl⟩ : syracuseStep 1959063 = 2938595) B2938595
theorem B2353537 : Blo 1957435 2353537 := bbase (se 2 (by rfl) ⟨882576, by rfl⟩ : syracuseStep 2353537 = 1765153) (by norm_num)
theorem B3138049 : Blo 1957435 3138049 := bstep (se 2 (by rfl) ⟨1176768, by rfl⟩ : syracuseStep 3138049 = 2353537) B2353537
theorem B4184065 : Blo 1957435 4184065 := bstep (se 2 (by rfl) ⟨1569024, by rfl⟩ : syracuseStep 4184065 = 3138049) B3138049
theorem B5578753 : Blo 1957435 5578753 := bstep (se 2 (by rfl) ⟨2092032, by rfl⟩ : syracuseStep 5578753 = 4184065) B4184065
theorem B7438337 : Blo 1957435 7438337 := bstep (se 2 (by rfl) ⟨2789376, by rfl⟩ : syracuseStep 7438337 = 5578753) B5578753
theorem B4958891 : Blo 1957435 4958891 := bstep (se 1 (by rfl) ⟨3719168, by rfl⟩ : syracuseStep 4958891 = 7438337) B7438337
theorem B3305927 : Blo 1957435 3305927 := bstep (se 1 (by rfl) ⟨2479445, by rfl⟩ : syracuseStep 3305927 = 4958891) B4958891
theorem B2203951 : Blo 1957435 2203951 := bstep (se 1 (by rfl) ⟨1652963, by rfl⟩ : syracuseStep 2203951 = 3305927) B3305927
theorem B2938601 : Blo 1957435 2938601 := bstep (se 2 (by rfl) ⟨1101975, by rfl⟩ : syracuseStep 2938601 = 2203951) B2203951
theorem B1959067 : Blo 1957435 1959067 := bstep (se 1 (by rfl) ⟨1469300, by rfl⟩ : syracuseStep 1959067 = 2938601) B2938601
theorem B2353541 : Blo 1957435 2353541 := bbase (se 4 (by rfl) ⟨220644, by rfl⟩ : syracuseStep 2353541 = 441289) (by norm_num)
theorem B25104437 : Blo 1957435 25104437 := bstep (se 5 (by rfl) ⟨1176770, by rfl⟩ : syracuseStep 25104437 = 2353541) B2353541
theorem B16736291 : Blo 1957435 16736291 := bstep (se 1 (by rfl) ⟨12552218, by rfl⟩ : syracuseStep 16736291 = 25104437) B25104437
theorem B11157527 : Blo 1957435 11157527 := bstep (se 1 (by rfl) ⟨8368145, by rfl⟩ : syracuseStep 11157527 = 16736291) B16736291
theorem B7438351 : Blo 1957435 7438351 := bstep (se 1 (by rfl) ⟨5578763, by rfl⟩ : syracuseStep 7438351 = 11157527) B11157527
theorem B9917801 : Blo 1957435 9917801 := bstep (se 2 (by rfl) ⟨3719175, by rfl⟩ : syracuseStep 9917801 = 7438351) B7438351
theorem B6611867 : Blo 1957435 6611867 := bstep (se 1 (by rfl) ⟨4958900, by rfl⟩ : syracuseStep 6611867 = 9917801) B9917801
theorem B4407911 : Blo 1957435 4407911 := bstep (se 1 (by rfl) ⟨3305933, by rfl⟩ : syracuseStep 4407911 = 6611867) B6611867
theorem B2938607 : Blo 1957435 2938607 := bstep (se 1 (by rfl) ⟨2203955, by rfl⟩ : syracuseStep 2938607 = 4407911) B4407911
theorem B1959071 : Blo 1957435 1959071 := bstep (se 1 (by rfl) ⟨1469303, by rfl⟩ : syracuseStep 1959071 = 2938607) B2938607
theorem B2938613 : Blo 1957435 2938613 := bbase (se 5 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 2938613 = 275495) (by norm_num)
theorem B1959075 : Blo 1957435 1959075 := bstep (se 1 (by rfl) ⟨1469306, by rfl⟩ : syracuseStep 1959075 = 2938613) B2938613
theorem B8368181 : Blo 1957435 8368181 := bbase (se 5 (by rfl) ⟨392258, by rfl⟩ : syracuseStep 8368181 = 784517) (by norm_num)
theorem B5578787 : Blo 1957435 5578787 := bstep (se 1 (by rfl) ⟨4184090, by rfl⟩ : syracuseStep 5578787 = 8368181) B8368181
theorem B3719191 : Blo 1957435 3719191 := bstep (se 1 (by rfl) ⟨2789393, by rfl⟩ : syracuseStep 3719191 = 5578787) B5578787
theorem B4958921 : Blo 1957435 4958921 := bstep (se 2 (by rfl) ⟨1859595, by rfl⟩ : syracuseStep 4958921 = 3719191) B3719191
theorem B3305947 : Blo 1957435 3305947 := bstep (se 1 (by rfl) ⟨2479460, by rfl⟩ : syracuseStep 3305947 = 4958921) B4958921
theorem B4407929 : Blo 1957435 4407929 := bstep (se 2 (by rfl) ⟨1652973, by rfl⟩ : syracuseStep 4407929 = 3305947) B3305947
theorem B2938619 : Blo 1957435 2938619 := bstep (se 1 (by rfl) ⟨2203964, by rfl⟩ : syracuseStep 2938619 = 4407929) B4407929
theorem B1959079 : Blo 1957435 1959079 := bstep (se 1 (by rfl) ⟨1469309, by rfl⟩ : syracuseStep 1959079 = 2938619) B2938619
theorem B2203969 : Blo 1957435 2203969 := bbase (se 2 (by rfl) ⟨826488, by rfl⟩ : syracuseStep 2203969 = 1652977) (by norm_num)
theorem B2938625 : Blo 1957435 2938625 := bstep (se 2 (by rfl) ⟨1101984, by rfl⟩ : syracuseStep 2938625 = 2203969) B2203969
theorem B1959083 : Blo 1957435 1959083 := bstep (se 1 (by rfl) ⟨1469312, by rfl⟩ : syracuseStep 1959083 = 2938625) B2938625
theorem B4958941 : Blo 1957435 4958941 := bbase (se 3 (by rfl) ⟨929801, by rfl⟩ : syracuseStep 4958941 = 1859603) (by norm_num)
theorem B6611921 : Blo 1957435 6611921 := bstep (se 2 (by rfl) ⟨2479470, by rfl⟩ : syracuseStep 6611921 = 4958941) B4958941
theorem B4407947 : Blo 1957435 4407947 := bstep (se 1 (by rfl) ⟨3305960, by rfl⟩ : syracuseStep 4407947 = 6611921) B6611921
theorem B2938631 : Blo 1957435 2938631 := bstep (se 1 (by rfl) ⟨2203973, by rfl⟩ : syracuseStep 2938631 = 4407947) B4407947
theorem B1959087 : Blo 1957435 1959087 := bstep (se 1 (by rfl) ⟨1469315, by rfl⟩ : syracuseStep 1959087 = 2938631) B2938631
theorem B2938637 : Blo 1957435 2938637 := bbase (se 3 (by rfl) ⟨550994, by rfl⟩ : syracuseStep 2938637 = 1101989) (by norm_num)
theorem B1959091 : Blo 1957435 1959091 := bstep (se 1 (by rfl) ⟨1469318, by rfl⟩ : syracuseStep 1959091 = 2938637) B2938637
theorem B4407965 : Blo 1957435 4407965 := bbase (se 3 (by rfl) ⟨826493, by rfl⟩ : syracuseStep 4407965 = 1652987) (by norm_num)
theorem B2938643 : Blo 1957435 2938643 := bstep (se 1 (by rfl) ⟨2203982, by rfl⟩ : syracuseStep 2938643 = 4407965) B4407965
theorem B1959095 : Blo 1957435 1959095 := bstep (se 1 (by rfl) ⟨1469321, by rfl⟩ : syracuseStep 1959095 = 2938643) B2938643
theorem B3305981 : Blo 1957435 3305981 := bbase (se 3 (by rfl) ⟨619871, by rfl⟩ : syracuseStep 3305981 = 1239743) (by norm_num)
theorem B2203987 : Blo 1957435 2203987 := bstep (se 1 (by rfl) ⟨1652990, by rfl⟩ : syracuseStep 2203987 = 3305981) B3305981
theorem B2938649 : Blo 1957435 2938649 := bstep (se 2 (by rfl) ⟨1101993, by rfl⟩ : syracuseStep 2938649 = 2203987) B2203987
theorem B1959099 : Blo 1957435 1959099 := bstep (se 1 (by rfl) ⟨1469324, by rfl⟩ : syracuseStep 1959099 = 2938649) B2938649
theorem B4184141 : Blo 1957435 4184141 := bbase (se 3 (by rfl) ⟨784526, by rfl⟩ : syracuseStep 4184141 = 1569053) (by norm_num)
theorem B11157709 : Blo 1957435 11157709 := bstep (se 3 (by rfl) ⟨2092070, by rfl⟩ : syracuseStep 11157709 = 4184141) B4184141
theorem B14876945 : Blo 1957435 14876945 := bstep (se 2 (by rfl) ⟨5578854, by rfl⟩ : syracuseStep 14876945 = 11157709) B11157709
theorem B9917963 : Blo 1957435 9917963 := bstep (se 1 (by rfl) ⟨7438472, by rfl⟩ : syracuseStep 9917963 = 14876945) B14876945
theorem B6611975 : Blo 1957435 6611975 := bstep (se 1 (by rfl) ⟨4958981, by rfl⟩ : syracuseStep 6611975 = 9917963) B9917963
theorem B4407983 : Blo 1957435 4407983 := bstep (se 1 (by rfl) ⟨3305987, by rfl⟩ : syracuseStep 4407983 = 6611975) B6611975
theorem B2938655 : Blo 1957435 2938655 := bstep (se 1 (by rfl) ⟨2203991, by rfl⟩ : syracuseStep 2938655 = 4407983) B4407983
theorem B1959103 : Blo 1957435 1959103 := bstep (se 1 (by rfl) ⟨1469327, by rfl⟩ : syracuseStep 1959103 = 2938655) B2938655
theorem B2938661 : Blo 1957435 2938661 := bbase (se 4 (by rfl) ⟨275499, by rfl⟩ : syracuseStep 2938661 = 550999) (by norm_num)
theorem B1959107 : Blo 1957435 1959107 := bstep (se 1 (by rfl) ⟨1469330, by rfl⟩ : syracuseStep 1959107 = 2938661) B2938661
theorem B2479501 : Blo 1957435 2479501 := bbase (se 3 (by rfl) ⟨464906, by rfl⟩ : syracuseStep 2479501 = 929813) (by norm_num)
theorem B3306001 : Blo 1957435 3306001 := bstep (se 2 (by rfl) ⟨1239750, by rfl⟩ : syracuseStep 3306001 = 2479501) B2479501
theorem B4408001 : Blo 1957435 4408001 := bstep (se 2 (by rfl) ⟨1653000, by rfl⟩ : syracuseStep 4408001 = 3306001) B3306001
theorem B2938667 : Blo 1957435 2938667 := bstep (se 1 (by rfl) ⟨2204000, by rfl⟩ : syracuseStep 2938667 = 4408001) B4408001
theorem B1959111 : Blo 1957435 1959111 := bstep (se 1 (by rfl) ⟨1469333, by rfl⟩ : syracuseStep 1959111 = 2938667) B2938667
theorem B2204005 : Blo 1957435 2204005 := bbase (se 4 (by rfl) ⟨206625, by rfl⟩ : syracuseStep 2204005 = 413251) (by norm_num)
theorem B2938673 : Blo 1957435 2938673 := bstep (se 2 (by rfl) ⟨1102002, by rfl⟩ : syracuseStep 2938673 = 2204005) B2204005
theorem B1959115 : Blo 1957435 1959115 := bstep (se 1 (by rfl) ⟨1469336, by rfl⟩ : syracuseStep 1959115 = 2938673) B2938673
theorem B5578901 : Blo 1957435 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B3719267 : Blo 1957435 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B2479511 : Blo 1957435 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B6612029 : Blo 1957435 6612029 := bstep (se 3 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 6612029 = 2479511) B2479511
theorem B4408019 : Blo 1957435 4408019 := bstep (se 1 (by rfl) ⟨3306014, by rfl⟩ : syracuseStep 4408019 = 6612029) B6612029
theorem B2938679 : Blo 1957435 2938679 := bstep (se 1 (by rfl) ⟨2204009, by rfl⟩ : syracuseStep 2938679 = 4408019) B4408019
theorem B1959119 : Blo 1957435 1959119 := bstep (se 1 (by rfl) ⟨1469339, by rfl⟩ : syracuseStep 1959119 = 2938679) B2938679
theorem B2938685 : Blo 1957435 2938685 := bbase (se 3 (by rfl) ⟨551003, by rfl⟩ : syracuseStep 2938685 = 1102007) (by norm_num)
theorem B1959123 : Blo 1957435 1959123 := bstep (se 1 (by rfl) ⟨1469342, by rfl⟩ : syracuseStep 1959123 = 2938685) B2938685
theorem B4408037 : Blo 1957435 4408037 := bbase (se 4 (by rfl) ⟨413253, by rfl⟩ : syracuseStep 4408037 = 826507) (by norm_num)
theorem B2938691 : Blo 1957435 2938691 := bstep (se 1 (by rfl) ⟨2204018, by rfl⟩ : syracuseStep 2938691 = 4408037) B4408037
theorem B1959127 : Blo 1957435 1959127 := bstep (se 1 (by rfl) ⟨1469345, by rfl⟩ : syracuseStep 1959127 = 2938691) B2938691
theorem B4959053 : Blo 1957435 4959053 := bbase (se 3 (by rfl) ⟨929822, by rfl⟩ : syracuseStep 4959053 = 1859645) (by norm_num)
theorem B3306035 : Blo 1957435 3306035 := bstep (se 1 (by rfl) ⟨2479526, by rfl⟩ : syracuseStep 3306035 = 4959053) B4959053
theorem B2204023 : Blo 1957435 2204023 := bstep (se 1 (by rfl) ⟨1653017, by rfl⟩ : syracuseStep 2204023 = 3306035) B3306035
theorem B2938697 : Blo 1957435 2938697 := bstep (se 2 (by rfl) ⟨1102011, by rfl⟩ : syracuseStep 2938697 = 2204023) B2204023
theorem B1959131 : Blo 1957435 1959131 := bstep (se 1 (by rfl) ⟨1469348, by rfl⟩ : syracuseStep 1959131 = 2938697) B2938697
theorem B2092105 : Blo 1957435 2092105 := bbase (se 2 (by rfl) ⟨784539, by rfl⟩ : syracuseStep 2092105 = 1569079) (by norm_num)
theorem B2789473 : Blo 1957435 2789473 := bstep (se 2 (by rfl) ⟨1046052, by rfl⟩ : syracuseStep 2789473 = 2092105) B2092105
theorem B3719297 : Blo 1957435 3719297 := bstep (se 2 (by rfl) ⟨1394736, by rfl⟩ : syracuseStep 3719297 = 2789473) B2789473
theorem B9918125 : Blo 1957435 9918125 := bstep (se 3 (by rfl) ⟨1859648, by rfl⟩ : syracuseStep 9918125 = 3719297) B3719297
theorem B6612083 : Blo 1957435 6612083 := bstep (se 1 (by rfl) ⟨4959062, by rfl⟩ : syracuseStep 6612083 = 9918125) B9918125
theorem B4408055 : Blo 1957435 4408055 := bstep (se 1 (by rfl) ⟨3306041, by rfl⟩ : syracuseStep 4408055 = 6612083) B6612083
theorem B2938703 : Blo 1957435 2938703 := bstep (se 1 (by rfl) ⟨2204027, by rfl⟩ : syracuseStep 2938703 = 4408055) B4408055
theorem B1959135 : Blo 1957435 1959135 := bstep (se 1 (by rfl) ⟨1469351, by rfl⟩ : syracuseStep 1959135 = 2938703) B2938703
theorem B2938709 : Blo 1957435 2938709 := bbase (se 9 (by rfl) ⟨8609, by rfl⟩ : syracuseStep 2938709 = 17219) (by norm_num)
theorem B1959139 : Blo 1957435 1959139 := bstep (se 1 (by rfl) ⟨1469354, by rfl⟩ : syracuseStep 1959139 = 2938709) B2938709
theorem B6276341 : Blo 1957435 6276341 := bbase (se 5 (by rfl) ⟨294203, by rfl⟩ : syracuseStep 6276341 = 588407) (by norm_num)
theorem B4184227 : Blo 1957435 4184227 := bstep (se 1 (by rfl) ⟨3138170, by rfl⟩ : syracuseStep 4184227 = 6276341) B6276341
theorem B5578969 : Blo 1957435 5578969 := bstep (se 2 (by rfl) ⟨2092113, by rfl⟩ : syracuseStep 5578969 = 4184227) B4184227
theorem B7438625 : Blo 1957435 7438625 := bstep (se 2 (by rfl) ⟨2789484, by rfl⟩ : syracuseStep 7438625 = 5578969) B5578969
theorem B4959083 : Blo 1957435 4959083 := bstep (se 1 (by rfl) ⟨3719312, by rfl⟩ : syracuseStep 4959083 = 7438625) B7438625
theorem B3306055 : Blo 1957435 3306055 := bstep (se 1 (by rfl) ⟨2479541, by rfl⟩ : syracuseStep 3306055 = 4959083) B4959083
theorem B4408073 : Blo 1957435 4408073 := bstep (se 2 (by rfl) ⟨1653027, by rfl⟩ : syracuseStep 4408073 = 3306055) B3306055
theorem B2938715 : Blo 1957435 2938715 := bstep (se 1 (by rfl) ⟨2204036, by rfl⟩ : syracuseStep 2938715 = 4408073) B4408073
theorem B1959143 : Blo 1957435 1959143 := bstep (se 1 (by rfl) ⟨1469357, by rfl⟩ : syracuseStep 1959143 = 2938715) B2938715
theorem B2204041 : Blo 1957435 2204041 := bbase (se 2 (by rfl) ⟨826515, by rfl⟩ : syracuseStep 2204041 = 1653031) (by norm_num)
theorem B2938721 : Blo 1957435 2938721 := bstep (se 2 (by rfl) ⟨1102020, by rfl⟩ : syracuseStep 2938721 = 2204041) B2204041
theorem B1959147 : Blo 1957435 1959147 := bstep (se 1 (by rfl) ⟨1469360, by rfl⟩ : syracuseStep 1959147 = 2938721) B2938721
theorem B5655109 : Blo 1957435 5655109 := bbase (se 4 (by rfl) ⟨530166, by rfl⟩ : syracuseStep 5655109 = 1060333) (by norm_num)
theorem B7540145 : Blo 1957435 7540145 := bstep (se 2 (by rfl) ⟨2827554, by rfl⟩ : syracuseStep 7540145 = 5655109) B5655109
theorem B5026763 : Blo 1957435 5026763 := bstep (se 1 (by rfl) ⟨3770072, by rfl⟩ : syracuseStep 5026763 = 7540145) B7540145
theorem B3351175 : Blo 1957435 3351175 := bstep (se 1 (by rfl) ⟨2513381, by rfl⟩ : syracuseStep 3351175 = 5026763) B5026763
theorem B71491733 : Blo 1957435 71491733 := bstep (se 6 (by rfl) ⟨1675587, by rfl⟩ : syracuseStep 71491733 = 3351175) B3351175
theorem B47661155 : Blo 1957435 47661155 := bstep (se 1 (by rfl) ⟨35745866, by rfl⟩ : syracuseStep 47661155 = 71491733) B71491733
theorem B31774103 : Blo 1957435 31774103 := bstep (se 1 (by rfl) ⟨23830577, by rfl⟩ : syracuseStep 31774103 = 47661155) B47661155
theorem B21182735 : Blo 1957435 21182735 := bstep (se 1 (by rfl) ⟨15887051, by rfl⟩ : syracuseStep 21182735 = 31774103) B31774103
theorem B56487293 : Blo 1957435 56487293 := bstep (se 3 (by rfl) ⟨10591367, by rfl⟩ : syracuseStep 56487293 = 21182735) B21182735
theorem B37658195 : Blo 1957435 37658195 := bstep (se 1 (by rfl) ⟨28243646, by rfl⟩ : syracuseStep 37658195 = 56487293) B56487293
theorem B25105463 : Blo 1957435 25105463 := bstep (se 1 (by rfl) ⟨18829097, by rfl⟩ : syracuseStep 25105463 = 37658195) B37658195
theorem B16736975 : Blo 1957435 16736975 := bstep (se 1 (by rfl) ⟨12552731, by rfl⟩ : syracuseStep 16736975 = 25105463) B25105463
theorem B11157983 : Blo 1957435 11157983 := bstep (se 1 (by rfl) ⟨8368487, by rfl⟩ : syracuseStep 11157983 = 16736975) B16736975
theorem B7438655 : Blo 1957435 7438655 := bstep (se 1 (by rfl) ⟨5578991, by rfl⟩ : syracuseStep 7438655 = 11157983) B11157983
theorem B4959103 : Blo 1957435 4959103 := bstep (se 1 (by rfl) ⟨3719327, by rfl⟩ : syracuseStep 4959103 = 7438655) B7438655
theorem B6612137 : Blo 1957435 6612137 := bstep (se 2 (by rfl) ⟨2479551, by rfl⟩ : syracuseStep 6612137 = 4959103) B4959103
theorem B4408091 : Blo 1957435 4408091 := bstep (se 1 (by rfl) ⟨3306068, by rfl⟩ : syracuseStep 4408091 = 6612137) B6612137
theorem B2938727 : Blo 1957435 2938727 := bstep (se 1 (by rfl) ⟨2204045, by rfl⟩ : syracuseStep 2938727 = 4408091) B4408091
theorem B1959151 : Blo 1957435 1959151 := bstep (se 1 (by rfl) ⟨1469363, by rfl⟩ : syracuseStep 1959151 = 2938727) B2938727
theorem B2938733 : Blo 1957435 2938733 := bbase (se 3 (by rfl) ⟨551012, by rfl⟩ : syracuseStep 2938733 = 1102025) (by norm_num)
theorem B1959155 : Blo 1957435 1959155 := bstep (se 1 (by rfl) ⟨1469366, by rfl⟩ : syracuseStep 1959155 = 2938733) B2938733
theorem B4408109 : Blo 1957435 4408109 := bbase (se 3 (by rfl) ⟨826520, by rfl⟩ : syracuseStep 4408109 = 1653041) (by norm_num)
theorem B2938739 : Blo 1957435 2938739 := bstep (se 1 (by rfl) ⟨2204054, by rfl⟩ : syracuseStep 2938739 = 4408109) B4408109
theorem B1959159 : Blo 1957435 1959159 := bstep (se 1 (by rfl) ⟨1469369, by rfl⟩ : syracuseStep 1959159 = 2938739) B2938739
theorem B11310293 : Blo 1957435 11310293 := bbase (se 7 (by rfl) ⟨132542, by rfl⟩ : syracuseStep 11310293 = 265085) (by norm_num)
theorem B30160781 : Blo 1957435 30160781 := bstep (se 3 (by rfl) ⟨5655146, by rfl⟩ : syracuseStep 30160781 = 11310293) B11310293
theorem B20107187 : Blo 1957435 20107187 := bstep (se 1 (by rfl) ⟨15080390, by rfl⟩ : syracuseStep 20107187 = 30160781) B30160781
theorem B13404791 : Blo 1957435 13404791 := bstep (se 1 (by rfl) ⟨10053593, by rfl⟩ : syracuseStep 13404791 = 20107187) B20107187
theorem B8936527 : Blo 1957435 8936527 := bstep (se 1 (by rfl) ⟨6702395, by rfl⟩ : syracuseStep 8936527 = 13404791) B13404791
theorem B11915369 : Blo 1957435 11915369 := bstep (se 2 (by rfl) ⟨4468263, by rfl⟩ : syracuseStep 11915369 = 8936527) B8936527
theorem B7943579 : Blo 1957435 7943579 := bstep (se 1 (by rfl) ⟨5957684, by rfl⟩ : syracuseStep 7943579 = 11915369) B11915369
theorem B5295719 : Blo 1957435 5295719 := bstep (se 1 (by rfl) ⟨3971789, by rfl⟩ : syracuseStep 5295719 = 7943579) B7943579
theorem B3530479 : Blo 1957435 3530479 := bstep (se 1 (by rfl) ⟨2647859, by rfl⟩ : syracuseStep 3530479 = 5295719) B5295719
theorem B4707305 : Blo 1957435 4707305 := bstep (se 2 (by rfl) ⟨1765239, by rfl⟩ : syracuseStep 4707305 = 3530479) B3530479
theorem B3138203 : Blo 1957435 3138203 := bstep (se 1 (by rfl) ⟨2353652, by rfl⟩ : syracuseStep 3138203 = 4707305) B4707305
theorem B8368541 : Blo 1957435 8368541 := bstep (se 3 (by rfl) ⟨1569101, by rfl⟩ : syracuseStep 8368541 = 3138203) B3138203
theorem B5579027 : Blo 1957435 5579027 := bstep (se 1 (by rfl) ⟨4184270, by rfl⟩ : syracuseStep 5579027 = 8368541) B8368541
theorem B3719351 : Blo 1957435 3719351 := bstep (se 1 (by rfl) ⟨2789513, by rfl⟩ : syracuseStep 3719351 = 5579027) B5579027
theorem B2479567 : Blo 1957435 2479567 := bstep (se 1 (by rfl) ⟨1859675, by rfl⟩ : syracuseStep 2479567 = 3719351) B3719351
theorem B3306089 : Blo 1957435 3306089 := bstep (se 2 (by rfl) ⟨1239783, by rfl⟩ : syracuseStep 3306089 = 2479567) B2479567
theorem B2204059 : Blo 1957435 2204059 := bstep (se 1 (by rfl) ⟨1653044, by rfl⟩ : syracuseStep 2204059 = 3306089) B3306089
theorem B2938745 : Blo 1957435 2938745 := bstep (se 2 (by rfl) ⟨1102029, by rfl⟩ : syracuseStep 2938745 = 2204059) B2204059
theorem B1959163 : Blo 1957435 1959163 := bstep (se 1 (by rfl) ⟨1469372, by rfl⟩ : syracuseStep 1959163 = 2938745) B2938745
theorem B2385769 : Blo 1957435 2385769 := bbase (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) (by norm_num)
theorem B3181025 : Blo 1957435 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B8482733 : Blo 1957435 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B5655155 : Blo 1957435 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B15080413 : Blo 1957435 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B20107217 : Blo 1957435 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B13404811 : Blo 1957435 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B17873081 : Blo 1957435 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B11915387 : Blo 1957435 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B7943591 : Blo 1957435 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B5295727 : Blo 1957435 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B7060969 : Blo 1957435 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B9414625 : Blo 1957435 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B12552833 : Blo 1957435 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B33474221 : Blo 1957435 33474221 := bstep (se 3 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 33474221 = 12552833) B12552833
theorem B22316147 : Blo 1957435 22316147 := bstep (se 1 (by rfl) ⟨16737110, by rfl⟩ : syracuseStep 22316147 = 33474221) B33474221
theorem B14877431 : Blo 1957435 14877431 := bstep (se 1 (by rfl) ⟨11158073, by rfl⟩ : syracuseStep 14877431 = 22316147) B22316147
theorem B9918287 : Blo 1957435 9918287 := bstep (se 1 (by rfl) ⟨7438715, by rfl⟩ : syracuseStep 9918287 = 14877431) B14877431
theorem B6612191 : Blo 1957435 6612191 := bstep (se 1 (by rfl) ⟨4959143, by rfl⟩ : syracuseStep 6612191 = 9918287) B9918287
theorem B4408127 : Blo 1957435 4408127 := bstep (se 1 (by rfl) ⟨3306095, by rfl⟩ : syracuseStep 4408127 = 6612191) B6612191
theorem B2938751 : Blo 1957435 2938751 := bstep (se 1 (by rfl) ⟨2204063, by rfl⟩ : syracuseStep 2938751 = 4408127) B4408127
theorem B1959167 : Blo 1957435 1959167 := bstep (se 1 (by rfl) ⟨1469375, by rfl⟩ : syracuseStep 1959167 = 2938751) B2938751
theorem B2938757 : Blo 1957435 2938757 := bbase (se 4 (by rfl) ⟨275508, by rfl⟩ : syracuseStep 2938757 = 551017) (by norm_num)
theorem B1959171 : Blo 1957435 1959171 := bstep (se 1 (by rfl) ⟨1469378, by rfl⟩ : syracuseStep 1959171 = 2938757) B2938757
theorem B3306109 : Blo 1957435 3306109 := bbase (se 3 (by rfl) ⟨619895, by rfl⟩ : syracuseStep 3306109 = 1239791) (by norm_num)
theorem B4408145 : Blo 1957435 4408145 := bstep (se 2 (by rfl) ⟨1653054, by rfl⟩ : syracuseStep 4408145 = 3306109) B3306109
theorem B2938763 : Blo 1957435 2938763 := bstep (se 1 (by rfl) ⟨2204072, by rfl⟩ : syracuseStep 2938763 = 4408145) B4408145
theorem B1959175 : Blo 1957435 1959175 := bstep (se 1 (by rfl) ⟨1469381, by rfl⟩ : syracuseStep 1959175 = 2938763) B2938763
theorem B2204077 : Blo 1957435 2204077 := bbase (se 3 (by rfl) ⟨413264, by rfl⟩ : syracuseStep 2204077 = 826529) (by norm_num)
theorem B2938769 : Blo 1957435 2938769 := bstep (se 2 (by rfl) ⟨1102038, by rfl⟩ : syracuseStep 2938769 = 2204077) B2204077
theorem B1959179 : Blo 1957435 1959179 := bstep (se 1 (by rfl) ⟨1469384, by rfl⟩ : syracuseStep 1959179 = 2938769) B2938769
theorem B6612245 : Blo 1957435 6612245 := bbase (se 6 (by rfl) ⟨154974, by rfl⟩ : syracuseStep 6612245 = 309949) (by norm_num)
theorem B4408163 : Blo 1957435 4408163 := bstep (se 1 (by rfl) ⟨3306122, by rfl⟩ : syracuseStep 4408163 = 6612245) B6612245
theorem B2938775 : Blo 1957435 2938775 := bstep (se 1 (by rfl) ⟨2204081, by rfl⟩ : syracuseStep 2938775 = 4408163) B4408163
theorem B1959183 : Blo 1957435 1959183 := bstep (se 1 (by rfl) ⟨1469387, by rfl⟩ : syracuseStep 1959183 = 2938775) B2938775
theorem B2938781 : Blo 1957435 2938781 := bbase (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) (by norm_num)
theorem B1959187 : Blo 1957435 1959187 := bstep (se 1 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 1959187 = 2938781) B2938781
theorem B4408181 : Blo 1957435 4408181 := bbase (se 5 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 4408181 = 413267) (by norm_num)
theorem B2938787 : Blo 1957435 2938787 := bstep (se 1 (by rfl) ⟨2204090, by rfl⟩ : syracuseStep 2938787 = 4408181) B4408181
theorem B1959191 : Blo 1957435 1959191 := bstep (se 1 (by rfl) ⟨1469393, by rfl⟩ : syracuseStep 1959191 = 2938787) B2938787
theorem B5026877 : Blo 1957435 5026877 := bbase (se 3 (by rfl) ⟨942539, by rfl⟩ : syracuseStep 5026877 = 1885079) (by norm_num)
theorem B3351251 : Blo 1957435 3351251 := bstep (se 1 (by rfl) ⟨2513438, by rfl⟩ : syracuseStep 3351251 = 5026877) B5026877
theorem B8936669 : Blo 1957435 8936669 := bstep (se 3 (by rfl) ⟨1675625, by rfl⟩ : syracuseStep 8936669 = 3351251) B3351251
theorem B23831117 : Blo 1957435 23831117 := bstep (se 3 (by rfl) ⟨4468334, by rfl⟩ : syracuseStep 23831117 = 8936669) B8936669
theorem B15887411 : Blo 1957435 15887411 := bstep (se 1 (by rfl) ⟨11915558, by rfl⟩ : syracuseStep 15887411 = 23831117) B23831117
theorem B10591607 : Blo 1957435 10591607 := bstep (se 1 (by rfl) ⟨7943705, by rfl⟩ : syracuseStep 10591607 = 15887411) B15887411
theorem B28244285 : Blo 1957435 28244285 := bstep (se 3 (by rfl) ⟨5295803, by rfl⟩ : syracuseStep 28244285 = 10591607) B10591607
theorem B18829523 : Blo 1957435 18829523 := bstep (se 1 (by rfl) ⟨14122142, by rfl⟩ : syracuseStep 18829523 = 28244285) B28244285
theorem B12553015 : Blo 1957435 12553015 := bstep (se 1 (by rfl) ⟨9414761, by rfl⟩ : syracuseStep 12553015 = 18829523) B18829523
theorem B16737353 : Blo 1957435 16737353 := bstep (se 2 (by rfl) ⟨6276507, by rfl⟩ : syracuseStep 16737353 = 12553015) B12553015
theorem B11158235 : Blo 1957435 11158235 := bstep (se 1 (by rfl) ⟨8368676, by rfl⟩ : syracuseStep 11158235 = 16737353) B16737353
theorem B7438823 : Blo 1957435 7438823 := bstep (se 1 (by rfl) ⟨5579117, by rfl⟩ : syracuseStep 7438823 = 11158235) B11158235
theorem B4959215 : Blo 1957435 4959215 := bstep (se 1 (by rfl) ⟨3719411, by rfl⟩ : syracuseStep 4959215 = 7438823) B7438823
theorem B3306143 : Blo 1957435 3306143 := bstep (se 1 (by rfl) ⟨2479607, by rfl⟩ : syracuseStep 3306143 = 4959215) B4959215
theorem B2204095 : Blo 1957435 2204095 := bstep (se 1 (by rfl) ⟨1653071, by rfl⟩ : syracuseStep 2204095 = 3306143) B3306143
theorem B2938793 : Blo 1957435 2938793 := bstep (se 2 (by rfl) ⟨1102047, by rfl⟩ : syracuseStep 2938793 = 2204095) B2204095
theorem B1959195 : Blo 1957435 1959195 := bstep (se 1 (by rfl) ⟨1469396, by rfl⟩ : syracuseStep 1959195 = 2938793) B2938793
theorem B7438837 : Blo 1957435 7438837 := bbase (se 5 (by rfl) ⟨348695, by rfl⟩ : syracuseStep 7438837 = 697391) (by norm_num)
theorem B9918449 : Blo 1957435 9918449 := bstep (se 2 (by rfl) ⟨3719418, by rfl⟩ : syracuseStep 9918449 = 7438837) B7438837
theorem B6612299 : Blo 1957435 6612299 := bstep (se 1 (by rfl) ⟨4959224, by rfl⟩ : syracuseStep 6612299 = 9918449) B9918449
theorem B4408199 : Blo 1957435 4408199 := bstep (se 1 (by rfl) ⟨3306149, by rfl⟩ : syracuseStep 4408199 = 6612299) B6612299
theorem B2938799 : Blo 1957435 2938799 := bstep (se 1 (by rfl) ⟨2204099, by rfl⟩ : syracuseStep 2938799 = 4408199) B4408199
theorem B1959199 : Blo 1957435 1959199 := bstep (se 1 (by rfl) ⟨1469399, by rfl⟩ : syracuseStep 1959199 = 2938799) B2938799
theorem B2938805 : Blo 1957435 2938805 := bbase (se 5 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 2938805 = 275513) (by norm_num)
theorem B1959203 : Blo 1957435 1959203 := bstep (se 1 (by rfl) ⟨1469402, by rfl⟩ : syracuseStep 1959203 = 2938805) B2938805
theorem B4959245 : Blo 1957435 4959245 := bbase (se 3 (by rfl) ⟨929858, by rfl⟩ : syracuseStep 4959245 = 1859717) (by norm_num)
theorem B3306163 : Blo 1957435 3306163 := bstep (se 1 (by rfl) ⟨2479622, by rfl⟩ : syracuseStep 3306163 = 4959245) B4959245
theorem B4408217 : Blo 1957435 4408217 := bstep (se 2 (by rfl) ⟨1653081, by rfl⟩ : syracuseStep 4408217 = 3306163) B3306163
theorem B2938811 : Blo 1957435 2938811 := bstep (se 1 (by rfl) ⟨2204108, by rfl⟩ : syracuseStep 2938811 = 4408217) B4408217
theorem B1959207 : Blo 1957435 1959207 := bstep (se 1 (by rfl) ⟨1469405, by rfl⟩ : syracuseStep 1959207 = 2938811) B2938811
theorem B2204113 : Blo 1957435 2204113 := bbase (se 2 (by rfl) ⟨826542, by rfl⟩ : syracuseStep 2204113 = 1653085) (by norm_num)
theorem B2938817 : Blo 1957435 2938817 := bstep (se 2 (by rfl) ⟨1102056, by rfl⟩ : syracuseStep 2938817 = 2204113) B2204113
theorem B1959211 : Blo 1957435 1959211 := bstep (se 1 (by rfl) ⟨1469408, by rfl⟩ : syracuseStep 1959211 = 2938817) B2938817
theorem B4184381 : Blo 1957435 4184381 := bbase (se 3 (by rfl) ⟨784571, by rfl⟩ : syracuseStep 4184381 = 1569143) (by norm_num)
theorem B2789587 : Blo 1957435 2789587 := bstep (se 1 (by rfl) ⟨2092190, by rfl⟩ : syracuseStep 2789587 = 4184381) B4184381
theorem B3719449 : Blo 1957435 3719449 := bstep (se 2 (by rfl) ⟨1394793, by rfl⟩ : syracuseStep 3719449 = 2789587) B2789587
theorem B4959265 : Blo 1957435 4959265 := bstep (se 2 (by rfl) ⟨1859724, by rfl⟩ : syracuseStep 4959265 = 3719449) B3719449
theorem B6612353 : Blo 1957435 6612353 := bstep (se 2 (by rfl) ⟨2479632, by rfl⟩ : syracuseStep 6612353 = 4959265) B4959265
theorem B4408235 : Blo 1957435 4408235 := bstep (se 1 (by rfl) ⟨3306176, by rfl⟩ : syracuseStep 4408235 = 6612353) B6612353
theorem B2938823 : Blo 1957435 2938823 := bstep (se 1 (by rfl) ⟨2204117, by rfl⟩ : syracuseStep 2938823 = 4408235) B4408235
theorem B1959215 : Blo 1957435 1959215 := bstep (se 1 (by rfl) ⟨1469411, by rfl⟩ : syracuseStep 1959215 = 2938823) B2938823
theorem B2938829 : Blo 1957435 2938829 := bbase (se 3 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 2938829 = 1102061) (by norm_num)
theorem B1959219 : Blo 1957435 1959219 := bstep (se 1 (by rfl) ⟨1469414, by rfl⟩ : syracuseStep 1959219 = 2938829) B2938829
theorem B4408253 : Blo 1957435 4408253 := bbase (se 3 (by rfl) ⟨826547, by rfl⟩ : syracuseStep 4408253 = 1653095) (by norm_num)
theorem B2938835 : Blo 1957435 2938835 := bstep (se 1 (by rfl) ⟨2204126, by rfl⟩ : syracuseStep 2938835 = 4408253) B4408253
theorem B1959223 : Blo 1957435 1959223 := bstep (se 1 (by rfl) ⟨1469417, by rfl⟩ : syracuseStep 1959223 = 2938835) B2938835
theorem B3306197 : Blo 1957435 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B2204131 : Blo 1957435 2204131 := bstep (se 1 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 2204131 = 3306197) B3306197
theorem B2938841 : Blo 1957435 2938841 := bstep (se 2 (by rfl) ⟨1102065, by rfl⟩ : syracuseStep 2938841 = 2204131) B2204131
theorem B1959227 : Blo 1957435 1959227 := bstep (se 1 (by rfl) ⟨1469420, by rfl⟩ : syracuseStep 1959227 = 2938841) B2938841
theorem B2234209 : Blo 1957435 2234209 := bbase (se 2 (by rfl) ⟨837828, by rfl⟩ : syracuseStep 2234209 = 1675657) (by norm_num)
theorem B2978945 : Blo 1957435 2978945 := bstep (se 2 (by rfl) ⟨1117104, by rfl⟩ : syracuseStep 2978945 = 2234209) B2234209
theorem B1985963 : Blo 1957435 1985963 := bstep (se 1 (by rfl) ⟨1489472, by rfl⟩ : syracuseStep 1985963 = 2978945) B2978945
theorem B5295901 : Blo 1957435 5295901 := bstep (se 3 (by rfl) ⟨992981, by rfl⟩ : syracuseStep 5295901 = 1985963) B1985963
theorem B7061201 : Blo 1957435 7061201 := bstep (se 2 (by rfl) ⟨2647950, by rfl⟩ : syracuseStep 7061201 = 5295901) B5295901
theorem B4707467 : Blo 1957435 4707467 := bstep (se 1 (by rfl) ⟨3530600, by rfl⟩ : syracuseStep 4707467 = 7061201) B7061201
theorem B3138311 : Blo 1957435 3138311 := bstep (se 1 (by rfl) ⟨2353733, by rfl⟩ : syracuseStep 3138311 = 4707467) B4707467
theorem B8368829 : Blo 1957435 8368829 := bstep (se 3 (by rfl) ⟨1569155, by rfl⟩ : syracuseStep 8368829 = 3138311) B3138311
theorem B5579219 : Blo 1957435 5579219 := bstep (se 1 (by rfl) ⟨4184414, by rfl⟩ : syracuseStep 5579219 = 8368829) B8368829
theorem B14877917 : Blo 1957435 14877917 := bstep (se 3 (by rfl) ⟨2789609, by rfl⟩ : syracuseStep 14877917 = 5579219) B5579219
theorem B9918611 : Blo 1957435 9918611 := bstep (se 1 (by rfl) ⟨7438958, by rfl⟩ : syracuseStep 9918611 = 14877917) B14877917
theorem B6612407 : Blo 1957435 6612407 := bstep (se 1 (by rfl) ⟨4959305, by rfl⟩ : syracuseStep 6612407 = 9918611) B9918611
theorem B4408271 : Blo 1957435 4408271 := bstep (se 1 (by rfl) ⟨3306203, by rfl⟩ : syracuseStep 4408271 = 6612407) B6612407
theorem B2938847 : Blo 1957435 2938847 := bstep (se 1 (by rfl) ⟨2204135, by rfl⟩ : syracuseStep 2938847 = 4408271) B4408271
theorem B1959231 : Blo 1957435 1959231 := bstep (se 1 (by rfl) ⟨1469423, by rfl⟩ : syracuseStep 1959231 = 2938847) B2938847
theorem B2938853 : Blo 1957435 2938853 := bbase (se 4 (by rfl) ⟨275517, by rfl⟩ : syracuseStep 2938853 = 551035) (by norm_num)
theorem B1959235 : Blo 1957435 1959235 := bstep (se 1 (by rfl) ⟨1469426, by rfl⟩ : syracuseStep 1959235 = 2938853) B2938853
theorem B2385857 : Blo 1957435 2385857 := bbase (se 2 (by rfl) ⟨894696, by rfl⟩ : syracuseStep 2385857 = 1789393) (by norm_num)
theorem B6362285 : Blo 1957435 6362285 := bstep (se 3 (by rfl) ⟨1192928, by rfl⟩ : syracuseStep 6362285 = 2385857) B2385857
theorem B16966093 : Blo 1957435 16966093 := bstep (se 3 (by rfl) ⟨3181142, by rfl⟩ : syracuseStep 16966093 = 6362285) B6362285
theorem B22621457 : Blo 1957435 22621457 := bstep (se 2 (by rfl) ⟨8483046, by rfl⟩ : syracuseStep 22621457 = 16966093) B16966093
theorem B60323885 : Blo 1957435 60323885 := bstep (se 3 (by rfl) ⟨11310728, by rfl⟩ : syracuseStep 60323885 = 22621457) B22621457
theorem B40215923 : Blo 1957435 40215923 := bstep (se 1 (by rfl) ⟨30161942, by rfl⟩ : syracuseStep 40215923 = 60323885) B60323885
theorem B26810615 : Blo 1957435 26810615 := bstep (se 1 (by rfl) ⟨20107961, by rfl⟩ : syracuseStep 26810615 = 40215923) B40215923
theorem B17873743 : Blo 1957435 17873743 := bstep (se 1 (by rfl) ⟨13405307, by rfl⟩ : syracuseStep 17873743 = 26810615) B26810615
theorem B23831657 : Blo 1957435 23831657 := bstep (se 2 (by rfl) ⟨8936871, by rfl⟩ : syracuseStep 23831657 = 17873743) B17873743
theorem B15887771 : Blo 1957435 15887771 := bstep (se 1 (by rfl) ⟨11915828, by rfl⟩ : syracuseStep 15887771 = 23831657) B23831657
theorem B10591847 : Blo 1957435 10591847 := bstep (se 1 (by rfl) ⟨7943885, by rfl⟩ : syracuseStep 10591847 = 15887771) B15887771
theorem B7061231 : Blo 1957435 7061231 := bstep (se 1 (by rfl) ⟨5295923, by rfl⟩ : syracuseStep 7061231 = 10591847) B10591847
theorem B4707487 : Blo 1957435 4707487 := bstep (se 1 (by rfl) ⟨3530615, by rfl⟩ : syracuseStep 4707487 = 7061231) B7061231
theorem B6276649 : Blo 1957435 6276649 := bstep (se 2 (by rfl) ⟨2353743, by rfl⟩ : syracuseStep 6276649 = 4707487) B4707487
theorem B8368865 : Blo 1957435 8368865 := bstep (se 2 (by rfl) ⟨3138324, by rfl⟩ : syracuseStep 8368865 = 6276649) B6276649
theorem B5579243 : Blo 1957435 5579243 := bstep (se 1 (by rfl) ⟨4184432, by rfl⟩ : syracuseStep 5579243 = 8368865) B8368865
theorem B3719495 : Blo 1957435 3719495 := bstep (se 1 (by rfl) ⟨2789621, by rfl⟩ : syracuseStep 3719495 = 5579243) B5579243
theorem B2479663 : Blo 1957435 2479663 := bstep (se 1 (by rfl) ⟨1859747, by rfl⟩ : syracuseStep 2479663 = 3719495) B3719495
theorem B3306217 : Blo 1957435 3306217 := bstep (se 2 (by rfl) ⟨1239831, by rfl⟩ : syracuseStep 3306217 = 2479663) B2479663
theorem B4408289 : Blo 1957435 4408289 := bstep (se 2 (by rfl) ⟨1653108, by rfl⟩ : syracuseStep 4408289 = 3306217) B3306217
theorem B2938859 : Blo 1957435 2938859 := bstep (se 1 (by rfl) ⟨2204144, by rfl⟩ : syracuseStep 2938859 = 4408289) B4408289
theorem B1959239 : Blo 1957435 1959239 := bstep (se 1 (by rfl) ⟨1469429, by rfl⟩ : syracuseStep 1959239 = 2938859) B2938859
theorem B2204149 : Blo 1957435 2204149 := bbase (se 5 (by rfl) ⟨103319, by rfl⟩ : syracuseStep 2204149 = 206639) (by norm_num)
theorem B2938865 : Blo 1957435 2938865 := bstep (se 2 (by rfl) ⟨1102074, by rfl⟩ : syracuseStep 2938865 = 2204149) B2204149
theorem B1959243 : Blo 1957435 1959243 := bstep (se 1 (by rfl) ⟨1469432, by rfl⟩ : syracuseStep 1959243 = 2938865) B2938865
theorem B2479673 : Blo 1957435 2479673 := bbase (se 2 (by rfl) ⟨929877, by rfl⟩ : syracuseStep 2479673 = 1859755) (by norm_num)
theorem B6612461 : Blo 1957435 6612461 := bstep (se 3 (by rfl) ⟨1239836, by rfl⟩ : syracuseStep 6612461 = 2479673) B2479673
theorem B4408307 : Blo 1957435 4408307 := bstep (se 1 (by rfl) ⟨3306230, by rfl⟩ : syracuseStep 4408307 = 6612461) B6612461
theorem B2938871 : Blo 1957435 2938871 := bstep (se 1 (by rfl) ⟨2204153, by rfl⟩ : syracuseStep 2938871 = 4408307) B4408307
theorem B1959247 : Blo 1957435 1959247 := bstep (se 1 (by rfl) ⟨1469435, by rfl⟩ : syracuseStep 1959247 = 2938871) B2938871
theorem B2938877 : Blo 1957435 2938877 := bbase (se 3 (by rfl) ⟨551039, by rfl⟩ : syracuseStep 2938877 = 1102079) (by norm_num)
theorem B1959251 : Blo 1957435 1959251 := bstep (se 1 (by rfl) ⟨1469438, by rfl⟩ : syracuseStep 1959251 = 2938877) B2938877
theorem B4408325 : Blo 1957435 4408325 := bbase (se 4 (by rfl) ⟨413280, by rfl⟩ : syracuseStep 4408325 = 826561) (by norm_num)
theorem B2938883 : Blo 1957435 2938883 := bstep (se 1 (by rfl) ⟨2204162, by rfl⟩ : syracuseStep 2938883 = 4408325) B4408325
theorem B1959255 : Blo 1957435 1959255 := bstep (se 1 (by rfl) ⟨1469441, by rfl⟩ : syracuseStep 1959255 = 2938883) B2938883
theorem B3719533 : Blo 1957435 3719533 := bbase (se 3 (by rfl) ⟨697412, by rfl⟩ : syracuseStep 3719533 = 1394825) (by norm_num)
theorem B4959377 : Blo 1957435 4959377 := bstep (se 2 (by rfl) ⟨1859766, by rfl⟩ : syracuseStep 4959377 = 3719533) B3719533
theorem B3306251 : Blo 1957435 3306251 := bstep (se 1 (by rfl) ⟨2479688, by rfl⟩ : syracuseStep 3306251 = 4959377) B4959377
theorem B2204167 : Blo 1957435 2204167 := bstep (se 1 (by rfl) ⟨1653125, by rfl⟩ : syracuseStep 2204167 = 3306251) B3306251
theorem B2938889 : Blo 1957435 2938889 := bstep (se 2 (by rfl) ⟨1102083, by rfl⟩ : syracuseStep 2938889 = 2204167) B2204167
theorem B1959259 : Blo 1957435 1959259 := bstep (se 1 (by rfl) ⟨1469444, by rfl⟩ : syracuseStep 1959259 = 2938889) B2938889
theorem B9918773 : Blo 1957435 9918773 := bbase (se 5 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 9918773 = 929885) (by norm_num)
theorem B6612515 : Blo 1957435 6612515 := bstep (se 1 (by rfl) ⟨4959386, by rfl⟩ : syracuseStep 6612515 = 9918773) B9918773
theorem B4408343 : Blo 1957435 4408343 := bstep (se 1 (by rfl) ⟨3306257, by rfl⟩ : syracuseStep 4408343 = 6612515) B6612515
theorem B2938895 : Blo 1957435 2938895 := bstep (se 1 (by rfl) ⟨2204171, by rfl⟩ : syracuseStep 2938895 = 4408343) B4408343
theorem B1959263 : Blo 1957435 1959263 := bstep (se 1 (by rfl) ⟨1469447, by rfl⟩ : syracuseStep 1959263 = 2938895) B2938895
theorem B2938901 : Blo 1957435 2938901 := bbase (se 6 (by rfl) ⟨68880, by rfl⟩ : syracuseStep 2938901 = 137761) (by norm_num)
theorem B1959267 : Blo 1957435 1959267 := bstep (se 1 (by rfl) ⟨1469450, by rfl⟩ : syracuseStep 1959267 = 2938901) B2938901
theorem B3578845 : Blo 1957435 3578845 := bbase (se 3 (by rfl) ⟨671033, by rfl⟩ : syracuseStep 3578845 = 1342067) (by norm_num)
theorem B4771793 : Blo 1957435 4771793 := bstep (se 2 (by rfl) ⟨1789422, by rfl⟩ : syracuseStep 4771793 = 3578845) B3578845
theorem B3181195 : Blo 1957435 3181195 := bstep (se 1 (by rfl) ⟨2385896, by rfl⟩ : syracuseStep 3181195 = 4771793) B4771793
theorem B4241593 : Blo 1957435 4241593 := bstep (se 2 (by rfl) ⟨1590597, by rfl⟩ : syracuseStep 4241593 = 3181195) B3181195
theorem B5655457 : Blo 1957435 5655457 := bstep (se 2 (by rfl) ⟨2120796, by rfl⟩ : syracuseStep 5655457 = 4241593) B4241593
theorem B7540609 : Blo 1957435 7540609 := bstep (se 2 (by rfl) ⟨2827728, by rfl⟩ : syracuseStep 7540609 = 5655457) B5655457
theorem B10054145 : Blo 1957435 10054145 := bstep (se 2 (by rfl) ⟨3770304, by rfl⟩ : syracuseStep 10054145 = 7540609) B7540609
theorem B6702763 : Blo 1957435 6702763 := bstep (se 1 (by rfl) ⟨5027072, by rfl⟩ : syracuseStep 6702763 = 10054145) B10054145
theorem B8937017 : Blo 1957435 8937017 := bstep (se 2 (by rfl) ⟨3351381, by rfl⟩ : syracuseStep 8937017 = 6702763) B6702763
theorem B5958011 : Blo 1957435 5958011 := bstep (se 1 (by rfl) ⟨4468508, by rfl⟩ : syracuseStep 5958011 = 8937017) B8937017
theorem B3972007 : Blo 1957435 3972007 := bstep (se 1 (by rfl) ⟨2979005, by rfl⟩ : syracuseStep 3972007 = 5958011) B5958011
theorem B5296009 : Blo 1957435 5296009 := bstep (se 2 (by rfl) ⟨1986003, by rfl⟩ : syracuseStep 5296009 = 3972007) B3972007
theorem B7061345 : Blo 1957435 7061345 := bstep (se 2 (by rfl) ⟨2648004, by rfl⟩ : syracuseStep 7061345 = 5296009) B5296009
theorem B4707563 : Blo 1957435 4707563 := bstep (se 1 (by rfl) ⟨3530672, by rfl⟩ : syracuseStep 4707563 = 7061345) B7061345
theorem B12553501 : Blo 1957435 12553501 := bstep (se 3 (by rfl) ⟨2353781, by rfl⟩ : syracuseStep 12553501 = 4707563) B4707563
theorem B16738001 : Blo 1957435 16738001 := bstep (se 2 (by rfl) ⟨6276750, by rfl⟩ : syracuseStep 16738001 = 12553501) B12553501
theorem B11158667 : Blo 1957435 11158667 := bstep (se 1 (by rfl) ⟨8369000, by rfl⟩ : syracuseStep 11158667 = 16738001) B16738001
theorem B7439111 : Blo 1957435 7439111 := bstep (se 1 (by rfl) ⟨5579333, by rfl⟩ : syracuseStep 7439111 = 11158667) B11158667
theorem B4959407 : Blo 1957435 4959407 := bstep (se 1 (by rfl) ⟨3719555, by rfl⟩ : syracuseStep 4959407 = 7439111) B7439111
theorem B3306271 : Blo 1957435 3306271 := bstep (se 1 (by rfl) ⟨2479703, by rfl⟩ : syracuseStep 3306271 = 4959407) B4959407
theorem B4408361 : Blo 1957435 4408361 := bstep (se 2 (by rfl) ⟨1653135, by rfl⟩ : syracuseStep 4408361 = 3306271) B3306271
theorem B2938907 : Blo 1957435 2938907 := bstep (se 1 (by rfl) ⟨2204180, by rfl⟩ : syracuseStep 2938907 = 4408361) B4408361
theorem B1959271 : Blo 1957435 1959271 := bstep (se 1 (by rfl) ⟨1469453, by rfl⟩ : syracuseStep 1959271 = 2938907) B2938907
theorem B2204185 : Blo 1957435 2204185 := bbase (se 2 (by rfl) ⟨826569, by rfl⟩ : syracuseStep 2204185 = 1653139) (by norm_num)
theorem B2938913 : Blo 1957435 2938913 := bstep (se 2 (by rfl) ⟨1102092, by rfl⟩ : syracuseStep 2938913 = 2204185) B2204185
theorem B1959275 : Blo 1957435 1959275 := bstep (se 1 (by rfl) ⟨1469456, by rfl⟩ : syracuseStep 1959275 = 2938913) B2938913
theorem B7439141 : Blo 1957435 7439141 := bbase (se 4 (by rfl) ⟨697419, by rfl⟩ : syracuseStep 7439141 = 1394839) (by norm_num)
theorem B4959427 : Blo 1957435 4959427 := bstep (se 1 (by rfl) ⟨3719570, by rfl⟩ : syracuseStep 4959427 = 7439141) B7439141
theorem B6612569 : Blo 1957435 6612569 := bstep (se 2 (by rfl) ⟨2479713, by rfl⟩ : syracuseStep 6612569 = 4959427) B4959427
theorem B4408379 : Blo 1957435 4408379 := bstep (se 1 (by rfl) ⟨3306284, by rfl⟩ : syracuseStep 4408379 = 6612569) B6612569
theorem B2938919 : Blo 1957435 2938919 := bstep (se 1 (by rfl) ⟨2204189, by rfl⟩ : syracuseStep 2938919 = 4408379) B4408379
theorem B1959279 : Blo 1957435 1959279 := bstep (se 1 (by rfl) ⟨1469459, by rfl⟩ : syracuseStep 1959279 = 2938919) B2938919
theorem B2938925 : Blo 1957435 2938925 := bbase (se 3 (by rfl) ⟨551048, by rfl⟩ : syracuseStep 2938925 = 1102097) (by norm_num)
theorem B1959283 : Blo 1957435 1959283 := bstep (se 1 (by rfl) ⟨1469462, by rfl⟩ : syracuseStep 1959283 = 2938925) B2938925
theorem B4408397 : Blo 1957435 4408397 := bbase (se 3 (by rfl) ⟨826574, by rfl⟩ : syracuseStep 4408397 = 1653149) (by norm_num)
theorem B2938931 : Blo 1957435 2938931 := bstep (se 1 (by rfl) ⟨2204198, by rfl⟩ : syracuseStep 2938931 = 4408397) B4408397
theorem B1959287 : Blo 1957435 1959287 := bstep (se 1 (by rfl) ⟨1469465, by rfl⟩ : syracuseStep 1959287 = 2938931) B2938931
theorem B2479729 : Blo 1957435 2479729 := bbase (se 2 (by rfl) ⟨929898, by rfl⟩ : syracuseStep 2479729 = 1859797) (by norm_num)
theorem B3306305 : Blo 1957435 3306305 := bstep (se 2 (by rfl) ⟨1239864, by rfl⟩ : syracuseStep 3306305 = 2479729) B2479729
theorem B2204203 : Blo 1957435 2204203 := bstep (se 1 (by rfl) ⟨1653152, by rfl⟩ : syracuseStep 2204203 = 3306305) B3306305
theorem B2938937 : Blo 1957435 2938937 := bstep (se 2 (by rfl) ⟨1102101, by rfl⟩ : syracuseStep 2938937 = 2204203) B2204203
theorem B1959291 : Blo 1957435 1959291 := bstep (se 1 (by rfl) ⟨1469468, by rfl⟩ : syracuseStep 1959291 = 2938937) B2938937
theorem B8937125 : Blo 1957435 8937125 := bbase (se 4 (by rfl) ⟨837855, by rfl⟩ : syracuseStep 8937125 = 1675711) (by norm_num)
theorem B5958083 : Blo 1957435 5958083 := bstep (se 1 (by rfl) ⟨4468562, by rfl⟩ : syracuseStep 5958083 = 8937125) B8937125
theorem B15888221 : Blo 1957435 15888221 := bstep (se 3 (by rfl) ⟨2979041, by rfl⟩ : syracuseStep 15888221 = 5958083) B5958083
theorem B10592147 : Blo 1957435 10592147 := bstep (se 1 (by rfl) ⟨7944110, by rfl⟩ : syracuseStep 10592147 = 15888221) B15888221
theorem B7061431 : Blo 1957435 7061431 := bstep (se 1 (by rfl) ⟨5296073, by rfl⟩ : syracuseStep 7061431 = 10592147) B10592147
theorem B9415241 : Blo 1957435 9415241 := bstep (se 2 (by rfl) ⟨3530715, by rfl⟩ : syracuseStep 9415241 = 7061431) B7061431
theorem B6276827 : Blo 1957435 6276827 := bstep (se 1 (by rfl) ⟨4707620, by rfl⟩ : syracuseStep 6276827 = 9415241) B9415241
theorem B4184551 : Blo 1957435 4184551 := bstep (se 1 (by rfl) ⟨3138413, by rfl⟩ : syracuseStep 4184551 = 6276827) B6276827
theorem B22317605 : Blo 1957435 22317605 := bstep (se 4 (by rfl) ⟨2092275, by rfl⟩ : syracuseStep 22317605 = 4184551) B4184551
theorem B14878403 : Blo 1957435 14878403 := bstep (se 1 (by rfl) ⟨11158802, by rfl⟩ : syracuseStep 14878403 = 22317605) B22317605
theorem B9918935 : Blo 1957435 9918935 := bstep (se 1 (by rfl) ⟨7439201, by rfl⟩ : syracuseStep 9918935 = 14878403) B14878403
theorem B6612623 : Blo 1957435 6612623 := bstep (se 1 (by rfl) ⟨4959467, by rfl⟩ : syracuseStep 6612623 = 9918935) B9918935
theorem B4408415 : Blo 1957435 4408415 := bstep (se 1 (by rfl) ⟨3306311, by rfl⟩ : syracuseStep 4408415 = 6612623) B6612623
theorem B2938943 : Blo 1957435 2938943 := bstep (se 1 (by rfl) ⟨2204207, by rfl⟩ : syracuseStep 2938943 = 4408415) B4408415
theorem B1959295 : Blo 1957435 1959295 := bstep (se 1 (by rfl) ⟨1469471, by rfl⟩ : syracuseStep 1959295 = 2938943) B2938943
theorem B2938949 : Blo 1957435 2938949 := bbase (se 4 (by rfl) ⟨275526, by rfl⟩ : syracuseStep 2938949 = 551053) (by norm_num)
theorem B1959299 : Blo 1957435 1959299 := bstep (se 1 (by rfl) ⟨1469474, by rfl⟩ : syracuseStep 1959299 = 2938949) B2938949
theorem B3306325 : Blo 1957435 3306325 := bbase (se 9 (by rfl) ⟨9686, by rfl⟩ : syracuseStep 3306325 = 19373) (by norm_num)
theorem B4408433 : Blo 1957435 4408433 := bstep (se 2 (by rfl) ⟨1653162, by rfl⟩ : syracuseStep 4408433 = 3306325) B3306325
theorem B2938955 : Blo 1957435 2938955 := bstep (se 1 (by rfl) ⟨2204216, by rfl⟩ : syracuseStep 2938955 = 4408433) B4408433
theorem B1959303 : Blo 1957435 1959303 := bstep (se 1 (by rfl) ⟨1469477, by rfl⟩ : syracuseStep 1959303 = 2938955) B2938955
theorem B2204221 : Blo 1957435 2204221 := bbase (se 3 (by rfl) ⟨413291, by rfl⟩ : syracuseStep 2204221 = 826583) (by norm_num)
theorem B2938961 : Blo 1957435 2938961 := bstep (se 2 (by rfl) ⟨1102110, by rfl⟩ : syracuseStep 2938961 = 2204221) B2204221
theorem B1959307 : Blo 1957435 1959307 := bstep (se 1 (by rfl) ⟨1469480, by rfl⟩ : syracuseStep 1959307 = 2938961) B2938961
theorem B6612677 : Blo 1957435 6612677 := bbase (se 4 (by rfl) ⟨619938, by rfl⟩ : syracuseStep 6612677 = 1239877) (by norm_num)
theorem B4408451 : Blo 1957435 4408451 := bstep (se 1 (by rfl) ⟨3306338, by rfl⟩ : syracuseStep 4408451 = 6612677) B6612677
theorem B2938967 : Blo 1957435 2938967 := bstep (se 1 (by rfl) ⟨2204225, by rfl⟩ : syracuseStep 2938967 = 4408451) B4408451
theorem B1959311 : Blo 1957435 1959311 := bstep (se 1 (by rfl) ⟨1469483, by rfl⟩ : syracuseStep 1959311 = 2938967) B2938967
theorem B2938973 : Blo 1957435 2938973 := bbase (se 3 (by rfl) ⟨551057, by rfl⟩ : syracuseStep 2938973 = 1102115) (by norm_num)
theorem B1959315 : Blo 1957435 1959315 := bstep (se 1 (by rfl) ⟨1469486, by rfl⟩ : syracuseStep 1959315 = 2938973) B2938973
theorem B4408469 : Blo 1957435 4408469 := bbase (se 6 (by rfl) ⟨103323, by rfl⟩ : syracuseStep 4408469 = 206647) (by norm_num)
theorem B2938979 : Blo 1957435 2938979 := bstep (se 1 (by rfl) ⟨2204234, by rfl⟩ : syracuseStep 2938979 = 4408469) B4408469
theorem B1959319 : Blo 1957435 1959319 := bstep (se 1 (by rfl) ⟨1469489, by rfl⟩ : syracuseStep 1959319 = 2938979) B2938979
theorem B2789741 : Blo 1957435 2789741 := bbase (se 3 (by rfl) ⟨523076, by rfl⟩ : syracuseStep 2789741 = 1046153) (by norm_num)
theorem B7439309 : Blo 1957435 7439309 := bstep (se 3 (by rfl) ⟨1394870, by rfl⟩ : syracuseStep 7439309 = 2789741) B2789741
theorem B4959539 : Blo 1957435 4959539 := bstep (se 1 (by rfl) ⟨3719654, by rfl⟩ : syracuseStep 4959539 = 7439309) B7439309
theorem B3306359 : Blo 1957435 3306359 := bstep (se 1 (by rfl) ⟨2479769, by rfl⟩ : syracuseStep 3306359 = 4959539) B4959539
theorem B2204239 : Blo 1957435 2204239 := bstep (se 1 (by rfl) ⟨1653179, by rfl⟩ : syracuseStep 2204239 = 3306359) B3306359
theorem B2938985 : Blo 1957435 2938985 := bstep (se 2 (by rfl) ⟨1102119, by rfl⟩ : syracuseStep 2938985 = 2204239) B2204239
theorem B1959323 : Blo 1957435 1959323 := bstep (se 1 (by rfl) ⟨1469492, by rfl⟩ : syracuseStep 1959323 = 2938985) B2938985
theorem B3530773 : Blo 1957435 3530773 := bbase (se 6 (by rfl) ⟨82752, by rfl⟩ : syracuseStep 3530773 = 165505) (by norm_num)
theorem B18830789 : Blo 1957435 18830789 := bstep (se 4 (by rfl) ⟨1765386, by rfl⟩ : syracuseStep 18830789 = 3530773) B3530773
theorem B12553859 : Blo 1957435 12553859 := bstep (se 1 (by rfl) ⟨9415394, by rfl⟩ : syracuseStep 12553859 = 18830789) B18830789
theorem B8369239 : Blo 1957435 8369239 := bstep (se 1 (by rfl) ⟨6276929, by rfl⟩ : syracuseStep 8369239 = 12553859) B12553859
theorem B11158985 : Blo 1957435 11158985 := bstep (se 2 (by rfl) ⟨4184619, by rfl⟩ : syracuseStep 11158985 = 8369239) B8369239
theorem B7439323 : Blo 1957435 7439323 := bstep (se 1 (by rfl) ⟨5579492, by rfl⟩ : syracuseStep 7439323 = 11158985) B11158985
theorem B9919097 : Blo 1957435 9919097 := bstep (se 2 (by rfl) ⟨3719661, by rfl⟩ : syracuseStep 9919097 = 7439323) B7439323
theorem B6612731 : Blo 1957435 6612731 := bstep (se 1 (by rfl) ⟨4959548, by rfl⟩ : syracuseStep 6612731 = 9919097) B9919097
theorem B4408487 : Blo 1957435 4408487 := bstep (se 1 (by rfl) ⟨3306365, by rfl⟩ : syracuseStep 4408487 = 6612731) B6612731
theorem B2938991 : Blo 1957435 2938991 := bstep (se 1 (by rfl) ⟨2204243, by rfl⟩ : syracuseStep 2938991 = 4408487) B4408487
theorem B1959327 : Blo 1957435 1959327 := bstep (se 1 (by rfl) ⟨1469495, by rfl⟩ : syracuseStep 1959327 = 2938991) B2938991
theorem B2938997 : Blo 1957435 2938997 := bbase (se 5 (by rfl) ⟨137765, by rfl⟩ : syracuseStep 2938997 = 275531) (by norm_num)
theorem B1959331 : Blo 1957435 1959331 := bstep (se 1 (by rfl) ⟨1469498, by rfl⟩ : syracuseStep 1959331 = 2938997) B2938997
theorem B3719677 : Blo 1957435 3719677 := bbase (se 3 (by rfl) ⟨697439, by rfl⟩ : syracuseStep 3719677 = 1394879) (by norm_num)
theorem B4959569 : Blo 1957435 4959569 := bstep (se 2 (by rfl) ⟨1859838, by rfl⟩ : syracuseStep 4959569 = 3719677) B3719677
theorem B3306379 : Blo 1957435 3306379 := bstep (se 1 (by rfl) ⟨2479784, by rfl⟩ : syracuseStep 3306379 = 4959569) B4959569
theorem B4408505 : Blo 1957435 4408505 := bstep (se 2 (by rfl) ⟨1653189, by rfl⟩ : syracuseStep 4408505 = 3306379) B3306379
theorem B2939003 : Blo 1957435 2939003 := bstep (se 1 (by rfl) ⟨2204252, by rfl⟩ : syracuseStep 2939003 = 4408505) B4408505
theorem B1959335 : Blo 1957435 1959335 := bstep (se 1 (by rfl) ⟨1469501, by rfl⟩ : syracuseStep 1959335 = 2939003) B2939003
theorem B2204257 : Blo 1957435 2204257 := bbase (se 2 (by rfl) ⟨826596, by rfl⟩ : syracuseStep 2204257 = 1653193) (by norm_num)
theorem B2939009 : Blo 1957435 2939009 := bstep (se 2 (by rfl) ⟨1102128, by rfl⟩ : syracuseStep 2939009 = 2204257) B2204257
theorem B1959339 : Blo 1957435 1959339 := bstep (se 1 (by rfl) ⟨1469504, by rfl⟩ : syracuseStep 1959339 = 2939009) B2939009
theorem B4959589 : Blo 1957435 4959589 := bbase (se 4 (by rfl) ⟨464961, by rfl⟩ : syracuseStep 4959589 = 929923) (by norm_num)
theorem B6612785 : Blo 1957435 6612785 := bstep (se 2 (by rfl) ⟨2479794, by rfl⟩ : syracuseStep 6612785 = 4959589) B4959589
theorem B4408523 : Blo 1957435 4408523 := bstep (se 1 (by rfl) ⟨3306392, by rfl⟩ : syracuseStep 4408523 = 6612785) B6612785
theorem B2939015 : Blo 1957435 2939015 := bstep (se 1 (by rfl) ⟨2204261, by rfl⟩ : syracuseStep 2939015 = 4408523) B4408523
theorem B1959343 : Blo 1957435 1959343 := bstep (se 1 (by rfl) ⟨1469507, by rfl⟩ : syracuseStep 1959343 = 2939015) B2939015
theorem B2939021 : Blo 1957435 2939021 := bbase (se 3 (by rfl) ⟨551066, by rfl⟩ : syracuseStep 2939021 = 1102133) (by norm_num)
theorem B1959347 : Blo 1957435 1959347 := bstep (se 1 (by rfl) ⟨1469510, by rfl⟩ : syracuseStep 1959347 = 2939021) B2939021
theorem B4408541 : Blo 1957435 4408541 := bbase (se 3 (by rfl) ⟨826601, by rfl⟩ : syracuseStep 4408541 = 1653203) (by norm_num)
theorem B2939027 : Blo 1957435 2939027 := bstep (se 1 (by rfl) ⟨2204270, by rfl⟩ : syracuseStep 2939027 = 4408541) B4408541
theorem B1959351 : Blo 1957435 1959351 := bstep (se 1 (by rfl) ⟨1469513, by rfl⟩ : syracuseStep 1959351 = 2939027) B2939027
theorem B3306413 : Blo 1957435 3306413 := bbase (se 3 (by rfl) ⟨619952, by rfl⟩ : syracuseStep 3306413 = 1239905) (by norm_num)
theorem B2204275 : Blo 1957435 2204275 := bstep (se 1 (by rfl) ⟨1653206, by rfl⟩ : syracuseStep 2204275 = 3306413) B3306413
theorem B2939033 : Blo 1957435 2939033 := bstep (se 2 (by rfl) ⟨1102137, by rfl⟩ : syracuseStep 2939033 = 2204275) B2204275
theorem B1959355 : Blo 1957435 1959355 := bstep (se 1 (by rfl) ⟨1469516, by rfl⟩ : syracuseStep 1959355 = 2939033) B2939033
theorem B6205493 : Blo 1957435 6205493 := bbase (se 5 (by rfl) ⟨290882, by rfl⟩ : syracuseStep 6205493 = 581765) (by norm_num)
theorem B4136995 : Blo 1957435 4136995 := bstep (se 1 (by rfl) ⟨3102746, by rfl⟩ : syracuseStep 4136995 = 6205493) B6205493
theorem B5515993 : Blo 1957435 5515993 := bstep (se 2 (by rfl) ⟨2068497, by rfl⟩ : syracuseStep 5515993 = 4136995) B4136995
theorem B7354657 : Blo 1957435 7354657 := bstep (se 2 (by rfl) ⟨2757996, by rfl⟩ : syracuseStep 7354657 = 5515993) B5515993
theorem B39224837 : Blo 1957435 39224837 := bstep (se 4 (by rfl) ⟨3677328, by rfl⟩ : syracuseStep 39224837 = 7354657) B7354657
theorem B26149891 : Blo 1957435 26149891 := bstep (se 1 (by rfl) ⟨19612418, by rfl⟩ : syracuseStep 26149891 = 39224837) B39224837
theorem B34866521 : Blo 1957435 34866521 := bstep (se 2 (by rfl) ⟨13074945, by rfl⟩ : syracuseStep 34866521 = 26149891) B26149891
theorem B23244347 : Blo 1957435 23244347 := bstep (se 1 (by rfl) ⟨17433260, by rfl⟩ : syracuseStep 23244347 = 34866521) B34866521
theorem B61984925 : Blo 1957435 61984925 := bstep (se 3 (by rfl) ⟨11622173, by rfl⟩ : syracuseStep 61984925 = 23244347) B23244347
theorem B41323283 : Blo 1957435 41323283 := bstep (se 1 (by rfl) ⟨30992462, by rfl⟩ : syracuseStep 41323283 = 61984925) B61984925
theorem B27548855 : Blo 1957435 27548855 := bstep (se 1 (by rfl) ⟨20661641, by rfl⟩ : syracuseStep 27548855 = 41323283) B41323283
theorem B18365903 : Blo 1957435 18365903 := bstep (se 1 (by rfl) ⟨13774427, by rfl⟩ : syracuseStep 18365903 = 27548855) B27548855
theorem B12243935 : Blo 1957435 12243935 := bstep (se 1 (by rfl) ⟨9182951, by rfl⟩ : syracuseStep 12243935 = 18365903) B18365903
theorem B8162623 : Blo 1957435 8162623 := bstep (se 1 (by rfl) ⟨6121967, by rfl⟩ : syracuseStep 8162623 = 12243935) B12243935
theorem B10883497 : Blo 1957435 10883497 := bstep (se 2 (by rfl) ⟨4081311, by rfl⟩ : syracuseStep 10883497 = 8162623) B8162623
theorem B14511329 : Blo 1957435 14511329 := bstep (se 2 (by rfl) ⟨5441748, by rfl⟩ : syracuseStep 14511329 = 10883497) B10883497
theorem B9674219 : Blo 1957435 9674219 := bstep (se 1 (by rfl) ⟨7255664, by rfl⟩ : syracuseStep 9674219 = 14511329) B14511329
theorem B6449479 : Blo 1957435 6449479 := bstep (se 1 (by rfl) ⟨4837109, by rfl⟩ : syracuseStep 6449479 = 9674219) B9674219
theorem B137588885 : Blo 1957435 137588885 := bstep (se 6 (by rfl) ⟨3224739, by rfl⟩ : syracuseStep 137588885 = 6449479) B6449479
theorem B91725923 : Blo 1957435 91725923 := bstep (se 1 (by rfl) ⟨68794442, by rfl⟩ : syracuseStep 91725923 = 137588885) B137588885
theorem B244602461 : Blo 1957435 244602461 := bstep (se 3 (by rfl) ⟨45862961, by rfl⟩ : syracuseStep 244602461 = 91725923) B91725923
theorem B652273229 : Blo 1957435 652273229 := bstep (se 3 (by rfl) ⟨122301230, by rfl⟩ : syracuseStep 652273229 = 244602461) B244602461
theorem B434848819 : Blo 1957435 434848819 := bstep (se 1 (by rfl) ⟨326136614, by rfl⟩ : syracuseStep 434848819 = 652273229) B652273229
theorem B579798425 : Blo 1957435 579798425 := bstep (se 2 (by rfl) ⟨217424409, by rfl⟩ : syracuseStep 579798425 = 434848819) B434848819
theorem B386532283 : Blo 1957435 386532283 := bstep (se 1 (by rfl) ⟨289899212, by rfl⟩ : syracuseStep 386532283 = 579798425) B579798425
theorem B515376377 : Blo 1957435 515376377 := bstep (se 2 (by rfl) ⟨193266141, by rfl⟩ : syracuseStep 515376377 = 386532283) B386532283
theorem B343584251 : Blo 1957435 343584251 := bstep (se 1 (by rfl) ⟨257688188, by rfl⟩ : syracuseStep 343584251 = 515376377) B515376377
theorem B229056167 : Blo 1957435 229056167 := bstep (se 1 (by rfl) ⟨171792125, by rfl⟩ : syracuseStep 229056167 = 343584251) B343584251
theorem B152704111 : Blo 1957435 152704111 := bstep (se 1 (by rfl) ⟨114528083, by rfl⟩ : syracuseStep 152704111 = 229056167) B229056167
theorem B203605481 : Blo 1957435 203605481 := bstep (se 2 (by rfl) ⟨76352055, by rfl⟩ : syracuseStep 203605481 = 152704111) B152704111
theorem B135736987 : Blo 1957435 135736987 := bstep (se 1 (by rfl) ⟨101802740, by rfl⟩ : syracuseStep 135736987 = 203605481) B203605481
theorem B180982649 : Blo 1957435 180982649 := bstep (se 2 (by rfl) ⟨67868493, by rfl⟩ : syracuseStep 180982649 = 135736987) B135736987
theorem B120655099 : Blo 1957435 120655099 := bstep (se 1 (by rfl) ⟨90491324, by rfl⟩ : syracuseStep 120655099 = 180982649) B180982649
theorem B160873465 : Blo 1957435 160873465 := bstep (se 2 (by rfl) ⟨60327549, by rfl⟩ : syracuseStep 160873465 = 120655099) B120655099
theorem B214497953 : Blo 1957435 214497953 := bstep (se 2 (by rfl) ⟨80436732, by rfl⟩ : syracuseStep 214497953 = 160873465) B160873465
theorem B142998635 : Blo 1957435 142998635 := bstep (se 1 (by rfl) ⟨107248976, by rfl⟩ : syracuseStep 142998635 = 214497953) B214497953
theorem B95332423 : Blo 1957435 95332423 := bstep (se 1 (by rfl) ⟨71499317, by rfl⟩ : syracuseStep 95332423 = 142998635) B142998635
theorem B127109897 : Blo 1957435 127109897 := bstep (se 2 (by rfl) ⟨47666211, by rfl⟩ : syracuseStep 127109897 = 95332423) B95332423
theorem B84739931 : Blo 1957435 84739931 := bstep (se 1 (by rfl) ⟨63554948, by rfl⟩ : syracuseStep 84739931 = 127109897) B127109897
theorem B56493287 : Blo 1957435 56493287 := bstep (se 1 (by rfl) ⟨42369965, by rfl⟩ : syracuseStep 56493287 = 84739931) B84739931
theorem B37662191 : Blo 1957435 37662191 := bstep (se 1 (by rfl) ⟨28246643, by rfl⟩ : syracuseStep 37662191 = 56493287) B56493287
theorem B25108127 : Blo 1957435 25108127 := bstep (se 1 (by rfl) ⟨18831095, by rfl⟩ : syracuseStep 25108127 = 37662191) B37662191
theorem B16738751 : Blo 1957435 16738751 := bstep (se 1 (by rfl) ⟨12554063, by rfl⟩ : syracuseStep 16738751 = 25108127) B25108127
theorem B11159167 : Blo 1957435 11159167 := bstep (se 1 (by rfl) ⟨8369375, by rfl⟩ : syracuseStep 11159167 = 16738751) B16738751
theorem B14878889 : Blo 1957435 14878889 := bstep (se 2 (by rfl) ⟨5579583, by rfl⟩ : syracuseStep 14878889 = 11159167) B11159167
theorem B9919259 : Blo 1957435 9919259 := bstep (se 1 (by rfl) ⟨7439444, by rfl⟩ : syracuseStep 9919259 = 14878889) B14878889
theorem B6612839 : Blo 1957435 6612839 := bstep (se 1 (by rfl) ⟨4959629, by rfl⟩ : syracuseStep 6612839 = 9919259) B9919259
theorem B4408559 : Blo 1957435 4408559 := bstep (se 1 (by rfl) ⟨3306419, by rfl⟩ : syracuseStep 4408559 = 6612839) B6612839
theorem B2939039 : Blo 1957435 2939039 := bstep (se 1 (by rfl) ⟨2204279, by rfl⟩ : syracuseStep 2939039 = 4408559) B4408559
theorem B1959359 : Blo 1957435 1959359 := bstep (se 1 (by rfl) ⟨1469519, by rfl⟩ : syracuseStep 1959359 = 2939039) B2939039
theorem B2939045 : Blo 1957435 2939045 := bbase (se 4 (by rfl) ⟨275535, by rfl⟩ : syracuseStep 2939045 = 551071) (by norm_num)
theorem B1959363 : Blo 1957435 1959363 := bstep (se 1 (by rfl) ⟨1469522, by rfl⟩ : syracuseStep 1959363 = 2939045) B2939045
theorem B2479825 : Blo 1957435 2479825 := bbase (se 2 (by rfl) ⟨929934, by rfl⟩ : syracuseStep 2479825 = 1859869) (by norm_num)
theorem B3306433 : Blo 1957435 3306433 := bstep (se 2 (by rfl) ⟨1239912, by rfl⟩ : syracuseStep 3306433 = 2479825) B2479825
theorem B4408577 : Blo 1957435 4408577 := bstep (se 2 (by rfl) ⟨1653216, by rfl⟩ : syracuseStep 4408577 = 3306433) B3306433
theorem B2939051 : Blo 1957435 2939051 := bstep (se 1 (by rfl) ⟨2204288, by rfl⟩ : syracuseStep 2939051 = 4408577) B4408577
theorem B1959367 : Blo 1957435 1959367 := bstep (se 1 (by rfl) ⟨1469525, by rfl⟩ : syracuseStep 1959367 = 2939051) B2939051
theorem B2204293 : Blo 1957435 2204293 := bbase (se 4 (by rfl) ⟨206652, by rfl⟩ : syracuseStep 2204293 = 413305) (by norm_num)
theorem B2939057 : Blo 1957435 2939057 := bstep (se 2 (by rfl) ⟨1102146, by rfl⟩ : syracuseStep 2939057 = 2204293) B2204293
theorem B1959371 : Blo 1957435 1959371 := bstep (se 1 (by rfl) ⟨1469528, by rfl⟩ : syracuseStep 1959371 = 2939057) B2939057
theorem B3530861 : Blo 1957435 3530861 := bbase (se 3 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 3530861 = 1324073) (by norm_num)
theorem B2353907 : Blo 1957435 2353907 := bstep (se 1 (by rfl) ⟨1765430, by rfl⟩ : syracuseStep 2353907 = 3530861) B3530861
theorem B6277085 : Blo 1957435 6277085 := bstep (se 3 (by rfl) ⟨1176953, by rfl⟩ : syracuseStep 6277085 = 2353907) B2353907
theorem B4184723 : Blo 1957435 4184723 := bstep (se 1 (by rfl) ⟨3138542, by rfl⟩ : syracuseStep 4184723 = 6277085) B6277085
theorem B2789815 : Blo 1957435 2789815 := bstep (se 1 (by rfl) ⟨2092361, by rfl⟩ : syracuseStep 2789815 = 4184723) B4184723
theorem B3719753 : Blo 1957435 3719753 := bstep (se 2 (by rfl) ⟨1394907, by rfl⟩ : syracuseStep 3719753 = 2789815) B2789815
theorem B2479835 : Blo 1957435 2479835 := bstep (se 1 (by rfl) ⟨1859876, by rfl⟩ : syracuseStep 2479835 = 3719753) B3719753
theorem B6612893 : Blo 1957435 6612893 := bstep (se 3 (by rfl) ⟨1239917, by rfl⟩ : syracuseStep 6612893 = 2479835) B2479835
theorem B4408595 : Blo 1957435 4408595 := bstep (se 1 (by rfl) ⟨3306446, by rfl⟩ : syracuseStep 4408595 = 6612893) B6612893
theorem B2939063 : Blo 1957435 2939063 := bstep (se 1 (by rfl) ⟨2204297, by rfl⟩ : syracuseStep 2939063 = 4408595) B4408595
theorem B1959375 : Blo 1957435 1959375 := bstep (se 1 (by rfl) ⟨1469531, by rfl⟩ : syracuseStep 1959375 = 2939063) B2939063
theorem B2939069 : Blo 1957435 2939069 := bbase (se 3 (by rfl) ⟨551075, by rfl⟩ : syracuseStep 2939069 = 1102151) (by norm_num)
theorem B1959379 : Blo 1957435 1959379 := bstep (se 1 (by rfl) ⟨1469534, by rfl⟩ : syracuseStep 1959379 = 2939069) B2939069
theorem B4408613 : Blo 1957435 4408613 := bbase (se 4 (by rfl) ⟨413307, by rfl⟩ : syracuseStep 4408613 = 826615) (by norm_num)
theorem B2939075 : Blo 1957435 2939075 := bstep (se 1 (by rfl) ⟨2204306, by rfl⟩ : syracuseStep 2939075 = 4408613) B4408613
theorem B1959383 : Blo 1957435 1959383 := bstep (se 1 (by rfl) ⟨1469537, by rfl⟩ : syracuseStep 1959383 = 2939075) B2939075
theorem B4959701 : Blo 1957435 4959701 := bbase (se 7 (by rfl) ⟨58121, by rfl⟩ : syracuseStep 4959701 = 116243) (by norm_num)
theorem B3306467 : Blo 1957435 3306467 := bstep (se 1 (by rfl) ⟨2479850, by rfl⟩ : syracuseStep 3306467 = 4959701) B4959701
theorem B2204311 : Blo 1957435 2204311 := bstep (se 1 (by rfl) ⟨1653233, by rfl⟩ : syracuseStep 2204311 = 3306467) B3306467
theorem B2939081 : Blo 1957435 2939081 := bstep (se 2 (by rfl) ⟨1102155, by rfl⟩ : syracuseStep 2939081 = 2204311) B2204311
theorem B1959387 : Blo 1957435 1959387 := bstep (se 1 (by rfl) ⟨1469540, by rfl⟩ : syracuseStep 1959387 = 2939081) B2939081
theorem B1986125 : Blo 1957435 1986125 := bbase (se 3 (by rfl) ⟨372398, by rfl⟩ : syracuseStep 1986125 = 744797) (by norm_num)
theorem B21185333 : Blo 1957435 21185333 := bstep (se 5 (by rfl) ⟨993062, by rfl⟩ : syracuseStep 21185333 = 1986125) B1986125
theorem B14123555 : Blo 1957435 14123555 := bstep (se 1 (by rfl) ⟨10592666, by rfl⟩ : syracuseStep 14123555 = 21185333) B21185333
theorem B9415703 : Blo 1957435 9415703 := bstep (se 1 (by rfl) ⟨7061777, by rfl⟩ : syracuseStep 9415703 = 14123555) B14123555
theorem B6277135 : Blo 1957435 6277135 := bstep (se 1 (by rfl) ⟨4707851, by rfl⟩ : syracuseStep 6277135 = 9415703) B9415703
theorem B8369513 : Blo 1957435 8369513 := bstep (se 2 (by rfl) ⟨3138567, by rfl⟩ : syracuseStep 8369513 = 6277135) B6277135
theorem B5579675 : Blo 1957435 5579675 := bstep (se 1 (by rfl) ⟨4184756, by rfl⟩ : syracuseStep 5579675 = 8369513) B8369513
theorem B3719783 : Blo 1957435 3719783 := bstep (se 1 (by rfl) ⟨2789837, by rfl⟩ : syracuseStep 3719783 = 5579675) B5579675
theorem B9919421 : Blo 1957435 9919421 := bstep (se 3 (by rfl) ⟨1859891, by rfl⟩ : syracuseStep 9919421 = 3719783) B3719783
theorem B6612947 : Blo 1957435 6612947 := bstep (se 1 (by rfl) ⟨4959710, by rfl⟩ : syracuseStep 6612947 = 9919421) B9919421
theorem B4408631 : Blo 1957435 4408631 := bstep (se 1 (by rfl) ⟨3306473, by rfl⟩ : syracuseStep 4408631 = 6612947) B6612947
theorem B2939087 : Blo 1957435 2939087 := bstep (se 1 (by rfl) ⟨2204315, by rfl⟩ : syracuseStep 2939087 = 4408631) B4408631
theorem B1959391 : Blo 1957435 1959391 := bstep (se 1 (by rfl) ⟨1469543, by rfl⟩ : syracuseStep 1959391 = 2939087) B2939087
theorem B2939093 : Blo 1957435 2939093 := bbase (se 7 (by rfl) ⟨34442, by rfl⟩ : syracuseStep 2939093 = 68885) (by norm_num)
theorem B1959395 : Blo 1957435 1959395 := bstep (se 1 (by rfl) ⟨1469546, by rfl⟩ : syracuseStep 1959395 = 2939093) B2939093
theorem B3138581 : Blo 1957435 3138581 := bbase (se 6 (by rfl) ⟨73560, by rfl⟩ : syracuseStep 3138581 = 147121) (by norm_num)
theorem B2092387 : Blo 1957435 2092387 := bstep (se 1 (by rfl) ⟨1569290, by rfl⟩ : syracuseStep 2092387 = 3138581) B3138581
theorem B2789849 : Blo 1957435 2789849 := bstep (se 2 (by rfl) ⟨1046193, by rfl⟩ : syracuseStep 2789849 = 2092387) B2092387
theorem B7439597 : Blo 1957435 7439597 := bstep (se 3 (by rfl) ⟨1394924, by rfl⟩ : syracuseStep 7439597 = 2789849) B2789849
theorem B4959731 : Blo 1957435 4959731 := bstep (se 1 (by rfl) ⟨3719798, by rfl⟩ : syracuseStep 4959731 = 7439597) B7439597
theorem B3306487 : Blo 1957435 3306487 := bstep (se 1 (by rfl) ⟨2479865, by rfl⟩ : syracuseStep 3306487 = 4959731) B4959731
theorem B4408649 : Blo 1957435 4408649 := bstep (se 2 (by rfl) ⟨1653243, by rfl⟩ : syracuseStep 4408649 = 3306487) B3306487
theorem B2939099 : Blo 1957435 2939099 := bstep (se 1 (by rfl) ⟨2204324, by rfl⟩ : syracuseStep 2939099 = 4408649) B4408649
theorem B1959399 : Blo 1957435 1959399 := bstep (se 1 (by rfl) ⟨1469549, by rfl⟩ : syracuseStep 1959399 = 2939099) B2939099
theorem B2204329 : Blo 1957435 2204329 := bbase (se 2 (by rfl) ⟨826623, by rfl⟩ : syracuseStep 2204329 = 1653247) (by norm_num)
theorem B2939105 : Blo 1957435 2939105 := bstep (se 2 (by rfl) ⟨1102164, by rfl⟩ : syracuseStep 2939105 = 2204329) B2204329
theorem B1959403 : Blo 1957435 1959403 := bstep (se 1 (by rfl) ⟨1469552, by rfl⟩ : syracuseStep 1959403 = 2939105) B2939105
theorem B2353945 : Blo 1957435 2353945 := bbase (se 2 (by rfl) ⟨882729, by rfl⟩ : syracuseStep 2353945 = 1765459) (by norm_num)
theorem B3138593 : Blo 1957435 3138593 := bstep (se 2 (by rfl) ⟨1176972, by rfl⟩ : syracuseStep 3138593 = 2353945) B2353945
theorem B8369581 : Blo 1957435 8369581 := bstep (se 3 (by rfl) ⟨1569296, by rfl⟩ : syracuseStep 8369581 = 3138593) B3138593
theorem B11159441 : Blo 1957435 11159441 := bstep (se 2 (by rfl) ⟨4184790, by rfl⟩ : syracuseStep 11159441 = 8369581) B8369581
theorem B7439627 : Blo 1957435 7439627 := bstep (se 1 (by rfl) ⟨5579720, by rfl⟩ : syracuseStep 7439627 = 11159441) B11159441
theorem B4959751 : Blo 1957435 4959751 := bstep (se 1 (by rfl) ⟨3719813, by rfl⟩ : syracuseStep 4959751 = 7439627) B7439627
theorem B6613001 : Blo 1957435 6613001 := bstep (se 2 (by rfl) ⟨2479875, by rfl⟩ : syracuseStep 6613001 = 4959751) B4959751
theorem B4408667 : Blo 1957435 4408667 := bstep (se 1 (by rfl) ⟨3306500, by rfl⟩ : syracuseStep 4408667 = 6613001) B6613001
theorem B2939111 : Blo 1957435 2939111 := bstep (se 1 (by rfl) ⟨2204333, by rfl⟩ : syracuseStep 2939111 = 4408667) B4408667
theorem B1959407 : Blo 1957435 1959407 := bstep (se 1 (by rfl) ⟨1469555, by rfl⟩ : syracuseStep 1959407 = 2939111) B2939111
theorem B2939117 : Blo 1957435 2939117 := bbase (se 3 (by rfl) ⟨551084, by rfl⟩ : syracuseStep 2939117 = 1102169) (by norm_num)
theorem B1959411 : Blo 1957435 1959411 := bstep (se 1 (by rfl) ⟨1469558, by rfl⟩ : syracuseStep 1959411 = 2939117) B2939117
theorem B4408685 : Blo 1957435 4408685 := bbase (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) (by norm_num)
theorem B2939123 : Blo 1957435 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B1959415 : Blo 1957435 1959415 := bstep (se 1 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 1959415 = 2939123) B2939123
theorem B3719837 : Blo 1957435 3719837 := bbase (se 3 (by rfl) ⟨697469, by rfl⟩ : syracuseStep 3719837 = 1394939) (by norm_num)
theorem B2479891 : Blo 1957435 2479891 := bstep (se 1 (by rfl) ⟨1859918, by rfl⟩ : syracuseStep 2479891 = 3719837) B3719837
theorem B3306521 : Blo 1957435 3306521 := bstep (se 2 (by rfl) ⟨1239945, by rfl⟩ : syracuseStep 3306521 = 2479891) B2479891
theorem B2204347 : Blo 1957435 2204347 := bstep (se 1 (by rfl) ⟨1653260, by rfl⟩ : syracuseStep 2204347 = 3306521) B3306521
theorem B2939129 : Blo 1957435 2939129 := bstep (se 2 (by rfl) ⟨1102173, by rfl⟩ : syracuseStep 2939129 = 2204347) B2204347
theorem B1959419 : Blo 1957435 1959419 := bstep (se 1 (by rfl) ⟨1469564, by rfl⟩ : syracuseStep 1959419 = 2939129) B2939129
theorem B4299797 : Blo 1957435 4299797 := bbase (se 6 (by rfl) ⟨100776, by rfl⟩ : syracuseStep 4299797 = 201553) (by norm_num)
theorem B2866531 : Blo 1957435 2866531 := bstep (se 1 (by rfl) ⟨2149898, by rfl⟩ : syracuseStep 2866531 = 4299797) B4299797
theorem B3822041 : Blo 1957435 3822041 := bstep (se 2 (by rfl) ⟨1433265, by rfl⟩ : syracuseStep 3822041 = 2866531) B2866531
theorem B2548027 : Blo 1957435 2548027 := bstep (se 1 (by rfl) ⟨1911020, by rfl⟩ : syracuseStep 2548027 = 3822041) B3822041
theorem B13589477 : Blo 1957435 13589477 := bstep (se 4 (by rfl) ⟨1274013, by rfl⟩ : syracuseStep 13589477 = 2548027) B2548027
theorem B9059651 : Blo 1957435 9059651 := bstep (se 1 (by rfl) ⟨6794738, by rfl⟩ : syracuseStep 9059651 = 13589477) B13589477
theorem B6039767 : Blo 1957435 6039767 := bstep (se 1 (by rfl) ⟨4529825, by rfl⟩ : syracuseStep 6039767 = 9059651) B9059651
theorem B4026511 : Blo 1957435 4026511 := bstep (se 1 (by rfl) ⟨3019883, by rfl⟩ : syracuseStep 4026511 = 6039767) B6039767
theorem B5368681 : Blo 1957435 5368681 := bstep (se 2 (by rfl) ⟨2013255, by rfl⟩ : syracuseStep 5368681 = 4026511) B4026511
theorem B7158241 : Blo 1957435 7158241 := bstep (se 2 (by rfl) ⟨2684340, by rfl⟩ : syracuseStep 7158241 = 5368681) B5368681
theorem B9544321 : Blo 1957435 9544321 := bstep (se 2 (by rfl) ⟨3579120, by rfl⟩ : syracuseStep 9544321 = 7158241) B7158241
theorem B12725761 : Blo 1957435 12725761 := bstep (se 2 (by rfl) ⟨4772160, by rfl⟩ : syracuseStep 12725761 = 9544321) B9544321
theorem B16967681 : Blo 1957435 16967681 := bstep (se 2 (by rfl) ⟨6362880, by rfl⟩ : syracuseStep 16967681 = 12725761) B12725761
theorem B11311787 : Blo 1957435 11311787 := bstep (se 1 (by rfl) ⟨8483840, by rfl⟩ : syracuseStep 11311787 = 16967681) B16967681
theorem B7541191 : Blo 1957435 7541191 := bstep (se 1 (by rfl) ⟨5655893, by rfl⟩ : syracuseStep 7541191 = 11311787) B11311787
theorem B10054921 : Blo 1957435 10054921 := bstep (se 2 (by rfl) ⟨3770595, by rfl⟩ : syracuseStep 10054921 = 7541191) B7541191
theorem B13406561 : Blo 1957435 13406561 := bstep (se 2 (by rfl) ⟨5027460, by rfl⟩ : syracuseStep 13406561 = 10054921) B10054921
theorem B8937707 : Blo 1957435 8937707 := bstep (se 1 (by rfl) ⟨6703280, by rfl⟩ : syracuseStep 8937707 = 13406561) B13406561
theorem B23833885 : Blo 1957435 23833885 := bstep (se 3 (by rfl) ⟨4468853, by rfl⟩ : syracuseStep 23833885 = 8937707) B8937707
theorem B31778513 : Blo 1957435 31778513 := bstep (se 2 (by rfl) ⟨11916942, by rfl⟩ : syracuseStep 31778513 = 23833885) B23833885
theorem B21185675 : Blo 1957435 21185675 := bstep (se 1 (by rfl) ⟨15889256, by rfl⟩ : syracuseStep 21185675 = 31778513) B31778513
theorem B14123783 : Blo 1957435 14123783 := bstep (se 1 (by rfl) ⟨10592837, by rfl⟩ : syracuseStep 14123783 = 21185675) B21185675
theorem B9415855 : Blo 1957435 9415855 := bstep (se 1 (by rfl) ⟨7061891, by rfl⟩ : syracuseStep 9415855 = 14123783) B14123783
theorem B50217893 : Blo 1957435 50217893 := bstep (se 4 (by rfl) ⟨4707927, by rfl⟩ : syracuseStep 50217893 = 9415855) B9415855
theorem B33478595 : Blo 1957435 33478595 := bstep (se 1 (by rfl) ⟨25108946, by rfl⟩ : syracuseStep 33478595 = 50217893) B50217893
theorem B22319063 : Blo 1957435 22319063 := bstep (se 1 (by rfl) ⟨16739297, by rfl⟩ : syracuseStep 22319063 = 33478595) B33478595
theorem B14879375 : Blo 1957435 14879375 := bstep (se 1 (by rfl) ⟨11159531, by rfl⟩ : syracuseStep 14879375 = 22319063) B22319063
theorem B9919583 : Blo 1957435 9919583 := bstep (se 1 (by rfl) ⟨7439687, by rfl⟩ : syracuseStep 9919583 = 14879375) B14879375
theorem B6613055 : Blo 1957435 6613055 := bstep (se 1 (by rfl) ⟨4959791, by rfl⟩ : syracuseStep 6613055 = 9919583) B9919583
theorem B4408703 : Blo 1957435 4408703 := bstep (se 1 (by rfl) ⟨3306527, by rfl⟩ : syracuseStep 4408703 = 6613055) B6613055
theorem B2939135 : Blo 1957435 2939135 := bstep (se 1 (by rfl) ⟨2204351, by rfl⟩ : syracuseStep 2939135 = 4408703) B4408703
theorem B1959423 : Blo 1957435 1959423 := bstep (se 1 (by rfl) ⟨1469567, by rfl⟩ : syracuseStep 1959423 = 2939135) B2939135
theorem B2939141 : Blo 1957435 2939141 := bbase (se 4 (by rfl) ⟨275544, by rfl⟩ : syracuseStep 2939141 = 551089) (by norm_num)
theorem B1959427 : Blo 1957435 1959427 := bstep (se 1 (by rfl) ⟨1469570, by rfl⟩ : syracuseStep 1959427 = 2939141) B2939141
theorem B3306541 : Blo 1957435 3306541 := bbase (se 3 (by rfl) ⟨619976, by rfl⟩ : syracuseStep 3306541 = 1239953) (by norm_num)
theorem B4408721 : Blo 1957435 4408721 := bstep (se 2 (by rfl) ⟨1653270, by rfl⟩ : syracuseStep 4408721 = 3306541) B3306541
theorem B2939147 : Blo 1957435 2939147 := bstep (se 1 (by rfl) ⟨2204360, by rfl⟩ : syracuseStep 2939147 = 4408721) B4408721
theorem B1959431 : Blo 1957435 1959431 := bstep (se 1 (by rfl) ⟨1469573, by rfl⟩ : syracuseStep 1959431 = 2939147) B2939147
theorem B2204365 : Blo 1957435 2204365 := bbase (se 3 (by rfl) ⟨413318, by rfl⟩ : syracuseStep 2204365 = 826637) (by norm_num)
theorem B2939153 : Blo 1957435 2939153 := bstep (se 2 (by rfl) ⟨1102182, by rfl⟩ : syracuseStep 2939153 = 2204365) B2204365
theorem B1959435 : Blo 1957435 1959435 := bstep (se 1 (by rfl) ⟨1469576, by rfl⟩ : syracuseStep 1959435 = 2939153) B2939153
theorem C0 (j : ℕ) (h1 : 489358 ≤ j) (h2 : j ≤ 489858) : Blo 1957435 (4 * j + 3) := by
  interval_cases j
  · exact B1957435
  · exact B1957439
  · exact B1957443
  · exact B1957447
  · exact B1957451
  · exact B1957455
  · exact B1957459
  · exact B1957463
  · exact B1957467
  · exact B1957471
  · exact B1957475
  · exact B1957479
  · exact B1957483
  · exact B1957487
  · exact B1957491
  · exact B1957495
  · exact B1957499
  · exact B1957503
  · exact B1957507
  · exact B1957511
  · exact B1957515
  · exact B1957519
  · exact B1957523
  · exact B1957527
  · exact B1957531
  · exact B1957535
  · exact B1957539
  · exact B1957543
  · exact B1957547
  · exact B1957551
  · exact B1957555
  · exact B1957559
  · exact B1957563
  · exact B1957567
  · exact B1957571
  · exact B1957575
  · exact B1957579
  · exact B1957583
  · exact B1957587
  · exact B1957591
  · exact B1957595
  · exact B1957599
  · exact B1957603
  · exact B1957607
  · exact B1957611
  · exact B1957615
  · exact B1957619
  · exact B1957623
  · exact B1957627
  · exact B1957631
  · exact B1957635
  · exact B1957639
  · exact B1957643
  · exact B1957647
  · exact B1957651
  · exact B1957655
  · exact B1957659
  · exact B1957663
  · exact B1957667
  · exact B1957671
  · exact B1957675
  · exact B1957679
  · exact B1957683
  · exact B1957687
  · exact B1957691
  · exact B1957695
  · exact B1957699
  · exact B1957703
  · exact B1957707
  · exact B1957711
  · exact B1957715
  · exact B1957719
  · exact B1957723
  · exact B1957727
  · exact B1957731
  · exact B1957735
  · exact B1957739
  · exact B1957743
  · exact B1957747
  · exact B1957751
  · exact B1957755
  · exact B1957759
  · exact B1957763
  · exact B1957767
  · exact B1957771
  · exact B1957775
  · exact B1957779
  · exact B1957783
  · exact B1957787
  · exact B1957791
  · exact B1957795
  · exact B1957799
  · exact B1957803
  · exact B1957807
  · exact B1957811
  · exact B1957815
  · exact B1957819
  · exact B1957823
  · exact B1957827
  · exact B1957831
  · exact B1957835
  · exact B1957839
  · exact B1957843
  · exact B1957847
  · exact B1957851
  · exact B1957855
  · exact B1957859
  · exact B1957863
  · exact B1957867
  · exact B1957871
  · exact B1957875
  · exact B1957879
  · exact B1957883
  · exact B1957887
  · exact B1957891
  · exact B1957895
  · exact B1957899
  · exact B1957903
  · exact B1957907
  · exact B1957911
  · exact B1957915
  · exact B1957919
  · exact B1957923
  · exact B1957927
  · exact B1957931
  · exact B1957935
  · exact B1957939
  · exact B1957943
  · exact B1957947
  · exact B1957951
  · exact B1957955
  · exact B1957959
  · exact B1957963
  · exact B1957967
  · exact B1957971
  · exact B1957975
  · exact B1957979
  · exact B1957983
  · exact B1957987
  · exact B1957991
  · exact B1957995
  · exact B1957999
  · exact B1958003
  · exact B1958007
  · exact B1958011
  · exact B1958015
  · exact B1958019
  · exact B1958023
  · exact B1958027
  · exact B1958031
  · exact B1958035
  · exact B1958039
  · exact B1958043
  · exact B1958047
  · exact B1958051
  · exact B1958055
  · exact B1958059
  · exact B1958063
  · exact B1958067
  · exact B1958071
  · exact B1958075
  · exact B1958079
  · exact B1958083
  · exact B1958087
  · exact B1958091
  · exact B1958095
  · exact B1958099
  · exact B1958103
  · exact B1958107
  · exact B1958111
  · exact B1958115
  · exact B1958119
  · exact B1958123
  · exact B1958127
  · exact B1958131
  · exact B1958135
  · exact B1958139
  · exact B1958143
  · exact B1958147
  · exact B1958151
  · exact B1958155
  · exact B1958159
  · exact B1958163
  · exact B1958167
  · exact B1958171
  · exact B1958175
  · exact B1958179
  · exact B1958183
  · exact B1958187
  · exact B1958191
  · exact B1958195
  · exact B1958199
  · exact B1958203
  · exact B1958207
  · exact B1958211
  · exact B1958215
  · exact B1958219
  · exact B1958223
  · exact B1958227
  · exact B1958231
  · exact B1958235
  · exact B1958239
  · exact B1958243
  · exact B1958247
  · exact B1958251
  · exact B1958255
  · exact B1958259
  · exact B1958263
  · exact B1958267
  · exact B1958271
  · exact B1958275
  · exact B1958279
  · exact B1958283
  · exact B1958287
  · exact B1958291
  · exact B1958295
  · exact B1958299
  · exact B1958303
  · exact B1958307
  · exact B1958311
  · exact B1958315
  · exact B1958319
  · exact B1958323
  · exact B1958327
  · exact B1958331
  · exact B1958335
  · exact B1958339
  · exact B1958343
  · exact B1958347
  · exact B1958351
  · exact B1958355
  · exact B1958359
  · exact B1958363
  · exact B1958367
  · exact B1958371
  · exact B1958375
  · exact B1958379
  · exact B1958383
  · exact B1958387
  · exact B1958391
  · exact B1958395
  · exact B1958399
  · exact B1958403
  · exact B1958407
  · exact B1958411
  · exact B1958415
  · exact B1958419
  · exact B1958423
  · exact B1958427
  · exact B1958431
  · exact B1958435
  · exact B1958439
  · exact B1958443
  · exact B1958447
  · exact B1958451
  · exact B1958455
  · exact B1958459
  · exact B1958463
  · exact B1958467
  · exact B1958471
  · exact B1958475
  · exact B1958479
  · exact B1958483
  · exact B1958487
  · exact B1958491
  · exact B1958495
  · exact B1958499
  · exact B1958503
  · exact B1958507
  · exact B1958511
  · exact B1958515
  · exact B1958519
  · exact B1958523
  · exact B1958527
  · exact B1958531
  · exact B1958535
  · exact B1958539
  · exact B1958543
  · exact B1958547
  · exact B1958551
  · exact B1958555
  · exact B1958559
  · exact B1958563
  · exact B1958567
  · exact B1958571
  · exact B1958575
  · exact B1958579
  · exact B1958583
  · exact B1958587
  · exact B1958591
  · exact B1958595
  · exact B1958599
  · exact B1958603
  · exact B1958607
  · exact B1958611
  · exact B1958615
  · exact B1958619
  · exact B1958623
  · exact B1958627
  · exact B1958631
  · exact B1958635
  · exact B1958639
  · exact B1958643
  · exact B1958647
  · exact B1958651
  · exact B1958655
  · exact B1958659
  · exact B1958663
  · exact B1958667
  · exact B1958671
  · exact B1958675
  · exact B1958679
  · exact B1958683
  · exact B1958687
  · exact B1958691
  · exact B1958695
  · exact B1958699
  · exact B1958703
  · exact B1958707
  · exact B1958711
  · exact B1958715
  · exact B1958719
  · exact B1958723
  · exact B1958727
  · exact B1958731
  · exact B1958735
  · exact B1958739
  · exact B1958743
  · exact B1958747
  · exact B1958751
  · exact B1958755
  · exact B1958759
  · exact B1958763
  · exact B1958767
  · exact B1958771
  · exact B1958775
  · exact B1958779
  · exact B1958783
  · exact B1958787
  · exact B1958791
  · exact B1958795
  · exact B1958799
  · exact B1958803
  · exact B1958807
  · exact B1958811
  · exact B1958815
  · exact B1958819
  · exact B1958823
  · exact B1958827
  · exact B1958831
  · exact B1958835
  · exact B1958839
  · exact B1958843
  · exact B1958847
  · exact B1958851
  · exact B1958855
  · exact B1958859
  · exact B1958863
  · exact B1958867
  · exact B1958871
  · exact B1958875
  · exact B1958879
  · exact B1958883
  · exact B1958887
  · exact B1958891
  · exact B1958895
  · exact B1958899
  · exact B1958903
  · exact B1958907
  · exact B1958911
  · exact B1958915
  · exact B1958919
  · exact B1958923
  · exact B1958927
  · exact B1958931
  · exact B1958935
  · exact B1958939
  · exact B1958943
  · exact B1958947
  · exact B1958951
  · exact B1958955
  · exact B1958959
  · exact B1958963
  · exact B1958967
  · exact B1958971
  · exact B1958975
  · exact B1958979
  · exact B1958983
  · exact B1958987
  · exact B1958991
  · exact B1958995
  · exact B1958999
  · exact B1959003
  · exact B1959007
  · exact B1959011
  · exact B1959015
  · exact B1959019
  · exact B1959023
  · exact B1959027
  · exact B1959031
  · exact B1959035
  · exact B1959039
  · exact B1959043
  · exact B1959047
  · exact B1959051
  · exact B1959055
  · exact B1959059
  · exact B1959063
  · exact B1959067
  · exact B1959071
  · exact B1959075
  · exact B1959079
  · exact B1959083
  · exact B1959087
  · exact B1959091
  · exact B1959095
  · exact B1959099
  · exact B1959103
  · exact B1959107
  · exact B1959111
  · exact B1959115
  · exact B1959119
  · exact B1959123
  · exact B1959127
  · exact B1959131
  · exact B1959135
  · exact B1959139
  · exact B1959143
  · exact B1959147
  · exact B1959151
  · exact B1959155
  · exact B1959159
  · exact B1959163
  · exact B1959167
  · exact B1959171
  · exact B1959175
  · exact B1959179
  · exact B1959183
  · exact B1959187
  · exact B1959191
  · exact B1959195
  · exact B1959199
  · exact B1959203
  · exact B1959207
  · exact B1959211
  · exact B1959215
  · exact B1959219
  · exact B1959223
  · exact B1959227
  · exact B1959231
  · exact B1959235
  · exact B1959239
  · exact B1959243
  · exact B1959247
  · exact B1959251
  · exact B1959255
  · exact B1959259
  · exact B1959263
  · exact B1959267
  · exact B1959271
  · exact B1959275
  · exact B1959279
  · exact B1959283
  · exact B1959287
  · exact B1959291
  · exact B1959295
  · exact B1959299
  · exact B1959303
  · exact B1959307
  · exact B1959311
  · exact B1959315
  · exact B1959319
  · exact B1959323
  · exact B1959327
  · exact B1959331
  · exact B1959335
  · exact B1959339
  · exact B1959343
  · exact B1959347
  · exact B1959351
  · exact B1959355
  · exact B1959359
  · exact B1959363
  · exact B1959367
  · exact B1959371
  · exact B1959375
  · exact B1959379
  · exact B1959383
  · exact B1959387
  · exact B1959391
  · exact B1959395
  · exact B1959399
  · exact B1959403
  · exact B1959407
  · exact B1959411
  · exact B1959415
  · exact B1959419
  · exact B1959423
  · exact B1959427
  · exact B1959431
  · exact B1959435
theorem solution (m : ℕ) (hlo : 1957435 ≤ m) (hhi : m ≤ 1959435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 489358 ≤ j := by omega
    have hj2 : j ≤ 489858 := by omega
    have hb : Blo 1957435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
