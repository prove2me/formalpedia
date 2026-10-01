-- Prove2me | solution 1 for syracuse_descends_range_2061435_2063435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:37.48127+00:00
-- url     : https://prove2.me/submissions/a6c2e941-c1e7-4d0c-b658-6e8d92678512

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

theorem B2609005 : Blo 2061435 2609005 := bbase (se 3 (by rfl) ⟨489188, by rfl⟩ : syracuseStep 2609005 = 978377) (by norm_num)
theorem B3478673 : Blo 2061435 3478673 := bstep (se 2 (by rfl) ⟨1304502, by rfl⟩ : syracuseStep 3478673 = 2609005) B2609005
theorem B2319115 : Blo 2061435 2319115 := bstep (se 1 (by rfl) ⟨1739336, by rfl⟩ : syracuseStep 2319115 = 3478673) B3478673
theorem B3092153 : Blo 2061435 3092153 := bstep (se 2 (by rfl) ⟨1159557, by rfl⟩ : syracuseStep 3092153 = 2319115) B2319115
theorem B2061435 : Blo 2061435 2061435 := bstep (se 1 (by rfl) ⟨1546076, by rfl⟩ : syracuseStep 2061435 = 3092153) B3092153
theorem B9906085 : Blo 2061435 9906085 := bbase (se 4 (by rfl) ⟨928695, by rfl⟩ : syracuseStep 9906085 = 1857391) (by norm_num)
theorem B13208113 : Blo 2061435 13208113 := bstep (se 2 (by rfl) ⟨4953042, by rfl⟩ : syracuseStep 13208113 = 9906085) B9906085
theorem B17610817 : Blo 2061435 17610817 := bstep (se 2 (by rfl) ⟨6604056, by rfl⟩ : syracuseStep 17610817 = 13208113) B13208113
theorem B23481089 : Blo 2061435 23481089 := bstep (se 2 (by rfl) ⟨8805408, by rfl⟩ : syracuseStep 23481089 = 17610817) B17610817
theorem B15654059 : Blo 2061435 15654059 := bstep (se 1 (by rfl) ⟨11740544, by rfl⟩ : syracuseStep 15654059 = 23481089) B23481089
theorem B10436039 : Blo 2061435 10436039 := bstep (se 1 (by rfl) ⟨7827029, by rfl⟩ : syracuseStep 10436039 = 15654059) B15654059
theorem B6957359 : Blo 2061435 6957359 := bstep (se 1 (by rfl) ⟨5218019, by rfl⟩ : syracuseStep 6957359 = 10436039) B10436039
theorem B4638239 : Blo 2061435 4638239 := bstep (se 1 (by rfl) ⟨3478679, by rfl⟩ : syracuseStep 4638239 = 6957359) B6957359
theorem B3092159 : Blo 2061435 3092159 := bstep (se 1 (by rfl) ⟨2319119, by rfl⟩ : syracuseStep 3092159 = 4638239) B4638239
theorem B2061439 : Blo 2061435 2061439 := bstep (se 1 (by rfl) ⟨1546079, by rfl⟩ : syracuseStep 2061439 = 3092159) B3092159
theorem B3092165 : Blo 2061435 3092165 := bbase (se 4 (by rfl) ⟨289890, by rfl⟩ : syracuseStep 3092165 = 579781) (by norm_num)
theorem B2061443 : Blo 2061435 2061443 := bstep (se 1 (by rfl) ⟨1546082, by rfl⟩ : syracuseStep 2061443 = 3092165) B3092165
theorem B3478693 : Blo 2061435 3478693 := bbase (se 4 (by rfl) ⟨326127, by rfl⟩ : syracuseStep 3478693 = 652255) (by norm_num)
theorem B4638257 : Blo 2061435 4638257 := bstep (se 2 (by rfl) ⟨1739346, by rfl⟩ : syracuseStep 4638257 = 3478693) B3478693
theorem B3092171 : Blo 2061435 3092171 := bstep (se 1 (by rfl) ⟨2319128, by rfl⟩ : syracuseStep 3092171 = 4638257) B4638257
theorem B2061447 : Blo 2061435 2061447 := bstep (se 1 (by rfl) ⟨1546085, by rfl⟩ : syracuseStep 2061447 = 3092171) B3092171
theorem B2319133 : Blo 2061435 2319133 := bbase (se 3 (by rfl) ⟨434837, by rfl⟩ : syracuseStep 2319133 = 869675) (by norm_num)
theorem B3092177 : Blo 2061435 3092177 := bstep (se 2 (by rfl) ⟨1159566, by rfl⟩ : syracuseStep 3092177 = 2319133) B2319133
theorem B2061451 : Blo 2061435 2061451 := bstep (se 1 (by rfl) ⟨1546088, by rfl⟩ : syracuseStep 2061451 = 3092177) B3092177
theorem B6957413 : Blo 2061435 6957413 := bbase (se 4 (by rfl) ⟨652257, by rfl⟩ : syracuseStep 6957413 = 1304515) (by norm_num)
theorem B4638275 : Blo 2061435 4638275 := bstep (se 1 (by rfl) ⟨3478706, by rfl⟩ : syracuseStep 4638275 = 6957413) B6957413
theorem B3092183 : Blo 2061435 3092183 := bstep (se 1 (by rfl) ⟨2319137, by rfl⟩ : syracuseStep 3092183 = 4638275) B4638275
theorem B2061455 : Blo 2061435 2061455 := bstep (se 1 (by rfl) ⟨1546091, by rfl⟩ : syracuseStep 2061455 = 3092183) B3092183
theorem B3092189 : Blo 2061435 3092189 := bbase (se 3 (by rfl) ⟨579785, by rfl⟩ : syracuseStep 3092189 = 1159571) (by norm_num)
theorem B2061459 : Blo 2061435 2061459 := bstep (se 1 (by rfl) ⟨1546094, by rfl⟩ : syracuseStep 2061459 = 3092189) B3092189
theorem B4638293 : Blo 2061435 4638293 := bbase (se 8 (by rfl) ⟨27177, by rfl⟩ : syracuseStep 4638293 = 54355) (by norm_num)
theorem B3092195 : Blo 2061435 3092195 := bstep (se 1 (by rfl) ⟨2319146, by rfl⟩ : syracuseStep 3092195 = 4638293) B4638293
theorem B2061463 : Blo 2061435 2061463 := bstep (se 1 (by rfl) ⟨1546097, by rfl⟩ : syracuseStep 2061463 = 3092195) B3092195
theorem B4402765 : Blo 2061435 4402765 := bbase (se 3 (by rfl) ⟨825518, by rfl⟩ : syracuseStep 4402765 = 1651037) (by norm_num)
theorem B5870353 : Blo 2061435 5870353 := bstep (se 2 (by rfl) ⟨2201382, by rfl⟩ : syracuseStep 5870353 = 4402765) B4402765
theorem B7827137 : Blo 2061435 7827137 := bstep (se 2 (by rfl) ⟨2935176, by rfl⟩ : syracuseStep 7827137 = 5870353) B5870353
theorem B5218091 : Blo 2061435 5218091 := bstep (se 1 (by rfl) ⟨3913568, by rfl⟩ : syracuseStep 5218091 = 7827137) B7827137
theorem B3478727 : Blo 2061435 3478727 := bstep (se 1 (by rfl) ⟨2609045, by rfl⟩ : syracuseStep 3478727 = 5218091) B5218091
theorem B2319151 : Blo 2061435 2319151 := bstep (se 1 (by rfl) ⟨1739363, by rfl⟩ : syracuseStep 2319151 = 3478727) B3478727
theorem B3092201 : Blo 2061435 3092201 := bstep (se 2 (by rfl) ⟨1159575, by rfl⟩ : syracuseStep 3092201 = 2319151) B2319151
theorem B2061467 : Blo 2061435 2061467 := bstep (se 1 (by rfl) ⟨1546100, by rfl⟩ : syracuseStep 2061467 = 3092201) B3092201
theorem B67779413 : Blo 2061435 67779413 := bbase (se 9 (by rfl) ⟨198572, by rfl⟩ : syracuseStep 67779413 = 397145) (by norm_num)
theorem B45186275 : Blo 2061435 45186275 := bstep (se 1 (by rfl) ⟨33889706, by rfl⟩ : syracuseStep 45186275 = 67779413) B67779413
theorem B30124183 : Blo 2061435 30124183 := bstep (se 1 (by rfl) ⟨22593137, by rfl⟩ : syracuseStep 30124183 = 45186275) B45186275
theorem B40165577 : Blo 2061435 40165577 := bstep (se 2 (by rfl) ⟨15062091, by rfl⟩ : syracuseStep 40165577 = 30124183) B30124183
theorem B26777051 : Blo 2061435 26777051 := bstep (se 1 (by rfl) ⟨20082788, by rfl⟩ : syracuseStep 26777051 = 40165577) B40165577
theorem B17851367 : Blo 2061435 17851367 := bstep (se 1 (by rfl) ⟨13388525, by rfl⟩ : syracuseStep 17851367 = 26777051) B26777051
theorem B47603645 : Blo 2061435 47603645 := bstep (se 3 (by rfl) ⟨8925683, by rfl⟩ : syracuseStep 47603645 = 17851367) B17851367
theorem B31735763 : Blo 2061435 31735763 := bstep (se 1 (by rfl) ⟨23801822, by rfl⟩ : syracuseStep 31735763 = 47603645) B47603645
theorem B21157175 : Blo 2061435 21157175 := bstep (se 1 (by rfl) ⟨15867881, by rfl⟩ : syracuseStep 21157175 = 31735763) B31735763
theorem B14104783 : Blo 2061435 14104783 := bstep (se 1 (by rfl) ⟨10578587, by rfl⟩ : syracuseStep 14104783 = 21157175) B21157175
theorem B75225509 : Blo 2061435 75225509 := bstep (se 4 (by rfl) ⟨7052391, by rfl⟩ : syracuseStep 75225509 = 14104783) B14104783
theorem B50150339 : Blo 2061435 50150339 := bstep (se 1 (by rfl) ⟨37612754, by rfl⟩ : syracuseStep 50150339 = 75225509) B75225509
theorem B33433559 : Blo 2061435 33433559 := bstep (se 1 (by rfl) ⟨25075169, by rfl⟩ : syracuseStep 33433559 = 50150339) B50150339
theorem B22289039 : Blo 2061435 22289039 := bstep (se 1 (by rfl) ⟨16716779, by rfl⟩ : syracuseStep 22289039 = 33433559) B33433559
theorem B14859359 : Blo 2061435 14859359 := bstep (se 1 (by rfl) ⟨11144519, by rfl⟩ : syracuseStep 14859359 = 22289039) B22289039
theorem B9906239 : Blo 2061435 9906239 := bstep (se 1 (by rfl) ⟨7429679, by rfl⟩ : syracuseStep 9906239 = 14859359) B14859359
theorem B26416637 : Blo 2061435 26416637 := bstep (se 3 (by rfl) ⟨4953119, by rfl⟩ : syracuseStep 26416637 = 9906239) B9906239
theorem B17611091 : Blo 2061435 17611091 := bstep (se 1 (by rfl) ⟨13208318, by rfl⟩ : syracuseStep 17611091 = 26416637) B26416637
theorem B11740727 : Blo 2061435 11740727 := bstep (se 1 (by rfl) ⟨8805545, by rfl⟩ : syracuseStep 11740727 = 17611091) B17611091
theorem B7827151 : Blo 2061435 7827151 := bstep (se 1 (by rfl) ⟨5870363, by rfl⟩ : syracuseStep 7827151 = 11740727) B11740727
theorem B10436201 : Blo 2061435 10436201 := bstep (se 2 (by rfl) ⟨3913575, by rfl⟩ : syracuseStep 10436201 = 7827151) B7827151
theorem B6957467 : Blo 2061435 6957467 := bstep (se 1 (by rfl) ⟨5218100, by rfl⟩ : syracuseStep 6957467 = 10436201) B10436201
theorem B4638311 : Blo 2061435 4638311 := bstep (se 1 (by rfl) ⟨3478733, by rfl⟩ : syracuseStep 4638311 = 6957467) B6957467
theorem B3092207 : Blo 2061435 3092207 := bstep (se 1 (by rfl) ⟨2319155, by rfl⟩ : syracuseStep 3092207 = 4638311) B4638311
theorem B2061471 : Blo 2061435 2061471 := bstep (se 1 (by rfl) ⟨1546103, by rfl⟩ : syracuseStep 2061471 = 3092207) B3092207
theorem B3092213 : Blo 2061435 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B2061475 : Blo 2061435 2061475 := bstep (se 1 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 2061475 = 3092213) B3092213
theorem B3302093 : Blo 2061435 3302093 := bbase (se 3 (by rfl) ⟨619142, by rfl⟩ : syracuseStep 3302093 = 1238285) (by norm_num)
theorem B8805581 : Blo 2061435 8805581 := bstep (se 3 (by rfl) ⟨1651046, by rfl⟩ : syracuseStep 8805581 = 3302093) B3302093
theorem B5870387 : Blo 2061435 5870387 := bstep (se 1 (by rfl) ⟨4402790, by rfl⟩ : syracuseStep 5870387 = 8805581) B8805581
theorem B3913591 : Blo 2061435 3913591 := bstep (se 1 (by rfl) ⟨2935193, by rfl⟩ : syracuseStep 3913591 = 5870387) B5870387
theorem B5218121 : Blo 2061435 5218121 := bstep (se 2 (by rfl) ⟨1956795, by rfl⟩ : syracuseStep 5218121 = 3913591) B3913591
theorem B3478747 : Blo 2061435 3478747 := bstep (se 1 (by rfl) ⟨2609060, by rfl⟩ : syracuseStep 3478747 = 5218121) B5218121
theorem B4638329 : Blo 2061435 4638329 := bstep (se 2 (by rfl) ⟨1739373, by rfl⟩ : syracuseStep 4638329 = 3478747) B3478747
theorem B3092219 : Blo 2061435 3092219 := bstep (se 1 (by rfl) ⟨2319164, by rfl⟩ : syracuseStep 3092219 = 4638329) B4638329
theorem B2061479 : Blo 2061435 2061479 := bstep (se 1 (by rfl) ⟨1546109, by rfl⟩ : syracuseStep 2061479 = 3092219) B3092219
theorem B2319169 : Blo 2061435 2319169 := bbase (se 2 (by rfl) ⟨869688, by rfl⟩ : syracuseStep 2319169 = 1739377) (by norm_num)
theorem B3092225 : Blo 2061435 3092225 := bstep (se 2 (by rfl) ⟨1159584, by rfl⟩ : syracuseStep 3092225 = 2319169) B2319169
theorem B2061483 : Blo 2061435 2061483 := bstep (se 1 (by rfl) ⟨1546112, by rfl⟩ : syracuseStep 2061483 = 3092225) B3092225
theorem B5218141 : Blo 2061435 5218141 := bbase (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) (by norm_num)
theorem B6957521 : Blo 2061435 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B4638347 : Blo 2061435 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B3092231 : Blo 2061435 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B2061487 : Blo 2061435 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B3092237 : Blo 2061435 3092237 := bbase (se 3 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 3092237 = 1159589) (by norm_num)
theorem B2061491 : Blo 2061435 2061491 := bstep (se 1 (by rfl) ⟨1546118, by rfl⟩ : syracuseStep 2061491 = 3092237) B3092237
theorem B4638365 : Blo 2061435 4638365 := bbase (se 3 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 4638365 = 1739387) (by norm_num)
theorem B3092243 : Blo 2061435 3092243 := bstep (se 1 (by rfl) ⟨2319182, by rfl⟩ : syracuseStep 3092243 = 4638365) B4638365
theorem B2061495 : Blo 2061435 2061495 := bstep (se 1 (by rfl) ⟨1546121, by rfl⟩ : syracuseStep 2061495 = 3092243) B3092243
theorem B3478781 : Blo 2061435 3478781 := bbase (se 3 (by rfl) ⟨652271, by rfl⟩ : syracuseStep 3478781 = 1304543) (by norm_num)
theorem B2319187 : Blo 2061435 2319187 := bstep (se 1 (by rfl) ⟨1739390, by rfl⟩ : syracuseStep 2319187 = 3478781) B3478781
theorem B3092249 : Blo 2061435 3092249 := bstep (se 2 (by rfl) ⟨1159593, by rfl⟩ : syracuseStep 3092249 = 2319187) B2319187
theorem B2061499 : Blo 2061435 2061499 := bstep (se 1 (by rfl) ⟨1546124, by rfl⟩ : syracuseStep 2061499 = 3092249) B3092249
theorem B4953197 : Blo 2061435 4953197 := bbase (se 3 (by rfl) ⟨928724, by rfl⟩ : syracuseStep 4953197 = 1857449) (by norm_num)
theorem B3302131 : Blo 2061435 3302131 := bstep (se 1 (by rfl) ⟨2476598, by rfl⟩ : syracuseStep 3302131 = 4953197) B4953197
theorem B4402841 : Blo 2061435 4402841 := bstep (se 2 (by rfl) ⟨1651065, by rfl⟩ : syracuseStep 4402841 = 3302131) B3302131
theorem B11740909 : Blo 2061435 11740909 := bstep (se 3 (by rfl) ⟨2201420, by rfl⟩ : syracuseStep 11740909 = 4402841) B4402841
theorem B15654545 : Blo 2061435 15654545 := bstep (se 2 (by rfl) ⟨5870454, by rfl⟩ : syracuseStep 15654545 = 11740909) B11740909
theorem B10436363 : Blo 2061435 10436363 := bstep (se 1 (by rfl) ⟨7827272, by rfl⟩ : syracuseStep 10436363 = 15654545) B15654545
theorem B6957575 : Blo 2061435 6957575 := bstep (se 1 (by rfl) ⟨5218181, by rfl⟩ : syracuseStep 6957575 = 10436363) B10436363
theorem B4638383 : Blo 2061435 4638383 := bstep (se 1 (by rfl) ⟨3478787, by rfl⟩ : syracuseStep 4638383 = 6957575) B6957575
theorem B3092255 : Blo 2061435 3092255 := bstep (se 1 (by rfl) ⟨2319191, by rfl⟩ : syracuseStep 3092255 = 4638383) B4638383
theorem B2061503 : Blo 2061435 2061503 := bstep (se 1 (by rfl) ⟨1546127, by rfl⟩ : syracuseStep 2061503 = 3092255) B3092255
theorem B3092261 : Blo 2061435 3092261 := bbase (se 4 (by rfl) ⟨289899, by rfl⟩ : syracuseStep 3092261 = 579799) (by norm_num)
theorem B2061507 : Blo 2061435 2061507 := bstep (se 1 (by rfl) ⟨1546130, by rfl⟩ : syracuseStep 2061507 = 3092261) B3092261
theorem B2609101 : Blo 2061435 2609101 := bbase (se 3 (by rfl) ⟨489206, by rfl⟩ : syracuseStep 2609101 = 978413) (by norm_num)
theorem B3478801 : Blo 2061435 3478801 := bstep (se 2 (by rfl) ⟨1304550, by rfl⟩ : syracuseStep 3478801 = 2609101) B2609101
theorem B4638401 : Blo 2061435 4638401 := bstep (se 2 (by rfl) ⟨1739400, by rfl⟩ : syracuseStep 4638401 = 3478801) B3478801
theorem B3092267 : Blo 2061435 3092267 := bstep (se 1 (by rfl) ⟨2319200, by rfl⟩ : syracuseStep 3092267 = 4638401) B4638401
theorem B2061511 : Blo 2061435 2061511 := bstep (se 1 (by rfl) ⟨1546133, by rfl⟩ : syracuseStep 2061511 = 3092267) B3092267
theorem B2319205 : Blo 2061435 2319205 := bbase (se 4 (by rfl) ⟨217425, by rfl⟩ : syracuseStep 2319205 = 434851) (by norm_num)
theorem B3092273 : Blo 2061435 3092273 := bstep (se 2 (by rfl) ⟨1159602, by rfl⟩ : syracuseStep 3092273 = 2319205) B2319205
theorem B2061515 : Blo 2061435 2061515 := bstep (se 1 (by rfl) ⟨1546136, by rfl⟩ : syracuseStep 2061515 = 3092273) B3092273
theorem B5870501 : Blo 2061435 5870501 := bbase (se 4 (by rfl) ⟨550359, by rfl⟩ : syracuseStep 5870501 = 1100719) (by norm_num)
theorem B3913667 : Blo 2061435 3913667 := bstep (se 1 (by rfl) ⟨2935250, by rfl⟩ : syracuseStep 3913667 = 5870501) B5870501
theorem B2609111 : Blo 2061435 2609111 := bstep (se 1 (by rfl) ⟨1956833, by rfl⟩ : syracuseStep 2609111 = 3913667) B3913667
theorem B6957629 : Blo 2061435 6957629 := bstep (se 3 (by rfl) ⟨1304555, by rfl⟩ : syracuseStep 6957629 = 2609111) B2609111
theorem B4638419 : Blo 2061435 4638419 := bstep (se 1 (by rfl) ⟨3478814, by rfl⟩ : syracuseStep 4638419 = 6957629) B6957629
theorem B3092279 : Blo 2061435 3092279 := bstep (se 1 (by rfl) ⟨2319209, by rfl⟩ : syracuseStep 3092279 = 4638419) B4638419
theorem B2061519 : Blo 2061435 2061519 := bstep (se 1 (by rfl) ⟨1546139, by rfl⟩ : syracuseStep 2061519 = 3092279) B3092279
theorem B3092285 : Blo 2061435 3092285 := bbase (se 3 (by rfl) ⟨579803, by rfl⟩ : syracuseStep 3092285 = 1159607) (by norm_num)
theorem B2061523 : Blo 2061435 2061523 := bstep (se 1 (by rfl) ⟨1546142, by rfl⟩ : syracuseStep 2061523 = 3092285) B3092285
theorem B4638437 : Blo 2061435 4638437 := bbase (se 4 (by rfl) ⟨434853, by rfl⟩ : syracuseStep 4638437 = 869707) (by norm_num)
theorem B3092291 : Blo 2061435 3092291 := bstep (se 1 (by rfl) ⟨2319218, by rfl⟩ : syracuseStep 3092291 = 4638437) B4638437
theorem B2061527 : Blo 2061435 2061527 := bstep (se 1 (by rfl) ⟨1546145, by rfl⟩ : syracuseStep 2061527 = 3092291) B3092291
theorem B5218253 : Blo 2061435 5218253 := bbase (se 3 (by rfl) ⟨978422, by rfl⟩ : syracuseStep 5218253 = 1956845) (by norm_num)
theorem B3478835 : Blo 2061435 3478835 := bstep (se 1 (by rfl) ⟨2609126, by rfl⟩ : syracuseStep 3478835 = 5218253) B5218253
theorem B2319223 : Blo 2061435 2319223 := bstep (se 1 (by rfl) ⟨1739417, by rfl⟩ : syracuseStep 2319223 = 3478835) B3478835
theorem B3092297 : Blo 2061435 3092297 := bstep (se 2 (by rfl) ⟨1159611, by rfl⟩ : syracuseStep 3092297 = 2319223) B2319223
theorem B2061531 : Blo 2061435 2061531 := bstep (se 1 (by rfl) ⟨1546148, by rfl⟩ : syracuseStep 2061531 = 3092297) B3092297
theorem B30125141 : Blo 2061435 30125141 := bbase (se 8 (by rfl) ⟨176514, by rfl⟩ : syracuseStep 30125141 = 353029) (by norm_num)
theorem B20083427 : Blo 2061435 20083427 := bstep (se 1 (by rfl) ⟨15062570, by rfl⟩ : syracuseStep 20083427 = 30125141) B30125141
theorem B13388951 : Blo 2061435 13388951 := bstep (se 1 (by rfl) ⟨10041713, by rfl⟩ : syracuseStep 13388951 = 20083427) B20083427
theorem B8925967 : Blo 2061435 8925967 := bstep (se 1 (by rfl) ⟨6694475, by rfl⟩ : syracuseStep 8925967 = 13388951) B13388951
theorem B11901289 : Blo 2061435 11901289 := bstep (se 2 (by rfl) ⟨4462983, by rfl⟩ : syracuseStep 11901289 = 8925967) B8925967
theorem B15868385 : Blo 2061435 15868385 := bstep (se 2 (by rfl) ⟨5950644, by rfl⟩ : syracuseStep 15868385 = 11901289) B11901289
theorem B10578923 : Blo 2061435 10578923 := bstep (se 1 (by rfl) ⟨7934192, by rfl⟩ : syracuseStep 10578923 = 15868385) B15868385
theorem B7052615 : Blo 2061435 7052615 := bstep (se 1 (by rfl) ⟨5289461, by rfl⟩ : syracuseStep 7052615 = 10578923) B10578923
theorem B4701743 : Blo 2061435 4701743 := bstep (se 1 (by rfl) ⟨3526307, by rfl⟩ : syracuseStep 4701743 = 7052615) B7052615
theorem B3134495 : Blo 2061435 3134495 := bstep (se 1 (by rfl) ⟨2350871, by rfl⟩ : syracuseStep 3134495 = 4701743) B4701743
theorem B8358653 : Blo 2061435 8358653 := bstep (se 3 (by rfl) ⟨1567247, by rfl⟩ : syracuseStep 8358653 = 3134495) B3134495
theorem B5572435 : Blo 2061435 5572435 := bstep (se 1 (by rfl) ⟨4179326, by rfl⟩ : syracuseStep 5572435 = 8358653) B8358653
theorem B7429913 : Blo 2061435 7429913 := bstep (se 2 (by rfl) ⟨2786217, by rfl⟩ : syracuseStep 7429913 = 5572435) B5572435
theorem B4953275 : Blo 2061435 4953275 := bstep (se 1 (by rfl) ⟨3714956, by rfl⟩ : syracuseStep 4953275 = 7429913) B7429913
theorem B3302183 : Blo 2061435 3302183 := bstep (se 1 (by rfl) ⟨2476637, by rfl⟩ : syracuseStep 3302183 = 4953275) B4953275
theorem B2201455 : Blo 2061435 2201455 := bstep (se 1 (by rfl) ⟨1651091, by rfl⟩ : syracuseStep 2201455 = 3302183) B3302183
theorem B2935273 : Blo 2061435 2935273 := bstep (se 2 (by rfl) ⟨1100727, by rfl⟩ : syracuseStep 2935273 = 2201455) B2201455
theorem B3913697 : Blo 2061435 3913697 := bstep (se 2 (by rfl) ⟨1467636, by rfl⟩ : syracuseStep 3913697 = 2935273) B2935273
theorem B10436525 : Blo 2061435 10436525 := bstep (se 3 (by rfl) ⟨1956848, by rfl⟩ : syracuseStep 10436525 = 3913697) B3913697
theorem B6957683 : Blo 2061435 6957683 := bstep (se 1 (by rfl) ⟨5218262, by rfl⟩ : syracuseStep 6957683 = 10436525) B10436525
theorem B4638455 : Blo 2061435 4638455 := bstep (se 1 (by rfl) ⟨3478841, by rfl⟩ : syracuseStep 4638455 = 6957683) B6957683
theorem B3092303 : Blo 2061435 3092303 := bstep (se 1 (by rfl) ⟨2319227, by rfl⟩ : syracuseStep 3092303 = 4638455) B4638455
theorem B2061535 : Blo 2061435 2061535 := bstep (se 1 (by rfl) ⟨1546151, by rfl⟩ : syracuseStep 2061535 = 3092303) B3092303
theorem B3092309 : Blo 2061435 3092309 := bbase (se 9 (by rfl) ⟨9059, by rfl⟩ : syracuseStep 3092309 = 18119) (by norm_num)
theorem B2061539 : Blo 2061435 2061539 := bstep (se 1 (by rfl) ⟨1546154, by rfl⟩ : syracuseStep 2061539 = 3092309) B3092309
theorem B3392917 : Blo 2061435 3392917 := bbase (se 6 (by rfl) ⟨79521, by rfl⟩ : syracuseStep 3392917 = 159043) (by norm_num)
theorem B18095557 : Blo 2061435 18095557 := bstep (se 4 (by rfl) ⟨1696458, by rfl⟩ : syracuseStep 18095557 = 3392917) B3392917
theorem B24127409 : Blo 2061435 24127409 := bstep (se 2 (by rfl) ⟨9047778, by rfl⟩ : syracuseStep 24127409 = 18095557) B18095557
theorem B16084939 : Blo 2061435 16084939 := bstep (se 1 (by rfl) ⟨12063704, by rfl⟩ : syracuseStep 16084939 = 24127409) B24127409
theorem B21446585 : Blo 2061435 21446585 := bstep (se 2 (by rfl) ⟨8042469, by rfl⟩ : syracuseStep 21446585 = 16084939) B16084939
theorem B14297723 : Blo 2061435 14297723 := bstep (se 1 (by rfl) ⟨10723292, by rfl⟩ : syracuseStep 14297723 = 21446585) B21446585
theorem B9531815 : Blo 2061435 9531815 := bstep (se 1 (by rfl) ⟨7148861, by rfl⟩ : syracuseStep 9531815 = 14297723) B14297723
theorem B25418173 : Blo 2061435 25418173 := bstep (se 3 (by rfl) ⟨4765907, by rfl⟩ : syracuseStep 25418173 = 9531815) B9531815
theorem B33890897 : Blo 2061435 33890897 := bstep (se 2 (by rfl) ⟨12709086, by rfl⟩ : syracuseStep 33890897 = 25418173) B25418173
theorem B90375725 : Blo 2061435 90375725 := bstep (se 3 (by rfl) ⟨16945448, by rfl⟩ : syracuseStep 90375725 = 33890897) B33890897
theorem B60250483 : Blo 2061435 60250483 := bstep (se 1 (by rfl) ⟨45187862, by rfl⟩ : syracuseStep 60250483 = 90375725) B90375725
theorem B80333977 : Blo 2061435 80333977 := bstep (se 2 (by rfl) ⟨30125241, by rfl⟩ : syracuseStep 80333977 = 60250483) B60250483
theorem B107111969 : Blo 2061435 107111969 := bstep (se 2 (by rfl) ⟨40166988, by rfl⟩ : syracuseStep 107111969 = 80333977) B80333977
theorem B71407979 : Blo 2061435 71407979 := bstep (se 1 (by rfl) ⟨53555984, by rfl⟩ : syracuseStep 71407979 = 107111969) B107111969
theorem B47605319 : Blo 2061435 47605319 := bstep (se 1 (by rfl) ⟨35703989, by rfl⟩ : syracuseStep 47605319 = 71407979) B71407979
theorem B31736879 : Blo 2061435 31736879 := bstep (se 1 (by rfl) ⟨23802659, by rfl⟩ : syracuseStep 31736879 = 47605319) B47605319
theorem B21157919 : Blo 2061435 21157919 := bstep (se 1 (by rfl) ⟨15868439, by rfl⟩ : syracuseStep 21157919 = 31736879) B31736879
theorem B14105279 : Blo 2061435 14105279 := bstep (se 1 (by rfl) ⟨10578959, by rfl⟩ : syracuseStep 14105279 = 21157919) B21157919
theorem B37614077 : Blo 2061435 37614077 := bstep (se 3 (by rfl) ⟨7052639, by rfl⟩ : syracuseStep 37614077 = 14105279) B14105279
theorem B25076051 : Blo 2061435 25076051 := bstep (se 1 (by rfl) ⟨18807038, by rfl⟩ : syracuseStep 25076051 = 37614077) B37614077
theorem B16717367 : Blo 2061435 16717367 := bstep (se 1 (by rfl) ⟨12538025, by rfl⟩ : syracuseStep 16717367 = 25076051) B25076051
theorem B11144911 : Blo 2061435 11144911 := bstep (se 1 (by rfl) ⟨8358683, by rfl⟩ : syracuseStep 11144911 = 16717367) B16717367
theorem B14859881 : Blo 2061435 14859881 := bstep (se 2 (by rfl) ⟨5572455, by rfl⟩ : syracuseStep 14859881 = 11144911) B11144911
theorem B9906587 : Blo 2061435 9906587 := bstep (se 1 (by rfl) ⟨7429940, by rfl⟩ : syracuseStep 9906587 = 14859881) B14859881
theorem B6604391 : Blo 2061435 6604391 := bstep (se 1 (by rfl) ⟨4953293, by rfl⟩ : syracuseStep 6604391 = 9906587) B9906587
theorem B4402927 : Blo 2061435 4402927 := bstep (se 1 (by rfl) ⟨3302195, by rfl⟩ : syracuseStep 4402927 = 6604391) B6604391
theorem B5870569 : Blo 2061435 5870569 := bstep (se 2 (by rfl) ⟨2201463, by rfl⟩ : syracuseStep 5870569 = 4402927) B4402927
theorem B7827425 : Blo 2061435 7827425 := bstep (se 2 (by rfl) ⟨2935284, by rfl⟩ : syracuseStep 7827425 = 5870569) B5870569
theorem B5218283 : Blo 2061435 5218283 := bstep (se 1 (by rfl) ⟨3913712, by rfl⟩ : syracuseStep 5218283 = 7827425) B7827425
theorem B3478855 : Blo 2061435 3478855 := bstep (se 1 (by rfl) ⟨2609141, by rfl⟩ : syracuseStep 3478855 = 5218283) B5218283
theorem B4638473 : Blo 2061435 4638473 := bstep (se 2 (by rfl) ⟨1739427, by rfl⟩ : syracuseStep 4638473 = 3478855) B3478855
theorem B3092315 : Blo 2061435 3092315 := bstep (se 1 (by rfl) ⟨2319236, by rfl⟩ : syracuseStep 3092315 = 4638473) B4638473
theorem B2061543 : Blo 2061435 2061543 := bstep (se 1 (by rfl) ⟨1546157, by rfl⟩ : syracuseStep 2061543 = 3092315) B3092315
theorem B2319241 : Blo 2061435 2319241 := bbase (se 2 (by rfl) ⟨869715, by rfl⟩ : syracuseStep 2319241 = 1739431) (by norm_num)
theorem B3092321 : Blo 2061435 3092321 := bstep (se 2 (by rfl) ⟨1159620, by rfl⟩ : syracuseStep 3092321 = 2319241) B2319241
theorem B2061547 : Blo 2061435 2061547 := bstep (se 1 (by rfl) ⟨1546160, by rfl⟩ : syracuseStep 2061547 = 3092321) B3092321
theorem B2261953 : Blo 2061435 2261953 := bbase (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) (by norm_num)
theorem B3015937 : Blo 2061435 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B4021249 : Blo 2061435 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B5361665 : Blo 2061435 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B57191093 : Blo 2061435 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B38127395 : Blo 2061435 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B101673053 : Blo 2061435 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B67782035 : Blo 2061435 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B45188023 : Blo 2061435 45188023 := bstep (se 1 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 45188023 = 67782035) B67782035
theorem B60250697 : Blo 2061435 60250697 := bstep (se 2 (by rfl) ⟨22594011, by rfl⟩ : syracuseStep 60250697 = 45188023) B45188023
theorem B40167131 : Blo 2061435 40167131 := bstep (se 1 (by rfl) ⟨30125348, by rfl⟩ : syracuseStep 40167131 = 60250697) B60250697
theorem B107112349 : Blo 2061435 107112349 := bstep (se 3 (by rfl) ⟨20083565, by rfl⟩ : syracuseStep 107112349 = 40167131) B40167131
theorem B142816465 : Blo 2061435 142816465 := bstep (se 2 (by rfl) ⟨53556174, by rfl⟩ : syracuseStep 142816465 = 107112349) B107112349
theorem B761687813 : Blo 2061435 761687813 := bstep (se 4 (by rfl) ⟨71408232, by rfl⟩ : syracuseStep 761687813 = 142816465) B142816465
theorem B507791875 : Blo 2061435 507791875 := bstep (se 1 (by rfl) ⟨380843906, by rfl⟩ : syracuseStep 507791875 = 761687813) B761687813
theorem B677055833 : Blo 2061435 677055833 := bstep (se 2 (by rfl) ⟨253895937, by rfl⟩ : syracuseStep 677055833 = 507791875) B507791875
theorem B451370555 : Blo 2061435 451370555 := bstep (se 1 (by rfl) ⟨338527916, by rfl⟩ : syracuseStep 451370555 = 677055833) B677055833
theorem B300913703 : Blo 2061435 300913703 := bstep (se 1 (by rfl) ⟨225685277, by rfl⟩ : syracuseStep 300913703 = 451370555) B451370555
theorem B200609135 : Blo 2061435 200609135 := bstep (se 1 (by rfl) ⟨150456851, by rfl⟩ : syracuseStep 200609135 = 300913703) B300913703
theorem B133739423 : Blo 2061435 133739423 := bstep (se 1 (by rfl) ⟨100304567, by rfl⟩ : syracuseStep 133739423 = 200609135) B200609135
theorem B89159615 : Blo 2061435 89159615 := bstep (se 1 (by rfl) ⟨66869711, by rfl⟩ : syracuseStep 89159615 = 133739423) B133739423
theorem B59439743 : Blo 2061435 59439743 := bstep (se 1 (by rfl) ⟨44579807, by rfl⟩ : syracuseStep 59439743 = 89159615) B89159615
theorem B39626495 : Blo 2061435 39626495 := bstep (se 1 (by rfl) ⟨29719871, by rfl⟩ : syracuseStep 39626495 = 59439743) B59439743
theorem B26417663 : Blo 2061435 26417663 := bstep (se 1 (by rfl) ⟨19813247, by rfl⟩ : syracuseStep 26417663 = 39626495) B39626495
theorem B17611775 : Blo 2061435 17611775 := bstep (se 1 (by rfl) ⟨13208831, by rfl⟩ : syracuseStep 17611775 = 26417663) B26417663
theorem B11741183 : Blo 2061435 11741183 := bstep (se 1 (by rfl) ⟨8805887, by rfl⟩ : syracuseStep 11741183 = 17611775) B17611775
theorem B7827455 : Blo 2061435 7827455 := bstep (se 1 (by rfl) ⟨5870591, by rfl⟩ : syracuseStep 7827455 = 11741183) B11741183
theorem B5218303 : Blo 2061435 5218303 := bstep (se 1 (by rfl) ⟨3913727, by rfl⟩ : syracuseStep 5218303 = 7827455) B7827455
theorem B6957737 : Blo 2061435 6957737 := bstep (se 2 (by rfl) ⟨2609151, by rfl⟩ : syracuseStep 6957737 = 5218303) B5218303
theorem B4638491 : Blo 2061435 4638491 := bstep (se 1 (by rfl) ⟨3478868, by rfl⟩ : syracuseStep 4638491 = 6957737) B6957737
theorem B3092327 : Blo 2061435 3092327 := bstep (se 1 (by rfl) ⟨2319245, by rfl⟩ : syracuseStep 3092327 = 4638491) B4638491
theorem B2061551 : Blo 2061435 2061551 := bstep (se 1 (by rfl) ⟨1546163, by rfl⟩ : syracuseStep 2061551 = 3092327) B3092327
theorem B3092333 : Blo 2061435 3092333 := bbase (se 3 (by rfl) ⟨579812, by rfl⟩ : syracuseStep 3092333 = 1159625) (by norm_num)
theorem B2061555 : Blo 2061435 2061555 := bstep (se 1 (by rfl) ⟨1546166, by rfl⟩ : syracuseStep 2061555 = 3092333) B3092333
theorem B4638509 : Blo 2061435 4638509 := bbase (se 3 (by rfl) ⟨869720, by rfl⟩ : syracuseStep 4638509 = 1739441) (by norm_num)
theorem B3092339 : Blo 2061435 3092339 := bstep (se 1 (by rfl) ⟨2319254, by rfl⟩ : syracuseStep 3092339 = 4638509) B4638509
theorem B2061559 : Blo 2061435 2061559 := bstep (se 1 (by rfl) ⟨1546169, by rfl⟩ : syracuseStep 2061559 = 3092339) B3092339
theorem B8805941 : Blo 2061435 8805941 := bbase (se 5 (by rfl) ⟨412778, by rfl⟩ : syracuseStep 8805941 = 825557) (by norm_num)
theorem B5870627 : Blo 2061435 5870627 := bstep (se 1 (by rfl) ⟨4402970, by rfl⟩ : syracuseStep 5870627 = 8805941) B8805941
theorem B3913751 : Blo 2061435 3913751 := bstep (se 1 (by rfl) ⟨2935313, by rfl⟩ : syracuseStep 3913751 = 5870627) B5870627
theorem B2609167 : Blo 2061435 2609167 := bstep (se 1 (by rfl) ⟨1956875, by rfl⟩ : syracuseStep 2609167 = 3913751) B3913751
theorem B3478889 : Blo 2061435 3478889 := bstep (se 2 (by rfl) ⟨1304583, by rfl⟩ : syracuseStep 3478889 = 2609167) B2609167
theorem B2319259 : Blo 2061435 2319259 := bstep (se 1 (by rfl) ⟨1739444, by rfl⟩ : syracuseStep 2319259 = 3478889) B3478889
theorem B3092345 : Blo 2061435 3092345 := bstep (se 2 (by rfl) ⟨1159629, by rfl⟩ : syracuseStep 3092345 = 2319259) B2319259
theorem B2061563 : Blo 2061435 2061563 := bstep (se 1 (by rfl) ⟨1546172, by rfl⟩ : syracuseStep 2061563 = 3092345) B3092345
theorem B3715013 : Blo 2061435 3715013 := bbase (se 4 (by rfl) ⟨348282, by rfl⟩ : syracuseStep 3715013 = 696565) (by norm_num)
theorem B2476675 : Blo 2061435 2476675 := bstep (se 1 (by rfl) ⟨1857506, by rfl⟩ : syracuseStep 2476675 = 3715013) B3715013
theorem B13208933 : Blo 2061435 13208933 := bstep (se 4 (by rfl) ⟨1238337, by rfl⟩ : syracuseStep 13208933 = 2476675) B2476675
theorem B35223821 : Blo 2061435 35223821 := bstep (se 3 (by rfl) ⟨6604466, by rfl⟩ : syracuseStep 35223821 = 13208933) B13208933
theorem B23482547 : Blo 2061435 23482547 := bstep (se 1 (by rfl) ⟨17611910, by rfl⟩ : syracuseStep 23482547 = 35223821) B35223821
theorem B15655031 : Blo 2061435 15655031 := bstep (se 1 (by rfl) ⟨11741273, by rfl⟩ : syracuseStep 15655031 = 23482547) B23482547
theorem B10436687 : Blo 2061435 10436687 := bstep (se 1 (by rfl) ⟨7827515, by rfl⟩ : syracuseStep 10436687 = 15655031) B15655031
theorem B6957791 : Blo 2061435 6957791 := bstep (se 1 (by rfl) ⟨5218343, by rfl⟩ : syracuseStep 6957791 = 10436687) B10436687
theorem B4638527 : Blo 2061435 4638527 := bstep (se 1 (by rfl) ⟨3478895, by rfl⟩ : syracuseStep 4638527 = 6957791) B6957791
theorem B3092351 : Blo 2061435 3092351 := bstep (se 1 (by rfl) ⟨2319263, by rfl⟩ : syracuseStep 3092351 = 4638527) B4638527
theorem B2061567 : Blo 2061435 2061567 := bstep (se 1 (by rfl) ⟨1546175, by rfl⟩ : syracuseStep 2061567 = 3092351) B3092351
theorem B3092357 : Blo 2061435 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B2061571 : Blo 2061435 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B3478909 : Blo 2061435 3478909 := bbase (se 3 (by rfl) ⟨652295, by rfl⟩ : syracuseStep 3478909 = 1304591) (by norm_num)
theorem B4638545 : Blo 2061435 4638545 := bstep (se 2 (by rfl) ⟨1739454, by rfl⟩ : syracuseStep 4638545 = 3478909) B3478909
theorem B3092363 : Blo 2061435 3092363 := bstep (se 1 (by rfl) ⟨2319272, by rfl⟩ : syracuseStep 3092363 = 4638545) B4638545
theorem B2061575 : Blo 2061435 2061575 := bstep (se 1 (by rfl) ⟨1546181, by rfl⟩ : syracuseStep 2061575 = 3092363) B3092363
theorem B2319277 : Blo 2061435 2319277 := bbase (se 3 (by rfl) ⟨434864, by rfl⟩ : syracuseStep 2319277 = 869729) (by norm_num)
theorem B3092369 : Blo 2061435 3092369 := bstep (se 2 (by rfl) ⟨1159638, by rfl⟩ : syracuseStep 3092369 = 2319277) B2319277
theorem B2061579 : Blo 2061435 2061579 := bstep (se 1 (by rfl) ⟨1546184, by rfl⟩ : syracuseStep 2061579 = 3092369) B3092369
theorem B6957845 : Blo 2061435 6957845 := bbase (se 6 (by rfl) ⟨163074, by rfl⟩ : syracuseStep 6957845 = 326149) (by norm_num)
theorem B4638563 : Blo 2061435 4638563 := bstep (se 1 (by rfl) ⟨3478922, by rfl⟩ : syracuseStep 4638563 = 6957845) B6957845
theorem B3092375 : Blo 2061435 3092375 := bstep (se 1 (by rfl) ⟨2319281, by rfl⟩ : syracuseStep 3092375 = 4638563) B4638563
theorem B2061583 : Blo 2061435 2061583 := bstep (se 1 (by rfl) ⟨1546187, by rfl⟩ : syracuseStep 2061583 = 3092375) B3092375
theorem B3092381 : Blo 2061435 3092381 := bbase (se 3 (by rfl) ⟨579821, by rfl⟩ : syracuseStep 3092381 = 1159643) (by norm_num)
theorem B2061587 : Blo 2061435 2061587 := bstep (se 1 (by rfl) ⟨1546190, by rfl⟩ : syracuseStep 2061587 = 3092381) B3092381
theorem B4638581 : Blo 2061435 4638581 := bbase (se 5 (by rfl) ⟨217433, by rfl⟩ : syracuseStep 4638581 = 434867) (by norm_num)
theorem B3092387 : Blo 2061435 3092387 := bstep (se 1 (by rfl) ⟨2319290, by rfl⟩ : syracuseStep 3092387 = 4638581) B4638581
theorem B2061591 : Blo 2061435 2061591 := bstep (se 1 (by rfl) ⟨1546193, by rfl⟩ : syracuseStep 2061591 = 3092387) B3092387
theorem B2415529 : Blo 2061435 2415529 := bbase (se 2 (by rfl) ⟨905823, by rfl⟩ : syracuseStep 2415529 = 1811647) (by norm_num)
theorem B3220705 : Blo 2061435 3220705 := bstep (se 2 (by rfl) ⟨1207764, by rfl⟩ : syracuseStep 3220705 = 2415529) B2415529
theorem B17177093 : Blo 2061435 17177093 := bstep (se 4 (by rfl) ⟨1610352, by rfl⟩ : syracuseStep 17177093 = 3220705) B3220705
theorem B11451395 : Blo 2061435 11451395 := bstep (se 1 (by rfl) ⟨8588546, by rfl⟩ : syracuseStep 11451395 = 17177093) B17177093
theorem B7634263 : Blo 2061435 7634263 := bstep (se 1 (by rfl) ⟨5725697, by rfl⟩ : syracuseStep 7634263 = 11451395) B11451395
theorem B10179017 : Blo 2061435 10179017 := bstep (se 2 (by rfl) ⟨3817131, by rfl⟩ : syracuseStep 10179017 = 7634263) B7634263
theorem B6786011 : Blo 2061435 6786011 := bstep (se 1 (by rfl) ⟨5089508, by rfl⟩ : syracuseStep 6786011 = 10179017) B10179017
theorem B4524007 : Blo 2061435 4524007 := bstep (se 1 (by rfl) ⟨3393005, by rfl⟩ : syracuseStep 4524007 = 6786011) B6786011
theorem B6032009 : Blo 2061435 6032009 := bstep (se 2 (by rfl) ⟨2262003, by rfl⟩ : syracuseStep 6032009 = 4524007) B4524007
theorem B4021339 : Blo 2061435 4021339 := bstep (se 1 (by rfl) ⟨3016004, by rfl⟩ : syracuseStep 4021339 = 6032009) B6032009
theorem B5361785 : Blo 2061435 5361785 := bstep (se 2 (by rfl) ⟨2010669, by rfl⟩ : syracuseStep 5361785 = 4021339) B4021339
theorem B3574523 : Blo 2061435 3574523 := bstep (se 1 (by rfl) ⟨2680892, by rfl⟩ : syracuseStep 3574523 = 5361785) B5361785
theorem B2383015 : Blo 2061435 2383015 := bstep (se 1 (by rfl) ⟨1787261, by rfl⟩ : syracuseStep 2383015 = 3574523) B3574523
theorem B3177353 : Blo 2061435 3177353 := bstep (se 2 (by rfl) ⟨1191507, by rfl⟩ : syracuseStep 3177353 = 2383015) B2383015
theorem B2118235 : Blo 2061435 2118235 := bstep (se 1 (by rfl) ⟨1588676, by rfl⟩ : syracuseStep 2118235 = 3177353) B3177353
theorem B2824313 : Blo 2061435 2824313 := bstep (se 2 (by rfl) ⟨1059117, by rfl⟩ : syracuseStep 2824313 = 2118235) B2118235
theorem B7531501 : Blo 2061435 7531501 := bstep (se 3 (by rfl) ⟨1412156, by rfl⟩ : syracuseStep 7531501 = 2824313) B2824313
theorem B10042001 : Blo 2061435 10042001 := bstep (se 2 (by rfl) ⟨3765750, by rfl⟩ : syracuseStep 10042001 = 7531501) B7531501
theorem B6694667 : Blo 2061435 6694667 := bstep (se 1 (by rfl) ⟨5021000, by rfl⟩ : syracuseStep 6694667 = 10042001) B10042001
theorem B4463111 : Blo 2061435 4463111 := bstep (se 1 (by rfl) ⟨3347333, by rfl⟩ : syracuseStep 4463111 = 6694667) B6694667
theorem B11901629 : Blo 2061435 11901629 := bstep (se 3 (by rfl) ⟨2231555, by rfl⟩ : syracuseStep 11901629 = 4463111) B4463111
theorem B7934419 : Blo 2061435 7934419 := bstep (se 1 (by rfl) ⟨5950814, by rfl⟩ : syracuseStep 7934419 = 11901629) B11901629
theorem B42316901 : Blo 2061435 42316901 := bstep (se 4 (by rfl) ⟨3967209, by rfl⟩ : syracuseStep 42316901 = 7934419) B7934419
theorem B28211267 : Blo 2061435 28211267 := bstep (se 1 (by rfl) ⟨21158450, by rfl⟩ : syracuseStep 28211267 = 42316901) B42316901
theorem B75230045 : Blo 2061435 75230045 := bstep (se 3 (by rfl) ⟨14105633, by rfl⟩ : syracuseStep 75230045 = 28211267) B28211267
theorem B50153363 : Blo 2061435 50153363 := bstep (se 1 (by rfl) ⟨37615022, by rfl⟩ : syracuseStep 50153363 = 75230045) B75230045
theorem B33435575 : Blo 2061435 33435575 := bstep (se 1 (by rfl) ⟨25076681, by rfl⟩ : syracuseStep 33435575 = 50153363) B50153363
theorem B22290383 : Blo 2061435 22290383 := bstep (se 1 (by rfl) ⟨16717787, by rfl⟩ : syracuseStep 22290383 = 33435575) B33435575
theorem B14860255 : Blo 2061435 14860255 := bstep (se 1 (by rfl) ⟨11145191, by rfl⟩ : syracuseStep 14860255 = 22290383) B22290383
theorem B19813673 : Blo 2061435 19813673 := bstep (se 2 (by rfl) ⟨7430127, by rfl⟩ : syracuseStep 19813673 = 14860255) B14860255
theorem B13209115 : Blo 2061435 13209115 := bstep (se 1 (by rfl) ⟨9906836, by rfl⟩ : syracuseStep 13209115 = 19813673) B19813673
theorem B17612153 : Blo 2061435 17612153 := bstep (se 2 (by rfl) ⟨6604557, by rfl⟩ : syracuseStep 17612153 = 13209115) B13209115
theorem B11741435 : Blo 2061435 11741435 := bstep (se 1 (by rfl) ⟨8806076, by rfl⟩ : syracuseStep 11741435 = 17612153) B17612153
theorem B7827623 : Blo 2061435 7827623 := bstep (se 1 (by rfl) ⟨5870717, by rfl⟩ : syracuseStep 7827623 = 11741435) B11741435
theorem B5218415 : Blo 2061435 5218415 := bstep (se 1 (by rfl) ⟨3913811, by rfl⟩ : syracuseStep 5218415 = 7827623) B7827623
theorem B3478943 : Blo 2061435 3478943 := bstep (se 1 (by rfl) ⟨2609207, by rfl⟩ : syracuseStep 3478943 = 5218415) B5218415
theorem B2319295 : Blo 2061435 2319295 := bstep (se 1 (by rfl) ⟨1739471, by rfl⟩ : syracuseStep 2319295 = 3478943) B3478943
theorem B3092393 : Blo 2061435 3092393 := bstep (se 2 (by rfl) ⟨1159647, by rfl⟩ : syracuseStep 3092393 = 2319295) B2319295
theorem B2061595 : Blo 2061435 2061595 := bstep (se 1 (by rfl) ⟨1546196, by rfl⟩ : syracuseStep 2061595 = 3092393) B3092393
theorem B7827637 : Blo 2061435 7827637 := bbase (se 5 (by rfl) ⟨366920, by rfl⟩ : syracuseStep 7827637 = 733841) (by norm_num)
theorem B10436849 : Blo 2061435 10436849 := bstep (se 2 (by rfl) ⟨3913818, by rfl⟩ : syracuseStep 10436849 = 7827637) B7827637
theorem B6957899 : Blo 2061435 6957899 := bstep (se 1 (by rfl) ⟨5218424, by rfl⟩ : syracuseStep 6957899 = 10436849) B10436849
theorem B4638599 : Blo 2061435 4638599 := bstep (se 1 (by rfl) ⟨3478949, by rfl⟩ : syracuseStep 4638599 = 6957899) B6957899
theorem B3092399 : Blo 2061435 3092399 := bstep (se 1 (by rfl) ⟨2319299, by rfl⟩ : syracuseStep 3092399 = 4638599) B4638599
theorem B2061599 : Blo 2061435 2061599 := bstep (se 1 (by rfl) ⟨1546199, by rfl⟩ : syracuseStep 2061599 = 3092399) B3092399
theorem B3092405 : Blo 2061435 3092405 := bbase (se 5 (by rfl) ⟨144956, by rfl⟩ : syracuseStep 3092405 = 289913) (by norm_num)
theorem B2061603 : Blo 2061435 2061603 := bstep (se 1 (by rfl) ⟨1546202, by rfl⟩ : syracuseStep 2061603 = 3092405) B3092405
theorem B5218445 : Blo 2061435 5218445 := bbase (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) (by norm_num)
theorem B3478963 : Blo 2061435 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B4638617 : Blo 2061435 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B3092411 : Blo 2061435 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B2061607 : Blo 2061435 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B2319313 : Blo 2061435 2319313 := bbase (se 2 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 2319313 = 1739485) (by norm_num)
theorem B3092417 : Blo 2061435 3092417 := bstep (se 2 (by rfl) ⟨1159656, by rfl⟩ : syracuseStep 3092417 = 2319313) B2319313
theorem B2061611 : Blo 2061435 2061611 := bstep (se 1 (by rfl) ⟨1546208, by rfl⟩ : syracuseStep 2061611 = 3092417) B3092417
theorem B4701925 : Blo 2061435 4701925 := bbase (se 4 (by rfl) ⟨440805, by rfl⟩ : syracuseStep 4701925 = 881611) (by norm_num)
theorem B6269233 : Blo 2061435 6269233 := bstep (se 2 (by rfl) ⟨2350962, by rfl⟩ : syracuseStep 6269233 = 4701925) B4701925
theorem B8358977 : Blo 2061435 8358977 := bstep (se 2 (by rfl) ⟨3134616, by rfl⟩ : syracuseStep 8358977 = 6269233) B6269233
theorem B5572651 : Blo 2061435 5572651 := bstep (se 1 (by rfl) ⟨4179488, by rfl⟩ : syracuseStep 5572651 = 8358977) B8358977
theorem B7430201 : Blo 2061435 7430201 := bstep (se 2 (by rfl) ⟨2786325, by rfl⟩ : syracuseStep 7430201 = 5572651) B5572651
theorem B4953467 : Blo 2061435 4953467 := bstep (se 1 (by rfl) ⟨3715100, by rfl⟩ : syracuseStep 4953467 = 7430201) B7430201
theorem B3302311 : Blo 2061435 3302311 := bstep (se 1 (by rfl) ⟨2476733, by rfl⟩ : syracuseStep 3302311 = 4953467) B4953467
theorem B4403081 : Blo 2061435 4403081 := bstep (se 2 (by rfl) ⟨1651155, by rfl⟩ : syracuseStep 4403081 = 3302311) B3302311
theorem B2935387 : Blo 2061435 2935387 := bstep (se 1 (by rfl) ⟨2201540, by rfl⟩ : syracuseStep 2935387 = 4403081) B4403081
theorem B3913849 : Blo 2061435 3913849 := bstep (se 2 (by rfl) ⟨1467693, by rfl⟩ : syracuseStep 3913849 = 2935387) B2935387
theorem B5218465 : Blo 2061435 5218465 := bstep (se 2 (by rfl) ⟨1956924, by rfl⟩ : syracuseStep 5218465 = 3913849) B3913849
theorem B6957953 : Blo 2061435 6957953 := bstep (se 2 (by rfl) ⟨2609232, by rfl⟩ : syracuseStep 6957953 = 5218465) B5218465
theorem B4638635 : Blo 2061435 4638635 := bstep (se 1 (by rfl) ⟨3478976, by rfl⟩ : syracuseStep 4638635 = 6957953) B6957953
theorem B3092423 : Blo 2061435 3092423 := bstep (se 1 (by rfl) ⟨2319317, by rfl⟩ : syracuseStep 3092423 = 4638635) B4638635
theorem B2061615 : Blo 2061435 2061615 := bstep (se 1 (by rfl) ⟨1546211, by rfl⟩ : syracuseStep 2061615 = 3092423) B3092423
theorem B3092429 : Blo 2061435 3092429 := bbase (se 3 (by rfl) ⟨579830, by rfl⟩ : syracuseStep 3092429 = 1159661) (by norm_num)
theorem B2061619 : Blo 2061435 2061619 := bstep (se 1 (by rfl) ⟨1546214, by rfl⟩ : syracuseStep 2061619 = 3092429) B3092429
theorem B4638653 : Blo 2061435 4638653 := bbase (se 3 (by rfl) ⟨869747, by rfl⟩ : syracuseStep 4638653 = 1739495) (by norm_num)
theorem B3092435 : Blo 2061435 3092435 := bstep (se 1 (by rfl) ⟨2319326, by rfl⟩ : syracuseStep 3092435 = 4638653) B4638653
theorem B2061623 : Blo 2061435 2061623 := bstep (se 1 (by rfl) ⟨1546217, by rfl⟩ : syracuseStep 2061623 = 3092435) B3092435
theorem B3478997 : Blo 2061435 3478997 := bbase (se 7 (by rfl) ⟨40769, by rfl⟩ : syracuseStep 3478997 = 81539) (by norm_num)
theorem B2319331 : Blo 2061435 2319331 := bstep (se 1 (by rfl) ⟨1739498, by rfl⟩ : syracuseStep 2319331 = 3478997) B3478997
theorem B3092441 : Blo 2061435 3092441 := bstep (se 2 (by rfl) ⟨1159665, by rfl⟩ : syracuseStep 3092441 = 2319331) B2319331
theorem B2061627 : Blo 2061435 2061627 := bstep (se 1 (by rfl) ⟨1546220, by rfl⟩ : syracuseStep 2061627 = 3092441) B3092441
theorem B8806229 : Blo 2061435 8806229 := bbase (se 9 (by rfl) ⟨25799, by rfl⟩ : syracuseStep 8806229 = 51599) (by norm_num)
theorem B5870819 : Blo 2061435 5870819 := bstep (se 1 (by rfl) ⟨4403114, by rfl⟩ : syracuseStep 5870819 = 8806229) B8806229
theorem B15655517 : Blo 2061435 15655517 := bstep (se 3 (by rfl) ⟨2935409, by rfl⟩ : syracuseStep 15655517 = 5870819) B5870819
theorem B10437011 : Blo 2061435 10437011 := bstep (se 1 (by rfl) ⟨7827758, by rfl⟩ : syracuseStep 10437011 = 15655517) B15655517
theorem B6958007 : Blo 2061435 6958007 := bstep (se 1 (by rfl) ⟨5218505, by rfl⟩ : syracuseStep 6958007 = 10437011) B10437011
theorem B4638671 : Blo 2061435 4638671 := bstep (se 1 (by rfl) ⟨3479003, by rfl⟩ : syracuseStep 4638671 = 6958007) B6958007
theorem B3092447 : Blo 2061435 3092447 := bstep (se 1 (by rfl) ⟨2319335, by rfl⟩ : syracuseStep 3092447 = 4638671) B4638671
theorem B2061631 : Blo 2061435 2061631 := bstep (se 1 (by rfl) ⟨1546223, by rfl⟩ : syracuseStep 2061631 = 3092447) B3092447
theorem B3092453 : Blo 2061435 3092453 := bbase (se 4 (by rfl) ⟨289917, by rfl⟩ : syracuseStep 3092453 = 579835) (by norm_num)
theorem B2061635 : Blo 2061435 2061635 := bstep (se 1 (by rfl) ⟨1546226, by rfl⟩ : syracuseStep 2061635 = 3092453) B3092453
theorem B6114437 : Blo 2061435 6114437 := bbase (se 4 (by rfl) ⟨573228, by rfl⟩ : syracuseStep 6114437 = 1146457) (by norm_num)
theorem B4076291 : Blo 2061435 4076291 := bstep (se 1 (by rfl) ⟨3057218, by rfl⟩ : syracuseStep 4076291 = 6114437) B6114437
theorem B10870109 : Blo 2061435 10870109 := bstep (se 3 (by rfl) ⟨2038145, by rfl⟩ : syracuseStep 10870109 = 4076291) B4076291
theorem B7246739 : Blo 2061435 7246739 := bstep (se 1 (by rfl) ⟨5435054, by rfl⟩ : syracuseStep 7246739 = 10870109) B10870109
theorem B4831159 : Blo 2061435 4831159 := bstep (se 1 (by rfl) ⟨3623369, by rfl⟩ : syracuseStep 4831159 = 7246739) B7246739
theorem B6441545 : Blo 2061435 6441545 := bstep (se 2 (by rfl) ⟨2415579, by rfl⟩ : syracuseStep 6441545 = 4831159) B4831159
theorem B4294363 : Blo 2061435 4294363 := bstep (se 1 (by rfl) ⟨3220772, by rfl⟩ : syracuseStep 4294363 = 6441545) B6441545
theorem B5725817 : Blo 2061435 5725817 := bstep (se 2 (by rfl) ⟨2147181, by rfl⟩ : syracuseStep 5725817 = 4294363) B4294363
theorem B3817211 : Blo 2061435 3817211 := bstep (se 1 (by rfl) ⟨2862908, by rfl⟩ : syracuseStep 3817211 = 5725817) B5725817
theorem B10179229 : Blo 2061435 10179229 := bstep (se 3 (by rfl) ⟨1908605, by rfl⟩ : syracuseStep 10179229 = 3817211) B3817211
theorem B13572305 : Blo 2061435 13572305 := bstep (se 2 (by rfl) ⟨5089614, by rfl⟩ : syracuseStep 13572305 = 10179229) B10179229
theorem B9048203 : Blo 2061435 9048203 := bstep (se 1 (by rfl) ⟨6786152, by rfl⟩ : syracuseStep 9048203 = 13572305) B13572305
theorem B6032135 : Blo 2061435 6032135 := bstep (se 1 (by rfl) ⟨4524101, by rfl⟩ : syracuseStep 6032135 = 9048203) B9048203
theorem B4021423 : Blo 2061435 4021423 := bstep (se 1 (by rfl) ⟨3016067, by rfl⟩ : syracuseStep 4021423 = 6032135) B6032135
theorem B21447589 : Blo 2061435 21447589 := bstep (se 4 (by rfl) ⟨2010711, by rfl⟩ : syracuseStep 21447589 = 4021423) B4021423
theorem B28596785 : Blo 2061435 28596785 := bstep (se 2 (by rfl) ⟨10723794, by rfl⟩ : syracuseStep 28596785 = 21447589) B21447589
theorem B76258093 : Blo 2061435 76258093 := bstep (se 3 (by rfl) ⟨14298392, by rfl⟩ : syracuseStep 76258093 = 28596785) B28596785
theorem B101677457 : Blo 2061435 101677457 := bstep (se 2 (by rfl) ⟨38129046, by rfl⟩ : syracuseStep 101677457 = 76258093) B76258093
theorem B67784971 : Blo 2061435 67784971 := bstep (se 1 (by rfl) ⟨50838728, by rfl⟩ : syracuseStep 67784971 = 101677457) B101677457
theorem B90379961 : Blo 2061435 90379961 := bstep (se 2 (by rfl) ⟨33892485, by rfl⟩ : syracuseStep 90379961 = 67784971) B67784971
theorem B60253307 : Blo 2061435 60253307 := bstep (se 1 (by rfl) ⟨45189980, by rfl⟩ : syracuseStep 60253307 = 90379961) B90379961
theorem B40168871 : Blo 2061435 40168871 := bstep (se 1 (by rfl) ⟨30126653, by rfl⟩ : syracuseStep 40168871 = 60253307) B60253307
theorem B26779247 : Blo 2061435 26779247 := bstep (se 1 (by rfl) ⟨20084435, by rfl⟩ : syracuseStep 26779247 = 40168871) B40168871
theorem B17852831 : Blo 2061435 17852831 := bstep (se 1 (by rfl) ⟨13389623, by rfl⟩ : syracuseStep 17852831 = 26779247) B26779247
theorem B11901887 : Blo 2061435 11901887 := bstep (se 1 (by rfl) ⟨8926415, by rfl⟩ : syracuseStep 11901887 = 17852831) B17852831
theorem B7934591 : Blo 2061435 7934591 := bstep (se 1 (by rfl) ⟨5950943, by rfl⟩ : syracuseStep 7934591 = 11901887) B11901887
theorem B5289727 : Blo 2061435 5289727 := bstep (se 1 (by rfl) ⟨3967295, by rfl⟩ : syracuseStep 5289727 = 7934591) B7934591
theorem B7052969 : Blo 2061435 7052969 := bstep (se 2 (by rfl) ⟨2644863, by rfl⟩ : syracuseStep 7052969 = 5289727) B5289727
theorem B4701979 : Blo 2061435 4701979 := bstep (se 1 (by rfl) ⟨3526484, by rfl⟩ : syracuseStep 4701979 = 7052969) B7052969
theorem B25077221 : Blo 2061435 25077221 := bstep (se 4 (by rfl) ⟨2350989, by rfl⟩ : syracuseStep 25077221 = 4701979) B4701979
theorem B16718147 : Blo 2061435 16718147 := bstep (se 1 (by rfl) ⟨12538610, by rfl⟩ : syracuseStep 16718147 = 25077221) B25077221
theorem B11145431 : Blo 2061435 11145431 := bstep (se 1 (by rfl) ⟨8359073, by rfl⟩ : syracuseStep 11145431 = 16718147) B16718147
theorem B7430287 : Blo 2061435 7430287 := bstep (se 1 (by rfl) ⟨5572715, by rfl⟩ : syracuseStep 7430287 = 11145431) B11145431
theorem B9907049 : Blo 2061435 9907049 := bstep (se 2 (by rfl) ⟨3715143, by rfl⟩ : syracuseStep 9907049 = 7430287) B7430287
theorem B6604699 : Blo 2061435 6604699 := bstep (se 1 (by rfl) ⟨4953524, by rfl⟩ : syracuseStep 6604699 = 9907049) B9907049
theorem B8806265 : Blo 2061435 8806265 := bstep (se 2 (by rfl) ⟨3302349, by rfl⟩ : syracuseStep 8806265 = 6604699) B6604699
theorem B5870843 : Blo 2061435 5870843 := bstep (se 1 (by rfl) ⟨4403132, by rfl⟩ : syracuseStep 5870843 = 8806265) B8806265
theorem B3913895 : Blo 2061435 3913895 := bstep (se 1 (by rfl) ⟨2935421, by rfl⟩ : syracuseStep 3913895 = 5870843) B5870843
theorem B2609263 : Blo 2061435 2609263 := bstep (se 1 (by rfl) ⟨1956947, by rfl⟩ : syracuseStep 2609263 = 3913895) B3913895
theorem B3479017 : Blo 2061435 3479017 := bstep (se 2 (by rfl) ⟨1304631, by rfl⟩ : syracuseStep 3479017 = 2609263) B2609263
theorem B4638689 : Blo 2061435 4638689 := bstep (se 2 (by rfl) ⟨1739508, by rfl⟩ : syracuseStep 4638689 = 3479017) B3479017
theorem B3092459 : Blo 2061435 3092459 := bstep (se 1 (by rfl) ⟨2319344, by rfl⟩ : syracuseStep 3092459 = 4638689) B4638689
theorem B2061639 : Blo 2061435 2061639 := bstep (se 1 (by rfl) ⟨1546229, by rfl⟩ : syracuseStep 2061639 = 3092459) B3092459
theorem B2319349 : Blo 2061435 2319349 := bbase (se 5 (by rfl) ⟨108719, by rfl⟩ : syracuseStep 2319349 = 217439) (by norm_num)
theorem B3092465 : Blo 2061435 3092465 := bstep (se 2 (by rfl) ⟨1159674, by rfl⟩ : syracuseStep 3092465 = 2319349) B2319349
theorem B2061643 : Blo 2061435 2061643 := bstep (se 1 (by rfl) ⟨1546232, by rfl⟩ : syracuseStep 2061643 = 3092465) B3092465
theorem B2609273 : Blo 2061435 2609273 := bbase (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) (by norm_num)
theorem B6958061 : Blo 2061435 6958061 := bstep (se 3 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 6958061 = 2609273) B2609273
theorem B4638707 : Blo 2061435 4638707 := bstep (se 1 (by rfl) ⟨3479030, by rfl⟩ : syracuseStep 4638707 = 6958061) B6958061
theorem B3092471 : Blo 2061435 3092471 := bstep (se 1 (by rfl) ⟨2319353, by rfl⟩ : syracuseStep 3092471 = 4638707) B4638707
theorem B2061647 : Blo 2061435 2061647 := bstep (se 1 (by rfl) ⟨1546235, by rfl⟩ : syracuseStep 2061647 = 3092471) B3092471
theorem B3092477 : Blo 2061435 3092477 := bbase (se 3 (by rfl) ⟨579839, by rfl⟩ : syracuseStep 3092477 = 1159679) (by norm_num)
theorem B2061651 : Blo 2061435 2061651 := bstep (se 1 (by rfl) ⟨1546238, by rfl⟩ : syracuseStep 2061651 = 3092477) B3092477
theorem B4638725 : Blo 2061435 4638725 := bbase (se 4 (by rfl) ⟨434880, by rfl⟩ : syracuseStep 4638725 = 869761) (by norm_num)
theorem B3092483 : Blo 2061435 3092483 := bstep (se 1 (by rfl) ⟨2319362, by rfl⟩ : syracuseStep 3092483 = 4638725) B4638725
theorem B2061655 : Blo 2061435 2061655 := bstep (se 1 (by rfl) ⟨1546241, by rfl⟩ : syracuseStep 2061655 = 3092483) B3092483
theorem B3913933 : Blo 2061435 3913933 := bbase (se 3 (by rfl) ⟨733862, by rfl⟩ : syracuseStep 3913933 = 1467725) (by norm_num)
theorem B5218577 : Blo 2061435 5218577 := bstep (se 2 (by rfl) ⟨1956966, by rfl⟩ : syracuseStep 5218577 = 3913933) B3913933
theorem B3479051 : Blo 2061435 3479051 := bstep (se 1 (by rfl) ⟨2609288, by rfl⟩ : syracuseStep 3479051 = 5218577) B5218577
theorem B2319367 : Blo 2061435 2319367 := bstep (se 1 (by rfl) ⟨1739525, by rfl⟩ : syracuseStep 2319367 = 3479051) B3479051
theorem B3092489 : Blo 2061435 3092489 := bstep (se 2 (by rfl) ⟨1159683, by rfl⟩ : syracuseStep 3092489 = 2319367) B2319367
theorem B2061659 : Blo 2061435 2061659 := bstep (se 1 (by rfl) ⟨1546244, by rfl⟩ : syracuseStep 2061659 = 3092489) B3092489
theorem B10437173 : Blo 2061435 10437173 := bbase (se 5 (by rfl) ⟨489242, by rfl⟩ : syracuseStep 10437173 = 978485) (by norm_num)
theorem B6958115 : Blo 2061435 6958115 := bstep (se 1 (by rfl) ⟨5218586, by rfl⟩ : syracuseStep 6958115 = 10437173) B10437173
theorem B4638743 : Blo 2061435 4638743 := bstep (se 1 (by rfl) ⟨3479057, by rfl⟩ : syracuseStep 4638743 = 6958115) B6958115
theorem B3092495 : Blo 2061435 3092495 := bstep (se 1 (by rfl) ⟨2319371, by rfl⟩ : syracuseStep 3092495 = 4638743) B4638743
theorem B2061663 : Blo 2061435 2061663 := bstep (se 1 (by rfl) ⟨1546247, by rfl⟩ : syracuseStep 2061663 = 3092495) B3092495
theorem B3092501 : Blo 2061435 3092501 := bbase (se 6 (by rfl) ⟨72480, by rfl⟩ : syracuseStep 3092501 = 144961) (by norm_num)
theorem B2061667 : Blo 2061435 2061667 := bstep (se 1 (by rfl) ⟨1546250, by rfl⟩ : syracuseStep 2061667 = 3092501) B3092501
theorem B3134701 : Blo 2061435 3134701 := bbase (se 3 (by rfl) ⟨587756, by rfl⟩ : syracuseStep 3134701 = 1175513) (by norm_num)
theorem B4179601 : Blo 2061435 4179601 := bstep (se 2 (by rfl) ⟨1567350, by rfl⟩ : syracuseStep 4179601 = 3134701) B3134701
theorem B5572801 : Blo 2061435 5572801 := bstep (se 2 (by rfl) ⟨2089800, by rfl⟩ : syracuseStep 5572801 = 4179601) B4179601
theorem B7430401 : Blo 2061435 7430401 := bstep (se 2 (by rfl) ⟨2786400, by rfl⟩ : syracuseStep 7430401 = 5572801) B5572801
theorem B9907201 : Blo 2061435 9907201 := bstep (se 2 (by rfl) ⟨3715200, by rfl⟩ : syracuseStep 9907201 = 7430401) B7430401
theorem B13209601 : Blo 2061435 13209601 := bstep (se 2 (by rfl) ⟨4953600, by rfl⟩ : syracuseStep 13209601 = 9907201) B9907201
theorem B17612801 : Blo 2061435 17612801 := bstep (se 2 (by rfl) ⟨6604800, by rfl⟩ : syracuseStep 17612801 = 13209601) B13209601
theorem B11741867 : Blo 2061435 11741867 := bstep (se 1 (by rfl) ⟨8806400, by rfl⟩ : syracuseStep 11741867 = 17612801) B17612801
theorem B7827911 : Blo 2061435 7827911 := bstep (se 1 (by rfl) ⟨5870933, by rfl⟩ : syracuseStep 7827911 = 11741867) B11741867
theorem B5218607 : Blo 2061435 5218607 := bstep (se 1 (by rfl) ⟨3913955, by rfl⟩ : syracuseStep 5218607 = 7827911) B7827911
theorem B3479071 : Blo 2061435 3479071 := bstep (se 1 (by rfl) ⟨2609303, by rfl⟩ : syracuseStep 3479071 = 5218607) B5218607
theorem B4638761 : Blo 2061435 4638761 := bstep (se 2 (by rfl) ⟨1739535, by rfl⟩ : syracuseStep 4638761 = 3479071) B3479071
theorem B3092507 : Blo 2061435 3092507 := bstep (se 1 (by rfl) ⟨2319380, by rfl⟩ : syracuseStep 3092507 = 4638761) B4638761
theorem B2061671 : Blo 2061435 2061671 := bstep (se 1 (by rfl) ⟨1546253, by rfl⟩ : syracuseStep 2061671 = 3092507) B3092507
theorem B2319385 : Blo 2061435 2319385 := bbase (se 2 (by rfl) ⟨869769, by rfl⟩ : syracuseStep 2319385 = 1739539) (by norm_num)
theorem B3092513 : Blo 2061435 3092513 := bstep (se 2 (by rfl) ⟨1159692, by rfl⟩ : syracuseStep 3092513 = 2319385) B2319385
theorem B2061675 : Blo 2061435 2061675 := bstep (se 1 (by rfl) ⟨1546256, by rfl⟩ : syracuseStep 2061675 = 3092513) B3092513
theorem B7827941 : Blo 2061435 7827941 := bbase (se 4 (by rfl) ⟨733869, by rfl⟩ : syracuseStep 7827941 = 1467739) (by norm_num)
theorem B5218627 : Blo 2061435 5218627 := bstep (se 1 (by rfl) ⟨3913970, by rfl⟩ : syracuseStep 5218627 = 7827941) B7827941
theorem B6958169 : Blo 2061435 6958169 := bstep (se 2 (by rfl) ⟨2609313, by rfl⟩ : syracuseStep 6958169 = 5218627) B5218627
theorem B4638779 : Blo 2061435 4638779 := bstep (se 1 (by rfl) ⟨3479084, by rfl⟩ : syracuseStep 4638779 = 6958169) B6958169
theorem B3092519 : Blo 2061435 3092519 := bstep (se 1 (by rfl) ⟨2319389, by rfl⟩ : syracuseStep 3092519 = 4638779) B4638779
theorem B2061679 : Blo 2061435 2061679 := bstep (se 1 (by rfl) ⟨1546259, by rfl⟩ : syracuseStep 2061679 = 3092519) B3092519
theorem B3092525 : Blo 2061435 3092525 := bbase (se 3 (by rfl) ⟨579848, by rfl⟩ : syracuseStep 3092525 = 1159697) (by norm_num)
theorem B2061683 : Blo 2061435 2061683 := bstep (se 1 (by rfl) ⟨1546262, by rfl⟩ : syracuseStep 2061683 = 3092525) B3092525
theorem B4638797 : Blo 2061435 4638797 := bbase (se 3 (by rfl) ⟨869774, by rfl⟩ : syracuseStep 4638797 = 1739549) (by norm_num)
theorem B3092531 : Blo 2061435 3092531 := bstep (se 1 (by rfl) ⟨2319398, by rfl⟩ : syracuseStep 3092531 = 4638797) B4638797
theorem B2061687 : Blo 2061435 2061687 := bstep (se 1 (by rfl) ⟨1546265, by rfl⟩ : syracuseStep 2061687 = 3092531) B3092531
theorem B2609329 : Blo 2061435 2609329 := bbase (se 2 (by rfl) ⟨978498, by rfl⟩ : syracuseStep 2609329 = 1956997) (by norm_num)
theorem B3479105 : Blo 2061435 3479105 := bstep (se 2 (by rfl) ⟨1304664, by rfl⟩ : syracuseStep 3479105 = 2609329) B2609329
theorem B2319403 : Blo 2061435 2319403 := bstep (se 1 (by rfl) ⟨1739552, by rfl⟩ : syracuseStep 2319403 = 3479105) B3479105
theorem B3092537 : Blo 2061435 3092537 := bstep (se 2 (by rfl) ⟨1159701, by rfl⟩ : syracuseStep 3092537 = 2319403) B2319403
theorem B2061691 : Blo 2061435 2061691 := bstep (se 1 (by rfl) ⟨1546268, by rfl⟩ : syracuseStep 2061691 = 3092537) B3092537
theorem B2476829 : Blo 2061435 2476829 := bbase (se 3 (by rfl) ⟨464405, by rfl⟩ : syracuseStep 2476829 = 928811) (by norm_num)
theorem B6604877 : Blo 2061435 6604877 := bstep (se 3 (by rfl) ⟨1238414, by rfl⟩ : syracuseStep 6604877 = 2476829) B2476829
theorem B4403251 : Blo 2061435 4403251 := bstep (se 1 (by rfl) ⟨3302438, by rfl⟩ : syracuseStep 4403251 = 6604877) B6604877
theorem B23484005 : Blo 2061435 23484005 := bstep (se 4 (by rfl) ⟨2201625, by rfl⟩ : syracuseStep 23484005 = 4403251) B4403251
theorem B15656003 : Blo 2061435 15656003 := bstep (se 1 (by rfl) ⟨11742002, by rfl⟩ : syracuseStep 15656003 = 23484005) B23484005
theorem B10437335 : Blo 2061435 10437335 := bstep (se 1 (by rfl) ⟨7828001, by rfl⟩ : syracuseStep 10437335 = 15656003) B15656003
theorem B6958223 : Blo 2061435 6958223 := bstep (se 1 (by rfl) ⟨5218667, by rfl⟩ : syracuseStep 6958223 = 10437335) B10437335
theorem B4638815 : Blo 2061435 4638815 := bstep (se 1 (by rfl) ⟨3479111, by rfl⟩ : syracuseStep 4638815 = 6958223) B6958223
theorem B3092543 : Blo 2061435 3092543 := bstep (se 1 (by rfl) ⟨2319407, by rfl⟩ : syracuseStep 3092543 = 4638815) B4638815
theorem B2061695 : Blo 2061435 2061695 := bstep (se 1 (by rfl) ⟨1546271, by rfl⟩ : syracuseStep 2061695 = 3092543) B3092543
theorem B3092549 : Blo 2061435 3092549 := bbase (se 4 (by rfl) ⟨289926, by rfl⟩ : syracuseStep 3092549 = 579853) (by norm_num)
theorem B2061699 : Blo 2061435 2061699 := bstep (se 1 (by rfl) ⟨1546274, by rfl⟩ : syracuseStep 2061699 = 3092549) B3092549
theorem B3479125 : Blo 2061435 3479125 := bbase (se 8 (by rfl) ⟨20385, by rfl⟩ : syracuseStep 3479125 = 40771) (by norm_num)
theorem B4638833 : Blo 2061435 4638833 := bstep (se 2 (by rfl) ⟨1739562, by rfl⟩ : syracuseStep 4638833 = 3479125) B3479125
theorem B3092555 : Blo 2061435 3092555 := bstep (se 1 (by rfl) ⟨2319416, by rfl⟩ : syracuseStep 3092555 = 4638833) B4638833
theorem B2061703 : Blo 2061435 2061703 := bstep (se 1 (by rfl) ⟨1546277, by rfl⟩ : syracuseStep 2061703 = 3092555) B3092555
theorem B2319421 : Blo 2061435 2319421 := bbase (se 3 (by rfl) ⟨434891, by rfl⟩ : syracuseStep 2319421 = 869783) (by norm_num)
theorem B3092561 : Blo 2061435 3092561 := bstep (se 2 (by rfl) ⟨1159710, by rfl⟩ : syracuseStep 3092561 = 2319421) B2319421
theorem B2061707 : Blo 2061435 2061707 := bstep (se 1 (by rfl) ⟨1546280, by rfl⟩ : syracuseStep 2061707 = 3092561) B3092561
theorem B6958277 : Blo 2061435 6958277 := bbase (se 4 (by rfl) ⟨652338, by rfl⟩ : syracuseStep 6958277 = 1304677) (by norm_num)
theorem B4638851 : Blo 2061435 4638851 := bstep (se 1 (by rfl) ⟨3479138, by rfl⟩ : syracuseStep 4638851 = 6958277) B6958277
theorem B3092567 : Blo 2061435 3092567 := bstep (se 1 (by rfl) ⟨2319425, by rfl⟩ : syracuseStep 3092567 = 4638851) B4638851
theorem B2061711 : Blo 2061435 2061711 := bstep (se 1 (by rfl) ⟨1546283, by rfl⟩ : syracuseStep 2061711 = 3092567) B3092567
theorem B3092573 : Blo 2061435 3092573 := bbase (se 3 (by rfl) ⟨579857, by rfl⟩ : syracuseStep 3092573 = 1159715) (by norm_num)
theorem B2061715 : Blo 2061435 2061715 := bstep (se 1 (by rfl) ⟨1546286, by rfl⟩ : syracuseStep 2061715 = 3092573) B3092573
theorem B4638869 : Blo 2061435 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B3092579 : Blo 2061435 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B2061719 : Blo 2061435 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B2935541 : Blo 2061435 2935541 := bbase (se 5 (by rfl) ⟨137603, by rfl⟩ : syracuseStep 2935541 = 275207) (by norm_num)
theorem B7828109 : Blo 2061435 7828109 := bstep (se 3 (by rfl) ⟨1467770, by rfl⟩ : syracuseStep 7828109 = 2935541) B2935541
theorem B5218739 : Blo 2061435 5218739 := bstep (se 1 (by rfl) ⟨3914054, by rfl⟩ : syracuseStep 5218739 = 7828109) B7828109
theorem B3479159 : Blo 2061435 3479159 := bstep (se 1 (by rfl) ⟨2609369, by rfl⟩ : syracuseStep 3479159 = 5218739) B5218739
theorem B2319439 : Blo 2061435 2319439 := bstep (se 1 (by rfl) ⟨1739579, by rfl⟩ : syracuseStep 2319439 = 3479159) B3479159
theorem B3092585 : Blo 2061435 3092585 := bstep (se 2 (by rfl) ⟨1159719, by rfl⟩ : syracuseStep 3092585 = 2319439) B2319439
theorem B2061723 : Blo 2061435 2061723 := bstep (se 1 (by rfl) ⟨1546292, by rfl⟩ : syracuseStep 2061723 = 3092585) B3092585
theorem B3817373 : Blo 2061435 3817373 := bbase (se 3 (by rfl) ⟨715757, by rfl⟩ : syracuseStep 3817373 = 1431515) (by norm_num)
theorem B40718645 : Blo 2061435 40718645 := bstep (se 5 (by rfl) ⟨1908686, by rfl⟩ : syracuseStep 40718645 = 3817373) B3817373
theorem B27145763 : Blo 2061435 27145763 := bstep (se 1 (by rfl) ⟨20359322, by rfl⟩ : syracuseStep 27145763 = 40718645) B40718645
theorem B18097175 : Blo 2061435 18097175 := bstep (se 1 (by rfl) ⟨13572881, by rfl⟩ : syracuseStep 18097175 = 27145763) B27145763
theorem B12064783 : Blo 2061435 12064783 := bstep (se 1 (by rfl) ⟨9048587, by rfl⟩ : syracuseStep 12064783 = 18097175) B18097175
theorem B16086377 : Blo 2061435 16086377 := bstep (se 2 (by rfl) ⟨6032391, by rfl⟩ : syracuseStep 16086377 = 12064783) B12064783
theorem B10724251 : Blo 2061435 10724251 := bstep (se 1 (by rfl) ⟨8043188, by rfl⟩ : syracuseStep 10724251 = 16086377) B16086377
theorem B14299001 : Blo 2061435 14299001 := bstep (se 2 (by rfl) ⟨5362125, by rfl⟩ : syracuseStep 14299001 = 10724251) B10724251
theorem B9532667 : Blo 2061435 9532667 := bstep (se 1 (by rfl) ⟨7149500, by rfl⟩ : syracuseStep 9532667 = 14299001) B14299001
theorem B6355111 : Blo 2061435 6355111 := bstep (se 1 (by rfl) ⟨4766333, by rfl⟩ : syracuseStep 6355111 = 9532667) B9532667
theorem B8473481 : Blo 2061435 8473481 := bstep (se 2 (by rfl) ⟨3177555, by rfl⟩ : syracuseStep 8473481 = 6355111) B6355111
theorem B5648987 : Blo 2061435 5648987 := bstep (se 1 (by rfl) ⟨4236740, by rfl⟩ : syracuseStep 5648987 = 8473481) B8473481
theorem B15063965 : Blo 2061435 15063965 := bstep (se 3 (by rfl) ⟨2824493, by rfl⟩ : syracuseStep 15063965 = 5648987) B5648987
theorem B10042643 : Blo 2061435 10042643 := bstep (se 1 (by rfl) ⟨7531982, by rfl⟩ : syracuseStep 10042643 = 15063965) B15063965
theorem B6695095 : Blo 2061435 6695095 := bstep (se 1 (by rfl) ⟨5021321, by rfl⟩ : syracuseStep 6695095 = 10042643) B10042643
theorem B8926793 : Blo 2061435 8926793 := bstep (se 2 (by rfl) ⟨3347547, by rfl⟩ : syracuseStep 8926793 = 6695095) B6695095
theorem B5951195 : Blo 2061435 5951195 := bstep (se 1 (by rfl) ⟨4463396, by rfl⟩ : syracuseStep 5951195 = 8926793) B8926793
theorem B3967463 : Blo 2061435 3967463 := bstep (se 1 (by rfl) ⟨2975597, by rfl⟩ : syracuseStep 3967463 = 5951195) B5951195
theorem B10579901 : Blo 2061435 10579901 := bstep (se 3 (by rfl) ⟨1983731, by rfl⟩ : syracuseStep 10579901 = 3967463) B3967463
theorem B112852277 : Blo 2061435 112852277 := bstep (se 5 (by rfl) ⟨5289950, by rfl⟩ : syracuseStep 112852277 = 10579901) B10579901
theorem B75234851 : Blo 2061435 75234851 := bstep (se 1 (by rfl) ⟨56426138, by rfl⟩ : syracuseStep 75234851 = 112852277) B112852277
theorem B50156567 : Blo 2061435 50156567 := bstep (se 1 (by rfl) ⟨37617425, by rfl⟩ : syracuseStep 50156567 = 75234851) B75234851
theorem B33437711 : Blo 2061435 33437711 := bstep (se 1 (by rfl) ⟨25078283, by rfl⟩ : syracuseStep 33437711 = 50156567) B50156567
theorem B22291807 : Blo 2061435 22291807 := bstep (se 1 (by rfl) ⟨16718855, by rfl⟩ : syracuseStep 22291807 = 33437711) B33437711
theorem B29722409 : Blo 2061435 29722409 := bstep (se 2 (by rfl) ⟨11145903, by rfl⟩ : syracuseStep 29722409 = 22291807) B22291807
theorem B19814939 : Blo 2061435 19814939 := bstep (se 1 (by rfl) ⟨14861204, by rfl⟩ : syracuseStep 19814939 = 29722409) B29722409
theorem B13209959 : Blo 2061435 13209959 := bstep (se 1 (by rfl) ⟨9907469, by rfl⟩ : syracuseStep 13209959 = 19814939) B19814939
theorem B8806639 : Blo 2061435 8806639 := bstep (se 1 (by rfl) ⟨6604979, by rfl⟩ : syracuseStep 8806639 = 13209959) B13209959
theorem B11742185 : Blo 2061435 11742185 := bstep (se 2 (by rfl) ⟨4403319, by rfl⟩ : syracuseStep 11742185 = 8806639) B8806639
theorem B7828123 : Blo 2061435 7828123 := bstep (se 1 (by rfl) ⟨5871092, by rfl⟩ : syracuseStep 7828123 = 11742185) B11742185
theorem B10437497 : Blo 2061435 10437497 := bstep (se 2 (by rfl) ⟨3914061, by rfl⟩ : syracuseStep 10437497 = 7828123) B7828123
theorem B6958331 : Blo 2061435 6958331 := bstep (se 1 (by rfl) ⟨5218748, by rfl⟩ : syracuseStep 6958331 = 10437497) B10437497
theorem B4638887 : Blo 2061435 4638887 := bstep (se 1 (by rfl) ⟨3479165, by rfl⟩ : syracuseStep 4638887 = 6958331) B6958331
theorem B3092591 : Blo 2061435 3092591 := bstep (se 1 (by rfl) ⟨2319443, by rfl⟩ : syracuseStep 3092591 = 4638887) B4638887
theorem B2061727 : Blo 2061435 2061727 := bstep (se 1 (by rfl) ⟨1546295, by rfl⟩ : syracuseStep 2061727 = 3092591) B3092591
theorem B3092597 : Blo 2061435 3092597 := bbase (se 5 (by rfl) ⟨144965, by rfl⟩ : syracuseStep 3092597 = 289931) (by norm_num)
theorem B2061731 : Blo 2061435 2061731 := bstep (se 1 (by rfl) ⟨1546298, by rfl⟩ : syracuseStep 2061731 = 3092597) B3092597
theorem B3914077 : Blo 2061435 3914077 := bbase (se 3 (by rfl) ⟨733889, by rfl⟩ : syracuseStep 3914077 = 1467779) (by norm_num)
theorem B5218769 : Blo 2061435 5218769 := bstep (se 2 (by rfl) ⟨1957038, by rfl⟩ : syracuseStep 5218769 = 3914077) B3914077
theorem B3479179 : Blo 2061435 3479179 := bstep (se 1 (by rfl) ⟨2609384, by rfl⟩ : syracuseStep 3479179 = 5218769) B5218769
theorem B4638905 : Blo 2061435 4638905 := bstep (se 2 (by rfl) ⟨1739589, by rfl⟩ : syracuseStep 4638905 = 3479179) B3479179
theorem B3092603 : Blo 2061435 3092603 := bstep (se 1 (by rfl) ⟨2319452, by rfl⟩ : syracuseStep 3092603 = 4638905) B4638905
theorem B2061735 : Blo 2061435 2061735 := bstep (se 1 (by rfl) ⟨1546301, by rfl⟩ : syracuseStep 2061735 = 3092603) B3092603
theorem B2319457 : Blo 2061435 2319457 := bbase (se 2 (by rfl) ⟨869796, by rfl⟩ : syracuseStep 2319457 = 1739593) (by norm_num)
theorem B3092609 : Blo 2061435 3092609 := bstep (se 2 (by rfl) ⟨1159728, by rfl⟩ : syracuseStep 3092609 = 2319457) B2319457
theorem B2061739 : Blo 2061435 2061739 := bstep (se 1 (by rfl) ⟨1546304, by rfl⟩ : syracuseStep 2061739 = 3092609) B3092609
theorem B5218789 : Blo 2061435 5218789 := bbase (se 4 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 5218789 = 978523) (by norm_num)
theorem B6958385 : Blo 2061435 6958385 := bstep (se 2 (by rfl) ⟨2609394, by rfl⟩ : syracuseStep 6958385 = 5218789) B5218789
theorem B4638923 : Blo 2061435 4638923 := bstep (se 1 (by rfl) ⟨3479192, by rfl⟩ : syracuseStep 4638923 = 6958385) B6958385
theorem B3092615 : Blo 2061435 3092615 := bstep (se 1 (by rfl) ⟨2319461, by rfl⟩ : syracuseStep 3092615 = 4638923) B4638923
theorem B2061743 : Blo 2061435 2061743 := bstep (se 1 (by rfl) ⟨1546307, by rfl⟩ : syracuseStep 2061743 = 3092615) B3092615
theorem B3092621 : Blo 2061435 3092621 := bbase (se 3 (by rfl) ⟨579866, by rfl⟩ : syracuseStep 3092621 = 1159733) (by norm_num)
theorem B2061747 : Blo 2061435 2061747 := bstep (se 1 (by rfl) ⟨1546310, by rfl⟩ : syracuseStep 2061747 = 3092621) B3092621
theorem B4638941 : Blo 2061435 4638941 := bbase (se 3 (by rfl) ⟨869801, by rfl⟩ : syracuseStep 4638941 = 1739603) (by norm_num)
theorem B3092627 : Blo 2061435 3092627 := bstep (se 1 (by rfl) ⟨2319470, by rfl⟩ : syracuseStep 3092627 = 4638941) B4638941
theorem B2061751 : Blo 2061435 2061751 := bstep (se 1 (by rfl) ⟨1546313, by rfl⟩ : syracuseStep 2061751 = 3092627) B3092627
theorem B3479213 : Blo 2061435 3479213 := bbase (se 3 (by rfl) ⟨652352, by rfl⟩ : syracuseStep 3479213 = 1304705) (by norm_num)
theorem B2319475 : Blo 2061435 2319475 := bstep (se 1 (by rfl) ⟨1739606, by rfl⟩ : syracuseStep 2319475 = 3479213) B3479213
theorem B3092633 : Blo 2061435 3092633 := bstep (se 2 (by rfl) ⟨1159737, by rfl⟩ : syracuseStep 3092633 = 2319475) B2319475
theorem B2061755 : Blo 2061435 2061755 := bstep (se 1 (by rfl) ⟨1546316, by rfl⟩ : syracuseStep 2061755 = 3092633) B3092633
theorem B3177605 : Blo 2061435 3177605 := bbase (se 4 (by rfl) ⟨297900, by rfl⟩ : syracuseStep 3177605 = 595801) (by norm_num)
theorem B2118403 : Blo 2061435 2118403 := bstep (se 1 (by rfl) ⟨1588802, by rfl⟩ : syracuseStep 2118403 = 3177605) B3177605
theorem B2824537 : Blo 2061435 2824537 := bstep (se 2 (by rfl) ⟨1059201, by rfl⟩ : syracuseStep 2824537 = 2118403) B2118403
theorem B3766049 : Blo 2061435 3766049 := bstep (se 2 (by rfl) ⟨1412268, by rfl⟩ : syracuseStep 3766049 = 2824537) B2824537
theorem B2510699 : Blo 2061435 2510699 := bstep (se 1 (by rfl) ⟨1883024, by rfl⟩ : syracuseStep 2510699 = 3766049) B3766049
theorem B26780789 : Blo 2061435 26780789 := bstep (se 5 (by rfl) ⟨1255349, by rfl⟩ : syracuseStep 26780789 = 2510699) B2510699
theorem B17853859 : Blo 2061435 17853859 := bstep (se 1 (by rfl) ⟨13390394, by rfl⟩ : syracuseStep 17853859 = 26780789) B26780789
theorem B23805145 : Blo 2061435 23805145 := bstep (se 2 (by rfl) ⟨8926929, by rfl⟩ : syracuseStep 23805145 = 17853859) B17853859
theorem B31740193 : Blo 2061435 31740193 := bstep (se 2 (by rfl) ⟨11902572, by rfl⟩ : syracuseStep 31740193 = 23805145) B23805145
theorem B169281029 : Blo 2061435 169281029 := bstep (se 4 (by rfl) ⟨15870096, by rfl⟩ : syracuseStep 169281029 = 31740193) B31740193
theorem B112854019 : Blo 2061435 112854019 := bstep (se 1 (by rfl) ⟨84640514, by rfl⟩ : syracuseStep 112854019 = 169281029) B169281029
theorem B150472025 : Blo 2061435 150472025 := bstep (se 2 (by rfl) ⟨56427009, by rfl⟩ : syracuseStep 150472025 = 112854019) B112854019
theorem B100314683 : Blo 2061435 100314683 := bstep (se 1 (by rfl) ⟨75236012, by rfl⟩ : syracuseStep 100314683 = 150472025) B150472025
theorem B66876455 : Blo 2061435 66876455 := bstep (se 1 (by rfl) ⟨50157341, by rfl⟩ : syracuseStep 66876455 = 100314683) B100314683
theorem B44584303 : Blo 2061435 44584303 := bstep (se 1 (by rfl) ⟨33438227, by rfl⟩ : syracuseStep 44584303 = 66876455) B66876455
theorem B59445737 : Blo 2061435 59445737 := bstep (se 2 (by rfl) ⟨22292151, by rfl⟩ : syracuseStep 59445737 = 44584303) B44584303
theorem B39630491 : Blo 2061435 39630491 := bstep (se 1 (by rfl) ⟨29722868, by rfl⟩ : syracuseStep 39630491 = 59445737) B59445737
theorem B26420327 : Blo 2061435 26420327 := bstep (se 1 (by rfl) ⟨19815245, by rfl⟩ : syracuseStep 26420327 = 39630491) B39630491
theorem B17613551 : Blo 2061435 17613551 := bstep (se 1 (by rfl) ⟨13210163, by rfl⟩ : syracuseStep 17613551 = 26420327) B26420327
theorem B11742367 : Blo 2061435 11742367 := bstep (se 1 (by rfl) ⟨8806775, by rfl⟩ : syracuseStep 11742367 = 17613551) B17613551
theorem B15656489 : Blo 2061435 15656489 := bstep (se 2 (by rfl) ⟨5871183, by rfl⟩ : syracuseStep 15656489 = 11742367) B11742367
theorem B10437659 : Blo 2061435 10437659 := bstep (se 1 (by rfl) ⟨7828244, by rfl⟩ : syracuseStep 10437659 = 15656489) B15656489
theorem B6958439 : Blo 2061435 6958439 := bstep (se 1 (by rfl) ⟨5218829, by rfl⟩ : syracuseStep 6958439 = 10437659) B10437659
theorem B4638959 : Blo 2061435 4638959 := bstep (se 1 (by rfl) ⟨3479219, by rfl⟩ : syracuseStep 4638959 = 6958439) B6958439
theorem B3092639 : Blo 2061435 3092639 := bstep (se 1 (by rfl) ⟨2319479, by rfl⟩ : syracuseStep 3092639 = 4638959) B4638959
theorem B2061759 : Blo 2061435 2061759 := bstep (se 1 (by rfl) ⟨1546319, by rfl⟩ : syracuseStep 2061759 = 3092639) B3092639
theorem B3092645 : Blo 2061435 3092645 := bbase (se 4 (by rfl) ⟨289935, by rfl⟩ : syracuseStep 3092645 = 579871) (by norm_num)
theorem B2061763 : Blo 2061435 2061763 := bstep (se 1 (by rfl) ⟨1546322, by rfl⟩ : syracuseStep 2061763 = 3092645) B3092645
theorem B2609425 : Blo 2061435 2609425 := bbase (se 2 (by rfl) ⟨978534, by rfl⟩ : syracuseStep 2609425 = 1957069) (by norm_num)
theorem B3479233 : Blo 2061435 3479233 := bstep (se 2 (by rfl) ⟨1304712, by rfl⟩ : syracuseStep 3479233 = 2609425) B2609425
theorem B4638977 : Blo 2061435 4638977 := bstep (se 2 (by rfl) ⟨1739616, by rfl⟩ : syracuseStep 4638977 = 3479233) B3479233
theorem B3092651 : Blo 2061435 3092651 := bstep (se 1 (by rfl) ⟨2319488, by rfl⟩ : syracuseStep 3092651 = 4638977) B4638977
theorem B2061767 : Blo 2061435 2061767 := bstep (se 1 (by rfl) ⟨1546325, by rfl⟩ : syracuseStep 2061767 = 3092651) B3092651
theorem B2319493 : Blo 2061435 2319493 := bbase (se 4 (by rfl) ⟨217452, by rfl⟩ : syracuseStep 2319493 = 434905) (by norm_num)
theorem B3092657 : Blo 2061435 3092657 := bstep (se 2 (by rfl) ⟨1159746, by rfl⟩ : syracuseStep 3092657 = 2319493) B2319493
theorem B2061771 : Blo 2061435 2061771 := bstep (se 1 (by rfl) ⟨1546328, by rfl⟩ : syracuseStep 2061771 = 3092657) B3092657
theorem B14106869 : Blo 2061435 14106869 := bbase (se 5 (by rfl) ⟨661259, by rfl⟩ : syracuseStep 14106869 = 1322519) (by norm_num)
theorem B9404579 : Blo 2061435 9404579 := bstep (se 1 (by rfl) ⟨7053434, by rfl⟩ : syracuseStep 9404579 = 14106869) B14106869
theorem B6269719 : Blo 2061435 6269719 := bstep (se 1 (by rfl) ⟨4702289, by rfl⟩ : syracuseStep 6269719 = 9404579) B9404579
theorem B8359625 : Blo 2061435 8359625 := bstep (se 2 (by rfl) ⟨3134859, by rfl⟩ : syracuseStep 8359625 = 6269719) B6269719
theorem B22292333 : Blo 2061435 22292333 := bstep (se 3 (by rfl) ⟨4179812, by rfl⟩ : syracuseStep 22292333 = 8359625) B8359625
theorem B14861555 : Blo 2061435 14861555 := bstep (se 1 (by rfl) ⟨11146166, by rfl⟩ : syracuseStep 14861555 = 22292333) B22292333
theorem B9907703 : Blo 2061435 9907703 := bstep (se 1 (by rfl) ⟨7430777, by rfl⟩ : syracuseStep 9907703 = 14861555) B14861555
theorem B6605135 : Blo 2061435 6605135 := bstep (se 1 (by rfl) ⟨4953851, by rfl⟩ : syracuseStep 6605135 = 9907703) B9907703
theorem B4403423 : Blo 2061435 4403423 := bstep (se 1 (by rfl) ⟨3302567, by rfl⟩ : syracuseStep 4403423 = 6605135) B6605135
theorem B2935615 : Blo 2061435 2935615 := bstep (se 1 (by rfl) ⟨2201711, by rfl⟩ : syracuseStep 2935615 = 4403423) B4403423
theorem B3914153 : Blo 2061435 3914153 := bstep (se 2 (by rfl) ⟨1467807, by rfl⟩ : syracuseStep 3914153 = 2935615) B2935615
theorem B2609435 : Blo 2061435 2609435 := bstep (se 1 (by rfl) ⟨1957076, by rfl⟩ : syracuseStep 2609435 = 3914153) B3914153
theorem B6958493 : Blo 2061435 6958493 := bstep (se 3 (by rfl) ⟨1304717, by rfl⟩ : syracuseStep 6958493 = 2609435) B2609435
theorem B4638995 : Blo 2061435 4638995 := bstep (se 1 (by rfl) ⟨3479246, by rfl⟩ : syracuseStep 4638995 = 6958493) B6958493
theorem B3092663 : Blo 2061435 3092663 := bstep (se 1 (by rfl) ⟨2319497, by rfl⟩ : syracuseStep 3092663 = 4638995) B4638995
theorem B2061775 : Blo 2061435 2061775 := bstep (se 1 (by rfl) ⟨1546331, by rfl⟩ : syracuseStep 2061775 = 3092663) B3092663
theorem B3092669 : Blo 2061435 3092669 := bbase (se 3 (by rfl) ⟨579875, by rfl⟩ : syracuseStep 3092669 = 1159751) (by norm_num)
theorem B2061779 : Blo 2061435 2061779 := bstep (se 1 (by rfl) ⟨1546334, by rfl⟩ : syracuseStep 2061779 = 3092669) B3092669
theorem B4639013 : Blo 2061435 4639013 := bbase (se 4 (by rfl) ⟨434907, by rfl⟩ : syracuseStep 4639013 = 869815) (by norm_num)
theorem B3092675 : Blo 2061435 3092675 := bstep (se 1 (by rfl) ⟨2319506, by rfl⟩ : syracuseStep 3092675 = 4639013) B4639013
theorem B2061783 : Blo 2061435 2061783 := bstep (se 1 (by rfl) ⟨1546337, by rfl⟩ : syracuseStep 2061783 = 3092675) B3092675
theorem B5218901 : Blo 2061435 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B3479267 : Blo 2061435 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B2319511 : Blo 2061435 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B3092681 : Blo 2061435 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B2061787 : Blo 2061435 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B4179845 : Blo 2061435 4179845 := bbase (se 4 (by rfl) ⟨391860, by rfl⟩ : syracuseStep 4179845 = 783721) (by norm_num)
theorem B2786563 : Blo 2061435 2786563 := bstep (se 1 (by rfl) ⟨2089922, by rfl⟩ : syracuseStep 2786563 = 4179845) B4179845
theorem B3715417 : Blo 2061435 3715417 := bstep (se 2 (by rfl) ⟨1393281, by rfl⟩ : syracuseStep 3715417 = 2786563) B2786563
theorem B4953889 : Blo 2061435 4953889 := bstep (se 2 (by rfl) ⟨1857708, by rfl⟩ : syracuseStep 4953889 = 3715417) B3715417
theorem B6605185 : Blo 2061435 6605185 := bstep (se 2 (by rfl) ⟨2476944, by rfl⟩ : syracuseStep 6605185 = 4953889) B4953889
theorem B8806913 : Blo 2061435 8806913 := bstep (se 2 (by rfl) ⟨3302592, by rfl⟩ : syracuseStep 8806913 = 6605185) B6605185
theorem B5871275 : Blo 2061435 5871275 := bstep (se 1 (by rfl) ⟨4403456, by rfl⟩ : syracuseStep 5871275 = 8806913) B8806913
theorem B3914183 : Blo 2061435 3914183 := bstep (se 1 (by rfl) ⟨2935637, by rfl⟩ : syracuseStep 3914183 = 5871275) B5871275
theorem B10437821 : Blo 2061435 10437821 := bstep (se 3 (by rfl) ⟨1957091, by rfl⟩ : syracuseStep 10437821 = 3914183) B3914183
theorem B6958547 : Blo 2061435 6958547 := bstep (se 1 (by rfl) ⟨5218910, by rfl⟩ : syracuseStep 6958547 = 10437821) B10437821
theorem B4639031 : Blo 2061435 4639031 := bstep (se 1 (by rfl) ⟨3479273, by rfl⟩ : syracuseStep 4639031 = 6958547) B6958547
theorem B3092687 : Blo 2061435 3092687 := bstep (se 1 (by rfl) ⟨2319515, by rfl⟩ : syracuseStep 3092687 = 4639031) B4639031
theorem B2061791 : Blo 2061435 2061791 := bstep (se 1 (by rfl) ⟨1546343, by rfl⟩ : syracuseStep 2061791 = 3092687) B3092687
theorem B3092693 : Blo 2061435 3092693 := bbase (se 7 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 3092693 = 72485) (by norm_num)
theorem B2061795 : Blo 2061435 2061795 := bstep (se 1 (by rfl) ⟨1546346, by rfl⟩ : syracuseStep 2061795 = 3092693) B3092693
theorem B2201737 : Blo 2061435 2201737 := bbase (se 2 (by rfl) ⟨825651, by rfl⟩ : syracuseStep 2201737 = 1651303) (by norm_num)
theorem B2935649 : Blo 2061435 2935649 := bstep (se 2 (by rfl) ⟨1100868, by rfl⟩ : syracuseStep 2935649 = 2201737) B2201737
theorem B7828397 : Blo 2061435 7828397 := bstep (se 3 (by rfl) ⟨1467824, by rfl⟩ : syracuseStep 7828397 = 2935649) B2935649
theorem B5218931 : Blo 2061435 5218931 := bstep (se 1 (by rfl) ⟨3914198, by rfl⟩ : syracuseStep 5218931 = 7828397) B7828397
theorem B3479287 : Blo 2061435 3479287 := bstep (se 1 (by rfl) ⟨2609465, by rfl⟩ : syracuseStep 3479287 = 5218931) B5218931
theorem B4639049 : Blo 2061435 4639049 := bstep (se 2 (by rfl) ⟨1739643, by rfl⟩ : syracuseStep 4639049 = 3479287) B3479287
theorem B3092699 : Blo 2061435 3092699 := bstep (se 1 (by rfl) ⟨2319524, by rfl⟩ : syracuseStep 3092699 = 4639049) B4639049
theorem B2061799 : Blo 2061435 2061799 := bstep (se 1 (by rfl) ⟨1546349, by rfl⟩ : syracuseStep 2061799 = 3092699) B3092699
theorem B2319529 : Blo 2061435 2319529 := bbase (se 2 (by rfl) ⟨869823, by rfl⟩ : syracuseStep 2319529 = 1739647) (by norm_num)
theorem B3092705 : Blo 2061435 3092705 := bstep (se 2 (by rfl) ⟨1159764, by rfl⟩ : syracuseStep 3092705 = 2319529) B2319529
theorem B2061803 : Blo 2061435 2061803 := bstep (se 1 (by rfl) ⟨1546352, by rfl⟩ : syracuseStep 2061803 = 3092705) B3092705
theorem B8806981 : Blo 2061435 8806981 := bbase (se 4 (by rfl) ⟨825654, by rfl⟩ : syracuseStep 8806981 = 1651309) (by norm_num)
theorem B11742641 : Blo 2061435 11742641 := bstep (se 2 (by rfl) ⟨4403490, by rfl⟩ : syracuseStep 11742641 = 8806981) B8806981
theorem B7828427 : Blo 2061435 7828427 := bstep (se 1 (by rfl) ⟨5871320, by rfl⟩ : syracuseStep 7828427 = 11742641) B11742641
theorem B5218951 : Blo 2061435 5218951 := bstep (se 1 (by rfl) ⟨3914213, by rfl⟩ : syracuseStep 5218951 = 7828427) B7828427
theorem B6958601 : Blo 2061435 6958601 := bstep (se 2 (by rfl) ⟨2609475, by rfl⟩ : syracuseStep 6958601 = 5218951) B5218951
theorem B4639067 : Blo 2061435 4639067 := bstep (se 1 (by rfl) ⟨3479300, by rfl⟩ : syracuseStep 4639067 = 6958601) B6958601
theorem B3092711 : Blo 2061435 3092711 := bstep (se 1 (by rfl) ⟨2319533, by rfl⟩ : syracuseStep 3092711 = 4639067) B4639067
theorem B2061807 : Blo 2061435 2061807 := bstep (se 1 (by rfl) ⟨1546355, by rfl⟩ : syracuseStep 2061807 = 3092711) B3092711
theorem B3092717 : Blo 2061435 3092717 := bbase (se 3 (by rfl) ⟨579884, by rfl⟩ : syracuseStep 3092717 = 1159769) (by norm_num)
theorem B2061811 : Blo 2061435 2061811 := bstep (se 1 (by rfl) ⟨1546358, by rfl⟩ : syracuseStep 2061811 = 3092717) B3092717
theorem B4639085 : Blo 2061435 4639085 := bbase (se 3 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 4639085 = 1739657) (by norm_num)
theorem B3092723 : Blo 2061435 3092723 := bstep (se 1 (by rfl) ⟨2319542, by rfl⟩ : syracuseStep 3092723 = 4639085) B4639085
theorem B2061815 : Blo 2061435 2061815 := bstep (se 1 (by rfl) ⟨1546361, by rfl⟩ : syracuseStep 2061815 = 3092723) B3092723
theorem B3914237 : Blo 2061435 3914237 := bbase (se 3 (by rfl) ⟨733919, by rfl⟩ : syracuseStep 3914237 = 1467839) (by norm_num)
theorem B2609491 : Blo 2061435 2609491 := bstep (se 1 (by rfl) ⟨1957118, by rfl⟩ : syracuseStep 2609491 = 3914237) B3914237
theorem B3479321 : Blo 2061435 3479321 := bstep (se 2 (by rfl) ⟨1304745, by rfl⟩ : syracuseStep 3479321 = 2609491) B2609491
theorem B2319547 : Blo 2061435 2319547 := bstep (se 1 (by rfl) ⟨1739660, by rfl⟩ : syracuseStep 2319547 = 3479321) B3479321
theorem B3092729 : Blo 2061435 3092729 := bstep (se 2 (by rfl) ⟨1159773, by rfl⟩ : syracuseStep 3092729 = 2319547) B2319547
theorem B2061819 : Blo 2061435 2061819 := bstep (se 1 (by rfl) ⟨1546364, by rfl⟩ : syracuseStep 2061819 = 3092729) B3092729
theorem B4953965 : Blo 2061435 4953965 := bbase (se 3 (by rfl) ⟨928868, by rfl⟩ : syracuseStep 4953965 = 1857737) (by norm_num)
theorem B52842293 : Blo 2061435 52842293 := bstep (se 5 (by rfl) ⟨2476982, by rfl⟩ : syracuseStep 52842293 = 4953965) B4953965
theorem B35228195 : Blo 2061435 35228195 := bstep (se 1 (by rfl) ⟨26421146, by rfl⟩ : syracuseStep 35228195 = 52842293) B52842293
theorem B23485463 : Blo 2061435 23485463 := bstep (se 1 (by rfl) ⟨17614097, by rfl⟩ : syracuseStep 23485463 = 35228195) B35228195
theorem B15656975 : Blo 2061435 15656975 := bstep (se 1 (by rfl) ⟨11742731, by rfl⟩ : syracuseStep 15656975 = 23485463) B23485463
theorem B10437983 : Blo 2061435 10437983 := bstep (se 1 (by rfl) ⟨7828487, by rfl⟩ : syracuseStep 10437983 = 15656975) B15656975
theorem B6958655 : Blo 2061435 6958655 := bstep (se 1 (by rfl) ⟨5218991, by rfl⟩ : syracuseStep 6958655 = 10437983) B10437983
theorem B4639103 : Blo 2061435 4639103 := bstep (se 1 (by rfl) ⟨3479327, by rfl⟩ : syracuseStep 4639103 = 6958655) B6958655
theorem B3092735 : Blo 2061435 3092735 := bstep (se 1 (by rfl) ⟨2319551, by rfl⟩ : syracuseStep 3092735 = 4639103) B4639103
theorem B2061823 : Blo 2061435 2061823 := bstep (se 1 (by rfl) ⟨1546367, by rfl⟩ : syracuseStep 2061823 = 3092735) B3092735
theorem B3092741 : Blo 2061435 3092741 := bbase (se 4 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 3092741 = 579889) (by norm_num)
theorem B2061827 : Blo 2061435 2061827 := bstep (se 1 (by rfl) ⟨1546370, by rfl⟩ : syracuseStep 2061827 = 3092741) B3092741
theorem B3479341 : Blo 2061435 3479341 := bbase (se 3 (by rfl) ⟨652376, by rfl⟩ : syracuseStep 3479341 = 1304753) (by norm_num)
theorem B4639121 : Blo 2061435 4639121 := bstep (se 2 (by rfl) ⟨1739670, by rfl⟩ : syracuseStep 4639121 = 3479341) B3479341
theorem B3092747 : Blo 2061435 3092747 := bstep (se 1 (by rfl) ⟨2319560, by rfl⟩ : syracuseStep 3092747 = 4639121) B4639121
theorem B2061831 : Blo 2061435 2061831 := bstep (se 1 (by rfl) ⟨1546373, by rfl⟩ : syracuseStep 2061831 = 3092747) B3092747
theorem B2319565 : Blo 2061435 2319565 := bbase (se 3 (by rfl) ⟨434918, by rfl⟩ : syracuseStep 2319565 = 869837) (by norm_num)
theorem B3092753 : Blo 2061435 3092753 := bstep (se 2 (by rfl) ⟨1159782, by rfl⟩ : syracuseStep 3092753 = 2319565) B2319565
theorem B2061835 : Blo 2061435 2061835 := bstep (se 1 (by rfl) ⟨1546376, by rfl⟩ : syracuseStep 2061835 = 3092753) B3092753
theorem B6958709 : Blo 2061435 6958709 := bbase (se 5 (by rfl) ⟨326189, by rfl⟩ : syracuseStep 6958709 = 652379) (by norm_num)
theorem B4639139 : Blo 2061435 4639139 := bstep (se 1 (by rfl) ⟨3479354, by rfl⟩ : syracuseStep 4639139 = 6958709) B6958709
theorem B3092759 : Blo 2061435 3092759 := bstep (se 1 (by rfl) ⟨2319569, by rfl⟩ : syracuseStep 3092759 = 4639139) B4639139
theorem B2061839 : Blo 2061435 2061839 := bstep (se 1 (by rfl) ⟨1546379, by rfl⟩ : syracuseStep 2061839 = 3092759) B3092759
theorem B3092765 : Blo 2061435 3092765 := bbase (se 3 (by rfl) ⟨579893, by rfl⟩ : syracuseStep 3092765 = 1159787) (by norm_num)
theorem B2061843 : Blo 2061435 2061843 := bstep (se 1 (by rfl) ⟨1546382, by rfl⟩ : syracuseStep 2061843 = 3092765) B3092765
theorem B4639157 : Blo 2061435 4639157 := bbase (se 5 (by rfl) ⟨217460, by rfl⟩ : syracuseStep 4639157 = 434921) (by norm_num)
theorem B3092771 : Blo 2061435 3092771 := bstep (se 1 (by rfl) ⟨2319578, by rfl⟩ : syracuseStep 3092771 = 4639157) B4639157
theorem B2061847 : Blo 2061435 2061847 := bstep (se 1 (by rfl) ⟨1546385, by rfl⟩ : syracuseStep 2061847 = 3092771) B3092771
theorem B2477017 : Blo 2061435 2477017 := bbase (se 2 (by rfl) ⟨928881, by rfl⟩ : syracuseStep 2477017 = 1857763) (by norm_num)
theorem B3302689 : Blo 2061435 3302689 := bstep (se 2 (by rfl) ⟨1238508, by rfl⟩ : syracuseStep 3302689 = 2477017) B2477017
theorem B4403585 : Blo 2061435 4403585 := bstep (se 2 (by rfl) ⟨1651344, by rfl⟩ : syracuseStep 4403585 = 3302689) B3302689
theorem B11742893 : Blo 2061435 11742893 := bstep (se 3 (by rfl) ⟨2201792, by rfl⟩ : syracuseStep 11742893 = 4403585) B4403585
theorem B7828595 : Blo 2061435 7828595 := bstep (se 1 (by rfl) ⟨5871446, by rfl⟩ : syracuseStep 7828595 = 11742893) B11742893
theorem B5219063 : Blo 2061435 5219063 := bstep (se 1 (by rfl) ⟨3914297, by rfl⟩ : syracuseStep 5219063 = 7828595) B7828595
theorem B3479375 : Blo 2061435 3479375 := bstep (se 1 (by rfl) ⟨2609531, by rfl⟩ : syracuseStep 3479375 = 5219063) B5219063
theorem B2319583 : Blo 2061435 2319583 := bstep (se 1 (by rfl) ⟨1739687, by rfl⟩ : syracuseStep 2319583 = 3479375) B3479375
theorem B3092777 : Blo 2061435 3092777 := bstep (se 2 (by rfl) ⟨1159791, by rfl⟩ : syracuseStep 3092777 = 2319583) B2319583
theorem B2061851 : Blo 2061435 2061851 := bstep (se 1 (by rfl) ⟨1546388, by rfl⟩ : syracuseStep 2061851 = 3092777) B3092777
theorem B3134981 : Blo 2061435 3134981 := bbase (se 4 (by rfl) ⟨293904, by rfl⟩ : syracuseStep 3134981 = 587809) (by norm_num)
theorem B8359949 : Blo 2061435 8359949 := bstep (se 3 (by rfl) ⟨1567490, by rfl⟩ : syracuseStep 8359949 = 3134981) B3134981
theorem B5573299 : Blo 2061435 5573299 := bstep (se 1 (by rfl) ⟨4179974, by rfl⟩ : syracuseStep 5573299 = 8359949) B8359949
theorem B7431065 : Blo 2061435 7431065 := bstep (se 2 (by rfl) ⟨2786649, by rfl⟩ : syracuseStep 7431065 = 5573299) B5573299
theorem B4954043 : Blo 2061435 4954043 := bstep (se 1 (by rfl) ⟨3715532, by rfl⟩ : syracuseStep 4954043 = 7431065) B7431065
theorem B3302695 : Blo 2061435 3302695 := bstep (se 1 (by rfl) ⟨2477021, by rfl⟩ : syracuseStep 3302695 = 4954043) B4954043
theorem B4403593 : Blo 2061435 4403593 := bstep (se 2 (by rfl) ⟨1651347, by rfl⟩ : syracuseStep 4403593 = 3302695) B3302695
theorem B5871457 : Blo 2061435 5871457 := bstep (se 2 (by rfl) ⟨2201796, by rfl⟩ : syracuseStep 5871457 = 4403593) B4403593
theorem B7828609 : Blo 2061435 7828609 := bstep (se 2 (by rfl) ⟨2935728, by rfl⟩ : syracuseStep 7828609 = 5871457) B5871457
theorem B10438145 : Blo 2061435 10438145 := bstep (se 2 (by rfl) ⟨3914304, by rfl⟩ : syracuseStep 10438145 = 7828609) B7828609
theorem B6958763 : Blo 2061435 6958763 := bstep (se 1 (by rfl) ⟨5219072, by rfl⟩ : syracuseStep 6958763 = 10438145) B10438145
theorem B4639175 : Blo 2061435 4639175 := bstep (se 1 (by rfl) ⟨3479381, by rfl⟩ : syracuseStep 4639175 = 6958763) B6958763
theorem B3092783 : Blo 2061435 3092783 := bstep (se 1 (by rfl) ⟨2319587, by rfl⟩ : syracuseStep 3092783 = 4639175) B4639175
theorem B2061855 : Blo 2061435 2061855 := bstep (se 1 (by rfl) ⟨1546391, by rfl⟩ : syracuseStep 2061855 = 3092783) B3092783
theorem B3092789 : Blo 2061435 3092789 := bbase (se 5 (by rfl) ⟨144974, by rfl⟩ : syracuseStep 3092789 = 289949) (by norm_num)
theorem B2061859 : Blo 2061435 2061859 := bstep (se 1 (by rfl) ⟨1546394, by rfl⟩ : syracuseStep 2061859 = 3092789) B3092789
theorem B5219093 : Blo 2061435 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B3479395 : Blo 2061435 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B4639193 : Blo 2061435 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B3092795 : Blo 2061435 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B2061863 : Blo 2061435 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B2319601 : Blo 2061435 2319601 := bbase (se 2 (by rfl) ⟨869850, by rfl⟩ : syracuseStep 2319601 = 1739701) (by norm_num)
theorem B3092801 : Blo 2061435 3092801 := bstep (se 2 (by rfl) ⟨1159800, by rfl⟩ : syracuseStep 3092801 = 2319601) B2319601
theorem B2061867 : Blo 2061435 2061867 := bstep (se 1 (by rfl) ⟨1546400, by rfl⟩ : syracuseStep 2061867 = 3092801) B3092801
theorem B10580645 : Blo 2061435 10580645 := bbase (se 4 (by rfl) ⟨991935, by rfl⟩ : syracuseStep 10580645 = 1983871) (by norm_num)
theorem B7053763 : Blo 2061435 7053763 := bstep (se 1 (by rfl) ⟨5290322, by rfl⟩ : syracuseStep 7053763 = 10580645) B10580645
theorem B9405017 : Blo 2061435 9405017 := bstep (se 2 (by rfl) ⟨3526881, by rfl⟩ : syracuseStep 9405017 = 7053763) B7053763
theorem B6270011 : Blo 2061435 6270011 := bstep (se 1 (by rfl) ⟨4702508, by rfl⟩ : syracuseStep 6270011 = 9405017) B9405017
theorem B4180007 : Blo 2061435 4180007 := bstep (se 1 (by rfl) ⟨3135005, by rfl⟩ : syracuseStep 4180007 = 6270011) B6270011
theorem B2786671 : Blo 2061435 2786671 := bstep (se 1 (by rfl) ⟨2090003, by rfl⟩ : syracuseStep 2786671 = 4180007) B4180007
theorem B3715561 : Blo 2061435 3715561 := bstep (se 2 (by rfl) ⟨1393335, by rfl⟩ : syracuseStep 3715561 = 2786671) B2786671
theorem B19816325 : Blo 2061435 19816325 := bstep (se 4 (by rfl) ⟨1857780, by rfl⟩ : syracuseStep 19816325 = 3715561) B3715561
theorem B13210883 : Blo 2061435 13210883 := bstep (se 1 (by rfl) ⟨9908162, by rfl⟩ : syracuseStep 13210883 = 19816325) B19816325
theorem B8807255 : Blo 2061435 8807255 := bstep (se 1 (by rfl) ⟨6605441, by rfl⟩ : syracuseStep 8807255 = 13210883) B13210883
theorem B5871503 : Blo 2061435 5871503 := bstep (se 1 (by rfl) ⟨4403627, by rfl⟩ : syracuseStep 5871503 = 8807255) B8807255
theorem B3914335 : Blo 2061435 3914335 := bstep (se 1 (by rfl) ⟨2935751, by rfl⟩ : syracuseStep 3914335 = 5871503) B5871503
theorem B5219113 : Blo 2061435 5219113 := bstep (se 2 (by rfl) ⟨1957167, by rfl⟩ : syracuseStep 5219113 = 3914335) B3914335
theorem B6958817 : Blo 2061435 6958817 := bstep (se 2 (by rfl) ⟨2609556, by rfl⟩ : syracuseStep 6958817 = 5219113) B5219113
theorem B4639211 : Blo 2061435 4639211 := bstep (se 1 (by rfl) ⟨3479408, by rfl⟩ : syracuseStep 4639211 = 6958817) B6958817
theorem B3092807 : Blo 2061435 3092807 := bstep (se 1 (by rfl) ⟨2319605, by rfl⟩ : syracuseStep 3092807 = 4639211) B4639211
theorem B2061871 : Blo 2061435 2061871 := bstep (se 1 (by rfl) ⟨1546403, by rfl⟩ : syracuseStep 2061871 = 3092807) B3092807
theorem B3092813 : Blo 2061435 3092813 := bbase (se 3 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 3092813 = 1159805) (by norm_num)
theorem B2061875 : Blo 2061435 2061875 := bstep (se 1 (by rfl) ⟨1546406, by rfl⟩ : syracuseStep 2061875 = 3092813) B3092813
theorem B4639229 : Blo 2061435 4639229 := bbase (se 3 (by rfl) ⟨869855, by rfl⟩ : syracuseStep 4639229 = 1739711) (by norm_num)
theorem B3092819 : Blo 2061435 3092819 := bstep (se 1 (by rfl) ⟨2319614, by rfl⟩ : syracuseStep 3092819 = 4639229) B4639229
theorem B2061879 : Blo 2061435 2061879 := bstep (se 1 (by rfl) ⟨1546409, by rfl⟩ : syracuseStep 2061879 = 3092819) B3092819
theorem B3479429 : Blo 2061435 3479429 := bbase (se 4 (by rfl) ⟨326196, by rfl⟩ : syracuseStep 3479429 = 652393) (by norm_num)
theorem B2319619 : Blo 2061435 2319619 := bstep (se 1 (by rfl) ⟨1739714, by rfl⟩ : syracuseStep 2319619 = 3479429) B3479429
theorem B3092825 : Blo 2061435 3092825 := bstep (se 2 (by rfl) ⟨1159809, by rfl⟩ : syracuseStep 3092825 = 2319619) B2319619
theorem B2061883 : Blo 2061435 2061883 := bstep (se 1 (by rfl) ⟨1546412, by rfl⟩ : syracuseStep 2061883 = 3092825) B3092825
theorem B15657461 : Blo 2061435 15657461 := bbase (se 5 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 15657461 = 1467887) (by norm_num)
theorem B10438307 : Blo 2061435 10438307 := bstep (se 1 (by rfl) ⟨7828730, by rfl⟩ : syracuseStep 10438307 = 15657461) B15657461
theorem B6958871 : Blo 2061435 6958871 := bstep (se 1 (by rfl) ⟨5219153, by rfl⟩ : syracuseStep 6958871 = 10438307) B10438307
theorem B4639247 : Blo 2061435 4639247 := bstep (se 1 (by rfl) ⟨3479435, by rfl⟩ : syracuseStep 4639247 = 6958871) B6958871
theorem B3092831 : Blo 2061435 3092831 := bstep (se 1 (by rfl) ⟨2319623, by rfl⟩ : syracuseStep 3092831 = 4639247) B4639247
theorem B2061887 : Blo 2061435 2061887 := bstep (se 1 (by rfl) ⟨1546415, by rfl⟩ : syracuseStep 2061887 = 3092831) B3092831
theorem B3092837 : Blo 2061435 3092837 := bbase (se 4 (by rfl) ⟨289953, by rfl⟩ : syracuseStep 3092837 = 579907) (by norm_num)
theorem B2061891 : Blo 2061435 2061891 := bstep (se 1 (by rfl) ⟨1546418, by rfl⟩ : syracuseStep 2061891 = 3092837) B3092837
theorem B3914381 : Blo 2061435 3914381 := bbase (se 3 (by rfl) ⟨733946, by rfl⟩ : syracuseStep 3914381 = 1467893) (by norm_num)
theorem B2609587 : Blo 2061435 2609587 := bstep (se 1 (by rfl) ⟨1957190, by rfl⟩ : syracuseStep 2609587 = 3914381) B3914381
theorem B3479449 : Blo 2061435 3479449 := bstep (se 2 (by rfl) ⟨1304793, by rfl⟩ : syracuseStep 3479449 = 2609587) B2609587
theorem B4639265 : Blo 2061435 4639265 := bstep (se 2 (by rfl) ⟨1739724, by rfl⟩ : syracuseStep 4639265 = 3479449) B3479449
theorem B3092843 : Blo 2061435 3092843 := bstep (se 1 (by rfl) ⟨2319632, by rfl⟩ : syracuseStep 3092843 = 4639265) B4639265
theorem B2061895 : Blo 2061435 2061895 := bstep (se 1 (by rfl) ⟨1546421, by rfl⟩ : syracuseStep 2061895 = 3092843) B3092843
theorem B2319637 : Blo 2061435 2319637 := bbase (se 6 (by rfl) ⟨54366, by rfl⟩ : syracuseStep 2319637 = 108733) (by norm_num)
theorem B3092849 : Blo 2061435 3092849 := bstep (se 2 (by rfl) ⟨1159818, by rfl⟩ : syracuseStep 3092849 = 2319637) B2319637
theorem B2061899 : Blo 2061435 2061899 := bstep (se 1 (by rfl) ⟨1546424, by rfl⟩ : syracuseStep 2061899 = 3092849) B3092849
theorem B2609597 : Blo 2061435 2609597 := bbase (se 3 (by rfl) ⟨489299, by rfl⟩ : syracuseStep 2609597 = 978599) (by norm_num)
theorem B6958925 : Blo 2061435 6958925 := bstep (se 3 (by rfl) ⟨1304798, by rfl⟩ : syracuseStep 6958925 = 2609597) B2609597
theorem B4639283 : Blo 2061435 4639283 := bstep (se 1 (by rfl) ⟨3479462, by rfl⟩ : syracuseStep 4639283 = 6958925) B6958925
theorem B3092855 : Blo 2061435 3092855 := bstep (se 1 (by rfl) ⟨2319641, by rfl⟩ : syracuseStep 3092855 = 4639283) B4639283
theorem B2061903 : Blo 2061435 2061903 := bstep (se 1 (by rfl) ⟨1546427, by rfl⟩ : syracuseStep 2061903 = 3092855) B3092855
theorem B3092861 : Blo 2061435 3092861 := bbase (se 3 (by rfl) ⟨579911, by rfl⟩ : syracuseStep 3092861 = 1159823) (by norm_num)
theorem B2061907 : Blo 2061435 2061907 := bstep (se 1 (by rfl) ⟨1546430, by rfl⟩ : syracuseStep 2061907 = 3092861) B3092861
theorem B4639301 : Blo 2061435 4639301 := bbase (se 4 (by rfl) ⟨434934, by rfl⟩ : syracuseStep 4639301 = 869869) (by norm_num)
theorem B3092867 : Blo 2061435 3092867 := bstep (se 1 (by rfl) ⟨2319650, by rfl⟩ : syracuseStep 3092867 = 4639301) B4639301
theorem B2061911 : Blo 2061435 2061911 := bstep (se 1 (by rfl) ⟨1546433, by rfl⟩ : syracuseStep 2061911 = 3092867) B3092867
theorem B2201861 : Blo 2061435 2201861 := bbase (se 4 (by rfl) ⟨206424, by rfl⟩ : syracuseStep 2201861 = 412849) (by norm_num)
theorem B5871629 : Blo 2061435 5871629 := bstep (se 3 (by rfl) ⟨1100930, by rfl⟩ : syracuseStep 5871629 = 2201861) B2201861
theorem B3914419 : Blo 2061435 3914419 := bstep (se 1 (by rfl) ⟨2935814, by rfl⟩ : syracuseStep 3914419 = 5871629) B5871629
theorem B5219225 : Blo 2061435 5219225 := bstep (se 2 (by rfl) ⟨1957209, by rfl⟩ : syracuseStep 5219225 = 3914419) B3914419
theorem B3479483 : Blo 2061435 3479483 := bstep (se 1 (by rfl) ⟨2609612, by rfl⟩ : syracuseStep 3479483 = 5219225) B5219225
theorem B2319655 : Blo 2061435 2319655 := bstep (se 1 (by rfl) ⟨1739741, by rfl⟩ : syracuseStep 2319655 = 3479483) B3479483
theorem B3092873 : Blo 2061435 3092873 := bstep (se 2 (by rfl) ⟨1159827, by rfl⟩ : syracuseStep 3092873 = 2319655) B2319655
theorem B2061915 : Blo 2061435 2061915 := bstep (se 1 (by rfl) ⟨1546436, by rfl⟩ : syracuseStep 2061915 = 3092873) B3092873
theorem B10438469 : Blo 2061435 10438469 := bbase (se 4 (by rfl) ⟨978606, by rfl⟩ : syracuseStep 10438469 = 1957213) (by norm_num)
theorem B6958979 : Blo 2061435 6958979 := bstep (se 1 (by rfl) ⟨5219234, by rfl⟩ : syracuseStep 6958979 = 10438469) B10438469
theorem B4639319 : Blo 2061435 4639319 := bstep (se 1 (by rfl) ⟨3479489, by rfl⟩ : syracuseStep 4639319 = 6958979) B6958979
theorem B3092879 : Blo 2061435 3092879 := bstep (se 1 (by rfl) ⟨2319659, by rfl⟩ : syracuseStep 3092879 = 4639319) B4639319
theorem B2061919 : Blo 2061435 2061919 := bstep (se 1 (by rfl) ⟨1546439, by rfl⟩ : syracuseStep 2061919 = 3092879) B3092879
theorem B3092885 : Blo 2061435 3092885 := bbase (se 6 (by rfl) ⟨72489, by rfl⟩ : syracuseStep 3092885 = 144979) (by norm_num)
theorem B2061923 : Blo 2061435 2061923 := bstep (se 1 (by rfl) ⟨1546442, by rfl⟩ : syracuseStep 2061923 = 3092885) B3092885
theorem B6605621 : Blo 2061435 6605621 := bbase (se 5 (by rfl) ⟨309638, by rfl⟩ : syracuseStep 6605621 = 619277) (by norm_num)
theorem B4403747 : Blo 2061435 4403747 := bstep (se 1 (by rfl) ⟨3302810, by rfl⟩ : syracuseStep 4403747 = 6605621) B6605621
theorem B11743325 : Blo 2061435 11743325 := bstep (se 3 (by rfl) ⟨2201873, by rfl⟩ : syracuseStep 11743325 = 4403747) B4403747
theorem B7828883 : Blo 2061435 7828883 := bstep (se 1 (by rfl) ⟨5871662, by rfl⟩ : syracuseStep 7828883 = 11743325) B11743325
theorem B5219255 : Blo 2061435 5219255 := bstep (se 1 (by rfl) ⟨3914441, by rfl⟩ : syracuseStep 5219255 = 7828883) B7828883
theorem B3479503 : Blo 2061435 3479503 := bstep (se 1 (by rfl) ⟨2609627, by rfl⟩ : syracuseStep 3479503 = 5219255) B5219255
theorem B4639337 : Blo 2061435 4639337 := bstep (se 2 (by rfl) ⟨1739751, by rfl⟩ : syracuseStep 4639337 = 3479503) B3479503
theorem B3092891 : Blo 2061435 3092891 := bstep (se 1 (by rfl) ⟨2319668, by rfl⟩ : syracuseStep 3092891 = 4639337) B4639337
theorem B2061927 : Blo 2061435 2061927 := bstep (se 1 (by rfl) ⟨1546445, by rfl⟩ : syracuseStep 2061927 = 3092891) B3092891
theorem B2319673 : Blo 2061435 2319673 := bbase (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) (by norm_num)
theorem B3092897 : Blo 2061435 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B2061931 : Blo 2061435 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B5871685 : Blo 2061435 5871685 := bbase (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) (by norm_num)
theorem B7828913 : Blo 2061435 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B5219275 : Blo 2061435 5219275 := bstep (se 1 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 5219275 = 7828913) B7828913
theorem B6959033 : Blo 2061435 6959033 := bstep (se 2 (by rfl) ⟨2609637, by rfl⟩ : syracuseStep 6959033 = 5219275) B5219275
theorem B4639355 : Blo 2061435 4639355 := bstep (se 1 (by rfl) ⟨3479516, by rfl⟩ : syracuseStep 4639355 = 6959033) B6959033
theorem B3092903 : Blo 2061435 3092903 := bstep (se 1 (by rfl) ⟨2319677, by rfl⟩ : syracuseStep 3092903 = 4639355) B4639355
theorem B2061935 : Blo 2061435 2061935 := bstep (se 1 (by rfl) ⟨1546451, by rfl⟩ : syracuseStep 2061935 = 3092903) B3092903
theorem B3092909 : Blo 2061435 3092909 := bbase (se 3 (by rfl) ⟨579920, by rfl⟩ : syracuseStep 3092909 = 1159841) (by norm_num)
theorem B2061939 : Blo 2061435 2061939 := bstep (se 1 (by rfl) ⟨1546454, by rfl⟩ : syracuseStep 2061939 = 3092909) B3092909
theorem B4639373 : Blo 2061435 4639373 := bbase (se 3 (by rfl) ⟨869882, by rfl⟩ : syracuseStep 4639373 = 1739765) (by norm_num)
theorem B3092915 : Blo 2061435 3092915 := bstep (se 1 (by rfl) ⟨2319686, by rfl⟩ : syracuseStep 3092915 = 4639373) B4639373
theorem B2061943 : Blo 2061435 2061943 := bstep (se 1 (by rfl) ⟨1546457, by rfl⟩ : syracuseStep 2061943 = 3092915) B3092915
theorem B2609653 : Blo 2061435 2609653 := bbase (se 5 (by rfl) ⟨122327, by rfl⟩ : syracuseStep 2609653 = 244655) (by norm_num)
theorem B3479537 : Blo 2061435 3479537 := bstep (se 2 (by rfl) ⟨1304826, by rfl⟩ : syracuseStep 3479537 = 2609653) B2609653
theorem B2319691 : Blo 2061435 2319691 := bstep (se 1 (by rfl) ⟨1739768, by rfl⟩ : syracuseStep 2319691 = 3479537) B3479537
theorem B3092921 : Blo 2061435 3092921 := bstep (se 2 (by rfl) ⟨1159845, by rfl⟩ : syracuseStep 3092921 = 2319691) B2319691
theorem B2061947 : Blo 2061435 2061947 := bstep (se 1 (by rfl) ⟨1546460, by rfl⟩ : syracuseStep 2061947 = 3092921) B3092921
theorem B5573557 : Blo 2061435 5573557 := bbase (se 5 (by rfl) ⟨261260, by rfl⟩ : syracuseStep 5573557 = 522521) (by norm_num)
theorem B7431409 : Blo 2061435 7431409 := bstep (se 2 (by rfl) ⟨2786778, by rfl⟩ : syracuseStep 7431409 = 5573557) B5573557
theorem B39634181 : Blo 2061435 39634181 := bstep (se 4 (by rfl) ⟨3715704, by rfl⟩ : syracuseStep 39634181 = 7431409) B7431409
theorem B26422787 : Blo 2061435 26422787 := bstep (se 1 (by rfl) ⟨19817090, by rfl⟩ : syracuseStep 26422787 = 39634181) B39634181
theorem B17615191 : Blo 2061435 17615191 := bstep (se 1 (by rfl) ⟨13211393, by rfl⟩ : syracuseStep 17615191 = 26422787) B26422787
theorem B23486921 : Blo 2061435 23486921 := bstep (se 2 (by rfl) ⟨8807595, by rfl⟩ : syracuseStep 23486921 = 17615191) B17615191
theorem B15657947 : Blo 2061435 15657947 := bstep (se 1 (by rfl) ⟨11743460, by rfl⟩ : syracuseStep 15657947 = 23486921) B23486921
theorem B10438631 : Blo 2061435 10438631 := bstep (se 1 (by rfl) ⟨7828973, by rfl⟩ : syracuseStep 10438631 = 15657947) B15657947
theorem B6959087 : Blo 2061435 6959087 := bstep (se 1 (by rfl) ⟨5219315, by rfl⟩ : syracuseStep 6959087 = 10438631) B10438631
theorem B4639391 : Blo 2061435 4639391 := bstep (se 1 (by rfl) ⟨3479543, by rfl⟩ : syracuseStep 4639391 = 6959087) B6959087
theorem B3092927 : Blo 2061435 3092927 := bstep (se 1 (by rfl) ⟨2319695, by rfl⟩ : syracuseStep 3092927 = 4639391) B4639391
theorem B2061951 : Blo 2061435 2061951 := bstep (se 1 (by rfl) ⟨1546463, by rfl⟩ : syracuseStep 2061951 = 3092927) B3092927
theorem B3092933 : Blo 2061435 3092933 := bbase (se 4 (by rfl) ⟨289962, by rfl⟩ : syracuseStep 3092933 = 579925) (by norm_num)
theorem B2061955 : Blo 2061435 2061955 := bstep (se 1 (by rfl) ⟨1546466, by rfl⟩ : syracuseStep 2061955 = 3092933) B3092933
theorem B3479557 : Blo 2061435 3479557 := bbase (se 4 (by rfl) ⟨326208, by rfl⟩ : syracuseStep 3479557 = 652417) (by norm_num)
theorem B4639409 : Blo 2061435 4639409 := bstep (se 2 (by rfl) ⟨1739778, by rfl⟩ : syracuseStep 4639409 = 3479557) B3479557
theorem B3092939 : Blo 2061435 3092939 := bstep (se 1 (by rfl) ⟨2319704, by rfl⟩ : syracuseStep 3092939 = 4639409) B4639409
theorem B2061959 : Blo 2061435 2061959 := bstep (se 1 (by rfl) ⟨1546469, by rfl⟩ : syracuseStep 2061959 = 3092939) B3092939
theorem B2319709 : Blo 2061435 2319709 := bbase (se 3 (by rfl) ⟨434945, by rfl⟩ : syracuseStep 2319709 = 869891) (by norm_num)
theorem B3092945 : Blo 2061435 3092945 := bstep (se 2 (by rfl) ⟨1159854, by rfl⟩ : syracuseStep 3092945 = 2319709) B2319709
theorem B2061963 : Blo 2061435 2061963 := bstep (se 1 (by rfl) ⟨1546472, by rfl⟩ : syracuseStep 2061963 = 3092945) B3092945
theorem B6959141 : Blo 2061435 6959141 := bbase (se 4 (by rfl) ⟨652419, by rfl⟩ : syracuseStep 6959141 = 1304839) (by norm_num)
theorem B4639427 : Blo 2061435 4639427 := bstep (se 1 (by rfl) ⟨3479570, by rfl⟩ : syracuseStep 4639427 = 6959141) B6959141
theorem B3092951 : Blo 2061435 3092951 := bstep (se 1 (by rfl) ⟨2319713, by rfl⟩ : syracuseStep 3092951 = 4639427) B4639427
theorem B2061967 : Blo 2061435 2061967 := bstep (se 1 (by rfl) ⟨1546475, by rfl⟩ : syracuseStep 2061967 = 3092951) B3092951
theorem B3092957 : Blo 2061435 3092957 := bbase (se 3 (by rfl) ⟨579929, by rfl⟩ : syracuseStep 3092957 = 1159859) (by norm_num)
theorem B2061971 : Blo 2061435 2061971 := bstep (se 1 (by rfl) ⟨1546478, by rfl⟩ : syracuseStep 2061971 = 3092957) B3092957
theorem B4639445 : Blo 2061435 4639445 := bbase (se 7 (by rfl) ⟨54368, by rfl⟩ : syracuseStep 4639445 = 108737) (by norm_num)
theorem B3092963 : Blo 2061435 3092963 := bstep (se 1 (by rfl) ⟨2319722, by rfl⟩ : syracuseStep 3092963 = 4639445) B4639445
theorem B2061975 : Blo 2061435 2061975 := bstep (se 1 (by rfl) ⟨1546481, by rfl⟩ : syracuseStep 2061975 = 3092963) B3092963
theorem B8807717 : Blo 2061435 8807717 := bbase (se 4 (by rfl) ⟨825723, by rfl⟩ : syracuseStep 8807717 = 1651447) (by norm_num)
theorem B5871811 : Blo 2061435 5871811 := bstep (se 1 (by rfl) ⟨4403858, by rfl⟩ : syracuseStep 5871811 = 8807717) B8807717
theorem B7829081 : Blo 2061435 7829081 := bstep (se 2 (by rfl) ⟨2935905, by rfl⟩ : syracuseStep 7829081 = 5871811) B5871811
theorem B5219387 : Blo 2061435 5219387 := bstep (se 1 (by rfl) ⟨3914540, by rfl⟩ : syracuseStep 5219387 = 7829081) B7829081
theorem B3479591 : Blo 2061435 3479591 := bstep (se 1 (by rfl) ⟨2609693, by rfl⟩ : syracuseStep 3479591 = 5219387) B5219387
theorem B2319727 : Blo 2061435 2319727 := bstep (se 1 (by rfl) ⟨1739795, by rfl⟩ : syracuseStep 2319727 = 3479591) B3479591
theorem B3092969 : Blo 2061435 3092969 := bstep (se 2 (by rfl) ⟨1159863, by rfl⟩ : syracuseStep 3092969 = 2319727) B2319727
theorem B2061979 : Blo 2061435 2061979 := bstep (se 1 (by rfl) ⟨1546484, by rfl⟩ : syracuseStep 2061979 = 3092969) B3092969
theorem B2351381 : Blo 2061435 2351381 := bbase (se 6 (by rfl) ⟨55110, by rfl⟩ : syracuseStep 2351381 = 110221) (by norm_num)
theorem B25081397 : Blo 2061435 25081397 := bstep (se 5 (by rfl) ⟨1175690, by rfl⟩ : syracuseStep 25081397 = 2351381) B2351381
theorem B16720931 : Blo 2061435 16720931 := bstep (se 1 (by rfl) ⟨12540698, by rfl⟩ : syracuseStep 16720931 = 25081397) B25081397
theorem B44589149 : Blo 2061435 44589149 := bstep (se 3 (by rfl) ⟨8360465, by rfl⟩ : syracuseStep 44589149 = 16720931) B16720931
theorem B29726099 : Blo 2061435 29726099 := bstep (se 1 (by rfl) ⟨22294574, by rfl⟩ : syracuseStep 29726099 = 44589149) B44589149
theorem B19817399 : Blo 2061435 19817399 := bstep (se 1 (by rfl) ⟨14863049, by rfl⟩ : syracuseStep 19817399 = 29726099) B29726099
theorem B13211599 : Blo 2061435 13211599 := bstep (se 1 (by rfl) ⟨9908699, by rfl⟩ : syracuseStep 13211599 = 19817399) B19817399
theorem B17615465 : Blo 2061435 17615465 := bstep (se 2 (by rfl) ⟨6605799, by rfl⟩ : syracuseStep 17615465 = 13211599) B13211599
theorem B11743643 : Blo 2061435 11743643 := bstep (se 1 (by rfl) ⟨8807732, by rfl⟩ : syracuseStep 11743643 = 17615465) B17615465
theorem B7829095 : Blo 2061435 7829095 := bstep (se 1 (by rfl) ⟨5871821, by rfl⟩ : syracuseStep 7829095 = 11743643) B11743643
theorem B10438793 : Blo 2061435 10438793 := bstep (se 2 (by rfl) ⟨3914547, by rfl⟩ : syracuseStep 10438793 = 7829095) B7829095
theorem B6959195 : Blo 2061435 6959195 := bstep (se 1 (by rfl) ⟨5219396, by rfl⟩ : syracuseStep 6959195 = 10438793) B10438793
theorem B4639463 : Blo 2061435 4639463 := bstep (se 1 (by rfl) ⟨3479597, by rfl⟩ : syracuseStep 4639463 = 6959195) B6959195
theorem B3092975 : Blo 2061435 3092975 := bstep (se 1 (by rfl) ⟨2319731, by rfl⟩ : syracuseStep 3092975 = 4639463) B4639463
theorem B2061983 : Blo 2061435 2061983 := bstep (se 1 (by rfl) ⟨1546487, by rfl⟩ : syracuseStep 2061983 = 3092975) B3092975
theorem B3092981 : Blo 2061435 3092981 := bbase (se 5 (by rfl) ⟨144983, by rfl⟩ : syracuseStep 3092981 = 289967) (by norm_num)
theorem B2061987 : Blo 2061435 2061987 := bstep (se 1 (by rfl) ⟨1546490, by rfl⟩ : syracuseStep 2061987 = 3092981) B3092981
theorem B5871845 : Blo 2061435 5871845 := bbase (se 4 (by rfl) ⟨550485, by rfl⟩ : syracuseStep 5871845 = 1100971) (by norm_num)
theorem B3914563 : Blo 2061435 3914563 := bstep (se 1 (by rfl) ⟨2935922, by rfl⟩ : syracuseStep 3914563 = 5871845) B5871845
theorem B5219417 : Blo 2061435 5219417 := bstep (se 2 (by rfl) ⟨1957281, by rfl⟩ : syracuseStep 5219417 = 3914563) B3914563
theorem B3479611 : Blo 2061435 3479611 := bstep (se 1 (by rfl) ⟨2609708, by rfl⟩ : syracuseStep 3479611 = 5219417) B5219417
theorem B4639481 : Blo 2061435 4639481 := bstep (se 2 (by rfl) ⟨1739805, by rfl⟩ : syracuseStep 4639481 = 3479611) B3479611
theorem B3092987 : Blo 2061435 3092987 := bstep (se 1 (by rfl) ⟨2319740, by rfl⟩ : syracuseStep 3092987 = 4639481) B4639481
theorem B2061991 : Blo 2061435 2061991 := bstep (se 1 (by rfl) ⟨1546493, by rfl⟩ : syracuseStep 2061991 = 3092987) B3092987
theorem B2319745 : Blo 2061435 2319745 := bbase (se 2 (by rfl) ⟨869904, by rfl⟩ : syracuseStep 2319745 = 1739809) (by norm_num)
theorem B3092993 : Blo 2061435 3092993 := bstep (se 2 (by rfl) ⟨1159872, by rfl⟩ : syracuseStep 3092993 = 2319745) B2319745
theorem B2061995 : Blo 2061435 2061995 := bstep (se 1 (by rfl) ⟨1546496, by rfl⟩ : syracuseStep 2061995 = 3092993) B3092993
theorem B5219437 : Blo 2061435 5219437 := bbase (se 3 (by rfl) ⟨978644, by rfl⟩ : syracuseStep 5219437 = 1957289) (by norm_num)
theorem B6959249 : Blo 2061435 6959249 := bstep (se 2 (by rfl) ⟨2609718, by rfl⟩ : syracuseStep 6959249 = 5219437) B5219437
theorem B4639499 : Blo 2061435 4639499 := bstep (se 1 (by rfl) ⟨3479624, by rfl⟩ : syracuseStep 4639499 = 6959249) B6959249
theorem B3092999 : Blo 2061435 3092999 := bstep (se 1 (by rfl) ⟨2319749, by rfl⟩ : syracuseStep 3092999 = 4639499) B4639499
theorem B2061999 : Blo 2061435 2061999 := bstep (se 1 (by rfl) ⟨1546499, by rfl⟩ : syracuseStep 2061999 = 3092999) B3092999
theorem B3093005 : Blo 2061435 3093005 := bbase (se 3 (by rfl) ⟨579938, by rfl⟩ : syracuseStep 3093005 = 1159877) (by norm_num)
theorem B2062003 : Blo 2061435 2062003 := bstep (se 1 (by rfl) ⟨1546502, by rfl⟩ : syracuseStep 2062003 = 3093005) B3093005
theorem B4639517 : Blo 2061435 4639517 := bbase (se 3 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 4639517 = 1739819) (by norm_num)
theorem B3093011 : Blo 2061435 3093011 := bstep (se 1 (by rfl) ⟨2319758, by rfl⟩ : syracuseStep 3093011 = 4639517) B4639517
theorem B2062007 : Blo 2061435 2062007 := bstep (se 1 (by rfl) ⟨1546505, by rfl⟩ : syracuseStep 2062007 = 3093011) B3093011
theorem B3479645 : Blo 2061435 3479645 := bbase (se 3 (by rfl) ⟨652433, by rfl⟩ : syracuseStep 3479645 = 1304867) (by norm_num)
theorem B2319763 : Blo 2061435 2319763 := bstep (se 1 (by rfl) ⟨1739822, by rfl⟩ : syracuseStep 2319763 = 3479645) B3479645
theorem B3093017 : Blo 2061435 3093017 := bstep (se 2 (by rfl) ⟨1159881, by rfl⟩ : syracuseStep 3093017 = 2319763) B2319763
theorem B2062011 : Blo 2061435 2062011 := bstep (se 1 (by rfl) ⟨1546508, by rfl⟩ : syracuseStep 2062011 = 3093017) B3093017
theorem B8360597 : Blo 2061435 8360597 := bbase (se 6 (by rfl) ⟨195951, by rfl⟩ : syracuseStep 8360597 = 391903) (by norm_num)
theorem B5573731 : Blo 2061435 5573731 := bstep (se 1 (by rfl) ⟨4180298, by rfl⟩ : syracuseStep 5573731 = 8360597) B8360597
theorem B7431641 : Blo 2061435 7431641 := bstep (se 2 (by rfl) ⟨2786865, by rfl⟩ : syracuseStep 7431641 = 5573731) B5573731
theorem B4954427 : Blo 2061435 4954427 := bstep (se 1 (by rfl) ⟨3715820, by rfl⟩ : syracuseStep 4954427 = 7431641) B7431641
theorem B3302951 : Blo 2061435 3302951 := bstep (se 1 (by rfl) ⟨2477213, by rfl⟩ : syracuseStep 3302951 = 4954427) B4954427
theorem B8807869 : Blo 2061435 8807869 := bstep (se 3 (by rfl) ⟨1651475, by rfl⟩ : syracuseStep 8807869 = 3302951) B3302951
theorem B11743825 : Blo 2061435 11743825 := bstep (se 2 (by rfl) ⟨4403934, by rfl⟩ : syracuseStep 11743825 = 8807869) B8807869
theorem B15658433 : Blo 2061435 15658433 := bstep (se 2 (by rfl) ⟨5871912, by rfl⟩ : syracuseStep 15658433 = 11743825) B11743825
theorem B10438955 : Blo 2061435 10438955 := bstep (se 1 (by rfl) ⟨7829216, by rfl⟩ : syracuseStep 10438955 = 15658433) B15658433
theorem B6959303 : Blo 2061435 6959303 := bstep (se 1 (by rfl) ⟨5219477, by rfl⟩ : syracuseStep 6959303 = 10438955) B10438955
theorem B4639535 : Blo 2061435 4639535 := bstep (se 1 (by rfl) ⟨3479651, by rfl⟩ : syracuseStep 4639535 = 6959303) B6959303
theorem B3093023 : Blo 2061435 3093023 := bstep (se 1 (by rfl) ⟨2319767, by rfl⟩ : syracuseStep 3093023 = 4639535) B4639535
theorem B2062015 : Blo 2061435 2062015 := bstep (se 1 (by rfl) ⟨1546511, by rfl⟩ : syracuseStep 2062015 = 3093023) B3093023
theorem B3093029 : Blo 2061435 3093029 := bbase (se 4 (by rfl) ⟨289971, by rfl⟩ : syracuseStep 3093029 = 579943) (by norm_num)
theorem B2062019 : Blo 2061435 2062019 := bstep (se 1 (by rfl) ⟨1546514, by rfl⟩ : syracuseStep 2062019 = 3093029) B3093029
theorem B2609749 : Blo 2061435 2609749 := bbase (se 8 (by rfl) ⟨15291, by rfl⟩ : syracuseStep 2609749 = 30583) (by norm_num)
theorem B3479665 : Blo 2061435 3479665 := bstep (se 2 (by rfl) ⟨1304874, by rfl⟩ : syracuseStep 3479665 = 2609749) B2609749
theorem B4639553 : Blo 2061435 4639553 := bstep (se 2 (by rfl) ⟨1739832, by rfl⟩ : syracuseStep 4639553 = 3479665) B3479665
theorem B3093035 : Blo 2061435 3093035 := bstep (se 1 (by rfl) ⟨2319776, by rfl⟩ : syracuseStep 3093035 = 4639553) B4639553
theorem B2062023 : Blo 2061435 2062023 := bstep (se 1 (by rfl) ⟨1546517, by rfl⟩ : syracuseStep 2062023 = 3093035) B3093035
theorem B2319781 : Blo 2061435 2319781 := bbase (se 4 (by rfl) ⟨217479, by rfl⟩ : syracuseStep 2319781 = 434959) (by norm_num)
theorem B3093041 : Blo 2061435 3093041 := bstep (se 2 (by rfl) ⟨1159890, by rfl⟩ : syracuseStep 3093041 = 2319781) B2319781
theorem B2062027 : Blo 2061435 2062027 := bstep (se 1 (by rfl) ⟨1546520, by rfl⟩ : syracuseStep 2062027 = 3093041) B3093041
theorem B2477233 : Blo 2061435 2477233 := bbase (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) (by norm_num)
theorem B13211909 : Blo 2061435 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B8807939 : Blo 2061435 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B5871959 : Blo 2061435 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B3914639 : Blo 2061435 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B2609759 : Blo 2061435 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B6959357 : Blo 2061435 6959357 := bstep (se 3 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 6959357 = 2609759) B2609759
theorem B4639571 : Blo 2061435 4639571 := bstep (se 1 (by rfl) ⟨3479678, by rfl⟩ : syracuseStep 4639571 = 6959357) B6959357
theorem B3093047 : Blo 2061435 3093047 := bstep (se 1 (by rfl) ⟨2319785, by rfl⟩ : syracuseStep 3093047 = 4639571) B4639571
theorem B2062031 : Blo 2061435 2062031 := bstep (se 1 (by rfl) ⟨1546523, by rfl⟩ : syracuseStep 2062031 = 3093047) B3093047
theorem B3093053 : Blo 2061435 3093053 := bbase (se 3 (by rfl) ⟨579947, by rfl⟩ : syracuseStep 3093053 = 1159895) (by norm_num)
theorem B2062035 : Blo 2061435 2062035 := bstep (se 1 (by rfl) ⟨1546526, by rfl⟩ : syracuseStep 2062035 = 3093053) B3093053
theorem B4639589 : Blo 2061435 4639589 := bbase (se 4 (by rfl) ⟨434961, by rfl⟩ : syracuseStep 4639589 = 869923) (by norm_num)
theorem B3093059 : Blo 2061435 3093059 := bstep (se 1 (by rfl) ⟨2319794, by rfl⟩ : syracuseStep 3093059 = 4639589) B4639589
theorem B2062039 : Blo 2061435 2062039 := bstep (se 1 (by rfl) ⟨1546529, by rfl⟩ : syracuseStep 2062039 = 3093059) B3093059
theorem B5219549 : Blo 2061435 5219549 := bbase (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) (by norm_num)
theorem B3479699 : Blo 2061435 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B2319799 : Blo 2061435 2319799 := bstep (se 1 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 2319799 = 3479699) B3479699
theorem B3093065 : Blo 2061435 3093065 := bstep (se 2 (by rfl) ⟨1159899, by rfl⟩ : syracuseStep 3093065 = 2319799) B2319799
theorem B2062043 : Blo 2061435 2062043 := bstep (se 1 (by rfl) ⟨1546532, by rfl⟩ : syracuseStep 2062043 = 3093065) B3093065
theorem B3914669 : Blo 2061435 3914669 := bbase (se 3 (by rfl) ⟨734000, by rfl⟩ : syracuseStep 3914669 = 1468001) (by norm_num)
theorem B10439117 : Blo 2061435 10439117 := bstep (se 3 (by rfl) ⟨1957334, by rfl⟩ : syracuseStep 10439117 = 3914669) B3914669
theorem B6959411 : Blo 2061435 6959411 := bstep (se 1 (by rfl) ⟨5219558, by rfl⟩ : syracuseStep 6959411 = 10439117) B10439117
theorem B4639607 : Blo 2061435 4639607 := bstep (se 1 (by rfl) ⟨3479705, by rfl⟩ : syracuseStep 4639607 = 6959411) B6959411
theorem B3093071 : Blo 2061435 3093071 := bstep (se 1 (by rfl) ⟨2319803, by rfl⟩ : syracuseStep 3093071 = 4639607) B4639607
theorem B2062047 : Blo 2061435 2062047 := bstep (se 1 (by rfl) ⟨1546535, by rfl⟩ : syracuseStep 2062047 = 3093071) B3093071
theorem B3093077 : Blo 2061435 3093077 := bbase (se 8 (by rfl) ⟨18123, by rfl⟩ : syracuseStep 3093077 = 36247) (by norm_num)
theorem B2062051 : Blo 2061435 2062051 := bstep (se 1 (by rfl) ⟨1546538, by rfl⟩ : syracuseStep 2062051 = 3093077) B3093077
theorem B3817981 : Blo 2061435 3817981 := bbase (se 3 (by rfl) ⟨715871, by rfl⟩ : syracuseStep 3817981 = 1431743) (by norm_num)
theorem B20362565 : Blo 2061435 20362565 := bstep (se 4 (by rfl) ⟨1908990, by rfl⟩ : syracuseStep 20362565 = 3817981) B3817981
theorem B13575043 : Blo 2061435 13575043 := bstep (se 1 (by rfl) ⟨10181282, by rfl⟩ : syracuseStep 13575043 = 20362565) B20362565
theorem B18100057 : Blo 2061435 18100057 := bstep (se 2 (by rfl) ⟨6787521, by rfl⟩ : syracuseStep 18100057 = 13575043) B13575043
theorem B24133409 : Blo 2061435 24133409 := bstep (se 2 (by rfl) ⟨9050028, by rfl⟩ : syracuseStep 24133409 = 18100057) B18100057
theorem B16088939 : Blo 2061435 16088939 := bstep (se 1 (by rfl) ⟨12066704, by rfl⟩ : syracuseStep 16088939 = 24133409) B24133409
theorem B10725959 : Blo 2061435 10725959 := bstep (se 1 (by rfl) ⟨8044469, by rfl⟩ : syracuseStep 10725959 = 16088939) B16088939
theorem B28602557 : Blo 2061435 28602557 := bstep (se 3 (by rfl) ⟨5362979, by rfl⟩ : syracuseStep 28602557 = 10725959) B10725959
theorem B19068371 : Blo 2061435 19068371 := bstep (se 1 (by rfl) ⟨14301278, by rfl⟩ : syracuseStep 19068371 = 28602557) B28602557
theorem B12712247 : Blo 2061435 12712247 := bstep (se 1 (by rfl) ⟨9534185, by rfl⟩ : syracuseStep 12712247 = 19068371) B19068371
theorem B8474831 : Blo 2061435 8474831 := bstep (se 1 (by rfl) ⟨6356123, by rfl⟩ : syracuseStep 8474831 = 12712247) B12712247
theorem B5649887 : Blo 2061435 5649887 := bstep (se 1 (by rfl) ⟨4237415, by rfl⟩ : syracuseStep 5649887 = 8474831) B8474831
theorem B3766591 : Blo 2061435 3766591 := bstep (se 1 (by rfl) ⟨2824943, by rfl⟩ : syracuseStep 3766591 = 5649887) B5649887
theorem B20088485 : Blo 2061435 20088485 := bstep (se 4 (by rfl) ⟨1883295, by rfl⟩ : syracuseStep 20088485 = 3766591) B3766591
theorem B13392323 : Blo 2061435 13392323 := bstep (se 1 (by rfl) ⟨10044242, by rfl⟩ : syracuseStep 13392323 = 20088485) B20088485
theorem B8928215 : Blo 2061435 8928215 := bstep (se 1 (by rfl) ⟨6696161, by rfl⟩ : syracuseStep 8928215 = 13392323) B13392323
theorem B5952143 : Blo 2061435 5952143 := bstep (se 1 (by rfl) ⟨4464107, by rfl⟩ : syracuseStep 5952143 = 8928215) B8928215
theorem B15872381 : Blo 2061435 15872381 := bstep (se 3 (by rfl) ⟨2976071, by rfl⟩ : syracuseStep 15872381 = 5952143) B5952143
theorem B10581587 : Blo 2061435 10581587 := bstep (se 1 (by rfl) ⟨7936190, by rfl⟩ : syracuseStep 10581587 = 15872381) B15872381
theorem B7054391 : Blo 2061435 7054391 := bstep (se 1 (by rfl) ⟨5290793, by rfl⟩ : syracuseStep 7054391 = 10581587) B10581587
theorem B18811709 : Blo 2061435 18811709 := bstep (se 3 (by rfl) ⟨3527195, by rfl⟩ : syracuseStep 18811709 = 7054391) B7054391
theorem B12541139 : Blo 2061435 12541139 := bstep (se 1 (by rfl) ⟨9405854, by rfl⟩ : syracuseStep 12541139 = 18811709) B18811709
theorem B8360759 : Blo 2061435 8360759 := bstep (se 1 (by rfl) ⟨6270569, by rfl⟩ : syracuseStep 8360759 = 12541139) B12541139
theorem B22295357 : Blo 2061435 22295357 := bstep (se 3 (by rfl) ⟨4180379, by rfl⟩ : syracuseStep 22295357 = 8360759) B8360759
theorem B14863571 : Blo 2061435 14863571 := bstep (se 1 (by rfl) ⟨11147678, by rfl⟩ : syracuseStep 14863571 = 22295357) B22295357
theorem B9909047 : Blo 2061435 9909047 := bstep (se 1 (by rfl) ⟨7431785, by rfl⟩ : syracuseStep 9909047 = 14863571) B14863571
theorem B6606031 : Blo 2061435 6606031 := bstep (se 1 (by rfl) ⟨4954523, by rfl⟩ : syracuseStep 6606031 = 9909047) B9909047
theorem B8808041 : Blo 2061435 8808041 := bstep (se 2 (by rfl) ⟨3303015, by rfl⟩ : syracuseStep 8808041 = 6606031) B6606031
theorem B5872027 : Blo 2061435 5872027 := bstep (se 1 (by rfl) ⟨4404020, by rfl⟩ : syracuseStep 5872027 = 8808041) B8808041
theorem B7829369 : Blo 2061435 7829369 := bstep (se 2 (by rfl) ⟨2936013, by rfl⟩ : syracuseStep 7829369 = 5872027) B5872027
theorem B5219579 : Blo 2061435 5219579 := bstep (se 1 (by rfl) ⟨3914684, by rfl⟩ : syracuseStep 5219579 = 7829369) B7829369
theorem B3479719 : Blo 2061435 3479719 := bstep (se 1 (by rfl) ⟨2609789, by rfl⟩ : syracuseStep 3479719 = 5219579) B5219579
theorem B4639625 : Blo 2061435 4639625 := bstep (se 2 (by rfl) ⟨1739859, by rfl⟩ : syracuseStep 4639625 = 3479719) B3479719
theorem B3093083 : Blo 2061435 3093083 := bstep (se 1 (by rfl) ⟨2319812, by rfl⟩ : syracuseStep 3093083 = 4639625) B4639625
theorem B2062055 : Blo 2061435 2062055 := bstep (se 1 (by rfl) ⟨1546541, by rfl⟩ : syracuseStep 2062055 = 3093083) B3093083
theorem B2319817 : Blo 2061435 2319817 := bbase (se 2 (by rfl) ⟨869931, by rfl⟩ : syracuseStep 2319817 = 1739863) (by norm_num)
theorem B3093089 : Blo 2061435 3093089 := bstep (se 2 (by rfl) ⟨1159908, by rfl⟩ : syracuseStep 3093089 = 2319817) B2319817
theorem B2062059 : Blo 2061435 2062059 := bstep (se 1 (by rfl) ⟨1546544, by rfl⟩ : syracuseStep 2062059 = 3093089) B3093089
theorem B17616149 : Blo 2061435 17616149 := bbase (se 6 (by rfl) ⟨412878, by rfl⟩ : syracuseStep 17616149 = 825757) (by norm_num)
theorem B11744099 : Blo 2061435 11744099 := bstep (se 1 (by rfl) ⟨8808074, by rfl⟩ : syracuseStep 11744099 = 17616149) B17616149
theorem B7829399 : Blo 2061435 7829399 := bstep (se 1 (by rfl) ⟨5872049, by rfl⟩ : syracuseStep 7829399 = 11744099) B11744099
theorem B5219599 : Blo 2061435 5219599 := bstep (se 1 (by rfl) ⟨3914699, by rfl⟩ : syracuseStep 5219599 = 7829399) B7829399
theorem B6959465 : Blo 2061435 6959465 := bstep (se 2 (by rfl) ⟨2609799, by rfl⟩ : syracuseStep 6959465 = 5219599) B5219599
theorem B4639643 : Blo 2061435 4639643 := bstep (se 1 (by rfl) ⟨3479732, by rfl⟩ : syracuseStep 4639643 = 6959465) B6959465
theorem B3093095 : Blo 2061435 3093095 := bstep (se 1 (by rfl) ⟨2319821, by rfl⟩ : syracuseStep 3093095 = 4639643) B4639643
theorem B2062063 : Blo 2061435 2062063 := bstep (se 1 (by rfl) ⟨1546547, by rfl⟩ : syracuseStep 2062063 = 3093095) B3093095
theorem B3093101 : Blo 2061435 3093101 := bbase (se 3 (by rfl) ⟨579956, by rfl⟩ : syracuseStep 3093101 = 1159913) (by norm_num)
theorem B2062067 : Blo 2061435 2062067 := bstep (se 1 (by rfl) ⟨1546550, by rfl⟩ : syracuseStep 2062067 = 3093101) B3093101
theorem B4639661 : Blo 2061435 4639661 := bbase (se 3 (by rfl) ⟨869936, by rfl⟩ : syracuseStep 4639661 = 1739873) (by norm_num)
theorem B3093107 : Blo 2061435 3093107 := bstep (se 1 (by rfl) ⟨2319830, by rfl⟩ : syracuseStep 3093107 = 4639661) B4639661
theorem B2062071 : Blo 2061435 2062071 := bstep (se 1 (by rfl) ⟨1546553, by rfl⟩ : syracuseStep 2062071 = 3093107) B3093107
theorem B5872085 : Blo 2061435 5872085 := bbase (se 7 (by rfl) ⟨68813, by rfl⟩ : syracuseStep 5872085 = 137627) (by norm_num)
theorem B3914723 : Blo 2061435 3914723 := bstep (se 1 (by rfl) ⟨2936042, by rfl⟩ : syracuseStep 3914723 = 5872085) B5872085
theorem B2609815 : Blo 2061435 2609815 := bstep (se 1 (by rfl) ⟨1957361, by rfl⟩ : syracuseStep 2609815 = 3914723) B3914723
theorem B3479753 : Blo 2061435 3479753 := bstep (se 2 (by rfl) ⟨1304907, by rfl⟩ : syracuseStep 3479753 = 2609815) B2609815
theorem B2319835 : Blo 2061435 2319835 := bstep (se 1 (by rfl) ⟨1739876, by rfl⟩ : syracuseStep 2319835 = 3479753) B3479753
theorem B3093113 : Blo 2061435 3093113 := bstep (se 2 (by rfl) ⟨1159917, by rfl⟩ : syracuseStep 3093113 = 2319835) B2319835
theorem B2062075 : Blo 2061435 2062075 := bstep (se 1 (by rfl) ⟨1546556, by rfl⟩ : syracuseStep 2062075 = 3093113) B3093113
theorem B7533269 : Blo 2061435 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B5022179 : Blo 2061435 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B3348119 : Blo 2061435 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2232079 : Blo 2061435 2232079 := bstep (se 1 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 2232079 = 3348119) B3348119
theorem B11904421 : Blo 2061435 11904421 := bstep (se 4 (by rfl) ⟨1116039, by rfl⟩ : syracuseStep 11904421 = 2232079) B2232079
theorem B15872561 : Blo 2061435 15872561 := bstep (se 2 (by rfl) ⟨5952210, by rfl⟩ : syracuseStep 15872561 = 11904421) B11904421
theorem B10581707 : Blo 2061435 10581707 := bstep (se 1 (by rfl) ⟨7936280, by rfl⟩ : syracuseStep 10581707 = 15872561) B15872561
theorem B7054471 : Blo 2061435 7054471 := bstep (se 1 (by rfl) ⟨5290853, by rfl⟩ : syracuseStep 7054471 = 10581707) B10581707
theorem B37623845 : Blo 2061435 37623845 := bstep (se 4 (by rfl) ⟨3527235, by rfl⟩ : syracuseStep 37623845 = 7054471) B7054471
theorem B25082563 : Blo 2061435 25082563 := bstep (se 1 (by rfl) ⟨18811922, by rfl⟩ : syracuseStep 25082563 = 37623845) B37623845
theorem B33443417 : Blo 2061435 33443417 := bstep (se 2 (by rfl) ⟨12541281, by rfl⟩ : syracuseStep 33443417 = 25082563) B25082563
theorem B22295611 : Blo 2061435 22295611 := bstep (se 1 (by rfl) ⟨16721708, by rfl⟩ : syracuseStep 22295611 = 33443417) B33443417
theorem B29727481 : Blo 2061435 29727481 := bstep (se 2 (by rfl) ⟨11147805, by rfl⟩ : syracuseStep 29727481 = 22295611) B22295611
theorem B39636641 : Blo 2061435 39636641 := bstep (se 2 (by rfl) ⟨14863740, by rfl⟩ : syracuseStep 39636641 = 29727481) B29727481
theorem B26424427 : Blo 2061435 26424427 := bstep (se 1 (by rfl) ⟨19818320, by rfl⟩ : syracuseStep 26424427 = 39636641) B39636641
theorem B35232569 : Blo 2061435 35232569 := bstep (se 2 (by rfl) ⟨13212213, by rfl⟩ : syracuseStep 35232569 = 26424427) B26424427
theorem B23488379 : Blo 2061435 23488379 := bstep (se 1 (by rfl) ⟨17616284, by rfl⟩ : syracuseStep 23488379 = 35232569) B35232569
theorem B15658919 : Blo 2061435 15658919 := bstep (se 1 (by rfl) ⟨11744189, by rfl⟩ : syracuseStep 15658919 = 23488379) B23488379
theorem B10439279 : Blo 2061435 10439279 := bstep (se 1 (by rfl) ⟨7829459, by rfl⟩ : syracuseStep 10439279 = 15658919) B15658919
theorem B6959519 : Blo 2061435 6959519 := bstep (se 1 (by rfl) ⟨5219639, by rfl⟩ : syracuseStep 6959519 = 10439279) B10439279
theorem B4639679 : Blo 2061435 4639679 := bstep (se 1 (by rfl) ⟨3479759, by rfl⟩ : syracuseStep 4639679 = 6959519) B6959519
theorem B3093119 : Blo 2061435 3093119 := bstep (se 1 (by rfl) ⟨2319839, by rfl⟩ : syracuseStep 3093119 = 4639679) B4639679
theorem B2062079 : Blo 2061435 2062079 := bstep (se 1 (by rfl) ⟨1546559, by rfl⟩ : syracuseStep 2062079 = 3093119) B3093119
theorem B3093125 : Blo 2061435 3093125 := bbase (se 4 (by rfl) ⟨289980, by rfl⟩ : syracuseStep 3093125 = 579961) (by norm_num)
theorem B2062083 : Blo 2061435 2062083 := bstep (se 1 (by rfl) ⟨1546562, by rfl⟩ : syracuseStep 2062083 = 3093125) B3093125
theorem B3479773 : Blo 2061435 3479773 := bbase (se 3 (by rfl) ⟨652457, by rfl⟩ : syracuseStep 3479773 = 1304915) (by norm_num)
theorem B4639697 : Blo 2061435 4639697 := bstep (se 2 (by rfl) ⟨1739886, by rfl⟩ : syracuseStep 4639697 = 3479773) B3479773
theorem B3093131 : Blo 2061435 3093131 := bstep (se 1 (by rfl) ⟨2319848, by rfl⟩ : syracuseStep 3093131 = 4639697) B4639697
theorem B2062087 : Blo 2061435 2062087 := bstep (se 1 (by rfl) ⟨1546565, by rfl⟩ : syracuseStep 2062087 = 3093131) B3093131
theorem B2319853 : Blo 2061435 2319853 := bbase (se 3 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 2319853 = 869945) (by norm_num)
theorem B3093137 : Blo 2061435 3093137 := bstep (se 2 (by rfl) ⟨1159926, by rfl⟩ : syracuseStep 3093137 = 2319853) B2319853
theorem B2062091 : Blo 2061435 2062091 := bstep (se 1 (by rfl) ⟨1546568, by rfl⟩ : syracuseStep 2062091 = 3093137) B3093137
theorem B6959573 : Blo 2061435 6959573 := bbase (se 7 (by rfl) ⟨81557, by rfl⟩ : syracuseStep 6959573 = 163115) (by norm_num)
theorem B4639715 : Blo 2061435 4639715 := bstep (se 1 (by rfl) ⟨3479786, by rfl⟩ : syracuseStep 4639715 = 6959573) B6959573
theorem B3093143 : Blo 2061435 3093143 := bstep (se 1 (by rfl) ⟨2319857, by rfl⟩ : syracuseStep 3093143 = 4639715) B4639715
theorem B2062095 : Blo 2061435 2062095 := bstep (se 1 (by rfl) ⟨1546571, by rfl⟩ : syracuseStep 2062095 = 3093143) B3093143
theorem B3093149 : Blo 2061435 3093149 := bbase (se 3 (by rfl) ⟨579965, by rfl⟩ : syracuseStep 3093149 = 1159931) (by norm_num)
theorem B2062099 : Blo 2061435 2062099 := bstep (se 1 (by rfl) ⟨1546574, by rfl⟩ : syracuseStep 2062099 = 3093149) B3093149
theorem B4639733 : Blo 2061435 4639733 := bbase (se 5 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 4639733 = 434975) (by norm_num)
theorem B3093155 : Blo 2061435 3093155 := bstep (se 1 (by rfl) ⟨2319866, by rfl⟩ : syracuseStep 3093155 = 4639733) B4639733
theorem B2062103 : Blo 2061435 2062103 := bstep (se 1 (by rfl) ⟨1546577, by rfl⟩ : syracuseStep 2062103 = 3093155) B3093155
theorem B5952293 : Blo 2061435 5952293 := bbase (se 4 (by rfl) ⟨558027, by rfl⟩ : syracuseStep 5952293 = 1116055) (by norm_num)
theorem B3968195 : Blo 2061435 3968195 := bstep (se 1 (by rfl) ⟨2976146, by rfl⟩ : syracuseStep 3968195 = 5952293) B5952293
theorem B10581853 : Blo 2061435 10581853 := bstep (se 3 (by rfl) ⟨1984097, by rfl⟩ : syracuseStep 10581853 = 3968195) B3968195
theorem B14109137 : Blo 2061435 14109137 := bstep (se 2 (by rfl) ⟨5290926, by rfl⟩ : syracuseStep 14109137 = 10581853) B10581853
theorem B9406091 : Blo 2061435 9406091 := bstep (se 1 (by rfl) ⟨7054568, by rfl⟩ : syracuseStep 9406091 = 14109137) B14109137
theorem B25082909 : Blo 2061435 25082909 := bstep (se 3 (by rfl) ⟨4703045, by rfl⟩ : syracuseStep 25082909 = 9406091) B9406091
theorem B16721939 : Blo 2061435 16721939 := bstep (se 1 (by rfl) ⟨12541454, by rfl⟩ : syracuseStep 16721939 = 25082909) B25082909
theorem B11147959 : Blo 2061435 11147959 := bstep (se 1 (by rfl) ⟨8360969, by rfl⟩ : syracuseStep 11147959 = 16721939) B16721939
theorem B59455781 : Blo 2061435 59455781 := bstep (se 4 (by rfl) ⟨5573979, by rfl⟩ : syracuseStep 59455781 = 11147959) B11147959
theorem B39637187 : Blo 2061435 39637187 := bstep (se 1 (by rfl) ⟨29727890, by rfl⟩ : syracuseStep 39637187 = 59455781) B59455781
theorem B26424791 : Blo 2061435 26424791 := bstep (se 1 (by rfl) ⟨19818593, by rfl⟩ : syracuseStep 26424791 = 39637187) B39637187
theorem B17616527 : Blo 2061435 17616527 := bstep (se 1 (by rfl) ⟨13212395, by rfl⟩ : syracuseStep 17616527 = 26424791) B26424791
theorem B11744351 : Blo 2061435 11744351 := bstep (se 1 (by rfl) ⟨8808263, by rfl⟩ : syracuseStep 11744351 = 17616527) B17616527
theorem B7829567 : Blo 2061435 7829567 := bstep (se 1 (by rfl) ⟨5872175, by rfl⟩ : syracuseStep 7829567 = 11744351) B11744351
theorem B5219711 : Blo 2061435 5219711 := bstep (se 1 (by rfl) ⟨3914783, by rfl⟩ : syracuseStep 5219711 = 7829567) B7829567
theorem B3479807 : Blo 2061435 3479807 := bstep (se 1 (by rfl) ⟨2609855, by rfl⟩ : syracuseStep 3479807 = 5219711) B5219711
theorem B2319871 : Blo 2061435 2319871 := bstep (se 1 (by rfl) ⟨1739903, by rfl⟩ : syracuseStep 2319871 = 3479807) B3479807
theorem B3093161 : Blo 2061435 3093161 := bstep (se 2 (by rfl) ⟨1159935, by rfl⟩ : syracuseStep 3093161 = 2319871) B2319871
theorem B2062107 : Blo 2061435 2062107 := bstep (se 1 (by rfl) ⟨1546580, by rfl⟩ : syracuseStep 2062107 = 3093161) B3093161
theorem B2936093 : Blo 2061435 2936093 := bbase (se 3 (by rfl) ⟨550517, by rfl⟩ : syracuseStep 2936093 = 1101035) (by norm_num)
theorem B7829581 : Blo 2061435 7829581 := bstep (se 3 (by rfl) ⟨1468046, by rfl⟩ : syracuseStep 7829581 = 2936093) B2936093
theorem B10439441 : Blo 2061435 10439441 := bstep (se 2 (by rfl) ⟨3914790, by rfl⟩ : syracuseStep 10439441 = 7829581) B7829581
theorem B6959627 : Blo 2061435 6959627 := bstep (se 1 (by rfl) ⟨5219720, by rfl⟩ : syracuseStep 6959627 = 10439441) B10439441
theorem B4639751 : Blo 2061435 4639751 := bstep (se 1 (by rfl) ⟨3479813, by rfl⟩ : syracuseStep 4639751 = 6959627) B6959627
theorem B3093167 : Blo 2061435 3093167 := bstep (se 1 (by rfl) ⟨2319875, by rfl⟩ : syracuseStep 3093167 = 4639751) B4639751
theorem B2062111 : Blo 2061435 2062111 := bstep (se 1 (by rfl) ⟨1546583, by rfl⟩ : syracuseStep 2062111 = 3093167) B3093167
theorem B3093173 : Blo 2061435 3093173 := bbase (se 5 (by rfl) ⟨144992, by rfl⟩ : syracuseStep 3093173 = 289985) (by norm_num)
theorem B2062115 : Blo 2061435 2062115 := bstep (se 1 (by rfl) ⟨1546586, by rfl⟩ : syracuseStep 2062115 = 3093173) B3093173
theorem B5219741 : Blo 2061435 5219741 := bbase (se 3 (by rfl) ⟨978701, by rfl⟩ : syracuseStep 5219741 = 1957403) (by norm_num)
theorem B3479827 : Blo 2061435 3479827 := bstep (se 1 (by rfl) ⟨2609870, by rfl⟩ : syracuseStep 3479827 = 5219741) B5219741
theorem B4639769 : Blo 2061435 4639769 := bstep (se 2 (by rfl) ⟨1739913, by rfl⟩ : syracuseStep 4639769 = 3479827) B3479827
theorem B3093179 : Blo 2061435 3093179 := bstep (se 1 (by rfl) ⟨2319884, by rfl⟩ : syracuseStep 3093179 = 4639769) B4639769
theorem B2062119 : Blo 2061435 2062119 := bstep (se 1 (by rfl) ⟨1546589, by rfl⟩ : syracuseStep 2062119 = 3093179) B3093179
theorem B2319889 : Blo 2061435 2319889 := bbase (se 2 (by rfl) ⟨869958, by rfl⟩ : syracuseStep 2319889 = 1739917) (by norm_num)
theorem B3093185 : Blo 2061435 3093185 := bstep (se 2 (by rfl) ⟨1159944, by rfl⟩ : syracuseStep 3093185 = 2319889) B2319889
theorem B2062123 : Blo 2061435 2062123 := bstep (se 1 (by rfl) ⟨1546592, by rfl⟩ : syracuseStep 2062123 = 3093185) B3093185
theorem B3914821 : Blo 2061435 3914821 := bbase (se 4 (by rfl) ⟨367014, by rfl⟩ : syracuseStep 3914821 = 734029) (by norm_num)
theorem B5219761 : Blo 2061435 5219761 := bstep (se 2 (by rfl) ⟨1957410, by rfl⟩ : syracuseStep 5219761 = 3914821) B3914821
theorem B6959681 : Blo 2061435 6959681 := bstep (se 2 (by rfl) ⟨2609880, by rfl⟩ : syracuseStep 6959681 = 5219761) B5219761
theorem B4639787 : Blo 2061435 4639787 := bstep (se 1 (by rfl) ⟨3479840, by rfl⟩ : syracuseStep 4639787 = 6959681) B6959681
theorem B3093191 : Blo 2061435 3093191 := bstep (se 1 (by rfl) ⟨2319893, by rfl⟩ : syracuseStep 3093191 = 4639787) B4639787
theorem B2062127 : Blo 2061435 2062127 := bstep (se 1 (by rfl) ⟨1546595, by rfl⟩ : syracuseStep 2062127 = 3093191) B3093191
theorem B3093197 : Blo 2061435 3093197 := bbase (se 3 (by rfl) ⟨579974, by rfl⟩ : syracuseStep 3093197 = 1159949) (by norm_num)
theorem B2062131 : Blo 2061435 2062131 := bstep (se 1 (by rfl) ⟨1546598, by rfl⟩ : syracuseStep 2062131 = 3093197) B3093197
theorem B4639805 : Blo 2061435 4639805 := bbase (se 3 (by rfl) ⟨869963, by rfl⟩ : syracuseStep 4639805 = 1739927) (by norm_num)
theorem B3093203 : Blo 2061435 3093203 := bstep (se 1 (by rfl) ⟨2319902, by rfl⟩ : syracuseStep 3093203 = 4639805) B4639805
theorem B2062135 : Blo 2061435 2062135 := bstep (se 1 (by rfl) ⟨1546601, by rfl⟩ : syracuseStep 2062135 = 3093203) B3093203
theorem B3479861 : Blo 2061435 3479861 := bbase (se 5 (by rfl) ⟨163118, by rfl⟩ : syracuseStep 3479861 = 326237) (by norm_num)
theorem B2319907 : Blo 2061435 2319907 := bstep (se 1 (by rfl) ⟨1739930, by rfl⟩ : syracuseStep 2319907 = 3479861) B3479861
theorem B3093209 : Blo 2061435 3093209 := bstep (se 2 (by rfl) ⟨1159953, by rfl⟩ : syracuseStep 3093209 = 2319907) B2319907
theorem B2062139 : Blo 2061435 2062139 := bstep (se 1 (by rfl) ⟨1546604, by rfl⟩ : syracuseStep 2062139 = 3093209) B3093209
theorem B5872277 : Blo 2061435 5872277 := bbase (se 6 (by rfl) ⟨137631, by rfl⟩ : syracuseStep 5872277 = 275263) (by norm_num)
theorem B15659405 : Blo 2061435 15659405 := bstep (se 3 (by rfl) ⟨2936138, by rfl⟩ : syracuseStep 15659405 = 5872277) B5872277
theorem B10439603 : Blo 2061435 10439603 := bstep (se 1 (by rfl) ⟨7829702, by rfl⟩ : syracuseStep 10439603 = 15659405) B15659405
theorem B6959735 : Blo 2061435 6959735 := bstep (se 1 (by rfl) ⟨5219801, by rfl⟩ : syracuseStep 6959735 = 10439603) B10439603
theorem B4639823 : Blo 2061435 4639823 := bstep (se 1 (by rfl) ⟨3479867, by rfl⟩ : syracuseStep 4639823 = 6959735) B6959735
theorem B3093215 : Blo 2061435 3093215 := bstep (se 1 (by rfl) ⟨2319911, by rfl⟩ : syracuseStep 3093215 = 4639823) B4639823
theorem B2062143 : Blo 2061435 2062143 := bstep (se 1 (by rfl) ⟨1546607, by rfl⟩ : syracuseStep 2062143 = 3093215) B3093215
theorem B3093221 : Blo 2061435 3093221 := bbase (se 4 (by rfl) ⟨289989, by rfl⟩ : syracuseStep 3093221 = 579979) (by norm_num)
theorem B2062147 : Blo 2061435 2062147 := bstep (se 1 (by rfl) ⟨1546610, by rfl⟩ : syracuseStep 2062147 = 3093221) B3093221
theorem B2202113 : Blo 2061435 2202113 := bbase (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) (by norm_num)
theorem B5872301 : Blo 2061435 5872301 := bstep (se 3 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 5872301 = 2202113) B2202113
theorem B3914867 : Blo 2061435 3914867 := bstep (se 1 (by rfl) ⟨2936150, by rfl⟩ : syracuseStep 3914867 = 5872301) B5872301
theorem B2609911 : Blo 2061435 2609911 := bstep (se 1 (by rfl) ⟨1957433, by rfl⟩ : syracuseStep 2609911 = 3914867) B3914867
theorem B3479881 : Blo 2061435 3479881 := bstep (se 2 (by rfl) ⟨1304955, by rfl⟩ : syracuseStep 3479881 = 2609911) B2609911
theorem B4639841 : Blo 2061435 4639841 := bstep (se 2 (by rfl) ⟨1739940, by rfl⟩ : syracuseStep 4639841 = 3479881) B3479881
theorem B3093227 : Blo 2061435 3093227 := bstep (se 1 (by rfl) ⟨2319920, by rfl⟩ : syracuseStep 3093227 = 4639841) B4639841
theorem B2062151 : Blo 2061435 2062151 := bstep (se 1 (by rfl) ⟨1546613, by rfl⟩ : syracuseStep 2062151 = 3093227) B3093227
theorem B2319925 : Blo 2061435 2319925 := bbase (se 5 (by rfl) ⟨108746, by rfl⟩ : syracuseStep 2319925 = 217493) (by norm_num)
theorem B3093233 : Blo 2061435 3093233 := bstep (se 2 (by rfl) ⟨1159962, by rfl⟩ : syracuseStep 3093233 = 2319925) B2319925
theorem B2062155 : Blo 2061435 2062155 := bstep (se 1 (by rfl) ⟨1546616, by rfl⟩ : syracuseStep 2062155 = 3093233) B3093233
theorem B2609921 : Blo 2061435 2609921 := bbase (se 2 (by rfl) ⟨978720, by rfl⟩ : syracuseStep 2609921 = 1957441) (by norm_num)
theorem B6959789 : Blo 2061435 6959789 := bstep (se 3 (by rfl) ⟨1304960, by rfl⟩ : syracuseStep 6959789 = 2609921) B2609921
theorem B4639859 : Blo 2061435 4639859 := bstep (se 1 (by rfl) ⟨3479894, by rfl⟩ : syracuseStep 4639859 = 6959789) B6959789
theorem B3093239 : Blo 2061435 3093239 := bstep (se 1 (by rfl) ⟨2319929, by rfl⟩ : syracuseStep 3093239 = 4639859) B4639859
theorem B2062159 : Blo 2061435 2062159 := bstep (se 1 (by rfl) ⟨1546619, by rfl⟩ : syracuseStep 2062159 = 3093239) B3093239
theorem B3093245 : Blo 2061435 3093245 := bbase (se 3 (by rfl) ⟨579983, by rfl⟩ : syracuseStep 3093245 = 1159967) (by norm_num)
theorem B2062163 : Blo 2061435 2062163 := bstep (se 1 (by rfl) ⟨1546622, by rfl⟩ : syracuseStep 2062163 = 3093245) B3093245
theorem B4639877 : Blo 2061435 4639877 := bbase (se 4 (by rfl) ⟨434988, by rfl⟩ : syracuseStep 4639877 = 869977) (by norm_num)
theorem B3093251 : Blo 2061435 3093251 := bstep (se 1 (by rfl) ⟨2319938, by rfl⟩ : syracuseStep 3093251 = 4639877) B4639877
theorem B2062167 : Blo 2061435 2062167 := bstep (se 1 (by rfl) ⟨1546625, by rfl⟩ : syracuseStep 2062167 = 3093251) B3093251
theorem B4404269 : Blo 2061435 4404269 := bbase (se 3 (by rfl) ⟨825800, by rfl⟩ : syracuseStep 4404269 = 1651601) (by norm_num)
theorem B2936179 : Blo 2061435 2936179 := bstep (se 1 (by rfl) ⟨2202134, by rfl⟩ : syracuseStep 2936179 = 4404269) B4404269
theorem B3914905 : Blo 2061435 3914905 := bstep (se 2 (by rfl) ⟨1468089, by rfl⟩ : syracuseStep 3914905 = 2936179) B2936179
theorem B5219873 : Blo 2061435 5219873 := bstep (se 2 (by rfl) ⟨1957452, by rfl⟩ : syracuseStep 5219873 = 3914905) B3914905
theorem B3479915 : Blo 2061435 3479915 := bstep (se 1 (by rfl) ⟨2609936, by rfl⟩ : syracuseStep 3479915 = 5219873) B5219873
theorem B2319943 : Blo 2061435 2319943 := bstep (se 1 (by rfl) ⟨1739957, by rfl⟩ : syracuseStep 2319943 = 3479915) B3479915
theorem B3093257 : Blo 2061435 3093257 := bstep (se 2 (by rfl) ⟨1159971, by rfl⟩ : syracuseStep 3093257 = 2319943) B2319943
theorem B2062171 : Blo 2061435 2062171 := bstep (se 1 (by rfl) ⟨1546628, by rfl⟩ : syracuseStep 2062171 = 3093257) B3093257
theorem B10439765 : Blo 2061435 10439765 := bbase (se 8 (by rfl) ⟨61170, by rfl⟩ : syracuseStep 10439765 = 122341) (by norm_num)
theorem B6959843 : Blo 2061435 6959843 := bstep (se 1 (by rfl) ⟨5219882, by rfl⟩ : syracuseStep 6959843 = 10439765) B10439765
theorem B4639895 : Blo 2061435 4639895 := bstep (se 1 (by rfl) ⟨3479921, by rfl⟩ : syracuseStep 4639895 = 6959843) B6959843
theorem B3093263 : Blo 2061435 3093263 := bstep (se 1 (by rfl) ⟨2319947, by rfl⟩ : syracuseStep 3093263 = 4639895) B4639895
theorem B2062175 : Blo 2061435 2062175 := bstep (se 1 (by rfl) ⟨1546631, by rfl⟩ : syracuseStep 2062175 = 3093263) B3093263
theorem B3093269 : Blo 2061435 3093269 := bbase (se 6 (by rfl) ⟨72498, by rfl⟩ : syracuseStep 3093269 = 144997) (by norm_num)
theorem B2062179 : Blo 2061435 2062179 := bstep (se 1 (by rfl) ⟨1546634, by rfl⟩ : syracuseStep 2062179 = 3093269) B3093269
theorem B16089941 : Blo 2061435 16089941 := bbase (se 9 (by rfl) ⟨47138, by rfl⟩ : syracuseStep 16089941 = 94277) (by norm_num)
theorem B10726627 : Blo 2061435 10726627 := bstep (se 1 (by rfl) ⟨8044970, by rfl⟩ : syracuseStep 10726627 = 16089941) B16089941
theorem B14302169 : Blo 2061435 14302169 := bstep (se 2 (by rfl) ⟨5363313, by rfl⟩ : syracuseStep 14302169 = 10726627) B10726627
theorem B9534779 : Blo 2061435 9534779 := bstep (se 1 (by rfl) ⟨7151084, by rfl⟩ : syracuseStep 9534779 = 14302169) B14302169
theorem B6356519 : Blo 2061435 6356519 := bstep (se 1 (by rfl) ⟨4767389, by rfl⟩ : syracuseStep 6356519 = 9534779) B9534779
theorem B4237679 : Blo 2061435 4237679 := bstep (se 1 (by rfl) ⟨3178259, by rfl⟩ : syracuseStep 4237679 = 6356519) B6356519
theorem B2825119 : Blo 2061435 2825119 := bstep (se 1 (by rfl) ⟨2118839, by rfl⟩ : syracuseStep 2825119 = 4237679) B4237679
theorem B3766825 : Blo 2061435 3766825 := bstep (se 2 (by rfl) ⟨1412559, by rfl⟩ : syracuseStep 3766825 = 2825119) B2825119
theorem B5022433 : Blo 2061435 5022433 := bstep (se 2 (by rfl) ⟨1883412, by rfl⟩ : syracuseStep 5022433 = 3766825) B3766825
theorem B6696577 : Blo 2061435 6696577 := bstep (se 2 (by rfl) ⟨2511216, by rfl⟩ : syracuseStep 6696577 = 5022433) B5022433
theorem B35715077 : Blo 2061435 35715077 := bstep (se 4 (by rfl) ⟨3348288, by rfl⟩ : syracuseStep 35715077 = 6696577) B6696577
theorem B23810051 : Blo 2061435 23810051 := bstep (se 1 (by rfl) ⟨17857538, by rfl⟩ : syracuseStep 23810051 = 35715077) B35715077
theorem B15873367 : Blo 2061435 15873367 := bstep (se 1 (by rfl) ⟨11905025, by rfl⟩ : syracuseStep 15873367 = 23810051) B23810051
theorem B21164489 : Blo 2061435 21164489 := bstep (se 2 (by rfl) ⟨7936683, by rfl⟩ : syracuseStep 21164489 = 15873367) B15873367
theorem B14109659 : Blo 2061435 14109659 := bstep (se 1 (by rfl) ⟨10582244, by rfl⟩ : syracuseStep 14109659 = 21164489) B21164489
theorem B9406439 : Blo 2061435 9406439 := bstep (se 1 (by rfl) ⟨7054829, by rfl⟩ : syracuseStep 9406439 = 14109659) B14109659
theorem B6270959 : Blo 2061435 6270959 := bstep (se 1 (by rfl) ⟨4703219, by rfl⟩ : syracuseStep 6270959 = 9406439) B9406439
theorem B4180639 : Blo 2061435 4180639 := bstep (se 1 (by rfl) ⟨3135479, by rfl⟩ : syracuseStep 4180639 = 6270959) B6270959
theorem B5574185 : Blo 2061435 5574185 := bstep (se 2 (by rfl) ⟨2090319, by rfl⟩ : syracuseStep 5574185 = 4180639) B4180639
theorem B3716123 : Blo 2061435 3716123 := bstep (se 1 (by rfl) ⟨2787092, by rfl⟩ : syracuseStep 3716123 = 5574185) B5574185
theorem B39638645 : Blo 2061435 39638645 := bstep (se 5 (by rfl) ⟨1858061, by rfl⟩ : syracuseStep 39638645 = 3716123) B3716123
theorem B26425763 : Blo 2061435 26425763 := bstep (se 1 (by rfl) ⟨19819322, by rfl⟩ : syracuseStep 26425763 = 39638645) B39638645
theorem B17617175 : Blo 2061435 17617175 := bstep (se 1 (by rfl) ⟨13212881, by rfl⟩ : syracuseStep 17617175 = 26425763) B26425763
theorem B11744783 : Blo 2061435 11744783 := bstep (se 1 (by rfl) ⟨8808587, by rfl⟩ : syracuseStep 11744783 = 17617175) B17617175
theorem B7829855 : Blo 2061435 7829855 := bstep (se 1 (by rfl) ⟨5872391, by rfl⟩ : syracuseStep 7829855 = 11744783) B11744783
theorem B5219903 : Blo 2061435 5219903 := bstep (se 1 (by rfl) ⟨3914927, by rfl⟩ : syracuseStep 5219903 = 7829855) B7829855
theorem B3479935 : Blo 2061435 3479935 := bstep (se 1 (by rfl) ⟨2609951, by rfl⟩ : syracuseStep 3479935 = 5219903) B5219903
theorem B4639913 : Blo 2061435 4639913 := bstep (se 2 (by rfl) ⟨1739967, by rfl⟩ : syracuseStep 4639913 = 3479935) B3479935
theorem B3093275 : Blo 2061435 3093275 := bstep (se 1 (by rfl) ⟨2319956, by rfl⟩ : syracuseStep 3093275 = 4639913) B4639913
theorem B2062183 : Blo 2061435 2062183 := bstep (se 1 (by rfl) ⟨1546637, by rfl⟩ : syracuseStep 2062183 = 3093275) B3093275
theorem B2319961 : Blo 2061435 2319961 := bbase (se 2 (by rfl) ⟨869985, by rfl⟩ : syracuseStep 2319961 = 1739971) (by norm_num)
theorem B3093281 : Blo 2061435 3093281 := bstep (se 2 (by rfl) ⟨1159980, by rfl⟩ : syracuseStep 3093281 = 2319961) B2319961
theorem B2062187 : Blo 2061435 2062187 := bstep (se 1 (by rfl) ⟨1546640, by rfl⟩ : syracuseStep 2062187 = 3093281) B3093281
theorem B9909701 : Blo 2061435 9909701 := bbase (se 4 (by rfl) ⟨929034, by rfl⟩ : syracuseStep 9909701 = 1858069) (by norm_num)
theorem B6606467 : Blo 2061435 6606467 := bstep (se 1 (by rfl) ⟨4954850, by rfl⟩ : syracuseStep 6606467 = 9909701) B9909701
theorem B4404311 : Blo 2061435 4404311 := bstep (se 1 (by rfl) ⟨3303233, by rfl⟩ : syracuseStep 4404311 = 6606467) B6606467
theorem B2936207 : Blo 2061435 2936207 := bstep (se 1 (by rfl) ⟨2202155, by rfl⟩ : syracuseStep 2936207 = 4404311) B4404311
theorem B7829885 : Blo 2061435 7829885 := bstep (se 3 (by rfl) ⟨1468103, by rfl⟩ : syracuseStep 7829885 = 2936207) B2936207
theorem B5219923 : Blo 2061435 5219923 := bstep (se 1 (by rfl) ⟨3914942, by rfl⟩ : syracuseStep 5219923 = 7829885) B7829885
theorem B6959897 : Blo 2061435 6959897 := bstep (se 2 (by rfl) ⟨2609961, by rfl⟩ : syracuseStep 6959897 = 5219923) B5219923
theorem B4639931 : Blo 2061435 4639931 := bstep (se 1 (by rfl) ⟨3479948, by rfl⟩ : syracuseStep 4639931 = 6959897) B6959897
theorem B3093287 : Blo 2061435 3093287 := bstep (se 1 (by rfl) ⟨2319965, by rfl⟩ : syracuseStep 3093287 = 4639931) B4639931
theorem B2062191 : Blo 2061435 2062191 := bstep (se 1 (by rfl) ⟨1546643, by rfl⟩ : syracuseStep 2062191 = 3093287) B3093287
theorem B3093293 : Blo 2061435 3093293 := bbase (se 3 (by rfl) ⟨579992, by rfl⟩ : syracuseStep 3093293 = 1159985) (by norm_num)
theorem B2062195 : Blo 2061435 2062195 := bstep (se 1 (by rfl) ⟨1546646, by rfl⟩ : syracuseStep 2062195 = 3093293) B3093293
theorem B4639949 : Blo 2061435 4639949 := bbase (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) (by norm_num)
theorem B3093299 : Blo 2061435 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B2062199 : Blo 2061435 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B2609977 : Blo 2061435 2609977 := bbase (se 2 (by rfl) ⟨978741, by rfl⟩ : syracuseStep 2609977 = 1957483) (by norm_num)
theorem B3479969 : Blo 2061435 3479969 := bstep (se 2 (by rfl) ⟨1304988, by rfl⟩ : syracuseStep 3479969 = 2609977) B2609977
theorem B2319979 : Blo 2061435 2319979 := bstep (se 1 (by rfl) ⟨1739984, by rfl⟩ : syracuseStep 2319979 = 3479969) B3479969
theorem B3093305 : Blo 2061435 3093305 := bstep (se 2 (by rfl) ⟨1159989, by rfl⟩ : syracuseStep 3093305 = 2319979) B2319979
theorem B2062203 : Blo 2061435 2062203 := bstep (se 1 (by rfl) ⟨1546652, by rfl⟩ : syracuseStep 2062203 = 3093305) B3093305
theorem B6606517 : Blo 2061435 6606517 := bbase (se 5 (by rfl) ⟨309680, by rfl⟩ : syracuseStep 6606517 = 619361) (by norm_num)
theorem B8808689 : Blo 2061435 8808689 := bstep (se 2 (by rfl) ⟨3303258, by rfl⟩ : syracuseStep 8808689 = 6606517) B6606517
theorem B23489837 : Blo 2061435 23489837 := bstep (se 3 (by rfl) ⟨4404344, by rfl⟩ : syracuseStep 23489837 = 8808689) B8808689
theorem B15659891 : Blo 2061435 15659891 := bstep (se 1 (by rfl) ⟨11744918, by rfl⟩ : syracuseStep 15659891 = 23489837) B23489837
theorem B10439927 : Blo 2061435 10439927 := bstep (se 1 (by rfl) ⟨7829945, by rfl⟩ : syracuseStep 10439927 = 15659891) B15659891
theorem B6959951 : Blo 2061435 6959951 := bstep (se 1 (by rfl) ⟨5219963, by rfl⟩ : syracuseStep 6959951 = 10439927) B10439927
theorem B4639967 : Blo 2061435 4639967 := bstep (se 1 (by rfl) ⟨3479975, by rfl⟩ : syracuseStep 4639967 = 6959951) B6959951
theorem B3093311 : Blo 2061435 3093311 := bstep (se 1 (by rfl) ⟨2319983, by rfl⟩ : syracuseStep 3093311 = 4639967) B4639967
theorem B2062207 : Blo 2061435 2062207 := bstep (se 1 (by rfl) ⟨1546655, by rfl⟩ : syracuseStep 2062207 = 3093311) B3093311
theorem B3093317 : Blo 2061435 3093317 := bbase (se 4 (by rfl) ⟨289998, by rfl⟩ : syracuseStep 3093317 = 579997) (by norm_num)
theorem B2062211 : Blo 2061435 2062211 := bstep (se 1 (by rfl) ⟨1546658, by rfl⟩ : syracuseStep 2062211 = 3093317) B3093317
theorem B3479989 : Blo 2061435 3479989 := bbase (se 5 (by rfl) ⟨163124, by rfl⟩ : syracuseStep 3479989 = 326249) (by norm_num)
theorem B4639985 : Blo 2061435 4639985 := bstep (se 2 (by rfl) ⟨1739994, by rfl⟩ : syracuseStep 4639985 = 3479989) B3479989
theorem B3093323 : Blo 2061435 3093323 := bstep (se 1 (by rfl) ⟨2319992, by rfl⟩ : syracuseStep 3093323 = 4639985) B4639985
theorem B2062215 : Blo 2061435 2062215 := bstep (se 1 (by rfl) ⟨1546661, by rfl⟩ : syracuseStep 2062215 = 3093323) B3093323
theorem B2319997 : Blo 2061435 2319997 := bbase (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) (by norm_num)
theorem B3093329 : Blo 2061435 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B2062219 : Blo 2061435 2062219 := bstep (se 1 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 2062219 = 3093329) B3093329
theorem B6960005 : Blo 2061435 6960005 := bbase (se 4 (by rfl) ⟨652500, by rfl⟩ : syracuseStep 6960005 = 1305001) (by norm_num)
theorem B4640003 : Blo 2061435 4640003 := bstep (se 1 (by rfl) ⟨3480002, by rfl⟩ : syracuseStep 4640003 = 6960005) B6960005
theorem B3093335 : Blo 2061435 3093335 := bstep (se 1 (by rfl) ⟨2320001, by rfl⟩ : syracuseStep 3093335 = 4640003) B4640003
theorem B2062223 : Blo 2061435 2062223 := bstep (se 1 (by rfl) ⟨1546667, by rfl⟩ : syracuseStep 2062223 = 3093335) B3093335
theorem B3093341 : Blo 2061435 3093341 := bbase (se 3 (by rfl) ⟨580001, by rfl⟩ : syracuseStep 3093341 = 1160003) (by norm_num)
theorem B2062227 : Blo 2061435 2062227 := bstep (se 1 (by rfl) ⟨1546670, by rfl⟩ : syracuseStep 2062227 = 3093341) B3093341
theorem B4640021 : Blo 2061435 4640021 := bbase (se 6 (by rfl) ⟨108750, by rfl⟩ : syracuseStep 4640021 = 217501) (by norm_num)
theorem B3093347 : Blo 2061435 3093347 := bstep (se 1 (by rfl) ⟨2320010, by rfl⟩ : syracuseStep 3093347 = 4640021) B4640021
theorem B2062231 : Blo 2061435 2062231 := bstep (se 1 (by rfl) ⟨1546673, by rfl⟩ : syracuseStep 2062231 = 3093347) B3093347
theorem B7830053 : Blo 2061435 7830053 := bbase (se 4 (by rfl) ⟨734067, by rfl⟩ : syracuseStep 7830053 = 1468135) (by norm_num)
theorem B5220035 : Blo 2061435 5220035 := bstep (se 1 (by rfl) ⟨3915026, by rfl⟩ : syracuseStep 5220035 = 7830053) B7830053
theorem B3480023 : Blo 2061435 3480023 := bstep (se 1 (by rfl) ⟨2610017, by rfl⟩ : syracuseStep 3480023 = 5220035) B5220035
theorem B2320015 : Blo 2061435 2320015 := bstep (se 1 (by rfl) ⟨1740011, by rfl⟩ : syracuseStep 2320015 = 3480023) B3480023
theorem B3093353 : Blo 2061435 3093353 := bstep (se 2 (by rfl) ⟨1160007, by rfl⟩ : syracuseStep 3093353 = 2320015) B2320015
theorem B2062235 : Blo 2061435 2062235 := bstep (se 1 (by rfl) ⟨1546676, by rfl⟩ : syracuseStep 2062235 = 3093353) B3093353
theorem B4404413 : Blo 2061435 4404413 := bbase (se 3 (by rfl) ⟨825827, by rfl⟩ : syracuseStep 4404413 = 1651655) (by norm_num)
theorem B11745101 : Blo 2061435 11745101 := bstep (se 3 (by rfl) ⟨2202206, by rfl⟩ : syracuseStep 11745101 = 4404413) B4404413
theorem B7830067 : Blo 2061435 7830067 := bstep (se 1 (by rfl) ⟨5872550, by rfl⟩ : syracuseStep 7830067 = 11745101) B11745101
theorem B10440089 : Blo 2061435 10440089 := bstep (se 2 (by rfl) ⟨3915033, by rfl⟩ : syracuseStep 10440089 = 7830067) B7830067
theorem B6960059 : Blo 2061435 6960059 := bstep (se 1 (by rfl) ⟨5220044, by rfl⟩ : syracuseStep 6960059 = 10440089) B10440089
theorem B4640039 : Blo 2061435 4640039 := bstep (se 1 (by rfl) ⟨3480029, by rfl⟩ : syracuseStep 4640039 = 6960059) B6960059
theorem B3093359 : Blo 2061435 3093359 := bstep (se 1 (by rfl) ⟨2320019, by rfl⟩ : syracuseStep 3093359 = 4640039) B4640039
theorem B2062239 : Blo 2061435 2062239 := bstep (se 1 (by rfl) ⟨1546679, by rfl⟩ : syracuseStep 2062239 = 3093359) B3093359
theorem B3093365 : Blo 2061435 3093365 := bbase (se 5 (by rfl) ⟨145001, by rfl⟩ : syracuseStep 3093365 = 290003) (by norm_num)
theorem B2062243 : Blo 2061435 2062243 := bstep (se 1 (by rfl) ⟨1546682, by rfl⟩ : syracuseStep 2062243 = 3093365) B3093365
theorem B3527525 : Blo 2061435 3527525 := bbase (se 4 (by rfl) ⟨330705, by rfl⟩ : syracuseStep 3527525 = 661411) (by norm_num)
theorem B2351683 : Blo 2061435 2351683 := bstep (se 1 (by rfl) ⟨1763762, by rfl⟩ : syracuseStep 2351683 = 3527525) B3527525
theorem B12542309 : Blo 2061435 12542309 := bstep (se 4 (by rfl) ⟨1175841, by rfl⟩ : syracuseStep 12542309 = 2351683) B2351683
theorem B8361539 : Blo 2061435 8361539 := bstep (se 1 (by rfl) ⟨6271154, by rfl⟩ : syracuseStep 8361539 = 12542309) B12542309
theorem B5574359 : Blo 2061435 5574359 := bstep (se 1 (by rfl) ⟨4180769, by rfl⟩ : syracuseStep 5574359 = 8361539) B8361539
theorem B14864957 : Blo 2061435 14864957 := bstep (se 3 (by rfl) ⟨2787179, by rfl⟩ : syracuseStep 14864957 = 5574359) B5574359
theorem B9909971 : Blo 2061435 9909971 := bstep (se 1 (by rfl) ⟨7432478, by rfl⟩ : syracuseStep 9909971 = 14864957) B14864957
theorem B6606647 : Blo 2061435 6606647 := bstep (se 1 (by rfl) ⟨4954985, by rfl⟩ : syracuseStep 6606647 = 9909971) B9909971
theorem B4404431 : Blo 2061435 4404431 := bstep (se 1 (by rfl) ⟨3303323, by rfl⟩ : syracuseStep 4404431 = 6606647) B6606647
theorem B2936287 : Blo 2061435 2936287 := bstep (se 1 (by rfl) ⟨2202215, by rfl⟩ : syracuseStep 2936287 = 4404431) B4404431
theorem B3915049 : Blo 2061435 3915049 := bstep (se 2 (by rfl) ⟨1468143, by rfl⟩ : syracuseStep 3915049 = 2936287) B2936287
theorem B5220065 : Blo 2061435 5220065 := bstep (se 2 (by rfl) ⟨1957524, by rfl⟩ : syracuseStep 5220065 = 3915049) B3915049
theorem B3480043 : Blo 2061435 3480043 := bstep (se 1 (by rfl) ⟨2610032, by rfl⟩ : syracuseStep 3480043 = 5220065) B5220065
theorem B4640057 : Blo 2061435 4640057 := bstep (se 2 (by rfl) ⟨1740021, by rfl⟩ : syracuseStep 4640057 = 3480043) B3480043
theorem B3093371 : Blo 2061435 3093371 := bstep (se 1 (by rfl) ⟨2320028, by rfl⟩ : syracuseStep 3093371 = 4640057) B4640057
theorem B2062247 : Blo 2061435 2062247 := bstep (se 1 (by rfl) ⟨1546685, by rfl⟩ : syracuseStep 2062247 = 3093371) B3093371
theorem B2320033 : Blo 2061435 2320033 := bbase (se 2 (by rfl) ⟨870012, by rfl⟩ : syracuseStep 2320033 = 1740025) (by norm_num)
theorem B3093377 : Blo 2061435 3093377 := bstep (se 2 (by rfl) ⟨1160016, by rfl⟩ : syracuseStep 3093377 = 2320033) B2320033
theorem B2062251 : Blo 2061435 2062251 := bstep (se 1 (by rfl) ⟨1546688, by rfl⟩ : syracuseStep 2062251 = 3093377) B3093377
theorem B5220085 : Blo 2061435 5220085 := bbase (se 5 (by rfl) ⟨244691, by rfl⟩ : syracuseStep 5220085 = 489383) (by norm_num)
theorem B6960113 : Blo 2061435 6960113 := bstep (se 2 (by rfl) ⟨2610042, by rfl⟩ : syracuseStep 6960113 = 5220085) B5220085
theorem B4640075 : Blo 2061435 4640075 := bstep (se 1 (by rfl) ⟨3480056, by rfl⟩ : syracuseStep 4640075 = 6960113) B6960113
theorem B3093383 : Blo 2061435 3093383 := bstep (se 1 (by rfl) ⟨2320037, by rfl⟩ : syracuseStep 3093383 = 4640075) B4640075
theorem B2062255 : Blo 2061435 2062255 := bstep (se 1 (by rfl) ⟨1546691, by rfl⟩ : syracuseStep 2062255 = 3093383) B3093383
theorem B3093389 : Blo 2061435 3093389 := bbase (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) (by norm_num)
theorem B2062259 : Blo 2061435 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B4640093 : Blo 2061435 4640093 := bbase (se 3 (by rfl) ⟨870017, by rfl⟩ : syracuseStep 4640093 = 1740035) (by norm_num)
theorem B3093395 : Blo 2061435 3093395 := bstep (se 1 (by rfl) ⟨2320046, by rfl⟩ : syracuseStep 3093395 = 4640093) B4640093
theorem B2062263 : Blo 2061435 2062263 := bstep (se 1 (by rfl) ⟨1546697, by rfl⟩ : syracuseStep 2062263 = 3093395) B3093395
theorem B3480077 : Blo 2061435 3480077 := bbase (se 3 (by rfl) ⟨652514, by rfl⟩ : syracuseStep 3480077 = 1305029) (by norm_num)
theorem B2320051 : Blo 2061435 2320051 := bstep (se 1 (by rfl) ⟨1740038, by rfl⟩ : syracuseStep 2320051 = 3480077) B3480077
theorem B3093401 : Blo 2061435 3093401 := bstep (se 2 (by rfl) ⟨1160025, by rfl⟩ : syracuseStep 3093401 = 2320051) B2320051
theorem B2062267 : Blo 2061435 2062267 := bstep (se 1 (by rfl) ⟨1546700, by rfl⟩ : syracuseStep 2062267 = 3093401) B3093401
theorem B2477521 : Blo 2061435 2477521 := bbase (se 2 (by rfl) ⟨929070, by rfl⟩ : syracuseStep 2477521 = 1858141) (by norm_num)
theorem B3303361 : Blo 2061435 3303361 := bstep (se 2 (by rfl) ⟨1238760, by rfl⟩ : syracuseStep 3303361 = 2477521) B2477521
theorem B17617925 : Blo 2061435 17617925 := bstep (se 4 (by rfl) ⟨1651680, by rfl⟩ : syracuseStep 17617925 = 3303361) B3303361
theorem B11745283 : Blo 2061435 11745283 := bstep (se 1 (by rfl) ⟨8808962, by rfl⟩ : syracuseStep 11745283 = 17617925) B17617925
theorem B15660377 : Blo 2061435 15660377 := bstep (se 2 (by rfl) ⟨5872641, by rfl⟩ : syracuseStep 15660377 = 11745283) B11745283
theorem B10440251 : Blo 2061435 10440251 := bstep (se 1 (by rfl) ⟨7830188, by rfl⟩ : syracuseStep 10440251 = 15660377) B15660377
theorem B6960167 : Blo 2061435 6960167 := bstep (se 1 (by rfl) ⟨5220125, by rfl⟩ : syracuseStep 6960167 = 10440251) B10440251
theorem B4640111 : Blo 2061435 4640111 := bstep (se 1 (by rfl) ⟨3480083, by rfl⟩ : syracuseStep 4640111 = 6960167) B6960167
theorem B3093407 : Blo 2061435 3093407 := bstep (se 1 (by rfl) ⟨2320055, by rfl⟩ : syracuseStep 3093407 = 4640111) B4640111
theorem B2062271 : Blo 2061435 2062271 := bstep (se 1 (by rfl) ⟨1546703, by rfl⟩ : syracuseStep 2062271 = 3093407) B3093407
theorem B3093413 : Blo 2061435 3093413 := bbase (se 4 (by rfl) ⟨290007, by rfl⟩ : syracuseStep 3093413 = 580015) (by norm_num)
theorem B2062275 : Blo 2061435 2062275 := bstep (se 1 (by rfl) ⟨1546706, by rfl⟩ : syracuseStep 2062275 = 3093413) B3093413
theorem B2610073 : Blo 2061435 2610073 := bbase (se 2 (by rfl) ⟨978777, by rfl⟩ : syracuseStep 2610073 = 1957555) (by norm_num)
theorem B3480097 : Blo 2061435 3480097 := bstep (se 2 (by rfl) ⟨1305036, by rfl⟩ : syracuseStep 3480097 = 2610073) B2610073
theorem B4640129 : Blo 2061435 4640129 := bstep (se 2 (by rfl) ⟨1740048, by rfl⟩ : syracuseStep 4640129 = 3480097) B3480097
theorem B3093419 : Blo 2061435 3093419 := bstep (se 1 (by rfl) ⟨2320064, by rfl⟩ : syracuseStep 3093419 = 4640129) B4640129
theorem B2062279 : Blo 2061435 2062279 := bstep (se 1 (by rfl) ⟨1546709, by rfl⟩ : syracuseStep 2062279 = 3093419) B3093419
theorem B2320069 : Blo 2061435 2320069 := bbase (se 4 (by rfl) ⟨217506, by rfl⟩ : syracuseStep 2320069 = 435013) (by norm_num)
theorem B3093425 : Blo 2061435 3093425 := bstep (se 2 (by rfl) ⟨1160034, by rfl⟩ : syracuseStep 3093425 = 2320069) B2320069
theorem B2062283 : Blo 2061435 2062283 := bstep (se 1 (by rfl) ⟨1546712, by rfl⟩ : syracuseStep 2062283 = 3093425) B3093425
theorem B3915125 : Blo 2061435 3915125 := bbase (se 5 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 3915125 = 367043) (by norm_num)
theorem B2610083 : Blo 2061435 2610083 := bstep (se 1 (by rfl) ⟨1957562, by rfl⟩ : syracuseStep 2610083 = 3915125) B3915125
theorem B6960221 : Blo 2061435 6960221 := bstep (se 3 (by rfl) ⟨1305041, by rfl⟩ : syracuseStep 6960221 = 2610083) B2610083
theorem B4640147 : Blo 2061435 4640147 := bstep (se 1 (by rfl) ⟨3480110, by rfl⟩ : syracuseStep 4640147 = 6960221) B6960221
theorem B3093431 : Blo 2061435 3093431 := bstep (se 1 (by rfl) ⟨2320073, by rfl⟩ : syracuseStep 3093431 = 4640147) B4640147
theorem B2062287 : Blo 2061435 2062287 := bstep (se 1 (by rfl) ⟨1546715, by rfl⟩ : syracuseStep 2062287 = 3093431) B3093431
theorem B3093437 : Blo 2061435 3093437 := bbase (se 3 (by rfl) ⟨580019, by rfl⟩ : syracuseStep 3093437 = 1160039) (by norm_num)
theorem B2062291 : Blo 2061435 2062291 := bstep (se 1 (by rfl) ⟨1546718, by rfl⟩ : syracuseStep 2062291 = 3093437) B3093437
theorem B4640165 : Blo 2061435 4640165 := bbase (se 4 (by rfl) ⟨435015, by rfl⟩ : syracuseStep 4640165 = 870031) (by norm_num)
theorem B3093443 : Blo 2061435 3093443 := bstep (se 1 (by rfl) ⟨2320082, by rfl⟩ : syracuseStep 3093443 = 4640165) B4640165
theorem B2062295 : Blo 2061435 2062295 := bstep (se 1 (by rfl) ⟨1546721, by rfl⟩ : syracuseStep 2062295 = 3093443) B3093443
theorem B5220197 : Blo 2061435 5220197 := bbase (se 4 (by rfl) ⟨489393, by rfl⟩ : syracuseStep 5220197 = 978787) (by norm_num)
theorem B3480131 : Blo 2061435 3480131 := bstep (se 1 (by rfl) ⟨2610098, by rfl⟩ : syracuseStep 3480131 = 5220197) B5220197
theorem B2320087 : Blo 2061435 2320087 := bstep (se 1 (by rfl) ⟨1740065, by rfl⟩ : syracuseStep 2320087 = 3480131) B3480131
theorem B3093449 : Blo 2061435 3093449 := bstep (se 2 (by rfl) ⟨1160043, by rfl⟩ : syracuseStep 3093449 = 2320087) B2320087
theorem B2062299 : Blo 2061435 2062299 := bstep (se 1 (by rfl) ⟨1546724, by rfl⟩ : syracuseStep 2062299 = 3093449) B3093449
theorem B3303413 : Blo 2061435 3303413 := bbase (se 5 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 3303413 = 309695) (by norm_num)
theorem B2202275 : Blo 2061435 2202275 := bstep (se 1 (by rfl) ⟨1651706, by rfl⟩ : syracuseStep 2202275 = 3303413) B3303413
theorem B5872733 : Blo 2061435 5872733 := bstep (se 3 (by rfl) ⟨1101137, by rfl⟩ : syracuseStep 5872733 = 2202275) B2202275
theorem B3915155 : Blo 2061435 3915155 := bstep (se 1 (by rfl) ⟨2936366, by rfl⟩ : syracuseStep 3915155 = 5872733) B5872733
theorem B10440413 : Blo 2061435 10440413 := bstep (se 3 (by rfl) ⟨1957577, by rfl⟩ : syracuseStep 10440413 = 3915155) B3915155
theorem B6960275 : Blo 2061435 6960275 := bstep (se 1 (by rfl) ⟨5220206, by rfl⟩ : syracuseStep 6960275 = 10440413) B10440413
theorem B4640183 : Blo 2061435 4640183 := bstep (se 1 (by rfl) ⟨3480137, by rfl⟩ : syracuseStep 4640183 = 6960275) B6960275
theorem B3093455 : Blo 2061435 3093455 := bstep (se 1 (by rfl) ⟨2320091, by rfl⟩ : syracuseStep 3093455 = 4640183) B4640183
theorem B2062303 : Blo 2061435 2062303 := bstep (se 1 (by rfl) ⟨1546727, by rfl⟩ : syracuseStep 2062303 = 3093455) B3093455
theorem B3093461 : Blo 2061435 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B2062307 : Blo 2061435 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B7830341 : Blo 2061435 7830341 := bbase (se 4 (by rfl) ⟨734094, by rfl⟩ : syracuseStep 7830341 = 1468189) (by norm_num)
theorem B5220227 : Blo 2061435 5220227 := bstep (se 1 (by rfl) ⟨3915170, by rfl⟩ : syracuseStep 5220227 = 7830341) B7830341
theorem B3480151 : Blo 2061435 3480151 := bstep (se 1 (by rfl) ⟨2610113, by rfl⟩ : syracuseStep 3480151 = 5220227) B5220227
theorem B4640201 : Blo 2061435 4640201 := bstep (se 2 (by rfl) ⟨1740075, by rfl⟩ : syracuseStep 4640201 = 3480151) B3480151
theorem B3093467 : Blo 2061435 3093467 := bstep (se 1 (by rfl) ⟨2320100, by rfl⟩ : syracuseStep 3093467 = 4640201) B4640201
theorem B2062311 : Blo 2061435 2062311 := bstep (se 1 (by rfl) ⟨1546733, by rfl⟩ : syracuseStep 2062311 = 3093467) B3093467
theorem B2320105 : Blo 2061435 2320105 := bbase (se 2 (by rfl) ⟨870039, by rfl⟩ : syracuseStep 2320105 = 1740079) (by norm_num)
theorem B3093473 : Blo 2061435 3093473 := bstep (se 2 (by rfl) ⟨1160052, by rfl⟩ : syracuseStep 3093473 = 2320105) B2320105
theorem B2062315 : Blo 2061435 2062315 := bstep (se 1 (by rfl) ⟨1546736, by rfl⟩ : syracuseStep 2062315 = 3093473) B3093473
theorem B11745557 : Blo 2061435 11745557 := bbase (se 6 (by rfl) ⟨275286, by rfl⟩ : syracuseStep 11745557 = 550573) (by norm_num)
theorem B7830371 : Blo 2061435 7830371 := bstep (se 1 (by rfl) ⟨5872778, by rfl⟩ : syracuseStep 7830371 = 11745557) B11745557
theorem B5220247 : Blo 2061435 5220247 := bstep (se 1 (by rfl) ⟨3915185, by rfl⟩ : syracuseStep 5220247 = 7830371) B7830371
theorem B6960329 : Blo 2061435 6960329 := bstep (se 2 (by rfl) ⟨2610123, by rfl⟩ : syracuseStep 6960329 = 5220247) B5220247
theorem B4640219 : Blo 2061435 4640219 := bstep (se 1 (by rfl) ⟨3480164, by rfl⟩ : syracuseStep 4640219 = 6960329) B6960329
theorem B3093479 : Blo 2061435 3093479 := bstep (se 1 (by rfl) ⟨2320109, by rfl⟩ : syracuseStep 3093479 = 4640219) B4640219
theorem B2062319 : Blo 2061435 2062319 := bstep (se 1 (by rfl) ⟨1546739, by rfl⟩ : syracuseStep 2062319 = 3093479) B3093479
theorem B3093485 : Blo 2061435 3093485 := bbase (se 3 (by rfl) ⟨580028, by rfl⟩ : syracuseStep 3093485 = 1160057) (by norm_num)
theorem B2062323 : Blo 2061435 2062323 := bstep (se 1 (by rfl) ⟨1546742, by rfl⟩ : syracuseStep 2062323 = 3093485) B3093485
theorem B4640237 : Blo 2061435 4640237 := bbase (se 3 (by rfl) ⟨870044, by rfl⟩ : syracuseStep 4640237 = 1740089) (by norm_num)
theorem B3093491 : Blo 2061435 3093491 := bstep (se 1 (by rfl) ⟨2320118, by rfl⟩ : syracuseStep 3093491 = 4640237) B4640237
theorem B2062327 : Blo 2061435 2062327 := bstep (se 1 (by rfl) ⟨1546745, by rfl⟩ : syracuseStep 2062327 = 3093491) B3093491
theorem B6606917 : Blo 2061435 6606917 := bbase (se 4 (by rfl) ⟨619398, by rfl⟩ : syracuseStep 6606917 = 1238797) (by norm_num)
theorem B4404611 : Blo 2061435 4404611 := bstep (se 1 (by rfl) ⟨3303458, by rfl⟩ : syracuseStep 4404611 = 6606917) B6606917
theorem B2936407 : Blo 2061435 2936407 := bstep (se 1 (by rfl) ⟨2202305, by rfl⟩ : syracuseStep 2936407 = 4404611) B4404611
theorem B3915209 : Blo 2061435 3915209 := bstep (se 2 (by rfl) ⟨1468203, by rfl⟩ : syracuseStep 3915209 = 2936407) B2936407
theorem B2610139 : Blo 2061435 2610139 := bstep (se 1 (by rfl) ⟨1957604, by rfl⟩ : syracuseStep 2610139 = 3915209) B3915209
theorem B3480185 : Blo 2061435 3480185 := bstep (se 2 (by rfl) ⟨1305069, by rfl⟩ : syracuseStep 3480185 = 2610139) B2610139
theorem B2320123 : Blo 2061435 2320123 := bstep (se 1 (by rfl) ⟨1740092, by rfl⟩ : syracuseStep 2320123 = 3480185) B3480185
theorem B3093497 : Blo 2061435 3093497 := bstep (se 2 (by rfl) ⟨1160061, by rfl⟩ : syracuseStep 3093497 = 2320123) B2320123
theorem B2062331 : Blo 2061435 2062331 := bstep (se 1 (by rfl) ⟨1546748, by rfl⟩ : syracuseStep 2062331 = 3093497) B3093497
theorem B2090473 : Blo 2061435 2090473 := bbase (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) (by norm_num)
theorem B44596757 : Blo 2061435 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B118924685 : Blo 2061435 118924685 := bstep (se 3 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 118924685 = 44596757) B44596757
theorem B79283123 : Blo 2061435 79283123 := bstep (se 1 (by rfl) ⟨59462342, by rfl⟩ : syracuseStep 79283123 = 118924685) B118924685
theorem B52855415 : Blo 2061435 52855415 := bstep (se 1 (by rfl) ⟨39641561, by rfl⟩ : syracuseStep 52855415 = 79283123) B79283123
theorem B35236943 : Blo 2061435 35236943 := bstep (se 1 (by rfl) ⟨26427707, by rfl⟩ : syracuseStep 35236943 = 52855415) B52855415
theorem B23491295 : Blo 2061435 23491295 := bstep (se 1 (by rfl) ⟨17618471, by rfl⟩ : syracuseStep 23491295 = 35236943) B35236943
theorem B15660863 : Blo 2061435 15660863 := bstep (se 1 (by rfl) ⟨11745647, by rfl⟩ : syracuseStep 15660863 = 23491295) B23491295
theorem B10440575 : Blo 2061435 10440575 := bstep (se 1 (by rfl) ⟨7830431, by rfl⟩ : syracuseStep 10440575 = 15660863) B15660863
theorem B6960383 : Blo 2061435 6960383 := bstep (se 1 (by rfl) ⟨5220287, by rfl⟩ : syracuseStep 6960383 = 10440575) B10440575
theorem B4640255 : Blo 2061435 4640255 := bstep (se 1 (by rfl) ⟨3480191, by rfl⟩ : syracuseStep 4640255 = 6960383) B6960383
theorem B3093503 : Blo 2061435 3093503 := bstep (se 1 (by rfl) ⟨2320127, by rfl⟩ : syracuseStep 3093503 = 4640255) B4640255
theorem B2062335 : Blo 2061435 2062335 := bstep (se 1 (by rfl) ⟨1546751, by rfl⟩ : syracuseStep 2062335 = 3093503) B3093503
theorem B3093509 : Blo 2061435 3093509 := bbase (se 4 (by rfl) ⟨290016, by rfl⟩ : syracuseStep 3093509 = 580033) (by norm_num)
theorem B2062339 : Blo 2061435 2062339 := bstep (se 1 (by rfl) ⟨1546754, by rfl⟩ : syracuseStep 2062339 = 3093509) B3093509
theorem B3480205 : Blo 2061435 3480205 := bbase (se 3 (by rfl) ⟨652538, by rfl⟩ : syracuseStep 3480205 = 1305077) (by norm_num)
theorem B4640273 : Blo 2061435 4640273 := bstep (se 2 (by rfl) ⟨1740102, by rfl⟩ : syracuseStep 4640273 = 3480205) B3480205
theorem B3093515 : Blo 2061435 3093515 := bstep (se 1 (by rfl) ⟨2320136, by rfl⟩ : syracuseStep 3093515 = 4640273) B4640273
theorem B2062343 : Blo 2061435 2062343 := bstep (se 1 (by rfl) ⟨1546757, by rfl⟩ : syracuseStep 2062343 = 3093515) B3093515
theorem B2320141 : Blo 2061435 2320141 := bbase (se 3 (by rfl) ⟨435026, by rfl⟩ : syracuseStep 2320141 = 870053) (by norm_num)
theorem B3093521 : Blo 2061435 3093521 := bstep (se 2 (by rfl) ⟨1160070, by rfl⟩ : syracuseStep 3093521 = 2320141) B2320141
theorem B2062347 : Blo 2061435 2062347 := bstep (se 1 (by rfl) ⟨1546760, by rfl⟩ : syracuseStep 2062347 = 3093521) B3093521
theorem B6960437 : Blo 2061435 6960437 := bbase (se 5 (by rfl) ⟨326270, by rfl⟩ : syracuseStep 6960437 = 652541) (by norm_num)
theorem B4640291 : Blo 2061435 4640291 := bstep (se 1 (by rfl) ⟨3480218, by rfl⟩ : syracuseStep 4640291 = 6960437) B6960437
theorem B3093527 : Blo 2061435 3093527 := bstep (se 1 (by rfl) ⟨2320145, by rfl⟩ : syracuseStep 3093527 = 4640291) B4640291
theorem B2062351 : Blo 2061435 2062351 := bstep (se 1 (by rfl) ⟨1546763, by rfl⟩ : syracuseStep 2062351 = 3093527) B3093527
theorem B3093533 : Blo 2061435 3093533 := bbase (se 3 (by rfl) ⟨580037, by rfl⟩ : syracuseStep 3093533 = 1160075) (by norm_num)
theorem B2062355 : Blo 2061435 2062355 := bstep (se 1 (by rfl) ⟨1546766, by rfl⟩ : syracuseStep 2062355 = 3093533) B3093533
theorem B4640309 : Blo 2061435 4640309 := bbase (se 5 (by rfl) ⟨217514, by rfl⟩ : syracuseStep 4640309 = 435029) (by norm_num)
theorem B3093539 : Blo 2061435 3093539 := bstep (se 1 (by rfl) ⟨2320154, by rfl⟩ : syracuseStep 3093539 = 4640309) B4640309
theorem B2062359 : Blo 2061435 2062359 := bstep (se 1 (by rfl) ⟨1546769, by rfl⟩ : syracuseStep 2062359 = 3093539) B3093539
theorem B3303509 : Blo 2061435 3303509 := bbase (se 8 (by rfl) ⟨19356, by rfl⟩ : syracuseStep 3303509 = 38713) (by norm_num)
theorem B8809357 : Blo 2061435 8809357 := bstep (se 3 (by rfl) ⟨1651754, by rfl⟩ : syracuseStep 8809357 = 3303509) B3303509
theorem B11745809 : Blo 2061435 11745809 := bstep (se 2 (by rfl) ⟨4404678, by rfl⟩ : syracuseStep 11745809 = 8809357) B8809357
theorem B7830539 : Blo 2061435 7830539 := bstep (se 1 (by rfl) ⟨5872904, by rfl⟩ : syracuseStep 7830539 = 11745809) B11745809
theorem B5220359 : Blo 2061435 5220359 := bstep (se 1 (by rfl) ⟨3915269, by rfl⟩ : syracuseStep 5220359 = 7830539) B7830539
theorem B3480239 : Blo 2061435 3480239 := bstep (se 1 (by rfl) ⟨2610179, by rfl⟩ : syracuseStep 3480239 = 5220359) B5220359
theorem B2320159 : Blo 2061435 2320159 := bstep (se 1 (by rfl) ⟨1740119, by rfl⟩ : syracuseStep 2320159 = 3480239) B3480239
theorem B3093545 : Blo 2061435 3093545 := bstep (se 2 (by rfl) ⟨1160079, by rfl⟩ : syracuseStep 3093545 = 2320159) B2320159
theorem B2062363 : Blo 2061435 2062363 := bstep (se 1 (by rfl) ⟨1546772, by rfl⟩ : syracuseStep 2062363 = 3093545) B3093545
theorem B2416433 : Blo 2061435 2416433 := bbase (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) (by norm_num)
theorem B6443821 : Blo 2061435 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B8591761 : Blo 2061435 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B11455681 : Blo 2061435 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B15274241 : Blo 2061435 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B10182827 : Blo 2061435 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B6788551 : Blo 2061435 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B9051401 : Blo 2061435 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B6034267 : Blo 2061435 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B8045689 : Blo 2061435 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B10727585 : Blo 2061435 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B7151723 : Blo 2061435 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B4767815 : Blo 2061435 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B3178543 : Blo 2061435 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B4238057 : Blo 2061435 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B2825371 : Blo 2061435 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B15068645 : Blo 2061435 15068645 := bstep (se 4 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 15068645 = 2825371) B2825371
theorem B10045763 : Blo 2061435 10045763 := bstep (se 1 (by rfl) ⟨7534322, by rfl⟩ : syracuseStep 10045763 = 15068645) B15068645
theorem B6697175 : Blo 2061435 6697175 := bstep (se 1 (by rfl) ⟨5022881, by rfl⟩ : syracuseStep 6697175 = 10045763) B10045763
theorem B17859133 : Blo 2061435 17859133 := bstep (se 3 (by rfl) ⟨3348587, by rfl⟩ : syracuseStep 17859133 = 6697175) B6697175
theorem B23812177 : Blo 2061435 23812177 := bstep (se 2 (by rfl) ⟨8929566, by rfl⟩ : syracuseStep 23812177 = 17859133) B17859133
theorem B31749569 : Blo 2061435 31749569 := bstep (se 2 (by rfl) ⟨11906088, by rfl⟩ : syracuseStep 31749569 = 23812177) B23812177
theorem B21166379 : Blo 2061435 21166379 := bstep (se 1 (by rfl) ⟨15874784, by rfl⟩ : syracuseStep 21166379 = 31749569) B31749569
theorem B14110919 : Blo 2061435 14110919 := bstep (se 1 (by rfl) ⟨10583189, by rfl⟩ : syracuseStep 14110919 = 21166379) B21166379
theorem B9407279 : Blo 2061435 9407279 := bstep (se 1 (by rfl) ⟨7055459, by rfl⟩ : syracuseStep 9407279 = 14110919) B14110919
theorem B6271519 : Blo 2061435 6271519 := bstep (se 1 (by rfl) ⟨4703639, by rfl⟩ : syracuseStep 6271519 = 9407279) B9407279
theorem B8362025 : Blo 2061435 8362025 := bstep (se 2 (by rfl) ⟨3135759, by rfl⟩ : syracuseStep 8362025 = 6271519) B6271519
theorem B5574683 : Blo 2061435 5574683 := bstep (se 1 (by rfl) ⟨4181012, by rfl⟩ : syracuseStep 5574683 = 8362025) B8362025
theorem B3716455 : Blo 2061435 3716455 := bstep (se 1 (by rfl) ⟨2787341, by rfl⟩ : syracuseStep 3716455 = 5574683) B5574683
theorem B4955273 : Blo 2061435 4955273 := bstep (se 2 (by rfl) ⟨1858227, by rfl⟩ : syracuseStep 4955273 = 3716455) B3716455
theorem B3303515 : Blo 2061435 3303515 := bstep (se 1 (by rfl) ⟨2477636, by rfl⟩ : syracuseStep 3303515 = 4955273) B4955273
theorem B8809373 : Blo 2061435 8809373 := bstep (se 3 (by rfl) ⟨1651757, by rfl⟩ : syracuseStep 8809373 = 3303515) B3303515
theorem B5872915 : Blo 2061435 5872915 := bstep (se 1 (by rfl) ⟨4404686, by rfl⟩ : syracuseStep 5872915 = 8809373) B8809373
theorem B7830553 : Blo 2061435 7830553 := bstep (se 2 (by rfl) ⟨2936457, by rfl⟩ : syracuseStep 7830553 = 5872915) B5872915
theorem B10440737 : Blo 2061435 10440737 := bstep (se 2 (by rfl) ⟨3915276, by rfl⟩ : syracuseStep 10440737 = 7830553) B7830553
theorem B6960491 : Blo 2061435 6960491 := bstep (se 1 (by rfl) ⟨5220368, by rfl⟩ : syracuseStep 6960491 = 10440737) B10440737
theorem B4640327 : Blo 2061435 4640327 := bstep (se 1 (by rfl) ⟨3480245, by rfl⟩ : syracuseStep 4640327 = 6960491) B6960491
theorem B3093551 : Blo 2061435 3093551 := bstep (se 1 (by rfl) ⟨2320163, by rfl⟩ : syracuseStep 3093551 = 4640327) B4640327
theorem B2062367 : Blo 2061435 2062367 := bstep (se 1 (by rfl) ⟨1546775, by rfl⟩ : syracuseStep 2062367 = 3093551) B3093551
theorem B3093557 : Blo 2061435 3093557 := bbase (se 5 (by rfl) ⟨145010, by rfl⟩ : syracuseStep 3093557 = 290021) (by norm_num)
theorem B2062371 : Blo 2061435 2062371 := bstep (se 1 (by rfl) ⟨1546778, by rfl⟩ : syracuseStep 2062371 = 3093557) B3093557
theorem B5220389 : Blo 2061435 5220389 := bbase (se 4 (by rfl) ⟨489411, by rfl⟩ : syracuseStep 5220389 = 978823) (by norm_num)
theorem B3480259 : Blo 2061435 3480259 := bstep (se 1 (by rfl) ⟨2610194, by rfl⟩ : syracuseStep 3480259 = 5220389) B5220389
theorem B4640345 : Blo 2061435 4640345 := bstep (se 2 (by rfl) ⟨1740129, by rfl⟩ : syracuseStep 4640345 = 3480259) B3480259
theorem B3093563 : Blo 2061435 3093563 := bstep (se 1 (by rfl) ⟨2320172, by rfl⟩ : syracuseStep 3093563 = 4640345) B4640345
theorem B2062375 : Blo 2061435 2062375 := bstep (se 1 (by rfl) ⟨1546781, by rfl⟩ : syracuseStep 2062375 = 3093563) B3093563
theorem B2320177 : Blo 2061435 2320177 := bbase (se 2 (by rfl) ⟨870066, by rfl⟩ : syracuseStep 2320177 = 1740133) (by norm_num)
theorem B3093569 : Blo 2061435 3093569 := bstep (se 2 (by rfl) ⟨1160088, by rfl⟩ : syracuseStep 3093569 = 2320177) B2320177
theorem B2062379 : Blo 2061435 2062379 := bstep (se 1 (by rfl) ⟨1546784, by rfl⟩ : syracuseStep 2062379 = 3093569) B3093569
theorem B3303541 : Blo 2061435 3303541 := bbase (se 5 (by rfl) ⟨154853, by rfl⟩ : syracuseStep 3303541 = 309707) (by norm_num)
theorem B4404721 : Blo 2061435 4404721 := bstep (se 2 (by rfl) ⟨1651770, by rfl⟩ : syracuseStep 4404721 = 3303541) B3303541
theorem B5872961 : Blo 2061435 5872961 := bstep (se 2 (by rfl) ⟨2202360, by rfl⟩ : syracuseStep 5872961 = 4404721) B4404721
theorem B3915307 : Blo 2061435 3915307 := bstep (se 1 (by rfl) ⟨2936480, by rfl⟩ : syracuseStep 3915307 = 5872961) B5872961
theorem B5220409 : Blo 2061435 5220409 := bstep (se 2 (by rfl) ⟨1957653, by rfl⟩ : syracuseStep 5220409 = 3915307) B3915307
theorem B6960545 : Blo 2061435 6960545 := bstep (se 2 (by rfl) ⟨2610204, by rfl⟩ : syracuseStep 6960545 = 5220409) B5220409
theorem B4640363 : Blo 2061435 4640363 := bstep (se 1 (by rfl) ⟨3480272, by rfl⟩ : syracuseStep 4640363 = 6960545) B6960545
theorem B3093575 : Blo 2061435 3093575 := bstep (se 1 (by rfl) ⟨2320181, by rfl⟩ : syracuseStep 3093575 = 4640363) B4640363
theorem B2062383 : Blo 2061435 2062383 := bstep (se 1 (by rfl) ⟨1546787, by rfl⟩ : syracuseStep 2062383 = 3093575) B3093575
theorem B3093581 : Blo 2061435 3093581 := bbase (se 3 (by rfl) ⟨580046, by rfl⟩ : syracuseStep 3093581 = 1160093) (by norm_num)
theorem B2062387 : Blo 2061435 2062387 := bstep (se 1 (by rfl) ⟨1546790, by rfl⟩ : syracuseStep 2062387 = 3093581) B3093581
theorem B4640381 : Blo 2061435 4640381 := bbase (se 3 (by rfl) ⟨870071, by rfl⟩ : syracuseStep 4640381 = 1740143) (by norm_num)
theorem B3093587 : Blo 2061435 3093587 := bstep (se 1 (by rfl) ⟨2320190, by rfl⟩ : syracuseStep 3093587 = 4640381) B4640381
theorem B2062391 : Blo 2061435 2062391 := bstep (se 1 (by rfl) ⟨1546793, by rfl⟩ : syracuseStep 2062391 = 3093587) B3093587
theorem B3480293 : Blo 2061435 3480293 := bbase (se 4 (by rfl) ⟨326277, by rfl⟩ : syracuseStep 3480293 = 652555) (by norm_num)
theorem B2320195 : Blo 2061435 2320195 := bstep (se 1 (by rfl) ⟨1740146, by rfl⟩ : syracuseStep 2320195 = 3480293) B3480293
theorem B3093593 : Blo 2061435 3093593 := bstep (se 2 (by rfl) ⟨1160097, by rfl⟩ : syracuseStep 3093593 = 2320195) B2320195
theorem B2062395 : Blo 2061435 2062395 := bstep (se 1 (by rfl) ⟨1546796, by rfl⟩ : syracuseStep 2062395 = 3093593) B3093593
theorem B2351857 : Blo 2061435 2351857 := bbase (se 2 (by rfl) ⟨881946, by rfl⟩ : syracuseStep 2351857 = 1763893) (by norm_num)
theorem B3135809 : Blo 2061435 3135809 := bstep (se 2 (by rfl) ⟨1175928, by rfl⟩ : syracuseStep 3135809 = 2351857) B2351857
theorem B2090539 : Blo 2061435 2090539 := bstep (se 1 (by rfl) ⟨1567904, by rfl⟩ : syracuseStep 2090539 = 3135809) B3135809
theorem B2787385 : Blo 2061435 2787385 := bstep (se 2 (by rfl) ⟨1045269, by rfl⟩ : syracuseStep 2787385 = 2090539) B2090539
theorem B3716513 : Blo 2061435 3716513 := bstep (se 2 (by rfl) ⟨1393692, by rfl⟩ : syracuseStep 3716513 = 2787385) B2787385
theorem B2477675 : Blo 2061435 2477675 := bstep (se 1 (by rfl) ⟨1858256, by rfl⟩ : syracuseStep 2477675 = 3716513) B3716513
theorem B6607133 : Blo 2061435 6607133 := bstep (se 3 (by rfl) ⟨1238837, by rfl⟩ : syracuseStep 6607133 = 2477675) B2477675
theorem B4404755 : Blo 2061435 4404755 := bstep (se 1 (by rfl) ⟨3303566, by rfl⟩ : syracuseStep 4404755 = 6607133) B6607133
theorem B2936503 : Blo 2061435 2936503 := bstep (se 1 (by rfl) ⟨2202377, by rfl⟩ : syracuseStep 2936503 = 4404755) B4404755
theorem B15661349 : Blo 2061435 15661349 := bstep (se 4 (by rfl) ⟨1468251, by rfl⟩ : syracuseStep 15661349 = 2936503) B2936503
theorem B10440899 : Blo 2061435 10440899 := bstep (se 1 (by rfl) ⟨7830674, by rfl⟩ : syracuseStep 10440899 = 15661349) B15661349
theorem B6960599 : Blo 2061435 6960599 := bstep (se 1 (by rfl) ⟨5220449, by rfl⟩ : syracuseStep 6960599 = 10440899) B10440899
theorem B4640399 : Blo 2061435 4640399 := bstep (se 1 (by rfl) ⟨3480299, by rfl⟩ : syracuseStep 4640399 = 6960599) B6960599
theorem B3093599 : Blo 2061435 3093599 := bstep (se 1 (by rfl) ⟨2320199, by rfl⟩ : syracuseStep 3093599 = 4640399) B4640399
theorem B2062399 : Blo 2061435 2062399 := bstep (se 1 (by rfl) ⟨1546799, by rfl⟩ : syracuseStep 2062399 = 3093599) B3093599
theorem B3093605 : Blo 2061435 3093605 := bbase (se 4 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 3093605 = 580051) (by norm_num)
theorem B2062403 : Blo 2061435 2062403 := bstep (se 1 (by rfl) ⟨1546802, by rfl⟩ : syracuseStep 2062403 = 3093605) B3093605
theorem B4404773 : Blo 2061435 4404773 := bbase (se 4 (by rfl) ⟨412947, by rfl⟩ : syracuseStep 4404773 = 825895) (by norm_num)
theorem B2936515 : Blo 2061435 2936515 := bstep (se 1 (by rfl) ⟨2202386, by rfl⟩ : syracuseStep 2936515 = 4404773) B4404773
theorem B3915353 : Blo 2061435 3915353 := bstep (se 2 (by rfl) ⟨1468257, by rfl⟩ : syracuseStep 3915353 = 2936515) B2936515
theorem B2610235 : Blo 2061435 2610235 := bstep (se 1 (by rfl) ⟨1957676, by rfl⟩ : syracuseStep 2610235 = 3915353) B3915353
theorem B3480313 : Blo 2061435 3480313 := bstep (se 2 (by rfl) ⟨1305117, by rfl⟩ : syracuseStep 3480313 = 2610235) B2610235
theorem B4640417 : Blo 2061435 4640417 := bstep (se 2 (by rfl) ⟨1740156, by rfl⟩ : syracuseStep 4640417 = 3480313) B3480313
theorem B3093611 : Blo 2061435 3093611 := bstep (se 1 (by rfl) ⟨2320208, by rfl⟩ : syracuseStep 3093611 = 4640417) B4640417
theorem B2062407 : Blo 2061435 2062407 := bstep (se 1 (by rfl) ⟨1546805, by rfl⟩ : syracuseStep 2062407 = 3093611) B3093611
theorem B2320213 : Blo 2061435 2320213 := bbase (se 9 (by rfl) ⟨6797, by rfl⟩ : syracuseStep 2320213 = 13595) (by norm_num)
theorem B3093617 : Blo 2061435 3093617 := bstep (se 2 (by rfl) ⟨1160106, by rfl⟩ : syracuseStep 3093617 = 2320213) B2320213
theorem B2062411 : Blo 2061435 2062411 := bstep (se 1 (by rfl) ⟨1546808, by rfl⟩ : syracuseStep 2062411 = 3093617) B3093617
theorem B2610245 : Blo 2061435 2610245 := bbase (se 4 (by rfl) ⟨244710, by rfl⟩ : syracuseStep 2610245 = 489421) (by norm_num)
theorem B6960653 : Blo 2061435 6960653 := bstep (se 3 (by rfl) ⟨1305122, by rfl⟩ : syracuseStep 6960653 = 2610245) B2610245
theorem B4640435 : Blo 2061435 4640435 := bstep (se 1 (by rfl) ⟨3480326, by rfl⟩ : syracuseStep 4640435 = 6960653) B6960653
theorem B3093623 : Blo 2061435 3093623 := bstep (se 1 (by rfl) ⟨2320217, by rfl⟩ : syracuseStep 3093623 = 4640435) B4640435
theorem B2062415 : Blo 2061435 2062415 := bstep (se 1 (by rfl) ⟨1546811, by rfl⟩ : syracuseStep 2062415 = 3093623) B3093623
theorem B3093629 : Blo 2061435 3093629 := bbase (se 3 (by rfl) ⟨580055, by rfl⟩ : syracuseStep 3093629 = 1160111) (by norm_num)
theorem B2062419 : Blo 2061435 2062419 := bstep (se 1 (by rfl) ⟨1546814, by rfl⟩ : syracuseStep 2062419 = 3093629) B3093629
theorem B4640453 : Blo 2061435 4640453 := bbase (se 4 (by rfl) ⟨435042, by rfl⟩ : syracuseStep 4640453 = 870085) (by norm_num)
theorem B3093635 : Blo 2061435 3093635 := bstep (se 1 (by rfl) ⟨2320226, by rfl⟩ : syracuseStep 3093635 = 4640453) B4640453
theorem B2062423 : Blo 2061435 2062423 := bstep (se 1 (by rfl) ⟨1546817, by rfl⟩ : syracuseStep 2062423 = 3093635) B3093635
theorem B33905429 : Blo 2061435 33905429 := bbase (se 6 (by rfl) ⟨794658, by rfl⟩ : syracuseStep 33905429 = 1589317) (by norm_num)
theorem B22603619 : Blo 2061435 22603619 := bstep (se 1 (by rfl) ⟨16952714, by rfl⟩ : syracuseStep 22603619 = 33905429) B33905429
theorem B15069079 : Blo 2061435 15069079 := bstep (se 1 (by rfl) ⟨11301809, by rfl⟩ : syracuseStep 15069079 = 22603619) B22603619
theorem B20092105 : Blo 2061435 20092105 := bstep (se 2 (by rfl) ⟨7534539, by rfl⟩ : syracuseStep 20092105 = 15069079) B15069079
theorem B26789473 : Blo 2061435 26789473 := bstep (se 2 (by rfl) ⟨10046052, by rfl⟩ : syracuseStep 26789473 = 20092105) B20092105
theorem B142877189 : Blo 2061435 142877189 := bstep (se 4 (by rfl) ⟨13394736, by rfl⟩ : syracuseStep 142877189 = 26789473) B26789473
theorem B95251459 : Blo 2061435 95251459 := bstep (se 1 (by rfl) ⟨71438594, by rfl⟩ : syracuseStep 95251459 = 142877189) B142877189
theorem B127001945 : Blo 2061435 127001945 := bstep (se 2 (by rfl) ⟨47625729, by rfl⟩ : syracuseStep 127001945 = 95251459) B95251459
theorem B84667963 : Blo 2061435 84667963 := bstep (se 1 (by rfl) ⟨63500972, by rfl⟩ : syracuseStep 84667963 = 127001945) B127001945
theorem B112890617 : Blo 2061435 112890617 := bstep (se 2 (by rfl) ⟨42333981, by rfl⟩ : syracuseStep 112890617 = 84667963) B84667963
theorem B75260411 : Blo 2061435 75260411 := bstep (se 1 (by rfl) ⟨56445308, by rfl⟩ : syracuseStep 75260411 = 112890617) B112890617
theorem B50173607 : Blo 2061435 50173607 := bstep (se 1 (by rfl) ⟨37630205, by rfl⟩ : syracuseStep 50173607 = 75260411) B75260411
theorem B33449071 : Blo 2061435 33449071 := bstep (se 1 (by rfl) ⟨25086803, by rfl⟩ : syracuseStep 33449071 = 50173607) B50173607
theorem B44598761 : Blo 2061435 44598761 := bstep (se 2 (by rfl) ⟨16724535, by rfl⟩ : syracuseStep 44598761 = 33449071) B33449071
theorem B29732507 : Blo 2061435 29732507 := bstep (se 1 (by rfl) ⟨22299380, by rfl⟩ : syracuseStep 29732507 = 44598761) B44598761
theorem B19821671 : Blo 2061435 19821671 := bstep (se 1 (by rfl) ⟨14866253, by rfl⟩ : syracuseStep 19821671 = 29732507) B29732507
theorem B13214447 : Blo 2061435 13214447 := bstep (se 1 (by rfl) ⟨9910835, by rfl⟩ : syracuseStep 13214447 = 19821671) B19821671
theorem B8809631 : Blo 2061435 8809631 := bstep (se 1 (by rfl) ⟨6607223, by rfl⟩ : syracuseStep 8809631 = 13214447) B13214447
theorem B5873087 : Blo 2061435 5873087 := bstep (se 1 (by rfl) ⟨4404815, by rfl⟩ : syracuseStep 5873087 = 8809631) B8809631
theorem B3915391 : Blo 2061435 3915391 := bstep (se 1 (by rfl) ⟨2936543, by rfl⟩ : syracuseStep 3915391 = 5873087) B5873087
theorem B5220521 : Blo 2061435 5220521 := bstep (se 2 (by rfl) ⟨1957695, by rfl⟩ : syracuseStep 5220521 = 3915391) B3915391
theorem B3480347 : Blo 2061435 3480347 := bstep (se 1 (by rfl) ⟨2610260, by rfl⟩ : syracuseStep 3480347 = 5220521) B5220521
theorem B2320231 : Blo 2061435 2320231 := bstep (se 1 (by rfl) ⟨1740173, by rfl⟩ : syracuseStep 2320231 = 3480347) B3480347
theorem B3093641 : Blo 2061435 3093641 := bstep (se 2 (by rfl) ⟨1160115, by rfl⟩ : syracuseStep 3093641 = 2320231) B2320231
theorem B2062427 : Blo 2061435 2062427 := bstep (se 1 (by rfl) ⟨1546820, by rfl⟩ : syracuseStep 2062427 = 3093641) B3093641
theorem B10441061 : Blo 2061435 10441061 := bbase (se 4 (by rfl) ⟨978849, by rfl⟩ : syracuseStep 10441061 = 1957699) (by norm_num)
theorem B6960707 : Blo 2061435 6960707 := bstep (se 1 (by rfl) ⟨5220530, by rfl⟩ : syracuseStep 6960707 = 10441061) B10441061
theorem B4640471 : Blo 2061435 4640471 := bstep (se 1 (by rfl) ⟨3480353, by rfl⟩ : syracuseStep 4640471 = 6960707) B6960707
theorem B3093647 : Blo 2061435 3093647 := bstep (se 1 (by rfl) ⟨2320235, by rfl⟩ : syracuseStep 3093647 = 4640471) B4640471
theorem B2062431 : Blo 2061435 2062431 := bstep (se 1 (by rfl) ⟨1546823, by rfl⟩ : syracuseStep 2062431 = 3093647) B3093647
theorem B3093653 : Blo 2061435 3093653 := bbase (se 6 (by rfl) ⟨72507, by rfl⟩ : syracuseStep 3093653 = 145015) (by norm_num)
theorem B2062435 : Blo 2061435 2062435 := bstep (se 1 (by rfl) ⟨1546826, by rfl⟩ : syracuseStep 2062435 = 3093653) B3093653
theorem B2511529 : Blo 2061435 2511529 := bbase (se 2 (by rfl) ⟨941823, by rfl⟩ : syracuseStep 2511529 = 1883647) (by norm_num)
theorem B13394821 : Blo 2061435 13394821 := bstep (se 4 (by rfl) ⟨1255764, by rfl⟩ : syracuseStep 13394821 = 2511529) B2511529
theorem B17859761 : Blo 2061435 17859761 := bstep (se 2 (by rfl) ⟨6697410, by rfl⟩ : syracuseStep 17859761 = 13394821) B13394821
theorem B11906507 : Blo 2061435 11906507 := bstep (se 1 (by rfl) ⟨8929880, by rfl⟩ : syracuseStep 11906507 = 17859761) B17859761
theorem B7937671 : Blo 2061435 7937671 := bstep (se 1 (by rfl) ⟨5953253, by rfl⟩ : syracuseStep 7937671 = 11906507) B11906507
theorem B10583561 : Blo 2061435 10583561 := bstep (se 2 (by rfl) ⟨3968835, by rfl⟩ : syracuseStep 10583561 = 7937671) B7937671
theorem B7055707 : Blo 2061435 7055707 := bstep (se 1 (by rfl) ⟨5291780, by rfl⟩ : syracuseStep 7055707 = 10583561) B10583561
theorem B9407609 : Blo 2061435 9407609 := bstep (se 2 (by rfl) ⟨3527853, by rfl⟩ : syracuseStep 9407609 = 7055707) B7055707
theorem B6271739 : Blo 2061435 6271739 := bstep (se 1 (by rfl) ⟨4703804, by rfl⟩ : syracuseStep 6271739 = 9407609) B9407609
theorem B4181159 : Blo 2061435 4181159 := bstep (se 1 (by rfl) ⟨3135869, by rfl⟩ : syracuseStep 4181159 = 6271739) B6271739
theorem B2787439 : Blo 2061435 2787439 := bstep (se 1 (by rfl) ⟨2090579, by rfl⟩ : syracuseStep 2787439 = 4181159) B4181159
theorem B3716585 : Blo 2061435 3716585 := bstep (se 2 (by rfl) ⟨1393719, by rfl⟩ : syracuseStep 3716585 = 2787439) B2787439
theorem B2477723 : Blo 2061435 2477723 := bstep (se 1 (by rfl) ⟨1858292, by rfl⟩ : syracuseStep 2477723 = 3716585) B3716585
theorem B6607261 : Blo 2061435 6607261 := bstep (se 3 (by rfl) ⟨1238861, by rfl⟩ : syracuseStep 6607261 = 2477723) B2477723
theorem B8809681 : Blo 2061435 8809681 := bstep (se 2 (by rfl) ⟨3303630, by rfl⟩ : syracuseStep 8809681 = 6607261) B6607261
theorem B11746241 : Blo 2061435 11746241 := bstep (se 2 (by rfl) ⟨4404840, by rfl⟩ : syracuseStep 11746241 = 8809681) B8809681
theorem B7830827 : Blo 2061435 7830827 := bstep (se 1 (by rfl) ⟨5873120, by rfl⟩ : syracuseStep 7830827 = 11746241) B11746241
theorem B5220551 : Blo 2061435 5220551 := bstep (se 1 (by rfl) ⟨3915413, by rfl⟩ : syracuseStep 5220551 = 7830827) B7830827
theorem B3480367 : Blo 2061435 3480367 := bstep (se 1 (by rfl) ⟨2610275, by rfl⟩ : syracuseStep 3480367 = 5220551) B5220551
theorem B4640489 : Blo 2061435 4640489 := bstep (se 2 (by rfl) ⟨1740183, by rfl⟩ : syracuseStep 4640489 = 3480367) B3480367
theorem B3093659 : Blo 2061435 3093659 := bstep (se 1 (by rfl) ⟨2320244, by rfl⟩ : syracuseStep 3093659 = 4640489) B4640489
theorem B2062439 : Blo 2061435 2062439 := bstep (se 1 (by rfl) ⟨1546829, by rfl⟩ : syracuseStep 2062439 = 3093659) B3093659
theorem B2320249 : Blo 2061435 2320249 := bbase (se 2 (by rfl) ⟨870093, by rfl⟩ : syracuseStep 2320249 = 1740187) (by norm_num)
theorem B3093665 : Blo 2061435 3093665 := bstep (se 2 (by rfl) ⟨1160124, by rfl⟩ : syracuseStep 3093665 = 2320249) B2320249
theorem B2062443 : Blo 2061435 2062443 := bstep (se 1 (by rfl) ⟨1546832, by rfl⟩ : syracuseStep 2062443 = 3093665) B3093665
theorem B4525877 : Blo 2061435 4525877 := bbase (se 5 (by rfl) ⟨212150, by rfl⟩ : syracuseStep 4525877 = 424301) (by norm_num)
theorem B12069005 : Blo 2061435 12069005 := bstep (se 3 (by rfl) ⟨2262938, by rfl⟩ : syracuseStep 12069005 = 4525877) B4525877
theorem B32184013 : Blo 2061435 32184013 := bstep (se 3 (by rfl) ⟨6034502, by rfl⟩ : syracuseStep 32184013 = 12069005) B12069005
theorem B42912017 : Blo 2061435 42912017 := bstep (se 2 (by rfl) ⟨16092006, by rfl⟩ : syracuseStep 42912017 = 32184013) B32184013
theorem B28608011 : Blo 2061435 28608011 := bstep (se 1 (by rfl) ⟨21456008, by rfl⟩ : syracuseStep 28608011 = 42912017) B42912017
theorem B19072007 : Blo 2061435 19072007 := bstep (se 1 (by rfl) ⟨14304005, by rfl⟩ : syracuseStep 19072007 = 28608011) B28608011
theorem B12714671 : Blo 2061435 12714671 := bstep (se 1 (by rfl) ⟨9536003, by rfl⟩ : syracuseStep 12714671 = 19072007) B19072007
theorem B8476447 : Blo 2061435 8476447 := bstep (se 1 (by rfl) ⟨6357335, by rfl⟩ : syracuseStep 8476447 = 12714671) B12714671
theorem B11301929 : Blo 2061435 11301929 := bstep (se 2 (by rfl) ⟨4238223, by rfl⟩ : syracuseStep 11301929 = 8476447) B8476447
theorem B7534619 : Blo 2061435 7534619 := bstep (se 1 (by rfl) ⟨5650964, by rfl⟩ : syracuseStep 7534619 = 11301929) B11301929
theorem B5023079 : Blo 2061435 5023079 := bstep (se 1 (by rfl) ⟨3767309, by rfl⟩ : syracuseStep 5023079 = 7534619) B7534619
theorem B3348719 : Blo 2061435 3348719 := bstep (se 1 (by rfl) ⟨2511539, by rfl⟩ : syracuseStep 3348719 = 5023079) B5023079
theorem B2232479 : Blo 2061435 2232479 := bstep (se 1 (by rfl) ⟨1674359, by rfl⟩ : syracuseStep 2232479 = 3348719) B3348719
theorem B5953277 : Blo 2061435 5953277 := bstep (se 3 (by rfl) ⟨1116239, by rfl⟩ : syracuseStep 5953277 = 2232479) B2232479
theorem B3968851 : Blo 2061435 3968851 := bstep (se 1 (by rfl) ⟨2976638, by rfl⟩ : syracuseStep 3968851 = 5953277) B5953277
theorem B5291801 : Blo 2061435 5291801 := bstep (se 2 (by rfl) ⟨1984425, by rfl⟩ : syracuseStep 5291801 = 3968851) B3968851
theorem B3527867 : Blo 2061435 3527867 := bstep (se 1 (by rfl) ⟨2645900, by rfl⟩ : syracuseStep 3527867 = 5291801) B5291801
theorem B2351911 : Blo 2061435 2351911 := bstep (se 1 (by rfl) ⟨1763933, by rfl⟩ : syracuseStep 2351911 = 3527867) B3527867
theorem B3135881 : Blo 2061435 3135881 := bstep (se 2 (by rfl) ⟨1175955, by rfl⟩ : syracuseStep 3135881 = 2351911) B2351911
theorem B8362349 : Blo 2061435 8362349 := bstep (se 3 (by rfl) ⟨1567940, by rfl⟩ : syracuseStep 8362349 = 3135881) B3135881
theorem B5574899 : Blo 2061435 5574899 := bstep (se 1 (by rfl) ⟨4181174, by rfl⟩ : syracuseStep 5574899 = 8362349) B8362349
theorem B3716599 : Blo 2061435 3716599 := bstep (se 1 (by rfl) ⟨2787449, by rfl⟩ : syracuseStep 3716599 = 5574899) B5574899
theorem B4955465 : Blo 2061435 4955465 := bstep (se 2 (by rfl) ⟨1858299, by rfl⟩ : syracuseStep 4955465 = 3716599) B3716599
theorem B13214573 : Blo 2061435 13214573 := bstep (se 3 (by rfl) ⟨2477732, by rfl⟩ : syracuseStep 13214573 = 4955465) B4955465
theorem B8809715 : Blo 2061435 8809715 := bstep (se 1 (by rfl) ⟨6607286, by rfl⟩ : syracuseStep 8809715 = 13214573) B13214573
theorem B5873143 : Blo 2061435 5873143 := bstep (se 1 (by rfl) ⟨4404857, by rfl⟩ : syracuseStep 5873143 = 8809715) B8809715
theorem B7830857 : Blo 2061435 7830857 := bstep (se 2 (by rfl) ⟨2936571, by rfl⟩ : syracuseStep 7830857 = 5873143) B5873143
theorem B5220571 : Blo 2061435 5220571 := bstep (se 1 (by rfl) ⟨3915428, by rfl⟩ : syracuseStep 5220571 = 7830857) B7830857
theorem B6960761 : Blo 2061435 6960761 := bstep (se 2 (by rfl) ⟨2610285, by rfl⟩ : syracuseStep 6960761 = 5220571) B5220571
theorem B4640507 : Blo 2061435 4640507 := bstep (se 1 (by rfl) ⟨3480380, by rfl⟩ : syracuseStep 4640507 = 6960761) B6960761
theorem B3093671 : Blo 2061435 3093671 := bstep (se 1 (by rfl) ⟨2320253, by rfl⟩ : syracuseStep 3093671 = 4640507) B4640507
theorem B2062447 : Blo 2061435 2062447 := bstep (se 1 (by rfl) ⟨1546835, by rfl⟩ : syracuseStep 2062447 = 3093671) B3093671
theorem B3093677 : Blo 2061435 3093677 := bbase (se 3 (by rfl) ⟨580064, by rfl⟩ : syracuseStep 3093677 = 1160129) (by norm_num)
theorem B2062451 : Blo 2061435 2062451 := bstep (se 1 (by rfl) ⟨1546838, by rfl⟩ : syracuseStep 2062451 = 3093677) B3093677
theorem B4640525 : Blo 2061435 4640525 := bbase (se 3 (by rfl) ⟨870098, by rfl⟩ : syracuseStep 4640525 = 1740197) (by norm_num)
theorem B3093683 : Blo 2061435 3093683 := bstep (se 1 (by rfl) ⟨2320262, by rfl⟩ : syracuseStep 3093683 = 4640525) B4640525
theorem B2062455 : Blo 2061435 2062455 := bstep (se 1 (by rfl) ⟨1546841, by rfl⟩ : syracuseStep 2062455 = 3093683) B3093683
theorem B2610301 : Blo 2061435 2610301 := bbase (se 3 (by rfl) ⟨489431, by rfl⟩ : syracuseStep 2610301 = 978863) (by norm_num)
theorem B3480401 : Blo 2061435 3480401 := bstep (se 2 (by rfl) ⟨1305150, by rfl⟩ : syracuseStep 3480401 = 2610301) B2610301
theorem B2320267 : Blo 2061435 2320267 := bstep (se 1 (by rfl) ⟨1740200, by rfl⟩ : syracuseStep 2320267 = 3480401) B3480401
theorem B3093689 : Blo 2061435 3093689 := bstep (se 2 (by rfl) ⟨1160133, by rfl⟩ : syracuseStep 3093689 = 2320267) B2320267
theorem B2062459 : Blo 2061435 2062459 := bstep (se 1 (by rfl) ⟨1546844, by rfl⟩ : syracuseStep 2062459 = 3093689) B3093689
theorem B3527893 : Blo 2061435 3527893 := bbase (se 7 (by rfl) ⟨41342, by rfl⟩ : syracuseStep 3527893 = 82685) (by norm_num)
theorem B18815429 : Blo 2061435 18815429 := bstep (se 4 (by rfl) ⟨1763946, by rfl⟩ : syracuseStep 18815429 = 3527893) B3527893
theorem B12543619 : Blo 2061435 12543619 := bstep (se 1 (by rfl) ⟨9407714, by rfl⟩ : syracuseStep 12543619 = 18815429) B18815429
theorem B16724825 : Blo 2061435 16724825 := bstep (se 2 (by rfl) ⟨6271809, by rfl⟩ : syracuseStep 16724825 = 12543619) B12543619
theorem B11149883 : Blo 2061435 11149883 := bstep (se 1 (by rfl) ⟨8362412, by rfl⟩ : syracuseStep 11149883 = 16724825) B16724825
theorem B7433255 : Blo 2061435 7433255 := bstep (se 1 (by rfl) ⟨5574941, by rfl⟩ : syracuseStep 7433255 = 11149883) B11149883
theorem B4955503 : Blo 2061435 4955503 := bstep (se 1 (by rfl) ⟨3716627, by rfl⟩ : syracuseStep 4955503 = 7433255) B7433255
theorem B6607337 : Blo 2061435 6607337 := bstep (se 2 (by rfl) ⟨2477751, by rfl⟩ : syracuseStep 6607337 = 4955503) B4955503
theorem B17619565 : Blo 2061435 17619565 := bstep (se 3 (by rfl) ⟨3303668, by rfl⟩ : syracuseStep 17619565 = 6607337) B6607337
theorem B23492753 : Blo 2061435 23492753 := bstep (se 2 (by rfl) ⟨8809782, by rfl⟩ : syracuseStep 23492753 = 17619565) B17619565
theorem B15661835 : Blo 2061435 15661835 := bstep (se 1 (by rfl) ⟨11746376, by rfl⟩ : syracuseStep 15661835 = 23492753) B23492753
theorem B10441223 : Blo 2061435 10441223 := bstep (se 1 (by rfl) ⟨7830917, by rfl⟩ : syracuseStep 10441223 = 15661835) B15661835
theorem B6960815 : Blo 2061435 6960815 := bstep (se 1 (by rfl) ⟨5220611, by rfl⟩ : syracuseStep 6960815 = 10441223) B10441223
theorem B4640543 : Blo 2061435 4640543 := bstep (se 1 (by rfl) ⟨3480407, by rfl⟩ : syracuseStep 4640543 = 6960815) B6960815
theorem B3093695 : Blo 2061435 3093695 := bstep (se 1 (by rfl) ⟨2320271, by rfl⟩ : syracuseStep 3093695 = 4640543) B4640543
theorem B2062463 : Blo 2061435 2062463 := bstep (se 1 (by rfl) ⟨1546847, by rfl⟩ : syracuseStep 2062463 = 3093695) B3093695
theorem B3093701 : Blo 2061435 3093701 := bbase (se 4 (by rfl) ⟨290034, by rfl⟩ : syracuseStep 3093701 = 580069) (by norm_num)
theorem B2062467 : Blo 2061435 2062467 := bstep (se 1 (by rfl) ⟨1546850, by rfl⟩ : syracuseStep 2062467 = 3093701) B3093701
theorem B3480421 : Blo 2061435 3480421 := bbase (se 4 (by rfl) ⟨326289, by rfl⟩ : syracuseStep 3480421 = 652579) (by norm_num)
theorem B4640561 : Blo 2061435 4640561 := bstep (se 2 (by rfl) ⟨1740210, by rfl⟩ : syracuseStep 4640561 = 3480421) B3480421
theorem B3093707 : Blo 2061435 3093707 := bstep (se 1 (by rfl) ⟨2320280, by rfl⟩ : syracuseStep 3093707 = 4640561) B4640561
theorem B2062471 : Blo 2061435 2062471 := bstep (se 1 (by rfl) ⟨1546853, by rfl⟩ : syracuseStep 2062471 = 3093707) B3093707
theorem B2320285 : Blo 2061435 2320285 := bbase (se 3 (by rfl) ⟨435053, by rfl⟩ : syracuseStep 2320285 = 870107) (by norm_num)
theorem B3093713 : Blo 2061435 3093713 := bstep (se 2 (by rfl) ⟨1160142, by rfl⟩ : syracuseStep 3093713 = 2320285) B2320285
theorem B2062475 : Blo 2061435 2062475 := bstep (se 1 (by rfl) ⟨1546856, by rfl⟩ : syracuseStep 2062475 = 3093713) B3093713
theorem B6960869 : Blo 2061435 6960869 := bbase (se 4 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 6960869 = 1305163) (by norm_num)
theorem B4640579 : Blo 2061435 4640579 := bstep (se 1 (by rfl) ⟨3480434, by rfl⟩ : syracuseStep 4640579 = 6960869) B6960869
theorem B3093719 : Blo 2061435 3093719 := bstep (se 1 (by rfl) ⟨2320289, by rfl⟩ : syracuseStep 3093719 = 4640579) B4640579
theorem B2062479 : Blo 2061435 2062479 := bstep (se 1 (by rfl) ⟨1546859, by rfl⟩ : syracuseStep 2062479 = 3093719) B3093719
theorem B3093725 : Blo 2061435 3093725 := bbase (se 3 (by rfl) ⟨580073, by rfl⟩ : syracuseStep 3093725 = 1160147) (by norm_num)
theorem B2062483 : Blo 2061435 2062483 := bstep (se 1 (by rfl) ⟨1546862, by rfl⟩ : syracuseStep 2062483 = 3093725) B3093725
theorem B4640597 : Blo 2061435 4640597 := bbase (se 9 (by rfl) ⟨13595, by rfl⟩ : syracuseStep 4640597 = 27191) (by norm_num)
theorem B3093731 : Blo 2061435 3093731 := bstep (se 1 (by rfl) ⟨2320298, by rfl⟩ : syracuseStep 3093731 = 4640597) B4640597
theorem B2062487 : Blo 2061435 2062487 := bstep (se 1 (by rfl) ⟨1546865, by rfl⟩ : syracuseStep 2062487 = 3093731) B3093731
theorem B5873269 : Blo 2061435 5873269 := bbase (se 5 (by rfl) ⟨275309, by rfl⟩ : syracuseStep 5873269 = 550619) (by norm_num)
theorem B7831025 : Blo 2061435 7831025 := bstep (se 2 (by rfl) ⟨2936634, by rfl⟩ : syracuseStep 7831025 = 5873269) B5873269
theorem B5220683 : Blo 2061435 5220683 := bstep (se 1 (by rfl) ⟨3915512, by rfl⟩ : syracuseStep 5220683 = 7831025) B7831025
theorem B3480455 : Blo 2061435 3480455 := bstep (se 1 (by rfl) ⟨2610341, by rfl⟩ : syracuseStep 3480455 = 5220683) B5220683
theorem B2320303 : Blo 2061435 2320303 := bstep (se 1 (by rfl) ⟨1740227, by rfl⟩ : syracuseStep 2320303 = 3480455) B3480455
theorem B3093737 : Blo 2061435 3093737 := bstep (se 2 (by rfl) ⟨1160151, by rfl⟩ : syracuseStep 3093737 = 2320303) B2320303
theorem B2062491 : Blo 2061435 2062491 := bstep (se 1 (by rfl) ⟨1546868, by rfl⟩ : syracuseStep 2062491 = 3093737) B3093737
theorem B8930117 : Blo 2061435 8930117 := bbase (se 4 (by rfl) ⟨837198, by rfl⟩ : syracuseStep 8930117 = 1674397) (by norm_num)
theorem B5953411 : Blo 2061435 5953411 := bstep (se 1 (by rfl) ⟨4465058, by rfl⟩ : syracuseStep 5953411 = 8930117) B8930117
theorem B7937881 : Blo 2061435 7937881 := bstep (se 2 (by rfl) ⟨2976705, by rfl⟩ : syracuseStep 7937881 = 5953411) B5953411
theorem B169341461 : Blo 2061435 169341461 := bstep (se 6 (by rfl) ⟨3968940, by rfl⟩ : syracuseStep 169341461 = 7937881) B7937881
theorem B112894307 : Blo 2061435 112894307 := bstep (se 1 (by rfl) ⟨84670730, by rfl⟩ : syracuseStep 112894307 = 169341461) B169341461
theorem B75262871 : Blo 2061435 75262871 := bstep (se 1 (by rfl) ⟨56447153, by rfl⟩ : syracuseStep 75262871 = 112894307) B112894307
theorem B200700989 : Blo 2061435 200700989 := bstep (se 3 (by rfl) ⟨37631435, by rfl⟩ : syracuseStep 200700989 = 75262871) B75262871
theorem B133800659 : Blo 2061435 133800659 := bstep (se 1 (by rfl) ⟨100350494, by rfl⟩ : syracuseStep 133800659 = 200700989) B200700989
theorem B89200439 : Blo 2061435 89200439 := bstep (se 1 (by rfl) ⟨66900329, by rfl⟩ : syracuseStep 89200439 = 133800659) B133800659
theorem B59466959 : Blo 2061435 59466959 := bstep (se 1 (by rfl) ⟨44600219, by rfl⟩ : syracuseStep 59466959 = 89200439) B89200439
theorem B39644639 : Blo 2061435 39644639 := bstep (se 1 (by rfl) ⟨29733479, by rfl⟩ : syracuseStep 39644639 = 59466959) B59466959
theorem B26429759 : Blo 2061435 26429759 := bstep (se 1 (by rfl) ⟨19822319, by rfl⟩ : syracuseStep 26429759 = 39644639) B39644639
theorem B17619839 : Blo 2061435 17619839 := bstep (se 1 (by rfl) ⟨13214879, by rfl⟩ : syracuseStep 17619839 = 26429759) B26429759
theorem B11746559 : Blo 2061435 11746559 := bstep (se 1 (by rfl) ⟨8809919, by rfl⟩ : syracuseStep 11746559 = 17619839) B17619839
theorem B7831039 : Blo 2061435 7831039 := bstep (se 1 (by rfl) ⟨5873279, by rfl⟩ : syracuseStep 7831039 = 11746559) B11746559
theorem B10441385 : Blo 2061435 10441385 := bstep (se 2 (by rfl) ⟨3915519, by rfl⟩ : syracuseStep 10441385 = 7831039) B7831039
theorem B6960923 : Blo 2061435 6960923 := bstep (se 1 (by rfl) ⟨5220692, by rfl⟩ : syracuseStep 6960923 = 10441385) B10441385
theorem B4640615 : Blo 2061435 4640615 := bstep (se 1 (by rfl) ⟨3480461, by rfl⟩ : syracuseStep 4640615 = 6960923) B6960923
theorem B3093743 : Blo 2061435 3093743 := bstep (se 1 (by rfl) ⟨2320307, by rfl⟩ : syracuseStep 3093743 = 4640615) B4640615
theorem B2062495 : Blo 2061435 2062495 := bstep (se 1 (by rfl) ⟨1546871, by rfl⟩ : syracuseStep 2062495 = 3093743) B3093743
theorem B3093749 : Blo 2061435 3093749 := bbase (se 5 (by rfl) ⟨145019, by rfl⟩ : syracuseStep 3093749 = 290039) (by norm_num)
theorem B2062499 : Blo 2061435 2062499 := bstep (se 1 (by rfl) ⟨1546874, by rfl⟩ : syracuseStep 2062499 = 3093749) B3093749
theorem B13214933 : Blo 2061435 13214933 := bbase (se 7 (by rfl) ⟨154862, by rfl⟩ : syracuseStep 13214933 = 309725) (by norm_num)
theorem B8809955 : Blo 2061435 8809955 := bstep (se 1 (by rfl) ⟨6607466, by rfl⟩ : syracuseStep 8809955 = 13214933) B13214933
theorem B5873303 : Blo 2061435 5873303 := bstep (se 1 (by rfl) ⟨4404977, by rfl⟩ : syracuseStep 5873303 = 8809955) B8809955
theorem B3915535 : Blo 2061435 3915535 := bstep (se 1 (by rfl) ⟨2936651, by rfl⟩ : syracuseStep 3915535 = 5873303) B5873303
theorem B5220713 : Blo 2061435 5220713 := bstep (se 2 (by rfl) ⟨1957767, by rfl⟩ : syracuseStep 5220713 = 3915535) B3915535
theorem B3480475 : Blo 2061435 3480475 := bstep (se 1 (by rfl) ⟨2610356, by rfl⟩ : syracuseStep 3480475 = 5220713) B5220713
theorem B4640633 : Blo 2061435 4640633 := bstep (se 2 (by rfl) ⟨1740237, by rfl⟩ : syracuseStep 4640633 = 3480475) B3480475
theorem B3093755 : Blo 2061435 3093755 := bstep (se 1 (by rfl) ⟨2320316, by rfl⟩ : syracuseStep 3093755 = 4640633) B4640633
theorem B2062503 : Blo 2061435 2062503 := bstep (se 1 (by rfl) ⟨1546877, by rfl⟩ : syracuseStep 2062503 = 3093755) B3093755
theorem B2320321 : Blo 2061435 2320321 := bbase (se 2 (by rfl) ⟨870120, by rfl⟩ : syracuseStep 2320321 = 1740241) (by norm_num)
theorem B3093761 : Blo 2061435 3093761 := bstep (se 2 (by rfl) ⟨1160160, by rfl⟩ : syracuseStep 3093761 = 2320321) B2320321
theorem B2062507 : Blo 2061435 2062507 := bstep (se 1 (by rfl) ⟨1546880, by rfl⟩ : syracuseStep 2062507 = 3093761) B3093761
theorem B5220733 : Blo 2061435 5220733 := bbase (se 3 (by rfl) ⟨978887, by rfl⟩ : syracuseStep 5220733 = 1957775) (by norm_num)
theorem B6960977 : Blo 2061435 6960977 := bstep (se 2 (by rfl) ⟨2610366, by rfl⟩ : syracuseStep 6960977 = 5220733) B5220733
theorem B4640651 : Blo 2061435 4640651 := bstep (se 1 (by rfl) ⟨3480488, by rfl⟩ : syracuseStep 4640651 = 6960977) B6960977
theorem B3093767 : Blo 2061435 3093767 := bstep (se 1 (by rfl) ⟨2320325, by rfl⟩ : syracuseStep 3093767 = 4640651) B4640651
theorem B2062511 : Blo 2061435 2062511 := bstep (se 1 (by rfl) ⟨1546883, by rfl⟩ : syracuseStep 2062511 = 3093767) B3093767
theorem B3093773 : Blo 2061435 3093773 := bbase (se 3 (by rfl) ⟨580082, by rfl⟩ : syracuseStep 3093773 = 1160165) (by norm_num)
theorem B2062515 : Blo 2061435 2062515 := bstep (se 1 (by rfl) ⟨1546886, by rfl⟩ : syracuseStep 2062515 = 3093773) B3093773
theorem B4640669 : Blo 2061435 4640669 := bbase (se 3 (by rfl) ⟨870125, by rfl⟩ : syracuseStep 4640669 = 1740251) (by norm_num)
theorem B3093779 : Blo 2061435 3093779 := bstep (se 1 (by rfl) ⟨2320334, by rfl⟩ : syracuseStep 3093779 = 4640669) B4640669
theorem B2062519 : Blo 2061435 2062519 := bstep (se 1 (by rfl) ⟨1546889, by rfl⟩ : syracuseStep 2062519 = 3093779) B3093779
theorem B3480509 : Blo 2061435 3480509 := bbase (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) (by norm_num)
theorem B2320339 : Blo 2061435 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B3093785 : Blo 2061435 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B2062523 : Blo 2061435 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B11746741 : Blo 2061435 11746741 := bbase (se 5 (by rfl) ⟨550628, by rfl⟩ : syracuseStep 11746741 = 1101257) (by norm_num)
theorem B15662321 : Blo 2061435 15662321 := bstep (se 2 (by rfl) ⟨5873370, by rfl⟩ : syracuseStep 15662321 = 11746741) B11746741
theorem B10441547 : Blo 2061435 10441547 := bstep (se 1 (by rfl) ⟨7831160, by rfl⟩ : syracuseStep 10441547 = 15662321) B15662321
theorem B6961031 : Blo 2061435 6961031 := bstep (se 1 (by rfl) ⟨5220773, by rfl⟩ : syracuseStep 6961031 = 10441547) B10441547
theorem B4640687 : Blo 2061435 4640687 := bstep (se 1 (by rfl) ⟨3480515, by rfl⟩ : syracuseStep 4640687 = 6961031) B6961031
theorem B3093791 : Blo 2061435 3093791 := bstep (se 1 (by rfl) ⟨2320343, by rfl⟩ : syracuseStep 3093791 = 4640687) B4640687
theorem B2062527 : Blo 2061435 2062527 := bstep (se 1 (by rfl) ⟨1546895, by rfl⟩ : syracuseStep 2062527 = 3093791) B3093791
theorem B3093797 : Blo 2061435 3093797 := bbase (se 4 (by rfl) ⟨290043, by rfl⟩ : syracuseStep 3093797 = 580087) (by norm_num)
theorem B2062531 : Blo 2061435 2062531 := bstep (se 1 (by rfl) ⟨1546898, by rfl⟩ : syracuseStep 2062531 = 3093797) B3093797
theorem B2610397 : Blo 2061435 2610397 := bbase (se 3 (by rfl) ⟨489449, by rfl⟩ : syracuseStep 2610397 = 978899) (by norm_num)
theorem B3480529 : Blo 2061435 3480529 := bstep (se 2 (by rfl) ⟨1305198, by rfl⟩ : syracuseStep 3480529 = 2610397) B2610397
theorem B4640705 : Blo 2061435 4640705 := bstep (se 2 (by rfl) ⟨1740264, by rfl⟩ : syracuseStep 4640705 = 3480529) B3480529
theorem B3093803 : Blo 2061435 3093803 := bstep (se 1 (by rfl) ⟨2320352, by rfl⟩ : syracuseStep 3093803 = 4640705) B4640705
theorem B2062535 : Blo 2061435 2062535 := bstep (se 1 (by rfl) ⟨1546901, by rfl⟩ : syracuseStep 2062535 = 3093803) B3093803
theorem B2320357 : Blo 2061435 2320357 := bbase (se 4 (by rfl) ⟨217533, by rfl⟩ : syracuseStep 2320357 = 435067) (by norm_num)
theorem B3093809 : Blo 2061435 3093809 := bstep (se 2 (by rfl) ⟨1160178, by rfl⟩ : syracuseStep 3093809 = 2320357) B2320357
theorem B2062539 : Blo 2061435 2062539 := bstep (se 1 (by rfl) ⟨1546904, by rfl⟩ : syracuseStep 2062539 = 3093809) B3093809
theorem B17860661 : Blo 2061435 17860661 := bbase (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) (by norm_num)
theorem B11907107 : Blo 2061435 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B7938071 : Blo 2061435 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B5292047 : Blo 2061435 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B3528031 : Blo 2061435 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B4704041 : Blo 2061435 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B12544109 : Blo 2061435 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B8362739 : Blo 2061435 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B5575159 : Blo 2061435 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B7433545 : Blo 2061435 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B9911393 : Blo 2061435 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B6607595 : Blo 2061435 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B4405063 : Blo 2061435 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B5873417 : Blo 2061435 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B3915611 : Blo 2061435 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B2610407 : Blo 2061435 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B6961085 : Blo 2061435 6961085 := bstep (se 3 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 6961085 = 2610407) B2610407
theorem B4640723 : Blo 2061435 4640723 := bstep (se 1 (by rfl) ⟨3480542, by rfl⟩ : syracuseStep 4640723 = 6961085) B6961085
theorem B3093815 : Blo 2061435 3093815 := bstep (se 1 (by rfl) ⟨2320361, by rfl⟩ : syracuseStep 3093815 = 4640723) B4640723
theorem B2062543 : Blo 2061435 2062543 := bstep (se 1 (by rfl) ⟨1546907, by rfl⟩ : syracuseStep 2062543 = 3093815) B3093815
theorem B3093821 : Blo 2061435 3093821 := bbase (se 3 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 3093821 = 1160183) (by norm_num)
theorem B2062547 : Blo 2061435 2062547 := bstep (se 1 (by rfl) ⟨1546910, by rfl⟩ : syracuseStep 2062547 = 3093821) B3093821
theorem B4640741 : Blo 2061435 4640741 := bbase (se 4 (by rfl) ⟨435069, by rfl⟩ : syracuseStep 4640741 = 870139) (by norm_num)
theorem B3093827 : Blo 2061435 3093827 := bstep (se 1 (by rfl) ⟨2320370, by rfl⟩ : syracuseStep 3093827 = 4640741) B4640741
theorem B2062551 : Blo 2061435 2062551 := bstep (se 1 (by rfl) ⟨1546913, by rfl⟩ : syracuseStep 2062551 = 3093827) B3093827
theorem B5220845 : Blo 2061435 5220845 := bbase (se 3 (by rfl) ⟨978908, by rfl⟩ : syracuseStep 5220845 = 1957817) (by norm_num)
theorem B3480563 : Blo 2061435 3480563 := bstep (se 1 (by rfl) ⟨2610422, by rfl⟩ : syracuseStep 3480563 = 5220845) B5220845
theorem B2320375 : Blo 2061435 2320375 := bstep (se 1 (by rfl) ⟨1740281, by rfl⟩ : syracuseStep 2320375 = 3480563) B3480563
theorem B3093833 : Blo 2061435 3093833 := bstep (se 2 (by rfl) ⟨1160187, by rfl⟩ : syracuseStep 3093833 = 2320375) B2320375
theorem B2062555 : Blo 2061435 2062555 := bstep (se 1 (by rfl) ⟨1546916, by rfl⟩ : syracuseStep 2062555 = 3093833) B3093833
theorem B2090701 : Blo 2061435 2090701 := bbase (se 3 (by rfl) ⟨392006, by rfl⟩ : syracuseStep 2090701 = 784013) (by norm_num)
theorem B11150405 : Blo 2061435 11150405 := bstep (se 4 (by rfl) ⟨1045350, by rfl⟩ : syracuseStep 11150405 = 2090701) B2090701
theorem B7433603 : Blo 2061435 7433603 := bstep (se 1 (by rfl) ⟨5575202, by rfl⟩ : syracuseStep 7433603 = 11150405) B11150405
theorem B4955735 : Blo 2061435 4955735 := bstep (se 1 (by rfl) ⟨3716801, by rfl⟩ : syracuseStep 4955735 = 7433603) B7433603
theorem B3303823 : Blo 2061435 3303823 := bstep (se 1 (by rfl) ⟨2477867, by rfl⟩ : syracuseStep 3303823 = 4955735) B4955735
theorem B4405097 : Blo 2061435 4405097 := bstep (se 2 (by rfl) ⟨1651911, by rfl⟩ : syracuseStep 4405097 = 3303823) B3303823
theorem B2936731 : Blo 2061435 2936731 := bstep (se 1 (by rfl) ⟨2202548, by rfl⟩ : syracuseStep 2936731 = 4405097) B4405097
theorem B3915641 : Blo 2061435 3915641 := bstep (se 2 (by rfl) ⟨1468365, by rfl⟩ : syracuseStep 3915641 = 2936731) B2936731
theorem B10441709 : Blo 2061435 10441709 := bstep (se 3 (by rfl) ⟨1957820, by rfl⟩ : syracuseStep 10441709 = 3915641) B3915641
theorem B6961139 : Blo 2061435 6961139 := bstep (se 1 (by rfl) ⟨5220854, by rfl⟩ : syracuseStep 6961139 = 10441709) B10441709
theorem B4640759 : Blo 2061435 4640759 := bstep (se 1 (by rfl) ⟨3480569, by rfl⟩ : syracuseStep 4640759 = 6961139) B6961139
theorem B3093839 : Blo 2061435 3093839 := bstep (se 1 (by rfl) ⟨2320379, by rfl⟩ : syracuseStep 3093839 = 4640759) B4640759
theorem B2062559 : Blo 2061435 2062559 := bstep (se 1 (by rfl) ⟨1546919, by rfl⟩ : syracuseStep 2062559 = 3093839) B3093839
theorem B3093845 : Blo 2061435 3093845 := bbase (se 13 (by rfl) ⟨566, by rfl⟩ : syracuseStep 3093845 = 1133) (by norm_num)
theorem B2062563 : Blo 2061435 2062563 := bstep (se 1 (by rfl) ⟨1546922, by rfl⟩ : syracuseStep 2062563 = 3093845) B3093845
theorem B2202557 : Blo 2061435 2202557 := bbase (se 3 (by rfl) ⟨412979, by rfl⟩ : syracuseStep 2202557 = 825959) (by norm_num)
theorem B5873485 : Blo 2061435 5873485 := bstep (se 3 (by rfl) ⟨1101278, by rfl⟩ : syracuseStep 5873485 = 2202557) B2202557
theorem B7831313 : Blo 2061435 7831313 := bstep (se 2 (by rfl) ⟨2936742, by rfl⟩ : syracuseStep 7831313 = 5873485) B5873485
theorem B5220875 : Blo 2061435 5220875 := bstep (se 1 (by rfl) ⟨3915656, by rfl⟩ : syracuseStep 5220875 = 7831313) B7831313
theorem B3480583 : Blo 2061435 3480583 := bstep (se 1 (by rfl) ⟨2610437, by rfl⟩ : syracuseStep 3480583 = 5220875) B5220875
theorem B4640777 : Blo 2061435 4640777 := bstep (se 2 (by rfl) ⟨1740291, by rfl⟩ : syracuseStep 4640777 = 3480583) B3480583
theorem B3093851 : Blo 2061435 3093851 := bstep (se 1 (by rfl) ⟨2320388, by rfl⟩ : syracuseStep 3093851 = 4640777) B4640777
theorem B2062567 : Blo 2061435 2062567 := bstep (se 1 (by rfl) ⟨1546925, by rfl⟩ : syracuseStep 2062567 = 3093851) B3093851
theorem B2320393 : Blo 2061435 2320393 := bbase (se 2 (by rfl) ⟨870147, by rfl⟩ : syracuseStep 2320393 = 1740295) (by norm_num)
theorem B3093857 : Blo 2061435 3093857 := bstep (se 2 (by rfl) ⟨1160196, by rfl⟩ : syracuseStep 3093857 = 2320393) B2320393
theorem B2062571 : Blo 2061435 2062571 := bstep (se 1 (by rfl) ⟨1546928, by rfl⟩ : syracuseStep 2062571 = 3093857) B3093857
theorem B14867317 : Blo 2061435 14867317 := bbase (se 5 (by rfl) ⟨696905, by rfl⟩ : syracuseStep 14867317 = 1393811) (by norm_num)
theorem B19823089 : Blo 2061435 19823089 := bstep (se 2 (by rfl) ⟨7433658, by rfl⟩ : syracuseStep 19823089 = 14867317) B14867317
theorem B26430785 : Blo 2061435 26430785 := bstep (se 2 (by rfl) ⟨9911544, by rfl⟩ : syracuseStep 26430785 = 19823089) B19823089
theorem B17620523 : Blo 2061435 17620523 := bstep (se 1 (by rfl) ⟨13215392, by rfl⟩ : syracuseStep 17620523 = 26430785) B26430785
theorem B11747015 : Blo 2061435 11747015 := bstep (se 1 (by rfl) ⟨8810261, by rfl⟩ : syracuseStep 11747015 = 17620523) B17620523
theorem B7831343 : Blo 2061435 7831343 := bstep (se 1 (by rfl) ⟨5873507, by rfl⟩ : syracuseStep 7831343 = 11747015) B11747015
theorem B5220895 : Blo 2061435 5220895 := bstep (se 1 (by rfl) ⟨3915671, by rfl⟩ : syracuseStep 5220895 = 7831343) B7831343
theorem B6961193 : Blo 2061435 6961193 := bstep (se 2 (by rfl) ⟨2610447, by rfl⟩ : syracuseStep 6961193 = 5220895) B5220895
theorem B4640795 : Blo 2061435 4640795 := bstep (se 1 (by rfl) ⟨3480596, by rfl⟩ : syracuseStep 4640795 = 6961193) B6961193
theorem B3093863 : Blo 2061435 3093863 := bstep (se 1 (by rfl) ⟨2320397, by rfl⟩ : syracuseStep 3093863 = 4640795) B4640795
theorem B2062575 : Blo 2061435 2062575 := bstep (se 1 (by rfl) ⟨1546931, by rfl⟩ : syracuseStep 2062575 = 3093863) B3093863
theorem B3093869 : Blo 2061435 3093869 := bbase (se 3 (by rfl) ⟨580100, by rfl⟩ : syracuseStep 3093869 = 1160201) (by norm_num)
theorem B2062579 : Blo 2061435 2062579 := bstep (se 1 (by rfl) ⟨1546934, by rfl⟩ : syracuseStep 2062579 = 3093869) B3093869
theorem B4640813 : Blo 2061435 4640813 := bbase (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) (by norm_num)
theorem B3093875 : Blo 2061435 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B2062583 : Blo 2061435 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B9911605 : Blo 2061435 9911605 := bbase (se 5 (by rfl) ⟨464606, by rfl⟩ : syracuseStep 9911605 = 929213) (by norm_num)
theorem B13215473 : Blo 2061435 13215473 := bstep (se 2 (by rfl) ⟨4955802, by rfl⟩ : syracuseStep 13215473 = 9911605) B9911605
theorem B8810315 : Blo 2061435 8810315 := bstep (se 1 (by rfl) ⟨6607736, by rfl⟩ : syracuseStep 8810315 = 13215473) B13215473
theorem B5873543 : Blo 2061435 5873543 := bstep (se 1 (by rfl) ⟨4405157, by rfl⟩ : syracuseStep 5873543 = 8810315) B8810315
theorem B3915695 : Blo 2061435 3915695 := bstep (se 1 (by rfl) ⟨2936771, by rfl⟩ : syracuseStep 3915695 = 5873543) B5873543
theorem B2610463 : Blo 2061435 2610463 := bstep (se 1 (by rfl) ⟨1957847, by rfl⟩ : syracuseStep 2610463 = 3915695) B3915695
theorem B3480617 : Blo 2061435 3480617 := bstep (se 2 (by rfl) ⟨1305231, by rfl⟩ : syracuseStep 3480617 = 2610463) B2610463
theorem B2320411 : Blo 2061435 2320411 := bstep (se 1 (by rfl) ⟨1740308, by rfl⟩ : syracuseStep 2320411 = 3480617) B3480617
theorem B3093881 : Blo 2061435 3093881 := bstep (se 2 (by rfl) ⟨1160205, by rfl⟩ : syracuseStep 3093881 = 2320411) B2320411
theorem B2062587 : Blo 2061435 2062587 := bstep (se 1 (by rfl) ⟨1546940, by rfl⟩ : syracuseStep 2062587 = 3093881) B3093881
theorem B9911621 : Blo 2061435 9911621 := bbase (se 4 (by rfl) ⟨929214, by rfl⟩ : syracuseStep 9911621 = 1858429) (by norm_num)
theorem B6607747 : Blo 2061435 6607747 := bstep (se 1 (by rfl) ⟨4955810, by rfl⟩ : syracuseStep 6607747 = 9911621) B9911621
theorem B35241317 : Blo 2061435 35241317 := bstep (se 4 (by rfl) ⟨3303873, by rfl⟩ : syracuseStep 35241317 = 6607747) B6607747
theorem B23494211 : Blo 2061435 23494211 := bstep (se 1 (by rfl) ⟨17620658, by rfl⟩ : syracuseStep 23494211 = 35241317) B35241317
theorem B15662807 : Blo 2061435 15662807 := bstep (se 1 (by rfl) ⟨11747105, by rfl⟩ : syracuseStep 15662807 = 23494211) B23494211
theorem B10441871 : Blo 2061435 10441871 := bstep (se 1 (by rfl) ⟨7831403, by rfl⟩ : syracuseStep 10441871 = 15662807) B15662807
theorem B6961247 : Blo 2061435 6961247 := bstep (se 1 (by rfl) ⟨5220935, by rfl⟩ : syracuseStep 6961247 = 10441871) B10441871
theorem B4640831 : Blo 2061435 4640831 := bstep (se 1 (by rfl) ⟨3480623, by rfl⟩ : syracuseStep 4640831 = 6961247) B6961247
theorem B3093887 : Blo 2061435 3093887 := bstep (se 1 (by rfl) ⟨2320415, by rfl⟩ : syracuseStep 3093887 = 4640831) B4640831
theorem B2062591 : Blo 2061435 2062591 := bstep (se 1 (by rfl) ⟨1546943, by rfl⟩ : syracuseStep 2062591 = 3093887) B3093887
theorem B3093893 : Blo 2061435 3093893 := bbase (se 4 (by rfl) ⟨290052, by rfl⟩ : syracuseStep 3093893 = 580105) (by norm_num)
theorem B2062595 : Blo 2061435 2062595 := bstep (se 1 (by rfl) ⟨1546946, by rfl⟩ : syracuseStep 2062595 = 3093893) B3093893
theorem B3480637 : Blo 2061435 3480637 := bbase (se 3 (by rfl) ⟨652619, by rfl⟩ : syracuseStep 3480637 = 1305239) (by norm_num)
theorem B4640849 : Blo 2061435 4640849 := bstep (se 2 (by rfl) ⟨1740318, by rfl⟩ : syracuseStep 4640849 = 3480637) B3480637
theorem B3093899 : Blo 2061435 3093899 := bstep (se 1 (by rfl) ⟨2320424, by rfl⟩ : syracuseStep 3093899 = 4640849) B4640849
theorem B2062599 : Blo 2061435 2062599 := bstep (se 1 (by rfl) ⟨1546949, by rfl⟩ : syracuseStep 2062599 = 3093899) B3093899
theorem B2320429 : Blo 2061435 2320429 := bbase (se 3 (by rfl) ⟨435080, by rfl⟩ : syracuseStep 2320429 = 870161) (by norm_num)
theorem B3093905 : Blo 2061435 3093905 := bstep (se 2 (by rfl) ⟨1160214, by rfl⟩ : syracuseStep 3093905 = 2320429) B2320429
theorem B2062603 : Blo 2061435 2062603 := bstep (se 1 (by rfl) ⟨1546952, by rfl⟩ : syracuseStep 2062603 = 3093905) B3093905
theorem B6961301 : Blo 2061435 6961301 := bbase (se 6 (by rfl) ⟨163155, by rfl⟩ : syracuseStep 6961301 = 326311) (by norm_num)
theorem B4640867 : Blo 2061435 4640867 := bstep (se 1 (by rfl) ⟨3480650, by rfl⟩ : syracuseStep 4640867 = 6961301) B6961301
theorem B3093911 : Blo 2061435 3093911 := bstep (se 1 (by rfl) ⟨2320433, by rfl⟩ : syracuseStep 3093911 = 4640867) B4640867
theorem B2062607 : Blo 2061435 2062607 := bstep (se 1 (by rfl) ⟨1546955, by rfl⟩ : syracuseStep 2062607 = 3093911) B3093911
theorem B3093917 : Blo 2061435 3093917 := bbase (se 3 (by rfl) ⟨580109, by rfl⟩ : syracuseStep 3093917 = 1160219) (by norm_num)
theorem B2062611 : Blo 2061435 2062611 := bstep (se 1 (by rfl) ⟨1546958, by rfl⟩ : syracuseStep 2062611 = 3093917) B3093917
theorem B4640885 : Blo 2061435 4640885 := bbase (se 5 (by rfl) ⟨217541, by rfl⟩ : syracuseStep 4640885 = 435083) (by norm_num)
theorem B3093923 : Blo 2061435 3093923 := bstep (se 1 (by rfl) ⟨2320442, by rfl⟩ : syracuseStep 3093923 = 4640885) B4640885
theorem B2062615 : Blo 2061435 2062615 := bstep (se 1 (by rfl) ⟨1546961, by rfl⟩ : syracuseStep 2062615 = 3093923) B3093923
theorem B3969181 : Blo 2061435 3969181 := bbase (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) (by norm_num)
theorem B21168965 : Blo 2061435 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B14112643 : Blo 2061435 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B18816857 : Blo 2061435 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B12544571 : Blo 2061435 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B8363047 : Blo 2061435 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B11150729 : Blo 2061435 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B7433819 : Blo 2061435 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B4955879 : Blo 2061435 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B3303919 : Blo 2061435 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B17620901 : Blo 2061435 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B11747267 : Blo 2061435 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B7831511 : Blo 2061435 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B5221007 : Blo 2061435 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B3480671 : Blo 2061435 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B2320447 : Blo 2061435 2320447 := bstep (se 1 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 2320447 = 3480671) B3480671
theorem B3093929 : Blo 2061435 3093929 := bstep (se 2 (by rfl) ⟨1160223, by rfl⟩ : syracuseStep 3093929 = 2320447) B2320447
theorem B2062619 : Blo 2061435 2062619 := bstep (se 1 (by rfl) ⟨1546964, by rfl⟩ : syracuseStep 2062619 = 3093929) B3093929
theorem B7831525 : Blo 2061435 7831525 := bbase (se 4 (by rfl) ⟨734205, by rfl⟩ : syracuseStep 7831525 = 1468411) (by norm_num)
theorem B10442033 : Blo 2061435 10442033 := bstep (se 2 (by rfl) ⟨3915762, by rfl⟩ : syracuseStep 10442033 = 7831525) B7831525
theorem B6961355 : Blo 2061435 6961355 := bstep (se 1 (by rfl) ⟨5221016, by rfl⟩ : syracuseStep 6961355 = 10442033) B10442033
theorem B4640903 : Blo 2061435 4640903 := bstep (se 1 (by rfl) ⟨3480677, by rfl⟩ : syracuseStep 4640903 = 6961355) B6961355
theorem B3093935 : Blo 2061435 3093935 := bstep (se 1 (by rfl) ⟨2320451, by rfl⟩ : syracuseStep 3093935 = 4640903) B4640903
theorem B2062623 : Blo 2061435 2062623 := bstep (se 1 (by rfl) ⟨1546967, by rfl⟩ : syracuseStep 2062623 = 3093935) B3093935
theorem B3093941 : Blo 2061435 3093941 := bbase (se 5 (by rfl) ⟨145028, by rfl⟩ : syracuseStep 3093941 = 290057) (by norm_num)
theorem B2062627 : Blo 2061435 2062627 := bstep (se 1 (by rfl) ⟨1546970, by rfl⟩ : syracuseStep 2062627 = 3093941) B3093941
theorem B5221037 : Blo 2061435 5221037 := bbase (se 3 (by rfl) ⟨978944, by rfl⟩ : syracuseStep 5221037 = 1957889) (by norm_num)
theorem B3480691 : Blo 2061435 3480691 := bstep (se 1 (by rfl) ⟨2610518, by rfl⟩ : syracuseStep 3480691 = 5221037) B5221037
theorem B4640921 : Blo 2061435 4640921 := bstep (se 2 (by rfl) ⟨1740345, by rfl⟩ : syracuseStep 4640921 = 3480691) B3480691
theorem B3093947 : Blo 2061435 3093947 := bstep (se 1 (by rfl) ⟨2320460, by rfl⟩ : syracuseStep 3093947 = 4640921) B4640921
theorem B2062631 : Blo 2061435 2062631 := bstep (se 1 (by rfl) ⟨1546973, by rfl⟩ : syracuseStep 2062631 = 3093947) B3093947
theorem B2320465 : Blo 2061435 2320465 := bbase (se 2 (by rfl) ⟨870174, by rfl⟩ : syracuseStep 2320465 = 1740349) (by norm_num)
theorem B3093953 : Blo 2061435 3093953 := bstep (se 2 (by rfl) ⟨1160232, by rfl⟩ : syracuseStep 3093953 = 2320465) B2320465
theorem B2062635 : Blo 2061435 2062635 := bstep (se 1 (by rfl) ⟨1546976, by rfl⟩ : syracuseStep 2062635 = 3093953) B3093953
theorem B2936845 : Blo 2061435 2936845 := bbase (se 3 (by rfl) ⟨550658, by rfl⟩ : syracuseStep 2936845 = 1101317) (by norm_num)
theorem B3915793 : Blo 2061435 3915793 := bstep (se 2 (by rfl) ⟨1468422, by rfl⟩ : syracuseStep 3915793 = 2936845) B2936845
theorem B5221057 : Blo 2061435 5221057 := bstep (se 2 (by rfl) ⟨1957896, by rfl⟩ : syracuseStep 5221057 = 3915793) B3915793
theorem B6961409 : Blo 2061435 6961409 := bstep (se 2 (by rfl) ⟨2610528, by rfl⟩ : syracuseStep 6961409 = 5221057) B5221057
theorem B4640939 : Blo 2061435 4640939 := bstep (se 1 (by rfl) ⟨3480704, by rfl⟩ : syracuseStep 4640939 = 6961409) B6961409
theorem B3093959 : Blo 2061435 3093959 := bstep (se 1 (by rfl) ⟨2320469, by rfl⟩ : syracuseStep 3093959 = 4640939) B4640939
theorem B2062639 : Blo 2061435 2062639 := bstep (se 1 (by rfl) ⟨1546979, by rfl⟩ : syracuseStep 2062639 = 3093959) B3093959
theorem B3093965 : Blo 2061435 3093965 := bbase (se 3 (by rfl) ⟨580118, by rfl⟩ : syracuseStep 3093965 = 1160237) (by norm_num)
theorem B2062643 : Blo 2061435 2062643 := bstep (se 1 (by rfl) ⟨1546982, by rfl⟩ : syracuseStep 2062643 = 3093965) B3093965
theorem B4640957 : Blo 2061435 4640957 := bbase (se 3 (by rfl) ⟨870179, by rfl⟩ : syracuseStep 4640957 = 1740359) (by norm_num)
theorem B3093971 : Blo 2061435 3093971 := bstep (se 1 (by rfl) ⟨2320478, by rfl⟩ : syracuseStep 3093971 = 4640957) B4640957
theorem B2062647 : Blo 2061435 2062647 := bstep (se 1 (by rfl) ⟨1546985, by rfl⟩ : syracuseStep 2062647 = 3093971) B3093971
theorem B3480725 : Blo 2061435 3480725 := bbase (se 6 (by rfl) ⟨81579, by rfl⟩ : syracuseStep 3480725 = 163159) (by norm_num)
theorem B2320483 : Blo 2061435 2320483 := bstep (se 1 (by rfl) ⟨1740362, by rfl⟩ : syracuseStep 2320483 = 3480725) B3480725
theorem B3093977 : Blo 2061435 3093977 := bstep (se 2 (by rfl) ⟨1160241, by rfl⟩ : syracuseStep 3093977 = 2320483) B2320483
theorem B2062651 : Blo 2061435 2062651 := bstep (se 1 (by rfl) ⟨1546988, by rfl⟩ : syracuseStep 2062651 = 3093977) B3093977
theorem B25431893 : Blo 2061435 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B16954595 : Blo 2061435 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B11303063 : Blo 2061435 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B7535375 : Blo 2061435 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B5023583 : Blo 2061435 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B3349055 : Blo 2061435 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B2232703 : Blo 2061435 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B11907749 : Blo 2061435 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B7938499 : Blo 2061435 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B10584665 : Blo 2061435 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B7056443 : Blo 2061435 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B18817181 : Blo 2061435 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B12544787 : Blo 2061435 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B8363191 : Blo 2061435 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B11150921 : Blo 2061435 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B7433947 : Blo 2061435 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B9911929 : Blo 2061435 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B13215905 : Blo 2061435 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B8810603 : Blo 2061435 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B5873735 : Blo 2061435 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B15663293 : Blo 2061435 15663293 := bstep (se 3 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 15663293 = 5873735) B5873735
theorem B10442195 : Blo 2061435 10442195 := bstep (se 1 (by rfl) ⟨7831646, by rfl⟩ : syracuseStep 10442195 = 15663293) B15663293
theorem B6961463 : Blo 2061435 6961463 := bstep (se 1 (by rfl) ⟨5221097, by rfl⟩ : syracuseStep 6961463 = 10442195) B10442195
theorem B4640975 : Blo 2061435 4640975 := bstep (se 1 (by rfl) ⟨3480731, by rfl⟩ : syracuseStep 4640975 = 6961463) B6961463
theorem B3093983 : Blo 2061435 3093983 := bstep (se 1 (by rfl) ⟨2320487, by rfl⟩ : syracuseStep 3093983 = 4640975) B4640975
theorem B2062655 : Blo 2061435 2062655 := bstep (se 1 (by rfl) ⟨1546991, by rfl⟩ : syracuseStep 2062655 = 3093983) B3093983
theorem B3093989 : Blo 2061435 3093989 := bbase (se 4 (by rfl) ⟨290061, by rfl⟩ : syracuseStep 3093989 = 580123) (by norm_num)
theorem B2062659 : Blo 2061435 2062659 := bstep (se 1 (by rfl) ⟨1546994, by rfl⟩ : syracuseStep 2062659 = 3093989) B3093989
theorem B9408629 : Blo 2061435 9408629 := bbase (se 5 (by rfl) ⟨441029, by rfl⟩ : syracuseStep 9408629 = 882059) (by norm_num)
theorem B6272419 : Blo 2061435 6272419 := bstep (se 1 (by rfl) ⟨4704314, by rfl⟩ : syracuseStep 6272419 = 9408629) B9408629
theorem B8363225 : Blo 2061435 8363225 := bstep (se 2 (by rfl) ⟨3136209, by rfl⟩ : syracuseStep 8363225 = 6272419) B6272419
theorem B5575483 : Blo 2061435 5575483 := bstep (se 1 (by rfl) ⟨4181612, by rfl⟩ : syracuseStep 5575483 = 8363225) B8363225
theorem B29735909 : Blo 2061435 29735909 := bstep (se 4 (by rfl) ⟨2787741, by rfl⟩ : syracuseStep 29735909 = 5575483) B5575483
theorem B19823939 : Blo 2061435 19823939 := bstep (se 1 (by rfl) ⟨14867954, by rfl⟩ : syracuseStep 19823939 = 29735909) B29735909
theorem B13215959 : Blo 2061435 13215959 := bstep (se 1 (by rfl) ⟨9911969, by rfl⟩ : syracuseStep 13215959 = 19823939) B19823939
theorem B8810639 : Blo 2061435 8810639 := bstep (se 1 (by rfl) ⟨6607979, by rfl⟩ : syracuseStep 8810639 = 13215959) B13215959
theorem B5873759 : Blo 2061435 5873759 := bstep (se 1 (by rfl) ⟨4405319, by rfl⟩ : syracuseStep 5873759 = 8810639) B8810639
theorem B3915839 : Blo 2061435 3915839 := bstep (se 1 (by rfl) ⟨2936879, by rfl⟩ : syracuseStep 3915839 = 5873759) B5873759
theorem B2610559 : Blo 2061435 2610559 := bstep (se 1 (by rfl) ⟨1957919, by rfl⟩ : syracuseStep 2610559 = 3915839) B3915839
theorem B3480745 : Blo 2061435 3480745 := bstep (se 2 (by rfl) ⟨1305279, by rfl⟩ : syracuseStep 3480745 = 2610559) B2610559
theorem B4640993 : Blo 2061435 4640993 := bstep (se 2 (by rfl) ⟨1740372, by rfl⟩ : syracuseStep 4640993 = 3480745) B3480745
theorem B3093995 : Blo 2061435 3093995 := bstep (se 1 (by rfl) ⟨2320496, by rfl⟩ : syracuseStep 3093995 = 4640993) B4640993
theorem B2062663 : Blo 2061435 2062663 := bstep (se 1 (by rfl) ⟨1546997, by rfl⟩ : syracuseStep 2062663 = 3093995) B3093995
theorem B2320501 : Blo 2061435 2320501 := bbase (se 5 (by rfl) ⟨108773, by rfl⟩ : syracuseStep 2320501 = 217547) (by norm_num)
theorem B3094001 : Blo 2061435 3094001 := bstep (se 2 (by rfl) ⟨1160250, by rfl⟩ : syracuseStep 3094001 = 2320501) B2320501
theorem B2062667 : Blo 2061435 2062667 := bstep (se 1 (by rfl) ⟨1547000, by rfl⟩ : syracuseStep 2062667 = 3094001) B3094001
theorem B2610569 : Blo 2061435 2610569 := bbase (se 2 (by rfl) ⟨978963, by rfl⟩ : syracuseStep 2610569 = 1957927) (by norm_num)
theorem B6961517 : Blo 2061435 6961517 := bstep (se 3 (by rfl) ⟨1305284, by rfl⟩ : syracuseStep 6961517 = 2610569) B2610569
theorem B4641011 : Blo 2061435 4641011 := bstep (se 1 (by rfl) ⟨3480758, by rfl⟩ : syracuseStep 4641011 = 6961517) B6961517
theorem B3094007 : Blo 2061435 3094007 := bstep (se 1 (by rfl) ⟨2320505, by rfl⟩ : syracuseStep 3094007 = 4641011) B4641011
theorem B2062671 : Blo 2061435 2062671 := bstep (se 1 (by rfl) ⟨1547003, by rfl⟩ : syracuseStep 2062671 = 3094007) B3094007
theorem B3094013 : Blo 2061435 3094013 := bbase (se 3 (by rfl) ⟨580127, by rfl⟩ : syracuseStep 3094013 = 1160255) (by norm_num)
theorem B2062675 : Blo 2061435 2062675 := bstep (se 1 (by rfl) ⟨1547006, by rfl⟩ : syracuseStep 2062675 = 3094013) B3094013
theorem B4641029 : Blo 2061435 4641029 := bbase (se 4 (by rfl) ⟨435096, by rfl⟩ : syracuseStep 4641029 = 870193) (by norm_num)
theorem B3094019 : Blo 2061435 3094019 := bstep (se 1 (by rfl) ⟨2320514, by rfl⟩ : syracuseStep 3094019 = 4641029) B4641029
theorem B2062679 : Blo 2061435 2062679 := bstep (se 1 (by rfl) ⟨1547009, by rfl⟩ : syracuseStep 2062679 = 3094019) B3094019
theorem B3915877 : Blo 2061435 3915877 := bbase (se 4 (by rfl) ⟨367113, by rfl⟩ : syracuseStep 3915877 = 734227) (by norm_num)
theorem B5221169 : Blo 2061435 5221169 := bstep (se 2 (by rfl) ⟨1957938, by rfl⟩ : syracuseStep 5221169 = 3915877) B3915877
theorem B3480779 : Blo 2061435 3480779 := bstep (se 1 (by rfl) ⟨2610584, by rfl⟩ : syracuseStep 3480779 = 5221169) B5221169
theorem B2320519 : Blo 2061435 2320519 := bstep (se 1 (by rfl) ⟨1740389, by rfl⟩ : syracuseStep 2320519 = 3480779) B3480779
theorem B3094025 : Blo 2061435 3094025 := bstep (se 2 (by rfl) ⟨1160259, by rfl⟩ : syracuseStep 3094025 = 2320519) B2320519
theorem B2062683 : Blo 2061435 2062683 := bstep (se 1 (by rfl) ⟨1547012, by rfl⟩ : syracuseStep 2062683 = 3094025) B3094025
theorem B10442357 : Blo 2061435 10442357 := bbase (se 5 (by rfl) ⟨489485, by rfl⟩ : syracuseStep 10442357 = 978971) (by norm_num)
theorem B6961571 : Blo 2061435 6961571 := bstep (se 1 (by rfl) ⟨5221178, by rfl⟩ : syracuseStep 6961571 = 10442357) B10442357
theorem B4641047 : Blo 2061435 4641047 := bstep (se 1 (by rfl) ⟨3480785, by rfl⟩ : syracuseStep 4641047 = 6961571) B6961571
theorem B3094031 : Blo 2061435 3094031 := bstep (se 1 (by rfl) ⟨2320523, by rfl⟩ : syracuseStep 3094031 = 4641047) B4641047
theorem B2062687 : Blo 2061435 2062687 := bstep (se 1 (by rfl) ⟨1547015, by rfl⟩ : syracuseStep 2062687 = 3094031) B3094031
theorem B3094037 : Blo 2061435 3094037 := bbase (se 6 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 3094037 = 145033) (by norm_num)
theorem B2062691 : Blo 2061435 2062691 := bstep (se 1 (by rfl) ⟨1547018, by rfl⟩ : syracuseStep 2062691 = 3094037) B3094037
theorem B4956061 : Blo 2061435 4956061 := bbase (se 3 (by rfl) ⟨929261, by rfl⟩ : syracuseStep 4956061 = 1858523) (by norm_num)
theorem B6608081 : Blo 2061435 6608081 := bstep (se 2 (by rfl) ⟨2478030, by rfl⟩ : syracuseStep 6608081 = 4956061) B4956061
theorem B17621549 : Blo 2061435 17621549 := bstep (se 3 (by rfl) ⟨3304040, by rfl⟩ : syracuseStep 17621549 = 6608081) B6608081
theorem B11747699 : Blo 2061435 11747699 := bstep (se 1 (by rfl) ⟨8810774, by rfl⟩ : syracuseStep 11747699 = 17621549) B17621549
theorem B7831799 : Blo 2061435 7831799 := bstep (se 1 (by rfl) ⟨5873849, by rfl⟩ : syracuseStep 7831799 = 11747699) B11747699
theorem B5221199 : Blo 2061435 5221199 := bstep (se 1 (by rfl) ⟨3915899, by rfl⟩ : syracuseStep 5221199 = 7831799) B7831799
theorem B3480799 : Blo 2061435 3480799 := bstep (se 1 (by rfl) ⟨2610599, by rfl⟩ : syracuseStep 3480799 = 5221199) B5221199
theorem B4641065 : Blo 2061435 4641065 := bstep (se 2 (by rfl) ⟨1740399, by rfl⟩ : syracuseStep 4641065 = 3480799) B3480799
theorem B3094043 : Blo 2061435 3094043 := bstep (se 1 (by rfl) ⟨2320532, by rfl⟩ : syracuseStep 3094043 = 4641065) B4641065
theorem B2062695 : Blo 2061435 2062695 := bstep (se 1 (by rfl) ⟨1547021, by rfl⟩ : syracuseStep 2062695 = 3094043) B3094043
theorem B2320537 : Blo 2061435 2320537 := bbase (se 2 (by rfl) ⟨870201, by rfl⟩ : syracuseStep 2320537 = 1740403) (by norm_num)
theorem B3094049 : Blo 2061435 3094049 := bstep (se 2 (by rfl) ⟨1160268, by rfl⟩ : syracuseStep 3094049 = 2320537) B2320537
theorem B2062699 : Blo 2061435 2062699 := bstep (se 1 (by rfl) ⟨1547024, by rfl⟩ : syracuseStep 2062699 = 3094049) B3094049
theorem B7831829 : Blo 2061435 7831829 := bbase (se 6 (by rfl) ⟨183558, by rfl⟩ : syracuseStep 7831829 = 367117) (by norm_num)
theorem B5221219 : Blo 2061435 5221219 := bstep (se 1 (by rfl) ⟨3915914, by rfl⟩ : syracuseStep 5221219 = 7831829) B7831829
theorem B6961625 : Blo 2061435 6961625 := bstep (se 2 (by rfl) ⟨2610609, by rfl⟩ : syracuseStep 6961625 = 5221219) B5221219
theorem B4641083 : Blo 2061435 4641083 := bstep (se 1 (by rfl) ⟨3480812, by rfl⟩ : syracuseStep 4641083 = 6961625) B6961625
theorem B3094055 : Blo 2061435 3094055 := bstep (se 1 (by rfl) ⟨2320541, by rfl⟩ : syracuseStep 3094055 = 4641083) B4641083
theorem B2062703 : Blo 2061435 2062703 := bstep (se 1 (by rfl) ⟨1547027, by rfl⟩ : syracuseStep 2062703 = 3094055) B3094055
theorem B3094061 : Blo 2061435 3094061 := bbase (se 3 (by rfl) ⟨580136, by rfl⟩ : syracuseStep 3094061 = 1160273) (by norm_num)
theorem B2062707 : Blo 2061435 2062707 := bstep (se 1 (by rfl) ⟨1547030, by rfl⟩ : syracuseStep 2062707 = 3094061) B3094061
theorem B4641101 : Blo 2061435 4641101 := bbase (se 3 (by rfl) ⟨870206, by rfl⟩ : syracuseStep 4641101 = 1740413) (by norm_num)
theorem B3094067 : Blo 2061435 3094067 := bstep (se 1 (by rfl) ⟨2320550, by rfl⟩ : syracuseStep 3094067 = 4641101) B4641101
theorem B2062711 : Blo 2061435 2062711 := bstep (se 1 (by rfl) ⟨1547033, by rfl⟩ : syracuseStep 2062711 = 3094067) B3094067
theorem B2610625 : Blo 2061435 2610625 := bbase (se 2 (by rfl) ⟨978984, by rfl⟩ : syracuseStep 2610625 = 1957969) (by norm_num)
theorem B3480833 : Blo 2061435 3480833 := bstep (se 2 (by rfl) ⟨1305312, by rfl⟩ : syracuseStep 3480833 = 2610625) B2610625
theorem B2320555 : Blo 2061435 2320555 := bstep (se 1 (by rfl) ⟨1740416, by rfl⟩ : syracuseStep 2320555 = 3480833) B3480833
theorem B3094073 : Blo 2061435 3094073 := bstep (se 2 (by rfl) ⟨1160277, by rfl⟩ : syracuseStep 3094073 = 2320555) B2320555
theorem B2062715 : Blo 2061435 2062715 := bstep (se 1 (by rfl) ⟨1547036, by rfl⟩ : syracuseStep 2062715 = 3094073) B3094073
theorem B5023741 : Blo 2061435 5023741 := bbase (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) (by norm_num)
theorem B6698321 : Blo 2061435 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B4465547 : Blo 2061435 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B2977031 : Blo 2061435 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B7938749 : Blo 2061435 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B5292499 : Blo 2061435 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B7056665 : Blo 2061435 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B4704443 : Blo 2061435 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B3136295 : Blo 2061435 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B2090863 : Blo 2061435 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B11151269 : Blo 2061435 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B7434179 : Blo 2061435 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B4956119 : Blo 2061435 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B3304079 : Blo 2061435 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B2202719 : Blo 2061435 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B23495669 : Blo 2061435 23495669 := bstep (se 5 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 23495669 = 2202719) B2202719
theorem B15663779 : Blo 2061435 15663779 := bstep (se 1 (by rfl) ⟨11747834, by rfl⟩ : syracuseStep 15663779 = 23495669) B23495669
theorem B10442519 : Blo 2061435 10442519 := bstep (se 1 (by rfl) ⟨7831889, by rfl⟩ : syracuseStep 10442519 = 15663779) B15663779
theorem B6961679 : Blo 2061435 6961679 := bstep (se 1 (by rfl) ⟨5221259, by rfl⟩ : syracuseStep 6961679 = 10442519) B10442519
theorem B4641119 : Blo 2061435 4641119 := bstep (se 1 (by rfl) ⟨3480839, by rfl⟩ : syracuseStep 4641119 = 6961679) B6961679
theorem B3094079 : Blo 2061435 3094079 := bstep (se 1 (by rfl) ⟨2320559, by rfl⟩ : syracuseStep 3094079 = 4641119) B4641119
theorem B2062719 : Blo 2061435 2062719 := bstep (se 1 (by rfl) ⟨1547039, by rfl⟩ : syracuseStep 2062719 = 3094079) B3094079
theorem B3094085 : Blo 2061435 3094085 := bbase (se 4 (by rfl) ⟨290070, by rfl⟩ : syracuseStep 3094085 = 580141) (by norm_num)
theorem B2062723 : Blo 2061435 2062723 := bstep (se 1 (by rfl) ⟨1547042, by rfl⟩ : syracuseStep 2062723 = 3094085) B3094085
theorem B3480853 : Blo 2061435 3480853 := bbase (se 6 (by rfl) ⟨81582, by rfl⟩ : syracuseStep 3480853 = 163165) (by norm_num)
theorem B4641137 : Blo 2061435 4641137 := bstep (se 2 (by rfl) ⟨1740426, by rfl⟩ : syracuseStep 4641137 = 3480853) B3480853
theorem B3094091 : Blo 2061435 3094091 := bstep (se 1 (by rfl) ⟨2320568, by rfl⟩ : syracuseStep 3094091 = 4641137) B4641137
theorem B2062727 : Blo 2061435 2062727 := bstep (se 1 (by rfl) ⟨1547045, by rfl⟩ : syracuseStep 2062727 = 3094091) B3094091
theorem B2320573 : Blo 2061435 2320573 := bbase (se 3 (by rfl) ⟨435107, by rfl⟩ : syracuseStep 2320573 = 870215) (by norm_num)
theorem B3094097 : Blo 2061435 3094097 := bstep (se 2 (by rfl) ⟨1160286, by rfl⟩ : syracuseStep 3094097 = 2320573) B2320573
theorem B2062731 : Blo 2061435 2062731 := bstep (se 1 (by rfl) ⟨1547048, by rfl⟩ : syracuseStep 2062731 = 3094097) B3094097
theorem B6961733 : Blo 2061435 6961733 := bbase (se 4 (by rfl) ⟨652662, by rfl⟩ : syracuseStep 6961733 = 1305325) (by norm_num)
theorem B4641155 : Blo 2061435 4641155 := bstep (se 1 (by rfl) ⟨3480866, by rfl⟩ : syracuseStep 4641155 = 6961733) B6961733
theorem B3094103 : Blo 2061435 3094103 := bstep (se 1 (by rfl) ⟨2320577, by rfl⟩ : syracuseStep 3094103 = 4641155) B4641155
theorem B2062735 : Blo 2061435 2062735 := bstep (se 1 (by rfl) ⟨1547051, by rfl⟩ : syracuseStep 2062735 = 3094103) B3094103
theorem B3094109 : Blo 2061435 3094109 := bbase (se 3 (by rfl) ⟨580145, by rfl⟩ : syracuseStep 3094109 = 1160291) (by norm_num)
theorem B2062739 : Blo 2061435 2062739 := bstep (se 1 (by rfl) ⟨1547054, by rfl⟩ : syracuseStep 2062739 = 3094109) B3094109
theorem B4641173 : Blo 2061435 4641173 := bbase (se 6 (by rfl) ⟨108777, by rfl⟩ : syracuseStep 4641173 = 217555) (by norm_num)
theorem B3094115 : Blo 2061435 3094115 := bstep (se 1 (by rfl) ⟨2320586, by rfl⟩ : syracuseStep 3094115 = 4641173) B4641173
theorem B2062743 : Blo 2061435 2062743 := bstep (se 1 (by rfl) ⟨1547057, by rfl⟩ : syracuseStep 2062743 = 3094115) B3094115
theorem B4526533 : Blo 2061435 4526533 := bbase (se 4 (by rfl) ⟨424362, by rfl⟩ : syracuseStep 4526533 = 848725) (by norm_num)
theorem B24141509 : Blo 2061435 24141509 := bstep (se 4 (by rfl) ⟨2263266, by rfl⟩ : syracuseStep 24141509 = 4526533) B4526533
theorem B16094339 : Blo 2061435 16094339 := bstep (se 1 (by rfl) ⟨12070754, by rfl⟩ : syracuseStep 16094339 = 24141509) B24141509
theorem B10729559 : Blo 2061435 10729559 := bstep (se 1 (by rfl) ⟨8047169, by rfl⟩ : syracuseStep 10729559 = 16094339) B16094339
theorem B7153039 : Blo 2061435 7153039 := bstep (se 1 (by rfl) ⟨5364779, by rfl⟩ : syracuseStep 7153039 = 10729559) B10729559
theorem B38149541 : Blo 2061435 38149541 := bstep (se 4 (by rfl) ⟨3576519, by rfl⟩ : syracuseStep 38149541 = 7153039) B7153039
theorem B25433027 : Blo 2061435 25433027 := bstep (se 1 (by rfl) ⟨19074770, by rfl⟩ : syracuseStep 25433027 = 38149541) B38149541
theorem B16955351 : Blo 2061435 16955351 := bstep (se 1 (by rfl) ⟨12716513, by rfl⟩ : syracuseStep 16955351 = 25433027) B25433027
theorem B11303567 : Blo 2061435 11303567 := bstep (se 1 (by rfl) ⟨8477675, by rfl⟩ : syracuseStep 11303567 = 16955351) B16955351
theorem B7535711 : Blo 2061435 7535711 := bstep (se 1 (by rfl) ⟨5651783, by rfl⟩ : syracuseStep 7535711 = 11303567) B11303567
theorem B20095229 : Blo 2061435 20095229 := bstep (se 3 (by rfl) ⟨3767855, by rfl⟩ : syracuseStep 20095229 = 7535711) B7535711
theorem B53587277 : Blo 2061435 53587277 := bstep (se 3 (by rfl) ⟨10047614, by rfl⟩ : syracuseStep 53587277 = 20095229) B20095229
theorem B35724851 : Blo 2061435 35724851 := bstep (se 1 (by rfl) ⟨26793638, by rfl⟩ : syracuseStep 35724851 = 53587277) B53587277
theorem B23816567 : Blo 2061435 23816567 := bstep (se 1 (by rfl) ⟨17862425, by rfl⟩ : syracuseStep 23816567 = 35724851) B35724851
theorem B15877711 : Blo 2061435 15877711 := bstep (se 1 (by rfl) ⟨11908283, by rfl⟩ : syracuseStep 15877711 = 23816567) B23816567
theorem B21170281 : Blo 2061435 21170281 := bstep (se 2 (by rfl) ⟨7938855, by rfl⟩ : syracuseStep 21170281 = 15877711) B15877711
theorem B28227041 : Blo 2061435 28227041 := bstep (se 2 (by rfl) ⟨10585140, by rfl⟩ : syracuseStep 28227041 = 21170281) B21170281
theorem B18818027 : Blo 2061435 18818027 := bstep (se 1 (by rfl) ⟨14113520, by rfl⟩ : syracuseStep 18818027 = 28227041) B28227041
theorem B12545351 : Blo 2061435 12545351 := bstep (se 1 (by rfl) ⟨9409013, by rfl⟩ : syracuseStep 12545351 = 18818027) B18818027
theorem B8363567 : Blo 2061435 8363567 := bstep (se 1 (by rfl) ⟨6272675, by rfl⟩ : syracuseStep 8363567 = 12545351) B12545351
theorem B5575711 : Blo 2061435 5575711 := bstep (se 1 (by rfl) ⟨4181783, by rfl⟩ : syracuseStep 5575711 = 8363567) B8363567
theorem B7434281 : Blo 2061435 7434281 := bstep (se 2 (by rfl) ⟨2787855, by rfl⟩ : syracuseStep 7434281 = 5575711) B5575711
theorem B4956187 : Blo 2061435 4956187 := bstep (se 1 (by rfl) ⟨3717140, by rfl⟩ : syracuseStep 4956187 = 7434281) B7434281
theorem B6608249 : Blo 2061435 6608249 := bstep (se 2 (by rfl) ⟨2478093, by rfl⟩ : syracuseStep 6608249 = 4956187) B4956187
theorem B4405499 : Blo 2061435 4405499 := bstep (se 1 (by rfl) ⟨3304124, by rfl⟩ : syracuseStep 4405499 = 6608249) B6608249
theorem B2936999 : Blo 2061435 2936999 := bstep (se 1 (by rfl) ⟨2202749, by rfl⟩ : syracuseStep 2936999 = 4405499) B4405499
theorem B7831997 : Blo 2061435 7831997 := bstep (se 3 (by rfl) ⟨1468499, by rfl⟩ : syracuseStep 7831997 = 2936999) B2936999
theorem B5221331 : Blo 2061435 5221331 := bstep (se 1 (by rfl) ⟨3915998, by rfl⟩ : syracuseStep 5221331 = 7831997) B7831997
theorem B3480887 : Blo 2061435 3480887 := bstep (se 1 (by rfl) ⟨2610665, by rfl⟩ : syracuseStep 3480887 = 5221331) B5221331
theorem B2320591 : Blo 2061435 2320591 := bstep (se 1 (by rfl) ⟨1740443, by rfl⟩ : syracuseStep 2320591 = 3480887) B3480887
theorem B3094121 : Blo 2061435 3094121 := bstep (se 2 (by rfl) ⟨1160295, by rfl⟩ : syracuseStep 3094121 = 2320591) B2320591
theorem B2062747 : Blo 2061435 2062747 := bstep (se 1 (by rfl) ⟨1547060, by rfl⟩ : syracuseStep 2062747 = 3094121) B3094121
theorem B8811013 : Blo 2061435 8811013 := bbase (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) (by norm_num)
theorem B11748017 : Blo 2061435 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B7832011 : Blo 2061435 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B10442681 : Blo 2061435 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B6961787 : Blo 2061435 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B4641191 : Blo 2061435 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B3094127 : Blo 2061435 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B2062751 : Blo 2061435 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B3094133 : Blo 2061435 3094133 := bbase (se 5 (by rfl) ⟨145037, by rfl⟩ : syracuseStep 3094133 = 290075) (by norm_num)
theorem B2062755 : Blo 2061435 2062755 := bstep (se 1 (by rfl) ⟨1547066, by rfl⟩ : syracuseStep 2062755 = 3094133) B3094133
theorem B3916021 : Blo 2061435 3916021 := bbase (se 5 (by rfl) ⟨183563, by rfl⟩ : syracuseStep 3916021 = 367127) (by norm_num)
theorem B5221361 : Blo 2061435 5221361 := bstep (se 2 (by rfl) ⟨1958010, by rfl⟩ : syracuseStep 5221361 = 3916021) B3916021
theorem B3480907 : Blo 2061435 3480907 := bstep (se 1 (by rfl) ⟨2610680, by rfl⟩ : syracuseStep 3480907 = 5221361) B5221361
theorem B4641209 : Blo 2061435 4641209 := bstep (se 2 (by rfl) ⟨1740453, by rfl⟩ : syracuseStep 4641209 = 3480907) B3480907
theorem B3094139 : Blo 2061435 3094139 := bstep (se 1 (by rfl) ⟨2320604, by rfl⟩ : syracuseStep 3094139 = 4641209) B4641209
theorem B2062759 : Blo 2061435 2062759 := bstep (se 1 (by rfl) ⟨1547069, by rfl⟩ : syracuseStep 2062759 = 3094139) B3094139
theorem B2320609 : Blo 2061435 2320609 := bbase (se 2 (by rfl) ⟨870228, by rfl⟩ : syracuseStep 2320609 = 1740457) (by norm_num)
theorem B3094145 : Blo 2061435 3094145 := bstep (se 2 (by rfl) ⟨1160304, by rfl⟩ : syracuseStep 3094145 = 2320609) B2320609
theorem B2062763 : Blo 2061435 2062763 := bstep (se 1 (by rfl) ⟨1547072, by rfl⟩ : syracuseStep 2062763 = 3094145) B3094145
theorem B5221381 : Blo 2061435 5221381 := bbase (se 4 (by rfl) ⟨489504, by rfl⟩ : syracuseStep 5221381 = 979009) (by norm_num)
theorem B6961841 : Blo 2061435 6961841 := bstep (se 2 (by rfl) ⟨2610690, by rfl⟩ : syracuseStep 6961841 = 5221381) B5221381
theorem B4641227 : Blo 2061435 4641227 := bstep (se 1 (by rfl) ⟨3480920, by rfl⟩ : syracuseStep 4641227 = 6961841) B6961841
theorem B3094151 : Blo 2061435 3094151 := bstep (se 1 (by rfl) ⟨2320613, by rfl⟩ : syracuseStep 3094151 = 4641227) B4641227
theorem B2062767 : Blo 2061435 2062767 := bstep (se 1 (by rfl) ⟨1547075, by rfl⟩ : syracuseStep 2062767 = 3094151) B3094151
theorem B3094157 : Blo 2061435 3094157 := bbase (se 3 (by rfl) ⟨580154, by rfl⟩ : syracuseStep 3094157 = 1160309) (by norm_num)
theorem B2062771 : Blo 2061435 2062771 := bstep (se 1 (by rfl) ⟨1547078, by rfl⟩ : syracuseStep 2062771 = 3094157) B3094157
theorem B4641245 : Blo 2061435 4641245 := bbase (se 3 (by rfl) ⟨870233, by rfl⟩ : syracuseStep 4641245 = 1740467) (by norm_num)
theorem B3094163 : Blo 2061435 3094163 := bstep (se 1 (by rfl) ⟨2320622, by rfl⟩ : syracuseStep 3094163 = 4641245) B4641245
theorem B2062775 : Blo 2061435 2062775 := bstep (se 1 (by rfl) ⟨1547081, by rfl⟩ : syracuseStep 2062775 = 3094163) B3094163
theorem B3480941 : Blo 2061435 3480941 := bbase (se 3 (by rfl) ⟨652676, by rfl⟩ : syracuseStep 3480941 = 1305353) (by norm_num)
theorem B2320627 : Blo 2061435 2320627 := bstep (se 1 (by rfl) ⟨1740470, by rfl⟩ : syracuseStep 2320627 = 3480941) B3480941
theorem B3094169 : Blo 2061435 3094169 := bstep (se 2 (by rfl) ⟨1160313, by rfl⟩ : syracuseStep 3094169 = 2320627) B2320627
theorem B2062779 : Blo 2061435 2062779 := bstep (se 1 (by rfl) ⟨1547084, by rfl⟩ : syracuseStep 2062779 = 3094169) B3094169
theorem B3394957 : Blo 2061435 3394957 := bbase (se 3 (by rfl) ⟨636554, by rfl⟩ : syracuseStep 3394957 = 1273109) (by norm_num)
theorem B4526609 : Blo 2061435 4526609 := bstep (se 2 (by rfl) ⟨1697478, by rfl⟩ : syracuseStep 4526609 = 3394957) B3394957
theorem B12070957 : Blo 2061435 12070957 := bstep (se 3 (by rfl) ⟨2263304, by rfl⟩ : syracuseStep 12070957 = 4526609) B4526609
theorem B16094609 : Blo 2061435 16094609 := bstep (se 2 (by rfl) ⟨6035478, by rfl⟩ : syracuseStep 16094609 = 12070957) B12070957
theorem B10729739 : Blo 2061435 10729739 := bstep (se 1 (by rfl) ⟨8047304, by rfl⟩ : syracuseStep 10729739 = 16094609) B16094609
theorem B7153159 : Blo 2061435 7153159 := bstep (se 1 (by rfl) ⟨5364869, by rfl⟩ : syracuseStep 7153159 = 10729739) B10729739
theorem B9537545 : Blo 2061435 9537545 := bstep (se 2 (by rfl) ⟨3576579, by rfl⟩ : syracuseStep 9537545 = 7153159) B7153159
theorem B25433453 : Blo 2061435 25433453 := bstep (se 3 (by rfl) ⟨4768772, by rfl⟩ : syracuseStep 25433453 = 9537545) B9537545
theorem B67822541 : Blo 2061435 67822541 := bstep (se 3 (by rfl) ⟨12716726, by rfl⟩ : syracuseStep 67822541 = 25433453) B25433453
theorem B45215027 : Blo 2061435 45215027 := bstep (se 1 (by rfl) ⟨33911270, by rfl⟩ : syracuseStep 45215027 = 67822541) B67822541
theorem B30143351 : Blo 2061435 30143351 := bstep (se 1 (by rfl) ⟨22607513, by rfl⟩ : syracuseStep 30143351 = 45215027) B45215027
theorem B80382269 : Blo 2061435 80382269 := bstep (se 3 (by rfl) ⟨15071675, by rfl⟩ : syracuseStep 80382269 = 30143351) B30143351
theorem B53588179 : Blo 2061435 53588179 := bstep (se 1 (by rfl) ⟨40191134, by rfl⟩ : syracuseStep 53588179 = 80382269) B80382269
theorem B71450905 : Blo 2061435 71450905 := bstep (se 2 (by rfl) ⟨26794089, by rfl⟩ : syracuseStep 71450905 = 53588179) B53588179
theorem B95267873 : Blo 2061435 95267873 := bstep (se 2 (by rfl) ⟨35725452, by rfl⟩ : syracuseStep 95267873 = 71450905) B71450905
theorem B254047661 : Blo 2061435 254047661 := bstep (se 3 (by rfl) ⟨47633936, by rfl⟩ : syracuseStep 254047661 = 95267873) B95267873
theorem B169365107 : Blo 2061435 169365107 := bstep (se 1 (by rfl) ⟨127023830, by rfl⟩ : syracuseStep 169365107 = 254047661) B254047661
theorem B112910071 : Blo 2061435 112910071 := bstep (se 1 (by rfl) ⟨84682553, by rfl⟩ : syracuseStep 112910071 = 169365107) B169365107
theorem B150546761 : Blo 2061435 150546761 := bstep (se 2 (by rfl) ⟨56455035, by rfl⟩ : syracuseStep 150546761 = 112910071) B112910071
theorem B100364507 : Blo 2061435 100364507 := bstep (se 1 (by rfl) ⟨75273380, by rfl⟩ : syracuseStep 100364507 = 150546761) B150546761
theorem B66909671 : Blo 2061435 66909671 := bstep (se 1 (by rfl) ⟨50182253, by rfl⟩ : syracuseStep 66909671 = 100364507) B100364507
theorem B44606447 : Blo 2061435 44606447 := bstep (se 1 (by rfl) ⟨33454835, by rfl⟩ : syracuseStep 44606447 = 66909671) B66909671
theorem B29737631 : Blo 2061435 29737631 := bstep (se 1 (by rfl) ⟨22303223, by rfl⟩ : syracuseStep 29737631 = 44606447) B44606447
theorem B19825087 : Blo 2061435 19825087 := bstep (se 1 (by rfl) ⟨14868815, by rfl⟩ : syracuseStep 19825087 = 29737631) B29737631
theorem B26433449 : Blo 2061435 26433449 := bstep (se 2 (by rfl) ⟨9912543, by rfl⟩ : syracuseStep 26433449 = 19825087) B19825087
theorem B17622299 : Blo 2061435 17622299 := bstep (se 1 (by rfl) ⟨13216724, by rfl⟩ : syracuseStep 17622299 = 26433449) B26433449
theorem B11748199 : Blo 2061435 11748199 := bstep (se 1 (by rfl) ⟨8811149, by rfl⟩ : syracuseStep 11748199 = 17622299) B17622299
theorem B15664265 : Blo 2061435 15664265 := bstep (se 2 (by rfl) ⟨5874099, by rfl⟩ : syracuseStep 15664265 = 11748199) B11748199
theorem B10442843 : Blo 2061435 10442843 := bstep (se 1 (by rfl) ⟨7832132, by rfl⟩ : syracuseStep 10442843 = 15664265) B15664265
theorem B6961895 : Blo 2061435 6961895 := bstep (se 1 (by rfl) ⟨5221421, by rfl⟩ : syracuseStep 6961895 = 10442843) B10442843
theorem B4641263 : Blo 2061435 4641263 := bstep (se 1 (by rfl) ⟨3480947, by rfl⟩ : syracuseStep 4641263 = 6961895) B6961895
theorem B3094175 : Blo 2061435 3094175 := bstep (se 1 (by rfl) ⟨2320631, by rfl⟩ : syracuseStep 3094175 = 4641263) B4641263
theorem B2062783 : Blo 2061435 2062783 := bstep (se 1 (by rfl) ⟨1547087, by rfl⟩ : syracuseStep 2062783 = 3094175) B3094175
theorem B3094181 : Blo 2061435 3094181 := bbase (se 4 (by rfl) ⟨290079, by rfl⟩ : syracuseStep 3094181 = 580159) (by norm_num)
theorem B2062787 : Blo 2061435 2062787 := bstep (se 1 (by rfl) ⟨1547090, by rfl⟩ : syracuseStep 2062787 = 3094181) B3094181
theorem B2610721 : Blo 2061435 2610721 := bbase (se 2 (by rfl) ⟨979020, by rfl⟩ : syracuseStep 2610721 = 1958041) (by norm_num)
theorem B3480961 : Blo 2061435 3480961 := bstep (se 2 (by rfl) ⟨1305360, by rfl⟩ : syracuseStep 3480961 = 2610721) B2610721
theorem B4641281 : Blo 2061435 4641281 := bstep (se 2 (by rfl) ⟨1740480, by rfl⟩ : syracuseStep 4641281 = 3480961) B3480961
theorem B3094187 : Blo 2061435 3094187 := bstep (se 1 (by rfl) ⟨2320640, by rfl⟩ : syracuseStep 3094187 = 4641281) B4641281
theorem B2062791 : Blo 2061435 2062791 := bstep (se 1 (by rfl) ⟨1547093, by rfl⟩ : syracuseStep 2062791 = 3094187) B3094187
theorem B2320645 : Blo 2061435 2320645 := bbase (se 4 (by rfl) ⟨217560, by rfl⟩ : syracuseStep 2320645 = 435121) (by norm_num)
theorem B3094193 : Blo 2061435 3094193 := bstep (se 2 (by rfl) ⟨1160322, by rfl⟩ : syracuseStep 3094193 = 2320645) B2320645
theorem B2062795 : Blo 2061435 2062795 := bstep (se 1 (by rfl) ⟨1547096, by rfl⟩ : syracuseStep 2062795 = 3094193) B3094193
theorem B2202805 : Blo 2061435 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B2937073 : Blo 2061435 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B3916097 : Blo 2061435 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B2610731 : Blo 2061435 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B6961949 : Blo 2061435 6961949 := bstep (se 3 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 6961949 = 2610731) B2610731
theorem B4641299 : Blo 2061435 4641299 := bstep (se 1 (by rfl) ⟨3480974, by rfl⟩ : syracuseStep 4641299 = 6961949) B6961949
theorem B3094199 : Blo 2061435 3094199 := bstep (se 1 (by rfl) ⟨2320649, by rfl⟩ : syracuseStep 3094199 = 4641299) B4641299
theorem B2062799 : Blo 2061435 2062799 := bstep (se 1 (by rfl) ⟨1547099, by rfl⟩ : syracuseStep 2062799 = 3094199) B3094199
theorem B3094205 : Blo 2061435 3094205 := bbase (se 3 (by rfl) ⟨580163, by rfl⟩ : syracuseStep 3094205 = 1160327) (by norm_num)
theorem B2062803 : Blo 2061435 2062803 := bstep (se 1 (by rfl) ⟨1547102, by rfl⟩ : syracuseStep 2062803 = 3094205) B3094205
theorem B4641317 : Blo 2061435 4641317 := bbase (se 4 (by rfl) ⟨435123, by rfl⟩ : syracuseStep 4641317 = 870247) (by norm_num)
theorem B3094211 : Blo 2061435 3094211 := bstep (se 1 (by rfl) ⟨2320658, by rfl⟩ : syracuseStep 3094211 = 4641317) B4641317
theorem B2062807 : Blo 2061435 2062807 := bstep (se 1 (by rfl) ⟨1547105, by rfl⟩ : syracuseStep 2062807 = 3094211) B3094211
theorem B5221493 : Blo 2061435 5221493 := bbase (se 5 (by rfl) ⟨244757, by rfl⟩ : syracuseStep 5221493 = 489515) (by norm_num)
theorem B3480995 : Blo 2061435 3480995 := bstep (se 1 (by rfl) ⟨2610746, by rfl⟩ : syracuseStep 3480995 = 5221493) B5221493
theorem B2320663 : Blo 2061435 2320663 := bstep (se 1 (by rfl) ⟨1740497, by rfl⟩ : syracuseStep 2320663 = 3480995) B3480995
theorem B3094217 : Blo 2061435 3094217 := bstep (se 2 (by rfl) ⟨1160331, by rfl⟩ : syracuseStep 3094217 = 2320663) B2320663
theorem B2062811 : Blo 2061435 2062811 := bstep (se 1 (by rfl) ⟨1547108, by rfl⟩ : syracuseStep 2062811 = 3094217) B3094217
theorem B19825397 : Blo 2061435 19825397 := bbase (se 5 (by rfl) ⟨929315, by rfl⟩ : syracuseStep 19825397 = 1858631) (by norm_num)
theorem B13216931 : Blo 2061435 13216931 := bstep (se 1 (by rfl) ⟨9912698, by rfl⟩ : syracuseStep 13216931 = 19825397) B19825397
theorem B8811287 : Blo 2061435 8811287 := bstep (se 1 (by rfl) ⟨6608465, by rfl⟩ : syracuseStep 8811287 = 13216931) B13216931
theorem B5874191 : Blo 2061435 5874191 := bstep (se 1 (by rfl) ⟨4405643, by rfl⟩ : syracuseStep 5874191 = 8811287) B8811287
theorem B3916127 : Blo 2061435 3916127 := bstep (se 1 (by rfl) ⟨2937095, by rfl⟩ : syracuseStep 3916127 = 5874191) B5874191
theorem B10443005 : Blo 2061435 10443005 := bstep (se 3 (by rfl) ⟨1958063, by rfl⟩ : syracuseStep 10443005 = 3916127) B3916127
theorem B6962003 : Blo 2061435 6962003 := bstep (se 1 (by rfl) ⟨5221502, by rfl⟩ : syracuseStep 6962003 = 10443005) B10443005
theorem B4641335 : Blo 2061435 4641335 := bstep (se 1 (by rfl) ⟨3481001, by rfl⟩ : syracuseStep 4641335 = 6962003) B6962003
theorem B3094223 : Blo 2061435 3094223 := bstep (se 1 (by rfl) ⟨2320667, by rfl⟩ : syracuseStep 3094223 = 4641335) B4641335
theorem B2062815 : Blo 2061435 2062815 := bstep (se 1 (by rfl) ⟨1547111, by rfl⟩ : syracuseStep 2062815 = 3094223) B3094223
theorem B3094229 : Blo 2061435 3094229 := bbase (se 7 (by rfl) ⟨36260, by rfl⟩ : syracuseStep 3094229 = 72521) (by norm_num)
theorem B2062819 : Blo 2061435 2062819 := bstep (se 1 (by rfl) ⟨1547114, by rfl⟩ : syracuseStep 2062819 = 3094229) B3094229
theorem B4405661 : Blo 2061435 4405661 := bbase (se 3 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 4405661 = 1652123) (by norm_num)
theorem B2937107 : Blo 2061435 2937107 := bstep (se 1 (by rfl) ⟨2202830, by rfl⟩ : syracuseStep 2937107 = 4405661) B4405661
theorem B7832285 : Blo 2061435 7832285 := bstep (se 3 (by rfl) ⟨1468553, by rfl⟩ : syracuseStep 7832285 = 2937107) B2937107
theorem B5221523 : Blo 2061435 5221523 := bstep (se 1 (by rfl) ⟨3916142, by rfl⟩ : syracuseStep 5221523 = 7832285) B7832285
theorem B3481015 : Blo 2061435 3481015 := bstep (se 1 (by rfl) ⟨2610761, by rfl⟩ : syracuseStep 3481015 = 5221523) B5221523
theorem B4641353 : Blo 2061435 4641353 := bstep (se 2 (by rfl) ⟨1740507, by rfl⟩ : syracuseStep 4641353 = 3481015) B3481015
theorem B3094235 : Blo 2061435 3094235 := bstep (se 1 (by rfl) ⟨2320676, by rfl⟩ : syracuseStep 3094235 = 4641353) B4641353
theorem B2062823 : Blo 2061435 2062823 := bstep (se 1 (by rfl) ⟨1547117, by rfl⟩ : syracuseStep 2062823 = 3094235) B3094235
theorem B2320681 : Blo 2061435 2320681 := bbase (se 2 (by rfl) ⟨870255, by rfl⟩ : syracuseStep 2320681 = 1740511) (by norm_num)
theorem B3094241 : Blo 2061435 3094241 := bstep (se 2 (by rfl) ⟨1160340, by rfl⟩ : syracuseStep 3094241 = 2320681) B2320681
theorem B2062827 : Blo 2061435 2062827 := bstep (se 1 (by rfl) ⟨1547120, by rfl⟩ : syracuseStep 2062827 = 3094241) B3094241
theorem B7057045 : Blo 2061435 7057045 := bbase (se 6 (by rfl) ⟨165399, by rfl⟩ : syracuseStep 7057045 = 330799) (by norm_num)
theorem B9409393 : Blo 2061435 9409393 := bstep (se 2 (by rfl) ⟨3528522, by rfl⟩ : syracuseStep 9409393 = 7057045) B7057045
theorem B12545857 : Blo 2061435 12545857 := bstep (se 2 (by rfl) ⟨4704696, by rfl⟩ : syracuseStep 12545857 = 9409393) B9409393
theorem B16727809 : Blo 2061435 16727809 := bstep (se 2 (by rfl) ⟨6272928, by rfl⟩ : syracuseStep 16727809 = 12545857) B12545857
theorem B22303745 : Blo 2061435 22303745 := bstep (se 2 (by rfl) ⟨8363904, by rfl⟩ : syracuseStep 22303745 = 16727809) B16727809
theorem B14869163 : Blo 2061435 14869163 := bstep (se 1 (by rfl) ⟨11151872, by rfl⟩ : syracuseStep 14869163 = 22303745) B22303745
theorem B9912775 : Blo 2061435 9912775 := bstep (se 1 (by rfl) ⟨7434581, by rfl⟩ : syracuseStep 9912775 = 14869163) B14869163
theorem B13217033 : Blo 2061435 13217033 := bstep (se 2 (by rfl) ⟨4956387, by rfl⟩ : syracuseStep 13217033 = 9912775) B9912775
theorem B8811355 : Blo 2061435 8811355 := bstep (se 1 (by rfl) ⟨6608516, by rfl⟩ : syracuseStep 8811355 = 13217033) B13217033
theorem B11748473 : Blo 2061435 11748473 := bstep (se 2 (by rfl) ⟨4405677, by rfl⟩ : syracuseStep 11748473 = 8811355) B8811355
theorem B7832315 : Blo 2061435 7832315 := bstep (se 1 (by rfl) ⟨5874236, by rfl⟩ : syracuseStep 7832315 = 11748473) B11748473
theorem B5221543 : Blo 2061435 5221543 := bstep (se 1 (by rfl) ⟨3916157, by rfl⟩ : syracuseStep 5221543 = 7832315) B7832315
theorem B6962057 : Blo 2061435 6962057 := bstep (se 2 (by rfl) ⟨2610771, by rfl⟩ : syracuseStep 6962057 = 5221543) B5221543
theorem B4641371 : Blo 2061435 4641371 := bstep (se 1 (by rfl) ⟨3481028, by rfl⟩ : syracuseStep 4641371 = 6962057) B6962057
theorem B3094247 : Blo 2061435 3094247 := bstep (se 1 (by rfl) ⟨2320685, by rfl⟩ : syracuseStep 3094247 = 4641371) B4641371
theorem B2062831 : Blo 2061435 2062831 := bstep (se 1 (by rfl) ⟨1547123, by rfl⟩ : syracuseStep 2062831 = 3094247) B3094247
theorem B3094253 : Blo 2061435 3094253 := bbase (se 3 (by rfl) ⟨580172, by rfl⟩ : syracuseStep 3094253 = 1160345) (by norm_num)
theorem B2062835 : Blo 2061435 2062835 := bstep (se 1 (by rfl) ⟨1547126, by rfl⟩ : syracuseStep 2062835 = 3094253) B3094253
theorem B4641389 : Blo 2061435 4641389 := bbase (se 3 (by rfl) ⟨870260, by rfl⟩ : syracuseStep 4641389 = 1740521) (by norm_num)
theorem B3094259 : Blo 2061435 3094259 := bstep (se 1 (by rfl) ⟨2320694, by rfl⟩ : syracuseStep 3094259 = 4641389) B4641389
theorem B2062839 : Blo 2061435 2062839 := bstep (se 1 (by rfl) ⟨1547129, by rfl⟩ : syracuseStep 2062839 = 3094259) B3094259
theorem B3916181 : Blo 2061435 3916181 := bbase (se 6 (by rfl) ⟨91785, by rfl⟩ : syracuseStep 3916181 = 183571) (by norm_num)
theorem B2610787 : Blo 2061435 2610787 := bstep (se 1 (by rfl) ⟨1958090, by rfl⟩ : syracuseStep 2610787 = 3916181) B3916181
theorem B3481049 : Blo 2061435 3481049 := bstep (se 2 (by rfl) ⟨1305393, by rfl⟩ : syracuseStep 3481049 = 2610787) B2610787
theorem B2320699 : Blo 2061435 2320699 := bstep (se 1 (by rfl) ⟨1740524, by rfl⟩ : syracuseStep 2320699 = 3481049) B3481049
theorem B3094265 : Blo 2061435 3094265 := bstep (se 2 (by rfl) ⟨1160349, by rfl⟩ : syracuseStep 3094265 = 2320699) B2320699
theorem B2062843 : Blo 2061435 2062843 := bstep (se 1 (by rfl) ⟨1547132, by rfl⟩ : syracuseStep 2062843 = 3094265) B3094265
theorem B44607829 : Blo 2061435 44607829 := bbase (se 10 (by rfl) ⟨65343, by rfl⟩ : syracuseStep 44607829 = 130687) (by norm_num)
theorem B59477105 : Blo 2061435 59477105 := bstep (se 2 (by rfl) ⟨22303914, by rfl⟩ : syracuseStep 59477105 = 44607829) B44607829
theorem B39651403 : Blo 2061435 39651403 := bstep (se 1 (by rfl) ⟨29738552, by rfl⟩ : syracuseStep 39651403 = 59477105) B59477105
theorem B52868537 : Blo 2061435 52868537 := bstep (se 2 (by rfl) ⟨19825701, by rfl⟩ : syracuseStep 52868537 = 39651403) B39651403
theorem B35245691 : Blo 2061435 35245691 := bstep (se 1 (by rfl) ⟨26434268, by rfl⟩ : syracuseStep 35245691 = 52868537) B52868537
theorem B23497127 : Blo 2061435 23497127 := bstep (se 1 (by rfl) ⟨17622845, by rfl⟩ : syracuseStep 23497127 = 35245691) B35245691
theorem B15664751 : Blo 2061435 15664751 := bstep (se 1 (by rfl) ⟨11748563, by rfl⟩ : syracuseStep 15664751 = 23497127) B23497127
theorem B10443167 : Blo 2061435 10443167 := bstep (se 1 (by rfl) ⟨7832375, by rfl⟩ : syracuseStep 10443167 = 15664751) B15664751
theorem B6962111 : Blo 2061435 6962111 := bstep (se 1 (by rfl) ⟨5221583, by rfl⟩ : syracuseStep 6962111 = 10443167) B10443167
theorem B4641407 : Blo 2061435 4641407 := bstep (se 1 (by rfl) ⟨3481055, by rfl⟩ : syracuseStep 4641407 = 6962111) B6962111
theorem B3094271 : Blo 2061435 3094271 := bstep (se 1 (by rfl) ⟨2320703, by rfl⟩ : syracuseStep 3094271 = 4641407) B4641407
theorem B2062847 : Blo 2061435 2062847 := bstep (se 1 (by rfl) ⟨1547135, by rfl⟩ : syracuseStep 2062847 = 3094271) B3094271
theorem B3094277 : Blo 2061435 3094277 := bbase (se 4 (by rfl) ⟨290088, by rfl⟩ : syracuseStep 3094277 = 580177) (by norm_num)
theorem B2062851 : Blo 2061435 2062851 := bstep (se 1 (by rfl) ⟨1547138, by rfl⟩ : syracuseStep 2062851 = 3094277) B3094277
theorem B3481069 : Blo 2061435 3481069 := bbase (se 3 (by rfl) ⟨652700, by rfl⟩ : syracuseStep 3481069 = 1305401) (by norm_num)
theorem B4641425 : Blo 2061435 4641425 := bstep (se 2 (by rfl) ⟨1740534, by rfl⟩ : syracuseStep 4641425 = 3481069) B3481069
theorem B3094283 : Blo 2061435 3094283 := bstep (se 1 (by rfl) ⟨2320712, by rfl⟩ : syracuseStep 3094283 = 4641425) B4641425
theorem B2062855 : Blo 2061435 2062855 := bstep (se 1 (by rfl) ⟨1547141, by rfl⟩ : syracuseStep 2062855 = 3094283) B3094283
theorem B2320717 : Blo 2061435 2320717 := bbase (se 3 (by rfl) ⟨435134, by rfl⟩ : syracuseStep 2320717 = 870269) (by norm_num)
theorem B3094289 : Blo 2061435 3094289 := bstep (se 2 (by rfl) ⟨1160358, by rfl⟩ : syracuseStep 3094289 = 2320717) B2320717
theorem B2062859 : Blo 2061435 2062859 := bstep (se 1 (by rfl) ⟨1547144, by rfl⟩ : syracuseStep 2062859 = 3094289) B3094289
theorem B6962165 : Blo 2061435 6962165 := bbase (se 5 (by rfl) ⟨326351, by rfl⟩ : syracuseStep 6962165 = 652703) (by norm_num)
theorem B4641443 : Blo 2061435 4641443 := bstep (se 1 (by rfl) ⟨3481082, by rfl⟩ : syracuseStep 4641443 = 6962165) B6962165
theorem B3094295 : Blo 2061435 3094295 := bstep (se 1 (by rfl) ⟨2320721, by rfl⟩ : syracuseStep 3094295 = 4641443) B4641443
theorem B2062863 : Blo 2061435 2062863 := bstep (se 1 (by rfl) ⟨1547147, by rfl⟩ : syracuseStep 2062863 = 3094295) B3094295
theorem B3094301 : Blo 2061435 3094301 := bbase (se 3 (by rfl) ⟨580181, by rfl⟩ : syracuseStep 3094301 = 1160363) (by norm_num)
theorem B2062867 : Blo 2061435 2062867 := bstep (se 1 (by rfl) ⟨1547150, by rfl⟩ : syracuseStep 2062867 = 3094301) B3094301
theorem B4641461 : Blo 2061435 4641461 := bbase (se 5 (by rfl) ⟨217568, by rfl⟩ : syracuseStep 4641461 = 435137) (by norm_num)
theorem B3094307 : Blo 2061435 3094307 := bstep (se 1 (by rfl) ⟨2320730, by rfl⟩ : syracuseStep 3094307 = 4641461) B4641461
theorem B2062871 : Blo 2061435 2062871 := bstep (se 1 (by rfl) ⟨1547153, by rfl⟩ : syracuseStep 2062871 = 3094307) B3094307
theorem B11748725 : Blo 2061435 11748725 := bbase (se 5 (by rfl) ⟨550721, by rfl⟩ : syracuseStep 11748725 = 1101443) (by norm_num)
theorem B7832483 : Blo 2061435 7832483 := bstep (se 1 (by rfl) ⟨5874362, by rfl⟩ : syracuseStep 7832483 = 11748725) B11748725
theorem B5221655 : Blo 2061435 5221655 := bstep (se 1 (by rfl) ⟨3916241, by rfl⟩ : syracuseStep 5221655 = 7832483) B7832483
theorem B3481103 : Blo 2061435 3481103 := bstep (se 1 (by rfl) ⟨2610827, by rfl⟩ : syracuseStep 3481103 = 5221655) B5221655
theorem B2320735 : Blo 2061435 2320735 := bstep (se 1 (by rfl) ⟨1740551, by rfl⟩ : syracuseStep 2320735 = 3481103) B3481103
theorem B3094313 : Blo 2061435 3094313 := bstep (se 2 (by rfl) ⟨1160367, by rfl⟩ : syracuseStep 3094313 = 2320735) B2320735
theorem B2062875 : Blo 2061435 2062875 := bstep (se 1 (by rfl) ⟨1547156, by rfl⟩ : syracuseStep 2062875 = 3094313) B3094313
theorem B5874373 : Blo 2061435 5874373 := bbase (se 4 (by rfl) ⟨550722, by rfl⟩ : syracuseStep 5874373 = 1101445) (by norm_num)
theorem B7832497 : Blo 2061435 7832497 := bstep (se 2 (by rfl) ⟨2937186, by rfl⟩ : syracuseStep 7832497 = 5874373) B5874373
theorem B10443329 : Blo 2061435 10443329 := bstep (se 2 (by rfl) ⟨3916248, by rfl⟩ : syracuseStep 10443329 = 7832497) B7832497
theorem B6962219 : Blo 2061435 6962219 := bstep (se 1 (by rfl) ⟨5221664, by rfl⟩ : syracuseStep 6962219 = 10443329) B10443329
theorem B4641479 : Blo 2061435 4641479 := bstep (se 1 (by rfl) ⟨3481109, by rfl⟩ : syracuseStep 4641479 = 6962219) B6962219
theorem B3094319 : Blo 2061435 3094319 := bstep (se 1 (by rfl) ⟨2320739, by rfl⟩ : syracuseStep 3094319 = 4641479) B4641479
theorem B2062879 : Blo 2061435 2062879 := bstep (se 1 (by rfl) ⟨1547159, by rfl⟩ : syracuseStep 2062879 = 3094319) B3094319
theorem B3094325 : Blo 2061435 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B2062883 : Blo 2061435 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B5221685 : Blo 2061435 5221685 := bbase (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) (by norm_num)
theorem B3481123 : Blo 2061435 3481123 := bstep (se 1 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 3481123 = 5221685) B5221685
theorem B4641497 : Blo 2061435 4641497 := bstep (se 2 (by rfl) ⟨1740561, by rfl⟩ : syracuseStep 4641497 = 3481123) B3481123
theorem B3094331 : Blo 2061435 3094331 := bstep (se 1 (by rfl) ⟨2320748, by rfl⟩ : syracuseStep 3094331 = 4641497) B4641497
theorem B2062887 : Blo 2061435 2062887 := bstep (se 1 (by rfl) ⟨1547165, by rfl⟩ : syracuseStep 2062887 = 3094331) B3094331
theorem B2320753 : Blo 2061435 2320753 := bbase (se 2 (by rfl) ⟨870282, by rfl⟩ : syracuseStep 2320753 = 1740565) (by norm_num)
theorem B3094337 : Blo 2061435 3094337 := bstep (se 2 (by rfl) ⟨1160376, by rfl⟩ : syracuseStep 3094337 = 2320753) B2320753
theorem B2062891 : Blo 2061435 2062891 := bstep (se 1 (by rfl) ⟨1547168, by rfl⟩ : syracuseStep 2062891 = 3094337) B3094337
theorem B2977285 : Blo 2061435 2977285 := bbase (se 4 (by rfl) ⟨279120, by rfl⟩ : syracuseStep 2977285 = 558241) (by norm_num)
theorem B3969713 : Blo 2061435 3969713 := bstep (se 2 (by rfl) ⟨1488642, by rfl⟩ : syracuseStep 3969713 = 2977285) B2977285
theorem B2646475 : Blo 2061435 2646475 := bstep (se 1 (by rfl) ⟨1984856, by rfl⟩ : syracuseStep 2646475 = 3969713) B3969713
theorem B14114533 : Blo 2061435 14114533 := bstep (se 4 (by rfl) ⟨1323237, by rfl⟩ : syracuseStep 14114533 = 2646475) B2646475
theorem B18819377 : Blo 2061435 18819377 := bstep (se 2 (by rfl) ⟨7057266, by rfl⟩ : syracuseStep 18819377 = 14114533) B14114533
theorem B12546251 : Blo 2061435 12546251 := bstep (se 1 (by rfl) ⟨9409688, by rfl⟩ : syracuseStep 12546251 = 18819377) B18819377
theorem B8364167 : Blo 2061435 8364167 := bstep (se 1 (by rfl) ⟨6273125, by rfl⟩ : syracuseStep 8364167 = 12546251) B12546251
theorem B5576111 : Blo 2061435 5576111 := bstep (se 1 (by rfl) ⟨4182083, by rfl⟩ : syracuseStep 5576111 = 8364167) B8364167
theorem B3717407 : Blo 2061435 3717407 := bstep (se 1 (by rfl) ⟨2788055, by rfl⟩ : syracuseStep 3717407 = 5576111) B5576111
theorem B2478271 : Blo 2061435 2478271 := bstep (se 1 (by rfl) ⟨1858703, by rfl⟩ : syracuseStep 2478271 = 3717407) B3717407
theorem B3304361 : Blo 2061435 3304361 := bstep (se 2 (by rfl) ⟨1239135, by rfl⟩ : syracuseStep 3304361 = 2478271) B2478271
theorem B8811629 : Blo 2061435 8811629 := bstep (se 3 (by rfl) ⟨1652180, by rfl⟩ : syracuseStep 8811629 = 3304361) B3304361
theorem B5874419 : Blo 2061435 5874419 := bstep (se 1 (by rfl) ⟨4405814, by rfl⟩ : syracuseStep 5874419 = 8811629) B8811629
theorem B3916279 : Blo 2061435 3916279 := bstep (se 1 (by rfl) ⟨2937209, by rfl⟩ : syracuseStep 3916279 = 5874419) B5874419
theorem B5221705 : Blo 2061435 5221705 := bstep (se 2 (by rfl) ⟨1958139, by rfl⟩ : syracuseStep 5221705 = 3916279) B3916279
theorem B6962273 : Blo 2061435 6962273 := bstep (se 2 (by rfl) ⟨2610852, by rfl⟩ : syracuseStep 6962273 = 5221705) B5221705
theorem B4641515 : Blo 2061435 4641515 := bstep (se 1 (by rfl) ⟨3481136, by rfl⟩ : syracuseStep 4641515 = 6962273) B6962273
theorem B3094343 : Blo 2061435 3094343 := bstep (se 1 (by rfl) ⟨2320757, by rfl⟩ : syracuseStep 3094343 = 4641515) B4641515
theorem B2062895 : Blo 2061435 2062895 := bstep (se 1 (by rfl) ⟨1547171, by rfl⟩ : syracuseStep 2062895 = 3094343) B3094343
theorem B3094349 : Blo 2061435 3094349 := bbase (se 3 (by rfl) ⟨580190, by rfl⟩ : syracuseStep 3094349 = 1160381) (by norm_num)
theorem B2062899 : Blo 2061435 2062899 := bstep (se 1 (by rfl) ⟨1547174, by rfl⟩ : syracuseStep 2062899 = 3094349) B3094349
theorem B4641533 : Blo 2061435 4641533 := bbase (se 3 (by rfl) ⟨870287, by rfl⟩ : syracuseStep 4641533 = 1740575) (by norm_num)
theorem B3094355 : Blo 2061435 3094355 := bstep (se 1 (by rfl) ⟨2320766, by rfl⟩ : syracuseStep 3094355 = 4641533) B4641533
theorem B2062903 : Blo 2061435 2062903 := bstep (se 1 (by rfl) ⟨1547177, by rfl⟩ : syracuseStep 2062903 = 3094355) B3094355
theorem B3481157 : Blo 2061435 3481157 := bbase (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) (by norm_num)
theorem B2320771 : Blo 2061435 2320771 := bstep (se 1 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 2320771 = 3481157) B3481157
theorem B3094361 : Blo 2061435 3094361 := bstep (se 2 (by rfl) ⟨1160385, by rfl⟩ : syracuseStep 3094361 = 2320771) B2320771
theorem B2062907 : Blo 2061435 2062907 := bstep (se 1 (by rfl) ⟨1547180, by rfl⟩ : syracuseStep 2062907 = 3094361) B3094361
theorem B15665237 : Blo 2061435 15665237 := bbase (se 8 (by rfl) ⟨91788, by rfl⟩ : syracuseStep 15665237 = 183577) (by norm_num)
theorem B10443491 : Blo 2061435 10443491 := bstep (se 1 (by rfl) ⟨7832618, by rfl⟩ : syracuseStep 10443491 = 15665237) B15665237
theorem B6962327 : Blo 2061435 6962327 := bstep (se 1 (by rfl) ⟨5221745, by rfl⟩ : syracuseStep 6962327 = 10443491) B10443491
theorem B4641551 : Blo 2061435 4641551 := bstep (se 1 (by rfl) ⟨3481163, by rfl⟩ : syracuseStep 4641551 = 6962327) B6962327
theorem B3094367 : Blo 2061435 3094367 := bstep (se 1 (by rfl) ⟨2320775, by rfl⟩ : syracuseStep 3094367 = 4641551) B4641551
theorem B2062911 : Blo 2061435 2062911 := bstep (se 1 (by rfl) ⟨1547183, by rfl⟩ : syracuseStep 2062911 = 3094367) B3094367
theorem B3094373 : Blo 2061435 3094373 := bbase (se 4 (by rfl) ⟨290097, by rfl⟩ : syracuseStep 3094373 = 580195) (by norm_num)
theorem B2062915 : Blo 2061435 2062915 := bstep (se 1 (by rfl) ⟨1547186, by rfl⟩ : syracuseStep 2062915 = 3094373) B3094373
theorem B3916325 : Blo 2061435 3916325 := bbase (se 4 (by rfl) ⟨367155, by rfl⟩ : syracuseStep 3916325 = 734311) (by norm_num)
theorem B2610883 : Blo 2061435 2610883 := bstep (se 1 (by rfl) ⟨1958162, by rfl⟩ : syracuseStep 2610883 = 3916325) B3916325
theorem B3481177 : Blo 2061435 3481177 := bstep (se 2 (by rfl) ⟨1305441, by rfl⟩ : syracuseStep 3481177 = 2610883) B2610883
theorem B4641569 : Blo 2061435 4641569 := bstep (se 2 (by rfl) ⟨1740588, by rfl⟩ : syracuseStep 4641569 = 3481177) B3481177
theorem B3094379 : Blo 2061435 3094379 := bstep (se 1 (by rfl) ⟨2320784, by rfl⟩ : syracuseStep 3094379 = 4641569) B4641569
theorem B2062919 : Blo 2061435 2062919 := bstep (se 1 (by rfl) ⟨1547189, by rfl⟩ : syracuseStep 2062919 = 3094379) B3094379
theorem B2320789 : Blo 2061435 2320789 := bbase (se 6 (by rfl) ⟨54393, by rfl⟩ : syracuseStep 2320789 = 108787) (by norm_num)
theorem B3094385 : Blo 2061435 3094385 := bstep (se 2 (by rfl) ⟨1160394, by rfl⟩ : syracuseStep 3094385 = 2320789) B2320789
theorem B2062923 : Blo 2061435 2062923 := bstep (se 1 (by rfl) ⟨1547192, by rfl⟩ : syracuseStep 2062923 = 3094385) B3094385
theorem B2610893 : Blo 2061435 2610893 := bbase (se 3 (by rfl) ⟨489542, by rfl⟩ : syracuseStep 2610893 = 979085) (by norm_num)
theorem B6962381 : Blo 2061435 6962381 := bstep (se 3 (by rfl) ⟨1305446, by rfl⟩ : syracuseStep 6962381 = 2610893) B2610893
theorem B4641587 : Blo 2061435 4641587 := bstep (se 1 (by rfl) ⟨3481190, by rfl⟩ : syracuseStep 4641587 = 6962381) B6962381
theorem B3094391 : Blo 2061435 3094391 := bstep (se 1 (by rfl) ⟨2320793, by rfl⟩ : syracuseStep 3094391 = 4641587) B4641587
theorem B2062927 : Blo 2061435 2062927 := bstep (se 1 (by rfl) ⟨1547195, by rfl⟩ : syracuseStep 2062927 = 3094391) B3094391
theorem B3094397 : Blo 2061435 3094397 := bbase (se 3 (by rfl) ⟨580199, by rfl⟩ : syracuseStep 3094397 = 1160399) (by norm_num)
theorem B2062931 : Blo 2061435 2062931 := bstep (se 1 (by rfl) ⟨1547198, by rfl⟩ : syracuseStep 2062931 = 3094397) B3094397
theorem B4641605 : Blo 2061435 4641605 := bbase (se 4 (by rfl) ⟨435150, by rfl⟩ : syracuseStep 4641605 = 870301) (by norm_num)
theorem B3094403 : Blo 2061435 3094403 := bstep (se 1 (by rfl) ⟨2320802, by rfl⟩ : syracuseStep 3094403 = 4641605) B4641605
theorem B2062935 : Blo 2061435 2062935 := bstep (se 1 (by rfl) ⟨1547201, by rfl⟩ : syracuseStep 2062935 = 3094403) B3094403
theorem B4405909 : Blo 2061435 4405909 := bbase (se 6 (by rfl) ⟨103263, by rfl⟩ : syracuseStep 4405909 = 206527) (by norm_num)
theorem B5874545 : Blo 2061435 5874545 := bstep (se 2 (by rfl) ⟨2202954, by rfl⟩ : syracuseStep 5874545 = 4405909) B4405909
theorem B3916363 : Blo 2061435 3916363 := bstep (se 1 (by rfl) ⟨2937272, by rfl⟩ : syracuseStep 3916363 = 5874545) B5874545
theorem B5221817 : Blo 2061435 5221817 := bstep (se 2 (by rfl) ⟨1958181, by rfl⟩ : syracuseStep 5221817 = 3916363) B3916363
theorem B3481211 : Blo 2061435 3481211 := bstep (se 1 (by rfl) ⟨2610908, by rfl⟩ : syracuseStep 3481211 = 5221817) B5221817
theorem B2320807 : Blo 2061435 2320807 := bstep (se 1 (by rfl) ⟨1740605, by rfl⟩ : syracuseStep 2320807 = 3481211) B3481211
theorem B3094409 : Blo 2061435 3094409 := bstep (se 2 (by rfl) ⟨1160403, by rfl⟩ : syracuseStep 3094409 = 2320807) B2320807
theorem B2062939 : Blo 2061435 2062939 := bstep (se 1 (by rfl) ⟨1547204, by rfl⟩ : syracuseStep 2062939 = 3094409) B3094409
theorem B10443653 : Blo 2061435 10443653 := bbase (se 4 (by rfl) ⟨979092, by rfl⟩ : syracuseStep 10443653 = 1958185) (by norm_num)
theorem B6962435 : Blo 2061435 6962435 := bstep (se 1 (by rfl) ⟨5221826, by rfl⟩ : syracuseStep 6962435 = 10443653) B10443653
theorem B4641623 : Blo 2061435 4641623 := bstep (se 1 (by rfl) ⟨3481217, by rfl⟩ : syracuseStep 4641623 = 6962435) B6962435
theorem B3094415 : Blo 2061435 3094415 := bstep (se 1 (by rfl) ⟨2320811, by rfl⟩ : syracuseStep 3094415 = 4641623) B4641623
theorem B2062943 : Blo 2061435 2062943 := bstep (se 1 (by rfl) ⟨1547207, by rfl⟩ : syracuseStep 2062943 = 3094415) B3094415
theorem B3094421 : Blo 2061435 3094421 := bbase (se 6 (by rfl) ⟨72525, by rfl⟩ : syracuseStep 3094421 = 145051) (by norm_num)
theorem B2062947 : Blo 2061435 2062947 := bstep (se 1 (by rfl) ⟨1547210, by rfl⟩ : syracuseStep 2062947 = 3094421) B3094421
theorem B4956677 : Blo 2061435 4956677 := bbase (se 4 (by rfl) ⟨464688, by rfl⟩ : syracuseStep 4956677 = 929377) (by norm_num)
theorem B3304451 : Blo 2061435 3304451 := bstep (se 1 (by rfl) ⟨2478338, by rfl⟩ : syracuseStep 3304451 = 4956677) B4956677
theorem B2202967 : Blo 2061435 2202967 := bstep (se 1 (by rfl) ⟨1652225, by rfl⟩ : syracuseStep 2202967 = 3304451) B3304451
theorem B11749157 : Blo 2061435 11749157 := bstep (se 4 (by rfl) ⟨1101483, by rfl⟩ : syracuseStep 11749157 = 2202967) B2202967
theorem B7832771 : Blo 2061435 7832771 := bstep (se 1 (by rfl) ⟨5874578, by rfl⟩ : syracuseStep 7832771 = 11749157) B11749157
theorem B5221847 : Blo 2061435 5221847 := bstep (se 1 (by rfl) ⟨3916385, by rfl⟩ : syracuseStep 5221847 = 7832771) B7832771
theorem B3481231 : Blo 2061435 3481231 := bstep (se 1 (by rfl) ⟨2610923, by rfl⟩ : syracuseStep 3481231 = 5221847) B5221847
theorem B4641641 : Blo 2061435 4641641 := bstep (se 2 (by rfl) ⟨1740615, by rfl⟩ : syracuseStep 4641641 = 3481231) B3481231
theorem B3094427 : Blo 2061435 3094427 := bstep (se 1 (by rfl) ⟨2320820, by rfl⟩ : syracuseStep 3094427 = 4641641) B4641641
theorem B2062951 : Blo 2061435 2062951 := bstep (se 1 (by rfl) ⟨1547213, by rfl⟩ : syracuseStep 2062951 = 3094427) B3094427
theorem B2320825 : Blo 2061435 2320825 := bbase (se 2 (by rfl) ⟨870309, by rfl⟩ : syracuseStep 2320825 = 1740619) (by norm_num)
theorem B3094433 : Blo 2061435 3094433 := bstep (se 2 (by rfl) ⟨1160412, by rfl⟩ : syracuseStep 3094433 = 2320825) B2320825
theorem B2062955 : Blo 2061435 2062955 := bstep (se 1 (by rfl) ⟨1547216, by rfl⟩ : syracuseStep 2062955 = 3094433) B3094433
theorem B7939669 : Blo 2061435 7939669 := bbase (se 8 (by rfl) ⟨46521, by rfl⟩ : syracuseStep 7939669 = 93043) (by norm_num)
theorem B10586225 : Blo 2061435 10586225 := bstep (se 2 (by rfl) ⟨3969834, by rfl⟩ : syracuseStep 10586225 = 7939669) B7939669
theorem B28229933 : Blo 2061435 28229933 := bstep (se 3 (by rfl) ⟨5293112, by rfl⟩ : syracuseStep 28229933 = 10586225) B10586225
theorem B18819955 : Blo 2061435 18819955 := bstep (se 1 (by rfl) ⟨14114966, by rfl⟩ : syracuseStep 18819955 = 28229933) B28229933
theorem B25093273 : Blo 2061435 25093273 := bstep (se 2 (by rfl) ⟨9409977, by rfl⟩ : syracuseStep 25093273 = 18819955) B18819955
theorem B33457697 : Blo 2061435 33457697 := bstep (se 2 (by rfl) ⟨12546636, by rfl⟩ : syracuseStep 33457697 = 25093273) B25093273
theorem B22305131 : Blo 2061435 22305131 := bstep (se 1 (by rfl) ⟨16728848, by rfl⟩ : syracuseStep 22305131 = 33457697) B33457697
theorem B14870087 : Blo 2061435 14870087 := bstep (se 1 (by rfl) ⟨11152565, by rfl⟩ : syracuseStep 14870087 = 22305131) B22305131
theorem B9913391 : Blo 2061435 9913391 := bstep (se 1 (by rfl) ⟨7435043, by rfl⟩ : syracuseStep 9913391 = 14870087) B14870087
theorem B6608927 : Blo 2061435 6608927 := bstep (se 1 (by rfl) ⟨4956695, by rfl⟩ : syracuseStep 6608927 = 9913391) B9913391
theorem B4405951 : Blo 2061435 4405951 := bstep (se 1 (by rfl) ⟨3304463, by rfl⟩ : syracuseStep 4405951 = 6608927) B6608927
theorem B5874601 : Blo 2061435 5874601 := bstep (se 2 (by rfl) ⟨2202975, by rfl⟩ : syracuseStep 5874601 = 4405951) B4405951
theorem B7832801 : Blo 2061435 7832801 := bstep (se 2 (by rfl) ⟨2937300, by rfl⟩ : syracuseStep 7832801 = 5874601) B5874601
theorem B5221867 : Blo 2061435 5221867 := bstep (se 1 (by rfl) ⟨3916400, by rfl⟩ : syracuseStep 5221867 = 7832801) B7832801
theorem B6962489 : Blo 2061435 6962489 := bstep (se 2 (by rfl) ⟨2610933, by rfl⟩ : syracuseStep 6962489 = 5221867) B5221867
theorem B4641659 : Blo 2061435 4641659 := bstep (se 1 (by rfl) ⟨3481244, by rfl⟩ : syracuseStep 4641659 = 6962489) B6962489
theorem B3094439 : Blo 2061435 3094439 := bstep (se 1 (by rfl) ⟨2320829, by rfl⟩ : syracuseStep 3094439 = 4641659) B4641659
theorem B2062959 : Blo 2061435 2062959 := bstep (se 1 (by rfl) ⟨1547219, by rfl⟩ : syracuseStep 2062959 = 3094439) B3094439
theorem B3094445 : Blo 2061435 3094445 := bbase (se 3 (by rfl) ⟨580208, by rfl⟩ : syracuseStep 3094445 = 1160417) (by norm_num)
theorem B2062963 : Blo 2061435 2062963 := bstep (se 1 (by rfl) ⟨1547222, by rfl⟩ : syracuseStep 2062963 = 3094445) B3094445
theorem B4641677 : Blo 2061435 4641677 := bbase (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) (by norm_num)
theorem B3094451 : Blo 2061435 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B2062967 : Blo 2061435 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B2610949 : Blo 2061435 2610949 := bbase (se 4 (by rfl) ⟨244776, by rfl⟩ : syracuseStep 2610949 = 489553) (by norm_num)
theorem B3481265 : Blo 2061435 3481265 := bstep (se 2 (by rfl) ⟨1305474, by rfl⟩ : syracuseStep 3481265 = 2610949) B2610949
theorem B2320843 : Blo 2061435 2320843 := bstep (se 1 (by rfl) ⟨1740632, by rfl⟩ : syracuseStep 2320843 = 3481265) B3481265
theorem B3094457 : Blo 2061435 3094457 := bstep (se 2 (by rfl) ⟨1160421, by rfl⟩ : syracuseStep 3094457 = 2320843) B2320843
theorem B2062971 : Blo 2061435 2062971 := bstep (se 1 (by rfl) ⟨1547228, by rfl⟩ : syracuseStep 2062971 = 3094457) B3094457
theorem B4956733 : Blo 2061435 4956733 := bbase (se 3 (by rfl) ⟨929387, by rfl⟩ : syracuseStep 4956733 = 1858775) (by norm_num)
theorem B26435909 : Blo 2061435 26435909 := bstep (se 4 (by rfl) ⟨2478366, by rfl⟩ : syracuseStep 26435909 = 4956733) B4956733
theorem B17623939 : Blo 2061435 17623939 := bstep (se 1 (by rfl) ⟨13217954, by rfl⟩ : syracuseStep 17623939 = 26435909) B26435909
theorem B23498585 : Blo 2061435 23498585 := bstep (se 2 (by rfl) ⟨8811969, by rfl⟩ : syracuseStep 23498585 = 17623939) B17623939
theorem B15665723 : Blo 2061435 15665723 := bstep (se 1 (by rfl) ⟨11749292, by rfl⟩ : syracuseStep 15665723 = 23498585) B23498585
theorem B10443815 : Blo 2061435 10443815 := bstep (se 1 (by rfl) ⟨7832861, by rfl⟩ : syracuseStep 10443815 = 15665723) B15665723
theorem B6962543 : Blo 2061435 6962543 := bstep (se 1 (by rfl) ⟨5221907, by rfl⟩ : syracuseStep 6962543 = 10443815) B10443815
theorem B4641695 : Blo 2061435 4641695 := bstep (se 1 (by rfl) ⟨3481271, by rfl⟩ : syracuseStep 4641695 = 6962543) B6962543
theorem B3094463 : Blo 2061435 3094463 := bstep (se 1 (by rfl) ⟨2320847, by rfl⟩ : syracuseStep 3094463 = 4641695) B4641695
theorem B2062975 : Blo 2061435 2062975 := bstep (se 1 (by rfl) ⟨1547231, by rfl⟩ : syracuseStep 2062975 = 3094463) B3094463
theorem B3094469 : Blo 2061435 3094469 := bbase (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) (by norm_num)
theorem B2062979 : Blo 2061435 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B3481285 : Blo 2061435 3481285 := bbase (se 4 (by rfl) ⟨326370, by rfl⟩ : syracuseStep 3481285 = 652741) (by norm_num)
theorem B4641713 : Blo 2061435 4641713 := bstep (se 2 (by rfl) ⟨1740642, by rfl⟩ : syracuseStep 4641713 = 3481285) B3481285
theorem B3094475 : Blo 2061435 3094475 := bstep (se 1 (by rfl) ⟨2320856, by rfl⟩ : syracuseStep 3094475 = 4641713) B4641713
theorem B2062983 : Blo 2061435 2062983 := bstep (se 1 (by rfl) ⟨1547237, by rfl⟩ : syracuseStep 2062983 = 3094475) B3094475
theorem B2320861 : Blo 2061435 2320861 := bbase (se 3 (by rfl) ⟨435161, by rfl⟩ : syracuseStep 2320861 = 870323) (by norm_num)
theorem B3094481 : Blo 2061435 3094481 := bstep (se 2 (by rfl) ⟨1160430, by rfl⟩ : syracuseStep 3094481 = 2320861) B2320861
theorem B2062987 : Blo 2061435 2062987 := bstep (se 1 (by rfl) ⟨1547240, by rfl⟩ : syracuseStep 2062987 = 3094481) B3094481
theorem B6962597 : Blo 2061435 6962597 := bbase (se 4 (by rfl) ⟨652743, by rfl⟩ : syracuseStep 6962597 = 1305487) (by norm_num)
theorem B4641731 : Blo 2061435 4641731 := bstep (se 1 (by rfl) ⟨3481298, by rfl⟩ : syracuseStep 4641731 = 6962597) B6962597
theorem B3094487 : Blo 2061435 3094487 := bstep (se 1 (by rfl) ⟨2320865, by rfl⟩ : syracuseStep 3094487 = 4641731) B4641731
theorem B2062991 : Blo 2061435 2062991 := bstep (se 1 (by rfl) ⟨1547243, by rfl⟩ : syracuseStep 2062991 = 3094487) B3094487
theorem B3094493 : Blo 2061435 3094493 := bbase (se 3 (by rfl) ⟨580217, by rfl⟩ : syracuseStep 3094493 = 1160435) (by norm_num)
theorem B2062995 : Blo 2061435 2062995 := bstep (se 1 (by rfl) ⟨1547246, by rfl⟩ : syracuseStep 2062995 = 3094493) B3094493
theorem B4641749 : Blo 2061435 4641749 := bbase (se 7 (by rfl) ⟨54395, by rfl⟩ : syracuseStep 4641749 = 108791) (by norm_num)
theorem B3094499 : Blo 2061435 3094499 := bstep (se 1 (by rfl) ⟨2320874, by rfl⟩ : syracuseStep 3094499 = 4641749) B4641749
theorem B2062999 : Blo 2061435 2062999 := bstep (se 1 (by rfl) ⟨1547249, by rfl⟩ : syracuseStep 2062999 = 3094499) B3094499
theorem B7057637 : Blo 2061435 7057637 := bbase (se 4 (by rfl) ⟨661653, by rfl⟩ : syracuseStep 7057637 = 1323307) (by norm_num)
theorem B4705091 : Blo 2061435 4705091 := bstep (se 1 (by rfl) ⟨3528818, by rfl⟩ : syracuseStep 4705091 = 7057637) B7057637
theorem B3136727 : Blo 2061435 3136727 := bstep (se 1 (by rfl) ⟨2352545, by rfl⟩ : syracuseStep 3136727 = 4705091) B4705091
theorem B2091151 : Blo 2061435 2091151 := bstep (se 1 (by rfl) ⟨1568363, by rfl⟩ : syracuseStep 2091151 = 3136727) B3136727
theorem B2788201 : Blo 2061435 2788201 := bstep (se 2 (by rfl) ⟨1045575, by rfl⟩ : syracuseStep 2788201 = 2091151) B2091151
theorem B14870405 : Blo 2061435 14870405 := bstep (se 4 (by rfl) ⟨1394100, by rfl⟩ : syracuseStep 14870405 = 2788201) B2788201
theorem B9913603 : Blo 2061435 9913603 := bstep (se 1 (by rfl) ⟨7435202, by rfl⟩ : syracuseStep 9913603 = 14870405) B14870405
theorem B13218137 : Blo 2061435 13218137 := bstep (se 2 (by rfl) ⟨4956801, by rfl⟩ : syracuseStep 13218137 = 9913603) B9913603
theorem B8812091 : Blo 2061435 8812091 := bstep (se 1 (by rfl) ⟨6609068, by rfl⟩ : syracuseStep 8812091 = 13218137) B13218137
theorem B5874727 : Blo 2061435 5874727 := bstep (se 1 (by rfl) ⟨4406045, by rfl⟩ : syracuseStep 5874727 = 8812091) B8812091
theorem B7832969 : Blo 2061435 7832969 := bstep (se 2 (by rfl) ⟨2937363, by rfl⟩ : syracuseStep 7832969 = 5874727) B5874727
theorem B5221979 : Blo 2061435 5221979 := bstep (se 1 (by rfl) ⟨3916484, by rfl⟩ : syracuseStep 5221979 = 7832969) B7832969
theorem B3481319 : Blo 2061435 3481319 := bstep (se 1 (by rfl) ⟨2610989, by rfl⟩ : syracuseStep 3481319 = 5221979) B5221979
theorem B2320879 : Blo 2061435 2320879 := bstep (se 1 (by rfl) ⟨1740659, by rfl⟩ : syracuseStep 2320879 = 3481319) B3481319
theorem B3094505 : Blo 2061435 3094505 := bstep (se 2 (by rfl) ⟨1160439, by rfl⟩ : syracuseStep 3094505 = 2320879) B2320879
theorem B2063003 : Blo 2061435 2063003 := bstep (se 1 (by rfl) ⟨1547252, by rfl⟩ : syracuseStep 2063003 = 3094505) B3094505
theorem B17624213 : Blo 2061435 17624213 := bbase (se 6 (by rfl) ⟨413067, by rfl⟩ : syracuseStep 17624213 = 826135) (by norm_num)
theorem B11749475 : Blo 2061435 11749475 := bstep (se 1 (by rfl) ⟨8812106, by rfl⟩ : syracuseStep 11749475 = 17624213) B17624213
theorem B7832983 : Blo 2061435 7832983 := bstep (se 1 (by rfl) ⟨5874737, by rfl⟩ : syracuseStep 7832983 = 11749475) B11749475
theorem B10443977 : Blo 2061435 10443977 := bstep (se 2 (by rfl) ⟨3916491, by rfl⟩ : syracuseStep 10443977 = 7832983) B7832983
theorem B6962651 : Blo 2061435 6962651 := bstep (se 1 (by rfl) ⟨5221988, by rfl⟩ : syracuseStep 6962651 = 10443977) B10443977
theorem B4641767 : Blo 2061435 4641767 := bstep (se 1 (by rfl) ⟨3481325, by rfl⟩ : syracuseStep 4641767 = 6962651) B6962651
theorem B3094511 : Blo 2061435 3094511 := bstep (se 1 (by rfl) ⟨2320883, by rfl⟩ : syracuseStep 3094511 = 4641767) B4641767
theorem B2063007 : Blo 2061435 2063007 := bstep (se 1 (by rfl) ⟨1547255, by rfl⟩ : syracuseStep 2063007 = 3094511) B3094511
theorem B3094517 : Blo 2061435 3094517 := bbase (se 5 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 3094517 = 290111) (by norm_num)
theorem B2063011 : Blo 2061435 2063011 := bstep (se 1 (by rfl) ⟨1547258, by rfl⟩ : syracuseStep 2063011 = 3094517) B3094517
theorem B5954917 : Blo 2061435 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B7939889 : Blo 2061435 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B5293259 : Blo 2061435 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B3528839 : Blo 2061435 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B2352559 : Blo 2061435 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B3136745 : Blo 2061435 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B8364653 : Blo 2061435 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B5576435 : Blo 2061435 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B3717623 : Blo 2061435 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B9913661 : Blo 2061435 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B6609107 : Blo 2061435 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B4406071 : Blo 2061435 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B5874761 : Blo 2061435 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B3916507 : Blo 2061435 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B5222009 : Blo 2061435 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B3481339 : Blo 2061435 3481339 := bstep (se 1 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 3481339 = 5222009) B5222009
theorem B4641785 : Blo 2061435 4641785 := bstep (se 2 (by rfl) ⟨1740669, by rfl⟩ : syracuseStep 4641785 = 3481339) B3481339
theorem B3094523 : Blo 2061435 3094523 := bstep (se 1 (by rfl) ⟨2320892, by rfl⟩ : syracuseStep 3094523 = 4641785) B4641785
theorem B2063015 : Blo 2061435 2063015 := bstep (se 1 (by rfl) ⟨1547261, by rfl⟩ : syracuseStep 2063015 = 3094523) B3094523
theorem B2320897 : Blo 2061435 2320897 := bbase (se 2 (by rfl) ⟨870336, by rfl⟩ : syracuseStep 2320897 = 1740673) (by norm_num)
theorem B3094529 : Blo 2061435 3094529 := bstep (se 2 (by rfl) ⟨1160448, by rfl⟩ : syracuseStep 3094529 = 2320897) B2320897
theorem B2063019 : Blo 2061435 2063019 := bstep (se 1 (by rfl) ⟨1547264, by rfl⟩ : syracuseStep 2063019 = 3094529) B3094529
theorem B5222029 : Blo 2061435 5222029 := bbase (se 3 (by rfl) ⟨979130, by rfl⟩ : syracuseStep 5222029 = 1958261) (by norm_num)
theorem B6962705 : Blo 2061435 6962705 := bstep (se 2 (by rfl) ⟨2611014, by rfl⟩ : syracuseStep 6962705 = 5222029) B5222029
theorem B4641803 : Blo 2061435 4641803 := bstep (se 1 (by rfl) ⟨3481352, by rfl⟩ : syracuseStep 4641803 = 6962705) B6962705
theorem B3094535 : Blo 2061435 3094535 := bstep (se 1 (by rfl) ⟨2320901, by rfl⟩ : syracuseStep 3094535 = 4641803) B4641803
theorem B2063023 : Blo 2061435 2063023 := bstep (se 1 (by rfl) ⟨1547267, by rfl⟩ : syracuseStep 2063023 = 3094535) B3094535
theorem B3094541 : Blo 2061435 3094541 := bbase (se 3 (by rfl) ⟨580226, by rfl⟩ : syracuseStep 3094541 = 1160453) (by norm_num)
theorem B2063027 : Blo 2061435 2063027 := bstep (se 1 (by rfl) ⟨1547270, by rfl⟩ : syracuseStep 2063027 = 3094541) B3094541
theorem B4641821 : Blo 2061435 4641821 := bbase (se 3 (by rfl) ⟨870341, by rfl⟩ : syracuseStep 4641821 = 1740683) (by norm_num)
theorem B3094547 : Blo 2061435 3094547 := bstep (se 1 (by rfl) ⟨2320910, by rfl⟩ : syracuseStep 3094547 = 4641821) B4641821
theorem B2063031 : Blo 2061435 2063031 := bstep (se 1 (by rfl) ⟨1547273, by rfl⟩ : syracuseStep 2063031 = 3094547) B3094547
theorem B3481373 : Blo 2061435 3481373 := bbase (se 3 (by rfl) ⟨652757, by rfl⟩ : syracuseStep 3481373 = 1305515) (by norm_num)
theorem B2320915 : Blo 2061435 2320915 := bstep (se 1 (by rfl) ⟨1740686, by rfl⟩ : syracuseStep 2320915 = 3481373) B3481373
theorem B3094553 : Blo 2061435 3094553 := bstep (se 2 (by rfl) ⟨1160457, by rfl⟩ : syracuseStep 3094553 = 2320915) B2320915
theorem B2063035 : Blo 2061435 2063035 := bstep (se 1 (by rfl) ⟨1547276, by rfl⟩ : syracuseStep 2063035 = 3094553) B3094553
theorem B3136781 : Blo 2061435 3136781 := bbase (se 3 (by rfl) ⟨588146, by rfl⟩ : syracuseStep 3136781 = 1176293) (by norm_num)
theorem B2091187 : Blo 2061435 2091187 := bstep (se 1 (by rfl) ⟨1568390, by rfl⟩ : syracuseStep 2091187 = 3136781) B3136781
theorem B11152997 : Blo 2061435 11152997 := bstep (se 4 (by rfl) ⟨1045593, by rfl⟩ : syracuseStep 11152997 = 2091187) B2091187
theorem B7435331 : Blo 2061435 7435331 := bstep (se 1 (by rfl) ⟨5576498, by rfl⟩ : syracuseStep 7435331 = 11152997) B11152997
theorem B4956887 : Blo 2061435 4956887 := bstep (se 1 (by rfl) ⟨3717665, by rfl⟩ : syracuseStep 4956887 = 7435331) B7435331
theorem B13218365 : Blo 2061435 13218365 := bstep (se 3 (by rfl) ⟨2478443, by rfl⟩ : syracuseStep 13218365 = 4956887) B4956887
theorem B8812243 : Blo 2061435 8812243 := bstep (se 1 (by rfl) ⟨6609182, by rfl⟩ : syracuseStep 8812243 = 13218365) B13218365
theorem B11749657 : Blo 2061435 11749657 := bstep (se 2 (by rfl) ⟨4406121, by rfl⟩ : syracuseStep 11749657 = 8812243) B8812243
theorem B15666209 : Blo 2061435 15666209 := bstep (se 2 (by rfl) ⟨5874828, by rfl⟩ : syracuseStep 15666209 = 11749657) B11749657
theorem B10444139 : Blo 2061435 10444139 := bstep (se 1 (by rfl) ⟨7833104, by rfl⟩ : syracuseStep 10444139 = 15666209) B15666209
theorem B6962759 : Blo 2061435 6962759 := bstep (se 1 (by rfl) ⟨5222069, by rfl⟩ : syracuseStep 6962759 = 10444139) B10444139
theorem B4641839 : Blo 2061435 4641839 := bstep (se 1 (by rfl) ⟨3481379, by rfl⟩ : syracuseStep 4641839 = 6962759) B6962759
theorem B3094559 : Blo 2061435 3094559 := bstep (se 1 (by rfl) ⟨2320919, by rfl⟩ : syracuseStep 3094559 = 4641839) B4641839
theorem B2063039 : Blo 2061435 2063039 := bstep (se 1 (by rfl) ⟨1547279, by rfl⟩ : syracuseStep 2063039 = 3094559) B3094559
theorem B3094565 : Blo 2061435 3094565 := bbase (se 4 (by rfl) ⟨290115, by rfl⟩ : syracuseStep 3094565 = 580231) (by norm_num)
theorem B2063043 : Blo 2061435 2063043 := bstep (se 1 (by rfl) ⟨1547282, by rfl⟩ : syracuseStep 2063043 = 3094565) B3094565
theorem B2611045 : Blo 2061435 2611045 := bbase (se 4 (by rfl) ⟨244785, by rfl⟩ : syracuseStep 2611045 = 489571) (by norm_num)
theorem B3481393 : Blo 2061435 3481393 := bstep (se 2 (by rfl) ⟨1305522, by rfl⟩ : syracuseStep 3481393 = 2611045) B2611045
theorem B4641857 : Blo 2061435 4641857 := bstep (se 2 (by rfl) ⟨1740696, by rfl⟩ : syracuseStep 4641857 = 3481393) B3481393
theorem B3094571 : Blo 2061435 3094571 := bstep (se 1 (by rfl) ⟨2320928, by rfl⟩ : syracuseStep 3094571 = 4641857) B4641857
theorem B2063047 : Blo 2061435 2063047 := bstep (se 1 (by rfl) ⟨1547285, by rfl⟩ : syracuseStep 2063047 = 3094571) B3094571
theorem B2320933 : Blo 2061435 2320933 := bbase (se 4 (by rfl) ⟨217587, by rfl⟩ : syracuseStep 2320933 = 435175) (by norm_num)
theorem B3094577 : Blo 2061435 3094577 := bstep (se 2 (by rfl) ⟨1160466, by rfl⟩ : syracuseStep 3094577 = 2320933) B2320933
theorem B2063051 : Blo 2061435 2063051 := bstep (se 1 (by rfl) ⟨1547288, by rfl⟩ : syracuseStep 2063051 = 3094577) B3094577
theorem B28231253 : Blo 2061435 28231253 := bbase (se 8 (by rfl) ⟨165417, by rfl⟩ : syracuseStep 28231253 = 330835) (by norm_num)
theorem B18820835 : Blo 2061435 18820835 := bstep (se 1 (by rfl) ⟨14115626, by rfl⟩ : syracuseStep 18820835 = 28231253) B28231253
theorem B12547223 : Blo 2061435 12547223 := bstep (se 1 (by rfl) ⟨9410417, by rfl⟩ : syracuseStep 12547223 = 18820835) B18820835
theorem B8364815 : Blo 2061435 8364815 := bstep (se 1 (by rfl) ⟨6273611, by rfl⟩ : syracuseStep 8364815 = 12547223) B12547223
theorem B5576543 : Blo 2061435 5576543 := bstep (se 1 (by rfl) ⟨4182407, by rfl⟩ : syracuseStep 5576543 = 8364815) B8364815
theorem B3717695 : Blo 2061435 3717695 := bstep (se 1 (by rfl) ⟨2788271, by rfl⟩ : syracuseStep 3717695 = 5576543) B5576543
theorem B9913853 : Blo 2061435 9913853 := bstep (se 3 (by rfl) ⟨1858847, by rfl⟩ : syracuseStep 9913853 = 3717695) B3717695
theorem B6609235 : Blo 2061435 6609235 := bstep (se 1 (by rfl) ⟨4956926, by rfl⟩ : syracuseStep 6609235 = 9913853) B9913853
theorem B8812313 : Blo 2061435 8812313 := bstep (se 2 (by rfl) ⟨3304617, by rfl⟩ : syracuseStep 8812313 = 6609235) B6609235
theorem B5874875 : Blo 2061435 5874875 := bstep (se 1 (by rfl) ⟨4406156, by rfl⟩ : syracuseStep 5874875 = 8812313) B8812313
theorem B3916583 : Blo 2061435 3916583 := bstep (se 1 (by rfl) ⟨2937437, by rfl⟩ : syracuseStep 3916583 = 5874875) B5874875
theorem B2611055 : Blo 2061435 2611055 := bstep (se 1 (by rfl) ⟨1958291, by rfl⟩ : syracuseStep 2611055 = 3916583) B3916583
theorem B6962813 : Blo 2061435 6962813 := bstep (se 3 (by rfl) ⟨1305527, by rfl⟩ : syracuseStep 6962813 = 2611055) B2611055
theorem B4641875 : Blo 2061435 4641875 := bstep (se 1 (by rfl) ⟨3481406, by rfl⟩ : syracuseStep 4641875 = 6962813) B6962813
theorem B3094583 : Blo 2061435 3094583 := bstep (se 1 (by rfl) ⟨2320937, by rfl⟩ : syracuseStep 3094583 = 4641875) B4641875
theorem B2063055 : Blo 2061435 2063055 := bstep (se 1 (by rfl) ⟨1547291, by rfl⟩ : syracuseStep 2063055 = 3094583) B3094583
theorem B3094589 : Blo 2061435 3094589 := bbase (se 3 (by rfl) ⟨580235, by rfl⟩ : syracuseStep 3094589 = 1160471) (by norm_num)
theorem B2063059 : Blo 2061435 2063059 := bstep (se 1 (by rfl) ⟨1547294, by rfl⟩ : syracuseStep 2063059 = 3094589) B3094589
theorem B4641893 : Blo 2061435 4641893 := bbase (se 4 (by rfl) ⟨435177, by rfl⟩ : syracuseStep 4641893 = 870355) (by norm_num)
theorem B3094595 : Blo 2061435 3094595 := bstep (se 1 (by rfl) ⟨2320946, by rfl⟩ : syracuseStep 3094595 = 4641893) B4641893
theorem B2063063 : Blo 2061435 2063063 := bstep (se 1 (by rfl) ⟨1547297, by rfl⟩ : syracuseStep 2063063 = 3094595) B3094595
theorem B5222141 : Blo 2061435 5222141 := bbase (se 3 (by rfl) ⟨979151, by rfl⟩ : syracuseStep 5222141 = 1958303) (by norm_num)
theorem B3481427 : Blo 2061435 3481427 := bstep (se 1 (by rfl) ⟨2611070, by rfl⟩ : syracuseStep 3481427 = 5222141) B5222141
theorem B2320951 : Blo 2061435 2320951 := bstep (se 1 (by rfl) ⟨1740713, by rfl⟩ : syracuseStep 2320951 = 3481427) B3481427
theorem B3094601 : Blo 2061435 3094601 := bstep (se 2 (by rfl) ⟨1160475, by rfl⟩ : syracuseStep 3094601 = 2320951) B2320951
theorem B2063067 : Blo 2061435 2063067 := bstep (se 1 (by rfl) ⟨1547300, by rfl⟩ : syracuseStep 2063067 = 3094601) B3094601
theorem B3916613 : Blo 2061435 3916613 := bbase (se 4 (by rfl) ⟨367182, by rfl⟩ : syracuseStep 3916613 = 734365) (by norm_num)
theorem B10444301 : Blo 2061435 10444301 := bstep (se 3 (by rfl) ⟨1958306, by rfl⟩ : syracuseStep 10444301 = 3916613) B3916613
theorem B6962867 : Blo 2061435 6962867 := bstep (se 1 (by rfl) ⟨5222150, by rfl⟩ : syracuseStep 6962867 = 10444301) B10444301
theorem B4641911 : Blo 2061435 4641911 := bstep (se 1 (by rfl) ⟨3481433, by rfl⟩ : syracuseStep 4641911 = 6962867) B6962867
theorem B3094607 : Blo 2061435 3094607 := bstep (se 1 (by rfl) ⟨2320955, by rfl⟩ : syracuseStep 3094607 = 4641911) B4641911
theorem B2063071 : Blo 2061435 2063071 := bstep (se 1 (by rfl) ⟨1547303, by rfl⟩ : syracuseStep 2063071 = 3094607) B3094607
theorem B3094613 : Blo 2061435 3094613 := bbase (se 8 (by rfl) ⟨18132, by rfl⟩ : syracuseStep 3094613 = 36265) (by norm_num)
theorem B2063075 : Blo 2061435 2063075 := bstep (se 1 (by rfl) ⟨1547306, by rfl⟩ : syracuseStep 2063075 = 3094613) B3094613
theorem B28231573 : Blo 2061435 28231573 := bbase (se 6 (by rfl) ⟨661677, by rfl⟩ : syracuseStep 28231573 = 1323355) (by norm_num)
theorem B37642097 : Blo 2061435 37642097 := bstep (se 2 (by rfl) ⟨14115786, by rfl⟩ : syracuseStep 37642097 = 28231573) B28231573
theorem B100378925 : Blo 2061435 100378925 := bstep (se 3 (by rfl) ⟨18821048, by rfl⟩ : syracuseStep 100378925 = 37642097) B37642097
theorem B66919283 : Blo 2061435 66919283 := bstep (se 1 (by rfl) ⟨50189462, by rfl⟩ : syracuseStep 66919283 = 100378925) B100378925
theorem B44612855 : Blo 2061435 44612855 := bstep (se 1 (by rfl) ⟨33459641, by rfl⟩ : syracuseStep 44612855 = 66919283) B66919283
theorem B29741903 : Blo 2061435 29741903 := bstep (se 1 (by rfl) ⟨22306427, by rfl⟩ : syracuseStep 29741903 = 44612855) B44612855
theorem B19827935 : Blo 2061435 19827935 := bstep (se 1 (by rfl) ⟨14870951, by rfl⟩ : syracuseStep 19827935 = 29741903) B29741903
theorem B13218623 : Blo 2061435 13218623 := bstep (se 1 (by rfl) ⟨9913967, by rfl⟩ : syracuseStep 13218623 = 19827935) B19827935
theorem B8812415 : Blo 2061435 8812415 := bstep (se 1 (by rfl) ⟨6609311, by rfl⟩ : syracuseStep 8812415 = 13218623) B13218623
theorem B5874943 : Blo 2061435 5874943 := bstep (se 1 (by rfl) ⟨4406207, by rfl⟩ : syracuseStep 5874943 = 8812415) B8812415
theorem B7833257 : Blo 2061435 7833257 := bstep (se 2 (by rfl) ⟨2937471, by rfl⟩ : syracuseStep 7833257 = 5874943) B5874943
theorem B5222171 : Blo 2061435 5222171 := bstep (se 1 (by rfl) ⟨3916628, by rfl⟩ : syracuseStep 5222171 = 7833257) B7833257
theorem B3481447 : Blo 2061435 3481447 := bstep (se 1 (by rfl) ⟨2611085, by rfl⟩ : syracuseStep 3481447 = 5222171) B5222171
theorem B4641929 : Blo 2061435 4641929 := bstep (se 2 (by rfl) ⟨1740723, by rfl⟩ : syracuseStep 4641929 = 3481447) B3481447
theorem B3094619 : Blo 2061435 3094619 := bstep (se 1 (by rfl) ⟨2320964, by rfl⟩ : syracuseStep 3094619 = 4641929) B4641929
theorem B2063079 : Blo 2061435 2063079 := bstep (se 1 (by rfl) ⟨1547309, by rfl⟩ : syracuseStep 2063079 = 3094619) B3094619
theorem B2320969 : Blo 2061435 2320969 := bbase (se 2 (by rfl) ⟨870363, by rfl⟩ : syracuseStep 2320969 = 1740727) (by norm_num)
theorem B3094625 : Blo 2061435 3094625 := bstep (se 2 (by rfl) ⟨1160484, by rfl⟩ : syracuseStep 3094625 = 2320969) B2320969
theorem B2063083 : Blo 2061435 2063083 := bstep (se 1 (by rfl) ⟨1547312, by rfl⟩ : syracuseStep 2063083 = 3094625) B3094625
theorem B9914005 : Blo 2061435 9914005 := bbase (se 6 (by rfl) ⟨232359, by rfl⟩ : syracuseStep 9914005 = 464719) (by norm_num)
theorem B13218673 : Blo 2061435 13218673 := bstep (se 2 (by rfl) ⟨4957002, by rfl⟩ : syracuseStep 13218673 = 9914005) B9914005
theorem B17624897 : Blo 2061435 17624897 := bstep (se 2 (by rfl) ⟨6609336, by rfl⟩ : syracuseStep 17624897 = 13218673) B13218673
theorem B11749931 : Blo 2061435 11749931 := bstep (se 1 (by rfl) ⟨8812448, by rfl⟩ : syracuseStep 11749931 = 17624897) B17624897
theorem B7833287 : Blo 2061435 7833287 := bstep (se 1 (by rfl) ⟨5874965, by rfl⟩ : syracuseStep 7833287 = 11749931) B11749931
theorem B5222191 : Blo 2061435 5222191 := bstep (se 1 (by rfl) ⟨3916643, by rfl⟩ : syracuseStep 5222191 = 7833287) B7833287
theorem B6962921 : Blo 2061435 6962921 := bstep (se 2 (by rfl) ⟨2611095, by rfl⟩ : syracuseStep 6962921 = 5222191) B5222191
theorem B4641947 : Blo 2061435 4641947 := bstep (se 1 (by rfl) ⟨3481460, by rfl⟩ : syracuseStep 4641947 = 6962921) B6962921
theorem B3094631 : Blo 2061435 3094631 := bstep (se 1 (by rfl) ⟨2320973, by rfl⟩ : syracuseStep 3094631 = 4641947) B4641947
theorem B2063087 : Blo 2061435 2063087 := bstep (se 1 (by rfl) ⟨1547315, by rfl⟩ : syracuseStep 2063087 = 3094631) B3094631
theorem B3094637 : Blo 2061435 3094637 := bbase (se 3 (by rfl) ⟨580244, by rfl⟩ : syracuseStep 3094637 = 1160489) (by norm_num)
theorem B2063091 : Blo 2061435 2063091 := bstep (se 1 (by rfl) ⟨1547318, by rfl⟩ : syracuseStep 2063091 = 3094637) B3094637
theorem B4641965 : Blo 2061435 4641965 := bbase (se 3 (by rfl) ⟨870368, by rfl⟩ : syracuseStep 4641965 = 1740737) (by norm_num)
theorem B3094643 : Blo 2061435 3094643 := bstep (se 1 (by rfl) ⟨2320982, by rfl⟩ : syracuseStep 3094643 = 4641965) B4641965
theorem B2063095 : Blo 2061435 2063095 := bstep (se 1 (by rfl) ⟨1547321, by rfl⟩ : syracuseStep 2063095 = 3094643) B3094643
theorem B7940213 : Blo 2061435 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B5293475 : Blo 2061435 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B3528983 : Blo 2061435 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B2352655 : Blo 2061435 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B12547493 : Blo 2061435 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B8364995 : Blo 2061435 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B5576663 : Blo 2061435 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B3717775 : Blo 2061435 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B4957033 : Blo 2061435 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B6609377 : Blo 2061435 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B4406251 : Blo 2061435 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B5875001 : Blo 2061435 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B3916667 : Blo 2061435 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B2611111 : Blo 2061435 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B3481481 : Blo 2061435 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B2320987 : Blo 2061435 2320987 := bstep (se 1 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 2320987 = 3481481) B3481481
theorem B3094649 : Blo 2061435 3094649 := bstep (se 2 (by rfl) ⟨1160493, by rfl⟩ : syracuseStep 3094649 = 2320987) B2320987
theorem B2063099 : Blo 2061435 2063099 := bstep (se 1 (by rfl) ⟨1547324, by rfl⟩ : syracuseStep 2063099 = 3094649) B3094649
theorem B5652757 : Blo 2061435 5652757 := bbase (se 6 (by rfl) ⟨132486, by rfl⟩ : syracuseStep 5652757 = 264973) (by norm_num)
theorem B30148037 : Blo 2061435 30148037 := bstep (se 4 (by rfl) ⟨2826378, by rfl⟩ : syracuseStep 30148037 = 5652757) B5652757
theorem B20098691 : Blo 2061435 20098691 := bstep (se 1 (by rfl) ⟨15074018, by rfl⟩ : syracuseStep 20098691 = 30148037) B30148037
theorem B13399127 : Blo 2061435 13399127 := bstep (se 1 (by rfl) ⟨10049345, by rfl⟩ : syracuseStep 13399127 = 20098691) B20098691
theorem B8932751 : Blo 2061435 8932751 := bstep (se 1 (by rfl) ⟨6699563, by rfl⟩ : syracuseStep 8932751 = 13399127) B13399127
theorem B5955167 : Blo 2061435 5955167 := bstep (se 1 (by rfl) ⟨4466375, by rfl⟩ : syracuseStep 5955167 = 8932751) B8932751
theorem B15880445 : Blo 2061435 15880445 := bstep (se 3 (by rfl) ⟨2977583, by rfl⟩ : syracuseStep 15880445 = 5955167) B5955167
theorem B10586963 : Blo 2061435 10586963 := bstep (se 1 (by rfl) ⟨7940222, by rfl⟩ : syracuseStep 10586963 = 15880445) B15880445
theorem B28231901 : Blo 2061435 28231901 := bstep (se 3 (by rfl) ⟨5293481, by rfl⟩ : syracuseStep 28231901 = 10586963) B10586963
theorem B18821267 : Blo 2061435 18821267 := bstep (se 1 (by rfl) ⟨14115950, by rfl⟩ : syracuseStep 18821267 = 28231901) B28231901
theorem B12547511 : Blo 2061435 12547511 := bstep (se 1 (by rfl) ⟨9410633, by rfl⟩ : syracuseStep 12547511 = 18821267) B18821267
theorem B8365007 : Blo 2061435 8365007 := bstep (se 1 (by rfl) ⟨6273755, by rfl⟩ : syracuseStep 8365007 = 12547511) B12547511
theorem B5576671 : Blo 2061435 5576671 := bstep (se 1 (by rfl) ⟨4182503, by rfl⟩ : syracuseStep 5576671 = 8365007) B8365007
theorem B7435561 : Blo 2061435 7435561 := bstep (se 2 (by rfl) ⟨2788335, by rfl⟩ : syracuseStep 7435561 = 5576671) B5576671
theorem B9914081 : Blo 2061435 9914081 := bstep (se 2 (by rfl) ⟨3717780, by rfl⟩ : syracuseStep 9914081 = 7435561) B7435561
theorem B26437549 : Blo 2061435 26437549 := bstep (se 3 (by rfl) ⟨4957040, by rfl⟩ : syracuseStep 26437549 = 9914081) B9914081
theorem B35250065 : Blo 2061435 35250065 := bstep (se 2 (by rfl) ⟨13218774, by rfl⟩ : syracuseStep 35250065 = 26437549) B26437549
theorem B23500043 : Blo 2061435 23500043 := bstep (se 1 (by rfl) ⟨17625032, by rfl⟩ : syracuseStep 23500043 = 35250065) B35250065
theorem B15666695 : Blo 2061435 15666695 := bstep (se 1 (by rfl) ⟨11750021, by rfl⟩ : syracuseStep 15666695 = 23500043) B23500043
theorem B10444463 : Blo 2061435 10444463 := bstep (se 1 (by rfl) ⟨7833347, by rfl⟩ : syracuseStep 10444463 = 15666695) B15666695
theorem B6962975 : Blo 2061435 6962975 := bstep (se 1 (by rfl) ⟨5222231, by rfl⟩ : syracuseStep 6962975 = 10444463) B10444463
theorem B4641983 : Blo 2061435 4641983 := bstep (se 1 (by rfl) ⟨3481487, by rfl⟩ : syracuseStep 4641983 = 6962975) B6962975
theorem B3094655 : Blo 2061435 3094655 := bstep (se 1 (by rfl) ⟨2320991, by rfl⟩ : syracuseStep 3094655 = 4641983) B4641983
theorem B2063103 : Blo 2061435 2063103 := bstep (se 1 (by rfl) ⟨1547327, by rfl⟩ : syracuseStep 2063103 = 3094655) B3094655
theorem B3094661 : Blo 2061435 3094661 := bbase (se 4 (by rfl) ⟨290124, by rfl⟩ : syracuseStep 3094661 = 580249) (by norm_num)
theorem B2063107 : Blo 2061435 2063107 := bstep (se 1 (by rfl) ⟨1547330, by rfl⟩ : syracuseStep 2063107 = 3094661) B3094661
theorem B3481501 : Blo 2061435 3481501 := bbase (se 3 (by rfl) ⟨652781, by rfl⟩ : syracuseStep 3481501 = 1305563) (by norm_num)
theorem B4642001 : Blo 2061435 4642001 := bstep (se 2 (by rfl) ⟨1740750, by rfl⟩ : syracuseStep 4642001 = 3481501) B3481501
theorem B3094667 : Blo 2061435 3094667 := bstep (se 1 (by rfl) ⟨2321000, by rfl⟩ : syracuseStep 3094667 = 4642001) B4642001
theorem B2063111 : Blo 2061435 2063111 := bstep (se 1 (by rfl) ⟨1547333, by rfl⟩ : syracuseStep 2063111 = 3094667) B3094667
theorem B2321005 : Blo 2061435 2321005 := bbase (se 3 (by rfl) ⟨435188, by rfl⟩ : syracuseStep 2321005 = 870377) (by norm_num)
theorem B3094673 : Blo 2061435 3094673 := bstep (se 2 (by rfl) ⟨1160502, by rfl⟩ : syracuseStep 3094673 = 2321005) B2321005
theorem B2063115 : Blo 2061435 2063115 := bstep (se 1 (by rfl) ⟨1547336, by rfl⟩ : syracuseStep 2063115 = 3094673) B3094673
theorem B6963029 : Blo 2061435 6963029 := bbase (se 9 (by rfl) ⟨20399, by rfl⟩ : syracuseStep 6963029 = 40799) (by norm_num)
theorem B4642019 : Blo 2061435 4642019 := bstep (se 1 (by rfl) ⟨3481514, by rfl⟩ : syracuseStep 4642019 = 6963029) B6963029
theorem B3094679 : Blo 2061435 3094679 := bstep (se 1 (by rfl) ⟨2321009, by rfl⟩ : syracuseStep 3094679 = 4642019) B4642019
theorem B2063119 : Blo 2061435 2063119 := bstep (se 1 (by rfl) ⟨1547339, by rfl⟩ : syracuseStep 2063119 = 3094679) B3094679
theorem B3094685 : Blo 2061435 3094685 := bbase (se 3 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 3094685 = 1160507) (by norm_num)
theorem B2063123 : Blo 2061435 2063123 := bstep (se 1 (by rfl) ⟨1547342, by rfl⟩ : syracuseStep 2063123 = 3094685) B3094685
theorem B4642037 : Blo 2061435 4642037 := bbase (se 5 (by rfl) ⟨217595, by rfl⟩ : syracuseStep 4642037 = 435191) (by norm_num)
theorem B3094691 : Blo 2061435 3094691 := bstep (se 1 (by rfl) ⟨2321018, by rfl⟩ : syracuseStep 3094691 = 4642037) B4642037
theorem B2063127 : Blo 2061435 2063127 := bstep (se 1 (by rfl) ⟨1547345, by rfl⟩ : syracuseStep 2063127 = 3094691) B3094691
theorem B4705381 : Blo 2061435 4705381 := bbase (se 4 (by rfl) ⟨441129, by rfl⟩ : syracuseStep 4705381 = 882259) (by norm_num)
theorem B25095365 : Blo 2061435 25095365 := bstep (se 4 (by rfl) ⟨2352690, by rfl⟩ : syracuseStep 25095365 = 4705381) B4705381
theorem B16730243 : Blo 2061435 16730243 := bstep (se 1 (by rfl) ⟨12547682, by rfl⟩ : syracuseStep 16730243 = 25095365) B25095365
theorem B11153495 : Blo 2061435 11153495 := bstep (se 1 (by rfl) ⟨8365121, by rfl⟩ : syracuseStep 11153495 = 16730243) B16730243
theorem B29742653 : Blo 2061435 29742653 := bstep (se 3 (by rfl) ⟨5576747, by rfl⟩ : syracuseStep 29742653 = 11153495) B11153495
theorem B19828435 : Blo 2061435 19828435 := bstep (se 1 (by rfl) ⟨14871326, by rfl⟩ : syracuseStep 19828435 = 29742653) B29742653
theorem B26437913 : Blo 2061435 26437913 := bstep (se 2 (by rfl) ⟨9914217, by rfl⟩ : syracuseStep 26437913 = 19828435) B19828435
theorem B17625275 : Blo 2061435 17625275 := bstep (se 1 (by rfl) ⟨13218956, by rfl⟩ : syracuseStep 17625275 = 26437913) B26437913
theorem B11750183 : Blo 2061435 11750183 := bstep (se 1 (by rfl) ⟨8812637, by rfl⟩ : syracuseStep 11750183 = 17625275) B17625275
theorem B7833455 : Blo 2061435 7833455 := bstep (se 1 (by rfl) ⟨5875091, by rfl⟩ : syracuseStep 7833455 = 11750183) B11750183
theorem B5222303 : Blo 2061435 5222303 := bstep (se 1 (by rfl) ⟨3916727, by rfl⟩ : syracuseStep 5222303 = 7833455) B7833455
theorem B3481535 : Blo 2061435 3481535 := bstep (se 1 (by rfl) ⟨2611151, by rfl⟩ : syracuseStep 3481535 = 5222303) B5222303
theorem B2321023 : Blo 2061435 2321023 := bstep (se 1 (by rfl) ⟨1740767, by rfl⟩ : syracuseStep 2321023 = 3481535) B3481535
theorem B3094697 : Blo 2061435 3094697 := bstep (se 2 (by rfl) ⟨1160511, by rfl⟩ : syracuseStep 3094697 = 2321023) B2321023
theorem B2063131 : Blo 2061435 2063131 := bstep (se 1 (by rfl) ⟨1547348, by rfl⟩ : syracuseStep 2063131 = 3094697) B3094697
theorem B9054773 : Blo 2061435 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B6036515 : Blo 2061435 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B4024343 : Blo 2061435 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B2682895 : Blo 2061435 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B3577193 : Blo 2061435 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B2384795 : Blo 2061435 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B6359453 : Blo 2061435 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B4239635 : Blo 2061435 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B11305693 : Blo 2061435 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B15074257 : Blo 2061435 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B20099009 : Blo 2061435 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B13399339 : Blo 2061435 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B17865785 : Blo 2061435 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B11910523 : Blo 2061435 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B15880697 : Blo 2061435 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B10587131 : Blo 2061435 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B7058087 : Blo 2061435 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B4705391 : Blo 2061435 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B12547709 : Blo 2061435 12547709 := bstep (se 3 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 12547709 = 4705391) B4705391
theorem B8365139 : Blo 2061435 8365139 := bstep (se 1 (by rfl) ⟨6273854, by rfl⟩ : syracuseStep 8365139 = 12547709) B12547709
theorem B5576759 : Blo 2061435 5576759 := bstep (se 1 (by rfl) ⟨4182569, by rfl⟩ : syracuseStep 5576759 = 8365139) B8365139
theorem B3717839 : Blo 2061435 3717839 := bstep (se 1 (by rfl) ⟨2788379, by rfl⟩ : syracuseStep 3717839 = 5576759) B5576759
theorem B9914237 : Blo 2061435 9914237 := bstep (se 3 (by rfl) ⟨1858919, by rfl⟩ : syracuseStep 9914237 = 3717839) B3717839
theorem B6609491 : Blo 2061435 6609491 := bstep (se 1 (by rfl) ⟨4957118, by rfl⟩ : syracuseStep 6609491 = 9914237) B9914237
theorem B4406327 : Blo 2061435 4406327 := bstep (se 1 (by rfl) ⟨3304745, by rfl⟩ : syracuseStep 4406327 = 6609491) B6609491
theorem B2937551 : Blo 2061435 2937551 := bstep (se 1 (by rfl) ⟨2203163, by rfl⟩ : syracuseStep 2937551 = 4406327) B4406327
theorem B7833469 : Blo 2061435 7833469 := bstep (se 3 (by rfl) ⟨1468775, by rfl⟩ : syracuseStep 7833469 = 2937551) B2937551
theorem B10444625 : Blo 2061435 10444625 := bstep (se 2 (by rfl) ⟨3916734, by rfl⟩ : syracuseStep 10444625 = 7833469) B7833469
theorem B6963083 : Blo 2061435 6963083 := bstep (se 1 (by rfl) ⟨5222312, by rfl⟩ : syracuseStep 6963083 = 10444625) B10444625
theorem B4642055 : Blo 2061435 4642055 := bstep (se 1 (by rfl) ⟨3481541, by rfl⟩ : syracuseStep 4642055 = 6963083) B6963083
theorem B3094703 : Blo 2061435 3094703 := bstep (se 1 (by rfl) ⟨2321027, by rfl⟩ : syracuseStep 3094703 = 4642055) B4642055
theorem B2063135 : Blo 2061435 2063135 := bstep (se 1 (by rfl) ⟨1547351, by rfl⟩ : syracuseStep 2063135 = 3094703) B3094703
theorem B3094709 : Blo 2061435 3094709 := bbase (se 5 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 3094709 = 290129) (by norm_num)
theorem B2063139 : Blo 2061435 2063139 := bstep (se 1 (by rfl) ⟨1547354, by rfl⟩ : syracuseStep 2063139 = 3094709) B3094709
theorem B5222333 : Blo 2061435 5222333 := bbase (se 3 (by rfl) ⟨979187, by rfl⟩ : syracuseStep 5222333 = 1958375) (by norm_num)
theorem B3481555 : Blo 2061435 3481555 := bstep (se 1 (by rfl) ⟨2611166, by rfl⟩ : syracuseStep 3481555 = 5222333) B5222333
theorem B4642073 : Blo 2061435 4642073 := bstep (se 2 (by rfl) ⟨1740777, by rfl⟩ : syracuseStep 4642073 = 3481555) B3481555
theorem B3094715 : Blo 2061435 3094715 := bstep (se 1 (by rfl) ⟨2321036, by rfl⟩ : syracuseStep 3094715 = 4642073) B4642073
theorem B2063143 : Blo 2061435 2063143 := bstep (se 1 (by rfl) ⟨1547357, by rfl⟩ : syracuseStep 2063143 = 3094715) B3094715
theorem B2321041 : Blo 2061435 2321041 := bbase (se 2 (by rfl) ⟨870390, by rfl⟩ : syracuseStep 2321041 = 1740781) (by norm_num)
theorem B3094721 : Blo 2061435 3094721 := bstep (se 2 (by rfl) ⟨1160520, by rfl⟩ : syracuseStep 3094721 = 2321041) B2321041
theorem B2063147 : Blo 2061435 2063147 := bstep (se 1 (by rfl) ⟨1547360, by rfl⟩ : syracuseStep 2063147 = 3094721) B3094721
theorem B3916765 : Blo 2061435 3916765 := bbase (se 3 (by rfl) ⟨734393, by rfl⟩ : syracuseStep 3916765 = 1468787) (by norm_num)
theorem B5222353 : Blo 2061435 5222353 := bstep (se 2 (by rfl) ⟨1958382, by rfl⟩ : syracuseStep 5222353 = 3916765) B3916765
theorem B6963137 : Blo 2061435 6963137 := bstep (se 2 (by rfl) ⟨2611176, by rfl⟩ : syracuseStep 6963137 = 5222353) B5222353
theorem B4642091 : Blo 2061435 4642091 := bstep (se 1 (by rfl) ⟨3481568, by rfl⟩ : syracuseStep 4642091 = 6963137) B6963137
theorem B3094727 : Blo 2061435 3094727 := bstep (se 1 (by rfl) ⟨2321045, by rfl⟩ : syracuseStep 3094727 = 4642091) B4642091
theorem B2063151 : Blo 2061435 2063151 := bstep (se 1 (by rfl) ⟨1547363, by rfl⟩ : syracuseStep 2063151 = 3094727) B3094727
theorem B3094733 : Blo 2061435 3094733 := bbase (se 3 (by rfl) ⟨580262, by rfl⟩ : syracuseStep 3094733 = 1160525) (by norm_num)
theorem B2063155 : Blo 2061435 2063155 := bstep (se 1 (by rfl) ⟨1547366, by rfl⟩ : syracuseStep 2063155 = 3094733) B3094733
theorem B4642109 : Blo 2061435 4642109 := bbase (se 3 (by rfl) ⟨870395, by rfl⟩ : syracuseStep 4642109 = 1740791) (by norm_num)
theorem B3094739 : Blo 2061435 3094739 := bstep (se 1 (by rfl) ⟨2321054, by rfl⟩ : syracuseStep 3094739 = 4642109) B4642109
theorem B2063159 : Blo 2061435 2063159 := bstep (se 1 (by rfl) ⟨1547369, by rfl⟩ : syracuseStep 2063159 = 3094739) B3094739
theorem B3481589 : Blo 2061435 3481589 := bbase (se 5 (by rfl) ⟨163199, by rfl⟩ : syracuseStep 3481589 = 326399) (by norm_num)
theorem B2321059 : Blo 2061435 2321059 := bstep (se 1 (by rfl) ⟨1740794, by rfl⟩ : syracuseStep 2321059 = 3481589) B3481589
theorem B3094745 : Blo 2061435 3094745 := bstep (se 2 (by rfl) ⟨1160529, by rfl⟩ : syracuseStep 3094745 = 2321059) B2321059
theorem B2063163 : Blo 2061435 2063163 := bstep (se 1 (by rfl) ⟨1547372, by rfl⟩ : syracuseStep 2063163 = 3094745) B3094745
theorem B2091317 : Blo 2061435 2091317 := bbase (se 5 (by rfl) ⟨98030, by rfl⟩ : syracuseStep 2091317 = 196061) (by norm_num)
theorem B5576845 : Blo 2061435 5576845 := bstep (se 3 (by rfl) ⟨1045658, by rfl⟩ : syracuseStep 5576845 = 2091317) B2091317
theorem B7435793 : Blo 2061435 7435793 := bstep (se 2 (by rfl) ⟨2788422, by rfl⟩ : syracuseStep 7435793 = 5576845) B5576845
theorem B4957195 : Blo 2061435 4957195 := bstep (se 1 (by rfl) ⟨3717896, by rfl⟩ : syracuseStep 4957195 = 7435793) B7435793
theorem B6609593 : Blo 2061435 6609593 := bstep (se 2 (by rfl) ⟨2478597, by rfl⟩ : syracuseStep 6609593 = 4957195) B4957195
theorem B4406395 : Blo 2061435 4406395 := bstep (se 1 (by rfl) ⟨3304796, by rfl⟩ : syracuseStep 4406395 = 6609593) B6609593
theorem B5875193 : Blo 2061435 5875193 := bstep (se 2 (by rfl) ⟨2203197, by rfl⟩ : syracuseStep 5875193 = 4406395) B4406395
theorem B15667181 : Blo 2061435 15667181 := bstep (se 3 (by rfl) ⟨2937596, by rfl⟩ : syracuseStep 15667181 = 5875193) B5875193
theorem B10444787 : Blo 2061435 10444787 := bstep (se 1 (by rfl) ⟨7833590, by rfl⟩ : syracuseStep 10444787 = 15667181) B15667181
theorem B6963191 : Blo 2061435 6963191 := bstep (se 1 (by rfl) ⟨5222393, by rfl⟩ : syracuseStep 6963191 = 10444787) B10444787
theorem B4642127 : Blo 2061435 4642127 := bstep (se 1 (by rfl) ⟨3481595, by rfl⟩ : syracuseStep 4642127 = 6963191) B6963191
theorem B3094751 : Blo 2061435 3094751 := bstep (se 1 (by rfl) ⟨2321063, by rfl⟩ : syracuseStep 3094751 = 4642127) B4642127
theorem B2063167 : Blo 2061435 2063167 := bstep (se 1 (by rfl) ⟨1547375, by rfl⟩ : syracuseStep 2063167 = 3094751) B3094751
theorem B3094757 : Blo 2061435 3094757 := bbase (se 4 (by rfl) ⟨290133, by rfl⟩ : syracuseStep 3094757 = 580267) (by norm_num)
theorem B2063171 : Blo 2061435 2063171 := bstep (se 1 (by rfl) ⟨1547378, by rfl⟩ : syracuseStep 2063171 = 3094757) B3094757
theorem B4406413 : Blo 2061435 4406413 := bbase (se 3 (by rfl) ⟨826202, by rfl⟩ : syracuseStep 4406413 = 1652405) (by norm_num)
theorem B5875217 : Blo 2061435 5875217 := bstep (se 2 (by rfl) ⟨2203206, by rfl⟩ : syracuseStep 5875217 = 4406413) B4406413
theorem B3916811 : Blo 2061435 3916811 := bstep (se 1 (by rfl) ⟨2937608, by rfl⟩ : syracuseStep 3916811 = 5875217) B5875217
theorem B2611207 : Blo 2061435 2611207 := bstep (se 1 (by rfl) ⟨1958405, by rfl⟩ : syracuseStep 2611207 = 3916811) B3916811
theorem B3481609 : Blo 2061435 3481609 := bstep (se 2 (by rfl) ⟨1305603, by rfl⟩ : syracuseStep 3481609 = 2611207) B2611207
theorem B4642145 : Blo 2061435 4642145 := bstep (se 2 (by rfl) ⟨1740804, by rfl⟩ : syracuseStep 4642145 = 3481609) B3481609
theorem B3094763 : Blo 2061435 3094763 := bstep (se 1 (by rfl) ⟨2321072, by rfl⟩ : syracuseStep 3094763 = 4642145) B4642145
theorem B2063175 : Blo 2061435 2063175 := bstep (se 1 (by rfl) ⟨1547381, by rfl⟩ : syracuseStep 2063175 = 3094763) B3094763
theorem B2321077 : Blo 2061435 2321077 := bbase (se 5 (by rfl) ⟨108800, by rfl⟩ : syracuseStep 2321077 = 217601) (by norm_num)
theorem B3094769 : Blo 2061435 3094769 := bstep (se 2 (by rfl) ⟨1160538, by rfl⟩ : syracuseStep 3094769 = 2321077) B2321077
theorem B2063179 : Blo 2061435 2063179 := bstep (se 1 (by rfl) ⟨1547384, by rfl⟩ : syracuseStep 2063179 = 3094769) B3094769
theorem B2611217 : Blo 2061435 2611217 := bbase (se 2 (by rfl) ⟨979206, by rfl⟩ : syracuseStep 2611217 = 1958413) (by norm_num)
theorem B6963245 : Blo 2061435 6963245 := bstep (se 3 (by rfl) ⟨1305608, by rfl⟩ : syracuseStep 6963245 = 2611217) B2611217
theorem B4642163 : Blo 2061435 4642163 := bstep (se 1 (by rfl) ⟨3481622, by rfl⟩ : syracuseStep 4642163 = 6963245) B6963245
theorem B3094775 : Blo 2061435 3094775 := bstep (se 1 (by rfl) ⟨2321081, by rfl⟩ : syracuseStep 3094775 = 4642163) B4642163
theorem B2063183 : Blo 2061435 2063183 := bstep (se 1 (by rfl) ⟨1547387, by rfl⟩ : syracuseStep 2063183 = 3094775) B3094775
theorem B3094781 : Blo 2061435 3094781 := bbase (se 3 (by rfl) ⟨580271, by rfl⟩ : syracuseStep 3094781 = 1160543) (by norm_num)
theorem B2063187 : Blo 2061435 2063187 := bstep (se 1 (by rfl) ⟨1547390, by rfl⟩ : syracuseStep 2063187 = 3094781) B3094781
theorem B4642181 : Blo 2061435 4642181 := bbase (se 4 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 4642181 = 870409) (by norm_num)
theorem B3094787 : Blo 2061435 3094787 := bstep (se 1 (by rfl) ⟨2321090, by rfl⟩ : syracuseStep 3094787 = 4642181) B4642181
theorem B2063191 : Blo 2061435 2063191 := bstep (se 1 (by rfl) ⟨1547393, by rfl⟩ : syracuseStep 2063191 = 3094787) B3094787
theorem B2937637 : Blo 2061435 2937637 := bbase (se 4 (by rfl) ⟨275403, by rfl⟩ : syracuseStep 2937637 = 550807) (by norm_num)
theorem B3916849 : Blo 2061435 3916849 := bstep (se 2 (by rfl) ⟨1468818, by rfl⟩ : syracuseStep 3916849 = 2937637) B2937637
theorem B5222465 : Blo 2061435 5222465 := bstep (se 2 (by rfl) ⟨1958424, by rfl⟩ : syracuseStep 5222465 = 3916849) B3916849
theorem B3481643 : Blo 2061435 3481643 := bstep (se 1 (by rfl) ⟨2611232, by rfl⟩ : syracuseStep 3481643 = 5222465) B5222465
theorem B2321095 : Blo 2061435 2321095 := bstep (se 1 (by rfl) ⟨1740821, by rfl⟩ : syracuseStep 2321095 = 3481643) B3481643
theorem B3094793 : Blo 2061435 3094793 := bstep (se 2 (by rfl) ⟨1160547, by rfl⟩ : syracuseStep 3094793 = 2321095) B2321095
theorem B2063195 : Blo 2061435 2063195 := bstep (se 1 (by rfl) ⟨1547396, by rfl⟩ : syracuseStep 2063195 = 3094793) B3094793
theorem B10444949 : Blo 2061435 10444949 := bbase (se 6 (by rfl) ⟨244803, by rfl⟩ : syracuseStep 10444949 = 489607) (by norm_num)
theorem B6963299 : Blo 2061435 6963299 := bstep (se 1 (by rfl) ⟨5222474, by rfl⟩ : syracuseStep 6963299 = 10444949) B10444949
theorem B4642199 : Blo 2061435 4642199 := bstep (se 1 (by rfl) ⟨3481649, by rfl⟩ : syracuseStep 4642199 = 6963299) B6963299
theorem B3094799 : Blo 2061435 3094799 := bstep (se 1 (by rfl) ⟨2321099, by rfl⟩ : syracuseStep 3094799 = 4642199) B4642199
theorem B2063199 : Blo 2061435 2063199 := bstep (se 1 (by rfl) ⟨1547399, by rfl⟩ : syracuseStep 2063199 = 3094799) B3094799
theorem B3094805 : Blo 2061435 3094805 := bbase (se 6 (by rfl) ⟨72534, by rfl⟩ : syracuseStep 3094805 = 145069) (by norm_num)
theorem B2063203 : Blo 2061435 2063203 := bstep (se 1 (by rfl) ⟨1547402, by rfl⟩ : syracuseStep 2063203 = 3094805) B3094805
theorem B3820117 : Blo 2061435 3820117 := bbase (se 8 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 3820117 = 44767) (by norm_num)
theorem B5093489 : Blo 2061435 5093489 := bstep (se 2 (by rfl) ⟨1910058, by rfl⟩ : syracuseStep 5093489 = 3820117) B3820117
theorem B13582637 : Blo 2061435 13582637 := bstep (se 3 (by rfl) ⟨2546744, by rfl⟩ : syracuseStep 13582637 = 5093489) B5093489
theorem B9055091 : Blo 2061435 9055091 := bstep (se 1 (by rfl) ⟨6791318, by rfl⟩ : syracuseStep 9055091 = 13582637) B13582637
theorem B24146909 : Blo 2061435 24146909 := bstep (se 3 (by rfl) ⟨4527545, by rfl⟩ : syracuseStep 24146909 = 9055091) B9055091
theorem B16097939 : Blo 2061435 16097939 := bstep (se 1 (by rfl) ⟨12073454, by rfl⟩ : syracuseStep 16097939 = 24146909) B24146909
theorem B10731959 : Blo 2061435 10731959 := bstep (se 1 (by rfl) ⟨8048969, by rfl⟩ : syracuseStep 10731959 = 16097939) B16097939
theorem B7154639 : Blo 2061435 7154639 := bstep (se 1 (by rfl) ⟨5365979, by rfl⟩ : syracuseStep 7154639 = 10731959) B10731959
theorem B4769759 : Blo 2061435 4769759 := bstep (se 1 (by rfl) ⟨3577319, by rfl⟩ : syracuseStep 4769759 = 7154639) B7154639
theorem B3179839 : Blo 2061435 3179839 := bstep (se 1 (by rfl) ⟨2384879, by rfl⟩ : syracuseStep 3179839 = 4769759) B4769759
theorem B4239785 : Blo 2061435 4239785 := bstep (se 2 (by rfl) ⟨1589919, by rfl⟩ : syracuseStep 4239785 = 3179839) B3179839
theorem B2826523 : Blo 2061435 2826523 := bstep (se 1 (by rfl) ⟨2119892, by rfl⟩ : syracuseStep 2826523 = 4239785) B4239785
theorem B3768697 : Blo 2061435 3768697 := bstep (se 2 (by rfl) ⟨1413261, by rfl⟩ : syracuseStep 3768697 = 2826523) B2826523
theorem B5024929 : Blo 2061435 5024929 := bstep (se 2 (by rfl) ⟨1884348, by rfl⟩ : syracuseStep 5024929 = 3768697) B3768697
theorem B6699905 : Blo 2061435 6699905 := bstep (se 2 (by rfl) ⟨2512464, by rfl⟩ : syracuseStep 6699905 = 5024929) B5024929
theorem B4466603 : Blo 2061435 4466603 := bstep (se 1 (by rfl) ⟨3349952, by rfl⟩ : syracuseStep 4466603 = 6699905) B6699905
theorem B2977735 : Blo 2061435 2977735 := bstep (se 1 (by rfl) ⟨2233301, by rfl⟩ : syracuseStep 2977735 = 4466603) B4466603
theorem B3970313 : Blo 2061435 3970313 := bstep (se 2 (by rfl) ⟨1488867, by rfl⟩ : syracuseStep 3970313 = 2977735) B2977735
theorem B2646875 : Blo 2061435 2646875 := bstep (se 1 (by rfl) ⟨1985156, by rfl⟩ : syracuseStep 2646875 = 3970313) B3970313
theorem B7058333 : Blo 2061435 7058333 := bstep (se 3 (by rfl) ⟨1323437, by rfl⟩ : syracuseStep 7058333 = 2646875) B2646875
theorem B4705555 : Blo 2061435 4705555 := bstep (se 1 (by rfl) ⟨3529166, by rfl⟩ : syracuseStep 4705555 = 7058333) B7058333
theorem B6274073 : Blo 2061435 6274073 := bstep (se 2 (by rfl) ⟨2352777, by rfl⟩ : syracuseStep 6274073 = 4705555) B4705555
theorem B4182715 : Blo 2061435 4182715 := bstep (se 1 (by rfl) ⟨3137036, by rfl⟩ : syracuseStep 4182715 = 6274073) B6274073
theorem B5576953 : Blo 2061435 5576953 := bstep (se 2 (by rfl) ⟨2091357, by rfl⟩ : syracuseStep 5576953 = 4182715) B4182715
theorem B7435937 : Blo 2061435 7435937 := bstep (se 2 (by rfl) ⟨2788476, by rfl⟩ : syracuseStep 7435937 = 5576953) B5576953
theorem B4957291 : Blo 2061435 4957291 := bstep (se 1 (by rfl) ⟨3717968, by rfl⟩ : syracuseStep 4957291 = 7435937) B7435937
theorem B26438885 : Blo 2061435 26438885 := bstep (se 4 (by rfl) ⟨2478645, by rfl⟩ : syracuseStep 26438885 = 4957291) B4957291
theorem B17625923 : Blo 2061435 17625923 := bstep (se 1 (by rfl) ⟨13219442, by rfl⟩ : syracuseStep 17625923 = 26438885) B26438885
theorem B11750615 : Blo 2061435 11750615 := bstep (se 1 (by rfl) ⟨8812961, by rfl⟩ : syracuseStep 11750615 = 17625923) B17625923
theorem B7833743 : Blo 2061435 7833743 := bstep (se 1 (by rfl) ⟨5875307, by rfl⟩ : syracuseStep 7833743 = 11750615) B11750615
theorem B5222495 : Blo 2061435 5222495 := bstep (se 1 (by rfl) ⟨3916871, by rfl⟩ : syracuseStep 5222495 = 7833743) B7833743
theorem B3481663 : Blo 2061435 3481663 := bstep (se 1 (by rfl) ⟨2611247, by rfl⟩ : syracuseStep 3481663 = 5222495) B5222495
theorem B4642217 : Blo 2061435 4642217 := bstep (se 2 (by rfl) ⟨1740831, by rfl⟩ : syracuseStep 4642217 = 3481663) B3481663
theorem B3094811 : Blo 2061435 3094811 := bstep (se 1 (by rfl) ⟨2321108, by rfl⟩ : syracuseStep 3094811 = 4642217) B4642217
theorem B2063207 : Blo 2061435 2063207 := bstep (se 1 (by rfl) ⟨1547405, by rfl⟩ : syracuseStep 2063207 = 3094811) B3094811
theorem B2321113 : Blo 2061435 2321113 := bbase (se 2 (by rfl) ⟨870417, by rfl⟩ : syracuseStep 2321113 = 1740835) (by norm_num)
theorem B3094817 : Blo 2061435 3094817 := bstep (se 2 (by rfl) ⟨1160556, by rfl⟩ : syracuseStep 3094817 = 2321113) B2321113
theorem B2063211 : Blo 2061435 2063211 := bstep (se 1 (by rfl) ⟨1547408, by rfl⟩ : syracuseStep 2063211 = 3094817) B3094817
theorem B2203249 : Blo 2061435 2203249 := bbase (se 2 (by rfl) ⟨826218, by rfl⟩ : syracuseStep 2203249 = 1652437) (by norm_num)
theorem B2937665 : Blo 2061435 2937665 := bstep (se 2 (by rfl) ⟨1101624, by rfl⟩ : syracuseStep 2937665 = 2203249) B2203249
theorem B7833773 : Blo 2061435 7833773 := bstep (se 3 (by rfl) ⟨1468832, by rfl⟩ : syracuseStep 7833773 = 2937665) B2937665
theorem B5222515 : Blo 2061435 5222515 := bstep (se 1 (by rfl) ⟨3916886, by rfl⟩ : syracuseStep 5222515 = 7833773) B7833773
theorem B6963353 : Blo 2061435 6963353 := bstep (se 2 (by rfl) ⟨2611257, by rfl⟩ : syracuseStep 6963353 = 5222515) B5222515
theorem B4642235 : Blo 2061435 4642235 := bstep (se 1 (by rfl) ⟨3481676, by rfl⟩ : syracuseStep 4642235 = 6963353) B6963353
theorem B3094823 : Blo 2061435 3094823 := bstep (se 1 (by rfl) ⟨2321117, by rfl⟩ : syracuseStep 3094823 = 4642235) B4642235
theorem B2063215 : Blo 2061435 2063215 := bstep (se 1 (by rfl) ⟨1547411, by rfl⟩ : syracuseStep 2063215 = 3094823) B3094823
theorem B3094829 : Blo 2061435 3094829 := bbase (se 3 (by rfl) ⟨580280, by rfl⟩ : syracuseStep 3094829 = 1160561) (by norm_num)
theorem B2063219 : Blo 2061435 2063219 := bstep (se 1 (by rfl) ⟨1547414, by rfl⟩ : syracuseStep 2063219 = 3094829) B3094829
theorem B4642253 : Blo 2061435 4642253 := bbase (se 3 (by rfl) ⟨870422, by rfl⟩ : syracuseStep 4642253 = 1740845) (by norm_num)
theorem B3094835 : Blo 2061435 3094835 := bstep (se 1 (by rfl) ⟨2321126, by rfl⟩ : syracuseStep 3094835 = 4642253) B4642253
theorem B2063223 : Blo 2061435 2063223 := bstep (se 1 (by rfl) ⟨1547417, by rfl⟩ : syracuseStep 2063223 = 3094835) B3094835
theorem B2611273 : Blo 2061435 2611273 := bbase (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) (by norm_num)
theorem B3481697 : Blo 2061435 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B2321131 : Blo 2061435 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B3094841 : Blo 2061435 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B2063227 : Blo 2061435 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B4769813 : Blo 2061435 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B12719501 : Blo 2061435 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B8479667 : Blo 2061435 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B5653111 : Blo 2061435 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B7537481 : Blo 2061435 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B5024987 : Blo 2061435 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B3349991 : Blo 2061435 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B2233327 : Blo 2061435 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2977769 : Blo 2061435 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B7940717 : Blo 2061435 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B5293811 : Blo 2061435 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B3529207 : Blo 2061435 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B4705609 : Blo 2061435 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B6274145 : Blo 2061435 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B4182763 : Blo 2061435 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B5577017 : Blo 2061435 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B14872045 : Blo 2061435 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B19829393 : Blo 2061435 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B13219595 : Blo 2061435 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B8813063 : Blo 2061435 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B23501501 : Blo 2061435 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B15667667 : Blo 2061435 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B10445111 : Blo 2061435 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B6963407 : Blo 2061435 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B4642271 : Blo 2061435 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B3094847 : Blo 2061435 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B2063231 : Blo 2061435 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B3094853 : Blo 2061435 3094853 := bbase (se 4 (by rfl) ⟨290142, by rfl⟩ : syracuseStep 3094853 = 580285) (by norm_num)
theorem B2063235 : Blo 2061435 2063235 := bstep (se 1 (by rfl) ⟨1547426, by rfl⟩ : syracuseStep 2063235 = 3094853) B3094853
theorem B3481717 : Blo 2061435 3481717 := bbase (se 5 (by rfl) ⟨163205, by rfl⟩ : syracuseStep 3481717 = 326411) (by norm_num)
theorem B4642289 : Blo 2061435 4642289 := bstep (se 2 (by rfl) ⟨1740858, by rfl⟩ : syracuseStep 4642289 = 3481717) B3481717
theorem B3094859 : Blo 2061435 3094859 := bstep (se 1 (by rfl) ⟨2321144, by rfl⟩ : syracuseStep 3094859 = 4642289) B4642289
theorem B2063239 : Blo 2061435 2063239 := bstep (se 1 (by rfl) ⟨1547429, by rfl⟩ : syracuseStep 2063239 = 3094859) B3094859
theorem B2321149 : Blo 2061435 2321149 := bbase (se 3 (by rfl) ⟨435215, by rfl⟩ : syracuseStep 2321149 = 870431) (by norm_num)
theorem B3094865 : Blo 2061435 3094865 := bstep (se 2 (by rfl) ⟨1160574, by rfl⟩ : syracuseStep 3094865 = 2321149) B2321149
theorem B2063243 : Blo 2061435 2063243 := bstep (se 1 (by rfl) ⟨1547432, by rfl⟩ : syracuseStep 2063243 = 3094865) B3094865
theorem B6963461 : Blo 2061435 6963461 := bbase (se 4 (by rfl) ⟨652824, by rfl⟩ : syracuseStep 6963461 = 1305649) (by norm_num)
theorem B4642307 : Blo 2061435 4642307 := bstep (se 1 (by rfl) ⟨3481730, by rfl⟩ : syracuseStep 4642307 = 6963461) B6963461
theorem B3094871 : Blo 2061435 3094871 := bstep (se 1 (by rfl) ⟨2321153, by rfl⟩ : syracuseStep 3094871 = 4642307) B4642307
theorem B2063247 : Blo 2061435 2063247 := bstep (se 1 (by rfl) ⟨1547435, by rfl⟩ : syracuseStep 2063247 = 3094871) B3094871
theorem B3094877 : Blo 2061435 3094877 := bbase (se 3 (by rfl) ⟨580289, by rfl⟩ : syracuseStep 3094877 = 1160579) (by norm_num)
theorem B2063251 : Blo 2061435 2063251 := bstep (se 1 (by rfl) ⟨1547438, by rfl⟩ : syracuseStep 2063251 = 3094877) B3094877
theorem B4642325 : Blo 2061435 4642325 := bbase (se 6 (by rfl) ⟨108804, by rfl⟩ : syracuseStep 4642325 = 217609) (by norm_num)
theorem B3094883 : Blo 2061435 3094883 := bstep (se 1 (by rfl) ⟨2321162, by rfl⟩ : syracuseStep 3094883 = 4642325) B4642325
theorem B2063255 : Blo 2061435 2063255 := bstep (se 1 (by rfl) ⟨1547441, by rfl⟩ : syracuseStep 2063255 = 3094883) B3094883
theorem B7833941 : Blo 2061435 7833941 := bbase (se 10 (by rfl) ⟨11475, by rfl⟩ : syracuseStep 7833941 = 22951) (by norm_num)
theorem B5222627 : Blo 2061435 5222627 := bstep (se 1 (by rfl) ⟨3916970, by rfl⟩ : syracuseStep 5222627 = 7833941) B7833941
theorem B3481751 : Blo 2061435 3481751 := bstep (se 1 (by rfl) ⟨2611313, by rfl⟩ : syracuseStep 3481751 = 5222627) B5222627
theorem B2321167 : Blo 2061435 2321167 := bstep (se 1 (by rfl) ⟨1740875, by rfl⟩ : syracuseStep 2321167 = 3481751) B3481751
theorem B3094889 : Blo 2061435 3094889 := bstep (se 2 (by rfl) ⟨1160583, by rfl⟩ : syracuseStep 3094889 = 2321167) B2321167
theorem B2063259 : Blo 2061435 2063259 := bstep (se 1 (by rfl) ⟨1547444, by rfl⟩ : syracuseStep 2063259 = 3094889) B3094889
theorem B11750933 : Blo 2061435 11750933 := bbase (se 6 (by rfl) ⟨275412, by rfl⟩ : syracuseStep 11750933 = 550825) (by norm_num)
theorem B7833955 : Blo 2061435 7833955 := bstep (se 1 (by rfl) ⟨5875466, by rfl⟩ : syracuseStep 7833955 = 11750933) B11750933
theorem B10445273 : Blo 2061435 10445273 := bstep (se 2 (by rfl) ⟨3916977, by rfl⟩ : syracuseStep 10445273 = 7833955) B7833955
theorem B6963515 : Blo 2061435 6963515 := bstep (se 1 (by rfl) ⟨5222636, by rfl⟩ : syracuseStep 6963515 = 10445273) B10445273
theorem B4642343 : Blo 2061435 4642343 := bstep (se 1 (by rfl) ⟨3481757, by rfl⟩ : syracuseStep 4642343 = 6963515) B6963515
theorem B3094895 : Blo 2061435 3094895 := bstep (se 1 (by rfl) ⟨2321171, by rfl⟩ : syracuseStep 3094895 = 4642343) B4642343
theorem B2063263 : Blo 2061435 2063263 := bstep (se 1 (by rfl) ⟨1547447, by rfl⟩ : syracuseStep 2063263 = 3094895) B3094895
theorem B3094901 : Blo 2061435 3094901 := bbase (se 5 (by rfl) ⟨145073, by rfl⟩ : syracuseStep 3094901 = 290147) (by norm_num)
theorem B2063267 : Blo 2061435 2063267 := bstep (se 1 (by rfl) ⟨1547450, by rfl⟩ : syracuseStep 2063267 = 3094901) B3094901
theorem B2203309 : Blo 2061435 2203309 := bbase (se 3 (by rfl) ⟨413120, by rfl⟩ : syracuseStep 2203309 = 826241) (by norm_num)
theorem B2937745 : Blo 2061435 2937745 := bstep (se 2 (by rfl) ⟨1101654, by rfl⟩ : syracuseStep 2937745 = 2203309) B2203309
theorem B3916993 : Blo 2061435 3916993 := bstep (se 2 (by rfl) ⟨1468872, by rfl⟩ : syracuseStep 3916993 = 2937745) B2937745
theorem B5222657 : Blo 2061435 5222657 := bstep (se 2 (by rfl) ⟨1958496, by rfl⟩ : syracuseStep 5222657 = 3916993) B3916993
theorem B3481771 : Blo 2061435 3481771 := bstep (se 1 (by rfl) ⟨2611328, by rfl⟩ : syracuseStep 3481771 = 5222657) B5222657
theorem B4642361 : Blo 2061435 4642361 := bstep (se 2 (by rfl) ⟨1740885, by rfl⟩ : syracuseStep 4642361 = 3481771) B3481771
theorem B3094907 : Blo 2061435 3094907 := bstep (se 1 (by rfl) ⟨2321180, by rfl⟩ : syracuseStep 3094907 = 4642361) B4642361
theorem B2063271 : Blo 2061435 2063271 := bstep (se 1 (by rfl) ⟨1547453, by rfl⟩ : syracuseStep 2063271 = 3094907) B3094907
theorem B2321185 : Blo 2061435 2321185 := bbase (se 2 (by rfl) ⟨870444, by rfl⟩ : syracuseStep 2321185 = 1740889) (by norm_num)
theorem B3094913 : Blo 2061435 3094913 := bstep (se 2 (by rfl) ⟨1160592, by rfl⟩ : syracuseStep 3094913 = 2321185) B2321185
theorem B2063275 : Blo 2061435 2063275 := bstep (se 1 (by rfl) ⟨1547456, by rfl⟩ : syracuseStep 2063275 = 3094913) B3094913
theorem B5222677 : Blo 2061435 5222677 := bbase (se 6 (by rfl) ⟨122406, by rfl⟩ : syracuseStep 5222677 = 244813) (by norm_num)
theorem B6963569 : Blo 2061435 6963569 := bstep (se 2 (by rfl) ⟨2611338, by rfl⟩ : syracuseStep 6963569 = 5222677) B5222677
theorem B4642379 : Blo 2061435 4642379 := bstep (se 1 (by rfl) ⟨3481784, by rfl⟩ : syracuseStep 4642379 = 6963569) B6963569
theorem B3094919 : Blo 2061435 3094919 := bstep (se 1 (by rfl) ⟨2321189, by rfl⟩ : syracuseStep 3094919 = 4642379) B4642379
theorem B2063279 : Blo 2061435 2063279 := bstep (se 1 (by rfl) ⟨1547459, by rfl⟩ : syracuseStep 2063279 = 3094919) B3094919
theorem B3094925 : Blo 2061435 3094925 := bbase (se 3 (by rfl) ⟨580298, by rfl⟩ : syracuseStep 3094925 = 1160597) (by norm_num)
theorem B2063283 : Blo 2061435 2063283 := bstep (se 1 (by rfl) ⟨1547462, by rfl⟩ : syracuseStep 2063283 = 3094925) B3094925
theorem B4642397 : Blo 2061435 4642397 := bbase (se 3 (by rfl) ⟨870449, by rfl⟩ : syracuseStep 4642397 = 1740899) (by norm_num)
theorem B3094931 : Blo 2061435 3094931 := bstep (se 1 (by rfl) ⟨2321198, by rfl⟩ : syracuseStep 3094931 = 4642397) B4642397
theorem B2063287 : Blo 2061435 2063287 := bstep (se 1 (by rfl) ⟨1547465, by rfl⟩ : syracuseStep 2063287 = 3094931) B3094931
theorem B3481805 : Blo 2061435 3481805 := bbase (se 3 (by rfl) ⟨652838, by rfl⟩ : syracuseStep 3481805 = 1305677) (by norm_num)
theorem B2321203 : Blo 2061435 2321203 := bstep (se 1 (by rfl) ⟨1740902, by rfl⟩ : syracuseStep 2321203 = 3481805) B3481805
theorem B3094937 : Blo 2061435 3094937 := bstep (se 2 (by rfl) ⟨1160601, by rfl⟩ : syracuseStep 3094937 = 2321203) B2321203
theorem B2063291 : Blo 2061435 2063291 := bstep (se 1 (by rfl) ⟨1547468, by rfl⟩ : syracuseStep 2063291 = 3094937) B3094937
theorem B11911445 : Blo 2061435 11911445 := bbase (se 6 (by rfl) ⟨279174, by rfl⟩ : syracuseStep 11911445 = 558349) (by norm_num)
theorem B7940963 : Blo 2061435 7940963 := bstep (se 1 (by rfl) ⟨5955722, by rfl⟩ : syracuseStep 7940963 = 11911445) B11911445
theorem B21175901 : Blo 2061435 21175901 := bstep (se 3 (by rfl) ⟨3970481, by rfl⟩ : syracuseStep 21175901 = 7940963) B7940963
theorem B14117267 : Blo 2061435 14117267 := bstep (se 1 (by rfl) ⟨10587950, by rfl⟩ : syracuseStep 14117267 = 21175901) B21175901
theorem B9411511 : Blo 2061435 9411511 := bstep (se 1 (by rfl) ⟨7058633, by rfl⟩ : syracuseStep 9411511 = 14117267) B14117267
theorem B12548681 : Blo 2061435 12548681 := bstep (se 2 (by rfl) ⟨4705755, by rfl⟩ : syracuseStep 12548681 = 9411511) B9411511
theorem B8365787 : Blo 2061435 8365787 := bstep (se 1 (by rfl) ⟨6274340, by rfl⟩ : syracuseStep 8365787 = 12548681) B12548681
theorem B5577191 : Blo 2061435 5577191 := bstep (se 1 (by rfl) ⟨4182893, by rfl⟩ : syracuseStep 5577191 = 8365787) B8365787
theorem B3718127 : Blo 2061435 3718127 := bstep (se 1 (by rfl) ⟨2788595, by rfl⟩ : syracuseStep 3718127 = 5577191) B5577191
theorem B2478751 : Blo 2061435 2478751 := bstep (se 1 (by rfl) ⟨1859063, by rfl⟩ : syracuseStep 2478751 = 3718127) B3718127
theorem B13220005 : Blo 2061435 13220005 := bstep (se 4 (by rfl) ⟨1239375, by rfl⟩ : syracuseStep 13220005 = 2478751) B2478751
theorem B17626673 : Blo 2061435 17626673 := bstep (se 2 (by rfl) ⟨6610002, by rfl⟩ : syracuseStep 17626673 = 13220005) B13220005
theorem B11751115 : Blo 2061435 11751115 := bstep (se 1 (by rfl) ⟨8813336, by rfl⟩ : syracuseStep 11751115 = 17626673) B17626673
theorem B15668153 : Blo 2061435 15668153 := bstep (se 2 (by rfl) ⟨5875557, by rfl⟩ : syracuseStep 15668153 = 11751115) B11751115
theorem B10445435 : Blo 2061435 10445435 := bstep (se 1 (by rfl) ⟨7834076, by rfl⟩ : syracuseStep 10445435 = 15668153) B15668153
theorem B6963623 : Blo 2061435 6963623 := bstep (se 1 (by rfl) ⟨5222717, by rfl⟩ : syracuseStep 6963623 = 10445435) B10445435
theorem B4642415 : Blo 2061435 4642415 := bstep (se 1 (by rfl) ⟨3481811, by rfl⟩ : syracuseStep 4642415 = 6963623) B6963623
theorem B3094943 : Blo 2061435 3094943 := bstep (se 1 (by rfl) ⟨2321207, by rfl⟩ : syracuseStep 3094943 = 4642415) B4642415
theorem B2063295 : Blo 2061435 2063295 := bstep (se 1 (by rfl) ⟨1547471, by rfl⟩ : syracuseStep 2063295 = 3094943) B3094943
theorem B3094949 : Blo 2061435 3094949 := bbase (se 4 (by rfl) ⟨290151, by rfl⟩ : syracuseStep 3094949 = 580303) (by norm_num)
theorem B2063299 : Blo 2061435 2063299 := bstep (se 1 (by rfl) ⟨1547474, by rfl⟩ : syracuseStep 2063299 = 3094949) B3094949
theorem B2611369 : Blo 2061435 2611369 := bbase (se 2 (by rfl) ⟨979263, by rfl⟩ : syracuseStep 2611369 = 1958527) (by norm_num)
theorem B3481825 : Blo 2061435 3481825 := bstep (se 2 (by rfl) ⟨1305684, by rfl⟩ : syracuseStep 3481825 = 2611369) B2611369
theorem B4642433 : Blo 2061435 4642433 := bstep (se 2 (by rfl) ⟨1740912, by rfl⟩ : syracuseStep 4642433 = 3481825) B3481825
theorem B3094955 : Blo 2061435 3094955 := bstep (se 1 (by rfl) ⟨2321216, by rfl⟩ : syracuseStep 3094955 = 4642433) B4642433
theorem B2063303 : Blo 2061435 2063303 := bstep (se 1 (by rfl) ⟨1547477, by rfl⟩ : syracuseStep 2063303 = 3094955) B3094955
theorem B2321221 : Blo 2061435 2321221 := bbase (se 4 (by rfl) ⟨217614, by rfl⟩ : syracuseStep 2321221 = 435229) (by norm_num)
theorem B3094961 : Blo 2061435 3094961 := bstep (se 2 (by rfl) ⟨1160610, by rfl⟩ : syracuseStep 3094961 = 2321221) B2321221
theorem B2063307 : Blo 2061435 2063307 := bstep (se 1 (by rfl) ⟨1547480, by rfl⟩ : syracuseStep 2063307 = 3094961) B3094961
theorem B3917069 : Blo 2061435 3917069 := bbase (se 3 (by rfl) ⟨734450, by rfl⟩ : syracuseStep 3917069 = 1468901) (by norm_num)
theorem B2611379 : Blo 2061435 2611379 := bstep (se 1 (by rfl) ⟨1958534, by rfl⟩ : syracuseStep 2611379 = 3917069) B3917069
theorem B6963677 : Blo 2061435 6963677 := bstep (se 3 (by rfl) ⟨1305689, by rfl⟩ : syracuseStep 6963677 = 2611379) B2611379
theorem B4642451 : Blo 2061435 4642451 := bstep (se 1 (by rfl) ⟨3481838, by rfl⟩ : syracuseStep 4642451 = 6963677) B6963677
theorem B3094967 : Blo 2061435 3094967 := bstep (se 1 (by rfl) ⟨2321225, by rfl⟩ : syracuseStep 3094967 = 4642451) B4642451
theorem B2063311 : Blo 2061435 2063311 := bstep (se 1 (by rfl) ⟨1547483, by rfl⟩ : syracuseStep 2063311 = 3094967) B3094967
theorem B3094973 : Blo 2061435 3094973 := bbase (se 3 (by rfl) ⟨580307, by rfl⟩ : syracuseStep 3094973 = 1160615) (by norm_num)
theorem B2063315 : Blo 2061435 2063315 := bstep (se 1 (by rfl) ⟨1547486, by rfl⟩ : syracuseStep 2063315 = 3094973) B3094973
theorem B4642469 : Blo 2061435 4642469 := bbase (se 4 (by rfl) ⟨435231, by rfl⟩ : syracuseStep 4642469 = 870463) (by norm_num)
theorem B3094979 : Blo 2061435 3094979 := bstep (se 1 (by rfl) ⟨2321234, by rfl⟩ : syracuseStep 3094979 = 4642469) B4642469
theorem B2063319 : Blo 2061435 2063319 := bstep (se 1 (by rfl) ⟨1547489, by rfl⟩ : syracuseStep 2063319 = 3094979) B3094979
theorem B5222789 : Blo 2061435 5222789 := bbase (se 4 (by rfl) ⟨489636, by rfl⟩ : syracuseStep 5222789 = 979273) (by norm_num)
theorem B3481859 : Blo 2061435 3481859 := bstep (se 1 (by rfl) ⟨2611394, by rfl⟩ : syracuseStep 3481859 = 5222789) B5222789
theorem B2321239 : Blo 2061435 2321239 := bstep (se 1 (by rfl) ⟨1740929, by rfl⟩ : syracuseStep 2321239 = 3481859) B3481859
theorem B3094985 : Blo 2061435 3094985 := bstep (se 2 (by rfl) ⟨1160619, by rfl⟩ : syracuseStep 3094985 = 2321239) B2321239
theorem B2063323 : Blo 2061435 2063323 := bstep (se 1 (by rfl) ⟨1547492, by rfl⟩ : syracuseStep 2063323 = 3094985) B3094985
theorem B3305053 : Blo 2061435 3305053 := bbase (se 3 (by rfl) ⟨619697, by rfl⟩ : syracuseStep 3305053 = 1239395) (by norm_num)
theorem B4406737 : Blo 2061435 4406737 := bstep (se 2 (by rfl) ⟨1652526, by rfl⟩ : syracuseStep 4406737 = 3305053) B3305053
theorem B5875649 : Blo 2061435 5875649 := bstep (se 2 (by rfl) ⟨2203368, by rfl⟩ : syracuseStep 5875649 = 4406737) B4406737
theorem B3917099 : Blo 2061435 3917099 := bstep (se 1 (by rfl) ⟨2937824, by rfl⟩ : syracuseStep 3917099 = 5875649) B5875649
theorem B10445597 : Blo 2061435 10445597 := bstep (se 3 (by rfl) ⟨1958549, by rfl⟩ : syracuseStep 10445597 = 3917099) B3917099
theorem B6963731 : Blo 2061435 6963731 := bstep (se 1 (by rfl) ⟨5222798, by rfl⟩ : syracuseStep 6963731 = 10445597) B10445597
theorem B4642487 : Blo 2061435 4642487 := bstep (se 1 (by rfl) ⟨3481865, by rfl⟩ : syracuseStep 4642487 = 6963731) B6963731
theorem B3094991 : Blo 2061435 3094991 := bstep (se 1 (by rfl) ⟨2321243, by rfl⟩ : syracuseStep 3094991 = 4642487) B4642487
theorem B2063327 : Blo 2061435 2063327 := bstep (se 1 (by rfl) ⟨1547495, by rfl⟩ : syracuseStep 2063327 = 3094991) B3094991
theorem B3094997 : Blo 2061435 3094997 := bbase (se 7 (by rfl) ⟨36269, by rfl⟩ : syracuseStep 3094997 = 72539) (by norm_num)
theorem B2063331 : Blo 2061435 2063331 := bstep (se 1 (by rfl) ⟨1547498, by rfl⟩ : syracuseStep 2063331 = 3094997) B3094997
theorem B7834229 : Blo 2061435 7834229 := bbase (se 5 (by rfl) ⟨367229, by rfl⟩ : syracuseStep 7834229 = 734459) (by norm_num)
theorem B5222819 : Blo 2061435 5222819 := bstep (se 1 (by rfl) ⟨3917114, by rfl⟩ : syracuseStep 5222819 = 7834229) B7834229
theorem B3481879 : Blo 2061435 3481879 := bstep (se 1 (by rfl) ⟨2611409, by rfl⟩ : syracuseStep 3481879 = 5222819) B5222819
theorem B4642505 : Blo 2061435 4642505 := bstep (se 2 (by rfl) ⟨1740939, by rfl⟩ : syracuseStep 4642505 = 3481879) B3481879
theorem B3095003 : Blo 2061435 3095003 := bstep (se 1 (by rfl) ⟨2321252, by rfl⟩ : syracuseStep 3095003 = 4642505) B4642505
theorem B2063335 : Blo 2061435 2063335 := bstep (se 1 (by rfl) ⟨1547501, by rfl⟩ : syracuseStep 2063335 = 3095003) B3095003
theorem B2321257 : Blo 2061435 2321257 := bbase (se 2 (by rfl) ⟨870471, by rfl⟩ : syracuseStep 2321257 = 1740943) (by norm_num)
theorem B3095009 : Blo 2061435 3095009 := bstep (se 2 (by rfl) ⟨1160628, by rfl⟩ : syracuseStep 3095009 = 2321257) B2321257
theorem B2063339 : Blo 2061435 2063339 := bstep (se 1 (by rfl) ⟨1547504, by rfl⟩ : syracuseStep 2063339 = 3095009) B3095009
theorem B2478809 : Blo 2061435 2478809 := bbase (se 2 (by rfl) ⟨929553, by rfl⟩ : syracuseStep 2478809 = 1859107) (by norm_num)
theorem B6610157 : Blo 2061435 6610157 := bstep (se 3 (by rfl) ⟨1239404, by rfl⟩ : syracuseStep 6610157 = 2478809) B2478809
theorem B4406771 : Blo 2061435 4406771 := bstep (se 1 (by rfl) ⟨3305078, by rfl⟩ : syracuseStep 4406771 = 6610157) B6610157
theorem B11751389 : Blo 2061435 11751389 := bstep (se 3 (by rfl) ⟨2203385, by rfl⟩ : syracuseStep 11751389 = 4406771) B4406771
theorem B7834259 : Blo 2061435 7834259 := bstep (se 1 (by rfl) ⟨5875694, by rfl⟩ : syracuseStep 7834259 = 11751389) B11751389
theorem B5222839 : Blo 2061435 5222839 := bstep (se 1 (by rfl) ⟨3917129, by rfl⟩ : syracuseStep 5222839 = 7834259) B7834259
theorem B6963785 : Blo 2061435 6963785 := bstep (se 2 (by rfl) ⟨2611419, by rfl⟩ : syracuseStep 6963785 = 5222839) B5222839
theorem B4642523 : Blo 2061435 4642523 := bstep (se 1 (by rfl) ⟨3481892, by rfl⟩ : syracuseStep 4642523 = 6963785) B6963785
theorem B3095015 : Blo 2061435 3095015 := bstep (se 1 (by rfl) ⟨2321261, by rfl⟩ : syracuseStep 3095015 = 4642523) B4642523
theorem B2063343 : Blo 2061435 2063343 := bstep (se 1 (by rfl) ⟨1547507, by rfl⟩ : syracuseStep 2063343 = 3095015) B3095015
theorem B3095021 : Blo 2061435 3095021 := bbase (se 3 (by rfl) ⟨580316, by rfl⟩ : syracuseStep 3095021 = 1160633) (by norm_num)
theorem B2063347 : Blo 2061435 2063347 := bstep (se 1 (by rfl) ⟨1547510, by rfl⟩ : syracuseStep 2063347 = 3095021) B3095021
theorem B4642541 : Blo 2061435 4642541 := bbase (se 3 (by rfl) ⟨870476, by rfl⟩ : syracuseStep 4642541 = 1740953) (by norm_num)
theorem B3095027 : Blo 2061435 3095027 := bstep (se 1 (by rfl) ⟨2321270, by rfl⟩ : syracuseStep 3095027 = 4642541) B4642541
theorem B2063351 : Blo 2061435 2063351 := bstep (se 1 (by rfl) ⟨1547513, by rfl⟩ : syracuseStep 2063351 = 3095027) B3095027
theorem B3718237 : Blo 2061435 3718237 := bbase (se 3 (by rfl) ⟨697169, by rfl⟩ : syracuseStep 3718237 = 1394339) (by norm_num)
theorem B4957649 : Blo 2061435 4957649 := bstep (se 2 (by rfl) ⟨1859118, by rfl⟩ : syracuseStep 4957649 = 3718237) B3718237
theorem B3305099 : Blo 2061435 3305099 := bstep (se 1 (by rfl) ⟨2478824, by rfl⟩ : syracuseStep 3305099 = 4957649) B4957649
theorem B2203399 : Blo 2061435 2203399 := bstep (se 1 (by rfl) ⟨1652549, by rfl⟩ : syracuseStep 2203399 = 3305099) B3305099
theorem B2937865 : Blo 2061435 2937865 := bstep (se 2 (by rfl) ⟨1101699, by rfl⟩ : syracuseStep 2937865 = 2203399) B2203399
theorem B3917153 : Blo 2061435 3917153 := bstep (se 2 (by rfl) ⟨1468932, by rfl⟩ : syracuseStep 3917153 = 2937865) B2937865
theorem B2611435 : Blo 2061435 2611435 := bstep (se 1 (by rfl) ⟨1958576, by rfl⟩ : syracuseStep 2611435 = 3917153) B3917153
theorem B3481913 : Blo 2061435 3481913 := bstep (se 2 (by rfl) ⟨1305717, by rfl⟩ : syracuseStep 3481913 = 2611435) B2611435
theorem B2321275 : Blo 2061435 2321275 := bstep (se 1 (by rfl) ⟨1740956, by rfl⟩ : syracuseStep 2321275 = 3481913) B3481913
theorem B3095033 : Blo 2061435 3095033 := bstep (se 2 (by rfl) ⟨1160637, by rfl⟩ : syracuseStep 3095033 = 2321275) B2321275
theorem B2063355 : Blo 2061435 2063355 := bstep (se 1 (by rfl) ⟨1547516, by rfl⟩ : syracuseStep 2063355 = 3095033) B3095033
theorem B4240093 : Blo 2061435 4240093 := bbase (se 3 (by rfl) ⟨795017, by rfl⟩ : syracuseStep 4240093 = 1590035) (by norm_num)
theorem B5653457 : Blo 2061435 5653457 := bstep (se 2 (by rfl) ⟨2120046, by rfl⟩ : syracuseStep 5653457 = 4240093) B4240093
theorem B3768971 : Blo 2061435 3768971 := bstep (se 1 (by rfl) ⟨2826728, by rfl⟩ : syracuseStep 3768971 = 5653457) B5653457
theorem B10050589 : Blo 2061435 10050589 := bstep (se 3 (by rfl) ⟨1884485, by rfl⟩ : syracuseStep 10050589 = 3768971) B3768971
theorem B13400785 : Blo 2061435 13400785 := bstep (se 2 (by rfl) ⟨5025294, by rfl⟩ : syracuseStep 13400785 = 10050589) B10050589
theorem B71470853 : Blo 2061435 71470853 := bstep (se 4 (by rfl) ⟨6700392, by rfl⟩ : syracuseStep 71470853 = 13400785) B13400785
theorem B47647235 : Blo 2061435 47647235 := bstep (se 1 (by rfl) ⟨35735426, by rfl⟩ : syracuseStep 47647235 = 71470853) B71470853
theorem B127059293 : Blo 2061435 127059293 := bstep (se 3 (by rfl) ⟨23823617, by rfl⟩ : syracuseStep 127059293 = 47647235) B47647235
theorem B338824781 : Blo 2061435 338824781 := bstep (se 3 (by rfl) ⟨63529646, by rfl⟩ : syracuseStep 338824781 = 127059293) B127059293
theorem B225883187 : Blo 2061435 225883187 := bstep (se 1 (by rfl) ⟨169412390, by rfl⟩ : syracuseStep 225883187 = 338824781) B338824781
theorem B150588791 : Blo 2061435 150588791 := bstep (se 1 (by rfl) ⟨112941593, by rfl⟩ : syracuseStep 150588791 = 225883187) B225883187
theorem B100392527 : Blo 2061435 100392527 := bstep (se 1 (by rfl) ⟨75294395, by rfl⟩ : syracuseStep 100392527 = 150588791) B150588791
theorem B66928351 : Blo 2061435 66928351 := bstep (se 1 (by rfl) ⟨50196263, by rfl⟩ : syracuseStep 66928351 = 100392527) B100392527
theorem B89237801 : Blo 2061435 89237801 := bstep (se 2 (by rfl) ⟨33464175, by rfl⟩ : syracuseStep 89237801 = 66928351) B66928351
theorem B59491867 : Blo 2061435 59491867 := bstep (se 1 (by rfl) ⟨44618900, by rfl⟩ : syracuseStep 59491867 = 89237801) B89237801
theorem B79322489 : Blo 2061435 79322489 := bstep (se 2 (by rfl) ⟨29745933, by rfl⟩ : syracuseStep 79322489 = 59491867) B59491867
theorem B52881659 : Blo 2061435 52881659 := bstep (se 1 (by rfl) ⟨39661244, by rfl⟩ : syracuseStep 52881659 = 79322489) B79322489
theorem B35254439 : Blo 2061435 35254439 := bstep (se 1 (by rfl) ⟨26440829, by rfl⟩ : syracuseStep 35254439 = 52881659) B52881659
theorem B23502959 : Blo 2061435 23502959 := bstep (se 1 (by rfl) ⟨17627219, by rfl⟩ : syracuseStep 23502959 = 35254439) B35254439
theorem B15668639 : Blo 2061435 15668639 := bstep (se 1 (by rfl) ⟨11751479, by rfl⟩ : syracuseStep 15668639 = 23502959) B23502959
theorem B10445759 : Blo 2061435 10445759 := bstep (se 1 (by rfl) ⟨7834319, by rfl⟩ : syracuseStep 10445759 = 15668639) B15668639
theorem B6963839 : Blo 2061435 6963839 := bstep (se 1 (by rfl) ⟨5222879, by rfl⟩ : syracuseStep 6963839 = 10445759) B10445759
theorem B4642559 : Blo 2061435 4642559 := bstep (se 1 (by rfl) ⟨3481919, by rfl⟩ : syracuseStep 4642559 = 6963839) B6963839
theorem B3095039 : Blo 2061435 3095039 := bstep (se 1 (by rfl) ⟨2321279, by rfl⟩ : syracuseStep 3095039 = 4642559) B4642559
theorem B2063359 : Blo 2061435 2063359 := bstep (se 1 (by rfl) ⟨1547519, by rfl⟩ : syracuseStep 2063359 = 3095039) B3095039
theorem B3095045 : Blo 2061435 3095045 := bbase (se 4 (by rfl) ⟨290160, by rfl⟩ : syracuseStep 3095045 = 580321) (by norm_num)
theorem B2063363 : Blo 2061435 2063363 := bstep (se 1 (by rfl) ⟨1547522, by rfl⟩ : syracuseStep 2063363 = 3095045) B3095045
theorem B3481933 : Blo 2061435 3481933 := bbase (se 3 (by rfl) ⟨652862, by rfl⟩ : syracuseStep 3481933 = 1305725) (by norm_num)
theorem B4642577 : Blo 2061435 4642577 := bstep (se 2 (by rfl) ⟨1740966, by rfl⟩ : syracuseStep 4642577 = 3481933) B3481933
theorem B3095051 : Blo 2061435 3095051 := bstep (se 1 (by rfl) ⟨2321288, by rfl⟩ : syracuseStep 3095051 = 4642577) B4642577
theorem B2063367 : Blo 2061435 2063367 := bstep (se 1 (by rfl) ⟨1547525, by rfl⟩ : syracuseStep 2063367 = 3095051) B3095051
theorem B2321293 : Blo 2061435 2321293 := bbase (se 3 (by rfl) ⟨435242, by rfl⟩ : syracuseStep 2321293 = 870485) (by norm_num)
theorem B3095057 : Blo 2061435 3095057 := bstep (se 2 (by rfl) ⟨1160646, by rfl⟩ : syracuseStep 3095057 = 2321293) B2321293
theorem B2063371 : Blo 2061435 2063371 := bstep (se 1 (by rfl) ⟨1547528, by rfl⟩ : syracuseStep 2063371 = 3095057) B3095057
theorem B6963893 : Blo 2061435 6963893 := bbase (se 5 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 6963893 = 652865) (by norm_num)
theorem B4642595 : Blo 2061435 4642595 := bstep (se 1 (by rfl) ⟨3481946, by rfl⟩ : syracuseStep 4642595 = 6963893) B6963893
theorem B3095063 : Blo 2061435 3095063 := bstep (se 1 (by rfl) ⟨2321297, by rfl⟩ : syracuseStep 3095063 = 4642595) B4642595
theorem B2063375 : Blo 2061435 2063375 := bstep (se 1 (by rfl) ⟨1547531, by rfl⟩ : syracuseStep 2063375 = 3095063) B3095063
theorem B3095069 : Blo 2061435 3095069 := bbase (se 3 (by rfl) ⟨580325, by rfl⟩ : syracuseStep 3095069 = 1160651) (by norm_num)
theorem B2063379 : Blo 2061435 2063379 := bstep (se 1 (by rfl) ⟨1547534, by rfl⟩ : syracuseStep 2063379 = 3095069) B3095069
theorem B4642613 : Blo 2061435 4642613 := bbase (se 5 (by rfl) ⟨217622, by rfl⟩ : syracuseStep 4642613 = 435245) (by norm_num)
theorem B3095075 : Blo 2061435 3095075 := bstep (se 1 (by rfl) ⟨2321306, by rfl⟩ : syracuseStep 3095075 = 4642613) B4642613
theorem B2063383 : Blo 2061435 2063383 := bstep (se 1 (by rfl) ⟨1547537, by rfl⟩ : syracuseStep 2063383 = 3095075) B3095075
theorem B13220597 : Blo 2061435 13220597 := bbase (se 5 (by rfl) ⟨619715, by rfl⟩ : syracuseStep 13220597 = 1239431) (by norm_num)
theorem B8813731 : Blo 2061435 8813731 := bstep (se 1 (by rfl) ⟨6610298, by rfl⟩ : syracuseStep 8813731 = 13220597) B13220597
theorem B11751641 : Blo 2061435 11751641 := bstep (se 2 (by rfl) ⟨4406865, by rfl⟩ : syracuseStep 11751641 = 8813731) B8813731
theorem B7834427 : Blo 2061435 7834427 := bstep (se 1 (by rfl) ⟨5875820, by rfl⟩ : syracuseStep 7834427 = 11751641) B11751641
theorem B5222951 : Blo 2061435 5222951 := bstep (se 1 (by rfl) ⟨3917213, by rfl⟩ : syracuseStep 5222951 = 7834427) B7834427
theorem B3481967 : Blo 2061435 3481967 := bstep (se 1 (by rfl) ⟨2611475, by rfl⟩ : syracuseStep 3481967 = 5222951) B5222951
theorem B2321311 : Blo 2061435 2321311 := bstep (se 1 (by rfl) ⟨1740983, by rfl⟩ : syracuseStep 2321311 = 3481967) B3481967
theorem B3095081 : Blo 2061435 3095081 := bstep (se 2 (by rfl) ⟨1160655, by rfl⟩ : syracuseStep 3095081 = 2321311) B2321311
theorem B2063387 : Blo 2061435 2063387 := bstep (se 1 (by rfl) ⟨1547540, by rfl⟩ : syracuseStep 2063387 = 3095081) B3095081
theorem B4957733 : Blo 2061435 4957733 := bbase (se 4 (by rfl) ⟨464787, by rfl⟩ : syracuseStep 4957733 = 929575) (by norm_num)
theorem B13220621 : Blo 2061435 13220621 := bstep (se 3 (by rfl) ⟨2478866, by rfl⟩ : syracuseStep 13220621 = 4957733) B4957733
theorem B8813747 : Blo 2061435 8813747 := bstep (se 1 (by rfl) ⟨6610310, by rfl⟩ : syracuseStep 8813747 = 13220621) B13220621
theorem B5875831 : Blo 2061435 5875831 := bstep (se 1 (by rfl) ⟨4406873, by rfl⟩ : syracuseStep 5875831 = 8813747) B8813747
theorem B7834441 : Blo 2061435 7834441 := bstep (se 2 (by rfl) ⟨2937915, by rfl⟩ : syracuseStep 7834441 = 5875831) B5875831
theorem B10445921 : Blo 2061435 10445921 := bstep (se 2 (by rfl) ⟨3917220, by rfl⟩ : syracuseStep 10445921 = 7834441) B7834441
theorem B6963947 : Blo 2061435 6963947 := bstep (se 1 (by rfl) ⟨5222960, by rfl⟩ : syracuseStep 6963947 = 10445921) B10445921
theorem B4642631 : Blo 2061435 4642631 := bstep (se 1 (by rfl) ⟨3481973, by rfl⟩ : syracuseStep 4642631 = 6963947) B6963947
theorem B3095087 : Blo 2061435 3095087 := bstep (se 1 (by rfl) ⟨2321315, by rfl⟩ : syracuseStep 3095087 = 4642631) B4642631
theorem B2063391 : Blo 2061435 2063391 := bstep (se 1 (by rfl) ⟨1547543, by rfl⟩ : syracuseStep 2063391 = 3095087) B3095087
theorem B3095093 : Blo 2061435 3095093 := bbase (se 5 (by rfl) ⟨145082, by rfl⟩ : syracuseStep 3095093 = 290165) (by norm_num)
theorem B2063395 : Blo 2061435 2063395 := bstep (se 1 (by rfl) ⟨1547546, by rfl⟩ : syracuseStep 2063395 = 3095093) B3095093
theorem B5222981 : Blo 2061435 5222981 := bbase (se 4 (by rfl) ⟨489654, by rfl⟩ : syracuseStep 5222981 = 979309) (by norm_num)
theorem B3481987 : Blo 2061435 3481987 := bstep (se 1 (by rfl) ⟨2611490, by rfl⟩ : syracuseStep 3481987 = 5222981) B5222981
theorem B4642649 : Blo 2061435 4642649 := bstep (se 2 (by rfl) ⟨1740993, by rfl⟩ : syracuseStep 4642649 = 3481987) B3481987
theorem B3095099 : Blo 2061435 3095099 := bstep (se 1 (by rfl) ⟨2321324, by rfl⟩ : syracuseStep 3095099 = 4642649) B4642649
theorem B2063399 : Blo 2061435 2063399 := bstep (se 1 (by rfl) ⟨1547549, by rfl⟩ : syracuseStep 2063399 = 3095099) B3095099
theorem B2321329 : Blo 2061435 2321329 := bbase (se 2 (by rfl) ⟨870498, by rfl⟩ : syracuseStep 2321329 = 1740997) (by norm_num)
theorem B3095105 : Blo 2061435 3095105 := bstep (se 2 (by rfl) ⟨1160664, by rfl⟩ : syracuseStep 3095105 = 2321329) B2321329
theorem B2063403 : Blo 2061435 2063403 := bstep (se 1 (by rfl) ⟨1547552, by rfl⟩ : syracuseStep 2063403 = 3095105) B3095105
theorem B5875877 : Blo 2061435 5875877 := bbase (se 4 (by rfl) ⟨550863, by rfl⟩ : syracuseStep 5875877 = 1101727) (by norm_num)
theorem B3917251 : Blo 2061435 3917251 := bstep (se 1 (by rfl) ⟨2937938, by rfl⟩ : syracuseStep 3917251 = 5875877) B5875877
theorem B5223001 : Blo 2061435 5223001 := bstep (se 2 (by rfl) ⟨1958625, by rfl⟩ : syracuseStep 5223001 = 3917251) B3917251
theorem B6964001 : Blo 2061435 6964001 := bstep (se 2 (by rfl) ⟨2611500, by rfl⟩ : syracuseStep 6964001 = 5223001) B5223001
theorem B4642667 : Blo 2061435 4642667 := bstep (se 1 (by rfl) ⟨3482000, by rfl⟩ : syracuseStep 4642667 = 6964001) B6964001
theorem B3095111 : Blo 2061435 3095111 := bstep (se 1 (by rfl) ⟨2321333, by rfl⟩ : syracuseStep 3095111 = 4642667) B4642667
theorem B2063407 : Blo 2061435 2063407 := bstep (se 1 (by rfl) ⟨1547555, by rfl⟩ : syracuseStep 2063407 = 3095111) B3095111
theorem B3095117 : Blo 2061435 3095117 := bbase (se 3 (by rfl) ⟨580334, by rfl⟩ : syracuseStep 3095117 = 1160669) (by norm_num)
theorem B2063411 : Blo 2061435 2063411 := bstep (se 1 (by rfl) ⟨1547558, by rfl⟩ : syracuseStep 2063411 = 3095117) B3095117
theorem B4642685 : Blo 2061435 4642685 := bbase (se 3 (by rfl) ⟨870503, by rfl⟩ : syracuseStep 4642685 = 1741007) (by norm_num)
theorem B3095123 : Blo 2061435 3095123 := bstep (se 1 (by rfl) ⟨2321342, by rfl⟩ : syracuseStep 3095123 = 4642685) B4642685
theorem B2063415 : Blo 2061435 2063415 := bstep (se 1 (by rfl) ⟨1547561, by rfl⟩ : syracuseStep 2063415 = 3095123) B3095123
theorem B3482021 : Blo 2061435 3482021 := bbase (se 4 (by rfl) ⟨326439, by rfl⟩ : syracuseStep 3482021 = 652879) (by norm_num)
theorem B2321347 : Blo 2061435 2321347 := bstep (se 1 (by rfl) ⟨1741010, by rfl⟩ : syracuseStep 2321347 = 3482021) B3482021
theorem B3095129 : Blo 2061435 3095129 := bstep (se 2 (by rfl) ⟨1160673, by rfl⟩ : syracuseStep 3095129 = 2321347) B2321347
theorem B2063419 : Blo 2061435 2063419 := bstep (se 1 (by rfl) ⟨1547564, by rfl⟩ : syracuseStep 2063419 = 3095129) B3095129
theorem B2091577 : Blo 2061435 2091577 := bbase (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) (by norm_num)
theorem B2788769 : Blo 2061435 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B7436717 : Blo 2061435 7436717 := bstep (se 3 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 7436717 = 2788769) B2788769
theorem B4957811 : Blo 2061435 4957811 := bstep (se 1 (by rfl) ⟨3718358, by rfl⟩ : syracuseStep 4957811 = 7436717) B7436717
theorem B3305207 : Blo 2061435 3305207 := bstep (se 1 (by rfl) ⟨2478905, by rfl⟩ : syracuseStep 3305207 = 4957811) B4957811
theorem B2203471 : Blo 2061435 2203471 := bstep (se 1 (by rfl) ⟨1652603, by rfl⟩ : syracuseStep 2203471 = 3305207) B3305207
theorem B2937961 : Blo 2061435 2937961 := bstep (se 2 (by rfl) ⟨1101735, by rfl⟩ : syracuseStep 2937961 = 2203471) B2203471
theorem B15669125 : Blo 2061435 15669125 := bstep (se 4 (by rfl) ⟨1468980, by rfl⟩ : syracuseStep 15669125 = 2937961) B2937961
theorem B10446083 : Blo 2061435 10446083 := bstep (se 1 (by rfl) ⟨7834562, by rfl⟩ : syracuseStep 10446083 = 15669125) B15669125
theorem B6964055 : Blo 2061435 6964055 := bstep (se 1 (by rfl) ⟨5223041, by rfl⟩ : syracuseStep 6964055 = 10446083) B10446083
theorem B4642703 : Blo 2061435 4642703 := bstep (se 1 (by rfl) ⟨3482027, by rfl⟩ : syracuseStep 4642703 = 6964055) B6964055
theorem B3095135 : Blo 2061435 3095135 := bstep (se 1 (by rfl) ⟨2321351, by rfl⟩ : syracuseStep 3095135 = 4642703) B4642703
theorem B2063423 : Blo 2061435 2063423 := bstep (se 1 (by rfl) ⟨1547567, by rfl⟩ : syracuseStep 2063423 = 3095135) B3095135
theorem B3095141 : Blo 2061435 3095141 := bbase (se 4 (by rfl) ⟨290169, by rfl⟩ : syracuseStep 3095141 = 580339) (by norm_num)
theorem B2063427 : Blo 2061435 2063427 := bstep (se 1 (by rfl) ⟨1547570, by rfl⟩ : syracuseStep 2063427 = 3095141) B3095141
theorem B2937973 : Blo 2061435 2937973 := bbase (se 5 (by rfl) ⟨137717, by rfl⟩ : syracuseStep 2937973 = 275435) (by norm_num)
theorem B3917297 : Blo 2061435 3917297 := bstep (se 2 (by rfl) ⟨1468986, by rfl⟩ : syracuseStep 3917297 = 2937973) B2937973
theorem B2611531 : Blo 2061435 2611531 := bstep (se 1 (by rfl) ⟨1958648, by rfl⟩ : syracuseStep 2611531 = 3917297) B3917297
theorem B3482041 : Blo 2061435 3482041 := bstep (se 2 (by rfl) ⟨1305765, by rfl⟩ : syracuseStep 3482041 = 2611531) B2611531
theorem B4642721 : Blo 2061435 4642721 := bstep (se 2 (by rfl) ⟨1741020, by rfl⟩ : syracuseStep 4642721 = 3482041) B3482041
theorem B3095147 : Blo 2061435 3095147 := bstep (se 1 (by rfl) ⟨2321360, by rfl⟩ : syracuseStep 3095147 = 4642721) B4642721
theorem B2063431 : Blo 2061435 2063431 := bstep (se 1 (by rfl) ⟨1547573, by rfl⟩ : syracuseStep 2063431 = 3095147) B3095147
theorem B2321365 : Blo 2061435 2321365 := bbase (se 7 (by rfl) ⟨27203, by rfl⟩ : syracuseStep 2321365 = 54407) (by norm_num)
theorem B3095153 : Blo 2061435 3095153 := bstep (se 2 (by rfl) ⟨1160682, by rfl⟩ : syracuseStep 3095153 = 2321365) B2321365
theorem B2063435 : Blo 2061435 2063435 := bstep (se 1 (by rfl) ⟨1547576, by rfl⟩ : syracuseStep 2063435 = 3095153) B3095153
theorem C0 (j : ℕ) (h1 : 515358 ≤ j) (h2 : j ≤ 515858) : Blo 2061435 (4 * j + 3) := by
  interval_cases j
  · exact B2061435
  · exact B2061439
  · exact B2061443
  · exact B2061447
  · exact B2061451
  · exact B2061455
  · exact B2061459
  · exact B2061463
  · exact B2061467
  · exact B2061471
  · exact B2061475
  · exact B2061479
  · exact B2061483
  · exact B2061487
  · exact B2061491
  · exact B2061495
  · exact B2061499
  · exact B2061503
  · exact B2061507
  · exact B2061511
  · exact B2061515
  · exact B2061519
  · exact B2061523
  · exact B2061527
  · exact B2061531
  · exact B2061535
  · exact B2061539
  · exact B2061543
  · exact B2061547
  · exact B2061551
  · exact B2061555
  · exact B2061559
  · exact B2061563
  · exact B2061567
  · exact B2061571
  · exact B2061575
  · exact B2061579
  · exact B2061583
  · exact B2061587
  · exact B2061591
  · exact B2061595
  · exact B2061599
  · exact B2061603
  · exact B2061607
  · exact B2061611
  · exact B2061615
  · exact B2061619
  · exact B2061623
  · exact B2061627
  · exact B2061631
  · exact B2061635
  · exact B2061639
  · exact B2061643
  · exact B2061647
  · exact B2061651
  · exact B2061655
  · exact B2061659
  · exact B2061663
  · exact B2061667
  · exact B2061671
  · exact B2061675
  · exact B2061679
  · exact B2061683
  · exact B2061687
  · exact B2061691
  · exact B2061695
  · exact B2061699
  · exact B2061703
  · exact B2061707
  · exact B2061711
  · exact B2061715
  · exact B2061719
  · exact B2061723
  · exact B2061727
  · exact B2061731
  · exact B2061735
  · exact B2061739
  · exact B2061743
  · exact B2061747
  · exact B2061751
  · exact B2061755
  · exact B2061759
  · exact B2061763
  · exact B2061767
  · exact B2061771
  · exact B2061775
  · exact B2061779
  · exact B2061783
  · exact B2061787
  · exact B2061791
  · exact B2061795
  · exact B2061799
  · exact B2061803
  · exact B2061807
  · exact B2061811
  · exact B2061815
  · exact B2061819
  · exact B2061823
  · exact B2061827
  · exact B2061831
  · exact B2061835
  · exact B2061839
  · exact B2061843
  · exact B2061847
  · exact B2061851
  · exact B2061855
  · exact B2061859
  · exact B2061863
  · exact B2061867
  · exact B2061871
  · exact B2061875
  · exact B2061879
  · exact B2061883
  · exact B2061887
  · exact B2061891
  · exact B2061895
  · exact B2061899
  · exact B2061903
  · exact B2061907
  · exact B2061911
  · exact B2061915
  · exact B2061919
  · exact B2061923
  · exact B2061927
  · exact B2061931
  · exact B2061935
  · exact B2061939
  · exact B2061943
  · exact B2061947
  · exact B2061951
  · exact B2061955
  · exact B2061959
  · exact B2061963
  · exact B2061967
  · exact B2061971
  · exact B2061975
  · exact B2061979
  · exact B2061983
  · exact B2061987
  · exact B2061991
  · exact B2061995
  · exact B2061999
  · exact B2062003
  · exact B2062007
  · exact B2062011
  · exact B2062015
  · exact B2062019
  · exact B2062023
  · exact B2062027
  · exact B2062031
  · exact B2062035
  · exact B2062039
  · exact B2062043
  · exact B2062047
  · exact B2062051
  · exact B2062055
  · exact B2062059
  · exact B2062063
  · exact B2062067
  · exact B2062071
  · exact B2062075
  · exact B2062079
  · exact B2062083
  · exact B2062087
  · exact B2062091
  · exact B2062095
  · exact B2062099
  · exact B2062103
  · exact B2062107
  · exact B2062111
  · exact B2062115
  · exact B2062119
  · exact B2062123
  · exact B2062127
  · exact B2062131
  · exact B2062135
  · exact B2062139
  · exact B2062143
  · exact B2062147
  · exact B2062151
  · exact B2062155
  · exact B2062159
  · exact B2062163
  · exact B2062167
  · exact B2062171
  · exact B2062175
  · exact B2062179
  · exact B2062183
  · exact B2062187
  · exact B2062191
  · exact B2062195
  · exact B2062199
  · exact B2062203
  · exact B2062207
  · exact B2062211
  · exact B2062215
  · exact B2062219
  · exact B2062223
  · exact B2062227
  · exact B2062231
  · exact B2062235
  · exact B2062239
  · exact B2062243
  · exact B2062247
  · exact B2062251
  · exact B2062255
  · exact B2062259
  · exact B2062263
  · exact B2062267
  · exact B2062271
  · exact B2062275
  · exact B2062279
  · exact B2062283
  · exact B2062287
  · exact B2062291
  · exact B2062295
  · exact B2062299
  · exact B2062303
  · exact B2062307
  · exact B2062311
  · exact B2062315
  · exact B2062319
  · exact B2062323
  · exact B2062327
  · exact B2062331
  · exact B2062335
  · exact B2062339
  · exact B2062343
  · exact B2062347
  · exact B2062351
  · exact B2062355
  · exact B2062359
  · exact B2062363
  · exact B2062367
  · exact B2062371
  · exact B2062375
  · exact B2062379
  · exact B2062383
  · exact B2062387
  · exact B2062391
  · exact B2062395
  · exact B2062399
  · exact B2062403
  · exact B2062407
  · exact B2062411
  · exact B2062415
  · exact B2062419
  · exact B2062423
  · exact B2062427
  · exact B2062431
  · exact B2062435
  · exact B2062439
  · exact B2062443
  · exact B2062447
  · exact B2062451
  · exact B2062455
  · exact B2062459
  · exact B2062463
  · exact B2062467
  · exact B2062471
  · exact B2062475
  · exact B2062479
  · exact B2062483
  · exact B2062487
  · exact B2062491
  · exact B2062495
  · exact B2062499
  · exact B2062503
  · exact B2062507
  · exact B2062511
  · exact B2062515
  · exact B2062519
  · exact B2062523
  · exact B2062527
  · exact B2062531
  · exact B2062535
  · exact B2062539
  · exact B2062543
  · exact B2062547
  · exact B2062551
  · exact B2062555
  · exact B2062559
  · exact B2062563
  · exact B2062567
  · exact B2062571
  · exact B2062575
  · exact B2062579
  · exact B2062583
  · exact B2062587
  · exact B2062591
  · exact B2062595
  · exact B2062599
  · exact B2062603
  · exact B2062607
  · exact B2062611
  · exact B2062615
  · exact B2062619
  · exact B2062623
  · exact B2062627
  · exact B2062631
  · exact B2062635
  · exact B2062639
  · exact B2062643
  · exact B2062647
  · exact B2062651
  · exact B2062655
  · exact B2062659
  · exact B2062663
  · exact B2062667
  · exact B2062671
  · exact B2062675
  · exact B2062679
  · exact B2062683
  · exact B2062687
  · exact B2062691
  · exact B2062695
  · exact B2062699
  · exact B2062703
  · exact B2062707
  · exact B2062711
  · exact B2062715
  · exact B2062719
  · exact B2062723
  · exact B2062727
  · exact B2062731
  · exact B2062735
  · exact B2062739
  · exact B2062743
  · exact B2062747
  · exact B2062751
  · exact B2062755
  · exact B2062759
  · exact B2062763
  · exact B2062767
  · exact B2062771
  · exact B2062775
  · exact B2062779
  · exact B2062783
  · exact B2062787
  · exact B2062791
  · exact B2062795
  · exact B2062799
  · exact B2062803
  · exact B2062807
  · exact B2062811
  · exact B2062815
  · exact B2062819
  · exact B2062823
  · exact B2062827
  · exact B2062831
  · exact B2062835
  · exact B2062839
  · exact B2062843
  · exact B2062847
  · exact B2062851
  · exact B2062855
  · exact B2062859
  · exact B2062863
  · exact B2062867
  · exact B2062871
  · exact B2062875
  · exact B2062879
  · exact B2062883
  · exact B2062887
  · exact B2062891
  · exact B2062895
  · exact B2062899
  · exact B2062903
  · exact B2062907
  · exact B2062911
  · exact B2062915
  · exact B2062919
  · exact B2062923
  · exact B2062927
  · exact B2062931
  · exact B2062935
  · exact B2062939
  · exact B2062943
  · exact B2062947
  · exact B2062951
  · exact B2062955
  · exact B2062959
  · exact B2062963
  · exact B2062967
  · exact B2062971
  · exact B2062975
  · exact B2062979
  · exact B2062983
  · exact B2062987
  · exact B2062991
  · exact B2062995
  · exact B2062999
  · exact B2063003
  · exact B2063007
  · exact B2063011
  · exact B2063015
  · exact B2063019
  · exact B2063023
  · exact B2063027
  · exact B2063031
  · exact B2063035
  · exact B2063039
  · exact B2063043
  · exact B2063047
  · exact B2063051
  · exact B2063055
  · exact B2063059
  · exact B2063063
  · exact B2063067
  · exact B2063071
  · exact B2063075
  · exact B2063079
  · exact B2063083
  · exact B2063087
  · exact B2063091
  · exact B2063095
  · exact B2063099
  · exact B2063103
  · exact B2063107
  · exact B2063111
  · exact B2063115
  · exact B2063119
  · exact B2063123
  · exact B2063127
  · exact B2063131
  · exact B2063135
  · exact B2063139
  · exact B2063143
  · exact B2063147
  · exact B2063151
  · exact B2063155
  · exact B2063159
  · exact B2063163
  · exact B2063167
  · exact B2063171
  · exact B2063175
  · exact B2063179
  · exact B2063183
  · exact B2063187
  · exact B2063191
  · exact B2063195
  · exact B2063199
  · exact B2063203
  · exact B2063207
  · exact B2063211
  · exact B2063215
  · exact B2063219
  · exact B2063223
  · exact B2063227
  · exact B2063231
  · exact B2063235
  · exact B2063239
  · exact B2063243
  · exact B2063247
  · exact B2063251
  · exact B2063255
  · exact B2063259
  · exact B2063263
  · exact B2063267
  · exact B2063271
  · exact B2063275
  · exact B2063279
  · exact B2063283
  · exact B2063287
  · exact B2063291
  · exact B2063295
  · exact B2063299
  · exact B2063303
  · exact B2063307
  · exact B2063311
  · exact B2063315
  · exact B2063319
  · exact B2063323
  · exact B2063327
  · exact B2063331
  · exact B2063335
  · exact B2063339
  · exact B2063343
  · exact B2063347
  · exact B2063351
  · exact B2063355
  · exact B2063359
  · exact B2063363
  · exact B2063367
  · exact B2063371
  · exact B2063375
  · exact B2063379
  · exact B2063383
  · exact B2063387
  · exact B2063391
  · exact B2063395
  · exact B2063399
  · exact B2063403
  · exact B2063407
  · exact B2063411
  · exact B2063415
  · exact B2063419
  · exact B2063423
  · exact B2063427
  · exact B2063431
  · exact B2063435
theorem solution (m : ℕ) (hlo : 2061435 ≤ m) (hhi : m ≤ 2063435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 515358 ≤ j := by omega
    have hj2 : j ≤ 515858 := by omega
    have hb : Blo 2061435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
