-- Prove2me | solution 1 for syracuse_descends_range_2233435_2235435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:51.774524+00:00
-- url     : https://prove2.me/submissions/1428fe18-7709-43c3-a870-f89a3375ec7c

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

theorem B2546897 : Blo 2233435 2546897 := bbase (se 2 (by rfl) ⟨955086, by rfl⟩ : syracuseStep 2546897 = 1910173) (by norm_num)
theorem B6791725 : Blo 2233435 6791725 := bstep (se 3 (by rfl) ⟨1273448, by rfl⟩ : syracuseStep 6791725 = 2546897) B2546897
theorem B9055633 : Blo 2233435 9055633 := bstep (se 2 (by rfl) ⟨3395862, by rfl⟩ : syracuseStep 9055633 = 6791725) B6791725
theorem B12074177 : Blo 2233435 12074177 := bstep (se 2 (by rfl) ⟨4527816, by rfl⟩ : syracuseStep 12074177 = 9055633) B9055633
theorem B8049451 : Blo 2233435 8049451 := bstep (se 1 (by rfl) ⟨6037088, by rfl⟩ : syracuseStep 8049451 = 12074177) B12074177
theorem B10732601 : Blo 2233435 10732601 := bstep (se 2 (by rfl) ⟨4024725, by rfl⟩ : syracuseStep 10732601 = 8049451) B8049451
theorem B7155067 : Blo 2233435 7155067 := bstep (se 1 (by rfl) ⟨5366300, by rfl⟩ : syracuseStep 7155067 = 10732601) B10732601
theorem B9540089 : Blo 2233435 9540089 := bstep (se 2 (by rfl) ⟨3577533, by rfl⟩ : syracuseStep 9540089 = 7155067) B7155067
theorem B6360059 : Blo 2233435 6360059 := bstep (se 1 (by rfl) ⟨4770044, by rfl⟩ : syracuseStep 6360059 = 9540089) B9540089
theorem B4240039 : Blo 2233435 4240039 := bstep (se 1 (by rfl) ⟨3180029, by rfl⟩ : syracuseStep 4240039 = 6360059) B6360059
theorem B5653385 : Blo 2233435 5653385 := bstep (se 2 (by rfl) ⟨2120019, by rfl⟩ : syracuseStep 5653385 = 4240039) B4240039
theorem B3768923 : Blo 2233435 3768923 := bstep (se 1 (by rfl) ⟨2826692, by rfl⟩ : syracuseStep 3768923 = 5653385) B5653385
theorem B2512615 : Blo 2233435 2512615 := bstep (se 1 (by rfl) ⟨1884461, by rfl⟩ : syracuseStep 2512615 = 3768923) B3768923
theorem B3350153 : Blo 2233435 3350153 := bstep (se 2 (by rfl) ⟨1256307, by rfl⟩ : syracuseStep 3350153 = 2512615) B2512615
theorem B2233435 : Blo 2233435 2233435 := bstep (se 1 (by rfl) ⟨1675076, by rfl⟩ : syracuseStep 2233435 = 3350153) B3350153
theorem B11306789 : Blo 2233435 11306789 := bbase (se 4 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 11306789 = 2120023) (by norm_num)
theorem B7537859 : Blo 2233435 7537859 := bstep (se 1 (by rfl) ⟨5653394, by rfl⟩ : syracuseStep 7537859 = 11306789) B11306789
theorem B5025239 : Blo 2233435 5025239 := bstep (se 1 (by rfl) ⟨3768929, by rfl⟩ : syracuseStep 5025239 = 7537859) B7537859
theorem B3350159 : Blo 2233435 3350159 := bstep (se 1 (by rfl) ⟨2512619, by rfl⟩ : syracuseStep 3350159 = 5025239) B5025239
theorem B2233439 : Blo 2233435 2233439 := bstep (se 1 (by rfl) ⟨1675079, by rfl⟩ : syracuseStep 2233439 = 3350159) B3350159
theorem B3350165 : Blo 2233435 3350165 := bbase (se 6 (by rfl) ⟨78519, by rfl⟩ : syracuseStep 3350165 = 157039) (by norm_num)
theorem B2233443 : Blo 2233435 2233443 := bstep (se 1 (by rfl) ⟨1675082, by rfl⟩ : syracuseStep 2233443 = 3350165) B3350165
theorem B8049493 : Blo 2233435 8049493 := bbase (se 9 (by rfl) ⟨23582, by rfl⟩ : syracuseStep 8049493 = 47165) (by norm_num)
theorem B10732657 : Blo 2233435 10732657 := bstep (se 2 (by rfl) ⟨4024746, by rfl⟩ : syracuseStep 10732657 = 8049493) B8049493
theorem B14310209 : Blo 2233435 14310209 := bstep (se 2 (by rfl) ⟨5366328, by rfl⟩ : syracuseStep 14310209 = 10732657) B10732657
theorem B9540139 : Blo 2233435 9540139 := bstep (se 1 (by rfl) ⟨7155104, by rfl⟩ : syracuseStep 9540139 = 14310209) B14310209
theorem B12720185 : Blo 2233435 12720185 := bstep (se 2 (by rfl) ⟨4770069, by rfl⟩ : syracuseStep 12720185 = 9540139) B9540139
theorem B8480123 : Blo 2233435 8480123 := bstep (se 1 (by rfl) ⟨6360092, by rfl⟩ : syracuseStep 8480123 = 12720185) B12720185
theorem B5653415 : Blo 2233435 5653415 := bstep (se 1 (by rfl) ⟨4240061, by rfl⟩ : syracuseStep 5653415 = 8480123) B8480123
theorem B3768943 : Blo 2233435 3768943 := bstep (se 1 (by rfl) ⟨2826707, by rfl⟩ : syracuseStep 3768943 = 5653415) B5653415
theorem B5025257 : Blo 2233435 5025257 := bstep (se 2 (by rfl) ⟨1884471, by rfl⟩ : syracuseStep 5025257 = 3768943) B3768943
theorem B3350171 : Blo 2233435 3350171 := bstep (se 1 (by rfl) ⟨2512628, by rfl⟩ : syracuseStep 3350171 = 5025257) B5025257
theorem B2233447 : Blo 2233435 2233447 := bstep (se 1 (by rfl) ⟨1675085, by rfl⟩ : syracuseStep 2233447 = 3350171) B3350171
theorem B2512633 : Blo 2233435 2512633 := bbase (se 2 (by rfl) ⟨942237, by rfl⟩ : syracuseStep 2512633 = 1884475) (by norm_num)
theorem B3350177 : Blo 2233435 3350177 := bstep (se 2 (by rfl) ⟨1256316, by rfl⟩ : syracuseStep 3350177 = 2512633) B2512633
theorem B2233451 : Blo 2233435 2233451 := bstep (se 1 (by rfl) ⟨1675088, by rfl⟩ : syracuseStep 2233451 = 3350177) B3350177
theorem B3577565 : Blo 2233435 3577565 := bbase (se 3 (by rfl) ⟨670793, by rfl⟩ : syracuseStep 3577565 = 1341587) (by norm_num)
theorem B9540173 : Blo 2233435 9540173 := bstep (se 3 (by rfl) ⟨1788782, by rfl⟩ : syracuseStep 9540173 = 3577565) B3577565
theorem B6360115 : Blo 2233435 6360115 := bstep (se 1 (by rfl) ⟨4770086, by rfl⟩ : syracuseStep 6360115 = 9540173) B9540173
theorem B8480153 : Blo 2233435 8480153 := bstep (se 2 (by rfl) ⟨3180057, by rfl⟩ : syracuseStep 8480153 = 6360115) B6360115
theorem B5653435 : Blo 2233435 5653435 := bstep (se 1 (by rfl) ⟨4240076, by rfl⟩ : syracuseStep 5653435 = 8480153) B8480153
theorem B7537913 : Blo 2233435 7537913 := bstep (se 2 (by rfl) ⟨2826717, by rfl⟩ : syracuseStep 7537913 = 5653435) B5653435
theorem B5025275 : Blo 2233435 5025275 := bstep (se 1 (by rfl) ⟨3768956, by rfl⟩ : syracuseStep 5025275 = 7537913) B7537913
theorem B3350183 : Blo 2233435 3350183 := bstep (se 1 (by rfl) ⟨2512637, by rfl⟩ : syracuseStep 3350183 = 5025275) B5025275
theorem B2233455 : Blo 2233435 2233455 := bstep (se 1 (by rfl) ⟨1675091, by rfl⟩ : syracuseStep 2233455 = 3350183) B3350183
theorem B3350189 : Blo 2233435 3350189 := bbase (se 3 (by rfl) ⟨628160, by rfl⟩ : syracuseStep 3350189 = 1256321) (by norm_num)
theorem B2233459 : Blo 2233435 2233459 := bstep (se 1 (by rfl) ⟨1675094, by rfl⟩ : syracuseStep 2233459 = 3350189) B3350189
theorem B5025293 : Blo 2233435 5025293 := bbase (se 3 (by rfl) ⟨942242, by rfl⟩ : syracuseStep 5025293 = 1884485) (by norm_num)
theorem B3350195 : Blo 2233435 3350195 := bstep (se 1 (by rfl) ⟨2512646, by rfl⟩ : syracuseStep 3350195 = 5025293) B5025293
theorem B2233463 : Blo 2233435 2233463 := bstep (se 1 (by rfl) ⟨1675097, by rfl⟩ : syracuseStep 2233463 = 3350195) B3350195
theorem B2826733 : Blo 2233435 2826733 := bbase (se 3 (by rfl) ⟨530012, by rfl⟩ : syracuseStep 2826733 = 1060025) (by norm_num)
theorem B3768977 : Blo 2233435 3768977 := bstep (se 2 (by rfl) ⟨1413366, by rfl⟩ : syracuseStep 3768977 = 2826733) B2826733
theorem B2512651 : Blo 2233435 2512651 := bstep (se 1 (by rfl) ⟨1884488, by rfl⟩ : syracuseStep 2512651 = 3768977) B3768977
theorem B3350201 : Blo 2233435 3350201 := bstep (se 2 (by rfl) ⟨1256325, by rfl⟩ : syracuseStep 3350201 = 2512651) B2512651
theorem B2233467 : Blo 2233435 2233467 := bstep (se 1 (by rfl) ⟨1675100, by rfl⟩ : syracuseStep 2233467 = 3350201) B3350201
theorem B16099157 : Blo 2233435 16099157 := bbase (se 9 (by rfl) ⟨47165, by rfl⟩ : syracuseStep 16099157 = 94331) (by norm_num)
theorem B10732771 : Blo 2233435 10732771 := bstep (se 1 (by rfl) ⟨8049578, by rfl⟩ : syracuseStep 10732771 = 16099157) B16099157
theorem B14310361 : Blo 2233435 14310361 := bstep (se 2 (by rfl) ⟨5366385, by rfl⟩ : syracuseStep 14310361 = 10732771) B10732771
theorem B19080481 : Blo 2233435 19080481 := bstep (se 2 (by rfl) ⟨7155180, by rfl⟩ : syracuseStep 19080481 = 14310361) B14310361
theorem B25440641 : Blo 2233435 25440641 := bstep (se 2 (by rfl) ⟨9540240, by rfl⟩ : syracuseStep 25440641 = 19080481) B19080481
theorem B16960427 : Blo 2233435 16960427 := bstep (se 1 (by rfl) ⟨12720320, by rfl⟩ : syracuseStep 16960427 = 25440641) B25440641
theorem B11306951 : Blo 2233435 11306951 := bstep (se 1 (by rfl) ⟨8480213, by rfl⟩ : syracuseStep 11306951 = 16960427) B16960427
theorem B7537967 : Blo 2233435 7537967 := bstep (se 1 (by rfl) ⟨5653475, by rfl⟩ : syracuseStep 7537967 = 11306951) B11306951
theorem B5025311 : Blo 2233435 5025311 := bstep (se 1 (by rfl) ⟨3768983, by rfl⟩ : syracuseStep 5025311 = 7537967) B7537967
theorem B3350207 : Blo 2233435 3350207 := bstep (se 1 (by rfl) ⟨2512655, by rfl⟩ : syracuseStep 3350207 = 5025311) B5025311
theorem B2233471 : Blo 2233435 2233471 := bstep (se 1 (by rfl) ⟨1675103, by rfl⟩ : syracuseStep 2233471 = 3350207) B3350207
theorem B3350213 : Blo 2233435 3350213 := bbase (se 4 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 3350213 = 628165) (by norm_num)
theorem B2233475 : Blo 2233435 2233475 := bstep (se 1 (by rfl) ⟨1675106, by rfl⟩ : syracuseStep 2233475 = 3350213) B3350213
theorem B3768997 : Blo 2233435 3768997 := bbase (se 4 (by rfl) ⟨353343, by rfl⟩ : syracuseStep 3768997 = 706687) (by norm_num)
theorem B5025329 : Blo 2233435 5025329 := bstep (se 2 (by rfl) ⟨1884498, by rfl⟩ : syracuseStep 5025329 = 3768997) B3768997
theorem B3350219 : Blo 2233435 3350219 := bstep (se 1 (by rfl) ⟨2512664, by rfl⟩ : syracuseStep 3350219 = 5025329) B5025329
theorem B2233479 : Blo 2233435 2233479 := bstep (se 1 (by rfl) ⟨1675109, by rfl⟩ : syracuseStep 2233479 = 3350219) B3350219
theorem B2512669 : Blo 2233435 2512669 := bbase (se 3 (by rfl) ⟨471125, by rfl⟩ : syracuseStep 2512669 = 942251) (by norm_num)
theorem B3350225 : Blo 2233435 3350225 := bstep (se 2 (by rfl) ⟨1256334, by rfl⟩ : syracuseStep 3350225 = 2512669) B2512669
theorem B2233483 : Blo 2233435 2233483 := bstep (se 1 (by rfl) ⟨1675112, by rfl⟩ : syracuseStep 2233483 = 3350225) B3350225
theorem B7538021 : Blo 2233435 7538021 := bbase (se 4 (by rfl) ⟨706689, by rfl⟩ : syracuseStep 7538021 = 1413379) (by norm_num)
theorem B5025347 : Blo 2233435 5025347 := bstep (se 1 (by rfl) ⟨3769010, by rfl⟩ : syracuseStep 5025347 = 7538021) B7538021
theorem B3350231 : Blo 2233435 3350231 := bstep (se 1 (by rfl) ⟨2512673, by rfl⟩ : syracuseStep 3350231 = 5025347) B5025347
theorem B2233487 : Blo 2233435 2233487 := bstep (se 1 (by rfl) ⟨1675115, by rfl⟩ : syracuseStep 2233487 = 3350231) B3350231
theorem B3350237 : Blo 2233435 3350237 := bbase (se 3 (by rfl) ⟨628169, by rfl⟩ : syracuseStep 3350237 = 1256339) (by norm_num)
theorem B2233491 : Blo 2233435 2233491 := bstep (se 1 (by rfl) ⟨1675118, by rfl⟩ : syracuseStep 2233491 = 3350237) B3350237
theorem B5025365 : Blo 2233435 5025365 := bbase (se 8 (by rfl) ⟨29445, by rfl⟩ : syracuseStep 5025365 = 58891) (by norm_num)
theorem B3350243 : Blo 2233435 3350243 := bstep (se 1 (by rfl) ⟨2512682, by rfl⟩ : syracuseStep 3350243 = 5025365) B5025365
theorem B2233495 : Blo 2233435 2233495 := bstep (se 1 (by rfl) ⟨1675121, by rfl⟩ : syracuseStep 2233495 = 3350243) B3350243
theorem B4770181 : Blo 2233435 4770181 := bbase (se 4 (by rfl) ⟨447204, by rfl⟩ : syracuseStep 4770181 = 894409) (by norm_num)
theorem B6360241 : Blo 2233435 6360241 := bstep (se 2 (by rfl) ⟨2385090, by rfl⟩ : syracuseStep 6360241 = 4770181) B4770181
theorem B8480321 : Blo 2233435 8480321 := bstep (se 2 (by rfl) ⟨3180120, by rfl⟩ : syracuseStep 8480321 = 6360241) B6360241
theorem B5653547 : Blo 2233435 5653547 := bstep (se 1 (by rfl) ⟨4240160, by rfl⟩ : syracuseStep 5653547 = 8480321) B8480321
theorem B3769031 : Blo 2233435 3769031 := bstep (se 1 (by rfl) ⟨2826773, by rfl⟩ : syracuseStep 3769031 = 5653547) B5653547
theorem B2512687 : Blo 2233435 2512687 := bstep (se 1 (by rfl) ⟨1884515, by rfl⟩ : syracuseStep 2512687 = 3769031) B3769031
theorem B3350249 : Blo 2233435 3350249 := bstep (se 2 (by rfl) ⟨1256343, by rfl⟩ : syracuseStep 3350249 = 2512687) B2512687
theorem B2233499 : Blo 2233435 2233499 := bstep (se 1 (by rfl) ⟨1675124, by rfl⟩ : syracuseStep 2233499 = 3350249) B3350249
theorem B13583861 : Blo 2233435 13583861 := bbase (se 5 (by rfl) ⟨636743, by rfl⟩ : syracuseStep 13583861 = 1273487) (by norm_num)
theorem B9055907 : Blo 2233435 9055907 := bstep (se 1 (by rfl) ⟨6791930, by rfl⟩ : syracuseStep 9055907 = 13583861) B13583861
theorem B6037271 : Blo 2233435 6037271 := bstep (se 1 (by rfl) ⟨4527953, by rfl⟩ : syracuseStep 6037271 = 9055907) B9055907
theorem B4024847 : Blo 2233435 4024847 := bstep (se 1 (by rfl) ⟨3018635, by rfl⟩ : syracuseStep 4024847 = 6037271) B6037271
theorem B10732925 : Blo 2233435 10732925 := bstep (se 3 (by rfl) ⟨2012423, by rfl⟩ : syracuseStep 10732925 = 4024847) B4024847
theorem B28621133 : Blo 2233435 28621133 := bstep (se 3 (by rfl) ⟨5366462, by rfl⟩ : syracuseStep 28621133 = 10732925) B10732925
theorem B19080755 : Blo 2233435 19080755 := bstep (se 1 (by rfl) ⟨14310566, by rfl⟩ : syracuseStep 19080755 = 28621133) B28621133
theorem B12720503 : Blo 2233435 12720503 := bstep (se 1 (by rfl) ⟨9540377, by rfl⟩ : syracuseStep 12720503 = 19080755) B19080755
theorem B8480335 : Blo 2233435 8480335 := bstep (se 1 (by rfl) ⟨6360251, by rfl⟩ : syracuseStep 8480335 = 12720503) B12720503
theorem B11307113 : Blo 2233435 11307113 := bstep (se 2 (by rfl) ⟨4240167, by rfl⟩ : syracuseStep 11307113 = 8480335) B8480335
theorem B7538075 : Blo 2233435 7538075 := bstep (se 1 (by rfl) ⟨5653556, by rfl⟩ : syracuseStep 7538075 = 11307113) B11307113
theorem B5025383 : Blo 2233435 5025383 := bstep (se 1 (by rfl) ⟨3769037, by rfl⟩ : syracuseStep 5025383 = 7538075) B7538075
theorem B3350255 : Blo 2233435 3350255 := bstep (se 1 (by rfl) ⟨2512691, by rfl⟩ : syracuseStep 3350255 = 5025383) B5025383
theorem B2233503 : Blo 2233435 2233503 := bstep (se 1 (by rfl) ⟨1675127, by rfl⟩ : syracuseStep 2233503 = 3350255) B3350255
theorem B3350261 : Blo 2233435 3350261 := bbase (se 5 (by rfl) ⟨157043, by rfl⟩ : syracuseStep 3350261 = 314087) (by norm_num)
theorem B2233507 : Blo 2233435 2233507 := bstep (se 1 (by rfl) ⟨1675130, by rfl⟩ : syracuseStep 2233507 = 3350261) B3350261
theorem B6791957 : Blo 2233435 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B4527971 : Blo 2233435 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B3018647 : Blo 2233435 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B8049725 : Blo 2233435 8049725 := bstep (se 3 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 8049725 = 3018647) B3018647
theorem B5366483 : Blo 2233435 5366483 := bstep (se 1 (by rfl) ⟨4024862, by rfl⟩ : syracuseStep 5366483 = 8049725) B8049725
theorem B3577655 : Blo 2233435 3577655 := bstep (se 1 (by rfl) ⟨2683241, by rfl⟩ : syracuseStep 3577655 = 5366483) B5366483
theorem B9540413 : Blo 2233435 9540413 := bstep (se 3 (by rfl) ⟨1788827, by rfl⟩ : syracuseStep 9540413 = 3577655) B3577655
theorem B6360275 : Blo 2233435 6360275 := bstep (se 1 (by rfl) ⟨4770206, by rfl⟩ : syracuseStep 6360275 = 9540413) B9540413
theorem B4240183 : Blo 2233435 4240183 := bstep (se 1 (by rfl) ⟨3180137, by rfl⟩ : syracuseStep 4240183 = 6360275) B6360275
theorem B5653577 : Blo 2233435 5653577 := bstep (se 2 (by rfl) ⟨2120091, by rfl⟩ : syracuseStep 5653577 = 4240183) B4240183
theorem B3769051 : Blo 2233435 3769051 := bstep (se 1 (by rfl) ⟨2826788, by rfl⟩ : syracuseStep 3769051 = 5653577) B5653577
theorem B5025401 : Blo 2233435 5025401 := bstep (se 2 (by rfl) ⟨1884525, by rfl⟩ : syracuseStep 5025401 = 3769051) B3769051
theorem B3350267 : Blo 2233435 3350267 := bstep (se 1 (by rfl) ⟨2512700, by rfl⟩ : syracuseStep 3350267 = 5025401) B5025401
theorem B2233511 : Blo 2233435 2233511 := bstep (se 1 (by rfl) ⟨1675133, by rfl⟩ : syracuseStep 2233511 = 3350267) B3350267
theorem B2512705 : Blo 2233435 2512705 := bbase (se 2 (by rfl) ⟨942264, by rfl⟩ : syracuseStep 2512705 = 1884529) (by norm_num)
theorem B3350273 : Blo 2233435 3350273 := bstep (se 2 (by rfl) ⟨1256352, by rfl⟩ : syracuseStep 3350273 = 2512705) B2512705
theorem B2233515 : Blo 2233435 2233515 := bstep (se 1 (by rfl) ⟨1675136, by rfl⟩ : syracuseStep 2233515 = 3350273) B3350273
theorem B5653597 : Blo 2233435 5653597 := bbase (se 3 (by rfl) ⟨1060049, by rfl⟩ : syracuseStep 5653597 = 2120099) (by norm_num)
theorem B7538129 : Blo 2233435 7538129 := bstep (se 2 (by rfl) ⟨2826798, by rfl⟩ : syracuseStep 7538129 = 5653597) B5653597
theorem B5025419 : Blo 2233435 5025419 := bstep (se 1 (by rfl) ⟨3769064, by rfl⟩ : syracuseStep 5025419 = 7538129) B7538129
theorem B3350279 : Blo 2233435 3350279 := bstep (se 1 (by rfl) ⟨2512709, by rfl⟩ : syracuseStep 3350279 = 5025419) B5025419
theorem B2233519 : Blo 2233435 2233519 := bstep (se 1 (by rfl) ⟨1675139, by rfl⟩ : syracuseStep 2233519 = 3350279) B3350279
theorem B3350285 : Blo 2233435 3350285 := bbase (se 3 (by rfl) ⟨628178, by rfl⟩ : syracuseStep 3350285 = 1256357) (by norm_num)
theorem B2233523 : Blo 2233435 2233523 := bstep (se 1 (by rfl) ⟨1675142, by rfl⟩ : syracuseStep 2233523 = 3350285) B3350285
theorem B5025437 : Blo 2233435 5025437 := bbase (se 3 (by rfl) ⟨942269, by rfl⟩ : syracuseStep 5025437 = 1884539) (by norm_num)
theorem B3350291 : Blo 2233435 3350291 := bstep (se 1 (by rfl) ⟨2512718, by rfl⟩ : syracuseStep 3350291 = 5025437) B5025437
theorem B2233527 : Blo 2233435 2233527 := bstep (se 1 (by rfl) ⟨1675145, by rfl⟩ : syracuseStep 2233527 = 3350291) B3350291
theorem B3769085 : Blo 2233435 3769085 := bbase (se 3 (by rfl) ⟨706703, by rfl⟩ : syracuseStep 3769085 = 1413407) (by norm_num)
theorem B2512723 : Blo 2233435 2512723 := bstep (se 1 (by rfl) ⟨1884542, by rfl⟩ : syracuseStep 2512723 = 3769085) B3769085
theorem B3350297 : Blo 2233435 3350297 := bstep (se 2 (by rfl) ⟨1256361, by rfl⟩ : syracuseStep 3350297 = 2512723) B2512723
theorem B2233531 : Blo 2233435 2233531 := bstep (se 1 (by rfl) ⟨1675148, by rfl⟩ : syracuseStep 2233531 = 3350297) B3350297
theorem B3577693 : Blo 2233435 3577693 := bbase (se 3 (by rfl) ⟨670817, by rfl⟩ : syracuseStep 3577693 = 1341635) (by norm_num)
theorem B4770257 : Blo 2233435 4770257 := bstep (se 2 (by rfl) ⟨1788846, by rfl⟩ : syracuseStep 4770257 = 3577693) B3577693
theorem B12720685 : Blo 2233435 12720685 := bstep (se 3 (by rfl) ⟨2385128, by rfl⟩ : syracuseStep 12720685 = 4770257) B4770257
theorem B16960913 : Blo 2233435 16960913 := bstep (se 2 (by rfl) ⟨6360342, by rfl⟩ : syracuseStep 16960913 = 12720685) B12720685
theorem B11307275 : Blo 2233435 11307275 := bstep (se 1 (by rfl) ⟨8480456, by rfl⟩ : syracuseStep 11307275 = 16960913) B16960913
theorem B7538183 : Blo 2233435 7538183 := bstep (se 1 (by rfl) ⟨5653637, by rfl⟩ : syracuseStep 7538183 = 11307275) B11307275
theorem B5025455 : Blo 2233435 5025455 := bstep (se 1 (by rfl) ⟨3769091, by rfl⟩ : syracuseStep 5025455 = 7538183) B7538183
theorem B3350303 : Blo 2233435 3350303 := bstep (se 1 (by rfl) ⟨2512727, by rfl⟩ : syracuseStep 3350303 = 5025455) B5025455
theorem B2233535 : Blo 2233435 2233535 := bstep (se 1 (by rfl) ⟨1675151, by rfl⟩ : syracuseStep 2233535 = 3350303) B3350303
theorem B3350309 : Blo 2233435 3350309 := bbase (se 4 (by rfl) ⟨314091, by rfl⟩ : syracuseStep 3350309 = 628183) (by norm_num)
theorem B2233539 : Blo 2233435 2233539 := bstep (se 1 (by rfl) ⟨1675154, by rfl⟩ : syracuseStep 2233539 = 3350309) B3350309
theorem B2826829 : Blo 2233435 2826829 := bbase (se 3 (by rfl) ⟨530030, by rfl⟩ : syracuseStep 2826829 = 1060061) (by norm_num)
theorem B3769105 : Blo 2233435 3769105 := bstep (se 2 (by rfl) ⟨1413414, by rfl⟩ : syracuseStep 3769105 = 2826829) B2826829
theorem B5025473 : Blo 2233435 5025473 := bstep (se 2 (by rfl) ⟨1884552, by rfl⟩ : syracuseStep 5025473 = 3769105) B3769105
theorem B3350315 : Blo 2233435 3350315 := bstep (se 1 (by rfl) ⟨2512736, by rfl⟩ : syracuseStep 3350315 = 5025473) B5025473
theorem B2233543 : Blo 2233435 2233543 := bstep (se 1 (by rfl) ⟨1675157, by rfl⟩ : syracuseStep 2233543 = 3350315) B3350315
theorem B2512741 : Blo 2233435 2512741 := bbase (se 4 (by rfl) ⟨235569, by rfl⟩ : syracuseStep 2512741 = 471139) (by norm_num)
theorem B3350321 : Blo 2233435 3350321 := bstep (se 2 (by rfl) ⟨1256370, by rfl⟩ : syracuseStep 3350321 = 2512741) B2512741
theorem B2233547 : Blo 2233435 2233547 := bstep (se 1 (by rfl) ⟨1675160, by rfl⟩ : syracuseStep 2233547 = 3350321) B3350321
theorem B6360389 : Blo 2233435 6360389 := bbase (se 4 (by rfl) ⟨596286, by rfl⟩ : syracuseStep 6360389 = 1192573) (by norm_num)
theorem B4240259 : Blo 2233435 4240259 := bstep (se 1 (by rfl) ⟨3180194, by rfl⟩ : syracuseStep 4240259 = 6360389) B6360389
theorem B2826839 : Blo 2233435 2826839 := bstep (se 1 (by rfl) ⟨2120129, by rfl⟩ : syracuseStep 2826839 = 4240259) B4240259
theorem B7538237 : Blo 2233435 7538237 := bstep (se 3 (by rfl) ⟨1413419, by rfl⟩ : syracuseStep 7538237 = 2826839) B2826839
theorem B5025491 : Blo 2233435 5025491 := bstep (se 1 (by rfl) ⟨3769118, by rfl⟩ : syracuseStep 5025491 = 7538237) B7538237
theorem B3350327 : Blo 2233435 3350327 := bstep (se 1 (by rfl) ⟨2512745, by rfl⟩ : syracuseStep 3350327 = 5025491) B5025491
theorem B2233551 : Blo 2233435 2233551 := bstep (se 1 (by rfl) ⟨1675163, by rfl⟩ : syracuseStep 2233551 = 3350327) B3350327
theorem B3350333 : Blo 2233435 3350333 := bbase (se 3 (by rfl) ⟨628187, by rfl⟩ : syracuseStep 3350333 = 1256375) (by norm_num)
theorem B2233555 : Blo 2233435 2233555 := bstep (se 1 (by rfl) ⟨1675166, by rfl⟩ : syracuseStep 2233555 = 3350333) B3350333
theorem B5025509 : Blo 2233435 5025509 := bbase (se 4 (by rfl) ⟨471141, by rfl⟩ : syracuseStep 5025509 = 942283) (by norm_num)
theorem B3350339 : Blo 2233435 3350339 := bstep (se 1 (by rfl) ⟨2512754, by rfl⟩ : syracuseStep 3350339 = 5025509) B5025509
theorem B2233559 : Blo 2233435 2233559 := bstep (se 1 (by rfl) ⟨1675169, by rfl⟩ : syracuseStep 2233559 = 3350339) B3350339
theorem B5653709 : Blo 2233435 5653709 := bbase (se 3 (by rfl) ⟨1060070, by rfl⟩ : syracuseStep 5653709 = 2120141) (by norm_num)
theorem B3769139 : Blo 2233435 3769139 := bstep (se 1 (by rfl) ⟨2826854, by rfl⟩ : syracuseStep 3769139 = 5653709) B5653709
theorem B2512759 : Blo 2233435 2512759 := bstep (se 1 (by rfl) ⟨1884569, by rfl⟩ : syracuseStep 2512759 = 3769139) B3769139
theorem B3350345 : Blo 2233435 3350345 := bstep (se 2 (by rfl) ⟨1256379, by rfl⟩ : syracuseStep 3350345 = 2512759) B2512759
theorem B2233563 : Blo 2233435 2233563 := bstep (se 1 (by rfl) ⟨1675172, by rfl⟩ : syracuseStep 2233563 = 3350345) B3350345
theorem B2683309 : Blo 2233435 2683309 := bbase (se 3 (by rfl) ⟨503120, by rfl⟩ : syracuseStep 2683309 = 1006241) (by norm_num)
theorem B3577745 : Blo 2233435 3577745 := bstep (se 2 (by rfl) ⟨1341654, by rfl⟩ : syracuseStep 3577745 = 2683309) B2683309
theorem B2385163 : Blo 2233435 2385163 := bstep (se 1 (by rfl) ⟨1788872, by rfl⟩ : syracuseStep 2385163 = 3577745) B3577745
theorem B3180217 : Blo 2233435 3180217 := bstep (se 2 (by rfl) ⟨1192581, by rfl⟩ : syracuseStep 3180217 = 2385163) B2385163
theorem B4240289 : Blo 2233435 4240289 := bstep (se 2 (by rfl) ⟨1590108, by rfl⟩ : syracuseStep 4240289 = 3180217) B3180217
theorem B11307437 : Blo 2233435 11307437 := bstep (se 3 (by rfl) ⟨2120144, by rfl⟩ : syracuseStep 11307437 = 4240289) B4240289
theorem B7538291 : Blo 2233435 7538291 := bstep (se 1 (by rfl) ⟨5653718, by rfl⟩ : syracuseStep 7538291 = 11307437) B11307437
theorem B5025527 : Blo 2233435 5025527 := bstep (se 1 (by rfl) ⟨3769145, by rfl⟩ : syracuseStep 5025527 = 7538291) B7538291
theorem B3350351 : Blo 2233435 3350351 := bstep (se 1 (by rfl) ⟨2512763, by rfl⟩ : syracuseStep 3350351 = 5025527) B5025527
theorem B2233567 : Blo 2233435 2233567 := bstep (se 1 (by rfl) ⟨1675175, by rfl⟩ : syracuseStep 2233567 = 3350351) B3350351
theorem B3350357 : Blo 2233435 3350357 := bbase (se 9 (by rfl) ⟨9815, by rfl⟩ : syracuseStep 3350357 = 19631) (by norm_num)
theorem B2233571 : Blo 2233435 2233571 := bstep (se 1 (by rfl) ⟨1675178, by rfl⟩ : syracuseStep 2233571 = 3350357) B3350357
theorem B12074933 : Blo 2233435 12074933 := bbase (se 5 (by rfl) ⟨566012, by rfl⟩ : syracuseStep 12074933 = 1132025) (by norm_num)
theorem B8049955 : Blo 2233435 8049955 := bstep (se 1 (by rfl) ⟨6037466, by rfl⟩ : syracuseStep 8049955 = 12074933) B12074933
theorem B10733273 : Blo 2233435 10733273 := bstep (se 2 (by rfl) ⟨4024977, by rfl⟩ : syracuseStep 10733273 = 8049955) B8049955
theorem B7155515 : Blo 2233435 7155515 := bstep (se 1 (by rfl) ⟨5366636, by rfl⟩ : syracuseStep 7155515 = 10733273) B10733273
theorem B4770343 : Blo 2233435 4770343 := bstep (se 1 (by rfl) ⟨3577757, by rfl⟩ : syracuseStep 4770343 = 7155515) B7155515
theorem B6360457 : Blo 2233435 6360457 := bstep (se 2 (by rfl) ⟨2385171, by rfl⟩ : syracuseStep 6360457 = 4770343) B4770343
theorem B8480609 : Blo 2233435 8480609 := bstep (se 2 (by rfl) ⟨3180228, by rfl⟩ : syracuseStep 8480609 = 6360457) B6360457
theorem B5653739 : Blo 2233435 5653739 := bstep (se 1 (by rfl) ⟨4240304, by rfl⟩ : syracuseStep 5653739 = 8480609) B8480609
theorem B3769159 : Blo 2233435 3769159 := bstep (se 1 (by rfl) ⟨2826869, by rfl⟩ : syracuseStep 3769159 = 5653739) B5653739
theorem B5025545 : Blo 2233435 5025545 := bstep (se 2 (by rfl) ⟨1884579, by rfl⟩ : syracuseStep 5025545 = 3769159) B3769159
theorem B3350363 : Blo 2233435 3350363 := bstep (se 1 (by rfl) ⟨2512772, by rfl⟩ : syracuseStep 3350363 = 5025545) B5025545
theorem B2233575 : Blo 2233435 2233575 := bstep (se 1 (by rfl) ⟨1675181, by rfl⟩ : syracuseStep 2233575 = 3350363) B3350363
theorem B2512777 : Blo 2233435 2512777 := bbase (se 2 (by rfl) ⟨942291, by rfl⟩ : syracuseStep 2512777 = 1884583) (by norm_num)
theorem B3350369 : Blo 2233435 3350369 := bstep (se 2 (by rfl) ⟨1256388, by rfl⟩ : syracuseStep 3350369 = 2512777) B2512777
theorem B2233579 : Blo 2233435 2233579 := bstep (se 1 (by rfl) ⟨1675184, by rfl⟩ : syracuseStep 2233579 = 3350369) B3350369
theorem B15282389 : Blo 2233435 15282389 := bbase (se 7 (by rfl) ⟨179090, by rfl⟩ : syracuseStep 15282389 = 358181) (by norm_num)
theorem B40753037 : Blo 2233435 40753037 := bstep (se 3 (by rfl) ⟨7641194, by rfl⟩ : syracuseStep 40753037 = 15282389) B15282389
theorem B27168691 : Blo 2233435 27168691 := bstep (se 1 (by rfl) ⟨20376518, by rfl⟩ : syracuseStep 27168691 = 40753037) B40753037
theorem B36224921 : Blo 2233435 36224921 := bstep (se 2 (by rfl) ⟨13584345, by rfl⟩ : syracuseStep 36224921 = 27168691) B27168691
theorem B96599789 : Blo 2233435 96599789 := bstep (se 3 (by rfl) ⟨18112460, by rfl⟩ : syracuseStep 96599789 = 36224921) B36224921
theorem B64399859 : Blo 2233435 64399859 := bstep (se 1 (by rfl) ⟨48299894, by rfl⟩ : syracuseStep 64399859 = 96599789) B96599789
theorem B42933239 : Blo 2233435 42933239 := bstep (se 1 (by rfl) ⟨32199929, by rfl⟩ : syracuseStep 42933239 = 64399859) B64399859
theorem B28622159 : Blo 2233435 28622159 := bstep (se 1 (by rfl) ⟨21466619, by rfl⟩ : syracuseStep 28622159 = 42933239) B42933239
theorem B19081439 : Blo 2233435 19081439 := bstep (se 1 (by rfl) ⟨14311079, by rfl⟩ : syracuseStep 19081439 = 28622159) B28622159
theorem B12720959 : Blo 2233435 12720959 := bstep (se 1 (by rfl) ⟨9540719, by rfl⟩ : syracuseStep 12720959 = 19081439) B19081439
theorem B8480639 : Blo 2233435 8480639 := bstep (se 1 (by rfl) ⟨6360479, by rfl⟩ : syracuseStep 8480639 = 12720959) B12720959
theorem B5653759 : Blo 2233435 5653759 := bstep (se 1 (by rfl) ⟨4240319, by rfl⟩ : syracuseStep 5653759 = 8480639) B8480639
theorem B7538345 : Blo 2233435 7538345 := bstep (se 2 (by rfl) ⟨2826879, by rfl⟩ : syracuseStep 7538345 = 5653759) B5653759
theorem B5025563 : Blo 2233435 5025563 := bstep (se 1 (by rfl) ⟨3769172, by rfl⟩ : syracuseStep 5025563 = 7538345) B7538345
theorem B3350375 : Blo 2233435 3350375 := bstep (se 1 (by rfl) ⟨2512781, by rfl⟩ : syracuseStep 3350375 = 5025563) B5025563
theorem B2233583 : Blo 2233435 2233583 := bstep (se 1 (by rfl) ⟨1675187, by rfl⟩ : syracuseStep 2233583 = 3350375) B3350375
theorem B3350381 : Blo 2233435 3350381 := bbase (se 3 (by rfl) ⟨628196, by rfl⟩ : syracuseStep 3350381 = 1256393) (by norm_num)
theorem B2233587 : Blo 2233435 2233587 := bstep (se 1 (by rfl) ⟨1675190, by rfl⟩ : syracuseStep 2233587 = 3350381) B3350381
theorem B5025581 : Blo 2233435 5025581 := bbase (se 3 (by rfl) ⟨942296, by rfl⟩ : syracuseStep 5025581 = 1884593) (by norm_num)
theorem B3350387 : Blo 2233435 3350387 := bstep (se 1 (by rfl) ⟨2512790, by rfl⟩ : syracuseStep 3350387 = 5025581) B5025581
theorem B2233591 : Blo 2233435 2233591 := bstep (se 1 (by rfl) ⟨1675193, by rfl⟩ : syracuseStep 2233591 = 3350387) B3350387
theorem B9540773 : Blo 2233435 9540773 := bbase (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) (by norm_num)
theorem B6360515 : Blo 2233435 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B4240343 : Blo 2233435 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B2826895 : Blo 2233435 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B3769193 : Blo 2233435 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B2512795 : Blo 2233435 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B3350393 : Blo 2233435 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B2233595 : Blo 2233435 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B5366693 : Blo 2233435 5366693 := bbase (se 4 (by rfl) ⟨503127, by rfl⟩ : syracuseStep 5366693 = 1006255) (by norm_num)
theorem B14311181 : Blo 2233435 14311181 := bstep (se 3 (by rfl) ⟨2683346, by rfl⟩ : syracuseStep 14311181 = 5366693) B5366693
theorem B38163149 : Blo 2233435 38163149 := bstep (se 3 (by rfl) ⟨7155590, by rfl⟩ : syracuseStep 38163149 = 14311181) B14311181
theorem B25442099 : Blo 2233435 25442099 := bstep (se 1 (by rfl) ⟨19081574, by rfl⟩ : syracuseStep 25442099 = 38163149) B38163149
theorem B16961399 : Blo 2233435 16961399 := bstep (se 1 (by rfl) ⟨12721049, by rfl⟩ : syracuseStep 16961399 = 25442099) B25442099
theorem B11307599 : Blo 2233435 11307599 := bstep (se 1 (by rfl) ⟨8480699, by rfl⟩ : syracuseStep 11307599 = 16961399) B16961399
theorem B7538399 : Blo 2233435 7538399 := bstep (se 1 (by rfl) ⟨5653799, by rfl⟩ : syracuseStep 7538399 = 11307599) B11307599
theorem B5025599 : Blo 2233435 5025599 := bstep (se 1 (by rfl) ⟨3769199, by rfl⟩ : syracuseStep 5025599 = 7538399) B7538399
theorem B3350399 : Blo 2233435 3350399 := bstep (se 1 (by rfl) ⟨2512799, by rfl⟩ : syracuseStep 3350399 = 5025599) B5025599
theorem B2233599 : Blo 2233435 2233599 := bstep (se 1 (by rfl) ⟨1675199, by rfl⟩ : syracuseStep 2233599 = 3350399) B3350399
theorem B3350405 : Blo 2233435 3350405 := bbase (se 4 (by rfl) ⟨314100, by rfl⟩ : syracuseStep 3350405 = 628201) (by norm_num)
theorem B2233603 : Blo 2233435 2233603 := bstep (se 1 (by rfl) ⟨1675202, by rfl⟩ : syracuseStep 2233603 = 3350405) B3350405
theorem B3769213 : Blo 2233435 3769213 := bbase (se 3 (by rfl) ⟨706727, by rfl⟩ : syracuseStep 3769213 = 1413455) (by norm_num)
theorem B5025617 : Blo 2233435 5025617 := bstep (se 2 (by rfl) ⟨1884606, by rfl⟩ : syracuseStep 5025617 = 3769213) B3769213
theorem B3350411 : Blo 2233435 3350411 := bstep (se 1 (by rfl) ⟨2512808, by rfl⟩ : syracuseStep 3350411 = 5025617) B5025617
theorem B2233607 : Blo 2233435 2233607 := bstep (se 1 (by rfl) ⟨1675205, by rfl⟩ : syracuseStep 2233607 = 3350411) B3350411
theorem B2512813 : Blo 2233435 2512813 := bbase (se 3 (by rfl) ⟨471152, by rfl⟩ : syracuseStep 2512813 = 942305) (by norm_num)
theorem B3350417 : Blo 2233435 3350417 := bstep (se 2 (by rfl) ⟨1256406, by rfl⟩ : syracuseStep 3350417 = 2512813) B2512813
theorem B2233611 : Blo 2233435 2233611 := bstep (se 1 (by rfl) ⟨1675208, by rfl⟩ : syracuseStep 2233611 = 3350417) B3350417
theorem B7538453 : Blo 2233435 7538453 := bbase (se 6 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 7538453 = 353365) (by norm_num)
theorem B5025635 : Blo 2233435 5025635 := bstep (se 1 (by rfl) ⟨3769226, by rfl⟩ : syracuseStep 5025635 = 7538453) B7538453
theorem B3350423 : Blo 2233435 3350423 := bstep (se 1 (by rfl) ⟨2512817, by rfl⟩ : syracuseStep 3350423 = 5025635) B5025635
theorem B2233615 : Blo 2233435 2233615 := bstep (se 1 (by rfl) ⟨1675211, by rfl⟩ : syracuseStep 2233615 = 3350423) B3350423
theorem B3350429 : Blo 2233435 3350429 := bbase (se 3 (by rfl) ⟨628205, by rfl⟩ : syracuseStep 3350429 = 1256411) (by norm_num)
theorem B2233619 : Blo 2233435 2233619 := bstep (se 1 (by rfl) ⟨1675214, by rfl⟩ : syracuseStep 2233619 = 3350429) B3350429
theorem B5025653 : Blo 2233435 5025653 := bbase (se 5 (by rfl) ⟨235577, by rfl⟩ : syracuseStep 5025653 = 471155) (by norm_num)
theorem B3350435 : Blo 2233435 3350435 := bstep (se 1 (by rfl) ⟨2512826, by rfl⟩ : syracuseStep 3350435 = 5025653) B5025653
theorem B2233623 : Blo 2233435 2233623 := bstep (se 1 (by rfl) ⟨1675217, by rfl⟩ : syracuseStep 2233623 = 3350435) B3350435
theorem B2617093 : Blo 2233435 2617093 := bbase (se 4 (by rfl) ⟨245352, by rfl⟩ : syracuseStep 2617093 = 490705) (by norm_num)
theorem B13957829 : Blo 2233435 13957829 := bstep (se 4 (by rfl) ⟨1308546, by rfl⟩ : syracuseStep 13957829 = 2617093) B2617093
theorem B9305219 : Blo 2233435 9305219 := bstep (se 1 (by rfl) ⟨6978914, by rfl⟩ : syracuseStep 9305219 = 13957829) B13957829
theorem B24813917 : Blo 2233435 24813917 := bstep (se 3 (by rfl) ⟨4652609, by rfl⟩ : syracuseStep 24813917 = 9305219) B9305219
theorem B16542611 : Blo 2233435 16542611 := bstep (se 1 (by rfl) ⟨12406958, by rfl⟩ : syracuseStep 16542611 = 24813917) B24813917
theorem B11028407 : Blo 2233435 11028407 := bstep (se 1 (by rfl) ⟨8271305, by rfl⟩ : syracuseStep 11028407 = 16542611) B16542611
theorem B29409085 : Blo 2233435 29409085 := bstep (se 3 (by rfl) ⟨5514203, by rfl⟩ : syracuseStep 29409085 = 11028407) B11028407
theorem B39212113 : Blo 2233435 39212113 := bstep (se 2 (by rfl) ⟨14704542, by rfl⟩ : syracuseStep 39212113 = 29409085) B29409085
theorem B52282817 : Blo 2233435 52282817 := bstep (se 2 (by rfl) ⟨19606056, by rfl⟩ : syracuseStep 52282817 = 39212113) B39212113
theorem B34855211 : Blo 2233435 34855211 := bstep (se 1 (by rfl) ⟨26141408, by rfl⟩ : syracuseStep 34855211 = 52282817) B52282817
theorem B23236807 : Blo 2233435 23236807 := bstep (se 1 (by rfl) ⟨17427605, by rfl⟩ : syracuseStep 23236807 = 34855211) B34855211
theorem B30982409 : Blo 2233435 30982409 := bstep (se 2 (by rfl) ⟨11618403, by rfl⟩ : syracuseStep 30982409 = 23236807) B23236807
theorem B20654939 : Blo 2233435 20654939 := bstep (se 1 (by rfl) ⟨15491204, by rfl⟩ : syracuseStep 20654939 = 30982409) B30982409
theorem B55079837 : Blo 2233435 55079837 := bstep (se 3 (by rfl) ⟨10327469, by rfl⟩ : syracuseStep 55079837 = 20654939) B20654939
theorem B36719891 : Blo 2233435 36719891 := bstep (se 1 (by rfl) ⟨27539918, by rfl⟩ : syracuseStep 36719891 = 55079837) B55079837
theorem B24479927 : Blo 2233435 24479927 := bstep (se 1 (by rfl) ⟨18359945, by rfl⟩ : syracuseStep 24479927 = 36719891) B36719891
theorem B16319951 : Blo 2233435 16319951 := bstep (se 1 (by rfl) ⟨12239963, by rfl⟩ : syracuseStep 16319951 = 24479927) B24479927
theorem B10879967 : Blo 2233435 10879967 := bstep (se 1 (by rfl) ⟨8159975, by rfl⟩ : syracuseStep 10879967 = 16319951) B16319951
theorem B7253311 : Blo 2233435 7253311 := bstep (se 1 (by rfl) ⟨5439983, by rfl⟩ : syracuseStep 7253311 = 10879967) B10879967
theorem B9671081 : Blo 2233435 9671081 := bstep (se 2 (by rfl) ⟨3626655, by rfl⟩ : syracuseStep 9671081 = 7253311) B7253311
theorem B25789549 : Blo 2233435 25789549 := bstep (se 3 (by rfl) ⟨4835540, by rfl⟩ : syracuseStep 25789549 = 9671081) B9671081
theorem B34386065 : Blo 2233435 34386065 := bstep (se 2 (by rfl) ⟨12894774, by rfl⟩ : syracuseStep 34386065 = 25789549) B25789549
theorem B22924043 : Blo 2233435 22924043 := bstep (se 1 (by rfl) ⟨17193032, by rfl⟩ : syracuseStep 22924043 = 34386065) B34386065
theorem B15282695 : Blo 2233435 15282695 := bstep (se 1 (by rfl) ⟨11462021, by rfl⟩ : syracuseStep 15282695 = 22924043) B22924043
theorem B10188463 : Blo 2233435 10188463 := bstep (se 1 (by rfl) ⟨7641347, by rfl⟩ : syracuseStep 10188463 = 15282695) B15282695
theorem B13584617 : Blo 2233435 13584617 := bstep (se 2 (by rfl) ⟨5094231, by rfl⟩ : syracuseStep 13584617 = 10188463) B10188463
theorem B9056411 : Blo 2233435 9056411 := bstep (se 1 (by rfl) ⟨6792308, by rfl⟩ : syracuseStep 9056411 = 13584617) B13584617
theorem B6037607 : Blo 2233435 6037607 := bstep (se 1 (by rfl) ⟨4528205, by rfl⟩ : syracuseStep 6037607 = 9056411) B9056411
theorem B4025071 : Blo 2233435 4025071 := bstep (se 1 (by rfl) ⟨3018803, by rfl⟩ : syracuseStep 4025071 = 6037607) B6037607
theorem B21467045 : Blo 2233435 21467045 := bstep (se 4 (by rfl) ⟨2012535, by rfl⟩ : syracuseStep 21467045 = 4025071) B4025071
theorem B14311363 : Blo 2233435 14311363 := bstep (se 1 (by rfl) ⟨10733522, by rfl⟩ : syracuseStep 14311363 = 21467045) B21467045
theorem B19081817 : Blo 2233435 19081817 := bstep (se 2 (by rfl) ⟨7155681, by rfl⟩ : syracuseStep 19081817 = 14311363) B14311363
theorem B12721211 : Blo 2233435 12721211 := bstep (se 1 (by rfl) ⟨9540908, by rfl⟩ : syracuseStep 12721211 = 19081817) B19081817
theorem B8480807 : Blo 2233435 8480807 := bstep (se 1 (by rfl) ⟨6360605, by rfl⟩ : syracuseStep 8480807 = 12721211) B12721211
theorem B5653871 : Blo 2233435 5653871 := bstep (se 1 (by rfl) ⟨4240403, by rfl⟩ : syracuseStep 5653871 = 8480807) B8480807
theorem B3769247 : Blo 2233435 3769247 := bstep (se 1 (by rfl) ⟨2826935, by rfl⟩ : syracuseStep 3769247 = 5653871) B5653871
theorem B2512831 : Blo 2233435 2512831 := bstep (se 1 (by rfl) ⟨1884623, by rfl⟩ : syracuseStep 2512831 = 3769247) B3769247
theorem B3350441 : Blo 2233435 3350441 := bstep (se 2 (by rfl) ⟨1256415, by rfl⟩ : syracuseStep 3350441 = 2512831) B2512831
theorem B2233627 : Blo 2233435 2233627 := bstep (se 1 (by rfl) ⟨1675220, by rfl⟩ : syracuseStep 2233627 = 3350441) B3350441
theorem B8480821 : Blo 2233435 8480821 := bbase (se 5 (by rfl) ⟨397538, by rfl⟩ : syracuseStep 8480821 = 795077) (by norm_num)
theorem B11307761 : Blo 2233435 11307761 := bstep (se 2 (by rfl) ⟨4240410, by rfl⟩ : syracuseStep 11307761 = 8480821) B8480821
theorem B7538507 : Blo 2233435 7538507 := bstep (se 1 (by rfl) ⟨5653880, by rfl⟩ : syracuseStep 7538507 = 11307761) B11307761
theorem B5025671 : Blo 2233435 5025671 := bstep (se 1 (by rfl) ⟨3769253, by rfl⟩ : syracuseStep 5025671 = 7538507) B7538507
theorem B3350447 : Blo 2233435 3350447 := bstep (se 1 (by rfl) ⟨2512835, by rfl⟩ : syracuseStep 3350447 = 5025671) B5025671
theorem B2233631 : Blo 2233435 2233631 := bstep (se 1 (by rfl) ⟨1675223, by rfl⟩ : syracuseStep 2233631 = 3350447) B3350447
theorem B3350453 : Blo 2233435 3350453 := bbase (se 5 (by rfl) ⟨157052, by rfl⟩ : syracuseStep 3350453 = 314105) (by norm_num)
theorem B2233635 : Blo 2233435 2233635 := bstep (se 1 (by rfl) ⟨1675226, by rfl⟩ : syracuseStep 2233635 = 3350453) B3350453
theorem B5653901 : Blo 2233435 5653901 := bbase (se 3 (by rfl) ⟨1060106, by rfl⟩ : syracuseStep 5653901 = 2120213) (by norm_num)
theorem B3769267 : Blo 2233435 3769267 := bstep (se 1 (by rfl) ⟨2826950, by rfl⟩ : syracuseStep 3769267 = 5653901) B5653901
theorem B5025689 : Blo 2233435 5025689 := bstep (se 2 (by rfl) ⟨1884633, by rfl⟩ : syracuseStep 5025689 = 3769267) B3769267
theorem B3350459 : Blo 2233435 3350459 := bstep (se 1 (by rfl) ⟨2512844, by rfl⟩ : syracuseStep 3350459 = 5025689) B5025689
theorem B2233639 : Blo 2233435 2233639 := bstep (se 1 (by rfl) ⟨1675229, by rfl⟩ : syracuseStep 2233639 = 3350459) B3350459
theorem B2512849 : Blo 2233435 2512849 := bbase (se 2 (by rfl) ⟨942318, by rfl⟩ : syracuseStep 2512849 = 1884637) (by norm_num)
theorem B3350465 : Blo 2233435 3350465 := bstep (se 2 (by rfl) ⟨1256424, by rfl⟩ : syracuseStep 3350465 = 2512849) B2512849
theorem B2233643 : Blo 2233435 2233643 := bstep (se 1 (by rfl) ⟨1675232, by rfl⟩ : syracuseStep 2233643 = 3350465) B3350465
theorem B2683405 : Blo 2233435 2683405 := bbase (se 3 (by rfl) ⟨503138, by rfl⟩ : syracuseStep 2683405 = 1006277) (by norm_num)
theorem B3577873 : Blo 2233435 3577873 := bstep (se 2 (by rfl) ⟨1341702, by rfl⟩ : syracuseStep 3577873 = 2683405) B2683405
theorem B4770497 : Blo 2233435 4770497 := bstep (se 2 (by rfl) ⟨1788936, by rfl⟩ : syracuseStep 4770497 = 3577873) B3577873
theorem B3180331 : Blo 2233435 3180331 := bstep (se 1 (by rfl) ⟨2385248, by rfl⟩ : syracuseStep 3180331 = 4770497) B4770497
theorem B4240441 : Blo 2233435 4240441 := bstep (se 2 (by rfl) ⟨1590165, by rfl⟩ : syracuseStep 4240441 = 3180331) B3180331
theorem B5653921 : Blo 2233435 5653921 := bstep (se 2 (by rfl) ⟨2120220, by rfl⟩ : syracuseStep 5653921 = 4240441) B4240441
theorem B7538561 : Blo 2233435 7538561 := bstep (se 2 (by rfl) ⟨2826960, by rfl⟩ : syracuseStep 7538561 = 5653921) B5653921
theorem B5025707 : Blo 2233435 5025707 := bstep (se 1 (by rfl) ⟨3769280, by rfl⟩ : syracuseStep 5025707 = 7538561) B7538561
theorem B3350471 : Blo 2233435 3350471 := bstep (se 1 (by rfl) ⟨2512853, by rfl⟩ : syracuseStep 3350471 = 5025707) B5025707
theorem B2233647 : Blo 2233435 2233647 := bstep (se 1 (by rfl) ⟨1675235, by rfl⟩ : syracuseStep 2233647 = 3350471) B3350471
theorem B3350477 : Blo 2233435 3350477 := bbase (se 3 (by rfl) ⟨628214, by rfl⟩ : syracuseStep 3350477 = 1256429) (by norm_num)
theorem B2233651 : Blo 2233435 2233651 := bstep (se 1 (by rfl) ⟨1675238, by rfl⟩ : syracuseStep 2233651 = 3350477) B3350477
theorem B5025725 : Blo 2233435 5025725 := bbase (se 3 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 5025725 = 1884647) (by norm_num)
theorem B3350483 : Blo 2233435 3350483 := bstep (se 1 (by rfl) ⟨2512862, by rfl⟩ : syracuseStep 3350483 = 5025725) B5025725
theorem B2233655 : Blo 2233435 2233655 := bstep (se 1 (by rfl) ⟨1675241, by rfl⟩ : syracuseStep 2233655 = 3350483) B3350483
theorem B3769301 : Blo 2233435 3769301 := bbase (se 7 (by rfl) ⟨44171, by rfl⟩ : syracuseStep 3769301 = 88343) (by norm_num)
theorem B2512867 : Blo 2233435 2512867 := bstep (se 1 (by rfl) ⟨1884650, by rfl⟩ : syracuseStep 2512867 = 3769301) B3769301
theorem B3350489 : Blo 2233435 3350489 := bstep (se 2 (by rfl) ⟨1256433, by rfl⟩ : syracuseStep 3350489 = 2512867) B2512867
theorem B2233659 : Blo 2233435 2233659 := bstep (se 1 (by rfl) ⟨1675244, by rfl⟩ : syracuseStep 2233659 = 3350489) B3350489
theorem B9541061 : Blo 2233435 9541061 := bbase (se 4 (by rfl) ⟨894474, by rfl⟩ : syracuseStep 9541061 = 1788949) (by norm_num)
theorem B6360707 : Blo 2233435 6360707 := bstep (se 1 (by rfl) ⟨4770530, by rfl⟩ : syracuseStep 6360707 = 9541061) B9541061
theorem B16961885 : Blo 2233435 16961885 := bstep (se 3 (by rfl) ⟨3180353, by rfl⟩ : syracuseStep 16961885 = 6360707) B6360707
theorem B11307923 : Blo 2233435 11307923 := bstep (se 1 (by rfl) ⟨8480942, by rfl⟩ : syracuseStep 11307923 = 16961885) B16961885
theorem B7538615 : Blo 2233435 7538615 := bstep (se 1 (by rfl) ⟨5653961, by rfl⟩ : syracuseStep 7538615 = 11307923) B11307923
theorem B5025743 : Blo 2233435 5025743 := bstep (se 1 (by rfl) ⟨3769307, by rfl⟩ : syracuseStep 5025743 = 7538615) B7538615
theorem B3350495 : Blo 2233435 3350495 := bstep (se 1 (by rfl) ⟨2512871, by rfl⟩ : syracuseStep 3350495 = 5025743) B5025743
theorem B2233663 : Blo 2233435 2233663 := bstep (se 1 (by rfl) ⟨1675247, by rfl⟩ : syracuseStep 2233663 = 3350495) B3350495
theorem B3350501 : Blo 2233435 3350501 := bbase (se 4 (by rfl) ⟨314109, by rfl⟩ : syracuseStep 3350501 = 628219) (by norm_num)
theorem B2233667 : Blo 2233435 2233667 := bstep (se 1 (by rfl) ⟨1675250, by rfl⟩ : syracuseStep 2233667 = 3350501) B3350501
theorem B44716373 : Blo 2233435 44716373 := bbase (se 10 (by rfl) ⟨65502, by rfl⟩ : syracuseStep 44716373 = 131005) (by norm_num)
theorem B29810915 : Blo 2233435 29810915 := bstep (se 1 (by rfl) ⟨22358186, by rfl⟩ : syracuseStep 29810915 = 44716373) B44716373
theorem B19873943 : Blo 2233435 19873943 := bstep (se 1 (by rfl) ⟨14905457, by rfl⟩ : syracuseStep 19873943 = 29810915) B29810915
theorem B13249295 : Blo 2233435 13249295 := bstep (se 1 (by rfl) ⟨9936971, by rfl⟩ : syracuseStep 13249295 = 19873943) B19873943
theorem B8832863 : Blo 2233435 8832863 := bstep (se 1 (by rfl) ⟨6624647, by rfl⟩ : syracuseStep 8832863 = 13249295) B13249295
theorem B5888575 : Blo 2233435 5888575 := bstep (se 1 (by rfl) ⟨4416431, by rfl⟩ : syracuseStep 5888575 = 8832863) B8832863
theorem B7851433 : Blo 2233435 7851433 := bstep (se 2 (by rfl) ⟨2944287, by rfl⟩ : syracuseStep 7851433 = 5888575) B5888575
theorem B10468577 : Blo 2233435 10468577 := bstep (se 2 (by rfl) ⟨3925716, by rfl⟩ : syracuseStep 10468577 = 7851433) B7851433
theorem B6979051 : Blo 2233435 6979051 := bstep (se 1 (by rfl) ⟨5234288, by rfl⟩ : syracuseStep 6979051 = 10468577) B10468577
theorem B9305401 : Blo 2233435 9305401 := bstep (se 2 (by rfl) ⟨3489525, by rfl⟩ : syracuseStep 9305401 = 6979051) B6979051
theorem B12407201 : Blo 2233435 12407201 := bstep (se 2 (by rfl) ⟨4652700, by rfl⟩ : syracuseStep 12407201 = 9305401) B9305401
theorem B8271467 : Blo 2233435 8271467 := bstep (se 1 (by rfl) ⟨6203600, by rfl⟩ : syracuseStep 8271467 = 12407201) B12407201
theorem B5514311 : Blo 2233435 5514311 := bstep (se 1 (by rfl) ⟨4135733, by rfl⟩ : syracuseStep 5514311 = 8271467) B8271467
theorem B14704829 : Blo 2233435 14704829 := bstep (se 3 (by rfl) ⟨2757155, by rfl⟩ : syracuseStep 14704829 = 5514311) B5514311
theorem B9803219 : Blo 2233435 9803219 := bstep (se 1 (by rfl) ⟨7352414, by rfl⟩ : syracuseStep 9803219 = 14704829) B14704829
theorem B104567669 : Blo 2233435 104567669 := bstep (se 5 (by rfl) ⟨4901609, by rfl⟩ : syracuseStep 104567669 = 9803219) B9803219
theorem B69711779 : Blo 2233435 69711779 := bstep (se 1 (by rfl) ⟨52283834, by rfl⟩ : syracuseStep 69711779 = 104567669) B104567669
theorem B185898077 : Blo 2233435 185898077 := bstep (se 3 (by rfl) ⟨34855889, by rfl⟩ : syracuseStep 185898077 = 69711779) B69711779
theorem B123932051 : Blo 2233435 123932051 := bstep (se 1 (by rfl) ⟨92949038, by rfl⟩ : syracuseStep 123932051 = 185898077) B185898077
theorem B82621367 : Blo 2233435 82621367 := bstep (se 1 (by rfl) ⟨61966025, by rfl⟩ : syracuseStep 82621367 = 123932051) B123932051
theorem B55080911 : Blo 2233435 55080911 := bstep (se 1 (by rfl) ⟨41310683, by rfl⟩ : syracuseStep 55080911 = 82621367) B82621367
theorem B146882429 : Blo 2233435 146882429 := bstep (se 3 (by rfl) ⟨27540455, by rfl⟩ : syracuseStep 146882429 = 55080911) B55080911
theorem B97921619 : Blo 2233435 97921619 := bstep (se 1 (by rfl) ⟨73441214, by rfl⟩ : syracuseStep 97921619 = 146882429) B146882429
theorem B65281079 : Blo 2233435 65281079 := bstep (se 1 (by rfl) ⟨48960809, by rfl⟩ : syracuseStep 65281079 = 97921619) B97921619
theorem B174082877 : Blo 2233435 174082877 := bstep (se 3 (by rfl) ⟨32640539, by rfl⟩ : syracuseStep 174082877 = 65281079) B65281079
theorem B116055251 : Blo 2233435 116055251 := bstep (se 1 (by rfl) ⟨87041438, by rfl⟩ : syracuseStep 116055251 = 174082877) B174082877
theorem B77370167 : Blo 2233435 77370167 := bstep (se 1 (by rfl) ⟨58027625, by rfl⟩ : syracuseStep 77370167 = 116055251) B116055251
theorem B51580111 : Blo 2233435 51580111 := bstep (se 1 (by rfl) ⟨38685083, by rfl⟩ : syracuseStep 51580111 = 77370167) B77370167
theorem B68773481 : Blo 2233435 68773481 := bstep (se 2 (by rfl) ⟨25790055, by rfl⟩ : syracuseStep 68773481 = 51580111) B51580111
theorem B45848987 : Blo 2233435 45848987 := bstep (se 1 (by rfl) ⟨34386740, by rfl⟩ : syracuseStep 45848987 = 68773481) B68773481
theorem B30565991 : Blo 2233435 30565991 := bstep (se 1 (by rfl) ⟨22924493, by rfl⟩ : syracuseStep 30565991 = 45848987) B45848987
theorem B20377327 : Blo 2233435 20377327 := bstep (se 1 (by rfl) ⟨15282995, by rfl⟩ : syracuseStep 20377327 = 30565991) B30565991
theorem B27169769 : Blo 2233435 27169769 := bstep (se 2 (by rfl) ⟨10188663, by rfl⟩ : syracuseStep 27169769 = 20377327) B20377327
theorem B18113179 : Blo 2233435 18113179 := bstep (se 1 (by rfl) ⟨13584884, by rfl⟩ : syracuseStep 18113179 = 27169769) B27169769
theorem B24150905 : Blo 2233435 24150905 := bstep (se 2 (by rfl) ⟨9056589, by rfl⟩ : syracuseStep 24150905 = 18113179) B18113179
theorem B16100603 : Blo 2233435 16100603 := bstep (se 1 (by rfl) ⟨12075452, by rfl⟩ : syracuseStep 16100603 = 24150905) B24150905
theorem B10733735 : Blo 2233435 10733735 := bstep (se 1 (by rfl) ⟨8050301, by rfl⟩ : syracuseStep 10733735 = 16100603) B16100603
theorem B7155823 : Blo 2233435 7155823 := bstep (se 1 (by rfl) ⟨5366867, by rfl⟩ : syracuseStep 7155823 = 10733735) B10733735
theorem B9541097 : Blo 2233435 9541097 := bstep (se 2 (by rfl) ⟨3577911, by rfl⟩ : syracuseStep 9541097 = 7155823) B7155823
theorem B6360731 : Blo 2233435 6360731 := bstep (se 1 (by rfl) ⟨4770548, by rfl⟩ : syracuseStep 6360731 = 9541097) B9541097
theorem B4240487 : Blo 2233435 4240487 := bstep (se 1 (by rfl) ⟨3180365, by rfl⟩ : syracuseStep 4240487 = 6360731) B6360731
theorem B2826991 : Blo 2233435 2826991 := bstep (se 1 (by rfl) ⟨2120243, by rfl⟩ : syracuseStep 2826991 = 4240487) B4240487
theorem B3769321 : Blo 2233435 3769321 := bstep (se 2 (by rfl) ⟨1413495, by rfl⟩ : syracuseStep 3769321 = 2826991) B2826991
theorem B5025761 : Blo 2233435 5025761 := bstep (se 2 (by rfl) ⟨1884660, by rfl⟩ : syracuseStep 5025761 = 3769321) B3769321
theorem B3350507 : Blo 2233435 3350507 := bstep (se 1 (by rfl) ⟨2512880, by rfl⟩ : syracuseStep 3350507 = 5025761) B5025761
theorem B2233671 : Blo 2233435 2233671 := bstep (se 1 (by rfl) ⟨1675253, by rfl⟩ : syracuseStep 2233671 = 3350507) B3350507
theorem B2512885 : Blo 2233435 2512885 := bbase (se 5 (by rfl) ⟨117791, by rfl⟩ : syracuseStep 2512885 = 235583) (by norm_num)
theorem B3350513 : Blo 2233435 3350513 := bstep (se 2 (by rfl) ⟨1256442, by rfl⟩ : syracuseStep 3350513 = 2512885) B2512885
theorem B2233675 : Blo 2233435 2233675 := bstep (se 1 (by rfl) ⟨1675256, by rfl⟩ : syracuseStep 2233675 = 3350513) B3350513
theorem B2827001 : Blo 2233435 2827001 := bbase (se 2 (by rfl) ⟨1060125, by rfl⟩ : syracuseStep 2827001 = 2120251) (by norm_num)
theorem B7538669 : Blo 2233435 7538669 := bstep (se 3 (by rfl) ⟨1413500, by rfl⟩ : syracuseStep 7538669 = 2827001) B2827001
theorem B5025779 : Blo 2233435 5025779 := bstep (se 1 (by rfl) ⟨3769334, by rfl⟩ : syracuseStep 5025779 = 7538669) B7538669
theorem B3350519 : Blo 2233435 3350519 := bstep (se 1 (by rfl) ⟨2512889, by rfl⟩ : syracuseStep 3350519 = 5025779) B5025779
theorem B2233679 : Blo 2233435 2233679 := bstep (se 1 (by rfl) ⟨1675259, by rfl⟩ : syracuseStep 2233679 = 3350519) B3350519
theorem B3350525 : Blo 2233435 3350525 := bbase (se 3 (by rfl) ⟨628223, by rfl⟩ : syracuseStep 3350525 = 1256447) (by norm_num)
theorem B2233683 : Blo 2233435 2233683 := bstep (se 1 (by rfl) ⟨1675262, by rfl⟩ : syracuseStep 2233683 = 3350525) B3350525
theorem B5025797 : Blo 2233435 5025797 := bbase (se 4 (by rfl) ⟨471168, by rfl⟩ : syracuseStep 5025797 = 942337) (by norm_num)
theorem B3350531 : Blo 2233435 3350531 := bstep (se 1 (by rfl) ⟨2512898, by rfl⟩ : syracuseStep 3350531 = 5025797) B5025797
theorem B2233687 : Blo 2233435 2233687 := bstep (se 1 (by rfl) ⟨1675265, by rfl⟩ : syracuseStep 2233687 = 3350531) B3350531
theorem B4240525 : Blo 2233435 4240525 := bbase (se 3 (by rfl) ⟨795098, by rfl⟩ : syracuseStep 4240525 = 1590197) (by norm_num)
theorem B5654033 : Blo 2233435 5654033 := bstep (se 2 (by rfl) ⟨2120262, by rfl⟩ : syracuseStep 5654033 = 4240525) B4240525
theorem B3769355 : Blo 2233435 3769355 := bstep (se 1 (by rfl) ⟨2827016, by rfl⟩ : syracuseStep 3769355 = 5654033) B5654033
theorem B2512903 : Blo 2233435 2512903 := bstep (se 1 (by rfl) ⟨1884677, by rfl⟩ : syracuseStep 2512903 = 3769355) B3769355
theorem B3350537 : Blo 2233435 3350537 := bstep (se 2 (by rfl) ⟨1256451, by rfl⟩ : syracuseStep 3350537 = 2512903) B2512903
theorem B2233691 : Blo 2233435 2233691 := bstep (se 1 (by rfl) ⟨1675268, by rfl⟩ : syracuseStep 2233691 = 3350537) B3350537
theorem B11308085 : Blo 2233435 11308085 := bbase (se 5 (by rfl) ⟨530066, by rfl⟩ : syracuseStep 11308085 = 1060133) (by norm_num)
theorem B7538723 : Blo 2233435 7538723 := bstep (se 1 (by rfl) ⟨5654042, by rfl⟩ : syracuseStep 7538723 = 11308085) B11308085
theorem B5025815 : Blo 2233435 5025815 := bstep (se 1 (by rfl) ⟨3769361, by rfl⟩ : syracuseStep 5025815 = 7538723) B7538723
theorem B3350543 : Blo 2233435 3350543 := bstep (se 1 (by rfl) ⟨2512907, by rfl⟩ : syracuseStep 3350543 = 5025815) B5025815
theorem B2233695 : Blo 2233435 2233695 := bstep (se 1 (by rfl) ⟨1675271, by rfl⟩ : syracuseStep 2233695 = 3350543) B3350543
theorem B3350549 : Blo 2233435 3350549 := bbase (se 6 (by rfl) ⟨78528, by rfl⟩ : syracuseStep 3350549 = 157057) (by norm_num)
theorem B2233699 : Blo 2233435 2233699 := bstep (se 1 (by rfl) ⟨1675274, by rfl⟩ : syracuseStep 2233699 = 3350549) B3350549
theorem B6447605 : Blo 2233435 6447605 := bbase (se 5 (by rfl) ⟨302231, by rfl⟩ : syracuseStep 6447605 = 604463) (by norm_num)
theorem B68774453 : Blo 2233435 68774453 := bstep (se 5 (by rfl) ⟨3223802, by rfl⟩ : syracuseStep 68774453 = 6447605) B6447605
theorem B45849635 : Blo 2233435 45849635 := bstep (se 1 (by rfl) ⟨34387226, by rfl⟩ : syracuseStep 45849635 = 68774453) B68774453
theorem B30566423 : Blo 2233435 30566423 := bstep (se 1 (by rfl) ⟨22924817, by rfl⟩ : syracuseStep 30566423 = 45849635) B45849635
theorem B81510461 : Blo 2233435 81510461 := bstep (se 3 (by rfl) ⟨15283211, by rfl⟩ : syracuseStep 81510461 = 30566423) B30566423
theorem B54340307 : Blo 2233435 54340307 := bstep (se 1 (by rfl) ⟨40755230, by rfl⟩ : syracuseStep 54340307 = 81510461) B81510461
theorem B36226871 : Blo 2233435 36226871 := bstep (se 1 (by rfl) ⟨27170153, by rfl⟩ : syracuseStep 36226871 = 54340307) B54340307
theorem B24151247 : Blo 2233435 24151247 := bstep (se 1 (by rfl) ⟨18113435, by rfl⟩ : syracuseStep 24151247 = 36226871) B36226871
theorem B16100831 : Blo 2233435 16100831 := bstep (se 1 (by rfl) ⟨12075623, by rfl⟩ : syracuseStep 16100831 = 24151247) B24151247
theorem B10733887 : Blo 2233435 10733887 := bstep (se 1 (by rfl) ⟨8050415, by rfl⟩ : syracuseStep 10733887 = 16100831) B16100831
theorem B14311849 : Blo 2233435 14311849 := bstep (se 2 (by rfl) ⟨5366943, by rfl⟩ : syracuseStep 14311849 = 10733887) B10733887
theorem B19082465 : Blo 2233435 19082465 := bstep (se 2 (by rfl) ⟨7155924, by rfl⟩ : syracuseStep 19082465 = 14311849) B14311849
theorem B12721643 : Blo 2233435 12721643 := bstep (se 1 (by rfl) ⟨9541232, by rfl⟩ : syracuseStep 12721643 = 19082465) B19082465
theorem B8481095 : Blo 2233435 8481095 := bstep (se 1 (by rfl) ⟨6360821, by rfl⟩ : syracuseStep 8481095 = 12721643) B12721643
theorem B5654063 : Blo 2233435 5654063 := bstep (se 1 (by rfl) ⟨4240547, by rfl⟩ : syracuseStep 5654063 = 8481095) B8481095
theorem B3769375 : Blo 2233435 3769375 := bstep (se 1 (by rfl) ⟨2827031, by rfl⟩ : syracuseStep 3769375 = 5654063) B5654063
theorem B5025833 : Blo 2233435 5025833 := bstep (se 2 (by rfl) ⟨1884687, by rfl⟩ : syracuseStep 5025833 = 3769375) B3769375
theorem B3350555 : Blo 2233435 3350555 := bstep (se 1 (by rfl) ⟨2512916, by rfl⟩ : syracuseStep 3350555 = 5025833) B5025833
theorem B2233703 : Blo 2233435 2233703 := bstep (se 1 (by rfl) ⟨1675277, by rfl⟩ : syracuseStep 2233703 = 3350555) B3350555
theorem B2512921 : Blo 2233435 2512921 := bbase (se 2 (by rfl) ⟨942345, by rfl⟩ : syracuseStep 2512921 = 1884691) (by norm_num)
theorem B3350561 : Blo 2233435 3350561 := bstep (se 2 (by rfl) ⟨1256460, by rfl⟩ : syracuseStep 3350561 = 2512921) B2512921
theorem B2233707 : Blo 2233435 2233707 := bstep (se 1 (by rfl) ⟨1675280, by rfl⟩ : syracuseStep 2233707 = 3350561) B3350561
theorem B8481125 : Blo 2233435 8481125 := bbase (se 4 (by rfl) ⟨795105, by rfl⟩ : syracuseStep 8481125 = 1590211) (by norm_num)
theorem B5654083 : Blo 2233435 5654083 := bstep (se 1 (by rfl) ⟨4240562, by rfl⟩ : syracuseStep 5654083 = 8481125) B8481125
theorem B7538777 : Blo 2233435 7538777 := bstep (se 2 (by rfl) ⟨2827041, by rfl⟩ : syracuseStep 7538777 = 5654083) B5654083
theorem B5025851 : Blo 2233435 5025851 := bstep (se 1 (by rfl) ⟨3769388, by rfl⟩ : syracuseStep 5025851 = 7538777) B7538777
theorem B3350567 : Blo 2233435 3350567 := bstep (se 1 (by rfl) ⟨2512925, by rfl⟩ : syracuseStep 3350567 = 5025851) B5025851
theorem B2233711 : Blo 2233435 2233711 := bstep (se 1 (by rfl) ⟨1675283, by rfl⟩ : syracuseStep 2233711 = 3350567) B3350567
theorem B3350573 : Blo 2233435 3350573 := bbase (se 3 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 3350573 = 1256465) (by norm_num)
theorem B2233715 : Blo 2233435 2233715 := bstep (se 1 (by rfl) ⟨1675286, by rfl⟩ : syracuseStep 2233715 = 3350573) B3350573
theorem B5025869 : Blo 2233435 5025869 := bbase (se 3 (by rfl) ⟨942350, by rfl⟩ : syracuseStep 5025869 = 1884701) (by norm_num)
theorem B3350579 : Blo 2233435 3350579 := bstep (se 1 (by rfl) ⟨2512934, by rfl⟩ : syracuseStep 3350579 = 5025869) B5025869
theorem B2233719 : Blo 2233435 2233719 := bstep (se 1 (by rfl) ⟨1675289, by rfl⟩ : syracuseStep 2233719 = 3350579) B3350579
theorem B2827057 : Blo 2233435 2827057 := bbase (se 2 (by rfl) ⟨1060146, by rfl⟩ : syracuseStep 2827057 = 2120293) (by norm_num)
theorem B3769409 : Blo 2233435 3769409 := bstep (se 2 (by rfl) ⟨1413528, by rfl⟩ : syracuseStep 3769409 = 2827057) B2827057
theorem B2512939 : Blo 2233435 2512939 := bstep (se 1 (by rfl) ⟨1884704, by rfl⟩ : syracuseStep 2512939 = 3769409) B3769409
theorem B3350585 : Blo 2233435 3350585 := bstep (se 2 (by rfl) ⟨1256469, by rfl⟩ : syracuseStep 3350585 = 2512939) B2512939
theorem B2233723 : Blo 2233435 2233723 := bstep (se 1 (by rfl) ⟨1675292, by rfl⟩ : syracuseStep 2233723 = 3350585) B3350585
theorem B6037877 : Blo 2233435 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B4025251 : Blo 2233435 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B5367001 : Blo 2233435 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B7156001 : Blo 2233435 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B4770667 : Blo 2233435 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B25443557 : Blo 2233435 25443557 := bstep (se 4 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 25443557 = 4770667) B4770667
theorem B16962371 : Blo 2233435 16962371 := bstep (se 1 (by rfl) ⟨12721778, by rfl⟩ : syracuseStep 16962371 = 25443557) B25443557
theorem B11308247 : Blo 2233435 11308247 := bstep (se 1 (by rfl) ⟨8481185, by rfl⟩ : syracuseStep 11308247 = 16962371) B16962371
theorem B7538831 : Blo 2233435 7538831 := bstep (se 1 (by rfl) ⟨5654123, by rfl⟩ : syracuseStep 7538831 = 11308247) B11308247
theorem B5025887 : Blo 2233435 5025887 := bstep (se 1 (by rfl) ⟨3769415, by rfl⟩ : syracuseStep 5025887 = 7538831) B7538831
theorem B3350591 : Blo 2233435 3350591 := bstep (se 1 (by rfl) ⟨2512943, by rfl⟩ : syracuseStep 3350591 = 5025887) B5025887
theorem B2233727 : Blo 2233435 2233727 := bstep (se 1 (by rfl) ⟨1675295, by rfl⟩ : syracuseStep 2233727 = 3350591) B3350591
theorem B3350597 : Blo 2233435 3350597 := bbase (se 4 (by rfl) ⟨314118, by rfl⟩ : syracuseStep 3350597 = 628237) (by norm_num)
theorem B2233731 : Blo 2233435 2233731 := bstep (se 1 (by rfl) ⟨1675298, by rfl⟩ : syracuseStep 2233731 = 3350597) B3350597
theorem B3769429 : Blo 2233435 3769429 := bbase (se 8 (by rfl) ⟨22086, by rfl⟩ : syracuseStep 3769429 = 44173) (by norm_num)
theorem B5025905 : Blo 2233435 5025905 := bstep (se 2 (by rfl) ⟨1884714, by rfl⟩ : syracuseStep 5025905 = 3769429) B3769429
theorem B3350603 : Blo 2233435 3350603 := bstep (se 1 (by rfl) ⟨2512952, by rfl⟩ : syracuseStep 3350603 = 5025905) B5025905
theorem B2233735 : Blo 2233435 2233735 := bstep (se 1 (by rfl) ⟨1675301, by rfl⟩ : syracuseStep 2233735 = 3350603) B3350603
theorem B2512957 : Blo 2233435 2512957 := bbase (se 3 (by rfl) ⟨471179, by rfl⟩ : syracuseStep 2512957 = 942359) (by norm_num)
theorem B3350609 : Blo 2233435 3350609 := bstep (se 2 (by rfl) ⟨1256478, by rfl⟩ : syracuseStep 3350609 = 2512957) B2512957
theorem B2233739 : Blo 2233435 2233739 := bstep (se 1 (by rfl) ⟨1675304, by rfl⟩ : syracuseStep 2233739 = 3350609) B3350609
theorem B7538885 : Blo 2233435 7538885 := bbase (se 4 (by rfl) ⟨706770, by rfl⟩ : syracuseStep 7538885 = 1413541) (by norm_num)
theorem B5025923 : Blo 2233435 5025923 := bstep (se 1 (by rfl) ⟨3769442, by rfl⟩ : syracuseStep 5025923 = 7538885) B7538885
theorem B3350615 : Blo 2233435 3350615 := bstep (se 1 (by rfl) ⟨2512961, by rfl⟩ : syracuseStep 3350615 = 5025923) B5025923
theorem B2233743 : Blo 2233435 2233743 := bstep (se 1 (by rfl) ⟨1675307, by rfl⟩ : syracuseStep 2233743 = 3350615) B3350615
theorem B3350621 : Blo 2233435 3350621 := bbase (se 3 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 3350621 = 1256483) (by norm_num)
theorem B2233747 : Blo 2233435 2233747 := bstep (se 1 (by rfl) ⟨1675310, by rfl⟩ : syracuseStep 2233747 = 3350621) B3350621
theorem B5025941 : Blo 2233435 5025941 := bbase (se 6 (by rfl) ⟨117795, by rfl⟩ : syracuseStep 5025941 = 235591) (by norm_num)
theorem B3350627 : Blo 2233435 3350627 := bstep (se 1 (by rfl) ⟨2512970, by rfl⟩ : syracuseStep 3350627 = 5025941) B5025941
theorem B2233751 : Blo 2233435 2233751 := bstep (se 1 (by rfl) ⟨1675313, by rfl⟩ : syracuseStep 2233751 = 3350627) B3350627
theorem B3180485 : Blo 2233435 3180485 := bbase (se 4 (by rfl) ⟨298170, by rfl⟩ : syracuseStep 3180485 = 596341) (by norm_num)
theorem B8481293 : Blo 2233435 8481293 := bstep (se 3 (by rfl) ⟨1590242, by rfl⟩ : syracuseStep 8481293 = 3180485) B3180485
theorem B5654195 : Blo 2233435 5654195 := bstep (se 1 (by rfl) ⟨4240646, by rfl⟩ : syracuseStep 5654195 = 8481293) B8481293
theorem B3769463 : Blo 2233435 3769463 := bstep (se 1 (by rfl) ⟨2827097, by rfl⟩ : syracuseStep 3769463 = 5654195) B5654195
theorem B2512975 : Blo 2233435 2512975 := bstep (se 1 (by rfl) ⟨1884731, by rfl⟩ : syracuseStep 2512975 = 3769463) B3769463
theorem B3350633 : Blo 2233435 3350633 := bstep (se 2 (by rfl) ⟨1256487, by rfl⟩ : syracuseStep 3350633 = 2512975) B2512975
theorem B2233755 : Blo 2233435 2233755 := bstep (se 1 (by rfl) ⟨1675316, by rfl⟩ : syracuseStep 2233755 = 3350633) B3350633
theorem B48303701 : Blo 2233435 48303701 := bbase (se 8 (by rfl) ⟨283029, by rfl⟩ : syracuseStep 48303701 = 566059) (by norm_num)
theorem B32202467 : Blo 2233435 32202467 := bstep (se 1 (by rfl) ⟨24151850, by rfl⟩ : syracuseStep 32202467 = 48303701) B48303701
theorem B21468311 : Blo 2233435 21468311 := bstep (se 1 (by rfl) ⟨16101233, by rfl⟩ : syracuseStep 21468311 = 32202467) B32202467
theorem B14312207 : Blo 2233435 14312207 := bstep (se 1 (by rfl) ⟨10734155, by rfl⟩ : syracuseStep 14312207 = 21468311) B21468311
theorem B9541471 : Blo 2233435 9541471 := bstep (se 1 (by rfl) ⟨7156103, by rfl⟩ : syracuseStep 9541471 = 14312207) B14312207
theorem B12721961 : Blo 2233435 12721961 := bstep (se 2 (by rfl) ⟨4770735, by rfl⟩ : syracuseStep 12721961 = 9541471) B9541471
theorem B8481307 : Blo 2233435 8481307 := bstep (se 1 (by rfl) ⟨6360980, by rfl⟩ : syracuseStep 8481307 = 12721961) B12721961
theorem B11308409 : Blo 2233435 11308409 := bstep (se 2 (by rfl) ⟨4240653, by rfl⟩ : syracuseStep 11308409 = 8481307) B8481307
theorem B7538939 : Blo 2233435 7538939 := bstep (se 1 (by rfl) ⟨5654204, by rfl⟩ : syracuseStep 7538939 = 11308409) B11308409
theorem B5025959 : Blo 2233435 5025959 := bstep (se 1 (by rfl) ⟨3769469, by rfl⟩ : syracuseStep 5025959 = 7538939) B7538939
theorem B3350639 : Blo 2233435 3350639 := bstep (se 1 (by rfl) ⟨2512979, by rfl⟩ : syracuseStep 3350639 = 5025959) B5025959
theorem B2233759 : Blo 2233435 2233759 := bstep (se 1 (by rfl) ⟨1675319, by rfl⟩ : syracuseStep 2233759 = 3350639) B3350639
theorem B3350645 : Blo 2233435 3350645 := bbase (se 5 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 3350645 = 314123) (by norm_num)
theorem B2233763 : Blo 2233435 2233763 := bstep (se 1 (by rfl) ⟨1675322, by rfl⟩ : syracuseStep 2233763 = 3350645) B3350645
theorem B4240669 : Blo 2233435 4240669 := bbase (se 3 (by rfl) ⟨795125, by rfl⟩ : syracuseStep 4240669 = 1590251) (by norm_num)
theorem B5654225 : Blo 2233435 5654225 := bstep (se 2 (by rfl) ⟨2120334, by rfl⟩ : syracuseStep 5654225 = 4240669) B4240669
theorem B3769483 : Blo 2233435 3769483 := bstep (se 1 (by rfl) ⟨2827112, by rfl⟩ : syracuseStep 3769483 = 5654225) B5654225
theorem B5025977 : Blo 2233435 5025977 := bstep (se 2 (by rfl) ⟨1884741, by rfl⟩ : syracuseStep 5025977 = 3769483) B3769483
theorem B3350651 : Blo 2233435 3350651 := bstep (se 1 (by rfl) ⟨2512988, by rfl⟩ : syracuseStep 3350651 = 5025977) B5025977
theorem B2233767 : Blo 2233435 2233767 := bstep (se 1 (by rfl) ⟨1675325, by rfl⟩ : syracuseStep 2233767 = 3350651) B3350651
theorem B2512993 : Blo 2233435 2512993 := bbase (se 2 (by rfl) ⟨942372, by rfl⟩ : syracuseStep 2512993 = 1884745) (by norm_num)
theorem B3350657 : Blo 2233435 3350657 := bstep (se 2 (by rfl) ⟨1256496, by rfl⟩ : syracuseStep 3350657 = 2512993) B2512993
theorem B2233771 : Blo 2233435 2233771 := bstep (se 1 (by rfl) ⟨1675328, by rfl⟩ : syracuseStep 2233771 = 3350657) B3350657
theorem B5654245 : Blo 2233435 5654245 := bbase (se 4 (by rfl) ⟨530085, by rfl⟩ : syracuseStep 5654245 = 1060171) (by norm_num)
theorem B7538993 : Blo 2233435 7538993 := bstep (se 2 (by rfl) ⟨2827122, by rfl⟩ : syracuseStep 7538993 = 5654245) B5654245
theorem B5025995 : Blo 2233435 5025995 := bstep (se 1 (by rfl) ⟨3769496, by rfl⟩ : syracuseStep 5025995 = 7538993) B7538993
theorem B3350663 : Blo 2233435 3350663 := bstep (se 1 (by rfl) ⟨2512997, by rfl⟩ : syracuseStep 3350663 = 5025995) B5025995
theorem B2233775 : Blo 2233435 2233775 := bstep (se 1 (by rfl) ⟨1675331, by rfl⟩ : syracuseStep 2233775 = 3350663) B3350663
theorem B3350669 : Blo 2233435 3350669 := bbase (se 3 (by rfl) ⟨628250, by rfl⟩ : syracuseStep 3350669 = 1256501) (by norm_num)
theorem B2233779 : Blo 2233435 2233779 := bstep (se 1 (by rfl) ⟨1675334, by rfl⟩ : syracuseStep 2233779 = 3350669) B3350669
theorem B5026013 : Blo 2233435 5026013 := bbase (se 3 (by rfl) ⟨942377, by rfl⟩ : syracuseStep 5026013 = 1884755) (by norm_num)
theorem B3350675 : Blo 2233435 3350675 := bstep (se 1 (by rfl) ⟨2513006, by rfl⟩ : syracuseStep 3350675 = 5026013) B5026013
theorem B2233783 : Blo 2233435 2233783 := bstep (se 1 (by rfl) ⟨1675337, by rfl⟩ : syracuseStep 2233783 = 3350675) B3350675
theorem B3769517 : Blo 2233435 3769517 := bbase (se 3 (by rfl) ⟨706784, by rfl⟩ : syracuseStep 3769517 = 1413569) (by norm_num)
theorem B2513011 : Blo 2233435 2513011 := bstep (se 1 (by rfl) ⟨1884758, by rfl⟩ : syracuseStep 2513011 = 3769517) B3769517
theorem B3350681 : Blo 2233435 3350681 := bstep (se 2 (by rfl) ⟨1256505, by rfl⟩ : syracuseStep 3350681 = 2513011) B2513011
theorem B2233787 : Blo 2233435 2233787 := bstep (se 1 (by rfl) ⟨1675340, by rfl⟩ : syracuseStep 2233787 = 3350681) B3350681
theorem B6792805 : Blo 2233435 6792805 := bbase (se 4 (by rfl) ⟨636825, by rfl⟩ : syracuseStep 6792805 = 1273651) (by norm_num)
theorem B36228293 : Blo 2233435 36228293 := bstep (se 4 (by rfl) ⟨3396402, by rfl⟩ : syracuseStep 36228293 = 6792805) B6792805
theorem B24152195 : Blo 2233435 24152195 := bstep (se 1 (by rfl) ⟨18114146, by rfl⟩ : syracuseStep 24152195 = 36228293) B36228293
theorem B64405853 : Blo 2233435 64405853 := bstep (se 3 (by rfl) ⟨12076097, by rfl⟩ : syracuseStep 64405853 = 24152195) B24152195
theorem B42937235 : Blo 2233435 42937235 := bstep (se 1 (by rfl) ⟨32202926, by rfl⟩ : syracuseStep 42937235 = 64405853) B64405853
theorem B28624823 : Blo 2233435 28624823 := bstep (se 1 (by rfl) ⟨21468617, by rfl⟩ : syracuseStep 28624823 = 42937235) B42937235
theorem B19083215 : Blo 2233435 19083215 := bstep (se 1 (by rfl) ⟨14312411, by rfl⟩ : syracuseStep 19083215 = 28624823) B28624823
theorem B12722143 : Blo 2233435 12722143 := bstep (se 1 (by rfl) ⟨9541607, by rfl⟩ : syracuseStep 12722143 = 19083215) B19083215
theorem B16962857 : Blo 2233435 16962857 := bstep (se 2 (by rfl) ⟨6361071, by rfl⟩ : syracuseStep 16962857 = 12722143) B12722143
theorem B11308571 : Blo 2233435 11308571 := bstep (se 1 (by rfl) ⟨8481428, by rfl⟩ : syracuseStep 11308571 = 16962857) B16962857
theorem B7539047 : Blo 2233435 7539047 := bstep (se 1 (by rfl) ⟨5654285, by rfl⟩ : syracuseStep 7539047 = 11308571) B11308571
theorem B5026031 : Blo 2233435 5026031 := bstep (se 1 (by rfl) ⟨3769523, by rfl⟩ : syracuseStep 5026031 = 7539047) B7539047
theorem B3350687 : Blo 2233435 3350687 := bstep (se 1 (by rfl) ⟨2513015, by rfl⟩ : syracuseStep 3350687 = 5026031) B5026031
theorem B2233791 : Blo 2233435 2233791 := bstep (se 1 (by rfl) ⟨1675343, by rfl⟩ : syracuseStep 2233791 = 3350687) B3350687
theorem B3350693 : Blo 2233435 3350693 := bbase (se 4 (by rfl) ⟨314127, by rfl⟩ : syracuseStep 3350693 = 628255) (by norm_num)
theorem B2233795 : Blo 2233435 2233795 := bstep (se 1 (by rfl) ⟨1675346, by rfl⟩ : syracuseStep 2233795 = 3350693) B3350693
theorem B2827153 : Blo 2233435 2827153 := bbase (se 2 (by rfl) ⟨1060182, by rfl⟩ : syracuseStep 2827153 = 2120365) (by norm_num)
theorem B3769537 : Blo 2233435 3769537 := bstep (se 2 (by rfl) ⟨1413576, by rfl⟩ : syracuseStep 3769537 = 2827153) B2827153
theorem B5026049 : Blo 2233435 5026049 := bstep (se 2 (by rfl) ⟨1884768, by rfl⟩ : syracuseStep 5026049 = 3769537) B3769537
theorem B3350699 : Blo 2233435 3350699 := bstep (se 1 (by rfl) ⟨2513024, by rfl⟩ : syracuseStep 3350699 = 5026049) B5026049
theorem B2233799 : Blo 2233435 2233799 := bstep (se 1 (by rfl) ⟨1675349, by rfl⟩ : syracuseStep 2233799 = 3350699) B3350699
theorem B2513029 : Blo 2233435 2513029 := bbase (se 4 (by rfl) ⟨235596, by rfl⟩ : syracuseStep 2513029 = 471193) (by norm_num)
theorem B3350705 : Blo 2233435 3350705 := bstep (se 2 (by rfl) ⟨1256514, by rfl⟩ : syracuseStep 3350705 = 2513029) B2513029
theorem B2233803 : Blo 2233435 2233803 := bstep (se 1 (by rfl) ⟨1675352, by rfl⟩ : syracuseStep 2233803 = 3350705) B3350705
theorem B10734389 : Blo 2233435 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B7156259 : Blo 2233435 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B4770839 : Blo 2233435 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B3180559 : Blo 2233435 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B4240745 : Blo 2233435 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B2827163 : Blo 2233435 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B7539101 : Blo 2233435 7539101 := bstep (se 3 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 7539101 = 2827163) B2827163
theorem B5026067 : Blo 2233435 5026067 := bstep (se 1 (by rfl) ⟨3769550, by rfl⟩ : syracuseStep 5026067 = 7539101) B7539101
theorem B3350711 : Blo 2233435 3350711 := bstep (se 1 (by rfl) ⟨2513033, by rfl⟩ : syracuseStep 3350711 = 5026067) B5026067
theorem B2233807 : Blo 2233435 2233807 := bstep (se 1 (by rfl) ⟨1675355, by rfl⟩ : syracuseStep 2233807 = 3350711) B3350711
theorem B3350717 : Blo 2233435 3350717 := bbase (se 3 (by rfl) ⟨628259, by rfl⟩ : syracuseStep 3350717 = 1256519) (by norm_num)
theorem B2233811 : Blo 2233435 2233811 := bstep (se 1 (by rfl) ⟨1675358, by rfl⟩ : syracuseStep 2233811 = 3350717) B3350717
theorem B5026085 : Blo 2233435 5026085 := bbase (se 4 (by rfl) ⟨471195, by rfl⟩ : syracuseStep 5026085 = 942391) (by norm_num)
theorem B3350723 : Blo 2233435 3350723 := bstep (se 1 (by rfl) ⟨2513042, by rfl⟩ : syracuseStep 3350723 = 5026085) B5026085
theorem B2233815 : Blo 2233435 2233815 := bstep (se 1 (by rfl) ⟨1675361, by rfl⟩ : syracuseStep 2233815 = 3350723) B3350723
theorem B5654357 : Blo 2233435 5654357 := bbase (se 9 (by rfl) ⟨16565, by rfl⟩ : syracuseStep 5654357 = 33131) (by norm_num)
theorem B3769571 : Blo 2233435 3769571 := bstep (se 1 (by rfl) ⟨2827178, by rfl⟩ : syracuseStep 3769571 = 5654357) B5654357
theorem B2513047 : Blo 2233435 2513047 := bstep (se 1 (by rfl) ⟨1884785, by rfl⟩ : syracuseStep 2513047 = 3769571) B3769571
theorem B3350729 : Blo 2233435 3350729 := bstep (se 2 (by rfl) ⟨1256523, by rfl⟩ : syracuseStep 3350729 = 2513047) B2513047
theorem B2233819 : Blo 2233435 2233819 := bstep (se 1 (by rfl) ⟨1675364, by rfl⟩ : syracuseStep 2233819 = 3350729) B3350729
theorem B7156309 : Blo 2233435 7156309 := bbase (se 8 (by rfl) ⟨41931, by rfl⟩ : syracuseStep 7156309 = 83863) (by norm_num)
theorem B9541745 : Blo 2233435 9541745 := bstep (se 2 (by rfl) ⟨3578154, by rfl⟩ : syracuseStep 9541745 = 7156309) B7156309
theorem B6361163 : Blo 2233435 6361163 := bstep (se 1 (by rfl) ⟨4770872, by rfl⟩ : syracuseStep 6361163 = 9541745) B9541745
theorem B4240775 : Blo 2233435 4240775 := bstep (se 1 (by rfl) ⟨3180581, by rfl⟩ : syracuseStep 4240775 = 6361163) B6361163
theorem B11308733 : Blo 2233435 11308733 := bstep (se 3 (by rfl) ⟨2120387, by rfl⟩ : syracuseStep 11308733 = 4240775) B4240775
theorem B7539155 : Blo 2233435 7539155 := bstep (se 1 (by rfl) ⟨5654366, by rfl⟩ : syracuseStep 7539155 = 11308733) B11308733
theorem B5026103 : Blo 2233435 5026103 := bstep (se 1 (by rfl) ⟨3769577, by rfl⟩ : syracuseStep 5026103 = 7539155) B7539155
theorem B3350735 : Blo 2233435 3350735 := bstep (se 1 (by rfl) ⟨2513051, by rfl⟩ : syracuseStep 3350735 = 5026103) B5026103
theorem B2233823 : Blo 2233435 2233823 := bstep (se 1 (by rfl) ⟨1675367, by rfl⟩ : syracuseStep 2233823 = 3350735) B3350735
theorem B3350741 : Blo 2233435 3350741 := bbase (se 7 (by rfl) ⟨39266, by rfl⟩ : syracuseStep 3350741 = 78533) (by norm_num)
theorem B2233827 : Blo 2233435 2233827 := bstep (se 1 (by rfl) ⟨1675370, by rfl⟩ : syracuseStep 2233827 = 3350741) B3350741
theorem B2385445 : Blo 2233435 2385445 := bbase (se 4 (by rfl) ⟨223635, by rfl⟩ : syracuseStep 2385445 = 447271) (by norm_num)
theorem B3180593 : Blo 2233435 3180593 := bstep (se 2 (by rfl) ⟨1192722, by rfl⟩ : syracuseStep 3180593 = 2385445) B2385445
theorem B8481581 : Blo 2233435 8481581 := bstep (se 3 (by rfl) ⟨1590296, by rfl⟩ : syracuseStep 8481581 = 3180593) B3180593
theorem B5654387 : Blo 2233435 5654387 := bstep (se 1 (by rfl) ⟨4240790, by rfl⟩ : syracuseStep 5654387 = 8481581) B8481581
theorem B3769591 : Blo 2233435 3769591 := bstep (se 1 (by rfl) ⟨2827193, by rfl⟩ : syracuseStep 3769591 = 5654387) B5654387
theorem B5026121 : Blo 2233435 5026121 := bstep (se 2 (by rfl) ⟨1884795, by rfl⟩ : syracuseStep 5026121 = 3769591) B3769591
theorem B3350747 : Blo 2233435 3350747 := bstep (se 1 (by rfl) ⟨2513060, by rfl⟩ : syracuseStep 3350747 = 5026121) B5026121
theorem B2233831 : Blo 2233435 2233831 := bstep (se 1 (by rfl) ⟨1675373, by rfl⟩ : syracuseStep 2233831 = 3350747) B3350747
theorem B2513065 : Blo 2233435 2513065 := bbase (se 2 (by rfl) ⟨942399, by rfl⟩ : syracuseStep 2513065 = 1884799) (by norm_num)
theorem B3350753 : Blo 2233435 3350753 := bstep (se 2 (by rfl) ⟨1256532, by rfl⟩ : syracuseStep 3350753 = 2513065) B2513065
theorem B2233835 : Blo 2233435 2233835 := bstep (se 1 (by rfl) ⟨1675376, by rfl⟩ : syracuseStep 2233835 = 3350753) B3350753
theorem B9541813 : Blo 2233435 9541813 := bbase (se 5 (by rfl) ⟨447272, by rfl⟩ : syracuseStep 9541813 = 894545) (by norm_num)
theorem B12722417 : Blo 2233435 12722417 := bstep (se 2 (by rfl) ⟨4770906, by rfl⟩ : syracuseStep 12722417 = 9541813) B9541813
theorem B8481611 : Blo 2233435 8481611 := bstep (se 1 (by rfl) ⟨6361208, by rfl⟩ : syracuseStep 8481611 = 12722417) B12722417
theorem B5654407 : Blo 2233435 5654407 := bstep (se 1 (by rfl) ⟨4240805, by rfl⟩ : syracuseStep 5654407 = 8481611) B8481611
theorem B7539209 : Blo 2233435 7539209 := bstep (se 2 (by rfl) ⟨2827203, by rfl⟩ : syracuseStep 7539209 = 5654407) B5654407
theorem B5026139 : Blo 2233435 5026139 := bstep (se 1 (by rfl) ⟨3769604, by rfl⟩ : syracuseStep 5026139 = 7539209) B7539209
theorem B3350759 : Blo 2233435 3350759 := bstep (se 1 (by rfl) ⟨2513069, by rfl⟩ : syracuseStep 3350759 = 5026139) B5026139
theorem B2233839 : Blo 2233435 2233839 := bstep (se 1 (by rfl) ⟨1675379, by rfl⟩ : syracuseStep 2233839 = 3350759) B3350759
theorem B3350765 : Blo 2233435 3350765 := bbase (se 3 (by rfl) ⟨628268, by rfl⟩ : syracuseStep 3350765 = 1256537) (by norm_num)
theorem B2233843 : Blo 2233435 2233843 := bstep (se 1 (by rfl) ⟨1675382, by rfl⟩ : syracuseStep 2233843 = 3350765) B3350765
theorem B5026157 : Blo 2233435 5026157 := bbase (se 3 (by rfl) ⟨942404, by rfl⟩ : syracuseStep 5026157 = 1884809) (by norm_num)
theorem B3350771 : Blo 2233435 3350771 := bstep (se 1 (by rfl) ⟨2513078, by rfl⟩ : syracuseStep 3350771 = 5026157) B5026157
theorem B2233847 : Blo 2233435 2233847 := bstep (se 1 (by rfl) ⟨1675385, by rfl⟩ : syracuseStep 2233847 = 3350771) B3350771
theorem B4240829 : Blo 2233435 4240829 := bbase (se 3 (by rfl) ⟨795155, by rfl⟩ : syracuseStep 4240829 = 1590311) (by norm_num)
theorem B2827219 : Blo 2233435 2827219 := bstep (se 1 (by rfl) ⟨2120414, by rfl⟩ : syracuseStep 2827219 = 4240829) B4240829
theorem B3769625 : Blo 2233435 3769625 := bstep (se 2 (by rfl) ⟨1413609, by rfl⟩ : syracuseStep 3769625 = 2827219) B2827219
theorem B2513083 : Blo 2233435 2513083 := bstep (se 1 (by rfl) ⟨1884812, by rfl⟩ : syracuseStep 2513083 = 3769625) B3769625
theorem B3350777 : Blo 2233435 3350777 := bstep (se 2 (by rfl) ⟨1256541, by rfl⟩ : syracuseStep 3350777 = 2513083) B2513083
theorem B2233851 : Blo 2233435 2233851 := bstep (se 1 (by rfl) ⟨1675388, by rfl⟩ : syracuseStep 2233851 = 3350777) B3350777
theorem B57251285 : Blo 2233435 57251285 := bbase (se 7 (by rfl) ⟨670913, by rfl⟩ : syracuseStep 57251285 = 1341827) (by norm_num)
theorem B38167523 : Blo 2233435 38167523 := bstep (se 1 (by rfl) ⟨28625642, by rfl⟩ : syracuseStep 38167523 = 57251285) B57251285
theorem B25445015 : Blo 2233435 25445015 := bstep (se 1 (by rfl) ⟨19083761, by rfl⟩ : syracuseStep 25445015 = 38167523) B38167523
theorem B16963343 : Blo 2233435 16963343 := bstep (se 1 (by rfl) ⟨12722507, by rfl⟩ : syracuseStep 16963343 = 25445015) B25445015
theorem B11308895 : Blo 2233435 11308895 := bstep (se 1 (by rfl) ⟨8481671, by rfl⟩ : syracuseStep 11308895 = 16963343) B16963343
theorem B7539263 : Blo 2233435 7539263 := bstep (se 1 (by rfl) ⟨5654447, by rfl⟩ : syracuseStep 7539263 = 11308895) B11308895
theorem B5026175 : Blo 2233435 5026175 := bstep (se 1 (by rfl) ⟨3769631, by rfl⟩ : syracuseStep 5026175 = 7539263) B7539263
theorem B3350783 : Blo 2233435 3350783 := bstep (se 1 (by rfl) ⟨2513087, by rfl⟩ : syracuseStep 3350783 = 5026175) B5026175
theorem B2233855 : Blo 2233435 2233855 := bstep (se 1 (by rfl) ⟨1675391, by rfl⟩ : syracuseStep 2233855 = 3350783) B3350783
theorem B3350789 : Blo 2233435 3350789 := bbase (se 4 (by rfl) ⟨314136, by rfl⟩ : syracuseStep 3350789 = 628273) (by norm_num)
theorem B2233859 : Blo 2233435 2233859 := bstep (se 1 (by rfl) ⟨1675394, by rfl⟩ : syracuseStep 2233859 = 3350789) B3350789
theorem B3769645 : Blo 2233435 3769645 := bbase (se 3 (by rfl) ⟨706808, by rfl⟩ : syracuseStep 3769645 = 1413617) (by norm_num)
theorem B5026193 : Blo 2233435 5026193 := bstep (se 2 (by rfl) ⟨1884822, by rfl⟩ : syracuseStep 5026193 = 3769645) B3769645
theorem B3350795 : Blo 2233435 3350795 := bstep (se 1 (by rfl) ⟨2513096, by rfl⟩ : syracuseStep 3350795 = 5026193) B5026193
theorem B2233863 : Blo 2233435 2233863 := bstep (se 1 (by rfl) ⟨1675397, by rfl⟩ : syracuseStep 2233863 = 3350795) B3350795
theorem B2513101 : Blo 2233435 2513101 := bbase (se 3 (by rfl) ⟨471206, by rfl⟩ : syracuseStep 2513101 = 942413) (by norm_num)
theorem B3350801 : Blo 2233435 3350801 := bstep (se 2 (by rfl) ⟨1256550, by rfl⟩ : syracuseStep 3350801 = 2513101) B2513101
theorem B2233867 : Blo 2233435 2233867 := bstep (se 1 (by rfl) ⟨1675400, by rfl⟩ : syracuseStep 2233867 = 3350801) B3350801
theorem B7539317 : Blo 2233435 7539317 := bbase (se 5 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 7539317 = 706811) (by norm_num)
theorem B5026211 : Blo 2233435 5026211 := bstep (se 1 (by rfl) ⟨3769658, by rfl⟩ : syracuseStep 5026211 = 7539317) B7539317
theorem B3350807 : Blo 2233435 3350807 := bstep (se 1 (by rfl) ⟨2513105, by rfl⟩ : syracuseStep 3350807 = 5026211) B5026211
theorem B2233871 : Blo 2233435 2233871 := bstep (se 1 (by rfl) ⟨1675403, by rfl⟩ : syracuseStep 2233871 = 3350807) B3350807
theorem B3350813 : Blo 2233435 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B2233875 : Blo 2233435 2233875 := bstep (se 1 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 2233875 = 3350813) B3350813
theorem B5026229 : Blo 2233435 5026229 := bbase (se 5 (by rfl) ⟨235604, by rfl⟩ : syracuseStep 5026229 = 471209) (by norm_num)
theorem B3350819 : Blo 2233435 3350819 := bstep (se 1 (by rfl) ⟨2513114, by rfl⟩ : syracuseStep 3350819 = 5026229) B5026229
theorem B2233879 : Blo 2233435 2233879 := bstep (se 1 (by rfl) ⟨1675409, by rfl⟩ : syracuseStep 2233879 = 3350819) B3350819
theorem B4025533 : Blo 2233435 4025533 := bbase (se 3 (by rfl) ⟨754787, by rfl⟩ : syracuseStep 4025533 = 1509575) (by norm_num)
theorem B5367377 : Blo 2233435 5367377 := bstep (se 2 (by rfl) ⟨2012766, by rfl⟩ : syracuseStep 5367377 = 4025533) B4025533
theorem B3578251 : Blo 2233435 3578251 := bstep (se 1 (by rfl) ⟨2683688, by rfl⟩ : syracuseStep 3578251 = 5367377) B5367377
theorem B4771001 : Blo 2233435 4771001 := bstep (se 2 (by rfl) ⟨1789125, by rfl⟩ : syracuseStep 4771001 = 3578251) B3578251
theorem B12722669 : Blo 2233435 12722669 := bstep (se 3 (by rfl) ⟨2385500, by rfl⟩ : syracuseStep 12722669 = 4771001) B4771001
theorem B8481779 : Blo 2233435 8481779 := bstep (se 1 (by rfl) ⟨6361334, by rfl⟩ : syracuseStep 8481779 = 12722669) B12722669
theorem B5654519 : Blo 2233435 5654519 := bstep (se 1 (by rfl) ⟨4240889, by rfl⟩ : syracuseStep 5654519 = 8481779) B8481779
theorem B3769679 : Blo 2233435 3769679 := bstep (se 1 (by rfl) ⟨2827259, by rfl⟩ : syracuseStep 3769679 = 5654519) B5654519
theorem B2513119 : Blo 2233435 2513119 := bstep (se 1 (by rfl) ⟨1884839, by rfl⟩ : syracuseStep 2513119 = 3769679) B3769679
theorem B3350825 : Blo 2233435 3350825 := bstep (se 2 (by rfl) ⟨1256559, by rfl⟩ : syracuseStep 3350825 = 2513119) B2513119
theorem B2233883 : Blo 2233435 2233883 := bstep (se 1 (by rfl) ⟨1675412, by rfl⟩ : syracuseStep 2233883 = 3350825) B3350825
theorem B2683693 : Blo 2233435 2683693 := bbase (se 3 (by rfl) ⟨503192, by rfl⟩ : syracuseStep 2683693 = 1006385) (by norm_num)
theorem B3578257 : Blo 2233435 3578257 := bstep (se 2 (by rfl) ⟨1341846, by rfl⟩ : syracuseStep 3578257 = 2683693) B2683693
theorem B4771009 : Blo 2233435 4771009 := bstep (se 2 (by rfl) ⟨1789128, by rfl⟩ : syracuseStep 4771009 = 3578257) B3578257
theorem B6361345 : Blo 2233435 6361345 := bstep (se 2 (by rfl) ⟨2385504, by rfl⟩ : syracuseStep 6361345 = 4771009) B4771009
theorem B8481793 : Blo 2233435 8481793 := bstep (se 2 (by rfl) ⟨3180672, by rfl⟩ : syracuseStep 8481793 = 6361345) B6361345
theorem B11309057 : Blo 2233435 11309057 := bstep (se 2 (by rfl) ⟨4240896, by rfl⟩ : syracuseStep 11309057 = 8481793) B8481793
theorem B7539371 : Blo 2233435 7539371 := bstep (se 1 (by rfl) ⟨5654528, by rfl⟩ : syracuseStep 7539371 = 11309057) B11309057
theorem B5026247 : Blo 2233435 5026247 := bstep (se 1 (by rfl) ⟨3769685, by rfl⟩ : syracuseStep 5026247 = 7539371) B7539371
theorem B3350831 : Blo 2233435 3350831 := bstep (se 1 (by rfl) ⟨2513123, by rfl⟩ : syracuseStep 3350831 = 5026247) B5026247
theorem B2233887 : Blo 2233435 2233887 := bstep (se 1 (by rfl) ⟨1675415, by rfl⟩ : syracuseStep 2233887 = 3350831) B3350831
theorem B3350837 : Blo 2233435 3350837 := bbase (se 5 (by rfl) ⟨157070, by rfl⟩ : syracuseStep 3350837 = 314141) (by norm_num)
theorem B2233891 : Blo 2233435 2233891 := bstep (se 1 (by rfl) ⟨1675418, by rfl⟩ : syracuseStep 2233891 = 3350837) B3350837
theorem B5654549 : Blo 2233435 5654549 := bbase (se 6 (by rfl) ⟨132528, by rfl⟩ : syracuseStep 5654549 = 265057) (by norm_num)
theorem B3769699 : Blo 2233435 3769699 := bstep (se 1 (by rfl) ⟨2827274, by rfl⟩ : syracuseStep 3769699 = 5654549) B5654549
theorem B5026265 : Blo 2233435 5026265 := bstep (se 2 (by rfl) ⟨1884849, by rfl⟩ : syracuseStep 5026265 = 3769699) B3769699
theorem B3350843 : Blo 2233435 3350843 := bstep (se 1 (by rfl) ⟨2513132, by rfl⟩ : syracuseStep 3350843 = 5026265) B5026265
theorem B2233895 : Blo 2233435 2233895 := bstep (se 1 (by rfl) ⟨1675421, by rfl⟩ : syracuseStep 2233895 = 3350843) B3350843
theorem B2513137 : Blo 2233435 2513137 := bbase (se 2 (by rfl) ⟨942426, by rfl⟩ : syracuseStep 2513137 = 1884853) (by norm_num)
theorem B3350849 : Blo 2233435 3350849 := bstep (se 2 (by rfl) ⟨1256568, by rfl⟩ : syracuseStep 3350849 = 2513137) B2513137
theorem B2233899 : Blo 2233435 2233899 := bstep (se 1 (by rfl) ⟨1675424, by rfl⟩ : syracuseStep 2233899 = 3350849) B3350849
theorem B4298789 : Blo 2233435 4298789 := bbase (se 4 (by rfl) ⟨403011, by rfl⟩ : syracuseStep 4298789 = 806023) (by norm_num)
theorem B11463437 : Blo 2233435 11463437 := bstep (se 3 (by rfl) ⟨2149394, by rfl⟩ : syracuseStep 11463437 = 4298789) B4298789
theorem B7642291 : Blo 2233435 7642291 := bstep (se 1 (by rfl) ⟨5731718, by rfl⟩ : syracuseStep 7642291 = 11463437) B11463437
theorem B10189721 : Blo 2233435 10189721 := bstep (se 2 (by rfl) ⟨3821145, by rfl⟩ : syracuseStep 10189721 = 7642291) B7642291
theorem B6793147 : Blo 2233435 6793147 := bstep (se 1 (by rfl) ⟨5094860, by rfl⟩ : syracuseStep 6793147 = 10189721) B10189721
theorem B9057529 : Blo 2233435 9057529 := bstep (se 2 (by rfl) ⟨3396573, by rfl⟩ : syracuseStep 9057529 = 6793147) B6793147
theorem B12076705 : Blo 2233435 12076705 := bstep (se 2 (by rfl) ⟨4528764, by rfl⟩ : syracuseStep 12076705 = 9057529) B9057529
theorem B16102273 : Blo 2233435 16102273 := bstep (se 2 (by rfl) ⟨6038352, by rfl⟩ : syracuseStep 16102273 = 12076705) B12076705
theorem B21469697 : Blo 2233435 21469697 := bstep (se 2 (by rfl) ⟨8051136, by rfl⟩ : syracuseStep 21469697 = 16102273) B16102273
theorem B14313131 : Blo 2233435 14313131 := bstep (se 1 (by rfl) ⟨10734848, by rfl⟩ : syracuseStep 14313131 = 21469697) B21469697
theorem B9542087 : Blo 2233435 9542087 := bstep (se 1 (by rfl) ⟨7156565, by rfl⟩ : syracuseStep 9542087 = 14313131) B14313131
theorem B6361391 : Blo 2233435 6361391 := bstep (se 1 (by rfl) ⟨4771043, by rfl⟩ : syracuseStep 6361391 = 9542087) B9542087
theorem B4240927 : Blo 2233435 4240927 := bstep (se 1 (by rfl) ⟨3180695, by rfl⟩ : syracuseStep 4240927 = 6361391) B6361391
theorem B5654569 : Blo 2233435 5654569 := bstep (se 2 (by rfl) ⟨2120463, by rfl⟩ : syracuseStep 5654569 = 4240927) B4240927
theorem B7539425 : Blo 2233435 7539425 := bstep (se 2 (by rfl) ⟨2827284, by rfl⟩ : syracuseStep 7539425 = 5654569) B5654569
theorem B5026283 : Blo 2233435 5026283 := bstep (se 1 (by rfl) ⟨3769712, by rfl⟩ : syracuseStep 5026283 = 7539425) B7539425
theorem B3350855 : Blo 2233435 3350855 := bstep (se 1 (by rfl) ⟨2513141, by rfl⟩ : syracuseStep 3350855 = 5026283) B5026283
theorem B2233903 : Blo 2233435 2233903 := bstep (se 1 (by rfl) ⟨1675427, by rfl⟩ : syracuseStep 2233903 = 3350855) B3350855
theorem B3350861 : Blo 2233435 3350861 := bbase (se 3 (by rfl) ⟨628286, by rfl⟩ : syracuseStep 3350861 = 1256573) (by norm_num)
theorem B2233907 : Blo 2233435 2233907 := bstep (se 1 (by rfl) ⟨1675430, by rfl⟩ : syracuseStep 2233907 = 3350861) B3350861
theorem B5026301 : Blo 2233435 5026301 := bbase (se 3 (by rfl) ⟨942431, by rfl⟩ : syracuseStep 5026301 = 1884863) (by norm_num)
theorem B3350867 : Blo 2233435 3350867 := bstep (se 1 (by rfl) ⟨2513150, by rfl⟩ : syracuseStep 3350867 = 5026301) B5026301
theorem B2233911 : Blo 2233435 2233911 := bstep (se 1 (by rfl) ⟨1675433, by rfl⟩ : syracuseStep 2233911 = 3350867) B3350867
theorem B3769733 : Blo 2233435 3769733 := bbase (se 4 (by rfl) ⟨353412, by rfl⟩ : syracuseStep 3769733 = 706825) (by norm_num)
theorem B2513155 : Blo 2233435 2513155 := bstep (se 1 (by rfl) ⟨1884866, by rfl⟩ : syracuseStep 2513155 = 3769733) B3769733
theorem B3350873 : Blo 2233435 3350873 := bstep (se 2 (by rfl) ⟨1256577, by rfl⟩ : syracuseStep 3350873 = 2513155) B2513155
theorem B2233915 : Blo 2233435 2233915 := bstep (se 1 (by rfl) ⟨1675436, by rfl⟩ : syracuseStep 2233915 = 3350873) B3350873
theorem B16963829 : Blo 2233435 16963829 := bbase (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) (by norm_num)
theorem B11309219 : Blo 2233435 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B7539479 : Blo 2233435 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B5026319 : Blo 2233435 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B3350879 : Blo 2233435 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B2233919 : Blo 2233435 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B3350885 : Blo 2233435 3350885 := bbase (se 4 (by rfl) ⟨314145, by rfl⟩ : syracuseStep 3350885 = 628291) (by norm_num)
theorem B2233923 : Blo 2233435 2233923 := bstep (se 1 (by rfl) ⟨1675442, by rfl⟩ : syracuseStep 2233923 = 3350885) B3350885
theorem B4240973 : Blo 2233435 4240973 := bbase (se 3 (by rfl) ⟨795182, by rfl⟩ : syracuseStep 4240973 = 1590365) (by norm_num)
theorem B2827315 : Blo 2233435 2827315 := bstep (se 1 (by rfl) ⟨2120486, by rfl⟩ : syracuseStep 2827315 = 4240973) B4240973
theorem B3769753 : Blo 2233435 3769753 := bstep (se 2 (by rfl) ⟨1413657, by rfl⟩ : syracuseStep 3769753 = 2827315) B2827315
theorem B5026337 : Blo 2233435 5026337 := bstep (se 2 (by rfl) ⟨1884876, by rfl⟩ : syracuseStep 5026337 = 3769753) B3769753
theorem B3350891 : Blo 2233435 3350891 := bstep (se 1 (by rfl) ⟨2513168, by rfl⟩ : syracuseStep 3350891 = 5026337) B5026337
theorem B2233927 : Blo 2233435 2233927 := bstep (se 1 (by rfl) ⟨1675445, by rfl⟩ : syracuseStep 2233927 = 3350891) B3350891
theorem B2513173 : Blo 2233435 2513173 := bbase (se 6 (by rfl) ⟨58902, by rfl⟩ : syracuseStep 2513173 = 117805) (by norm_num)
theorem B3350897 : Blo 2233435 3350897 := bstep (se 2 (by rfl) ⟨1256586, by rfl⟩ : syracuseStep 3350897 = 2513173) B2513173
theorem B2233931 : Blo 2233435 2233931 := bstep (se 1 (by rfl) ⟨1675448, by rfl⟩ : syracuseStep 2233931 = 3350897) B3350897
theorem B2827325 : Blo 2233435 2827325 := bbase (se 3 (by rfl) ⟨530123, by rfl⟩ : syracuseStep 2827325 = 1060247) (by norm_num)
theorem B7539533 : Blo 2233435 7539533 := bstep (se 3 (by rfl) ⟨1413662, by rfl⟩ : syracuseStep 7539533 = 2827325) B2827325
theorem B5026355 : Blo 2233435 5026355 := bstep (se 1 (by rfl) ⟨3769766, by rfl⟩ : syracuseStep 5026355 = 7539533) B7539533
theorem B3350903 : Blo 2233435 3350903 := bstep (se 1 (by rfl) ⟨2513177, by rfl⟩ : syracuseStep 3350903 = 5026355) B5026355
theorem B2233935 : Blo 2233435 2233935 := bstep (se 1 (by rfl) ⟨1675451, by rfl⟩ : syracuseStep 2233935 = 3350903) B3350903
theorem B3350909 : Blo 2233435 3350909 := bbase (se 3 (by rfl) ⟨628295, by rfl⟩ : syracuseStep 3350909 = 1256591) (by norm_num)
theorem B2233939 : Blo 2233435 2233939 := bstep (se 1 (by rfl) ⟨1675454, by rfl⟩ : syracuseStep 2233939 = 3350909) B3350909
theorem B5026373 : Blo 2233435 5026373 := bbase (se 4 (by rfl) ⟨471222, by rfl⟩ : syracuseStep 5026373 = 942445) (by norm_num)
theorem B3350915 : Blo 2233435 3350915 := bstep (se 1 (by rfl) ⟨2513186, by rfl⟩ : syracuseStep 3350915 = 5026373) B5026373
theorem B2233943 : Blo 2233435 2233943 := bstep (se 1 (by rfl) ⟨1675457, by rfl⟩ : syracuseStep 2233943 = 3350915) B3350915
theorem B2385569 : Blo 2233435 2385569 := bbase (se 2 (by rfl) ⟨894588, by rfl⟩ : syracuseStep 2385569 = 1789177) (by norm_num)
theorem B6361517 : Blo 2233435 6361517 := bstep (se 3 (by rfl) ⟨1192784, by rfl⟩ : syracuseStep 6361517 = 2385569) B2385569
theorem B4241011 : Blo 2233435 4241011 := bstep (se 1 (by rfl) ⟨3180758, by rfl⟩ : syracuseStep 4241011 = 6361517) B6361517
theorem B5654681 : Blo 2233435 5654681 := bstep (se 2 (by rfl) ⟨2120505, by rfl⟩ : syracuseStep 5654681 = 4241011) B4241011
theorem B3769787 : Blo 2233435 3769787 := bstep (se 1 (by rfl) ⟨2827340, by rfl⟩ : syracuseStep 3769787 = 5654681) B5654681
theorem B2513191 : Blo 2233435 2513191 := bstep (se 1 (by rfl) ⟨1884893, by rfl⟩ : syracuseStep 2513191 = 3769787) B3769787
theorem B3350921 : Blo 2233435 3350921 := bstep (se 2 (by rfl) ⟨1256595, by rfl⟩ : syracuseStep 3350921 = 2513191) B2513191
theorem B2233947 : Blo 2233435 2233947 := bstep (se 1 (by rfl) ⟨1675460, by rfl⟩ : syracuseStep 2233947 = 3350921) B3350921
theorem B11309381 : Blo 2233435 11309381 := bbase (se 4 (by rfl) ⟨1060254, by rfl⟩ : syracuseStep 11309381 = 2120509) (by norm_num)
theorem B7539587 : Blo 2233435 7539587 := bstep (se 1 (by rfl) ⟨5654690, by rfl⟩ : syracuseStep 7539587 = 11309381) B11309381
theorem B5026391 : Blo 2233435 5026391 := bstep (se 1 (by rfl) ⟨3769793, by rfl⟩ : syracuseStep 5026391 = 7539587) B7539587
theorem B3350927 : Blo 2233435 3350927 := bstep (se 1 (by rfl) ⟨2513195, by rfl⟩ : syracuseStep 3350927 = 5026391) B5026391
theorem B2233951 : Blo 2233435 2233951 := bstep (se 1 (by rfl) ⟨1675463, by rfl⟩ : syracuseStep 2233951 = 3350927) B3350927
theorem B3350933 : Blo 2233435 3350933 := bbase (se 6 (by rfl) ⟨78537, by rfl⟩ : syracuseStep 3350933 = 157075) (by norm_num)
theorem B2233955 : Blo 2233435 2233955 := bstep (se 1 (by rfl) ⟨1675466, by rfl⟩ : syracuseStep 2233955 = 3350933) B3350933
theorem B5094989 : Blo 2233435 5094989 := bbase (se 3 (by rfl) ⟨955310, by rfl⟩ : syracuseStep 5094989 = 1910621) (by norm_num)
theorem B3396659 : Blo 2233435 3396659 := bstep (se 1 (by rfl) ⟨2547494, by rfl⟩ : syracuseStep 3396659 = 5094989) B5094989
theorem B9057757 : Blo 2233435 9057757 := bstep (se 3 (by rfl) ⟨1698329, by rfl⟩ : syracuseStep 9057757 = 3396659) B3396659
theorem B12077009 : Blo 2233435 12077009 := bstep (se 2 (by rfl) ⟨4528878, by rfl⟩ : syracuseStep 12077009 = 9057757) B9057757
theorem B8051339 : Blo 2233435 8051339 := bstep (se 1 (by rfl) ⟨6038504, by rfl⟩ : syracuseStep 8051339 = 12077009) B12077009
theorem B5367559 : Blo 2233435 5367559 := bstep (se 1 (by rfl) ⟨4025669, by rfl⟩ : syracuseStep 5367559 = 8051339) B8051339
theorem B7156745 : Blo 2233435 7156745 := bstep (se 2 (by rfl) ⟨2683779, by rfl⟩ : syracuseStep 7156745 = 5367559) B5367559
theorem B4771163 : Blo 2233435 4771163 := bstep (se 1 (by rfl) ⟨3578372, by rfl⟩ : syracuseStep 4771163 = 7156745) B7156745
theorem B12723101 : Blo 2233435 12723101 := bstep (se 3 (by rfl) ⟨2385581, by rfl⟩ : syracuseStep 12723101 = 4771163) B4771163
theorem B8482067 : Blo 2233435 8482067 := bstep (se 1 (by rfl) ⟨6361550, by rfl⟩ : syracuseStep 8482067 = 12723101) B12723101
theorem B5654711 : Blo 2233435 5654711 := bstep (se 1 (by rfl) ⟨4241033, by rfl⟩ : syracuseStep 5654711 = 8482067) B8482067
theorem B3769807 : Blo 2233435 3769807 := bstep (se 1 (by rfl) ⟨2827355, by rfl⟩ : syracuseStep 3769807 = 5654711) B5654711
theorem B5026409 : Blo 2233435 5026409 := bstep (se 2 (by rfl) ⟨1884903, by rfl⟩ : syracuseStep 5026409 = 3769807) B3769807
theorem B3350939 : Blo 2233435 3350939 := bstep (se 1 (by rfl) ⟨2513204, by rfl⟩ : syracuseStep 3350939 = 5026409) B5026409
theorem B2233959 : Blo 2233435 2233959 := bstep (se 1 (by rfl) ⟨1675469, by rfl⟩ : syracuseStep 2233959 = 3350939) B3350939
theorem B2513209 : Blo 2233435 2513209 := bbase (se 2 (by rfl) ⟨942453, by rfl⟩ : syracuseStep 2513209 = 1884907) (by norm_num)
theorem B3350945 : Blo 2233435 3350945 := bstep (se 2 (by rfl) ⟨1256604, by rfl⟩ : syracuseStep 3350945 = 2513209) B2513209
theorem B2233963 : Blo 2233435 2233963 := bstep (se 1 (by rfl) ⟨1675472, by rfl⟩ : syracuseStep 2233963 = 3350945) B3350945
theorem B6361573 : Blo 2233435 6361573 := bbase (se 4 (by rfl) ⟨596397, by rfl⟩ : syracuseStep 6361573 = 1192795) (by norm_num)
theorem B8482097 : Blo 2233435 8482097 := bstep (se 2 (by rfl) ⟨3180786, by rfl⟩ : syracuseStep 8482097 = 6361573) B6361573
theorem B5654731 : Blo 2233435 5654731 := bstep (se 1 (by rfl) ⟨4241048, by rfl⟩ : syracuseStep 5654731 = 8482097) B8482097
theorem B7539641 : Blo 2233435 7539641 := bstep (se 2 (by rfl) ⟨2827365, by rfl⟩ : syracuseStep 7539641 = 5654731) B5654731
theorem B5026427 : Blo 2233435 5026427 := bstep (se 1 (by rfl) ⟨3769820, by rfl⟩ : syracuseStep 5026427 = 7539641) B7539641
theorem B3350951 : Blo 2233435 3350951 := bstep (se 1 (by rfl) ⟨2513213, by rfl⟩ : syracuseStep 3350951 = 5026427) B5026427
theorem B2233967 : Blo 2233435 2233967 := bstep (se 1 (by rfl) ⟨1675475, by rfl⟩ : syracuseStep 2233967 = 3350951) B3350951
theorem B3350957 : Blo 2233435 3350957 := bbase (se 3 (by rfl) ⟨628304, by rfl⟩ : syracuseStep 3350957 = 1256609) (by norm_num)
theorem B2233971 : Blo 2233435 2233971 := bstep (se 1 (by rfl) ⟨1675478, by rfl⟩ : syracuseStep 2233971 = 3350957) B3350957
theorem B5026445 : Blo 2233435 5026445 := bbase (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) (by norm_num)
theorem B3350963 : Blo 2233435 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B2233975 : Blo 2233435 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B2827381 : Blo 2233435 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B3769841 : Blo 2233435 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B2513227 : Blo 2233435 2513227 := bstep (se 1 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 2513227 = 3769841) B3769841
theorem B3350969 : Blo 2233435 3350969 := bstep (se 2 (by rfl) ⟨1256613, by rfl⟩ : syracuseStep 3350969 = 2513227) B2513227
theorem B2233979 : Blo 2233435 2233979 := bstep (se 1 (by rfl) ⟨1675484, by rfl⟩ : syracuseStep 2233979 = 3350969) B3350969
theorem B4902293 : Blo 2233435 4902293 := bbase (se 6 (by rfl) ⟨114897, by rfl⟩ : syracuseStep 4902293 = 229795) (by norm_num)
theorem B3268195 : Blo 2233435 3268195 := bstep (se 1 (by rfl) ⟨2451146, by rfl⟩ : syracuseStep 3268195 = 4902293) B4902293
theorem B17430373 : Blo 2233435 17430373 := bstep (se 4 (by rfl) ⟨1634097, by rfl⟩ : syracuseStep 17430373 = 3268195) B3268195
theorem B92961989 : Blo 2233435 92961989 := bstep (se 4 (by rfl) ⟨8715186, by rfl⟩ : syracuseStep 92961989 = 17430373) B17430373
theorem B61974659 : Blo 2233435 61974659 := bstep (se 1 (by rfl) ⟨46480994, by rfl⟩ : syracuseStep 61974659 = 92961989) B92961989
theorem B165265757 : Blo 2233435 165265757 := bstep (se 3 (by rfl) ⟨30987329, by rfl⟩ : syracuseStep 165265757 = 61974659) B61974659
theorem B110177171 : Blo 2233435 110177171 := bstep (se 1 (by rfl) ⟨82632878, by rfl⟩ : syracuseStep 110177171 = 165265757) B165265757
theorem B73451447 : Blo 2233435 73451447 := bstep (se 1 (by rfl) ⟨55088585, by rfl⟩ : syracuseStep 73451447 = 110177171) B110177171
theorem B48967631 : Blo 2233435 48967631 := bstep (se 1 (by rfl) ⟨36725723, by rfl⟩ : syracuseStep 48967631 = 73451447) B73451447
theorem B32645087 : Blo 2233435 32645087 := bstep (se 1 (by rfl) ⟨24483815, by rfl⟩ : syracuseStep 32645087 = 48967631) B48967631
theorem B348214261 : Blo 2233435 348214261 := bstep (se 5 (by rfl) ⟨16322543, by rfl⟩ : syracuseStep 348214261 = 32645087) B32645087
theorem B464285681 : Blo 2233435 464285681 := bstep (se 2 (by rfl) ⟨174107130, by rfl⟩ : syracuseStep 464285681 = 348214261) B348214261
theorem B309523787 : Blo 2233435 309523787 := bstep (se 1 (by rfl) ⟨232142840, by rfl⟩ : syracuseStep 309523787 = 464285681) B464285681
theorem B206349191 : Blo 2233435 206349191 := bstep (se 1 (by rfl) ⟨154761893, by rfl⟩ : syracuseStep 206349191 = 309523787) B309523787
theorem B137566127 : Blo 2233435 137566127 := bstep (se 1 (by rfl) ⟨103174595, by rfl⟩ : syracuseStep 137566127 = 206349191) B206349191
theorem B91710751 : Blo 2233435 91710751 := bstep (se 1 (by rfl) ⟨68783063, by rfl⟩ : syracuseStep 91710751 = 137566127) B137566127
theorem B122281001 : Blo 2233435 122281001 := bstep (se 2 (by rfl) ⟨45855375, by rfl⟩ : syracuseStep 122281001 = 91710751) B91710751
theorem B81520667 : Blo 2233435 81520667 := bstep (se 1 (by rfl) ⟨61140500, by rfl⟩ : syracuseStep 81520667 = 122281001) B122281001
theorem B54347111 : Blo 2233435 54347111 := bstep (se 1 (by rfl) ⟨40760333, by rfl⟩ : syracuseStep 54347111 = 81520667) B81520667
theorem B36231407 : Blo 2233435 36231407 := bstep (se 1 (by rfl) ⟨27173555, by rfl⟩ : syracuseStep 36231407 = 54347111) B54347111
theorem B24154271 : Blo 2233435 24154271 := bstep (se 1 (by rfl) ⟨18115703, by rfl⟩ : syracuseStep 24154271 = 36231407) B36231407
theorem B16102847 : Blo 2233435 16102847 := bstep (se 1 (by rfl) ⟨12077135, by rfl⟩ : syracuseStep 16102847 = 24154271) B24154271
theorem B42940925 : Blo 2233435 42940925 := bstep (se 3 (by rfl) ⟨8051423, by rfl⟩ : syracuseStep 42940925 = 16102847) B16102847
theorem B28627283 : Blo 2233435 28627283 := bstep (se 1 (by rfl) ⟨21470462, by rfl⟩ : syracuseStep 28627283 = 42940925) B42940925
theorem B19084855 : Blo 2233435 19084855 := bstep (se 1 (by rfl) ⟨14313641, by rfl⟩ : syracuseStep 19084855 = 28627283) B28627283
theorem B25446473 : Blo 2233435 25446473 := bstep (se 2 (by rfl) ⟨9542427, by rfl⟩ : syracuseStep 25446473 = 19084855) B19084855
theorem B16964315 : Blo 2233435 16964315 := bstep (se 1 (by rfl) ⟨12723236, by rfl⟩ : syracuseStep 16964315 = 25446473) B25446473
theorem B11309543 : Blo 2233435 11309543 := bstep (se 1 (by rfl) ⟨8482157, by rfl⟩ : syracuseStep 11309543 = 16964315) B16964315
theorem B7539695 : Blo 2233435 7539695 := bstep (se 1 (by rfl) ⟨5654771, by rfl⟩ : syracuseStep 7539695 = 11309543) B11309543
theorem B5026463 : Blo 2233435 5026463 := bstep (se 1 (by rfl) ⟨3769847, by rfl⟩ : syracuseStep 5026463 = 7539695) B7539695
theorem B3350975 : Blo 2233435 3350975 := bstep (se 1 (by rfl) ⟨2513231, by rfl⟩ : syracuseStep 3350975 = 5026463) B5026463
theorem B2233983 : Blo 2233435 2233983 := bstep (se 1 (by rfl) ⟨1675487, by rfl⟩ : syracuseStep 2233983 = 3350975) B3350975
theorem B3350981 : Blo 2233435 3350981 := bbase (se 4 (by rfl) ⟨314154, by rfl⟩ : syracuseStep 3350981 = 628309) (by norm_num)
theorem B2233987 : Blo 2233435 2233987 := bstep (se 1 (by rfl) ⟨1675490, by rfl⟩ : syracuseStep 2233987 = 3350981) B3350981
theorem B3769861 : Blo 2233435 3769861 := bbase (se 4 (by rfl) ⟨353424, by rfl⟩ : syracuseStep 3769861 = 706849) (by norm_num)
theorem B5026481 : Blo 2233435 5026481 := bstep (se 2 (by rfl) ⟨1884930, by rfl⟩ : syracuseStep 5026481 = 3769861) B3769861
theorem B3350987 : Blo 2233435 3350987 := bstep (se 1 (by rfl) ⟨2513240, by rfl⟩ : syracuseStep 3350987 = 5026481) B5026481
theorem B2233991 : Blo 2233435 2233991 := bstep (se 1 (by rfl) ⟨1675493, by rfl⟩ : syracuseStep 2233991 = 3350987) B3350987
theorem B2513245 : Blo 2233435 2513245 := bbase (se 3 (by rfl) ⟨471233, by rfl⟩ : syracuseStep 2513245 = 942467) (by norm_num)
theorem B3350993 : Blo 2233435 3350993 := bstep (se 2 (by rfl) ⟨1256622, by rfl⟩ : syracuseStep 3350993 = 2513245) B2513245
theorem B2233995 : Blo 2233435 2233995 := bstep (se 1 (by rfl) ⟨1675496, by rfl⟩ : syracuseStep 2233995 = 3350993) B3350993
theorem B7539749 : Blo 2233435 7539749 := bbase (se 4 (by rfl) ⟨706851, by rfl⟩ : syracuseStep 7539749 = 1413703) (by norm_num)
theorem B5026499 : Blo 2233435 5026499 := bstep (se 1 (by rfl) ⟨3769874, by rfl⟩ : syracuseStep 5026499 = 7539749) B7539749
theorem B3350999 : Blo 2233435 3350999 := bstep (se 1 (by rfl) ⟨2513249, by rfl⟩ : syracuseStep 3350999 = 5026499) B5026499
theorem B2233999 : Blo 2233435 2233999 := bstep (se 1 (by rfl) ⟨1675499, by rfl⟩ : syracuseStep 2233999 = 3350999) B3350999
theorem B3351005 : Blo 2233435 3351005 := bbase (se 3 (by rfl) ⟨628313, by rfl⟩ : syracuseStep 3351005 = 1256627) (by norm_num)
theorem B2234003 : Blo 2233435 2234003 := bstep (se 1 (by rfl) ⟨1675502, by rfl⟩ : syracuseStep 2234003 = 3351005) B3351005
theorem B5026517 : Blo 2233435 5026517 := bbase (se 7 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 5026517 = 117809) (by norm_num)
theorem B3351011 : Blo 2233435 3351011 := bstep (se 1 (by rfl) ⟨2513258, by rfl⟩ : syracuseStep 3351011 = 5026517) B5026517
theorem B2234007 : Blo 2233435 2234007 := bstep (se 1 (by rfl) ⟨1675505, by rfl⟩ : syracuseStep 2234007 = 3351011) B3351011
theorem B9542549 : Blo 2233435 9542549 := bbase (se 6 (by rfl) ⟨223653, by rfl⟩ : syracuseStep 9542549 = 447307) (by norm_num)
theorem B6361699 : Blo 2233435 6361699 := bstep (se 1 (by rfl) ⟨4771274, by rfl⟩ : syracuseStep 6361699 = 9542549) B9542549
theorem B8482265 : Blo 2233435 8482265 := bstep (se 2 (by rfl) ⟨3180849, by rfl⟩ : syracuseStep 8482265 = 6361699) B6361699
theorem B5654843 : Blo 2233435 5654843 := bstep (se 1 (by rfl) ⟨4241132, by rfl⟩ : syracuseStep 5654843 = 8482265) B8482265
theorem B3769895 : Blo 2233435 3769895 := bstep (se 1 (by rfl) ⟨2827421, by rfl⟩ : syracuseStep 3769895 = 5654843) B5654843
theorem B2513263 : Blo 2233435 2513263 := bstep (se 1 (by rfl) ⟨1884947, by rfl⟩ : syracuseStep 2513263 = 3769895) B3769895
theorem B3351017 : Blo 2233435 3351017 := bstep (se 2 (by rfl) ⟨1256631, by rfl⟩ : syracuseStep 3351017 = 2513263) B2513263
theorem B2234011 : Blo 2233435 2234011 := bstep (se 1 (by rfl) ⟨1675508, by rfl⟩ : syracuseStep 2234011 = 3351017) B3351017
theorem B22928021 : Blo 2233435 22928021 := bbase (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) (by norm_num)
theorem B15285347 : Blo 2233435 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B10190231 : Blo 2233435 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B6793487 : Blo 2233435 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B4528991 : Blo 2233435 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B12077309 : Blo 2233435 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B32206157 : Blo 2233435 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B21470771 : Blo 2233435 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B14313847 : Blo 2233435 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B19085129 : Blo 2233435 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B12723419 : Blo 2233435 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B8482279 : Blo 2233435 8482279 := bstep (se 1 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 8482279 = 12723419) B12723419
theorem B11309705 : Blo 2233435 11309705 := bstep (se 2 (by rfl) ⟨4241139, by rfl⟩ : syracuseStep 11309705 = 8482279) B8482279
theorem B7539803 : Blo 2233435 7539803 := bstep (se 1 (by rfl) ⟨5654852, by rfl⟩ : syracuseStep 7539803 = 11309705) B11309705
theorem B5026535 : Blo 2233435 5026535 := bstep (se 1 (by rfl) ⟨3769901, by rfl⟩ : syracuseStep 5026535 = 7539803) B7539803
theorem B3351023 : Blo 2233435 3351023 := bstep (se 1 (by rfl) ⟨2513267, by rfl⟩ : syracuseStep 3351023 = 5026535) B5026535
theorem B2234015 : Blo 2233435 2234015 := bstep (se 1 (by rfl) ⟨1675511, by rfl⟩ : syracuseStep 2234015 = 3351023) B3351023
theorem B3351029 : Blo 2233435 3351029 := bbase (se 5 (by rfl) ⟨157079, by rfl⟩ : syracuseStep 3351029 = 314159) (by norm_num)
theorem B2234019 : Blo 2233435 2234019 := bstep (se 1 (by rfl) ⟨1675514, by rfl⟩ : syracuseStep 2234019 = 3351029) B3351029
theorem B6361733 : Blo 2233435 6361733 := bbase (se 4 (by rfl) ⟨596412, by rfl⟩ : syracuseStep 6361733 = 1192825) (by norm_num)
theorem B4241155 : Blo 2233435 4241155 := bstep (se 1 (by rfl) ⟨3180866, by rfl⟩ : syracuseStep 4241155 = 6361733) B6361733
theorem B5654873 : Blo 2233435 5654873 := bstep (se 2 (by rfl) ⟨2120577, by rfl⟩ : syracuseStep 5654873 = 4241155) B4241155
theorem B3769915 : Blo 2233435 3769915 := bstep (se 1 (by rfl) ⟨2827436, by rfl⟩ : syracuseStep 3769915 = 5654873) B5654873
theorem B5026553 : Blo 2233435 5026553 := bstep (se 2 (by rfl) ⟨1884957, by rfl⟩ : syracuseStep 5026553 = 3769915) B3769915
theorem B3351035 : Blo 2233435 3351035 := bstep (se 1 (by rfl) ⟨2513276, by rfl⟩ : syracuseStep 3351035 = 5026553) B5026553
theorem B2234023 : Blo 2233435 2234023 := bstep (se 1 (by rfl) ⟨1675517, by rfl⟩ : syracuseStep 2234023 = 3351035) B3351035
theorem B2513281 : Blo 2233435 2513281 := bbase (se 2 (by rfl) ⟨942480, by rfl⟩ : syracuseStep 2513281 = 1884961) (by norm_num)
theorem B3351041 : Blo 2233435 3351041 := bstep (se 2 (by rfl) ⟨1256640, by rfl⟩ : syracuseStep 3351041 = 2513281) B2513281
theorem B2234027 : Blo 2233435 2234027 := bstep (se 1 (by rfl) ⟨1675520, by rfl⟩ : syracuseStep 2234027 = 3351041) B3351041
theorem B5654893 : Blo 2233435 5654893 := bbase (se 3 (by rfl) ⟨1060292, by rfl⟩ : syracuseStep 5654893 = 2120585) (by norm_num)
theorem B7539857 : Blo 2233435 7539857 := bstep (se 2 (by rfl) ⟨2827446, by rfl⟩ : syracuseStep 7539857 = 5654893) B5654893
theorem B5026571 : Blo 2233435 5026571 := bstep (se 1 (by rfl) ⟨3769928, by rfl⟩ : syracuseStep 5026571 = 7539857) B7539857
theorem B3351047 : Blo 2233435 3351047 := bstep (se 1 (by rfl) ⟨2513285, by rfl⟩ : syracuseStep 3351047 = 5026571) B5026571
theorem B2234031 : Blo 2233435 2234031 := bstep (se 1 (by rfl) ⟨1675523, by rfl⟩ : syracuseStep 2234031 = 3351047) B3351047
theorem B3351053 : Blo 2233435 3351053 := bbase (se 3 (by rfl) ⟨628322, by rfl⟩ : syracuseStep 3351053 = 1256645) (by norm_num)
theorem B2234035 : Blo 2233435 2234035 := bstep (se 1 (by rfl) ⟨1675526, by rfl⟩ : syracuseStep 2234035 = 3351053) B3351053
theorem B5026589 : Blo 2233435 5026589 := bbase (se 3 (by rfl) ⟨942485, by rfl⟩ : syracuseStep 5026589 = 1884971) (by norm_num)
theorem B3351059 : Blo 2233435 3351059 := bstep (se 1 (by rfl) ⟨2513294, by rfl⟩ : syracuseStep 3351059 = 5026589) B5026589
theorem B2234039 : Blo 2233435 2234039 := bstep (se 1 (by rfl) ⟨1675529, by rfl⟩ : syracuseStep 2234039 = 3351059) B3351059
theorem B3769949 : Blo 2233435 3769949 := bbase (se 3 (by rfl) ⟨706865, by rfl⟩ : syracuseStep 3769949 = 1413731) (by norm_num)
theorem B2513299 : Blo 2233435 2513299 := bstep (se 1 (by rfl) ⟨1884974, by rfl⟩ : syracuseStep 2513299 = 3769949) B3769949
theorem B3351065 : Blo 2233435 3351065 := bstep (se 2 (by rfl) ⟨1256649, by rfl⟩ : syracuseStep 3351065 = 2513299) B2513299
theorem B2234043 : Blo 2233435 2234043 := bstep (se 1 (by rfl) ⟨1675532, by rfl⟩ : syracuseStep 2234043 = 3351065) B3351065
theorem B2683885 : Blo 2233435 2683885 := bbase (se 3 (by rfl) ⟨503228, by rfl⟩ : syracuseStep 2683885 = 1006457) (by norm_num)
theorem B3578513 : Blo 2233435 3578513 := bstep (se 2 (by rfl) ⟨1341942, by rfl⟩ : syracuseStep 3578513 = 2683885) B2683885
theorem B9542701 : Blo 2233435 9542701 := bstep (se 3 (by rfl) ⟨1789256, by rfl⟩ : syracuseStep 9542701 = 3578513) B3578513
theorem B12723601 : Blo 2233435 12723601 := bstep (se 2 (by rfl) ⟨4771350, by rfl⟩ : syracuseStep 12723601 = 9542701) B9542701
theorem B16964801 : Blo 2233435 16964801 := bstep (se 2 (by rfl) ⟨6361800, by rfl⟩ : syracuseStep 16964801 = 12723601) B12723601
theorem B11309867 : Blo 2233435 11309867 := bstep (se 1 (by rfl) ⟨8482400, by rfl⟩ : syracuseStep 11309867 = 16964801) B16964801
theorem B7539911 : Blo 2233435 7539911 := bstep (se 1 (by rfl) ⟨5654933, by rfl⟩ : syracuseStep 7539911 = 11309867) B11309867
theorem B5026607 : Blo 2233435 5026607 := bstep (se 1 (by rfl) ⟨3769955, by rfl⟩ : syracuseStep 5026607 = 7539911) B7539911
theorem B3351071 : Blo 2233435 3351071 := bstep (se 1 (by rfl) ⟨2513303, by rfl⟩ : syracuseStep 3351071 = 5026607) B5026607
theorem B2234047 : Blo 2233435 2234047 := bstep (se 1 (by rfl) ⟨1675535, by rfl⟩ : syracuseStep 2234047 = 3351071) B3351071
theorem B3351077 : Blo 2233435 3351077 := bbase (se 4 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 3351077 = 628327) (by norm_num)
theorem B2234051 : Blo 2233435 2234051 := bstep (se 1 (by rfl) ⟨1675538, by rfl⟩ : syracuseStep 2234051 = 3351077) B3351077
theorem B2827477 : Blo 2233435 2827477 := bbase (se 7 (by rfl) ⟨33134, by rfl⟩ : syracuseStep 2827477 = 66269) (by norm_num)
theorem B3769969 : Blo 2233435 3769969 := bstep (se 2 (by rfl) ⟨1413738, by rfl⟩ : syracuseStep 3769969 = 2827477) B2827477
theorem B5026625 : Blo 2233435 5026625 := bstep (se 2 (by rfl) ⟨1884984, by rfl⟩ : syracuseStep 5026625 = 3769969) B3769969
theorem B3351083 : Blo 2233435 3351083 := bstep (se 1 (by rfl) ⟨2513312, by rfl⟩ : syracuseStep 3351083 = 5026625) B5026625
theorem B2234055 : Blo 2233435 2234055 := bstep (se 1 (by rfl) ⟨1675541, by rfl⟩ : syracuseStep 2234055 = 3351083) B3351083
theorem B2513317 : Blo 2233435 2513317 := bbase (se 4 (by rfl) ⟨235623, by rfl⟩ : syracuseStep 2513317 = 471247) (by norm_num)
theorem B3351089 : Blo 2233435 3351089 := bstep (se 2 (by rfl) ⟨1256658, by rfl⟩ : syracuseStep 3351089 = 2513317) B2513317
theorem B2234059 : Blo 2233435 2234059 := bstep (se 1 (by rfl) ⟨1675544, by rfl⟩ : syracuseStep 2234059 = 3351089) B3351089
theorem B2264545 : Blo 2233435 2264545 := bbase (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) (by norm_num)
theorem B3019393 : Blo 2233435 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B4025857 : Blo 2233435 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B5367809 : Blo 2233435 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B14314157 : Blo 2233435 14314157 := bstep (se 3 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 14314157 = 5367809) B5367809
theorem B9542771 : Blo 2233435 9542771 := bstep (se 1 (by rfl) ⟨7157078, by rfl⟩ : syracuseStep 9542771 = 14314157) B14314157
theorem B6361847 : Blo 2233435 6361847 := bstep (se 1 (by rfl) ⟨4771385, by rfl⟩ : syracuseStep 6361847 = 9542771) B9542771
theorem B4241231 : Blo 2233435 4241231 := bstep (se 1 (by rfl) ⟨3180923, by rfl⟩ : syracuseStep 4241231 = 6361847) B6361847
theorem B2827487 : Blo 2233435 2827487 := bstep (se 1 (by rfl) ⟨2120615, by rfl⟩ : syracuseStep 2827487 = 4241231) B4241231
theorem B7539965 : Blo 2233435 7539965 := bstep (se 3 (by rfl) ⟨1413743, by rfl⟩ : syracuseStep 7539965 = 2827487) B2827487
theorem B5026643 : Blo 2233435 5026643 := bstep (se 1 (by rfl) ⟨3769982, by rfl⟩ : syracuseStep 5026643 = 7539965) B7539965
theorem B3351095 : Blo 2233435 3351095 := bstep (se 1 (by rfl) ⟨2513321, by rfl⟩ : syracuseStep 3351095 = 5026643) B5026643
theorem B2234063 : Blo 2233435 2234063 := bstep (se 1 (by rfl) ⟨1675547, by rfl⟩ : syracuseStep 2234063 = 3351095) B3351095
theorem B3351101 : Blo 2233435 3351101 := bbase (se 3 (by rfl) ⟨628331, by rfl⟩ : syracuseStep 3351101 = 1256663) (by norm_num)
theorem B2234067 : Blo 2233435 2234067 := bstep (se 1 (by rfl) ⟨1675550, by rfl⟩ : syracuseStep 2234067 = 3351101) B3351101
theorem B5026661 : Blo 2233435 5026661 := bbase (se 4 (by rfl) ⟨471249, by rfl⟩ : syracuseStep 5026661 = 942499) (by norm_num)
theorem B3351107 : Blo 2233435 3351107 := bstep (se 1 (by rfl) ⟨2513330, by rfl⟩ : syracuseStep 3351107 = 5026661) B5026661
theorem B2234071 : Blo 2233435 2234071 := bstep (se 1 (by rfl) ⟨1675553, by rfl⟩ : syracuseStep 2234071 = 3351107) B3351107
theorem B5655005 : Blo 2233435 5655005 := bbase (se 3 (by rfl) ⟨1060313, by rfl⟩ : syracuseStep 5655005 = 2120627) (by norm_num)
theorem B3770003 : Blo 2233435 3770003 := bstep (se 1 (by rfl) ⟨2827502, by rfl⟩ : syracuseStep 3770003 = 5655005) B5655005
theorem B2513335 : Blo 2233435 2513335 := bstep (se 1 (by rfl) ⟨1885001, by rfl⟩ : syracuseStep 2513335 = 3770003) B3770003
theorem B3351113 : Blo 2233435 3351113 := bstep (se 2 (by rfl) ⟨1256667, by rfl⟩ : syracuseStep 3351113 = 2513335) B2513335
theorem B2234075 : Blo 2233435 2234075 := bstep (se 1 (by rfl) ⟨1675556, by rfl⟩ : syracuseStep 2234075 = 3351113) B3351113
theorem B4241261 : Blo 2233435 4241261 := bbase (se 3 (by rfl) ⟨795236, by rfl⟩ : syracuseStep 4241261 = 1590473) (by norm_num)
theorem B11310029 : Blo 2233435 11310029 := bstep (se 3 (by rfl) ⟨2120630, by rfl⟩ : syracuseStep 11310029 = 4241261) B4241261
theorem B7540019 : Blo 2233435 7540019 := bstep (se 1 (by rfl) ⟨5655014, by rfl⟩ : syracuseStep 7540019 = 11310029) B11310029
theorem B5026679 : Blo 2233435 5026679 := bstep (se 1 (by rfl) ⟨3770009, by rfl⟩ : syracuseStep 5026679 = 7540019) B7540019
theorem B3351119 : Blo 2233435 3351119 := bstep (se 1 (by rfl) ⟨2513339, by rfl⟩ : syracuseStep 3351119 = 5026679) B5026679
theorem B2234079 : Blo 2233435 2234079 := bstep (se 1 (by rfl) ⟨1675559, by rfl⟩ : syracuseStep 2234079 = 3351119) B3351119
theorem B3351125 : Blo 2233435 3351125 := bbase (se 8 (by rfl) ⟨19635, by rfl⟩ : syracuseStep 3351125 = 39271) (by norm_num)
theorem B2234083 : Blo 2233435 2234083 := bstep (se 1 (by rfl) ⟨1675562, by rfl⟩ : syracuseStep 2234083 = 3351125) B3351125
theorem B10735733 : Blo 2233435 10735733 := bbase (se 5 (by rfl) ⟨503237, by rfl⟩ : syracuseStep 10735733 = 1006475) (by norm_num)
theorem B7157155 : Blo 2233435 7157155 := bstep (se 1 (by rfl) ⟨5367866, by rfl⟩ : syracuseStep 7157155 = 10735733) B10735733
theorem B9542873 : Blo 2233435 9542873 := bstep (se 2 (by rfl) ⟨3578577, by rfl⟩ : syracuseStep 9542873 = 7157155) B7157155
theorem B6361915 : Blo 2233435 6361915 := bstep (se 1 (by rfl) ⟨4771436, by rfl⟩ : syracuseStep 6361915 = 9542873) B9542873
theorem B8482553 : Blo 2233435 8482553 := bstep (se 2 (by rfl) ⟨3180957, by rfl⟩ : syracuseStep 8482553 = 6361915) B6361915
theorem B5655035 : Blo 2233435 5655035 := bstep (se 1 (by rfl) ⟨4241276, by rfl⟩ : syracuseStep 5655035 = 8482553) B8482553
theorem B3770023 : Blo 2233435 3770023 := bstep (se 1 (by rfl) ⟨2827517, by rfl⟩ : syracuseStep 3770023 = 5655035) B5655035
theorem B5026697 : Blo 2233435 5026697 := bstep (se 2 (by rfl) ⟨1885011, by rfl⟩ : syracuseStep 5026697 = 3770023) B3770023
theorem B3351131 : Blo 2233435 3351131 := bstep (se 1 (by rfl) ⟨2513348, by rfl⟩ : syracuseStep 3351131 = 5026697) B5026697
theorem B2234087 : Blo 2233435 2234087 := bstep (se 1 (by rfl) ⟨1675565, by rfl⟩ : syracuseStep 2234087 = 3351131) B3351131
theorem B2513353 : Blo 2233435 2513353 := bbase (se 2 (by rfl) ⟨942507, by rfl⟩ : syracuseStep 2513353 = 1885015) (by norm_num)
theorem B3351137 : Blo 2233435 3351137 := bstep (se 2 (by rfl) ⟨1256676, by rfl⟩ : syracuseStep 3351137 = 2513353) B2513353
theorem B2234091 : Blo 2233435 2234091 := bstep (se 1 (by rfl) ⟨1675568, by rfl⟩ : syracuseStep 2234091 = 3351137) B3351137
theorem B19085813 : Blo 2233435 19085813 := bbase (se 5 (by rfl) ⟨894647, by rfl⟩ : syracuseStep 19085813 = 1789295) (by norm_num)
theorem B12723875 : Blo 2233435 12723875 := bstep (se 1 (by rfl) ⟨9542906, by rfl⟩ : syracuseStep 12723875 = 19085813) B19085813
theorem B8482583 : Blo 2233435 8482583 := bstep (se 1 (by rfl) ⟨6361937, by rfl⟩ : syracuseStep 8482583 = 12723875) B12723875
theorem B5655055 : Blo 2233435 5655055 := bstep (se 1 (by rfl) ⟨4241291, by rfl⟩ : syracuseStep 5655055 = 8482583) B8482583
theorem B7540073 : Blo 2233435 7540073 := bstep (se 2 (by rfl) ⟨2827527, by rfl⟩ : syracuseStep 7540073 = 5655055) B5655055
theorem B5026715 : Blo 2233435 5026715 := bstep (se 1 (by rfl) ⟨3770036, by rfl⟩ : syracuseStep 5026715 = 7540073) B7540073
theorem B3351143 : Blo 2233435 3351143 := bstep (se 1 (by rfl) ⟨2513357, by rfl⟩ : syracuseStep 3351143 = 5026715) B5026715
theorem B2234095 : Blo 2233435 2234095 := bstep (se 1 (by rfl) ⟨1675571, by rfl⟩ : syracuseStep 2234095 = 3351143) B3351143
theorem B3351149 : Blo 2233435 3351149 := bbase (se 3 (by rfl) ⟨628340, by rfl⟩ : syracuseStep 3351149 = 1256681) (by norm_num)
theorem B2234099 : Blo 2233435 2234099 := bstep (se 1 (by rfl) ⟨1675574, by rfl⟩ : syracuseStep 2234099 = 3351149) B3351149
theorem B5026733 : Blo 2233435 5026733 := bbase (se 3 (by rfl) ⟨942512, by rfl⟩ : syracuseStep 5026733 = 1885025) (by norm_num)
theorem B3351155 : Blo 2233435 3351155 := bstep (se 1 (by rfl) ⟨2513366, by rfl⟩ : syracuseStep 3351155 = 5026733) B5026733
theorem B2234103 : Blo 2233435 2234103 := bstep (se 1 (by rfl) ⟨1675577, by rfl⟩ : syracuseStep 2234103 = 3351155) B3351155
theorem B6361973 : Blo 2233435 6361973 := bbase (se 5 (by rfl) ⟨298217, by rfl⟩ : syracuseStep 6361973 = 596435) (by norm_num)
theorem B4241315 : Blo 2233435 4241315 := bstep (se 1 (by rfl) ⟨3180986, by rfl⟩ : syracuseStep 4241315 = 6361973) B6361973
theorem B2827543 : Blo 2233435 2827543 := bstep (se 1 (by rfl) ⟨2120657, by rfl⟩ : syracuseStep 2827543 = 4241315) B4241315
theorem B3770057 : Blo 2233435 3770057 := bstep (se 2 (by rfl) ⟨1413771, by rfl⟩ : syracuseStep 3770057 = 2827543) B2827543
theorem B2513371 : Blo 2233435 2513371 := bstep (se 1 (by rfl) ⟨1885028, by rfl⟩ : syracuseStep 2513371 = 3770057) B3770057
theorem B3351161 : Blo 2233435 3351161 := bstep (se 2 (by rfl) ⟨1256685, by rfl⟩ : syracuseStep 3351161 = 2513371) B2513371
theorem B2234107 : Blo 2233435 2234107 := bstep (se 1 (by rfl) ⟨1675580, by rfl⟩ : syracuseStep 2234107 = 3351161) B3351161
theorem B3821501 : Blo 2233435 3821501 := bbase (se 3 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 3821501 = 1433063) (by norm_num)
theorem B2547667 : Blo 2233435 2547667 := bstep (se 1 (by rfl) ⟨1910750, by rfl⟩ : syracuseStep 2547667 = 3821501) B3821501
theorem B3396889 : Blo 2233435 3396889 := bstep (se 2 (by rfl) ⟨1273833, by rfl⟩ : syracuseStep 3396889 = 2547667) B2547667
theorem B18116741 : Blo 2233435 18116741 := bstep (se 4 (by rfl) ⟨1698444, by rfl⟩ : syracuseStep 18116741 = 3396889) B3396889
theorem B48311309 : Blo 2233435 48311309 := bstep (se 3 (by rfl) ⟨9058370, by rfl⟩ : syracuseStep 48311309 = 18116741) B18116741
theorem B32207539 : Blo 2233435 32207539 := bstep (se 1 (by rfl) ⟨24155654, by rfl⟩ : syracuseStep 32207539 = 48311309) B48311309
theorem B42943385 : Blo 2233435 42943385 := bstep (se 2 (by rfl) ⟨16103769, by rfl⟩ : syracuseStep 42943385 = 32207539) B32207539
theorem B28628923 : Blo 2233435 28628923 := bstep (se 1 (by rfl) ⟨21471692, by rfl⟩ : syracuseStep 28628923 = 42943385) B42943385
theorem B38171897 : Blo 2233435 38171897 := bstep (se 2 (by rfl) ⟨14314461, by rfl⟩ : syracuseStep 38171897 = 28628923) B28628923
theorem B25447931 : Blo 2233435 25447931 := bstep (se 1 (by rfl) ⟨19085948, by rfl⟩ : syracuseStep 25447931 = 38171897) B38171897
theorem B16965287 : Blo 2233435 16965287 := bstep (se 1 (by rfl) ⟨12723965, by rfl⟩ : syracuseStep 16965287 = 25447931) B25447931
theorem B11310191 : Blo 2233435 11310191 := bstep (se 1 (by rfl) ⟨8482643, by rfl⟩ : syracuseStep 11310191 = 16965287) B16965287
theorem B7540127 : Blo 2233435 7540127 := bstep (se 1 (by rfl) ⟨5655095, by rfl⟩ : syracuseStep 7540127 = 11310191) B11310191
theorem B5026751 : Blo 2233435 5026751 := bstep (se 1 (by rfl) ⟨3770063, by rfl⟩ : syracuseStep 5026751 = 7540127) B7540127
theorem B3351167 : Blo 2233435 3351167 := bstep (se 1 (by rfl) ⟨2513375, by rfl⟩ : syracuseStep 3351167 = 5026751) B5026751
theorem B2234111 : Blo 2233435 2234111 := bstep (se 1 (by rfl) ⟨1675583, by rfl⟩ : syracuseStep 2234111 = 3351167) B3351167
theorem B3351173 : Blo 2233435 3351173 := bbase (se 4 (by rfl) ⟨314172, by rfl⟩ : syracuseStep 3351173 = 628345) (by norm_num)
theorem B2234115 : Blo 2233435 2234115 := bstep (se 1 (by rfl) ⟨1675586, by rfl⟩ : syracuseStep 2234115 = 3351173) B3351173
theorem B3770077 : Blo 2233435 3770077 := bbase (se 3 (by rfl) ⟨706889, by rfl⟩ : syracuseStep 3770077 = 1413779) (by norm_num)
theorem B5026769 : Blo 2233435 5026769 := bstep (se 2 (by rfl) ⟨1885038, by rfl⟩ : syracuseStep 5026769 = 3770077) B3770077
theorem B3351179 : Blo 2233435 3351179 := bstep (se 1 (by rfl) ⟨2513384, by rfl⟩ : syracuseStep 3351179 = 5026769) B5026769
theorem B2234119 : Blo 2233435 2234119 := bstep (se 1 (by rfl) ⟨1675589, by rfl⟩ : syracuseStep 2234119 = 3351179) B3351179
theorem B2513389 : Blo 2233435 2513389 := bbase (se 3 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 2513389 = 942521) (by norm_num)
theorem B3351185 : Blo 2233435 3351185 := bstep (se 2 (by rfl) ⟨1256694, by rfl⟩ : syracuseStep 3351185 = 2513389) B2513389
theorem B2234123 : Blo 2233435 2234123 := bstep (se 1 (by rfl) ⟨1675592, by rfl⟩ : syracuseStep 2234123 = 3351185) B3351185
theorem B7540181 : Blo 2233435 7540181 := bbase (se 7 (by rfl) ⟨88361, by rfl⟩ : syracuseStep 7540181 = 176723) (by norm_num)
theorem B5026787 : Blo 2233435 5026787 := bstep (se 1 (by rfl) ⟨3770090, by rfl⟩ : syracuseStep 5026787 = 7540181) B7540181
theorem B3351191 : Blo 2233435 3351191 := bstep (se 1 (by rfl) ⟨2513393, by rfl⟩ : syracuseStep 3351191 = 5026787) B5026787
theorem B2234127 : Blo 2233435 2234127 := bstep (se 1 (by rfl) ⟨1675595, by rfl⟩ : syracuseStep 2234127 = 3351191) B3351191
theorem B3351197 : Blo 2233435 3351197 := bbase (se 3 (by rfl) ⟨628349, by rfl⟩ : syracuseStep 3351197 = 1256699) (by norm_num)
theorem B2234131 : Blo 2233435 2234131 := bstep (se 1 (by rfl) ⟨1675598, by rfl⟩ : syracuseStep 2234131 = 3351197) B3351197
theorem B5026805 : Blo 2233435 5026805 := bbase (se 5 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 5026805 = 471263) (by norm_num)
theorem B3351203 : Blo 2233435 3351203 := bstep (se 1 (by rfl) ⟨2513402, by rfl⟩ : syracuseStep 3351203 = 5026805) B5026805
theorem B2234135 : Blo 2233435 2234135 := bstep (se 1 (by rfl) ⟨1675601, by rfl⟩ : syracuseStep 2234135 = 3351203) B3351203
theorem B8598485 : Blo 2233435 8598485 := bbase (se 7 (by rfl) ⟨100763, by rfl⟩ : syracuseStep 8598485 = 201527) (by norm_num)
theorem B22929293 : Blo 2233435 22929293 := bstep (se 3 (by rfl) ⟨4299242, by rfl⟩ : syracuseStep 22929293 = 8598485) B8598485
theorem B15286195 : Blo 2233435 15286195 := bstep (se 1 (by rfl) ⟨11464646, by rfl⟩ : syracuseStep 15286195 = 22929293) B22929293
theorem B20381593 : Blo 2233435 20381593 := bstep (se 2 (by rfl) ⟨7643097, by rfl⟩ : syracuseStep 20381593 = 15286195) B15286195
theorem B27175457 : Blo 2233435 27175457 := bstep (se 2 (by rfl) ⟨10190796, by rfl⟩ : syracuseStep 27175457 = 20381593) B20381593
theorem B72467885 : Blo 2233435 72467885 := bstep (se 3 (by rfl) ⟨13587728, by rfl⟩ : syracuseStep 72467885 = 27175457) B27175457
theorem B48311923 : Blo 2233435 48311923 := bstep (se 1 (by rfl) ⟨36233942, by rfl⟩ : syracuseStep 48311923 = 72467885) B72467885
theorem B64415897 : Blo 2233435 64415897 := bstep (se 2 (by rfl) ⟨24155961, by rfl⟩ : syracuseStep 64415897 = 48311923) B48311923
theorem B42943931 : Blo 2233435 42943931 := bstep (se 1 (by rfl) ⟨32207948, by rfl⟩ : syracuseStep 42943931 = 64415897) B64415897
theorem B28629287 : Blo 2233435 28629287 := bstep (se 1 (by rfl) ⟨21471965, by rfl⟩ : syracuseStep 28629287 = 42943931) B42943931
theorem B19086191 : Blo 2233435 19086191 := bstep (se 1 (by rfl) ⟨14314643, by rfl⟩ : syracuseStep 19086191 = 28629287) B28629287
theorem B12724127 : Blo 2233435 12724127 := bstep (se 1 (by rfl) ⟨9543095, by rfl⟩ : syracuseStep 12724127 = 19086191) B19086191
theorem B8482751 : Blo 2233435 8482751 := bstep (se 1 (by rfl) ⟨6362063, by rfl⟩ : syracuseStep 8482751 = 12724127) B12724127
theorem B5655167 : Blo 2233435 5655167 := bstep (se 1 (by rfl) ⟨4241375, by rfl⟩ : syracuseStep 5655167 = 8482751) B8482751
theorem B3770111 : Blo 2233435 3770111 := bstep (se 1 (by rfl) ⟨2827583, by rfl⟩ : syracuseStep 3770111 = 5655167) B5655167
theorem B2513407 : Blo 2233435 2513407 := bstep (se 1 (by rfl) ⟨1885055, by rfl⟩ : syracuseStep 2513407 = 3770111) B3770111
theorem B3351209 : Blo 2233435 3351209 := bstep (se 2 (by rfl) ⟨1256703, by rfl⟩ : syracuseStep 3351209 = 2513407) B2513407
theorem B2234139 : Blo 2233435 2234139 := bstep (se 1 (by rfl) ⟨1675604, by rfl⟩ : syracuseStep 2234139 = 3351209) B3351209
theorem B3181037 : Blo 2233435 3181037 := bbase (se 3 (by rfl) ⟨596444, by rfl⟩ : syracuseStep 3181037 = 1192889) (by norm_num)
theorem B8482765 : Blo 2233435 8482765 := bstep (se 3 (by rfl) ⟨1590518, by rfl⟩ : syracuseStep 8482765 = 3181037) B3181037
theorem B11310353 : Blo 2233435 11310353 := bstep (se 2 (by rfl) ⟨4241382, by rfl⟩ : syracuseStep 11310353 = 8482765) B8482765
theorem B7540235 : Blo 2233435 7540235 := bstep (se 1 (by rfl) ⟨5655176, by rfl⟩ : syracuseStep 7540235 = 11310353) B11310353
theorem B5026823 : Blo 2233435 5026823 := bstep (se 1 (by rfl) ⟨3770117, by rfl⟩ : syracuseStep 5026823 = 7540235) B7540235
theorem B3351215 : Blo 2233435 3351215 := bstep (se 1 (by rfl) ⟨2513411, by rfl⟩ : syracuseStep 3351215 = 5026823) B5026823
theorem B2234143 : Blo 2233435 2234143 := bstep (se 1 (by rfl) ⟨1675607, by rfl⟩ : syracuseStep 2234143 = 3351215) B3351215
theorem B3351221 : Blo 2233435 3351221 := bbase (se 5 (by rfl) ⟨157088, by rfl⟩ : syracuseStep 3351221 = 314177) (by norm_num)
theorem B2234147 : Blo 2233435 2234147 := bstep (se 1 (by rfl) ⟨1675610, by rfl⟩ : syracuseStep 2234147 = 3351221) B3351221
theorem B5655197 : Blo 2233435 5655197 := bbase (se 3 (by rfl) ⟨1060349, by rfl⟩ : syracuseStep 5655197 = 2120699) (by norm_num)
theorem B3770131 : Blo 2233435 3770131 := bstep (se 1 (by rfl) ⟨2827598, by rfl⟩ : syracuseStep 3770131 = 5655197) B5655197
theorem B5026841 : Blo 2233435 5026841 := bstep (se 2 (by rfl) ⟨1885065, by rfl⟩ : syracuseStep 5026841 = 3770131) B3770131
theorem B3351227 : Blo 2233435 3351227 := bstep (se 1 (by rfl) ⟨2513420, by rfl⟩ : syracuseStep 3351227 = 5026841) B5026841
theorem B2234151 : Blo 2233435 2234151 := bstep (se 1 (by rfl) ⟨1675613, by rfl⟩ : syracuseStep 2234151 = 3351227) B3351227
theorem B2513425 : Blo 2233435 2513425 := bbase (se 2 (by rfl) ⟨942534, by rfl⟩ : syracuseStep 2513425 = 1885069) (by norm_num)
theorem B3351233 : Blo 2233435 3351233 := bstep (se 2 (by rfl) ⟨1256712, by rfl⟩ : syracuseStep 3351233 = 2513425) B2513425
theorem B2234155 : Blo 2233435 2234155 := bstep (se 1 (by rfl) ⟨1675616, by rfl⟩ : syracuseStep 2234155 = 3351233) B3351233
theorem B4241413 : Blo 2233435 4241413 := bbase (se 4 (by rfl) ⟨397632, by rfl⟩ : syracuseStep 4241413 = 795265) (by norm_num)
theorem B5655217 : Blo 2233435 5655217 := bstep (se 2 (by rfl) ⟨2120706, by rfl⟩ : syracuseStep 5655217 = 4241413) B4241413
theorem B7540289 : Blo 2233435 7540289 := bstep (se 2 (by rfl) ⟨2827608, by rfl⟩ : syracuseStep 7540289 = 5655217) B5655217
theorem B5026859 : Blo 2233435 5026859 := bstep (se 1 (by rfl) ⟨3770144, by rfl⟩ : syracuseStep 5026859 = 7540289) B7540289
theorem B3351239 : Blo 2233435 3351239 := bstep (se 1 (by rfl) ⟨2513429, by rfl⟩ : syracuseStep 3351239 = 5026859) B5026859
theorem B2234159 : Blo 2233435 2234159 := bstep (se 1 (by rfl) ⟨1675619, by rfl⟩ : syracuseStep 2234159 = 3351239) B3351239
theorem B3351245 : Blo 2233435 3351245 := bbase (se 3 (by rfl) ⟨628358, by rfl⟩ : syracuseStep 3351245 = 1256717) (by norm_num)
theorem B2234163 : Blo 2233435 2234163 := bstep (se 1 (by rfl) ⟨1675622, by rfl⟩ : syracuseStep 2234163 = 3351245) B3351245
theorem B5026877 : Blo 2233435 5026877 := bbase (se 3 (by rfl) ⟨942539, by rfl⟩ : syracuseStep 5026877 = 1885079) (by norm_num)
theorem B3351251 : Blo 2233435 3351251 := bstep (se 1 (by rfl) ⟨2513438, by rfl⟩ : syracuseStep 3351251 = 5026877) B5026877
theorem B2234167 : Blo 2233435 2234167 := bstep (se 1 (by rfl) ⟨1675625, by rfl⟩ : syracuseStep 2234167 = 3351251) B3351251
theorem B3770165 : Blo 2233435 3770165 := bbase (se 5 (by rfl) ⟨176726, by rfl⟩ : syracuseStep 3770165 = 353453) (by norm_num)
theorem B2513443 : Blo 2233435 2513443 := bstep (se 1 (by rfl) ⟨1885082, by rfl⟩ : syracuseStep 2513443 = 3770165) B3770165
theorem B3351257 : Blo 2233435 3351257 := bstep (se 2 (by rfl) ⟨1256721, by rfl⟩ : syracuseStep 3351257 = 2513443) B2513443
theorem B2234171 : Blo 2233435 2234171 := bstep (se 1 (by rfl) ⟨1675628, by rfl⟩ : syracuseStep 2234171 = 3351257) B3351257
theorem B6362165 : Blo 2233435 6362165 := bbase (se 5 (by rfl) ⟨298226, by rfl⟩ : syracuseStep 6362165 = 596453) (by norm_num)
theorem B16965773 : Blo 2233435 16965773 := bstep (se 3 (by rfl) ⟨3181082, by rfl⟩ : syracuseStep 16965773 = 6362165) B6362165
theorem B11310515 : Blo 2233435 11310515 := bstep (se 1 (by rfl) ⟨8482886, by rfl⟩ : syracuseStep 11310515 = 16965773) B16965773
theorem B7540343 : Blo 2233435 7540343 := bstep (se 1 (by rfl) ⟨5655257, by rfl⟩ : syracuseStep 7540343 = 11310515) B11310515
theorem B5026895 : Blo 2233435 5026895 := bstep (se 1 (by rfl) ⟨3770171, by rfl⟩ : syracuseStep 5026895 = 7540343) B7540343
theorem B3351263 : Blo 2233435 3351263 := bstep (se 1 (by rfl) ⟨2513447, by rfl⟩ : syracuseStep 3351263 = 5026895) B5026895
theorem B2234175 : Blo 2233435 2234175 := bstep (se 1 (by rfl) ⟨1675631, by rfl⟩ : syracuseStep 2234175 = 3351263) B3351263
theorem B3351269 : Blo 2233435 3351269 := bbase (se 4 (by rfl) ⟨314181, by rfl⟩ : syracuseStep 3351269 = 628363) (by norm_num)
theorem B2234179 : Blo 2233435 2234179 := bstep (se 1 (by rfl) ⟨1675634, by rfl⟩ : syracuseStep 2234179 = 3351269) B3351269
theorem B2385821 : Blo 2233435 2385821 := bbase (se 3 (by rfl) ⟨447341, by rfl⟩ : syracuseStep 2385821 = 894683) (by norm_num)
theorem B6362189 : Blo 2233435 6362189 := bstep (se 3 (by rfl) ⟨1192910, by rfl⟩ : syracuseStep 6362189 = 2385821) B2385821
theorem B4241459 : Blo 2233435 4241459 := bstep (se 1 (by rfl) ⟨3181094, by rfl⟩ : syracuseStep 4241459 = 6362189) B6362189
theorem B2827639 : Blo 2233435 2827639 := bstep (se 1 (by rfl) ⟨2120729, by rfl⟩ : syracuseStep 2827639 = 4241459) B4241459
theorem B3770185 : Blo 2233435 3770185 := bstep (se 2 (by rfl) ⟨1413819, by rfl⟩ : syracuseStep 3770185 = 2827639) B2827639
theorem B5026913 : Blo 2233435 5026913 := bstep (se 2 (by rfl) ⟨1885092, by rfl⟩ : syracuseStep 5026913 = 3770185) B3770185
theorem B3351275 : Blo 2233435 3351275 := bstep (se 1 (by rfl) ⟨2513456, by rfl⟩ : syracuseStep 3351275 = 5026913) B5026913
theorem B2234183 : Blo 2233435 2234183 := bstep (se 1 (by rfl) ⟨1675637, by rfl⟩ : syracuseStep 2234183 = 3351275) B3351275
theorem B2513461 : Blo 2233435 2513461 := bbase (se 5 (by rfl) ⟨117818, by rfl⟩ : syracuseStep 2513461 = 235637) (by norm_num)
theorem B3351281 : Blo 2233435 3351281 := bstep (se 2 (by rfl) ⟨1256730, by rfl⟩ : syracuseStep 3351281 = 2513461) B2513461
theorem B2234187 : Blo 2233435 2234187 := bstep (se 1 (by rfl) ⟨1675640, by rfl⟩ : syracuseStep 2234187 = 3351281) B3351281
theorem B2827649 : Blo 2233435 2827649 := bbase (se 2 (by rfl) ⟨1060368, by rfl⟩ : syracuseStep 2827649 = 2120737) (by norm_num)
theorem B7540397 : Blo 2233435 7540397 := bstep (se 3 (by rfl) ⟨1413824, by rfl⟩ : syracuseStep 7540397 = 2827649) B2827649
theorem B5026931 : Blo 2233435 5026931 := bstep (se 1 (by rfl) ⟨3770198, by rfl⟩ : syracuseStep 5026931 = 7540397) B7540397
theorem B3351287 : Blo 2233435 3351287 := bstep (se 1 (by rfl) ⟨2513465, by rfl⟩ : syracuseStep 3351287 = 5026931) B5026931
theorem B2234191 : Blo 2233435 2234191 := bstep (se 1 (by rfl) ⟨1675643, by rfl⟩ : syracuseStep 2234191 = 3351287) B3351287
theorem B3351293 : Blo 2233435 3351293 := bbase (se 3 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 3351293 = 1256735) (by norm_num)
theorem B2234195 : Blo 2233435 2234195 := bstep (se 1 (by rfl) ⟨1675646, by rfl⟩ : syracuseStep 2234195 = 3351293) B3351293
theorem B5026949 : Blo 2233435 5026949 := bbase (se 4 (by rfl) ⟨471276, by rfl⟩ : syracuseStep 5026949 = 942553) (by norm_num)
theorem B3351299 : Blo 2233435 3351299 := bstep (se 1 (by rfl) ⟨2513474, by rfl⟩ : syracuseStep 3351299 = 5026949) B5026949
theorem B2234199 : Blo 2233435 2234199 := bstep (se 1 (by rfl) ⟨1675649, by rfl⟩ : syracuseStep 2234199 = 3351299) B3351299
theorem B4771685 : Blo 2233435 4771685 := bbase (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) (by norm_num)
theorem B3181123 : Blo 2233435 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B4241497 : Blo 2233435 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B5655329 : Blo 2233435 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B3770219 : Blo 2233435 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B2513479 : Blo 2233435 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B3351305 : Blo 2233435 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B2234203 : Blo 2233435 2234203 := bstep (se 1 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 2234203 = 3351305) B3351305
theorem B11310677 : Blo 2233435 11310677 := bbase (se 8 (by rfl) ⟨66273, by rfl⟩ : syracuseStep 11310677 = 132547) (by norm_num)
theorem B7540451 : Blo 2233435 7540451 := bstep (se 1 (by rfl) ⟨5655338, by rfl⟩ : syracuseStep 7540451 = 11310677) B11310677
theorem B5026967 : Blo 2233435 5026967 := bstep (se 1 (by rfl) ⟨3770225, by rfl⟩ : syracuseStep 5026967 = 7540451) B7540451
theorem B3351311 : Blo 2233435 3351311 := bstep (se 1 (by rfl) ⟨2513483, by rfl⟩ : syracuseStep 3351311 = 5026967) B5026967
theorem B2234207 : Blo 2233435 2234207 := bstep (se 1 (by rfl) ⟨1675655, by rfl⟩ : syracuseStep 2234207 = 3351311) B3351311
theorem B3351317 : Blo 2233435 3351317 := bbase (se 6 (by rfl) ⟨78546, by rfl⟩ : syracuseStep 3351317 = 157093) (by norm_num)
theorem B2234211 : Blo 2233435 2234211 := bstep (se 1 (by rfl) ⟨1675658, by rfl⟩ : syracuseStep 2234211 = 3351317) B3351317
theorem B4081061 : Blo 2233435 4081061 := bbase (se 4 (by rfl) ⟨382599, by rfl⟩ : syracuseStep 4081061 = 765199) (by norm_num)
theorem B10882829 : Blo 2233435 10882829 := bstep (se 3 (by rfl) ⟨2040530, by rfl⟩ : syracuseStep 10882829 = 4081061) B4081061
theorem B7255219 : Blo 2233435 7255219 := bstep (se 1 (by rfl) ⟨5441414, by rfl⟩ : syracuseStep 7255219 = 10882829) B10882829
theorem B9673625 : Blo 2233435 9673625 := bstep (se 2 (by rfl) ⟨3627609, by rfl⟩ : syracuseStep 9673625 = 7255219) B7255219
theorem B25796333 : Blo 2233435 25796333 := bstep (se 3 (by rfl) ⟨4836812, by rfl⟩ : syracuseStep 25796333 = 9673625) B9673625
theorem B17197555 : Blo 2233435 17197555 := bstep (se 1 (by rfl) ⟨12898166, by rfl⟩ : syracuseStep 17197555 = 25796333) B25796333
theorem B22930073 : Blo 2233435 22930073 := bstep (se 2 (by rfl) ⟨8598777, by rfl⟩ : syracuseStep 22930073 = 17197555) B17197555
theorem B15286715 : Blo 2233435 15286715 := bstep (se 1 (by rfl) ⟨11465036, by rfl⟩ : syracuseStep 15286715 = 22930073) B22930073
theorem B10191143 : Blo 2233435 10191143 := bstep (se 1 (by rfl) ⟨7643357, by rfl⟩ : syracuseStep 10191143 = 15286715) B15286715
theorem B27176381 : Blo 2233435 27176381 := bstep (se 3 (by rfl) ⟨5095571, by rfl⟩ : syracuseStep 27176381 = 10191143) B10191143
theorem B18117587 : Blo 2233435 18117587 := bstep (se 1 (by rfl) ⟨13588190, by rfl⟩ : syracuseStep 18117587 = 27176381) B27176381
theorem B12078391 : Blo 2233435 12078391 := bstep (se 1 (by rfl) ⟨9058793, by rfl⟩ : syracuseStep 12078391 = 18117587) B18117587
theorem B16104521 : Blo 2233435 16104521 := bstep (se 2 (by rfl) ⟨6039195, by rfl⟩ : syracuseStep 16104521 = 12078391) B12078391
theorem B42945389 : Blo 2233435 42945389 := bstep (se 3 (by rfl) ⟨8052260, by rfl⟩ : syracuseStep 42945389 = 16104521) B16104521
theorem B28630259 : Blo 2233435 28630259 := bstep (se 1 (by rfl) ⟨21472694, by rfl⟩ : syracuseStep 28630259 = 42945389) B42945389
theorem B19086839 : Blo 2233435 19086839 := bstep (se 1 (by rfl) ⟨14315129, by rfl⟩ : syracuseStep 19086839 = 28630259) B28630259
theorem B12724559 : Blo 2233435 12724559 := bstep (se 1 (by rfl) ⟨9543419, by rfl⟩ : syracuseStep 12724559 = 19086839) B19086839
theorem B8483039 : Blo 2233435 8483039 := bstep (se 1 (by rfl) ⟨6362279, by rfl⟩ : syracuseStep 8483039 = 12724559) B12724559
theorem B5655359 : Blo 2233435 5655359 := bstep (se 1 (by rfl) ⟨4241519, by rfl⟩ : syracuseStep 5655359 = 8483039) B8483039
theorem B3770239 : Blo 2233435 3770239 := bstep (se 1 (by rfl) ⟨2827679, by rfl⟩ : syracuseStep 3770239 = 5655359) B5655359
theorem B5026985 : Blo 2233435 5026985 := bstep (se 2 (by rfl) ⟨1885119, by rfl⟩ : syracuseStep 5026985 = 3770239) B3770239
theorem B3351323 : Blo 2233435 3351323 := bstep (se 1 (by rfl) ⟨2513492, by rfl⟩ : syracuseStep 3351323 = 5026985) B5026985
theorem B2234215 : Blo 2233435 2234215 := bstep (se 1 (by rfl) ⟨1675661, by rfl⟩ : syracuseStep 2234215 = 3351323) B3351323
theorem B2513497 : Blo 2233435 2513497 := bbase (se 2 (by rfl) ⟨942561, by rfl⟩ : syracuseStep 2513497 = 1885123) (by norm_num)
theorem B3351329 : Blo 2233435 3351329 := bstep (se 2 (by rfl) ⟨1256748, by rfl⟩ : syracuseStep 3351329 = 2513497) B2513497
theorem B2234219 : Blo 2233435 2234219 := bstep (se 1 (by rfl) ⟨1675664, by rfl⟩ : syracuseStep 2234219 = 3351329) B3351329
theorem B3397061 : Blo 2233435 3397061 := bbase (se 4 (by rfl) ⟨318474, by rfl⟩ : syracuseStep 3397061 = 636949) (by norm_num)
theorem B2264707 : Blo 2233435 2264707 := bstep (se 1 (by rfl) ⟨1698530, by rfl⟩ : syracuseStep 2264707 = 3397061) B3397061
theorem B3019609 : Blo 2233435 3019609 := bstep (se 2 (by rfl) ⟨1132353, by rfl⟩ : syracuseStep 3019609 = 2264707) B2264707
theorem B16104581 : Blo 2233435 16104581 := bstep (se 4 (by rfl) ⟨1509804, by rfl⟩ : syracuseStep 16104581 = 3019609) B3019609
theorem B10736387 : Blo 2233435 10736387 := bstep (se 1 (by rfl) ⟨8052290, by rfl⟩ : syracuseStep 10736387 = 16104581) B16104581
theorem B7157591 : Blo 2233435 7157591 := bstep (se 1 (by rfl) ⟨5368193, by rfl⟩ : syracuseStep 7157591 = 10736387) B10736387
theorem B4771727 : Blo 2233435 4771727 := bstep (se 1 (by rfl) ⟨3578795, by rfl⟩ : syracuseStep 4771727 = 7157591) B7157591
theorem B3181151 : Blo 2233435 3181151 := bstep (se 1 (by rfl) ⟨2385863, by rfl⟩ : syracuseStep 3181151 = 4771727) B4771727
theorem B8483069 : Blo 2233435 8483069 := bstep (se 3 (by rfl) ⟨1590575, by rfl⟩ : syracuseStep 8483069 = 3181151) B3181151
theorem B5655379 : Blo 2233435 5655379 := bstep (se 1 (by rfl) ⟨4241534, by rfl⟩ : syracuseStep 5655379 = 8483069) B8483069
theorem B7540505 : Blo 2233435 7540505 := bstep (se 2 (by rfl) ⟨2827689, by rfl⟩ : syracuseStep 7540505 = 5655379) B5655379
theorem B5027003 : Blo 2233435 5027003 := bstep (se 1 (by rfl) ⟨3770252, by rfl⟩ : syracuseStep 5027003 = 7540505) B7540505
theorem B3351335 : Blo 2233435 3351335 := bstep (se 1 (by rfl) ⟨2513501, by rfl⟩ : syracuseStep 3351335 = 5027003) B5027003
theorem B2234223 : Blo 2233435 2234223 := bstep (se 1 (by rfl) ⟨1675667, by rfl⟩ : syracuseStep 2234223 = 3351335) B3351335
theorem B3351341 : Blo 2233435 3351341 := bbase (se 3 (by rfl) ⟨628376, by rfl⟩ : syracuseStep 3351341 = 1256753) (by norm_num)
theorem B2234227 : Blo 2233435 2234227 := bstep (se 1 (by rfl) ⟨1675670, by rfl⟩ : syracuseStep 2234227 = 3351341) B3351341
theorem B5027021 : Blo 2233435 5027021 := bbase (se 3 (by rfl) ⟨942566, by rfl⟩ : syracuseStep 5027021 = 1885133) (by norm_num)
theorem B3351347 : Blo 2233435 3351347 := bstep (se 1 (by rfl) ⟨2513510, by rfl⟩ : syracuseStep 3351347 = 5027021) B5027021
theorem B2234231 : Blo 2233435 2234231 := bstep (se 1 (by rfl) ⟨1675673, by rfl⟩ : syracuseStep 2234231 = 3351347) B3351347
theorem B2827705 : Blo 2233435 2827705 := bbase (se 2 (by rfl) ⟨1060389, by rfl⟩ : syracuseStep 2827705 = 2120779) (by norm_num)
theorem B3770273 : Blo 2233435 3770273 := bstep (se 2 (by rfl) ⟨1413852, by rfl⟩ : syracuseStep 3770273 = 2827705) B2827705
theorem B2513515 : Blo 2233435 2513515 := bstep (se 1 (by rfl) ⟨1885136, by rfl⟩ : syracuseStep 2513515 = 3770273) B3770273
theorem B3351353 : Blo 2233435 3351353 := bstep (se 2 (by rfl) ⟨1256757, by rfl⟩ : syracuseStep 3351353 = 2513515) B2513515
theorem B2234235 : Blo 2233435 2234235 := bstep (se 1 (by rfl) ⟨1675676, by rfl⟩ : syracuseStep 2234235 = 3351353) B3351353
theorem B10191253 : Blo 2233435 10191253 := bbase (se 6 (by rfl) ⟨238857, by rfl⟩ : syracuseStep 10191253 = 477715) (by norm_num)
theorem B13588337 : Blo 2233435 13588337 := bstep (se 2 (by rfl) ⟨5095626, by rfl⟩ : syracuseStep 13588337 = 10191253) B10191253
theorem B9058891 : Blo 2233435 9058891 := bstep (se 1 (by rfl) ⟨6794168, by rfl⟩ : syracuseStep 9058891 = 13588337) B13588337
theorem B12078521 : Blo 2233435 12078521 := bstep (se 2 (by rfl) ⟨4529445, by rfl⟩ : syracuseStep 12078521 = 9058891) B9058891
theorem B8052347 : Blo 2233435 8052347 := bstep (se 1 (by rfl) ⟨6039260, by rfl⟩ : syracuseStep 8052347 = 12078521) B12078521
theorem B5368231 : Blo 2233435 5368231 := bstep (se 1 (by rfl) ⟨4026173, by rfl⟩ : syracuseStep 5368231 = 8052347) B8052347
theorem B7157641 : Blo 2233435 7157641 := bstep (se 2 (by rfl) ⟨2684115, by rfl⟩ : syracuseStep 7157641 = 5368231) B5368231
theorem B9543521 : Blo 2233435 9543521 := bstep (se 2 (by rfl) ⟨3578820, by rfl⟩ : syracuseStep 9543521 = 7157641) B7157641
theorem B25449389 : Blo 2233435 25449389 := bstep (se 3 (by rfl) ⟨4771760, by rfl⟩ : syracuseStep 25449389 = 9543521) B9543521
theorem B16966259 : Blo 2233435 16966259 := bstep (se 1 (by rfl) ⟨12724694, by rfl⟩ : syracuseStep 16966259 = 25449389) B25449389
theorem B11310839 : Blo 2233435 11310839 := bstep (se 1 (by rfl) ⟨8483129, by rfl⟩ : syracuseStep 11310839 = 16966259) B16966259
theorem B7540559 : Blo 2233435 7540559 := bstep (se 1 (by rfl) ⟨5655419, by rfl⟩ : syracuseStep 7540559 = 11310839) B11310839
theorem B5027039 : Blo 2233435 5027039 := bstep (se 1 (by rfl) ⟨3770279, by rfl⟩ : syracuseStep 5027039 = 7540559) B7540559
theorem B3351359 : Blo 2233435 3351359 := bstep (se 1 (by rfl) ⟨2513519, by rfl⟩ : syracuseStep 3351359 = 5027039) B5027039
theorem B2234239 : Blo 2233435 2234239 := bstep (se 1 (by rfl) ⟨1675679, by rfl⟩ : syracuseStep 2234239 = 3351359) B3351359
theorem B3351365 : Blo 2233435 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B2234243 : Blo 2233435 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B3770293 : Blo 2233435 3770293 := bbase (se 5 (by rfl) ⟨176732, by rfl⟩ : syracuseStep 3770293 = 353465) (by norm_num)
theorem B5027057 : Blo 2233435 5027057 := bstep (se 2 (by rfl) ⟨1885146, by rfl⟩ : syracuseStep 5027057 = 3770293) B3770293
theorem B3351371 : Blo 2233435 3351371 := bstep (se 1 (by rfl) ⟨2513528, by rfl⟩ : syracuseStep 3351371 = 5027057) B5027057
theorem B2234247 : Blo 2233435 2234247 := bstep (se 1 (by rfl) ⟨1675685, by rfl⟩ : syracuseStep 2234247 = 3351371) B3351371
theorem B2513533 : Blo 2233435 2513533 := bbase (se 3 (by rfl) ⟨471287, by rfl⟩ : syracuseStep 2513533 = 942575) (by norm_num)
theorem B3351377 : Blo 2233435 3351377 := bstep (se 2 (by rfl) ⟨1256766, by rfl⟩ : syracuseStep 3351377 = 2513533) B2513533
theorem B2234251 : Blo 2233435 2234251 := bstep (se 1 (by rfl) ⟨1675688, by rfl⟩ : syracuseStep 2234251 = 3351377) B3351377
theorem B7540613 : Blo 2233435 7540613 := bbase (se 4 (by rfl) ⟨706932, by rfl⟩ : syracuseStep 7540613 = 1413865) (by norm_num)
theorem B5027075 : Blo 2233435 5027075 := bstep (se 1 (by rfl) ⟨3770306, by rfl⟩ : syracuseStep 5027075 = 7540613) B7540613
theorem B3351383 : Blo 2233435 3351383 := bstep (se 1 (by rfl) ⟨2513537, by rfl⟩ : syracuseStep 3351383 = 5027075) B5027075
theorem B2234255 : Blo 2233435 2234255 := bstep (se 1 (by rfl) ⟨1675691, by rfl⟩ : syracuseStep 2234255 = 3351383) B3351383
theorem B3351389 : Blo 2233435 3351389 := bbase (se 3 (by rfl) ⟨628385, by rfl⟩ : syracuseStep 3351389 = 1256771) (by norm_num)
theorem B2234259 : Blo 2233435 2234259 := bstep (se 1 (by rfl) ⟨1675694, by rfl⟩ : syracuseStep 2234259 = 3351389) B3351389
theorem B5027093 : Blo 2233435 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B3351395 : Blo 2233435 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B2234263 : Blo 2233435 2234263 := bstep (se 1 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 2234263 = 3351395) B3351395
theorem B8483237 : Blo 2233435 8483237 := bbase (se 4 (by rfl) ⟨795303, by rfl⟩ : syracuseStep 8483237 = 1590607) (by norm_num)
theorem B5655491 : Blo 2233435 5655491 := bstep (se 1 (by rfl) ⟨4241618, by rfl⟩ : syracuseStep 5655491 = 8483237) B8483237
theorem B3770327 : Blo 2233435 3770327 := bstep (se 1 (by rfl) ⟨2827745, by rfl⟩ : syracuseStep 3770327 = 5655491) B5655491
theorem B2513551 : Blo 2233435 2513551 := bstep (se 1 (by rfl) ⟨1885163, by rfl⟩ : syracuseStep 2513551 = 3770327) B3770327
theorem B3351401 : Blo 2233435 3351401 := bstep (se 2 (by rfl) ⟨1256775, by rfl⟩ : syracuseStep 3351401 = 2513551) B2513551
theorem B2234267 : Blo 2233435 2234267 := bstep (se 1 (by rfl) ⟨1675700, by rfl⟩ : syracuseStep 2234267 = 3351401) B3351401
theorem B4771829 : Blo 2233435 4771829 := bbase (se 5 (by rfl) ⟨223679, by rfl⟩ : syracuseStep 4771829 = 447359) (by norm_num)
theorem B12724877 : Blo 2233435 12724877 := bstep (se 3 (by rfl) ⟨2385914, by rfl⟩ : syracuseStep 12724877 = 4771829) B4771829
theorem B8483251 : Blo 2233435 8483251 := bstep (se 1 (by rfl) ⟨6362438, by rfl⟩ : syracuseStep 8483251 = 12724877) B12724877
theorem B11311001 : Blo 2233435 11311001 := bstep (se 2 (by rfl) ⟨4241625, by rfl⟩ : syracuseStep 11311001 = 8483251) B8483251
theorem B7540667 : Blo 2233435 7540667 := bstep (se 1 (by rfl) ⟨5655500, by rfl⟩ : syracuseStep 7540667 = 11311001) B11311001
theorem B5027111 : Blo 2233435 5027111 := bstep (se 1 (by rfl) ⟨3770333, by rfl⟩ : syracuseStep 5027111 = 7540667) B7540667
theorem B3351407 : Blo 2233435 3351407 := bstep (se 1 (by rfl) ⟨2513555, by rfl⟩ : syracuseStep 3351407 = 5027111) B5027111
theorem B2234271 : Blo 2233435 2234271 := bstep (se 1 (by rfl) ⟨1675703, by rfl⟩ : syracuseStep 2234271 = 3351407) B3351407
theorem B3351413 : Blo 2233435 3351413 := bbase (se 5 (by rfl) ⟨157097, by rfl⟩ : syracuseStep 3351413 = 314195) (by norm_num)
theorem B2234275 : Blo 2233435 2234275 := bstep (se 1 (by rfl) ⟨1675706, by rfl⟩ : syracuseStep 2234275 = 3351413) B3351413
theorem B3019685 : Blo 2233435 3019685 := bbase (se 4 (by rfl) ⟨283095, by rfl⟩ : syracuseStep 3019685 = 566191) (by norm_num)
theorem B8052493 : Blo 2233435 8052493 := bstep (se 3 (by rfl) ⟨1509842, by rfl⟩ : syracuseStep 8052493 = 3019685) B3019685
theorem B10736657 : Blo 2233435 10736657 := bstep (se 2 (by rfl) ⟨4026246, by rfl⟩ : syracuseStep 10736657 = 8052493) B8052493
theorem B7157771 : Blo 2233435 7157771 := bstep (se 1 (by rfl) ⟨5368328, by rfl⟩ : syracuseStep 7157771 = 10736657) B10736657
theorem B4771847 : Blo 2233435 4771847 := bstep (se 1 (by rfl) ⟨3578885, by rfl⟩ : syracuseStep 4771847 = 7157771) B7157771
theorem B3181231 : Blo 2233435 3181231 := bstep (se 1 (by rfl) ⟨2385923, by rfl⟩ : syracuseStep 3181231 = 4771847) B4771847
theorem B4241641 : Blo 2233435 4241641 := bstep (se 2 (by rfl) ⟨1590615, by rfl⟩ : syracuseStep 4241641 = 3181231) B3181231
theorem B5655521 : Blo 2233435 5655521 := bstep (se 2 (by rfl) ⟨2120820, by rfl⟩ : syracuseStep 5655521 = 4241641) B4241641
theorem B3770347 : Blo 2233435 3770347 := bstep (se 1 (by rfl) ⟨2827760, by rfl⟩ : syracuseStep 3770347 = 5655521) B5655521
theorem B5027129 : Blo 2233435 5027129 := bstep (se 2 (by rfl) ⟨1885173, by rfl⟩ : syracuseStep 5027129 = 3770347) B3770347
theorem B3351419 : Blo 2233435 3351419 := bstep (se 1 (by rfl) ⟨2513564, by rfl⟩ : syracuseStep 3351419 = 5027129) B5027129
theorem B2234279 : Blo 2233435 2234279 := bstep (se 1 (by rfl) ⟨1675709, by rfl⟩ : syracuseStep 2234279 = 3351419) B3351419
theorem B2513569 : Blo 2233435 2513569 := bbase (se 2 (by rfl) ⟨942588, by rfl⟩ : syracuseStep 2513569 = 1885177) (by norm_num)
theorem B3351425 : Blo 2233435 3351425 := bstep (se 2 (by rfl) ⟨1256784, by rfl⟩ : syracuseStep 3351425 = 2513569) B2513569
theorem B2234283 : Blo 2233435 2234283 := bstep (se 1 (by rfl) ⟨1675712, by rfl⟩ : syracuseStep 2234283 = 3351425) B3351425
theorem B5655541 : Blo 2233435 5655541 := bbase (se 5 (by rfl) ⟨265103, by rfl⟩ : syracuseStep 5655541 = 530207) (by norm_num)
theorem B7540721 : Blo 2233435 7540721 := bstep (se 2 (by rfl) ⟨2827770, by rfl⟩ : syracuseStep 7540721 = 5655541) B5655541
theorem B5027147 : Blo 2233435 5027147 := bstep (se 1 (by rfl) ⟨3770360, by rfl⟩ : syracuseStep 5027147 = 7540721) B7540721
theorem B3351431 : Blo 2233435 3351431 := bstep (se 1 (by rfl) ⟨2513573, by rfl⟩ : syracuseStep 3351431 = 5027147) B5027147
theorem B2234287 : Blo 2233435 2234287 := bstep (se 1 (by rfl) ⟨1675715, by rfl⟩ : syracuseStep 2234287 = 3351431) B3351431
theorem B3351437 : Blo 2233435 3351437 := bbase (se 3 (by rfl) ⟨628394, by rfl⟩ : syracuseStep 3351437 = 1256789) (by norm_num)
theorem B2234291 : Blo 2233435 2234291 := bstep (se 1 (by rfl) ⟨1675718, by rfl⟩ : syracuseStep 2234291 = 3351437) B3351437
theorem B5027165 : Blo 2233435 5027165 := bbase (se 3 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 5027165 = 1885187) (by norm_num)
theorem B3351443 : Blo 2233435 3351443 := bstep (se 1 (by rfl) ⟨2513582, by rfl⟩ : syracuseStep 3351443 = 5027165) B5027165
theorem B2234295 : Blo 2233435 2234295 := bstep (se 1 (by rfl) ⟨1675721, by rfl⟩ : syracuseStep 2234295 = 3351443) B3351443
theorem B3770381 : Blo 2233435 3770381 := bbase (se 3 (by rfl) ⟨706946, by rfl⟩ : syracuseStep 3770381 = 1413893) (by norm_num)
theorem B2513587 : Blo 2233435 2513587 := bstep (se 1 (by rfl) ⟨1885190, by rfl⟩ : syracuseStep 2513587 = 3770381) B3770381
theorem B3351449 : Blo 2233435 3351449 := bstep (se 2 (by rfl) ⟨1256793, by rfl⟩ : syracuseStep 3351449 = 2513587) B2513587
theorem B2234299 : Blo 2233435 2234299 := bstep (se 1 (by rfl) ⟨1675724, by rfl⟩ : syracuseStep 2234299 = 3351449) B3351449
theorem B3019717 : Blo 2233435 3019717 := bbase (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) (by norm_num)
theorem B4026289 : Blo 2233435 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B5368385 : Blo 2233435 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B3578923 : Blo 2233435 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B19087589 : Blo 2233435 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B12725059 : Blo 2233435 12725059 := bstep (se 1 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 12725059 = 19087589) B19087589
theorem B16966745 : Blo 2233435 16966745 := bstep (se 2 (by rfl) ⟨6362529, by rfl⟩ : syracuseStep 16966745 = 12725059) B12725059
theorem B11311163 : Blo 2233435 11311163 := bstep (se 1 (by rfl) ⟨8483372, by rfl⟩ : syracuseStep 11311163 = 16966745) B16966745
theorem B7540775 : Blo 2233435 7540775 := bstep (se 1 (by rfl) ⟨5655581, by rfl⟩ : syracuseStep 7540775 = 11311163) B11311163
theorem B5027183 : Blo 2233435 5027183 := bstep (se 1 (by rfl) ⟨3770387, by rfl⟩ : syracuseStep 5027183 = 7540775) B7540775
theorem B3351455 : Blo 2233435 3351455 := bstep (se 1 (by rfl) ⟨2513591, by rfl⟩ : syracuseStep 3351455 = 5027183) B5027183
theorem B2234303 : Blo 2233435 2234303 := bstep (se 1 (by rfl) ⟨1675727, by rfl⟩ : syracuseStep 2234303 = 3351455) B3351455
theorem B3351461 : Blo 2233435 3351461 := bbase (se 4 (by rfl) ⟨314199, by rfl⟩ : syracuseStep 3351461 = 628399) (by norm_num)
theorem B2234307 : Blo 2233435 2234307 := bstep (se 1 (by rfl) ⟨1675730, by rfl⟩ : syracuseStep 2234307 = 3351461) B3351461
theorem B2827801 : Blo 2233435 2827801 := bbase (se 2 (by rfl) ⟨1060425, by rfl⟩ : syracuseStep 2827801 = 2120851) (by norm_num)
theorem B3770401 : Blo 2233435 3770401 := bstep (se 2 (by rfl) ⟨1413900, by rfl⟩ : syracuseStep 3770401 = 2827801) B2827801
theorem B5027201 : Blo 2233435 5027201 := bstep (se 2 (by rfl) ⟨1885200, by rfl⟩ : syracuseStep 5027201 = 3770401) B3770401
theorem B3351467 : Blo 2233435 3351467 := bstep (se 1 (by rfl) ⟨2513600, by rfl⟩ : syracuseStep 3351467 = 5027201) B5027201
theorem B2234311 : Blo 2233435 2234311 := bstep (se 1 (by rfl) ⟨1675733, by rfl⟩ : syracuseStep 2234311 = 3351467) B3351467
theorem B2513605 : Blo 2233435 2513605 := bbase (se 4 (by rfl) ⟨235650, by rfl⟩ : syracuseStep 2513605 = 471301) (by norm_num)
theorem B3351473 : Blo 2233435 3351473 := bstep (se 2 (by rfl) ⟨1256802, by rfl⟩ : syracuseStep 3351473 = 2513605) B2513605
theorem B2234315 : Blo 2233435 2234315 := bstep (se 1 (by rfl) ⟨1675736, by rfl⟩ : syracuseStep 2234315 = 3351473) B3351473
theorem B4241717 : Blo 2233435 4241717 := bbase (se 5 (by rfl) ⟨198830, by rfl⟩ : syracuseStep 4241717 = 397661) (by norm_num)
theorem B2827811 : Blo 2233435 2827811 := bstep (se 1 (by rfl) ⟨2120858, by rfl⟩ : syracuseStep 2827811 = 4241717) B4241717
theorem B7540829 : Blo 2233435 7540829 := bstep (se 3 (by rfl) ⟨1413905, by rfl⟩ : syracuseStep 7540829 = 2827811) B2827811
theorem B5027219 : Blo 2233435 5027219 := bstep (se 1 (by rfl) ⟨3770414, by rfl⟩ : syracuseStep 5027219 = 7540829) B7540829
theorem B3351479 : Blo 2233435 3351479 := bstep (se 1 (by rfl) ⟨2513609, by rfl⟩ : syracuseStep 3351479 = 5027219) B5027219
theorem B2234319 : Blo 2233435 2234319 := bstep (se 1 (by rfl) ⟨1675739, by rfl⟩ : syracuseStep 2234319 = 3351479) B3351479
theorem B3351485 : Blo 2233435 3351485 := bbase (se 3 (by rfl) ⟨628403, by rfl⟩ : syracuseStep 3351485 = 1256807) (by norm_num)
theorem B2234323 : Blo 2233435 2234323 := bstep (se 1 (by rfl) ⟨1675742, by rfl⟩ : syracuseStep 2234323 = 3351485) B3351485
theorem B5027237 : Blo 2233435 5027237 := bbase (se 4 (by rfl) ⟨471303, by rfl⟩ : syracuseStep 5027237 = 942607) (by norm_num)
theorem B3351491 : Blo 2233435 3351491 := bstep (se 1 (by rfl) ⟨2513618, by rfl⟩ : syracuseStep 3351491 = 5027237) B5027237
theorem B2234327 : Blo 2233435 2234327 := bstep (se 1 (by rfl) ⟨1675745, by rfl⟩ : syracuseStep 2234327 = 3351491) B3351491
theorem B5655653 : Blo 2233435 5655653 := bbase (se 4 (by rfl) ⟨530217, by rfl⟩ : syracuseStep 5655653 = 1060435) (by norm_num)
theorem B3770435 : Blo 2233435 3770435 := bstep (se 1 (by rfl) ⟨2827826, by rfl⟩ : syracuseStep 3770435 = 5655653) B5655653
theorem B2513623 : Blo 2233435 2513623 := bstep (se 1 (by rfl) ⟨1885217, by rfl⟩ : syracuseStep 2513623 = 3770435) B3770435
theorem B3351497 : Blo 2233435 3351497 := bstep (se 2 (by rfl) ⟨1256811, by rfl⟩ : syracuseStep 3351497 = 2513623) B2513623
theorem B2234331 : Blo 2233435 2234331 := bstep (se 1 (by rfl) ⟨1675748, by rfl⟩ : syracuseStep 2234331 = 3351497) B3351497
theorem B9674149 : Blo 2233435 9674149 := bbase (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) (by norm_num)
theorem B12898865 : Blo 2233435 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B8599243 : Blo 2233435 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B11465657 : Blo 2233435 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B7643771 : Blo 2233435 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B5095847 : Blo 2233435 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B3397231 : Blo 2233435 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B18118565 : Blo 2233435 18118565 := bstep (se 4 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 18118565 = 3397231) B3397231
theorem B12079043 : Blo 2233435 12079043 := bstep (se 1 (by rfl) ⟨9059282, by rfl⟩ : syracuseStep 12079043 = 18118565) B18118565
theorem B8052695 : Blo 2233435 8052695 := bstep (se 1 (by rfl) ⟨6039521, by rfl⟩ : syracuseStep 8052695 = 12079043) B12079043
theorem B5368463 : Blo 2233435 5368463 := bstep (se 1 (by rfl) ⟨4026347, by rfl⟩ : syracuseStep 5368463 = 8052695) B8052695
theorem B3578975 : Blo 2233435 3578975 := bstep (se 1 (by rfl) ⟨2684231, by rfl⟩ : syracuseStep 3578975 = 5368463) B5368463
theorem B2385983 : Blo 2233435 2385983 := bstep (se 1 (by rfl) ⟨1789487, by rfl⟩ : syracuseStep 2385983 = 3578975) B3578975
theorem B6362621 : Blo 2233435 6362621 := bstep (se 3 (by rfl) ⟨1192991, by rfl⟩ : syracuseStep 6362621 = 2385983) B2385983
theorem B4241747 : Blo 2233435 4241747 := bstep (se 1 (by rfl) ⟨3181310, by rfl⟩ : syracuseStep 4241747 = 6362621) B6362621
theorem B11311325 : Blo 2233435 11311325 := bstep (se 3 (by rfl) ⟨2120873, by rfl⟩ : syracuseStep 11311325 = 4241747) B4241747
theorem B7540883 : Blo 2233435 7540883 := bstep (se 1 (by rfl) ⟨5655662, by rfl⟩ : syracuseStep 7540883 = 11311325) B11311325
theorem B5027255 : Blo 2233435 5027255 := bstep (se 1 (by rfl) ⟨3770441, by rfl⟩ : syracuseStep 5027255 = 7540883) B7540883
theorem B3351503 : Blo 2233435 3351503 := bstep (se 1 (by rfl) ⟨2513627, by rfl⟩ : syracuseStep 3351503 = 5027255) B5027255
theorem B2234335 : Blo 2233435 2234335 := bstep (se 1 (by rfl) ⟨1675751, by rfl⟩ : syracuseStep 2234335 = 3351503) B3351503
theorem B3351509 : Blo 2233435 3351509 := bbase (se 7 (by rfl) ⟨39275, by rfl⟩ : syracuseStep 3351509 = 78551) (by norm_num)
theorem B2234339 : Blo 2233435 2234339 := bstep (se 1 (by rfl) ⟨1675754, by rfl⟩ : syracuseStep 2234339 = 3351509) B3351509
theorem B8483525 : Blo 2233435 8483525 := bbase (se 4 (by rfl) ⟨795330, by rfl⟩ : syracuseStep 8483525 = 1590661) (by norm_num)
theorem B5655683 : Blo 2233435 5655683 := bstep (se 1 (by rfl) ⟨4241762, by rfl⟩ : syracuseStep 5655683 = 8483525) B8483525
theorem B3770455 : Blo 2233435 3770455 := bstep (se 1 (by rfl) ⟨2827841, by rfl⟩ : syracuseStep 3770455 = 5655683) B5655683
theorem B5027273 : Blo 2233435 5027273 := bstep (se 2 (by rfl) ⟨1885227, by rfl⟩ : syracuseStep 5027273 = 3770455) B3770455
theorem B3351515 : Blo 2233435 3351515 := bstep (se 1 (by rfl) ⟨2513636, by rfl⟩ : syracuseStep 3351515 = 5027273) B5027273
theorem B2234343 : Blo 2233435 2234343 := bstep (se 1 (by rfl) ⟨1675757, by rfl⟩ : syracuseStep 2234343 = 3351515) B3351515
theorem B2513641 : Blo 2233435 2513641 := bbase (se 2 (by rfl) ⟨942615, by rfl⟩ : syracuseStep 2513641 = 1885231) (by norm_num)
theorem B3351521 : Blo 2233435 3351521 := bstep (se 2 (by rfl) ⟨1256820, by rfl⟩ : syracuseStep 3351521 = 2513641) B2513641
theorem B2234347 : Blo 2233435 2234347 := bstep (se 1 (by rfl) ⟨1675760, by rfl⟩ : syracuseStep 2234347 = 3351521) B3351521
theorem B12725333 : Blo 2233435 12725333 := bbase (se 8 (by rfl) ⟨74562, by rfl⟩ : syracuseStep 12725333 = 149125) (by norm_num)
theorem B8483555 : Blo 2233435 8483555 := bstep (se 1 (by rfl) ⟨6362666, by rfl⟩ : syracuseStep 8483555 = 12725333) B12725333
theorem B5655703 : Blo 2233435 5655703 := bstep (se 1 (by rfl) ⟨4241777, by rfl⟩ : syracuseStep 5655703 = 8483555) B8483555
theorem B7540937 : Blo 2233435 7540937 := bstep (se 2 (by rfl) ⟨2827851, by rfl⟩ : syracuseStep 7540937 = 5655703) B5655703
theorem B5027291 : Blo 2233435 5027291 := bstep (se 1 (by rfl) ⟨3770468, by rfl⟩ : syracuseStep 5027291 = 7540937) B7540937
theorem B3351527 : Blo 2233435 3351527 := bstep (se 1 (by rfl) ⟨2513645, by rfl⟩ : syracuseStep 3351527 = 5027291) B5027291
theorem B2234351 : Blo 2233435 2234351 := bstep (se 1 (by rfl) ⟨1675763, by rfl⟩ : syracuseStep 2234351 = 3351527) B3351527
theorem B3351533 : Blo 2233435 3351533 := bbase (se 3 (by rfl) ⟨628412, by rfl⟩ : syracuseStep 3351533 = 1256825) (by norm_num)
theorem B2234355 : Blo 2233435 2234355 := bstep (se 1 (by rfl) ⟨1675766, by rfl⟩ : syracuseStep 2234355 = 3351533) B3351533
theorem B5027309 : Blo 2233435 5027309 := bbase (se 3 (by rfl) ⟨942620, by rfl⟩ : syracuseStep 5027309 = 1885241) (by norm_num)
theorem B3351539 : Blo 2233435 3351539 := bstep (se 1 (by rfl) ⟨2513654, by rfl⟩ : syracuseStep 3351539 = 5027309) B5027309
theorem B2234359 : Blo 2233435 2234359 := bstep (se 1 (by rfl) ⟨1675769, by rfl⟩ : syracuseStep 2234359 = 3351539) B3351539
theorem B6794549 : Blo 2233435 6794549 := bbase (se 5 (by rfl) ⟨318494, by rfl⟩ : syracuseStep 6794549 = 636989) (by norm_num)
theorem B4529699 : Blo 2233435 4529699 := bstep (se 1 (by rfl) ⟨3397274, by rfl⟩ : syracuseStep 4529699 = 6794549) B6794549
theorem B3019799 : Blo 2233435 3019799 := bstep (se 1 (by rfl) ⟨2264849, by rfl⟩ : syracuseStep 3019799 = 4529699) B4529699
theorem B8052797 : Blo 2233435 8052797 := bstep (se 3 (by rfl) ⟨1509899, by rfl⟩ : syracuseStep 8052797 = 3019799) B3019799
theorem B5368531 : Blo 2233435 5368531 := bstep (se 1 (by rfl) ⟨4026398, by rfl⟩ : syracuseStep 5368531 = 8052797) B8052797
theorem B7158041 : Blo 2233435 7158041 := bstep (se 2 (by rfl) ⟨2684265, by rfl⟩ : syracuseStep 7158041 = 5368531) B5368531
theorem B4772027 : Blo 2233435 4772027 := bstep (se 1 (by rfl) ⟨3579020, by rfl⟩ : syracuseStep 4772027 = 7158041) B7158041
theorem B3181351 : Blo 2233435 3181351 := bstep (se 1 (by rfl) ⟨2386013, by rfl⟩ : syracuseStep 3181351 = 4772027) B4772027
theorem B4241801 : Blo 2233435 4241801 := bstep (se 2 (by rfl) ⟨1590675, by rfl⟩ : syracuseStep 4241801 = 3181351) B3181351
theorem B2827867 : Blo 2233435 2827867 := bstep (se 1 (by rfl) ⟨2120900, by rfl⟩ : syracuseStep 2827867 = 4241801) B4241801
theorem B3770489 : Blo 2233435 3770489 := bstep (se 2 (by rfl) ⟨1413933, by rfl⟩ : syracuseStep 3770489 = 2827867) B2827867
theorem B2513659 : Blo 2233435 2513659 := bstep (se 1 (by rfl) ⟨1885244, by rfl⟩ : syracuseStep 2513659 = 3770489) B3770489
theorem B3351545 : Blo 2233435 3351545 := bstep (se 2 (by rfl) ⟨1256829, by rfl⟩ : syracuseStep 3351545 = 2513659) B2513659
theorem B2234363 : Blo 2233435 2234363 := bstep (se 1 (by rfl) ⟨1675772, by rfl⟩ : syracuseStep 2234363 = 3351545) B3351545
theorem B4837141 : Blo 2233435 4837141 := bbase (se 6 (by rfl) ⟨113370, by rfl⟩ : syracuseStep 4837141 = 226741) (by norm_num)
theorem B25798085 : Blo 2233435 25798085 := bstep (se 4 (by rfl) ⟨2418570, by rfl⟩ : syracuseStep 25798085 = 4837141) B4837141
theorem B17198723 : Blo 2233435 17198723 := bstep (se 1 (by rfl) ⟨12899042, by rfl⟩ : syracuseStep 17198723 = 25798085) B25798085
theorem B11465815 : Blo 2233435 11465815 := bstep (se 1 (by rfl) ⟨8599361, by rfl⟩ : syracuseStep 11465815 = 17198723) B17198723
theorem B15287753 : Blo 2233435 15287753 := bstep (se 2 (by rfl) ⟨5732907, by rfl⟩ : syracuseStep 15287753 = 11465815) B11465815
theorem B10191835 : Blo 2233435 10191835 := bstep (se 1 (by rfl) ⟨7643876, by rfl⟩ : syracuseStep 10191835 = 15287753) B15287753
theorem B13589113 : Blo 2233435 13589113 := bstep (se 2 (by rfl) ⟨5095917, by rfl⟩ : syracuseStep 13589113 = 10191835) B10191835
theorem B18118817 : Blo 2233435 18118817 := bstep (se 2 (by rfl) ⟨6794556, by rfl⟩ : syracuseStep 18118817 = 13589113) B13589113
theorem B12079211 : Blo 2233435 12079211 := bstep (se 1 (by rfl) ⟨9059408, by rfl⟩ : syracuseStep 12079211 = 18118817) B18118817
theorem B128844917 : Blo 2233435 128844917 := bstep (se 5 (by rfl) ⟨6039605, by rfl⟩ : syracuseStep 128844917 = 12079211) B12079211
theorem B85896611 : Blo 2233435 85896611 := bstep (se 1 (by rfl) ⟨64422458, by rfl⟩ : syracuseStep 85896611 = 128844917) B128844917
theorem B57264407 : Blo 2233435 57264407 := bstep (se 1 (by rfl) ⟨42948305, by rfl⟩ : syracuseStep 57264407 = 85896611) B85896611
theorem B38176271 : Blo 2233435 38176271 := bstep (se 1 (by rfl) ⟨28632203, by rfl⟩ : syracuseStep 38176271 = 57264407) B57264407
theorem B25450847 : Blo 2233435 25450847 := bstep (se 1 (by rfl) ⟨19088135, by rfl⟩ : syracuseStep 25450847 = 38176271) B38176271
theorem B16967231 : Blo 2233435 16967231 := bstep (se 1 (by rfl) ⟨12725423, by rfl⟩ : syracuseStep 16967231 = 25450847) B25450847
theorem B11311487 : Blo 2233435 11311487 := bstep (se 1 (by rfl) ⟨8483615, by rfl⟩ : syracuseStep 11311487 = 16967231) B16967231
theorem B7540991 : Blo 2233435 7540991 := bstep (se 1 (by rfl) ⟨5655743, by rfl⟩ : syracuseStep 7540991 = 11311487) B11311487
theorem B5027327 : Blo 2233435 5027327 := bstep (se 1 (by rfl) ⟨3770495, by rfl⟩ : syracuseStep 5027327 = 7540991) B7540991
theorem B3351551 : Blo 2233435 3351551 := bstep (se 1 (by rfl) ⟨2513663, by rfl⟩ : syracuseStep 3351551 = 5027327) B5027327
theorem B2234367 : Blo 2233435 2234367 := bstep (se 1 (by rfl) ⟨1675775, by rfl⟩ : syracuseStep 2234367 = 3351551) B3351551
theorem B3351557 : Blo 2233435 3351557 := bbase (se 4 (by rfl) ⟨314208, by rfl⟩ : syracuseStep 3351557 = 628417) (by norm_num)
theorem B2234371 : Blo 2233435 2234371 := bstep (se 1 (by rfl) ⟨1675778, by rfl⟩ : syracuseStep 2234371 = 3351557) B3351557
theorem B3770509 : Blo 2233435 3770509 := bbase (se 3 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 3770509 = 1413941) (by norm_num)
theorem B5027345 : Blo 2233435 5027345 := bstep (se 2 (by rfl) ⟨1885254, by rfl⟩ : syracuseStep 5027345 = 3770509) B3770509
theorem B3351563 : Blo 2233435 3351563 := bstep (se 1 (by rfl) ⟨2513672, by rfl⟩ : syracuseStep 3351563 = 5027345) B5027345
theorem B2234375 : Blo 2233435 2234375 := bstep (se 1 (by rfl) ⟨1675781, by rfl⟩ : syracuseStep 2234375 = 3351563) B3351563
theorem B2513677 : Blo 2233435 2513677 := bbase (se 3 (by rfl) ⟨471314, by rfl⟩ : syracuseStep 2513677 = 942629) (by norm_num)
theorem B3351569 : Blo 2233435 3351569 := bstep (se 2 (by rfl) ⟨1256838, by rfl⟩ : syracuseStep 3351569 = 2513677) B2513677
theorem B2234379 : Blo 2233435 2234379 := bstep (se 1 (by rfl) ⟨1675784, by rfl⟩ : syracuseStep 2234379 = 3351569) B3351569
theorem B7541045 : Blo 2233435 7541045 := bbase (se 5 (by rfl) ⟨353486, by rfl⟩ : syracuseStep 7541045 = 706973) (by norm_num)
theorem B5027363 : Blo 2233435 5027363 := bstep (se 1 (by rfl) ⟨3770522, by rfl⟩ : syracuseStep 5027363 = 7541045) B7541045
theorem B3351575 : Blo 2233435 3351575 := bstep (se 1 (by rfl) ⟨2513681, by rfl⟩ : syracuseStep 3351575 = 5027363) B5027363
theorem B2234383 : Blo 2233435 2234383 := bstep (se 1 (by rfl) ⟨1675787, by rfl⟩ : syracuseStep 2234383 = 3351575) B3351575
theorem B3351581 : Blo 2233435 3351581 := bbase (se 3 (by rfl) ⟨628421, by rfl⟩ : syracuseStep 3351581 = 1256843) (by norm_num)
theorem B2234387 : Blo 2233435 2234387 := bstep (se 1 (by rfl) ⟨1675790, by rfl⟩ : syracuseStep 2234387 = 3351581) B3351581
theorem B5027381 : Blo 2233435 5027381 := bbase (se 5 (by rfl) ⟨235658, by rfl⟩ : syracuseStep 5027381 = 471317) (by norm_num)
theorem B3351587 : Blo 2233435 3351587 := bstep (se 1 (by rfl) ⟨2513690, by rfl⟩ : syracuseStep 3351587 = 5027381) B5027381
theorem B2234391 : Blo 2233435 2234391 := bstep (se 1 (by rfl) ⟨1675793, by rfl⟩ : syracuseStep 2234391 = 3351587) B3351587
theorem B3874133 : Blo 2233435 3874133 := bbase (se 11 (by rfl) ⟨2837, by rfl⟩ : syracuseStep 3874133 = 5675) (by norm_num)
theorem B10331021 : Blo 2233435 10331021 := bstep (se 3 (by rfl) ⟨1937066, by rfl⟩ : syracuseStep 10331021 = 3874133) B3874133
theorem B27549389 : Blo 2233435 27549389 := bstep (se 3 (by rfl) ⟨5165510, by rfl⟩ : syracuseStep 27549389 = 10331021) B10331021
theorem B18366259 : Blo 2233435 18366259 := bstep (se 1 (by rfl) ⟨13774694, by rfl⟩ : syracuseStep 18366259 = 27549389) B27549389
theorem B24488345 : Blo 2233435 24488345 := bstep (se 2 (by rfl) ⟨9183129, by rfl⟩ : syracuseStep 24488345 = 18366259) B18366259
theorem B16325563 : Blo 2233435 16325563 := bstep (se 1 (by rfl) ⟨12244172, by rfl⟩ : syracuseStep 16325563 = 24488345) B24488345
theorem B21767417 : Blo 2233435 21767417 := bstep (se 2 (by rfl) ⟨8162781, by rfl⟩ : syracuseStep 21767417 = 16325563) B16325563
theorem B14511611 : Blo 2233435 14511611 := bstep (se 1 (by rfl) ⟨10883708, by rfl⟩ : syracuseStep 14511611 = 21767417) B21767417
theorem B9674407 : Blo 2233435 9674407 := bstep (se 1 (by rfl) ⟨7255805, by rfl⟩ : syracuseStep 9674407 = 14511611) B14511611
theorem B12899209 : Blo 2233435 12899209 := bstep (se 2 (by rfl) ⟨4837203, by rfl⟩ : syracuseStep 12899209 = 9674407) B9674407
theorem B17198945 : Blo 2233435 17198945 := bstep (se 2 (by rfl) ⟨6449604, by rfl⟩ : syracuseStep 17198945 = 12899209) B12899209
theorem B11465963 : Blo 2233435 11465963 := bstep (se 1 (by rfl) ⟨8599472, by rfl⟩ : syracuseStep 11465963 = 17198945) B17198945
theorem B7643975 : Blo 2233435 7643975 := bstep (se 1 (by rfl) ⟨5732981, by rfl⟩ : syracuseStep 7643975 = 11465963) B11465963
theorem B20383933 : Blo 2233435 20383933 := bstep (se 3 (by rfl) ⟨3821987, by rfl⟩ : syracuseStep 20383933 = 7643975) B7643975
theorem B27178577 : Blo 2233435 27178577 := bstep (se 2 (by rfl) ⟨10191966, by rfl⟩ : syracuseStep 27178577 = 20383933) B20383933
theorem B18119051 : Blo 2233435 18119051 := bstep (se 1 (by rfl) ⟨13589288, by rfl⟩ : syracuseStep 18119051 = 27178577) B27178577
theorem B12079367 : Blo 2233435 12079367 := bstep (se 1 (by rfl) ⟨9059525, by rfl⟩ : syracuseStep 12079367 = 18119051) B18119051
theorem B8052911 : Blo 2233435 8052911 := bstep (se 1 (by rfl) ⟨6039683, by rfl⟩ : syracuseStep 8052911 = 12079367) B12079367
theorem B5368607 : Blo 2233435 5368607 := bstep (se 1 (by rfl) ⟨4026455, by rfl⟩ : syracuseStep 5368607 = 8052911) B8052911
theorem B3579071 : Blo 2233435 3579071 := bstep (se 1 (by rfl) ⟨2684303, by rfl⟩ : syracuseStep 3579071 = 5368607) B5368607
theorem B9544189 : Blo 2233435 9544189 := bstep (se 3 (by rfl) ⟨1789535, by rfl⟩ : syracuseStep 9544189 = 3579071) B3579071
theorem B12725585 : Blo 2233435 12725585 := bstep (se 2 (by rfl) ⟨4772094, by rfl⟩ : syracuseStep 12725585 = 9544189) B9544189
theorem B8483723 : Blo 2233435 8483723 := bstep (se 1 (by rfl) ⟨6362792, by rfl⟩ : syracuseStep 8483723 = 12725585) B12725585
theorem B5655815 : Blo 2233435 5655815 := bstep (se 1 (by rfl) ⟨4241861, by rfl⟩ : syracuseStep 5655815 = 8483723) B8483723
theorem B3770543 : Blo 2233435 3770543 := bstep (se 1 (by rfl) ⟨2827907, by rfl⟩ : syracuseStep 3770543 = 5655815) B5655815
theorem B2513695 : Blo 2233435 2513695 := bstep (se 1 (by rfl) ⟨1885271, by rfl⟩ : syracuseStep 2513695 = 3770543) B3770543
theorem B3351593 : Blo 2233435 3351593 := bstep (se 2 (by rfl) ⟨1256847, by rfl⟩ : syracuseStep 3351593 = 2513695) B2513695
theorem B2234395 : Blo 2233435 2234395 := bstep (se 1 (by rfl) ⟨1675796, by rfl⟩ : syracuseStep 2234395 = 3351593) B3351593
theorem B3579077 : Blo 2233435 3579077 := bbase (se 4 (by rfl) ⟨335538, by rfl⟩ : syracuseStep 3579077 = 671077) (by norm_num)
theorem B9544205 : Blo 2233435 9544205 := bstep (se 3 (by rfl) ⟨1789538, by rfl⟩ : syracuseStep 9544205 = 3579077) B3579077
theorem B6362803 : Blo 2233435 6362803 := bstep (se 1 (by rfl) ⟨4772102, by rfl⟩ : syracuseStep 6362803 = 9544205) B9544205
theorem B8483737 : Blo 2233435 8483737 := bstep (se 2 (by rfl) ⟨3181401, by rfl⟩ : syracuseStep 8483737 = 6362803) B6362803
theorem B11311649 : Blo 2233435 11311649 := bstep (se 2 (by rfl) ⟨4241868, by rfl⟩ : syracuseStep 11311649 = 8483737) B8483737
theorem B7541099 : Blo 2233435 7541099 := bstep (se 1 (by rfl) ⟨5655824, by rfl⟩ : syracuseStep 7541099 = 11311649) B11311649
theorem B5027399 : Blo 2233435 5027399 := bstep (se 1 (by rfl) ⟨3770549, by rfl⟩ : syracuseStep 5027399 = 7541099) B7541099
theorem B3351599 : Blo 2233435 3351599 := bstep (se 1 (by rfl) ⟨2513699, by rfl⟩ : syracuseStep 3351599 = 5027399) B5027399
theorem B2234399 : Blo 2233435 2234399 := bstep (se 1 (by rfl) ⟨1675799, by rfl⟩ : syracuseStep 2234399 = 3351599) B3351599
theorem B3351605 : Blo 2233435 3351605 := bbase (se 5 (by rfl) ⟨157106, by rfl⟩ : syracuseStep 3351605 = 314213) (by norm_num)
theorem B2234403 : Blo 2233435 2234403 := bstep (se 1 (by rfl) ⟨1675802, by rfl⟩ : syracuseStep 2234403 = 3351605) B3351605
theorem B5655845 : Blo 2233435 5655845 := bbase (se 4 (by rfl) ⟨530235, by rfl⟩ : syracuseStep 5655845 = 1060471) (by norm_num)
theorem B3770563 : Blo 2233435 3770563 := bstep (se 1 (by rfl) ⟨2827922, by rfl⟩ : syracuseStep 3770563 = 5655845) B5655845
theorem B5027417 : Blo 2233435 5027417 := bstep (se 2 (by rfl) ⟨1885281, by rfl⟩ : syracuseStep 5027417 = 3770563) B3770563
theorem B3351611 : Blo 2233435 3351611 := bstep (se 1 (by rfl) ⟨2513708, by rfl⟩ : syracuseStep 3351611 = 5027417) B5027417
theorem B2234407 : Blo 2233435 2234407 := bstep (se 1 (by rfl) ⟨1675805, by rfl⟩ : syracuseStep 2234407 = 3351611) B3351611
theorem B2513713 : Blo 2233435 2513713 := bbase (se 2 (by rfl) ⟨942642, by rfl⟩ : syracuseStep 2513713 = 1885285) (by norm_num)
theorem B3351617 : Blo 2233435 3351617 := bstep (se 2 (by rfl) ⟨1256856, by rfl⟩ : syracuseStep 3351617 = 2513713) B2513713
theorem B2234411 : Blo 2233435 2234411 := bstep (se 1 (by rfl) ⟨1675808, by rfl⟩ : syracuseStep 2234411 = 3351617) B3351617
theorem B5096029 : Blo 2233435 5096029 := bbase (se 3 (by rfl) ⟨955505, by rfl⟩ : syracuseStep 5096029 = 1911011) (by norm_num)
theorem B6794705 : Blo 2233435 6794705 := bstep (se 2 (by rfl) ⟨2548014, by rfl⟩ : syracuseStep 6794705 = 5096029) B5096029
theorem B18119213 : Blo 2233435 18119213 := bstep (se 3 (by rfl) ⟨3397352, by rfl⟩ : syracuseStep 18119213 = 6794705) B6794705
theorem B12079475 : Blo 2233435 12079475 := bstep (se 1 (by rfl) ⟨9059606, by rfl⟩ : syracuseStep 12079475 = 18119213) B18119213
theorem B8052983 : Blo 2233435 8052983 := bstep (se 1 (by rfl) ⟨6039737, by rfl⟩ : syracuseStep 8052983 = 12079475) B12079475
theorem B5368655 : Blo 2233435 5368655 := bstep (se 1 (by rfl) ⟨4026491, by rfl⟩ : syracuseStep 5368655 = 8052983) B8052983
theorem B3579103 : Blo 2233435 3579103 := bstep (se 1 (by rfl) ⟨2684327, by rfl⟩ : syracuseStep 3579103 = 5368655) B5368655
theorem B4772137 : Blo 2233435 4772137 := bstep (se 2 (by rfl) ⟨1789551, by rfl⟩ : syracuseStep 4772137 = 3579103) B3579103
theorem B6362849 : Blo 2233435 6362849 := bstep (se 2 (by rfl) ⟨2386068, by rfl⟩ : syracuseStep 6362849 = 4772137) B4772137
theorem B4241899 : Blo 2233435 4241899 := bstep (se 1 (by rfl) ⟨3181424, by rfl⟩ : syracuseStep 4241899 = 6362849) B6362849
theorem B5655865 : Blo 2233435 5655865 := bstep (se 2 (by rfl) ⟨2120949, by rfl⟩ : syracuseStep 5655865 = 4241899) B4241899
theorem B7541153 : Blo 2233435 7541153 := bstep (se 2 (by rfl) ⟨2827932, by rfl⟩ : syracuseStep 7541153 = 5655865) B5655865
theorem B5027435 : Blo 2233435 5027435 := bstep (se 1 (by rfl) ⟨3770576, by rfl⟩ : syracuseStep 5027435 = 7541153) B7541153
theorem B3351623 : Blo 2233435 3351623 := bstep (se 1 (by rfl) ⟨2513717, by rfl⟩ : syracuseStep 3351623 = 5027435) B5027435
theorem B2234415 : Blo 2233435 2234415 := bstep (se 1 (by rfl) ⟨1675811, by rfl⟩ : syracuseStep 2234415 = 3351623) B3351623
theorem B3351629 : Blo 2233435 3351629 := bbase (se 3 (by rfl) ⟨628430, by rfl⟩ : syracuseStep 3351629 = 1256861) (by norm_num)
theorem B2234419 : Blo 2233435 2234419 := bstep (se 1 (by rfl) ⟨1675814, by rfl⟩ : syracuseStep 2234419 = 3351629) B3351629
theorem B5027453 : Blo 2233435 5027453 := bbase (se 3 (by rfl) ⟨942647, by rfl⟩ : syracuseStep 5027453 = 1885295) (by norm_num)
theorem B3351635 : Blo 2233435 3351635 := bstep (se 1 (by rfl) ⟨2513726, by rfl⟩ : syracuseStep 3351635 = 5027453) B5027453
theorem B2234423 : Blo 2233435 2234423 := bstep (se 1 (by rfl) ⟨1675817, by rfl⟩ : syracuseStep 2234423 = 3351635) B3351635
theorem B3770597 : Blo 2233435 3770597 := bbase (se 4 (by rfl) ⟨353493, by rfl⟩ : syracuseStep 3770597 = 706987) (by norm_num)
theorem B2513731 : Blo 2233435 2513731 := bstep (se 1 (by rfl) ⟨1885298, by rfl⟩ : syracuseStep 2513731 = 3770597) B3770597
theorem B3351641 : Blo 2233435 3351641 := bstep (se 2 (by rfl) ⟨1256865, by rfl⟩ : syracuseStep 3351641 = 2513731) B2513731
theorem B2234427 : Blo 2233435 2234427 := bstep (se 1 (by rfl) ⟨1675820, by rfl⟩ : syracuseStep 2234427 = 3351641) B3351641
theorem B5368693 : Blo 2233435 5368693 := bbase (se 5 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 5368693 = 503315) (by norm_num)
theorem B7158257 : Blo 2233435 7158257 := bstep (se 2 (by rfl) ⟨2684346, by rfl⟩ : syracuseStep 7158257 = 5368693) B5368693
theorem B4772171 : Blo 2233435 4772171 := bstep (se 1 (by rfl) ⟨3579128, by rfl⟩ : syracuseStep 4772171 = 7158257) B7158257
theorem B3181447 : Blo 2233435 3181447 := bstep (se 1 (by rfl) ⟨2386085, by rfl⟩ : syracuseStep 3181447 = 4772171) B4772171
theorem B16967717 : Blo 2233435 16967717 := bstep (se 4 (by rfl) ⟨1590723, by rfl⟩ : syracuseStep 16967717 = 3181447) B3181447
theorem B11311811 : Blo 2233435 11311811 := bstep (se 1 (by rfl) ⟨8483858, by rfl⟩ : syracuseStep 11311811 = 16967717) B16967717
theorem B7541207 : Blo 2233435 7541207 := bstep (se 1 (by rfl) ⟨5655905, by rfl⟩ : syracuseStep 7541207 = 11311811) B11311811
theorem B5027471 : Blo 2233435 5027471 := bstep (se 1 (by rfl) ⟨3770603, by rfl⟩ : syracuseStep 5027471 = 7541207) B7541207
theorem B3351647 : Blo 2233435 3351647 := bstep (se 1 (by rfl) ⟨2513735, by rfl⟩ : syracuseStep 3351647 = 5027471) B5027471
theorem B2234431 : Blo 2233435 2234431 := bstep (se 1 (by rfl) ⟨1675823, by rfl⟩ : syracuseStep 2234431 = 3351647) B3351647
theorem B3351653 : Blo 2233435 3351653 := bbase (se 4 (by rfl) ⟨314217, by rfl⟩ : syracuseStep 3351653 = 628435) (by norm_num)
theorem B2234435 : Blo 2233435 2234435 := bstep (se 1 (by rfl) ⟨1675826, by rfl⟩ : syracuseStep 2234435 = 3351653) B3351653
theorem B4772189 : Blo 2233435 4772189 := bbase (se 3 (by rfl) ⟨894785, by rfl⟩ : syracuseStep 4772189 = 1789571) (by norm_num)
theorem B3181459 : Blo 2233435 3181459 := bstep (se 1 (by rfl) ⟨2386094, by rfl⟩ : syracuseStep 3181459 = 4772189) B4772189
theorem B4241945 : Blo 2233435 4241945 := bstep (se 2 (by rfl) ⟨1590729, by rfl⟩ : syracuseStep 4241945 = 3181459) B3181459
theorem B2827963 : Blo 2233435 2827963 := bstep (se 1 (by rfl) ⟨2120972, by rfl⟩ : syracuseStep 2827963 = 4241945) B4241945
theorem B3770617 : Blo 2233435 3770617 := bstep (se 2 (by rfl) ⟨1413981, by rfl⟩ : syracuseStep 3770617 = 2827963) B2827963
theorem B5027489 : Blo 2233435 5027489 := bstep (se 2 (by rfl) ⟨1885308, by rfl⟩ : syracuseStep 5027489 = 3770617) B3770617
theorem B3351659 : Blo 2233435 3351659 := bstep (se 1 (by rfl) ⟨2513744, by rfl⟩ : syracuseStep 3351659 = 5027489) B5027489
theorem B2234439 : Blo 2233435 2234439 := bstep (se 1 (by rfl) ⟨1675829, by rfl⟩ : syracuseStep 2234439 = 3351659) B3351659
theorem B2513749 : Blo 2233435 2513749 := bbase (se 9 (by rfl) ⟨7364, by rfl⟩ : syracuseStep 2513749 = 14729) (by norm_num)
theorem B3351665 : Blo 2233435 3351665 := bstep (se 2 (by rfl) ⟨1256874, by rfl⟩ : syracuseStep 3351665 = 2513749) B2513749
theorem B2234443 : Blo 2233435 2234443 := bstep (se 1 (by rfl) ⟨1675832, by rfl⟩ : syracuseStep 2234443 = 3351665) B3351665
theorem B2827973 : Blo 2233435 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B7541261 : Blo 2233435 7541261 := bstep (se 3 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 7541261 = 2827973) B2827973
theorem B5027507 : Blo 2233435 5027507 := bstep (se 1 (by rfl) ⟨3770630, by rfl⟩ : syracuseStep 5027507 = 7541261) B7541261
theorem B3351671 : Blo 2233435 3351671 := bstep (se 1 (by rfl) ⟨2513753, by rfl⟩ : syracuseStep 3351671 = 5027507) B5027507
theorem B2234447 : Blo 2233435 2234447 := bstep (se 1 (by rfl) ⟨1675835, by rfl⟩ : syracuseStep 2234447 = 3351671) B3351671
theorem B3351677 : Blo 2233435 3351677 := bbase (se 3 (by rfl) ⟨628439, by rfl⟩ : syracuseStep 3351677 = 1256879) (by norm_num)
theorem B2234451 : Blo 2233435 2234451 := bstep (se 1 (by rfl) ⟨1675838, by rfl⟩ : syracuseStep 2234451 = 3351677) B3351677
theorem B5027525 : Blo 2233435 5027525 := bbase (se 4 (by rfl) ⟨471330, by rfl⟩ : syracuseStep 5027525 = 942661) (by norm_num)
theorem B3351683 : Blo 2233435 3351683 := bstep (se 1 (by rfl) ⟨2513762, by rfl⟩ : syracuseStep 3351683 = 5027525) B5027525
theorem B2234455 : Blo 2233435 2234455 := bstep (se 1 (by rfl) ⟨1675841, by rfl⟩ : syracuseStep 2234455 = 3351683) B3351683
theorem B32212565 : Blo 2233435 32212565 := bbase (se 8 (by rfl) ⟨188745, by rfl⟩ : syracuseStep 32212565 = 377491) (by norm_num)
theorem B21475043 : Blo 2233435 21475043 := bstep (se 1 (by rfl) ⟨16106282, by rfl⟩ : syracuseStep 21475043 = 32212565) B32212565
theorem B14316695 : Blo 2233435 14316695 := bstep (se 1 (by rfl) ⟨10737521, by rfl⟩ : syracuseStep 14316695 = 21475043) B21475043
theorem B9544463 : Blo 2233435 9544463 := bstep (se 1 (by rfl) ⟨7158347, by rfl⟩ : syracuseStep 9544463 = 14316695) B14316695
theorem B6362975 : Blo 2233435 6362975 := bstep (se 1 (by rfl) ⟨4772231, by rfl⟩ : syracuseStep 6362975 = 9544463) B9544463
theorem B4241983 : Blo 2233435 4241983 := bstep (se 1 (by rfl) ⟨3181487, by rfl⟩ : syracuseStep 4241983 = 6362975) B6362975
theorem B5655977 : Blo 2233435 5655977 := bstep (se 2 (by rfl) ⟨2120991, by rfl⟩ : syracuseStep 5655977 = 4241983) B4241983
theorem B3770651 : Blo 2233435 3770651 := bstep (se 1 (by rfl) ⟨2827988, by rfl⟩ : syracuseStep 3770651 = 5655977) B5655977
theorem B2513767 : Blo 2233435 2513767 := bstep (se 1 (by rfl) ⟨1885325, by rfl⟩ : syracuseStep 2513767 = 3770651) B3770651
theorem B3351689 : Blo 2233435 3351689 := bstep (se 2 (by rfl) ⟨1256883, by rfl⟩ : syracuseStep 3351689 = 2513767) B2513767
theorem B2234459 : Blo 2233435 2234459 := bstep (se 1 (by rfl) ⟨1675844, by rfl⟩ : syracuseStep 2234459 = 3351689) B3351689
theorem B11311973 : Blo 2233435 11311973 := bbase (se 4 (by rfl) ⟨1060497, by rfl⟩ : syracuseStep 11311973 = 2120995) (by norm_num)
theorem B7541315 : Blo 2233435 7541315 := bstep (se 1 (by rfl) ⟨5655986, by rfl⟩ : syracuseStep 7541315 = 11311973) B11311973
theorem B5027543 : Blo 2233435 5027543 := bstep (se 1 (by rfl) ⟨3770657, by rfl⟩ : syracuseStep 5027543 = 7541315) B7541315
theorem B3351695 : Blo 2233435 3351695 := bstep (se 1 (by rfl) ⟨2513771, by rfl⟩ : syracuseStep 3351695 = 5027543) B5027543
theorem B2234463 : Blo 2233435 2234463 := bstep (se 1 (by rfl) ⟨1675847, by rfl⟩ : syracuseStep 2234463 = 3351695) B3351695
theorem B3351701 : Blo 2233435 3351701 := bbase (se 6 (by rfl) ⟨78555, by rfl⟩ : syracuseStep 3351701 = 157111) (by norm_num)
theorem B2234467 : Blo 2233435 2234467 := bstep (se 1 (by rfl) ⟨1675850, by rfl⟩ : syracuseStep 2234467 = 3351701) B3351701
theorem B5368789 : Blo 2233435 5368789 := bbase (se 7 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 5368789 = 125831) (by norm_num)
theorem B7158385 : Blo 2233435 7158385 := bstep (se 2 (by rfl) ⟨2684394, by rfl⟩ : syracuseStep 7158385 = 5368789) B5368789
theorem B9544513 : Blo 2233435 9544513 := bstep (se 2 (by rfl) ⟨3579192, by rfl⟩ : syracuseStep 9544513 = 7158385) B7158385
theorem B12726017 : Blo 2233435 12726017 := bstep (se 2 (by rfl) ⟨4772256, by rfl⟩ : syracuseStep 12726017 = 9544513) B9544513
theorem B8484011 : Blo 2233435 8484011 := bstep (se 1 (by rfl) ⟨6363008, by rfl⟩ : syracuseStep 8484011 = 12726017) B12726017
theorem B5656007 : Blo 2233435 5656007 := bstep (se 1 (by rfl) ⟨4242005, by rfl⟩ : syracuseStep 5656007 = 8484011) B8484011
theorem B3770671 : Blo 2233435 3770671 := bstep (se 1 (by rfl) ⟨2828003, by rfl⟩ : syracuseStep 3770671 = 5656007) B5656007
theorem B5027561 : Blo 2233435 5027561 := bstep (se 2 (by rfl) ⟨1885335, by rfl⟩ : syracuseStep 5027561 = 3770671) B3770671
theorem B3351707 : Blo 2233435 3351707 := bstep (se 1 (by rfl) ⟨2513780, by rfl⟩ : syracuseStep 3351707 = 5027561) B5027561
theorem B2234471 : Blo 2233435 2234471 := bstep (se 1 (by rfl) ⟨1675853, by rfl⟩ : syracuseStep 2234471 = 3351707) B3351707
theorem B2513785 : Blo 2233435 2513785 := bbase (se 2 (by rfl) ⟨942669, by rfl⟩ : syracuseStep 2513785 = 1885339) (by norm_num)
theorem B3351713 : Blo 2233435 3351713 := bstep (se 2 (by rfl) ⟨1256892, by rfl⟩ : syracuseStep 3351713 = 2513785) B2513785
theorem B2234475 : Blo 2233435 2234475 := bstep (se 1 (by rfl) ⟨1675856, by rfl⟩ : syracuseStep 2234475 = 3351713) B3351713
theorem B14316821 : Blo 2233435 14316821 := bbase (se 6 (by rfl) ⟨335550, by rfl⟩ : syracuseStep 14316821 = 671101) (by norm_num)
theorem B9544547 : Blo 2233435 9544547 := bstep (se 1 (by rfl) ⟨7158410, by rfl⟩ : syracuseStep 9544547 = 14316821) B14316821
theorem B6363031 : Blo 2233435 6363031 := bstep (se 1 (by rfl) ⟨4772273, by rfl⟩ : syracuseStep 6363031 = 9544547) B9544547
theorem B8484041 : Blo 2233435 8484041 := bstep (se 2 (by rfl) ⟨3181515, by rfl⟩ : syracuseStep 8484041 = 6363031) B6363031
theorem B5656027 : Blo 2233435 5656027 := bstep (se 1 (by rfl) ⟨4242020, by rfl⟩ : syracuseStep 5656027 = 8484041) B8484041
theorem B7541369 : Blo 2233435 7541369 := bstep (se 2 (by rfl) ⟨2828013, by rfl⟩ : syracuseStep 7541369 = 5656027) B5656027
theorem B5027579 : Blo 2233435 5027579 := bstep (se 1 (by rfl) ⟨3770684, by rfl⟩ : syracuseStep 5027579 = 7541369) B7541369
theorem B3351719 : Blo 2233435 3351719 := bstep (se 1 (by rfl) ⟨2513789, by rfl⟩ : syracuseStep 3351719 = 5027579) B5027579
theorem B2234479 : Blo 2233435 2234479 := bstep (se 1 (by rfl) ⟨1675859, by rfl⟩ : syracuseStep 2234479 = 3351719) B3351719
theorem B3351725 : Blo 2233435 3351725 := bbase (se 3 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 3351725 = 1256897) (by norm_num)
theorem B2234483 : Blo 2233435 2234483 := bstep (se 1 (by rfl) ⟨1675862, by rfl⟩ : syracuseStep 2234483 = 3351725) B3351725
theorem B5027597 : Blo 2233435 5027597 := bbase (se 3 (by rfl) ⟨942674, by rfl⟩ : syracuseStep 5027597 = 1885349) (by norm_num)
theorem B3351731 : Blo 2233435 3351731 := bstep (se 1 (by rfl) ⟨2513798, by rfl⟩ : syracuseStep 3351731 = 5027597) B5027597
theorem B2234487 : Blo 2233435 2234487 := bstep (se 1 (by rfl) ⟨1675865, by rfl⟩ : syracuseStep 2234487 = 3351731) B3351731
theorem B2828029 : Blo 2233435 2828029 := bbase (se 3 (by rfl) ⟨530255, by rfl⟩ : syracuseStep 2828029 = 1060511) (by norm_num)
theorem B3770705 : Blo 2233435 3770705 := bstep (se 2 (by rfl) ⟨1414014, by rfl⟩ : syracuseStep 3770705 = 2828029) B2828029
theorem B2513803 : Blo 2233435 2513803 := bstep (se 1 (by rfl) ⟨1885352, by rfl⟩ : syracuseStep 2513803 = 3770705) B3770705
theorem B3351737 : Blo 2233435 3351737 := bstep (se 2 (by rfl) ⟨1256901, by rfl⟩ : syracuseStep 3351737 = 2513803) B2513803
theorem B2234491 : Blo 2233435 2234491 := bstep (se 1 (by rfl) ⟨1675868, by rfl⟩ : syracuseStep 2234491 = 3351737) B3351737
theorem B4529965 : Blo 2233435 4529965 := bbase (se 3 (by rfl) ⟨849368, by rfl⟩ : syracuseStep 4529965 = 1698737) (by norm_num)
theorem B6039953 : Blo 2233435 6039953 := bstep (se 2 (by rfl) ⟨2264982, by rfl⟩ : syracuseStep 6039953 = 4529965) B4529965
theorem B4026635 : Blo 2233435 4026635 := bstep (se 1 (by rfl) ⟨3019976, by rfl⟩ : syracuseStep 4026635 = 6039953) B6039953
theorem B2684423 : Blo 2233435 2684423 := bstep (se 1 (by rfl) ⟨2013317, by rfl⟩ : syracuseStep 2684423 = 4026635) B4026635
theorem B7158461 : Blo 2233435 7158461 := bstep (se 3 (by rfl) ⟨1342211, by rfl⟩ : syracuseStep 7158461 = 2684423) B2684423
theorem B19089229 : Blo 2233435 19089229 := bstep (se 3 (by rfl) ⟨3579230, by rfl⟩ : syracuseStep 19089229 = 7158461) B7158461
theorem B25452305 : Blo 2233435 25452305 := bstep (se 2 (by rfl) ⟨9544614, by rfl⟩ : syracuseStep 25452305 = 19089229) B19089229
theorem B16968203 : Blo 2233435 16968203 := bstep (se 1 (by rfl) ⟨12726152, by rfl⟩ : syracuseStep 16968203 = 25452305) B25452305
theorem B11312135 : Blo 2233435 11312135 := bstep (se 1 (by rfl) ⟨8484101, by rfl⟩ : syracuseStep 11312135 = 16968203) B16968203
theorem B7541423 : Blo 2233435 7541423 := bstep (se 1 (by rfl) ⟨5656067, by rfl⟩ : syracuseStep 7541423 = 11312135) B11312135
theorem B5027615 : Blo 2233435 5027615 := bstep (se 1 (by rfl) ⟨3770711, by rfl⟩ : syracuseStep 5027615 = 7541423) B7541423
theorem B3351743 : Blo 2233435 3351743 := bstep (se 1 (by rfl) ⟨2513807, by rfl⟩ : syracuseStep 3351743 = 5027615) B5027615
theorem B2234495 : Blo 2233435 2234495 := bstep (se 1 (by rfl) ⟨1675871, by rfl⟩ : syracuseStep 2234495 = 3351743) B3351743
theorem B3351749 : Blo 2233435 3351749 := bbase (se 4 (by rfl) ⟨314226, by rfl⟩ : syracuseStep 3351749 = 628453) (by norm_num)
theorem B2234499 : Blo 2233435 2234499 := bstep (se 1 (by rfl) ⟨1675874, by rfl⟩ : syracuseStep 2234499 = 3351749) B3351749
theorem B3770725 : Blo 2233435 3770725 := bbase (se 4 (by rfl) ⟨353505, by rfl⟩ : syracuseStep 3770725 = 707011) (by norm_num)
theorem B5027633 : Blo 2233435 5027633 := bstep (se 2 (by rfl) ⟨1885362, by rfl⟩ : syracuseStep 5027633 = 3770725) B3770725
theorem B3351755 : Blo 2233435 3351755 := bstep (se 1 (by rfl) ⟨2513816, by rfl⟩ : syracuseStep 3351755 = 5027633) B5027633
theorem B2234503 : Blo 2233435 2234503 := bstep (se 1 (by rfl) ⟨1675877, by rfl⟩ : syracuseStep 2234503 = 3351755) B3351755
theorem B2513821 : Blo 2233435 2513821 := bbase (se 3 (by rfl) ⟨471341, by rfl⟩ : syracuseStep 2513821 = 942683) (by norm_num)
theorem B3351761 : Blo 2233435 3351761 := bstep (se 2 (by rfl) ⟨1256910, by rfl⟩ : syracuseStep 3351761 = 2513821) B2513821
theorem B2234507 : Blo 2233435 2234507 := bstep (se 1 (by rfl) ⟨1675880, by rfl⟩ : syracuseStep 2234507 = 3351761) B3351761
theorem B7541477 : Blo 2233435 7541477 := bbase (se 4 (by rfl) ⟨707013, by rfl⟩ : syracuseStep 7541477 = 1414027) (by norm_num)
theorem B5027651 : Blo 2233435 5027651 := bstep (se 1 (by rfl) ⟨3770738, by rfl⟩ : syracuseStep 5027651 = 7541477) B7541477
theorem B3351767 : Blo 2233435 3351767 := bstep (se 1 (by rfl) ⟨2513825, by rfl⟩ : syracuseStep 3351767 = 5027651) B5027651
theorem B2234511 : Blo 2233435 2234511 := bstep (se 1 (by rfl) ⟨1675883, by rfl⟩ : syracuseStep 2234511 = 3351767) B3351767
theorem B3351773 : Blo 2233435 3351773 := bbase (se 3 (by rfl) ⟨628457, by rfl⟩ : syracuseStep 3351773 = 1256915) (by norm_num)
theorem B2234515 : Blo 2233435 2234515 := bstep (se 1 (by rfl) ⟨1675886, by rfl⟩ : syracuseStep 2234515 = 3351773) B3351773
theorem B5027669 : Blo 2233435 5027669 := bbase (se 9 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 5027669 = 29459) (by norm_num)
theorem B3351779 : Blo 2233435 3351779 := bstep (se 1 (by rfl) ⟨2513834, by rfl⟩ : syracuseStep 3351779 = 5027669) B5027669
theorem B2234519 : Blo 2233435 2234519 := bstep (se 1 (by rfl) ⟨1675889, by rfl⟩ : syracuseStep 2234519 = 3351779) B3351779
theorem B6363157 : Blo 2233435 6363157 := bbase (se 6 (by rfl) ⟨149136, by rfl⟩ : syracuseStep 6363157 = 298273) (by norm_num)
theorem B8484209 : Blo 2233435 8484209 := bstep (se 2 (by rfl) ⟨3181578, by rfl⟩ : syracuseStep 8484209 = 6363157) B6363157
theorem B5656139 : Blo 2233435 5656139 := bstep (se 1 (by rfl) ⟨4242104, by rfl⟩ : syracuseStep 5656139 = 8484209) B8484209
theorem B3770759 : Blo 2233435 3770759 := bstep (se 1 (by rfl) ⟨2828069, by rfl⟩ : syracuseStep 3770759 = 5656139) B5656139
theorem B2513839 : Blo 2233435 2513839 := bstep (se 1 (by rfl) ⟨1885379, by rfl⟩ : syracuseStep 2513839 = 3770759) B3770759
theorem B3351785 : Blo 2233435 3351785 := bstep (se 2 (by rfl) ⟨1256919, by rfl⟩ : syracuseStep 3351785 = 2513839) B2513839
theorem B2234523 : Blo 2233435 2234523 := bstep (se 1 (by rfl) ⟨1675892, by rfl⟩ : syracuseStep 2234523 = 3351785) B3351785
theorem B10192565 : Blo 2233435 10192565 := bbase (se 5 (by rfl) ⟨477776, by rfl⟩ : syracuseStep 10192565 = 955553) (by norm_num)
theorem B27180173 : Blo 2233435 27180173 := bstep (se 3 (by rfl) ⟨5096282, by rfl⟩ : syracuseStep 27180173 = 10192565) B10192565
theorem B18120115 : Blo 2233435 18120115 := bstep (se 1 (by rfl) ⟨13590086, by rfl⟩ : syracuseStep 18120115 = 27180173) B27180173
theorem B96640613 : Blo 2233435 96640613 := bstep (se 4 (by rfl) ⟨9060057, by rfl⟩ : syracuseStep 96640613 = 18120115) B18120115
theorem B64427075 : Blo 2233435 64427075 := bstep (se 1 (by rfl) ⟨48320306, by rfl⟩ : syracuseStep 64427075 = 96640613) B96640613
theorem B42951383 : Blo 2233435 42951383 := bstep (se 1 (by rfl) ⟨32213537, by rfl⟩ : syracuseStep 42951383 = 64427075) B64427075
theorem B28634255 : Blo 2233435 28634255 := bstep (se 1 (by rfl) ⟨21475691, by rfl⟩ : syracuseStep 28634255 = 42951383) B42951383
theorem B19089503 : Blo 2233435 19089503 := bstep (se 1 (by rfl) ⟨14317127, by rfl⟩ : syracuseStep 19089503 = 28634255) B28634255
theorem B12726335 : Blo 2233435 12726335 := bstep (se 1 (by rfl) ⟨9544751, by rfl⟩ : syracuseStep 12726335 = 19089503) B19089503
theorem B8484223 : Blo 2233435 8484223 := bstep (se 1 (by rfl) ⟨6363167, by rfl⟩ : syracuseStep 8484223 = 12726335) B12726335
theorem B11312297 : Blo 2233435 11312297 := bstep (se 2 (by rfl) ⟨4242111, by rfl⟩ : syracuseStep 11312297 = 8484223) B8484223
theorem B7541531 : Blo 2233435 7541531 := bstep (se 1 (by rfl) ⟨5656148, by rfl⟩ : syracuseStep 7541531 = 11312297) B11312297
theorem B5027687 : Blo 2233435 5027687 := bstep (se 1 (by rfl) ⟨3770765, by rfl⟩ : syracuseStep 5027687 = 7541531) B7541531
theorem B3351791 : Blo 2233435 3351791 := bstep (se 1 (by rfl) ⟨2513843, by rfl⟩ : syracuseStep 3351791 = 5027687) B5027687
theorem B2234527 : Blo 2233435 2234527 := bstep (se 1 (by rfl) ⟨1675895, by rfl⟩ : syracuseStep 2234527 = 3351791) B3351791
theorem B3351797 : Blo 2233435 3351797 := bbase (se 5 (by rfl) ⟨157115, by rfl⟩ : syracuseStep 3351797 = 314231) (by norm_num)
theorem B2234531 : Blo 2233435 2234531 := bstep (se 1 (by rfl) ⟨1675898, by rfl⟩ : syracuseStep 2234531 = 3351797) B3351797
theorem B17200021 : Blo 2233435 17200021 := bbase (se 6 (by rfl) ⟨403125, by rfl⟩ : syracuseStep 17200021 = 806251) (by norm_num)
theorem B22933361 : Blo 2233435 22933361 := bstep (se 2 (by rfl) ⟨8600010, by rfl⟩ : syracuseStep 22933361 = 17200021) B17200021
theorem B15288907 : Blo 2233435 15288907 := bstep (se 1 (by rfl) ⟨11466680, by rfl⟩ : syracuseStep 15288907 = 22933361) B22933361
theorem B20385209 : Blo 2233435 20385209 := bstep (se 2 (by rfl) ⟨7644453, by rfl⟩ : syracuseStep 20385209 = 15288907) B15288907
theorem B13590139 : Blo 2233435 13590139 := bstep (se 1 (by rfl) ⟨10192604, by rfl⟩ : syracuseStep 13590139 = 20385209) B20385209
theorem B18120185 : Blo 2233435 18120185 := bstep (se 2 (by rfl) ⟨6795069, by rfl⟩ : syracuseStep 18120185 = 13590139) B13590139
theorem B12080123 : Blo 2233435 12080123 := bstep (se 1 (by rfl) ⟨9060092, by rfl⟩ : syracuseStep 12080123 = 18120185) B18120185
theorem B8053415 : Blo 2233435 8053415 := bstep (se 1 (by rfl) ⟨6040061, by rfl⟩ : syracuseStep 8053415 = 12080123) B12080123
theorem B5368943 : Blo 2233435 5368943 := bstep (se 1 (by rfl) ⟨4026707, by rfl⟩ : syracuseStep 5368943 = 8053415) B8053415
theorem B14317181 : Blo 2233435 14317181 := bstep (se 3 (by rfl) ⟨2684471, by rfl⟩ : syracuseStep 14317181 = 5368943) B5368943
theorem B9544787 : Blo 2233435 9544787 := bstep (se 1 (by rfl) ⟨7158590, by rfl⟩ : syracuseStep 9544787 = 14317181) B14317181
theorem B6363191 : Blo 2233435 6363191 := bstep (se 1 (by rfl) ⟨4772393, by rfl⟩ : syracuseStep 6363191 = 9544787) B9544787
theorem B4242127 : Blo 2233435 4242127 := bstep (se 1 (by rfl) ⟨3181595, by rfl⟩ : syracuseStep 4242127 = 6363191) B6363191
theorem B5656169 : Blo 2233435 5656169 := bstep (se 2 (by rfl) ⟨2121063, by rfl⟩ : syracuseStep 5656169 = 4242127) B4242127
theorem B3770779 : Blo 2233435 3770779 := bstep (se 1 (by rfl) ⟨2828084, by rfl⟩ : syracuseStep 3770779 = 5656169) B5656169
theorem B5027705 : Blo 2233435 5027705 := bstep (se 2 (by rfl) ⟨1885389, by rfl⟩ : syracuseStep 5027705 = 3770779) B3770779
theorem B3351803 : Blo 2233435 3351803 := bstep (se 1 (by rfl) ⟨2513852, by rfl⟩ : syracuseStep 3351803 = 5027705) B5027705
theorem B2234535 : Blo 2233435 2234535 := bstep (se 1 (by rfl) ⟨1675901, by rfl⟩ : syracuseStep 2234535 = 3351803) B3351803
theorem B2513857 : Blo 2233435 2513857 := bbase (se 2 (by rfl) ⟨942696, by rfl⟩ : syracuseStep 2513857 = 1885393) (by norm_num)
theorem B3351809 : Blo 2233435 3351809 := bstep (se 2 (by rfl) ⟨1256928, by rfl⟩ : syracuseStep 3351809 = 2513857) B2513857
theorem B2234539 : Blo 2233435 2234539 := bstep (se 1 (by rfl) ⟨1675904, by rfl⟩ : syracuseStep 2234539 = 3351809) B3351809
theorem B5656189 : Blo 2233435 5656189 := bbase (se 3 (by rfl) ⟨1060535, by rfl⟩ : syracuseStep 5656189 = 2121071) (by norm_num)
theorem B7541585 : Blo 2233435 7541585 := bstep (se 2 (by rfl) ⟨2828094, by rfl⟩ : syracuseStep 7541585 = 5656189) B5656189
theorem B5027723 : Blo 2233435 5027723 := bstep (se 1 (by rfl) ⟨3770792, by rfl⟩ : syracuseStep 5027723 = 7541585) B7541585
theorem B3351815 : Blo 2233435 3351815 := bstep (se 1 (by rfl) ⟨2513861, by rfl⟩ : syracuseStep 3351815 = 5027723) B5027723
theorem B2234543 : Blo 2233435 2234543 := bstep (se 1 (by rfl) ⟨1675907, by rfl⟩ : syracuseStep 2234543 = 3351815) B3351815
theorem B3351821 : Blo 2233435 3351821 := bbase (se 3 (by rfl) ⟨628466, by rfl⟩ : syracuseStep 3351821 = 1256933) (by norm_num)
theorem B2234547 : Blo 2233435 2234547 := bstep (se 1 (by rfl) ⟨1675910, by rfl⟩ : syracuseStep 2234547 = 3351821) B3351821
theorem B5027741 : Blo 2233435 5027741 := bbase (se 3 (by rfl) ⟨942701, by rfl⟩ : syracuseStep 5027741 = 1885403) (by norm_num)
theorem B3351827 : Blo 2233435 3351827 := bstep (se 1 (by rfl) ⟨2513870, by rfl⟩ : syracuseStep 3351827 = 5027741) B5027741
theorem B2234551 : Blo 2233435 2234551 := bstep (se 1 (by rfl) ⟨1675913, by rfl⟩ : syracuseStep 2234551 = 3351827) B3351827
theorem B3770813 : Blo 2233435 3770813 := bbase (se 3 (by rfl) ⟨707027, by rfl⟩ : syracuseStep 3770813 = 1414055) (by norm_num)
theorem B2513875 : Blo 2233435 2513875 := bstep (se 1 (by rfl) ⟨1885406, by rfl⟩ : syracuseStep 2513875 = 3770813) B3770813
theorem B3351833 : Blo 2233435 3351833 := bstep (se 2 (by rfl) ⟨1256937, by rfl⟩ : syracuseStep 3351833 = 2513875) B2513875
theorem B2234555 : Blo 2233435 2234555 := bstep (se 1 (by rfl) ⟨1675916, by rfl⟩ : syracuseStep 2234555 = 3351833) B3351833
theorem B12726517 : Blo 2233435 12726517 := bbase (se 5 (by rfl) ⟨596555, by rfl⟩ : syracuseStep 12726517 = 1193111) (by norm_num)
theorem B16968689 : Blo 2233435 16968689 := bstep (se 2 (by rfl) ⟨6363258, by rfl⟩ : syracuseStep 16968689 = 12726517) B12726517
theorem B11312459 : Blo 2233435 11312459 := bstep (se 1 (by rfl) ⟨8484344, by rfl⟩ : syracuseStep 11312459 = 16968689) B16968689
theorem B7541639 : Blo 2233435 7541639 := bstep (se 1 (by rfl) ⟨5656229, by rfl⟩ : syracuseStep 7541639 = 11312459) B11312459
theorem B5027759 : Blo 2233435 5027759 := bstep (se 1 (by rfl) ⟨3770819, by rfl⟩ : syracuseStep 5027759 = 7541639) B7541639
theorem B3351839 : Blo 2233435 3351839 := bstep (se 1 (by rfl) ⟨2513879, by rfl⟩ : syracuseStep 3351839 = 5027759) B5027759
theorem B2234559 : Blo 2233435 2234559 := bstep (se 1 (by rfl) ⟨1675919, by rfl⟩ : syracuseStep 2234559 = 3351839) B3351839
theorem B3351845 : Blo 2233435 3351845 := bbase (se 4 (by rfl) ⟨314235, by rfl⟩ : syracuseStep 3351845 = 628471) (by norm_num)
theorem B2234563 : Blo 2233435 2234563 := bstep (se 1 (by rfl) ⟨1675922, by rfl⟩ : syracuseStep 2234563 = 3351845) B3351845
theorem B2828125 : Blo 2233435 2828125 := bbase (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) (by norm_num)
theorem B3770833 : Blo 2233435 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B5027777 : Blo 2233435 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B3351851 : Blo 2233435 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B2234567 : Blo 2233435 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B2513893 : Blo 2233435 2513893 := bbase (se 4 (by rfl) ⟨235677, by rfl⟩ : syracuseStep 2513893 = 471355) (by norm_num)
theorem B3351857 : Blo 2233435 3351857 := bstep (se 2 (by rfl) ⟨1256946, by rfl⟩ : syracuseStep 3351857 = 2513893) B2513893
theorem B2234571 : Blo 2233435 2234571 := bstep (se 1 (by rfl) ⟨1675928, by rfl⟩ : syracuseStep 2234571 = 3351857) B3351857
theorem B45867541 : Blo 2233435 45867541 := bbase (se 6 (by rfl) ⟨1075020, by rfl⟩ : syracuseStep 45867541 = 2150041) (by norm_num)
theorem B61156721 : Blo 2233435 61156721 := bstep (se 2 (by rfl) ⟨22933770, by rfl⟩ : syracuseStep 61156721 = 45867541) B45867541
theorem B40771147 : Blo 2233435 40771147 := bstep (se 1 (by rfl) ⟨30578360, by rfl⟩ : syracuseStep 40771147 = 61156721) B61156721
theorem B54361529 : Blo 2233435 54361529 := bstep (se 2 (by rfl) ⟨20385573, by rfl⟩ : syracuseStep 54361529 = 40771147) B40771147
theorem B36241019 : Blo 2233435 36241019 := bstep (se 1 (by rfl) ⟨27180764, by rfl⟩ : syracuseStep 36241019 = 54361529) B54361529
theorem B24160679 : Blo 2233435 24160679 := bstep (se 1 (by rfl) ⟨18120509, by rfl⟩ : syracuseStep 24160679 = 36241019) B36241019
theorem B16107119 : Blo 2233435 16107119 := bstep (se 1 (by rfl) ⟨12080339, by rfl⟩ : syracuseStep 16107119 = 24160679) B24160679
theorem B10738079 : Blo 2233435 10738079 := bstep (se 1 (by rfl) ⟨8053559, by rfl⟩ : syracuseStep 10738079 = 16107119) B16107119
theorem B7158719 : Blo 2233435 7158719 := bstep (se 1 (by rfl) ⟨5369039, by rfl⟩ : syracuseStep 7158719 = 10738079) B10738079
theorem B4772479 : Blo 2233435 4772479 := bstep (se 1 (by rfl) ⟨3579359, by rfl⟩ : syracuseStep 4772479 = 7158719) B7158719
theorem B6363305 : Blo 2233435 6363305 := bstep (se 2 (by rfl) ⟨2386239, by rfl⟩ : syracuseStep 6363305 = 4772479) B4772479
theorem B4242203 : Blo 2233435 4242203 := bstep (se 1 (by rfl) ⟨3181652, by rfl⟩ : syracuseStep 4242203 = 6363305) B6363305
theorem B2828135 : Blo 2233435 2828135 := bstep (se 1 (by rfl) ⟨2121101, by rfl⟩ : syracuseStep 2828135 = 4242203) B4242203
theorem B7541693 : Blo 2233435 7541693 := bstep (se 3 (by rfl) ⟨1414067, by rfl⟩ : syracuseStep 7541693 = 2828135) B2828135
theorem B5027795 : Blo 2233435 5027795 := bstep (se 1 (by rfl) ⟨3770846, by rfl⟩ : syracuseStep 5027795 = 7541693) B7541693
theorem B3351863 : Blo 2233435 3351863 := bstep (se 1 (by rfl) ⟨2513897, by rfl⟩ : syracuseStep 3351863 = 5027795) B5027795
theorem B2234575 : Blo 2233435 2234575 := bstep (se 1 (by rfl) ⟨1675931, by rfl⟩ : syracuseStep 2234575 = 3351863) B3351863
theorem B3351869 : Blo 2233435 3351869 := bbase (se 3 (by rfl) ⟨628475, by rfl⟩ : syracuseStep 3351869 = 1256951) (by norm_num)
theorem B2234579 : Blo 2233435 2234579 := bstep (se 1 (by rfl) ⟨1675934, by rfl⟩ : syracuseStep 2234579 = 3351869) B3351869
theorem B5027813 : Blo 2233435 5027813 := bbase (se 4 (by rfl) ⟨471357, by rfl⟩ : syracuseStep 5027813 = 942715) (by norm_num)
theorem B3351875 : Blo 2233435 3351875 := bstep (se 1 (by rfl) ⟨2513906, by rfl⟩ : syracuseStep 3351875 = 5027813) B5027813
theorem B2234583 : Blo 2233435 2234583 := bstep (se 1 (by rfl) ⟨1675937, by rfl⟩ : syracuseStep 2234583 = 3351875) B3351875
theorem B5656301 : Blo 2233435 5656301 := bbase (se 3 (by rfl) ⟨1060556, by rfl⟩ : syracuseStep 5656301 = 2121113) (by norm_num)
theorem B3770867 : Blo 2233435 3770867 := bstep (se 1 (by rfl) ⟨2828150, by rfl⟩ : syracuseStep 3770867 = 5656301) B5656301
theorem B2513911 : Blo 2233435 2513911 := bstep (se 1 (by rfl) ⟨1885433, by rfl⟩ : syracuseStep 2513911 = 3770867) B3770867
theorem B3351881 : Blo 2233435 3351881 := bstep (se 2 (by rfl) ⟨1256955, by rfl⟩ : syracuseStep 3351881 = 2513911) B2513911
theorem B2234587 : Blo 2233435 2234587 := bstep (se 1 (by rfl) ⟨1675940, by rfl⟩ : syracuseStep 2234587 = 3351881) B3351881
theorem B3397621 : Blo 2233435 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B4530161 : Blo 2233435 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B3020107 : Blo 2233435 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B4026809 : Blo 2233435 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B2684539 : Blo 2233435 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B3579385 : Blo 2233435 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B4772513 : Blo 2233435 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B3181675 : Blo 2233435 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B4242233 : Blo 2233435 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B11312621 : Blo 2233435 11312621 := bstep (se 3 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 11312621 = 4242233) B4242233
theorem B7541747 : Blo 2233435 7541747 := bstep (se 1 (by rfl) ⟨5656310, by rfl⟩ : syracuseStep 7541747 = 11312621) B11312621
theorem B5027831 : Blo 2233435 5027831 := bstep (se 1 (by rfl) ⟨3770873, by rfl⟩ : syracuseStep 5027831 = 7541747) B7541747
theorem B3351887 : Blo 2233435 3351887 := bstep (se 1 (by rfl) ⟨2513915, by rfl⟩ : syracuseStep 3351887 = 5027831) B5027831
theorem B2234591 : Blo 2233435 2234591 := bstep (se 1 (by rfl) ⟨1675943, by rfl⟩ : syracuseStep 2234591 = 3351887) B3351887
theorem B3351893 : Blo 2233435 3351893 := bbase (se 12 (by rfl) ⟨1227, by rfl⟩ : syracuseStep 3351893 = 2455) (by norm_num)
theorem B2234595 : Blo 2233435 2234595 := bstep (se 1 (by rfl) ⟨1675946, by rfl⟩ : syracuseStep 2234595 = 3351893) B3351893
theorem B2386265 : Blo 2233435 2386265 := bbase (se 2 (by rfl) ⟨894849, by rfl⟩ : syracuseStep 2386265 = 1789699) (by norm_num)
theorem B6363373 : Blo 2233435 6363373 := bstep (se 3 (by rfl) ⟨1193132, by rfl⟩ : syracuseStep 6363373 = 2386265) B2386265
theorem B8484497 : Blo 2233435 8484497 := bstep (se 2 (by rfl) ⟨3181686, by rfl⟩ : syracuseStep 8484497 = 6363373) B6363373
theorem B5656331 : Blo 2233435 5656331 := bstep (se 1 (by rfl) ⟨4242248, by rfl⟩ : syracuseStep 5656331 = 8484497) B8484497
theorem B3770887 : Blo 2233435 3770887 := bstep (se 1 (by rfl) ⟨2828165, by rfl⟩ : syracuseStep 3770887 = 5656331) B5656331
theorem B5027849 : Blo 2233435 5027849 := bstep (se 2 (by rfl) ⟨1885443, by rfl⟩ : syracuseStep 5027849 = 3770887) B3770887
theorem B3351899 : Blo 2233435 3351899 := bstep (se 1 (by rfl) ⟨2513924, by rfl⟩ : syracuseStep 3351899 = 5027849) B5027849
theorem B2234599 : Blo 2233435 2234599 := bstep (se 1 (by rfl) ⟨1675949, by rfl⟩ : syracuseStep 2234599 = 3351899) B3351899
theorem B2513929 : Blo 2233435 2513929 := bbase (se 2 (by rfl) ⟨942723, by rfl⟩ : syracuseStep 2513929 = 1885447) (by norm_num)
theorem B3351905 : Blo 2233435 3351905 := bstep (se 2 (by rfl) ⟨1256964, by rfl⟩ : syracuseStep 3351905 = 2513929) B2513929
theorem B2234603 : Blo 2233435 2234603 := bstep (se 1 (by rfl) ⟨1675952, by rfl⟩ : syracuseStep 2234603 = 3351905) B3351905
theorem B5307925 : Blo 2233435 5307925 := bbase (se 6 (by rfl) ⟨124404, by rfl⟩ : syracuseStep 5307925 = 248809) (by norm_num)
theorem B7077233 : Blo 2233435 7077233 := bstep (se 2 (by rfl) ⟨2653962, by rfl⟩ : syracuseStep 7077233 = 5307925) B5307925
theorem B18872621 : Blo 2233435 18872621 := bstep (se 3 (by rfl) ⟨3538616, by rfl⟩ : syracuseStep 18872621 = 7077233) B7077233
theorem B12581747 : Blo 2233435 12581747 := bstep (se 1 (by rfl) ⟨9436310, by rfl⟩ : syracuseStep 12581747 = 18872621) B18872621
theorem B8387831 : Blo 2233435 8387831 := bstep (se 1 (by rfl) ⟨6290873, by rfl⟩ : syracuseStep 8387831 = 12581747) B12581747
theorem B22367549 : Blo 2233435 22367549 := bstep (se 3 (by rfl) ⟨4193915, by rfl⟩ : syracuseStep 22367549 = 8387831) B8387831
theorem B14911699 : Blo 2233435 14911699 := bstep (se 1 (by rfl) ⟨11183774, by rfl⟩ : syracuseStep 14911699 = 22367549) B22367549
theorem B19882265 : Blo 2233435 19882265 := bstep (se 2 (by rfl) ⟨7455849, by rfl⟩ : syracuseStep 19882265 = 14911699) B14911699
theorem B53019373 : Blo 2233435 53019373 := bstep (se 3 (by rfl) ⟨9941132, by rfl⟩ : syracuseStep 53019373 = 19882265) B19882265
theorem B70692497 : Blo 2233435 70692497 := bstep (se 2 (by rfl) ⟨26509686, by rfl⟩ : syracuseStep 70692497 = 53019373) B53019373
theorem B47128331 : Blo 2233435 47128331 := bstep (se 1 (by rfl) ⟨35346248, by rfl⟩ : syracuseStep 47128331 = 70692497) B70692497
theorem B31418887 : Blo 2233435 31418887 := bstep (se 1 (by rfl) ⟨23564165, by rfl⟩ : syracuseStep 31418887 = 47128331) B47128331
theorem B41891849 : Blo 2233435 41891849 := bstep (se 2 (by rfl) ⟨15709443, by rfl⟩ : syracuseStep 41891849 = 31418887) B31418887
theorem B27927899 : Blo 2233435 27927899 := bstep (se 1 (by rfl) ⟨20945924, by rfl⟩ : syracuseStep 27927899 = 41891849) B41891849
theorem B18618599 : Blo 2233435 18618599 := bstep (se 1 (by rfl) ⟨13963949, by rfl⟩ : syracuseStep 18618599 = 27927899) B27927899
theorem B12412399 : Blo 2233435 12412399 := bstep (se 1 (by rfl) ⟨9309299, by rfl⟩ : syracuseStep 12412399 = 18618599) B18618599
theorem B16549865 : Blo 2233435 16549865 := bstep (se 2 (by rfl) ⟨6206199, by rfl⟩ : syracuseStep 16549865 = 12412399) B12412399
theorem B11033243 : Blo 2233435 11033243 := bstep (se 1 (by rfl) ⟨8274932, by rfl⟩ : syracuseStep 11033243 = 16549865) B16549865
theorem B7355495 : Blo 2233435 7355495 := bstep (se 1 (by rfl) ⟨5516621, by rfl⟩ : syracuseStep 7355495 = 11033243) B11033243
theorem B19614653 : Blo 2233435 19614653 := bstep (se 3 (by rfl) ⟨3677747, by rfl⟩ : syracuseStep 19614653 = 7355495) B7355495
theorem B13076435 : Blo 2233435 13076435 := bstep (se 1 (by rfl) ⟨9807326, by rfl⟩ : syracuseStep 13076435 = 19614653) B19614653
theorem B34870493 : Blo 2233435 34870493 := bstep (se 3 (by rfl) ⟨6538217, by rfl⟩ : syracuseStep 34870493 = 13076435) B13076435
theorem B23246995 : Blo 2233435 23246995 := bstep (se 1 (by rfl) ⟨17435246, by rfl⟩ : syracuseStep 23246995 = 34870493) B34870493
theorem B30995993 : Blo 2233435 30995993 := bstep (se 2 (by rfl) ⟨11623497, by rfl⟩ : syracuseStep 30995993 = 23246995) B23246995
theorem B20663995 : Blo 2233435 20663995 := bstep (se 1 (by rfl) ⟨15497996, by rfl⟩ : syracuseStep 20663995 = 30995993) B30995993
theorem B27551993 : Blo 2233435 27551993 := bstep (se 2 (by rfl) ⟨10331997, by rfl⟩ : syracuseStep 27551993 = 20663995) B20663995
theorem B73471981 : Blo 2233435 73471981 := bstep (se 3 (by rfl) ⟨13775996, by rfl⟩ : syracuseStep 73471981 = 27551993) B27551993
theorem B97962641 : Blo 2233435 97962641 := bstep (se 2 (by rfl) ⟨36735990, by rfl⟩ : syracuseStep 97962641 = 73471981) B73471981
theorem B65308427 : Blo 2233435 65308427 := bstep (se 1 (by rfl) ⟨48981320, by rfl⟩ : syracuseStep 65308427 = 97962641) B97962641
theorem B43538951 : Blo 2233435 43538951 := bstep (se 1 (by rfl) ⟨32654213, by rfl⟩ : syracuseStep 43538951 = 65308427) B65308427
theorem B29025967 : Blo 2233435 29025967 := bstep (se 1 (by rfl) ⟨21769475, by rfl⟩ : syracuseStep 29025967 = 43538951) B43538951
theorem B38701289 : Blo 2233435 38701289 := bstep (se 2 (by rfl) ⟨14512983, by rfl⟩ : syracuseStep 38701289 = 29025967) B29025967
theorem B25800859 : Blo 2233435 25800859 := bstep (se 1 (by rfl) ⟨19350644, by rfl⟩ : syracuseStep 25800859 = 38701289) B38701289
theorem B34401145 : Blo 2233435 34401145 := bstep (se 2 (by rfl) ⟨12900429, by rfl⟩ : syracuseStep 34401145 = 25800859) B25800859
theorem B45868193 : Blo 2233435 45868193 := bstep (se 2 (by rfl) ⟨17200572, by rfl⟩ : syracuseStep 45868193 = 34401145) B34401145
theorem B30578795 : Blo 2233435 30578795 := bstep (se 1 (by rfl) ⟨22934096, by rfl⟩ : syracuseStep 30578795 = 45868193) B45868193
theorem B20385863 : Blo 2233435 20385863 := bstep (se 1 (by rfl) ⟨15289397, by rfl⟩ : syracuseStep 20385863 = 30578795) B30578795
theorem B13590575 : Blo 2233435 13590575 := bstep (se 1 (by rfl) ⟨10192931, by rfl⟩ : syracuseStep 13590575 = 20385863) B20385863
theorem B9060383 : Blo 2233435 9060383 := bstep (se 1 (by rfl) ⟨6795287, by rfl⟩ : syracuseStep 9060383 = 13590575) B13590575
theorem B6040255 : Blo 2233435 6040255 := bstep (se 1 (by rfl) ⟨4530191, by rfl⟩ : syracuseStep 6040255 = 9060383) B9060383
theorem B8053673 : Blo 2233435 8053673 := bstep (se 2 (by rfl) ⟨3020127, by rfl⟩ : syracuseStep 8053673 = 6040255) B6040255
theorem B21476461 : Blo 2233435 21476461 := bstep (se 3 (by rfl) ⟨4026836, by rfl⟩ : syracuseStep 21476461 = 8053673) B8053673
theorem B28635281 : Blo 2233435 28635281 := bstep (se 2 (by rfl) ⟨10738230, by rfl⟩ : syracuseStep 28635281 = 21476461) B21476461
theorem B19090187 : Blo 2233435 19090187 := bstep (se 1 (by rfl) ⟨14317640, by rfl⟩ : syracuseStep 19090187 = 28635281) B28635281
theorem B12726791 : Blo 2233435 12726791 := bstep (se 1 (by rfl) ⟨9545093, by rfl⟩ : syracuseStep 12726791 = 19090187) B19090187
theorem B8484527 : Blo 2233435 8484527 := bstep (se 1 (by rfl) ⟨6363395, by rfl⟩ : syracuseStep 8484527 = 12726791) B12726791
theorem B5656351 : Blo 2233435 5656351 := bstep (se 1 (by rfl) ⟨4242263, by rfl⟩ : syracuseStep 5656351 = 8484527) B8484527
theorem B7541801 : Blo 2233435 7541801 := bstep (se 2 (by rfl) ⟨2828175, by rfl⟩ : syracuseStep 7541801 = 5656351) B5656351
theorem B5027867 : Blo 2233435 5027867 := bstep (se 1 (by rfl) ⟨3770900, by rfl⟩ : syracuseStep 5027867 = 7541801) B7541801
theorem B3351911 : Blo 2233435 3351911 := bstep (se 1 (by rfl) ⟨2513933, by rfl⟩ : syracuseStep 3351911 = 5027867) B5027867
theorem B2234607 : Blo 2233435 2234607 := bstep (se 1 (by rfl) ⟨1675955, by rfl⟩ : syracuseStep 2234607 = 3351911) B3351911
theorem B3351917 : Blo 2233435 3351917 := bbase (se 3 (by rfl) ⟨628484, by rfl⟩ : syracuseStep 3351917 = 1256969) (by norm_num)
theorem B2234611 : Blo 2233435 2234611 := bstep (se 1 (by rfl) ⟨1675958, by rfl⟩ : syracuseStep 2234611 = 3351917) B3351917
theorem B5027885 : Blo 2233435 5027885 := bbase (se 3 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 5027885 = 1885457) (by norm_num)
theorem B3351923 : Blo 2233435 3351923 := bstep (se 1 (by rfl) ⟨2513942, by rfl⟩ : syracuseStep 3351923 = 5027885) B5027885
theorem B2234615 : Blo 2233435 2234615 := bstep (se 1 (by rfl) ⟨1675961, by rfl⟩ : syracuseStep 2234615 = 3351923) B3351923
theorem B4137493 : Blo 2233435 4137493 := bbase (se 6 (by rfl) ⟨96972, by rfl⟩ : syracuseStep 4137493 = 193945) (by norm_num)
theorem B5516657 : Blo 2233435 5516657 := bstep (se 2 (by rfl) ⟨2068746, by rfl⟩ : syracuseStep 5516657 = 4137493) B4137493
theorem B3677771 : Blo 2233435 3677771 := bstep (se 1 (by rfl) ⟨2758328, by rfl⟩ : syracuseStep 3677771 = 5516657) B5516657
theorem B9807389 : Blo 2233435 9807389 := bstep (se 3 (by rfl) ⟨1838885, by rfl⟩ : syracuseStep 9807389 = 3677771) B3677771
theorem B6538259 : Blo 2233435 6538259 := bstep (se 1 (by rfl) ⟨4903694, by rfl⟩ : syracuseStep 6538259 = 9807389) B9807389
theorem B17435357 : Blo 2233435 17435357 := bstep (se 3 (by rfl) ⟨3269129, by rfl⟩ : syracuseStep 17435357 = 6538259) B6538259
theorem B11623571 : Blo 2233435 11623571 := bstep (se 1 (by rfl) ⟨8717678, by rfl⟩ : syracuseStep 11623571 = 17435357) B17435357
theorem B7749047 : Blo 2233435 7749047 := bstep (se 1 (by rfl) ⟨5811785, by rfl⟩ : syracuseStep 7749047 = 11623571) B11623571
theorem B5166031 : Blo 2233435 5166031 := bstep (se 1 (by rfl) ⟨3874523, by rfl⟩ : syracuseStep 5166031 = 7749047) B7749047
theorem B6888041 : Blo 2233435 6888041 := bstep (se 2 (by rfl) ⟨2583015, by rfl⟩ : syracuseStep 6888041 = 5166031) B5166031
theorem B4592027 : Blo 2233435 4592027 := bstep (se 1 (by rfl) ⟨3444020, by rfl⟩ : syracuseStep 4592027 = 6888041) B6888041
theorem B3061351 : Blo 2233435 3061351 := bstep (se 1 (by rfl) ⟨2296013, by rfl⟩ : syracuseStep 3061351 = 4592027) B4592027
theorem B4081801 : Blo 2233435 4081801 := bstep (se 2 (by rfl) ⟨1530675, by rfl⟩ : syracuseStep 4081801 = 3061351) B3061351
theorem B5442401 : Blo 2233435 5442401 := bstep (se 2 (by rfl) ⟨2040900, by rfl⟩ : syracuseStep 5442401 = 4081801) B4081801
theorem B14513069 : Blo 2233435 14513069 := bstep (se 3 (by rfl) ⟨2721200, by rfl⟩ : syracuseStep 14513069 = 5442401) B5442401
theorem B9675379 : Blo 2233435 9675379 := bstep (se 1 (by rfl) ⟨7256534, by rfl⟩ : syracuseStep 9675379 = 14513069) B14513069
theorem B12900505 : Blo 2233435 12900505 := bstep (se 2 (by rfl) ⟨4837689, by rfl⟩ : syracuseStep 12900505 = 9675379) B9675379
theorem B17200673 : Blo 2233435 17200673 := bstep (se 2 (by rfl) ⟨6450252, by rfl⟩ : syracuseStep 17200673 = 12900505) B12900505
theorem B11467115 : Blo 2233435 11467115 := bstep (se 1 (by rfl) ⟨8600336, by rfl⟩ : syracuseStep 11467115 = 17200673) B17200673
theorem B7644743 : Blo 2233435 7644743 := bstep (se 1 (by rfl) ⟨5733557, by rfl⟩ : syracuseStep 7644743 = 11467115) B11467115
theorem B5096495 : Blo 2233435 5096495 := bstep (se 1 (by rfl) ⟨3822371, by rfl⟩ : syracuseStep 5096495 = 7644743) B7644743
theorem B3397663 : Blo 2233435 3397663 := bstep (se 1 (by rfl) ⟨2548247, by rfl⟩ : syracuseStep 3397663 = 5096495) B5096495
theorem B4530217 : Blo 2233435 4530217 := bstep (se 2 (by rfl) ⟨1698831, by rfl⟩ : syracuseStep 4530217 = 3397663) B3397663
theorem B6040289 : Blo 2233435 6040289 := bstep (se 2 (by rfl) ⟨2265108, by rfl⟩ : syracuseStep 6040289 = 4530217) B4530217
theorem B16107437 : Blo 2233435 16107437 := bstep (se 3 (by rfl) ⟨3020144, by rfl⟩ : syracuseStep 16107437 = 6040289) B6040289
theorem B10738291 : Blo 2233435 10738291 := bstep (se 1 (by rfl) ⟨8053718, by rfl⟩ : syracuseStep 10738291 = 16107437) B16107437
theorem B14317721 : Blo 2233435 14317721 := bstep (se 2 (by rfl) ⟨5369145, by rfl⟩ : syracuseStep 14317721 = 10738291) B10738291
theorem B9545147 : Blo 2233435 9545147 := bstep (se 1 (by rfl) ⟨7158860, by rfl⟩ : syracuseStep 9545147 = 14317721) B14317721
theorem B6363431 : Blo 2233435 6363431 := bstep (se 1 (by rfl) ⟨4772573, by rfl⟩ : syracuseStep 6363431 = 9545147) B9545147
theorem B4242287 : Blo 2233435 4242287 := bstep (se 1 (by rfl) ⟨3181715, by rfl⟩ : syracuseStep 4242287 = 6363431) B6363431
theorem B2828191 : Blo 2233435 2828191 := bstep (se 1 (by rfl) ⟨2121143, by rfl⟩ : syracuseStep 2828191 = 4242287) B4242287
theorem B3770921 : Blo 2233435 3770921 := bstep (se 2 (by rfl) ⟨1414095, by rfl⟩ : syracuseStep 3770921 = 2828191) B2828191
theorem B2513947 : Blo 2233435 2513947 := bstep (se 1 (by rfl) ⟨1885460, by rfl⟩ : syracuseStep 2513947 = 3770921) B3770921
theorem B3351929 : Blo 2233435 3351929 := bstep (se 2 (by rfl) ⟨1256973, by rfl⟩ : syracuseStep 3351929 = 2513947) B2513947
theorem B2234619 : Blo 2233435 2234619 := bstep (se 1 (by rfl) ⟨1675964, by rfl⟩ : syracuseStep 2234619 = 3351929) B3351929
theorem B3020149 : Blo 2233435 3020149 := bbase (se 5 (by rfl) ⟨141569, by rfl⟩ : syracuseStep 3020149 = 283139) (by norm_num)
theorem B16107461 : Blo 2233435 16107461 := bstep (se 4 (by rfl) ⟨1510074, by rfl⟩ : syracuseStep 16107461 = 3020149) B3020149
theorem B10738307 : Blo 2233435 10738307 := bstep (se 1 (by rfl) ⟨8053730, by rfl⟩ : syracuseStep 10738307 = 16107461) B16107461
theorem B7158871 : Blo 2233435 7158871 := bstep (se 1 (by rfl) ⟨5369153, by rfl⟩ : syracuseStep 7158871 = 10738307) B10738307
theorem B38180645 : Blo 2233435 38180645 := bstep (se 4 (by rfl) ⟨3579435, by rfl⟩ : syracuseStep 38180645 = 7158871) B7158871
theorem B25453763 : Blo 2233435 25453763 := bstep (se 1 (by rfl) ⟨19090322, by rfl⟩ : syracuseStep 25453763 = 38180645) B38180645
theorem B16969175 : Blo 2233435 16969175 := bstep (se 1 (by rfl) ⟨12726881, by rfl⟩ : syracuseStep 16969175 = 25453763) B25453763
theorem B11312783 : Blo 2233435 11312783 := bstep (se 1 (by rfl) ⟨8484587, by rfl⟩ : syracuseStep 11312783 = 16969175) B16969175
theorem B7541855 : Blo 2233435 7541855 := bstep (se 1 (by rfl) ⟨5656391, by rfl⟩ : syracuseStep 7541855 = 11312783) B11312783
theorem B5027903 : Blo 2233435 5027903 := bstep (se 1 (by rfl) ⟨3770927, by rfl⟩ : syracuseStep 5027903 = 7541855) B7541855
theorem B3351935 : Blo 2233435 3351935 := bstep (se 1 (by rfl) ⟨2513951, by rfl⟩ : syracuseStep 3351935 = 5027903) B5027903
theorem B2234623 : Blo 2233435 2234623 := bstep (se 1 (by rfl) ⟨1675967, by rfl⟩ : syracuseStep 2234623 = 3351935) B3351935
theorem B3351941 : Blo 2233435 3351941 := bbase (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) (by norm_num)
theorem B2234627 : Blo 2233435 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B3770941 : Blo 2233435 3770941 := bbase (se 3 (by rfl) ⟨707051, by rfl⟩ : syracuseStep 3770941 = 1414103) (by norm_num)
theorem B5027921 : Blo 2233435 5027921 := bstep (se 2 (by rfl) ⟨1885470, by rfl⟩ : syracuseStep 5027921 = 3770941) B3770941
theorem B3351947 : Blo 2233435 3351947 := bstep (se 1 (by rfl) ⟨2513960, by rfl⟩ : syracuseStep 3351947 = 5027921) B5027921
theorem B2234631 : Blo 2233435 2234631 := bstep (se 1 (by rfl) ⟨1675973, by rfl⟩ : syracuseStep 2234631 = 3351947) B3351947
theorem B2513965 : Blo 2233435 2513965 := bbase (se 3 (by rfl) ⟨471368, by rfl⟩ : syracuseStep 2513965 = 942737) (by norm_num)
theorem B3351953 : Blo 2233435 3351953 := bstep (se 2 (by rfl) ⟨1256982, by rfl⟩ : syracuseStep 3351953 = 2513965) B2513965
theorem B2234635 : Blo 2233435 2234635 := bstep (se 1 (by rfl) ⟨1675976, by rfl⟩ : syracuseStep 2234635 = 3351953) B3351953
theorem B7541909 : Blo 2233435 7541909 := bbase (se 6 (by rfl) ⟨176763, by rfl⟩ : syracuseStep 7541909 = 353527) (by norm_num)
theorem B5027939 : Blo 2233435 5027939 := bstep (se 1 (by rfl) ⟨3770954, by rfl⟩ : syracuseStep 5027939 = 7541909) B7541909
theorem B3351959 : Blo 2233435 3351959 := bstep (se 1 (by rfl) ⟨2513969, by rfl⟩ : syracuseStep 3351959 = 5027939) B5027939
theorem B2234639 : Blo 2233435 2234639 := bstep (se 1 (by rfl) ⟨1675979, by rfl⟩ : syracuseStep 2234639 = 3351959) B3351959
theorem B3351965 : Blo 2233435 3351965 := bbase (se 3 (by rfl) ⟨628493, by rfl⟩ : syracuseStep 3351965 = 1256987) (by norm_num)
theorem B2234643 : Blo 2233435 2234643 := bstep (se 1 (by rfl) ⟨1675982, by rfl⟩ : syracuseStep 2234643 = 3351965) B3351965
theorem B5027957 : Blo 2233435 5027957 := bbase (se 5 (by rfl) ⟨235685, by rfl⟩ : syracuseStep 5027957 = 471371) (by norm_num)
theorem B3351971 : Blo 2233435 3351971 := bstep (se 1 (by rfl) ⟨2513978, by rfl⟩ : syracuseStep 3351971 = 5027957) B5027957
theorem B2234647 : Blo 2233435 2234647 := bstep (se 1 (by rfl) ⟨1675985, by rfl⟩ : syracuseStep 2234647 = 3351971) B3351971
theorem B4026917 : Blo 2233435 4026917 := bbase (se 4 (by rfl) ⟨377523, by rfl⟩ : syracuseStep 4026917 = 755047) (by norm_num)
theorem B2684611 : Blo 2233435 2684611 := bstep (se 1 (by rfl) ⟨2013458, by rfl⟩ : syracuseStep 2684611 = 4026917) B4026917
theorem B3579481 : Blo 2233435 3579481 := bstep (se 2 (by rfl) ⟨1342305, by rfl⟩ : syracuseStep 3579481 = 2684611) B2684611
theorem B19090565 : Blo 2233435 19090565 := bstep (se 4 (by rfl) ⟨1789740, by rfl⟩ : syracuseStep 19090565 = 3579481) B3579481
theorem B12727043 : Blo 2233435 12727043 := bstep (se 1 (by rfl) ⟨9545282, by rfl⟩ : syracuseStep 12727043 = 19090565) B19090565
theorem B8484695 : Blo 2233435 8484695 := bstep (se 1 (by rfl) ⟨6363521, by rfl⟩ : syracuseStep 8484695 = 12727043) B12727043
theorem B5656463 : Blo 2233435 5656463 := bstep (se 1 (by rfl) ⟨4242347, by rfl⟩ : syracuseStep 5656463 = 8484695) B8484695
theorem B3770975 : Blo 2233435 3770975 := bstep (se 1 (by rfl) ⟨2828231, by rfl⟩ : syracuseStep 3770975 = 5656463) B5656463
theorem B2513983 : Blo 2233435 2513983 := bstep (se 1 (by rfl) ⟨1885487, by rfl⟩ : syracuseStep 2513983 = 3770975) B3770975
theorem B3351977 : Blo 2233435 3351977 := bstep (se 2 (by rfl) ⟨1256991, by rfl⟩ : syracuseStep 3351977 = 2513983) B2513983
theorem B2234651 : Blo 2233435 2234651 := bstep (se 1 (by rfl) ⟨1675988, by rfl⟩ : syracuseStep 2234651 = 3351977) B3351977
theorem B8484709 : Blo 2233435 8484709 := bbase (se 4 (by rfl) ⟨795441, by rfl⟩ : syracuseStep 8484709 = 1590883) (by norm_num)
theorem B11312945 : Blo 2233435 11312945 := bstep (se 2 (by rfl) ⟨4242354, by rfl⟩ : syracuseStep 11312945 = 8484709) B8484709
theorem B7541963 : Blo 2233435 7541963 := bstep (se 1 (by rfl) ⟨5656472, by rfl⟩ : syracuseStep 7541963 = 11312945) B11312945
theorem B5027975 : Blo 2233435 5027975 := bstep (se 1 (by rfl) ⟨3770981, by rfl⟩ : syracuseStep 5027975 = 7541963) B7541963
theorem B3351983 : Blo 2233435 3351983 := bstep (se 1 (by rfl) ⟨2513987, by rfl⟩ : syracuseStep 3351983 = 5027975) B5027975
theorem B2234655 : Blo 2233435 2234655 := bstep (se 1 (by rfl) ⟨1675991, by rfl⟩ : syracuseStep 2234655 = 3351983) B3351983
theorem B3351989 : Blo 2233435 3351989 := bbase (se 5 (by rfl) ⟨157124, by rfl⟩ : syracuseStep 3351989 = 314249) (by norm_num)
theorem B2234659 : Blo 2233435 2234659 := bstep (se 1 (by rfl) ⟨1675994, by rfl⟩ : syracuseStep 2234659 = 3351989) B3351989
theorem B5656493 : Blo 2233435 5656493 := bbase (se 3 (by rfl) ⟨1060592, by rfl⟩ : syracuseStep 5656493 = 2121185) (by norm_num)
theorem B3770995 : Blo 2233435 3770995 := bstep (se 1 (by rfl) ⟨2828246, by rfl⟩ : syracuseStep 3770995 = 5656493) B5656493
theorem B5027993 : Blo 2233435 5027993 := bstep (se 2 (by rfl) ⟨1885497, by rfl⟩ : syracuseStep 5027993 = 3770995) B3770995
theorem B3351995 : Blo 2233435 3351995 := bstep (se 1 (by rfl) ⟨2513996, by rfl⟩ : syracuseStep 3351995 = 5027993) B5027993
theorem B2234663 : Blo 2233435 2234663 := bstep (se 1 (by rfl) ⟨1675997, by rfl⟩ : syracuseStep 2234663 = 3351995) B3351995
theorem B2514001 : Blo 2233435 2514001 := bbase (se 2 (by rfl) ⟨942750, by rfl⟩ : syracuseStep 2514001 = 1885501) (by norm_num)
theorem B3352001 : Blo 2233435 3352001 := bstep (se 2 (by rfl) ⟨1257000, by rfl⟩ : syracuseStep 3352001 = 2514001) B2514001
theorem B2234667 : Blo 2233435 2234667 := bstep (se 1 (by rfl) ⟨1676000, by rfl⟩ : syracuseStep 2234667 = 3352001) B3352001
theorem B3181789 : Blo 2233435 3181789 := bbase (se 3 (by rfl) ⟨596585, by rfl⟩ : syracuseStep 3181789 = 1193171) (by norm_num)
theorem B4242385 : Blo 2233435 4242385 := bstep (se 2 (by rfl) ⟨1590894, by rfl⟩ : syracuseStep 4242385 = 3181789) B3181789
theorem B5656513 : Blo 2233435 5656513 := bstep (se 2 (by rfl) ⟨2121192, by rfl⟩ : syracuseStep 5656513 = 4242385) B4242385
theorem B7542017 : Blo 2233435 7542017 := bstep (se 2 (by rfl) ⟨2828256, by rfl⟩ : syracuseStep 7542017 = 5656513) B5656513
theorem B5028011 : Blo 2233435 5028011 := bstep (se 1 (by rfl) ⟨3771008, by rfl⟩ : syracuseStep 5028011 = 7542017) B7542017
theorem B3352007 : Blo 2233435 3352007 := bstep (se 1 (by rfl) ⟨2514005, by rfl⟩ : syracuseStep 3352007 = 5028011) B5028011
theorem B2234671 : Blo 2233435 2234671 := bstep (se 1 (by rfl) ⟨1676003, by rfl⟩ : syracuseStep 2234671 = 3352007) B3352007
theorem B3352013 : Blo 2233435 3352013 := bbase (se 3 (by rfl) ⟨628502, by rfl⟩ : syracuseStep 3352013 = 1257005) (by norm_num)
theorem B2234675 : Blo 2233435 2234675 := bstep (se 1 (by rfl) ⟨1676006, by rfl⟩ : syracuseStep 2234675 = 3352013) B3352013
theorem B5028029 : Blo 2233435 5028029 := bbase (se 3 (by rfl) ⟨942755, by rfl⟩ : syracuseStep 5028029 = 1885511) (by norm_num)
theorem B3352019 : Blo 2233435 3352019 := bstep (se 1 (by rfl) ⟨2514014, by rfl⟩ : syracuseStep 3352019 = 5028029) B5028029
theorem B2234679 : Blo 2233435 2234679 := bstep (se 1 (by rfl) ⟨1676009, by rfl⟩ : syracuseStep 2234679 = 3352019) B3352019
theorem B3771029 : Blo 2233435 3771029 := bbase (se 6 (by rfl) ⟨88383, by rfl⟩ : syracuseStep 3771029 = 176767) (by norm_num)
theorem B2514019 : Blo 2233435 2514019 := bstep (se 1 (by rfl) ⟨1885514, by rfl⟩ : syracuseStep 2514019 = 3771029) B3771029
theorem B3352025 : Blo 2233435 3352025 := bstep (se 2 (by rfl) ⟨1257009, by rfl⟩ : syracuseStep 3352025 = 2514019) B2514019
theorem B2234683 : Blo 2233435 2234683 := bstep (se 1 (by rfl) ⟨1676012, by rfl⟩ : syracuseStep 2234683 = 3352025) B3352025
theorem B13591061 : Blo 2233435 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B9060707 : Blo 2233435 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B24161885 : Blo 2233435 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B16107923 : Blo 2233435 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B10738615 : Blo 2233435 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B14318153 : Blo 2233435 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B9545435 : Blo 2233435 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B6363623 : Blo 2233435 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B16969661 : Blo 2233435 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B11313107 : Blo 2233435 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B7542071 : Blo 2233435 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B5028047 : Blo 2233435 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B3352031 : Blo 2233435 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B2234687 : Blo 2233435 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B3352037 : Blo 2233435 3352037 := bbase (se 4 (by rfl) ⟨314253, by rfl⟩ : syracuseStep 3352037 = 628507) (by norm_num)
theorem B2234691 : Blo 2233435 2234691 := bstep (se 1 (by rfl) ⟨1676018, by rfl⟩ : syracuseStep 2234691 = 3352037) B3352037
theorem B6450469 : Blo 2233435 6450469 := bbase (se 4 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 6450469 = 1209463) (by norm_num)
theorem B34402501 : Blo 2233435 34402501 := bstep (se 4 (by rfl) ⟨3225234, by rfl⟩ : syracuseStep 34402501 = 6450469) B6450469
theorem B183480005 : Blo 2233435 183480005 := bstep (se 4 (by rfl) ⟨17201250, by rfl⟩ : syracuseStep 183480005 = 34402501) B34402501
theorem B122320003 : Blo 2233435 122320003 := bstep (se 1 (by rfl) ⟨91740002, by rfl⟩ : syracuseStep 122320003 = 183480005) B183480005
theorem B163093337 : Blo 2233435 163093337 := bstep (se 2 (by rfl) ⟨61160001, by rfl⟩ : syracuseStep 163093337 = 122320003) B122320003
theorem B108728891 : Blo 2233435 108728891 := bstep (se 1 (by rfl) ⟨81546668, by rfl⟩ : syracuseStep 108728891 = 163093337) B163093337
theorem B72485927 : Blo 2233435 72485927 := bstep (se 1 (by rfl) ⟨54364445, by rfl⟩ : syracuseStep 72485927 = 108728891) B108728891
theorem B48323951 : Blo 2233435 48323951 := bstep (se 1 (by rfl) ⟨36242963, by rfl⟩ : syracuseStep 48323951 = 72485927) B72485927
theorem B32215967 : Blo 2233435 32215967 := bstep (se 1 (by rfl) ⟨24161975, by rfl⟩ : syracuseStep 32215967 = 48323951) B48323951
theorem B21477311 : Blo 2233435 21477311 := bstep (se 1 (by rfl) ⟨16107983, by rfl⟩ : syracuseStep 21477311 = 32215967) B32215967
theorem B14318207 : Blo 2233435 14318207 := bstep (se 1 (by rfl) ⟨10738655, by rfl⟩ : syracuseStep 14318207 = 21477311) B21477311
theorem B9545471 : Blo 2233435 9545471 := bstep (se 1 (by rfl) ⟨7159103, by rfl⟩ : syracuseStep 9545471 = 14318207) B14318207
theorem B6363647 : Blo 2233435 6363647 := bstep (se 1 (by rfl) ⟨4772735, by rfl⟩ : syracuseStep 6363647 = 9545471) B9545471
theorem B4242431 : Blo 2233435 4242431 := bstep (se 1 (by rfl) ⟨3181823, by rfl⟩ : syracuseStep 4242431 = 6363647) B6363647
theorem B2828287 : Blo 2233435 2828287 := bstep (se 1 (by rfl) ⟨2121215, by rfl⟩ : syracuseStep 2828287 = 4242431) B4242431
theorem B3771049 : Blo 2233435 3771049 := bstep (se 2 (by rfl) ⟨1414143, by rfl⟩ : syracuseStep 3771049 = 2828287) B2828287
theorem B5028065 : Blo 2233435 5028065 := bstep (se 2 (by rfl) ⟨1885524, by rfl⟩ : syracuseStep 5028065 = 3771049) B3771049
theorem B3352043 : Blo 2233435 3352043 := bstep (se 1 (by rfl) ⟨2514032, by rfl⟩ : syracuseStep 3352043 = 5028065) B5028065
theorem B2234695 : Blo 2233435 2234695 := bstep (se 1 (by rfl) ⟨1676021, by rfl⟩ : syracuseStep 2234695 = 3352043) B3352043
theorem B2514037 : Blo 2233435 2514037 := bbase (se 5 (by rfl) ⟨117845, by rfl⟩ : syracuseStep 2514037 = 235691) (by norm_num)
theorem B3352049 : Blo 2233435 3352049 := bstep (se 2 (by rfl) ⟨1257018, by rfl⟩ : syracuseStep 3352049 = 2514037) B2514037
theorem B2234699 : Blo 2233435 2234699 := bstep (se 1 (by rfl) ⟨1676024, by rfl⟩ : syracuseStep 2234699 = 3352049) B3352049
theorem B2828297 : Blo 2233435 2828297 := bbase (se 2 (by rfl) ⟨1060611, by rfl⟩ : syracuseStep 2828297 = 2121223) (by norm_num)
theorem B7542125 : Blo 2233435 7542125 := bstep (se 3 (by rfl) ⟨1414148, by rfl⟩ : syracuseStep 7542125 = 2828297) B2828297
theorem B5028083 : Blo 2233435 5028083 := bstep (se 1 (by rfl) ⟨3771062, by rfl⟩ : syracuseStep 5028083 = 7542125) B7542125
theorem B3352055 : Blo 2233435 3352055 := bstep (se 1 (by rfl) ⟨2514041, by rfl⟩ : syracuseStep 3352055 = 5028083) B5028083
theorem B2234703 : Blo 2233435 2234703 := bstep (se 1 (by rfl) ⟨1676027, by rfl⟩ : syracuseStep 2234703 = 3352055) B3352055
theorem B3352061 : Blo 2233435 3352061 := bbase (se 3 (by rfl) ⟨628511, by rfl⟩ : syracuseStep 3352061 = 1257023) (by norm_num)
theorem B2234707 : Blo 2233435 2234707 := bstep (se 1 (by rfl) ⟨1676030, by rfl⟩ : syracuseStep 2234707 = 3352061) B3352061
theorem B5028101 : Blo 2233435 5028101 := bbase (se 4 (by rfl) ⟨471384, by rfl⟩ : syracuseStep 5028101 = 942769) (by norm_num)
theorem B3352067 : Blo 2233435 3352067 := bstep (se 1 (by rfl) ⟨2514050, by rfl⟩ : syracuseStep 3352067 = 5028101) B5028101
theorem B2234711 : Blo 2233435 2234711 := bstep (se 1 (by rfl) ⟨1676033, by rfl⟩ : syracuseStep 2234711 = 3352067) B3352067
theorem B4242469 : Blo 2233435 4242469 := bbase (se 4 (by rfl) ⟨397731, by rfl⟩ : syracuseStep 4242469 = 795463) (by norm_num)
theorem B5656625 : Blo 2233435 5656625 := bstep (se 2 (by rfl) ⟨2121234, by rfl⟩ : syracuseStep 5656625 = 4242469) B4242469
theorem B3771083 : Blo 2233435 3771083 := bstep (se 1 (by rfl) ⟨2828312, by rfl⟩ : syracuseStep 3771083 = 5656625) B5656625
theorem B2514055 : Blo 2233435 2514055 := bstep (se 1 (by rfl) ⟨1885541, by rfl⟩ : syracuseStep 2514055 = 3771083) B3771083
theorem B3352073 : Blo 2233435 3352073 := bstep (se 2 (by rfl) ⟨1257027, by rfl⟩ : syracuseStep 3352073 = 2514055) B2514055
theorem B2234715 : Blo 2233435 2234715 := bstep (se 1 (by rfl) ⟨1676036, by rfl⟩ : syracuseStep 2234715 = 3352073) B3352073
theorem B11313269 : Blo 2233435 11313269 := bbase (se 5 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 11313269 = 1060619) (by norm_num)
theorem B7542179 : Blo 2233435 7542179 := bstep (se 1 (by rfl) ⟨5656634, by rfl⟩ : syracuseStep 7542179 = 11313269) B11313269
theorem B5028119 : Blo 2233435 5028119 := bstep (se 1 (by rfl) ⟨3771089, by rfl⟩ : syracuseStep 5028119 = 7542179) B7542179
theorem B3352079 : Blo 2233435 3352079 := bstep (se 1 (by rfl) ⟨2514059, by rfl⟩ : syracuseStep 3352079 = 5028119) B5028119
theorem B2234719 : Blo 2233435 2234719 := bstep (se 1 (by rfl) ⟨1676039, by rfl⟩ : syracuseStep 2234719 = 3352079) B3352079
theorem B3352085 : Blo 2233435 3352085 := bbase (se 6 (by rfl) ⟨78564, by rfl⟩ : syracuseStep 3352085 = 157129) (by norm_num)
theorem B2234723 : Blo 2233435 2234723 := bstep (se 1 (by rfl) ⟨1676042, by rfl⟩ : syracuseStep 2234723 = 3352085) B3352085
theorem B7159205 : Blo 2233435 7159205 := bbase (se 4 (by rfl) ⟨671175, by rfl⟩ : syracuseStep 7159205 = 1342351) (by norm_num)
theorem B19091213 : Blo 2233435 19091213 := bstep (se 3 (by rfl) ⟨3579602, by rfl⟩ : syracuseStep 19091213 = 7159205) B7159205
theorem B12727475 : Blo 2233435 12727475 := bstep (se 1 (by rfl) ⟨9545606, by rfl⟩ : syracuseStep 12727475 = 19091213) B19091213
theorem B8484983 : Blo 2233435 8484983 := bstep (se 1 (by rfl) ⟨6363737, by rfl⟩ : syracuseStep 8484983 = 12727475) B12727475
theorem B5656655 : Blo 2233435 5656655 := bstep (se 1 (by rfl) ⟨4242491, by rfl⟩ : syracuseStep 5656655 = 8484983) B8484983
theorem B3771103 : Blo 2233435 3771103 := bstep (se 1 (by rfl) ⟨2828327, by rfl⟩ : syracuseStep 3771103 = 5656655) B5656655
theorem B5028137 : Blo 2233435 5028137 := bstep (se 2 (by rfl) ⟨1885551, by rfl⟩ : syracuseStep 5028137 = 3771103) B3771103
theorem B3352091 : Blo 2233435 3352091 := bstep (se 1 (by rfl) ⟨2514068, by rfl⟩ : syracuseStep 3352091 = 5028137) B5028137
theorem B2234727 : Blo 2233435 2234727 := bstep (se 1 (by rfl) ⟨1676045, by rfl⟩ : syracuseStep 2234727 = 3352091) B3352091
theorem B2514073 : Blo 2233435 2514073 := bbase (se 2 (by rfl) ⟨942777, by rfl⟩ : syracuseStep 2514073 = 1885555) (by norm_num)
theorem B3352097 : Blo 2233435 3352097 := bstep (se 2 (by rfl) ⟨1257036, by rfl⟩ : syracuseStep 3352097 = 2514073) B2514073
theorem B2234731 : Blo 2233435 2234731 := bstep (se 1 (by rfl) ⟨1676048, by rfl⟩ : syracuseStep 2234731 = 3352097) B3352097
theorem B8485013 : Blo 2233435 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B5656675 : Blo 2233435 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B7542233 : Blo 2233435 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B5028155 : Blo 2233435 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B3352103 : Blo 2233435 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B2234735 : Blo 2233435 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B3352109 : Blo 2233435 3352109 := bbase (se 3 (by rfl) ⟨628520, by rfl⟩ : syracuseStep 3352109 = 1257041) (by norm_num)
theorem B2234739 : Blo 2233435 2234739 := bstep (se 1 (by rfl) ⟨1676054, by rfl⟩ : syracuseStep 2234739 = 3352109) B3352109
theorem B5028173 : Blo 2233435 5028173 := bbase (se 3 (by rfl) ⟨942782, by rfl⟩ : syracuseStep 5028173 = 1885565) (by norm_num)
theorem B3352115 : Blo 2233435 3352115 := bstep (se 1 (by rfl) ⟨2514086, by rfl⟩ : syracuseStep 3352115 = 5028173) B5028173
theorem B2234743 : Blo 2233435 2234743 := bstep (se 1 (by rfl) ⟨1676057, by rfl⟩ : syracuseStep 2234743 = 3352115) B3352115
theorem B2828353 : Blo 2233435 2828353 := bbase (se 2 (by rfl) ⟨1060632, by rfl⟩ : syracuseStep 2828353 = 2121265) (by norm_num)
theorem B3771137 : Blo 2233435 3771137 := bstep (se 2 (by rfl) ⟨1414176, by rfl⟩ : syracuseStep 3771137 = 2828353) B2828353
theorem B2514091 : Blo 2233435 2514091 := bstep (se 1 (by rfl) ⟨1885568, by rfl⟩ : syracuseStep 2514091 = 3771137) B3771137
theorem B3352121 : Blo 2233435 3352121 := bstep (se 2 (by rfl) ⟨1257045, by rfl⟩ : syracuseStep 3352121 = 2514091) B2514091
theorem B2234747 : Blo 2233435 2234747 := bstep (se 1 (by rfl) ⟨1676060, by rfl⟩ : syracuseStep 2234747 = 3352121) B3352121
theorem B4530485 : Blo 2233435 4530485 := bbase (se 5 (by rfl) ⟨212366, by rfl⟩ : syracuseStep 4530485 = 424733) (by norm_num)
theorem B3020323 : Blo 2233435 3020323 := bstep (se 1 (by rfl) ⟨2265242, by rfl⟩ : syracuseStep 3020323 = 4530485) B4530485
theorem B4027097 : Blo 2233435 4027097 := bstep (se 2 (by rfl) ⟨1510161, by rfl⟩ : syracuseStep 4027097 = 3020323) B3020323
theorem B2684731 : Blo 2233435 2684731 := bstep (se 1 (by rfl) ⟨2013548, by rfl⟩ : syracuseStep 2684731 = 4027097) B4027097
theorem B3579641 : Blo 2233435 3579641 := bstep (se 2 (by rfl) ⟨1342365, by rfl⟩ : syracuseStep 3579641 = 2684731) B2684731
theorem B2386427 : Blo 2233435 2386427 := bstep (se 1 (by rfl) ⟨1789820, by rfl⟩ : syracuseStep 2386427 = 3579641) B3579641
theorem B25455221 : Blo 2233435 25455221 := bstep (se 5 (by rfl) ⟨1193213, by rfl⟩ : syracuseStep 25455221 = 2386427) B2386427
theorem B16970147 : Blo 2233435 16970147 := bstep (se 1 (by rfl) ⟨12727610, by rfl⟩ : syracuseStep 16970147 = 25455221) B25455221
theorem B11313431 : Blo 2233435 11313431 := bstep (se 1 (by rfl) ⟨8485073, by rfl⟩ : syracuseStep 11313431 = 16970147) B16970147
theorem B7542287 : Blo 2233435 7542287 := bstep (se 1 (by rfl) ⟨5656715, by rfl⟩ : syracuseStep 7542287 = 11313431) B11313431
theorem B5028191 : Blo 2233435 5028191 := bstep (se 1 (by rfl) ⟨3771143, by rfl⟩ : syracuseStep 5028191 = 7542287) B7542287
theorem B3352127 : Blo 2233435 3352127 := bstep (se 1 (by rfl) ⟨2514095, by rfl⟩ : syracuseStep 3352127 = 5028191) B5028191
theorem B2234751 : Blo 2233435 2234751 := bstep (se 1 (by rfl) ⟨1676063, by rfl⟩ : syracuseStep 2234751 = 3352127) B3352127
theorem B3352133 : Blo 2233435 3352133 := bbase (se 4 (by rfl) ⟨314262, by rfl⟩ : syracuseStep 3352133 = 628525) (by norm_num)
theorem B2234755 : Blo 2233435 2234755 := bstep (se 1 (by rfl) ⟨1676066, by rfl⟩ : syracuseStep 2234755 = 3352133) B3352133
theorem B3771157 : Blo 2233435 3771157 := bbase (se 6 (by rfl) ⟨88386, by rfl⟩ : syracuseStep 3771157 = 176773) (by norm_num)
theorem B5028209 : Blo 2233435 5028209 := bstep (se 2 (by rfl) ⟨1885578, by rfl⟩ : syracuseStep 5028209 = 3771157) B3771157
theorem B3352139 : Blo 2233435 3352139 := bstep (se 1 (by rfl) ⟨2514104, by rfl⟩ : syracuseStep 3352139 = 5028209) B5028209
theorem B2234759 : Blo 2233435 2234759 := bstep (se 1 (by rfl) ⟨1676069, by rfl⟩ : syracuseStep 2234759 = 3352139) B3352139
theorem B2514109 : Blo 2233435 2514109 := bbase (se 3 (by rfl) ⟨471395, by rfl⟩ : syracuseStep 2514109 = 942791) (by norm_num)
theorem B3352145 : Blo 2233435 3352145 := bstep (se 2 (by rfl) ⟨1257054, by rfl⟩ : syracuseStep 3352145 = 2514109) B2514109
theorem B2234763 : Blo 2233435 2234763 := bstep (se 1 (by rfl) ⟨1676072, by rfl⟩ : syracuseStep 2234763 = 3352145) B3352145
theorem B7542341 : Blo 2233435 7542341 := bbase (se 4 (by rfl) ⟨707094, by rfl⟩ : syracuseStep 7542341 = 1414189) (by norm_num)
theorem B5028227 : Blo 2233435 5028227 := bstep (se 1 (by rfl) ⟨3771170, by rfl⟩ : syracuseStep 5028227 = 7542341) B7542341
theorem B3352151 : Blo 2233435 3352151 := bstep (se 1 (by rfl) ⟨2514113, by rfl⟩ : syracuseStep 3352151 = 5028227) B5028227
theorem B2234767 : Blo 2233435 2234767 := bstep (se 1 (by rfl) ⟨1676075, by rfl⟩ : syracuseStep 2234767 = 3352151) B3352151
theorem B3352157 : Blo 2233435 3352157 := bbase (se 3 (by rfl) ⟨628529, by rfl⟩ : syracuseStep 3352157 = 1257059) (by norm_num)
theorem B2234771 : Blo 2233435 2234771 := bstep (se 1 (by rfl) ⟨1676078, by rfl⟩ : syracuseStep 2234771 = 3352157) B3352157
theorem B5028245 : Blo 2233435 5028245 := bbase (se 6 (by rfl) ⟨117849, by rfl⟩ : syracuseStep 5028245 = 235699) (by norm_num)
theorem B3352163 : Blo 2233435 3352163 := bstep (se 1 (by rfl) ⟨2514122, by rfl⟩ : syracuseStep 3352163 = 5028245) B5028245
theorem B2234775 : Blo 2233435 2234775 := bstep (se 1 (by rfl) ⟨1676081, by rfl⟩ : syracuseStep 2234775 = 3352163) B3352163
theorem B2684765 : Blo 2233435 2684765 := bbase (se 3 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 2684765 = 1006787) (by norm_num)
theorem B7159373 : Blo 2233435 7159373 := bstep (se 3 (by rfl) ⟨1342382, by rfl⟩ : syracuseStep 7159373 = 2684765) B2684765
theorem B4772915 : Blo 2233435 4772915 := bstep (se 1 (by rfl) ⟨3579686, by rfl⟩ : syracuseStep 4772915 = 7159373) B7159373
theorem B3181943 : Blo 2233435 3181943 := bstep (se 1 (by rfl) ⟨2386457, by rfl⟩ : syracuseStep 3181943 = 4772915) B4772915
theorem B8485181 : Blo 2233435 8485181 := bstep (se 3 (by rfl) ⟨1590971, by rfl⟩ : syracuseStep 8485181 = 3181943) B3181943
theorem B5656787 : Blo 2233435 5656787 := bstep (se 1 (by rfl) ⟨4242590, by rfl⟩ : syracuseStep 5656787 = 8485181) B8485181
theorem B3771191 : Blo 2233435 3771191 := bstep (se 1 (by rfl) ⟨2828393, by rfl⟩ : syracuseStep 3771191 = 5656787) B5656787
theorem B2514127 : Blo 2233435 2514127 := bstep (se 1 (by rfl) ⟨1885595, by rfl⟩ : syracuseStep 2514127 = 3771191) B3771191
theorem B3352169 : Blo 2233435 3352169 := bstep (se 2 (by rfl) ⟨1257063, by rfl⟩ : syracuseStep 3352169 = 2514127) B2514127
theorem B2234779 : Blo 2233435 2234779 := bstep (se 1 (by rfl) ⟨1676084, by rfl⟩ : syracuseStep 2234779 = 3352169) B3352169
theorem B9545845 : Blo 2233435 9545845 := bbase (se 5 (by rfl) ⟨447461, by rfl⟩ : syracuseStep 9545845 = 894923) (by norm_num)
theorem B12727793 : Blo 2233435 12727793 := bstep (se 2 (by rfl) ⟨4772922, by rfl⟩ : syracuseStep 12727793 = 9545845) B9545845
theorem B8485195 : Blo 2233435 8485195 := bstep (se 1 (by rfl) ⟨6363896, by rfl⟩ : syracuseStep 8485195 = 12727793) B12727793
theorem B11313593 : Blo 2233435 11313593 := bstep (se 2 (by rfl) ⟨4242597, by rfl⟩ : syracuseStep 11313593 = 8485195) B8485195
theorem B7542395 : Blo 2233435 7542395 := bstep (se 1 (by rfl) ⟨5656796, by rfl⟩ : syracuseStep 7542395 = 11313593) B11313593
theorem B5028263 : Blo 2233435 5028263 := bstep (se 1 (by rfl) ⟨3771197, by rfl⟩ : syracuseStep 5028263 = 7542395) B7542395
theorem B3352175 : Blo 2233435 3352175 := bstep (se 1 (by rfl) ⟨2514131, by rfl⟩ : syracuseStep 3352175 = 5028263) B5028263
theorem B2234783 : Blo 2233435 2234783 := bstep (se 1 (by rfl) ⟨1676087, by rfl⟩ : syracuseStep 2234783 = 3352175) B3352175
theorem B3352181 : Blo 2233435 3352181 := bbase (se 5 (by rfl) ⟨157133, by rfl⟩ : syracuseStep 3352181 = 314267) (by norm_num)
theorem B2234787 : Blo 2233435 2234787 := bstep (se 1 (by rfl) ⟨1676090, by rfl⟩ : syracuseStep 2234787 = 3352181) B3352181
theorem B4242613 : Blo 2233435 4242613 := bbase (se 5 (by rfl) ⟨198872, by rfl⟩ : syracuseStep 4242613 = 397745) (by norm_num)
theorem B5656817 : Blo 2233435 5656817 := bstep (se 2 (by rfl) ⟨2121306, by rfl⟩ : syracuseStep 5656817 = 4242613) B4242613
theorem B3771211 : Blo 2233435 3771211 := bstep (se 1 (by rfl) ⟨2828408, by rfl⟩ : syracuseStep 3771211 = 5656817) B5656817
theorem B5028281 : Blo 2233435 5028281 := bstep (se 2 (by rfl) ⟨1885605, by rfl⟩ : syracuseStep 5028281 = 3771211) B3771211
theorem B3352187 : Blo 2233435 3352187 := bstep (se 1 (by rfl) ⟨2514140, by rfl⟩ : syracuseStep 3352187 = 5028281) B5028281
theorem B2234791 : Blo 2233435 2234791 := bstep (se 1 (by rfl) ⟨1676093, by rfl⟩ : syracuseStep 2234791 = 3352187) B3352187
theorem B2514145 : Blo 2233435 2514145 := bbase (se 2 (by rfl) ⟨942804, by rfl⟩ : syracuseStep 2514145 = 1885609) (by norm_num)
theorem B3352193 : Blo 2233435 3352193 := bstep (se 2 (by rfl) ⟨1257072, by rfl⟩ : syracuseStep 3352193 = 2514145) B2514145
theorem B2234795 : Blo 2233435 2234795 := bstep (se 1 (by rfl) ⟨1676096, by rfl⟩ : syracuseStep 2234795 = 3352193) B3352193
theorem B5656837 : Blo 2233435 5656837 := bbase (se 4 (by rfl) ⟨530328, by rfl⟩ : syracuseStep 5656837 = 1060657) (by norm_num)
theorem B7542449 : Blo 2233435 7542449 := bstep (se 2 (by rfl) ⟨2828418, by rfl⟩ : syracuseStep 7542449 = 5656837) B5656837
theorem B5028299 : Blo 2233435 5028299 := bstep (se 1 (by rfl) ⟨3771224, by rfl⟩ : syracuseStep 5028299 = 7542449) B7542449
theorem B3352199 : Blo 2233435 3352199 := bstep (se 1 (by rfl) ⟨2514149, by rfl⟩ : syracuseStep 3352199 = 5028299) B5028299
theorem B2234799 : Blo 2233435 2234799 := bstep (se 1 (by rfl) ⟨1676099, by rfl⟩ : syracuseStep 2234799 = 3352199) B3352199
theorem B3352205 : Blo 2233435 3352205 := bbase (se 3 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 3352205 = 1257077) (by norm_num)
theorem B2234803 : Blo 2233435 2234803 := bstep (se 1 (by rfl) ⟨1676102, by rfl⟩ : syracuseStep 2234803 = 3352205) B3352205
theorem B5028317 : Blo 2233435 5028317 := bbase (se 3 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 5028317 = 1885619) (by norm_num)
theorem B3352211 : Blo 2233435 3352211 := bstep (se 1 (by rfl) ⟨2514158, by rfl⟩ : syracuseStep 3352211 = 5028317) B5028317
theorem B2234807 : Blo 2233435 2234807 := bstep (se 1 (by rfl) ⟨1676105, by rfl⟩ : syracuseStep 2234807 = 3352211) B3352211
theorem B3771245 : Blo 2233435 3771245 := bbase (se 3 (by rfl) ⟨707108, by rfl⟩ : syracuseStep 3771245 = 1414217) (by norm_num)
theorem B2514163 : Blo 2233435 2514163 := bstep (se 1 (by rfl) ⟨1885622, by rfl⟩ : syracuseStep 2514163 = 3771245) B3771245
theorem B3352217 : Blo 2233435 3352217 := bstep (se 2 (by rfl) ⟨1257081, by rfl⟩ : syracuseStep 3352217 = 2514163) B2514163
theorem B2234811 : Blo 2233435 2234811 := bstep (se 1 (by rfl) ⟨1676108, by rfl⟩ : syracuseStep 2234811 = 3352217) B3352217
theorem B8736661 : Blo 2233435 8736661 := bbase (se 6 (by rfl) ⟨204765, by rfl⟩ : syracuseStep 8736661 = 409531) (by norm_num)
theorem B11648881 : Blo 2233435 11648881 := bstep (se 2 (by rfl) ⟨4368330, by rfl⟩ : syracuseStep 11648881 = 8736661) B8736661
theorem B15531841 : Blo 2233435 15531841 := bstep (se 2 (by rfl) ⟨5824440, by rfl⟩ : syracuseStep 15531841 = 11648881) B11648881
theorem B20709121 : Blo 2233435 20709121 := bstep (se 2 (by rfl) ⟨7765920, by rfl⟩ : syracuseStep 20709121 = 15531841) B15531841
theorem B27612161 : Blo 2233435 27612161 := bstep (se 2 (by rfl) ⟨10354560, by rfl⟩ : syracuseStep 27612161 = 20709121) B20709121
theorem B18408107 : Blo 2233435 18408107 := bstep (se 1 (by rfl) ⟨13806080, by rfl⟩ : syracuseStep 18408107 = 27612161) B27612161
theorem B12272071 : Blo 2233435 12272071 := bstep (se 1 (by rfl) ⟨9204053, by rfl⟩ : syracuseStep 12272071 = 18408107) B18408107
theorem B16362761 : Blo 2233435 16362761 := bstep (se 2 (by rfl) ⟨6136035, by rfl⟩ : syracuseStep 16362761 = 12272071) B12272071
theorem B174536117 : Blo 2233435 174536117 := bstep (se 5 (by rfl) ⟨8181380, by rfl⟩ : syracuseStep 174536117 = 16362761) B16362761
theorem B116357411 : Blo 2233435 116357411 := bstep (se 1 (by rfl) ⟨87268058, by rfl⟩ : syracuseStep 116357411 = 174536117) B174536117
theorem B77571607 : Blo 2233435 77571607 := bstep (se 1 (by rfl) ⟨58178705, by rfl⟩ : syracuseStep 77571607 = 116357411) B116357411
theorem B103428809 : Blo 2233435 103428809 := bstep (se 2 (by rfl) ⟨38785803, by rfl⟩ : syracuseStep 103428809 = 77571607) B77571607
theorem B68952539 : Blo 2233435 68952539 := bstep (se 1 (by rfl) ⟨51714404, by rfl⟩ : syracuseStep 68952539 = 103428809) B103428809
theorem B45968359 : Blo 2233435 45968359 := bstep (se 1 (by rfl) ⟨34476269, by rfl⟩ : syracuseStep 45968359 = 68952539) B68952539
theorem B61291145 : Blo 2233435 61291145 := bstep (se 2 (by rfl) ⟨22984179, by rfl⟩ : syracuseStep 61291145 = 45968359) B45968359
theorem B40860763 : Blo 2233435 40860763 := bstep (se 1 (by rfl) ⟨30645572, by rfl⟩ : syracuseStep 40860763 = 61291145) B61291145
theorem B217924069 : Blo 2233435 217924069 := bstep (se 4 (by rfl) ⟨20430381, by rfl⟩ : syracuseStep 217924069 = 40860763) B40860763
theorem B290565425 : Blo 2233435 290565425 := bstep (se 2 (by rfl) ⟨108962034, by rfl⟩ : syracuseStep 290565425 = 217924069) B217924069
theorem B774841133 : Blo 2233435 774841133 := bstep (se 3 (by rfl) ⟨145282712, by rfl⟩ : syracuseStep 774841133 = 290565425) B290565425
theorem B516560755 : Blo 2233435 516560755 := bstep (se 1 (by rfl) ⟨387420566, by rfl⟩ : syracuseStep 516560755 = 774841133) B774841133
theorem B688747673 : Blo 2233435 688747673 := bstep (se 2 (by rfl) ⟨258280377, by rfl⟩ : syracuseStep 688747673 = 516560755) B516560755
theorem B459165115 : Blo 2233435 459165115 := bstep (se 1 (by rfl) ⟨344373836, by rfl⟩ : syracuseStep 459165115 = 688747673) B688747673
theorem B612220153 : Blo 2233435 612220153 := bstep (se 2 (by rfl) ⟨229582557, by rfl⟩ : syracuseStep 612220153 = 459165115) B459165115
theorem B816293537 : Blo 2233435 816293537 := bstep (se 2 (by rfl) ⟨306110076, by rfl⟩ : syracuseStep 816293537 = 612220153) B612220153
theorem B544195691 : Blo 2233435 544195691 := bstep (se 1 (by rfl) ⟨408146768, by rfl⟩ : syracuseStep 544195691 = 816293537) B816293537
theorem B362797127 : Blo 2233435 362797127 := bstep (se 1 (by rfl) ⟨272097845, by rfl⟩ : syracuseStep 362797127 = 544195691) B544195691
theorem B241864751 : Blo 2233435 241864751 := bstep (se 1 (by rfl) ⟨181398563, by rfl⟩ : syracuseStep 241864751 = 362797127) B362797127
theorem B161243167 : Blo 2233435 161243167 := bstep (se 1 (by rfl) ⟨120932375, by rfl⟩ : syracuseStep 161243167 = 241864751) B241864751
theorem B3439854229 : Blo 2233435 3439854229 := bstep (se 6 (by rfl) ⟨80621583, by rfl⟩ : syracuseStep 3439854229 = 161243167) B161243167
theorem B4586472305 : Blo 2233435 4586472305 := bstep (se 2 (by rfl) ⟨1719927114, by rfl⟩ : syracuseStep 4586472305 = 3439854229) B3439854229
theorem B3057648203 : Blo 2233435 3057648203 := bstep (se 1 (by rfl) ⟨2293236152, by rfl⟩ : syracuseStep 3057648203 = 4586472305) B4586472305
theorem B8153728541 : Blo 2233435 8153728541 := bstep (se 3 (by rfl) ⟨1528824101, by rfl⟩ : syracuseStep 8153728541 = 3057648203) B3057648203
theorem B5435819027 : Blo 2233435 5435819027 := bstep (se 1 (by rfl) ⟨4076864270, by rfl⟩ : syracuseStep 5435819027 = 8153728541) B8153728541
theorem B3623879351 : Blo 2233435 3623879351 := bstep (se 1 (by rfl) ⟨2717909513, by rfl⟩ : syracuseStep 3623879351 = 5435819027) B5435819027
theorem B2415919567 : Blo 2233435 2415919567 := bstep (se 1 (by rfl) ⟨1811939675, by rfl⟩ : syracuseStep 2415919567 = 3623879351) B3623879351
theorem B3221226089 : Blo 2233435 3221226089 := bstep (se 2 (by rfl) ⟨1207959783, by rfl⟩ : syracuseStep 3221226089 = 2415919567) B2415919567
theorem B2147484059 : Blo 2233435 2147484059 := bstep (se 1 (by rfl) ⟨1610613044, by rfl⟩ : syracuseStep 2147484059 = 3221226089) B3221226089
theorem B1431656039 : Blo 2233435 1431656039 := bstep (se 1 (by rfl) ⟨1073742029, by rfl⟩ : syracuseStep 1431656039 = 2147484059) B2147484059
theorem B954437359 : Blo 2233435 954437359 := bstep (se 1 (by rfl) ⟨715828019, by rfl⟩ : syracuseStep 954437359 = 1431656039) B1431656039
theorem B1272583145 : Blo 2233435 1272583145 := bstep (se 2 (by rfl) ⟨477218679, by rfl⟩ : syracuseStep 1272583145 = 954437359) B954437359
theorem B848388763 : Blo 2233435 848388763 := bstep (se 1 (by rfl) ⟨636291572, by rfl⟩ : syracuseStep 848388763 = 1272583145) B1272583145
theorem B1131185017 : Blo 2233435 1131185017 := bstep (se 2 (by rfl) ⟨424194381, by rfl⟩ : syracuseStep 1131185017 = 848388763) B848388763
theorem B1508246689 : Blo 2233435 1508246689 := bstep (se 2 (by rfl) ⟨565592508, by rfl⟩ : syracuseStep 1508246689 = 1131185017) B1131185017
theorem B2010995585 : Blo 2233435 2010995585 := bstep (se 2 (by rfl) ⟨754123344, by rfl⟩ : syracuseStep 2010995585 = 1508246689) B1508246689
theorem B1340663723 : Blo 2233435 1340663723 := bstep (se 1 (by rfl) ⟨1005497792, by rfl⟩ : syracuseStep 1340663723 = 2010995585) B2010995585
theorem B893775815 : Blo 2233435 893775815 := bstep (se 1 (by rfl) ⟨670331861, by rfl⟩ : syracuseStep 893775815 = 1340663723) B1340663723
theorem B595850543 : Blo 2233435 595850543 := bstep (se 1 (by rfl) ⟨446887907, by rfl⟩ : syracuseStep 595850543 = 893775815) B893775815
theorem B397233695 : Blo 2233435 397233695 := bstep (se 1 (by rfl) ⟨297925271, by rfl⟩ : syracuseStep 397233695 = 595850543) B595850543
theorem B264822463 : Blo 2233435 264822463 := bstep (se 1 (by rfl) ⟨198616847, by rfl⟩ : syracuseStep 264822463 = 397233695) B397233695
theorem B1412386469 : Blo 2233435 1412386469 := bstep (se 4 (by rfl) ⟨132411231, by rfl⟩ : syracuseStep 1412386469 = 264822463) B264822463
theorem B941590979 : Blo 2233435 941590979 := bstep (se 1 (by rfl) ⟨706193234, by rfl⟩ : syracuseStep 941590979 = 1412386469) B1412386469
theorem B627727319 : Blo 2233435 627727319 := bstep (se 1 (by rfl) ⟨470795489, by rfl⟩ : syracuseStep 627727319 = 941590979) B941590979
theorem B418484879 : Blo 2233435 418484879 := bstep (se 1 (by rfl) ⟨313863659, by rfl⟩ : syracuseStep 418484879 = 627727319) B627727319
theorem B278989919 : Blo 2233435 278989919 := bstep (se 1 (by rfl) ⟨209242439, by rfl⟩ : syracuseStep 278989919 = 418484879) B418484879
theorem B185993279 : Blo 2233435 185993279 := bstep (se 1 (by rfl) ⟨139494959, by rfl⟩ : syracuseStep 185993279 = 278989919) B278989919
theorem B123995519 : Blo 2233435 123995519 := bstep (se 1 (by rfl) ⟨92996639, by rfl⟩ : syracuseStep 123995519 = 185993279) B185993279
theorem B82663679 : Blo 2233435 82663679 := bstep (se 1 (by rfl) ⟨61997759, by rfl⟩ : syracuseStep 82663679 = 123995519) B123995519
theorem B55109119 : Blo 2233435 55109119 := bstep (se 1 (by rfl) ⟨41331839, by rfl⟩ : syracuseStep 55109119 = 82663679) B82663679
theorem B73478825 : Blo 2233435 73478825 := bstep (se 2 (by rfl) ⟨27554559, by rfl⟩ : syracuseStep 73478825 = 55109119) B55109119
theorem B48985883 : Blo 2233435 48985883 := bstep (se 1 (by rfl) ⟨36739412, by rfl⟩ : syracuseStep 48985883 = 73478825) B73478825
theorem B32657255 : Blo 2233435 32657255 := bstep (se 1 (by rfl) ⟨24492941, by rfl⟩ : syracuseStep 32657255 = 48985883) B48985883
theorem B21771503 : Blo 2233435 21771503 := bstep (se 1 (by rfl) ⟨16328627, by rfl⟩ : syracuseStep 21771503 = 32657255) B32657255
theorem B14514335 : Blo 2233435 14514335 := bstep (se 1 (by rfl) ⟨10885751, by rfl⟩ : syracuseStep 14514335 = 21771503) B21771503
theorem B9676223 : Blo 2233435 9676223 := bstep (se 1 (by rfl) ⟨7257167, by rfl⟩ : syracuseStep 9676223 = 14514335) B14514335
theorem B6450815 : Blo 2233435 6450815 := bstep (se 1 (by rfl) ⟨4838111, by rfl⟩ : syracuseStep 6450815 = 9676223) B9676223
theorem B4300543 : Blo 2233435 4300543 := bstep (se 1 (by rfl) ⟨3225407, by rfl⟩ : syracuseStep 4300543 = 6450815) B6450815
theorem B22936229 : Blo 2233435 22936229 := bstep (se 4 (by rfl) ⟨2150271, by rfl⟩ : syracuseStep 22936229 = 4300543) B4300543
theorem B15290819 : Blo 2233435 15290819 := bstep (se 1 (by rfl) ⟨11468114, by rfl⟩ : syracuseStep 15290819 = 22936229) B22936229
theorem B10193879 : Blo 2233435 10193879 := bstep (se 1 (by rfl) ⟨7645409, by rfl⟩ : syracuseStep 10193879 = 15290819) B15290819
theorem B6795919 : Blo 2233435 6795919 := bstep (se 1 (by rfl) ⟨5096939, by rfl⟩ : syracuseStep 6795919 = 10193879) B10193879
theorem B36244901 : Blo 2233435 36244901 := bstep (se 4 (by rfl) ⟨3397959, by rfl⟩ : syracuseStep 36244901 = 6795919) B6795919
theorem B24163267 : Blo 2233435 24163267 := bstep (se 1 (by rfl) ⟨18122450, by rfl⟩ : syracuseStep 24163267 = 36244901) B36244901
theorem B32217689 : Blo 2233435 32217689 := bstep (se 2 (by rfl) ⟨12081633, by rfl⟩ : syracuseStep 32217689 = 24163267) B24163267
theorem B21478459 : Blo 2233435 21478459 := bstep (se 1 (by rfl) ⟨16108844, by rfl⟩ : syracuseStep 21478459 = 32217689) B32217689
theorem B28637945 : Blo 2233435 28637945 := bstep (se 2 (by rfl) ⟨10739229, by rfl⟩ : syracuseStep 28637945 = 21478459) B21478459
theorem B19091963 : Blo 2233435 19091963 := bstep (se 1 (by rfl) ⟨14318972, by rfl⟩ : syracuseStep 19091963 = 28637945) B28637945
theorem B12727975 : Blo 2233435 12727975 := bstep (se 1 (by rfl) ⟨9545981, by rfl⟩ : syracuseStep 12727975 = 19091963) B19091963
theorem B16970633 : Blo 2233435 16970633 := bstep (se 2 (by rfl) ⟨6363987, by rfl⟩ : syracuseStep 16970633 = 12727975) B12727975
theorem B11313755 : Blo 2233435 11313755 := bstep (se 1 (by rfl) ⟨8485316, by rfl⟩ : syracuseStep 11313755 = 16970633) B16970633
theorem B7542503 : Blo 2233435 7542503 := bstep (se 1 (by rfl) ⟨5656877, by rfl⟩ : syracuseStep 7542503 = 11313755) B11313755
theorem B5028335 : Blo 2233435 5028335 := bstep (se 1 (by rfl) ⟨3771251, by rfl⟩ : syracuseStep 5028335 = 7542503) B7542503
theorem B3352223 : Blo 2233435 3352223 := bstep (se 1 (by rfl) ⟨2514167, by rfl⟩ : syracuseStep 3352223 = 5028335) B5028335
theorem B2234815 : Blo 2233435 2234815 := bstep (se 1 (by rfl) ⟨1676111, by rfl⟩ : syracuseStep 2234815 = 3352223) B3352223
theorem B3352229 : Blo 2233435 3352229 := bbase (se 4 (by rfl) ⟨314271, by rfl⟩ : syracuseStep 3352229 = 628543) (by norm_num)
theorem B2234819 : Blo 2233435 2234819 := bstep (se 1 (by rfl) ⟨1676114, by rfl⟩ : syracuseStep 2234819 = 3352229) B3352229
theorem B2828449 : Blo 2233435 2828449 := bbase (se 2 (by rfl) ⟨1060668, by rfl⟩ : syracuseStep 2828449 = 2121337) (by norm_num)
theorem B3771265 : Blo 2233435 3771265 := bstep (se 2 (by rfl) ⟨1414224, by rfl⟩ : syracuseStep 3771265 = 2828449) B2828449
theorem B5028353 : Blo 2233435 5028353 := bstep (se 2 (by rfl) ⟨1885632, by rfl⟩ : syracuseStep 5028353 = 3771265) B3771265
theorem B3352235 : Blo 2233435 3352235 := bstep (se 1 (by rfl) ⟨2514176, by rfl⟩ : syracuseStep 3352235 = 5028353) B5028353
theorem B2234823 : Blo 2233435 2234823 := bstep (se 1 (by rfl) ⟨1676117, by rfl⟩ : syracuseStep 2234823 = 3352235) B3352235
theorem B2514181 : Blo 2233435 2514181 := bbase (se 4 (by rfl) ⟨235704, by rfl⟩ : syracuseStep 2514181 = 471409) (by norm_num)
theorem B3352241 : Blo 2233435 3352241 := bstep (se 2 (by rfl) ⟨1257090, by rfl⟩ : syracuseStep 3352241 = 2514181) B2514181
theorem B2234827 : Blo 2233435 2234827 := bstep (se 1 (by rfl) ⟨1676120, by rfl⟩ : syracuseStep 2234827 = 3352241) B3352241
theorem B2386513 : Blo 2233435 2386513 := bbase (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) (by norm_num)
theorem B3182017 : Blo 2233435 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B4242689 : Blo 2233435 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B2828459 : Blo 2233435 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B7542557 : Blo 2233435 7542557 := bstep (se 3 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 7542557 = 2828459) B2828459
theorem B5028371 : Blo 2233435 5028371 := bstep (se 1 (by rfl) ⟨3771278, by rfl⟩ : syracuseStep 5028371 = 7542557) B7542557
theorem B3352247 : Blo 2233435 3352247 := bstep (se 1 (by rfl) ⟨2514185, by rfl⟩ : syracuseStep 3352247 = 5028371) B5028371
theorem B2234831 : Blo 2233435 2234831 := bstep (se 1 (by rfl) ⟨1676123, by rfl⟩ : syracuseStep 2234831 = 3352247) B3352247
theorem B3352253 : Blo 2233435 3352253 := bbase (se 3 (by rfl) ⟨628547, by rfl⟩ : syracuseStep 3352253 = 1257095) (by norm_num)
theorem B2234835 : Blo 2233435 2234835 := bstep (se 1 (by rfl) ⟨1676126, by rfl⟩ : syracuseStep 2234835 = 3352253) B3352253
theorem B5028389 : Blo 2233435 5028389 := bbase (se 4 (by rfl) ⟨471411, by rfl⟩ : syracuseStep 5028389 = 942823) (by norm_num)
theorem B3352259 : Blo 2233435 3352259 := bstep (se 1 (by rfl) ⟨2514194, by rfl⟩ : syracuseStep 3352259 = 5028389) B5028389
theorem B2234839 : Blo 2233435 2234839 := bstep (se 1 (by rfl) ⟨1676129, by rfl⟩ : syracuseStep 2234839 = 3352259) B3352259
theorem B5656949 : Blo 2233435 5656949 := bbase (se 5 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 5656949 = 530339) (by norm_num)
theorem B3771299 : Blo 2233435 3771299 := bstep (se 1 (by rfl) ⟨2828474, by rfl⟩ : syracuseStep 3771299 = 5656949) B5656949
theorem B2514199 : Blo 2233435 2514199 := bstep (se 1 (by rfl) ⟨1885649, by rfl⟩ : syracuseStep 2514199 = 3771299) B3771299
theorem B3352265 : Blo 2233435 3352265 := bstep (se 2 (by rfl) ⟨1257099, by rfl⟩ : syracuseStep 3352265 = 2514199) B2514199
theorem B2234843 : Blo 2233435 2234843 := bstep (se 1 (by rfl) ⟨1676132, by rfl⟩ : syracuseStep 2234843 = 3352265) B3352265
theorem B16109077 : Blo 2233435 16109077 := bbase (se 6 (by rfl) ⟨377556, by rfl⟩ : syracuseStep 16109077 = 755113) (by norm_num)
theorem B21478769 : Blo 2233435 21478769 := bstep (se 2 (by rfl) ⟨8054538, by rfl⟩ : syracuseStep 21478769 = 16109077) B16109077
theorem B14319179 : Blo 2233435 14319179 := bstep (se 1 (by rfl) ⟨10739384, by rfl⟩ : syracuseStep 14319179 = 21478769) B21478769
theorem B9546119 : Blo 2233435 9546119 := bstep (se 1 (by rfl) ⟨7159589, by rfl⟩ : syracuseStep 9546119 = 14319179) B14319179
theorem B6364079 : Blo 2233435 6364079 := bstep (se 1 (by rfl) ⟨4773059, by rfl⟩ : syracuseStep 6364079 = 9546119) B9546119
theorem B4242719 : Blo 2233435 4242719 := bstep (se 1 (by rfl) ⟨3182039, by rfl⟩ : syracuseStep 4242719 = 6364079) B6364079
theorem B11313917 : Blo 2233435 11313917 := bstep (se 3 (by rfl) ⟨2121359, by rfl⟩ : syracuseStep 11313917 = 4242719) B4242719
theorem B7542611 : Blo 2233435 7542611 := bstep (se 1 (by rfl) ⟨5656958, by rfl⟩ : syracuseStep 7542611 = 11313917) B11313917
theorem B5028407 : Blo 2233435 5028407 := bstep (se 1 (by rfl) ⟨3771305, by rfl⟩ : syracuseStep 5028407 = 7542611) B7542611
theorem B3352271 : Blo 2233435 3352271 := bstep (se 1 (by rfl) ⟨2514203, by rfl⟩ : syracuseStep 3352271 = 5028407) B5028407
theorem B2234847 : Blo 2233435 2234847 := bstep (se 1 (by rfl) ⟨1676135, by rfl⟩ : syracuseStep 2234847 = 3352271) B3352271
theorem B3352277 : Blo 2233435 3352277 := bbase (se 7 (by rfl) ⟨39284, by rfl⟩ : syracuseStep 3352277 = 78569) (by norm_num)
theorem B2234851 : Blo 2233435 2234851 := bstep (se 1 (by rfl) ⟨1676138, by rfl⟩ : syracuseStep 2234851 = 3352277) B3352277
theorem B4773077 : Blo 2233435 4773077 := bbase (se 7 (by rfl) ⟨55934, by rfl⟩ : syracuseStep 4773077 = 111869) (by norm_num)
theorem B3182051 : Blo 2233435 3182051 := bstep (se 1 (by rfl) ⟨2386538, by rfl⟩ : syracuseStep 3182051 = 4773077) B4773077
theorem B8485469 : Blo 2233435 8485469 := bstep (se 3 (by rfl) ⟨1591025, by rfl⟩ : syracuseStep 8485469 = 3182051) B3182051
theorem B5656979 : Blo 2233435 5656979 := bstep (se 1 (by rfl) ⟨4242734, by rfl⟩ : syracuseStep 5656979 = 8485469) B8485469
theorem B3771319 : Blo 2233435 3771319 := bstep (se 1 (by rfl) ⟨2828489, by rfl⟩ : syracuseStep 3771319 = 5656979) B5656979
theorem B5028425 : Blo 2233435 5028425 := bstep (se 2 (by rfl) ⟨1885659, by rfl⟩ : syracuseStep 5028425 = 3771319) B3771319
theorem B3352283 : Blo 2233435 3352283 := bstep (se 1 (by rfl) ⟨2514212, by rfl⟩ : syracuseStep 3352283 = 5028425) B5028425
theorem B2234855 : Blo 2233435 2234855 := bstep (se 1 (by rfl) ⟨1676141, by rfl⟩ : syracuseStep 2234855 = 3352283) B3352283
theorem B2514217 : Blo 2233435 2514217 := bbase (se 2 (by rfl) ⟨942831, by rfl⟩ : syracuseStep 2514217 = 1885663) (by norm_num)
theorem B3352289 : Blo 2233435 3352289 := bstep (se 2 (by rfl) ⟨1257108, by rfl⟩ : syracuseStep 3352289 = 2514217) B2514217
theorem B2234859 : Blo 2233435 2234859 := bstep (se 1 (by rfl) ⟨1676144, by rfl⟩ : syracuseStep 2234859 = 3352289) B3352289
theorem B10739461 : Blo 2233435 10739461 := bbase (se 4 (by rfl) ⟨1006824, by rfl⟩ : syracuseStep 10739461 = 2013649) (by norm_num)
theorem B14319281 : Blo 2233435 14319281 := bstep (se 2 (by rfl) ⟨5369730, by rfl⟩ : syracuseStep 14319281 = 10739461) B10739461
theorem B9546187 : Blo 2233435 9546187 := bstep (se 1 (by rfl) ⟨7159640, by rfl⟩ : syracuseStep 9546187 = 14319281) B14319281
theorem B12728249 : Blo 2233435 12728249 := bstep (se 2 (by rfl) ⟨4773093, by rfl⟩ : syracuseStep 12728249 = 9546187) B9546187
theorem B8485499 : Blo 2233435 8485499 := bstep (se 1 (by rfl) ⟨6364124, by rfl⟩ : syracuseStep 8485499 = 12728249) B12728249
theorem B5656999 : Blo 2233435 5656999 := bstep (se 1 (by rfl) ⟨4242749, by rfl⟩ : syracuseStep 5656999 = 8485499) B8485499
theorem B7542665 : Blo 2233435 7542665 := bstep (se 2 (by rfl) ⟨2828499, by rfl⟩ : syracuseStep 7542665 = 5656999) B5656999
theorem B5028443 : Blo 2233435 5028443 := bstep (se 1 (by rfl) ⟨3771332, by rfl⟩ : syracuseStep 5028443 = 7542665) B7542665
theorem B3352295 : Blo 2233435 3352295 := bstep (se 1 (by rfl) ⟨2514221, by rfl⟩ : syracuseStep 3352295 = 5028443) B5028443
theorem B2234863 : Blo 2233435 2234863 := bstep (se 1 (by rfl) ⟨1676147, by rfl⟩ : syracuseStep 2234863 = 3352295) B3352295
theorem B3352301 : Blo 2233435 3352301 := bbase (se 3 (by rfl) ⟨628556, by rfl⟩ : syracuseStep 3352301 = 1257113) (by norm_num)
theorem B2234867 : Blo 2233435 2234867 := bstep (se 1 (by rfl) ⟨1676150, by rfl⟩ : syracuseStep 2234867 = 3352301) B3352301
theorem B5028461 : Blo 2233435 5028461 := bbase (se 3 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 5028461 = 1885673) (by norm_num)
theorem B3352307 : Blo 2233435 3352307 := bstep (se 1 (by rfl) ⟨2514230, by rfl⟩ : syracuseStep 3352307 = 5028461) B5028461
theorem B2234871 : Blo 2233435 2234871 := bstep (se 1 (by rfl) ⟨1676153, by rfl⟩ : syracuseStep 2234871 = 3352307) B3352307
theorem B4242773 : Blo 2233435 4242773 := bbase (se 11 (by rfl) ⟨3107, by rfl⟩ : syracuseStep 4242773 = 6215) (by norm_num)
theorem B2828515 : Blo 2233435 2828515 := bstep (se 1 (by rfl) ⟨2121386, by rfl⟩ : syracuseStep 2828515 = 4242773) B4242773
theorem B3771353 : Blo 2233435 3771353 := bstep (se 2 (by rfl) ⟨1414257, by rfl⟩ : syracuseStep 3771353 = 2828515) B2828515
theorem B2514235 : Blo 2233435 2514235 := bstep (se 1 (by rfl) ⟨1885676, by rfl⟩ : syracuseStep 2514235 = 3771353) B3771353
theorem B3352313 : Blo 2233435 3352313 := bstep (se 2 (by rfl) ⟨1257117, by rfl⟩ : syracuseStep 3352313 = 2514235) B2514235
theorem B2234875 : Blo 2233435 2234875 := bstep (se 1 (by rfl) ⟨1676156, by rfl⟩ : syracuseStep 2234875 = 3352313) B3352313
theorem B20388341 : Blo 2233435 20388341 := bbase (se 5 (by rfl) ⟨955703, by rfl⟩ : syracuseStep 20388341 = 1911407) (by norm_num)
theorem B13592227 : Blo 2233435 13592227 := bstep (se 1 (by rfl) ⟨10194170, by rfl⟩ : syracuseStep 13592227 = 20388341) B20388341
theorem B18122969 : Blo 2233435 18122969 := bstep (se 2 (by rfl) ⟨6796113, by rfl⟩ : syracuseStep 18122969 = 13592227) B13592227
theorem B12081979 : Blo 2233435 12081979 := bstep (se 1 (by rfl) ⟨9061484, by rfl⟩ : syracuseStep 12081979 = 18122969) B18122969
theorem B64437221 : Blo 2233435 64437221 := bstep (se 4 (by rfl) ⟨6040989, by rfl⟩ : syracuseStep 64437221 = 12081979) B12081979
theorem B42958147 : Blo 2233435 42958147 := bstep (se 1 (by rfl) ⟨32218610, by rfl⟩ : syracuseStep 42958147 = 64437221) B64437221
theorem B57277529 : Blo 2233435 57277529 := bstep (se 2 (by rfl) ⟨21479073, by rfl⟩ : syracuseStep 57277529 = 42958147) B42958147
theorem B38185019 : Blo 2233435 38185019 := bstep (se 1 (by rfl) ⟨28638764, by rfl⟩ : syracuseStep 38185019 = 57277529) B57277529
theorem B25456679 : Blo 2233435 25456679 := bstep (se 1 (by rfl) ⟨19092509, by rfl⟩ : syracuseStep 25456679 = 38185019) B38185019
theorem B16971119 : Blo 2233435 16971119 := bstep (se 1 (by rfl) ⟨12728339, by rfl⟩ : syracuseStep 16971119 = 25456679) B25456679
theorem B11314079 : Blo 2233435 11314079 := bstep (se 1 (by rfl) ⟨8485559, by rfl⟩ : syracuseStep 11314079 = 16971119) B16971119
theorem B7542719 : Blo 2233435 7542719 := bstep (se 1 (by rfl) ⟨5657039, by rfl⟩ : syracuseStep 7542719 = 11314079) B11314079
theorem B5028479 : Blo 2233435 5028479 := bstep (se 1 (by rfl) ⟨3771359, by rfl⟩ : syracuseStep 5028479 = 7542719) B7542719
theorem B3352319 : Blo 2233435 3352319 := bstep (se 1 (by rfl) ⟨2514239, by rfl⟩ : syracuseStep 3352319 = 5028479) B5028479
theorem B2234879 : Blo 2233435 2234879 := bstep (se 1 (by rfl) ⟨1676159, by rfl⟩ : syracuseStep 2234879 = 3352319) B3352319
theorem B3352325 : Blo 2233435 3352325 := bbase (se 4 (by rfl) ⟨314280, by rfl⟩ : syracuseStep 3352325 = 628561) (by norm_num)
theorem B2234883 : Blo 2233435 2234883 := bstep (se 1 (by rfl) ⟨1676162, by rfl⟩ : syracuseStep 2234883 = 3352325) B3352325
theorem B3771373 : Blo 2233435 3771373 := bbase (se 3 (by rfl) ⟨707132, by rfl⟩ : syracuseStep 3771373 = 1414265) (by norm_num)
theorem B5028497 : Blo 2233435 5028497 := bstep (se 2 (by rfl) ⟨1885686, by rfl⟩ : syracuseStep 5028497 = 3771373) B3771373
theorem B3352331 : Blo 2233435 3352331 := bstep (se 1 (by rfl) ⟨2514248, by rfl⟩ : syracuseStep 3352331 = 5028497) B5028497
theorem B2234887 : Blo 2233435 2234887 := bstep (se 1 (by rfl) ⟨1676165, by rfl⟩ : syracuseStep 2234887 = 3352331) B3352331
theorem B2514253 : Blo 2233435 2514253 := bbase (se 3 (by rfl) ⟨471422, by rfl⟩ : syracuseStep 2514253 = 942845) (by norm_num)
theorem B3352337 : Blo 2233435 3352337 := bstep (se 2 (by rfl) ⟨1257126, by rfl⟩ : syracuseStep 3352337 = 2514253) B2514253
theorem B2234891 : Blo 2233435 2234891 := bstep (se 1 (by rfl) ⟨1676168, by rfl⟩ : syracuseStep 2234891 = 3352337) B3352337
theorem B7542773 : Blo 2233435 7542773 := bbase (se 5 (by rfl) ⟨353567, by rfl⟩ : syracuseStep 7542773 = 707135) (by norm_num)
theorem B5028515 : Blo 2233435 5028515 := bstep (se 1 (by rfl) ⟨3771386, by rfl⟩ : syracuseStep 5028515 = 7542773) B7542773
theorem B3352343 : Blo 2233435 3352343 := bstep (se 1 (by rfl) ⟨2514257, by rfl⟩ : syracuseStep 3352343 = 5028515) B5028515
theorem B2234895 : Blo 2233435 2234895 := bstep (se 1 (by rfl) ⟨1676171, by rfl⟩ : syracuseStep 2234895 = 3352343) B3352343
theorem B3352349 : Blo 2233435 3352349 := bbase (se 3 (by rfl) ⟨628565, by rfl⟩ : syracuseStep 3352349 = 1257131) (by norm_num)
theorem B2234899 : Blo 2233435 2234899 := bstep (se 1 (by rfl) ⟨1676174, by rfl⟩ : syracuseStep 2234899 = 3352349) B3352349
theorem B5028533 : Blo 2233435 5028533 := bbase (se 5 (by rfl) ⟨235712, by rfl⟩ : syracuseStep 5028533 = 471425) (by norm_num)
theorem B3352355 : Blo 2233435 3352355 := bstep (se 1 (by rfl) ⟨2514266, by rfl⟩ : syracuseStep 3352355 = 5028533) B5028533
theorem B2234903 : Blo 2233435 2234903 := bstep (se 1 (by rfl) ⟨1676177, by rfl⟩ : syracuseStep 2234903 = 3352355) B3352355
theorem B12728501 : Blo 2233435 12728501 := bbase (se 5 (by rfl) ⟨596648, by rfl⟩ : syracuseStep 12728501 = 1193297) (by norm_num)
theorem B8485667 : Blo 2233435 8485667 := bstep (se 1 (by rfl) ⟨6364250, by rfl⟩ : syracuseStep 8485667 = 12728501) B12728501
theorem B5657111 : Blo 2233435 5657111 := bstep (se 1 (by rfl) ⟨4242833, by rfl⟩ : syracuseStep 5657111 = 8485667) B8485667
theorem B3771407 : Blo 2233435 3771407 := bstep (se 1 (by rfl) ⟨2828555, by rfl⟩ : syracuseStep 3771407 = 5657111) B5657111
theorem B2514271 : Blo 2233435 2514271 := bstep (se 1 (by rfl) ⟨1885703, by rfl⟩ : syracuseStep 2514271 = 3771407) B3771407
theorem B3352361 : Blo 2233435 3352361 := bstep (se 2 (by rfl) ⟨1257135, by rfl⟩ : syracuseStep 3352361 = 2514271) B2514271
theorem B2234907 : Blo 2233435 2234907 := bstep (se 1 (by rfl) ⟨1676180, by rfl⟩ : syracuseStep 2234907 = 3352361) B3352361
theorem B6364261 : Blo 2233435 6364261 := bbase (se 4 (by rfl) ⟨596649, by rfl⟩ : syracuseStep 6364261 = 1193299) (by norm_num)
theorem B8485681 : Blo 2233435 8485681 := bstep (se 2 (by rfl) ⟨3182130, by rfl⟩ : syracuseStep 8485681 = 6364261) B6364261
theorem B11314241 : Blo 2233435 11314241 := bstep (se 2 (by rfl) ⟨4242840, by rfl⟩ : syracuseStep 11314241 = 8485681) B8485681
theorem B7542827 : Blo 2233435 7542827 := bstep (se 1 (by rfl) ⟨5657120, by rfl⟩ : syracuseStep 7542827 = 11314241) B11314241
theorem B5028551 : Blo 2233435 5028551 := bstep (se 1 (by rfl) ⟨3771413, by rfl⟩ : syracuseStep 5028551 = 7542827) B7542827
theorem B3352367 : Blo 2233435 3352367 := bstep (se 1 (by rfl) ⟨2514275, by rfl⟩ : syracuseStep 3352367 = 5028551) B5028551
theorem B2234911 : Blo 2233435 2234911 := bstep (se 1 (by rfl) ⟨1676183, by rfl⟩ : syracuseStep 2234911 = 3352367) B3352367
theorem B3352373 : Blo 2233435 3352373 := bbase (se 5 (by rfl) ⟨157142, by rfl⟩ : syracuseStep 3352373 = 314285) (by norm_num)
theorem B2234915 : Blo 2233435 2234915 := bstep (se 1 (by rfl) ⟨1676186, by rfl⟩ : syracuseStep 2234915 = 3352373) B3352373
theorem B5657141 : Blo 2233435 5657141 := bbase (se 5 (by rfl) ⟨265178, by rfl⟩ : syracuseStep 5657141 = 530357) (by norm_num)
theorem B3771427 : Blo 2233435 3771427 := bstep (se 1 (by rfl) ⟨2828570, by rfl⟩ : syracuseStep 3771427 = 5657141) B5657141
theorem B5028569 : Blo 2233435 5028569 := bstep (se 2 (by rfl) ⟨1885713, by rfl⟩ : syracuseStep 5028569 = 3771427) B3771427
theorem B3352379 : Blo 2233435 3352379 := bstep (se 1 (by rfl) ⟨2514284, by rfl⟩ : syracuseStep 3352379 = 5028569) B5028569
theorem B2234919 : Blo 2233435 2234919 := bstep (se 1 (by rfl) ⟨1676189, by rfl⟩ : syracuseStep 2234919 = 3352379) B3352379
theorem B2514289 : Blo 2233435 2514289 := bbase (se 2 (by rfl) ⟨942858, by rfl⟩ : syracuseStep 2514289 = 1885717) (by norm_num)
theorem B3352385 : Blo 2233435 3352385 := bstep (se 2 (by rfl) ⟨1257144, by rfl⟩ : syracuseStep 3352385 = 2514289) B2514289
theorem B2234923 : Blo 2233435 2234923 := bstep (se 1 (by rfl) ⟨1676192, by rfl⟩ : syracuseStep 2234923 = 3352385) B3352385
theorem B5369885 : Blo 2233435 5369885 := bbase (se 3 (by rfl) ⟨1006853, by rfl⟩ : syracuseStep 5369885 = 2013707) (by norm_num)
theorem B3579923 : Blo 2233435 3579923 := bstep (se 1 (by rfl) ⟨2684942, by rfl⟩ : syracuseStep 3579923 = 5369885) B5369885
theorem B9546461 : Blo 2233435 9546461 := bstep (se 3 (by rfl) ⟨1789961, by rfl⟩ : syracuseStep 9546461 = 3579923) B3579923
theorem B6364307 : Blo 2233435 6364307 := bstep (se 1 (by rfl) ⟨4773230, by rfl⟩ : syracuseStep 6364307 = 9546461) B9546461
theorem B4242871 : Blo 2233435 4242871 := bstep (se 1 (by rfl) ⟨3182153, by rfl⟩ : syracuseStep 4242871 = 6364307) B6364307
theorem B5657161 : Blo 2233435 5657161 := bstep (se 2 (by rfl) ⟨2121435, by rfl⟩ : syracuseStep 5657161 = 4242871) B4242871
theorem B7542881 : Blo 2233435 7542881 := bstep (se 2 (by rfl) ⟨2828580, by rfl⟩ : syracuseStep 7542881 = 5657161) B5657161
theorem B5028587 : Blo 2233435 5028587 := bstep (se 1 (by rfl) ⟨3771440, by rfl⟩ : syracuseStep 5028587 = 7542881) B7542881
theorem B3352391 : Blo 2233435 3352391 := bstep (se 1 (by rfl) ⟨2514293, by rfl⟩ : syracuseStep 3352391 = 5028587) B5028587
theorem B2234927 : Blo 2233435 2234927 := bstep (se 1 (by rfl) ⟨1676195, by rfl⟩ : syracuseStep 2234927 = 3352391) B3352391
theorem B3352397 : Blo 2233435 3352397 := bbase (se 3 (by rfl) ⟨628574, by rfl⟩ : syracuseStep 3352397 = 1257149) (by norm_num)
theorem B2234931 : Blo 2233435 2234931 := bstep (se 1 (by rfl) ⟨1676198, by rfl⟩ : syracuseStep 2234931 = 3352397) B3352397
theorem B5028605 : Blo 2233435 5028605 := bbase (se 3 (by rfl) ⟨942863, by rfl⟩ : syracuseStep 5028605 = 1885727) (by norm_num)
theorem B3352403 : Blo 2233435 3352403 := bstep (se 1 (by rfl) ⟨2514302, by rfl⟩ : syracuseStep 3352403 = 5028605) B5028605
theorem B2234935 : Blo 2233435 2234935 := bstep (se 1 (by rfl) ⟨1676201, by rfl⟩ : syracuseStep 2234935 = 3352403) B3352403
theorem B3771461 : Blo 2233435 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B2514307 : Blo 2233435 2514307 := bstep (se 1 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 2514307 = 3771461) B3771461
theorem B3352409 : Blo 2233435 3352409 := bstep (se 2 (by rfl) ⟨1257153, by rfl⟩ : syracuseStep 3352409 = 2514307) B2514307
theorem B2234939 : Blo 2233435 2234939 := bstep (se 1 (by rfl) ⟨1676204, by rfl⟩ : syracuseStep 2234939 = 3352409) B3352409
theorem B16971605 : Blo 2233435 16971605 := bbase (se 9 (by rfl) ⟨49721, by rfl⟩ : syracuseStep 16971605 = 99443) (by norm_num)
theorem B11314403 : Blo 2233435 11314403 := bstep (se 1 (by rfl) ⟨8485802, by rfl⟩ : syracuseStep 11314403 = 16971605) B16971605
theorem B7542935 : Blo 2233435 7542935 := bstep (se 1 (by rfl) ⟨5657201, by rfl⟩ : syracuseStep 7542935 = 11314403) B11314403
theorem B5028623 : Blo 2233435 5028623 := bstep (se 1 (by rfl) ⟨3771467, by rfl⟩ : syracuseStep 5028623 = 7542935) B7542935
theorem B3352415 : Blo 2233435 3352415 := bstep (se 1 (by rfl) ⟨2514311, by rfl⟩ : syracuseStep 3352415 = 5028623) B5028623
theorem B2234943 : Blo 2233435 2234943 := bstep (se 1 (by rfl) ⟨1676207, by rfl⟩ : syracuseStep 2234943 = 3352415) B3352415
theorem B3352421 : Blo 2233435 3352421 := bbase (se 4 (by rfl) ⟨314289, by rfl⟩ : syracuseStep 3352421 = 628579) (by norm_num)
theorem B2234947 : Blo 2233435 2234947 := bstep (se 1 (by rfl) ⟨1676210, by rfl⟩ : syracuseStep 2234947 = 3352421) B3352421
theorem B4242917 : Blo 2233435 4242917 := bbase (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) (by norm_num)
theorem B2828611 : Blo 2233435 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B3771481 : Blo 2233435 3771481 := bstep (se 2 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 3771481 = 2828611) B2828611
theorem B5028641 : Blo 2233435 5028641 := bstep (se 2 (by rfl) ⟨1885740, by rfl⟩ : syracuseStep 5028641 = 3771481) B3771481
theorem B3352427 : Blo 2233435 3352427 := bstep (se 1 (by rfl) ⟨2514320, by rfl⟩ : syracuseStep 3352427 = 5028641) B5028641
theorem B2234951 : Blo 2233435 2234951 := bstep (se 1 (by rfl) ⟨1676213, by rfl⟩ : syracuseStep 2234951 = 3352427) B3352427
theorem B2514325 : Blo 2233435 2514325 := bbase (se 6 (by rfl) ⟨58929, by rfl⟩ : syracuseStep 2514325 = 117859) (by norm_num)
theorem B3352433 : Blo 2233435 3352433 := bstep (se 2 (by rfl) ⟨1257162, by rfl⟩ : syracuseStep 3352433 = 2514325) B2514325
theorem B2234955 : Blo 2233435 2234955 := bstep (se 1 (by rfl) ⟨1676216, by rfl⟩ : syracuseStep 2234955 = 3352433) B3352433
theorem B2828621 : Blo 2233435 2828621 := bbase (se 3 (by rfl) ⟨530366, by rfl⟩ : syracuseStep 2828621 = 1060733) (by norm_num)
theorem B7542989 : Blo 2233435 7542989 := bstep (se 3 (by rfl) ⟨1414310, by rfl⟩ : syracuseStep 7542989 = 2828621) B2828621
theorem B5028659 : Blo 2233435 5028659 := bstep (se 1 (by rfl) ⟨3771494, by rfl⟩ : syracuseStep 5028659 = 7542989) B7542989
theorem B3352439 : Blo 2233435 3352439 := bstep (se 1 (by rfl) ⟨2514329, by rfl⟩ : syracuseStep 3352439 = 5028659) B5028659
theorem B2234959 : Blo 2233435 2234959 := bstep (se 1 (by rfl) ⟨1676219, by rfl⟩ : syracuseStep 2234959 = 3352439) B3352439
theorem B3352445 : Blo 2233435 3352445 := bbase (se 3 (by rfl) ⟨628583, by rfl⟩ : syracuseStep 3352445 = 1257167) (by norm_num)
theorem B2234963 : Blo 2233435 2234963 := bstep (se 1 (by rfl) ⟨1676222, by rfl⟩ : syracuseStep 2234963 = 3352445) B3352445
theorem B5028677 : Blo 2233435 5028677 := bbase (se 4 (by rfl) ⟨471438, by rfl⟩ : syracuseStep 5028677 = 942877) (by norm_num)
theorem B3352451 : Blo 2233435 3352451 := bstep (se 1 (by rfl) ⟨2514338, by rfl⟩ : syracuseStep 3352451 = 5028677) B5028677
theorem B2234967 : Blo 2233435 2234967 := bstep (se 1 (by rfl) ⟨1676225, by rfl⟩ : syracuseStep 2234967 = 3352451) B3352451
theorem B4773325 : Blo 2233435 4773325 := bbase (se 3 (by rfl) ⟨894998, by rfl⟩ : syracuseStep 4773325 = 1789997) (by norm_num)
theorem B6364433 : Blo 2233435 6364433 := bstep (se 2 (by rfl) ⟨2386662, by rfl⟩ : syracuseStep 6364433 = 4773325) B4773325
theorem B4242955 : Blo 2233435 4242955 := bstep (se 1 (by rfl) ⟨3182216, by rfl⟩ : syracuseStep 4242955 = 6364433) B6364433
theorem B5657273 : Blo 2233435 5657273 := bstep (se 2 (by rfl) ⟨2121477, by rfl⟩ : syracuseStep 5657273 = 4242955) B4242955
theorem B3771515 : Blo 2233435 3771515 := bstep (se 1 (by rfl) ⟨2828636, by rfl⟩ : syracuseStep 3771515 = 5657273) B5657273
theorem B2514343 : Blo 2233435 2514343 := bstep (se 1 (by rfl) ⟨1885757, by rfl⟩ : syracuseStep 2514343 = 3771515) B3771515
theorem B3352457 : Blo 2233435 3352457 := bstep (se 2 (by rfl) ⟨1257171, by rfl⟩ : syracuseStep 3352457 = 2514343) B2514343
theorem B2234971 : Blo 2233435 2234971 := bstep (se 1 (by rfl) ⟨1676228, by rfl⟩ : syracuseStep 2234971 = 3352457) B3352457
theorem B11314565 : Blo 2233435 11314565 := bbase (se 4 (by rfl) ⟨1060740, by rfl⟩ : syracuseStep 11314565 = 2121481) (by norm_num)
theorem B7543043 : Blo 2233435 7543043 := bstep (se 1 (by rfl) ⟨5657282, by rfl⟩ : syracuseStep 7543043 = 11314565) B11314565
theorem B5028695 : Blo 2233435 5028695 := bstep (se 1 (by rfl) ⟨3771521, by rfl⟩ : syracuseStep 5028695 = 7543043) B7543043
theorem B3352463 : Blo 2233435 3352463 := bstep (se 1 (by rfl) ⟨2514347, by rfl⟩ : syracuseStep 3352463 = 5028695) B5028695
theorem B2234975 : Blo 2233435 2234975 := bstep (se 1 (by rfl) ⟨1676231, by rfl⟩ : syracuseStep 2234975 = 3352463) B3352463
theorem B3352469 : Blo 2233435 3352469 := bbase (se 6 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 3352469 = 157147) (by norm_num)
theorem B2234979 : Blo 2233435 2234979 := bstep (se 1 (by rfl) ⟨1676234, by rfl⟩ : syracuseStep 2234979 = 3352469) B3352469
theorem B3580013 : Blo 2233435 3580013 := bbase (se 3 (by rfl) ⟨671252, by rfl⟩ : syracuseStep 3580013 = 1342505) (by norm_num)
theorem B2386675 : Blo 2233435 2386675 := bstep (se 1 (by rfl) ⟨1790006, by rfl⟩ : syracuseStep 2386675 = 3580013) B3580013
theorem B12728933 : Blo 2233435 12728933 := bstep (se 4 (by rfl) ⟨1193337, by rfl⟩ : syracuseStep 12728933 = 2386675) B2386675
theorem B8485955 : Blo 2233435 8485955 := bstep (se 1 (by rfl) ⟨6364466, by rfl⟩ : syracuseStep 8485955 = 12728933) B12728933
theorem B5657303 : Blo 2233435 5657303 := bstep (se 1 (by rfl) ⟨4242977, by rfl⟩ : syracuseStep 5657303 = 8485955) B8485955
theorem B3771535 : Blo 2233435 3771535 := bstep (se 1 (by rfl) ⟨2828651, by rfl⟩ : syracuseStep 3771535 = 5657303) B5657303
theorem B5028713 : Blo 2233435 5028713 := bstep (se 2 (by rfl) ⟨1885767, by rfl⟩ : syracuseStep 5028713 = 3771535) B3771535
theorem B3352475 : Blo 2233435 3352475 := bstep (se 1 (by rfl) ⟨2514356, by rfl⟩ : syracuseStep 3352475 = 5028713) B5028713
theorem B2234983 : Blo 2233435 2234983 := bstep (se 1 (by rfl) ⟨1676237, by rfl⟩ : syracuseStep 2234983 = 3352475) B3352475
theorem B2514361 : Blo 2233435 2514361 := bbase (se 2 (by rfl) ⟨942885, by rfl⟩ : syracuseStep 2514361 = 1885771) (by norm_num)
theorem B3352481 : Blo 2233435 3352481 := bstep (se 2 (by rfl) ⟨1257180, by rfl⟩ : syracuseStep 3352481 = 2514361) B2514361
theorem B2234987 : Blo 2233435 2234987 := bstep (se 1 (by rfl) ⟨1676240, by rfl⟩ : syracuseStep 2234987 = 3352481) B3352481
theorem B16778549 : Blo 2233435 16778549 := bbase (se 5 (by rfl) ⟨786494, by rfl⟩ : syracuseStep 16778549 = 1572989) (by norm_num)
theorem B11185699 : Blo 2233435 11185699 := bstep (se 1 (by rfl) ⟨8389274, by rfl⟩ : syracuseStep 11185699 = 16778549) B16778549
theorem B14914265 : Blo 2233435 14914265 := bstep (se 2 (by rfl) ⟨5592849, by rfl⟩ : syracuseStep 14914265 = 11185699) B11185699
theorem B39771373 : Blo 2233435 39771373 := bstep (se 3 (by rfl) ⟨7457132, by rfl⟩ : syracuseStep 39771373 = 14914265) B14914265
theorem B53028497 : Blo 2233435 53028497 := bstep (se 2 (by rfl) ⟨19885686, by rfl⟩ : syracuseStep 53028497 = 39771373) B39771373
theorem B35352331 : Blo 2233435 35352331 := bstep (se 1 (by rfl) ⟨26514248, by rfl⟩ : syracuseStep 35352331 = 53028497) B53028497
theorem B188545765 : Blo 2233435 188545765 := bstep (se 4 (by rfl) ⟨17676165, by rfl⟩ : syracuseStep 188545765 = 35352331) B35352331
theorem B251394353 : Blo 2233435 251394353 := bstep (se 2 (by rfl) ⟨94272882, by rfl⟩ : syracuseStep 251394353 = 188545765) B188545765
theorem B167596235 : Blo 2233435 167596235 := bstep (se 1 (by rfl) ⟨125697176, by rfl⟩ : syracuseStep 167596235 = 251394353) B251394353
theorem B111730823 : Blo 2233435 111730823 := bstep (se 1 (by rfl) ⟨83798117, by rfl⟩ : syracuseStep 111730823 = 167596235) B167596235
theorem B74487215 : Blo 2233435 74487215 := bstep (se 1 (by rfl) ⟨55865411, by rfl⟩ : syracuseStep 74487215 = 111730823) B111730823
theorem B49658143 : Blo 2233435 49658143 := bstep (se 1 (by rfl) ⟨37243607, by rfl⟩ : syracuseStep 49658143 = 74487215) B74487215
theorem B66210857 : Blo 2233435 66210857 := bstep (se 2 (by rfl) ⟨24829071, by rfl⟩ : syracuseStep 66210857 = 49658143) B49658143
theorem B44140571 : Blo 2233435 44140571 := bstep (se 1 (by rfl) ⟨33105428, by rfl⟩ : syracuseStep 44140571 = 66210857) B66210857
theorem B29427047 : Blo 2233435 29427047 := bstep (se 1 (by rfl) ⟨22070285, by rfl⟩ : syracuseStep 29427047 = 44140571) B44140571
theorem B19618031 : Blo 2233435 19618031 := bstep (se 1 (by rfl) ⟨14713523, by rfl⟩ : syracuseStep 19618031 = 29427047) B29427047
theorem B52314749 : Blo 2233435 52314749 := bstep (se 3 (by rfl) ⟨9809015, by rfl⟩ : syracuseStep 52314749 = 19618031) B19618031
theorem B34876499 : Blo 2233435 34876499 := bstep (se 1 (by rfl) ⟨26157374, by rfl⟩ : syracuseStep 34876499 = 52314749) B52314749
theorem B93003997 : Blo 2233435 93003997 := bstep (se 3 (by rfl) ⟨17438249, by rfl⟩ : syracuseStep 93003997 = 34876499) B34876499
theorem B124005329 : Blo 2233435 124005329 := bstep (se 2 (by rfl) ⟨46501998, by rfl⟩ : syracuseStep 124005329 = 93003997) B93003997
theorem B82670219 : Blo 2233435 82670219 := bstep (se 1 (by rfl) ⟨62002664, by rfl⟩ : syracuseStep 82670219 = 124005329) B124005329
theorem B55113479 : Blo 2233435 55113479 := bstep (se 1 (by rfl) ⟨41335109, by rfl⟩ : syracuseStep 55113479 = 82670219) B82670219
theorem B36742319 : Blo 2233435 36742319 := bstep (se 1 (by rfl) ⟨27556739, by rfl⟩ : syracuseStep 36742319 = 55113479) B55113479
theorem B24494879 : Blo 2233435 24494879 := bstep (se 1 (by rfl) ⟨18371159, by rfl⟩ : syracuseStep 24494879 = 36742319) B36742319
theorem B16329919 : Blo 2233435 16329919 := bstep (se 1 (by rfl) ⟨12247439, by rfl⟩ : syracuseStep 16329919 = 24494879) B24494879
theorem B21773225 : Blo 2233435 21773225 := bstep (se 2 (by rfl) ⟨8164959, by rfl⟩ : syracuseStep 21773225 = 16329919) B16329919
theorem B58061933 : Blo 2233435 58061933 := bstep (se 3 (by rfl) ⟨10886612, by rfl⟩ : syracuseStep 58061933 = 21773225) B21773225
theorem B38707955 : Blo 2233435 38707955 := bstep (se 1 (by rfl) ⟨29030966, by rfl⟩ : syracuseStep 38707955 = 58061933) B58061933
theorem B25805303 : Blo 2233435 25805303 := bstep (se 1 (by rfl) ⟨19353977, by rfl⟩ : syracuseStep 25805303 = 38707955) B38707955
theorem B17203535 : Blo 2233435 17203535 := bstep (se 1 (by rfl) ⟨12902651, by rfl⟩ : syracuseStep 17203535 = 25805303) B25805303
theorem B11469023 : Blo 2233435 11469023 := bstep (se 1 (by rfl) ⟨8601767, by rfl⟩ : syracuseStep 11469023 = 17203535) B17203535
theorem B7646015 : Blo 2233435 7646015 := bstep (se 1 (by rfl) ⟨5734511, by rfl⟩ : syracuseStep 7646015 = 11469023) B11469023
theorem B5097343 : Blo 2233435 5097343 := bstep (se 1 (by rfl) ⟨3823007, by rfl⟩ : syracuseStep 5097343 = 7646015) B7646015
theorem B6796457 : Blo 2233435 6796457 := bstep (se 2 (by rfl) ⟨2548671, by rfl⟩ : syracuseStep 6796457 = 5097343) B5097343
theorem B4530971 : Blo 2233435 4530971 := bstep (se 1 (by rfl) ⟨3398228, by rfl⟩ : syracuseStep 4530971 = 6796457) B6796457
theorem B3020647 : Blo 2233435 3020647 := bstep (se 1 (by rfl) ⟨2265485, by rfl⟩ : syracuseStep 3020647 = 4530971) B4530971
theorem B4027529 : Blo 2233435 4027529 := bstep (se 2 (by rfl) ⟨1510323, by rfl⟩ : syracuseStep 4027529 = 3020647) B3020647
theorem B10740077 : Blo 2233435 10740077 := bstep (se 3 (by rfl) ⟨2013764, by rfl⟩ : syracuseStep 10740077 = 4027529) B4027529
theorem B7160051 : Blo 2233435 7160051 := bstep (se 1 (by rfl) ⟨5370038, by rfl⟩ : syracuseStep 7160051 = 10740077) B10740077
theorem B4773367 : Blo 2233435 4773367 := bstep (se 1 (by rfl) ⟨3580025, by rfl⟩ : syracuseStep 4773367 = 7160051) B7160051
theorem B6364489 : Blo 2233435 6364489 := bstep (se 2 (by rfl) ⟨2386683, by rfl⟩ : syracuseStep 6364489 = 4773367) B4773367
theorem B8485985 : Blo 2233435 8485985 := bstep (se 2 (by rfl) ⟨3182244, by rfl⟩ : syracuseStep 8485985 = 6364489) B6364489
theorem B5657323 : Blo 2233435 5657323 := bstep (se 1 (by rfl) ⟨4242992, by rfl⟩ : syracuseStep 5657323 = 8485985) B8485985
theorem B7543097 : Blo 2233435 7543097 := bstep (se 2 (by rfl) ⟨2828661, by rfl⟩ : syracuseStep 7543097 = 5657323) B5657323
theorem B5028731 : Blo 2233435 5028731 := bstep (se 1 (by rfl) ⟨3771548, by rfl⟩ : syracuseStep 5028731 = 7543097) B7543097
theorem B3352487 : Blo 2233435 3352487 := bstep (se 1 (by rfl) ⟨2514365, by rfl⟩ : syracuseStep 3352487 = 5028731) B5028731
theorem B2234991 : Blo 2233435 2234991 := bstep (se 1 (by rfl) ⟨1676243, by rfl⟩ : syracuseStep 2234991 = 3352487) B3352487
theorem B3352493 : Blo 2233435 3352493 := bbase (se 3 (by rfl) ⟨628592, by rfl⟩ : syracuseStep 3352493 = 1257185) (by norm_num)
theorem B2234995 : Blo 2233435 2234995 := bstep (se 1 (by rfl) ⟨1676246, by rfl⟩ : syracuseStep 2234995 = 3352493) B3352493
theorem B5028749 : Blo 2233435 5028749 := bbase (se 3 (by rfl) ⟨942890, by rfl⟩ : syracuseStep 5028749 = 1885781) (by norm_num)
theorem B3352499 : Blo 2233435 3352499 := bstep (se 1 (by rfl) ⟨2514374, by rfl⟩ : syracuseStep 3352499 = 5028749) B5028749
theorem B2234999 : Blo 2233435 2234999 := bstep (se 1 (by rfl) ⟨1676249, by rfl⟩ : syracuseStep 2234999 = 3352499) B3352499
theorem B2828677 : Blo 2233435 2828677 := bbase (se 4 (by rfl) ⟨265188, by rfl⟩ : syracuseStep 2828677 = 530377) (by norm_num)
theorem B3771569 : Blo 2233435 3771569 := bstep (se 2 (by rfl) ⟨1414338, by rfl⟩ : syracuseStep 3771569 = 2828677) B2828677
theorem B2514379 : Blo 2233435 2514379 := bstep (se 1 (by rfl) ⟨1885784, by rfl⟩ : syracuseStep 2514379 = 3771569) B3771569
theorem B3352505 : Blo 2233435 3352505 := bstep (se 2 (by rfl) ⟨1257189, by rfl⟩ : syracuseStep 3352505 = 2514379) B2514379
theorem B2235003 : Blo 2233435 2235003 := bstep (se 1 (by rfl) ⟨1676252, by rfl⟩ : syracuseStep 2235003 = 3352505) B3352505
theorem B28640405 : Blo 2233435 28640405 := bbase (se 6 (by rfl) ⟨671259, by rfl⟩ : syracuseStep 28640405 = 1342519) (by norm_num)
theorem B19093603 : Blo 2233435 19093603 := bstep (se 1 (by rfl) ⟨14320202, by rfl⟩ : syracuseStep 19093603 = 28640405) B28640405
theorem B25458137 : Blo 2233435 25458137 := bstep (se 2 (by rfl) ⟨9546801, by rfl⟩ : syracuseStep 25458137 = 19093603) B19093603
theorem B16972091 : Blo 2233435 16972091 := bstep (se 1 (by rfl) ⟨12729068, by rfl⟩ : syracuseStep 16972091 = 25458137) B25458137
theorem B11314727 : Blo 2233435 11314727 := bstep (se 1 (by rfl) ⟨8486045, by rfl⟩ : syracuseStep 11314727 = 16972091) B16972091
theorem B7543151 : Blo 2233435 7543151 := bstep (se 1 (by rfl) ⟨5657363, by rfl⟩ : syracuseStep 7543151 = 11314727) B11314727
theorem B5028767 : Blo 2233435 5028767 := bstep (se 1 (by rfl) ⟨3771575, by rfl⟩ : syracuseStep 5028767 = 7543151) B7543151
theorem B3352511 : Blo 2233435 3352511 := bstep (se 1 (by rfl) ⟨2514383, by rfl⟩ : syracuseStep 3352511 = 5028767) B5028767
theorem B2235007 : Blo 2233435 2235007 := bstep (se 1 (by rfl) ⟨1676255, by rfl⟩ : syracuseStep 2235007 = 3352511) B3352511
theorem B3352517 : Blo 2233435 3352517 := bbase (se 4 (by rfl) ⟨314298, by rfl⟩ : syracuseStep 3352517 = 628597) (by norm_num)
theorem B2235011 : Blo 2233435 2235011 := bstep (se 1 (by rfl) ⟨1676258, by rfl⟩ : syracuseStep 2235011 = 3352517) B3352517
theorem B3771589 : Blo 2233435 3771589 := bbase (se 4 (by rfl) ⟨353586, by rfl⟩ : syracuseStep 3771589 = 707173) (by norm_num)
theorem B5028785 : Blo 2233435 5028785 := bstep (se 2 (by rfl) ⟨1885794, by rfl⟩ : syracuseStep 5028785 = 3771589) B3771589
theorem B3352523 : Blo 2233435 3352523 := bstep (se 1 (by rfl) ⟨2514392, by rfl⟩ : syracuseStep 3352523 = 5028785) B5028785
theorem B2235015 : Blo 2233435 2235015 := bstep (se 1 (by rfl) ⟨1676261, by rfl⟩ : syracuseStep 2235015 = 3352523) B3352523
theorem B2514397 : Blo 2233435 2514397 := bbase (se 3 (by rfl) ⟨471449, by rfl⟩ : syracuseStep 2514397 = 942899) (by norm_num)
theorem B3352529 : Blo 2233435 3352529 := bstep (se 2 (by rfl) ⟨1257198, by rfl⟩ : syracuseStep 3352529 = 2514397) B2514397
theorem B2235019 : Blo 2233435 2235019 := bstep (se 1 (by rfl) ⟨1676264, by rfl⟩ : syracuseStep 2235019 = 3352529) B3352529
theorem B7543205 : Blo 2233435 7543205 := bbase (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) (by norm_num)
theorem B5028803 : Blo 2233435 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B3352535 : Blo 2233435 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B2235023 : Blo 2233435 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B3352541 : Blo 2233435 3352541 := bbase (se 3 (by rfl) ⟨628601, by rfl⟩ : syracuseStep 3352541 = 1257203) (by norm_num)
theorem B2235027 : Blo 2233435 2235027 := bstep (se 1 (by rfl) ⟨1676270, by rfl⟩ : syracuseStep 2235027 = 3352541) B3352541
theorem B5028821 : Blo 2233435 5028821 := bbase (se 7 (by rfl) ⟨58931, by rfl⟩ : syracuseStep 5028821 = 117863) (by norm_num)
theorem B3352547 : Blo 2233435 3352547 := bstep (se 1 (by rfl) ⟨2514410, by rfl⟩ : syracuseStep 3352547 = 5028821) B5028821
theorem B2235031 : Blo 2233435 2235031 := bstep (se 1 (by rfl) ⟨1676273, by rfl⟩ : syracuseStep 2235031 = 3352547) B3352547
theorem B6041413 : Blo 2233435 6041413 := bbase (se 4 (by rfl) ⟨566382, by rfl⟩ : syracuseStep 6041413 = 1132765) (by norm_num)
theorem B8055217 : Blo 2233435 8055217 := bstep (se 2 (by rfl) ⟨3020706, by rfl⟩ : syracuseStep 8055217 = 6041413) B6041413
theorem B10740289 : Blo 2233435 10740289 := bstep (se 2 (by rfl) ⟨4027608, by rfl⟩ : syracuseStep 10740289 = 8055217) B8055217
theorem B14320385 : Blo 2233435 14320385 := bstep (se 2 (by rfl) ⟨5370144, by rfl⟩ : syracuseStep 14320385 = 10740289) B10740289
theorem B9546923 : Blo 2233435 9546923 := bstep (se 1 (by rfl) ⟨7160192, by rfl⟩ : syracuseStep 9546923 = 14320385) B14320385
theorem B6364615 : Blo 2233435 6364615 := bstep (se 1 (by rfl) ⟨4773461, by rfl⟩ : syracuseStep 6364615 = 9546923) B9546923
theorem B8486153 : Blo 2233435 8486153 := bstep (se 2 (by rfl) ⟨3182307, by rfl⟩ : syracuseStep 8486153 = 6364615) B6364615
theorem B5657435 : Blo 2233435 5657435 := bstep (se 1 (by rfl) ⟨4243076, by rfl⟩ : syracuseStep 5657435 = 8486153) B8486153
theorem B3771623 : Blo 2233435 3771623 := bstep (se 1 (by rfl) ⟨2828717, by rfl⟩ : syracuseStep 3771623 = 5657435) B5657435
theorem B2514415 : Blo 2233435 2514415 := bstep (se 1 (by rfl) ⟨1885811, by rfl⟩ : syracuseStep 2514415 = 3771623) B3771623
theorem B3352553 : Blo 2233435 3352553 := bstep (se 2 (by rfl) ⟨1257207, by rfl⟩ : syracuseStep 3352553 = 2514415) B2514415
theorem B2235035 : Blo 2233435 2235035 := bstep (se 1 (by rfl) ⟨1676276, by rfl⟩ : syracuseStep 2235035 = 3352553) B3352553
theorem B19093877 : Blo 2233435 19093877 := bbase (se 5 (by rfl) ⟨895025, by rfl⟩ : syracuseStep 19093877 = 1790051) (by norm_num)
theorem B12729251 : Blo 2233435 12729251 := bstep (se 1 (by rfl) ⟨9546938, by rfl⟩ : syracuseStep 12729251 = 19093877) B19093877
theorem B8486167 : Blo 2233435 8486167 := bstep (se 1 (by rfl) ⟨6364625, by rfl⟩ : syracuseStep 8486167 = 12729251) B12729251
theorem B11314889 : Blo 2233435 11314889 := bstep (se 2 (by rfl) ⟨4243083, by rfl⟩ : syracuseStep 11314889 = 8486167) B8486167
theorem B7543259 : Blo 2233435 7543259 := bstep (se 1 (by rfl) ⟨5657444, by rfl⟩ : syracuseStep 7543259 = 11314889) B11314889
theorem B5028839 : Blo 2233435 5028839 := bstep (se 1 (by rfl) ⟨3771629, by rfl⟩ : syracuseStep 5028839 = 7543259) B7543259
theorem B3352559 : Blo 2233435 3352559 := bstep (se 1 (by rfl) ⟨2514419, by rfl⟩ : syracuseStep 3352559 = 5028839) B5028839
theorem B2235039 : Blo 2233435 2235039 := bstep (se 1 (by rfl) ⟨1676279, by rfl⟩ : syracuseStep 2235039 = 3352559) B3352559
theorem B3352565 : Blo 2233435 3352565 := bbase (se 5 (by rfl) ⟨157151, by rfl⟩ : syracuseStep 3352565 = 314303) (by norm_num)
theorem B2235043 : Blo 2233435 2235043 := bstep (se 1 (by rfl) ⟨1676282, by rfl⟩ : syracuseStep 2235043 = 3352565) B3352565
theorem B4138285 : Blo 2233435 4138285 := bbase (se 3 (by rfl) ⟨775928, by rfl⟩ : syracuseStep 4138285 = 1551857) (by norm_num)
theorem B5517713 : Blo 2233435 5517713 := bstep (se 2 (by rfl) ⟨2069142, by rfl⟩ : syracuseStep 5517713 = 4138285) B4138285
theorem B3678475 : Blo 2233435 3678475 := bstep (se 1 (by rfl) ⟨2758856, by rfl⟩ : syracuseStep 3678475 = 5517713) B5517713
theorem B4904633 : Blo 2233435 4904633 := bstep (se 2 (by rfl) ⟨1839237, by rfl⟩ : syracuseStep 4904633 = 3678475) B3678475
theorem B3269755 : Blo 2233435 3269755 := bstep (se 1 (by rfl) ⟨2452316, by rfl⟩ : syracuseStep 3269755 = 4904633) B4904633
theorem B4359673 : Blo 2233435 4359673 := bstep (se 2 (by rfl) ⟨1634877, by rfl⟩ : syracuseStep 4359673 = 3269755) B3269755
theorem B5812897 : Blo 2233435 5812897 := bstep (se 2 (by rfl) ⟨2179836, by rfl⟩ : syracuseStep 5812897 = 4359673) B4359673
theorem B7750529 : Blo 2233435 7750529 := bstep (se 2 (by rfl) ⟨2906448, by rfl⟩ : syracuseStep 7750529 = 5812897) B5812897
theorem B5167019 : Blo 2233435 5167019 := bstep (se 1 (by rfl) ⟨3875264, by rfl⟩ : syracuseStep 5167019 = 7750529) B7750529
theorem B3444679 : Blo 2233435 3444679 := bstep (se 1 (by rfl) ⟨2583509, by rfl⟩ : syracuseStep 3444679 = 5167019) B5167019
theorem B4592905 : Blo 2233435 4592905 := bstep (se 2 (by rfl) ⟨1722339, by rfl⟩ : syracuseStep 4592905 = 3444679) B3444679
theorem B97981973 : Blo 2233435 97981973 := bstep (se 6 (by rfl) ⟨2296452, by rfl⟩ : syracuseStep 97981973 = 4592905) B4592905
theorem B65321315 : Blo 2233435 65321315 := bstep (se 1 (by rfl) ⟨48990986, by rfl⟩ : syracuseStep 65321315 = 97981973) B97981973
theorem B43547543 : Blo 2233435 43547543 := bstep (se 1 (by rfl) ⟨32660657, by rfl⟩ : syracuseStep 43547543 = 65321315) B65321315
theorem B29031695 : Blo 2233435 29031695 := bstep (se 1 (by rfl) ⟨21773771, by rfl⟩ : syracuseStep 29031695 = 43547543) B43547543
theorem B19354463 : Blo 2233435 19354463 := bstep (se 1 (by rfl) ⟨14515847, by rfl⟩ : syracuseStep 19354463 = 29031695) B29031695
theorem B12902975 : Blo 2233435 12902975 := bstep (se 1 (by rfl) ⟨9677231, by rfl⟩ : syracuseStep 12902975 = 19354463) B19354463
theorem B8601983 : Blo 2233435 8601983 := bstep (se 1 (by rfl) ⟨6451487, by rfl⟩ : syracuseStep 8601983 = 12902975) B12902975
theorem B5734655 : Blo 2233435 5734655 := bstep (se 1 (by rfl) ⟨4300991, by rfl⟩ : syracuseStep 5734655 = 8601983) B8601983
theorem B3823103 : Blo 2233435 3823103 := bstep (se 1 (by rfl) ⟨2867327, by rfl⟩ : syracuseStep 3823103 = 5734655) B5734655
theorem B2548735 : Blo 2233435 2548735 := bstep (se 1 (by rfl) ⟨1911551, by rfl⟩ : syracuseStep 2548735 = 3823103) B3823103
theorem B13593253 : Blo 2233435 13593253 := bstep (se 4 (by rfl) ⟨1274367, by rfl⟩ : syracuseStep 13593253 = 2548735) B2548735
theorem B18124337 : Blo 2233435 18124337 := bstep (se 2 (by rfl) ⟨6796626, by rfl⟩ : syracuseStep 18124337 = 13593253) B13593253
theorem B12082891 : Blo 2233435 12082891 := bstep (se 1 (by rfl) ⟨9062168, by rfl⟩ : syracuseStep 12082891 = 18124337) B18124337
theorem B16110521 : Blo 2233435 16110521 := bstep (se 2 (by rfl) ⟨6041445, by rfl⟩ : syracuseStep 16110521 = 12082891) B12082891
theorem B10740347 : Blo 2233435 10740347 := bstep (se 1 (by rfl) ⟨8055260, by rfl⟩ : syracuseStep 10740347 = 16110521) B16110521
theorem B7160231 : Blo 2233435 7160231 := bstep (se 1 (by rfl) ⟨5370173, by rfl⟩ : syracuseStep 7160231 = 10740347) B10740347
theorem B4773487 : Blo 2233435 4773487 := bstep (se 1 (by rfl) ⟨3580115, by rfl⟩ : syracuseStep 4773487 = 7160231) B7160231
theorem B6364649 : Blo 2233435 6364649 := bstep (se 2 (by rfl) ⟨2386743, by rfl⟩ : syracuseStep 6364649 = 4773487) B4773487
theorem B4243099 : Blo 2233435 4243099 := bstep (se 1 (by rfl) ⟨3182324, by rfl⟩ : syracuseStep 4243099 = 6364649) B6364649
theorem B5657465 : Blo 2233435 5657465 := bstep (se 2 (by rfl) ⟨2121549, by rfl⟩ : syracuseStep 5657465 = 4243099) B4243099
theorem B3771643 : Blo 2233435 3771643 := bstep (se 1 (by rfl) ⟨2828732, by rfl⟩ : syracuseStep 3771643 = 5657465) B5657465
theorem B5028857 : Blo 2233435 5028857 := bstep (se 2 (by rfl) ⟨1885821, by rfl⟩ : syracuseStep 5028857 = 3771643) B3771643
theorem B3352571 : Blo 2233435 3352571 := bstep (se 1 (by rfl) ⟨2514428, by rfl⟩ : syracuseStep 3352571 = 5028857) B5028857
theorem B2235047 : Blo 2233435 2235047 := bstep (se 1 (by rfl) ⟨1676285, by rfl⟩ : syracuseStep 2235047 = 3352571) B3352571
theorem B2514433 : Blo 2233435 2514433 := bbase (se 2 (by rfl) ⟨942912, by rfl⟩ : syracuseStep 2514433 = 1885825) (by norm_num)
theorem B3352577 : Blo 2233435 3352577 := bstep (se 2 (by rfl) ⟨1257216, by rfl⟩ : syracuseStep 3352577 = 2514433) B2514433
theorem B2235051 : Blo 2233435 2235051 := bstep (se 1 (by rfl) ⟨1676288, by rfl⟩ : syracuseStep 2235051 = 3352577) B3352577
theorem B5657485 : Blo 2233435 5657485 := bbase (se 3 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 5657485 = 2121557) (by norm_num)
theorem B7543313 : Blo 2233435 7543313 := bstep (se 2 (by rfl) ⟨2828742, by rfl⟩ : syracuseStep 7543313 = 5657485) B5657485
theorem B5028875 : Blo 2233435 5028875 := bstep (se 1 (by rfl) ⟨3771656, by rfl⟩ : syracuseStep 5028875 = 7543313) B7543313
theorem B3352583 : Blo 2233435 3352583 := bstep (se 1 (by rfl) ⟨2514437, by rfl⟩ : syracuseStep 3352583 = 5028875) B5028875
theorem B2235055 : Blo 2233435 2235055 := bstep (se 1 (by rfl) ⟨1676291, by rfl⟩ : syracuseStep 2235055 = 3352583) B3352583
theorem B3352589 : Blo 2233435 3352589 := bbase (se 3 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 3352589 = 1257221) (by norm_num)
theorem B2235059 : Blo 2233435 2235059 := bstep (se 1 (by rfl) ⟨1676294, by rfl⟩ : syracuseStep 2235059 = 3352589) B3352589
theorem B5028893 : Blo 2233435 5028893 := bbase (se 3 (by rfl) ⟨942917, by rfl⟩ : syracuseStep 5028893 = 1885835) (by norm_num)
theorem B3352595 : Blo 2233435 3352595 := bstep (se 1 (by rfl) ⟨2514446, by rfl⟩ : syracuseStep 3352595 = 5028893) B5028893
theorem B2235063 : Blo 2233435 2235063 := bstep (se 1 (by rfl) ⟨1676297, by rfl⟩ : syracuseStep 2235063 = 3352595) B3352595
theorem B3771677 : Blo 2233435 3771677 := bbase (se 3 (by rfl) ⟨707189, by rfl⟩ : syracuseStep 3771677 = 1414379) (by norm_num)
theorem B2514451 : Blo 2233435 2514451 := bstep (se 1 (by rfl) ⟨1885838, by rfl⟩ : syracuseStep 2514451 = 3771677) B3771677
theorem B3352601 : Blo 2233435 3352601 := bstep (se 2 (by rfl) ⟨1257225, by rfl⟩ : syracuseStep 3352601 = 2514451) B2514451
theorem B2235067 : Blo 2233435 2235067 := bstep (se 1 (by rfl) ⟨1676300, by rfl⟩ : syracuseStep 2235067 = 3352601) B3352601
theorem B4531133 : Blo 2233435 4531133 := bbase (se 3 (by rfl) ⟨849587, by rfl⟩ : syracuseStep 4531133 = 1699175) (by norm_num)
theorem B3020755 : Blo 2233435 3020755 := bstep (se 1 (by rfl) ⟨2265566, by rfl⟩ : syracuseStep 3020755 = 4531133) B4531133
theorem B4027673 : Blo 2233435 4027673 := bstep (se 2 (by rfl) ⟨1510377, by rfl⟩ : syracuseStep 4027673 = 3020755) B3020755
theorem B2685115 : Blo 2233435 2685115 := bstep (se 1 (by rfl) ⟨2013836, by rfl⟩ : syracuseStep 2685115 = 4027673) B4027673
theorem B14320613 : Blo 2233435 14320613 := bstep (se 4 (by rfl) ⟨1342557, by rfl⟩ : syracuseStep 14320613 = 2685115) B2685115
theorem B9547075 : Blo 2233435 9547075 := bstep (se 1 (by rfl) ⟨7160306, by rfl⟩ : syracuseStep 9547075 = 14320613) B14320613
theorem B12729433 : Blo 2233435 12729433 := bstep (se 2 (by rfl) ⟨4773537, by rfl⟩ : syracuseStep 12729433 = 9547075) B9547075
theorem B16972577 : Blo 2233435 16972577 := bstep (se 2 (by rfl) ⟨6364716, by rfl⟩ : syracuseStep 16972577 = 12729433) B12729433
theorem B11315051 : Blo 2233435 11315051 := bstep (se 1 (by rfl) ⟨8486288, by rfl⟩ : syracuseStep 11315051 = 16972577) B16972577
theorem B7543367 : Blo 2233435 7543367 := bstep (se 1 (by rfl) ⟨5657525, by rfl⟩ : syracuseStep 7543367 = 11315051) B11315051
theorem B5028911 : Blo 2233435 5028911 := bstep (se 1 (by rfl) ⟨3771683, by rfl⟩ : syracuseStep 5028911 = 7543367) B7543367
theorem B3352607 : Blo 2233435 3352607 := bstep (se 1 (by rfl) ⟨2514455, by rfl⟩ : syracuseStep 3352607 = 5028911) B5028911
theorem B2235071 : Blo 2233435 2235071 := bstep (se 1 (by rfl) ⟨1676303, by rfl⟩ : syracuseStep 2235071 = 3352607) B3352607
theorem B3352613 : Blo 2233435 3352613 := bbase (se 4 (by rfl) ⟨314307, by rfl⟩ : syracuseStep 3352613 = 628615) (by norm_num)
theorem B2235075 : Blo 2233435 2235075 := bstep (se 1 (by rfl) ⟨1676306, by rfl⟩ : syracuseStep 2235075 = 3352613) B3352613
theorem B2828773 : Blo 2233435 2828773 := bbase (se 4 (by rfl) ⟨265197, by rfl⟩ : syracuseStep 2828773 = 530395) (by norm_num)
theorem B3771697 : Blo 2233435 3771697 := bstep (se 2 (by rfl) ⟨1414386, by rfl⟩ : syracuseStep 3771697 = 2828773) B2828773
theorem B5028929 : Blo 2233435 5028929 := bstep (se 2 (by rfl) ⟨1885848, by rfl⟩ : syracuseStep 5028929 = 3771697) B3771697
theorem B3352619 : Blo 2233435 3352619 := bstep (se 1 (by rfl) ⟨2514464, by rfl⟩ : syracuseStep 3352619 = 5028929) B5028929
theorem B2235079 : Blo 2233435 2235079 := bstep (se 1 (by rfl) ⟨1676309, by rfl⟩ : syracuseStep 2235079 = 3352619) B3352619
theorem B2514469 : Blo 2233435 2514469 := bbase (se 4 (by rfl) ⟨235731, by rfl⟩ : syracuseStep 2514469 = 471463) (by norm_num)
theorem B3352625 : Blo 2233435 3352625 := bstep (se 2 (by rfl) ⟨1257234, by rfl⟩ : syracuseStep 3352625 = 2514469) B2514469
theorem B2235083 : Blo 2233435 2235083 := bstep (se 1 (by rfl) ⟨1676312, by rfl⟩ : syracuseStep 2235083 = 3352625) B3352625
theorem B18124661 : Blo 2233435 18124661 := bbase (se 5 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 18124661 = 1699187) (by norm_num)
theorem B12083107 : Blo 2233435 12083107 := bstep (se 1 (by rfl) ⟨9062330, by rfl⟩ : syracuseStep 12083107 = 18124661) B18124661
theorem B16110809 : Blo 2233435 16110809 := bstep (se 2 (by rfl) ⟨6041553, by rfl⟩ : syracuseStep 16110809 = 12083107) B12083107
theorem B10740539 : Blo 2233435 10740539 := bstep (se 1 (by rfl) ⟨8055404, by rfl⟩ : syracuseStep 10740539 = 16110809) B16110809
theorem B7160359 : Blo 2233435 7160359 := bstep (se 1 (by rfl) ⟨5370269, by rfl⟩ : syracuseStep 7160359 = 10740539) B10740539
theorem B9547145 : Blo 2233435 9547145 := bstep (se 2 (by rfl) ⟨3580179, by rfl⟩ : syracuseStep 9547145 = 7160359) B7160359
theorem B6364763 : Blo 2233435 6364763 := bstep (se 1 (by rfl) ⟨4773572, by rfl⟩ : syracuseStep 6364763 = 9547145) B9547145
theorem B4243175 : Blo 2233435 4243175 := bstep (se 1 (by rfl) ⟨3182381, by rfl⟩ : syracuseStep 4243175 = 6364763) B6364763
theorem B2828783 : Blo 2233435 2828783 := bstep (se 1 (by rfl) ⟨2121587, by rfl⟩ : syracuseStep 2828783 = 4243175) B4243175
theorem B7543421 : Blo 2233435 7543421 := bstep (se 3 (by rfl) ⟨1414391, by rfl⟩ : syracuseStep 7543421 = 2828783) B2828783
theorem B5028947 : Blo 2233435 5028947 := bstep (se 1 (by rfl) ⟨3771710, by rfl⟩ : syracuseStep 5028947 = 7543421) B7543421
theorem B3352631 : Blo 2233435 3352631 := bstep (se 1 (by rfl) ⟨2514473, by rfl⟩ : syracuseStep 3352631 = 5028947) B5028947
theorem B2235087 : Blo 2233435 2235087 := bstep (se 1 (by rfl) ⟨1676315, by rfl⟩ : syracuseStep 2235087 = 3352631) B3352631
theorem B3352637 : Blo 2233435 3352637 := bbase (se 3 (by rfl) ⟨628619, by rfl⟩ : syracuseStep 3352637 = 1257239) (by norm_num)
theorem B2235091 : Blo 2233435 2235091 := bstep (se 1 (by rfl) ⟨1676318, by rfl⟩ : syracuseStep 2235091 = 3352637) B3352637
theorem B5028965 : Blo 2233435 5028965 := bbase (se 4 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 5028965 = 942931) (by norm_num)
theorem B3352643 : Blo 2233435 3352643 := bstep (se 1 (by rfl) ⟨2514482, by rfl⟩ : syracuseStep 3352643 = 5028965) B5028965
theorem B2235095 : Blo 2233435 2235095 := bstep (se 1 (by rfl) ⟨1676321, by rfl⟩ : syracuseStep 2235095 = 3352643) B3352643
theorem B5657597 : Blo 2233435 5657597 := bbase (se 3 (by rfl) ⟨1060799, by rfl⟩ : syracuseStep 5657597 = 2121599) (by norm_num)
theorem B3771731 : Blo 2233435 3771731 := bstep (se 1 (by rfl) ⟨2828798, by rfl⟩ : syracuseStep 3771731 = 5657597) B5657597
theorem B2514487 : Blo 2233435 2514487 := bstep (se 1 (by rfl) ⟨1885865, by rfl⟩ : syracuseStep 2514487 = 3771731) B3771731
theorem B3352649 : Blo 2233435 3352649 := bstep (se 2 (by rfl) ⟨1257243, by rfl⟩ : syracuseStep 3352649 = 2514487) B2514487
theorem B2235099 : Blo 2233435 2235099 := bstep (se 1 (by rfl) ⟨1676324, by rfl⟩ : syracuseStep 2235099 = 3352649) B3352649
theorem B4243205 : Blo 2233435 4243205 := bbase (se 4 (by rfl) ⟨397800, by rfl⟩ : syracuseStep 4243205 = 795601) (by norm_num)
theorem B11315213 : Blo 2233435 11315213 := bstep (se 3 (by rfl) ⟨2121602, by rfl⟩ : syracuseStep 11315213 = 4243205) B4243205
theorem B7543475 : Blo 2233435 7543475 := bstep (se 1 (by rfl) ⟨5657606, by rfl⟩ : syracuseStep 7543475 = 11315213) B11315213
theorem B5028983 : Blo 2233435 5028983 := bstep (se 1 (by rfl) ⟨3771737, by rfl⟩ : syracuseStep 5028983 = 7543475) B7543475
theorem B3352655 : Blo 2233435 3352655 := bstep (se 1 (by rfl) ⟨2514491, by rfl⟩ : syracuseStep 3352655 = 5028983) B5028983
theorem B2235103 : Blo 2233435 2235103 := bstep (se 1 (by rfl) ⟨1676327, by rfl⟩ : syracuseStep 2235103 = 3352655) B3352655
theorem B3352661 : Blo 2233435 3352661 := bbase (se 8 (by rfl) ⟨19644, by rfl⟩ : syracuseStep 3352661 = 39289) (by norm_num)
theorem B2235107 : Blo 2233435 2235107 := bstep (se 1 (by rfl) ⟨1676330, by rfl⟩ : syracuseStep 2235107 = 3352661) B3352661
theorem B20950645 : Blo 2233435 20950645 := bbase (se 5 (by rfl) ⟨982061, by rfl⟩ : syracuseStep 20950645 = 1964123) (by norm_num)
theorem B27934193 : Blo 2233435 27934193 := bstep (se 2 (by rfl) ⟨10475322, by rfl⟩ : syracuseStep 27934193 = 20950645) B20950645
theorem B18622795 : Blo 2233435 18622795 := bstep (se 1 (by rfl) ⟨13967096, by rfl⟩ : syracuseStep 18622795 = 27934193) B27934193
theorem B24830393 : Blo 2233435 24830393 := bstep (se 2 (by rfl) ⟨9311397, by rfl⟩ : syracuseStep 24830393 = 18622795) B18622795
theorem B264857525 : Blo 2233435 264857525 := bstep (se 5 (by rfl) ⟨12415196, by rfl⟩ : syracuseStep 264857525 = 24830393) B24830393
theorem B176571683 : Blo 2233435 176571683 := bstep (se 1 (by rfl) ⟨132428762, by rfl⟩ : syracuseStep 176571683 = 264857525) B264857525
theorem B117714455 : Blo 2233435 117714455 := bstep (se 1 (by rfl) ⟨88285841, by rfl⟩ : syracuseStep 117714455 = 176571683) B176571683
theorem B78476303 : Blo 2233435 78476303 := bstep (se 1 (by rfl) ⟨58857227, by rfl⟩ : syracuseStep 78476303 = 117714455) B117714455
theorem B52317535 : Blo 2233435 52317535 := bstep (se 1 (by rfl) ⟨39238151, by rfl⟩ : syracuseStep 52317535 = 78476303) B78476303
theorem B69756713 : Blo 2233435 69756713 := bstep (se 2 (by rfl) ⟨26158767, by rfl⟩ : syracuseStep 69756713 = 52317535) B52317535
theorem B46504475 : Blo 2233435 46504475 := bstep (se 1 (by rfl) ⟨34878356, by rfl⟩ : syracuseStep 46504475 = 69756713) B69756713
theorem B31002983 : Blo 2233435 31002983 := bstep (se 1 (by rfl) ⟨23252237, by rfl⟩ : syracuseStep 31002983 = 46504475) B46504475
theorem B20668655 : Blo 2233435 20668655 := bstep (se 1 (by rfl) ⟨15501491, by rfl⟩ : syracuseStep 20668655 = 31002983) B31002983
theorem B55116413 : Blo 2233435 55116413 := bstep (se 3 (by rfl) ⟨10334327, by rfl⟩ : syracuseStep 55116413 = 20668655) B20668655
theorem B36744275 : Blo 2233435 36744275 := bstep (se 1 (by rfl) ⟨27558206, by rfl⟩ : syracuseStep 36744275 = 55116413) B55116413
theorem B24496183 : Blo 2233435 24496183 := bstep (se 1 (by rfl) ⟨18372137, by rfl⟩ : syracuseStep 24496183 = 36744275) B36744275
theorem B32661577 : Blo 2233435 32661577 := bstep (se 2 (by rfl) ⟨12248091, by rfl⟩ : syracuseStep 32661577 = 24496183) B24496183
theorem B43548769 : Blo 2233435 43548769 := bstep (se 2 (by rfl) ⟨16330788, by rfl⟩ : syracuseStep 43548769 = 32661577) B32661577
theorem B58065025 : Blo 2233435 58065025 := bstep (se 2 (by rfl) ⟨21774384, by rfl⟩ : syracuseStep 58065025 = 43548769) B43548769
theorem B77420033 : Blo 2233435 77420033 := bstep (se 2 (by rfl) ⟨29032512, by rfl⟩ : syracuseStep 77420033 = 58065025) B58065025
theorem B51613355 : Blo 2233435 51613355 := bstep (se 1 (by rfl) ⟨38710016, by rfl⟩ : syracuseStep 51613355 = 77420033) B77420033
theorem B34408903 : Blo 2233435 34408903 := bstep (se 1 (by rfl) ⟨25806677, by rfl⟩ : syracuseStep 34408903 = 51613355) B51613355
theorem B45878537 : Blo 2233435 45878537 := bstep (se 2 (by rfl) ⟨17204451, by rfl⟩ : syracuseStep 45878537 = 34408903) B34408903
theorem B30585691 : Blo 2233435 30585691 := bstep (se 1 (by rfl) ⟨22939268, by rfl⟩ : syracuseStep 30585691 = 45878537) B45878537
theorem B40780921 : Blo 2233435 40780921 := bstep (se 2 (by rfl) ⟨15292845, by rfl⟩ : syracuseStep 40780921 = 30585691) B30585691
theorem B54374561 : Blo 2233435 54374561 := bstep (se 2 (by rfl) ⟨20390460, by rfl⟩ : syracuseStep 54374561 = 40780921) B40780921
theorem B36249707 : Blo 2233435 36249707 := bstep (se 1 (by rfl) ⟨27187280, by rfl⟩ : syracuseStep 36249707 = 54374561) B54374561
theorem B24166471 : Blo 2233435 24166471 := bstep (se 1 (by rfl) ⟨18124853, by rfl⟩ : syracuseStep 24166471 = 36249707) B36249707
theorem B32221961 : Blo 2233435 32221961 := bstep (se 2 (by rfl) ⟨12083235, by rfl⟩ : syracuseStep 32221961 = 24166471) B24166471
theorem B21481307 : Blo 2233435 21481307 := bstep (se 1 (by rfl) ⟨16110980, by rfl⟩ : syracuseStep 21481307 = 32221961) B32221961
theorem B14320871 : Blo 2233435 14320871 := bstep (se 1 (by rfl) ⟨10740653, by rfl⟩ : syracuseStep 14320871 = 21481307) B21481307
theorem B9547247 : Blo 2233435 9547247 := bstep (se 1 (by rfl) ⟨7160435, by rfl⟩ : syracuseStep 9547247 = 14320871) B14320871
theorem B6364831 : Blo 2233435 6364831 := bstep (se 1 (by rfl) ⟨4773623, by rfl⟩ : syracuseStep 6364831 = 9547247) B9547247
theorem B8486441 : Blo 2233435 8486441 := bstep (se 2 (by rfl) ⟨3182415, by rfl⟩ : syracuseStep 8486441 = 6364831) B6364831
theorem B5657627 : Blo 2233435 5657627 := bstep (se 1 (by rfl) ⟨4243220, by rfl⟩ : syracuseStep 5657627 = 8486441) B8486441
theorem B3771751 : Blo 2233435 3771751 := bstep (se 1 (by rfl) ⟨2828813, by rfl⟩ : syracuseStep 3771751 = 5657627) B5657627
theorem B5029001 : Blo 2233435 5029001 := bstep (se 2 (by rfl) ⟨1885875, by rfl⟩ : syracuseStep 5029001 = 3771751) B3771751
theorem B3352667 : Blo 2233435 3352667 := bstep (se 1 (by rfl) ⟨2514500, by rfl⟩ : syracuseStep 3352667 = 5029001) B5029001
theorem B2235111 : Blo 2233435 2235111 := bstep (se 1 (by rfl) ⟨1676333, by rfl⟩ : syracuseStep 2235111 = 3352667) B3352667
theorem B2514505 : Blo 2233435 2514505 := bbase (se 2 (by rfl) ⟨942939, by rfl⟩ : syracuseStep 2514505 = 1885879) (by norm_num)
theorem B3352673 : Blo 2233435 3352673 := bstep (se 2 (by rfl) ⟨1257252, by rfl⟩ : syracuseStep 3352673 = 2514505) B2514505
theorem B2235115 : Blo 2233435 2235115 := bstep (se 1 (by rfl) ⟨1676336, by rfl⟩ : syracuseStep 2235115 = 3352673) B3352673
theorem B2721809 : Blo 2233435 2721809 := bbase (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) (by norm_num)
theorem B7258157 : Blo 2233435 7258157 := bstep (se 3 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 7258157 = 2721809) B2721809
theorem B4838771 : Blo 2233435 4838771 := bstep (se 1 (by rfl) ⟨3629078, by rfl⟩ : syracuseStep 4838771 = 7258157) B7258157
theorem B3225847 : Blo 2233435 3225847 := bstep (se 1 (by rfl) ⟨2419385, by rfl⟩ : syracuseStep 3225847 = 4838771) B4838771
theorem B4301129 : Blo 2233435 4301129 := bstep (se 2 (by rfl) ⟨1612923, by rfl⟩ : syracuseStep 4301129 = 3225847) B3225847
theorem B2867419 : Blo 2233435 2867419 := bstep (se 1 (by rfl) ⟨2150564, by rfl⟩ : syracuseStep 2867419 = 4301129) B4301129
theorem B15292901 : Blo 2233435 15292901 := bstep (se 4 (by rfl) ⟨1433709, by rfl⟩ : syracuseStep 15292901 = 2867419) B2867419
theorem B10195267 : Blo 2233435 10195267 := bstep (se 1 (by rfl) ⟨7646450, by rfl⟩ : syracuseStep 10195267 = 15292901) B15292901
theorem B13593689 : Blo 2233435 13593689 := bstep (se 2 (by rfl) ⟨5097633, by rfl⟩ : syracuseStep 13593689 = 10195267) B10195267
theorem B9062459 : Blo 2233435 9062459 := bstep (se 1 (by rfl) ⟨6796844, by rfl⟩ : syracuseStep 9062459 = 13593689) B13593689
theorem B6041639 : Blo 2233435 6041639 := bstep (se 1 (by rfl) ⟨4531229, by rfl⟩ : syracuseStep 6041639 = 9062459) B9062459
theorem B16111037 : Blo 2233435 16111037 := bstep (se 3 (by rfl) ⟨3020819, by rfl⟩ : syracuseStep 16111037 = 6041639) B6041639
theorem B10740691 : Blo 2233435 10740691 := bstep (se 1 (by rfl) ⟨8055518, by rfl⟩ : syracuseStep 10740691 = 16111037) B16111037
theorem B14320921 : Blo 2233435 14320921 := bstep (se 2 (by rfl) ⟨5370345, by rfl⟩ : syracuseStep 14320921 = 10740691) B10740691
theorem B19094561 : Blo 2233435 19094561 := bstep (se 2 (by rfl) ⟨7160460, by rfl⟩ : syracuseStep 19094561 = 14320921) B14320921
theorem B12729707 : Blo 2233435 12729707 := bstep (se 1 (by rfl) ⟨9547280, by rfl⟩ : syracuseStep 12729707 = 19094561) B19094561
theorem B8486471 : Blo 2233435 8486471 := bstep (se 1 (by rfl) ⟨6364853, by rfl⟩ : syracuseStep 8486471 = 12729707) B12729707
theorem B5657647 : Blo 2233435 5657647 := bstep (se 1 (by rfl) ⟨4243235, by rfl⟩ : syracuseStep 5657647 = 8486471) B8486471
theorem B7543529 : Blo 2233435 7543529 := bstep (se 2 (by rfl) ⟨2828823, by rfl⟩ : syracuseStep 7543529 = 5657647) B5657647
theorem B5029019 : Blo 2233435 5029019 := bstep (se 1 (by rfl) ⟨3771764, by rfl⟩ : syracuseStep 5029019 = 7543529) B7543529
theorem B3352679 : Blo 2233435 3352679 := bstep (se 1 (by rfl) ⟨2514509, by rfl⟩ : syracuseStep 3352679 = 5029019) B5029019
theorem B2235119 : Blo 2233435 2235119 := bstep (se 1 (by rfl) ⟨1676339, by rfl⟩ : syracuseStep 2235119 = 3352679) B3352679
theorem B3352685 : Blo 2233435 3352685 := bbase (se 3 (by rfl) ⟨628628, by rfl⟩ : syracuseStep 3352685 = 1257257) (by norm_num)
theorem B2235123 : Blo 2233435 2235123 := bstep (se 1 (by rfl) ⟨1676342, by rfl⟩ : syracuseStep 2235123 = 3352685) B3352685
theorem B5029037 : Blo 2233435 5029037 := bbase (se 3 (by rfl) ⟨942944, by rfl⟩ : syracuseStep 5029037 = 1885889) (by norm_num)
theorem B3352691 : Blo 2233435 3352691 := bstep (se 1 (by rfl) ⟨2514518, by rfl⟩ : syracuseStep 3352691 = 5029037) B5029037
theorem B2235127 : Blo 2233435 2235127 := bstep (se 1 (by rfl) ⟨1676345, by rfl⟩ : syracuseStep 2235127 = 3352691) B3352691
theorem B7160501 : Blo 2233435 7160501 := bbase (se 5 (by rfl) ⟨335648, by rfl⟩ : syracuseStep 7160501 = 671297) (by norm_num)
theorem B4773667 : Blo 2233435 4773667 := bstep (se 1 (by rfl) ⟨3580250, by rfl⟩ : syracuseStep 4773667 = 7160501) B7160501
theorem B6364889 : Blo 2233435 6364889 := bstep (se 2 (by rfl) ⟨2386833, by rfl⟩ : syracuseStep 6364889 = 4773667) B4773667
theorem B4243259 : Blo 2233435 4243259 := bstep (se 1 (by rfl) ⟨3182444, by rfl⟩ : syracuseStep 4243259 = 6364889) B6364889
theorem B2828839 : Blo 2233435 2828839 := bstep (se 1 (by rfl) ⟨2121629, by rfl⟩ : syracuseStep 2828839 = 4243259) B4243259
theorem B3771785 : Blo 2233435 3771785 := bstep (se 2 (by rfl) ⟨1414419, by rfl⟩ : syracuseStep 3771785 = 2828839) B2828839
theorem B2514523 : Blo 2233435 2514523 := bstep (se 1 (by rfl) ⟨1885892, by rfl⟩ : syracuseStep 2514523 = 3771785) B3771785
theorem B3352697 : Blo 2233435 3352697 := bstep (se 2 (by rfl) ⟨1257261, by rfl⟩ : syracuseStep 3352697 = 2514523) B2514523
theorem B2235131 : Blo 2233435 2235131 := bstep (se 1 (by rfl) ⟨1676348, by rfl⟩ : syracuseStep 2235131 = 3352697) B3352697
theorem B4719269 : Blo 2233435 4719269 := bbase (se 4 (by rfl) ⟨442431, by rfl⟩ : syracuseStep 4719269 = 884863) (by norm_num)
theorem B12584717 : Blo 2233435 12584717 := bstep (se 3 (by rfl) ⟨2359634, by rfl⟩ : syracuseStep 12584717 = 4719269) B4719269
theorem B8389811 : Blo 2233435 8389811 := bstep (se 1 (by rfl) ⟨6292358, by rfl⟩ : syracuseStep 8389811 = 12584717) B12584717
theorem B5593207 : Blo 2233435 5593207 := bstep (se 1 (by rfl) ⟨4194905, by rfl⟩ : syracuseStep 5593207 = 8389811) B8389811
theorem B7457609 : Blo 2233435 7457609 := bstep (se 2 (by rfl) ⟨2796603, by rfl⟩ : syracuseStep 7457609 = 5593207) B5593207
theorem B4971739 : Blo 2233435 4971739 := bstep (se 1 (by rfl) ⟨3728804, by rfl⟩ : syracuseStep 4971739 = 7457609) B7457609
theorem B6628985 : Blo 2233435 6628985 := bstep (se 2 (by rfl) ⟨2485869, by rfl⟩ : syracuseStep 6628985 = 4971739) B4971739
theorem B4419323 : Blo 2233435 4419323 := bstep (se 1 (by rfl) ⟨3314492, by rfl⟩ : syracuseStep 4419323 = 6628985) B6628985
theorem B47139445 : Blo 2233435 47139445 := bstep (se 5 (by rfl) ⟨2209661, by rfl⟩ : syracuseStep 47139445 = 4419323) B4419323
theorem B62852593 : Blo 2233435 62852593 := bstep (se 2 (by rfl) ⟨23569722, by rfl⟩ : syracuseStep 62852593 = 47139445) B47139445
theorem B83803457 : Blo 2233435 83803457 := bstep (se 2 (by rfl) ⟨31426296, by rfl⟩ : syracuseStep 83803457 = 62852593) B62852593
theorem B223475885 : Blo 2233435 223475885 := bstep (se 3 (by rfl) ⟨41901728, by rfl⟩ : syracuseStep 223475885 = 83803457) B83803457
theorem B148983923 : Blo 2233435 148983923 := bstep (se 1 (by rfl) ⟨111737942, by rfl⟩ : syracuseStep 148983923 = 223475885) B223475885
theorem B99322615 : Blo 2233435 99322615 := bstep (se 1 (by rfl) ⟨74491961, by rfl⟩ : syracuseStep 99322615 = 148983923) B148983923
theorem B132430153 : Blo 2233435 132430153 := bstep (se 2 (by rfl) ⟨49661307, by rfl⟩ : syracuseStep 132430153 = 99322615) B99322615
theorem B176573537 : Blo 2233435 176573537 := bstep (se 2 (by rfl) ⟨66215076, by rfl⟩ : syracuseStep 176573537 = 132430153) B132430153
theorem B117715691 : Blo 2233435 117715691 := bstep (se 1 (by rfl) ⟨88286768, by rfl⟩ : syracuseStep 117715691 = 176573537) B176573537
theorem B313908509 : Blo 2233435 313908509 := bstep (se 3 (by rfl) ⟨58857845, by rfl⟩ : syracuseStep 313908509 = 117715691) B117715691
theorem B209272339 : Blo 2233435 209272339 := bstep (se 1 (by rfl) ⟨156954254, by rfl⟩ : syracuseStep 209272339 = 313908509) B313908509
theorem B279029785 : Blo 2233435 279029785 := bstep (se 2 (by rfl) ⟨104636169, by rfl⟩ : syracuseStep 279029785 = 209272339) B209272339
theorem B372039713 : Blo 2233435 372039713 := bstep (se 2 (by rfl) ⟨139514892, by rfl⟩ : syracuseStep 372039713 = 279029785) B279029785
theorem B248026475 : Blo 2233435 248026475 := bstep (se 1 (by rfl) ⟨186019856, by rfl⟩ : syracuseStep 248026475 = 372039713) B372039713
theorem B165350983 : Blo 2233435 165350983 := bstep (se 1 (by rfl) ⟨124013237, by rfl⟩ : syracuseStep 165350983 = 248026475) B248026475
theorem B220467977 : Blo 2233435 220467977 := bstep (se 2 (by rfl) ⟨82675491, by rfl⟩ : syracuseStep 220467977 = 165350983) B165350983
theorem B146978651 : Blo 2233435 146978651 := bstep (se 1 (by rfl) ⟨110233988, by rfl⟩ : syracuseStep 146978651 = 220467977) B220467977
theorem B391943069 : Blo 2233435 391943069 := bstep (se 3 (by rfl) ⟨73489325, by rfl⟩ : syracuseStep 391943069 = 146978651) B146978651
theorem B261295379 : Blo 2233435 261295379 := bstep (se 1 (by rfl) ⟨195971534, by rfl⟩ : syracuseStep 261295379 = 391943069) B391943069
theorem B174196919 : Blo 2233435 174196919 := bstep (se 1 (by rfl) ⟨130647689, by rfl⟩ : syracuseStep 174196919 = 261295379) B261295379
theorem B116131279 : Blo 2233435 116131279 := bstep (se 1 (by rfl) ⟨87098459, by rfl⟩ : syracuseStep 116131279 = 174196919) B174196919
theorem B154841705 : Blo 2233435 154841705 := bstep (se 2 (by rfl) ⟨58065639, by rfl⟩ : syracuseStep 154841705 = 116131279) B116131279
theorem B103227803 : Blo 2233435 103227803 := bstep (se 1 (by rfl) ⟨77420852, by rfl⟩ : syracuseStep 103227803 = 154841705) B154841705
theorem B68818535 : Blo 2233435 68818535 := bstep (se 1 (by rfl) ⟨51613901, by rfl⟩ : syracuseStep 68818535 = 103227803) B103227803
theorem B45879023 : Blo 2233435 45879023 := bstep (se 1 (by rfl) ⟨34409267, by rfl⟩ : syracuseStep 45879023 = 68818535) B68818535
theorem B30586015 : Blo 2233435 30586015 := bstep (se 1 (by rfl) ⟨22939511, by rfl⟩ : syracuseStep 30586015 = 45879023) B45879023
theorem B40781353 : Blo 2233435 40781353 := bstep (se 2 (by rfl) ⟨15293007, by rfl⟩ : syracuseStep 40781353 = 30586015) B30586015
theorem B54375137 : Blo 2233435 54375137 := bstep (se 2 (by rfl) ⟨20390676, by rfl⟩ : syracuseStep 54375137 = 40781353) B40781353
theorem B36250091 : Blo 2233435 36250091 := bstep (se 1 (by rfl) ⟨27187568, by rfl⟩ : syracuseStep 36250091 = 54375137) B54375137
theorem B24166727 : Blo 2233435 24166727 := bstep (se 1 (by rfl) ⟨18125045, by rfl⟩ : syracuseStep 24166727 = 36250091) B36250091
theorem B16111151 : Blo 2233435 16111151 := bstep (se 1 (by rfl) ⟨12083363, by rfl⟩ : syracuseStep 16111151 = 24166727) B24166727
theorem B10740767 : Blo 2233435 10740767 := bstep (se 1 (by rfl) ⟨8055575, by rfl⟩ : syracuseStep 10740767 = 16111151) B16111151
theorem B28642045 : Blo 2233435 28642045 := bstep (se 3 (by rfl) ⟨5370383, by rfl⟩ : syracuseStep 28642045 = 10740767) B10740767
theorem B38189393 : Blo 2233435 38189393 := bstep (se 2 (by rfl) ⟨14321022, by rfl⟩ : syracuseStep 38189393 = 28642045) B28642045
theorem B25459595 : Blo 2233435 25459595 := bstep (se 1 (by rfl) ⟨19094696, by rfl⟩ : syracuseStep 25459595 = 38189393) B38189393
theorem B16973063 : Blo 2233435 16973063 := bstep (se 1 (by rfl) ⟨12729797, by rfl⟩ : syracuseStep 16973063 = 25459595) B25459595
theorem B11315375 : Blo 2233435 11315375 := bstep (se 1 (by rfl) ⟨8486531, by rfl⟩ : syracuseStep 11315375 = 16973063) B16973063
theorem B7543583 : Blo 2233435 7543583 := bstep (se 1 (by rfl) ⟨5657687, by rfl⟩ : syracuseStep 7543583 = 11315375) B11315375
theorem B5029055 : Blo 2233435 5029055 := bstep (se 1 (by rfl) ⟨3771791, by rfl⟩ : syracuseStep 5029055 = 7543583) B7543583
theorem B3352703 : Blo 2233435 3352703 := bstep (se 1 (by rfl) ⟨2514527, by rfl⟩ : syracuseStep 3352703 = 5029055) B5029055
theorem B2235135 : Blo 2233435 2235135 := bstep (se 1 (by rfl) ⟨1676351, by rfl⟩ : syracuseStep 2235135 = 3352703) B3352703
theorem B3352709 : Blo 2233435 3352709 := bbase (se 4 (by rfl) ⟨314316, by rfl⟩ : syracuseStep 3352709 = 628633) (by norm_num)
theorem B2235139 : Blo 2233435 2235139 := bstep (se 1 (by rfl) ⟨1676354, by rfl⟩ : syracuseStep 2235139 = 3352709) B3352709
theorem B3771805 : Blo 2233435 3771805 := bbase (se 3 (by rfl) ⟨707213, by rfl⟩ : syracuseStep 3771805 = 1414427) (by norm_num)
theorem B5029073 : Blo 2233435 5029073 := bstep (se 2 (by rfl) ⟨1885902, by rfl⟩ : syracuseStep 5029073 = 3771805) B3771805
theorem B3352715 : Blo 2233435 3352715 := bstep (se 1 (by rfl) ⟨2514536, by rfl⟩ : syracuseStep 3352715 = 5029073) B5029073
theorem B2235143 : Blo 2233435 2235143 := bstep (se 1 (by rfl) ⟨1676357, by rfl⟩ : syracuseStep 2235143 = 3352715) B3352715
theorem B2514541 : Blo 2233435 2514541 := bbase (se 3 (by rfl) ⟨471476, by rfl⟩ : syracuseStep 2514541 = 942953) (by norm_num)
theorem B3352721 : Blo 2233435 3352721 := bstep (se 2 (by rfl) ⟨1257270, by rfl⟩ : syracuseStep 3352721 = 2514541) B2514541
theorem B2235147 : Blo 2233435 2235147 := bstep (se 1 (by rfl) ⟨1676360, by rfl⟩ : syracuseStep 2235147 = 3352721) B3352721
theorem B7543637 : Blo 2233435 7543637 := bbase (se 9 (by rfl) ⟨22100, by rfl⟩ : syracuseStep 7543637 = 44201) (by norm_num)
theorem B5029091 : Blo 2233435 5029091 := bstep (se 1 (by rfl) ⟨3771818, by rfl⟩ : syracuseStep 5029091 = 7543637) B7543637
theorem B3352727 : Blo 2233435 3352727 := bstep (se 1 (by rfl) ⟨2514545, by rfl⟩ : syracuseStep 3352727 = 5029091) B5029091
theorem B2235151 : Blo 2233435 2235151 := bstep (se 1 (by rfl) ⟨1676363, by rfl⟩ : syracuseStep 2235151 = 3352727) B3352727
theorem B3352733 : Blo 2233435 3352733 := bbase (se 3 (by rfl) ⟨628637, by rfl⟩ : syracuseStep 3352733 = 1257275) (by norm_num)
theorem B2235155 : Blo 2233435 2235155 := bstep (se 1 (by rfl) ⟨1676366, by rfl⟩ : syracuseStep 2235155 = 3352733) B3352733
theorem B5029109 : Blo 2233435 5029109 := bbase (se 5 (by rfl) ⟨235739, by rfl⟩ : syracuseStep 5029109 = 471479) (by norm_num)
theorem B3352739 : Blo 2233435 3352739 := bstep (se 1 (by rfl) ⟨2514554, by rfl⟩ : syracuseStep 3352739 = 5029109) B5029109
theorem B2235159 : Blo 2233435 2235159 := bstep (se 1 (by rfl) ⟨1676369, by rfl⟩ : syracuseStep 2235159 = 3352739) B3352739
theorem B4301213 : Blo 2233435 4301213 := bbase (se 3 (by rfl) ⟨806477, by rfl⟩ : syracuseStep 4301213 = 1612955) (by norm_num)
theorem B45879605 : Blo 2233435 45879605 := bstep (se 5 (by rfl) ⟨2150606, by rfl⟩ : syracuseStep 45879605 = 4301213) B4301213
theorem B30586403 : Blo 2233435 30586403 := bstep (se 1 (by rfl) ⟨22939802, by rfl⟩ : syracuseStep 30586403 = 45879605) B45879605
theorem B20390935 : Blo 2233435 20390935 := bstep (se 1 (by rfl) ⟨15293201, by rfl⟩ : syracuseStep 20390935 = 30586403) B30586403
theorem B27187913 : Blo 2233435 27187913 := bstep (se 2 (by rfl) ⟨10195467, by rfl⟩ : syracuseStep 27187913 = 20390935) B20390935
theorem B72501101 : Blo 2233435 72501101 := bstep (se 3 (by rfl) ⟨13593956, by rfl⟩ : syracuseStep 72501101 = 27187913) B27187913
theorem B48334067 : Blo 2233435 48334067 := bstep (se 1 (by rfl) ⟨36250550, by rfl⟩ : syracuseStep 48334067 = 72501101) B72501101
theorem B32222711 : Blo 2233435 32222711 := bstep (se 1 (by rfl) ⟨24167033, by rfl⟩ : syracuseStep 32222711 = 48334067) B48334067
theorem B21481807 : Blo 2233435 21481807 := bstep (se 1 (by rfl) ⟨16111355, by rfl⟩ : syracuseStep 21481807 = 32222711) B32222711
theorem B28642409 : Blo 2233435 28642409 := bstep (se 2 (by rfl) ⟨10740903, by rfl⟩ : syracuseStep 28642409 = 21481807) B21481807
theorem B19094939 : Blo 2233435 19094939 := bstep (se 1 (by rfl) ⟨14321204, by rfl⟩ : syracuseStep 19094939 = 28642409) B28642409
theorem B12729959 : Blo 2233435 12729959 := bstep (se 1 (by rfl) ⟨9547469, by rfl⟩ : syracuseStep 12729959 = 19094939) B19094939
theorem B8486639 : Blo 2233435 8486639 := bstep (se 1 (by rfl) ⟨6364979, by rfl⟩ : syracuseStep 8486639 = 12729959) B12729959
theorem B5657759 : Blo 2233435 5657759 := bstep (se 1 (by rfl) ⟨4243319, by rfl⟩ : syracuseStep 5657759 = 8486639) B8486639
theorem B3771839 : Blo 2233435 3771839 := bstep (se 1 (by rfl) ⟨2828879, by rfl⟩ : syracuseStep 3771839 = 5657759) B5657759
theorem B2514559 : Blo 2233435 2514559 := bstep (se 1 (by rfl) ⟨1885919, by rfl⟩ : syracuseStep 2514559 = 3771839) B3771839
theorem B3352745 : Blo 2233435 3352745 := bstep (se 2 (by rfl) ⟨1257279, by rfl⟩ : syracuseStep 3352745 = 2514559) B2514559
theorem B2235163 : Blo 2233435 2235163 := bstep (se 1 (by rfl) ⟨1676372, by rfl⟩ : syracuseStep 2235163 = 3352745) B3352745
theorem B5237797 : Blo 2233435 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B6983729 : Blo 2233435 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B4655819 : Blo 2233435 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B3103879 : Blo 2233435 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B4138505 : Blo 2233435 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B2759003 : Blo 2233435 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B29429365 : Blo 2233435 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B39239153 : Blo 2233435 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B26159435 : Blo 2233435 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B17439623 : Blo 2233435 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B11626415 : Blo 2233435 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B7750943 : Blo 2233435 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B5167295 : Blo 2233435 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B3444863 : Blo 2233435 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B9186301 : Blo 2233435 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B12248401 : Blo 2233435 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B16331201 : Blo 2233435 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B10887467 : Blo 2233435 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B29033245 : Blo 2233435 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B38710993 : Blo 2233435 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B51614657 : Blo 2233435 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B34409771 : Blo 2233435 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B22939847 : Blo 2233435 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B15293231 : Blo 2233435 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B10195487 : Blo 2233435 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B6796991 : Blo 2233435 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B18125309 : Blo 2233435 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B12083539 : Blo 2233435 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B16111385 : Blo 2233435 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B10740923 : Blo 2233435 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B7160615 : Blo 2233435 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B4773743 : Blo 2233435 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B3182495 : Blo 2233435 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B8486653 : Blo 2233435 8486653 := bstep (se 3 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 8486653 = 3182495) B3182495
theorem B11315537 : Blo 2233435 11315537 := bstep (se 2 (by rfl) ⟨4243326, by rfl⟩ : syracuseStep 11315537 = 8486653) B8486653
theorem B7543691 : Blo 2233435 7543691 := bstep (se 1 (by rfl) ⟨5657768, by rfl⟩ : syracuseStep 7543691 = 11315537) B11315537
theorem B5029127 : Blo 2233435 5029127 := bstep (se 1 (by rfl) ⟨3771845, by rfl⟩ : syracuseStep 5029127 = 7543691) B7543691
theorem B3352751 : Blo 2233435 3352751 := bstep (se 1 (by rfl) ⟨2514563, by rfl⟩ : syracuseStep 3352751 = 5029127) B5029127
theorem B2235167 : Blo 2233435 2235167 := bstep (se 1 (by rfl) ⟨1676375, by rfl⟩ : syracuseStep 2235167 = 3352751) B3352751
theorem B3352757 : Blo 2233435 3352757 := bbase (se 5 (by rfl) ⟨157160, by rfl⟩ : syracuseStep 3352757 = 314321) (by norm_num)
theorem B2235171 : Blo 2233435 2235171 := bstep (se 1 (by rfl) ⟨1676378, by rfl⟩ : syracuseStep 2235171 = 3352757) B3352757
theorem B5657789 : Blo 2233435 5657789 := bbase (se 3 (by rfl) ⟨1060835, by rfl⟩ : syracuseStep 5657789 = 2121671) (by norm_num)
theorem B3771859 : Blo 2233435 3771859 := bstep (se 1 (by rfl) ⟨2828894, by rfl⟩ : syracuseStep 3771859 = 5657789) B5657789
theorem B5029145 : Blo 2233435 5029145 := bstep (se 2 (by rfl) ⟨1885929, by rfl⟩ : syracuseStep 5029145 = 3771859) B3771859
theorem B3352763 : Blo 2233435 3352763 := bstep (se 1 (by rfl) ⟨2514572, by rfl⟩ : syracuseStep 3352763 = 5029145) B5029145
theorem B2235175 : Blo 2233435 2235175 := bstep (se 1 (by rfl) ⟨1676381, by rfl⟩ : syracuseStep 2235175 = 3352763) B3352763
theorem B2514577 : Blo 2233435 2514577 := bbase (se 2 (by rfl) ⟨942966, by rfl⟩ : syracuseStep 2514577 = 1885933) (by norm_num)
theorem B3352769 : Blo 2233435 3352769 := bstep (se 2 (by rfl) ⟨1257288, by rfl⟩ : syracuseStep 3352769 = 2514577) B2514577
theorem B2235179 : Blo 2233435 2235179 := bstep (se 1 (by rfl) ⟨1676384, by rfl⟩ : syracuseStep 2235179 = 3352769) B3352769
theorem B4243357 : Blo 2233435 4243357 := bbase (se 3 (by rfl) ⟨795629, by rfl⟩ : syracuseStep 4243357 = 1591259) (by norm_num)
theorem B5657809 : Blo 2233435 5657809 := bstep (se 2 (by rfl) ⟨2121678, by rfl⟩ : syracuseStep 5657809 = 4243357) B4243357
theorem B7543745 : Blo 2233435 7543745 := bstep (se 2 (by rfl) ⟨2828904, by rfl⟩ : syracuseStep 7543745 = 5657809) B5657809
theorem B5029163 : Blo 2233435 5029163 := bstep (se 1 (by rfl) ⟨3771872, by rfl⟩ : syracuseStep 5029163 = 7543745) B7543745
theorem B3352775 : Blo 2233435 3352775 := bstep (se 1 (by rfl) ⟨2514581, by rfl⟩ : syracuseStep 3352775 = 5029163) B5029163
theorem B2235183 : Blo 2233435 2235183 := bstep (se 1 (by rfl) ⟨1676387, by rfl⟩ : syracuseStep 2235183 = 3352775) B3352775
theorem B3352781 : Blo 2233435 3352781 := bbase (se 3 (by rfl) ⟨628646, by rfl⟩ : syracuseStep 3352781 = 1257293) (by norm_num)
theorem B2235187 : Blo 2233435 2235187 := bstep (se 1 (by rfl) ⟨1676390, by rfl⟩ : syracuseStep 2235187 = 3352781) B3352781
theorem B5029181 : Blo 2233435 5029181 := bbase (se 3 (by rfl) ⟨942971, by rfl⟩ : syracuseStep 5029181 = 1885943) (by norm_num)
theorem B3352787 : Blo 2233435 3352787 := bstep (se 1 (by rfl) ⟨2514590, by rfl⟩ : syracuseStep 3352787 = 5029181) B5029181
theorem B2235191 : Blo 2233435 2235191 := bstep (se 1 (by rfl) ⟨1676393, by rfl⟩ : syracuseStep 2235191 = 3352787) B3352787
theorem B3771893 : Blo 2233435 3771893 := bbase (se 5 (by rfl) ⟨176807, by rfl⟩ : syracuseStep 3771893 = 353615) (by norm_num)
theorem B2514595 : Blo 2233435 2514595 := bstep (se 1 (by rfl) ⟨1885946, by rfl⟩ : syracuseStep 2514595 = 3771893) B3771893
theorem B3352793 : Blo 2233435 3352793 := bstep (se 2 (by rfl) ⟨1257297, by rfl⟩ : syracuseStep 3352793 = 2514595) B2514595
theorem B2235195 : Blo 2233435 2235195 := bstep (se 1 (by rfl) ⟨1676396, by rfl⟩ : syracuseStep 2235195 = 3352793) B3352793
theorem B2685269 : Blo 2233435 2685269 := bbase (se 10 (by rfl) ⟨3933, by rfl⟩ : syracuseStep 2685269 = 7867) (by norm_num)
theorem B7160717 : Blo 2233435 7160717 := bstep (se 3 (by rfl) ⟨1342634, by rfl⟩ : syracuseStep 7160717 = 2685269) B2685269
theorem B4773811 : Blo 2233435 4773811 := bstep (se 1 (by rfl) ⟨3580358, by rfl⟩ : syracuseStep 4773811 = 7160717) B7160717
theorem B6365081 : Blo 2233435 6365081 := bstep (se 2 (by rfl) ⟨2386905, by rfl⟩ : syracuseStep 6365081 = 4773811) B4773811
theorem B16973549 : Blo 2233435 16973549 := bstep (se 3 (by rfl) ⟨3182540, by rfl⟩ : syracuseStep 16973549 = 6365081) B6365081
theorem B11315699 : Blo 2233435 11315699 := bstep (se 1 (by rfl) ⟨8486774, by rfl⟩ : syracuseStep 11315699 = 16973549) B16973549
theorem B7543799 : Blo 2233435 7543799 := bstep (se 1 (by rfl) ⟨5657849, by rfl⟩ : syracuseStep 7543799 = 11315699) B11315699
theorem B5029199 : Blo 2233435 5029199 := bstep (se 1 (by rfl) ⟨3771899, by rfl⟩ : syracuseStep 5029199 = 7543799) B7543799
theorem B3352799 : Blo 2233435 3352799 := bstep (se 1 (by rfl) ⟨2514599, by rfl⟩ : syracuseStep 3352799 = 5029199) B5029199
theorem B2235199 : Blo 2233435 2235199 := bstep (se 1 (by rfl) ⟨1676399, by rfl⟩ : syracuseStep 2235199 = 3352799) B3352799
theorem B3352805 : Blo 2233435 3352805 := bbase (se 4 (by rfl) ⟨314325, by rfl⟩ : syracuseStep 3352805 = 628651) (by norm_num)
theorem B2235203 : Blo 2233435 2235203 := bstep (se 1 (by rfl) ⟨1676402, by rfl⟩ : syracuseStep 2235203 = 3352805) B3352805
theorem B4773829 : Blo 2233435 4773829 := bbase (se 4 (by rfl) ⟨447546, by rfl⟩ : syracuseStep 4773829 = 895093) (by norm_num)
theorem B6365105 : Blo 2233435 6365105 := bstep (se 2 (by rfl) ⟨2386914, by rfl⟩ : syracuseStep 6365105 = 4773829) B4773829
theorem B4243403 : Blo 2233435 4243403 := bstep (se 1 (by rfl) ⟨3182552, by rfl⟩ : syracuseStep 4243403 = 6365105) B6365105
theorem B2828935 : Blo 2233435 2828935 := bstep (se 1 (by rfl) ⟨2121701, by rfl⟩ : syracuseStep 2828935 = 4243403) B4243403
theorem B3771913 : Blo 2233435 3771913 := bstep (se 2 (by rfl) ⟨1414467, by rfl⟩ : syracuseStep 3771913 = 2828935) B2828935
theorem B5029217 : Blo 2233435 5029217 := bstep (se 2 (by rfl) ⟨1885956, by rfl⟩ : syracuseStep 5029217 = 3771913) B3771913
theorem B3352811 : Blo 2233435 3352811 := bstep (se 1 (by rfl) ⟨2514608, by rfl⟩ : syracuseStep 3352811 = 5029217) B5029217
theorem B2235207 : Blo 2233435 2235207 := bstep (se 1 (by rfl) ⟨1676405, by rfl⟩ : syracuseStep 2235207 = 3352811) B3352811
theorem B2514613 : Blo 2233435 2514613 := bbase (se 5 (by rfl) ⟨117872, by rfl⟩ : syracuseStep 2514613 = 235745) (by norm_num)
theorem B3352817 : Blo 2233435 3352817 := bstep (se 2 (by rfl) ⟨1257306, by rfl⟩ : syracuseStep 3352817 = 2514613) B2514613
theorem B2235211 : Blo 2233435 2235211 := bstep (se 1 (by rfl) ⟨1676408, by rfl⟩ : syracuseStep 2235211 = 3352817) B3352817
theorem B2828945 : Blo 2233435 2828945 := bbase (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) (by norm_num)
theorem B7543853 : Blo 2233435 7543853 := bstep (se 3 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 7543853 = 2828945) B2828945
theorem B5029235 : Blo 2233435 5029235 := bstep (se 1 (by rfl) ⟨3771926, by rfl⟩ : syracuseStep 5029235 = 7543853) B7543853
theorem B3352823 : Blo 2233435 3352823 := bstep (se 1 (by rfl) ⟨2514617, by rfl⟩ : syracuseStep 3352823 = 5029235) B5029235
theorem B2235215 : Blo 2233435 2235215 := bstep (se 1 (by rfl) ⟨1676411, by rfl⟩ : syracuseStep 2235215 = 3352823) B3352823
theorem B3352829 : Blo 2233435 3352829 := bbase (se 3 (by rfl) ⟨628655, by rfl⟩ : syracuseStep 3352829 = 1257311) (by norm_num)
theorem B2235219 : Blo 2233435 2235219 := bstep (se 1 (by rfl) ⟨1676414, by rfl⟩ : syracuseStep 2235219 = 3352829) B3352829
theorem B5029253 : Blo 2233435 5029253 := bbase (se 4 (by rfl) ⟨471492, by rfl⟩ : syracuseStep 5029253 = 942985) (by norm_num)
theorem B3352835 : Blo 2233435 3352835 := bstep (se 1 (by rfl) ⟨2514626, by rfl⟩ : syracuseStep 3352835 = 5029253) B5029253
theorem B2235223 : Blo 2233435 2235223 := bstep (se 1 (by rfl) ⟨1676417, by rfl⟩ : syracuseStep 2235223 = 3352835) B3352835
theorem B3182581 : Blo 2233435 3182581 := bbase (se 5 (by rfl) ⟨149183, by rfl⟩ : syracuseStep 3182581 = 298367) (by norm_num)
theorem B4243441 : Blo 2233435 4243441 := bstep (se 2 (by rfl) ⟨1591290, by rfl⟩ : syracuseStep 4243441 = 3182581) B3182581
theorem B5657921 : Blo 2233435 5657921 := bstep (se 2 (by rfl) ⟨2121720, by rfl⟩ : syracuseStep 5657921 = 4243441) B4243441
theorem B3771947 : Blo 2233435 3771947 := bstep (se 1 (by rfl) ⟨2828960, by rfl⟩ : syracuseStep 3771947 = 5657921) B5657921
theorem B2514631 : Blo 2233435 2514631 := bstep (se 1 (by rfl) ⟨1885973, by rfl⟩ : syracuseStep 2514631 = 3771947) B3771947
theorem B3352841 : Blo 2233435 3352841 := bstep (se 2 (by rfl) ⟨1257315, by rfl⟩ : syracuseStep 3352841 = 2514631) B2514631
theorem B2235227 : Blo 2233435 2235227 := bstep (se 1 (by rfl) ⟨1676420, by rfl⟩ : syracuseStep 2235227 = 3352841) B3352841
theorem B11315861 : Blo 2233435 11315861 := bbase (se 6 (by rfl) ⟨265215, by rfl⟩ : syracuseStep 11315861 = 530431) (by norm_num)
theorem B7543907 : Blo 2233435 7543907 := bstep (se 1 (by rfl) ⟨5657930, by rfl⟩ : syracuseStep 7543907 = 11315861) B11315861
theorem B5029271 : Blo 2233435 5029271 := bstep (se 1 (by rfl) ⟨3771953, by rfl⟩ : syracuseStep 5029271 = 7543907) B7543907
theorem B3352847 : Blo 2233435 3352847 := bstep (se 1 (by rfl) ⟨2514635, by rfl⟩ : syracuseStep 3352847 = 5029271) B5029271
theorem B2235231 : Blo 2233435 2235231 := bstep (se 1 (by rfl) ⟨1676423, by rfl⟩ : syracuseStep 2235231 = 3352847) B3352847
theorem B3352853 : Blo 2233435 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B2235235 : Blo 2233435 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B2685317 : Blo 2233435 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B28643381 : Blo 2233435 28643381 := bstep (se 5 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 28643381 = 2685317) B2685317
theorem B19095587 : Blo 2233435 19095587 := bstep (se 1 (by rfl) ⟨14321690, by rfl⟩ : syracuseStep 19095587 = 28643381) B28643381
theorem B12730391 : Blo 2233435 12730391 := bstep (se 1 (by rfl) ⟨9547793, by rfl⟩ : syracuseStep 12730391 = 19095587) B19095587
theorem B8486927 : Blo 2233435 8486927 := bstep (se 1 (by rfl) ⟨6365195, by rfl⟩ : syracuseStep 8486927 = 12730391) B12730391
theorem B5657951 : Blo 2233435 5657951 := bstep (se 1 (by rfl) ⟨4243463, by rfl⟩ : syracuseStep 5657951 = 8486927) B8486927
theorem B3771967 : Blo 2233435 3771967 := bstep (se 1 (by rfl) ⟨2828975, by rfl⟩ : syracuseStep 3771967 = 5657951) B5657951
theorem B5029289 : Blo 2233435 5029289 := bstep (se 2 (by rfl) ⟨1885983, by rfl⟩ : syracuseStep 5029289 = 3771967) B3771967
theorem B3352859 : Blo 2233435 3352859 := bstep (se 1 (by rfl) ⟨2514644, by rfl⟩ : syracuseStep 3352859 = 5029289) B5029289
theorem B2235239 : Blo 2233435 2235239 := bstep (se 1 (by rfl) ⟨1676429, by rfl⟩ : syracuseStep 2235239 = 3352859) B3352859
theorem B2514649 : Blo 2233435 2514649 := bbase (se 2 (by rfl) ⟨942993, by rfl⟩ : syracuseStep 2514649 = 1885987) (by norm_num)
theorem B3352865 : Blo 2233435 3352865 := bstep (se 2 (by rfl) ⟨1257324, by rfl⟩ : syracuseStep 3352865 = 2514649) B2514649
theorem B2235243 : Blo 2233435 2235243 := bstep (se 1 (by rfl) ⟨1676432, by rfl⟩ : syracuseStep 2235243 = 3352865) B3352865
theorem B2386957 : Blo 2233435 2386957 := bbase (se 3 (by rfl) ⟨447554, by rfl⟩ : syracuseStep 2386957 = 895109) (by norm_num)
theorem B3182609 : Blo 2233435 3182609 := bstep (se 2 (by rfl) ⟨1193478, by rfl⟩ : syracuseStep 3182609 = 2386957) B2386957
theorem B8486957 : Blo 2233435 8486957 := bstep (se 3 (by rfl) ⟨1591304, by rfl⟩ : syracuseStep 8486957 = 3182609) B3182609
theorem B5657971 : Blo 2233435 5657971 := bstep (se 1 (by rfl) ⟨4243478, by rfl⟩ : syracuseStep 5657971 = 8486957) B8486957
theorem B7543961 : Blo 2233435 7543961 := bstep (se 2 (by rfl) ⟨2828985, by rfl⟩ : syracuseStep 7543961 = 5657971) B5657971
theorem B5029307 : Blo 2233435 5029307 := bstep (se 1 (by rfl) ⟨3771980, by rfl⟩ : syracuseStep 5029307 = 7543961) B7543961
theorem B3352871 : Blo 2233435 3352871 := bstep (se 1 (by rfl) ⟨2514653, by rfl⟩ : syracuseStep 3352871 = 5029307) B5029307
theorem B2235247 : Blo 2233435 2235247 := bstep (se 1 (by rfl) ⟨1676435, by rfl⟩ : syracuseStep 2235247 = 3352871) B3352871
theorem B3352877 : Blo 2233435 3352877 := bbase (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) (by norm_num)
theorem B2235251 : Blo 2233435 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B5029325 : Blo 2233435 5029325 := bbase (se 3 (by rfl) ⟨942998, by rfl⟩ : syracuseStep 5029325 = 1885997) (by norm_num)
theorem B3352883 : Blo 2233435 3352883 := bstep (se 1 (by rfl) ⟨2514662, by rfl⟩ : syracuseStep 3352883 = 5029325) B5029325
theorem B2235255 : Blo 2233435 2235255 := bstep (se 1 (by rfl) ⟨1676441, by rfl⟩ : syracuseStep 2235255 = 3352883) B3352883
theorem B2829001 : Blo 2233435 2829001 := bbase (se 2 (by rfl) ⟨1060875, by rfl⟩ : syracuseStep 2829001 = 2121751) (by norm_num)
theorem B3772001 : Blo 2233435 3772001 := bstep (se 2 (by rfl) ⟨1414500, by rfl⟩ : syracuseStep 3772001 = 2829001) B2829001
theorem B2514667 : Blo 2233435 2514667 := bstep (se 1 (by rfl) ⟨1886000, by rfl⟩ : syracuseStep 2514667 = 3772001) B3772001
theorem B3352889 : Blo 2233435 3352889 := bstep (se 2 (by rfl) ⟨1257333, by rfl⟩ : syracuseStep 3352889 = 2514667) B2514667
theorem B2235259 : Blo 2233435 2235259 := bstep (se 1 (by rfl) ⟨1676444, by rfl⟩ : syracuseStep 2235259 = 3352889) B3352889
theorem B8056037 : Blo 2233435 8056037 := bbase (se 4 (by rfl) ⟨755253, by rfl⟩ : syracuseStep 8056037 = 1510507) (by norm_num)
theorem B21482765 : Blo 2233435 21482765 := bstep (se 3 (by rfl) ⟨4028018, by rfl⟩ : syracuseStep 21482765 = 8056037) B8056037
theorem B14321843 : Blo 2233435 14321843 := bstep (se 1 (by rfl) ⟨10741382, by rfl⟩ : syracuseStep 14321843 = 21482765) B21482765
theorem B9547895 : Blo 2233435 9547895 := bstep (se 1 (by rfl) ⟨7160921, by rfl⟩ : syracuseStep 9547895 = 14321843) B14321843
theorem B25461053 : Blo 2233435 25461053 := bstep (se 3 (by rfl) ⟨4773947, by rfl⟩ : syracuseStep 25461053 = 9547895) B9547895
theorem B16974035 : Blo 2233435 16974035 := bstep (se 1 (by rfl) ⟨12730526, by rfl⟩ : syracuseStep 16974035 = 25461053) B25461053
theorem B11316023 : Blo 2233435 11316023 := bstep (se 1 (by rfl) ⟨8487017, by rfl⟩ : syracuseStep 11316023 = 16974035) B16974035
theorem B7544015 : Blo 2233435 7544015 := bstep (se 1 (by rfl) ⟨5658011, by rfl⟩ : syracuseStep 7544015 = 11316023) B11316023
theorem B5029343 : Blo 2233435 5029343 := bstep (se 1 (by rfl) ⟨3772007, by rfl⟩ : syracuseStep 5029343 = 7544015) B7544015
theorem B3352895 : Blo 2233435 3352895 := bstep (se 1 (by rfl) ⟨2514671, by rfl⟩ : syracuseStep 3352895 = 5029343) B5029343
theorem B2235263 : Blo 2233435 2235263 := bstep (se 1 (by rfl) ⟨1676447, by rfl⟩ : syracuseStep 2235263 = 3352895) B3352895
theorem B3352901 : Blo 2233435 3352901 := bbase (se 4 (by rfl) ⟨314334, by rfl⟩ : syracuseStep 3352901 = 628669) (by norm_num)
theorem B2235267 : Blo 2233435 2235267 := bstep (se 1 (by rfl) ⟨1676450, by rfl⟩ : syracuseStep 2235267 = 3352901) B3352901
theorem B3772021 : Blo 2233435 3772021 := bbase (se 5 (by rfl) ⟨176813, by rfl⟩ : syracuseStep 3772021 = 353627) (by norm_num)
theorem B5029361 : Blo 2233435 5029361 := bstep (se 2 (by rfl) ⟨1886010, by rfl⟩ : syracuseStep 5029361 = 3772021) B3772021
theorem B3352907 : Blo 2233435 3352907 := bstep (se 1 (by rfl) ⟨2514680, by rfl⟩ : syracuseStep 3352907 = 5029361) B5029361
theorem B2235271 : Blo 2233435 2235271 := bstep (se 1 (by rfl) ⟨1676453, by rfl⟩ : syracuseStep 2235271 = 3352907) B3352907
theorem B2514685 : Blo 2233435 2514685 := bbase (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) (by norm_num)
theorem B3352913 : Blo 2233435 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B2235275 : Blo 2233435 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B7544069 : Blo 2233435 7544069 := bbase (se 4 (by rfl) ⟨707256, by rfl⟩ : syracuseStep 7544069 = 1414513) (by norm_num)
theorem B5029379 : Blo 2233435 5029379 := bstep (se 1 (by rfl) ⟨3772034, by rfl⟩ : syracuseStep 5029379 = 7544069) B7544069
theorem B3352919 : Blo 2233435 3352919 := bstep (se 1 (by rfl) ⟨2514689, by rfl⟩ : syracuseStep 3352919 = 5029379) B5029379
theorem B2235279 : Blo 2233435 2235279 := bstep (se 1 (by rfl) ⟨1676459, by rfl⟩ : syracuseStep 2235279 = 3352919) B3352919
theorem B3352925 : Blo 2233435 3352925 := bbase (se 3 (by rfl) ⟨628673, by rfl⟩ : syracuseStep 3352925 = 1257347) (by norm_num)
theorem B2235283 : Blo 2233435 2235283 := bstep (se 1 (by rfl) ⟨1676462, by rfl⟩ : syracuseStep 2235283 = 3352925) B3352925
theorem B5029397 : Blo 2233435 5029397 := bbase (se 6 (by rfl) ⟨117876, by rfl⟩ : syracuseStep 5029397 = 235753) (by norm_num)
theorem B3352931 : Blo 2233435 3352931 := bstep (se 1 (by rfl) ⟨2514698, by rfl⟩ : syracuseStep 3352931 = 5029397) B5029397
theorem B2235287 : Blo 2233435 2235287 := bstep (se 1 (by rfl) ⟨1676465, by rfl⟩ : syracuseStep 2235287 = 3352931) B3352931
theorem B8487125 : Blo 2233435 8487125 := bbase (se 7 (by rfl) ⟨99458, by rfl⟩ : syracuseStep 8487125 = 198917) (by norm_num)
theorem B5658083 : Blo 2233435 5658083 := bstep (se 1 (by rfl) ⟨4243562, by rfl⟩ : syracuseStep 5658083 = 8487125) B8487125
theorem B3772055 : Blo 2233435 3772055 := bstep (se 1 (by rfl) ⟨2829041, by rfl⟩ : syracuseStep 3772055 = 5658083) B5658083
theorem B2514703 : Blo 2233435 2514703 := bstep (se 1 (by rfl) ⟨1886027, by rfl⟩ : syracuseStep 2514703 = 3772055) B3772055
theorem B3352937 : Blo 2233435 3352937 := bstep (se 2 (by rfl) ⟨1257351, by rfl⟩ : syracuseStep 3352937 = 2514703) B2514703
theorem B2235291 : Blo 2233435 2235291 := bstep (se 1 (by rfl) ⟨1676468, by rfl⟩ : syracuseStep 2235291 = 3352937) B3352937
theorem B12730709 : Blo 2233435 12730709 := bbase (se 10 (by rfl) ⟨18648, by rfl⟩ : syracuseStep 12730709 = 37297) (by norm_num)
theorem B8487139 : Blo 2233435 8487139 := bstep (se 1 (by rfl) ⟨6365354, by rfl⟩ : syracuseStep 8487139 = 12730709) B12730709
theorem B11316185 : Blo 2233435 11316185 := bstep (se 2 (by rfl) ⟨4243569, by rfl⟩ : syracuseStep 11316185 = 8487139) B8487139
theorem B7544123 : Blo 2233435 7544123 := bstep (se 1 (by rfl) ⟨5658092, by rfl⟩ : syracuseStep 7544123 = 11316185) B11316185
theorem B5029415 : Blo 2233435 5029415 := bstep (se 1 (by rfl) ⟨3772061, by rfl⟩ : syracuseStep 5029415 = 7544123) B7544123
theorem B3352943 : Blo 2233435 3352943 := bstep (se 1 (by rfl) ⟨2514707, by rfl⟩ : syracuseStep 3352943 = 5029415) B5029415
theorem B2235295 : Blo 2233435 2235295 := bstep (se 1 (by rfl) ⟨1676471, by rfl⟩ : syracuseStep 2235295 = 3352943) B3352943
theorem B3352949 : Blo 2233435 3352949 := bbase (se 5 (by rfl) ⟨157169, by rfl⟩ : syracuseStep 3352949 = 314339) (by norm_num)
theorem B2235299 : Blo 2233435 2235299 := bstep (se 1 (by rfl) ⟨1676474, by rfl⟩ : syracuseStep 2235299 = 3352949) B3352949
theorem B2387017 : Blo 2233435 2387017 := bbase (se 2 (by rfl) ⟨895131, by rfl⟩ : syracuseStep 2387017 = 1790263) (by norm_num)
theorem B3182689 : Blo 2233435 3182689 := bstep (se 2 (by rfl) ⟨1193508, by rfl⟩ : syracuseStep 3182689 = 2387017) B2387017
theorem B4243585 : Blo 2233435 4243585 := bstep (se 2 (by rfl) ⟨1591344, by rfl⟩ : syracuseStep 4243585 = 3182689) B3182689
theorem B5658113 : Blo 2233435 5658113 := bstep (se 2 (by rfl) ⟨2121792, by rfl⟩ : syracuseStep 5658113 = 4243585) B4243585
theorem B3772075 : Blo 2233435 3772075 := bstep (se 1 (by rfl) ⟨2829056, by rfl⟩ : syracuseStep 3772075 = 5658113) B5658113
theorem B5029433 : Blo 2233435 5029433 := bstep (se 2 (by rfl) ⟨1886037, by rfl⟩ : syracuseStep 5029433 = 3772075) B3772075
theorem B3352955 : Blo 2233435 3352955 := bstep (se 1 (by rfl) ⟨2514716, by rfl⟩ : syracuseStep 3352955 = 5029433) B5029433
theorem B2235303 : Blo 2233435 2235303 := bstep (se 1 (by rfl) ⟨1676477, by rfl⟩ : syracuseStep 2235303 = 3352955) B3352955
theorem B2514721 : Blo 2233435 2514721 := bbase (se 2 (by rfl) ⟨943020, by rfl⟩ : syracuseStep 2514721 = 1886041) (by norm_num)
theorem B3352961 : Blo 2233435 3352961 := bstep (se 2 (by rfl) ⟨1257360, by rfl⟩ : syracuseStep 3352961 = 2514721) B2514721
theorem B2235307 : Blo 2233435 2235307 := bstep (se 1 (by rfl) ⟨1676480, by rfl⟩ : syracuseStep 2235307 = 3352961) B3352961
theorem B5658133 : Blo 2233435 5658133 := bbase (se 6 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 5658133 = 265225) (by norm_num)
theorem B7544177 : Blo 2233435 7544177 := bstep (se 2 (by rfl) ⟨2829066, by rfl⟩ : syracuseStep 7544177 = 5658133) B5658133
theorem B5029451 : Blo 2233435 5029451 := bstep (se 1 (by rfl) ⟨3772088, by rfl⟩ : syracuseStep 5029451 = 7544177) B7544177
theorem B3352967 : Blo 2233435 3352967 := bstep (se 1 (by rfl) ⟨2514725, by rfl⟩ : syracuseStep 3352967 = 5029451) B5029451
theorem B2235311 : Blo 2233435 2235311 := bstep (se 1 (by rfl) ⟨1676483, by rfl⟩ : syracuseStep 2235311 = 3352967) B3352967
theorem B3352973 : Blo 2233435 3352973 := bbase (se 3 (by rfl) ⟨628682, by rfl⟩ : syracuseStep 3352973 = 1257365) (by norm_num)
theorem B2235315 : Blo 2233435 2235315 := bstep (se 1 (by rfl) ⟨1676486, by rfl⟩ : syracuseStep 2235315 = 3352973) B3352973
theorem B5029469 : Blo 2233435 5029469 := bbase (se 3 (by rfl) ⟨943025, by rfl⟩ : syracuseStep 5029469 = 1886051) (by norm_num)
theorem B3352979 : Blo 2233435 3352979 := bstep (se 1 (by rfl) ⟨2514734, by rfl⟩ : syracuseStep 3352979 = 5029469) B5029469
theorem B2235319 : Blo 2233435 2235319 := bstep (se 1 (by rfl) ⟨1676489, by rfl⟩ : syracuseStep 2235319 = 3352979) B3352979
theorem B3772109 : Blo 2233435 3772109 := bbase (se 3 (by rfl) ⟨707270, by rfl⟩ : syracuseStep 3772109 = 1414541) (by norm_num)
theorem B2514739 : Blo 2233435 2514739 := bstep (se 1 (by rfl) ⟨1886054, by rfl⟩ : syracuseStep 2514739 = 3772109) B3772109
theorem B3352985 : Blo 2233435 3352985 := bstep (se 2 (by rfl) ⟨1257369, by rfl⟩ : syracuseStep 3352985 = 2514739) B2514739
theorem B2235323 : Blo 2233435 2235323 := bstep (se 1 (by rfl) ⟨1676492, by rfl⟩ : syracuseStep 2235323 = 3352985) B3352985
theorem B5370845 : Blo 2233435 5370845 := bbase (se 3 (by rfl) ⟨1007033, by rfl⟩ : syracuseStep 5370845 = 2014067) (by norm_num)
theorem B14322253 : Blo 2233435 14322253 := bstep (se 3 (by rfl) ⟨2685422, by rfl⟩ : syracuseStep 14322253 = 5370845) B5370845
theorem B19096337 : Blo 2233435 19096337 := bstep (se 2 (by rfl) ⟨7161126, by rfl⟩ : syracuseStep 19096337 = 14322253) B14322253
theorem B12730891 : Blo 2233435 12730891 := bstep (se 1 (by rfl) ⟨9548168, by rfl⟩ : syracuseStep 12730891 = 19096337) B19096337
theorem B16974521 : Blo 2233435 16974521 := bstep (se 2 (by rfl) ⟨6365445, by rfl⟩ : syracuseStep 16974521 = 12730891) B12730891
theorem B11316347 : Blo 2233435 11316347 := bstep (se 1 (by rfl) ⟨8487260, by rfl⟩ : syracuseStep 11316347 = 16974521) B16974521
theorem B7544231 : Blo 2233435 7544231 := bstep (se 1 (by rfl) ⟨5658173, by rfl⟩ : syracuseStep 7544231 = 11316347) B11316347
theorem B5029487 : Blo 2233435 5029487 := bstep (se 1 (by rfl) ⟨3772115, by rfl⟩ : syracuseStep 5029487 = 7544231) B7544231
theorem B3352991 : Blo 2233435 3352991 := bstep (se 1 (by rfl) ⟨2514743, by rfl⟩ : syracuseStep 3352991 = 5029487) B5029487
theorem B2235327 : Blo 2233435 2235327 := bstep (se 1 (by rfl) ⟨1676495, by rfl⟩ : syracuseStep 2235327 = 3352991) B3352991
theorem B3352997 : Blo 2233435 3352997 := bbase (se 4 (by rfl) ⟨314343, by rfl⟩ : syracuseStep 3352997 = 628687) (by norm_num)
theorem B2235331 : Blo 2233435 2235331 := bstep (se 1 (by rfl) ⟨1676498, by rfl⟩ : syracuseStep 2235331 = 3352997) B3352997
theorem B2829097 : Blo 2233435 2829097 := bbase (se 2 (by rfl) ⟨1060911, by rfl⟩ : syracuseStep 2829097 = 2121823) (by norm_num)
theorem B3772129 : Blo 2233435 3772129 := bstep (se 2 (by rfl) ⟨1414548, by rfl⟩ : syracuseStep 3772129 = 2829097) B2829097
theorem B5029505 : Blo 2233435 5029505 := bstep (se 2 (by rfl) ⟨1886064, by rfl⟩ : syracuseStep 5029505 = 3772129) B3772129
theorem B3353003 : Blo 2233435 3353003 := bstep (se 1 (by rfl) ⟨2514752, by rfl⟩ : syracuseStep 3353003 = 5029505) B5029505
theorem B2235335 : Blo 2233435 2235335 := bstep (se 1 (by rfl) ⟨1676501, by rfl⟩ : syracuseStep 2235335 = 3353003) B3353003
theorem B2514757 : Blo 2233435 2514757 := bbase (se 4 (by rfl) ⟨235758, by rfl⟩ : syracuseStep 2514757 = 471517) (by norm_num)
theorem B3353009 : Blo 2233435 3353009 := bstep (se 2 (by rfl) ⟨1257378, by rfl⟩ : syracuseStep 3353009 = 2514757) B2514757
theorem B2235339 : Blo 2233435 2235339 := bstep (se 1 (by rfl) ⟨1676504, by rfl⟩ : syracuseStep 2235339 = 3353009) B3353009
theorem B4243661 : Blo 2233435 4243661 := bbase (se 3 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 4243661 = 1591373) (by norm_num)
theorem B2829107 : Blo 2233435 2829107 := bstep (se 1 (by rfl) ⟨2121830, by rfl⟩ : syracuseStep 2829107 = 4243661) B4243661
theorem B7544285 : Blo 2233435 7544285 := bstep (se 3 (by rfl) ⟨1414553, by rfl⟩ : syracuseStep 7544285 = 2829107) B2829107
theorem B5029523 : Blo 2233435 5029523 := bstep (se 1 (by rfl) ⟨3772142, by rfl⟩ : syracuseStep 5029523 = 7544285) B7544285
theorem B3353015 : Blo 2233435 3353015 := bstep (se 1 (by rfl) ⟨2514761, by rfl⟩ : syracuseStep 3353015 = 5029523) B5029523
theorem B2235343 : Blo 2233435 2235343 := bstep (se 1 (by rfl) ⟨1676507, by rfl⟩ : syracuseStep 2235343 = 3353015) B3353015
theorem B3353021 : Blo 2233435 3353021 := bbase (se 3 (by rfl) ⟨628691, by rfl⟩ : syracuseStep 3353021 = 1257383) (by norm_num)
theorem B2235347 : Blo 2233435 2235347 := bstep (se 1 (by rfl) ⟨1676510, by rfl⟩ : syracuseStep 2235347 = 3353021) B3353021
theorem B5029541 : Blo 2233435 5029541 := bbase (se 4 (by rfl) ⟨471519, by rfl⟩ : syracuseStep 5029541 = 943039) (by norm_num)
theorem B3353027 : Blo 2233435 3353027 := bstep (se 1 (by rfl) ⟨2514770, by rfl⟩ : syracuseStep 3353027 = 5029541) B5029541
theorem B2235351 : Blo 2233435 2235351 := bstep (se 1 (by rfl) ⟨1676513, by rfl⟩ : syracuseStep 2235351 = 3353027) B3353027
theorem B5658245 : Blo 2233435 5658245 := bbase (se 4 (by rfl) ⟨530460, by rfl⟩ : syracuseStep 5658245 = 1060921) (by norm_num)
theorem B3772163 : Blo 2233435 3772163 := bstep (se 1 (by rfl) ⟨2829122, by rfl⟩ : syracuseStep 3772163 = 5658245) B5658245
theorem B2514775 : Blo 2233435 2514775 := bstep (se 1 (by rfl) ⟨1886081, by rfl⟩ : syracuseStep 2514775 = 3772163) B3772163
theorem B3353033 : Blo 2233435 3353033 := bstep (se 2 (by rfl) ⟨1257387, by rfl⟩ : syracuseStep 3353033 = 2514775) B2514775
theorem B2235355 : Blo 2233435 2235355 := bstep (se 1 (by rfl) ⟨1676516, by rfl⟩ : syracuseStep 2235355 = 3353033) B3353033
theorem B4531717 : Blo 2233435 4531717 := bbase (se 4 (by rfl) ⟨424848, by rfl⟩ : syracuseStep 4531717 = 849697) (by norm_num)
theorem B6042289 : Blo 2233435 6042289 := bstep (se 2 (by rfl) ⟨2265858, by rfl⟩ : syracuseStep 6042289 = 4531717) B4531717
theorem B8056385 : Blo 2233435 8056385 := bstep (se 2 (by rfl) ⟨3021144, by rfl⟩ : syracuseStep 8056385 = 6042289) B6042289
theorem B5370923 : Blo 2233435 5370923 := bstep (se 1 (by rfl) ⟨4028192, by rfl⟩ : syracuseStep 5370923 = 8056385) B8056385
theorem B3580615 : Blo 2233435 3580615 := bstep (se 1 (by rfl) ⟨2685461, by rfl⟩ : syracuseStep 3580615 = 5370923) B5370923
theorem B4774153 : Blo 2233435 4774153 := bstep (se 2 (by rfl) ⟨1790307, by rfl⟩ : syracuseStep 4774153 = 3580615) B3580615
theorem B6365537 : Blo 2233435 6365537 := bstep (se 2 (by rfl) ⟨2387076, by rfl⟩ : syracuseStep 6365537 = 4774153) B4774153
theorem B4243691 : Blo 2233435 4243691 := bstep (se 1 (by rfl) ⟨3182768, by rfl⟩ : syracuseStep 4243691 = 6365537) B6365537
theorem B11316509 : Blo 2233435 11316509 := bstep (se 3 (by rfl) ⟨2121845, by rfl⟩ : syracuseStep 11316509 = 4243691) B4243691
theorem B7544339 : Blo 2233435 7544339 := bstep (se 1 (by rfl) ⟨5658254, by rfl⟩ : syracuseStep 7544339 = 11316509) B11316509
theorem B5029559 : Blo 2233435 5029559 := bstep (se 1 (by rfl) ⟨3772169, by rfl⟩ : syracuseStep 5029559 = 7544339) B7544339
theorem B3353039 : Blo 2233435 3353039 := bstep (se 1 (by rfl) ⟨2514779, by rfl⟩ : syracuseStep 3353039 = 5029559) B5029559
theorem B2235359 : Blo 2233435 2235359 := bstep (se 1 (by rfl) ⟨1676519, by rfl⟩ : syracuseStep 2235359 = 3353039) B3353039
theorem B3353045 : Blo 2233435 3353045 := bbase (se 7 (by rfl) ⟨39293, by rfl⟩ : syracuseStep 3353045 = 78587) (by norm_num)
theorem B2235363 : Blo 2233435 2235363 := bstep (se 1 (by rfl) ⟨1676522, by rfl⟩ : syracuseStep 2235363 = 3353045) B3353045
theorem B8487413 : Blo 2233435 8487413 := bbase (se 5 (by rfl) ⟨397847, by rfl⟩ : syracuseStep 8487413 = 795695) (by norm_num)
theorem B5658275 : Blo 2233435 5658275 := bstep (se 1 (by rfl) ⟨4243706, by rfl⟩ : syracuseStep 5658275 = 8487413) B8487413
theorem B3772183 : Blo 2233435 3772183 := bstep (se 1 (by rfl) ⟨2829137, by rfl⟩ : syracuseStep 3772183 = 5658275) B5658275
theorem B5029577 : Blo 2233435 5029577 := bstep (se 2 (by rfl) ⟨1886091, by rfl⟩ : syracuseStep 5029577 = 3772183) B3772183
theorem B3353051 : Blo 2233435 3353051 := bstep (se 1 (by rfl) ⟨2514788, by rfl⟩ : syracuseStep 3353051 = 5029577) B5029577
theorem B2235367 : Blo 2233435 2235367 := bstep (se 1 (by rfl) ⟨1676525, by rfl⟩ : syracuseStep 2235367 = 3353051) B3353051
theorem B2514793 : Blo 2233435 2514793 := bbase (se 2 (by rfl) ⟨943047, by rfl⟩ : syracuseStep 2514793 = 1886095) (by norm_num)
theorem B3353057 : Blo 2233435 3353057 := bstep (se 2 (by rfl) ⟨1257396, by rfl⟩ : syracuseStep 3353057 = 2514793) B2514793
theorem B2235371 : Blo 2233435 2235371 := bstep (se 1 (by rfl) ⟨1676528, by rfl⟩ : syracuseStep 2235371 = 3353057) B3353057
theorem B4028221 : Blo 2233435 4028221 := bbase (se 3 (by rfl) ⟨755291, by rfl⟩ : syracuseStep 4028221 = 1510583) (by norm_num)
theorem B5370961 : Blo 2233435 5370961 := bstep (se 2 (by rfl) ⟨2014110, by rfl⟩ : syracuseStep 5370961 = 4028221) B4028221
theorem B7161281 : Blo 2233435 7161281 := bstep (se 2 (by rfl) ⟨2685480, by rfl⟩ : syracuseStep 7161281 = 5370961) B5370961
theorem B4774187 : Blo 2233435 4774187 := bstep (se 1 (by rfl) ⟨3580640, by rfl⟩ : syracuseStep 4774187 = 7161281) B7161281
theorem B12731165 : Blo 2233435 12731165 := bstep (se 3 (by rfl) ⟨2387093, by rfl⟩ : syracuseStep 12731165 = 4774187) B4774187
theorem B8487443 : Blo 2233435 8487443 := bstep (se 1 (by rfl) ⟨6365582, by rfl⟩ : syracuseStep 8487443 = 12731165) B12731165
theorem B5658295 : Blo 2233435 5658295 := bstep (se 1 (by rfl) ⟨4243721, by rfl⟩ : syracuseStep 5658295 = 8487443) B8487443
theorem B7544393 : Blo 2233435 7544393 := bstep (se 2 (by rfl) ⟨2829147, by rfl⟩ : syracuseStep 7544393 = 5658295) B5658295
theorem B5029595 : Blo 2233435 5029595 := bstep (se 1 (by rfl) ⟨3772196, by rfl⟩ : syracuseStep 5029595 = 7544393) B7544393
theorem B3353063 : Blo 2233435 3353063 := bstep (se 1 (by rfl) ⟨2514797, by rfl⟩ : syracuseStep 3353063 = 5029595) B5029595
theorem B2235375 : Blo 2233435 2235375 := bstep (se 1 (by rfl) ⟨1676531, by rfl⟩ : syracuseStep 2235375 = 3353063) B3353063
theorem B3353069 : Blo 2233435 3353069 := bbase (se 3 (by rfl) ⟨628700, by rfl⟩ : syracuseStep 3353069 = 1257401) (by norm_num)
theorem B2235379 : Blo 2233435 2235379 := bstep (se 1 (by rfl) ⟨1676534, by rfl⟩ : syracuseStep 2235379 = 3353069) B3353069
theorem B5029613 : Blo 2233435 5029613 := bbase (se 3 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 5029613 = 1886105) (by norm_num)
theorem B3353075 : Blo 2233435 3353075 := bstep (se 1 (by rfl) ⟨2514806, by rfl⟩ : syracuseStep 3353075 = 5029613) B5029613
theorem B2235383 : Blo 2233435 2235383 := bstep (se 1 (by rfl) ⟨1676537, by rfl⟩ : syracuseStep 2235383 = 3353075) B3353075
theorem B3580661 : Blo 2233435 3580661 := bbase (se 5 (by rfl) ⟨167843, by rfl⟩ : syracuseStep 3580661 = 335687) (by norm_num)
theorem B2387107 : Blo 2233435 2387107 := bstep (se 1 (by rfl) ⟨1790330, by rfl⟩ : syracuseStep 2387107 = 3580661) B3580661
theorem B3182809 : Blo 2233435 3182809 := bstep (se 2 (by rfl) ⟨1193553, by rfl⟩ : syracuseStep 3182809 = 2387107) B2387107
theorem B4243745 : Blo 2233435 4243745 := bstep (se 2 (by rfl) ⟨1591404, by rfl⟩ : syracuseStep 4243745 = 3182809) B3182809
theorem B2829163 : Blo 2233435 2829163 := bstep (se 1 (by rfl) ⟨2121872, by rfl⟩ : syracuseStep 2829163 = 4243745) B4243745
theorem B3772217 : Blo 2233435 3772217 := bstep (se 2 (by rfl) ⟨1414581, by rfl⟩ : syracuseStep 3772217 = 2829163) B2829163
theorem B2514811 : Blo 2233435 2514811 := bstep (se 1 (by rfl) ⟨1886108, by rfl⟩ : syracuseStep 2514811 = 3772217) B3772217
theorem B3353081 : Blo 2233435 3353081 := bstep (se 2 (by rfl) ⟨1257405, by rfl⟩ : syracuseStep 3353081 = 2514811) B2514811
theorem B2235387 : Blo 2233435 2235387 := bstep (se 1 (by rfl) ⟨1676540, by rfl⟩ : syracuseStep 2235387 = 3353081) B3353081
theorem B5167813 : Blo 2233435 5167813 := bbase (se 4 (by rfl) ⟨484482, by rfl⟩ : syracuseStep 5167813 = 968965) (by norm_num)
theorem B6890417 : Blo 2233435 6890417 := bstep (se 2 (by rfl) ⟨2583906, by rfl⟩ : syracuseStep 6890417 = 5167813) B5167813
theorem B4593611 : Blo 2233435 4593611 := bstep (se 1 (by rfl) ⟨3445208, by rfl⟩ : syracuseStep 4593611 = 6890417) B6890417
theorem B12249629 : Blo 2233435 12249629 := bstep (se 3 (by rfl) ⟨2296805, by rfl⟩ : syracuseStep 12249629 = 4593611) B4593611
theorem B8166419 : Blo 2233435 8166419 := bstep (se 1 (by rfl) ⟨6124814, by rfl⟩ : syracuseStep 8166419 = 12249629) B12249629
theorem B5444279 : Blo 2233435 5444279 := bstep (se 1 (by rfl) ⟨4083209, by rfl⟩ : syracuseStep 5444279 = 8166419) B8166419
theorem B3629519 : Blo 2233435 3629519 := bstep (se 1 (by rfl) ⟨2722139, by rfl⟩ : syracuseStep 3629519 = 5444279) B5444279
theorem B2419679 : Blo 2233435 2419679 := bstep (se 1 (by rfl) ⟨1814759, by rfl⟩ : syracuseStep 2419679 = 3629519) B3629519
theorem B6452477 : Blo 2233435 6452477 := bstep (se 3 (by rfl) ⟨1209839, by rfl⟩ : syracuseStep 6452477 = 2419679) B2419679
theorem B4301651 : Blo 2233435 4301651 := bstep (se 1 (by rfl) ⟨3226238, by rfl⟩ : syracuseStep 4301651 = 6452477) B6452477
theorem B11471069 : Blo 2233435 11471069 := bstep (se 3 (by rfl) ⟨2150825, by rfl⟩ : syracuseStep 11471069 = 4301651) B4301651
theorem B7647379 : Blo 2233435 7647379 := bstep (se 1 (by rfl) ⟨5735534, by rfl⟩ : syracuseStep 7647379 = 11471069) B11471069
theorem B40786021 : Blo 2233435 40786021 := bstep (se 4 (by rfl) ⟨3823689, by rfl⟩ : syracuseStep 40786021 = 7647379) B7647379
theorem B217525445 : Blo 2233435 217525445 := bstep (se 4 (by rfl) ⟨20393010, by rfl⟩ : syracuseStep 217525445 = 40786021) B40786021
theorem B145016963 : Blo 2233435 145016963 := bstep (se 1 (by rfl) ⟨108762722, by rfl⟩ : syracuseStep 145016963 = 217525445) B217525445
theorem B96677975 : Blo 2233435 96677975 := bstep (se 1 (by rfl) ⟨72508481, by rfl⟩ : syracuseStep 96677975 = 145016963) B145016963
theorem B64451983 : Blo 2233435 64451983 := bstep (se 1 (by rfl) ⟨48338987, by rfl⟩ : syracuseStep 64451983 = 96677975) B96677975
theorem B85935977 : Blo 2233435 85935977 := bstep (se 2 (by rfl) ⟨32225991, by rfl⟩ : syracuseStep 85935977 = 64451983) B64451983
theorem B57290651 : Blo 2233435 57290651 := bstep (se 1 (by rfl) ⟨42967988, by rfl⟩ : syracuseStep 57290651 = 85935977) B85935977
theorem B38193767 : Blo 2233435 38193767 := bstep (se 1 (by rfl) ⟨28645325, by rfl⟩ : syracuseStep 38193767 = 57290651) B57290651
theorem B25462511 : Blo 2233435 25462511 := bstep (se 1 (by rfl) ⟨19096883, by rfl⟩ : syracuseStep 25462511 = 38193767) B38193767
theorem B16975007 : Blo 2233435 16975007 := bstep (se 1 (by rfl) ⟨12731255, by rfl⟩ : syracuseStep 16975007 = 25462511) B25462511
theorem B11316671 : Blo 2233435 11316671 := bstep (se 1 (by rfl) ⟨8487503, by rfl⟩ : syracuseStep 11316671 = 16975007) B16975007
theorem B7544447 : Blo 2233435 7544447 := bstep (se 1 (by rfl) ⟨5658335, by rfl⟩ : syracuseStep 7544447 = 11316671) B11316671
theorem B5029631 : Blo 2233435 5029631 := bstep (se 1 (by rfl) ⟨3772223, by rfl⟩ : syracuseStep 5029631 = 7544447) B7544447
theorem B3353087 : Blo 2233435 3353087 := bstep (se 1 (by rfl) ⟨2514815, by rfl⟩ : syracuseStep 3353087 = 5029631) B5029631
theorem B2235391 : Blo 2233435 2235391 := bstep (se 1 (by rfl) ⟨1676543, by rfl⟩ : syracuseStep 2235391 = 3353087) B3353087
theorem B3353093 : Blo 2233435 3353093 := bbase (se 4 (by rfl) ⟨314352, by rfl⟩ : syracuseStep 3353093 = 628705) (by norm_num)
theorem B2235395 : Blo 2233435 2235395 := bstep (se 1 (by rfl) ⟨1676546, by rfl⟩ : syracuseStep 2235395 = 3353093) B3353093
theorem B3772237 : Blo 2233435 3772237 := bbase (se 3 (by rfl) ⟨707294, by rfl⟩ : syracuseStep 3772237 = 1414589) (by norm_num)
theorem B5029649 : Blo 2233435 5029649 := bstep (se 2 (by rfl) ⟨1886118, by rfl⟩ : syracuseStep 5029649 = 3772237) B3772237
theorem B3353099 : Blo 2233435 3353099 := bstep (se 1 (by rfl) ⟨2514824, by rfl⟩ : syracuseStep 3353099 = 5029649) B5029649
theorem B2235399 : Blo 2233435 2235399 := bstep (se 1 (by rfl) ⟨1676549, by rfl⟩ : syracuseStep 2235399 = 3353099) B3353099
theorem B2514829 : Blo 2233435 2514829 := bbase (se 3 (by rfl) ⟨471530, by rfl⟩ : syracuseStep 2514829 = 943061) (by norm_num)
theorem B3353105 : Blo 2233435 3353105 := bstep (se 2 (by rfl) ⟨1257414, by rfl⟩ : syracuseStep 3353105 = 2514829) B2514829
theorem B2235403 : Blo 2233435 2235403 := bstep (se 1 (by rfl) ⟨1676552, by rfl⟩ : syracuseStep 2235403 = 3353105) B3353105
theorem B7544501 : Blo 2233435 7544501 := bbase (se 5 (by rfl) ⟨353648, by rfl⟩ : syracuseStep 7544501 = 707297) (by norm_num)
theorem B5029667 : Blo 2233435 5029667 := bstep (se 1 (by rfl) ⟨3772250, by rfl⟩ : syracuseStep 5029667 = 7544501) B7544501
theorem B3353111 : Blo 2233435 3353111 := bstep (se 1 (by rfl) ⟨2514833, by rfl⟩ : syracuseStep 3353111 = 5029667) B5029667
theorem B2235407 : Blo 2233435 2235407 := bstep (se 1 (by rfl) ⟨1676555, by rfl⟩ : syracuseStep 2235407 = 3353111) B3353111
theorem B3353117 : Blo 2233435 3353117 := bbase (se 3 (by rfl) ⟨628709, by rfl⟩ : syracuseStep 3353117 = 1257419) (by norm_num)
theorem B2235411 : Blo 2233435 2235411 := bstep (se 1 (by rfl) ⟨1676558, by rfl⟩ : syracuseStep 2235411 = 3353117) B3353117
theorem B5029685 : Blo 2233435 5029685 := bbase (se 5 (by rfl) ⟨235766, by rfl⟩ : syracuseStep 5029685 = 471533) (by norm_num)
theorem B3353123 : Blo 2233435 3353123 := bstep (se 1 (by rfl) ⟨2514842, by rfl⟩ : syracuseStep 3353123 = 5029685) B5029685
theorem B2235415 : Blo 2233435 2235415 := bstep (se 1 (by rfl) ⟨1676561, by rfl⟩ : syracuseStep 2235415 = 3353123) B3353123
theorem B4839421 : Blo 2233435 4839421 := bbase (se 3 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 4839421 = 1814783) (by norm_num)
theorem B6452561 : Blo 2233435 6452561 := bstep (se 2 (by rfl) ⟨2419710, by rfl⟩ : syracuseStep 6452561 = 4839421) B4839421
theorem B17206829 : Blo 2233435 17206829 := bstep (se 3 (by rfl) ⟨3226280, by rfl⟩ : syracuseStep 17206829 = 6452561) B6452561
theorem B11471219 : Blo 2233435 11471219 := bstep (se 1 (by rfl) ⟨8603414, by rfl⟩ : syracuseStep 11471219 = 17206829) B17206829
theorem B7647479 : Blo 2233435 7647479 := bstep (se 1 (by rfl) ⟨5735609, by rfl⟩ : syracuseStep 7647479 = 11471219) B11471219
theorem B5098319 : Blo 2233435 5098319 := bstep (se 1 (by rfl) ⟨3823739, by rfl⟩ : syracuseStep 5098319 = 7647479) B7647479
theorem B3398879 : Blo 2233435 3398879 := bstep (se 1 (by rfl) ⟨2549159, by rfl⟩ : syracuseStep 3398879 = 5098319) B5098319
theorem B9063677 : Blo 2233435 9063677 := bstep (se 3 (by rfl) ⟨1699439, by rfl⟩ : syracuseStep 9063677 = 3398879) B3398879
theorem B6042451 : Blo 2233435 6042451 := bstep (se 1 (by rfl) ⟨4531838, by rfl⟩ : syracuseStep 6042451 = 9063677) B9063677
theorem B8056601 : Blo 2233435 8056601 := bstep (se 2 (by rfl) ⟨3021225, by rfl⟩ : syracuseStep 8056601 = 6042451) B6042451
theorem B5371067 : Blo 2233435 5371067 := bstep (se 1 (by rfl) ⟨4028300, by rfl⟩ : syracuseStep 5371067 = 8056601) B8056601
theorem B14322845 : Blo 2233435 14322845 := bstep (se 3 (by rfl) ⟨2685533, by rfl⟩ : syracuseStep 14322845 = 5371067) B5371067
theorem B9548563 : Blo 2233435 9548563 := bstep (se 1 (by rfl) ⟨7161422, by rfl⟩ : syracuseStep 9548563 = 14322845) B14322845
theorem B12731417 : Blo 2233435 12731417 := bstep (se 2 (by rfl) ⟨4774281, by rfl⟩ : syracuseStep 12731417 = 9548563) B9548563
theorem B8487611 : Blo 2233435 8487611 := bstep (se 1 (by rfl) ⟨6365708, by rfl⟩ : syracuseStep 8487611 = 12731417) B12731417
theorem B5658407 : Blo 2233435 5658407 := bstep (se 1 (by rfl) ⟨4243805, by rfl⟩ : syracuseStep 5658407 = 8487611) B8487611
theorem B3772271 : Blo 2233435 3772271 := bstep (se 1 (by rfl) ⟨2829203, by rfl⟩ : syracuseStep 3772271 = 5658407) B5658407
theorem B2514847 : Blo 2233435 2514847 := bstep (se 1 (by rfl) ⟨1886135, by rfl⟩ : syracuseStep 2514847 = 3772271) B3772271
theorem B3353129 : Blo 2233435 3353129 := bstep (se 2 (by rfl) ⟨1257423, by rfl⟩ : syracuseStep 3353129 = 2514847) B2514847
theorem B2235419 : Blo 2233435 2235419 := bstep (se 1 (by rfl) ⟨1676564, by rfl⟩ : syracuseStep 2235419 = 3353129) B3353129
theorem B14322869 : Blo 2233435 14322869 := bbase (se 5 (by rfl) ⟨671384, by rfl⟩ : syracuseStep 14322869 = 1342769) (by norm_num)
theorem B9548579 : Blo 2233435 9548579 := bstep (se 1 (by rfl) ⟨7161434, by rfl⟩ : syracuseStep 9548579 = 14322869) B14322869
theorem B6365719 : Blo 2233435 6365719 := bstep (se 1 (by rfl) ⟨4774289, by rfl⟩ : syracuseStep 6365719 = 9548579) B9548579
theorem B8487625 : Blo 2233435 8487625 := bstep (se 2 (by rfl) ⟨3182859, by rfl⟩ : syracuseStep 8487625 = 6365719) B6365719
theorem B11316833 : Blo 2233435 11316833 := bstep (se 2 (by rfl) ⟨4243812, by rfl⟩ : syracuseStep 11316833 = 8487625) B8487625
theorem B7544555 : Blo 2233435 7544555 := bstep (se 1 (by rfl) ⟨5658416, by rfl⟩ : syracuseStep 7544555 = 11316833) B11316833
theorem B5029703 : Blo 2233435 5029703 := bstep (se 1 (by rfl) ⟨3772277, by rfl⟩ : syracuseStep 5029703 = 7544555) B7544555
theorem B3353135 : Blo 2233435 3353135 := bstep (se 1 (by rfl) ⟨2514851, by rfl⟩ : syracuseStep 3353135 = 5029703) B5029703
theorem B2235423 : Blo 2233435 2235423 := bstep (se 1 (by rfl) ⟨1676567, by rfl⟩ : syracuseStep 2235423 = 3353135) B3353135
theorem B3353141 : Blo 2233435 3353141 := bbase (se 5 (by rfl) ⟨157178, by rfl⟩ : syracuseStep 3353141 = 314357) (by norm_num)
theorem B2235427 : Blo 2233435 2235427 := bstep (se 1 (by rfl) ⟨1676570, by rfl⟩ : syracuseStep 2235427 = 3353141) B3353141
theorem B5658437 : Blo 2233435 5658437 := bbase (se 4 (by rfl) ⟨530478, by rfl⟩ : syracuseStep 5658437 = 1060957) (by norm_num)
theorem B3772291 : Blo 2233435 3772291 := bstep (se 1 (by rfl) ⟨2829218, by rfl⟩ : syracuseStep 3772291 = 5658437) B5658437
theorem B5029721 : Blo 2233435 5029721 := bstep (se 2 (by rfl) ⟨1886145, by rfl⟩ : syracuseStep 5029721 = 3772291) B3772291
theorem B3353147 : Blo 2233435 3353147 := bstep (se 1 (by rfl) ⟨2514860, by rfl⟩ : syracuseStep 3353147 = 5029721) B5029721
theorem B2235431 : Blo 2233435 2235431 := bstep (se 1 (by rfl) ⟨1676573, by rfl⟩ : syracuseStep 2235431 = 3353147) B3353147
theorem B2514865 : Blo 2233435 2514865 := bbase (se 2 (by rfl) ⟨943074, by rfl⟩ : syracuseStep 2514865 = 1886149) (by norm_num)
theorem B3353153 : Blo 2233435 3353153 := bstep (se 2 (by rfl) ⟨1257432, by rfl⟩ : syracuseStep 3353153 = 2514865) B2514865
theorem B2235435 : Blo 2233435 2235435 := bstep (se 1 (by rfl) ⟨1676576, by rfl⟩ : syracuseStep 2235435 = 3353153) B3353153
theorem C0 (j : ℕ) (h1 : 558358 ≤ j) (h2 : j ≤ 558858) : Blo 2233435 (4 * j + 3) := by
  interval_cases j
  · exact B2233435
  · exact B2233439
  · exact B2233443
  · exact B2233447
  · exact B2233451
  · exact B2233455
  · exact B2233459
  · exact B2233463
  · exact B2233467
  · exact B2233471
  · exact B2233475
  · exact B2233479
  · exact B2233483
  · exact B2233487
  · exact B2233491
  · exact B2233495
  · exact B2233499
  · exact B2233503
  · exact B2233507
  · exact B2233511
  · exact B2233515
  · exact B2233519
  · exact B2233523
  · exact B2233527
  · exact B2233531
  · exact B2233535
  · exact B2233539
  · exact B2233543
  · exact B2233547
  · exact B2233551
  · exact B2233555
  · exact B2233559
  · exact B2233563
  · exact B2233567
  · exact B2233571
  · exact B2233575
  · exact B2233579
  · exact B2233583
  · exact B2233587
  · exact B2233591
  · exact B2233595
  · exact B2233599
  · exact B2233603
  · exact B2233607
  · exact B2233611
  · exact B2233615
  · exact B2233619
  · exact B2233623
  · exact B2233627
  · exact B2233631
  · exact B2233635
  · exact B2233639
  · exact B2233643
  · exact B2233647
  · exact B2233651
  · exact B2233655
  · exact B2233659
  · exact B2233663
  · exact B2233667
  · exact B2233671
  · exact B2233675
  · exact B2233679
  · exact B2233683
  · exact B2233687
  · exact B2233691
  · exact B2233695
  · exact B2233699
  · exact B2233703
  · exact B2233707
  · exact B2233711
  · exact B2233715
  · exact B2233719
  · exact B2233723
  · exact B2233727
  · exact B2233731
  · exact B2233735
  · exact B2233739
  · exact B2233743
  · exact B2233747
  · exact B2233751
  · exact B2233755
  · exact B2233759
  · exact B2233763
  · exact B2233767
  · exact B2233771
  · exact B2233775
  · exact B2233779
  · exact B2233783
  · exact B2233787
  · exact B2233791
  · exact B2233795
  · exact B2233799
  · exact B2233803
  · exact B2233807
  · exact B2233811
  · exact B2233815
  · exact B2233819
  · exact B2233823
  · exact B2233827
  · exact B2233831
  · exact B2233835
  · exact B2233839
  · exact B2233843
  · exact B2233847
  · exact B2233851
  · exact B2233855
  · exact B2233859
  · exact B2233863
  · exact B2233867
  · exact B2233871
  · exact B2233875
  · exact B2233879
  · exact B2233883
  · exact B2233887
  · exact B2233891
  · exact B2233895
  · exact B2233899
  · exact B2233903
  · exact B2233907
  · exact B2233911
  · exact B2233915
  · exact B2233919
  · exact B2233923
  · exact B2233927
  · exact B2233931
  · exact B2233935
  · exact B2233939
  · exact B2233943
  · exact B2233947
  · exact B2233951
  · exact B2233955
  · exact B2233959
  · exact B2233963
  · exact B2233967
  · exact B2233971
  · exact B2233975
  · exact B2233979
  · exact B2233983
  · exact B2233987
  · exact B2233991
  · exact B2233995
  · exact B2233999
  · exact B2234003
  · exact B2234007
  · exact B2234011
  · exact B2234015
  · exact B2234019
  · exact B2234023
  · exact B2234027
  · exact B2234031
  · exact B2234035
  · exact B2234039
  · exact B2234043
  · exact B2234047
  · exact B2234051
  · exact B2234055
  · exact B2234059
  · exact B2234063
  · exact B2234067
  · exact B2234071
  · exact B2234075
  · exact B2234079
  · exact B2234083
  · exact B2234087
  · exact B2234091
  · exact B2234095
  · exact B2234099
  · exact B2234103
  · exact B2234107
  · exact B2234111
  · exact B2234115
  · exact B2234119
  · exact B2234123
  · exact B2234127
  · exact B2234131
  · exact B2234135
  · exact B2234139
  · exact B2234143
  · exact B2234147
  · exact B2234151
  · exact B2234155
  · exact B2234159
  · exact B2234163
  · exact B2234167
  · exact B2234171
  · exact B2234175
  · exact B2234179
  · exact B2234183
  · exact B2234187
  · exact B2234191
  · exact B2234195
  · exact B2234199
  · exact B2234203
  · exact B2234207
  · exact B2234211
  · exact B2234215
  · exact B2234219
  · exact B2234223
  · exact B2234227
  · exact B2234231
  · exact B2234235
  · exact B2234239
  · exact B2234243
  · exact B2234247
  · exact B2234251
  · exact B2234255
  · exact B2234259
  · exact B2234263
  · exact B2234267
  · exact B2234271
  · exact B2234275
  · exact B2234279
  · exact B2234283
  · exact B2234287
  · exact B2234291
  · exact B2234295
  · exact B2234299
  · exact B2234303
  · exact B2234307
  · exact B2234311
  · exact B2234315
  · exact B2234319
  · exact B2234323
  · exact B2234327
  · exact B2234331
  · exact B2234335
  · exact B2234339
  · exact B2234343
  · exact B2234347
  · exact B2234351
  · exact B2234355
  · exact B2234359
  · exact B2234363
  · exact B2234367
  · exact B2234371
  · exact B2234375
  · exact B2234379
  · exact B2234383
  · exact B2234387
  · exact B2234391
  · exact B2234395
  · exact B2234399
  · exact B2234403
  · exact B2234407
  · exact B2234411
  · exact B2234415
  · exact B2234419
  · exact B2234423
  · exact B2234427
  · exact B2234431
  · exact B2234435
  · exact B2234439
  · exact B2234443
  · exact B2234447
  · exact B2234451
  · exact B2234455
  · exact B2234459
  · exact B2234463
  · exact B2234467
  · exact B2234471
  · exact B2234475
  · exact B2234479
  · exact B2234483
  · exact B2234487
  · exact B2234491
  · exact B2234495
  · exact B2234499
  · exact B2234503
  · exact B2234507
  · exact B2234511
  · exact B2234515
  · exact B2234519
  · exact B2234523
  · exact B2234527
  · exact B2234531
  · exact B2234535
  · exact B2234539
  · exact B2234543
  · exact B2234547
  · exact B2234551
  · exact B2234555
  · exact B2234559
  · exact B2234563
  · exact B2234567
  · exact B2234571
  · exact B2234575
  · exact B2234579
  · exact B2234583
  · exact B2234587
  · exact B2234591
  · exact B2234595
  · exact B2234599
  · exact B2234603
  · exact B2234607
  · exact B2234611
  · exact B2234615
  · exact B2234619
  · exact B2234623
  · exact B2234627
  · exact B2234631
  · exact B2234635
  · exact B2234639
  · exact B2234643
  · exact B2234647
  · exact B2234651
  · exact B2234655
  · exact B2234659
  · exact B2234663
  · exact B2234667
  · exact B2234671
  · exact B2234675
  · exact B2234679
  · exact B2234683
  · exact B2234687
  · exact B2234691
  · exact B2234695
  · exact B2234699
  · exact B2234703
  · exact B2234707
  · exact B2234711
  · exact B2234715
  · exact B2234719
  · exact B2234723
  · exact B2234727
  · exact B2234731
  · exact B2234735
  · exact B2234739
  · exact B2234743
  · exact B2234747
  · exact B2234751
  · exact B2234755
  · exact B2234759
  · exact B2234763
  · exact B2234767
  · exact B2234771
  · exact B2234775
  · exact B2234779
  · exact B2234783
  · exact B2234787
  · exact B2234791
  · exact B2234795
  · exact B2234799
  · exact B2234803
  · exact B2234807
  · exact B2234811
  · exact B2234815
  · exact B2234819
  · exact B2234823
  · exact B2234827
  · exact B2234831
  · exact B2234835
  · exact B2234839
  · exact B2234843
  · exact B2234847
  · exact B2234851
  · exact B2234855
  · exact B2234859
  · exact B2234863
  · exact B2234867
  · exact B2234871
  · exact B2234875
  · exact B2234879
  · exact B2234883
  · exact B2234887
  · exact B2234891
  · exact B2234895
  · exact B2234899
  · exact B2234903
  · exact B2234907
  · exact B2234911
  · exact B2234915
  · exact B2234919
  · exact B2234923
  · exact B2234927
  · exact B2234931
  · exact B2234935
  · exact B2234939
  · exact B2234943
  · exact B2234947
  · exact B2234951
  · exact B2234955
  · exact B2234959
  · exact B2234963
  · exact B2234967
  · exact B2234971
  · exact B2234975
  · exact B2234979
  · exact B2234983
  · exact B2234987
  · exact B2234991
  · exact B2234995
  · exact B2234999
  · exact B2235003
  · exact B2235007
  · exact B2235011
  · exact B2235015
  · exact B2235019
  · exact B2235023
  · exact B2235027
  · exact B2235031
  · exact B2235035
  · exact B2235039
  · exact B2235043
  · exact B2235047
  · exact B2235051
  · exact B2235055
  · exact B2235059
  · exact B2235063
  · exact B2235067
  · exact B2235071
  · exact B2235075
  · exact B2235079
  · exact B2235083
  · exact B2235087
  · exact B2235091
  · exact B2235095
  · exact B2235099
  · exact B2235103
  · exact B2235107
  · exact B2235111
  · exact B2235115
  · exact B2235119
  · exact B2235123
  · exact B2235127
  · exact B2235131
  · exact B2235135
  · exact B2235139
  · exact B2235143
  · exact B2235147
  · exact B2235151
  · exact B2235155
  · exact B2235159
  · exact B2235163
  · exact B2235167
  · exact B2235171
  · exact B2235175
  · exact B2235179
  · exact B2235183
  · exact B2235187
  · exact B2235191
  · exact B2235195
  · exact B2235199
  · exact B2235203
  · exact B2235207
  · exact B2235211
  · exact B2235215
  · exact B2235219
  · exact B2235223
  · exact B2235227
  · exact B2235231
  · exact B2235235
  · exact B2235239
  · exact B2235243
  · exact B2235247
  · exact B2235251
  · exact B2235255
  · exact B2235259
  · exact B2235263
  · exact B2235267
  · exact B2235271
  · exact B2235275
  · exact B2235279
  · exact B2235283
  · exact B2235287
  · exact B2235291
  · exact B2235295
  · exact B2235299
  · exact B2235303
  · exact B2235307
  · exact B2235311
  · exact B2235315
  · exact B2235319
  · exact B2235323
  · exact B2235327
  · exact B2235331
  · exact B2235335
  · exact B2235339
  · exact B2235343
  · exact B2235347
  · exact B2235351
  · exact B2235355
  · exact B2235359
  · exact B2235363
  · exact B2235367
  · exact B2235371
  · exact B2235375
  · exact B2235379
  · exact B2235383
  · exact B2235387
  · exact B2235391
  · exact B2235395
  · exact B2235399
  · exact B2235403
  · exact B2235407
  · exact B2235411
  · exact B2235415
  · exact B2235419
  · exact B2235423
  · exact B2235427
  · exact B2235431
  · exact B2235435
theorem solution (m : ℕ) (hlo : 2233435 ≤ m) (hhi : m ≤ 2235435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 558358 ≤ j := by omega
    have hj2 : j ≤ 558858 := by omega
    have hb : Blo 2233435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
