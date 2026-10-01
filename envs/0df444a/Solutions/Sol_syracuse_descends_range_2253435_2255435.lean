-- Prove2me | solution 1 for syracuse_descends_range_2253435_2255435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:10.319628+00:00
-- url     : https://prove2.me/submissions/66c2a043-98ac-4cf0-92f3-b6dfc1db3d2e

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

theorem B2852005 : Blo 2253435 2852005 := bbase (se 4 (by rfl) ⟨267375, by rfl⟩ : syracuseStep 2852005 = 534751) (by norm_num)
theorem B3802673 : Blo 2253435 3802673 := bstep (se 2 (by rfl) ⟨1426002, by rfl⟩ : syracuseStep 3802673 = 2852005) B2852005
theorem B2535115 : Blo 2253435 2535115 := bstep (se 1 (by rfl) ⟨1901336, by rfl⟩ : syracuseStep 2535115 = 3802673) B3802673
theorem B3380153 : Blo 2253435 3380153 := bstep (se 2 (by rfl) ⟨1267557, by rfl⟩ : syracuseStep 3380153 = 2535115) B2535115
theorem B2253435 : Blo 2253435 2253435 := bstep (se 1 (by rfl) ⟨1690076, by rfl⟩ : syracuseStep 2253435 = 3380153) B3380153
theorem B11563685 : Blo 2253435 11563685 := bbase (se 4 (by rfl) ⟨1084095, by rfl⟩ : syracuseStep 11563685 = 2168191) (by norm_num)
theorem B7709123 : Blo 2253435 7709123 := bstep (se 1 (by rfl) ⟨5781842, by rfl⟩ : syracuseStep 7709123 = 11563685) B11563685
theorem B5139415 : Blo 2253435 5139415 := bstep (se 1 (by rfl) ⟨3854561, by rfl⟩ : syracuseStep 5139415 = 7709123) B7709123
theorem B27410213 : Blo 2253435 27410213 := bstep (se 4 (by rfl) ⟨2569707, by rfl⟩ : syracuseStep 27410213 = 5139415) B5139415
theorem B18273475 : Blo 2253435 18273475 := bstep (se 1 (by rfl) ⟨13705106, by rfl⟩ : syracuseStep 18273475 = 27410213) B27410213
theorem B24364633 : Blo 2253435 24364633 := bstep (se 2 (by rfl) ⟨9136737, by rfl⟩ : syracuseStep 24364633 = 18273475) B18273475
theorem B32486177 : Blo 2253435 32486177 := bstep (se 2 (by rfl) ⟨12182316, by rfl⟩ : syracuseStep 32486177 = 24364633) B24364633
theorem B21657451 : Blo 2253435 21657451 := bstep (se 1 (by rfl) ⟨16243088, by rfl⟩ : syracuseStep 21657451 = 32486177) B32486177
theorem B28876601 : Blo 2253435 28876601 := bstep (se 2 (by rfl) ⟨10828725, by rfl⟩ : syracuseStep 28876601 = 21657451) B21657451
theorem B19251067 : Blo 2253435 19251067 := bstep (se 1 (by rfl) ⟨14438300, by rfl⟩ : syracuseStep 19251067 = 28876601) B28876601
theorem B25668089 : Blo 2253435 25668089 := bstep (se 2 (by rfl) ⟨9625533, by rfl⟩ : syracuseStep 25668089 = 19251067) B19251067
theorem B17112059 : Blo 2253435 17112059 := bstep (se 1 (by rfl) ⟨12834044, by rfl⟩ : syracuseStep 17112059 = 25668089) B25668089
theorem B11408039 : Blo 2253435 11408039 := bstep (se 1 (by rfl) ⟨8556029, by rfl⟩ : syracuseStep 11408039 = 17112059) B17112059
theorem B7605359 : Blo 2253435 7605359 := bstep (se 1 (by rfl) ⟨5704019, by rfl⟩ : syracuseStep 7605359 = 11408039) B11408039
theorem B5070239 : Blo 2253435 5070239 := bstep (se 1 (by rfl) ⟨3802679, by rfl⟩ : syracuseStep 5070239 = 7605359) B7605359
theorem B3380159 : Blo 2253435 3380159 := bstep (se 1 (by rfl) ⟨2535119, by rfl⟩ : syracuseStep 3380159 = 5070239) B5070239
theorem B2253439 : Blo 2253435 2253439 := bstep (se 1 (by rfl) ⟨1690079, by rfl⟩ : syracuseStep 2253439 = 3380159) B3380159
theorem B3380165 : Blo 2253435 3380165 := bbase (se 4 (by rfl) ⟨316890, by rfl⟩ : syracuseStep 3380165 = 633781) (by norm_num)
theorem B2253443 : Blo 2253435 2253443 := bstep (se 1 (by rfl) ⟨1690082, by rfl⟩ : syracuseStep 2253443 = 3380165) B3380165
theorem B3802693 : Blo 2253435 3802693 := bbase (se 4 (by rfl) ⟨356502, by rfl⟩ : syracuseStep 3802693 = 713005) (by norm_num)
theorem B5070257 : Blo 2253435 5070257 := bstep (se 2 (by rfl) ⟨1901346, by rfl⟩ : syracuseStep 5070257 = 3802693) B3802693
theorem B3380171 : Blo 2253435 3380171 := bstep (se 1 (by rfl) ⟨2535128, by rfl⟩ : syracuseStep 3380171 = 5070257) B5070257
theorem B2253447 : Blo 2253435 2253447 := bstep (se 1 (by rfl) ⟨1690085, by rfl⟩ : syracuseStep 2253447 = 3380171) B3380171
theorem B2535133 : Blo 2253435 2535133 := bbase (se 3 (by rfl) ⟨475337, by rfl⟩ : syracuseStep 2535133 = 950675) (by norm_num)
theorem B3380177 : Blo 2253435 3380177 := bstep (se 2 (by rfl) ⟨1267566, by rfl⟩ : syracuseStep 3380177 = 2535133) B2535133
theorem B2253451 : Blo 2253435 2253451 := bstep (se 1 (by rfl) ⟨1690088, by rfl⟩ : syracuseStep 2253451 = 3380177) B3380177
theorem B7605413 : Blo 2253435 7605413 := bbase (se 4 (by rfl) ⟨713007, by rfl⟩ : syracuseStep 7605413 = 1426015) (by norm_num)
theorem B5070275 : Blo 2253435 5070275 := bstep (se 1 (by rfl) ⟨3802706, by rfl⟩ : syracuseStep 5070275 = 7605413) B7605413
theorem B3380183 : Blo 2253435 3380183 := bstep (se 1 (by rfl) ⟨2535137, by rfl⟩ : syracuseStep 3380183 = 5070275) B5070275
theorem B2253455 : Blo 2253435 2253455 := bstep (se 1 (by rfl) ⟨1690091, by rfl⟩ : syracuseStep 2253455 = 3380183) B3380183
theorem B3380189 : Blo 2253435 3380189 := bbase (se 3 (by rfl) ⟨633785, by rfl⟩ : syracuseStep 3380189 = 1267571) (by norm_num)
theorem B2253459 : Blo 2253435 2253459 := bstep (se 1 (by rfl) ⟨1690094, by rfl⟩ : syracuseStep 2253459 = 3380189) B3380189
theorem B5070293 : Blo 2253435 5070293 := bbase (se 7 (by rfl) ⟨59417, by rfl⟩ : syracuseStep 5070293 = 118835) (by norm_num)
theorem B3380195 : Blo 2253435 3380195 := bstep (se 1 (by rfl) ⟨2535146, by rfl⟩ : syracuseStep 3380195 = 5070293) B5070293
theorem B2253463 : Blo 2253435 2253463 := bstep (se 1 (by rfl) ⟨1690097, by rfl⟩ : syracuseStep 2253463 = 3380195) B3380195
theorem B2930401 : Blo 2253435 2930401 := bbase (se 2 (by rfl) ⟨1098900, by rfl⟩ : syracuseStep 2930401 = 2197801) (by norm_num)
theorem B3907201 : Blo 2253435 3907201 := bstep (se 2 (by rfl) ⟨1465200, by rfl⟩ : syracuseStep 3907201 = 2930401) B2930401
theorem B5209601 : Blo 2253435 5209601 := bstep (se 2 (by rfl) ⟨1953600, by rfl⟩ : syracuseStep 5209601 = 3907201) B3907201
theorem B13892269 : Blo 2253435 13892269 := bstep (se 3 (by rfl) ⟨2604800, by rfl⟩ : syracuseStep 13892269 = 5209601) B5209601
theorem B18523025 : Blo 2253435 18523025 := bstep (se 2 (by rfl) ⟨6946134, by rfl⟩ : syracuseStep 18523025 = 13892269) B13892269
theorem B12348683 : Blo 2253435 12348683 := bstep (se 1 (by rfl) ⟨9261512, by rfl⟩ : syracuseStep 12348683 = 18523025) B18523025
theorem B8232455 : Blo 2253435 8232455 := bstep (se 1 (by rfl) ⟨6174341, by rfl⟩ : syracuseStep 8232455 = 12348683) B12348683
theorem B21953213 : Blo 2253435 21953213 := bstep (se 3 (by rfl) ⟨4116227, by rfl⟩ : syracuseStep 21953213 = 8232455) B8232455
theorem B14635475 : Blo 2253435 14635475 := bstep (se 1 (by rfl) ⟨10976606, by rfl⟩ : syracuseStep 14635475 = 21953213) B21953213
theorem B9756983 : Blo 2253435 9756983 := bstep (se 1 (by rfl) ⟨7317737, by rfl⟩ : syracuseStep 9756983 = 14635475) B14635475
theorem B26018621 : Blo 2253435 26018621 := bstep (se 3 (by rfl) ⟨4878491, by rfl⟩ : syracuseStep 26018621 = 9756983) B9756983
theorem B17345747 : Blo 2253435 17345747 := bstep (se 1 (by rfl) ⟨13009310, by rfl⟩ : syracuseStep 17345747 = 26018621) B26018621
theorem B11563831 : Blo 2253435 11563831 := bstep (se 1 (by rfl) ⟨8672873, by rfl⟩ : syracuseStep 11563831 = 17345747) B17345747
theorem B15418441 : Blo 2253435 15418441 := bstep (se 2 (by rfl) ⟨5781915, by rfl⟩ : syracuseStep 15418441 = 11563831) B11563831
theorem B20557921 : Blo 2253435 20557921 := bstep (se 2 (by rfl) ⟨7709220, by rfl⟩ : syracuseStep 20557921 = 15418441) B15418441
theorem B27410561 : Blo 2253435 27410561 := bstep (se 2 (by rfl) ⟨10278960, by rfl⟩ : syracuseStep 27410561 = 20557921) B20557921
theorem B18273707 : Blo 2253435 18273707 := bstep (se 1 (by rfl) ⟨13705280, by rfl⟩ : syracuseStep 18273707 = 27410561) B27410561
theorem B12182471 : Blo 2253435 12182471 := bstep (se 1 (by rfl) ⟨9136853, by rfl⟩ : syracuseStep 12182471 = 18273707) B18273707
theorem B8121647 : Blo 2253435 8121647 := bstep (se 1 (by rfl) ⟨6091235, by rfl⟩ : syracuseStep 8121647 = 12182471) B12182471
theorem B21657725 : Blo 2253435 21657725 := bstep (se 3 (by rfl) ⟨4060823, by rfl⟩ : syracuseStep 21657725 = 8121647) B8121647
theorem B14438483 : Blo 2253435 14438483 := bstep (se 1 (by rfl) ⟨10828862, by rfl⟩ : syracuseStep 14438483 = 21657725) B21657725
theorem B9625655 : Blo 2253435 9625655 := bstep (se 1 (by rfl) ⟨7219241, by rfl⟩ : syracuseStep 9625655 = 14438483) B14438483
theorem B6417103 : Blo 2253435 6417103 := bstep (se 1 (by rfl) ⟨4812827, by rfl⟩ : syracuseStep 6417103 = 9625655) B9625655
theorem B8556137 : Blo 2253435 8556137 := bstep (se 2 (by rfl) ⟨3208551, by rfl⟩ : syracuseStep 8556137 = 6417103) B6417103
theorem B5704091 : Blo 2253435 5704091 := bstep (se 1 (by rfl) ⟨4278068, by rfl⟩ : syracuseStep 5704091 = 8556137) B8556137
theorem B3802727 : Blo 2253435 3802727 := bstep (se 1 (by rfl) ⟨2852045, by rfl⟩ : syracuseStep 3802727 = 5704091) B5704091
theorem B2535151 : Blo 2253435 2535151 := bstep (se 1 (by rfl) ⟨1901363, by rfl⟩ : syracuseStep 2535151 = 3802727) B3802727
theorem B3380201 : Blo 2253435 3380201 := bstep (se 2 (by rfl) ⟨1267575, by rfl⟩ : syracuseStep 3380201 = 2535151) B2535151
theorem B2253467 : Blo 2253435 2253467 := bstep (se 1 (by rfl) ⟨1690100, by rfl⟩ : syracuseStep 2253467 = 3380201) B3380201
theorem B7219253 : Blo 2253435 7219253 := bbase (se 5 (by rfl) ⟨338402, by rfl⟩ : syracuseStep 7219253 = 676805) (by norm_num)
theorem B19251341 : Blo 2253435 19251341 := bstep (se 3 (by rfl) ⟨3609626, by rfl⟩ : syracuseStep 19251341 = 7219253) B7219253
theorem B12834227 : Blo 2253435 12834227 := bstep (se 1 (by rfl) ⟨9625670, by rfl⟩ : syracuseStep 12834227 = 19251341) B19251341
theorem B8556151 : Blo 2253435 8556151 := bstep (se 1 (by rfl) ⟨6417113, by rfl⟩ : syracuseStep 8556151 = 12834227) B12834227
theorem B11408201 : Blo 2253435 11408201 := bstep (se 2 (by rfl) ⟨4278075, by rfl⟩ : syracuseStep 11408201 = 8556151) B8556151
theorem B7605467 : Blo 2253435 7605467 := bstep (se 1 (by rfl) ⟨5704100, by rfl⟩ : syracuseStep 7605467 = 11408201) B11408201
theorem B5070311 : Blo 2253435 5070311 := bstep (se 1 (by rfl) ⟨3802733, by rfl⟩ : syracuseStep 5070311 = 7605467) B7605467
theorem B3380207 : Blo 2253435 3380207 := bstep (se 1 (by rfl) ⟨2535155, by rfl⟩ : syracuseStep 3380207 = 5070311) B5070311
theorem B2253471 : Blo 2253435 2253471 := bstep (se 1 (by rfl) ⟨1690103, by rfl⟩ : syracuseStep 2253471 = 3380207) B3380207
theorem B3380213 : Blo 2253435 3380213 := bbase (se 5 (by rfl) ⟨158447, by rfl⟩ : syracuseStep 3380213 = 316895) (by norm_num)
theorem B2253475 : Blo 2253435 2253475 := bstep (se 1 (by rfl) ⟨1690106, by rfl⟩ : syracuseStep 2253475 = 3380213) B3380213
theorem B4812853 : Blo 2253435 4812853 := bbase (se 5 (by rfl) ⟨225602, by rfl⟩ : syracuseStep 4812853 = 451205) (by norm_num)
theorem B6417137 : Blo 2253435 6417137 := bstep (se 2 (by rfl) ⟨2406426, by rfl⟩ : syracuseStep 6417137 = 4812853) B4812853
theorem B4278091 : Blo 2253435 4278091 := bstep (se 1 (by rfl) ⟨3208568, by rfl⟩ : syracuseStep 4278091 = 6417137) B6417137
theorem B5704121 : Blo 2253435 5704121 := bstep (se 2 (by rfl) ⟨2139045, by rfl⟩ : syracuseStep 5704121 = 4278091) B4278091
theorem B3802747 : Blo 2253435 3802747 := bstep (se 1 (by rfl) ⟨2852060, by rfl⟩ : syracuseStep 3802747 = 5704121) B5704121
theorem B5070329 : Blo 2253435 5070329 := bstep (se 2 (by rfl) ⟨1901373, by rfl⟩ : syracuseStep 5070329 = 3802747) B3802747
theorem B3380219 : Blo 2253435 3380219 := bstep (se 1 (by rfl) ⟨2535164, by rfl⟩ : syracuseStep 3380219 = 5070329) B5070329
theorem B2253479 : Blo 2253435 2253479 := bstep (se 1 (by rfl) ⟨1690109, by rfl⟩ : syracuseStep 2253479 = 3380219) B3380219
theorem B2535169 : Blo 2253435 2535169 := bbase (se 2 (by rfl) ⟨950688, by rfl⟩ : syracuseStep 2535169 = 1901377) (by norm_num)
theorem B3380225 : Blo 2253435 3380225 := bstep (se 2 (by rfl) ⟨1267584, by rfl⟩ : syracuseStep 3380225 = 2535169) B2535169
theorem B2253483 : Blo 2253435 2253483 := bstep (se 1 (by rfl) ⟨1690112, by rfl⟩ : syracuseStep 2253483 = 3380225) B3380225
theorem B5704141 : Blo 2253435 5704141 := bbase (se 3 (by rfl) ⟨1069526, by rfl⟩ : syracuseStep 5704141 = 2139053) (by norm_num)
theorem B7605521 : Blo 2253435 7605521 := bstep (se 2 (by rfl) ⟨2852070, by rfl⟩ : syracuseStep 7605521 = 5704141) B5704141
theorem B5070347 : Blo 2253435 5070347 := bstep (se 1 (by rfl) ⟨3802760, by rfl⟩ : syracuseStep 5070347 = 7605521) B7605521
theorem B3380231 : Blo 2253435 3380231 := bstep (se 1 (by rfl) ⟨2535173, by rfl⟩ : syracuseStep 3380231 = 5070347) B5070347
theorem B2253487 : Blo 2253435 2253487 := bstep (se 1 (by rfl) ⟨1690115, by rfl⟩ : syracuseStep 2253487 = 3380231) B3380231
theorem B3380237 : Blo 2253435 3380237 := bbase (se 3 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 3380237 = 1267589) (by norm_num)
theorem B2253491 : Blo 2253435 2253491 := bstep (se 1 (by rfl) ⟨1690118, by rfl⟩ : syracuseStep 2253491 = 3380237) B3380237
theorem B5070365 : Blo 2253435 5070365 := bbase (se 3 (by rfl) ⟨950693, by rfl⟩ : syracuseStep 5070365 = 1901387) (by norm_num)
theorem B3380243 : Blo 2253435 3380243 := bstep (se 1 (by rfl) ⟨2535182, by rfl⟩ : syracuseStep 3380243 = 5070365) B5070365
theorem B2253495 : Blo 2253435 2253495 := bstep (se 1 (by rfl) ⟨1690121, by rfl⟩ : syracuseStep 2253495 = 3380243) B3380243
theorem B3802781 : Blo 2253435 3802781 := bbase (se 3 (by rfl) ⟨713021, by rfl⟩ : syracuseStep 3802781 = 1426043) (by norm_num)
theorem B2535187 : Blo 2253435 2535187 := bstep (se 1 (by rfl) ⟨1901390, by rfl⟩ : syracuseStep 2535187 = 3802781) B3802781
theorem B3380249 : Blo 2253435 3380249 := bstep (se 2 (by rfl) ⟨1267593, by rfl⟩ : syracuseStep 3380249 = 2535187) B2535187
theorem B2253499 : Blo 2253435 2253499 := bstep (se 1 (by rfl) ⟨1690124, by rfl⟩ : syracuseStep 2253499 = 3380249) B3380249
theorem B5209685 : Blo 2253435 5209685 := bbase (se 8 (by rfl) ⟨30525, by rfl⟩ : syracuseStep 5209685 = 61051) (by norm_num)
theorem B3473123 : Blo 2253435 3473123 := bstep (se 1 (by rfl) ⟨2604842, by rfl⟩ : syracuseStep 3473123 = 5209685) B5209685
theorem B9261661 : Blo 2253435 9261661 := bstep (se 3 (by rfl) ⟨1736561, by rfl⟩ : syracuseStep 9261661 = 3473123) B3473123
theorem B12348881 : Blo 2253435 12348881 := bstep (se 2 (by rfl) ⟨4630830, by rfl⟩ : syracuseStep 12348881 = 9261661) B9261661
theorem B8232587 : Blo 2253435 8232587 := bstep (se 1 (by rfl) ⟨6174440, by rfl⟩ : syracuseStep 8232587 = 12348881) B12348881
theorem B5488391 : Blo 2253435 5488391 := bstep (se 1 (by rfl) ⟨4116293, by rfl⟩ : syracuseStep 5488391 = 8232587) B8232587
theorem B3658927 : Blo 2253435 3658927 := bstep (se 1 (by rfl) ⟨2744195, by rfl⟩ : syracuseStep 3658927 = 5488391) B5488391
theorem B4878569 : Blo 2253435 4878569 := bstep (se 2 (by rfl) ⟨1829463, by rfl⟩ : syracuseStep 4878569 = 3658927) B3658927
theorem B13009517 : Blo 2253435 13009517 := bstep (se 3 (by rfl) ⟨2439284, by rfl⟩ : syracuseStep 13009517 = 4878569) B4878569
theorem B8673011 : Blo 2253435 8673011 := bstep (se 1 (by rfl) ⟨6504758, by rfl⟩ : syracuseStep 8673011 = 13009517) B13009517
theorem B5782007 : Blo 2253435 5782007 := bstep (se 1 (by rfl) ⟨4336505, by rfl⟩ : syracuseStep 5782007 = 8673011) B8673011
theorem B3854671 : Blo 2253435 3854671 := bstep (se 1 (by rfl) ⟨2891003, by rfl⟩ : syracuseStep 3854671 = 5782007) B5782007
theorem B20558245 : Blo 2253435 20558245 := bstep (se 4 (by rfl) ⟨1927335, by rfl⟩ : syracuseStep 20558245 = 3854671) B3854671
theorem B27410993 : Blo 2253435 27410993 := bstep (se 2 (by rfl) ⟨10279122, by rfl⟩ : syracuseStep 27410993 = 20558245) B20558245
theorem B18273995 : Blo 2253435 18273995 := bstep (se 1 (by rfl) ⟨13705496, by rfl⟩ : syracuseStep 18273995 = 27410993) B27410993
theorem B12182663 : Blo 2253435 12182663 := bstep (se 1 (by rfl) ⟨9136997, by rfl⟩ : syracuseStep 12182663 = 18273995) B18273995
theorem B32487101 : Blo 2253435 32487101 := bstep (se 3 (by rfl) ⟨6091331, by rfl⟩ : syracuseStep 32487101 = 12182663) B12182663
theorem B21658067 : Blo 2253435 21658067 := bstep (se 1 (by rfl) ⟨16243550, by rfl⟩ : syracuseStep 21658067 = 32487101) B32487101
theorem B14438711 : Blo 2253435 14438711 := bstep (se 1 (by rfl) ⟨10829033, by rfl⟩ : syracuseStep 14438711 = 21658067) B21658067
theorem B9625807 : Blo 2253435 9625807 := bstep (se 1 (by rfl) ⟨7219355, by rfl⟩ : syracuseStep 9625807 = 14438711) B14438711
theorem B12834409 : Blo 2253435 12834409 := bstep (se 2 (by rfl) ⟨4812903, by rfl⟩ : syracuseStep 12834409 = 9625807) B9625807
theorem B17112545 : Blo 2253435 17112545 := bstep (se 2 (by rfl) ⟨6417204, by rfl⟩ : syracuseStep 17112545 = 12834409) B12834409
theorem B11408363 : Blo 2253435 11408363 := bstep (se 1 (by rfl) ⟨8556272, by rfl⟩ : syracuseStep 11408363 = 17112545) B17112545
theorem B7605575 : Blo 2253435 7605575 := bstep (se 1 (by rfl) ⟨5704181, by rfl⟩ : syracuseStep 7605575 = 11408363) B11408363
theorem B5070383 : Blo 2253435 5070383 := bstep (se 1 (by rfl) ⟨3802787, by rfl⟩ : syracuseStep 5070383 = 7605575) B7605575
theorem B3380255 : Blo 2253435 3380255 := bstep (se 1 (by rfl) ⟨2535191, by rfl⟩ : syracuseStep 3380255 = 5070383) B5070383
theorem B2253503 : Blo 2253435 2253503 := bstep (se 1 (by rfl) ⟨1690127, by rfl⟩ : syracuseStep 2253503 = 3380255) B3380255
theorem B3380261 : Blo 2253435 3380261 := bbase (se 4 (by rfl) ⟨316899, by rfl⟩ : syracuseStep 3380261 = 633799) (by norm_num)
theorem B2253507 : Blo 2253435 2253507 := bstep (se 1 (by rfl) ⟨1690130, by rfl⟩ : syracuseStep 2253507 = 3380261) B3380261
theorem B2852101 : Blo 2253435 2852101 := bbase (se 4 (by rfl) ⟨267384, by rfl⟩ : syracuseStep 2852101 = 534769) (by norm_num)
theorem B3802801 : Blo 2253435 3802801 := bstep (se 2 (by rfl) ⟨1426050, by rfl⟩ : syracuseStep 3802801 = 2852101) B2852101
theorem B5070401 : Blo 2253435 5070401 := bstep (se 2 (by rfl) ⟨1901400, by rfl⟩ : syracuseStep 5070401 = 3802801) B3802801
theorem B3380267 : Blo 2253435 3380267 := bstep (se 1 (by rfl) ⟨2535200, by rfl⟩ : syracuseStep 3380267 = 5070401) B5070401
theorem B2253511 : Blo 2253435 2253511 := bstep (se 1 (by rfl) ⟨1690133, by rfl⟩ : syracuseStep 2253511 = 3380267) B3380267
theorem B2535205 : Blo 2253435 2535205 := bbase (se 4 (by rfl) ⟨237675, by rfl⟩ : syracuseStep 2535205 = 475351) (by norm_num)
theorem B3380273 : Blo 2253435 3380273 := bstep (se 2 (by rfl) ⟨1267602, by rfl⟩ : syracuseStep 3380273 = 2535205) B2535205
theorem B2253515 : Blo 2253435 2253515 := bstep (se 1 (by rfl) ⟨1690136, by rfl⟩ : syracuseStep 2253515 = 3380273) B3380273
theorem B9625877 : Blo 2253435 9625877 := bbase (se 6 (by rfl) ⟨225606, by rfl⟩ : syracuseStep 9625877 = 451213) (by norm_num)
theorem B6417251 : Blo 2253435 6417251 := bstep (se 1 (by rfl) ⟨4812938, by rfl⟩ : syracuseStep 6417251 = 9625877) B9625877
theorem B4278167 : Blo 2253435 4278167 := bstep (se 1 (by rfl) ⟨3208625, by rfl⟩ : syracuseStep 4278167 = 6417251) B6417251
theorem B2852111 : Blo 2253435 2852111 := bstep (se 1 (by rfl) ⟨2139083, by rfl⟩ : syracuseStep 2852111 = 4278167) B4278167
theorem B7605629 : Blo 2253435 7605629 := bstep (se 3 (by rfl) ⟨1426055, by rfl⟩ : syracuseStep 7605629 = 2852111) B2852111
theorem B5070419 : Blo 2253435 5070419 := bstep (se 1 (by rfl) ⟨3802814, by rfl⟩ : syracuseStep 5070419 = 7605629) B7605629
theorem B3380279 : Blo 2253435 3380279 := bstep (se 1 (by rfl) ⟨2535209, by rfl⟩ : syracuseStep 3380279 = 5070419) B5070419
theorem B2253519 : Blo 2253435 2253519 := bstep (se 1 (by rfl) ⟨1690139, by rfl⟩ : syracuseStep 2253519 = 3380279) B3380279
theorem B3380285 : Blo 2253435 3380285 := bbase (se 3 (by rfl) ⟨633803, by rfl⟩ : syracuseStep 3380285 = 1267607) (by norm_num)
theorem B2253523 : Blo 2253435 2253523 := bstep (se 1 (by rfl) ⟨1690142, by rfl⟩ : syracuseStep 2253523 = 3380285) B3380285
theorem B5070437 : Blo 2253435 5070437 := bbase (se 4 (by rfl) ⟨475353, by rfl⟩ : syracuseStep 5070437 = 950707) (by norm_num)
theorem B3380291 : Blo 2253435 3380291 := bstep (se 1 (by rfl) ⟨2535218, by rfl⟩ : syracuseStep 3380291 = 5070437) B5070437
theorem B2253527 : Blo 2253435 2253527 := bstep (se 1 (by rfl) ⟨1690145, by rfl⟩ : syracuseStep 2253527 = 3380291) B3380291
theorem B5704253 : Blo 2253435 5704253 := bbase (se 3 (by rfl) ⟨1069547, by rfl⟩ : syracuseStep 5704253 = 2139095) (by norm_num)
theorem B3802835 : Blo 2253435 3802835 := bstep (se 1 (by rfl) ⟨2852126, by rfl⟩ : syracuseStep 3802835 = 5704253) B5704253
theorem B2535223 : Blo 2253435 2535223 := bstep (se 1 (by rfl) ⟨1901417, by rfl⟩ : syracuseStep 2535223 = 3802835) B3802835
theorem B3380297 : Blo 2253435 3380297 := bstep (se 2 (by rfl) ⟨1267611, by rfl⟩ : syracuseStep 3380297 = 2535223) B2535223
theorem B2253531 : Blo 2253435 2253531 := bstep (se 1 (by rfl) ⟨1690148, by rfl⟩ : syracuseStep 2253531 = 3380297) B3380297
theorem B4278197 : Blo 2253435 4278197 := bbase (se 5 (by rfl) ⟨200540, by rfl⟩ : syracuseStep 4278197 = 401081) (by norm_num)
theorem B11408525 : Blo 2253435 11408525 := bstep (se 3 (by rfl) ⟨2139098, by rfl⟩ : syracuseStep 11408525 = 4278197) B4278197
theorem B7605683 : Blo 2253435 7605683 := bstep (se 1 (by rfl) ⟨5704262, by rfl⟩ : syracuseStep 7605683 = 11408525) B11408525
theorem B5070455 : Blo 2253435 5070455 := bstep (se 1 (by rfl) ⟨3802841, by rfl⟩ : syracuseStep 5070455 = 7605683) B7605683
theorem B3380303 : Blo 2253435 3380303 := bstep (se 1 (by rfl) ⟨2535227, by rfl⟩ : syracuseStep 3380303 = 5070455) B5070455
theorem B2253535 : Blo 2253435 2253535 := bstep (se 1 (by rfl) ⟨1690151, by rfl⟩ : syracuseStep 2253535 = 3380303) B3380303
theorem B3380309 : Blo 2253435 3380309 := bbase (se 8 (by rfl) ⟨19806, by rfl⟩ : syracuseStep 3380309 = 39613) (by norm_num)
theorem B2253539 : Blo 2253435 2253539 := bstep (se 1 (by rfl) ⟨1690154, by rfl⟩ : syracuseStep 2253539 = 3380309) B3380309
theorem B2604889 : Blo 2253435 2604889 := bbase (se 2 (by rfl) ⟨976833, by rfl⟩ : syracuseStep 2604889 = 1953667) (by norm_num)
theorem B13892741 : Blo 2253435 13892741 := bstep (se 4 (by rfl) ⟨1302444, by rfl⟩ : syracuseStep 13892741 = 2604889) B2604889
theorem B9261827 : Blo 2253435 9261827 := bstep (se 1 (by rfl) ⟨6946370, by rfl⟩ : syracuseStep 9261827 = 13892741) B13892741
theorem B6174551 : Blo 2253435 6174551 := bstep (se 1 (by rfl) ⟨4630913, by rfl⟩ : syracuseStep 6174551 = 9261827) B9261827
theorem B4116367 : Blo 2253435 4116367 := bstep (se 1 (by rfl) ⟨3087275, by rfl⟩ : syracuseStep 4116367 = 6174551) B6174551
theorem B5488489 : Blo 2253435 5488489 := bstep (se 2 (by rfl) ⟨2058183, by rfl⟩ : syracuseStep 5488489 = 4116367) B4116367
theorem B7317985 : Blo 2253435 7317985 := bstep (se 2 (by rfl) ⟨2744244, by rfl⟩ : syracuseStep 7317985 = 5488489) B5488489
theorem B9757313 : Blo 2253435 9757313 := bstep (se 2 (by rfl) ⟨3658992, by rfl⟩ : syracuseStep 9757313 = 7317985) B7317985
theorem B6504875 : Blo 2253435 6504875 := bstep (se 1 (by rfl) ⟨4878656, by rfl⟩ : syracuseStep 6504875 = 9757313) B9757313
theorem B4336583 : Blo 2253435 4336583 := bstep (se 1 (by rfl) ⟨3252437, by rfl⟩ : syracuseStep 4336583 = 6504875) B6504875
theorem B11564221 : Blo 2253435 11564221 := bstep (se 3 (by rfl) ⟨2168291, by rfl⟩ : syracuseStep 11564221 = 4336583) B4336583
theorem B15418961 : Blo 2253435 15418961 := bstep (se 2 (by rfl) ⟨5782110, by rfl⟩ : syracuseStep 15418961 = 11564221) B11564221
theorem B10279307 : Blo 2253435 10279307 := bstep (se 1 (by rfl) ⟨7709480, by rfl⟩ : syracuseStep 10279307 = 15418961) B15418961
theorem B6852871 : Blo 2253435 6852871 := bstep (se 1 (by rfl) ⟨5139653, by rfl⟩ : syracuseStep 6852871 = 10279307) B10279307
theorem B9137161 : Blo 2253435 9137161 := bstep (se 2 (by rfl) ⟨3426435, by rfl⟩ : syracuseStep 9137161 = 6852871) B6852871
theorem B12182881 : Blo 2253435 12182881 := bstep (se 2 (by rfl) ⟨4568580, by rfl⟩ : syracuseStep 12182881 = 9137161) B9137161
theorem B16243841 : Blo 2253435 16243841 := bstep (se 2 (by rfl) ⟨6091440, by rfl⟩ : syracuseStep 16243841 = 12182881) B12182881
theorem B10829227 : Blo 2253435 10829227 := bstep (se 1 (by rfl) ⟨8121920, by rfl⟩ : syracuseStep 10829227 = 16243841) B16243841
theorem B14438969 : Blo 2253435 14438969 := bstep (se 2 (by rfl) ⟨5414613, by rfl⟩ : syracuseStep 14438969 = 10829227) B10829227
theorem B9625979 : Blo 2253435 9625979 := bstep (se 1 (by rfl) ⟨7219484, by rfl⟩ : syracuseStep 9625979 = 14438969) B14438969
theorem B6417319 : Blo 2253435 6417319 := bstep (se 1 (by rfl) ⟨4812989, by rfl⟩ : syracuseStep 6417319 = 9625979) B9625979
theorem B8556425 : Blo 2253435 8556425 := bstep (se 2 (by rfl) ⟨3208659, by rfl⟩ : syracuseStep 8556425 = 6417319) B6417319
theorem B5704283 : Blo 2253435 5704283 := bstep (se 1 (by rfl) ⟨4278212, by rfl⟩ : syracuseStep 5704283 = 8556425) B8556425
theorem B3802855 : Blo 2253435 3802855 := bstep (se 1 (by rfl) ⟨2852141, by rfl⟩ : syracuseStep 3802855 = 5704283) B5704283
theorem B5070473 : Blo 2253435 5070473 := bstep (se 2 (by rfl) ⟨1901427, by rfl⟩ : syracuseStep 5070473 = 3802855) B3802855
theorem B3380315 : Blo 2253435 3380315 := bstep (se 1 (by rfl) ⟨2535236, by rfl⟩ : syracuseStep 3380315 = 5070473) B5070473
theorem B2253543 : Blo 2253435 2253543 := bstep (se 1 (by rfl) ⟨1690157, by rfl⟩ : syracuseStep 2253543 = 3380315) B3380315
theorem B2535241 : Blo 2253435 2535241 := bbase (se 2 (by rfl) ⟨950715, by rfl⟩ : syracuseStep 2535241 = 1901431) (by norm_num)
theorem B3380321 : Blo 2253435 3380321 := bstep (se 2 (by rfl) ⟨1267620, by rfl⟩ : syracuseStep 3380321 = 2535241) B2535241
theorem B2253547 : Blo 2253435 2253547 := bstep (se 1 (by rfl) ⟨1690160, by rfl⟩ : syracuseStep 2253547 = 3380321) B3380321
theorem B11564261 : Blo 2253435 11564261 := bbase (se 4 (by rfl) ⟨1084149, by rfl⟩ : syracuseStep 11564261 = 2168299) (by norm_num)
theorem B7709507 : Blo 2253435 7709507 := bstep (se 1 (by rfl) ⟨5782130, by rfl⟩ : syracuseStep 7709507 = 11564261) B11564261
theorem B5139671 : Blo 2253435 5139671 := bstep (se 1 (by rfl) ⟨3854753, by rfl⟩ : syracuseStep 5139671 = 7709507) B7709507
theorem B13705789 : Blo 2253435 13705789 := bstep (se 3 (by rfl) ⟨2569835, by rfl⟩ : syracuseStep 13705789 = 5139671) B5139671
theorem B18274385 : Blo 2253435 18274385 := bstep (se 2 (by rfl) ⟨6852894, by rfl⟩ : syracuseStep 18274385 = 13705789) B13705789
theorem B12182923 : Blo 2253435 12182923 := bstep (se 1 (by rfl) ⟨9137192, by rfl⟩ : syracuseStep 12182923 = 18274385) B18274385
theorem B16243897 : Blo 2253435 16243897 := bstep (se 2 (by rfl) ⟨6091461, by rfl⟩ : syracuseStep 16243897 = 12182923) B12182923
theorem B21658529 : Blo 2253435 21658529 := bstep (se 2 (by rfl) ⟨8121948, by rfl⟩ : syracuseStep 21658529 = 16243897) B16243897
theorem B14439019 : Blo 2253435 14439019 := bstep (se 1 (by rfl) ⟨10829264, by rfl⟩ : syracuseStep 14439019 = 21658529) B21658529
theorem B19252025 : Blo 2253435 19252025 := bstep (se 2 (by rfl) ⟨7219509, by rfl⟩ : syracuseStep 19252025 = 14439019) B14439019
theorem B12834683 : Blo 2253435 12834683 := bstep (se 1 (by rfl) ⟨9626012, by rfl⟩ : syracuseStep 12834683 = 19252025) B19252025
theorem B8556455 : Blo 2253435 8556455 := bstep (se 1 (by rfl) ⟨6417341, by rfl⟩ : syracuseStep 8556455 = 12834683) B12834683
theorem B5704303 : Blo 2253435 5704303 := bstep (se 1 (by rfl) ⟨4278227, by rfl⟩ : syracuseStep 5704303 = 8556455) B8556455
theorem B7605737 : Blo 2253435 7605737 := bstep (se 2 (by rfl) ⟨2852151, by rfl⟩ : syracuseStep 7605737 = 5704303) B5704303
theorem B5070491 : Blo 2253435 5070491 := bstep (se 1 (by rfl) ⟨3802868, by rfl⟩ : syracuseStep 5070491 = 7605737) B7605737
theorem B3380327 : Blo 2253435 3380327 := bstep (se 1 (by rfl) ⟨2535245, by rfl⟩ : syracuseStep 3380327 = 5070491) B5070491
theorem B2253551 : Blo 2253435 2253551 := bstep (se 1 (by rfl) ⟨1690163, by rfl⟩ : syracuseStep 2253551 = 3380327) B3380327
theorem B3380333 : Blo 2253435 3380333 := bbase (se 3 (by rfl) ⟨633812, by rfl⟩ : syracuseStep 3380333 = 1267625) (by norm_num)
theorem B2253555 : Blo 2253435 2253555 := bstep (se 1 (by rfl) ⟨1690166, by rfl⟩ : syracuseStep 2253555 = 3380333) B3380333
theorem B5070509 : Blo 2253435 5070509 := bbase (se 3 (by rfl) ⟨950720, by rfl⟩ : syracuseStep 5070509 = 1901441) (by norm_num)
theorem B3380339 : Blo 2253435 3380339 := bstep (se 1 (by rfl) ⟨2535254, by rfl⟩ : syracuseStep 3380339 = 5070509) B5070509
theorem B2253559 : Blo 2253435 2253559 := bstep (se 1 (by rfl) ⟨1690169, by rfl⟩ : syracuseStep 2253559 = 3380339) B3380339
theorem B5139701 : Blo 2253435 5139701 := bbase (se 5 (by rfl) ⟨240923, by rfl⟩ : syracuseStep 5139701 = 481847) (by norm_num)
theorem B3426467 : Blo 2253435 3426467 := bstep (se 1 (by rfl) ⟨2569850, by rfl⟩ : syracuseStep 3426467 = 5139701) B5139701
theorem B9137245 : Blo 2253435 9137245 := bstep (se 3 (by rfl) ⟨1713233, by rfl⟩ : syracuseStep 9137245 = 3426467) B3426467
theorem B12182993 : Blo 2253435 12182993 := bstep (se 2 (by rfl) ⟨4568622, by rfl⟩ : syracuseStep 12182993 = 9137245) B9137245
theorem B8121995 : Blo 2253435 8121995 := bstep (se 1 (by rfl) ⟨6091496, by rfl⟩ : syracuseStep 8121995 = 12182993) B12182993
theorem B5414663 : Blo 2253435 5414663 := bstep (se 1 (by rfl) ⟨4060997, by rfl⟩ : syracuseStep 5414663 = 8121995) B8121995
theorem B3609775 : Blo 2253435 3609775 := bstep (se 1 (by rfl) ⟨2707331, by rfl⟩ : syracuseStep 3609775 = 5414663) B5414663
theorem B4813033 : Blo 2253435 4813033 := bstep (se 2 (by rfl) ⟨1804887, by rfl⟩ : syracuseStep 4813033 = 3609775) B3609775
theorem B6417377 : Blo 2253435 6417377 := bstep (se 2 (by rfl) ⟨2406516, by rfl⟩ : syracuseStep 6417377 = 4813033) B4813033
theorem B4278251 : Blo 2253435 4278251 := bstep (se 1 (by rfl) ⟨3208688, by rfl⟩ : syracuseStep 4278251 = 6417377) B6417377
theorem B2852167 : Blo 2253435 2852167 := bstep (se 1 (by rfl) ⟨2139125, by rfl⟩ : syracuseStep 2852167 = 4278251) B4278251
theorem B3802889 : Blo 2253435 3802889 := bstep (se 2 (by rfl) ⟨1426083, by rfl⟩ : syracuseStep 3802889 = 2852167) B2852167
theorem B2535259 : Blo 2253435 2535259 := bstep (se 1 (by rfl) ⟨1901444, by rfl⟩ : syracuseStep 2535259 = 3802889) B3802889
theorem B3380345 : Blo 2253435 3380345 := bstep (se 2 (by rfl) ⟨1267629, by rfl⟩ : syracuseStep 3380345 = 2535259) B2535259
theorem B2253563 : Blo 2253435 2253563 := bstep (se 1 (by rfl) ⟨1690172, by rfl⟩ : syracuseStep 2253563 = 3380345) B3380345
theorem B4172573 : Blo 2253435 4172573 := bbase (se 3 (by rfl) ⟨782357, by rfl⟩ : syracuseStep 4172573 = 1564715) (by norm_num)
theorem B2781715 : Blo 2253435 2781715 := bstep (se 1 (by rfl) ⟨2086286, by rfl⟩ : syracuseStep 2781715 = 4172573) B4172573
theorem B3708953 : Blo 2253435 3708953 := bstep (se 2 (by rfl) ⟨1390857, by rfl⟩ : syracuseStep 3708953 = 2781715) B2781715
theorem B2472635 : Blo 2253435 2472635 := bstep (se 1 (by rfl) ⟨1854476, by rfl⟩ : syracuseStep 2472635 = 3708953) B3708953
theorem B6593693 : Blo 2253435 6593693 := bstep (se 3 (by rfl) ⟨1236317, by rfl⟩ : syracuseStep 6593693 = 2472635) B2472635
theorem B70332725 : Blo 2253435 70332725 := bstep (se 5 (by rfl) ⟨3296846, by rfl⟩ : syracuseStep 70332725 = 6593693) B6593693
theorem B46888483 : Blo 2253435 46888483 := bstep (se 1 (by rfl) ⟨35166362, by rfl⟩ : syracuseStep 46888483 = 70332725) B70332725
theorem B62517977 : Blo 2253435 62517977 := bstep (se 2 (by rfl) ⟨23444241, by rfl⟩ : syracuseStep 62517977 = 46888483) B46888483
theorem B41678651 : Blo 2253435 41678651 := bstep (se 1 (by rfl) ⟨31258988, by rfl⟩ : syracuseStep 41678651 = 62517977) B62517977
theorem B27785767 : Blo 2253435 27785767 := bstep (se 1 (by rfl) ⟨20839325, by rfl⟩ : syracuseStep 27785767 = 41678651) B41678651
theorem B37047689 : Blo 2253435 37047689 := bstep (se 2 (by rfl) ⟨13892883, by rfl⟩ : syracuseStep 37047689 = 27785767) B27785767
theorem B24698459 : Blo 2253435 24698459 := bstep (se 1 (by rfl) ⟨18523844, by rfl⟩ : syracuseStep 24698459 = 37047689) B37047689
theorem B16465639 : Blo 2253435 16465639 := bstep (se 1 (by rfl) ⟨12349229, by rfl⟩ : syracuseStep 16465639 = 24698459) B24698459
theorem B21954185 : Blo 2253435 21954185 := bstep (se 2 (by rfl) ⟨8232819, by rfl⟩ : syracuseStep 21954185 = 16465639) B16465639
theorem B14636123 : Blo 2253435 14636123 := bstep (se 1 (by rfl) ⟨10977092, by rfl⟩ : syracuseStep 14636123 = 21954185) B21954185
theorem B9757415 : Blo 2253435 9757415 := bstep (se 1 (by rfl) ⟨7318061, by rfl⟩ : syracuseStep 9757415 = 14636123) B14636123
theorem B6504943 : Blo 2253435 6504943 := bstep (se 1 (by rfl) ⟨4878707, by rfl⟩ : syracuseStep 6504943 = 9757415) B9757415
theorem B8673257 : Blo 2253435 8673257 := bstep (se 2 (by rfl) ⟨3252471, by rfl⟩ : syracuseStep 8673257 = 6504943) B6504943
theorem B5782171 : Blo 2253435 5782171 := bstep (se 1 (by rfl) ⟨4336628, by rfl⟩ : syracuseStep 5782171 = 8673257) B8673257
theorem B7709561 : Blo 2253435 7709561 := bstep (se 2 (by rfl) ⟨2891085, by rfl⟩ : syracuseStep 7709561 = 5782171) B5782171
theorem B5139707 : Blo 2253435 5139707 := bstep (se 1 (by rfl) ⟨3854780, by rfl⟩ : syracuseStep 5139707 = 7709561) B7709561
theorem B13705885 : Blo 2253435 13705885 := bstep (se 3 (by rfl) ⟨2569853, by rfl⟩ : syracuseStep 13705885 = 5139707) B5139707
theorem B18274513 : Blo 2253435 18274513 := bstep (se 2 (by rfl) ⟨6852942, by rfl⟩ : syracuseStep 18274513 = 13705885) B13705885
theorem B24366017 : Blo 2253435 24366017 := bstep (se 2 (by rfl) ⟨9137256, by rfl⟩ : syracuseStep 24366017 = 18274513) B18274513
theorem B16244011 : Blo 2253435 16244011 := bstep (se 1 (by rfl) ⟨12183008, by rfl⟩ : syracuseStep 16244011 = 24366017) B24366017
theorem B21658681 : Blo 2253435 21658681 := bstep (se 2 (by rfl) ⟨8122005, by rfl⟩ : syracuseStep 21658681 = 16244011) B16244011
theorem B28878241 : Blo 2253435 28878241 := bstep (se 2 (by rfl) ⟨10829340, by rfl⟩ : syracuseStep 28878241 = 21658681) B21658681
theorem B38504321 : Blo 2253435 38504321 := bstep (se 2 (by rfl) ⟨14439120, by rfl⟩ : syracuseStep 38504321 = 28878241) B28878241
theorem B25669547 : Blo 2253435 25669547 := bstep (se 1 (by rfl) ⟨19252160, by rfl⟩ : syracuseStep 25669547 = 38504321) B38504321
theorem B17113031 : Blo 2253435 17113031 := bstep (se 1 (by rfl) ⟨12834773, by rfl⟩ : syracuseStep 17113031 = 25669547) B25669547
theorem B11408687 : Blo 2253435 11408687 := bstep (se 1 (by rfl) ⟨8556515, by rfl⟩ : syracuseStep 11408687 = 17113031) B17113031
theorem B7605791 : Blo 2253435 7605791 := bstep (se 1 (by rfl) ⟨5704343, by rfl⟩ : syracuseStep 7605791 = 11408687) B11408687
theorem B5070527 : Blo 2253435 5070527 := bstep (se 1 (by rfl) ⟨3802895, by rfl⟩ : syracuseStep 5070527 = 7605791) B7605791
theorem B3380351 : Blo 2253435 3380351 := bstep (se 1 (by rfl) ⟨2535263, by rfl⟩ : syracuseStep 3380351 = 5070527) B5070527
theorem B2253567 : Blo 2253435 2253567 := bstep (se 1 (by rfl) ⟨1690175, by rfl⟩ : syracuseStep 2253567 = 3380351) B3380351
theorem B3380357 : Blo 2253435 3380357 := bbase (se 4 (by rfl) ⟨316908, by rfl⟩ : syracuseStep 3380357 = 633817) (by norm_num)
theorem B2253571 : Blo 2253435 2253571 := bstep (se 1 (by rfl) ⟨1690178, by rfl⟩ : syracuseStep 2253571 = 3380357) B3380357
theorem B3802909 : Blo 2253435 3802909 := bbase (se 3 (by rfl) ⟨713045, by rfl⟩ : syracuseStep 3802909 = 1426091) (by norm_num)
theorem B5070545 : Blo 2253435 5070545 := bstep (se 2 (by rfl) ⟨1901454, by rfl⟩ : syracuseStep 5070545 = 3802909) B3802909
theorem B3380363 : Blo 2253435 3380363 := bstep (se 1 (by rfl) ⟨2535272, by rfl⟩ : syracuseStep 3380363 = 5070545) B5070545
theorem B2253575 : Blo 2253435 2253575 := bstep (se 1 (by rfl) ⟨1690181, by rfl⟩ : syracuseStep 2253575 = 3380363) B3380363
theorem B2535277 : Blo 2253435 2535277 := bbase (se 3 (by rfl) ⟨475364, by rfl⟩ : syracuseStep 2535277 = 950729) (by norm_num)
theorem B3380369 : Blo 2253435 3380369 := bstep (se 2 (by rfl) ⟨1267638, by rfl⟩ : syracuseStep 3380369 = 2535277) B2535277
theorem B2253579 : Blo 2253435 2253579 := bstep (se 1 (by rfl) ⟨1690184, by rfl⟩ : syracuseStep 2253579 = 3380369) B3380369
theorem B7605845 : Blo 2253435 7605845 := bbase (se 8 (by rfl) ⟨44565, by rfl⟩ : syracuseStep 7605845 = 89131) (by norm_num)
theorem B5070563 : Blo 2253435 5070563 := bstep (se 1 (by rfl) ⟨3802922, by rfl⟩ : syracuseStep 5070563 = 7605845) B7605845
theorem B3380375 : Blo 2253435 3380375 := bstep (se 1 (by rfl) ⟨2535281, by rfl⟩ : syracuseStep 3380375 = 5070563) B5070563
theorem B2253583 : Blo 2253435 2253583 := bstep (se 1 (by rfl) ⟨1690187, by rfl⟩ : syracuseStep 2253583 = 3380375) B3380375
theorem B3380381 : Blo 2253435 3380381 := bbase (se 3 (by rfl) ⟨633821, by rfl⟩ : syracuseStep 3380381 = 1267643) (by norm_num)
theorem B2253587 : Blo 2253435 2253587 := bstep (se 1 (by rfl) ⟨1690190, by rfl⟩ : syracuseStep 2253587 = 3380381) B3380381
theorem B5070581 : Blo 2253435 5070581 := bbase (se 5 (by rfl) ⟨237683, by rfl⟩ : syracuseStep 5070581 = 475367) (by norm_num)
theorem B3380387 : Blo 2253435 3380387 := bstep (se 1 (by rfl) ⟨2535290, by rfl⟩ : syracuseStep 3380387 = 5070581) B5070581
theorem B2253591 : Blo 2253435 2253591 := bstep (se 1 (by rfl) ⟨1690193, by rfl⟩ : syracuseStep 2253591 = 3380387) B3380387
theorem B10829477 : Blo 2253435 10829477 := bbase (se 4 (by rfl) ⟨1015263, by rfl⟩ : syracuseStep 10829477 = 2030527) (by norm_num)
theorem B28878605 : Blo 2253435 28878605 := bstep (se 3 (by rfl) ⟨5414738, by rfl⟩ : syracuseStep 28878605 = 10829477) B10829477
theorem B19252403 : Blo 2253435 19252403 := bstep (se 1 (by rfl) ⟨14439302, by rfl⟩ : syracuseStep 19252403 = 28878605) B28878605
theorem B12834935 : Blo 2253435 12834935 := bstep (se 1 (by rfl) ⟨9626201, by rfl⟩ : syracuseStep 12834935 = 19252403) B19252403
theorem B8556623 : Blo 2253435 8556623 := bstep (se 1 (by rfl) ⟨6417467, by rfl⟩ : syracuseStep 8556623 = 12834935) B12834935
theorem B5704415 : Blo 2253435 5704415 := bstep (se 1 (by rfl) ⟨4278311, by rfl⟩ : syracuseStep 5704415 = 8556623) B8556623
theorem B3802943 : Blo 2253435 3802943 := bstep (se 1 (by rfl) ⟨2852207, by rfl⟩ : syracuseStep 3802943 = 5704415) B5704415
theorem B2535295 : Blo 2253435 2535295 := bstep (se 1 (by rfl) ⟨1901471, by rfl⟩ : syracuseStep 2535295 = 3802943) B3802943
theorem B3380393 : Blo 2253435 3380393 := bstep (se 2 (by rfl) ⟨1267647, by rfl⟩ : syracuseStep 3380393 = 2535295) B2535295
theorem B2253595 : Blo 2253435 2253595 := bstep (se 1 (by rfl) ⟨1690196, by rfl⟩ : syracuseStep 2253595 = 3380393) B3380393
theorem B4813109 : Blo 2253435 4813109 := bbase (se 5 (by rfl) ⟨225614, by rfl⟩ : syracuseStep 4813109 = 451229) (by norm_num)
theorem B3208739 : Blo 2253435 3208739 := bstep (se 1 (by rfl) ⟨2406554, by rfl⟩ : syracuseStep 3208739 = 4813109) B4813109
theorem B8556637 : Blo 2253435 8556637 := bstep (se 3 (by rfl) ⟨1604369, by rfl⟩ : syracuseStep 8556637 = 3208739) B3208739
theorem B11408849 : Blo 2253435 11408849 := bstep (se 2 (by rfl) ⟨4278318, by rfl⟩ : syracuseStep 11408849 = 8556637) B8556637
theorem B7605899 : Blo 2253435 7605899 := bstep (se 1 (by rfl) ⟨5704424, by rfl⟩ : syracuseStep 7605899 = 11408849) B11408849
theorem B5070599 : Blo 2253435 5070599 := bstep (se 1 (by rfl) ⟨3802949, by rfl⟩ : syracuseStep 5070599 = 7605899) B7605899
theorem B3380399 : Blo 2253435 3380399 := bstep (se 1 (by rfl) ⟨2535299, by rfl⟩ : syracuseStep 3380399 = 5070599) B5070599
theorem B2253599 : Blo 2253435 2253599 := bstep (se 1 (by rfl) ⟨1690199, by rfl⟩ : syracuseStep 2253599 = 3380399) B3380399
theorem B3380405 : Blo 2253435 3380405 := bbase (se 5 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 3380405 = 316913) (by norm_num)
theorem B2253603 : Blo 2253435 2253603 := bstep (se 1 (by rfl) ⟨1690202, by rfl⟩ : syracuseStep 2253603 = 3380405) B3380405
theorem B5704445 : Blo 2253435 5704445 := bbase (se 3 (by rfl) ⟨1069583, by rfl⟩ : syracuseStep 5704445 = 2139167) (by norm_num)
theorem B3802963 : Blo 2253435 3802963 := bstep (se 1 (by rfl) ⟨2852222, by rfl⟩ : syracuseStep 3802963 = 5704445) B5704445
theorem B5070617 : Blo 2253435 5070617 := bstep (se 2 (by rfl) ⟨1901481, by rfl⟩ : syracuseStep 5070617 = 3802963) B3802963
theorem B3380411 : Blo 2253435 3380411 := bstep (se 1 (by rfl) ⟨2535308, by rfl⟩ : syracuseStep 3380411 = 5070617) B5070617
theorem B2253607 : Blo 2253435 2253607 := bstep (se 1 (by rfl) ⟨1690205, by rfl⟩ : syracuseStep 2253607 = 3380411) B3380411
theorem B2535313 : Blo 2253435 2535313 := bbase (se 2 (by rfl) ⟨950742, by rfl⟩ : syracuseStep 2535313 = 1901485) (by norm_num)
theorem B3380417 : Blo 2253435 3380417 := bstep (se 2 (by rfl) ⟨1267656, by rfl⟩ : syracuseStep 3380417 = 2535313) B2535313
theorem B2253611 : Blo 2253435 2253611 := bstep (se 1 (by rfl) ⟨1690208, by rfl⟩ : syracuseStep 2253611 = 3380417) B3380417
theorem B4278349 : Blo 2253435 4278349 := bbase (se 3 (by rfl) ⟨802190, by rfl⟩ : syracuseStep 4278349 = 1604381) (by norm_num)
theorem B5704465 : Blo 2253435 5704465 := bstep (se 2 (by rfl) ⟨2139174, by rfl⟩ : syracuseStep 5704465 = 4278349) B4278349
theorem B7605953 : Blo 2253435 7605953 := bstep (se 2 (by rfl) ⟨2852232, by rfl⟩ : syracuseStep 7605953 = 5704465) B5704465
theorem B5070635 : Blo 2253435 5070635 := bstep (se 1 (by rfl) ⟨3802976, by rfl⟩ : syracuseStep 5070635 = 7605953) B7605953
theorem B3380423 : Blo 2253435 3380423 := bstep (se 1 (by rfl) ⟨2535317, by rfl⟩ : syracuseStep 3380423 = 5070635) B5070635
theorem B2253615 : Blo 2253435 2253615 := bstep (se 1 (by rfl) ⟨1690211, by rfl⟩ : syracuseStep 2253615 = 3380423) B3380423
theorem B3380429 : Blo 2253435 3380429 := bbase (se 3 (by rfl) ⟨633830, by rfl⟩ : syracuseStep 3380429 = 1267661) (by norm_num)
theorem B2253619 : Blo 2253435 2253619 := bstep (se 1 (by rfl) ⟨1690214, by rfl⟩ : syracuseStep 2253619 = 3380429) B3380429
theorem B5070653 : Blo 2253435 5070653 := bbase (se 3 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 5070653 = 1901495) (by norm_num)
theorem B3380435 : Blo 2253435 3380435 := bstep (se 1 (by rfl) ⟨2535326, by rfl⟩ : syracuseStep 3380435 = 5070653) B5070653
theorem B2253623 : Blo 2253435 2253623 := bstep (se 1 (by rfl) ⟨1690217, by rfl⟩ : syracuseStep 2253623 = 3380435) B3380435
theorem B3802997 : Blo 2253435 3802997 := bbase (se 5 (by rfl) ⟨178265, by rfl⟩ : syracuseStep 3802997 = 356531) (by norm_num)
theorem B2535331 : Blo 2253435 2535331 := bstep (se 1 (by rfl) ⟨1901498, by rfl⟩ : syracuseStep 2535331 = 3802997) B3802997
theorem B3380441 : Blo 2253435 3380441 := bstep (se 2 (by rfl) ⟨1267665, by rfl⟩ : syracuseStep 3380441 = 2535331) B2535331
theorem B2253627 : Blo 2253435 2253627 := bstep (se 1 (by rfl) ⟨1690220, by rfl⟩ : syracuseStep 2253627 = 3380441) B3380441
theorem B3296941 : Blo 2253435 3296941 := bbase (se 3 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 3296941 = 1236353) (by norm_num)
theorem B17583685 : Blo 2253435 17583685 := bstep (se 4 (by rfl) ⟨1648470, by rfl⟩ : syracuseStep 17583685 = 3296941) B3296941
theorem B93779653 : Blo 2253435 93779653 := bstep (se 4 (by rfl) ⟨8791842, by rfl⟩ : syracuseStep 93779653 = 17583685) B17583685
theorem B125039537 : Blo 2253435 125039537 := bstep (se 2 (by rfl) ⟨46889826, by rfl⟩ : syracuseStep 125039537 = 93779653) B93779653
theorem B83359691 : Blo 2253435 83359691 := bstep (se 1 (by rfl) ⟨62519768, by rfl⟩ : syracuseStep 83359691 = 125039537) B125039537
theorem B55573127 : Blo 2253435 55573127 := bstep (se 1 (by rfl) ⟨41679845, by rfl⟩ : syracuseStep 55573127 = 83359691) B83359691
theorem B37048751 : Blo 2253435 37048751 := bstep (se 1 (by rfl) ⟨27786563, by rfl⟩ : syracuseStep 37048751 = 55573127) B55573127
theorem B24699167 : Blo 2253435 24699167 := bstep (se 1 (by rfl) ⟨18524375, by rfl⟩ : syracuseStep 24699167 = 37048751) B37048751
theorem B16466111 : Blo 2253435 16466111 := bstep (se 1 (by rfl) ⟨12349583, by rfl⟩ : syracuseStep 16466111 = 24699167) B24699167
theorem B10977407 : Blo 2253435 10977407 := bstep (se 1 (by rfl) ⟨8233055, by rfl⟩ : syracuseStep 10977407 = 16466111) B16466111
theorem B7318271 : Blo 2253435 7318271 := bstep (se 1 (by rfl) ⟨5488703, by rfl⟩ : syracuseStep 7318271 = 10977407) B10977407
theorem B4878847 : Blo 2253435 4878847 := bstep (se 1 (by rfl) ⟨3659135, by rfl⟩ : syracuseStep 4878847 = 7318271) B7318271
theorem B6505129 : Blo 2253435 6505129 := bstep (se 2 (by rfl) ⟨2439423, by rfl⟩ : syracuseStep 6505129 = 4878847) B4878847
theorem B34694021 : Blo 2253435 34694021 := bstep (se 4 (by rfl) ⟨3252564, by rfl⟩ : syracuseStep 34694021 = 6505129) B6505129
theorem B23129347 : Blo 2253435 23129347 := bstep (se 1 (by rfl) ⟨17347010, by rfl⟩ : syracuseStep 23129347 = 34694021) B34694021
theorem B30839129 : Blo 2253435 30839129 := bstep (se 2 (by rfl) ⟨11564673, by rfl⟩ : syracuseStep 30839129 = 23129347) B23129347
theorem B20559419 : Blo 2253435 20559419 := bstep (se 1 (by rfl) ⟨15419564, by rfl⟩ : syracuseStep 20559419 = 30839129) B30839129
theorem B13706279 : Blo 2253435 13706279 := bstep (se 1 (by rfl) ⟨10279709, by rfl⟩ : syracuseStep 13706279 = 20559419) B20559419
theorem B9137519 : Blo 2253435 9137519 := bstep (se 1 (by rfl) ⟨6853139, by rfl⟩ : syracuseStep 9137519 = 13706279) B13706279
theorem B6091679 : Blo 2253435 6091679 := bstep (se 1 (by rfl) ⟨4568759, by rfl⟩ : syracuseStep 6091679 = 9137519) B9137519
theorem B4061119 : Blo 2253435 4061119 := bstep (se 1 (by rfl) ⟨3045839, by rfl⟩ : syracuseStep 4061119 = 6091679) B6091679
theorem B5414825 : Blo 2253435 5414825 := bstep (se 2 (by rfl) ⟨2030559, by rfl⟩ : syracuseStep 5414825 = 4061119) B4061119
theorem B3609883 : Blo 2253435 3609883 := bstep (se 1 (by rfl) ⟨2707412, by rfl⟩ : syracuseStep 3609883 = 5414825) B5414825
theorem B4813177 : Blo 2253435 4813177 := bstep (se 2 (by rfl) ⟨1804941, by rfl⟩ : syracuseStep 4813177 = 3609883) B3609883
theorem B6417569 : Blo 2253435 6417569 := bstep (se 2 (by rfl) ⟨2406588, by rfl⟩ : syracuseStep 6417569 = 4813177) B4813177
theorem B17113517 : Blo 2253435 17113517 := bstep (se 3 (by rfl) ⟨3208784, by rfl⟩ : syracuseStep 17113517 = 6417569) B6417569
theorem B11409011 : Blo 2253435 11409011 := bstep (se 1 (by rfl) ⟨8556758, by rfl⟩ : syracuseStep 11409011 = 17113517) B17113517
theorem B7606007 : Blo 2253435 7606007 := bstep (se 1 (by rfl) ⟨5704505, by rfl⟩ : syracuseStep 7606007 = 11409011) B11409011
theorem B5070671 : Blo 2253435 5070671 := bstep (se 1 (by rfl) ⟨3803003, by rfl⟩ : syracuseStep 5070671 = 7606007) B7606007
theorem B3380447 : Blo 2253435 3380447 := bstep (se 1 (by rfl) ⟨2535335, by rfl⟩ : syracuseStep 3380447 = 5070671) B5070671
theorem B2253631 : Blo 2253435 2253631 := bstep (se 1 (by rfl) ⟨1690223, by rfl⟩ : syracuseStep 2253631 = 3380447) B3380447
theorem B3380453 : Blo 2253435 3380453 := bbase (se 4 (by rfl) ⟨316917, by rfl⟩ : syracuseStep 3380453 = 633835) (by norm_num)
theorem B2253635 : Blo 2253435 2253635 := bstep (se 1 (by rfl) ⟨1690226, by rfl⟩ : syracuseStep 2253635 = 3380453) B3380453
theorem B5414845 : Blo 2253435 5414845 := bbase (se 3 (by rfl) ⟨1015283, by rfl⟩ : syracuseStep 5414845 = 2030567) (by norm_num)
theorem B7219793 : Blo 2253435 7219793 := bstep (se 2 (by rfl) ⟨2707422, by rfl⟩ : syracuseStep 7219793 = 5414845) B5414845
theorem B4813195 : Blo 2253435 4813195 := bstep (se 1 (by rfl) ⟨3609896, by rfl⟩ : syracuseStep 4813195 = 7219793) B7219793
theorem B6417593 : Blo 2253435 6417593 := bstep (se 2 (by rfl) ⟨2406597, by rfl⟩ : syracuseStep 6417593 = 4813195) B4813195
theorem B4278395 : Blo 2253435 4278395 := bstep (se 1 (by rfl) ⟨3208796, by rfl⟩ : syracuseStep 4278395 = 6417593) B6417593
theorem B2852263 : Blo 2253435 2852263 := bstep (se 1 (by rfl) ⟨2139197, by rfl⟩ : syracuseStep 2852263 = 4278395) B4278395
theorem B3803017 : Blo 2253435 3803017 := bstep (se 2 (by rfl) ⟨1426131, by rfl⟩ : syracuseStep 3803017 = 2852263) B2852263
theorem B5070689 : Blo 2253435 5070689 := bstep (se 2 (by rfl) ⟨1901508, by rfl⟩ : syracuseStep 5070689 = 3803017) B3803017
theorem B3380459 : Blo 2253435 3380459 := bstep (se 1 (by rfl) ⟨2535344, by rfl⟩ : syracuseStep 3380459 = 5070689) B5070689
theorem B2253639 : Blo 2253435 2253639 := bstep (se 1 (by rfl) ⟨1690229, by rfl⟩ : syracuseStep 2253639 = 3380459) B3380459
theorem B2535349 : Blo 2253435 2535349 := bbase (se 5 (by rfl) ⟨118844, by rfl⟩ : syracuseStep 2535349 = 237689) (by norm_num)
theorem B3380465 : Blo 2253435 3380465 := bstep (se 2 (by rfl) ⟨1267674, by rfl⟩ : syracuseStep 3380465 = 2535349) B2535349
theorem B2253643 : Blo 2253435 2253643 := bstep (se 1 (by rfl) ⟨1690232, by rfl⟩ : syracuseStep 2253643 = 3380465) B3380465
theorem B2852273 : Blo 2253435 2852273 := bbase (se 2 (by rfl) ⟨1069602, by rfl⟩ : syracuseStep 2852273 = 2139205) (by norm_num)
theorem B7606061 : Blo 2253435 7606061 := bstep (se 3 (by rfl) ⟨1426136, by rfl⟩ : syracuseStep 7606061 = 2852273) B2852273
theorem B5070707 : Blo 2253435 5070707 := bstep (se 1 (by rfl) ⟨3803030, by rfl⟩ : syracuseStep 5070707 = 7606061) B7606061
theorem B3380471 : Blo 2253435 3380471 := bstep (se 1 (by rfl) ⟨2535353, by rfl⟩ : syracuseStep 3380471 = 5070707) B5070707
theorem B2253647 : Blo 2253435 2253647 := bstep (se 1 (by rfl) ⟨1690235, by rfl⟩ : syracuseStep 2253647 = 3380471) B3380471
theorem B3380477 : Blo 2253435 3380477 := bbase (se 3 (by rfl) ⟨633839, by rfl⟩ : syracuseStep 3380477 = 1267679) (by norm_num)
theorem B2253651 : Blo 2253435 2253651 := bstep (se 1 (by rfl) ⟨1690238, by rfl⟩ : syracuseStep 2253651 = 3380477) B3380477
theorem B5070725 : Blo 2253435 5070725 := bbase (se 4 (by rfl) ⟨475380, by rfl⟩ : syracuseStep 5070725 = 950761) (by norm_num)
theorem B3380483 : Blo 2253435 3380483 := bstep (se 1 (by rfl) ⟨2535362, by rfl⟩ : syracuseStep 3380483 = 5070725) B5070725
theorem B2253655 : Blo 2253435 2253655 := bstep (se 1 (by rfl) ⟨1690241, by rfl⟩ : syracuseStep 2253655 = 3380483) B3380483
theorem B2284409 : Blo 2253435 2284409 := bbase (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) (by norm_num)
theorem B6091757 : Blo 2253435 6091757 := bstep (se 3 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 6091757 = 2284409) B2284409
theorem B4061171 : Blo 2253435 4061171 := bstep (se 1 (by rfl) ⟨3045878, by rfl⟩ : syracuseStep 4061171 = 6091757) B6091757
theorem B2707447 : Blo 2253435 2707447 := bstep (se 1 (by rfl) ⟨2030585, by rfl⟩ : syracuseStep 2707447 = 4061171) B4061171
theorem B3609929 : Blo 2253435 3609929 := bstep (se 2 (by rfl) ⟨1353723, by rfl⟩ : syracuseStep 3609929 = 2707447) B2707447
theorem B2406619 : Blo 2253435 2406619 := bstep (se 1 (by rfl) ⟨1804964, by rfl⟩ : syracuseStep 2406619 = 3609929) B3609929
theorem B3208825 : Blo 2253435 3208825 := bstep (se 2 (by rfl) ⟨1203309, by rfl⟩ : syracuseStep 3208825 = 2406619) B2406619
theorem B4278433 : Blo 2253435 4278433 := bstep (se 2 (by rfl) ⟨1604412, by rfl⟩ : syracuseStep 4278433 = 3208825) B3208825
theorem B5704577 : Blo 2253435 5704577 := bstep (se 2 (by rfl) ⟨2139216, by rfl⟩ : syracuseStep 5704577 = 4278433) B4278433
theorem B3803051 : Blo 2253435 3803051 := bstep (se 1 (by rfl) ⟨2852288, by rfl⟩ : syracuseStep 3803051 = 5704577) B5704577
theorem B2535367 : Blo 2253435 2535367 := bstep (se 1 (by rfl) ⟨1901525, by rfl⟩ : syracuseStep 2535367 = 3803051) B3803051
theorem B3380489 : Blo 2253435 3380489 := bstep (se 2 (by rfl) ⟨1267683, by rfl⟩ : syracuseStep 3380489 = 2535367) B2535367
theorem B2253659 : Blo 2253435 2253659 := bstep (se 1 (by rfl) ⟨1690244, by rfl⟩ : syracuseStep 2253659 = 3380489) B3380489
theorem B11409173 : Blo 2253435 11409173 := bbase (se 6 (by rfl) ⟨267402, by rfl⟩ : syracuseStep 11409173 = 534805) (by norm_num)
theorem B7606115 : Blo 2253435 7606115 := bstep (se 1 (by rfl) ⟨5704586, by rfl⟩ : syracuseStep 7606115 = 11409173) B11409173
theorem B5070743 : Blo 2253435 5070743 := bstep (se 1 (by rfl) ⟨3803057, by rfl⟩ : syracuseStep 5070743 = 7606115) B7606115
theorem B3380495 : Blo 2253435 3380495 := bstep (se 1 (by rfl) ⟨2535371, by rfl⟩ : syracuseStep 3380495 = 5070743) B5070743
theorem B2253663 : Blo 2253435 2253663 := bstep (se 1 (by rfl) ⟨1690247, by rfl⟩ : syracuseStep 2253663 = 3380495) B3380495
theorem B3380501 : Blo 2253435 3380501 := bbase (se 6 (by rfl) ⟨79230, by rfl⟩ : syracuseStep 3380501 = 158461) (by norm_num)
theorem B2253667 : Blo 2253435 2253667 := bstep (se 1 (by rfl) ⟨1690250, by rfl⟩ : syracuseStep 2253667 = 3380501) B3380501
theorem B3045893 : Blo 2253435 3045893 := bbase (se 4 (by rfl) ⟨285552, by rfl⟩ : syracuseStep 3045893 = 571105) (by norm_num)
theorem B32489525 : Blo 2253435 32489525 := bstep (se 5 (by rfl) ⟨1522946, by rfl⟩ : syracuseStep 32489525 = 3045893) B3045893
theorem B21659683 : Blo 2253435 21659683 := bstep (se 1 (by rfl) ⟨16244762, by rfl⟩ : syracuseStep 21659683 = 32489525) B32489525
theorem B28879577 : Blo 2253435 28879577 := bstep (se 2 (by rfl) ⟨10829841, by rfl⟩ : syracuseStep 28879577 = 21659683) B21659683
theorem B19253051 : Blo 2253435 19253051 := bstep (se 1 (by rfl) ⟨14439788, by rfl⟩ : syracuseStep 19253051 = 28879577) B28879577
theorem B12835367 : Blo 2253435 12835367 := bstep (se 1 (by rfl) ⟨9626525, by rfl⟩ : syracuseStep 12835367 = 19253051) B19253051
theorem B8556911 : Blo 2253435 8556911 := bstep (se 1 (by rfl) ⟨6417683, by rfl⟩ : syracuseStep 8556911 = 12835367) B12835367
theorem B5704607 : Blo 2253435 5704607 := bstep (se 1 (by rfl) ⟨4278455, by rfl⟩ : syracuseStep 5704607 = 8556911) B8556911
theorem B3803071 : Blo 2253435 3803071 := bstep (se 1 (by rfl) ⟨2852303, by rfl⟩ : syracuseStep 3803071 = 5704607) B5704607
theorem B5070761 : Blo 2253435 5070761 := bstep (se 2 (by rfl) ⟨1901535, by rfl⟩ : syracuseStep 5070761 = 3803071) B3803071
theorem B3380507 : Blo 2253435 3380507 := bstep (se 1 (by rfl) ⟨2535380, by rfl⟩ : syracuseStep 3380507 = 5070761) B5070761
theorem B2253671 : Blo 2253435 2253671 := bstep (se 1 (by rfl) ⟨1690253, by rfl⟩ : syracuseStep 2253671 = 3380507) B3380507
theorem B2535385 : Blo 2253435 2535385 := bbase (se 2 (by rfl) ⟨950769, by rfl⟩ : syracuseStep 2535385 = 1901539) (by norm_num)
theorem B3380513 : Blo 2253435 3380513 := bstep (se 2 (by rfl) ⟨1267692, by rfl⟩ : syracuseStep 3380513 = 2535385) B2535385
theorem B2253675 : Blo 2253435 2253675 := bstep (se 1 (by rfl) ⟨1690256, by rfl⟩ : syracuseStep 2253675 = 3380513) B3380513
theorem B3208853 : Blo 2253435 3208853 := bbase (se 6 (by rfl) ⟨75207, by rfl⟩ : syracuseStep 3208853 = 150415) (by norm_num)
theorem B8556941 : Blo 2253435 8556941 := bstep (se 3 (by rfl) ⟨1604426, by rfl⟩ : syracuseStep 8556941 = 3208853) B3208853
theorem B5704627 : Blo 2253435 5704627 := bstep (se 1 (by rfl) ⟨4278470, by rfl⟩ : syracuseStep 5704627 = 8556941) B8556941
theorem B7606169 : Blo 2253435 7606169 := bstep (se 2 (by rfl) ⟨2852313, by rfl⟩ : syracuseStep 7606169 = 5704627) B5704627
theorem B5070779 : Blo 2253435 5070779 := bstep (se 1 (by rfl) ⟨3803084, by rfl⟩ : syracuseStep 5070779 = 7606169) B7606169
theorem B3380519 : Blo 2253435 3380519 := bstep (se 1 (by rfl) ⟨2535389, by rfl⟩ : syracuseStep 3380519 = 5070779) B5070779
theorem B2253679 : Blo 2253435 2253679 := bstep (se 1 (by rfl) ⟨1690259, by rfl⟩ : syracuseStep 2253679 = 3380519) B3380519
theorem B3380525 : Blo 2253435 3380525 := bbase (se 3 (by rfl) ⟨633848, by rfl⟩ : syracuseStep 3380525 = 1267697) (by norm_num)
theorem B2253683 : Blo 2253435 2253683 := bstep (se 1 (by rfl) ⟨1690262, by rfl⟩ : syracuseStep 2253683 = 3380525) B3380525
theorem B5070797 : Blo 2253435 5070797 := bbase (se 3 (by rfl) ⟨950774, by rfl⟩ : syracuseStep 5070797 = 1901549) (by norm_num)
theorem B3380531 : Blo 2253435 3380531 := bstep (se 1 (by rfl) ⟨2535398, by rfl⟩ : syracuseStep 3380531 = 5070797) B5070797
theorem B2253687 : Blo 2253435 2253687 := bstep (se 1 (by rfl) ⟨1690265, by rfl⟩ : syracuseStep 2253687 = 3380531) B3380531
theorem B2852329 : Blo 2253435 2852329 := bbase (se 2 (by rfl) ⟨1069623, by rfl⟩ : syracuseStep 2852329 = 2139247) (by norm_num)
theorem B3803105 : Blo 2253435 3803105 := bstep (se 2 (by rfl) ⟨1426164, by rfl⟩ : syracuseStep 3803105 = 2852329) B2852329
theorem B2535403 : Blo 2253435 2535403 := bstep (se 1 (by rfl) ⟨1901552, by rfl⟩ : syracuseStep 2535403 = 3803105) B3803105
theorem B3380537 : Blo 2253435 3380537 := bstep (se 2 (by rfl) ⟨1267701, by rfl⟩ : syracuseStep 3380537 = 2535403) B2535403
theorem B2253691 : Blo 2253435 2253691 := bstep (se 1 (by rfl) ⟨1690268, by rfl⟩ : syracuseStep 2253691 = 3380537) B3380537
theorem B2707489 : Blo 2253435 2707489 := bbase (se 2 (by rfl) ⟨1015308, by rfl⟩ : syracuseStep 2707489 = 2030617) (by norm_num)
theorem B14439941 : Blo 2253435 14439941 := bstep (se 4 (by rfl) ⟨1353744, by rfl⟩ : syracuseStep 14439941 = 2707489) B2707489
theorem B9626627 : Blo 2253435 9626627 := bstep (se 1 (by rfl) ⟨7219970, by rfl⟩ : syracuseStep 9626627 = 14439941) B14439941
theorem B25671005 : Blo 2253435 25671005 := bstep (se 3 (by rfl) ⟨4813313, by rfl⟩ : syracuseStep 25671005 = 9626627) B9626627
theorem B17114003 : Blo 2253435 17114003 := bstep (se 1 (by rfl) ⟨12835502, by rfl⟩ : syracuseStep 17114003 = 25671005) B25671005
theorem B11409335 : Blo 2253435 11409335 := bstep (se 1 (by rfl) ⟨8557001, by rfl⟩ : syracuseStep 11409335 = 17114003) B17114003
theorem B7606223 : Blo 2253435 7606223 := bstep (se 1 (by rfl) ⟨5704667, by rfl⟩ : syracuseStep 7606223 = 11409335) B11409335
theorem B5070815 : Blo 2253435 5070815 := bstep (se 1 (by rfl) ⟨3803111, by rfl⟩ : syracuseStep 5070815 = 7606223) B7606223
theorem B3380543 : Blo 2253435 3380543 := bstep (se 1 (by rfl) ⟨2535407, by rfl⟩ : syracuseStep 3380543 = 5070815) B5070815
theorem B2253695 : Blo 2253435 2253695 := bstep (se 1 (by rfl) ⟨1690271, by rfl⟩ : syracuseStep 2253695 = 3380543) B3380543
theorem B3380549 : Blo 2253435 3380549 := bbase (se 4 (by rfl) ⟨316926, by rfl⟩ : syracuseStep 3380549 = 633853) (by norm_num)
theorem B2253699 : Blo 2253435 2253699 := bstep (se 1 (by rfl) ⟨1690274, by rfl⟩ : syracuseStep 2253699 = 3380549) B3380549
theorem B3803125 : Blo 2253435 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B5070833 : Blo 2253435 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B3380555 : Blo 2253435 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B2253703 : Blo 2253435 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B2535421 : Blo 2253435 2535421 := bbase (se 3 (by rfl) ⟨475391, by rfl⟩ : syracuseStep 2535421 = 950783) (by norm_num)
theorem B3380561 : Blo 2253435 3380561 := bstep (se 2 (by rfl) ⟨1267710, by rfl⟩ : syracuseStep 3380561 = 2535421) B2535421
theorem B2253707 : Blo 2253435 2253707 := bstep (se 1 (by rfl) ⟨1690280, by rfl⟩ : syracuseStep 2253707 = 3380561) B3380561
theorem B7606277 : Blo 2253435 7606277 := bbase (se 4 (by rfl) ⟨713088, by rfl⟩ : syracuseStep 7606277 = 1426177) (by norm_num)
theorem B5070851 : Blo 2253435 5070851 := bstep (se 1 (by rfl) ⟨3803138, by rfl⟩ : syracuseStep 5070851 = 7606277) B7606277
theorem B3380567 : Blo 2253435 3380567 := bstep (se 1 (by rfl) ⟨2535425, by rfl⟩ : syracuseStep 3380567 = 5070851) B5070851
theorem B2253711 : Blo 2253435 2253711 := bstep (se 1 (by rfl) ⟨1690283, by rfl⟩ : syracuseStep 2253711 = 3380567) B3380567
theorem B3380573 : Blo 2253435 3380573 := bbase (se 3 (by rfl) ⟨633857, by rfl⟩ : syracuseStep 3380573 = 1267715) (by norm_num)
theorem B2253715 : Blo 2253435 2253715 := bstep (se 1 (by rfl) ⟨1690286, by rfl⟩ : syracuseStep 2253715 = 3380573) B3380573
theorem B5070869 : Blo 2253435 5070869 := bbase (se 6 (by rfl) ⟨118848, by rfl⟩ : syracuseStep 5070869 = 237697) (by norm_num)
theorem B3380579 : Blo 2253435 3380579 := bstep (se 1 (by rfl) ⟨2535434, by rfl⟩ : syracuseStep 3380579 = 5070869) B5070869
theorem B2253719 : Blo 2253435 2253719 := bstep (se 1 (by rfl) ⟨1690289, by rfl⟩ : syracuseStep 2253719 = 3380579) B3380579
theorem B8557109 : Blo 2253435 8557109 := bbase (se 5 (by rfl) ⟨401114, by rfl⟩ : syracuseStep 8557109 = 802229) (by norm_num)
theorem B5704739 : Blo 2253435 5704739 := bstep (se 1 (by rfl) ⟨4278554, by rfl⟩ : syracuseStep 5704739 = 8557109) B8557109
theorem B3803159 : Blo 2253435 3803159 := bstep (se 1 (by rfl) ⟨2852369, by rfl⟩ : syracuseStep 3803159 = 5704739) B5704739
theorem B2535439 : Blo 2253435 2535439 := bstep (se 1 (by rfl) ⟨1901579, by rfl⟩ : syracuseStep 2535439 = 3803159) B3803159
theorem B3380585 : Blo 2253435 3380585 := bstep (se 2 (by rfl) ⟨1267719, by rfl⟩ : syracuseStep 3380585 = 2535439) B2535439
theorem B2253723 : Blo 2253435 2253723 := bstep (se 1 (by rfl) ⟨1690292, by rfl⟩ : syracuseStep 2253723 = 3380585) B3380585
theorem B3610037 : Blo 2253435 3610037 := bbase (se 5 (by rfl) ⟨169220, by rfl⟩ : syracuseStep 3610037 = 338441) (by norm_num)
theorem B2406691 : Blo 2253435 2406691 := bstep (se 1 (by rfl) ⟨1805018, by rfl⟩ : syracuseStep 2406691 = 3610037) B3610037
theorem B12835685 : Blo 2253435 12835685 := bstep (se 4 (by rfl) ⟨1203345, by rfl⟩ : syracuseStep 12835685 = 2406691) B2406691
theorem B8557123 : Blo 2253435 8557123 := bstep (se 1 (by rfl) ⟨6417842, by rfl⟩ : syracuseStep 8557123 = 12835685) B12835685
theorem B11409497 : Blo 2253435 11409497 := bstep (se 2 (by rfl) ⟨4278561, by rfl⟩ : syracuseStep 11409497 = 8557123) B8557123
theorem B7606331 : Blo 2253435 7606331 := bstep (se 1 (by rfl) ⟨5704748, by rfl⟩ : syracuseStep 7606331 = 11409497) B11409497
theorem B5070887 : Blo 2253435 5070887 := bstep (se 1 (by rfl) ⟨3803165, by rfl⟩ : syracuseStep 5070887 = 7606331) B7606331
theorem B3380591 : Blo 2253435 3380591 := bstep (se 1 (by rfl) ⟨2535443, by rfl⟩ : syracuseStep 3380591 = 5070887) B5070887
theorem B2253727 : Blo 2253435 2253727 := bstep (se 1 (by rfl) ⟨1690295, by rfl⟩ : syracuseStep 2253727 = 3380591) B3380591
theorem B3380597 : Blo 2253435 3380597 := bbase (se 5 (by rfl) ⟨158465, by rfl⟩ : syracuseStep 3380597 = 316931) (by norm_num)
theorem B2253731 : Blo 2253435 2253731 := bstep (se 1 (by rfl) ⟨1690298, by rfl⟩ : syracuseStep 2253731 = 3380597) B3380597
theorem B3208933 : Blo 2253435 3208933 := bbase (se 4 (by rfl) ⟨300837, by rfl⟩ : syracuseStep 3208933 = 601675) (by norm_num)
theorem B4278577 : Blo 2253435 4278577 := bstep (se 2 (by rfl) ⟨1604466, by rfl⟩ : syracuseStep 4278577 = 3208933) B3208933
theorem B5704769 : Blo 2253435 5704769 := bstep (se 2 (by rfl) ⟨2139288, by rfl⟩ : syracuseStep 5704769 = 4278577) B4278577
theorem B3803179 : Blo 2253435 3803179 := bstep (se 1 (by rfl) ⟨2852384, by rfl⟩ : syracuseStep 3803179 = 5704769) B5704769
theorem B5070905 : Blo 2253435 5070905 := bstep (se 2 (by rfl) ⟨1901589, by rfl⟩ : syracuseStep 5070905 = 3803179) B3803179
theorem B3380603 : Blo 2253435 3380603 := bstep (se 1 (by rfl) ⟨2535452, by rfl⟩ : syracuseStep 3380603 = 5070905) B5070905
theorem B2253735 : Blo 2253435 2253735 := bstep (se 1 (by rfl) ⟨1690301, by rfl⟩ : syracuseStep 2253735 = 3380603) B3380603
theorem B2535457 : Blo 2253435 2535457 := bbase (se 2 (by rfl) ⟨950796, by rfl⟩ : syracuseStep 2535457 = 1901593) (by norm_num)
theorem B3380609 : Blo 2253435 3380609 := bstep (se 2 (by rfl) ⟨1267728, by rfl⟩ : syracuseStep 3380609 = 2535457) B2535457
theorem B2253739 : Blo 2253435 2253739 := bstep (se 1 (by rfl) ⟨1690304, by rfl⟩ : syracuseStep 2253739 = 3380609) B3380609
theorem B5704789 : Blo 2253435 5704789 := bbase (se 8 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 5704789 = 66853) (by norm_num)
theorem B7606385 : Blo 2253435 7606385 := bstep (se 2 (by rfl) ⟨2852394, by rfl⟩ : syracuseStep 7606385 = 5704789) B5704789
theorem B5070923 : Blo 2253435 5070923 := bstep (se 1 (by rfl) ⟨3803192, by rfl⟩ : syracuseStep 5070923 = 7606385) B7606385
theorem B3380615 : Blo 2253435 3380615 := bstep (se 1 (by rfl) ⟨2535461, by rfl⟩ : syracuseStep 3380615 = 5070923) B5070923
theorem B2253743 : Blo 2253435 2253743 := bstep (se 1 (by rfl) ⟨1690307, by rfl⟩ : syracuseStep 2253743 = 3380615) B3380615
theorem B3380621 : Blo 2253435 3380621 := bbase (se 3 (by rfl) ⟨633866, by rfl⟩ : syracuseStep 3380621 = 1267733) (by norm_num)
theorem B2253747 : Blo 2253435 2253747 := bstep (se 1 (by rfl) ⟨1690310, by rfl⟩ : syracuseStep 2253747 = 3380621) B3380621
theorem B5070941 : Blo 2253435 5070941 := bbase (se 3 (by rfl) ⟨950801, by rfl⟩ : syracuseStep 5070941 = 1901603) (by norm_num)
theorem B3380627 : Blo 2253435 3380627 := bstep (se 1 (by rfl) ⟨2535470, by rfl⟩ : syracuseStep 3380627 = 5070941) B5070941
theorem B2253751 : Blo 2253435 2253751 := bstep (se 1 (by rfl) ⟨1690313, by rfl⟩ : syracuseStep 2253751 = 3380627) B3380627
theorem B3803213 : Blo 2253435 3803213 := bbase (se 3 (by rfl) ⟨713102, by rfl⟩ : syracuseStep 3803213 = 1426205) (by norm_num)
theorem B2535475 : Blo 2253435 2535475 := bstep (se 1 (by rfl) ⟨1901606, by rfl⟩ : syracuseStep 2535475 = 3803213) B3803213
theorem B3380633 : Blo 2253435 3380633 := bstep (se 2 (by rfl) ⟨1267737, by rfl⟩ : syracuseStep 3380633 = 2535475) B2535475
theorem B2253755 : Blo 2253435 2253755 := bstep (se 1 (by rfl) ⟨1690316, by rfl⟩ : syracuseStep 2253755 = 3380633) B3380633
theorem B9758245 : Blo 2253435 9758245 := bbase (se 4 (by rfl) ⟨914835, by rfl⟩ : syracuseStep 9758245 = 1829671) (by norm_num)
theorem B13010993 : Blo 2253435 13010993 := bstep (se 2 (by rfl) ⟨4879122, by rfl⟩ : syracuseStep 13010993 = 9758245) B9758245
theorem B8673995 : Blo 2253435 8673995 := bstep (se 1 (by rfl) ⟨6505496, by rfl⟩ : syracuseStep 8673995 = 13010993) B13010993
theorem B5782663 : Blo 2253435 5782663 := bstep (se 1 (by rfl) ⟨4336997, by rfl⟩ : syracuseStep 5782663 = 8673995) B8673995
theorem B30840869 : Blo 2253435 30840869 := bstep (se 4 (by rfl) ⟨2891331, by rfl⟩ : syracuseStep 30840869 = 5782663) B5782663
theorem B82242317 : Blo 2253435 82242317 := bstep (se 3 (by rfl) ⟨15420434, by rfl⟩ : syracuseStep 82242317 = 30840869) B30840869
theorem B54828211 : Blo 2253435 54828211 := bstep (se 1 (by rfl) ⟨41121158, by rfl⟩ : syracuseStep 54828211 = 82242317) B82242317
theorem B73104281 : Blo 2253435 73104281 := bstep (se 2 (by rfl) ⟨27414105, by rfl⟩ : syracuseStep 73104281 = 54828211) B54828211
theorem B48736187 : Blo 2253435 48736187 := bstep (se 1 (by rfl) ⟨36552140, by rfl⟩ : syracuseStep 48736187 = 73104281) B73104281
theorem B32490791 : Blo 2253435 32490791 := bstep (se 1 (by rfl) ⟨24368093, by rfl⟩ : syracuseStep 32490791 = 48736187) B48736187
theorem B21660527 : Blo 2253435 21660527 := bstep (se 1 (by rfl) ⟨16245395, by rfl⟩ : syracuseStep 21660527 = 32490791) B32490791
theorem B14440351 : Blo 2253435 14440351 := bstep (se 1 (by rfl) ⟨10830263, by rfl⟩ : syracuseStep 14440351 = 21660527) B21660527
theorem B19253801 : Blo 2253435 19253801 := bstep (se 2 (by rfl) ⟨7220175, by rfl⟩ : syracuseStep 19253801 = 14440351) B14440351
theorem B12835867 : Blo 2253435 12835867 := bstep (se 1 (by rfl) ⟨9626900, by rfl⟩ : syracuseStep 12835867 = 19253801) B19253801
theorem B17114489 : Blo 2253435 17114489 := bstep (se 2 (by rfl) ⟨6417933, by rfl⟩ : syracuseStep 17114489 = 12835867) B12835867
theorem B11409659 : Blo 2253435 11409659 := bstep (se 1 (by rfl) ⟨8557244, by rfl⟩ : syracuseStep 11409659 = 17114489) B17114489
theorem B7606439 : Blo 2253435 7606439 := bstep (se 1 (by rfl) ⟨5704829, by rfl⟩ : syracuseStep 7606439 = 11409659) B11409659
theorem B5070959 : Blo 2253435 5070959 := bstep (se 1 (by rfl) ⟨3803219, by rfl⟩ : syracuseStep 5070959 = 7606439) B7606439
theorem B3380639 : Blo 2253435 3380639 := bstep (se 1 (by rfl) ⟨2535479, by rfl⟩ : syracuseStep 3380639 = 5070959) B5070959
theorem B2253759 : Blo 2253435 2253759 := bstep (se 1 (by rfl) ⟨1690319, by rfl⟩ : syracuseStep 2253759 = 3380639) B3380639
theorem B3380645 : Blo 2253435 3380645 := bbase (se 4 (by rfl) ⟨316935, by rfl⟩ : syracuseStep 3380645 = 633871) (by norm_num)
theorem B2253763 : Blo 2253435 2253763 := bstep (se 1 (by rfl) ⟨1690322, by rfl⟩ : syracuseStep 2253763 = 3380645) B3380645
theorem B2852425 : Blo 2253435 2852425 := bbase (se 2 (by rfl) ⟨1069659, by rfl⟩ : syracuseStep 2852425 = 2139319) (by norm_num)
theorem B3803233 : Blo 2253435 3803233 := bstep (se 2 (by rfl) ⟨1426212, by rfl⟩ : syracuseStep 3803233 = 2852425) B2852425
theorem B5070977 : Blo 2253435 5070977 := bstep (se 2 (by rfl) ⟨1901616, by rfl⟩ : syracuseStep 5070977 = 3803233) B3803233
theorem B3380651 : Blo 2253435 3380651 := bstep (se 1 (by rfl) ⟨2535488, by rfl⟩ : syracuseStep 3380651 = 5070977) B5070977
theorem B2253767 : Blo 2253435 2253767 := bstep (se 1 (by rfl) ⟨1690325, by rfl⟩ : syracuseStep 2253767 = 3380651) B3380651
theorem B2535493 : Blo 2253435 2535493 := bbase (se 4 (by rfl) ⟨237702, by rfl⟩ : syracuseStep 2535493 = 475405) (by norm_num)
theorem B3380657 : Blo 2253435 3380657 := bstep (se 2 (by rfl) ⟨1267746, by rfl⟩ : syracuseStep 3380657 = 2535493) B2535493
theorem B2253771 : Blo 2253435 2253771 := bstep (se 1 (by rfl) ⟨1690328, by rfl⟩ : syracuseStep 2253771 = 3380657) B3380657
theorem B4278653 : Blo 2253435 4278653 := bbase (se 3 (by rfl) ⟨802247, by rfl⟩ : syracuseStep 4278653 = 1604495) (by norm_num)
theorem B2852435 : Blo 2253435 2852435 := bstep (se 1 (by rfl) ⟨2139326, by rfl⟩ : syracuseStep 2852435 = 4278653) B4278653
theorem B7606493 : Blo 2253435 7606493 := bstep (se 3 (by rfl) ⟨1426217, by rfl⟩ : syracuseStep 7606493 = 2852435) B2852435
theorem B5070995 : Blo 2253435 5070995 := bstep (se 1 (by rfl) ⟨3803246, by rfl⟩ : syracuseStep 5070995 = 7606493) B7606493
theorem B3380663 : Blo 2253435 3380663 := bstep (se 1 (by rfl) ⟨2535497, by rfl⟩ : syracuseStep 3380663 = 5070995) B5070995
theorem B2253775 : Blo 2253435 2253775 := bstep (se 1 (by rfl) ⟨1690331, by rfl⟩ : syracuseStep 2253775 = 3380663) B3380663
theorem B3380669 : Blo 2253435 3380669 := bbase (se 3 (by rfl) ⟨633875, by rfl⟩ : syracuseStep 3380669 = 1267751) (by norm_num)
theorem B2253779 : Blo 2253435 2253779 := bstep (se 1 (by rfl) ⟨1690334, by rfl⟩ : syracuseStep 2253779 = 3380669) B3380669
theorem B5071013 : Blo 2253435 5071013 := bbase (se 4 (by rfl) ⟨475407, by rfl⟩ : syracuseStep 5071013 = 950815) (by norm_num)
theorem B3380675 : Blo 2253435 3380675 := bstep (se 1 (by rfl) ⟨2535506, by rfl⟩ : syracuseStep 3380675 = 5071013) B5071013
theorem B2253783 : Blo 2253435 2253783 := bstep (se 1 (by rfl) ⟨1690337, by rfl⟩ : syracuseStep 2253783 = 3380675) B3380675
theorem B5704901 : Blo 2253435 5704901 := bbase (se 4 (by rfl) ⟨534834, by rfl⟩ : syracuseStep 5704901 = 1069669) (by norm_num)
theorem B3803267 : Blo 2253435 3803267 := bstep (se 1 (by rfl) ⟨2852450, by rfl⟩ : syracuseStep 3803267 = 5704901) B5704901
theorem B2535511 : Blo 2253435 2535511 := bstep (se 1 (by rfl) ⟨1901633, by rfl⟩ : syracuseStep 2535511 = 3803267) B3803267
theorem B3380681 : Blo 2253435 3380681 := bstep (se 2 (by rfl) ⟨1267755, by rfl⟩ : syracuseStep 3380681 = 2535511) B2535511
theorem B2253787 : Blo 2253435 2253787 := bstep (se 1 (by rfl) ⟨1690340, by rfl⟩ : syracuseStep 2253787 = 3380681) B3380681
theorem B5489093 : Blo 2253435 5489093 := bbase (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) (by norm_num)
theorem B14637581 : Blo 2253435 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B9758387 : Blo 2253435 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B6505591 : Blo 2253435 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B8674121 : Blo 2253435 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B5782747 : Blo 2253435 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B7710329 : Blo 2253435 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B20560877 : Blo 2253435 20560877 := bstep (se 3 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 20560877 = 7710329) B7710329
theorem B13707251 : Blo 2253435 13707251 := bstep (se 1 (by rfl) ⟨10280438, by rfl⟩ : syracuseStep 13707251 = 20560877) B20560877
theorem B9138167 : Blo 2253435 9138167 := bstep (se 1 (by rfl) ⟨6853625, by rfl⟩ : syracuseStep 9138167 = 13707251) B13707251
theorem B6092111 : Blo 2253435 6092111 := bstep (se 1 (by rfl) ⟨4569083, by rfl⟩ : syracuseStep 6092111 = 9138167) B9138167
theorem B16245629 : Blo 2253435 16245629 := bstep (se 3 (by rfl) ⟨3046055, by rfl⟩ : syracuseStep 16245629 = 6092111) B6092111
theorem B10830419 : Blo 2253435 10830419 := bstep (se 1 (by rfl) ⟨8122814, by rfl⟩ : syracuseStep 10830419 = 16245629) B16245629
theorem B7220279 : Blo 2253435 7220279 := bstep (se 1 (by rfl) ⟨5415209, by rfl⟩ : syracuseStep 7220279 = 10830419) B10830419
theorem B4813519 : Blo 2253435 4813519 := bstep (se 1 (by rfl) ⟨3610139, by rfl⟩ : syracuseStep 4813519 = 7220279) B7220279
theorem B6418025 : Blo 2253435 6418025 := bstep (se 2 (by rfl) ⟨2406759, by rfl⟩ : syracuseStep 6418025 = 4813519) B4813519
theorem B4278683 : Blo 2253435 4278683 := bstep (se 1 (by rfl) ⟨3209012, by rfl⟩ : syracuseStep 4278683 = 6418025) B6418025
theorem B11409821 : Blo 2253435 11409821 := bstep (se 3 (by rfl) ⟨2139341, by rfl⟩ : syracuseStep 11409821 = 4278683) B4278683
theorem B7606547 : Blo 2253435 7606547 := bstep (se 1 (by rfl) ⟨5704910, by rfl⟩ : syracuseStep 7606547 = 11409821) B11409821
theorem B5071031 : Blo 2253435 5071031 := bstep (se 1 (by rfl) ⟨3803273, by rfl⟩ : syracuseStep 5071031 = 7606547) B7606547
theorem B3380687 : Blo 2253435 3380687 := bstep (se 1 (by rfl) ⟨2535515, by rfl⟩ : syracuseStep 3380687 = 5071031) B5071031
theorem B2253791 : Blo 2253435 2253791 := bstep (se 1 (by rfl) ⟨1690343, by rfl⟩ : syracuseStep 2253791 = 3380687) B3380687
theorem B3380693 : Blo 2253435 3380693 := bbase (se 7 (by rfl) ⟨39617, by rfl⟩ : syracuseStep 3380693 = 79235) (by norm_num)
theorem B2253795 : Blo 2253435 2253795 := bstep (se 1 (by rfl) ⟨1690346, by rfl⟩ : syracuseStep 2253795 = 3380693) B3380693
theorem B8557397 : Blo 2253435 8557397 := bbase (se 9 (by rfl) ⟨25070, by rfl⟩ : syracuseStep 8557397 = 50141) (by norm_num)
theorem B5704931 : Blo 2253435 5704931 := bstep (se 1 (by rfl) ⟨4278698, by rfl⟩ : syracuseStep 5704931 = 8557397) B8557397
theorem B3803287 : Blo 2253435 3803287 := bstep (se 1 (by rfl) ⟨2852465, by rfl⟩ : syracuseStep 3803287 = 5704931) B5704931
theorem B5071049 : Blo 2253435 5071049 := bstep (se 2 (by rfl) ⟨1901643, by rfl⟩ : syracuseStep 5071049 = 3803287) B3803287
theorem B3380699 : Blo 2253435 3380699 := bstep (se 1 (by rfl) ⟨2535524, by rfl⟩ : syracuseStep 3380699 = 5071049) B5071049
theorem B2253799 : Blo 2253435 2253799 := bstep (se 1 (by rfl) ⟨1690349, by rfl⟩ : syracuseStep 2253799 = 3380699) B3380699
theorem B2535529 : Blo 2253435 2535529 := bbase (se 2 (by rfl) ⟨950823, by rfl⟩ : syracuseStep 2535529 = 1901647) (by norm_num)
theorem B3380705 : Blo 2253435 3380705 := bstep (se 2 (by rfl) ⟨1267764, by rfl⟩ : syracuseStep 3380705 = 2535529) B2535529
theorem B2253803 : Blo 2253435 2253803 := bstep (se 1 (by rfl) ⟨1690352, by rfl⟩ : syracuseStep 2253803 = 3380705) B3380705
theorem B3610165 : Blo 2253435 3610165 := bbase (se 5 (by rfl) ⟨169226, by rfl⟩ : syracuseStep 3610165 = 338453) (by norm_num)
theorem B4813553 : Blo 2253435 4813553 := bstep (se 2 (by rfl) ⟨1805082, by rfl⟩ : syracuseStep 4813553 = 3610165) B3610165
theorem B12836141 : Blo 2253435 12836141 := bstep (se 3 (by rfl) ⟨2406776, by rfl⟩ : syracuseStep 12836141 = 4813553) B4813553
theorem B8557427 : Blo 2253435 8557427 := bstep (se 1 (by rfl) ⟨6418070, by rfl⟩ : syracuseStep 8557427 = 12836141) B12836141
theorem B5704951 : Blo 2253435 5704951 := bstep (se 1 (by rfl) ⟨4278713, by rfl⟩ : syracuseStep 5704951 = 8557427) B8557427
theorem B7606601 : Blo 2253435 7606601 := bstep (se 2 (by rfl) ⟨2852475, by rfl⟩ : syracuseStep 7606601 = 5704951) B5704951
theorem B5071067 : Blo 2253435 5071067 := bstep (se 1 (by rfl) ⟨3803300, by rfl⟩ : syracuseStep 5071067 = 7606601) B7606601
theorem B3380711 : Blo 2253435 3380711 := bstep (se 1 (by rfl) ⟨2535533, by rfl⟩ : syracuseStep 3380711 = 5071067) B5071067
theorem B2253807 : Blo 2253435 2253807 := bstep (se 1 (by rfl) ⟨1690355, by rfl⟩ : syracuseStep 2253807 = 3380711) B3380711
theorem B3380717 : Blo 2253435 3380717 := bbase (se 3 (by rfl) ⟨633884, by rfl⟩ : syracuseStep 3380717 = 1267769) (by norm_num)
theorem B2253811 : Blo 2253435 2253811 := bstep (se 1 (by rfl) ⟨1690358, by rfl⟩ : syracuseStep 2253811 = 3380717) B3380717
theorem B5071085 : Blo 2253435 5071085 := bbase (se 3 (by rfl) ⟨950828, by rfl⟩ : syracuseStep 5071085 = 1901657) (by norm_num)
theorem B3380723 : Blo 2253435 3380723 := bstep (se 1 (by rfl) ⟨2535542, by rfl⟩ : syracuseStep 3380723 = 5071085) B5071085
theorem B2253815 : Blo 2253435 2253815 := bstep (se 1 (by rfl) ⟨1690361, by rfl⟩ : syracuseStep 2253815 = 3380723) B3380723
theorem B3209053 : Blo 2253435 3209053 := bbase (se 3 (by rfl) ⟨601697, by rfl⟩ : syracuseStep 3209053 = 1203395) (by norm_num)
theorem B4278737 : Blo 2253435 4278737 := bstep (se 2 (by rfl) ⟨1604526, by rfl⟩ : syracuseStep 4278737 = 3209053) B3209053
theorem B2852491 : Blo 2253435 2852491 := bstep (se 1 (by rfl) ⟨2139368, by rfl⟩ : syracuseStep 2852491 = 4278737) B4278737
theorem B3803321 : Blo 2253435 3803321 := bstep (se 2 (by rfl) ⟨1426245, by rfl⟩ : syracuseStep 3803321 = 2852491) B2852491
theorem B2535547 : Blo 2253435 2535547 := bstep (se 1 (by rfl) ⟨1901660, by rfl⟩ : syracuseStep 2535547 = 3803321) B3803321
theorem B3380729 : Blo 2253435 3380729 := bstep (se 2 (by rfl) ⟨1267773, by rfl⟩ : syracuseStep 3380729 = 2535547) B2535547
theorem B2253819 : Blo 2253435 2253819 := bstep (se 1 (by rfl) ⟨1690364, by rfl⟩ : syracuseStep 2253819 = 3380729) B3380729
theorem B86644565 : Blo 2253435 86644565 := bbase (se 9 (by rfl) ⟨253841, by rfl⟩ : syracuseStep 86644565 = 507683) (by norm_num)
theorem B57763043 : Blo 2253435 57763043 := bstep (se 1 (by rfl) ⟨43322282, by rfl⟩ : syracuseStep 57763043 = 86644565) B86644565
theorem B38508695 : Blo 2253435 38508695 := bstep (se 1 (by rfl) ⟨28881521, by rfl⟩ : syracuseStep 38508695 = 57763043) B57763043
theorem B25672463 : Blo 2253435 25672463 := bstep (se 1 (by rfl) ⟨19254347, by rfl⟩ : syracuseStep 25672463 = 38508695) B38508695
theorem B17114975 : Blo 2253435 17114975 := bstep (se 1 (by rfl) ⟨12836231, by rfl⟩ : syracuseStep 17114975 = 25672463) B25672463
theorem B11409983 : Blo 2253435 11409983 := bstep (se 1 (by rfl) ⟨8557487, by rfl⟩ : syracuseStep 11409983 = 17114975) B17114975
theorem B7606655 : Blo 2253435 7606655 := bstep (se 1 (by rfl) ⟨5704991, by rfl⟩ : syracuseStep 7606655 = 11409983) B11409983
theorem B5071103 : Blo 2253435 5071103 := bstep (se 1 (by rfl) ⟨3803327, by rfl⟩ : syracuseStep 5071103 = 7606655) B7606655
theorem B3380735 : Blo 2253435 3380735 := bstep (se 1 (by rfl) ⟨2535551, by rfl⟩ : syracuseStep 3380735 = 5071103) B5071103
theorem B2253823 : Blo 2253435 2253823 := bstep (se 1 (by rfl) ⟨1690367, by rfl⟩ : syracuseStep 2253823 = 3380735) B3380735
theorem B3380741 : Blo 2253435 3380741 := bbase (se 4 (by rfl) ⟨316944, by rfl⟩ : syracuseStep 3380741 = 633889) (by norm_num)
theorem B2253827 : Blo 2253435 2253827 := bstep (se 1 (by rfl) ⟨1690370, by rfl⟩ : syracuseStep 2253827 = 3380741) B3380741
theorem B3803341 : Blo 2253435 3803341 := bbase (se 3 (by rfl) ⟨713126, by rfl⟩ : syracuseStep 3803341 = 1426253) (by norm_num)
theorem B5071121 : Blo 2253435 5071121 := bstep (se 2 (by rfl) ⟨1901670, by rfl⟩ : syracuseStep 5071121 = 3803341) B3803341
theorem B3380747 : Blo 2253435 3380747 := bstep (se 1 (by rfl) ⟨2535560, by rfl⟩ : syracuseStep 3380747 = 5071121) B5071121
theorem B2253831 : Blo 2253435 2253831 := bstep (se 1 (by rfl) ⟨1690373, by rfl⟩ : syracuseStep 2253831 = 3380747) B3380747
theorem B2535565 : Blo 2253435 2535565 := bbase (se 3 (by rfl) ⟨475418, by rfl⟩ : syracuseStep 2535565 = 950837) (by norm_num)
theorem B3380753 : Blo 2253435 3380753 := bstep (se 2 (by rfl) ⟨1267782, by rfl⟩ : syracuseStep 3380753 = 2535565) B2535565
theorem B2253835 : Blo 2253435 2253835 := bstep (se 1 (by rfl) ⟨1690376, by rfl⟩ : syracuseStep 2253835 = 3380753) B3380753
theorem B7606709 : Blo 2253435 7606709 := bbase (se 5 (by rfl) ⟨356564, by rfl⟩ : syracuseStep 7606709 = 713129) (by norm_num)
theorem B5071139 : Blo 2253435 5071139 := bstep (se 1 (by rfl) ⟨3803354, by rfl⟩ : syracuseStep 5071139 = 7606709) B7606709
theorem B3380759 : Blo 2253435 3380759 := bstep (se 1 (by rfl) ⟨2535569, by rfl⟩ : syracuseStep 3380759 = 5071139) B5071139
theorem B2253839 : Blo 2253435 2253839 := bstep (se 1 (by rfl) ⟨1690379, by rfl⟩ : syracuseStep 2253839 = 3380759) B3380759
theorem B3380765 : Blo 2253435 3380765 := bbase (se 3 (by rfl) ⟨633893, by rfl⟩ : syracuseStep 3380765 = 1267787) (by norm_num)
theorem B2253843 : Blo 2253435 2253843 := bstep (se 1 (by rfl) ⟨1690382, by rfl⟩ : syracuseStep 2253843 = 3380765) B3380765
theorem B5071157 : Blo 2253435 5071157 := bbase (se 5 (by rfl) ⟨237710, by rfl⟩ : syracuseStep 5071157 = 475421) (by norm_num)
theorem B3380771 : Blo 2253435 3380771 := bstep (se 1 (by rfl) ⟨2535578, by rfl⟩ : syracuseStep 3380771 = 5071157) B5071157
theorem B2253847 : Blo 2253435 2253847 := bstep (se 1 (by rfl) ⟨1690385, by rfl⟩ : syracuseStep 2253847 = 3380771) B3380771
theorem B2439661 : Blo 2253435 2439661 := bbase (se 3 (by rfl) ⟨457436, by rfl⟩ : syracuseStep 2439661 = 914873) (by norm_num)
theorem B52046101 : Blo 2253435 52046101 := bstep (se 6 (by rfl) ⟨1219830, by rfl⟩ : syracuseStep 52046101 = 2439661) B2439661
theorem B69394801 : Blo 2253435 69394801 := bstep (se 2 (by rfl) ⟨26023050, by rfl⟩ : syracuseStep 69394801 = 52046101) B52046101
theorem B92526401 : Blo 2253435 92526401 := bstep (se 2 (by rfl) ⟨34697400, by rfl⟩ : syracuseStep 92526401 = 69394801) B69394801
theorem B61684267 : Blo 2253435 61684267 := bstep (se 1 (by rfl) ⟨46263200, by rfl⟩ : syracuseStep 61684267 = 92526401) B92526401
theorem B82245689 : Blo 2253435 82245689 := bstep (se 2 (by rfl) ⟨30842133, by rfl⟩ : syracuseStep 82245689 = 61684267) B61684267
theorem B54830459 : Blo 2253435 54830459 := bstep (se 1 (by rfl) ⟨41122844, by rfl⟩ : syracuseStep 54830459 = 82245689) B82245689
theorem B36553639 : Blo 2253435 36553639 := bstep (se 1 (by rfl) ⟨27415229, by rfl⟩ : syracuseStep 36553639 = 54830459) B54830459
theorem B48738185 : Blo 2253435 48738185 := bstep (se 2 (by rfl) ⟨18276819, by rfl⟩ : syracuseStep 48738185 = 36553639) B36553639
theorem B32492123 : Blo 2253435 32492123 := bstep (se 1 (by rfl) ⟨24369092, by rfl⟩ : syracuseStep 32492123 = 48738185) B48738185
theorem B21661415 : Blo 2253435 21661415 := bstep (se 1 (by rfl) ⟨16246061, by rfl⟩ : syracuseStep 21661415 = 32492123) B32492123
theorem B14440943 : Blo 2253435 14440943 := bstep (se 1 (by rfl) ⟨10830707, by rfl⟩ : syracuseStep 14440943 = 21661415) B21661415
theorem B9627295 : Blo 2253435 9627295 := bstep (se 1 (by rfl) ⟨7220471, by rfl⟩ : syracuseStep 9627295 = 14440943) B14440943
theorem B12836393 : Blo 2253435 12836393 := bstep (se 2 (by rfl) ⟨4813647, by rfl⟩ : syracuseStep 12836393 = 9627295) B9627295
theorem B8557595 : Blo 2253435 8557595 := bstep (se 1 (by rfl) ⟨6418196, by rfl⟩ : syracuseStep 8557595 = 12836393) B12836393
theorem B5705063 : Blo 2253435 5705063 := bstep (se 1 (by rfl) ⟨4278797, by rfl⟩ : syracuseStep 5705063 = 8557595) B8557595
theorem B3803375 : Blo 2253435 3803375 := bstep (se 1 (by rfl) ⟨2852531, by rfl⟩ : syracuseStep 3803375 = 5705063) B5705063
theorem B2535583 : Blo 2253435 2535583 := bstep (se 1 (by rfl) ⟨1901687, by rfl⟩ : syracuseStep 2535583 = 3803375) B3803375
theorem B3380777 : Blo 2253435 3380777 := bstep (se 2 (by rfl) ⟨1267791, by rfl⟩ : syracuseStep 3380777 = 2535583) B2535583
theorem B2253851 : Blo 2253435 2253851 := bstep (se 1 (by rfl) ⟨1690388, by rfl⟩ : syracuseStep 2253851 = 3380777) B3380777
theorem B2605249 : Blo 2253435 2605249 := bbase (se 2 (by rfl) ⟨976968, by rfl⟩ : syracuseStep 2605249 = 1953937) (by norm_num)
theorem B13894661 : Blo 2253435 13894661 := bstep (se 4 (by rfl) ⟨1302624, by rfl⟩ : syracuseStep 13894661 = 2605249) B2605249
theorem B9263107 : Blo 2253435 9263107 := bstep (se 1 (by rfl) ⟨6947330, by rfl⟩ : syracuseStep 9263107 = 13894661) B13894661
theorem B12350809 : Blo 2253435 12350809 := bstep (se 2 (by rfl) ⟨4631553, by rfl⟩ : syracuseStep 12350809 = 9263107) B9263107
theorem B16467745 : Blo 2253435 16467745 := bstep (se 2 (by rfl) ⟨6175404, by rfl⟩ : syracuseStep 16467745 = 12350809) B12350809
theorem B21956993 : Blo 2253435 21956993 := bstep (se 2 (by rfl) ⟨8233872, by rfl⟩ : syracuseStep 21956993 = 16467745) B16467745
theorem B14637995 : Blo 2253435 14637995 := bstep (se 1 (by rfl) ⟨10978496, by rfl⟩ : syracuseStep 14637995 = 21956993) B21956993
theorem B9758663 : Blo 2253435 9758663 := bstep (se 1 (by rfl) ⟨7318997, by rfl⟩ : syracuseStep 9758663 = 14637995) B14637995
theorem B6505775 : Blo 2253435 6505775 := bstep (se 1 (by rfl) ⟨4879331, by rfl⟩ : syracuseStep 6505775 = 9758663) B9758663
theorem B4337183 : Blo 2253435 4337183 := bstep (se 1 (by rfl) ⟨3252887, by rfl⟩ : syracuseStep 4337183 = 6505775) B6505775
theorem B11565821 : Blo 2253435 11565821 := bstep (se 3 (by rfl) ⟨2168591, by rfl⟩ : syracuseStep 11565821 = 4337183) B4337183
theorem B7710547 : Blo 2253435 7710547 := bstep (se 1 (by rfl) ⟨5782910, by rfl⟩ : syracuseStep 7710547 = 11565821) B11565821
theorem B10280729 : Blo 2253435 10280729 := bstep (se 2 (by rfl) ⟨3855273, by rfl⟩ : syracuseStep 10280729 = 7710547) B7710547
theorem B6853819 : Blo 2253435 6853819 := bstep (se 1 (by rfl) ⟨5140364, by rfl⟩ : syracuseStep 6853819 = 10280729) B10280729
theorem B9138425 : Blo 2253435 9138425 := bstep (se 2 (by rfl) ⟨3426909, by rfl⟩ : syracuseStep 9138425 = 6853819) B6853819
theorem B24369133 : Blo 2253435 24369133 := bstep (se 3 (by rfl) ⟨4569212, by rfl⟩ : syracuseStep 24369133 = 9138425) B9138425
theorem B32492177 : Blo 2253435 32492177 := bstep (se 2 (by rfl) ⟨12184566, by rfl⟩ : syracuseStep 32492177 = 24369133) B24369133
theorem B21661451 : Blo 2253435 21661451 := bstep (se 1 (by rfl) ⟨16246088, by rfl⟩ : syracuseStep 21661451 = 32492177) B32492177
theorem B14440967 : Blo 2253435 14440967 := bstep (se 1 (by rfl) ⟨10830725, by rfl⟩ : syracuseStep 14440967 = 21661451) B21661451
theorem B9627311 : Blo 2253435 9627311 := bstep (se 1 (by rfl) ⟨7220483, by rfl⟩ : syracuseStep 9627311 = 14440967) B14440967
theorem B6418207 : Blo 2253435 6418207 := bstep (se 1 (by rfl) ⟨4813655, by rfl⟩ : syracuseStep 6418207 = 9627311) B9627311
theorem B8557609 : Blo 2253435 8557609 := bstep (se 2 (by rfl) ⟨3209103, by rfl⟩ : syracuseStep 8557609 = 6418207) B6418207
theorem B11410145 : Blo 2253435 11410145 := bstep (se 2 (by rfl) ⟨4278804, by rfl⟩ : syracuseStep 11410145 = 8557609) B8557609
theorem B7606763 : Blo 2253435 7606763 := bstep (se 1 (by rfl) ⟨5705072, by rfl⟩ : syracuseStep 7606763 = 11410145) B11410145
theorem B5071175 : Blo 2253435 5071175 := bstep (se 1 (by rfl) ⟨3803381, by rfl⟩ : syracuseStep 5071175 = 7606763) B7606763
theorem B3380783 : Blo 2253435 3380783 := bstep (se 1 (by rfl) ⟨2535587, by rfl⟩ : syracuseStep 3380783 = 5071175) B5071175
theorem B2253855 : Blo 2253435 2253855 := bstep (se 1 (by rfl) ⟨1690391, by rfl⟩ : syracuseStep 2253855 = 3380783) B3380783
theorem B3380789 : Blo 2253435 3380789 := bbase (se 5 (by rfl) ⟨158474, by rfl⟩ : syracuseStep 3380789 = 316949) (by norm_num)
theorem B2253859 : Blo 2253435 2253859 := bstep (se 1 (by rfl) ⟨1690394, by rfl⟩ : syracuseStep 2253859 = 3380789) B3380789
theorem B5705093 : Blo 2253435 5705093 := bbase (se 4 (by rfl) ⟨534852, by rfl⟩ : syracuseStep 5705093 = 1069705) (by norm_num)
theorem B3803395 : Blo 2253435 3803395 := bstep (se 1 (by rfl) ⟨2852546, by rfl⟩ : syracuseStep 3803395 = 5705093) B5705093
theorem B5071193 : Blo 2253435 5071193 := bstep (se 2 (by rfl) ⟨1901697, by rfl⟩ : syracuseStep 5071193 = 3803395) B3803395
theorem B3380795 : Blo 2253435 3380795 := bstep (se 1 (by rfl) ⟨2535596, by rfl⟩ : syracuseStep 3380795 = 5071193) B5071193
theorem B2253863 : Blo 2253435 2253863 := bstep (se 1 (by rfl) ⟨1690397, by rfl⟩ : syracuseStep 2253863 = 3380795) B3380795
theorem B2535601 : Blo 2253435 2535601 := bbase (se 2 (by rfl) ⟨950850, by rfl⟩ : syracuseStep 2535601 = 1901701) (by norm_num)
theorem B3380801 : Blo 2253435 3380801 := bstep (se 2 (by rfl) ⟨1267800, by rfl⟩ : syracuseStep 3380801 = 2535601) B2535601
theorem B2253867 : Blo 2253435 2253867 := bstep (se 1 (by rfl) ⟨1690400, by rfl⟩ : syracuseStep 2253867 = 3380801) B3380801
theorem B2406845 : Blo 2253435 2406845 := bbase (se 3 (by rfl) ⟨451283, by rfl⟩ : syracuseStep 2406845 = 902567) (by norm_num)
theorem B6418253 : Blo 2253435 6418253 := bstep (se 3 (by rfl) ⟨1203422, by rfl⟩ : syracuseStep 6418253 = 2406845) B2406845
theorem B4278835 : Blo 2253435 4278835 := bstep (se 1 (by rfl) ⟨3209126, by rfl⟩ : syracuseStep 4278835 = 6418253) B6418253
theorem B5705113 : Blo 2253435 5705113 := bstep (se 2 (by rfl) ⟨2139417, by rfl⟩ : syracuseStep 5705113 = 4278835) B4278835
theorem B7606817 : Blo 2253435 7606817 := bstep (se 2 (by rfl) ⟨2852556, by rfl⟩ : syracuseStep 7606817 = 5705113) B5705113
theorem B5071211 : Blo 2253435 5071211 := bstep (se 1 (by rfl) ⟨3803408, by rfl⟩ : syracuseStep 5071211 = 7606817) B7606817
theorem B3380807 : Blo 2253435 3380807 := bstep (se 1 (by rfl) ⟨2535605, by rfl⟩ : syracuseStep 3380807 = 5071211) B5071211
theorem B2253871 : Blo 2253435 2253871 := bstep (se 1 (by rfl) ⟨1690403, by rfl⟩ : syracuseStep 2253871 = 3380807) B3380807
theorem B3380813 : Blo 2253435 3380813 := bbase (se 3 (by rfl) ⟨633902, by rfl⟩ : syracuseStep 3380813 = 1267805) (by norm_num)
theorem B2253875 : Blo 2253435 2253875 := bstep (se 1 (by rfl) ⟨1690406, by rfl⟩ : syracuseStep 2253875 = 3380813) B3380813
theorem B5071229 : Blo 2253435 5071229 := bbase (se 3 (by rfl) ⟨950855, by rfl⟩ : syracuseStep 5071229 = 1901711) (by norm_num)
theorem B3380819 : Blo 2253435 3380819 := bstep (se 1 (by rfl) ⟨2535614, by rfl⟩ : syracuseStep 3380819 = 5071229) B5071229
theorem B2253879 : Blo 2253435 2253879 := bstep (se 1 (by rfl) ⟨1690409, by rfl⟩ : syracuseStep 2253879 = 3380819) B3380819
theorem B3803429 : Blo 2253435 3803429 := bbase (se 4 (by rfl) ⟨356571, by rfl⟩ : syracuseStep 3803429 = 713143) (by norm_num)
theorem B2535619 : Blo 2253435 2535619 := bstep (se 1 (by rfl) ⟨1901714, by rfl⟩ : syracuseStep 2535619 = 3803429) B3803429
theorem B3380825 : Blo 2253435 3380825 := bstep (se 2 (by rfl) ⟨1267809, by rfl⟩ : syracuseStep 3380825 = 2535619) B2535619
theorem B2253883 : Blo 2253435 2253883 := bstep (se 1 (by rfl) ⟨1690412, by rfl⟩ : syracuseStep 2253883 = 3380825) B3380825
theorem B3209149 : Blo 2253435 3209149 := bbase (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) (by norm_num)
theorem B17115461 : Blo 2253435 17115461 := bstep (se 4 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 17115461 = 3209149) B3209149
theorem B11410307 : Blo 2253435 11410307 := bstep (se 1 (by rfl) ⟨8557730, by rfl⟩ : syracuseStep 11410307 = 17115461) B17115461
theorem B7606871 : Blo 2253435 7606871 := bstep (se 1 (by rfl) ⟨5705153, by rfl⟩ : syracuseStep 7606871 = 11410307) B11410307
theorem B5071247 : Blo 2253435 5071247 := bstep (se 1 (by rfl) ⟨3803435, by rfl⟩ : syracuseStep 5071247 = 7606871) B7606871
theorem B3380831 : Blo 2253435 3380831 := bstep (se 1 (by rfl) ⟨2535623, by rfl⟩ : syracuseStep 3380831 = 5071247) B5071247
theorem B2253887 : Blo 2253435 2253887 := bstep (se 1 (by rfl) ⟨1690415, by rfl⟩ : syracuseStep 2253887 = 3380831) B3380831
theorem B3380837 : Blo 2253435 3380837 := bbase (se 4 (by rfl) ⟨316953, by rfl⟩ : syracuseStep 3380837 = 633907) (by norm_num)
theorem B2253891 : Blo 2253435 2253891 := bstep (se 1 (by rfl) ⟨1690418, by rfl⟩ : syracuseStep 2253891 = 3380837) B3380837
theorem B5415461 : Blo 2253435 5415461 := bbase (se 4 (by rfl) ⟨507699, by rfl⟩ : syracuseStep 5415461 = 1015399) (by norm_num)
theorem B3610307 : Blo 2253435 3610307 := bstep (se 1 (by rfl) ⟨2707730, by rfl⟩ : syracuseStep 3610307 = 5415461) B5415461
theorem B2406871 : Blo 2253435 2406871 := bstep (se 1 (by rfl) ⟨1805153, by rfl⟩ : syracuseStep 2406871 = 3610307) B3610307
theorem B3209161 : Blo 2253435 3209161 := bstep (se 2 (by rfl) ⟨1203435, by rfl⟩ : syracuseStep 3209161 = 2406871) B2406871
theorem B4278881 : Blo 2253435 4278881 := bstep (se 2 (by rfl) ⟨1604580, by rfl⟩ : syracuseStep 4278881 = 3209161) B3209161
theorem B2852587 : Blo 2253435 2852587 := bstep (se 1 (by rfl) ⟨2139440, by rfl⟩ : syracuseStep 2852587 = 4278881) B4278881
theorem B3803449 : Blo 2253435 3803449 := bstep (se 2 (by rfl) ⟨1426293, by rfl⟩ : syracuseStep 3803449 = 2852587) B2852587
theorem B5071265 : Blo 2253435 5071265 := bstep (se 2 (by rfl) ⟨1901724, by rfl⟩ : syracuseStep 5071265 = 3803449) B3803449
theorem B3380843 : Blo 2253435 3380843 := bstep (se 1 (by rfl) ⟨2535632, by rfl⟩ : syracuseStep 3380843 = 5071265) B5071265
theorem B2253895 : Blo 2253435 2253895 := bstep (se 1 (by rfl) ⟨1690421, by rfl⟩ : syracuseStep 2253895 = 3380843) B3380843
theorem B2535637 : Blo 2253435 2535637 := bbase (se 7 (by rfl) ⟨29714, by rfl⟩ : syracuseStep 2535637 = 59429) (by norm_num)
theorem B3380849 : Blo 2253435 3380849 := bstep (se 2 (by rfl) ⟨1267818, by rfl⟩ : syracuseStep 3380849 = 2535637) B2535637
theorem B2253899 : Blo 2253435 2253899 := bstep (se 1 (by rfl) ⟨1690424, by rfl⟩ : syracuseStep 2253899 = 3380849) B3380849
theorem B2852597 : Blo 2253435 2852597 := bbase (se 5 (by rfl) ⟨133715, by rfl⟩ : syracuseStep 2852597 = 267431) (by norm_num)
theorem B7606925 : Blo 2253435 7606925 := bstep (se 3 (by rfl) ⟨1426298, by rfl⟩ : syracuseStep 7606925 = 2852597) B2852597
theorem B5071283 : Blo 2253435 5071283 := bstep (se 1 (by rfl) ⟨3803462, by rfl⟩ : syracuseStep 5071283 = 7606925) B7606925
theorem B3380855 : Blo 2253435 3380855 := bstep (se 1 (by rfl) ⟨2535641, by rfl⟩ : syracuseStep 3380855 = 5071283) B5071283
theorem B2253903 : Blo 2253435 2253903 := bstep (se 1 (by rfl) ⟨1690427, by rfl⟩ : syracuseStep 2253903 = 3380855) B3380855
theorem B3380861 : Blo 2253435 3380861 := bbase (se 3 (by rfl) ⟨633911, by rfl⟩ : syracuseStep 3380861 = 1267823) (by norm_num)
theorem B2253907 : Blo 2253435 2253907 := bstep (se 1 (by rfl) ⟨1690430, by rfl⟩ : syracuseStep 2253907 = 3380861) B3380861
theorem B5071301 : Blo 2253435 5071301 := bbase (se 4 (by rfl) ⟨475434, by rfl⟩ : syracuseStep 5071301 = 950869) (by norm_num)
theorem B3380867 : Blo 2253435 3380867 := bstep (se 1 (by rfl) ⟨2535650, by rfl⟩ : syracuseStep 3380867 = 5071301) B5071301
theorem B2253911 : Blo 2253435 2253911 := bstep (se 1 (by rfl) ⟨1690433, by rfl⟩ : syracuseStep 2253911 = 3380867) B3380867
theorem B7220677 : Blo 2253435 7220677 := bbase (se 4 (by rfl) ⟨676938, by rfl⟩ : syracuseStep 7220677 = 1353877) (by norm_num)
theorem B9627569 : Blo 2253435 9627569 := bstep (se 2 (by rfl) ⟨3610338, by rfl⟩ : syracuseStep 9627569 = 7220677) B7220677
theorem B6418379 : Blo 2253435 6418379 := bstep (se 1 (by rfl) ⟨4813784, by rfl⟩ : syracuseStep 6418379 = 9627569) B9627569
theorem B4278919 : Blo 2253435 4278919 := bstep (se 1 (by rfl) ⟨3209189, by rfl⟩ : syracuseStep 4278919 = 6418379) B6418379
theorem B5705225 : Blo 2253435 5705225 := bstep (se 2 (by rfl) ⟨2139459, by rfl⟩ : syracuseStep 5705225 = 4278919) B4278919
theorem B3803483 : Blo 2253435 3803483 := bstep (se 1 (by rfl) ⟨2852612, by rfl⟩ : syracuseStep 3803483 = 5705225) B5705225
theorem B2535655 : Blo 2253435 2535655 := bstep (se 1 (by rfl) ⟨1901741, by rfl⟩ : syracuseStep 2535655 = 3803483) B3803483
theorem B3380873 : Blo 2253435 3380873 := bstep (se 2 (by rfl) ⟨1267827, by rfl⟩ : syracuseStep 3380873 = 2535655) B2535655
theorem B2253915 : Blo 2253435 2253915 := bstep (se 1 (by rfl) ⟨1690436, by rfl⟩ : syracuseStep 2253915 = 3380873) B3380873
theorem B11410469 : Blo 2253435 11410469 := bbase (se 4 (by rfl) ⟨1069731, by rfl⟩ : syracuseStep 11410469 = 2139463) (by norm_num)
theorem B7606979 : Blo 2253435 7606979 := bstep (se 1 (by rfl) ⟨5705234, by rfl⟩ : syracuseStep 7606979 = 11410469) B11410469
theorem B5071319 : Blo 2253435 5071319 := bstep (se 1 (by rfl) ⟨3803489, by rfl⟩ : syracuseStep 5071319 = 7606979) B7606979
theorem B3380879 : Blo 2253435 3380879 := bstep (se 1 (by rfl) ⟨2535659, by rfl⟩ : syracuseStep 3380879 = 5071319) B5071319
theorem B2253919 : Blo 2253435 2253919 := bstep (se 1 (by rfl) ⟨1690439, by rfl⟩ : syracuseStep 2253919 = 3380879) B3380879
theorem B3380885 : Blo 2253435 3380885 := bbase (se 6 (by rfl) ⟨79239, by rfl⟩ : syracuseStep 3380885 = 158479) (by norm_num)
theorem B2253923 : Blo 2253435 2253923 := bstep (se 1 (by rfl) ⟨1690442, by rfl⟩ : syracuseStep 2253923 = 3380885) B3380885
theorem B14441429 : Blo 2253435 14441429 := bbase (se 7 (by rfl) ⟨169235, by rfl⟩ : syracuseStep 14441429 = 338471) (by norm_num)
theorem B9627619 : Blo 2253435 9627619 := bstep (se 1 (by rfl) ⟨7220714, by rfl⟩ : syracuseStep 9627619 = 14441429) B14441429
theorem B12836825 : Blo 2253435 12836825 := bstep (se 2 (by rfl) ⟨4813809, by rfl⟩ : syracuseStep 12836825 = 9627619) B9627619
theorem B8557883 : Blo 2253435 8557883 := bstep (se 1 (by rfl) ⟨6418412, by rfl⟩ : syracuseStep 8557883 = 12836825) B12836825
theorem B5705255 : Blo 2253435 5705255 := bstep (se 1 (by rfl) ⟨4278941, by rfl⟩ : syracuseStep 5705255 = 8557883) B8557883
theorem B3803503 : Blo 2253435 3803503 := bstep (se 1 (by rfl) ⟨2852627, by rfl⟩ : syracuseStep 3803503 = 5705255) B5705255
theorem B5071337 : Blo 2253435 5071337 := bstep (se 2 (by rfl) ⟨1901751, by rfl⟩ : syracuseStep 5071337 = 3803503) B3803503
theorem B3380891 : Blo 2253435 3380891 := bstep (se 1 (by rfl) ⟨2535668, by rfl⟩ : syracuseStep 3380891 = 5071337) B5071337
theorem B2253927 : Blo 2253435 2253927 := bstep (se 1 (by rfl) ⟨1690445, by rfl⟩ : syracuseStep 2253927 = 3380891) B3380891
theorem B2535673 : Blo 2253435 2535673 := bbase (se 2 (by rfl) ⟨950877, by rfl⟩ : syracuseStep 2535673 = 1901755) (by norm_num)
theorem B3380897 : Blo 2253435 3380897 := bstep (se 2 (by rfl) ⟨1267836, by rfl⟩ : syracuseStep 3380897 = 2535673) B2535673
theorem B2253931 : Blo 2253435 2253931 := bstep (se 1 (by rfl) ⟨1690448, by rfl⟩ : syracuseStep 2253931 = 3380897) B3380897
theorem B9627653 : Blo 2253435 9627653 := bbase (se 4 (by rfl) ⟨902592, by rfl⟩ : syracuseStep 9627653 = 1805185) (by norm_num)
theorem B6418435 : Blo 2253435 6418435 := bstep (se 1 (by rfl) ⟨4813826, by rfl⟩ : syracuseStep 6418435 = 9627653) B9627653
theorem B8557913 : Blo 2253435 8557913 := bstep (se 2 (by rfl) ⟨3209217, by rfl⟩ : syracuseStep 8557913 = 6418435) B6418435
theorem B5705275 : Blo 2253435 5705275 := bstep (se 1 (by rfl) ⟨4278956, by rfl⟩ : syracuseStep 5705275 = 8557913) B8557913
theorem B7607033 : Blo 2253435 7607033 := bstep (se 2 (by rfl) ⟨2852637, by rfl⟩ : syracuseStep 7607033 = 5705275) B5705275
theorem B5071355 : Blo 2253435 5071355 := bstep (se 1 (by rfl) ⟨3803516, by rfl⟩ : syracuseStep 5071355 = 7607033) B7607033
theorem B3380903 : Blo 2253435 3380903 := bstep (se 1 (by rfl) ⟨2535677, by rfl⟩ : syracuseStep 3380903 = 5071355) B5071355
theorem B2253935 : Blo 2253435 2253935 := bstep (se 1 (by rfl) ⟨1690451, by rfl⟩ : syracuseStep 2253935 = 3380903) B3380903
theorem B3380909 : Blo 2253435 3380909 := bbase (se 3 (by rfl) ⟨633920, by rfl⟩ : syracuseStep 3380909 = 1267841) (by norm_num)
theorem B2253939 : Blo 2253435 2253939 := bstep (se 1 (by rfl) ⟨1690454, by rfl⟩ : syracuseStep 2253939 = 3380909) B3380909
theorem B5071373 : Blo 2253435 5071373 := bbase (se 3 (by rfl) ⟨950882, by rfl⟩ : syracuseStep 5071373 = 1901765) (by norm_num)
theorem B3380915 : Blo 2253435 3380915 := bstep (se 1 (by rfl) ⟨2535686, by rfl⟩ : syracuseStep 3380915 = 5071373) B5071373
theorem B2253943 : Blo 2253435 2253943 := bstep (se 1 (by rfl) ⟨1690457, by rfl⟩ : syracuseStep 2253943 = 3380915) B3380915
theorem B2852653 : Blo 2253435 2852653 := bbase (se 3 (by rfl) ⟨534872, by rfl⟩ : syracuseStep 2852653 = 1069745) (by norm_num)
theorem B3803537 : Blo 2253435 3803537 := bstep (se 2 (by rfl) ⟨1426326, by rfl⟩ : syracuseStep 3803537 = 2852653) B2852653
theorem B2535691 : Blo 2253435 2535691 := bstep (se 1 (by rfl) ⟨1901768, by rfl⟩ : syracuseStep 2535691 = 3803537) B3803537
theorem B3380921 : Blo 2253435 3380921 := bstep (se 2 (by rfl) ⟨1267845, by rfl⟩ : syracuseStep 3380921 = 2535691) B2535691
theorem B2253947 : Blo 2253435 2253947 := bstep (se 1 (by rfl) ⟨1690460, by rfl⟩ : syracuseStep 2253947 = 3380921) B3380921
theorem B2782189 : Blo 2253435 2782189 := bbase (se 3 (by rfl) ⟨521660, by rfl⟩ : syracuseStep 2782189 = 1043321) (by norm_num)
theorem B3709585 : Blo 2253435 3709585 := bstep (se 2 (by rfl) ⟨1391094, by rfl⟩ : syracuseStep 3709585 = 2782189) B2782189
theorem B4946113 : Blo 2253435 4946113 := bstep (se 2 (by rfl) ⟨1854792, by rfl⟩ : syracuseStep 4946113 = 3709585) B3709585
theorem B6594817 : Blo 2253435 6594817 := bstep (se 2 (by rfl) ⟨2473056, by rfl⟩ : syracuseStep 6594817 = 4946113) B4946113
theorem B8793089 : Blo 2253435 8793089 := bstep (se 2 (by rfl) ⟨3297408, by rfl⟩ : syracuseStep 8793089 = 6594817) B6594817
theorem B5862059 : Blo 2253435 5862059 := bstep (se 1 (by rfl) ⟨4396544, by rfl⟩ : syracuseStep 5862059 = 8793089) B8793089
theorem B3908039 : Blo 2253435 3908039 := bstep (se 1 (by rfl) ⟨2931029, by rfl⟩ : syracuseStep 3908039 = 5862059) B5862059
theorem B41685749 : Blo 2253435 41685749 := bstep (se 5 (by rfl) ⟨1954019, by rfl⟩ : syracuseStep 41685749 = 3908039) B3908039
theorem B27790499 : Blo 2253435 27790499 := bstep (se 1 (by rfl) ⟨20842874, by rfl⟩ : syracuseStep 27790499 = 41685749) B41685749
theorem B18526999 : Blo 2253435 18526999 := bstep (se 1 (by rfl) ⟨13895249, by rfl⟩ : syracuseStep 18526999 = 27790499) B27790499
theorem B24702665 : Blo 2253435 24702665 := bstep (se 2 (by rfl) ⟨9263499, by rfl⟩ : syracuseStep 24702665 = 18526999) B18526999
theorem B65873773 : Blo 2253435 65873773 := bstep (se 3 (by rfl) ⟨12351332, by rfl⟩ : syracuseStep 65873773 = 24702665) B24702665
theorem B87831697 : Blo 2253435 87831697 := bstep (se 2 (by rfl) ⟨32936886, by rfl⟩ : syracuseStep 87831697 = 65873773) B65873773
theorem B117108929 : Blo 2253435 117108929 := bstep (se 2 (by rfl) ⟨43915848, by rfl⟩ : syracuseStep 117108929 = 87831697) B87831697
theorem B78072619 : Blo 2253435 78072619 := bstep (se 1 (by rfl) ⟨58554464, by rfl⟩ : syracuseStep 78072619 = 117108929) B117108929
theorem B104096825 : Blo 2253435 104096825 := bstep (se 2 (by rfl) ⟨39036309, by rfl⟩ : syracuseStep 104096825 = 78072619) B78072619
theorem B69397883 : Blo 2253435 69397883 := bstep (se 1 (by rfl) ⟨52048412, by rfl⟩ : syracuseStep 69397883 = 104096825) B104096825
theorem B46265255 : Blo 2253435 46265255 := bstep (se 1 (by rfl) ⟨34698941, by rfl⟩ : syracuseStep 46265255 = 69397883) B69397883
theorem B30843503 : Blo 2253435 30843503 := bstep (se 1 (by rfl) ⟨23132627, by rfl⟩ : syracuseStep 30843503 = 46265255) B46265255
theorem B20562335 : Blo 2253435 20562335 := bstep (se 1 (by rfl) ⟨15421751, by rfl⟩ : syracuseStep 20562335 = 30843503) B30843503
theorem B13708223 : Blo 2253435 13708223 := bstep (se 1 (by rfl) ⟨10281167, by rfl⟩ : syracuseStep 13708223 = 20562335) B20562335
theorem B9138815 : Blo 2253435 9138815 := bstep (se 1 (by rfl) ⟨6854111, by rfl⟩ : syracuseStep 9138815 = 13708223) B13708223
theorem B6092543 : Blo 2253435 6092543 := bstep (se 1 (by rfl) ⟨4569407, by rfl⟩ : syracuseStep 6092543 = 9138815) B9138815
theorem B4061695 : Blo 2253435 4061695 := bstep (se 1 (by rfl) ⟨3046271, by rfl⟩ : syracuseStep 4061695 = 6092543) B6092543
theorem B5415593 : Blo 2253435 5415593 := bstep (se 2 (by rfl) ⟨2030847, by rfl⟩ : syracuseStep 5415593 = 4061695) B4061695
theorem B14441581 : Blo 2253435 14441581 := bstep (se 3 (by rfl) ⟨2707796, by rfl⟩ : syracuseStep 14441581 = 5415593) B5415593
theorem B19255441 : Blo 2253435 19255441 := bstep (se 2 (by rfl) ⟨7220790, by rfl⟩ : syracuseStep 19255441 = 14441581) B14441581
theorem B25673921 : Blo 2253435 25673921 := bstep (se 2 (by rfl) ⟨9627720, by rfl⟩ : syracuseStep 25673921 = 19255441) B19255441
theorem B17115947 : Blo 2253435 17115947 := bstep (se 1 (by rfl) ⟨12836960, by rfl⟩ : syracuseStep 17115947 = 25673921) B25673921
theorem B11410631 : Blo 2253435 11410631 := bstep (se 1 (by rfl) ⟨8557973, by rfl⟩ : syracuseStep 11410631 = 17115947) B17115947
theorem B7607087 : Blo 2253435 7607087 := bstep (se 1 (by rfl) ⟨5705315, by rfl⟩ : syracuseStep 7607087 = 11410631) B11410631
theorem B5071391 : Blo 2253435 5071391 := bstep (se 1 (by rfl) ⟨3803543, by rfl⟩ : syracuseStep 5071391 = 7607087) B7607087
theorem B3380927 : Blo 2253435 3380927 := bstep (se 1 (by rfl) ⟨2535695, by rfl⟩ : syracuseStep 3380927 = 5071391) B5071391
theorem B2253951 : Blo 2253435 2253951 := bstep (se 1 (by rfl) ⟨1690463, by rfl⟩ : syracuseStep 2253951 = 3380927) B3380927
theorem B3380933 : Blo 2253435 3380933 := bbase (se 4 (by rfl) ⟨316962, by rfl⟩ : syracuseStep 3380933 = 633925) (by norm_num)
theorem B2253955 : Blo 2253435 2253955 := bstep (se 1 (by rfl) ⟨1690466, by rfl⟩ : syracuseStep 2253955 = 3380933) B3380933
theorem B3803557 : Blo 2253435 3803557 := bbase (se 4 (by rfl) ⟨356583, by rfl⟩ : syracuseStep 3803557 = 713167) (by norm_num)
theorem B5071409 : Blo 2253435 5071409 := bstep (se 2 (by rfl) ⟨1901778, by rfl⟩ : syracuseStep 5071409 = 3803557) B3803557
theorem B3380939 : Blo 2253435 3380939 := bstep (se 1 (by rfl) ⟨2535704, by rfl⟩ : syracuseStep 3380939 = 5071409) B5071409
theorem B2253959 : Blo 2253435 2253959 := bstep (se 1 (by rfl) ⟨1690469, by rfl⟩ : syracuseStep 2253959 = 3380939) B3380939
theorem B2535709 : Blo 2253435 2535709 := bbase (se 3 (by rfl) ⟨475445, by rfl⟩ : syracuseStep 2535709 = 950891) (by norm_num)
theorem B3380945 : Blo 2253435 3380945 := bstep (se 2 (by rfl) ⟨1267854, by rfl⟩ : syracuseStep 3380945 = 2535709) B2535709
theorem B2253963 : Blo 2253435 2253963 := bstep (se 1 (by rfl) ⟨1690472, by rfl⟩ : syracuseStep 2253963 = 3380945) B3380945
theorem B7607141 : Blo 2253435 7607141 := bbase (se 4 (by rfl) ⟨713169, by rfl⟩ : syracuseStep 7607141 = 1426339) (by norm_num)
theorem B5071427 : Blo 2253435 5071427 := bstep (se 1 (by rfl) ⟨3803570, by rfl⟩ : syracuseStep 5071427 = 7607141) B7607141
theorem B3380951 : Blo 2253435 3380951 := bstep (se 1 (by rfl) ⟨2535713, by rfl⟩ : syracuseStep 3380951 = 5071427) B5071427
theorem B2253967 : Blo 2253435 2253967 := bstep (se 1 (by rfl) ⟨1690475, by rfl⟩ : syracuseStep 2253967 = 3380951) B3380951
theorem B3380957 : Blo 2253435 3380957 := bbase (se 3 (by rfl) ⟨633929, by rfl⟩ : syracuseStep 3380957 = 1267859) (by norm_num)
theorem B2253971 : Blo 2253435 2253971 := bstep (se 1 (by rfl) ⟨1690478, by rfl⟩ : syracuseStep 2253971 = 3380957) B3380957
theorem B5071445 : Blo 2253435 5071445 := bbase (se 8 (by rfl) ⟨29715, by rfl⟩ : syracuseStep 5071445 = 59431) (by norm_num)
theorem B3380963 : Blo 2253435 3380963 := bstep (se 1 (by rfl) ⟨2535722, by rfl⟩ : syracuseStep 3380963 = 5071445) B5071445
theorem B2253975 : Blo 2253435 2253975 := bstep (se 1 (by rfl) ⟨1690481, by rfl⟩ : syracuseStep 2253975 = 3380963) B3380963
theorem B2284733 : Blo 2253435 2284733 := bbase (se 3 (by rfl) ⟨428387, by rfl⟩ : syracuseStep 2284733 = 856775) (by norm_num)
theorem B6092621 : Blo 2253435 6092621 := bstep (se 3 (by rfl) ⟨1142366, by rfl⟩ : syracuseStep 6092621 = 2284733) B2284733
theorem B4061747 : Blo 2253435 4061747 := bstep (se 1 (by rfl) ⟨3046310, by rfl⟩ : syracuseStep 4061747 = 6092621) B6092621
theorem B2707831 : Blo 2253435 2707831 := bstep (se 1 (by rfl) ⟨2030873, by rfl⟩ : syracuseStep 2707831 = 4061747) B4061747
theorem B3610441 : Blo 2253435 3610441 := bstep (se 2 (by rfl) ⟨1353915, by rfl⟩ : syracuseStep 3610441 = 2707831) B2707831
theorem B4813921 : Blo 2253435 4813921 := bstep (se 2 (by rfl) ⟨1805220, by rfl⟩ : syracuseStep 4813921 = 3610441) B3610441
theorem B6418561 : Blo 2253435 6418561 := bstep (se 2 (by rfl) ⟨2406960, by rfl⟩ : syracuseStep 6418561 = 4813921) B4813921
theorem B8558081 : Blo 2253435 8558081 := bstep (se 2 (by rfl) ⟨3209280, by rfl⟩ : syracuseStep 8558081 = 6418561) B6418561
theorem B5705387 : Blo 2253435 5705387 := bstep (se 1 (by rfl) ⟨4279040, by rfl⟩ : syracuseStep 5705387 = 8558081) B8558081
theorem B3803591 : Blo 2253435 3803591 := bstep (se 1 (by rfl) ⟨2852693, by rfl⟩ : syracuseStep 3803591 = 5705387) B5705387
theorem B2535727 : Blo 2253435 2535727 := bstep (se 1 (by rfl) ⟨1901795, by rfl⟩ : syracuseStep 2535727 = 3803591) B3803591
theorem B3380969 : Blo 2253435 3380969 := bstep (se 2 (by rfl) ⟨1267863, by rfl⟩ : syracuseStep 3380969 = 2535727) B2535727
theorem B2253979 : Blo 2253435 2253979 := bstep (se 1 (by rfl) ⟨1690484, by rfl⟩ : syracuseStep 2253979 = 3380969) B3380969
theorem B2570329 : Blo 2253435 2570329 := bbase (se 2 (by rfl) ⟨963873, by rfl⟩ : syracuseStep 2570329 = 1927747) (by norm_num)
theorem B3427105 : Blo 2253435 3427105 := bstep (se 2 (by rfl) ⟨1285164, by rfl⟩ : syracuseStep 3427105 = 2570329) B2570329
theorem B4569473 : Blo 2253435 4569473 := bstep (se 2 (by rfl) ⟨1713552, by rfl⟩ : syracuseStep 4569473 = 3427105) B3427105
theorem B3046315 : Blo 2253435 3046315 := bstep (se 1 (by rfl) ⟨2284736, by rfl⟩ : syracuseStep 3046315 = 4569473) B4569473
theorem B4061753 : Blo 2253435 4061753 := bstep (se 2 (by rfl) ⟨1523157, by rfl⟩ : syracuseStep 4061753 = 3046315) B3046315
theorem B2707835 : Blo 2253435 2707835 := bstep (se 1 (by rfl) ⟨2030876, by rfl⟩ : syracuseStep 2707835 = 4061753) B4061753
theorem B28883573 : Blo 2253435 28883573 := bstep (se 5 (by rfl) ⟨1353917, by rfl⟩ : syracuseStep 28883573 = 2707835) B2707835
theorem B19255715 : Blo 2253435 19255715 := bstep (se 1 (by rfl) ⟨14441786, by rfl⟩ : syracuseStep 19255715 = 28883573) B28883573
theorem B12837143 : Blo 2253435 12837143 := bstep (se 1 (by rfl) ⟨9627857, by rfl⟩ : syracuseStep 12837143 = 19255715) B19255715
theorem B8558095 : Blo 2253435 8558095 := bstep (se 1 (by rfl) ⟨6418571, by rfl⟩ : syracuseStep 8558095 = 12837143) B12837143
theorem B11410793 : Blo 2253435 11410793 := bstep (se 2 (by rfl) ⟨4279047, by rfl⟩ : syracuseStep 11410793 = 8558095) B8558095
theorem B7607195 : Blo 2253435 7607195 := bstep (se 1 (by rfl) ⟨5705396, by rfl⟩ : syracuseStep 7607195 = 11410793) B11410793
theorem B5071463 : Blo 2253435 5071463 := bstep (se 1 (by rfl) ⟨3803597, by rfl⟩ : syracuseStep 5071463 = 7607195) B7607195
theorem B3380975 : Blo 2253435 3380975 := bstep (se 1 (by rfl) ⟨2535731, by rfl⟩ : syracuseStep 3380975 = 5071463) B5071463
theorem B2253983 : Blo 2253435 2253983 := bstep (se 1 (by rfl) ⟨1690487, by rfl⟩ : syracuseStep 2253983 = 3380975) B3380975
theorem B3380981 : Blo 2253435 3380981 := bbase (se 5 (by rfl) ⟨158483, by rfl⟩ : syracuseStep 3380981 = 316967) (by norm_num)
theorem B2253987 : Blo 2253435 2253987 := bstep (se 1 (by rfl) ⟨1690490, by rfl⟩ : syracuseStep 2253987 = 3380981) B3380981
theorem B9627893 : Blo 2253435 9627893 := bbase (se 5 (by rfl) ⟨451307, by rfl⟩ : syracuseStep 9627893 = 902615) (by norm_num)
theorem B6418595 : Blo 2253435 6418595 := bstep (se 1 (by rfl) ⟨4813946, by rfl⟩ : syracuseStep 6418595 = 9627893) B9627893
theorem B4279063 : Blo 2253435 4279063 := bstep (se 1 (by rfl) ⟨3209297, by rfl⟩ : syracuseStep 4279063 = 6418595) B6418595
theorem B5705417 : Blo 2253435 5705417 := bstep (se 2 (by rfl) ⟨2139531, by rfl⟩ : syracuseStep 5705417 = 4279063) B4279063
theorem B3803611 : Blo 2253435 3803611 := bstep (se 1 (by rfl) ⟨2852708, by rfl⟩ : syracuseStep 3803611 = 5705417) B5705417
theorem B5071481 : Blo 2253435 5071481 := bstep (se 2 (by rfl) ⟨1901805, by rfl⟩ : syracuseStep 5071481 = 3803611) B3803611
theorem B3380987 : Blo 2253435 3380987 := bstep (se 1 (by rfl) ⟨2535740, by rfl⟩ : syracuseStep 3380987 = 5071481) B5071481
theorem B2253991 : Blo 2253435 2253991 := bstep (se 1 (by rfl) ⟨1690493, by rfl⟩ : syracuseStep 2253991 = 3380987) B3380987
theorem B2535745 : Blo 2253435 2535745 := bbase (se 2 (by rfl) ⟨950904, by rfl⟩ : syracuseStep 2535745 = 1901809) (by norm_num)
theorem B3380993 : Blo 2253435 3380993 := bstep (se 2 (by rfl) ⟨1267872, by rfl⟩ : syracuseStep 3380993 = 2535745) B2535745
theorem B2253995 : Blo 2253435 2253995 := bstep (se 1 (by rfl) ⟨1690496, by rfl⟩ : syracuseStep 2253995 = 3380993) B3380993
theorem B5705437 : Blo 2253435 5705437 := bbase (se 3 (by rfl) ⟨1069769, by rfl⟩ : syracuseStep 5705437 = 2139539) (by norm_num)
theorem B7607249 : Blo 2253435 7607249 := bstep (se 2 (by rfl) ⟨2852718, by rfl⟩ : syracuseStep 7607249 = 5705437) B5705437
theorem B5071499 : Blo 2253435 5071499 := bstep (se 1 (by rfl) ⟨3803624, by rfl⟩ : syracuseStep 5071499 = 7607249) B7607249
theorem B3380999 : Blo 2253435 3380999 := bstep (se 1 (by rfl) ⟨2535749, by rfl⟩ : syracuseStep 3380999 = 5071499) B5071499
theorem B2253999 : Blo 2253435 2253999 := bstep (se 1 (by rfl) ⟨1690499, by rfl⟩ : syracuseStep 2253999 = 3380999) B3380999
theorem B3381005 : Blo 2253435 3381005 := bbase (se 3 (by rfl) ⟨633938, by rfl⟩ : syracuseStep 3381005 = 1267877) (by norm_num)
theorem B2254003 : Blo 2253435 2254003 := bstep (se 1 (by rfl) ⟨1690502, by rfl⟩ : syracuseStep 2254003 = 3381005) B3381005
theorem B5071517 : Blo 2253435 5071517 := bbase (se 3 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 5071517 = 1901819) (by norm_num)
theorem B3381011 : Blo 2253435 3381011 := bstep (se 1 (by rfl) ⟨2535758, by rfl⟩ : syracuseStep 3381011 = 5071517) B5071517
theorem B2254007 : Blo 2253435 2254007 := bstep (se 1 (by rfl) ⟨1690505, by rfl⟩ : syracuseStep 2254007 = 3381011) B3381011
theorem B3803645 : Blo 2253435 3803645 := bbase (se 3 (by rfl) ⟨713183, by rfl⟩ : syracuseStep 3803645 = 1426367) (by norm_num)
theorem B2535763 : Blo 2253435 2535763 := bstep (se 1 (by rfl) ⟨1901822, by rfl⟩ : syracuseStep 2535763 = 3803645) B3803645
theorem B3381017 : Blo 2253435 3381017 := bstep (se 2 (by rfl) ⟨1267881, by rfl⟩ : syracuseStep 3381017 = 2535763) B2535763
theorem B2254011 : Blo 2253435 2254011 := bstep (se 1 (by rfl) ⟨1690508, by rfl⟩ : syracuseStep 2254011 = 3381017) B3381017
theorem B4813997 : Blo 2253435 4813997 := bbase (se 3 (by rfl) ⟨902624, by rfl⟩ : syracuseStep 4813997 = 1805249) (by norm_num)
theorem B12837325 : Blo 2253435 12837325 := bstep (se 3 (by rfl) ⟨2406998, by rfl⟩ : syracuseStep 12837325 = 4813997) B4813997
theorem B17116433 : Blo 2253435 17116433 := bstep (se 2 (by rfl) ⟨6418662, by rfl⟩ : syracuseStep 17116433 = 12837325) B12837325
theorem B11410955 : Blo 2253435 11410955 := bstep (se 1 (by rfl) ⟨8558216, by rfl⟩ : syracuseStep 11410955 = 17116433) B17116433
theorem B7607303 : Blo 2253435 7607303 := bstep (se 1 (by rfl) ⟨5705477, by rfl⟩ : syracuseStep 7607303 = 11410955) B11410955
theorem B5071535 : Blo 2253435 5071535 := bstep (se 1 (by rfl) ⟨3803651, by rfl⟩ : syracuseStep 5071535 = 7607303) B7607303
theorem B3381023 : Blo 2253435 3381023 := bstep (se 1 (by rfl) ⟨2535767, by rfl⟩ : syracuseStep 3381023 = 5071535) B5071535
theorem B2254015 : Blo 2253435 2254015 := bstep (se 1 (by rfl) ⟨1690511, by rfl⟩ : syracuseStep 2254015 = 3381023) B3381023
theorem B3381029 : Blo 2253435 3381029 := bbase (se 4 (by rfl) ⟨316971, by rfl⟩ : syracuseStep 3381029 = 633943) (by norm_num)
theorem B2254019 : Blo 2253435 2254019 := bstep (se 1 (by rfl) ⟨1690514, by rfl⟩ : syracuseStep 2254019 = 3381029) B3381029
theorem B2852749 : Blo 2253435 2852749 := bbase (se 3 (by rfl) ⟨534890, by rfl⟩ : syracuseStep 2852749 = 1069781) (by norm_num)
theorem B3803665 : Blo 2253435 3803665 := bstep (se 2 (by rfl) ⟨1426374, by rfl⟩ : syracuseStep 3803665 = 2852749) B2852749
theorem B5071553 : Blo 2253435 5071553 := bstep (se 2 (by rfl) ⟨1901832, by rfl⟩ : syracuseStep 5071553 = 3803665) B3803665
theorem B3381035 : Blo 2253435 3381035 := bstep (se 1 (by rfl) ⟨2535776, by rfl⟩ : syracuseStep 3381035 = 5071553) B5071553
theorem B2254023 : Blo 2253435 2254023 := bstep (se 1 (by rfl) ⟨1690517, by rfl⟩ : syracuseStep 2254023 = 3381035) B3381035
theorem B2535781 : Blo 2253435 2535781 := bbase (se 4 (by rfl) ⟨237729, by rfl⟩ : syracuseStep 2535781 = 475459) (by norm_num)
theorem B3381041 : Blo 2253435 3381041 := bstep (se 2 (by rfl) ⟨1267890, by rfl⟩ : syracuseStep 3381041 = 2535781) B2535781
theorem B2254027 : Blo 2253435 2254027 := bstep (se 1 (by rfl) ⟨1690520, by rfl⟩ : syracuseStep 2254027 = 3381041) B3381041
theorem B6418709 : Blo 2253435 6418709 := bbase (se 6 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 6418709 = 300877) (by norm_num)
theorem B4279139 : Blo 2253435 4279139 := bstep (se 1 (by rfl) ⟨3209354, by rfl⟩ : syracuseStep 4279139 = 6418709) B6418709
theorem B2852759 : Blo 2253435 2852759 := bstep (se 1 (by rfl) ⟨2139569, by rfl⟩ : syracuseStep 2852759 = 4279139) B4279139
theorem B7607357 : Blo 2253435 7607357 := bstep (se 3 (by rfl) ⟨1426379, by rfl⟩ : syracuseStep 7607357 = 2852759) B2852759
theorem B5071571 : Blo 2253435 5071571 := bstep (se 1 (by rfl) ⟨3803678, by rfl⟩ : syracuseStep 5071571 = 7607357) B7607357
theorem B3381047 : Blo 2253435 3381047 := bstep (se 1 (by rfl) ⟨2535785, by rfl⟩ : syracuseStep 3381047 = 5071571) B5071571
theorem B2254031 : Blo 2253435 2254031 := bstep (se 1 (by rfl) ⟨1690523, by rfl⟩ : syracuseStep 2254031 = 3381047) B3381047
theorem B3381053 : Blo 2253435 3381053 := bbase (se 3 (by rfl) ⟨633947, by rfl⟩ : syracuseStep 3381053 = 1267895) (by norm_num)
theorem B2254035 : Blo 2253435 2254035 := bstep (se 1 (by rfl) ⟨1690526, by rfl⟩ : syracuseStep 2254035 = 3381053) B3381053
theorem B5071589 : Blo 2253435 5071589 := bbase (se 4 (by rfl) ⟨475461, by rfl⟩ : syracuseStep 5071589 = 950923) (by norm_num)
theorem B3381059 : Blo 2253435 3381059 := bstep (se 1 (by rfl) ⟨2535794, by rfl⟩ : syracuseStep 3381059 = 5071589) B5071589
theorem B2254039 : Blo 2253435 2254039 := bstep (se 1 (by rfl) ⟨1690529, by rfl⟩ : syracuseStep 2254039 = 3381059) B3381059
theorem B5705549 : Blo 2253435 5705549 := bbase (se 3 (by rfl) ⟨1069790, by rfl⟩ : syracuseStep 5705549 = 2139581) (by norm_num)
theorem B3803699 : Blo 2253435 3803699 := bstep (se 1 (by rfl) ⟨2852774, by rfl⟩ : syracuseStep 3803699 = 5705549) B5705549
theorem B2535799 : Blo 2253435 2535799 := bstep (se 1 (by rfl) ⟨1901849, by rfl⟩ : syracuseStep 2535799 = 3803699) B3803699
theorem B3381065 : Blo 2253435 3381065 := bstep (se 2 (by rfl) ⟨1267899, by rfl⟩ : syracuseStep 3381065 = 2535799) B2535799
theorem B2254043 : Blo 2253435 2254043 := bstep (se 1 (by rfl) ⟨1690532, by rfl⟩ : syracuseStep 2254043 = 3381065) B3381065
theorem B2407033 : Blo 2253435 2407033 := bbase (se 2 (by rfl) ⟨902637, by rfl⟩ : syracuseStep 2407033 = 1805275) (by norm_num)
theorem B3209377 : Blo 2253435 3209377 := bstep (se 2 (by rfl) ⟨1203516, by rfl⟩ : syracuseStep 3209377 = 2407033) B2407033
theorem B4279169 : Blo 2253435 4279169 := bstep (se 2 (by rfl) ⟨1604688, by rfl⟩ : syracuseStep 4279169 = 3209377) B3209377
theorem B11411117 : Blo 2253435 11411117 := bstep (se 3 (by rfl) ⟨2139584, by rfl⟩ : syracuseStep 11411117 = 4279169) B4279169
theorem B7607411 : Blo 2253435 7607411 := bstep (se 1 (by rfl) ⟨5705558, by rfl⟩ : syracuseStep 7607411 = 11411117) B11411117
theorem B5071607 : Blo 2253435 5071607 := bstep (se 1 (by rfl) ⟨3803705, by rfl⟩ : syracuseStep 5071607 = 7607411) B7607411
theorem B3381071 : Blo 2253435 3381071 := bstep (se 1 (by rfl) ⟨2535803, by rfl⟩ : syracuseStep 3381071 = 5071607) B5071607
theorem B2254047 : Blo 2253435 2254047 := bstep (se 1 (by rfl) ⟨1690535, by rfl⟩ : syracuseStep 2254047 = 3381071) B3381071
theorem B3381077 : Blo 2253435 3381077 := bbase (se 9 (by rfl) ⟨9905, by rfl⟩ : syracuseStep 3381077 = 19811) (by norm_num)
theorem B2254051 : Blo 2253435 2254051 := bstep (se 1 (by rfl) ⟨1690538, by rfl⟩ : syracuseStep 2254051 = 3381077) B3381077
theorem B7221125 : Blo 2253435 7221125 := bbase (se 4 (by rfl) ⟨676980, by rfl⟩ : syracuseStep 7221125 = 1353961) (by norm_num)
theorem B4814083 : Blo 2253435 4814083 := bstep (se 1 (by rfl) ⟨3610562, by rfl⟩ : syracuseStep 4814083 = 7221125) B7221125
theorem B6418777 : Blo 2253435 6418777 := bstep (se 2 (by rfl) ⟨2407041, by rfl⟩ : syracuseStep 6418777 = 4814083) B4814083
theorem B8558369 : Blo 2253435 8558369 := bstep (se 2 (by rfl) ⟨3209388, by rfl⟩ : syracuseStep 8558369 = 6418777) B6418777
theorem B5705579 : Blo 2253435 5705579 := bstep (se 1 (by rfl) ⟨4279184, by rfl⟩ : syracuseStep 5705579 = 8558369) B8558369
theorem B3803719 : Blo 2253435 3803719 := bstep (se 1 (by rfl) ⟨2852789, by rfl⟩ : syracuseStep 3803719 = 5705579) B5705579
theorem B5071625 : Blo 2253435 5071625 := bstep (se 2 (by rfl) ⟨1901859, by rfl⟩ : syracuseStep 5071625 = 3803719) B3803719
theorem B3381083 : Blo 2253435 3381083 := bstep (se 1 (by rfl) ⟨2535812, by rfl⟩ : syracuseStep 3381083 = 5071625) B5071625
theorem B2254055 : Blo 2253435 2254055 := bstep (se 1 (by rfl) ⟨1690541, by rfl⟩ : syracuseStep 2254055 = 3381083) B3381083
theorem B2535817 : Blo 2253435 2535817 := bbase (se 2 (by rfl) ⟨950931, by rfl⟩ : syracuseStep 2535817 = 1901863) (by norm_num)
theorem B3381089 : Blo 2253435 3381089 := bstep (se 2 (by rfl) ⟨1267908, by rfl⟩ : syracuseStep 3381089 = 2535817) B2535817
theorem B2254059 : Blo 2253435 2254059 := bstep (se 1 (by rfl) ⟨1690544, by rfl⟩ : syracuseStep 2254059 = 3381089) B3381089
theorem B2284817 : Blo 2253435 2284817 := bbase (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) (by norm_num)
theorem B24371381 : Blo 2253435 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B64990349 : Blo 2253435 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B43326899 : Blo 2253435 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B28884599 : Blo 2253435 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B19256399 : Blo 2253435 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B12837599 : Blo 2253435 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B8558399 : Blo 2253435 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B5705599 : Blo 2253435 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B7607465 : Blo 2253435 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B5071643 : Blo 2253435 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B3381095 : Blo 2253435 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B2254063 : Blo 2253435 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B3381101 : Blo 2253435 3381101 := bbase (se 3 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 3381101 = 1267913) (by norm_num)
theorem B2254067 : Blo 2253435 2254067 := bstep (se 1 (by rfl) ⟨1690550, by rfl⟩ : syracuseStep 2254067 = 3381101) B3381101
theorem B5071661 : Blo 2253435 5071661 := bbase (se 3 (by rfl) ⟨950936, by rfl⟩ : syracuseStep 5071661 = 1901873) (by norm_num)
theorem B3381107 : Blo 2253435 3381107 := bstep (se 1 (by rfl) ⟨2535830, by rfl⟩ : syracuseStep 3381107 = 5071661) B5071661
theorem B2254071 : Blo 2253435 2254071 := bstep (se 1 (by rfl) ⟨1690553, by rfl⟩ : syracuseStep 2254071 = 3381107) B3381107
theorem B5415893 : Blo 2253435 5415893 := bbase (se 7 (by rfl) ⟨63467, by rfl⟩ : syracuseStep 5415893 = 126935) (by norm_num)
theorem B3610595 : Blo 2253435 3610595 := bstep (se 1 (by rfl) ⟨2707946, by rfl⟩ : syracuseStep 3610595 = 5415893) B5415893
theorem B9628253 : Blo 2253435 9628253 := bstep (se 3 (by rfl) ⟨1805297, by rfl⟩ : syracuseStep 9628253 = 3610595) B3610595
theorem B6418835 : Blo 2253435 6418835 := bstep (se 1 (by rfl) ⟨4814126, by rfl⟩ : syracuseStep 6418835 = 9628253) B9628253
theorem B4279223 : Blo 2253435 4279223 := bstep (se 1 (by rfl) ⟨3209417, by rfl⟩ : syracuseStep 4279223 = 6418835) B6418835
theorem B2852815 : Blo 2253435 2852815 := bstep (se 1 (by rfl) ⟨2139611, by rfl⟩ : syracuseStep 2852815 = 4279223) B4279223
theorem B3803753 : Blo 2253435 3803753 := bstep (se 2 (by rfl) ⟨1426407, by rfl⟩ : syracuseStep 3803753 = 2852815) B2852815
theorem B2535835 : Blo 2253435 2535835 := bstep (se 1 (by rfl) ⟨1901876, by rfl⟩ : syracuseStep 2535835 = 3803753) B3803753
theorem B3381113 : Blo 2253435 3381113 := bstep (se 2 (by rfl) ⟨1267917, by rfl⟩ : syracuseStep 3381113 = 2535835) B2535835
theorem B2254075 : Blo 2253435 2254075 := bstep (se 1 (by rfl) ⟨1690556, by rfl⟩ : syracuseStep 2254075 = 3381113) B3381113
theorem B9139333 : Blo 2253435 9139333 := bbase (se 4 (by rfl) ⟨856812, by rfl⟩ : syracuseStep 9139333 = 1713625) (by norm_num)
theorem B12185777 : Blo 2253435 12185777 := bstep (se 2 (by rfl) ⟨4569666, by rfl⟩ : syracuseStep 12185777 = 9139333) B9139333
theorem B8123851 : Blo 2253435 8123851 := bstep (se 1 (by rfl) ⟨6092888, by rfl⟩ : syracuseStep 8123851 = 12185777) B12185777
theorem B10831801 : Blo 2253435 10831801 := bstep (se 2 (by rfl) ⟨4061925, by rfl⟩ : syracuseStep 10831801 = 8123851) B8123851
theorem B14442401 : Blo 2253435 14442401 := bstep (se 2 (by rfl) ⟨5415900, by rfl⟩ : syracuseStep 14442401 = 10831801) B10831801
theorem B38513069 : Blo 2253435 38513069 := bstep (se 3 (by rfl) ⟨7221200, by rfl⟩ : syracuseStep 38513069 = 14442401) B14442401
theorem B25675379 : Blo 2253435 25675379 := bstep (se 1 (by rfl) ⟨19256534, by rfl⟩ : syracuseStep 25675379 = 38513069) B38513069
theorem B17116919 : Blo 2253435 17116919 := bstep (se 1 (by rfl) ⟨12837689, by rfl⟩ : syracuseStep 17116919 = 25675379) B25675379
theorem B11411279 : Blo 2253435 11411279 := bstep (se 1 (by rfl) ⟨8558459, by rfl⟩ : syracuseStep 11411279 = 17116919) B17116919
theorem B7607519 : Blo 2253435 7607519 := bstep (se 1 (by rfl) ⟨5705639, by rfl⟩ : syracuseStep 7607519 = 11411279) B11411279
theorem B5071679 : Blo 2253435 5071679 := bstep (se 1 (by rfl) ⟨3803759, by rfl⟩ : syracuseStep 5071679 = 7607519) B7607519
theorem B3381119 : Blo 2253435 3381119 := bstep (se 1 (by rfl) ⟨2535839, by rfl⟩ : syracuseStep 3381119 = 5071679) B5071679
theorem B2254079 : Blo 2253435 2254079 := bstep (se 1 (by rfl) ⟨1690559, by rfl⟩ : syracuseStep 2254079 = 3381119) B3381119
theorem B3381125 : Blo 2253435 3381125 := bbase (se 4 (by rfl) ⟨316980, by rfl⟩ : syracuseStep 3381125 = 633961) (by norm_num)
theorem B2254083 : Blo 2253435 2254083 := bstep (se 1 (by rfl) ⟨1690562, by rfl⟩ : syracuseStep 2254083 = 3381125) B3381125
theorem B3803773 : Blo 2253435 3803773 := bbase (se 3 (by rfl) ⟨713207, by rfl⟩ : syracuseStep 3803773 = 1426415) (by norm_num)
theorem B5071697 : Blo 2253435 5071697 := bstep (se 2 (by rfl) ⟨1901886, by rfl⟩ : syracuseStep 5071697 = 3803773) B3803773
theorem B3381131 : Blo 2253435 3381131 := bstep (se 1 (by rfl) ⟨2535848, by rfl⟩ : syracuseStep 3381131 = 5071697) B5071697
theorem B2254087 : Blo 2253435 2254087 := bstep (se 1 (by rfl) ⟨1690565, by rfl⟩ : syracuseStep 2254087 = 3381131) B3381131
theorem B2535853 : Blo 2253435 2535853 := bbase (se 3 (by rfl) ⟨475472, by rfl⟩ : syracuseStep 2535853 = 950945) (by norm_num)
theorem B3381137 : Blo 2253435 3381137 := bstep (se 2 (by rfl) ⟨1267926, by rfl⟩ : syracuseStep 3381137 = 2535853) B2535853
theorem B2254091 : Blo 2253435 2254091 := bstep (se 1 (by rfl) ⟨1690568, by rfl⟩ : syracuseStep 2254091 = 3381137) B3381137
theorem B7607573 : Blo 2253435 7607573 := bbase (se 6 (by rfl) ⟨178302, by rfl⟩ : syracuseStep 7607573 = 356605) (by norm_num)
theorem B5071715 : Blo 2253435 5071715 := bstep (se 1 (by rfl) ⟨3803786, by rfl⟩ : syracuseStep 5071715 = 7607573) B7607573
theorem B3381143 : Blo 2253435 3381143 := bstep (se 1 (by rfl) ⟨2535857, by rfl⟩ : syracuseStep 3381143 = 5071715) B5071715
theorem B2254095 : Blo 2253435 2254095 := bstep (se 1 (by rfl) ⟨1690571, by rfl⟩ : syracuseStep 2254095 = 3381143) B3381143
theorem B3381149 : Blo 2253435 3381149 := bbase (se 3 (by rfl) ⟨633965, by rfl⟩ : syracuseStep 3381149 = 1267931) (by norm_num)
theorem B2254099 : Blo 2253435 2254099 := bstep (se 1 (by rfl) ⟨1690574, by rfl⟩ : syracuseStep 2254099 = 3381149) B3381149
theorem B5071733 : Blo 2253435 5071733 := bbase (se 5 (by rfl) ⟨237737, by rfl⟩ : syracuseStep 5071733 = 475475) (by norm_num)
theorem B3381155 : Blo 2253435 3381155 := bstep (se 1 (by rfl) ⟨2535866, by rfl⟩ : syracuseStep 3381155 = 5071733) B5071733
theorem B2254103 : Blo 2253435 2254103 := bstep (se 1 (by rfl) ⟨1690577, by rfl⟩ : syracuseStep 2254103 = 3381155) B3381155
theorem B6092965 : Blo 2253435 6092965 := bbase (se 4 (by rfl) ⟨571215, by rfl⟩ : syracuseStep 6092965 = 1142431) (by norm_num)
theorem B32495813 : Blo 2253435 32495813 := bstep (se 4 (by rfl) ⟨3046482, by rfl⟩ : syracuseStep 32495813 = 6092965) B6092965
theorem B21663875 : Blo 2253435 21663875 := bstep (se 1 (by rfl) ⟨16247906, by rfl⟩ : syracuseStep 21663875 = 32495813) B32495813
theorem B14442583 : Blo 2253435 14442583 := bstep (se 1 (by rfl) ⟨10831937, by rfl⟩ : syracuseStep 14442583 = 21663875) B21663875
theorem B19256777 : Blo 2253435 19256777 := bstep (se 2 (by rfl) ⟨7221291, by rfl⟩ : syracuseStep 19256777 = 14442583) B14442583
theorem B12837851 : Blo 2253435 12837851 := bstep (se 1 (by rfl) ⟨9628388, by rfl⟩ : syracuseStep 12837851 = 19256777) B19256777
theorem B8558567 : Blo 2253435 8558567 := bstep (se 1 (by rfl) ⟨6418925, by rfl⟩ : syracuseStep 8558567 = 12837851) B12837851
theorem B5705711 : Blo 2253435 5705711 := bstep (se 1 (by rfl) ⟨4279283, by rfl⟩ : syracuseStep 5705711 = 8558567) B8558567
theorem B3803807 : Blo 2253435 3803807 := bstep (se 1 (by rfl) ⟨2852855, by rfl⟩ : syracuseStep 3803807 = 5705711) B5705711
theorem B2535871 : Blo 2253435 2535871 := bstep (se 1 (by rfl) ⟨1901903, by rfl⟩ : syracuseStep 2535871 = 3803807) B3803807
theorem B3381161 : Blo 2253435 3381161 := bstep (se 2 (by rfl) ⟨1267935, by rfl⟩ : syracuseStep 3381161 = 2535871) B2535871
theorem B2254107 : Blo 2253435 2254107 := bstep (se 1 (by rfl) ⟨1690580, by rfl⟩ : syracuseStep 2254107 = 3381161) B3381161
theorem B8558581 : Blo 2253435 8558581 := bbase (se 5 (by rfl) ⟨401183, by rfl⟩ : syracuseStep 8558581 = 802367) (by norm_num)
theorem B11411441 : Blo 2253435 11411441 := bstep (se 2 (by rfl) ⟨4279290, by rfl⟩ : syracuseStep 11411441 = 8558581) B8558581
theorem B7607627 : Blo 2253435 7607627 := bstep (se 1 (by rfl) ⟨5705720, by rfl⟩ : syracuseStep 7607627 = 11411441) B11411441
theorem B5071751 : Blo 2253435 5071751 := bstep (se 1 (by rfl) ⟨3803813, by rfl⟩ : syracuseStep 5071751 = 7607627) B7607627
theorem B3381167 : Blo 2253435 3381167 := bstep (se 1 (by rfl) ⟨2535875, by rfl⟩ : syracuseStep 3381167 = 5071751) B5071751
theorem B2254111 : Blo 2253435 2254111 := bstep (se 1 (by rfl) ⟨1690583, by rfl⟩ : syracuseStep 2254111 = 3381167) B3381167
theorem B3381173 : Blo 2253435 3381173 := bbase (se 5 (by rfl) ⟨158492, by rfl⟩ : syracuseStep 3381173 = 316985) (by norm_num)
theorem B2254115 : Blo 2253435 2254115 := bstep (se 1 (by rfl) ⟨1690586, by rfl⟩ : syracuseStep 2254115 = 3381173) B3381173
theorem B5705741 : Blo 2253435 5705741 := bbase (se 3 (by rfl) ⟨1069826, by rfl⟩ : syracuseStep 5705741 = 2139653) (by norm_num)
theorem B3803827 : Blo 2253435 3803827 := bstep (se 1 (by rfl) ⟨2852870, by rfl⟩ : syracuseStep 3803827 = 5705741) B5705741
theorem B5071769 : Blo 2253435 5071769 := bstep (se 2 (by rfl) ⟨1901913, by rfl⟩ : syracuseStep 5071769 = 3803827) B3803827
theorem B3381179 : Blo 2253435 3381179 := bstep (se 1 (by rfl) ⟨2535884, by rfl⟩ : syracuseStep 3381179 = 5071769) B5071769
theorem B2254119 : Blo 2253435 2254119 := bstep (se 1 (by rfl) ⟨1690589, by rfl⟩ : syracuseStep 2254119 = 3381179) B3381179
theorem B2535889 : Blo 2253435 2535889 := bbase (se 2 (by rfl) ⟨950958, by rfl⟩ : syracuseStep 2535889 = 1901917) (by norm_num)
theorem B3381185 : Blo 2253435 3381185 := bstep (se 2 (by rfl) ⟨1267944, by rfl⟩ : syracuseStep 3381185 = 2535889) B2535889
theorem B2254123 : Blo 2253435 2254123 := bstep (se 1 (by rfl) ⟨1690592, by rfl⟩ : syracuseStep 2254123 = 3381185) B3381185
theorem B4814237 : Blo 2253435 4814237 := bbase (se 3 (by rfl) ⟨902669, by rfl⟩ : syracuseStep 4814237 = 1805339) (by norm_num)
theorem B3209491 : Blo 2253435 3209491 := bstep (se 1 (by rfl) ⟨2407118, by rfl⟩ : syracuseStep 3209491 = 4814237) B4814237
theorem B4279321 : Blo 2253435 4279321 := bstep (se 2 (by rfl) ⟨1604745, by rfl⟩ : syracuseStep 4279321 = 3209491) B3209491
theorem B5705761 : Blo 2253435 5705761 := bstep (se 2 (by rfl) ⟨2139660, by rfl⟩ : syracuseStep 5705761 = 4279321) B4279321
theorem B7607681 : Blo 2253435 7607681 := bstep (se 2 (by rfl) ⟨2852880, by rfl⟩ : syracuseStep 7607681 = 5705761) B5705761
theorem B5071787 : Blo 2253435 5071787 := bstep (se 1 (by rfl) ⟨3803840, by rfl⟩ : syracuseStep 5071787 = 7607681) B7607681
theorem B3381191 : Blo 2253435 3381191 := bstep (se 1 (by rfl) ⟨2535893, by rfl⟩ : syracuseStep 3381191 = 5071787) B5071787
theorem B2254127 : Blo 2253435 2254127 := bstep (se 1 (by rfl) ⟨1690595, by rfl⟩ : syracuseStep 2254127 = 3381191) B3381191
theorem B3381197 : Blo 2253435 3381197 := bbase (se 3 (by rfl) ⟨633974, by rfl⟩ : syracuseStep 3381197 = 1267949) (by norm_num)
theorem B2254131 : Blo 2253435 2254131 := bstep (se 1 (by rfl) ⟨1690598, by rfl⟩ : syracuseStep 2254131 = 3381197) B3381197
theorem B5071805 : Blo 2253435 5071805 := bbase (se 3 (by rfl) ⟨950963, by rfl⟩ : syracuseStep 5071805 = 1901927) (by norm_num)
theorem B3381203 : Blo 2253435 3381203 := bstep (se 1 (by rfl) ⟨2535902, by rfl⟩ : syracuseStep 3381203 = 5071805) B5071805
theorem B2254135 : Blo 2253435 2254135 := bstep (se 1 (by rfl) ⟨1690601, by rfl⟩ : syracuseStep 2254135 = 3381203) B3381203
theorem B3803861 : Blo 2253435 3803861 := bbase (se 7 (by rfl) ⟨44576, by rfl⟩ : syracuseStep 3803861 = 89153) (by norm_num)
theorem B2535907 : Blo 2253435 2535907 := bstep (se 1 (by rfl) ⟨1901930, by rfl⟩ : syracuseStep 2535907 = 3803861) B3803861
theorem B3381209 : Blo 2253435 3381209 := bstep (se 2 (by rfl) ⟨1267953, by rfl⟩ : syracuseStep 3381209 = 2535907) B2535907
theorem B2254139 : Blo 2253435 2254139 := bstep (se 1 (by rfl) ⟨1690604, by rfl⟩ : syracuseStep 2254139 = 3381209) B3381209
theorem B4569797 : Blo 2253435 4569797 := bbase (se 4 (by rfl) ⟨428418, by rfl⟩ : syracuseStep 4569797 = 856837) (by norm_num)
theorem B12186125 : Blo 2253435 12186125 := bstep (se 3 (by rfl) ⟨2284898, by rfl⟩ : syracuseStep 12186125 = 4569797) B4569797
theorem B8124083 : Blo 2253435 8124083 := bstep (se 1 (by rfl) ⟨6093062, by rfl⟩ : syracuseStep 8124083 = 12186125) B12186125
theorem B5416055 : Blo 2253435 5416055 := bstep (se 1 (by rfl) ⟨4062041, by rfl⟩ : syracuseStep 5416055 = 8124083) B8124083
theorem B3610703 : Blo 2253435 3610703 := bstep (se 1 (by rfl) ⟨2708027, by rfl⟩ : syracuseStep 3610703 = 5416055) B5416055
theorem B9628541 : Blo 2253435 9628541 := bstep (se 3 (by rfl) ⟨1805351, by rfl⟩ : syracuseStep 9628541 = 3610703) B3610703
theorem B6419027 : Blo 2253435 6419027 := bstep (se 1 (by rfl) ⟨4814270, by rfl⟩ : syracuseStep 6419027 = 9628541) B9628541
theorem B17117405 : Blo 2253435 17117405 := bstep (se 3 (by rfl) ⟨3209513, by rfl⟩ : syracuseStep 17117405 = 6419027) B6419027
theorem B11411603 : Blo 2253435 11411603 := bstep (se 1 (by rfl) ⟨8558702, by rfl⟩ : syracuseStep 11411603 = 17117405) B17117405
theorem B7607735 : Blo 2253435 7607735 := bstep (se 1 (by rfl) ⟨5705801, by rfl⟩ : syracuseStep 7607735 = 11411603) B11411603
theorem B5071823 : Blo 2253435 5071823 := bstep (se 1 (by rfl) ⟨3803867, by rfl⟩ : syracuseStep 5071823 = 7607735) B7607735
theorem B3381215 : Blo 2253435 3381215 := bstep (se 1 (by rfl) ⟨2535911, by rfl⟩ : syracuseStep 3381215 = 5071823) B5071823
theorem B2254143 : Blo 2253435 2254143 := bstep (se 1 (by rfl) ⟨1690607, by rfl⟩ : syracuseStep 2254143 = 3381215) B3381215
theorem B3381221 : Blo 2253435 3381221 := bbase (se 4 (by rfl) ⟨316989, by rfl⟩ : syracuseStep 3381221 = 633979) (by norm_num)
theorem B2254147 : Blo 2253435 2254147 := bstep (se 1 (by rfl) ⟨1690610, by rfl⟩ : syracuseStep 2254147 = 3381221) B3381221
theorem B2570521 : Blo 2253435 2570521 := bbase (se 2 (by rfl) ⟨963945, by rfl⟩ : syracuseStep 2570521 = 1927891) (by norm_num)
theorem B3427361 : Blo 2253435 3427361 := bstep (se 2 (by rfl) ⟨1285260, by rfl⟩ : syracuseStep 3427361 = 2570521) B2570521
theorem B2284907 : Blo 2253435 2284907 := bstep (se 1 (by rfl) ⟨1713680, by rfl⟩ : syracuseStep 2284907 = 3427361) B3427361
theorem B6093085 : Blo 2253435 6093085 := bstep (se 3 (by rfl) ⟨1142453, by rfl⟩ : syracuseStep 6093085 = 2284907) B2284907
theorem B8124113 : Blo 2253435 8124113 := bstep (se 2 (by rfl) ⟨3046542, by rfl⟩ : syracuseStep 8124113 = 6093085) B6093085
theorem B5416075 : Blo 2253435 5416075 := bstep (se 1 (by rfl) ⟨4062056, by rfl⟩ : syracuseStep 5416075 = 8124113) B8124113
theorem B7221433 : Blo 2253435 7221433 := bstep (se 2 (by rfl) ⟨2708037, by rfl⟩ : syracuseStep 7221433 = 5416075) B5416075
theorem B9628577 : Blo 2253435 9628577 := bstep (se 2 (by rfl) ⟨3610716, by rfl⟩ : syracuseStep 9628577 = 7221433) B7221433
theorem B6419051 : Blo 2253435 6419051 := bstep (se 1 (by rfl) ⟨4814288, by rfl⟩ : syracuseStep 6419051 = 9628577) B9628577
theorem B4279367 : Blo 2253435 4279367 := bstep (se 1 (by rfl) ⟨3209525, by rfl⟩ : syracuseStep 4279367 = 6419051) B6419051
theorem B2852911 : Blo 2253435 2852911 := bstep (se 1 (by rfl) ⟨2139683, by rfl⟩ : syracuseStep 2852911 = 4279367) B4279367
theorem B3803881 : Blo 2253435 3803881 := bstep (se 2 (by rfl) ⟨1426455, by rfl⟩ : syracuseStep 3803881 = 2852911) B2852911
theorem B5071841 : Blo 2253435 5071841 := bstep (se 2 (by rfl) ⟨1901940, by rfl⟩ : syracuseStep 5071841 = 3803881) B3803881
theorem B3381227 : Blo 2253435 3381227 := bstep (se 1 (by rfl) ⟨2535920, by rfl⟩ : syracuseStep 3381227 = 5071841) B5071841
theorem B2254151 : Blo 2253435 2254151 := bstep (se 1 (by rfl) ⟨1690613, by rfl⟩ : syracuseStep 2254151 = 3381227) B3381227
theorem B2535925 : Blo 2253435 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B3381233 : Blo 2253435 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B2254155 : Blo 2253435 2254155 := bstep (se 1 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 2254155 = 3381233) B3381233
theorem B2852921 : Blo 2253435 2852921 := bbase (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) (by norm_num)
theorem B7607789 : Blo 2253435 7607789 := bstep (se 3 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 7607789 = 2852921) B2852921
theorem B5071859 : Blo 2253435 5071859 := bstep (se 1 (by rfl) ⟨3803894, by rfl⟩ : syracuseStep 5071859 = 7607789) B7607789
theorem B3381239 : Blo 2253435 3381239 := bstep (se 1 (by rfl) ⟨2535929, by rfl⟩ : syracuseStep 3381239 = 5071859) B5071859
theorem B2254159 : Blo 2253435 2254159 := bstep (se 1 (by rfl) ⟨1690619, by rfl⟩ : syracuseStep 2254159 = 3381239) B3381239
theorem B3381245 : Blo 2253435 3381245 := bbase (se 3 (by rfl) ⟨633983, by rfl⟩ : syracuseStep 3381245 = 1267967) (by norm_num)
theorem B2254163 : Blo 2253435 2254163 := bstep (se 1 (by rfl) ⟨1690622, by rfl⟩ : syracuseStep 2254163 = 3381245) B3381245
theorem B5071877 : Blo 2253435 5071877 := bbase (se 4 (by rfl) ⟨475488, by rfl⟩ : syracuseStep 5071877 = 950977) (by norm_num)
theorem B3381251 : Blo 2253435 3381251 := bstep (se 1 (by rfl) ⟨2535938, by rfl⟩ : syracuseStep 3381251 = 5071877) B5071877
theorem B2254167 : Blo 2253435 2254167 := bstep (se 1 (by rfl) ⟨1690625, by rfl⟩ : syracuseStep 2254167 = 3381251) B3381251
theorem B4279405 : Blo 2253435 4279405 := bbase (se 3 (by rfl) ⟨802388, by rfl⟩ : syracuseStep 4279405 = 1604777) (by norm_num)
theorem B5705873 : Blo 2253435 5705873 := bstep (se 2 (by rfl) ⟨2139702, by rfl⟩ : syracuseStep 5705873 = 4279405) B4279405
theorem B3803915 : Blo 2253435 3803915 := bstep (se 1 (by rfl) ⟨2852936, by rfl⟩ : syracuseStep 3803915 = 5705873) B5705873
theorem B2535943 : Blo 2253435 2535943 := bstep (se 1 (by rfl) ⟨1901957, by rfl⟩ : syracuseStep 2535943 = 3803915) B3803915
theorem B3381257 : Blo 2253435 3381257 := bstep (se 2 (by rfl) ⟨1267971, by rfl⟩ : syracuseStep 3381257 = 2535943) B2535943
theorem B2254171 : Blo 2253435 2254171 := bstep (se 1 (by rfl) ⟨1690628, by rfl⟩ : syracuseStep 2254171 = 3381257) B3381257
theorem B11411765 : Blo 2253435 11411765 := bbase (se 5 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 11411765 = 1069853) (by norm_num)
theorem B7607843 : Blo 2253435 7607843 := bstep (se 1 (by rfl) ⟨5705882, by rfl⟩ : syracuseStep 7607843 = 11411765) B11411765
theorem B5071895 : Blo 2253435 5071895 := bstep (se 1 (by rfl) ⟨3803921, by rfl⟩ : syracuseStep 5071895 = 7607843) B7607843
theorem B3381263 : Blo 2253435 3381263 := bstep (se 1 (by rfl) ⟨2535947, by rfl⟩ : syracuseStep 3381263 = 5071895) B5071895
theorem B2254175 : Blo 2253435 2254175 := bstep (se 1 (by rfl) ⟨1690631, by rfl⟩ : syracuseStep 2254175 = 3381263) B3381263
theorem B3381269 : Blo 2253435 3381269 := bbase (se 6 (by rfl) ⟨79248, by rfl⟩ : syracuseStep 3381269 = 158497) (by norm_num)
theorem B2254179 : Blo 2253435 2254179 := bstep (se 1 (by rfl) ⟨1690634, by rfl⟩ : syracuseStep 2254179 = 3381269) B3381269
theorem B2570557 : Blo 2253435 2570557 := bbase (se 3 (by rfl) ⟨481979, by rfl⟩ : syracuseStep 2570557 = 963959) (by norm_num)
theorem B3427409 : Blo 2253435 3427409 := bstep (se 2 (by rfl) ⟨1285278, by rfl⟩ : syracuseStep 3427409 = 2570557) B2570557
theorem B2284939 : Blo 2253435 2284939 := bstep (se 1 (by rfl) ⟨1713704, by rfl⟩ : syracuseStep 2284939 = 3427409) B3427409
theorem B12186341 : Blo 2253435 12186341 := bstep (se 4 (by rfl) ⟨1142469, by rfl⟩ : syracuseStep 12186341 = 2284939) B2284939
theorem B8124227 : Blo 2253435 8124227 := bstep (se 1 (by rfl) ⟨6093170, by rfl⟩ : syracuseStep 8124227 = 12186341) B12186341
theorem B5416151 : Blo 2253435 5416151 := bstep (se 1 (by rfl) ⟨4062113, by rfl⟩ : syracuseStep 5416151 = 8124227) B8124227
theorem B14443069 : Blo 2253435 14443069 := bstep (se 3 (by rfl) ⟨2708075, by rfl⟩ : syracuseStep 14443069 = 5416151) B5416151
theorem B19257425 : Blo 2253435 19257425 := bstep (se 2 (by rfl) ⟨7221534, by rfl⟩ : syracuseStep 19257425 = 14443069) B14443069
theorem B12838283 : Blo 2253435 12838283 := bstep (se 1 (by rfl) ⟨9628712, by rfl⟩ : syracuseStep 12838283 = 19257425) B19257425
theorem B8558855 : Blo 2253435 8558855 := bstep (se 1 (by rfl) ⟨6419141, by rfl⟩ : syracuseStep 8558855 = 12838283) B12838283
theorem B5705903 : Blo 2253435 5705903 := bstep (se 1 (by rfl) ⟨4279427, by rfl⟩ : syracuseStep 5705903 = 8558855) B8558855
theorem B3803935 : Blo 2253435 3803935 := bstep (se 1 (by rfl) ⟨2852951, by rfl⟩ : syracuseStep 3803935 = 5705903) B5705903
theorem B5071913 : Blo 2253435 5071913 := bstep (se 2 (by rfl) ⟨1901967, by rfl⟩ : syracuseStep 5071913 = 3803935) B3803935
theorem B3381275 : Blo 2253435 3381275 := bstep (se 1 (by rfl) ⟨2535956, by rfl⟩ : syracuseStep 3381275 = 5071913) B5071913
theorem B2254183 : Blo 2253435 2254183 := bstep (se 1 (by rfl) ⟨1690637, by rfl⟩ : syracuseStep 2254183 = 3381275) B3381275
theorem B2535961 : Blo 2253435 2535961 := bbase (se 2 (by rfl) ⟨950985, by rfl⟩ : syracuseStep 2535961 = 1901971) (by norm_num)
theorem B3381281 : Blo 2253435 3381281 := bstep (se 2 (by rfl) ⟨1267980, by rfl⟩ : syracuseStep 3381281 = 2535961) B2535961
theorem B2254187 : Blo 2253435 2254187 := bstep (se 1 (by rfl) ⟨1690640, by rfl⟩ : syracuseStep 2254187 = 3381281) B3381281
theorem B8558885 : Blo 2253435 8558885 := bbase (se 4 (by rfl) ⟨802395, by rfl⟩ : syracuseStep 8558885 = 1604791) (by norm_num)
theorem B5705923 : Blo 2253435 5705923 := bstep (se 1 (by rfl) ⟨4279442, by rfl⟩ : syracuseStep 5705923 = 8558885) B8558885
theorem B7607897 : Blo 2253435 7607897 := bstep (se 2 (by rfl) ⟨2852961, by rfl⟩ : syracuseStep 7607897 = 5705923) B5705923
theorem B5071931 : Blo 2253435 5071931 := bstep (se 1 (by rfl) ⟨3803948, by rfl⟩ : syracuseStep 5071931 = 7607897) B7607897
theorem B3381287 : Blo 2253435 3381287 := bstep (se 1 (by rfl) ⟨2535965, by rfl⟩ : syracuseStep 3381287 = 5071931) B5071931
theorem B2254191 : Blo 2253435 2254191 := bstep (se 1 (by rfl) ⟨1690643, by rfl⟩ : syracuseStep 2254191 = 3381287) B3381287
theorem B3381293 : Blo 2253435 3381293 := bbase (se 3 (by rfl) ⟨633992, by rfl⟩ : syracuseStep 3381293 = 1267985) (by norm_num)
theorem B2254195 : Blo 2253435 2254195 := bstep (se 1 (by rfl) ⟨1690646, by rfl⟩ : syracuseStep 2254195 = 3381293) B3381293
theorem B5071949 : Blo 2253435 5071949 := bbase (se 3 (by rfl) ⟨950990, by rfl⟩ : syracuseStep 5071949 = 1901981) (by norm_num)
theorem B3381299 : Blo 2253435 3381299 := bstep (se 1 (by rfl) ⟨2535974, by rfl⟩ : syracuseStep 3381299 = 5071949) B5071949
theorem B2254199 : Blo 2253435 2254199 := bstep (se 1 (by rfl) ⟨1690649, by rfl⟩ : syracuseStep 2254199 = 3381299) B3381299
theorem B2852977 : Blo 2253435 2852977 := bbase (se 2 (by rfl) ⟨1069866, by rfl⟩ : syracuseStep 2852977 = 2139733) (by norm_num)
theorem B3803969 : Blo 2253435 3803969 := bstep (se 2 (by rfl) ⟨1426488, by rfl⟩ : syracuseStep 3803969 = 2852977) B2852977
theorem B2535979 : Blo 2253435 2535979 := bstep (se 1 (by rfl) ⟨1901984, by rfl⟩ : syracuseStep 2535979 = 3803969) B3803969
theorem B3381305 : Blo 2253435 3381305 := bstep (se 2 (by rfl) ⟨1267989, by rfl⟩ : syracuseStep 3381305 = 2535979) B2535979
theorem B2254203 : Blo 2253435 2254203 := bstep (se 1 (by rfl) ⟨1690652, by rfl⟩ : syracuseStep 2254203 = 3381305) B3381305
theorem B3427445 : Blo 2253435 3427445 := bbase (se 5 (by rfl) ⟨160661, by rfl⟩ : syracuseStep 3427445 = 321323) (by norm_num)
theorem B9139853 : Blo 2253435 9139853 := bstep (se 3 (by rfl) ⟨1713722, by rfl⟩ : syracuseStep 9139853 = 3427445) B3427445
theorem B6093235 : Blo 2253435 6093235 := bstep (se 1 (by rfl) ⟨4569926, by rfl⟩ : syracuseStep 6093235 = 9139853) B9139853
theorem B8124313 : Blo 2253435 8124313 := bstep (se 2 (by rfl) ⟨3046617, by rfl⟩ : syracuseStep 8124313 = 6093235) B6093235
theorem B10832417 : Blo 2253435 10832417 := bstep (se 2 (by rfl) ⟨4062156, by rfl⟩ : syracuseStep 10832417 = 8124313) B8124313
theorem B7221611 : Blo 2253435 7221611 := bstep (se 1 (by rfl) ⟨5416208, by rfl⟩ : syracuseStep 7221611 = 10832417) B10832417
theorem B4814407 : Blo 2253435 4814407 := bstep (se 1 (by rfl) ⟨3610805, by rfl⟩ : syracuseStep 4814407 = 7221611) B7221611
theorem B25676837 : Blo 2253435 25676837 := bstep (se 4 (by rfl) ⟨2407203, by rfl⟩ : syracuseStep 25676837 = 4814407) B4814407
theorem B17117891 : Blo 2253435 17117891 := bstep (se 1 (by rfl) ⟨12838418, by rfl⟩ : syracuseStep 17117891 = 25676837) B25676837
theorem B11411927 : Blo 2253435 11411927 := bstep (se 1 (by rfl) ⟨8558945, by rfl⟩ : syracuseStep 11411927 = 17117891) B17117891
theorem B7607951 : Blo 2253435 7607951 := bstep (se 1 (by rfl) ⟨5705963, by rfl⟩ : syracuseStep 7607951 = 11411927) B11411927
theorem B5071967 : Blo 2253435 5071967 := bstep (se 1 (by rfl) ⟨3803975, by rfl⟩ : syracuseStep 5071967 = 7607951) B7607951
theorem B3381311 : Blo 2253435 3381311 := bstep (se 1 (by rfl) ⟨2535983, by rfl⟩ : syracuseStep 3381311 = 5071967) B5071967
theorem B2254207 : Blo 2253435 2254207 := bstep (se 1 (by rfl) ⟨1690655, by rfl⟩ : syracuseStep 2254207 = 3381311) B3381311
theorem B3381317 : Blo 2253435 3381317 := bbase (se 4 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 3381317 = 633997) (by norm_num)
theorem B2254211 : Blo 2253435 2254211 := bstep (se 1 (by rfl) ⟨1690658, by rfl⟩ : syracuseStep 2254211 = 3381317) B3381317
theorem B3803989 : Blo 2253435 3803989 := bbase (se 9 (by rfl) ⟨11144, by rfl⟩ : syracuseStep 3803989 = 22289) (by norm_num)
theorem B5071985 : Blo 2253435 5071985 := bstep (se 2 (by rfl) ⟨1901994, by rfl⟩ : syracuseStep 5071985 = 3803989) B3803989
theorem B3381323 : Blo 2253435 3381323 := bstep (se 1 (by rfl) ⟨2535992, by rfl⟩ : syracuseStep 3381323 = 5071985) B5071985
theorem B2254215 : Blo 2253435 2254215 := bstep (se 1 (by rfl) ⟨1690661, by rfl⟩ : syracuseStep 2254215 = 3381323) B3381323
theorem B2535997 : Blo 2253435 2535997 := bbase (se 3 (by rfl) ⟨475499, by rfl⟩ : syracuseStep 2535997 = 950999) (by norm_num)
theorem B3381329 : Blo 2253435 3381329 := bstep (se 2 (by rfl) ⟨1267998, by rfl⟩ : syracuseStep 3381329 = 2535997) B2535997
theorem B2254219 : Blo 2253435 2254219 := bstep (se 1 (by rfl) ⟨1690664, by rfl⟩ : syracuseStep 2254219 = 3381329) B3381329
theorem B7608005 : Blo 2253435 7608005 := bbase (se 4 (by rfl) ⟨713250, by rfl⟩ : syracuseStep 7608005 = 1426501) (by norm_num)
theorem B5072003 : Blo 2253435 5072003 := bstep (se 1 (by rfl) ⟨3804002, by rfl⟩ : syracuseStep 5072003 = 7608005) B7608005
theorem B3381335 : Blo 2253435 3381335 := bstep (se 1 (by rfl) ⟨2536001, by rfl⟩ : syracuseStep 3381335 = 5072003) B5072003
theorem B2254223 : Blo 2253435 2254223 := bstep (se 1 (by rfl) ⟨1690667, by rfl⟩ : syracuseStep 2254223 = 3381335) B3381335
theorem B3381341 : Blo 2253435 3381341 := bbase (se 3 (by rfl) ⟨634001, by rfl⟩ : syracuseStep 3381341 = 1268003) (by norm_num)
theorem B2254227 : Blo 2253435 2254227 := bstep (se 1 (by rfl) ⟨1690670, by rfl⟩ : syracuseStep 2254227 = 3381341) B3381341
theorem B5072021 : Blo 2253435 5072021 := bbase (se 6 (by rfl) ⟨118875, by rfl⟩ : syracuseStep 5072021 = 237751) (by norm_num)
theorem B3381347 : Blo 2253435 3381347 := bstep (se 1 (by rfl) ⟨2536010, by rfl⟩ : syracuseStep 3381347 = 5072021) B5072021
theorem B2254231 : Blo 2253435 2254231 := bstep (se 1 (by rfl) ⟨1690673, by rfl⟩ : syracuseStep 2254231 = 3381347) B3381347
theorem B3209645 : Blo 2253435 3209645 := bbase (se 3 (by rfl) ⟨601808, by rfl⟩ : syracuseStep 3209645 = 1203617) (by norm_num)
theorem B8559053 : Blo 2253435 8559053 := bstep (se 3 (by rfl) ⟨1604822, by rfl⟩ : syracuseStep 8559053 = 3209645) B3209645
theorem B5706035 : Blo 2253435 5706035 := bstep (se 1 (by rfl) ⟨4279526, by rfl⟩ : syracuseStep 5706035 = 8559053) B8559053
theorem B3804023 : Blo 2253435 3804023 := bstep (se 1 (by rfl) ⟨2853017, by rfl⟩ : syracuseStep 3804023 = 5706035) B5706035
theorem B2536015 : Blo 2253435 2536015 := bstep (se 1 (by rfl) ⟨1902011, by rfl⟩ : syracuseStep 2536015 = 3804023) B3804023
theorem B3381353 : Blo 2253435 3381353 := bstep (se 2 (by rfl) ⟨1268007, by rfl⟩ : syracuseStep 3381353 = 2536015) B2536015
theorem B2254235 : Blo 2253435 2254235 := bstep (se 1 (by rfl) ⟨1690676, by rfl⟩ : syracuseStep 2254235 = 3381353) B3381353
theorem B21665141 : Blo 2253435 21665141 := bbase (se 5 (by rfl) ⟨1015553, by rfl⟩ : syracuseStep 21665141 = 2031107) (by norm_num)
theorem B14443427 : Blo 2253435 14443427 := bstep (se 1 (by rfl) ⟨10832570, by rfl⟩ : syracuseStep 14443427 = 21665141) B21665141
theorem B9628951 : Blo 2253435 9628951 := bstep (se 1 (by rfl) ⟨7221713, by rfl⟩ : syracuseStep 9628951 = 14443427) B14443427
theorem B12838601 : Blo 2253435 12838601 := bstep (se 2 (by rfl) ⟨4814475, by rfl⟩ : syracuseStep 12838601 = 9628951) B9628951
theorem B8559067 : Blo 2253435 8559067 := bstep (se 1 (by rfl) ⟨6419300, by rfl⟩ : syracuseStep 8559067 = 12838601) B12838601
theorem B11412089 : Blo 2253435 11412089 := bstep (se 2 (by rfl) ⟨4279533, by rfl⟩ : syracuseStep 11412089 = 8559067) B8559067
theorem B7608059 : Blo 2253435 7608059 := bstep (se 1 (by rfl) ⟨5706044, by rfl⟩ : syracuseStep 7608059 = 11412089) B11412089
theorem B5072039 : Blo 2253435 5072039 := bstep (se 1 (by rfl) ⟨3804029, by rfl⟩ : syracuseStep 5072039 = 7608059) B7608059
theorem B3381359 : Blo 2253435 3381359 := bstep (se 1 (by rfl) ⟨2536019, by rfl⟩ : syracuseStep 3381359 = 5072039) B5072039
theorem B2254239 : Blo 2253435 2254239 := bstep (se 1 (by rfl) ⟨1690679, by rfl⟩ : syracuseStep 2254239 = 3381359) B3381359
theorem B3381365 : Blo 2253435 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B2254243 : Blo 2253435 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B4279549 : Blo 2253435 4279549 := bbase (se 3 (by rfl) ⟨802415, by rfl⟩ : syracuseStep 4279549 = 1604831) (by norm_num)
theorem B5706065 : Blo 2253435 5706065 := bstep (se 2 (by rfl) ⟨2139774, by rfl⟩ : syracuseStep 5706065 = 4279549) B4279549
theorem B3804043 : Blo 2253435 3804043 := bstep (se 1 (by rfl) ⟨2853032, by rfl⟩ : syracuseStep 3804043 = 5706065) B5706065
theorem B5072057 : Blo 2253435 5072057 := bstep (se 2 (by rfl) ⟨1902021, by rfl⟩ : syracuseStep 5072057 = 3804043) B3804043
theorem B3381371 : Blo 2253435 3381371 := bstep (se 1 (by rfl) ⟨2536028, by rfl⟩ : syracuseStep 3381371 = 5072057) B5072057
theorem B2254247 : Blo 2253435 2254247 := bstep (se 1 (by rfl) ⟨1690685, by rfl⟩ : syracuseStep 2254247 = 3381371) B3381371
theorem B2536033 : Blo 2253435 2536033 := bbase (se 2 (by rfl) ⟨951012, by rfl⟩ : syracuseStep 2536033 = 1902025) (by norm_num)
theorem B3381377 : Blo 2253435 3381377 := bstep (se 2 (by rfl) ⟨1268016, by rfl⟩ : syracuseStep 3381377 = 2536033) B2536033
theorem B2254251 : Blo 2253435 2254251 := bstep (se 1 (by rfl) ⟨1690688, by rfl⟩ : syracuseStep 2254251 = 3381377) B3381377
theorem B5706085 : Blo 2253435 5706085 := bbase (se 4 (by rfl) ⟨534945, by rfl⟩ : syracuseStep 5706085 = 1069891) (by norm_num)
theorem B7608113 : Blo 2253435 7608113 := bstep (se 2 (by rfl) ⟨2853042, by rfl⟩ : syracuseStep 7608113 = 5706085) B5706085
theorem B5072075 : Blo 2253435 5072075 := bstep (se 1 (by rfl) ⟨3804056, by rfl⟩ : syracuseStep 5072075 = 7608113) B7608113
theorem B3381383 : Blo 2253435 3381383 := bstep (se 1 (by rfl) ⟨2536037, by rfl⟩ : syracuseStep 3381383 = 5072075) B5072075
theorem B2254255 : Blo 2253435 2254255 := bstep (se 1 (by rfl) ⟨1690691, by rfl⟩ : syracuseStep 2254255 = 3381383) B3381383
theorem B3381389 : Blo 2253435 3381389 := bbase (se 3 (by rfl) ⟨634010, by rfl⟩ : syracuseStep 3381389 = 1268021) (by norm_num)
theorem B2254259 : Blo 2253435 2254259 := bstep (se 1 (by rfl) ⟨1690694, by rfl⟩ : syracuseStep 2254259 = 3381389) B3381389
theorem B5072093 : Blo 2253435 5072093 := bbase (se 3 (by rfl) ⟨951017, by rfl⟩ : syracuseStep 5072093 = 1902035) (by norm_num)
theorem B3381395 : Blo 2253435 3381395 := bstep (se 1 (by rfl) ⟨2536046, by rfl⟩ : syracuseStep 3381395 = 5072093) B5072093
theorem B2254263 : Blo 2253435 2254263 := bstep (se 1 (by rfl) ⟨1690697, by rfl⟩ : syracuseStep 2254263 = 3381395) B3381395
theorem B3804077 : Blo 2253435 3804077 := bbase (se 3 (by rfl) ⟨713264, by rfl⟩ : syracuseStep 3804077 = 1426529) (by norm_num)
theorem B2536051 : Blo 2253435 2536051 := bstep (se 1 (by rfl) ⟨1902038, by rfl⟩ : syracuseStep 2536051 = 3804077) B3804077
theorem B3381401 : Blo 2253435 3381401 := bstep (se 2 (by rfl) ⟨1268025, by rfl⟩ : syracuseStep 3381401 = 2536051) B2536051
theorem B2254267 : Blo 2253435 2254267 := bstep (se 1 (by rfl) ⟨1690700, by rfl⟩ : syracuseStep 2254267 = 3381401) B3381401
theorem B7521461 : Blo 2253435 7521461 := bbase (se 5 (by rfl) ⟨352568, by rfl⟩ : syracuseStep 7521461 = 705137) (by norm_num)
theorem B5014307 : Blo 2253435 5014307 := bstep (se 1 (by rfl) ⟨3760730, by rfl⟩ : syracuseStep 5014307 = 7521461) B7521461
theorem B13371485 : Blo 2253435 13371485 := bstep (se 3 (by rfl) ⟨2507153, by rfl⟩ : syracuseStep 13371485 = 5014307) B5014307
theorem B35657293 : Blo 2253435 35657293 := bstep (se 3 (by rfl) ⟨6685742, by rfl⟩ : syracuseStep 35657293 = 13371485) B13371485
theorem B47543057 : Blo 2253435 47543057 := bstep (se 2 (by rfl) ⟨17828646, by rfl⟩ : syracuseStep 47543057 = 35657293) B35657293
theorem B31695371 : Blo 2253435 31695371 := bstep (se 1 (by rfl) ⟨23771528, by rfl⟩ : syracuseStep 31695371 = 47543057) B47543057
theorem B21130247 : Blo 2253435 21130247 := bstep (se 1 (by rfl) ⟨15847685, by rfl⟩ : syracuseStep 21130247 = 31695371) B31695371
theorem B56347325 : Blo 2253435 56347325 := bstep (se 3 (by rfl) ⟨10565123, by rfl⟩ : syracuseStep 56347325 = 21130247) B21130247
theorem B37564883 : Blo 2253435 37564883 := bstep (se 1 (by rfl) ⟨28173662, by rfl⟩ : syracuseStep 37564883 = 56347325) B56347325
theorem B25043255 : Blo 2253435 25043255 := bstep (se 1 (by rfl) ⟨18782441, by rfl⟩ : syracuseStep 25043255 = 37564883) B37564883
theorem B16695503 : Blo 2253435 16695503 := bstep (se 1 (by rfl) ⟨12521627, by rfl⟩ : syracuseStep 16695503 = 25043255) B25043255
theorem B11130335 : Blo 2253435 11130335 := bstep (se 1 (by rfl) ⟨8347751, by rfl⟩ : syracuseStep 11130335 = 16695503) B16695503
theorem B7420223 : Blo 2253435 7420223 := bstep (se 1 (by rfl) ⟨5565167, by rfl⟩ : syracuseStep 7420223 = 11130335) B11130335
theorem B4946815 : Blo 2253435 4946815 := bstep (se 1 (by rfl) ⟨3710111, by rfl⟩ : syracuseStep 4946815 = 7420223) B7420223
theorem B6595753 : Blo 2253435 6595753 := bstep (se 2 (by rfl) ⟨2473407, by rfl⟩ : syracuseStep 6595753 = 4946815) B4946815
theorem B8794337 : Blo 2253435 8794337 := bstep (se 2 (by rfl) ⟨3297876, by rfl⟩ : syracuseStep 8794337 = 6595753) B6595753
theorem B93806261 : Blo 2253435 93806261 := bstep (se 5 (by rfl) ⟨4397168, by rfl⟩ : syracuseStep 93806261 = 8794337) B8794337
theorem B62537507 : Blo 2253435 62537507 := bstep (se 1 (by rfl) ⟨46903130, by rfl⟩ : syracuseStep 62537507 = 93806261) B93806261
theorem B41691671 : Blo 2253435 41691671 := bstep (se 1 (by rfl) ⟨31268753, by rfl⟩ : syracuseStep 41691671 = 62537507) B62537507
theorem B27794447 : Blo 2253435 27794447 := bstep (se 1 (by rfl) ⟨20845835, by rfl⟩ : syracuseStep 27794447 = 41691671) B41691671
theorem B18529631 : Blo 2253435 18529631 := bstep (se 1 (by rfl) ⟨13897223, by rfl⟩ : syracuseStep 18529631 = 27794447) B27794447
theorem B12353087 : Blo 2253435 12353087 := bstep (se 1 (by rfl) ⟨9264815, by rfl⟩ : syracuseStep 12353087 = 18529631) B18529631
theorem B8235391 : Blo 2253435 8235391 := bstep (se 1 (by rfl) ⟨6176543, by rfl⟩ : syracuseStep 8235391 = 12353087) B12353087
theorem B10980521 : Blo 2253435 10980521 := bstep (se 2 (by rfl) ⟨4117695, by rfl⟩ : syracuseStep 10980521 = 8235391) B8235391
theorem B7320347 : Blo 2253435 7320347 := bstep (se 1 (by rfl) ⟨5490260, by rfl⟩ : syracuseStep 7320347 = 10980521) B10980521
theorem B4880231 : Blo 2253435 4880231 := bstep (se 1 (by rfl) ⟨3660173, by rfl⟩ : syracuseStep 4880231 = 7320347) B7320347
theorem B3253487 : Blo 2253435 3253487 := bstep (se 1 (by rfl) ⟨2440115, by rfl⟩ : syracuseStep 3253487 = 4880231) B4880231
theorem B8675965 : Blo 2253435 8675965 := bstep (se 3 (by rfl) ⟨1626743, by rfl⟩ : syracuseStep 8675965 = 3253487) B3253487
theorem B11567953 : Blo 2253435 11567953 := bstep (se 2 (by rfl) ⟨4337982, by rfl⟩ : syracuseStep 11567953 = 8675965) B8675965
theorem B61695749 : Blo 2253435 61695749 := bstep (se 4 (by rfl) ⟨5783976, by rfl⟩ : syracuseStep 61695749 = 11567953) B11567953
theorem B41130499 : Blo 2253435 41130499 := bstep (se 1 (by rfl) ⟨30847874, by rfl⟩ : syracuseStep 41130499 = 61695749) B61695749
theorem B54840665 : Blo 2253435 54840665 := bstep (se 2 (by rfl) ⟨20565249, by rfl⟩ : syracuseStep 54840665 = 41130499) B41130499
theorem B146241773 : Blo 2253435 146241773 := bstep (se 3 (by rfl) ⟨27420332, by rfl⟩ : syracuseStep 146241773 = 54840665) B54840665
theorem B97494515 : Blo 2253435 97494515 := bstep (se 1 (by rfl) ⟨73120886, by rfl⟩ : syracuseStep 97494515 = 146241773) B146241773
theorem B64996343 : Blo 2253435 64996343 := bstep (se 1 (by rfl) ⟨48747257, by rfl⟩ : syracuseStep 64996343 = 97494515) B97494515
theorem B43330895 : Blo 2253435 43330895 := bstep (se 1 (by rfl) ⟨32498171, by rfl⟩ : syracuseStep 43330895 = 64996343) B64996343
theorem B28887263 : Blo 2253435 28887263 := bstep (se 1 (by rfl) ⟨21665447, by rfl⟩ : syracuseStep 28887263 = 43330895) B43330895
theorem B19258175 : Blo 2253435 19258175 := bstep (se 1 (by rfl) ⟨14443631, by rfl⟩ : syracuseStep 19258175 = 28887263) B28887263
theorem B12838783 : Blo 2253435 12838783 := bstep (se 1 (by rfl) ⟨9629087, by rfl⟩ : syracuseStep 12838783 = 19258175) B19258175
theorem B17118377 : Blo 2253435 17118377 := bstep (se 2 (by rfl) ⟨6419391, by rfl⟩ : syracuseStep 17118377 = 12838783) B12838783
theorem B11412251 : Blo 2253435 11412251 := bstep (se 1 (by rfl) ⟨8559188, by rfl⟩ : syracuseStep 11412251 = 17118377) B17118377
theorem B7608167 : Blo 2253435 7608167 := bstep (se 1 (by rfl) ⟨5706125, by rfl⟩ : syracuseStep 7608167 = 11412251) B11412251
theorem B5072111 : Blo 2253435 5072111 := bstep (se 1 (by rfl) ⟨3804083, by rfl⟩ : syracuseStep 5072111 = 7608167) B7608167
theorem B3381407 : Blo 2253435 3381407 := bstep (se 1 (by rfl) ⟨2536055, by rfl⟩ : syracuseStep 3381407 = 5072111) B5072111
theorem B2254271 : Blo 2253435 2254271 := bstep (se 1 (by rfl) ⟨1690703, by rfl⟩ : syracuseStep 2254271 = 3381407) B3381407
theorem B3381413 : Blo 2253435 3381413 := bbase (se 4 (by rfl) ⟨317007, by rfl⟩ : syracuseStep 3381413 = 634015) (by norm_num)
theorem B2254275 : Blo 2253435 2254275 := bstep (se 1 (by rfl) ⟨1690706, by rfl⟩ : syracuseStep 2254275 = 3381413) B3381413
theorem B2853073 : Blo 2253435 2853073 := bbase (se 2 (by rfl) ⟨1069902, by rfl⟩ : syracuseStep 2853073 = 2139805) (by norm_num)
theorem B3804097 : Blo 2253435 3804097 := bstep (se 2 (by rfl) ⟨1426536, by rfl⟩ : syracuseStep 3804097 = 2853073) B2853073
theorem B5072129 : Blo 2253435 5072129 := bstep (se 2 (by rfl) ⟨1902048, by rfl⟩ : syracuseStep 5072129 = 3804097) B3804097
theorem B3381419 : Blo 2253435 3381419 := bstep (se 1 (by rfl) ⟨2536064, by rfl⟩ : syracuseStep 3381419 = 5072129) B5072129
theorem B2254279 : Blo 2253435 2254279 := bstep (se 1 (by rfl) ⟨1690709, by rfl⟩ : syracuseStep 2254279 = 3381419) B3381419
theorem B2536069 : Blo 2253435 2536069 := bbase (se 4 (by rfl) ⟨237756, by rfl⟩ : syracuseStep 2536069 = 475513) (by norm_num)
theorem B3381425 : Blo 2253435 3381425 := bstep (se 2 (by rfl) ⟨1268034, by rfl⟩ : syracuseStep 3381425 = 2536069) B2536069
theorem B2254283 : Blo 2253435 2254283 := bstep (se 1 (by rfl) ⟨1690712, by rfl⟩ : syracuseStep 2254283 = 3381425) B3381425
theorem B2708201 : Blo 2253435 2708201 := bbase (se 2 (by rfl) ⟨1015575, by rfl⟩ : syracuseStep 2708201 = 2031151) (by norm_num)
theorem B7221869 : Blo 2253435 7221869 := bstep (se 3 (by rfl) ⟨1354100, by rfl⟩ : syracuseStep 7221869 = 2708201) B2708201
theorem B4814579 : Blo 2253435 4814579 := bstep (se 1 (by rfl) ⟨3610934, by rfl⟩ : syracuseStep 4814579 = 7221869) B7221869
theorem B3209719 : Blo 2253435 3209719 := bstep (se 1 (by rfl) ⟨2407289, by rfl⟩ : syracuseStep 3209719 = 4814579) B4814579
theorem B4279625 : Blo 2253435 4279625 := bstep (se 2 (by rfl) ⟨1604859, by rfl⟩ : syracuseStep 4279625 = 3209719) B3209719
theorem B2853083 : Blo 2253435 2853083 := bstep (se 1 (by rfl) ⟨2139812, by rfl⟩ : syracuseStep 2853083 = 4279625) B4279625
theorem B7608221 : Blo 2253435 7608221 := bstep (se 3 (by rfl) ⟨1426541, by rfl⟩ : syracuseStep 7608221 = 2853083) B2853083
theorem B5072147 : Blo 2253435 5072147 := bstep (se 1 (by rfl) ⟨3804110, by rfl⟩ : syracuseStep 5072147 = 7608221) B7608221
theorem B3381431 : Blo 2253435 3381431 := bstep (se 1 (by rfl) ⟨2536073, by rfl⟩ : syracuseStep 3381431 = 5072147) B5072147
theorem B2254287 : Blo 2253435 2254287 := bstep (se 1 (by rfl) ⟨1690715, by rfl⟩ : syracuseStep 2254287 = 3381431) B3381431
theorem B3381437 : Blo 2253435 3381437 := bbase (se 3 (by rfl) ⟨634019, by rfl⟩ : syracuseStep 3381437 = 1268039) (by norm_num)
theorem B2254291 : Blo 2253435 2254291 := bstep (se 1 (by rfl) ⟨1690718, by rfl⟩ : syracuseStep 2254291 = 3381437) B3381437
theorem B5072165 : Blo 2253435 5072165 := bbase (se 4 (by rfl) ⟨475515, by rfl⟩ : syracuseStep 5072165 = 951031) (by norm_num)
theorem B3381443 : Blo 2253435 3381443 := bstep (se 1 (by rfl) ⟨2536082, by rfl⟩ : syracuseStep 3381443 = 5072165) B5072165
theorem B2254295 : Blo 2253435 2254295 := bstep (se 1 (by rfl) ⟨1690721, by rfl⟩ : syracuseStep 2254295 = 3381443) B3381443
theorem B5706197 : Blo 2253435 5706197 := bbase (se 7 (by rfl) ⟨66869, by rfl⟩ : syracuseStep 5706197 = 133739) (by norm_num)
theorem B3804131 : Blo 2253435 3804131 := bstep (se 1 (by rfl) ⟨2853098, by rfl⟩ : syracuseStep 3804131 = 5706197) B5706197
theorem B2536087 : Blo 2253435 2536087 := bstep (se 1 (by rfl) ⟨1902065, by rfl⟩ : syracuseStep 2536087 = 3804131) B3804131
theorem B3381449 : Blo 2253435 3381449 := bstep (se 2 (by rfl) ⟨1268043, by rfl⟩ : syracuseStep 3381449 = 2536087) B2536087
theorem B2254299 : Blo 2253435 2254299 := bstep (se 1 (by rfl) ⟨1690724, by rfl⟩ : syracuseStep 2254299 = 3381449) B3381449
theorem B5211533 : Blo 2253435 5211533 := bbase (se 3 (by rfl) ⟨977162, by rfl⟩ : syracuseStep 5211533 = 1954325) (by norm_num)
theorem B3474355 : Blo 2253435 3474355 := bstep (se 1 (by rfl) ⟨2605766, by rfl⟩ : syracuseStep 3474355 = 5211533) B5211533
theorem B4632473 : Blo 2253435 4632473 := bstep (se 2 (by rfl) ⟨1737177, by rfl⟩ : syracuseStep 4632473 = 3474355) B3474355
theorem B12353261 : Blo 2253435 12353261 := bstep (se 3 (by rfl) ⟨2316236, by rfl⟩ : syracuseStep 12353261 = 4632473) B4632473
theorem B131768117 : Blo 2253435 131768117 := bstep (se 5 (by rfl) ⟨6176630, by rfl⟩ : syracuseStep 131768117 = 12353261) B12353261
theorem B87845411 : Blo 2253435 87845411 := bstep (se 1 (by rfl) ⟨65884058, by rfl⟩ : syracuseStep 87845411 = 131768117) B131768117
theorem B58563607 : Blo 2253435 58563607 := bstep (se 1 (by rfl) ⟨43922705, by rfl⟩ : syracuseStep 58563607 = 87845411) B87845411
theorem B78084809 : Blo 2253435 78084809 := bstep (se 2 (by rfl) ⟨29281803, by rfl⟩ : syracuseStep 78084809 = 58563607) B58563607
theorem B52056539 : Blo 2253435 52056539 := bstep (se 1 (by rfl) ⟨39042404, by rfl⟩ : syracuseStep 52056539 = 78084809) B78084809
theorem B34704359 : Blo 2253435 34704359 := bstep (se 1 (by rfl) ⟨26028269, by rfl⟩ : syracuseStep 34704359 = 52056539) B52056539
theorem B23136239 : Blo 2253435 23136239 := bstep (se 1 (by rfl) ⟨17352179, by rfl⟩ : syracuseStep 23136239 = 34704359) B34704359
theorem B61696637 : Blo 2253435 61696637 := bstep (se 3 (by rfl) ⟨11568119, by rfl⟩ : syracuseStep 61696637 = 23136239) B23136239
theorem B41131091 : Blo 2253435 41131091 := bstep (se 1 (by rfl) ⟨30848318, by rfl⟩ : syracuseStep 41131091 = 61696637) B61696637
theorem B27420727 : Blo 2253435 27420727 := bstep (se 1 (by rfl) ⟨20565545, by rfl⟩ : syracuseStep 27420727 = 41131091) B41131091
theorem B36560969 : Blo 2253435 36560969 := bstep (se 2 (by rfl) ⟨13710363, by rfl⟩ : syracuseStep 36560969 = 27420727) B27420727
theorem B24373979 : Blo 2253435 24373979 := bstep (se 1 (by rfl) ⟨18280484, by rfl⟩ : syracuseStep 24373979 = 36560969) B36560969
theorem B16249319 : Blo 2253435 16249319 := bstep (se 1 (by rfl) ⟨12186989, by rfl⟩ : syracuseStep 16249319 = 24373979) B24373979
theorem B10832879 : Blo 2253435 10832879 := bstep (se 1 (by rfl) ⟨8124659, by rfl⟩ : syracuseStep 10832879 = 16249319) B16249319
theorem B7221919 : Blo 2253435 7221919 := bstep (se 1 (by rfl) ⟨5416439, by rfl⟩ : syracuseStep 7221919 = 10832879) B10832879
theorem B9629225 : Blo 2253435 9629225 := bstep (se 2 (by rfl) ⟨3610959, by rfl⟩ : syracuseStep 9629225 = 7221919) B7221919
theorem B6419483 : Blo 2253435 6419483 := bstep (se 1 (by rfl) ⟨4814612, by rfl⟩ : syracuseStep 6419483 = 9629225) B9629225
theorem B4279655 : Blo 2253435 4279655 := bstep (se 1 (by rfl) ⟨3209741, by rfl⟩ : syracuseStep 4279655 = 6419483) B6419483
theorem B11412413 : Blo 2253435 11412413 := bstep (se 3 (by rfl) ⟨2139827, by rfl⟩ : syracuseStep 11412413 = 4279655) B4279655
theorem B7608275 : Blo 2253435 7608275 := bstep (se 1 (by rfl) ⟨5706206, by rfl⟩ : syracuseStep 7608275 = 11412413) B11412413
theorem B5072183 : Blo 2253435 5072183 := bstep (se 1 (by rfl) ⟨3804137, by rfl⟩ : syracuseStep 5072183 = 7608275) B7608275
theorem B3381455 : Blo 2253435 3381455 := bstep (se 1 (by rfl) ⟨2536091, by rfl⟩ : syracuseStep 3381455 = 5072183) B5072183
theorem B2254303 : Blo 2253435 2254303 := bstep (se 1 (by rfl) ⟨1690727, by rfl⟩ : syracuseStep 2254303 = 3381455) B3381455
theorem B3381461 : Blo 2253435 3381461 := bbase (se 7 (by rfl) ⟨39626, by rfl⟩ : syracuseStep 3381461 = 79253) (by norm_num)
theorem B2254307 : Blo 2253435 2254307 := bstep (se 1 (by rfl) ⟨1690730, by rfl⟩ : syracuseStep 2254307 = 3381461) B3381461
theorem B3610973 : Blo 2253435 3610973 := bbase (se 3 (by rfl) ⟨677057, by rfl⟩ : syracuseStep 3610973 = 1354115) (by norm_num)
theorem B2407315 : Blo 2253435 2407315 := bstep (se 1 (by rfl) ⟨1805486, by rfl⟩ : syracuseStep 2407315 = 3610973) B3610973
theorem B3209753 : Blo 2253435 3209753 := bstep (se 2 (by rfl) ⟨1203657, by rfl⟩ : syracuseStep 3209753 = 2407315) B2407315
theorem B8559341 : Blo 2253435 8559341 := bstep (se 3 (by rfl) ⟨1604876, by rfl⟩ : syracuseStep 8559341 = 3209753) B3209753
theorem B5706227 : Blo 2253435 5706227 := bstep (se 1 (by rfl) ⟨4279670, by rfl⟩ : syracuseStep 5706227 = 8559341) B8559341
theorem B3804151 : Blo 2253435 3804151 := bstep (se 1 (by rfl) ⟨2853113, by rfl⟩ : syracuseStep 3804151 = 5706227) B5706227
theorem B5072201 : Blo 2253435 5072201 := bstep (se 2 (by rfl) ⟨1902075, by rfl⟩ : syracuseStep 5072201 = 3804151) B3804151
theorem B3381467 : Blo 2253435 3381467 := bstep (se 1 (by rfl) ⟨2536100, by rfl⟩ : syracuseStep 3381467 = 5072201) B5072201
theorem B2254311 : Blo 2253435 2254311 := bstep (se 1 (by rfl) ⟨1690733, by rfl⟩ : syracuseStep 2254311 = 3381467) B3381467
theorem B2536105 : Blo 2253435 2536105 := bbase (se 2 (by rfl) ⟨951039, by rfl⟩ : syracuseStep 2536105 = 1902079) (by norm_num)
theorem B3381473 : Blo 2253435 3381473 := bstep (se 2 (by rfl) ⟨1268052, by rfl⟩ : syracuseStep 3381473 = 2536105) B2536105
theorem B2254315 : Blo 2253435 2254315 := bstep (se 1 (by rfl) ⟨1690736, by rfl⟩ : syracuseStep 2254315 = 3381473) B3381473
theorem B9140309 : Blo 2253435 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B6093539 : Blo 2253435 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B4062359 : Blo 2253435 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B2708239 : Blo 2253435 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B3610985 : Blo 2253435 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B9629293 : Blo 2253435 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B12839057 : Blo 2253435 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B8559371 : Blo 2253435 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B5706247 : Blo 2253435 5706247 := bstep (se 1 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 5706247 = 8559371) B8559371
theorem B7608329 : Blo 2253435 7608329 := bstep (se 2 (by rfl) ⟨2853123, by rfl⟩ : syracuseStep 7608329 = 5706247) B5706247
theorem B5072219 : Blo 2253435 5072219 := bstep (se 1 (by rfl) ⟨3804164, by rfl⟩ : syracuseStep 5072219 = 7608329) B7608329
theorem B3381479 : Blo 2253435 3381479 := bstep (se 1 (by rfl) ⟨2536109, by rfl⟩ : syracuseStep 3381479 = 5072219) B5072219
theorem B2254319 : Blo 2253435 2254319 := bstep (se 1 (by rfl) ⟨1690739, by rfl⟩ : syracuseStep 2254319 = 3381479) B3381479
theorem B3381485 : Blo 2253435 3381485 := bbase (se 3 (by rfl) ⟨634028, by rfl⟩ : syracuseStep 3381485 = 1268057) (by norm_num)
theorem B2254323 : Blo 2253435 2254323 := bstep (se 1 (by rfl) ⟨1690742, by rfl⟩ : syracuseStep 2254323 = 3381485) B3381485
theorem B5072237 : Blo 2253435 5072237 := bbase (se 3 (by rfl) ⟨951044, by rfl⟩ : syracuseStep 5072237 = 1902089) (by norm_num)
theorem B3381491 : Blo 2253435 3381491 := bstep (se 1 (by rfl) ⟨2536118, by rfl⟩ : syracuseStep 3381491 = 5072237) B5072237
theorem B2254327 : Blo 2253435 2254327 := bstep (se 1 (by rfl) ⟨1690745, by rfl⟩ : syracuseStep 2254327 = 3381491) B3381491
theorem B4279709 : Blo 2253435 4279709 := bbase (se 3 (by rfl) ⟨802445, by rfl⟩ : syracuseStep 4279709 = 1604891) (by norm_num)
theorem B2853139 : Blo 2253435 2853139 := bstep (se 1 (by rfl) ⟨2139854, by rfl⟩ : syracuseStep 2853139 = 4279709) B4279709
theorem B3804185 : Blo 2253435 3804185 := bstep (se 2 (by rfl) ⟨1426569, by rfl⟩ : syracuseStep 3804185 = 2853139) B2853139
theorem B2536123 : Blo 2253435 2536123 := bstep (se 1 (by rfl) ⟨1902092, by rfl⟩ : syracuseStep 2536123 = 3804185) B3804185
theorem B3381497 : Blo 2253435 3381497 := bstep (se 2 (by rfl) ⟨1268061, by rfl⟩ : syracuseStep 3381497 = 2536123) B2536123
theorem B2254331 : Blo 2253435 2254331 := bstep (se 1 (by rfl) ⟨1690748, by rfl⟩ : syracuseStep 2254331 = 3381497) B3381497
theorem B2745209 : Blo 2253435 2745209 := bbase (se 2 (by rfl) ⟨1029453, by rfl⟩ : syracuseStep 2745209 = 2058907) (by norm_num)
theorem B7320557 : Blo 2253435 7320557 := bstep (se 3 (by rfl) ⟨1372604, by rfl⟩ : syracuseStep 7320557 = 2745209) B2745209
theorem B4880371 : Blo 2253435 4880371 := bstep (se 1 (by rfl) ⟨3660278, by rfl⟩ : syracuseStep 4880371 = 7320557) B7320557
theorem B6507161 : Blo 2253435 6507161 := bstep (se 2 (by rfl) ⟨2440185, by rfl⟩ : syracuseStep 6507161 = 4880371) B4880371
theorem B4338107 : Blo 2253435 4338107 := bstep (se 1 (by rfl) ⟨3253580, by rfl⟩ : syracuseStep 4338107 = 6507161) B6507161
theorem B2892071 : Blo 2253435 2892071 := bstep (se 1 (by rfl) ⟨2169053, by rfl⟩ : syracuseStep 2892071 = 4338107) B4338107
theorem B7712189 : Blo 2253435 7712189 := bstep (se 3 (by rfl) ⟨1446035, by rfl⟩ : syracuseStep 7712189 = 2892071) B2892071
theorem B5141459 : Blo 2253435 5141459 := bstep (se 1 (by rfl) ⟨3856094, by rfl⟩ : syracuseStep 5141459 = 7712189) B7712189
theorem B3427639 : Blo 2253435 3427639 := bstep (se 1 (by rfl) ⟨2570729, by rfl⟩ : syracuseStep 3427639 = 5141459) B5141459
theorem B18280741 : Blo 2253435 18280741 := bstep (se 4 (by rfl) ⟨1713819, by rfl⟩ : syracuseStep 18280741 = 3427639) B3427639
theorem B24374321 : Blo 2253435 24374321 := bstep (se 2 (by rfl) ⟨9140370, by rfl⟩ : syracuseStep 24374321 = 18280741) B18280741
theorem B16249547 : Blo 2253435 16249547 := bstep (se 1 (by rfl) ⟨12187160, by rfl⟩ : syracuseStep 16249547 = 24374321) B24374321
theorem B10833031 : Blo 2253435 10833031 := bstep (se 1 (by rfl) ⟨8124773, by rfl⟩ : syracuseStep 10833031 = 16249547) B16249547
theorem B57776165 : Blo 2253435 57776165 := bstep (se 4 (by rfl) ⟨5416515, by rfl⟩ : syracuseStep 57776165 = 10833031) B10833031
theorem B38517443 : Blo 2253435 38517443 := bstep (se 1 (by rfl) ⟨28888082, by rfl⟩ : syracuseStep 38517443 = 57776165) B57776165
theorem B25678295 : Blo 2253435 25678295 := bstep (se 1 (by rfl) ⟨19258721, by rfl⟩ : syracuseStep 25678295 = 38517443) B38517443
theorem B17118863 : Blo 2253435 17118863 := bstep (se 1 (by rfl) ⟨12839147, by rfl⟩ : syracuseStep 17118863 = 25678295) B25678295
theorem B11412575 : Blo 2253435 11412575 := bstep (se 1 (by rfl) ⟨8559431, by rfl⟩ : syracuseStep 11412575 = 17118863) B17118863
theorem B7608383 : Blo 2253435 7608383 := bstep (se 1 (by rfl) ⟨5706287, by rfl⟩ : syracuseStep 7608383 = 11412575) B11412575
theorem B5072255 : Blo 2253435 5072255 := bstep (se 1 (by rfl) ⟨3804191, by rfl⟩ : syracuseStep 5072255 = 7608383) B7608383
theorem B3381503 : Blo 2253435 3381503 := bstep (se 1 (by rfl) ⟨2536127, by rfl⟩ : syracuseStep 3381503 = 5072255) B5072255
theorem B2254335 : Blo 2253435 2254335 := bstep (se 1 (by rfl) ⟨1690751, by rfl⟩ : syracuseStep 2254335 = 3381503) B3381503
theorem B3381509 : Blo 2253435 3381509 := bbase (se 4 (by rfl) ⟨317016, by rfl⟩ : syracuseStep 3381509 = 634033) (by norm_num)
theorem B2254339 : Blo 2253435 2254339 := bstep (se 1 (by rfl) ⟨1690754, by rfl⟩ : syracuseStep 2254339 = 3381509) B3381509
theorem B3804205 : Blo 2253435 3804205 := bbase (se 3 (by rfl) ⟨713288, by rfl⟩ : syracuseStep 3804205 = 1426577) (by norm_num)
theorem B5072273 : Blo 2253435 5072273 := bstep (se 2 (by rfl) ⟨1902102, by rfl⟩ : syracuseStep 5072273 = 3804205) B3804205
theorem B3381515 : Blo 2253435 3381515 := bstep (se 1 (by rfl) ⟨2536136, by rfl⟩ : syracuseStep 3381515 = 5072273) B5072273
theorem B2254343 : Blo 2253435 2254343 := bstep (se 1 (by rfl) ⟨1690757, by rfl⟩ : syracuseStep 2254343 = 3381515) B3381515
theorem B2536141 : Blo 2253435 2536141 := bbase (se 3 (by rfl) ⟨475526, by rfl⟩ : syracuseStep 2536141 = 951053) (by norm_num)
theorem B3381521 : Blo 2253435 3381521 := bstep (se 2 (by rfl) ⟨1268070, by rfl⟩ : syracuseStep 3381521 = 2536141) B2536141
theorem B2254347 : Blo 2253435 2254347 := bstep (se 1 (by rfl) ⟨1690760, by rfl⟩ : syracuseStep 2254347 = 3381521) B3381521
theorem B7608437 : Blo 2253435 7608437 := bbase (se 5 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 7608437 = 713291) (by norm_num)
theorem B5072291 : Blo 2253435 5072291 := bstep (se 1 (by rfl) ⟨3804218, by rfl⟩ : syracuseStep 5072291 = 7608437) B7608437
theorem B3381527 : Blo 2253435 3381527 := bstep (se 1 (by rfl) ⟨2536145, by rfl⟩ : syracuseStep 3381527 = 5072291) B5072291
theorem B2254351 : Blo 2253435 2254351 := bstep (se 1 (by rfl) ⟨1690763, by rfl⟩ : syracuseStep 2254351 = 3381527) B3381527
theorem B3381533 : Blo 2253435 3381533 := bbase (se 3 (by rfl) ⟨634037, by rfl⟩ : syracuseStep 3381533 = 1268075) (by norm_num)
theorem B2254355 : Blo 2253435 2254355 := bstep (se 1 (by rfl) ⟨1690766, by rfl⟩ : syracuseStep 2254355 = 3381533) B3381533
theorem B5072309 : Blo 2253435 5072309 := bbase (se 5 (by rfl) ⟨237764, by rfl⟩ : syracuseStep 5072309 = 475529) (by norm_num)
theorem B3381539 : Blo 2253435 3381539 := bstep (se 1 (by rfl) ⟨2536154, by rfl⟩ : syracuseStep 3381539 = 5072309) B5072309
theorem B2254359 : Blo 2253435 2254359 := bstep (se 1 (by rfl) ⟨1690769, by rfl⟩ : syracuseStep 2254359 = 3381539) B3381539
theorem B4814741 : Blo 2253435 4814741 := bbase (se 6 (by rfl) ⟨112845, by rfl⟩ : syracuseStep 4814741 = 225691) (by norm_num)
theorem B12839309 : Blo 2253435 12839309 := bstep (se 3 (by rfl) ⟨2407370, by rfl⟩ : syracuseStep 12839309 = 4814741) B4814741
theorem B8559539 : Blo 2253435 8559539 := bstep (se 1 (by rfl) ⟨6419654, by rfl⟩ : syracuseStep 8559539 = 12839309) B12839309
theorem B5706359 : Blo 2253435 5706359 := bstep (se 1 (by rfl) ⟨4279769, by rfl⟩ : syracuseStep 5706359 = 8559539) B8559539
theorem B3804239 : Blo 2253435 3804239 := bstep (se 1 (by rfl) ⟨2853179, by rfl⟩ : syracuseStep 3804239 = 5706359) B5706359
theorem B2536159 : Blo 2253435 2536159 := bstep (se 1 (by rfl) ⟨1902119, by rfl⟩ : syracuseStep 2536159 = 3804239) B3804239
theorem B3381545 : Blo 2253435 3381545 := bstep (se 2 (by rfl) ⟨1268079, by rfl⟩ : syracuseStep 3381545 = 2536159) B2536159
theorem B2254363 : Blo 2253435 2254363 := bstep (se 1 (by rfl) ⟨1690772, by rfl⟩ : syracuseStep 2254363 = 3381545) B3381545
theorem B4814749 : Blo 2253435 4814749 := bbase (se 3 (by rfl) ⟨902765, by rfl⟩ : syracuseStep 4814749 = 1805531) (by norm_num)
theorem B6419665 : Blo 2253435 6419665 := bstep (se 2 (by rfl) ⟨2407374, by rfl⟩ : syracuseStep 6419665 = 4814749) B4814749
theorem B8559553 : Blo 2253435 8559553 := bstep (se 2 (by rfl) ⟨3209832, by rfl⟩ : syracuseStep 8559553 = 6419665) B6419665
theorem B11412737 : Blo 2253435 11412737 := bstep (se 2 (by rfl) ⟨4279776, by rfl⟩ : syracuseStep 11412737 = 8559553) B8559553
theorem B7608491 : Blo 2253435 7608491 := bstep (se 1 (by rfl) ⟨5706368, by rfl⟩ : syracuseStep 7608491 = 11412737) B11412737
theorem B5072327 : Blo 2253435 5072327 := bstep (se 1 (by rfl) ⟨3804245, by rfl⟩ : syracuseStep 5072327 = 7608491) B7608491
theorem B3381551 : Blo 2253435 3381551 := bstep (se 1 (by rfl) ⟨2536163, by rfl⟩ : syracuseStep 3381551 = 5072327) B5072327
theorem B2254367 : Blo 2253435 2254367 := bstep (se 1 (by rfl) ⟨1690775, by rfl⟩ : syracuseStep 2254367 = 3381551) B3381551
theorem B3381557 : Blo 2253435 3381557 := bbase (se 5 (by rfl) ⟨158510, by rfl⟩ : syracuseStep 3381557 = 317021) (by norm_num)
theorem B2254371 : Blo 2253435 2254371 := bstep (se 1 (by rfl) ⟨1690778, by rfl⟩ : syracuseStep 2254371 = 3381557) B3381557
theorem B5706389 : Blo 2253435 5706389 := bbase (se 6 (by rfl) ⟨133743, by rfl⟩ : syracuseStep 5706389 = 267487) (by norm_num)
theorem B3804259 : Blo 2253435 3804259 := bstep (se 1 (by rfl) ⟨2853194, by rfl⟩ : syracuseStep 3804259 = 5706389) B5706389
theorem B5072345 : Blo 2253435 5072345 := bstep (se 2 (by rfl) ⟨1902129, by rfl⟩ : syracuseStep 5072345 = 3804259) B3804259
theorem B3381563 : Blo 2253435 3381563 := bstep (se 1 (by rfl) ⟨2536172, by rfl⟩ : syracuseStep 3381563 = 5072345) B5072345
theorem B2254375 : Blo 2253435 2254375 := bstep (se 1 (by rfl) ⟨1690781, by rfl⟩ : syracuseStep 2254375 = 3381563) B3381563
theorem B2536177 : Blo 2253435 2536177 := bbase (se 2 (by rfl) ⟨951066, by rfl⟩ : syracuseStep 2536177 = 1902133) (by norm_num)
theorem B3381569 : Blo 2253435 3381569 := bstep (se 2 (by rfl) ⟨1268088, by rfl⟩ : syracuseStep 3381569 = 2536177) B2536177
theorem B2254379 : Blo 2253435 2254379 := bstep (se 1 (by rfl) ⟨1690784, by rfl⟩ : syracuseStep 2254379 = 3381569) B3381569
theorem B9760949 : Blo 2253435 9760949 := bbase (se 5 (by rfl) ⟨457544, by rfl⟩ : syracuseStep 9760949 = 915089) (by norm_num)
theorem B6507299 : Blo 2253435 6507299 := bstep (se 1 (by rfl) ⟨4880474, by rfl⟩ : syracuseStep 6507299 = 9760949) B9760949
theorem B4338199 : Blo 2253435 4338199 := bstep (se 1 (by rfl) ⟨3253649, by rfl⟩ : syracuseStep 4338199 = 6507299) B6507299
theorem B5784265 : Blo 2253435 5784265 := bstep (se 2 (by rfl) ⟨2169099, by rfl⟩ : syracuseStep 5784265 = 4338199) B4338199
theorem B7712353 : Blo 2253435 7712353 := bstep (se 2 (by rfl) ⟨2892132, by rfl⟩ : syracuseStep 7712353 = 5784265) B5784265
theorem B41132549 : Blo 2253435 41132549 := bstep (se 4 (by rfl) ⟨3856176, by rfl⟩ : syracuseStep 41132549 = 7712353) B7712353
theorem B109686797 : Blo 2253435 109686797 := bstep (se 3 (by rfl) ⟨20566274, by rfl⟩ : syracuseStep 109686797 = 41132549) B41132549
theorem B73124531 : Blo 2253435 73124531 := bstep (se 1 (by rfl) ⟨54843398, by rfl⟩ : syracuseStep 73124531 = 109686797) B109686797
theorem B48749687 : Blo 2253435 48749687 := bstep (se 1 (by rfl) ⟨36562265, by rfl⟩ : syracuseStep 48749687 = 73124531) B73124531
theorem B32499791 : Blo 2253435 32499791 := bstep (se 1 (by rfl) ⟨24374843, by rfl⟩ : syracuseStep 32499791 = 48749687) B48749687
theorem B21666527 : Blo 2253435 21666527 := bstep (se 1 (by rfl) ⟨16249895, by rfl⟩ : syracuseStep 21666527 = 32499791) B32499791
theorem B14444351 : Blo 2253435 14444351 := bstep (se 1 (by rfl) ⟨10833263, by rfl⟩ : syracuseStep 14444351 = 21666527) B21666527
theorem B9629567 : Blo 2253435 9629567 := bstep (se 1 (by rfl) ⟨7222175, by rfl⟩ : syracuseStep 9629567 = 14444351) B14444351
theorem B6419711 : Blo 2253435 6419711 := bstep (se 1 (by rfl) ⟨4814783, by rfl⟩ : syracuseStep 6419711 = 9629567) B9629567
theorem B4279807 : Blo 2253435 4279807 := bstep (se 1 (by rfl) ⟨3209855, by rfl⟩ : syracuseStep 4279807 = 6419711) B6419711
theorem B5706409 : Blo 2253435 5706409 := bstep (se 2 (by rfl) ⟨2139903, by rfl⟩ : syracuseStep 5706409 = 4279807) B4279807
theorem B7608545 : Blo 2253435 7608545 := bstep (se 2 (by rfl) ⟨2853204, by rfl⟩ : syracuseStep 7608545 = 5706409) B5706409
theorem B5072363 : Blo 2253435 5072363 := bstep (se 1 (by rfl) ⟨3804272, by rfl⟩ : syracuseStep 5072363 = 7608545) B7608545
theorem B3381575 : Blo 2253435 3381575 := bstep (se 1 (by rfl) ⟨2536181, by rfl⟩ : syracuseStep 3381575 = 5072363) B5072363
theorem B2254383 : Blo 2253435 2254383 := bstep (se 1 (by rfl) ⟨1690787, by rfl⟩ : syracuseStep 2254383 = 3381575) B3381575
theorem B3381581 : Blo 2253435 3381581 := bbase (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) (by norm_num)
theorem B2254387 : Blo 2253435 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B5072381 : Blo 2253435 5072381 := bbase (se 3 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 5072381 = 1902143) (by norm_num)
theorem B3381587 : Blo 2253435 3381587 := bstep (se 1 (by rfl) ⟨2536190, by rfl⟩ : syracuseStep 3381587 = 5072381) B5072381
theorem B2254391 : Blo 2253435 2254391 := bstep (se 1 (by rfl) ⟨1690793, by rfl⟩ : syracuseStep 2254391 = 3381587) B3381587
theorem B3804293 : Blo 2253435 3804293 := bbase (se 4 (by rfl) ⟨356652, by rfl⟩ : syracuseStep 3804293 = 713305) (by norm_num)
theorem B2536195 : Blo 2253435 2536195 := bstep (se 1 (by rfl) ⟨1902146, by rfl⟩ : syracuseStep 2536195 = 3804293) B3804293
theorem B3381593 : Blo 2253435 3381593 := bstep (se 2 (by rfl) ⟨1268097, by rfl⟩ : syracuseStep 3381593 = 2536195) B2536195
theorem B2254395 : Blo 2253435 2254395 := bstep (se 1 (by rfl) ⟨1690796, by rfl⟩ : syracuseStep 2254395 = 3381593) B3381593
theorem B17119349 : Blo 2253435 17119349 := bbase (se 5 (by rfl) ⟨802469, by rfl⟩ : syracuseStep 17119349 = 1604939) (by norm_num)
theorem B11412899 : Blo 2253435 11412899 := bstep (se 1 (by rfl) ⟨8559674, by rfl⟩ : syracuseStep 11412899 = 17119349) B17119349
theorem B7608599 : Blo 2253435 7608599 := bstep (se 1 (by rfl) ⟨5706449, by rfl⟩ : syracuseStep 7608599 = 11412899) B11412899
theorem B5072399 : Blo 2253435 5072399 := bstep (se 1 (by rfl) ⟨3804299, by rfl⟩ : syracuseStep 5072399 = 7608599) B7608599
theorem B3381599 : Blo 2253435 3381599 := bstep (se 1 (by rfl) ⟨2536199, by rfl⟩ : syracuseStep 3381599 = 5072399) B5072399
theorem B2254399 : Blo 2253435 2254399 := bstep (se 1 (by rfl) ⟨1690799, by rfl⟩ : syracuseStep 2254399 = 3381599) B3381599
theorem B3381605 : Blo 2253435 3381605 := bbase (se 4 (by rfl) ⟨317025, by rfl⟩ : syracuseStep 3381605 = 634051) (by norm_num)
theorem B2254403 : Blo 2253435 2254403 := bstep (se 1 (by rfl) ⟨1690802, by rfl⟩ : syracuseStep 2254403 = 3381605) B3381605
theorem B4279853 : Blo 2253435 4279853 := bbase (se 3 (by rfl) ⟨802472, by rfl⟩ : syracuseStep 4279853 = 1604945) (by norm_num)
theorem B2853235 : Blo 2253435 2853235 := bstep (se 1 (by rfl) ⟨2139926, by rfl⟩ : syracuseStep 2853235 = 4279853) B4279853
theorem B3804313 : Blo 2253435 3804313 := bstep (se 2 (by rfl) ⟨1426617, by rfl⟩ : syracuseStep 3804313 = 2853235) B2853235
theorem B5072417 : Blo 2253435 5072417 := bstep (se 2 (by rfl) ⟨1902156, by rfl⟩ : syracuseStep 5072417 = 3804313) B3804313
theorem B3381611 : Blo 2253435 3381611 := bstep (se 1 (by rfl) ⟨2536208, by rfl⟩ : syracuseStep 3381611 = 5072417) B5072417
theorem B2254407 : Blo 2253435 2254407 := bstep (se 1 (by rfl) ⟨1690805, by rfl⟩ : syracuseStep 2254407 = 3381611) B3381611
theorem B2536213 : Blo 2253435 2536213 := bbase (se 6 (by rfl) ⟨59442, by rfl⟩ : syracuseStep 2536213 = 118885) (by norm_num)
theorem B3381617 : Blo 2253435 3381617 := bstep (se 2 (by rfl) ⟨1268106, by rfl⟩ : syracuseStep 3381617 = 2536213) B2536213
theorem B2254411 : Blo 2253435 2254411 := bstep (se 1 (by rfl) ⟨1690808, by rfl⟩ : syracuseStep 2254411 = 3381617) B3381617
theorem B2853245 : Blo 2253435 2853245 := bbase (se 3 (by rfl) ⟨534983, by rfl⟩ : syracuseStep 2853245 = 1069967) (by norm_num)
theorem B7608653 : Blo 2253435 7608653 := bstep (se 3 (by rfl) ⟨1426622, by rfl⟩ : syracuseStep 7608653 = 2853245) B2853245
theorem B5072435 : Blo 2253435 5072435 := bstep (se 1 (by rfl) ⟨3804326, by rfl⟩ : syracuseStep 5072435 = 7608653) B7608653
theorem B3381623 : Blo 2253435 3381623 := bstep (se 1 (by rfl) ⟨2536217, by rfl⟩ : syracuseStep 3381623 = 5072435) B5072435
theorem B2254415 : Blo 2253435 2254415 := bstep (se 1 (by rfl) ⟨1690811, by rfl⟩ : syracuseStep 2254415 = 3381623) B3381623
theorem B3381629 : Blo 2253435 3381629 := bbase (se 3 (by rfl) ⟨634055, by rfl⟩ : syracuseStep 3381629 = 1268111) (by norm_num)
theorem B2254419 : Blo 2253435 2254419 := bstep (se 1 (by rfl) ⟨1690814, by rfl⟩ : syracuseStep 2254419 = 3381629) B3381629
theorem B5072453 : Blo 2253435 5072453 := bbase (se 4 (by rfl) ⟨475542, by rfl⟩ : syracuseStep 5072453 = 951085) (by norm_num)
theorem B3381635 : Blo 2253435 3381635 := bstep (se 1 (by rfl) ⟨2536226, by rfl⟩ : syracuseStep 3381635 = 5072453) B5072453
theorem B2254423 : Blo 2253435 2254423 := bstep (se 1 (by rfl) ⟨1690817, by rfl⟩ : syracuseStep 2254423 = 3381635) B3381635
theorem B8125109 : Blo 2253435 8125109 := bbase (se 5 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 8125109 = 761729) (by norm_num)
theorem B5416739 : Blo 2253435 5416739 := bstep (se 1 (by rfl) ⟨4062554, by rfl⟩ : syracuseStep 5416739 = 8125109) B8125109
theorem B3611159 : Blo 2253435 3611159 := bstep (se 1 (by rfl) ⟨2708369, by rfl⟩ : syracuseStep 3611159 = 5416739) B5416739
theorem B2407439 : Blo 2253435 2407439 := bstep (se 1 (by rfl) ⟨1805579, by rfl⟩ : syracuseStep 2407439 = 3611159) B3611159
theorem B6419837 : Blo 2253435 6419837 := bstep (se 3 (by rfl) ⟨1203719, by rfl⟩ : syracuseStep 6419837 = 2407439) B2407439
theorem B4279891 : Blo 2253435 4279891 := bstep (se 1 (by rfl) ⟨3209918, by rfl⟩ : syracuseStep 4279891 = 6419837) B6419837
theorem B5706521 : Blo 2253435 5706521 := bstep (se 2 (by rfl) ⟨2139945, by rfl⟩ : syracuseStep 5706521 = 4279891) B4279891
theorem B3804347 : Blo 2253435 3804347 := bstep (se 1 (by rfl) ⟨2853260, by rfl⟩ : syracuseStep 3804347 = 5706521) B5706521
theorem B2536231 : Blo 2253435 2536231 := bstep (se 1 (by rfl) ⟨1902173, by rfl⟩ : syracuseStep 2536231 = 3804347) B3804347
theorem B3381641 : Blo 2253435 3381641 := bstep (se 2 (by rfl) ⟨1268115, by rfl⟩ : syracuseStep 3381641 = 2536231) B2536231
theorem B2254427 : Blo 2253435 2254427 := bstep (se 1 (by rfl) ⟨1690820, by rfl⟩ : syracuseStep 2254427 = 3381641) B3381641
theorem B11413061 : Blo 2253435 11413061 := bbase (se 4 (by rfl) ⟨1069974, by rfl⟩ : syracuseStep 11413061 = 2139949) (by norm_num)
theorem B7608707 : Blo 2253435 7608707 := bstep (se 1 (by rfl) ⟨5706530, by rfl⟩ : syracuseStep 7608707 = 11413061) B11413061
theorem B5072471 : Blo 2253435 5072471 := bstep (se 1 (by rfl) ⟨3804353, by rfl⟩ : syracuseStep 5072471 = 7608707) B7608707
theorem B3381647 : Blo 2253435 3381647 := bstep (se 1 (by rfl) ⟨2536235, by rfl⟩ : syracuseStep 3381647 = 5072471) B5072471
theorem B2254431 : Blo 2253435 2254431 := bstep (se 1 (by rfl) ⟨1690823, by rfl⟩ : syracuseStep 2254431 = 3381647) B3381647
theorem B3381653 : Blo 2253435 3381653 := bbase (se 6 (by rfl) ⟨79257, by rfl⟩ : syracuseStep 3381653 = 158515) (by norm_num)
theorem B2254435 : Blo 2253435 2254435 := bstep (se 1 (by rfl) ⟨1690826, by rfl⟩ : syracuseStep 2254435 = 3381653) B3381653
theorem B2892205 : Blo 2253435 2892205 := bbase (se 3 (by rfl) ⟨542288, by rfl⟩ : syracuseStep 2892205 = 1084577) (by norm_num)
theorem B15425093 : Blo 2253435 15425093 := bstep (se 4 (by rfl) ⟨1446102, by rfl⟩ : syracuseStep 15425093 = 2892205) B2892205
theorem B10283395 : Blo 2253435 10283395 := bstep (se 1 (by rfl) ⟨7712546, by rfl⟩ : syracuseStep 10283395 = 15425093) B15425093
theorem B13711193 : Blo 2253435 13711193 := bstep (se 2 (by rfl) ⟨5141697, by rfl⟩ : syracuseStep 13711193 = 10283395) B10283395
theorem B9140795 : Blo 2253435 9140795 := bstep (se 1 (by rfl) ⟨6855596, by rfl⟩ : syracuseStep 9140795 = 13711193) B13711193
theorem B6093863 : Blo 2253435 6093863 := bstep (se 1 (by rfl) ⟨4570397, by rfl⟩ : syracuseStep 6093863 = 9140795) B9140795
theorem B4062575 : Blo 2253435 4062575 := bstep (se 1 (by rfl) ⟨3046931, by rfl⟩ : syracuseStep 4062575 = 6093863) B6093863
theorem B10833533 : Blo 2253435 10833533 := bstep (se 3 (by rfl) ⟨2031287, by rfl⟩ : syracuseStep 10833533 = 4062575) B4062575
theorem B7222355 : Blo 2253435 7222355 := bstep (se 1 (by rfl) ⟨5416766, by rfl⟩ : syracuseStep 7222355 = 10833533) B10833533
theorem B4814903 : Blo 2253435 4814903 := bstep (se 1 (by rfl) ⟨3611177, by rfl⟩ : syracuseStep 4814903 = 7222355) B7222355
theorem B12839741 : Blo 2253435 12839741 := bstep (se 3 (by rfl) ⟨2407451, by rfl⟩ : syracuseStep 12839741 = 4814903) B4814903
theorem B8559827 : Blo 2253435 8559827 := bstep (se 1 (by rfl) ⟨6419870, by rfl⟩ : syracuseStep 8559827 = 12839741) B12839741
theorem B5706551 : Blo 2253435 5706551 := bstep (se 1 (by rfl) ⟨4279913, by rfl⟩ : syracuseStep 5706551 = 8559827) B8559827
theorem B3804367 : Blo 2253435 3804367 := bstep (se 1 (by rfl) ⟨2853275, by rfl⟩ : syracuseStep 3804367 = 5706551) B5706551
theorem B5072489 : Blo 2253435 5072489 := bstep (se 2 (by rfl) ⟨1902183, by rfl⟩ : syracuseStep 5072489 = 3804367) B3804367
theorem B3381659 : Blo 2253435 3381659 := bstep (se 1 (by rfl) ⟨2536244, by rfl⟩ : syracuseStep 3381659 = 5072489) B5072489
theorem B2254439 : Blo 2253435 2254439 := bstep (se 1 (by rfl) ⟨1690829, by rfl⟩ : syracuseStep 2254439 = 3381659) B3381659
theorem B2536249 : Blo 2253435 2536249 := bbase (se 2 (by rfl) ⟨951093, by rfl⟩ : syracuseStep 2536249 = 1902187) (by norm_num)
theorem B3381665 : Blo 2253435 3381665 := bstep (se 2 (by rfl) ⟨1268124, by rfl⟩ : syracuseStep 3381665 = 2536249) B2536249
theorem B2254443 : Blo 2253435 2254443 := bstep (se 1 (by rfl) ⟨1690832, by rfl⟩ : syracuseStep 2254443 = 3381665) B3381665
theorem B6419893 : Blo 2253435 6419893 := bbase (se 5 (by rfl) ⟨300932, by rfl⟩ : syracuseStep 6419893 = 601865) (by norm_num)
theorem B8559857 : Blo 2253435 8559857 := bstep (se 2 (by rfl) ⟨3209946, by rfl⟩ : syracuseStep 8559857 = 6419893) B6419893
theorem B5706571 : Blo 2253435 5706571 := bstep (se 1 (by rfl) ⟨4279928, by rfl⟩ : syracuseStep 5706571 = 8559857) B8559857
theorem B7608761 : Blo 2253435 7608761 := bstep (se 2 (by rfl) ⟨2853285, by rfl⟩ : syracuseStep 7608761 = 5706571) B5706571
theorem B5072507 : Blo 2253435 5072507 := bstep (se 1 (by rfl) ⟨3804380, by rfl⟩ : syracuseStep 5072507 = 7608761) B7608761
theorem B3381671 : Blo 2253435 3381671 := bstep (se 1 (by rfl) ⟨2536253, by rfl⟩ : syracuseStep 3381671 = 5072507) B5072507
theorem B2254447 : Blo 2253435 2254447 := bstep (se 1 (by rfl) ⟨1690835, by rfl⟩ : syracuseStep 2254447 = 3381671) B3381671
theorem B3381677 : Blo 2253435 3381677 := bbase (se 3 (by rfl) ⟨634064, by rfl⟩ : syracuseStep 3381677 = 1268129) (by norm_num)
theorem B2254451 : Blo 2253435 2254451 := bstep (se 1 (by rfl) ⟨1690838, by rfl⟩ : syracuseStep 2254451 = 3381677) B3381677
theorem B5072525 : Blo 2253435 5072525 := bbase (se 3 (by rfl) ⟨951098, by rfl⟩ : syracuseStep 5072525 = 1902197) (by norm_num)
theorem B3381683 : Blo 2253435 3381683 := bstep (se 1 (by rfl) ⟨2536262, by rfl⟩ : syracuseStep 3381683 = 5072525) B5072525
theorem B2254455 : Blo 2253435 2254455 := bstep (se 1 (by rfl) ⟨1690841, by rfl⟩ : syracuseStep 2254455 = 3381683) B3381683
theorem B2853301 : Blo 2253435 2853301 := bbase (se 5 (by rfl) ⟨133748, by rfl⟩ : syracuseStep 2853301 = 267497) (by norm_num)
theorem B3804401 : Blo 2253435 3804401 := bstep (se 2 (by rfl) ⟨1426650, by rfl⟩ : syracuseStep 3804401 = 2853301) B2853301
theorem B2536267 : Blo 2253435 2536267 := bstep (se 1 (by rfl) ⟨1902200, by rfl⟩ : syracuseStep 2536267 = 3804401) B3804401
theorem B3381689 : Blo 2253435 3381689 := bstep (se 2 (by rfl) ⟨1268133, by rfl⟩ : syracuseStep 3381689 = 2536267) B2536267
theorem B2254459 : Blo 2253435 2254459 := bstep (se 1 (by rfl) ⟨1690844, by rfl⟩ : syracuseStep 2254459 = 3381689) B3381689
theorem B3253765 : Blo 2253435 3253765 := bbase (se 4 (by rfl) ⟨305040, by rfl⟩ : syracuseStep 3253765 = 610081) (by norm_num)
theorem B4338353 : Blo 2253435 4338353 := bstep (se 2 (by rfl) ⟨1626882, by rfl⟩ : syracuseStep 4338353 = 3253765) B3253765
theorem B2892235 : Blo 2253435 2892235 := bstep (se 1 (by rfl) ⟨2169176, by rfl⟩ : syracuseStep 2892235 = 4338353) B4338353
theorem B3856313 : Blo 2253435 3856313 := bstep (se 2 (by rfl) ⟨1446117, by rfl⟩ : syracuseStep 3856313 = 2892235) B2892235
theorem B10283501 : Blo 2253435 10283501 := bstep (se 3 (by rfl) ⟨1928156, by rfl⟩ : syracuseStep 10283501 = 3856313) B3856313
theorem B6855667 : Blo 2253435 6855667 := bstep (se 1 (by rfl) ⟨5141750, by rfl⟩ : syracuseStep 6855667 = 10283501) B10283501
theorem B36563557 : Blo 2253435 36563557 := bstep (se 4 (by rfl) ⟨3427833, by rfl⟩ : syracuseStep 36563557 = 6855667) B6855667
theorem B48751409 : Blo 2253435 48751409 := bstep (se 2 (by rfl) ⟨18281778, by rfl⟩ : syracuseStep 48751409 = 36563557) B36563557
theorem B32500939 : Blo 2253435 32500939 := bstep (se 1 (by rfl) ⟨24375704, by rfl⟩ : syracuseStep 32500939 = 48751409) B48751409
theorem B43334585 : Blo 2253435 43334585 := bstep (se 2 (by rfl) ⟨16250469, by rfl⟩ : syracuseStep 43334585 = 32500939) B32500939
theorem B28889723 : Blo 2253435 28889723 := bstep (se 1 (by rfl) ⟨21667292, by rfl⟩ : syracuseStep 28889723 = 43334585) B43334585
theorem B19259815 : Blo 2253435 19259815 := bstep (se 1 (by rfl) ⟨14444861, by rfl⟩ : syracuseStep 19259815 = 28889723) B28889723
theorem B25679753 : Blo 2253435 25679753 := bstep (se 2 (by rfl) ⟨9629907, by rfl⟩ : syracuseStep 25679753 = 19259815) B19259815
theorem B17119835 : Blo 2253435 17119835 := bstep (se 1 (by rfl) ⟨12839876, by rfl⟩ : syracuseStep 17119835 = 25679753) B25679753
theorem B11413223 : Blo 2253435 11413223 := bstep (se 1 (by rfl) ⟨8559917, by rfl⟩ : syracuseStep 11413223 = 17119835) B17119835
theorem B7608815 : Blo 2253435 7608815 := bstep (se 1 (by rfl) ⟨5706611, by rfl⟩ : syracuseStep 7608815 = 11413223) B11413223
theorem B5072543 : Blo 2253435 5072543 := bstep (se 1 (by rfl) ⟨3804407, by rfl⟩ : syracuseStep 5072543 = 7608815) B7608815
theorem B3381695 : Blo 2253435 3381695 := bstep (se 1 (by rfl) ⟨2536271, by rfl⟩ : syracuseStep 3381695 = 5072543) B5072543
theorem B2254463 : Blo 2253435 2254463 := bstep (se 1 (by rfl) ⟨1690847, by rfl⟩ : syracuseStep 2254463 = 3381695) B3381695
theorem B3381701 : Blo 2253435 3381701 := bbase (se 4 (by rfl) ⟨317034, by rfl⟩ : syracuseStep 3381701 = 634069) (by norm_num)
theorem B2254467 : Blo 2253435 2254467 := bstep (se 1 (by rfl) ⟨1690850, by rfl⟩ : syracuseStep 2254467 = 3381701) B3381701
theorem B3804421 : Blo 2253435 3804421 := bbase (se 4 (by rfl) ⟨356664, by rfl⟩ : syracuseStep 3804421 = 713329) (by norm_num)
theorem B5072561 : Blo 2253435 5072561 := bstep (se 2 (by rfl) ⟨1902210, by rfl⟩ : syracuseStep 5072561 = 3804421) B3804421
theorem B3381707 : Blo 2253435 3381707 := bstep (se 1 (by rfl) ⟨2536280, by rfl⟩ : syracuseStep 3381707 = 5072561) B5072561
theorem B2254471 : Blo 2253435 2254471 := bstep (se 1 (by rfl) ⟨1690853, by rfl⟩ : syracuseStep 2254471 = 3381707) B3381707
theorem B2536285 : Blo 2253435 2536285 := bbase (se 3 (by rfl) ⟨475553, by rfl⟩ : syracuseStep 2536285 = 951107) (by norm_num)
theorem B3381713 : Blo 2253435 3381713 := bstep (se 2 (by rfl) ⟨1268142, by rfl⟩ : syracuseStep 3381713 = 2536285) B2536285
theorem B2254475 : Blo 2253435 2254475 := bstep (se 1 (by rfl) ⟨1690856, by rfl⟩ : syracuseStep 2254475 = 3381713) B3381713
theorem B7608869 : Blo 2253435 7608869 := bbase (se 4 (by rfl) ⟨713331, by rfl⟩ : syracuseStep 7608869 = 1426663) (by norm_num)
theorem B5072579 : Blo 2253435 5072579 := bstep (se 1 (by rfl) ⟨3804434, by rfl⟩ : syracuseStep 5072579 = 7608869) B7608869
theorem B3381719 : Blo 2253435 3381719 := bstep (se 1 (by rfl) ⟨2536289, by rfl⟩ : syracuseStep 3381719 = 5072579) B5072579
theorem B2254479 : Blo 2253435 2254479 := bstep (se 1 (by rfl) ⟨1690859, by rfl⟩ : syracuseStep 2254479 = 3381719) B3381719
theorem B3381725 : Blo 2253435 3381725 := bbase (se 3 (by rfl) ⟨634073, by rfl⟩ : syracuseStep 3381725 = 1268147) (by norm_num)
theorem B2254483 : Blo 2253435 2254483 := bstep (se 1 (by rfl) ⟨1690862, by rfl⟩ : syracuseStep 2254483 = 3381725) B3381725
theorem B5072597 : Blo 2253435 5072597 := bbase (se 7 (by rfl) ⟨59444, by rfl⟩ : syracuseStep 5072597 = 118889) (by norm_num)
theorem B3381731 : Blo 2253435 3381731 := bstep (se 1 (by rfl) ⟨2536298, by rfl⟩ : syracuseStep 3381731 = 5072597) B5072597
theorem B2254487 : Blo 2253435 2254487 := bstep (se 1 (by rfl) ⟨1690865, by rfl⟩ : syracuseStep 2254487 = 3381731) B3381731
theorem B3611261 : Blo 2253435 3611261 := bbase (se 3 (by rfl) ⟨677111, by rfl⟩ : syracuseStep 3611261 = 1354223) (by norm_num)
theorem B9630029 : Blo 2253435 9630029 := bstep (se 3 (by rfl) ⟨1805630, by rfl⟩ : syracuseStep 9630029 = 3611261) B3611261
theorem B6420019 : Blo 2253435 6420019 := bstep (se 1 (by rfl) ⟨4815014, by rfl⟩ : syracuseStep 6420019 = 9630029) B9630029
theorem B8560025 : Blo 2253435 8560025 := bstep (se 2 (by rfl) ⟨3210009, by rfl⟩ : syracuseStep 8560025 = 6420019) B6420019
theorem B5706683 : Blo 2253435 5706683 := bstep (se 1 (by rfl) ⟨4280012, by rfl⟩ : syracuseStep 5706683 = 8560025) B8560025
theorem B3804455 : Blo 2253435 3804455 := bstep (se 1 (by rfl) ⟨2853341, by rfl⟩ : syracuseStep 3804455 = 5706683) B5706683
theorem B2536303 : Blo 2253435 2536303 := bstep (se 1 (by rfl) ⟨1902227, by rfl⟩ : syracuseStep 2536303 = 3804455) B3804455
theorem B3381737 : Blo 2253435 3381737 := bstep (se 2 (by rfl) ⟨1268151, by rfl⟩ : syracuseStep 3381737 = 2536303) B2536303
theorem B2254491 : Blo 2253435 2254491 := bstep (se 1 (by rfl) ⟨1690868, by rfl⟩ : syracuseStep 2254491 = 3381737) B3381737
theorem B2892277 : Blo 2253435 2892277 := bbase (se 5 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 2892277 = 271151) (by norm_num)
theorem B3856369 : Blo 2253435 3856369 := bstep (se 2 (by rfl) ⟨1446138, by rfl⟩ : syracuseStep 3856369 = 2892277) B2892277
theorem B5141825 : Blo 2253435 5141825 := bstep (se 2 (by rfl) ⟨1928184, by rfl⟩ : syracuseStep 5141825 = 3856369) B3856369
theorem B3427883 : Blo 2253435 3427883 := bstep (se 1 (by rfl) ⟨2570912, by rfl⟩ : syracuseStep 3427883 = 5141825) B5141825
theorem B2285255 : Blo 2253435 2285255 := bstep (se 1 (by rfl) ⟨1713941, by rfl⟩ : syracuseStep 2285255 = 3427883) B3427883
theorem B6094013 : Blo 2253435 6094013 := bstep (se 3 (by rfl) ⟨1142627, by rfl⟩ : syracuseStep 6094013 = 2285255) B2285255
theorem B16250701 : Blo 2253435 16250701 := bstep (se 3 (by rfl) ⟨3047006, by rfl⟩ : syracuseStep 16250701 = 6094013) B6094013
theorem B21667601 : Blo 2253435 21667601 := bstep (se 2 (by rfl) ⟨8125350, by rfl⟩ : syracuseStep 21667601 = 16250701) B16250701
theorem B14445067 : Blo 2253435 14445067 := bstep (se 1 (by rfl) ⟨10833800, by rfl⟩ : syracuseStep 14445067 = 21667601) B21667601
theorem B19260089 : Blo 2253435 19260089 := bstep (se 2 (by rfl) ⟨7222533, by rfl⟩ : syracuseStep 19260089 = 14445067) B14445067
theorem B12840059 : Blo 2253435 12840059 := bstep (se 1 (by rfl) ⟨9630044, by rfl⟩ : syracuseStep 12840059 = 19260089) B19260089
theorem B8560039 : Blo 2253435 8560039 := bstep (se 1 (by rfl) ⟨6420029, by rfl⟩ : syracuseStep 8560039 = 12840059) B12840059
theorem B11413385 : Blo 2253435 11413385 := bstep (se 2 (by rfl) ⟨4280019, by rfl⟩ : syracuseStep 11413385 = 8560039) B8560039
theorem B7608923 : Blo 2253435 7608923 := bstep (se 1 (by rfl) ⟨5706692, by rfl⟩ : syracuseStep 7608923 = 11413385) B11413385
theorem B5072615 : Blo 2253435 5072615 := bstep (se 1 (by rfl) ⟨3804461, by rfl⟩ : syracuseStep 5072615 = 7608923) B7608923
theorem B3381743 : Blo 2253435 3381743 := bstep (se 1 (by rfl) ⟨2536307, by rfl⟩ : syracuseStep 3381743 = 5072615) B5072615
theorem B2254495 : Blo 2253435 2254495 := bstep (se 1 (by rfl) ⟨1690871, by rfl⟩ : syracuseStep 2254495 = 3381743) B3381743
theorem B3381749 : Blo 2253435 3381749 := bbase (se 5 (by rfl) ⟨158519, by rfl⟩ : syracuseStep 3381749 = 317039) (by norm_num)
theorem B2254499 : Blo 2253435 2254499 := bstep (se 1 (by rfl) ⟨1690874, by rfl⟩ : syracuseStep 2254499 = 3381749) B3381749
theorem B6420053 : Blo 2253435 6420053 := bbase (se 8 (by rfl) ⟨37617, by rfl⟩ : syracuseStep 6420053 = 75235) (by norm_num)
theorem B4280035 : Blo 2253435 4280035 := bstep (se 1 (by rfl) ⟨3210026, by rfl⟩ : syracuseStep 4280035 = 6420053) B6420053
theorem B5706713 : Blo 2253435 5706713 := bstep (se 2 (by rfl) ⟨2140017, by rfl⟩ : syracuseStep 5706713 = 4280035) B4280035
theorem B3804475 : Blo 2253435 3804475 := bstep (se 1 (by rfl) ⟨2853356, by rfl⟩ : syracuseStep 3804475 = 5706713) B5706713
theorem B5072633 : Blo 2253435 5072633 := bstep (se 2 (by rfl) ⟨1902237, by rfl⟩ : syracuseStep 5072633 = 3804475) B3804475
theorem B3381755 : Blo 2253435 3381755 := bstep (se 1 (by rfl) ⟨2536316, by rfl⟩ : syracuseStep 3381755 = 5072633) B5072633
theorem B2254503 : Blo 2253435 2254503 := bstep (se 1 (by rfl) ⟨1690877, by rfl⟩ : syracuseStep 2254503 = 3381755) B3381755
theorem B2536321 : Blo 2253435 2536321 := bbase (se 2 (by rfl) ⟨951120, by rfl⟩ : syracuseStep 2536321 = 1902241) (by norm_num)
theorem B3381761 : Blo 2253435 3381761 := bstep (se 2 (by rfl) ⟨1268160, by rfl⟩ : syracuseStep 3381761 = 2536321) B2536321
theorem B2254507 : Blo 2253435 2254507 := bstep (se 1 (by rfl) ⟨1690880, by rfl⟩ : syracuseStep 2254507 = 3381761) B3381761
theorem B5706733 : Blo 2253435 5706733 := bbase (se 3 (by rfl) ⟨1070012, by rfl⟩ : syracuseStep 5706733 = 2140025) (by norm_num)
theorem B7608977 : Blo 2253435 7608977 := bstep (se 2 (by rfl) ⟨2853366, by rfl⟩ : syracuseStep 7608977 = 5706733) B5706733
theorem B5072651 : Blo 2253435 5072651 := bstep (se 1 (by rfl) ⟨3804488, by rfl⟩ : syracuseStep 5072651 = 7608977) B7608977
theorem B3381767 : Blo 2253435 3381767 := bstep (se 1 (by rfl) ⟨2536325, by rfl⟩ : syracuseStep 3381767 = 5072651) B5072651
theorem B2254511 : Blo 2253435 2254511 := bstep (se 1 (by rfl) ⟨1690883, by rfl⟩ : syracuseStep 2254511 = 3381767) B3381767
theorem B3381773 : Blo 2253435 3381773 := bbase (se 3 (by rfl) ⟨634082, by rfl⟩ : syracuseStep 3381773 = 1268165) (by norm_num)
theorem B2254515 : Blo 2253435 2254515 := bstep (se 1 (by rfl) ⟨1690886, by rfl⟩ : syracuseStep 2254515 = 3381773) B3381773
theorem B5072669 : Blo 2253435 5072669 := bbase (se 3 (by rfl) ⟨951125, by rfl⟩ : syracuseStep 5072669 = 1902251) (by norm_num)
theorem B3381779 : Blo 2253435 3381779 := bstep (se 1 (by rfl) ⟨2536334, by rfl⟩ : syracuseStep 3381779 = 5072669) B5072669
theorem B2254519 : Blo 2253435 2254519 := bstep (se 1 (by rfl) ⟨1690889, by rfl⟩ : syracuseStep 2254519 = 3381779) B3381779
theorem B3804509 : Blo 2253435 3804509 := bbase (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) (by norm_num)
theorem B2536339 : Blo 2253435 2536339 := bstep (se 1 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 2536339 = 3804509) B3804509
theorem B3381785 : Blo 2253435 3381785 := bstep (se 2 (by rfl) ⟨1268169, by rfl⟩ : syracuseStep 3381785 = 2536339) B2536339
theorem B2254523 : Blo 2253435 2254523 := bstep (se 1 (by rfl) ⟨1690892, by rfl⟩ : syracuseStep 2254523 = 3381785) B3381785
theorem B9630181 : Blo 2253435 9630181 := bbase (se 4 (by rfl) ⟨902829, by rfl⟩ : syracuseStep 9630181 = 1805659) (by norm_num)
theorem B12840241 : Blo 2253435 12840241 := bstep (se 2 (by rfl) ⟨4815090, by rfl⟩ : syracuseStep 12840241 = 9630181) B9630181
theorem B17120321 : Blo 2253435 17120321 := bstep (se 2 (by rfl) ⟨6420120, by rfl⟩ : syracuseStep 17120321 = 12840241) B12840241
theorem B11413547 : Blo 2253435 11413547 := bstep (se 1 (by rfl) ⟨8560160, by rfl⟩ : syracuseStep 11413547 = 17120321) B17120321
theorem B7609031 : Blo 2253435 7609031 := bstep (se 1 (by rfl) ⟨5706773, by rfl⟩ : syracuseStep 7609031 = 11413547) B11413547
theorem B5072687 : Blo 2253435 5072687 := bstep (se 1 (by rfl) ⟨3804515, by rfl⟩ : syracuseStep 5072687 = 7609031) B7609031
theorem B3381791 : Blo 2253435 3381791 := bstep (se 1 (by rfl) ⟨2536343, by rfl⟩ : syracuseStep 3381791 = 5072687) B5072687
theorem B2254527 : Blo 2253435 2254527 := bstep (se 1 (by rfl) ⟨1690895, by rfl⟩ : syracuseStep 2254527 = 3381791) B3381791
theorem B3381797 : Blo 2253435 3381797 := bbase (se 4 (by rfl) ⟨317043, by rfl⟩ : syracuseStep 3381797 = 634087) (by norm_num)
theorem B2254531 : Blo 2253435 2254531 := bstep (se 1 (by rfl) ⟨1690898, by rfl⟩ : syracuseStep 2254531 = 3381797) B3381797
theorem B2853397 : Blo 2253435 2853397 := bbase (se 6 (by rfl) ⟨66876, by rfl⟩ : syracuseStep 2853397 = 133753) (by norm_num)
theorem B3804529 : Blo 2253435 3804529 := bstep (se 2 (by rfl) ⟨1426698, by rfl⟩ : syracuseStep 3804529 = 2853397) B2853397
theorem B5072705 : Blo 2253435 5072705 := bstep (se 2 (by rfl) ⟨1902264, by rfl⟩ : syracuseStep 5072705 = 3804529) B3804529
theorem B3381803 : Blo 2253435 3381803 := bstep (se 1 (by rfl) ⟨2536352, by rfl⟩ : syracuseStep 3381803 = 5072705) B5072705
theorem B2254535 : Blo 2253435 2254535 := bstep (se 1 (by rfl) ⟨1690901, by rfl⟩ : syracuseStep 2254535 = 3381803) B3381803
theorem B2536357 : Blo 2253435 2536357 := bbase (se 4 (by rfl) ⟨237783, by rfl⟩ : syracuseStep 2536357 = 475567) (by norm_num)
theorem B3381809 : Blo 2253435 3381809 := bstep (se 2 (by rfl) ⟨1268178, by rfl⟩ : syracuseStep 3381809 = 2536357) B2536357
theorem B2254539 : Blo 2253435 2254539 := bstep (se 1 (by rfl) ⟨1690904, by rfl⟩ : syracuseStep 2254539 = 3381809) B3381809
theorem B8125525 : Blo 2253435 8125525 := bbase (se 8 (by rfl) ⟨47610, by rfl⟩ : syracuseStep 8125525 = 95221) (by norm_num)
theorem B10834033 : Blo 2253435 10834033 := bstep (se 2 (by rfl) ⟨4062762, by rfl⟩ : syracuseStep 10834033 = 8125525) B8125525
theorem B14445377 : Blo 2253435 14445377 := bstep (se 2 (by rfl) ⟨5417016, by rfl⟩ : syracuseStep 14445377 = 10834033) B10834033
theorem B9630251 : Blo 2253435 9630251 := bstep (se 1 (by rfl) ⟨7222688, by rfl⟩ : syracuseStep 9630251 = 14445377) B14445377
theorem B6420167 : Blo 2253435 6420167 := bstep (se 1 (by rfl) ⟨4815125, by rfl⟩ : syracuseStep 6420167 = 9630251) B9630251
theorem B4280111 : Blo 2253435 4280111 := bstep (se 1 (by rfl) ⟨3210083, by rfl⟩ : syracuseStep 4280111 = 6420167) B6420167
theorem B2853407 : Blo 2253435 2853407 := bstep (se 1 (by rfl) ⟨2140055, by rfl⟩ : syracuseStep 2853407 = 4280111) B4280111
theorem B7609085 : Blo 2253435 7609085 := bstep (se 3 (by rfl) ⟨1426703, by rfl⟩ : syracuseStep 7609085 = 2853407) B2853407
theorem B5072723 : Blo 2253435 5072723 := bstep (se 1 (by rfl) ⟨3804542, by rfl⟩ : syracuseStep 5072723 = 7609085) B7609085
theorem B3381815 : Blo 2253435 3381815 := bstep (se 1 (by rfl) ⟨2536361, by rfl⟩ : syracuseStep 3381815 = 5072723) B5072723
theorem B2254543 : Blo 2253435 2254543 := bstep (se 1 (by rfl) ⟨1690907, by rfl⟩ : syracuseStep 2254543 = 3381815) B3381815
theorem B3381821 : Blo 2253435 3381821 := bbase (se 3 (by rfl) ⟨634091, by rfl⟩ : syracuseStep 3381821 = 1268183) (by norm_num)
theorem B2254547 : Blo 2253435 2254547 := bstep (se 1 (by rfl) ⟨1690910, by rfl⟩ : syracuseStep 2254547 = 3381821) B3381821
theorem B5072741 : Blo 2253435 5072741 := bbase (se 4 (by rfl) ⟨475569, by rfl⟩ : syracuseStep 5072741 = 951139) (by norm_num)
theorem B3381827 : Blo 2253435 3381827 := bstep (se 1 (by rfl) ⟨2536370, by rfl⟩ : syracuseStep 3381827 = 5072741) B5072741
theorem B2254551 : Blo 2253435 2254551 := bstep (se 1 (by rfl) ⟨1690913, by rfl⟩ : syracuseStep 2254551 = 3381827) B3381827
theorem B5706845 : Blo 2253435 5706845 := bbase (se 3 (by rfl) ⟨1070033, by rfl⟩ : syracuseStep 5706845 = 2140067) (by norm_num)
theorem B3804563 : Blo 2253435 3804563 := bstep (se 1 (by rfl) ⟨2853422, by rfl⟩ : syracuseStep 3804563 = 5706845) B5706845
theorem B2536375 : Blo 2253435 2536375 := bstep (se 1 (by rfl) ⟨1902281, by rfl⟩ : syracuseStep 2536375 = 3804563) B3804563
theorem B3381833 : Blo 2253435 3381833 := bstep (se 2 (by rfl) ⟨1268187, by rfl⟩ : syracuseStep 3381833 = 2536375) B2536375
theorem B2254555 : Blo 2253435 2254555 := bstep (se 1 (by rfl) ⟨1690916, by rfl⟩ : syracuseStep 2254555 = 3381833) B3381833
theorem B4280141 : Blo 2253435 4280141 := bbase (se 3 (by rfl) ⟨802526, by rfl⟩ : syracuseStep 4280141 = 1605053) (by norm_num)
theorem B11413709 : Blo 2253435 11413709 := bstep (se 3 (by rfl) ⟨2140070, by rfl⟩ : syracuseStep 11413709 = 4280141) B4280141
theorem B7609139 : Blo 2253435 7609139 := bstep (se 1 (by rfl) ⟨5706854, by rfl⟩ : syracuseStep 7609139 = 11413709) B11413709
theorem B5072759 : Blo 2253435 5072759 := bstep (se 1 (by rfl) ⟨3804569, by rfl⟩ : syracuseStep 5072759 = 7609139) B7609139
theorem B3381839 : Blo 2253435 3381839 := bstep (se 1 (by rfl) ⟨2536379, by rfl⟩ : syracuseStep 3381839 = 5072759) B5072759
theorem B2254559 : Blo 2253435 2254559 := bstep (se 1 (by rfl) ⟨1690919, by rfl⟩ : syracuseStep 2254559 = 3381839) B3381839
theorem B3381845 : Blo 2253435 3381845 := bbase (se 8 (by rfl) ⟨19815, by rfl⟩ : syracuseStep 3381845 = 39631) (by norm_num)
theorem B2254563 : Blo 2253435 2254563 := bstep (se 1 (by rfl) ⟨1690922, by rfl⟩ : syracuseStep 2254563 = 3381845) B3381845
theorem B2708537 : Blo 2253435 2708537 := bbase (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) (by norm_num)
theorem B7222765 : Blo 2253435 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B9630353 : Blo 2253435 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B6420235 : Blo 2253435 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B8560313 : Blo 2253435 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B5706875 : Blo 2253435 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B3804583 : Blo 2253435 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B5072777 : Blo 2253435 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B3381851 : Blo 2253435 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B2254567 : Blo 2253435 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B2536393 : Blo 2253435 2536393 := bbase (se 2 (by rfl) ⟨951147, by rfl⟩ : syracuseStep 2536393 = 1902295) (by norm_num)
theorem B3381857 : Blo 2253435 3381857 := bstep (se 2 (by rfl) ⟨1268196, by rfl⟩ : syracuseStep 3381857 = 2536393) B2536393
theorem B2254571 : Blo 2253435 2254571 := bstep (se 1 (by rfl) ⟨1690928, by rfl⟩ : syracuseStep 2254571 = 3381857) B3381857
theorem B5417093 : Blo 2253435 5417093 := bbase (se 4 (by rfl) ⟨507852, by rfl⟩ : syracuseStep 5417093 = 1015705) (by norm_num)
theorem B3611395 : Blo 2253435 3611395 := bstep (se 1 (by rfl) ⟨2708546, by rfl⟩ : syracuseStep 3611395 = 5417093) B5417093
theorem B19260773 : Blo 2253435 19260773 := bstep (se 4 (by rfl) ⟨1805697, by rfl⟩ : syracuseStep 19260773 = 3611395) B3611395
theorem B12840515 : Blo 2253435 12840515 := bstep (se 1 (by rfl) ⟨9630386, by rfl⟩ : syracuseStep 12840515 = 19260773) B19260773
theorem B8560343 : Blo 2253435 8560343 := bstep (se 1 (by rfl) ⟨6420257, by rfl⟩ : syracuseStep 8560343 = 12840515) B12840515
theorem B5706895 : Blo 2253435 5706895 := bstep (se 1 (by rfl) ⟨4280171, by rfl⟩ : syracuseStep 5706895 = 8560343) B8560343
theorem B7609193 : Blo 2253435 7609193 := bstep (se 2 (by rfl) ⟨2853447, by rfl⟩ : syracuseStep 7609193 = 5706895) B5706895
theorem B5072795 : Blo 2253435 5072795 := bstep (se 1 (by rfl) ⟨3804596, by rfl⟩ : syracuseStep 5072795 = 7609193) B7609193
theorem B3381863 : Blo 2253435 3381863 := bstep (se 1 (by rfl) ⟨2536397, by rfl⟩ : syracuseStep 3381863 = 5072795) B5072795
theorem B2254575 : Blo 2253435 2254575 := bstep (se 1 (by rfl) ⟨1690931, by rfl⟩ : syracuseStep 2254575 = 3381863) B3381863
theorem B3381869 : Blo 2253435 3381869 := bbase (se 3 (by rfl) ⟨634100, by rfl⟩ : syracuseStep 3381869 = 1268201) (by norm_num)
theorem B2254579 : Blo 2253435 2254579 := bstep (se 1 (by rfl) ⟨1690934, by rfl⟩ : syracuseStep 2254579 = 3381869) B3381869
theorem B5072813 : Blo 2253435 5072813 := bbase (se 3 (by rfl) ⟨951152, by rfl⟩ : syracuseStep 5072813 = 1902305) (by norm_num)
theorem B3381875 : Blo 2253435 3381875 := bstep (se 1 (by rfl) ⟨2536406, by rfl⟩ : syracuseStep 3381875 = 5072813) B5072813
theorem B2254583 : Blo 2253435 2254583 := bstep (se 1 (by rfl) ⟨1690937, by rfl⟩ : syracuseStep 2254583 = 3381875) B3381875
theorem B6420293 : Blo 2253435 6420293 := bbase (se 4 (by rfl) ⟨601902, by rfl⟩ : syracuseStep 6420293 = 1203805) (by norm_num)
theorem B4280195 : Blo 2253435 4280195 := bstep (se 1 (by rfl) ⟨3210146, by rfl⟩ : syracuseStep 4280195 = 6420293) B6420293
theorem B2853463 : Blo 2253435 2853463 := bstep (se 1 (by rfl) ⟨2140097, by rfl⟩ : syracuseStep 2853463 = 4280195) B4280195
theorem B3804617 : Blo 2253435 3804617 := bstep (se 2 (by rfl) ⟨1426731, by rfl⟩ : syracuseStep 3804617 = 2853463) B2853463
theorem B2536411 : Blo 2253435 2536411 := bstep (se 1 (by rfl) ⟨1902308, by rfl⟩ : syracuseStep 2536411 = 3804617) B3804617
theorem B3381881 : Blo 2253435 3381881 := bstep (se 2 (by rfl) ⟨1268205, by rfl⟩ : syracuseStep 3381881 = 2536411) B2536411
theorem B2254587 : Blo 2253435 2254587 := bstep (se 1 (by rfl) ⟨1690940, by rfl⟩ : syracuseStep 2254587 = 3381881) B3381881
theorem B43337045 : Blo 2253435 43337045 := bbase (se 12 (by rfl) ⟨15870, by rfl⟩ : syracuseStep 43337045 = 31741) (by norm_num)
theorem B28891363 : Blo 2253435 28891363 := bstep (se 1 (by rfl) ⟨21668522, by rfl⟩ : syracuseStep 28891363 = 43337045) B43337045
theorem B38521817 : Blo 2253435 38521817 := bstep (se 2 (by rfl) ⟨14445681, by rfl⟩ : syracuseStep 38521817 = 28891363) B28891363
theorem B25681211 : Blo 2253435 25681211 := bstep (se 1 (by rfl) ⟨19260908, by rfl⟩ : syracuseStep 25681211 = 38521817) B38521817
theorem B17120807 : Blo 2253435 17120807 := bstep (se 1 (by rfl) ⟨12840605, by rfl⟩ : syracuseStep 17120807 = 25681211) B25681211
theorem B11413871 : Blo 2253435 11413871 := bstep (se 1 (by rfl) ⟨8560403, by rfl⟩ : syracuseStep 11413871 = 17120807) B17120807
theorem B7609247 : Blo 2253435 7609247 := bstep (se 1 (by rfl) ⟨5706935, by rfl⟩ : syracuseStep 7609247 = 11413871) B11413871
theorem B5072831 : Blo 2253435 5072831 := bstep (se 1 (by rfl) ⟨3804623, by rfl⟩ : syracuseStep 5072831 = 7609247) B7609247
theorem B3381887 : Blo 2253435 3381887 := bstep (se 1 (by rfl) ⟨2536415, by rfl⟩ : syracuseStep 3381887 = 5072831) B5072831
theorem B2254591 : Blo 2253435 2254591 := bstep (se 1 (by rfl) ⟨1690943, by rfl⟩ : syracuseStep 2254591 = 3381887) B3381887
theorem B3381893 : Blo 2253435 3381893 := bbase (se 4 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 3381893 = 634105) (by norm_num)
theorem B2254595 : Blo 2253435 2254595 := bstep (se 1 (by rfl) ⟨1690946, by rfl⟩ : syracuseStep 2254595 = 3381893) B3381893
theorem B3804637 : Blo 2253435 3804637 := bbase (se 3 (by rfl) ⟨713369, by rfl⟩ : syracuseStep 3804637 = 1426739) (by norm_num)
theorem B5072849 : Blo 2253435 5072849 := bstep (se 2 (by rfl) ⟨1902318, by rfl⟩ : syracuseStep 5072849 = 3804637) B3804637
theorem B3381899 : Blo 2253435 3381899 := bstep (se 1 (by rfl) ⟨2536424, by rfl⟩ : syracuseStep 3381899 = 5072849) B5072849
theorem B2254599 : Blo 2253435 2254599 := bstep (se 1 (by rfl) ⟨1690949, by rfl⟩ : syracuseStep 2254599 = 3381899) B3381899
theorem B2536429 : Blo 2253435 2536429 := bbase (se 3 (by rfl) ⟨475580, by rfl⟩ : syracuseStep 2536429 = 951161) (by norm_num)
theorem B3381905 : Blo 2253435 3381905 := bstep (se 2 (by rfl) ⟨1268214, by rfl⟩ : syracuseStep 3381905 = 2536429) B2536429
theorem B2254603 : Blo 2253435 2254603 := bstep (se 1 (by rfl) ⟨1690952, by rfl⟩ : syracuseStep 2254603 = 3381905) B3381905
theorem B7609301 : Blo 2253435 7609301 := bbase (se 7 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 7609301 = 178343) (by norm_num)
theorem B5072867 : Blo 2253435 5072867 := bstep (se 1 (by rfl) ⟨3804650, by rfl⟩ : syracuseStep 5072867 = 7609301) B7609301
theorem B3381911 : Blo 2253435 3381911 := bstep (se 1 (by rfl) ⟨2536433, by rfl⟩ : syracuseStep 3381911 = 5072867) B5072867
theorem B2254607 : Blo 2253435 2254607 := bstep (se 1 (by rfl) ⟨1690955, by rfl⟩ : syracuseStep 2254607 = 3381911) B3381911
theorem B3381917 : Blo 2253435 3381917 := bbase (se 3 (by rfl) ⟨634109, by rfl⟩ : syracuseStep 3381917 = 1268219) (by norm_num)
theorem B2254611 : Blo 2253435 2254611 := bstep (se 1 (by rfl) ⟨1690958, by rfl⟩ : syracuseStep 2254611 = 3381917) B3381917
theorem B5072885 : Blo 2253435 5072885 := bbase (se 5 (by rfl) ⟨237791, by rfl⟩ : syracuseStep 5072885 = 475583) (by norm_num)
theorem B3381923 : Blo 2253435 3381923 := bstep (se 1 (by rfl) ⟨2536442, by rfl⟩ : syracuseStep 3381923 = 5072885) B5072885
theorem B2254615 : Blo 2253435 2254615 := bstep (se 1 (by rfl) ⟨1690961, by rfl⟩ : syracuseStep 2254615 = 3381923) B3381923
theorem B5491109 : Blo 2253435 5491109 := bbase (se 4 (by rfl) ⟨514791, by rfl⟩ : syracuseStep 5491109 = 1029583) (by norm_num)
theorem B14642957 : Blo 2253435 14642957 := bstep (se 3 (by rfl) ⟨2745554, by rfl⟩ : syracuseStep 14642957 = 5491109) B5491109
theorem B9761971 : Blo 2253435 9761971 := bstep (se 1 (by rfl) ⟨7321478, by rfl⟩ : syracuseStep 9761971 = 14642957) B14642957
theorem B13015961 : Blo 2253435 13015961 := bstep (se 2 (by rfl) ⟨4880985, by rfl⟩ : syracuseStep 13015961 = 9761971) B9761971
theorem B8677307 : Blo 2253435 8677307 := bstep (se 1 (by rfl) ⟨6507980, by rfl⟩ : syracuseStep 8677307 = 13015961) B13015961
theorem B5784871 : Blo 2253435 5784871 := bstep (se 1 (by rfl) ⟨4338653, by rfl⟩ : syracuseStep 5784871 = 8677307) B8677307
theorem B7713161 : Blo 2253435 7713161 := bstep (se 2 (by rfl) ⟨2892435, by rfl⟩ : syracuseStep 7713161 = 5784871) B5784871
theorem B5142107 : Blo 2253435 5142107 := bstep (se 1 (by rfl) ⟨3856580, by rfl⟩ : syracuseStep 5142107 = 7713161) B7713161
theorem B13712285 : Blo 2253435 13712285 := bstep (se 3 (by rfl) ⟨2571053, by rfl⟩ : syracuseStep 13712285 = 5142107) B5142107
theorem B36566093 : Blo 2253435 36566093 := bstep (se 3 (by rfl) ⟨6856142, by rfl⟩ : syracuseStep 36566093 = 13712285) B13712285
theorem B97509581 : Blo 2253435 97509581 := bstep (se 3 (by rfl) ⟨18283046, by rfl⟩ : syracuseStep 97509581 = 36566093) B36566093
theorem B65006387 : Blo 2253435 65006387 := bstep (se 1 (by rfl) ⟨48754790, by rfl⟩ : syracuseStep 65006387 = 97509581) B97509581
theorem B43337591 : Blo 2253435 43337591 := bstep (se 1 (by rfl) ⟨32503193, by rfl⟩ : syracuseStep 43337591 = 65006387) B65006387
theorem B28891727 : Blo 2253435 28891727 := bstep (se 1 (by rfl) ⟨21668795, by rfl⟩ : syracuseStep 28891727 = 43337591) B43337591
theorem B19261151 : Blo 2253435 19261151 := bstep (se 1 (by rfl) ⟨14445863, by rfl⟩ : syracuseStep 19261151 = 28891727) B28891727
theorem B12840767 : Blo 2253435 12840767 := bstep (se 1 (by rfl) ⟨9630575, by rfl⟩ : syracuseStep 12840767 = 19261151) B19261151
theorem B8560511 : Blo 2253435 8560511 := bstep (se 1 (by rfl) ⟨6420383, by rfl⟩ : syracuseStep 8560511 = 12840767) B12840767
theorem B5707007 : Blo 2253435 5707007 := bstep (se 1 (by rfl) ⟨4280255, by rfl⟩ : syracuseStep 5707007 = 8560511) B8560511
theorem B3804671 : Blo 2253435 3804671 := bstep (se 1 (by rfl) ⟨2853503, by rfl⟩ : syracuseStep 3804671 = 5707007) B5707007
theorem B2536447 : Blo 2253435 2536447 := bstep (se 1 (by rfl) ⟨1902335, by rfl⟩ : syracuseStep 2536447 = 3804671) B3804671
theorem B3381929 : Blo 2253435 3381929 := bstep (se 2 (by rfl) ⟨1268223, by rfl⟩ : syracuseStep 3381929 = 2536447) B2536447
theorem B2254619 : Blo 2253435 2254619 := bstep (se 1 (by rfl) ⟨1690964, by rfl⟩ : syracuseStep 2254619 = 3381929) B3381929
theorem B3210197 : Blo 2253435 3210197 := bbase (se 7 (by rfl) ⟨37619, by rfl⟩ : syracuseStep 3210197 = 75239) (by norm_num)
theorem B8560525 : Blo 2253435 8560525 := bstep (se 3 (by rfl) ⟨1605098, by rfl⟩ : syracuseStep 8560525 = 3210197) B3210197
theorem B11414033 : Blo 2253435 11414033 := bstep (se 2 (by rfl) ⟨4280262, by rfl⟩ : syracuseStep 11414033 = 8560525) B8560525
theorem B7609355 : Blo 2253435 7609355 := bstep (se 1 (by rfl) ⟨5707016, by rfl⟩ : syracuseStep 7609355 = 11414033) B11414033
theorem B5072903 : Blo 2253435 5072903 := bstep (se 1 (by rfl) ⟨3804677, by rfl⟩ : syracuseStep 5072903 = 7609355) B7609355
theorem B3381935 : Blo 2253435 3381935 := bstep (se 1 (by rfl) ⟨2536451, by rfl⟩ : syracuseStep 3381935 = 5072903) B5072903
theorem B2254623 : Blo 2253435 2254623 := bstep (se 1 (by rfl) ⟨1690967, by rfl⟩ : syracuseStep 2254623 = 3381935) B3381935
theorem B3381941 : Blo 2253435 3381941 := bbase (se 5 (by rfl) ⟨158528, by rfl⟩ : syracuseStep 3381941 = 317057) (by norm_num)
theorem B2254627 : Blo 2253435 2254627 := bstep (se 1 (by rfl) ⟨1690970, by rfl⟩ : syracuseStep 2254627 = 3381941) B3381941
theorem B5707037 : Blo 2253435 5707037 := bbase (se 3 (by rfl) ⟨1070069, by rfl⟩ : syracuseStep 5707037 = 2140139) (by norm_num)
theorem B3804691 : Blo 2253435 3804691 := bstep (se 1 (by rfl) ⟨2853518, by rfl⟩ : syracuseStep 3804691 = 5707037) B5707037
theorem B5072921 : Blo 2253435 5072921 := bstep (se 2 (by rfl) ⟨1902345, by rfl⟩ : syracuseStep 5072921 = 3804691) B3804691
theorem B3381947 : Blo 2253435 3381947 := bstep (se 1 (by rfl) ⟨2536460, by rfl⟩ : syracuseStep 3381947 = 5072921) B5072921
theorem B2254631 : Blo 2253435 2254631 := bstep (se 1 (by rfl) ⟨1690973, by rfl⟩ : syracuseStep 2254631 = 3381947) B3381947
theorem B2536465 : Blo 2253435 2536465 := bbase (se 2 (by rfl) ⟨951174, by rfl⟩ : syracuseStep 2536465 = 1902349) (by norm_num)
theorem B3381953 : Blo 2253435 3381953 := bstep (se 2 (by rfl) ⟨1268232, by rfl⟩ : syracuseStep 3381953 = 2536465) B2536465
theorem B2254635 : Blo 2253435 2254635 := bstep (se 1 (by rfl) ⟨1690976, by rfl⟩ : syracuseStep 2254635 = 3381953) B3381953
theorem B4280293 : Blo 2253435 4280293 := bbase (se 4 (by rfl) ⟨401277, by rfl⟩ : syracuseStep 4280293 = 802555) (by norm_num)
theorem B5707057 : Blo 2253435 5707057 := bstep (se 2 (by rfl) ⟨2140146, by rfl⟩ : syracuseStep 5707057 = 4280293) B4280293
theorem B7609409 : Blo 2253435 7609409 := bstep (se 2 (by rfl) ⟨2853528, by rfl⟩ : syracuseStep 7609409 = 5707057) B5707057
theorem B5072939 : Blo 2253435 5072939 := bstep (se 1 (by rfl) ⟨3804704, by rfl⟩ : syracuseStep 5072939 = 7609409) B7609409
theorem B3381959 : Blo 2253435 3381959 := bstep (se 1 (by rfl) ⟨2536469, by rfl⟩ : syracuseStep 3381959 = 5072939) B5072939
theorem B2254639 : Blo 2253435 2254639 := bstep (se 1 (by rfl) ⟨1690979, by rfl⟩ : syracuseStep 2254639 = 3381959) B3381959
theorem B3381965 : Blo 2253435 3381965 := bbase (se 3 (by rfl) ⟨634118, by rfl⟩ : syracuseStep 3381965 = 1268237) (by norm_num)
theorem B2254643 : Blo 2253435 2254643 := bstep (se 1 (by rfl) ⟨1690982, by rfl⟩ : syracuseStep 2254643 = 3381965) B3381965
theorem B5072957 : Blo 2253435 5072957 := bbase (se 3 (by rfl) ⟨951179, by rfl⟩ : syracuseStep 5072957 = 1902359) (by norm_num)
theorem B3381971 : Blo 2253435 3381971 := bstep (se 1 (by rfl) ⟨2536478, by rfl⟩ : syracuseStep 3381971 = 5072957) B5072957
theorem B2254647 : Blo 2253435 2254647 := bstep (se 1 (by rfl) ⟨1690985, by rfl⟩ : syracuseStep 2254647 = 3381971) B3381971
theorem B3804725 : Blo 2253435 3804725 := bbase (se 5 (by rfl) ⟨178346, by rfl⟩ : syracuseStep 3804725 = 356693) (by norm_num)
theorem B2536483 : Blo 2253435 2536483 := bstep (se 1 (by rfl) ⟨1902362, by rfl⟩ : syracuseStep 2536483 = 3804725) B3804725
theorem B3381977 : Blo 2253435 3381977 := bstep (se 2 (by rfl) ⟨1268241, by rfl⟩ : syracuseStep 3381977 = 2536483) B2536483
theorem B2254651 : Blo 2253435 2254651 := bstep (se 1 (by rfl) ⟨1690988, by rfl⟩ : syracuseStep 2254651 = 3381977) B3381977
theorem B6420485 : Blo 2253435 6420485 := bbase (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) (by norm_num)
theorem B17121293 : Blo 2253435 17121293 := bstep (se 3 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 17121293 = 6420485) B6420485
theorem B11414195 : Blo 2253435 11414195 := bstep (se 1 (by rfl) ⟨8560646, by rfl⟩ : syracuseStep 11414195 = 17121293) B17121293
theorem B7609463 : Blo 2253435 7609463 := bstep (se 1 (by rfl) ⟨5707097, by rfl⟩ : syracuseStep 7609463 = 11414195) B11414195
theorem B5072975 : Blo 2253435 5072975 := bstep (se 1 (by rfl) ⟨3804731, by rfl⟩ : syracuseStep 5072975 = 7609463) B7609463
theorem B3381983 : Blo 2253435 3381983 := bstep (se 1 (by rfl) ⟨2536487, by rfl⟩ : syracuseStep 3381983 = 5072975) B5072975
theorem B2254655 : Blo 2253435 2254655 := bstep (se 1 (by rfl) ⟨1690991, by rfl⟩ : syracuseStep 2254655 = 3381983) B3381983
theorem B3381989 : Blo 2253435 3381989 := bbase (se 4 (by rfl) ⟨317061, by rfl⟩ : syracuseStep 3381989 = 634123) (by norm_num)
theorem B2254659 : Blo 2253435 2254659 := bstep (se 1 (by rfl) ⟨1690994, by rfl⟩ : syracuseStep 2254659 = 3381989) B3381989
theorem B2708653 : Blo 2253435 2708653 := bbase (se 3 (by rfl) ⟨507872, by rfl⟩ : syracuseStep 2708653 = 1015745) (by norm_num)
theorem B3611537 : Blo 2253435 3611537 := bstep (se 2 (by rfl) ⟨1354326, by rfl⟩ : syracuseStep 3611537 = 2708653) B2708653
theorem B2407691 : Blo 2253435 2407691 := bstep (se 1 (by rfl) ⟨1805768, by rfl⟩ : syracuseStep 2407691 = 3611537) B3611537
theorem B6420509 : Blo 2253435 6420509 := bstep (se 3 (by rfl) ⟨1203845, by rfl⟩ : syracuseStep 6420509 = 2407691) B2407691
theorem B4280339 : Blo 2253435 4280339 := bstep (se 1 (by rfl) ⟨3210254, by rfl⟩ : syracuseStep 4280339 = 6420509) B6420509
theorem B2853559 : Blo 2253435 2853559 := bstep (se 1 (by rfl) ⟨2140169, by rfl⟩ : syracuseStep 2853559 = 4280339) B4280339
theorem B3804745 : Blo 2253435 3804745 := bstep (se 2 (by rfl) ⟨1426779, by rfl⟩ : syracuseStep 3804745 = 2853559) B2853559
theorem B5072993 : Blo 2253435 5072993 := bstep (se 2 (by rfl) ⟨1902372, by rfl⟩ : syracuseStep 5072993 = 3804745) B3804745
theorem B3381995 : Blo 2253435 3381995 := bstep (se 1 (by rfl) ⟨2536496, by rfl⟩ : syracuseStep 3381995 = 5072993) B5072993
theorem B2254663 : Blo 2253435 2254663 := bstep (se 1 (by rfl) ⟨1690997, by rfl⟩ : syracuseStep 2254663 = 3381995) B3381995
theorem B2536501 : Blo 2253435 2536501 := bbase (se 5 (by rfl) ⟨118898, by rfl⟩ : syracuseStep 2536501 = 237797) (by norm_num)
theorem B3382001 : Blo 2253435 3382001 := bstep (se 2 (by rfl) ⟨1268250, by rfl⟩ : syracuseStep 3382001 = 2536501) B2536501
theorem B2254667 : Blo 2253435 2254667 := bstep (se 1 (by rfl) ⟨1691000, by rfl⟩ : syracuseStep 2254667 = 3382001) B3382001
theorem B2853569 : Blo 2253435 2853569 := bbase (se 2 (by rfl) ⟨1070088, by rfl⟩ : syracuseStep 2853569 = 2140177) (by norm_num)
theorem B7609517 : Blo 2253435 7609517 := bstep (se 3 (by rfl) ⟨1426784, by rfl⟩ : syracuseStep 7609517 = 2853569) B2853569
theorem B5073011 : Blo 2253435 5073011 := bstep (se 1 (by rfl) ⟨3804758, by rfl⟩ : syracuseStep 5073011 = 7609517) B7609517
theorem B3382007 : Blo 2253435 3382007 := bstep (se 1 (by rfl) ⟨2536505, by rfl⟩ : syracuseStep 3382007 = 5073011) B5073011
theorem B2254671 : Blo 2253435 2254671 := bstep (se 1 (by rfl) ⟨1691003, by rfl⟩ : syracuseStep 2254671 = 3382007) B3382007
theorem B3382013 : Blo 2253435 3382013 := bbase (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) (by norm_num)
theorem B2254675 : Blo 2253435 2254675 := bstep (se 1 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 2254675 = 3382013) B3382013
theorem B5073029 : Blo 2253435 5073029 := bbase (se 4 (by rfl) ⟨475596, by rfl⟩ : syracuseStep 5073029 = 951193) (by norm_num)
theorem B3382019 : Blo 2253435 3382019 := bstep (se 1 (by rfl) ⟨2536514, by rfl⟩ : syracuseStep 3382019 = 5073029) B5073029
theorem B2254679 : Blo 2253435 2254679 := bstep (se 1 (by rfl) ⟨1691009, by rfl⟩ : syracuseStep 2254679 = 3382019) B3382019
theorem B2708677 : Blo 2253435 2708677 := bbase (se 4 (by rfl) ⟨253938, by rfl⟩ : syracuseStep 2708677 = 507877) (by norm_num)
theorem B3611569 : Blo 2253435 3611569 := bstep (se 2 (by rfl) ⟨1354338, by rfl⟩ : syracuseStep 3611569 = 2708677) B2708677
theorem B4815425 : Blo 2253435 4815425 := bstep (se 2 (by rfl) ⟨1805784, by rfl⟩ : syracuseStep 4815425 = 3611569) B3611569
theorem B3210283 : Blo 2253435 3210283 := bstep (se 1 (by rfl) ⟨2407712, by rfl⟩ : syracuseStep 3210283 = 4815425) B4815425
theorem B4280377 : Blo 2253435 4280377 := bstep (se 2 (by rfl) ⟨1605141, by rfl⟩ : syracuseStep 4280377 = 3210283) B3210283
theorem B5707169 : Blo 2253435 5707169 := bstep (se 2 (by rfl) ⟨2140188, by rfl⟩ : syracuseStep 5707169 = 4280377) B4280377
theorem B3804779 : Blo 2253435 3804779 := bstep (se 1 (by rfl) ⟨2853584, by rfl⟩ : syracuseStep 3804779 = 5707169) B5707169
theorem B2536519 : Blo 2253435 2536519 := bstep (se 1 (by rfl) ⟨1902389, by rfl⟩ : syracuseStep 2536519 = 3804779) B3804779
theorem B3382025 : Blo 2253435 3382025 := bstep (se 2 (by rfl) ⟨1268259, by rfl⟩ : syracuseStep 3382025 = 2536519) B2536519
theorem B2254683 : Blo 2253435 2254683 := bstep (se 1 (by rfl) ⟨1691012, by rfl⟩ : syracuseStep 2254683 = 3382025) B3382025
theorem B11414357 : Blo 2253435 11414357 := bbase (se 9 (by rfl) ⟨33440, by rfl⟩ : syracuseStep 11414357 = 66881) (by norm_num)
theorem B7609571 : Blo 2253435 7609571 := bstep (se 1 (by rfl) ⟨5707178, by rfl⟩ : syracuseStep 7609571 = 11414357) B11414357
theorem B5073047 : Blo 2253435 5073047 := bstep (se 1 (by rfl) ⟨3804785, by rfl⟩ : syracuseStep 5073047 = 7609571) B7609571
theorem B3382031 : Blo 2253435 3382031 := bstep (se 1 (by rfl) ⟨2536523, by rfl⟩ : syracuseStep 3382031 = 5073047) B5073047
theorem B2254687 : Blo 2253435 2254687 := bstep (se 1 (by rfl) ⟨1691015, by rfl⟩ : syracuseStep 2254687 = 3382031) B3382031
theorem B3382037 : Blo 2253435 3382037 := bbase (se 6 (by rfl) ⟨79266, by rfl⟩ : syracuseStep 3382037 = 158533) (by norm_num)
theorem B2254691 : Blo 2253435 2254691 := bstep (se 1 (by rfl) ⟨1691018, by rfl⟩ : syracuseStep 2254691 = 3382037) B3382037
theorem B15045749 : Blo 2253435 15045749 := bbase (se 5 (by rfl) ⟨705269, by rfl⟩ : syracuseStep 15045749 = 1410539) (by norm_num)
theorem B10030499 : Blo 2253435 10030499 := bstep (se 1 (by rfl) ⟨7522874, by rfl⟩ : syracuseStep 10030499 = 15045749) B15045749
theorem B6686999 : Blo 2253435 6686999 := bstep (se 1 (by rfl) ⟨5015249, by rfl⟩ : syracuseStep 6686999 = 10030499) B10030499
theorem B4457999 : Blo 2253435 4457999 := bstep (se 1 (by rfl) ⟨3343499, by rfl⟩ : syracuseStep 4457999 = 6686999) B6686999
theorem B2971999 : Blo 2253435 2971999 := bstep (se 1 (by rfl) ⟨2228999, by rfl⟩ : syracuseStep 2971999 = 4457999) B4457999
theorem B3962665 : Blo 2253435 3962665 := bstep (se 2 (by rfl) ⟨1485999, by rfl⟩ : syracuseStep 3962665 = 2971999) B2971999
theorem B5283553 : Blo 2253435 5283553 := bstep (se 2 (by rfl) ⟨1981332, by rfl⟩ : syracuseStep 5283553 = 3962665) B3962665
theorem B7044737 : Blo 2253435 7044737 := bstep (se 2 (by rfl) ⟨2641776, by rfl⟩ : syracuseStep 7044737 = 5283553) B5283553
theorem B75143861 : Blo 2253435 75143861 := bstep (se 5 (by rfl) ⟨3522368, by rfl⟩ : syracuseStep 75143861 = 7044737) B7044737
theorem B50095907 : Blo 2253435 50095907 := bstep (se 1 (by rfl) ⟨37571930, by rfl⟩ : syracuseStep 50095907 = 75143861) B75143861
theorem B33397271 : Blo 2253435 33397271 := bstep (se 1 (by rfl) ⟨25047953, by rfl⟩ : syracuseStep 33397271 = 50095907) B50095907
theorem B22264847 : Blo 2253435 22264847 := bstep (se 1 (by rfl) ⟨16698635, by rfl⟩ : syracuseStep 22264847 = 33397271) B33397271
theorem B14843231 : Blo 2253435 14843231 := bstep (se 1 (by rfl) ⟨11132423, by rfl⟩ : syracuseStep 14843231 = 22264847) B22264847
theorem B158327797 : Blo 2253435 158327797 := bstep (se 5 (by rfl) ⟨7421615, by rfl⟩ : syracuseStep 158327797 = 14843231) B14843231
theorem B211103729 : Blo 2253435 211103729 := bstep (se 2 (by rfl) ⟨79163898, by rfl⟩ : syracuseStep 211103729 = 158327797) B158327797
theorem B140735819 : Blo 2253435 140735819 := bstep (se 1 (by rfl) ⟨105551864, by rfl⟩ : syracuseStep 140735819 = 211103729) B211103729
theorem B93823879 : Blo 2253435 93823879 := bstep (se 1 (by rfl) ⟨70367909, by rfl⟩ : syracuseStep 93823879 = 140735819) B140735819
theorem B125098505 : Blo 2253435 125098505 := bstep (se 2 (by rfl) ⟨46911939, by rfl⟩ : syracuseStep 125098505 = 93823879) B93823879
theorem B83399003 : Blo 2253435 83399003 := bstep (se 1 (by rfl) ⟨62549252, by rfl⟩ : syracuseStep 83399003 = 125098505) B125098505
theorem B55599335 : Blo 2253435 55599335 := bstep (se 1 (by rfl) ⟨41699501, by rfl⟩ : syracuseStep 55599335 = 83399003) B83399003
theorem B37066223 : Blo 2253435 37066223 := bstep (se 1 (by rfl) ⟨27799667, by rfl⟩ : syracuseStep 37066223 = 55599335) B55599335
theorem B24710815 : Blo 2253435 24710815 := bstep (se 1 (by rfl) ⟨18533111, by rfl⟩ : syracuseStep 24710815 = 37066223) B37066223
theorem B131791013 : Blo 2253435 131791013 := bstep (se 4 (by rfl) ⟨12355407, by rfl⟩ : syracuseStep 131791013 = 24710815) B24710815
theorem B87860675 : Blo 2253435 87860675 := bstep (se 1 (by rfl) ⟨65895506, by rfl⟩ : syracuseStep 87860675 = 131791013) B131791013
theorem B58573783 : Blo 2253435 58573783 := bstep (se 1 (by rfl) ⟨43930337, by rfl⟩ : syracuseStep 58573783 = 87860675) B87860675
theorem B312393509 : Blo 2253435 312393509 := bstep (se 4 (by rfl) ⟨29286891, by rfl⟩ : syracuseStep 312393509 = 58573783) B58573783
theorem B208262339 : Blo 2253435 208262339 := bstep (se 1 (by rfl) ⟨156196754, by rfl⟩ : syracuseStep 208262339 = 312393509) B312393509
theorem B138841559 : Blo 2253435 138841559 := bstep (se 1 (by rfl) ⟨104131169, by rfl⟩ : syracuseStep 138841559 = 208262339) B208262339
theorem B92561039 : Blo 2253435 92561039 := bstep (se 1 (by rfl) ⟨69420779, by rfl⟩ : syracuseStep 92561039 = 138841559) B138841559
theorem B61707359 : Blo 2253435 61707359 := bstep (se 1 (by rfl) ⟨46280519, by rfl⟩ : syracuseStep 61707359 = 92561039) B92561039
theorem B164552957 : Blo 2253435 164552957 := bstep (se 3 (by rfl) ⟨30853679, by rfl⟩ : syracuseStep 164552957 = 61707359) B61707359
theorem B109701971 : Blo 2253435 109701971 := bstep (se 1 (by rfl) ⟨82276478, by rfl⟩ : syracuseStep 109701971 = 164552957) B164552957
theorem B73134647 : Blo 2253435 73134647 := bstep (se 1 (by rfl) ⟨54850985, by rfl⟩ : syracuseStep 73134647 = 109701971) B109701971
theorem B48756431 : Blo 2253435 48756431 := bstep (se 1 (by rfl) ⟨36567323, by rfl⟩ : syracuseStep 48756431 = 73134647) B73134647
theorem B32504287 : Blo 2253435 32504287 := bstep (se 1 (by rfl) ⟨24378215, by rfl⟩ : syracuseStep 32504287 = 48756431) B48756431
theorem B43339049 : Blo 2253435 43339049 := bstep (se 2 (by rfl) ⟨16252143, by rfl⟩ : syracuseStep 43339049 = 32504287) B32504287
theorem B28892699 : Blo 2253435 28892699 := bstep (se 1 (by rfl) ⟨21669524, by rfl⟩ : syracuseStep 28892699 = 43339049) B43339049
theorem B19261799 : Blo 2253435 19261799 := bstep (se 1 (by rfl) ⟨14446349, by rfl⟩ : syracuseStep 19261799 = 28892699) B28892699
theorem B12841199 : Blo 2253435 12841199 := bstep (se 1 (by rfl) ⟨9630899, by rfl⟩ : syracuseStep 12841199 = 19261799) B19261799
theorem B8560799 : Blo 2253435 8560799 := bstep (se 1 (by rfl) ⟨6420599, by rfl⟩ : syracuseStep 8560799 = 12841199) B12841199
theorem B5707199 : Blo 2253435 5707199 := bstep (se 1 (by rfl) ⟨4280399, by rfl⟩ : syracuseStep 5707199 = 8560799) B8560799
theorem B3804799 : Blo 2253435 3804799 := bstep (se 1 (by rfl) ⟨2853599, by rfl⟩ : syracuseStep 3804799 = 5707199) B5707199
theorem B5073065 : Blo 2253435 5073065 := bstep (se 2 (by rfl) ⟨1902399, by rfl⟩ : syracuseStep 5073065 = 3804799) B3804799
theorem B3382043 : Blo 2253435 3382043 := bstep (se 1 (by rfl) ⟨2536532, by rfl⟩ : syracuseStep 3382043 = 5073065) B5073065
theorem B2254695 : Blo 2253435 2254695 := bstep (se 1 (by rfl) ⟨1691021, by rfl⟩ : syracuseStep 2254695 = 3382043) B3382043
theorem B2536537 : Blo 2253435 2536537 := bbase (se 2 (by rfl) ⟨951201, by rfl⟩ : syracuseStep 2536537 = 1902403) (by norm_num)
theorem B3382049 : Blo 2253435 3382049 := bstep (se 2 (by rfl) ⟨1268268, by rfl⟩ : syracuseStep 3382049 = 2536537) B2536537
theorem B2254699 : Blo 2253435 2254699 := bstep (se 1 (by rfl) ⟨1691024, by rfl⟩ : syracuseStep 2254699 = 3382049) B3382049
theorem B4570933 : Blo 2253435 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B6094577 : Blo 2253435 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B4063051 : Blo 2253435 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B5417401 : Blo 2253435 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B7223201 : Blo 2253435 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B4815467 : Blo 2253435 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B3210311 : Blo 2253435 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B8560829 : Blo 2253435 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B5707219 : Blo 2253435 5707219 := bstep (se 1 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 5707219 = 8560829) B8560829
theorem B7609625 : Blo 2253435 7609625 := bstep (se 2 (by rfl) ⟨2853609, by rfl⟩ : syracuseStep 7609625 = 5707219) B5707219
theorem B5073083 : Blo 2253435 5073083 := bstep (se 1 (by rfl) ⟨3804812, by rfl⟩ : syracuseStep 5073083 = 7609625) B7609625
theorem B3382055 : Blo 2253435 3382055 := bstep (se 1 (by rfl) ⟨2536541, by rfl⟩ : syracuseStep 3382055 = 5073083) B5073083
theorem B2254703 : Blo 2253435 2254703 := bstep (se 1 (by rfl) ⟨1691027, by rfl⟩ : syracuseStep 2254703 = 3382055) B3382055
theorem B3382061 : Blo 2253435 3382061 := bbase (se 3 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 3382061 = 1268273) (by norm_num)
theorem B2254707 : Blo 2253435 2254707 := bstep (se 1 (by rfl) ⟨1691030, by rfl⟩ : syracuseStep 2254707 = 3382061) B3382061
theorem B5073101 : Blo 2253435 5073101 := bbase (se 3 (by rfl) ⟨951206, by rfl⟩ : syracuseStep 5073101 = 1902413) (by norm_num)
theorem B3382067 : Blo 2253435 3382067 := bstep (se 1 (by rfl) ⟨2536550, by rfl⟩ : syracuseStep 3382067 = 5073101) B5073101
theorem B2254711 : Blo 2253435 2254711 := bstep (se 1 (by rfl) ⟨1691033, by rfl⟩ : syracuseStep 2254711 = 3382067) B3382067
theorem B2853625 : Blo 2253435 2853625 := bbase (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) (by norm_num)
theorem B3804833 : Blo 2253435 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B2536555 : Blo 2253435 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B3382073 : Blo 2253435 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B2254715 : Blo 2253435 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B4016773 : Blo 2253435 4016773 := bbase (se 4 (by rfl) ⟨376572, by rfl⟩ : syracuseStep 4016773 = 753145) (by norm_num)
theorem B21422789 : Blo 2253435 21422789 := bstep (se 4 (by rfl) ⟨2008386, by rfl⟩ : syracuseStep 21422789 = 4016773) B4016773
theorem B14281859 : Blo 2253435 14281859 := bstep (se 1 (by rfl) ⟨10711394, by rfl⟩ : syracuseStep 14281859 = 21422789) B21422789
theorem B9521239 : Blo 2253435 9521239 := bstep (se 1 (by rfl) ⟨7140929, by rfl⟩ : syracuseStep 9521239 = 14281859) B14281859
theorem B12694985 : Blo 2253435 12694985 := bstep (se 2 (by rfl) ⟨4760619, by rfl⟩ : syracuseStep 12694985 = 9521239) B9521239
theorem B8463323 : Blo 2253435 8463323 := bstep (se 1 (by rfl) ⟨6347492, by rfl⟩ : syracuseStep 8463323 = 12694985) B12694985
theorem B22568861 : Blo 2253435 22568861 := bstep (se 3 (by rfl) ⟨4231661, by rfl⟩ : syracuseStep 22568861 = 8463323) B8463323
theorem B15045907 : Blo 2253435 15045907 := bstep (se 1 (by rfl) ⟨11284430, by rfl⟩ : syracuseStep 15045907 = 22568861) B22568861
theorem B20061209 : Blo 2253435 20061209 := bstep (se 2 (by rfl) ⟨7522953, by rfl⟩ : syracuseStep 20061209 = 15045907) B15045907
theorem B53496557 : Blo 2253435 53496557 := bstep (se 3 (by rfl) ⟨10030604, by rfl⟩ : syracuseStep 53496557 = 20061209) B20061209
theorem B35664371 : Blo 2253435 35664371 := bstep (se 1 (by rfl) ⟨26748278, by rfl⟩ : syracuseStep 35664371 = 53496557) B53496557
theorem B23776247 : Blo 2253435 23776247 := bstep (se 1 (by rfl) ⟨17832185, by rfl⟩ : syracuseStep 23776247 = 35664371) B35664371
theorem B15850831 : Blo 2253435 15850831 := bstep (se 1 (by rfl) ⟨11888123, by rfl⟩ : syracuseStep 15850831 = 23776247) B23776247
theorem B21134441 : Blo 2253435 21134441 := bstep (se 2 (by rfl) ⟨7925415, by rfl⟩ : syracuseStep 21134441 = 15850831) B15850831
theorem B14089627 : Blo 2253435 14089627 := bstep (se 1 (by rfl) ⟨10567220, by rfl⟩ : syracuseStep 14089627 = 21134441) B21134441
theorem B18786169 : Blo 2253435 18786169 := bstep (se 2 (by rfl) ⟨7044813, by rfl⟩ : syracuseStep 18786169 = 14089627) B14089627
theorem B25048225 : Blo 2253435 25048225 := bstep (se 2 (by rfl) ⟨9393084, by rfl⟩ : syracuseStep 25048225 = 18786169) B18786169
theorem B33397633 : Blo 2253435 33397633 := bstep (se 2 (by rfl) ⟨12524112, by rfl⟩ : syracuseStep 33397633 = 25048225) B25048225
theorem B44530177 : Blo 2253435 44530177 := bstep (se 2 (by rfl) ⟨16698816, by rfl⟩ : syracuseStep 44530177 = 33397633) B33397633
theorem B59373569 : Blo 2253435 59373569 := bstep (se 2 (by rfl) ⟨22265088, by rfl⟩ : syracuseStep 59373569 = 44530177) B44530177
theorem B39582379 : Blo 2253435 39582379 := bstep (se 1 (by rfl) ⟨29686784, by rfl⟩ : syracuseStep 39582379 = 59373569) B59373569
theorem B52776505 : Blo 2253435 52776505 := bstep (se 2 (by rfl) ⟨19791189, by rfl⟩ : syracuseStep 52776505 = 39582379) B39582379
theorem B70368673 : Blo 2253435 70368673 := bstep (se 2 (by rfl) ⟨26388252, by rfl⟩ : syracuseStep 70368673 = 52776505) B52776505
theorem B93824897 : Blo 2253435 93824897 := bstep (se 2 (by rfl) ⟨35184336, by rfl⟩ : syracuseStep 93824897 = 70368673) B70368673
theorem B1000798901 : Blo 2253435 1000798901 := bstep (se 5 (by rfl) ⟨46912448, by rfl⟩ : syracuseStep 1000798901 = 93824897) B93824897
theorem B667199267 : Blo 2253435 667199267 := bstep (se 1 (by rfl) ⟨500399450, by rfl⟩ : syracuseStep 667199267 = 1000798901) B1000798901
theorem B444799511 : Blo 2253435 444799511 := bstep (se 1 (by rfl) ⟨333599633, by rfl⟩ : syracuseStep 444799511 = 667199267) B667199267
theorem B296533007 : Blo 2253435 296533007 := bstep (se 1 (by rfl) ⟨222399755, by rfl⟩ : syracuseStep 296533007 = 444799511) B444799511
theorem B197688671 : Blo 2253435 197688671 := bstep (se 1 (by rfl) ⟨148266503, by rfl⟩ : syracuseStep 197688671 = 296533007) B296533007
theorem B131792447 : Blo 2253435 131792447 := bstep (se 1 (by rfl) ⟨98844335, by rfl⟩ : syracuseStep 131792447 = 197688671) B197688671
theorem B87861631 : Blo 2253435 87861631 := bstep (se 1 (by rfl) ⟨65896223, by rfl⟩ : syracuseStep 87861631 = 131792447) B131792447
theorem B117148841 : Blo 2253435 117148841 := bstep (se 2 (by rfl) ⟨43930815, by rfl⟩ : syracuseStep 117148841 = 87861631) B87861631
theorem B78099227 : Blo 2253435 78099227 := bstep (se 1 (by rfl) ⟨58574420, by rfl⟩ : syracuseStep 78099227 = 117148841) B117148841
theorem B52066151 : Blo 2253435 52066151 := bstep (se 1 (by rfl) ⟨39049613, by rfl⟩ : syracuseStep 52066151 = 78099227) B78099227
theorem B34710767 : Blo 2253435 34710767 := bstep (se 1 (by rfl) ⟨26033075, by rfl⟩ : syracuseStep 34710767 = 52066151) B52066151
theorem B23140511 : Blo 2253435 23140511 := bstep (se 1 (by rfl) ⟨17355383, by rfl⟩ : syracuseStep 23140511 = 34710767) B34710767
theorem B15427007 : Blo 2253435 15427007 := bstep (se 1 (by rfl) ⟨11570255, by rfl⟩ : syracuseStep 15427007 = 23140511) B23140511
theorem B10284671 : Blo 2253435 10284671 := bstep (se 1 (by rfl) ⟨7713503, by rfl⟩ : syracuseStep 10284671 = 15427007) B15427007
theorem B6856447 : Blo 2253435 6856447 := bstep (se 1 (by rfl) ⟨5142335, by rfl⟩ : syracuseStep 6856447 = 10284671) B10284671
theorem B9141929 : Blo 2253435 9141929 := bstep (se 2 (by rfl) ⟨3428223, by rfl⟩ : syracuseStep 9141929 = 6856447) B6856447
theorem B6094619 : Blo 2253435 6094619 := bstep (se 1 (by rfl) ⟨4570964, by rfl⟩ : syracuseStep 6094619 = 9141929) B9141929
theorem B4063079 : Blo 2253435 4063079 := bstep (se 1 (by rfl) ⟨3047309, by rfl⟩ : syracuseStep 4063079 = 6094619) B6094619
theorem B10834877 : Blo 2253435 10834877 := bstep (se 3 (by rfl) ⟨2031539, by rfl⟩ : syracuseStep 10834877 = 4063079) B4063079
theorem B7223251 : Blo 2253435 7223251 := bstep (se 1 (by rfl) ⟨5417438, by rfl⟩ : syracuseStep 7223251 = 10834877) B10834877
theorem B9631001 : Blo 2253435 9631001 := bstep (se 2 (by rfl) ⟨3611625, by rfl⟩ : syracuseStep 9631001 = 7223251) B7223251
theorem B25682669 : Blo 2253435 25682669 := bstep (se 3 (by rfl) ⟨4815500, by rfl⟩ : syracuseStep 25682669 = 9631001) B9631001
theorem B17121779 : Blo 2253435 17121779 := bstep (se 1 (by rfl) ⟨12841334, by rfl⟩ : syracuseStep 17121779 = 25682669) B25682669
theorem B11414519 : Blo 2253435 11414519 := bstep (se 1 (by rfl) ⟨8560889, by rfl⟩ : syracuseStep 11414519 = 17121779) B17121779
theorem B7609679 : Blo 2253435 7609679 := bstep (se 1 (by rfl) ⟨5707259, by rfl⟩ : syracuseStep 7609679 = 11414519) B11414519
theorem B5073119 : Blo 2253435 5073119 := bstep (se 1 (by rfl) ⟨3804839, by rfl⟩ : syracuseStep 5073119 = 7609679) B7609679
theorem B3382079 : Blo 2253435 3382079 := bstep (se 1 (by rfl) ⟨2536559, by rfl⟩ : syracuseStep 3382079 = 5073119) B5073119
theorem B2254719 : Blo 2253435 2254719 := bstep (se 1 (by rfl) ⟨1691039, by rfl⟩ : syracuseStep 2254719 = 3382079) B3382079
theorem B3382085 : Blo 2253435 3382085 := bbase (se 4 (by rfl) ⟨317070, by rfl⟩ : syracuseStep 3382085 = 634141) (by norm_num)
theorem B2254723 : Blo 2253435 2254723 := bstep (se 1 (by rfl) ⟨1691042, by rfl⟩ : syracuseStep 2254723 = 3382085) B3382085
theorem B3804853 : Blo 2253435 3804853 := bbase (se 5 (by rfl) ⟨178352, by rfl⟩ : syracuseStep 3804853 = 356705) (by norm_num)
theorem B5073137 : Blo 2253435 5073137 := bstep (se 2 (by rfl) ⟨1902426, by rfl⟩ : syracuseStep 5073137 = 3804853) B3804853
theorem B3382091 : Blo 2253435 3382091 := bstep (se 1 (by rfl) ⟨2536568, by rfl⟩ : syracuseStep 3382091 = 5073137) B5073137
theorem B2254727 : Blo 2253435 2254727 := bstep (se 1 (by rfl) ⟨1691045, by rfl⟩ : syracuseStep 2254727 = 3382091) B3382091
theorem B2536573 : Blo 2253435 2536573 := bbase (se 3 (by rfl) ⟨475607, by rfl⟩ : syracuseStep 2536573 = 951215) (by norm_num)
theorem B3382097 : Blo 2253435 3382097 := bstep (se 2 (by rfl) ⟨1268286, by rfl⟩ : syracuseStep 3382097 = 2536573) B2536573
theorem B2254731 : Blo 2253435 2254731 := bstep (se 1 (by rfl) ⟨1691048, by rfl⟩ : syracuseStep 2254731 = 3382097) B3382097
theorem B7609733 : Blo 2253435 7609733 := bbase (se 4 (by rfl) ⟨713412, by rfl⟩ : syracuseStep 7609733 = 1426825) (by norm_num)
theorem B5073155 : Blo 2253435 5073155 := bstep (se 1 (by rfl) ⟨3804866, by rfl⟩ : syracuseStep 5073155 = 7609733) B7609733
theorem B3382103 : Blo 2253435 3382103 := bstep (se 1 (by rfl) ⟨2536577, by rfl⟩ : syracuseStep 3382103 = 5073155) B5073155
theorem B2254735 : Blo 2253435 2254735 := bstep (se 1 (by rfl) ⟨1691051, by rfl⟩ : syracuseStep 2254735 = 3382103) B3382103
theorem B3382109 : Blo 2253435 3382109 := bbase (se 3 (by rfl) ⟨634145, by rfl⟩ : syracuseStep 3382109 = 1268291) (by norm_num)
theorem B2254739 : Blo 2253435 2254739 := bstep (se 1 (by rfl) ⟨1691054, by rfl⟩ : syracuseStep 2254739 = 3382109) B3382109
theorem B5073173 : Blo 2253435 5073173 := bbase (se 6 (by rfl) ⟨118902, by rfl⟩ : syracuseStep 5073173 = 237805) (by norm_num)
theorem B3382115 : Blo 2253435 3382115 := bstep (se 1 (by rfl) ⟨2536586, by rfl⟩ : syracuseStep 3382115 = 5073173) B5073173
theorem B2254743 : Blo 2253435 2254743 := bstep (se 1 (by rfl) ⟨1691057, by rfl⟩ : syracuseStep 2254743 = 3382115) B3382115
theorem B8560997 : Blo 2253435 8560997 := bbase (se 4 (by rfl) ⟨802593, by rfl⟩ : syracuseStep 8560997 = 1605187) (by norm_num)
theorem B5707331 : Blo 2253435 5707331 := bstep (se 1 (by rfl) ⟨4280498, by rfl⟩ : syracuseStep 5707331 = 8560997) B8560997
theorem B3804887 : Blo 2253435 3804887 := bstep (se 1 (by rfl) ⟨2853665, by rfl⟩ : syracuseStep 3804887 = 5707331) B5707331
theorem B2536591 : Blo 2253435 2536591 := bstep (se 1 (by rfl) ⟨1902443, by rfl⟩ : syracuseStep 2536591 = 3804887) B3804887
theorem B3382121 : Blo 2253435 3382121 := bstep (se 2 (by rfl) ⟨1268295, by rfl⟩ : syracuseStep 3382121 = 2536591) B2536591
theorem B2254747 : Blo 2253435 2254747 := bstep (se 1 (by rfl) ⟨1691060, by rfl⟩ : syracuseStep 2254747 = 3382121) B3382121
theorem B3611677 : Blo 2253435 3611677 := bbase (se 3 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 3611677 = 1354379) (by norm_num)
theorem B4815569 : Blo 2253435 4815569 := bstep (se 2 (by rfl) ⟨1805838, by rfl⟩ : syracuseStep 4815569 = 3611677) B3611677
theorem B12841517 : Blo 2253435 12841517 := bstep (se 3 (by rfl) ⟨2407784, by rfl⟩ : syracuseStep 12841517 = 4815569) B4815569
theorem B8561011 : Blo 2253435 8561011 := bstep (se 1 (by rfl) ⟨6420758, by rfl⟩ : syracuseStep 8561011 = 12841517) B12841517
theorem B11414681 : Blo 2253435 11414681 := bstep (se 2 (by rfl) ⟨4280505, by rfl⟩ : syracuseStep 11414681 = 8561011) B8561011
theorem B7609787 : Blo 2253435 7609787 := bstep (se 1 (by rfl) ⟨5707340, by rfl⟩ : syracuseStep 7609787 = 11414681) B11414681
theorem B5073191 : Blo 2253435 5073191 := bstep (se 1 (by rfl) ⟨3804893, by rfl⟩ : syracuseStep 5073191 = 7609787) B7609787
theorem B3382127 : Blo 2253435 3382127 := bstep (se 1 (by rfl) ⟨2536595, by rfl⟩ : syracuseStep 3382127 = 5073191) B5073191
theorem B2254751 : Blo 2253435 2254751 := bstep (se 1 (by rfl) ⟨1691063, by rfl⟩ : syracuseStep 2254751 = 3382127) B3382127
theorem B3382133 : Blo 2253435 3382133 := bbase (se 5 (by rfl) ⟨158537, by rfl⟩ : syracuseStep 3382133 = 317075) (by norm_num)
theorem B2254755 : Blo 2253435 2254755 := bstep (se 1 (by rfl) ⟨1691066, by rfl⟩ : syracuseStep 2254755 = 3382133) B3382133
theorem B7223381 : Blo 2253435 7223381 := bbase (se 8 (by rfl) ⟨42324, by rfl⟩ : syracuseStep 7223381 = 84649) (by norm_num)
theorem B4815587 : Blo 2253435 4815587 := bstep (se 1 (by rfl) ⟨3611690, by rfl⟩ : syracuseStep 4815587 = 7223381) B7223381
theorem B3210391 : Blo 2253435 3210391 := bstep (se 1 (by rfl) ⟨2407793, by rfl⟩ : syracuseStep 3210391 = 4815587) B4815587
theorem B4280521 : Blo 2253435 4280521 := bstep (se 2 (by rfl) ⟨1605195, by rfl⟩ : syracuseStep 4280521 = 3210391) B3210391
theorem B5707361 : Blo 2253435 5707361 := bstep (se 2 (by rfl) ⟨2140260, by rfl⟩ : syracuseStep 5707361 = 4280521) B4280521
theorem B3804907 : Blo 2253435 3804907 := bstep (se 1 (by rfl) ⟨2853680, by rfl⟩ : syracuseStep 3804907 = 5707361) B5707361
theorem B5073209 : Blo 2253435 5073209 := bstep (se 2 (by rfl) ⟨1902453, by rfl⟩ : syracuseStep 5073209 = 3804907) B3804907
theorem B3382139 : Blo 2253435 3382139 := bstep (se 1 (by rfl) ⟨2536604, by rfl⟩ : syracuseStep 3382139 = 5073209) B5073209
theorem B2254759 : Blo 2253435 2254759 := bstep (se 1 (by rfl) ⟨1691069, by rfl⟩ : syracuseStep 2254759 = 3382139) B3382139
theorem B2536609 : Blo 2253435 2536609 := bbase (se 2 (by rfl) ⟨951228, by rfl⟩ : syracuseStep 2536609 = 1902457) (by norm_num)
theorem B3382145 : Blo 2253435 3382145 := bstep (se 2 (by rfl) ⟨1268304, by rfl⟩ : syracuseStep 3382145 = 2536609) B2536609
theorem B2254763 : Blo 2253435 2254763 := bstep (se 1 (by rfl) ⟨1691072, by rfl⟩ : syracuseStep 2254763 = 3382145) B3382145
theorem B5707381 : Blo 2253435 5707381 := bbase (se 5 (by rfl) ⟨267533, by rfl⟩ : syracuseStep 5707381 = 535067) (by norm_num)
theorem B7609841 : Blo 2253435 7609841 := bstep (se 2 (by rfl) ⟨2853690, by rfl⟩ : syracuseStep 7609841 = 5707381) B5707381
theorem B5073227 : Blo 2253435 5073227 := bstep (se 1 (by rfl) ⟨3804920, by rfl⟩ : syracuseStep 5073227 = 7609841) B7609841
theorem B3382151 : Blo 2253435 3382151 := bstep (se 1 (by rfl) ⟨2536613, by rfl⟩ : syracuseStep 3382151 = 5073227) B5073227
theorem B2254767 : Blo 2253435 2254767 := bstep (se 1 (by rfl) ⟨1691075, by rfl⟩ : syracuseStep 2254767 = 3382151) B3382151
theorem B3382157 : Blo 2253435 3382157 := bbase (se 3 (by rfl) ⟨634154, by rfl⟩ : syracuseStep 3382157 = 1268309) (by norm_num)
theorem B2254771 : Blo 2253435 2254771 := bstep (se 1 (by rfl) ⟨1691078, by rfl⟩ : syracuseStep 2254771 = 3382157) B3382157
theorem B5073245 : Blo 2253435 5073245 := bbase (se 3 (by rfl) ⟨951233, by rfl⟩ : syracuseStep 5073245 = 1902467) (by norm_num)
theorem B3382163 : Blo 2253435 3382163 := bstep (se 1 (by rfl) ⟨2536622, by rfl⟩ : syracuseStep 3382163 = 5073245) B5073245
theorem B2254775 : Blo 2253435 2254775 := bstep (se 1 (by rfl) ⟨1691081, by rfl⟩ : syracuseStep 2254775 = 3382163) B3382163
theorem B3804941 : Blo 2253435 3804941 := bbase (se 3 (by rfl) ⟨713426, by rfl⟩ : syracuseStep 3804941 = 1426853) (by norm_num)
theorem B2536627 : Blo 2253435 2536627 := bstep (se 1 (by rfl) ⟨1902470, by rfl⟩ : syracuseStep 2536627 = 3804941) B3804941
theorem B3382169 : Blo 2253435 3382169 := bstep (se 2 (by rfl) ⟨1268313, by rfl⟩ : syracuseStep 3382169 = 2536627) B2536627
theorem B2254779 : Blo 2253435 2254779 := bstep (se 1 (by rfl) ⟨1691084, by rfl⟩ : syracuseStep 2254779 = 3382169) B3382169
theorem B19262549 : Blo 2253435 19262549 := bbase (se 8 (by rfl) ⟨112866, by rfl⟩ : syracuseStep 19262549 = 225733) (by norm_num)
theorem B12841699 : Blo 2253435 12841699 := bstep (se 1 (by rfl) ⟨9631274, by rfl⟩ : syracuseStep 12841699 = 19262549) B19262549
theorem B17122265 : Blo 2253435 17122265 := bstep (se 2 (by rfl) ⟨6420849, by rfl⟩ : syracuseStep 17122265 = 12841699) B12841699
theorem B11414843 : Blo 2253435 11414843 := bstep (se 1 (by rfl) ⟨8561132, by rfl⟩ : syracuseStep 11414843 = 17122265) B17122265
theorem B7609895 : Blo 2253435 7609895 := bstep (se 1 (by rfl) ⟨5707421, by rfl⟩ : syracuseStep 7609895 = 11414843) B11414843
theorem B5073263 : Blo 2253435 5073263 := bstep (se 1 (by rfl) ⟨3804947, by rfl⟩ : syracuseStep 5073263 = 7609895) B7609895
theorem B3382175 : Blo 2253435 3382175 := bstep (se 1 (by rfl) ⟨2536631, by rfl⟩ : syracuseStep 3382175 = 5073263) B5073263
theorem B2254783 : Blo 2253435 2254783 := bstep (se 1 (by rfl) ⟨1691087, by rfl⟩ : syracuseStep 2254783 = 3382175) B3382175
theorem B3382181 : Blo 2253435 3382181 := bbase (se 4 (by rfl) ⟨317079, by rfl⟩ : syracuseStep 3382181 = 634159) (by norm_num)
theorem B2254787 : Blo 2253435 2254787 := bstep (se 1 (by rfl) ⟨1691090, by rfl⟩ : syracuseStep 2254787 = 3382181) B3382181
theorem B2853721 : Blo 2253435 2853721 := bbase (se 2 (by rfl) ⟨1070145, by rfl⟩ : syracuseStep 2853721 = 2140291) (by norm_num)
theorem B3804961 : Blo 2253435 3804961 := bstep (se 2 (by rfl) ⟨1426860, by rfl⟩ : syracuseStep 3804961 = 2853721) B2853721
theorem B5073281 : Blo 2253435 5073281 := bstep (se 2 (by rfl) ⟨1902480, by rfl⟩ : syracuseStep 5073281 = 3804961) B3804961
theorem B3382187 : Blo 2253435 3382187 := bstep (se 1 (by rfl) ⟨2536640, by rfl⟩ : syracuseStep 3382187 = 5073281) B5073281
theorem B2254791 : Blo 2253435 2254791 := bstep (se 1 (by rfl) ⟨1691093, by rfl⟩ : syracuseStep 2254791 = 3382187) B3382187
theorem B2536645 : Blo 2253435 2536645 := bbase (se 4 (by rfl) ⟨237810, by rfl⟩ : syracuseStep 2536645 = 475621) (by norm_num)
theorem B3382193 : Blo 2253435 3382193 := bstep (se 2 (by rfl) ⟨1268322, by rfl⟩ : syracuseStep 3382193 = 2536645) B2536645
theorem B2254795 : Blo 2253435 2254795 := bstep (se 1 (by rfl) ⟨1691096, by rfl⟩ : syracuseStep 2254795 = 3382193) B3382193
theorem B4280597 : Blo 2253435 4280597 := bbase (se 6 (by rfl) ⟨100326, by rfl⟩ : syracuseStep 4280597 = 200653) (by norm_num)
theorem B2853731 : Blo 2253435 2853731 := bstep (se 1 (by rfl) ⟨2140298, by rfl⟩ : syracuseStep 2853731 = 4280597) B4280597
theorem B7609949 : Blo 2253435 7609949 := bstep (se 3 (by rfl) ⟨1426865, by rfl⟩ : syracuseStep 7609949 = 2853731) B2853731
theorem B5073299 : Blo 2253435 5073299 := bstep (se 1 (by rfl) ⟨3804974, by rfl⟩ : syracuseStep 5073299 = 7609949) B7609949
theorem B3382199 : Blo 2253435 3382199 := bstep (se 1 (by rfl) ⟨2536649, by rfl⟩ : syracuseStep 3382199 = 5073299) B5073299
theorem B2254799 : Blo 2253435 2254799 := bstep (se 1 (by rfl) ⟨1691099, by rfl⟩ : syracuseStep 2254799 = 3382199) B3382199
theorem B3382205 : Blo 2253435 3382205 := bbase (se 3 (by rfl) ⟨634163, by rfl⟩ : syracuseStep 3382205 = 1268327) (by norm_num)
theorem B2254803 : Blo 2253435 2254803 := bstep (se 1 (by rfl) ⟨1691102, by rfl⟩ : syracuseStep 2254803 = 3382205) B3382205
theorem B5073317 : Blo 2253435 5073317 := bbase (se 4 (by rfl) ⟨475623, by rfl⟩ : syracuseStep 5073317 = 951247) (by norm_num)
theorem B3382211 : Blo 2253435 3382211 := bstep (se 1 (by rfl) ⟨2536658, by rfl⟩ : syracuseStep 3382211 = 5073317) B5073317
theorem B2254807 : Blo 2253435 2254807 := bstep (se 1 (by rfl) ⟨1691105, by rfl⟩ : syracuseStep 2254807 = 3382211) B3382211
theorem B5707493 : Blo 2253435 5707493 := bbase (se 4 (by rfl) ⟨535077, by rfl⟩ : syracuseStep 5707493 = 1070155) (by norm_num)
theorem B3804995 : Blo 2253435 3804995 := bstep (se 1 (by rfl) ⟨2853746, by rfl⟩ : syracuseStep 3804995 = 5707493) B5707493
theorem B2536663 : Blo 2253435 2536663 := bstep (se 1 (by rfl) ⟨1902497, by rfl⟩ : syracuseStep 2536663 = 3804995) B3804995
theorem B3382217 : Blo 2253435 3382217 := bstep (se 2 (by rfl) ⟨1268331, by rfl⟩ : syracuseStep 3382217 = 2536663) B2536663
theorem B2254811 : Blo 2253435 2254811 := bstep (se 1 (by rfl) ⟨1691108, by rfl⟩ : syracuseStep 2254811 = 3382217) B3382217
theorem B2407853 : Blo 2253435 2407853 := bbase (se 3 (by rfl) ⟨451472, by rfl⟩ : syracuseStep 2407853 = 902945) (by norm_num)
theorem B6420941 : Blo 2253435 6420941 := bstep (se 3 (by rfl) ⟨1203926, by rfl⟩ : syracuseStep 6420941 = 2407853) B2407853
theorem B4280627 : Blo 2253435 4280627 := bstep (se 1 (by rfl) ⟨3210470, by rfl⟩ : syracuseStep 4280627 = 6420941) B6420941
theorem B11415005 : Blo 2253435 11415005 := bstep (se 3 (by rfl) ⟨2140313, by rfl⟩ : syracuseStep 11415005 = 4280627) B4280627
theorem B7610003 : Blo 2253435 7610003 := bstep (se 1 (by rfl) ⟨5707502, by rfl⟩ : syracuseStep 7610003 = 11415005) B11415005
theorem B5073335 : Blo 2253435 5073335 := bstep (se 1 (by rfl) ⟨3805001, by rfl⟩ : syracuseStep 5073335 = 7610003) B7610003
theorem B3382223 : Blo 2253435 3382223 := bstep (se 1 (by rfl) ⟨2536667, by rfl⟩ : syracuseStep 3382223 = 5073335) B5073335
theorem B2254815 : Blo 2253435 2254815 := bstep (se 1 (by rfl) ⟨1691111, by rfl⟩ : syracuseStep 2254815 = 3382223) B3382223
theorem B3382229 : Blo 2253435 3382229 := bbase (se 7 (by rfl) ⟨39635, by rfl⟩ : syracuseStep 3382229 = 79271) (by norm_num)
theorem B2254819 : Blo 2253435 2254819 := bstep (se 1 (by rfl) ⟨1691114, by rfl⟩ : syracuseStep 2254819 = 3382229) B3382229
theorem B8561285 : Blo 2253435 8561285 := bbase (se 4 (by rfl) ⟨802620, by rfl⟩ : syracuseStep 8561285 = 1605241) (by norm_num)
theorem B5707523 : Blo 2253435 5707523 := bstep (se 1 (by rfl) ⟨4280642, by rfl⟩ : syracuseStep 5707523 = 8561285) B8561285
theorem B3805015 : Blo 2253435 3805015 := bstep (se 1 (by rfl) ⟨2853761, by rfl⟩ : syracuseStep 3805015 = 5707523) B5707523
theorem B5073353 : Blo 2253435 5073353 := bstep (se 2 (by rfl) ⟨1902507, by rfl⟩ : syracuseStep 5073353 = 3805015) B3805015
theorem B3382235 : Blo 2253435 3382235 := bstep (se 1 (by rfl) ⟨2536676, by rfl⟩ : syracuseStep 3382235 = 5073353) B5073353
theorem B2254823 : Blo 2253435 2254823 := bstep (se 1 (by rfl) ⟨1691117, by rfl⟩ : syracuseStep 2254823 = 3382235) B3382235
theorem B2536681 : Blo 2253435 2536681 := bbase (se 2 (by rfl) ⟨951255, by rfl⟩ : syracuseStep 2536681 = 1902511) (by norm_num)
theorem B3382241 : Blo 2253435 3382241 := bstep (se 2 (by rfl) ⟨1268340, by rfl⟩ : syracuseStep 3382241 = 2536681) B2536681
theorem B2254827 : Blo 2253435 2254827 := bstep (se 1 (by rfl) ⟨1691120, by rfl⟩ : syracuseStep 2254827 = 3382241) B3382241
theorem B12841973 : Blo 2253435 12841973 := bbase (se 5 (by rfl) ⟨601967, by rfl⟩ : syracuseStep 12841973 = 1203935) (by norm_num)
theorem B8561315 : Blo 2253435 8561315 := bstep (se 1 (by rfl) ⟨6420986, by rfl⟩ : syracuseStep 8561315 = 12841973) B12841973
theorem B5707543 : Blo 2253435 5707543 := bstep (se 1 (by rfl) ⟨4280657, by rfl⟩ : syracuseStep 5707543 = 8561315) B8561315
theorem B7610057 : Blo 2253435 7610057 := bstep (se 2 (by rfl) ⟨2853771, by rfl⟩ : syracuseStep 7610057 = 5707543) B5707543
theorem B5073371 : Blo 2253435 5073371 := bstep (se 1 (by rfl) ⟨3805028, by rfl⟩ : syracuseStep 5073371 = 7610057) B7610057
theorem B3382247 : Blo 2253435 3382247 := bstep (se 1 (by rfl) ⟨2536685, by rfl⟩ : syracuseStep 3382247 = 5073371) B5073371
theorem B2254831 : Blo 2253435 2254831 := bstep (se 1 (by rfl) ⟨1691123, by rfl⟩ : syracuseStep 2254831 = 3382247) B3382247
theorem B3382253 : Blo 2253435 3382253 := bbase (se 3 (by rfl) ⟨634172, by rfl⟩ : syracuseStep 3382253 = 1268345) (by norm_num)
theorem B2254835 : Blo 2253435 2254835 := bstep (se 1 (by rfl) ⟨1691126, by rfl⟩ : syracuseStep 2254835 = 3382253) B3382253
theorem B5073389 : Blo 2253435 5073389 := bbase (se 3 (by rfl) ⟨951260, by rfl⟩ : syracuseStep 5073389 = 1902521) (by norm_num)
theorem B3382259 : Blo 2253435 3382259 := bstep (se 1 (by rfl) ⟨2536694, by rfl⟩ : syracuseStep 3382259 = 5073389) B5073389
theorem B2254839 : Blo 2253435 2254839 := bstep (se 1 (by rfl) ⟨1691129, by rfl⟩ : syracuseStep 2254839 = 3382259) B3382259
theorem B10835477 : Blo 2253435 10835477 := bbase (se 6 (by rfl) ⟨253956, by rfl⟩ : syracuseStep 10835477 = 507913) (by norm_num)
theorem B7223651 : Blo 2253435 7223651 := bstep (se 1 (by rfl) ⟨5417738, by rfl⟩ : syracuseStep 7223651 = 10835477) B10835477
theorem B4815767 : Blo 2253435 4815767 := bstep (se 1 (by rfl) ⟨3611825, by rfl⟩ : syracuseStep 4815767 = 7223651) B7223651
theorem B3210511 : Blo 2253435 3210511 := bstep (se 1 (by rfl) ⟨2407883, by rfl⟩ : syracuseStep 3210511 = 4815767) B4815767
theorem B4280681 : Blo 2253435 4280681 := bstep (se 2 (by rfl) ⟨1605255, by rfl⟩ : syracuseStep 4280681 = 3210511) B3210511
theorem B2853787 : Blo 2253435 2853787 := bstep (se 1 (by rfl) ⟨2140340, by rfl⟩ : syracuseStep 2853787 = 4280681) B4280681
theorem B3805049 : Blo 2253435 3805049 := bstep (se 2 (by rfl) ⟨1426893, by rfl⟩ : syracuseStep 3805049 = 2853787) B2853787
theorem B2536699 : Blo 2253435 2536699 := bstep (se 1 (by rfl) ⟨1902524, by rfl⟩ : syracuseStep 2536699 = 3805049) B3805049
theorem B3382265 : Blo 2253435 3382265 := bstep (se 2 (by rfl) ⟨1268349, by rfl⟩ : syracuseStep 3382265 = 2536699) B2536699
theorem B2254843 : Blo 2253435 2254843 := bstep (se 1 (by rfl) ⟨1691132, by rfl⟩ : syracuseStep 2254843 = 3382265) B3382265
theorem B19792309 : Blo 2253435 19792309 := bbase (se 5 (by rfl) ⟨927764, by rfl⟩ : syracuseStep 19792309 = 1855529) (by norm_num)
theorem B26389745 : Blo 2253435 26389745 := bstep (se 2 (by rfl) ⟨9896154, by rfl⟩ : syracuseStep 26389745 = 19792309) B19792309
theorem B17593163 : Blo 2253435 17593163 := bstep (se 1 (by rfl) ⟨13194872, by rfl⟩ : syracuseStep 17593163 = 26389745) B26389745
theorem B11728775 : Blo 2253435 11728775 := bstep (se 1 (by rfl) ⟨8796581, by rfl⟩ : syracuseStep 11728775 = 17593163) B17593163
theorem B7819183 : Blo 2253435 7819183 := bstep (se 1 (by rfl) ⟨5864387, by rfl⟩ : syracuseStep 7819183 = 11728775) B11728775
theorem B10425577 : Blo 2253435 10425577 := bstep (se 2 (by rfl) ⟨3909591, by rfl⟩ : syracuseStep 10425577 = 7819183) B7819183
theorem B13900769 : Blo 2253435 13900769 := bstep (se 2 (by rfl) ⟨5212788, by rfl⟩ : syracuseStep 13900769 = 10425577) B10425577
theorem B9267179 : Blo 2253435 9267179 := bstep (se 1 (by rfl) ⟨6950384, by rfl⟩ : syracuseStep 9267179 = 13900769) B13900769
theorem B98849909 : Blo 2253435 98849909 := bstep (se 5 (by rfl) ⟨4633589, by rfl⟩ : syracuseStep 98849909 = 9267179) B9267179
theorem B263599757 : Blo 2253435 263599757 := bstep (se 3 (by rfl) ⟨49424954, by rfl⟩ : syracuseStep 263599757 = 98849909) B98849909
theorem B175733171 : Blo 2253435 175733171 := bstep (se 1 (by rfl) ⟨131799878, by rfl⟩ : syracuseStep 175733171 = 263599757) B263599757
theorem B117155447 : Blo 2253435 117155447 := bstep (se 1 (by rfl) ⟨87866585, by rfl⟩ : syracuseStep 117155447 = 175733171) B175733171
theorem B78103631 : Blo 2253435 78103631 := bstep (se 1 (by rfl) ⟨58577723, by rfl⟩ : syracuseStep 78103631 = 117155447) B117155447
theorem B52069087 : Blo 2253435 52069087 := bstep (se 1 (by rfl) ⟨39051815, by rfl⟩ : syracuseStep 52069087 = 78103631) B78103631
theorem B277701797 : Blo 2253435 277701797 := bstep (se 4 (by rfl) ⟨26034543, by rfl⟩ : syracuseStep 277701797 = 52069087) B52069087
theorem B740538125 : Blo 2253435 740538125 := bstep (se 3 (by rfl) ⟨138850898, by rfl⟩ : syracuseStep 740538125 = 277701797) B277701797
theorem B493692083 : Blo 2253435 493692083 := bstep (se 1 (by rfl) ⟨370269062, by rfl⟩ : syracuseStep 493692083 = 740538125) B740538125
theorem B329128055 : Blo 2253435 329128055 := bstep (se 1 (by rfl) ⟨246846041, by rfl⟩ : syracuseStep 329128055 = 493692083) B493692083
theorem B219418703 : Blo 2253435 219418703 := bstep (se 1 (by rfl) ⟨164564027, by rfl⟩ : syracuseStep 219418703 = 329128055) B329128055
theorem B146279135 : Blo 2253435 146279135 := bstep (se 1 (by rfl) ⟨109709351, by rfl⟩ : syracuseStep 146279135 = 219418703) B219418703
theorem B97519423 : Blo 2253435 97519423 := bstep (se 1 (by rfl) ⟨73139567, by rfl⟩ : syracuseStep 97519423 = 146279135) B146279135
theorem B130025897 : Blo 2253435 130025897 := bstep (se 2 (by rfl) ⟨48759711, by rfl⟩ : syracuseStep 130025897 = 97519423) B97519423
theorem B86683931 : Blo 2253435 86683931 := bstep (se 1 (by rfl) ⟨65012948, by rfl⟩ : syracuseStep 86683931 = 130025897) B130025897
theorem B57789287 : Blo 2253435 57789287 := bstep (se 1 (by rfl) ⟨43341965, by rfl⟩ : syracuseStep 57789287 = 86683931) B86683931
theorem B38526191 : Blo 2253435 38526191 := bstep (se 1 (by rfl) ⟨28894643, by rfl⟩ : syracuseStep 38526191 = 57789287) B57789287
theorem B25684127 : Blo 2253435 25684127 := bstep (se 1 (by rfl) ⟨19263095, by rfl⟩ : syracuseStep 25684127 = 38526191) B38526191
theorem B17122751 : Blo 2253435 17122751 := bstep (se 1 (by rfl) ⟨12842063, by rfl⟩ : syracuseStep 17122751 = 25684127) B25684127
theorem B11415167 : Blo 2253435 11415167 := bstep (se 1 (by rfl) ⟨8561375, by rfl⟩ : syracuseStep 11415167 = 17122751) B17122751
theorem B7610111 : Blo 2253435 7610111 := bstep (se 1 (by rfl) ⟨5707583, by rfl⟩ : syracuseStep 7610111 = 11415167) B11415167
theorem B5073407 : Blo 2253435 5073407 := bstep (se 1 (by rfl) ⟨3805055, by rfl⟩ : syracuseStep 5073407 = 7610111) B7610111
theorem B3382271 : Blo 2253435 3382271 := bstep (se 1 (by rfl) ⟨2536703, by rfl⟩ : syracuseStep 3382271 = 5073407) B5073407
theorem B2254847 : Blo 2253435 2254847 := bstep (se 1 (by rfl) ⟨1691135, by rfl⟩ : syracuseStep 2254847 = 3382271) B3382271
theorem B3382277 : Blo 2253435 3382277 := bbase (se 4 (by rfl) ⟨317088, by rfl⟩ : syracuseStep 3382277 = 634177) (by norm_num)
theorem B2254851 : Blo 2253435 2254851 := bstep (se 1 (by rfl) ⟨1691138, by rfl⟩ : syracuseStep 2254851 = 3382277) B3382277
theorem B3805069 : Blo 2253435 3805069 := bbase (se 3 (by rfl) ⟨713450, by rfl⟩ : syracuseStep 3805069 = 1426901) (by norm_num)
theorem B5073425 : Blo 2253435 5073425 := bstep (se 2 (by rfl) ⟨1902534, by rfl⟩ : syracuseStep 5073425 = 3805069) B3805069
theorem B3382283 : Blo 2253435 3382283 := bstep (se 1 (by rfl) ⟨2536712, by rfl⟩ : syracuseStep 3382283 = 5073425) B5073425
theorem B2254855 : Blo 2253435 2254855 := bstep (se 1 (by rfl) ⟨1691141, by rfl⟩ : syracuseStep 2254855 = 3382283) B3382283
theorem B2536717 : Blo 2253435 2536717 := bbase (se 3 (by rfl) ⟨475634, by rfl⟩ : syracuseStep 2536717 = 951269) (by norm_num)
theorem B3382289 : Blo 2253435 3382289 := bstep (se 2 (by rfl) ⟨1268358, by rfl⟩ : syracuseStep 3382289 = 2536717) B2536717
theorem B2254859 : Blo 2253435 2254859 := bstep (se 1 (by rfl) ⟨1691144, by rfl⟩ : syracuseStep 2254859 = 3382289) B3382289
theorem B7610165 : Blo 2253435 7610165 := bbase (se 5 (by rfl) ⟨356726, by rfl⟩ : syracuseStep 7610165 = 713453) (by norm_num)
theorem B5073443 : Blo 2253435 5073443 := bstep (se 1 (by rfl) ⟨3805082, by rfl⟩ : syracuseStep 5073443 = 7610165) B7610165
theorem B3382295 : Blo 2253435 3382295 := bstep (se 1 (by rfl) ⟨2536721, by rfl⟩ : syracuseStep 3382295 = 5073443) B5073443
theorem B2254863 : Blo 2253435 2254863 := bstep (se 1 (by rfl) ⟨1691147, by rfl⟩ : syracuseStep 2254863 = 3382295) B3382295
theorem B3382301 : Blo 2253435 3382301 := bbase (se 3 (by rfl) ⟨634181, by rfl⟩ : syracuseStep 3382301 = 1268363) (by norm_num)
theorem B2254867 : Blo 2253435 2254867 := bstep (se 1 (by rfl) ⟨1691150, by rfl⟩ : syracuseStep 2254867 = 3382301) B3382301
theorem B5073461 : Blo 2253435 5073461 := bbase (se 5 (by rfl) ⟨237818, by rfl⟩ : syracuseStep 5073461 = 475637) (by norm_num)
theorem B3382307 : Blo 2253435 3382307 := bstep (se 1 (by rfl) ⟨2536730, by rfl⟩ : syracuseStep 3382307 = 5073461) B5073461
theorem B2254871 : Blo 2253435 2254871 := bstep (se 1 (by rfl) ⟨1691153, by rfl⟩ : syracuseStep 2254871 = 3382307) B3382307
theorem B9631669 : Blo 2253435 9631669 := bbase (se 5 (by rfl) ⟨451484, by rfl⟩ : syracuseStep 9631669 = 902969) (by norm_num)
theorem B12842225 : Blo 2253435 12842225 := bstep (se 2 (by rfl) ⟨4815834, by rfl⟩ : syracuseStep 12842225 = 9631669) B9631669
theorem B8561483 : Blo 2253435 8561483 := bstep (se 1 (by rfl) ⟨6421112, by rfl⟩ : syracuseStep 8561483 = 12842225) B12842225
theorem B5707655 : Blo 2253435 5707655 := bstep (se 1 (by rfl) ⟨4280741, by rfl⟩ : syracuseStep 5707655 = 8561483) B8561483
theorem B3805103 : Blo 2253435 3805103 := bstep (se 1 (by rfl) ⟨2853827, by rfl⟩ : syracuseStep 3805103 = 5707655) B5707655
theorem B2536735 : Blo 2253435 2536735 := bstep (se 1 (by rfl) ⟨1902551, by rfl⟩ : syracuseStep 2536735 = 3805103) B3805103
theorem B3382313 : Blo 2253435 3382313 := bstep (se 2 (by rfl) ⟨1268367, by rfl⟩ : syracuseStep 3382313 = 2536735) B2536735
theorem B2254875 : Blo 2253435 2254875 := bstep (se 1 (by rfl) ⟨1691156, by rfl⟩ : syracuseStep 2254875 = 3382313) B3382313
theorem B9631685 : Blo 2253435 9631685 := bbase (se 4 (by rfl) ⟨902970, by rfl⟩ : syracuseStep 9631685 = 1805941) (by norm_num)
theorem B6421123 : Blo 2253435 6421123 := bstep (se 1 (by rfl) ⟨4815842, by rfl⟩ : syracuseStep 6421123 = 9631685) B9631685
theorem B8561497 : Blo 2253435 8561497 := bstep (se 2 (by rfl) ⟨3210561, by rfl⟩ : syracuseStep 8561497 = 6421123) B6421123
theorem B11415329 : Blo 2253435 11415329 := bstep (se 2 (by rfl) ⟨4280748, by rfl⟩ : syracuseStep 11415329 = 8561497) B8561497
theorem B7610219 : Blo 2253435 7610219 := bstep (se 1 (by rfl) ⟨5707664, by rfl⟩ : syracuseStep 7610219 = 11415329) B11415329
theorem B5073479 : Blo 2253435 5073479 := bstep (se 1 (by rfl) ⟨3805109, by rfl⟩ : syracuseStep 5073479 = 7610219) B7610219
theorem B3382319 : Blo 2253435 3382319 := bstep (se 1 (by rfl) ⟨2536739, by rfl⟩ : syracuseStep 3382319 = 5073479) B5073479
theorem B2254879 : Blo 2253435 2254879 := bstep (se 1 (by rfl) ⟨1691159, by rfl⟩ : syracuseStep 2254879 = 3382319) B3382319
theorem B3382325 : Blo 2253435 3382325 := bbase (se 5 (by rfl) ⟨158546, by rfl⟩ : syracuseStep 3382325 = 317093) (by norm_num)
theorem B2254883 : Blo 2253435 2254883 := bstep (se 1 (by rfl) ⟨1691162, by rfl⟩ : syracuseStep 2254883 = 3382325) B3382325
theorem B5707685 : Blo 2253435 5707685 := bbase (se 4 (by rfl) ⟨535095, by rfl⟩ : syracuseStep 5707685 = 1070191) (by norm_num)
theorem B3805123 : Blo 2253435 3805123 := bstep (se 1 (by rfl) ⟨2853842, by rfl⟩ : syracuseStep 3805123 = 5707685) B5707685
theorem B5073497 : Blo 2253435 5073497 := bstep (se 2 (by rfl) ⟨1902561, by rfl⟩ : syracuseStep 5073497 = 3805123) B3805123
theorem B3382331 : Blo 2253435 3382331 := bstep (se 1 (by rfl) ⟨2536748, by rfl⟩ : syracuseStep 3382331 = 5073497) B5073497
theorem B2254887 : Blo 2253435 2254887 := bstep (se 1 (by rfl) ⟨1691165, by rfl⟩ : syracuseStep 2254887 = 3382331) B3382331
theorem B2536753 : Blo 2253435 2536753 := bbase (se 2 (by rfl) ⟨951282, by rfl⟩ : syracuseStep 2536753 = 1902565) (by norm_num)
theorem B3382337 : Blo 2253435 3382337 := bstep (se 2 (by rfl) ⟨1268376, by rfl⟩ : syracuseStep 3382337 = 2536753) B2536753
theorem B2254891 : Blo 2253435 2254891 := bstep (se 1 (by rfl) ⟨1691168, by rfl⟩ : syracuseStep 2254891 = 3382337) B3382337
theorem B4815877 : Blo 2253435 4815877 := bbase (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) (by norm_num)
theorem B6421169 : Blo 2253435 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B4280779 : Blo 2253435 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B5707705 : Blo 2253435 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B7610273 : Blo 2253435 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B5073515 : Blo 2253435 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B3382343 : Blo 2253435 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B2254895 : Blo 2253435 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B3382349 : Blo 2253435 3382349 := bbase (se 3 (by rfl) ⟨634190, by rfl⟩ : syracuseStep 3382349 = 1268381) (by norm_num)
theorem B2254899 : Blo 2253435 2254899 := bstep (se 1 (by rfl) ⟨1691174, by rfl⟩ : syracuseStep 2254899 = 3382349) B3382349
theorem B5073533 : Blo 2253435 5073533 := bbase (se 3 (by rfl) ⟨951287, by rfl⟩ : syracuseStep 5073533 = 1902575) (by norm_num)
theorem B3382355 : Blo 2253435 3382355 := bstep (se 1 (by rfl) ⟨2536766, by rfl⟩ : syracuseStep 3382355 = 5073533) B5073533
theorem B2254903 : Blo 2253435 2254903 := bstep (se 1 (by rfl) ⟨1691177, by rfl⟩ : syracuseStep 2254903 = 3382355) B3382355
theorem B3805157 : Blo 2253435 3805157 := bbase (se 4 (by rfl) ⟨356733, by rfl⟩ : syracuseStep 3805157 = 713467) (by norm_num)
theorem B2536771 : Blo 2253435 2536771 := bstep (se 1 (by rfl) ⟨1902578, by rfl⟩ : syracuseStep 2536771 = 3805157) B3805157
theorem B3382361 : Blo 2253435 3382361 := bstep (se 2 (by rfl) ⟨1268385, by rfl⟩ : syracuseStep 3382361 = 2536771) B2536771
theorem B2254907 : Blo 2253435 2254907 := bstep (se 1 (by rfl) ⟨1691180, by rfl⟩ : syracuseStep 2254907 = 3382361) B3382361
theorem B2285677 : Blo 2253435 2285677 := bbase (se 3 (by rfl) ⟨428564, by rfl⟩ : syracuseStep 2285677 = 857129) (by norm_num)
theorem B12190277 : Blo 2253435 12190277 := bstep (se 4 (by rfl) ⟨1142838, by rfl⟩ : syracuseStep 12190277 = 2285677) B2285677
theorem B8126851 : Blo 2253435 8126851 := bstep (se 1 (by rfl) ⟨6095138, by rfl⟩ : syracuseStep 8126851 = 12190277) B12190277
theorem B10835801 : Blo 2253435 10835801 := bstep (se 2 (by rfl) ⟨4063425, by rfl⟩ : syracuseStep 10835801 = 8126851) B8126851
theorem B7223867 : Blo 2253435 7223867 := bstep (se 1 (by rfl) ⟨5417900, by rfl⟩ : syracuseStep 7223867 = 10835801) B10835801
theorem B4815911 : Blo 2253435 4815911 := bstep (se 1 (by rfl) ⟨3611933, by rfl⟩ : syracuseStep 4815911 = 7223867) B7223867
theorem B3210607 : Blo 2253435 3210607 := bstep (se 1 (by rfl) ⟨2407955, by rfl⟩ : syracuseStep 3210607 = 4815911) B4815911
theorem B17123237 : Blo 2253435 17123237 := bstep (se 4 (by rfl) ⟨1605303, by rfl⟩ : syracuseStep 17123237 = 3210607) B3210607
theorem B11415491 : Blo 2253435 11415491 := bstep (se 1 (by rfl) ⟨8561618, by rfl⟩ : syracuseStep 11415491 = 17123237) B17123237
theorem B7610327 : Blo 2253435 7610327 := bstep (se 1 (by rfl) ⟨5707745, by rfl⟩ : syracuseStep 7610327 = 11415491) B11415491
theorem B5073551 : Blo 2253435 5073551 := bstep (se 1 (by rfl) ⟨3805163, by rfl⟩ : syracuseStep 5073551 = 7610327) B7610327
theorem B3382367 : Blo 2253435 3382367 := bstep (se 1 (by rfl) ⟨2536775, by rfl⟩ : syracuseStep 3382367 = 5073551) B5073551
theorem B2254911 : Blo 2253435 2254911 := bstep (se 1 (by rfl) ⟨1691183, by rfl⟩ : syracuseStep 2254911 = 3382367) B3382367
theorem B3382373 : Blo 2253435 3382373 := bbase (se 4 (by rfl) ⟨317097, by rfl⟩ : syracuseStep 3382373 = 634195) (by norm_num)
theorem B2254915 : Blo 2253435 2254915 := bstep (se 1 (by rfl) ⟨1691186, by rfl⟩ : syracuseStep 2254915 = 3382373) B3382373
theorem B3047581 : Blo 2253435 3047581 := bbase (se 3 (by rfl) ⟨571421, by rfl⟩ : syracuseStep 3047581 = 1142843) (by norm_num)
theorem B4063441 : Blo 2253435 4063441 := bstep (se 2 (by rfl) ⟨1523790, by rfl⟩ : syracuseStep 4063441 = 3047581) B3047581
theorem B5417921 : Blo 2253435 5417921 := bstep (se 2 (by rfl) ⟨2031720, by rfl⟩ : syracuseStep 5417921 = 4063441) B4063441
theorem B3611947 : Blo 2253435 3611947 := bstep (se 1 (by rfl) ⟨2708960, by rfl⟩ : syracuseStep 3611947 = 5417921) B5417921
theorem B4815929 : Blo 2253435 4815929 := bstep (se 2 (by rfl) ⟨1805973, by rfl⟩ : syracuseStep 4815929 = 3611947) B3611947
theorem B3210619 : Blo 2253435 3210619 := bstep (se 1 (by rfl) ⟨2407964, by rfl⟩ : syracuseStep 3210619 = 4815929) B4815929
theorem B4280825 : Blo 2253435 4280825 := bstep (se 2 (by rfl) ⟨1605309, by rfl⟩ : syracuseStep 4280825 = 3210619) B3210619
theorem B2853883 : Blo 2253435 2853883 := bstep (se 1 (by rfl) ⟨2140412, by rfl⟩ : syracuseStep 2853883 = 4280825) B4280825
theorem B3805177 : Blo 2253435 3805177 := bstep (se 2 (by rfl) ⟨1426941, by rfl⟩ : syracuseStep 3805177 = 2853883) B2853883
theorem B5073569 : Blo 2253435 5073569 := bstep (se 2 (by rfl) ⟨1902588, by rfl⟩ : syracuseStep 5073569 = 3805177) B3805177
theorem B3382379 : Blo 2253435 3382379 := bstep (se 1 (by rfl) ⟨2536784, by rfl⟩ : syracuseStep 3382379 = 5073569) B5073569
theorem B2254919 : Blo 2253435 2254919 := bstep (se 1 (by rfl) ⟨1691189, by rfl⟩ : syracuseStep 2254919 = 3382379) B3382379
theorem B2536789 : Blo 2253435 2536789 := bbase (se 13 (by rfl) ⟨464, by rfl⟩ : syracuseStep 2536789 = 929) (by norm_num)
theorem B3382385 : Blo 2253435 3382385 := bstep (se 2 (by rfl) ⟨1268394, by rfl⟩ : syracuseStep 3382385 = 2536789) B2536789
theorem B2254923 : Blo 2253435 2254923 := bstep (se 1 (by rfl) ⟨1691192, by rfl⟩ : syracuseStep 2254923 = 3382385) B3382385
theorem B2853893 : Blo 2253435 2853893 := bbase (se 4 (by rfl) ⟨267552, by rfl⟩ : syracuseStep 2853893 = 535105) (by norm_num)
theorem B7610381 : Blo 2253435 7610381 := bstep (se 3 (by rfl) ⟨1426946, by rfl⟩ : syracuseStep 7610381 = 2853893) B2853893
theorem B5073587 : Blo 2253435 5073587 := bstep (se 1 (by rfl) ⟨3805190, by rfl⟩ : syracuseStep 5073587 = 7610381) B7610381
theorem B3382391 : Blo 2253435 3382391 := bstep (se 1 (by rfl) ⟨2536793, by rfl⟩ : syracuseStep 3382391 = 5073587) B5073587
theorem B2254927 : Blo 2253435 2254927 := bstep (se 1 (by rfl) ⟨1691195, by rfl⟩ : syracuseStep 2254927 = 3382391) B3382391
theorem B3382397 : Blo 2253435 3382397 := bbase (se 3 (by rfl) ⟨634199, by rfl⟩ : syracuseStep 3382397 = 1268399) (by norm_num)
theorem B2254931 : Blo 2253435 2254931 := bstep (se 1 (by rfl) ⟨1691198, by rfl⟩ : syracuseStep 2254931 = 3382397) B3382397
theorem B5073605 : Blo 2253435 5073605 := bbase (se 4 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 5073605 = 951301) (by norm_num)
theorem B3382403 : Blo 2253435 3382403 := bstep (se 1 (by rfl) ⟨2536802, by rfl⟩ : syracuseStep 3382403 = 5073605) B5073605
theorem B2254935 : Blo 2253435 2254935 := bstep (se 1 (by rfl) ⟨1691201, by rfl⟩ : syracuseStep 2254935 = 3382403) B3382403
theorem B3089189 : Blo 2253435 3089189 := bbase (se 4 (by rfl) ⟨289611, by rfl⟩ : syracuseStep 3089189 = 579223) (by norm_num)
theorem B8237837 : Blo 2253435 8237837 := bstep (se 3 (by rfl) ⟨1544594, by rfl⟩ : syracuseStep 8237837 = 3089189) B3089189
theorem B5491891 : Blo 2253435 5491891 := bstep (se 1 (by rfl) ⟨4118918, by rfl⟩ : syracuseStep 5491891 = 8237837) B8237837
theorem B7322521 : Blo 2253435 7322521 := bstep (se 2 (by rfl) ⟨2745945, by rfl⟩ : syracuseStep 7322521 = 5491891) B5491891
theorem B9763361 : Blo 2253435 9763361 := bstep (se 2 (by rfl) ⟨3661260, by rfl⟩ : syracuseStep 9763361 = 7322521) B7322521
theorem B6508907 : Blo 2253435 6508907 := bstep (se 1 (by rfl) ⟨4881680, by rfl⟩ : syracuseStep 6508907 = 9763361) B9763361
theorem B4339271 : Blo 2253435 4339271 := bstep (se 1 (by rfl) ⟨3254453, by rfl⟩ : syracuseStep 4339271 = 6508907) B6508907
theorem B2892847 : Blo 2253435 2892847 := bstep (se 1 (by rfl) ⟨2169635, by rfl⟩ : syracuseStep 2892847 = 4339271) B4339271
theorem B3857129 : Blo 2253435 3857129 := bstep (se 2 (by rfl) ⟨1446423, by rfl⟩ : syracuseStep 3857129 = 2892847) B2892847
theorem B2571419 : Blo 2253435 2571419 := bstep (se 1 (by rfl) ⟨1928564, by rfl⟩ : syracuseStep 2571419 = 3857129) B3857129
theorem B6857117 : Blo 2253435 6857117 := bstep (se 3 (by rfl) ⟨1285709, by rfl⟩ : syracuseStep 6857117 = 2571419) B2571419
theorem B4571411 : Blo 2253435 4571411 := bstep (se 1 (by rfl) ⟨3428558, by rfl⟩ : syracuseStep 4571411 = 6857117) B6857117
theorem B12190429 : Blo 2253435 12190429 := bstep (se 3 (by rfl) ⟨2285705, by rfl⟩ : syracuseStep 12190429 = 4571411) B4571411
theorem B16253905 : Blo 2253435 16253905 := bstep (se 2 (by rfl) ⟨6095214, by rfl⟩ : syracuseStep 16253905 = 12190429) B12190429
theorem B21671873 : Blo 2253435 21671873 := bstep (se 2 (by rfl) ⟨8126952, by rfl⟩ : syracuseStep 21671873 = 16253905) B16253905
theorem B14447915 : Blo 2253435 14447915 := bstep (se 1 (by rfl) ⟨10835936, by rfl⟩ : syracuseStep 14447915 = 21671873) B21671873
theorem B9631943 : Blo 2253435 9631943 := bstep (se 1 (by rfl) ⟨7223957, by rfl⟩ : syracuseStep 9631943 = 14447915) B14447915
theorem B6421295 : Blo 2253435 6421295 := bstep (se 1 (by rfl) ⟨4815971, by rfl⟩ : syracuseStep 6421295 = 9631943) B9631943
theorem B4280863 : Blo 2253435 4280863 := bstep (se 1 (by rfl) ⟨3210647, by rfl⟩ : syracuseStep 4280863 = 6421295) B6421295
theorem B5707817 : Blo 2253435 5707817 := bstep (se 2 (by rfl) ⟨2140431, by rfl⟩ : syracuseStep 5707817 = 4280863) B4280863
theorem B3805211 : Blo 2253435 3805211 := bstep (se 1 (by rfl) ⟨2853908, by rfl⟩ : syracuseStep 3805211 = 5707817) B5707817
theorem B2536807 : Blo 2253435 2536807 := bstep (se 1 (by rfl) ⟨1902605, by rfl⟩ : syracuseStep 2536807 = 3805211) B3805211
theorem B3382409 : Blo 2253435 3382409 := bstep (se 2 (by rfl) ⟨1268403, by rfl⟩ : syracuseStep 3382409 = 2536807) B2536807
theorem B2254939 : Blo 2253435 2254939 := bstep (se 1 (by rfl) ⟨1691204, by rfl⟩ : syracuseStep 2254939 = 3382409) B3382409
theorem B11415653 : Blo 2253435 11415653 := bbase (se 4 (by rfl) ⟨1070217, by rfl⟩ : syracuseStep 11415653 = 2140435) (by norm_num)
theorem B7610435 : Blo 2253435 7610435 := bstep (se 1 (by rfl) ⟨5707826, by rfl⟩ : syracuseStep 7610435 = 11415653) B11415653
theorem B5073623 : Blo 2253435 5073623 := bstep (se 1 (by rfl) ⟨3805217, by rfl⟩ : syracuseStep 5073623 = 7610435) B7610435
theorem B3382415 : Blo 2253435 3382415 := bstep (se 1 (by rfl) ⟨2536811, by rfl⟩ : syracuseStep 3382415 = 5073623) B5073623
theorem B2254943 : Blo 2253435 2254943 := bstep (se 1 (by rfl) ⟨1691207, by rfl⟩ : syracuseStep 2254943 = 3382415) B3382415
theorem B3382421 : Blo 2253435 3382421 := bbase (se 6 (by rfl) ⟨79275, by rfl⟩ : syracuseStep 3382421 = 158551) (by norm_num)
theorem B2254947 : Blo 2253435 2254947 := bstep (se 1 (by rfl) ⟨1691210, by rfl⟩ : syracuseStep 2254947 = 3382421) B3382421
theorem B3857149 : Blo 2253435 3857149 := bbase (se 3 (by rfl) ⟨723215, by rfl⟩ : syracuseStep 3857149 = 1446431) (by norm_num)
theorem B5142865 : Blo 2253435 5142865 := bstep (se 2 (by rfl) ⟨1928574, by rfl⟩ : syracuseStep 5142865 = 3857149) B3857149
theorem B6857153 : Blo 2253435 6857153 := bstep (se 2 (by rfl) ⟨2571432, by rfl⟩ : syracuseStep 6857153 = 5142865) B5142865
theorem B4571435 : Blo 2253435 4571435 := bstep (se 1 (by rfl) ⟨3428576, by rfl⟩ : syracuseStep 4571435 = 6857153) B6857153
theorem B12190493 : Blo 2253435 12190493 := bstep (se 3 (by rfl) ⟨2285717, by rfl⟩ : syracuseStep 12190493 = 4571435) B4571435
theorem B8126995 : Blo 2253435 8126995 := bstep (se 1 (by rfl) ⟨6095246, by rfl⟩ : syracuseStep 8126995 = 12190493) B12190493
theorem B10835993 : Blo 2253435 10835993 := bstep (se 2 (by rfl) ⟨4063497, by rfl⟩ : syracuseStep 10835993 = 8126995) B8126995
theorem B7223995 : Blo 2253435 7223995 := bstep (se 1 (by rfl) ⟨5417996, by rfl⟩ : syracuseStep 7223995 = 10835993) B10835993
theorem B9631993 : Blo 2253435 9631993 := bstep (se 2 (by rfl) ⟨3611997, by rfl⟩ : syracuseStep 9631993 = 7223995) B7223995
theorem B12842657 : Blo 2253435 12842657 := bstep (se 2 (by rfl) ⟨4815996, by rfl⟩ : syracuseStep 12842657 = 9631993) B9631993
theorem B8561771 : Blo 2253435 8561771 := bstep (se 1 (by rfl) ⟨6421328, by rfl⟩ : syracuseStep 8561771 = 12842657) B12842657
theorem B5707847 : Blo 2253435 5707847 := bstep (se 1 (by rfl) ⟨4280885, by rfl⟩ : syracuseStep 5707847 = 8561771) B8561771
theorem B3805231 : Blo 2253435 3805231 := bstep (se 1 (by rfl) ⟨2853923, by rfl⟩ : syracuseStep 3805231 = 5707847) B5707847
theorem B5073641 : Blo 2253435 5073641 := bstep (se 2 (by rfl) ⟨1902615, by rfl⟩ : syracuseStep 5073641 = 3805231) B3805231
theorem B3382427 : Blo 2253435 3382427 := bstep (se 1 (by rfl) ⟨2536820, by rfl⟩ : syracuseStep 3382427 = 5073641) B5073641
theorem B2254951 : Blo 2253435 2254951 := bstep (se 1 (by rfl) ⟨1691213, by rfl⟩ : syracuseStep 2254951 = 3382427) B3382427
theorem B2536825 : Blo 2253435 2536825 := bbase (se 2 (by rfl) ⟨951309, by rfl⟩ : syracuseStep 2536825 = 1902619) (by norm_num)
theorem B3382433 : Blo 2253435 3382433 := bstep (se 2 (by rfl) ⟨1268412, by rfl⟩ : syracuseStep 3382433 = 2536825) B2536825
theorem B2254955 : Blo 2253435 2254955 := bstep (se 1 (by rfl) ⟨1691216, by rfl⟩ : syracuseStep 2254955 = 3382433) B3382433
theorem B7322581 : Blo 2253435 7322581 := bbase (se 7 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 7322581 = 171623) (by norm_num)
theorem B39053765 : Blo 2253435 39053765 := bstep (se 4 (by rfl) ⟨3661290, by rfl⟩ : syracuseStep 39053765 = 7322581) B7322581
theorem B26035843 : Blo 2253435 26035843 := bstep (se 1 (by rfl) ⟨19526882, by rfl⟩ : syracuseStep 26035843 = 39053765) B39053765
theorem B34714457 : Blo 2253435 34714457 := bstep (se 2 (by rfl) ⟨13017921, by rfl⟩ : syracuseStep 34714457 = 26035843) B26035843
theorem B23142971 : Blo 2253435 23142971 := bstep (se 1 (by rfl) ⟨17357228, by rfl⟩ : syracuseStep 23142971 = 34714457) B34714457
theorem B15428647 : Blo 2253435 15428647 := bstep (se 1 (by rfl) ⟨11571485, by rfl⟩ : syracuseStep 15428647 = 23142971) B23142971
theorem B82286117 : Blo 2253435 82286117 := bstep (se 4 (by rfl) ⟨7714323, by rfl⟩ : syracuseStep 82286117 = 15428647) B15428647
theorem B54857411 : Blo 2253435 54857411 := bstep (se 1 (by rfl) ⟨41143058, by rfl⟩ : syracuseStep 54857411 = 82286117) B82286117
theorem B36571607 : Blo 2253435 36571607 := bstep (se 1 (by rfl) ⟨27428705, by rfl⟩ : syracuseStep 36571607 = 54857411) B54857411
theorem B24381071 : Blo 2253435 24381071 := bstep (se 1 (by rfl) ⟨18285803, by rfl⟩ : syracuseStep 24381071 = 36571607) B36571607
theorem B16254047 : Blo 2253435 16254047 := bstep (se 1 (by rfl) ⟨12190535, by rfl⟩ : syracuseStep 16254047 = 24381071) B24381071
theorem B10836031 : Blo 2253435 10836031 := bstep (se 1 (by rfl) ⟨8127023, by rfl⟩ : syracuseStep 10836031 = 16254047) B16254047
theorem B14448041 : Blo 2253435 14448041 := bstep (se 2 (by rfl) ⟨5418015, by rfl⟩ : syracuseStep 14448041 = 10836031) B10836031
theorem B9632027 : Blo 2253435 9632027 := bstep (se 1 (by rfl) ⟨7224020, by rfl⟩ : syracuseStep 9632027 = 14448041) B14448041
theorem B6421351 : Blo 2253435 6421351 := bstep (se 1 (by rfl) ⟨4816013, by rfl⟩ : syracuseStep 6421351 = 9632027) B9632027
theorem B8561801 : Blo 2253435 8561801 := bstep (se 2 (by rfl) ⟨3210675, by rfl⟩ : syracuseStep 8561801 = 6421351) B6421351
theorem B5707867 : Blo 2253435 5707867 := bstep (se 1 (by rfl) ⟨4280900, by rfl⟩ : syracuseStep 5707867 = 8561801) B8561801
theorem B7610489 : Blo 2253435 7610489 := bstep (se 2 (by rfl) ⟨2853933, by rfl⟩ : syracuseStep 7610489 = 5707867) B5707867
theorem B5073659 : Blo 2253435 5073659 := bstep (se 1 (by rfl) ⟨3805244, by rfl⟩ : syracuseStep 5073659 = 7610489) B7610489
theorem B3382439 : Blo 2253435 3382439 := bstep (se 1 (by rfl) ⟨2536829, by rfl⟩ : syracuseStep 3382439 = 5073659) B5073659
theorem B2254959 : Blo 2253435 2254959 := bstep (se 1 (by rfl) ⟨1691219, by rfl⟩ : syracuseStep 2254959 = 3382439) B3382439
theorem B3382445 : Blo 2253435 3382445 := bbase (se 3 (by rfl) ⟨634208, by rfl⟩ : syracuseStep 3382445 = 1268417) (by norm_num)
theorem B2254963 : Blo 2253435 2254963 := bstep (se 1 (by rfl) ⟨1691222, by rfl⟩ : syracuseStep 2254963 = 3382445) B3382445
theorem B5073677 : Blo 2253435 5073677 := bbase (se 3 (by rfl) ⟨951314, by rfl⟩ : syracuseStep 5073677 = 1902629) (by norm_num)
theorem B3382451 : Blo 2253435 3382451 := bstep (se 1 (by rfl) ⟨2536838, by rfl⟩ : syracuseStep 3382451 = 5073677) B5073677
theorem B2254967 : Blo 2253435 2254967 := bstep (se 1 (by rfl) ⟨1691225, by rfl⟩ : syracuseStep 2254967 = 3382451) B3382451
theorem B2853949 : Blo 2253435 2853949 := bbase (se 3 (by rfl) ⟨535115, by rfl⟩ : syracuseStep 2853949 = 1070231) (by norm_num)
theorem B3805265 : Blo 2253435 3805265 := bstep (se 2 (by rfl) ⟨1426974, by rfl⟩ : syracuseStep 3805265 = 2853949) B2853949
theorem B2536843 : Blo 2253435 2536843 := bstep (se 1 (by rfl) ⟨1902632, by rfl⟩ : syracuseStep 2536843 = 3805265) B3805265
theorem B3382457 : Blo 2253435 3382457 := bstep (se 2 (by rfl) ⟨1268421, by rfl⟩ : syracuseStep 3382457 = 2536843) B2536843
theorem B2254971 : Blo 2253435 2254971 := bstep (se 1 (by rfl) ⟨1691228, by rfl⟩ : syracuseStep 2254971 = 3382457) B3382457
theorem B8678677 : Blo 2253435 8678677 := bbase (se 6 (by rfl) ⟨203406, by rfl⟩ : syracuseStep 8678677 = 406813) (by norm_num)
theorem B11571569 : Blo 2253435 11571569 := bstep (se 2 (by rfl) ⟨4339338, by rfl⟩ : syracuseStep 11571569 = 8678677) B8678677
theorem B7714379 : Blo 2253435 7714379 := bstep (se 1 (by rfl) ⟨5785784, by rfl⟩ : syracuseStep 7714379 = 11571569) B11571569
theorem B5142919 : Blo 2253435 5142919 := bstep (se 1 (by rfl) ⟨3857189, by rfl⟩ : syracuseStep 5142919 = 7714379) B7714379
theorem B6857225 : Blo 2253435 6857225 := bstep (se 2 (by rfl) ⟨2571459, by rfl⟩ : syracuseStep 6857225 = 5142919) B5142919
theorem B4571483 : Blo 2253435 4571483 := bstep (se 1 (by rfl) ⟨3428612, by rfl⟩ : syracuseStep 4571483 = 6857225) B6857225
theorem B12190621 : Blo 2253435 12190621 := bstep (se 3 (by rfl) ⟨2285741, by rfl⟩ : syracuseStep 12190621 = 4571483) B4571483
theorem B16254161 : Blo 2253435 16254161 := bstep (se 2 (by rfl) ⟨6095310, by rfl⟩ : syracuseStep 16254161 = 12190621) B12190621
theorem B10836107 : Blo 2253435 10836107 := bstep (se 1 (by rfl) ⟨8127080, by rfl⟩ : syracuseStep 10836107 = 16254161) B16254161
theorem B7224071 : Blo 2253435 7224071 := bstep (se 1 (by rfl) ⟨5418053, by rfl⟩ : syracuseStep 7224071 = 10836107) B10836107
theorem B19264189 : Blo 2253435 19264189 := bstep (se 3 (by rfl) ⟨3612035, by rfl⟩ : syracuseStep 19264189 = 7224071) B7224071
theorem B25685585 : Blo 2253435 25685585 := bstep (se 2 (by rfl) ⟨9632094, by rfl⟩ : syracuseStep 25685585 = 19264189) B19264189
theorem B17123723 : Blo 2253435 17123723 := bstep (se 1 (by rfl) ⟨12842792, by rfl⟩ : syracuseStep 17123723 = 25685585) B25685585
theorem B11415815 : Blo 2253435 11415815 := bstep (se 1 (by rfl) ⟨8561861, by rfl⟩ : syracuseStep 11415815 = 17123723) B17123723
theorem B7610543 : Blo 2253435 7610543 := bstep (se 1 (by rfl) ⟨5707907, by rfl⟩ : syracuseStep 7610543 = 11415815) B11415815
theorem B5073695 : Blo 2253435 5073695 := bstep (se 1 (by rfl) ⟨3805271, by rfl⟩ : syracuseStep 5073695 = 7610543) B7610543
theorem B3382463 : Blo 2253435 3382463 := bstep (se 1 (by rfl) ⟨2536847, by rfl⟩ : syracuseStep 3382463 = 5073695) B5073695
theorem B2254975 : Blo 2253435 2254975 := bstep (se 1 (by rfl) ⟨1691231, by rfl⟩ : syracuseStep 2254975 = 3382463) B3382463
theorem B3382469 : Blo 2253435 3382469 := bbase (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) (by norm_num)
theorem B2254979 : Blo 2253435 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B3805285 : Blo 2253435 3805285 := bbase (se 4 (by rfl) ⟨356745, by rfl⟩ : syracuseStep 3805285 = 713491) (by norm_num)
theorem B5073713 : Blo 2253435 5073713 := bstep (se 2 (by rfl) ⟨1902642, by rfl⟩ : syracuseStep 5073713 = 3805285) B3805285
theorem B3382475 : Blo 2253435 3382475 := bstep (se 1 (by rfl) ⟨2536856, by rfl⟩ : syracuseStep 3382475 = 5073713) B5073713
theorem B2254983 : Blo 2253435 2254983 := bstep (se 1 (by rfl) ⟨1691237, by rfl⟩ : syracuseStep 2254983 = 3382475) B3382475
theorem B2536861 : Blo 2253435 2536861 := bbase (se 3 (by rfl) ⟨475661, by rfl⟩ : syracuseStep 2536861 = 951323) (by norm_num)
theorem B3382481 : Blo 2253435 3382481 := bstep (se 2 (by rfl) ⟨1268430, by rfl⟩ : syracuseStep 3382481 = 2536861) B2536861
theorem B2254987 : Blo 2253435 2254987 := bstep (se 1 (by rfl) ⟨1691240, by rfl⟩ : syracuseStep 2254987 = 3382481) B3382481
theorem B7610597 : Blo 2253435 7610597 := bbase (se 4 (by rfl) ⟨713493, by rfl⟩ : syracuseStep 7610597 = 1426987) (by norm_num)
theorem B5073731 : Blo 2253435 5073731 := bstep (se 1 (by rfl) ⟨3805298, by rfl⟩ : syracuseStep 5073731 = 7610597) B7610597
theorem B3382487 : Blo 2253435 3382487 := bstep (se 1 (by rfl) ⟨2536865, by rfl⟩ : syracuseStep 3382487 = 5073731) B5073731
theorem B2254991 : Blo 2253435 2254991 := bstep (se 1 (by rfl) ⟨1691243, by rfl⟩ : syracuseStep 2254991 = 3382487) B3382487
theorem B3382493 : Blo 2253435 3382493 := bbase (se 3 (by rfl) ⟨634217, by rfl⟩ : syracuseStep 3382493 = 1268435) (by norm_num)
theorem B2254995 : Blo 2253435 2254995 := bstep (se 1 (by rfl) ⟨1691246, by rfl⟩ : syracuseStep 2254995 = 3382493) B3382493
theorem B5073749 : Blo 2253435 5073749 := bbase (se 9 (by rfl) ⟨14864, by rfl⟩ : syracuseStep 5073749 = 29729) (by norm_num)
theorem B3382499 : Blo 2253435 3382499 := bstep (se 1 (by rfl) ⟨2536874, by rfl⟩ : syracuseStep 3382499 = 5073749) B5073749
theorem B2254999 : Blo 2253435 2254999 := bstep (se 1 (by rfl) ⟨1691249, by rfl⟩ : syracuseStep 2254999 = 3382499) B3382499
theorem B6421477 : Blo 2253435 6421477 := bbase (se 4 (by rfl) ⟨602013, by rfl⟩ : syracuseStep 6421477 = 1204027) (by norm_num)
theorem B8561969 : Blo 2253435 8561969 := bstep (se 2 (by rfl) ⟨3210738, by rfl⟩ : syracuseStep 8561969 = 6421477) B6421477
theorem B5707979 : Blo 2253435 5707979 := bstep (se 1 (by rfl) ⟨4280984, by rfl⟩ : syracuseStep 5707979 = 8561969) B8561969
theorem B3805319 : Blo 2253435 3805319 := bstep (se 1 (by rfl) ⟨2853989, by rfl⟩ : syracuseStep 3805319 = 5707979) B5707979
theorem B2536879 : Blo 2253435 2536879 := bstep (se 1 (by rfl) ⟨1902659, by rfl⟩ : syracuseStep 2536879 = 3805319) B3805319
theorem B3382505 : Blo 2253435 3382505 := bstep (se 2 (by rfl) ⟨1268439, by rfl⟩ : syracuseStep 3382505 = 2536879) B2536879
theorem B2255003 : Blo 2253435 2255003 := bstep (se 1 (by rfl) ⟨1691252, by rfl⟩ : syracuseStep 2255003 = 3382505) B3382505
theorem B5492053 : Blo 2253435 5492053 := bbase (se 11 (by rfl) ⟨4022, by rfl⟩ : syracuseStep 5492053 = 8045) (by norm_num)
theorem B7322737 : Blo 2253435 7322737 := bstep (se 2 (by rfl) ⟨2746026, by rfl⟩ : syracuseStep 7322737 = 5492053) B5492053
theorem B9763649 : Blo 2253435 9763649 := bstep (se 2 (by rfl) ⟨3661368, by rfl⟩ : syracuseStep 9763649 = 7322737) B7322737
theorem B6509099 : Blo 2253435 6509099 := bstep (se 1 (by rfl) ⟨4881824, by rfl⟩ : syracuseStep 6509099 = 9763649) B9763649
theorem B17357597 : Blo 2253435 17357597 := bstep (se 3 (by rfl) ⟨3254549, by rfl⟩ : syracuseStep 17357597 = 6509099) B6509099
theorem B11571731 : Blo 2253435 11571731 := bstep (se 1 (by rfl) ⟨8678798, by rfl⟩ : syracuseStep 11571731 = 17357597) B17357597
theorem B7714487 : Blo 2253435 7714487 := bstep (se 1 (by rfl) ⟨5785865, by rfl⟩ : syracuseStep 7714487 = 11571731) B11571731
theorem B20571965 : Blo 2253435 20571965 := bstep (se 3 (by rfl) ⟨3857243, by rfl⟩ : syracuseStep 20571965 = 7714487) B7714487
theorem B13714643 : Blo 2253435 13714643 := bstep (se 1 (by rfl) ⟨10285982, by rfl⟩ : syracuseStep 13714643 = 20571965) B20571965
theorem B36572381 : Blo 2253435 36572381 := bstep (se 3 (by rfl) ⟨6857321, by rfl⟩ : syracuseStep 36572381 = 13714643) B13714643
theorem B24381587 : Blo 2253435 24381587 := bstep (se 1 (by rfl) ⟨18286190, by rfl⟩ : syracuseStep 24381587 = 36572381) B36572381
theorem B65017565 : Blo 2253435 65017565 := bstep (se 3 (by rfl) ⟨12190793, by rfl⟩ : syracuseStep 65017565 = 24381587) B24381587
theorem B43345043 : Blo 2253435 43345043 := bstep (se 1 (by rfl) ⟨32508782, by rfl⟩ : syracuseStep 43345043 = 65017565) B65017565
theorem B28896695 : Blo 2253435 28896695 := bstep (se 1 (by rfl) ⟨21672521, by rfl⟩ : syracuseStep 28896695 = 43345043) B43345043
theorem B19264463 : Blo 2253435 19264463 := bstep (se 1 (by rfl) ⟨14448347, by rfl⟩ : syracuseStep 19264463 = 28896695) B28896695
theorem B12842975 : Blo 2253435 12842975 := bstep (se 1 (by rfl) ⟨9632231, by rfl⟩ : syracuseStep 12842975 = 19264463) B19264463
theorem B8561983 : Blo 2253435 8561983 := bstep (se 1 (by rfl) ⟨6421487, by rfl⟩ : syracuseStep 8561983 = 12842975) B12842975
theorem B11415977 : Blo 2253435 11415977 := bstep (se 2 (by rfl) ⟨4280991, by rfl⟩ : syracuseStep 11415977 = 8561983) B8561983
theorem B7610651 : Blo 2253435 7610651 := bstep (se 1 (by rfl) ⟨5707988, by rfl⟩ : syracuseStep 7610651 = 11415977) B11415977
theorem B5073767 : Blo 2253435 5073767 := bstep (se 1 (by rfl) ⟨3805325, by rfl⟩ : syracuseStep 5073767 = 7610651) B7610651
theorem B3382511 : Blo 2253435 3382511 := bstep (se 1 (by rfl) ⟨2536883, by rfl⟩ : syracuseStep 3382511 = 5073767) B5073767
theorem B2255007 : Blo 2253435 2255007 := bstep (se 1 (by rfl) ⟨1691255, by rfl⟩ : syracuseStep 2255007 = 3382511) B3382511
theorem B3382517 : Blo 2253435 3382517 := bbase (se 5 (by rfl) ⟨158555, by rfl⟩ : syracuseStep 3382517 = 317111) (by norm_num)
theorem B2255011 : Blo 2253435 2255011 := bstep (se 1 (by rfl) ⟨1691258, by rfl⟩ : syracuseStep 2255011 = 3382517) B3382517
theorem B4063613 : Blo 2253435 4063613 := bbase (se 3 (by rfl) ⟨761927, by rfl⟩ : syracuseStep 4063613 = 1523855) (by norm_num)
theorem B10836301 : Blo 2253435 10836301 := bstep (se 3 (by rfl) ⟨2031806, by rfl⟩ : syracuseStep 10836301 = 4063613) B4063613
theorem B14448401 : Blo 2253435 14448401 := bstep (se 2 (by rfl) ⟨5418150, by rfl⟩ : syracuseStep 14448401 = 10836301) B10836301
theorem B9632267 : Blo 2253435 9632267 := bstep (se 1 (by rfl) ⟨7224200, by rfl⟩ : syracuseStep 9632267 = 14448401) B14448401
theorem B6421511 : Blo 2253435 6421511 := bstep (se 1 (by rfl) ⟨4816133, by rfl⟩ : syracuseStep 6421511 = 9632267) B9632267
theorem B4281007 : Blo 2253435 4281007 := bstep (se 1 (by rfl) ⟨3210755, by rfl⟩ : syracuseStep 4281007 = 6421511) B6421511
theorem B5708009 : Blo 2253435 5708009 := bstep (se 2 (by rfl) ⟨2140503, by rfl⟩ : syracuseStep 5708009 = 4281007) B4281007
theorem B3805339 : Blo 2253435 3805339 := bstep (se 1 (by rfl) ⟨2854004, by rfl⟩ : syracuseStep 3805339 = 5708009) B5708009
theorem B5073785 : Blo 2253435 5073785 := bstep (se 2 (by rfl) ⟨1902669, by rfl⟩ : syracuseStep 5073785 = 3805339) B3805339
theorem B3382523 : Blo 2253435 3382523 := bstep (se 1 (by rfl) ⟨2536892, by rfl⟩ : syracuseStep 3382523 = 5073785) B5073785
theorem B2255015 : Blo 2253435 2255015 := bstep (se 1 (by rfl) ⟨1691261, by rfl⟩ : syracuseStep 2255015 = 3382523) B3382523
theorem B2536897 : Blo 2253435 2536897 := bbase (se 2 (by rfl) ⟨951336, by rfl⟩ : syracuseStep 2536897 = 1902673) (by norm_num)
theorem B3382529 : Blo 2253435 3382529 := bstep (se 2 (by rfl) ⟨1268448, by rfl⟩ : syracuseStep 3382529 = 2536897) B2536897
theorem B2255019 : Blo 2253435 2255019 := bstep (se 1 (by rfl) ⟨1691264, by rfl⟩ : syracuseStep 2255019 = 3382529) B3382529
theorem B5708029 : Blo 2253435 5708029 := bbase (se 3 (by rfl) ⟨1070255, by rfl⟩ : syracuseStep 5708029 = 2140511) (by norm_num)
theorem B7610705 : Blo 2253435 7610705 := bstep (se 2 (by rfl) ⟨2854014, by rfl⟩ : syracuseStep 7610705 = 5708029) B5708029
theorem B5073803 : Blo 2253435 5073803 := bstep (se 1 (by rfl) ⟨3805352, by rfl⟩ : syracuseStep 5073803 = 7610705) B7610705
theorem B3382535 : Blo 2253435 3382535 := bstep (se 1 (by rfl) ⟨2536901, by rfl⟩ : syracuseStep 3382535 = 5073803) B5073803
theorem B2255023 : Blo 2253435 2255023 := bstep (se 1 (by rfl) ⟨1691267, by rfl⟩ : syracuseStep 2255023 = 3382535) B3382535
theorem B3382541 : Blo 2253435 3382541 := bbase (se 3 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 3382541 = 1268453) (by norm_num)
theorem B2255027 : Blo 2253435 2255027 := bstep (se 1 (by rfl) ⟨1691270, by rfl⟩ : syracuseStep 2255027 = 3382541) B3382541
theorem B5073821 : Blo 2253435 5073821 := bbase (se 3 (by rfl) ⟨951341, by rfl⟩ : syracuseStep 5073821 = 1902683) (by norm_num)
theorem B3382547 : Blo 2253435 3382547 := bstep (se 1 (by rfl) ⟨2536910, by rfl⟩ : syracuseStep 3382547 = 5073821) B5073821
theorem B2255031 : Blo 2253435 2255031 := bstep (se 1 (by rfl) ⟨1691273, by rfl⟩ : syracuseStep 2255031 = 3382547) B3382547
theorem B3805373 : Blo 2253435 3805373 := bbase (se 3 (by rfl) ⟨713507, by rfl⟩ : syracuseStep 3805373 = 1427015) (by norm_num)
theorem B2536915 : Blo 2253435 2536915 := bstep (se 1 (by rfl) ⟨1902686, by rfl⟩ : syracuseStep 2536915 = 3805373) B3805373
theorem B3382553 : Blo 2253435 3382553 := bstep (se 2 (by rfl) ⟨1268457, by rfl⟩ : syracuseStep 3382553 = 2536915) B2536915
theorem B2255035 : Blo 2253435 2255035 := bstep (se 1 (by rfl) ⟨1691276, by rfl⟩ : syracuseStep 2255035 = 3382553) B3382553
theorem B12843157 : Blo 2253435 12843157 := bbase (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) (by norm_num)
theorem B17124209 : Blo 2253435 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B11416139 : Blo 2253435 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B7610759 : Blo 2253435 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B5073839 : Blo 2253435 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B3382559 : Blo 2253435 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B2255039 : Blo 2253435 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B3382565 : Blo 2253435 3382565 := bbase (se 4 (by rfl) ⟨317115, by rfl⟩ : syracuseStep 3382565 = 634231) (by norm_num)
theorem B2255043 : Blo 2253435 2255043 := bstep (se 1 (by rfl) ⟨1691282, by rfl⟩ : syracuseStep 2255043 = 3382565) B3382565
theorem B2854045 : Blo 2253435 2854045 := bbase (se 3 (by rfl) ⟨535133, by rfl⟩ : syracuseStep 2854045 = 1070267) (by norm_num)
theorem B3805393 : Blo 2253435 3805393 := bstep (se 2 (by rfl) ⟨1427022, by rfl⟩ : syracuseStep 3805393 = 2854045) B2854045
theorem B5073857 : Blo 2253435 5073857 := bstep (se 2 (by rfl) ⟨1902696, by rfl⟩ : syracuseStep 5073857 = 3805393) B3805393
theorem B3382571 : Blo 2253435 3382571 := bstep (se 1 (by rfl) ⟨2536928, by rfl⟩ : syracuseStep 3382571 = 5073857) B5073857
theorem B2255047 : Blo 2253435 2255047 := bstep (se 1 (by rfl) ⟨1691285, by rfl⟩ : syracuseStep 2255047 = 3382571) B3382571
theorem B2536933 : Blo 2253435 2536933 := bbase (se 4 (by rfl) ⟨237837, by rfl⟩ : syracuseStep 2536933 = 475675) (by norm_num)
theorem B3382577 : Blo 2253435 3382577 := bstep (se 2 (by rfl) ⟨1268466, by rfl⟩ : syracuseStep 3382577 = 2536933) B2536933
theorem B2255051 : Blo 2253435 2255051 := bstep (se 1 (by rfl) ⟨1691288, by rfl⟩ : syracuseStep 2255051 = 3382577) B3382577
theorem B39055445 : Blo 2253435 39055445 := bbase (se 8 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 39055445 = 457681) (by norm_num)
theorem B26036963 : Blo 2253435 26036963 := bstep (se 1 (by rfl) ⟨19527722, by rfl⟩ : syracuseStep 26036963 = 39055445) B39055445
theorem B17357975 : Blo 2253435 17357975 := bstep (se 1 (by rfl) ⟨13018481, by rfl⟩ : syracuseStep 17357975 = 26036963) B26036963
theorem B11571983 : Blo 2253435 11571983 := bstep (se 1 (by rfl) ⟨8678987, by rfl⟩ : syracuseStep 11571983 = 17357975) B17357975
theorem B7714655 : Blo 2253435 7714655 := bstep (se 1 (by rfl) ⟨5785991, by rfl⟩ : syracuseStep 7714655 = 11571983) B11571983
theorem B5143103 : Blo 2253435 5143103 := bstep (se 1 (by rfl) ⟨3857327, by rfl⟩ : syracuseStep 5143103 = 7714655) B7714655
theorem B3428735 : Blo 2253435 3428735 := bstep (se 1 (by rfl) ⟨2571551, by rfl⟩ : syracuseStep 3428735 = 5143103) B5143103
theorem B9143293 : Blo 2253435 9143293 := bstep (se 3 (by rfl) ⟨1714367, by rfl⟩ : syracuseStep 9143293 = 3428735) B3428735
theorem B12191057 : Blo 2253435 12191057 := bstep (se 2 (by rfl) ⟨4571646, by rfl⟩ : syracuseStep 12191057 = 9143293) B9143293
theorem B8127371 : Blo 2253435 8127371 := bstep (se 1 (by rfl) ⟨6095528, by rfl⟩ : syracuseStep 8127371 = 12191057) B12191057
theorem B5418247 : Blo 2253435 5418247 := bstep (se 1 (by rfl) ⟨4063685, by rfl⟩ : syracuseStep 5418247 = 8127371) B8127371
theorem B7224329 : Blo 2253435 7224329 := bstep (se 2 (by rfl) ⟨2709123, by rfl⟩ : syracuseStep 7224329 = 5418247) B5418247
theorem B4816219 : Blo 2253435 4816219 := bstep (se 1 (by rfl) ⟨3612164, by rfl⟩ : syracuseStep 4816219 = 7224329) B7224329
theorem B6421625 : Blo 2253435 6421625 := bstep (se 2 (by rfl) ⟨2408109, by rfl⟩ : syracuseStep 6421625 = 4816219) B4816219
theorem B4281083 : Blo 2253435 4281083 := bstep (se 1 (by rfl) ⟨3210812, by rfl⟩ : syracuseStep 4281083 = 6421625) B6421625
theorem B2854055 : Blo 2253435 2854055 := bstep (se 1 (by rfl) ⟨2140541, by rfl⟩ : syracuseStep 2854055 = 4281083) B4281083
theorem B7610813 : Blo 2253435 7610813 := bstep (se 3 (by rfl) ⟨1427027, by rfl⟩ : syracuseStep 7610813 = 2854055) B2854055
theorem B5073875 : Blo 2253435 5073875 := bstep (se 1 (by rfl) ⟨3805406, by rfl⟩ : syracuseStep 5073875 = 7610813) B7610813
theorem B3382583 : Blo 2253435 3382583 := bstep (se 1 (by rfl) ⟨2536937, by rfl⟩ : syracuseStep 3382583 = 5073875) B5073875
theorem B2255055 : Blo 2253435 2255055 := bstep (se 1 (by rfl) ⟨1691291, by rfl⟩ : syracuseStep 2255055 = 3382583) B3382583
theorem B3382589 : Blo 2253435 3382589 := bbase (se 3 (by rfl) ⟨634235, by rfl⟩ : syracuseStep 3382589 = 1268471) (by norm_num)
theorem B2255059 : Blo 2253435 2255059 := bstep (se 1 (by rfl) ⟨1691294, by rfl⟩ : syracuseStep 2255059 = 3382589) B3382589
theorem B5073893 : Blo 2253435 5073893 := bbase (se 4 (by rfl) ⟨475677, by rfl⟩ : syracuseStep 5073893 = 951355) (by norm_num)
theorem B3382595 : Blo 2253435 3382595 := bstep (se 1 (by rfl) ⟨2536946, by rfl⟩ : syracuseStep 3382595 = 5073893) B5073893
theorem B2255063 : Blo 2253435 2255063 := bstep (se 1 (by rfl) ⟨1691297, by rfl⟩ : syracuseStep 2255063 = 3382595) B3382595
theorem B5708141 : Blo 2253435 5708141 := bbase (se 3 (by rfl) ⟨1070276, by rfl⟩ : syracuseStep 5708141 = 2140553) (by norm_num)
theorem B3805427 : Blo 2253435 3805427 := bstep (se 1 (by rfl) ⟨2854070, by rfl⟩ : syracuseStep 3805427 = 5708141) B5708141
theorem B2536951 : Blo 2253435 2536951 := bstep (se 1 (by rfl) ⟨1902713, by rfl⟩ : syracuseStep 2536951 = 3805427) B3805427
theorem B3382601 : Blo 2253435 3382601 := bstep (se 2 (by rfl) ⟨1268475, by rfl⟩ : syracuseStep 3382601 = 2536951) B2536951
theorem B2255067 : Blo 2253435 2255067 := bstep (se 1 (by rfl) ⟨1691300, by rfl⟩ : syracuseStep 2255067 = 3382601) B3382601
theorem B4816253 : Blo 2253435 4816253 := bbase (se 3 (by rfl) ⟨903047, by rfl⟩ : syracuseStep 4816253 = 1806095) (by norm_num)
theorem B3210835 : Blo 2253435 3210835 := bstep (se 1 (by rfl) ⟨2408126, by rfl⟩ : syracuseStep 3210835 = 4816253) B4816253
theorem B4281113 : Blo 2253435 4281113 := bstep (se 2 (by rfl) ⟨1605417, by rfl⟩ : syracuseStep 4281113 = 3210835) B3210835
theorem B11416301 : Blo 2253435 11416301 := bstep (se 3 (by rfl) ⟨2140556, by rfl⟩ : syracuseStep 11416301 = 4281113) B4281113
theorem B7610867 : Blo 2253435 7610867 := bstep (se 1 (by rfl) ⟨5708150, by rfl⟩ : syracuseStep 7610867 = 11416301) B11416301
theorem B5073911 : Blo 2253435 5073911 := bstep (se 1 (by rfl) ⟨3805433, by rfl⟩ : syracuseStep 5073911 = 7610867) B7610867
theorem B3382607 : Blo 2253435 3382607 := bstep (se 1 (by rfl) ⟨2536955, by rfl⟩ : syracuseStep 3382607 = 5073911) B5073911
theorem B2255071 : Blo 2253435 2255071 := bstep (se 1 (by rfl) ⟨1691303, by rfl⟩ : syracuseStep 2255071 = 3382607) B3382607
theorem B3382613 : Blo 2253435 3382613 := bbase (se 11 (by rfl) ⟨2477, by rfl⟩ : syracuseStep 3382613 = 4955) (by norm_num)
theorem B2255075 : Blo 2253435 2255075 := bstep (se 1 (by rfl) ⟨1691306, by rfl⟩ : syracuseStep 2255075 = 3382613) B3382613
theorem B3047797 : Blo 2253435 3047797 := bbase (se 5 (by rfl) ⟨142865, by rfl⟩ : syracuseStep 3047797 = 285731) (by norm_num)
theorem B4063729 : Blo 2253435 4063729 := bstep (se 2 (by rfl) ⟨1523898, by rfl⟩ : syracuseStep 4063729 = 3047797) B3047797
theorem B5418305 : Blo 2253435 5418305 := bstep (se 2 (by rfl) ⟨2031864, by rfl⟩ : syracuseStep 5418305 = 4063729) B4063729
theorem B3612203 : Blo 2253435 3612203 := bstep (se 1 (by rfl) ⟨2709152, by rfl⟩ : syracuseStep 3612203 = 5418305) B5418305
theorem B2408135 : Blo 2253435 2408135 := bstep (se 1 (by rfl) ⟨1806101, by rfl⟩ : syracuseStep 2408135 = 3612203) B3612203
theorem B6421693 : Blo 2253435 6421693 := bstep (se 3 (by rfl) ⟨1204067, by rfl⟩ : syracuseStep 6421693 = 2408135) B2408135
theorem B8562257 : Blo 2253435 8562257 := bstep (se 2 (by rfl) ⟨3210846, by rfl⟩ : syracuseStep 8562257 = 6421693) B6421693
theorem B5708171 : Blo 2253435 5708171 := bstep (se 1 (by rfl) ⟨4281128, by rfl⟩ : syracuseStep 5708171 = 8562257) B8562257
theorem B3805447 : Blo 2253435 3805447 := bstep (se 1 (by rfl) ⟨2854085, by rfl⟩ : syracuseStep 3805447 = 5708171) B5708171
theorem B5073929 : Blo 2253435 5073929 := bstep (se 2 (by rfl) ⟨1902723, by rfl⟩ : syracuseStep 5073929 = 3805447) B3805447
theorem B3382619 : Blo 2253435 3382619 := bstep (se 1 (by rfl) ⟨2536964, by rfl⟩ : syracuseStep 3382619 = 5073929) B5073929
theorem B2255079 : Blo 2253435 2255079 := bstep (se 1 (by rfl) ⟨1691309, by rfl⟩ : syracuseStep 2255079 = 3382619) B3382619
theorem B2536969 : Blo 2253435 2536969 := bbase (se 2 (by rfl) ⟨951363, by rfl⟩ : syracuseStep 2536969 = 1902727) (by norm_num)
theorem B3382625 : Blo 2253435 3382625 := bstep (se 2 (by rfl) ⟨1268484, by rfl⟩ : syracuseStep 3382625 = 2536969) B2536969
theorem B2255083 : Blo 2253435 2255083 := bstep (se 1 (by rfl) ⟨1691312, by rfl⟩ : syracuseStep 2255083 = 3382625) B3382625
theorem B8679109 : Blo 2253435 8679109 := bbase (se 4 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 8679109 = 1627333) (by norm_num)
theorem B11572145 : Blo 2253435 11572145 := bstep (se 2 (by rfl) ⟨4339554, by rfl⟩ : syracuseStep 11572145 = 8679109) B8679109
theorem B7714763 : Blo 2253435 7714763 := bstep (se 1 (by rfl) ⟨5786072, by rfl⟩ : syracuseStep 7714763 = 11572145) B11572145
theorem B5143175 : Blo 2253435 5143175 := bstep (se 1 (by rfl) ⟨3857381, by rfl⟩ : syracuseStep 5143175 = 7714763) B7714763
theorem B3428783 : Blo 2253435 3428783 := bstep (se 1 (by rfl) ⟨2571587, by rfl⟩ : syracuseStep 3428783 = 5143175) B5143175
theorem B2285855 : Blo 2253435 2285855 := bstep (se 1 (by rfl) ⟨1714391, by rfl⟩ : syracuseStep 2285855 = 3428783) B3428783
theorem B24382453 : Blo 2253435 24382453 := bstep (se 5 (by rfl) ⟨1142927, by rfl⟩ : syracuseStep 24382453 = 2285855) B2285855
theorem B32509937 : Blo 2253435 32509937 := bstep (se 2 (by rfl) ⟨12191226, by rfl⟩ : syracuseStep 32509937 = 24382453) B24382453
theorem B21673291 : Blo 2253435 21673291 := bstep (se 1 (by rfl) ⟨16254968, by rfl⟩ : syracuseStep 21673291 = 32509937) B32509937
theorem B28897721 : Blo 2253435 28897721 := bstep (se 2 (by rfl) ⟨10836645, by rfl⟩ : syracuseStep 28897721 = 21673291) B21673291
theorem B19265147 : Blo 2253435 19265147 := bstep (se 1 (by rfl) ⟨14448860, by rfl⟩ : syracuseStep 19265147 = 28897721) B28897721
theorem B12843431 : Blo 2253435 12843431 := bstep (se 1 (by rfl) ⟨9632573, by rfl⟩ : syracuseStep 12843431 = 19265147) B19265147
theorem B8562287 : Blo 2253435 8562287 := bstep (se 1 (by rfl) ⟨6421715, by rfl⟩ : syracuseStep 8562287 = 12843431) B12843431
theorem B5708191 : Blo 2253435 5708191 := bstep (se 1 (by rfl) ⟨4281143, by rfl⟩ : syracuseStep 5708191 = 8562287) B8562287
theorem B7610921 : Blo 2253435 7610921 := bstep (se 2 (by rfl) ⟨2854095, by rfl⟩ : syracuseStep 7610921 = 5708191) B5708191
theorem B5073947 : Blo 2253435 5073947 := bstep (se 1 (by rfl) ⟨3805460, by rfl⟩ : syracuseStep 5073947 = 7610921) B7610921
theorem B3382631 : Blo 2253435 3382631 := bstep (se 1 (by rfl) ⟨2536973, by rfl⟩ : syracuseStep 3382631 = 5073947) B5073947
theorem B2255087 : Blo 2253435 2255087 := bstep (se 1 (by rfl) ⟨1691315, by rfl⟩ : syracuseStep 2255087 = 3382631) B3382631
theorem B3382637 : Blo 2253435 3382637 := bbase (se 3 (by rfl) ⟨634244, by rfl⟩ : syracuseStep 3382637 = 1268489) (by norm_num)
theorem B2255091 : Blo 2253435 2255091 := bstep (se 1 (by rfl) ⟨1691318, by rfl⟩ : syracuseStep 2255091 = 3382637) B3382637
theorem B5073965 : Blo 2253435 5073965 := bbase (se 3 (by rfl) ⟨951368, by rfl⟩ : syracuseStep 5073965 = 1902737) (by norm_num)
theorem B3382643 : Blo 2253435 3382643 := bstep (se 1 (by rfl) ⟨2536982, by rfl⟩ : syracuseStep 3382643 = 5073965) B5073965
theorem B2255095 : Blo 2253435 2255095 := bstep (se 1 (by rfl) ⟨1691321, by rfl⟩ : syracuseStep 2255095 = 3382643) B3382643
theorem B4063765 : Blo 2253435 4063765 := bbase (se 6 (by rfl) ⟨95244, by rfl⟩ : syracuseStep 4063765 = 190489) (by norm_num)
theorem B5418353 : Blo 2253435 5418353 := bstep (se 2 (by rfl) ⟨2031882, by rfl⟩ : syracuseStep 5418353 = 4063765) B4063765
theorem B14448941 : Blo 2253435 14448941 := bstep (se 3 (by rfl) ⟨2709176, by rfl⟩ : syracuseStep 14448941 = 5418353) B5418353
theorem B9632627 : Blo 2253435 9632627 := bstep (se 1 (by rfl) ⟨7224470, by rfl⟩ : syracuseStep 9632627 = 14448941) B14448941
theorem B6421751 : Blo 2253435 6421751 := bstep (se 1 (by rfl) ⟨4816313, by rfl⟩ : syracuseStep 6421751 = 9632627) B9632627
theorem B4281167 : Blo 2253435 4281167 := bstep (se 1 (by rfl) ⟨3210875, by rfl⟩ : syracuseStep 4281167 = 6421751) B6421751
theorem B2854111 : Blo 2253435 2854111 := bstep (se 1 (by rfl) ⟨2140583, by rfl⟩ : syracuseStep 2854111 = 4281167) B4281167
theorem B3805481 : Blo 2253435 3805481 := bstep (se 2 (by rfl) ⟨1427055, by rfl⟩ : syracuseStep 3805481 = 2854111) B2854111
theorem B2536987 : Blo 2253435 2536987 := bstep (se 1 (by rfl) ⟨1902740, by rfl⟩ : syracuseStep 2536987 = 3805481) B3805481
theorem B3382649 : Blo 2253435 3382649 := bstep (se 2 (by rfl) ⟨1268493, by rfl⟩ : syracuseStep 3382649 = 2536987) B2536987
theorem B2255099 : Blo 2253435 2255099 := bstep (se 1 (by rfl) ⟨1691324, by rfl⟩ : syracuseStep 2255099 = 3382649) B3382649
theorem B2441017 : Blo 2253435 2441017 := bbase (se 2 (by rfl) ⟨915381, by rfl⟩ : syracuseStep 2441017 = 1830763) (by norm_num)
theorem B3254689 : Blo 2253435 3254689 := bstep (se 2 (by rfl) ⟨1220508, by rfl⟩ : syracuseStep 3254689 = 2441017) B2441017
theorem B4339585 : Blo 2253435 4339585 := bstep (se 2 (by rfl) ⟨1627344, by rfl⟩ : syracuseStep 4339585 = 3254689) B3254689
theorem B23144453 : Blo 2253435 23144453 := bstep (se 4 (by rfl) ⟨2169792, by rfl⟩ : syracuseStep 23144453 = 4339585) B4339585
theorem B15429635 : Blo 2253435 15429635 := bstep (se 1 (by rfl) ⟨11572226, by rfl⟩ : syracuseStep 15429635 = 23144453) B23144453
theorem B10286423 : Blo 2253435 10286423 := bstep (se 1 (by rfl) ⟨7714817, by rfl⟩ : syracuseStep 10286423 = 15429635) B15429635
theorem B6857615 : Blo 2253435 6857615 := bstep (se 1 (by rfl) ⟨5143211, by rfl⟩ : syracuseStep 6857615 = 10286423) B10286423
theorem B4571743 : Blo 2253435 4571743 := bstep (se 1 (by rfl) ⟨3428807, by rfl⟩ : syracuseStep 4571743 = 6857615) B6857615
theorem B6095657 : Blo 2253435 6095657 := bstep (se 2 (by rfl) ⟨2285871, by rfl⟩ : syracuseStep 6095657 = 4571743) B4571743
theorem B4063771 : Blo 2253435 4063771 := bstep (se 1 (by rfl) ⟨3047828, by rfl⟩ : syracuseStep 4063771 = 6095657) B6095657
theorem B5418361 : Blo 2253435 5418361 := bstep (se 2 (by rfl) ⟨2031885, by rfl⟩ : syracuseStep 5418361 = 4063771) B4063771
theorem B7224481 : Blo 2253435 7224481 := bstep (se 2 (by rfl) ⟨2709180, by rfl⟩ : syracuseStep 7224481 = 5418361) B5418361
theorem B38530565 : Blo 2253435 38530565 := bstep (se 4 (by rfl) ⟨3612240, by rfl⟩ : syracuseStep 38530565 = 7224481) B7224481
theorem B25687043 : Blo 2253435 25687043 := bstep (se 1 (by rfl) ⟨19265282, by rfl⟩ : syracuseStep 25687043 = 38530565) B38530565
theorem B17124695 : Blo 2253435 17124695 := bstep (se 1 (by rfl) ⟨12843521, by rfl⟩ : syracuseStep 17124695 = 25687043) B25687043
theorem B11416463 : Blo 2253435 11416463 := bstep (se 1 (by rfl) ⟨8562347, by rfl⟩ : syracuseStep 11416463 = 17124695) B17124695
theorem B7610975 : Blo 2253435 7610975 := bstep (se 1 (by rfl) ⟨5708231, by rfl⟩ : syracuseStep 7610975 = 11416463) B11416463
theorem B5073983 : Blo 2253435 5073983 := bstep (se 1 (by rfl) ⟨3805487, by rfl⟩ : syracuseStep 5073983 = 7610975) B7610975
theorem B3382655 : Blo 2253435 3382655 := bstep (se 1 (by rfl) ⟨2536991, by rfl⟩ : syracuseStep 3382655 = 5073983) B5073983
theorem B2255103 : Blo 2253435 2255103 := bstep (se 1 (by rfl) ⟨1691327, by rfl⟩ : syracuseStep 2255103 = 3382655) B3382655
theorem B3382661 : Blo 2253435 3382661 := bbase (se 4 (by rfl) ⟨317124, by rfl⟩ : syracuseStep 3382661 = 634249) (by norm_num)
theorem B2255107 : Blo 2253435 2255107 := bstep (se 1 (by rfl) ⟨1691330, by rfl⟩ : syracuseStep 2255107 = 3382661) B3382661
theorem B3805501 : Blo 2253435 3805501 := bbase (se 3 (by rfl) ⟨713531, by rfl⟩ : syracuseStep 3805501 = 1427063) (by norm_num)
theorem B5074001 : Blo 2253435 5074001 := bstep (se 2 (by rfl) ⟨1902750, by rfl⟩ : syracuseStep 5074001 = 3805501) B3805501
theorem B3382667 : Blo 2253435 3382667 := bstep (se 1 (by rfl) ⟨2537000, by rfl⟩ : syracuseStep 3382667 = 5074001) B5074001
theorem B2255111 : Blo 2253435 2255111 := bstep (se 1 (by rfl) ⟨1691333, by rfl⟩ : syracuseStep 2255111 = 3382667) B3382667
theorem B2537005 : Blo 2253435 2537005 := bbase (se 3 (by rfl) ⟨475688, by rfl⟩ : syracuseStep 2537005 = 951377) (by norm_num)
theorem B3382673 : Blo 2253435 3382673 := bstep (se 2 (by rfl) ⟨1268502, by rfl⟩ : syracuseStep 3382673 = 2537005) B2537005
theorem B2255115 : Blo 2253435 2255115 := bstep (se 1 (by rfl) ⟨1691336, by rfl⟩ : syracuseStep 2255115 = 3382673) B3382673
theorem B7611029 : Blo 2253435 7611029 := bbase (se 6 (by rfl) ⟨178383, by rfl⟩ : syracuseStep 7611029 = 356767) (by norm_num)
theorem B5074019 : Blo 2253435 5074019 := bstep (se 1 (by rfl) ⟨3805514, by rfl⟩ : syracuseStep 5074019 = 7611029) B7611029
theorem B3382679 : Blo 2253435 3382679 := bstep (se 1 (by rfl) ⟨2537009, by rfl⟩ : syracuseStep 3382679 = 5074019) B5074019
theorem B2255119 : Blo 2253435 2255119 := bstep (se 1 (by rfl) ⟨1691339, by rfl⟩ : syracuseStep 2255119 = 3382679) B3382679
theorem B3382685 : Blo 2253435 3382685 := bbase (se 3 (by rfl) ⟨634253, by rfl⟩ : syracuseStep 3382685 = 1268507) (by norm_num)
theorem B2255123 : Blo 2253435 2255123 := bstep (se 1 (by rfl) ⟨1691342, by rfl⟩ : syracuseStep 2255123 = 3382685) B3382685
theorem B5074037 : Blo 2253435 5074037 := bbase (se 5 (by rfl) ⟨237845, by rfl⟩ : syracuseStep 5074037 = 475691) (by norm_num)
theorem B3382691 : Blo 2253435 3382691 := bstep (se 1 (by rfl) ⟨2537018, by rfl⟩ : syracuseStep 3382691 = 5074037) B5074037
theorem B2255127 : Blo 2253435 2255127 := bstep (se 1 (by rfl) ⟨1691345, by rfl⟩ : syracuseStep 2255127 = 3382691) B3382691
theorem B19265525 : Blo 2253435 19265525 := bbase (se 5 (by rfl) ⟨903071, by rfl⟩ : syracuseStep 19265525 = 1806143) (by norm_num)
theorem B12843683 : Blo 2253435 12843683 := bstep (se 1 (by rfl) ⟨9632762, by rfl⟩ : syracuseStep 12843683 = 19265525) B19265525
theorem B8562455 : Blo 2253435 8562455 := bstep (se 1 (by rfl) ⟨6421841, by rfl⟩ : syracuseStep 8562455 = 12843683) B12843683
theorem B5708303 : Blo 2253435 5708303 := bstep (se 1 (by rfl) ⟨4281227, by rfl⟩ : syracuseStep 5708303 = 8562455) B8562455
theorem B3805535 : Blo 2253435 3805535 := bstep (se 1 (by rfl) ⟨2854151, by rfl⟩ : syracuseStep 3805535 = 5708303) B5708303
theorem B2537023 : Blo 2253435 2537023 := bstep (se 1 (by rfl) ⟨1902767, by rfl⟩ : syracuseStep 2537023 = 3805535) B3805535
theorem B3382697 : Blo 2253435 3382697 := bstep (se 2 (by rfl) ⟨1268511, by rfl⟩ : syracuseStep 3382697 = 2537023) B2537023
theorem B2255131 : Blo 2253435 2255131 := bstep (se 1 (by rfl) ⟨1691348, by rfl⟩ : syracuseStep 2255131 = 3382697) B3382697
theorem B8562469 : Blo 2253435 8562469 := bbase (se 4 (by rfl) ⟨802731, by rfl⟩ : syracuseStep 8562469 = 1605463) (by norm_num)
theorem B11416625 : Blo 2253435 11416625 := bstep (se 2 (by rfl) ⟨4281234, by rfl⟩ : syracuseStep 11416625 = 8562469) B8562469
theorem B7611083 : Blo 2253435 7611083 := bstep (se 1 (by rfl) ⟨5708312, by rfl⟩ : syracuseStep 7611083 = 11416625) B11416625
theorem B5074055 : Blo 2253435 5074055 := bstep (se 1 (by rfl) ⟨3805541, by rfl⟩ : syracuseStep 5074055 = 7611083) B7611083
theorem B3382703 : Blo 2253435 3382703 := bstep (se 1 (by rfl) ⟨2537027, by rfl⟩ : syracuseStep 3382703 = 5074055) B5074055
theorem B2255135 : Blo 2253435 2255135 := bstep (se 1 (by rfl) ⟨1691351, by rfl⟩ : syracuseStep 2255135 = 3382703) B3382703
theorem B3382709 : Blo 2253435 3382709 := bbase (se 5 (by rfl) ⟨158564, by rfl⟩ : syracuseStep 3382709 = 317129) (by norm_num)
theorem B2255139 : Blo 2253435 2255139 := bstep (se 1 (by rfl) ⟨1691354, by rfl⟩ : syracuseStep 2255139 = 3382709) B3382709
theorem B5708333 : Blo 2253435 5708333 := bbase (se 3 (by rfl) ⟨1070312, by rfl⟩ : syracuseStep 5708333 = 2140625) (by norm_num)
theorem B3805555 : Blo 2253435 3805555 := bstep (se 1 (by rfl) ⟨2854166, by rfl⟩ : syracuseStep 3805555 = 5708333) B5708333
theorem B5074073 : Blo 2253435 5074073 := bstep (se 2 (by rfl) ⟨1902777, by rfl⟩ : syracuseStep 5074073 = 3805555) B3805555
theorem B3382715 : Blo 2253435 3382715 := bstep (se 1 (by rfl) ⟨2537036, by rfl⟩ : syracuseStep 3382715 = 5074073) B5074073
theorem B2255143 : Blo 2253435 2255143 := bstep (se 1 (by rfl) ⟨1691357, by rfl⟩ : syracuseStep 2255143 = 3382715) B3382715
theorem B2537041 : Blo 2253435 2537041 := bbase (se 2 (by rfl) ⟨951390, by rfl⟩ : syracuseStep 2537041 = 1902781) (by norm_num)
theorem B3382721 : Blo 2253435 3382721 := bstep (se 2 (by rfl) ⟨1268520, by rfl⟩ : syracuseStep 3382721 = 2537041) B2537041
theorem B2255147 : Blo 2253435 2255147 := bstep (se 1 (by rfl) ⟨1691360, by rfl⟩ : syracuseStep 2255147 = 3382721) B3382721
theorem B3210949 : Blo 2253435 3210949 := bbase (se 4 (by rfl) ⟨301026, by rfl⟩ : syracuseStep 3210949 = 602053) (by norm_num)
theorem B4281265 : Blo 2253435 4281265 := bstep (se 2 (by rfl) ⟨1605474, by rfl⟩ : syracuseStep 4281265 = 3210949) B3210949
theorem B5708353 : Blo 2253435 5708353 := bstep (se 2 (by rfl) ⟨2140632, by rfl⟩ : syracuseStep 5708353 = 4281265) B4281265
theorem B7611137 : Blo 2253435 7611137 := bstep (se 2 (by rfl) ⟨2854176, by rfl⟩ : syracuseStep 7611137 = 5708353) B5708353
theorem B5074091 : Blo 2253435 5074091 := bstep (se 1 (by rfl) ⟨3805568, by rfl⟩ : syracuseStep 5074091 = 7611137) B7611137
theorem B3382727 : Blo 2253435 3382727 := bstep (se 1 (by rfl) ⟨2537045, by rfl⟩ : syracuseStep 3382727 = 5074091) B5074091
theorem B2255151 : Blo 2253435 2255151 := bstep (se 1 (by rfl) ⟨1691363, by rfl⟩ : syracuseStep 2255151 = 3382727) B3382727
theorem B3382733 : Blo 2253435 3382733 := bbase (se 3 (by rfl) ⟨634262, by rfl⟩ : syracuseStep 3382733 = 1268525) (by norm_num)
theorem B2255155 : Blo 2253435 2255155 := bstep (se 1 (by rfl) ⟨1691366, by rfl⟩ : syracuseStep 2255155 = 3382733) B3382733
theorem B5074109 : Blo 2253435 5074109 := bbase (se 3 (by rfl) ⟨951395, by rfl⟩ : syracuseStep 5074109 = 1902791) (by norm_num)
theorem B3382739 : Blo 2253435 3382739 := bstep (se 1 (by rfl) ⟨2537054, by rfl⟩ : syracuseStep 3382739 = 5074109) B5074109
theorem B2255159 : Blo 2253435 2255159 := bstep (se 1 (by rfl) ⟨1691369, by rfl⟩ : syracuseStep 2255159 = 3382739) B3382739
theorem B3805589 : Blo 2253435 3805589 := bbase (se 6 (by rfl) ⟨89193, by rfl⟩ : syracuseStep 3805589 = 178387) (by norm_num)
theorem B2537059 : Blo 2253435 2537059 := bstep (se 1 (by rfl) ⟨1902794, by rfl⟩ : syracuseStep 2537059 = 3805589) B3805589
theorem B3382745 : Blo 2253435 3382745 := bstep (se 2 (by rfl) ⟨1268529, by rfl⟩ : syracuseStep 3382745 = 2537059) B2537059
theorem B2255163 : Blo 2253435 2255163 := bstep (se 1 (by rfl) ⟨1691372, by rfl⟩ : syracuseStep 2255163 = 3382745) B3382745
theorem B5213533 : Blo 2253435 5213533 := bbase (se 3 (by rfl) ⟨977537, by rfl⟩ : syracuseStep 5213533 = 1955075) (by norm_num)
theorem B6951377 : Blo 2253435 6951377 := bstep (se 2 (by rfl) ⟨2606766, by rfl⟩ : syracuseStep 6951377 = 5213533) B5213533
theorem B18537005 : Blo 2253435 18537005 := bstep (se 3 (by rfl) ⟨3475688, by rfl⟩ : syracuseStep 18537005 = 6951377) B6951377
theorem B12358003 : Blo 2253435 12358003 := bstep (se 1 (by rfl) ⟨9268502, by rfl⟩ : syracuseStep 12358003 = 18537005) B18537005
theorem B16477337 : Blo 2253435 16477337 := bstep (se 2 (by rfl) ⟨6179001, by rfl⟩ : syracuseStep 16477337 = 12358003) B12358003
theorem B10984891 : Blo 2253435 10984891 := bstep (se 1 (by rfl) ⟨8238668, by rfl⟩ : syracuseStep 10984891 = 16477337) B16477337
theorem B14646521 : Blo 2253435 14646521 := bstep (se 2 (by rfl) ⟨5492445, by rfl⟩ : syracuseStep 14646521 = 10984891) B10984891
theorem B9764347 : Blo 2253435 9764347 := bstep (se 1 (by rfl) ⟨7323260, by rfl⟩ : syracuseStep 9764347 = 14646521) B14646521
theorem B13019129 : Blo 2253435 13019129 := bstep (se 2 (by rfl) ⟨4882173, by rfl⟩ : syracuseStep 13019129 = 9764347) B9764347
theorem B8679419 : Blo 2253435 8679419 := bstep (se 1 (by rfl) ⟨6509564, by rfl⟩ : syracuseStep 8679419 = 13019129) B13019129
theorem B5786279 : Blo 2253435 5786279 := bstep (se 1 (by rfl) ⟨4339709, by rfl⟩ : syracuseStep 5786279 = 8679419) B8679419
theorem B3857519 : Blo 2253435 3857519 := bstep (se 1 (by rfl) ⟨2893139, by rfl⟩ : syracuseStep 3857519 = 5786279) B5786279
theorem B2571679 : Blo 2253435 2571679 := bstep (se 1 (by rfl) ⟨1928759, by rfl⟩ : syracuseStep 2571679 = 3857519) B3857519
theorem B3428905 : Blo 2253435 3428905 := bstep (se 2 (by rfl) ⟨1285839, by rfl⟩ : syracuseStep 3428905 = 2571679) B2571679
theorem B4571873 : Blo 2253435 4571873 := bstep (se 2 (by rfl) ⟨1714452, by rfl⟩ : syracuseStep 4571873 = 3428905) B3428905
theorem B3047915 : Blo 2253435 3047915 := bstep (se 1 (by rfl) ⟨2285936, by rfl⟩ : syracuseStep 3047915 = 4571873) B4571873
theorem B8127773 : Blo 2253435 8127773 := bstep (se 3 (by rfl) ⟨1523957, by rfl⟩ : syracuseStep 8127773 = 3047915) B3047915
theorem B5418515 : Blo 2253435 5418515 := bstep (se 1 (by rfl) ⟨4063886, by rfl⟩ : syracuseStep 5418515 = 8127773) B8127773
theorem B14449373 : Blo 2253435 14449373 := bstep (se 3 (by rfl) ⟨2709257, by rfl⟩ : syracuseStep 14449373 = 5418515) B5418515
theorem B9632915 : Blo 2253435 9632915 := bstep (se 1 (by rfl) ⟨7224686, by rfl⟩ : syracuseStep 9632915 = 14449373) B14449373
theorem B6421943 : Blo 2253435 6421943 := bstep (se 1 (by rfl) ⟨4816457, by rfl⟩ : syracuseStep 6421943 = 9632915) B9632915
theorem B17125181 : Blo 2253435 17125181 := bstep (se 3 (by rfl) ⟨3210971, by rfl⟩ : syracuseStep 17125181 = 6421943) B6421943
theorem B11416787 : Blo 2253435 11416787 := bstep (se 1 (by rfl) ⟨8562590, by rfl⟩ : syracuseStep 11416787 = 17125181) B17125181
theorem B7611191 : Blo 2253435 7611191 := bstep (se 1 (by rfl) ⟨5708393, by rfl⟩ : syracuseStep 7611191 = 11416787) B11416787
theorem B5074127 : Blo 2253435 5074127 := bstep (se 1 (by rfl) ⟨3805595, by rfl⟩ : syracuseStep 5074127 = 7611191) B7611191
theorem B3382751 : Blo 2253435 3382751 := bstep (se 1 (by rfl) ⟨2537063, by rfl⟩ : syracuseStep 3382751 = 5074127) B5074127
theorem B2255167 : Blo 2253435 2255167 := bstep (se 1 (by rfl) ⟨1691375, by rfl⟩ : syracuseStep 2255167 = 3382751) B3382751
theorem B3382757 : Blo 2253435 3382757 := bbase (se 4 (by rfl) ⟨317133, by rfl⟩ : syracuseStep 3382757 = 634267) (by norm_num)
theorem B2255171 : Blo 2253435 2255171 := bstep (se 1 (by rfl) ⟨1691378, by rfl⟩ : syracuseStep 2255171 = 3382757) B3382757
theorem B13715669 : Blo 2253435 13715669 := bbase (se 7 (by rfl) ⟨160730, by rfl⟩ : syracuseStep 13715669 = 321461) (by norm_num)
theorem B9143779 : Blo 2253435 9143779 := bstep (se 1 (by rfl) ⟨6857834, by rfl⟩ : syracuseStep 9143779 = 13715669) B13715669
theorem B12191705 : Blo 2253435 12191705 := bstep (se 2 (by rfl) ⟨4571889, by rfl⟩ : syracuseStep 12191705 = 9143779) B9143779
theorem B8127803 : Blo 2253435 8127803 := bstep (se 1 (by rfl) ⟨6095852, by rfl⟩ : syracuseStep 8127803 = 12191705) B12191705
theorem B21674141 : Blo 2253435 21674141 := bstep (se 3 (by rfl) ⟨4063901, by rfl⟩ : syracuseStep 21674141 = 8127803) B8127803
theorem B14449427 : Blo 2253435 14449427 := bstep (se 1 (by rfl) ⟨10837070, by rfl⟩ : syracuseStep 14449427 = 21674141) B21674141
theorem B9632951 : Blo 2253435 9632951 := bstep (se 1 (by rfl) ⟨7224713, by rfl⟩ : syracuseStep 9632951 = 14449427) B14449427
theorem B6421967 : Blo 2253435 6421967 := bstep (se 1 (by rfl) ⟨4816475, by rfl⟩ : syracuseStep 6421967 = 9632951) B9632951
theorem B4281311 : Blo 2253435 4281311 := bstep (se 1 (by rfl) ⟨3210983, by rfl⟩ : syracuseStep 4281311 = 6421967) B6421967
theorem B2854207 : Blo 2253435 2854207 := bstep (se 1 (by rfl) ⟨2140655, by rfl⟩ : syracuseStep 2854207 = 4281311) B4281311
theorem B3805609 : Blo 2253435 3805609 := bstep (se 2 (by rfl) ⟨1427103, by rfl⟩ : syracuseStep 3805609 = 2854207) B2854207
theorem B5074145 : Blo 2253435 5074145 := bstep (se 2 (by rfl) ⟨1902804, by rfl⟩ : syracuseStep 5074145 = 3805609) B3805609
theorem B3382763 : Blo 2253435 3382763 := bstep (se 1 (by rfl) ⟨2537072, by rfl⟩ : syracuseStep 3382763 = 5074145) B5074145
theorem B2255175 : Blo 2253435 2255175 := bstep (se 1 (by rfl) ⟨1691381, by rfl⟩ : syracuseStep 2255175 = 3382763) B3382763
theorem B2537077 : Blo 2253435 2537077 := bbase (se 5 (by rfl) ⟨118925, by rfl⟩ : syracuseStep 2537077 = 237851) (by norm_num)
theorem B3382769 : Blo 2253435 3382769 := bstep (se 2 (by rfl) ⟨1268538, by rfl⟩ : syracuseStep 3382769 = 2537077) B2537077
theorem B2255179 : Blo 2253435 2255179 := bstep (se 1 (by rfl) ⟨1691384, by rfl⟩ : syracuseStep 2255179 = 3382769) B3382769
theorem B2854217 : Blo 2253435 2854217 := bbase (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) (by norm_num)
theorem B7611245 : Blo 2253435 7611245 := bstep (se 3 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 7611245 = 2854217) B2854217
theorem B5074163 : Blo 2253435 5074163 := bstep (se 1 (by rfl) ⟨3805622, by rfl⟩ : syracuseStep 5074163 = 7611245) B7611245
theorem B3382775 : Blo 2253435 3382775 := bstep (se 1 (by rfl) ⟨2537081, by rfl⟩ : syracuseStep 3382775 = 5074163) B5074163
theorem B2255183 : Blo 2253435 2255183 := bstep (se 1 (by rfl) ⟨1691387, by rfl⟩ : syracuseStep 2255183 = 3382775) B3382775
theorem B3382781 : Blo 2253435 3382781 := bbase (se 3 (by rfl) ⟨634271, by rfl⟩ : syracuseStep 3382781 = 1268543) (by norm_num)
theorem B2255187 : Blo 2253435 2255187 := bstep (se 1 (by rfl) ⟨1691390, by rfl⟩ : syracuseStep 2255187 = 3382781) B3382781
theorem B5074181 : Blo 2253435 5074181 := bbase (se 4 (by rfl) ⟨475704, by rfl⟩ : syracuseStep 5074181 = 951409) (by norm_num)
theorem B3382787 : Blo 2253435 3382787 := bstep (se 1 (by rfl) ⟨2537090, by rfl⟩ : syracuseStep 3382787 = 5074181) B5074181
theorem B2255191 : Blo 2253435 2255191 := bstep (se 1 (by rfl) ⟨1691393, by rfl⟩ : syracuseStep 2255191 = 3382787) B3382787
theorem B4281349 : Blo 2253435 4281349 := bbase (se 4 (by rfl) ⟨401376, by rfl⟩ : syracuseStep 4281349 = 802753) (by norm_num)
theorem B5708465 : Blo 2253435 5708465 := bstep (se 2 (by rfl) ⟨2140674, by rfl⟩ : syracuseStep 5708465 = 4281349) B4281349
theorem B3805643 : Blo 2253435 3805643 := bstep (se 1 (by rfl) ⟨2854232, by rfl⟩ : syracuseStep 3805643 = 5708465) B5708465
theorem B2537095 : Blo 2253435 2537095 := bstep (se 1 (by rfl) ⟨1902821, by rfl⟩ : syracuseStep 2537095 = 3805643) B3805643
theorem B3382793 : Blo 2253435 3382793 := bstep (se 2 (by rfl) ⟨1268547, by rfl⟩ : syracuseStep 3382793 = 2537095) B2537095
theorem B2255195 : Blo 2253435 2255195 := bstep (se 1 (by rfl) ⟨1691396, by rfl⟩ : syracuseStep 2255195 = 3382793) B3382793
theorem B11416949 : Blo 2253435 11416949 := bbase (se 5 (by rfl) ⟨535169, by rfl⟩ : syracuseStep 11416949 = 1070339) (by norm_num)
theorem B7611299 : Blo 2253435 7611299 := bstep (se 1 (by rfl) ⟨5708474, by rfl⟩ : syracuseStep 7611299 = 11416949) B11416949
theorem B5074199 : Blo 2253435 5074199 := bstep (se 1 (by rfl) ⟨3805649, by rfl⟩ : syracuseStep 5074199 = 7611299) B7611299
theorem B3382799 : Blo 2253435 3382799 := bstep (se 1 (by rfl) ⟨2537099, by rfl⟩ : syracuseStep 3382799 = 5074199) B5074199
theorem B2255199 : Blo 2253435 2255199 := bstep (se 1 (by rfl) ⟨1691399, by rfl⟩ : syracuseStep 2255199 = 3382799) B3382799
theorem B3382805 : Blo 2253435 3382805 := bbase (se 6 (by rfl) ⟨79284, by rfl⟩ : syracuseStep 3382805 = 158569) (by norm_num)
theorem B2255203 : Blo 2253435 2255203 := bstep (se 1 (by rfl) ⟨1691402, by rfl⟩ : syracuseStep 2255203 = 3382805) B3382805
theorem B2441129 : Blo 2253435 2441129 := bbase (se 2 (by rfl) ⟨915423, by rfl⟩ : syracuseStep 2441129 = 1830847) (by norm_num)
theorem B6509677 : Blo 2253435 6509677 := bstep (se 3 (by rfl) ⟨1220564, by rfl⟩ : syracuseStep 6509677 = 2441129) B2441129
theorem B8679569 : Blo 2253435 8679569 := bstep (se 2 (by rfl) ⟨3254838, by rfl⟩ : syracuseStep 8679569 = 6509677) B6509677
theorem B23145517 : Blo 2253435 23145517 := bstep (se 3 (by rfl) ⟨4339784, by rfl⟩ : syracuseStep 23145517 = 8679569) B8679569
theorem B30860689 : Blo 2253435 30860689 := bstep (se 2 (by rfl) ⟨11572758, by rfl⟩ : syracuseStep 30860689 = 23145517) B23145517
theorem B41147585 : Blo 2253435 41147585 := bstep (se 2 (by rfl) ⟨15430344, by rfl⟩ : syracuseStep 41147585 = 30860689) B30860689
theorem B27431723 : Blo 2253435 27431723 := bstep (se 1 (by rfl) ⟨20573792, by rfl⟩ : syracuseStep 27431723 = 41147585) B41147585
theorem B18287815 : Blo 2253435 18287815 := bstep (se 1 (by rfl) ⟨13715861, by rfl⟩ : syracuseStep 18287815 = 27431723) B27431723
theorem B24383753 : Blo 2253435 24383753 := bstep (se 2 (by rfl) ⟨9143907, by rfl⟩ : syracuseStep 24383753 = 18287815) B18287815
theorem B16255835 : Blo 2253435 16255835 := bstep (se 1 (by rfl) ⟨12191876, by rfl⟩ : syracuseStep 16255835 = 24383753) B24383753
theorem B10837223 : Blo 2253435 10837223 := bstep (se 1 (by rfl) ⟨8127917, by rfl⟩ : syracuseStep 10837223 = 16255835) B16255835
theorem B7224815 : Blo 2253435 7224815 := bstep (se 1 (by rfl) ⟨5418611, by rfl⟩ : syracuseStep 7224815 = 10837223) B10837223
theorem B19266173 : Blo 2253435 19266173 := bstep (se 3 (by rfl) ⟨3612407, by rfl⟩ : syracuseStep 19266173 = 7224815) B7224815
theorem B12844115 : Blo 2253435 12844115 := bstep (se 1 (by rfl) ⟨9633086, by rfl⟩ : syracuseStep 12844115 = 19266173) B19266173
theorem B8562743 : Blo 2253435 8562743 := bstep (se 1 (by rfl) ⟨6422057, by rfl⟩ : syracuseStep 8562743 = 12844115) B12844115
theorem B5708495 : Blo 2253435 5708495 := bstep (se 1 (by rfl) ⟨4281371, by rfl⟩ : syracuseStep 5708495 = 8562743) B8562743
theorem B3805663 : Blo 2253435 3805663 := bstep (se 1 (by rfl) ⟨2854247, by rfl⟩ : syracuseStep 3805663 = 5708495) B5708495
theorem B5074217 : Blo 2253435 5074217 := bstep (se 2 (by rfl) ⟨1902831, by rfl⟩ : syracuseStep 5074217 = 3805663) B3805663
theorem B3382811 : Blo 2253435 3382811 := bstep (se 1 (by rfl) ⟨2537108, by rfl⟩ : syracuseStep 3382811 = 5074217) B5074217
theorem B2255207 : Blo 2253435 2255207 := bstep (se 1 (by rfl) ⟨1691405, by rfl⟩ : syracuseStep 2255207 = 3382811) B3382811
theorem B2537113 : Blo 2253435 2537113 := bbase (se 2 (by rfl) ⟨951417, by rfl⟩ : syracuseStep 2537113 = 1902835) (by norm_num)
theorem B3382817 : Blo 2253435 3382817 := bstep (se 2 (by rfl) ⟨1268556, by rfl⟩ : syracuseStep 3382817 = 2537113) B2537113
theorem B2255211 : Blo 2253435 2255211 := bstep (se 1 (by rfl) ⟨1691408, by rfl⟩ : syracuseStep 2255211 = 3382817) B3382817
theorem B8562773 : Blo 2253435 8562773 := bbase (se 8 (by rfl) ⟨50172, by rfl⟩ : syracuseStep 8562773 = 100345) (by norm_num)
theorem B5708515 : Blo 2253435 5708515 := bstep (se 1 (by rfl) ⟨4281386, by rfl⟩ : syracuseStep 5708515 = 8562773) B8562773
theorem B7611353 : Blo 2253435 7611353 := bstep (se 2 (by rfl) ⟨2854257, by rfl⟩ : syracuseStep 7611353 = 5708515) B5708515
theorem B5074235 : Blo 2253435 5074235 := bstep (se 1 (by rfl) ⟨3805676, by rfl⟩ : syracuseStep 5074235 = 7611353) B7611353
theorem B3382823 : Blo 2253435 3382823 := bstep (se 1 (by rfl) ⟨2537117, by rfl⟩ : syracuseStep 3382823 = 5074235) B5074235
theorem B2255215 : Blo 2253435 2255215 := bstep (se 1 (by rfl) ⟨1691411, by rfl⟩ : syracuseStep 2255215 = 3382823) B3382823
theorem B3382829 : Blo 2253435 3382829 := bbase (se 3 (by rfl) ⟨634280, by rfl⟩ : syracuseStep 3382829 = 1268561) (by norm_num)
theorem B2255219 : Blo 2253435 2255219 := bstep (se 1 (by rfl) ⟨1691414, by rfl⟩ : syracuseStep 2255219 = 3382829) B3382829
theorem B5074253 : Blo 2253435 5074253 := bbase (se 3 (by rfl) ⟨951422, by rfl⟩ : syracuseStep 5074253 = 1902845) (by norm_num)
theorem B3382835 : Blo 2253435 3382835 := bstep (se 1 (by rfl) ⟨2537126, by rfl⟩ : syracuseStep 3382835 = 5074253) B5074253
theorem B2255223 : Blo 2253435 2255223 := bstep (se 1 (by rfl) ⟨1691417, by rfl⟩ : syracuseStep 2255223 = 3382835) B3382835
theorem B2854273 : Blo 2253435 2854273 := bbase (se 2 (by rfl) ⟨1070352, by rfl⟩ : syracuseStep 2854273 = 2140705) (by norm_num)
theorem B3805697 : Blo 2253435 3805697 := bstep (se 2 (by rfl) ⟨1427136, by rfl⟩ : syracuseStep 3805697 = 2854273) B2854273
theorem B2537131 : Blo 2253435 2537131 := bstep (se 1 (by rfl) ⟨1902848, by rfl⟩ : syracuseStep 2537131 = 3805697) B3805697
theorem B3382841 : Blo 2253435 3382841 := bstep (se 2 (by rfl) ⟨1268565, by rfl⟩ : syracuseStep 3382841 = 2537131) B2537131
theorem B2255227 : Blo 2253435 2255227 := bstep (se 1 (by rfl) ⟨1691420, by rfl⟩ : syracuseStep 2255227 = 3382841) B3382841
theorem B2408297 : Blo 2253435 2408297 := bbase (se 2 (by rfl) ⟨903111, by rfl⟩ : syracuseStep 2408297 = 1806223) (by norm_num)
theorem B25688501 : Blo 2253435 25688501 := bstep (se 5 (by rfl) ⟨1204148, by rfl⟩ : syracuseStep 25688501 = 2408297) B2408297
theorem B17125667 : Blo 2253435 17125667 := bstep (se 1 (by rfl) ⟨12844250, by rfl⟩ : syracuseStep 17125667 = 25688501) B25688501
theorem B11417111 : Blo 2253435 11417111 := bstep (se 1 (by rfl) ⟨8562833, by rfl⟩ : syracuseStep 11417111 = 17125667) B17125667
theorem B7611407 : Blo 2253435 7611407 := bstep (se 1 (by rfl) ⟨5708555, by rfl⟩ : syracuseStep 7611407 = 11417111) B11417111
theorem B5074271 : Blo 2253435 5074271 := bstep (se 1 (by rfl) ⟨3805703, by rfl⟩ : syracuseStep 5074271 = 7611407) B7611407
theorem B3382847 : Blo 2253435 3382847 := bstep (se 1 (by rfl) ⟨2537135, by rfl⟩ : syracuseStep 3382847 = 5074271) B5074271
theorem B2255231 : Blo 2253435 2255231 := bstep (se 1 (by rfl) ⟨1691423, by rfl⟩ : syracuseStep 2255231 = 3382847) B3382847
theorem B3382853 : Blo 2253435 3382853 := bbase (se 4 (by rfl) ⟨317142, by rfl⟩ : syracuseStep 3382853 = 634285) (by norm_num)
theorem B2255235 : Blo 2253435 2255235 := bstep (se 1 (by rfl) ⟨1691426, by rfl⟩ : syracuseStep 2255235 = 3382853) B3382853
theorem B3805717 : Blo 2253435 3805717 := bbase (se 6 (by rfl) ⟨89196, by rfl⟩ : syracuseStep 3805717 = 178393) (by norm_num)
theorem B5074289 : Blo 2253435 5074289 := bstep (se 2 (by rfl) ⟨1902858, by rfl⟩ : syracuseStep 5074289 = 3805717) B3805717
theorem B3382859 : Blo 2253435 3382859 := bstep (se 1 (by rfl) ⟨2537144, by rfl⟩ : syracuseStep 3382859 = 5074289) B5074289
theorem B2255239 : Blo 2253435 2255239 := bstep (se 1 (by rfl) ⟨1691429, by rfl⟩ : syracuseStep 2255239 = 3382859) B3382859
theorem B2537149 : Blo 2253435 2537149 := bbase (se 3 (by rfl) ⟨475715, by rfl⟩ : syracuseStep 2537149 = 951431) (by norm_num)
theorem B3382865 : Blo 2253435 3382865 := bstep (se 2 (by rfl) ⟨1268574, by rfl⟩ : syracuseStep 3382865 = 2537149) B2537149
theorem B2255243 : Blo 2253435 2255243 := bstep (se 1 (by rfl) ⟨1691432, by rfl⟩ : syracuseStep 2255243 = 3382865) B3382865
theorem B7611461 : Blo 2253435 7611461 := bbase (se 4 (by rfl) ⟨713574, by rfl⟩ : syracuseStep 7611461 = 1427149) (by norm_num)
theorem B5074307 : Blo 2253435 5074307 := bstep (se 1 (by rfl) ⟨3805730, by rfl⟩ : syracuseStep 5074307 = 7611461) B7611461
theorem B3382871 : Blo 2253435 3382871 := bstep (se 1 (by rfl) ⟨2537153, by rfl⟩ : syracuseStep 3382871 = 5074307) B5074307
theorem B2255247 : Blo 2253435 2255247 := bstep (se 1 (by rfl) ⟨1691435, by rfl⟩ : syracuseStep 2255247 = 3382871) B3382871
theorem B3382877 : Blo 2253435 3382877 := bbase (se 3 (by rfl) ⟨634289, by rfl⟩ : syracuseStep 3382877 = 1268579) (by norm_num)
theorem B2255251 : Blo 2253435 2255251 := bstep (se 1 (by rfl) ⟨1691438, by rfl⟩ : syracuseStep 2255251 = 3382877) B3382877
theorem B5074325 : Blo 2253435 5074325 := bbase (se 6 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 5074325 = 237859) (by norm_num)
theorem B3382883 : Blo 2253435 3382883 := bstep (se 1 (by rfl) ⟨2537162, by rfl⟩ : syracuseStep 3382883 = 5074325) B5074325
theorem B2255255 : Blo 2253435 2255255 := bstep (se 1 (by rfl) ⟨1691441, by rfl⟩ : syracuseStep 2255255 = 3382883) B3382883
theorem B16256213 : Blo 2253435 16256213 := bbase (se 7 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 16256213 = 381005) (by norm_num)
theorem B10837475 : Blo 2253435 10837475 := bstep (se 1 (by rfl) ⟨8128106, by rfl⟩ : syracuseStep 10837475 = 16256213) B16256213
theorem B7224983 : Blo 2253435 7224983 := bstep (se 1 (by rfl) ⟨5418737, by rfl⟩ : syracuseStep 7224983 = 10837475) B10837475
theorem B4816655 : Blo 2253435 4816655 := bstep (se 1 (by rfl) ⟨3612491, by rfl⟩ : syracuseStep 4816655 = 7224983) B7224983
theorem B3211103 : Blo 2253435 3211103 := bstep (se 1 (by rfl) ⟨2408327, by rfl⟩ : syracuseStep 3211103 = 4816655) B4816655
theorem B8562941 : Blo 2253435 8562941 := bstep (se 3 (by rfl) ⟨1605551, by rfl⟩ : syracuseStep 8562941 = 3211103) B3211103
theorem B5708627 : Blo 2253435 5708627 := bstep (se 1 (by rfl) ⟨4281470, by rfl⟩ : syracuseStep 5708627 = 8562941) B8562941
theorem B3805751 : Blo 2253435 3805751 := bstep (se 1 (by rfl) ⟨2854313, by rfl⟩ : syracuseStep 3805751 = 5708627) B5708627
theorem B2537167 : Blo 2253435 2537167 := bstep (se 1 (by rfl) ⟨1902875, by rfl⟩ : syracuseStep 2537167 = 3805751) B3805751
theorem B3382889 : Blo 2253435 3382889 := bstep (se 2 (by rfl) ⟨1268583, by rfl⟩ : syracuseStep 3382889 = 2537167) B2537167
theorem B2255259 : Blo 2253435 2255259 := bstep (se 1 (by rfl) ⟨1691444, by rfl⟩ : syracuseStep 2255259 = 3382889) B3382889
theorem B2709373 : Blo 2253435 2709373 := bbase (se 3 (by rfl) ⟨508007, by rfl⟩ : syracuseStep 2709373 = 1016015) (by norm_num)
theorem B3612497 : Blo 2253435 3612497 := bstep (se 2 (by rfl) ⟨1354686, by rfl⟩ : syracuseStep 3612497 = 2709373) B2709373
theorem B9633325 : Blo 2253435 9633325 := bstep (se 3 (by rfl) ⟨1806248, by rfl⟩ : syracuseStep 9633325 = 3612497) B3612497
theorem B12844433 : Blo 2253435 12844433 := bstep (se 2 (by rfl) ⟨4816662, by rfl⟩ : syracuseStep 12844433 = 9633325) B9633325
theorem B8562955 : Blo 2253435 8562955 := bstep (se 1 (by rfl) ⟨6422216, by rfl⟩ : syracuseStep 8562955 = 12844433) B12844433
theorem B11417273 : Blo 2253435 11417273 := bstep (se 2 (by rfl) ⟨4281477, by rfl⟩ : syracuseStep 11417273 = 8562955) B8562955
theorem B7611515 : Blo 2253435 7611515 := bstep (se 1 (by rfl) ⟨5708636, by rfl⟩ : syracuseStep 7611515 = 11417273) B11417273
theorem B5074343 : Blo 2253435 5074343 := bstep (se 1 (by rfl) ⟨3805757, by rfl⟩ : syracuseStep 5074343 = 7611515) B7611515
theorem B3382895 : Blo 2253435 3382895 := bstep (se 1 (by rfl) ⟨2537171, by rfl⟩ : syracuseStep 3382895 = 5074343) B5074343
theorem B2255263 : Blo 2253435 2255263 := bstep (se 1 (by rfl) ⟨1691447, by rfl⟩ : syracuseStep 2255263 = 3382895) B3382895
theorem B3382901 : Blo 2253435 3382901 := bbase (se 5 (by rfl) ⟨158573, by rfl⟩ : syracuseStep 3382901 = 317147) (by norm_num)
theorem B2255267 : Blo 2253435 2255267 := bstep (se 1 (by rfl) ⟨1691450, by rfl⟩ : syracuseStep 2255267 = 3382901) B3382901
theorem B4281493 : Blo 2253435 4281493 := bbase (se 6 (by rfl) ⟨100347, by rfl⟩ : syracuseStep 4281493 = 200695) (by norm_num)
theorem B5708657 : Blo 2253435 5708657 := bstep (se 2 (by rfl) ⟨2140746, by rfl⟩ : syracuseStep 5708657 = 4281493) B4281493
theorem B3805771 : Blo 2253435 3805771 := bstep (se 1 (by rfl) ⟨2854328, by rfl⟩ : syracuseStep 3805771 = 5708657) B5708657
theorem B5074361 : Blo 2253435 5074361 := bstep (se 2 (by rfl) ⟨1902885, by rfl⟩ : syracuseStep 5074361 = 3805771) B3805771
theorem B3382907 : Blo 2253435 3382907 := bstep (se 1 (by rfl) ⟨2537180, by rfl⟩ : syracuseStep 3382907 = 5074361) B5074361
theorem B2255271 : Blo 2253435 2255271 := bstep (se 1 (by rfl) ⟨1691453, by rfl⟩ : syracuseStep 2255271 = 3382907) B3382907
theorem B2537185 : Blo 2253435 2537185 := bbase (se 2 (by rfl) ⟨951444, by rfl⟩ : syracuseStep 2537185 = 1902889) (by norm_num)
theorem B3382913 : Blo 2253435 3382913 := bstep (se 2 (by rfl) ⟨1268592, by rfl⟩ : syracuseStep 3382913 = 2537185) B2537185
theorem B2255275 : Blo 2253435 2255275 := bstep (se 1 (by rfl) ⟨1691456, by rfl⟩ : syracuseStep 2255275 = 3382913) B3382913
theorem B5708677 : Blo 2253435 5708677 := bbase (se 4 (by rfl) ⟨535188, by rfl⟩ : syracuseStep 5708677 = 1070377) (by norm_num)
theorem B7611569 : Blo 2253435 7611569 := bstep (se 2 (by rfl) ⟨2854338, by rfl⟩ : syracuseStep 7611569 = 5708677) B5708677
theorem B5074379 : Blo 2253435 5074379 := bstep (se 1 (by rfl) ⟨3805784, by rfl⟩ : syracuseStep 5074379 = 7611569) B7611569
theorem B3382919 : Blo 2253435 3382919 := bstep (se 1 (by rfl) ⟨2537189, by rfl⟩ : syracuseStep 3382919 = 5074379) B5074379
theorem B2255279 : Blo 2253435 2255279 := bstep (se 1 (by rfl) ⟨1691459, by rfl⟩ : syracuseStep 2255279 = 3382919) B3382919
theorem B3382925 : Blo 2253435 3382925 := bbase (se 3 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 3382925 = 1268597) (by norm_num)
theorem B2255283 : Blo 2253435 2255283 := bstep (se 1 (by rfl) ⟨1691462, by rfl⟩ : syracuseStep 2255283 = 3382925) B3382925
theorem B5074397 : Blo 2253435 5074397 := bbase (se 3 (by rfl) ⟨951449, by rfl⟩ : syracuseStep 5074397 = 1902899) (by norm_num)
theorem B3382931 : Blo 2253435 3382931 := bstep (se 1 (by rfl) ⟨2537198, by rfl⟩ : syracuseStep 3382931 = 5074397) B5074397
theorem B2255287 : Blo 2253435 2255287 := bstep (se 1 (by rfl) ⟨1691465, by rfl⟩ : syracuseStep 2255287 = 3382931) B3382931
theorem B3805805 : Blo 2253435 3805805 := bbase (se 3 (by rfl) ⟨713588, by rfl⟩ : syracuseStep 3805805 = 1427177) (by norm_num)
theorem B2537203 : Blo 2253435 2537203 := bstep (se 1 (by rfl) ⟨1902902, by rfl⟩ : syracuseStep 2537203 = 3805805) B3805805
theorem B3382937 : Blo 2253435 3382937 := bstep (se 2 (by rfl) ⟨1268601, by rfl⟩ : syracuseStep 3382937 = 2537203) B2537203
theorem B2255291 : Blo 2253435 2255291 := bstep (se 1 (by rfl) ⟨1691468, by rfl⟩ : syracuseStep 2255291 = 3382937) B3382937
theorem B13019861 : Blo 2253435 13019861 := bbase (se 7 (by rfl) ⟨152576, by rfl⟩ : syracuseStep 13019861 = 305153) (by norm_num)
theorem B8679907 : Blo 2253435 8679907 := bstep (se 1 (by rfl) ⟨6509930, by rfl⟩ : syracuseStep 8679907 = 13019861) B13019861
theorem B11573209 : Blo 2253435 11573209 := bstep (se 2 (by rfl) ⟨4339953, by rfl⟩ : syracuseStep 11573209 = 8679907) B8679907
theorem B15430945 : Blo 2253435 15430945 := bstep (se 2 (by rfl) ⟨5786604, by rfl⟩ : syracuseStep 15430945 = 11573209) B11573209
theorem B20574593 : Blo 2253435 20574593 := bstep (se 2 (by rfl) ⟨7715472, by rfl⟩ : syracuseStep 20574593 = 15430945) B15430945
theorem B13716395 : Blo 2253435 13716395 := bstep (se 1 (by rfl) ⟨10287296, by rfl⟩ : syracuseStep 13716395 = 20574593) B20574593
theorem B9144263 : Blo 2253435 9144263 := bstep (se 1 (by rfl) ⟨6858197, by rfl⟩ : syracuseStep 9144263 = 13716395) B13716395
theorem B24384701 : Blo 2253435 24384701 := bstep (se 3 (by rfl) ⟨4572131, by rfl⟩ : syracuseStep 24384701 = 9144263) B9144263
theorem B16256467 : Blo 2253435 16256467 := bstep (se 1 (by rfl) ⟨12192350, by rfl⟩ : syracuseStep 16256467 = 24384701) B24384701
theorem B21675289 : Blo 2253435 21675289 := bstep (se 2 (by rfl) ⟨8128233, by rfl⟩ : syracuseStep 21675289 = 16256467) B16256467
theorem B28900385 : Blo 2253435 28900385 := bstep (se 2 (by rfl) ⟨10837644, by rfl⟩ : syracuseStep 28900385 = 21675289) B21675289
theorem B19266923 : Blo 2253435 19266923 := bstep (se 1 (by rfl) ⟨14450192, by rfl⟩ : syracuseStep 19266923 = 28900385) B28900385
theorem B12844615 : Blo 2253435 12844615 := bstep (se 1 (by rfl) ⟨9633461, by rfl⟩ : syracuseStep 12844615 = 19266923) B19266923
theorem B17126153 : Blo 2253435 17126153 := bstep (se 2 (by rfl) ⟨6422307, by rfl⟩ : syracuseStep 17126153 = 12844615) B12844615
theorem B11417435 : Blo 2253435 11417435 := bstep (se 1 (by rfl) ⟨8563076, by rfl⟩ : syracuseStep 11417435 = 17126153) B17126153
theorem B7611623 : Blo 2253435 7611623 := bstep (se 1 (by rfl) ⟨5708717, by rfl⟩ : syracuseStep 7611623 = 11417435) B11417435
theorem B5074415 : Blo 2253435 5074415 := bstep (se 1 (by rfl) ⟨3805811, by rfl⟩ : syracuseStep 5074415 = 7611623) B7611623
theorem B3382943 : Blo 2253435 3382943 := bstep (se 1 (by rfl) ⟨2537207, by rfl⟩ : syracuseStep 3382943 = 5074415) B5074415
theorem B2255295 : Blo 2253435 2255295 := bstep (se 1 (by rfl) ⟨1691471, by rfl⟩ : syracuseStep 2255295 = 3382943) B3382943
theorem B3382949 : Blo 2253435 3382949 := bbase (se 4 (by rfl) ⟨317151, by rfl⟩ : syracuseStep 3382949 = 634303) (by norm_num)
theorem B2255299 : Blo 2253435 2255299 := bstep (se 1 (by rfl) ⟨1691474, by rfl⟩ : syracuseStep 2255299 = 3382949) B3382949
theorem B2854369 : Blo 2253435 2854369 := bbase (se 2 (by rfl) ⟨1070388, by rfl⟩ : syracuseStep 2854369 = 2140777) (by norm_num)
theorem B3805825 : Blo 2253435 3805825 := bstep (se 2 (by rfl) ⟨1427184, by rfl⟩ : syracuseStep 3805825 = 2854369) B2854369
theorem B5074433 : Blo 2253435 5074433 := bstep (se 2 (by rfl) ⟨1902912, by rfl⟩ : syracuseStep 5074433 = 3805825) B3805825
theorem B3382955 : Blo 2253435 3382955 := bstep (se 1 (by rfl) ⟨2537216, by rfl⟩ : syracuseStep 3382955 = 5074433) B5074433
theorem B2255303 : Blo 2253435 2255303 := bstep (se 1 (by rfl) ⟨1691477, by rfl⟩ : syracuseStep 2255303 = 3382955) B3382955
theorem B2537221 : Blo 2253435 2537221 := bbase (se 4 (by rfl) ⟨237864, by rfl⟩ : syracuseStep 2537221 = 475729) (by norm_num)
theorem B3382961 : Blo 2253435 3382961 := bstep (se 2 (by rfl) ⟨1268610, by rfl⟩ : syracuseStep 3382961 = 2537221) B2537221
theorem B2255307 : Blo 2253435 2255307 := bstep (se 1 (by rfl) ⟨1691480, by rfl⟩ : syracuseStep 2255307 = 3382961) B3382961
theorem B8679973 : Blo 2253435 8679973 := bbase (se 4 (by rfl) ⟨813747, by rfl⟩ : syracuseStep 8679973 = 1627495) (by norm_num)
theorem B11573297 : Blo 2253435 11573297 := bstep (se 2 (by rfl) ⟨4339986, by rfl⟩ : syracuseStep 11573297 = 8679973) B8679973
theorem B7715531 : Blo 2253435 7715531 := bstep (se 1 (by rfl) ⟨5786648, by rfl⟩ : syracuseStep 7715531 = 11573297) B11573297
theorem B20574749 : Blo 2253435 20574749 := bstep (se 3 (by rfl) ⟨3857765, by rfl⟩ : syracuseStep 20574749 = 7715531) B7715531
theorem B13716499 : Blo 2253435 13716499 := bstep (se 1 (by rfl) ⟨10287374, by rfl⟩ : syracuseStep 13716499 = 20574749) B20574749
theorem B18288665 : Blo 2253435 18288665 := bstep (se 2 (by rfl) ⟨6858249, by rfl⟩ : syracuseStep 18288665 = 13716499) B13716499
theorem B12192443 : Blo 2253435 12192443 := bstep (se 1 (by rfl) ⟨9144332, by rfl⟩ : syracuseStep 12192443 = 18288665) B18288665
theorem B8128295 : Blo 2253435 8128295 := bstep (se 1 (by rfl) ⟨6096221, by rfl⟩ : syracuseStep 8128295 = 12192443) B12192443
theorem B5418863 : Blo 2253435 5418863 := bstep (se 1 (by rfl) ⟨4064147, by rfl⟩ : syracuseStep 5418863 = 8128295) B8128295
theorem B3612575 : Blo 2253435 3612575 := bstep (se 1 (by rfl) ⟨2709431, by rfl⟩ : syracuseStep 3612575 = 5418863) B5418863
theorem B2408383 : Blo 2253435 2408383 := bstep (se 1 (by rfl) ⟨1806287, by rfl⟩ : syracuseStep 2408383 = 3612575) B3612575
theorem B3211177 : Blo 2253435 3211177 := bstep (se 2 (by rfl) ⟨1204191, by rfl⟩ : syracuseStep 3211177 = 2408383) B2408383
theorem B4281569 : Blo 2253435 4281569 := bstep (se 2 (by rfl) ⟨1605588, by rfl⟩ : syracuseStep 4281569 = 3211177) B3211177
theorem B2854379 : Blo 2253435 2854379 := bstep (se 1 (by rfl) ⟨2140784, by rfl⟩ : syracuseStep 2854379 = 4281569) B4281569
theorem B7611677 : Blo 2253435 7611677 := bstep (se 3 (by rfl) ⟨1427189, by rfl⟩ : syracuseStep 7611677 = 2854379) B2854379
theorem B5074451 : Blo 2253435 5074451 := bstep (se 1 (by rfl) ⟨3805838, by rfl⟩ : syracuseStep 5074451 = 7611677) B7611677
theorem B3382967 : Blo 2253435 3382967 := bstep (se 1 (by rfl) ⟨2537225, by rfl⟩ : syracuseStep 3382967 = 5074451) B5074451
theorem B2255311 : Blo 2253435 2255311 := bstep (se 1 (by rfl) ⟨1691483, by rfl⟩ : syracuseStep 2255311 = 3382967) B3382967
theorem B3382973 : Blo 2253435 3382973 := bbase (se 3 (by rfl) ⟨634307, by rfl⟩ : syracuseStep 3382973 = 1268615) (by norm_num)
theorem B2255315 : Blo 2253435 2255315 := bstep (se 1 (by rfl) ⟨1691486, by rfl⟩ : syracuseStep 2255315 = 3382973) B3382973
theorem B5074469 : Blo 2253435 5074469 := bbase (se 4 (by rfl) ⟨475731, by rfl⟩ : syracuseStep 5074469 = 951463) (by norm_num)
theorem B3382979 : Blo 2253435 3382979 := bstep (se 1 (by rfl) ⟨2537234, by rfl⟩ : syracuseStep 3382979 = 5074469) B5074469
theorem B2255319 : Blo 2253435 2255319 := bstep (se 1 (by rfl) ⟨1691489, by rfl⟩ : syracuseStep 2255319 = 3382979) B3382979
theorem B5708789 : Blo 2253435 5708789 := bbase (se 5 (by rfl) ⟨267599, by rfl⟩ : syracuseStep 5708789 = 535199) (by norm_num)
theorem B3805859 : Blo 2253435 3805859 := bstep (se 1 (by rfl) ⟨2854394, by rfl⟩ : syracuseStep 3805859 = 5708789) B5708789
theorem B2537239 : Blo 2253435 2537239 := bstep (se 1 (by rfl) ⟨1902929, by rfl⟩ : syracuseStep 2537239 = 3805859) B3805859
theorem B3382985 : Blo 2253435 3382985 := bstep (se 2 (by rfl) ⟨1268619, by rfl⟩ : syracuseStep 3382985 = 2537239) B2537239
theorem B2255323 : Blo 2253435 2255323 := bstep (se 1 (by rfl) ⟨1691492, by rfl⟩ : syracuseStep 2255323 = 3382985) B3382985
theorem B2317289 : Blo 2253435 2317289 := bbase (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) (by norm_num)
theorem B6179437 : Blo 2253435 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B8239249 : Blo 2253435 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B43942661 : Blo 2253435 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B29295107 : Blo 2253435 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B19530071 : Blo 2253435 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B13020047 : Blo 2253435 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B8680031 : Blo 2253435 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B5786687 : Blo 2253435 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B15431165 : Blo 2253435 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B10287443 : Blo 2253435 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B27433181 : Blo 2253435 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B73155149 : Blo 2253435 73155149 := bstep (se 3 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 73155149 = 27433181) B27433181
theorem B48770099 : Blo 2253435 48770099 := bstep (se 1 (by rfl) ⟨36577574, by rfl⟩ : syracuseStep 48770099 = 73155149) B73155149
theorem B32513399 : Blo 2253435 32513399 := bstep (se 1 (by rfl) ⟨24385049, by rfl⟩ : syracuseStep 32513399 = 48770099) B48770099
theorem B21675599 : Blo 2253435 21675599 := bstep (se 1 (by rfl) ⟨16256699, by rfl⟩ : syracuseStep 21675599 = 32513399) B32513399
theorem B14450399 : Blo 2253435 14450399 := bstep (se 1 (by rfl) ⟨10837799, by rfl⟩ : syracuseStep 14450399 = 21675599) B21675599
theorem B9633599 : Blo 2253435 9633599 := bstep (se 1 (by rfl) ⟨7225199, by rfl⟩ : syracuseStep 9633599 = 14450399) B14450399
theorem B6422399 : Blo 2253435 6422399 := bstep (se 1 (by rfl) ⟨4816799, by rfl⟩ : syracuseStep 6422399 = 9633599) B9633599
theorem B4281599 : Blo 2253435 4281599 := bstep (se 1 (by rfl) ⟨3211199, by rfl⟩ : syracuseStep 4281599 = 6422399) B6422399
theorem B11417597 : Blo 2253435 11417597 := bstep (se 3 (by rfl) ⟨2140799, by rfl⟩ : syracuseStep 11417597 = 4281599) B4281599
theorem B7611731 : Blo 2253435 7611731 := bstep (se 1 (by rfl) ⟨5708798, by rfl⟩ : syracuseStep 7611731 = 11417597) B11417597
theorem B5074487 : Blo 2253435 5074487 := bstep (se 1 (by rfl) ⟨3805865, by rfl⟩ : syracuseStep 5074487 = 7611731) B7611731
theorem B3382991 : Blo 2253435 3382991 := bstep (se 1 (by rfl) ⟨2537243, by rfl⟩ : syracuseStep 3382991 = 5074487) B5074487
theorem B2255327 : Blo 2253435 2255327 := bstep (se 1 (by rfl) ⟨1691495, by rfl⟩ : syracuseStep 2255327 = 3382991) B3382991
theorem B3382997 : Blo 2253435 3382997 := bbase (se 7 (by rfl) ⟨39644, by rfl⟩ : syracuseStep 3382997 = 79289) (by norm_num)
theorem B2255331 : Blo 2253435 2255331 := bstep (se 1 (by rfl) ⟨1691498, by rfl⟩ : syracuseStep 2255331 = 3382997) B3382997
theorem B3612613 : Blo 2253435 3612613 := bbase (se 4 (by rfl) ⟨338682, by rfl⟩ : syracuseStep 3612613 = 677365) (by norm_num)
theorem B4816817 : Blo 2253435 4816817 := bstep (se 2 (by rfl) ⟨1806306, by rfl⟩ : syracuseStep 4816817 = 3612613) B3612613
theorem B3211211 : Blo 2253435 3211211 := bstep (se 1 (by rfl) ⟨2408408, by rfl⟩ : syracuseStep 3211211 = 4816817) B4816817
theorem B8563229 : Blo 2253435 8563229 := bstep (se 3 (by rfl) ⟨1605605, by rfl⟩ : syracuseStep 8563229 = 3211211) B3211211
theorem B5708819 : Blo 2253435 5708819 := bstep (se 1 (by rfl) ⟨4281614, by rfl⟩ : syracuseStep 5708819 = 8563229) B8563229
theorem B3805879 : Blo 2253435 3805879 := bstep (se 1 (by rfl) ⟨2854409, by rfl⟩ : syracuseStep 3805879 = 5708819) B5708819
theorem B5074505 : Blo 2253435 5074505 := bstep (se 2 (by rfl) ⟨1902939, by rfl⟩ : syracuseStep 5074505 = 3805879) B3805879
theorem B3383003 : Blo 2253435 3383003 := bstep (se 1 (by rfl) ⟨2537252, by rfl⟩ : syracuseStep 3383003 = 5074505) B5074505
theorem B2255335 : Blo 2253435 2255335 := bstep (se 1 (by rfl) ⟨1691501, by rfl⟩ : syracuseStep 2255335 = 3383003) B3383003
theorem B2537257 : Blo 2253435 2537257 := bbase (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) (by norm_num)
theorem B3383009 : Blo 2253435 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B2255339 : Blo 2253435 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B2709469 : Blo 2253435 2709469 := bbase (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) (by norm_num)
theorem B14450501 : Blo 2253435 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B9633667 : Blo 2253435 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B12844889 : Blo 2253435 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B8563259 : Blo 2253435 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B5708839 : Blo 2253435 5708839 := bstep (se 1 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 5708839 = 8563259) B8563259
theorem B7611785 : Blo 2253435 7611785 := bstep (se 2 (by rfl) ⟨2854419, by rfl⟩ : syracuseStep 7611785 = 5708839) B5708839
theorem B5074523 : Blo 2253435 5074523 := bstep (se 1 (by rfl) ⟨3805892, by rfl⟩ : syracuseStep 5074523 = 7611785) B7611785
theorem B3383015 : Blo 2253435 3383015 := bstep (se 1 (by rfl) ⟨2537261, by rfl⟩ : syracuseStep 3383015 = 5074523) B5074523
theorem B2255343 : Blo 2253435 2255343 := bstep (se 1 (by rfl) ⟨1691507, by rfl⟩ : syracuseStep 2255343 = 3383015) B3383015
theorem B3383021 : Blo 2253435 3383021 := bbase (se 3 (by rfl) ⟨634316, by rfl⟩ : syracuseStep 3383021 = 1268633) (by norm_num)
theorem B2255347 : Blo 2253435 2255347 := bstep (se 1 (by rfl) ⟨1691510, by rfl⟩ : syracuseStep 2255347 = 3383021) B3383021
theorem B5074541 : Blo 2253435 5074541 := bbase (se 3 (by rfl) ⟨951476, by rfl⟩ : syracuseStep 5074541 = 1902953) (by norm_num)
theorem B3383027 : Blo 2253435 3383027 := bstep (se 1 (by rfl) ⟨2537270, by rfl⟩ : syracuseStep 3383027 = 5074541) B5074541
theorem B2255351 : Blo 2253435 2255351 := bstep (se 1 (by rfl) ⟨1691513, by rfl⟩ : syracuseStep 2255351 = 3383027) B3383027
theorem B4281653 : Blo 2253435 4281653 := bbase (se 5 (by rfl) ⟨200702, by rfl⟩ : syracuseStep 4281653 = 401405) (by norm_num)
theorem B2854435 : Blo 2253435 2854435 := bstep (se 1 (by rfl) ⟨2140826, by rfl⟩ : syracuseStep 2854435 = 4281653) B4281653
theorem B3805913 : Blo 2253435 3805913 := bstep (se 2 (by rfl) ⟨1427217, by rfl⟩ : syracuseStep 3805913 = 2854435) B2854435
theorem B2537275 : Blo 2253435 2537275 := bstep (se 1 (by rfl) ⟨1902956, by rfl⟩ : syracuseStep 2537275 = 3805913) B3805913
theorem B3383033 : Blo 2253435 3383033 := bstep (se 2 (by rfl) ⟨1268637, by rfl⟩ : syracuseStep 3383033 = 2537275) B2537275
theorem B2255355 : Blo 2253435 2255355 := bstep (se 1 (by rfl) ⟨1691516, by rfl⟩ : syracuseStep 2255355 = 3383033) B3383033
theorem B26395733 : Blo 2253435 26395733 := bbase (se 8 (by rfl) ⟨154662, by rfl⟩ : syracuseStep 26395733 = 309325) (by norm_num)
theorem B17597155 : Blo 2253435 17597155 := bstep (se 1 (by rfl) ⟨13197866, by rfl⟩ : syracuseStep 17597155 = 26395733) B26395733
theorem B23462873 : Blo 2253435 23462873 := bstep (se 2 (by rfl) ⟨8798577, by rfl⟩ : syracuseStep 23462873 = 17597155) B17597155
theorem B1001082581 : Blo 2253435 1001082581 := bstep (se 7 (by rfl) ⟨11731436, by rfl⟩ : syracuseStep 1001082581 = 23462873) B23462873
theorem B667388387 : Blo 2253435 667388387 := bstep (se 1 (by rfl) ⟨500541290, by rfl⟩ : syracuseStep 667388387 = 1001082581) B1001082581
theorem B444925591 : Blo 2253435 444925591 := bstep (se 1 (by rfl) ⟨333694193, by rfl⟩ : syracuseStep 444925591 = 667388387) B667388387
theorem B2372936485 : Blo 2253435 2372936485 := bstep (se 4 (by rfl) ⟨222462795, by rfl⟩ : syracuseStep 2372936485 = 444925591) B444925591
theorem B3163915313 : Blo 2253435 3163915313 := bstep (se 2 (by rfl) ⟨1186468242, by rfl⟩ : syracuseStep 3163915313 = 2372936485) B2372936485
theorem B2109276875 : Blo 2253435 2109276875 := bstep (se 1 (by rfl) ⟨1581957656, by rfl⟩ : syracuseStep 2109276875 = 3163915313) B3163915313
theorem B1406184583 : Blo 2253435 1406184583 := bstep (se 1 (by rfl) ⟨1054638437, by rfl⟩ : syracuseStep 1406184583 = 2109276875) B2109276875
theorem B1874912777 : Blo 2253435 1874912777 := bstep (se 2 (by rfl) ⟨703092291, by rfl⟩ : syracuseStep 1874912777 = 1406184583) B1406184583
theorem B1249941851 : Blo 2253435 1249941851 := bstep (se 1 (by rfl) ⟨937456388, by rfl⟩ : syracuseStep 1249941851 = 1874912777) B1874912777
theorem B833294567 : Blo 2253435 833294567 := bstep (se 1 (by rfl) ⟨624970925, by rfl⟩ : syracuseStep 833294567 = 1249941851) B1249941851
theorem B555529711 : Blo 2253435 555529711 := bstep (se 1 (by rfl) ⟨416647283, by rfl⟩ : syracuseStep 555529711 = 833294567) B833294567
theorem B740706281 : Blo 2253435 740706281 := bstep (se 2 (by rfl) ⟨277764855, by rfl⟩ : syracuseStep 740706281 = 555529711) B555529711
theorem B493804187 : Blo 2253435 493804187 := bstep (se 1 (by rfl) ⟨370353140, by rfl⟩ : syracuseStep 493804187 = 740706281) B740706281
theorem B329202791 : Blo 2253435 329202791 := bstep (se 1 (by rfl) ⟨246902093, by rfl⟩ : syracuseStep 329202791 = 493804187) B493804187
theorem B219468527 : Blo 2253435 219468527 := bstep (se 1 (by rfl) ⟨164601395, by rfl⟩ : syracuseStep 219468527 = 329202791) B329202791
theorem B146312351 : Blo 2253435 146312351 := bstep (se 1 (by rfl) ⟨109734263, by rfl⟩ : syracuseStep 146312351 = 219468527) B219468527
theorem B97541567 : Blo 2253435 97541567 := bstep (se 1 (by rfl) ⟨73156175, by rfl⟩ : syracuseStep 97541567 = 146312351) B146312351
theorem B65027711 : Blo 2253435 65027711 := bstep (se 1 (by rfl) ⟨48770783, by rfl⟩ : syracuseStep 65027711 = 97541567) B97541567
theorem B43351807 : Blo 2253435 43351807 := bstep (se 1 (by rfl) ⟨32513855, by rfl⟩ : syracuseStep 43351807 = 65027711) B65027711
theorem B57802409 : Blo 2253435 57802409 := bstep (se 2 (by rfl) ⟨21675903, by rfl⟩ : syracuseStep 57802409 = 43351807) B43351807
theorem B38534939 : Blo 2253435 38534939 := bstep (se 1 (by rfl) ⟨28901204, by rfl⟩ : syracuseStep 38534939 = 57802409) B57802409
theorem B25689959 : Blo 2253435 25689959 := bstep (se 1 (by rfl) ⟨19267469, by rfl⟩ : syracuseStep 25689959 = 38534939) B38534939
theorem B17126639 : Blo 2253435 17126639 := bstep (se 1 (by rfl) ⟨12844979, by rfl⟩ : syracuseStep 17126639 = 25689959) B25689959
theorem B11417759 : Blo 2253435 11417759 := bstep (se 1 (by rfl) ⟨8563319, by rfl⟩ : syracuseStep 11417759 = 17126639) B17126639
theorem B7611839 : Blo 2253435 7611839 := bstep (se 1 (by rfl) ⟨5708879, by rfl⟩ : syracuseStep 7611839 = 11417759) B11417759
theorem B5074559 : Blo 2253435 5074559 := bstep (se 1 (by rfl) ⟨3805919, by rfl⟩ : syracuseStep 5074559 = 7611839) B7611839
theorem B3383039 : Blo 2253435 3383039 := bstep (se 1 (by rfl) ⟨2537279, by rfl⟩ : syracuseStep 3383039 = 5074559) B5074559
theorem B2255359 : Blo 2253435 2255359 := bstep (se 1 (by rfl) ⟨1691519, by rfl⟩ : syracuseStep 2255359 = 3383039) B3383039
theorem B3383045 : Blo 2253435 3383045 := bbase (se 4 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 3383045 = 634321) (by norm_num)
theorem B2255363 : Blo 2253435 2255363 := bstep (se 1 (by rfl) ⟨1691522, by rfl⟩ : syracuseStep 2255363 = 3383045) B3383045
theorem B3805933 : Blo 2253435 3805933 := bbase (se 3 (by rfl) ⟨713612, by rfl⟩ : syracuseStep 3805933 = 1427225) (by norm_num)
theorem B5074577 : Blo 2253435 5074577 := bstep (se 2 (by rfl) ⟨1902966, by rfl⟩ : syracuseStep 5074577 = 3805933) B3805933
theorem B3383051 : Blo 2253435 3383051 := bstep (se 1 (by rfl) ⟨2537288, by rfl⟩ : syracuseStep 3383051 = 5074577) B5074577
theorem B2255367 : Blo 2253435 2255367 := bstep (se 1 (by rfl) ⟨1691525, by rfl⟩ : syracuseStep 2255367 = 3383051) B3383051
theorem B2537293 : Blo 2253435 2537293 := bbase (se 3 (by rfl) ⟨475742, by rfl⟩ : syracuseStep 2537293 = 951485) (by norm_num)
theorem B3383057 : Blo 2253435 3383057 := bstep (se 2 (by rfl) ⟨1268646, by rfl⟩ : syracuseStep 3383057 = 2537293) B2537293
theorem B2255371 : Blo 2253435 2255371 := bstep (se 1 (by rfl) ⟨1691528, by rfl⟩ : syracuseStep 2255371 = 3383057) B3383057
theorem B7611893 : Blo 2253435 7611893 := bbase (se 5 (by rfl) ⟨356807, by rfl⟩ : syracuseStep 7611893 = 713615) (by norm_num)
theorem B5074595 : Blo 2253435 5074595 := bstep (se 1 (by rfl) ⟨3805946, by rfl⟩ : syracuseStep 5074595 = 7611893) B7611893
theorem B3383063 : Blo 2253435 3383063 := bstep (se 1 (by rfl) ⟨2537297, by rfl⟩ : syracuseStep 3383063 = 5074595) B5074595
theorem B2255375 : Blo 2253435 2255375 := bstep (se 1 (by rfl) ⟨1691531, by rfl⟩ : syracuseStep 2255375 = 3383063) B3383063
theorem B3383069 : Blo 2253435 3383069 := bbase (se 3 (by rfl) ⟨634325, by rfl⟩ : syracuseStep 3383069 = 1268651) (by norm_num)
theorem B2255379 : Blo 2253435 2255379 := bstep (se 1 (by rfl) ⟨1691534, by rfl⟩ : syracuseStep 2255379 = 3383069) B3383069
theorem B5074613 : Blo 2253435 5074613 := bbase (se 5 (by rfl) ⟨237872, by rfl⟩ : syracuseStep 5074613 = 475745) (by norm_num)
theorem B3383075 : Blo 2253435 3383075 := bstep (se 1 (by rfl) ⟨2537306, by rfl⟩ : syracuseStep 3383075 = 5074613) B5074613
theorem B2255383 : Blo 2253435 2255383 := bstep (se 1 (by rfl) ⟨1691537, by rfl⟩ : syracuseStep 2255383 = 3383075) B3383075
theorem B12845141 : Blo 2253435 12845141 := bbase (se 8 (by rfl) ⟨75264, by rfl⟩ : syracuseStep 12845141 = 150529) (by norm_num)
theorem B8563427 : Blo 2253435 8563427 := bstep (se 1 (by rfl) ⟨6422570, by rfl⟩ : syracuseStep 8563427 = 12845141) B12845141
theorem B5708951 : Blo 2253435 5708951 := bstep (se 1 (by rfl) ⟨4281713, by rfl⟩ : syracuseStep 5708951 = 8563427) B8563427
theorem B3805967 : Blo 2253435 3805967 := bstep (se 1 (by rfl) ⟨2854475, by rfl⟩ : syracuseStep 3805967 = 5708951) B5708951
theorem B2537311 : Blo 2253435 2537311 := bstep (se 1 (by rfl) ⟨1902983, by rfl⟩ : syracuseStep 2537311 = 3805967) B3805967
theorem B3383081 : Blo 2253435 3383081 := bstep (se 2 (by rfl) ⟨1268655, by rfl⟩ : syracuseStep 3383081 = 2537311) B2537311
theorem B2255387 : Blo 2253435 2255387 := bstep (se 1 (by rfl) ⟨1691540, by rfl⟩ : syracuseStep 2255387 = 3383081) B3383081
theorem B6422581 : Blo 2253435 6422581 := bbase (se 5 (by rfl) ⟨301058, by rfl⟩ : syracuseStep 6422581 = 602117) (by norm_num)
theorem B8563441 : Blo 2253435 8563441 := bstep (se 2 (by rfl) ⟨3211290, by rfl⟩ : syracuseStep 8563441 = 6422581) B6422581
theorem B11417921 : Blo 2253435 11417921 := bstep (se 2 (by rfl) ⟨4281720, by rfl⟩ : syracuseStep 11417921 = 8563441) B8563441
theorem B7611947 : Blo 2253435 7611947 := bstep (se 1 (by rfl) ⟨5708960, by rfl⟩ : syracuseStep 7611947 = 11417921) B11417921
theorem B5074631 : Blo 2253435 5074631 := bstep (se 1 (by rfl) ⟨3805973, by rfl⟩ : syracuseStep 5074631 = 7611947) B7611947
theorem B3383087 : Blo 2253435 3383087 := bstep (se 1 (by rfl) ⟨2537315, by rfl⟩ : syracuseStep 3383087 = 5074631) B5074631
theorem B2255391 : Blo 2253435 2255391 := bstep (se 1 (by rfl) ⟨1691543, by rfl⟩ : syracuseStep 2255391 = 3383087) B3383087
theorem B3383093 : Blo 2253435 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B2255395 : Blo 2253435 2255395 := bstep (se 1 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 2255395 = 3383093) B3383093
theorem B5708981 : Blo 2253435 5708981 := bbase (se 5 (by rfl) ⟨267608, by rfl⟩ : syracuseStep 5708981 = 535217) (by norm_num)
theorem B3805987 : Blo 2253435 3805987 := bstep (se 1 (by rfl) ⟨2854490, by rfl⟩ : syracuseStep 3805987 = 5708981) B5708981
theorem B5074649 : Blo 2253435 5074649 := bstep (se 2 (by rfl) ⟨1902993, by rfl⟩ : syracuseStep 5074649 = 3805987) B3805987
theorem B3383099 : Blo 2253435 3383099 := bstep (se 1 (by rfl) ⟨2537324, by rfl⟩ : syracuseStep 3383099 = 5074649) B5074649
theorem B2255399 : Blo 2253435 2255399 := bstep (se 1 (by rfl) ⟨1691549, by rfl⟩ : syracuseStep 2255399 = 3383099) B3383099
theorem B2537329 : Blo 2253435 2537329 := bbase (se 2 (by rfl) ⟨951498, by rfl⟩ : syracuseStep 2537329 = 1902997) (by norm_num)
theorem B3383105 : Blo 2253435 3383105 := bstep (se 2 (by rfl) ⟨1268664, by rfl⟩ : syracuseStep 3383105 = 2537329) B2537329
theorem B2255403 : Blo 2253435 2255403 := bstep (se 1 (by rfl) ⟨1691552, by rfl⟩ : syracuseStep 2255403 = 3383105) B3383105
theorem B9633941 : Blo 2253435 9633941 := bbase (se 6 (by rfl) ⟨225795, by rfl⟩ : syracuseStep 9633941 = 451591) (by norm_num)
theorem B6422627 : Blo 2253435 6422627 := bstep (se 1 (by rfl) ⟨4816970, by rfl⟩ : syracuseStep 6422627 = 9633941) B9633941
theorem B4281751 : Blo 2253435 4281751 := bstep (se 1 (by rfl) ⟨3211313, by rfl⟩ : syracuseStep 4281751 = 6422627) B6422627
theorem B5709001 : Blo 2253435 5709001 := bstep (se 2 (by rfl) ⟨2140875, by rfl⟩ : syracuseStep 5709001 = 4281751) B4281751
theorem B7612001 : Blo 2253435 7612001 := bstep (se 2 (by rfl) ⟨2854500, by rfl⟩ : syracuseStep 7612001 = 5709001) B5709001
theorem B5074667 : Blo 2253435 5074667 := bstep (se 1 (by rfl) ⟨3806000, by rfl⟩ : syracuseStep 5074667 = 7612001) B7612001
theorem B3383111 : Blo 2253435 3383111 := bstep (se 1 (by rfl) ⟨2537333, by rfl⟩ : syracuseStep 3383111 = 5074667) B5074667
theorem B2255407 : Blo 2253435 2255407 := bstep (se 1 (by rfl) ⟨1691555, by rfl⟩ : syracuseStep 2255407 = 3383111) B3383111
theorem B3383117 : Blo 2253435 3383117 := bbase (se 3 (by rfl) ⟨634334, by rfl⟩ : syracuseStep 3383117 = 1268669) (by norm_num)
theorem B2255411 : Blo 2253435 2255411 := bstep (se 1 (by rfl) ⟨1691558, by rfl⟩ : syracuseStep 2255411 = 3383117) B3383117
theorem B5074685 : Blo 2253435 5074685 := bbase (se 3 (by rfl) ⟨951503, by rfl⟩ : syracuseStep 5074685 = 1903007) (by norm_num)
theorem B3383123 : Blo 2253435 3383123 := bstep (se 1 (by rfl) ⟨2537342, by rfl⟩ : syracuseStep 3383123 = 5074685) B5074685
theorem B2255415 : Blo 2253435 2255415 := bstep (se 1 (by rfl) ⟨1691561, by rfl⟩ : syracuseStep 2255415 = 3383123) B3383123
theorem B3806021 : Blo 2253435 3806021 := bbase (se 4 (by rfl) ⟨356814, by rfl⟩ : syracuseStep 3806021 = 713629) (by norm_num)
theorem B2537347 : Blo 2253435 2537347 := bstep (se 1 (by rfl) ⟨1903010, by rfl⟩ : syracuseStep 2537347 = 3806021) B3806021
theorem B3383129 : Blo 2253435 3383129 := bstep (se 2 (by rfl) ⟨1268673, by rfl⟩ : syracuseStep 3383129 = 2537347) B2537347
theorem B2255419 : Blo 2253435 2255419 := bstep (se 1 (by rfl) ⟨1691564, by rfl⟩ : syracuseStep 2255419 = 3383129) B3383129
theorem B17127125 : Blo 2253435 17127125 := bbase (se 7 (by rfl) ⟨200708, by rfl⟩ : syracuseStep 17127125 = 401417) (by norm_num)
theorem B11418083 : Blo 2253435 11418083 := bstep (se 1 (by rfl) ⟨8563562, by rfl⟩ : syracuseStep 11418083 = 17127125) B17127125
theorem B7612055 : Blo 2253435 7612055 := bstep (se 1 (by rfl) ⟨5709041, by rfl⟩ : syracuseStep 7612055 = 11418083) B11418083
theorem B5074703 : Blo 2253435 5074703 := bstep (se 1 (by rfl) ⟨3806027, by rfl⟩ : syracuseStep 5074703 = 7612055) B7612055
theorem B3383135 : Blo 2253435 3383135 := bstep (se 1 (by rfl) ⟨2537351, by rfl⟩ : syracuseStep 3383135 = 5074703) B5074703
theorem B2255423 : Blo 2253435 2255423 := bstep (se 1 (by rfl) ⟨1691567, by rfl⟩ : syracuseStep 2255423 = 3383135) B3383135
theorem B3383141 : Blo 2253435 3383141 := bbase (se 4 (by rfl) ⟨317169, by rfl⟩ : syracuseStep 3383141 = 634339) (by norm_num)
theorem B2255427 : Blo 2253435 2255427 := bstep (se 1 (by rfl) ⟨1691570, by rfl⟩ : syracuseStep 2255427 = 3383141) B3383141
theorem B4281797 : Blo 2253435 4281797 := bbase (se 4 (by rfl) ⟨401418, by rfl⟩ : syracuseStep 4281797 = 802837) (by norm_num)
theorem B2854531 : Blo 2253435 2854531 := bstep (se 1 (by rfl) ⟨2140898, by rfl⟩ : syracuseStep 2854531 = 4281797) B4281797
theorem B3806041 : Blo 2253435 3806041 := bstep (se 2 (by rfl) ⟨1427265, by rfl⟩ : syracuseStep 3806041 = 2854531) B2854531
theorem B5074721 : Blo 2253435 5074721 := bstep (se 2 (by rfl) ⟨1903020, by rfl⟩ : syracuseStep 5074721 = 3806041) B3806041
theorem B3383147 : Blo 2253435 3383147 := bstep (se 1 (by rfl) ⟨2537360, by rfl⟩ : syracuseStep 3383147 = 5074721) B5074721
theorem B2255431 : Blo 2253435 2255431 := bstep (se 1 (by rfl) ⟨1691573, by rfl⟩ : syracuseStep 2255431 = 3383147) B3383147
theorem B2537365 : Blo 2253435 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B3383153 : Blo 2253435 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B2255435 : Blo 2253435 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem C0 (j : ℕ) (h1 : 563358 ≤ j) (h2 : j ≤ 563858) : Blo 2253435 (4 * j + 3) := by
  interval_cases j
  · exact B2253435
  · exact B2253439
  · exact B2253443
  · exact B2253447
  · exact B2253451
  · exact B2253455
  · exact B2253459
  · exact B2253463
  · exact B2253467
  · exact B2253471
  · exact B2253475
  · exact B2253479
  · exact B2253483
  · exact B2253487
  · exact B2253491
  · exact B2253495
  · exact B2253499
  · exact B2253503
  · exact B2253507
  · exact B2253511
  · exact B2253515
  · exact B2253519
  · exact B2253523
  · exact B2253527
  · exact B2253531
  · exact B2253535
  · exact B2253539
  · exact B2253543
  · exact B2253547
  · exact B2253551
  · exact B2253555
  · exact B2253559
  · exact B2253563
  · exact B2253567
  · exact B2253571
  · exact B2253575
  · exact B2253579
  · exact B2253583
  · exact B2253587
  · exact B2253591
  · exact B2253595
  · exact B2253599
  · exact B2253603
  · exact B2253607
  · exact B2253611
  · exact B2253615
  · exact B2253619
  · exact B2253623
  · exact B2253627
  · exact B2253631
  · exact B2253635
  · exact B2253639
  · exact B2253643
  · exact B2253647
  · exact B2253651
  · exact B2253655
  · exact B2253659
  · exact B2253663
  · exact B2253667
  · exact B2253671
  · exact B2253675
  · exact B2253679
  · exact B2253683
  · exact B2253687
  · exact B2253691
  · exact B2253695
  · exact B2253699
  · exact B2253703
  · exact B2253707
  · exact B2253711
  · exact B2253715
  · exact B2253719
  · exact B2253723
  · exact B2253727
  · exact B2253731
  · exact B2253735
  · exact B2253739
  · exact B2253743
  · exact B2253747
  · exact B2253751
  · exact B2253755
  · exact B2253759
  · exact B2253763
  · exact B2253767
  · exact B2253771
  · exact B2253775
  · exact B2253779
  · exact B2253783
  · exact B2253787
  · exact B2253791
  · exact B2253795
  · exact B2253799
  · exact B2253803
  · exact B2253807
  · exact B2253811
  · exact B2253815
  · exact B2253819
  · exact B2253823
  · exact B2253827
  · exact B2253831
  · exact B2253835
  · exact B2253839
  · exact B2253843
  · exact B2253847
  · exact B2253851
  · exact B2253855
  · exact B2253859
  · exact B2253863
  · exact B2253867
  · exact B2253871
  · exact B2253875
  · exact B2253879
  · exact B2253883
  · exact B2253887
  · exact B2253891
  · exact B2253895
  · exact B2253899
  · exact B2253903
  · exact B2253907
  · exact B2253911
  · exact B2253915
  · exact B2253919
  · exact B2253923
  · exact B2253927
  · exact B2253931
  · exact B2253935
  · exact B2253939
  · exact B2253943
  · exact B2253947
  · exact B2253951
  · exact B2253955
  · exact B2253959
  · exact B2253963
  · exact B2253967
  · exact B2253971
  · exact B2253975
  · exact B2253979
  · exact B2253983
  · exact B2253987
  · exact B2253991
  · exact B2253995
  · exact B2253999
  · exact B2254003
  · exact B2254007
  · exact B2254011
  · exact B2254015
  · exact B2254019
  · exact B2254023
  · exact B2254027
  · exact B2254031
  · exact B2254035
  · exact B2254039
  · exact B2254043
  · exact B2254047
  · exact B2254051
  · exact B2254055
  · exact B2254059
  · exact B2254063
  · exact B2254067
  · exact B2254071
  · exact B2254075
  · exact B2254079
  · exact B2254083
  · exact B2254087
  · exact B2254091
  · exact B2254095
  · exact B2254099
  · exact B2254103
  · exact B2254107
  · exact B2254111
  · exact B2254115
  · exact B2254119
  · exact B2254123
  · exact B2254127
  · exact B2254131
  · exact B2254135
  · exact B2254139
  · exact B2254143
  · exact B2254147
  · exact B2254151
  · exact B2254155
  · exact B2254159
  · exact B2254163
  · exact B2254167
  · exact B2254171
  · exact B2254175
  · exact B2254179
  · exact B2254183
  · exact B2254187
  · exact B2254191
  · exact B2254195
  · exact B2254199
  · exact B2254203
  · exact B2254207
  · exact B2254211
  · exact B2254215
  · exact B2254219
  · exact B2254223
  · exact B2254227
  · exact B2254231
  · exact B2254235
  · exact B2254239
  · exact B2254243
  · exact B2254247
  · exact B2254251
  · exact B2254255
  · exact B2254259
  · exact B2254263
  · exact B2254267
  · exact B2254271
  · exact B2254275
  · exact B2254279
  · exact B2254283
  · exact B2254287
  · exact B2254291
  · exact B2254295
  · exact B2254299
  · exact B2254303
  · exact B2254307
  · exact B2254311
  · exact B2254315
  · exact B2254319
  · exact B2254323
  · exact B2254327
  · exact B2254331
  · exact B2254335
  · exact B2254339
  · exact B2254343
  · exact B2254347
  · exact B2254351
  · exact B2254355
  · exact B2254359
  · exact B2254363
  · exact B2254367
  · exact B2254371
  · exact B2254375
  · exact B2254379
  · exact B2254383
  · exact B2254387
  · exact B2254391
  · exact B2254395
  · exact B2254399
  · exact B2254403
  · exact B2254407
  · exact B2254411
  · exact B2254415
  · exact B2254419
  · exact B2254423
  · exact B2254427
  · exact B2254431
  · exact B2254435
  · exact B2254439
  · exact B2254443
  · exact B2254447
  · exact B2254451
  · exact B2254455
  · exact B2254459
  · exact B2254463
  · exact B2254467
  · exact B2254471
  · exact B2254475
  · exact B2254479
  · exact B2254483
  · exact B2254487
  · exact B2254491
  · exact B2254495
  · exact B2254499
  · exact B2254503
  · exact B2254507
  · exact B2254511
  · exact B2254515
  · exact B2254519
  · exact B2254523
  · exact B2254527
  · exact B2254531
  · exact B2254535
  · exact B2254539
  · exact B2254543
  · exact B2254547
  · exact B2254551
  · exact B2254555
  · exact B2254559
  · exact B2254563
  · exact B2254567
  · exact B2254571
  · exact B2254575
  · exact B2254579
  · exact B2254583
  · exact B2254587
  · exact B2254591
  · exact B2254595
  · exact B2254599
  · exact B2254603
  · exact B2254607
  · exact B2254611
  · exact B2254615
  · exact B2254619
  · exact B2254623
  · exact B2254627
  · exact B2254631
  · exact B2254635
  · exact B2254639
  · exact B2254643
  · exact B2254647
  · exact B2254651
  · exact B2254655
  · exact B2254659
  · exact B2254663
  · exact B2254667
  · exact B2254671
  · exact B2254675
  · exact B2254679
  · exact B2254683
  · exact B2254687
  · exact B2254691
  · exact B2254695
  · exact B2254699
  · exact B2254703
  · exact B2254707
  · exact B2254711
  · exact B2254715
  · exact B2254719
  · exact B2254723
  · exact B2254727
  · exact B2254731
  · exact B2254735
  · exact B2254739
  · exact B2254743
  · exact B2254747
  · exact B2254751
  · exact B2254755
  · exact B2254759
  · exact B2254763
  · exact B2254767
  · exact B2254771
  · exact B2254775
  · exact B2254779
  · exact B2254783
  · exact B2254787
  · exact B2254791
  · exact B2254795
  · exact B2254799
  · exact B2254803
  · exact B2254807
  · exact B2254811
  · exact B2254815
  · exact B2254819
  · exact B2254823
  · exact B2254827
  · exact B2254831
  · exact B2254835
  · exact B2254839
  · exact B2254843
  · exact B2254847
  · exact B2254851
  · exact B2254855
  · exact B2254859
  · exact B2254863
  · exact B2254867
  · exact B2254871
  · exact B2254875
  · exact B2254879
  · exact B2254883
  · exact B2254887
  · exact B2254891
  · exact B2254895
  · exact B2254899
  · exact B2254903
  · exact B2254907
  · exact B2254911
  · exact B2254915
  · exact B2254919
  · exact B2254923
  · exact B2254927
  · exact B2254931
  · exact B2254935
  · exact B2254939
  · exact B2254943
  · exact B2254947
  · exact B2254951
  · exact B2254955
  · exact B2254959
  · exact B2254963
  · exact B2254967
  · exact B2254971
  · exact B2254975
  · exact B2254979
  · exact B2254983
  · exact B2254987
  · exact B2254991
  · exact B2254995
  · exact B2254999
  · exact B2255003
  · exact B2255007
  · exact B2255011
  · exact B2255015
  · exact B2255019
  · exact B2255023
  · exact B2255027
  · exact B2255031
  · exact B2255035
  · exact B2255039
  · exact B2255043
  · exact B2255047
  · exact B2255051
  · exact B2255055
  · exact B2255059
  · exact B2255063
  · exact B2255067
  · exact B2255071
  · exact B2255075
  · exact B2255079
  · exact B2255083
  · exact B2255087
  · exact B2255091
  · exact B2255095
  · exact B2255099
  · exact B2255103
  · exact B2255107
  · exact B2255111
  · exact B2255115
  · exact B2255119
  · exact B2255123
  · exact B2255127
  · exact B2255131
  · exact B2255135
  · exact B2255139
  · exact B2255143
  · exact B2255147
  · exact B2255151
  · exact B2255155
  · exact B2255159
  · exact B2255163
  · exact B2255167
  · exact B2255171
  · exact B2255175
  · exact B2255179
  · exact B2255183
  · exact B2255187
  · exact B2255191
  · exact B2255195
  · exact B2255199
  · exact B2255203
  · exact B2255207
  · exact B2255211
  · exact B2255215
  · exact B2255219
  · exact B2255223
  · exact B2255227
  · exact B2255231
  · exact B2255235
  · exact B2255239
  · exact B2255243
  · exact B2255247
  · exact B2255251
  · exact B2255255
  · exact B2255259
  · exact B2255263
  · exact B2255267
  · exact B2255271
  · exact B2255275
  · exact B2255279
  · exact B2255283
  · exact B2255287
  · exact B2255291
  · exact B2255295
  · exact B2255299
  · exact B2255303
  · exact B2255307
  · exact B2255311
  · exact B2255315
  · exact B2255319
  · exact B2255323
  · exact B2255327
  · exact B2255331
  · exact B2255335
  · exact B2255339
  · exact B2255343
  · exact B2255347
  · exact B2255351
  · exact B2255355
  · exact B2255359
  · exact B2255363
  · exact B2255367
  · exact B2255371
  · exact B2255375
  · exact B2255379
  · exact B2255383
  · exact B2255387
  · exact B2255391
  · exact B2255395
  · exact B2255399
  · exact B2255403
  · exact B2255407
  · exact B2255411
  · exact B2255415
  · exact B2255419
  · exact B2255423
  · exact B2255427
  · exact B2255431
  · exact B2255435
theorem solution (m : ℕ) (hlo : 2253435 ≤ m) (hhi : m ≤ 2255435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 563358 ≤ j := by omega
    have hj2 : j ≤ 563858 := by omega
    have hb : Blo 2253435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
