-- Prove2me | solution 1 for syracuse_descends_range_2021435_2023435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:52.461291+00:00
-- url     : https://prove2.me/submissions/415f8faa-bf2d-4c9c-bc2a-7fa03f2146b5

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

theorem B3411173 : Blo 2021435 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B2274115 : Blo 2021435 2274115 := bstep (se 1 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 2274115 = 3411173) B3411173
theorem B3032153 : Blo 2021435 3032153 := bstep (se 2 (by rfl) ⟨1137057, by rfl⟩ : syracuseStep 3032153 = 2274115) B2274115
theorem B2021435 : Blo 2021435 2021435 := bstep (se 1 (by rfl) ⟨1516076, by rfl⟩ : syracuseStep 2021435 = 3032153) B3032153
theorem B8752357 : Blo 2021435 8752357 := bbase (se 4 (by rfl) ⟨820533, by rfl⟩ : syracuseStep 8752357 = 1641067) (by norm_num)
theorem B46679237 : Blo 2021435 46679237 := bstep (se 4 (by rfl) ⟨4376178, by rfl⟩ : syracuseStep 46679237 = 8752357) B8752357
theorem B31119491 : Blo 2021435 31119491 := bstep (se 1 (by rfl) ⟨23339618, by rfl⟩ : syracuseStep 31119491 = 46679237) B46679237
theorem B20746327 : Blo 2021435 20746327 := bstep (se 1 (by rfl) ⟨15559745, by rfl⟩ : syracuseStep 20746327 = 31119491) B31119491
theorem B27661769 : Blo 2021435 27661769 := bstep (se 2 (by rfl) ⟨10373163, by rfl⟩ : syracuseStep 27661769 = 20746327) B20746327
theorem B18441179 : Blo 2021435 18441179 := bstep (se 1 (by rfl) ⟨13830884, by rfl⟩ : syracuseStep 18441179 = 27661769) B27661769
theorem B12294119 : Blo 2021435 12294119 := bstep (se 1 (by rfl) ⟨9220589, by rfl⟩ : syracuseStep 12294119 = 18441179) B18441179
theorem B8196079 : Blo 2021435 8196079 := bstep (se 1 (by rfl) ⟨6147059, by rfl⟩ : syracuseStep 8196079 = 12294119) B12294119
theorem B10928105 : Blo 2021435 10928105 := bstep (se 2 (by rfl) ⟨4098039, by rfl⟩ : syracuseStep 10928105 = 8196079) B8196079
theorem B7285403 : Blo 2021435 7285403 := bstep (se 1 (by rfl) ⟨5464052, by rfl⟩ : syracuseStep 7285403 = 10928105) B10928105
theorem B4856935 : Blo 2021435 4856935 := bstep (se 1 (by rfl) ⟨3642701, by rfl⟩ : syracuseStep 4856935 = 7285403) B7285403
theorem B6475913 : Blo 2021435 6475913 := bstep (se 2 (by rfl) ⟨2428467, by rfl⟩ : syracuseStep 6475913 = 4856935) B4856935
theorem B4317275 : Blo 2021435 4317275 := bstep (se 1 (by rfl) ⟨3237956, by rfl⟩ : syracuseStep 4317275 = 6475913) B6475913
theorem B2878183 : Blo 2021435 2878183 := bstep (se 1 (by rfl) ⟨2158637, by rfl⟩ : syracuseStep 2878183 = 4317275) B4317275
theorem B15350309 : Blo 2021435 15350309 := bstep (se 4 (by rfl) ⟨1439091, by rfl⟩ : syracuseStep 15350309 = 2878183) B2878183
theorem B10233539 : Blo 2021435 10233539 := bstep (se 1 (by rfl) ⟨7675154, by rfl⟩ : syracuseStep 10233539 = 15350309) B15350309
theorem B6822359 : Blo 2021435 6822359 := bstep (se 1 (by rfl) ⟨5116769, by rfl⟩ : syracuseStep 6822359 = 10233539) B10233539
theorem B4548239 : Blo 2021435 4548239 := bstep (se 1 (by rfl) ⟨3411179, by rfl⟩ : syracuseStep 4548239 = 6822359) B6822359
theorem B3032159 : Blo 2021435 3032159 := bstep (se 1 (by rfl) ⟨2274119, by rfl⟩ : syracuseStep 3032159 = 4548239) B4548239
theorem B2021439 : Blo 2021435 2021439 := bstep (se 1 (by rfl) ⟨1516079, by rfl⟩ : syracuseStep 2021439 = 3032159) B3032159
theorem B3032165 : Blo 2021435 3032165 := bbase (se 4 (by rfl) ⟨284265, by rfl⟩ : syracuseStep 3032165 = 568531) (by norm_num)
theorem B2021443 : Blo 2021435 2021443 := bstep (se 1 (by rfl) ⟨1516082, by rfl⟩ : syracuseStep 2021443 = 3032165) B3032165
theorem B4317293 : Blo 2021435 4317293 := bbase (se 3 (by rfl) ⟨809492, by rfl⟩ : syracuseStep 4317293 = 1618985) (by norm_num)
theorem B2878195 : Blo 2021435 2878195 := bstep (se 1 (by rfl) ⟨2158646, by rfl⟩ : syracuseStep 2878195 = 4317293) B4317293
theorem B3837593 : Blo 2021435 3837593 := bstep (se 2 (by rfl) ⟨1439097, by rfl⟩ : syracuseStep 3837593 = 2878195) B2878195
theorem B2558395 : Blo 2021435 2558395 := bstep (se 1 (by rfl) ⟨1918796, by rfl⟩ : syracuseStep 2558395 = 3837593) B3837593
theorem B3411193 : Blo 2021435 3411193 := bstep (se 2 (by rfl) ⟨1279197, by rfl⟩ : syracuseStep 3411193 = 2558395) B2558395
theorem B4548257 : Blo 2021435 4548257 := bstep (se 2 (by rfl) ⟨1705596, by rfl⟩ : syracuseStep 4548257 = 3411193) B3411193
theorem B3032171 : Blo 2021435 3032171 := bstep (se 1 (by rfl) ⟨2274128, by rfl⟩ : syracuseStep 3032171 = 4548257) B4548257
theorem B2021447 : Blo 2021435 2021447 := bstep (se 1 (by rfl) ⟨1516085, by rfl⟩ : syracuseStep 2021447 = 3032171) B3032171
theorem B2274133 : Blo 2021435 2274133 := bbase (se 9 (by rfl) ⟨6662, by rfl⟩ : syracuseStep 2274133 = 13325) (by norm_num)
theorem B3032177 : Blo 2021435 3032177 := bstep (se 2 (by rfl) ⟨1137066, by rfl⟩ : syracuseStep 3032177 = 2274133) B2274133
theorem B2021451 : Blo 2021435 2021451 := bstep (se 1 (by rfl) ⟨1516088, by rfl⟩ : syracuseStep 2021451 = 3032177) B3032177
theorem B2558405 : Blo 2021435 2558405 := bbase (se 4 (by rfl) ⟨239850, by rfl⟩ : syracuseStep 2558405 = 479701) (by norm_num)
theorem B6822413 : Blo 2021435 6822413 := bstep (se 3 (by rfl) ⟨1279202, by rfl⟩ : syracuseStep 6822413 = 2558405) B2558405
theorem B4548275 : Blo 2021435 4548275 := bstep (se 1 (by rfl) ⟨3411206, by rfl⟩ : syracuseStep 4548275 = 6822413) B6822413
theorem B3032183 : Blo 2021435 3032183 := bstep (se 1 (by rfl) ⟨2274137, by rfl⟩ : syracuseStep 3032183 = 4548275) B4548275
theorem B2021455 : Blo 2021435 2021455 := bstep (se 1 (by rfl) ⟨1516091, by rfl⟩ : syracuseStep 2021455 = 3032183) B3032183
theorem B3032189 : Blo 2021435 3032189 := bbase (se 3 (by rfl) ⟨568535, by rfl⟩ : syracuseStep 3032189 = 1137071) (by norm_num)
theorem B2021459 : Blo 2021435 2021459 := bstep (se 1 (by rfl) ⟨1516094, by rfl⟩ : syracuseStep 2021459 = 3032189) B3032189
theorem B4548293 : Blo 2021435 4548293 := bbase (se 4 (by rfl) ⟨426402, by rfl⟩ : syracuseStep 4548293 = 852805) (by norm_num)
theorem B3032195 : Blo 2021435 3032195 := bstep (se 1 (by rfl) ⟨2274146, by rfl⟩ : syracuseStep 3032195 = 4548293) B4548293
theorem B2021463 : Blo 2021435 2021463 := bstep (se 1 (by rfl) ⟨1516097, by rfl⟩ : syracuseStep 2021463 = 3032195) B3032195
theorem B8308021 : Blo 2021435 8308021 := bbase (se 5 (by rfl) ⟨389438, by rfl⟩ : syracuseStep 8308021 = 778877) (by norm_num)
theorem B11077361 : Blo 2021435 11077361 := bstep (se 2 (by rfl) ⟨4154010, by rfl⟩ : syracuseStep 11077361 = 8308021) B8308021
theorem B7384907 : Blo 2021435 7384907 := bstep (se 1 (by rfl) ⟨5538680, by rfl⟩ : syracuseStep 7384907 = 11077361) B11077361
theorem B4923271 : Blo 2021435 4923271 := bstep (se 1 (by rfl) ⟨3692453, by rfl⟩ : syracuseStep 4923271 = 7384907) B7384907
theorem B6564361 : Blo 2021435 6564361 := bstep (se 2 (by rfl) ⟨2461635, by rfl⟩ : syracuseStep 6564361 = 4923271) B4923271
theorem B8752481 : Blo 2021435 8752481 := bstep (se 2 (by rfl) ⟨3282180, by rfl⟩ : syracuseStep 8752481 = 6564361) B6564361
theorem B5834987 : Blo 2021435 5834987 := bstep (se 1 (by rfl) ⟨4376240, by rfl⟩ : syracuseStep 5834987 = 8752481) B8752481
theorem B3889991 : Blo 2021435 3889991 := bstep (se 1 (by rfl) ⟨2917493, by rfl⟩ : syracuseStep 3889991 = 5834987) B5834987
theorem B2593327 : Blo 2021435 2593327 := bstep (se 1 (by rfl) ⟨1944995, by rfl⟩ : syracuseStep 2593327 = 3889991) B3889991
theorem B3457769 : Blo 2021435 3457769 := bstep (se 2 (by rfl) ⟨1296663, by rfl⟩ : syracuseStep 3457769 = 2593327) B2593327
theorem B9220717 : Blo 2021435 9220717 := bstep (se 3 (by rfl) ⟨1728884, by rfl⟩ : syracuseStep 9220717 = 3457769) B3457769
theorem B12294289 : Blo 2021435 12294289 := bstep (se 2 (by rfl) ⟨4610358, by rfl⟩ : syracuseStep 12294289 = 9220717) B9220717
theorem B16392385 : Blo 2021435 16392385 := bstep (se 2 (by rfl) ⟨6147144, by rfl⟩ : syracuseStep 16392385 = 12294289) B12294289
theorem B21856513 : Blo 2021435 21856513 := bstep (se 2 (by rfl) ⟨8196192, by rfl⟩ : syracuseStep 21856513 = 16392385) B16392385
theorem B29142017 : Blo 2021435 29142017 := bstep (se 2 (by rfl) ⟨10928256, by rfl⟩ : syracuseStep 29142017 = 21856513) B21856513
theorem B19428011 : Blo 2021435 19428011 := bstep (se 1 (by rfl) ⟨14571008, by rfl⟩ : syracuseStep 19428011 = 29142017) B29142017
theorem B12952007 : Blo 2021435 12952007 := bstep (se 1 (by rfl) ⟨9714005, by rfl⟩ : syracuseStep 12952007 = 19428011) B19428011
theorem B8634671 : Blo 2021435 8634671 := bstep (se 1 (by rfl) ⟨6476003, by rfl⟩ : syracuseStep 8634671 = 12952007) B12952007
theorem B5756447 : Blo 2021435 5756447 := bstep (se 1 (by rfl) ⟨4317335, by rfl⟩ : syracuseStep 5756447 = 8634671) B8634671
theorem B3837631 : Blo 2021435 3837631 := bstep (se 1 (by rfl) ⟨2878223, by rfl⟩ : syracuseStep 3837631 = 5756447) B5756447
theorem B5116841 : Blo 2021435 5116841 := bstep (se 2 (by rfl) ⟨1918815, by rfl⟩ : syracuseStep 5116841 = 3837631) B3837631
theorem B3411227 : Blo 2021435 3411227 := bstep (se 1 (by rfl) ⟨2558420, by rfl⟩ : syracuseStep 3411227 = 5116841) B5116841
theorem B2274151 : Blo 2021435 2274151 := bstep (se 1 (by rfl) ⟨1705613, by rfl⟩ : syracuseStep 2274151 = 3411227) B3411227
theorem B3032201 : Blo 2021435 3032201 := bstep (se 2 (by rfl) ⟨1137075, by rfl⟩ : syracuseStep 3032201 = 2274151) B2274151
theorem B2021467 : Blo 2021435 2021467 := bstep (se 1 (by rfl) ⟨1516100, by rfl⟩ : syracuseStep 2021467 = 3032201) B3032201
theorem B10233701 : Blo 2021435 10233701 := bbase (se 4 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 10233701 = 1918819) (by norm_num)
theorem B6822467 : Blo 2021435 6822467 := bstep (se 1 (by rfl) ⟨5116850, by rfl⟩ : syracuseStep 6822467 = 10233701) B10233701
theorem B4548311 : Blo 2021435 4548311 := bstep (se 1 (by rfl) ⟨3411233, by rfl⟩ : syracuseStep 4548311 = 6822467) B6822467
theorem B3032207 : Blo 2021435 3032207 := bstep (se 1 (by rfl) ⟨2274155, by rfl⟩ : syracuseStep 3032207 = 4548311) B4548311
theorem B2021471 : Blo 2021435 2021471 := bstep (se 1 (by rfl) ⟨1516103, by rfl⟩ : syracuseStep 2021471 = 3032207) B3032207
theorem B3032213 : Blo 2021435 3032213 := bbase (se 6 (by rfl) ⟨71067, by rfl⟩ : syracuseStep 3032213 = 142135) (by norm_num)
theorem B2021475 : Blo 2021435 2021475 := bstep (se 1 (by rfl) ⟨1516106, by rfl⟩ : syracuseStep 2021475 = 3032213) B3032213
theorem B2305193 : Blo 2021435 2305193 := bbase (se 2 (by rfl) ⟨864447, by rfl⟩ : syracuseStep 2305193 = 1728895) (by norm_num)
theorem B6147181 : Blo 2021435 6147181 := bstep (se 3 (by rfl) ⟨1152596, by rfl⟩ : syracuseStep 6147181 = 2305193) B2305193
theorem B8196241 : Blo 2021435 8196241 := bstep (se 2 (by rfl) ⟨3073590, by rfl⟩ : syracuseStep 8196241 = 6147181) B6147181
theorem B10928321 : Blo 2021435 10928321 := bstep (se 2 (by rfl) ⟨4098120, by rfl⟩ : syracuseStep 10928321 = 8196241) B8196241
theorem B7285547 : Blo 2021435 7285547 := bstep (se 1 (by rfl) ⟨5464160, by rfl⟩ : syracuseStep 7285547 = 10928321) B10928321
theorem B4857031 : Blo 2021435 4857031 := bstep (se 1 (by rfl) ⟨3642773, by rfl⟩ : syracuseStep 4857031 = 7285547) B7285547
theorem B6476041 : Blo 2021435 6476041 := bstep (se 2 (by rfl) ⟨2428515, by rfl⟩ : syracuseStep 6476041 = 4857031) B4857031
theorem B8634721 : Blo 2021435 8634721 := bstep (se 2 (by rfl) ⟨3238020, by rfl⟩ : syracuseStep 8634721 = 6476041) B6476041
theorem B11512961 : Blo 2021435 11512961 := bstep (se 2 (by rfl) ⟨4317360, by rfl⟩ : syracuseStep 11512961 = 8634721) B8634721
theorem B7675307 : Blo 2021435 7675307 := bstep (se 1 (by rfl) ⟨5756480, by rfl⟩ : syracuseStep 7675307 = 11512961) B11512961
theorem B5116871 : Blo 2021435 5116871 := bstep (se 1 (by rfl) ⟨3837653, by rfl⟩ : syracuseStep 5116871 = 7675307) B7675307
theorem B3411247 : Blo 2021435 3411247 := bstep (se 1 (by rfl) ⟨2558435, by rfl⟩ : syracuseStep 3411247 = 5116871) B5116871
theorem B4548329 : Blo 2021435 4548329 := bstep (se 2 (by rfl) ⟨1705623, by rfl⟩ : syracuseStep 4548329 = 3411247) B3411247
theorem B3032219 : Blo 2021435 3032219 := bstep (se 1 (by rfl) ⟨2274164, by rfl⟩ : syracuseStep 3032219 = 4548329) B4548329
theorem B2021479 : Blo 2021435 2021479 := bstep (se 1 (by rfl) ⟨1516109, by rfl⟩ : syracuseStep 2021479 = 3032219) B3032219
theorem B2274169 : Blo 2021435 2274169 := bbase (se 2 (by rfl) ⟨852813, by rfl⟩ : syracuseStep 2274169 = 1705627) (by norm_num)
theorem B3032225 : Blo 2021435 3032225 := bstep (se 2 (by rfl) ⟨1137084, by rfl⟩ : syracuseStep 3032225 = 2274169) B2274169
theorem B2021483 : Blo 2021435 2021483 := bstep (se 1 (by rfl) ⟨1516112, by rfl⟩ : syracuseStep 2021483 = 3032225) B3032225
theorem B2428525 : Blo 2021435 2428525 := bbase (se 3 (by rfl) ⟨455348, by rfl⟩ : syracuseStep 2428525 = 910697) (by norm_num)
theorem B12952133 : Blo 2021435 12952133 := bstep (se 4 (by rfl) ⟨1214262, by rfl⟩ : syracuseStep 12952133 = 2428525) B2428525
theorem B8634755 : Blo 2021435 8634755 := bstep (se 1 (by rfl) ⟨6476066, by rfl⟩ : syracuseStep 8634755 = 12952133) B12952133
theorem B5756503 : Blo 2021435 5756503 := bstep (se 1 (by rfl) ⟨4317377, by rfl⟩ : syracuseStep 5756503 = 8634755) B8634755
theorem B7675337 : Blo 2021435 7675337 := bstep (se 2 (by rfl) ⟨2878251, by rfl⟩ : syracuseStep 7675337 = 5756503) B5756503
theorem B5116891 : Blo 2021435 5116891 := bstep (se 1 (by rfl) ⟨3837668, by rfl⟩ : syracuseStep 5116891 = 7675337) B7675337
theorem B6822521 : Blo 2021435 6822521 := bstep (se 2 (by rfl) ⟨2558445, by rfl⟩ : syracuseStep 6822521 = 5116891) B5116891
theorem B4548347 : Blo 2021435 4548347 := bstep (se 1 (by rfl) ⟨3411260, by rfl⟩ : syracuseStep 4548347 = 6822521) B6822521
theorem B3032231 : Blo 2021435 3032231 := bstep (se 1 (by rfl) ⟨2274173, by rfl⟩ : syracuseStep 3032231 = 4548347) B4548347
theorem B2021487 : Blo 2021435 2021487 := bstep (se 1 (by rfl) ⟨1516115, by rfl⟩ : syracuseStep 2021487 = 3032231) B3032231
theorem B3032237 : Blo 2021435 3032237 := bbase (se 3 (by rfl) ⟨568544, by rfl⟩ : syracuseStep 3032237 = 1137089) (by norm_num)
theorem B2021491 : Blo 2021435 2021491 := bstep (se 1 (by rfl) ⟨1516118, by rfl⟩ : syracuseStep 2021491 = 3032237) B3032237
theorem B4548365 : Blo 2021435 4548365 := bbase (se 3 (by rfl) ⟨852818, by rfl⟩ : syracuseStep 4548365 = 1705637) (by norm_num)
theorem B3032243 : Blo 2021435 3032243 := bstep (se 1 (by rfl) ⟨2274182, by rfl⟩ : syracuseStep 3032243 = 4548365) B4548365
theorem B2021495 : Blo 2021435 2021495 := bstep (se 1 (by rfl) ⟨1516121, by rfl⟩ : syracuseStep 2021495 = 3032243) B3032243
theorem B2558461 : Blo 2021435 2558461 := bbase (se 3 (by rfl) ⟨479711, by rfl⟩ : syracuseStep 2558461 = 959423) (by norm_num)
theorem B3411281 : Blo 2021435 3411281 := bstep (se 2 (by rfl) ⟨1279230, by rfl⟩ : syracuseStep 3411281 = 2558461) B2558461
theorem B2274187 : Blo 2021435 2274187 := bstep (se 1 (by rfl) ⟨1705640, by rfl⟩ : syracuseStep 2274187 = 3411281) B3411281
theorem B3032249 : Blo 2021435 3032249 := bstep (se 2 (by rfl) ⟨1137093, by rfl⟩ : syracuseStep 3032249 = 2274187) B2274187
theorem B2021499 : Blo 2021435 2021499 := bstep (se 1 (by rfl) ⟨1516124, by rfl⟩ : syracuseStep 2021499 = 3032249) B3032249
theorem B6476117 : Blo 2021435 6476117 := bbase (se 10 (by rfl) ⟨9486, by rfl⟩ : syracuseStep 6476117 = 18973) (by norm_num)
theorem B17269645 : Blo 2021435 17269645 := bstep (se 3 (by rfl) ⟨3238058, by rfl⟩ : syracuseStep 17269645 = 6476117) B6476117
theorem B23026193 : Blo 2021435 23026193 := bstep (se 2 (by rfl) ⟨8634822, by rfl⟩ : syracuseStep 23026193 = 17269645) B17269645
theorem B15350795 : Blo 2021435 15350795 := bstep (se 1 (by rfl) ⟨11513096, by rfl⟩ : syracuseStep 15350795 = 23026193) B23026193
theorem B10233863 : Blo 2021435 10233863 := bstep (se 1 (by rfl) ⟨7675397, by rfl⟩ : syracuseStep 10233863 = 15350795) B15350795
theorem B6822575 : Blo 2021435 6822575 := bstep (se 1 (by rfl) ⟨5116931, by rfl⟩ : syracuseStep 6822575 = 10233863) B10233863
theorem B4548383 : Blo 2021435 4548383 := bstep (se 1 (by rfl) ⟨3411287, by rfl⟩ : syracuseStep 4548383 = 6822575) B6822575
theorem B3032255 : Blo 2021435 3032255 := bstep (se 1 (by rfl) ⟨2274191, by rfl⟩ : syracuseStep 3032255 = 4548383) B4548383
theorem B2021503 : Blo 2021435 2021503 := bstep (se 1 (by rfl) ⟨1516127, by rfl⟩ : syracuseStep 2021503 = 3032255) B3032255
theorem B3032261 : Blo 2021435 3032261 := bbase (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) (by norm_num)
theorem B2021507 : Blo 2021435 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B3411301 : Blo 2021435 3411301 := bbase (se 4 (by rfl) ⟨319809, by rfl⟩ : syracuseStep 3411301 = 639619) (by norm_num)
theorem B4548401 : Blo 2021435 4548401 := bstep (se 2 (by rfl) ⟨1705650, by rfl⟩ : syracuseStep 4548401 = 3411301) B3411301
theorem B3032267 : Blo 2021435 3032267 := bstep (se 1 (by rfl) ⟨2274200, by rfl⟩ : syracuseStep 3032267 = 4548401) B4548401
theorem B2021511 : Blo 2021435 2021511 := bstep (se 1 (by rfl) ⟨1516133, by rfl⟩ : syracuseStep 2021511 = 3032267) B3032267
theorem B2274205 : Blo 2021435 2274205 := bbase (se 3 (by rfl) ⟨426413, by rfl⟩ : syracuseStep 2274205 = 852827) (by norm_num)
theorem B3032273 : Blo 2021435 3032273 := bstep (se 2 (by rfl) ⟨1137102, by rfl⟩ : syracuseStep 3032273 = 2274205) B2274205
theorem B2021515 : Blo 2021435 2021515 := bstep (se 1 (by rfl) ⟨1516136, by rfl⟩ : syracuseStep 2021515 = 3032273) B3032273
theorem B6822629 : Blo 2021435 6822629 := bbase (se 4 (by rfl) ⟨639621, by rfl⟩ : syracuseStep 6822629 = 1279243) (by norm_num)
theorem B4548419 : Blo 2021435 4548419 := bstep (se 1 (by rfl) ⟨3411314, by rfl⟩ : syracuseStep 4548419 = 6822629) B6822629
theorem B3032279 : Blo 2021435 3032279 := bstep (se 1 (by rfl) ⟨2274209, by rfl⟩ : syracuseStep 3032279 = 4548419) B4548419
theorem B2021519 : Blo 2021435 2021519 := bstep (se 1 (by rfl) ⟨1516139, by rfl⟩ : syracuseStep 2021519 = 3032279) B3032279
theorem B3032285 : Blo 2021435 3032285 := bbase (se 3 (by rfl) ⟨568553, by rfl⟩ : syracuseStep 3032285 = 1137107) (by norm_num)
theorem B2021523 : Blo 2021435 2021523 := bstep (se 1 (by rfl) ⟨1516142, by rfl⟩ : syracuseStep 2021523 = 3032285) B3032285
theorem B4548437 : Blo 2021435 4548437 := bbase (se 9 (by rfl) ⟨13325, by rfl⟩ : syracuseStep 4548437 = 26651) (by norm_num)
theorem B3032291 : Blo 2021435 3032291 := bstep (se 1 (by rfl) ⟨2274218, by rfl⟩ : syracuseStep 3032291 = 4548437) B4548437
theorem B2021527 : Blo 2021435 2021527 := bstep (se 1 (by rfl) ⟨1516145, by rfl⟩ : syracuseStep 2021527 = 3032291) B3032291
theorem B5756629 : Blo 2021435 5756629 := bbase (se 7 (by rfl) ⟨67460, by rfl⟩ : syracuseStep 5756629 = 134921) (by norm_num)
theorem B7675505 : Blo 2021435 7675505 := bstep (se 2 (by rfl) ⟨2878314, by rfl⟩ : syracuseStep 7675505 = 5756629) B5756629
theorem B5117003 : Blo 2021435 5117003 := bstep (se 1 (by rfl) ⟨3837752, by rfl⟩ : syracuseStep 5117003 = 7675505) B7675505
theorem B3411335 : Blo 2021435 3411335 := bstep (se 1 (by rfl) ⟨2558501, by rfl⟩ : syracuseStep 3411335 = 5117003) B5117003
theorem B2274223 : Blo 2021435 2274223 := bstep (se 1 (by rfl) ⟨1705667, by rfl⟩ : syracuseStep 2274223 = 3411335) B3411335
theorem B3032297 : Blo 2021435 3032297 := bstep (se 2 (by rfl) ⟨1137111, by rfl⟩ : syracuseStep 3032297 = 2274223) B2274223
theorem B2021531 : Blo 2021435 2021531 := bstep (se 1 (by rfl) ⟨1516148, by rfl⟩ : syracuseStep 2021531 = 3032297) B3032297
theorem B37897429 : Blo 2021435 37897429 := bbase (se 7 (by rfl) ⟨444110, by rfl⟩ : syracuseStep 37897429 = 888221) (by norm_num)
theorem B50529905 : Blo 2021435 50529905 := bstep (se 2 (by rfl) ⟨18948714, by rfl⟩ : syracuseStep 50529905 = 37897429) B37897429
theorem B33686603 : Blo 2021435 33686603 := bstep (se 1 (by rfl) ⟨25264952, by rfl⟩ : syracuseStep 33686603 = 50529905) B50529905
theorem B22457735 : Blo 2021435 22457735 := bstep (se 1 (by rfl) ⟨16843301, by rfl⟩ : syracuseStep 22457735 = 33686603) B33686603
theorem B14971823 : Blo 2021435 14971823 := bstep (se 1 (by rfl) ⟨11228867, by rfl⟩ : syracuseStep 14971823 = 22457735) B22457735
theorem B9981215 : Blo 2021435 9981215 := bstep (se 1 (by rfl) ⟨7485911, by rfl⟩ : syracuseStep 9981215 = 14971823) B14971823
theorem B6654143 : Blo 2021435 6654143 := bstep (se 1 (by rfl) ⟨4990607, by rfl⟩ : syracuseStep 6654143 = 9981215) B9981215
theorem B4436095 : Blo 2021435 4436095 := bstep (se 1 (by rfl) ⟨3327071, by rfl⟩ : syracuseStep 4436095 = 6654143) B6654143
theorem B5914793 : Blo 2021435 5914793 := bstep (se 2 (by rfl) ⟨2218047, by rfl⟩ : syracuseStep 5914793 = 4436095) B4436095
theorem B15772781 : Blo 2021435 15772781 := bstep (se 3 (by rfl) ⟨2957396, by rfl⟩ : syracuseStep 15772781 = 5914793) B5914793
theorem B10515187 : Blo 2021435 10515187 := bstep (se 1 (by rfl) ⟨7886390, by rfl⟩ : syracuseStep 10515187 = 15772781) B15772781
theorem B14020249 : Blo 2021435 14020249 := bstep (se 2 (by rfl) ⟨5257593, by rfl⟩ : syracuseStep 14020249 = 10515187) B10515187
theorem B18693665 : Blo 2021435 18693665 := bstep (se 2 (by rfl) ⟨7010124, by rfl⟩ : syracuseStep 18693665 = 14020249) B14020249
theorem B12462443 : Blo 2021435 12462443 := bstep (se 1 (by rfl) ⟨9346832, by rfl⟩ : syracuseStep 12462443 = 18693665) B18693665
theorem B8308295 : Blo 2021435 8308295 := bstep (se 1 (by rfl) ⟨6231221, by rfl⟩ : syracuseStep 8308295 = 12462443) B12462443
theorem B5538863 : Blo 2021435 5538863 := bstep (se 1 (by rfl) ⟨4154147, by rfl⟩ : syracuseStep 5538863 = 8308295) B8308295
theorem B3692575 : Blo 2021435 3692575 := bstep (se 1 (by rfl) ⟨2769431, by rfl⟩ : syracuseStep 3692575 = 5538863) B5538863
theorem B4923433 : Blo 2021435 4923433 := bstep (se 2 (by rfl) ⟨1846287, by rfl⟩ : syracuseStep 4923433 = 3692575) B3692575
theorem B26258309 : Blo 2021435 26258309 := bstep (se 4 (by rfl) ⟨2461716, by rfl⟩ : syracuseStep 26258309 = 4923433) B4923433
theorem B17505539 : Blo 2021435 17505539 := bstep (se 1 (by rfl) ⟨13129154, by rfl⟩ : syracuseStep 17505539 = 26258309) B26258309
theorem B11670359 : Blo 2021435 11670359 := bstep (se 1 (by rfl) ⟨8752769, by rfl⟩ : syracuseStep 11670359 = 17505539) B17505539
theorem B31120957 : Blo 2021435 31120957 := bstep (se 3 (by rfl) ⟨5835179, by rfl⟩ : syracuseStep 31120957 = 11670359) B11670359
theorem B41494609 : Blo 2021435 41494609 := bstep (se 2 (by rfl) ⟨15560478, by rfl⟩ : syracuseStep 41494609 = 31120957) B31120957
theorem B221304581 : Blo 2021435 221304581 := bstep (se 4 (by rfl) ⟨20747304, by rfl⟩ : syracuseStep 221304581 = 41494609) B41494609
theorem B147536387 : Blo 2021435 147536387 := bstep (se 1 (by rfl) ⟨110652290, by rfl⟩ : syracuseStep 147536387 = 221304581) B221304581
theorem B98357591 : Blo 2021435 98357591 := bstep (se 1 (by rfl) ⟨73768193, by rfl⟩ : syracuseStep 98357591 = 147536387) B147536387
theorem B65571727 : Blo 2021435 65571727 := bstep (se 1 (by rfl) ⟨49178795, by rfl⟩ : syracuseStep 65571727 = 98357591) B98357591
theorem B87428969 : Blo 2021435 87428969 := bstep (se 2 (by rfl) ⟨32785863, by rfl⟩ : syracuseStep 87428969 = 65571727) B65571727
theorem B58285979 : Blo 2021435 58285979 := bstep (se 1 (by rfl) ⟨43714484, by rfl⟩ : syracuseStep 58285979 = 87428969) B87428969
theorem B38857319 : Blo 2021435 38857319 := bstep (se 1 (by rfl) ⟨29142989, by rfl⟩ : syracuseStep 38857319 = 58285979) B58285979
theorem B25904879 : Blo 2021435 25904879 := bstep (se 1 (by rfl) ⟨19428659, by rfl⟩ : syracuseStep 25904879 = 38857319) B38857319
theorem B17269919 : Blo 2021435 17269919 := bstep (se 1 (by rfl) ⟨12952439, by rfl⟩ : syracuseStep 17269919 = 25904879) B25904879
theorem B11513279 : Blo 2021435 11513279 := bstep (se 1 (by rfl) ⟨8634959, by rfl⟩ : syracuseStep 11513279 = 17269919) B17269919
theorem B7675519 : Blo 2021435 7675519 := bstep (se 1 (by rfl) ⟨5756639, by rfl⟩ : syracuseStep 7675519 = 11513279) B11513279
theorem B10234025 : Blo 2021435 10234025 := bstep (se 2 (by rfl) ⟨3837759, by rfl⟩ : syracuseStep 10234025 = 7675519) B7675519
theorem B6822683 : Blo 2021435 6822683 := bstep (se 1 (by rfl) ⟨5117012, by rfl⟩ : syracuseStep 6822683 = 10234025) B10234025
theorem B4548455 : Blo 2021435 4548455 := bstep (se 1 (by rfl) ⟨3411341, by rfl⟩ : syracuseStep 4548455 = 6822683) B6822683
theorem B3032303 : Blo 2021435 3032303 := bstep (se 1 (by rfl) ⟨2274227, by rfl⟩ : syracuseStep 3032303 = 4548455) B4548455
theorem B2021535 : Blo 2021435 2021535 := bstep (se 1 (by rfl) ⟨1516151, by rfl⟩ : syracuseStep 2021535 = 3032303) B3032303
theorem B3032309 : Blo 2021435 3032309 := bbase (se 5 (by rfl) ⟨142139, by rfl⟩ : syracuseStep 3032309 = 284279) (by norm_num)
theorem B2021539 : Blo 2021435 2021539 := bstep (se 1 (by rfl) ⟨1516154, by rfl⟩ : syracuseStep 2021539 = 3032309) B3032309
theorem B4610533 : Blo 2021435 4610533 := bbase (se 4 (by rfl) ⟨432237, by rfl⟩ : syracuseStep 4610533 = 864475) (by norm_num)
theorem B6147377 : Blo 2021435 6147377 := bstep (se 2 (by rfl) ⟨2305266, by rfl⟩ : syracuseStep 6147377 = 4610533) B4610533
theorem B4098251 : Blo 2021435 4098251 := bstep (se 1 (by rfl) ⟨3073688, by rfl⟩ : syracuseStep 4098251 = 6147377) B6147377
theorem B2732167 : Blo 2021435 2732167 := bstep (se 1 (by rfl) ⟨2049125, by rfl⟩ : syracuseStep 2732167 = 4098251) B4098251
theorem B3642889 : Blo 2021435 3642889 := bstep (se 2 (by rfl) ⟨1366083, by rfl⟩ : syracuseStep 3642889 = 2732167) B2732167
theorem B4857185 : Blo 2021435 4857185 := bstep (se 2 (by rfl) ⟨1821444, by rfl⟩ : syracuseStep 4857185 = 3642889) B3642889
theorem B12952493 : Blo 2021435 12952493 := bstep (se 3 (by rfl) ⟨2428592, by rfl⟩ : syracuseStep 12952493 = 4857185) B4857185
theorem B8634995 : Blo 2021435 8634995 := bstep (se 1 (by rfl) ⟨6476246, by rfl⟩ : syracuseStep 8634995 = 12952493) B12952493
theorem B5756663 : Blo 2021435 5756663 := bstep (se 1 (by rfl) ⟨4317497, by rfl⟩ : syracuseStep 5756663 = 8634995) B8634995
theorem B3837775 : Blo 2021435 3837775 := bstep (se 1 (by rfl) ⟨2878331, by rfl⟩ : syracuseStep 3837775 = 5756663) B5756663
theorem B5117033 : Blo 2021435 5117033 := bstep (se 2 (by rfl) ⟨1918887, by rfl⟩ : syracuseStep 5117033 = 3837775) B3837775
theorem B3411355 : Blo 2021435 3411355 := bstep (se 1 (by rfl) ⟨2558516, by rfl⟩ : syracuseStep 3411355 = 5117033) B5117033
theorem B4548473 : Blo 2021435 4548473 := bstep (se 2 (by rfl) ⟨1705677, by rfl⟩ : syracuseStep 4548473 = 3411355) B3411355
theorem B3032315 : Blo 2021435 3032315 := bstep (se 1 (by rfl) ⟨2274236, by rfl⟩ : syracuseStep 3032315 = 4548473) B4548473
theorem B2021543 : Blo 2021435 2021543 := bstep (se 1 (by rfl) ⟨1516157, by rfl⟩ : syracuseStep 2021543 = 3032315) B3032315
theorem B2274241 : Blo 2021435 2274241 := bbase (se 2 (by rfl) ⟨852840, by rfl⟩ : syracuseStep 2274241 = 1705681) (by norm_num)
theorem B3032321 : Blo 2021435 3032321 := bstep (se 2 (by rfl) ⟨1137120, by rfl⟩ : syracuseStep 3032321 = 2274241) B2274241
theorem B2021547 : Blo 2021435 2021547 := bstep (se 1 (by rfl) ⟨1516160, by rfl⟩ : syracuseStep 2021547 = 3032321) B3032321
theorem B5117053 : Blo 2021435 5117053 := bbase (se 3 (by rfl) ⟨959447, by rfl⟩ : syracuseStep 5117053 = 1918895) (by norm_num)
theorem B6822737 : Blo 2021435 6822737 := bstep (se 2 (by rfl) ⟨2558526, by rfl⟩ : syracuseStep 6822737 = 5117053) B5117053
theorem B4548491 : Blo 2021435 4548491 := bstep (se 1 (by rfl) ⟨3411368, by rfl⟩ : syracuseStep 4548491 = 6822737) B6822737
theorem B3032327 : Blo 2021435 3032327 := bstep (se 1 (by rfl) ⟨2274245, by rfl⟩ : syracuseStep 3032327 = 4548491) B4548491
theorem B2021551 : Blo 2021435 2021551 := bstep (se 1 (by rfl) ⟨1516163, by rfl⟩ : syracuseStep 2021551 = 3032327) B3032327
theorem B3032333 : Blo 2021435 3032333 := bbase (se 3 (by rfl) ⟨568562, by rfl⟩ : syracuseStep 3032333 = 1137125) (by norm_num)
theorem B2021555 : Blo 2021435 2021555 := bstep (se 1 (by rfl) ⟨1516166, by rfl⟩ : syracuseStep 2021555 = 3032333) B3032333
theorem B4548509 : Blo 2021435 4548509 := bbase (se 3 (by rfl) ⟨852845, by rfl⟩ : syracuseStep 4548509 = 1705691) (by norm_num)
theorem B3032339 : Blo 2021435 3032339 := bstep (se 1 (by rfl) ⟨2274254, by rfl⟩ : syracuseStep 3032339 = 4548509) B4548509
theorem B2021559 : Blo 2021435 2021559 := bstep (se 1 (by rfl) ⟨1516169, by rfl⟩ : syracuseStep 2021559 = 3032339) B3032339
theorem B3411389 : Blo 2021435 3411389 := bbase (se 3 (by rfl) ⟨639635, by rfl⟩ : syracuseStep 3411389 = 1279271) (by norm_num)
theorem B2274259 : Blo 2021435 2274259 := bstep (se 1 (by rfl) ⟨1705694, by rfl⟩ : syracuseStep 2274259 = 3411389) B3411389
theorem B3032345 : Blo 2021435 3032345 := bstep (se 2 (by rfl) ⟨1137129, by rfl⟩ : syracuseStep 3032345 = 2274259) B2274259
theorem B2021563 : Blo 2021435 2021563 := bstep (se 1 (by rfl) ⟨1516172, by rfl⟩ : syracuseStep 2021563 = 3032345) B3032345
theorem B11513461 : Blo 2021435 11513461 := bbase (se 5 (by rfl) ⟨539693, by rfl⟩ : syracuseStep 11513461 = 1079387) (by norm_num)
theorem B15351281 : Blo 2021435 15351281 := bstep (se 2 (by rfl) ⟨5756730, by rfl⟩ : syracuseStep 15351281 = 11513461) B11513461
theorem B10234187 : Blo 2021435 10234187 := bstep (se 1 (by rfl) ⟨7675640, by rfl⟩ : syracuseStep 10234187 = 15351281) B15351281
theorem B6822791 : Blo 2021435 6822791 := bstep (se 1 (by rfl) ⟨5117093, by rfl⟩ : syracuseStep 6822791 = 10234187) B10234187
theorem B4548527 : Blo 2021435 4548527 := bstep (se 1 (by rfl) ⟨3411395, by rfl⟩ : syracuseStep 4548527 = 6822791) B6822791
theorem B3032351 : Blo 2021435 3032351 := bstep (se 1 (by rfl) ⟨2274263, by rfl⟩ : syracuseStep 3032351 = 4548527) B4548527
theorem B2021567 : Blo 2021435 2021567 := bstep (se 1 (by rfl) ⟨1516175, by rfl⟩ : syracuseStep 2021567 = 3032351) B3032351
theorem B3032357 : Blo 2021435 3032357 := bbase (se 4 (by rfl) ⟨284283, by rfl⟩ : syracuseStep 3032357 = 568567) (by norm_num)
theorem B2021571 : Blo 2021435 2021571 := bstep (se 1 (by rfl) ⟨1516178, by rfl⟩ : syracuseStep 2021571 = 3032357) B3032357
theorem B2558557 : Blo 2021435 2558557 := bbase (se 3 (by rfl) ⟨479729, by rfl⟩ : syracuseStep 2558557 = 959459) (by norm_num)
theorem B3411409 : Blo 2021435 3411409 := bstep (se 2 (by rfl) ⟨1279278, by rfl⟩ : syracuseStep 3411409 = 2558557) B2558557
theorem B4548545 : Blo 2021435 4548545 := bstep (se 2 (by rfl) ⟨1705704, by rfl⟩ : syracuseStep 4548545 = 3411409) B3411409
theorem B3032363 : Blo 2021435 3032363 := bstep (se 1 (by rfl) ⟨2274272, by rfl⟩ : syracuseStep 3032363 = 4548545) B4548545
theorem B2021575 : Blo 2021435 2021575 := bstep (se 1 (by rfl) ⟨1516181, by rfl⟩ : syracuseStep 2021575 = 3032363) B3032363
theorem B2274277 : Blo 2021435 2274277 := bbase (se 4 (by rfl) ⟨213213, by rfl⟩ : syracuseStep 2274277 = 426427) (by norm_num)
theorem B3032369 : Blo 2021435 3032369 := bstep (se 2 (by rfl) ⟨1137138, by rfl⟩ : syracuseStep 3032369 = 2274277) B2274277
theorem B2021579 : Blo 2021435 2021579 := bstep (se 1 (by rfl) ⟨1516184, by rfl⟩ : syracuseStep 2021579 = 3032369) B3032369
theorem B2732221 : Blo 2021435 2732221 := bbase (se 3 (by rfl) ⟨512291, by rfl⟩ : syracuseStep 2732221 = 1024583) (by norm_num)
theorem B14571845 : Blo 2021435 14571845 := bstep (se 4 (by rfl) ⟨1366110, by rfl⟩ : syracuseStep 14571845 = 2732221) B2732221
theorem B9714563 : Blo 2021435 9714563 := bstep (se 1 (by rfl) ⟨7285922, by rfl⟩ : syracuseStep 9714563 = 14571845) B14571845
theorem B6476375 : Blo 2021435 6476375 := bstep (se 1 (by rfl) ⟨4857281, by rfl⟩ : syracuseStep 6476375 = 9714563) B9714563
theorem B4317583 : Blo 2021435 4317583 := bstep (se 1 (by rfl) ⟨3238187, by rfl⟩ : syracuseStep 4317583 = 6476375) B6476375
theorem B5756777 : Blo 2021435 5756777 := bstep (se 2 (by rfl) ⟨2158791, by rfl⟩ : syracuseStep 5756777 = 4317583) B4317583
theorem B3837851 : Blo 2021435 3837851 := bstep (se 1 (by rfl) ⟨2878388, by rfl⟩ : syracuseStep 3837851 = 5756777) B5756777
theorem B2558567 : Blo 2021435 2558567 := bstep (se 1 (by rfl) ⟨1918925, by rfl⟩ : syracuseStep 2558567 = 3837851) B3837851
theorem B6822845 : Blo 2021435 6822845 := bstep (se 3 (by rfl) ⟨1279283, by rfl⟩ : syracuseStep 6822845 = 2558567) B2558567
theorem B4548563 : Blo 2021435 4548563 := bstep (se 1 (by rfl) ⟨3411422, by rfl⟩ : syracuseStep 4548563 = 6822845) B6822845
theorem B3032375 : Blo 2021435 3032375 := bstep (se 1 (by rfl) ⟨2274281, by rfl⟩ : syracuseStep 3032375 = 4548563) B4548563
theorem B2021583 : Blo 2021435 2021583 := bstep (se 1 (by rfl) ⟨1516187, by rfl⟩ : syracuseStep 2021583 = 3032375) B3032375
theorem B3032381 : Blo 2021435 3032381 := bbase (se 3 (by rfl) ⟨568571, by rfl⟩ : syracuseStep 3032381 = 1137143) (by norm_num)
theorem B2021587 : Blo 2021435 2021587 := bstep (se 1 (by rfl) ⟨1516190, by rfl⟩ : syracuseStep 2021587 = 3032381) B3032381
theorem B4548581 : Blo 2021435 4548581 := bbase (se 4 (by rfl) ⟨426429, by rfl⟩ : syracuseStep 4548581 = 852859) (by norm_num)
theorem B3032387 : Blo 2021435 3032387 := bstep (se 1 (by rfl) ⟨2274290, by rfl⟩ : syracuseStep 3032387 = 4548581) B4548581
theorem B2021591 : Blo 2021435 2021591 := bstep (se 1 (by rfl) ⟨1516193, by rfl⟩ : syracuseStep 2021591 = 3032387) B3032387
theorem B5117165 : Blo 2021435 5117165 := bbase (se 3 (by rfl) ⟨959468, by rfl⟩ : syracuseStep 5117165 = 1918937) (by norm_num)
theorem B3411443 : Blo 2021435 3411443 := bstep (se 1 (by rfl) ⟨2558582, by rfl⟩ : syracuseStep 3411443 = 5117165) B5117165
theorem B2274295 : Blo 2021435 2274295 := bstep (se 1 (by rfl) ⟨1705721, by rfl⟩ : syracuseStep 2274295 = 3411443) B3411443
theorem B3032393 : Blo 2021435 3032393 := bstep (se 2 (by rfl) ⟨1137147, by rfl⟩ : syracuseStep 3032393 = 2274295) B2274295
theorem B2021595 : Blo 2021435 2021595 := bstep (se 1 (by rfl) ⟨1516196, by rfl⟩ : syracuseStep 2021595 = 3032393) B3032393
theorem B3238213 : Blo 2021435 3238213 := bbase (se 4 (by rfl) ⟨303582, by rfl⟩ : syracuseStep 3238213 = 607165) (by norm_num)
theorem B4317617 : Blo 2021435 4317617 := bstep (se 2 (by rfl) ⟨1619106, by rfl⟩ : syracuseStep 4317617 = 3238213) B3238213
theorem B2878411 : Blo 2021435 2878411 := bstep (se 1 (by rfl) ⟨2158808, by rfl⟩ : syracuseStep 2878411 = 4317617) B4317617
theorem B3837881 : Blo 2021435 3837881 := bstep (se 2 (by rfl) ⟨1439205, by rfl⟩ : syracuseStep 3837881 = 2878411) B2878411
theorem B10234349 : Blo 2021435 10234349 := bstep (se 3 (by rfl) ⟨1918940, by rfl⟩ : syracuseStep 10234349 = 3837881) B3837881
theorem B6822899 : Blo 2021435 6822899 := bstep (se 1 (by rfl) ⟨5117174, by rfl⟩ : syracuseStep 6822899 = 10234349) B10234349
theorem B4548599 : Blo 2021435 4548599 := bstep (se 1 (by rfl) ⟨3411449, by rfl⟩ : syracuseStep 4548599 = 6822899) B6822899
theorem B3032399 : Blo 2021435 3032399 := bstep (se 1 (by rfl) ⟨2274299, by rfl⟩ : syracuseStep 3032399 = 4548599) B4548599
theorem B2021599 : Blo 2021435 2021599 := bstep (se 1 (by rfl) ⟨1516199, by rfl⟩ : syracuseStep 2021599 = 3032399) B3032399
theorem B3032405 : Blo 2021435 3032405 := bbase (se 12 (by rfl) ⟨1110, by rfl⟩ : syracuseStep 3032405 = 2221) (by norm_num)
theorem B2021603 : Blo 2021435 2021603 := bstep (se 1 (by rfl) ⟨1516202, by rfl⟩ : syracuseStep 2021603 = 3032405) B3032405
theorem B2158817 : Blo 2021435 2158817 := bbase (se 2 (by rfl) ⟨809556, by rfl⟩ : syracuseStep 2158817 = 1619113) (by norm_num)
theorem B5756845 : Blo 2021435 5756845 := bstep (se 3 (by rfl) ⟨1079408, by rfl⟩ : syracuseStep 5756845 = 2158817) B2158817
theorem B7675793 : Blo 2021435 7675793 := bstep (se 2 (by rfl) ⟨2878422, by rfl⟩ : syracuseStep 7675793 = 5756845) B5756845
theorem B5117195 : Blo 2021435 5117195 := bstep (se 1 (by rfl) ⟨3837896, by rfl⟩ : syracuseStep 5117195 = 7675793) B7675793
theorem B3411463 : Blo 2021435 3411463 := bstep (se 1 (by rfl) ⟨2558597, by rfl⟩ : syracuseStep 3411463 = 5117195) B5117195
theorem B4548617 : Blo 2021435 4548617 := bstep (se 2 (by rfl) ⟨1705731, by rfl⟩ : syracuseStep 4548617 = 3411463) B3411463
theorem B3032411 : Blo 2021435 3032411 := bstep (se 1 (by rfl) ⟨2274308, by rfl⟩ : syracuseStep 3032411 = 4548617) B4548617
theorem B2021607 : Blo 2021435 2021607 := bstep (se 1 (by rfl) ⟨1516205, by rfl⟩ : syracuseStep 2021607 = 3032411) B3032411
theorem B2274313 : Blo 2021435 2274313 := bbase (se 2 (by rfl) ⟨852867, by rfl⟩ : syracuseStep 2274313 = 1705735) (by norm_num)
theorem B3032417 : Blo 2021435 3032417 := bstep (se 2 (by rfl) ⟨1137156, by rfl⟩ : syracuseStep 3032417 = 2274313) B2274313
theorem B2021611 : Blo 2021435 2021611 := bstep (se 1 (by rfl) ⟨1516208, by rfl⟩ : syracuseStep 2021611 = 3032417) B3032417
theorem B19429429 : Blo 2021435 19429429 := bbase (se 5 (by rfl) ⟨910754, by rfl⟩ : syracuseStep 19429429 = 1821509) (by norm_num)
theorem B25905905 : Blo 2021435 25905905 := bstep (se 2 (by rfl) ⟨9714714, by rfl⟩ : syracuseStep 25905905 = 19429429) B19429429
theorem B17270603 : Blo 2021435 17270603 := bstep (se 1 (by rfl) ⟨12952952, by rfl⟩ : syracuseStep 17270603 = 25905905) B25905905
theorem B11513735 : Blo 2021435 11513735 := bstep (se 1 (by rfl) ⟨8635301, by rfl⟩ : syracuseStep 11513735 = 17270603) B17270603
theorem B7675823 : Blo 2021435 7675823 := bstep (se 1 (by rfl) ⟨5756867, by rfl⟩ : syracuseStep 7675823 = 11513735) B11513735
theorem B5117215 : Blo 2021435 5117215 := bstep (se 1 (by rfl) ⟨3837911, by rfl⟩ : syracuseStep 5117215 = 7675823) B7675823
theorem B6822953 : Blo 2021435 6822953 := bstep (se 2 (by rfl) ⟨2558607, by rfl⟩ : syracuseStep 6822953 = 5117215) B5117215
theorem B4548635 : Blo 2021435 4548635 := bstep (se 1 (by rfl) ⟨3411476, by rfl⟩ : syracuseStep 4548635 = 6822953) B6822953
theorem B3032423 : Blo 2021435 3032423 := bstep (se 1 (by rfl) ⟨2274317, by rfl⟩ : syracuseStep 3032423 = 4548635) B4548635
theorem B2021615 : Blo 2021435 2021615 := bstep (se 1 (by rfl) ⟨1516211, by rfl⟩ : syracuseStep 2021615 = 3032423) B3032423
theorem B3032429 : Blo 2021435 3032429 := bbase (se 3 (by rfl) ⟨568580, by rfl⟩ : syracuseStep 3032429 = 1137161) (by norm_num)
theorem B2021619 : Blo 2021435 2021619 := bstep (se 1 (by rfl) ⟨1516214, by rfl⟩ : syracuseStep 2021619 = 3032429) B3032429
theorem B4548653 : Blo 2021435 4548653 := bbase (se 3 (by rfl) ⟨852872, by rfl⟩ : syracuseStep 4548653 = 1705745) (by norm_num)
theorem B3032435 : Blo 2021435 3032435 := bstep (se 1 (by rfl) ⟨2274326, by rfl⟩ : syracuseStep 3032435 = 4548653) B4548653
theorem B2021623 : Blo 2021435 2021623 := bstep (se 1 (by rfl) ⟨1516217, by rfl⟩ : syracuseStep 2021623 = 3032435) B3032435
theorem B4098421 : Blo 2021435 4098421 := bbase (se 5 (by rfl) ⟨192113, by rfl⟩ : syracuseStep 4098421 = 384227) (by norm_num)
theorem B21858245 : Blo 2021435 21858245 := bstep (se 4 (by rfl) ⟨2049210, by rfl⟩ : syracuseStep 21858245 = 4098421) B4098421
theorem B14572163 : Blo 2021435 14572163 := bstep (se 1 (by rfl) ⟨10929122, by rfl⟩ : syracuseStep 14572163 = 21858245) B21858245
theorem B9714775 : Blo 2021435 9714775 := bstep (se 1 (by rfl) ⟨7286081, by rfl⟩ : syracuseStep 9714775 = 14572163) B14572163
theorem B12953033 : Blo 2021435 12953033 := bstep (se 2 (by rfl) ⟨4857387, by rfl⟩ : syracuseStep 12953033 = 9714775) B9714775
theorem B8635355 : Blo 2021435 8635355 := bstep (se 1 (by rfl) ⟨6476516, by rfl⟩ : syracuseStep 8635355 = 12953033) B12953033
theorem B5756903 : Blo 2021435 5756903 := bstep (se 1 (by rfl) ⟨4317677, by rfl⟩ : syracuseStep 5756903 = 8635355) B8635355
theorem B3837935 : Blo 2021435 3837935 := bstep (se 1 (by rfl) ⟨2878451, by rfl⟩ : syracuseStep 3837935 = 5756903) B5756903
theorem B2558623 : Blo 2021435 2558623 := bstep (se 1 (by rfl) ⟨1918967, by rfl⟩ : syracuseStep 2558623 = 3837935) B3837935
theorem B3411497 : Blo 2021435 3411497 := bstep (se 2 (by rfl) ⟨1279311, by rfl⟩ : syracuseStep 3411497 = 2558623) B2558623
theorem B2274331 : Blo 2021435 2274331 := bstep (se 1 (by rfl) ⟨1705748, by rfl⟩ : syracuseStep 2274331 = 3411497) B3411497
theorem B3032441 : Blo 2021435 3032441 := bstep (se 2 (by rfl) ⟨1137165, by rfl⟩ : syracuseStep 3032441 = 2274331) B2274331
theorem B2021627 : Blo 2021435 2021627 := bstep (se 1 (by rfl) ⟨1516220, by rfl⟩ : syracuseStep 2021627 = 3032441) B3032441
theorem B19963381 : Blo 2021435 19963381 := bbase (se 5 (by rfl) ⟨935783, by rfl⟩ : syracuseStep 19963381 = 1871567) (by norm_num)
theorem B26617841 : Blo 2021435 26617841 := bstep (se 2 (by rfl) ⟨9981690, by rfl⟩ : syracuseStep 26617841 = 19963381) B19963381
theorem B17745227 : Blo 2021435 17745227 := bstep (se 1 (by rfl) ⟨13308920, by rfl⟩ : syracuseStep 17745227 = 26617841) B26617841
theorem B11830151 : Blo 2021435 11830151 := bstep (se 1 (by rfl) ⟨8872613, by rfl⟩ : syracuseStep 11830151 = 17745227) B17745227
theorem B7886767 : Blo 2021435 7886767 := bstep (se 1 (by rfl) ⟨5915075, by rfl⟩ : syracuseStep 7886767 = 11830151) B11830151
theorem B10515689 : Blo 2021435 10515689 := bstep (se 2 (by rfl) ⟨3943383, by rfl⟩ : syracuseStep 10515689 = 7886767) B7886767
theorem B7010459 : Blo 2021435 7010459 := bstep (se 1 (by rfl) ⟨5257844, by rfl⟩ : syracuseStep 7010459 = 10515689) B10515689
theorem B4673639 : Blo 2021435 4673639 := bstep (se 1 (by rfl) ⟨3505229, by rfl⟩ : syracuseStep 4673639 = 7010459) B7010459
theorem B3115759 : Blo 2021435 3115759 := bstep (se 1 (by rfl) ⟨2336819, by rfl⟩ : syracuseStep 3115759 = 4673639) B4673639
theorem B4154345 : Blo 2021435 4154345 := bstep (se 2 (by rfl) ⟨1557879, by rfl⟩ : syracuseStep 4154345 = 3115759) B3115759
theorem B2769563 : Blo 2021435 2769563 := bstep (se 1 (by rfl) ⟨2077172, by rfl⟩ : syracuseStep 2769563 = 4154345) B4154345
theorem B7385501 : Blo 2021435 7385501 := bstep (se 3 (by rfl) ⟨1384781, by rfl⟩ : syracuseStep 7385501 = 2769563) B2769563
theorem B4923667 : Blo 2021435 4923667 := bstep (se 1 (by rfl) ⟨3692750, by rfl⟩ : syracuseStep 4923667 = 7385501) B7385501
theorem B26259557 : Blo 2021435 26259557 := bstep (se 4 (by rfl) ⟨2461833, by rfl⟩ : syracuseStep 26259557 = 4923667) B4923667
theorem B70025485 : Blo 2021435 70025485 := bstep (se 3 (by rfl) ⟨13129778, by rfl⟩ : syracuseStep 70025485 = 26259557) B26259557
theorem B93367313 : Blo 2021435 93367313 := bstep (se 2 (by rfl) ⟨35012742, by rfl⟩ : syracuseStep 93367313 = 70025485) B70025485
theorem B62244875 : Blo 2021435 62244875 := bstep (se 1 (by rfl) ⟨46683656, by rfl⟩ : syracuseStep 62244875 = 93367313) B93367313
theorem B41496583 : Blo 2021435 41496583 := bstep (se 1 (by rfl) ⟨31122437, by rfl⟩ : syracuseStep 41496583 = 62244875) B62244875
theorem B55328777 : Blo 2021435 55328777 := bstep (se 2 (by rfl) ⟨20748291, by rfl⟩ : syracuseStep 55328777 = 41496583) B41496583
theorem B36885851 : Blo 2021435 36885851 := bstep (se 1 (by rfl) ⟨27664388, by rfl⟩ : syracuseStep 36885851 = 55328777) B55328777
theorem B24590567 : Blo 2021435 24590567 := bstep (se 1 (by rfl) ⟨18442925, by rfl⟩ : syracuseStep 24590567 = 36885851) B36885851
theorem B16393711 : Blo 2021435 16393711 := bstep (se 1 (by rfl) ⟨12295283, by rfl⟩ : syracuseStep 16393711 = 24590567) B24590567
theorem B21858281 : Blo 2021435 21858281 := bstep (se 2 (by rfl) ⟨8196855, by rfl⟩ : syracuseStep 21858281 = 16393711) B16393711
theorem B14572187 : Blo 2021435 14572187 := bstep (se 1 (by rfl) ⟨10929140, by rfl⟩ : syracuseStep 14572187 = 21858281) B21858281
theorem B9714791 : Blo 2021435 9714791 := bstep (se 1 (by rfl) ⟨7286093, by rfl⟩ : syracuseStep 9714791 = 14572187) B14572187
theorem B6476527 : Blo 2021435 6476527 := bstep (se 1 (by rfl) ⟨4857395, by rfl⟩ : syracuseStep 6476527 = 9714791) B9714791
theorem B34541477 : Blo 2021435 34541477 := bstep (se 4 (by rfl) ⟨3238263, by rfl⟩ : syracuseStep 34541477 = 6476527) B6476527
theorem B23027651 : Blo 2021435 23027651 := bstep (se 1 (by rfl) ⟨17270738, by rfl⟩ : syracuseStep 23027651 = 34541477) B34541477
theorem B15351767 : Blo 2021435 15351767 := bstep (se 1 (by rfl) ⟨11513825, by rfl⟩ : syracuseStep 15351767 = 23027651) B23027651
theorem B10234511 : Blo 2021435 10234511 := bstep (se 1 (by rfl) ⟨7675883, by rfl⟩ : syracuseStep 10234511 = 15351767) B15351767
theorem B6823007 : Blo 2021435 6823007 := bstep (se 1 (by rfl) ⟨5117255, by rfl⟩ : syracuseStep 6823007 = 10234511) B10234511
theorem B4548671 : Blo 2021435 4548671 := bstep (se 1 (by rfl) ⟨3411503, by rfl⟩ : syracuseStep 4548671 = 6823007) B6823007
theorem B3032447 : Blo 2021435 3032447 := bstep (se 1 (by rfl) ⟨2274335, by rfl⟩ : syracuseStep 3032447 = 4548671) B4548671
theorem B2021631 : Blo 2021435 2021631 := bstep (se 1 (by rfl) ⟨1516223, by rfl⟩ : syracuseStep 2021631 = 3032447) B3032447
theorem B3032453 : Blo 2021435 3032453 := bbase (se 4 (by rfl) ⟨284292, by rfl⟩ : syracuseStep 3032453 = 568585) (by norm_num)
theorem B2021635 : Blo 2021435 2021635 := bstep (se 1 (by rfl) ⟨1516226, by rfl⟩ : syracuseStep 2021635 = 3032453) B3032453
theorem B3411517 : Blo 2021435 3411517 := bbase (se 3 (by rfl) ⟨639659, by rfl⟩ : syracuseStep 3411517 = 1279319) (by norm_num)
theorem B4548689 : Blo 2021435 4548689 := bstep (se 2 (by rfl) ⟨1705758, by rfl⟩ : syracuseStep 4548689 = 3411517) B3411517
theorem B3032459 : Blo 2021435 3032459 := bstep (se 1 (by rfl) ⟨2274344, by rfl⟩ : syracuseStep 3032459 = 4548689) B4548689
theorem B2021639 : Blo 2021435 2021639 := bstep (se 1 (by rfl) ⟨1516229, by rfl⟩ : syracuseStep 2021639 = 3032459) B3032459
theorem B2274349 : Blo 2021435 2274349 := bbase (se 3 (by rfl) ⟨426440, by rfl⟩ : syracuseStep 2274349 = 852881) (by norm_num)
theorem B3032465 : Blo 2021435 3032465 := bstep (se 2 (by rfl) ⟨1137174, by rfl⟩ : syracuseStep 3032465 = 2274349) B2274349
theorem B2021643 : Blo 2021435 2021643 := bstep (se 1 (by rfl) ⟨1516232, by rfl⟩ : syracuseStep 2021643 = 3032465) B3032465
theorem B6823061 : Blo 2021435 6823061 := bbase (se 6 (by rfl) ⟨159915, by rfl⟩ : syracuseStep 6823061 = 319831) (by norm_num)
theorem B4548707 : Blo 2021435 4548707 := bstep (se 1 (by rfl) ⟨3411530, by rfl⟩ : syracuseStep 4548707 = 6823061) B6823061
theorem B3032471 : Blo 2021435 3032471 := bstep (se 1 (by rfl) ⟨2274353, by rfl⟩ : syracuseStep 3032471 = 4548707) B4548707
theorem B2021647 : Blo 2021435 2021647 := bstep (se 1 (by rfl) ⟨1516235, by rfl⟩ : syracuseStep 2021647 = 3032471) B3032471
theorem B3032477 : Blo 2021435 3032477 := bbase (se 3 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 3032477 = 1137179) (by norm_num)
theorem B2021651 : Blo 2021435 2021651 := bstep (se 1 (by rfl) ⟨1516238, by rfl⟩ : syracuseStep 2021651 = 3032477) B3032477
theorem B4548725 : Blo 2021435 4548725 := bbase (se 5 (by rfl) ⟨213221, by rfl⟩ : syracuseStep 4548725 = 426443) (by norm_num)
theorem B3032483 : Blo 2021435 3032483 := bstep (se 1 (by rfl) ⟨2274362, by rfl⟩ : syracuseStep 3032483 = 4548725) B4548725
theorem B2021655 : Blo 2021435 2021655 := bstep (se 1 (by rfl) ⟨1516241, by rfl⟩ : syracuseStep 2021655 = 3032483) B3032483
theorem B3238309 : Blo 2021435 3238309 := bbase (se 4 (by rfl) ⟨303591, by rfl⟩ : syracuseStep 3238309 = 607183) (by norm_num)
theorem B17270981 : Blo 2021435 17270981 := bstep (se 4 (by rfl) ⟨1619154, by rfl⟩ : syracuseStep 17270981 = 3238309) B3238309
theorem B11513987 : Blo 2021435 11513987 := bstep (se 1 (by rfl) ⟨8635490, by rfl⟩ : syracuseStep 11513987 = 17270981) B17270981
theorem B7675991 : Blo 2021435 7675991 := bstep (se 1 (by rfl) ⟨5756993, by rfl⟩ : syracuseStep 7675991 = 11513987) B11513987
theorem B5117327 : Blo 2021435 5117327 := bstep (se 1 (by rfl) ⟨3837995, by rfl⟩ : syracuseStep 5117327 = 7675991) B7675991
theorem B3411551 : Blo 2021435 3411551 := bstep (se 1 (by rfl) ⟨2558663, by rfl⟩ : syracuseStep 3411551 = 5117327) B5117327
theorem B2274367 : Blo 2021435 2274367 := bstep (se 1 (by rfl) ⟨1705775, by rfl⟩ : syracuseStep 2274367 = 3411551) B3411551
theorem B3032489 : Blo 2021435 3032489 := bstep (se 2 (by rfl) ⟨1137183, by rfl⟩ : syracuseStep 3032489 = 2274367) B2274367
theorem B2021659 : Blo 2021435 2021659 := bstep (se 1 (by rfl) ⟨1516244, by rfl⟩ : syracuseStep 2021659 = 3032489) B3032489
theorem B7676005 : Blo 2021435 7676005 := bbase (se 4 (by rfl) ⟨719625, by rfl⟩ : syracuseStep 7676005 = 1439251) (by norm_num)
theorem B10234673 : Blo 2021435 10234673 := bstep (se 2 (by rfl) ⟨3838002, by rfl⟩ : syracuseStep 10234673 = 7676005) B7676005
theorem B6823115 : Blo 2021435 6823115 := bstep (se 1 (by rfl) ⟨5117336, by rfl⟩ : syracuseStep 6823115 = 10234673) B10234673
theorem B4548743 : Blo 2021435 4548743 := bstep (se 1 (by rfl) ⟨3411557, by rfl⟩ : syracuseStep 4548743 = 6823115) B6823115
theorem B3032495 : Blo 2021435 3032495 := bstep (se 1 (by rfl) ⟨2274371, by rfl⟩ : syracuseStep 3032495 = 4548743) B4548743
theorem B2021663 : Blo 2021435 2021663 := bstep (se 1 (by rfl) ⟨1516247, by rfl⟩ : syracuseStep 2021663 = 3032495) B3032495
theorem B3032501 : Blo 2021435 3032501 := bbase (se 5 (by rfl) ⟨142148, by rfl⟩ : syracuseStep 3032501 = 284297) (by norm_num)
theorem B2021667 : Blo 2021435 2021667 := bstep (se 1 (by rfl) ⟨1516250, by rfl⟩ : syracuseStep 2021667 = 3032501) B3032501
theorem B5117357 : Blo 2021435 5117357 := bbase (se 3 (by rfl) ⟨959504, by rfl⟩ : syracuseStep 5117357 = 1919009) (by norm_num)
theorem B3411571 : Blo 2021435 3411571 := bstep (se 1 (by rfl) ⟨2558678, by rfl⟩ : syracuseStep 3411571 = 5117357) B5117357
theorem B4548761 : Blo 2021435 4548761 := bstep (se 2 (by rfl) ⟨1705785, by rfl⟩ : syracuseStep 4548761 = 3411571) B3411571
theorem B3032507 : Blo 2021435 3032507 := bstep (se 1 (by rfl) ⟨2274380, by rfl⟩ : syracuseStep 3032507 = 4548761) B4548761
theorem B2021671 : Blo 2021435 2021671 := bstep (se 1 (by rfl) ⟨1516253, by rfl⟩ : syracuseStep 2021671 = 3032507) B3032507
theorem B2274385 : Blo 2021435 2274385 := bbase (se 2 (by rfl) ⟨852894, by rfl⟩ : syracuseStep 2274385 = 1705789) (by norm_num)
theorem B3032513 : Blo 2021435 3032513 := bstep (se 2 (by rfl) ⟨1137192, by rfl⟩ : syracuseStep 3032513 = 2274385) B2274385
theorem B2021675 : Blo 2021435 2021675 := bstep (se 1 (by rfl) ⟨1516256, by rfl⟩ : syracuseStep 2021675 = 3032513) B3032513
theorem B2878525 : Blo 2021435 2878525 := bbase (se 3 (by rfl) ⟨539723, by rfl⟩ : syracuseStep 2878525 = 1079447) (by norm_num)
theorem B3838033 : Blo 2021435 3838033 := bstep (se 2 (by rfl) ⟨1439262, by rfl⟩ : syracuseStep 3838033 = 2878525) B2878525
theorem B5117377 : Blo 2021435 5117377 := bstep (se 2 (by rfl) ⟨1919016, by rfl⟩ : syracuseStep 5117377 = 3838033) B3838033
theorem B6823169 : Blo 2021435 6823169 := bstep (se 2 (by rfl) ⟨2558688, by rfl⟩ : syracuseStep 6823169 = 5117377) B5117377
theorem B4548779 : Blo 2021435 4548779 := bstep (se 1 (by rfl) ⟨3411584, by rfl⟩ : syracuseStep 4548779 = 6823169) B6823169
theorem B3032519 : Blo 2021435 3032519 := bstep (se 1 (by rfl) ⟨2274389, by rfl⟩ : syracuseStep 3032519 = 4548779) B4548779
theorem B2021679 : Blo 2021435 2021679 := bstep (se 1 (by rfl) ⟨1516259, by rfl⟩ : syracuseStep 2021679 = 3032519) B3032519
theorem B3032525 : Blo 2021435 3032525 := bbase (se 3 (by rfl) ⟨568598, by rfl⟩ : syracuseStep 3032525 = 1137197) (by norm_num)
theorem B2021683 : Blo 2021435 2021683 := bstep (se 1 (by rfl) ⟨1516262, by rfl⟩ : syracuseStep 2021683 = 3032525) B3032525
theorem B4548797 : Blo 2021435 4548797 := bbase (se 3 (by rfl) ⟨852899, by rfl⟩ : syracuseStep 4548797 = 1705799) (by norm_num)
theorem B3032531 : Blo 2021435 3032531 := bstep (se 1 (by rfl) ⟨2274398, by rfl⟩ : syracuseStep 3032531 = 4548797) B4548797
theorem B2021687 : Blo 2021435 2021687 := bstep (se 1 (by rfl) ⟨1516265, by rfl⟩ : syracuseStep 2021687 = 3032531) B3032531
theorem B3411605 : Blo 2021435 3411605 := bbase (se 6 (by rfl) ⟨79959, by rfl⟩ : syracuseStep 3411605 = 159919) (by norm_num)
theorem B2274403 : Blo 2021435 2274403 := bstep (se 1 (by rfl) ⟨1705802, by rfl⟩ : syracuseStep 2274403 = 3411605) B3411605
theorem B3032537 : Blo 2021435 3032537 := bstep (se 2 (by rfl) ⟨1137201, by rfl⟩ : syracuseStep 3032537 = 2274403) B2274403
theorem B2021691 : Blo 2021435 2021691 := bstep (se 1 (by rfl) ⟨1516268, by rfl⟩ : syracuseStep 2021691 = 3032537) B3032537
theorem B11671285 : Blo 2021435 11671285 := bbase (se 5 (by rfl) ⟨547091, by rfl⟩ : syracuseStep 11671285 = 1094183) (by norm_num)
theorem B15561713 : Blo 2021435 15561713 := bstep (se 2 (by rfl) ⟨5835642, by rfl⟩ : syracuseStep 15561713 = 11671285) B11671285
theorem B10374475 : Blo 2021435 10374475 := bstep (se 1 (by rfl) ⟨7780856, by rfl⟩ : syracuseStep 10374475 = 15561713) B15561713
theorem B13832633 : Blo 2021435 13832633 := bstep (se 2 (by rfl) ⟨5187237, by rfl⟩ : syracuseStep 13832633 = 10374475) B10374475
theorem B36887021 : Blo 2021435 36887021 := bstep (se 3 (by rfl) ⟨6916316, by rfl⟩ : syracuseStep 36887021 = 13832633) B13832633
theorem B24591347 : Blo 2021435 24591347 := bstep (se 1 (by rfl) ⟨18443510, by rfl⟩ : syracuseStep 24591347 = 36887021) B36887021
theorem B16394231 : Blo 2021435 16394231 := bstep (se 1 (by rfl) ⟨12295673, by rfl⟩ : syracuseStep 16394231 = 24591347) B24591347
theorem B10929487 : Blo 2021435 10929487 := bstep (se 1 (by rfl) ⟨8197115, by rfl⟩ : syracuseStep 10929487 = 16394231) B16394231
theorem B14572649 : Blo 2021435 14572649 := bstep (se 2 (by rfl) ⟨5464743, by rfl⟩ : syracuseStep 14572649 = 10929487) B10929487
theorem B9715099 : Blo 2021435 9715099 := bstep (se 1 (by rfl) ⟨7286324, by rfl⟩ : syracuseStep 9715099 = 14572649) B14572649
theorem B12953465 : Blo 2021435 12953465 := bstep (se 2 (by rfl) ⟨4857549, by rfl⟩ : syracuseStep 12953465 = 9715099) B9715099
theorem B8635643 : Blo 2021435 8635643 := bstep (se 1 (by rfl) ⟨6476732, by rfl⟩ : syracuseStep 8635643 = 12953465) B12953465
theorem B5757095 : Blo 2021435 5757095 := bstep (se 1 (by rfl) ⟨4317821, by rfl⟩ : syracuseStep 5757095 = 8635643) B8635643
theorem B15352253 : Blo 2021435 15352253 := bstep (se 3 (by rfl) ⟨2878547, by rfl⟩ : syracuseStep 15352253 = 5757095) B5757095
theorem B10234835 : Blo 2021435 10234835 := bstep (se 1 (by rfl) ⟨7676126, by rfl⟩ : syracuseStep 10234835 = 15352253) B15352253
theorem B6823223 : Blo 2021435 6823223 := bstep (se 1 (by rfl) ⟨5117417, by rfl⟩ : syracuseStep 6823223 = 10234835) B10234835
theorem B4548815 : Blo 2021435 4548815 := bstep (se 1 (by rfl) ⟨3411611, by rfl⟩ : syracuseStep 4548815 = 6823223) B6823223
theorem B3032543 : Blo 2021435 3032543 := bstep (se 1 (by rfl) ⟨2274407, by rfl⟩ : syracuseStep 3032543 = 4548815) B4548815
theorem B2021695 : Blo 2021435 2021695 := bstep (se 1 (by rfl) ⟨1516271, by rfl⟩ : syracuseStep 2021695 = 3032543) B3032543
theorem B3032549 : Blo 2021435 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B2021699 : Blo 2021435 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B3458173 : Blo 2021435 3458173 := bbase (se 3 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 3458173 = 1296815) (by norm_num)
theorem B4610897 : Blo 2021435 4610897 := bstep (se 2 (by rfl) ⟨1729086, by rfl⟩ : syracuseStep 4610897 = 3458173) B3458173
theorem B3073931 : Blo 2021435 3073931 := bstep (se 1 (by rfl) ⟨2305448, by rfl⟩ : syracuseStep 3073931 = 4610897) B4610897
theorem B32788597 : Blo 2021435 32788597 := bstep (se 5 (by rfl) ⟨1536965, by rfl⟩ : syracuseStep 32788597 = 3073931) B3073931
theorem B43718129 : Blo 2021435 43718129 := bstep (se 2 (by rfl) ⟨16394298, by rfl⟩ : syracuseStep 43718129 = 32788597) B32788597
theorem B29145419 : Blo 2021435 29145419 := bstep (se 1 (by rfl) ⟨21859064, by rfl⟩ : syracuseStep 29145419 = 43718129) B43718129
theorem B19430279 : Blo 2021435 19430279 := bstep (se 1 (by rfl) ⟨14572709, by rfl⟩ : syracuseStep 19430279 = 29145419) B29145419
theorem B12953519 : Blo 2021435 12953519 := bstep (se 1 (by rfl) ⟨9715139, by rfl⟩ : syracuseStep 12953519 = 19430279) B19430279
theorem B8635679 : Blo 2021435 8635679 := bstep (se 1 (by rfl) ⟨6476759, by rfl⟩ : syracuseStep 8635679 = 12953519) B12953519
theorem B5757119 : Blo 2021435 5757119 := bstep (se 1 (by rfl) ⟨4317839, by rfl⟩ : syracuseStep 5757119 = 8635679) B8635679
theorem B3838079 : Blo 2021435 3838079 := bstep (se 1 (by rfl) ⟨2878559, by rfl⟩ : syracuseStep 3838079 = 5757119) B5757119
theorem B2558719 : Blo 2021435 2558719 := bstep (se 1 (by rfl) ⟨1919039, by rfl⟩ : syracuseStep 2558719 = 3838079) B3838079
theorem B3411625 : Blo 2021435 3411625 := bstep (se 2 (by rfl) ⟨1279359, by rfl⟩ : syracuseStep 3411625 = 2558719) B2558719
theorem B4548833 : Blo 2021435 4548833 := bstep (se 2 (by rfl) ⟨1705812, by rfl⟩ : syracuseStep 4548833 = 3411625) B3411625
theorem B3032555 : Blo 2021435 3032555 := bstep (se 1 (by rfl) ⟨2274416, by rfl⟩ : syracuseStep 3032555 = 4548833) B4548833
theorem B2021703 : Blo 2021435 2021703 := bstep (se 1 (by rfl) ⟨1516277, by rfl⟩ : syracuseStep 2021703 = 3032555) B3032555
theorem B2274421 : Blo 2021435 2274421 := bbase (se 5 (by rfl) ⟨106613, by rfl⟩ : syracuseStep 2274421 = 213227) (by norm_num)
theorem B3032561 : Blo 2021435 3032561 := bstep (se 2 (by rfl) ⟨1137210, by rfl⟩ : syracuseStep 3032561 = 2274421) B2274421
theorem B2021707 : Blo 2021435 2021707 := bstep (se 1 (by rfl) ⟨1516280, by rfl⟩ : syracuseStep 2021707 = 3032561) B3032561
theorem B2558729 : Blo 2021435 2558729 := bbase (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) (by norm_num)
theorem B6823277 : Blo 2021435 6823277 := bstep (se 3 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 6823277 = 2558729) B2558729
theorem B4548851 : Blo 2021435 4548851 := bstep (se 1 (by rfl) ⟨3411638, by rfl⟩ : syracuseStep 4548851 = 6823277) B6823277
theorem B3032567 : Blo 2021435 3032567 := bstep (se 1 (by rfl) ⟨2274425, by rfl⟩ : syracuseStep 3032567 = 4548851) B4548851
theorem B2021711 : Blo 2021435 2021711 := bstep (se 1 (by rfl) ⟨1516283, by rfl⟩ : syracuseStep 2021711 = 3032567) B3032567
theorem B3032573 : Blo 2021435 3032573 := bbase (se 3 (by rfl) ⟨568607, by rfl⟩ : syracuseStep 3032573 = 1137215) (by norm_num)
theorem B2021715 : Blo 2021435 2021715 := bstep (se 1 (by rfl) ⟨1516286, by rfl⟩ : syracuseStep 2021715 = 3032573) B3032573
theorem B4548869 : Blo 2021435 4548869 := bbase (se 4 (by rfl) ⟨426456, by rfl⟩ : syracuseStep 4548869 = 852913) (by norm_num)
theorem B3032579 : Blo 2021435 3032579 := bstep (se 1 (by rfl) ⟨2274434, by rfl⟩ : syracuseStep 3032579 = 4548869) B4548869
theorem B2021719 : Blo 2021435 2021719 := bstep (se 1 (by rfl) ⟨1516289, by rfl⟩ : syracuseStep 2021719 = 3032579) B3032579
theorem B3838117 : Blo 2021435 3838117 := bbase (se 4 (by rfl) ⟨359823, by rfl⟩ : syracuseStep 3838117 = 719647) (by norm_num)
theorem B5117489 : Blo 2021435 5117489 := bstep (se 2 (by rfl) ⟨1919058, by rfl⟩ : syracuseStep 5117489 = 3838117) B3838117
theorem B3411659 : Blo 2021435 3411659 := bstep (se 1 (by rfl) ⟨2558744, by rfl⟩ : syracuseStep 3411659 = 5117489) B5117489
theorem B2274439 : Blo 2021435 2274439 := bstep (se 1 (by rfl) ⟨1705829, by rfl⟩ : syracuseStep 2274439 = 3411659) B3411659
theorem B3032585 : Blo 2021435 3032585 := bstep (se 2 (by rfl) ⟨1137219, by rfl⟩ : syracuseStep 3032585 = 2274439) B2274439
theorem B2021723 : Blo 2021435 2021723 := bstep (se 1 (by rfl) ⟨1516292, by rfl⟩ : syracuseStep 2021723 = 3032585) B3032585
theorem B10234997 : Blo 2021435 10234997 := bbase (se 5 (by rfl) ⟨479765, by rfl⟩ : syracuseStep 10234997 = 959531) (by norm_num)
theorem B6823331 : Blo 2021435 6823331 := bstep (se 1 (by rfl) ⟨5117498, by rfl⟩ : syracuseStep 6823331 = 10234997) B10234997
theorem B4548887 : Blo 2021435 4548887 := bstep (se 1 (by rfl) ⟨3411665, by rfl⟩ : syracuseStep 4548887 = 6823331) B6823331
theorem B3032591 : Blo 2021435 3032591 := bstep (se 1 (by rfl) ⟨2274443, by rfl⟩ : syracuseStep 3032591 = 4548887) B4548887
theorem B2021727 : Blo 2021435 2021727 := bstep (se 1 (by rfl) ⟨1516295, by rfl⟩ : syracuseStep 2021727 = 3032591) B3032591
theorem B3032597 : Blo 2021435 3032597 := bbase (se 6 (by rfl) ⟨71076, by rfl⟩ : syracuseStep 3032597 = 142153) (by norm_num)
theorem B2021731 : Blo 2021435 2021731 := bstep (se 1 (by rfl) ⟨1516298, by rfl⟩ : syracuseStep 2021731 = 3032597) B3032597
theorem B5464853 : Blo 2021435 5464853 := bbase (se 6 (by rfl) ⟨128082, by rfl⟩ : syracuseStep 5464853 = 256165) (by norm_num)
theorem B3643235 : Blo 2021435 3643235 := bstep (se 1 (by rfl) ⟨2732426, by rfl⟩ : syracuseStep 3643235 = 5464853) B5464853
theorem B2428823 : Blo 2021435 2428823 := bstep (se 1 (by rfl) ⟨1821617, by rfl⟩ : syracuseStep 2428823 = 3643235) B3643235
theorem B6476861 : Blo 2021435 6476861 := bstep (se 3 (by rfl) ⟨1214411, by rfl⟩ : syracuseStep 6476861 = 2428823) B2428823
theorem B17271629 : Blo 2021435 17271629 := bstep (se 3 (by rfl) ⟨3238430, by rfl⟩ : syracuseStep 17271629 = 6476861) B6476861
theorem B11514419 : Blo 2021435 11514419 := bstep (se 1 (by rfl) ⟨8635814, by rfl⟩ : syracuseStep 11514419 = 17271629) B17271629
theorem B7676279 : Blo 2021435 7676279 := bstep (se 1 (by rfl) ⟨5757209, by rfl⟩ : syracuseStep 7676279 = 11514419) B11514419
theorem B5117519 : Blo 2021435 5117519 := bstep (se 1 (by rfl) ⟨3838139, by rfl⟩ : syracuseStep 5117519 = 7676279) B7676279
theorem B3411679 : Blo 2021435 3411679 := bstep (se 1 (by rfl) ⟨2558759, by rfl⟩ : syracuseStep 3411679 = 5117519) B5117519
theorem B4548905 : Blo 2021435 4548905 := bstep (se 2 (by rfl) ⟨1705839, by rfl⟩ : syracuseStep 4548905 = 3411679) B3411679
theorem B3032603 : Blo 2021435 3032603 := bstep (se 1 (by rfl) ⟨2274452, by rfl⟩ : syracuseStep 3032603 = 4548905) B4548905
theorem B2021735 : Blo 2021435 2021735 := bstep (se 1 (by rfl) ⟨1516301, by rfl⟩ : syracuseStep 2021735 = 3032603) B3032603
theorem B2274457 : Blo 2021435 2274457 := bbase (se 2 (by rfl) ⟨852921, by rfl⟩ : syracuseStep 2274457 = 1705843) (by norm_num)
theorem B3032609 : Blo 2021435 3032609 := bstep (se 2 (by rfl) ⟨1137228, by rfl⟩ : syracuseStep 3032609 = 2274457) B2274457
theorem B2021739 : Blo 2021435 2021739 := bstep (se 1 (by rfl) ⟨1516304, by rfl⟩ : syracuseStep 2021739 = 3032609) B3032609
theorem B7676309 : Blo 2021435 7676309 := bbase (se 6 (by rfl) ⟨179913, by rfl⟩ : syracuseStep 7676309 = 359827) (by norm_num)
theorem B5117539 : Blo 2021435 5117539 := bstep (se 1 (by rfl) ⟨3838154, by rfl⟩ : syracuseStep 5117539 = 7676309) B7676309
theorem B6823385 : Blo 2021435 6823385 := bstep (se 2 (by rfl) ⟨2558769, by rfl⟩ : syracuseStep 6823385 = 5117539) B5117539
theorem B4548923 : Blo 2021435 4548923 := bstep (se 1 (by rfl) ⟨3411692, by rfl⟩ : syracuseStep 4548923 = 6823385) B6823385
theorem B3032615 : Blo 2021435 3032615 := bstep (se 1 (by rfl) ⟨2274461, by rfl⟩ : syracuseStep 3032615 = 4548923) B4548923
theorem B2021743 : Blo 2021435 2021743 := bstep (se 1 (by rfl) ⟨1516307, by rfl⟩ : syracuseStep 2021743 = 3032615) B3032615
theorem B3032621 : Blo 2021435 3032621 := bbase (se 3 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 3032621 = 1137233) (by norm_num)
theorem B2021747 : Blo 2021435 2021747 := bstep (se 1 (by rfl) ⟨1516310, by rfl⟩ : syracuseStep 2021747 = 3032621) B3032621
theorem B4548941 : Blo 2021435 4548941 := bbase (se 3 (by rfl) ⟨852926, by rfl⟩ : syracuseStep 4548941 = 1705853) (by norm_num)
theorem B3032627 : Blo 2021435 3032627 := bstep (se 1 (by rfl) ⟨2274470, by rfl⟩ : syracuseStep 3032627 = 4548941) B4548941
theorem B2021751 : Blo 2021435 2021751 := bstep (se 1 (by rfl) ⟨1516313, by rfl⟩ : syracuseStep 2021751 = 3032627) B3032627
theorem B2558785 : Blo 2021435 2558785 := bbase (se 2 (by rfl) ⟨959544, by rfl⟩ : syracuseStep 2558785 = 1919089) (by norm_num)
theorem B3411713 : Blo 2021435 3411713 := bstep (se 2 (by rfl) ⟨1279392, by rfl⟩ : syracuseStep 3411713 = 2558785) B2558785
theorem B2274475 : Blo 2021435 2274475 := bstep (se 1 (by rfl) ⟨1705856, by rfl⟩ : syracuseStep 2274475 = 3411713) B3411713
theorem B3032633 : Blo 2021435 3032633 := bstep (se 2 (by rfl) ⟨1137237, by rfl⟩ : syracuseStep 3032633 = 2274475) B2274475
theorem B2021755 : Blo 2021435 2021755 := bstep (se 1 (by rfl) ⟨1516316, by rfl⟩ : syracuseStep 2021755 = 3032633) B3032633
theorem B3238469 : Blo 2021435 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B2158979 : Blo 2021435 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B23029109 : Blo 2021435 23029109 := bstep (se 5 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 23029109 = 2158979) B2158979
theorem B15352739 : Blo 2021435 15352739 := bstep (se 1 (by rfl) ⟨11514554, by rfl⟩ : syracuseStep 15352739 = 23029109) B23029109
theorem B10235159 : Blo 2021435 10235159 := bstep (se 1 (by rfl) ⟨7676369, by rfl⟩ : syracuseStep 10235159 = 15352739) B15352739
theorem B6823439 : Blo 2021435 6823439 := bstep (se 1 (by rfl) ⟨5117579, by rfl⟩ : syracuseStep 6823439 = 10235159) B10235159
theorem B4548959 : Blo 2021435 4548959 := bstep (se 1 (by rfl) ⟨3411719, by rfl⟩ : syracuseStep 4548959 = 6823439) B6823439
theorem B3032639 : Blo 2021435 3032639 := bstep (se 1 (by rfl) ⟨2274479, by rfl⟩ : syracuseStep 3032639 = 4548959) B4548959
theorem B2021759 : Blo 2021435 2021759 := bstep (se 1 (by rfl) ⟨1516319, by rfl⟩ : syracuseStep 2021759 = 3032639) B3032639
theorem B3032645 : Blo 2021435 3032645 := bbase (se 4 (by rfl) ⟨284310, by rfl⟩ : syracuseStep 3032645 = 568621) (by norm_num)
theorem B2021763 : Blo 2021435 2021763 := bstep (se 1 (by rfl) ⟨1516322, by rfl⟩ : syracuseStep 2021763 = 3032645) B3032645
theorem B3411733 : Blo 2021435 3411733 := bbase (se 6 (by rfl) ⟨79962, by rfl⟩ : syracuseStep 3411733 = 159925) (by norm_num)
theorem B4548977 : Blo 2021435 4548977 := bstep (se 2 (by rfl) ⟨1705866, by rfl⟩ : syracuseStep 4548977 = 3411733) B3411733
theorem B3032651 : Blo 2021435 3032651 := bstep (se 1 (by rfl) ⟨2274488, by rfl⟩ : syracuseStep 3032651 = 4548977) B4548977
theorem B2021767 : Blo 2021435 2021767 := bstep (se 1 (by rfl) ⟨1516325, by rfl⟩ : syracuseStep 2021767 = 3032651) B3032651
theorem B2274493 : Blo 2021435 2274493 := bbase (se 3 (by rfl) ⟨426467, by rfl⟩ : syracuseStep 2274493 = 852935) (by norm_num)
theorem B3032657 : Blo 2021435 3032657 := bstep (se 2 (by rfl) ⟨1137246, by rfl⟩ : syracuseStep 3032657 = 2274493) B2274493
theorem B2021771 : Blo 2021435 2021771 := bstep (se 1 (by rfl) ⟨1516328, by rfl⟩ : syracuseStep 2021771 = 3032657) B3032657
theorem B6823493 : Blo 2021435 6823493 := bbase (se 4 (by rfl) ⟨639702, by rfl⟩ : syracuseStep 6823493 = 1279405) (by norm_num)
theorem B4548995 : Blo 2021435 4548995 := bstep (se 1 (by rfl) ⟨3411746, by rfl⟩ : syracuseStep 4548995 = 6823493) B6823493
theorem B3032663 : Blo 2021435 3032663 := bstep (se 1 (by rfl) ⟨2274497, by rfl⟩ : syracuseStep 3032663 = 4548995) B4548995
theorem B2021775 : Blo 2021435 2021775 := bstep (se 1 (by rfl) ⟨1516331, by rfl⟩ : syracuseStep 2021775 = 3032663) B3032663
theorem B3032669 : Blo 2021435 3032669 := bbase (se 3 (by rfl) ⟨568625, by rfl⟩ : syracuseStep 3032669 = 1137251) (by norm_num)
theorem B2021779 : Blo 2021435 2021779 := bstep (se 1 (by rfl) ⟨1516334, by rfl⟩ : syracuseStep 2021779 = 3032669) B3032669
theorem B4549013 : Blo 2021435 4549013 := bbase (se 6 (by rfl) ⟨106617, by rfl⟩ : syracuseStep 4549013 = 213235) (by norm_num)
theorem B3032675 : Blo 2021435 3032675 := bstep (se 1 (by rfl) ⟨2274506, by rfl⟩ : syracuseStep 3032675 = 4549013) B4549013
theorem B2021783 : Blo 2021435 2021783 := bstep (se 1 (by rfl) ⟨1516337, by rfl⟩ : syracuseStep 2021783 = 3032675) B3032675
theorem B6477029 : Blo 2021435 6477029 := bbase (se 4 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 6477029 = 1214443) (by norm_num)
theorem B4318019 : Blo 2021435 4318019 := bstep (se 1 (by rfl) ⟨3238514, by rfl⟩ : syracuseStep 4318019 = 6477029) B6477029
theorem B2878679 : Blo 2021435 2878679 := bstep (se 1 (by rfl) ⟨2159009, by rfl⟩ : syracuseStep 2878679 = 4318019) B4318019
theorem B7676477 : Blo 2021435 7676477 := bstep (se 3 (by rfl) ⟨1439339, by rfl⟩ : syracuseStep 7676477 = 2878679) B2878679
theorem B5117651 : Blo 2021435 5117651 := bstep (se 1 (by rfl) ⟨3838238, by rfl⟩ : syracuseStep 5117651 = 7676477) B7676477
theorem B3411767 : Blo 2021435 3411767 := bstep (se 1 (by rfl) ⟨2558825, by rfl⟩ : syracuseStep 3411767 = 5117651) B5117651
theorem B2274511 : Blo 2021435 2274511 := bstep (se 1 (by rfl) ⟨1705883, by rfl⟩ : syracuseStep 2274511 = 3411767) B3411767
theorem B3032681 : Blo 2021435 3032681 := bstep (se 2 (by rfl) ⟨1137255, by rfl⟩ : syracuseStep 3032681 = 2274511) B2274511
theorem B2021787 : Blo 2021435 2021787 := bstep (se 1 (by rfl) ⟨1516340, by rfl⟩ : syracuseStep 2021787 = 3032681) B3032681
theorem B8636053 : Blo 2021435 8636053 := bbase (se 6 (by rfl) ⟨202407, by rfl⟩ : syracuseStep 8636053 = 404815) (by norm_num)
theorem B11514737 : Blo 2021435 11514737 := bstep (se 2 (by rfl) ⟨4318026, by rfl⟩ : syracuseStep 11514737 = 8636053) B8636053
theorem B7676491 : Blo 2021435 7676491 := bstep (se 1 (by rfl) ⟨5757368, by rfl⟩ : syracuseStep 7676491 = 11514737) B11514737
theorem B10235321 : Blo 2021435 10235321 := bstep (se 2 (by rfl) ⟨3838245, by rfl⟩ : syracuseStep 10235321 = 7676491) B7676491
theorem B6823547 : Blo 2021435 6823547 := bstep (se 1 (by rfl) ⟨5117660, by rfl⟩ : syracuseStep 6823547 = 10235321) B10235321
theorem B4549031 : Blo 2021435 4549031 := bstep (se 1 (by rfl) ⟨3411773, by rfl⟩ : syracuseStep 4549031 = 6823547) B6823547
theorem B3032687 : Blo 2021435 3032687 := bstep (se 1 (by rfl) ⟨2274515, by rfl⟩ : syracuseStep 3032687 = 4549031) B4549031
theorem B2021791 : Blo 2021435 2021791 := bstep (se 1 (by rfl) ⟨1516343, by rfl⟩ : syracuseStep 2021791 = 3032687) B3032687
theorem B3032693 : Blo 2021435 3032693 := bbase (se 5 (by rfl) ⟨142157, by rfl⟩ : syracuseStep 3032693 = 284315) (by norm_num)
theorem B2021795 : Blo 2021435 2021795 := bstep (se 1 (by rfl) ⟨1516346, by rfl⟩ : syracuseStep 2021795 = 3032693) B3032693
theorem B3838261 : Blo 2021435 3838261 := bbase (se 5 (by rfl) ⟨179918, by rfl⟩ : syracuseStep 3838261 = 359837) (by norm_num)
theorem B5117681 : Blo 2021435 5117681 := bstep (se 2 (by rfl) ⟨1919130, by rfl⟩ : syracuseStep 5117681 = 3838261) B3838261
theorem B3411787 : Blo 2021435 3411787 := bstep (se 1 (by rfl) ⟨2558840, by rfl⟩ : syracuseStep 3411787 = 5117681) B5117681
theorem B4549049 : Blo 2021435 4549049 := bstep (se 2 (by rfl) ⟨1705893, by rfl⟩ : syracuseStep 4549049 = 3411787) B3411787
theorem B3032699 : Blo 2021435 3032699 := bstep (se 1 (by rfl) ⟨2274524, by rfl⟩ : syracuseStep 3032699 = 4549049) B4549049
theorem B2021799 : Blo 2021435 2021799 := bstep (se 1 (by rfl) ⟨1516349, by rfl⟩ : syracuseStep 2021799 = 3032699) B3032699
theorem B2274529 : Blo 2021435 2274529 := bbase (se 2 (by rfl) ⟨852948, by rfl⟩ : syracuseStep 2274529 = 1705897) (by norm_num)
theorem B3032705 : Blo 2021435 3032705 := bstep (se 2 (by rfl) ⟨1137264, by rfl⟩ : syracuseStep 3032705 = 2274529) B2274529
theorem B2021803 : Blo 2021435 2021803 := bstep (se 1 (by rfl) ⟨1516352, by rfl⟩ : syracuseStep 2021803 = 3032705) B3032705
theorem B5117701 : Blo 2021435 5117701 := bbase (se 4 (by rfl) ⟨479784, by rfl⟩ : syracuseStep 5117701 = 959569) (by norm_num)
theorem B6823601 : Blo 2021435 6823601 := bstep (se 2 (by rfl) ⟨2558850, by rfl⟩ : syracuseStep 6823601 = 5117701) B5117701
theorem B4549067 : Blo 2021435 4549067 := bstep (se 1 (by rfl) ⟨3411800, by rfl⟩ : syracuseStep 4549067 = 6823601) B6823601
theorem B3032711 : Blo 2021435 3032711 := bstep (se 1 (by rfl) ⟨2274533, by rfl⟩ : syracuseStep 3032711 = 4549067) B4549067
theorem B2021807 : Blo 2021435 2021807 := bstep (se 1 (by rfl) ⟨1516355, by rfl⟩ : syracuseStep 2021807 = 3032711) B3032711
theorem B3032717 : Blo 2021435 3032717 := bbase (se 3 (by rfl) ⟨568634, by rfl⟩ : syracuseStep 3032717 = 1137269) (by norm_num)
theorem B2021811 : Blo 2021435 2021811 := bstep (se 1 (by rfl) ⟨1516358, by rfl⟩ : syracuseStep 2021811 = 3032717) B3032717
theorem B4549085 : Blo 2021435 4549085 := bbase (se 3 (by rfl) ⟨852953, by rfl⟩ : syracuseStep 4549085 = 1705907) (by norm_num)
theorem B3032723 : Blo 2021435 3032723 := bstep (se 1 (by rfl) ⟨2274542, by rfl⟩ : syracuseStep 3032723 = 4549085) B4549085
theorem B2021815 : Blo 2021435 2021815 := bstep (se 1 (by rfl) ⟨1516361, by rfl⟩ : syracuseStep 2021815 = 3032723) B3032723
theorem B3411821 : Blo 2021435 3411821 := bbase (se 3 (by rfl) ⟨639716, by rfl⟩ : syracuseStep 3411821 = 1279433) (by norm_num)
theorem B2274547 : Blo 2021435 2274547 := bstep (se 1 (by rfl) ⟨1705910, by rfl⟩ : syracuseStep 2274547 = 3411821) B3411821
theorem B3032729 : Blo 2021435 3032729 := bstep (se 2 (by rfl) ⟨1137273, by rfl⟩ : syracuseStep 3032729 = 2274547) B2274547
theorem B2021819 : Blo 2021435 2021819 := bstep (se 1 (by rfl) ⟨1516364, by rfl⟩ : syracuseStep 2021819 = 3032729) B3032729
theorem B2305585 : Blo 2021435 2305585 := bbase (se 2 (by rfl) ⟨864594, by rfl⟩ : syracuseStep 2305585 = 1729189) (by norm_num)
theorem B3074113 : Blo 2021435 3074113 := bstep (se 2 (by rfl) ⟨1152792, by rfl⟩ : syracuseStep 3074113 = 2305585) B2305585
theorem B4098817 : Blo 2021435 4098817 := bstep (se 2 (by rfl) ⟨1537056, by rfl⟩ : syracuseStep 4098817 = 3074113) B3074113
theorem B5465089 : Blo 2021435 5465089 := bstep (se 2 (by rfl) ⟨2049408, by rfl⟩ : syracuseStep 5465089 = 4098817) B4098817
theorem B29147141 : Blo 2021435 29147141 := bstep (se 4 (by rfl) ⟨2732544, by rfl⟩ : syracuseStep 29147141 = 5465089) B5465089
theorem B19431427 : Blo 2021435 19431427 := bstep (se 1 (by rfl) ⟨14573570, by rfl⟩ : syracuseStep 19431427 = 29147141) B29147141
theorem B25908569 : Blo 2021435 25908569 := bstep (se 2 (by rfl) ⟨9715713, by rfl⟩ : syracuseStep 25908569 = 19431427) B19431427
theorem B17272379 : Blo 2021435 17272379 := bstep (se 1 (by rfl) ⟨12954284, by rfl⟩ : syracuseStep 17272379 = 25908569) B25908569
theorem B11514919 : Blo 2021435 11514919 := bstep (se 1 (by rfl) ⟨8636189, by rfl⟩ : syracuseStep 11514919 = 17272379) B17272379
theorem B15353225 : Blo 2021435 15353225 := bstep (se 2 (by rfl) ⟨5757459, by rfl⟩ : syracuseStep 15353225 = 11514919) B11514919
theorem B10235483 : Blo 2021435 10235483 := bstep (se 1 (by rfl) ⟨7676612, by rfl⟩ : syracuseStep 10235483 = 15353225) B15353225
theorem B6823655 : Blo 2021435 6823655 := bstep (se 1 (by rfl) ⟨5117741, by rfl⟩ : syracuseStep 6823655 = 10235483) B10235483
theorem B4549103 : Blo 2021435 4549103 := bstep (se 1 (by rfl) ⟨3411827, by rfl⟩ : syracuseStep 4549103 = 6823655) B6823655
theorem B3032735 : Blo 2021435 3032735 := bstep (se 1 (by rfl) ⟨2274551, by rfl⟩ : syracuseStep 3032735 = 4549103) B4549103
theorem B2021823 : Blo 2021435 2021823 := bstep (se 1 (by rfl) ⟨1516367, by rfl⟩ : syracuseStep 2021823 = 3032735) B3032735
theorem B3032741 : Blo 2021435 3032741 := bbase (se 4 (by rfl) ⟨284319, by rfl⟩ : syracuseStep 3032741 = 568639) (by norm_num)
theorem B2021827 : Blo 2021435 2021827 := bstep (se 1 (by rfl) ⟨1516370, by rfl⟩ : syracuseStep 2021827 = 3032741) B3032741
theorem B2558881 : Blo 2021435 2558881 := bbase (se 2 (by rfl) ⟨959580, by rfl⟩ : syracuseStep 2558881 = 1919161) (by norm_num)
theorem B3411841 : Blo 2021435 3411841 := bstep (se 2 (by rfl) ⟨1279440, by rfl⟩ : syracuseStep 3411841 = 2558881) B2558881
theorem B4549121 : Blo 2021435 4549121 := bstep (se 2 (by rfl) ⟨1705920, by rfl⟩ : syracuseStep 4549121 = 3411841) B3411841
theorem B3032747 : Blo 2021435 3032747 := bstep (se 1 (by rfl) ⟨2274560, by rfl⟩ : syracuseStep 3032747 = 4549121) B4549121
theorem B2021831 : Blo 2021435 2021831 := bstep (se 1 (by rfl) ⟨1516373, by rfl⟩ : syracuseStep 2021831 = 3032747) B3032747
theorem B2274565 : Blo 2021435 2274565 := bbase (se 4 (by rfl) ⟨213240, by rfl⟩ : syracuseStep 2274565 = 426481) (by norm_num)
theorem B3032753 : Blo 2021435 3032753 := bstep (se 2 (by rfl) ⟨1137282, by rfl⟩ : syracuseStep 3032753 = 2274565) B2274565
theorem B2021835 : Blo 2021435 2021835 := bstep (se 1 (by rfl) ⟨1516376, by rfl⟩ : syracuseStep 2021835 = 3032753) B3032753
theorem B2159065 : Blo 2021435 2159065 := bbase (se 2 (by rfl) ⟨809649, by rfl⟩ : syracuseStep 2159065 = 1619299) (by norm_num)
theorem B2878753 : Blo 2021435 2878753 := bstep (se 2 (by rfl) ⟨1079532, by rfl⟩ : syracuseStep 2878753 = 2159065) B2159065
theorem B3838337 : Blo 2021435 3838337 := bstep (se 2 (by rfl) ⟨1439376, by rfl⟩ : syracuseStep 3838337 = 2878753) B2878753
theorem B2558891 : Blo 2021435 2558891 := bstep (se 1 (by rfl) ⟨1919168, by rfl⟩ : syracuseStep 2558891 = 3838337) B3838337
theorem B6823709 : Blo 2021435 6823709 := bstep (se 3 (by rfl) ⟨1279445, by rfl⟩ : syracuseStep 6823709 = 2558891) B2558891
theorem B4549139 : Blo 2021435 4549139 := bstep (se 1 (by rfl) ⟨3411854, by rfl⟩ : syracuseStep 4549139 = 6823709) B6823709
theorem B3032759 : Blo 2021435 3032759 := bstep (se 1 (by rfl) ⟨2274569, by rfl⟩ : syracuseStep 3032759 = 4549139) B4549139
theorem B2021839 : Blo 2021435 2021839 := bstep (se 1 (by rfl) ⟨1516379, by rfl⟩ : syracuseStep 2021839 = 3032759) B3032759
theorem B3032765 : Blo 2021435 3032765 := bbase (se 3 (by rfl) ⟨568643, by rfl⟩ : syracuseStep 3032765 = 1137287) (by norm_num)
theorem B2021843 : Blo 2021435 2021843 := bstep (se 1 (by rfl) ⟨1516382, by rfl⟩ : syracuseStep 2021843 = 3032765) B3032765
theorem B4549157 : Blo 2021435 4549157 := bbase (se 4 (by rfl) ⟨426483, by rfl⟩ : syracuseStep 4549157 = 852967) (by norm_num)
theorem B3032771 : Blo 2021435 3032771 := bstep (se 1 (by rfl) ⟨2274578, by rfl⟩ : syracuseStep 3032771 = 4549157) B4549157
theorem B2021847 : Blo 2021435 2021847 := bstep (se 1 (by rfl) ⟨1516385, by rfl⟩ : syracuseStep 2021847 = 3032771) B3032771
theorem B5117813 : Blo 2021435 5117813 := bbase (se 5 (by rfl) ⟨239897, by rfl⟩ : syracuseStep 5117813 = 479795) (by norm_num)
theorem B3411875 : Blo 2021435 3411875 := bstep (se 1 (by rfl) ⟨2558906, by rfl⟩ : syracuseStep 3411875 = 5117813) B5117813
theorem B2274583 : Blo 2021435 2274583 := bstep (se 1 (by rfl) ⟨1705937, by rfl⟩ : syracuseStep 2274583 = 3411875) B3411875
theorem B3032777 : Blo 2021435 3032777 := bstep (se 2 (by rfl) ⟨1137291, by rfl⟩ : syracuseStep 3032777 = 2274583) B2274583
theorem B2021851 : Blo 2021435 2021851 := bstep (se 1 (by rfl) ⟨1516388, by rfl⟩ : syracuseStep 2021851 = 3032777) B3032777
theorem B5258429 : Blo 2021435 5258429 := bbase (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) (by norm_num)
theorem B3505619 : Blo 2021435 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B9348317 : Blo 2021435 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B6232211 : Blo 2021435 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B4154807 : Blo 2021435 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B2769871 : Blo 2021435 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B3693161 : Blo 2021435 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B2462107 : Blo 2021435 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B3282809 : Blo 2021435 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B8754157 : Blo 2021435 8754157 := bstep (se 3 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 8754157 = 3282809) B3282809
theorem B11672209 : Blo 2021435 11672209 := bstep (se 2 (by rfl) ⟨4377078, by rfl⟩ : syracuseStep 11672209 = 8754157) B8754157
theorem B15562945 : Blo 2021435 15562945 := bstep (se 2 (by rfl) ⟨5836104, by rfl⟩ : syracuseStep 15562945 = 11672209) B11672209
theorem B20750593 : Blo 2021435 20750593 := bstep (se 2 (by rfl) ⟨7781472, by rfl⟩ : syracuseStep 20750593 = 15562945) B15562945
theorem B27667457 : Blo 2021435 27667457 := bstep (se 2 (by rfl) ⟨10375296, by rfl⟩ : syracuseStep 27667457 = 20750593) B20750593
theorem B18444971 : Blo 2021435 18444971 := bstep (se 1 (by rfl) ⟨13833728, by rfl⟩ : syracuseStep 18444971 = 27667457) B27667457
theorem B12296647 : Blo 2021435 12296647 := bstep (se 1 (by rfl) ⟨9222485, by rfl⟩ : syracuseStep 12296647 = 18444971) B18444971
theorem B16395529 : Blo 2021435 16395529 := bstep (se 2 (by rfl) ⟨6148323, by rfl⟩ : syracuseStep 16395529 = 12296647) B12296647
theorem B21860705 : Blo 2021435 21860705 := bstep (se 2 (by rfl) ⟨8197764, by rfl⟩ : syracuseStep 21860705 = 16395529) B16395529
theorem B14573803 : Blo 2021435 14573803 := bstep (se 1 (by rfl) ⟨10930352, by rfl⟩ : syracuseStep 14573803 = 21860705) B21860705
theorem B19431737 : Blo 2021435 19431737 := bstep (se 2 (by rfl) ⟨7286901, by rfl⟩ : syracuseStep 19431737 = 14573803) B14573803
theorem B12954491 : Blo 2021435 12954491 := bstep (se 1 (by rfl) ⟨9715868, by rfl⟩ : syracuseStep 12954491 = 19431737) B19431737
theorem B8636327 : Blo 2021435 8636327 := bstep (se 1 (by rfl) ⟨6477245, by rfl⟩ : syracuseStep 8636327 = 12954491) B12954491
theorem B5757551 : Blo 2021435 5757551 := bstep (se 1 (by rfl) ⟨4318163, by rfl⟩ : syracuseStep 5757551 = 8636327) B8636327
theorem B3838367 : Blo 2021435 3838367 := bstep (se 1 (by rfl) ⟨2878775, by rfl⟩ : syracuseStep 3838367 = 5757551) B5757551
theorem B10235645 : Blo 2021435 10235645 := bstep (se 3 (by rfl) ⟨1919183, by rfl⟩ : syracuseStep 10235645 = 3838367) B3838367
theorem B6823763 : Blo 2021435 6823763 := bstep (se 1 (by rfl) ⟨5117822, by rfl⟩ : syracuseStep 6823763 = 10235645) B10235645
theorem B4549175 : Blo 2021435 4549175 := bstep (se 1 (by rfl) ⟨3411881, by rfl⟩ : syracuseStep 4549175 = 6823763) B6823763
theorem B3032783 : Blo 2021435 3032783 := bstep (se 1 (by rfl) ⟨2274587, by rfl⟩ : syracuseStep 3032783 = 4549175) B4549175
theorem B2021855 : Blo 2021435 2021855 := bstep (se 1 (by rfl) ⟨1516391, by rfl⟩ : syracuseStep 2021855 = 3032783) B3032783
theorem B3032789 : Blo 2021435 3032789 := bbase (se 7 (by rfl) ⟨35540, by rfl⟩ : syracuseStep 3032789 = 71081) (by norm_num)
theorem B2021859 : Blo 2021435 2021859 := bstep (se 1 (by rfl) ⟨1516394, by rfl⟩ : syracuseStep 2021859 = 3032789) B3032789
theorem B4318181 : Blo 2021435 4318181 := bbase (se 4 (by rfl) ⟨404829, by rfl⟩ : syracuseStep 4318181 = 809659) (by norm_num)
theorem B2878787 : Blo 2021435 2878787 := bstep (se 1 (by rfl) ⟨2159090, by rfl⟩ : syracuseStep 2878787 = 4318181) B4318181
theorem B7676765 : Blo 2021435 7676765 := bstep (se 3 (by rfl) ⟨1439393, by rfl⟩ : syracuseStep 7676765 = 2878787) B2878787
theorem B5117843 : Blo 2021435 5117843 := bstep (se 1 (by rfl) ⟨3838382, by rfl⟩ : syracuseStep 5117843 = 7676765) B7676765
theorem B3411895 : Blo 2021435 3411895 := bstep (se 1 (by rfl) ⟨2558921, by rfl⟩ : syracuseStep 3411895 = 5117843) B5117843
theorem B4549193 : Blo 2021435 4549193 := bstep (se 2 (by rfl) ⟨1705947, by rfl⟩ : syracuseStep 4549193 = 3411895) B3411895
theorem B3032795 : Blo 2021435 3032795 := bstep (se 1 (by rfl) ⟨2274596, by rfl⟩ : syracuseStep 3032795 = 4549193) B4549193
theorem B2021863 : Blo 2021435 2021863 := bstep (se 1 (by rfl) ⟨1516397, by rfl⟩ : syracuseStep 2021863 = 3032795) B3032795
theorem B2274601 : Blo 2021435 2274601 := bbase (se 2 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 2274601 = 1705951) (by norm_num)
theorem B3032801 : Blo 2021435 3032801 := bstep (se 2 (by rfl) ⟨1137300, by rfl⟩ : syracuseStep 3032801 = 2274601) B2274601
theorem B2021867 : Blo 2021435 2021867 := bstep (se 1 (by rfl) ⟨1516400, by rfl⟩ : syracuseStep 2021867 = 3032801) B3032801
theorem B4924253 : Blo 2021435 4924253 := bbase (se 3 (by rfl) ⟨923297, by rfl⟩ : syracuseStep 4924253 = 1846595) (by norm_num)
theorem B13131341 : Blo 2021435 13131341 := bstep (se 3 (by rfl) ⟨2462126, by rfl⟩ : syracuseStep 13131341 = 4924253) B4924253
theorem B8754227 : Blo 2021435 8754227 := bstep (se 1 (by rfl) ⟨6565670, by rfl⟩ : syracuseStep 8754227 = 13131341) B13131341
theorem B5836151 : Blo 2021435 5836151 := bstep (se 1 (by rfl) ⟨4377113, by rfl⟩ : syracuseStep 5836151 = 8754227) B8754227
theorem B15563069 : Blo 2021435 15563069 := bstep (se 3 (by rfl) ⟨2918075, by rfl⟩ : syracuseStep 15563069 = 5836151) B5836151
theorem B10375379 : Blo 2021435 10375379 := bstep (se 1 (by rfl) ⟨7781534, by rfl⟩ : syracuseStep 10375379 = 15563069) B15563069
theorem B6916919 : Blo 2021435 6916919 := bstep (se 1 (by rfl) ⟨5187689, by rfl⟩ : syracuseStep 6916919 = 10375379) B10375379
theorem B18445117 : Blo 2021435 18445117 := bstep (se 3 (by rfl) ⟨3458459, by rfl⟩ : syracuseStep 18445117 = 6916919) B6916919
theorem B24593489 : Blo 2021435 24593489 := bstep (se 2 (by rfl) ⟨9222558, by rfl⟩ : syracuseStep 24593489 = 18445117) B18445117
theorem B16395659 : Blo 2021435 16395659 := bstep (se 1 (by rfl) ⟨12296744, by rfl⟩ : syracuseStep 16395659 = 24593489) B24593489
theorem B10930439 : Blo 2021435 10930439 := bstep (se 1 (by rfl) ⟨8197829, by rfl⟩ : syracuseStep 10930439 = 16395659) B16395659
theorem B7286959 : Blo 2021435 7286959 := bstep (se 1 (by rfl) ⟨5465219, by rfl⟩ : syracuseStep 7286959 = 10930439) B10930439
theorem B9715945 : Blo 2021435 9715945 := bstep (se 2 (by rfl) ⟨3643479, by rfl⟩ : syracuseStep 9715945 = 7286959) B7286959
theorem B12954593 : Blo 2021435 12954593 := bstep (se 2 (by rfl) ⟨4857972, by rfl⟩ : syracuseStep 12954593 = 9715945) B9715945
theorem B8636395 : Blo 2021435 8636395 := bstep (se 1 (by rfl) ⟨6477296, by rfl⟩ : syracuseStep 8636395 = 12954593) B12954593
theorem B11515193 : Blo 2021435 11515193 := bstep (se 2 (by rfl) ⟨4318197, by rfl⟩ : syracuseStep 11515193 = 8636395) B8636395
theorem B7676795 : Blo 2021435 7676795 := bstep (se 1 (by rfl) ⟨5757596, by rfl⟩ : syracuseStep 7676795 = 11515193) B11515193
theorem B5117863 : Blo 2021435 5117863 := bstep (se 1 (by rfl) ⟨3838397, by rfl⟩ : syracuseStep 5117863 = 7676795) B7676795
theorem B6823817 : Blo 2021435 6823817 := bstep (se 2 (by rfl) ⟨2558931, by rfl⟩ : syracuseStep 6823817 = 5117863) B5117863
theorem B4549211 : Blo 2021435 4549211 := bstep (se 1 (by rfl) ⟨3411908, by rfl⟩ : syracuseStep 4549211 = 6823817) B6823817
theorem B3032807 : Blo 2021435 3032807 := bstep (se 1 (by rfl) ⟨2274605, by rfl⟩ : syracuseStep 3032807 = 4549211) B4549211
theorem B2021871 : Blo 2021435 2021871 := bstep (se 1 (by rfl) ⟨1516403, by rfl⟩ : syracuseStep 2021871 = 3032807) B3032807
theorem B3032813 : Blo 2021435 3032813 := bbase (se 3 (by rfl) ⟨568652, by rfl⟩ : syracuseStep 3032813 = 1137305) (by norm_num)
theorem B2021875 : Blo 2021435 2021875 := bstep (se 1 (by rfl) ⟨1516406, by rfl⟩ : syracuseStep 2021875 = 3032813) B3032813
theorem B4549229 : Blo 2021435 4549229 := bbase (se 3 (by rfl) ⟨852980, by rfl⟩ : syracuseStep 4549229 = 1705961) (by norm_num)
theorem B3032819 : Blo 2021435 3032819 := bstep (se 1 (by rfl) ⟨2274614, by rfl⟩ : syracuseStep 3032819 = 4549229) B4549229
theorem B2021879 : Blo 2021435 2021879 := bstep (se 1 (by rfl) ⟨1516409, by rfl⟩ : syracuseStep 2021879 = 3032819) B3032819
theorem B3838421 : Blo 2021435 3838421 := bbase (se 7 (by rfl) ⟨44981, by rfl⟩ : syracuseStep 3838421 = 89963) (by norm_num)
theorem B2558947 : Blo 2021435 2558947 := bstep (se 1 (by rfl) ⟨1919210, by rfl⟩ : syracuseStep 2558947 = 3838421) B3838421
theorem B3411929 : Blo 2021435 3411929 := bstep (se 2 (by rfl) ⟨1279473, by rfl⟩ : syracuseStep 3411929 = 2558947) B2558947
theorem B2274619 : Blo 2021435 2274619 := bstep (se 1 (by rfl) ⟨1705964, by rfl⟩ : syracuseStep 2274619 = 3411929) B3411929
theorem B3032825 : Blo 2021435 3032825 := bstep (se 2 (by rfl) ⟨1137309, by rfl⟩ : syracuseStep 3032825 = 2274619) B2274619
theorem B2021883 : Blo 2021435 2021883 := bstep (se 1 (by rfl) ⟨1516412, by rfl⟩ : syracuseStep 2021883 = 3032825) B3032825
theorem B3890797 : Blo 2021435 3890797 := bbase (se 3 (by rfl) ⟨729524, by rfl⟩ : syracuseStep 3890797 = 1459049) (by norm_num)
theorem B20750917 : Blo 2021435 20750917 := bstep (se 4 (by rfl) ⟨1945398, by rfl⟩ : syracuseStep 20750917 = 3890797) B3890797
theorem B27667889 : Blo 2021435 27667889 := bstep (se 2 (by rfl) ⟨10375458, by rfl⟩ : syracuseStep 27667889 = 20750917) B20750917
theorem B18445259 : Blo 2021435 18445259 := bstep (se 1 (by rfl) ⟨13833944, by rfl⟩ : syracuseStep 18445259 = 27667889) B27667889
theorem B49187357 : Blo 2021435 49187357 := bstep (se 3 (by rfl) ⟨9222629, by rfl⟩ : syracuseStep 49187357 = 18445259) B18445259
theorem B32791571 : Blo 2021435 32791571 := bstep (se 1 (by rfl) ⟨24593678, by rfl⟩ : syracuseStep 32791571 = 49187357) B49187357
theorem B21861047 : Blo 2021435 21861047 := bstep (se 1 (by rfl) ⟨16395785, by rfl⟩ : syracuseStep 21861047 = 32791571) B32791571
theorem B58296125 : Blo 2021435 58296125 := bstep (se 3 (by rfl) ⟨10930523, by rfl⟩ : syracuseStep 58296125 = 21861047) B21861047
theorem B38864083 : Blo 2021435 38864083 := bstep (se 1 (by rfl) ⟨29148062, by rfl⟩ : syracuseStep 38864083 = 58296125) B58296125
theorem B51818777 : Blo 2021435 51818777 := bstep (se 2 (by rfl) ⟨19432041, by rfl⟩ : syracuseStep 51818777 = 38864083) B38864083
theorem B34545851 : Blo 2021435 34545851 := bstep (se 1 (by rfl) ⟨25909388, by rfl⟩ : syracuseStep 34545851 = 51818777) B51818777
theorem B23030567 : Blo 2021435 23030567 := bstep (se 1 (by rfl) ⟨17272925, by rfl⟩ : syracuseStep 23030567 = 34545851) B34545851
theorem B15353711 : Blo 2021435 15353711 := bstep (se 1 (by rfl) ⟨11515283, by rfl⟩ : syracuseStep 15353711 = 23030567) B23030567
theorem B10235807 : Blo 2021435 10235807 := bstep (se 1 (by rfl) ⟨7676855, by rfl⟩ : syracuseStep 10235807 = 15353711) B15353711
theorem B6823871 : Blo 2021435 6823871 := bstep (se 1 (by rfl) ⟨5117903, by rfl⟩ : syracuseStep 6823871 = 10235807) B10235807
theorem B4549247 : Blo 2021435 4549247 := bstep (se 1 (by rfl) ⟨3411935, by rfl⟩ : syracuseStep 4549247 = 6823871) B6823871
theorem B3032831 : Blo 2021435 3032831 := bstep (se 1 (by rfl) ⟨2274623, by rfl⟩ : syracuseStep 3032831 = 4549247) B4549247
theorem B2021887 : Blo 2021435 2021887 := bstep (se 1 (by rfl) ⟨1516415, by rfl⟩ : syracuseStep 2021887 = 3032831) B3032831
theorem B3032837 : Blo 2021435 3032837 := bbase (se 4 (by rfl) ⟨284328, by rfl⟩ : syracuseStep 3032837 = 568657) (by norm_num)
theorem B2021891 : Blo 2021435 2021891 := bstep (se 1 (by rfl) ⟨1516418, by rfl⟩ : syracuseStep 2021891 = 3032837) B3032837
theorem B3411949 : Blo 2021435 3411949 := bbase (se 3 (by rfl) ⟨639740, by rfl⟩ : syracuseStep 3411949 = 1279481) (by norm_num)
theorem B4549265 : Blo 2021435 4549265 := bstep (se 2 (by rfl) ⟨1705974, by rfl⟩ : syracuseStep 4549265 = 3411949) B3411949
theorem B3032843 : Blo 2021435 3032843 := bstep (se 1 (by rfl) ⟨2274632, by rfl⟩ : syracuseStep 3032843 = 4549265) B4549265
theorem B2021895 : Blo 2021435 2021895 := bstep (se 1 (by rfl) ⟨1516421, by rfl⟩ : syracuseStep 2021895 = 3032843) B3032843
theorem B2274637 : Blo 2021435 2274637 := bbase (se 3 (by rfl) ⟨426494, by rfl⟩ : syracuseStep 2274637 = 852989) (by norm_num)
theorem B3032849 : Blo 2021435 3032849 := bstep (se 2 (by rfl) ⟨1137318, by rfl⟩ : syracuseStep 3032849 = 2274637) B2274637
theorem B2021899 : Blo 2021435 2021899 := bstep (se 1 (by rfl) ⟨1516424, by rfl⟩ : syracuseStep 2021899 = 3032849) B3032849
theorem B6823925 : Blo 2021435 6823925 := bbase (se 5 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 6823925 = 639743) (by norm_num)
theorem B4549283 : Blo 2021435 4549283 := bstep (se 1 (by rfl) ⟨3411962, by rfl⟩ : syracuseStep 4549283 = 6823925) B6823925
theorem B3032855 : Blo 2021435 3032855 := bstep (se 1 (by rfl) ⟨2274641, by rfl⟩ : syracuseStep 3032855 = 4549283) B4549283
theorem B2021903 : Blo 2021435 2021903 := bstep (se 1 (by rfl) ⟨1516427, by rfl⟩ : syracuseStep 2021903 = 3032855) B3032855
theorem B3032861 : Blo 2021435 3032861 := bbase (se 3 (by rfl) ⟨568661, by rfl⟩ : syracuseStep 3032861 = 1137323) (by norm_num)
theorem B2021907 : Blo 2021435 2021907 := bstep (se 1 (by rfl) ⟨1516430, by rfl⟩ : syracuseStep 2021907 = 3032861) B3032861
theorem B4549301 : Blo 2021435 4549301 := bbase (se 5 (by rfl) ⟨213248, by rfl⟩ : syracuseStep 4549301 = 426497) (by norm_num)
theorem B3032867 : Blo 2021435 3032867 := bstep (se 1 (by rfl) ⟨2274650, by rfl⟩ : syracuseStep 3032867 = 4549301) B4549301
theorem B2021911 : Blo 2021435 2021911 := bstep (se 1 (by rfl) ⟨1516433, by rfl⟩ : syracuseStep 2021911 = 3032867) B3032867
theorem B11515445 : Blo 2021435 11515445 := bbase (se 5 (by rfl) ⟨539786, by rfl⟩ : syracuseStep 11515445 = 1079573) (by norm_num)
theorem B7676963 : Blo 2021435 7676963 := bstep (se 1 (by rfl) ⟨5757722, by rfl⟩ : syracuseStep 7676963 = 11515445) B11515445
theorem B5117975 : Blo 2021435 5117975 := bstep (se 1 (by rfl) ⟨3838481, by rfl⟩ : syracuseStep 5117975 = 7676963) B7676963
theorem B3411983 : Blo 2021435 3411983 := bstep (se 1 (by rfl) ⟨2558987, by rfl⟩ : syracuseStep 3411983 = 5117975) B5117975
theorem B2274655 : Blo 2021435 2274655 := bstep (se 1 (by rfl) ⟨1705991, by rfl⟩ : syracuseStep 2274655 = 3411983) B3411983
theorem B3032873 : Blo 2021435 3032873 := bstep (se 2 (by rfl) ⟨1137327, by rfl⟩ : syracuseStep 3032873 = 2274655) B2274655
theorem B2021915 : Blo 2021435 2021915 := bstep (se 1 (by rfl) ⟨1516436, by rfl⟩ : syracuseStep 2021915 = 3032873) B3032873
theorem B5757733 : Blo 2021435 5757733 := bbase (se 4 (by rfl) ⟨539787, by rfl⟩ : syracuseStep 5757733 = 1079575) (by norm_num)
theorem B7676977 : Blo 2021435 7676977 := bstep (se 2 (by rfl) ⟨2878866, by rfl⟩ : syracuseStep 7676977 = 5757733) B5757733
theorem B10235969 : Blo 2021435 10235969 := bstep (se 2 (by rfl) ⟨3838488, by rfl⟩ : syracuseStep 10235969 = 7676977) B7676977
theorem B6823979 : Blo 2021435 6823979 := bstep (se 1 (by rfl) ⟨5117984, by rfl⟩ : syracuseStep 6823979 = 10235969) B10235969
theorem B4549319 : Blo 2021435 4549319 := bstep (se 1 (by rfl) ⟨3411989, by rfl⟩ : syracuseStep 4549319 = 6823979) B6823979
theorem B3032879 : Blo 2021435 3032879 := bstep (se 1 (by rfl) ⟨2274659, by rfl⟩ : syracuseStep 3032879 = 4549319) B4549319
theorem B2021919 : Blo 2021435 2021919 := bstep (se 1 (by rfl) ⟨1516439, by rfl⟩ : syracuseStep 2021919 = 3032879) B3032879
theorem B3032885 : Blo 2021435 3032885 := bbase (se 5 (by rfl) ⟨142166, by rfl⟩ : syracuseStep 3032885 = 284333) (by norm_num)
theorem B2021923 : Blo 2021435 2021923 := bstep (se 1 (by rfl) ⟨1516442, by rfl⟩ : syracuseStep 2021923 = 3032885) B3032885
theorem B5118005 : Blo 2021435 5118005 := bbase (se 5 (by rfl) ⟨239906, by rfl⟩ : syracuseStep 5118005 = 479813) (by norm_num)
theorem B3412003 : Blo 2021435 3412003 := bstep (se 1 (by rfl) ⟨2559002, by rfl⟩ : syracuseStep 3412003 = 5118005) B5118005
theorem B4549337 : Blo 2021435 4549337 := bstep (se 2 (by rfl) ⟨1706001, by rfl⟩ : syracuseStep 4549337 = 3412003) B3412003
theorem B3032891 : Blo 2021435 3032891 := bstep (se 1 (by rfl) ⟨2274668, by rfl⟩ : syracuseStep 3032891 = 4549337) B4549337
theorem B2021927 : Blo 2021435 2021927 := bstep (se 1 (by rfl) ⟨1516445, by rfl⟩ : syracuseStep 2021927 = 3032891) B3032891
theorem B2274673 : Blo 2021435 2274673 := bbase (se 2 (by rfl) ⟨853002, by rfl⟩ : syracuseStep 2274673 = 1706005) (by norm_num)
theorem B3032897 : Blo 2021435 3032897 := bstep (se 2 (by rfl) ⟨1137336, by rfl⟩ : syracuseStep 3032897 = 2274673) B2274673
theorem B2021931 : Blo 2021435 2021931 := bstep (se 1 (by rfl) ⟨1516448, by rfl⟩ : syracuseStep 2021931 = 3032897) B3032897
theorem B16396181 : Blo 2021435 16396181 := bbase (se 6 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 16396181 = 768571) (by norm_num)
theorem B10930787 : Blo 2021435 10930787 := bstep (se 1 (by rfl) ⟨8198090, by rfl⟩ : syracuseStep 10930787 = 16396181) B16396181
theorem B7287191 : Blo 2021435 7287191 := bstep (se 1 (by rfl) ⟨5465393, by rfl⟩ : syracuseStep 7287191 = 10930787) B10930787
theorem B4858127 : Blo 2021435 4858127 := bstep (se 1 (by rfl) ⟨3643595, by rfl⟩ : syracuseStep 4858127 = 7287191) B7287191
theorem B3238751 : Blo 2021435 3238751 := bstep (se 1 (by rfl) ⟨2429063, by rfl⟩ : syracuseStep 3238751 = 4858127) B4858127
theorem B8636669 : Blo 2021435 8636669 := bstep (se 3 (by rfl) ⟨1619375, by rfl⟩ : syracuseStep 8636669 = 3238751) B3238751
theorem B5757779 : Blo 2021435 5757779 := bstep (se 1 (by rfl) ⟨4318334, by rfl⟩ : syracuseStep 5757779 = 8636669) B8636669
theorem B3838519 : Blo 2021435 3838519 := bstep (se 1 (by rfl) ⟨2878889, by rfl⟩ : syracuseStep 3838519 = 5757779) B5757779
theorem B5118025 : Blo 2021435 5118025 := bstep (se 2 (by rfl) ⟨1919259, by rfl⟩ : syracuseStep 5118025 = 3838519) B3838519
theorem B6824033 : Blo 2021435 6824033 := bstep (se 2 (by rfl) ⟨2559012, by rfl⟩ : syracuseStep 6824033 = 5118025) B5118025
theorem B4549355 : Blo 2021435 4549355 := bstep (se 1 (by rfl) ⟨3412016, by rfl⟩ : syracuseStep 4549355 = 6824033) B6824033
theorem B3032903 : Blo 2021435 3032903 := bstep (se 1 (by rfl) ⟨2274677, by rfl⟩ : syracuseStep 3032903 = 4549355) B4549355
theorem B2021935 : Blo 2021435 2021935 := bstep (se 1 (by rfl) ⟨1516451, by rfl⟩ : syracuseStep 2021935 = 3032903) B3032903
theorem B3032909 : Blo 2021435 3032909 := bbase (se 3 (by rfl) ⟨568670, by rfl⟩ : syracuseStep 3032909 = 1137341) (by norm_num)
theorem B2021939 : Blo 2021435 2021939 := bstep (se 1 (by rfl) ⟨1516454, by rfl⟩ : syracuseStep 2021939 = 3032909) B3032909
theorem B4549373 : Blo 2021435 4549373 := bbase (se 3 (by rfl) ⟨853007, by rfl⟩ : syracuseStep 4549373 = 1706015) (by norm_num)
theorem B3032915 : Blo 2021435 3032915 := bstep (se 1 (by rfl) ⟨2274686, by rfl⟩ : syracuseStep 3032915 = 4549373) B4549373
theorem B2021943 : Blo 2021435 2021943 := bstep (se 1 (by rfl) ⟨1516457, by rfl⟩ : syracuseStep 2021943 = 3032915) B3032915
theorem B3412037 : Blo 2021435 3412037 := bbase (se 4 (by rfl) ⟨319878, by rfl⟩ : syracuseStep 3412037 = 639757) (by norm_num)
theorem B2274691 : Blo 2021435 2274691 := bstep (se 1 (by rfl) ⟨1706018, by rfl⟩ : syracuseStep 2274691 = 3412037) B3412037
theorem B3032921 : Blo 2021435 3032921 := bstep (se 2 (by rfl) ⟨1137345, by rfl⟩ : syracuseStep 3032921 = 2274691) B2274691
theorem B2021947 : Blo 2021435 2021947 := bstep (se 1 (by rfl) ⟨1516460, by rfl⟩ : syracuseStep 2021947 = 3032921) B3032921
theorem B15354197 : Blo 2021435 15354197 := bbase (se 10 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 15354197 = 44983) (by norm_num)
theorem B10236131 : Blo 2021435 10236131 := bstep (se 1 (by rfl) ⟨7677098, by rfl⟩ : syracuseStep 10236131 = 15354197) B15354197
theorem B6824087 : Blo 2021435 6824087 := bstep (se 1 (by rfl) ⟨5118065, by rfl⟩ : syracuseStep 6824087 = 10236131) B10236131
theorem B4549391 : Blo 2021435 4549391 := bstep (se 1 (by rfl) ⟨3412043, by rfl⟩ : syracuseStep 4549391 = 6824087) B6824087
theorem B3032927 : Blo 2021435 3032927 := bstep (se 1 (by rfl) ⟨2274695, by rfl⟩ : syracuseStep 3032927 = 4549391) B4549391
theorem B2021951 : Blo 2021435 2021951 := bstep (se 1 (by rfl) ⟨1516463, by rfl⟩ : syracuseStep 2021951 = 3032927) B3032927
theorem B3032933 : Blo 2021435 3032933 := bbase (se 4 (by rfl) ⟨284337, by rfl⟩ : syracuseStep 3032933 = 568675) (by norm_num)
theorem B2021955 : Blo 2021435 2021955 := bstep (se 1 (by rfl) ⟨1516466, by rfl⟩ : syracuseStep 2021955 = 3032933) B3032933
theorem B3838565 : Blo 2021435 3838565 := bbase (se 4 (by rfl) ⟨359865, by rfl⟩ : syracuseStep 3838565 = 719731) (by norm_num)
theorem B2559043 : Blo 2021435 2559043 := bstep (se 1 (by rfl) ⟨1919282, by rfl⟩ : syracuseStep 2559043 = 3838565) B3838565
theorem B3412057 : Blo 2021435 3412057 := bstep (se 2 (by rfl) ⟨1279521, by rfl⟩ : syracuseStep 3412057 = 2559043) B2559043
theorem B4549409 : Blo 2021435 4549409 := bstep (se 2 (by rfl) ⟨1706028, by rfl⟩ : syracuseStep 4549409 = 3412057) B3412057
theorem B3032939 : Blo 2021435 3032939 := bstep (se 1 (by rfl) ⟨2274704, by rfl⟩ : syracuseStep 3032939 = 4549409) B4549409
theorem B2021959 : Blo 2021435 2021959 := bstep (se 1 (by rfl) ⟨1516469, by rfl⟩ : syracuseStep 2021959 = 3032939) B3032939
theorem B2274709 : Blo 2021435 2274709 := bbase (se 6 (by rfl) ⟨53313, by rfl⟩ : syracuseStep 2274709 = 106627) (by norm_num)
theorem B3032945 : Blo 2021435 3032945 := bstep (se 2 (by rfl) ⟨1137354, by rfl⟩ : syracuseStep 3032945 = 2274709) B2274709
theorem B2021963 : Blo 2021435 2021963 := bstep (se 1 (by rfl) ⟨1516472, by rfl⟩ : syracuseStep 2021963 = 3032945) B3032945
theorem B2559053 : Blo 2021435 2559053 := bbase (se 3 (by rfl) ⟨479822, by rfl⟩ : syracuseStep 2559053 = 959645) (by norm_num)
theorem B6824141 : Blo 2021435 6824141 := bstep (se 3 (by rfl) ⟨1279526, by rfl⟩ : syracuseStep 6824141 = 2559053) B2559053
theorem B4549427 : Blo 2021435 4549427 := bstep (se 1 (by rfl) ⟨3412070, by rfl⟩ : syracuseStep 4549427 = 6824141) B6824141
theorem B3032951 : Blo 2021435 3032951 := bstep (se 1 (by rfl) ⟨2274713, by rfl⟩ : syracuseStep 3032951 = 4549427) B4549427
theorem B2021967 : Blo 2021435 2021967 := bstep (se 1 (by rfl) ⟨1516475, by rfl⟩ : syracuseStep 2021967 = 3032951) B3032951
theorem B3032957 : Blo 2021435 3032957 := bbase (se 3 (by rfl) ⟨568679, by rfl⟩ : syracuseStep 3032957 = 1137359) (by norm_num)
theorem B2021971 : Blo 2021435 2021971 := bstep (se 1 (by rfl) ⟨1516478, by rfl⟩ : syracuseStep 2021971 = 3032957) B3032957
theorem B4549445 : Blo 2021435 4549445 := bbase (se 4 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 4549445 = 853021) (by norm_num)
theorem B3032963 : Blo 2021435 3032963 := bstep (se 1 (by rfl) ⟨2274722, by rfl⟩ : syracuseStep 3032963 = 4549445) B4549445
theorem B2021975 : Blo 2021435 2021975 := bstep (se 1 (by rfl) ⟨1516481, by rfl⟩ : syracuseStep 2021975 = 3032963) B3032963
theorem B4318429 : Blo 2021435 4318429 := bbase (se 3 (by rfl) ⟨809705, by rfl⟩ : syracuseStep 4318429 = 1619411) (by norm_num)
theorem B5757905 : Blo 2021435 5757905 := bstep (se 2 (by rfl) ⟨2159214, by rfl⟩ : syracuseStep 5757905 = 4318429) B4318429
theorem B3838603 : Blo 2021435 3838603 := bstep (se 1 (by rfl) ⟨2878952, by rfl⟩ : syracuseStep 3838603 = 5757905) B5757905
theorem B5118137 : Blo 2021435 5118137 := bstep (se 2 (by rfl) ⟨1919301, by rfl⟩ : syracuseStep 5118137 = 3838603) B3838603
theorem B3412091 : Blo 2021435 3412091 := bstep (se 1 (by rfl) ⟨2559068, by rfl⟩ : syracuseStep 3412091 = 5118137) B5118137
theorem B2274727 : Blo 2021435 2274727 := bstep (se 1 (by rfl) ⟨1706045, by rfl⟩ : syracuseStep 2274727 = 3412091) B3412091
theorem B3032969 : Blo 2021435 3032969 := bstep (se 2 (by rfl) ⟨1137363, by rfl⟩ : syracuseStep 3032969 = 2274727) B2274727
theorem B2021979 : Blo 2021435 2021979 := bstep (se 1 (by rfl) ⟨1516484, by rfl⟩ : syracuseStep 2021979 = 3032969) B3032969
theorem B10236293 : Blo 2021435 10236293 := bbase (se 4 (by rfl) ⟨959652, by rfl⟩ : syracuseStep 10236293 = 1919305) (by norm_num)
theorem B6824195 : Blo 2021435 6824195 := bstep (se 1 (by rfl) ⟨5118146, by rfl⟩ : syracuseStep 6824195 = 10236293) B10236293
theorem B4549463 : Blo 2021435 4549463 := bstep (se 1 (by rfl) ⟨3412097, by rfl⟩ : syracuseStep 4549463 = 6824195) B6824195
theorem B3032975 : Blo 2021435 3032975 := bstep (se 1 (by rfl) ⟨2274731, by rfl⟩ : syracuseStep 3032975 = 4549463) B4549463
theorem B2021983 : Blo 2021435 2021983 := bstep (se 1 (by rfl) ⟨1516487, by rfl⟩ : syracuseStep 2021983 = 3032975) B3032975
theorem B3032981 : Blo 2021435 3032981 := bbase (se 6 (by rfl) ⟨71085, by rfl⟩ : syracuseStep 3032981 = 142171) (by norm_num)
theorem B2021987 : Blo 2021435 2021987 := bstep (se 1 (by rfl) ⟨1516490, by rfl⟩ : syracuseStep 2021987 = 3032981) B3032981
theorem B2732773 : Blo 2021435 2732773 := bbase (se 4 (by rfl) ⟨256197, by rfl⟩ : syracuseStep 2732773 = 512395) (by norm_num)
theorem B3643697 : Blo 2021435 3643697 := bstep (se 2 (by rfl) ⟨1366386, by rfl⟩ : syracuseStep 3643697 = 2732773) B2732773
theorem B2429131 : Blo 2021435 2429131 := bstep (se 1 (by rfl) ⟨1821848, by rfl⟩ : syracuseStep 2429131 = 3643697) B3643697
theorem B3238841 : Blo 2021435 3238841 := bstep (se 2 (by rfl) ⟨1214565, by rfl⟩ : syracuseStep 3238841 = 2429131) B2429131
theorem B2159227 : Blo 2021435 2159227 := bstep (se 1 (by rfl) ⟨1619420, by rfl⟩ : syracuseStep 2159227 = 3238841) B3238841
theorem B11515877 : Blo 2021435 11515877 := bstep (se 4 (by rfl) ⟨1079613, by rfl⟩ : syracuseStep 11515877 = 2159227) B2159227
theorem B7677251 : Blo 2021435 7677251 := bstep (se 1 (by rfl) ⟨5757938, by rfl⟩ : syracuseStep 7677251 = 11515877) B11515877
theorem B5118167 : Blo 2021435 5118167 := bstep (se 1 (by rfl) ⟨3838625, by rfl⟩ : syracuseStep 5118167 = 7677251) B7677251
theorem B3412111 : Blo 2021435 3412111 := bstep (se 1 (by rfl) ⟨2559083, by rfl⟩ : syracuseStep 3412111 = 5118167) B5118167
theorem B4549481 : Blo 2021435 4549481 := bstep (se 2 (by rfl) ⟨1706055, by rfl⟩ : syracuseStep 4549481 = 3412111) B3412111
theorem B3032987 : Blo 2021435 3032987 := bstep (se 1 (by rfl) ⟨2274740, by rfl⟩ : syracuseStep 3032987 = 4549481) B4549481
theorem B2021991 : Blo 2021435 2021991 := bstep (se 1 (by rfl) ⟨1516493, by rfl⟩ : syracuseStep 2021991 = 3032987) B3032987
theorem B2274745 : Blo 2021435 2274745 := bbase (se 2 (by rfl) ⟨853029, by rfl⟩ : syracuseStep 2274745 = 1706059) (by norm_num)
theorem B3032993 : Blo 2021435 3032993 := bstep (se 2 (by rfl) ⟨1137372, by rfl⟩ : syracuseStep 3032993 = 2274745) B2274745
theorem B2021995 : Blo 2021435 2021995 := bstep (se 1 (by rfl) ⟨1516496, by rfl⟩ : syracuseStep 2021995 = 3032993) B3032993
theorem B4497653 : Blo 2021435 4497653 := bbase (se 5 (by rfl) ⟨210827, by rfl⟩ : syracuseStep 4497653 = 421655) (by norm_num)
theorem B11993741 : Blo 2021435 11993741 := bstep (se 3 (by rfl) ⟨2248826, by rfl⟩ : syracuseStep 11993741 = 4497653) B4497653
theorem B7995827 : Blo 2021435 7995827 := bstep (se 1 (by rfl) ⟨5996870, by rfl⟩ : syracuseStep 7995827 = 11993741) B11993741
theorem B5330551 : Blo 2021435 5330551 := bstep (se 1 (by rfl) ⟨3997913, by rfl⟩ : syracuseStep 5330551 = 7995827) B7995827
theorem B7107401 : Blo 2021435 7107401 := bstep (se 2 (by rfl) ⟨2665275, by rfl⟩ : syracuseStep 7107401 = 5330551) B5330551
theorem B4738267 : Blo 2021435 4738267 := bstep (se 1 (by rfl) ⟨3553700, by rfl⟩ : syracuseStep 4738267 = 7107401) B7107401
theorem B6317689 : Blo 2021435 6317689 := bstep (se 2 (by rfl) ⟨2369133, by rfl⟩ : syracuseStep 6317689 = 4738267) B4738267
theorem B8423585 : Blo 2021435 8423585 := bstep (se 2 (by rfl) ⟨3158844, by rfl⟩ : syracuseStep 8423585 = 6317689) B6317689
theorem B5615723 : Blo 2021435 5615723 := bstep (se 1 (by rfl) ⟨4211792, by rfl⟩ : syracuseStep 5615723 = 8423585) B8423585
theorem B14975261 : Blo 2021435 14975261 := bstep (se 3 (by rfl) ⟨2807861, by rfl⟩ : syracuseStep 14975261 = 5615723) B5615723
theorem B9983507 : Blo 2021435 9983507 := bstep (se 1 (by rfl) ⟨7487630, by rfl⟩ : syracuseStep 9983507 = 14975261) B14975261
theorem B26622685 : Blo 2021435 26622685 := bstep (se 3 (by rfl) ⟨4991753, by rfl⟩ : syracuseStep 26622685 = 9983507) B9983507
theorem B35496913 : Blo 2021435 35496913 := bstep (se 2 (by rfl) ⟨13311342, by rfl⟩ : syracuseStep 35496913 = 26622685) B26622685
theorem B47329217 : Blo 2021435 47329217 := bstep (se 2 (by rfl) ⟨17748456, by rfl⟩ : syracuseStep 47329217 = 35496913) B35496913
theorem B31552811 : Blo 2021435 31552811 := bstep (se 1 (by rfl) ⟨23664608, by rfl⟩ : syracuseStep 31552811 = 47329217) B47329217
theorem B21035207 : Blo 2021435 21035207 := bstep (se 1 (by rfl) ⟨15776405, by rfl⟩ : syracuseStep 21035207 = 31552811) B31552811
theorem B56093885 : Blo 2021435 56093885 := bstep (se 3 (by rfl) ⟨10517603, by rfl⟩ : syracuseStep 56093885 = 21035207) B21035207
theorem B37395923 : Blo 2021435 37395923 := bstep (se 1 (by rfl) ⟨28046942, by rfl⟩ : syracuseStep 37395923 = 56093885) B56093885
theorem B99722461 : Blo 2021435 99722461 := bstep (se 3 (by rfl) ⟨18697961, by rfl⟩ : syracuseStep 99722461 = 37395923) B37395923
theorem B132963281 : Blo 2021435 132963281 := bstep (se 2 (by rfl) ⟨49861230, by rfl⟩ : syracuseStep 132963281 = 99722461) B99722461
theorem B88642187 : Blo 2021435 88642187 := bstep (se 1 (by rfl) ⟨66481640, by rfl⟩ : syracuseStep 88642187 = 132963281) B132963281
theorem B59094791 : Blo 2021435 59094791 := bstep (se 1 (by rfl) ⟨44321093, by rfl⟩ : syracuseStep 59094791 = 88642187) B88642187
theorem B39396527 : Blo 2021435 39396527 := bstep (se 1 (by rfl) ⟨29547395, by rfl⟩ : syracuseStep 39396527 = 59094791) B59094791
theorem B26264351 : Blo 2021435 26264351 := bstep (se 1 (by rfl) ⟨19698263, by rfl⟩ : syracuseStep 26264351 = 39396527) B39396527
theorem B17509567 : Blo 2021435 17509567 := bstep (se 1 (by rfl) ⟨13132175, by rfl⟩ : syracuseStep 17509567 = 26264351) B26264351
theorem B23346089 : Blo 2021435 23346089 := bstep (se 2 (by rfl) ⟨8754783, by rfl⟩ : syracuseStep 23346089 = 17509567) B17509567
theorem B15564059 : Blo 2021435 15564059 := bstep (se 1 (by rfl) ⟨11673044, by rfl⟩ : syracuseStep 15564059 = 23346089) B23346089
theorem B10376039 : Blo 2021435 10376039 := bstep (se 1 (by rfl) ⟨7782029, by rfl⟩ : syracuseStep 10376039 = 15564059) B15564059
theorem B6917359 : Blo 2021435 6917359 := bstep (se 1 (by rfl) ⟨5188019, by rfl⟩ : syracuseStep 6917359 = 10376039) B10376039
theorem B9223145 : Blo 2021435 9223145 := bstep (se 2 (by rfl) ⟨3458679, by rfl⟩ : syracuseStep 9223145 = 6917359) B6917359
theorem B6148763 : Blo 2021435 6148763 := bstep (se 1 (by rfl) ⟨4611572, by rfl⟩ : syracuseStep 6148763 = 9223145) B9223145
theorem B4099175 : Blo 2021435 4099175 := bstep (se 1 (by rfl) ⟨3074381, by rfl⟩ : syracuseStep 4099175 = 6148763) B6148763
theorem B2732783 : Blo 2021435 2732783 := bstep (se 1 (by rfl) ⟨2049587, by rfl⟩ : syracuseStep 2732783 = 4099175) B4099175
theorem B7287421 : Blo 2021435 7287421 := bstep (se 3 (by rfl) ⟨1366391, by rfl⟩ : syracuseStep 7287421 = 2732783) B2732783
theorem B9716561 : Blo 2021435 9716561 := bstep (se 2 (by rfl) ⟨3643710, by rfl⟩ : syracuseStep 9716561 = 7287421) B7287421
theorem B6477707 : Blo 2021435 6477707 := bstep (se 1 (by rfl) ⟨4858280, by rfl⟩ : syracuseStep 6477707 = 9716561) B9716561
theorem B4318471 : Blo 2021435 4318471 := bstep (se 1 (by rfl) ⟨3238853, by rfl⟩ : syracuseStep 4318471 = 6477707) B6477707
theorem B5757961 : Blo 2021435 5757961 := bstep (se 2 (by rfl) ⟨2159235, by rfl⟩ : syracuseStep 5757961 = 4318471) B4318471
theorem B7677281 : Blo 2021435 7677281 := bstep (se 2 (by rfl) ⟨2878980, by rfl⟩ : syracuseStep 7677281 = 5757961) B5757961
theorem B5118187 : Blo 2021435 5118187 := bstep (se 1 (by rfl) ⟨3838640, by rfl⟩ : syracuseStep 5118187 = 7677281) B7677281
theorem B6824249 : Blo 2021435 6824249 := bstep (se 2 (by rfl) ⟨2559093, by rfl⟩ : syracuseStep 6824249 = 5118187) B5118187
theorem B4549499 : Blo 2021435 4549499 := bstep (se 1 (by rfl) ⟨3412124, by rfl⟩ : syracuseStep 4549499 = 6824249) B6824249
theorem B3032999 : Blo 2021435 3032999 := bstep (se 1 (by rfl) ⟨2274749, by rfl⟩ : syracuseStep 3032999 = 4549499) B4549499
theorem B2021999 : Blo 2021435 2021999 := bstep (se 1 (by rfl) ⟨1516499, by rfl⟩ : syracuseStep 2021999 = 3032999) B3032999
theorem B3033005 : Blo 2021435 3033005 := bbase (se 3 (by rfl) ⟨568688, by rfl⟩ : syracuseStep 3033005 = 1137377) (by norm_num)
theorem B2022003 : Blo 2021435 2022003 := bstep (se 1 (by rfl) ⟨1516502, by rfl⟩ : syracuseStep 2022003 = 3033005) B3033005
theorem B4549517 : Blo 2021435 4549517 := bbase (se 3 (by rfl) ⟨853034, by rfl⟩ : syracuseStep 4549517 = 1706069) (by norm_num)
theorem B3033011 : Blo 2021435 3033011 := bstep (se 1 (by rfl) ⟨2274758, by rfl⟩ : syracuseStep 3033011 = 4549517) B4549517
theorem B2022007 : Blo 2021435 2022007 := bstep (se 1 (by rfl) ⟨1516505, by rfl⟩ : syracuseStep 2022007 = 3033011) B3033011
theorem B2559109 : Blo 2021435 2559109 := bbase (se 4 (by rfl) ⟨239916, by rfl⟩ : syracuseStep 2559109 = 479833) (by norm_num)
theorem B3412145 : Blo 2021435 3412145 := bstep (se 2 (by rfl) ⟨1279554, by rfl⟩ : syracuseStep 3412145 = 2559109) B2559109
theorem B2274763 : Blo 2021435 2274763 := bstep (se 1 (by rfl) ⟨1706072, by rfl⟩ : syracuseStep 2274763 = 3412145) B3412145
theorem B3033017 : Blo 2021435 3033017 := bstep (se 2 (by rfl) ⟨1137381, by rfl⟩ : syracuseStep 3033017 = 2274763) B2274763
theorem B2022011 : Blo 2021435 2022011 := bstep (se 1 (by rfl) ⟨1516508, by rfl⟩ : syracuseStep 2022011 = 3033017) B3033017
theorem B6917413 : Blo 2021435 6917413 := bbase (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) (by norm_num)
theorem B9223217 : Blo 2021435 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B6148811 : Blo 2021435 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B4099207 : Blo 2021435 4099207 := bstep (se 1 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 4099207 = 6148811) B6148811
theorem B5465609 : Blo 2021435 5465609 := bstep (se 2 (by rfl) ⟨2049603, by rfl⟩ : syracuseStep 5465609 = 4099207) B4099207
theorem B3643739 : Blo 2021435 3643739 := bstep (se 1 (by rfl) ⟨2732804, by rfl⟩ : syracuseStep 3643739 = 5465609) B5465609
theorem B2429159 : Blo 2021435 2429159 := bstep (se 1 (by rfl) ⟨1821869, by rfl⟩ : syracuseStep 2429159 = 3643739) B3643739
theorem B25911029 : Blo 2021435 25911029 := bstep (se 5 (by rfl) ⟨1214579, by rfl⟩ : syracuseStep 25911029 = 2429159) B2429159
theorem B17274019 : Blo 2021435 17274019 := bstep (se 1 (by rfl) ⟨12955514, by rfl⟩ : syracuseStep 17274019 = 25911029) B25911029
theorem B23032025 : Blo 2021435 23032025 := bstep (se 2 (by rfl) ⟨8637009, by rfl⟩ : syracuseStep 23032025 = 17274019) B17274019
theorem B15354683 : Blo 2021435 15354683 := bstep (se 1 (by rfl) ⟨11516012, by rfl⟩ : syracuseStep 15354683 = 23032025) B23032025
theorem B10236455 : Blo 2021435 10236455 := bstep (se 1 (by rfl) ⟨7677341, by rfl⟩ : syracuseStep 10236455 = 15354683) B15354683
theorem B6824303 : Blo 2021435 6824303 := bstep (se 1 (by rfl) ⟨5118227, by rfl⟩ : syracuseStep 6824303 = 10236455) B10236455
theorem B4549535 : Blo 2021435 4549535 := bstep (se 1 (by rfl) ⟨3412151, by rfl⟩ : syracuseStep 4549535 = 6824303) B6824303
theorem B3033023 : Blo 2021435 3033023 := bstep (se 1 (by rfl) ⟨2274767, by rfl⟩ : syracuseStep 3033023 = 4549535) B4549535
theorem B2022015 : Blo 2021435 2022015 := bstep (se 1 (by rfl) ⟨1516511, by rfl⟩ : syracuseStep 2022015 = 3033023) B3033023
theorem B3033029 : Blo 2021435 3033029 := bbase (se 4 (by rfl) ⟨284346, by rfl⟩ : syracuseStep 3033029 = 568693) (by norm_num)
theorem B2022019 : Blo 2021435 2022019 := bstep (se 1 (by rfl) ⟨1516514, by rfl⟩ : syracuseStep 2022019 = 3033029) B3033029
theorem B3412165 : Blo 2021435 3412165 := bbase (se 4 (by rfl) ⟨319890, by rfl⟩ : syracuseStep 3412165 = 639781) (by norm_num)
theorem B4549553 : Blo 2021435 4549553 := bstep (se 2 (by rfl) ⟨1706082, by rfl⟩ : syracuseStep 4549553 = 3412165) B3412165
theorem B3033035 : Blo 2021435 3033035 := bstep (se 1 (by rfl) ⟨2274776, by rfl⟩ : syracuseStep 3033035 = 4549553) B4549553
theorem B2022023 : Blo 2021435 2022023 := bstep (se 1 (by rfl) ⟨1516517, by rfl⟩ : syracuseStep 2022023 = 3033035) B3033035
theorem B2274781 : Blo 2021435 2274781 := bbase (se 3 (by rfl) ⟨426521, by rfl⟩ : syracuseStep 2274781 = 853043) (by norm_num)
theorem B3033041 : Blo 2021435 3033041 := bstep (se 2 (by rfl) ⟨1137390, by rfl⟩ : syracuseStep 3033041 = 2274781) B2274781
theorem B2022027 : Blo 2021435 2022027 := bstep (se 1 (by rfl) ⟨1516520, by rfl⟩ : syracuseStep 2022027 = 3033041) B3033041
theorem B6824357 : Blo 2021435 6824357 := bbase (se 4 (by rfl) ⟨639783, by rfl⟩ : syracuseStep 6824357 = 1279567) (by norm_num)
theorem B4549571 : Blo 2021435 4549571 := bstep (se 1 (by rfl) ⟨3412178, by rfl⟩ : syracuseStep 4549571 = 6824357) B6824357
theorem B3033047 : Blo 2021435 3033047 := bstep (se 1 (by rfl) ⟨2274785, by rfl⟩ : syracuseStep 3033047 = 4549571) B4549571
theorem B2022031 : Blo 2021435 2022031 := bstep (se 1 (by rfl) ⟨1516523, by rfl⟩ : syracuseStep 2022031 = 3033047) B3033047
theorem B3033053 : Blo 2021435 3033053 := bbase (se 3 (by rfl) ⟨568697, by rfl⟩ : syracuseStep 3033053 = 1137395) (by norm_num)
theorem B2022035 : Blo 2021435 2022035 := bstep (se 1 (by rfl) ⟨1516526, by rfl⟩ : syracuseStep 2022035 = 3033053) B3033053
theorem B4549589 : Blo 2021435 4549589 := bbase (se 7 (by rfl) ⟨53315, by rfl⟩ : syracuseStep 4549589 = 106631) (by norm_num)
theorem B3033059 : Blo 2021435 3033059 := bstep (se 1 (by rfl) ⟨2274794, by rfl⟩ : syracuseStep 3033059 = 4549589) B4549589
theorem B2022039 : Blo 2021435 2022039 := bstep (se 1 (by rfl) ⟨1516529, by rfl⟩ : syracuseStep 2022039 = 3033059) B3033059
theorem B9716773 : Blo 2021435 9716773 := bbase (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) (by norm_num)
theorem B12955697 : Blo 2021435 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B8637131 : Blo 2021435 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B5758087 : Blo 2021435 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B7677449 : Blo 2021435 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B5118299 : Blo 2021435 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B3412199 : Blo 2021435 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B2274799 : Blo 2021435 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B3033065 : Blo 2021435 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B2022043 : Blo 2021435 2022043 := bstep (se 1 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 2022043 = 3033065) B3033065
theorem B17274293 : Blo 2021435 17274293 := bbase (se 5 (by rfl) ⟨809732, by rfl⟩ : syracuseStep 17274293 = 1619465) (by norm_num)
theorem B11516195 : Blo 2021435 11516195 := bstep (se 1 (by rfl) ⟨8637146, by rfl⟩ : syracuseStep 11516195 = 17274293) B17274293
theorem B7677463 : Blo 2021435 7677463 := bstep (se 1 (by rfl) ⟨5758097, by rfl⟩ : syracuseStep 7677463 = 11516195) B11516195
theorem B10236617 : Blo 2021435 10236617 := bstep (se 2 (by rfl) ⟨3838731, by rfl⟩ : syracuseStep 10236617 = 7677463) B7677463
theorem B6824411 : Blo 2021435 6824411 := bstep (se 1 (by rfl) ⟨5118308, by rfl⟩ : syracuseStep 6824411 = 10236617) B10236617
theorem B4549607 : Blo 2021435 4549607 := bstep (se 1 (by rfl) ⟨3412205, by rfl⟩ : syracuseStep 4549607 = 6824411) B6824411
theorem B3033071 : Blo 2021435 3033071 := bstep (se 1 (by rfl) ⟨2274803, by rfl⟩ : syracuseStep 3033071 = 4549607) B4549607
theorem B2022047 : Blo 2021435 2022047 := bstep (se 1 (by rfl) ⟨1516535, by rfl⟩ : syracuseStep 2022047 = 3033071) B3033071
theorem B3033077 : Blo 2021435 3033077 := bbase (se 5 (by rfl) ⟨142175, by rfl⟩ : syracuseStep 3033077 = 284351) (by norm_num)
theorem B2022051 : Blo 2021435 2022051 := bstep (se 1 (by rfl) ⟨1516538, by rfl⟩ : syracuseStep 2022051 = 3033077) B3033077
theorem B19698805 : Blo 2021435 19698805 := bbase (se 5 (by rfl) ⟨923381, by rfl⟩ : syracuseStep 19698805 = 1846763) (by norm_num)
theorem B26265073 : Blo 2021435 26265073 := bstep (se 2 (by rfl) ⟨9849402, by rfl⟩ : syracuseStep 26265073 = 19698805) B19698805
theorem B35020097 : Blo 2021435 35020097 := bstep (se 2 (by rfl) ⟨13132536, by rfl⟩ : syracuseStep 35020097 = 26265073) B26265073
theorem B23346731 : Blo 2021435 23346731 := bstep (se 1 (by rfl) ⟨17510048, by rfl⟩ : syracuseStep 23346731 = 35020097) B35020097
theorem B15564487 : Blo 2021435 15564487 := bstep (se 1 (by rfl) ⟨11673365, by rfl⟩ : syracuseStep 15564487 = 23346731) B23346731
theorem B20752649 : Blo 2021435 20752649 := bstep (se 2 (by rfl) ⟨7782243, by rfl⟩ : syracuseStep 20752649 = 15564487) B15564487
theorem B13835099 : Blo 2021435 13835099 := bstep (se 1 (by rfl) ⟨10376324, by rfl⟩ : syracuseStep 13835099 = 20752649) B20752649
theorem B9223399 : Blo 2021435 9223399 := bstep (se 1 (by rfl) ⟨6917549, by rfl⟩ : syracuseStep 9223399 = 13835099) B13835099
theorem B49191461 : Blo 2021435 49191461 := bstep (se 4 (by rfl) ⟨4611699, by rfl⟩ : syracuseStep 49191461 = 9223399) B9223399
theorem B32794307 : Blo 2021435 32794307 := bstep (se 1 (by rfl) ⟨24595730, by rfl⟩ : syracuseStep 32794307 = 49191461) B49191461
theorem B21862871 : Blo 2021435 21862871 := bstep (se 1 (by rfl) ⟨16397153, by rfl⟩ : syracuseStep 21862871 = 32794307) B32794307
theorem B14575247 : Blo 2021435 14575247 := bstep (se 1 (by rfl) ⟨10931435, by rfl⟩ : syracuseStep 14575247 = 21862871) B21862871
theorem B9716831 : Blo 2021435 9716831 := bstep (se 1 (by rfl) ⟨7287623, by rfl⟩ : syracuseStep 9716831 = 14575247) B14575247
theorem B6477887 : Blo 2021435 6477887 := bstep (se 1 (by rfl) ⟨4858415, by rfl⟩ : syracuseStep 6477887 = 9716831) B9716831
theorem B4318591 : Blo 2021435 4318591 := bstep (se 1 (by rfl) ⟨3238943, by rfl⟩ : syracuseStep 4318591 = 6477887) B6477887
theorem B5758121 : Blo 2021435 5758121 := bstep (se 2 (by rfl) ⟨2159295, by rfl⟩ : syracuseStep 5758121 = 4318591) B4318591
theorem B3838747 : Blo 2021435 3838747 := bstep (se 1 (by rfl) ⟨2879060, by rfl⟩ : syracuseStep 3838747 = 5758121) B5758121
theorem B5118329 : Blo 2021435 5118329 := bstep (se 2 (by rfl) ⟨1919373, by rfl⟩ : syracuseStep 5118329 = 3838747) B3838747
theorem B3412219 : Blo 2021435 3412219 := bstep (se 1 (by rfl) ⟨2559164, by rfl⟩ : syracuseStep 3412219 = 5118329) B5118329
theorem B4549625 : Blo 2021435 4549625 := bstep (se 2 (by rfl) ⟨1706109, by rfl⟩ : syracuseStep 4549625 = 3412219) B3412219
theorem B3033083 : Blo 2021435 3033083 := bstep (se 1 (by rfl) ⟨2274812, by rfl⟩ : syracuseStep 3033083 = 4549625) B4549625
theorem B2022055 : Blo 2021435 2022055 := bstep (se 1 (by rfl) ⟨1516541, by rfl⟩ : syracuseStep 2022055 = 3033083) B3033083
theorem B2274817 : Blo 2021435 2274817 := bbase (se 2 (by rfl) ⟨853056, by rfl⟩ : syracuseStep 2274817 = 1706113) (by norm_num)
theorem B3033089 : Blo 2021435 3033089 := bstep (se 2 (by rfl) ⟨1137408, by rfl⟩ : syracuseStep 3033089 = 2274817) B2274817
theorem B2022059 : Blo 2021435 2022059 := bstep (se 1 (by rfl) ⟨1516544, by rfl⟩ : syracuseStep 2022059 = 3033089) B3033089
theorem B5118349 : Blo 2021435 5118349 := bbase (se 3 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 5118349 = 1919381) (by norm_num)
theorem B6824465 : Blo 2021435 6824465 := bstep (se 2 (by rfl) ⟨2559174, by rfl⟩ : syracuseStep 6824465 = 5118349) B5118349
theorem B4549643 : Blo 2021435 4549643 := bstep (se 1 (by rfl) ⟨3412232, by rfl⟩ : syracuseStep 4549643 = 6824465) B6824465
theorem B3033095 : Blo 2021435 3033095 := bstep (se 1 (by rfl) ⟨2274821, by rfl⟩ : syracuseStep 3033095 = 4549643) B4549643
theorem B2022063 : Blo 2021435 2022063 := bstep (se 1 (by rfl) ⟨1516547, by rfl⟩ : syracuseStep 2022063 = 3033095) B3033095
theorem B3033101 : Blo 2021435 3033101 := bbase (se 3 (by rfl) ⟨568706, by rfl⟩ : syracuseStep 3033101 = 1137413) (by norm_num)
theorem B2022067 : Blo 2021435 2022067 := bstep (se 1 (by rfl) ⟨1516550, by rfl⟩ : syracuseStep 2022067 = 3033101) B3033101
theorem B4549661 : Blo 2021435 4549661 := bbase (se 3 (by rfl) ⟨853061, by rfl⟩ : syracuseStep 4549661 = 1706123) (by norm_num)
theorem B3033107 : Blo 2021435 3033107 := bstep (se 1 (by rfl) ⟨2274830, by rfl⟩ : syracuseStep 3033107 = 4549661) B4549661
theorem B2022071 : Blo 2021435 2022071 := bstep (se 1 (by rfl) ⟨1516553, by rfl⟩ : syracuseStep 2022071 = 3033107) B3033107
theorem B3412253 : Blo 2021435 3412253 := bbase (se 3 (by rfl) ⟨639797, by rfl⟩ : syracuseStep 3412253 = 1279595) (by norm_num)
theorem B2274835 : Blo 2021435 2274835 := bstep (se 1 (by rfl) ⟨1706126, by rfl⟩ : syracuseStep 2274835 = 3412253) B3412253
theorem B3033113 : Blo 2021435 3033113 := bstep (se 2 (by rfl) ⟨1137417, by rfl⟩ : syracuseStep 3033113 = 2274835) B2274835
theorem B2022075 : Blo 2021435 2022075 := bstep (se 1 (by rfl) ⟨1516556, by rfl⟩ : syracuseStep 2022075 = 3033113) B3033113
theorem B12955925 : Blo 2021435 12955925 := bbase (se 6 (by rfl) ⟨303654, by rfl⟩ : syracuseStep 12955925 = 607309) (by norm_num)
theorem B8637283 : Blo 2021435 8637283 := bstep (se 1 (by rfl) ⟨6477962, by rfl⟩ : syracuseStep 8637283 = 12955925) B12955925
theorem B11516377 : Blo 2021435 11516377 := bstep (se 2 (by rfl) ⟨4318641, by rfl⟩ : syracuseStep 11516377 = 8637283) B8637283
theorem B15355169 : Blo 2021435 15355169 := bstep (se 2 (by rfl) ⟨5758188, by rfl⟩ : syracuseStep 15355169 = 11516377) B11516377
theorem B10236779 : Blo 2021435 10236779 := bstep (se 1 (by rfl) ⟨7677584, by rfl⟩ : syracuseStep 10236779 = 15355169) B15355169
theorem B6824519 : Blo 2021435 6824519 := bstep (se 1 (by rfl) ⟨5118389, by rfl⟩ : syracuseStep 6824519 = 10236779) B10236779
theorem B4549679 : Blo 2021435 4549679 := bstep (se 1 (by rfl) ⟨3412259, by rfl⟩ : syracuseStep 4549679 = 6824519) B6824519
theorem B3033119 : Blo 2021435 3033119 := bstep (se 1 (by rfl) ⟨2274839, by rfl⟩ : syracuseStep 3033119 = 4549679) B4549679
theorem B2022079 : Blo 2021435 2022079 := bstep (se 1 (by rfl) ⟨1516559, by rfl⟩ : syracuseStep 2022079 = 3033119) B3033119
theorem B3033125 : Blo 2021435 3033125 := bbase (se 4 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 3033125 = 568711) (by norm_num)
theorem B2022083 : Blo 2021435 2022083 := bstep (se 1 (by rfl) ⟨1516562, by rfl⟩ : syracuseStep 2022083 = 3033125) B3033125
theorem B2559205 : Blo 2021435 2559205 := bbase (se 4 (by rfl) ⟨239925, by rfl⟩ : syracuseStep 2559205 = 479851) (by norm_num)
theorem B3412273 : Blo 2021435 3412273 := bstep (se 2 (by rfl) ⟨1279602, by rfl⟩ : syracuseStep 3412273 = 2559205) B2559205
theorem B4549697 : Blo 2021435 4549697 := bstep (se 2 (by rfl) ⟨1706136, by rfl⟩ : syracuseStep 4549697 = 3412273) B3412273
theorem B3033131 : Blo 2021435 3033131 := bstep (se 1 (by rfl) ⟨2274848, by rfl⟩ : syracuseStep 3033131 = 4549697) B4549697
theorem B2022087 : Blo 2021435 2022087 := bstep (se 1 (by rfl) ⟨1516565, by rfl⟩ : syracuseStep 2022087 = 3033131) B3033131
theorem B2274853 : Blo 2021435 2274853 := bbase (se 4 (by rfl) ⟨213267, by rfl⟩ : syracuseStep 2274853 = 426535) (by norm_num)
theorem B3033137 : Blo 2021435 3033137 := bstep (se 2 (by rfl) ⟨1137426, by rfl⟩ : syracuseStep 3033137 = 2274853) B2274853
theorem B2022091 : Blo 2021435 2022091 := bstep (se 1 (by rfl) ⟨1516568, by rfl⟩ : syracuseStep 2022091 = 3033137) B3033137
theorem B4437325 : Blo 2021435 4437325 := bbase (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) (by norm_num)
theorem B5916433 : Blo 2021435 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B504868949 : Blo 2021435 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B336579299 : Blo 2021435 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B224386199 : Blo 2021435 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B149590799 : Blo 2021435 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B99727199 : Blo 2021435 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B66484799 : Blo 2021435 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B44323199 : Blo 2021435 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B29548799 : Blo 2021435 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B19699199 : Blo 2021435 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B13132799 : Blo 2021435 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B8755199 : Blo 2021435 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B5836799 : Blo 2021435 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B3891199 : Blo 2021435 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B5188265 : Blo 2021435 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B3458843 : Blo 2021435 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B36894325 : Blo 2021435 36894325 := bstep (se 5 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 36894325 = 3458843) B3458843
theorem B49192433 : Blo 2021435 49192433 := bstep (se 2 (by rfl) ⟨18447162, by rfl⟩ : syracuseStep 49192433 = 36894325) B36894325
theorem B32794955 : Blo 2021435 32794955 := bstep (se 1 (by rfl) ⟨24596216, by rfl⟩ : syracuseStep 32794955 = 49192433) B49192433
theorem B21863303 : Blo 2021435 21863303 := bstep (se 1 (by rfl) ⟨16397477, by rfl⟩ : syracuseStep 21863303 = 32794955) B32794955
theorem B14575535 : Blo 2021435 14575535 := bstep (se 1 (by rfl) ⟨10931651, by rfl⟩ : syracuseStep 14575535 = 21863303) B21863303
theorem B9717023 : Blo 2021435 9717023 := bstep (se 1 (by rfl) ⟨7287767, by rfl⟩ : syracuseStep 9717023 = 14575535) B14575535
theorem B6478015 : Blo 2021435 6478015 := bstep (se 1 (by rfl) ⟨4858511, by rfl⟩ : syracuseStep 6478015 = 9717023) B9717023
theorem B8637353 : Blo 2021435 8637353 := bstep (se 2 (by rfl) ⟨3239007, by rfl⟩ : syracuseStep 8637353 = 6478015) B6478015
theorem B5758235 : Blo 2021435 5758235 := bstep (se 1 (by rfl) ⟨4318676, by rfl⟩ : syracuseStep 5758235 = 8637353) B8637353
theorem B3838823 : Blo 2021435 3838823 := bstep (se 1 (by rfl) ⟨2879117, by rfl⟩ : syracuseStep 3838823 = 5758235) B5758235
theorem B2559215 : Blo 2021435 2559215 := bstep (se 1 (by rfl) ⟨1919411, by rfl⟩ : syracuseStep 2559215 = 3838823) B3838823
theorem B6824573 : Blo 2021435 6824573 := bstep (se 3 (by rfl) ⟨1279607, by rfl⟩ : syracuseStep 6824573 = 2559215) B2559215
theorem B4549715 : Blo 2021435 4549715 := bstep (se 1 (by rfl) ⟨3412286, by rfl⟩ : syracuseStep 4549715 = 6824573) B6824573
theorem B3033143 : Blo 2021435 3033143 := bstep (se 1 (by rfl) ⟨2274857, by rfl⟩ : syracuseStep 3033143 = 4549715) B4549715
theorem B2022095 : Blo 2021435 2022095 := bstep (se 1 (by rfl) ⟨1516571, by rfl⟩ : syracuseStep 2022095 = 3033143) B3033143
theorem B3033149 : Blo 2021435 3033149 := bbase (se 3 (by rfl) ⟨568715, by rfl⟩ : syracuseStep 3033149 = 1137431) (by norm_num)
theorem B2022099 : Blo 2021435 2022099 := bstep (se 1 (by rfl) ⟨1516574, by rfl⟩ : syracuseStep 2022099 = 3033149) B3033149
theorem B4549733 : Blo 2021435 4549733 := bbase (se 4 (by rfl) ⟨426537, by rfl⟩ : syracuseStep 4549733 = 853075) (by norm_num)
theorem B3033155 : Blo 2021435 3033155 := bstep (se 1 (by rfl) ⟨2274866, by rfl⟩ : syracuseStep 3033155 = 4549733) B4549733
theorem B2022103 : Blo 2021435 2022103 := bstep (se 1 (by rfl) ⟨1516577, by rfl⟩ : syracuseStep 2022103 = 3033155) B3033155
theorem B5118461 : Blo 2021435 5118461 := bbase (se 3 (by rfl) ⟨959711, by rfl⟩ : syracuseStep 5118461 = 1919423) (by norm_num)
theorem B3412307 : Blo 2021435 3412307 := bstep (se 1 (by rfl) ⟨2559230, by rfl⟩ : syracuseStep 3412307 = 5118461) B5118461
theorem B2274871 : Blo 2021435 2274871 := bstep (se 1 (by rfl) ⟨1706153, by rfl⟩ : syracuseStep 2274871 = 3412307) B3412307
theorem B3033161 : Blo 2021435 3033161 := bstep (se 2 (by rfl) ⟨1137435, by rfl⟩ : syracuseStep 3033161 = 2274871) B2274871
theorem B2022107 : Blo 2021435 2022107 := bstep (se 1 (by rfl) ⟨1516580, by rfl⟩ : syracuseStep 2022107 = 3033161) B3033161
theorem B3838853 : Blo 2021435 3838853 := bbase (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) (by norm_num)
theorem B10236941 : Blo 2021435 10236941 := bstep (se 3 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 10236941 = 3838853) B3838853
theorem B6824627 : Blo 2021435 6824627 := bstep (se 1 (by rfl) ⟨5118470, by rfl⟩ : syracuseStep 6824627 = 10236941) B10236941
theorem B4549751 : Blo 2021435 4549751 := bstep (se 1 (by rfl) ⟨3412313, by rfl⟩ : syracuseStep 4549751 = 6824627) B6824627
theorem B3033167 : Blo 2021435 3033167 := bstep (se 1 (by rfl) ⟨2274875, by rfl⟩ : syracuseStep 3033167 = 4549751) B4549751
theorem B2022111 : Blo 2021435 2022111 := bstep (se 1 (by rfl) ⟨1516583, by rfl⟩ : syracuseStep 2022111 = 3033167) B3033167
theorem B3033173 : Blo 2021435 3033173 := bbase (se 8 (by rfl) ⟨17772, by rfl⟩ : syracuseStep 3033173 = 35545) (by norm_num)
theorem B2022115 : Blo 2021435 2022115 := bstep (se 1 (by rfl) ⟨1516586, by rfl⟩ : syracuseStep 2022115 = 3033173) B3033173
theorem B2049709 : Blo 2021435 2049709 := bbase (se 3 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 2049709 = 768641) (by norm_num)
theorem B2732945 : Blo 2021435 2732945 := bstep (se 2 (by rfl) ⟨1024854, by rfl⟩ : syracuseStep 2732945 = 2049709) B2049709
theorem B29151413 : Blo 2021435 29151413 := bstep (se 5 (by rfl) ⟨1366472, by rfl⟩ : syracuseStep 29151413 = 2732945) B2732945
theorem B19434275 : Blo 2021435 19434275 := bstep (se 1 (by rfl) ⟨14575706, by rfl⟩ : syracuseStep 19434275 = 29151413) B29151413
theorem B12956183 : Blo 2021435 12956183 := bstep (se 1 (by rfl) ⟨9717137, by rfl⟩ : syracuseStep 12956183 = 19434275) B19434275
theorem B8637455 : Blo 2021435 8637455 := bstep (se 1 (by rfl) ⟨6478091, by rfl⟩ : syracuseStep 8637455 = 12956183) B12956183
theorem B5758303 : Blo 2021435 5758303 := bstep (se 1 (by rfl) ⟨4318727, by rfl⟩ : syracuseStep 5758303 = 8637455) B8637455
theorem B7677737 : Blo 2021435 7677737 := bstep (se 2 (by rfl) ⟨2879151, by rfl⟩ : syracuseStep 7677737 = 5758303) B5758303
theorem B5118491 : Blo 2021435 5118491 := bstep (se 1 (by rfl) ⟨3838868, by rfl⟩ : syracuseStep 5118491 = 7677737) B7677737
theorem B3412327 : Blo 2021435 3412327 := bstep (se 1 (by rfl) ⟨2559245, by rfl⟩ : syracuseStep 3412327 = 5118491) B5118491
theorem B4549769 : Blo 2021435 4549769 := bstep (se 2 (by rfl) ⟨1706163, by rfl⟩ : syracuseStep 4549769 = 3412327) B3412327
theorem B3033179 : Blo 2021435 3033179 := bstep (se 1 (by rfl) ⟨2274884, by rfl⟩ : syracuseStep 3033179 = 4549769) B4549769
theorem B2022119 : Blo 2021435 2022119 := bstep (se 1 (by rfl) ⟨1516589, by rfl⟩ : syracuseStep 2022119 = 3033179) B3033179
theorem B2274889 : Blo 2021435 2274889 := bbase (se 2 (by rfl) ⟨853083, by rfl⟩ : syracuseStep 2274889 = 1706167) (by norm_num)
theorem B3033185 : Blo 2021435 3033185 := bstep (se 2 (by rfl) ⟨1137444, by rfl⟩ : syracuseStep 3033185 = 2274889) B2274889
theorem B2022123 : Blo 2021435 2022123 := bstep (se 1 (by rfl) ⟨1516592, by rfl⟩ : syracuseStep 2022123 = 3033185) B3033185
theorem B10376693 : Blo 2021435 10376693 := bbase (se 5 (by rfl) ⟨486407, by rfl⟩ : syracuseStep 10376693 = 972815) (by norm_num)
theorem B6917795 : Blo 2021435 6917795 := bstep (se 1 (by rfl) ⟨5188346, by rfl⟩ : syracuseStep 6917795 = 10376693) B10376693
theorem B4611863 : Blo 2021435 4611863 := bstep (se 1 (by rfl) ⟨3458897, by rfl⟩ : syracuseStep 4611863 = 6917795) B6917795
theorem B12298301 : Blo 2021435 12298301 := bstep (se 3 (by rfl) ⟨2305931, by rfl⟩ : syracuseStep 12298301 = 4611863) B4611863
theorem B8198867 : Blo 2021435 8198867 := bstep (se 1 (by rfl) ⟨6149150, by rfl⟩ : syracuseStep 8198867 = 12298301) B12298301
theorem B21863645 : Blo 2021435 21863645 := bstep (se 3 (by rfl) ⟨4099433, by rfl⟩ : syracuseStep 21863645 = 8198867) B8198867
theorem B14575763 : Blo 2021435 14575763 := bstep (se 1 (by rfl) ⟨10931822, by rfl⟩ : syracuseStep 14575763 = 21863645) B21863645
theorem B9717175 : Blo 2021435 9717175 := bstep (se 1 (by rfl) ⟨7287881, by rfl⟩ : syracuseStep 9717175 = 14575763) B14575763
theorem B12956233 : Blo 2021435 12956233 := bstep (se 2 (by rfl) ⟨4858587, by rfl⟩ : syracuseStep 12956233 = 9717175) B9717175
theorem B17274977 : Blo 2021435 17274977 := bstep (se 2 (by rfl) ⟨6478116, by rfl⟩ : syracuseStep 17274977 = 12956233) B12956233
theorem B11516651 : Blo 2021435 11516651 := bstep (se 1 (by rfl) ⟨8637488, by rfl⟩ : syracuseStep 11516651 = 17274977) B17274977
theorem B7677767 : Blo 2021435 7677767 := bstep (se 1 (by rfl) ⟨5758325, by rfl⟩ : syracuseStep 7677767 = 11516651) B11516651
theorem B5118511 : Blo 2021435 5118511 := bstep (se 1 (by rfl) ⟨3838883, by rfl⟩ : syracuseStep 5118511 = 7677767) B7677767
theorem B6824681 : Blo 2021435 6824681 := bstep (se 2 (by rfl) ⟨2559255, by rfl⟩ : syracuseStep 6824681 = 5118511) B5118511
theorem B4549787 : Blo 2021435 4549787 := bstep (se 1 (by rfl) ⟨3412340, by rfl⟩ : syracuseStep 4549787 = 6824681) B6824681
theorem B3033191 : Blo 2021435 3033191 := bstep (se 1 (by rfl) ⟨2274893, by rfl⟩ : syracuseStep 3033191 = 4549787) B4549787
theorem B2022127 : Blo 2021435 2022127 := bstep (se 1 (by rfl) ⟨1516595, by rfl⟩ : syracuseStep 2022127 = 3033191) B3033191
theorem B3033197 : Blo 2021435 3033197 := bbase (se 3 (by rfl) ⟨568724, by rfl⟩ : syracuseStep 3033197 = 1137449) (by norm_num)
theorem B2022131 : Blo 2021435 2022131 := bstep (se 1 (by rfl) ⟨1516598, by rfl⟩ : syracuseStep 2022131 = 3033197) B3033197
theorem B4549805 : Blo 2021435 4549805 := bbase (se 3 (by rfl) ⟨853088, by rfl⟩ : syracuseStep 4549805 = 1706177) (by norm_num)
theorem B3033203 : Blo 2021435 3033203 := bstep (se 1 (by rfl) ⟨2274902, by rfl⟩ : syracuseStep 3033203 = 4549805) B4549805
theorem B2022135 : Blo 2021435 2022135 := bstep (se 1 (by rfl) ⟨1516601, by rfl⟩ : syracuseStep 2022135 = 3033203) B3033203
theorem B2429309 : Blo 2021435 2429309 := bbase (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) (by norm_num)
theorem B6478157 : Blo 2021435 6478157 := bstep (se 3 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 6478157 = 2429309) B2429309
theorem B4318771 : Blo 2021435 4318771 := bstep (se 1 (by rfl) ⟨3239078, by rfl⟩ : syracuseStep 4318771 = 6478157) B6478157
theorem B5758361 : Blo 2021435 5758361 := bstep (se 2 (by rfl) ⟨2159385, by rfl⟩ : syracuseStep 5758361 = 4318771) B4318771
theorem B3838907 : Blo 2021435 3838907 := bstep (se 1 (by rfl) ⟨2879180, by rfl⟩ : syracuseStep 3838907 = 5758361) B5758361
theorem B2559271 : Blo 2021435 2559271 := bstep (se 1 (by rfl) ⟨1919453, by rfl⟩ : syracuseStep 2559271 = 3838907) B3838907
theorem B3412361 : Blo 2021435 3412361 := bstep (se 2 (by rfl) ⟨1279635, by rfl⟩ : syracuseStep 3412361 = 2559271) B2559271
theorem B2274907 : Blo 2021435 2274907 := bstep (se 1 (by rfl) ⟨1706180, by rfl⟩ : syracuseStep 2274907 = 3412361) B3412361
theorem B3033209 : Blo 2021435 3033209 := bstep (se 2 (by rfl) ⟨1137453, by rfl⟩ : syracuseStep 3033209 = 2274907) B2274907
theorem B2022139 : Blo 2021435 2022139 := bstep (se 1 (by rfl) ⟨1516604, by rfl⟩ : syracuseStep 2022139 = 3033209) B3033209
theorem B2049733 : Blo 2021435 2049733 := bbase (se 4 (by rfl) ⟨192162, by rfl⟩ : syracuseStep 2049733 = 384325) (by norm_num)
theorem B2732977 : Blo 2021435 2732977 := bstep (se 2 (by rfl) ⟨1024866, by rfl⟩ : syracuseStep 2732977 = 2049733) B2049733
theorem B14575877 : Blo 2021435 14575877 := bstep (se 4 (by rfl) ⟨1366488, by rfl⟩ : syracuseStep 14575877 = 2732977) B2732977
theorem B9717251 : Blo 2021435 9717251 := bstep (se 1 (by rfl) ⟨7287938, by rfl⟩ : syracuseStep 9717251 = 14575877) B14575877
theorem B25912669 : Blo 2021435 25912669 := bstep (se 3 (by rfl) ⟨4858625, by rfl⟩ : syracuseStep 25912669 = 9717251) B9717251
theorem B34550225 : Blo 2021435 34550225 := bstep (se 2 (by rfl) ⟨12956334, by rfl⟩ : syracuseStep 34550225 = 25912669) B25912669
theorem B23033483 : Blo 2021435 23033483 := bstep (se 1 (by rfl) ⟨17275112, by rfl⟩ : syracuseStep 23033483 = 34550225) B34550225
theorem B15355655 : Blo 2021435 15355655 := bstep (se 1 (by rfl) ⟨11516741, by rfl⟩ : syracuseStep 15355655 = 23033483) B23033483
theorem B10237103 : Blo 2021435 10237103 := bstep (se 1 (by rfl) ⟨7677827, by rfl⟩ : syracuseStep 10237103 = 15355655) B15355655
theorem B6824735 : Blo 2021435 6824735 := bstep (se 1 (by rfl) ⟨5118551, by rfl⟩ : syracuseStep 6824735 = 10237103) B10237103
theorem B4549823 : Blo 2021435 4549823 := bstep (se 1 (by rfl) ⟨3412367, by rfl⟩ : syracuseStep 4549823 = 6824735) B6824735
theorem B3033215 : Blo 2021435 3033215 := bstep (se 1 (by rfl) ⟨2274911, by rfl⟩ : syracuseStep 3033215 = 4549823) B4549823
theorem B2022143 : Blo 2021435 2022143 := bstep (se 1 (by rfl) ⟨1516607, by rfl⟩ : syracuseStep 2022143 = 3033215) B3033215
theorem B3033221 : Blo 2021435 3033221 := bbase (se 4 (by rfl) ⟨284364, by rfl⟩ : syracuseStep 3033221 = 568729) (by norm_num)
theorem B2022147 : Blo 2021435 2022147 := bstep (se 1 (by rfl) ⟨1516610, by rfl⟩ : syracuseStep 2022147 = 3033221) B3033221
theorem B3412381 : Blo 2021435 3412381 := bbase (se 3 (by rfl) ⟨639821, by rfl⟩ : syracuseStep 3412381 = 1279643) (by norm_num)
theorem B4549841 : Blo 2021435 4549841 := bstep (se 2 (by rfl) ⟨1706190, by rfl⟩ : syracuseStep 4549841 = 3412381) B3412381
theorem B3033227 : Blo 2021435 3033227 := bstep (se 1 (by rfl) ⟨2274920, by rfl⟩ : syracuseStep 3033227 = 4549841) B4549841
theorem B2022151 : Blo 2021435 2022151 := bstep (se 1 (by rfl) ⟨1516613, by rfl⟩ : syracuseStep 2022151 = 3033227) B3033227
theorem B2274925 : Blo 2021435 2274925 := bbase (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) (by norm_num)
theorem B3033233 : Blo 2021435 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B2022155 : Blo 2021435 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B6824789 : Blo 2021435 6824789 := bbase (se 9 (by rfl) ⟨19994, by rfl⟩ : syracuseStep 6824789 = 39989) (by norm_num)
theorem B4549859 : Blo 2021435 4549859 := bstep (se 1 (by rfl) ⟨3412394, by rfl⟩ : syracuseStep 4549859 = 6824789) B6824789
theorem B3033239 : Blo 2021435 3033239 := bstep (se 1 (by rfl) ⟨2274929, by rfl⟩ : syracuseStep 3033239 = 4549859) B4549859
theorem B2022159 : Blo 2021435 2022159 := bstep (se 1 (by rfl) ⟨1516619, by rfl⟩ : syracuseStep 2022159 = 3033239) B3033239
theorem B3033245 : Blo 2021435 3033245 := bbase (se 3 (by rfl) ⟨568733, by rfl⟩ : syracuseStep 3033245 = 1137467) (by norm_num)
theorem B2022163 : Blo 2021435 2022163 := bstep (se 1 (by rfl) ⟨1516622, by rfl⟩ : syracuseStep 2022163 = 3033245) B3033245
theorem B4549877 : Blo 2021435 4549877 := bbase (se 5 (by rfl) ⟨213275, by rfl⟩ : syracuseStep 4549877 = 426551) (by norm_num)
theorem B3033251 : Blo 2021435 3033251 := bstep (se 1 (by rfl) ⟨2274938, by rfl⟩ : syracuseStep 3033251 = 4549877) B4549877
theorem B2022167 : Blo 2021435 2022167 := bstep (se 1 (by rfl) ⟨1516625, by rfl⟩ : syracuseStep 2022167 = 3033251) B3033251
theorem B6149285 : Blo 2021435 6149285 := bbase (se 4 (by rfl) ⟨576495, by rfl⟩ : syracuseStep 6149285 = 1152991) (by norm_num)
theorem B4099523 : Blo 2021435 4099523 := bstep (se 1 (by rfl) ⟨3074642, by rfl⟩ : syracuseStep 4099523 = 6149285) B6149285
theorem B43728245 : Blo 2021435 43728245 := bstep (se 5 (by rfl) ⟨2049761, by rfl⟩ : syracuseStep 43728245 = 4099523) B4099523
theorem B29152163 : Blo 2021435 29152163 := bstep (se 1 (by rfl) ⟨21864122, by rfl⟩ : syracuseStep 29152163 = 43728245) B43728245
theorem B19434775 : Blo 2021435 19434775 := bstep (se 1 (by rfl) ⟨14576081, by rfl⟩ : syracuseStep 19434775 = 29152163) B29152163
theorem B25913033 : Blo 2021435 25913033 := bstep (se 2 (by rfl) ⟨9717387, by rfl⟩ : syracuseStep 25913033 = 19434775) B19434775
theorem B17275355 : Blo 2021435 17275355 := bstep (se 1 (by rfl) ⟨12956516, by rfl⟩ : syracuseStep 17275355 = 25913033) B25913033
theorem B11516903 : Blo 2021435 11516903 := bstep (se 1 (by rfl) ⟨8637677, by rfl⟩ : syracuseStep 11516903 = 17275355) B17275355
theorem B7677935 : Blo 2021435 7677935 := bstep (se 1 (by rfl) ⟨5758451, by rfl⟩ : syracuseStep 7677935 = 11516903) B11516903
theorem B5118623 : Blo 2021435 5118623 := bstep (se 1 (by rfl) ⟨3838967, by rfl⟩ : syracuseStep 5118623 = 7677935) B7677935
theorem B3412415 : Blo 2021435 3412415 := bstep (se 1 (by rfl) ⟨2559311, by rfl⟩ : syracuseStep 3412415 = 5118623) B5118623
theorem B2274943 : Blo 2021435 2274943 := bstep (se 1 (by rfl) ⟨1706207, by rfl⟩ : syracuseStep 2274943 = 3412415) B3412415
theorem B3033257 : Blo 2021435 3033257 := bstep (se 2 (by rfl) ⟨1137471, by rfl⟩ : syracuseStep 3033257 = 2274943) B2274943
theorem B2022171 : Blo 2021435 2022171 := bstep (se 1 (by rfl) ⟨1516628, by rfl⟩ : syracuseStep 2022171 = 3033257) B3033257
theorem B2770309 : Blo 2021435 2770309 := bbase (se 4 (by rfl) ⟨259716, by rfl⟩ : syracuseStep 2770309 = 519433) (by norm_num)
theorem B3693745 : Blo 2021435 3693745 := bstep (se 2 (by rfl) ⟨1385154, by rfl⟩ : syracuseStep 3693745 = 2770309) B2770309
theorem B4924993 : Blo 2021435 4924993 := bstep (se 2 (by rfl) ⟨1846872, by rfl⟩ : syracuseStep 4924993 = 3693745) B3693745
theorem B6566657 : Blo 2021435 6566657 := bstep (se 2 (by rfl) ⟨2462496, by rfl⟩ : syracuseStep 6566657 = 4924993) B4924993
theorem B17511085 : Blo 2021435 17511085 := bstep (se 3 (by rfl) ⟨3283328, by rfl⟩ : syracuseStep 17511085 = 6566657) B6566657
theorem B93392453 : Blo 2021435 93392453 := bstep (se 4 (by rfl) ⟨8755542, by rfl⟩ : syracuseStep 93392453 = 17511085) B17511085
theorem B62261635 : Blo 2021435 62261635 := bstep (se 1 (by rfl) ⟨46696226, by rfl⟩ : syracuseStep 62261635 = 93392453) B93392453
theorem B83015513 : Blo 2021435 83015513 := bstep (se 2 (by rfl) ⟨31130817, by rfl⟩ : syracuseStep 83015513 = 62261635) B62261635
theorem B55343675 : Blo 2021435 55343675 := bstep (se 1 (by rfl) ⟨41507756, by rfl⟩ : syracuseStep 55343675 = 83015513) B83015513
theorem B36895783 : Blo 2021435 36895783 := bstep (se 1 (by rfl) ⟨27671837, by rfl⟩ : syracuseStep 36895783 = 55343675) B55343675
theorem B49194377 : Blo 2021435 49194377 := bstep (se 2 (by rfl) ⟨18447891, by rfl⟩ : syracuseStep 49194377 = 36895783) B36895783
theorem B32796251 : Blo 2021435 32796251 := bstep (se 1 (by rfl) ⟨24597188, by rfl⟩ : syracuseStep 32796251 = 49194377) B49194377
theorem B21864167 : Blo 2021435 21864167 := bstep (se 1 (by rfl) ⟨16398125, by rfl⟩ : syracuseStep 21864167 = 32796251) B32796251
theorem B14576111 : Blo 2021435 14576111 := bstep (se 1 (by rfl) ⟨10932083, by rfl⟩ : syracuseStep 14576111 = 21864167) B21864167
theorem B9717407 : Blo 2021435 9717407 := bstep (se 1 (by rfl) ⟨7288055, by rfl⟩ : syracuseStep 9717407 = 14576111) B14576111
theorem B6478271 : Blo 2021435 6478271 := bstep (se 1 (by rfl) ⟨4858703, by rfl⟩ : syracuseStep 6478271 = 9717407) B9717407
theorem B4318847 : Blo 2021435 4318847 := bstep (se 1 (by rfl) ⟨3239135, by rfl⟩ : syracuseStep 4318847 = 6478271) B6478271
theorem B2879231 : Blo 2021435 2879231 := bstep (se 1 (by rfl) ⟨2159423, by rfl⟩ : syracuseStep 2879231 = 4318847) B4318847
theorem B7677949 : Blo 2021435 7677949 := bstep (se 3 (by rfl) ⟨1439615, by rfl⟩ : syracuseStep 7677949 = 2879231) B2879231
theorem B10237265 : Blo 2021435 10237265 := bstep (se 2 (by rfl) ⟨3838974, by rfl⟩ : syracuseStep 10237265 = 7677949) B7677949
theorem B6824843 : Blo 2021435 6824843 := bstep (se 1 (by rfl) ⟨5118632, by rfl⟩ : syracuseStep 6824843 = 10237265) B10237265
theorem B4549895 : Blo 2021435 4549895 := bstep (se 1 (by rfl) ⟨3412421, by rfl⟩ : syracuseStep 4549895 = 6824843) B6824843
theorem B3033263 : Blo 2021435 3033263 := bstep (se 1 (by rfl) ⟨2274947, by rfl⟩ : syracuseStep 3033263 = 4549895) B4549895
theorem B2022175 : Blo 2021435 2022175 := bstep (se 1 (by rfl) ⟨1516631, by rfl⟩ : syracuseStep 2022175 = 3033263) B3033263
theorem B3033269 : Blo 2021435 3033269 := bbase (se 5 (by rfl) ⟨142184, by rfl⟩ : syracuseStep 3033269 = 284369) (by norm_num)
theorem B2022179 : Blo 2021435 2022179 := bstep (se 1 (by rfl) ⟨1516634, by rfl⟩ : syracuseStep 2022179 = 3033269) B3033269
theorem B5118653 : Blo 2021435 5118653 := bbase (se 3 (by rfl) ⟨959747, by rfl⟩ : syracuseStep 5118653 = 1919495) (by norm_num)
theorem B3412435 : Blo 2021435 3412435 := bstep (se 1 (by rfl) ⟨2559326, by rfl⟩ : syracuseStep 3412435 = 5118653) B5118653
theorem B4549913 : Blo 2021435 4549913 := bstep (se 2 (by rfl) ⟨1706217, by rfl⟩ : syracuseStep 4549913 = 3412435) B3412435
theorem B3033275 : Blo 2021435 3033275 := bstep (se 1 (by rfl) ⟨2274956, by rfl⟩ : syracuseStep 3033275 = 4549913) B4549913
theorem B2022183 : Blo 2021435 2022183 := bstep (se 1 (by rfl) ⟨1516637, by rfl⟩ : syracuseStep 2022183 = 3033275) B3033275
theorem B2274961 : Blo 2021435 2274961 := bbase (se 2 (by rfl) ⟨853110, by rfl⟩ : syracuseStep 2274961 = 1706221) (by norm_num)
theorem B3033281 : Blo 2021435 3033281 := bstep (se 2 (by rfl) ⟨1137480, by rfl⟩ : syracuseStep 3033281 = 2274961) B2274961
theorem B2022187 : Blo 2021435 2022187 := bstep (se 1 (by rfl) ⟨1516640, by rfl⟩ : syracuseStep 2022187 = 3033281) B3033281
theorem B3839005 : Blo 2021435 3839005 := bbase (se 3 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 3839005 = 1439627) (by norm_num)
theorem B5118673 : Blo 2021435 5118673 := bstep (se 2 (by rfl) ⟨1919502, by rfl⟩ : syracuseStep 5118673 = 3839005) B3839005
theorem B6824897 : Blo 2021435 6824897 := bstep (se 2 (by rfl) ⟨2559336, by rfl⟩ : syracuseStep 6824897 = 5118673) B5118673
theorem B4549931 : Blo 2021435 4549931 := bstep (se 1 (by rfl) ⟨3412448, by rfl⟩ : syracuseStep 4549931 = 6824897) B6824897
theorem B3033287 : Blo 2021435 3033287 := bstep (se 1 (by rfl) ⟨2274965, by rfl⟩ : syracuseStep 3033287 = 4549931) B4549931
theorem B2022191 : Blo 2021435 2022191 := bstep (se 1 (by rfl) ⟨1516643, by rfl⟩ : syracuseStep 2022191 = 3033287) B3033287
theorem B3033293 : Blo 2021435 3033293 := bbase (se 3 (by rfl) ⟨568742, by rfl⟩ : syracuseStep 3033293 = 1137485) (by norm_num)
theorem B2022195 : Blo 2021435 2022195 := bstep (se 1 (by rfl) ⟨1516646, by rfl⟩ : syracuseStep 2022195 = 3033293) B3033293
theorem B4549949 : Blo 2021435 4549949 := bbase (se 3 (by rfl) ⟨853115, by rfl⟩ : syracuseStep 4549949 = 1706231) (by norm_num)
theorem B3033299 : Blo 2021435 3033299 := bstep (se 1 (by rfl) ⟨2274974, by rfl⟩ : syracuseStep 3033299 = 4549949) B4549949
theorem B2022199 : Blo 2021435 2022199 := bstep (se 1 (by rfl) ⟨1516649, by rfl⟩ : syracuseStep 2022199 = 3033299) B3033299
theorem B3412469 : Blo 2021435 3412469 := bbase (se 5 (by rfl) ⟨159959, by rfl⟩ : syracuseStep 3412469 = 319919) (by norm_num)
theorem B2274979 : Blo 2021435 2274979 := bstep (se 1 (by rfl) ⟨1706234, by rfl⟩ : syracuseStep 2274979 = 3412469) B3412469
theorem B3033305 : Blo 2021435 3033305 := bstep (se 2 (by rfl) ⟨1137489, by rfl⟩ : syracuseStep 3033305 = 2274979) B2274979
theorem B2022203 : Blo 2021435 2022203 := bstep (se 1 (by rfl) ⟨1516652, by rfl⟩ : syracuseStep 2022203 = 3033305) B3033305
theorem B6478373 : Blo 2021435 6478373 := bbase (se 4 (by rfl) ⟨607347, by rfl⟩ : syracuseStep 6478373 = 1214695) (by norm_num)
theorem B4318915 : Blo 2021435 4318915 := bstep (se 1 (by rfl) ⟨3239186, by rfl⟩ : syracuseStep 4318915 = 6478373) B6478373
theorem B5758553 : Blo 2021435 5758553 := bstep (se 2 (by rfl) ⟨2159457, by rfl⟩ : syracuseStep 5758553 = 4318915) B4318915
theorem B15356141 : Blo 2021435 15356141 := bstep (se 3 (by rfl) ⟨2879276, by rfl⟩ : syracuseStep 15356141 = 5758553) B5758553
theorem B10237427 : Blo 2021435 10237427 := bstep (se 1 (by rfl) ⟨7678070, by rfl⟩ : syracuseStep 10237427 = 15356141) B15356141
theorem B6824951 : Blo 2021435 6824951 := bstep (se 1 (by rfl) ⟨5118713, by rfl⟩ : syracuseStep 6824951 = 10237427) B10237427
theorem B4549967 : Blo 2021435 4549967 := bstep (se 1 (by rfl) ⟨3412475, by rfl⟩ : syracuseStep 4549967 = 6824951) B6824951
theorem B3033311 : Blo 2021435 3033311 := bstep (se 1 (by rfl) ⟨2274983, by rfl⟩ : syracuseStep 3033311 = 4549967) B4549967
theorem B2022207 : Blo 2021435 2022207 := bstep (se 1 (by rfl) ⟨1516655, by rfl⟩ : syracuseStep 2022207 = 3033311) B3033311
theorem B3033317 : Blo 2021435 3033317 := bbase (se 4 (by rfl) ⟨284373, by rfl⟩ : syracuseStep 3033317 = 568747) (by norm_num)
theorem B2022211 : Blo 2021435 2022211 := bstep (se 1 (by rfl) ⟨1516658, by rfl⟩ : syracuseStep 2022211 = 3033317) B3033317
theorem B4318933 : Blo 2021435 4318933 := bbase (se 7 (by rfl) ⟨50612, by rfl⟩ : syracuseStep 4318933 = 101225) (by norm_num)
theorem B5758577 : Blo 2021435 5758577 := bstep (se 2 (by rfl) ⟨2159466, by rfl⟩ : syracuseStep 5758577 = 4318933) B4318933
theorem B3839051 : Blo 2021435 3839051 := bstep (se 1 (by rfl) ⟨2879288, by rfl⟩ : syracuseStep 3839051 = 5758577) B5758577
theorem B2559367 : Blo 2021435 2559367 := bstep (se 1 (by rfl) ⟨1919525, by rfl⟩ : syracuseStep 2559367 = 3839051) B3839051
theorem B3412489 : Blo 2021435 3412489 := bstep (se 2 (by rfl) ⟨1279683, by rfl⟩ : syracuseStep 3412489 = 2559367) B2559367
theorem B4549985 : Blo 2021435 4549985 := bstep (se 2 (by rfl) ⟨1706244, by rfl⟩ : syracuseStep 4549985 = 3412489) B3412489
theorem B3033323 : Blo 2021435 3033323 := bstep (se 1 (by rfl) ⟨2274992, by rfl⟩ : syracuseStep 3033323 = 4549985) B4549985
theorem B2022215 : Blo 2021435 2022215 := bstep (se 1 (by rfl) ⟨1516661, by rfl⟩ : syracuseStep 2022215 = 3033323) B3033323
theorem B2274997 : Blo 2021435 2274997 := bbase (se 5 (by rfl) ⟨106640, by rfl⟩ : syracuseStep 2274997 = 213281) (by norm_num)
theorem B3033329 : Blo 2021435 3033329 := bstep (se 2 (by rfl) ⟨1137498, by rfl⟩ : syracuseStep 3033329 = 2274997) B2274997
theorem B2022219 : Blo 2021435 2022219 := bstep (se 1 (by rfl) ⟨1516664, by rfl⟩ : syracuseStep 2022219 = 3033329) B3033329
theorem B2559377 : Blo 2021435 2559377 := bbase (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) (by norm_num)
theorem B6825005 : Blo 2021435 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B4550003 : Blo 2021435 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B3033335 : Blo 2021435 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B2022223 : Blo 2021435 2022223 := bstep (se 1 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 2022223 = 3033335) B3033335
theorem B3033341 : Blo 2021435 3033341 := bbase (se 3 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 3033341 = 1137503) (by norm_num)
theorem B2022227 : Blo 2021435 2022227 := bstep (se 1 (by rfl) ⟨1516670, by rfl⟩ : syracuseStep 2022227 = 3033341) B3033341
theorem B4550021 : Blo 2021435 4550021 := bbase (se 4 (by rfl) ⟨426564, by rfl⟩ : syracuseStep 4550021 = 853129) (by norm_num)
theorem B3033347 : Blo 2021435 3033347 := bstep (se 1 (by rfl) ⟨2275010, by rfl⟩ : syracuseStep 3033347 = 4550021) B4550021
theorem B2022231 : Blo 2021435 2022231 := bstep (se 1 (by rfl) ⟨1516673, by rfl⟩ : syracuseStep 2022231 = 3033347) B3033347
theorem B2879317 : Blo 2021435 2879317 := bbase (se 9 (by rfl) ⟨8435, by rfl⟩ : syracuseStep 2879317 = 16871) (by norm_num)
theorem B3839089 : Blo 2021435 3839089 := bstep (se 2 (by rfl) ⟨1439658, by rfl⟩ : syracuseStep 3839089 = 2879317) B2879317
theorem B5118785 : Blo 2021435 5118785 := bstep (se 2 (by rfl) ⟨1919544, by rfl⟩ : syracuseStep 5118785 = 3839089) B3839089
theorem B3412523 : Blo 2021435 3412523 := bstep (se 1 (by rfl) ⟨2559392, by rfl⟩ : syracuseStep 3412523 = 5118785) B5118785
theorem B2275015 : Blo 2021435 2275015 := bstep (se 1 (by rfl) ⟨1706261, by rfl⟩ : syracuseStep 2275015 = 3412523) B3412523
theorem B3033353 : Blo 2021435 3033353 := bstep (se 2 (by rfl) ⟨1137507, by rfl⟩ : syracuseStep 3033353 = 2275015) B2275015
theorem B2022235 : Blo 2021435 2022235 := bstep (se 1 (by rfl) ⟨1516676, by rfl⟩ : syracuseStep 2022235 = 3033353) B3033353
theorem B10237589 : Blo 2021435 10237589 := bbase (se 6 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 10237589 = 479887) (by norm_num)
theorem B6825059 : Blo 2021435 6825059 := bstep (se 1 (by rfl) ⟨5118794, by rfl⟩ : syracuseStep 6825059 = 10237589) B10237589
theorem B4550039 : Blo 2021435 4550039 := bstep (se 1 (by rfl) ⟨3412529, by rfl⟩ : syracuseStep 4550039 = 6825059) B6825059
theorem B3033359 : Blo 2021435 3033359 := bstep (se 1 (by rfl) ⟨2275019, by rfl⟩ : syracuseStep 3033359 = 4550039) B4550039
theorem B2022239 : Blo 2021435 2022239 := bstep (se 1 (by rfl) ⟨1516679, by rfl⟩ : syracuseStep 2022239 = 3033359) B3033359
theorem B3033365 : Blo 2021435 3033365 := bbase (se 6 (by rfl) ⟨71094, by rfl⟩ : syracuseStep 3033365 = 142189) (by norm_num)
theorem B2022243 : Blo 2021435 2022243 := bstep (se 1 (by rfl) ⟨1516682, by rfl⟩ : syracuseStep 2022243 = 3033365) B3033365
theorem B25914005 : Blo 2021435 25914005 := bbase (se 6 (by rfl) ⟨607359, by rfl⟩ : syracuseStep 25914005 = 1214719) (by norm_num)
theorem B17276003 : Blo 2021435 17276003 := bstep (se 1 (by rfl) ⟨12957002, by rfl⟩ : syracuseStep 17276003 = 25914005) B25914005
theorem B11517335 : Blo 2021435 11517335 := bstep (se 1 (by rfl) ⟨8638001, by rfl⟩ : syracuseStep 11517335 = 17276003) B17276003
theorem B7678223 : Blo 2021435 7678223 := bstep (se 1 (by rfl) ⟨5758667, by rfl⟩ : syracuseStep 7678223 = 11517335) B11517335
theorem B5118815 : Blo 2021435 5118815 := bstep (se 1 (by rfl) ⟨3839111, by rfl⟩ : syracuseStep 5118815 = 7678223) B7678223
theorem B3412543 : Blo 2021435 3412543 := bstep (se 1 (by rfl) ⟨2559407, by rfl⟩ : syracuseStep 3412543 = 5118815) B5118815
theorem B4550057 : Blo 2021435 4550057 := bstep (se 2 (by rfl) ⟨1706271, by rfl⟩ : syracuseStep 4550057 = 3412543) B3412543
theorem B3033371 : Blo 2021435 3033371 := bstep (se 1 (by rfl) ⟨2275028, by rfl⟩ : syracuseStep 3033371 = 4550057) B4550057
theorem B2022247 : Blo 2021435 2022247 := bstep (se 1 (by rfl) ⟨1516685, by rfl⟩ : syracuseStep 2022247 = 3033371) B3033371
theorem B2275033 : Blo 2021435 2275033 := bbase (se 2 (by rfl) ⟨853137, by rfl⟩ : syracuseStep 2275033 = 1706275) (by norm_num)
theorem B3033377 : Blo 2021435 3033377 := bstep (se 2 (by rfl) ⟨1137516, by rfl⟩ : syracuseStep 3033377 = 2275033) B2275033
theorem B2022251 : Blo 2021435 2022251 := bstep (se 1 (by rfl) ⟨1516688, by rfl⟩ : syracuseStep 2022251 = 3033377) B3033377
theorem B2159509 : Blo 2021435 2159509 := bbase (se 6 (by rfl) ⟨50613, by rfl⟩ : syracuseStep 2159509 = 101227) (by norm_num)
theorem B2879345 : Blo 2021435 2879345 := bstep (se 2 (by rfl) ⟨1079754, by rfl⟩ : syracuseStep 2879345 = 2159509) B2159509
theorem B7678253 : Blo 2021435 7678253 := bstep (se 3 (by rfl) ⟨1439672, by rfl⟩ : syracuseStep 7678253 = 2879345) B2879345
theorem B5118835 : Blo 2021435 5118835 := bstep (se 1 (by rfl) ⟨3839126, by rfl⟩ : syracuseStep 5118835 = 7678253) B7678253
theorem B6825113 : Blo 2021435 6825113 := bstep (se 2 (by rfl) ⟨2559417, by rfl⟩ : syracuseStep 6825113 = 5118835) B5118835
theorem B4550075 : Blo 2021435 4550075 := bstep (se 1 (by rfl) ⟨3412556, by rfl⟩ : syracuseStep 4550075 = 6825113) B6825113
theorem B3033383 : Blo 2021435 3033383 := bstep (se 1 (by rfl) ⟨2275037, by rfl⟩ : syracuseStep 3033383 = 4550075) B4550075
theorem B2022255 : Blo 2021435 2022255 := bstep (se 1 (by rfl) ⟨1516691, by rfl⟩ : syracuseStep 2022255 = 3033383) B3033383
theorem B3033389 : Blo 2021435 3033389 := bbase (se 3 (by rfl) ⟨568760, by rfl⟩ : syracuseStep 3033389 = 1137521) (by norm_num)
theorem B2022259 : Blo 2021435 2022259 := bstep (se 1 (by rfl) ⟨1516694, by rfl⟩ : syracuseStep 2022259 = 3033389) B3033389
theorem B4550093 : Blo 2021435 4550093 := bbase (se 3 (by rfl) ⟨853142, by rfl⟩ : syracuseStep 4550093 = 1706285) (by norm_num)
theorem B3033395 : Blo 2021435 3033395 := bstep (se 1 (by rfl) ⟨2275046, by rfl⟩ : syracuseStep 3033395 = 4550093) B4550093
theorem B2022263 : Blo 2021435 2022263 := bstep (se 1 (by rfl) ⟨1516697, by rfl⟩ : syracuseStep 2022263 = 3033395) B3033395
theorem B2559433 : Blo 2021435 2559433 := bbase (se 2 (by rfl) ⟨959787, by rfl⟩ : syracuseStep 2559433 = 1919575) (by norm_num)
theorem B3412577 : Blo 2021435 3412577 := bstep (se 2 (by rfl) ⟨1279716, by rfl⟩ : syracuseStep 3412577 = 2559433) B2559433
theorem B2275051 : Blo 2021435 2275051 := bstep (se 1 (by rfl) ⟨1706288, by rfl⟩ : syracuseStep 2275051 = 3412577) B3412577
theorem B3033401 : Blo 2021435 3033401 := bstep (se 2 (by rfl) ⟨1137525, by rfl⟩ : syracuseStep 3033401 = 2275051) B2275051
theorem B2022267 : Blo 2021435 2022267 := bstep (se 1 (by rfl) ⟨1516700, by rfl⟩ : syracuseStep 2022267 = 3033401) B3033401
theorem B19435733 : Blo 2021435 19435733 := bbase (se 7 (by rfl) ⟨227762, by rfl⟩ : syracuseStep 19435733 = 455525) (by norm_num)
theorem B12957155 : Blo 2021435 12957155 := bstep (se 1 (by rfl) ⟨9717866, by rfl⟩ : syracuseStep 12957155 = 19435733) B19435733
theorem B8638103 : Blo 2021435 8638103 := bstep (se 1 (by rfl) ⟨6478577, by rfl⟩ : syracuseStep 8638103 = 12957155) B12957155
theorem B23034941 : Blo 2021435 23034941 := bstep (se 3 (by rfl) ⟨4319051, by rfl⟩ : syracuseStep 23034941 = 8638103) B8638103
theorem B15356627 : Blo 2021435 15356627 := bstep (se 1 (by rfl) ⟨11517470, by rfl⟩ : syracuseStep 15356627 = 23034941) B23034941
theorem B10237751 : Blo 2021435 10237751 := bstep (se 1 (by rfl) ⟨7678313, by rfl⟩ : syracuseStep 10237751 = 15356627) B15356627
theorem B6825167 : Blo 2021435 6825167 := bstep (se 1 (by rfl) ⟨5118875, by rfl⟩ : syracuseStep 6825167 = 10237751) B10237751
theorem B4550111 : Blo 2021435 4550111 := bstep (se 1 (by rfl) ⟨3412583, by rfl⟩ : syracuseStep 4550111 = 6825167) B6825167
theorem B3033407 : Blo 2021435 3033407 := bstep (se 1 (by rfl) ⟨2275055, by rfl⟩ : syracuseStep 3033407 = 4550111) B4550111
theorem B2022271 : Blo 2021435 2022271 := bstep (se 1 (by rfl) ⟨1516703, by rfl⟩ : syracuseStep 2022271 = 3033407) B3033407
theorem B3033413 : Blo 2021435 3033413 := bbase (se 4 (by rfl) ⟨284382, by rfl⟩ : syracuseStep 3033413 = 568765) (by norm_num)
theorem B2022275 : Blo 2021435 2022275 := bstep (se 1 (by rfl) ⟨1516706, by rfl⟩ : syracuseStep 2022275 = 3033413) B3033413
theorem B3412597 : Blo 2021435 3412597 := bbase (se 5 (by rfl) ⟨159965, by rfl⟩ : syracuseStep 3412597 = 319931) (by norm_num)
theorem B4550129 : Blo 2021435 4550129 := bstep (se 2 (by rfl) ⟨1706298, by rfl⟩ : syracuseStep 4550129 = 3412597) B3412597
theorem B3033419 : Blo 2021435 3033419 := bstep (se 1 (by rfl) ⟨2275064, by rfl⟩ : syracuseStep 3033419 = 4550129) B4550129
theorem B2022279 : Blo 2021435 2022279 := bstep (se 1 (by rfl) ⟨1516709, by rfl⟩ : syracuseStep 2022279 = 3033419) B3033419
theorem B2275069 : Blo 2021435 2275069 := bbase (se 3 (by rfl) ⟨426575, by rfl⟩ : syracuseStep 2275069 = 853151) (by norm_num)
theorem B3033425 : Blo 2021435 3033425 := bstep (se 2 (by rfl) ⟨1137534, by rfl⟩ : syracuseStep 3033425 = 2275069) B2275069
theorem B2022283 : Blo 2021435 2022283 := bstep (se 1 (by rfl) ⟨1516712, by rfl⟩ : syracuseStep 2022283 = 3033425) B3033425
theorem B6825221 : Blo 2021435 6825221 := bbase (se 4 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 6825221 = 1279729) (by norm_num)
theorem B4550147 : Blo 2021435 4550147 := bstep (se 1 (by rfl) ⟨3412610, by rfl⟩ : syracuseStep 4550147 = 6825221) B6825221
theorem B3033431 : Blo 2021435 3033431 := bstep (se 1 (by rfl) ⟨2275073, by rfl⟩ : syracuseStep 3033431 = 4550147) B4550147
theorem B2022287 : Blo 2021435 2022287 := bstep (se 1 (by rfl) ⟨1516715, by rfl⟩ : syracuseStep 2022287 = 3033431) B3033431
theorem B3033437 : Blo 2021435 3033437 := bbase (se 3 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 3033437 = 1137539) (by norm_num)
theorem B2022291 : Blo 2021435 2022291 := bstep (se 1 (by rfl) ⟨1516718, by rfl⟩ : syracuseStep 2022291 = 3033437) B3033437
theorem B4550165 : Blo 2021435 4550165 := bbase (se 6 (by rfl) ⟨106644, by rfl⟩ : syracuseStep 4550165 = 213289) (by norm_num)
theorem B3033443 : Blo 2021435 3033443 := bstep (se 1 (by rfl) ⟨2275082, by rfl⟩ : syracuseStep 3033443 = 4550165) B4550165
theorem B2022295 : Blo 2021435 2022295 := bstep (se 1 (by rfl) ⟨1516721, by rfl⟩ : syracuseStep 2022295 = 3033443) B3033443
theorem B7678421 : Blo 2021435 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B5118947 : Blo 2021435 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B3412631 : Blo 2021435 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B2275087 : Blo 2021435 2275087 := bstep (se 1 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 2275087 = 3412631) B3412631
theorem B3033449 : Blo 2021435 3033449 := bstep (se 2 (by rfl) ⟨1137543, by rfl⟩ : syracuseStep 3033449 = 2275087) B2275087
theorem B2022299 : Blo 2021435 2022299 := bstep (se 1 (by rfl) ⟨1516724, by rfl⟩ : syracuseStep 2022299 = 3033449) B3033449
theorem B11517653 : Blo 2021435 11517653 := bbase (se 7 (by rfl) ⟨134972, by rfl⟩ : syracuseStep 11517653 = 269945) (by norm_num)
theorem B7678435 : Blo 2021435 7678435 := bstep (se 1 (by rfl) ⟨5758826, by rfl⟩ : syracuseStep 7678435 = 11517653) B11517653
theorem B10237913 : Blo 2021435 10237913 := bstep (se 2 (by rfl) ⟨3839217, by rfl⟩ : syracuseStep 10237913 = 7678435) B7678435
theorem B6825275 : Blo 2021435 6825275 := bstep (se 1 (by rfl) ⟨5118956, by rfl⟩ : syracuseStep 6825275 = 10237913) B10237913
theorem B4550183 : Blo 2021435 4550183 := bstep (se 1 (by rfl) ⟨3412637, by rfl⟩ : syracuseStep 4550183 = 6825275) B6825275
theorem B3033455 : Blo 2021435 3033455 := bstep (se 1 (by rfl) ⟨2275091, by rfl⟩ : syracuseStep 3033455 = 4550183) B4550183
theorem B2022303 : Blo 2021435 2022303 := bstep (se 1 (by rfl) ⟨1516727, by rfl⟩ : syracuseStep 2022303 = 3033455) B3033455
theorem B3033461 : Blo 2021435 3033461 := bbase (se 5 (by rfl) ⟨142193, by rfl⟩ : syracuseStep 3033461 = 284387) (by norm_num)
theorem B2022307 : Blo 2021435 2022307 := bstep (se 1 (by rfl) ⟨1516730, by rfl⟩ : syracuseStep 2022307 = 3033461) B3033461
theorem B2159569 : Blo 2021435 2159569 := bbase (se 2 (by rfl) ⟨809838, by rfl⟩ : syracuseStep 2159569 = 1619677) (by norm_num)
theorem B2879425 : Blo 2021435 2879425 := bstep (se 2 (by rfl) ⟨1079784, by rfl⟩ : syracuseStep 2879425 = 2159569) B2159569
theorem B3839233 : Blo 2021435 3839233 := bstep (se 2 (by rfl) ⟨1439712, by rfl⟩ : syracuseStep 3839233 = 2879425) B2879425
theorem B5118977 : Blo 2021435 5118977 := bstep (se 2 (by rfl) ⟨1919616, by rfl⟩ : syracuseStep 5118977 = 3839233) B3839233
theorem B3412651 : Blo 2021435 3412651 := bstep (se 1 (by rfl) ⟨2559488, by rfl⟩ : syracuseStep 3412651 = 5118977) B5118977
theorem B4550201 : Blo 2021435 4550201 := bstep (se 2 (by rfl) ⟨1706325, by rfl⟩ : syracuseStep 4550201 = 3412651) B3412651
theorem B3033467 : Blo 2021435 3033467 := bstep (se 1 (by rfl) ⟨2275100, by rfl⟩ : syracuseStep 3033467 = 4550201) B4550201
theorem B2022311 : Blo 2021435 2022311 := bstep (se 1 (by rfl) ⟨1516733, by rfl⟩ : syracuseStep 2022311 = 3033467) B3033467
theorem B2275105 : Blo 2021435 2275105 := bbase (se 2 (by rfl) ⟨853164, by rfl⟩ : syracuseStep 2275105 = 1706329) (by norm_num)
theorem B3033473 : Blo 2021435 3033473 := bstep (se 2 (by rfl) ⟨1137552, by rfl⟩ : syracuseStep 3033473 = 2275105) B2275105
theorem B2022315 : Blo 2021435 2022315 := bstep (se 1 (by rfl) ⟨1516736, by rfl⟩ : syracuseStep 2022315 = 3033473) B3033473
theorem B5118997 : Blo 2021435 5118997 := bbase (se 6 (by rfl) ⟨119976, by rfl⟩ : syracuseStep 5118997 = 239953) (by norm_num)
theorem B6825329 : Blo 2021435 6825329 := bstep (se 2 (by rfl) ⟨2559498, by rfl⟩ : syracuseStep 6825329 = 5118997) B5118997
theorem B4550219 : Blo 2021435 4550219 := bstep (se 1 (by rfl) ⟨3412664, by rfl⟩ : syracuseStep 4550219 = 6825329) B6825329
theorem B3033479 : Blo 2021435 3033479 := bstep (se 1 (by rfl) ⟨2275109, by rfl⟩ : syracuseStep 3033479 = 4550219) B4550219
theorem B2022319 : Blo 2021435 2022319 := bstep (se 1 (by rfl) ⟨1516739, by rfl⟩ : syracuseStep 2022319 = 3033479) B3033479
theorem B3033485 : Blo 2021435 3033485 := bbase (se 3 (by rfl) ⟨568778, by rfl⟩ : syracuseStep 3033485 = 1137557) (by norm_num)
theorem B2022323 : Blo 2021435 2022323 := bstep (se 1 (by rfl) ⟨1516742, by rfl⟩ : syracuseStep 2022323 = 3033485) B3033485
theorem B4550237 : Blo 2021435 4550237 := bbase (se 3 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 4550237 = 1706339) (by norm_num)
theorem B3033491 : Blo 2021435 3033491 := bstep (se 1 (by rfl) ⟨2275118, by rfl⟩ : syracuseStep 3033491 = 4550237) B4550237
theorem B2022327 : Blo 2021435 2022327 := bstep (se 1 (by rfl) ⟨1516745, by rfl⟩ : syracuseStep 2022327 = 3033491) B3033491
theorem B3412685 : Blo 2021435 3412685 := bbase (se 3 (by rfl) ⟨639878, by rfl⟩ : syracuseStep 3412685 = 1279757) (by norm_num)
theorem B2275123 : Blo 2021435 2275123 := bstep (se 1 (by rfl) ⟨1706342, by rfl⟩ : syracuseStep 2275123 = 3412685) B3412685
theorem B3033497 : Blo 2021435 3033497 := bstep (se 2 (by rfl) ⟨1137561, by rfl⟩ : syracuseStep 3033497 = 2275123) B2275123
theorem B2022331 : Blo 2021435 2022331 := bstep (se 1 (by rfl) ⟨1516748, by rfl⟩ : syracuseStep 2022331 = 3033497) B3033497
theorem B13837013 : Blo 2021435 13837013 := bbase (se 7 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 13837013 = 324305) (by norm_num)
theorem B9224675 : Blo 2021435 9224675 := bstep (se 1 (by rfl) ⟨6918506, by rfl⟩ : syracuseStep 9224675 = 13837013) B13837013
theorem B6149783 : Blo 2021435 6149783 := bstep (se 1 (by rfl) ⟨4612337, by rfl⟩ : syracuseStep 6149783 = 9224675) B9224675
theorem B16399421 : Blo 2021435 16399421 := bstep (se 3 (by rfl) ⟨3074891, by rfl⟩ : syracuseStep 16399421 = 6149783) B6149783
theorem B10932947 : Blo 2021435 10932947 := bstep (se 1 (by rfl) ⟨8199710, by rfl⟩ : syracuseStep 10932947 = 16399421) B16399421
theorem B7288631 : Blo 2021435 7288631 := bstep (se 1 (by rfl) ⟨5466473, by rfl⟩ : syracuseStep 7288631 = 10932947) B10932947
theorem B4859087 : Blo 2021435 4859087 := bstep (se 1 (by rfl) ⟨3644315, by rfl⟩ : syracuseStep 4859087 = 7288631) B7288631
theorem B12957565 : Blo 2021435 12957565 := bstep (se 3 (by rfl) ⟨2429543, by rfl⟩ : syracuseStep 12957565 = 4859087) B4859087
theorem B17276753 : Blo 2021435 17276753 := bstep (se 2 (by rfl) ⟨6478782, by rfl⟩ : syracuseStep 17276753 = 12957565) B12957565
theorem B11517835 : Blo 2021435 11517835 := bstep (se 1 (by rfl) ⟨8638376, by rfl⟩ : syracuseStep 11517835 = 17276753) B17276753
theorem B15357113 : Blo 2021435 15357113 := bstep (se 2 (by rfl) ⟨5758917, by rfl⟩ : syracuseStep 15357113 = 11517835) B11517835
theorem B10238075 : Blo 2021435 10238075 := bstep (se 1 (by rfl) ⟨7678556, by rfl⟩ : syracuseStep 10238075 = 15357113) B15357113
theorem B6825383 : Blo 2021435 6825383 := bstep (se 1 (by rfl) ⟨5119037, by rfl⟩ : syracuseStep 6825383 = 10238075) B10238075
theorem B4550255 : Blo 2021435 4550255 := bstep (se 1 (by rfl) ⟨3412691, by rfl⟩ : syracuseStep 4550255 = 6825383) B6825383
theorem B3033503 : Blo 2021435 3033503 := bstep (se 1 (by rfl) ⟨2275127, by rfl⟩ : syracuseStep 3033503 = 4550255) B4550255
theorem B2022335 : Blo 2021435 2022335 := bstep (se 1 (by rfl) ⟨1516751, by rfl⟩ : syracuseStep 2022335 = 3033503) B3033503
theorem B3033509 : Blo 2021435 3033509 := bbase (se 4 (by rfl) ⟨284391, by rfl⟩ : syracuseStep 3033509 = 568783) (by norm_num)
theorem B2022339 : Blo 2021435 2022339 := bstep (se 1 (by rfl) ⟨1516754, by rfl⟩ : syracuseStep 2022339 = 3033509) B3033509
theorem B2559529 : Blo 2021435 2559529 := bbase (se 2 (by rfl) ⟨959823, by rfl⟩ : syracuseStep 2559529 = 1919647) (by norm_num)
theorem B3412705 : Blo 2021435 3412705 := bstep (se 2 (by rfl) ⟨1279764, by rfl⟩ : syracuseStep 3412705 = 2559529) B2559529
theorem B4550273 : Blo 2021435 4550273 := bstep (se 2 (by rfl) ⟨1706352, by rfl⟩ : syracuseStep 4550273 = 3412705) B3412705
theorem B3033515 : Blo 2021435 3033515 := bstep (se 1 (by rfl) ⟨2275136, by rfl⟩ : syracuseStep 3033515 = 4550273) B4550273
theorem B2022343 : Blo 2021435 2022343 := bstep (se 1 (by rfl) ⟨1516757, by rfl⟩ : syracuseStep 2022343 = 3033515) B3033515
theorem B2275141 : Blo 2021435 2275141 := bbase (se 4 (by rfl) ⟨213294, by rfl⟩ : syracuseStep 2275141 = 426589) (by norm_num)
theorem B3033521 : Blo 2021435 3033521 := bstep (se 2 (by rfl) ⟨1137570, by rfl⟩ : syracuseStep 3033521 = 2275141) B2275141
theorem B2022347 : Blo 2021435 2022347 := bstep (se 1 (by rfl) ⟨1516760, by rfl⟩ : syracuseStep 2022347 = 3033521) B3033521
theorem B3839309 : Blo 2021435 3839309 := bbase (se 3 (by rfl) ⟨719870, by rfl⟩ : syracuseStep 3839309 = 1439741) (by norm_num)
theorem B2559539 : Blo 2021435 2559539 := bstep (se 1 (by rfl) ⟨1919654, by rfl⟩ : syracuseStep 2559539 = 3839309) B3839309
theorem B6825437 : Blo 2021435 6825437 := bstep (se 3 (by rfl) ⟨1279769, by rfl⟩ : syracuseStep 6825437 = 2559539) B2559539
theorem B4550291 : Blo 2021435 4550291 := bstep (se 1 (by rfl) ⟨3412718, by rfl⟩ : syracuseStep 4550291 = 6825437) B6825437
theorem B3033527 : Blo 2021435 3033527 := bstep (se 1 (by rfl) ⟨2275145, by rfl⟩ : syracuseStep 3033527 = 4550291) B4550291
theorem B2022351 : Blo 2021435 2022351 := bstep (se 1 (by rfl) ⟨1516763, by rfl⟩ : syracuseStep 2022351 = 3033527) B3033527
theorem B3033533 : Blo 2021435 3033533 := bbase (se 3 (by rfl) ⟨568787, by rfl⟩ : syracuseStep 3033533 = 1137575) (by norm_num)
theorem B2022355 : Blo 2021435 2022355 := bstep (se 1 (by rfl) ⟨1516766, by rfl⟩ : syracuseStep 2022355 = 3033533) B3033533
theorem B4550309 : Blo 2021435 4550309 := bbase (se 4 (by rfl) ⟨426591, by rfl⟩ : syracuseStep 4550309 = 853183) (by norm_num)
theorem B3033539 : Blo 2021435 3033539 := bstep (se 1 (by rfl) ⟨2275154, by rfl⟩ : syracuseStep 3033539 = 4550309) B4550309
theorem B2022359 : Blo 2021435 2022359 := bstep (se 1 (by rfl) ⟨1516769, by rfl⟩ : syracuseStep 2022359 = 3033539) B3033539
theorem B5119109 : Blo 2021435 5119109 := bbase (se 4 (by rfl) ⟨479916, by rfl⟩ : syracuseStep 5119109 = 959833) (by norm_num)
theorem B3412739 : Blo 2021435 3412739 := bstep (se 1 (by rfl) ⟨2559554, by rfl⟩ : syracuseStep 3412739 = 5119109) B5119109
theorem B2275159 : Blo 2021435 2275159 := bstep (se 1 (by rfl) ⟨1706369, by rfl⟩ : syracuseStep 2275159 = 3412739) B3412739
theorem B3033545 : Blo 2021435 3033545 := bstep (se 2 (by rfl) ⟨1137579, by rfl⟩ : syracuseStep 3033545 = 2275159) B2275159
theorem B2022363 : Blo 2021435 2022363 := bstep (se 1 (by rfl) ⟨1516772, by rfl⟩ : syracuseStep 2022363 = 3033545) B3033545
theorem B4859165 : Blo 2021435 4859165 := bbase (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) (by norm_num)
theorem B3239443 : Blo 2021435 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B4319257 : Blo 2021435 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B5759009 : Blo 2021435 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B3839339 : Blo 2021435 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B10238237 : Blo 2021435 10238237 := bstep (se 3 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 10238237 = 3839339) B3839339
theorem B6825491 : Blo 2021435 6825491 := bstep (se 1 (by rfl) ⟨5119118, by rfl⟩ : syracuseStep 6825491 = 10238237) B10238237
theorem B4550327 : Blo 2021435 4550327 := bstep (se 1 (by rfl) ⟨3412745, by rfl⟩ : syracuseStep 4550327 = 6825491) B6825491
theorem B3033551 : Blo 2021435 3033551 := bstep (se 1 (by rfl) ⟨2275163, by rfl⟩ : syracuseStep 3033551 = 4550327) B4550327
theorem B2022367 : Blo 2021435 2022367 := bstep (se 1 (by rfl) ⟨1516775, by rfl⟩ : syracuseStep 2022367 = 3033551) B3033551
theorem B3033557 : Blo 2021435 3033557 := bbase (se 7 (by rfl) ⟨35549, by rfl⟩ : syracuseStep 3033557 = 71099) (by norm_num)
theorem B2022371 : Blo 2021435 2022371 := bstep (se 1 (by rfl) ⟨1516778, by rfl⟩ : syracuseStep 2022371 = 3033557) B3033557
theorem B7678709 : Blo 2021435 7678709 := bbase (se 5 (by rfl) ⟨359939, by rfl⟩ : syracuseStep 7678709 = 719879) (by norm_num)
theorem B5119139 : Blo 2021435 5119139 := bstep (se 1 (by rfl) ⟨3839354, by rfl⟩ : syracuseStep 5119139 = 7678709) B7678709
theorem B3412759 : Blo 2021435 3412759 := bstep (se 1 (by rfl) ⟨2559569, by rfl⟩ : syracuseStep 3412759 = 5119139) B5119139
theorem B4550345 : Blo 2021435 4550345 := bstep (se 2 (by rfl) ⟨1706379, by rfl⟩ : syracuseStep 4550345 = 3412759) B3412759
theorem B3033563 : Blo 2021435 3033563 := bstep (se 1 (by rfl) ⟨2275172, by rfl⟩ : syracuseStep 3033563 = 4550345) B4550345
theorem B2022375 : Blo 2021435 2022375 := bstep (se 1 (by rfl) ⟨1516781, by rfl⟩ : syracuseStep 2022375 = 3033563) B3033563
theorem B2275177 : Blo 2021435 2275177 := bbase (se 2 (by rfl) ⟨853191, by rfl⟩ : syracuseStep 2275177 = 1706383) (by norm_num)
theorem B3033569 : Blo 2021435 3033569 := bstep (se 2 (by rfl) ⟨1137588, by rfl⟩ : syracuseStep 3033569 = 2275177) B2275177
theorem B2022379 : Blo 2021435 2022379 := bstep (se 1 (by rfl) ⟨1516784, by rfl⟩ : syracuseStep 2022379 = 3033569) B3033569
theorem B7288805 : Blo 2021435 7288805 := bbase (se 4 (by rfl) ⟨683325, by rfl⟩ : syracuseStep 7288805 = 1366651) (by norm_num)
theorem B4859203 : Blo 2021435 4859203 := bstep (se 1 (by rfl) ⟨3644402, by rfl⟩ : syracuseStep 4859203 = 7288805) B7288805
theorem B6478937 : Blo 2021435 6478937 := bstep (se 2 (by rfl) ⟨2429601, by rfl⟩ : syracuseStep 6478937 = 4859203) B4859203
theorem B4319291 : Blo 2021435 4319291 := bstep (se 1 (by rfl) ⟨3239468, by rfl⟩ : syracuseStep 4319291 = 6478937) B6478937
theorem B11518109 : Blo 2021435 11518109 := bstep (se 3 (by rfl) ⟨2159645, by rfl⟩ : syracuseStep 11518109 = 4319291) B4319291
theorem B7678739 : Blo 2021435 7678739 := bstep (se 1 (by rfl) ⟨5759054, by rfl⟩ : syracuseStep 7678739 = 11518109) B11518109
theorem B5119159 : Blo 2021435 5119159 := bstep (se 1 (by rfl) ⟨3839369, by rfl⟩ : syracuseStep 5119159 = 7678739) B7678739
theorem B6825545 : Blo 2021435 6825545 := bstep (se 2 (by rfl) ⟨2559579, by rfl⟩ : syracuseStep 6825545 = 5119159) B5119159
theorem B4550363 : Blo 2021435 4550363 := bstep (se 1 (by rfl) ⟨3412772, by rfl⟩ : syracuseStep 4550363 = 6825545) B6825545
theorem B3033575 : Blo 2021435 3033575 := bstep (se 1 (by rfl) ⟨2275181, by rfl⟩ : syracuseStep 3033575 = 4550363) B4550363
theorem B2022383 : Blo 2021435 2022383 := bstep (se 1 (by rfl) ⟨1516787, by rfl⟩ : syracuseStep 2022383 = 3033575) B3033575
theorem B3033581 : Blo 2021435 3033581 := bbase (se 3 (by rfl) ⟨568796, by rfl⟩ : syracuseStep 3033581 = 1137593) (by norm_num)
theorem B2022387 : Blo 2021435 2022387 := bstep (se 1 (by rfl) ⟨1516790, by rfl⟩ : syracuseStep 2022387 = 3033581) B3033581
theorem B4550381 : Blo 2021435 4550381 := bbase (se 3 (by rfl) ⟨853196, by rfl⟩ : syracuseStep 4550381 = 1706393) (by norm_num)
theorem B3033587 : Blo 2021435 3033587 := bstep (se 1 (by rfl) ⟨2275190, by rfl⟩ : syracuseStep 3033587 = 4550381) B4550381
theorem B2022391 : Blo 2021435 2022391 := bstep (se 1 (by rfl) ⟨1516793, by rfl⟩ : syracuseStep 2022391 = 3033587) B3033587
theorem B2429617 : Blo 2021435 2429617 := bbase (se 2 (by rfl) ⟨911106, by rfl⟩ : syracuseStep 2429617 = 1822213) (by norm_num)
theorem B3239489 : Blo 2021435 3239489 := bstep (se 2 (by rfl) ⟨1214808, by rfl⟩ : syracuseStep 3239489 = 2429617) B2429617
theorem B2159659 : Blo 2021435 2159659 := bstep (se 1 (by rfl) ⟨1619744, by rfl⟩ : syracuseStep 2159659 = 3239489) B3239489
theorem B2879545 : Blo 2021435 2879545 := bstep (se 2 (by rfl) ⟨1079829, by rfl⟩ : syracuseStep 2879545 = 2159659) B2159659
theorem B3839393 : Blo 2021435 3839393 := bstep (se 2 (by rfl) ⟨1439772, by rfl⟩ : syracuseStep 3839393 = 2879545) B2879545
theorem B2559595 : Blo 2021435 2559595 := bstep (se 1 (by rfl) ⟨1919696, by rfl⟩ : syracuseStep 2559595 = 3839393) B3839393
theorem B3412793 : Blo 2021435 3412793 := bstep (se 2 (by rfl) ⟨1279797, by rfl⟩ : syracuseStep 3412793 = 2559595) B2559595
theorem B2275195 : Blo 2021435 2275195 := bstep (se 1 (by rfl) ⟨1706396, by rfl⟩ : syracuseStep 2275195 = 3412793) B3412793
theorem B3033593 : Blo 2021435 3033593 := bstep (se 2 (by rfl) ⟨1137597, by rfl⟩ : syracuseStep 3033593 = 2275195) B2275195
theorem B2022395 : Blo 2021435 2022395 := bstep (se 1 (by rfl) ⟨1516796, by rfl⟩ : syracuseStep 2022395 = 3033593) B3033593
theorem B166049365 : Blo 2021435 166049365 := bbase (se 8 (by rfl) ⟨972945, by rfl⟩ : syracuseStep 166049365 = 1945891) (by norm_num)
theorem B221399153 : Blo 2021435 221399153 := bstep (se 2 (by rfl) ⟨83024682, by rfl⟩ : syracuseStep 221399153 = 166049365) B166049365
theorem B147599435 : Blo 2021435 147599435 := bstep (se 1 (by rfl) ⟨110699576, by rfl⟩ : syracuseStep 147599435 = 221399153) B221399153
theorem B98399623 : Blo 2021435 98399623 := bstep (se 1 (by rfl) ⟨73799717, by rfl⟩ : syracuseStep 98399623 = 147599435) B147599435
theorem B131199497 : Blo 2021435 131199497 := bstep (se 2 (by rfl) ⟨49199811, by rfl⟩ : syracuseStep 131199497 = 98399623) B98399623
theorem B87466331 : Blo 2021435 87466331 := bstep (se 1 (by rfl) ⟨65599748, by rfl⟩ : syracuseStep 87466331 = 131199497) B131199497
theorem B58310887 : Blo 2021435 58310887 := bstep (se 1 (by rfl) ⟨43733165, by rfl⟩ : syracuseStep 58310887 = 87466331) B87466331
theorem B77747849 : Blo 2021435 77747849 := bstep (se 2 (by rfl) ⟨29155443, by rfl⟩ : syracuseStep 77747849 = 58310887) B58310887
theorem B51831899 : Blo 2021435 51831899 := bstep (se 1 (by rfl) ⟨38873924, by rfl⟩ : syracuseStep 51831899 = 77747849) B77747849
theorem B34554599 : Blo 2021435 34554599 := bstep (se 1 (by rfl) ⟨25915949, by rfl⟩ : syracuseStep 34554599 = 51831899) B51831899
theorem B23036399 : Blo 2021435 23036399 := bstep (se 1 (by rfl) ⟨17277299, by rfl⟩ : syracuseStep 23036399 = 34554599) B34554599
theorem B15357599 : Blo 2021435 15357599 := bstep (se 1 (by rfl) ⟨11518199, by rfl⟩ : syracuseStep 15357599 = 23036399) B23036399
theorem B10238399 : Blo 2021435 10238399 := bstep (se 1 (by rfl) ⟨7678799, by rfl⟩ : syracuseStep 10238399 = 15357599) B15357599
theorem B6825599 : Blo 2021435 6825599 := bstep (se 1 (by rfl) ⟨5119199, by rfl⟩ : syracuseStep 6825599 = 10238399) B10238399
theorem B4550399 : Blo 2021435 4550399 := bstep (se 1 (by rfl) ⟨3412799, by rfl⟩ : syracuseStep 4550399 = 6825599) B6825599
theorem B3033599 : Blo 2021435 3033599 := bstep (se 1 (by rfl) ⟨2275199, by rfl⟩ : syracuseStep 3033599 = 4550399) B4550399
theorem B2022399 : Blo 2021435 2022399 := bstep (se 1 (by rfl) ⟨1516799, by rfl⟩ : syracuseStep 2022399 = 3033599) B3033599
theorem B3033605 : Blo 2021435 3033605 := bbase (se 4 (by rfl) ⟨284400, by rfl⟩ : syracuseStep 3033605 = 568801) (by norm_num)
theorem B2022403 : Blo 2021435 2022403 := bstep (se 1 (by rfl) ⟨1516802, by rfl⟩ : syracuseStep 2022403 = 3033605) B3033605
theorem B3412813 : Blo 2021435 3412813 := bbase (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) (by norm_num)
theorem B4550417 : Blo 2021435 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B3033611 : Blo 2021435 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B2022407 : Blo 2021435 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B2275213 : Blo 2021435 2275213 := bbase (se 3 (by rfl) ⟨426602, by rfl⟩ : syracuseStep 2275213 = 853205) (by norm_num)
theorem B3033617 : Blo 2021435 3033617 := bstep (se 2 (by rfl) ⟨1137606, by rfl⟩ : syracuseStep 3033617 = 2275213) B2275213
theorem B2022411 : Blo 2021435 2022411 := bstep (se 1 (by rfl) ⟨1516808, by rfl⟩ : syracuseStep 2022411 = 3033617) B3033617
theorem B6825653 : Blo 2021435 6825653 := bbase (se 5 (by rfl) ⟨319952, by rfl⟩ : syracuseStep 6825653 = 639905) (by norm_num)
theorem B4550435 : Blo 2021435 4550435 := bstep (se 1 (by rfl) ⟨3412826, by rfl⟩ : syracuseStep 4550435 = 6825653) B6825653
theorem B3033623 : Blo 2021435 3033623 := bstep (se 1 (by rfl) ⟨2275217, by rfl⟩ : syracuseStep 3033623 = 4550435) B4550435
theorem B2022415 : Blo 2021435 2022415 := bstep (se 1 (by rfl) ⟨1516811, by rfl⟩ : syracuseStep 2022415 = 3033623) B3033623
theorem B3033629 : Blo 2021435 3033629 := bbase (se 3 (by rfl) ⟨568805, by rfl⟩ : syracuseStep 3033629 = 1137611) (by norm_num)
theorem B2022419 : Blo 2021435 2022419 := bstep (se 1 (by rfl) ⟨1516814, by rfl⟩ : syracuseStep 2022419 = 3033629) B3033629
theorem B4550453 : Blo 2021435 4550453 := bbase (se 5 (by rfl) ⟨213302, by rfl⟩ : syracuseStep 4550453 = 426605) (by norm_num)
theorem B3033635 : Blo 2021435 3033635 := bstep (se 1 (by rfl) ⟨2275226, by rfl⟩ : syracuseStep 3033635 = 4550453) B4550453
theorem B2022423 : Blo 2021435 2022423 := bstep (se 1 (by rfl) ⟨1516817, by rfl⟩ : syracuseStep 2022423 = 3033635) B3033635
theorem B4859309 : Blo 2021435 4859309 := bbase (se 3 (by rfl) ⟨911120, by rfl⟩ : syracuseStep 4859309 = 1822241) (by norm_num)
theorem B12958157 : Blo 2021435 12958157 := bstep (se 3 (by rfl) ⟨2429654, by rfl⟩ : syracuseStep 12958157 = 4859309) B4859309
theorem B8638771 : Blo 2021435 8638771 := bstep (se 1 (by rfl) ⟨6479078, by rfl⟩ : syracuseStep 8638771 = 12958157) B12958157
theorem B11518361 : Blo 2021435 11518361 := bstep (se 2 (by rfl) ⟨4319385, by rfl⟩ : syracuseStep 11518361 = 8638771) B8638771
theorem B7678907 : Blo 2021435 7678907 := bstep (se 1 (by rfl) ⟨5759180, by rfl⟩ : syracuseStep 7678907 = 11518361) B11518361
theorem B5119271 : Blo 2021435 5119271 := bstep (se 1 (by rfl) ⟨3839453, by rfl⟩ : syracuseStep 5119271 = 7678907) B7678907
theorem B3412847 : Blo 2021435 3412847 := bstep (se 1 (by rfl) ⟨2559635, by rfl⟩ : syracuseStep 3412847 = 5119271) B5119271
theorem B2275231 : Blo 2021435 2275231 := bstep (se 1 (by rfl) ⟨1706423, by rfl⟩ : syracuseStep 2275231 = 3412847) B3412847
theorem B3033641 : Blo 2021435 3033641 := bstep (se 2 (by rfl) ⟨1137615, by rfl⟩ : syracuseStep 3033641 = 2275231) B2275231
theorem B2022427 : Blo 2021435 2022427 := bstep (se 1 (by rfl) ⟨1516820, by rfl⟩ : syracuseStep 2022427 = 3033641) B3033641
theorem B6567493 : Blo 2021435 6567493 := bbase (se 4 (by rfl) ⟨615702, by rfl⟩ : syracuseStep 6567493 = 1231405) (by norm_num)
theorem B8756657 : Blo 2021435 8756657 := bstep (se 2 (by rfl) ⟨3283746, by rfl⟩ : syracuseStep 8756657 = 6567493) B6567493
theorem B5837771 : Blo 2021435 5837771 := bstep (se 1 (by rfl) ⟨4378328, by rfl⟩ : syracuseStep 5837771 = 8756657) B8756657
theorem B3891847 : Blo 2021435 3891847 := bstep (se 1 (by rfl) ⟨2918885, by rfl⟩ : syracuseStep 3891847 = 5837771) B5837771
theorem B5189129 : Blo 2021435 5189129 := bstep (se 2 (by rfl) ⟨1945923, by rfl⟩ : syracuseStep 5189129 = 3891847) B3891847
theorem B3459419 : Blo 2021435 3459419 := bstep (se 1 (by rfl) ⟨2594564, by rfl⟩ : syracuseStep 3459419 = 5189129) B5189129
theorem B2306279 : Blo 2021435 2306279 := bstep (se 1 (by rfl) ⟨1729709, by rfl⟩ : syracuseStep 2306279 = 3459419) B3459419
theorem B6150077 : Blo 2021435 6150077 := bstep (se 3 (by rfl) ⟨1153139, by rfl⟩ : syracuseStep 6150077 = 2306279) B2306279
theorem B4100051 : Blo 2021435 4100051 := bstep (se 1 (by rfl) ⟨3075038, by rfl⟩ : syracuseStep 4100051 = 6150077) B6150077
theorem B2733367 : Blo 2021435 2733367 := bstep (se 1 (by rfl) ⟨2050025, by rfl⟩ : syracuseStep 2733367 = 4100051) B4100051
theorem B3644489 : Blo 2021435 3644489 := bstep (se 2 (by rfl) ⟨1366683, by rfl⟩ : syracuseStep 3644489 = 2733367) B2733367
theorem B2429659 : Blo 2021435 2429659 := bstep (se 1 (by rfl) ⟨1822244, by rfl⟩ : syracuseStep 2429659 = 3644489) B3644489
theorem B12958181 : Blo 2021435 12958181 := bstep (se 4 (by rfl) ⟨1214829, by rfl⟩ : syracuseStep 12958181 = 2429659) B2429659
theorem B8638787 : Blo 2021435 8638787 := bstep (se 1 (by rfl) ⟨6479090, by rfl⟩ : syracuseStep 8638787 = 12958181) B12958181
theorem B5759191 : Blo 2021435 5759191 := bstep (se 1 (by rfl) ⟨4319393, by rfl⟩ : syracuseStep 5759191 = 8638787) B8638787
theorem B7678921 : Blo 2021435 7678921 := bstep (se 2 (by rfl) ⟨2879595, by rfl⟩ : syracuseStep 7678921 = 5759191) B5759191
theorem B10238561 : Blo 2021435 10238561 := bstep (se 2 (by rfl) ⟨3839460, by rfl⟩ : syracuseStep 10238561 = 7678921) B7678921
theorem B6825707 : Blo 2021435 6825707 := bstep (se 1 (by rfl) ⟨5119280, by rfl⟩ : syracuseStep 6825707 = 10238561) B10238561
theorem B4550471 : Blo 2021435 4550471 := bstep (se 1 (by rfl) ⟨3412853, by rfl⟩ : syracuseStep 4550471 = 6825707) B6825707
theorem B3033647 : Blo 2021435 3033647 := bstep (se 1 (by rfl) ⟨2275235, by rfl⟩ : syracuseStep 3033647 = 4550471) B4550471
theorem B2022431 : Blo 2021435 2022431 := bstep (se 1 (by rfl) ⟨1516823, by rfl⟩ : syracuseStep 2022431 = 3033647) B3033647
theorem B3033653 : Blo 2021435 3033653 := bbase (se 5 (by rfl) ⟨142202, by rfl⟩ : syracuseStep 3033653 = 284405) (by norm_num)
theorem B2022435 : Blo 2021435 2022435 := bstep (se 1 (by rfl) ⟨1516826, by rfl⟩ : syracuseStep 2022435 = 3033653) B3033653
theorem B5119301 : Blo 2021435 5119301 := bbase (se 4 (by rfl) ⟨479934, by rfl⟩ : syracuseStep 5119301 = 959869) (by norm_num)
theorem B3412867 : Blo 2021435 3412867 := bstep (se 1 (by rfl) ⟨2559650, by rfl⟩ : syracuseStep 3412867 = 5119301) B5119301
theorem B4550489 : Blo 2021435 4550489 := bstep (se 2 (by rfl) ⟨1706433, by rfl⟩ : syracuseStep 4550489 = 3412867) B3412867
theorem B3033659 : Blo 2021435 3033659 := bstep (se 1 (by rfl) ⟨2275244, by rfl⟩ : syracuseStep 3033659 = 4550489) B4550489
theorem B2022439 : Blo 2021435 2022439 := bstep (se 1 (by rfl) ⟨1516829, by rfl⟩ : syracuseStep 2022439 = 3033659) B3033659
theorem B2275249 : Blo 2021435 2275249 := bbase (se 2 (by rfl) ⟨853218, by rfl⟩ : syracuseStep 2275249 = 1706437) (by norm_num)
theorem B3033665 : Blo 2021435 3033665 := bstep (se 2 (by rfl) ⟨1137624, by rfl⟩ : syracuseStep 3033665 = 2275249) B2275249
theorem B2022443 : Blo 2021435 2022443 := bstep (se 1 (by rfl) ⟨1516832, by rfl⟩ : syracuseStep 2022443 = 3033665) B3033665
theorem B5759237 : Blo 2021435 5759237 := bbase (se 4 (by rfl) ⟨539928, by rfl⟩ : syracuseStep 5759237 = 1079857) (by norm_num)
theorem B3839491 : Blo 2021435 3839491 := bstep (se 1 (by rfl) ⟨2879618, by rfl⟩ : syracuseStep 3839491 = 5759237) B5759237
theorem B5119321 : Blo 2021435 5119321 := bstep (se 2 (by rfl) ⟨1919745, by rfl⟩ : syracuseStep 5119321 = 3839491) B3839491
theorem B6825761 : Blo 2021435 6825761 := bstep (se 2 (by rfl) ⟨2559660, by rfl⟩ : syracuseStep 6825761 = 5119321) B5119321
theorem B4550507 : Blo 2021435 4550507 := bstep (se 1 (by rfl) ⟨3412880, by rfl⟩ : syracuseStep 4550507 = 6825761) B6825761
theorem B3033671 : Blo 2021435 3033671 := bstep (se 1 (by rfl) ⟨2275253, by rfl⟩ : syracuseStep 3033671 = 4550507) B4550507
theorem B2022447 : Blo 2021435 2022447 := bstep (se 1 (by rfl) ⟨1516835, by rfl⟩ : syracuseStep 2022447 = 3033671) B3033671
theorem B3033677 : Blo 2021435 3033677 := bbase (se 3 (by rfl) ⟨568814, by rfl⟩ : syracuseStep 3033677 = 1137629) (by norm_num)
theorem B2022451 : Blo 2021435 2022451 := bstep (se 1 (by rfl) ⟨1516838, by rfl⟩ : syracuseStep 2022451 = 3033677) B3033677
theorem B4550525 : Blo 2021435 4550525 := bbase (se 3 (by rfl) ⟨853223, by rfl⟩ : syracuseStep 4550525 = 1706447) (by norm_num)
theorem B3033683 : Blo 2021435 3033683 := bstep (se 1 (by rfl) ⟨2275262, by rfl⟩ : syracuseStep 3033683 = 4550525) B4550525
theorem B2022455 : Blo 2021435 2022455 := bstep (se 1 (by rfl) ⟨1516841, by rfl⟩ : syracuseStep 2022455 = 3033683) B3033683
theorem B3412901 : Blo 2021435 3412901 := bbase (se 4 (by rfl) ⟨319959, by rfl⟩ : syracuseStep 3412901 = 639919) (by norm_num)
theorem B2275267 : Blo 2021435 2275267 := bstep (se 1 (by rfl) ⟨1706450, by rfl⟩ : syracuseStep 2275267 = 3412901) B3412901
theorem B3033689 : Blo 2021435 3033689 := bstep (se 2 (by rfl) ⟨1137633, by rfl⟩ : syracuseStep 3033689 = 2275267) B2275267
theorem B2022459 : Blo 2021435 2022459 := bstep (se 1 (by rfl) ⟨1516844, by rfl⟩ : syracuseStep 2022459 = 3033689) B3033689
theorem B3239597 : Blo 2021435 3239597 := bbase (se 3 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 3239597 = 1214849) (by norm_num)
theorem B2159731 : Blo 2021435 2159731 := bstep (se 1 (by rfl) ⟨1619798, by rfl⟩ : syracuseStep 2159731 = 3239597) B3239597
theorem B2879641 : Blo 2021435 2879641 := bstep (se 2 (by rfl) ⟨1079865, by rfl⟩ : syracuseStep 2879641 = 2159731) B2159731
theorem B15358085 : Blo 2021435 15358085 := bstep (se 4 (by rfl) ⟨1439820, by rfl⟩ : syracuseStep 15358085 = 2879641) B2879641
theorem B10238723 : Blo 2021435 10238723 := bstep (se 1 (by rfl) ⟨7679042, by rfl⟩ : syracuseStep 10238723 = 15358085) B15358085
theorem B6825815 : Blo 2021435 6825815 := bstep (se 1 (by rfl) ⟨5119361, by rfl⟩ : syracuseStep 6825815 = 10238723) B10238723
theorem B4550543 : Blo 2021435 4550543 := bstep (se 1 (by rfl) ⟨3412907, by rfl⟩ : syracuseStep 4550543 = 6825815) B6825815
theorem B3033695 : Blo 2021435 3033695 := bstep (se 1 (by rfl) ⟨2275271, by rfl⟩ : syracuseStep 3033695 = 4550543) B4550543
theorem B2022463 : Blo 2021435 2022463 := bstep (se 1 (by rfl) ⟨1516847, by rfl⟩ : syracuseStep 2022463 = 3033695) B3033695
theorem B3033701 : Blo 2021435 3033701 := bbase (se 4 (by rfl) ⟨284409, by rfl⟩ : syracuseStep 3033701 = 568819) (by norm_num)
theorem B2022467 : Blo 2021435 2022467 := bstep (se 1 (by rfl) ⟨1516850, by rfl⟩ : syracuseStep 2022467 = 3033701) B3033701
theorem B2879653 : Blo 2021435 2879653 := bbase (se 4 (by rfl) ⟨269967, by rfl⟩ : syracuseStep 2879653 = 539935) (by norm_num)
theorem B3839537 : Blo 2021435 3839537 := bstep (se 2 (by rfl) ⟨1439826, by rfl⟩ : syracuseStep 3839537 = 2879653) B2879653
theorem B2559691 : Blo 2021435 2559691 := bstep (se 1 (by rfl) ⟨1919768, by rfl⟩ : syracuseStep 2559691 = 3839537) B3839537
theorem B3412921 : Blo 2021435 3412921 := bstep (se 2 (by rfl) ⟨1279845, by rfl⟩ : syracuseStep 3412921 = 2559691) B2559691
theorem B4550561 : Blo 2021435 4550561 := bstep (se 2 (by rfl) ⟨1706460, by rfl⟩ : syracuseStep 4550561 = 3412921) B3412921
theorem B3033707 : Blo 2021435 3033707 := bstep (se 1 (by rfl) ⟨2275280, by rfl⟩ : syracuseStep 3033707 = 4550561) B4550561
theorem B2022471 : Blo 2021435 2022471 := bstep (se 1 (by rfl) ⟨1516853, by rfl⟩ : syracuseStep 2022471 = 3033707) B3033707
theorem B2275285 : Blo 2021435 2275285 := bbase (se 7 (by rfl) ⟨26663, by rfl⟩ : syracuseStep 2275285 = 53327) (by norm_num)
theorem B3033713 : Blo 2021435 3033713 := bstep (se 2 (by rfl) ⟨1137642, by rfl⟩ : syracuseStep 3033713 = 2275285) B2275285
theorem B2022475 : Blo 2021435 2022475 := bstep (se 1 (by rfl) ⟨1516856, by rfl⟩ : syracuseStep 2022475 = 3033713) B3033713
theorem B2559701 : Blo 2021435 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B6825869 : Blo 2021435 6825869 := bstep (se 3 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 6825869 = 2559701) B2559701
theorem B4550579 : Blo 2021435 4550579 := bstep (se 1 (by rfl) ⟨3412934, by rfl⟩ : syracuseStep 4550579 = 6825869) B6825869
theorem B3033719 : Blo 2021435 3033719 := bstep (se 1 (by rfl) ⟨2275289, by rfl⟩ : syracuseStep 3033719 = 4550579) B4550579
theorem B2022479 : Blo 2021435 2022479 := bstep (se 1 (by rfl) ⟨1516859, by rfl⟩ : syracuseStep 2022479 = 3033719) B3033719
theorem B3033725 : Blo 2021435 3033725 := bbase (se 3 (by rfl) ⟨568823, by rfl⟩ : syracuseStep 3033725 = 1137647) (by norm_num)
theorem B2022483 : Blo 2021435 2022483 := bstep (se 1 (by rfl) ⟨1516862, by rfl⟩ : syracuseStep 2022483 = 3033725) B3033725
theorem B4550597 : Blo 2021435 4550597 := bbase (se 4 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 4550597 = 853237) (by norm_num)
theorem B3033731 : Blo 2021435 3033731 := bstep (se 1 (by rfl) ⟨2275298, by rfl⟩ : syracuseStep 3033731 = 4550597) B4550597
theorem B2022487 : Blo 2021435 2022487 := bstep (se 1 (by rfl) ⟨1516865, by rfl⟩ : syracuseStep 2022487 = 3033731) B3033731
theorem B8639045 : Blo 2021435 8639045 := bbase (se 4 (by rfl) ⟨809910, by rfl⟩ : syracuseStep 8639045 = 1619821) (by norm_num)
theorem B5759363 : Blo 2021435 5759363 := bstep (se 1 (by rfl) ⟨4319522, by rfl⟩ : syracuseStep 5759363 = 8639045) B8639045
theorem B3839575 : Blo 2021435 3839575 := bstep (se 1 (by rfl) ⟨2879681, by rfl⟩ : syracuseStep 3839575 = 5759363) B5759363
theorem B5119433 : Blo 2021435 5119433 := bstep (se 2 (by rfl) ⟨1919787, by rfl⟩ : syracuseStep 5119433 = 3839575) B3839575
theorem B3412955 : Blo 2021435 3412955 := bstep (se 1 (by rfl) ⟨2559716, by rfl⟩ : syracuseStep 3412955 = 5119433) B5119433
theorem B2275303 : Blo 2021435 2275303 := bstep (se 1 (by rfl) ⟨1706477, by rfl⟩ : syracuseStep 2275303 = 3412955) B3412955
theorem B3033737 : Blo 2021435 3033737 := bstep (se 2 (by rfl) ⟨1137651, by rfl⟩ : syracuseStep 3033737 = 2275303) B2275303
theorem B2022491 : Blo 2021435 2022491 := bstep (se 1 (by rfl) ⟨1516868, by rfl⟩ : syracuseStep 2022491 = 3033737) B3033737
theorem B10238885 : Blo 2021435 10238885 := bbase (se 4 (by rfl) ⟨959895, by rfl⟩ : syracuseStep 10238885 = 1919791) (by norm_num)
theorem B6825923 : Blo 2021435 6825923 := bstep (se 1 (by rfl) ⟨5119442, by rfl⟩ : syracuseStep 6825923 = 10238885) B10238885
theorem B4550615 : Blo 2021435 4550615 := bstep (se 1 (by rfl) ⟨3412961, by rfl⟩ : syracuseStep 4550615 = 6825923) B6825923
theorem B3033743 : Blo 2021435 3033743 := bstep (se 1 (by rfl) ⟨2275307, by rfl⟩ : syracuseStep 3033743 = 4550615) B4550615
theorem B2022495 : Blo 2021435 2022495 := bstep (se 1 (by rfl) ⟨1516871, by rfl⟩ : syracuseStep 2022495 = 3033743) B3033743
theorem B3033749 : Blo 2021435 3033749 := bbase (se 6 (by rfl) ⟨71103, by rfl⟩ : syracuseStep 3033749 = 142207) (by norm_num)
theorem B2022499 : Blo 2021435 2022499 := bstep (se 1 (by rfl) ⟨1516874, by rfl⟩ : syracuseStep 2022499 = 3033749) B3033749
theorem B7289237 : Blo 2021435 7289237 := bbase (se 6 (by rfl) ⟨170841, by rfl⟩ : syracuseStep 7289237 = 341683) (by norm_num)
theorem B19437965 : Blo 2021435 19437965 := bstep (se 3 (by rfl) ⟨3644618, by rfl⟩ : syracuseStep 19437965 = 7289237) B7289237
theorem B12958643 : Blo 2021435 12958643 := bstep (se 1 (by rfl) ⟨9718982, by rfl⟩ : syracuseStep 12958643 = 19437965) B19437965
theorem B8639095 : Blo 2021435 8639095 := bstep (se 1 (by rfl) ⟨6479321, by rfl⟩ : syracuseStep 8639095 = 12958643) B12958643
theorem B11518793 : Blo 2021435 11518793 := bstep (se 2 (by rfl) ⟨4319547, by rfl⟩ : syracuseStep 11518793 = 8639095) B8639095
theorem B7679195 : Blo 2021435 7679195 := bstep (se 1 (by rfl) ⟨5759396, by rfl⟩ : syracuseStep 7679195 = 11518793) B11518793
theorem B5119463 : Blo 2021435 5119463 := bstep (se 1 (by rfl) ⟨3839597, by rfl⟩ : syracuseStep 5119463 = 7679195) B7679195
theorem B3412975 : Blo 2021435 3412975 := bstep (se 1 (by rfl) ⟨2559731, by rfl⟩ : syracuseStep 3412975 = 5119463) B5119463
theorem B4550633 : Blo 2021435 4550633 := bstep (se 2 (by rfl) ⟨1706487, by rfl⟩ : syracuseStep 4550633 = 3412975) B3412975
theorem B3033755 : Blo 2021435 3033755 := bstep (se 1 (by rfl) ⟨2275316, by rfl⟩ : syracuseStep 3033755 = 4550633) B4550633
theorem B2022503 : Blo 2021435 2022503 := bstep (se 1 (by rfl) ⟨1516877, by rfl⟩ : syracuseStep 2022503 = 3033755) B3033755
theorem B2275321 : Blo 2021435 2275321 := bbase (se 2 (by rfl) ⟨853245, by rfl⟩ : syracuseStep 2275321 = 1706491) (by norm_num)
theorem B3033761 : Blo 2021435 3033761 := bstep (se 2 (by rfl) ⟨1137660, by rfl⟩ : syracuseStep 3033761 = 2275321) B2275321
theorem B2022507 : Blo 2021435 2022507 := bstep (se 1 (by rfl) ⟨1516880, by rfl⟩ : syracuseStep 2022507 = 3033761) B3033761
theorem B4100213 : Blo 2021435 4100213 := bbase (se 5 (by rfl) ⟨192197, by rfl⟩ : syracuseStep 4100213 = 384395) (by norm_num)
theorem B2733475 : Blo 2021435 2733475 := bstep (se 1 (by rfl) ⟨2050106, by rfl⟩ : syracuseStep 2733475 = 4100213) B4100213
theorem B3644633 : Blo 2021435 3644633 := bstep (se 2 (by rfl) ⟨1366737, by rfl⟩ : syracuseStep 3644633 = 2733475) B2733475
theorem B9719021 : Blo 2021435 9719021 := bstep (se 3 (by rfl) ⟨1822316, by rfl⟩ : syracuseStep 9719021 = 3644633) B3644633
theorem B6479347 : Blo 2021435 6479347 := bstep (se 1 (by rfl) ⟨4859510, by rfl⟩ : syracuseStep 6479347 = 9719021) B9719021
theorem B8639129 : Blo 2021435 8639129 := bstep (se 2 (by rfl) ⟨3239673, by rfl⟩ : syracuseStep 8639129 = 6479347) B6479347
theorem B5759419 : Blo 2021435 5759419 := bstep (se 1 (by rfl) ⟨4319564, by rfl⟩ : syracuseStep 5759419 = 8639129) B8639129
theorem B7679225 : Blo 2021435 7679225 := bstep (se 2 (by rfl) ⟨2879709, by rfl⟩ : syracuseStep 7679225 = 5759419) B5759419
theorem B5119483 : Blo 2021435 5119483 := bstep (se 1 (by rfl) ⟨3839612, by rfl⟩ : syracuseStep 5119483 = 7679225) B7679225
theorem B6825977 : Blo 2021435 6825977 := bstep (se 2 (by rfl) ⟨2559741, by rfl⟩ : syracuseStep 6825977 = 5119483) B5119483
theorem B4550651 : Blo 2021435 4550651 := bstep (se 1 (by rfl) ⟨3412988, by rfl⟩ : syracuseStep 4550651 = 6825977) B6825977
theorem B3033767 : Blo 2021435 3033767 := bstep (se 1 (by rfl) ⟨2275325, by rfl⟩ : syracuseStep 3033767 = 4550651) B4550651
theorem B2022511 : Blo 2021435 2022511 := bstep (se 1 (by rfl) ⟨1516883, by rfl⟩ : syracuseStep 2022511 = 3033767) B3033767
theorem B3033773 : Blo 2021435 3033773 := bbase (se 3 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 3033773 = 1137665) (by norm_num)
theorem B2022515 : Blo 2021435 2022515 := bstep (se 1 (by rfl) ⟨1516886, by rfl⟩ : syracuseStep 2022515 = 3033773) B3033773
theorem B4550669 : Blo 2021435 4550669 := bbase (se 3 (by rfl) ⟨853250, by rfl⟩ : syracuseStep 4550669 = 1706501) (by norm_num)
theorem B3033779 : Blo 2021435 3033779 := bstep (se 1 (by rfl) ⟨2275334, by rfl⟩ : syracuseStep 3033779 = 4550669) B4550669
theorem B2022519 : Blo 2021435 2022519 := bstep (se 1 (by rfl) ⟨1516889, by rfl⟩ : syracuseStep 2022519 = 3033779) B3033779
theorem B2559757 : Blo 2021435 2559757 := bbase (se 3 (by rfl) ⟨479954, by rfl⟩ : syracuseStep 2559757 = 959909) (by norm_num)
theorem B3413009 : Blo 2021435 3413009 := bstep (se 2 (by rfl) ⟨1279878, by rfl⟩ : syracuseStep 3413009 = 2559757) B2559757
theorem B2275339 : Blo 2021435 2275339 := bstep (se 1 (by rfl) ⟨1706504, by rfl⟩ : syracuseStep 2275339 = 3413009) B3413009
theorem B3033785 : Blo 2021435 3033785 := bstep (se 2 (by rfl) ⟨1137669, by rfl⟩ : syracuseStep 3033785 = 2275339) B2275339
theorem B2022523 : Blo 2021435 2022523 := bstep (se 1 (by rfl) ⟨1516892, by rfl⟩ : syracuseStep 2022523 = 3033785) B3033785
theorem B14578645 : Blo 2021435 14578645 := bbase (se 7 (by rfl) ⟨170843, by rfl⟩ : syracuseStep 14578645 = 341687) (by norm_num)
theorem B19438193 : Blo 2021435 19438193 := bstep (se 2 (by rfl) ⟨7289322, by rfl⟩ : syracuseStep 19438193 = 14578645) B14578645
theorem B12958795 : Blo 2021435 12958795 := bstep (se 1 (by rfl) ⟨9719096, by rfl⟩ : syracuseStep 12958795 = 19438193) B19438193
theorem B17278393 : Blo 2021435 17278393 := bstep (se 2 (by rfl) ⟨6479397, by rfl⟩ : syracuseStep 17278393 = 12958795) B12958795
theorem B23037857 : Blo 2021435 23037857 := bstep (se 2 (by rfl) ⟨8639196, by rfl⟩ : syracuseStep 23037857 = 17278393) B17278393
theorem B15358571 : Blo 2021435 15358571 := bstep (se 1 (by rfl) ⟨11518928, by rfl⟩ : syracuseStep 15358571 = 23037857) B23037857
theorem B10239047 : Blo 2021435 10239047 := bstep (se 1 (by rfl) ⟨7679285, by rfl⟩ : syracuseStep 10239047 = 15358571) B15358571
theorem B6826031 : Blo 2021435 6826031 := bstep (se 1 (by rfl) ⟨5119523, by rfl⟩ : syracuseStep 6826031 = 10239047) B10239047
theorem B4550687 : Blo 2021435 4550687 := bstep (se 1 (by rfl) ⟨3413015, by rfl⟩ : syracuseStep 4550687 = 6826031) B6826031
theorem B3033791 : Blo 2021435 3033791 := bstep (se 1 (by rfl) ⟨2275343, by rfl⟩ : syracuseStep 3033791 = 4550687) B4550687
theorem B2022527 : Blo 2021435 2022527 := bstep (se 1 (by rfl) ⟨1516895, by rfl⟩ : syracuseStep 2022527 = 3033791) B3033791
theorem B3033797 : Blo 2021435 3033797 := bbase (se 4 (by rfl) ⟨284418, by rfl⟩ : syracuseStep 3033797 = 568837) (by norm_num)
theorem B2022531 : Blo 2021435 2022531 := bstep (se 1 (by rfl) ⟨1516898, by rfl⟩ : syracuseStep 2022531 = 3033797) B3033797
theorem B3413029 : Blo 2021435 3413029 := bbase (se 4 (by rfl) ⟨319971, by rfl⟩ : syracuseStep 3413029 = 639943) (by norm_num)
theorem B4550705 : Blo 2021435 4550705 := bstep (se 2 (by rfl) ⟨1706514, by rfl⟩ : syracuseStep 4550705 = 3413029) B3413029
theorem B3033803 : Blo 2021435 3033803 := bstep (se 1 (by rfl) ⟨2275352, by rfl⟩ : syracuseStep 3033803 = 4550705) B4550705
theorem B2022535 : Blo 2021435 2022535 := bstep (se 1 (by rfl) ⟨1516901, by rfl⟩ : syracuseStep 2022535 = 3033803) B3033803
theorem B2275357 : Blo 2021435 2275357 := bbase (se 3 (by rfl) ⟨426629, by rfl⟩ : syracuseStep 2275357 = 853259) (by norm_num)
theorem B3033809 : Blo 2021435 3033809 := bstep (se 2 (by rfl) ⟨1137678, by rfl⟩ : syracuseStep 3033809 = 2275357) B2275357
theorem B2022539 : Blo 2021435 2022539 := bstep (se 1 (by rfl) ⟨1516904, by rfl⟩ : syracuseStep 2022539 = 3033809) B3033809
theorem B6826085 : Blo 2021435 6826085 := bbase (se 4 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 6826085 = 1279891) (by norm_num)
theorem B4550723 : Blo 2021435 4550723 := bstep (se 1 (by rfl) ⟨3413042, by rfl⟩ : syracuseStep 4550723 = 6826085) B6826085
theorem B3033815 : Blo 2021435 3033815 := bstep (se 1 (by rfl) ⟨2275361, by rfl⟩ : syracuseStep 3033815 = 4550723) B4550723
theorem B2022543 : Blo 2021435 2022543 := bstep (se 1 (by rfl) ⟨1516907, by rfl⟩ : syracuseStep 2022543 = 3033815) B3033815
theorem B3033821 : Blo 2021435 3033821 := bbase (se 3 (by rfl) ⟨568841, by rfl⟩ : syracuseStep 3033821 = 1137683) (by norm_num)
theorem B2022547 : Blo 2021435 2022547 := bstep (se 1 (by rfl) ⟨1516910, by rfl⟩ : syracuseStep 2022547 = 3033821) B3033821
theorem B4550741 : Blo 2021435 4550741 := bbase (se 8 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 4550741 = 53329) (by norm_num)
theorem B3033827 : Blo 2021435 3033827 := bstep (se 1 (by rfl) ⟨2275370, by rfl⟩ : syracuseStep 3033827 = 4550741) B4550741
theorem B2022551 : Blo 2021435 2022551 := bstep (se 1 (by rfl) ⟨1516913, by rfl⟩ : syracuseStep 2022551 = 3033827) B3033827
theorem B9351557 : Blo 2021435 9351557 := bbase (se 4 (by rfl) ⟨876708, by rfl⟩ : syracuseStep 9351557 = 1753417) (by norm_num)
theorem B6234371 : Blo 2021435 6234371 := bstep (se 1 (by rfl) ⟨4675778, by rfl⟩ : syracuseStep 6234371 = 9351557) B9351557
theorem B4156247 : Blo 2021435 4156247 := bstep (se 1 (by rfl) ⟨3117185, by rfl⟩ : syracuseStep 4156247 = 6234371) B6234371
theorem B2770831 : Blo 2021435 2770831 := bstep (se 1 (by rfl) ⟨2078123, by rfl⟩ : syracuseStep 2770831 = 4156247) B4156247
theorem B14777765 : Blo 2021435 14777765 := bstep (se 4 (by rfl) ⟨1385415, by rfl⟩ : syracuseStep 14777765 = 2770831) B2770831
theorem B9851843 : Blo 2021435 9851843 := bstep (se 1 (by rfl) ⟨7388882, by rfl⟩ : syracuseStep 9851843 = 14777765) B14777765
theorem B6567895 : Blo 2021435 6567895 := bstep (se 1 (by rfl) ⟨4925921, by rfl⟩ : syracuseStep 6567895 = 9851843) B9851843
theorem B8757193 : Blo 2021435 8757193 := bstep (se 2 (by rfl) ⟨3283947, by rfl⟩ : syracuseStep 8757193 = 6567895) B6567895
theorem B11676257 : Blo 2021435 11676257 := bstep (se 2 (by rfl) ⟨4378596, by rfl⟩ : syracuseStep 11676257 = 8757193) B8757193
theorem B7784171 : Blo 2021435 7784171 := bstep (se 1 (by rfl) ⟨5838128, by rfl⟩ : syracuseStep 7784171 = 11676257) B11676257
theorem B5189447 : Blo 2021435 5189447 := bstep (se 1 (by rfl) ⟨3892085, by rfl⟩ : syracuseStep 5189447 = 7784171) B7784171
theorem B13838525 : Blo 2021435 13838525 := bstep (se 3 (by rfl) ⟨2594723, by rfl⟩ : syracuseStep 13838525 = 5189447) B5189447
theorem B9225683 : Blo 2021435 9225683 := bstep (se 1 (by rfl) ⟨6919262, by rfl⟩ : syracuseStep 9225683 = 13838525) B13838525
theorem B6150455 : Blo 2021435 6150455 := bstep (se 1 (by rfl) ⟨4612841, by rfl⟩ : syracuseStep 6150455 = 9225683) B9225683
theorem B4100303 : Blo 2021435 4100303 := bstep (se 1 (by rfl) ⟨3075227, by rfl⟩ : syracuseStep 4100303 = 6150455) B6150455
theorem B2733535 : Blo 2021435 2733535 := bstep (se 1 (by rfl) ⟨2050151, by rfl⟩ : syracuseStep 2733535 = 4100303) B4100303
theorem B3644713 : Blo 2021435 3644713 := bstep (se 2 (by rfl) ⟨1366767, by rfl⟩ : syracuseStep 3644713 = 2733535) B2733535
theorem B4859617 : Blo 2021435 4859617 := bstep (se 2 (by rfl) ⟨1822356, by rfl⟩ : syracuseStep 4859617 = 3644713) B3644713
theorem B6479489 : Blo 2021435 6479489 := bstep (se 2 (by rfl) ⟨2429808, by rfl⟩ : syracuseStep 6479489 = 4859617) B4859617
theorem B4319659 : Blo 2021435 4319659 := bstep (se 1 (by rfl) ⟨3239744, by rfl⟩ : syracuseStep 4319659 = 6479489) B6479489
theorem B5759545 : Blo 2021435 5759545 := bstep (se 2 (by rfl) ⟨2159829, by rfl⟩ : syracuseStep 5759545 = 4319659) B4319659
theorem B7679393 : Blo 2021435 7679393 := bstep (se 2 (by rfl) ⟨2879772, by rfl⟩ : syracuseStep 7679393 = 5759545) B5759545
theorem B5119595 : Blo 2021435 5119595 := bstep (se 1 (by rfl) ⟨3839696, by rfl⟩ : syracuseStep 5119595 = 7679393) B7679393
theorem B3413063 : Blo 2021435 3413063 := bstep (se 1 (by rfl) ⟨2559797, by rfl⟩ : syracuseStep 3413063 = 5119595) B5119595
theorem B2275375 : Blo 2021435 2275375 := bstep (se 1 (by rfl) ⟨1706531, by rfl⟩ : syracuseStep 2275375 = 3413063) B3413063
theorem B3033833 : Blo 2021435 3033833 := bstep (se 2 (by rfl) ⟨1137687, by rfl⟩ : syracuseStep 3033833 = 2275375) B2275375
theorem B2022555 : Blo 2021435 2022555 := bstep (se 1 (by rfl) ⟨1516916, by rfl⟩ : syracuseStep 2022555 = 3033833) B3033833
theorem B7890389 : Blo 2021435 7890389 := bbase (se 7 (by rfl) ⟨92465, by rfl⟩ : syracuseStep 7890389 = 184931) (by norm_num)
theorem B5260259 : Blo 2021435 5260259 := bstep (se 1 (by rfl) ⟨3945194, by rfl⟩ : syracuseStep 5260259 = 7890389) B7890389
theorem B14027357 : Blo 2021435 14027357 := bstep (se 3 (by rfl) ⟨2630129, by rfl⟩ : syracuseStep 14027357 = 5260259) B5260259
theorem B9351571 : Blo 2021435 9351571 := bstep (se 1 (by rfl) ⟨7013678, by rfl⟩ : syracuseStep 9351571 = 14027357) B14027357
theorem B12468761 : Blo 2021435 12468761 := bstep (se 2 (by rfl) ⟨4675785, by rfl⟩ : syracuseStep 12468761 = 9351571) B9351571
theorem B8312507 : Blo 2021435 8312507 := bstep (se 1 (by rfl) ⟨6234380, by rfl⟩ : syracuseStep 8312507 = 12468761) B12468761
theorem B5541671 : Blo 2021435 5541671 := bstep (se 1 (by rfl) ⟨4156253, by rfl⟩ : syracuseStep 5541671 = 8312507) B8312507
theorem B3694447 : Blo 2021435 3694447 := bstep (se 1 (by rfl) ⟨2770835, by rfl⟩ : syracuseStep 3694447 = 5541671) B5541671
theorem B4925929 : Blo 2021435 4925929 := bstep (se 2 (by rfl) ⟨1847223, by rfl⟩ : syracuseStep 4925929 = 3694447) B3694447
theorem B6567905 : Blo 2021435 6567905 := bstep (se 2 (by rfl) ⟨2462964, by rfl⟩ : syracuseStep 6567905 = 4925929) B4925929
theorem B17514413 : Blo 2021435 17514413 := bstep (se 3 (by rfl) ⟨3283952, by rfl⟩ : syracuseStep 17514413 = 6567905) B6567905
theorem B11676275 : Blo 2021435 11676275 := bstep (se 1 (by rfl) ⟨8757206, by rfl⟩ : syracuseStep 11676275 = 17514413) B17514413
theorem B7784183 : Blo 2021435 7784183 := bstep (se 1 (by rfl) ⟨5838137, by rfl⟩ : syracuseStep 7784183 = 11676275) B11676275
theorem B5189455 : Blo 2021435 5189455 := bstep (se 1 (by rfl) ⟨3892091, by rfl⟩ : syracuseStep 5189455 = 7784183) B7784183
theorem B6919273 : Blo 2021435 6919273 := bstep (se 2 (by rfl) ⟨2594727, by rfl⟩ : syracuseStep 6919273 = 5189455) B5189455
theorem B9225697 : Blo 2021435 9225697 := bstep (se 2 (by rfl) ⟨3459636, by rfl⟩ : syracuseStep 9225697 = 6919273) B6919273
theorem B12300929 : Blo 2021435 12300929 := bstep (se 2 (by rfl) ⟨4612848, by rfl⟩ : syracuseStep 12300929 = 9225697) B9225697
theorem B8200619 : Blo 2021435 8200619 := bstep (se 1 (by rfl) ⟨6150464, by rfl⟩ : syracuseStep 8200619 = 12300929) B12300929
theorem B5467079 : Blo 2021435 5467079 := bstep (se 1 (by rfl) ⟨4100309, by rfl⟩ : syracuseStep 5467079 = 8200619) B8200619
theorem B3644719 : Blo 2021435 3644719 := bstep (se 1 (by rfl) ⟨2733539, by rfl⟩ : syracuseStep 3644719 = 5467079) B5467079
theorem B19438501 : Blo 2021435 19438501 := bstep (se 4 (by rfl) ⟨1822359, by rfl⟩ : syracuseStep 19438501 = 3644719) B3644719
theorem B25918001 : Blo 2021435 25918001 := bstep (se 2 (by rfl) ⟨9719250, by rfl⟩ : syracuseStep 25918001 = 19438501) B19438501
theorem B17278667 : Blo 2021435 17278667 := bstep (se 1 (by rfl) ⟨12959000, by rfl⟩ : syracuseStep 17278667 = 25918001) B25918001
theorem B11519111 : Blo 2021435 11519111 := bstep (se 1 (by rfl) ⟨8639333, by rfl⟩ : syracuseStep 11519111 = 17278667) B17278667
theorem B7679407 : Blo 2021435 7679407 := bstep (se 1 (by rfl) ⟨5759555, by rfl⟩ : syracuseStep 7679407 = 11519111) B11519111
theorem B10239209 : Blo 2021435 10239209 := bstep (se 2 (by rfl) ⟨3839703, by rfl⟩ : syracuseStep 10239209 = 7679407) B7679407
theorem B6826139 : Blo 2021435 6826139 := bstep (se 1 (by rfl) ⟨5119604, by rfl⟩ : syracuseStep 6826139 = 10239209) B10239209
theorem B4550759 : Blo 2021435 4550759 := bstep (se 1 (by rfl) ⟨3413069, by rfl⟩ : syracuseStep 4550759 = 6826139) B6826139
theorem B3033839 : Blo 2021435 3033839 := bstep (se 1 (by rfl) ⟨2275379, by rfl⟩ : syracuseStep 3033839 = 4550759) B4550759
theorem B2022559 : Blo 2021435 2022559 := bstep (se 1 (by rfl) ⟨1516919, by rfl⟩ : syracuseStep 2022559 = 3033839) B3033839
theorem B3033845 : Blo 2021435 3033845 := bbase (se 5 (by rfl) ⟨142211, by rfl⟩ : syracuseStep 3033845 = 284423) (by norm_num)
theorem B2022563 : Blo 2021435 2022563 := bstep (se 1 (by rfl) ⟨1516922, by rfl⟩ : syracuseStep 2022563 = 3033845) B3033845
theorem B6919301 : Blo 2021435 6919301 := bbase (se 4 (by rfl) ⟨648684, by rfl⟩ : syracuseStep 6919301 = 1297369) (by norm_num)
theorem B18451469 : Blo 2021435 18451469 := bstep (se 3 (by rfl) ⟨3459650, by rfl⟩ : syracuseStep 18451469 = 6919301) B6919301
theorem B12300979 : Blo 2021435 12300979 := bstep (se 1 (by rfl) ⟨9225734, by rfl⟩ : syracuseStep 12300979 = 18451469) B18451469
theorem B16401305 : Blo 2021435 16401305 := bstep (se 2 (by rfl) ⟨6150489, by rfl⟩ : syracuseStep 16401305 = 12300979) B12300979
theorem B10934203 : Blo 2021435 10934203 := bstep (se 1 (by rfl) ⟨8200652, by rfl⟩ : syracuseStep 10934203 = 16401305) B16401305
theorem B14578937 : Blo 2021435 14578937 := bstep (se 2 (by rfl) ⟨5467101, by rfl⟩ : syracuseStep 14578937 = 10934203) B10934203
theorem B9719291 : Blo 2021435 9719291 := bstep (se 1 (by rfl) ⟨7289468, by rfl⟩ : syracuseStep 9719291 = 14578937) B14578937
theorem B6479527 : Blo 2021435 6479527 := bstep (se 1 (by rfl) ⟨4859645, by rfl⟩ : syracuseStep 6479527 = 9719291) B9719291
theorem B8639369 : Blo 2021435 8639369 := bstep (se 2 (by rfl) ⟨3239763, by rfl⟩ : syracuseStep 8639369 = 6479527) B6479527
theorem B5759579 : Blo 2021435 5759579 := bstep (se 1 (by rfl) ⟨4319684, by rfl⟩ : syracuseStep 5759579 = 8639369) B8639369
theorem B3839719 : Blo 2021435 3839719 := bstep (se 1 (by rfl) ⟨2879789, by rfl⟩ : syracuseStep 3839719 = 5759579) B5759579
theorem B5119625 : Blo 2021435 5119625 := bstep (se 2 (by rfl) ⟨1919859, by rfl⟩ : syracuseStep 5119625 = 3839719) B3839719
theorem B3413083 : Blo 2021435 3413083 := bstep (se 1 (by rfl) ⟨2559812, by rfl⟩ : syracuseStep 3413083 = 5119625) B5119625
theorem B4550777 : Blo 2021435 4550777 := bstep (se 2 (by rfl) ⟨1706541, by rfl⟩ : syracuseStep 4550777 = 3413083) B3413083
theorem B3033851 : Blo 2021435 3033851 := bstep (se 1 (by rfl) ⟨2275388, by rfl⟩ : syracuseStep 3033851 = 4550777) B4550777
theorem B2022567 : Blo 2021435 2022567 := bstep (se 1 (by rfl) ⟨1516925, by rfl⟩ : syracuseStep 2022567 = 3033851) B3033851
theorem B2275393 : Blo 2021435 2275393 := bbase (se 2 (by rfl) ⟨853272, by rfl⟩ : syracuseStep 2275393 = 1706545) (by norm_num)
theorem B3033857 : Blo 2021435 3033857 := bstep (se 2 (by rfl) ⟨1137696, by rfl⟩ : syracuseStep 3033857 = 2275393) B2275393
theorem B2022571 : Blo 2021435 2022571 := bstep (se 1 (by rfl) ⟨1516928, by rfl⟩ : syracuseStep 2022571 = 3033857) B3033857
theorem B5119645 : Blo 2021435 5119645 := bbase (se 3 (by rfl) ⟨959933, by rfl⟩ : syracuseStep 5119645 = 1919867) (by norm_num)
theorem B6826193 : Blo 2021435 6826193 := bstep (se 2 (by rfl) ⟨2559822, by rfl⟩ : syracuseStep 6826193 = 5119645) B5119645
theorem B4550795 : Blo 2021435 4550795 := bstep (se 1 (by rfl) ⟨3413096, by rfl⟩ : syracuseStep 4550795 = 6826193) B6826193
theorem B3033863 : Blo 2021435 3033863 := bstep (se 1 (by rfl) ⟨2275397, by rfl⟩ : syracuseStep 3033863 = 4550795) B4550795
theorem B2022575 : Blo 2021435 2022575 := bstep (se 1 (by rfl) ⟨1516931, by rfl⟩ : syracuseStep 2022575 = 3033863) B3033863
theorem B3033869 : Blo 2021435 3033869 := bbase (se 3 (by rfl) ⟨568850, by rfl⟩ : syracuseStep 3033869 = 1137701) (by norm_num)
theorem B2022579 : Blo 2021435 2022579 := bstep (se 1 (by rfl) ⟨1516934, by rfl⟩ : syracuseStep 2022579 = 3033869) B3033869
theorem B4550813 : Blo 2021435 4550813 := bbase (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) (by norm_num)
theorem B3033875 : Blo 2021435 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B2022583 : Blo 2021435 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B3413117 : Blo 2021435 3413117 := bbase (se 3 (by rfl) ⟨639959, by rfl⟩ : syracuseStep 3413117 = 1279919) (by norm_num)
theorem B2275411 : Blo 2021435 2275411 := bstep (se 1 (by rfl) ⟨1706558, by rfl⟩ : syracuseStep 2275411 = 3413117) B3413117
theorem B3033881 : Blo 2021435 3033881 := bstep (se 2 (by rfl) ⟨1137705, by rfl⟩ : syracuseStep 3033881 = 2275411) B2275411
theorem B2022587 : Blo 2021435 2022587 := bstep (se 1 (by rfl) ⟨1516940, by rfl⟩ : syracuseStep 2022587 = 3033881) B3033881
theorem B9225845 : Blo 2021435 9225845 := bbase (se 5 (by rfl) ⟨432461, by rfl⟩ : syracuseStep 9225845 = 864923) (by norm_num)
theorem B6150563 : Blo 2021435 6150563 := bstep (se 1 (by rfl) ⟨4612922, by rfl⟩ : syracuseStep 6150563 = 9225845) B9225845
theorem B4100375 : Blo 2021435 4100375 := bstep (se 1 (by rfl) ⟨3075281, by rfl⟩ : syracuseStep 4100375 = 6150563) B6150563
theorem B2733583 : Blo 2021435 2733583 := bstep (se 1 (by rfl) ⟨2050187, by rfl⟩ : syracuseStep 2733583 = 4100375) B4100375
theorem B3644777 : Blo 2021435 3644777 := bstep (se 2 (by rfl) ⟨1366791, by rfl⟩ : syracuseStep 3644777 = 2733583) B2733583
theorem B9719405 : Blo 2021435 9719405 := bstep (se 3 (by rfl) ⟨1822388, by rfl⟩ : syracuseStep 9719405 = 3644777) B3644777
theorem B6479603 : Blo 2021435 6479603 := bstep (se 1 (by rfl) ⟨4859702, by rfl⟩ : syracuseStep 6479603 = 9719405) B9719405
theorem B4319735 : Blo 2021435 4319735 := bstep (se 1 (by rfl) ⟨3239801, by rfl⟩ : syracuseStep 4319735 = 6479603) B6479603
theorem B11519293 : Blo 2021435 11519293 := bstep (se 3 (by rfl) ⟨2159867, by rfl⟩ : syracuseStep 11519293 = 4319735) B4319735
theorem B15359057 : Blo 2021435 15359057 := bstep (se 2 (by rfl) ⟨5759646, by rfl⟩ : syracuseStep 15359057 = 11519293) B11519293
theorem B10239371 : Blo 2021435 10239371 := bstep (se 1 (by rfl) ⟨7679528, by rfl⟩ : syracuseStep 10239371 = 15359057) B15359057
theorem B6826247 : Blo 2021435 6826247 := bstep (se 1 (by rfl) ⟨5119685, by rfl⟩ : syracuseStep 6826247 = 10239371) B10239371
theorem B4550831 : Blo 2021435 4550831 := bstep (se 1 (by rfl) ⟨3413123, by rfl⟩ : syracuseStep 4550831 = 6826247) B6826247
theorem B3033887 : Blo 2021435 3033887 := bstep (se 1 (by rfl) ⟨2275415, by rfl⟩ : syracuseStep 3033887 = 4550831) B4550831
theorem B2022591 : Blo 2021435 2022591 := bstep (se 1 (by rfl) ⟨1516943, by rfl⟩ : syracuseStep 2022591 = 3033887) B3033887
theorem B3033893 : Blo 2021435 3033893 := bbase (se 4 (by rfl) ⟨284427, by rfl⟩ : syracuseStep 3033893 = 568855) (by norm_num)
theorem B2022595 : Blo 2021435 2022595 := bstep (se 1 (by rfl) ⟨1516946, by rfl⟩ : syracuseStep 2022595 = 3033893) B3033893
theorem B2559853 : Blo 2021435 2559853 := bbase (se 3 (by rfl) ⟨479972, by rfl⟩ : syracuseStep 2559853 = 959945) (by norm_num)
theorem B3413137 : Blo 2021435 3413137 := bstep (se 2 (by rfl) ⟨1279926, by rfl⟩ : syracuseStep 3413137 = 2559853) B2559853
theorem B4550849 : Blo 2021435 4550849 := bstep (se 2 (by rfl) ⟨1706568, by rfl⟩ : syracuseStep 4550849 = 3413137) B3413137
theorem B3033899 : Blo 2021435 3033899 := bstep (se 1 (by rfl) ⟨2275424, by rfl⟩ : syracuseStep 3033899 = 4550849) B4550849
theorem B2022599 : Blo 2021435 2022599 := bstep (se 1 (by rfl) ⟨1516949, by rfl⟩ : syracuseStep 2022599 = 3033899) B3033899
theorem B2275429 : Blo 2021435 2275429 := bbase (se 4 (by rfl) ⟨213321, by rfl⟩ : syracuseStep 2275429 = 426643) (by norm_num)
theorem B3033905 : Blo 2021435 3033905 := bstep (se 2 (by rfl) ⟨1137714, by rfl⟩ : syracuseStep 3033905 = 2275429) B2275429
theorem B2022603 : Blo 2021435 2022603 := bstep (se 1 (by rfl) ⟨1516952, by rfl⟩ : syracuseStep 2022603 = 3033905) B3033905
theorem B2159885 : Blo 2021435 2159885 := bbase (se 3 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 2159885 = 809957) (by norm_num)
theorem B5759693 : Blo 2021435 5759693 := bstep (se 3 (by rfl) ⟨1079942, by rfl⟩ : syracuseStep 5759693 = 2159885) B2159885
theorem B3839795 : Blo 2021435 3839795 := bstep (se 1 (by rfl) ⟨2879846, by rfl⟩ : syracuseStep 3839795 = 5759693) B5759693
theorem B2559863 : Blo 2021435 2559863 := bstep (se 1 (by rfl) ⟨1919897, by rfl⟩ : syracuseStep 2559863 = 3839795) B3839795
theorem B6826301 : Blo 2021435 6826301 := bstep (se 3 (by rfl) ⟨1279931, by rfl⟩ : syracuseStep 6826301 = 2559863) B2559863
theorem B4550867 : Blo 2021435 4550867 := bstep (se 1 (by rfl) ⟨3413150, by rfl⟩ : syracuseStep 4550867 = 6826301) B6826301
theorem B3033911 : Blo 2021435 3033911 := bstep (se 1 (by rfl) ⟨2275433, by rfl⟩ : syracuseStep 3033911 = 4550867) B4550867
theorem B2022607 : Blo 2021435 2022607 := bstep (se 1 (by rfl) ⟨1516955, by rfl⟩ : syracuseStep 2022607 = 3033911) B3033911
theorem B3033917 : Blo 2021435 3033917 := bbase (se 3 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 3033917 = 1137719) (by norm_num)
theorem B2022611 : Blo 2021435 2022611 := bstep (se 1 (by rfl) ⟨1516958, by rfl⟩ : syracuseStep 2022611 = 3033917) B3033917
theorem B4550885 : Blo 2021435 4550885 := bbase (se 4 (by rfl) ⟨426645, by rfl⟩ : syracuseStep 4550885 = 853291) (by norm_num)
theorem B3033923 : Blo 2021435 3033923 := bstep (se 1 (by rfl) ⟨2275442, by rfl⟩ : syracuseStep 3033923 = 4550885) B4550885
theorem B2022615 : Blo 2021435 2022615 := bstep (se 1 (by rfl) ⟨1516961, by rfl⟩ : syracuseStep 2022615 = 3033923) B3033923
theorem B5119757 : Blo 2021435 5119757 := bbase (se 3 (by rfl) ⟨959954, by rfl⟩ : syracuseStep 5119757 = 1919909) (by norm_num)
theorem B3413171 : Blo 2021435 3413171 := bstep (se 1 (by rfl) ⟨2559878, by rfl⟩ : syracuseStep 3413171 = 5119757) B5119757
theorem B2275447 : Blo 2021435 2275447 := bstep (se 1 (by rfl) ⟨1706585, by rfl⟩ : syracuseStep 2275447 = 3413171) B3413171
theorem B3033929 : Blo 2021435 3033929 := bstep (se 2 (by rfl) ⟨1137723, by rfl⟩ : syracuseStep 3033929 = 2275447) B2275447
theorem B2022619 : Blo 2021435 2022619 := bstep (se 1 (by rfl) ⟨1516964, by rfl⟩ : syracuseStep 2022619 = 3033929) B3033929
theorem B2879869 : Blo 2021435 2879869 := bbase (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) (by norm_num)
theorem B3839825 : Blo 2021435 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B10239533 : Blo 2021435 10239533 := bstep (se 3 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 10239533 = 3839825) B3839825
theorem B6826355 : Blo 2021435 6826355 := bstep (se 1 (by rfl) ⟨5119766, by rfl⟩ : syracuseStep 6826355 = 10239533) B10239533
theorem B4550903 : Blo 2021435 4550903 := bstep (se 1 (by rfl) ⟨3413177, by rfl⟩ : syracuseStep 4550903 = 6826355) B6826355
theorem B3033935 : Blo 2021435 3033935 := bstep (se 1 (by rfl) ⟨2275451, by rfl⟩ : syracuseStep 3033935 = 4550903) B4550903
theorem B2022623 : Blo 2021435 2022623 := bstep (se 1 (by rfl) ⟨1516967, by rfl⟩ : syracuseStep 2022623 = 3033935) B3033935
theorem B3033941 : Blo 2021435 3033941 := bbase (se 9 (by rfl) ⟨8888, by rfl⟩ : syracuseStep 3033941 = 17777) (by norm_num)
theorem B2022627 : Blo 2021435 2022627 := bstep (se 1 (by rfl) ⟨1516970, by rfl⟩ : syracuseStep 2022627 = 3033941) B3033941
theorem B4319821 : Blo 2021435 4319821 := bbase (se 3 (by rfl) ⟨809966, by rfl⟩ : syracuseStep 4319821 = 1619933) (by norm_num)
theorem B5759761 : Blo 2021435 5759761 := bstep (se 2 (by rfl) ⟨2159910, by rfl⟩ : syracuseStep 5759761 = 4319821) B4319821
theorem B7679681 : Blo 2021435 7679681 := bstep (se 2 (by rfl) ⟨2879880, by rfl⟩ : syracuseStep 7679681 = 5759761) B5759761
theorem B5119787 : Blo 2021435 5119787 := bstep (se 1 (by rfl) ⟨3839840, by rfl⟩ : syracuseStep 5119787 = 7679681) B7679681
theorem B3413191 : Blo 2021435 3413191 := bstep (se 1 (by rfl) ⟨2559893, by rfl⟩ : syracuseStep 3413191 = 5119787) B5119787
theorem B4550921 : Blo 2021435 4550921 := bstep (se 2 (by rfl) ⟨1706595, by rfl⟩ : syracuseStep 4550921 = 3413191) B3413191
theorem B3033947 : Blo 2021435 3033947 := bstep (se 1 (by rfl) ⟨2275460, by rfl⟩ : syracuseStep 3033947 = 4550921) B4550921
theorem B2022631 : Blo 2021435 2022631 := bstep (se 1 (by rfl) ⟨1516973, by rfl⟩ : syracuseStep 2022631 = 3033947) B3033947
theorem B2275465 : Blo 2021435 2275465 := bbase (se 2 (by rfl) ⟨853299, by rfl⟩ : syracuseStep 2275465 = 1706599) (by norm_num)
theorem B3033953 : Blo 2021435 3033953 := bstep (se 2 (by rfl) ⟨1137732, by rfl⟩ : syracuseStep 3033953 = 2275465) B2275465
theorem B2022635 : Blo 2021435 2022635 := bstep (se 1 (by rfl) ⟨1516976, by rfl⟩ : syracuseStep 2022635 = 3033953) B3033953
theorem B2501885 : Blo 2021435 2501885 := bbase (se 3 (by rfl) ⟨469103, by rfl⟩ : syracuseStep 2501885 = 938207) (by norm_num)
theorem B6671693 : Blo 2021435 6671693 := bstep (se 3 (by rfl) ⟨1250942, by rfl⟩ : syracuseStep 6671693 = 2501885) B2501885
theorem B4447795 : Blo 2021435 4447795 := bstep (se 1 (by rfl) ⟨3335846, by rfl⟩ : syracuseStep 4447795 = 6671693) B6671693
theorem B5930393 : Blo 2021435 5930393 := bstep (se 2 (by rfl) ⟨2223897, by rfl⟩ : syracuseStep 5930393 = 4447795) B4447795
theorem B15814381 : Blo 2021435 15814381 := bstep (se 3 (by rfl) ⟨2965196, by rfl⟩ : syracuseStep 15814381 = 5930393) B5930393
theorem B21085841 : Blo 2021435 21085841 := bstep (se 2 (by rfl) ⟨7907190, by rfl⟩ : syracuseStep 21085841 = 15814381) B15814381
theorem B14057227 : Blo 2021435 14057227 := bstep (se 1 (by rfl) ⟨10542920, by rfl⟩ : syracuseStep 14057227 = 21085841) B21085841
theorem B74971877 : Blo 2021435 74971877 := bstep (se 4 (by rfl) ⟨7028613, by rfl⟩ : syracuseStep 74971877 = 14057227) B14057227
theorem B199925005 : Blo 2021435 199925005 := bstep (se 3 (by rfl) ⟨37485938, by rfl⟩ : syracuseStep 199925005 = 74971877) B74971877
theorem B266566673 : Blo 2021435 266566673 := bstep (se 2 (by rfl) ⟨99962502, by rfl⟩ : syracuseStep 266566673 = 199925005) B199925005
theorem B710844461 : Blo 2021435 710844461 := bstep (se 3 (by rfl) ⟨133283336, by rfl⟩ : syracuseStep 710844461 = 266566673) B266566673
theorem B473896307 : Blo 2021435 473896307 := bstep (se 1 (by rfl) ⟨355422230, by rfl⟩ : syracuseStep 473896307 = 710844461) B710844461
theorem B315930871 : Blo 2021435 315930871 := bstep (se 1 (by rfl) ⟨236948153, by rfl⟩ : syracuseStep 315930871 = 473896307) B473896307
theorem B421241161 : Blo 2021435 421241161 := bstep (se 2 (by rfl) ⟨157965435, by rfl⟩ : syracuseStep 421241161 = 315930871) B315930871
theorem B561654881 : Blo 2021435 561654881 := bstep (se 2 (by rfl) ⟨210620580, by rfl⟩ : syracuseStep 561654881 = 421241161) B421241161
theorem B374436587 : Blo 2021435 374436587 := bstep (se 1 (by rfl) ⟨280827440, by rfl⟩ : syracuseStep 374436587 = 561654881) B561654881
theorem B249624391 : Blo 2021435 249624391 := bstep (se 1 (by rfl) ⟨187218293, by rfl⟩ : syracuseStep 249624391 = 374436587) B374436587
theorem B332832521 : Blo 2021435 332832521 := bstep (se 2 (by rfl) ⟨124812195, by rfl⟩ : syracuseStep 332832521 = 249624391) B249624391
theorem B221888347 : Blo 2021435 221888347 := bstep (se 1 (by rfl) ⟨166416260, by rfl⟩ : syracuseStep 221888347 = 332832521) B332832521
theorem B4733618069 : Blo 2021435 4733618069 := bstep (se 6 (by rfl) ⟨110944173, by rfl⟩ : syracuseStep 4733618069 = 221888347) B221888347
theorem B12622981517 : Blo 2021435 12622981517 := bstep (se 3 (by rfl) ⟨2366809034, by rfl⟩ : syracuseStep 12622981517 = 4733618069) B4733618069
theorem B8415321011 : Blo 2021435 8415321011 := bstep (se 1 (by rfl) ⟨6311490758, by rfl⟩ : syracuseStep 8415321011 = 12622981517) B12622981517
theorem B5610214007 : Blo 2021435 5610214007 := bstep (se 1 (by rfl) ⟨4207660505, by rfl⟩ : syracuseStep 5610214007 = 8415321011) B8415321011
theorem B3740142671 : Blo 2021435 3740142671 := bstep (se 1 (by rfl) ⟨2805107003, by rfl⟩ : syracuseStep 3740142671 = 5610214007) B5610214007
theorem B2493428447 : Blo 2021435 2493428447 := bstep (se 1 (by rfl) ⟨1870071335, by rfl⟩ : syracuseStep 2493428447 = 3740142671) B3740142671
theorem B6649142525 : Blo 2021435 6649142525 := bstep (se 3 (by rfl) ⟨1246714223, by rfl⟩ : syracuseStep 6649142525 = 2493428447) B2493428447
theorem B4432761683 : Blo 2021435 4432761683 := bstep (se 1 (by rfl) ⟨3324571262, by rfl⟩ : syracuseStep 4432761683 = 6649142525) B6649142525
theorem B2955174455 : Blo 2021435 2955174455 := bstep (se 1 (by rfl) ⟨2216380841, by rfl⟩ : syracuseStep 2955174455 = 4432761683) B4432761683
theorem B1970116303 : Blo 2021435 1970116303 := bstep (se 1 (by rfl) ⟨1477587227, by rfl⟩ : syracuseStep 1970116303 = 2955174455) B2955174455
theorem B2626821737 : Blo 2021435 2626821737 := bstep (se 2 (by rfl) ⟨985058151, by rfl⟩ : syracuseStep 2626821737 = 1970116303) B1970116303
theorem B1751214491 : Blo 2021435 1751214491 := bstep (se 1 (by rfl) ⟨1313410868, by rfl⟩ : syracuseStep 1751214491 = 2626821737) B2626821737
theorem B1167476327 : Blo 2021435 1167476327 := bstep (se 1 (by rfl) ⟨875607245, by rfl⟩ : syracuseStep 1167476327 = 1751214491) B1751214491
theorem B778317551 : Blo 2021435 778317551 := bstep (se 1 (by rfl) ⟨583738163, by rfl⟩ : syracuseStep 778317551 = 1167476327) B1167476327
theorem B518878367 : Blo 2021435 518878367 := bstep (se 1 (by rfl) ⟨389158775, by rfl⟩ : syracuseStep 518878367 = 778317551) B778317551
theorem B5534702581 : Blo 2021435 5534702581 := bstep (se 5 (by rfl) ⟨259439183, by rfl⟩ : syracuseStep 5534702581 = 518878367) B518878367
theorem B7379603441 : Blo 2021435 7379603441 := bstep (se 2 (by rfl) ⟨2767351290, by rfl⟩ : syracuseStep 7379603441 = 5534702581) B5534702581
theorem B4919735627 : Blo 2021435 4919735627 := bstep (se 1 (by rfl) ⟨3689801720, by rfl⟩ : syracuseStep 4919735627 = 7379603441) B7379603441
theorem B3279823751 : Blo 2021435 3279823751 := bstep (se 1 (by rfl) ⟨2459867813, by rfl⟩ : syracuseStep 3279823751 = 4919735627) B4919735627
theorem B2186549167 : Blo 2021435 2186549167 := bstep (se 1 (by rfl) ⟨1639911875, by rfl⟩ : syracuseStep 2186549167 = 3279823751) B3279823751
theorem B2915398889 : Blo 2021435 2915398889 := bstep (se 2 (by rfl) ⟨1093274583, by rfl⟩ : syracuseStep 2915398889 = 2186549167) B2186549167
theorem B1943599259 : Blo 2021435 1943599259 := bstep (se 1 (by rfl) ⟨1457699444, by rfl⟩ : syracuseStep 1943599259 = 2915398889) B2915398889
theorem B5182931357 : Blo 2021435 5182931357 := bstep (se 3 (by rfl) ⟨971799629, by rfl⟩ : syracuseStep 5182931357 = 1943599259) B1943599259
theorem B3455287571 : Blo 2021435 3455287571 := bstep (se 1 (by rfl) ⟨2591465678, by rfl⟩ : syracuseStep 3455287571 = 5182931357) B5182931357
theorem B2303525047 : Blo 2021435 2303525047 := bstep (se 1 (by rfl) ⟨1727643785, by rfl⟩ : syracuseStep 2303525047 = 3455287571) B3455287571
theorem B3071366729 : Blo 2021435 3071366729 := bstep (se 2 (by rfl) ⟨1151762523, by rfl⟩ : syracuseStep 3071366729 = 2303525047) B2303525047
theorem B2047577819 : Blo 2021435 2047577819 := bstep (se 1 (by rfl) ⟨1535683364, by rfl⟩ : syracuseStep 2047577819 = 3071366729) B3071366729
theorem B5460207517 : Blo 2021435 5460207517 := bstep (se 3 (by rfl) ⟨1023788909, by rfl⟩ : syracuseStep 5460207517 = 2047577819) B2047577819
theorem B7280276689 : Blo 2021435 7280276689 := bstep (se 2 (by rfl) ⟨2730103758, by rfl⟩ : syracuseStep 7280276689 = 5460207517) B5460207517
theorem B38828142341 : Blo 2021435 38828142341 := bstep (se 4 (by rfl) ⟨3640138344, by rfl⟩ : syracuseStep 38828142341 = 7280276689) B7280276689
theorem B25885428227 : Blo 2021435 25885428227 := bstep (se 1 (by rfl) ⟨19414071170, by rfl⟩ : syracuseStep 25885428227 = 38828142341) B38828142341
theorem B17256952151 : Blo 2021435 17256952151 := bstep (se 1 (by rfl) ⟨12942714113, by rfl⟩ : syracuseStep 17256952151 = 25885428227) B25885428227
theorem B11504634767 : Blo 2021435 11504634767 := bstep (se 1 (by rfl) ⟨8628476075, by rfl⟩ : syracuseStep 11504634767 = 17256952151) B17256952151
theorem B7669756511 : Blo 2021435 7669756511 := bstep (se 1 (by rfl) ⟨5752317383, by rfl⟩ : syracuseStep 7669756511 = 11504634767) B11504634767
theorem B5113171007 : Blo 2021435 5113171007 := bstep (se 1 (by rfl) ⟨3834878255, by rfl⟩ : syracuseStep 5113171007 = 7669756511) B7669756511
theorem B3408780671 : Blo 2021435 3408780671 := bstep (se 1 (by rfl) ⟨2556585503, by rfl⟩ : syracuseStep 3408780671 = 5113171007) B5113171007
theorem B2272520447 : Blo 2021435 2272520447 := bstep (se 1 (by rfl) ⟨1704390335, by rfl⟩ : syracuseStep 2272520447 = 3408780671) B3408780671
theorem B1515013631 : Blo 2021435 1515013631 := bstep (se 1 (by rfl) ⟨1136260223, by rfl⟩ : syracuseStep 1515013631 = 2272520447) B2272520447
theorem B1010009087 : Blo 2021435 1010009087 := bstep (se 1 (by rfl) ⟨757506815, by rfl⟩ : syracuseStep 1010009087 = 1515013631) B1515013631
theorem B673339391 : Blo 2021435 673339391 := bstep (se 1 (by rfl) ⟨505004543, by rfl⟩ : syracuseStep 673339391 = 1010009087) B1010009087
theorem B448892927 : Blo 2021435 448892927 := bstep (se 1 (by rfl) ⟨336669695, by rfl⟩ : syracuseStep 448892927 = 673339391) B673339391
theorem B299261951 : Blo 2021435 299261951 := bstep (se 1 (by rfl) ⟨224446463, by rfl⟩ : syracuseStep 299261951 = 448892927) B448892927
theorem B199507967 : Blo 2021435 199507967 := bstep (se 1 (by rfl) ⟨149630975, by rfl⟩ : syracuseStep 199507967 = 299261951) B299261951
theorem B133005311 : Blo 2021435 133005311 := bstep (se 1 (by rfl) ⟨99753983, by rfl⟩ : syracuseStep 133005311 = 199507967) B199507967
theorem B88670207 : Blo 2021435 88670207 := bstep (se 1 (by rfl) ⟨66502655, by rfl⟩ : syracuseStep 88670207 = 133005311) B133005311
theorem B59113471 : Blo 2021435 59113471 := bstep (se 1 (by rfl) ⟨44335103, by rfl⟩ : syracuseStep 59113471 = 88670207) B88670207
theorem B78817961 : Blo 2021435 78817961 := bstep (se 2 (by rfl) ⟨29556735, by rfl⟩ : syracuseStep 78817961 = 59113471) B59113471
theorem B52545307 : Blo 2021435 52545307 := bstep (se 1 (by rfl) ⟨39408980, by rfl⟩ : syracuseStep 52545307 = 78817961) B78817961
theorem B70060409 : Blo 2021435 70060409 := bstep (se 2 (by rfl) ⟨26272653, by rfl⟩ : syracuseStep 70060409 = 52545307) B52545307
theorem B46706939 : Blo 2021435 46706939 := bstep (se 1 (by rfl) ⟨35030204, by rfl⟩ : syracuseStep 46706939 = 70060409) B70060409
theorem B31137959 : Blo 2021435 31137959 := bstep (se 1 (by rfl) ⟨23353469, by rfl⟩ : syracuseStep 31137959 = 46706939) B46706939
theorem B20758639 : Blo 2021435 20758639 := bstep (se 1 (by rfl) ⟨15568979, by rfl⟩ : syracuseStep 20758639 = 31137959) B31137959
theorem B27678185 : Blo 2021435 27678185 := bstep (se 2 (by rfl) ⟨10379319, by rfl⟩ : syracuseStep 27678185 = 20758639) B20758639
theorem B18452123 : Blo 2021435 18452123 := bstep (se 1 (by rfl) ⟨13839092, by rfl⟩ : syracuseStep 18452123 = 27678185) B27678185
theorem B12301415 : Blo 2021435 12301415 := bstep (se 1 (by rfl) ⟨9226061, by rfl⟩ : syracuseStep 12301415 = 18452123) B18452123
theorem B8200943 : Blo 2021435 8200943 := bstep (se 1 (by rfl) ⟨6150707, by rfl⟩ : syracuseStep 8200943 = 12301415) B12301415
theorem B5467295 : Blo 2021435 5467295 := bstep (se 1 (by rfl) ⟨4100471, by rfl⟩ : syracuseStep 5467295 = 8200943) B8200943
theorem B14579453 : Blo 2021435 14579453 := bstep (se 3 (by rfl) ⟨2733647, by rfl⟩ : syracuseStep 14579453 = 5467295) B5467295
theorem B38878541 : Blo 2021435 38878541 := bstep (se 3 (by rfl) ⟨7289726, by rfl⟩ : syracuseStep 38878541 = 14579453) B14579453
theorem B25919027 : Blo 2021435 25919027 := bstep (se 1 (by rfl) ⟨19439270, by rfl⟩ : syracuseStep 25919027 = 38878541) B38878541
theorem B17279351 : Blo 2021435 17279351 := bstep (se 1 (by rfl) ⟨12959513, by rfl⟩ : syracuseStep 17279351 = 25919027) B25919027
theorem B11519567 : Blo 2021435 11519567 := bstep (se 1 (by rfl) ⟨8639675, by rfl⟩ : syracuseStep 11519567 = 17279351) B17279351
theorem B7679711 : Blo 2021435 7679711 := bstep (se 1 (by rfl) ⟨5759783, by rfl⟩ : syracuseStep 7679711 = 11519567) B11519567
theorem B5119807 : Blo 2021435 5119807 := bstep (se 1 (by rfl) ⟨3839855, by rfl⟩ : syracuseStep 5119807 = 7679711) B7679711
theorem B6826409 : Blo 2021435 6826409 := bstep (se 2 (by rfl) ⟨2559903, by rfl⟩ : syracuseStep 6826409 = 5119807) B5119807
theorem B4550939 : Blo 2021435 4550939 := bstep (se 1 (by rfl) ⟨3413204, by rfl⟩ : syracuseStep 4550939 = 6826409) B6826409
theorem B3033959 : Blo 2021435 3033959 := bstep (se 1 (by rfl) ⟨2275469, by rfl⟩ : syracuseStep 3033959 = 4550939) B4550939
theorem B2022639 : Blo 2021435 2022639 := bstep (se 1 (by rfl) ⟨1516979, by rfl⟩ : syracuseStep 2022639 = 3033959) B3033959
theorem B3033965 : Blo 2021435 3033965 := bbase (se 3 (by rfl) ⟨568868, by rfl⟩ : syracuseStep 3033965 = 1137737) (by norm_num)
theorem B2022643 : Blo 2021435 2022643 := bstep (se 1 (by rfl) ⟨1516982, by rfl⟩ : syracuseStep 2022643 = 3033965) B3033965
theorem B4550957 : Blo 2021435 4550957 := bbase (se 3 (by rfl) ⟨853304, by rfl⟩ : syracuseStep 4550957 = 1706609) (by norm_num)
theorem B3033971 : Blo 2021435 3033971 := bstep (se 1 (by rfl) ⟨2275478, by rfl⟩ : syracuseStep 3033971 = 4550957) B4550957
theorem B2022647 : Blo 2021435 2022647 := bstep (se 1 (by rfl) ⟨1516985, by rfl⟩ : syracuseStep 2022647 = 3033971) B3033971
theorem B6479797 : Blo 2021435 6479797 := bbase (se 5 (by rfl) ⟨303740, by rfl⟩ : syracuseStep 6479797 = 607481) (by norm_num)
theorem B8639729 : Blo 2021435 8639729 := bstep (se 2 (by rfl) ⟨3239898, by rfl⟩ : syracuseStep 8639729 = 6479797) B6479797
theorem B5759819 : Blo 2021435 5759819 := bstep (se 1 (by rfl) ⟨4319864, by rfl⟩ : syracuseStep 5759819 = 8639729) B8639729
theorem B3839879 : Blo 2021435 3839879 := bstep (se 1 (by rfl) ⟨2879909, by rfl⟩ : syracuseStep 3839879 = 5759819) B5759819
theorem B2559919 : Blo 2021435 2559919 := bstep (se 1 (by rfl) ⟨1919939, by rfl⟩ : syracuseStep 2559919 = 3839879) B3839879
theorem B3413225 : Blo 2021435 3413225 := bstep (se 2 (by rfl) ⟨1279959, by rfl⟩ : syracuseStep 3413225 = 2559919) B2559919
theorem B2275483 : Blo 2021435 2275483 := bstep (se 1 (by rfl) ⟨1706612, by rfl⟩ : syracuseStep 2275483 = 3413225) B3413225
theorem B3033977 : Blo 2021435 3033977 := bstep (se 2 (by rfl) ⟨1137741, by rfl⟩ : syracuseStep 3033977 = 2275483) B2275483
theorem B2022651 : Blo 2021435 2022651 := bstep (se 1 (by rfl) ⟨1516988, by rfl⟩ : syracuseStep 2022651 = 3033977) B3033977
theorem B3694621 : Blo 2021435 3694621 := bbase (se 3 (by rfl) ⟨692741, by rfl⟩ : syracuseStep 3694621 = 1385483) (by norm_num)
theorem B4926161 : Blo 2021435 4926161 := bstep (se 2 (by rfl) ⟨1847310, by rfl⟩ : syracuseStep 4926161 = 3694621) B3694621
theorem B3284107 : Blo 2021435 3284107 := bstep (se 1 (by rfl) ⟨2463080, by rfl⟩ : syracuseStep 3284107 = 4926161) B4926161
theorem B70060949 : Blo 2021435 70060949 := bstep (se 6 (by rfl) ⟨1642053, by rfl⟩ : syracuseStep 70060949 = 3284107) B3284107
theorem B46707299 : Blo 2021435 46707299 := bstep (se 1 (by rfl) ⟨35030474, by rfl⟩ : syracuseStep 46707299 = 70060949) B70060949
theorem B31138199 : Blo 2021435 31138199 := bstep (se 1 (by rfl) ⟨23353649, by rfl⟩ : syracuseStep 31138199 = 46707299) B46707299
theorem B20758799 : Blo 2021435 20758799 := bstep (se 1 (by rfl) ⟨15569099, by rfl⟩ : syracuseStep 20758799 = 31138199) B31138199
theorem B55356797 : Blo 2021435 55356797 := bstep (se 3 (by rfl) ⟨10379399, by rfl⟩ : syracuseStep 55356797 = 20758799) B20758799
theorem B147618125 : Blo 2021435 147618125 := bstep (se 3 (by rfl) ⟨27678398, by rfl⟩ : syracuseStep 147618125 = 55356797) B55356797
theorem B98412083 : Blo 2021435 98412083 := bstep (se 1 (by rfl) ⟨73809062, by rfl⟩ : syracuseStep 98412083 = 147618125) B147618125
theorem B65608055 : Blo 2021435 65608055 := bstep (se 1 (by rfl) ⟨49206041, by rfl⟩ : syracuseStep 65608055 = 98412083) B98412083
theorem B43738703 : Blo 2021435 43738703 := bstep (se 1 (by rfl) ⟨32804027, by rfl⟩ : syracuseStep 43738703 = 65608055) B65608055
theorem B29159135 : Blo 2021435 29159135 := bstep (se 1 (by rfl) ⟨21869351, by rfl⟩ : syracuseStep 29159135 = 43738703) B43738703
theorem B19439423 : Blo 2021435 19439423 := bstep (se 1 (by rfl) ⟨14579567, by rfl⟩ : syracuseStep 19439423 = 29159135) B29159135
theorem B12959615 : Blo 2021435 12959615 := bstep (se 1 (by rfl) ⟨9719711, by rfl⟩ : syracuseStep 12959615 = 19439423) B19439423
theorem B34558973 : Blo 2021435 34558973 := bstep (se 3 (by rfl) ⟨6479807, by rfl⟩ : syracuseStep 34558973 = 12959615) B12959615
theorem B23039315 : Blo 2021435 23039315 := bstep (se 1 (by rfl) ⟨17279486, by rfl⟩ : syracuseStep 23039315 = 34558973) B34558973
theorem B15359543 : Blo 2021435 15359543 := bstep (se 1 (by rfl) ⟨11519657, by rfl⟩ : syracuseStep 15359543 = 23039315) B23039315
theorem B10239695 : Blo 2021435 10239695 := bstep (se 1 (by rfl) ⟨7679771, by rfl⟩ : syracuseStep 10239695 = 15359543) B15359543
theorem B6826463 : Blo 2021435 6826463 := bstep (se 1 (by rfl) ⟨5119847, by rfl⟩ : syracuseStep 6826463 = 10239695) B10239695
theorem B4550975 : Blo 2021435 4550975 := bstep (se 1 (by rfl) ⟨3413231, by rfl⟩ : syracuseStep 4550975 = 6826463) B6826463
theorem B3033983 : Blo 2021435 3033983 := bstep (se 1 (by rfl) ⟨2275487, by rfl⟩ : syracuseStep 3033983 = 4550975) B4550975
theorem B2022655 : Blo 2021435 2022655 := bstep (se 1 (by rfl) ⟨1516991, by rfl⟩ : syracuseStep 2022655 = 3033983) B3033983
theorem B3033989 : Blo 2021435 3033989 := bbase (se 4 (by rfl) ⟨284436, by rfl⟩ : syracuseStep 3033989 = 568873) (by norm_num)
theorem B2022659 : Blo 2021435 2022659 := bstep (se 1 (by rfl) ⟨1516994, by rfl⟩ : syracuseStep 2022659 = 3033989) B3033989
theorem B3413245 : Blo 2021435 3413245 := bbase (se 3 (by rfl) ⟨639983, by rfl⟩ : syracuseStep 3413245 = 1279967) (by norm_num)
theorem B4550993 : Blo 2021435 4550993 := bstep (se 2 (by rfl) ⟨1706622, by rfl⟩ : syracuseStep 4550993 = 3413245) B3413245
theorem B3033995 : Blo 2021435 3033995 := bstep (se 1 (by rfl) ⟨2275496, by rfl⟩ : syracuseStep 3033995 = 4550993) B4550993
theorem B2022663 : Blo 2021435 2022663 := bstep (se 1 (by rfl) ⟨1516997, by rfl⟩ : syracuseStep 2022663 = 3033995) B3033995
theorem B2275501 : Blo 2021435 2275501 := bbase (se 3 (by rfl) ⟨426656, by rfl⟩ : syracuseStep 2275501 = 853313) (by norm_num)
theorem B3034001 : Blo 2021435 3034001 := bstep (se 2 (by rfl) ⟨1137750, by rfl⟩ : syracuseStep 3034001 = 2275501) B2275501
theorem B2022667 : Blo 2021435 2022667 := bstep (se 1 (by rfl) ⟨1517000, by rfl⟩ : syracuseStep 2022667 = 3034001) B3034001
theorem B6826517 : Blo 2021435 6826517 := bbase (se 6 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 6826517 = 319993) (by norm_num)
theorem B4551011 : Blo 2021435 4551011 := bstep (se 1 (by rfl) ⟨3413258, by rfl⟩ : syracuseStep 4551011 = 6826517) B6826517
theorem B3034007 : Blo 2021435 3034007 := bstep (se 1 (by rfl) ⟨2275505, by rfl⟩ : syracuseStep 3034007 = 4551011) B4551011
theorem B2022671 : Blo 2021435 2022671 := bstep (se 1 (by rfl) ⟨1517003, by rfl⟩ : syracuseStep 2022671 = 3034007) B3034007
theorem B3034013 : Blo 2021435 3034013 := bbase (se 3 (by rfl) ⟨568877, by rfl⟩ : syracuseStep 3034013 = 1137755) (by norm_num)
theorem B2022675 : Blo 2021435 2022675 := bstep (se 1 (by rfl) ⟨1517006, by rfl⟩ : syracuseStep 2022675 = 3034013) B3034013
theorem B4551029 : Blo 2021435 4551029 := bbase (se 5 (by rfl) ⟨213329, by rfl⟩ : syracuseStep 4551029 = 426659) (by norm_num)
theorem B3034019 : Blo 2021435 3034019 := bstep (se 1 (by rfl) ⟨2275514, by rfl⟩ : syracuseStep 3034019 = 4551029) B4551029
theorem B2022679 : Blo 2021435 2022679 := bstep (se 1 (by rfl) ⟨1517009, by rfl⟩ : syracuseStep 2022679 = 3034019) B3034019
theorem B12959797 : Blo 2021435 12959797 := bbase (se 5 (by rfl) ⟨607490, by rfl⟩ : syracuseStep 12959797 = 1214981) (by norm_num)
theorem B17279729 : Blo 2021435 17279729 := bstep (se 2 (by rfl) ⟨6479898, by rfl⟩ : syracuseStep 17279729 = 12959797) B12959797
theorem B11519819 : Blo 2021435 11519819 := bstep (se 1 (by rfl) ⟨8639864, by rfl⟩ : syracuseStep 11519819 = 17279729) B17279729
theorem B7679879 : Blo 2021435 7679879 := bstep (se 1 (by rfl) ⟨5759909, by rfl⟩ : syracuseStep 7679879 = 11519819) B11519819
theorem B5119919 : Blo 2021435 5119919 := bstep (se 1 (by rfl) ⟨3839939, by rfl⟩ : syracuseStep 5119919 = 7679879) B7679879
theorem B3413279 : Blo 2021435 3413279 := bstep (se 1 (by rfl) ⟨2559959, by rfl⟩ : syracuseStep 3413279 = 5119919) B5119919
theorem B2275519 : Blo 2021435 2275519 := bstep (se 1 (by rfl) ⟨1706639, by rfl⟩ : syracuseStep 2275519 = 3413279) B3413279
theorem B3034025 : Blo 2021435 3034025 := bstep (se 2 (by rfl) ⟨1137759, by rfl⟩ : syracuseStep 3034025 = 2275519) B2275519
theorem B2022683 : Blo 2021435 2022683 := bstep (se 1 (by rfl) ⟨1517012, by rfl⟩ : syracuseStep 2022683 = 3034025) B3034025
theorem B7679893 : Blo 2021435 7679893 := bbase (se 6 (by rfl) ⟨179997, by rfl⟩ : syracuseStep 7679893 = 359995) (by norm_num)
theorem B10239857 : Blo 2021435 10239857 := bstep (se 2 (by rfl) ⟨3839946, by rfl⟩ : syracuseStep 10239857 = 7679893) B7679893
theorem B6826571 : Blo 2021435 6826571 := bstep (se 1 (by rfl) ⟨5119928, by rfl⟩ : syracuseStep 6826571 = 10239857) B10239857
theorem B4551047 : Blo 2021435 4551047 := bstep (se 1 (by rfl) ⟨3413285, by rfl⟩ : syracuseStep 4551047 = 6826571) B6826571
theorem B3034031 : Blo 2021435 3034031 := bstep (se 1 (by rfl) ⟨2275523, by rfl⟩ : syracuseStep 3034031 = 4551047) B4551047
theorem B2022687 : Blo 2021435 2022687 := bstep (se 1 (by rfl) ⟨1517015, by rfl⟩ : syracuseStep 2022687 = 3034031) B3034031
theorem B3034037 : Blo 2021435 3034037 := bbase (se 5 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 3034037 = 284441) (by norm_num)
theorem B2022691 : Blo 2021435 2022691 := bstep (se 1 (by rfl) ⟨1517018, by rfl⟩ : syracuseStep 2022691 = 3034037) B3034037
theorem B5119949 : Blo 2021435 5119949 := bbase (se 3 (by rfl) ⟨959990, by rfl⟩ : syracuseStep 5119949 = 1919981) (by norm_num)
theorem B3413299 : Blo 2021435 3413299 := bstep (se 1 (by rfl) ⟨2559974, by rfl⟩ : syracuseStep 3413299 = 5119949) B5119949
theorem B4551065 : Blo 2021435 4551065 := bstep (se 2 (by rfl) ⟨1706649, by rfl⟩ : syracuseStep 4551065 = 3413299) B3413299
theorem B3034043 : Blo 2021435 3034043 := bstep (se 1 (by rfl) ⟨2275532, by rfl⟩ : syracuseStep 3034043 = 4551065) B4551065
theorem B2022695 : Blo 2021435 2022695 := bstep (se 1 (by rfl) ⟨1517021, by rfl⟩ : syracuseStep 2022695 = 3034043) B3034043
theorem B2275537 : Blo 2021435 2275537 := bbase (se 2 (by rfl) ⟨853326, by rfl⟩ : syracuseStep 2275537 = 1706653) (by norm_num)
theorem B3034049 : Blo 2021435 3034049 := bstep (se 2 (by rfl) ⟨1137768, by rfl⟩ : syracuseStep 3034049 = 2275537) B2275537
theorem B2022699 : Blo 2021435 2022699 := bstep (se 1 (by rfl) ⟨1517024, by rfl⟩ : syracuseStep 2022699 = 3034049) B3034049
theorem B7890949 : Blo 2021435 7890949 := bbase (se 4 (by rfl) ⟨739776, by rfl⟩ : syracuseStep 7890949 = 1479553) (by norm_num)
theorem B10521265 : Blo 2021435 10521265 := bstep (se 2 (by rfl) ⟨3945474, by rfl⟩ : syracuseStep 10521265 = 7890949) B7890949
theorem B14028353 : Blo 2021435 14028353 := bstep (se 2 (by rfl) ⟨5260632, by rfl⟩ : syracuseStep 14028353 = 10521265) B10521265
theorem B9352235 : Blo 2021435 9352235 := bstep (se 1 (by rfl) ⟨7014176, by rfl⟩ : syracuseStep 9352235 = 14028353) B14028353
theorem B6234823 : Blo 2021435 6234823 := bstep (se 1 (by rfl) ⟨4676117, by rfl⟩ : syracuseStep 6234823 = 9352235) B9352235
theorem B33252389 : Blo 2021435 33252389 := bstep (se 4 (by rfl) ⟨3117411, by rfl⟩ : syracuseStep 33252389 = 6234823) B6234823
theorem B22168259 : Blo 2021435 22168259 := bstep (se 1 (by rfl) ⟨16626194, by rfl⟩ : syracuseStep 22168259 = 33252389) B33252389
theorem B14778839 : Blo 2021435 14778839 := bstep (se 1 (by rfl) ⟨11084129, by rfl⟩ : syracuseStep 14778839 = 22168259) B22168259
theorem B9852559 : Blo 2021435 9852559 := bstep (se 1 (by rfl) ⟨7389419, by rfl⟩ : syracuseStep 9852559 = 14778839) B14778839
theorem B52546981 : Blo 2021435 52546981 := bstep (se 4 (by rfl) ⟨4926279, by rfl⟩ : syracuseStep 52546981 = 9852559) B9852559
theorem B70062641 : Blo 2021435 70062641 := bstep (se 2 (by rfl) ⟨26273490, by rfl⟩ : syracuseStep 70062641 = 52546981) B52546981
theorem B46708427 : Blo 2021435 46708427 := bstep (se 1 (by rfl) ⟨35031320, by rfl⟩ : syracuseStep 46708427 = 70062641) B70062641
theorem B31138951 : Blo 2021435 31138951 := bstep (se 1 (by rfl) ⟨23354213, by rfl⟩ : syracuseStep 31138951 = 46708427) B46708427
theorem B41518601 : Blo 2021435 41518601 := bstep (se 2 (by rfl) ⟨15569475, by rfl⟩ : syracuseStep 41518601 = 31138951) B31138951
theorem B27679067 : Blo 2021435 27679067 := bstep (se 1 (by rfl) ⟨20759300, by rfl⟩ : syracuseStep 27679067 = 41518601) B41518601
theorem B18452711 : Blo 2021435 18452711 := bstep (se 1 (by rfl) ⟨13839533, by rfl⟩ : syracuseStep 18452711 = 27679067) B27679067
theorem B12301807 : Blo 2021435 12301807 := bstep (se 1 (by rfl) ⟨9226355, by rfl⟩ : syracuseStep 12301807 = 18452711) B18452711
theorem B16402409 : Blo 2021435 16402409 := bstep (se 2 (by rfl) ⟨6150903, by rfl⟩ : syracuseStep 16402409 = 12301807) B12301807
theorem B10934939 : Blo 2021435 10934939 := bstep (se 1 (by rfl) ⟨8201204, by rfl⟩ : syracuseStep 10934939 = 16402409) B16402409
theorem B7289959 : Blo 2021435 7289959 := bstep (se 1 (by rfl) ⟨5467469, by rfl⟩ : syracuseStep 7289959 = 10934939) B10934939
theorem B9719945 : Blo 2021435 9719945 := bstep (se 2 (by rfl) ⟨3644979, by rfl⟩ : syracuseStep 9719945 = 7289959) B7289959
theorem B6479963 : Blo 2021435 6479963 := bstep (se 1 (by rfl) ⟨4859972, by rfl⟩ : syracuseStep 6479963 = 9719945) B9719945
theorem B4319975 : Blo 2021435 4319975 := bstep (se 1 (by rfl) ⟨3239981, by rfl⟩ : syracuseStep 4319975 = 6479963) B6479963
theorem B2879983 : Blo 2021435 2879983 := bstep (se 1 (by rfl) ⟨2159987, by rfl⟩ : syracuseStep 2879983 = 4319975) B4319975
theorem B3839977 : Blo 2021435 3839977 := bstep (se 2 (by rfl) ⟨1439991, by rfl⟩ : syracuseStep 3839977 = 2879983) B2879983
theorem B5119969 : Blo 2021435 5119969 := bstep (se 2 (by rfl) ⟨1919988, by rfl⟩ : syracuseStep 5119969 = 3839977) B3839977
theorem B6826625 : Blo 2021435 6826625 := bstep (se 2 (by rfl) ⟨2559984, by rfl⟩ : syracuseStep 6826625 = 5119969) B5119969
theorem B4551083 : Blo 2021435 4551083 := bstep (se 1 (by rfl) ⟨3413312, by rfl⟩ : syracuseStep 4551083 = 6826625) B6826625
theorem B3034055 : Blo 2021435 3034055 := bstep (se 1 (by rfl) ⟨2275541, by rfl⟩ : syracuseStep 3034055 = 4551083) B4551083
theorem B2022703 : Blo 2021435 2022703 := bstep (se 1 (by rfl) ⟨1517027, by rfl⟩ : syracuseStep 2022703 = 3034055) B3034055
theorem B3034061 : Blo 2021435 3034061 := bbase (se 3 (by rfl) ⟨568886, by rfl⟩ : syracuseStep 3034061 = 1137773) (by norm_num)
theorem B2022707 : Blo 2021435 2022707 := bstep (se 1 (by rfl) ⟨1517030, by rfl⟩ : syracuseStep 2022707 = 3034061) B3034061
theorem B4551101 : Blo 2021435 4551101 := bbase (se 3 (by rfl) ⟨853331, by rfl⟩ : syracuseStep 4551101 = 1706663) (by norm_num)
theorem B3034067 : Blo 2021435 3034067 := bstep (se 1 (by rfl) ⟨2275550, by rfl⟩ : syracuseStep 3034067 = 4551101) B4551101
theorem B2022711 : Blo 2021435 2022711 := bstep (se 1 (by rfl) ⟨1517033, by rfl⟩ : syracuseStep 2022711 = 3034067) B3034067
theorem B3413333 : Blo 2021435 3413333 := bbase (se 14 (by rfl) ⟨312, by rfl⟩ : syracuseStep 3413333 = 625) (by norm_num)
theorem B2275555 : Blo 2021435 2275555 := bstep (se 1 (by rfl) ⟨1706666, by rfl⟩ : syracuseStep 2275555 = 3413333) B3413333
theorem B3034073 : Blo 2021435 3034073 := bstep (se 2 (by rfl) ⟨1137777, by rfl⟩ : syracuseStep 3034073 = 2275555) B2275555
theorem B2022715 : Blo 2021435 2022715 := bstep (se 1 (by rfl) ⟨1517036, by rfl⟩ : syracuseStep 2022715 = 3034073) B3034073
theorem B2430005 : Blo 2021435 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B6480013 : Blo 2021435 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B8640017 : Blo 2021435 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B5760011 : Blo 2021435 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B15360029 : Blo 2021435 15360029 := bstep (se 3 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 15360029 = 5760011) B5760011
theorem B10240019 : Blo 2021435 10240019 := bstep (se 1 (by rfl) ⟨7680014, by rfl⟩ : syracuseStep 10240019 = 15360029) B15360029
theorem B6826679 : Blo 2021435 6826679 := bstep (se 1 (by rfl) ⟨5120009, by rfl⟩ : syracuseStep 6826679 = 10240019) B10240019
theorem B4551119 : Blo 2021435 4551119 := bstep (se 1 (by rfl) ⟨3413339, by rfl⟩ : syracuseStep 4551119 = 6826679) B6826679
theorem B3034079 : Blo 2021435 3034079 := bstep (se 1 (by rfl) ⟨2275559, by rfl⟩ : syracuseStep 3034079 = 4551119) B4551119
theorem B2022719 : Blo 2021435 2022719 := bstep (se 1 (by rfl) ⟨1517039, by rfl⟩ : syracuseStep 2022719 = 3034079) B3034079
theorem B3034085 : Blo 2021435 3034085 := bbase (se 4 (by rfl) ⟨284445, by rfl⟩ : syracuseStep 3034085 = 568891) (by norm_num)
theorem B2022723 : Blo 2021435 2022723 := bstep (se 1 (by rfl) ⟨1517042, by rfl⟩ : syracuseStep 2022723 = 3034085) B3034085
theorem B8640053 : Blo 2021435 8640053 := bbase (se 5 (by rfl) ⟨405002, by rfl⟩ : syracuseStep 8640053 = 810005) (by norm_num)
theorem B5760035 : Blo 2021435 5760035 := bstep (se 1 (by rfl) ⟨4320026, by rfl⟩ : syracuseStep 5760035 = 8640053) B8640053
theorem B3840023 : Blo 2021435 3840023 := bstep (se 1 (by rfl) ⟨2880017, by rfl⟩ : syracuseStep 3840023 = 5760035) B5760035
theorem B2560015 : Blo 2021435 2560015 := bstep (se 1 (by rfl) ⟨1920011, by rfl⟩ : syracuseStep 2560015 = 3840023) B3840023
theorem B3413353 : Blo 2021435 3413353 := bstep (se 2 (by rfl) ⟨1280007, by rfl⟩ : syracuseStep 3413353 = 2560015) B2560015
theorem B4551137 : Blo 2021435 4551137 := bstep (se 2 (by rfl) ⟨1706676, by rfl⟩ : syracuseStep 4551137 = 3413353) B3413353
theorem B3034091 : Blo 2021435 3034091 := bstep (se 1 (by rfl) ⟨2275568, by rfl⟩ : syracuseStep 3034091 = 4551137) B4551137
theorem B2022727 : Blo 2021435 2022727 := bstep (se 1 (by rfl) ⟨1517045, by rfl⟩ : syracuseStep 2022727 = 3034091) B3034091
theorem B2275573 : Blo 2021435 2275573 := bbase (se 5 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 2275573 = 213335) (by norm_num)
theorem B3034097 : Blo 2021435 3034097 := bstep (se 2 (by rfl) ⟨1137786, by rfl⟩ : syracuseStep 3034097 = 2275573) B2275573
theorem B2022731 : Blo 2021435 2022731 := bstep (se 1 (by rfl) ⟨1517048, by rfl⟩ : syracuseStep 2022731 = 3034097) B3034097
theorem B2560025 : Blo 2021435 2560025 := bbase (se 2 (by rfl) ⟨960009, by rfl⟩ : syracuseStep 2560025 = 1920019) (by norm_num)
theorem B6826733 : Blo 2021435 6826733 := bstep (se 3 (by rfl) ⟨1280012, by rfl⟩ : syracuseStep 6826733 = 2560025) B2560025
theorem B4551155 : Blo 2021435 4551155 := bstep (se 1 (by rfl) ⟨3413366, by rfl⟩ : syracuseStep 4551155 = 6826733) B6826733
theorem B3034103 : Blo 2021435 3034103 := bstep (se 1 (by rfl) ⟨2275577, by rfl⟩ : syracuseStep 3034103 = 4551155) B4551155
theorem B2022735 : Blo 2021435 2022735 := bstep (se 1 (by rfl) ⟨1517051, by rfl⟩ : syracuseStep 2022735 = 3034103) B3034103
theorem B3034109 : Blo 2021435 3034109 := bbase (se 3 (by rfl) ⟨568895, by rfl⟩ : syracuseStep 3034109 = 1137791) (by norm_num)
theorem B2022739 : Blo 2021435 2022739 := bstep (se 1 (by rfl) ⟨1517054, by rfl⟩ : syracuseStep 2022739 = 3034109) B3034109
theorem B4551173 : Blo 2021435 4551173 := bbase (se 4 (by rfl) ⟨426672, by rfl⟩ : syracuseStep 4551173 = 853345) (by norm_num)
theorem B3034115 : Blo 2021435 3034115 := bstep (se 1 (by rfl) ⟨2275586, by rfl⟩ : syracuseStep 3034115 = 4551173) B4551173
theorem B2022743 : Blo 2021435 2022743 := bstep (se 1 (by rfl) ⟨1517057, by rfl⟩ : syracuseStep 2022743 = 3034115) B3034115
theorem B3840061 : Blo 2021435 3840061 := bbase (se 3 (by rfl) ⟨720011, by rfl⟩ : syracuseStep 3840061 = 1440023) (by norm_num)
theorem B5120081 : Blo 2021435 5120081 := bstep (se 2 (by rfl) ⟨1920030, by rfl⟩ : syracuseStep 5120081 = 3840061) B3840061
theorem B3413387 : Blo 2021435 3413387 := bstep (se 1 (by rfl) ⟨2560040, by rfl⟩ : syracuseStep 3413387 = 5120081) B5120081
theorem B2275591 : Blo 2021435 2275591 := bstep (se 1 (by rfl) ⟨1706693, by rfl⟩ : syracuseStep 2275591 = 3413387) B3413387
theorem B3034121 : Blo 2021435 3034121 := bstep (se 2 (by rfl) ⟨1137795, by rfl⟩ : syracuseStep 3034121 = 2275591) B2275591
theorem B2022747 : Blo 2021435 2022747 := bstep (se 1 (by rfl) ⟨1517060, by rfl⟩ : syracuseStep 2022747 = 3034121) B3034121
theorem B10240181 : Blo 2021435 10240181 := bbase (se 5 (by rfl) ⟨480008, by rfl⟩ : syracuseStep 10240181 = 960017) (by norm_num)
theorem B6826787 : Blo 2021435 6826787 := bstep (se 1 (by rfl) ⟨5120090, by rfl⟩ : syracuseStep 6826787 = 10240181) B10240181
theorem B4551191 : Blo 2021435 4551191 := bstep (se 1 (by rfl) ⟨3413393, by rfl⟩ : syracuseStep 4551191 = 6826787) B6826787
theorem B3034127 : Blo 2021435 3034127 := bstep (se 1 (by rfl) ⟨2275595, by rfl⟩ : syracuseStep 3034127 = 4551191) B4551191
theorem B2022751 : Blo 2021435 2022751 := bstep (se 1 (by rfl) ⟨1517063, by rfl⟩ : syracuseStep 2022751 = 3034127) B3034127
theorem B3034133 : Blo 2021435 3034133 := bbase (se 6 (by rfl) ⟨71112, by rfl⟩ : syracuseStep 3034133 = 142225) (by norm_num)
theorem B2022755 : Blo 2021435 2022755 := bstep (se 1 (by rfl) ⟨1517066, by rfl⟩ : syracuseStep 2022755 = 3034133) B3034133
theorem B2630389 : Blo 2021435 2630389 := bbase (se 5 (by rfl) ⟨123299, by rfl⟩ : syracuseStep 2630389 = 246599) (by norm_num)
theorem B3507185 : Blo 2021435 3507185 := bstep (se 2 (by rfl) ⟨1315194, by rfl⟩ : syracuseStep 3507185 = 2630389) B2630389
theorem B2338123 : Blo 2021435 2338123 := bstep (se 1 (by rfl) ⟨1753592, by rfl⟩ : syracuseStep 2338123 = 3507185) B3507185
theorem B3117497 : Blo 2021435 3117497 := bstep (se 2 (by rfl) ⟨1169061, by rfl⟩ : syracuseStep 3117497 = 2338123) B2338123
theorem B33253301 : Blo 2021435 33253301 := bstep (se 5 (by rfl) ⟨1558748, by rfl⟩ : syracuseStep 33253301 = 3117497) B3117497
theorem B88675469 : Blo 2021435 88675469 := bstep (se 3 (by rfl) ⟨16626650, by rfl⟩ : syracuseStep 88675469 = 33253301) B33253301
theorem B59116979 : Blo 2021435 59116979 := bstep (se 1 (by rfl) ⟨44337734, by rfl⟩ : syracuseStep 59116979 = 88675469) B88675469
theorem B39411319 : Blo 2021435 39411319 := bstep (se 1 (by rfl) ⟨29558489, by rfl⟩ : syracuseStep 39411319 = 59116979) B59116979
theorem B52548425 : Blo 2021435 52548425 := bstep (se 2 (by rfl) ⟨19705659, by rfl⟩ : syracuseStep 52548425 = 39411319) B39411319
theorem B35032283 : Blo 2021435 35032283 := bstep (se 1 (by rfl) ⟨26274212, by rfl⟩ : syracuseStep 35032283 = 52548425) B52548425
theorem B23354855 : Blo 2021435 23354855 := bstep (se 1 (by rfl) ⟨17516141, by rfl⟩ : syracuseStep 23354855 = 35032283) B35032283
theorem B15569903 : Blo 2021435 15569903 := bstep (se 1 (by rfl) ⟨11677427, by rfl⟩ : syracuseStep 15569903 = 23354855) B23354855
theorem B10379935 : Blo 2021435 10379935 := bstep (se 1 (by rfl) ⟨7784951, by rfl⟩ : syracuseStep 10379935 = 15569903) B15569903
theorem B13839913 : Blo 2021435 13839913 := bstep (se 2 (by rfl) ⟨5189967, by rfl⟩ : syracuseStep 13839913 = 10379935) B10379935
theorem B73812869 : Blo 2021435 73812869 := bstep (se 4 (by rfl) ⟨6919956, by rfl⟩ : syracuseStep 73812869 = 13839913) B13839913
theorem B49208579 : Blo 2021435 49208579 := bstep (se 1 (by rfl) ⟨36906434, by rfl⟩ : syracuseStep 49208579 = 73812869) B73812869
theorem B32805719 : Blo 2021435 32805719 := bstep (se 1 (by rfl) ⟨24604289, by rfl⟩ : syracuseStep 32805719 = 49208579) B49208579
theorem B21870479 : Blo 2021435 21870479 := bstep (se 1 (by rfl) ⟨16402859, by rfl⟩ : syracuseStep 21870479 = 32805719) B32805719
theorem B14580319 : Blo 2021435 14580319 := bstep (se 1 (by rfl) ⟨10935239, by rfl⟩ : syracuseStep 14580319 = 21870479) B21870479
theorem B19440425 : Blo 2021435 19440425 := bstep (se 2 (by rfl) ⟨7290159, by rfl⟩ : syracuseStep 19440425 = 14580319) B14580319
theorem B12960283 : Blo 2021435 12960283 := bstep (se 1 (by rfl) ⟨9720212, by rfl⟩ : syracuseStep 12960283 = 19440425) B19440425
theorem B17280377 : Blo 2021435 17280377 := bstep (se 2 (by rfl) ⟨6480141, by rfl⟩ : syracuseStep 17280377 = 12960283) B12960283
theorem B11520251 : Blo 2021435 11520251 := bstep (se 1 (by rfl) ⟨8640188, by rfl⟩ : syracuseStep 11520251 = 17280377) B17280377
theorem B7680167 : Blo 2021435 7680167 := bstep (se 1 (by rfl) ⟨5760125, by rfl⟩ : syracuseStep 7680167 = 11520251) B11520251
theorem B5120111 : Blo 2021435 5120111 := bstep (se 1 (by rfl) ⟨3840083, by rfl⟩ : syracuseStep 5120111 = 7680167) B7680167
theorem B3413407 : Blo 2021435 3413407 := bstep (se 1 (by rfl) ⟨2560055, by rfl⟩ : syracuseStep 3413407 = 5120111) B5120111
theorem B4551209 : Blo 2021435 4551209 := bstep (se 2 (by rfl) ⟨1706703, by rfl⟩ : syracuseStep 4551209 = 3413407) B3413407
theorem B3034139 : Blo 2021435 3034139 := bstep (se 1 (by rfl) ⟨2275604, by rfl⟩ : syracuseStep 3034139 = 4551209) B4551209
theorem B2022759 : Blo 2021435 2022759 := bstep (se 1 (by rfl) ⟨1517069, by rfl⟩ : syracuseStep 2022759 = 3034139) B3034139
theorem B2275609 : Blo 2021435 2275609 := bbase (se 2 (by rfl) ⟨853353, by rfl⟩ : syracuseStep 2275609 = 1706707) (by norm_num)
theorem B3034145 : Blo 2021435 3034145 := bstep (se 2 (by rfl) ⟨1137804, by rfl⟩ : syracuseStep 3034145 = 2275609) B2275609
theorem B2022763 : Blo 2021435 2022763 := bstep (se 1 (by rfl) ⟨1517072, by rfl⟩ : syracuseStep 2022763 = 3034145) B3034145
theorem B7680197 : Blo 2021435 7680197 := bbase (se 4 (by rfl) ⟨720018, by rfl⟩ : syracuseStep 7680197 = 1440037) (by norm_num)
theorem B5120131 : Blo 2021435 5120131 := bstep (se 1 (by rfl) ⟨3840098, by rfl⟩ : syracuseStep 5120131 = 7680197) B7680197
theorem B6826841 : Blo 2021435 6826841 := bstep (se 2 (by rfl) ⟨2560065, by rfl⟩ : syracuseStep 6826841 = 5120131) B5120131
theorem B4551227 : Blo 2021435 4551227 := bstep (se 1 (by rfl) ⟨3413420, by rfl⟩ : syracuseStep 4551227 = 6826841) B6826841
theorem B3034151 : Blo 2021435 3034151 := bstep (se 1 (by rfl) ⟨2275613, by rfl⟩ : syracuseStep 3034151 = 4551227) B4551227
theorem B2022767 : Blo 2021435 2022767 := bstep (se 1 (by rfl) ⟨1517075, by rfl⟩ : syracuseStep 2022767 = 3034151) B3034151
theorem B3034157 : Blo 2021435 3034157 := bbase (se 3 (by rfl) ⟨568904, by rfl⟩ : syracuseStep 3034157 = 1137809) (by norm_num)
theorem B2022771 : Blo 2021435 2022771 := bstep (se 1 (by rfl) ⟨1517078, by rfl⟩ : syracuseStep 2022771 = 3034157) B3034157
theorem B4551245 : Blo 2021435 4551245 := bbase (se 3 (by rfl) ⟨853358, by rfl⟩ : syracuseStep 4551245 = 1706717) (by norm_num)
theorem B3034163 : Blo 2021435 3034163 := bstep (se 1 (by rfl) ⟨2275622, by rfl⟩ : syracuseStep 3034163 = 4551245) B4551245
theorem B2022775 : Blo 2021435 2022775 := bstep (se 1 (by rfl) ⟨1517081, by rfl⟩ : syracuseStep 2022775 = 3034163) B3034163
theorem B2560081 : Blo 2021435 2560081 := bbase (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) (by norm_num)
theorem B3413441 : Blo 2021435 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2275627 : Blo 2021435 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B3034169 : Blo 2021435 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B2022779 : Blo 2021435 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B3240109 : Blo 2021435 3240109 := bbase (se 3 (by rfl) ⟨607520, by rfl⟩ : syracuseStep 3240109 = 1215041) (by norm_num)
theorem B4320145 : Blo 2021435 4320145 := bstep (se 2 (by rfl) ⟨1620054, by rfl⟩ : syracuseStep 4320145 = 3240109) B3240109
theorem B23040773 : Blo 2021435 23040773 := bstep (se 4 (by rfl) ⟨2160072, by rfl⟩ : syracuseStep 23040773 = 4320145) B4320145
theorem B15360515 : Blo 2021435 15360515 := bstep (se 1 (by rfl) ⟨11520386, by rfl⟩ : syracuseStep 15360515 = 23040773) B23040773
theorem B10240343 : Blo 2021435 10240343 := bstep (se 1 (by rfl) ⟨7680257, by rfl⟩ : syracuseStep 10240343 = 15360515) B15360515
theorem B6826895 : Blo 2021435 6826895 := bstep (se 1 (by rfl) ⟨5120171, by rfl⟩ : syracuseStep 6826895 = 10240343) B10240343
theorem B4551263 : Blo 2021435 4551263 := bstep (se 1 (by rfl) ⟨3413447, by rfl⟩ : syracuseStep 4551263 = 6826895) B6826895
theorem B3034175 : Blo 2021435 3034175 := bstep (se 1 (by rfl) ⟨2275631, by rfl⟩ : syracuseStep 3034175 = 4551263) B4551263
theorem B2022783 : Blo 2021435 2022783 := bstep (se 1 (by rfl) ⟨1517087, by rfl⟩ : syracuseStep 2022783 = 3034175) B3034175
theorem B3034181 : Blo 2021435 3034181 := bbase (se 4 (by rfl) ⟨284454, by rfl⟩ : syracuseStep 3034181 = 568909) (by norm_num)
theorem B2022787 : Blo 2021435 2022787 := bstep (se 1 (by rfl) ⟨1517090, by rfl⟩ : syracuseStep 2022787 = 3034181) B3034181
theorem B3413461 : Blo 2021435 3413461 := bbase (se 7 (by rfl) ⟨40001, by rfl⟩ : syracuseStep 3413461 = 80003) (by norm_num)
theorem B4551281 : Blo 2021435 4551281 := bstep (se 2 (by rfl) ⟨1706730, by rfl⟩ : syracuseStep 4551281 = 3413461) B3413461
theorem B3034187 : Blo 2021435 3034187 := bstep (se 1 (by rfl) ⟨2275640, by rfl⟩ : syracuseStep 3034187 = 4551281) B4551281
theorem B2022791 : Blo 2021435 2022791 := bstep (se 1 (by rfl) ⟨1517093, by rfl⟩ : syracuseStep 2022791 = 3034187) B3034187
theorem B2275645 : Blo 2021435 2275645 := bbase (se 3 (by rfl) ⟨426683, by rfl⟩ : syracuseStep 2275645 = 853367) (by norm_num)
theorem B3034193 : Blo 2021435 3034193 := bstep (se 2 (by rfl) ⟨1137822, by rfl⟩ : syracuseStep 3034193 = 2275645) B2275645
theorem B2022795 : Blo 2021435 2022795 := bstep (se 1 (by rfl) ⟨1517096, by rfl⟩ : syracuseStep 2022795 = 3034193) B3034193
theorem B6826949 : Blo 2021435 6826949 := bbase (se 4 (by rfl) ⟨640026, by rfl⟩ : syracuseStep 6826949 = 1280053) (by norm_num)
theorem B4551299 : Blo 2021435 4551299 := bstep (se 1 (by rfl) ⟨3413474, by rfl⟩ : syracuseStep 4551299 = 6826949) B6826949
theorem B3034199 : Blo 2021435 3034199 := bstep (se 1 (by rfl) ⟨2275649, by rfl⟩ : syracuseStep 3034199 = 4551299) B4551299
theorem B2022799 : Blo 2021435 2022799 := bstep (se 1 (by rfl) ⟨1517099, by rfl⟩ : syracuseStep 2022799 = 3034199) B3034199
theorem B3034205 : Blo 2021435 3034205 := bbase (se 3 (by rfl) ⟨568913, by rfl⟩ : syracuseStep 3034205 = 1137827) (by norm_num)
theorem B2022803 : Blo 2021435 2022803 := bstep (se 1 (by rfl) ⟨1517102, by rfl⟩ : syracuseStep 2022803 = 3034205) B3034205
theorem B4551317 : Blo 2021435 4551317 := bbase (se 6 (by rfl) ⟨106671, by rfl⟩ : syracuseStep 4551317 = 213343) (by norm_num)
theorem B3034211 : Blo 2021435 3034211 := bstep (se 1 (by rfl) ⟨2275658, by rfl⟩ : syracuseStep 3034211 = 4551317) B4551317
theorem B2022807 : Blo 2021435 2022807 := bstep (se 1 (by rfl) ⟨1517105, by rfl⟩ : syracuseStep 2022807 = 3034211) B3034211
theorem B2306713 : Blo 2021435 2306713 := bbase (se 2 (by rfl) ⟨865017, by rfl⟩ : syracuseStep 2306713 = 1730035) (by norm_num)
theorem B3075617 : Blo 2021435 3075617 := bstep (se 2 (by rfl) ⟨1153356, by rfl⟩ : syracuseStep 3075617 = 2306713) B2306713
theorem B8201645 : Blo 2021435 8201645 := bstep (se 3 (by rfl) ⟨1537808, by rfl⟩ : syracuseStep 8201645 = 3075617) B3075617
theorem B5467763 : Blo 2021435 5467763 := bstep (se 1 (by rfl) ⟨4100822, by rfl⟩ : syracuseStep 5467763 = 8201645) B8201645
theorem B3645175 : Blo 2021435 3645175 := bstep (se 1 (by rfl) ⟨2733881, by rfl⟩ : syracuseStep 3645175 = 5467763) B5467763
theorem B4860233 : Blo 2021435 4860233 := bstep (se 2 (by rfl) ⟨1822587, by rfl⟩ : syracuseStep 4860233 = 3645175) B3645175
theorem B3240155 : Blo 2021435 3240155 := bstep (se 1 (by rfl) ⟨2430116, by rfl⟩ : syracuseStep 3240155 = 4860233) B4860233
theorem B2160103 : Blo 2021435 2160103 := bstep (se 1 (by rfl) ⟨1620077, by rfl⟩ : syracuseStep 2160103 = 3240155) B3240155
theorem B2880137 : Blo 2021435 2880137 := bstep (se 2 (by rfl) ⟨1080051, by rfl⟩ : syracuseStep 2880137 = 2160103) B2160103
theorem B7680365 : Blo 2021435 7680365 := bstep (se 3 (by rfl) ⟨1440068, by rfl⟩ : syracuseStep 7680365 = 2880137) B2880137
theorem B5120243 : Blo 2021435 5120243 := bstep (se 1 (by rfl) ⟨3840182, by rfl⟩ : syracuseStep 5120243 = 7680365) B7680365
theorem B3413495 : Blo 2021435 3413495 := bstep (se 1 (by rfl) ⟨2560121, by rfl⟩ : syracuseStep 3413495 = 5120243) B5120243
theorem B2275663 : Blo 2021435 2275663 := bstep (se 1 (by rfl) ⟨1706747, by rfl⟩ : syracuseStep 2275663 = 3413495) B3413495
theorem B3034217 : Blo 2021435 3034217 := bstep (se 2 (by rfl) ⟨1137831, by rfl⟩ : syracuseStep 3034217 = 2275663) B2275663
theorem B2022811 : Blo 2021435 2022811 := bstep (se 1 (by rfl) ⟨1517108, by rfl⟩ : syracuseStep 2022811 = 3034217) B3034217
theorem B6920149 : Blo 2021435 6920149 := bbase (se 7 (by rfl) ⟨81095, by rfl⟩ : syracuseStep 6920149 = 162191) (by norm_num)
theorem B9226865 : Blo 2021435 9226865 := bstep (se 2 (by rfl) ⟨3460074, by rfl⟩ : syracuseStep 9226865 = 6920149) B6920149
theorem B6151243 : Blo 2021435 6151243 := bstep (se 1 (by rfl) ⟨4613432, by rfl⟩ : syracuseStep 6151243 = 9226865) B9226865
theorem B8201657 : Blo 2021435 8201657 := bstep (se 2 (by rfl) ⟨3075621, by rfl⟩ : syracuseStep 8201657 = 6151243) B6151243
theorem B5467771 : Blo 2021435 5467771 := bstep (se 1 (by rfl) ⟨4100828, by rfl⟩ : syracuseStep 5467771 = 8201657) B8201657
theorem B7290361 : Blo 2021435 7290361 := bstep (se 2 (by rfl) ⟨2733885, by rfl⟩ : syracuseStep 7290361 = 5467771) B5467771
theorem B9720481 : Blo 2021435 9720481 := bstep (se 2 (by rfl) ⟨3645180, by rfl⟩ : syracuseStep 9720481 = 7290361) B7290361
theorem B12960641 : Blo 2021435 12960641 := bstep (se 2 (by rfl) ⟨4860240, by rfl⟩ : syracuseStep 12960641 = 9720481) B9720481
theorem B8640427 : Blo 2021435 8640427 := bstep (se 1 (by rfl) ⟨6480320, by rfl⟩ : syracuseStep 8640427 = 12960641) B12960641
theorem B11520569 : Blo 2021435 11520569 := bstep (se 2 (by rfl) ⟨4320213, by rfl⟩ : syracuseStep 11520569 = 8640427) B8640427
theorem B7680379 : Blo 2021435 7680379 := bstep (se 1 (by rfl) ⟨5760284, by rfl⟩ : syracuseStep 7680379 = 11520569) B11520569
theorem B10240505 : Blo 2021435 10240505 := bstep (se 2 (by rfl) ⟨3840189, by rfl⟩ : syracuseStep 10240505 = 7680379) B7680379
theorem B6827003 : Blo 2021435 6827003 := bstep (se 1 (by rfl) ⟨5120252, by rfl⟩ : syracuseStep 6827003 = 10240505) B10240505
theorem B4551335 : Blo 2021435 4551335 := bstep (se 1 (by rfl) ⟨3413501, by rfl⟩ : syracuseStep 4551335 = 6827003) B6827003
theorem B3034223 : Blo 2021435 3034223 := bstep (se 1 (by rfl) ⟨2275667, by rfl⟩ : syracuseStep 3034223 = 4551335) B4551335
theorem B2022815 : Blo 2021435 2022815 := bstep (se 1 (by rfl) ⟨1517111, by rfl⟩ : syracuseStep 2022815 = 3034223) B3034223
theorem B3034229 : Blo 2021435 3034229 := bbase (se 5 (by rfl) ⟨142229, by rfl⟩ : syracuseStep 3034229 = 284459) (by norm_num)
theorem B2022819 : Blo 2021435 2022819 := bstep (se 1 (by rfl) ⟨1517114, by rfl⟩ : syracuseStep 2022819 = 3034229) B3034229
theorem B3840205 : Blo 2021435 3840205 := bbase (se 3 (by rfl) ⟨720038, by rfl⟩ : syracuseStep 3840205 = 1440077) (by norm_num)
theorem B5120273 : Blo 2021435 5120273 := bstep (se 2 (by rfl) ⟨1920102, by rfl⟩ : syracuseStep 5120273 = 3840205) B3840205
theorem B3413515 : Blo 2021435 3413515 := bstep (se 1 (by rfl) ⟨2560136, by rfl⟩ : syracuseStep 3413515 = 5120273) B5120273
theorem B4551353 : Blo 2021435 4551353 := bstep (se 2 (by rfl) ⟨1706757, by rfl⟩ : syracuseStep 4551353 = 3413515) B3413515
theorem B3034235 : Blo 2021435 3034235 := bstep (se 1 (by rfl) ⟨2275676, by rfl⟩ : syracuseStep 3034235 = 4551353) B4551353
theorem B2022823 : Blo 2021435 2022823 := bstep (se 1 (by rfl) ⟨1517117, by rfl⟩ : syracuseStep 2022823 = 3034235) B3034235
theorem B2275681 : Blo 2021435 2275681 := bbase (se 2 (by rfl) ⟨853380, by rfl⟩ : syracuseStep 2275681 = 1706761) (by norm_num)
theorem B3034241 : Blo 2021435 3034241 := bstep (se 2 (by rfl) ⟨1137840, by rfl⟩ : syracuseStep 3034241 = 2275681) B2275681
theorem B2022827 : Blo 2021435 2022827 := bstep (se 1 (by rfl) ⟨1517120, by rfl⟩ : syracuseStep 2022827 = 3034241) B3034241
theorem B5120293 : Blo 2021435 5120293 := bbase (se 4 (by rfl) ⟨480027, by rfl⟩ : syracuseStep 5120293 = 960055) (by norm_num)
theorem B6827057 : Blo 2021435 6827057 := bstep (se 2 (by rfl) ⟨2560146, by rfl⟩ : syracuseStep 6827057 = 5120293) B5120293
theorem B4551371 : Blo 2021435 4551371 := bstep (se 1 (by rfl) ⟨3413528, by rfl⟩ : syracuseStep 4551371 = 6827057) B6827057
theorem B3034247 : Blo 2021435 3034247 := bstep (se 1 (by rfl) ⟨2275685, by rfl⟩ : syracuseStep 3034247 = 4551371) B4551371
theorem B2022831 : Blo 2021435 2022831 := bstep (se 1 (by rfl) ⟨1517123, by rfl⟩ : syracuseStep 2022831 = 3034247) B3034247
theorem B3034253 : Blo 2021435 3034253 := bbase (se 3 (by rfl) ⟨568922, by rfl⟩ : syracuseStep 3034253 = 1137845) (by norm_num)
theorem B2022835 : Blo 2021435 2022835 := bstep (se 1 (by rfl) ⟨1517126, by rfl⟩ : syracuseStep 2022835 = 3034253) B3034253
theorem B4551389 : Blo 2021435 4551389 := bbase (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) (by norm_num)
theorem B3034259 : Blo 2021435 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B2022839 : Blo 2021435 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B3413549 : Blo 2021435 3413549 := bbase (se 3 (by rfl) ⟨640040, by rfl⟩ : syracuseStep 3413549 = 1280081) (by norm_num)
theorem B2275699 : Blo 2021435 2275699 := bstep (se 1 (by rfl) ⟨1706774, by rfl⟩ : syracuseStep 2275699 = 3413549) B3413549
theorem B3034265 : Blo 2021435 3034265 := bstep (se 2 (by rfl) ⟨1137849, by rfl⟩ : syracuseStep 3034265 = 2275699) B2275699
theorem B2022843 : Blo 2021435 2022843 := bstep (se 1 (by rfl) ⟨1517132, by rfl⟩ : syracuseStep 2022843 = 3034265) B3034265
theorem B4926629 : Blo 2021435 4926629 := bbase (se 4 (by rfl) ⟨461871, by rfl⟩ : syracuseStep 4926629 = 923743) (by norm_num)
theorem B13137677 : Blo 2021435 13137677 := bstep (se 3 (by rfl) ⟨2463314, by rfl⟩ : syracuseStep 13137677 = 4926629) B4926629
theorem B8758451 : Blo 2021435 8758451 := bstep (se 1 (by rfl) ⟨6568838, by rfl⟩ : syracuseStep 8758451 = 13137677) B13137677
theorem B5838967 : Blo 2021435 5838967 := bstep (se 1 (by rfl) ⟨4379225, by rfl⟩ : syracuseStep 5838967 = 8758451) B8758451
theorem B7785289 : Blo 2021435 7785289 := bstep (se 2 (by rfl) ⟨2919483, by rfl⟩ : syracuseStep 7785289 = 5838967) B5838967
theorem B10380385 : Blo 2021435 10380385 := bstep (se 2 (by rfl) ⟨3892644, by rfl⟩ : syracuseStep 10380385 = 7785289) B7785289
theorem B13840513 : Blo 2021435 13840513 := bstep (se 2 (by rfl) ⟨5190192, by rfl⟩ : syracuseStep 13840513 = 10380385) B10380385
theorem B73816069 : Blo 2021435 73816069 := bstep (se 4 (by rfl) ⟨6920256, by rfl⟩ : syracuseStep 73816069 = 13840513) B13840513
theorem B98421425 : Blo 2021435 98421425 := bstep (se 2 (by rfl) ⟨36908034, by rfl⟩ : syracuseStep 98421425 = 73816069) B73816069
theorem B65614283 : Blo 2021435 65614283 := bstep (se 1 (by rfl) ⟨49210712, by rfl⟩ : syracuseStep 65614283 = 98421425) B98421425
theorem B43742855 : Blo 2021435 43742855 := bstep (se 1 (by rfl) ⟨32807141, by rfl⟩ : syracuseStep 43742855 = 65614283) B65614283
theorem B29161903 : Blo 2021435 29161903 := bstep (se 1 (by rfl) ⟨21871427, by rfl⟩ : syracuseStep 29161903 = 43742855) B43742855
theorem B38882537 : Blo 2021435 38882537 := bstep (se 2 (by rfl) ⟨14580951, by rfl⟩ : syracuseStep 38882537 = 29161903) B29161903
theorem B25921691 : Blo 2021435 25921691 := bstep (se 1 (by rfl) ⟨19441268, by rfl⟩ : syracuseStep 25921691 = 38882537) B38882537
theorem B17281127 : Blo 2021435 17281127 := bstep (se 1 (by rfl) ⟨12960845, by rfl⟩ : syracuseStep 17281127 = 25921691) B25921691
theorem B11520751 : Blo 2021435 11520751 := bstep (se 1 (by rfl) ⟨8640563, by rfl⟩ : syracuseStep 11520751 = 17281127) B17281127
theorem B15361001 : Blo 2021435 15361001 := bstep (se 2 (by rfl) ⟨5760375, by rfl⟩ : syracuseStep 15361001 = 11520751) B11520751
theorem B10240667 : Blo 2021435 10240667 := bstep (se 1 (by rfl) ⟨7680500, by rfl⟩ : syracuseStep 10240667 = 15361001) B15361001
theorem B6827111 : Blo 2021435 6827111 := bstep (se 1 (by rfl) ⟨5120333, by rfl⟩ : syracuseStep 6827111 = 10240667) B10240667
theorem B4551407 : Blo 2021435 4551407 := bstep (se 1 (by rfl) ⟨3413555, by rfl⟩ : syracuseStep 4551407 = 6827111) B6827111
theorem B3034271 : Blo 2021435 3034271 := bstep (se 1 (by rfl) ⟨2275703, by rfl⟩ : syracuseStep 3034271 = 4551407) B4551407
theorem B2022847 : Blo 2021435 2022847 := bstep (se 1 (by rfl) ⟨1517135, by rfl⟩ : syracuseStep 2022847 = 3034271) B3034271
theorem B3034277 : Blo 2021435 3034277 := bbase (se 4 (by rfl) ⟨284463, by rfl⟩ : syracuseStep 3034277 = 568927) (by norm_num)
theorem B2022851 : Blo 2021435 2022851 := bstep (se 1 (by rfl) ⟨1517138, by rfl⟩ : syracuseStep 2022851 = 3034277) B3034277
theorem B2560177 : Blo 2021435 2560177 := bbase (se 2 (by rfl) ⟨960066, by rfl⟩ : syracuseStep 2560177 = 1920133) (by norm_num)
theorem B3413569 : Blo 2021435 3413569 := bstep (se 2 (by rfl) ⟨1280088, by rfl⟩ : syracuseStep 3413569 = 2560177) B2560177
theorem B4551425 : Blo 2021435 4551425 := bstep (se 2 (by rfl) ⟨1706784, by rfl⟩ : syracuseStep 4551425 = 3413569) B3413569
theorem B3034283 : Blo 2021435 3034283 := bstep (se 1 (by rfl) ⟨2275712, by rfl⟩ : syracuseStep 3034283 = 4551425) B4551425
theorem B2022855 : Blo 2021435 2022855 := bstep (se 1 (by rfl) ⟨1517141, by rfl⟩ : syracuseStep 2022855 = 3034283) B3034283
theorem B2275717 : Blo 2021435 2275717 := bbase (se 4 (by rfl) ⟨213348, by rfl⟩ : syracuseStep 2275717 = 426697) (by norm_num)
theorem B3034289 : Blo 2021435 3034289 := bstep (se 2 (by rfl) ⟨1137858, by rfl⟩ : syracuseStep 3034289 = 2275717) B2275717
theorem B2022859 : Blo 2021435 2022859 := bstep (se 1 (by rfl) ⟨1517144, by rfl⟩ : syracuseStep 2022859 = 3034289) B3034289
theorem B4320317 : Blo 2021435 4320317 := bbase (se 3 (by rfl) ⟨810059, by rfl⟩ : syracuseStep 4320317 = 1620119) (by norm_num)
theorem B2880211 : Blo 2021435 2880211 := bstep (se 1 (by rfl) ⟨2160158, by rfl⟩ : syracuseStep 2880211 = 4320317) B4320317
theorem B3840281 : Blo 2021435 3840281 := bstep (se 2 (by rfl) ⟨1440105, by rfl⟩ : syracuseStep 3840281 = 2880211) B2880211
theorem B2560187 : Blo 2021435 2560187 := bstep (se 1 (by rfl) ⟨1920140, by rfl⟩ : syracuseStep 2560187 = 3840281) B3840281
theorem B6827165 : Blo 2021435 6827165 := bstep (se 3 (by rfl) ⟨1280093, by rfl⟩ : syracuseStep 6827165 = 2560187) B2560187
theorem B4551443 : Blo 2021435 4551443 := bstep (se 1 (by rfl) ⟨3413582, by rfl⟩ : syracuseStep 4551443 = 6827165) B6827165
theorem B3034295 : Blo 2021435 3034295 := bstep (se 1 (by rfl) ⟨2275721, by rfl⟩ : syracuseStep 3034295 = 4551443) B4551443
theorem B2022863 : Blo 2021435 2022863 := bstep (se 1 (by rfl) ⟨1517147, by rfl⟩ : syracuseStep 2022863 = 3034295) B3034295
theorem B3034301 : Blo 2021435 3034301 := bbase (se 3 (by rfl) ⟨568931, by rfl⟩ : syracuseStep 3034301 = 1137863) (by norm_num)
theorem B2022867 : Blo 2021435 2022867 := bstep (se 1 (by rfl) ⟨1517150, by rfl⟩ : syracuseStep 2022867 = 3034301) B3034301
theorem B4551461 : Blo 2021435 4551461 := bbase (se 4 (by rfl) ⟨426699, by rfl⟩ : syracuseStep 4551461 = 853399) (by norm_num)
theorem B3034307 : Blo 2021435 3034307 := bstep (se 1 (by rfl) ⟨2275730, by rfl⟩ : syracuseStep 3034307 = 4551461) B4551461
theorem B2022871 : Blo 2021435 2022871 := bstep (se 1 (by rfl) ⟨1517153, by rfl⟩ : syracuseStep 2022871 = 3034307) B3034307
theorem B5120405 : Blo 2021435 5120405 := bbase (se 6 (by rfl) ⟨120009, by rfl⟩ : syracuseStep 5120405 = 240019) (by norm_num)
theorem B3413603 : Blo 2021435 3413603 := bstep (se 1 (by rfl) ⟨2560202, by rfl⟩ : syracuseStep 3413603 = 5120405) B5120405
theorem B2275735 : Blo 2021435 2275735 := bstep (se 1 (by rfl) ⟨1706801, by rfl⟩ : syracuseStep 2275735 = 3413603) B3413603
theorem B3034313 : Blo 2021435 3034313 := bstep (se 2 (by rfl) ⟨1137867, by rfl⟩ : syracuseStep 3034313 = 2275735) B2275735
theorem B2022875 : Blo 2021435 2022875 := bstep (se 1 (by rfl) ⟨1517156, by rfl⟩ : syracuseStep 2022875 = 3034313) B3034313
theorem B20761109 : Blo 2021435 20761109 := bbase (se 6 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 20761109 = 973177) (by norm_num)
theorem B13840739 : Blo 2021435 13840739 := bstep (se 1 (by rfl) ⟨10380554, by rfl⟩ : syracuseStep 13840739 = 20761109) B20761109
theorem B9227159 : Blo 2021435 9227159 := bstep (se 1 (by rfl) ⟨6920369, by rfl⟩ : syracuseStep 9227159 = 13840739) B13840739
theorem B6151439 : Blo 2021435 6151439 := bstep (se 1 (by rfl) ⟨4613579, by rfl⟩ : syracuseStep 6151439 = 9227159) B9227159
theorem B4100959 : Blo 2021435 4100959 := bstep (se 1 (by rfl) ⟨3075719, by rfl⟩ : syracuseStep 4100959 = 6151439) B6151439
theorem B5467945 : Blo 2021435 5467945 := bstep (se 2 (by rfl) ⟨2050479, by rfl⟩ : syracuseStep 5467945 = 4100959) B4100959
theorem B7290593 : Blo 2021435 7290593 := bstep (se 2 (by rfl) ⟨2733972, by rfl⟩ : syracuseStep 7290593 = 5467945) B5467945
theorem B4860395 : Blo 2021435 4860395 := bstep (se 1 (by rfl) ⟨3645296, by rfl⟩ : syracuseStep 4860395 = 7290593) B7290593
theorem B3240263 : Blo 2021435 3240263 := bstep (se 1 (by rfl) ⟨2430197, by rfl⟩ : syracuseStep 3240263 = 4860395) B4860395
theorem B8640701 : Blo 2021435 8640701 := bstep (se 3 (by rfl) ⟨1620131, by rfl⟩ : syracuseStep 8640701 = 3240263) B3240263
theorem B5760467 : Blo 2021435 5760467 := bstep (se 1 (by rfl) ⟨4320350, by rfl⟩ : syracuseStep 5760467 = 8640701) B8640701
theorem B3840311 : Blo 2021435 3840311 := bstep (se 1 (by rfl) ⟨2880233, by rfl⟩ : syracuseStep 3840311 = 5760467) B5760467
theorem B10240829 : Blo 2021435 10240829 := bstep (se 3 (by rfl) ⟨1920155, by rfl⟩ : syracuseStep 10240829 = 3840311) B3840311
theorem B6827219 : Blo 2021435 6827219 := bstep (se 1 (by rfl) ⟨5120414, by rfl⟩ : syracuseStep 6827219 = 10240829) B10240829
theorem B4551479 : Blo 2021435 4551479 := bstep (se 1 (by rfl) ⟨3413609, by rfl⟩ : syracuseStep 4551479 = 6827219) B6827219
theorem B3034319 : Blo 2021435 3034319 := bstep (se 1 (by rfl) ⟨2275739, by rfl⟩ : syracuseStep 3034319 = 4551479) B4551479
theorem B2022879 : Blo 2021435 2022879 := bstep (se 1 (by rfl) ⟨1517159, by rfl⟩ : syracuseStep 2022879 = 3034319) B3034319
theorem B3034325 : Blo 2021435 3034325 := bbase (se 7 (by rfl) ⟨35558, by rfl⟩ : syracuseStep 3034325 = 71117) (by norm_num)
theorem B2022883 : Blo 2021435 2022883 := bstep (se 1 (by rfl) ⟨1517162, by rfl⟩ : syracuseStep 2022883 = 3034325) B3034325
theorem B2880245 : Blo 2021435 2880245 := bbase (se 5 (by rfl) ⟨135011, by rfl⟩ : syracuseStep 2880245 = 270023) (by norm_num)
theorem B7680653 : Blo 2021435 7680653 := bstep (se 3 (by rfl) ⟨1440122, by rfl⟩ : syracuseStep 7680653 = 2880245) B2880245
theorem B5120435 : Blo 2021435 5120435 := bstep (se 1 (by rfl) ⟨3840326, by rfl⟩ : syracuseStep 5120435 = 7680653) B7680653
theorem B3413623 : Blo 2021435 3413623 := bstep (se 1 (by rfl) ⟨2560217, by rfl⟩ : syracuseStep 3413623 = 5120435) B5120435
theorem B4551497 : Blo 2021435 4551497 := bstep (se 2 (by rfl) ⟨1706811, by rfl⟩ : syracuseStep 4551497 = 3413623) B3413623
theorem B3034331 : Blo 2021435 3034331 := bstep (se 1 (by rfl) ⟨2275748, by rfl⟩ : syracuseStep 3034331 = 4551497) B4551497
theorem B2022887 : Blo 2021435 2022887 := bstep (se 1 (by rfl) ⟨1517165, by rfl⟩ : syracuseStep 2022887 = 3034331) B3034331
theorem B2275753 : Blo 2021435 2275753 := bbase (se 2 (by rfl) ⟨853407, by rfl⟩ : syracuseStep 2275753 = 1706815) (by norm_num)
theorem B3034337 : Blo 2021435 3034337 := bstep (se 2 (by rfl) ⟨1137876, by rfl⟩ : syracuseStep 3034337 = 2275753) B2275753
theorem B2022891 : Blo 2021435 2022891 := bstep (se 1 (by rfl) ⟨1517168, by rfl⟩ : syracuseStep 2022891 = 3034337) B3034337
theorem B3645325 : Blo 2021435 3645325 := bbase (se 3 (by rfl) ⟨683498, by rfl⟩ : syracuseStep 3645325 = 1366997) (by norm_num)
theorem B4860433 : Blo 2021435 4860433 := bstep (se 2 (by rfl) ⟨1822662, by rfl⟩ : syracuseStep 4860433 = 3645325) B3645325
theorem B6480577 : Blo 2021435 6480577 := bstep (se 2 (by rfl) ⟨2430216, by rfl⟩ : syracuseStep 6480577 = 4860433) B4860433
theorem B8640769 : Blo 2021435 8640769 := bstep (se 2 (by rfl) ⟨3240288, by rfl⟩ : syracuseStep 8640769 = 6480577) B6480577
theorem B11521025 : Blo 2021435 11521025 := bstep (se 2 (by rfl) ⟨4320384, by rfl⟩ : syracuseStep 11521025 = 8640769) B8640769
theorem B7680683 : Blo 2021435 7680683 := bstep (se 1 (by rfl) ⟨5760512, by rfl⟩ : syracuseStep 7680683 = 11521025) B11521025
theorem B5120455 : Blo 2021435 5120455 := bstep (se 1 (by rfl) ⟨3840341, by rfl⟩ : syracuseStep 5120455 = 7680683) B7680683
theorem B6827273 : Blo 2021435 6827273 := bstep (se 2 (by rfl) ⟨2560227, by rfl⟩ : syracuseStep 6827273 = 5120455) B5120455
theorem B4551515 : Blo 2021435 4551515 := bstep (se 1 (by rfl) ⟨3413636, by rfl⟩ : syracuseStep 4551515 = 6827273) B6827273
theorem B3034343 : Blo 2021435 3034343 := bstep (se 1 (by rfl) ⟨2275757, by rfl⟩ : syracuseStep 3034343 = 4551515) B4551515
theorem B2022895 : Blo 2021435 2022895 := bstep (se 1 (by rfl) ⟨1517171, by rfl⟩ : syracuseStep 2022895 = 3034343) B3034343
theorem B3034349 : Blo 2021435 3034349 := bbase (se 3 (by rfl) ⟨568940, by rfl⟩ : syracuseStep 3034349 = 1137881) (by norm_num)
theorem B2022899 : Blo 2021435 2022899 := bstep (se 1 (by rfl) ⟨1517174, by rfl⟩ : syracuseStep 2022899 = 3034349) B3034349
theorem B4551533 : Blo 2021435 4551533 := bbase (se 3 (by rfl) ⟨853412, by rfl⟩ : syracuseStep 4551533 = 1706825) (by norm_num)
theorem B3034355 : Blo 2021435 3034355 := bstep (se 1 (by rfl) ⟨2275766, by rfl⟩ : syracuseStep 3034355 = 4551533) B4551533
theorem B2022903 : Blo 2021435 2022903 := bstep (se 1 (by rfl) ⟨1517177, by rfl⟩ : syracuseStep 2022903 = 3034355) B3034355
theorem B3840365 : Blo 2021435 3840365 := bbase (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) (by norm_num)
theorem B2560243 : Blo 2021435 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B3413657 : Blo 2021435 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B2275771 : Blo 2021435 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B3034361 : Blo 2021435 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B2022907 : Blo 2021435 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B4676597 : Blo 2021435 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B3117731 : Blo 2021435 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B8313949 : Blo 2021435 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B11085265 : Blo 2021435 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B59121413 : Blo 2021435 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B39414275 : Blo 2021435 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B26276183 : Blo 2021435 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B17517455 : Blo 2021435 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B11678303 : Blo 2021435 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B31142141 : Blo 2021435 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B20761427 : Blo 2021435 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B13840951 : Blo 2021435 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B18454601 : Blo 2021435 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B49212269 : Blo 2021435 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B32808179 : Blo 2021435 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B21872119 : Blo 2021435 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B29162825 : Blo 2021435 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B19441883 : Blo 2021435 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B51845021 : Blo 2021435 51845021 := bstep (se 3 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 51845021 = 19441883) B19441883
theorem B34563347 : Blo 2021435 34563347 := bstep (se 1 (by rfl) ⟨25922510, by rfl⟩ : syracuseStep 34563347 = 51845021) B51845021
theorem B23042231 : Blo 2021435 23042231 := bstep (se 1 (by rfl) ⟨17281673, by rfl⟩ : syracuseStep 23042231 = 34563347) B34563347
theorem B15361487 : Blo 2021435 15361487 := bstep (se 1 (by rfl) ⟨11521115, by rfl⟩ : syracuseStep 15361487 = 23042231) B23042231
theorem B10240991 : Blo 2021435 10240991 := bstep (se 1 (by rfl) ⟨7680743, by rfl⟩ : syracuseStep 10240991 = 15361487) B15361487
theorem B6827327 : Blo 2021435 6827327 := bstep (se 1 (by rfl) ⟨5120495, by rfl⟩ : syracuseStep 6827327 = 10240991) B10240991
theorem B4551551 : Blo 2021435 4551551 := bstep (se 1 (by rfl) ⟨3413663, by rfl⟩ : syracuseStep 4551551 = 6827327) B6827327
theorem B3034367 : Blo 2021435 3034367 := bstep (se 1 (by rfl) ⟨2275775, by rfl⟩ : syracuseStep 3034367 = 4551551) B4551551
theorem B2022911 : Blo 2021435 2022911 := bstep (se 1 (by rfl) ⟨1517183, by rfl⟩ : syracuseStep 2022911 = 3034367) B3034367
theorem B3034373 : Blo 2021435 3034373 := bbase (se 4 (by rfl) ⟨284472, by rfl⟩ : syracuseStep 3034373 = 568945) (by norm_num)
theorem B2022915 : Blo 2021435 2022915 := bstep (se 1 (by rfl) ⟨1517186, by rfl⟩ : syracuseStep 2022915 = 3034373) B3034373
theorem B3413677 : Blo 2021435 3413677 := bbase (se 3 (by rfl) ⟨640064, by rfl⟩ : syracuseStep 3413677 = 1280129) (by norm_num)
theorem B4551569 : Blo 2021435 4551569 := bstep (se 2 (by rfl) ⟨1706838, by rfl⟩ : syracuseStep 4551569 = 3413677) B3413677
theorem B3034379 : Blo 2021435 3034379 := bstep (se 1 (by rfl) ⟨2275784, by rfl⟩ : syracuseStep 3034379 = 4551569) B4551569
theorem B2022919 : Blo 2021435 2022919 := bstep (se 1 (by rfl) ⟨1517189, by rfl⟩ : syracuseStep 2022919 = 3034379) B3034379
theorem B2275789 : Blo 2021435 2275789 := bbase (se 3 (by rfl) ⟨426710, by rfl⟩ : syracuseStep 2275789 = 853421) (by norm_num)
theorem B3034385 : Blo 2021435 3034385 := bstep (se 2 (by rfl) ⟨1137894, by rfl⟩ : syracuseStep 3034385 = 2275789) B2275789
theorem B2022923 : Blo 2021435 2022923 := bstep (se 1 (by rfl) ⟨1517192, by rfl⟩ : syracuseStep 2022923 = 3034385) B3034385
theorem B6827381 : Blo 2021435 6827381 := bbase (se 5 (by rfl) ⟨320033, by rfl⟩ : syracuseStep 6827381 = 640067) (by norm_num)
theorem B4551587 : Blo 2021435 4551587 := bstep (se 1 (by rfl) ⟨3413690, by rfl⟩ : syracuseStep 4551587 = 6827381) B6827381
theorem B3034391 : Blo 2021435 3034391 := bstep (se 1 (by rfl) ⟨2275793, by rfl⟩ : syracuseStep 3034391 = 4551587) B4551587
theorem B2022927 : Blo 2021435 2022927 := bstep (se 1 (by rfl) ⟨1517195, by rfl⟩ : syracuseStep 2022927 = 3034391) B3034391
theorem B3034397 : Blo 2021435 3034397 := bbase (se 3 (by rfl) ⟨568949, by rfl⟩ : syracuseStep 3034397 = 1137899) (by norm_num)
theorem B2022931 : Blo 2021435 2022931 := bstep (se 1 (by rfl) ⟨1517198, by rfl⟩ : syracuseStep 2022931 = 3034397) B3034397
theorem B4551605 : Blo 2021435 4551605 := bbase (se 5 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 4551605 = 426713) (by norm_num)
theorem B3034403 : Blo 2021435 3034403 := bstep (se 1 (by rfl) ⟨2275802, by rfl⟩ : syracuseStep 3034403 = 4551605) B4551605
theorem B2022935 : Blo 2021435 2022935 := bstep (se 1 (by rfl) ⟨1517201, by rfl⟩ : syracuseStep 2022935 = 3034403) B3034403
theorem B6151621 : Blo 2021435 6151621 := bbase (se 4 (by rfl) ⟨576714, by rfl⟩ : syracuseStep 6151621 = 1153429) (by norm_num)
theorem B8202161 : Blo 2021435 8202161 := bstep (se 2 (by rfl) ⟨3075810, by rfl⟩ : syracuseStep 8202161 = 6151621) B6151621
theorem B21872429 : Blo 2021435 21872429 := bstep (se 3 (by rfl) ⟨4101080, by rfl⟩ : syracuseStep 21872429 = 8202161) B8202161
theorem B14581619 : Blo 2021435 14581619 := bstep (se 1 (by rfl) ⟨10936214, by rfl⟩ : syracuseStep 14581619 = 21872429) B21872429
theorem B9721079 : Blo 2021435 9721079 := bstep (se 1 (by rfl) ⟨7290809, by rfl⟩ : syracuseStep 9721079 = 14581619) B14581619
theorem B6480719 : Blo 2021435 6480719 := bstep (se 1 (by rfl) ⟨4860539, by rfl⟩ : syracuseStep 6480719 = 9721079) B9721079
theorem B4320479 : Blo 2021435 4320479 := bstep (se 1 (by rfl) ⟨3240359, by rfl⟩ : syracuseStep 4320479 = 6480719) B6480719
theorem B11521277 : Blo 2021435 11521277 := bstep (se 3 (by rfl) ⟨2160239, by rfl⟩ : syracuseStep 11521277 = 4320479) B4320479
theorem B7680851 : Blo 2021435 7680851 := bstep (se 1 (by rfl) ⟨5760638, by rfl⟩ : syracuseStep 7680851 = 11521277) B11521277
theorem B5120567 : Blo 2021435 5120567 := bstep (se 1 (by rfl) ⟨3840425, by rfl⟩ : syracuseStep 5120567 = 7680851) B7680851
theorem B3413711 : Blo 2021435 3413711 := bstep (se 1 (by rfl) ⟨2560283, by rfl⟩ : syracuseStep 3413711 = 5120567) B5120567
theorem B2275807 : Blo 2021435 2275807 := bstep (se 1 (by rfl) ⟨1706855, by rfl⟩ : syracuseStep 2275807 = 3413711) B3413711
theorem B3034409 : Blo 2021435 3034409 := bstep (se 2 (by rfl) ⟨1137903, by rfl⟩ : syracuseStep 3034409 = 2275807) B2275807
theorem B2022939 : Blo 2021435 2022939 := bstep (se 1 (by rfl) ⟨1517204, by rfl⟩ : syracuseStep 2022939 = 3034409) B3034409
theorem B3695149 : Blo 2021435 3695149 := bbase (se 3 (by rfl) ⟨692840, by rfl⟩ : syracuseStep 3695149 = 1385681) (by norm_num)
theorem B4926865 : Blo 2021435 4926865 := bstep (se 2 (by rfl) ⟨1847574, by rfl⟩ : syracuseStep 4926865 = 3695149) B3695149
theorem B6569153 : Blo 2021435 6569153 := bstep (se 2 (by rfl) ⟨2463432, by rfl⟩ : syracuseStep 6569153 = 4926865) B4926865
theorem B4379435 : Blo 2021435 4379435 := bstep (se 1 (by rfl) ⟨3284576, by rfl⟩ : syracuseStep 4379435 = 6569153) B6569153
theorem B2919623 : Blo 2021435 2919623 := bstep (se 1 (by rfl) ⟨2189717, by rfl⟩ : syracuseStep 2919623 = 4379435) B4379435
theorem B7785661 : Blo 2021435 7785661 := bstep (se 3 (by rfl) ⟨1459811, by rfl⟩ : syracuseStep 7785661 = 2919623) B2919623
theorem B10380881 : Blo 2021435 10380881 := bstep (se 2 (by rfl) ⟨3892830, by rfl⟩ : syracuseStep 10380881 = 7785661) B7785661
theorem B6920587 : Blo 2021435 6920587 := bstep (se 1 (by rfl) ⟨5190440, by rfl⟩ : syracuseStep 6920587 = 10380881) B10380881
theorem B9227449 : Blo 2021435 9227449 := bstep (se 2 (by rfl) ⟨3460293, by rfl⟩ : syracuseStep 9227449 = 6920587) B6920587
theorem B12303265 : Blo 2021435 12303265 := bstep (se 2 (by rfl) ⟨4613724, by rfl⟩ : syracuseStep 12303265 = 9227449) B9227449
theorem B16404353 : Blo 2021435 16404353 := bstep (se 2 (by rfl) ⟨6151632, by rfl⟩ : syracuseStep 16404353 = 12303265) B12303265
theorem B10936235 : Blo 2021435 10936235 := bstep (se 1 (by rfl) ⟨8202176, by rfl⟩ : syracuseStep 10936235 = 16404353) B16404353
theorem B7290823 : Blo 2021435 7290823 := bstep (se 1 (by rfl) ⟨5468117, by rfl⟩ : syracuseStep 7290823 = 10936235) B10936235
theorem B9721097 : Blo 2021435 9721097 := bstep (se 2 (by rfl) ⟨3645411, by rfl⟩ : syracuseStep 9721097 = 7290823) B7290823
theorem B6480731 : Blo 2021435 6480731 := bstep (se 1 (by rfl) ⟨4860548, by rfl⟩ : syracuseStep 6480731 = 9721097) B9721097
theorem B4320487 : Blo 2021435 4320487 := bstep (se 1 (by rfl) ⟨3240365, by rfl⟩ : syracuseStep 4320487 = 6480731) B6480731
theorem B5760649 : Blo 2021435 5760649 := bstep (se 2 (by rfl) ⟨2160243, by rfl⟩ : syracuseStep 5760649 = 4320487) B4320487
theorem B7680865 : Blo 2021435 7680865 := bstep (se 2 (by rfl) ⟨2880324, by rfl⟩ : syracuseStep 7680865 = 5760649) B5760649
theorem B10241153 : Blo 2021435 10241153 := bstep (se 2 (by rfl) ⟨3840432, by rfl⟩ : syracuseStep 10241153 = 7680865) B7680865
theorem B6827435 : Blo 2021435 6827435 := bstep (se 1 (by rfl) ⟨5120576, by rfl⟩ : syracuseStep 6827435 = 10241153) B10241153
theorem B4551623 : Blo 2021435 4551623 := bstep (se 1 (by rfl) ⟨3413717, by rfl⟩ : syracuseStep 4551623 = 6827435) B6827435
theorem B3034415 : Blo 2021435 3034415 := bstep (se 1 (by rfl) ⟨2275811, by rfl⟩ : syracuseStep 3034415 = 4551623) B4551623
theorem B2022943 : Blo 2021435 2022943 := bstep (se 1 (by rfl) ⟨1517207, by rfl⟩ : syracuseStep 2022943 = 3034415) B3034415
theorem B3034421 : Blo 2021435 3034421 := bbase (se 5 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 3034421 = 284477) (by norm_num)
theorem B2022947 : Blo 2021435 2022947 := bstep (se 1 (by rfl) ⟨1517210, by rfl⟩ : syracuseStep 2022947 = 3034421) B3034421
theorem B5120597 : Blo 2021435 5120597 := bbase (se 8 (by rfl) ⟨30003, by rfl⟩ : syracuseStep 5120597 = 60007) (by norm_num)
theorem B3413731 : Blo 2021435 3413731 := bstep (se 1 (by rfl) ⟨2560298, by rfl⟩ : syracuseStep 3413731 = 5120597) B5120597
theorem B4551641 : Blo 2021435 4551641 := bstep (se 2 (by rfl) ⟨1706865, by rfl⟩ : syracuseStep 4551641 = 3413731) B3413731
theorem B3034427 : Blo 2021435 3034427 := bstep (se 1 (by rfl) ⟨2275820, by rfl⟩ : syracuseStep 3034427 = 4551641) B4551641
theorem B2022951 : Blo 2021435 2022951 := bstep (se 1 (by rfl) ⟨1517213, by rfl⟩ : syracuseStep 2022951 = 3034427) B3034427
theorem B2275825 : Blo 2021435 2275825 := bbase (se 2 (by rfl) ⟨853434, by rfl⟩ : syracuseStep 2275825 = 1706869) (by norm_num)
theorem B3034433 : Blo 2021435 3034433 := bstep (se 2 (by rfl) ⟨1137912, by rfl⟩ : syracuseStep 3034433 = 2275825) B2275825
theorem B2022955 : Blo 2021435 2022955 := bstep (se 1 (by rfl) ⟨1517216, by rfl⟩ : syracuseStep 2022955 = 3034433) B3034433
theorem B2306881 : Blo 2021435 2306881 := bbase (se 2 (by rfl) ⟨865080, by rfl⟩ : syracuseStep 2306881 = 1730161) (by norm_num)
theorem B3075841 : Blo 2021435 3075841 := bstep (se 2 (by rfl) ⟨1153440, by rfl⟩ : syracuseStep 3075841 = 2306881) B2306881
theorem B4101121 : Blo 2021435 4101121 := bstep (se 2 (by rfl) ⟨1537920, by rfl⟩ : syracuseStep 4101121 = 3075841) B3075841
theorem B5468161 : Blo 2021435 5468161 := bstep (se 2 (by rfl) ⟨2050560, by rfl⟩ : syracuseStep 5468161 = 4101121) B4101121
theorem B7290881 : Blo 2021435 7290881 := bstep (se 2 (by rfl) ⟨2734080, by rfl⟩ : syracuseStep 7290881 = 5468161) B5468161
theorem B4860587 : Blo 2021435 4860587 := bstep (se 1 (by rfl) ⟨3645440, by rfl⟩ : syracuseStep 4860587 = 7290881) B7290881
theorem B12961565 : Blo 2021435 12961565 := bstep (se 3 (by rfl) ⟨2430293, by rfl⟩ : syracuseStep 12961565 = 4860587) B4860587
theorem B8641043 : Blo 2021435 8641043 := bstep (se 1 (by rfl) ⟨6480782, by rfl⟩ : syracuseStep 8641043 = 12961565) B12961565
theorem B5760695 : Blo 2021435 5760695 := bstep (se 1 (by rfl) ⟨4320521, by rfl⟩ : syracuseStep 5760695 = 8641043) B8641043
theorem B3840463 : Blo 2021435 3840463 := bstep (se 1 (by rfl) ⟨2880347, by rfl⟩ : syracuseStep 3840463 = 5760695) B5760695
theorem B5120617 : Blo 2021435 5120617 := bstep (se 2 (by rfl) ⟨1920231, by rfl⟩ : syracuseStep 5120617 = 3840463) B3840463
theorem B6827489 : Blo 2021435 6827489 := bstep (se 2 (by rfl) ⟨2560308, by rfl⟩ : syracuseStep 6827489 = 5120617) B5120617
theorem B4551659 : Blo 2021435 4551659 := bstep (se 1 (by rfl) ⟨3413744, by rfl⟩ : syracuseStep 4551659 = 6827489) B6827489
theorem B3034439 : Blo 2021435 3034439 := bstep (se 1 (by rfl) ⟨2275829, by rfl⟩ : syracuseStep 3034439 = 4551659) B4551659
theorem B2022959 : Blo 2021435 2022959 := bstep (se 1 (by rfl) ⟨1517219, by rfl⟩ : syracuseStep 2022959 = 3034439) B3034439
theorem B3034445 : Blo 2021435 3034445 := bbase (se 3 (by rfl) ⟨568958, by rfl⟩ : syracuseStep 3034445 = 1137917) (by norm_num)
theorem B2022963 : Blo 2021435 2022963 := bstep (se 1 (by rfl) ⟨1517222, by rfl⟩ : syracuseStep 2022963 = 3034445) B3034445
theorem B4551677 : Blo 2021435 4551677 := bbase (se 3 (by rfl) ⟨853439, by rfl⟩ : syracuseStep 4551677 = 1706879) (by norm_num)
theorem B3034451 : Blo 2021435 3034451 := bstep (se 1 (by rfl) ⟨2275838, by rfl⟩ : syracuseStep 3034451 = 4551677) B4551677
theorem B2022967 : Blo 2021435 2022967 := bstep (se 1 (by rfl) ⟨1517225, by rfl⟩ : syracuseStep 2022967 = 3034451) B3034451
theorem B3413765 : Blo 2021435 3413765 := bbase (se 4 (by rfl) ⟨320040, by rfl⟩ : syracuseStep 3413765 = 640081) (by norm_num)
theorem B2275843 : Blo 2021435 2275843 := bstep (se 1 (by rfl) ⟨1706882, by rfl⟩ : syracuseStep 2275843 = 3413765) B3413765
theorem B3034457 : Blo 2021435 3034457 := bstep (se 2 (by rfl) ⟨1137921, by rfl⟩ : syracuseStep 3034457 = 2275843) B2275843
theorem B2022971 : Blo 2021435 2022971 := bstep (se 1 (by rfl) ⟨1517228, by rfl⟩ : syracuseStep 2022971 = 3034457) B3034457
theorem B15361973 : Blo 2021435 15361973 := bbase (se 5 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 15361973 = 1440185) (by norm_num)
theorem B10241315 : Blo 2021435 10241315 := bstep (se 1 (by rfl) ⟨7680986, by rfl⟩ : syracuseStep 10241315 = 15361973) B15361973
theorem B6827543 : Blo 2021435 6827543 := bstep (se 1 (by rfl) ⟨5120657, by rfl⟩ : syracuseStep 6827543 = 10241315) B10241315
theorem B4551695 : Blo 2021435 4551695 := bstep (se 1 (by rfl) ⟨3413771, by rfl⟩ : syracuseStep 4551695 = 6827543) B6827543
theorem B3034463 : Blo 2021435 3034463 := bstep (se 1 (by rfl) ⟨2275847, by rfl⟩ : syracuseStep 3034463 = 4551695) B4551695
theorem B2022975 : Blo 2021435 2022975 := bstep (se 1 (by rfl) ⟨1517231, by rfl⟩ : syracuseStep 2022975 = 3034463) B3034463
theorem B3034469 : Blo 2021435 3034469 := bbase (se 4 (by rfl) ⟨284481, by rfl⟩ : syracuseStep 3034469 = 568963) (by norm_num)
theorem B2022979 : Blo 2021435 2022979 := bstep (se 1 (by rfl) ⟨1517234, by rfl⟩ : syracuseStep 2022979 = 3034469) B3034469
theorem B3840509 : Blo 2021435 3840509 := bbase (se 3 (by rfl) ⟨720095, by rfl⟩ : syracuseStep 3840509 = 1440191) (by norm_num)
theorem B2560339 : Blo 2021435 2560339 := bstep (se 1 (by rfl) ⟨1920254, by rfl⟩ : syracuseStep 2560339 = 3840509) B3840509
theorem B3413785 : Blo 2021435 3413785 := bstep (se 2 (by rfl) ⟨1280169, by rfl⟩ : syracuseStep 3413785 = 2560339) B2560339
theorem B4551713 : Blo 2021435 4551713 := bstep (se 2 (by rfl) ⟨1706892, by rfl⟩ : syracuseStep 4551713 = 3413785) B3413785
theorem B3034475 : Blo 2021435 3034475 := bstep (se 1 (by rfl) ⟨2275856, by rfl⟩ : syracuseStep 3034475 = 4551713) B4551713
theorem B2022983 : Blo 2021435 2022983 := bstep (se 1 (by rfl) ⟨1517237, by rfl⟩ : syracuseStep 2022983 = 3034475) B3034475
theorem B2275861 : Blo 2021435 2275861 := bbase (se 6 (by rfl) ⟨53340, by rfl⟩ : syracuseStep 2275861 = 106681) (by norm_num)
theorem B3034481 : Blo 2021435 3034481 := bstep (se 2 (by rfl) ⟨1137930, by rfl⟩ : syracuseStep 3034481 = 2275861) B2275861
theorem B2022987 : Blo 2021435 2022987 := bstep (se 1 (by rfl) ⟨1517240, by rfl⟩ : syracuseStep 2022987 = 3034481) B3034481
theorem B2560349 : Blo 2021435 2560349 := bbase (se 3 (by rfl) ⟨480065, by rfl⟩ : syracuseStep 2560349 = 960131) (by norm_num)
theorem B6827597 : Blo 2021435 6827597 := bstep (se 3 (by rfl) ⟨1280174, by rfl⟩ : syracuseStep 6827597 = 2560349) B2560349
theorem B4551731 : Blo 2021435 4551731 := bstep (se 1 (by rfl) ⟨3413798, by rfl⟩ : syracuseStep 4551731 = 6827597) B6827597
theorem B3034487 : Blo 2021435 3034487 := bstep (se 1 (by rfl) ⟨2275865, by rfl⟩ : syracuseStep 3034487 = 4551731) B4551731
theorem B2022991 : Blo 2021435 2022991 := bstep (se 1 (by rfl) ⟨1517243, by rfl⟩ : syracuseStep 2022991 = 3034487) B3034487
theorem B3034493 : Blo 2021435 3034493 := bbase (se 3 (by rfl) ⟨568967, by rfl⟩ : syracuseStep 3034493 = 1137935) (by norm_num)
theorem B2022995 : Blo 2021435 2022995 := bstep (se 1 (by rfl) ⟨1517246, by rfl⟩ : syracuseStep 2022995 = 3034493) B3034493
theorem B4551749 : Blo 2021435 4551749 := bbase (se 4 (by rfl) ⟨426726, by rfl⟩ : syracuseStep 4551749 = 853453) (by norm_num)
theorem B3034499 : Blo 2021435 3034499 := bstep (se 1 (by rfl) ⟨2275874, by rfl⟩ : syracuseStep 3034499 = 4551749) B4551749
theorem B2022999 : Blo 2021435 2022999 := bstep (se 1 (by rfl) ⟨1517249, by rfl⟩ : syracuseStep 2022999 = 3034499) B3034499
theorem B5760821 : Blo 2021435 5760821 := bbase (se 5 (by rfl) ⟨270038, by rfl⟩ : syracuseStep 5760821 = 540077) (by norm_num)
theorem B3840547 : Blo 2021435 3840547 := bstep (se 1 (by rfl) ⟨2880410, by rfl⟩ : syracuseStep 3840547 = 5760821) B5760821
theorem B5120729 : Blo 2021435 5120729 := bstep (se 2 (by rfl) ⟨1920273, by rfl⟩ : syracuseStep 5120729 = 3840547) B3840547
theorem B3413819 : Blo 2021435 3413819 := bstep (se 1 (by rfl) ⟨2560364, by rfl⟩ : syracuseStep 3413819 = 5120729) B5120729
theorem B2275879 : Blo 2021435 2275879 := bstep (se 1 (by rfl) ⟨1706909, by rfl⟩ : syracuseStep 2275879 = 3413819) B3413819
theorem B3034505 : Blo 2021435 3034505 := bstep (se 2 (by rfl) ⟨1137939, by rfl⟩ : syracuseStep 3034505 = 2275879) B2275879
theorem B2023003 : Blo 2021435 2023003 := bstep (se 1 (by rfl) ⟨1517252, by rfl⟩ : syracuseStep 2023003 = 3034505) B3034505
theorem B10241477 : Blo 2021435 10241477 := bbase (se 4 (by rfl) ⟨960138, by rfl⟩ : syracuseStep 10241477 = 1920277) (by norm_num)
theorem B6827651 : Blo 2021435 6827651 := bstep (se 1 (by rfl) ⟨5120738, by rfl⟩ : syracuseStep 6827651 = 10241477) B10241477
theorem B4551767 : Blo 2021435 4551767 := bstep (se 1 (by rfl) ⟨3413825, by rfl⟩ : syracuseStep 4551767 = 6827651) B6827651
theorem B3034511 : Blo 2021435 3034511 := bstep (se 1 (by rfl) ⟨2275883, by rfl⟩ : syracuseStep 3034511 = 4551767) B4551767
theorem B2023007 : Blo 2021435 2023007 := bstep (se 1 (by rfl) ⟨1517255, by rfl⟩ : syracuseStep 2023007 = 3034511) B3034511
theorem B3034517 : Blo 2021435 3034517 := bbase (se 6 (by rfl) ⟨71121, by rfl⟩ : syracuseStep 3034517 = 142243) (by norm_num)
theorem B2023011 : Blo 2021435 2023011 := bstep (se 1 (by rfl) ⟨1517258, by rfl⟩ : syracuseStep 2023011 = 3034517) B3034517
theorem B2430361 : Blo 2021435 2430361 := bbase (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) (by norm_num)
theorem B3240481 : Blo 2021435 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B4320641 : Blo 2021435 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B11521709 : Blo 2021435 11521709 := bstep (se 3 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 11521709 = 4320641) B4320641
theorem B7681139 : Blo 2021435 7681139 := bstep (se 1 (by rfl) ⟨5760854, by rfl⟩ : syracuseStep 7681139 = 11521709) B11521709
theorem B5120759 : Blo 2021435 5120759 := bstep (se 1 (by rfl) ⟨3840569, by rfl⟩ : syracuseStep 5120759 = 7681139) B7681139
theorem B3413839 : Blo 2021435 3413839 := bstep (se 1 (by rfl) ⟨2560379, by rfl⟩ : syracuseStep 3413839 = 5120759) B5120759
theorem B4551785 : Blo 2021435 4551785 := bstep (se 2 (by rfl) ⟨1706919, by rfl⟩ : syracuseStep 4551785 = 3413839) B3413839
theorem B3034523 : Blo 2021435 3034523 := bstep (se 1 (by rfl) ⟨2275892, by rfl⟩ : syracuseStep 3034523 = 4551785) B4551785
theorem B2023015 : Blo 2021435 2023015 := bstep (se 1 (by rfl) ⟨1517261, by rfl⟩ : syracuseStep 2023015 = 3034523) B3034523
theorem B2275897 : Blo 2021435 2275897 := bbase (se 2 (by rfl) ⟨853461, by rfl⟩ : syracuseStep 2275897 = 1706923) (by norm_num)
theorem B3034529 : Blo 2021435 3034529 := bstep (se 2 (by rfl) ⟨1137948, by rfl⟩ : syracuseStep 3034529 = 2275897) B2275897
theorem B2023019 : Blo 2021435 2023019 := bstep (se 1 (by rfl) ⟨1517264, by rfl⟩ : syracuseStep 2023019 = 3034529) B3034529
theorem B2160329 : Blo 2021435 2160329 := bbase (se 2 (by rfl) ⟨810123, by rfl⟩ : syracuseStep 2160329 = 1620247) (by norm_num)
theorem B5760877 : Blo 2021435 5760877 := bstep (se 3 (by rfl) ⟨1080164, by rfl⟩ : syracuseStep 5760877 = 2160329) B2160329
theorem B7681169 : Blo 2021435 7681169 := bstep (se 2 (by rfl) ⟨2880438, by rfl⟩ : syracuseStep 7681169 = 5760877) B5760877
theorem B5120779 : Blo 2021435 5120779 := bstep (se 1 (by rfl) ⟨3840584, by rfl⟩ : syracuseStep 5120779 = 7681169) B7681169
theorem B6827705 : Blo 2021435 6827705 := bstep (se 2 (by rfl) ⟨2560389, by rfl⟩ : syracuseStep 6827705 = 5120779) B5120779
theorem B4551803 : Blo 2021435 4551803 := bstep (se 1 (by rfl) ⟨3413852, by rfl⟩ : syracuseStep 4551803 = 6827705) B6827705
theorem B3034535 : Blo 2021435 3034535 := bstep (se 1 (by rfl) ⟨2275901, by rfl⟩ : syracuseStep 3034535 = 4551803) B4551803
theorem B2023023 : Blo 2021435 2023023 := bstep (se 1 (by rfl) ⟨1517267, by rfl⟩ : syracuseStep 2023023 = 3034535) B3034535
theorem B3034541 : Blo 2021435 3034541 := bbase (se 3 (by rfl) ⟨568976, by rfl⟩ : syracuseStep 3034541 = 1137953) (by norm_num)
theorem B2023027 : Blo 2021435 2023027 := bstep (se 1 (by rfl) ⟨1517270, by rfl⟩ : syracuseStep 2023027 = 3034541) B3034541
theorem B4551821 : Blo 2021435 4551821 := bbase (se 3 (by rfl) ⟨853466, by rfl⟩ : syracuseStep 4551821 = 1706933) (by norm_num)
theorem B3034547 : Blo 2021435 3034547 := bstep (se 1 (by rfl) ⟨2275910, by rfl⟩ : syracuseStep 3034547 = 4551821) B4551821
theorem B2023031 : Blo 2021435 2023031 := bstep (se 1 (by rfl) ⟨1517273, by rfl⟩ : syracuseStep 2023031 = 3034547) B3034547
theorem B2560405 : Blo 2021435 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B3413873 : Blo 2021435 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B2275915 : Blo 2021435 2275915 := bstep (se 1 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 2275915 = 3413873) B3413873
theorem B3034553 : Blo 2021435 3034553 := bstep (se 2 (by rfl) ⟨1137957, by rfl⟩ : syracuseStep 3034553 = 2275915) B2275915
theorem B2023035 : Blo 2021435 2023035 := bstep (se 1 (by rfl) ⟨1517276, by rfl⟩ : syracuseStep 2023035 = 3034553) B3034553
theorem B5190685 : Blo 2021435 5190685 := bbase (se 3 (by rfl) ⟨973253, by rfl⟩ : syracuseStep 5190685 = 1946507) (by norm_num)
theorem B110734613 : Blo 2021435 110734613 := bstep (se 6 (by rfl) ⟨2595342, by rfl⟩ : syracuseStep 110734613 = 5190685) B5190685
theorem B73823075 : Blo 2021435 73823075 := bstep (se 1 (by rfl) ⟨55367306, by rfl⟩ : syracuseStep 73823075 = 110734613) B110734613
theorem B49215383 : Blo 2021435 49215383 := bstep (se 1 (by rfl) ⟨36911537, by rfl⟩ : syracuseStep 49215383 = 73823075) B73823075
theorem B32810255 : Blo 2021435 32810255 := bstep (se 1 (by rfl) ⟨24607691, by rfl⟩ : syracuseStep 32810255 = 49215383) B49215383
theorem B21873503 : Blo 2021435 21873503 := bstep (se 1 (by rfl) ⟨16405127, by rfl⟩ : syracuseStep 21873503 = 32810255) B32810255
theorem B58329341 : Blo 2021435 58329341 := bstep (se 3 (by rfl) ⟨10936751, by rfl⟩ : syracuseStep 58329341 = 21873503) B21873503
theorem B38886227 : Blo 2021435 38886227 := bstep (se 1 (by rfl) ⟨29164670, by rfl⟩ : syracuseStep 38886227 = 58329341) B58329341
theorem B25924151 : Blo 2021435 25924151 := bstep (se 1 (by rfl) ⟨19443113, by rfl⟩ : syracuseStep 25924151 = 38886227) B38886227
theorem B17282767 : Blo 2021435 17282767 := bstep (se 1 (by rfl) ⟨12962075, by rfl⟩ : syracuseStep 17282767 = 25924151) B25924151
theorem B23043689 : Blo 2021435 23043689 := bstep (se 2 (by rfl) ⟨8641383, by rfl⟩ : syracuseStep 23043689 = 17282767) B17282767
theorem B15362459 : Blo 2021435 15362459 := bstep (se 1 (by rfl) ⟨11521844, by rfl⟩ : syracuseStep 15362459 = 23043689) B23043689
theorem B10241639 : Blo 2021435 10241639 := bstep (se 1 (by rfl) ⟨7681229, by rfl⟩ : syracuseStep 10241639 = 15362459) B15362459
theorem B6827759 : Blo 2021435 6827759 := bstep (se 1 (by rfl) ⟨5120819, by rfl⟩ : syracuseStep 6827759 = 10241639) B10241639
theorem B4551839 : Blo 2021435 4551839 := bstep (se 1 (by rfl) ⟨3413879, by rfl⟩ : syracuseStep 4551839 = 6827759) B6827759
theorem B3034559 : Blo 2021435 3034559 := bstep (se 1 (by rfl) ⟨2275919, by rfl⟩ : syracuseStep 3034559 = 4551839) B4551839
theorem B2023039 : Blo 2021435 2023039 := bstep (se 1 (by rfl) ⟨1517279, by rfl⟩ : syracuseStep 2023039 = 3034559) B3034559
theorem B3034565 : Blo 2021435 3034565 := bbase (se 4 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 3034565 = 568981) (by norm_num)
theorem B2023043 : Blo 2021435 2023043 := bstep (se 1 (by rfl) ⟨1517282, by rfl⟩ : syracuseStep 2023043 = 3034565) B3034565
theorem B3413893 : Blo 2021435 3413893 := bbase (se 4 (by rfl) ⟨320052, by rfl⟩ : syracuseStep 3413893 = 640105) (by norm_num)
theorem B4551857 : Blo 2021435 4551857 := bstep (se 2 (by rfl) ⟨1706946, by rfl⟩ : syracuseStep 4551857 = 3413893) B3413893
theorem B3034571 : Blo 2021435 3034571 := bstep (se 1 (by rfl) ⟨2275928, by rfl⟩ : syracuseStep 3034571 = 4551857) B4551857
theorem B2023047 : Blo 2021435 2023047 := bstep (se 1 (by rfl) ⟨1517285, by rfl⟩ : syracuseStep 2023047 = 3034571) B3034571
theorem B2275933 : Blo 2021435 2275933 := bbase (se 3 (by rfl) ⟨426737, by rfl⟩ : syracuseStep 2275933 = 853475) (by norm_num)
theorem B3034577 : Blo 2021435 3034577 := bstep (se 2 (by rfl) ⟨1137966, by rfl⟩ : syracuseStep 3034577 = 2275933) B2275933
theorem B2023051 : Blo 2021435 2023051 := bstep (se 1 (by rfl) ⟨1517288, by rfl⟩ : syracuseStep 2023051 = 3034577) B3034577
theorem B6827813 : Blo 2021435 6827813 := bbase (se 4 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 6827813 = 1280215) (by norm_num)
theorem B4551875 : Blo 2021435 4551875 := bstep (se 1 (by rfl) ⟨3413906, by rfl⟩ : syracuseStep 4551875 = 6827813) B6827813
theorem B3034583 : Blo 2021435 3034583 := bstep (se 1 (by rfl) ⟨2275937, by rfl⟩ : syracuseStep 3034583 = 4551875) B4551875
theorem B2023055 : Blo 2021435 2023055 := bstep (se 1 (by rfl) ⟨1517291, by rfl⟩ : syracuseStep 2023055 = 3034583) B3034583
theorem B3034589 : Blo 2021435 3034589 := bbase (se 3 (by rfl) ⟨568985, by rfl⟩ : syracuseStep 3034589 = 1137971) (by norm_num)
theorem B2023059 : Blo 2021435 2023059 := bstep (se 1 (by rfl) ⟨1517294, by rfl⟩ : syracuseStep 2023059 = 3034589) B3034589
theorem B4551893 : Blo 2021435 4551893 := bbase (se 7 (by rfl) ⟨53342, by rfl⟩ : syracuseStep 4551893 = 106685) (by norm_num)
theorem B3034595 : Blo 2021435 3034595 := bstep (se 1 (by rfl) ⟨2275946, by rfl⟩ : syracuseStep 3034595 = 4551893) B4551893
theorem B2023063 : Blo 2021435 2023063 := bstep (se 1 (by rfl) ⟨1517297, by rfl⟩ : syracuseStep 2023063 = 3034595) B3034595
theorem B12304021 : Blo 2021435 12304021 := bbase (se 6 (by rfl) ⟨288375, by rfl⟩ : syracuseStep 12304021 = 576751) (by norm_num)
theorem B16405361 : Blo 2021435 16405361 := bstep (se 2 (by rfl) ⟨6152010, by rfl⟩ : syracuseStep 16405361 = 12304021) B12304021
theorem B10936907 : Blo 2021435 10936907 := bstep (se 1 (by rfl) ⟨8202680, by rfl⟩ : syracuseStep 10936907 = 16405361) B16405361
theorem B7291271 : Blo 2021435 7291271 := bstep (se 1 (by rfl) ⟨5468453, by rfl⟩ : syracuseStep 7291271 = 10936907) B10936907
theorem B4860847 : Blo 2021435 4860847 := bstep (se 1 (by rfl) ⟨3645635, by rfl⟩ : syracuseStep 4860847 = 7291271) B7291271
theorem B6481129 : Blo 2021435 6481129 := bstep (se 2 (by rfl) ⟨2430423, by rfl⟩ : syracuseStep 6481129 = 4860847) B4860847
theorem B8641505 : Blo 2021435 8641505 := bstep (se 2 (by rfl) ⟨3240564, by rfl⟩ : syracuseStep 8641505 = 6481129) B6481129
theorem B5761003 : Blo 2021435 5761003 := bstep (se 1 (by rfl) ⟨4320752, by rfl⟩ : syracuseStep 5761003 = 8641505) B8641505
theorem B7681337 : Blo 2021435 7681337 := bstep (se 2 (by rfl) ⟨2880501, by rfl⟩ : syracuseStep 7681337 = 5761003) B5761003
theorem B5120891 : Blo 2021435 5120891 := bstep (se 1 (by rfl) ⟨3840668, by rfl⟩ : syracuseStep 5120891 = 7681337) B7681337
theorem B3413927 : Blo 2021435 3413927 := bstep (se 1 (by rfl) ⟨2560445, by rfl⟩ : syracuseStep 3413927 = 5120891) B5120891
theorem B2275951 : Blo 2021435 2275951 := bstep (se 1 (by rfl) ⟨1706963, by rfl⟩ : syracuseStep 2275951 = 3413927) B3413927
theorem B3034601 : Blo 2021435 3034601 := bstep (se 2 (by rfl) ⟨1137975, by rfl⟩ : syracuseStep 3034601 = 2275951) B2275951
theorem B2023067 : Blo 2021435 2023067 := bstep (se 1 (by rfl) ⟨1517300, by rfl⟩ : syracuseStep 2023067 = 3034601) B3034601
theorem B3507725 : Blo 2021435 3507725 := bbase (se 3 (by rfl) ⟨657698, by rfl⟩ : syracuseStep 3507725 = 1315397) (by norm_num)
theorem B9353933 : Blo 2021435 9353933 := bstep (se 3 (by rfl) ⟨1753862, by rfl⟩ : syracuseStep 9353933 = 3507725) B3507725
theorem B6235955 : Blo 2021435 6235955 := bstep (se 1 (by rfl) ⟨4676966, by rfl⟩ : syracuseStep 6235955 = 9353933) B9353933
theorem B266067413 : Blo 2021435 266067413 := bstep (se 7 (by rfl) ⟨3117977, by rfl⟩ : syracuseStep 266067413 = 6235955) B6235955
theorem B177378275 : Blo 2021435 177378275 := bstep (se 1 (by rfl) ⟨133033706, by rfl⟩ : syracuseStep 177378275 = 266067413) B266067413
theorem B118252183 : Blo 2021435 118252183 := bstep (se 1 (by rfl) ⟨88689137, by rfl⟩ : syracuseStep 118252183 = 177378275) B177378275
theorem B157669577 : Blo 2021435 157669577 := bstep (se 2 (by rfl) ⟨59126091, by rfl⟩ : syracuseStep 157669577 = 118252183) B118252183
theorem B105113051 : Blo 2021435 105113051 := bstep (se 1 (by rfl) ⟨78834788, by rfl⟩ : syracuseStep 105113051 = 157669577) B157669577
theorem B70075367 : Blo 2021435 70075367 := bstep (se 1 (by rfl) ⟨52556525, by rfl⟩ : syracuseStep 70075367 = 105113051) B105113051
theorem B46716911 : Blo 2021435 46716911 := bstep (se 1 (by rfl) ⟨35037683, by rfl⟩ : syracuseStep 46716911 = 70075367) B70075367
theorem B31144607 : Blo 2021435 31144607 := bstep (se 1 (by rfl) ⟨23358455, by rfl⟩ : syracuseStep 31144607 = 46716911) B46716911
theorem B20763071 : Blo 2021435 20763071 := bstep (se 1 (by rfl) ⟨15572303, by rfl⟩ : syracuseStep 20763071 = 31144607) B31144607
theorem B13842047 : Blo 2021435 13842047 := bstep (se 1 (by rfl) ⟨10381535, by rfl⟩ : syracuseStep 13842047 = 20763071) B20763071
theorem B36912125 : Blo 2021435 36912125 := bstep (se 3 (by rfl) ⟨6921023, by rfl⟩ : syracuseStep 36912125 = 13842047) B13842047
theorem B24608083 : Blo 2021435 24608083 := bstep (se 1 (by rfl) ⟨18456062, by rfl⟩ : syracuseStep 24608083 = 36912125) B36912125
theorem B32810777 : Blo 2021435 32810777 := bstep (se 2 (by rfl) ⟨12304041, by rfl⟩ : syracuseStep 32810777 = 24608083) B24608083
theorem B21873851 : Blo 2021435 21873851 := bstep (se 1 (by rfl) ⟨16405388, by rfl⟩ : syracuseStep 21873851 = 32810777) B32810777
theorem B14582567 : Blo 2021435 14582567 := bstep (se 1 (by rfl) ⟨10936925, by rfl⟩ : syracuseStep 14582567 = 21873851) B21873851
theorem B9721711 : Blo 2021435 9721711 := bstep (se 1 (by rfl) ⟨7291283, by rfl⟩ : syracuseStep 9721711 = 14582567) B14582567
theorem B12962281 : Blo 2021435 12962281 := bstep (se 2 (by rfl) ⟨4860855, by rfl⟩ : syracuseStep 12962281 = 9721711) B9721711
theorem B17283041 : Blo 2021435 17283041 := bstep (se 2 (by rfl) ⟨6481140, by rfl⟩ : syracuseStep 17283041 = 12962281) B12962281
theorem B11522027 : Blo 2021435 11522027 := bstep (se 1 (by rfl) ⟨8641520, by rfl⟩ : syracuseStep 11522027 = 17283041) B17283041
theorem B7681351 : Blo 2021435 7681351 := bstep (se 1 (by rfl) ⟨5761013, by rfl⟩ : syracuseStep 7681351 = 11522027) B11522027
theorem B10241801 : Blo 2021435 10241801 := bstep (se 2 (by rfl) ⟨3840675, by rfl⟩ : syracuseStep 10241801 = 7681351) B7681351
theorem B6827867 : Blo 2021435 6827867 := bstep (se 1 (by rfl) ⟨5120900, by rfl⟩ : syracuseStep 6827867 = 10241801) B10241801
theorem B4551911 : Blo 2021435 4551911 := bstep (se 1 (by rfl) ⟨3413933, by rfl⟩ : syracuseStep 4551911 = 6827867) B6827867
theorem B3034607 : Blo 2021435 3034607 := bstep (se 1 (by rfl) ⟨2275955, by rfl⟩ : syracuseStep 3034607 = 4551911) B4551911
theorem B2023071 : Blo 2021435 2023071 := bstep (se 1 (by rfl) ⟨1517303, by rfl⟩ : syracuseStep 2023071 = 3034607) B3034607
theorem B3034613 : Blo 2021435 3034613 := bbase (se 5 (by rfl) ⟨142247, by rfl⟩ : syracuseStep 3034613 = 284495) (by norm_num)
theorem B2023075 : Blo 2021435 2023075 := bstep (se 1 (by rfl) ⟨1517306, by rfl⟩ : syracuseStep 2023075 = 3034613) B3034613
theorem B2160389 : Blo 2021435 2160389 := bbase (se 4 (by rfl) ⟨202536, by rfl⟩ : syracuseStep 2160389 = 405073) (by norm_num)
theorem B5761037 : Blo 2021435 5761037 := bstep (se 3 (by rfl) ⟨1080194, by rfl⟩ : syracuseStep 5761037 = 2160389) B2160389
theorem B3840691 : Blo 2021435 3840691 := bstep (se 1 (by rfl) ⟨2880518, by rfl⟩ : syracuseStep 3840691 = 5761037) B5761037
theorem B5120921 : Blo 2021435 5120921 := bstep (se 2 (by rfl) ⟨1920345, by rfl⟩ : syracuseStep 5120921 = 3840691) B3840691
theorem B3413947 : Blo 2021435 3413947 := bstep (se 1 (by rfl) ⟨2560460, by rfl⟩ : syracuseStep 3413947 = 5120921) B5120921
theorem B4551929 : Blo 2021435 4551929 := bstep (se 2 (by rfl) ⟨1706973, by rfl⟩ : syracuseStep 4551929 = 3413947) B3413947
theorem B3034619 : Blo 2021435 3034619 := bstep (se 1 (by rfl) ⟨2275964, by rfl⟩ : syracuseStep 3034619 = 4551929) B4551929
theorem B2023079 : Blo 2021435 2023079 := bstep (se 1 (by rfl) ⟨1517309, by rfl⟩ : syracuseStep 2023079 = 3034619) B3034619
theorem B2275969 : Blo 2021435 2275969 := bbase (se 2 (by rfl) ⟨853488, by rfl⟩ : syracuseStep 2275969 = 1706977) (by norm_num)
theorem B3034625 : Blo 2021435 3034625 := bstep (se 2 (by rfl) ⟨1137984, by rfl⟩ : syracuseStep 3034625 = 2275969) B2275969
theorem B2023083 : Blo 2021435 2023083 := bstep (se 1 (by rfl) ⟨1517312, by rfl⟩ : syracuseStep 2023083 = 3034625) B3034625
theorem B5120941 : Blo 2021435 5120941 := bbase (se 3 (by rfl) ⟨960176, by rfl⟩ : syracuseStep 5120941 = 1920353) (by norm_num)
theorem B6827921 : Blo 2021435 6827921 := bstep (se 2 (by rfl) ⟨2560470, by rfl⟩ : syracuseStep 6827921 = 5120941) B5120941
theorem B4551947 : Blo 2021435 4551947 := bstep (se 1 (by rfl) ⟨3413960, by rfl⟩ : syracuseStep 4551947 = 6827921) B6827921
theorem B3034631 : Blo 2021435 3034631 := bstep (se 1 (by rfl) ⟨2275973, by rfl⟩ : syracuseStep 3034631 = 4551947) B4551947
theorem B2023087 : Blo 2021435 2023087 := bstep (se 1 (by rfl) ⟨1517315, by rfl⟩ : syracuseStep 2023087 = 3034631) B3034631
theorem B3034637 : Blo 2021435 3034637 := bbase (se 3 (by rfl) ⟨568994, by rfl⟩ : syracuseStep 3034637 = 1137989) (by norm_num)
theorem B2023091 : Blo 2021435 2023091 := bstep (se 1 (by rfl) ⟨1517318, by rfl⟩ : syracuseStep 2023091 = 3034637) B3034637
theorem B4551965 : Blo 2021435 4551965 := bbase (se 3 (by rfl) ⟨853493, by rfl⟩ : syracuseStep 4551965 = 1706987) (by norm_num)
theorem B3034643 : Blo 2021435 3034643 := bstep (se 1 (by rfl) ⟨2275982, by rfl⟩ : syracuseStep 3034643 = 4551965) B4551965
theorem B2023095 : Blo 2021435 2023095 := bstep (se 1 (by rfl) ⟨1517321, by rfl⟩ : syracuseStep 2023095 = 3034643) B3034643
theorem B3413981 : Blo 2021435 3413981 := bbase (se 3 (by rfl) ⟨640121, by rfl⟩ : syracuseStep 3413981 = 1280243) (by norm_num)
theorem B2275987 : Blo 2021435 2275987 := bstep (se 1 (by rfl) ⟨1706990, by rfl⟩ : syracuseStep 2275987 = 3413981) B3413981
theorem B3034649 : Blo 2021435 3034649 := bstep (se 2 (by rfl) ⟨1137993, by rfl⟩ : syracuseStep 3034649 = 2275987) B2275987
theorem B2023099 : Blo 2021435 2023099 := bstep (se 1 (by rfl) ⟨1517324, by rfl⟩ : syracuseStep 2023099 = 3034649) B3034649
theorem B7786277 : Blo 2021435 7786277 := bbase (se 4 (by rfl) ⟨729963, by rfl⟩ : syracuseStep 7786277 = 1459927) (by norm_num)
theorem B5190851 : Blo 2021435 5190851 := bstep (se 1 (by rfl) ⟨3893138, by rfl⟩ : syracuseStep 5190851 = 7786277) B7786277
theorem B3460567 : Blo 2021435 3460567 := bstep (se 1 (by rfl) ⟨2595425, by rfl⟩ : syracuseStep 3460567 = 5190851) B5190851
theorem B4614089 : Blo 2021435 4614089 := bstep (se 2 (by rfl) ⟨1730283, by rfl⟩ : syracuseStep 4614089 = 3460567) B3460567
theorem B12304237 : Blo 2021435 12304237 := bstep (se 3 (by rfl) ⟨2307044, by rfl⟩ : syracuseStep 12304237 = 4614089) B4614089
theorem B16405649 : Blo 2021435 16405649 := bstep (se 2 (by rfl) ⟨6152118, by rfl⟩ : syracuseStep 16405649 = 12304237) B12304237
theorem B10937099 : Blo 2021435 10937099 := bstep (se 1 (by rfl) ⟨8202824, by rfl⟩ : syracuseStep 10937099 = 16405649) B16405649
theorem B7291399 : Blo 2021435 7291399 := bstep (se 1 (by rfl) ⟨5468549, by rfl⟩ : syracuseStep 7291399 = 10937099) B10937099
theorem B9721865 : Blo 2021435 9721865 := bstep (se 2 (by rfl) ⟨3645699, by rfl⟩ : syracuseStep 9721865 = 7291399) B7291399
theorem B6481243 : Blo 2021435 6481243 := bstep (se 1 (by rfl) ⟨4860932, by rfl⟩ : syracuseStep 6481243 = 9721865) B9721865
theorem B8641657 : Blo 2021435 8641657 := bstep (se 2 (by rfl) ⟨3240621, by rfl⟩ : syracuseStep 8641657 = 6481243) B6481243
theorem B11522209 : Blo 2021435 11522209 := bstep (se 2 (by rfl) ⟨4320828, by rfl⟩ : syracuseStep 11522209 = 8641657) B8641657
theorem B15362945 : Blo 2021435 15362945 := bstep (se 2 (by rfl) ⟨5761104, by rfl⟩ : syracuseStep 15362945 = 11522209) B11522209
theorem B10241963 : Blo 2021435 10241963 := bstep (se 1 (by rfl) ⟨7681472, by rfl⟩ : syracuseStep 10241963 = 15362945) B15362945
theorem B6827975 : Blo 2021435 6827975 := bstep (se 1 (by rfl) ⟨5120981, by rfl⟩ : syracuseStep 6827975 = 10241963) B10241963
theorem B4551983 : Blo 2021435 4551983 := bstep (se 1 (by rfl) ⟨3413987, by rfl⟩ : syracuseStep 4551983 = 6827975) B6827975
theorem B3034655 : Blo 2021435 3034655 := bstep (se 1 (by rfl) ⟨2275991, by rfl⟩ : syracuseStep 3034655 = 4551983) B4551983
theorem B2023103 : Blo 2021435 2023103 := bstep (se 1 (by rfl) ⟨1517327, by rfl⟩ : syracuseStep 2023103 = 3034655) B3034655
theorem B3034661 : Blo 2021435 3034661 := bbase (se 4 (by rfl) ⟨284499, by rfl⟩ : syracuseStep 3034661 = 568999) (by norm_num)
theorem B2023107 : Blo 2021435 2023107 := bstep (se 1 (by rfl) ⟨1517330, by rfl⟩ : syracuseStep 2023107 = 3034661) B3034661
theorem B2560501 : Blo 2021435 2560501 := bbase (se 5 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 2560501 = 240047) (by norm_num)
theorem B3414001 : Blo 2021435 3414001 := bstep (se 2 (by rfl) ⟨1280250, by rfl⟩ : syracuseStep 3414001 = 2560501) B2560501
theorem B4552001 : Blo 2021435 4552001 := bstep (se 2 (by rfl) ⟨1707000, by rfl⟩ : syracuseStep 4552001 = 3414001) B3414001
theorem B3034667 : Blo 2021435 3034667 := bstep (se 1 (by rfl) ⟨2276000, by rfl⟩ : syracuseStep 3034667 = 4552001) B4552001
theorem B2023111 : Blo 2021435 2023111 := bstep (se 1 (by rfl) ⟨1517333, by rfl⟩ : syracuseStep 2023111 = 3034667) B3034667
theorem B2276005 : Blo 2021435 2276005 := bbase (se 4 (by rfl) ⟨213375, by rfl⟩ : syracuseStep 2276005 = 426751) (by norm_num)
theorem B3034673 : Blo 2021435 3034673 := bstep (se 2 (by rfl) ⟨1138002, by rfl⟩ : syracuseStep 3034673 = 2276005) B2276005
theorem B2023115 : Blo 2021435 2023115 := bstep (se 1 (by rfl) ⟨1517336, by rfl⟩ : syracuseStep 2023115 = 3034673) B3034673
theorem B10523429 : Blo 2021435 10523429 := bbase (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) (by norm_num)
theorem B7015619 : Blo 2021435 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B18708317 : Blo 2021435 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B12472211 : Blo 2021435 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B8314807 : Blo 2021435 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B11086409 : Blo 2021435 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B7390939 : Blo 2021435 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B9854585 : Blo 2021435 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B6569723 : Blo 2021435 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B4379815 : Blo 2021435 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B23359013 : Blo 2021435 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B15572675 : Blo 2021435 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B41527133 : Blo 2021435 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B27684755 : Blo 2021435 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B18456503 : Blo 2021435 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B49217341 : Blo 2021435 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B65623121 : Blo 2021435 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B43748747 : Blo 2021435 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B29165831 : Blo 2021435 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B19443887 : Blo 2021435 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B12962591 : Blo 2021435 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B8641727 : Blo 2021435 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B5761151 : Blo 2021435 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B3840767 : Blo 2021435 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B2560511 : Blo 2021435 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B6828029 : Blo 2021435 6828029 := bstep (se 3 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 6828029 = 2560511) B2560511
theorem B4552019 : Blo 2021435 4552019 := bstep (se 1 (by rfl) ⟨3414014, by rfl⟩ : syracuseStep 4552019 = 6828029) B6828029
theorem B3034679 : Blo 2021435 3034679 := bstep (se 1 (by rfl) ⟨2276009, by rfl⟩ : syracuseStep 3034679 = 4552019) B4552019
theorem B2023119 : Blo 2021435 2023119 := bstep (se 1 (by rfl) ⟨1517339, by rfl⟩ : syracuseStep 2023119 = 3034679) B3034679
theorem B3034685 : Blo 2021435 3034685 := bbase (se 3 (by rfl) ⟨569003, by rfl⟩ : syracuseStep 3034685 = 1138007) (by norm_num)
theorem B2023123 : Blo 2021435 2023123 := bstep (se 1 (by rfl) ⟨1517342, by rfl⟩ : syracuseStep 2023123 = 3034685) B3034685
theorem B4552037 : Blo 2021435 4552037 := bbase (se 4 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 4552037 = 853507) (by norm_num)
theorem B3034691 : Blo 2021435 3034691 := bstep (se 1 (by rfl) ⟨2276018, by rfl⟩ : syracuseStep 3034691 = 4552037) B4552037
theorem B2023127 : Blo 2021435 2023127 := bstep (se 1 (by rfl) ⟨1517345, by rfl⟩ : syracuseStep 2023127 = 3034691) B3034691
theorem B5121053 : Blo 2021435 5121053 := bbase (se 3 (by rfl) ⟨960197, by rfl⟩ : syracuseStep 5121053 = 1920395) (by norm_num)
theorem B3414035 : Blo 2021435 3414035 := bstep (se 1 (by rfl) ⟨2560526, by rfl⟩ : syracuseStep 3414035 = 5121053) B5121053
theorem B2276023 : Blo 2021435 2276023 := bstep (se 1 (by rfl) ⟨1707017, by rfl⟩ : syracuseStep 2276023 = 3414035) B3414035
theorem B3034697 : Blo 2021435 3034697 := bstep (se 2 (by rfl) ⟨1138011, by rfl⟩ : syracuseStep 3034697 = 2276023) B2276023
theorem B2023131 : Blo 2021435 2023131 := bstep (se 1 (by rfl) ⟨1517348, by rfl⟩ : syracuseStep 2023131 = 3034697) B3034697
theorem B3840797 : Blo 2021435 3840797 := bbase (se 3 (by rfl) ⟨720149, by rfl⟩ : syracuseStep 3840797 = 1440299) (by norm_num)
theorem B10242125 : Blo 2021435 10242125 := bstep (se 3 (by rfl) ⟨1920398, by rfl⟩ : syracuseStep 10242125 = 3840797) B3840797
theorem B6828083 : Blo 2021435 6828083 := bstep (se 1 (by rfl) ⟨5121062, by rfl⟩ : syracuseStep 6828083 = 10242125) B10242125
theorem B4552055 : Blo 2021435 4552055 := bstep (se 1 (by rfl) ⟨3414041, by rfl⟩ : syracuseStep 4552055 = 6828083) B6828083
theorem B3034703 : Blo 2021435 3034703 := bstep (se 1 (by rfl) ⟨2276027, by rfl⟩ : syracuseStep 3034703 = 4552055) B4552055
theorem B2023135 : Blo 2021435 2023135 := bstep (se 1 (by rfl) ⟨1517351, by rfl⟩ : syracuseStep 2023135 = 3034703) B3034703
theorem B3034709 : Blo 2021435 3034709 := bbase (se 8 (by rfl) ⟨17781, by rfl⟩ : syracuseStep 3034709 = 35563) (by norm_num)
theorem B2023139 : Blo 2021435 2023139 := bstep (se 1 (by rfl) ⟨1517354, by rfl⟩ : syracuseStep 2023139 = 3034709) B3034709
theorem B8641829 : Blo 2021435 8641829 := bbase (se 4 (by rfl) ⟨810171, by rfl⟩ : syracuseStep 8641829 = 1620343) (by norm_num)
theorem B5761219 : Blo 2021435 5761219 := bstep (se 1 (by rfl) ⟨4320914, by rfl⟩ : syracuseStep 5761219 = 8641829) B8641829
theorem B7681625 : Blo 2021435 7681625 := bstep (se 2 (by rfl) ⟨2880609, by rfl⟩ : syracuseStep 7681625 = 5761219) B5761219
theorem B5121083 : Blo 2021435 5121083 := bstep (se 1 (by rfl) ⟨3840812, by rfl⟩ : syracuseStep 5121083 = 7681625) B7681625
theorem B3414055 : Blo 2021435 3414055 := bstep (se 1 (by rfl) ⟨2560541, by rfl⟩ : syracuseStep 3414055 = 5121083) B5121083
theorem B4552073 : Blo 2021435 4552073 := bstep (se 2 (by rfl) ⟨1707027, by rfl⟩ : syracuseStep 4552073 = 3414055) B3414055
theorem B3034715 : Blo 2021435 3034715 := bstep (se 1 (by rfl) ⟨2276036, by rfl⟩ : syracuseStep 3034715 = 4552073) B4552073
theorem B2023143 : Blo 2021435 2023143 := bstep (se 1 (by rfl) ⟨1517357, by rfl⟩ : syracuseStep 2023143 = 3034715) B3034715
theorem B2276041 : Blo 2021435 2276041 := bbase (se 2 (by rfl) ⟨853515, by rfl⟩ : syracuseStep 2276041 = 1707031) (by norm_num)
theorem B3034721 : Blo 2021435 3034721 := bstep (se 2 (by rfl) ⟨1138020, by rfl⟩ : syracuseStep 3034721 = 2276041) B2276041
theorem B2023147 : Blo 2021435 2023147 := bstep (se 1 (by rfl) ⟨1517360, by rfl⟩ : syracuseStep 2023147 = 3034721) B3034721
theorem B6481397 : Blo 2021435 6481397 := bbase (se 5 (by rfl) ⟨303815, by rfl⟩ : syracuseStep 6481397 = 607631) (by norm_num)
theorem B17283725 : Blo 2021435 17283725 := bstep (se 3 (by rfl) ⟨3240698, by rfl⟩ : syracuseStep 17283725 = 6481397) B6481397
theorem B11522483 : Blo 2021435 11522483 := bstep (se 1 (by rfl) ⟨8641862, by rfl⟩ : syracuseStep 11522483 = 17283725) B17283725
theorem B7681655 : Blo 2021435 7681655 := bstep (se 1 (by rfl) ⟨5761241, by rfl⟩ : syracuseStep 7681655 = 11522483) B11522483
theorem B5121103 : Blo 2021435 5121103 := bstep (se 1 (by rfl) ⟨3840827, by rfl⟩ : syracuseStep 5121103 = 7681655) B7681655
theorem B6828137 : Blo 2021435 6828137 := bstep (se 2 (by rfl) ⟨2560551, by rfl⟩ : syracuseStep 6828137 = 5121103) B5121103
theorem B4552091 : Blo 2021435 4552091 := bstep (se 1 (by rfl) ⟨3414068, by rfl⟩ : syracuseStep 4552091 = 6828137) B6828137
theorem B3034727 : Blo 2021435 3034727 := bstep (se 1 (by rfl) ⟨2276045, by rfl⟩ : syracuseStep 3034727 = 4552091) B4552091
theorem B2023151 : Blo 2021435 2023151 := bstep (se 1 (by rfl) ⟨1517363, by rfl⟩ : syracuseStep 2023151 = 3034727) B3034727
theorem B3034733 : Blo 2021435 3034733 := bbase (se 3 (by rfl) ⟨569012, by rfl⟩ : syracuseStep 3034733 = 1138025) (by norm_num)
theorem B2023155 : Blo 2021435 2023155 := bstep (se 1 (by rfl) ⟨1517366, by rfl⟩ : syracuseStep 2023155 = 3034733) B3034733
theorem B4552109 : Blo 2021435 4552109 := bbase (se 3 (by rfl) ⟨853520, by rfl⟩ : syracuseStep 4552109 = 1707041) (by norm_num)
theorem B3034739 : Blo 2021435 3034739 := bstep (se 1 (by rfl) ⟨2276054, by rfl⟩ : syracuseStep 3034739 = 4552109) B4552109
theorem B2023159 : Blo 2021435 2023159 := bstep (se 1 (by rfl) ⟨1517369, by rfl⟩ : syracuseStep 2023159 = 3034739) B3034739
theorem B10937429 : Blo 2021435 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B7291619 : Blo 2021435 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B4861079 : Blo 2021435 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B3240719 : Blo 2021435 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B2160479 : Blo 2021435 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B5761277 : Blo 2021435 5761277 := bstep (se 3 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 5761277 = 2160479) B2160479
theorem B3840851 : Blo 2021435 3840851 := bstep (se 1 (by rfl) ⟨2880638, by rfl⟩ : syracuseStep 3840851 = 5761277) B5761277
theorem B2560567 : Blo 2021435 2560567 := bstep (se 1 (by rfl) ⟨1920425, by rfl⟩ : syracuseStep 2560567 = 3840851) B3840851
theorem B3414089 : Blo 2021435 3414089 := bstep (se 2 (by rfl) ⟨1280283, by rfl⟩ : syracuseStep 3414089 = 2560567) B2560567
theorem B2276059 : Blo 2021435 2276059 := bstep (se 1 (by rfl) ⟨1707044, by rfl⟩ : syracuseStep 2276059 = 3414089) B3414089
theorem B3034745 : Blo 2021435 3034745 := bstep (se 2 (by rfl) ⟨1138029, by rfl⟩ : syracuseStep 3034745 = 2276059) B2276059
theorem B2023163 : Blo 2021435 2023163 := bstep (se 1 (by rfl) ⟨1517372, by rfl⟩ : syracuseStep 2023163 = 3034745) B3034745
theorem B7594165 : Blo 2021435 7594165 := bbase (se 5 (by rfl) ⟨355976, by rfl⟩ : syracuseStep 7594165 = 711953) (by norm_num)
theorem B10125553 : Blo 2021435 10125553 := bstep (se 2 (by rfl) ⟨3797082, by rfl⟩ : syracuseStep 10125553 = 7594165) B7594165
theorem B13500737 : Blo 2021435 13500737 := bstep (se 2 (by rfl) ⟨5062776, by rfl⟩ : syracuseStep 13500737 = 10125553) B10125553
theorem B9000491 : Blo 2021435 9000491 := bstep (se 1 (by rfl) ⟨6750368, by rfl⟩ : syracuseStep 9000491 = 13500737) B13500737
theorem B6144335189 : Blo 2021435 6144335189 := bstep (se 11 (by rfl) ⟨4500245, by rfl⟩ : syracuseStep 6144335189 = 9000491) B9000491
theorem B4096223459 : Blo 2021435 4096223459 := bstep (se 1 (by rfl) ⟨3072167594, by rfl⟩ : syracuseStep 4096223459 = 6144335189) B6144335189
theorem B2730815639 : Blo 2021435 2730815639 := bstep (se 1 (by rfl) ⟨2048111729, by rfl⟩ : syracuseStep 2730815639 = 4096223459) B4096223459
theorem B1820543759 : Blo 2021435 1820543759 := bstep (se 1 (by rfl) ⟨1365407819, by rfl⟩ : syracuseStep 1820543759 = 2730815639) B2730815639
theorem B1213695839 : Blo 2021435 1213695839 := bstep (se 1 (by rfl) ⟨910271879, by rfl⟩ : syracuseStep 1213695839 = 1820543759) B1820543759
theorem B809130559 : Blo 2021435 809130559 := bstep (se 1 (by rfl) ⟨606847919, by rfl⟩ : syracuseStep 809130559 = 1213695839) B1213695839
theorem B1078840745 : Blo 2021435 1078840745 := bstep (se 2 (by rfl) ⟨404565279, by rfl⟩ : syracuseStep 1078840745 = 809130559) B809130559
theorem B719227163 : Blo 2021435 719227163 := bstep (se 1 (by rfl) ⟨539420372, by rfl⟩ : syracuseStep 719227163 = 1078840745) B1078840745
theorem B479484775 : Blo 2021435 479484775 := bstep (se 1 (by rfl) ⟨359613581, by rfl⟩ : syracuseStep 479484775 = 719227163) B719227163
theorem B639313033 : Blo 2021435 639313033 := bstep (se 2 (by rfl) ⟨239742387, by rfl⟩ : syracuseStep 639313033 = 479484775) B479484775
theorem B852417377 : Blo 2021435 852417377 := bstep (se 2 (by rfl) ⟨319656516, by rfl⟩ : syracuseStep 852417377 = 639313033) B639313033
theorem B568278251 : Blo 2021435 568278251 := bstep (se 1 (by rfl) ⟨426208688, by rfl⟩ : syracuseStep 568278251 = 852417377) B852417377
theorem B378852167 : Blo 2021435 378852167 := bstep (se 1 (by rfl) ⟨284139125, by rfl⟩ : syracuseStep 378852167 = 568278251) B568278251
theorem B1010272445 : Blo 2021435 1010272445 := bstep (se 3 (by rfl) ⟨189426083, by rfl⟩ : syracuseStep 1010272445 = 378852167) B378852167
theorem B673514963 : Blo 2021435 673514963 := bstep (se 1 (by rfl) ⟨505136222, by rfl⟩ : syracuseStep 673514963 = 1010272445) B1010272445
theorem B449009975 : Blo 2021435 449009975 := bstep (se 1 (by rfl) ⟨336757481, by rfl⟩ : syracuseStep 449009975 = 673514963) B673514963
theorem B299339983 : Blo 2021435 299339983 := bstep (se 1 (by rfl) ⟨224504987, by rfl⟩ : syracuseStep 299339983 = 449009975) B449009975
theorem B399119977 : Blo 2021435 399119977 := bstep (se 2 (by rfl) ⟨149669991, by rfl⟩ : syracuseStep 399119977 = 299339983) B299339983
theorem B532159969 : Blo 2021435 532159969 := bstep (se 2 (by rfl) ⟨199559988, by rfl⟩ : syracuseStep 532159969 = 399119977) B399119977
theorem B709546625 : Blo 2021435 709546625 := bstep (se 2 (by rfl) ⟨266079984, by rfl⟩ : syracuseStep 709546625 = 532159969) B532159969
theorem B473031083 : Blo 2021435 473031083 := bstep (se 1 (by rfl) ⟨354773312, by rfl⟩ : syracuseStep 473031083 = 709546625) B709546625
theorem B315354055 : Blo 2021435 315354055 := bstep (se 1 (by rfl) ⟨236515541, by rfl⟩ : syracuseStep 315354055 = 473031083) B473031083
theorem B420472073 : Blo 2021435 420472073 := bstep (se 2 (by rfl) ⟨157677027, by rfl⟩ : syracuseStep 420472073 = 315354055) B315354055
theorem B1121258861 : Blo 2021435 1121258861 := bstep (se 3 (by rfl) ⟨210236036, by rfl⟩ : syracuseStep 1121258861 = 420472073) B420472073
theorem B747505907 : Blo 2021435 747505907 := bstep (se 1 (by rfl) ⟨560629430, by rfl⟩ : syracuseStep 747505907 = 1121258861) B1121258861
theorem B498337271 : Blo 2021435 498337271 := bstep (se 1 (by rfl) ⟨373752953, by rfl⟩ : syracuseStep 498337271 = 747505907) B747505907
theorem B332224847 : Blo 2021435 332224847 := bstep (se 1 (by rfl) ⟨249168635, by rfl⟩ : syracuseStep 332224847 = 498337271) B498337271
theorem B221483231 : Blo 2021435 221483231 := bstep (se 1 (by rfl) ⟨166112423, by rfl⟩ : syracuseStep 221483231 = 332224847) B332224847
theorem B147655487 : Blo 2021435 147655487 := bstep (se 1 (by rfl) ⟨110741615, by rfl⟩ : syracuseStep 147655487 = 221483231) B221483231
theorem B98436991 : Blo 2021435 98436991 := bstep (se 1 (by rfl) ⟨73827743, by rfl⟩ : syracuseStep 98436991 = 147655487) B147655487
theorem B131249321 : Blo 2021435 131249321 := bstep (se 2 (by rfl) ⟨49218495, by rfl⟩ : syracuseStep 131249321 = 98436991) B98436991
theorem B87499547 : Blo 2021435 87499547 := bstep (se 1 (by rfl) ⟨65624660, by rfl⟩ : syracuseStep 87499547 = 131249321) B131249321
theorem B58333031 : Blo 2021435 58333031 := bstep (se 1 (by rfl) ⟨43749773, by rfl⟩ : syracuseStep 58333031 = 87499547) B87499547
theorem B38888687 : Blo 2021435 38888687 := bstep (se 1 (by rfl) ⟨29166515, by rfl⟩ : syracuseStep 38888687 = 58333031) B58333031
theorem B25925791 : Blo 2021435 25925791 := bstep (se 1 (by rfl) ⟨19444343, by rfl⟩ : syracuseStep 25925791 = 38888687) B38888687
theorem B34567721 : Blo 2021435 34567721 := bstep (se 2 (by rfl) ⟨12962895, by rfl⟩ : syracuseStep 34567721 = 25925791) B25925791
theorem B23045147 : Blo 2021435 23045147 := bstep (se 1 (by rfl) ⟨17283860, by rfl⟩ : syracuseStep 23045147 = 34567721) B34567721
theorem B15363431 : Blo 2021435 15363431 := bstep (se 1 (by rfl) ⟨11522573, by rfl⟩ : syracuseStep 15363431 = 23045147) B23045147
theorem B10242287 : Blo 2021435 10242287 := bstep (se 1 (by rfl) ⟨7681715, by rfl⟩ : syracuseStep 10242287 = 15363431) B15363431
theorem B6828191 : Blo 2021435 6828191 := bstep (se 1 (by rfl) ⟨5121143, by rfl⟩ : syracuseStep 6828191 = 10242287) B10242287
theorem B4552127 : Blo 2021435 4552127 := bstep (se 1 (by rfl) ⟨3414095, by rfl⟩ : syracuseStep 4552127 = 6828191) B6828191
theorem B3034751 : Blo 2021435 3034751 := bstep (se 1 (by rfl) ⟨2276063, by rfl⟩ : syracuseStep 3034751 = 4552127) B4552127
theorem B2023167 : Blo 2021435 2023167 := bstep (se 1 (by rfl) ⟨1517375, by rfl⟩ : syracuseStep 2023167 = 3034751) B3034751
theorem B3034757 : Blo 2021435 3034757 := bbase (se 4 (by rfl) ⟨284508, by rfl⟩ : syracuseStep 3034757 = 569017) (by norm_num)
theorem B2023171 : Blo 2021435 2023171 := bstep (se 1 (by rfl) ⟨1517378, by rfl⟩ : syracuseStep 2023171 = 3034757) B3034757
theorem B3414109 : Blo 2021435 3414109 := bbase (se 3 (by rfl) ⟨640145, by rfl⟩ : syracuseStep 3414109 = 1280291) (by norm_num)
theorem B4552145 : Blo 2021435 4552145 := bstep (se 2 (by rfl) ⟨1707054, by rfl⟩ : syracuseStep 4552145 = 3414109) B3414109
theorem B3034763 : Blo 2021435 3034763 := bstep (se 1 (by rfl) ⟨2276072, by rfl⟩ : syracuseStep 3034763 = 4552145) B4552145
theorem B2023175 : Blo 2021435 2023175 := bstep (se 1 (by rfl) ⟨1517381, by rfl⟩ : syracuseStep 2023175 = 3034763) B3034763
theorem B2276077 : Blo 2021435 2276077 := bbase (se 3 (by rfl) ⟨426764, by rfl⟩ : syracuseStep 2276077 = 853529) (by norm_num)
theorem B3034769 : Blo 2021435 3034769 := bstep (se 2 (by rfl) ⟨1138038, by rfl⟩ : syracuseStep 3034769 = 2276077) B2276077
theorem B2023179 : Blo 2021435 2023179 := bstep (se 1 (by rfl) ⟨1517384, by rfl⟩ : syracuseStep 2023179 = 3034769) B3034769
theorem B6828245 : Blo 2021435 6828245 := bbase (se 7 (by rfl) ⟨80018, by rfl⟩ : syracuseStep 6828245 = 160037) (by norm_num)
theorem B4552163 : Blo 2021435 4552163 := bstep (se 1 (by rfl) ⟨3414122, by rfl⟩ : syracuseStep 4552163 = 6828245) B6828245
theorem B3034775 : Blo 2021435 3034775 := bstep (se 1 (by rfl) ⟨2276081, by rfl⟩ : syracuseStep 3034775 = 4552163) B4552163
theorem B2023183 : Blo 2021435 2023183 := bstep (se 1 (by rfl) ⟨1517387, by rfl⟩ : syracuseStep 2023183 = 3034775) B3034775
theorem B3034781 : Blo 2021435 3034781 := bbase (se 3 (by rfl) ⟨569021, by rfl⟩ : syracuseStep 3034781 = 1138043) (by norm_num)
theorem B2023187 : Blo 2021435 2023187 := bstep (se 1 (by rfl) ⟨1517390, by rfl⟩ : syracuseStep 2023187 = 3034781) B3034781
theorem B4552181 : Blo 2021435 4552181 := bbase (se 5 (by rfl) ⟨213383, by rfl⟩ : syracuseStep 4552181 = 426767) (by norm_num)
theorem B3034787 : Blo 2021435 3034787 := bstep (se 1 (by rfl) ⟨2276090, by rfl⟩ : syracuseStep 3034787 = 4552181) B4552181
theorem B2023191 : Blo 2021435 2023191 := bstep (se 1 (by rfl) ⟨1517393, by rfl⟩ : syracuseStep 2023191 = 3034787) B3034787
theorem B3555805 : Blo 2021435 3555805 := bbase (se 3 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 3555805 = 1333427) (by norm_num)
theorem B4741073 : Blo 2021435 4741073 := bstep (se 2 (by rfl) ⟨1777902, by rfl⟩ : syracuseStep 4741073 = 3555805) B3555805
theorem B3160715 : Blo 2021435 3160715 := bstep (se 1 (by rfl) ⟨2370536, by rfl⟩ : syracuseStep 3160715 = 4741073) B4741073
theorem B8428573 : Blo 2021435 8428573 := bstep (se 3 (by rfl) ⟨1580357, by rfl⟩ : syracuseStep 8428573 = 3160715) B3160715
theorem B11238097 : Blo 2021435 11238097 := bstep (se 2 (by rfl) ⟨4214286, by rfl⟩ : syracuseStep 11238097 = 8428573) B8428573
theorem B14984129 : Blo 2021435 14984129 := bstep (se 2 (by rfl) ⟨5619048, by rfl⟩ : syracuseStep 14984129 = 11238097) B11238097
theorem B9989419 : Blo 2021435 9989419 := bstep (se 1 (by rfl) ⟨7492064, by rfl⟩ : syracuseStep 9989419 = 14984129) B14984129
theorem B13319225 : Blo 2021435 13319225 := bstep (se 2 (by rfl) ⟨4994709, by rfl⟩ : syracuseStep 13319225 = 9989419) B9989419
theorem B8879483 : Blo 2021435 8879483 := bstep (se 1 (by rfl) ⟨6659612, by rfl⟩ : syracuseStep 8879483 = 13319225) B13319225
theorem B5919655 : Blo 2021435 5919655 := bstep (se 1 (by rfl) ⟨4439741, by rfl⟩ : syracuseStep 5919655 = 8879483) B8879483
theorem B7892873 : Blo 2021435 7892873 := bstep (se 2 (by rfl) ⟨2959827, by rfl⟩ : syracuseStep 7892873 = 5919655) B5919655
theorem B5261915 : Blo 2021435 5261915 := bstep (se 1 (by rfl) ⟨3946436, by rfl⟩ : syracuseStep 5261915 = 7892873) B7892873
theorem B3507943 : Blo 2021435 3507943 := bstep (se 1 (by rfl) ⟨2630957, by rfl⟩ : syracuseStep 3507943 = 5261915) B5261915
theorem B4677257 : Blo 2021435 4677257 := bstep (se 2 (by rfl) ⟨1753971, by rfl⟩ : syracuseStep 4677257 = 3507943) B3507943
theorem B3118171 : Blo 2021435 3118171 := bstep (se 1 (by rfl) ⟨2338628, by rfl⟩ : syracuseStep 3118171 = 4677257) B4677257
theorem B4157561 : Blo 2021435 4157561 := bstep (se 2 (by rfl) ⟨1559085, by rfl⟩ : syracuseStep 4157561 = 3118171) B3118171
theorem B2771707 : Blo 2021435 2771707 := bstep (se 1 (by rfl) ⟨2078780, by rfl⟩ : syracuseStep 2771707 = 4157561) B4157561
theorem B3695609 : Blo 2021435 3695609 := bstep (se 2 (by rfl) ⟨1385853, by rfl⟩ : syracuseStep 3695609 = 2771707) B2771707
theorem B2463739 : Blo 2021435 2463739 := bstep (se 1 (by rfl) ⟨1847804, by rfl⟩ : syracuseStep 2463739 = 3695609) B3695609
theorem B13139941 : Blo 2021435 13139941 := bstep (se 4 (by rfl) ⟨1231869, by rfl⟩ : syracuseStep 13139941 = 2463739) B2463739
theorem B17519921 : Blo 2021435 17519921 := bstep (se 2 (by rfl) ⟨6569970, by rfl⟩ : syracuseStep 17519921 = 13139941) B13139941
theorem B11679947 : Blo 2021435 11679947 := bstep (se 1 (by rfl) ⟨8759960, by rfl⟩ : syracuseStep 11679947 = 17519921) B17519921
theorem B7786631 : Blo 2021435 7786631 := bstep (se 1 (by rfl) ⟨5839973, by rfl⟩ : syracuseStep 7786631 = 11679947) B11679947
theorem B20764349 : Blo 2021435 20764349 := bstep (se 3 (by rfl) ⟨3893315, by rfl⟩ : syracuseStep 20764349 = 7786631) B7786631
theorem B13842899 : Blo 2021435 13842899 := bstep (se 1 (by rfl) ⟨10382174, by rfl⟩ : syracuseStep 13842899 = 20764349) B20764349
theorem B9228599 : Blo 2021435 9228599 := bstep (se 1 (by rfl) ⟨6921449, by rfl⟩ : syracuseStep 9228599 = 13842899) B13842899
theorem B6152399 : Blo 2021435 6152399 := bstep (se 1 (by rfl) ⟨4614299, by rfl⟩ : syracuseStep 6152399 = 9228599) B9228599
theorem B4101599 : Blo 2021435 4101599 := bstep (se 1 (by rfl) ⟨3076199, by rfl⟩ : syracuseStep 4101599 = 6152399) B6152399
theorem B10937597 : Blo 2021435 10937597 := bstep (se 3 (by rfl) ⟨2050799, by rfl⟩ : syracuseStep 10937597 = 4101599) B4101599
theorem B29166925 : Blo 2021435 29166925 := bstep (se 3 (by rfl) ⟨5468798, by rfl⟩ : syracuseStep 29166925 = 10937597) B10937597
theorem B38889233 : Blo 2021435 38889233 := bstep (se 2 (by rfl) ⟨14583462, by rfl⟩ : syracuseStep 38889233 = 29166925) B29166925
theorem B25926155 : Blo 2021435 25926155 := bstep (se 1 (by rfl) ⟨19444616, by rfl⟩ : syracuseStep 25926155 = 38889233) B38889233
theorem B17284103 : Blo 2021435 17284103 := bstep (se 1 (by rfl) ⟨12963077, by rfl⟩ : syracuseStep 17284103 = 25926155) B25926155
theorem B11522735 : Blo 2021435 11522735 := bstep (se 1 (by rfl) ⟨8642051, by rfl⟩ : syracuseStep 11522735 = 17284103) B17284103
theorem B7681823 : Blo 2021435 7681823 := bstep (se 1 (by rfl) ⟨5761367, by rfl⟩ : syracuseStep 7681823 = 11522735) B11522735
theorem B5121215 : Blo 2021435 5121215 := bstep (se 1 (by rfl) ⟨3840911, by rfl⟩ : syracuseStep 5121215 = 7681823) B7681823
theorem B3414143 : Blo 2021435 3414143 := bstep (se 1 (by rfl) ⟨2560607, by rfl⟩ : syracuseStep 3414143 = 5121215) B5121215
theorem B2276095 : Blo 2021435 2276095 := bstep (se 1 (by rfl) ⟨1707071, by rfl⟩ : syracuseStep 2276095 = 3414143) B3414143
theorem B3034793 : Blo 2021435 3034793 := bstep (se 2 (by rfl) ⟨1138047, by rfl⟩ : syracuseStep 3034793 = 2276095) B2276095
theorem B2023195 : Blo 2021435 2023195 := bstep (se 1 (by rfl) ⟨1517396, by rfl⟩ : syracuseStep 2023195 = 3034793) B3034793
theorem B2160517 : Blo 2021435 2160517 := bbase (se 4 (by rfl) ⟨202548, by rfl⟩ : syracuseStep 2160517 = 405097) (by norm_num)
theorem B2880689 : Blo 2021435 2880689 := bstep (se 2 (by rfl) ⟨1080258, by rfl⟩ : syracuseStep 2880689 = 2160517) B2160517
theorem B7681837 : Blo 2021435 7681837 := bstep (se 3 (by rfl) ⟨1440344, by rfl⟩ : syracuseStep 7681837 = 2880689) B2880689
theorem B10242449 : Blo 2021435 10242449 := bstep (se 2 (by rfl) ⟨3840918, by rfl⟩ : syracuseStep 10242449 = 7681837) B7681837
theorem B6828299 : Blo 2021435 6828299 := bstep (se 1 (by rfl) ⟨5121224, by rfl⟩ : syracuseStep 6828299 = 10242449) B10242449
theorem B4552199 : Blo 2021435 4552199 := bstep (se 1 (by rfl) ⟨3414149, by rfl⟩ : syracuseStep 4552199 = 6828299) B6828299
theorem B3034799 : Blo 2021435 3034799 := bstep (se 1 (by rfl) ⟨2276099, by rfl⟩ : syracuseStep 3034799 = 4552199) B4552199
theorem B2023199 : Blo 2021435 2023199 := bstep (se 1 (by rfl) ⟨1517399, by rfl⟩ : syracuseStep 2023199 = 3034799) B3034799
theorem B3034805 : Blo 2021435 3034805 := bbase (se 5 (by rfl) ⟨142256, by rfl⟩ : syracuseStep 3034805 = 284513) (by norm_num)
theorem B2023203 : Blo 2021435 2023203 := bstep (se 1 (by rfl) ⟨1517402, by rfl⟩ : syracuseStep 2023203 = 3034805) B3034805
theorem B5121245 : Blo 2021435 5121245 := bbase (se 3 (by rfl) ⟨960233, by rfl⟩ : syracuseStep 5121245 = 1920467) (by norm_num)
theorem B3414163 : Blo 2021435 3414163 := bstep (se 1 (by rfl) ⟨2560622, by rfl⟩ : syracuseStep 3414163 = 5121245) B5121245
theorem B4552217 : Blo 2021435 4552217 := bstep (se 2 (by rfl) ⟨1707081, by rfl⟩ : syracuseStep 4552217 = 3414163) B3414163
theorem B3034811 : Blo 2021435 3034811 := bstep (se 1 (by rfl) ⟨2276108, by rfl⟩ : syracuseStep 3034811 = 4552217) B4552217
theorem B2023207 : Blo 2021435 2023207 := bstep (se 1 (by rfl) ⟨1517405, by rfl⟩ : syracuseStep 2023207 = 3034811) B3034811
theorem B2276113 : Blo 2021435 2276113 := bbase (se 2 (by rfl) ⟨853542, by rfl⟩ : syracuseStep 2276113 = 1707085) (by norm_num)
theorem B3034817 : Blo 2021435 3034817 := bstep (se 2 (by rfl) ⟨1138056, by rfl⟩ : syracuseStep 3034817 = 2276113) B2276113
theorem B2023211 : Blo 2021435 2023211 := bstep (se 1 (by rfl) ⟨1517408, by rfl⟩ : syracuseStep 2023211 = 3034817) B3034817
theorem B3840949 : Blo 2021435 3840949 := bbase (se 5 (by rfl) ⟨180044, by rfl⟩ : syracuseStep 3840949 = 360089) (by norm_num)
theorem B5121265 : Blo 2021435 5121265 := bstep (se 2 (by rfl) ⟨1920474, by rfl⟩ : syracuseStep 5121265 = 3840949) B3840949
theorem B6828353 : Blo 2021435 6828353 := bstep (se 2 (by rfl) ⟨2560632, by rfl⟩ : syracuseStep 6828353 = 5121265) B5121265
theorem B4552235 : Blo 2021435 4552235 := bstep (se 1 (by rfl) ⟨3414176, by rfl⟩ : syracuseStep 4552235 = 6828353) B6828353
theorem B3034823 : Blo 2021435 3034823 := bstep (se 1 (by rfl) ⟨2276117, by rfl⟩ : syracuseStep 3034823 = 4552235) B4552235
theorem B2023215 : Blo 2021435 2023215 := bstep (se 1 (by rfl) ⟨1517411, by rfl⟩ : syracuseStep 2023215 = 3034823) B3034823
theorem B3034829 : Blo 2021435 3034829 := bbase (se 3 (by rfl) ⟨569030, by rfl⟩ : syracuseStep 3034829 = 1138061) (by norm_num)
theorem B2023219 : Blo 2021435 2023219 := bstep (se 1 (by rfl) ⟨1517414, by rfl⟩ : syracuseStep 2023219 = 3034829) B3034829
theorem B4552253 : Blo 2021435 4552253 := bbase (se 3 (by rfl) ⟨853547, by rfl⟩ : syracuseStep 4552253 = 1707095) (by norm_num)
theorem B3034835 : Blo 2021435 3034835 := bstep (se 1 (by rfl) ⟨2276126, by rfl⟩ : syracuseStep 3034835 = 4552253) B4552253
theorem B2023223 : Blo 2021435 2023223 := bstep (se 1 (by rfl) ⟨1517417, by rfl⟩ : syracuseStep 2023223 = 3034835) B3034835
theorem B3414197 : Blo 2021435 3414197 := bbase (se 5 (by rfl) ⟨160040, by rfl⟩ : syracuseStep 3414197 = 320081) (by norm_num)
theorem B2276131 : Blo 2021435 2276131 := bstep (se 1 (by rfl) ⟨1707098, by rfl⟩ : syracuseStep 2276131 = 3414197) B3414197
theorem B3034841 : Blo 2021435 3034841 := bstep (se 2 (by rfl) ⟨1138065, by rfl⟩ : syracuseStep 3034841 = 2276131) B2276131
theorem B2023227 : Blo 2021435 2023227 := bstep (se 1 (by rfl) ⟨1517420, by rfl⟩ : syracuseStep 2023227 = 3034841) B3034841
theorem B4994797 : Blo 2021435 4994797 := bbase (se 3 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 4994797 = 1873049) (by norm_num)
theorem B6659729 : Blo 2021435 6659729 := bstep (se 2 (by rfl) ⟨2497398, by rfl⟩ : syracuseStep 6659729 = 4994797) B4994797
theorem B4439819 : Blo 2021435 4439819 := bstep (se 1 (by rfl) ⟨3329864, by rfl⟩ : syracuseStep 4439819 = 6659729) B6659729
theorem B11839517 : Blo 2021435 11839517 := bstep (se 3 (by rfl) ⟨2219909, by rfl⟩ : syracuseStep 11839517 = 4439819) B4439819
theorem B7893011 : Blo 2021435 7893011 := bstep (se 1 (by rfl) ⟨5919758, by rfl⟩ : syracuseStep 7893011 = 11839517) B11839517
theorem B21048029 : Blo 2021435 21048029 := bstep (se 3 (by rfl) ⟨3946505, by rfl⟩ : syracuseStep 21048029 = 7893011) B7893011
theorem B14032019 : Blo 2021435 14032019 := bstep (se 1 (by rfl) ⟨10524014, by rfl⟩ : syracuseStep 14032019 = 21048029) B21048029
theorem B9354679 : Blo 2021435 9354679 := bstep (se 1 (by rfl) ⟨7016009, by rfl⟩ : syracuseStep 9354679 = 14032019) B14032019
theorem B49891621 : Blo 2021435 49891621 := bstep (se 4 (by rfl) ⟨4677339, by rfl⟩ : syracuseStep 49891621 = 9354679) B9354679
theorem B66522161 : Blo 2021435 66522161 := bstep (se 2 (by rfl) ⟨24945810, by rfl⟩ : syracuseStep 66522161 = 49891621) B49891621
theorem B44348107 : Blo 2021435 44348107 := bstep (se 1 (by rfl) ⟨33261080, by rfl⟩ : syracuseStep 44348107 = 66522161) B66522161
theorem B59130809 : Blo 2021435 59130809 := bstep (se 2 (by rfl) ⟨22174053, by rfl⟩ : syracuseStep 59130809 = 44348107) B44348107
theorem B39420539 : Blo 2021435 39420539 := bstep (se 1 (by rfl) ⟨29565404, by rfl⟩ : syracuseStep 39420539 = 59130809) B59130809
theorem B26280359 : Blo 2021435 26280359 := bstep (se 1 (by rfl) ⟨19710269, by rfl⟩ : syracuseStep 26280359 = 39420539) B39420539
theorem B17520239 : Blo 2021435 17520239 := bstep (se 1 (by rfl) ⟨13140179, by rfl⟩ : syracuseStep 17520239 = 26280359) B26280359
theorem B11680159 : Blo 2021435 11680159 := bstep (se 1 (by rfl) ⟨8760119, by rfl⟩ : syracuseStep 11680159 = 17520239) B17520239
theorem B15573545 : Blo 2021435 15573545 := bstep (se 2 (by rfl) ⟨5840079, by rfl⟩ : syracuseStep 15573545 = 11680159) B11680159
theorem B10382363 : Blo 2021435 10382363 := bstep (se 1 (by rfl) ⟨7786772, by rfl⟩ : syracuseStep 10382363 = 15573545) B15573545
theorem B6921575 : Blo 2021435 6921575 := bstep (se 1 (by rfl) ⟨5191181, by rfl⟩ : syracuseStep 6921575 = 10382363) B10382363
theorem B4614383 : Blo 2021435 4614383 := bstep (se 1 (by rfl) ⟨3460787, by rfl⟩ : syracuseStep 4614383 = 6921575) B6921575
theorem B3076255 : Blo 2021435 3076255 := bstep (se 1 (by rfl) ⟨2307191, by rfl⟩ : syracuseStep 3076255 = 4614383) B4614383
theorem B4101673 : Blo 2021435 4101673 := bstep (se 2 (by rfl) ⟨1538127, by rfl⟩ : syracuseStep 4101673 = 3076255) B3076255
theorem B5468897 : Blo 2021435 5468897 := bstep (se 2 (by rfl) ⟨2050836, by rfl⟩ : syracuseStep 5468897 = 4101673) B4101673
theorem B3645931 : Blo 2021435 3645931 := bstep (se 1 (by rfl) ⟨2734448, by rfl⟩ : syracuseStep 3645931 = 5468897) B5468897
theorem B4861241 : Blo 2021435 4861241 := bstep (se 2 (by rfl) ⟨1822965, by rfl⟩ : syracuseStep 4861241 = 3645931) B3645931
theorem B3240827 : Blo 2021435 3240827 := bstep (se 1 (by rfl) ⟨2430620, by rfl⟩ : syracuseStep 3240827 = 4861241) B4861241
theorem B2160551 : Blo 2021435 2160551 := bstep (se 1 (by rfl) ⟨1620413, by rfl⟩ : syracuseStep 2160551 = 3240827) B3240827
theorem B5761469 : Blo 2021435 5761469 := bstep (se 3 (by rfl) ⟨1080275, by rfl⟩ : syracuseStep 5761469 = 2160551) B2160551
theorem B15363917 : Blo 2021435 15363917 := bstep (se 3 (by rfl) ⟨2880734, by rfl⟩ : syracuseStep 15363917 = 5761469) B5761469
theorem B10242611 : Blo 2021435 10242611 := bstep (se 1 (by rfl) ⟨7681958, by rfl⟩ : syracuseStep 10242611 = 15363917) B15363917
theorem B6828407 : Blo 2021435 6828407 := bstep (se 1 (by rfl) ⟨5121305, by rfl⟩ : syracuseStep 6828407 = 10242611) B10242611
theorem B4552271 : Blo 2021435 4552271 := bstep (se 1 (by rfl) ⟨3414203, by rfl⟩ : syracuseStep 4552271 = 6828407) B6828407
theorem B3034847 : Blo 2021435 3034847 := bstep (se 1 (by rfl) ⟨2276135, by rfl⟩ : syracuseStep 3034847 = 4552271) B4552271
theorem B2023231 : Blo 2021435 2023231 := bstep (se 1 (by rfl) ⟨1517423, by rfl⟩ : syracuseStep 2023231 = 3034847) B3034847
theorem B3034853 : Blo 2021435 3034853 := bbase (se 4 (by rfl) ⟨284517, by rfl⟩ : syracuseStep 3034853 = 569035) (by norm_num)
theorem B2023235 : Blo 2021435 2023235 := bstep (se 1 (by rfl) ⟨1517426, by rfl⟩ : syracuseStep 2023235 = 3034853) B3034853
theorem B5761493 : Blo 2021435 5761493 := bbase (se 7 (by rfl) ⟨67517, by rfl⟩ : syracuseStep 5761493 = 135035) (by norm_num)
theorem B3840995 : Blo 2021435 3840995 := bstep (se 1 (by rfl) ⟨2880746, by rfl⟩ : syracuseStep 3840995 = 5761493) B5761493
theorem B2560663 : Blo 2021435 2560663 := bstep (se 1 (by rfl) ⟨1920497, by rfl⟩ : syracuseStep 2560663 = 3840995) B3840995
theorem B3414217 : Blo 2021435 3414217 := bstep (se 2 (by rfl) ⟨1280331, by rfl⟩ : syracuseStep 3414217 = 2560663) B2560663
theorem B4552289 : Blo 2021435 4552289 := bstep (se 2 (by rfl) ⟨1707108, by rfl⟩ : syracuseStep 4552289 = 3414217) B3414217
theorem B3034859 : Blo 2021435 3034859 := bstep (se 1 (by rfl) ⟨2276144, by rfl⟩ : syracuseStep 3034859 = 4552289) B4552289
theorem B2023239 : Blo 2021435 2023239 := bstep (se 1 (by rfl) ⟨1517429, by rfl⟩ : syracuseStep 2023239 = 3034859) B3034859
theorem B2276149 : Blo 2021435 2276149 := bbase (se 5 (by rfl) ⟨106694, by rfl⟩ : syracuseStep 2276149 = 213389) (by norm_num)
theorem B3034865 : Blo 2021435 3034865 := bstep (se 2 (by rfl) ⟨1138074, by rfl⟩ : syracuseStep 3034865 = 2276149) B2276149
theorem B2023243 : Blo 2021435 2023243 := bstep (se 1 (by rfl) ⟨1517432, by rfl⟩ : syracuseStep 2023243 = 3034865) B3034865
theorem B2560673 : Blo 2021435 2560673 := bbase (se 2 (by rfl) ⟨960252, by rfl⟩ : syracuseStep 2560673 = 1920505) (by norm_num)
theorem B6828461 : Blo 2021435 6828461 := bstep (se 3 (by rfl) ⟨1280336, by rfl⟩ : syracuseStep 6828461 = 2560673) B2560673
theorem B4552307 : Blo 2021435 4552307 := bstep (se 1 (by rfl) ⟨3414230, by rfl⟩ : syracuseStep 4552307 = 6828461) B6828461
theorem B3034871 : Blo 2021435 3034871 := bstep (se 1 (by rfl) ⟨2276153, by rfl⟩ : syracuseStep 3034871 = 4552307) B4552307
theorem B2023247 : Blo 2021435 2023247 := bstep (se 1 (by rfl) ⟨1517435, by rfl⟩ : syracuseStep 2023247 = 3034871) B3034871
theorem B3034877 : Blo 2021435 3034877 := bbase (se 3 (by rfl) ⟨569039, by rfl⟩ : syracuseStep 3034877 = 1138079) (by norm_num)
theorem B2023251 : Blo 2021435 2023251 := bstep (se 1 (by rfl) ⟨1517438, by rfl⟩ : syracuseStep 2023251 = 3034877) B3034877
theorem B4552325 : Blo 2021435 4552325 := bbase (se 4 (by rfl) ⟨426780, by rfl⟩ : syracuseStep 4552325 = 853561) (by norm_num)
theorem B3034883 : Blo 2021435 3034883 := bstep (se 1 (by rfl) ⟨2276162, by rfl⟩ : syracuseStep 3034883 = 4552325) B4552325
theorem B2023255 : Blo 2021435 2023255 := bstep (se 1 (by rfl) ⟨1517441, by rfl⟩ : syracuseStep 2023255 = 3034883) B3034883
theorem B4861309 : Blo 2021435 4861309 := bbase (se 3 (by rfl) ⟨911495, by rfl⟩ : syracuseStep 4861309 = 1822991) (by norm_num)
theorem B6481745 : Blo 2021435 6481745 := bstep (se 2 (by rfl) ⟨2430654, by rfl⟩ : syracuseStep 6481745 = 4861309) B4861309
theorem B4321163 : Blo 2021435 4321163 := bstep (se 1 (by rfl) ⟨3240872, by rfl⟩ : syracuseStep 4321163 = 6481745) B6481745
theorem B2880775 : Blo 2021435 2880775 := bstep (se 1 (by rfl) ⟨2160581, by rfl⟩ : syracuseStep 2880775 = 4321163) B4321163
theorem B3841033 : Blo 2021435 3841033 := bstep (se 2 (by rfl) ⟨1440387, by rfl⟩ : syracuseStep 3841033 = 2880775) B2880775
theorem B5121377 : Blo 2021435 5121377 := bstep (se 2 (by rfl) ⟨1920516, by rfl⟩ : syracuseStep 5121377 = 3841033) B3841033
theorem B3414251 : Blo 2021435 3414251 := bstep (se 1 (by rfl) ⟨2560688, by rfl⟩ : syracuseStep 3414251 = 5121377) B5121377
theorem B2276167 : Blo 2021435 2276167 := bstep (se 1 (by rfl) ⟨1707125, by rfl⟩ : syracuseStep 2276167 = 3414251) B3414251
theorem B3034889 : Blo 2021435 3034889 := bstep (se 2 (by rfl) ⟨1138083, by rfl⟩ : syracuseStep 3034889 = 2276167) B2276167
theorem B2023259 : Blo 2021435 2023259 := bstep (se 1 (by rfl) ⟨1517444, by rfl⟩ : syracuseStep 2023259 = 3034889) B3034889
theorem B10242773 : Blo 2021435 10242773 := bbase (se 7 (by rfl) ⟨120032, by rfl⟩ : syracuseStep 10242773 = 240065) (by norm_num)
theorem B6828515 : Blo 2021435 6828515 := bstep (se 1 (by rfl) ⟨5121386, by rfl⟩ : syracuseStep 6828515 = 10242773) B10242773
theorem B4552343 : Blo 2021435 4552343 := bstep (se 1 (by rfl) ⟨3414257, by rfl⟩ : syracuseStep 4552343 = 6828515) B6828515
theorem B3034895 : Blo 2021435 3034895 := bstep (se 1 (by rfl) ⟨2276171, by rfl⟩ : syracuseStep 3034895 = 4552343) B4552343
theorem B2023263 : Blo 2021435 2023263 := bstep (se 1 (by rfl) ⟨1517447, by rfl⟩ : syracuseStep 2023263 = 3034895) B3034895
theorem B3034901 : Blo 2021435 3034901 := bbase (se 6 (by rfl) ⟨71130, by rfl⟩ : syracuseStep 3034901 = 142261) (by norm_num)
theorem B2023267 : Blo 2021435 2023267 := bstep (se 1 (by rfl) ⟨1517450, by rfl⟩ : syracuseStep 2023267 = 3034901) B3034901
theorem B24610517 : Blo 2021435 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B16407011 : Blo 2021435 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B10938007 : Blo 2021435 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B58336037 : Blo 2021435 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B38890691 : Blo 2021435 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B25927127 : Blo 2021435 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B17284751 : Blo 2021435 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B11523167 : Blo 2021435 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B7682111 : Blo 2021435 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B5121407 : Blo 2021435 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B3414271 : Blo 2021435 3414271 := bstep (se 1 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 3414271 = 5121407) B5121407
theorem B4552361 : Blo 2021435 4552361 := bstep (se 2 (by rfl) ⟨1707135, by rfl⟩ : syracuseStep 4552361 = 3414271) B3414271
theorem B3034907 : Blo 2021435 3034907 := bstep (se 1 (by rfl) ⟨2276180, by rfl⟩ : syracuseStep 3034907 = 4552361) B4552361
theorem B2023271 : Blo 2021435 2023271 := bstep (se 1 (by rfl) ⟨1517453, by rfl⟩ : syracuseStep 2023271 = 3034907) B3034907
theorem B2276185 : Blo 2021435 2276185 := bbase (se 2 (by rfl) ⟨853569, by rfl⟩ : syracuseStep 2276185 = 1707139) (by norm_num)
theorem B3034913 : Blo 2021435 3034913 := bstep (se 2 (by rfl) ⟨1138092, by rfl⟩ : syracuseStep 3034913 = 2276185) B2276185
theorem B2023275 : Blo 2021435 2023275 := bstep (se 1 (by rfl) ⟨1517456, by rfl⟩ : syracuseStep 2023275 = 3034913) B3034913
theorem B4321205 : Blo 2021435 4321205 := bbase (se 5 (by rfl) ⟨202556, by rfl⟩ : syracuseStep 4321205 = 405113) (by norm_num)
theorem B2880803 : Blo 2021435 2880803 := bstep (se 1 (by rfl) ⟨2160602, by rfl⟩ : syracuseStep 2880803 = 4321205) B4321205
theorem B7682141 : Blo 2021435 7682141 := bstep (se 3 (by rfl) ⟨1440401, by rfl⟩ : syracuseStep 7682141 = 2880803) B2880803
theorem B5121427 : Blo 2021435 5121427 := bstep (se 1 (by rfl) ⟨3841070, by rfl⟩ : syracuseStep 5121427 = 7682141) B7682141
theorem B6828569 : Blo 2021435 6828569 := bstep (se 2 (by rfl) ⟨2560713, by rfl⟩ : syracuseStep 6828569 = 5121427) B5121427
theorem B4552379 : Blo 2021435 4552379 := bstep (se 1 (by rfl) ⟨3414284, by rfl⟩ : syracuseStep 4552379 = 6828569) B6828569
theorem B3034919 : Blo 2021435 3034919 := bstep (se 1 (by rfl) ⟨2276189, by rfl⟩ : syracuseStep 3034919 = 4552379) B4552379
theorem B2023279 : Blo 2021435 2023279 := bstep (se 1 (by rfl) ⟨1517459, by rfl⟩ : syracuseStep 2023279 = 3034919) B3034919
theorem B3034925 : Blo 2021435 3034925 := bbase (se 3 (by rfl) ⟨569048, by rfl⟩ : syracuseStep 3034925 = 1138097) (by norm_num)
theorem B2023283 : Blo 2021435 2023283 := bstep (se 1 (by rfl) ⟨1517462, by rfl⟩ : syracuseStep 2023283 = 3034925) B3034925
theorem B4552397 : Blo 2021435 4552397 := bbase (se 3 (by rfl) ⟨853574, by rfl⟩ : syracuseStep 4552397 = 1707149) (by norm_num)
theorem B3034931 : Blo 2021435 3034931 := bstep (se 1 (by rfl) ⟨2276198, by rfl⟩ : syracuseStep 3034931 = 4552397) B4552397
theorem B2023287 : Blo 2021435 2023287 := bstep (se 1 (by rfl) ⟨1517465, by rfl⟩ : syracuseStep 2023287 = 3034931) B3034931
theorem B2560729 : Blo 2021435 2560729 := bbase (se 2 (by rfl) ⟨960273, by rfl⟩ : syracuseStep 2560729 = 1920547) (by norm_num)
theorem B3414305 : Blo 2021435 3414305 := bstep (se 2 (by rfl) ⟨1280364, by rfl⟩ : syracuseStep 3414305 = 2560729) B2560729
theorem B2276203 : Blo 2021435 2276203 := bstep (se 1 (by rfl) ⟨1707152, by rfl⟩ : syracuseStep 2276203 = 3414305) B3414305
theorem B3034937 : Blo 2021435 3034937 := bstep (se 2 (by rfl) ⟨1138101, by rfl⟩ : syracuseStep 3034937 = 2276203) B2276203
theorem B2023291 : Blo 2021435 2023291 := bstep (se 1 (by rfl) ⟨1517468, by rfl⟩ : syracuseStep 2023291 = 3034937) B3034937
theorem B2430697 : Blo 2021435 2430697 := bbase (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) (by norm_num)
theorem B3240929 : Blo 2021435 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B8642477 : Blo 2021435 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B23046605 : Blo 2021435 23046605 := bstep (se 3 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 23046605 = 8642477) B8642477
theorem B15364403 : Blo 2021435 15364403 := bstep (se 1 (by rfl) ⟨11523302, by rfl⟩ : syracuseStep 15364403 = 23046605) B23046605
theorem B10242935 : Blo 2021435 10242935 := bstep (se 1 (by rfl) ⟨7682201, by rfl⟩ : syracuseStep 10242935 = 15364403) B15364403
theorem B6828623 : Blo 2021435 6828623 := bstep (se 1 (by rfl) ⟨5121467, by rfl⟩ : syracuseStep 6828623 = 10242935) B10242935
theorem B4552415 : Blo 2021435 4552415 := bstep (se 1 (by rfl) ⟨3414311, by rfl⟩ : syracuseStep 4552415 = 6828623) B6828623
theorem B3034943 : Blo 2021435 3034943 := bstep (se 1 (by rfl) ⟨2276207, by rfl⟩ : syracuseStep 3034943 = 4552415) B4552415
theorem B2023295 : Blo 2021435 2023295 := bstep (se 1 (by rfl) ⟨1517471, by rfl⟩ : syracuseStep 2023295 = 3034943) B3034943
theorem B3034949 : Blo 2021435 3034949 := bbase (se 4 (by rfl) ⟨284526, by rfl⟩ : syracuseStep 3034949 = 569053) (by norm_num)
theorem B2023299 : Blo 2021435 2023299 := bstep (se 1 (by rfl) ⟨1517474, by rfl⟩ : syracuseStep 2023299 = 3034949) B3034949
theorem B3414325 : Blo 2021435 3414325 := bbase (se 5 (by rfl) ⟨160046, by rfl⟩ : syracuseStep 3414325 = 320093) (by norm_num)
theorem B4552433 : Blo 2021435 4552433 := bstep (se 2 (by rfl) ⟨1707162, by rfl⟩ : syracuseStep 4552433 = 3414325) B3414325
theorem B3034955 : Blo 2021435 3034955 := bstep (se 1 (by rfl) ⟨2276216, by rfl⟩ : syracuseStep 3034955 = 4552433) B4552433
theorem B2023303 : Blo 2021435 2023303 := bstep (se 1 (by rfl) ⟨1517477, by rfl⟩ : syracuseStep 2023303 = 3034955) B3034955
theorem B2276221 : Blo 2021435 2276221 := bbase (se 3 (by rfl) ⟨426791, by rfl⟩ : syracuseStep 2276221 = 853583) (by norm_num)
theorem B3034961 : Blo 2021435 3034961 := bstep (se 2 (by rfl) ⟨1138110, by rfl⟩ : syracuseStep 3034961 = 2276221) B2276221
theorem B2023307 : Blo 2021435 2023307 := bstep (se 1 (by rfl) ⟨1517480, by rfl⟩ : syracuseStep 2023307 = 3034961) B3034961
theorem B6828677 : Blo 2021435 6828677 := bbase (se 4 (by rfl) ⟨640188, by rfl⟩ : syracuseStep 6828677 = 1280377) (by norm_num)
theorem B4552451 : Blo 2021435 4552451 := bstep (se 1 (by rfl) ⟨3414338, by rfl⟩ : syracuseStep 4552451 = 6828677) B6828677
theorem B3034967 : Blo 2021435 3034967 := bstep (se 1 (by rfl) ⟨2276225, by rfl⟩ : syracuseStep 3034967 = 4552451) B4552451
theorem B2023311 : Blo 2021435 2023311 := bstep (se 1 (by rfl) ⟨1517483, by rfl⟩ : syracuseStep 2023311 = 3034967) B3034967
theorem B3034973 : Blo 2021435 3034973 := bbase (se 3 (by rfl) ⟨569057, by rfl⟩ : syracuseStep 3034973 = 1138115) (by norm_num)
theorem B2023315 : Blo 2021435 2023315 := bstep (se 1 (by rfl) ⟨1517486, by rfl⟩ : syracuseStep 2023315 = 3034973) B3034973
theorem B4552469 : Blo 2021435 4552469 := bbase (se 6 (by rfl) ⟨106698, by rfl⟩ : syracuseStep 4552469 = 213397) (by norm_num)
theorem B3034979 : Blo 2021435 3034979 := bstep (se 1 (by rfl) ⟨2276234, by rfl⟩ : syracuseStep 3034979 = 4552469) B4552469
theorem B2023319 : Blo 2021435 2023319 := bstep (se 1 (by rfl) ⟨1517489, by rfl⟩ : syracuseStep 2023319 = 3034979) B3034979
theorem B7682309 : Blo 2021435 7682309 := bbase (se 4 (by rfl) ⟨720216, by rfl⟩ : syracuseStep 7682309 = 1440433) (by norm_num)
theorem B5121539 : Blo 2021435 5121539 := bstep (se 1 (by rfl) ⟨3841154, by rfl⟩ : syracuseStep 5121539 = 7682309) B7682309
theorem B3414359 : Blo 2021435 3414359 := bstep (se 1 (by rfl) ⟨2560769, by rfl⟩ : syracuseStep 3414359 = 5121539) B5121539
theorem B2276239 : Blo 2021435 2276239 := bstep (se 1 (by rfl) ⟨1707179, by rfl⟩ : syracuseStep 2276239 = 3414359) B3414359
theorem B3034985 : Blo 2021435 3034985 := bstep (se 2 (by rfl) ⟨1138119, by rfl⟩ : syracuseStep 3034985 = 2276239) B2276239
theorem B2023323 : Blo 2021435 2023323 := bstep (se 1 (by rfl) ⟨1517492, by rfl⟩ : syracuseStep 2023323 = 3034985) B3034985
theorem B2190133 : Blo 2021435 2190133 := bbase (se 5 (by rfl) ⟨102662, by rfl⟩ : syracuseStep 2190133 = 205325) (by norm_num)
theorem B2920177 : Blo 2021435 2920177 := bstep (se 2 (by rfl) ⟨1095066, by rfl⟩ : syracuseStep 2920177 = 2190133) B2190133
theorem B15574277 : Blo 2021435 15574277 := bstep (se 4 (by rfl) ⟨1460088, by rfl⟩ : syracuseStep 15574277 = 2920177) B2920177
theorem B10382851 : Blo 2021435 10382851 := bstep (se 1 (by rfl) ⟨7787138, by rfl⟩ : syracuseStep 10382851 = 15574277) B15574277
theorem B13843801 : Blo 2021435 13843801 := bstep (se 2 (by rfl) ⟨5191425, by rfl⟩ : syracuseStep 13843801 = 10382851) B10382851
theorem B18458401 : Blo 2021435 18458401 := bstep (se 2 (by rfl) ⟨6921900, by rfl⟩ : syracuseStep 18458401 = 13843801) B13843801
theorem B24611201 : Blo 2021435 24611201 := bstep (se 2 (by rfl) ⟨9229200, by rfl⟩ : syracuseStep 24611201 = 18458401) B18458401
theorem B16407467 : Blo 2021435 16407467 := bstep (se 1 (by rfl) ⟨12305600, by rfl⟩ : syracuseStep 16407467 = 24611201) B24611201
theorem B10938311 : Blo 2021435 10938311 := bstep (se 1 (by rfl) ⟨8203733, by rfl⟩ : syracuseStep 10938311 = 16407467) B16407467
theorem B7292207 : Blo 2021435 7292207 := bstep (se 1 (by rfl) ⟨5469155, by rfl⟩ : syracuseStep 7292207 = 10938311) B10938311
theorem B4861471 : Blo 2021435 4861471 := bstep (se 1 (by rfl) ⟨3646103, by rfl⟩ : syracuseStep 4861471 = 7292207) B7292207
theorem B6481961 : Blo 2021435 6481961 := bstep (se 2 (by rfl) ⟨2430735, by rfl⟩ : syracuseStep 6481961 = 4861471) B4861471
theorem B4321307 : Blo 2021435 4321307 := bstep (se 1 (by rfl) ⟨3240980, by rfl⟩ : syracuseStep 4321307 = 6481961) B6481961
theorem B11523485 : Blo 2021435 11523485 := bstep (se 3 (by rfl) ⟨2160653, by rfl⟩ : syracuseStep 11523485 = 4321307) B4321307
theorem B7682323 : Blo 2021435 7682323 := bstep (se 1 (by rfl) ⟨5761742, by rfl⟩ : syracuseStep 7682323 = 11523485) B11523485
theorem B10243097 : Blo 2021435 10243097 := bstep (se 2 (by rfl) ⟨3841161, by rfl⟩ : syracuseStep 10243097 = 7682323) B7682323
theorem B6828731 : Blo 2021435 6828731 := bstep (se 1 (by rfl) ⟨5121548, by rfl⟩ : syracuseStep 6828731 = 10243097) B10243097
theorem B4552487 : Blo 2021435 4552487 := bstep (se 1 (by rfl) ⟨3414365, by rfl⟩ : syracuseStep 4552487 = 6828731) B6828731
theorem B3034991 : Blo 2021435 3034991 := bstep (se 1 (by rfl) ⟨2276243, by rfl⟩ : syracuseStep 3034991 = 4552487) B4552487
theorem B2023327 : Blo 2021435 2023327 := bstep (se 1 (by rfl) ⟨1517495, by rfl⟩ : syracuseStep 2023327 = 3034991) B3034991
theorem B3034997 : Blo 2021435 3034997 := bbase (se 5 (by rfl) ⟨142265, by rfl⟩ : syracuseStep 3034997 = 284531) (by norm_num)
theorem B2023331 : Blo 2021435 2023331 := bstep (se 1 (by rfl) ⟨1517498, by rfl⟩ : syracuseStep 2023331 = 3034997) B3034997
theorem B4321325 : Blo 2021435 4321325 := bbase (se 3 (by rfl) ⟨810248, by rfl⟩ : syracuseStep 4321325 = 1620497) (by norm_num)
theorem B2880883 : Blo 2021435 2880883 := bstep (se 1 (by rfl) ⟨2160662, by rfl⟩ : syracuseStep 2880883 = 4321325) B4321325
theorem B3841177 : Blo 2021435 3841177 := bstep (se 2 (by rfl) ⟨1440441, by rfl⟩ : syracuseStep 3841177 = 2880883) B2880883
theorem B5121569 : Blo 2021435 5121569 := bstep (se 2 (by rfl) ⟨1920588, by rfl⟩ : syracuseStep 5121569 = 3841177) B3841177
theorem B3414379 : Blo 2021435 3414379 := bstep (se 1 (by rfl) ⟨2560784, by rfl⟩ : syracuseStep 3414379 = 5121569) B5121569
theorem B4552505 : Blo 2021435 4552505 := bstep (se 2 (by rfl) ⟨1707189, by rfl⟩ : syracuseStep 4552505 = 3414379) B3414379
theorem B3035003 : Blo 2021435 3035003 := bstep (se 1 (by rfl) ⟨2276252, by rfl⟩ : syracuseStep 3035003 = 4552505) B4552505
theorem B2023335 : Blo 2021435 2023335 := bstep (se 1 (by rfl) ⟨1517501, by rfl⟩ : syracuseStep 2023335 = 3035003) B3035003
theorem B2276257 : Blo 2021435 2276257 := bbase (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) (by norm_num)
theorem B3035009 : Blo 2021435 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B2023339 : Blo 2021435 2023339 := bstep (se 1 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 2023339 = 3035009) B3035009
theorem B5121589 : Blo 2021435 5121589 := bbase (se 5 (by rfl) ⟨240074, by rfl⟩ : syracuseStep 5121589 = 480149) (by norm_num)
theorem B6828785 : Blo 2021435 6828785 := bstep (se 2 (by rfl) ⟨2560794, by rfl⟩ : syracuseStep 6828785 = 5121589) B5121589
theorem B4552523 : Blo 2021435 4552523 := bstep (se 1 (by rfl) ⟨3414392, by rfl⟩ : syracuseStep 4552523 = 6828785) B6828785
theorem B3035015 : Blo 2021435 3035015 := bstep (se 1 (by rfl) ⟨2276261, by rfl⟩ : syracuseStep 3035015 = 4552523) B4552523
theorem B2023343 : Blo 2021435 2023343 := bstep (se 1 (by rfl) ⟨1517507, by rfl⟩ : syracuseStep 2023343 = 3035015) B3035015
theorem B3035021 : Blo 2021435 3035021 := bbase (se 3 (by rfl) ⟨569066, by rfl⟩ : syracuseStep 3035021 = 1138133) (by norm_num)
theorem B2023347 : Blo 2021435 2023347 := bstep (se 1 (by rfl) ⟨1517510, by rfl⟩ : syracuseStep 2023347 = 3035021) B3035021
theorem B4552541 : Blo 2021435 4552541 := bbase (se 3 (by rfl) ⟨853601, by rfl⟩ : syracuseStep 4552541 = 1707203) (by norm_num)
theorem B3035027 : Blo 2021435 3035027 := bstep (se 1 (by rfl) ⟨2276270, by rfl⟩ : syracuseStep 3035027 = 4552541) B4552541
theorem B2023351 : Blo 2021435 2023351 := bstep (se 1 (by rfl) ⟨1517513, by rfl⟩ : syracuseStep 2023351 = 3035027) B3035027
theorem B3414413 : Blo 2021435 3414413 := bbase (se 3 (by rfl) ⟨640202, by rfl⟩ : syracuseStep 3414413 = 1280405) (by norm_num)
theorem B2276275 : Blo 2021435 2276275 := bstep (se 1 (by rfl) ⟨1707206, by rfl⟩ : syracuseStep 2276275 = 3414413) B3414413
theorem B3035033 : Blo 2021435 3035033 := bstep (se 2 (by rfl) ⟨1138137, by rfl⟩ : syracuseStep 3035033 = 2276275) B2276275
theorem B2023355 : Blo 2021435 2023355 := bstep (se 1 (by rfl) ⟨1517516, by rfl⟩ : syracuseStep 2023355 = 3035033) B3035033
theorem B3461005 : Blo 2021435 3461005 := bbase (se 3 (by rfl) ⟨648938, by rfl⟩ : syracuseStep 3461005 = 1297877) (by norm_num)
theorem B4614673 : Blo 2021435 4614673 := bstep (se 2 (by rfl) ⟨1730502, by rfl⟩ : syracuseStep 4614673 = 3461005) B3461005
theorem B6152897 : Blo 2021435 6152897 := bstep (se 2 (by rfl) ⟨2307336, by rfl⟩ : syracuseStep 6152897 = 4614673) B4614673
theorem B4101931 : Blo 2021435 4101931 := bstep (se 1 (by rfl) ⟨3076448, by rfl⟩ : syracuseStep 4101931 = 6152897) B6152897
theorem B21876965 : Blo 2021435 21876965 := bstep (se 4 (by rfl) ⟨2050965, by rfl⟩ : syracuseStep 21876965 = 4101931) B4101931
theorem B14584643 : Blo 2021435 14584643 := bstep (se 1 (by rfl) ⟨10938482, by rfl⟩ : syracuseStep 14584643 = 21876965) B21876965
theorem B9723095 : Blo 2021435 9723095 := bstep (se 1 (by rfl) ⟨7292321, by rfl⟩ : syracuseStep 9723095 = 14584643) B14584643
theorem B6482063 : Blo 2021435 6482063 := bstep (se 1 (by rfl) ⟨4861547, by rfl⟩ : syracuseStep 6482063 = 9723095) B9723095
theorem B17285501 : Blo 2021435 17285501 := bstep (se 3 (by rfl) ⟨3241031, by rfl⟩ : syracuseStep 17285501 = 6482063) B6482063
theorem B11523667 : Blo 2021435 11523667 := bstep (se 1 (by rfl) ⟨8642750, by rfl⟩ : syracuseStep 11523667 = 17285501) B17285501
theorem B15364889 : Blo 2021435 15364889 := bstep (se 2 (by rfl) ⟨5761833, by rfl⟩ : syracuseStep 15364889 = 11523667) B11523667
theorem B10243259 : Blo 2021435 10243259 := bstep (se 1 (by rfl) ⟨7682444, by rfl⟩ : syracuseStep 10243259 = 15364889) B15364889
theorem B6828839 : Blo 2021435 6828839 := bstep (se 1 (by rfl) ⟨5121629, by rfl⟩ : syracuseStep 6828839 = 10243259) B10243259
theorem B4552559 : Blo 2021435 4552559 := bstep (se 1 (by rfl) ⟨3414419, by rfl⟩ : syracuseStep 4552559 = 6828839) B6828839
theorem B3035039 : Blo 2021435 3035039 := bstep (se 1 (by rfl) ⟨2276279, by rfl⟩ : syracuseStep 3035039 = 4552559) B4552559
theorem B2023359 : Blo 2021435 2023359 := bstep (se 1 (by rfl) ⟨1517519, by rfl⟩ : syracuseStep 2023359 = 3035039) B3035039
theorem B3035045 : Blo 2021435 3035045 := bbase (se 4 (by rfl) ⟨284535, by rfl⟩ : syracuseStep 3035045 = 569071) (by norm_num)
theorem B2023363 : Blo 2021435 2023363 := bstep (se 1 (by rfl) ⟨1517522, by rfl⟩ : syracuseStep 2023363 = 3035045) B3035045
theorem B2560825 : Blo 2021435 2560825 := bbase (se 2 (by rfl) ⟨960309, by rfl⟩ : syracuseStep 2560825 = 1920619) (by norm_num)
theorem B3414433 : Blo 2021435 3414433 := bstep (se 2 (by rfl) ⟨1280412, by rfl⟩ : syracuseStep 3414433 = 2560825) B2560825
theorem B4552577 : Blo 2021435 4552577 := bstep (se 2 (by rfl) ⟨1707216, by rfl⟩ : syracuseStep 4552577 = 3414433) B3414433
theorem B3035051 : Blo 2021435 3035051 := bstep (se 1 (by rfl) ⟨2276288, by rfl⟩ : syracuseStep 3035051 = 4552577) B4552577
theorem B2023367 : Blo 2021435 2023367 := bstep (se 1 (by rfl) ⟨1517525, by rfl⟩ : syracuseStep 2023367 = 3035051) B3035051
theorem B2276293 : Blo 2021435 2276293 := bbase (se 4 (by rfl) ⟨213402, by rfl⟩ : syracuseStep 2276293 = 426805) (by norm_num)
theorem B3035057 : Blo 2021435 3035057 := bstep (se 2 (by rfl) ⟨1138146, by rfl⟩ : syracuseStep 3035057 = 2276293) B2276293
theorem B2023371 : Blo 2021435 2023371 := bstep (se 1 (by rfl) ⟨1517528, by rfl⟩ : syracuseStep 2023371 = 3035057) B3035057
theorem B3841253 : Blo 2021435 3841253 := bbase (se 4 (by rfl) ⟨360117, by rfl⟩ : syracuseStep 3841253 = 720235) (by norm_num)
theorem B2560835 : Blo 2021435 2560835 := bstep (se 1 (by rfl) ⟨1920626, by rfl⟩ : syracuseStep 2560835 = 3841253) B3841253
theorem B6828893 : Blo 2021435 6828893 := bstep (se 3 (by rfl) ⟨1280417, by rfl⟩ : syracuseStep 6828893 = 2560835) B2560835
theorem B4552595 : Blo 2021435 4552595 := bstep (se 1 (by rfl) ⟨3414446, by rfl⟩ : syracuseStep 4552595 = 6828893) B6828893
theorem B3035063 : Blo 2021435 3035063 := bstep (se 1 (by rfl) ⟨2276297, by rfl⟩ : syracuseStep 3035063 = 4552595) B4552595
theorem B2023375 : Blo 2021435 2023375 := bstep (se 1 (by rfl) ⟨1517531, by rfl⟩ : syracuseStep 2023375 = 3035063) B3035063
theorem B3035069 : Blo 2021435 3035069 := bbase (se 3 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 3035069 = 1138151) (by norm_num)
theorem B2023379 : Blo 2021435 2023379 := bstep (se 1 (by rfl) ⟨1517534, by rfl⟩ : syracuseStep 2023379 = 3035069) B3035069
theorem B4552613 : Blo 2021435 4552613 := bbase (se 4 (by rfl) ⟨426807, by rfl⟩ : syracuseStep 4552613 = 853615) (by norm_num)
theorem B3035075 : Blo 2021435 3035075 := bstep (se 1 (by rfl) ⟨2276306, by rfl⟩ : syracuseStep 3035075 = 4552613) B4552613
theorem B2023383 : Blo 2021435 2023383 := bstep (se 1 (by rfl) ⟨1517537, by rfl⟩ : syracuseStep 2023383 = 3035075) B3035075
theorem B5121701 : Blo 2021435 5121701 := bbase (se 4 (by rfl) ⟨480159, by rfl⟩ : syracuseStep 5121701 = 960319) (by norm_num)
theorem B3414467 : Blo 2021435 3414467 := bstep (se 1 (by rfl) ⟨2560850, by rfl⟩ : syracuseStep 3414467 = 5121701) B5121701
theorem B2276311 : Blo 2021435 2276311 := bstep (se 1 (by rfl) ⟨1707233, by rfl⟩ : syracuseStep 2276311 = 3414467) B3414467
theorem B3035081 : Blo 2021435 3035081 := bstep (se 2 (by rfl) ⟨1138155, by rfl⟩ : syracuseStep 3035081 = 2276311) B2276311
theorem B2023387 : Blo 2021435 2023387 := bstep (se 1 (by rfl) ⟨1517540, by rfl⟩ : syracuseStep 2023387 = 3035081) B3035081
theorem B5761925 : Blo 2021435 5761925 := bbase (se 4 (by rfl) ⟨540180, by rfl⟩ : syracuseStep 5761925 = 1080361) (by norm_num)
theorem B3841283 : Blo 2021435 3841283 := bstep (se 1 (by rfl) ⟨2880962, by rfl⟩ : syracuseStep 3841283 = 5761925) B5761925
theorem B10243421 : Blo 2021435 10243421 := bstep (se 3 (by rfl) ⟨1920641, by rfl⟩ : syracuseStep 10243421 = 3841283) B3841283
theorem B6828947 : Blo 2021435 6828947 := bstep (se 1 (by rfl) ⟨5121710, by rfl⟩ : syracuseStep 6828947 = 10243421) B10243421
theorem B4552631 : Blo 2021435 4552631 := bstep (se 1 (by rfl) ⟨3414473, by rfl⟩ : syracuseStep 4552631 = 6828947) B6828947
theorem B3035087 : Blo 2021435 3035087 := bstep (se 1 (by rfl) ⟨2276315, by rfl⟩ : syracuseStep 3035087 = 4552631) B4552631
theorem B2023391 : Blo 2021435 2023391 := bstep (se 1 (by rfl) ⟨1517543, by rfl⟩ : syracuseStep 2023391 = 3035087) B3035087
theorem B3035093 : Blo 2021435 3035093 := bbase (se 7 (by rfl) ⟨35567, by rfl⟩ : syracuseStep 3035093 = 71135) (by norm_num)
theorem B2023395 : Blo 2021435 2023395 := bstep (se 1 (by rfl) ⟨1517546, by rfl⟩ : syracuseStep 2023395 = 3035093) B3035093
theorem B7682597 : Blo 2021435 7682597 := bbase (se 4 (by rfl) ⟨720243, by rfl⟩ : syracuseStep 7682597 = 1440487) (by norm_num)
theorem B5121731 : Blo 2021435 5121731 := bstep (se 1 (by rfl) ⟨3841298, by rfl⟩ : syracuseStep 5121731 = 7682597) B7682597
theorem B3414487 : Blo 2021435 3414487 := bstep (se 1 (by rfl) ⟨2560865, by rfl⟩ : syracuseStep 3414487 = 5121731) B5121731
theorem B4552649 : Blo 2021435 4552649 := bstep (se 2 (by rfl) ⟨1707243, by rfl⟩ : syracuseStep 4552649 = 3414487) B3414487
theorem B3035099 : Blo 2021435 3035099 := bstep (se 1 (by rfl) ⟨2276324, by rfl⟩ : syracuseStep 3035099 = 4552649) B4552649
theorem B2023399 : Blo 2021435 2023399 := bstep (se 1 (by rfl) ⟨1517549, by rfl⟩ : syracuseStep 2023399 = 3035099) B3035099
theorem B2276329 : Blo 2021435 2276329 := bbase (se 2 (by rfl) ⟨853623, by rfl⟩ : syracuseStep 2276329 = 1707247) (by norm_num)
theorem B3035105 : Blo 2021435 3035105 := bstep (se 2 (by rfl) ⟨1138164, by rfl⟩ : syracuseStep 3035105 = 2276329) B2276329
theorem B2023403 : Blo 2021435 2023403 := bstep (se 1 (by rfl) ⟨1517552, by rfl⟩ : syracuseStep 2023403 = 3035105) B3035105
theorem B3241109 : Blo 2021435 3241109 := bbase (se 6 (by rfl) ⟨75963, by rfl⟩ : syracuseStep 3241109 = 151927) (by norm_num)
theorem B2160739 : Blo 2021435 2160739 := bstep (se 1 (by rfl) ⟨1620554, by rfl⟩ : syracuseStep 2160739 = 3241109) B3241109
theorem B11523941 : Blo 2021435 11523941 := bstep (se 4 (by rfl) ⟨1080369, by rfl⟩ : syracuseStep 11523941 = 2160739) B2160739
theorem B7682627 : Blo 2021435 7682627 := bstep (se 1 (by rfl) ⟨5761970, by rfl⟩ : syracuseStep 7682627 = 11523941) B11523941
theorem B5121751 : Blo 2021435 5121751 := bstep (se 1 (by rfl) ⟨3841313, by rfl⟩ : syracuseStep 5121751 = 7682627) B7682627
theorem B6829001 : Blo 2021435 6829001 := bstep (se 2 (by rfl) ⟨2560875, by rfl⟩ : syracuseStep 6829001 = 5121751) B5121751
theorem B4552667 : Blo 2021435 4552667 := bstep (se 1 (by rfl) ⟨3414500, by rfl⟩ : syracuseStep 4552667 = 6829001) B6829001
theorem B3035111 : Blo 2021435 3035111 := bstep (se 1 (by rfl) ⟨2276333, by rfl⟩ : syracuseStep 3035111 = 4552667) B4552667
theorem B2023407 : Blo 2021435 2023407 := bstep (se 1 (by rfl) ⟨1517555, by rfl⟩ : syracuseStep 2023407 = 3035111) B3035111
theorem B3035117 : Blo 2021435 3035117 := bbase (se 3 (by rfl) ⟨569084, by rfl⟩ : syracuseStep 3035117 = 1138169) (by norm_num)
theorem B2023411 : Blo 2021435 2023411 := bstep (se 1 (by rfl) ⟨1517558, by rfl⟩ : syracuseStep 2023411 = 3035117) B3035117
theorem B4552685 : Blo 2021435 4552685 := bbase (se 3 (by rfl) ⟨853628, by rfl⟩ : syracuseStep 4552685 = 1707257) (by norm_num)
theorem B3035123 : Blo 2021435 3035123 := bstep (se 1 (by rfl) ⟨2276342, by rfl⟩ : syracuseStep 3035123 = 4552685) B4552685
theorem B2023415 : Blo 2021435 2023415 := bstep (se 1 (by rfl) ⟨1517561, by rfl⟩ : syracuseStep 2023415 = 3035123) B3035123
theorem B2667149 : Blo 2021435 2667149 := bbase (se 3 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 2667149 = 1000181) (by norm_num)
theorem B28449589 : Blo 2021435 28449589 := bstep (se 5 (by rfl) ⟨1333574, by rfl⟩ : syracuseStep 28449589 = 2667149) B2667149
theorem B37932785 : Blo 2021435 37932785 := bstep (se 2 (by rfl) ⟨14224794, by rfl⟩ : syracuseStep 37932785 = 28449589) B28449589
theorem B25288523 : Blo 2021435 25288523 := bstep (se 1 (by rfl) ⟨18966392, by rfl⟩ : syracuseStep 25288523 = 37932785) B37932785
theorem B16859015 : Blo 2021435 16859015 := bstep (se 1 (by rfl) ⟨12644261, by rfl⟩ : syracuseStep 16859015 = 25288523) B25288523
theorem B11239343 : Blo 2021435 11239343 := bstep (se 1 (by rfl) ⟨8429507, by rfl⟩ : syracuseStep 11239343 = 16859015) B16859015
theorem B7492895 : Blo 2021435 7492895 := bstep (se 1 (by rfl) ⟨5619671, by rfl⟩ : syracuseStep 7492895 = 11239343) B11239343
theorem B4995263 : Blo 2021435 4995263 := bstep (se 1 (by rfl) ⟨3746447, by rfl⟩ : syracuseStep 4995263 = 7492895) B7492895
theorem B3330175 : Blo 2021435 3330175 := bstep (se 1 (by rfl) ⟨2497631, by rfl⟩ : syracuseStep 3330175 = 4995263) B4995263
theorem B4440233 : Blo 2021435 4440233 := bstep (se 2 (by rfl) ⟨1665087, by rfl⟩ : syracuseStep 4440233 = 3330175) B3330175
theorem B2960155 : Blo 2021435 2960155 := bstep (se 1 (by rfl) ⟨2220116, by rfl⟩ : syracuseStep 2960155 = 4440233) B4440233
theorem B15787493 : Blo 2021435 15787493 := bstep (se 4 (by rfl) ⟨1480077, by rfl⟩ : syracuseStep 15787493 = 2960155) B2960155
theorem B10524995 : Blo 2021435 10524995 := bstep (se 1 (by rfl) ⟨7893746, by rfl⟩ : syracuseStep 10524995 = 15787493) B15787493
theorem B7016663 : Blo 2021435 7016663 := bstep (se 1 (by rfl) ⟨5262497, by rfl⟩ : syracuseStep 7016663 = 10524995) B10524995
theorem B18711101 : Blo 2021435 18711101 := bstep (se 3 (by rfl) ⟨3508331, by rfl⟩ : syracuseStep 18711101 = 7016663) B7016663
theorem B49896269 : Blo 2021435 49896269 := bstep (se 3 (by rfl) ⟨9355550, by rfl⟩ : syracuseStep 49896269 = 18711101) B18711101
theorem B33264179 : Blo 2021435 33264179 := bstep (se 1 (by rfl) ⟨24948134, by rfl⟩ : syracuseStep 33264179 = 49896269) B49896269
theorem B22176119 : Blo 2021435 22176119 := bstep (se 1 (by rfl) ⟨16632089, by rfl⟩ : syracuseStep 22176119 = 33264179) B33264179
theorem B14784079 : Blo 2021435 14784079 := bstep (se 1 (by rfl) ⟨11088059, by rfl⟩ : syracuseStep 14784079 = 22176119) B22176119
theorem B19712105 : Blo 2021435 19712105 := bstep (se 2 (by rfl) ⟨7392039, by rfl⟩ : syracuseStep 19712105 = 14784079) B14784079
theorem B13141403 : Blo 2021435 13141403 := bstep (se 1 (by rfl) ⟨9856052, by rfl⟩ : syracuseStep 13141403 = 19712105) B19712105
theorem B8760935 : Blo 2021435 8760935 := bstep (se 1 (by rfl) ⟨6570701, by rfl⟩ : syracuseStep 8760935 = 13141403) B13141403
theorem B5840623 : Blo 2021435 5840623 := bstep (se 1 (by rfl) ⟨4380467, by rfl⟩ : syracuseStep 5840623 = 8760935) B8760935
theorem B7787497 : Blo 2021435 7787497 := bstep (se 2 (by rfl) ⟨2920311, by rfl⟩ : syracuseStep 7787497 = 5840623) B5840623
theorem B10383329 : Blo 2021435 10383329 := bstep (se 2 (by rfl) ⟨3893748, by rfl⟩ : syracuseStep 10383329 = 7787497) B7787497
theorem B27688877 : Blo 2021435 27688877 := bstep (se 3 (by rfl) ⟨5191664, by rfl⟩ : syracuseStep 27688877 = 10383329) B10383329
theorem B18459251 : Blo 2021435 18459251 := bstep (se 1 (by rfl) ⟨13844438, by rfl⟩ : syracuseStep 18459251 = 27688877) B27688877
theorem B12306167 : Blo 2021435 12306167 := bstep (se 1 (by rfl) ⟨9229625, by rfl⟩ : syracuseStep 12306167 = 18459251) B18459251
theorem B8204111 : Blo 2021435 8204111 := bstep (se 1 (by rfl) ⟨6153083, by rfl⟩ : syracuseStep 8204111 = 12306167) B12306167
theorem B5469407 : Blo 2021435 5469407 := bstep (se 1 (by rfl) ⟨4102055, by rfl⟩ : syracuseStep 5469407 = 8204111) B8204111
theorem B3646271 : Blo 2021435 3646271 := bstep (se 1 (by rfl) ⟨2734703, by rfl⟩ : syracuseStep 3646271 = 5469407) B5469407
theorem B2430847 : Blo 2021435 2430847 := bstep (se 1 (by rfl) ⟨1823135, by rfl⟩ : syracuseStep 2430847 = 3646271) B3646271
theorem B3241129 : Blo 2021435 3241129 := bstep (se 2 (by rfl) ⟨1215423, by rfl⟩ : syracuseStep 3241129 = 2430847) B2430847
theorem B4321505 : Blo 2021435 4321505 := bstep (se 2 (by rfl) ⟨1620564, by rfl⟩ : syracuseStep 4321505 = 3241129) B3241129
theorem B2881003 : Blo 2021435 2881003 := bstep (se 1 (by rfl) ⟨2160752, by rfl⟩ : syracuseStep 2881003 = 4321505) B4321505
theorem B3841337 : Blo 2021435 3841337 := bstep (se 2 (by rfl) ⟨1440501, by rfl⟩ : syracuseStep 3841337 = 2881003) B2881003
theorem B2560891 : Blo 2021435 2560891 := bstep (se 1 (by rfl) ⟨1920668, by rfl⟩ : syracuseStep 2560891 = 3841337) B3841337
theorem B3414521 : Blo 2021435 3414521 := bstep (se 2 (by rfl) ⟨1280445, by rfl⟩ : syracuseStep 3414521 = 2560891) B2560891
theorem B2276347 : Blo 2021435 2276347 := bstep (se 1 (by rfl) ⟨1707260, by rfl⟩ : syracuseStep 2276347 = 3414521) B3414521
theorem B3035129 : Blo 2021435 3035129 := bstep (se 2 (by rfl) ⟨1138173, by rfl⟩ : syracuseStep 3035129 = 2276347) B2276347
theorem B2023419 : Blo 2021435 2023419 := bstep (se 1 (by rfl) ⟨1517564, by rfl⟩ : syracuseStep 2023419 = 3035129) B3035129
theorem B5840629 : Blo 2021435 5840629 := bbase (se 5 (by rfl) ⟨273779, by rfl⟩ : syracuseStep 5840629 = 547559) (by norm_num)
theorem B31150021 : Blo 2021435 31150021 := bstep (se 4 (by rfl) ⟨2920314, by rfl⟩ : syracuseStep 31150021 = 5840629) B5840629
theorem B41533361 : Blo 2021435 41533361 := bstep (se 2 (by rfl) ⟨15575010, by rfl⟩ : syracuseStep 41533361 = 31150021) B31150021
theorem B27688907 : Blo 2021435 27688907 := bstep (se 1 (by rfl) ⟨20766680, by rfl⟩ : syracuseStep 27688907 = 41533361) B41533361
theorem B18459271 : Blo 2021435 18459271 := bstep (se 1 (by rfl) ⟨13844453, by rfl⟩ : syracuseStep 18459271 = 27688907) B27688907
theorem B98449445 : Blo 2021435 98449445 := bstep (se 4 (by rfl) ⟨9229635, by rfl⟩ : syracuseStep 98449445 = 18459271) B18459271
theorem B262531853 : Blo 2021435 262531853 := bstep (se 3 (by rfl) ⟨49224722, by rfl⟩ : syracuseStep 262531853 = 98449445) B98449445
theorem B175021235 : Blo 2021435 175021235 := bstep (se 1 (by rfl) ⟨131265926, by rfl⟩ : syracuseStep 175021235 = 262531853) B262531853
theorem B116680823 : Blo 2021435 116680823 := bstep (se 1 (by rfl) ⟨87510617, by rfl⟩ : syracuseStep 116680823 = 175021235) B175021235
theorem B77787215 : Blo 2021435 77787215 := bstep (se 1 (by rfl) ⟨58340411, by rfl⟩ : syracuseStep 77787215 = 116680823) B116680823
theorem B51858143 : Blo 2021435 51858143 := bstep (se 1 (by rfl) ⟨38893607, by rfl⟩ : syracuseStep 51858143 = 77787215) B77787215
theorem B34572095 : Blo 2021435 34572095 := bstep (se 1 (by rfl) ⟨25929071, by rfl⟩ : syracuseStep 34572095 = 51858143) B51858143
theorem B23048063 : Blo 2021435 23048063 := bstep (se 1 (by rfl) ⟨17286047, by rfl⟩ : syracuseStep 23048063 = 34572095) B34572095
theorem B15365375 : Blo 2021435 15365375 := bstep (se 1 (by rfl) ⟨11524031, by rfl⟩ : syracuseStep 15365375 = 23048063) B23048063
theorem B10243583 : Blo 2021435 10243583 := bstep (se 1 (by rfl) ⟨7682687, by rfl⟩ : syracuseStep 10243583 = 15365375) B15365375
theorem B6829055 : Blo 2021435 6829055 := bstep (se 1 (by rfl) ⟨5121791, by rfl⟩ : syracuseStep 6829055 = 10243583) B10243583
theorem B4552703 : Blo 2021435 4552703 := bstep (se 1 (by rfl) ⟨3414527, by rfl⟩ : syracuseStep 4552703 = 6829055) B6829055
theorem B3035135 : Blo 2021435 3035135 := bstep (se 1 (by rfl) ⟨2276351, by rfl⟩ : syracuseStep 3035135 = 4552703) B4552703
theorem B2023423 : Blo 2021435 2023423 := bstep (se 1 (by rfl) ⟨1517567, by rfl⟩ : syracuseStep 2023423 = 3035135) B3035135
theorem B3035141 : Blo 2021435 3035141 := bbase (se 4 (by rfl) ⟨284544, by rfl⟩ : syracuseStep 3035141 = 569089) (by norm_num)
theorem B2023427 : Blo 2021435 2023427 := bstep (se 1 (by rfl) ⟨1517570, by rfl⟩ : syracuseStep 2023427 = 3035141) B3035141
theorem B3414541 : Blo 2021435 3414541 := bbase (se 3 (by rfl) ⟨640226, by rfl⟩ : syracuseStep 3414541 = 1280453) (by norm_num)
theorem B4552721 : Blo 2021435 4552721 := bstep (se 2 (by rfl) ⟨1707270, by rfl⟩ : syracuseStep 4552721 = 3414541) B3414541
theorem B3035147 : Blo 2021435 3035147 := bstep (se 1 (by rfl) ⟨2276360, by rfl⟩ : syracuseStep 3035147 = 4552721) B4552721
theorem B2023431 : Blo 2021435 2023431 := bstep (se 1 (by rfl) ⟨1517573, by rfl⟩ : syracuseStep 2023431 = 3035147) B3035147
theorem B2276365 : Blo 2021435 2276365 := bbase (se 3 (by rfl) ⟨426818, by rfl⟩ : syracuseStep 2276365 = 853637) (by norm_num)
theorem B3035153 : Blo 2021435 3035153 := bstep (se 2 (by rfl) ⟨1138182, by rfl⟩ : syracuseStep 3035153 = 2276365) B2276365
theorem B2023435 : Blo 2021435 2023435 := bstep (se 1 (by rfl) ⟨1517576, by rfl⟩ : syracuseStep 2023435 = 3035153) B3035153
theorem C0 (j : ℕ) (h1 : 505358 ≤ j) (h2 : j ≤ 505858) : Blo 2021435 (4 * j + 3) := by
  interval_cases j
  · exact B2021435
  · exact B2021439
  · exact B2021443
  · exact B2021447
  · exact B2021451
  · exact B2021455
  · exact B2021459
  · exact B2021463
  · exact B2021467
  · exact B2021471
  · exact B2021475
  · exact B2021479
  · exact B2021483
  · exact B2021487
  · exact B2021491
  · exact B2021495
  · exact B2021499
  · exact B2021503
  · exact B2021507
  · exact B2021511
  · exact B2021515
  · exact B2021519
  · exact B2021523
  · exact B2021527
  · exact B2021531
  · exact B2021535
  · exact B2021539
  · exact B2021543
  · exact B2021547
  · exact B2021551
  · exact B2021555
  · exact B2021559
  · exact B2021563
  · exact B2021567
  · exact B2021571
  · exact B2021575
  · exact B2021579
  · exact B2021583
  · exact B2021587
  · exact B2021591
  · exact B2021595
  · exact B2021599
  · exact B2021603
  · exact B2021607
  · exact B2021611
  · exact B2021615
  · exact B2021619
  · exact B2021623
  · exact B2021627
  · exact B2021631
  · exact B2021635
  · exact B2021639
  · exact B2021643
  · exact B2021647
  · exact B2021651
  · exact B2021655
  · exact B2021659
  · exact B2021663
  · exact B2021667
  · exact B2021671
  · exact B2021675
  · exact B2021679
  · exact B2021683
  · exact B2021687
  · exact B2021691
  · exact B2021695
  · exact B2021699
  · exact B2021703
  · exact B2021707
  · exact B2021711
  · exact B2021715
  · exact B2021719
  · exact B2021723
  · exact B2021727
  · exact B2021731
  · exact B2021735
  · exact B2021739
  · exact B2021743
  · exact B2021747
  · exact B2021751
  · exact B2021755
  · exact B2021759
  · exact B2021763
  · exact B2021767
  · exact B2021771
  · exact B2021775
  · exact B2021779
  · exact B2021783
  · exact B2021787
  · exact B2021791
  · exact B2021795
  · exact B2021799
  · exact B2021803
  · exact B2021807
  · exact B2021811
  · exact B2021815
  · exact B2021819
  · exact B2021823
  · exact B2021827
  · exact B2021831
  · exact B2021835
  · exact B2021839
  · exact B2021843
  · exact B2021847
  · exact B2021851
  · exact B2021855
  · exact B2021859
  · exact B2021863
  · exact B2021867
  · exact B2021871
  · exact B2021875
  · exact B2021879
  · exact B2021883
  · exact B2021887
  · exact B2021891
  · exact B2021895
  · exact B2021899
  · exact B2021903
  · exact B2021907
  · exact B2021911
  · exact B2021915
  · exact B2021919
  · exact B2021923
  · exact B2021927
  · exact B2021931
  · exact B2021935
  · exact B2021939
  · exact B2021943
  · exact B2021947
  · exact B2021951
  · exact B2021955
  · exact B2021959
  · exact B2021963
  · exact B2021967
  · exact B2021971
  · exact B2021975
  · exact B2021979
  · exact B2021983
  · exact B2021987
  · exact B2021991
  · exact B2021995
  · exact B2021999
  · exact B2022003
  · exact B2022007
  · exact B2022011
  · exact B2022015
  · exact B2022019
  · exact B2022023
  · exact B2022027
  · exact B2022031
  · exact B2022035
  · exact B2022039
  · exact B2022043
  · exact B2022047
  · exact B2022051
  · exact B2022055
  · exact B2022059
  · exact B2022063
  · exact B2022067
  · exact B2022071
  · exact B2022075
  · exact B2022079
  · exact B2022083
  · exact B2022087
  · exact B2022091
  · exact B2022095
  · exact B2022099
  · exact B2022103
  · exact B2022107
  · exact B2022111
  · exact B2022115
  · exact B2022119
  · exact B2022123
  · exact B2022127
  · exact B2022131
  · exact B2022135
  · exact B2022139
  · exact B2022143
  · exact B2022147
  · exact B2022151
  · exact B2022155
  · exact B2022159
  · exact B2022163
  · exact B2022167
  · exact B2022171
  · exact B2022175
  · exact B2022179
  · exact B2022183
  · exact B2022187
  · exact B2022191
  · exact B2022195
  · exact B2022199
  · exact B2022203
  · exact B2022207
  · exact B2022211
  · exact B2022215
  · exact B2022219
  · exact B2022223
  · exact B2022227
  · exact B2022231
  · exact B2022235
  · exact B2022239
  · exact B2022243
  · exact B2022247
  · exact B2022251
  · exact B2022255
  · exact B2022259
  · exact B2022263
  · exact B2022267
  · exact B2022271
  · exact B2022275
  · exact B2022279
  · exact B2022283
  · exact B2022287
  · exact B2022291
  · exact B2022295
  · exact B2022299
  · exact B2022303
  · exact B2022307
  · exact B2022311
  · exact B2022315
  · exact B2022319
  · exact B2022323
  · exact B2022327
  · exact B2022331
  · exact B2022335
  · exact B2022339
  · exact B2022343
  · exact B2022347
  · exact B2022351
  · exact B2022355
  · exact B2022359
  · exact B2022363
  · exact B2022367
  · exact B2022371
  · exact B2022375
  · exact B2022379
  · exact B2022383
  · exact B2022387
  · exact B2022391
  · exact B2022395
  · exact B2022399
  · exact B2022403
  · exact B2022407
  · exact B2022411
  · exact B2022415
  · exact B2022419
  · exact B2022423
  · exact B2022427
  · exact B2022431
  · exact B2022435
  · exact B2022439
  · exact B2022443
  · exact B2022447
  · exact B2022451
  · exact B2022455
  · exact B2022459
  · exact B2022463
  · exact B2022467
  · exact B2022471
  · exact B2022475
  · exact B2022479
  · exact B2022483
  · exact B2022487
  · exact B2022491
  · exact B2022495
  · exact B2022499
  · exact B2022503
  · exact B2022507
  · exact B2022511
  · exact B2022515
  · exact B2022519
  · exact B2022523
  · exact B2022527
  · exact B2022531
  · exact B2022535
  · exact B2022539
  · exact B2022543
  · exact B2022547
  · exact B2022551
  · exact B2022555
  · exact B2022559
  · exact B2022563
  · exact B2022567
  · exact B2022571
  · exact B2022575
  · exact B2022579
  · exact B2022583
  · exact B2022587
  · exact B2022591
  · exact B2022595
  · exact B2022599
  · exact B2022603
  · exact B2022607
  · exact B2022611
  · exact B2022615
  · exact B2022619
  · exact B2022623
  · exact B2022627
  · exact B2022631
  · exact B2022635
  · exact B2022639
  · exact B2022643
  · exact B2022647
  · exact B2022651
  · exact B2022655
  · exact B2022659
  · exact B2022663
  · exact B2022667
  · exact B2022671
  · exact B2022675
  · exact B2022679
  · exact B2022683
  · exact B2022687
  · exact B2022691
  · exact B2022695
  · exact B2022699
  · exact B2022703
  · exact B2022707
  · exact B2022711
  · exact B2022715
  · exact B2022719
  · exact B2022723
  · exact B2022727
  · exact B2022731
  · exact B2022735
  · exact B2022739
  · exact B2022743
  · exact B2022747
  · exact B2022751
  · exact B2022755
  · exact B2022759
  · exact B2022763
  · exact B2022767
  · exact B2022771
  · exact B2022775
  · exact B2022779
  · exact B2022783
  · exact B2022787
  · exact B2022791
  · exact B2022795
  · exact B2022799
  · exact B2022803
  · exact B2022807
  · exact B2022811
  · exact B2022815
  · exact B2022819
  · exact B2022823
  · exact B2022827
  · exact B2022831
  · exact B2022835
  · exact B2022839
  · exact B2022843
  · exact B2022847
  · exact B2022851
  · exact B2022855
  · exact B2022859
  · exact B2022863
  · exact B2022867
  · exact B2022871
  · exact B2022875
  · exact B2022879
  · exact B2022883
  · exact B2022887
  · exact B2022891
  · exact B2022895
  · exact B2022899
  · exact B2022903
  · exact B2022907
  · exact B2022911
  · exact B2022915
  · exact B2022919
  · exact B2022923
  · exact B2022927
  · exact B2022931
  · exact B2022935
  · exact B2022939
  · exact B2022943
  · exact B2022947
  · exact B2022951
  · exact B2022955
  · exact B2022959
  · exact B2022963
  · exact B2022967
  · exact B2022971
  · exact B2022975
  · exact B2022979
  · exact B2022983
  · exact B2022987
  · exact B2022991
  · exact B2022995
  · exact B2022999
  · exact B2023003
  · exact B2023007
  · exact B2023011
  · exact B2023015
  · exact B2023019
  · exact B2023023
  · exact B2023027
  · exact B2023031
  · exact B2023035
  · exact B2023039
  · exact B2023043
  · exact B2023047
  · exact B2023051
  · exact B2023055
  · exact B2023059
  · exact B2023063
  · exact B2023067
  · exact B2023071
  · exact B2023075
  · exact B2023079
  · exact B2023083
  · exact B2023087
  · exact B2023091
  · exact B2023095
  · exact B2023099
  · exact B2023103
  · exact B2023107
  · exact B2023111
  · exact B2023115
  · exact B2023119
  · exact B2023123
  · exact B2023127
  · exact B2023131
  · exact B2023135
  · exact B2023139
  · exact B2023143
  · exact B2023147
  · exact B2023151
  · exact B2023155
  · exact B2023159
  · exact B2023163
  · exact B2023167
  · exact B2023171
  · exact B2023175
  · exact B2023179
  · exact B2023183
  · exact B2023187
  · exact B2023191
  · exact B2023195
  · exact B2023199
  · exact B2023203
  · exact B2023207
  · exact B2023211
  · exact B2023215
  · exact B2023219
  · exact B2023223
  · exact B2023227
  · exact B2023231
  · exact B2023235
  · exact B2023239
  · exact B2023243
  · exact B2023247
  · exact B2023251
  · exact B2023255
  · exact B2023259
  · exact B2023263
  · exact B2023267
  · exact B2023271
  · exact B2023275
  · exact B2023279
  · exact B2023283
  · exact B2023287
  · exact B2023291
  · exact B2023295
  · exact B2023299
  · exact B2023303
  · exact B2023307
  · exact B2023311
  · exact B2023315
  · exact B2023319
  · exact B2023323
  · exact B2023327
  · exact B2023331
  · exact B2023335
  · exact B2023339
  · exact B2023343
  · exact B2023347
  · exact B2023351
  · exact B2023355
  · exact B2023359
  · exact B2023363
  · exact B2023367
  · exact B2023371
  · exact B2023375
  · exact B2023379
  · exact B2023383
  · exact B2023387
  · exact B2023391
  · exact B2023395
  · exact B2023399
  · exact B2023403
  · exact B2023407
  · exact B2023411
  · exact B2023415
  · exact B2023419
  · exact B2023423
  · exact B2023427
  · exact B2023431
  · exact B2023435
theorem solution (m : ℕ) (hlo : 2021435 ≤ m) (hhi : m ≤ 2023435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 505358 ≤ j := by omega
    have hj2 : j ≤ 505858 := by omega
    have hb : Blo 2021435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
