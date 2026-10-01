-- Prove2me | solution 1 for syracuse_descends_range_2117435_2119435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:53.941298+00:00
-- url     : https://prove2.me/submissions/69c737e6-1e5a-4f2b-a57b-4933be45ecfc

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

theorem B3573173 : Blo 2117435 3573173 := bbase (se 5 (by rfl) ⟨167492, by rfl⟩ : syracuseStep 3573173 = 334985) (by norm_num)
theorem B2382115 : Blo 2117435 2382115 := bstep (se 1 (by rfl) ⟨1786586, by rfl⟩ : syracuseStep 2382115 = 3573173) B3573173
theorem B3176153 : Blo 2117435 3176153 := bstep (se 2 (by rfl) ⟨1191057, by rfl⟩ : syracuseStep 3176153 = 2382115) B2382115
theorem B2117435 : Blo 2117435 2117435 := bstep (se 1 (by rfl) ⟨1588076, by rfl⟩ : syracuseStep 2117435 = 3176153) B3176153
theorem B2261153 : Blo 2117435 2261153 := bbase (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) (by norm_num)
theorem B6029741 : Blo 2117435 6029741 := bstep (se 3 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 6029741 = 2261153) B2261153
theorem B16079309 : Blo 2117435 16079309 := bstep (se 3 (by rfl) ⟨3014870, by rfl⟩ : syracuseStep 16079309 = 6029741) B6029741
theorem B10719539 : Blo 2117435 10719539 := bstep (se 1 (by rfl) ⟨8039654, by rfl⟩ : syracuseStep 10719539 = 16079309) B16079309
theorem B7146359 : Blo 2117435 7146359 := bstep (se 1 (by rfl) ⟨5359769, by rfl⟩ : syracuseStep 7146359 = 10719539) B10719539
theorem B4764239 : Blo 2117435 4764239 := bstep (se 1 (by rfl) ⟨3573179, by rfl⟩ : syracuseStep 4764239 = 7146359) B7146359
theorem B3176159 : Blo 2117435 3176159 := bstep (se 1 (by rfl) ⟨2382119, by rfl⟩ : syracuseStep 3176159 = 4764239) B4764239
theorem B2117439 : Blo 2117435 2117439 := bstep (se 1 (by rfl) ⟨1588079, by rfl⟩ : syracuseStep 2117439 = 3176159) B3176159
theorem B3176165 : Blo 2117435 3176165 := bbase (se 4 (by rfl) ⟨297765, by rfl⟩ : syracuseStep 3176165 = 595531) (by norm_num)
theorem B2117443 : Blo 2117435 2117443 := bstep (se 1 (by rfl) ⟨1588082, by rfl⟩ : syracuseStep 2117443 = 3176165) B3176165
theorem B6029765 : Blo 2117435 6029765 := bbase (se 4 (by rfl) ⟨565290, by rfl⟩ : syracuseStep 6029765 = 1130581) (by norm_num)
theorem B4019843 : Blo 2117435 4019843 := bstep (se 1 (by rfl) ⟨3014882, by rfl⟩ : syracuseStep 4019843 = 6029765) B6029765
theorem B2679895 : Blo 2117435 2679895 := bstep (se 1 (by rfl) ⟨2009921, by rfl⟩ : syracuseStep 2679895 = 4019843) B4019843
theorem B3573193 : Blo 2117435 3573193 := bstep (se 2 (by rfl) ⟨1339947, by rfl⟩ : syracuseStep 3573193 = 2679895) B2679895
theorem B4764257 : Blo 2117435 4764257 := bstep (se 2 (by rfl) ⟨1786596, by rfl⟩ : syracuseStep 4764257 = 3573193) B3573193
theorem B3176171 : Blo 2117435 3176171 := bstep (se 1 (by rfl) ⟨2382128, by rfl⟩ : syracuseStep 3176171 = 4764257) B4764257
theorem B2117447 : Blo 2117435 2117447 := bstep (se 1 (by rfl) ⟨1588085, by rfl⟩ : syracuseStep 2117447 = 3176171) B3176171
theorem B2382133 : Blo 2117435 2382133 := bbase (se 5 (by rfl) ⟨111662, by rfl⟩ : syracuseStep 2382133 = 223325) (by norm_num)
theorem B3176177 : Blo 2117435 3176177 := bstep (se 2 (by rfl) ⟨1191066, by rfl⟩ : syracuseStep 3176177 = 2382133) B2382133
theorem B2117451 : Blo 2117435 2117451 := bstep (se 1 (by rfl) ⟨1588088, by rfl⟩ : syracuseStep 2117451 = 3176177) B3176177
theorem B2679905 : Blo 2117435 2679905 := bbase (se 2 (by rfl) ⟨1004964, by rfl⟩ : syracuseStep 2679905 = 2009929) (by norm_num)
theorem B7146413 : Blo 2117435 7146413 := bstep (se 3 (by rfl) ⟨1339952, by rfl⟩ : syracuseStep 7146413 = 2679905) B2679905
theorem B4764275 : Blo 2117435 4764275 := bstep (se 1 (by rfl) ⟨3573206, by rfl⟩ : syracuseStep 4764275 = 7146413) B7146413
theorem B3176183 : Blo 2117435 3176183 := bstep (se 1 (by rfl) ⟨2382137, by rfl⟩ : syracuseStep 3176183 = 4764275) B4764275
theorem B2117455 : Blo 2117435 2117455 := bstep (se 1 (by rfl) ⟨1588091, by rfl⟩ : syracuseStep 2117455 = 3176183) B3176183
theorem B3176189 : Blo 2117435 3176189 := bbase (se 3 (by rfl) ⟨595535, by rfl⟩ : syracuseStep 3176189 = 1191071) (by norm_num)
theorem B2117459 : Blo 2117435 2117459 := bstep (se 1 (by rfl) ⟨1588094, by rfl⟩ : syracuseStep 2117459 = 3176189) B3176189
theorem B4764293 : Blo 2117435 4764293 := bbase (se 4 (by rfl) ⟨446652, by rfl⟩ : syracuseStep 4764293 = 893305) (by norm_num)
theorem B3176195 : Blo 2117435 3176195 := bstep (se 1 (by rfl) ⟨2382146, by rfl⟩ : syracuseStep 3176195 = 4764293) B4764293
theorem B2117463 : Blo 2117435 2117463 := bstep (se 1 (by rfl) ⟨1588097, by rfl⟩ : syracuseStep 2117463 = 3176195) B3176195
theorem B2414653 : Blo 2117435 2414653 := bbase (se 3 (by rfl) ⟨452747, by rfl⟩ : syracuseStep 2414653 = 905495) (by norm_num)
theorem B51512597 : Blo 2117435 51512597 := bstep (se 6 (by rfl) ⟨1207326, by rfl⟩ : syracuseStep 51512597 = 2414653) B2414653
theorem B34341731 : Blo 2117435 34341731 := bstep (se 1 (by rfl) ⟨25756298, by rfl⟩ : syracuseStep 34341731 = 51512597) B51512597
theorem B22894487 : Blo 2117435 22894487 := bstep (se 1 (by rfl) ⟨17170865, by rfl⟩ : syracuseStep 22894487 = 34341731) B34341731
theorem B15262991 : Blo 2117435 15262991 := bstep (se 1 (by rfl) ⟨11447243, by rfl⟩ : syracuseStep 15262991 = 22894487) B22894487
theorem B10175327 : Blo 2117435 10175327 := bstep (se 1 (by rfl) ⟨7631495, by rfl⟩ : syracuseStep 10175327 = 15262991) B15262991
theorem B6783551 : Blo 2117435 6783551 := bstep (se 1 (by rfl) ⟨5087663, by rfl⟩ : syracuseStep 6783551 = 10175327) B10175327
theorem B4522367 : Blo 2117435 4522367 := bstep (se 1 (by rfl) ⟨3391775, by rfl⟩ : syracuseStep 4522367 = 6783551) B6783551
theorem B3014911 : Blo 2117435 3014911 := bstep (se 1 (by rfl) ⟨2261183, by rfl⟩ : syracuseStep 3014911 = 4522367) B4522367
theorem B4019881 : Blo 2117435 4019881 := bstep (se 2 (by rfl) ⟨1507455, by rfl⟩ : syracuseStep 4019881 = 3014911) B3014911
theorem B5359841 : Blo 2117435 5359841 := bstep (se 2 (by rfl) ⟨2009940, by rfl⟩ : syracuseStep 5359841 = 4019881) B4019881
theorem B3573227 : Blo 2117435 3573227 := bstep (se 1 (by rfl) ⟨2679920, by rfl⟩ : syracuseStep 3573227 = 5359841) B5359841
theorem B2382151 : Blo 2117435 2382151 := bstep (se 1 (by rfl) ⟨1786613, by rfl⟩ : syracuseStep 2382151 = 3573227) B3573227
theorem B3176201 : Blo 2117435 3176201 := bstep (se 2 (by rfl) ⟨1191075, by rfl⟩ : syracuseStep 3176201 = 2382151) B2382151
theorem B2117467 : Blo 2117435 2117467 := bstep (se 1 (by rfl) ⟨1588100, by rfl⟩ : syracuseStep 2117467 = 3176201) B3176201
theorem B10719701 : Blo 2117435 10719701 := bbase (se 7 (by rfl) ⟨125621, by rfl⟩ : syracuseStep 10719701 = 251243) (by norm_num)
theorem B7146467 : Blo 2117435 7146467 := bstep (se 1 (by rfl) ⟨5359850, by rfl⟩ : syracuseStep 7146467 = 10719701) B10719701
theorem B4764311 : Blo 2117435 4764311 := bstep (se 1 (by rfl) ⟨3573233, by rfl⟩ : syracuseStep 4764311 = 7146467) B7146467
theorem B3176207 : Blo 2117435 3176207 := bstep (se 1 (by rfl) ⟨2382155, by rfl⟩ : syracuseStep 3176207 = 4764311) B4764311
theorem B2117471 : Blo 2117435 2117471 := bstep (se 1 (by rfl) ⟨1588103, by rfl⟩ : syracuseStep 2117471 = 3176207) B3176207
theorem B3176213 : Blo 2117435 3176213 := bbase (se 6 (by rfl) ⟨74442, by rfl⟩ : syracuseStep 3176213 = 148885) (by norm_num)
theorem B2117475 : Blo 2117435 2117475 := bstep (se 1 (by rfl) ⟨1588106, by rfl⟩ : syracuseStep 2117475 = 3176213) B3176213
theorem B6439109 : Blo 2117435 6439109 := bbase (se 4 (by rfl) ⟨603666, by rfl⟩ : syracuseStep 6439109 = 1207333) (by norm_num)
theorem B17170957 : Blo 2117435 17170957 := bstep (se 3 (by rfl) ⟨3219554, by rfl⟩ : syracuseStep 17170957 = 6439109) B6439109
theorem B91578437 : Blo 2117435 91578437 := bstep (se 4 (by rfl) ⟨8585478, by rfl⟩ : syracuseStep 91578437 = 17170957) B17170957
theorem B61052291 : Blo 2117435 61052291 := bstep (se 1 (by rfl) ⟨45789218, by rfl⟩ : syracuseStep 61052291 = 91578437) B91578437
theorem B40701527 : Blo 2117435 40701527 := bstep (se 1 (by rfl) ⟨30526145, by rfl⟩ : syracuseStep 40701527 = 61052291) B61052291
theorem B27134351 : Blo 2117435 27134351 := bstep (se 1 (by rfl) ⟨20350763, by rfl⟩ : syracuseStep 27134351 = 40701527) B40701527
theorem B18089567 : Blo 2117435 18089567 := bstep (se 1 (by rfl) ⟨13567175, by rfl⟩ : syracuseStep 18089567 = 27134351) B27134351
theorem B12059711 : Blo 2117435 12059711 := bstep (se 1 (by rfl) ⟨9044783, by rfl⟩ : syracuseStep 12059711 = 18089567) B18089567
theorem B8039807 : Blo 2117435 8039807 := bstep (se 1 (by rfl) ⟨6029855, by rfl⟩ : syracuseStep 8039807 = 12059711) B12059711
theorem B5359871 : Blo 2117435 5359871 := bstep (se 1 (by rfl) ⟨4019903, by rfl⟩ : syracuseStep 5359871 = 8039807) B8039807
theorem B3573247 : Blo 2117435 3573247 := bstep (se 1 (by rfl) ⟨2679935, by rfl⟩ : syracuseStep 3573247 = 5359871) B5359871
theorem B4764329 : Blo 2117435 4764329 := bstep (se 2 (by rfl) ⟨1786623, by rfl⟩ : syracuseStep 4764329 = 3573247) B3573247
theorem B3176219 : Blo 2117435 3176219 := bstep (se 1 (by rfl) ⟨2382164, by rfl⟩ : syracuseStep 3176219 = 4764329) B4764329
theorem B2117479 : Blo 2117435 2117479 := bstep (se 1 (by rfl) ⟨1588109, by rfl⟩ : syracuseStep 2117479 = 3176219) B3176219
theorem B2382169 : Blo 2117435 2382169 := bbase (se 2 (by rfl) ⟨893313, by rfl⟩ : syracuseStep 2382169 = 1786627) (by norm_num)
theorem B3176225 : Blo 2117435 3176225 := bstep (se 2 (by rfl) ⟨1191084, by rfl⟩ : syracuseStep 3176225 = 2382169) B2382169
theorem B2117483 : Blo 2117435 2117483 := bstep (se 1 (by rfl) ⟨1588112, by rfl⟩ : syracuseStep 2117483 = 3176225) B3176225
theorem B4351325 : Blo 2117435 4351325 := bbase (se 3 (by rfl) ⟨815873, by rfl⟩ : syracuseStep 4351325 = 1631747) (by norm_num)
theorem B46414133 : Blo 2117435 46414133 := bstep (se 5 (by rfl) ⟨2175662, by rfl⟩ : syracuseStep 46414133 = 4351325) B4351325
theorem B30942755 : Blo 2117435 30942755 := bstep (se 1 (by rfl) ⟨23207066, by rfl⟩ : syracuseStep 30942755 = 46414133) B46414133
theorem B20628503 : Blo 2117435 20628503 := bstep (se 1 (by rfl) ⟨15471377, by rfl⟩ : syracuseStep 20628503 = 30942755) B30942755
theorem B13752335 : Blo 2117435 13752335 := bstep (se 1 (by rfl) ⟨10314251, by rfl⟩ : syracuseStep 13752335 = 20628503) B20628503
theorem B9168223 : Blo 2117435 9168223 := bstep (se 1 (by rfl) ⟨6876167, by rfl⟩ : syracuseStep 9168223 = 13752335) B13752335
theorem B12224297 : Blo 2117435 12224297 := bstep (se 2 (by rfl) ⟨4584111, by rfl⟩ : syracuseStep 12224297 = 9168223) B9168223
theorem B32598125 : Blo 2117435 32598125 := bstep (se 3 (by rfl) ⟨6112148, by rfl⟩ : syracuseStep 32598125 = 12224297) B12224297
theorem B21732083 : Blo 2117435 21732083 := bstep (se 1 (by rfl) ⟨16299062, by rfl⟩ : syracuseStep 21732083 = 32598125) B32598125
theorem B14488055 : Blo 2117435 14488055 := bstep (se 1 (by rfl) ⟨10866041, by rfl⟩ : syracuseStep 14488055 = 21732083) B21732083
theorem B9658703 : Blo 2117435 9658703 := bstep (se 1 (by rfl) ⟨7244027, by rfl⟩ : syracuseStep 9658703 = 14488055) B14488055
theorem B25756541 : Blo 2117435 25756541 := bstep (se 3 (by rfl) ⟨4829351, by rfl⟩ : syracuseStep 25756541 = 9658703) B9658703
theorem B17171027 : Blo 2117435 17171027 := bstep (se 1 (by rfl) ⟨12878270, by rfl⟩ : syracuseStep 17171027 = 25756541) B25756541
theorem B11447351 : Blo 2117435 11447351 := bstep (se 1 (by rfl) ⟨8585513, by rfl⟩ : syracuseStep 11447351 = 17171027) B17171027
theorem B7631567 : Blo 2117435 7631567 := bstep (se 1 (by rfl) ⟨5723675, by rfl⟩ : syracuseStep 7631567 = 11447351) B11447351
theorem B5087711 : Blo 2117435 5087711 := bstep (se 1 (by rfl) ⟨3815783, by rfl⟩ : syracuseStep 5087711 = 7631567) B7631567
theorem B3391807 : Blo 2117435 3391807 := bstep (se 1 (by rfl) ⟨2543855, by rfl⟩ : syracuseStep 3391807 = 5087711) B5087711
theorem B4522409 : Blo 2117435 4522409 := bstep (se 2 (by rfl) ⟨1695903, by rfl⟩ : syracuseStep 4522409 = 3391807) B3391807
theorem B3014939 : Blo 2117435 3014939 := bstep (se 1 (by rfl) ⟨2261204, by rfl⟩ : syracuseStep 3014939 = 4522409) B4522409
theorem B8039837 : Blo 2117435 8039837 := bstep (se 3 (by rfl) ⟨1507469, by rfl⟩ : syracuseStep 8039837 = 3014939) B3014939
theorem B5359891 : Blo 2117435 5359891 := bstep (se 1 (by rfl) ⟨4019918, by rfl⟩ : syracuseStep 5359891 = 8039837) B8039837
theorem B7146521 : Blo 2117435 7146521 := bstep (se 2 (by rfl) ⟨2679945, by rfl⟩ : syracuseStep 7146521 = 5359891) B5359891
theorem B4764347 : Blo 2117435 4764347 := bstep (se 1 (by rfl) ⟨3573260, by rfl⟩ : syracuseStep 4764347 = 7146521) B7146521
theorem B3176231 : Blo 2117435 3176231 := bstep (se 1 (by rfl) ⟨2382173, by rfl⟩ : syracuseStep 3176231 = 4764347) B4764347
theorem B2117487 : Blo 2117435 2117487 := bstep (se 1 (by rfl) ⟨1588115, by rfl⟩ : syracuseStep 2117487 = 3176231) B3176231
theorem B3176237 : Blo 2117435 3176237 := bbase (se 3 (by rfl) ⟨595544, by rfl⟩ : syracuseStep 3176237 = 1191089) (by norm_num)
theorem B2117491 : Blo 2117435 2117491 := bstep (se 1 (by rfl) ⟨1588118, by rfl⟩ : syracuseStep 2117491 = 3176237) B3176237
theorem B4764365 : Blo 2117435 4764365 := bbase (se 3 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 4764365 = 1786637) (by norm_num)
theorem B3176243 : Blo 2117435 3176243 := bstep (se 1 (by rfl) ⟨2382182, by rfl⟩ : syracuseStep 3176243 = 4764365) B4764365
theorem B2117495 : Blo 2117435 2117495 := bstep (se 1 (by rfl) ⟨1588121, by rfl⟩ : syracuseStep 2117495 = 3176243) B3176243
theorem B2679961 : Blo 2117435 2679961 := bbase (se 2 (by rfl) ⟨1004985, by rfl⟩ : syracuseStep 2679961 = 2009971) (by norm_num)
theorem B3573281 : Blo 2117435 3573281 := bstep (se 2 (by rfl) ⟨1339980, by rfl⟩ : syracuseStep 3573281 = 2679961) B2679961
theorem B2382187 : Blo 2117435 2382187 := bstep (se 1 (by rfl) ⟨1786640, by rfl⟩ : syracuseStep 2382187 = 3573281) B3573281
theorem B3176249 : Blo 2117435 3176249 := bstep (se 2 (by rfl) ⟨1191093, by rfl⟩ : syracuseStep 3176249 = 2382187) B2382187
theorem B2117499 : Blo 2117435 2117499 := bstep (se 1 (by rfl) ⟨1588124, by rfl⟩ : syracuseStep 2117499 = 3176249) B3176249
theorem B9044885 : Blo 2117435 9044885 := bbase (se 6 (by rfl) ⟨211989, by rfl⟩ : syracuseStep 9044885 = 423979) (by norm_num)
theorem B24119693 : Blo 2117435 24119693 := bstep (se 3 (by rfl) ⟨4522442, by rfl⟩ : syracuseStep 24119693 = 9044885) B9044885
theorem B16079795 : Blo 2117435 16079795 := bstep (se 1 (by rfl) ⟨12059846, by rfl⟩ : syracuseStep 16079795 = 24119693) B24119693
theorem B10719863 : Blo 2117435 10719863 := bstep (se 1 (by rfl) ⟨8039897, by rfl⟩ : syracuseStep 10719863 = 16079795) B16079795
theorem B7146575 : Blo 2117435 7146575 := bstep (se 1 (by rfl) ⟨5359931, by rfl⟩ : syracuseStep 7146575 = 10719863) B10719863
theorem B4764383 : Blo 2117435 4764383 := bstep (se 1 (by rfl) ⟨3573287, by rfl⟩ : syracuseStep 4764383 = 7146575) B7146575
theorem B3176255 : Blo 2117435 3176255 := bstep (se 1 (by rfl) ⟨2382191, by rfl⟩ : syracuseStep 3176255 = 4764383) B4764383
theorem B2117503 : Blo 2117435 2117503 := bstep (se 1 (by rfl) ⟨1588127, by rfl⟩ : syracuseStep 2117503 = 3176255) B3176255
theorem B3176261 : Blo 2117435 3176261 := bbase (se 4 (by rfl) ⟨297774, by rfl⟩ : syracuseStep 3176261 = 595549) (by norm_num)
theorem B2117507 : Blo 2117435 2117507 := bstep (se 1 (by rfl) ⟨1588130, by rfl⟩ : syracuseStep 2117507 = 3176261) B3176261
theorem B3573301 : Blo 2117435 3573301 := bbase (se 5 (by rfl) ⟨167498, by rfl⟩ : syracuseStep 3573301 = 334997) (by norm_num)
theorem B4764401 : Blo 2117435 4764401 := bstep (se 2 (by rfl) ⟨1786650, by rfl⟩ : syracuseStep 4764401 = 3573301) B3573301
theorem B3176267 : Blo 2117435 3176267 := bstep (se 1 (by rfl) ⟨2382200, by rfl⟩ : syracuseStep 3176267 = 4764401) B4764401
theorem B2117511 : Blo 2117435 2117511 := bstep (se 1 (by rfl) ⟨1588133, by rfl⟩ : syracuseStep 2117511 = 3176267) B3176267
theorem B2382205 : Blo 2117435 2382205 := bbase (se 3 (by rfl) ⟨446663, by rfl⟩ : syracuseStep 2382205 = 893327) (by norm_num)
theorem B3176273 : Blo 2117435 3176273 := bstep (se 2 (by rfl) ⟨1191102, by rfl⟩ : syracuseStep 3176273 = 2382205) B2382205
theorem B2117515 : Blo 2117435 2117515 := bstep (se 1 (by rfl) ⟨1588136, by rfl⟩ : syracuseStep 2117515 = 3176273) B3176273
theorem B7146629 : Blo 2117435 7146629 := bbase (se 4 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 7146629 = 1339993) (by norm_num)
theorem B4764419 : Blo 2117435 4764419 := bstep (se 1 (by rfl) ⟨3573314, by rfl⟩ : syracuseStep 4764419 = 7146629) B7146629
theorem B3176279 : Blo 2117435 3176279 := bstep (se 1 (by rfl) ⟨2382209, by rfl⟩ : syracuseStep 3176279 = 4764419) B4764419
theorem B2117519 : Blo 2117435 2117519 := bstep (se 1 (by rfl) ⟨1588139, by rfl⟩ : syracuseStep 2117519 = 3176279) B3176279
theorem B3176285 : Blo 2117435 3176285 := bbase (se 3 (by rfl) ⟨595553, by rfl⟩ : syracuseStep 3176285 = 1191107) (by norm_num)
theorem B2117523 : Blo 2117435 2117523 := bstep (se 1 (by rfl) ⟨1588142, by rfl⟩ : syracuseStep 2117523 = 3176285) B3176285
theorem B4764437 : Blo 2117435 4764437 := bbase (se 6 (by rfl) ⟨111666, by rfl⟩ : syracuseStep 4764437 = 223333) (by norm_num)
theorem B3176291 : Blo 2117435 3176291 := bstep (se 1 (by rfl) ⟨2382218, by rfl⟩ : syracuseStep 3176291 = 4764437) B4764437
theorem B2117527 : Blo 2117435 2117527 := bstep (se 1 (by rfl) ⟨1588145, by rfl⟩ : syracuseStep 2117527 = 3176291) B3176291
theorem B8040005 : Blo 2117435 8040005 := bbase (se 4 (by rfl) ⟨753750, by rfl⟩ : syracuseStep 8040005 = 1507501) (by norm_num)
theorem B5360003 : Blo 2117435 5360003 := bstep (se 1 (by rfl) ⟨4020002, by rfl⟩ : syracuseStep 5360003 = 8040005) B8040005
theorem B3573335 : Blo 2117435 3573335 := bstep (se 1 (by rfl) ⟨2680001, by rfl⟩ : syracuseStep 3573335 = 5360003) B5360003
theorem B2382223 : Blo 2117435 2382223 := bstep (se 1 (by rfl) ⟨1786667, by rfl⟩ : syracuseStep 2382223 = 3573335) B3573335
theorem B3176297 : Blo 2117435 3176297 := bstep (se 2 (by rfl) ⟨1191111, by rfl⟩ : syracuseStep 3176297 = 2382223) B2382223
theorem B2117531 : Blo 2117435 2117531 := bstep (se 1 (by rfl) ⟨1588148, by rfl⟩ : syracuseStep 2117531 = 3176297) B3176297
theorem B15263477 : Blo 2117435 15263477 := bbase (se 5 (by rfl) ⟨715475, by rfl⟩ : syracuseStep 15263477 = 1430951) (by norm_num)
theorem B10175651 : Blo 2117435 10175651 := bstep (se 1 (by rfl) ⟨7631738, by rfl⟩ : syracuseStep 10175651 = 15263477) B15263477
theorem B6783767 : Blo 2117435 6783767 := bstep (se 1 (by rfl) ⟨5087825, by rfl⟩ : syracuseStep 6783767 = 10175651) B10175651
theorem B4522511 : Blo 2117435 4522511 := bstep (se 1 (by rfl) ⟨3391883, by rfl⟩ : syracuseStep 4522511 = 6783767) B6783767
theorem B12060029 : Blo 2117435 12060029 := bstep (se 3 (by rfl) ⟨2261255, by rfl⟩ : syracuseStep 12060029 = 4522511) B4522511
theorem B8040019 : Blo 2117435 8040019 := bstep (se 1 (by rfl) ⟨6030014, by rfl⟩ : syracuseStep 8040019 = 12060029) B12060029
theorem B10720025 : Blo 2117435 10720025 := bstep (se 2 (by rfl) ⟨4020009, by rfl⟩ : syracuseStep 10720025 = 8040019) B8040019
theorem B7146683 : Blo 2117435 7146683 := bstep (se 1 (by rfl) ⟨5360012, by rfl⟩ : syracuseStep 7146683 = 10720025) B10720025
theorem B4764455 : Blo 2117435 4764455 := bstep (se 1 (by rfl) ⟨3573341, by rfl⟩ : syracuseStep 4764455 = 7146683) B7146683
theorem B3176303 : Blo 2117435 3176303 := bstep (se 1 (by rfl) ⟨2382227, by rfl⟩ : syracuseStep 3176303 = 4764455) B4764455
theorem B2117535 : Blo 2117435 2117535 := bstep (se 1 (by rfl) ⟨1588151, by rfl⟩ : syracuseStep 2117535 = 3176303) B3176303
theorem B3176309 : Blo 2117435 3176309 := bbase (se 5 (by rfl) ⟨148889, by rfl⟩ : syracuseStep 3176309 = 297779) (by norm_num)
theorem B2117539 : Blo 2117435 2117539 := bstep (se 1 (by rfl) ⟨1588154, by rfl⟩ : syracuseStep 2117539 = 3176309) B3176309
theorem B3815885 : Blo 2117435 3815885 := bbase (se 3 (by rfl) ⟨715478, by rfl⟩ : syracuseStep 3815885 = 1430957) (by norm_num)
theorem B2543923 : Blo 2117435 2543923 := bstep (se 1 (by rfl) ⟨1907942, by rfl⟩ : syracuseStep 2543923 = 3815885) B3815885
theorem B3391897 : Blo 2117435 3391897 := bstep (se 2 (by rfl) ⟨1271961, by rfl⟩ : syracuseStep 3391897 = 2543923) B2543923
theorem B4522529 : Blo 2117435 4522529 := bstep (se 2 (by rfl) ⟨1695948, by rfl⟩ : syracuseStep 4522529 = 3391897) B3391897
theorem B3015019 : Blo 2117435 3015019 := bstep (se 1 (by rfl) ⟨2261264, by rfl⟩ : syracuseStep 3015019 = 4522529) B4522529
theorem B4020025 : Blo 2117435 4020025 := bstep (se 2 (by rfl) ⟨1507509, by rfl⟩ : syracuseStep 4020025 = 3015019) B3015019
theorem B5360033 : Blo 2117435 5360033 := bstep (se 2 (by rfl) ⟨2010012, by rfl⟩ : syracuseStep 5360033 = 4020025) B4020025
theorem B3573355 : Blo 2117435 3573355 := bstep (se 1 (by rfl) ⟨2680016, by rfl⟩ : syracuseStep 3573355 = 5360033) B5360033
theorem B4764473 : Blo 2117435 4764473 := bstep (se 2 (by rfl) ⟨1786677, by rfl⟩ : syracuseStep 4764473 = 3573355) B3573355
theorem B3176315 : Blo 2117435 3176315 := bstep (se 1 (by rfl) ⟨2382236, by rfl⟩ : syracuseStep 3176315 = 4764473) B4764473
theorem B2117543 : Blo 2117435 2117543 := bstep (se 1 (by rfl) ⟨1588157, by rfl⟩ : syracuseStep 2117543 = 3176315) B3176315
theorem B2382241 : Blo 2117435 2382241 := bbase (se 2 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 2382241 = 1786681) (by norm_num)
theorem B3176321 : Blo 2117435 3176321 := bstep (se 2 (by rfl) ⟨1191120, by rfl⟩ : syracuseStep 3176321 = 2382241) B2382241
theorem B2117547 : Blo 2117435 2117547 := bstep (se 1 (by rfl) ⟨1588160, by rfl⟩ : syracuseStep 2117547 = 3176321) B3176321
theorem B5360053 : Blo 2117435 5360053 := bbase (se 5 (by rfl) ⟨251252, by rfl⟩ : syracuseStep 5360053 = 502505) (by norm_num)
theorem B7146737 : Blo 2117435 7146737 := bstep (se 2 (by rfl) ⟨2680026, by rfl⟩ : syracuseStep 7146737 = 5360053) B5360053
theorem B4764491 : Blo 2117435 4764491 := bstep (se 1 (by rfl) ⟨3573368, by rfl⟩ : syracuseStep 4764491 = 7146737) B7146737
theorem B3176327 : Blo 2117435 3176327 := bstep (se 1 (by rfl) ⟨2382245, by rfl⟩ : syracuseStep 3176327 = 4764491) B4764491
theorem B2117551 : Blo 2117435 2117551 := bstep (se 1 (by rfl) ⟨1588163, by rfl⟩ : syracuseStep 2117551 = 3176327) B3176327
theorem B3176333 : Blo 2117435 3176333 := bbase (se 3 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 3176333 = 1191125) (by norm_num)
theorem B2117555 : Blo 2117435 2117555 := bstep (se 1 (by rfl) ⟨1588166, by rfl⟩ : syracuseStep 2117555 = 3176333) B3176333
theorem B4764509 : Blo 2117435 4764509 := bbase (se 3 (by rfl) ⟨893345, by rfl⟩ : syracuseStep 4764509 = 1786691) (by norm_num)
theorem B3176339 : Blo 2117435 3176339 := bstep (se 1 (by rfl) ⟨2382254, by rfl⟩ : syracuseStep 3176339 = 4764509) B4764509
theorem B2117559 : Blo 2117435 2117559 := bstep (se 1 (by rfl) ⟨1588169, by rfl⟩ : syracuseStep 2117559 = 3176339) B3176339
theorem B3573389 : Blo 2117435 3573389 := bbase (se 3 (by rfl) ⟨670010, by rfl⟩ : syracuseStep 3573389 = 1340021) (by norm_num)
theorem B2382259 : Blo 2117435 2382259 := bstep (se 1 (by rfl) ⟨1786694, by rfl⟩ : syracuseStep 2382259 = 3573389) B3573389
theorem B3176345 : Blo 2117435 3176345 := bstep (se 2 (by rfl) ⟨1191129, by rfl⟩ : syracuseStep 3176345 = 2382259) B2382259
theorem B2117563 : Blo 2117435 2117563 := bstep (se 1 (by rfl) ⟨1588172, by rfl⟩ : syracuseStep 2117563 = 3176345) B3176345
theorem B5801989 : Blo 2117435 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B7735985 : Blo 2117435 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B5157323 : Blo 2117435 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B3438215 : Blo 2117435 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B2292143 : Blo 2117435 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B6112381 : Blo 2117435 6112381 := bstep (se 3 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 6112381 = 2292143) B2292143
theorem B8149841 : Blo 2117435 8149841 := bstep (se 2 (by rfl) ⟨3056190, by rfl⟩ : syracuseStep 8149841 = 6112381) B6112381
theorem B5433227 : Blo 2117435 5433227 := bstep (se 1 (by rfl) ⟨4074920, by rfl⟩ : syracuseStep 5433227 = 8149841) B8149841
theorem B3622151 : Blo 2117435 3622151 := bstep (se 1 (by rfl) ⟨2716613, by rfl⟩ : syracuseStep 3622151 = 5433227) B5433227
theorem B2414767 : Blo 2117435 2414767 := bstep (se 1 (by rfl) ⟨1811075, by rfl⟩ : syracuseStep 2414767 = 3622151) B3622151
theorem B3219689 : Blo 2117435 3219689 := bstep (se 2 (by rfl) ⟨1207383, by rfl⟩ : syracuseStep 3219689 = 2414767) B2414767
theorem B8585837 : Blo 2117435 8585837 := bstep (se 3 (by rfl) ⟨1609844, by rfl⟩ : syracuseStep 8585837 = 3219689) B3219689
theorem B5723891 : Blo 2117435 5723891 := bstep (se 1 (by rfl) ⟨4292918, by rfl⟩ : syracuseStep 5723891 = 8585837) B8585837
theorem B3815927 : Blo 2117435 3815927 := bstep (se 1 (by rfl) ⟨2861945, by rfl⟩ : syracuseStep 3815927 = 5723891) B5723891
theorem B2543951 : Blo 2117435 2543951 := bstep (se 1 (by rfl) ⟨1907963, by rfl⟩ : syracuseStep 2543951 = 3815927) B3815927
theorem B6783869 : Blo 2117435 6783869 := bstep (se 3 (by rfl) ⟨1271975, by rfl⟩ : syracuseStep 6783869 = 2543951) B2543951
theorem B18090317 : Blo 2117435 18090317 := bstep (se 3 (by rfl) ⟨3391934, by rfl⟩ : syracuseStep 18090317 = 6783869) B6783869
theorem B12060211 : Blo 2117435 12060211 := bstep (se 1 (by rfl) ⟨9045158, by rfl⟩ : syracuseStep 12060211 = 18090317) B18090317
theorem B16080281 : Blo 2117435 16080281 := bstep (se 2 (by rfl) ⟨6030105, by rfl⟩ : syracuseStep 16080281 = 12060211) B12060211
theorem B10720187 : Blo 2117435 10720187 := bstep (se 1 (by rfl) ⟨8040140, by rfl⟩ : syracuseStep 10720187 = 16080281) B16080281
theorem B7146791 : Blo 2117435 7146791 := bstep (se 1 (by rfl) ⟨5360093, by rfl⟩ : syracuseStep 7146791 = 10720187) B10720187
theorem B4764527 : Blo 2117435 4764527 := bstep (se 1 (by rfl) ⟨3573395, by rfl⟩ : syracuseStep 4764527 = 7146791) B7146791
theorem B3176351 : Blo 2117435 3176351 := bstep (se 1 (by rfl) ⟨2382263, by rfl⟩ : syracuseStep 3176351 = 4764527) B4764527
theorem B2117567 : Blo 2117435 2117567 := bstep (se 1 (by rfl) ⟨1588175, by rfl⟩ : syracuseStep 2117567 = 3176351) B3176351
theorem B3176357 : Blo 2117435 3176357 := bbase (se 4 (by rfl) ⟨297783, by rfl⟩ : syracuseStep 3176357 = 595567) (by norm_num)
theorem B2117571 : Blo 2117435 2117571 := bstep (se 1 (by rfl) ⟨1588178, by rfl⟩ : syracuseStep 2117571 = 3176357) B3176357
theorem B2680057 : Blo 2117435 2680057 := bbase (se 2 (by rfl) ⟨1005021, by rfl⟩ : syracuseStep 2680057 = 2010043) (by norm_num)
theorem B3573409 : Blo 2117435 3573409 := bstep (se 2 (by rfl) ⟨1340028, by rfl⟩ : syracuseStep 3573409 = 2680057) B2680057
theorem B4764545 : Blo 2117435 4764545 := bstep (se 2 (by rfl) ⟨1786704, by rfl⟩ : syracuseStep 4764545 = 3573409) B3573409
theorem B3176363 : Blo 2117435 3176363 := bstep (se 1 (by rfl) ⟨2382272, by rfl⟩ : syracuseStep 3176363 = 4764545) B4764545
theorem B2117575 : Blo 2117435 2117575 := bstep (se 1 (by rfl) ⟨1588181, by rfl⟩ : syracuseStep 2117575 = 3176363) B3176363
theorem B2382277 : Blo 2117435 2382277 := bbase (se 4 (by rfl) ⟨223338, by rfl⟩ : syracuseStep 2382277 = 446677) (by norm_num)
theorem B3176369 : Blo 2117435 3176369 := bstep (se 2 (by rfl) ⟨1191138, by rfl⟩ : syracuseStep 3176369 = 2382277) B2382277
theorem B2117579 : Blo 2117435 2117579 := bstep (se 1 (by rfl) ⟨1588184, by rfl⟩ : syracuseStep 2117579 = 3176369) B3176369
theorem B4020101 : Blo 2117435 4020101 := bbase (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) (by norm_num)
theorem B2680067 : Blo 2117435 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B7146845 : Blo 2117435 7146845 := bstep (se 3 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 7146845 = 2680067) B2680067
theorem B4764563 : Blo 2117435 4764563 := bstep (se 1 (by rfl) ⟨3573422, by rfl⟩ : syracuseStep 4764563 = 7146845) B7146845
theorem B3176375 : Blo 2117435 3176375 := bstep (se 1 (by rfl) ⟨2382281, by rfl⟩ : syracuseStep 3176375 = 4764563) B4764563
theorem B2117583 : Blo 2117435 2117583 := bstep (se 1 (by rfl) ⟨1588187, by rfl⟩ : syracuseStep 2117583 = 3176375) B3176375
theorem B3176381 : Blo 2117435 3176381 := bbase (se 3 (by rfl) ⟨595571, by rfl⟩ : syracuseStep 3176381 = 1191143) (by norm_num)
theorem B2117587 : Blo 2117435 2117587 := bstep (se 1 (by rfl) ⟨1588190, by rfl⟩ : syracuseStep 2117587 = 3176381) B3176381
theorem B4764581 : Blo 2117435 4764581 := bbase (se 4 (by rfl) ⟨446679, by rfl⟩ : syracuseStep 4764581 = 893359) (by norm_num)
theorem B3176387 : Blo 2117435 3176387 := bstep (se 1 (by rfl) ⟨2382290, by rfl⟩ : syracuseStep 3176387 = 4764581) B4764581
theorem B2117591 : Blo 2117435 2117591 := bstep (se 1 (by rfl) ⟨1588193, by rfl⟩ : syracuseStep 2117591 = 3176387) B3176387
theorem B5360165 : Blo 2117435 5360165 := bbase (se 4 (by rfl) ⟨502515, by rfl⟩ : syracuseStep 5360165 = 1005031) (by norm_num)
theorem B3573443 : Blo 2117435 3573443 := bstep (se 1 (by rfl) ⟨2680082, by rfl⟩ : syracuseStep 3573443 = 5360165) B5360165
theorem B2382295 : Blo 2117435 2382295 := bstep (se 1 (by rfl) ⟨1786721, by rfl⟩ : syracuseStep 2382295 = 3573443) B3573443
theorem B3176393 : Blo 2117435 3176393 := bstep (se 2 (by rfl) ⟨1191147, by rfl⟩ : syracuseStep 3176393 = 2382295) B2382295
theorem B2117595 : Blo 2117435 2117595 := bstep (se 1 (by rfl) ⟨1588196, by rfl⟩ : syracuseStep 2117595 = 3176393) B3176393
theorem B6030197 : Blo 2117435 6030197 := bbase (se 5 (by rfl) ⟨282665, by rfl⟩ : syracuseStep 6030197 = 565331) (by norm_num)
theorem B4020131 : Blo 2117435 4020131 := bstep (se 1 (by rfl) ⟨3015098, by rfl⟩ : syracuseStep 4020131 = 6030197) B6030197
theorem B10720349 : Blo 2117435 10720349 := bstep (se 3 (by rfl) ⟨2010065, by rfl⟩ : syracuseStep 10720349 = 4020131) B4020131
theorem B7146899 : Blo 2117435 7146899 := bstep (se 1 (by rfl) ⟨5360174, by rfl⟩ : syracuseStep 7146899 = 10720349) B10720349
theorem B4764599 : Blo 2117435 4764599 := bstep (se 1 (by rfl) ⟨3573449, by rfl⟩ : syracuseStep 4764599 = 7146899) B7146899
theorem B3176399 : Blo 2117435 3176399 := bstep (se 1 (by rfl) ⟨2382299, by rfl⟩ : syracuseStep 3176399 = 4764599) B4764599
theorem B2117599 : Blo 2117435 2117599 := bstep (se 1 (by rfl) ⟨1588199, by rfl⟩ : syracuseStep 2117599 = 3176399) B3176399
theorem B3176405 : Blo 2117435 3176405 := bbase (se 7 (by rfl) ⟨37223, by rfl⟩ : syracuseStep 3176405 = 74447) (by norm_num)
theorem B2117603 : Blo 2117435 2117603 := bstep (se 1 (by rfl) ⟨1588202, by rfl⟩ : syracuseStep 2117603 = 3176405) B3176405
theorem B8040293 : Blo 2117435 8040293 := bbase (se 4 (by rfl) ⟨753777, by rfl⟩ : syracuseStep 8040293 = 1507555) (by norm_num)
theorem B5360195 : Blo 2117435 5360195 := bstep (se 1 (by rfl) ⟨4020146, by rfl⟩ : syracuseStep 5360195 = 8040293) B8040293
theorem B3573463 : Blo 2117435 3573463 := bstep (se 1 (by rfl) ⟨2680097, by rfl⟩ : syracuseStep 3573463 = 5360195) B5360195
theorem B4764617 : Blo 2117435 4764617 := bstep (se 2 (by rfl) ⟨1786731, by rfl⟩ : syracuseStep 4764617 = 3573463) B3573463
theorem B3176411 : Blo 2117435 3176411 := bstep (se 1 (by rfl) ⟨2382308, by rfl⟩ : syracuseStep 3176411 = 4764617) B4764617
theorem B2117607 : Blo 2117435 2117607 := bstep (se 1 (by rfl) ⟨1588205, by rfl⟩ : syracuseStep 2117607 = 3176411) B3176411
theorem B2382313 : Blo 2117435 2382313 := bbase (se 2 (by rfl) ⟨893367, by rfl⟩ : syracuseStep 2382313 = 1786735) (by norm_num)
theorem B3176417 : Blo 2117435 3176417 := bstep (se 2 (by rfl) ⟨1191156, by rfl⟩ : syracuseStep 3176417 = 2382313) B2382313
theorem B2117611 : Blo 2117435 2117611 := bstep (se 1 (by rfl) ⟨1588208, by rfl⟩ : syracuseStep 2117611 = 3176417) B3176417
theorem B2261341 : Blo 2117435 2261341 := bbase (se 3 (by rfl) ⟨424001, by rfl⟩ : syracuseStep 2261341 = 848003) (by norm_num)
theorem B12060485 : Blo 2117435 12060485 := bstep (se 4 (by rfl) ⟨1130670, by rfl⟩ : syracuseStep 12060485 = 2261341) B2261341
theorem B8040323 : Blo 2117435 8040323 := bstep (se 1 (by rfl) ⟨6030242, by rfl⟩ : syracuseStep 8040323 = 12060485) B12060485
theorem B5360215 : Blo 2117435 5360215 := bstep (se 1 (by rfl) ⟨4020161, by rfl⟩ : syracuseStep 5360215 = 8040323) B8040323
theorem B7146953 : Blo 2117435 7146953 := bstep (se 2 (by rfl) ⟨2680107, by rfl⟩ : syracuseStep 7146953 = 5360215) B5360215
theorem B4764635 : Blo 2117435 4764635 := bstep (se 1 (by rfl) ⟨3573476, by rfl⟩ : syracuseStep 4764635 = 7146953) B7146953
theorem B3176423 : Blo 2117435 3176423 := bstep (se 1 (by rfl) ⟨2382317, by rfl⟩ : syracuseStep 3176423 = 4764635) B4764635
theorem B2117615 : Blo 2117435 2117615 := bstep (se 1 (by rfl) ⟨1588211, by rfl⟩ : syracuseStep 2117615 = 3176423) B3176423
theorem B3176429 : Blo 2117435 3176429 := bbase (se 3 (by rfl) ⟨595580, by rfl⟩ : syracuseStep 3176429 = 1191161) (by norm_num)
theorem B2117619 : Blo 2117435 2117619 := bstep (se 1 (by rfl) ⟨1588214, by rfl⟩ : syracuseStep 2117619 = 3176429) B3176429
theorem B4764653 : Blo 2117435 4764653 := bbase (se 3 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 4764653 = 1786745) (by norm_num)
theorem B3176435 : Blo 2117435 3176435 := bstep (se 1 (by rfl) ⟨2382326, by rfl⟩ : syracuseStep 3176435 = 4764653) B4764653
theorem B2117623 : Blo 2117435 2117623 := bstep (se 1 (by rfl) ⟨1588217, by rfl⟩ : syracuseStep 2117623 = 3176435) B3176435
theorem B4522709 : Blo 2117435 4522709 := bbase (se 7 (by rfl) ⟨53000, by rfl⟩ : syracuseStep 4522709 = 106001) (by norm_num)
theorem B3015139 : Blo 2117435 3015139 := bstep (se 1 (by rfl) ⟨2261354, by rfl⟩ : syracuseStep 3015139 = 4522709) B4522709
theorem B4020185 : Blo 2117435 4020185 := bstep (se 2 (by rfl) ⟨1507569, by rfl⟩ : syracuseStep 4020185 = 3015139) B3015139
theorem B2680123 : Blo 2117435 2680123 := bstep (se 1 (by rfl) ⟨2010092, by rfl⟩ : syracuseStep 2680123 = 4020185) B4020185
theorem B3573497 : Blo 2117435 3573497 := bstep (se 2 (by rfl) ⟨1340061, by rfl⟩ : syracuseStep 3573497 = 2680123) B2680123
theorem B2382331 : Blo 2117435 2382331 := bstep (se 1 (by rfl) ⟨1786748, by rfl⟩ : syracuseStep 2382331 = 3573497) B3573497
theorem B3176441 : Blo 2117435 3176441 := bstep (se 2 (by rfl) ⟨1191165, by rfl⟩ : syracuseStep 3176441 = 2382331) B2382331
theorem B2117627 : Blo 2117435 2117627 := bstep (se 1 (by rfl) ⟨1588220, by rfl⟩ : syracuseStep 2117627 = 3176441) B3176441
theorem B4584421 : Blo 2117435 4584421 := bbase (se 4 (by rfl) ⟨429789, by rfl⟩ : syracuseStep 4584421 = 859579) (by norm_num)
theorem B24450245 : Blo 2117435 24450245 := bstep (se 4 (by rfl) ⟨2292210, by rfl⟩ : syracuseStep 24450245 = 4584421) B4584421
theorem B16300163 : Blo 2117435 16300163 := bstep (se 1 (by rfl) ⟨12225122, by rfl⟩ : syracuseStep 16300163 = 24450245) B24450245
theorem B43467101 : Blo 2117435 43467101 := bstep (se 3 (by rfl) ⟨8150081, by rfl⟩ : syracuseStep 43467101 = 16300163) B16300163
theorem B28978067 : Blo 2117435 28978067 := bstep (se 1 (by rfl) ⟨21733550, by rfl⟩ : syracuseStep 28978067 = 43467101) B43467101
theorem B19318711 : Blo 2117435 19318711 := bstep (se 1 (by rfl) ⟨14489033, by rfl⟩ : syracuseStep 19318711 = 28978067) B28978067
theorem B25758281 : Blo 2117435 25758281 := bstep (se 2 (by rfl) ⟨9659355, by rfl⟩ : syracuseStep 25758281 = 19318711) B19318711
theorem B68688749 : Blo 2117435 68688749 := bstep (se 3 (by rfl) ⟨12879140, by rfl⟩ : syracuseStep 68688749 = 25758281) B25758281
theorem B183169997 : Blo 2117435 183169997 := bstep (se 3 (by rfl) ⟨34344374, by rfl⟩ : syracuseStep 183169997 = 68688749) B68688749
theorem B122113331 : Blo 2117435 122113331 := bstep (se 1 (by rfl) ⟨91584998, by rfl⟩ : syracuseStep 122113331 = 183169997) B183169997
theorem B81408887 : Blo 2117435 81408887 := bstep (se 1 (by rfl) ⟨61056665, by rfl⟩ : syracuseStep 81408887 = 122113331) B122113331
theorem B54272591 : Blo 2117435 54272591 := bstep (se 1 (by rfl) ⟨40704443, by rfl⟩ : syracuseStep 54272591 = 81408887) B81408887
theorem B36181727 : Blo 2117435 36181727 := bstep (se 1 (by rfl) ⟨27136295, by rfl⟩ : syracuseStep 36181727 = 54272591) B54272591
theorem B24121151 : Blo 2117435 24121151 := bstep (se 1 (by rfl) ⟨18090863, by rfl⟩ : syracuseStep 24121151 = 36181727) B36181727
theorem B16080767 : Blo 2117435 16080767 := bstep (se 1 (by rfl) ⟨12060575, by rfl⟩ : syracuseStep 16080767 = 24121151) B24121151
theorem B10720511 : Blo 2117435 10720511 := bstep (se 1 (by rfl) ⟨8040383, by rfl⟩ : syracuseStep 10720511 = 16080767) B16080767
theorem B7147007 : Blo 2117435 7147007 := bstep (se 1 (by rfl) ⟨5360255, by rfl⟩ : syracuseStep 7147007 = 10720511) B10720511
theorem B4764671 : Blo 2117435 4764671 := bstep (se 1 (by rfl) ⟨3573503, by rfl⟩ : syracuseStep 4764671 = 7147007) B7147007
theorem B3176447 : Blo 2117435 3176447 := bstep (se 1 (by rfl) ⟨2382335, by rfl⟩ : syracuseStep 3176447 = 4764671) B4764671
theorem B2117631 : Blo 2117435 2117631 := bstep (se 1 (by rfl) ⟨1588223, by rfl⟩ : syracuseStep 2117631 = 3176447) B3176447
theorem B3176453 : Blo 2117435 3176453 := bbase (se 4 (by rfl) ⟨297792, by rfl⟩ : syracuseStep 3176453 = 595585) (by norm_num)
theorem B2117635 : Blo 2117435 2117635 := bstep (se 1 (by rfl) ⟨1588226, by rfl⟩ : syracuseStep 2117635 = 3176453) B3176453
theorem B3573517 : Blo 2117435 3573517 := bbase (se 3 (by rfl) ⟨670034, by rfl⟩ : syracuseStep 3573517 = 1340069) (by norm_num)
theorem B4764689 : Blo 2117435 4764689 := bstep (se 2 (by rfl) ⟨1786758, by rfl⟩ : syracuseStep 4764689 = 3573517) B3573517
theorem B3176459 : Blo 2117435 3176459 := bstep (se 1 (by rfl) ⟨2382344, by rfl⟩ : syracuseStep 3176459 = 4764689) B4764689
theorem B2117639 : Blo 2117435 2117639 := bstep (se 1 (by rfl) ⟨1588229, by rfl⟩ : syracuseStep 2117639 = 3176459) B3176459
theorem B2382349 : Blo 2117435 2382349 := bbase (se 3 (by rfl) ⟨446690, by rfl⟩ : syracuseStep 2382349 = 893381) (by norm_num)
theorem B3176465 : Blo 2117435 3176465 := bstep (se 2 (by rfl) ⟨1191174, by rfl⟩ : syracuseStep 3176465 = 2382349) B2382349
theorem B2117643 : Blo 2117435 2117643 := bstep (se 1 (by rfl) ⟨1588232, by rfl⟩ : syracuseStep 2117643 = 3176465) B3176465
theorem B7147061 : Blo 2117435 7147061 := bbase (se 5 (by rfl) ⟨335018, by rfl⟩ : syracuseStep 7147061 = 670037) (by norm_num)
theorem B4764707 : Blo 2117435 4764707 := bstep (se 1 (by rfl) ⟨3573530, by rfl⟩ : syracuseStep 4764707 = 7147061) B7147061
theorem B3176471 : Blo 2117435 3176471 := bstep (se 1 (by rfl) ⟨2382353, by rfl⟩ : syracuseStep 3176471 = 4764707) B4764707
theorem B2117647 : Blo 2117435 2117647 := bstep (se 1 (by rfl) ⟨1588235, by rfl⟩ : syracuseStep 2117647 = 3176471) B3176471
theorem B3176477 : Blo 2117435 3176477 := bbase (se 3 (by rfl) ⟨595589, by rfl⟩ : syracuseStep 3176477 = 1191179) (by norm_num)
theorem B2117651 : Blo 2117435 2117651 := bstep (se 1 (by rfl) ⟨1588238, by rfl⟩ : syracuseStep 2117651 = 3176477) B3176477
theorem B4764725 : Blo 2117435 4764725 := bbase (se 5 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 4764725 = 446693) (by norm_num)
theorem B3176483 : Blo 2117435 3176483 := bstep (se 1 (by rfl) ⟨2382362, by rfl⟩ : syracuseStep 3176483 = 4764725) B4764725
theorem B2117655 : Blo 2117435 2117655 := bstep (se 1 (by rfl) ⟨1588241, by rfl⟩ : syracuseStep 2117655 = 3176483) B3176483
theorem B6784165 : Blo 2117435 6784165 := bbase (se 4 (by rfl) ⟨636015, by rfl⟩ : syracuseStep 6784165 = 1272031) (by norm_num)
theorem B9045553 : Blo 2117435 9045553 := bstep (se 2 (by rfl) ⟨3392082, by rfl⟩ : syracuseStep 9045553 = 6784165) B6784165
theorem B12060737 : Blo 2117435 12060737 := bstep (se 2 (by rfl) ⟨4522776, by rfl⟩ : syracuseStep 12060737 = 9045553) B9045553
theorem B8040491 : Blo 2117435 8040491 := bstep (se 1 (by rfl) ⟨6030368, by rfl⟩ : syracuseStep 8040491 = 12060737) B12060737
theorem B5360327 : Blo 2117435 5360327 := bstep (se 1 (by rfl) ⟨4020245, by rfl⟩ : syracuseStep 5360327 = 8040491) B8040491
theorem B3573551 : Blo 2117435 3573551 := bstep (se 1 (by rfl) ⟨2680163, by rfl⟩ : syracuseStep 3573551 = 5360327) B5360327
theorem B2382367 : Blo 2117435 2382367 := bstep (se 1 (by rfl) ⟨1786775, by rfl⟩ : syracuseStep 2382367 = 3573551) B3573551
theorem B3176489 : Blo 2117435 3176489 := bstep (se 2 (by rfl) ⟨1191183, by rfl⟩ : syracuseStep 3176489 = 2382367) B2382367
theorem B2117659 : Blo 2117435 2117659 := bstep (se 1 (by rfl) ⟨1588244, by rfl⟩ : syracuseStep 2117659 = 3176489) B3176489
theorem B5088133 : Blo 2117435 5088133 := bbase (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) (by norm_num)
theorem B6784177 : Blo 2117435 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B9045569 : Blo 2117435 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B6030379 : Blo 2117435 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B8040505 : Blo 2117435 8040505 := bstep (se 2 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 8040505 = 6030379) B6030379
theorem B10720673 : Blo 2117435 10720673 := bstep (se 2 (by rfl) ⟨4020252, by rfl⟩ : syracuseStep 10720673 = 8040505) B8040505
theorem B7147115 : Blo 2117435 7147115 := bstep (se 1 (by rfl) ⟨5360336, by rfl⟩ : syracuseStep 7147115 = 10720673) B10720673
theorem B4764743 : Blo 2117435 4764743 := bstep (se 1 (by rfl) ⟨3573557, by rfl⟩ : syracuseStep 4764743 = 7147115) B7147115
theorem B3176495 : Blo 2117435 3176495 := bstep (se 1 (by rfl) ⟨2382371, by rfl⟩ : syracuseStep 3176495 = 4764743) B4764743
theorem B2117663 : Blo 2117435 2117663 := bstep (se 1 (by rfl) ⟨1588247, by rfl⟩ : syracuseStep 2117663 = 3176495) B3176495
theorem B3176501 : Blo 2117435 3176501 := bbase (se 5 (by rfl) ⟨148898, by rfl⟩ : syracuseStep 3176501 = 297797) (by norm_num)
theorem B2117667 : Blo 2117435 2117667 := bstep (se 1 (by rfl) ⟨1588250, by rfl⟩ : syracuseStep 2117667 = 3176501) B3176501
theorem B5360357 : Blo 2117435 5360357 := bbase (se 4 (by rfl) ⟨502533, by rfl⟩ : syracuseStep 5360357 = 1005067) (by norm_num)
theorem B3573571 : Blo 2117435 3573571 := bstep (se 1 (by rfl) ⟨2680178, by rfl⟩ : syracuseStep 3573571 = 5360357) B5360357
theorem B4764761 : Blo 2117435 4764761 := bstep (se 2 (by rfl) ⟨1786785, by rfl⟩ : syracuseStep 4764761 = 3573571) B3573571
theorem B3176507 : Blo 2117435 3176507 := bstep (se 1 (by rfl) ⟨2382380, by rfl⟩ : syracuseStep 3176507 = 4764761) B4764761
theorem B2117671 : Blo 2117435 2117671 := bstep (se 1 (by rfl) ⟨1588253, by rfl⟩ : syracuseStep 2117671 = 3176507) B3176507
theorem B2382385 : Blo 2117435 2382385 := bbase (se 2 (by rfl) ⟨893394, by rfl⟩ : syracuseStep 2382385 = 1786789) (by norm_num)
theorem B3176513 : Blo 2117435 3176513 := bstep (se 2 (by rfl) ⟨1191192, by rfl⟩ : syracuseStep 3176513 = 2382385) B2382385
theorem B2117675 : Blo 2117435 2117675 := bstep (se 1 (by rfl) ⟨1588256, by rfl⟩ : syracuseStep 2117675 = 3176513) B3176513
theorem B6784229 : Blo 2117435 6784229 := bbase (se 4 (by rfl) ⟨636021, by rfl⟩ : syracuseStep 6784229 = 1272043) (by norm_num)
theorem B4522819 : Blo 2117435 4522819 := bstep (se 1 (by rfl) ⟨3392114, by rfl⟩ : syracuseStep 4522819 = 6784229) B6784229
theorem B6030425 : Blo 2117435 6030425 := bstep (se 2 (by rfl) ⟨2261409, by rfl⟩ : syracuseStep 6030425 = 4522819) B4522819
theorem B4020283 : Blo 2117435 4020283 := bstep (se 1 (by rfl) ⟨3015212, by rfl⟩ : syracuseStep 4020283 = 6030425) B6030425
theorem B5360377 : Blo 2117435 5360377 := bstep (se 2 (by rfl) ⟨2010141, by rfl⟩ : syracuseStep 5360377 = 4020283) B4020283
theorem B7147169 : Blo 2117435 7147169 := bstep (se 2 (by rfl) ⟨2680188, by rfl⟩ : syracuseStep 7147169 = 5360377) B5360377
theorem B4764779 : Blo 2117435 4764779 := bstep (se 1 (by rfl) ⟨3573584, by rfl⟩ : syracuseStep 4764779 = 7147169) B7147169
theorem B3176519 : Blo 2117435 3176519 := bstep (se 1 (by rfl) ⟨2382389, by rfl⟩ : syracuseStep 3176519 = 4764779) B4764779
theorem B2117679 : Blo 2117435 2117679 := bstep (se 1 (by rfl) ⟨1588259, by rfl⟩ : syracuseStep 2117679 = 3176519) B3176519
theorem B3176525 : Blo 2117435 3176525 := bbase (se 3 (by rfl) ⟨595598, by rfl⟩ : syracuseStep 3176525 = 1191197) (by norm_num)
theorem B2117683 : Blo 2117435 2117683 := bstep (se 1 (by rfl) ⟨1588262, by rfl⟩ : syracuseStep 2117683 = 3176525) B3176525
theorem B4764797 : Blo 2117435 4764797 := bbase (se 3 (by rfl) ⟨893399, by rfl⟩ : syracuseStep 4764797 = 1786799) (by norm_num)
theorem B3176531 : Blo 2117435 3176531 := bstep (se 1 (by rfl) ⟨2382398, by rfl⟩ : syracuseStep 3176531 = 4764797) B4764797
theorem B2117687 : Blo 2117435 2117687 := bstep (se 1 (by rfl) ⟨1588265, by rfl⟩ : syracuseStep 2117687 = 3176531) B3176531
theorem B3573605 : Blo 2117435 3573605 := bbase (se 4 (by rfl) ⟨335025, by rfl⟩ : syracuseStep 3573605 = 670051) (by norm_num)
theorem B2382403 : Blo 2117435 2382403 := bstep (se 1 (by rfl) ⟨1786802, by rfl⟩ : syracuseStep 2382403 = 3573605) B3573605
theorem B3176537 : Blo 2117435 3176537 := bstep (se 2 (by rfl) ⟨1191201, by rfl⟩ : syracuseStep 3176537 = 2382403) B2382403
theorem B2117691 : Blo 2117435 2117691 := bstep (se 1 (by rfl) ⟨1588268, by rfl⟩ : syracuseStep 2117691 = 3176537) B3176537
theorem B4522853 : Blo 2117435 4522853 := bbase (se 4 (by rfl) ⟨424017, by rfl⟩ : syracuseStep 4522853 = 848035) (by norm_num)
theorem B3015235 : Blo 2117435 3015235 := bstep (se 1 (by rfl) ⟨2261426, by rfl⟩ : syracuseStep 3015235 = 4522853) B4522853
theorem B16081253 : Blo 2117435 16081253 := bstep (se 4 (by rfl) ⟨1507617, by rfl⟩ : syracuseStep 16081253 = 3015235) B3015235
theorem B10720835 : Blo 2117435 10720835 := bstep (se 1 (by rfl) ⟨8040626, by rfl⟩ : syracuseStep 10720835 = 16081253) B16081253
theorem B7147223 : Blo 2117435 7147223 := bstep (se 1 (by rfl) ⟨5360417, by rfl⟩ : syracuseStep 7147223 = 10720835) B10720835
theorem B4764815 : Blo 2117435 4764815 := bstep (se 1 (by rfl) ⟨3573611, by rfl⟩ : syracuseStep 4764815 = 7147223) B7147223
theorem B3176543 : Blo 2117435 3176543 := bstep (se 1 (by rfl) ⟨2382407, by rfl⟩ : syracuseStep 3176543 = 4764815) B4764815
theorem B2117695 : Blo 2117435 2117695 := bstep (se 1 (by rfl) ⟨1588271, by rfl⟩ : syracuseStep 2117695 = 3176543) B3176543
theorem B3176549 : Blo 2117435 3176549 := bbase (se 4 (by rfl) ⟨297801, by rfl⟩ : syracuseStep 3176549 = 595603) (by norm_num)
theorem B2117699 : Blo 2117435 2117699 := bstep (se 1 (by rfl) ⟨1588274, by rfl⟩ : syracuseStep 2117699 = 3176549) B3176549
theorem B3816173 : Blo 2117435 3816173 := bbase (se 3 (by rfl) ⟨715532, by rfl⟩ : syracuseStep 3816173 = 1431065) (by norm_num)
theorem B10176461 : Blo 2117435 10176461 := bstep (se 3 (by rfl) ⟨1908086, by rfl⟩ : syracuseStep 10176461 = 3816173) B3816173
theorem B6784307 : Blo 2117435 6784307 := bstep (se 1 (by rfl) ⟨5088230, by rfl⟩ : syracuseStep 6784307 = 10176461) B10176461
theorem B4522871 : Blo 2117435 4522871 := bstep (se 1 (by rfl) ⟨3392153, by rfl⟩ : syracuseStep 4522871 = 6784307) B6784307
theorem B3015247 : Blo 2117435 3015247 := bstep (se 1 (by rfl) ⟨2261435, by rfl⟩ : syracuseStep 3015247 = 4522871) B4522871
theorem B4020329 : Blo 2117435 4020329 := bstep (se 2 (by rfl) ⟨1507623, by rfl⟩ : syracuseStep 4020329 = 3015247) B3015247
theorem B2680219 : Blo 2117435 2680219 := bstep (se 1 (by rfl) ⟨2010164, by rfl⟩ : syracuseStep 2680219 = 4020329) B4020329
theorem B3573625 : Blo 2117435 3573625 := bstep (se 2 (by rfl) ⟨1340109, by rfl⟩ : syracuseStep 3573625 = 2680219) B2680219
theorem B4764833 : Blo 2117435 4764833 := bstep (se 2 (by rfl) ⟨1786812, by rfl⟩ : syracuseStep 4764833 = 3573625) B3573625
theorem B3176555 : Blo 2117435 3176555 := bstep (se 1 (by rfl) ⟨2382416, by rfl⟩ : syracuseStep 3176555 = 4764833) B4764833
theorem B2117703 : Blo 2117435 2117703 := bstep (se 1 (by rfl) ⟨1588277, by rfl⟩ : syracuseStep 2117703 = 3176555) B3176555
theorem B2382421 : Blo 2117435 2382421 := bbase (se 8 (by rfl) ⟨13959, by rfl⟩ : syracuseStep 2382421 = 27919) (by norm_num)
theorem B3176561 : Blo 2117435 3176561 := bstep (se 2 (by rfl) ⟨1191210, by rfl⟩ : syracuseStep 3176561 = 2382421) B2382421
theorem B2117707 : Blo 2117435 2117707 := bstep (se 1 (by rfl) ⟨1588280, by rfl⟩ : syracuseStep 2117707 = 3176561) B3176561
theorem B2680229 : Blo 2117435 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B7147277 : Blo 2117435 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B4764851 : Blo 2117435 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B3176567 : Blo 2117435 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B2117711 : Blo 2117435 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B3176573 : Blo 2117435 3176573 := bbase (se 3 (by rfl) ⟨595607, by rfl⟩ : syracuseStep 3176573 = 1191215) (by norm_num)
theorem B2117715 : Blo 2117435 2117715 := bstep (se 1 (by rfl) ⟨1588286, by rfl⟩ : syracuseStep 2117715 = 3176573) B3176573
theorem B4764869 : Blo 2117435 4764869 := bbase (se 4 (by rfl) ⟨446706, by rfl⟩ : syracuseStep 4764869 = 893413) (by norm_num)
theorem B3176579 : Blo 2117435 3176579 := bstep (se 1 (by rfl) ⟨2382434, by rfl⟩ : syracuseStep 3176579 = 4764869) B4764869
theorem B2117719 : Blo 2117435 2117719 := bstep (se 1 (by rfl) ⟨1588289, by rfl⟩ : syracuseStep 2117719 = 3176579) B3176579
theorem B2862157 : Blo 2117435 2862157 := bbase (se 3 (by rfl) ⟨536654, by rfl⟩ : syracuseStep 2862157 = 1073309) (by norm_num)
theorem B3816209 : Blo 2117435 3816209 := bstep (se 2 (by rfl) ⟨1431078, by rfl⟩ : syracuseStep 3816209 = 2862157) B2862157
theorem B2544139 : Blo 2117435 2544139 := bstep (se 1 (by rfl) ⟨1908104, by rfl⟩ : syracuseStep 2544139 = 3816209) B3816209
theorem B13568741 : Blo 2117435 13568741 := bstep (se 4 (by rfl) ⟨1272069, by rfl⟩ : syracuseStep 13568741 = 2544139) B2544139
theorem B9045827 : Blo 2117435 9045827 := bstep (se 1 (by rfl) ⟨6784370, by rfl⟩ : syracuseStep 9045827 = 13568741) B13568741
theorem B6030551 : Blo 2117435 6030551 := bstep (se 1 (by rfl) ⟨4522913, by rfl⟩ : syracuseStep 6030551 = 9045827) B9045827
theorem B4020367 : Blo 2117435 4020367 := bstep (se 1 (by rfl) ⟨3015275, by rfl⟩ : syracuseStep 4020367 = 6030551) B6030551
theorem B5360489 : Blo 2117435 5360489 := bstep (se 2 (by rfl) ⟨2010183, by rfl⟩ : syracuseStep 5360489 = 4020367) B4020367
theorem B3573659 : Blo 2117435 3573659 := bstep (se 1 (by rfl) ⟨2680244, by rfl⟩ : syracuseStep 3573659 = 5360489) B5360489
theorem B2382439 : Blo 2117435 2382439 := bstep (se 1 (by rfl) ⟨1786829, by rfl⟩ : syracuseStep 2382439 = 3573659) B3573659
theorem B3176585 : Blo 2117435 3176585 := bstep (se 2 (by rfl) ⟨1191219, by rfl⟩ : syracuseStep 3176585 = 2382439) B2382439
theorem B2117723 : Blo 2117435 2117723 := bstep (se 1 (by rfl) ⟨1588292, by rfl⟩ : syracuseStep 2117723 = 3176585) B3176585
theorem B10720997 : Blo 2117435 10720997 := bbase (se 4 (by rfl) ⟨1005093, by rfl⟩ : syracuseStep 10720997 = 2010187) (by norm_num)
theorem B7147331 : Blo 2117435 7147331 := bstep (se 1 (by rfl) ⟨5360498, by rfl⟩ : syracuseStep 7147331 = 10720997) B10720997
theorem B4764887 : Blo 2117435 4764887 := bstep (se 1 (by rfl) ⟨3573665, by rfl⟩ : syracuseStep 4764887 = 7147331) B7147331
theorem B3176591 : Blo 2117435 3176591 := bstep (se 1 (by rfl) ⟨2382443, by rfl⟩ : syracuseStep 3176591 = 4764887) B4764887
theorem B2117727 : Blo 2117435 2117727 := bstep (se 1 (by rfl) ⟨1588295, by rfl⟩ : syracuseStep 2117727 = 3176591) B3176591
theorem B3176597 : Blo 2117435 3176597 := bbase (se 6 (by rfl) ⟨74451, by rfl⟩ : syracuseStep 3176597 = 148903) (by norm_num)
theorem B2117731 : Blo 2117435 2117731 := bstep (se 1 (by rfl) ⟨1588298, by rfl⟩ : syracuseStep 2117731 = 3176597) B3176597
theorem B9045877 : Blo 2117435 9045877 := bbase (se 5 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 9045877 = 848051) (by norm_num)
theorem B12061169 : Blo 2117435 12061169 := bstep (se 2 (by rfl) ⟨4522938, by rfl⟩ : syracuseStep 12061169 = 9045877) B9045877
theorem B8040779 : Blo 2117435 8040779 := bstep (se 1 (by rfl) ⟨6030584, by rfl⟩ : syracuseStep 8040779 = 12061169) B12061169
theorem B5360519 : Blo 2117435 5360519 := bstep (se 1 (by rfl) ⟨4020389, by rfl⟩ : syracuseStep 5360519 = 8040779) B8040779
theorem B3573679 : Blo 2117435 3573679 := bstep (se 1 (by rfl) ⟨2680259, by rfl⟩ : syracuseStep 3573679 = 5360519) B5360519
theorem B4764905 : Blo 2117435 4764905 := bstep (se 2 (by rfl) ⟨1786839, by rfl⟩ : syracuseStep 4764905 = 3573679) B3573679
theorem B3176603 : Blo 2117435 3176603 := bstep (se 1 (by rfl) ⟨2382452, by rfl⟩ : syracuseStep 3176603 = 4764905) B4764905
theorem B2117735 : Blo 2117435 2117735 := bstep (se 1 (by rfl) ⟨1588301, by rfl⟩ : syracuseStep 2117735 = 3176603) B3176603
theorem B2382457 : Blo 2117435 2382457 := bbase (se 2 (by rfl) ⟨893421, by rfl⟩ : syracuseStep 2382457 = 1786843) (by norm_num)
theorem B3176609 : Blo 2117435 3176609 := bstep (se 2 (by rfl) ⟨1191228, by rfl⟩ : syracuseStep 3176609 = 2382457) B2382457
theorem B2117739 : Blo 2117435 2117739 := bstep (se 1 (by rfl) ⟨1588304, by rfl⟩ : syracuseStep 2117739 = 3176609) B3176609
theorem B20353301 : Blo 2117435 20353301 := bbase (se 6 (by rfl) ⟨477030, by rfl⟩ : syracuseStep 20353301 = 954061) (by norm_num)
theorem B13568867 : Blo 2117435 13568867 := bstep (se 1 (by rfl) ⟨10176650, by rfl⟩ : syracuseStep 13568867 = 20353301) B20353301
theorem B9045911 : Blo 2117435 9045911 := bstep (se 1 (by rfl) ⟨6784433, by rfl⟩ : syracuseStep 9045911 = 13568867) B13568867
theorem B6030607 : Blo 2117435 6030607 := bstep (se 1 (by rfl) ⟨4522955, by rfl⟩ : syracuseStep 6030607 = 9045911) B9045911
theorem B8040809 : Blo 2117435 8040809 := bstep (se 2 (by rfl) ⟨3015303, by rfl⟩ : syracuseStep 8040809 = 6030607) B6030607
theorem B5360539 : Blo 2117435 5360539 := bstep (se 1 (by rfl) ⟨4020404, by rfl⟩ : syracuseStep 5360539 = 8040809) B8040809
theorem B7147385 : Blo 2117435 7147385 := bstep (se 2 (by rfl) ⟨2680269, by rfl⟩ : syracuseStep 7147385 = 5360539) B5360539
theorem B4764923 : Blo 2117435 4764923 := bstep (se 1 (by rfl) ⟨3573692, by rfl⟩ : syracuseStep 4764923 = 7147385) B7147385
theorem B3176615 : Blo 2117435 3176615 := bstep (se 1 (by rfl) ⟨2382461, by rfl⟩ : syracuseStep 3176615 = 4764923) B4764923
theorem B2117743 : Blo 2117435 2117743 := bstep (se 1 (by rfl) ⟨1588307, by rfl⟩ : syracuseStep 2117743 = 3176615) B3176615
theorem B3176621 : Blo 2117435 3176621 := bbase (se 3 (by rfl) ⟨595616, by rfl⟩ : syracuseStep 3176621 = 1191233) (by norm_num)
theorem B2117747 : Blo 2117435 2117747 := bstep (se 1 (by rfl) ⟨1588310, by rfl⟩ : syracuseStep 2117747 = 3176621) B3176621
theorem B4764941 : Blo 2117435 4764941 := bbase (se 3 (by rfl) ⟨893426, by rfl⟩ : syracuseStep 4764941 = 1786853) (by norm_num)
theorem B3176627 : Blo 2117435 3176627 := bstep (se 1 (by rfl) ⟨2382470, by rfl⟩ : syracuseStep 3176627 = 4764941) B4764941
theorem B2117751 : Blo 2117435 2117751 := bstep (se 1 (by rfl) ⟨1588313, by rfl⟩ : syracuseStep 2117751 = 3176627) B3176627
theorem B2680285 : Blo 2117435 2680285 := bbase (se 3 (by rfl) ⟨502553, by rfl⟩ : syracuseStep 2680285 = 1005107) (by norm_num)
theorem B3573713 : Blo 2117435 3573713 := bstep (se 2 (by rfl) ⟨1340142, by rfl⟩ : syracuseStep 3573713 = 2680285) B2680285
theorem B2382475 : Blo 2117435 2382475 := bstep (se 1 (by rfl) ⟨1786856, by rfl⟩ : syracuseStep 2382475 = 3573713) B3573713
theorem B3176633 : Blo 2117435 3176633 := bstep (se 2 (by rfl) ⟨1191237, by rfl⟩ : syracuseStep 3176633 = 2382475) B2382475
theorem B2117755 : Blo 2117435 2117755 := bstep (se 1 (by rfl) ⟨1588316, by rfl⟩ : syracuseStep 2117755 = 3176633) B3176633
theorem B18091957 : Blo 2117435 18091957 := bbase (se 5 (by rfl) ⟨848060, by rfl⟩ : syracuseStep 18091957 = 1696121) (by norm_num)
theorem B24122609 : Blo 2117435 24122609 := bstep (se 2 (by rfl) ⟨9045978, by rfl⟩ : syracuseStep 24122609 = 18091957) B18091957
theorem B16081739 : Blo 2117435 16081739 := bstep (se 1 (by rfl) ⟨12061304, by rfl⟩ : syracuseStep 16081739 = 24122609) B24122609
theorem B10721159 : Blo 2117435 10721159 := bstep (se 1 (by rfl) ⟨8040869, by rfl⟩ : syracuseStep 10721159 = 16081739) B16081739
theorem B7147439 : Blo 2117435 7147439 := bstep (se 1 (by rfl) ⟨5360579, by rfl⟩ : syracuseStep 7147439 = 10721159) B10721159
theorem B4764959 : Blo 2117435 4764959 := bstep (se 1 (by rfl) ⟨3573719, by rfl⟩ : syracuseStep 4764959 = 7147439) B7147439
theorem B3176639 : Blo 2117435 3176639 := bstep (se 1 (by rfl) ⟨2382479, by rfl⟩ : syracuseStep 3176639 = 4764959) B4764959
theorem B2117759 : Blo 2117435 2117759 := bstep (se 1 (by rfl) ⟨1588319, by rfl⟩ : syracuseStep 2117759 = 3176639) B3176639
theorem B3176645 : Blo 2117435 3176645 := bbase (se 4 (by rfl) ⟨297810, by rfl⟩ : syracuseStep 3176645 = 595621) (by norm_num)
theorem B2117763 : Blo 2117435 2117763 := bstep (se 1 (by rfl) ⟨1588322, by rfl⟩ : syracuseStep 2117763 = 3176645) B3176645
theorem B3573733 : Blo 2117435 3573733 := bbase (se 4 (by rfl) ⟨335037, by rfl⟩ : syracuseStep 3573733 = 670075) (by norm_num)
theorem B4764977 : Blo 2117435 4764977 := bstep (se 2 (by rfl) ⟨1786866, by rfl⟩ : syracuseStep 4764977 = 3573733) B3573733
theorem B3176651 : Blo 2117435 3176651 := bstep (se 1 (by rfl) ⟨2382488, by rfl⟩ : syracuseStep 3176651 = 4764977) B4764977
theorem B2117767 : Blo 2117435 2117767 := bstep (se 1 (by rfl) ⟨1588325, by rfl⟩ : syracuseStep 2117767 = 3176651) B3176651
theorem B2382493 : Blo 2117435 2382493 := bbase (se 3 (by rfl) ⟨446717, by rfl⟩ : syracuseStep 2382493 = 893435) (by norm_num)
theorem B3176657 : Blo 2117435 3176657 := bstep (se 2 (by rfl) ⟨1191246, by rfl⟩ : syracuseStep 3176657 = 2382493) B2382493
theorem B2117771 : Blo 2117435 2117771 := bstep (se 1 (by rfl) ⟨1588328, by rfl⟩ : syracuseStep 2117771 = 3176657) B3176657
theorem B7147493 : Blo 2117435 7147493 := bbase (se 4 (by rfl) ⟨670077, by rfl⟩ : syracuseStep 7147493 = 1340155) (by norm_num)
theorem B4764995 : Blo 2117435 4764995 := bstep (se 1 (by rfl) ⟨3573746, by rfl⟩ : syracuseStep 4764995 = 7147493) B7147493
theorem B3176663 : Blo 2117435 3176663 := bstep (se 1 (by rfl) ⟨2382497, by rfl⟩ : syracuseStep 3176663 = 4764995) B4764995
theorem B2117775 : Blo 2117435 2117775 := bstep (se 1 (by rfl) ⟨1588331, by rfl⟩ : syracuseStep 2117775 = 3176663) B3176663
theorem B3176669 : Blo 2117435 3176669 := bbase (se 3 (by rfl) ⟨595625, by rfl⟩ : syracuseStep 3176669 = 1191251) (by norm_num)
theorem B2117779 : Blo 2117435 2117779 := bstep (se 1 (by rfl) ⟨1588334, by rfl⟩ : syracuseStep 2117779 = 3176669) B3176669
theorem B4765013 : Blo 2117435 4765013 := bbase (se 13 (by rfl) ⟨872, by rfl⟩ : syracuseStep 4765013 = 1745) (by norm_num)
theorem B3176675 : Blo 2117435 3176675 := bstep (se 1 (by rfl) ⟨2382506, by rfl⟩ : syracuseStep 3176675 = 4765013) B4765013
theorem B2117783 : Blo 2117435 2117783 := bstep (se 1 (by rfl) ⟨1588337, by rfl⟩ : syracuseStep 2117783 = 3176675) B3176675
theorem B2261525 : Blo 2117435 2261525 := bbase (se 6 (by rfl) ⟨53004, by rfl⟩ : syracuseStep 2261525 = 106009) (by norm_num)
theorem B6030733 : Blo 2117435 6030733 := bstep (se 3 (by rfl) ⟨1130762, by rfl⟩ : syracuseStep 6030733 = 2261525) B2261525
theorem B8040977 : Blo 2117435 8040977 := bstep (se 2 (by rfl) ⟨3015366, by rfl⟩ : syracuseStep 8040977 = 6030733) B6030733
theorem B5360651 : Blo 2117435 5360651 := bstep (se 1 (by rfl) ⟨4020488, by rfl⟩ : syracuseStep 5360651 = 8040977) B8040977
theorem B3573767 : Blo 2117435 3573767 := bstep (se 1 (by rfl) ⟨2680325, by rfl⟩ : syracuseStep 3573767 = 5360651) B5360651
theorem B2382511 : Blo 2117435 2382511 := bstep (se 1 (by rfl) ⟨1786883, by rfl⟩ : syracuseStep 2382511 = 3573767) B3573767
theorem B3176681 : Blo 2117435 3176681 := bstep (se 2 (by rfl) ⟨1191255, by rfl⟩ : syracuseStep 3176681 = 2382511) B2382511
theorem B2117787 : Blo 2117435 2117787 := bstep (se 1 (by rfl) ⟨1588340, by rfl⟩ : syracuseStep 2117787 = 3176681) B3176681
theorem B2323661 : Blo 2117435 2323661 := bbase (se 3 (by rfl) ⟨435686, by rfl⟩ : syracuseStep 2323661 = 871373) (by norm_num)
theorem B6196429 : Blo 2117435 6196429 := bstep (se 3 (by rfl) ⟨1161830, by rfl⟩ : syracuseStep 6196429 = 2323661) B2323661
theorem B33047621 : Blo 2117435 33047621 := bstep (se 4 (by rfl) ⟨3098214, by rfl⟩ : syracuseStep 33047621 = 6196429) B6196429
theorem B22031747 : Blo 2117435 22031747 := bstep (se 1 (by rfl) ⟨16523810, by rfl⟩ : syracuseStep 22031747 = 33047621) B33047621
theorem B14687831 : Blo 2117435 14687831 := bstep (se 1 (by rfl) ⟨11015873, by rfl⟩ : syracuseStep 14687831 = 22031747) B22031747
theorem B9791887 : Blo 2117435 9791887 := bstep (se 1 (by rfl) ⟨7343915, by rfl⟩ : syracuseStep 9791887 = 14687831) B14687831
theorem B13055849 : Blo 2117435 13055849 := bstep (se 2 (by rfl) ⟨4895943, by rfl⟩ : syracuseStep 13055849 = 9791887) B9791887
theorem B8703899 : Blo 2117435 8703899 := bstep (se 1 (by rfl) ⟨6527924, by rfl⟩ : syracuseStep 8703899 = 13055849) B13055849
theorem B5802599 : Blo 2117435 5802599 := bstep (se 1 (by rfl) ⟨4351949, by rfl⟩ : syracuseStep 5802599 = 8703899) B8703899
theorem B3868399 : Blo 2117435 3868399 := bstep (se 1 (by rfl) ⟨2901299, by rfl⟩ : syracuseStep 3868399 = 5802599) B5802599
theorem B5157865 : Blo 2117435 5157865 := bstep (se 2 (by rfl) ⟨1934199, by rfl⟩ : syracuseStep 5157865 = 3868399) B3868399
theorem B6877153 : Blo 2117435 6877153 := bstep (se 2 (by rfl) ⟨2578932, by rfl⟩ : syracuseStep 6877153 = 5157865) B5157865
theorem B9169537 : Blo 2117435 9169537 := bstep (se 2 (by rfl) ⟨3438576, by rfl⟩ : syracuseStep 9169537 = 6877153) B6877153
theorem B12226049 : Blo 2117435 12226049 := bstep (se 2 (by rfl) ⟨4584768, by rfl⟩ : syracuseStep 12226049 = 9169537) B9169537
theorem B8150699 : Blo 2117435 8150699 := bstep (se 1 (by rfl) ⟨6113024, by rfl⟩ : syracuseStep 8150699 = 12226049) B12226049
theorem B5433799 : Blo 2117435 5433799 := bstep (se 1 (by rfl) ⟨4075349, by rfl⟩ : syracuseStep 5433799 = 8150699) B8150699
theorem B7245065 : Blo 2117435 7245065 := bstep (se 2 (by rfl) ⟨2716899, by rfl⟩ : syracuseStep 7245065 = 5433799) B5433799
theorem B19320173 : Blo 2117435 19320173 := bstep (se 3 (by rfl) ⟨3622532, by rfl⟩ : syracuseStep 19320173 = 7245065) B7245065
theorem B12880115 : Blo 2117435 12880115 := bstep (se 1 (by rfl) ⟨9660086, by rfl⟩ : syracuseStep 12880115 = 19320173) B19320173
theorem B8586743 : Blo 2117435 8586743 := bstep (se 1 (by rfl) ⟨6440057, by rfl⟩ : syracuseStep 8586743 = 12880115) B12880115
theorem B22897981 : Blo 2117435 22897981 := bstep (se 3 (by rfl) ⟨4293371, by rfl⟩ : syracuseStep 22897981 = 8586743) B8586743
theorem B30530641 : Blo 2117435 30530641 := bstep (se 2 (by rfl) ⟨11448990, by rfl⟩ : syracuseStep 30530641 = 22897981) B22897981
theorem B40707521 : Blo 2117435 40707521 := bstep (se 2 (by rfl) ⟨15265320, by rfl⟩ : syracuseStep 40707521 = 30530641) B30530641
theorem B27138347 : Blo 2117435 27138347 := bstep (se 1 (by rfl) ⟨20353760, by rfl⟩ : syracuseStep 27138347 = 40707521) B40707521
theorem B18092231 : Blo 2117435 18092231 := bstep (se 1 (by rfl) ⟨13569173, by rfl⟩ : syracuseStep 18092231 = 27138347) B27138347
theorem B12061487 : Blo 2117435 12061487 := bstep (se 1 (by rfl) ⟨9046115, by rfl⟩ : syracuseStep 12061487 = 18092231) B18092231
theorem B8040991 : Blo 2117435 8040991 := bstep (se 1 (by rfl) ⟨6030743, by rfl⟩ : syracuseStep 8040991 = 12061487) B12061487
theorem B10721321 : Blo 2117435 10721321 := bstep (se 2 (by rfl) ⟨4020495, by rfl⟩ : syracuseStep 10721321 = 8040991) B8040991
theorem B7147547 : Blo 2117435 7147547 := bstep (se 1 (by rfl) ⟨5360660, by rfl⟩ : syracuseStep 7147547 = 10721321) B10721321
theorem B4765031 : Blo 2117435 4765031 := bstep (se 1 (by rfl) ⟨3573773, by rfl⟩ : syracuseStep 4765031 = 7147547) B7147547
theorem B3176687 : Blo 2117435 3176687 := bstep (se 1 (by rfl) ⟨2382515, by rfl⟩ : syracuseStep 3176687 = 4765031) B4765031
theorem B2117791 : Blo 2117435 2117791 := bstep (se 1 (by rfl) ⟨1588343, by rfl⟩ : syracuseStep 2117791 = 3176687) B3176687
theorem B3176693 : Blo 2117435 3176693 := bbase (se 5 (by rfl) ⟨148907, by rfl⟩ : syracuseStep 3176693 = 297815) (by norm_num)
theorem B2117795 : Blo 2117435 2117795 := bstep (se 1 (by rfl) ⟨1588346, by rfl⟩ : syracuseStep 2117795 = 3176693) B3176693
theorem B4293389 : Blo 2117435 4293389 := bbase (se 3 (by rfl) ⟨805010, by rfl⟩ : syracuseStep 4293389 = 1610021) (by norm_num)
theorem B2862259 : Blo 2117435 2862259 := bstep (se 1 (by rfl) ⟨2146694, by rfl⟩ : syracuseStep 2862259 = 4293389) B4293389
theorem B15265381 : Blo 2117435 15265381 := bstep (se 4 (by rfl) ⟨1431129, by rfl⟩ : syracuseStep 15265381 = 2862259) B2862259
theorem B20353841 : Blo 2117435 20353841 := bstep (se 2 (by rfl) ⟨7632690, by rfl⟩ : syracuseStep 20353841 = 15265381) B15265381
theorem B13569227 : Blo 2117435 13569227 := bstep (se 1 (by rfl) ⟨10176920, by rfl⟩ : syracuseStep 13569227 = 20353841) B20353841
theorem B9046151 : Blo 2117435 9046151 := bstep (se 1 (by rfl) ⟨6784613, by rfl⟩ : syracuseStep 9046151 = 13569227) B13569227
theorem B6030767 : Blo 2117435 6030767 := bstep (se 1 (by rfl) ⟨4523075, by rfl⟩ : syracuseStep 6030767 = 9046151) B9046151
theorem B4020511 : Blo 2117435 4020511 := bstep (se 1 (by rfl) ⟨3015383, by rfl⟩ : syracuseStep 4020511 = 6030767) B6030767
theorem B5360681 : Blo 2117435 5360681 := bstep (se 2 (by rfl) ⟨2010255, by rfl⟩ : syracuseStep 5360681 = 4020511) B4020511
theorem B3573787 : Blo 2117435 3573787 := bstep (se 1 (by rfl) ⟨2680340, by rfl⟩ : syracuseStep 3573787 = 5360681) B5360681
theorem B4765049 : Blo 2117435 4765049 := bstep (se 2 (by rfl) ⟨1786893, by rfl⟩ : syracuseStep 4765049 = 3573787) B3573787
theorem B3176699 : Blo 2117435 3176699 := bstep (se 1 (by rfl) ⟨2382524, by rfl⟩ : syracuseStep 3176699 = 4765049) B4765049
theorem B2117799 : Blo 2117435 2117799 := bstep (se 1 (by rfl) ⟨1588349, by rfl⟩ : syracuseStep 2117799 = 3176699) B3176699
theorem B2382529 : Blo 2117435 2382529 := bbase (se 2 (by rfl) ⟨893448, by rfl⟩ : syracuseStep 2382529 = 1786897) (by norm_num)
theorem B3176705 : Blo 2117435 3176705 := bstep (se 2 (by rfl) ⟨1191264, by rfl⟩ : syracuseStep 3176705 = 2382529) B2382529
theorem B2117803 : Blo 2117435 2117803 := bstep (se 1 (by rfl) ⟨1588352, by rfl⟩ : syracuseStep 2117803 = 3176705) B3176705
theorem B5360701 : Blo 2117435 5360701 := bbase (se 3 (by rfl) ⟨1005131, by rfl⟩ : syracuseStep 5360701 = 2010263) (by norm_num)
theorem B7147601 : Blo 2117435 7147601 := bstep (se 2 (by rfl) ⟨2680350, by rfl⟩ : syracuseStep 7147601 = 5360701) B5360701
theorem B4765067 : Blo 2117435 4765067 := bstep (se 1 (by rfl) ⟨3573800, by rfl⟩ : syracuseStep 4765067 = 7147601) B7147601
theorem B3176711 : Blo 2117435 3176711 := bstep (se 1 (by rfl) ⟨2382533, by rfl⟩ : syracuseStep 3176711 = 4765067) B4765067
theorem B2117807 : Blo 2117435 2117807 := bstep (se 1 (by rfl) ⟨1588355, by rfl⟩ : syracuseStep 2117807 = 3176711) B3176711
theorem B3176717 : Blo 2117435 3176717 := bbase (se 3 (by rfl) ⟨595634, by rfl⟩ : syracuseStep 3176717 = 1191269) (by norm_num)
theorem B2117811 : Blo 2117435 2117811 := bstep (se 1 (by rfl) ⟨1588358, by rfl⟩ : syracuseStep 2117811 = 3176717) B3176717
theorem B4765085 : Blo 2117435 4765085 := bbase (se 3 (by rfl) ⟨893453, by rfl⟩ : syracuseStep 4765085 = 1786907) (by norm_num)
theorem B3176723 : Blo 2117435 3176723 := bstep (se 1 (by rfl) ⟨2382542, by rfl⟩ : syracuseStep 3176723 = 4765085) B4765085
theorem B2117815 : Blo 2117435 2117815 := bstep (se 1 (by rfl) ⟨1588361, by rfl⟩ : syracuseStep 2117815 = 3176723) B3176723
theorem B3573821 : Blo 2117435 3573821 := bbase (se 3 (by rfl) ⟨670091, by rfl⟩ : syracuseStep 3573821 = 1340183) (by norm_num)
theorem B2382547 : Blo 2117435 2382547 := bstep (se 1 (by rfl) ⟨1786910, by rfl⟩ : syracuseStep 2382547 = 3573821) B3573821
theorem B3176729 : Blo 2117435 3176729 := bstep (se 2 (by rfl) ⟨1191273, by rfl⟩ : syracuseStep 3176729 = 2382547) B2382547
theorem B2117819 : Blo 2117435 2117819 := bstep (se 1 (by rfl) ⟨1588364, by rfl⟩ : syracuseStep 2117819 = 3176729) B3176729
theorem B3816389 : Blo 2117435 3816389 := bbase (se 4 (by rfl) ⟨357786, by rfl⟩ : syracuseStep 3816389 = 715573) (by norm_num)
theorem B2544259 : Blo 2117435 2544259 := bstep (se 1 (by rfl) ⟨1908194, by rfl⟩ : syracuseStep 2544259 = 3816389) B3816389
theorem B3392345 : Blo 2117435 3392345 := bstep (se 2 (by rfl) ⟨1272129, by rfl⟩ : syracuseStep 3392345 = 2544259) B2544259
theorem B2261563 : Blo 2117435 2261563 := bstep (se 1 (by rfl) ⟨1696172, by rfl⟩ : syracuseStep 2261563 = 3392345) B3392345
theorem B12061669 : Blo 2117435 12061669 := bstep (se 4 (by rfl) ⟨1130781, by rfl⟩ : syracuseStep 12061669 = 2261563) B2261563
theorem B16082225 : Blo 2117435 16082225 := bstep (se 2 (by rfl) ⟨6030834, by rfl⟩ : syracuseStep 16082225 = 12061669) B12061669
theorem B10721483 : Blo 2117435 10721483 := bstep (se 1 (by rfl) ⟨8041112, by rfl⟩ : syracuseStep 10721483 = 16082225) B16082225
theorem B7147655 : Blo 2117435 7147655 := bstep (se 1 (by rfl) ⟨5360741, by rfl⟩ : syracuseStep 7147655 = 10721483) B10721483
theorem B4765103 : Blo 2117435 4765103 := bstep (se 1 (by rfl) ⟨3573827, by rfl⟩ : syracuseStep 4765103 = 7147655) B7147655
theorem B3176735 : Blo 2117435 3176735 := bstep (se 1 (by rfl) ⟨2382551, by rfl⟩ : syracuseStep 3176735 = 4765103) B4765103
theorem B2117823 : Blo 2117435 2117823 := bstep (se 1 (by rfl) ⟨1588367, by rfl⟩ : syracuseStep 2117823 = 3176735) B3176735
theorem B3176741 : Blo 2117435 3176741 := bbase (se 4 (by rfl) ⟨297819, by rfl⟩ : syracuseStep 3176741 = 595639) (by norm_num)
theorem B2117827 : Blo 2117435 2117827 := bstep (se 1 (by rfl) ⟨1588370, by rfl⟩ : syracuseStep 2117827 = 3176741) B3176741
theorem B2680381 : Blo 2117435 2680381 := bbase (se 3 (by rfl) ⟨502571, by rfl⟩ : syracuseStep 2680381 = 1005143) (by norm_num)
theorem B3573841 : Blo 2117435 3573841 := bstep (se 2 (by rfl) ⟨1340190, by rfl⟩ : syracuseStep 3573841 = 2680381) B2680381
theorem B4765121 : Blo 2117435 4765121 := bstep (se 2 (by rfl) ⟨1786920, by rfl⟩ : syracuseStep 4765121 = 3573841) B3573841
theorem B3176747 : Blo 2117435 3176747 := bstep (se 1 (by rfl) ⟨2382560, by rfl⟩ : syracuseStep 3176747 = 4765121) B4765121
theorem B2117831 : Blo 2117435 2117831 := bstep (se 1 (by rfl) ⟨1588373, by rfl⟩ : syracuseStep 2117831 = 3176747) B3176747
theorem B2382565 : Blo 2117435 2382565 := bbase (se 4 (by rfl) ⟨223365, by rfl⟩ : syracuseStep 2382565 = 446731) (by norm_num)
theorem B3176753 : Blo 2117435 3176753 := bstep (se 2 (by rfl) ⟨1191282, by rfl⟩ : syracuseStep 3176753 = 2382565) B2382565
theorem B2117835 : Blo 2117435 2117835 := bstep (se 1 (by rfl) ⟨1588376, by rfl⟩ : syracuseStep 2117835 = 3176753) B3176753
theorem B5088557 : Blo 2117435 5088557 := bbase (se 3 (by rfl) ⟨954104, by rfl⟩ : syracuseStep 5088557 = 1908209) (by norm_num)
theorem B3392371 : Blo 2117435 3392371 := bstep (se 1 (by rfl) ⟨2544278, by rfl⟩ : syracuseStep 3392371 = 5088557) B5088557
theorem B4523161 : Blo 2117435 4523161 := bstep (se 2 (by rfl) ⟨1696185, by rfl⟩ : syracuseStep 4523161 = 3392371) B3392371
theorem B6030881 : Blo 2117435 6030881 := bstep (se 2 (by rfl) ⟨2261580, by rfl⟩ : syracuseStep 6030881 = 4523161) B4523161
theorem B4020587 : Blo 2117435 4020587 := bstep (se 1 (by rfl) ⟨3015440, by rfl⟩ : syracuseStep 4020587 = 6030881) B6030881
theorem B2680391 : Blo 2117435 2680391 := bstep (se 1 (by rfl) ⟨2010293, by rfl⟩ : syracuseStep 2680391 = 4020587) B4020587
theorem B7147709 : Blo 2117435 7147709 := bstep (se 3 (by rfl) ⟨1340195, by rfl⟩ : syracuseStep 7147709 = 2680391) B2680391
theorem B4765139 : Blo 2117435 4765139 := bstep (se 1 (by rfl) ⟨3573854, by rfl⟩ : syracuseStep 4765139 = 7147709) B7147709
theorem B3176759 : Blo 2117435 3176759 := bstep (se 1 (by rfl) ⟨2382569, by rfl⟩ : syracuseStep 3176759 = 4765139) B4765139
theorem B2117839 : Blo 2117435 2117839 := bstep (se 1 (by rfl) ⟨1588379, by rfl⟩ : syracuseStep 2117839 = 3176759) B3176759
theorem B3176765 : Blo 2117435 3176765 := bbase (se 3 (by rfl) ⟨595643, by rfl⟩ : syracuseStep 3176765 = 1191287) (by norm_num)
theorem B2117843 : Blo 2117435 2117843 := bstep (se 1 (by rfl) ⟨1588382, by rfl⟩ : syracuseStep 2117843 = 3176765) B3176765
theorem B4765157 : Blo 2117435 4765157 := bbase (se 4 (by rfl) ⟨446733, by rfl⟩ : syracuseStep 4765157 = 893467) (by norm_num)
theorem B3176771 : Blo 2117435 3176771 := bstep (se 1 (by rfl) ⟨2382578, by rfl⟩ : syracuseStep 3176771 = 4765157) B4765157
theorem B2117847 : Blo 2117435 2117847 := bstep (se 1 (by rfl) ⟨1588385, by rfl⟩ : syracuseStep 2117847 = 3176771) B3176771
theorem B5360813 : Blo 2117435 5360813 := bbase (se 3 (by rfl) ⟨1005152, by rfl⟩ : syracuseStep 5360813 = 2010305) (by norm_num)
theorem B3573875 : Blo 2117435 3573875 := bstep (se 1 (by rfl) ⟨2680406, by rfl⟩ : syracuseStep 3573875 = 5360813) B5360813
theorem B2382583 : Blo 2117435 2382583 := bstep (se 1 (by rfl) ⟨1786937, by rfl⟩ : syracuseStep 2382583 = 3573875) B3573875
theorem B3176777 : Blo 2117435 3176777 := bstep (se 2 (by rfl) ⟨1191291, by rfl⟩ : syracuseStep 3176777 = 2382583) B2382583
theorem B2117851 : Blo 2117435 2117851 := bstep (se 1 (by rfl) ⟨1588388, by rfl⟩ : syracuseStep 2117851 = 3176777) B3176777
theorem B3868517 : Blo 2117435 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B10316045 : Blo 2117435 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B27509453 : Blo 2117435 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B18339635 : Blo 2117435 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B48905693 : Blo 2117435 48905693 := bstep (se 3 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 48905693 = 18339635) B18339635
theorem B32603795 : Blo 2117435 32603795 := bstep (se 1 (by rfl) ⟨24452846, by rfl⟩ : syracuseStep 32603795 = 48905693) B48905693
theorem B21735863 : Blo 2117435 21735863 := bstep (se 1 (by rfl) ⟨16301897, by rfl⟩ : syracuseStep 21735863 = 32603795) B32603795
theorem B14490575 : Blo 2117435 14490575 := bstep (se 1 (by rfl) ⟨10867931, by rfl⟩ : syracuseStep 14490575 = 21735863) B21735863
theorem B9660383 : Blo 2117435 9660383 := bstep (se 1 (by rfl) ⟨7245287, by rfl⟩ : syracuseStep 9660383 = 14490575) B14490575
theorem B6440255 : Blo 2117435 6440255 := bstep (se 1 (by rfl) ⟨4830191, by rfl⟩ : syracuseStep 6440255 = 9660383) B9660383
theorem B4293503 : Blo 2117435 4293503 := bstep (se 1 (by rfl) ⟨3220127, by rfl⟩ : syracuseStep 4293503 = 6440255) B6440255
theorem B2862335 : Blo 2117435 2862335 := bstep (se 1 (by rfl) ⟨2146751, by rfl⟩ : syracuseStep 2862335 = 4293503) B4293503
theorem B7632893 : Blo 2117435 7632893 := bstep (se 3 (by rfl) ⟨1431167, by rfl⟩ : syracuseStep 7632893 = 2862335) B2862335
theorem B5088595 : Blo 2117435 5088595 := bstep (se 1 (by rfl) ⟨3816446, by rfl⟩ : syracuseStep 5088595 = 7632893) B7632893
theorem B6784793 : Blo 2117435 6784793 := bstep (se 2 (by rfl) ⟨2544297, by rfl⟩ : syracuseStep 6784793 = 5088595) B5088595
theorem B4523195 : Blo 2117435 4523195 := bstep (se 1 (by rfl) ⟨3392396, by rfl⟩ : syracuseStep 4523195 = 6784793) B6784793
theorem B3015463 : Blo 2117435 3015463 := bstep (se 1 (by rfl) ⟨2261597, by rfl⟩ : syracuseStep 3015463 = 4523195) B4523195
theorem B4020617 : Blo 2117435 4020617 := bstep (se 2 (by rfl) ⟨1507731, by rfl⟩ : syracuseStep 4020617 = 3015463) B3015463
theorem B10721645 : Blo 2117435 10721645 := bstep (se 3 (by rfl) ⟨2010308, by rfl⟩ : syracuseStep 10721645 = 4020617) B4020617
theorem B7147763 : Blo 2117435 7147763 := bstep (se 1 (by rfl) ⟨5360822, by rfl⟩ : syracuseStep 7147763 = 10721645) B10721645
theorem B4765175 : Blo 2117435 4765175 := bstep (se 1 (by rfl) ⟨3573881, by rfl⟩ : syracuseStep 4765175 = 7147763) B7147763
theorem B3176783 : Blo 2117435 3176783 := bstep (se 1 (by rfl) ⟨2382587, by rfl⟩ : syracuseStep 3176783 = 4765175) B4765175
theorem B2117855 : Blo 2117435 2117855 := bstep (se 1 (by rfl) ⟨1588391, by rfl⟩ : syracuseStep 2117855 = 3176783) B3176783
theorem B3176789 : Blo 2117435 3176789 := bbase (se 10 (by rfl) ⟨4653, by rfl⟩ : syracuseStep 3176789 = 9307) (by norm_num)
theorem B2117859 : Blo 2117435 2117859 := bstep (se 1 (by rfl) ⟨1588394, by rfl⟩ : syracuseStep 2117859 = 3176789) B3176789
theorem B6030949 : Blo 2117435 6030949 := bbase (se 4 (by rfl) ⟨565401, by rfl⟩ : syracuseStep 6030949 = 1130803) (by norm_num)
theorem B8041265 : Blo 2117435 8041265 := bstep (se 2 (by rfl) ⟨3015474, by rfl⟩ : syracuseStep 8041265 = 6030949) B6030949
theorem B5360843 : Blo 2117435 5360843 := bstep (se 1 (by rfl) ⟨4020632, by rfl⟩ : syracuseStep 5360843 = 8041265) B8041265
theorem B3573895 : Blo 2117435 3573895 := bstep (se 1 (by rfl) ⟨2680421, by rfl⟩ : syracuseStep 3573895 = 5360843) B5360843
theorem B4765193 : Blo 2117435 4765193 := bstep (se 2 (by rfl) ⟨1786947, by rfl⟩ : syracuseStep 4765193 = 3573895) B3573895
theorem B3176795 : Blo 2117435 3176795 := bstep (se 1 (by rfl) ⟨2382596, by rfl⟩ : syracuseStep 3176795 = 4765193) B4765193
theorem B2117863 : Blo 2117435 2117863 := bstep (se 1 (by rfl) ⟨1588397, by rfl⟩ : syracuseStep 2117863 = 3176795) B3176795
theorem B2382601 : Blo 2117435 2382601 := bbase (se 2 (by rfl) ⟨893475, by rfl⟩ : syracuseStep 2382601 = 1786951) (by norm_num)
theorem B3176801 : Blo 2117435 3176801 := bstep (se 2 (by rfl) ⟨1191300, by rfl⟩ : syracuseStep 3176801 = 2382601) B2382601
theorem B2117867 : Blo 2117435 2117867 := bstep (se 1 (by rfl) ⟨1588400, by rfl⟩ : syracuseStep 2117867 = 3176801) B3176801
theorem B7632949 : Blo 2117435 7632949 := bbase (se 5 (by rfl) ⟨357794, by rfl⟩ : syracuseStep 7632949 = 715589) (by norm_num)
theorem B10177265 : Blo 2117435 10177265 := bstep (se 2 (by rfl) ⟨3816474, by rfl⟩ : syracuseStep 10177265 = 7632949) B7632949
theorem B27139373 : Blo 2117435 27139373 := bstep (se 3 (by rfl) ⟨5088632, by rfl⟩ : syracuseStep 27139373 = 10177265) B10177265
theorem B18092915 : Blo 2117435 18092915 := bstep (se 1 (by rfl) ⟨13569686, by rfl⟩ : syracuseStep 18092915 = 27139373) B27139373
theorem B12061943 : Blo 2117435 12061943 := bstep (se 1 (by rfl) ⟨9046457, by rfl⟩ : syracuseStep 12061943 = 18092915) B18092915
theorem B8041295 : Blo 2117435 8041295 := bstep (se 1 (by rfl) ⟨6030971, by rfl⟩ : syracuseStep 8041295 = 12061943) B12061943
theorem B5360863 : Blo 2117435 5360863 := bstep (se 1 (by rfl) ⟨4020647, by rfl⟩ : syracuseStep 5360863 = 8041295) B8041295
theorem B7147817 : Blo 2117435 7147817 := bstep (se 2 (by rfl) ⟨2680431, by rfl⟩ : syracuseStep 7147817 = 5360863) B5360863
theorem B4765211 : Blo 2117435 4765211 := bstep (se 1 (by rfl) ⟨3573908, by rfl⟩ : syracuseStep 4765211 = 7147817) B7147817
theorem B3176807 : Blo 2117435 3176807 := bstep (se 1 (by rfl) ⟨2382605, by rfl⟩ : syracuseStep 3176807 = 4765211) B4765211
theorem B2117871 : Blo 2117435 2117871 := bstep (se 1 (by rfl) ⟨1588403, by rfl⟩ : syracuseStep 2117871 = 3176807) B3176807
theorem B3176813 : Blo 2117435 3176813 := bbase (se 3 (by rfl) ⟨595652, by rfl⟩ : syracuseStep 3176813 = 1191305) (by norm_num)
theorem B2117875 : Blo 2117435 2117875 := bstep (se 1 (by rfl) ⟨1588406, by rfl⟩ : syracuseStep 2117875 = 3176813) B3176813
theorem B4765229 : Blo 2117435 4765229 := bbase (se 3 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 4765229 = 1786961) (by norm_num)
theorem B3176819 : Blo 2117435 3176819 := bstep (se 1 (by rfl) ⟨2382614, by rfl⟩ : syracuseStep 3176819 = 4765229) B4765229
theorem B2117879 : Blo 2117435 2117879 := bstep (se 1 (by rfl) ⟨1588409, by rfl⟩ : syracuseStep 2117879 = 3176819) B3176819
theorem B2579045 : Blo 2117435 2579045 := bbase (se 4 (by rfl) ⟨241785, by rfl⟩ : syracuseStep 2579045 = 483571) (by norm_num)
theorem B6877453 : Blo 2117435 6877453 := bstep (se 3 (by rfl) ⟨1289522, by rfl⟩ : syracuseStep 6877453 = 2579045) B2579045
theorem B9169937 : Blo 2117435 9169937 := bstep (se 2 (by rfl) ⟨3438726, by rfl⟩ : syracuseStep 9169937 = 6877453) B6877453
theorem B6113291 : Blo 2117435 6113291 := bstep (se 1 (by rfl) ⟨4584968, by rfl⟩ : syracuseStep 6113291 = 9169937) B9169937
theorem B16302109 : Blo 2117435 16302109 := bstep (se 3 (by rfl) ⟨3056645, by rfl⟩ : syracuseStep 16302109 = 6113291) B6113291
theorem B21736145 : Blo 2117435 21736145 := bstep (se 2 (by rfl) ⟨8151054, by rfl⟩ : syracuseStep 21736145 = 16302109) B16302109
theorem B57963053 : Blo 2117435 57963053 := bstep (se 3 (by rfl) ⟨10868072, by rfl⟩ : syracuseStep 57963053 = 21736145) B21736145
theorem B38642035 : Blo 2117435 38642035 := bstep (se 1 (by rfl) ⟨28981526, by rfl⟩ : syracuseStep 38642035 = 57963053) B57963053
theorem B51522713 : Blo 2117435 51522713 := bstep (se 2 (by rfl) ⟨19321017, by rfl⟩ : syracuseStep 51522713 = 38642035) B38642035
theorem B34348475 : Blo 2117435 34348475 := bstep (se 1 (by rfl) ⟨25761356, by rfl⟩ : syracuseStep 34348475 = 51522713) B51522713
theorem B22898983 : Blo 2117435 22898983 := bstep (se 1 (by rfl) ⟨17174237, by rfl⟩ : syracuseStep 22898983 = 34348475) B34348475
theorem B30531977 : Blo 2117435 30531977 := bstep (se 2 (by rfl) ⟨11449491, by rfl⟩ : syracuseStep 30531977 = 22898983) B22898983
theorem B20354651 : Blo 2117435 20354651 := bstep (se 1 (by rfl) ⟨15265988, by rfl⟩ : syracuseStep 20354651 = 30531977) B30531977
theorem B13569767 : Blo 2117435 13569767 := bstep (se 1 (by rfl) ⟨10177325, by rfl⟩ : syracuseStep 13569767 = 20354651) B20354651
theorem B9046511 : Blo 2117435 9046511 := bstep (se 1 (by rfl) ⟨6784883, by rfl⟩ : syracuseStep 9046511 = 13569767) B13569767
theorem B6031007 : Blo 2117435 6031007 := bstep (se 1 (by rfl) ⟨4523255, by rfl⟩ : syracuseStep 6031007 = 9046511) B9046511
theorem B4020671 : Blo 2117435 4020671 := bstep (se 1 (by rfl) ⟨3015503, by rfl⟩ : syracuseStep 4020671 = 6031007) B6031007
theorem B2680447 : Blo 2117435 2680447 := bstep (se 1 (by rfl) ⟨2010335, by rfl⟩ : syracuseStep 2680447 = 4020671) B4020671
theorem B3573929 : Blo 2117435 3573929 := bstep (se 2 (by rfl) ⟨1340223, by rfl⟩ : syracuseStep 3573929 = 2680447) B2680447
theorem B2382619 : Blo 2117435 2382619 := bstep (se 1 (by rfl) ⟨1786964, by rfl⟩ : syracuseStep 2382619 = 3573929) B3573929
theorem B3176825 : Blo 2117435 3176825 := bstep (se 2 (by rfl) ⟨1191309, by rfl⟩ : syracuseStep 3176825 = 2382619) B2382619
theorem B2117883 : Blo 2117435 2117883 := bstep (se 1 (by rfl) ⟨1588412, by rfl⟩ : syracuseStep 2117883 = 3176825) B3176825
theorem B10316197 : Blo 2117435 10316197 := bbase (se 4 (by rfl) ⟨967143, by rfl⟩ : syracuseStep 10316197 = 1934287) (by norm_num)
theorem B13754929 : Blo 2117435 13754929 := bstep (se 2 (by rfl) ⟨5158098, by rfl⟩ : syracuseStep 13754929 = 10316197) B10316197
theorem B18339905 : Blo 2117435 18339905 := bstep (se 2 (by rfl) ⟨6877464, by rfl⟩ : syracuseStep 18339905 = 13754929) B13754929
theorem B48906413 : Blo 2117435 48906413 := bstep (se 3 (by rfl) ⟨9169952, by rfl⟩ : syracuseStep 48906413 = 18339905) B18339905
theorem B32604275 : Blo 2117435 32604275 := bstep (se 1 (by rfl) ⟨24453206, by rfl⟩ : syracuseStep 32604275 = 48906413) B48906413
theorem B21736183 : Blo 2117435 21736183 := bstep (se 1 (by rfl) ⟨16302137, by rfl⟩ : syracuseStep 21736183 = 32604275) B32604275
theorem B28981577 : Blo 2117435 28981577 := bstep (se 2 (by rfl) ⟨10868091, by rfl⟩ : syracuseStep 28981577 = 21736183) B21736183
theorem B19321051 : Blo 2117435 19321051 := bstep (se 1 (by rfl) ⟨14490788, by rfl⟩ : syracuseStep 19321051 = 28981577) B28981577
theorem B25761401 : Blo 2117435 25761401 := bstep (se 2 (by rfl) ⟨9660525, by rfl⟩ : syracuseStep 25761401 = 19321051) B19321051
theorem B17174267 : Blo 2117435 17174267 := bstep (se 1 (by rfl) ⟨12880700, by rfl⟩ : syracuseStep 17174267 = 25761401) B25761401
theorem B11449511 : Blo 2117435 11449511 := bstep (se 1 (by rfl) ⟨8587133, by rfl⟩ : syracuseStep 11449511 = 17174267) B17174267
theorem B7633007 : Blo 2117435 7633007 := bstep (se 1 (by rfl) ⟨5724755, by rfl⟩ : syracuseStep 7633007 = 11449511) B11449511
theorem B5088671 : Blo 2117435 5088671 := bstep (se 1 (by rfl) ⟨3816503, by rfl⟩ : syracuseStep 5088671 = 7633007) B7633007
theorem B3392447 : Blo 2117435 3392447 := bstep (se 1 (by rfl) ⟨2544335, by rfl⟩ : syracuseStep 3392447 = 5088671) B5088671
theorem B36186101 : Blo 2117435 36186101 := bstep (se 5 (by rfl) ⟨1696223, by rfl⟩ : syracuseStep 36186101 = 3392447) B3392447
theorem B24124067 : Blo 2117435 24124067 := bstep (se 1 (by rfl) ⟨18093050, by rfl⟩ : syracuseStep 24124067 = 36186101) B36186101
theorem B16082711 : Blo 2117435 16082711 := bstep (se 1 (by rfl) ⟨12062033, by rfl⟩ : syracuseStep 16082711 = 24124067) B24124067
theorem B10721807 : Blo 2117435 10721807 := bstep (se 1 (by rfl) ⟨8041355, by rfl⟩ : syracuseStep 10721807 = 16082711) B16082711
theorem B7147871 : Blo 2117435 7147871 := bstep (se 1 (by rfl) ⟨5360903, by rfl⟩ : syracuseStep 7147871 = 10721807) B10721807
theorem B4765247 : Blo 2117435 4765247 := bstep (se 1 (by rfl) ⟨3573935, by rfl⟩ : syracuseStep 4765247 = 7147871) B7147871
theorem B3176831 : Blo 2117435 3176831 := bstep (se 1 (by rfl) ⟨2382623, by rfl⟩ : syracuseStep 3176831 = 4765247) B4765247
theorem B2117887 : Blo 2117435 2117887 := bstep (se 1 (by rfl) ⟨1588415, by rfl⟩ : syracuseStep 2117887 = 3176831) B3176831
theorem B3176837 : Blo 2117435 3176837 := bbase (se 4 (by rfl) ⟨297828, by rfl⟩ : syracuseStep 3176837 = 595657) (by norm_num)
theorem B2117891 : Blo 2117435 2117891 := bstep (se 1 (by rfl) ⟨1588418, by rfl⟩ : syracuseStep 2117891 = 3176837) B3176837
theorem B3573949 : Blo 2117435 3573949 := bbase (se 3 (by rfl) ⟨670115, by rfl⟩ : syracuseStep 3573949 = 1340231) (by norm_num)
theorem B4765265 : Blo 2117435 4765265 := bstep (se 2 (by rfl) ⟨1786974, by rfl⟩ : syracuseStep 4765265 = 3573949) B3573949
theorem B3176843 : Blo 2117435 3176843 := bstep (se 1 (by rfl) ⟨2382632, by rfl⟩ : syracuseStep 3176843 = 4765265) B4765265
theorem B2117895 : Blo 2117435 2117895 := bstep (se 1 (by rfl) ⟨1588421, by rfl⟩ : syracuseStep 2117895 = 3176843) B3176843
theorem B2382637 : Blo 2117435 2382637 := bbase (se 3 (by rfl) ⟨446744, by rfl⟩ : syracuseStep 2382637 = 893489) (by norm_num)
theorem B3176849 : Blo 2117435 3176849 := bstep (se 2 (by rfl) ⟨1191318, by rfl⟩ : syracuseStep 3176849 = 2382637) B2382637
theorem B2117899 : Blo 2117435 2117899 := bstep (se 1 (by rfl) ⟨1588424, by rfl⟩ : syracuseStep 2117899 = 3176849) B3176849
theorem B7147925 : Blo 2117435 7147925 := bbase (se 6 (by rfl) ⟨167529, by rfl⟩ : syracuseStep 7147925 = 335059) (by norm_num)
theorem B4765283 : Blo 2117435 4765283 := bstep (se 1 (by rfl) ⟨3573962, by rfl⟩ : syracuseStep 4765283 = 7147925) B7147925
theorem B3176855 : Blo 2117435 3176855 := bstep (se 1 (by rfl) ⟨2382641, by rfl⟩ : syracuseStep 3176855 = 4765283) B4765283
theorem B2117903 : Blo 2117435 2117903 := bstep (se 1 (by rfl) ⟨1588427, by rfl⟩ : syracuseStep 2117903 = 3176855) B3176855
theorem B3176861 : Blo 2117435 3176861 := bbase (se 3 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 3176861 = 1191323) (by norm_num)
theorem B2117907 : Blo 2117435 2117907 := bstep (se 1 (by rfl) ⟨1588430, by rfl⟩ : syracuseStep 2117907 = 3176861) B3176861
theorem B4765301 : Blo 2117435 4765301 := bbase (se 5 (by rfl) ⟨223373, by rfl⟩ : syracuseStep 4765301 = 446747) (by norm_num)
theorem B3176867 : Blo 2117435 3176867 := bstep (se 1 (by rfl) ⟨2382650, by rfl⟩ : syracuseStep 3176867 = 4765301) B4765301
theorem B2117911 : Blo 2117435 2117911 := bstep (se 1 (by rfl) ⟨1588433, by rfl⟩ : syracuseStep 2117911 = 3176867) B3176867
theorem B7633109 : Blo 2117435 7633109 := bbase (se 7 (by rfl) ⟨89450, by rfl⟩ : syracuseStep 7633109 = 178901) (by norm_num)
theorem B5088739 : Blo 2117435 5088739 := bstep (se 1 (by rfl) ⟨3816554, by rfl⟩ : syracuseStep 5088739 = 7633109) B7633109
theorem B6784985 : Blo 2117435 6784985 := bstep (se 2 (by rfl) ⟨2544369, by rfl⟩ : syracuseStep 6784985 = 5088739) B5088739
theorem B18093293 : Blo 2117435 18093293 := bstep (se 3 (by rfl) ⟨3392492, by rfl⟩ : syracuseStep 18093293 = 6784985) B6784985
theorem B12062195 : Blo 2117435 12062195 := bstep (se 1 (by rfl) ⟨9046646, by rfl⟩ : syracuseStep 12062195 = 18093293) B18093293
theorem B8041463 : Blo 2117435 8041463 := bstep (se 1 (by rfl) ⟨6031097, by rfl⟩ : syracuseStep 8041463 = 12062195) B12062195
theorem B5360975 : Blo 2117435 5360975 := bstep (se 1 (by rfl) ⟨4020731, by rfl⟩ : syracuseStep 5360975 = 8041463) B8041463
theorem B3573983 : Blo 2117435 3573983 := bstep (se 1 (by rfl) ⟨2680487, by rfl⟩ : syracuseStep 3573983 = 5360975) B5360975
theorem B2382655 : Blo 2117435 2382655 := bstep (se 1 (by rfl) ⟨1786991, by rfl⟩ : syracuseStep 2382655 = 3573983) B3573983
theorem B3176873 : Blo 2117435 3176873 := bstep (se 2 (by rfl) ⟨1191327, by rfl⟩ : syracuseStep 3176873 = 2382655) B2382655
theorem B2117915 : Blo 2117435 2117915 := bstep (se 1 (by rfl) ⟨1588436, by rfl⟩ : syracuseStep 2117915 = 3176873) B3176873
theorem B8041477 : Blo 2117435 8041477 := bbase (se 4 (by rfl) ⟨753888, by rfl⟩ : syracuseStep 8041477 = 1507777) (by norm_num)
theorem B10721969 : Blo 2117435 10721969 := bstep (se 2 (by rfl) ⟨4020738, by rfl⟩ : syracuseStep 10721969 = 8041477) B8041477
theorem B7147979 : Blo 2117435 7147979 := bstep (se 1 (by rfl) ⟨5360984, by rfl⟩ : syracuseStep 7147979 = 10721969) B10721969
theorem B4765319 : Blo 2117435 4765319 := bstep (se 1 (by rfl) ⟨3573989, by rfl⟩ : syracuseStep 4765319 = 7147979) B7147979
theorem B3176879 : Blo 2117435 3176879 := bstep (se 1 (by rfl) ⟨2382659, by rfl⟩ : syracuseStep 3176879 = 4765319) B4765319
theorem B2117919 : Blo 2117435 2117919 := bstep (se 1 (by rfl) ⟨1588439, by rfl⟩ : syracuseStep 2117919 = 3176879) B3176879
theorem B3176885 : Blo 2117435 3176885 := bbase (se 5 (by rfl) ⟨148916, by rfl⟩ : syracuseStep 3176885 = 297833) (by norm_num)
theorem B2117923 : Blo 2117435 2117923 := bstep (se 1 (by rfl) ⟨1588442, by rfl⟩ : syracuseStep 2117923 = 3176885) B3176885
theorem B5361005 : Blo 2117435 5361005 := bbase (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) (by norm_num)
theorem B3574003 : Blo 2117435 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B4765337 : Blo 2117435 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B3176891 : Blo 2117435 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B2117927 : Blo 2117435 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B2382673 : Blo 2117435 2382673 := bbase (se 2 (by rfl) ⟨893502, by rfl⟩ : syracuseStep 2382673 = 1787005) (by norm_num)
theorem B3176897 : Blo 2117435 3176897 := bstep (se 2 (by rfl) ⟨1191336, by rfl⟩ : syracuseStep 3176897 = 2382673) B2382673
theorem B2117931 : Blo 2117435 2117931 := bstep (se 1 (by rfl) ⟨1588448, by rfl⟩ : syracuseStep 2117931 = 3176897) B3176897
theorem B3392525 : Blo 2117435 3392525 := bbase (se 3 (by rfl) ⟨636098, by rfl⟩ : syracuseStep 3392525 = 1272197) (by norm_num)
theorem B2261683 : Blo 2117435 2261683 := bstep (se 1 (by rfl) ⟨1696262, by rfl⟩ : syracuseStep 2261683 = 3392525) B3392525
theorem B3015577 : Blo 2117435 3015577 := bstep (se 2 (by rfl) ⟨1130841, by rfl⟩ : syracuseStep 3015577 = 2261683) B2261683
theorem B4020769 : Blo 2117435 4020769 := bstep (se 2 (by rfl) ⟨1507788, by rfl⟩ : syracuseStep 4020769 = 3015577) B3015577
theorem B5361025 : Blo 2117435 5361025 := bstep (se 2 (by rfl) ⟨2010384, by rfl⟩ : syracuseStep 5361025 = 4020769) B4020769
theorem B7148033 : Blo 2117435 7148033 := bstep (se 2 (by rfl) ⟨2680512, by rfl⟩ : syracuseStep 7148033 = 5361025) B5361025
theorem B4765355 : Blo 2117435 4765355 := bstep (se 1 (by rfl) ⟨3574016, by rfl⟩ : syracuseStep 4765355 = 7148033) B7148033
theorem B3176903 : Blo 2117435 3176903 := bstep (se 1 (by rfl) ⟨2382677, by rfl⟩ : syracuseStep 3176903 = 4765355) B4765355
theorem B2117935 : Blo 2117435 2117935 := bstep (se 1 (by rfl) ⟨1588451, by rfl⟩ : syracuseStep 2117935 = 3176903) B3176903
theorem B3176909 : Blo 2117435 3176909 := bbase (se 3 (by rfl) ⟨595670, by rfl⟩ : syracuseStep 3176909 = 1191341) (by norm_num)
theorem B2117939 : Blo 2117435 2117939 := bstep (se 1 (by rfl) ⟨1588454, by rfl⟩ : syracuseStep 2117939 = 3176909) B3176909
theorem B4765373 : Blo 2117435 4765373 := bbase (se 3 (by rfl) ⟨893507, by rfl⟩ : syracuseStep 4765373 = 1787015) (by norm_num)
theorem B3176915 : Blo 2117435 3176915 := bstep (se 1 (by rfl) ⟨2382686, by rfl⟩ : syracuseStep 3176915 = 4765373) B4765373
theorem B2117943 : Blo 2117435 2117943 := bstep (se 1 (by rfl) ⟨1588457, by rfl⟩ : syracuseStep 2117943 = 3176915) B3176915
theorem B3574037 : Blo 2117435 3574037 := bbase (se 6 (by rfl) ⟨83766, by rfl⟩ : syracuseStep 3574037 = 167533) (by norm_num)
theorem B2382691 : Blo 2117435 2382691 := bstep (se 1 (by rfl) ⟨1787018, by rfl⟩ : syracuseStep 2382691 = 3574037) B3574037
theorem B3176921 : Blo 2117435 3176921 := bstep (se 2 (by rfl) ⟨1191345, by rfl⟩ : syracuseStep 3176921 = 2382691) B2382691
theorem B2117947 : Blo 2117435 2117947 := bstep (se 1 (by rfl) ⟨1588460, by rfl⟩ : syracuseStep 2117947 = 3176921) B3176921
theorem B30532949 : Blo 2117435 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B20355299 : Blo 2117435 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B13570199 : Blo 2117435 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B9046799 : Blo 2117435 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B6031199 : Blo 2117435 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B16083197 : Blo 2117435 16083197 := bstep (se 3 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 16083197 = 6031199) B6031199
theorem B10722131 : Blo 2117435 10722131 := bstep (se 1 (by rfl) ⟨8041598, by rfl⟩ : syracuseStep 10722131 = 16083197) B16083197
theorem B7148087 : Blo 2117435 7148087 := bstep (se 1 (by rfl) ⟨5361065, by rfl⟩ : syracuseStep 7148087 = 10722131) B10722131
theorem B4765391 : Blo 2117435 4765391 := bstep (se 1 (by rfl) ⟨3574043, by rfl⟩ : syracuseStep 4765391 = 7148087) B7148087
theorem B3176927 : Blo 2117435 3176927 := bstep (se 1 (by rfl) ⟨2382695, by rfl⟩ : syracuseStep 3176927 = 4765391) B4765391
theorem B2117951 : Blo 2117435 2117951 := bstep (se 1 (by rfl) ⟨1588463, by rfl⟩ : syracuseStep 2117951 = 3176927) B3176927
theorem B3176933 : Blo 2117435 3176933 := bbase (se 4 (by rfl) ⟨297837, by rfl⟩ : syracuseStep 3176933 = 595675) (by norm_num)
theorem B2117955 : Blo 2117435 2117955 := bstep (se 1 (by rfl) ⟨1588466, by rfl⟩ : syracuseStep 2117955 = 3176933) B3176933
theorem B5088845 : Blo 2117435 5088845 := bbase (se 3 (by rfl) ⟨954158, by rfl⟩ : syracuseStep 5088845 = 1908317) (by norm_num)
theorem B13570253 : Blo 2117435 13570253 := bstep (se 3 (by rfl) ⟨2544422, by rfl⟩ : syracuseStep 13570253 = 5088845) B5088845
theorem B9046835 : Blo 2117435 9046835 := bstep (se 1 (by rfl) ⟨6785126, by rfl⟩ : syracuseStep 9046835 = 13570253) B13570253
theorem B6031223 : Blo 2117435 6031223 := bstep (se 1 (by rfl) ⟨4523417, by rfl⟩ : syracuseStep 6031223 = 9046835) B9046835
theorem B4020815 : Blo 2117435 4020815 := bstep (se 1 (by rfl) ⟨3015611, by rfl⟩ : syracuseStep 4020815 = 6031223) B6031223
theorem B2680543 : Blo 2117435 2680543 := bstep (se 1 (by rfl) ⟨2010407, by rfl⟩ : syracuseStep 2680543 = 4020815) B4020815
theorem B3574057 : Blo 2117435 3574057 := bstep (se 2 (by rfl) ⟨1340271, by rfl⟩ : syracuseStep 3574057 = 2680543) B2680543
theorem B4765409 : Blo 2117435 4765409 := bstep (se 2 (by rfl) ⟨1787028, by rfl⟩ : syracuseStep 4765409 = 3574057) B3574057
theorem B3176939 : Blo 2117435 3176939 := bstep (se 1 (by rfl) ⟨2382704, by rfl⟩ : syracuseStep 3176939 = 4765409) B4765409
theorem B2117959 : Blo 2117435 2117959 := bstep (se 1 (by rfl) ⟨1588469, by rfl⟩ : syracuseStep 2117959 = 3176939) B3176939
theorem B2382709 : Blo 2117435 2382709 := bbase (se 5 (by rfl) ⟨111689, by rfl⟩ : syracuseStep 2382709 = 223379) (by norm_num)
theorem B3176945 : Blo 2117435 3176945 := bstep (se 2 (by rfl) ⟨1191354, by rfl⟩ : syracuseStep 3176945 = 2382709) B2382709
theorem B2117963 : Blo 2117435 2117963 := bstep (se 1 (by rfl) ⟨1588472, by rfl⟩ : syracuseStep 2117963 = 3176945) B3176945
theorem B2680553 : Blo 2117435 2680553 := bbase (se 2 (by rfl) ⟨1005207, by rfl⟩ : syracuseStep 2680553 = 2010415) (by norm_num)
theorem B7148141 : Blo 2117435 7148141 := bstep (se 3 (by rfl) ⟨1340276, by rfl⟩ : syracuseStep 7148141 = 2680553) B2680553
theorem B4765427 : Blo 2117435 4765427 := bstep (se 1 (by rfl) ⟨3574070, by rfl⟩ : syracuseStep 4765427 = 7148141) B7148141
theorem B3176951 : Blo 2117435 3176951 := bstep (se 1 (by rfl) ⟨2382713, by rfl⟩ : syracuseStep 3176951 = 4765427) B4765427
theorem B2117967 : Blo 2117435 2117967 := bstep (se 1 (by rfl) ⟨1588475, by rfl⟩ : syracuseStep 2117967 = 3176951) B3176951
theorem B3176957 : Blo 2117435 3176957 := bbase (se 3 (by rfl) ⟨595679, by rfl⟩ : syracuseStep 3176957 = 1191359) (by norm_num)
theorem B2117971 : Blo 2117435 2117971 := bstep (se 1 (by rfl) ⟨1588478, by rfl⟩ : syracuseStep 2117971 = 3176957) B3176957
theorem B4765445 : Blo 2117435 4765445 := bbase (se 4 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 4765445 = 893521) (by norm_num)
theorem B3176963 : Blo 2117435 3176963 := bstep (se 1 (by rfl) ⟨2382722, by rfl⟩ : syracuseStep 3176963 = 4765445) B4765445
theorem B2117975 : Blo 2117435 2117975 := bstep (se 1 (by rfl) ⟨1588481, by rfl⟩ : syracuseStep 2117975 = 3176963) B3176963
theorem B4020853 : Blo 2117435 4020853 := bbase (se 5 (by rfl) ⟨188477, by rfl⟩ : syracuseStep 4020853 = 376955) (by norm_num)
theorem B5361137 : Blo 2117435 5361137 := bstep (se 2 (by rfl) ⟨2010426, by rfl⟩ : syracuseStep 5361137 = 4020853) B4020853
theorem B3574091 : Blo 2117435 3574091 := bstep (se 1 (by rfl) ⟨2680568, by rfl⟩ : syracuseStep 3574091 = 5361137) B5361137
theorem B2382727 : Blo 2117435 2382727 := bstep (se 1 (by rfl) ⟨1787045, by rfl⟩ : syracuseStep 2382727 = 3574091) B3574091
theorem B3176969 : Blo 2117435 3176969 := bstep (se 2 (by rfl) ⟨1191363, by rfl⟩ : syracuseStep 3176969 = 2382727) B2382727
theorem B2117979 : Blo 2117435 2117979 := bstep (se 1 (by rfl) ⟨1588484, by rfl⟩ : syracuseStep 2117979 = 3176969) B3176969
theorem B10722293 : Blo 2117435 10722293 := bbase (se 5 (by rfl) ⟨502607, by rfl⟩ : syracuseStep 10722293 = 1005215) (by norm_num)
theorem B7148195 : Blo 2117435 7148195 := bstep (se 1 (by rfl) ⟨5361146, by rfl⟩ : syracuseStep 7148195 = 10722293) B10722293
theorem B4765463 : Blo 2117435 4765463 := bstep (se 1 (by rfl) ⟨3574097, by rfl⟩ : syracuseStep 4765463 = 7148195) B7148195
theorem B3176975 : Blo 2117435 3176975 := bstep (se 1 (by rfl) ⟨2382731, by rfl⟩ : syracuseStep 3176975 = 4765463) B4765463
theorem B2117983 : Blo 2117435 2117983 := bstep (se 1 (by rfl) ⟨1588487, by rfl⟩ : syracuseStep 2117983 = 3176975) B3176975
theorem B3176981 : Blo 2117435 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B2117987 : Blo 2117435 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B18093941 : Blo 2117435 18093941 := bbase (se 5 (by rfl) ⟨848153, by rfl⟩ : syracuseStep 18093941 = 1696307) (by norm_num)
theorem B12062627 : Blo 2117435 12062627 := bstep (se 1 (by rfl) ⟨9046970, by rfl⟩ : syracuseStep 12062627 = 18093941) B18093941
theorem B8041751 : Blo 2117435 8041751 := bstep (se 1 (by rfl) ⟨6031313, by rfl⟩ : syracuseStep 8041751 = 12062627) B12062627
theorem B5361167 : Blo 2117435 5361167 := bstep (se 1 (by rfl) ⟨4020875, by rfl⟩ : syracuseStep 5361167 = 8041751) B8041751
theorem B3574111 : Blo 2117435 3574111 := bstep (se 1 (by rfl) ⟨2680583, by rfl⟩ : syracuseStep 3574111 = 5361167) B5361167
theorem B4765481 : Blo 2117435 4765481 := bstep (se 2 (by rfl) ⟨1787055, by rfl⟩ : syracuseStep 4765481 = 3574111) B3574111
theorem B3176987 : Blo 2117435 3176987 := bstep (se 1 (by rfl) ⟨2382740, by rfl⟩ : syracuseStep 3176987 = 4765481) B4765481
theorem B2117991 : Blo 2117435 2117991 := bstep (se 1 (by rfl) ⟨1588493, by rfl⟩ : syracuseStep 2117991 = 3176987) B3176987
theorem B2382745 : Blo 2117435 2382745 := bbase (se 2 (by rfl) ⟨893529, by rfl⟩ : syracuseStep 2382745 = 1787059) (by norm_num)
theorem B3176993 : Blo 2117435 3176993 := bstep (se 2 (by rfl) ⟨1191372, by rfl⟩ : syracuseStep 3176993 = 2382745) B2382745
theorem B2117995 : Blo 2117435 2117995 := bstep (se 1 (by rfl) ⟨1588496, by rfl⟩ : syracuseStep 2117995 = 3176993) B3176993
theorem B8041781 : Blo 2117435 8041781 := bbase (se 5 (by rfl) ⟨376958, by rfl⟩ : syracuseStep 8041781 = 753917) (by norm_num)
theorem B5361187 : Blo 2117435 5361187 := bstep (se 1 (by rfl) ⟨4020890, by rfl⟩ : syracuseStep 5361187 = 8041781) B8041781
theorem B7148249 : Blo 2117435 7148249 := bstep (se 2 (by rfl) ⟨2680593, by rfl⟩ : syracuseStep 7148249 = 5361187) B5361187
theorem B4765499 : Blo 2117435 4765499 := bstep (se 1 (by rfl) ⟨3574124, by rfl⟩ : syracuseStep 4765499 = 7148249) B7148249
theorem B3176999 : Blo 2117435 3176999 := bstep (se 1 (by rfl) ⟨2382749, by rfl⟩ : syracuseStep 3176999 = 4765499) B4765499
theorem B2117999 : Blo 2117435 2117999 := bstep (se 1 (by rfl) ⟨1588499, by rfl⟩ : syracuseStep 2117999 = 3176999) B3176999
theorem B3177005 : Blo 2117435 3177005 := bbase (se 3 (by rfl) ⟨595688, by rfl⟩ : syracuseStep 3177005 = 1191377) (by norm_num)
theorem B2118003 : Blo 2117435 2118003 := bstep (se 1 (by rfl) ⟨1588502, by rfl⟩ : syracuseStep 2118003 = 3177005) B3177005
theorem B4765517 : Blo 2117435 4765517 := bbase (se 3 (by rfl) ⟨893534, by rfl⟩ : syracuseStep 4765517 = 1787069) (by norm_num)
theorem B3177011 : Blo 2117435 3177011 := bstep (se 1 (by rfl) ⟨2382758, by rfl⟩ : syracuseStep 3177011 = 4765517) B4765517
theorem B2118007 : Blo 2117435 2118007 := bstep (se 1 (by rfl) ⟨1588505, by rfl⟩ : syracuseStep 2118007 = 3177011) B3177011
theorem B2680609 : Blo 2117435 2680609 := bbase (se 2 (by rfl) ⟨1005228, by rfl⟩ : syracuseStep 2680609 = 2010457) (by norm_num)
theorem B3574145 : Blo 2117435 3574145 := bstep (se 2 (by rfl) ⟨1340304, by rfl⟩ : syracuseStep 3574145 = 2680609) B2680609
theorem B2382763 : Blo 2117435 2382763 := bstep (se 1 (by rfl) ⟨1787072, by rfl⟩ : syracuseStep 2382763 = 3574145) B3574145
theorem B3177017 : Blo 2117435 3177017 := bstep (se 2 (by rfl) ⟨1191381, by rfl⟩ : syracuseStep 3177017 = 2382763) B2382763
theorem B2118011 : Blo 2117435 2118011 := bstep (se 1 (by rfl) ⟨1588508, by rfl⟩ : syracuseStep 2118011 = 3177017) B3177017
theorem B24125525 : Blo 2117435 24125525 := bbase (se 8 (by rfl) ⟨141360, by rfl⟩ : syracuseStep 24125525 = 282721) (by norm_num)
theorem B16083683 : Blo 2117435 16083683 := bstep (se 1 (by rfl) ⟨12062762, by rfl⟩ : syracuseStep 16083683 = 24125525) B24125525
theorem B10722455 : Blo 2117435 10722455 := bstep (se 1 (by rfl) ⟨8041841, by rfl⟩ : syracuseStep 10722455 = 16083683) B16083683
theorem B7148303 : Blo 2117435 7148303 := bstep (se 1 (by rfl) ⟨5361227, by rfl⟩ : syracuseStep 7148303 = 10722455) B10722455
theorem B4765535 : Blo 2117435 4765535 := bstep (se 1 (by rfl) ⟨3574151, by rfl⟩ : syracuseStep 4765535 = 7148303) B7148303
theorem B3177023 : Blo 2117435 3177023 := bstep (se 1 (by rfl) ⟨2382767, by rfl⟩ : syracuseStep 3177023 = 4765535) B4765535
theorem B2118015 : Blo 2117435 2118015 := bstep (se 1 (by rfl) ⟨1588511, by rfl⟩ : syracuseStep 2118015 = 3177023) B3177023
theorem B3177029 : Blo 2117435 3177029 := bbase (se 4 (by rfl) ⟨297846, by rfl⟩ : syracuseStep 3177029 = 595693) (by norm_num)
theorem B2118019 : Blo 2117435 2118019 := bstep (se 1 (by rfl) ⟨1588514, by rfl⟩ : syracuseStep 2118019 = 3177029) B3177029
theorem B3574165 : Blo 2117435 3574165 := bbase (se 6 (by rfl) ⟨83769, by rfl⟩ : syracuseStep 3574165 = 167539) (by norm_num)
theorem B4765553 : Blo 2117435 4765553 := bstep (se 2 (by rfl) ⟨1787082, by rfl⟩ : syracuseStep 4765553 = 3574165) B3574165
theorem B3177035 : Blo 2117435 3177035 := bstep (se 1 (by rfl) ⟨2382776, by rfl⟩ : syracuseStep 3177035 = 4765553) B4765553
theorem B2118023 : Blo 2117435 2118023 := bstep (se 1 (by rfl) ⟨1588517, by rfl⟩ : syracuseStep 2118023 = 3177035) B3177035
theorem B2382781 : Blo 2117435 2382781 := bbase (se 3 (by rfl) ⟨446771, by rfl⟩ : syracuseStep 2382781 = 893543) (by norm_num)
theorem B3177041 : Blo 2117435 3177041 := bstep (se 2 (by rfl) ⟨1191390, by rfl⟩ : syracuseStep 3177041 = 2382781) B2382781
theorem B2118027 : Blo 2117435 2118027 := bstep (se 1 (by rfl) ⟨1588520, by rfl⟩ : syracuseStep 2118027 = 3177041) B3177041
theorem B7148357 : Blo 2117435 7148357 := bbase (se 4 (by rfl) ⟨670158, by rfl⟩ : syracuseStep 7148357 = 1340317) (by norm_num)
theorem B4765571 : Blo 2117435 4765571 := bstep (se 1 (by rfl) ⟨3574178, by rfl⟩ : syracuseStep 4765571 = 7148357) B7148357
theorem B3177047 : Blo 2117435 3177047 := bstep (se 1 (by rfl) ⟨2382785, by rfl⟩ : syracuseStep 3177047 = 4765571) B4765571
theorem B2118031 : Blo 2117435 2118031 := bstep (se 1 (by rfl) ⟨1588523, by rfl⟩ : syracuseStep 2118031 = 3177047) B3177047
theorem B3177053 : Blo 2117435 3177053 := bbase (se 3 (by rfl) ⟨595697, by rfl⟩ : syracuseStep 3177053 = 1191395) (by norm_num)
theorem B2118035 : Blo 2117435 2118035 := bstep (se 1 (by rfl) ⟨1588526, by rfl⟩ : syracuseStep 2118035 = 3177053) B3177053
theorem B4765589 : Blo 2117435 4765589 := bbase (se 6 (by rfl) ⟨111693, by rfl⟩ : syracuseStep 4765589 = 223387) (by norm_num)
theorem B3177059 : Blo 2117435 3177059 := bstep (se 1 (by rfl) ⟨2382794, by rfl⟩ : syracuseStep 3177059 = 4765589) B4765589
theorem B2118039 : Blo 2117435 2118039 := bstep (se 1 (by rfl) ⟨1588529, by rfl⟩ : syracuseStep 2118039 = 3177059) B3177059
theorem B4523597 : Blo 2117435 4523597 := bbase (se 3 (by rfl) ⟨848174, by rfl⟩ : syracuseStep 4523597 = 1696349) (by norm_num)
theorem B3015731 : Blo 2117435 3015731 := bstep (se 1 (by rfl) ⟨2261798, by rfl⟩ : syracuseStep 3015731 = 4523597) B4523597
theorem B8041949 : Blo 2117435 8041949 := bstep (se 3 (by rfl) ⟨1507865, by rfl⟩ : syracuseStep 8041949 = 3015731) B3015731
theorem B5361299 : Blo 2117435 5361299 := bstep (se 1 (by rfl) ⟨4020974, by rfl⟩ : syracuseStep 5361299 = 8041949) B8041949
theorem B3574199 : Blo 2117435 3574199 := bstep (se 1 (by rfl) ⟨2680649, by rfl⟩ : syracuseStep 3574199 = 5361299) B5361299
theorem B2382799 : Blo 2117435 2382799 := bstep (se 1 (by rfl) ⟨1787099, by rfl⟩ : syracuseStep 2382799 = 3574199) B3574199
theorem B3177065 : Blo 2117435 3177065 := bstep (se 2 (by rfl) ⟨1191399, by rfl⟩ : syracuseStep 3177065 = 2382799) B2382799
theorem B2118043 : Blo 2117435 2118043 := bstep (se 1 (by rfl) ⟨1588532, by rfl⟩ : syracuseStep 2118043 = 3177065) B3177065
theorem B7245941 : Blo 2117435 7245941 := bbase (se 5 (by rfl) ⟨339653, by rfl⟩ : syracuseStep 7245941 = 679307) (by norm_num)
theorem B77290037 : Blo 2117435 77290037 := bstep (se 5 (by rfl) ⟨3622970, by rfl⟩ : syracuseStep 77290037 = 7245941) B7245941
theorem B51526691 : Blo 2117435 51526691 := bstep (se 1 (by rfl) ⟨38645018, by rfl⟩ : syracuseStep 51526691 = 77290037) B77290037
theorem B34351127 : Blo 2117435 34351127 := bstep (se 1 (by rfl) ⟨25763345, by rfl⟩ : syracuseStep 34351127 = 51526691) B51526691
theorem B22900751 : Blo 2117435 22900751 := bstep (se 1 (by rfl) ⟨17175563, by rfl⟩ : syracuseStep 22900751 = 34351127) B34351127
theorem B15267167 : Blo 2117435 15267167 := bstep (se 1 (by rfl) ⟨11450375, by rfl⟩ : syracuseStep 15267167 = 22900751) B22900751
theorem B10178111 : Blo 2117435 10178111 := bstep (se 1 (by rfl) ⟨7633583, by rfl⟩ : syracuseStep 10178111 = 15267167) B15267167
theorem B6785407 : Blo 2117435 6785407 := bstep (se 1 (by rfl) ⟨5089055, by rfl⟩ : syracuseStep 6785407 = 10178111) B10178111
theorem B9047209 : Blo 2117435 9047209 := bstep (se 2 (by rfl) ⟨3392703, by rfl⟩ : syracuseStep 9047209 = 6785407) B6785407
theorem B12062945 : Blo 2117435 12062945 := bstep (se 2 (by rfl) ⟨4523604, by rfl⟩ : syracuseStep 12062945 = 9047209) B9047209
theorem B8041963 : Blo 2117435 8041963 := bstep (se 1 (by rfl) ⟨6031472, by rfl⟩ : syracuseStep 8041963 = 12062945) B12062945
theorem B10722617 : Blo 2117435 10722617 := bstep (se 2 (by rfl) ⟨4020981, by rfl⟩ : syracuseStep 10722617 = 8041963) B8041963
theorem B7148411 : Blo 2117435 7148411 := bstep (se 1 (by rfl) ⟨5361308, by rfl⟩ : syracuseStep 7148411 = 10722617) B10722617
theorem B4765607 : Blo 2117435 4765607 := bstep (se 1 (by rfl) ⟨3574205, by rfl⟩ : syracuseStep 4765607 = 7148411) B7148411
theorem B3177071 : Blo 2117435 3177071 := bstep (se 1 (by rfl) ⟨2382803, by rfl⟩ : syracuseStep 3177071 = 4765607) B4765607
theorem B2118047 : Blo 2117435 2118047 := bstep (se 1 (by rfl) ⟨1588535, by rfl⟩ : syracuseStep 2118047 = 3177071) B3177071
theorem B3177077 : Blo 2117435 3177077 := bbase (se 5 (by rfl) ⟨148925, by rfl⟩ : syracuseStep 3177077 = 297851) (by norm_num)
theorem B2118051 : Blo 2117435 2118051 := bstep (se 1 (by rfl) ⟨1588538, by rfl⟩ : syracuseStep 2118051 = 3177077) B3177077
theorem B4020997 : Blo 2117435 4020997 := bbase (se 4 (by rfl) ⟨376968, by rfl⟩ : syracuseStep 4020997 = 753937) (by norm_num)
theorem B5361329 : Blo 2117435 5361329 := bstep (se 2 (by rfl) ⟨2010498, by rfl⟩ : syracuseStep 5361329 = 4020997) B4020997
theorem B3574219 : Blo 2117435 3574219 := bstep (se 1 (by rfl) ⟨2680664, by rfl⟩ : syracuseStep 3574219 = 5361329) B5361329
theorem B4765625 : Blo 2117435 4765625 := bstep (se 2 (by rfl) ⟨1787109, by rfl⟩ : syracuseStep 4765625 = 3574219) B3574219
theorem B3177083 : Blo 2117435 3177083 := bstep (se 1 (by rfl) ⟨2382812, by rfl⟩ : syracuseStep 3177083 = 4765625) B4765625
theorem B2118055 : Blo 2117435 2118055 := bstep (se 1 (by rfl) ⟨1588541, by rfl⟩ : syracuseStep 2118055 = 3177083) B3177083
theorem B2382817 : Blo 2117435 2382817 := bbase (se 2 (by rfl) ⟨893556, by rfl⟩ : syracuseStep 2382817 = 1787113) (by norm_num)
theorem B3177089 : Blo 2117435 3177089 := bstep (se 2 (by rfl) ⟨1191408, by rfl⟩ : syracuseStep 3177089 = 2382817) B2382817
theorem B2118059 : Blo 2117435 2118059 := bstep (se 1 (by rfl) ⟨1588544, by rfl⟩ : syracuseStep 2118059 = 3177089) B3177089
theorem B5361349 : Blo 2117435 5361349 := bbase (se 4 (by rfl) ⟨502626, by rfl⟩ : syracuseStep 5361349 = 1005253) (by norm_num)
theorem B7148465 : Blo 2117435 7148465 := bstep (se 2 (by rfl) ⟨2680674, by rfl⟩ : syracuseStep 7148465 = 5361349) B5361349
theorem B4765643 : Blo 2117435 4765643 := bstep (se 1 (by rfl) ⟨3574232, by rfl⟩ : syracuseStep 4765643 = 7148465) B7148465
theorem B3177095 : Blo 2117435 3177095 := bstep (se 1 (by rfl) ⟨2382821, by rfl⟩ : syracuseStep 3177095 = 4765643) B4765643
theorem B2118063 : Blo 2117435 2118063 := bstep (se 1 (by rfl) ⟨1588547, by rfl⟩ : syracuseStep 2118063 = 3177095) B3177095
theorem B3177101 : Blo 2117435 3177101 := bbase (se 3 (by rfl) ⟨595706, by rfl⟩ : syracuseStep 3177101 = 1191413) (by norm_num)
theorem B2118067 : Blo 2117435 2118067 := bstep (se 1 (by rfl) ⟨1588550, by rfl⟩ : syracuseStep 2118067 = 3177101) B3177101
theorem B4765661 : Blo 2117435 4765661 := bbase (se 3 (by rfl) ⟨893561, by rfl⟩ : syracuseStep 4765661 = 1787123) (by norm_num)
theorem B3177107 : Blo 2117435 3177107 := bstep (se 1 (by rfl) ⟨2382830, by rfl⟩ : syracuseStep 3177107 = 4765661) B4765661
theorem B2118071 : Blo 2117435 2118071 := bstep (se 1 (by rfl) ⟨1588553, by rfl⟩ : syracuseStep 2118071 = 3177107) B3177107
theorem B3574253 : Blo 2117435 3574253 := bbase (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) (by norm_num)
theorem B2382835 : Blo 2117435 2382835 := bstep (se 1 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 2382835 = 3574253) B3574253
theorem B3177113 : Blo 2117435 3177113 := bstep (se 2 (by rfl) ⟨1191417, by rfl⟩ : syracuseStep 3177113 = 2382835) B2382835
theorem B2118075 : Blo 2117435 2118075 := bstep (se 1 (by rfl) ⟨1588556, by rfl⟩ : syracuseStep 2118075 = 3177113) B3177113
theorem B27142037 : Blo 2117435 27142037 := bbase (se 6 (by rfl) ⟨636141, by rfl⟩ : syracuseStep 27142037 = 1272283) (by norm_num)
theorem B18094691 : Blo 2117435 18094691 := bstep (se 1 (by rfl) ⟨13571018, by rfl⟩ : syracuseStep 18094691 = 27142037) B27142037
theorem B12063127 : Blo 2117435 12063127 := bstep (se 1 (by rfl) ⟨9047345, by rfl⟩ : syracuseStep 12063127 = 18094691) B18094691
theorem B16084169 : Blo 2117435 16084169 := bstep (se 2 (by rfl) ⟨6031563, by rfl⟩ : syracuseStep 16084169 = 12063127) B12063127
theorem B10722779 : Blo 2117435 10722779 := bstep (se 1 (by rfl) ⟨8042084, by rfl⟩ : syracuseStep 10722779 = 16084169) B16084169
theorem B7148519 : Blo 2117435 7148519 := bstep (se 1 (by rfl) ⟨5361389, by rfl⟩ : syracuseStep 7148519 = 10722779) B10722779
theorem B4765679 : Blo 2117435 4765679 := bstep (se 1 (by rfl) ⟨3574259, by rfl⟩ : syracuseStep 4765679 = 7148519) B7148519
theorem B3177119 : Blo 2117435 3177119 := bstep (se 1 (by rfl) ⟨2382839, by rfl⟩ : syracuseStep 3177119 = 4765679) B4765679
theorem B2118079 : Blo 2117435 2118079 := bstep (se 1 (by rfl) ⟨1588559, by rfl⟩ : syracuseStep 2118079 = 3177119) B3177119
theorem B3177125 : Blo 2117435 3177125 := bbase (se 4 (by rfl) ⟨297855, by rfl⟩ : syracuseStep 3177125 = 595711) (by norm_num)
theorem B2118083 : Blo 2117435 2118083 := bstep (se 1 (by rfl) ⟨1588562, by rfl⟩ : syracuseStep 2118083 = 3177125) B3177125
theorem B2680705 : Blo 2117435 2680705 := bbase (se 2 (by rfl) ⟨1005264, by rfl⟩ : syracuseStep 2680705 = 2010529) (by norm_num)
theorem B3574273 : Blo 2117435 3574273 := bstep (se 2 (by rfl) ⟨1340352, by rfl⟩ : syracuseStep 3574273 = 2680705) B2680705
theorem B4765697 : Blo 2117435 4765697 := bstep (se 2 (by rfl) ⟨1787136, by rfl⟩ : syracuseStep 4765697 = 3574273) B3574273
theorem B3177131 : Blo 2117435 3177131 := bstep (se 1 (by rfl) ⟨2382848, by rfl⟩ : syracuseStep 3177131 = 4765697) B4765697
theorem B2118087 : Blo 2117435 2118087 := bstep (se 1 (by rfl) ⟨1588565, by rfl⟩ : syracuseStep 2118087 = 3177131) B3177131
theorem B2382853 : Blo 2117435 2382853 := bbase (se 4 (by rfl) ⟨223392, by rfl⟩ : syracuseStep 2382853 = 446785) (by norm_num)
theorem B3177137 : Blo 2117435 3177137 := bstep (se 2 (by rfl) ⟨1191426, by rfl⟩ : syracuseStep 3177137 = 2382853) B2382853
theorem B2118091 : Blo 2117435 2118091 := bstep (se 1 (by rfl) ⟨1588568, by rfl⟩ : syracuseStep 2118091 = 3177137) B3177137
theorem B3015805 : Blo 2117435 3015805 := bbase (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) (by norm_num)
theorem B4021073 : Blo 2117435 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B2680715 : Blo 2117435 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B7148573 : Blo 2117435 7148573 := bstep (se 3 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 7148573 = 2680715) B2680715
theorem B4765715 : Blo 2117435 4765715 := bstep (se 1 (by rfl) ⟨3574286, by rfl⟩ : syracuseStep 4765715 = 7148573) B7148573
theorem B3177143 : Blo 2117435 3177143 := bstep (se 1 (by rfl) ⟨2382857, by rfl⟩ : syracuseStep 3177143 = 4765715) B4765715
theorem B2118095 : Blo 2117435 2118095 := bstep (se 1 (by rfl) ⟨1588571, by rfl⟩ : syracuseStep 2118095 = 3177143) B3177143
theorem B3177149 : Blo 2117435 3177149 := bbase (se 3 (by rfl) ⟨595715, by rfl⟩ : syracuseStep 3177149 = 1191431) (by norm_num)
theorem B2118099 : Blo 2117435 2118099 := bstep (se 1 (by rfl) ⟨1588574, by rfl⟩ : syracuseStep 2118099 = 3177149) B3177149
theorem B4765733 : Blo 2117435 4765733 := bbase (se 4 (by rfl) ⟨446787, by rfl⟩ : syracuseStep 4765733 = 893575) (by norm_num)
theorem B3177155 : Blo 2117435 3177155 := bstep (se 1 (by rfl) ⟨2382866, by rfl⟩ : syracuseStep 3177155 = 4765733) B4765733
theorem B2118103 : Blo 2117435 2118103 := bstep (se 1 (by rfl) ⟨1588577, by rfl⟩ : syracuseStep 2118103 = 3177155) B3177155
theorem B5361461 : Blo 2117435 5361461 := bbase (se 5 (by rfl) ⟨251318, by rfl⟩ : syracuseStep 5361461 = 502637) (by norm_num)
theorem B3574307 : Blo 2117435 3574307 := bstep (se 1 (by rfl) ⟨2680730, by rfl⟩ : syracuseStep 3574307 = 5361461) B5361461
theorem B2382871 : Blo 2117435 2382871 := bstep (se 1 (by rfl) ⟨1787153, by rfl⟩ : syracuseStep 2382871 = 3574307) B3574307
theorem B3177161 : Blo 2117435 3177161 := bstep (se 2 (by rfl) ⟨1191435, by rfl⟩ : syracuseStep 3177161 = 2382871) B2382871
theorem B2118107 : Blo 2117435 2118107 := bstep (se 1 (by rfl) ⟨1588580, by rfl⟩ : syracuseStep 2118107 = 3177161) B3177161
theorem B4294021 : Blo 2117435 4294021 := bbase (se 4 (by rfl) ⟨402564, by rfl⟩ : syracuseStep 4294021 = 805129) (by norm_num)
theorem B5725361 : Blo 2117435 5725361 := bstep (se 2 (by rfl) ⟨2147010, by rfl⟩ : syracuseStep 5725361 = 4294021) B4294021
theorem B15267629 : Blo 2117435 15267629 := bstep (se 3 (by rfl) ⟨2862680, by rfl⟩ : syracuseStep 15267629 = 5725361) B5725361
theorem B10178419 : Blo 2117435 10178419 := bstep (se 1 (by rfl) ⟨7633814, by rfl⟩ : syracuseStep 10178419 = 15267629) B15267629
theorem B13571225 : Blo 2117435 13571225 := bstep (se 2 (by rfl) ⟨5089209, by rfl⟩ : syracuseStep 13571225 = 10178419) B10178419
theorem B9047483 : Blo 2117435 9047483 := bstep (se 1 (by rfl) ⟨6785612, by rfl⟩ : syracuseStep 9047483 = 13571225) B13571225
theorem B6031655 : Blo 2117435 6031655 := bstep (se 1 (by rfl) ⟨4523741, by rfl⟩ : syracuseStep 6031655 = 9047483) B9047483
theorem B4021103 : Blo 2117435 4021103 := bstep (se 1 (by rfl) ⟨3015827, by rfl⟩ : syracuseStep 4021103 = 6031655) B6031655
theorem B10722941 : Blo 2117435 10722941 := bstep (se 3 (by rfl) ⟨2010551, by rfl⟩ : syracuseStep 10722941 = 4021103) B4021103
theorem B7148627 : Blo 2117435 7148627 := bstep (se 1 (by rfl) ⟨5361470, by rfl⟩ : syracuseStep 7148627 = 10722941) B10722941
theorem B4765751 : Blo 2117435 4765751 := bstep (se 1 (by rfl) ⟨3574313, by rfl⟩ : syracuseStep 4765751 = 7148627) B7148627
theorem B3177167 : Blo 2117435 3177167 := bstep (se 1 (by rfl) ⟨2382875, by rfl⟩ : syracuseStep 3177167 = 4765751) B4765751
theorem B2118111 : Blo 2117435 2118111 := bstep (se 1 (by rfl) ⟨1588583, by rfl⟩ : syracuseStep 2118111 = 3177167) B3177167
theorem B3177173 : Blo 2117435 3177173 := bbase (se 7 (by rfl) ⟨37232, by rfl⟩ : syracuseStep 3177173 = 74465) (by norm_num)
theorem B2118115 : Blo 2117435 2118115 := bstep (se 1 (by rfl) ⟨1588586, by rfl⟩ : syracuseStep 2118115 = 3177173) B3177173
theorem B2717321 : Blo 2117435 2717321 := bbase (se 2 (by rfl) ⟨1018995, by rfl⟩ : syracuseStep 2717321 = 2037991) (by norm_num)
theorem B7246189 : Blo 2117435 7246189 := bstep (se 3 (by rfl) ⟨1358660, by rfl⟩ : syracuseStep 7246189 = 2717321) B2717321
theorem B38646341 : Blo 2117435 38646341 := bstep (se 4 (by rfl) ⟨3623094, by rfl⟩ : syracuseStep 38646341 = 7246189) B7246189
theorem B25764227 : Blo 2117435 25764227 := bstep (se 1 (by rfl) ⟨19323170, by rfl⟩ : syracuseStep 25764227 = 38646341) B38646341
theorem B17176151 : Blo 2117435 17176151 := bstep (se 1 (by rfl) ⟨12882113, by rfl⟩ : syracuseStep 17176151 = 25764227) B25764227
theorem B11450767 : Blo 2117435 11450767 := bstep (se 1 (by rfl) ⟨8588075, by rfl⟩ : syracuseStep 11450767 = 17176151) B17176151
theorem B15267689 : Blo 2117435 15267689 := bstep (se 2 (by rfl) ⟨5725383, by rfl⟩ : syracuseStep 15267689 = 11450767) B11450767
theorem B10178459 : Blo 2117435 10178459 := bstep (se 1 (by rfl) ⟨7633844, by rfl⟩ : syracuseStep 10178459 = 15267689) B15267689
theorem B6785639 : Blo 2117435 6785639 := bstep (se 1 (by rfl) ⟨5089229, by rfl⟩ : syracuseStep 6785639 = 10178459) B10178459
theorem B4523759 : Blo 2117435 4523759 := bstep (se 1 (by rfl) ⟨3392819, by rfl⟩ : syracuseStep 4523759 = 6785639) B6785639
theorem B3015839 : Blo 2117435 3015839 := bstep (se 1 (by rfl) ⟨2261879, by rfl⟩ : syracuseStep 3015839 = 4523759) B4523759
theorem B8042237 : Blo 2117435 8042237 := bstep (se 3 (by rfl) ⟨1507919, by rfl⟩ : syracuseStep 8042237 = 3015839) B3015839
theorem B5361491 : Blo 2117435 5361491 := bstep (se 1 (by rfl) ⟨4021118, by rfl⟩ : syracuseStep 5361491 = 8042237) B8042237
theorem B3574327 : Blo 2117435 3574327 := bstep (se 1 (by rfl) ⟨2680745, by rfl⟩ : syracuseStep 3574327 = 5361491) B5361491
theorem B4765769 : Blo 2117435 4765769 := bstep (se 2 (by rfl) ⟨1787163, by rfl⟩ : syracuseStep 4765769 = 3574327) B3574327
theorem B3177179 : Blo 2117435 3177179 := bstep (se 1 (by rfl) ⟨2382884, by rfl⟩ : syracuseStep 3177179 = 4765769) B4765769
theorem B2118119 : Blo 2117435 2118119 := bstep (se 1 (by rfl) ⟨1588589, by rfl⟩ : syracuseStep 2118119 = 3177179) B3177179
theorem B2382889 : Blo 2117435 2382889 := bbase (se 2 (by rfl) ⟨893583, by rfl⟩ : syracuseStep 2382889 = 1787167) (by norm_num)
theorem B3177185 : Blo 2117435 3177185 := bstep (se 2 (by rfl) ⟨1191444, by rfl⟩ : syracuseStep 3177185 = 2382889) B2382889
theorem B2118123 : Blo 2117435 2118123 := bstep (se 1 (by rfl) ⟨1588592, by rfl⟩ : syracuseStep 2118123 = 3177185) B3177185
theorem B10317365 : Blo 2117435 10317365 := bbase (se 5 (by rfl) ⟨483626, by rfl⟩ : syracuseStep 10317365 = 967253) (by norm_num)
theorem B6878243 : Blo 2117435 6878243 := bstep (se 1 (by rfl) ⟨5158682, by rfl⟩ : syracuseStep 6878243 = 10317365) B10317365
theorem B18341981 : Blo 2117435 18341981 := bstep (se 3 (by rfl) ⟨3439121, by rfl⟩ : syracuseStep 18341981 = 6878243) B6878243
theorem B12227987 : Blo 2117435 12227987 := bstep (se 1 (by rfl) ⟨9170990, by rfl⟩ : syracuseStep 12227987 = 18341981) B18341981
theorem B32607965 : Blo 2117435 32607965 := bstep (se 3 (by rfl) ⟨6113993, by rfl⟩ : syracuseStep 32607965 = 12227987) B12227987
theorem B86954573 : Blo 2117435 86954573 := bstep (se 3 (by rfl) ⟨16303982, by rfl⟩ : syracuseStep 86954573 = 32607965) B32607965
theorem B231878861 : Blo 2117435 231878861 := bstep (se 3 (by rfl) ⟨43477286, by rfl⟩ : syracuseStep 231878861 = 86954573) B86954573
theorem B154585907 : Blo 2117435 154585907 := bstep (se 1 (by rfl) ⟨115939430, by rfl⟩ : syracuseStep 154585907 = 231878861) B231878861
theorem B103057271 : Blo 2117435 103057271 := bstep (se 1 (by rfl) ⟨77292953, by rfl⟩ : syracuseStep 103057271 = 154585907) B154585907
theorem B68704847 : Blo 2117435 68704847 := bstep (se 1 (by rfl) ⟨51528635, by rfl⟩ : syracuseStep 68704847 = 103057271) B103057271
theorem B45803231 : Blo 2117435 45803231 := bstep (se 1 (by rfl) ⟨34352423, by rfl⟩ : syracuseStep 45803231 = 68704847) B68704847
theorem B30535487 : Blo 2117435 30535487 := bstep (se 1 (by rfl) ⟨22901615, by rfl⟩ : syracuseStep 30535487 = 45803231) B45803231
theorem B20356991 : Blo 2117435 20356991 := bstep (se 1 (by rfl) ⟨15267743, by rfl⟩ : syracuseStep 20356991 = 30535487) B30535487
theorem B13571327 : Blo 2117435 13571327 := bstep (se 1 (by rfl) ⟨10178495, by rfl⟩ : syracuseStep 13571327 = 20356991) B20356991
theorem B9047551 : Blo 2117435 9047551 := bstep (se 1 (by rfl) ⟨6785663, by rfl⟩ : syracuseStep 9047551 = 13571327) B13571327
theorem B12063401 : Blo 2117435 12063401 := bstep (se 2 (by rfl) ⟨4523775, by rfl⟩ : syracuseStep 12063401 = 9047551) B9047551
theorem B8042267 : Blo 2117435 8042267 := bstep (se 1 (by rfl) ⟨6031700, by rfl⟩ : syracuseStep 8042267 = 12063401) B12063401
theorem B5361511 : Blo 2117435 5361511 := bstep (se 1 (by rfl) ⟨4021133, by rfl⟩ : syracuseStep 5361511 = 8042267) B8042267
theorem B7148681 : Blo 2117435 7148681 := bstep (se 2 (by rfl) ⟨2680755, by rfl⟩ : syracuseStep 7148681 = 5361511) B5361511
theorem B4765787 : Blo 2117435 4765787 := bstep (se 1 (by rfl) ⟨3574340, by rfl⟩ : syracuseStep 4765787 = 7148681) B7148681
theorem B3177191 : Blo 2117435 3177191 := bstep (se 1 (by rfl) ⟨2382893, by rfl⟩ : syracuseStep 3177191 = 4765787) B4765787
theorem B2118127 : Blo 2117435 2118127 := bstep (se 1 (by rfl) ⟨1588595, by rfl⟩ : syracuseStep 2118127 = 3177191) B3177191
theorem B3177197 : Blo 2117435 3177197 := bbase (se 3 (by rfl) ⟨595724, by rfl⟩ : syracuseStep 3177197 = 1191449) (by norm_num)
theorem B2118131 : Blo 2117435 2118131 := bstep (se 1 (by rfl) ⟨1588598, by rfl⟩ : syracuseStep 2118131 = 3177197) B3177197
theorem B4765805 : Blo 2117435 4765805 := bbase (se 3 (by rfl) ⟨893588, by rfl⟩ : syracuseStep 4765805 = 1787177) (by norm_num)
theorem B3177203 : Blo 2117435 3177203 := bstep (se 1 (by rfl) ⟨2382902, by rfl⟩ : syracuseStep 3177203 = 4765805) B4765805
theorem B2118135 : Blo 2117435 2118135 := bstep (se 1 (by rfl) ⟨1588601, by rfl⟩ : syracuseStep 2118135 = 3177203) B3177203
theorem B4021157 : Blo 2117435 4021157 := bbase (se 4 (by rfl) ⟨376983, by rfl⟩ : syracuseStep 4021157 = 753967) (by norm_num)
theorem B2680771 : Blo 2117435 2680771 := bstep (se 1 (by rfl) ⟨2010578, by rfl⟩ : syracuseStep 2680771 = 4021157) B4021157
theorem B3574361 : Blo 2117435 3574361 := bstep (se 2 (by rfl) ⟨1340385, by rfl⟩ : syracuseStep 3574361 = 2680771) B2680771
theorem B2382907 : Blo 2117435 2382907 := bstep (se 1 (by rfl) ⟨1787180, by rfl⟩ : syracuseStep 2382907 = 3574361) B3574361
theorem B3177209 : Blo 2117435 3177209 := bstep (se 2 (by rfl) ⟨1191453, by rfl⟩ : syracuseStep 3177209 = 2382907) B2382907
theorem B2118139 : Blo 2117435 2118139 := bstep (se 1 (by rfl) ⟨1588604, by rfl⟩ : syracuseStep 2118139 = 3177209) B3177209
theorem B4294085 : Blo 2117435 4294085 := bbase (se 4 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 4294085 = 805141) (by norm_num)
theorem B11450893 : Blo 2117435 11450893 := bstep (se 3 (by rfl) ⟨2147042, by rfl⟩ : syracuseStep 11450893 = 4294085) B4294085
theorem B15267857 : Blo 2117435 15267857 := bstep (se 2 (by rfl) ⟨5725446, by rfl⟩ : syracuseStep 15267857 = 11450893) B11450893
theorem B40714285 : Blo 2117435 40714285 := bstep (se 3 (by rfl) ⟨7633928, by rfl⟩ : syracuseStep 40714285 = 15267857) B15267857
theorem B54285713 : Blo 2117435 54285713 := bstep (se 2 (by rfl) ⟨20357142, by rfl⟩ : syracuseStep 54285713 = 40714285) B40714285
theorem B36190475 : Blo 2117435 36190475 := bstep (se 1 (by rfl) ⟨27142856, by rfl⟩ : syracuseStep 36190475 = 54285713) B54285713
theorem B24126983 : Blo 2117435 24126983 := bstep (se 1 (by rfl) ⟨18095237, by rfl⟩ : syracuseStep 24126983 = 36190475) B36190475
theorem B16084655 : Blo 2117435 16084655 := bstep (se 1 (by rfl) ⟨12063491, by rfl⟩ : syracuseStep 16084655 = 24126983) B24126983
theorem B10723103 : Blo 2117435 10723103 := bstep (se 1 (by rfl) ⟨8042327, by rfl⟩ : syracuseStep 10723103 = 16084655) B16084655
theorem B7148735 : Blo 2117435 7148735 := bstep (se 1 (by rfl) ⟨5361551, by rfl⟩ : syracuseStep 7148735 = 10723103) B10723103
theorem B4765823 : Blo 2117435 4765823 := bstep (se 1 (by rfl) ⟨3574367, by rfl⟩ : syracuseStep 4765823 = 7148735) B7148735
theorem B3177215 : Blo 2117435 3177215 := bstep (se 1 (by rfl) ⟨2382911, by rfl⟩ : syracuseStep 3177215 = 4765823) B4765823
theorem B2118143 : Blo 2117435 2118143 := bstep (se 1 (by rfl) ⟨1588607, by rfl⟩ : syracuseStep 2118143 = 3177215) B3177215
theorem B3177221 : Blo 2117435 3177221 := bbase (se 4 (by rfl) ⟨297864, by rfl⟩ : syracuseStep 3177221 = 595729) (by norm_num)
theorem B2118147 : Blo 2117435 2118147 := bstep (se 1 (by rfl) ⟨1588610, by rfl⟩ : syracuseStep 2118147 = 3177221) B3177221
theorem B3574381 : Blo 2117435 3574381 := bbase (se 3 (by rfl) ⟨670196, by rfl⟩ : syracuseStep 3574381 = 1340393) (by norm_num)
theorem B4765841 : Blo 2117435 4765841 := bstep (se 2 (by rfl) ⟨1787190, by rfl⟩ : syracuseStep 4765841 = 3574381) B3574381
theorem B3177227 : Blo 2117435 3177227 := bstep (se 1 (by rfl) ⟨2382920, by rfl⟩ : syracuseStep 3177227 = 4765841) B4765841
theorem B2118151 : Blo 2117435 2118151 := bstep (se 1 (by rfl) ⟨1588613, by rfl⟩ : syracuseStep 2118151 = 3177227) B3177227
theorem B2382925 : Blo 2117435 2382925 := bbase (se 3 (by rfl) ⟨446798, by rfl⟩ : syracuseStep 2382925 = 893597) (by norm_num)
theorem B3177233 : Blo 2117435 3177233 := bstep (se 2 (by rfl) ⟨1191462, by rfl⟩ : syracuseStep 3177233 = 2382925) B2382925
theorem B2118155 : Blo 2117435 2118155 := bstep (se 1 (by rfl) ⟨1588616, by rfl⟩ : syracuseStep 2118155 = 3177233) B3177233
theorem B7148789 : Blo 2117435 7148789 := bbase (se 5 (by rfl) ⟨335099, by rfl⟩ : syracuseStep 7148789 = 670199) (by norm_num)
theorem B4765859 : Blo 2117435 4765859 := bstep (se 1 (by rfl) ⟨3574394, by rfl⟩ : syracuseStep 4765859 = 7148789) B7148789
theorem B3177239 : Blo 2117435 3177239 := bstep (se 1 (by rfl) ⟨2382929, by rfl⟩ : syracuseStep 3177239 = 4765859) B4765859
theorem B2118159 : Blo 2117435 2118159 := bstep (se 1 (by rfl) ⟨1588619, by rfl⟩ : syracuseStep 2118159 = 3177239) B3177239
theorem B3177245 : Blo 2117435 3177245 := bbase (se 3 (by rfl) ⟨595733, by rfl⟩ : syracuseStep 3177245 = 1191467) (by norm_num)
theorem B2118163 : Blo 2117435 2118163 := bstep (se 1 (by rfl) ⟨1588622, by rfl⟩ : syracuseStep 2118163 = 3177245) B3177245
theorem B4765877 : Blo 2117435 4765877 := bbase (se 5 (by rfl) ⟨223400, by rfl⟩ : syracuseStep 4765877 = 446801) (by norm_num)
theorem B3177251 : Blo 2117435 3177251 := bstep (se 1 (by rfl) ⟨2382938, by rfl⟩ : syracuseStep 3177251 = 4765877) B4765877
theorem B2118167 : Blo 2117435 2118167 := bstep (se 1 (by rfl) ⟨1588625, by rfl⟩ : syracuseStep 2118167 = 3177251) B3177251
theorem B5725525 : Blo 2117435 5725525 := bbase (se 11 (by rfl) ⟨4193, by rfl⟩ : syracuseStep 5725525 = 8387) (by norm_num)
theorem B7634033 : Blo 2117435 7634033 := bstep (se 2 (by rfl) ⟨2862762, by rfl⟩ : syracuseStep 7634033 = 5725525) B5725525
theorem B5089355 : Blo 2117435 5089355 := bstep (se 1 (by rfl) ⟨3817016, by rfl⟩ : syracuseStep 5089355 = 7634033) B7634033
theorem B3392903 : Blo 2117435 3392903 := bstep (se 1 (by rfl) ⟨2544677, by rfl⟩ : syracuseStep 3392903 = 5089355) B5089355
theorem B2261935 : Blo 2117435 2261935 := bstep (se 1 (by rfl) ⟨1696451, by rfl⟩ : syracuseStep 2261935 = 3392903) B3392903
theorem B12063653 : Blo 2117435 12063653 := bstep (se 4 (by rfl) ⟨1130967, by rfl⟩ : syracuseStep 12063653 = 2261935) B2261935
theorem B8042435 : Blo 2117435 8042435 := bstep (se 1 (by rfl) ⟨6031826, by rfl⟩ : syracuseStep 8042435 = 12063653) B12063653
theorem B5361623 : Blo 2117435 5361623 := bstep (se 1 (by rfl) ⟨4021217, by rfl⟩ : syracuseStep 5361623 = 8042435) B8042435
theorem B3574415 : Blo 2117435 3574415 := bstep (se 1 (by rfl) ⟨2680811, by rfl⟩ : syracuseStep 3574415 = 5361623) B5361623
theorem B2382943 : Blo 2117435 2382943 := bstep (se 1 (by rfl) ⟨1787207, by rfl⟩ : syracuseStep 2382943 = 3574415) B3574415
theorem B3177257 : Blo 2117435 3177257 := bstep (se 2 (by rfl) ⟨1191471, by rfl⟩ : syracuseStep 3177257 = 2382943) B2382943
theorem B2118171 : Blo 2117435 2118171 := bstep (se 1 (by rfl) ⟨1588628, by rfl⟩ : syracuseStep 2118171 = 3177257) B3177257
theorem B3392909 : Blo 2117435 3392909 := bbase (se 3 (by rfl) ⟨636170, by rfl⟩ : syracuseStep 3392909 = 1272341) (by norm_num)
theorem B2261939 : Blo 2117435 2261939 := bstep (se 1 (by rfl) ⟨1696454, by rfl⟩ : syracuseStep 2261939 = 3392909) B3392909
theorem B6031837 : Blo 2117435 6031837 := bstep (se 3 (by rfl) ⟨1130969, by rfl⟩ : syracuseStep 6031837 = 2261939) B2261939
theorem B8042449 : Blo 2117435 8042449 := bstep (se 2 (by rfl) ⟨3015918, by rfl⟩ : syracuseStep 8042449 = 6031837) B6031837
theorem B10723265 : Blo 2117435 10723265 := bstep (se 2 (by rfl) ⟨4021224, by rfl⟩ : syracuseStep 10723265 = 8042449) B8042449
theorem B7148843 : Blo 2117435 7148843 := bstep (se 1 (by rfl) ⟨5361632, by rfl⟩ : syracuseStep 7148843 = 10723265) B10723265
theorem B4765895 : Blo 2117435 4765895 := bstep (se 1 (by rfl) ⟨3574421, by rfl⟩ : syracuseStep 4765895 = 7148843) B7148843
theorem B3177263 : Blo 2117435 3177263 := bstep (se 1 (by rfl) ⟨2382947, by rfl⟩ : syracuseStep 3177263 = 4765895) B4765895
theorem B2118175 : Blo 2117435 2118175 := bstep (se 1 (by rfl) ⟨1588631, by rfl⟩ : syracuseStep 2118175 = 3177263) B3177263
theorem B3177269 : Blo 2117435 3177269 := bbase (se 5 (by rfl) ⟨148934, by rfl⟩ : syracuseStep 3177269 = 297869) (by norm_num)
theorem B2118179 : Blo 2117435 2118179 := bstep (se 1 (by rfl) ⟨1588634, by rfl⟩ : syracuseStep 2118179 = 3177269) B3177269
theorem B5361653 : Blo 2117435 5361653 := bbase (se 5 (by rfl) ⟨251327, by rfl⟩ : syracuseStep 5361653 = 502655) (by norm_num)
theorem B3574435 : Blo 2117435 3574435 := bstep (se 1 (by rfl) ⟨2680826, by rfl⟩ : syracuseStep 3574435 = 5361653) B5361653
theorem B4765913 : Blo 2117435 4765913 := bstep (se 2 (by rfl) ⟨1787217, by rfl⟩ : syracuseStep 4765913 = 3574435) B3574435
theorem B3177275 : Blo 2117435 3177275 := bstep (se 1 (by rfl) ⟨2382956, by rfl⟩ : syracuseStep 3177275 = 4765913) B4765913
theorem B2118183 : Blo 2117435 2118183 := bstep (se 1 (by rfl) ⟨1588637, by rfl⟩ : syracuseStep 2118183 = 3177275) B3177275
theorem B2382961 : Blo 2117435 2382961 := bbase (se 2 (by rfl) ⟨893610, by rfl⟩ : syracuseStep 2382961 = 1787221) (by norm_num)
theorem B3177281 : Blo 2117435 3177281 := bstep (se 2 (by rfl) ⟨1191480, by rfl⟩ : syracuseStep 3177281 = 2382961) B2382961
theorem B2118187 : Blo 2117435 2118187 := bstep (se 1 (by rfl) ⟨1588640, by rfl⟩ : syracuseStep 2118187 = 3177281) B3177281
theorem B2544701 : Blo 2117435 2544701 := bbase (se 3 (by rfl) ⟨477131, by rfl⟩ : syracuseStep 2544701 = 954263) (by norm_num)
theorem B6785869 : Blo 2117435 6785869 := bstep (se 3 (by rfl) ⟨1272350, by rfl⟩ : syracuseStep 6785869 = 2544701) B2544701
theorem B9047825 : Blo 2117435 9047825 := bstep (se 2 (by rfl) ⟨3392934, by rfl⟩ : syracuseStep 9047825 = 6785869) B6785869
theorem B6031883 : Blo 2117435 6031883 := bstep (se 1 (by rfl) ⟨4523912, by rfl⟩ : syracuseStep 6031883 = 9047825) B9047825
theorem B4021255 : Blo 2117435 4021255 := bstep (se 1 (by rfl) ⟨3015941, by rfl⟩ : syracuseStep 4021255 = 6031883) B6031883
theorem B5361673 : Blo 2117435 5361673 := bstep (se 2 (by rfl) ⟨2010627, by rfl⟩ : syracuseStep 5361673 = 4021255) B4021255
theorem B7148897 : Blo 2117435 7148897 := bstep (se 2 (by rfl) ⟨2680836, by rfl⟩ : syracuseStep 7148897 = 5361673) B5361673
theorem B4765931 : Blo 2117435 4765931 := bstep (se 1 (by rfl) ⟨3574448, by rfl⟩ : syracuseStep 4765931 = 7148897) B7148897
theorem B3177287 : Blo 2117435 3177287 := bstep (se 1 (by rfl) ⟨2382965, by rfl⟩ : syracuseStep 3177287 = 4765931) B4765931
theorem B2118191 : Blo 2117435 2118191 := bstep (se 1 (by rfl) ⟨1588643, by rfl⟩ : syracuseStep 2118191 = 3177287) B3177287
theorem B3177293 : Blo 2117435 3177293 := bbase (se 3 (by rfl) ⟨595742, by rfl⟩ : syracuseStep 3177293 = 1191485) (by norm_num)
theorem B2118195 : Blo 2117435 2118195 := bstep (se 1 (by rfl) ⟨1588646, by rfl⟩ : syracuseStep 2118195 = 3177293) B3177293
theorem B4765949 : Blo 2117435 4765949 := bbase (se 3 (by rfl) ⟨893615, by rfl⟩ : syracuseStep 4765949 = 1787231) (by norm_num)
theorem B3177299 : Blo 2117435 3177299 := bstep (se 1 (by rfl) ⟨2382974, by rfl⟩ : syracuseStep 3177299 = 4765949) B4765949
theorem B2118199 : Blo 2117435 2118199 := bstep (se 1 (by rfl) ⟨1588649, by rfl⟩ : syracuseStep 2118199 = 3177299) B3177299
theorem B3574469 : Blo 2117435 3574469 := bbase (se 4 (by rfl) ⟨335106, by rfl⟩ : syracuseStep 3574469 = 670213) (by norm_num)
theorem B2382979 : Blo 2117435 2382979 := bstep (se 1 (by rfl) ⟨1787234, by rfl⟩ : syracuseStep 2382979 = 3574469) B3574469
theorem B3177305 : Blo 2117435 3177305 := bstep (se 2 (by rfl) ⟨1191489, by rfl⟩ : syracuseStep 3177305 = 2382979) B2382979
theorem B2118203 : Blo 2117435 2118203 := bstep (se 1 (by rfl) ⟨1588652, by rfl⟩ : syracuseStep 2118203 = 3177305) B3177305
theorem B16085141 : Blo 2117435 16085141 := bbase (se 6 (by rfl) ⟨376995, by rfl⟩ : syracuseStep 16085141 = 753991) (by norm_num)
theorem B10723427 : Blo 2117435 10723427 := bstep (se 1 (by rfl) ⟨8042570, by rfl⟩ : syracuseStep 10723427 = 16085141) B16085141
theorem B7148951 : Blo 2117435 7148951 := bstep (se 1 (by rfl) ⟨5361713, by rfl⟩ : syracuseStep 7148951 = 10723427) B10723427
theorem B4765967 : Blo 2117435 4765967 := bstep (se 1 (by rfl) ⟨3574475, by rfl⟩ : syracuseStep 4765967 = 7148951) B7148951
theorem B3177311 : Blo 2117435 3177311 := bstep (se 1 (by rfl) ⟨2382983, by rfl⟩ : syracuseStep 3177311 = 4765967) B4765967
theorem B2118207 : Blo 2117435 2118207 := bstep (se 1 (by rfl) ⟨1588655, by rfl⟩ : syracuseStep 2118207 = 3177311) B3177311
theorem B3177317 : Blo 2117435 3177317 := bbase (se 4 (by rfl) ⟨297873, by rfl⟩ : syracuseStep 3177317 = 595747) (by norm_num)
theorem B2118211 : Blo 2117435 2118211 := bstep (se 1 (by rfl) ⟨1588658, by rfl⟩ : syracuseStep 2118211 = 3177317) B3177317
theorem B4021301 : Blo 2117435 4021301 := bbase (se 5 (by rfl) ⟨188498, by rfl⟩ : syracuseStep 4021301 = 376997) (by norm_num)
theorem B2680867 : Blo 2117435 2680867 := bstep (se 1 (by rfl) ⟨2010650, by rfl⟩ : syracuseStep 2680867 = 4021301) B4021301
theorem B3574489 : Blo 2117435 3574489 := bstep (se 2 (by rfl) ⟨1340433, by rfl⟩ : syracuseStep 3574489 = 2680867) B2680867
theorem B4765985 : Blo 2117435 4765985 := bstep (se 2 (by rfl) ⟨1787244, by rfl⟩ : syracuseStep 4765985 = 3574489) B3574489
theorem B3177323 : Blo 2117435 3177323 := bstep (se 1 (by rfl) ⟨2382992, by rfl⟩ : syracuseStep 3177323 = 4765985) B4765985
theorem B2118215 : Blo 2117435 2118215 := bstep (se 1 (by rfl) ⟨1588661, by rfl⟩ : syracuseStep 2118215 = 3177323) B3177323
theorem B2382997 : Blo 2117435 2382997 := bbase (se 6 (by rfl) ⟨55851, by rfl⟩ : syracuseStep 2382997 = 111703) (by norm_num)
theorem B3177329 : Blo 2117435 3177329 := bstep (se 2 (by rfl) ⟨1191498, by rfl⟩ : syracuseStep 3177329 = 2382997) B2382997
theorem B2118219 : Blo 2117435 2118219 := bstep (se 1 (by rfl) ⟨1588664, by rfl⟩ : syracuseStep 2118219 = 3177329) B3177329
theorem B2680877 : Blo 2117435 2680877 := bbase (se 3 (by rfl) ⟨502664, by rfl⟩ : syracuseStep 2680877 = 1005329) (by norm_num)
theorem B7149005 : Blo 2117435 7149005 := bstep (se 3 (by rfl) ⟨1340438, by rfl⟩ : syracuseStep 7149005 = 2680877) B2680877
theorem B4766003 : Blo 2117435 4766003 := bstep (se 1 (by rfl) ⟨3574502, by rfl⟩ : syracuseStep 4766003 = 7149005) B7149005
theorem B3177335 : Blo 2117435 3177335 := bstep (se 1 (by rfl) ⟨2383001, by rfl⟩ : syracuseStep 3177335 = 4766003) B4766003
theorem B2118223 : Blo 2117435 2118223 := bstep (se 1 (by rfl) ⟨1588667, by rfl⟩ : syracuseStep 2118223 = 3177335) B3177335
theorem B3177341 : Blo 2117435 3177341 := bbase (se 3 (by rfl) ⟨595751, by rfl⟩ : syracuseStep 3177341 = 1191503) (by norm_num)
theorem B2118227 : Blo 2117435 2118227 := bstep (se 1 (by rfl) ⟨1588670, by rfl⟩ : syracuseStep 2118227 = 3177341) B3177341
theorem B4766021 : Blo 2117435 4766021 := bbase (se 4 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 4766021 = 893629) (by norm_num)
theorem B3177347 : Blo 2117435 3177347 := bstep (se 1 (by rfl) ⟨2383010, by rfl⟩ : syracuseStep 3177347 = 4766021) B4766021
theorem B2118231 : Blo 2117435 2118231 := bstep (se 1 (by rfl) ⟨1588673, by rfl⟩ : syracuseStep 2118231 = 3177347) B3177347
theorem B2415529 : Blo 2117435 2415529 := bbase (se 2 (by rfl) ⟨905823, by rfl⟩ : syracuseStep 2415529 = 1811647) (by norm_num)
theorem B3220705 : Blo 2117435 3220705 := bstep (se 2 (by rfl) ⟨1207764, by rfl⟩ : syracuseStep 3220705 = 2415529) B2415529
theorem B17177093 : Blo 2117435 17177093 := bstep (se 4 (by rfl) ⟨1610352, by rfl⟩ : syracuseStep 17177093 = 3220705) B3220705
theorem B11451395 : Blo 2117435 11451395 := bstep (se 1 (by rfl) ⟨8588546, by rfl⟩ : syracuseStep 11451395 = 17177093) B17177093
theorem B7634263 : Blo 2117435 7634263 := bstep (se 1 (by rfl) ⟨5725697, by rfl⟩ : syracuseStep 7634263 = 11451395) B11451395
theorem B10179017 : Blo 2117435 10179017 := bstep (se 2 (by rfl) ⟨3817131, by rfl⟩ : syracuseStep 10179017 = 7634263) B7634263
theorem B6786011 : Blo 2117435 6786011 := bstep (se 1 (by rfl) ⟨5089508, by rfl⟩ : syracuseStep 6786011 = 10179017) B10179017
theorem B4524007 : Blo 2117435 4524007 := bstep (se 1 (by rfl) ⟨3393005, by rfl⟩ : syracuseStep 4524007 = 6786011) B6786011
theorem B6032009 : Blo 2117435 6032009 := bstep (se 2 (by rfl) ⟨2262003, by rfl⟩ : syracuseStep 6032009 = 4524007) B4524007
theorem B4021339 : Blo 2117435 4021339 := bstep (se 1 (by rfl) ⟨3016004, by rfl⟩ : syracuseStep 4021339 = 6032009) B6032009
theorem B5361785 : Blo 2117435 5361785 := bstep (se 2 (by rfl) ⟨2010669, by rfl⟩ : syracuseStep 5361785 = 4021339) B4021339
theorem B3574523 : Blo 2117435 3574523 := bstep (se 1 (by rfl) ⟨2680892, by rfl⟩ : syracuseStep 3574523 = 5361785) B5361785
theorem B2383015 : Blo 2117435 2383015 := bstep (se 1 (by rfl) ⟨1787261, by rfl⟩ : syracuseStep 2383015 = 3574523) B3574523
theorem B3177353 : Blo 2117435 3177353 := bstep (se 2 (by rfl) ⟨1191507, by rfl⟩ : syracuseStep 3177353 = 2383015) B2383015
theorem B2118235 : Blo 2117435 2118235 := bstep (se 1 (by rfl) ⟨1588676, by rfl⟩ : syracuseStep 2118235 = 3177353) B3177353
theorem B10723589 : Blo 2117435 10723589 := bbase (se 4 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 10723589 = 2010673) (by norm_num)
theorem B7149059 : Blo 2117435 7149059 := bstep (se 1 (by rfl) ⟨5361794, by rfl⟩ : syracuseStep 7149059 = 10723589) B10723589
theorem B4766039 : Blo 2117435 4766039 := bstep (se 1 (by rfl) ⟨3574529, by rfl⟩ : syracuseStep 4766039 = 7149059) B7149059
theorem B3177359 : Blo 2117435 3177359 := bstep (se 1 (by rfl) ⟨2383019, by rfl⟩ : syracuseStep 3177359 = 4766039) B4766039
theorem B2118239 : Blo 2117435 2118239 := bstep (se 1 (by rfl) ⟨1588679, by rfl⟩ : syracuseStep 2118239 = 3177359) B3177359
theorem B3177365 : Blo 2117435 3177365 := bbase (se 6 (by rfl) ⟨74469, by rfl⟩ : syracuseStep 3177365 = 148939) (by norm_num)
theorem B2118243 : Blo 2117435 2118243 := bstep (se 1 (by rfl) ⟨1588682, by rfl⟩ : syracuseStep 2118243 = 3177365) B3177365
theorem B12064085 : Blo 2117435 12064085 := bbase (se 14 (by rfl) ⟨1104, by rfl⟩ : syracuseStep 12064085 = 2209) (by norm_num)
theorem B8042723 : Blo 2117435 8042723 := bstep (se 1 (by rfl) ⟨6032042, by rfl⟩ : syracuseStep 8042723 = 12064085) B12064085
theorem B5361815 : Blo 2117435 5361815 := bstep (se 1 (by rfl) ⟨4021361, by rfl⟩ : syracuseStep 5361815 = 8042723) B8042723
theorem B3574543 : Blo 2117435 3574543 := bstep (se 1 (by rfl) ⟨2680907, by rfl⟩ : syracuseStep 3574543 = 5361815) B5361815
theorem B4766057 : Blo 2117435 4766057 := bstep (se 2 (by rfl) ⟨1787271, by rfl⟩ : syracuseStep 4766057 = 3574543) B3574543
theorem B3177371 : Blo 2117435 3177371 := bstep (se 1 (by rfl) ⟨2383028, by rfl⟩ : syracuseStep 3177371 = 4766057) B4766057
theorem B2118247 : Blo 2117435 2118247 := bstep (se 1 (by rfl) ⟨1588685, by rfl⟩ : syracuseStep 2118247 = 3177371) B3177371
theorem B2383033 : Blo 2117435 2383033 := bbase (se 2 (by rfl) ⟨893637, by rfl⟩ : syracuseStep 2383033 = 1787275) (by norm_num)
theorem B3177377 : Blo 2117435 3177377 := bstep (se 2 (by rfl) ⟨1191516, by rfl⟩ : syracuseStep 3177377 = 2383033) B2383033
theorem B2118251 : Blo 2117435 2118251 := bstep (se 1 (by rfl) ⟨1588688, by rfl⟩ : syracuseStep 2118251 = 3177377) B3177377
theorem B3393037 : Blo 2117435 3393037 := bbase (se 3 (by rfl) ⟨636194, by rfl⟩ : syracuseStep 3393037 = 1272389) (by norm_num)
theorem B4524049 : Blo 2117435 4524049 := bstep (se 2 (by rfl) ⟨1696518, by rfl⟩ : syracuseStep 4524049 = 3393037) B3393037
theorem B6032065 : Blo 2117435 6032065 := bstep (se 2 (by rfl) ⟨2262024, by rfl⟩ : syracuseStep 6032065 = 4524049) B4524049
theorem B8042753 : Blo 2117435 8042753 := bstep (se 2 (by rfl) ⟨3016032, by rfl⟩ : syracuseStep 8042753 = 6032065) B6032065
theorem B5361835 : Blo 2117435 5361835 := bstep (se 1 (by rfl) ⟨4021376, by rfl⟩ : syracuseStep 5361835 = 8042753) B8042753
theorem B7149113 : Blo 2117435 7149113 := bstep (se 2 (by rfl) ⟨2680917, by rfl⟩ : syracuseStep 7149113 = 5361835) B5361835
theorem B4766075 : Blo 2117435 4766075 := bstep (se 1 (by rfl) ⟨3574556, by rfl⟩ : syracuseStep 4766075 = 7149113) B7149113
theorem B3177383 : Blo 2117435 3177383 := bstep (se 1 (by rfl) ⟨2383037, by rfl⟩ : syracuseStep 3177383 = 4766075) B4766075
theorem B2118255 : Blo 2117435 2118255 := bstep (se 1 (by rfl) ⟨1588691, by rfl⟩ : syracuseStep 2118255 = 3177383) B3177383
theorem B3177389 : Blo 2117435 3177389 := bbase (se 3 (by rfl) ⟨595760, by rfl⟩ : syracuseStep 3177389 = 1191521) (by norm_num)
theorem B2118259 : Blo 2117435 2118259 := bstep (se 1 (by rfl) ⟨1588694, by rfl⟩ : syracuseStep 2118259 = 3177389) B3177389
theorem B4766093 : Blo 2117435 4766093 := bbase (se 3 (by rfl) ⟨893642, by rfl⟩ : syracuseStep 4766093 = 1787285) (by norm_num)
theorem B3177395 : Blo 2117435 3177395 := bstep (se 1 (by rfl) ⟨2383046, by rfl⟩ : syracuseStep 3177395 = 4766093) B4766093
theorem B2118263 : Blo 2117435 2118263 := bstep (se 1 (by rfl) ⟨1588697, by rfl⟩ : syracuseStep 2118263 = 3177395) B3177395
theorem B2680933 : Blo 2117435 2680933 := bbase (se 4 (by rfl) ⟨251337, by rfl⟩ : syracuseStep 2680933 = 502675) (by norm_num)
theorem B3574577 : Blo 2117435 3574577 := bstep (se 2 (by rfl) ⟨1340466, by rfl⟩ : syracuseStep 3574577 = 2680933) B2680933
theorem B2383051 : Blo 2117435 2383051 := bstep (se 1 (by rfl) ⟨1787288, by rfl⟩ : syracuseStep 2383051 = 3574577) B3574577
theorem B3177401 : Blo 2117435 3177401 := bstep (se 2 (by rfl) ⟨1191525, by rfl⟩ : syracuseStep 3177401 = 2383051) B2383051
theorem B2118267 : Blo 2117435 2118267 := bstep (se 1 (by rfl) ⟨1588700, by rfl⟩ : syracuseStep 2118267 = 3177401) B3177401
theorem B7246709 : Blo 2117435 7246709 := bbase (se 5 (by rfl) ⟨339689, by rfl⟩ : syracuseStep 7246709 = 679379) (by norm_num)
theorem B4831139 : Blo 2117435 4831139 := bstep (se 1 (by rfl) ⟨3623354, by rfl⟩ : syracuseStep 4831139 = 7246709) B7246709
theorem B3220759 : Blo 2117435 3220759 := bstep (se 1 (by rfl) ⟨2415569, by rfl⟩ : syracuseStep 3220759 = 4831139) B4831139
theorem B4294345 : Blo 2117435 4294345 := bstep (se 2 (by rfl) ⟨1610379, by rfl⟩ : syracuseStep 4294345 = 3220759) B3220759
theorem B5725793 : Blo 2117435 5725793 := bstep (se 2 (by rfl) ⟨2147172, by rfl⟩ : syracuseStep 5725793 = 4294345) B4294345
theorem B3817195 : Blo 2117435 3817195 := bstep (se 1 (by rfl) ⟨2862896, by rfl⟩ : syracuseStep 3817195 = 5725793) B5725793
theorem B20358373 : Blo 2117435 20358373 := bstep (se 4 (by rfl) ⟨1908597, by rfl⟩ : syracuseStep 20358373 = 3817195) B3817195
theorem B27144497 : Blo 2117435 27144497 := bstep (se 2 (by rfl) ⟨10179186, by rfl⟩ : syracuseStep 27144497 = 20358373) B20358373
theorem B18096331 : Blo 2117435 18096331 := bstep (se 1 (by rfl) ⟨13572248, by rfl⟩ : syracuseStep 18096331 = 27144497) B27144497
theorem B24128441 : Blo 2117435 24128441 := bstep (se 2 (by rfl) ⟨9048165, by rfl⟩ : syracuseStep 24128441 = 18096331) B18096331
theorem B16085627 : Blo 2117435 16085627 := bstep (se 1 (by rfl) ⟨12064220, by rfl⟩ : syracuseStep 16085627 = 24128441) B24128441
theorem B10723751 : Blo 2117435 10723751 := bstep (se 1 (by rfl) ⟨8042813, by rfl⟩ : syracuseStep 10723751 = 16085627) B16085627
theorem B7149167 : Blo 2117435 7149167 := bstep (se 1 (by rfl) ⟨5361875, by rfl⟩ : syracuseStep 7149167 = 10723751) B10723751
theorem B4766111 : Blo 2117435 4766111 := bstep (se 1 (by rfl) ⟨3574583, by rfl⟩ : syracuseStep 4766111 = 7149167) B7149167
theorem B3177407 : Blo 2117435 3177407 := bstep (se 1 (by rfl) ⟨2383055, by rfl⟩ : syracuseStep 3177407 = 4766111) B4766111
theorem B2118271 : Blo 2117435 2118271 := bstep (se 1 (by rfl) ⟨1588703, by rfl⟩ : syracuseStep 2118271 = 3177407) B3177407
theorem B3177413 : Blo 2117435 3177413 := bbase (se 4 (by rfl) ⟨297882, by rfl⟩ : syracuseStep 3177413 = 595765) (by norm_num)
theorem B2118275 : Blo 2117435 2118275 := bstep (se 1 (by rfl) ⟨1588706, by rfl⟩ : syracuseStep 2118275 = 3177413) B3177413
theorem B3574597 : Blo 2117435 3574597 := bbase (se 4 (by rfl) ⟨335118, by rfl⟩ : syracuseStep 3574597 = 670237) (by norm_num)
theorem B4766129 : Blo 2117435 4766129 := bstep (se 2 (by rfl) ⟨1787298, by rfl⟩ : syracuseStep 4766129 = 3574597) B3574597
theorem B3177419 : Blo 2117435 3177419 := bstep (se 1 (by rfl) ⟨2383064, by rfl⟩ : syracuseStep 3177419 = 4766129) B4766129
theorem B2118279 : Blo 2117435 2118279 := bstep (se 1 (by rfl) ⟨1588709, by rfl⟩ : syracuseStep 2118279 = 3177419) B3177419
theorem B2383069 : Blo 2117435 2383069 := bbase (se 3 (by rfl) ⟨446825, by rfl⟩ : syracuseStep 2383069 = 893651) (by norm_num)
theorem B3177425 : Blo 2117435 3177425 := bstep (se 2 (by rfl) ⟨1191534, by rfl⟩ : syracuseStep 3177425 = 2383069) B2383069
theorem B2118283 : Blo 2117435 2118283 := bstep (se 1 (by rfl) ⟨1588712, by rfl⟩ : syracuseStep 2118283 = 3177425) B3177425
theorem B7149221 : Blo 2117435 7149221 := bbase (se 4 (by rfl) ⟨670239, by rfl⟩ : syracuseStep 7149221 = 1340479) (by norm_num)
theorem B4766147 : Blo 2117435 4766147 := bstep (se 1 (by rfl) ⟨3574610, by rfl⟩ : syracuseStep 4766147 = 7149221) B7149221
theorem B3177431 : Blo 2117435 3177431 := bstep (se 1 (by rfl) ⟨2383073, by rfl⟩ : syracuseStep 3177431 = 4766147) B4766147
theorem B2118287 : Blo 2117435 2118287 := bstep (se 1 (by rfl) ⟨1588715, by rfl⟩ : syracuseStep 2118287 = 3177431) B3177431
theorem B3177437 : Blo 2117435 3177437 := bbase (se 3 (by rfl) ⟨595769, by rfl⟩ : syracuseStep 3177437 = 1191539) (by norm_num)
theorem B2118291 : Blo 2117435 2118291 := bstep (se 1 (by rfl) ⟨1588718, by rfl⟩ : syracuseStep 2118291 = 3177437) B3177437
theorem B4766165 : Blo 2117435 4766165 := bbase (se 7 (by rfl) ⟨55853, by rfl⟩ : syracuseStep 4766165 = 111707) (by norm_num)
theorem B3177443 : Blo 2117435 3177443 := bstep (se 1 (by rfl) ⟨2383082, by rfl⟩ : syracuseStep 3177443 = 4766165) B4766165
theorem B2118295 : Blo 2117435 2118295 := bstep (se 1 (by rfl) ⟨1588721, by rfl⟩ : syracuseStep 2118295 = 3177443) B3177443
theorem B6618581 : Blo 2117435 6618581 := bbase (se 7 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 6618581 = 155123) (by norm_num)
theorem B4412387 : Blo 2117435 4412387 := bstep (se 1 (by rfl) ⟨3309290, by rfl⟩ : syracuseStep 4412387 = 6618581) B6618581
theorem B2941591 : Blo 2117435 2941591 := bstep (se 1 (by rfl) ⟨2206193, by rfl⟩ : syracuseStep 2941591 = 4412387) B4412387
theorem B3922121 : Blo 2117435 3922121 := bstep (se 2 (by rfl) ⟨1470795, by rfl⟩ : syracuseStep 3922121 = 2941591) B2941591
theorem B2614747 : Blo 2117435 2614747 := bstep (se 1 (by rfl) ⟨1961060, by rfl⟩ : syracuseStep 2614747 = 3922121) B3922121
theorem B3486329 : Blo 2117435 3486329 := bstep (se 2 (by rfl) ⟨1307373, by rfl⟩ : syracuseStep 3486329 = 2614747) B2614747
theorem B2324219 : Blo 2117435 2324219 := bstep (se 1 (by rfl) ⟨1743164, by rfl⟩ : syracuseStep 2324219 = 3486329) B3486329
theorem B6197917 : Blo 2117435 6197917 := bstep (se 3 (by rfl) ⟨1162109, by rfl⟩ : syracuseStep 6197917 = 2324219) B2324219
theorem B8263889 : Blo 2117435 8263889 := bstep (se 2 (by rfl) ⟨3098958, by rfl⟩ : syracuseStep 8263889 = 6197917) B6197917
theorem B5509259 : Blo 2117435 5509259 := bstep (se 1 (by rfl) ⟨4131944, by rfl⟩ : syracuseStep 5509259 = 8263889) B8263889
theorem B3672839 : Blo 2117435 3672839 := bstep (se 1 (by rfl) ⟨2754629, by rfl⟩ : syracuseStep 3672839 = 5509259) B5509259
theorem B2448559 : Blo 2117435 2448559 := bstep (se 1 (by rfl) ⟨1836419, by rfl⟩ : syracuseStep 2448559 = 3672839) B3672839
theorem B13058981 : Blo 2117435 13058981 := bstep (se 4 (by rfl) ⟨1224279, by rfl⟩ : syracuseStep 13058981 = 2448559) B2448559
theorem B8705987 : Blo 2117435 8705987 := bstep (se 1 (by rfl) ⟨6529490, by rfl⟩ : syracuseStep 8705987 = 13058981) B13058981
theorem B5803991 : Blo 2117435 5803991 := bstep (se 1 (by rfl) ⟨4352993, by rfl⟩ : syracuseStep 5803991 = 8705987) B8705987
theorem B3869327 : Blo 2117435 3869327 := bstep (se 1 (by rfl) ⟨2901995, by rfl⟩ : syracuseStep 3869327 = 5803991) B5803991
theorem B10318205 : Blo 2117435 10318205 := bstep (se 3 (by rfl) ⟨1934663, by rfl⟩ : syracuseStep 10318205 = 3869327) B3869327
theorem B27515213 : Blo 2117435 27515213 := bstep (se 3 (by rfl) ⟨5159102, by rfl⟩ : syracuseStep 27515213 = 10318205) B10318205
theorem B18343475 : Blo 2117435 18343475 := bstep (se 1 (by rfl) ⟨13757606, by rfl⟩ : syracuseStep 18343475 = 27515213) B27515213
theorem B12228983 : Blo 2117435 12228983 := bstep (se 1 (by rfl) ⟨9171737, by rfl⟩ : syracuseStep 12228983 = 18343475) B18343475
theorem B8152655 : Blo 2117435 8152655 := bstep (se 1 (by rfl) ⟨6114491, by rfl⟩ : syracuseStep 8152655 = 12228983) B12228983
theorem B21740413 : Blo 2117435 21740413 := bstep (se 3 (by rfl) ⟨4076327, by rfl⟩ : syracuseStep 21740413 = 8152655) B8152655
theorem B28987217 : Blo 2117435 28987217 := bstep (se 2 (by rfl) ⟨10870206, by rfl⟩ : syracuseStep 28987217 = 21740413) B21740413
theorem B19324811 : Blo 2117435 19324811 := bstep (se 1 (by rfl) ⟨14493608, by rfl⟩ : syracuseStep 19324811 = 28987217) B28987217
theorem B12883207 : Blo 2117435 12883207 := bstep (se 1 (by rfl) ⟨9662405, by rfl⟩ : syracuseStep 12883207 = 19324811) B19324811
theorem B17177609 : Blo 2117435 17177609 := bstep (se 2 (by rfl) ⟨6441603, by rfl⟩ : syracuseStep 17177609 = 12883207) B12883207
theorem B45806957 : Blo 2117435 45806957 := bstep (se 3 (by rfl) ⟨8588804, by rfl⟩ : syracuseStep 45806957 = 17177609) B17177609
theorem B30537971 : Blo 2117435 30537971 := bstep (se 1 (by rfl) ⟨22903478, by rfl⟩ : syracuseStep 30537971 = 45806957) B45806957
theorem B20358647 : Blo 2117435 20358647 := bstep (se 1 (by rfl) ⟨15268985, by rfl⟩ : syracuseStep 20358647 = 30537971) B30537971
theorem B13572431 : Blo 2117435 13572431 := bstep (se 1 (by rfl) ⟨10179323, by rfl⟩ : syracuseStep 13572431 = 20358647) B20358647
theorem B9048287 : Blo 2117435 9048287 := bstep (se 1 (by rfl) ⟨6786215, by rfl⟩ : syracuseStep 9048287 = 13572431) B13572431
theorem B6032191 : Blo 2117435 6032191 := bstep (se 1 (by rfl) ⟨4524143, by rfl⟩ : syracuseStep 6032191 = 9048287) B9048287
theorem B8042921 : Blo 2117435 8042921 := bstep (se 2 (by rfl) ⟨3016095, by rfl⟩ : syracuseStep 8042921 = 6032191) B6032191
theorem B5361947 : Blo 2117435 5361947 := bstep (se 1 (by rfl) ⟨4021460, by rfl⟩ : syracuseStep 5361947 = 8042921) B8042921
theorem B3574631 : Blo 2117435 3574631 := bstep (se 1 (by rfl) ⟨2680973, by rfl⟩ : syracuseStep 3574631 = 5361947) B5361947
theorem B2383087 : Blo 2117435 2383087 := bstep (se 1 (by rfl) ⟨1787315, by rfl⟩ : syracuseStep 2383087 = 3574631) B3574631
theorem B3177449 : Blo 2117435 3177449 := bstep (se 2 (by rfl) ⟨1191543, by rfl⟩ : syracuseStep 3177449 = 2383087) B2383087
theorem B2118299 : Blo 2117435 2118299 := bstep (se 1 (by rfl) ⟨1588724, by rfl⟩ : syracuseStep 2118299 = 3177449) B3177449
theorem B3817253 : Blo 2117435 3817253 := bbase (se 4 (by rfl) ⟨357867, by rfl⟩ : syracuseStep 3817253 = 715735) (by norm_num)
theorem B10179341 : Blo 2117435 10179341 := bstep (se 3 (by rfl) ⟨1908626, by rfl⟩ : syracuseStep 10179341 = 3817253) B3817253
theorem B6786227 : Blo 2117435 6786227 := bstep (se 1 (by rfl) ⟨5089670, by rfl⟩ : syracuseStep 6786227 = 10179341) B10179341
theorem B18096605 : Blo 2117435 18096605 := bstep (se 3 (by rfl) ⟨3393113, by rfl⟩ : syracuseStep 18096605 = 6786227) B6786227
theorem B12064403 : Blo 2117435 12064403 := bstep (se 1 (by rfl) ⟨9048302, by rfl⟩ : syracuseStep 12064403 = 18096605) B18096605
theorem B8042935 : Blo 2117435 8042935 := bstep (se 1 (by rfl) ⟨6032201, by rfl⟩ : syracuseStep 8042935 = 12064403) B12064403
theorem B10723913 : Blo 2117435 10723913 := bstep (se 2 (by rfl) ⟨4021467, by rfl⟩ : syracuseStep 10723913 = 8042935) B8042935
theorem B7149275 : Blo 2117435 7149275 := bstep (se 1 (by rfl) ⟨5361956, by rfl⟩ : syracuseStep 7149275 = 10723913) B10723913
theorem B4766183 : Blo 2117435 4766183 := bstep (se 1 (by rfl) ⟨3574637, by rfl⟩ : syracuseStep 4766183 = 7149275) B7149275
theorem B3177455 : Blo 2117435 3177455 := bstep (se 1 (by rfl) ⟨2383091, by rfl⟩ : syracuseStep 3177455 = 4766183) B4766183
theorem B2118303 : Blo 2117435 2118303 := bstep (se 1 (by rfl) ⟨1588727, by rfl⟩ : syracuseStep 2118303 = 3177455) B3177455
theorem B3177461 : Blo 2117435 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B2118307 : Blo 2117435 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B3922141 : Blo 2117435 3922141 := bbase (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) (by norm_num)
theorem B5229521 : Blo 2117435 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B3486347 : Blo 2117435 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B148750805 : Blo 2117435 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B99167203 : Blo 2117435 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B132222937 : Blo 2117435 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B176297249 : Blo 2117435 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B117531499 : Blo 2117435 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B156708665 : Blo 2117435 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B104472443 : Blo 2117435 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B278593181 : Blo 2117435 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B185728787 : Blo 2117435 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B123819191 : Blo 2117435 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B82546127 : Blo 2117435 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B55030751 : Blo 2117435 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B36687167 : Blo 2117435 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B24458111 : Blo 2117435 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B16305407 : Blo 2117435 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B10870271 : Blo 2117435 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B7246847 : Blo 2117435 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B19324925 : Blo 2117435 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B12883283 : Blo 2117435 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B8588855 : Blo 2117435 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B5725903 : Blo 2117435 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B7634537 : Blo 2117435 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B5089691 : Blo 2117435 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B3393127 : Blo 2117435 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B4524169 : Blo 2117435 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B6032225 : Blo 2117435 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B4021483 : Blo 2117435 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B5361977 : Blo 2117435 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B3574651 : Blo 2117435 3574651 := bstep (se 1 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 3574651 = 5361977) B5361977
theorem B4766201 : Blo 2117435 4766201 := bstep (se 2 (by rfl) ⟨1787325, by rfl⟩ : syracuseStep 4766201 = 3574651) B3574651
theorem B3177467 : Blo 2117435 3177467 := bstep (se 1 (by rfl) ⟨2383100, by rfl⟩ : syracuseStep 3177467 = 4766201) B4766201
theorem B2118311 : Blo 2117435 2118311 := bstep (se 1 (by rfl) ⟨1588733, by rfl⟩ : syracuseStep 2118311 = 3177467) B3177467
theorem B2383105 : Blo 2117435 2383105 := bbase (se 2 (by rfl) ⟨893664, by rfl⟩ : syracuseStep 2383105 = 1787329) (by norm_num)
theorem B3177473 : Blo 2117435 3177473 := bstep (se 2 (by rfl) ⟨1191552, by rfl⟩ : syracuseStep 3177473 = 2383105) B2383105
theorem B2118315 : Blo 2117435 2118315 := bstep (se 1 (by rfl) ⟨1588736, by rfl⟩ : syracuseStep 2118315 = 3177473) B3177473
theorem B5361997 : Blo 2117435 5361997 := bbase (se 3 (by rfl) ⟨1005374, by rfl⟩ : syracuseStep 5361997 = 2010749) (by norm_num)
theorem B7149329 : Blo 2117435 7149329 := bstep (se 2 (by rfl) ⟨2680998, by rfl⟩ : syracuseStep 7149329 = 5361997) B5361997
theorem B4766219 : Blo 2117435 4766219 := bstep (se 1 (by rfl) ⟨3574664, by rfl⟩ : syracuseStep 4766219 = 7149329) B7149329
theorem B3177479 : Blo 2117435 3177479 := bstep (se 1 (by rfl) ⟨2383109, by rfl⟩ : syracuseStep 3177479 = 4766219) B4766219
theorem B2118319 : Blo 2117435 2118319 := bstep (se 1 (by rfl) ⟨1588739, by rfl⟩ : syracuseStep 2118319 = 3177479) B3177479
theorem B3177485 : Blo 2117435 3177485 := bbase (se 3 (by rfl) ⟨595778, by rfl⟩ : syracuseStep 3177485 = 1191557) (by norm_num)
theorem B2118323 : Blo 2117435 2118323 := bstep (se 1 (by rfl) ⟨1588742, by rfl⟩ : syracuseStep 2118323 = 3177485) B3177485
theorem B4766237 : Blo 2117435 4766237 := bbase (se 3 (by rfl) ⟨893669, by rfl⟩ : syracuseStep 4766237 = 1787339) (by norm_num)
theorem B3177491 : Blo 2117435 3177491 := bstep (se 1 (by rfl) ⟨2383118, by rfl⟩ : syracuseStep 3177491 = 4766237) B4766237
theorem B2118327 : Blo 2117435 2118327 := bstep (se 1 (by rfl) ⟨1588745, by rfl⟩ : syracuseStep 2118327 = 3177491) B3177491
theorem B3574685 : Blo 2117435 3574685 := bbase (se 3 (by rfl) ⟨670253, by rfl⟩ : syracuseStep 3574685 = 1340507) (by norm_num)
theorem B2383123 : Blo 2117435 2383123 := bstep (se 1 (by rfl) ⟨1787342, by rfl⟩ : syracuseStep 2383123 = 3574685) B3574685
theorem B3177497 : Blo 2117435 3177497 := bstep (se 2 (by rfl) ⟨1191561, by rfl⟩ : syracuseStep 3177497 = 2383123) B2383123
theorem B2118331 : Blo 2117435 2118331 := bstep (se 1 (by rfl) ⟨1588748, by rfl⟩ : syracuseStep 2118331 = 3177497) B3177497
theorem B4831285 : Blo 2117435 4831285 := bbase (se 5 (by rfl) ⟨226466, by rfl⟩ : syracuseStep 4831285 = 452933) (by norm_num)
theorem B6441713 : Blo 2117435 6441713 := bstep (se 2 (by rfl) ⟨2415642, by rfl⟩ : syracuseStep 6441713 = 4831285) B4831285
theorem B4294475 : Blo 2117435 4294475 := bstep (se 1 (by rfl) ⟨3220856, by rfl⟩ : syracuseStep 4294475 = 6441713) B6441713
theorem B2862983 : Blo 2117435 2862983 := bstep (se 1 (by rfl) ⟨2147237, by rfl⟩ : syracuseStep 2862983 = 4294475) B4294475
theorem B7634621 : Blo 2117435 7634621 := bstep (se 3 (by rfl) ⟨1431491, by rfl⟩ : syracuseStep 7634621 = 2862983) B2862983
theorem B20358989 : Blo 2117435 20358989 := bstep (se 3 (by rfl) ⟨3817310, by rfl⟩ : syracuseStep 20358989 = 7634621) B7634621
theorem B13572659 : Blo 2117435 13572659 := bstep (se 1 (by rfl) ⟨10179494, by rfl⟩ : syracuseStep 13572659 = 20358989) B20358989
theorem B9048439 : Blo 2117435 9048439 := bstep (se 1 (by rfl) ⟨6786329, by rfl⟩ : syracuseStep 9048439 = 13572659) B13572659
theorem B12064585 : Blo 2117435 12064585 := bstep (se 2 (by rfl) ⟨4524219, by rfl⟩ : syracuseStep 12064585 = 9048439) B9048439
theorem B16086113 : Blo 2117435 16086113 := bstep (se 2 (by rfl) ⟨6032292, by rfl⟩ : syracuseStep 16086113 = 12064585) B12064585
theorem B10724075 : Blo 2117435 10724075 := bstep (se 1 (by rfl) ⟨8043056, by rfl⟩ : syracuseStep 10724075 = 16086113) B16086113
theorem B7149383 : Blo 2117435 7149383 := bstep (se 1 (by rfl) ⟨5362037, by rfl⟩ : syracuseStep 7149383 = 10724075) B10724075
theorem B4766255 : Blo 2117435 4766255 := bstep (se 1 (by rfl) ⟨3574691, by rfl⟩ : syracuseStep 4766255 = 7149383) B7149383
theorem B3177503 : Blo 2117435 3177503 := bstep (se 1 (by rfl) ⟨2383127, by rfl⟩ : syracuseStep 3177503 = 4766255) B4766255
theorem B2118335 : Blo 2117435 2118335 := bstep (se 1 (by rfl) ⟨1588751, by rfl⟩ : syracuseStep 2118335 = 3177503) B3177503
theorem B3177509 : Blo 2117435 3177509 := bbase (se 4 (by rfl) ⟨297891, by rfl⟩ : syracuseStep 3177509 = 595783) (by norm_num)
theorem B2118339 : Blo 2117435 2118339 := bstep (se 1 (by rfl) ⟨1588754, by rfl⟩ : syracuseStep 2118339 = 3177509) B3177509
theorem B2681029 : Blo 2117435 2681029 := bbase (se 4 (by rfl) ⟨251346, by rfl⟩ : syracuseStep 2681029 = 502693) (by norm_num)
theorem B3574705 : Blo 2117435 3574705 := bstep (se 2 (by rfl) ⟨1340514, by rfl⟩ : syracuseStep 3574705 = 2681029) B2681029
theorem B4766273 : Blo 2117435 4766273 := bstep (se 2 (by rfl) ⟨1787352, by rfl⟩ : syracuseStep 4766273 = 3574705) B3574705
theorem B3177515 : Blo 2117435 3177515 := bstep (se 1 (by rfl) ⟨2383136, by rfl⟩ : syracuseStep 3177515 = 4766273) B4766273
theorem B2118343 : Blo 2117435 2118343 := bstep (se 1 (by rfl) ⟨1588757, by rfl⟩ : syracuseStep 2118343 = 3177515) B3177515
theorem B2383141 : Blo 2117435 2383141 := bbase (se 4 (by rfl) ⟨223419, by rfl⟩ : syracuseStep 2383141 = 446839) (by norm_num)
theorem B3177521 : Blo 2117435 3177521 := bstep (se 2 (by rfl) ⟨1191570, by rfl⟩ : syracuseStep 3177521 = 2383141) B2383141
theorem B2118347 : Blo 2117435 2118347 := bstep (se 1 (by rfl) ⟨1588760, by rfl⟩ : syracuseStep 2118347 = 3177521) B3177521
theorem B9662645 : Blo 2117435 9662645 := bbase (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) (by norm_num)
theorem B6441763 : Blo 2117435 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B8589017 : Blo 2117435 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B5726011 : Blo 2117435 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B7634681 : Blo 2117435 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B5089787 : Blo 2117435 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B3393191 : Blo 2117435 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B9048509 : Blo 2117435 9048509 := bstep (se 3 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 9048509 = 3393191) B3393191
theorem B6032339 : Blo 2117435 6032339 := bstep (se 1 (by rfl) ⟨4524254, by rfl⟩ : syracuseStep 6032339 = 9048509) B9048509
theorem B4021559 : Blo 2117435 4021559 := bstep (se 1 (by rfl) ⟨3016169, by rfl⟩ : syracuseStep 4021559 = 6032339) B6032339
theorem B2681039 : Blo 2117435 2681039 := bstep (se 1 (by rfl) ⟨2010779, by rfl⟩ : syracuseStep 2681039 = 4021559) B4021559
theorem B7149437 : Blo 2117435 7149437 := bstep (se 3 (by rfl) ⟨1340519, by rfl⟩ : syracuseStep 7149437 = 2681039) B2681039
theorem B4766291 : Blo 2117435 4766291 := bstep (se 1 (by rfl) ⟨3574718, by rfl⟩ : syracuseStep 4766291 = 7149437) B7149437
theorem B3177527 : Blo 2117435 3177527 := bstep (se 1 (by rfl) ⟨2383145, by rfl⟩ : syracuseStep 3177527 = 4766291) B4766291
theorem B2118351 : Blo 2117435 2118351 := bstep (se 1 (by rfl) ⟨1588763, by rfl⟩ : syracuseStep 2118351 = 3177527) B3177527
theorem B3177533 : Blo 2117435 3177533 := bbase (se 3 (by rfl) ⟨595787, by rfl⟩ : syracuseStep 3177533 = 1191575) (by norm_num)
theorem B2118355 : Blo 2117435 2118355 := bstep (se 1 (by rfl) ⟨1588766, by rfl⟩ : syracuseStep 2118355 = 3177533) B3177533
theorem B4766309 : Blo 2117435 4766309 := bbase (se 4 (by rfl) ⟨446841, by rfl⟩ : syracuseStep 4766309 = 893683) (by norm_num)
theorem B3177539 : Blo 2117435 3177539 := bstep (se 1 (by rfl) ⟨2383154, by rfl⟩ : syracuseStep 3177539 = 4766309) B4766309
theorem B2118359 : Blo 2117435 2118359 := bstep (se 1 (by rfl) ⟨1588769, by rfl⟩ : syracuseStep 2118359 = 3177539) B3177539
theorem B5362109 : Blo 2117435 5362109 := bbase (se 3 (by rfl) ⟨1005395, by rfl⟩ : syracuseStep 5362109 = 2010791) (by norm_num)
theorem B3574739 : Blo 2117435 3574739 := bstep (se 1 (by rfl) ⟨2681054, by rfl⟩ : syracuseStep 3574739 = 5362109) B5362109
theorem B2383159 : Blo 2117435 2383159 := bstep (se 1 (by rfl) ⟨1787369, by rfl⟩ : syracuseStep 2383159 = 3574739) B3574739
theorem B3177545 : Blo 2117435 3177545 := bstep (se 2 (by rfl) ⟨1191579, by rfl⟩ : syracuseStep 3177545 = 2383159) B2383159
theorem B2118363 : Blo 2117435 2118363 := bstep (se 1 (by rfl) ⟨1588772, by rfl⟩ : syracuseStep 2118363 = 3177545) B3177545
theorem B4021589 : Blo 2117435 4021589 := bbase (se 11 (by rfl) ⟨2945, by rfl⟩ : syracuseStep 4021589 = 5891) (by norm_num)
theorem B10724237 : Blo 2117435 10724237 := bstep (se 3 (by rfl) ⟨2010794, by rfl⟩ : syracuseStep 10724237 = 4021589) B4021589
theorem B7149491 : Blo 2117435 7149491 := bstep (se 1 (by rfl) ⟨5362118, by rfl⟩ : syracuseStep 7149491 = 10724237) B10724237
theorem B4766327 : Blo 2117435 4766327 := bstep (se 1 (by rfl) ⟨3574745, by rfl⟩ : syracuseStep 4766327 = 7149491) B7149491
theorem B3177551 : Blo 2117435 3177551 := bstep (se 1 (by rfl) ⟨2383163, by rfl⟩ : syracuseStep 3177551 = 4766327) B4766327
theorem B2118367 : Blo 2117435 2118367 := bstep (se 1 (by rfl) ⟨1588775, by rfl⟩ : syracuseStep 2118367 = 3177551) B3177551
theorem B3177557 : Blo 2117435 3177557 := bbase (se 8 (by rfl) ⟨18618, by rfl⟩ : syracuseStep 3177557 = 37237) (by norm_num)
theorem B2118371 : Blo 2117435 2118371 := bstep (se 1 (by rfl) ⟨1588778, by rfl⟩ : syracuseStep 2118371 = 3177557) B3177557
theorem B13572917 : Blo 2117435 13572917 := bbase (se 5 (by rfl) ⟨636230, by rfl⟩ : syracuseStep 13572917 = 1272461) (by norm_num)
theorem B9048611 : Blo 2117435 9048611 := bstep (se 1 (by rfl) ⟨6786458, by rfl⟩ : syracuseStep 9048611 = 13572917) B13572917
theorem B6032407 : Blo 2117435 6032407 := bstep (se 1 (by rfl) ⟨4524305, by rfl⟩ : syracuseStep 6032407 = 9048611) B9048611
theorem B8043209 : Blo 2117435 8043209 := bstep (se 2 (by rfl) ⟨3016203, by rfl⟩ : syracuseStep 8043209 = 6032407) B6032407
theorem B5362139 : Blo 2117435 5362139 := bstep (se 1 (by rfl) ⟨4021604, by rfl⟩ : syracuseStep 5362139 = 8043209) B8043209
theorem B3574759 : Blo 2117435 3574759 := bstep (se 1 (by rfl) ⟨2681069, by rfl⟩ : syracuseStep 3574759 = 5362139) B5362139
theorem B4766345 : Blo 2117435 4766345 := bstep (se 2 (by rfl) ⟨1787379, by rfl⟩ : syracuseStep 4766345 = 3574759) B3574759
theorem B3177563 : Blo 2117435 3177563 := bstep (se 1 (by rfl) ⟨2383172, by rfl⟩ : syracuseStep 3177563 = 4766345) B4766345
theorem B2118375 : Blo 2117435 2118375 := bstep (se 1 (by rfl) ⟨1588781, by rfl⟩ : syracuseStep 2118375 = 3177563) B3177563
theorem B2383177 : Blo 2117435 2383177 := bbase (se 2 (by rfl) ⟨893691, by rfl⟩ : syracuseStep 2383177 = 1787383) (by norm_num)
theorem B3177569 : Blo 2117435 3177569 := bstep (se 2 (by rfl) ⟨1191588, by rfl⟩ : syracuseStep 3177569 = 2383177) B2383177
theorem B2118379 : Blo 2117435 2118379 := bstep (se 1 (by rfl) ⟨1588784, by rfl⟩ : syracuseStep 2118379 = 3177569) B3177569
theorem B2579653 : Blo 2117435 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B13758149 : Blo 2117435 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B9172099 : Blo 2117435 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B12229465 : Blo 2117435 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B16305953 : Blo 2117435 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B173930165 : Blo 2117435 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B115953443 : Blo 2117435 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B77302295 : Blo 2117435 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B51534863 : Blo 2117435 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B34356575 : Blo 2117435 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B22904383 : Blo 2117435 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B30539177 : Blo 2117435 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B20359451 : Blo 2117435 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B13572967 : Blo 2117435 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B18097289 : Blo 2117435 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B12064859 : Blo 2117435 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B8043239 : Blo 2117435 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B5362159 : Blo 2117435 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B7149545 : Blo 2117435 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B4766363 : Blo 2117435 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B3177575 : Blo 2117435 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B2118383 : Blo 2117435 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B3177581 : Blo 2117435 3177581 := bbase (se 3 (by rfl) ⟨595796, by rfl⟩ : syracuseStep 3177581 = 1191593) (by norm_num)
theorem B2118387 : Blo 2117435 2118387 := bstep (se 1 (by rfl) ⟨1588790, by rfl⟩ : syracuseStep 2118387 = 3177581) B3177581
theorem B4766381 : Blo 2117435 4766381 := bbase (se 3 (by rfl) ⟨893696, by rfl⟩ : syracuseStep 4766381 = 1787393) (by norm_num)
theorem B3177587 : Blo 2117435 3177587 := bstep (se 1 (by rfl) ⟨2383190, by rfl⟩ : syracuseStep 3177587 = 4766381) B4766381
theorem B2118391 : Blo 2117435 2118391 := bstep (se 1 (by rfl) ⟨1588793, by rfl⟩ : syracuseStep 2118391 = 3177587) B3177587
theorem B4524349 : Blo 2117435 4524349 := bbase (se 3 (by rfl) ⟨848315, by rfl⟩ : syracuseStep 4524349 = 1696631) (by norm_num)
theorem B6032465 : Blo 2117435 6032465 := bstep (se 2 (by rfl) ⟨2262174, by rfl⟩ : syracuseStep 6032465 = 4524349) B4524349
theorem B4021643 : Blo 2117435 4021643 := bstep (se 1 (by rfl) ⟨3016232, by rfl⟩ : syracuseStep 4021643 = 6032465) B6032465
theorem B2681095 : Blo 2117435 2681095 := bstep (se 1 (by rfl) ⟨2010821, by rfl⟩ : syracuseStep 2681095 = 4021643) B4021643
theorem B3574793 : Blo 2117435 3574793 := bstep (se 2 (by rfl) ⟨1340547, by rfl⟩ : syracuseStep 3574793 = 2681095) B2681095
theorem B2383195 : Blo 2117435 2383195 := bstep (se 1 (by rfl) ⟨1787396, by rfl⟩ : syracuseStep 2383195 = 3574793) B3574793
theorem B3177593 : Blo 2117435 3177593 := bstep (se 2 (by rfl) ⟨1191597, by rfl⟩ : syracuseStep 3177593 = 2383195) B2383195
theorem B2118395 : Blo 2117435 2118395 := bstep (se 1 (by rfl) ⟨1588796, by rfl⟩ : syracuseStep 2118395 = 3177593) B3177593
theorem B11452277 : Blo 2117435 11452277 := bbase (se 5 (by rfl) ⟨536825, by rfl⟩ : syracuseStep 11452277 = 1073651) (by norm_num)
theorem B30539405 : Blo 2117435 30539405 := bstep (se 3 (by rfl) ⟨5726138, by rfl⟩ : syracuseStep 30539405 = 11452277) B11452277
theorem B20359603 : Blo 2117435 20359603 := bstep (se 1 (by rfl) ⟨15269702, by rfl⟩ : syracuseStep 20359603 = 30539405) B30539405
theorem B27146137 : Blo 2117435 27146137 := bstep (se 2 (by rfl) ⟨10179801, by rfl⟩ : syracuseStep 27146137 = 20359603) B20359603
theorem B36194849 : Blo 2117435 36194849 := bstep (se 2 (by rfl) ⟨13573068, by rfl⟩ : syracuseStep 36194849 = 27146137) B27146137
theorem B24129899 : Blo 2117435 24129899 := bstep (se 1 (by rfl) ⟨18097424, by rfl⟩ : syracuseStep 24129899 = 36194849) B36194849
theorem B16086599 : Blo 2117435 16086599 := bstep (se 1 (by rfl) ⟨12064949, by rfl⟩ : syracuseStep 16086599 = 24129899) B24129899
theorem B10724399 : Blo 2117435 10724399 := bstep (se 1 (by rfl) ⟨8043299, by rfl⟩ : syracuseStep 10724399 = 16086599) B16086599
theorem B7149599 : Blo 2117435 7149599 := bstep (se 1 (by rfl) ⟨5362199, by rfl⟩ : syracuseStep 7149599 = 10724399) B10724399
theorem B4766399 : Blo 2117435 4766399 := bstep (se 1 (by rfl) ⟨3574799, by rfl⟩ : syracuseStep 4766399 = 7149599) B7149599
theorem B3177599 : Blo 2117435 3177599 := bstep (se 1 (by rfl) ⟨2383199, by rfl⟩ : syracuseStep 3177599 = 4766399) B4766399
theorem B2118399 : Blo 2117435 2118399 := bstep (se 1 (by rfl) ⟨1588799, by rfl⟩ : syracuseStep 2118399 = 3177599) B3177599
theorem B3177605 : Blo 2117435 3177605 := bbase (se 4 (by rfl) ⟨297900, by rfl⟩ : syracuseStep 3177605 = 595801) (by norm_num)
theorem B2118403 : Blo 2117435 2118403 := bstep (se 1 (by rfl) ⟨1588802, by rfl⟩ : syracuseStep 2118403 = 3177605) B3177605
theorem B3574813 : Blo 2117435 3574813 := bbase (se 3 (by rfl) ⟨670277, by rfl⟩ : syracuseStep 3574813 = 1340555) (by norm_num)
theorem B4766417 : Blo 2117435 4766417 := bstep (se 2 (by rfl) ⟨1787406, by rfl⟩ : syracuseStep 4766417 = 3574813) B3574813
theorem B3177611 : Blo 2117435 3177611 := bstep (se 1 (by rfl) ⟨2383208, by rfl⟩ : syracuseStep 3177611 = 4766417) B4766417
theorem B2118407 : Blo 2117435 2118407 := bstep (se 1 (by rfl) ⟨1588805, by rfl⟩ : syracuseStep 2118407 = 3177611) B3177611
theorem B2383213 : Blo 2117435 2383213 := bbase (se 3 (by rfl) ⟨446852, by rfl⟩ : syracuseStep 2383213 = 893705) (by norm_num)
theorem B3177617 : Blo 2117435 3177617 := bstep (se 2 (by rfl) ⟨1191606, by rfl⟩ : syracuseStep 3177617 = 2383213) B2383213
theorem B2118411 : Blo 2117435 2118411 := bstep (se 1 (by rfl) ⟨1588808, by rfl⟩ : syracuseStep 2118411 = 3177617) B3177617
theorem B7149653 : Blo 2117435 7149653 := bbase (se 8 (by rfl) ⟨41892, by rfl⟩ : syracuseStep 7149653 = 83785) (by norm_num)
theorem B4766435 : Blo 2117435 4766435 := bstep (se 1 (by rfl) ⟨3574826, by rfl⟩ : syracuseStep 4766435 = 7149653) B7149653
theorem B3177623 : Blo 2117435 3177623 := bstep (se 1 (by rfl) ⟨2383217, by rfl⟩ : syracuseStep 3177623 = 4766435) B4766435
theorem B2118415 : Blo 2117435 2118415 := bstep (se 1 (by rfl) ⟨1588811, by rfl⟩ : syracuseStep 2118415 = 3177623) B3177623
theorem B3177629 : Blo 2117435 3177629 := bbase (se 3 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 3177629 = 1191611) (by norm_num)
theorem B2118419 : Blo 2117435 2118419 := bstep (se 1 (by rfl) ⟨1588814, by rfl⟩ : syracuseStep 2118419 = 3177629) B3177629
theorem B4766453 : Blo 2117435 4766453 := bbase (se 5 (by rfl) ⟨223427, by rfl⟩ : syracuseStep 4766453 = 446855) (by norm_num)
theorem B3177635 : Blo 2117435 3177635 := bstep (se 1 (by rfl) ⟨2383226, by rfl⟩ : syracuseStep 3177635 = 4766453) B4766453
theorem B2118423 : Blo 2117435 2118423 := bstep (se 1 (by rfl) ⟨1588817, by rfl⟩ : syracuseStep 2118423 = 3177635) B3177635
theorem B3817477 : Blo 2117435 3817477 := bbase (se 4 (by rfl) ⟨357888, by rfl⟩ : syracuseStep 3817477 = 715777) (by norm_num)
theorem B5089969 : Blo 2117435 5089969 := bstep (se 2 (by rfl) ⟨1908738, by rfl⟩ : syracuseStep 5089969 = 3817477) B3817477
theorem B27146501 : Blo 2117435 27146501 := bstep (se 4 (by rfl) ⟨2544984, by rfl⟩ : syracuseStep 27146501 = 5089969) B5089969
theorem B18097667 : Blo 2117435 18097667 := bstep (se 1 (by rfl) ⟨13573250, by rfl⟩ : syracuseStep 18097667 = 27146501) B27146501
theorem B12065111 : Blo 2117435 12065111 := bstep (se 1 (by rfl) ⟨9048833, by rfl⟩ : syracuseStep 12065111 = 18097667) B18097667
theorem B8043407 : Blo 2117435 8043407 := bstep (se 1 (by rfl) ⟨6032555, by rfl⟩ : syracuseStep 8043407 = 12065111) B12065111
theorem B5362271 : Blo 2117435 5362271 := bstep (se 1 (by rfl) ⟨4021703, by rfl⟩ : syracuseStep 5362271 = 8043407) B8043407
theorem B3574847 : Blo 2117435 3574847 := bstep (se 1 (by rfl) ⟨2681135, by rfl⟩ : syracuseStep 3574847 = 5362271) B5362271
theorem B2383231 : Blo 2117435 2383231 := bstep (se 1 (by rfl) ⟨1787423, by rfl⟩ : syracuseStep 2383231 = 3574847) B3574847
theorem B3177641 : Blo 2117435 3177641 := bstep (se 2 (by rfl) ⟨1191615, by rfl⟩ : syracuseStep 3177641 = 2383231) B2383231
theorem B2118427 : Blo 2117435 2118427 := bstep (se 1 (by rfl) ⟨1588820, by rfl⟩ : syracuseStep 2118427 = 3177641) B3177641
theorem B3623629 : Blo 2117435 3623629 := bbase (se 3 (by rfl) ⟨679430, by rfl⟩ : syracuseStep 3623629 = 1358861) (by norm_num)
theorem B4831505 : Blo 2117435 4831505 := bstep (se 2 (by rfl) ⟨1811814, by rfl⟩ : syracuseStep 4831505 = 3623629) B3623629
theorem B3221003 : Blo 2117435 3221003 := bstep (se 1 (by rfl) ⟨2415752, by rfl⟩ : syracuseStep 3221003 = 4831505) B4831505
theorem B8589341 : Blo 2117435 8589341 := bstep (se 3 (by rfl) ⟨1610501, by rfl⟩ : syracuseStep 8589341 = 3221003) B3221003
theorem B5726227 : Blo 2117435 5726227 := bstep (se 1 (by rfl) ⟨4294670, by rfl⟩ : syracuseStep 5726227 = 8589341) B8589341
theorem B7634969 : Blo 2117435 7634969 := bstep (se 2 (by rfl) ⟨2863113, by rfl⟩ : syracuseStep 7634969 = 5726227) B5726227
theorem B5089979 : Blo 2117435 5089979 := bstep (se 1 (by rfl) ⟨3817484, by rfl⟩ : syracuseStep 5089979 = 7634969) B7634969
theorem B3393319 : Blo 2117435 3393319 := bstep (se 1 (by rfl) ⟨2544989, by rfl⟩ : syracuseStep 3393319 = 5089979) B5089979
theorem B4524425 : Blo 2117435 4524425 := bstep (se 2 (by rfl) ⟨1696659, by rfl⟩ : syracuseStep 4524425 = 3393319) B3393319
theorem B3016283 : Blo 2117435 3016283 := bstep (se 1 (by rfl) ⟨2262212, by rfl⟩ : syracuseStep 3016283 = 4524425) B4524425
theorem B8043421 : Blo 2117435 8043421 := bstep (se 3 (by rfl) ⟨1508141, by rfl⟩ : syracuseStep 8043421 = 3016283) B3016283
theorem B10724561 : Blo 2117435 10724561 := bstep (se 2 (by rfl) ⟨4021710, by rfl⟩ : syracuseStep 10724561 = 8043421) B8043421
theorem B7149707 : Blo 2117435 7149707 := bstep (se 1 (by rfl) ⟨5362280, by rfl⟩ : syracuseStep 7149707 = 10724561) B10724561
theorem B4766471 : Blo 2117435 4766471 := bstep (se 1 (by rfl) ⟨3574853, by rfl⟩ : syracuseStep 4766471 = 7149707) B7149707
theorem B3177647 : Blo 2117435 3177647 := bstep (se 1 (by rfl) ⟨2383235, by rfl⟩ : syracuseStep 3177647 = 4766471) B4766471
theorem B2118431 : Blo 2117435 2118431 := bstep (se 1 (by rfl) ⟨1588823, by rfl⟩ : syracuseStep 2118431 = 3177647) B3177647
theorem B3177653 : Blo 2117435 3177653 := bbase (se 5 (by rfl) ⟨148952, by rfl⟩ : syracuseStep 3177653 = 297905) (by norm_num)
theorem B2118435 : Blo 2117435 2118435 := bstep (se 1 (by rfl) ⟨1588826, by rfl⟩ : syracuseStep 2118435 = 3177653) B3177653
theorem B5362301 : Blo 2117435 5362301 := bbase (se 3 (by rfl) ⟨1005431, by rfl⟩ : syracuseStep 5362301 = 2010863) (by norm_num)
theorem B3574867 : Blo 2117435 3574867 := bstep (se 1 (by rfl) ⟨2681150, by rfl⟩ : syracuseStep 3574867 = 5362301) B5362301
theorem B4766489 : Blo 2117435 4766489 := bstep (se 2 (by rfl) ⟨1787433, by rfl⟩ : syracuseStep 4766489 = 3574867) B3574867
theorem B3177659 : Blo 2117435 3177659 := bstep (se 1 (by rfl) ⟨2383244, by rfl⟩ : syracuseStep 3177659 = 4766489) B4766489
theorem B2118439 : Blo 2117435 2118439 := bstep (se 1 (by rfl) ⟨1588829, by rfl⟩ : syracuseStep 2118439 = 3177659) B3177659
theorem B2383249 : Blo 2117435 2383249 := bbase (se 2 (by rfl) ⟨893718, by rfl⟩ : syracuseStep 2383249 = 1787437) (by norm_num)
theorem B3177665 : Blo 2117435 3177665 := bstep (se 2 (by rfl) ⟨1191624, by rfl⟩ : syracuseStep 3177665 = 2383249) B2383249
theorem B2118443 : Blo 2117435 2118443 := bstep (se 1 (by rfl) ⟨1588832, by rfl⟩ : syracuseStep 2118443 = 3177665) B3177665
theorem B4021741 : Blo 2117435 4021741 := bbase (se 3 (by rfl) ⟨754076, by rfl⟩ : syracuseStep 4021741 = 1508153) (by norm_num)
theorem B5362321 : Blo 2117435 5362321 := bstep (se 2 (by rfl) ⟨2010870, by rfl⟩ : syracuseStep 5362321 = 4021741) B4021741
theorem B7149761 : Blo 2117435 7149761 := bstep (se 2 (by rfl) ⟨2681160, by rfl⟩ : syracuseStep 7149761 = 5362321) B5362321
theorem B4766507 : Blo 2117435 4766507 := bstep (se 1 (by rfl) ⟨3574880, by rfl⟩ : syracuseStep 4766507 = 7149761) B7149761
theorem B3177671 : Blo 2117435 3177671 := bstep (se 1 (by rfl) ⟨2383253, by rfl⟩ : syracuseStep 3177671 = 4766507) B4766507
theorem B2118447 : Blo 2117435 2118447 := bstep (se 1 (by rfl) ⟨1588835, by rfl⟩ : syracuseStep 2118447 = 3177671) B3177671
theorem B3177677 : Blo 2117435 3177677 := bbase (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) (by norm_num)
theorem B2118451 : Blo 2117435 2118451 := bstep (se 1 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 2118451 = 3177677) B3177677
theorem B4766525 : Blo 2117435 4766525 := bbase (se 3 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 4766525 = 1787447) (by norm_num)
theorem B3177683 : Blo 2117435 3177683 := bstep (se 1 (by rfl) ⟨2383262, by rfl⟩ : syracuseStep 3177683 = 4766525) B4766525
theorem B2118455 : Blo 2117435 2118455 := bstep (se 1 (by rfl) ⟨1588841, by rfl⟩ : syracuseStep 2118455 = 3177683) B3177683
theorem B3574901 : Blo 2117435 3574901 := bbase (se 5 (by rfl) ⟨167573, by rfl⟩ : syracuseStep 3574901 = 335147) (by norm_num)
theorem B2383267 : Blo 2117435 2383267 := bstep (se 1 (by rfl) ⟨1787450, by rfl⟩ : syracuseStep 2383267 = 3574901) B3574901
theorem B3177689 : Blo 2117435 3177689 := bstep (se 2 (by rfl) ⟨1191633, by rfl⟩ : syracuseStep 3177689 = 2383267) B2383267
theorem B2118459 : Blo 2117435 2118459 := bstep (se 1 (by rfl) ⟨1588844, by rfl⟩ : syracuseStep 2118459 = 3177689) B3177689
theorem B4524493 : Blo 2117435 4524493 := bbase (se 3 (by rfl) ⟨848342, by rfl⟩ : syracuseStep 4524493 = 1696685) (by norm_num)
theorem B6032657 : Blo 2117435 6032657 := bstep (se 2 (by rfl) ⟨2262246, by rfl⟩ : syracuseStep 6032657 = 4524493) B4524493
theorem B16087085 : Blo 2117435 16087085 := bstep (se 3 (by rfl) ⟨3016328, by rfl⟩ : syracuseStep 16087085 = 6032657) B6032657
theorem B10724723 : Blo 2117435 10724723 := bstep (se 1 (by rfl) ⟨8043542, by rfl⟩ : syracuseStep 10724723 = 16087085) B16087085
theorem B7149815 : Blo 2117435 7149815 := bstep (se 1 (by rfl) ⟨5362361, by rfl⟩ : syracuseStep 7149815 = 10724723) B10724723
theorem B4766543 : Blo 2117435 4766543 := bstep (se 1 (by rfl) ⟨3574907, by rfl⟩ : syracuseStep 4766543 = 7149815) B7149815
theorem B3177695 : Blo 2117435 3177695 := bstep (se 1 (by rfl) ⟨2383271, by rfl⟩ : syracuseStep 3177695 = 4766543) B4766543
theorem B2118463 : Blo 2117435 2118463 := bstep (se 1 (by rfl) ⟨1588847, by rfl⟩ : syracuseStep 2118463 = 3177695) B3177695
theorem B3177701 : Blo 2117435 3177701 := bbase (se 4 (by rfl) ⟨297909, by rfl⟩ : syracuseStep 3177701 = 595819) (by norm_num)
theorem B2118467 : Blo 2117435 2118467 := bstep (se 1 (by rfl) ⟨1588850, by rfl⟩ : syracuseStep 2118467 = 3177701) B3177701
theorem B2579761 : Blo 2117435 2579761 := bbase (se 2 (by rfl) ⟨967410, by rfl⟩ : syracuseStep 2579761 = 1934821) (by norm_num)
theorem B13758725 : Blo 2117435 13758725 := bstep (se 4 (by rfl) ⟨1289880, by rfl⟩ : syracuseStep 13758725 = 2579761) B2579761
theorem B9172483 : Blo 2117435 9172483 := bstep (se 1 (by rfl) ⟨6879362, by rfl⟩ : syracuseStep 9172483 = 13758725) B13758725
theorem B48919909 : Blo 2117435 48919909 := bstep (se 4 (by rfl) ⟨4586241, by rfl⟩ : syracuseStep 48919909 = 9172483) B9172483
theorem B65226545 : Blo 2117435 65226545 := bstep (se 2 (by rfl) ⟨24459954, by rfl⟩ : syracuseStep 65226545 = 48919909) B48919909
theorem B43484363 : Blo 2117435 43484363 := bstep (se 1 (by rfl) ⟨32613272, by rfl⟩ : syracuseStep 43484363 = 65226545) B65226545
theorem B28989575 : Blo 2117435 28989575 := bstep (se 1 (by rfl) ⟨21742181, by rfl⟩ : syracuseStep 28989575 = 43484363) B43484363
theorem B19326383 : Blo 2117435 19326383 := bstep (se 1 (by rfl) ⟨14494787, by rfl⟩ : syracuseStep 19326383 = 28989575) B28989575
theorem B12884255 : Blo 2117435 12884255 := bstep (se 1 (by rfl) ⟨9663191, by rfl⟩ : syracuseStep 12884255 = 19326383) B19326383
theorem B8589503 : Blo 2117435 8589503 := bstep (se 1 (by rfl) ⟨6442127, by rfl⟩ : syracuseStep 8589503 = 12884255) B12884255
theorem B22905341 : Blo 2117435 22905341 := bstep (se 3 (by rfl) ⟨4294751, by rfl⟩ : syracuseStep 22905341 = 8589503) B8589503
theorem B15270227 : Blo 2117435 15270227 := bstep (se 1 (by rfl) ⟨11452670, by rfl⟩ : syracuseStep 15270227 = 22905341) B22905341
theorem B10180151 : Blo 2117435 10180151 := bstep (se 1 (by rfl) ⟨7635113, by rfl⟩ : syracuseStep 10180151 = 15270227) B15270227
theorem B6786767 : Blo 2117435 6786767 := bstep (se 1 (by rfl) ⟨5090075, by rfl⟩ : syracuseStep 6786767 = 10180151) B10180151
theorem B4524511 : Blo 2117435 4524511 := bstep (se 1 (by rfl) ⟨3393383, by rfl⟩ : syracuseStep 4524511 = 6786767) B6786767
theorem B6032681 : Blo 2117435 6032681 := bstep (se 2 (by rfl) ⟨2262255, by rfl⟩ : syracuseStep 6032681 = 4524511) B4524511
theorem B4021787 : Blo 2117435 4021787 := bstep (se 1 (by rfl) ⟨3016340, by rfl⟩ : syracuseStep 4021787 = 6032681) B6032681
theorem B2681191 : Blo 2117435 2681191 := bstep (se 1 (by rfl) ⟨2010893, by rfl⟩ : syracuseStep 2681191 = 4021787) B4021787
theorem B3574921 : Blo 2117435 3574921 := bstep (se 2 (by rfl) ⟨1340595, by rfl⟩ : syracuseStep 3574921 = 2681191) B2681191
theorem B4766561 : Blo 2117435 4766561 := bstep (se 2 (by rfl) ⟨1787460, by rfl⟩ : syracuseStep 4766561 = 3574921) B3574921
theorem B3177707 : Blo 2117435 3177707 := bstep (se 1 (by rfl) ⟨2383280, by rfl⟩ : syracuseStep 3177707 = 4766561) B4766561
theorem B2118471 : Blo 2117435 2118471 := bstep (se 1 (by rfl) ⟨1588853, by rfl⟩ : syracuseStep 2118471 = 3177707) B3177707
theorem B2383285 : Blo 2117435 2383285 := bbase (se 5 (by rfl) ⟨111716, by rfl⟩ : syracuseStep 2383285 = 223433) (by norm_num)
theorem B3177713 : Blo 2117435 3177713 := bstep (se 2 (by rfl) ⟨1191642, by rfl⟩ : syracuseStep 3177713 = 2383285) B2383285
theorem B2118475 : Blo 2117435 2118475 := bstep (se 1 (by rfl) ⟨1588856, by rfl⟩ : syracuseStep 2118475 = 3177713) B3177713
theorem B2681201 : Blo 2117435 2681201 := bbase (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) (by norm_num)
theorem B7149869 : Blo 2117435 7149869 := bstep (se 3 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 7149869 = 2681201) B2681201
theorem B4766579 : Blo 2117435 4766579 := bstep (se 1 (by rfl) ⟨3574934, by rfl⟩ : syracuseStep 4766579 = 7149869) B7149869
theorem B3177719 : Blo 2117435 3177719 := bstep (se 1 (by rfl) ⟨2383289, by rfl⟩ : syracuseStep 3177719 = 4766579) B4766579
theorem B2118479 : Blo 2117435 2118479 := bstep (se 1 (by rfl) ⟨1588859, by rfl⟩ : syracuseStep 2118479 = 3177719) B3177719
theorem B3177725 : Blo 2117435 3177725 := bbase (se 3 (by rfl) ⟨595823, by rfl⟩ : syracuseStep 3177725 = 1191647) (by norm_num)
theorem B2118483 : Blo 2117435 2118483 := bstep (se 1 (by rfl) ⟨1588862, by rfl⟩ : syracuseStep 2118483 = 3177725) B3177725
theorem B4766597 : Blo 2117435 4766597 := bbase (se 4 (by rfl) ⟨446868, by rfl⟩ : syracuseStep 4766597 = 893737) (by norm_num)
theorem B3177731 : Blo 2117435 3177731 := bstep (se 1 (by rfl) ⟨2383298, by rfl⟩ : syracuseStep 3177731 = 4766597) B4766597
theorem B2118487 : Blo 2117435 2118487 := bstep (se 1 (by rfl) ⟨1588865, by rfl⟩ : syracuseStep 2118487 = 3177731) B3177731
theorem B2262277 : Blo 2117435 2262277 := bbase (se 4 (by rfl) ⟨212088, by rfl⟩ : syracuseStep 2262277 = 424177) (by norm_num)
theorem B3016369 : Blo 2117435 3016369 := bstep (se 2 (by rfl) ⟨1131138, by rfl⟩ : syracuseStep 3016369 = 2262277) B2262277
theorem B4021825 : Blo 2117435 4021825 := bstep (se 2 (by rfl) ⟨1508184, by rfl⟩ : syracuseStep 4021825 = 3016369) B3016369
theorem B5362433 : Blo 2117435 5362433 := bstep (se 2 (by rfl) ⟨2010912, by rfl⟩ : syracuseStep 5362433 = 4021825) B4021825
theorem B3574955 : Blo 2117435 3574955 := bstep (se 1 (by rfl) ⟨2681216, by rfl⟩ : syracuseStep 3574955 = 5362433) B5362433
theorem B2383303 : Blo 2117435 2383303 := bstep (se 1 (by rfl) ⟨1787477, by rfl⟩ : syracuseStep 2383303 = 3574955) B3574955
theorem B3177737 : Blo 2117435 3177737 := bstep (se 2 (by rfl) ⟨1191651, by rfl⟩ : syracuseStep 3177737 = 2383303) B2383303
theorem B2118491 : Blo 2117435 2118491 := bstep (se 1 (by rfl) ⟨1588868, by rfl⟩ : syracuseStep 2118491 = 3177737) B3177737
theorem B10724885 : Blo 2117435 10724885 := bbase (se 6 (by rfl) ⟨251364, by rfl⟩ : syracuseStep 10724885 = 502729) (by norm_num)
theorem B7149923 : Blo 2117435 7149923 := bstep (se 1 (by rfl) ⟨5362442, by rfl⟩ : syracuseStep 7149923 = 10724885) B10724885
theorem B4766615 : Blo 2117435 4766615 := bstep (se 1 (by rfl) ⟨3574961, by rfl⟩ : syracuseStep 4766615 = 7149923) B7149923
theorem B3177743 : Blo 2117435 3177743 := bstep (se 1 (by rfl) ⟨2383307, by rfl⟩ : syracuseStep 3177743 = 4766615) B4766615
theorem B2118495 : Blo 2117435 2118495 := bstep (se 1 (by rfl) ⟨1588871, by rfl⟩ : syracuseStep 2118495 = 3177743) B3177743
theorem B3177749 : Blo 2117435 3177749 := bbase (se 6 (by rfl) ⟨74478, by rfl⟩ : syracuseStep 3177749 = 148957) (by norm_num)
theorem B2118499 : Blo 2117435 2118499 := bstep (se 1 (by rfl) ⟨1588874, by rfl⟩ : syracuseStep 2118499 = 3177749) B3177749
theorem B7446613 : Blo 2117435 7446613 := bbase (se 8 (by rfl) ⟨43632, by rfl⟩ : syracuseStep 7446613 = 87265) (by norm_num)
theorem B9928817 : Blo 2117435 9928817 := bstep (se 2 (by rfl) ⟨3723306, by rfl⟩ : syracuseStep 9928817 = 7446613) B7446613
theorem B6619211 : Blo 2117435 6619211 := bstep (se 1 (by rfl) ⟨4964408, by rfl⟩ : syracuseStep 6619211 = 9928817) B9928817
theorem B4412807 : Blo 2117435 4412807 := bstep (se 1 (by rfl) ⟨3309605, by rfl⟩ : syracuseStep 4412807 = 6619211) B6619211
theorem B2941871 : Blo 2117435 2941871 := bstep (se 1 (by rfl) ⟨2206403, by rfl⟩ : syracuseStep 2941871 = 4412807) B4412807
theorem B7844989 : Blo 2117435 7844989 := bstep (se 3 (by rfl) ⟨1470935, by rfl⟩ : syracuseStep 7844989 = 2941871) B2941871
theorem B167359765 : Blo 2117435 167359765 := bstep (se 6 (by rfl) ⟨3922494, by rfl⟩ : syracuseStep 167359765 = 7844989) B7844989
theorem B223146353 : Blo 2117435 223146353 := bstep (se 2 (by rfl) ⟨83679882, by rfl⟩ : syracuseStep 223146353 = 167359765) B167359765
theorem B148764235 : Blo 2117435 148764235 := bstep (se 1 (by rfl) ⟨111573176, by rfl⟩ : syracuseStep 148764235 = 223146353) B223146353
theorem B198352313 : Blo 2117435 198352313 := bstep (se 2 (by rfl) ⟨74382117, by rfl⟩ : syracuseStep 198352313 = 148764235) B148764235
theorem B132234875 : Blo 2117435 132234875 := bstep (se 1 (by rfl) ⟨99176156, by rfl⟩ : syracuseStep 132234875 = 198352313) B198352313
theorem B88156583 : Blo 2117435 88156583 := bstep (se 1 (by rfl) ⟨66117437, by rfl⟩ : syracuseStep 88156583 = 132234875) B132234875
theorem B58771055 : Blo 2117435 58771055 := bstep (se 1 (by rfl) ⟨44078291, by rfl⟩ : syracuseStep 58771055 = 88156583) B88156583
theorem B156722813 : Blo 2117435 156722813 := bstep (se 3 (by rfl) ⟨29385527, by rfl⟩ : syracuseStep 156722813 = 58771055) B58771055
theorem B104481875 : Blo 2117435 104481875 := bstep (se 1 (by rfl) ⟨78361406, by rfl⟩ : syracuseStep 104481875 = 156722813) B156722813
theorem B69654583 : Blo 2117435 69654583 := bstep (se 1 (by rfl) ⟨52240937, by rfl⟩ : syracuseStep 69654583 = 104481875) B104481875
theorem B92872777 : Blo 2117435 92872777 := bstep (se 2 (by rfl) ⟨34827291, by rfl⟩ : syracuseStep 92872777 = 69654583) B69654583
theorem B123830369 : Blo 2117435 123830369 := bstep (se 2 (by rfl) ⟨46436388, by rfl⟩ : syracuseStep 123830369 = 92872777) B92872777
theorem B82553579 : Blo 2117435 82553579 := bstep (se 1 (by rfl) ⟨61915184, by rfl⟩ : syracuseStep 82553579 = 123830369) B123830369
theorem B55035719 : Blo 2117435 55035719 := bstep (se 1 (by rfl) ⟨41276789, by rfl⟩ : syracuseStep 55035719 = 82553579) B82553579
theorem B36690479 : Blo 2117435 36690479 := bstep (se 1 (by rfl) ⟨27517859, by rfl⟩ : syracuseStep 36690479 = 55035719) B55035719
theorem B24460319 : Blo 2117435 24460319 := bstep (se 1 (by rfl) ⟨18345239, by rfl⟩ : syracuseStep 24460319 = 36690479) B36690479
theorem B65227517 : Blo 2117435 65227517 := bstep (se 3 (by rfl) ⟨12230159, by rfl⟩ : syracuseStep 65227517 = 24460319) B24460319
theorem B43485011 : Blo 2117435 43485011 := bstep (se 1 (by rfl) ⟨32613758, by rfl⟩ : syracuseStep 43485011 = 65227517) B65227517
theorem B28990007 : Blo 2117435 28990007 := bstep (se 1 (by rfl) ⟨21742505, by rfl⟩ : syracuseStep 28990007 = 43485011) B43485011
theorem B19326671 : Blo 2117435 19326671 := bstep (se 1 (by rfl) ⟨14495003, by rfl⟩ : syracuseStep 19326671 = 28990007) B28990007
theorem B12884447 : Blo 2117435 12884447 := bstep (se 1 (by rfl) ⟨9663335, by rfl⟩ : syracuseStep 12884447 = 19326671) B19326671
theorem B8589631 : Blo 2117435 8589631 := bstep (se 1 (by rfl) ⟨6442223, by rfl⟩ : syracuseStep 8589631 = 12884447) B12884447
theorem B11452841 : Blo 2117435 11452841 := bstep (se 2 (by rfl) ⟨4294815, by rfl⟩ : syracuseStep 11452841 = 8589631) B8589631
theorem B7635227 : Blo 2117435 7635227 := bstep (se 1 (by rfl) ⟨5726420, by rfl⟩ : syracuseStep 7635227 = 11452841) B11452841
theorem B20360605 : Blo 2117435 20360605 := bstep (se 3 (by rfl) ⟨3817613, by rfl⟩ : syracuseStep 20360605 = 7635227) B7635227
theorem B27147473 : Blo 2117435 27147473 := bstep (se 2 (by rfl) ⟨10180302, by rfl⟩ : syracuseStep 27147473 = 20360605) B20360605
theorem B18098315 : Blo 2117435 18098315 := bstep (se 1 (by rfl) ⟨13573736, by rfl⟩ : syracuseStep 18098315 = 27147473) B27147473
theorem B12065543 : Blo 2117435 12065543 := bstep (se 1 (by rfl) ⟨9049157, by rfl⟩ : syracuseStep 12065543 = 18098315) B18098315
theorem B8043695 : Blo 2117435 8043695 := bstep (se 1 (by rfl) ⟨6032771, by rfl⟩ : syracuseStep 8043695 = 12065543) B12065543
theorem B5362463 : Blo 2117435 5362463 := bstep (se 1 (by rfl) ⟨4021847, by rfl⟩ : syracuseStep 5362463 = 8043695) B8043695
theorem B3574975 : Blo 2117435 3574975 := bstep (se 1 (by rfl) ⟨2681231, by rfl⟩ : syracuseStep 3574975 = 5362463) B5362463
theorem B4766633 : Blo 2117435 4766633 := bstep (se 2 (by rfl) ⟨1787487, by rfl⟩ : syracuseStep 4766633 = 3574975) B3574975
theorem B3177755 : Blo 2117435 3177755 := bstep (se 1 (by rfl) ⟨2383316, by rfl⟩ : syracuseStep 3177755 = 4766633) B4766633
theorem B2118503 : Blo 2117435 2118503 := bstep (se 1 (by rfl) ⟨1588877, by rfl⟩ : syracuseStep 2118503 = 3177755) B3177755
theorem B2383321 : Blo 2117435 2383321 := bbase (se 2 (by rfl) ⟨893745, by rfl⟩ : syracuseStep 2383321 = 1787491) (by norm_num)
theorem B3177761 : Blo 2117435 3177761 := bstep (se 2 (by rfl) ⟨1191660, by rfl⟩ : syracuseStep 3177761 = 2383321) B2383321
theorem B2118507 : Blo 2117435 2118507 := bstep (se 1 (by rfl) ⟨1588880, by rfl⟩ : syracuseStep 2118507 = 3177761) B3177761
theorem B3016397 : Blo 2117435 3016397 := bbase (se 3 (by rfl) ⟨565574, by rfl⟩ : syracuseStep 3016397 = 1131149) (by norm_num)
theorem B8043725 : Blo 2117435 8043725 := bstep (se 3 (by rfl) ⟨1508198, by rfl⟩ : syracuseStep 8043725 = 3016397) B3016397
theorem B5362483 : Blo 2117435 5362483 := bstep (se 1 (by rfl) ⟨4021862, by rfl⟩ : syracuseStep 5362483 = 8043725) B8043725
theorem B7149977 : Blo 2117435 7149977 := bstep (se 2 (by rfl) ⟨2681241, by rfl⟩ : syracuseStep 7149977 = 5362483) B5362483
theorem B4766651 : Blo 2117435 4766651 := bstep (se 1 (by rfl) ⟨3574988, by rfl⟩ : syracuseStep 4766651 = 7149977) B7149977
theorem B3177767 : Blo 2117435 3177767 := bstep (se 1 (by rfl) ⟨2383325, by rfl⟩ : syracuseStep 3177767 = 4766651) B4766651
theorem B2118511 : Blo 2117435 2118511 := bstep (se 1 (by rfl) ⟨1588883, by rfl⟩ : syracuseStep 2118511 = 3177767) B3177767
theorem B3177773 : Blo 2117435 3177773 := bbase (se 3 (by rfl) ⟨595832, by rfl⟩ : syracuseStep 3177773 = 1191665) (by norm_num)
theorem B2118515 : Blo 2117435 2118515 := bstep (se 1 (by rfl) ⟨1588886, by rfl⟩ : syracuseStep 2118515 = 3177773) B3177773
theorem B4766669 : Blo 2117435 4766669 := bbase (se 3 (by rfl) ⟨893750, by rfl⟩ : syracuseStep 4766669 = 1787501) (by norm_num)
theorem B3177779 : Blo 2117435 3177779 := bstep (se 1 (by rfl) ⟨2383334, by rfl⟩ : syracuseStep 3177779 = 4766669) B4766669
theorem B2118519 : Blo 2117435 2118519 := bstep (se 1 (by rfl) ⟨1588889, by rfl⟩ : syracuseStep 2118519 = 3177779) B3177779
theorem B2681257 : Blo 2117435 2681257 := bbase (se 2 (by rfl) ⟨1005471, by rfl⟩ : syracuseStep 2681257 = 2010943) (by norm_num)
theorem B3575009 : Blo 2117435 3575009 := bstep (se 2 (by rfl) ⟨1340628, by rfl⟩ : syracuseStep 3575009 = 2681257) B2681257
theorem B2383339 : Blo 2117435 2383339 := bstep (se 1 (by rfl) ⟨1787504, by rfl⟩ : syracuseStep 2383339 = 3575009) B3575009
theorem B3177785 : Blo 2117435 3177785 := bstep (se 2 (by rfl) ⟨1191669, by rfl⟩ : syracuseStep 3177785 = 2383339) B2383339
theorem B2118523 : Blo 2117435 2118523 := bstep (se 1 (by rfl) ⟨1588892, by rfl⟩ : syracuseStep 2118523 = 3177785) B3177785
theorem B5726485 : Blo 2117435 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B7635313 : Blo 2117435 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B10180417 : Blo 2117435 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B13573889 : Blo 2117435 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B9049259 : Blo 2117435 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B24131357 : Blo 2117435 24131357 := bstep (se 3 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 24131357 = 9049259) B9049259
theorem B16087571 : Blo 2117435 16087571 := bstep (se 1 (by rfl) ⟨12065678, by rfl⟩ : syracuseStep 16087571 = 24131357) B24131357
theorem B10725047 : Blo 2117435 10725047 := bstep (se 1 (by rfl) ⟨8043785, by rfl⟩ : syracuseStep 10725047 = 16087571) B16087571
theorem B7150031 : Blo 2117435 7150031 := bstep (se 1 (by rfl) ⟨5362523, by rfl⟩ : syracuseStep 7150031 = 10725047) B10725047
theorem B4766687 : Blo 2117435 4766687 := bstep (se 1 (by rfl) ⟨3575015, by rfl⟩ : syracuseStep 4766687 = 7150031) B7150031
theorem B3177791 : Blo 2117435 3177791 := bstep (se 1 (by rfl) ⟨2383343, by rfl⟩ : syracuseStep 3177791 = 4766687) B4766687
theorem B2118527 : Blo 2117435 2118527 := bstep (se 1 (by rfl) ⟨1588895, by rfl⟩ : syracuseStep 2118527 = 3177791) B3177791
theorem B3177797 : Blo 2117435 3177797 := bbase (se 4 (by rfl) ⟨297918, by rfl⟩ : syracuseStep 3177797 = 595837) (by norm_num)
theorem B2118531 : Blo 2117435 2118531 := bstep (se 1 (by rfl) ⟨1588898, by rfl⟩ : syracuseStep 2118531 = 3177797) B3177797
theorem B3575029 : Blo 2117435 3575029 := bbase (se 5 (by rfl) ⟨167579, by rfl⟩ : syracuseStep 3575029 = 335159) (by norm_num)
theorem B4766705 : Blo 2117435 4766705 := bstep (se 2 (by rfl) ⟨1787514, by rfl⟩ : syracuseStep 4766705 = 3575029) B3575029
theorem B3177803 : Blo 2117435 3177803 := bstep (se 1 (by rfl) ⟨2383352, by rfl⟩ : syracuseStep 3177803 = 4766705) B4766705
theorem B2118535 : Blo 2117435 2118535 := bstep (se 1 (by rfl) ⟨1588901, by rfl⟩ : syracuseStep 2118535 = 3177803) B3177803
theorem B2383357 : Blo 2117435 2383357 := bbase (se 3 (by rfl) ⟨446879, by rfl⟩ : syracuseStep 2383357 = 893759) (by norm_num)
theorem B3177809 : Blo 2117435 3177809 := bstep (se 2 (by rfl) ⟨1191678, by rfl⟩ : syracuseStep 3177809 = 2383357) B2383357
theorem B2118539 : Blo 2117435 2118539 := bstep (se 1 (by rfl) ⟨1588904, by rfl⟩ : syracuseStep 2118539 = 3177809) B3177809
theorem B7150085 : Blo 2117435 7150085 := bbase (se 4 (by rfl) ⟨670320, by rfl⟩ : syracuseStep 7150085 = 1340641) (by norm_num)
theorem B4766723 : Blo 2117435 4766723 := bstep (se 1 (by rfl) ⟨3575042, by rfl⟩ : syracuseStep 4766723 = 7150085) B7150085
theorem B3177815 : Blo 2117435 3177815 := bstep (se 1 (by rfl) ⟨2383361, by rfl⟩ : syracuseStep 3177815 = 4766723) B4766723
theorem B2118543 : Blo 2117435 2118543 := bstep (se 1 (by rfl) ⟨1588907, by rfl⟩ : syracuseStep 2118543 = 3177815) B3177815
theorem B3177821 : Blo 2117435 3177821 := bbase (se 3 (by rfl) ⟨595841, by rfl⟩ : syracuseStep 3177821 = 1191683) (by norm_num)
theorem B2118547 : Blo 2117435 2118547 := bstep (se 1 (by rfl) ⟨1588910, by rfl⟩ : syracuseStep 2118547 = 3177821) B3177821
theorem B4766741 : Blo 2117435 4766741 := bbase (se 6 (by rfl) ⟨111720, by rfl⟩ : syracuseStep 4766741 = 223441) (by norm_num)
theorem B3177827 : Blo 2117435 3177827 := bstep (se 1 (by rfl) ⟨2383370, by rfl⟩ : syracuseStep 3177827 = 4766741) B4766741
theorem B2118551 : Blo 2117435 2118551 := bstep (se 1 (by rfl) ⟨1588913, by rfl⟩ : syracuseStep 2118551 = 3177827) B3177827
theorem B8043893 : Blo 2117435 8043893 := bbase (se 5 (by rfl) ⟨377057, by rfl⟩ : syracuseStep 8043893 = 754115) (by norm_num)
theorem B5362595 : Blo 2117435 5362595 := bstep (se 1 (by rfl) ⟨4021946, by rfl⟩ : syracuseStep 5362595 = 8043893) B8043893
theorem B3575063 : Blo 2117435 3575063 := bstep (se 1 (by rfl) ⟨2681297, by rfl⟩ : syracuseStep 3575063 = 5362595) B5362595
theorem B2383375 : Blo 2117435 2383375 := bstep (se 1 (by rfl) ⟨1787531, by rfl⟩ : syracuseStep 2383375 = 3575063) B3575063
theorem B3177833 : Blo 2117435 3177833 := bstep (se 2 (by rfl) ⟨1191687, by rfl⟩ : syracuseStep 3177833 = 2383375) B2383375
theorem B2118555 : Blo 2117435 2118555 := bstep (se 1 (by rfl) ⟨1588916, by rfl⟩ : syracuseStep 2118555 = 3177833) B3177833
theorem B2262349 : Blo 2117435 2262349 := bbase (se 3 (by rfl) ⟨424190, by rfl⟩ : syracuseStep 2262349 = 848381) (by norm_num)
theorem B12065861 : Blo 2117435 12065861 := bstep (se 4 (by rfl) ⟨1131174, by rfl⟩ : syracuseStep 12065861 = 2262349) B2262349
theorem B8043907 : Blo 2117435 8043907 := bstep (se 1 (by rfl) ⟨6032930, by rfl⟩ : syracuseStep 8043907 = 12065861) B12065861
theorem B10725209 : Blo 2117435 10725209 := bstep (se 2 (by rfl) ⟨4021953, by rfl⟩ : syracuseStep 10725209 = 8043907) B8043907
theorem B7150139 : Blo 2117435 7150139 := bstep (se 1 (by rfl) ⟨5362604, by rfl⟩ : syracuseStep 7150139 = 10725209) B10725209
theorem B4766759 : Blo 2117435 4766759 := bstep (se 1 (by rfl) ⟨3575069, by rfl⟩ : syracuseStep 4766759 = 7150139) B7150139
theorem B3177839 : Blo 2117435 3177839 := bstep (se 1 (by rfl) ⟨2383379, by rfl⟩ : syracuseStep 3177839 = 4766759) B4766759
theorem B2118559 : Blo 2117435 2118559 := bstep (se 1 (by rfl) ⟨1588919, by rfl⟩ : syracuseStep 2118559 = 3177839) B3177839
theorem B3177845 : Blo 2117435 3177845 := bbase (se 5 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 3177845 = 297923) (by norm_num)
theorem B2118563 : Blo 2117435 2118563 := bstep (se 1 (by rfl) ⟨1588922, by rfl⟩ : syracuseStep 2118563 = 3177845) B3177845
theorem B3016477 : Blo 2117435 3016477 := bbase (se 3 (by rfl) ⟨565589, by rfl⟩ : syracuseStep 3016477 = 1131179) (by norm_num)
theorem B4021969 : Blo 2117435 4021969 := bstep (se 2 (by rfl) ⟨1508238, by rfl⟩ : syracuseStep 4021969 = 3016477) B3016477
theorem B5362625 : Blo 2117435 5362625 := bstep (se 2 (by rfl) ⟨2010984, by rfl⟩ : syracuseStep 5362625 = 4021969) B4021969
theorem B3575083 : Blo 2117435 3575083 := bstep (se 1 (by rfl) ⟨2681312, by rfl⟩ : syracuseStep 3575083 = 5362625) B5362625
theorem B4766777 : Blo 2117435 4766777 := bstep (se 2 (by rfl) ⟨1787541, by rfl⟩ : syracuseStep 4766777 = 3575083) B3575083
theorem B3177851 : Blo 2117435 3177851 := bstep (se 1 (by rfl) ⟨2383388, by rfl⟩ : syracuseStep 3177851 = 4766777) B4766777
theorem B2118567 : Blo 2117435 2118567 := bstep (se 1 (by rfl) ⟨1588925, by rfl⟩ : syracuseStep 2118567 = 3177851) B3177851
theorem B2383393 : Blo 2117435 2383393 := bbase (se 2 (by rfl) ⟨893772, by rfl⟩ : syracuseStep 2383393 = 1787545) (by norm_num)
theorem B3177857 : Blo 2117435 3177857 := bstep (se 2 (by rfl) ⟨1191696, by rfl⟩ : syracuseStep 3177857 = 2383393) B2383393
theorem B2118571 : Blo 2117435 2118571 := bstep (se 1 (by rfl) ⟨1588928, by rfl⟩ : syracuseStep 2118571 = 3177857) B3177857
theorem B5362645 : Blo 2117435 5362645 := bbase (se 7 (by rfl) ⟨62843, by rfl⟩ : syracuseStep 5362645 = 125687) (by norm_num)
theorem B7150193 : Blo 2117435 7150193 := bstep (se 2 (by rfl) ⟨2681322, by rfl⟩ : syracuseStep 7150193 = 5362645) B5362645
theorem B4766795 : Blo 2117435 4766795 := bstep (se 1 (by rfl) ⟨3575096, by rfl⟩ : syracuseStep 4766795 = 7150193) B7150193
theorem B3177863 : Blo 2117435 3177863 := bstep (se 1 (by rfl) ⟨2383397, by rfl⟩ : syracuseStep 3177863 = 4766795) B4766795
theorem B2118575 : Blo 2117435 2118575 := bstep (se 1 (by rfl) ⟨1588931, by rfl⟩ : syracuseStep 2118575 = 3177863) B3177863
theorem B3177869 : Blo 2117435 3177869 := bbase (se 3 (by rfl) ⟨595850, by rfl⟩ : syracuseStep 3177869 = 1191701) (by norm_num)
theorem B2118579 : Blo 2117435 2118579 := bstep (se 1 (by rfl) ⟨1588934, by rfl⟩ : syracuseStep 2118579 = 3177869) B3177869
theorem B4766813 : Blo 2117435 4766813 := bbase (se 3 (by rfl) ⟨893777, by rfl⟩ : syracuseStep 4766813 = 1787555) (by norm_num)
theorem B3177875 : Blo 2117435 3177875 := bstep (se 1 (by rfl) ⟨2383406, by rfl⟩ : syracuseStep 3177875 = 4766813) B4766813
theorem B2118583 : Blo 2117435 2118583 := bstep (se 1 (by rfl) ⟨1588937, by rfl⟩ : syracuseStep 2118583 = 3177875) B3177875
theorem B3575117 : Blo 2117435 3575117 := bbase (se 3 (by rfl) ⟨670334, by rfl⟩ : syracuseStep 3575117 = 1340669) (by norm_num)
theorem B2383411 : Blo 2117435 2383411 := bstep (se 1 (by rfl) ⟨1787558, by rfl⟩ : syracuseStep 2383411 = 3575117) B3575117
theorem B3177881 : Blo 2117435 3177881 := bstep (se 2 (by rfl) ⟨1191705, by rfl⟩ : syracuseStep 3177881 = 2383411) B2383411
theorem B2118587 : Blo 2117435 2118587 := bstep (se 1 (by rfl) ⟨1588940, by rfl⟩ : syracuseStep 2118587 = 3177881) B3177881
theorem B6115333 : Blo 2117435 6115333 := bbase (se 4 (by rfl) ⟨573312, by rfl⟩ : syracuseStep 6115333 = 1146625) (by norm_num)
theorem B8153777 : Blo 2117435 8153777 := bstep (se 2 (by rfl) ⟨3057666, by rfl⟩ : syracuseStep 8153777 = 6115333) B6115333
theorem B21743405 : Blo 2117435 21743405 := bstep (se 3 (by rfl) ⟨4076888, by rfl⟩ : syracuseStep 21743405 = 8153777) B8153777
theorem B14495603 : Blo 2117435 14495603 := bstep (se 1 (by rfl) ⟨10871702, by rfl⟩ : syracuseStep 14495603 = 21743405) B21743405
theorem B38654941 : Blo 2117435 38654941 := bstep (se 3 (by rfl) ⟨7247801, by rfl⟩ : syracuseStep 38654941 = 14495603) B14495603
theorem B51539921 : Blo 2117435 51539921 := bstep (se 2 (by rfl) ⟨19327470, by rfl⟩ : syracuseStep 51539921 = 38654941) B38654941
theorem B34359947 : Blo 2117435 34359947 := bstep (se 1 (by rfl) ⟨25769960, by rfl⟩ : syracuseStep 34359947 = 51539921) B51539921
theorem B22906631 : Blo 2117435 22906631 := bstep (se 1 (by rfl) ⟨17179973, by rfl⟩ : syracuseStep 22906631 = 34359947) B34359947
theorem B15271087 : Blo 2117435 15271087 := bstep (se 1 (by rfl) ⟨11453315, by rfl⟩ : syracuseStep 15271087 = 22906631) B22906631
theorem B20361449 : Blo 2117435 20361449 := bstep (se 2 (by rfl) ⟨7635543, by rfl⟩ : syracuseStep 20361449 = 15271087) B15271087
theorem B13574299 : Blo 2117435 13574299 := bstep (se 1 (by rfl) ⟨10180724, by rfl⟩ : syracuseStep 13574299 = 20361449) B20361449
theorem B18099065 : Blo 2117435 18099065 := bstep (se 2 (by rfl) ⟨6787149, by rfl⟩ : syracuseStep 18099065 = 13574299) B13574299
theorem B12066043 : Blo 2117435 12066043 := bstep (se 1 (by rfl) ⟨9049532, by rfl⟩ : syracuseStep 12066043 = 18099065) B18099065
theorem B16088057 : Blo 2117435 16088057 := bstep (se 2 (by rfl) ⟨6033021, by rfl⟩ : syracuseStep 16088057 = 12066043) B12066043
theorem B10725371 : Blo 2117435 10725371 := bstep (se 1 (by rfl) ⟨8044028, by rfl⟩ : syracuseStep 10725371 = 16088057) B16088057
theorem B7150247 : Blo 2117435 7150247 := bstep (se 1 (by rfl) ⟨5362685, by rfl⟩ : syracuseStep 7150247 = 10725371) B10725371
theorem B4766831 : Blo 2117435 4766831 := bstep (se 1 (by rfl) ⟨3575123, by rfl⟩ : syracuseStep 4766831 = 7150247) B7150247
theorem B3177887 : Blo 2117435 3177887 := bstep (se 1 (by rfl) ⟨2383415, by rfl⟩ : syracuseStep 3177887 = 4766831) B4766831
theorem B2118591 : Blo 2117435 2118591 := bstep (se 1 (by rfl) ⟨1588943, by rfl⟩ : syracuseStep 2118591 = 3177887) B3177887
theorem B3177893 : Blo 2117435 3177893 := bbase (se 4 (by rfl) ⟨297927, by rfl⟩ : syracuseStep 3177893 = 595855) (by norm_num)
theorem B2118595 : Blo 2117435 2118595 := bstep (se 1 (by rfl) ⟨1588946, by rfl⟩ : syracuseStep 2118595 = 3177893) B3177893
theorem B2681353 : Blo 2117435 2681353 := bbase (se 2 (by rfl) ⟨1005507, by rfl⟩ : syracuseStep 2681353 = 2011015) (by norm_num)
theorem B3575137 : Blo 2117435 3575137 := bstep (se 2 (by rfl) ⟨1340676, by rfl⟩ : syracuseStep 3575137 = 2681353) B2681353
theorem B4766849 : Blo 2117435 4766849 := bstep (se 2 (by rfl) ⟨1787568, by rfl⟩ : syracuseStep 4766849 = 3575137) B3575137
theorem B3177899 : Blo 2117435 3177899 := bstep (se 1 (by rfl) ⟨2383424, by rfl⟩ : syracuseStep 3177899 = 4766849) B4766849
theorem B2118599 : Blo 2117435 2118599 := bstep (se 1 (by rfl) ⟨1588949, by rfl⟩ : syracuseStep 2118599 = 3177899) B3177899
theorem B2383429 : Blo 2117435 2383429 := bbase (se 4 (by rfl) ⟨223446, by rfl⟩ : syracuseStep 2383429 = 446893) (by norm_num)
theorem B3177905 : Blo 2117435 3177905 := bstep (se 2 (by rfl) ⟨1191714, by rfl⟩ : syracuseStep 3177905 = 2383429) B2383429
theorem B2118603 : Blo 2117435 2118603 := bstep (se 1 (by rfl) ⟨1588952, by rfl⟩ : syracuseStep 2118603 = 3177905) B3177905
theorem B4022045 : Blo 2117435 4022045 := bbase (se 3 (by rfl) ⟨754133, by rfl⟩ : syracuseStep 4022045 = 1508267) (by norm_num)
theorem B2681363 : Blo 2117435 2681363 := bstep (se 1 (by rfl) ⟨2011022, by rfl⟩ : syracuseStep 2681363 = 4022045) B4022045
theorem B7150301 : Blo 2117435 7150301 := bstep (se 3 (by rfl) ⟨1340681, by rfl⟩ : syracuseStep 7150301 = 2681363) B2681363
theorem B4766867 : Blo 2117435 4766867 := bstep (se 1 (by rfl) ⟨3575150, by rfl⟩ : syracuseStep 4766867 = 7150301) B7150301
theorem B3177911 : Blo 2117435 3177911 := bstep (se 1 (by rfl) ⟨2383433, by rfl⟩ : syracuseStep 3177911 = 4766867) B4766867
theorem B2118607 : Blo 2117435 2118607 := bstep (se 1 (by rfl) ⟨1588955, by rfl⟩ : syracuseStep 2118607 = 3177911) B3177911
theorem B3177917 : Blo 2117435 3177917 := bbase (se 3 (by rfl) ⟨595859, by rfl⟩ : syracuseStep 3177917 = 1191719) (by norm_num)
theorem B2118611 : Blo 2117435 2118611 := bstep (se 1 (by rfl) ⟨1588958, by rfl⟩ : syracuseStep 2118611 = 3177917) B3177917
theorem B4766885 : Blo 2117435 4766885 := bbase (se 4 (by rfl) ⟨446895, by rfl⟩ : syracuseStep 4766885 = 893791) (by norm_num)
theorem B3177923 : Blo 2117435 3177923 := bstep (se 1 (by rfl) ⟨2383442, by rfl⟩ : syracuseStep 3177923 = 4766885) B4766885
theorem B2118615 : Blo 2117435 2118615 := bstep (se 1 (by rfl) ⟨1588961, by rfl⟩ : syracuseStep 2118615 = 3177923) B3177923
theorem B5362757 : Blo 2117435 5362757 := bbase (se 4 (by rfl) ⟨502758, by rfl⟩ : syracuseStep 5362757 = 1005517) (by norm_num)
theorem B3575171 : Blo 2117435 3575171 := bstep (se 1 (by rfl) ⟨2681378, by rfl⟩ : syracuseStep 3575171 = 5362757) B5362757
theorem B2383447 : Blo 2117435 2383447 := bstep (se 1 (by rfl) ⟨1787585, by rfl⟩ : syracuseStep 2383447 = 3575171) B3575171
theorem B3177929 : Blo 2117435 3177929 := bstep (se 2 (by rfl) ⟨1191723, by rfl⟩ : syracuseStep 3177929 = 2383447) B2383447
theorem B2118619 : Blo 2117435 2118619 := bstep (se 1 (by rfl) ⟨1588964, by rfl⟩ : syracuseStep 2118619 = 3177929) B3177929
theorem B6787253 : Blo 2117435 6787253 := bbase (se 5 (by rfl) ⟨318152, by rfl⟩ : syracuseStep 6787253 = 636305) (by norm_num)
theorem B4524835 : Blo 2117435 4524835 := bstep (se 1 (by rfl) ⟨3393626, by rfl⟩ : syracuseStep 4524835 = 6787253) B6787253
theorem B6033113 : Blo 2117435 6033113 := bstep (se 2 (by rfl) ⟨2262417, by rfl⟩ : syracuseStep 6033113 = 4524835) B4524835
theorem B4022075 : Blo 2117435 4022075 := bstep (se 1 (by rfl) ⟨3016556, by rfl⟩ : syracuseStep 4022075 = 6033113) B6033113
theorem B10725533 : Blo 2117435 10725533 := bstep (se 3 (by rfl) ⟨2011037, by rfl⟩ : syracuseStep 10725533 = 4022075) B4022075
theorem B7150355 : Blo 2117435 7150355 := bstep (se 1 (by rfl) ⟨5362766, by rfl⟩ : syracuseStep 7150355 = 10725533) B10725533
theorem B4766903 : Blo 2117435 4766903 := bstep (se 1 (by rfl) ⟨3575177, by rfl⟩ : syracuseStep 4766903 = 7150355) B7150355
theorem B3177935 : Blo 2117435 3177935 := bstep (se 1 (by rfl) ⟨2383451, by rfl⟩ : syracuseStep 3177935 = 4766903) B4766903
theorem B2118623 : Blo 2117435 2118623 := bstep (se 1 (by rfl) ⟨1588967, by rfl⟩ : syracuseStep 2118623 = 3177935) B3177935
theorem B3177941 : Blo 2117435 3177941 := bbase (se 7 (by rfl) ⟨37241, by rfl⟩ : syracuseStep 3177941 = 74483) (by norm_num)
theorem B2118627 : Blo 2117435 2118627 := bstep (se 1 (by rfl) ⟨1588970, by rfl⟩ : syracuseStep 2118627 = 3177941) B3177941
theorem B8044181 : Blo 2117435 8044181 := bbase (se 6 (by rfl) ⟨188535, by rfl⟩ : syracuseStep 8044181 = 377071) (by norm_num)
theorem B5362787 : Blo 2117435 5362787 := bstep (se 1 (by rfl) ⟨4022090, by rfl⟩ : syracuseStep 5362787 = 8044181) B8044181
theorem B3575191 : Blo 2117435 3575191 := bstep (se 1 (by rfl) ⟨2681393, by rfl⟩ : syracuseStep 3575191 = 5362787) B5362787
theorem B4766921 : Blo 2117435 4766921 := bstep (se 2 (by rfl) ⟨1787595, by rfl⟩ : syracuseStep 4766921 = 3575191) B3575191
theorem B3177947 : Blo 2117435 3177947 := bstep (se 1 (by rfl) ⟨2383460, by rfl⟩ : syracuseStep 3177947 = 4766921) B4766921
theorem B2118631 : Blo 2117435 2118631 := bstep (se 1 (by rfl) ⟨1588973, by rfl⟩ : syracuseStep 2118631 = 3177947) B3177947
theorem B2383465 : Blo 2117435 2383465 := bbase (se 2 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 2383465 = 1787599) (by norm_num)
theorem B3177953 : Blo 2117435 3177953 := bstep (se 2 (by rfl) ⟨1191732, by rfl⟩ : syracuseStep 3177953 = 2383465) B2383465
theorem B2118635 : Blo 2117435 2118635 := bstep (se 1 (by rfl) ⟨1588976, by rfl⟩ : syracuseStep 2118635 = 3177953) B3177953
theorem B4524869 : Blo 2117435 4524869 := bbase (se 4 (by rfl) ⟨424206, by rfl⟩ : syracuseStep 4524869 = 848413) (by norm_num)
theorem B12066317 : Blo 2117435 12066317 := bstep (se 3 (by rfl) ⟨2262434, by rfl⟩ : syracuseStep 12066317 = 4524869) B4524869
theorem B8044211 : Blo 2117435 8044211 := bstep (se 1 (by rfl) ⟨6033158, by rfl⟩ : syracuseStep 8044211 = 12066317) B12066317
theorem B5362807 : Blo 2117435 5362807 := bstep (se 1 (by rfl) ⟨4022105, by rfl⟩ : syracuseStep 5362807 = 8044211) B8044211
theorem B7150409 : Blo 2117435 7150409 := bstep (se 2 (by rfl) ⟨2681403, by rfl⟩ : syracuseStep 7150409 = 5362807) B5362807
theorem B4766939 : Blo 2117435 4766939 := bstep (se 1 (by rfl) ⟨3575204, by rfl⟩ : syracuseStep 4766939 = 7150409) B7150409
theorem B3177959 : Blo 2117435 3177959 := bstep (se 1 (by rfl) ⟨2383469, by rfl⟩ : syracuseStep 3177959 = 4766939) B4766939
theorem B2118639 : Blo 2117435 2118639 := bstep (se 1 (by rfl) ⟨1588979, by rfl⟩ : syracuseStep 2118639 = 3177959) B3177959
theorem B3177965 : Blo 2117435 3177965 := bbase (se 3 (by rfl) ⟨595868, by rfl⟩ : syracuseStep 3177965 = 1191737) (by norm_num)
theorem B2118643 : Blo 2117435 2118643 := bstep (se 1 (by rfl) ⟨1588982, by rfl⟩ : syracuseStep 2118643 = 3177965) B3177965
theorem B4766957 : Blo 2117435 4766957 := bbase (se 3 (by rfl) ⟨893804, by rfl⟩ : syracuseStep 4766957 = 1787609) (by norm_num)
theorem B3177971 : Blo 2117435 3177971 := bstep (se 1 (by rfl) ⟨2383478, by rfl⟩ : syracuseStep 3177971 = 4766957) B4766957
theorem B2118647 : Blo 2117435 2118647 := bstep (se 1 (by rfl) ⟨1588985, by rfl⟩ : syracuseStep 2118647 = 3177971) B3177971
theorem B3016597 : Blo 2117435 3016597 := bbase (se 6 (by rfl) ⟨70701, by rfl⟩ : syracuseStep 3016597 = 141403) (by norm_num)
theorem B4022129 : Blo 2117435 4022129 := bstep (se 2 (by rfl) ⟨1508298, by rfl⟩ : syracuseStep 4022129 = 3016597) B3016597
theorem B2681419 : Blo 2117435 2681419 := bstep (se 1 (by rfl) ⟨2011064, by rfl⟩ : syracuseStep 2681419 = 4022129) B4022129
theorem B3575225 : Blo 2117435 3575225 := bstep (se 2 (by rfl) ⟨1340709, by rfl⟩ : syracuseStep 3575225 = 2681419) B2681419
theorem B2383483 : Blo 2117435 2383483 := bstep (se 1 (by rfl) ⟨1787612, by rfl⟩ : syracuseStep 2383483 = 3575225) B3575225
theorem B3177977 : Blo 2117435 3177977 := bstep (se 2 (by rfl) ⟨1191741, by rfl⟩ : syracuseStep 3177977 = 2383483) B2383483
theorem B2118651 : Blo 2117435 2118651 := bstep (se 1 (by rfl) ⟨1588988, by rfl⟩ : syracuseStep 2118651 = 3177977) B3177977
theorem B19328053 : Blo 2117435 19328053 := bbase (se 5 (by rfl) ⟨906002, by rfl⟩ : syracuseStep 19328053 = 1812005) (by norm_num)
theorem B25770737 : Blo 2117435 25770737 := bstep (se 2 (by rfl) ⟨9664026, by rfl⟩ : syracuseStep 25770737 = 19328053) B19328053
theorem B68721965 : Blo 2117435 68721965 := bstep (se 3 (by rfl) ⟨12885368, by rfl⟩ : syracuseStep 68721965 = 25770737) B25770737
theorem B45814643 : Blo 2117435 45814643 := bstep (se 1 (by rfl) ⟨34360982, by rfl⟩ : syracuseStep 45814643 = 68721965) B68721965
theorem B30543095 : Blo 2117435 30543095 := bstep (se 1 (by rfl) ⟨22907321, by rfl⟩ : syracuseStep 30543095 = 45814643) B45814643
theorem B81448253 : Blo 2117435 81448253 := bstep (se 3 (by rfl) ⟨15271547, by rfl⟩ : syracuseStep 81448253 = 30543095) B30543095
theorem B54298835 : Blo 2117435 54298835 := bstep (se 1 (by rfl) ⟨40724126, by rfl⟩ : syracuseStep 54298835 = 81448253) B81448253
theorem B36199223 : Blo 2117435 36199223 := bstep (se 1 (by rfl) ⟨27149417, by rfl⟩ : syracuseStep 36199223 = 54298835) B54298835
theorem B24132815 : Blo 2117435 24132815 := bstep (se 1 (by rfl) ⟨18099611, by rfl⟩ : syracuseStep 24132815 = 36199223) B36199223
theorem B16088543 : Blo 2117435 16088543 := bstep (se 1 (by rfl) ⟨12066407, by rfl⟩ : syracuseStep 16088543 = 24132815) B24132815
theorem B10725695 : Blo 2117435 10725695 := bstep (se 1 (by rfl) ⟨8044271, by rfl⟩ : syracuseStep 10725695 = 16088543) B16088543
theorem B7150463 : Blo 2117435 7150463 := bstep (se 1 (by rfl) ⟨5362847, by rfl⟩ : syracuseStep 7150463 = 10725695) B10725695
theorem B4766975 : Blo 2117435 4766975 := bstep (se 1 (by rfl) ⟨3575231, by rfl⟩ : syracuseStep 4766975 = 7150463) B7150463
theorem B3177983 : Blo 2117435 3177983 := bstep (se 1 (by rfl) ⟨2383487, by rfl⟩ : syracuseStep 3177983 = 4766975) B4766975
theorem B2118655 : Blo 2117435 2118655 := bstep (se 1 (by rfl) ⟨1588991, by rfl⟩ : syracuseStep 2118655 = 3177983) B3177983
theorem B3177989 : Blo 2117435 3177989 := bbase (se 4 (by rfl) ⟨297936, by rfl⟩ : syracuseStep 3177989 = 595873) (by norm_num)
theorem B2118659 : Blo 2117435 2118659 := bstep (se 1 (by rfl) ⟨1588994, by rfl⟩ : syracuseStep 2118659 = 3177989) B3177989
theorem B3575245 : Blo 2117435 3575245 := bbase (se 3 (by rfl) ⟨670358, by rfl⟩ : syracuseStep 3575245 = 1340717) (by norm_num)
theorem B4766993 : Blo 2117435 4766993 := bstep (se 2 (by rfl) ⟨1787622, by rfl⟩ : syracuseStep 4766993 = 3575245) B3575245
theorem B3177995 : Blo 2117435 3177995 := bstep (se 1 (by rfl) ⟨2383496, by rfl⟩ : syracuseStep 3177995 = 4766993) B4766993
theorem B2118663 : Blo 2117435 2118663 := bstep (se 1 (by rfl) ⟨1588997, by rfl⟩ : syracuseStep 2118663 = 3177995) B3177995
theorem B2383501 : Blo 2117435 2383501 := bbase (se 3 (by rfl) ⟨446906, by rfl⟩ : syracuseStep 2383501 = 893813) (by norm_num)
theorem B3178001 : Blo 2117435 3178001 := bstep (se 2 (by rfl) ⟨1191750, by rfl⟩ : syracuseStep 3178001 = 2383501) B2383501
theorem B2118667 : Blo 2117435 2118667 := bstep (se 1 (by rfl) ⟨1589000, by rfl⟩ : syracuseStep 2118667 = 3178001) B3178001
theorem B7150517 : Blo 2117435 7150517 := bbase (se 5 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 7150517 = 670361) (by norm_num)
theorem B4767011 : Blo 2117435 4767011 := bstep (se 1 (by rfl) ⟨3575258, by rfl⟩ : syracuseStep 4767011 = 7150517) B7150517
theorem B3178007 : Blo 2117435 3178007 := bstep (se 1 (by rfl) ⟨2383505, by rfl⟩ : syracuseStep 3178007 = 4767011) B4767011
theorem B2118671 : Blo 2117435 2118671 := bstep (se 1 (by rfl) ⟨1589003, by rfl⟩ : syracuseStep 2118671 = 3178007) B3178007
theorem B3178013 : Blo 2117435 3178013 := bbase (se 3 (by rfl) ⟨595877, by rfl⟩ : syracuseStep 3178013 = 1191755) (by norm_num)
theorem B2118675 : Blo 2117435 2118675 := bstep (se 1 (by rfl) ⟨1589006, by rfl⟩ : syracuseStep 2118675 = 3178013) B3178013
theorem B4767029 : Blo 2117435 4767029 := bbase (se 5 (by rfl) ⟨223454, by rfl⟩ : syracuseStep 4767029 = 446909) (by norm_num)
theorem B3178019 : Blo 2117435 3178019 := bstep (se 1 (by rfl) ⟨2383514, by rfl⟩ : syracuseStep 3178019 = 4767029) B4767029
theorem B2118679 : Blo 2117435 2118679 := bstep (se 1 (by rfl) ⟨1589009, by rfl⟩ : syracuseStep 2118679 = 3178019) B3178019
theorem B4586701 : Blo 2117435 4586701 := bbase (se 3 (by rfl) ⟨860006, by rfl⟩ : syracuseStep 4586701 = 1720013) (by norm_num)
theorem B6115601 : Blo 2117435 6115601 := bstep (se 2 (by rfl) ⟨2293350, by rfl⟩ : syracuseStep 6115601 = 4586701) B4586701
theorem B4077067 : Blo 2117435 4077067 := bstep (se 1 (by rfl) ⟨3057800, by rfl⟩ : syracuseStep 4077067 = 6115601) B6115601
theorem B5436089 : Blo 2117435 5436089 := bstep (se 2 (by rfl) ⟨2038533, by rfl⟩ : syracuseStep 5436089 = 4077067) B4077067
theorem B3624059 : Blo 2117435 3624059 := bstep (se 1 (by rfl) ⟨2718044, by rfl⟩ : syracuseStep 3624059 = 5436089) B5436089
theorem B9664157 : Blo 2117435 9664157 := bstep (se 3 (by rfl) ⟨1812029, by rfl⟩ : syracuseStep 9664157 = 3624059) B3624059
theorem B25771085 : Blo 2117435 25771085 := bstep (se 3 (by rfl) ⟨4832078, by rfl⟩ : syracuseStep 25771085 = 9664157) B9664157
theorem B17180723 : Blo 2117435 17180723 := bstep (se 1 (by rfl) ⟨12885542, by rfl⟩ : syracuseStep 17180723 = 25771085) B25771085
theorem B11453815 : Blo 2117435 11453815 := bstep (se 1 (by rfl) ⟨8590361, by rfl⟩ : syracuseStep 11453815 = 17180723) B17180723
theorem B15271753 : Blo 2117435 15271753 := bstep (se 2 (by rfl) ⟨5726907, by rfl⟩ : syracuseStep 15271753 = 11453815) B11453815
theorem B20362337 : Blo 2117435 20362337 := bstep (se 2 (by rfl) ⟨7635876, by rfl⟩ : syracuseStep 20362337 = 15271753) B15271753
theorem B13574891 : Blo 2117435 13574891 := bstep (se 1 (by rfl) ⟨10181168, by rfl⟩ : syracuseStep 13574891 = 20362337) B20362337
theorem B9049927 : Blo 2117435 9049927 := bstep (se 1 (by rfl) ⟨6787445, by rfl⟩ : syracuseStep 9049927 = 13574891) B13574891
theorem B12066569 : Blo 2117435 12066569 := bstep (se 2 (by rfl) ⟨4524963, by rfl⟩ : syracuseStep 12066569 = 9049927) B9049927
theorem B8044379 : Blo 2117435 8044379 := bstep (se 1 (by rfl) ⟨6033284, by rfl⟩ : syracuseStep 8044379 = 12066569) B12066569
theorem B5362919 : Blo 2117435 5362919 := bstep (se 1 (by rfl) ⟨4022189, by rfl⟩ : syracuseStep 5362919 = 8044379) B8044379
theorem B3575279 : Blo 2117435 3575279 := bstep (se 1 (by rfl) ⟨2681459, by rfl⟩ : syracuseStep 3575279 = 5362919) B5362919
theorem B2383519 : Blo 2117435 2383519 := bstep (se 1 (by rfl) ⟨1787639, by rfl⟩ : syracuseStep 2383519 = 3575279) B3575279
theorem B3178025 : Blo 2117435 3178025 := bstep (se 2 (by rfl) ⟨1191759, by rfl⟩ : syracuseStep 3178025 = 2383519) B2383519
theorem B2118683 : Blo 2117435 2118683 := bstep (se 1 (by rfl) ⟨1589012, by rfl⟩ : syracuseStep 2118683 = 3178025) B3178025
theorem B4295189 : Blo 2117435 4295189 := bbase (se 6 (by rfl) ⟨100668, by rfl⟩ : syracuseStep 4295189 = 201337) (by norm_num)
theorem B2863459 : Blo 2117435 2863459 := bstep (se 1 (by rfl) ⟨2147594, by rfl⟩ : syracuseStep 2863459 = 4295189) B4295189
theorem B3817945 : Blo 2117435 3817945 := bstep (se 2 (by rfl) ⟨1431729, by rfl⟩ : syracuseStep 3817945 = 2863459) B2863459
theorem B20362373 : Blo 2117435 20362373 := bstep (se 4 (by rfl) ⟨1908972, by rfl⟩ : syracuseStep 20362373 = 3817945) B3817945
theorem B13574915 : Blo 2117435 13574915 := bstep (se 1 (by rfl) ⟨10181186, by rfl⟩ : syracuseStep 13574915 = 20362373) B20362373
theorem B9049943 : Blo 2117435 9049943 := bstep (se 1 (by rfl) ⟨6787457, by rfl⟩ : syracuseStep 9049943 = 13574915) B13574915
theorem B6033295 : Blo 2117435 6033295 := bstep (se 1 (by rfl) ⟨4524971, by rfl⟩ : syracuseStep 6033295 = 9049943) B9049943
theorem B8044393 : Blo 2117435 8044393 := bstep (se 2 (by rfl) ⟨3016647, by rfl⟩ : syracuseStep 8044393 = 6033295) B6033295
theorem B10725857 : Blo 2117435 10725857 := bstep (se 2 (by rfl) ⟨4022196, by rfl⟩ : syracuseStep 10725857 = 8044393) B8044393
theorem B7150571 : Blo 2117435 7150571 := bstep (se 1 (by rfl) ⟨5362928, by rfl⟩ : syracuseStep 7150571 = 10725857) B10725857
theorem B4767047 : Blo 2117435 4767047 := bstep (se 1 (by rfl) ⟨3575285, by rfl⟩ : syracuseStep 4767047 = 7150571) B7150571
theorem B3178031 : Blo 2117435 3178031 := bstep (se 1 (by rfl) ⟨2383523, by rfl⟩ : syracuseStep 3178031 = 4767047) B4767047
theorem B2118687 : Blo 2117435 2118687 := bstep (se 1 (by rfl) ⟨1589015, by rfl⟩ : syracuseStep 2118687 = 3178031) B3178031
theorem B3178037 : Blo 2117435 3178037 := bbase (se 5 (by rfl) ⟨148970, by rfl⟩ : syracuseStep 3178037 = 297941) (by norm_num)
theorem B2118691 : Blo 2117435 2118691 := bstep (se 1 (by rfl) ⟨1589018, by rfl⟩ : syracuseStep 2118691 = 3178037) B3178037
theorem B5362949 : Blo 2117435 5362949 := bbase (se 4 (by rfl) ⟨502776, by rfl⟩ : syracuseStep 5362949 = 1005553) (by norm_num)
theorem B3575299 : Blo 2117435 3575299 := bstep (se 1 (by rfl) ⟨2681474, by rfl⟩ : syracuseStep 3575299 = 5362949) B5362949
theorem B4767065 : Blo 2117435 4767065 := bstep (se 2 (by rfl) ⟨1787649, by rfl⟩ : syracuseStep 4767065 = 3575299) B3575299
theorem B3178043 : Blo 2117435 3178043 := bstep (se 1 (by rfl) ⟨2383532, by rfl⟩ : syracuseStep 3178043 = 4767065) B4767065
theorem B2118695 : Blo 2117435 2118695 := bstep (se 1 (by rfl) ⟨1589021, by rfl⟩ : syracuseStep 2118695 = 3178043) B3178043
theorem B2383537 : Blo 2117435 2383537 := bbase (se 2 (by rfl) ⟨893826, by rfl⟩ : syracuseStep 2383537 = 1787653) (by norm_num)
theorem B3178049 : Blo 2117435 3178049 := bstep (se 2 (by rfl) ⟨1191768, by rfl⟩ : syracuseStep 3178049 = 2383537) B2383537
theorem B2118699 : Blo 2117435 2118699 := bstep (se 1 (by rfl) ⟨1589024, by rfl⟩ : syracuseStep 2118699 = 3178049) B3178049
theorem B3723661 : Blo 2117435 3723661 := bbase (se 3 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 3723661 = 1396373) (by norm_num)
theorem B19859525 : Blo 2117435 19859525 := bstep (se 4 (by rfl) ⟨1861830, by rfl⟩ : syracuseStep 19859525 = 3723661) B3723661
theorem B13239683 : Blo 2117435 13239683 := bstep (se 1 (by rfl) ⟨9929762, by rfl⟩ : syracuseStep 13239683 = 19859525) B19859525
theorem B8826455 : Blo 2117435 8826455 := bstep (se 1 (by rfl) ⟨6619841, by rfl⟩ : syracuseStep 8826455 = 13239683) B13239683
theorem B23537213 : Blo 2117435 23537213 := bstep (se 3 (by rfl) ⟨4413227, by rfl⟩ : syracuseStep 23537213 = 8826455) B8826455
theorem B15691475 : Blo 2117435 15691475 := bstep (se 1 (by rfl) ⟨11768606, by rfl⟩ : syracuseStep 15691475 = 23537213) B23537213
theorem B10460983 : Blo 2117435 10460983 := bstep (se 1 (by rfl) ⟨7845737, by rfl⟩ : syracuseStep 10460983 = 15691475) B15691475
theorem B13947977 : Blo 2117435 13947977 := bstep (se 2 (by rfl) ⟨5230491, by rfl⟩ : syracuseStep 13947977 = 10460983) B10460983
theorem B9298651 : Blo 2117435 9298651 := bstep (se 1 (by rfl) ⟨6973988, by rfl⟩ : syracuseStep 9298651 = 13947977) B13947977
theorem B12398201 : Blo 2117435 12398201 := bstep (se 2 (by rfl) ⟨4649325, by rfl⟩ : syracuseStep 12398201 = 9298651) B9298651
theorem B8265467 : Blo 2117435 8265467 := bstep (se 1 (by rfl) ⟨6199100, by rfl⟩ : syracuseStep 8265467 = 12398201) B12398201
theorem B5510311 : Blo 2117435 5510311 := bstep (se 1 (by rfl) ⟨4132733, by rfl⟩ : syracuseStep 5510311 = 8265467) B8265467
theorem B117553301 : Blo 2117435 117553301 := bstep (se 6 (by rfl) ⟨2755155, by rfl⟩ : syracuseStep 117553301 = 5510311) B5510311
theorem B78368867 : Blo 2117435 78368867 := bstep (se 1 (by rfl) ⟨58776650, by rfl⟩ : syracuseStep 78368867 = 117553301) B117553301
theorem B52245911 : Blo 2117435 52245911 := bstep (se 1 (by rfl) ⟨39184433, by rfl⟩ : syracuseStep 52245911 = 78368867) B78368867
theorem B34830607 : Blo 2117435 34830607 := bstep (se 1 (by rfl) ⟨26122955, by rfl⟩ : syracuseStep 34830607 = 52245911) B52245911
theorem B46440809 : Blo 2117435 46440809 := bstep (se 2 (by rfl) ⟨17415303, by rfl⟩ : syracuseStep 46440809 = 34830607) B34830607
theorem B30960539 : Blo 2117435 30960539 := bstep (se 1 (by rfl) ⟨23220404, by rfl⟩ : syracuseStep 30960539 = 46440809) B46440809
theorem B20640359 : Blo 2117435 20640359 := bstep (se 1 (by rfl) ⟨15480269, by rfl⟩ : syracuseStep 20640359 = 30960539) B30960539
theorem B13760239 : Blo 2117435 13760239 := bstep (se 1 (by rfl) ⟨10320179, by rfl⟩ : syracuseStep 13760239 = 20640359) B20640359
theorem B18346985 : Blo 2117435 18346985 := bstep (se 2 (by rfl) ⟨6880119, by rfl⟩ : syracuseStep 18346985 = 13760239) B13760239
theorem B12231323 : Blo 2117435 12231323 := bstep (se 1 (by rfl) ⟨9173492, by rfl⟩ : syracuseStep 12231323 = 18346985) B18346985
theorem B8154215 : Blo 2117435 8154215 := bstep (se 1 (by rfl) ⟨6115661, by rfl⟩ : syracuseStep 8154215 = 12231323) B12231323
theorem B5436143 : Blo 2117435 5436143 := bstep (se 1 (by rfl) ⟨4077107, by rfl⟩ : syracuseStep 5436143 = 8154215) B8154215
theorem B3624095 : Blo 2117435 3624095 := bstep (se 1 (by rfl) ⟨2718071, by rfl⟩ : syracuseStep 3624095 = 5436143) B5436143
theorem B2416063 : Blo 2117435 2416063 := bstep (se 1 (by rfl) ⟨1812047, by rfl⟩ : syracuseStep 2416063 = 3624095) B3624095
theorem B3221417 : Blo 2117435 3221417 := bstep (se 2 (by rfl) ⟨1208031, by rfl⟩ : syracuseStep 3221417 = 2416063) B2416063
theorem B8590445 : Blo 2117435 8590445 := bstep (se 3 (by rfl) ⟨1610708, by rfl⟩ : syracuseStep 8590445 = 3221417) B3221417
theorem B5726963 : Blo 2117435 5726963 := bstep (se 1 (by rfl) ⟨4295222, by rfl⟩ : syracuseStep 5726963 = 8590445) B8590445
theorem B3817975 : Blo 2117435 3817975 := bstep (se 1 (by rfl) ⟨2863481, by rfl⟩ : syracuseStep 3817975 = 5726963) B5726963
theorem B5090633 : Blo 2117435 5090633 := bstep (se 2 (by rfl) ⟨1908987, by rfl⟩ : syracuseStep 5090633 = 3817975) B3817975
theorem B3393755 : Blo 2117435 3393755 := bstep (se 1 (by rfl) ⟨2545316, by rfl⟩ : syracuseStep 3393755 = 5090633) B5090633
theorem B2262503 : Blo 2117435 2262503 := bstep (se 1 (by rfl) ⟨1696877, by rfl⟩ : syracuseStep 2262503 = 3393755) B3393755
theorem B6033341 : Blo 2117435 6033341 := bstep (se 3 (by rfl) ⟨1131251, by rfl⟩ : syracuseStep 6033341 = 2262503) B2262503
theorem B4022227 : Blo 2117435 4022227 := bstep (se 1 (by rfl) ⟨3016670, by rfl⟩ : syracuseStep 4022227 = 6033341) B6033341
theorem B5362969 : Blo 2117435 5362969 := bstep (se 2 (by rfl) ⟨2011113, by rfl⟩ : syracuseStep 5362969 = 4022227) B4022227
theorem B7150625 : Blo 2117435 7150625 := bstep (se 2 (by rfl) ⟨2681484, by rfl⟩ : syracuseStep 7150625 = 5362969) B5362969
theorem B4767083 : Blo 2117435 4767083 := bstep (se 1 (by rfl) ⟨3575312, by rfl⟩ : syracuseStep 4767083 = 7150625) B7150625
theorem B3178055 : Blo 2117435 3178055 := bstep (se 1 (by rfl) ⟨2383541, by rfl⟩ : syracuseStep 3178055 = 4767083) B4767083
theorem B2118703 : Blo 2117435 2118703 := bstep (se 1 (by rfl) ⟨1589027, by rfl⟩ : syracuseStep 2118703 = 3178055) B3178055
theorem B3178061 : Blo 2117435 3178061 := bbase (se 3 (by rfl) ⟨595886, by rfl⟩ : syracuseStep 3178061 = 1191773) (by norm_num)
theorem B2118707 : Blo 2117435 2118707 := bstep (se 1 (by rfl) ⟨1589030, by rfl⟩ : syracuseStep 2118707 = 3178061) B3178061
theorem B4767101 : Blo 2117435 4767101 := bbase (se 3 (by rfl) ⟨893831, by rfl⟩ : syracuseStep 4767101 = 1787663) (by norm_num)
theorem B3178067 : Blo 2117435 3178067 := bstep (se 1 (by rfl) ⟨2383550, by rfl⟩ : syracuseStep 3178067 = 4767101) B4767101
theorem B2118711 : Blo 2117435 2118711 := bstep (se 1 (by rfl) ⟨1589033, by rfl⟩ : syracuseStep 2118711 = 3178067) B3178067
theorem B3575333 : Blo 2117435 3575333 := bbase (se 4 (by rfl) ⟨335187, by rfl⟩ : syracuseStep 3575333 = 670375) (by norm_num)
theorem B2383555 : Blo 2117435 2383555 := bstep (se 1 (by rfl) ⟨1787666, by rfl⟩ : syracuseStep 2383555 = 3575333) B3575333
theorem B3178073 : Blo 2117435 3178073 := bstep (se 2 (by rfl) ⟨1191777, by rfl⟩ : syracuseStep 3178073 = 2383555) B2383555
theorem B2118715 : Blo 2117435 2118715 := bstep (se 1 (by rfl) ⟨1589036, by rfl⟩ : syracuseStep 2118715 = 3178073) B3178073
theorem B3016693 : Blo 2117435 3016693 := bbase (se 5 (by rfl) ⟨141407, by rfl⟩ : syracuseStep 3016693 = 282815) (by norm_num)
theorem B16089029 : Blo 2117435 16089029 := bstep (se 4 (by rfl) ⟨1508346, by rfl⟩ : syracuseStep 16089029 = 3016693) B3016693
theorem B10726019 : Blo 2117435 10726019 := bstep (se 1 (by rfl) ⟨8044514, by rfl⟩ : syracuseStep 10726019 = 16089029) B16089029
theorem B7150679 : Blo 2117435 7150679 := bstep (se 1 (by rfl) ⟨5363009, by rfl⟩ : syracuseStep 7150679 = 10726019) B10726019
theorem B4767119 : Blo 2117435 4767119 := bstep (se 1 (by rfl) ⟨3575339, by rfl⟩ : syracuseStep 4767119 = 7150679) B7150679
theorem B3178079 : Blo 2117435 3178079 := bstep (se 1 (by rfl) ⟨2383559, by rfl⟩ : syracuseStep 3178079 = 4767119) B4767119
theorem B2118719 : Blo 2117435 2118719 := bstep (se 1 (by rfl) ⟨1589039, by rfl⟩ : syracuseStep 2118719 = 3178079) B3178079
theorem B3178085 : Blo 2117435 3178085 := bbase (se 4 (by rfl) ⟨297945, by rfl⟩ : syracuseStep 3178085 = 595891) (by norm_num)
theorem B2118723 : Blo 2117435 2118723 := bstep (se 1 (by rfl) ⟨1589042, by rfl⟩ : syracuseStep 2118723 = 3178085) B3178085
theorem B2262529 : Blo 2117435 2262529 := bbase (se 2 (by rfl) ⟨848448, by rfl⟩ : syracuseStep 2262529 = 1696897) (by norm_num)
theorem B3016705 : Blo 2117435 3016705 := bstep (se 2 (by rfl) ⟨1131264, by rfl⟩ : syracuseStep 3016705 = 2262529) B2262529
theorem B4022273 : Blo 2117435 4022273 := bstep (se 2 (by rfl) ⟨1508352, by rfl⟩ : syracuseStep 4022273 = 3016705) B3016705
theorem B2681515 : Blo 2117435 2681515 := bstep (se 1 (by rfl) ⟨2011136, by rfl⟩ : syracuseStep 2681515 = 4022273) B4022273
theorem B3575353 : Blo 2117435 3575353 := bstep (se 2 (by rfl) ⟨1340757, by rfl⟩ : syracuseStep 3575353 = 2681515) B2681515
theorem B4767137 : Blo 2117435 4767137 := bstep (se 2 (by rfl) ⟨1787676, by rfl⟩ : syracuseStep 4767137 = 3575353) B3575353
theorem B3178091 : Blo 2117435 3178091 := bstep (se 1 (by rfl) ⟨2383568, by rfl⟩ : syracuseStep 3178091 = 4767137) B4767137
theorem B2118727 : Blo 2117435 2118727 := bstep (se 1 (by rfl) ⟨1589045, by rfl⟩ : syracuseStep 2118727 = 3178091) B3178091
theorem B2383573 : Blo 2117435 2383573 := bbase (se 7 (by rfl) ⟨27932, by rfl⟩ : syracuseStep 2383573 = 55865) (by norm_num)
theorem B3178097 : Blo 2117435 3178097 := bstep (se 2 (by rfl) ⟨1191786, by rfl⟩ : syracuseStep 3178097 = 2383573) B2383573
theorem B2118731 : Blo 2117435 2118731 := bstep (se 1 (by rfl) ⟨1589048, by rfl⟩ : syracuseStep 2118731 = 3178097) B3178097
theorem B2681525 : Blo 2117435 2681525 := bbase (se 5 (by rfl) ⟨125696, by rfl⟩ : syracuseStep 2681525 = 251393) (by norm_num)
theorem B7150733 : Blo 2117435 7150733 := bstep (se 3 (by rfl) ⟨1340762, by rfl⟩ : syracuseStep 7150733 = 2681525) B2681525
theorem B4767155 : Blo 2117435 4767155 := bstep (se 1 (by rfl) ⟨3575366, by rfl⟩ : syracuseStep 4767155 = 7150733) B7150733
theorem B3178103 : Blo 2117435 3178103 := bstep (se 1 (by rfl) ⟨2383577, by rfl⟩ : syracuseStep 3178103 = 4767155) B4767155
theorem B2118735 : Blo 2117435 2118735 := bstep (se 1 (by rfl) ⟨1589051, by rfl⟩ : syracuseStep 2118735 = 3178103) B3178103
theorem B3178109 : Blo 2117435 3178109 := bbase (se 3 (by rfl) ⟨595895, by rfl⟩ : syracuseStep 3178109 = 1191791) (by norm_num)
theorem B2118739 : Blo 2117435 2118739 := bstep (se 1 (by rfl) ⟨1589054, by rfl⟩ : syracuseStep 2118739 = 3178109) B3178109
theorem B4767173 : Blo 2117435 4767173 := bbase (se 4 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 4767173 = 893845) (by norm_num)
theorem B3178115 : Blo 2117435 3178115 := bstep (se 1 (by rfl) ⟨2383586, by rfl⟩ : syracuseStep 3178115 = 4767173) B4767173
theorem B2118743 : Blo 2117435 2118743 := bstep (se 1 (by rfl) ⟨1589057, by rfl⟩ : syracuseStep 2118743 = 3178115) B3178115
theorem B10181477 : Blo 2117435 10181477 := bbase (se 4 (by rfl) ⟨954513, by rfl⟩ : syracuseStep 10181477 = 1909027) (by norm_num)
theorem B6787651 : Blo 2117435 6787651 := bstep (se 1 (by rfl) ⟨5090738, by rfl⟩ : syracuseStep 6787651 = 10181477) B10181477
theorem B9050201 : Blo 2117435 9050201 := bstep (se 2 (by rfl) ⟨3393825, by rfl⟩ : syracuseStep 9050201 = 6787651) B6787651
theorem B6033467 : Blo 2117435 6033467 := bstep (se 1 (by rfl) ⟨4525100, by rfl⟩ : syracuseStep 6033467 = 9050201) B9050201
theorem B4022311 : Blo 2117435 4022311 := bstep (se 1 (by rfl) ⟨3016733, by rfl⟩ : syracuseStep 4022311 = 6033467) B6033467
theorem B5363081 : Blo 2117435 5363081 := bstep (se 2 (by rfl) ⟨2011155, by rfl⟩ : syracuseStep 5363081 = 4022311) B4022311
theorem B3575387 : Blo 2117435 3575387 := bstep (se 1 (by rfl) ⟨2681540, by rfl⟩ : syracuseStep 3575387 = 5363081) B5363081
theorem B2383591 : Blo 2117435 2383591 := bstep (se 1 (by rfl) ⟨1787693, by rfl⟩ : syracuseStep 2383591 = 3575387) B3575387
theorem B3178121 : Blo 2117435 3178121 := bstep (se 2 (by rfl) ⟨1191795, by rfl⟩ : syracuseStep 3178121 = 2383591) B2383591
theorem B2118747 : Blo 2117435 2118747 := bstep (se 1 (by rfl) ⟨1589060, by rfl⟩ : syracuseStep 2118747 = 3178121) B3178121
theorem B10726181 : Blo 2117435 10726181 := bbase (se 4 (by rfl) ⟨1005579, by rfl⟩ : syracuseStep 10726181 = 2011159) (by norm_num)
theorem B7150787 : Blo 2117435 7150787 := bstep (se 1 (by rfl) ⟨5363090, by rfl⟩ : syracuseStep 7150787 = 10726181) B10726181
theorem B4767191 : Blo 2117435 4767191 := bstep (se 1 (by rfl) ⟨3575393, by rfl⟩ : syracuseStep 4767191 = 7150787) B7150787
theorem B3178127 : Blo 2117435 3178127 := bstep (se 1 (by rfl) ⟨2383595, by rfl⟩ : syracuseStep 3178127 = 4767191) B4767191
theorem B2118751 : Blo 2117435 2118751 := bstep (se 1 (by rfl) ⟨1589063, by rfl⟩ : syracuseStep 2118751 = 3178127) B3178127
theorem B3178133 : Blo 2117435 3178133 := bbase (se 6 (by rfl) ⟨74487, by rfl⟩ : syracuseStep 3178133 = 148975) (by norm_num)
theorem B2118755 : Blo 2117435 2118755 := bstep (se 1 (by rfl) ⟨1589066, by rfl⟩ : syracuseStep 2118755 = 3178133) B3178133
theorem B13760597 : Blo 2117435 13760597 := bbase (se 8 (by rfl) ⟨80628, by rfl⟩ : syracuseStep 13760597 = 161257) (by norm_num)
theorem B9173731 : Blo 2117435 9173731 := bstep (se 1 (by rfl) ⟨6880298, by rfl⟩ : syracuseStep 9173731 = 13760597) B13760597
theorem B12231641 : Blo 2117435 12231641 := bstep (se 2 (by rfl) ⟨4586865, by rfl⟩ : syracuseStep 12231641 = 9173731) B9173731
theorem B8154427 : Blo 2117435 8154427 := bstep (se 1 (by rfl) ⟨6115820, by rfl⟩ : syracuseStep 8154427 = 12231641) B12231641
theorem B10872569 : Blo 2117435 10872569 := bstep (se 2 (by rfl) ⟨4077213, by rfl⟩ : syracuseStep 10872569 = 8154427) B8154427
theorem B7248379 : Blo 2117435 7248379 := bstep (se 1 (by rfl) ⟨5436284, by rfl⟩ : syracuseStep 7248379 = 10872569) B10872569
theorem B9664505 : Blo 2117435 9664505 := bstep (se 2 (by rfl) ⟨3624189, by rfl⟩ : syracuseStep 9664505 = 7248379) B7248379
theorem B6443003 : Blo 2117435 6443003 := bstep (se 1 (by rfl) ⟨4832252, by rfl⟩ : syracuseStep 6443003 = 9664505) B9664505
theorem B4295335 : Blo 2117435 4295335 := bstep (se 1 (by rfl) ⟨3221501, by rfl⟩ : syracuseStep 4295335 = 6443003) B6443003
theorem B5727113 : Blo 2117435 5727113 := bstep (se 2 (by rfl) ⟨2147667, by rfl⟩ : syracuseStep 5727113 = 4295335) B4295335
theorem B3818075 : Blo 2117435 3818075 := bstep (se 1 (by rfl) ⟨2863556, by rfl⟩ : syracuseStep 3818075 = 5727113) B5727113
theorem B10181533 : Blo 2117435 10181533 := bstep (se 3 (by rfl) ⟨1909037, by rfl⟩ : syracuseStep 10181533 = 3818075) B3818075
theorem B13575377 : Blo 2117435 13575377 := bstep (se 2 (by rfl) ⟨5090766, by rfl⟩ : syracuseStep 13575377 = 10181533) B10181533
theorem B9050251 : Blo 2117435 9050251 := bstep (se 1 (by rfl) ⟨6787688, by rfl⟩ : syracuseStep 9050251 = 13575377) B13575377
theorem B12067001 : Blo 2117435 12067001 := bstep (se 2 (by rfl) ⟨4525125, by rfl⟩ : syracuseStep 12067001 = 9050251) B9050251
theorem B8044667 : Blo 2117435 8044667 := bstep (se 1 (by rfl) ⟨6033500, by rfl⟩ : syracuseStep 8044667 = 12067001) B12067001
theorem B5363111 : Blo 2117435 5363111 := bstep (se 1 (by rfl) ⟨4022333, by rfl⟩ : syracuseStep 5363111 = 8044667) B8044667
theorem B3575407 : Blo 2117435 3575407 := bstep (se 1 (by rfl) ⟨2681555, by rfl⟩ : syracuseStep 3575407 = 5363111) B5363111
theorem B4767209 : Blo 2117435 4767209 := bstep (se 2 (by rfl) ⟨1787703, by rfl⟩ : syracuseStep 4767209 = 3575407) B3575407
theorem B3178139 : Blo 2117435 3178139 := bstep (se 1 (by rfl) ⟨2383604, by rfl⟩ : syracuseStep 3178139 = 4767209) B4767209
theorem B2118759 : Blo 2117435 2118759 := bstep (se 1 (by rfl) ⟨1589069, by rfl⟩ : syracuseStep 2118759 = 3178139) B3178139
theorem B2383609 : Blo 2117435 2383609 := bbase (se 2 (by rfl) ⟨893853, by rfl⟩ : syracuseStep 2383609 = 1787707) (by norm_num)
theorem B3178145 : Blo 2117435 3178145 := bstep (se 2 (by rfl) ⟨1191804, by rfl⟩ : syracuseStep 3178145 = 2383609) B2383609
theorem B2118763 : Blo 2117435 2118763 := bstep (se 1 (by rfl) ⟨1589072, by rfl⟩ : syracuseStep 2118763 = 3178145) B3178145
theorem B2545393 : Blo 2117435 2545393 := bbase (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) (by norm_num)
theorem B3393857 : Blo 2117435 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B9050285 : Blo 2117435 9050285 := bstep (se 3 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 9050285 = 3393857) B3393857
theorem B6033523 : Blo 2117435 6033523 := bstep (se 1 (by rfl) ⟨4525142, by rfl⟩ : syracuseStep 6033523 = 9050285) B9050285
theorem B8044697 : Blo 2117435 8044697 := bstep (se 2 (by rfl) ⟨3016761, by rfl⟩ : syracuseStep 8044697 = 6033523) B6033523
theorem B5363131 : Blo 2117435 5363131 := bstep (se 1 (by rfl) ⟨4022348, by rfl⟩ : syracuseStep 5363131 = 8044697) B8044697
theorem B7150841 : Blo 2117435 7150841 := bstep (se 2 (by rfl) ⟨2681565, by rfl⟩ : syracuseStep 7150841 = 5363131) B5363131
theorem B4767227 : Blo 2117435 4767227 := bstep (se 1 (by rfl) ⟨3575420, by rfl⟩ : syracuseStep 4767227 = 7150841) B7150841
theorem B3178151 : Blo 2117435 3178151 := bstep (se 1 (by rfl) ⟨2383613, by rfl⟩ : syracuseStep 3178151 = 4767227) B4767227
theorem B2118767 : Blo 2117435 2118767 := bstep (se 1 (by rfl) ⟨1589075, by rfl⟩ : syracuseStep 2118767 = 3178151) B3178151
theorem B3178157 : Blo 2117435 3178157 := bbase (se 3 (by rfl) ⟨595904, by rfl⟩ : syracuseStep 3178157 = 1191809) (by norm_num)
theorem B2118771 : Blo 2117435 2118771 := bstep (se 1 (by rfl) ⟨1589078, by rfl⟩ : syracuseStep 2118771 = 3178157) B3178157
theorem B4767245 : Blo 2117435 4767245 := bbase (se 3 (by rfl) ⟨893858, by rfl⟩ : syracuseStep 4767245 = 1787717) (by norm_num)
theorem B3178163 : Blo 2117435 3178163 := bstep (se 1 (by rfl) ⟨2383622, by rfl⟩ : syracuseStep 3178163 = 4767245) B4767245
theorem B2118775 : Blo 2117435 2118775 := bstep (se 1 (by rfl) ⟨1589081, by rfl⟩ : syracuseStep 2118775 = 3178163) B3178163
theorem B2681581 : Blo 2117435 2681581 := bbase (se 3 (by rfl) ⟨502796, by rfl⟩ : syracuseStep 2681581 = 1005593) (by norm_num)
theorem B3575441 : Blo 2117435 3575441 := bstep (se 2 (by rfl) ⟨1340790, by rfl⟩ : syracuseStep 3575441 = 2681581) B2681581
theorem B2383627 : Blo 2117435 2383627 := bstep (se 1 (by rfl) ⟨1787720, by rfl⟩ : syracuseStep 2383627 = 3575441) B3575441
theorem B3178169 : Blo 2117435 3178169 := bstep (se 2 (by rfl) ⟨1191813, by rfl⟩ : syracuseStep 3178169 = 2383627) B2383627
theorem B2118779 : Blo 2117435 2118779 := bstep (se 1 (by rfl) ⟨1589084, by rfl⟩ : syracuseStep 2118779 = 3178169) B3178169
theorem B2416153 : Blo 2117435 2416153 := bbase (se 2 (by rfl) ⟨906057, by rfl⟩ : syracuseStep 2416153 = 1812115) (by norm_num)
theorem B3221537 : Blo 2117435 3221537 := bstep (se 2 (by rfl) ⟨1208076, by rfl⟩ : syracuseStep 3221537 = 2416153) B2416153
theorem B34363061 : Blo 2117435 34363061 := bstep (se 5 (by rfl) ⟨1610768, by rfl⟩ : syracuseStep 34363061 = 3221537) B3221537
theorem B22908707 : Blo 2117435 22908707 := bstep (se 1 (by rfl) ⟨17181530, by rfl⟩ : syracuseStep 22908707 = 34363061) B34363061
theorem B15272471 : Blo 2117435 15272471 := bstep (se 1 (by rfl) ⟨11454353, by rfl⟩ : syracuseStep 15272471 = 22908707) B22908707
theorem B10181647 : Blo 2117435 10181647 := bstep (se 1 (by rfl) ⟨7636235, by rfl⟩ : syracuseStep 10181647 = 15272471) B15272471
theorem B13575529 : Blo 2117435 13575529 := bstep (se 2 (by rfl) ⟨5090823, by rfl⟩ : syracuseStep 13575529 = 10181647) B10181647
theorem B18100705 : Blo 2117435 18100705 := bstep (se 2 (by rfl) ⟨6787764, by rfl⟩ : syracuseStep 18100705 = 13575529) B13575529
theorem B24134273 : Blo 2117435 24134273 := bstep (se 2 (by rfl) ⟨9050352, by rfl⟩ : syracuseStep 24134273 = 18100705) B18100705
theorem B16089515 : Blo 2117435 16089515 := bstep (se 1 (by rfl) ⟨12067136, by rfl⟩ : syracuseStep 16089515 = 24134273) B24134273
theorem B10726343 : Blo 2117435 10726343 := bstep (se 1 (by rfl) ⟨8044757, by rfl⟩ : syracuseStep 10726343 = 16089515) B16089515
theorem B7150895 : Blo 2117435 7150895 := bstep (se 1 (by rfl) ⟨5363171, by rfl⟩ : syracuseStep 7150895 = 10726343) B10726343
theorem B4767263 : Blo 2117435 4767263 := bstep (se 1 (by rfl) ⟨3575447, by rfl⟩ : syracuseStep 4767263 = 7150895) B7150895
theorem B3178175 : Blo 2117435 3178175 := bstep (se 1 (by rfl) ⟨2383631, by rfl⟩ : syracuseStep 3178175 = 4767263) B4767263
theorem B2118783 : Blo 2117435 2118783 := bstep (se 1 (by rfl) ⟨1589087, by rfl⟩ : syracuseStep 2118783 = 3178175) B3178175
theorem B3178181 : Blo 2117435 3178181 := bbase (se 4 (by rfl) ⟨297954, by rfl⟩ : syracuseStep 3178181 = 595909) (by norm_num)
theorem B2118787 : Blo 2117435 2118787 := bstep (se 1 (by rfl) ⟨1589090, by rfl⟩ : syracuseStep 2118787 = 3178181) B3178181
theorem B3575461 : Blo 2117435 3575461 := bbase (se 4 (by rfl) ⟨335199, by rfl⟩ : syracuseStep 3575461 = 670399) (by norm_num)
theorem B4767281 : Blo 2117435 4767281 := bstep (se 2 (by rfl) ⟨1787730, by rfl⟩ : syracuseStep 4767281 = 3575461) B3575461
theorem B3178187 : Blo 2117435 3178187 := bstep (se 1 (by rfl) ⟨2383640, by rfl⟩ : syracuseStep 3178187 = 4767281) B4767281
theorem B2118791 : Blo 2117435 2118791 := bstep (se 1 (by rfl) ⟨1589093, by rfl⟩ : syracuseStep 2118791 = 3178187) B3178187
theorem B2383645 : Blo 2117435 2383645 := bbase (se 3 (by rfl) ⟨446933, by rfl⟩ : syracuseStep 2383645 = 893867) (by norm_num)
theorem B3178193 : Blo 2117435 3178193 := bstep (se 2 (by rfl) ⟨1191822, by rfl⟩ : syracuseStep 3178193 = 2383645) B2383645
theorem B2118795 : Blo 2117435 2118795 := bstep (se 1 (by rfl) ⟨1589096, by rfl⟩ : syracuseStep 2118795 = 3178193) B3178193
theorem B7150949 : Blo 2117435 7150949 := bbase (se 4 (by rfl) ⟨670401, by rfl⟩ : syracuseStep 7150949 = 1340803) (by norm_num)
theorem B4767299 : Blo 2117435 4767299 := bstep (se 1 (by rfl) ⟨3575474, by rfl⟩ : syracuseStep 4767299 = 7150949) B7150949
theorem B3178199 : Blo 2117435 3178199 := bstep (se 1 (by rfl) ⟨2383649, by rfl⟩ : syracuseStep 3178199 = 4767299) B4767299
theorem B2118799 : Blo 2117435 2118799 := bstep (se 1 (by rfl) ⟨1589099, by rfl⟩ : syracuseStep 2118799 = 3178199) B3178199
theorem B3178205 : Blo 2117435 3178205 := bbase (se 3 (by rfl) ⟨595913, by rfl⟩ : syracuseStep 3178205 = 1191827) (by norm_num)
theorem B2118803 : Blo 2117435 2118803 := bstep (se 1 (by rfl) ⟨1589102, by rfl⟩ : syracuseStep 2118803 = 3178205) B3178205
theorem B4767317 : Blo 2117435 4767317 := bbase (se 8 (by rfl) ⟨27933, by rfl⟩ : syracuseStep 4767317 = 55867) (by norm_num)
theorem B3178211 : Blo 2117435 3178211 := bstep (se 1 (by rfl) ⟨2383658, by rfl⟩ : syracuseStep 3178211 = 4767317) B4767317
theorem B2118807 : Blo 2117435 2118807 := bstep (se 1 (by rfl) ⟨1589105, by rfl⟩ : syracuseStep 2118807 = 3178211) B3178211
theorem B4525237 : Blo 2117435 4525237 := bbase (se 5 (by rfl) ⟨212120, by rfl⟩ : syracuseStep 4525237 = 424241) (by norm_num)
theorem B6033649 : Blo 2117435 6033649 := bstep (se 2 (by rfl) ⟨2262618, by rfl⟩ : syracuseStep 6033649 = 4525237) B4525237
theorem B8044865 : Blo 2117435 8044865 := bstep (se 2 (by rfl) ⟨3016824, by rfl⟩ : syracuseStep 8044865 = 6033649) B6033649
theorem B5363243 : Blo 2117435 5363243 := bstep (se 1 (by rfl) ⟨4022432, by rfl⟩ : syracuseStep 5363243 = 8044865) B8044865
theorem B3575495 : Blo 2117435 3575495 := bstep (se 1 (by rfl) ⟨2681621, by rfl⟩ : syracuseStep 3575495 = 5363243) B5363243
theorem B2383663 : Blo 2117435 2383663 := bstep (se 1 (by rfl) ⟨1787747, by rfl⟩ : syracuseStep 2383663 = 3575495) B3575495
theorem B3178217 : Blo 2117435 3178217 := bstep (se 2 (by rfl) ⟨1191831, by rfl⟩ : syracuseStep 3178217 = 2383663) B2383663
theorem B2118811 : Blo 2117435 2118811 := bstep (se 1 (by rfl) ⟨1589108, by rfl⟩ : syracuseStep 2118811 = 3178217) B3178217
theorem B3310093 : Blo 2117435 3310093 := bbase (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) (by norm_num)
theorem B4413457 : Blo 2117435 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B23538437 : Blo 2117435 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B15692291 : Blo 2117435 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B10461527 : Blo 2117435 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B6974351 : Blo 2117435 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B4649567 : Blo 2117435 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B12398845 : Blo 2117435 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B16531793 : Blo 2117435 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B11021195 : Blo 2117435 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B29389853 : Blo 2117435 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B19593235 : Blo 2117435 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B104497253 : Blo 2117435 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B69664835 : Blo 2117435 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B46443223 : Blo 2117435 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B61924297 : Blo 2117435 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B82565729 : Blo 2117435 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B55043819 : Blo 2117435 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B36695879 : Blo 2117435 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B24463919 : Blo 2117435 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B16309279 : Blo 2117435 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B86982821 : Blo 2117435 86982821 := bstep (se 4 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 86982821 = 16309279) B16309279
theorem B57988547 : Blo 2117435 57988547 := bstep (se 1 (by rfl) ⟨43491410, by rfl⟩ : syracuseStep 57988547 = 86982821) B86982821
theorem B38659031 : Blo 2117435 38659031 := bstep (se 1 (by rfl) ⟨28994273, by rfl⟩ : syracuseStep 38659031 = 57988547) B57988547
theorem B25772687 : Blo 2117435 25772687 := bstep (se 1 (by rfl) ⟨19329515, by rfl⟩ : syracuseStep 25772687 = 38659031) B38659031
theorem B17181791 : Blo 2117435 17181791 := bstep (se 1 (by rfl) ⟨12886343, by rfl⟩ : syracuseStep 17181791 = 25772687) B25772687
theorem B11454527 : Blo 2117435 11454527 := bstep (se 1 (by rfl) ⟨8590895, by rfl⟩ : syracuseStep 11454527 = 17181791) B17181791
theorem B7636351 : Blo 2117435 7636351 := bstep (se 1 (by rfl) ⟨5727263, by rfl⟩ : syracuseStep 7636351 = 11454527) B11454527
theorem B10181801 : Blo 2117435 10181801 := bstep (se 2 (by rfl) ⟨3818175, by rfl⟩ : syracuseStep 10181801 = 7636351) B7636351
theorem B27151469 : Blo 2117435 27151469 := bstep (se 3 (by rfl) ⟨5090900, by rfl⟩ : syracuseStep 27151469 = 10181801) B10181801
theorem B18100979 : Blo 2117435 18100979 := bstep (se 1 (by rfl) ⟨13575734, by rfl⟩ : syracuseStep 18100979 = 27151469) B27151469
theorem B12067319 : Blo 2117435 12067319 := bstep (se 1 (by rfl) ⟨9050489, by rfl⟩ : syracuseStep 12067319 = 18100979) B18100979
theorem B8044879 : Blo 2117435 8044879 := bstep (se 1 (by rfl) ⟨6033659, by rfl⟩ : syracuseStep 8044879 = 12067319) B12067319
theorem B10726505 : Blo 2117435 10726505 := bstep (se 2 (by rfl) ⟨4022439, by rfl⟩ : syracuseStep 10726505 = 8044879) B8044879
theorem B7151003 : Blo 2117435 7151003 := bstep (se 1 (by rfl) ⟨5363252, by rfl⟩ : syracuseStep 7151003 = 10726505) B10726505
theorem B4767335 : Blo 2117435 4767335 := bstep (se 1 (by rfl) ⟨3575501, by rfl⟩ : syracuseStep 4767335 = 7151003) B7151003
theorem B3178223 : Blo 2117435 3178223 := bstep (se 1 (by rfl) ⟨2383667, by rfl⟩ : syracuseStep 3178223 = 4767335) B4767335
theorem B2118815 : Blo 2117435 2118815 := bstep (se 1 (by rfl) ⟨1589111, by rfl⟩ : syracuseStep 2118815 = 3178223) B3178223
theorem B3178229 : Blo 2117435 3178229 := bbase (se 5 (by rfl) ⟨148979, by rfl⟩ : syracuseStep 3178229 = 297959) (by norm_num)
theorem B2118819 : Blo 2117435 2118819 := bstep (se 1 (by rfl) ⟨1589114, by rfl⟩ : syracuseStep 2118819 = 3178229) B3178229
theorem B4587005 : Blo 2117435 4587005 := bbase (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) (by norm_num)
theorem B3058003 : Blo 2117435 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B16309349 : Blo 2117435 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B10872899 : Blo 2117435 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B7248599 : Blo 2117435 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B4832399 : Blo 2117435 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B12886397 : Blo 2117435 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B8590931 : Blo 2117435 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B5727287 : Blo 2117435 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3818191 : Blo 2117435 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B5090921 : Blo 2117435 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B3393947 : Blo 2117435 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B9050525 : Blo 2117435 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B6033683 : Blo 2117435 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B4022455 : Blo 2117435 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B5363273 : Blo 2117435 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B3575515 : Blo 2117435 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B4767353 : Blo 2117435 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B3178235 : Blo 2117435 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B2118823 : Blo 2117435 2118823 := bstep (se 1 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 2118823 = 3178235) B3178235
theorem B2383681 : Blo 2117435 2383681 := bbase (se 2 (by rfl) ⟨893880, by rfl⟩ : syracuseStep 2383681 = 1787761) (by norm_num)
theorem B3178241 : Blo 2117435 3178241 := bstep (se 2 (by rfl) ⟨1191840, by rfl⟩ : syracuseStep 3178241 = 2383681) B2383681
theorem B2118827 : Blo 2117435 2118827 := bstep (se 1 (by rfl) ⟨1589120, by rfl⟩ : syracuseStep 2118827 = 3178241) B3178241
theorem B5363293 : Blo 2117435 5363293 := bbase (se 3 (by rfl) ⟨1005617, by rfl⟩ : syracuseStep 5363293 = 2011235) (by norm_num)
theorem B7151057 : Blo 2117435 7151057 := bstep (se 2 (by rfl) ⟨2681646, by rfl⟩ : syracuseStep 7151057 = 5363293) B5363293
theorem B4767371 : Blo 2117435 4767371 := bstep (se 1 (by rfl) ⟨3575528, by rfl⟩ : syracuseStep 4767371 = 7151057) B7151057
theorem B3178247 : Blo 2117435 3178247 := bstep (se 1 (by rfl) ⟨2383685, by rfl⟩ : syracuseStep 3178247 = 4767371) B4767371
theorem B2118831 : Blo 2117435 2118831 := bstep (se 1 (by rfl) ⟨1589123, by rfl⟩ : syracuseStep 2118831 = 3178247) B3178247
theorem B3178253 : Blo 2117435 3178253 := bbase (se 3 (by rfl) ⟨595922, by rfl⟩ : syracuseStep 3178253 = 1191845) (by norm_num)
theorem B2118835 : Blo 2117435 2118835 := bstep (se 1 (by rfl) ⟨1589126, by rfl⟩ : syracuseStep 2118835 = 3178253) B3178253
theorem B4767389 : Blo 2117435 4767389 := bbase (se 3 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 4767389 = 1787771) (by norm_num)
theorem B3178259 : Blo 2117435 3178259 := bstep (se 1 (by rfl) ⟨2383694, by rfl⟩ : syracuseStep 3178259 = 4767389) B4767389
theorem B2118839 : Blo 2117435 2118839 := bstep (se 1 (by rfl) ⟨1589129, by rfl⟩ : syracuseStep 2118839 = 3178259) B3178259
theorem B3575549 : Blo 2117435 3575549 := bbase (se 3 (by rfl) ⟨670415, by rfl⟩ : syracuseStep 3575549 = 1340831) (by norm_num)
theorem B2383699 : Blo 2117435 2383699 := bstep (se 1 (by rfl) ⟨1787774, by rfl⟩ : syracuseStep 2383699 = 3575549) B3575549
theorem B3178265 : Blo 2117435 3178265 := bstep (se 2 (by rfl) ⟨1191849, by rfl⟩ : syracuseStep 3178265 = 2383699) B2383699
theorem B2118843 : Blo 2117435 2118843 := bstep (se 1 (by rfl) ⟨1589132, by rfl⟩ : syracuseStep 2118843 = 3178265) B3178265
theorem B2545489 : Blo 2117435 2545489 := bbase (se 2 (by rfl) ⟨954558, by rfl⟩ : syracuseStep 2545489 = 1909117) (by norm_num)
theorem B3393985 : Blo 2117435 3393985 := bstep (se 2 (by rfl) ⟨1272744, by rfl⟩ : syracuseStep 3393985 = 2545489) B2545489
theorem B4525313 : Blo 2117435 4525313 := bstep (se 2 (by rfl) ⟨1696992, by rfl⟩ : syracuseStep 4525313 = 3393985) B3393985
theorem B12067501 : Blo 2117435 12067501 := bstep (se 3 (by rfl) ⟨2262656, by rfl⟩ : syracuseStep 12067501 = 4525313) B4525313
theorem B16090001 : Blo 2117435 16090001 := bstep (se 2 (by rfl) ⟨6033750, by rfl⟩ : syracuseStep 16090001 = 12067501) B12067501
theorem B10726667 : Blo 2117435 10726667 := bstep (se 1 (by rfl) ⟨8045000, by rfl⟩ : syracuseStep 10726667 = 16090001) B16090001
theorem B7151111 : Blo 2117435 7151111 := bstep (se 1 (by rfl) ⟨5363333, by rfl⟩ : syracuseStep 7151111 = 10726667) B10726667
theorem B4767407 : Blo 2117435 4767407 := bstep (se 1 (by rfl) ⟨3575555, by rfl⟩ : syracuseStep 4767407 = 7151111) B7151111
theorem B3178271 : Blo 2117435 3178271 := bstep (se 1 (by rfl) ⟨2383703, by rfl⟩ : syracuseStep 3178271 = 4767407) B4767407
theorem B2118847 : Blo 2117435 2118847 := bstep (se 1 (by rfl) ⟨1589135, by rfl⟩ : syracuseStep 2118847 = 3178271) B3178271
theorem B3178277 : Blo 2117435 3178277 := bbase (se 4 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 3178277 = 595927) (by norm_num)
theorem B2118851 : Blo 2117435 2118851 := bstep (se 1 (by rfl) ⟨1589138, by rfl⟩ : syracuseStep 2118851 = 3178277) B3178277
theorem B2681677 : Blo 2117435 2681677 := bbase (se 3 (by rfl) ⟨502814, by rfl⟩ : syracuseStep 2681677 = 1005629) (by norm_num)
theorem B3575569 : Blo 2117435 3575569 := bstep (se 2 (by rfl) ⟨1340838, by rfl⟩ : syracuseStep 3575569 = 2681677) B2681677
theorem B4767425 : Blo 2117435 4767425 := bstep (se 2 (by rfl) ⟨1787784, by rfl⟩ : syracuseStep 4767425 = 3575569) B3575569
theorem B3178283 : Blo 2117435 3178283 := bstep (se 1 (by rfl) ⟨2383712, by rfl⟩ : syracuseStep 3178283 = 4767425) B4767425
theorem B2118855 : Blo 2117435 2118855 := bstep (se 1 (by rfl) ⟨1589141, by rfl⟩ : syracuseStep 2118855 = 3178283) B3178283
theorem B2383717 : Blo 2117435 2383717 := bbase (se 4 (by rfl) ⟨223473, by rfl⟩ : syracuseStep 2383717 = 446947) (by norm_num)
theorem B3178289 : Blo 2117435 3178289 := bstep (se 2 (by rfl) ⟨1191858, by rfl⟩ : syracuseStep 3178289 = 2383717) B2383717
theorem B2118859 : Blo 2117435 2118859 := bstep (se 1 (by rfl) ⟨1589144, by rfl⟩ : syracuseStep 2118859 = 3178289) B3178289
theorem B6033797 : Blo 2117435 6033797 := bbase (se 4 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 6033797 = 1131337) (by norm_num)
theorem B4022531 : Blo 2117435 4022531 := bstep (se 1 (by rfl) ⟨3016898, by rfl⟩ : syracuseStep 4022531 = 6033797) B6033797
theorem B2681687 : Blo 2117435 2681687 := bstep (se 1 (by rfl) ⟨2011265, by rfl⟩ : syracuseStep 2681687 = 4022531) B4022531
theorem B7151165 : Blo 2117435 7151165 := bstep (se 3 (by rfl) ⟨1340843, by rfl⟩ : syracuseStep 7151165 = 2681687) B2681687
theorem B4767443 : Blo 2117435 4767443 := bstep (se 1 (by rfl) ⟨3575582, by rfl⟩ : syracuseStep 4767443 = 7151165) B7151165
theorem B3178295 : Blo 2117435 3178295 := bstep (se 1 (by rfl) ⟨2383721, by rfl⟩ : syracuseStep 3178295 = 4767443) B4767443
theorem B2118863 : Blo 2117435 2118863 := bstep (se 1 (by rfl) ⟨1589147, by rfl⟩ : syracuseStep 2118863 = 3178295) B3178295
theorem B3178301 : Blo 2117435 3178301 := bbase (se 3 (by rfl) ⟨595931, by rfl⟩ : syracuseStep 3178301 = 1191863) (by norm_num)
theorem B2118867 : Blo 2117435 2118867 := bstep (se 1 (by rfl) ⟨1589150, by rfl⟩ : syracuseStep 2118867 = 3178301) B3178301
theorem B4767461 : Blo 2117435 4767461 := bbase (se 4 (by rfl) ⟨446949, by rfl⟩ : syracuseStep 4767461 = 893899) (by norm_num)
theorem B3178307 : Blo 2117435 3178307 := bstep (se 1 (by rfl) ⟨2383730, by rfl⟩ : syracuseStep 3178307 = 4767461) B4767461
theorem B2118871 : Blo 2117435 2118871 := bstep (se 1 (by rfl) ⟨1589153, by rfl⟩ : syracuseStep 2118871 = 3178307) B3178307
theorem B5363405 : Blo 2117435 5363405 := bbase (se 3 (by rfl) ⟨1005638, by rfl⟩ : syracuseStep 5363405 = 2011277) (by norm_num)
theorem B3575603 : Blo 2117435 3575603 := bstep (se 1 (by rfl) ⟨2681702, by rfl⟩ : syracuseStep 3575603 = 5363405) B5363405
theorem B2383735 : Blo 2117435 2383735 := bstep (se 1 (by rfl) ⟨1787801, by rfl⟩ : syracuseStep 2383735 = 3575603) B3575603
theorem B3178313 : Blo 2117435 3178313 := bstep (se 2 (by rfl) ⟨1191867, by rfl⟩ : syracuseStep 3178313 = 2383735) B2383735
theorem B2118875 : Blo 2117435 2118875 := bstep (se 1 (by rfl) ⟨1589156, by rfl⟩ : syracuseStep 2118875 = 3178313) B3178313
theorem B3394037 : Blo 2117435 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B2262691 : Blo 2117435 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B3016921 : Blo 2117435 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B4022561 : Blo 2117435 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B10726829 : Blo 2117435 10726829 := bstep (se 3 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 10726829 = 4022561) B4022561
theorem B7151219 : Blo 2117435 7151219 := bstep (se 1 (by rfl) ⟨5363414, by rfl⟩ : syracuseStep 7151219 = 10726829) B10726829
theorem B4767479 : Blo 2117435 4767479 := bstep (se 1 (by rfl) ⟨3575609, by rfl⟩ : syracuseStep 4767479 = 7151219) B7151219
theorem B3178319 : Blo 2117435 3178319 := bstep (se 1 (by rfl) ⟨2383739, by rfl⟩ : syracuseStep 3178319 = 4767479) B4767479
theorem B2118879 : Blo 2117435 2118879 := bstep (se 1 (by rfl) ⟨1589159, by rfl⟩ : syracuseStep 2118879 = 3178319) B3178319
theorem B3178325 : Blo 2117435 3178325 := bbase (se 9 (by rfl) ⟨9311, by rfl⟩ : syracuseStep 3178325 = 18623) (by norm_num)
theorem B2118883 : Blo 2117435 2118883 := bstep (se 1 (by rfl) ⟨1589162, by rfl⟩ : syracuseStep 2118883 = 3178325) B3178325
theorem B10182149 : Blo 2117435 10182149 := bbase (se 4 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 10182149 = 1909153) (by norm_num)
theorem B6788099 : Blo 2117435 6788099 := bstep (se 1 (by rfl) ⟨5091074, by rfl⟩ : syracuseStep 6788099 = 10182149) B10182149
theorem B4525399 : Blo 2117435 4525399 := bstep (se 1 (by rfl) ⟨3394049, by rfl⟩ : syracuseStep 4525399 = 6788099) B6788099
theorem B6033865 : Blo 2117435 6033865 := bstep (se 2 (by rfl) ⟨2262699, by rfl⟩ : syracuseStep 6033865 = 4525399) B4525399
theorem B8045153 : Blo 2117435 8045153 := bstep (se 2 (by rfl) ⟨3016932, by rfl⟩ : syracuseStep 8045153 = 6033865) B6033865
theorem B5363435 : Blo 2117435 5363435 := bstep (se 1 (by rfl) ⟨4022576, by rfl⟩ : syracuseStep 5363435 = 8045153) B8045153
theorem B3575623 : Blo 2117435 3575623 := bstep (se 1 (by rfl) ⟨2681717, by rfl⟩ : syracuseStep 3575623 = 5363435) B5363435
theorem B4767497 : Blo 2117435 4767497 := bstep (se 2 (by rfl) ⟨1787811, by rfl⟩ : syracuseStep 4767497 = 3575623) B3575623
theorem B3178331 : Blo 2117435 3178331 := bstep (se 1 (by rfl) ⟨2383748, by rfl⟩ : syracuseStep 3178331 = 4767497) B4767497
theorem B2118887 : Blo 2117435 2118887 := bstep (se 1 (by rfl) ⟨1589165, by rfl⟩ : syracuseStep 2118887 = 3178331) B3178331
theorem B2383753 : Blo 2117435 2383753 := bbase (se 2 (by rfl) ⟨893907, by rfl⟩ : syracuseStep 2383753 = 1787815) (by norm_num)
theorem B3178337 : Blo 2117435 3178337 := bstep (se 2 (by rfl) ⟨1191876, by rfl⟩ : syracuseStep 3178337 = 2383753) B2383753
theorem B2118891 : Blo 2117435 2118891 := bstep (se 1 (by rfl) ⟨1589168, by rfl⟩ : syracuseStep 2118891 = 3178337) B3178337
theorem B2580277 : Blo 2117435 2580277 := bbase (se 5 (by rfl) ⟨120950, by rfl⟩ : syracuseStep 2580277 = 241901) (by norm_num)
theorem B3440369 : Blo 2117435 3440369 := bstep (se 2 (by rfl) ⟨1290138, by rfl⟩ : syracuseStep 3440369 = 2580277) B2580277
theorem B2293579 : Blo 2117435 2293579 := bstep (se 1 (by rfl) ⟨1720184, by rfl⟩ : syracuseStep 2293579 = 3440369) B3440369
theorem B3058105 : Blo 2117435 3058105 := bstep (se 2 (by rfl) ⟨1146789, by rfl⟩ : syracuseStep 3058105 = 2293579) B2293579
theorem B260958293 : Blo 2117435 260958293 := bstep (se 8 (by rfl) ⟨1529052, by rfl⟩ : syracuseStep 260958293 = 3058105) B3058105
theorem B173972195 : Blo 2117435 173972195 := bstep (se 1 (by rfl) ⟨130479146, by rfl⟩ : syracuseStep 173972195 = 260958293) B260958293
theorem B115981463 : Blo 2117435 115981463 := bstep (se 1 (by rfl) ⟨86986097, by rfl⟩ : syracuseStep 115981463 = 173972195) B173972195
theorem B77320975 : Blo 2117435 77320975 := bstep (se 1 (by rfl) ⟨57990731, by rfl⟩ : syracuseStep 77320975 = 115981463) B115981463
theorem B103094633 : Blo 2117435 103094633 := bstep (se 2 (by rfl) ⟨38660487, by rfl⟩ : syracuseStep 103094633 = 77320975) B77320975
theorem B68729755 : Blo 2117435 68729755 := bstep (se 1 (by rfl) ⟨51547316, by rfl⟩ : syracuseStep 68729755 = 103094633) B103094633
theorem B91639673 : Blo 2117435 91639673 := bstep (se 2 (by rfl) ⟨34364877, by rfl⟩ : syracuseStep 91639673 = 68729755) B68729755
theorem B61093115 : Blo 2117435 61093115 := bstep (se 1 (by rfl) ⟨45819836, by rfl⟩ : syracuseStep 61093115 = 91639673) B91639673
theorem B40728743 : Blo 2117435 40728743 := bstep (se 1 (by rfl) ⟨30546557, by rfl⟩ : syracuseStep 40728743 = 61093115) B61093115
theorem B27152495 : Blo 2117435 27152495 := bstep (se 1 (by rfl) ⟨20364371, by rfl⟩ : syracuseStep 27152495 = 40728743) B40728743
theorem B18101663 : Blo 2117435 18101663 := bstep (se 1 (by rfl) ⟨13576247, by rfl⟩ : syracuseStep 18101663 = 27152495) B27152495
theorem B12067775 : Blo 2117435 12067775 := bstep (se 1 (by rfl) ⟨9050831, by rfl⟩ : syracuseStep 12067775 = 18101663) B18101663
theorem B8045183 : Blo 2117435 8045183 := bstep (se 1 (by rfl) ⟨6033887, by rfl⟩ : syracuseStep 8045183 = 12067775) B12067775
theorem B5363455 : Blo 2117435 5363455 := bstep (se 1 (by rfl) ⟨4022591, by rfl⟩ : syracuseStep 5363455 = 8045183) B8045183
theorem B7151273 : Blo 2117435 7151273 := bstep (se 2 (by rfl) ⟨2681727, by rfl⟩ : syracuseStep 7151273 = 5363455) B5363455
theorem B4767515 : Blo 2117435 4767515 := bstep (se 1 (by rfl) ⟨3575636, by rfl⟩ : syracuseStep 4767515 = 7151273) B7151273
theorem B3178343 : Blo 2117435 3178343 := bstep (se 1 (by rfl) ⟨2383757, by rfl⟩ : syracuseStep 3178343 = 4767515) B4767515
theorem B2118895 : Blo 2117435 2118895 := bstep (se 1 (by rfl) ⟨1589171, by rfl⟩ : syracuseStep 2118895 = 3178343) B3178343
theorem B3178349 : Blo 2117435 3178349 := bbase (se 3 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 3178349 = 1191881) (by norm_num)
theorem B2118899 : Blo 2117435 2118899 := bstep (se 1 (by rfl) ⟨1589174, by rfl⟩ : syracuseStep 2118899 = 3178349) B3178349
theorem B4767533 : Blo 2117435 4767533 := bbase (se 3 (by rfl) ⟨893912, by rfl⟩ : syracuseStep 4767533 = 1787825) (by norm_num)
theorem B3178355 : Blo 2117435 3178355 := bstep (se 1 (by rfl) ⟨2383766, by rfl⟩ : syracuseStep 3178355 = 4767533) B4767533
theorem B2118903 : Blo 2117435 2118903 := bstep (se 1 (by rfl) ⟨1589177, by rfl⟩ : syracuseStep 2118903 = 3178355) B3178355
theorem B9050885 : Blo 2117435 9050885 := bbase (se 4 (by rfl) ⟨848520, by rfl⟩ : syracuseStep 9050885 = 1697041) (by norm_num)
theorem B6033923 : Blo 2117435 6033923 := bstep (se 1 (by rfl) ⟨4525442, by rfl⟩ : syracuseStep 6033923 = 9050885) B9050885
theorem B4022615 : Blo 2117435 4022615 := bstep (se 1 (by rfl) ⟨3016961, by rfl⟩ : syracuseStep 4022615 = 6033923) B6033923
theorem B2681743 : Blo 2117435 2681743 := bstep (se 1 (by rfl) ⟨2011307, by rfl⟩ : syracuseStep 2681743 = 4022615) B4022615
theorem B3575657 : Blo 2117435 3575657 := bstep (se 2 (by rfl) ⟨1340871, by rfl⟩ : syracuseStep 3575657 = 2681743) B2681743
theorem B2383771 : Blo 2117435 2383771 := bstep (se 1 (by rfl) ⟨1787828, by rfl⟩ : syracuseStep 2383771 = 3575657) B3575657
theorem B3178361 : Blo 2117435 3178361 := bstep (se 2 (by rfl) ⟨1191885, by rfl⟩ : syracuseStep 3178361 = 2383771) B2383771
theorem B2118907 : Blo 2117435 2118907 := bstep (se 1 (by rfl) ⟨1589180, by rfl⟩ : syracuseStep 2118907 = 3178361) B3178361
theorem B8591285 : Blo 2117435 8591285 := bbase (se 5 (by rfl) ⟨402716, by rfl⟩ : syracuseStep 8591285 = 805433) (by norm_num)
theorem B5727523 : Blo 2117435 5727523 := bstep (se 1 (by rfl) ⟨4295642, by rfl⟩ : syracuseStep 5727523 = 8591285) B8591285
theorem B7636697 : Blo 2117435 7636697 := bstep (se 2 (by rfl) ⟨2863761, by rfl⟩ : syracuseStep 7636697 = 5727523) B5727523
theorem B5091131 : Blo 2117435 5091131 := bstep (se 1 (by rfl) ⟨3818348, by rfl⟩ : syracuseStep 5091131 = 7636697) B7636697
theorem B13576349 : Blo 2117435 13576349 := bstep (se 3 (by rfl) ⟨2545565, by rfl⟩ : syracuseStep 13576349 = 5091131) B5091131
theorem B36203597 : Blo 2117435 36203597 := bstep (se 3 (by rfl) ⟨6788174, by rfl⟩ : syracuseStep 36203597 = 13576349) B13576349
theorem B24135731 : Blo 2117435 24135731 := bstep (se 1 (by rfl) ⟨18101798, by rfl⟩ : syracuseStep 24135731 = 36203597) B36203597
theorem B16090487 : Blo 2117435 16090487 := bstep (se 1 (by rfl) ⟨12067865, by rfl⟩ : syracuseStep 16090487 = 24135731) B24135731
theorem B10726991 : Blo 2117435 10726991 := bstep (se 1 (by rfl) ⟨8045243, by rfl⟩ : syracuseStep 10726991 = 16090487) B16090487
theorem B7151327 : Blo 2117435 7151327 := bstep (se 1 (by rfl) ⟨5363495, by rfl⟩ : syracuseStep 7151327 = 10726991) B10726991
theorem B4767551 : Blo 2117435 4767551 := bstep (se 1 (by rfl) ⟨3575663, by rfl⟩ : syracuseStep 4767551 = 7151327) B7151327
theorem B3178367 : Blo 2117435 3178367 := bstep (se 1 (by rfl) ⟨2383775, by rfl⟩ : syracuseStep 3178367 = 4767551) B4767551
theorem B2118911 : Blo 2117435 2118911 := bstep (se 1 (by rfl) ⟨1589183, by rfl⟩ : syracuseStep 2118911 = 3178367) B3178367
theorem B3178373 : Blo 2117435 3178373 := bbase (se 4 (by rfl) ⟨297972, by rfl⟩ : syracuseStep 3178373 = 595945) (by norm_num)
theorem B2118915 : Blo 2117435 2118915 := bstep (se 1 (by rfl) ⟨1589186, by rfl⟩ : syracuseStep 2118915 = 3178373) B3178373
theorem B3575677 : Blo 2117435 3575677 := bbase (se 3 (by rfl) ⟨670439, by rfl⟩ : syracuseStep 3575677 = 1340879) (by norm_num)
theorem B4767569 : Blo 2117435 4767569 := bstep (se 2 (by rfl) ⟨1787838, by rfl⟩ : syracuseStep 4767569 = 3575677) B3575677
theorem B3178379 : Blo 2117435 3178379 := bstep (se 1 (by rfl) ⟨2383784, by rfl⟩ : syracuseStep 3178379 = 4767569) B4767569
theorem B2118919 : Blo 2117435 2118919 := bstep (se 1 (by rfl) ⟨1589189, by rfl⟩ : syracuseStep 2118919 = 3178379) B3178379
theorem B2383789 : Blo 2117435 2383789 := bbase (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) (by norm_num)
theorem B3178385 : Blo 2117435 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B2118923 : Blo 2117435 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B7151381 : Blo 2117435 7151381 := bbase (se 6 (by rfl) ⟨167610, by rfl⟩ : syracuseStep 7151381 = 335221) (by norm_num)
theorem B4767587 : Blo 2117435 4767587 := bstep (se 1 (by rfl) ⟨3575690, by rfl⟩ : syracuseStep 4767587 = 7151381) B7151381
theorem B3178391 : Blo 2117435 3178391 := bstep (se 1 (by rfl) ⟨2383793, by rfl⟩ : syracuseStep 3178391 = 4767587) B4767587
theorem B2118927 : Blo 2117435 2118927 := bstep (se 1 (by rfl) ⟨1589195, by rfl⟩ : syracuseStep 2118927 = 3178391) B3178391
theorem B3178397 : Blo 2117435 3178397 := bbase (se 3 (by rfl) ⟨595949, by rfl⟩ : syracuseStep 3178397 = 1191899) (by norm_num)
theorem B2118931 : Blo 2117435 2118931 := bstep (se 1 (by rfl) ⟨1589198, by rfl⟩ : syracuseStep 2118931 = 3178397) B3178397
theorem B4767605 : Blo 2117435 4767605 := bbase (se 5 (by rfl) ⟨223481, by rfl⟩ : syracuseStep 4767605 = 446963) (by norm_num)
theorem B3178403 : Blo 2117435 3178403 := bstep (se 1 (by rfl) ⟨2383802, by rfl⟩ : syracuseStep 3178403 = 4767605) B4767605
theorem B2118935 : Blo 2117435 2118935 := bstep (se 1 (by rfl) ⟨1589201, by rfl⟩ : syracuseStep 2118935 = 3178403) B3178403
theorem B3265733 : Blo 2117435 3265733 := bbase (se 4 (by rfl) ⟨306162, by rfl⟩ : syracuseStep 3265733 = 612325) (by norm_num)
theorem B2177155 : Blo 2117435 2177155 := bstep (se 1 (by rfl) ⟨1632866, by rfl⟩ : syracuseStep 2177155 = 3265733) B3265733
theorem B2902873 : Blo 2117435 2902873 := bstep (se 2 (by rfl) ⟨1088577, by rfl⟩ : syracuseStep 2902873 = 2177155) B2177155
theorem B3870497 : Blo 2117435 3870497 := bstep (se 2 (by rfl) ⟨1451436, by rfl⟩ : syracuseStep 3870497 = 2902873) B2902873
theorem B2580331 : Blo 2117435 2580331 := bstep (se 1 (by rfl) ⟨1935248, by rfl⟩ : syracuseStep 2580331 = 3870497) B3870497
theorem B3440441 : Blo 2117435 3440441 := bstep (se 2 (by rfl) ⟨1290165, by rfl⟩ : syracuseStep 3440441 = 2580331) B2580331
theorem B9174509 : Blo 2117435 9174509 := bstep (se 3 (by rfl) ⟨1720220, by rfl⟩ : syracuseStep 9174509 = 3440441) B3440441
theorem B6116339 : Blo 2117435 6116339 := bstep (se 1 (by rfl) ⟨4587254, by rfl⟩ : syracuseStep 6116339 = 9174509) B9174509
theorem B4077559 : Blo 2117435 4077559 := bstep (se 1 (by rfl) ⟨3058169, by rfl⟩ : syracuseStep 4077559 = 6116339) B6116339
theorem B21746981 : Blo 2117435 21746981 := bstep (se 4 (by rfl) ⟨2038779, by rfl⟩ : syracuseStep 21746981 = 4077559) B4077559
theorem B57991949 : Blo 2117435 57991949 := bstep (se 3 (by rfl) ⟨10873490, by rfl⟩ : syracuseStep 57991949 = 21746981) B21746981
theorem B38661299 : Blo 2117435 38661299 := bstep (se 1 (by rfl) ⟨28995974, by rfl⟩ : syracuseStep 38661299 = 57991949) B57991949
theorem B25774199 : Blo 2117435 25774199 := bstep (se 1 (by rfl) ⟨19330649, by rfl⟩ : syracuseStep 25774199 = 38661299) B38661299
theorem B17182799 : Blo 2117435 17182799 := bstep (se 1 (by rfl) ⟨12887099, by rfl⟩ : syracuseStep 17182799 = 25774199) B25774199
theorem B11455199 : Blo 2117435 11455199 := bstep (se 1 (by rfl) ⟨8591399, by rfl⟩ : syracuseStep 11455199 = 17182799) B17182799
theorem B7636799 : Blo 2117435 7636799 := bstep (se 1 (by rfl) ⟨5727599, by rfl⟩ : syracuseStep 7636799 = 11455199) B11455199
theorem B20364797 : Blo 2117435 20364797 := bstep (se 3 (by rfl) ⟨3818399, by rfl⟩ : syracuseStep 20364797 = 7636799) B7636799
theorem B13576531 : Blo 2117435 13576531 := bstep (se 1 (by rfl) ⟨10182398, by rfl⟩ : syracuseStep 13576531 = 20364797) B20364797
theorem B18102041 : Blo 2117435 18102041 := bstep (se 2 (by rfl) ⟨6788265, by rfl⟩ : syracuseStep 18102041 = 13576531) B13576531
theorem B12068027 : Blo 2117435 12068027 := bstep (se 1 (by rfl) ⟨9051020, by rfl⟩ : syracuseStep 12068027 = 18102041) B18102041
theorem B8045351 : Blo 2117435 8045351 := bstep (se 1 (by rfl) ⟨6034013, by rfl⟩ : syracuseStep 8045351 = 12068027) B12068027
theorem B5363567 : Blo 2117435 5363567 := bstep (se 1 (by rfl) ⟨4022675, by rfl⟩ : syracuseStep 5363567 = 8045351) B8045351
theorem B3575711 : Blo 2117435 3575711 := bstep (se 1 (by rfl) ⟨2681783, by rfl⟩ : syracuseStep 3575711 = 5363567) B5363567
theorem B2383807 : Blo 2117435 2383807 := bstep (se 1 (by rfl) ⟨1787855, by rfl⟩ : syracuseStep 2383807 = 3575711) B3575711
theorem B3178409 : Blo 2117435 3178409 := bstep (se 2 (by rfl) ⟨1191903, by rfl⟩ : syracuseStep 3178409 = 2383807) B2383807
theorem B2118939 : Blo 2117435 2118939 := bstep (se 1 (by rfl) ⟨1589204, by rfl⟩ : syracuseStep 2118939 = 3178409) B3178409
theorem B8045365 : Blo 2117435 8045365 := bbase (se 5 (by rfl) ⟨377126, by rfl⟩ : syracuseStep 8045365 = 754253) (by norm_num)
theorem B10727153 : Blo 2117435 10727153 := bstep (se 2 (by rfl) ⟨4022682, by rfl⟩ : syracuseStep 10727153 = 8045365) B8045365
theorem B7151435 : Blo 2117435 7151435 := bstep (se 1 (by rfl) ⟨5363576, by rfl⟩ : syracuseStep 7151435 = 10727153) B10727153
theorem B4767623 : Blo 2117435 4767623 := bstep (se 1 (by rfl) ⟨3575717, by rfl⟩ : syracuseStep 4767623 = 7151435) B7151435
theorem B3178415 : Blo 2117435 3178415 := bstep (se 1 (by rfl) ⟨2383811, by rfl⟩ : syracuseStep 3178415 = 4767623) B4767623
theorem B2118943 : Blo 2117435 2118943 := bstep (se 1 (by rfl) ⟨1589207, by rfl⟩ : syracuseStep 2118943 = 3178415) B3178415
theorem B3178421 : Blo 2117435 3178421 := bbase (se 5 (by rfl) ⟨148988, by rfl⟩ : syracuseStep 3178421 = 297977) (by norm_num)
theorem B2118947 : Blo 2117435 2118947 := bstep (se 1 (by rfl) ⟨1589210, by rfl⟩ : syracuseStep 2118947 = 3178421) B3178421
theorem B5363597 : Blo 2117435 5363597 := bbase (se 3 (by rfl) ⟨1005674, by rfl⟩ : syracuseStep 5363597 = 2011349) (by norm_num)
theorem B3575731 : Blo 2117435 3575731 := bstep (se 1 (by rfl) ⟨2681798, by rfl⟩ : syracuseStep 3575731 = 5363597) B5363597
theorem B4767641 : Blo 2117435 4767641 := bstep (se 2 (by rfl) ⟨1787865, by rfl⟩ : syracuseStep 4767641 = 3575731) B3575731
theorem B3178427 : Blo 2117435 3178427 := bstep (se 1 (by rfl) ⟨2383820, by rfl⟩ : syracuseStep 3178427 = 4767641) B4767641
theorem B2118951 : Blo 2117435 2118951 := bstep (se 1 (by rfl) ⟨1589213, by rfl⟩ : syracuseStep 2118951 = 3178427) B3178427
theorem B2383825 : Blo 2117435 2383825 := bbase (se 2 (by rfl) ⟨893934, by rfl⟩ : syracuseStep 2383825 = 1787869) (by norm_num)
theorem B3178433 : Blo 2117435 3178433 := bstep (se 2 (by rfl) ⟨1191912, by rfl⟩ : syracuseStep 3178433 = 2383825) B2383825
theorem B2118955 : Blo 2117435 2118955 := bstep (se 1 (by rfl) ⟨1589216, by rfl⟩ : syracuseStep 2118955 = 3178433) B3178433
theorem B3394165 : Blo 2117435 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B4525553 : Blo 2117435 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B3017035 : Blo 2117435 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B4022713 : Blo 2117435 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B5363617 : Blo 2117435 5363617 := bstep (se 2 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 5363617 = 4022713) B4022713
theorem B7151489 : Blo 2117435 7151489 := bstep (se 2 (by rfl) ⟨2681808, by rfl⟩ : syracuseStep 7151489 = 5363617) B5363617
theorem B4767659 : Blo 2117435 4767659 := bstep (se 1 (by rfl) ⟨3575744, by rfl⟩ : syracuseStep 4767659 = 7151489) B7151489
theorem B3178439 : Blo 2117435 3178439 := bstep (se 1 (by rfl) ⟨2383829, by rfl⟩ : syracuseStep 3178439 = 4767659) B4767659
theorem B2118959 : Blo 2117435 2118959 := bstep (se 1 (by rfl) ⟨1589219, by rfl⟩ : syracuseStep 2118959 = 3178439) B3178439
theorem B3178445 : Blo 2117435 3178445 := bbase (se 3 (by rfl) ⟨595958, by rfl⟩ : syracuseStep 3178445 = 1191917) (by norm_num)
theorem B2118963 : Blo 2117435 2118963 := bstep (se 1 (by rfl) ⟨1589222, by rfl⟩ : syracuseStep 2118963 = 3178445) B3178445
theorem B4767677 : Blo 2117435 4767677 := bbase (se 3 (by rfl) ⟨893939, by rfl⟩ : syracuseStep 4767677 = 1787879) (by norm_num)
theorem B3178451 : Blo 2117435 3178451 := bstep (se 1 (by rfl) ⟨2383838, by rfl⟩ : syracuseStep 3178451 = 4767677) B4767677
theorem B2118967 : Blo 2117435 2118967 := bstep (se 1 (by rfl) ⟨1589225, by rfl⟩ : syracuseStep 2118967 = 3178451) B3178451
theorem B3575765 : Blo 2117435 3575765 := bbase (se 7 (by rfl) ⟨41903, by rfl⟩ : syracuseStep 3575765 = 83807) (by norm_num)
theorem B2383843 : Blo 2117435 2383843 := bstep (se 1 (by rfl) ⟨1787882, by rfl⟩ : syracuseStep 2383843 = 3575765) B3575765
theorem B3178457 : Blo 2117435 3178457 := bstep (se 2 (by rfl) ⟨1191921, by rfl⟩ : syracuseStep 3178457 = 2383843) B2383843
theorem B2118971 : Blo 2117435 2118971 := bstep (se 1 (by rfl) ⟨1589228, by rfl⟩ : syracuseStep 2118971 = 3178457) B3178457
theorem B9051173 : Blo 2117435 9051173 := bbase (se 4 (by rfl) ⟨848547, by rfl⟩ : syracuseStep 9051173 = 1697095) (by norm_num)
theorem B6034115 : Blo 2117435 6034115 := bstep (se 1 (by rfl) ⟨4525586, by rfl⟩ : syracuseStep 6034115 = 9051173) B9051173
theorem B16090973 : Blo 2117435 16090973 := bstep (se 3 (by rfl) ⟨3017057, by rfl⟩ : syracuseStep 16090973 = 6034115) B6034115
theorem B10727315 : Blo 2117435 10727315 := bstep (se 1 (by rfl) ⟨8045486, by rfl⟩ : syracuseStep 10727315 = 16090973) B16090973
theorem B7151543 : Blo 2117435 7151543 := bstep (se 1 (by rfl) ⟨5363657, by rfl⟩ : syracuseStep 7151543 = 10727315) B10727315
theorem B4767695 : Blo 2117435 4767695 := bstep (se 1 (by rfl) ⟨3575771, by rfl⟩ : syracuseStep 4767695 = 7151543) B7151543
theorem B3178463 : Blo 2117435 3178463 := bstep (se 1 (by rfl) ⟨2383847, by rfl⟩ : syracuseStep 3178463 = 4767695) B4767695
theorem B2118975 : Blo 2117435 2118975 := bstep (se 1 (by rfl) ⟨1589231, by rfl⟩ : syracuseStep 2118975 = 3178463) B3178463
theorem B3178469 : Blo 2117435 3178469 := bbase (se 4 (by rfl) ⟨297981, by rfl⟩ : syracuseStep 3178469 = 595963) (by norm_num)
theorem B2118979 : Blo 2117435 2118979 := bstep (se 1 (by rfl) ⟨1589234, by rfl⟩ : syracuseStep 2118979 = 3178469) B3178469
theorem B2580385 : Blo 2117435 2580385 := bbase (se 2 (by rfl) ⟨967644, by rfl⟩ : syracuseStep 2580385 = 1935289) (by norm_num)
theorem B3440513 : Blo 2117435 3440513 := bstep (se 2 (by rfl) ⟨1290192, by rfl⟩ : syracuseStep 3440513 = 2580385) B2580385
theorem B9174701 : Blo 2117435 9174701 := bstep (se 3 (by rfl) ⟨1720256, by rfl⟩ : syracuseStep 9174701 = 3440513) B3440513
theorem B6116467 : Blo 2117435 6116467 := bstep (se 1 (by rfl) ⟨4587350, by rfl⟩ : syracuseStep 6116467 = 9174701) B9174701
theorem B8155289 : Blo 2117435 8155289 := bstep (se 2 (by rfl) ⟨3058233, by rfl⟩ : syracuseStep 8155289 = 6116467) B6116467
theorem B21747437 : Blo 2117435 21747437 := bstep (se 3 (by rfl) ⟨4077644, by rfl⟩ : syracuseStep 21747437 = 8155289) B8155289
theorem B14498291 : Blo 2117435 14498291 := bstep (se 1 (by rfl) ⟨10873718, by rfl⟩ : syracuseStep 14498291 = 21747437) B21747437
theorem B9665527 : Blo 2117435 9665527 := bstep (se 1 (by rfl) ⟨7249145, by rfl⟩ : syracuseStep 9665527 = 14498291) B14498291
theorem B12887369 : Blo 2117435 12887369 := bstep (se 2 (by rfl) ⟨4832763, by rfl⟩ : syracuseStep 12887369 = 9665527) B9665527
theorem B8591579 : Blo 2117435 8591579 := bstep (se 1 (by rfl) ⟨6443684, by rfl⟩ : syracuseStep 8591579 = 12887369) B12887369
theorem B5727719 : Blo 2117435 5727719 := bstep (se 1 (by rfl) ⟨4295789, by rfl⟩ : syracuseStep 5727719 = 8591579) B8591579
theorem B15273917 : Blo 2117435 15273917 := bstep (se 3 (by rfl) ⟨2863859, by rfl⟩ : syracuseStep 15273917 = 5727719) B5727719
theorem B10182611 : Blo 2117435 10182611 := bstep (se 1 (by rfl) ⟨7636958, by rfl⟩ : syracuseStep 10182611 = 15273917) B15273917
theorem B6788407 : Blo 2117435 6788407 := bstep (se 1 (by rfl) ⟨5091305, by rfl⟩ : syracuseStep 6788407 = 10182611) B10182611
theorem B9051209 : Blo 2117435 9051209 := bstep (se 2 (by rfl) ⟨3394203, by rfl⟩ : syracuseStep 9051209 = 6788407) B6788407
theorem B6034139 : Blo 2117435 6034139 := bstep (se 1 (by rfl) ⟨4525604, by rfl⟩ : syracuseStep 6034139 = 9051209) B9051209
theorem B4022759 : Blo 2117435 4022759 := bstep (se 1 (by rfl) ⟨3017069, by rfl⟩ : syracuseStep 4022759 = 6034139) B6034139
theorem B2681839 : Blo 2117435 2681839 := bstep (se 1 (by rfl) ⟨2011379, by rfl⟩ : syracuseStep 2681839 = 4022759) B4022759
theorem B3575785 : Blo 2117435 3575785 := bstep (se 2 (by rfl) ⟨1340919, by rfl⟩ : syracuseStep 3575785 = 2681839) B2681839
theorem B4767713 : Blo 2117435 4767713 := bstep (se 2 (by rfl) ⟨1787892, by rfl⟩ : syracuseStep 4767713 = 3575785) B3575785
theorem B3178475 : Blo 2117435 3178475 := bstep (se 1 (by rfl) ⟨2383856, by rfl⟩ : syracuseStep 3178475 = 4767713) B4767713
theorem B2118983 : Blo 2117435 2118983 := bstep (se 1 (by rfl) ⟨1589237, by rfl⟩ : syracuseStep 2118983 = 3178475) B3178475
theorem B2383861 : Blo 2117435 2383861 := bbase (se 5 (by rfl) ⟨111743, by rfl⟩ : syracuseStep 2383861 = 223487) (by norm_num)
theorem B3178481 : Blo 2117435 3178481 := bstep (se 2 (by rfl) ⟨1191930, by rfl⟩ : syracuseStep 3178481 = 2383861) B2383861
theorem B2118987 : Blo 2117435 2118987 := bstep (se 1 (by rfl) ⟨1589240, by rfl⟩ : syracuseStep 2118987 = 3178481) B3178481
theorem B2681849 : Blo 2117435 2681849 := bbase (se 2 (by rfl) ⟨1005693, by rfl⟩ : syracuseStep 2681849 = 2011387) (by norm_num)
theorem B7151597 : Blo 2117435 7151597 := bstep (se 3 (by rfl) ⟨1340924, by rfl⟩ : syracuseStep 7151597 = 2681849) B2681849
theorem B4767731 : Blo 2117435 4767731 := bstep (se 1 (by rfl) ⟨3575798, by rfl⟩ : syracuseStep 4767731 = 7151597) B7151597
theorem B3178487 : Blo 2117435 3178487 := bstep (se 1 (by rfl) ⟨2383865, by rfl⟩ : syracuseStep 3178487 = 4767731) B4767731
theorem B2118991 : Blo 2117435 2118991 := bstep (se 1 (by rfl) ⟨1589243, by rfl⟩ : syracuseStep 2118991 = 3178487) B3178487
theorem B3178493 : Blo 2117435 3178493 := bbase (se 3 (by rfl) ⟨595967, by rfl⟩ : syracuseStep 3178493 = 1191935) (by norm_num)
theorem B2118995 : Blo 2117435 2118995 := bstep (se 1 (by rfl) ⟨1589246, by rfl⟩ : syracuseStep 2118995 = 3178493) B3178493
theorem B4767749 : Blo 2117435 4767749 := bbase (se 4 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 4767749 = 893953) (by norm_num)
theorem B3178499 : Blo 2117435 3178499 := bstep (se 1 (by rfl) ⟨2383874, by rfl⟩ : syracuseStep 3178499 = 4767749) B4767749
theorem B2118999 : Blo 2117435 2118999 := bstep (se 1 (by rfl) ⟨1589249, by rfl⟩ : syracuseStep 2118999 = 3178499) B3178499
theorem B4022797 : Blo 2117435 4022797 := bbase (se 3 (by rfl) ⟨754274, by rfl⟩ : syracuseStep 4022797 = 1508549) (by norm_num)
theorem B5363729 : Blo 2117435 5363729 := bstep (se 2 (by rfl) ⟨2011398, by rfl⟩ : syracuseStep 5363729 = 4022797) B4022797
theorem B3575819 : Blo 2117435 3575819 := bstep (se 1 (by rfl) ⟨2681864, by rfl⟩ : syracuseStep 3575819 = 5363729) B5363729
theorem B2383879 : Blo 2117435 2383879 := bstep (se 1 (by rfl) ⟨1787909, by rfl⟩ : syracuseStep 2383879 = 3575819) B3575819
theorem B3178505 : Blo 2117435 3178505 := bstep (se 2 (by rfl) ⟨1191939, by rfl⟩ : syracuseStep 3178505 = 2383879) B2383879
theorem B2119003 : Blo 2117435 2119003 := bstep (se 1 (by rfl) ⟨1589252, by rfl⟩ : syracuseStep 2119003 = 3178505) B3178505
theorem B10727477 : Blo 2117435 10727477 := bbase (se 5 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 10727477 = 1005701) (by norm_num)
theorem B7151651 : Blo 2117435 7151651 := bstep (se 1 (by rfl) ⟨5363738, by rfl⟩ : syracuseStep 7151651 = 10727477) B10727477
theorem B4767767 : Blo 2117435 4767767 := bstep (se 1 (by rfl) ⟨3575825, by rfl⟩ : syracuseStep 4767767 = 7151651) B7151651
theorem B3178511 : Blo 2117435 3178511 := bstep (se 1 (by rfl) ⟨2383883, by rfl⟩ : syracuseStep 3178511 = 4767767) B4767767
theorem B2119007 : Blo 2117435 2119007 := bstep (se 1 (by rfl) ⟨1589255, by rfl⟩ : syracuseStep 2119007 = 3178511) B3178511
theorem B3178517 : Blo 2117435 3178517 := bbase (se 6 (by rfl) ⟨74496, by rfl⟩ : syracuseStep 3178517 = 148993) (by norm_num)
theorem B2119011 : Blo 2117435 2119011 := bstep (se 1 (by rfl) ⟨1589258, by rfl⟩ : syracuseStep 2119011 = 3178517) B3178517
theorem B2755561 : Blo 2117435 2755561 := bbase (se 2 (by rfl) ⟨1033335, by rfl⟩ : syracuseStep 2755561 = 2066671) (by norm_num)
theorem B3674081 : Blo 2117435 3674081 := bstep (se 2 (by rfl) ⟨1377780, by rfl⟩ : syracuseStep 3674081 = 2755561) B2755561
theorem B2449387 : Blo 2117435 2449387 := bstep (se 1 (by rfl) ⟨1837040, by rfl⟩ : syracuseStep 2449387 = 3674081) B3674081
theorem B3265849 : Blo 2117435 3265849 := bstep (se 2 (by rfl) ⟨1224693, by rfl⟩ : syracuseStep 3265849 = 2449387) B2449387
theorem B17417861 : Blo 2117435 17417861 := bstep (se 4 (by rfl) ⟨1632924, by rfl⟩ : syracuseStep 17417861 = 3265849) B3265849
theorem B11611907 : Blo 2117435 11611907 := bstep (se 1 (by rfl) ⟨8708930, by rfl⟩ : syracuseStep 11611907 = 17417861) B17417861
theorem B7741271 : Blo 2117435 7741271 := bstep (se 1 (by rfl) ⟨5805953, by rfl⟩ : syracuseStep 7741271 = 11611907) B11611907
theorem B5160847 : Blo 2117435 5160847 := bstep (se 1 (by rfl) ⟨3870635, by rfl⟩ : syracuseStep 5160847 = 7741271) B7741271
theorem B6881129 : Blo 2117435 6881129 := bstep (se 2 (by rfl) ⟨2580423, by rfl⟩ : syracuseStep 6881129 = 5160847) B5160847
theorem B4587419 : Blo 2117435 4587419 := bstep (se 1 (by rfl) ⟨3440564, by rfl⟩ : syracuseStep 4587419 = 6881129) B6881129
theorem B3058279 : Blo 2117435 3058279 := bstep (se 1 (by rfl) ⟨2293709, by rfl⟩ : syracuseStep 3058279 = 4587419) B4587419
theorem B16310821 : Blo 2117435 16310821 := bstep (se 4 (by rfl) ⟨1529139, by rfl⟩ : syracuseStep 16310821 = 3058279) B3058279
theorem B21747761 : Blo 2117435 21747761 := bstep (se 2 (by rfl) ⟨8155410, by rfl⟩ : syracuseStep 21747761 = 16310821) B16310821
theorem B14498507 : Blo 2117435 14498507 := bstep (se 1 (by rfl) ⟨10873880, by rfl⟩ : syracuseStep 14498507 = 21747761) B21747761
theorem B9665671 : Blo 2117435 9665671 := bstep (se 1 (by rfl) ⟨7249253, by rfl⟩ : syracuseStep 9665671 = 14498507) B14498507
theorem B12887561 : Blo 2117435 12887561 := bstep (se 2 (by rfl) ⟨4832835, by rfl⟩ : syracuseStep 12887561 = 9665671) B9665671
theorem B8591707 : Blo 2117435 8591707 := bstep (se 1 (by rfl) ⟨6443780, by rfl⟩ : syracuseStep 8591707 = 12887561) B12887561
theorem B11455609 : Blo 2117435 11455609 := bstep (se 2 (by rfl) ⟨4295853, by rfl⟩ : syracuseStep 11455609 = 8591707) B8591707
theorem B15274145 : Blo 2117435 15274145 := bstep (se 2 (by rfl) ⟨5727804, by rfl⟩ : syracuseStep 15274145 = 11455609) B11455609
theorem B10182763 : Blo 2117435 10182763 := bstep (se 1 (by rfl) ⟨7637072, by rfl⟩ : syracuseStep 10182763 = 15274145) B15274145
theorem B13577017 : Blo 2117435 13577017 := bstep (se 2 (by rfl) ⟨5091381, by rfl⟩ : syracuseStep 13577017 = 10182763) B10182763
theorem B18102689 : Blo 2117435 18102689 := bstep (se 2 (by rfl) ⟨6788508, by rfl⟩ : syracuseStep 18102689 = 13577017) B13577017
theorem B12068459 : Blo 2117435 12068459 := bstep (se 1 (by rfl) ⟨9051344, by rfl⟩ : syracuseStep 12068459 = 18102689) B18102689
theorem B8045639 : Blo 2117435 8045639 := bstep (se 1 (by rfl) ⟨6034229, by rfl⟩ : syracuseStep 8045639 = 12068459) B12068459
theorem B5363759 : Blo 2117435 5363759 := bstep (se 1 (by rfl) ⟨4022819, by rfl⟩ : syracuseStep 5363759 = 8045639) B8045639
theorem B3575839 : Blo 2117435 3575839 := bstep (se 1 (by rfl) ⟨2681879, by rfl⟩ : syracuseStep 3575839 = 5363759) B5363759
theorem B4767785 : Blo 2117435 4767785 := bstep (se 2 (by rfl) ⟨1787919, by rfl⟩ : syracuseStep 4767785 = 3575839) B3575839
theorem B3178523 : Blo 2117435 3178523 := bstep (se 1 (by rfl) ⟨2383892, by rfl⟩ : syracuseStep 3178523 = 4767785) B4767785
theorem B2119015 : Blo 2117435 2119015 := bstep (se 1 (by rfl) ⟨1589261, by rfl⟩ : syracuseStep 2119015 = 3178523) B3178523
theorem B2383897 : Blo 2117435 2383897 := bbase (se 2 (by rfl) ⟨893961, by rfl⟩ : syracuseStep 2383897 = 1787923) (by norm_num)
theorem B3178529 : Blo 2117435 3178529 := bstep (se 2 (by rfl) ⟨1191948, by rfl⟩ : syracuseStep 3178529 = 2383897) B2383897
theorem B2119019 : Blo 2117435 2119019 := bstep (se 1 (by rfl) ⟨1589264, by rfl⟩ : syracuseStep 2119019 = 3178529) B3178529
theorem B8045669 : Blo 2117435 8045669 := bbase (se 4 (by rfl) ⟨754281, by rfl⟩ : syracuseStep 8045669 = 1508563) (by norm_num)
theorem B5363779 : Blo 2117435 5363779 := bstep (se 1 (by rfl) ⟨4022834, by rfl⟩ : syracuseStep 5363779 = 8045669) B8045669
theorem B7151705 : Blo 2117435 7151705 := bstep (se 2 (by rfl) ⟨2681889, by rfl⟩ : syracuseStep 7151705 = 5363779) B5363779
theorem B4767803 : Blo 2117435 4767803 := bstep (se 1 (by rfl) ⟨3575852, by rfl⟩ : syracuseStep 4767803 = 7151705) B7151705
theorem B3178535 : Blo 2117435 3178535 := bstep (se 1 (by rfl) ⟨2383901, by rfl⟩ : syracuseStep 3178535 = 4767803) B4767803
theorem B2119023 : Blo 2117435 2119023 := bstep (se 1 (by rfl) ⟨1589267, by rfl⟩ : syracuseStep 2119023 = 3178535) B3178535
theorem B3178541 : Blo 2117435 3178541 := bbase (se 3 (by rfl) ⟨595976, by rfl⟩ : syracuseStep 3178541 = 1191953) (by norm_num)
theorem B2119027 : Blo 2117435 2119027 := bstep (se 1 (by rfl) ⟨1589270, by rfl⟩ : syracuseStep 2119027 = 3178541) B3178541
theorem B4767821 : Blo 2117435 4767821 := bbase (se 3 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 4767821 = 1787933) (by norm_num)
theorem B3178547 : Blo 2117435 3178547 := bstep (se 1 (by rfl) ⟨2383910, by rfl⟩ : syracuseStep 3178547 = 4767821) B4767821
theorem B2119031 : Blo 2117435 2119031 := bstep (se 1 (by rfl) ⟨1589273, by rfl⟩ : syracuseStep 2119031 = 3178547) B3178547
theorem B2681905 : Blo 2117435 2681905 := bbase (se 2 (by rfl) ⟨1005714, by rfl⟩ : syracuseStep 2681905 = 2011429) (by norm_num)
theorem B3575873 : Blo 2117435 3575873 := bstep (se 2 (by rfl) ⟨1340952, by rfl⟩ : syracuseStep 3575873 = 2681905) B2681905
theorem B2383915 : Blo 2117435 2383915 := bstep (se 1 (by rfl) ⟨1787936, by rfl⟩ : syracuseStep 2383915 = 3575873) B3575873
theorem B3178553 : Blo 2117435 3178553 := bstep (se 2 (by rfl) ⟨1191957, by rfl⟩ : syracuseStep 3178553 = 2383915) B2383915
theorem B2119035 : Blo 2117435 2119035 := bstep (se 1 (by rfl) ⟨1589276, by rfl⟩ : syracuseStep 2119035 = 3178553) B3178553
theorem B3265885 : Blo 2117435 3265885 := bbase (se 3 (by rfl) ⟨612353, by rfl⟩ : syracuseStep 3265885 = 1224707) (by norm_num)
theorem B17418053 : Blo 2117435 17418053 := bstep (se 4 (by rfl) ⟨1632942, by rfl⟩ : syracuseStep 17418053 = 3265885) B3265885
theorem B11612035 : Blo 2117435 11612035 := bstep (se 1 (by rfl) ⟨8709026, by rfl⟩ : syracuseStep 11612035 = 17418053) B17418053
theorem B15482713 : Blo 2117435 15482713 := bstep (se 2 (by rfl) ⟨5806017, by rfl⟩ : syracuseStep 15482713 = 11612035) B11612035
theorem B20643617 : Blo 2117435 20643617 := bstep (se 2 (by rfl) ⟨7741356, by rfl⟩ : syracuseStep 20643617 = 15482713) B15482713
theorem B55049645 : Blo 2117435 55049645 := bstep (se 3 (by rfl) ⟨10321808, by rfl⟩ : syracuseStep 55049645 = 20643617) B20643617
theorem B36699763 : Blo 2117435 36699763 := bstep (se 1 (by rfl) ⟨27524822, by rfl⟩ : syracuseStep 36699763 = 55049645) B55049645
theorem B48933017 : Blo 2117435 48933017 := bstep (se 2 (by rfl) ⟨18349881, by rfl⟩ : syracuseStep 48933017 = 36699763) B36699763
theorem B32622011 : Blo 2117435 32622011 := bstep (se 1 (by rfl) ⟨24466508, by rfl⟩ : syracuseStep 32622011 = 48933017) B48933017
theorem B21748007 : Blo 2117435 21748007 := bstep (se 1 (by rfl) ⟨16311005, by rfl⟩ : syracuseStep 21748007 = 32622011) B32622011
theorem B14498671 : Blo 2117435 14498671 := bstep (se 1 (by rfl) ⟨10874003, by rfl⟩ : syracuseStep 14498671 = 21748007) B21748007
theorem B19331561 : Blo 2117435 19331561 := bstep (se 2 (by rfl) ⟨7249335, by rfl⟩ : syracuseStep 19331561 = 14498671) B14498671
theorem B12887707 : Blo 2117435 12887707 := bstep (se 1 (by rfl) ⟨9665780, by rfl⟩ : syracuseStep 12887707 = 19331561) B19331561
theorem B17183609 : Blo 2117435 17183609 := bstep (se 2 (by rfl) ⟨6443853, by rfl⟩ : syracuseStep 17183609 = 12887707) B12887707
theorem B11455739 : Blo 2117435 11455739 := bstep (se 1 (by rfl) ⟨8591804, by rfl⟩ : syracuseStep 11455739 = 17183609) B17183609
theorem B7637159 : Blo 2117435 7637159 := bstep (se 1 (by rfl) ⟨5727869, by rfl⟩ : syracuseStep 7637159 = 11455739) B11455739
theorem B5091439 : Blo 2117435 5091439 := bstep (se 1 (by rfl) ⟨3818579, by rfl⟩ : syracuseStep 5091439 = 7637159) B7637159
theorem B6788585 : Blo 2117435 6788585 := bstep (se 2 (by rfl) ⟨2545719, by rfl⟩ : syracuseStep 6788585 = 5091439) B5091439
theorem B4525723 : Blo 2117435 4525723 := bstep (se 1 (by rfl) ⟨3394292, by rfl⟩ : syracuseStep 4525723 = 6788585) B6788585
theorem B24137189 : Blo 2117435 24137189 := bstep (se 4 (by rfl) ⟨2262861, by rfl⟩ : syracuseStep 24137189 = 4525723) B4525723
theorem B16091459 : Blo 2117435 16091459 := bstep (se 1 (by rfl) ⟨12068594, by rfl⟩ : syracuseStep 16091459 = 24137189) B24137189
theorem B10727639 : Blo 2117435 10727639 := bstep (se 1 (by rfl) ⟨8045729, by rfl⟩ : syracuseStep 10727639 = 16091459) B16091459
theorem B7151759 : Blo 2117435 7151759 := bstep (se 1 (by rfl) ⟨5363819, by rfl⟩ : syracuseStep 7151759 = 10727639) B10727639
theorem B4767839 : Blo 2117435 4767839 := bstep (se 1 (by rfl) ⟨3575879, by rfl⟩ : syracuseStep 4767839 = 7151759) B7151759
theorem B3178559 : Blo 2117435 3178559 := bstep (se 1 (by rfl) ⟨2383919, by rfl⟩ : syracuseStep 3178559 = 4767839) B4767839
theorem B2119039 : Blo 2117435 2119039 := bstep (se 1 (by rfl) ⟨1589279, by rfl⟩ : syracuseStep 2119039 = 3178559) B3178559
theorem B3178565 : Blo 2117435 3178565 := bbase (se 4 (by rfl) ⟨297990, by rfl⟩ : syracuseStep 3178565 = 595981) (by norm_num)
theorem B2119043 : Blo 2117435 2119043 := bstep (se 1 (by rfl) ⟨1589282, by rfl⟩ : syracuseStep 2119043 = 3178565) B3178565
theorem B3575893 : Blo 2117435 3575893 := bbase (se 8 (by rfl) ⟨20952, by rfl⟩ : syracuseStep 3575893 = 41905) (by norm_num)
theorem B4767857 : Blo 2117435 4767857 := bstep (se 2 (by rfl) ⟨1787946, by rfl⟩ : syracuseStep 4767857 = 3575893) B3575893
theorem B3178571 : Blo 2117435 3178571 := bstep (se 1 (by rfl) ⟨2383928, by rfl⟩ : syracuseStep 3178571 = 4767857) B4767857
theorem B2119047 : Blo 2117435 2119047 := bstep (se 1 (by rfl) ⟨1589285, by rfl⟩ : syracuseStep 2119047 = 3178571) B3178571
theorem B2383933 : Blo 2117435 2383933 := bbase (se 3 (by rfl) ⟨446987, by rfl⟩ : syracuseStep 2383933 = 893975) (by norm_num)
theorem B3178577 : Blo 2117435 3178577 := bstep (se 2 (by rfl) ⟨1191966, by rfl⟩ : syracuseStep 3178577 = 2383933) B2383933
theorem B2119051 : Blo 2117435 2119051 := bstep (se 1 (by rfl) ⟨1589288, by rfl⟩ : syracuseStep 2119051 = 3178577) B3178577
theorem B7151813 : Blo 2117435 7151813 := bbase (se 4 (by rfl) ⟨670482, by rfl⟩ : syracuseStep 7151813 = 1340965) (by norm_num)
theorem B4767875 : Blo 2117435 4767875 := bstep (se 1 (by rfl) ⟨3575906, by rfl⟩ : syracuseStep 4767875 = 7151813) B7151813
theorem B3178583 : Blo 2117435 3178583 := bstep (se 1 (by rfl) ⟨2383937, by rfl⟩ : syracuseStep 3178583 = 4767875) B4767875
theorem B2119055 : Blo 2117435 2119055 := bstep (se 1 (by rfl) ⟨1589291, by rfl⟩ : syracuseStep 2119055 = 3178583) B3178583
theorem B3178589 : Blo 2117435 3178589 := bbase (se 3 (by rfl) ⟨595985, by rfl⟩ : syracuseStep 3178589 = 1191971) (by norm_num)
theorem B2119059 : Blo 2117435 2119059 := bstep (se 1 (by rfl) ⟨1589294, by rfl⟩ : syracuseStep 2119059 = 3178589) B3178589
theorem B4767893 : Blo 2117435 4767893 := bbase (se 6 (by rfl) ⟨111747, by rfl⟩ : syracuseStep 4767893 = 223495) (by norm_num)
theorem B3178595 : Blo 2117435 3178595 := bstep (se 1 (by rfl) ⟨2383946, by rfl⟩ : syracuseStep 3178595 = 4767893) B4767893
theorem B2119063 : Blo 2117435 2119063 := bstep (se 1 (by rfl) ⟨1589297, by rfl⟩ : syracuseStep 2119063 = 3178595) B3178595
theorem B3017189 : Blo 2117435 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B8045837 : Blo 2117435 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B5363891 : Blo 2117435 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B3575927 : Blo 2117435 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B2383951 : Blo 2117435 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B3178601 : Blo 2117435 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B2119067 : Blo 2117435 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B36700309 : Blo 2117435 36700309 := bbase (se 6 (by rfl) ⟨860163, by rfl⟩ : syracuseStep 36700309 = 1720327) (by norm_num)
theorem B195734981 : Blo 2117435 195734981 := bstep (se 4 (by rfl) ⟨18350154, by rfl⟩ : syracuseStep 195734981 = 36700309) B36700309
theorem B130489987 : Blo 2117435 130489987 := bstep (se 1 (by rfl) ⟨97867490, by rfl⟩ : syracuseStep 130489987 = 195734981) B195734981
theorem B173986649 : Blo 2117435 173986649 := bstep (se 2 (by rfl) ⟨65244993, by rfl⟩ : syracuseStep 173986649 = 130489987) B130489987
theorem B115991099 : Blo 2117435 115991099 := bstep (se 1 (by rfl) ⟨86993324, by rfl⟩ : syracuseStep 115991099 = 173986649) B173986649
theorem B77327399 : Blo 2117435 77327399 := bstep (se 1 (by rfl) ⟨57995549, by rfl⟩ : syracuseStep 77327399 = 115991099) B115991099
theorem B51551599 : Blo 2117435 51551599 := bstep (se 1 (by rfl) ⟨38663699, by rfl⟩ : syracuseStep 51551599 = 77327399) B77327399
theorem B68735465 : Blo 2117435 68735465 := bstep (se 2 (by rfl) ⟨25775799, by rfl⟩ : syracuseStep 68735465 = 51551599) B51551599
theorem B45823643 : Blo 2117435 45823643 := bstep (se 1 (by rfl) ⟨34367732, by rfl⟩ : syracuseStep 45823643 = 68735465) B68735465
theorem B30549095 : Blo 2117435 30549095 := bstep (se 1 (by rfl) ⟨22911821, by rfl⟩ : syracuseStep 30549095 = 45823643) B45823643
theorem B20366063 : Blo 2117435 20366063 := bstep (se 1 (by rfl) ⟨15274547, by rfl⟩ : syracuseStep 20366063 = 30549095) B30549095
theorem B13577375 : Blo 2117435 13577375 := bstep (se 1 (by rfl) ⟨10183031, by rfl⟩ : syracuseStep 13577375 = 20366063) B20366063
theorem B9051583 : Blo 2117435 9051583 := bstep (se 1 (by rfl) ⟨6788687, by rfl⟩ : syracuseStep 9051583 = 13577375) B13577375
theorem B12068777 : Blo 2117435 12068777 := bstep (se 2 (by rfl) ⟨4525791, by rfl⟩ : syracuseStep 12068777 = 9051583) B9051583
theorem B8045851 : Blo 2117435 8045851 := bstep (se 1 (by rfl) ⟨6034388, by rfl⟩ : syracuseStep 8045851 = 12068777) B12068777
theorem B10727801 : Blo 2117435 10727801 := bstep (se 2 (by rfl) ⟨4022925, by rfl⟩ : syracuseStep 10727801 = 8045851) B8045851
theorem B7151867 : Blo 2117435 7151867 := bstep (se 1 (by rfl) ⟨5363900, by rfl⟩ : syracuseStep 7151867 = 10727801) B10727801
theorem B4767911 : Blo 2117435 4767911 := bstep (se 1 (by rfl) ⟨3575933, by rfl⟩ : syracuseStep 4767911 = 7151867) B7151867
theorem B3178607 : Blo 2117435 3178607 := bstep (se 1 (by rfl) ⟨2383955, by rfl⟩ : syracuseStep 3178607 = 4767911) B4767911
theorem B2119071 : Blo 2117435 2119071 := bstep (se 1 (by rfl) ⟨1589303, by rfl⟩ : syracuseStep 2119071 = 3178607) B3178607
theorem B3178613 : Blo 2117435 3178613 := bbase (se 5 (by rfl) ⟨148997, by rfl⟩ : syracuseStep 3178613 = 297995) (by norm_num)
theorem B2119075 : Blo 2117435 2119075 := bstep (se 1 (by rfl) ⟨1589306, by rfl⟩ : syracuseStep 2119075 = 3178613) B3178613
theorem B4022941 : Blo 2117435 4022941 := bbase (se 3 (by rfl) ⟨754301, by rfl⟩ : syracuseStep 4022941 = 1508603) (by norm_num)
theorem B5363921 : Blo 2117435 5363921 := bstep (se 2 (by rfl) ⟨2011470, by rfl⟩ : syracuseStep 5363921 = 4022941) B4022941
theorem B3575947 : Blo 2117435 3575947 := bstep (se 1 (by rfl) ⟨2681960, by rfl⟩ : syracuseStep 3575947 = 5363921) B5363921
theorem B4767929 : Blo 2117435 4767929 := bstep (se 2 (by rfl) ⟨1787973, by rfl⟩ : syracuseStep 4767929 = 3575947) B3575947
theorem B3178619 : Blo 2117435 3178619 := bstep (se 1 (by rfl) ⟨2383964, by rfl⟩ : syracuseStep 3178619 = 4767929) B4767929
theorem B2119079 : Blo 2117435 2119079 := bstep (se 1 (by rfl) ⟨1589309, by rfl⟩ : syracuseStep 2119079 = 3178619) B3178619
theorem B2383969 : Blo 2117435 2383969 := bbase (se 2 (by rfl) ⟨893988, by rfl⟩ : syracuseStep 2383969 = 1787977) (by norm_num)
theorem B3178625 : Blo 2117435 3178625 := bstep (se 2 (by rfl) ⟨1191984, by rfl⟩ : syracuseStep 3178625 = 2383969) B2383969
theorem B2119083 : Blo 2117435 2119083 := bstep (se 1 (by rfl) ⟨1589312, by rfl⟩ : syracuseStep 2119083 = 3178625) B3178625
theorem B5363941 : Blo 2117435 5363941 := bbase (se 4 (by rfl) ⟨502869, by rfl⟩ : syracuseStep 5363941 = 1005739) (by norm_num)
theorem B7151921 : Blo 2117435 7151921 := bstep (se 2 (by rfl) ⟨2681970, by rfl⟩ : syracuseStep 7151921 = 5363941) B5363941
theorem B4767947 : Blo 2117435 4767947 := bstep (se 1 (by rfl) ⟨3575960, by rfl⟩ : syracuseStep 4767947 = 7151921) B7151921
theorem B3178631 : Blo 2117435 3178631 := bstep (se 1 (by rfl) ⟨2383973, by rfl⟩ : syracuseStep 3178631 = 4767947) B4767947
theorem B2119087 : Blo 2117435 2119087 := bstep (se 1 (by rfl) ⟨1589315, by rfl⟩ : syracuseStep 2119087 = 3178631) B3178631
theorem B3178637 : Blo 2117435 3178637 := bbase (se 3 (by rfl) ⟨595994, by rfl⟩ : syracuseStep 3178637 = 1191989) (by norm_num)
theorem B2119091 : Blo 2117435 2119091 := bstep (se 1 (by rfl) ⟨1589318, by rfl⟩ : syracuseStep 2119091 = 3178637) B3178637
theorem B4767965 : Blo 2117435 4767965 := bbase (se 3 (by rfl) ⟨893993, by rfl⟩ : syracuseStep 4767965 = 1787987) (by norm_num)
theorem B3178643 : Blo 2117435 3178643 := bstep (se 1 (by rfl) ⟨2383982, by rfl⟩ : syracuseStep 3178643 = 4767965) B4767965
theorem B2119095 : Blo 2117435 2119095 := bstep (se 1 (by rfl) ⟨1589321, by rfl⟩ : syracuseStep 2119095 = 3178643) B3178643
theorem B3575981 : Blo 2117435 3575981 := bbase (se 3 (by rfl) ⟨670496, by rfl⟩ : syracuseStep 3575981 = 1340993) (by norm_num)
theorem B2383987 : Blo 2117435 2383987 := bstep (se 1 (by rfl) ⟨1787990, by rfl⟩ : syracuseStep 2383987 = 3575981) B3575981
theorem B3178649 : Blo 2117435 3178649 := bstep (se 2 (by rfl) ⟨1191993, by rfl⟩ : syracuseStep 3178649 = 2383987) B2383987
theorem B2119099 : Blo 2117435 2119099 := bstep (se 1 (by rfl) ⟨1589324, by rfl⟩ : syracuseStep 2119099 = 3178649) B3178649
theorem B21748661 : Blo 2117435 21748661 := bbase (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) (by norm_num)
theorem B14499107 : Blo 2117435 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B9666071 : Blo 2117435 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B6444047 : Blo 2117435 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B17184125 : Blo 2117435 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B11456083 : Blo 2117435 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B61099109 : Blo 2117435 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B40732739 : Blo 2117435 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B27155159 : Blo 2117435 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B18103439 : Blo 2117435 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B12068959 : Blo 2117435 12068959 := bstep (se 1 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 12068959 = 18103439) B18103439
theorem B16091945 : Blo 2117435 16091945 := bstep (se 2 (by rfl) ⟨6034479, by rfl⟩ : syracuseStep 16091945 = 12068959) B12068959
theorem B10727963 : Blo 2117435 10727963 := bstep (se 1 (by rfl) ⟨8045972, by rfl⟩ : syracuseStep 10727963 = 16091945) B16091945
theorem B7151975 : Blo 2117435 7151975 := bstep (se 1 (by rfl) ⟨5363981, by rfl⟩ : syracuseStep 7151975 = 10727963) B10727963
theorem B4767983 : Blo 2117435 4767983 := bstep (se 1 (by rfl) ⟨3575987, by rfl⟩ : syracuseStep 4767983 = 7151975) B7151975
theorem B3178655 : Blo 2117435 3178655 := bstep (se 1 (by rfl) ⟨2383991, by rfl⟩ : syracuseStep 3178655 = 4767983) B4767983
theorem B2119103 : Blo 2117435 2119103 := bstep (se 1 (by rfl) ⟨1589327, by rfl⟩ : syracuseStep 2119103 = 3178655) B3178655
theorem B3178661 : Blo 2117435 3178661 := bbase (se 4 (by rfl) ⟨297999, by rfl⟩ : syracuseStep 3178661 = 595999) (by norm_num)
theorem B2119107 : Blo 2117435 2119107 := bstep (se 1 (by rfl) ⟨1589330, by rfl⟩ : syracuseStep 2119107 = 3178661) B3178661
theorem B2682001 : Blo 2117435 2682001 := bbase (se 2 (by rfl) ⟨1005750, by rfl⟩ : syracuseStep 2682001 = 2011501) (by norm_num)
theorem B3576001 : Blo 2117435 3576001 := bstep (se 2 (by rfl) ⟨1341000, by rfl⟩ : syracuseStep 3576001 = 2682001) B2682001
theorem B4768001 : Blo 2117435 4768001 := bstep (se 2 (by rfl) ⟨1788000, by rfl⟩ : syracuseStep 4768001 = 3576001) B3576001
theorem B3178667 : Blo 2117435 3178667 := bstep (se 1 (by rfl) ⟨2384000, by rfl⟩ : syracuseStep 3178667 = 4768001) B4768001
theorem B2119111 : Blo 2117435 2119111 := bstep (se 1 (by rfl) ⟨1589333, by rfl⟩ : syracuseStep 2119111 = 3178667) B3178667
theorem B2384005 : Blo 2117435 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B3178673 : Blo 2117435 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B2119115 : Blo 2117435 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B2416537 : Blo 2117435 2416537 := bbase (se 2 (by rfl) ⟨906201, by rfl⟩ : syracuseStep 2416537 = 1812403) (by norm_num)
theorem B12888197 : Blo 2117435 12888197 := bstep (se 4 (by rfl) ⟨1208268, by rfl⟩ : syracuseStep 12888197 = 2416537) B2416537
theorem B8592131 : Blo 2117435 8592131 := bstep (se 1 (by rfl) ⟨6444098, by rfl⟩ : syracuseStep 8592131 = 12888197) B12888197
theorem B5728087 : Blo 2117435 5728087 := bstep (se 1 (by rfl) ⟨4296065, by rfl⟩ : syracuseStep 5728087 = 8592131) B8592131
theorem B7637449 : Blo 2117435 7637449 := bstep (se 2 (by rfl) ⟨2864043, by rfl⟩ : syracuseStep 7637449 = 5728087) B5728087
theorem B10183265 : Blo 2117435 10183265 := bstep (se 2 (by rfl) ⟨3818724, by rfl⟩ : syracuseStep 10183265 = 7637449) B7637449
theorem B6788843 : Blo 2117435 6788843 := bstep (se 1 (by rfl) ⟨5091632, by rfl⟩ : syracuseStep 6788843 = 10183265) B10183265
theorem B4525895 : Blo 2117435 4525895 := bstep (se 1 (by rfl) ⟨3394421, by rfl⟩ : syracuseStep 4525895 = 6788843) B6788843
theorem B3017263 : Blo 2117435 3017263 := bstep (se 1 (by rfl) ⟨2262947, by rfl⟩ : syracuseStep 3017263 = 4525895) B4525895
theorem B4023017 : Blo 2117435 4023017 := bstep (se 2 (by rfl) ⟨1508631, by rfl⟩ : syracuseStep 4023017 = 3017263) B3017263
theorem B2682011 : Blo 2117435 2682011 := bstep (se 1 (by rfl) ⟨2011508, by rfl⟩ : syracuseStep 2682011 = 4023017) B4023017
theorem B7152029 : Blo 2117435 7152029 := bstep (se 3 (by rfl) ⟨1341005, by rfl⟩ : syracuseStep 7152029 = 2682011) B2682011
theorem B4768019 : Blo 2117435 4768019 := bstep (se 1 (by rfl) ⟨3576014, by rfl⟩ : syracuseStep 4768019 = 7152029) B7152029
theorem B3178679 : Blo 2117435 3178679 := bstep (se 1 (by rfl) ⟨2384009, by rfl⟩ : syracuseStep 3178679 = 4768019) B4768019
theorem B2119119 : Blo 2117435 2119119 := bstep (se 1 (by rfl) ⟨1589339, by rfl⟩ : syracuseStep 2119119 = 3178679) B3178679
theorem B3178685 : Blo 2117435 3178685 := bbase (se 3 (by rfl) ⟨596003, by rfl⟩ : syracuseStep 3178685 = 1192007) (by norm_num)
theorem B2119123 : Blo 2117435 2119123 := bstep (se 1 (by rfl) ⟨1589342, by rfl⟩ : syracuseStep 2119123 = 3178685) B3178685
theorem B4768037 : Blo 2117435 4768037 := bbase (se 4 (by rfl) ⟨447003, by rfl⟩ : syracuseStep 4768037 = 894007) (by norm_num)
theorem B3178691 : Blo 2117435 3178691 := bstep (se 1 (by rfl) ⟨2384018, by rfl⟩ : syracuseStep 3178691 = 4768037) B4768037
theorem B2119127 : Blo 2117435 2119127 := bstep (se 1 (by rfl) ⟨1589345, by rfl⟩ : syracuseStep 2119127 = 3178691) B3178691
theorem B5364053 : Blo 2117435 5364053 := bbase (se 10 (by rfl) ⟨7857, by rfl⟩ : syracuseStep 5364053 = 15715) (by norm_num)
theorem B3576035 : Blo 2117435 3576035 := bstep (se 1 (by rfl) ⟨2682026, by rfl⟩ : syracuseStep 3576035 = 5364053) B5364053
theorem B2384023 : Blo 2117435 2384023 := bstep (se 1 (by rfl) ⟨1788017, by rfl⟩ : syracuseStep 2384023 = 3576035) B3576035
theorem B3178697 : Blo 2117435 3178697 := bstep (se 2 (by rfl) ⟨1192011, by rfl⟩ : syracuseStep 3178697 = 2384023) B2384023
theorem B2119131 : Blo 2117435 2119131 := bstep (se 1 (by rfl) ⟨1589348, by rfl⟩ : syracuseStep 2119131 = 3178697) B3178697
theorem B2148049 : Blo 2117435 2148049 := bbase (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) (by norm_num)
theorem B2864065 : Blo 2117435 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B3818753 : Blo 2117435 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B2545835 : Blo 2117435 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B6788893 : Blo 2117435 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B9051857 : Blo 2117435 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B6034571 : Blo 2117435 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B4023047 : Blo 2117435 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B10728125 : Blo 2117435 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B7152083 : Blo 2117435 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B4768055 : Blo 2117435 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B3178703 : Blo 2117435 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B2119135 : Blo 2117435 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B3178709 : Blo 2117435 3178709 := bbase (se 7 (by rfl) ⟨37250, by rfl⟩ : syracuseStep 3178709 = 74501) (by norm_num)
theorem B2119139 : Blo 2117435 2119139 := bstep (se 1 (by rfl) ⟨1589354, by rfl⟩ : syracuseStep 2119139 = 3178709) B3178709
theorem B2262973 : Blo 2117435 2262973 := bbase (se 3 (by rfl) ⟨424307, by rfl⟩ : syracuseStep 2262973 = 848615) (by norm_num)
theorem B3017297 : Blo 2117435 3017297 := bstep (se 2 (by rfl) ⟨1131486, by rfl⟩ : syracuseStep 3017297 = 2262973) B2262973
theorem B8046125 : Blo 2117435 8046125 := bstep (se 3 (by rfl) ⟨1508648, by rfl⟩ : syracuseStep 8046125 = 3017297) B3017297
theorem B5364083 : Blo 2117435 5364083 := bstep (se 1 (by rfl) ⟨4023062, by rfl⟩ : syracuseStep 5364083 = 8046125) B8046125
theorem B3576055 : Blo 2117435 3576055 := bstep (se 1 (by rfl) ⟨2682041, by rfl⟩ : syracuseStep 3576055 = 5364083) B5364083
theorem B4768073 : Blo 2117435 4768073 := bstep (se 2 (by rfl) ⟨1788027, by rfl⟩ : syracuseStep 4768073 = 3576055) B3576055
theorem B3178715 : Blo 2117435 3178715 := bstep (se 1 (by rfl) ⟨2384036, by rfl⟩ : syracuseStep 3178715 = 4768073) B4768073
theorem B2119143 : Blo 2117435 2119143 := bstep (se 1 (by rfl) ⟨1589357, by rfl⟩ : syracuseStep 2119143 = 3178715) B3178715
theorem B2384041 : Blo 2117435 2384041 := bbase (se 2 (by rfl) ⟨894015, by rfl⟩ : syracuseStep 2384041 = 1788031) (by norm_num)
theorem B3178721 : Blo 2117435 3178721 := bstep (se 2 (by rfl) ⟨1192020, by rfl⟩ : syracuseStep 3178721 = 2384041) B2384041
theorem B2119147 : Blo 2117435 2119147 := bstep (se 1 (by rfl) ⟨1589360, by rfl⟩ : syracuseStep 2119147 = 3178721) B3178721
theorem B9051925 : Blo 2117435 9051925 := bbase (se 6 (by rfl) ⟨212154, by rfl⟩ : syracuseStep 9051925 = 424309) (by norm_num)
theorem B12069233 : Blo 2117435 12069233 := bstep (se 2 (by rfl) ⟨4525962, by rfl⟩ : syracuseStep 12069233 = 9051925) B9051925
theorem B8046155 : Blo 2117435 8046155 := bstep (se 1 (by rfl) ⟨6034616, by rfl⟩ : syracuseStep 8046155 = 12069233) B12069233
theorem B5364103 : Blo 2117435 5364103 := bstep (se 1 (by rfl) ⟨4023077, by rfl⟩ : syracuseStep 5364103 = 8046155) B8046155
theorem B7152137 : Blo 2117435 7152137 := bstep (se 2 (by rfl) ⟨2682051, by rfl⟩ : syracuseStep 7152137 = 5364103) B5364103
theorem B4768091 : Blo 2117435 4768091 := bstep (se 1 (by rfl) ⟨3576068, by rfl⟩ : syracuseStep 4768091 = 7152137) B7152137
theorem B3178727 : Blo 2117435 3178727 := bstep (se 1 (by rfl) ⟨2384045, by rfl⟩ : syracuseStep 3178727 = 4768091) B4768091
theorem B2119151 : Blo 2117435 2119151 := bstep (se 1 (by rfl) ⟨1589363, by rfl⟩ : syracuseStep 2119151 = 3178727) B3178727
theorem B3178733 : Blo 2117435 3178733 := bbase (se 3 (by rfl) ⟨596012, by rfl⟩ : syracuseStep 3178733 = 1192025) (by norm_num)
theorem B2119155 : Blo 2117435 2119155 := bstep (se 1 (by rfl) ⟨1589366, by rfl⟩ : syracuseStep 2119155 = 3178733) B3178733
theorem B4768109 : Blo 2117435 4768109 := bbase (se 3 (by rfl) ⟨894020, by rfl⟩ : syracuseStep 4768109 = 1788041) (by norm_num)
theorem B3178739 : Blo 2117435 3178739 := bstep (se 1 (by rfl) ⟨2384054, by rfl⟩ : syracuseStep 3178739 = 4768109) B4768109
theorem B2119159 : Blo 2117435 2119159 := bstep (se 1 (by rfl) ⟨1589369, by rfl⟩ : syracuseStep 2119159 = 3178739) B3178739
theorem B4023101 : Blo 2117435 4023101 := bbase (se 3 (by rfl) ⟨754331, by rfl⟩ : syracuseStep 4023101 = 1508663) (by norm_num)
theorem B2682067 : Blo 2117435 2682067 := bstep (se 1 (by rfl) ⟨2011550, by rfl⟩ : syracuseStep 2682067 = 4023101) B4023101
theorem B3576089 : Blo 2117435 3576089 := bstep (se 2 (by rfl) ⟨1341033, by rfl⟩ : syracuseStep 3576089 = 2682067) B2682067
theorem B2384059 : Blo 2117435 2384059 := bstep (se 1 (by rfl) ⟨1788044, by rfl⟩ : syracuseStep 2384059 = 3576089) B3576089
theorem B3178745 : Blo 2117435 3178745 := bstep (se 2 (by rfl) ⟨1192029, by rfl⟩ : syracuseStep 3178745 = 2384059) B2384059
theorem B2119163 : Blo 2117435 2119163 := bstep (se 1 (by rfl) ⟨1589372, by rfl⟩ : syracuseStep 2119163 = 3178745) B3178745
theorem B2545873 : Blo 2117435 2545873 := bbase (se 2 (by rfl) ⟨954702, by rfl⟩ : syracuseStep 2545873 = 1909405) (by norm_num)
theorem B54311957 : Blo 2117435 54311957 := bstep (se 6 (by rfl) ⟨1272936, by rfl⟩ : syracuseStep 54311957 = 2545873) B2545873
theorem B36207971 : Blo 2117435 36207971 := bstep (se 1 (by rfl) ⟨27155978, by rfl⟩ : syracuseStep 36207971 = 54311957) B54311957
theorem B24138647 : Blo 2117435 24138647 := bstep (se 1 (by rfl) ⟨18103985, by rfl⟩ : syracuseStep 24138647 = 36207971) B36207971
theorem B16092431 : Blo 2117435 16092431 := bstep (se 1 (by rfl) ⟨12069323, by rfl⟩ : syracuseStep 16092431 = 24138647) B24138647
theorem B10728287 : Blo 2117435 10728287 := bstep (se 1 (by rfl) ⟨8046215, by rfl⟩ : syracuseStep 10728287 = 16092431) B16092431
theorem B7152191 : Blo 2117435 7152191 := bstep (se 1 (by rfl) ⟨5364143, by rfl⟩ : syracuseStep 7152191 = 10728287) B10728287
theorem B4768127 : Blo 2117435 4768127 := bstep (se 1 (by rfl) ⟨3576095, by rfl⟩ : syracuseStep 4768127 = 7152191) B7152191
theorem B3178751 : Blo 2117435 3178751 := bstep (se 1 (by rfl) ⟨2384063, by rfl⟩ : syracuseStep 3178751 = 4768127) B4768127
theorem B2119167 : Blo 2117435 2119167 := bstep (se 1 (by rfl) ⟨1589375, by rfl⟩ : syracuseStep 2119167 = 3178751) B3178751
theorem B3178757 : Blo 2117435 3178757 := bbase (se 4 (by rfl) ⟨298008, by rfl⟩ : syracuseStep 3178757 = 596017) (by norm_num)
theorem B2119171 : Blo 2117435 2119171 := bstep (se 1 (by rfl) ⟨1589378, by rfl⟩ : syracuseStep 2119171 = 3178757) B3178757
theorem B3576109 : Blo 2117435 3576109 := bbase (se 3 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 3576109 = 1341041) (by norm_num)
theorem B4768145 : Blo 2117435 4768145 := bstep (se 2 (by rfl) ⟨1788054, by rfl⟩ : syracuseStep 4768145 = 3576109) B3576109
theorem B3178763 : Blo 2117435 3178763 := bstep (se 1 (by rfl) ⟨2384072, by rfl⟩ : syracuseStep 3178763 = 4768145) B4768145
theorem B2119175 : Blo 2117435 2119175 := bstep (se 1 (by rfl) ⟨1589381, by rfl⟩ : syracuseStep 2119175 = 3178763) B3178763
theorem B2384077 : Blo 2117435 2384077 := bbase (se 3 (by rfl) ⟨447014, by rfl⟩ : syracuseStep 2384077 = 894029) (by norm_num)
theorem B3178769 : Blo 2117435 3178769 := bstep (se 2 (by rfl) ⟨1192038, by rfl⟩ : syracuseStep 3178769 = 2384077) B2384077
theorem B2119179 : Blo 2117435 2119179 := bstep (se 1 (by rfl) ⟨1589384, by rfl⟩ : syracuseStep 2119179 = 3178769) B3178769
theorem B7152245 : Blo 2117435 7152245 := bbase (se 5 (by rfl) ⟨335261, by rfl⟩ : syracuseStep 7152245 = 670523) (by norm_num)
theorem B4768163 : Blo 2117435 4768163 := bstep (se 1 (by rfl) ⟨3576122, by rfl⟩ : syracuseStep 4768163 = 7152245) B7152245
theorem B3178775 : Blo 2117435 3178775 := bstep (se 1 (by rfl) ⟨2384081, by rfl⟩ : syracuseStep 3178775 = 4768163) B4768163
theorem B2119183 : Blo 2117435 2119183 := bstep (se 1 (by rfl) ⟨1589387, by rfl⟩ : syracuseStep 2119183 = 3178775) B3178775
theorem B3178781 : Blo 2117435 3178781 := bbase (se 3 (by rfl) ⟨596021, by rfl⟩ : syracuseStep 3178781 = 1192043) (by norm_num)
theorem B2119187 : Blo 2117435 2119187 := bstep (se 1 (by rfl) ⟨1589390, by rfl⟩ : syracuseStep 2119187 = 3178781) B3178781
theorem B4768181 : Blo 2117435 4768181 := bbase (se 5 (by rfl) ⟨223508, by rfl⟩ : syracuseStep 4768181 = 447017) (by norm_num)
theorem B3178787 : Blo 2117435 3178787 := bstep (se 1 (by rfl) ⟨2384090, by rfl⟩ : syracuseStep 3178787 = 4768181) B4768181
theorem B2119191 : Blo 2117435 2119191 := bstep (se 1 (by rfl) ⟨1589393, by rfl⟩ : syracuseStep 2119191 = 3178787) B3178787
theorem B3870965 : Blo 2117435 3870965 := bbase (se 5 (by rfl) ⟨181451, by rfl⟩ : syracuseStep 3870965 = 362903) (by norm_num)
theorem B2580643 : Blo 2117435 2580643 := bstep (se 1 (by rfl) ⟨1935482, by rfl⟩ : syracuseStep 2580643 = 3870965) B3870965
theorem B13763429 : Blo 2117435 13763429 := bstep (se 4 (by rfl) ⟨1290321, by rfl⟩ : syracuseStep 13763429 = 2580643) B2580643
theorem B9175619 : Blo 2117435 9175619 := bstep (se 1 (by rfl) ⟨6881714, by rfl⟩ : syracuseStep 9175619 = 13763429) B13763429
theorem B24468317 : Blo 2117435 24468317 := bstep (se 3 (by rfl) ⟨4587809, by rfl⟩ : syracuseStep 24468317 = 9175619) B9175619
theorem B16312211 : Blo 2117435 16312211 := bstep (se 1 (by rfl) ⟨12234158, by rfl⟩ : syracuseStep 16312211 = 24468317) B24468317
theorem B10874807 : Blo 2117435 10874807 := bstep (se 1 (by rfl) ⟨8156105, by rfl⟩ : syracuseStep 10874807 = 16312211) B16312211
theorem B7249871 : Blo 2117435 7249871 := bstep (se 1 (by rfl) ⟨5437403, by rfl⟩ : syracuseStep 7249871 = 10874807) B10874807
theorem B19332989 : Blo 2117435 19332989 := bstep (se 3 (by rfl) ⟨3624935, by rfl⟩ : syracuseStep 19332989 = 7249871) B7249871
theorem B12888659 : Blo 2117435 12888659 := bstep (se 1 (by rfl) ⟨9666494, by rfl⟩ : syracuseStep 12888659 = 19332989) B19332989
theorem B8592439 : Blo 2117435 8592439 := bstep (se 1 (by rfl) ⟨6444329, by rfl⟩ : syracuseStep 8592439 = 12888659) B12888659
theorem B11456585 : Blo 2117435 11456585 := bstep (se 2 (by rfl) ⟨4296219, by rfl⟩ : syracuseStep 11456585 = 8592439) B8592439
theorem B7637723 : Blo 2117435 7637723 := bstep (se 1 (by rfl) ⟨5728292, by rfl⟩ : syracuseStep 7637723 = 11456585) B11456585
theorem B5091815 : Blo 2117435 5091815 := bstep (se 1 (by rfl) ⟨3818861, by rfl⟩ : syracuseStep 5091815 = 7637723) B7637723
theorem B3394543 : Blo 2117435 3394543 := bstep (se 1 (by rfl) ⟨2545907, by rfl⟩ : syracuseStep 3394543 = 5091815) B5091815
theorem B4526057 : Blo 2117435 4526057 := bstep (se 2 (by rfl) ⟨1697271, by rfl⟩ : syracuseStep 4526057 = 3394543) B3394543
theorem B12069485 : Blo 2117435 12069485 := bstep (se 3 (by rfl) ⟨2263028, by rfl⟩ : syracuseStep 12069485 = 4526057) B4526057
theorem B8046323 : Blo 2117435 8046323 := bstep (se 1 (by rfl) ⟨6034742, by rfl⟩ : syracuseStep 8046323 = 12069485) B12069485
theorem B5364215 : Blo 2117435 5364215 := bstep (se 1 (by rfl) ⟨4023161, by rfl⟩ : syracuseStep 5364215 = 8046323) B8046323
theorem B3576143 : Blo 2117435 3576143 := bstep (se 1 (by rfl) ⟨2682107, by rfl⟩ : syracuseStep 3576143 = 5364215) B5364215
theorem B2384095 : Blo 2117435 2384095 := bstep (se 1 (by rfl) ⟨1788071, by rfl⟩ : syracuseStep 2384095 = 3576143) B3576143
theorem B3178793 : Blo 2117435 3178793 := bstep (se 2 (by rfl) ⟨1192047, by rfl⟩ : syracuseStep 3178793 = 2384095) B2384095
theorem B2119195 : Blo 2117435 2119195 := bstep (se 1 (by rfl) ⟨1589396, by rfl⟩ : syracuseStep 2119195 = 3178793) B3178793
theorem B3394549 : Blo 2117435 3394549 := bbase (se 5 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 3394549 = 318239) (by norm_num)
theorem B4526065 : Blo 2117435 4526065 := bstep (se 2 (by rfl) ⟨1697274, by rfl⟩ : syracuseStep 4526065 = 3394549) B3394549
theorem B6034753 : Blo 2117435 6034753 := bstep (se 2 (by rfl) ⟨2263032, by rfl⟩ : syracuseStep 6034753 = 4526065) B4526065
theorem B8046337 : Blo 2117435 8046337 := bstep (se 2 (by rfl) ⟨3017376, by rfl⟩ : syracuseStep 8046337 = 6034753) B6034753
theorem B10728449 : Blo 2117435 10728449 := bstep (se 2 (by rfl) ⟨4023168, by rfl⟩ : syracuseStep 10728449 = 8046337) B8046337
theorem B7152299 : Blo 2117435 7152299 := bstep (se 1 (by rfl) ⟨5364224, by rfl⟩ : syracuseStep 7152299 = 10728449) B10728449
theorem B4768199 : Blo 2117435 4768199 := bstep (se 1 (by rfl) ⟨3576149, by rfl⟩ : syracuseStep 4768199 = 7152299) B7152299
theorem B3178799 : Blo 2117435 3178799 := bstep (se 1 (by rfl) ⟨2384099, by rfl⟩ : syracuseStep 3178799 = 4768199) B4768199
theorem B2119199 : Blo 2117435 2119199 := bstep (se 1 (by rfl) ⟨1589399, by rfl⟩ : syracuseStep 2119199 = 3178799) B3178799
theorem B3178805 : Blo 2117435 3178805 := bbase (se 5 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 3178805 = 298013) (by norm_num)
theorem B2119203 : Blo 2117435 2119203 := bstep (se 1 (by rfl) ⟨1589402, by rfl⟩ : syracuseStep 2119203 = 3178805) B3178805
theorem B5364245 : Blo 2117435 5364245 := bbase (se 6 (by rfl) ⟨125724, by rfl⟩ : syracuseStep 5364245 = 251449) (by norm_num)
theorem B3576163 : Blo 2117435 3576163 := bstep (se 1 (by rfl) ⟨2682122, by rfl⟩ : syracuseStep 3576163 = 5364245) B5364245
theorem B4768217 : Blo 2117435 4768217 := bstep (se 2 (by rfl) ⟨1788081, by rfl⟩ : syracuseStep 4768217 = 3576163) B3576163
theorem B3178811 : Blo 2117435 3178811 := bstep (se 1 (by rfl) ⟨2384108, by rfl⟩ : syracuseStep 3178811 = 4768217) B4768217
theorem B2119207 : Blo 2117435 2119207 := bstep (se 1 (by rfl) ⟨1589405, by rfl⟩ : syracuseStep 2119207 = 3178811) B3178811
theorem B2384113 : Blo 2117435 2384113 := bbase (se 2 (by rfl) ⟨894042, by rfl⟩ : syracuseStep 2384113 = 1788085) (by norm_num)
theorem B3178817 : Blo 2117435 3178817 := bstep (se 2 (by rfl) ⟨1192056, by rfl⟩ : syracuseStep 3178817 = 2384113) B2384113
theorem B2119211 : Blo 2117435 2119211 := bstep (se 1 (by rfl) ⟨1589408, by rfl⟩ : syracuseStep 2119211 = 3178817) B3178817
theorem B6444389 : Blo 2117435 6444389 := bbase (se 4 (by rfl) ⟨604161, by rfl⟩ : syracuseStep 6444389 = 1208323) (by norm_num)
theorem B4296259 : Blo 2117435 4296259 := bstep (se 1 (by rfl) ⟨3222194, by rfl⟩ : syracuseStep 4296259 = 6444389) B6444389
theorem B22913381 : Blo 2117435 22913381 := bstep (se 4 (by rfl) ⟨2148129, by rfl⟩ : syracuseStep 22913381 = 4296259) B4296259
theorem B15275587 : Blo 2117435 15275587 := bstep (se 1 (by rfl) ⟨11456690, by rfl⟩ : syracuseStep 15275587 = 22913381) B22913381
theorem B20367449 : Blo 2117435 20367449 := bstep (se 2 (by rfl) ⟨7637793, by rfl⟩ : syracuseStep 20367449 = 15275587) B15275587
theorem B13578299 : Blo 2117435 13578299 := bstep (se 1 (by rfl) ⟨10183724, by rfl⟩ : syracuseStep 13578299 = 20367449) B20367449
theorem B9052199 : Blo 2117435 9052199 := bstep (se 1 (by rfl) ⟨6789149, by rfl⟩ : syracuseStep 9052199 = 13578299) B13578299
theorem B6034799 : Blo 2117435 6034799 := bstep (se 1 (by rfl) ⟨4526099, by rfl⟩ : syracuseStep 6034799 = 9052199) B9052199
theorem B4023199 : Blo 2117435 4023199 := bstep (se 1 (by rfl) ⟨3017399, by rfl⟩ : syracuseStep 4023199 = 6034799) B6034799
theorem B5364265 : Blo 2117435 5364265 := bstep (se 2 (by rfl) ⟨2011599, by rfl⟩ : syracuseStep 5364265 = 4023199) B4023199
theorem B7152353 : Blo 2117435 7152353 := bstep (se 2 (by rfl) ⟨2682132, by rfl⟩ : syracuseStep 7152353 = 5364265) B5364265
theorem B4768235 : Blo 2117435 4768235 := bstep (se 1 (by rfl) ⟨3576176, by rfl⟩ : syracuseStep 4768235 = 7152353) B7152353
theorem B3178823 : Blo 2117435 3178823 := bstep (se 1 (by rfl) ⟨2384117, by rfl⟩ : syracuseStep 3178823 = 4768235) B4768235
theorem B2119215 : Blo 2117435 2119215 := bstep (se 1 (by rfl) ⟨1589411, by rfl⟩ : syracuseStep 2119215 = 3178823) B3178823
theorem B3178829 : Blo 2117435 3178829 := bbase (se 3 (by rfl) ⟨596030, by rfl⟩ : syracuseStep 3178829 = 1192061) (by norm_num)
theorem B2119219 : Blo 2117435 2119219 := bstep (se 1 (by rfl) ⟨1589414, by rfl⟩ : syracuseStep 2119219 = 3178829) B3178829
theorem B4768253 : Blo 2117435 4768253 := bbase (se 3 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 4768253 = 1788095) (by norm_num)
theorem B3178835 : Blo 2117435 3178835 := bstep (se 1 (by rfl) ⟨2384126, by rfl⟩ : syracuseStep 3178835 = 4768253) B4768253
theorem B2119223 : Blo 2117435 2119223 := bstep (se 1 (by rfl) ⟨1589417, by rfl⟩ : syracuseStep 2119223 = 3178835) B3178835
theorem B3576197 : Blo 2117435 3576197 := bbase (se 4 (by rfl) ⟨335268, by rfl⟩ : syracuseStep 3576197 = 670537) (by norm_num)
theorem B2384131 : Blo 2117435 2384131 := bstep (se 1 (by rfl) ⟨1788098, by rfl⟩ : syracuseStep 2384131 = 3576197) B3576197
theorem B3178841 : Blo 2117435 3178841 := bstep (se 2 (by rfl) ⟨1192065, by rfl⟩ : syracuseStep 3178841 = 2384131) B2384131
theorem B2119227 : Blo 2117435 2119227 := bstep (se 1 (by rfl) ⟨1589420, by rfl⟩ : syracuseStep 2119227 = 3178841) B3178841
theorem B16092917 : Blo 2117435 16092917 := bbase (se 5 (by rfl) ⟨754355, by rfl⟩ : syracuseStep 16092917 = 1508711) (by norm_num)
theorem B10728611 : Blo 2117435 10728611 := bstep (se 1 (by rfl) ⟨8046458, by rfl⟩ : syracuseStep 10728611 = 16092917) B16092917
theorem B7152407 : Blo 2117435 7152407 := bstep (se 1 (by rfl) ⟨5364305, by rfl⟩ : syracuseStep 7152407 = 10728611) B10728611
theorem B4768271 : Blo 2117435 4768271 := bstep (se 1 (by rfl) ⟨3576203, by rfl⟩ : syracuseStep 4768271 = 7152407) B7152407
theorem B3178847 : Blo 2117435 3178847 := bstep (se 1 (by rfl) ⟨2384135, by rfl⟩ : syracuseStep 3178847 = 4768271) B4768271
theorem B2119231 : Blo 2117435 2119231 := bstep (se 1 (by rfl) ⟨1589423, by rfl⟩ : syracuseStep 2119231 = 3178847) B3178847
theorem B3178853 : Blo 2117435 3178853 := bbase (se 4 (by rfl) ⟨298017, by rfl⟩ : syracuseStep 3178853 = 596035) (by norm_num)
theorem B2119235 : Blo 2117435 2119235 := bstep (se 1 (by rfl) ⟨1589426, by rfl⟩ : syracuseStep 2119235 = 3178853) B3178853
theorem B4023245 : Blo 2117435 4023245 := bbase (se 3 (by rfl) ⟨754358, by rfl⟩ : syracuseStep 4023245 = 1508717) (by norm_num)
theorem B2682163 : Blo 2117435 2682163 := bstep (se 1 (by rfl) ⟨2011622, by rfl⟩ : syracuseStep 2682163 = 4023245) B4023245
theorem B3576217 : Blo 2117435 3576217 := bstep (se 2 (by rfl) ⟨1341081, by rfl⟩ : syracuseStep 3576217 = 2682163) B2682163
theorem B4768289 : Blo 2117435 4768289 := bstep (se 2 (by rfl) ⟨1788108, by rfl⟩ : syracuseStep 4768289 = 3576217) B3576217
theorem B3178859 : Blo 2117435 3178859 := bstep (se 1 (by rfl) ⟨2384144, by rfl⟩ : syracuseStep 3178859 = 4768289) B4768289
theorem B2119239 : Blo 2117435 2119239 := bstep (se 1 (by rfl) ⟨1589429, by rfl⟩ : syracuseStep 2119239 = 3178859) B3178859
theorem B2384149 : Blo 2117435 2384149 := bbase (se 6 (by rfl) ⟨55878, by rfl⟩ : syracuseStep 2384149 = 111757) (by norm_num)
theorem B3178865 : Blo 2117435 3178865 := bstep (se 2 (by rfl) ⟨1192074, by rfl⟩ : syracuseStep 3178865 = 2384149) B2384149
theorem B2119243 : Blo 2117435 2119243 := bstep (se 1 (by rfl) ⟨1589432, by rfl⟩ : syracuseStep 2119243 = 3178865) B3178865
theorem B2682173 : Blo 2117435 2682173 := bbase (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) (by norm_num)
theorem B7152461 : Blo 2117435 7152461 := bstep (se 3 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 7152461 = 2682173) B2682173
theorem B4768307 : Blo 2117435 4768307 := bstep (se 1 (by rfl) ⟨3576230, by rfl⟩ : syracuseStep 4768307 = 7152461) B7152461
theorem B3178871 : Blo 2117435 3178871 := bstep (se 1 (by rfl) ⟨2384153, by rfl⟩ : syracuseStep 3178871 = 4768307) B4768307
theorem B2119247 : Blo 2117435 2119247 := bstep (se 1 (by rfl) ⟨1589435, by rfl⟩ : syracuseStep 2119247 = 3178871) B3178871
theorem B3178877 : Blo 2117435 3178877 := bbase (se 3 (by rfl) ⟨596039, by rfl⟩ : syracuseStep 3178877 = 1192079) (by norm_num)
theorem B2119251 : Blo 2117435 2119251 := bstep (se 1 (by rfl) ⟨1589438, by rfl⟩ : syracuseStep 2119251 = 3178877) B3178877
theorem B4768325 : Blo 2117435 4768325 := bbase (se 4 (by rfl) ⟨447030, by rfl⟩ : syracuseStep 4768325 = 894061) (by norm_num)
theorem B3178883 : Blo 2117435 3178883 := bstep (se 1 (by rfl) ⟨2384162, by rfl⟩ : syracuseStep 3178883 = 4768325) B4768325
theorem B2119255 : Blo 2117435 2119255 := bstep (se 1 (by rfl) ⟨1589441, by rfl⟩ : syracuseStep 2119255 = 3178883) B3178883
theorem B2263097 : Blo 2117435 2263097 := bbase (se 2 (by rfl) ⟨848661, by rfl⟩ : syracuseStep 2263097 = 1697323) (by norm_num)
theorem B6034925 : Blo 2117435 6034925 := bstep (se 3 (by rfl) ⟨1131548, by rfl⟩ : syracuseStep 6034925 = 2263097) B2263097
theorem B4023283 : Blo 2117435 4023283 := bstep (se 1 (by rfl) ⟨3017462, by rfl⟩ : syracuseStep 4023283 = 6034925) B6034925
theorem B5364377 : Blo 2117435 5364377 := bstep (se 2 (by rfl) ⟨2011641, by rfl⟩ : syracuseStep 5364377 = 4023283) B4023283
theorem B3576251 : Blo 2117435 3576251 := bstep (se 1 (by rfl) ⟨2682188, by rfl⟩ : syracuseStep 3576251 = 5364377) B5364377
theorem B2384167 : Blo 2117435 2384167 := bstep (se 1 (by rfl) ⟨1788125, by rfl⟩ : syracuseStep 2384167 = 3576251) B3576251
theorem B3178889 : Blo 2117435 3178889 := bstep (se 2 (by rfl) ⟨1192083, by rfl⟩ : syracuseStep 3178889 = 2384167) B2384167
theorem B2119259 : Blo 2117435 2119259 := bstep (se 1 (by rfl) ⟨1589444, by rfl⟩ : syracuseStep 2119259 = 3178889) B3178889
theorem B10728773 : Blo 2117435 10728773 := bbase (se 4 (by rfl) ⟨1005822, by rfl⟩ : syracuseStep 10728773 = 2011645) (by norm_num)
theorem B7152515 : Blo 2117435 7152515 := bstep (se 1 (by rfl) ⟨5364386, by rfl⟩ : syracuseStep 7152515 = 10728773) B10728773
theorem B4768343 : Blo 2117435 4768343 := bstep (se 1 (by rfl) ⟨3576257, by rfl⟩ : syracuseStep 4768343 = 7152515) B7152515
theorem B3178895 : Blo 2117435 3178895 := bstep (se 1 (by rfl) ⟨2384171, by rfl⟩ : syracuseStep 3178895 = 4768343) B4768343
theorem B2119263 : Blo 2117435 2119263 := bstep (se 1 (by rfl) ⟨1589447, by rfl⟩ : syracuseStep 2119263 = 3178895) B3178895
theorem B3178901 : Blo 2117435 3178901 := bbase (se 6 (by rfl) ⟨74505, by rfl⟩ : syracuseStep 3178901 = 149011) (by norm_num)
theorem B2119267 : Blo 2117435 2119267 := bstep (se 1 (by rfl) ⟨1589450, by rfl⟩ : syracuseStep 2119267 = 3178901) B3178901
theorem B5091997 : Blo 2117435 5091997 := bbase (se 3 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 5091997 = 1909499) (by norm_num)
theorem B6789329 : Blo 2117435 6789329 := bstep (se 2 (by rfl) ⟨2545998, by rfl⟩ : syracuseStep 6789329 = 5091997) B5091997
theorem B4526219 : Blo 2117435 4526219 := bstep (se 1 (by rfl) ⟨3394664, by rfl⟩ : syracuseStep 4526219 = 6789329) B6789329
theorem B12069917 : Blo 2117435 12069917 := bstep (se 3 (by rfl) ⟨2263109, by rfl⟩ : syracuseStep 12069917 = 4526219) B4526219
theorem B8046611 : Blo 2117435 8046611 := bstep (se 1 (by rfl) ⟨6034958, by rfl⟩ : syracuseStep 8046611 = 12069917) B12069917
theorem B5364407 : Blo 2117435 5364407 := bstep (se 1 (by rfl) ⟨4023305, by rfl⟩ : syracuseStep 5364407 = 8046611) B8046611
theorem B3576271 : Blo 2117435 3576271 := bstep (se 1 (by rfl) ⟨2682203, by rfl⟩ : syracuseStep 3576271 = 5364407) B5364407
theorem B4768361 : Blo 2117435 4768361 := bstep (se 2 (by rfl) ⟨1788135, by rfl⟩ : syracuseStep 4768361 = 3576271) B3576271
theorem B3178907 : Blo 2117435 3178907 := bstep (se 1 (by rfl) ⟨2384180, by rfl⟩ : syracuseStep 3178907 = 4768361) B4768361
theorem B2119271 : Blo 2117435 2119271 := bstep (se 1 (by rfl) ⟨1589453, by rfl⟩ : syracuseStep 2119271 = 3178907) B3178907
theorem B2384185 : Blo 2117435 2384185 := bbase (se 2 (by rfl) ⟨894069, by rfl⟩ : syracuseStep 2384185 = 1788139) (by norm_num)
theorem B3178913 : Blo 2117435 3178913 := bstep (se 2 (by rfl) ⟨1192092, by rfl⟩ : syracuseStep 3178913 = 2384185) B2384185
theorem B2119275 : Blo 2117435 2119275 := bstep (se 1 (by rfl) ⟨1589456, by rfl⟩ : syracuseStep 2119275 = 3178913) B3178913
theorem B6034981 : Blo 2117435 6034981 := bbase (se 4 (by rfl) ⟨565779, by rfl⟩ : syracuseStep 6034981 = 1131559) (by norm_num)
theorem B8046641 : Blo 2117435 8046641 := bstep (se 2 (by rfl) ⟨3017490, by rfl⟩ : syracuseStep 8046641 = 6034981) B6034981
theorem B5364427 : Blo 2117435 5364427 := bstep (se 1 (by rfl) ⟨4023320, by rfl⟩ : syracuseStep 5364427 = 8046641) B8046641
theorem B7152569 : Blo 2117435 7152569 := bstep (se 2 (by rfl) ⟨2682213, by rfl⟩ : syracuseStep 7152569 = 5364427) B5364427
theorem B4768379 : Blo 2117435 4768379 := bstep (se 1 (by rfl) ⟨3576284, by rfl⟩ : syracuseStep 4768379 = 7152569) B7152569
theorem B3178919 : Blo 2117435 3178919 := bstep (se 1 (by rfl) ⟨2384189, by rfl⟩ : syracuseStep 3178919 = 4768379) B4768379
theorem B2119279 : Blo 2117435 2119279 := bstep (se 1 (by rfl) ⟨1589459, by rfl⟩ : syracuseStep 2119279 = 3178919) B3178919
theorem B3178925 : Blo 2117435 3178925 := bbase (se 3 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 3178925 = 1192097) (by norm_num)
theorem B2119283 : Blo 2117435 2119283 := bstep (se 1 (by rfl) ⟨1589462, by rfl⟩ : syracuseStep 2119283 = 3178925) B3178925
theorem B4768397 : Blo 2117435 4768397 := bbase (se 3 (by rfl) ⟨894074, by rfl⟩ : syracuseStep 4768397 = 1788149) (by norm_num)
theorem B3178931 : Blo 2117435 3178931 := bstep (se 1 (by rfl) ⟨2384198, by rfl⟩ : syracuseStep 3178931 = 4768397) B4768397
theorem B2119287 : Blo 2117435 2119287 := bstep (se 1 (by rfl) ⟨1589465, by rfl⟩ : syracuseStep 2119287 = 3178931) B3178931
theorem B2682229 : Blo 2117435 2682229 := bbase (se 5 (by rfl) ⟨125729, by rfl⟩ : syracuseStep 2682229 = 251459) (by norm_num)
theorem B3576305 : Blo 2117435 3576305 := bstep (se 2 (by rfl) ⟨1341114, by rfl⟩ : syracuseStep 3576305 = 2682229) B2682229
theorem B2384203 : Blo 2117435 2384203 := bstep (se 1 (by rfl) ⟨1788152, by rfl⟩ : syracuseStep 2384203 = 3576305) B3576305
theorem B3178937 : Blo 2117435 3178937 := bstep (se 2 (by rfl) ⟨1192101, by rfl⟩ : syracuseStep 3178937 = 2384203) B2384203
theorem B2119291 : Blo 2117435 2119291 := bstep (se 1 (by rfl) ⟨1589468, by rfl⟩ : syracuseStep 2119291 = 3178937) B3178937
theorem B2718829 : Blo 2117435 2718829 := bbase (se 3 (by rfl) ⟨509780, by rfl⟩ : syracuseStep 2718829 = 1019561) (by norm_num)
theorem B14500421 : Blo 2117435 14500421 := bstep (se 4 (by rfl) ⟨1359414, by rfl⟩ : syracuseStep 14500421 = 2718829) B2718829
theorem B9666947 : Blo 2117435 9666947 := bstep (se 1 (by rfl) ⟨7250210, by rfl⟩ : syracuseStep 9666947 = 14500421) B14500421
theorem B6444631 : Blo 2117435 6444631 := bstep (se 1 (by rfl) ⟨4833473, by rfl⟩ : syracuseStep 6444631 = 9666947) B9666947
theorem B8592841 : Blo 2117435 8592841 := bstep (se 2 (by rfl) ⟨3222315, by rfl⟩ : syracuseStep 8592841 = 6444631) B6444631
theorem B11457121 : Blo 2117435 11457121 := bstep (se 2 (by rfl) ⟨4296420, by rfl⟩ : syracuseStep 11457121 = 8592841) B8592841
theorem B15276161 : Blo 2117435 15276161 := bstep (se 2 (by rfl) ⟨5728560, by rfl⟩ : syracuseStep 15276161 = 11457121) B11457121
theorem B40736429 : Blo 2117435 40736429 := bstep (se 3 (by rfl) ⟨7638080, by rfl⟩ : syracuseStep 40736429 = 15276161) B15276161
theorem B27157619 : Blo 2117435 27157619 := bstep (se 1 (by rfl) ⟨20368214, by rfl⟩ : syracuseStep 27157619 = 40736429) B40736429
theorem B18105079 : Blo 2117435 18105079 := bstep (se 1 (by rfl) ⟨13578809, by rfl⟩ : syracuseStep 18105079 = 27157619) B27157619
theorem B24140105 : Blo 2117435 24140105 := bstep (se 2 (by rfl) ⟨9052539, by rfl⟩ : syracuseStep 24140105 = 18105079) B18105079
theorem B16093403 : Blo 2117435 16093403 := bstep (se 1 (by rfl) ⟨12070052, by rfl⟩ : syracuseStep 16093403 = 24140105) B24140105
theorem B10728935 : Blo 2117435 10728935 := bstep (se 1 (by rfl) ⟨8046701, by rfl⟩ : syracuseStep 10728935 = 16093403) B16093403
theorem B7152623 : Blo 2117435 7152623 := bstep (se 1 (by rfl) ⟨5364467, by rfl⟩ : syracuseStep 7152623 = 10728935) B10728935
theorem B4768415 : Blo 2117435 4768415 := bstep (se 1 (by rfl) ⟨3576311, by rfl⟩ : syracuseStep 4768415 = 7152623) B7152623
theorem B3178943 : Blo 2117435 3178943 := bstep (se 1 (by rfl) ⟨2384207, by rfl⟩ : syracuseStep 3178943 = 4768415) B4768415
theorem B2119295 : Blo 2117435 2119295 := bstep (se 1 (by rfl) ⟨1589471, by rfl⟩ : syracuseStep 2119295 = 3178943) B3178943
theorem B3178949 : Blo 2117435 3178949 := bbase (se 4 (by rfl) ⟨298026, by rfl⟩ : syracuseStep 3178949 = 596053) (by norm_num)
theorem B2119299 : Blo 2117435 2119299 := bstep (se 1 (by rfl) ⟨1589474, by rfl⟩ : syracuseStep 2119299 = 3178949) B3178949
theorem B3576325 : Blo 2117435 3576325 := bbase (se 4 (by rfl) ⟨335280, by rfl⟩ : syracuseStep 3576325 = 670561) (by norm_num)
theorem B4768433 : Blo 2117435 4768433 := bstep (se 2 (by rfl) ⟨1788162, by rfl⟩ : syracuseStep 4768433 = 3576325) B3576325
theorem B3178955 : Blo 2117435 3178955 := bstep (se 1 (by rfl) ⟨2384216, by rfl⟩ : syracuseStep 3178955 = 4768433) B4768433
theorem B2119303 : Blo 2117435 2119303 := bstep (se 1 (by rfl) ⟨1589477, by rfl⟩ : syracuseStep 2119303 = 3178955) B3178955
theorem B2384221 : Blo 2117435 2384221 := bbase (se 3 (by rfl) ⟨447041, by rfl⟩ : syracuseStep 2384221 = 894083) (by norm_num)
theorem B3178961 : Blo 2117435 3178961 := bstep (se 2 (by rfl) ⟨1192110, by rfl⟩ : syracuseStep 3178961 = 2384221) B2384221
theorem B2119307 : Blo 2117435 2119307 := bstep (se 1 (by rfl) ⟨1589480, by rfl⟩ : syracuseStep 2119307 = 3178961) B3178961
theorem B7152677 : Blo 2117435 7152677 := bbase (se 4 (by rfl) ⟨670563, by rfl⟩ : syracuseStep 7152677 = 1341127) (by norm_num)
theorem B4768451 : Blo 2117435 4768451 := bstep (se 1 (by rfl) ⟨3576338, by rfl⟩ : syracuseStep 4768451 = 7152677) B7152677
theorem B3178967 : Blo 2117435 3178967 := bstep (se 1 (by rfl) ⟨2384225, by rfl⟩ : syracuseStep 3178967 = 4768451) B4768451
theorem B2119311 : Blo 2117435 2119311 := bstep (se 1 (by rfl) ⟨1589483, by rfl⟩ : syracuseStep 2119311 = 3178967) B3178967
theorem B3178973 : Blo 2117435 3178973 := bbase (se 3 (by rfl) ⟨596057, by rfl⟩ : syracuseStep 3178973 = 1192115) (by norm_num)
theorem B2119315 : Blo 2117435 2119315 := bstep (se 1 (by rfl) ⟨1589486, by rfl⟩ : syracuseStep 2119315 = 3178973) B3178973
theorem B4768469 : Blo 2117435 4768469 := bbase (se 7 (by rfl) ⟨55880, by rfl⟩ : syracuseStep 4768469 = 111761) (by norm_num)
theorem B3178979 : Blo 2117435 3178979 := bstep (se 1 (by rfl) ⟨2384234, by rfl⟩ : syracuseStep 3178979 = 4768469) B4768469
theorem B2119319 : Blo 2117435 2119319 := bstep (se 1 (by rfl) ⟨1589489, by rfl⟩ : syracuseStep 2119319 = 3178979) B3178979
theorem B9052661 : Blo 2117435 9052661 := bbase (se 5 (by rfl) ⟨424343, by rfl⟩ : syracuseStep 9052661 = 848687) (by norm_num)
theorem B6035107 : Blo 2117435 6035107 := bstep (se 1 (by rfl) ⟨4526330, by rfl⟩ : syracuseStep 6035107 = 9052661) B9052661
theorem B8046809 : Blo 2117435 8046809 := bstep (se 2 (by rfl) ⟨3017553, by rfl⟩ : syracuseStep 8046809 = 6035107) B6035107
theorem B5364539 : Blo 2117435 5364539 := bstep (se 1 (by rfl) ⟨4023404, by rfl⟩ : syracuseStep 5364539 = 8046809) B8046809
theorem B3576359 : Blo 2117435 3576359 := bstep (se 1 (by rfl) ⟨2682269, by rfl⟩ : syracuseStep 3576359 = 5364539) B5364539
theorem B2384239 : Blo 2117435 2384239 := bstep (se 1 (by rfl) ⟨1788179, by rfl⟩ : syracuseStep 2384239 = 3576359) B3576359
theorem B3178985 : Blo 2117435 3178985 := bstep (se 2 (by rfl) ⟨1192119, by rfl⟩ : syracuseStep 3178985 = 2384239) B2384239
theorem B2119323 : Blo 2117435 2119323 := bstep (se 1 (by rfl) ⟨1589492, by rfl⟩ : syracuseStep 2119323 = 3178985) B3178985
theorem B9667093 : Blo 2117435 9667093 := bbase (se 6 (by rfl) ⟨226572, by rfl⟩ : syracuseStep 9667093 = 453145) (by norm_num)
theorem B12889457 : Blo 2117435 12889457 := bstep (se 2 (by rfl) ⟨4833546, by rfl⟩ : syracuseStep 12889457 = 9667093) B9667093
theorem B8592971 : Blo 2117435 8592971 := bstep (se 1 (by rfl) ⟨6444728, by rfl⟩ : syracuseStep 8592971 = 12889457) B12889457
theorem B22914589 : Blo 2117435 22914589 := bstep (se 3 (by rfl) ⟨4296485, by rfl⟩ : syracuseStep 22914589 = 8592971) B8592971
theorem B30552785 : Blo 2117435 30552785 := bstep (se 2 (by rfl) ⟨11457294, by rfl⟩ : syracuseStep 30552785 = 22914589) B22914589
theorem B20368523 : Blo 2117435 20368523 := bstep (se 1 (by rfl) ⟨15276392, by rfl⟩ : syracuseStep 20368523 = 30552785) B30552785
theorem B13579015 : Blo 2117435 13579015 := bstep (se 1 (by rfl) ⟨10184261, by rfl⟩ : syracuseStep 13579015 = 20368523) B20368523
theorem B18105353 : Blo 2117435 18105353 := bstep (se 2 (by rfl) ⟨6789507, by rfl⟩ : syracuseStep 18105353 = 13579015) B13579015
theorem B12070235 : Blo 2117435 12070235 := bstep (se 1 (by rfl) ⟨9052676, by rfl⟩ : syracuseStep 12070235 = 18105353) B18105353
theorem B8046823 : Blo 2117435 8046823 := bstep (se 1 (by rfl) ⟨6035117, by rfl⟩ : syracuseStep 8046823 = 12070235) B12070235
theorem B10729097 : Blo 2117435 10729097 := bstep (se 2 (by rfl) ⟨4023411, by rfl⟩ : syracuseStep 10729097 = 8046823) B8046823
theorem B7152731 : Blo 2117435 7152731 := bstep (se 1 (by rfl) ⟨5364548, by rfl⟩ : syracuseStep 7152731 = 10729097) B10729097
theorem B4768487 : Blo 2117435 4768487 := bstep (se 1 (by rfl) ⟨3576365, by rfl⟩ : syracuseStep 4768487 = 7152731) B7152731
theorem B3178991 : Blo 2117435 3178991 := bstep (se 1 (by rfl) ⟨2384243, by rfl⟩ : syracuseStep 3178991 = 4768487) B4768487
theorem B2119327 : Blo 2117435 2119327 := bstep (se 1 (by rfl) ⟨1589495, by rfl⟩ : syracuseStep 2119327 = 3178991) B3178991
theorem B3178997 : Blo 2117435 3178997 := bbase (se 5 (by rfl) ⟨149015, by rfl⟩ : syracuseStep 3178997 = 298031) (by norm_num)
theorem B2119331 : Blo 2117435 2119331 := bstep (se 1 (by rfl) ⟨1589498, by rfl⟩ : syracuseStep 2119331 = 3178997) B3178997
theorem B6035141 : Blo 2117435 6035141 := bbase (se 4 (by rfl) ⟨565794, by rfl⟩ : syracuseStep 6035141 = 1131589) (by norm_num)
theorem B4023427 : Blo 2117435 4023427 := bstep (se 1 (by rfl) ⟨3017570, by rfl⟩ : syracuseStep 4023427 = 6035141) B6035141
theorem B5364569 : Blo 2117435 5364569 := bstep (se 2 (by rfl) ⟨2011713, by rfl⟩ : syracuseStep 5364569 = 4023427) B4023427
theorem B3576379 : Blo 2117435 3576379 := bstep (se 1 (by rfl) ⟨2682284, by rfl⟩ : syracuseStep 3576379 = 5364569) B5364569
theorem B4768505 : Blo 2117435 4768505 := bstep (se 2 (by rfl) ⟨1788189, by rfl⟩ : syracuseStep 4768505 = 3576379) B3576379
theorem B3179003 : Blo 2117435 3179003 := bstep (se 1 (by rfl) ⟨2384252, by rfl⟩ : syracuseStep 3179003 = 4768505) B4768505
theorem B2119335 : Blo 2117435 2119335 := bstep (se 1 (by rfl) ⟨1589501, by rfl⟩ : syracuseStep 2119335 = 3179003) B3179003
theorem B2384257 : Blo 2117435 2384257 := bbase (se 2 (by rfl) ⟨894096, by rfl⟩ : syracuseStep 2384257 = 1788193) (by norm_num)
theorem B3179009 : Blo 2117435 3179009 := bstep (se 2 (by rfl) ⟨1192128, by rfl⟩ : syracuseStep 3179009 = 2384257) B2384257
theorem B2119339 : Blo 2117435 2119339 := bstep (se 1 (by rfl) ⟨1589504, by rfl⟩ : syracuseStep 2119339 = 3179009) B3179009
theorem B5364589 : Blo 2117435 5364589 := bbase (se 3 (by rfl) ⟨1005860, by rfl⟩ : syracuseStep 5364589 = 2011721) (by norm_num)
theorem B7152785 : Blo 2117435 7152785 := bstep (se 2 (by rfl) ⟨2682294, by rfl⟩ : syracuseStep 7152785 = 5364589) B5364589
theorem B4768523 : Blo 2117435 4768523 := bstep (se 1 (by rfl) ⟨3576392, by rfl⟩ : syracuseStep 4768523 = 7152785) B7152785
theorem B3179015 : Blo 2117435 3179015 := bstep (se 1 (by rfl) ⟨2384261, by rfl⟩ : syracuseStep 3179015 = 4768523) B4768523
theorem B2119343 : Blo 2117435 2119343 := bstep (se 1 (by rfl) ⟨1589507, by rfl⟩ : syracuseStep 2119343 = 3179015) B3179015
theorem B3179021 : Blo 2117435 3179021 := bbase (se 3 (by rfl) ⟨596066, by rfl⟩ : syracuseStep 3179021 = 1192133) (by norm_num)
theorem B2119347 : Blo 2117435 2119347 := bstep (se 1 (by rfl) ⟨1589510, by rfl⟩ : syracuseStep 2119347 = 3179021) B3179021
theorem B4768541 : Blo 2117435 4768541 := bbase (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) (by norm_num)
theorem B3179027 : Blo 2117435 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B2119351 : Blo 2117435 2119351 := bstep (se 1 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 2119351 = 3179027) B3179027
theorem B3576413 : Blo 2117435 3576413 := bbase (se 3 (by rfl) ⟨670577, by rfl⟩ : syracuseStep 3576413 = 1341155) (by norm_num)
theorem B2384275 : Blo 2117435 2384275 := bstep (se 1 (by rfl) ⟨1788206, by rfl⟩ : syracuseStep 2384275 = 3576413) B3576413
theorem B3179033 : Blo 2117435 3179033 := bstep (se 2 (by rfl) ⟨1192137, by rfl⟩ : syracuseStep 3179033 = 2384275) B2384275
theorem B2119355 : Blo 2117435 2119355 := bstep (se 1 (by rfl) ⟨1589516, by rfl⟩ : syracuseStep 2119355 = 3179033) B3179033
theorem B3394805 : Blo 2117435 3394805 := bbase (se 5 (by rfl) ⟨159131, by rfl⟩ : syracuseStep 3394805 = 318263) (by norm_num)
theorem B9052813 : Blo 2117435 9052813 := bstep (se 3 (by rfl) ⟨1697402, by rfl⟩ : syracuseStep 9052813 = 3394805) B3394805
theorem B12070417 : Blo 2117435 12070417 := bstep (se 2 (by rfl) ⟨4526406, by rfl⟩ : syracuseStep 12070417 = 9052813) B9052813
theorem B16093889 : Blo 2117435 16093889 := bstep (se 2 (by rfl) ⟨6035208, by rfl⟩ : syracuseStep 16093889 = 12070417) B12070417
theorem B10729259 : Blo 2117435 10729259 := bstep (se 1 (by rfl) ⟨8046944, by rfl⟩ : syracuseStep 10729259 = 16093889) B16093889
theorem B7152839 : Blo 2117435 7152839 := bstep (se 1 (by rfl) ⟨5364629, by rfl⟩ : syracuseStep 7152839 = 10729259) B10729259
theorem B4768559 : Blo 2117435 4768559 := bstep (se 1 (by rfl) ⟨3576419, by rfl⟩ : syracuseStep 4768559 = 7152839) B7152839
theorem B3179039 : Blo 2117435 3179039 := bstep (se 1 (by rfl) ⟨2384279, by rfl⟩ : syracuseStep 3179039 = 4768559) B4768559
theorem B2119359 : Blo 2117435 2119359 := bstep (se 1 (by rfl) ⟨1589519, by rfl⟩ : syracuseStep 2119359 = 3179039) B3179039
theorem B3179045 : Blo 2117435 3179045 := bbase (se 4 (by rfl) ⟨298035, by rfl⟩ : syracuseStep 3179045 = 596071) (by norm_num)
theorem B2119363 : Blo 2117435 2119363 := bstep (se 1 (by rfl) ⟨1589522, by rfl⟩ : syracuseStep 2119363 = 3179045) B3179045
theorem B2682325 : Blo 2117435 2682325 := bbase (se 7 (by rfl) ⟨31433, by rfl⟩ : syracuseStep 2682325 = 62867) (by norm_num)
theorem B3576433 : Blo 2117435 3576433 := bstep (se 2 (by rfl) ⟨1341162, by rfl⟩ : syracuseStep 3576433 = 2682325) B2682325
theorem B4768577 : Blo 2117435 4768577 := bstep (se 2 (by rfl) ⟨1788216, by rfl⟩ : syracuseStep 4768577 = 3576433) B3576433
theorem B3179051 : Blo 2117435 3179051 := bstep (se 1 (by rfl) ⟨2384288, by rfl⟩ : syracuseStep 3179051 = 4768577) B4768577
theorem B2119367 : Blo 2117435 2119367 := bstep (se 1 (by rfl) ⟨1589525, by rfl⟩ : syracuseStep 2119367 = 3179051) B3179051
theorem B2384293 : Blo 2117435 2384293 := bbase (se 4 (by rfl) ⟨223527, by rfl⟩ : syracuseStep 2384293 = 447055) (by norm_num)
theorem B3179057 : Blo 2117435 3179057 := bstep (se 2 (by rfl) ⟨1192146, by rfl⟩ : syracuseStep 3179057 = 2384293) B2384293
theorem B2119371 : Blo 2117435 2119371 := bstep (se 1 (by rfl) ⟨1589528, by rfl⟩ : syracuseStep 2119371 = 3179057) B3179057
theorem B11457557 : Blo 2117435 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B7638371 : Blo 2117435 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B5092247 : Blo 2117435 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B13579325 : Blo 2117435 13579325 := bstep (se 3 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 13579325 = 5092247) B5092247
theorem B9052883 : Blo 2117435 9052883 := bstep (se 1 (by rfl) ⟨6789662, by rfl⟩ : syracuseStep 9052883 = 13579325) B13579325
theorem B6035255 : Blo 2117435 6035255 := bstep (se 1 (by rfl) ⟨4526441, by rfl⟩ : syracuseStep 6035255 = 9052883) B9052883
theorem B4023503 : Blo 2117435 4023503 := bstep (se 1 (by rfl) ⟨3017627, by rfl⟩ : syracuseStep 4023503 = 6035255) B6035255
theorem B2682335 : Blo 2117435 2682335 := bstep (se 1 (by rfl) ⟨2011751, by rfl⟩ : syracuseStep 2682335 = 4023503) B4023503
theorem B7152893 : Blo 2117435 7152893 := bstep (se 3 (by rfl) ⟨1341167, by rfl⟩ : syracuseStep 7152893 = 2682335) B2682335
theorem B4768595 : Blo 2117435 4768595 := bstep (se 1 (by rfl) ⟨3576446, by rfl⟩ : syracuseStep 4768595 = 7152893) B7152893
theorem B3179063 : Blo 2117435 3179063 := bstep (se 1 (by rfl) ⟨2384297, by rfl⟩ : syracuseStep 3179063 = 4768595) B4768595
theorem B2119375 : Blo 2117435 2119375 := bstep (se 1 (by rfl) ⟨1589531, by rfl⟩ : syracuseStep 2119375 = 3179063) B3179063
theorem B3179069 : Blo 2117435 3179069 := bbase (se 3 (by rfl) ⟨596075, by rfl⟩ : syracuseStep 3179069 = 1192151) (by norm_num)
theorem B2119379 : Blo 2117435 2119379 := bstep (se 1 (by rfl) ⟨1589534, by rfl⟩ : syracuseStep 2119379 = 3179069) B3179069
theorem B4768613 : Blo 2117435 4768613 := bbase (se 4 (by rfl) ⟨447057, by rfl⟩ : syracuseStep 4768613 = 894115) (by norm_num)
theorem B3179075 : Blo 2117435 3179075 := bstep (se 1 (by rfl) ⟨2384306, by rfl⟩ : syracuseStep 3179075 = 4768613) B4768613
theorem B2119383 : Blo 2117435 2119383 := bstep (se 1 (by rfl) ⟨1589537, by rfl⟩ : syracuseStep 2119383 = 3179075) B3179075
theorem B5364701 : Blo 2117435 5364701 := bbase (se 3 (by rfl) ⟨1005881, by rfl⟩ : syracuseStep 5364701 = 2011763) (by norm_num)
theorem B3576467 : Blo 2117435 3576467 := bstep (se 1 (by rfl) ⟨2682350, by rfl⟩ : syracuseStep 3576467 = 5364701) B5364701
theorem B2384311 : Blo 2117435 2384311 := bstep (se 1 (by rfl) ⟨1788233, by rfl⟩ : syracuseStep 2384311 = 3576467) B3576467
theorem B3179081 : Blo 2117435 3179081 := bstep (se 2 (by rfl) ⟨1192155, by rfl⟩ : syracuseStep 3179081 = 2384311) B2384311
theorem B2119387 : Blo 2117435 2119387 := bstep (se 1 (by rfl) ⟨1589540, by rfl⟩ : syracuseStep 2119387 = 3179081) B3179081
theorem B4023533 : Blo 2117435 4023533 := bbase (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) (by norm_num)
theorem B10729421 : Blo 2117435 10729421 := bstep (se 3 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 10729421 = 4023533) B4023533
theorem B7152947 : Blo 2117435 7152947 := bstep (se 1 (by rfl) ⟨5364710, by rfl⟩ : syracuseStep 7152947 = 10729421) B10729421
theorem B4768631 : Blo 2117435 4768631 := bstep (se 1 (by rfl) ⟨3576473, by rfl⟩ : syracuseStep 4768631 = 7152947) B7152947
theorem B3179087 : Blo 2117435 3179087 := bstep (se 1 (by rfl) ⟨2384315, by rfl⟩ : syracuseStep 3179087 = 4768631) B4768631
theorem B2119391 : Blo 2117435 2119391 := bstep (se 1 (by rfl) ⟨1589543, by rfl⟩ : syracuseStep 2119391 = 3179087) B3179087
theorem B3179093 : Blo 2117435 3179093 := bbase (se 8 (by rfl) ⟨18627, by rfl⟩ : syracuseStep 3179093 = 37255) (by norm_num)
theorem B2119395 : Blo 2117435 2119395 := bstep (se 1 (by rfl) ⟨1589546, by rfl⟩ : syracuseStep 2119395 = 3179093) B3179093
theorem B6444949 : Blo 2117435 6444949 := bbase (se 6 (by rfl) ⟨151053, by rfl⟩ : syracuseStep 6444949 = 302107) (by norm_num)
theorem B8593265 : Blo 2117435 8593265 := bstep (se 2 (by rfl) ⟨3222474, by rfl⟩ : syracuseStep 8593265 = 6444949) B6444949
theorem B5728843 : Blo 2117435 5728843 := bstep (se 1 (by rfl) ⟨4296632, by rfl⟩ : syracuseStep 5728843 = 8593265) B8593265
theorem B7638457 : Blo 2117435 7638457 := bstep (se 2 (by rfl) ⟨2864421, by rfl⟩ : syracuseStep 7638457 = 5728843) B5728843
theorem B10184609 : Blo 2117435 10184609 := bstep (se 2 (by rfl) ⟨3819228, by rfl⟩ : syracuseStep 10184609 = 7638457) B7638457
theorem B6789739 : Blo 2117435 6789739 := bstep (se 1 (by rfl) ⟨5092304, by rfl⟩ : syracuseStep 6789739 = 10184609) B10184609
theorem B9052985 : Blo 2117435 9052985 := bstep (se 2 (by rfl) ⟨3394869, by rfl⟩ : syracuseStep 9052985 = 6789739) B6789739
theorem B6035323 : Blo 2117435 6035323 := bstep (se 1 (by rfl) ⟨4526492, by rfl⟩ : syracuseStep 6035323 = 9052985) B9052985
theorem B8047097 : Blo 2117435 8047097 := bstep (se 2 (by rfl) ⟨3017661, by rfl⟩ : syracuseStep 8047097 = 6035323) B6035323
theorem B5364731 : Blo 2117435 5364731 := bstep (se 1 (by rfl) ⟨4023548, by rfl⟩ : syracuseStep 5364731 = 8047097) B8047097
theorem B3576487 : Blo 2117435 3576487 := bstep (se 1 (by rfl) ⟨2682365, by rfl⟩ : syracuseStep 3576487 = 5364731) B5364731
theorem B4768649 : Blo 2117435 4768649 := bstep (se 2 (by rfl) ⟨1788243, by rfl⟩ : syracuseStep 4768649 = 3576487) B3576487
theorem B3179099 : Blo 2117435 3179099 := bstep (se 1 (by rfl) ⟨2384324, by rfl⟩ : syracuseStep 3179099 = 4768649) B4768649
theorem B2119399 : Blo 2117435 2119399 := bstep (se 1 (by rfl) ⟨1589549, by rfl⟩ : syracuseStep 2119399 = 3179099) B3179099
theorem B2384329 : Blo 2117435 2384329 := bbase (se 2 (by rfl) ⟨894123, by rfl⟩ : syracuseStep 2384329 = 1788247) (by norm_num)
theorem B3179105 : Blo 2117435 3179105 := bstep (se 2 (by rfl) ⟨1192164, by rfl⟩ : syracuseStep 3179105 = 2384329) B2384329
theorem B2119403 : Blo 2117435 2119403 := bstep (se 1 (by rfl) ⟨1589552, by rfl⟩ : syracuseStep 2119403 = 3179105) B3179105
theorem B18106037 : Blo 2117435 18106037 := bbase (se 5 (by rfl) ⟨848720, by rfl⟩ : syracuseStep 18106037 = 1697441) (by norm_num)
theorem B12070691 : Blo 2117435 12070691 := bstep (se 1 (by rfl) ⟨9053018, by rfl⟩ : syracuseStep 12070691 = 18106037) B18106037
theorem B8047127 : Blo 2117435 8047127 := bstep (se 1 (by rfl) ⟨6035345, by rfl⟩ : syracuseStep 8047127 = 12070691) B12070691
theorem B5364751 : Blo 2117435 5364751 := bstep (se 1 (by rfl) ⟨4023563, by rfl⟩ : syracuseStep 5364751 = 8047127) B8047127
theorem B7153001 : Blo 2117435 7153001 := bstep (se 2 (by rfl) ⟨2682375, by rfl⟩ : syracuseStep 7153001 = 5364751) B5364751
theorem B4768667 : Blo 2117435 4768667 := bstep (se 1 (by rfl) ⟨3576500, by rfl⟩ : syracuseStep 4768667 = 7153001) B7153001
theorem B3179111 : Blo 2117435 3179111 := bstep (se 1 (by rfl) ⟨2384333, by rfl⟩ : syracuseStep 3179111 = 4768667) B4768667
theorem B2119407 : Blo 2117435 2119407 := bstep (se 1 (by rfl) ⟨1589555, by rfl⟩ : syracuseStep 2119407 = 3179111) B3179111
theorem B3179117 : Blo 2117435 3179117 := bbase (se 3 (by rfl) ⟨596084, by rfl⟩ : syracuseStep 3179117 = 1192169) (by norm_num)
theorem B2119411 : Blo 2117435 2119411 := bstep (se 1 (by rfl) ⟨1589558, by rfl⟩ : syracuseStep 2119411 = 3179117) B3179117
theorem B4768685 : Blo 2117435 4768685 := bbase (se 3 (by rfl) ⟨894128, by rfl⟩ : syracuseStep 4768685 = 1788257) (by norm_num)
theorem B3179123 : Blo 2117435 3179123 := bstep (se 1 (by rfl) ⟨2384342, by rfl⟩ : syracuseStep 3179123 = 4768685) B4768685
theorem B2119415 : Blo 2117435 2119415 := bstep (se 1 (by rfl) ⟨1589561, by rfl⟩ : syracuseStep 2119415 = 3179123) B3179123
theorem B6035381 : Blo 2117435 6035381 := bbase (se 5 (by rfl) ⟨282908, by rfl⟩ : syracuseStep 6035381 = 565817) (by norm_num)
theorem B4023587 : Blo 2117435 4023587 := bstep (se 1 (by rfl) ⟨3017690, by rfl⟩ : syracuseStep 4023587 = 6035381) B6035381
theorem B2682391 : Blo 2117435 2682391 := bstep (se 1 (by rfl) ⟨2011793, by rfl⟩ : syracuseStep 2682391 = 4023587) B4023587
theorem B3576521 : Blo 2117435 3576521 := bstep (se 2 (by rfl) ⟨1341195, by rfl⟩ : syracuseStep 3576521 = 2682391) B2682391
theorem B2384347 : Blo 2117435 2384347 := bstep (se 1 (by rfl) ⟨1788260, by rfl⟩ : syracuseStep 2384347 = 3576521) B3576521
theorem B3179129 : Blo 2117435 3179129 := bstep (se 2 (by rfl) ⟨1192173, by rfl⟩ : syracuseStep 3179129 = 2384347) B2384347
theorem B2119419 : Blo 2117435 2119419 := bstep (se 1 (by rfl) ⟨1589564, by rfl⟩ : syracuseStep 2119419 = 3179129) B3179129
theorem B3266477 : Blo 2117435 3266477 := bbase (se 3 (by rfl) ⟨612464, by rfl⟩ : syracuseStep 3266477 = 1224929) (by norm_num)
theorem B2177651 : Blo 2117435 2177651 := bstep (se 1 (by rfl) ⟨1633238, by rfl⟩ : syracuseStep 2177651 = 3266477) B3266477
theorem B5807069 : Blo 2117435 5807069 := bstep (se 3 (by rfl) ⟨1088825, by rfl⟩ : syracuseStep 5807069 = 2177651) B2177651
theorem B3871379 : Blo 2117435 3871379 := bstep (se 1 (by rfl) ⟨2903534, by rfl⟩ : syracuseStep 3871379 = 5807069) B5807069
theorem B2580919 : Blo 2117435 2580919 := bstep (se 1 (by rfl) ⟨1935689, by rfl⟩ : syracuseStep 2580919 = 3871379) B3871379
theorem B55059605 : Blo 2117435 55059605 := bstep (se 6 (by rfl) ⟨1290459, by rfl⟩ : syracuseStep 55059605 = 2580919) B2580919
theorem B36706403 : Blo 2117435 36706403 := bstep (se 1 (by rfl) ⟨27529802, by rfl⟩ : syracuseStep 36706403 = 55059605) B55059605
theorem B97883741 : Blo 2117435 97883741 := bstep (se 3 (by rfl) ⟨18353201, by rfl⟩ : syracuseStep 97883741 = 36706403) B36706403
theorem B65255827 : Blo 2117435 65255827 := bstep (se 1 (by rfl) ⟨48941870, by rfl⟩ : syracuseStep 65255827 = 97883741) B97883741
theorem B87007769 : Blo 2117435 87007769 := bstep (se 2 (by rfl) ⟨32627913, by rfl⟩ : syracuseStep 87007769 = 65255827) B65255827
theorem B58005179 : Blo 2117435 58005179 := bstep (se 1 (by rfl) ⟨43503884, by rfl⟩ : syracuseStep 58005179 = 87007769) B87007769
theorem B38670119 : Blo 2117435 38670119 := bstep (se 1 (by rfl) ⟨29002589, by rfl⟩ : syracuseStep 38670119 = 58005179) B58005179
theorem B25780079 : Blo 2117435 25780079 := bstep (se 1 (by rfl) ⟨19335059, by rfl⟩ : syracuseStep 25780079 = 38670119) B38670119
theorem B68746877 : Blo 2117435 68746877 := bstep (se 3 (by rfl) ⟨12890039, by rfl⟩ : syracuseStep 68746877 = 25780079) B25780079
theorem B45831251 : Blo 2117435 45831251 := bstep (se 1 (by rfl) ⟨34373438, by rfl⟩ : syracuseStep 45831251 = 68746877) B68746877
theorem B30554167 : Blo 2117435 30554167 := bstep (se 1 (by rfl) ⟨22915625, by rfl⟩ : syracuseStep 30554167 = 45831251) B45831251
theorem B40738889 : Blo 2117435 40738889 := bstep (se 2 (by rfl) ⟨15277083, by rfl⟩ : syracuseStep 40738889 = 30554167) B30554167
theorem B27159259 : Blo 2117435 27159259 := bstep (se 1 (by rfl) ⟨20369444, by rfl⟩ : syracuseStep 27159259 = 40738889) B40738889
theorem B36212345 : Blo 2117435 36212345 := bstep (se 2 (by rfl) ⟨13579629, by rfl⟩ : syracuseStep 36212345 = 27159259) B27159259
theorem B24141563 : Blo 2117435 24141563 := bstep (se 1 (by rfl) ⟨18106172, by rfl⟩ : syracuseStep 24141563 = 36212345) B36212345
theorem B16094375 : Blo 2117435 16094375 := bstep (se 1 (by rfl) ⟨12070781, by rfl⟩ : syracuseStep 16094375 = 24141563) B24141563
theorem B10729583 : Blo 2117435 10729583 := bstep (se 1 (by rfl) ⟨8047187, by rfl⟩ : syracuseStep 10729583 = 16094375) B16094375
theorem B7153055 : Blo 2117435 7153055 := bstep (se 1 (by rfl) ⟨5364791, by rfl⟩ : syracuseStep 7153055 = 10729583) B10729583
theorem B4768703 : Blo 2117435 4768703 := bstep (se 1 (by rfl) ⟨3576527, by rfl⟩ : syracuseStep 4768703 = 7153055) B7153055
theorem B3179135 : Blo 2117435 3179135 := bstep (se 1 (by rfl) ⟨2384351, by rfl⟩ : syracuseStep 3179135 = 4768703) B4768703
theorem B2119423 : Blo 2117435 2119423 := bstep (se 1 (by rfl) ⟨1589567, by rfl⟩ : syracuseStep 2119423 = 3179135) B3179135
theorem B3179141 : Blo 2117435 3179141 := bbase (se 4 (by rfl) ⟨298044, by rfl⟩ : syracuseStep 3179141 = 596089) (by norm_num)
theorem B2119427 : Blo 2117435 2119427 := bstep (se 1 (by rfl) ⟨1589570, by rfl⟩ : syracuseStep 2119427 = 3179141) B3179141
theorem B3576541 : Blo 2117435 3576541 := bbase (se 3 (by rfl) ⟨670601, by rfl⟩ : syracuseStep 3576541 = 1341203) (by norm_num)
theorem B4768721 : Blo 2117435 4768721 := bstep (se 2 (by rfl) ⟨1788270, by rfl⟩ : syracuseStep 4768721 = 3576541) B3576541
theorem B3179147 : Blo 2117435 3179147 := bstep (se 1 (by rfl) ⟨2384360, by rfl⟩ : syracuseStep 3179147 = 4768721) B4768721
theorem B2119431 : Blo 2117435 2119431 := bstep (se 1 (by rfl) ⟨1589573, by rfl⟩ : syracuseStep 2119431 = 3179147) B3179147
theorem B2384365 : Blo 2117435 2384365 := bbase (se 3 (by rfl) ⟨447068, by rfl⟩ : syracuseStep 2384365 = 894137) (by norm_num)
theorem B3179153 : Blo 2117435 3179153 := bstep (se 2 (by rfl) ⟨1192182, by rfl⟩ : syracuseStep 3179153 = 2384365) B2384365
theorem B2119435 : Blo 2117435 2119435 := bstep (se 1 (by rfl) ⟨1589576, by rfl⟩ : syracuseStep 2119435 = 3179153) B3179153
theorem C0 (j : ℕ) (h1 : 529358 ≤ j) (h2 : j ≤ 529858) : Blo 2117435 (4 * j + 3) := by
  interval_cases j
  · exact B2117435
  · exact B2117439
  · exact B2117443
  · exact B2117447
  · exact B2117451
  · exact B2117455
  · exact B2117459
  · exact B2117463
  · exact B2117467
  · exact B2117471
  · exact B2117475
  · exact B2117479
  · exact B2117483
  · exact B2117487
  · exact B2117491
  · exact B2117495
  · exact B2117499
  · exact B2117503
  · exact B2117507
  · exact B2117511
  · exact B2117515
  · exact B2117519
  · exact B2117523
  · exact B2117527
  · exact B2117531
  · exact B2117535
  · exact B2117539
  · exact B2117543
  · exact B2117547
  · exact B2117551
  · exact B2117555
  · exact B2117559
  · exact B2117563
  · exact B2117567
  · exact B2117571
  · exact B2117575
  · exact B2117579
  · exact B2117583
  · exact B2117587
  · exact B2117591
  · exact B2117595
  · exact B2117599
  · exact B2117603
  · exact B2117607
  · exact B2117611
  · exact B2117615
  · exact B2117619
  · exact B2117623
  · exact B2117627
  · exact B2117631
  · exact B2117635
  · exact B2117639
  · exact B2117643
  · exact B2117647
  · exact B2117651
  · exact B2117655
  · exact B2117659
  · exact B2117663
  · exact B2117667
  · exact B2117671
  · exact B2117675
  · exact B2117679
  · exact B2117683
  · exact B2117687
  · exact B2117691
  · exact B2117695
  · exact B2117699
  · exact B2117703
  · exact B2117707
  · exact B2117711
  · exact B2117715
  · exact B2117719
  · exact B2117723
  · exact B2117727
  · exact B2117731
  · exact B2117735
  · exact B2117739
  · exact B2117743
  · exact B2117747
  · exact B2117751
  · exact B2117755
  · exact B2117759
  · exact B2117763
  · exact B2117767
  · exact B2117771
  · exact B2117775
  · exact B2117779
  · exact B2117783
  · exact B2117787
  · exact B2117791
  · exact B2117795
  · exact B2117799
  · exact B2117803
  · exact B2117807
  · exact B2117811
  · exact B2117815
  · exact B2117819
  · exact B2117823
  · exact B2117827
  · exact B2117831
  · exact B2117835
  · exact B2117839
  · exact B2117843
  · exact B2117847
  · exact B2117851
  · exact B2117855
  · exact B2117859
  · exact B2117863
  · exact B2117867
  · exact B2117871
  · exact B2117875
  · exact B2117879
  · exact B2117883
  · exact B2117887
  · exact B2117891
  · exact B2117895
  · exact B2117899
  · exact B2117903
  · exact B2117907
  · exact B2117911
  · exact B2117915
  · exact B2117919
  · exact B2117923
  · exact B2117927
  · exact B2117931
  · exact B2117935
  · exact B2117939
  · exact B2117943
  · exact B2117947
  · exact B2117951
  · exact B2117955
  · exact B2117959
  · exact B2117963
  · exact B2117967
  · exact B2117971
  · exact B2117975
  · exact B2117979
  · exact B2117983
  · exact B2117987
  · exact B2117991
  · exact B2117995
  · exact B2117999
  · exact B2118003
  · exact B2118007
  · exact B2118011
  · exact B2118015
  · exact B2118019
  · exact B2118023
  · exact B2118027
  · exact B2118031
  · exact B2118035
  · exact B2118039
  · exact B2118043
  · exact B2118047
  · exact B2118051
  · exact B2118055
  · exact B2118059
  · exact B2118063
  · exact B2118067
  · exact B2118071
  · exact B2118075
  · exact B2118079
  · exact B2118083
  · exact B2118087
  · exact B2118091
  · exact B2118095
  · exact B2118099
  · exact B2118103
  · exact B2118107
  · exact B2118111
  · exact B2118115
  · exact B2118119
  · exact B2118123
  · exact B2118127
  · exact B2118131
  · exact B2118135
  · exact B2118139
  · exact B2118143
  · exact B2118147
  · exact B2118151
  · exact B2118155
  · exact B2118159
  · exact B2118163
  · exact B2118167
  · exact B2118171
  · exact B2118175
  · exact B2118179
  · exact B2118183
  · exact B2118187
  · exact B2118191
  · exact B2118195
  · exact B2118199
  · exact B2118203
  · exact B2118207
  · exact B2118211
  · exact B2118215
  · exact B2118219
  · exact B2118223
  · exact B2118227
  · exact B2118231
  · exact B2118235
  · exact B2118239
  · exact B2118243
  · exact B2118247
  · exact B2118251
  · exact B2118255
  · exact B2118259
  · exact B2118263
  · exact B2118267
  · exact B2118271
  · exact B2118275
  · exact B2118279
  · exact B2118283
  · exact B2118287
  · exact B2118291
  · exact B2118295
  · exact B2118299
  · exact B2118303
  · exact B2118307
  · exact B2118311
  · exact B2118315
  · exact B2118319
  · exact B2118323
  · exact B2118327
  · exact B2118331
  · exact B2118335
  · exact B2118339
  · exact B2118343
  · exact B2118347
  · exact B2118351
  · exact B2118355
  · exact B2118359
  · exact B2118363
  · exact B2118367
  · exact B2118371
  · exact B2118375
  · exact B2118379
  · exact B2118383
  · exact B2118387
  · exact B2118391
  · exact B2118395
  · exact B2118399
  · exact B2118403
  · exact B2118407
  · exact B2118411
  · exact B2118415
  · exact B2118419
  · exact B2118423
  · exact B2118427
  · exact B2118431
  · exact B2118435
  · exact B2118439
  · exact B2118443
  · exact B2118447
  · exact B2118451
  · exact B2118455
  · exact B2118459
  · exact B2118463
  · exact B2118467
  · exact B2118471
  · exact B2118475
  · exact B2118479
  · exact B2118483
  · exact B2118487
  · exact B2118491
  · exact B2118495
  · exact B2118499
  · exact B2118503
  · exact B2118507
  · exact B2118511
  · exact B2118515
  · exact B2118519
  · exact B2118523
  · exact B2118527
  · exact B2118531
  · exact B2118535
  · exact B2118539
  · exact B2118543
  · exact B2118547
  · exact B2118551
  · exact B2118555
  · exact B2118559
  · exact B2118563
  · exact B2118567
  · exact B2118571
  · exact B2118575
  · exact B2118579
  · exact B2118583
  · exact B2118587
  · exact B2118591
  · exact B2118595
  · exact B2118599
  · exact B2118603
  · exact B2118607
  · exact B2118611
  · exact B2118615
  · exact B2118619
  · exact B2118623
  · exact B2118627
  · exact B2118631
  · exact B2118635
  · exact B2118639
  · exact B2118643
  · exact B2118647
  · exact B2118651
  · exact B2118655
  · exact B2118659
  · exact B2118663
  · exact B2118667
  · exact B2118671
  · exact B2118675
  · exact B2118679
  · exact B2118683
  · exact B2118687
  · exact B2118691
  · exact B2118695
  · exact B2118699
  · exact B2118703
  · exact B2118707
  · exact B2118711
  · exact B2118715
  · exact B2118719
  · exact B2118723
  · exact B2118727
  · exact B2118731
  · exact B2118735
  · exact B2118739
  · exact B2118743
  · exact B2118747
  · exact B2118751
  · exact B2118755
  · exact B2118759
  · exact B2118763
  · exact B2118767
  · exact B2118771
  · exact B2118775
  · exact B2118779
  · exact B2118783
  · exact B2118787
  · exact B2118791
  · exact B2118795
  · exact B2118799
  · exact B2118803
  · exact B2118807
  · exact B2118811
  · exact B2118815
  · exact B2118819
  · exact B2118823
  · exact B2118827
  · exact B2118831
  · exact B2118835
  · exact B2118839
  · exact B2118843
  · exact B2118847
  · exact B2118851
  · exact B2118855
  · exact B2118859
  · exact B2118863
  · exact B2118867
  · exact B2118871
  · exact B2118875
  · exact B2118879
  · exact B2118883
  · exact B2118887
  · exact B2118891
  · exact B2118895
  · exact B2118899
  · exact B2118903
  · exact B2118907
  · exact B2118911
  · exact B2118915
  · exact B2118919
  · exact B2118923
  · exact B2118927
  · exact B2118931
  · exact B2118935
  · exact B2118939
  · exact B2118943
  · exact B2118947
  · exact B2118951
  · exact B2118955
  · exact B2118959
  · exact B2118963
  · exact B2118967
  · exact B2118971
  · exact B2118975
  · exact B2118979
  · exact B2118983
  · exact B2118987
  · exact B2118991
  · exact B2118995
  · exact B2118999
  · exact B2119003
  · exact B2119007
  · exact B2119011
  · exact B2119015
  · exact B2119019
  · exact B2119023
  · exact B2119027
  · exact B2119031
  · exact B2119035
  · exact B2119039
  · exact B2119043
  · exact B2119047
  · exact B2119051
  · exact B2119055
  · exact B2119059
  · exact B2119063
  · exact B2119067
  · exact B2119071
  · exact B2119075
  · exact B2119079
  · exact B2119083
  · exact B2119087
  · exact B2119091
  · exact B2119095
  · exact B2119099
  · exact B2119103
  · exact B2119107
  · exact B2119111
  · exact B2119115
  · exact B2119119
  · exact B2119123
  · exact B2119127
  · exact B2119131
  · exact B2119135
  · exact B2119139
  · exact B2119143
  · exact B2119147
  · exact B2119151
  · exact B2119155
  · exact B2119159
  · exact B2119163
  · exact B2119167
  · exact B2119171
  · exact B2119175
  · exact B2119179
  · exact B2119183
  · exact B2119187
  · exact B2119191
  · exact B2119195
  · exact B2119199
  · exact B2119203
  · exact B2119207
  · exact B2119211
  · exact B2119215
  · exact B2119219
  · exact B2119223
  · exact B2119227
  · exact B2119231
  · exact B2119235
  · exact B2119239
  · exact B2119243
  · exact B2119247
  · exact B2119251
  · exact B2119255
  · exact B2119259
  · exact B2119263
  · exact B2119267
  · exact B2119271
  · exact B2119275
  · exact B2119279
  · exact B2119283
  · exact B2119287
  · exact B2119291
  · exact B2119295
  · exact B2119299
  · exact B2119303
  · exact B2119307
  · exact B2119311
  · exact B2119315
  · exact B2119319
  · exact B2119323
  · exact B2119327
  · exact B2119331
  · exact B2119335
  · exact B2119339
  · exact B2119343
  · exact B2119347
  · exact B2119351
  · exact B2119355
  · exact B2119359
  · exact B2119363
  · exact B2119367
  · exact B2119371
  · exact B2119375
  · exact B2119379
  · exact B2119383
  · exact B2119387
  · exact B2119391
  · exact B2119395
  · exact B2119399
  · exact B2119403
  · exact B2119407
  · exact B2119411
  · exact B2119415
  · exact B2119419
  · exact B2119423
  · exact B2119427
  · exact B2119431
  · exact B2119435
theorem solution (m : ℕ) (hlo : 2117435 ≤ m) (hhi : m ≤ 2119435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 529358 ≤ j := by omega
    have hj2 : j ≤ 529858 := by omega
    have hb : Blo 2117435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
