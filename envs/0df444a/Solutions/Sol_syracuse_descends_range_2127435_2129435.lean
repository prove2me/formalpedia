-- Prove2me | solution 1 for syracuse_descends_range_2127435_2129435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:03.705807+00:00
-- url     : https://prove2.me/submissions/af787b13-f70f-4836-b7b3-9f636a500a1b

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

theorem B2393365 : Blo 2127435 2393365 := bbase (se 6 (by rfl) ⟨56094, by rfl⟩ : syracuseStep 2393365 = 112189) (by norm_num)
theorem B3191153 : Blo 2127435 3191153 := bstep (se 2 (by rfl) ⟨1196682, by rfl⟩ : syracuseStep 3191153 = 2393365) B2393365
theorem B2127435 : Blo 2127435 2127435 := bstep (se 1 (by rfl) ⟨1595576, by rfl⟩ : syracuseStep 2127435 = 3191153) B3191153
theorem B2692541 : Blo 2127435 2692541 := bbase (se 3 (by rfl) ⟨504851, by rfl⟩ : syracuseStep 2692541 = 1009703) (by norm_num)
theorem B7180109 : Blo 2127435 7180109 := bstep (se 3 (by rfl) ⟨1346270, by rfl⟩ : syracuseStep 7180109 = 2692541) B2692541
theorem B4786739 : Blo 2127435 4786739 := bstep (se 1 (by rfl) ⟨3590054, by rfl⟩ : syracuseStep 4786739 = 7180109) B7180109
theorem B3191159 : Blo 2127435 3191159 := bstep (se 1 (by rfl) ⟨2393369, by rfl⟩ : syracuseStep 3191159 = 4786739) B4786739
theorem B2127439 : Blo 2127435 2127439 := bstep (se 1 (by rfl) ⟨1595579, by rfl⟩ : syracuseStep 2127439 = 3191159) B3191159
theorem B3191165 : Blo 2127435 3191165 := bbase (se 3 (by rfl) ⟨598343, by rfl⟩ : syracuseStep 3191165 = 1196687) (by norm_num)
theorem B2127443 : Blo 2127435 2127443 := bstep (se 1 (by rfl) ⟨1595582, by rfl⟩ : syracuseStep 2127443 = 3191165) B3191165
theorem B4786757 : Blo 2127435 4786757 := bbase (se 4 (by rfl) ⟨448758, by rfl⟩ : syracuseStep 4786757 = 897517) (by norm_num)
theorem B3191171 : Blo 2127435 3191171 := bstep (se 1 (by rfl) ⟨2393378, by rfl⟩ : syracuseStep 3191171 = 4786757) B4786757
theorem B2127447 : Blo 2127435 2127447 := bstep (se 1 (by rfl) ⟨1595585, by rfl⟩ : syracuseStep 2127447 = 3191171) B3191171
theorem B2271845 : Blo 2127435 2271845 := bbase (se 4 (by rfl) ⟨212985, by rfl⟩ : syracuseStep 2271845 = 425971) (by norm_num)
theorem B6058253 : Blo 2127435 6058253 := bstep (se 3 (by rfl) ⟨1135922, by rfl⟩ : syracuseStep 6058253 = 2271845) B2271845
theorem B4038835 : Blo 2127435 4038835 := bstep (se 1 (by rfl) ⟨3029126, by rfl⟩ : syracuseStep 4038835 = 6058253) B6058253
theorem B5385113 : Blo 2127435 5385113 := bstep (se 2 (by rfl) ⟨2019417, by rfl⟩ : syracuseStep 5385113 = 4038835) B4038835
theorem B3590075 : Blo 2127435 3590075 := bstep (se 1 (by rfl) ⟨2692556, by rfl⟩ : syracuseStep 3590075 = 5385113) B5385113
theorem B2393383 : Blo 2127435 2393383 := bstep (se 1 (by rfl) ⟨1795037, by rfl⟩ : syracuseStep 2393383 = 3590075) B3590075
theorem B3191177 : Blo 2127435 3191177 := bstep (se 2 (by rfl) ⟨1196691, by rfl⟩ : syracuseStep 3191177 = 2393383) B2393383
theorem B2127451 : Blo 2127435 2127451 := bstep (se 1 (by rfl) ⟨1595588, by rfl⟩ : syracuseStep 2127451 = 3191177) B3191177
theorem B10770245 : Blo 2127435 10770245 := bbase (se 4 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 10770245 = 2019421) (by norm_num)
theorem B7180163 : Blo 2127435 7180163 := bstep (se 1 (by rfl) ⟨5385122, by rfl⟩ : syracuseStep 7180163 = 10770245) B10770245
theorem B4786775 : Blo 2127435 4786775 := bstep (se 1 (by rfl) ⟨3590081, by rfl⟩ : syracuseStep 4786775 = 7180163) B7180163
theorem B3191183 : Blo 2127435 3191183 := bstep (se 1 (by rfl) ⟨2393387, by rfl⟩ : syracuseStep 3191183 = 4786775) B4786775
theorem B2127455 : Blo 2127435 2127455 := bstep (se 1 (by rfl) ⟨1595591, by rfl⟩ : syracuseStep 2127455 = 3191183) B3191183
theorem B3191189 : Blo 2127435 3191189 := bbase (se 6 (by rfl) ⟨74793, by rfl⟩ : syracuseStep 3191189 = 149587) (by norm_num)
theorem B2127459 : Blo 2127435 2127459 := bstep (se 1 (by rfl) ⟨1595594, by rfl⟩ : syracuseStep 2127459 = 3191189) B3191189
theorem B6815573 : Blo 2127435 6815573 := bbase (se 9 (by rfl) ⟨19967, by rfl⟩ : syracuseStep 6815573 = 39935) (by norm_num)
theorem B4543715 : Blo 2127435 4543715 := bstep (se 1 (by rfl) ⟨3407786, by rfl⟩ : syracuseStep 4543715 = 6815573) B6815573
theorem B12116573 : Blo 2127435 12116573 := bstep (se 3 (by rfl) ⟨2271857, by rfl⟩ : syracuseStep 12116573 = 4543715) B4543715
theorem B8077715 : Blo 2127435 8077715 := bstep (se 1 (by rfl) ⟨6058286, by rfl⟩ : syracuseStep 8077715 = 12116573) B12116573
theorem B5385143 : Blo 2127435 5385143 := bstep (se 1 (by rfl) ⟨4038857, by rfl⟩ : syracuseStep 5385143 = 8077715) B8077715
theorem B3590095 : Blo 2127435 3590095 := bstep (se 1 (by rfl) ⟨2692571, by rfl⟩ : syracuseStep 3590095 = 5385143) B5385143
theorem B4786793 : Blo 2127435 4786793 := bstep (se 2 (by rfl) ⟨1795047, by rfl⟩ : syracuseStep 4786793 = 3590095) B3590095
theorem B3191195 : Blo 2127435 3191195 := bstep (se 1 (by rfl) ⟨2393396, by rfl⟩ : syracuseStep 3191195 = 4786793) B4786793
theorem B2127463 : Blo 2127435 2127463 := bstep (se 1 (by rfl) ⟨1595597, by rfl⟩ : syracuseStep 2127463 = 3191195) B3191195
theorem B2393401 : Blo 2127435 2393401 := bbase (se 2 (by rfl) ⟨897525, by rfl⟩ : syracuseStep 2393401 = 1795051) (by norm_num)
theorem B3191201 : Blo 2127435 3191201 := bstep (se 2 (by rfl) ⟨1196700, by rfl⟩ : syracuseStep 3191201 = 2393401) B2393401
theorem B2127467 : Blo 2127435 2127467 := bstep (se 1 (by rfl) ⟨1595600, by rfl⟩ : syracuseStep 2127467 = 3191201) B3191201
theorem B6058309 : Blo 2127435 6058309 := bbase (se 4 (by rfl) ⟨567966, by rfl⟩ : syracuseStep 6058309 = 1135933) (by norm_num)
theorem B8077745 : Blo 2127435 8077745 := bstep (se 2 (by rfl) ⟨3029154, by rfl⟩ : syracuseStep 8077745 = 6058309) B6058309
theorem B5385163 : Blo 2127435 5385163 := bstep (se 1 (by rfl) ⟨4038872, by rfl⟩ : syracuseStep 5385163 = 8077745) B8077745
theorem B7180217 : Blo 2127435 7180217 := bstep (se 2 (by rfl) ⟨2692581, by rfl⟩ : syracuseStep 7180217 = 5385163) B5385163
theorem B4786811 : Blo 2127435 4786811 := bstep (se 1 (by rfl) ⟨3590108, by rfl⟩ : syracuseStep 4786811 = 7180217) B7180217
theorem B3191207 : Blo 2127435 3191207 := bstep (se 1 (by rfl) ⟨2393405, by rfl⟩ : syracuseStep 3191207 = 4786811) B4786811
theorem B2127471 : Blo 2127435 2127471 := bstep (se 1 (by rfl) ⟨1595603, by rfl⟩ : syracuseStep 2127471 = 3191207) B3191207
theorem B3191213 : Blo 2127435 3191213 := bbase (se 3 (by rfl) ⟨598352, by rfl⟩ : syracuseStep 3191213 = 1196705) (by norm_num)
theorem B2127475 : Blo 2127435 2127475 := bstep (se 1 (by rfl) ⟨1595606, by rfl⟩ : syracuseStep 2127475 = 3191213) B3191213
theorem B4786829 : Blo 2127435 4786829 := bbase (se 3 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 4786829 = 1795061) (by norm_num)
theorem B3191219 : Blo 2127435 3191219 := bstep (se 1 (by rfl) ⟨2393414, by rfl⟩ : syracuseStep 3191219 = 4786829) B4786829
theorem B2127479 : Blo 2127435 2127479 := bstep (se 1 (by rfl) ⟨1595609, by rfl⟩ : syracuseStep 2127479 = 3191219) B3191219
theorem B2692597 : Blo 2127435 2692597 := bbase (se 5 (by rfl) ⟨126215, by rfl⟩ : syracuseStep 2692597 = 252431) (by norm_num)
theorem B3590129 : Blo 2127435 3590129 := bstep (se 2 (by rfl) ⟨1346298, by rfl⟩ : syracuseStep 3590129 = 2692597) B2692597
theorem B2393419 : Blo 2127435 2393419 := bstep (se 1 (by rfl) ⟨1795064, by rfl⟩ : syracuseStep 2393419 = 3590129) B3590129
theorem B3191225 : Blo 2127435 3191225 := bstep (se 2 (by rfl) ⟨1196709, by rfl⟩ : syracuseStep 3191225 = 2393419) B2393419
theorem B2127483 : Blo 2127435 2127483 := bstep (se 1 (by rfl) ⟨1595612, by rfl⟩ : syracuseStep 2127483 = 3191225) B3191225
theorem B7667605 : Blo 2127435 7667605 := bbase (se 6 (by rfl) ⟨179709, by rfl⟩ : syracuseStep 7667605 = 359419) (by norm_num)
theorem B40893893 : Blo 2127435 40893893 := bstep (se 4 (by rfl) ⟨3833802, by rfl⟩ : syracuseStep 40893893 = 7667605) B7667605
theorem B27262595 : Blo 2127435 27262595 := bstep (se 1 (by rfl) ⟨20446946, by rfl⟩ : syracuseStep 27262595 = 40893893) B40893893
theorem B18175063 : Blo 2127435 18175063 := bstep (se 1 (by rfl) ⟨13631297, by rfl⟩ : syracuseStep 18175063 = 27262595) B27262595
theorem B24233417 : Blo 2127435 24233417 := bstep (se 2 (by rfl) ⟨9087531, by rfl⟩ : syracuseStep 24233417 = 18175063) B18175063
theorem B16155611 : Blo 2127435 16155611 := bstep (se 1 (by rfl) ⟨12116708, by rfl⟩ : syracuseStep 16155611 = 24233417) B24233417
theorem B10770407 : Blo 2127435 10770407 := bstep (se 1 (by rfl) ⟨8077805, by rfl⟩ : syracuseStep 10770407 = 16155611) B16155611
theorem B7180271 : Blo 2127435 7180271 := bstep (se 1 (by rfl) ⟨5385203, by rfl⟩ : syracuseStep 7180271 = 10770407) B10770407
theorem B4786847 : Blo 2127435 4786847 := bstep (se 1 (by rfl) ⟨3590135, by rfl⟩ : syracuseStep 4786847 = 7180271) B7180271
theorem B3191231 : Blo 2127435 3191231 := bstep (se 1 (by rfl) ⟨2393423, by rfl⟩ : syracuseStep 3191231 = 4786847) B4786847
theorem B2127487 : Blo 2127435 2127487 := bstep (se 1 (by rfl) ⟨1595615, by rfl⟩ : syracuseStep 2127487 = 3191231) B3191231
theorem B3191237 : Blo 2127435 3191237 := bbase (se 4 (by rfl) ⟨299178, by rfl⟩ : syracuseStep 3191237 = 598357) (by norm_num)
theorem B2127491 : Blo 2127435 2127491 := bstep (se 1 (by rfl) ⟨1595618, by rfl⟩ : syracuseStep 2127491 = 3191237) B3191237
theorem B3590149 : Blo 2127435 3590149 := bbase (se 4 (by rfl) ⟨336576, by rfl⟩ : syracuseStep 3590149 = 673153) (by norm_num)
theorem B4786865 : Blo 2127435 4786865 := bstep (se 2 (by rfl) ⟨1795074, by rfl⟩ : syracuseStep 4786865 = 3590149) B3590149
theorem B3191243 : Blo 2127435 3191243 := bstep (se 1 (by rfl) ⟨2393432, by rfl⟩ : syracuseStep 3191243 = 4786865) B4786865
theorem B2127495 : Blo 2127435 2127495 := bstep (se 1 (by rfl) ⟨1595621, by rfl⟩ : syracuseStep 2127495 = 3191243) B3191243
theorem B2393437 : Blo 2127435 2393437 := bbase (se 3 (by rfl) ⟨448769, by rfl⟩ : syracuseStep 2393437 = 897539) (by norm_num)
theorem B3191249 : Blo 2127435 3191249 := bstep (se 2 (by rfl) ⟨1196718, by rfl⟩ : syracuseStep 3191249 = 2393437) B2393437
theorem B2127499 : Blo 2127435 2127499 := bstep (se 1 (by rfl) ⟨1595624, by rfl⟩ : syracuseStep 2127499 = 3191249) B3191249
theorem B7180325 : Blo 2127435 7180325 := bbase (se 4 (by rfl) ⟨673155, by rfl⟩ : syracuseStep 7180325 = 1346311) (by norm_num)
theorem B4786883 : Blo 2127435 4786883 := bstep (se 1 (by rfl) ⟨3590162, by rfl⟩ : syracuseStep 4786883 = 7180325) B7180325
theorem B3191255 : Blo 2127435 3191255 := bstep (se 1 (by rfl) ⟨2393441, by rfl⟩ : syracuseStep 3191255 = 4786883) B4786883
theorem B2127503 : Blo 2127435 2127503 := bstep (se 1 (by rfl) ⟨1595627, by rfl⟩ : syracuseStep 2127503 = 3191255) B3191255
theorem B3191261 : Blo 2127435 3191261 := bbase (se 3 (by rfl) ⟨598361, by rfl⟩ : syracuseStep 3191261 = 1196723) (by norm_num)
theorem B2127507 : Blo 2127435 2127507 := bstep (se 1 (by rfl) ⟨1595630, by rfl⟩ : syracuseStep 2127507 = 3191261) B3191261
theorem B4786901 : Blo 2127435 4786901 := bbase (se 7 (by rfl) ⟨56096, by rfl⟩ : syracuseStep 4786901 = 112193) (by norm_num)
theorem B3191267 : Blo 2127435 3191267 := bstep (se 1 (by rfl) ⟨2393450, by rfl⟩ : syracuseStep 3191267 = 4786901) B4786901
theorem B2127511 : Blo 2127435 2127511 := bstep (se 1 (by rfl) ⟨1595633, by rfl⟩ : syracuseStep 2127511 = 3191267) B3191267
theorem B9087653 : Blo 2127435 9087653 := bbase (se 4 (by rfl) ⟨851967, by rfl⟩ : syracuseStep 9087653 = 1703935) (by norm_num)
theorem B6058435 : Blo 2127435 6058435 := bstep (se 1 (by rfl) ⟨4543826, by rfl⟩ : syracuseStep 6058435 = 9087653) B9087653
theorem B8077913 : Blo 2127435 8077913 := bstep (se 2 (by rfl) ⟨3029217, by rfl⟩ : syracuseStep 8077913 = 6058435) B6058435
theorem B5385275 : Blo 2127435 5385275 := bstep (se 1 (by rfl) ⟨4038956, by rfl⟩ : syracuseStep 5385275 = 8077913) B8077913
theorem B3590183 : Blo 2127435 3590183 := bstep (se 1 (by rfl) ⟨2692637, by rfl⟩ : syracuseStep 3590183 = 5385275) B5385275
theorem B2393455 : Blo 2127435 2393455 := bstep (se 1 (by rfl) ⟨1795091, by rfl⟩ : syracuseStep 2393455 = 3590183) B3590183
theorem B3191273 : Blo 2127435 3191273 := bstep (se 2 (by rfl) ⟨1196727, by rfl⟩ : syracuseStep 3191273 = 2393455) B2393455
theorem B2127515 : Blo 2127435 2127515 := bstep (se 1 (by rfl) ⟨1595636, by rfl⟩ : syracuseStep 2127515 = 3191273) B3191273
theorem B4313093 : Blo 2127435 4313093 := bbase (se 4 (by rfl) ⟨404352, by rfl⟩ : syracuseStep 4313093 = 808705) (by norm_num)
theorem B46006325 : Blo 2127435 46006325 := bstep (se 5 (by rfl) ⟨2156546, by rfl⟩ : syracuseStep 46006325 = 4313093) B4313093
theorem B30670883 : Blo 2127435 30670883 := bstep (se 1 (by rfl) ⟨23003162, by rfl⟩ : syracuseStep 30670883 = 46006325) B46006325
theorem B20447255 : Blo 2127435 20447255 := bstep (se 1 (by rfl) ⟨15335441, by rfl⟩ : syracuseStep 20447255 = 30670883) B30670883
theorem B13631503 : Blo 2127435 13631503 := bstep (se 1 (by rfl) ⟨10223627, by rfl⟩ : syracuseStep 13631503 = 20447255) B20447255
theorem B18175337 : Blo 2127435 18175337 := bstep (se 2 (by rfl) ⟨6815751, by rfl⟩ : syracuseStep 18175337 = 13631503) B13631503
theorem B12116891 : Blo 2127435 12116891 := bstep (se 1 (by rfl) ⟨9087668, by rfl⟩ : syracuseStep 12116891 = 18175337) B18175337
theorem B8077927 : Blo 2127435 8077927 := bstep (se 1 (by rfl) ⟨6058445, by rfl⟩ : syracuseStep 8077927 = 12116891) B12116891
theorem B10770569 : Blo 2127435 10770569 := bstep (se 2 (by rfl) ⟨4038963, by rfl⟩ : syracuseStep 10770569 = 8077927) B8077927
theorem B7180379 : Blo 2127435 7180379 := bstep (se 1 (by rfl) ⟨5385284, by rfl⟩ : syracuseStep 7180379 = 10770569) B10770569
theorem B4786919 : Blo 2127435 4786919 := bstep (se 1 (by rfl) ⟨3590189, by rfl⟩ : syracuseStep 4786919 = 7180379) B7180379
theorem B3191279 : Blo 2127435 3191279 := bstep (se 1 (by rfl) ⟨2393459, by rfl⟩ : syracuseStep 3191279 = 4786919) B4786919
theorem B2127519 : Blo 2127435 2127519 := bstep (se 1 (by rfl) ⟨1595639, by rfl⟩ : syracuseStep 2127519 = 3191279) B3191279
theorem B3191285 : Blo 2127435 3191285 := bbase (se 5 (by rfl) ⟨149591, by rfl⟩ : syracuseStep 3191285 = 299183) (by norm_num)
theorem B2127523 : Blo 2127435 2127523 := bstep (se 1 (by rfl) ⟨1595642, by rfl⟩ : syracuseStep 2127523 = 3191285) B3191285
theorem B6058469 : Blo 2127435 6058469 := bbase (se 4 (by rfl) ⟨567981, by rfl⟩ : syracuseStep 6058469 = 1135963) (by norm_num)
theorem B4038979 : Blo 2127435 4038979 := bstep (se 1 (by rfl) ⟨3029234, by rfl⟩ : syracuseStep 4038979 = 6058469) B6058469
theorem B5385305 : Blo 2127435 5385305 := bstep (se 2 (by rfl) ⟨2019489, by rfl⟩ : syracuseStep 5385305 = 4038979) B4038979
theorem B3590203 : Blo 2127435 3590203 := bstep (se 1 (by rfl) ⟨2692652, by rfl⟩ : syracuseStep 3590203 = 5385305) B5385305
theorem B4786937 : Blo 2127435 4786937 := bstep (se 2 (by rfl) ⟨1795101, by rfl⟩ : syracuseStep 4786937 = 3590203) B3590203
theorem B3191291 : Blo 2127435 3191291 := bstep (se 1 (by rfl) ⟨2393468, by rfl⟩ : syracuseStep 3191291 = 4786937) B4786937
theorem B2127527 : Blo 2127435 2127527 := bstep (se 1 (by rfl) ⟨1595645, by rfl⟩ : syracuseStep 2127527 = 3191291) B3191291
theorem B2393473 : Blo 2127435 2393473 := bbase (se 2 (by rfl) ⟨897552, by rfl⟩ : syracuseStep 2393473 = 1795105) (by norm_num)
theorem B3191297 : Blo 2127435 3191297 := bstep (se 2 (by rfl) ⟨1196736, by rfl⟩ : syracuseStep 3191297 = 2393473) B2393473
theorem B2127531 : Blo 2127435 2127531 := bstep (se 1 (by rfl) ⟨1595648, by rfl⟩ : syracuseStep 2127531 = 3191297) B3191297
theorem B5385325 : Blo 2127435 5385325 := bbase (se 3 (by rfl) ⟨1009748, by rfl⟩ : syracuseStep 5385325 = 2019497) (by norm_num)
theorem B7180433 : Blo 2127435 7180433 := bstep (se 2 (by rfl) ⟨2692662, by rfl⟩ : syracuseStep 7180433 = 5385325) B5385325
theorem B4786955 : Blo 2127435 4786955 := bstep (se 1 (by rfl) ⟨3590216, by rfl⟩ : syracuseStep 4786955 = 7180433) B7180433
theorem B3191303 : Blo 2127435 3191303 := bstep (se 1 (by rfl) ⟨2393477, by rfl⟩ : syracuseStep 3191303 = 4786955) B4786955
theorem B2127535 : Blo 2127435 2127535 := bstep (se 1 (by rfl) ⟨1595651, by rfl⟩ : syracuseStep 2127535 = 3191303) B3191303
theorem B3191309 : Blo 2127435 3191309 := bbase (se 3 (by rfl) ⟨598370, by rfl⟩ : syracuseStep 3191309 = 1196741) (by norm_num)
theorem B2127539 : Blo 2127435 2127539 := bstep (se 1 (by rfl) ⟨1595654, by rfl⟩ : syracuseStep 2127539 = 3191309) B3191309
theorem B4786973 : Blo 2127435 4786973 := bbase (se 3 (by rfl) ⟨897557, by rfl⟩ : syracuseStep 4786973 = 1795115) (by norm_num)
theorem B3191315 : Blo 2127435 3191315 := bstep (se 1 (by rfl) ⟨2393486, by rfl⟩ : syracuseStep 3191315 = 4786973) B4786973
theorem B2127543 : Blo 2127435 2127543 := bstep (se 1 (by rfl) ⟨1595657, by rfl⟩ : syracuseStep 2127543 = 3191315) B3191315
theorem B3590237 : Blo 2127435 3590237 := bbase (se 3 (by rfl) ⟨673169, by rfl⟩ : syracuseStep 3590237 = 1346339) (by norm_num)
theorem B2393491 : Blo 2127435 2393491 := bstep (se 1 (by rfl) ⟨1795118, by rfl⟩ : syracuseStep 2393491 = 3590237) B3590237
theorem B3191321 : Blo 2127435 3191321 := bstep (se 2 (by rfl) ⟨1196745, by rfl⟩ : syracuseStep 3191321 = 2393491) B2393491
theorem B2127547 : Blo 2127435 2127547 := bstep (se 1 (by rfl) ⟨1595660, by rfl⟩ : syracuseStep 2127547 = 3191321) B3191321
theorem B20726549 : Blo 2127435 20726549 := bbase (se 6 (by rfl) ⟨485778, by rfl⟩ : syracuseStep 20726549 = 971557) (by norm_num)
theorem B13817699 : Blo 2127435 13817699 := bstep (se 1 (by rfl) ⟨10363274, by rfl⟩ : syracuseStep 13817699 = 20726549) B20726549
theorem B9211799 : Blo 2127435 9211799 := bstep (se 1 (by rfl) ⟨6908849, by rfl⟩ : syracuseStep 9211799 = 13817699) B13817699
theorem B6141199 : Blo 2127435 6141199 := bstep (se 1 (by rfl) ⟨4605899, by rfl⟩ : syracuseStep 6141199 = 9211799) B9211799
theorem B8188265 : Blo 2127435 8188265 := bstep (se 2 (by rfl) ⟨3070599, by rfl⟩ : syracuseStep 8188265 = 6141199) B6141199
theorem B5458843 : Blo 2127435 5458843 := bstep (se 1 (by rfl) ⟨4094132, by rfl⟩ : syracuseStep 5458843 = 8188265) B8188265
theorem B7278457 : Blo 2127435 7278457 := bstep (se 2 (by rfl) ⟨2729421, by rfl⟩ : syracuseStep 7278457 = 5458843) B5458843
theorem B9704609 : Blo 2127435 9704609 := bstep (se 2 (by rfl) ⟨3639228, by rfl⟩ : syracuseStep 9704609 = 7278457) B7278457
theorem B6469739 : Blo 2127435 6469739 := bstep (se 1 (by rfl) ⟨4852304, by rfl⟩ : syracuseStep 6469739 = 9704609) B9704609
theorem B4313159 : Blo 2127435 4313159 := bstep (se 1 (by rfl) ⟨3234869, by rfl⟩ : syracuseStep 4313159 = 6469739) B6469739
theorem B2875439 : Blo 2127435 2875439 := bstep (se 1 (by rfl) ⟨2156579, by rfl⟩ : syracuseStep 2875439 = 4313159) B4313159
theorem B7667837 : Blo 2127435 7667837 := bstep (se 3 (by rfl) ⟨1437719, by rfl⟩ : syracuseStep 7667837 = 2875439) B2875439
theorem B5111891 : Blo 2127435 5111891 := bstep (se 1 (by rfl) ⟨3833918, by rfl⟩ : syracuseStep 5111891 = 7667837) B7667837
theorem B3407927 : Blo 2127435 3407927 := bstep (se 1 (by rfl) ⟨2555945, by rfl⟩ : syracuseStep 3407927 = 5111891) B5111891
theorem B9087805 : Blo 2127435 9087805 := bstep (se 3 (by rfl) ⟨1703963, by rfl⟩ : syracuseStep 9087805 = 3407927) B3407927
theorem B12117073 : Blo 2127435 12117073 := bstep (se 2 (by rfl) ⟨4543902, by rfl⟩ : syracuseStep 12117073 = 9087805) B9087805
theorem B16156097 : Blo 2127435 16156097 := bstep (se 2 (by rfl) ⟨6058536, by rfl⟩ : syracuseStep 16156097 = 12117073) B12117073
theorem B10770731 : Blo 2127435 10770731 := bstep (se 1 (by rfl) ⟨8078048, by rfl⟩ : syracuseStep 10770731 = 16156097) B16156097
theorem B7180487 : Blo 2127435 7180487 := bstep (se 1 (by rfl) ⟨5385365, by rfl⟩ : syracuseStep 7180487 = 10770731) B10770731
theorem B4786991 : Blo 2127435 4786991 := bstep (se 1 (by rfl) ⟨3590243, by rfl⟩ : syracuseStep 4786991 = 7180487) B7180487
theorem B3191327 : Blo 2127435 3191327 := bstep (se 1 (by rfl) ⟨2393495, by rfl⟩ : syracuseStep 3191327 = 4786991) B4786991
theorem B2127551 : Blo 2127435 2127551 := bstep (se 1 (by rfl) ⟨1595663, by rfl⟩ : syracuseStep 2127551 = 3191327) B3191327
theorem B3191333 : Blo 2127435 3191333 := bbase (se 4 (by rfl) ⟨299187, by rfl⟩ : syracuseStep 3191333 = 598375) (by norm_num)
theorem B2127555 : Blo 2127435 2127555 := bstep (se 1 (by rfl) ⟨1595666, by rfl⟩ : syracuseStep 2127555 = 3191333) B3191333
theorem B2692693 : Blo 2127435 2692693 := bbase (se 8 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 2692693 = 31555) (by norm_num)
theorem B3590257 : Blo 2127435 3590257 := bstep (se 2 (by rfl) ⟨1346346, by rfl⟩ : syracuseStep 3590257 = 2692693) B2692693
theorem B4787009 : Blo 2127435 4787009 := bstep (se 2 (by rfl) ⟨1795128, by rfl⟩ : syracuseStep 4787009 = 3590257) B3590257
theorem B3191339 : Blo 2127435 3191339 := bstep (se 1 (by rfl) ⟨2393504, by rfl⟩ : syracuseStep 3191339 = 4787009) B4787009
theorem B2127559 : Blo 2127435 2127559 := bstep (se 1 (by rfl) ⟨1595669, by rfl⟩ : syracuseStep 2127559 = 3191339) B3191339
theorem B2393509 : Blo 2127435 2393509 := bbase (se 4 (by rfl) ⟨224391, by rfl⟩ : syracuseStep 2393509 = 448783) (by norm_num)
theorem B3191345 : Blo 2127435 3191345 := bstep (se 2 (by rfl) ⟨1196754, by rfl⟩ : syracuseStep 3191345 = 2393509) B2393509
theorem B2127563 : Blo 2127435 2127563 := bstep (se 1 (by rfl) ⟨1595672, by rfl⟩ : syracuseStep 2127563 = 3191345) B3191345
theorem B2555965 : Blo 2127435 2555965 := bbase (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) (by norm_num)
theorem B13631813 : Blo 2127435 13631813 := bstep (se 4 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 13631813 = 2555965) B2555965
theorem B9087875 : Blo 2127435 9087875 := bstep (se 1 (by rfl) ⟨6815906, by rfl⟩ : syracuseStep 9087875 = 13631813) B13631813
theorem B6058583 : Blo 2127435 6058583 := bstep (se 1 (by rfl) ⟨4543937, by rfl⟩ : syracuseStep 6058583 = 9087875) B9087875
theorem B4039055 : Blo 2127435 4039055 := bstep (se 1 (by rfl) ⟨3029291, by rfl⟩ : syracuseStep 4039055 = 6058583) B6058583
theorem B2692703 : Blo 2127435 2692703 := bstep (se 1 (by rfl) ⟨2019527, by rfl⟩ : syracuseStep 2692703 = 4039055) B4039055
theorem B7180541 : Blo 2127435 7180541 := bstep (se 3 (by rfl) ⟨1346351, by rfl⟩ : syracuseStep 7180541 = 2692703) B2692703
theorem B4787027 : Blo 2127435 4787027 := bstep (se 1 (by rfl) ⟨3590270, by rfl⟩ : syracuseStep 4787027 = 7180541) B7180541
theorem B3191351 : Blo 2127435 3191351 := bstep (se 1 (by rfl) ⟨2393513, by rfl⟩ : syracuseStep 3191351 = 4787027) B4787027
theorem B2127567 : Blo 2127435 2127567 := bstep (se 1 (by rfl) ⟨1595675, by rfl⟩ : syracuseStep 2127567 = 3191351) B3191351
theorem B3191357 : Blo 2127435 3191357 := bbase (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) (by norm_num)
theorem B2127571 : Blo 2127435 2127571 := bstep (se 1 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 2127571 = 3191357) B3191357
theorem B4787045 : Blo 2127435 4787045 := bbase (se 4 (by rfl) ⟨448785, by rfl⟩ : syracuseStep 4787045 = 897571) (by norm_num)
theorem B3191363 : Blo 2127435 3191363 := bstep (se 1 (by rfl) ⟨2393522, by rfl⟩ : syracuseStep 3191363 = 4787045) B4787045
theorem B2127575 : Blo 2127435 2127575 := bstep (se 1 (by rfl) ⟨1595681, by rfl⟩ : syracuseStep 2127575 = 3191363) B3191363
theorem B5385437 : Blo 2127435 5385437 := bbase (se 3 (by rfl) ⟨1009769, by rfl⟩ : syracuseStep 5385437 = 2019539) (by norm_num)
theorem B3590291 : Blo 2127435 3590291 := bstep (se 1 (by rfl) ⟨2692718, by rfl⟩ : syracuseStep 3590291 = 5385437) B5385437
theorem B2393527 : Blo 2127435 2393527 := bstep (se 1 (by rfl) ⟨1795145, by rfl⟩ : syracuseStep 2393527 = 3590291) B3590291
theorem B3191369 : Blo 2127435 3191369 := bstep (se 2 (by rfl) ⟨1196763, by rfl⟩ : syracuseStep 3191369 = 2393527) B2393527
theorem B2127579 : Blo 2127435 2127579 := bstep (se 1 (by rfl) ⟨1595684, by rfl⟩ : syracuseStep 2127579 = 3191369) B3191369
theorem B4039085 : Blo 2127435 4039085 := bbase (se 3 (by rfl) ⟨757328, by rfl⟩ : syracuseStep 4039085 = 1514657) (by norm_num)
theorem B10770893 : Blo 2127435 10770893 := bstep (se 3 (by rfl) ⟨2019542, by rfl⟩ : syracuseStep 10770893 = 4039085) B4039085
theorem B7180595 : Blo 2127435 7180595 := bstep (se 1 (by rfl) ⟨5385446, by rfl⟩ : syracuseStep 7180595 = 10770893) B10770893
theorem B4787063 : Blo 2127435 4787063 := bstep (se 1 (by rfl) ⟨3590297, by rfl⟩ : syracuseStep 4787063 = 7180595) B7180595
theorem B3191375 : Blo 2127435 3191375 := bstep (se 1 (by rfl) ⟨2393531, by rfl⟩ : syracuseStep 3191375 = 4787063) B4787063
theorem B2127583 : Blo 2127435 2127583 := bstep (se 1 (by rfl) ⟨1595687, by rfl⟩ : syracuseStep 2127583 = 3191375) B3191375
theorem B3191381 : Blo 2127435 3191381 := bbase (se 8 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 3191381 = 37399) (by norm_num)
theorem B2127587 : Blo 2127435 2127587 := bstep (se 1 (by rfl) ⟨1595690, by rfl⟩ : syracuseStep 2127587 = 3191381) B3191381
theorem B5181733 : Blo 2127435 5181733 := bbase (se 4 (by rfl) ⟨485787, by rfl⟩ : syracuseStep 5181733 = 971575) (by norm_num)
theorem B6908977 : Blo 2127435 6908977 := bstep (se 2 (by rfl) ⟨2590866, by rfl⟩ : syracuseStep 6908977 = 5181733) B5181733
theorem B9211969 : Blo 2127435 9211969 := bstep (se 2 (by rfl) ⟨3454488, by rfl⟩ : syracuseStep 9211969 = 6908977) B6908977
theorem B12282625 : Blo 2127435 12282625 := bstep (se 2 (by rfl) ⟨4605984, by rfl⟩ : syracuseStep 12282625 = 9211969) B9211969
theorem B16376833 : Blo 2127435 16376833 := bstep (se 2 (by rfl) ⟨6141312, by rfl⟩ : syracuseStep 16376833 = 12282625) B12282625
theorem B87343109 : Blo 2127435 87343109 := bstep (se 4 (by rfl) ⟨8188416, by rfl⟩ : syracuseStep 87343109 = 16376833) B16376833
theorem B58228739 : Blo 2127435 58228739 := bstep (se 1 (by rfl) ⟨43671554, by rfl⟩ : syracuseStep 58228739 = 87343109) B87343109
theorem B38819159 : Blo 2127435 38819159 := bstep (se 1 (by rfl) ⟨29114369, by rfl⟩ : syracuseStep 38819159 = 58228739) B58228739
theorem B25879439 : Blo 2127435 25879439 := bstep (se 1 (by rfl) ⟨19409579, by rfl⟩ : syracuseStep 25879439 = 38819159) B38819159
theorem B17252959 : Blo 2127435 17252959 := bstep (se 1 (by rfl) ⟨12939719, by rfl⟩ : syracuseStep 17252959 = 25879439) B25879439
theorem B23003945 : Blo 2127435 23003945 := bstep (se 2 (by rfl) ⟨8626479, by rfl⟩ : syracuseStep 23003945 = 17252959) B17252959
theorem B15335963 : Blo 2127435 15335963 := bstep (se 1 (by rfl) ⟨11501972, by rfl⟩ : syracuseStep 15335963 = 23003945) B23003945
theorem B10223975 : Blo 2127435 10223975 := bstep (se 1 (by rfl) ⟨7667981, by rfl⟩ : syracuseStep 10223975 = 15335963) B15335963
theorem B6815983 : Blo 2127435 6815983 := bstep (se 1 (by rfl) ⟨5111987, by rfl⟩ : syracuseStep 6815983 = 10223975) B10223975
theorem B9087977 : Blo 2127435 9087977 := bstep (se 2 (by rfl) ⟨3407991, by rfl⟩ : syracuseStep 9087977 = 6815983) B6815983
theorem B6058651 : Blo 2127435 6058651 := bstep (se 1 (by rfl) ⟨4543988, by rfl⟩ : syracuseStep 6058651 = 9087977) B9087977
theorem B8078201 : Blo 2127435 8078201 := bstep (se 2 (by rfl) ⟨3029325, by rfl⟩ : syracuseStep 8078201 = 6058651) B6058651
theorem B5385467 : Blo 2127435 5385467 := bstep (se 1 (by rfl) ⟨4039100, by rfl⟩ : syracuseStep 5385467 = 8078201) B8078201
theorem B3590311 : Blo 2127435 3590311 := bstep (se 1 (by rfl) ⟨2692733, by rfl⟩ : syracuseStep 3590311 = 5385467) B5385467
theorem B4787081 : Blo 2127435 4787081 := bstep (se 2 (by rfl) ⟨1795155, by rfl⟩ : syracuseStep 4787081 = 3590311) B3590311
theorem B3191387 : Blo 2127435 3191387 := bstep (se 1 (by rfl) ⟨2393540, by rfl⟩ : syracuseStep 3191387 = 4787081) B4787081
theorem B2127591 : Blo 2127435 2127591 := bstep (se 1 (by rfl) ⟨1595693, by rfl⟩ : syracuseStep 2127591 = 3191387) B3191387
theorem B2393545 : Blo 2127435 2393545 := bbase (se 2 (by rfl) ⟨897579, by rfl⟩ : syracuseStep 2393545 = 1795159) (by norm_num)
theorem B3191393 : Blo 2127435 3191393 := bstep (se 2 (by rfl) ⟨1196772, by rfl⟩ : syracuseStep 3191393 = 2393545) B2393545
theorem B2127595 : Blo 2127435 2127595 := bstep (se 1 (by rfl) ⟨1595696, by rfl⟩ : syracuseStep 2127595 = 3191393) B3191393
theorem B18176021 : Blo 2127435 18176021 := bbase (se 6 (by rfl) ⟨426000, by rfl⟩ : syracuseStep 18176021 = 852001) (by norm_num)
theorem B12117347 : Blo 2127435 12117347 := bstep (se 1 (by rfl) ⟨9088010, by rfl⟩ : syracuseStep 12117347 = 18176021) B18176021
theorem B8078231 : Blo 2127435 8078231 := bstep (se 1 (by rfl) ⟨6058673, by rfl⟩ : syracuseStep 8078231 = 12117347) B12117347
theorem B5385487 : Blo 2127435 5385487 := bstep (se 1 (by rfl) ⟨4039115, by rfl⟩ : syracuseStep 5385487 = 8078231) B8078231
theorem B7180649 : Blo 2127435 7180649 := bstep (se 2 (by rfl) ⟨2692743, by rfl⟩ : syracuseStep 7180649 = 5385487) B5385487
theorem B4787099 : Blo 2127435 4787099 := bstep (se 1 (by rfl) ⟨3590324, by rfl⟩ : syracuseStep 4787099 = 7180649) B7180649
theorem B3191399 : Blo 2127435 3191399 := bstep (se 1 (by rfl) ⟨2393549, by rfl⟩ : syracuseStep 3191399 = 4787099) B4787099
theorem B2127599 : Blo 2127435 2127599 := bstep (se 1 (by rfl) ⟨1595699, by rfl⟩ : syracuseStep 2127599 = 3191399) B3191399
theorem B3191405 : Blo 2127435 3191405 := bbase (se 3 (by rfl) ⟨598388, by rfl⟩ : syracuseStep 3191405 = 1196777) (by norm_num)
theorem B2127603 : Blo 2127435 2127603 := bstep (se 1 (by rfl) ⟨1595702, by rfl⟩ : syracuseStep 2127603 = 3191405) B3191405
theorem B4787117 : Blo 2127435 4787117 := bbase (se 3 (by rfl) ⟨897584, by rfl⟩ : syracuseStep 4787117 = 1795169) (by norm_num)
theorem B3191411 : Blo 2127435 3191411 := bstep (se 1 (by rfl) ⟨2393558, by rfl⟩ : syracuseStep 3191411 = 4787117) B4787117
theorem B2127607 : Blo 2127435 2127607 := bstep (se 1 (by rfl) ⟨1595705, by rfl⟩ : syracuseStep 2127607 = 3191411) B3191411
theorem B6058709 : Blo 2127435 6058709 := bbase (se 7 (by rfl) ⟨71000, by rfl⟩ : syracuseStep 6058709 = 142001) (by norm_num)
theorem B4039139 : Blo 2127435 4039139 := bstep (se 1 (by rfl) ⟨3029354, by rfl⟩ : syracuseStep 4039139 = 6058709) B6058709
theorem B2692759 : Blo 2127435 2692759 := bstep (se 1 (by rfl) ⟨2019569, by rfl⟩ : syracuseStep 2692759 = 4039139) B4039139
theorem B3590345 : Blo 2127435 3590345 := bstep (se 2 (by rfl) ⟨1346379, by rfl⟩ : syracuseStep 3590345 = 2692759) B2692759
theorem B2393563 : Blo 2127435 2393563 := bstep (se 1 (by rfl) ⟨1795172, by rfl⟩ : syracuseStep 2393563 = 3590345) B3590345
theorem B3191417 : Blo 2127435 3191417 := bstep (se 2 (by rfl) ⟨1196781, by rfl⟩ : syracuseStep 3191417 = 2393563) B2393563
theorem B2127611 : Blo 2127435 2127611 := bstep (se 1 (by rfl) ⟨1595708, by rfl⟩ : syracuseStep 2127611 = 3191417) B3191417
theorem B35454293 : Blo 2127435 35454293 := bbase (se 11 (by rfl) ⟨25967, by rfl⟩ : syracuseStep 35454293 = 51935) (by norm_num)
theorem B23636195 : Blo 2127435 23636195 := bstep (se 1 (by rfl) ⟨17727146, by rfl⟩ : syracuseStep 23636195 = 35454293) B35454293
theorem B15757463 : Blo 2127435 15757463 := bstep (se 1 (by rfl) ⟨11818097, by rfl⟩ : syracuseStep 15757463 = 23636195) B23636195
theorem B10504975 : Blo 2127435 10504975 := bstep (se 1 (by rfl) ⟨7878731, by rfl⟩ : syracuseStep 10504975 = 15757463) B15757463
theorem B14006633 : Blo 2127435 14006633 := bstep (se 2 (by rfl) ⟨5252487, by rfl⟩ : syracuseStep 14006633 = 10504975) B10504975
theorem B149404085 : Blo 2127435 149404085 := bstep (se 5 (by rfl) ⟨7003316, by rfl⟩ : syracuseStep 149404085 = 14006633) B14006633
theorem B99602723 : Blo 2127435 99602723 := bstep (se 1 (by rfl) ⟨74702042, by rfl⟩ : syracuseStep 99602723 = 149404085) B149404085
theorem B66401815 : Blo 2127435 66401815 := bstep (se 1 (by rfl) ⟨49801361, by rfl⟩ : syracuseStep 66401815 = 99602723) B99602723
theorem B88535753 : Blo 2127435 88535753 := bstep (se 2 (by rfl) ⟨33200907, by rfl⟩ : syracuseStep 88535753 = 66401815) B66401815
theorem B59023835 : Blo 2127435 59023835 := bstep (se 1 (by rfl) ⟨44267876, by rfl⟩ : syracuseStep 59023835 = 88535753) B88535753
theorem B39349223 : Blo 2127435 39349223 := bstep (se 1 (by rfl) ⟨29511917, by rfl⟩ : syracuseStep 39349223 = 59023835) B59023835
theorem B26232815 : Blo 2127435 26232815 := bstep (se 1 (by rfl) ⟨19674611, by rfl⟩ : syracuseStep 26232815 = 39349223) B39349223
theorem B17488543 : Blo 2127435 17488543 := bstep (se 1 (by rfl) ⟨13116407, by rfl⟩ : syracuseStep 17488543 = 26232815) B26232815
theorem B23318057 : Blo 2127435 23318057 := bstep (se 2 (by rfl) ⟨8744271, by rfl⟩ : syracuseStep 23318057 = 17488543) B17488543
theorem B15545371 : Blo 2127435 15545371 := bstep (se 1 (by rfl) ⟨11659028, by rfl⟩ : syracuseStep 15545371 = 23318057) B23318057
theorem B20727161 : Blo 2127435 20727161 := bstep (se 2 (by rfl) ⟨7772685, by rfl⟩ : syracuseStep 20727161 = 15545371) B15545371
theorem B13818107 : Blo 2127435 13818107 := bstep (se 1 (by rfl) ⟨10363580, by rfl⟩ : syracuseStep 13818107 = 20727161) B20727161
theorem B9212071 : Blo 2127435 9212071 := bstep (se 1 (by rfl) ⟨6909053, by rfl⟩ : syracuseStep 9212071 = 13818107) B13818107
theorem B12282761 : Blo 2127435 12282761 := bstep (se 2 (by rfl) ⟨4606035, by rfl⟩ : syracuseStep 12282761 = 9212071) B9212071
theorem B8188507 : Blo 2127435 8188507 := bstep (se 1 (by rfl) ⟨6141380, by rfl⟩ : syracuseStep 8188507 = 12282761) B12282761
theorem B10918009 : Blo 2127435 10918009 := bstep (se 2 (by rfl) ⟨4094253, by rfl⟩ : syracuseStep 10918009 = 8188507) B8188507
theorem B58229381 : Blo 2127435 58229381 := bstep (se 4 (by rfl) ⟨5459004, by rfl⟩ : syracuseStep 58229381 = 10918009) B10918009
theorem B38819587 : Blo 2127435 38819587 := bstep (se 1 (by rfl) ⟨29114690, by rfl⟩ : syracuseStep 38819587 = 58229381) B58229381
theorem B51759449 : Blo 2127435 51759449 := bstep (se 2 (by rfl) ⟨19409793, by rfl⟩ : syracuseStep 51759449 = 38819587) B38819587
theorem B34506299 : Blo 2127435 34506299 := bstep (se 1 (by rfl) ⟨25879724, by rfl⟩ : syracuseStep 34506299 = 51759449) B51759449
theorem B23004199 : Blo 2127435 23004199 := bstep (se 1 (by rfl) ⟨17253149, by rfl⟩ : syracuseStep 23004199 = 34506299) B34506299
theorem B30672265 : Blo 2127435 30672265 := bstep (se 2 (by rfl) ⟨11502099, by rfl⟩ : syracuseStep 30672265 = 23004199) B23004199
theorem B40896353 : Blo 2127435 40896353 := bstep (se 2 (by rfl) ⟨15336132, by rfl⟩ : syracuseStep 40896353 = 30672265) B30672265
theorem B27264235 : Blo 2127435 27264235 := bstep (se 1 (by rfl) ⟨20448176, by rfl⟩ : syracuseStep 27264235 = 40896353) B40896353
theorem B36352313 : Blo 2127435 36352313 := bstep (se 2 (by rfl) ⟨13632117, by rfl⟩ : syracuseStep 36352313 = 27264235) B27264235
theorem B24234875 : Blo 2127435 24234875 := bstep (se 1 (by rfl) ⟨18176156, by rfl⟩ : syracuseStep 24234875 = 36352313) B36352313
theorem B16156583 : Blo 2127435 16156583 := bstep (se 1 (by rfl) ⟨12117437, by rfl⟩ : syracuseStep 16156583 = 24234875) B24234875
theorem B10771055 : Blo 2127435 10771055 := bstep (se 1 (by rfl) ⟨8078291, by rfl⟩ : syracuseStep 10771055 = 16156583) B16156583
theorem B7180703 : Blo 2127435 7180703 := bstep (se 1 (by rfl) ⟨5385527, by rfl⟩ : syracuseStep 7180703 = 10771055) B10771055
theorem B4787135 : Blo 2127435 4787135 := bstep (se 1 (by rfl) ⟨3590351, by rfl⟩ : syracuseStep 4787135 = 7180703) B7180703
theorem B3191423 : Blo 2127435 3191423 := bstep (se 1 (by rfl) ⟨2393567, by rfl⟩ : syracuseStep 3191423 = 4787135) B4787135
theorem B2127615 : Blo 2127435 2127615 := bstep (se 1 (by rfl) ⟨1595711, by rfl⟩ : syracuseStep 2127615 = 3191423) B3191423
theorem B3191429 : Blo 2127435 3191429 := bbase (se 4 (by rfl) ⟨299196, by rfl⟩ : syracuseStep 3191429 = 598393) (by norm_num)
theorem B2127619 : Blo 2127435 2127619 := bstep (se 1 (by rfl) ⟨1595714, by rfl⟩ : syracuseStep 2127619 = 3191429) B3191429
theorem B3590365 : Blo 2127435 3590365 := bbase (se 3 (by rfl) ⟨673193, by rfl⟩ : syracuseStep 3590365 = 1346387) (by norm_num)
theorem B4787153 : Blo 2127435 4787153 := bstep (se 2 (by rfl) ⟨1795182, by rfl⟩ : syracuseStep 4787153 = 3590365) B3590365
theorem B3191435 : Blo 2127435 3191435 := bstep (se 1 (by rfl) ⟨2393576, by rfl⟩ : syracuseStep 3191435 = 4787153) B4787153
theorem B2127623 : Blo 2127435 2127623 := bstep (se 1 (by rfl) ⟨1595717, by rfl⟩ : syracuseStep 2127623 = 3191435) B3191435
theorem B2393581 : Blo 2127435 2393581 := bbase (se 3 (by rfl) ⟨448796, by rfl⟩ : syracuseStep 2393581 = 897593) (by norm_num)
theorem B3191441 : Blo 2127435 3191441 := bstep (se 2 (by rfl) ⟨1196790, by rfl⟩ : syracuseStep 3191441 = 2393581) B2393581
theorem B2127627 : Blo 2127435 2127627 := bstep (se 1 (by rfl) ⟨1595720, by rfl⟩ : syracuseStep 2127627 = 3191441) B3191441
theorem B7180757 : Blo 2127435 7180757 := bbase (se 7 (by rfl) ⟨84149, by rfl⟩ : syracuseStep 7180757 = 168299) (by norm_num)
theorem B4787171 : Blo 2127435 4787171 := bstep (se 1 (by rfl) ⟨3590378, by rfl⟩ : syracuseStep 4787171 = 7180757) B7180757
theorem B3191447 : Blo 2127435 3191447 := bstep (se 1 (by rfl) ⟨2393585, by rfl⟩ : syracuseStep 3191447 = 4787171) B4787171
theorem B2127631 : Blo 2127435 2127631 := bstep (se 1 (by rfl) ⟨1595723, by rfl⟩ : syracuseStep 2127631 = 3191447) B3191447
theorem B3191453 : Blo 2127435 3191453 := bbase (se 3 (by rfl) ⟨598397, by rfl⟩ : syracuseStep 3191453 = 1196795) (by norm_num)
theorem B2127635 : Blo 2127435 2127635 := bstep (se 1 (by rfl) ⟨1595726, by rfl⟩ : syracuseStep 2127635 = 3191453) B3191453
theorem B4787189 : Blo 2127435 4787189 := bbase (se 5 (by rfl) ⟨224399, by rfl⟩ : syracuseStep 4787189 = 448799) (by norm_num)
theorem B3191459 : Blo 2127435 3191459 := bstep (se 1 (by rfl) ⟨2393594, by rfl⟩ : syracuseStep 3191459 = 4787189) B4787189
theorem B2127639 : Blo 2127435 2127639 := bstep (se 1 (by rfl) ⟨1595729, by rfl⟩ : syracuseStep 2127639 = 3191459) B3191459
theorem B2426257 : Blo 2127435 2426257 := bbase (se 2 (by rfl) ⟨909846, by rfl⟩ : syracuseStep 2426257 = 1819693) (by norm_num)
theorem B3235009 : Blo 2127435 3235009 := bstep (se 2 (by rfl) ⟨1213128, by rfl⟩ : syracuseStep 3235009 = 2426257) B2426257
theorem B4313345 : Blo 2127435 4313345 := bstep (se 2 (by rfl) ⟨1617504, by rfl⟩ : syracuseStep 4313345 = 3235009) B3235009
theorem B11502253 : Blo 2127435 11502253 := bstep (se 3 (by rfl) ⟨2156672, by rfl⟩ : syracuseStep 11502253 = 4313345) B4313345
theorem B61345349 : Blo 2127435 61345349 := bstep (se 4 (by rfl) ⟨5751126, by rfl⟩ : syracuseStep 61345349 = 11502253) B11502253
theorem B40896899 : Blo 2127435 40896899 := bstep (se 1 (by rfl) ⟨30672674, by rfl⟩ : syracuseStep 40896899 = 61345349) B61345349
theorem B27264599 : Blo 2127435 27264599 := bstep (se 1 (by rfl) ⟨20448449, by rfl⟩ : syracuseStep 27264599 = 40896899) B40896899
theorem B18176399 : Blo 2127435 18176399 := bstep (se 1 (by rfl) ⟨13632299, by rfl⟩ : syracuseStep 18176399 = 27264599) B27264599
theorem B12117599 : Blo 2127435 12117599 := bstep (se 1 (by rfl) ⟨9088199, by rfl⟩ : syracuseStep 12117599 = 18176399) B18176399
theorem B8078399 : Blo 2127435 8078399 := bstep (se 1 (by rfl) ⟨6058799, by rfl⟩ : syracuseStep 8078399 = 12117599) B12117599
theorem B5385599 : Blo 2127435 5385599 := bstep (se 1 (by rfl) ⟨4039199, by rfl⟩ : syracuseStep 5385599 = 8078399) B8078399
theorem B3590399 : Blo 2127435 3590399 := bstep (se 1 (by rfl) ⟨2692799, by rfl⟩ : syracuseStep 3590399 = 5385599) B5385599
theorem B2393599 : Blo 2127435 2393599 := bstep (se 1 (by rfl) ⟨1795199, by rfl⟩ : syracuseStep 2393599 = 3590399) B3590399
theorem B3191465 : Blo 2127435 3191465 := bstep (se 2 (by rfl) ⟨1196799, by rfl⟩ : syracuseStep 3191465 = 2393599) B2393599
theorem B2127643 : Blo 2127435 2127643 := bstep (se 1 (by rfl) ⟨1595732, by rfl⟩ : syracuseStep 2127643 = 3191465) B3191465
theorem B3029405 : Blo 2127435 3029405 := bbase (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) (by norm_num)
theorem B8078413 : Blo 2127435 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B10771217 : Blo 2127435 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B7180811 : Blo 2127435 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B4787207 : Blo 2127435 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B3191471 : Blo 2127435 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B2127647 : Blo 2127435 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B3191477 : Blo 2127435 3191477 := bbase (se 5 (by rfl) ⟨149600, by rfl⟩ : syracuseStep 3191477 = 299201) (by norm_num)
theorem B2127651 : Blo 2127435 2127651 := bstep (se 1 (by rfl) ⟨1595738, by rfl⟩ : syracuseStep 2127651 = 3191477) B3191477
theorem B5385629 : Blo 2127435 5385629 := bbase (se 3 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 5385629 = 2019611) (by norm_num)
theorem B3590419 : Blo 2127435 3590419 := bstep (se 1 (by rfl) ⟨2692814, by rfl⟩ : syracuseStep 3590419 = 5385629) B5385629
theorem B4787225 : Blo 2127435 4787225 := bstep (se 2 (by rfl) ⟨1795209, by rfl⟩ : syracuseStep 4787225 = 3590419) B3590419
theorem B3191483 : Blo 2127435 3191483 := bstep (se 1 (by rfl) ⟨2393612, by rfl⟩ : syracuseStep 3191483 = 4787225) B4787225
theorem B2127655 : Blo 2127435 2127655 := bstep (se 1 (by rfl) ⟨1595741, by rfl⟩ : syracuseStep 2127655 = 3191483) B3191483
theorem B2393617 : Blo 2127435 2393617 := bbase (se 2 (by rfl) ⟨897606, by rfl⟩ : syracuseStep 2393617 = 1795213) (by norm_num)
theorem B3191489 : Blo 2127435 3191489 := bstep (se 2 (by rfl) ⟨1196808, by rfl⟩ : syracuseStep 3191489 = 2393617) B2393617
theorem B2127659 : Blo 2127435 2127659 := bstep (se 1 (by rfl) ⟨1595744, by rfl⟩ : syracuseStep 2127659 = 3191489) B3191489
theorem B4039237 : Blo 2127435 4039237 := bbase (se 4 (by rfl) ⟨378678, by rfl⟩ : syracuseStep 4039237 = 757357) (by norm_num)
theorem B5385649 : Blo 2127435 5385649 := bstep (se 2 (by rfl) ⟨2019618, by rfl⟩ : syracuseStep 5385649 = 4039237) B4039237
theorem B7180865 : Blo 2127435 7180865 := bstep (se 2 (by rfl) ⟨2692824, by rfl⟩ : syracuseStep 7180865 = 5385649) B5385649
theorem B4787243 : Blo 2127435 4787243 := bstep (se 1 (by rfl) ⟨3590432, by rfl⟩ : syracuseStep 4787243 = 7180865) B7180865
theorem B3191495 : Blo 2127435 3191495 := bstep (se 1 (by rfl) ⟨2393621, by rfl⟩ : syracuseStep 3191495 = 4787243) B4787243
theorem B2127663 : Blo 2127435 2127663 := bstep (se 1 (by rfl) ⟨1595747, by rfl⟩ : syracuseStep 2127663 = 3191495) B3191495
theorem B3191501 : Blo 2127435 3191501 := bbase (se 3 (by rfl) ⟨598406, by rfl⟩ : syracuseStep 3191501 = 1196813) (by norm_num)
theorem B2127667 : Blo 2127435 2127667 := bstep (se 1 (by rfl) ⟨1595750, by rfl⟩ : syracuseStep 2127667 = 3191501) B3191501
theorem B4787261 : Blo 2127435 4787261 := bbase (se 3 (by rfl) ⟨897611, by rfl⟩ : syracuseStep 4787261 = 1795223) (by norm_num)
theorem B3191507 : Blo 2127435 3191507 := bstep (se 1 (by rfl) ⟨2393630, by rfl⟩ : syracuseStep 3191507 = 4787261) B4787261
theorem B2127671 : Blo 2127435 2127671 := bstep (se 1 (by rfl) ⟨1595753, by rfl⟩ : syracuseStep 2127671 = 3191507) B3191507
theorem B3590453 : Blo 2127435 3590453 := bbase (se 5 (by rfl) ⟨168302, by rfl⟩ : syracuseStep 3590453 = 336605) (by norm_num)
theorem B2393635 : Blo 2127435 2393635 := bstep (se 1 (by rfl) ⟨1795226, by rfl⟩ : syracuseStep 2393635 = 3590453) B3590453
theorem B3191513 : Blo 2127435 3191513 := bstep (se 2 (by rfl) ⟨1196817, by rfl⟩ : syracuseStep 3191513 = 2393635) B2393635
theorem B2127675 : Blo 2127435 2127675 := bstep (se 1 (by rfl) ⟨1595756, by rfl⟩ : syracuseStep 2127675 = 3191513) B3191513
theorem B6058901 : Blo 2127435 6058901 := bbase (se 6 (by rfl) ⟨142005, by rfl⟩ : syracuseStep 6058901 = 284011) (by norm_num)
theorem B16157069 : Blo 2127435 16157069 := bstep (se 3 (by rfl) ⟨3029450, by rfl⟩ : syracuseStep 16157069 = 6058901) B6058901
theorem B10771379 : Blo 2127435 10771379 := bstep (se 1 (by rfl) ⟨8078534, by rfl⟩ : syracuseStep 10771379 = 16157069) B16157069
theorem B7180919 : Blo 2127435 7180919 := bstep (se 1 (by rfl) ⟨5385689, by rfl⟩ : syracuseStep 7180919 = 10771379) B10771379
theorem B4787279 : Blo 2127435 4787279 := bstep (se 1 (by rfl) ⟨3590459, by rfl⟩ : syracuseStep 4787279 = 7180919) B7180919
theorem B3191519 : Blo 2127435 3191519 := bstep (se 1 (by rfl) ⟨2393639, by rfl⟩ : syracuseStep 3191519 = 4787279) B4787279
theorem B2127679 : Blo 2127435 2127679 := bstep (se 1 (by rfl) ⟨1595759, by rfl⟩ : syracuseStep 2127679 = 3191519) B3191519
theorem B3191525 : Blo 2127435 3191525 := bbase (se 4 (by rfl) ⟨299205, by rfl⟩ : syracuseStep 3191525 = 598411) (by norm_num)
theorem B2127683 : Blo 2127435 2127683 := bstep (se 1 (by rfl) ⟨1595762, by rfl⟩ : syracuseStep 2127683 = 3191525) B3191525
theorem B2272097 : Blo 2127435 2272097 := bbase (se 2 (by rfl) ⟨852036, by rfl⟩ : syracuseStep 2272097 = 1704073) (by norm_num)
theorem B6058925 : Blo 2127435 6058925 := bstep (se 3 (by rfl) ⟨1136048, by rfl⟩ : syracuseStep 6058925 = 2272097) B2272097
theorem B4039283 : Blo 2127435 4039283 := bstep (se 1 (by rfl) ⟨3029462, by rfl⟩ : syracuseStep 4039283 = 6058925) B6058925
theorem B2692855 : Blo 2127435 2692855 := bstep (se 1 (by rfl) ⟨2019641, by rfl⟩ : syracuseStep 2692855 = 4039283) B4039283
theorem B3590473 : Blo 2127435 3590473 := bstep (se 2 (by rfl) ⟨1346427, by rfl⟩ : syracuseStep 3590473 = 2692855) B2692855
theorem B4787297 : Blo 2127435 4787297 := bstep (se 2 (by rfl) ⟨1795236, by rfl⟩ : syracuseStep 4787297 = 3590473) B3590473
theorem B3191531 : Blo 2127435 3191531 := bstep (se 1 (by rfl) ⟨2393648, by rfl⟩ : syracuseStep 3191531 = 4787297) B4787297
theorem B2127687 : Blo 2127435 2127687 := bstep (se 1 (by rfl) ⟨1595765, by rfl⟩ : syracuseStep 2127687 = 3191531) B3191531
theorem B2393653 : Blo 2127435 2393653 := bbase (se 5 (by rfl) ⟨112202, by rfl⟩ : syracuseStep 2393653 = 224405) (by norm_num)
theorem B3191537 : Blo 2127435 3191537 := bstep (se 2 (by rfl) ⟨1196826, by rfl⟩ : syracuseStep 3191537 = 2393653) B2393653
theorem B2127691 : Blo 2127435 2127691 := bstep (se 1 (by rfl) ⟨1595768, by rfl⟩ : syracuseStep 2127691 = 3191537) B3191537
theorem B2692865 : Blo 2127435 2692865 := bbase (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) (by norm_num)
theorem B7180973 : Blo 2127435 7180973 := bstep (se 3 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 7180973 = 2692865) B2692865
theorem B4787315 : Blo 2127435 4787315 := bstep (se 1 (by rfl) ⟨3590486, by rfl⟩ : syracuseStep 4787315 = 7180973) B7180973
theorem B3191543 : Blo 2127435 3191543 := bstep (se 1 (by rfl) ⟨2393657, by rfl⟩ : syracuseStep 3191543 = 4787315) B4787315
theorem B2127695 : Blo 2127435 2127695 := bstep (se 1 (by rfl) ⟨1595771, by rfl⟩ : syracuseStep 2127695 = 3191543) B3191543
theorem B3191549 : Blo 2127435 3191549 := bbase (se 3 (by rfl) ⟨598415, by rfl⟩ : syracuseStep 3191549 = 1196831) (by norm_num)
theorem B2127699 : Blo 2127435 2127699 := bstep (se 1 (by rfl) ⟨1595774, by rfl⟩ : syracuseStep 2127699 = 3191549) B3191549
theorem B4787333 : Blo 2127435 4787333 := bbase (se 4 (by rfl) ⟨448812, by rfl⟩ : syracuseStep 4787333 = 897625) (by norm_num)
theorem B3191555 : Blo 2127435 3191555 := bstep (se 1 (by rfl) ⟨2393666, by rfl⟩ : syracuseStep 3191555 = 4787333) B4787333
theorem B2127703 : Blo 2127435 2127703 := bstep (se 1 (by rfl) ⟨1595777, by rfl⟩ : syracuseStep 2127703 = 3191555) B3191555
theorem B4544237 : Blo 2127435 4544237 := bbase (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) (by norm_num)
theorem B3029491 : Blo 2127435 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B4039321 : Blo 2127435 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B5385761 : Blo 2127435 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B3590507 : Blo 2127435 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B2393671 : Blo 2127435 2393671 := bstep (se 1 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 2393671 = 3590507) B3590507
theorem B3191561 : Blo 2127435 3191561 := bstep (se 2 (by rfl) ⟨1196835, by rfl⟩ : syracuseStep 3191561 = 2393671) B2393671
theorem B2127707 : Blo 2127435 2127707 := bstep (se 1 (by rfl) ⟨1595780, by rfl⟩ : syracuseStep 2127707 = 3191561) B3191561
theorem B10771541 : Blo 2127435 10771541 := bbase (se 8 (by rfl) ⟨63114, by rfl⟩ : syracuseStep 10771541 = 126229) (by norm_num)
theorem B7181027 : Blo 2127435 7181027 := bstep (se 1 (by rfl) ⟨5385770, by rfl⟩ : syracuseStep 7181027 = 10771541) B10771541
theorem B4787351 : Blo 2127435 4787351 := bstep (se 1 (by rfl) ⟨3590513, by rfl⟩ : syracuseStep 4787351 = 7181027) B7181027
theorem B3191567 : Blo 2127435 3191567 := bstep (se 1 (by rfl) ⟨2393675, by rfl⟩ : syracuseStep 3191567 = 4787351) B4787351
theorem B2127711 : Blo 2127435 2127711 := bstep (se 1 (by rfl) ⟨1595783, by rfl⟩ : syracuseStep 2127711 = 3191567) B3191567
theorem B3191573 : Blo 2127435 3191573 := bbase (se 6 (by rfl) ⟨74802, by rfl⟩ : syracuseStep 3191573 = 149605) (by norm_num)
theorem B2127715 : Blo 2127435 2127715 := bstep (se 1 (by rfl) ⟨1595786, by rfl⟩ : syracuseStep 2127715 = 3191573) B3191573
theorem B3834221 : Blo 2127435 3834221 := bbase (se 3 (by rfl) ⟨718916, by rfl⟩ : syracuseStep 3834221 = 1437833) (by norm_num)
theorem B40898357 : Blo 2127435 40898357 := bstep (se 5 (by rfl) ⟨1917110, by rfl⟩ : syracuseStep 40898357 = 3834221) B3834221
theorem B27265571 : Blo 2127435 27265571 := bstep (se 1 (by rfl) ⟨20449178, by rfl⟩ : syracuseStep 27265571 = 40898357) B40898357
theorem B18177047 : Blo 2127435 18177047 := bstep (se 1 (by rfl) ⟨13632785, by rfl⟩ : syracuseStep 18177047 = 27265571) B27265571
theorem B12118031 : Blo 2127435 12118031 := bstep (se 1 (by rfl) ⟨9088523, by rfl⟩ : syracuseStep 12118031 = 18177047) B18177047
theorem B8078687 : Blo 2127435 8078687 := bstep (se 1 (by rfl) ⟨6059015, by rfl⟩ : syracuseStep 8078687 = 12118031) B12118031
theorem B5385791 : Blo 2127435 5385791 := bstep (se 1 (by rfl) ⟨4039343, by rfl⟩ : syracuseStep 5385791 = 8078687) B8078687
theorem B3590527 : Blo 2127435 3590527 := bstep (se 1 (by rfl) ⟨2692895, by rfl⟩ : syracuseStep 3590527 = 5385791) B5385791
theorem B4787369 : Blo 2127435 4787369 := bstep (se 2 (by rfl) ⟨1795263, by rfl⟩ : syracuseStep 4787369 = 3590527) B3590527
theorem B3191579 : Blo 2127435 3191579 := bstep (se 1 (by rfl) ⟨2393684, by rfl⟩ : syracuseStep 3191579 = 4787369) B4787369
theorem B2127719 : Blo 2127435 2127719 := bstep (se 1 (by rfl) ⟨1595789, by rfl⟩ : syracuseStep 2127719 = 3191579) B3191579
theorem B2393689 : Blo 2127435 2393689 := bbase (se 2 (by rfl) ⟨897633, by rfl⟩ : syracuseStep 2393689 = 1795267) (by norm_num)
theorem B3191585 : Blo 2127435 3191585 := bstep (se 2 (by rfl) ⟨1196844, by rfl⟩ : syracuseStep 3191585 = 2393689) B2393689
theorem B2127723 : Blo 2127435 2127723 := bstep (se 1 (by rfl) ⟨1595792, by rfl⟩ : syracuseStep 2127723 = 3191585) B3191585
theorem B10224629 : Blo 2127435 10224629 := bbase (se 5 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 10224629 = 958559) (by norm_num)
theorem B6816419 : Blo 2127435 6816419 := bstep (se 1 (by rfl) ⟨5112314, by rfl⟩ : syracuseStep 6816419 = 10224629) B10224629
theorem B4544279 : Blo 2127435 4544279 := bstep (se 1 (by rfl) ⟨3408209, by rfl⟩ : syracuseStep 4544279 = 6816419) B6816419
theorem B3029519 : Blo 2127435 3029519 := bstep (se 1 (by rfl) ⟨2272139, by rfl⟩ : syracuseStep 3029519 = 4544279) B4544279
theorem B8078717 : Blo 2127435 8078717 := bstep (se 3 (by rfl) ⟨1514759, by rfl⟩ : syracuseStep 8078717 = 3029519) B3029519
theorem B5385811 : Blo 2127435 5385811 := bstep (se 1 (by rfl) ⟨4039358, by rfl⟩ : syracuseStep 5385811 = 8078717) B8078717
theorem B7181081 : Blo 2127435 7181081 := bstep (se 2 (by rfl) ⟨2692905, by rfl⟩ : syracuseStep 7181081 = 5385811) B5385811
theorem B4787387 : Blo 2127435 4787387 := bstep (se 1 (by rfl) ⟨3590540, by rfl⟩ : syracuseStep 4787387 = 7181081) B7181081
theorem B3191591 : Blo 2127435 3191591 := bstep (se 1 (by rfl) ⟨2393693, by rfl⟩ : syracuseStep 3191591 = 4787387) B4787387
theorem B2127727 : Blo 2127435 2127727 := bstep (se 1 (by rfl) ⟨1595795, by rfl⟩ : syracuseStep 2127727 = 3191591) B3191591
theorem B3191597 : Blo 2127435 3191597 := bbase (se 3 (by rfl) ⟨598424, by rfl⟩ : syracuseStep 3191597 = 1196849) (by norm_num)
theorem B2127731 : Blo 2127435 2127731 := bstep (se 1 (by rfl) ⟨1595798, by rfl⟩ : syracuseStep 2127731 = 3191597) B3191597
theorem B4787405 : Blo 2127435 4787405 := bbase (se 3 (by rfl) ⟨897638, by rfl⟩ : syracuseStep 4787405 = 1795277) (by norm_num)
theorem B3191603 : Blo 2127435 3191603 := bstep (se 1 (by rfl) ⟨2393702, by rfl⟩ : syracuseStep 3191603 = 4787405) B4787405
theorem B2127735 : Blo 2127435 2127735 := bstep (se 1 (by rfl) ⟨1595801, by rfl⟩ : syracuseStep 2127735 = 3191603) B3191603
theorem B2692921 : Blo 2127435 2692921 := bbase (se 2 (by rfl) ⟨1009845, by rfl⟩ : syracuseStep 2692921 = 2019691) (by norm_num)
theorem B3590561 : Blo 2127435 3590561 := bstep (se 2 (by rfl) ⟨1346460, by rfl⟩ : syracuseStep 3590561 = 2692921) B2692921
theorem B2393707 : Blo 2127435 2393707 := bstep (se 1 (by rfl) ⟨1795280, by rfl⟩ : syracuseStep 2393707 = 3590561) B3590561
theorem B3191609 : Blo 2127435 3191609 := bstep (se 2 (by rfl) ⟨1196853, by rfl⟩ : syracuseStep 3191609 = 2393707) B2393707
theorem B2127739 : Blo 2127435 2127739 := bstep (se 1 (by rfl) ⟨1595804, by rfl⟩ : syracuseStep 2127739 = 3191609) B3191609
theorem B6816469 : Blo 2127435 6816469 := bbase (se 7 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 6816469 = 159761) (by norm_num)
theorem B9088625 : Blo 2127435 9088625 := bstep (se 2 (by rfl) ⟨3408234, by rfl⟩ : syracuseStep 9088625 = 6816469) B6816469
theorem B24236333 : Blo 2127435 24236333 := bstep (se 3 (by rfl) ⟨4544312, by rfl⟩ : syracuseStep 24236333 = 9088625) B9088625
theorem B16157555 : Blo 2127435 16157555 := bstep (se 1 (by rfl) ⟨12118166, by rfl⟩ : syracuseStep 16157555 = 24236333) B24236333
theorem B10771703 : Blo 2127435 10771703 := bstep (se 1 (by rfl) ⟨8078777, by rfl⟩ : syracuseStep 10771703 = 16157555) B16157555
theorem B7181135 : Blo 2127435 7181135 := bstep (se 1 (by rfl) ⟨5385851, by rfl⟩ : syracuseStep 7181135 = 10771703) B10771703
theorem B4787423 : Blo 2127435 4787423 := bstep (se 1 (by rfl) ⟨3590567, by rfl⟩ : syracuseStep 4787423 = 7181135) B7181135
theorem B3191615 : Blo 2127435 3191615 := bstep (se 1 (by rfl) ⟨2393711, by rfl⟩ : syracuseStep 3191615 = 4787423) B4787423
theorem B2127743 : Blo 2127435 2127743 := bstep (se 1 (by rfl) ⟨1595807, by rfl⟩ : syracuseStep 2127743 = 3191615) B3191615
theorem B3191621 : Blo 2127435 3191621 := bbase (se 4 (by rfl) ⟨299214, by rfl⟩ : syracuseStep 3191621 = 598429) (by norm_num)
theorem B2127747 : Blo 2127435 2127747 := bstep (se 1 (by rfl) ⟨1595810, by rfl⟩ : syracuseStep 2127747 = 3191621) B3191621
theorem B3590581 : Blo 2127435 3590581 := bbase (se 5 (by rfl) ⟨168308, by rfl⟩ : syracuseStep 3590581 = 336617) (by norm_num)
theorem B4787441 : Blo 2127435 4787441 := bstep (se 2 (by rfl) ⟨1795290, by rfl⟩ : syracuseStep 4787441 = 3590581) B3590581
theorem B3191627 : Blo 2127435 3191627 := bstep (se 1 (by rfl) ⟨2393720, by rfl⟩ : syracuseStep 3191627 = 4787441) B4787441
theorem B2127751 : Blo 2127435 2127751 := bstep (se 1 (by rfl) ⟨1595813, by rfl⟩ : syracuseStep 2127751 = 3191627) B3191627
theorem B2393725 : Blo 2127435 2393725 := bbase (se 3 (by rfl) ⟨448823, by rfl⟩ : syracuseStep 2393725 = 897647) (by norm_num)
theorem B3191633 : Blo 2127435 3191633 := bstep (se 2 (by rfl) ⟨1196862, by rfl⟩ : syracuseStep 3191633 = 2393725) B2393725
theorem B2127755 : Blo 2127435 2127755 := bstep (se 1 (by rfl) ⟨1595816, by rfl⟩ : syracuseStep 2127755 = 3191633) B3191633
theorem B7181189 : Blo 2127435 7181189 := bbase (se 4 (by rfl) ⟨673236, by rfl⟩ : syracuseStep 7181189 = 1346473) (by norm_num)
theorem B4787459 : Blo 2127435 4787459 := bstep (se 1 (by rfl) ⟨3590594, by rfl⟩ : syracuseStep 4787459 = 7181189) B7181189
theorem B3191639 : Blo 2127435 3191639 := bstep (se 1 (by rfl) ⟨2393729, by rfl⟩ : syracuseStep 3191639 = 4787459) B4787459
theorem B2127759 : Blo 2127435 2127759 := bstep (se 1 (by rfl) ⟨1595819, by rfl⟩ : syracuseStep 2127759 = 3191639) B3191639
theorem B3191645 : Blo 2127435 3191645 := bbase (se 3 (by rfl) ⟨598433, by rfl⟩ : syracuseStep 3191645 = 1196867) (by norm_num)
theorem B2127763 : Blo 2127435 2127763 := bstep (se 1 (by rfl) ⟨1595822, by rfl⟩ : syracuseStep 2127763 = 3191645) B3191645
theorem B4787477 : Blo 2127435 4787477 := bbase (se 6 (by rfl) ⟨112206, by rfl⟩ : syracuseStep 4787477 = 224413) (by norm_num)
theorem B3191651 : Blo 2127435 3191651 := bstep (se 1 (by rfl) ⟨2393738, by rfl⟩ : syracuseStep 3191651 = 4787477) B4787477
theorem B2127767 : Blo 2127435 2127767 := bstep (se 1 (by rfl) ⟨1595825, by rfl⟩ : syracuseStep 2127767 = 3191651) B3191651
theorem B8078885 : Blo 2127435 8078885 := bbase (se 4 (by rfl) ⟨757395, by rfl⟩ : syracuseStep 8078885 = 1514791) (by norm_num)
theorem B5385923 : Blo 2127435 5385923 := bstep (se 1 (by rfl) ⟨4039442, by rfl⟩ : syracuseStep 5385923 = 8078885) B8078885
theorem B3590615 : Blo 2127435 3590615 := bstep (se 1 (by rfl) ⟨2692961, by rfl⟩ : syracuseStep 3590615 = 5385923) B5385923
theorem B2393743 : Blo 2127435 2393743 := bstep (se 1 (by rfl) ⟨1795307, by rfl⟩ : syracuseStep 2393743 = 3590615) B3590615
theorem B3191657 : Blo 2127435 3191657 := bstep (se 2 (by rfl) ⟨1196871, by rfl⟩ : syracuseStep 3191657 = 2393743) B2393743
theorem B2127771 : Blo 2127435 2127771 := bstep (se 1 (by rfl) ⟨1595828, by rfl⟩ : syracuseStep 2127771 = 3191657) B3191657
theorem B4544381 : Blo 2127435 4544381 := bbase (se 3 (by rfl) ⟨852071, by rfl⟩ : syracuseStep 4544381 = 1704143) (by norm_num)
theorem B12118349 : Blo 2127435 12118349 := bstep (se 3 (by rfl) ⟨2272190, by rfl⟩ : syracuseStep 12118349 = 4544381) B4544381
theorem B8078899 : Blo 2127435 8078899 := bstep (se 1 (by rfl) ⟨6059174, by rfl⟩ : syracuseStep 8078899 = 12118349) B12118349
theorem B10771865 : Blo 2127435 10771865 := bstep (se 2 (by rfl) ⟨4039449, by rfl⟩ : syracuseStep 10771865 = 8078899) B8078899
theorem B7181243 : Blo 2127435 7181243 := bstep (se 1 (by rfl) ⟨5385932, by rfl⟩ : syracuseStep 7181243 = 10771865) B10771865
theorem B4787495 : Blo 2127435 4787495 := bstep (se 1 (by rfl) ⟨3590621, by rfl⟩ : syracuseStep 4787495 = 7181243) B7181243
theorem B3191663 : Blo 2127435 3191663 := bstep (se 1 (by rfl) ⟨2393747, by rfl⟩ : syracuseStep 3191663 = 4787495) B4787495
theorem B2127775 : Blo 2127435 2127775 := bstep (se 1 (by rfl) ⟨1595831, by rfl⟩ : syracuseStep 2127775 = 3191663) B3191663
theorem B3191669 : Blo 2127435 3191669 := bbase (se 5 (by rfl) ⟨149609, by rfl⟩ : syracuseStep 3191669 = 299219) (by norm_num)
theorem B2127779 : Blo 2127435 2127779 := bstep (se 1 (by rfl) ⟨1595834, by rfl⟩ : syracuseStep 2127779 = 3191669) B3191669
theorem B7279253 : Blo 2127435 7279253 := bbase (se 6 (by rfl) ⟨170607, by rfl⟩ : syracuseStep 7279253 = 341215) (by norm_num)
theorem B4852835 : Blo 2127435 4852835 := bstep (se 1 (by rfl) ⟨3639626, by rfl⟩ : syracuseStep 4852835 = 7279253) B7279253
theorem B3235223 : Blo 2127435 3235223 := bstep (se 1 (by rfl) ⟨2426417, by rfl⟩ : syracuseStep 3235223 = 4852835) B4852835
theorem B2156815 : Blo 2127435 2156815 := bstep (se 1 (by rfl) ⟨1617611, by rfl⟩ : syracuseStep 2156815 = 3235223) B3235223
theorem B2875753 : Blo 2127435 2875753 := bstep (se 2 (by rfl) ⟨1078407, by rfl⟩ : syracuseStep 2875753 = 2156815) B2156815
theorem B15337349 : Blo 2127435 15337349 := bstep (se 4 (by rfl) ⟨1437876, by rfl⟩ : syracuseStep 15337349 = 2875753) B2875753
theorem B10224899 : Blo 2127435 10224899 := bstep (se 1 (by rfl) ⟨7668674, by rfl⟩ : syracuseStep 10224899 = 15337349) B15337349
theorem B6816599 : Blo 2127435 6816599 := bstep (se 1 (by rfl) ⟨5112449, by rfl⟩ : syracuseStep 6816599 = 10224899) B10224899
theorem B4544399 : Blo 2127435 4544399 := bstep (se 1 (by rfl) ⟨3408299, by rfl⟩ : syracuseStep 4544399 = 6816599) B6816599
theorem B3029599 : Blo 2127435 3029599 := bstep (se 1 (by rfl) ⟨2272199, by rfl⟩ : syracuseStep 3029599 = 4544399) B4544399
theorem B4039465 : Blo 2127435 4039465 := bstep (se 2 (by rfl) ⟨1514799, by rfl⟩ : syracuseStep 4039465 = 3029599) B3029599
theorem B5385953 : Blo 2127435 5385953 := bstep (se 2 (by rfl) ⟨2019732, by rfl⟩ : syracuseStep 5385953 = 4039465) B4039465
theorem B3590635 : Blo 2127435 3590635 := bstep (se 1 (by rfl) ⟨2692976, by rfl⟩ : syracuseStep 3590635 = 5385953) B5385953
theorem B4787513 : Blo 2127435 4787513 := bstep (se 2 (by rfl) ⟨1795317, by rfl⟩ : syracuseStep 4787513 = 3590635) B3590635
theorem B3191675 : Blo 2127435 3191675 := bstep (se 1 (by rfl) ⟨2393756, by rfl⟩ : syracuseStep 3191675 = 4787513) B4787513
theorem B2127783 : Blo 2127435 2127783 := bstep (se 1 (by rfl) ⟨1595837, by rfl⟩ : syracuseStep 2127783 = 3191675) B3191675
theorem B2393761 : Blo 2127435 2393761 := bbase (se 2 (by rfl) ⟨897660, by rfl⟩ : syracuseStep 2393761 = 1795321) (by norm_num)
theorem B3191681 : Blo 2127435 3191681 := bstep (se 2 (by rfl) ⟨1196880, by rfl⟩ : syracuseStep 3191681 = 2393761) B2393761
theorem B2127787 : Blo 2127435 2127787 := bstep (se 1 (by rfl) ⟨1595840, by rfl⟩ : syracuseStep 2127787 = 3191681) B3191681
theorem B5385973 : Blo 2127435 5385973 := bbase (se 5 (by rfl) ⟨252467, by rfl⟩ : syracuseStep 5385973 = 504935) (by norm_num)
theorem B7181297 : Blo 2127435 7181297 := bstep (se 2 (by rfl) ⟨2692986, by rfl⟩ : syracuseStep 7181297 = 5385973) B5385973
theorem B4787531 : Blo 2127435 4787531 := bstep (se 1 (by rfl) ⟨3590648, by rfl⟩ : syracuseStep 4787531 = 7181297) B7181297
theorem B3191687 : Blo 2127435 3191687 := bstep (se 1 (by rfl) ⟨2393765, by rfl⟩ : syracuseStep 3191687 = 4787531) B4787531
theorem B2127791 : Blo 2127435 2127791 := bstep (se 1 (by rfl) ⟨1595843, by rfl⟩ : syracuseStep 2127791 = 3191687) B3191687
theorem B3191693 : Blo 2127435 3191693 := bbase (se 3 (by rfl) ⟨598442, by rfl⟩ : syracuseStep 3191693 = 1196885) (by norm_num)
theorem B2127795 : Blo 2127435 2127795 := bstep (se 1 (by rfl) ⟨1595846, by rfl⟩ : syracuseStep 2127795 = 3191693) B3191693
theorem B4787549 : Blo 2127435 4787549 := bbase (se 3 (by rfl) ⟨897665, by rfl⟩ : syracuseStep 4787549 = 1795331) (by norm_num)
theorem B3191699 : Blo 2127435 3191699 := bstep (se 1 (by rfl) ⟨2393774, by rfl⟩ : syracuseStep 3191699 = 4787549) B4787549
theorem B2127799 : Blo 2127435 2127799 := bstep (se 1 (by rfl) ⟨1595849, by rfl⟩ : syracuseStep 2127799 = 3191699) B3191699
theorem B3590669 : Blo 2127435 3590669 := bbase (se 3 (by rfl) ⟨673250, by rfl⟩ : syracuseStep 3590669 = 1346501) (by norm_num)
theorem B2393779 : Blo 2127435 2393779 := bstep (se 1 (by rfl) ⟨1795334, by rfl⟩ : syracuseStep 2393779 = 3590669) B3590669
theorem B3191705 : Blo 2127435 3191705 := bstep (se 2 (by rfl) ⟨1196889, by rfl⟩ : syracuseStep 3191705 = 2393779) B2393779
theorem B2127803 : Blo 2127435 2127803 := bstep (se 1 (by rfl) ⟨1595852, by rfl⟩ : syracuseStep 2127803 = 3191705) B3191705
theorem B2556253 : Blo 2127435 2556253 := bbase (se 3 (by rfl) ⟨479297, by rfl⟩ : syracuseStep 2556253 = 958595) (by norm_num)
theorem B3408337 : Blo 2127435 3408337 := bstep (se 2 (by rfl) ⟨1278126, by rfl⟩ : syracuseStep 3408337 = 2556253) B2556253
theorem B18177797 : Blo 2127435 18177797 := bstep (se 4 (by rfl) ⟨1704168, by rfl⟩ : syracuseStep 18177797 = 3408337) B3408337
theorem B12118531 : Blo 2127435 12118531 := bstep (se 1 (by rfl) ⟨9088898, by rfl⟩ : syracuseStep 12118531 = 18177797) B18177797
theorem B16158041 : Blo 2127435 16158041 := bstep (se 2 (by rfl) ⟨6059265, by rfl⟩ : syracuseStep 16158041 = 12118531) B12118531
theorem B10772027 : Blo 2127435 10772027 := bstep (se 1 (by rfl) ⟨8079020, by rfl⟩ : syracuseStep 10772027 = 16158041) B16158041
theorem B7181351 : Blo 2127435 7181351 := bstep (se 1 (by rfl) ⟨5386013, by rfl⟩ : syracuseStep 7181351 = 10772027) B10772027
theorem B4787567 : Blo 2127435 4787567 := bstep (se 1 (by rfl) ⟨3590675, by rfl⟩ : syracuseStep 4787567 = 7181351) B7181351
theorem B3191711 : Blo 2127435 3191711 := bstep (se 1 (by rfl) ⟨2393783, by rfl⟩ : syracuseStep 3191711 = 4787567) B4787567
theorem B2127807 : Blo 2127435 2127807 := bstep (se 1 (by rfl) ⟨1595855, by rfl⟩ : syracuseStep 2127807 = 3191711) B3191711
theorem B3191717 : Blo 2127435 3191717 := bbase (se 4 (by rfl) ⟨299223, by rfl⟩ : syracuseStep 3191717 = 598447) (by norm_num)
theorem B2127811 : Blo 2127435 2127811 := bstep (se 1 (by rfl) ⟨1595858, by rfl⟩ : syracuseStep 2127811 = 3191717) B3191717
theorem B2693017 : Blo 2127435 2693017 := bbase (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) (by norm_num)
theorem B3590689 : Blo 2127435 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B4787585 : Blo 2127435 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B3191723 : Blo 2127435 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B2127815 : Blo 2127435 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B2393797 : Blo 2127435 2393797 := bbase (se 4 (by rfl) ⟨224418, by rfl⟩ : syracuseStep 2393797 = 448837) (by norm_num)
theorem B3191729 : Blo 2127435 3191729 := bstep (se 2 (by rfl) ⟨1196898, by rfl⟩ : syracuseStep 3191729 = 2393797) B2393797
theorem B2127819 : Blo 2127435 2127819 := bstep (se 1 (by rfl) ⟨1595864, by rfl⟩ : syracuseStep 2127819 = 3191729) B3191729
theorem B4039541 : Blo 2127435 4039541 := bbase (se 5 (by rfl) ⟨189353, by rfl⟩ : syracuseStep 4039541 = 378707) (by norm_num)
theorem B2693027 : Blo 2127435 2693027 := bstep (se 1 (by rfl) ⟨2019770, by rfl⟩ : syracuseStep 2693027 = 4039541) B4039541
theorem B7181405 : Blo 2127435 7181405 := bstep (se 3 (by rfl) ⟨1346513, by rfl⟩ : syracuseStep 7181405 = 2693027) B2693027
theorem B4787603 : Blo 2127435 4787603 := bstep (se 1 (by rfl) ⟨3590702, by rfl⟩ : syracuseStep 4787603 = 7181405) B7181405
theorem B3191735 : Blo 2127435 3191735 := bstep (se 1 (by rfl) ⟨2393801, by rfl⟩ : syracuseStep 3191735 = 4787603) B4787603
theorem B2127823 : Blo 2127435 2127823 := bstep (se 1 (by rfl) ⟨1595867, by rfl⟩ : syracuseStep 2127823 = 3191735) B3191735
theorem B3191741 : Blo 2127435 3191741 := bbase (se 3 (by rfl) ⟨598451, by rfl⟩ : syracuseStep 3191741 = 1196903) (by norm_num)
theorem B2127827 : Blo 2127435 2127827 := bstep (se 1 (by rfl) ⟨1595870, by rfl⟩ : syracuseStep 2127827 = 3191741) B3191741
theorem B4787621 : Blo 2127435 4787621 := bbase (se 4 (by rfl) ⟨448839, by rfl⟩ : syracuseStep 4787621 = 897679) (by norm_num)
theorem B3191747 : Blo 2127435 3191747 := bstep (se 1 (by rfl) ⟨2393810, by rfl⟩ : syracuseStep 3191747 = 4787621) B4787621
theorem B2127831 : Blo 2127435 2127831 := bstep (se 1 (by rfl) ⟨1595873, by rfl⟩ : syracuseStep 2127831 = 3191747) B3191747
theorem B5386085 : Blo 2127435 5386085 := bbase (se 4 (by rfl) ⟨504945, by rfl⟩ : syracuseStep 5386085 = 1009891) (by norm_num)
theorem B3590723 : Blo 2127435 3590723 := bstep (se 1 (by rfl) ⟨2693042, by rfl⟩ : syracuseStep 3590723 = 5386085) B5386085
theorem B2393815 : Blo 2127435 2393815 := bstep (se 1 (by rfl) ⟨1795361, by rfl⟩ : syracuseStep 2393815 = 3590723) B3590723
theorem B3191753 : Blo 2127435 3191753 := bstep (se 2 (by rfl) ⟨1196907, by rfl⟩ : syracuseStep 3191753 = 2393815) B2393815
theorem B2127835 : Blo 2127435 2127835 := bstep (se 1 (by rfl) ⟨1595876, by rfl⟩ : syracuseStep 2127835 = 3191753) B3191753
theorem B3408389 : Blo 2127435 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B2272259 : Blo 2127435 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B6059357 : Blo 2127435 6059357 := bstep (se 3 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 6059357 = 2272259) B2272259
theorem B4039571 : Blo 2127435 4039571 := bstep (se 1 (by rfl) ⟨3029678, by rfl⟩ : syracuseStep 4039571 = 6059357) B6059357
theorem B10772189 : Blo 2127435 10772189 := bstep (se 3 (by rfl) ⟨2019785, by rfl⟩ : syracuseStep 10772189 = 4039571) B4039571
theorem B7181459 : Blo 2127435 7181459 := bstep (se 1 (by rfl) ⟨5386094, by rfl⟩ : syracuseStep 7181459 = 10772189) B10772189
theorem B4787639 : Blo 2127435 4787639 := bstep (se 1 (by rfl) ⟨3590729, by rfl⟩ : syracuseStep 4787639 = 7181459) B7181459
theorem B3191759 : Blo 2127435 3191759 := bstep (se 1 (by rfl) ⟨2393819, by rfl⟩ : syracuseStep 3191759 = 4787639) B4787639
theorem B2127839 : Blo 2127435 2127839 := bstep (se 1 (by rfl) ⟨1595879, by rfl⟩ : syracuseStep 2127839 = 3191759) B3191759
theorem B3191765 : Blo 2127435 3191765 := bbase (se 7 (by rfl) ⟨37403, by rfl⟩ : syracuseStep 3191765 = 74807) (by norm_num)
theorem B2127843 : Blo 2127435 2127843 := bstep (se 1 (by rfl) ⟨1595882, by rfl⟩ : syracuseStep 2127843 = 3191765) B3191765
theorem B8079173 : Blo 2127435 8079173 := bbase (se 4 (by rfl) ⟨757422, by rfl⟩ : syracuseStep 8079173 = 1514845) (by norm_num)
theorem B5386115 : Blo 2127435 5386115 := bstep (se 1 (by rfl) ⟨4039586, by rfl⟩ : syracuseStep 5386115 = 8079173) B8079173
theorem B3590743 : Blo 2127435 3590743 := bstep (se 1 (by rfl) ⟨2693057, by rfl⟩ : syracuseStep 3590743 = 5386115) B5386115
theorem B4787657 : Blo 2127435 4787657 := bstep (se 2 (by rfl) ⟨1795371, by rfl⟩ : syracuseStep 4787657 = 3590743) B3590743
theorem B3191771 : Blo 2127435 3191771 := bstep (se 1 (by rfl) ⟨2393828, by rfl⟩ : syracuseStep 3191771 = 4787657) B4787657
theorem B2127847 : Blo 2127435 2127847 := bstep (se 1 (by rfl) ⟨1595885, by rfl⟩ : syracuseStep 2127847 = 3191771) B3191771
theorem B2393833 : Blo 2127435 2393833 := bbase (se 2 (by rfl) ⟨897687, by rfl⟩ : syracuseStep 2393833 = 1795375) (by norm_num)
theorem B3191777 : Blo 2127435 3191777 := bstep (se 2 (by rfl) ⟨1196916, by rfl⟩ : syracuseStep 3191777 = 2393833) B2393833
theorem B2127851 : Blo 2127435 2127851 := bstep (se 1 (by rfl) ⟨1595888, by rfl⟩ : syracuseStep 2127851 = 3191777) B3191777
theorem B12118805 : Blo 2127435 12118805 := bbase (se 6 (by rfl) ⟨284034, by rfl⟩ : syracuseStep 12118805 = 568069) (by norm_num)
theorem B8079203 : Blo 2127435 8079203 := bstep (se 1 (by rfl) ⟨6059402, by rfl⟩ : syracuseStep 8079203 = 12118805) B12118805
theorem B5386135 : Blo 2127435 5386135 := bstep (se 1 (by rfl) ⟨4039601, by rfl⟩ : syracuseStep 5386135 = 8079203) B8079203
theorem B7181513 : Blo 2127435 7181513 := bstep (se 2 (by rfl) ⟨2693067, by rfl⟩ : syracuseStep 7181513 = 5386135) B5386135
theorem B4787675 : Blo 2127435 4787675 := bstep (se 1 (by rfl) ⟨3590756, by rfl⟩ : syracuseStep 4787675 = 7181513) B7181513
theorem B3191783 : Blo 2127435 3191783 := bstep (se 1 (by rfl) ⟨2393837, by rfl⟩ : syracuseStep 3191783 = 4787675) B4787675
theorem B2127855 : Blo 2127435 2127855 := bstep (se 1 (by rfl) ⟨1595891, by rfl⟩ : syracuseStep 2127855 = 3191783) B3191783
theorem B3191789 : Blo 2127435 3191789 := bbase (se 3 (by rfl) ⟨598460, by rfl⟩ : syracuseStep 3191789 = 1196921) (by norm_num)
theorem B2127859 : Blo 2127435 2127859 := bstep (se 1 (by rfl) ⟨1595894, by rfl⟩ : syracuseStep 2127859 = 3191789) B3191789
theorem B4787693 : Blo 2127435 4787693 := bbase (se 3 (by rfl) ⟨897692, by rfl⟩ : syracuseStep 4787693 = 1795385) (by norm_num)
theorem B3191795 : Blo 2127435 3191795 := bstep (se 1 (by rfl) ⟨2393846, by rfl⟩ : syracuseStep 3191795 = 4787693) B4787693
theorem B2127863 : Blo 2127435 2127863 := bstep (se 1 (by rfl) ⟨1595897, by rfl⟩ : syracuseStep 2127863 = 3191795) B3191795
theorem B6816869 : Blo 2127435 6816869 := bbase (se 4 (by rfl) ⟨639081, by rfl⟩ : syracuseStep 6816869 = 1278163) (by norm_num)
theorem B4544579 : Blo 2127435 4544579 := bstep (se 1 (by rfl) ⟨3408434, by rfl⟩ : syracuseStep 4544579 = 6816869) B6816869
theorem B3029719 : Blo 2127435 3029719 := bstep (se 1 (by rfl) ⟨2272289, by rfl⟩ : syracuseStep 3029719 = 4544579) B4544579
theorem B4039625 : Blo 2127435 4039625 := bstep (se 2 (by rfl) ⟨1514859, by rfl⟩ : syracuseStep 4039625 = 3029719) B3029719
theorem B2693083 : Blo 2127435 2693083 := bstep (se 1 (by rfl) ⟨2019812, by rfl⟩ : syracuseStep 2693083 = 4039625) B4039625
theorem B3590777 : Blo 2127435 3590777 := bstep (se 2 (by rfl) ⟨1346541, by rfl⟩ : syracuseStep 3590777 = 2693083) B2693083
theorem B2393851 : Blo 2127435 2393851 := bstep (se 1 (by rfl) ⟨1795388, by rfl⟩ : syracuseStep 2393851 = 3590777) B3590777
theorem B3191801 : Blo 2127435 3191801 := bstep (se 2 (by rfl) ⟨1196925, by rfl⟩ : syracuseStep 3191801 = 2393851) B2393851
theorem B2127867 : Blo 2127435 2127867 := bstep (se 1 (by rfl) ⟨1595900, by rfl⟩ : syracuseStep 2127867 = 3191801) B3191801
theorem B4150613 : Blo 2127435 4150613 := bbase (se 17 (by rfl) ⟨47, by rfl⟩ : syracuseStep 4150613 = 95) (by norm_num)
theorem B11068301 : Blo 2127435 11068301 := bstep (se 3 (by rfl) ⟨2075306, by rfl⟩ : syracuseStep 11068301 = 4150613) B4150613
theorem B7378867 : Blo 2127435 7378867 := bstep (se 1 (by rfl) ⟨5534150, by rfl⟩ : syracuseStep 7378867 = 11068301) B11068301
theorem B39353957 : Blo 2127435 39353957 := bstep (se 4 (by rfl) ⟨3689433, by rfl⟩ : syracuseStep 39353957 = 7378867) B7378867
theorem B26235971 : Blo 2127435 26235971 := bstep (se 1 (by rfl) ⟨19676978, by rfl⟩ : syracuseStep 26235971 = 39353957) B39353957
theorem B17490647 : Blo 2127435 17490647 := bstep (se 1 (by rfl) ⟨13117985, by rfl⟩ : syracuseStep 17490647 = 26235971) B26235971
theorem B11660431 : Blo 2127435 11660431 := bstep (se 1 (by rfl) ⟨8745323, by rfl⟩ : syracuseStep 11660431 = 17490647) B17490647
theorem B15547241 : Blo 2127435 15547241 := bstep (se 2 (by rfl) ⟨5830215, by rfl⟩ : syracuseStep 15547241 = 11660431) B11660431
theorem B41459309 : Blo 2127435 41459309 := bstep (se 3 (by rfl) ⟨7773620, by rfl⟩ : syracuseStep 41459309 = 15547241) B15547241
theorem B27639539 : Blo 2127435 27639539 := bstep (se 1 (by rfl) ⟨20729654, by rfl⟩ : syracuseStep 27639539 = 41459309) B41459309
theorem B18426359 : Blo 2127435 18426359 := bstep (se 1 (by rfl) ⟨13819769, by rfl⟩ : syracuseStep 18426359 = 27639539) B27639539
theorem B12284239 : Blo 2127435 12284239 := bstep (se 1 (by rfl) ⟨9213179, by rfl⟩ : syracuseStep 12284239 = 18426359) B18426359
theorem B16378985 : Blo 2127435 16378985 := bstep (se 2 (by rfl) ⟨6142119, by rfl⟩ : syracuseStep 16378985 = 12284239) B12284239
theorem B10919323 : Blo 2127435 10919323 := bstep (se 1 (by rfl) ⟨8189492, by rfl⟩ : syracuseStep 10919323 = 16378985) B16378985
theorem B14559097 : Blo 2127435 14559097 := bstep (se 2 (by rfl) ⟨5459661, by rfl⟩ : syracuseStep 14559097 = 10919323) B10919323
theorem B19412129 : Blo 2127435 19412129 := bstep (se 2 (by rfl) ⟨7279548, by rfl⟩ : syracuseStep 19412129 = 14559097) B14559097
theorem B12941419 : Blo 2127435 12941419 := bstep (se 1 (by rfl) ⟨9706064, by rfl⟩ : syracuseStep 12941419 = 19412129) B19412129
theorem B17255225 : Blo 2127435 17255225 := bstep (se 2 (by rfl) ⟨6470709, by rfl⟩ : syracuseStep 17255225 = 12941419) B12941419
theorem B46013933 : Blo 2127435 46013933 := bstep (se 3 (by rfl) ⟨8627612, by rfl⟩ : syracuseStep 46013933 = 17255225) B17255225
theorem B122703821 : Blo 2127435 122703821 := bstep (se 3 (by rfl) ⟨23006966, by rfl⟩ : syracuseStep 122703821 = 46013933) B46013933
theorem B81802547 : Blo 2127435 81802547 := bstep (se 1 (by rfl) ⟨61351910, by rfl⟩ : syracuseStep 81802547 = 122703821) B122703821
theorem B54535031 : Blo 2127435 54535031 := bstep (se 1 (by rfl) ⟨40901273, by rfl⟩ : syracuseStep 54535031 = 81802547) B81802547
theorem B36356687 : Blo 2127435 36356687 := bstep (se 1 (by rfl) ⟨27267515, by rfl⟩ : syracuseStep 36356687 = 54535031) B54535031
theorem B24237791 : Blo 2127435 24237791 := bstep (se 1 (by rfl) ⟨18178343, by rfl⟩ : syracuseStep 24237791 = 36356687) B36356687
theorem B16158527 : Blo 2127435 16158527 := bstep (se 1 (by rfl) ⟨12118895, by rfl⟩ : syracuseStep 16158527 = 24237791) B24237791
theorem B10772351 : Blo 2127435 10772351 := bstep (se 1 (by rfl) ⟨8079263, by rfl⟩ : syracuseStep 10772351 = 16158527) B16158527
theorem B7181567 : Blo 2127435 7181567 := bstep (se 1 (by rfl) ⟨5386175, by rfl⟩ : syracuseStep 7181567 = 10772351) B10772351
theorem B4787711 : Blo 2127435 4787711 := bstep (se 1 (by rfl) ⟨3590783, by rfl⟩ : syracuseStep 4787711 = 7181567) B7181567
theorem B3191807 : Blo 2127435 3191807 := bstep (se 1 (by rfl) ⟨2393855, by rfl⟩ : syracuseStep 3191807 = 4787711) B4787711
theorem B2127871 : Blo 2127435 2127871 := bstep (se 1 (by rfl) ⟨1595903, by rfl⟩ : syracuseStep 2127871 = 3191807) B3191807
theorem B3191813 : Blo 2127435 3191813 := bbase (se 4 (by rfl) ⟨299232, by rfl⟩ : syracuseStep 3191813 = 598465) (by norm_num)
theorem B2127875 : Blo 2127435 2127875 := bstep (se 1 (by rfl) ⟨1595906, by rfl⟩ : syracuseStep 2127875 = 3191813) B3191813
theorem B3590797 : Blo 2127435 3590797 := bbase (se 3 (by rfl) ⟨673274, by rfl⟩ : syracuseStep 3590797 = 1346549) (by norm_num)
theorem B4787729 : Blo 2127435 4787729 := bstep (se 2 (by rfl) ⟨1795398, by rfl⟩ : syracuseStep 4787729 = 3590797) B3590797
theorem B3191819 : Blo 2127435 3191819 := bstep (se 1 (by rfl) ⟨2393864, by rfl⟩ : syracuseStep 3191819 = 4787729) B4787729
theorem B2127879 : Blo 2127435 2127879 := bstep (se 1 (by rfl) ⟨1595909, by rfl⟩ : syracuseStep 2127879 = 3191819) B3191819
theorem B2393869 : Blo 2127435 2393869 := bbase (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) (by norm_num)
theorem B3191825 : Blo 2127435 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B2127883 : Blo 2127435 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B7181621 : Blo 2127435 7181621 := bbase (se 5 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 7181621 = 673277) (by norm_num)
theorem B4787747 : Blo 2127435 4787747 := bstep (se 1 (by rfl) ⟨3590810, by rfl⟩ : syracuseStep 4787747 = 7181621) B7181621
theorem B3191831 : Blo 2127435 3191831 := bstep (se 1 (by rfl) ⟨2393873, by rfl⟩ : syracuseStep 3191831 = 4787747) B4787747
theorem B2127887 : Blo 2127435 2127887 := bstep (se 1 (by rfl) ⟨1595915, by rfl⟩ : syracuseStep 2127887 = 3191831) B3191831
theorem B3191837 : Blo 2127435 3191837 := bbase (se 3 (by rfl) ⟨598469, by rfl⟩ : syracuseStep 3191837 = 1196939) (by norm_num)
theorem B2127891 : Blo 2127435 2127891 := bstep (se 1 (by rfl) ⟨1595918, by rfl⟩ : syracuseStep 2127891 = 3191837) B3191837
theorem B4787765 : Blo 2127435 4787765 := bbase (se 5 (by rfl) ⟨224426, by rfl⟩ : syracuseStep 4787765 = 448853) (by norm_num)
theorem B3191843 : Blo 2127435 3191843 := bstep (se 1 (by rfl) ⟨2393882, by rfl⟩ : syracuseStep 3191843 = 4787765) B4787765
theorem B2127895 : Blo 2127435 2127895 := bstep (se 1 (by rfl) ⟨1595921, by rfl⟩ : syracuseStep 2127895 = 3191843) B3191843
theorem B3408485 : Blo 2127435 3408485 := bbase (se 4 (by rfl) ⟨319545, by rfl⟩ : syracuseStep 3408485 = 639091) (by norm_num)
theorem B9089293 : Blo 2127435 9089293 := bstep (se 3 (by rfl) ⟨1704242, by rfl⟩ : syracuseStep 9089293 = 3408485) B3408485
theorem B12119057 : Blo 2127435 12119057 := bstep (se 2 (by rfl) ⟨4544646, by rfl⟩ : syracuseStep 12119057 = 9089293) B9089293
theorem B8079371 : Blo 2127435 8079371 := bstep (se 1 (by rfl) ⟨6059528, by rfl⟩ : syracuseStep 8079371 = 12119057) B12119057
theorem B5386247 : Blo 2127435 5386247 := bstep (se 1 (by rfl) ⟨4039685, by rfl⟩ : syracuseStep 5386247 = 8079371) B8079371
theorem B3590831 : Blo 2127435 3590831 := bstep (se 1 (by rfl) ⟨2693123, by rfl⟩ : syracuseStep 3590831 = 5386247) B5386247
theorem B2393887 : Blo 2127435 2393887 := bstep (se 1 (by rfl) ⟨1795415, by rfl⟩ : syracuseStep 2393887 = 3590831) B3590831
theorem B3191849 : Blo 2127435 3191849 := bstep (se 2 (by rfl) ⟨1196943, by rfl⟩ : syracuseStep 3191849 = 2393887) B2393887
theorem B2127899 : Blo 2127435 2127899 := bstep (se 1 (by rfl) ⟨1595924, by rfl⟩ : syracuseStep 2127899 = 3191849) B3191849
theorem B3235405 : Blo 2127435 3235405 := bbase (se 3 (by rfl) ⟨606638, by rfl⟩ : syracuseStep 3235405 = 1213277) (by norm_num)
theorem B4313873 : Blo 2127435 4313873 := bstep (se 2 (by rfl) ⟨1617702, by rfl⟩ : syracuseStep 4313873 = 3235405) B3235405
theorem B2875915 : Blo 2127435 2875915 := bstep (se 1 (by rfl) ⟨2156936, by rfl⟩ : syracuseStep 2875915 = 4313873) B4313873
theorem B3834553 : Blo 2127435 3834553 := bstep (se 2 (by rfl) ⟨1437957, by rfl⟩ : syracuseStep 3834553 = 2875915) B2875915
theorem B5112737 : Blo 2127435 5112737 := bstep (se 2 (by rfl) ⟨1917276, by rfl⟩ : syracuseStep 5112737 = 3834553) B3834553
theorem B3408491 : Blo 2127435 3408491 := bstep (se 1 (by rfl) ⟨2556368, by rfl⟩ : syracuseStep 3408491 = 5112737) B5112737
theorem B9089309 : Blo 2127435 9089309 := bstep (se 3 (by rfl) ⟨1704245, by rfl⟩ : syracuseStep 9089309 = 3408491) B3408491
theorem B6059539 : Blo 2127435 6059539 := bstep (se 1 (by rfl) ⟨4544654, by rfl⟩ : syracuseStep 6059539 = 9089309) B9089309
theorem B8079385 : Blo 2127435 8079385 := bstep (se 2 (by rfl) ⟨3029769, by rfl⟩ : syracuseStep 8079385 = 6059539) B6059539
theorem B10772513 : Blo 2127435 10772513 := bstep (se 2 (by rfl) ⟨4039692, by rfl⟩ : syracuseStep 10772513 = 8079385) B8079385
theorem B7181675 : Blo 2127435 7181675 := bstep (se 1 (by rfl) ⟨5386256, by rfl⟩ : syracuseStep 7181675 = 10772513) B10772513
theorem B4787783 : Blo 2127435 4787783 := bstep (se 1 (by rfl) ⟨3590837, by rfl⟩ : syracuseStep 4787783 = 7181675) B7181675
theorem B3191855 : Blo 2127435 3191855 := bstep (se 1 (by rfl) ⟨2393891, by rfl⟩ : syracuseStep 3191855 = 4787783) B4787783
theorem B2127903 : Blo 2127435 2127903 := bstep (se 1 (by rfl) ⟨1595927, by rfl⟩ : syracuseStep 2127903 = 3191855) B3191855
theorem B3191861 : Blo 2127435 3191861 := bbase (se 5 (by rfl) ⟨149618, by rfl⟩ : syracuseStep 3191861 = 299237) (by norm_num)
theorem B2127907 : Blo 2127435 2127907 := bstep (se 1 (by rfl) ⟨1595930, by rfl⟩ : syracuseStep 2127907 = 3191861) B3191861
theorem B5386277 : Blo 2127435 5386277 := bbase (se 4 (by rfl) ⟨504963, by rfl⟩ : syracuseStep 5386277 = 1009927) (by norm_num)
theorem B3590851 : Blo 2127435 3590851 := bstep (se 1 (by rfl) ⟨2693138, by rfl⟩ : syracuseStep 3590851 = 5386277) B5386277
theorem B4787801 : Blo 2127435 4787801 := bstep (se 2 (by rfl) ⟨1795425, by rfl⟩ : syracuseStep 4787801 = 3590851) B3590851
theorem B3191867 : Blo 2127435 3191867 := bstep (se 1 (by rfl) ⟨2393900, by rfl⟩ : syracuseStep 3191867 = 4787801) B4787801
theorem B2127911 : Blo 2127435 2127911 := bstep (se 1 (by rfl) ⟨1595933, by rfl⟩ : syracuseStep 2127911 = 3191867) B3191867
theorem B2393905 : Blo 2127435 2393905 := bbase (se 2 (by rfl) ⟨897714, by rfl⟩ : syracuseStep 2393905 = 1795429) (by norm_num)
theorem B3191873 : Blo 2127435 3191873 := bstep (se 2 (by rfl) ⟨1196952, by rfl⟩ : syracuseStep 3191873 = 2393905) B2393905
theorem B2127915 : Blo 2127435 2127915 := bstep (se 1 (by rfl) ⟨1595936, by rfl⟩ : syracuseStep 2127915 = 3191873) B3191873
theorem B3408517 : Blo 2127435 3408517 := bbase (se 4 (by rfl) ⟨319548, by rfl⟩ : syracuseStep 3408517 = 639097) (by norm_num)
theorem B4544689 : Blo 2127435 4544689 := bstep (se 2 (by rfl) ⟨1704258, by rfl⟩ : syracuseStep 4544689 = 3408517) B3408517
theorem B6059585 : Blo 2127435 6059585 := bstep (se 2 (by rfl) ⟨2272344, by rfl⟩ : syracuseStep 6059585 = 4544689) B4544689
theorem B4039723 : Blo 2127435 4039723 := bstep (se 1 (by rfl) ⟨3029792, by rfl⟩ : syracuseStep 4039723 = 6059585) B6059585
theorem B5386297 : Blo 2127435 5386297 := bstep (se 2 (by rfl) ⟨2019861, by rfl⟩ : syracuseStep 5386297 = 4039723) B4039723
theorem B7181729 : Blo 2127435 7181729 := bstep (se 2 (by rfl) ⟨2693148, by rfl⟩ : syracuseStep 7181729 = 5386297) B5386297
theorem B4787819 : Blo 2127435 4787819 := bstep (se 1 (by rfl) ⟨3590864, by rfl⟩ : syracuseStep 4787819 = 7181729) B7181729
theorem B3191879 : Blo 2127435 3191879 := bstep (se 1 (by rfl) ⟨2393909, by rfl⟩ : syracuseStep 3191879 = 4787819) B4787819
theorem B2127919 : Blo 2127435 2127919 := bstep (se 1 (by rfl) ⟨1595939, by rfl⟩ : syracuseStep 2127919 = 3191879) B3191879
theorem B3191885 : Blo 2127435 3191885 := bbase (se 3 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 3191885 = 1196957) (by norm_num)
theorem B2127923 : Blo 2127435 2127923 := bstep (se 1 (by rfl) ⟨1595942, by rfl⟩ : syracuseStep 2127923 = 3191885) B3191885
theorem B4787837 : Blo 2127435 4787837 := bbase (se 3 (by rfl) ⟨897719, by rfl⟩ : syracuseStep 4787837 = 1795439) (by norm_num)
theorem B3191891 : Blo 2127435 3191891 := bstep (se 1 (by rfl) ⟨2393918, by rfl⟩ : syracuseStep 3191891 = 4787837) B4787837
theorem B2127927 : Blo 2127435 2127927 := bstep (se 1 (by rfl) ⟨1595945, by rfl⟩ : syracuseStep 2127927 = 3191891) B3191891
theorem B3590885 : Blo 2127435 3590885 := bbase (se 4 (by rfl) ⟨336645, by rfl⟩ : syracuseStep 3590885 = 673291) (by norm_num)
theorem B2393923 : Blo 2127435 2393923 := bstep (se 1 (by rfl) ⟨1795442, by rfl⟩ : syracuseStep 2393923 = 3590885) B3590885
theorem B3191897 : Blo 2127435 3191897 := bstep (se 2 (by rfl) ⟨1196961, by rfl⟩ : syracuseStep 3191897 = 2393923) B2393923
theorem B2127931 : Blo 2127435 2127931 := bstep (se 1 (by rfl) ⟨1595948, by rfl⟩ : syracuseStep 2127931 = 3191897) B3191897
theorem B2156969 : Blo 2127435 2156969 := bbase (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) (by norm_num)
theorem B5751917 : Blo 2127435 5751917 := bstep (se 3 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 5751917 = 2156969) B2156969
theorem B3834611 : Blo 2127435 3834611 := bstep (se 1 (by rfl) ⟨2875958, by rfl⟩ : syracuseStep 3834611 = 5751917) B5751917
theorem B2556407 : Blo 2127435 2556407 := bstep (se 1 (by rfl) ⟨1917305, by rfl⟩ : syracuseStep 2556407 = 3834611) B3834611
theorem B6817085 : Blo 2127435 6817085 := bstep (se 3 (by rfl) ⟨1278203, by rfl⟩ : syracuseStep 6817085 = 2556407) B2556407
theorem B4544723 : Blo 2127435 4544723 := bstep (se 1 (by rfl) ⟨3408542, by rfl⟩ : syracuseStep 4544723 = 6817085) B6817085
theorem B3029815 : Blo 2127435 3029815 := bstep (se 1 (by rfl) ⟨2272361, by rfl⟩ : syracuseStep 3029815 = 4544723) B4544723
theorem B16159013 : Blo 2127435 16159013 := bstep (se 4 (by rfl) ⟨1514907, by rfl⟩ : syracuseStep 16159013 = 3029815) B3029815
theorem B10772675 : Blo 2127435 10772675 := bstep (se 1 (by rfl) ⟨8079506, by rfl⟩ : syracuseStep 10772675 = 16159013) B16159013
theorem B7181783 : Blo 2127435 7181783 := bstep (se 1 (by rfl) ⟨5386337, by rfl⟩ : syracuseStep 7181783 = 10772675) B10772675
theorem B4787855 : Blo 2127435 4787855 := bstep (se 1 (by rfl) ⟨3590891, by rfl⟩ : syracuseStep 4787855 = 7181783) B7181783
theorem B3191903 : Blo 2127435 3191903 := bstep (se 1 (by rfl) ⟨2393927, by rfl⟩ : syracuseStep 3191903 = 4787855) B4787855
theorem B2127935 : Blo 2127435 2127935 := bstep (se 1 (by rfl) ⟨1595951, by rfl⟩ : syracuseStep 2127935 = 3191903) B3191903
theorem B3191909 : Blo 2127435 3191909 := bbase (se 4 (by rfl) ⟨299241, by rfl⟩ : syracuseStep 3191909 = 598483) (by norm_num)
theorem B2127939 : Blo 2127435 2127939 := bstep (se 1 (by rfl) ⟨1595954, by rfl⟩ : syracuseStep 2127939 = 3191909) B3191909
theorem B4544741 : Blo 2127435 4544741 := bbase (se 4 (by rfl) ⟨426069, by rfl⟩ : syracuseStep 4544741 = 852139) (by norm_num)
theorem B3029827 : Blo 2127435 3029827 := bstep (se 1 (by rfl) ⟨2272370, by rfl⟩ : syracuseStep 3029827 = 4544741) B4544741
theorem B4039769 : Blo 2127435 4039769 := bstep (se 2 (by rfl) ⟨1514913, by rfl⟩ : syracuseStep 4039769 = 3029827) B3029827
theorem B2693179 : Blo 2127435 2693179 := bstep (se 1 (by rfl) ⟨2019884, by rfl⟩ : syracuseStep 2693179 = 4039769) B4039769
theorem B3590905 : Blo 2127435 3590905 := bstep (se 2 (by rfl) ⟨1346589, by rfl⟩ : syracuseStep 3590905 = 2693179) B2693179
theorem B4787873 : Blo 2127435 4787873 := bstep (se 2 (by rfl) ⟨1795452, by rfl⟩ : syracuseStep 4787873 = 3590905) B3590905
theorem B3191915 : Blo 2127435 3191915 := bstep (se 1 (by rfl) ⟨2393936, by rfl⟩ : syracuseStep 3191915 = 4787873) B4787873
theorem B2127943 : Blo 2127435 2127943 := bstep (se 1 (by rfl) ⟨1595957, by rfl⟩ : syracuseStep 2127943 = 3191915) B3191915
theorem B2393941 : Blo 2127435 2393941 := bbase (se 9 (by rfl) ⟨7013, by rfl⟩ : syracuseStep 2393941 = 14027) (by norm_num)
theorem B3191921 : Blo 2127435 3191921 := bstep (se 2 (by rfl) ⟨1196970, by rfl⟩ : syracuseStep 3191921 = 2393941) B2393941
theorem B2127947 : Blo 2127435 2127947 := bstep (se 1 (by rfl) ⟨1595960, by rfl⟩ : syracuseStep 2127947 = 3191921) B3191921
theorem B2693189 : Blo 2127435 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B7181837 : Blo 2127435 7181837 := bstep (se 3 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 7181837 = 2693189) B2693189
theorem B4787891 : Blo 2127435 4787891 := bstep (se 1 (by rfl) ⟨3590918, by rfl⟩ : syracuseStep 4787891 = 7181837) B7181837
theorem B3191927 : Blo 2127435 3191927 := bstep (se 1 (by rfl) ⟨2393945, by rfl⟩ : syracuseStep 3191927 = 4787891) B4787891
theorem B2127951 : Blo 2127435 2127951 := bstep (se 1 (by rfl) ⟨1595963, by rfl⟩ : syracuseStep 2127951 = 3191927) B3191927
theorem B3191933 : Blo 2127435 3191933 := bbase (se 3 (by rfl) ⟨598487, by rfl⟩ : syracuseStep 3191933 = 1196975) (by norm_num)
theorem B2127955 : Blo 2127435 2127955 := bstep (se 1 (by rfl) ⟨1595966, by rfl⟩ : syracuseStep 2127955 = 3191933) B3191933
theorem B4787909 : Blo 2127435 4787909 := bbase (se 4 (by rfl) ⟨448866, by rfl⟩ : syracuseStep 4787909 = 897733) (by norm_num)
theorem B3191939 : Blo 2127435 3191939 := bstep (se 1 (by rfl) ⟨2393954, by rfl⟩ : syracuseStep 3191939 = 4787909) B4787909
theorem B2127959 : Blo 2127435 2127959 := bstep (se 1 (by rfl) ⟨1595969, by rfl⟩ : syracuseStep 2127959 = 3191939) B3191939
theorem B3455093 : Blo 2127435 3455093 := bbase (se 5 (by rfl) ⟨161957, by rfl⟩ : syracuseStep 3455093 = 323915) (by norm_num)
theorem B9213581 : Blo 2127435 9213581 := bstep (se 3 (by rfl) ⟨1727546, by rfl⟩ : syracuseStep 9213581 = 3455093) B3455093
theorem B6142387 : Blo 2127435 6142387 := bstep (se 1 (by rfl) ⟨4606790, by rfl⟩ : syracuseStep 6142387 = 9213581) B9213581
theorem B8189849 : Blo 2127435 8189849 := bstep (se 2 (by rfl) ⟨3071193, by rfl⟩ : syracuseStep 8189849 = 6142387) B6142387
theorem B21839597 : Blo 2127435 21839597 := bstep (se 3 (by rfl) ⟨4094924, by rfl⟩ : syracuseStep 21839597 = 8189849) B8189849
theorem B14559731 : Blo 2127435 14559731 := bstep (se 1 (by rfl) ⟨10919798, by rfl⟩ : syracuseStep 14559731 = 21839597) B21839597
theorem B9706487 : Blo 2127435 9706487 := bstep (se 1 (by rfl) ⟨7279865, by rfl⟩ : syracuseStep 9706487 = 14559731) B14559731
theorem B25883965 : Blo 2127435 25883965 := bstep (se 3 (by rfl) ⟨4853243, by rfl⟩ : syracuseStep 25883965 = 9706487) B9706487
theorem B34511953 : Blo 2127435 34511953 := bstep (se 2 (by rfl) ⟨12941982, by rfl⟩ : syracuseStep 34511953 = 25883965) B25883965
theorem B46015937 : Blo 2127435 46015937 := bstep (se 2 (by rfl) ⟨17255976, by rfl⟩ : syracuseStep 46015937 = 34511953) B34511953
theorem B30677291 : Blo 2127435 30677291 := bstep (se 1 (by rfl) ⟨23007968, by rfl⟩ : syracuseStep 30677291 = 46015937) B46015937
theorem B20451527 : Blo 2127435 20451527 := bstep (se 1 (by rfl) ⟨15338645, by rfl⟩ : syracuseStep 20451527 = 30677291) B30677291
theorem B13634351 : Blo 2127435 13634351 := bstep (se 1 (by rfl) ⟨10225763, by rfl⟩ : syracuseStep 13634351 = 20451527) B20451527
theorem B9089567 : Blo 2127435 9089567 := bstep (se 1 (by rfl) ⟨6817175, by rfl⟩ : syracuseStep 9089567 = 13634351) B13634351
theorem B6059711 : Blo 2127435 6059711 := bstep (se 1 (by rfl) ⟨4544783, by rfl⟩ : syracuseStep 6059711 = 9089567) B9089567
theorem B4039807 : Blo 2127435 4039807 := bstep (se 1 (by rfl) ⟨3029855, by rfl⟩ : syracuseStep 4039807 = 6059711) B6059711
theorem B5386409 : Blo 2127435 5386409 := bstep (se 2 (by rfl) ⟨2019903, by rfl⟩ : syracuseStep 5386409 = 4039807) B4039807
theorem B3590939 : Blo 2127435 3590939 := bstep (se 1 (by rfl) ⟨2693204, by rfl⟩ : syracuseStep 3590939 = 5386409) B5386409
theorem B2393959 : Blo 2127435 2393959 := bstep (se 1 (by rfl) ⟨1795469, by rfl⟩ : syracuseStep 2393959 = 3590939) B3590939
theorem B3191945 : Blo 2127435 3191945 := bstep (se 2 (by rfl) ⟨1196979, by rfl⟩ : syracuseStep 3191945 = 2393959) B2393959
theorem B2127963 : Blo 2127435 2127963 := bstep (se 1 (by rfl) ⟨1595972, by rfl⟩ : syracuseStep 2127963 = 3191945) B3191945
theorem B10772837 : Blo 2127435 10772837 := bbase (se 4 (by rfl) ⟨1009953, by rfl⟩ : syracuseStep 10772837 = 2019907) (by norm_num)
theorem B7181891 : Blo 2127435 7181891 := bstep (se 1 (by rfl) ⟨5386418, by rfl⟩ : syracuseStep 7181891 = 10772837) B10772837
theorem B4787927 : Blo 2127435 4787927 := bstep (se 1 (by rfl) ⟨3590945, by rfl⟩ : syracuseStep 4787927 = 7181891) B7181891
theorem B3191951 : Blo 2127435 3191951 := bstep (se 1 (by rfl) ⟨2393963, by rfl⟩ : syracuseStep 3191951 = 4787927) B4787927
theorem B2127967 : Blo 2127435 2127967 := bstep (se 1 (by rfl) ⟨1595975, by rfl⟩ : syracuseStep 2127967 = 3191951) B3191951
theorem B3191957 : Blo 2127435 3191957 := bbase (se 6 (by rfl) ⟨74811, by rfl⟩ : syracuseStep 3191957 = 149623) (by norm_num)
theorem B2127971 : Blo 2127435 2127971 := bstep (se 1 (by rfl) ⟨1595978, by rfl⟩ : syracuseStep 2127971 = 3191957) B3191957
theorem B6471029 : Blo 2127435 6471029 := bbase (se 5 (by rfl) ⟨303329, by rfl⟩ : syracuseStep 6471029 = 606659) (by norm_num)
theorem B4314019 : Blo 2127435 4314019 := bstep (se 1 (by rfl) ⟨3235514, by rfl⟩ : syracuseStep 4314019 = 6471029) B6471029
theorem B5752025 : Blo 2127435 5752025 := bstep (se 2 (by rfl) ⟨2157009, by rfl⟩ : syracuseStep 5752025 = 4314019) B4314019
theorem B3834683 : Blo 2127435 3834683 := bstep (se 1 (by rfl) ⟨2876012, by rfl⟩ : syracuseStep 3834683 = 5752025) B5752025
theorem B2556455 : Blo 2127435 2556455 := bstep (se 1 (by rfl) ⟨1917341, by rfl⟩ : syracuseStep 2556455 = 3834683) B3834683
theorem B6817213 : Blo 2127435 6817213 := bstep (se 3 (by rfl) ⟨1278227, by rfl⟩ : syracuseStep 6817213 = 2556455) B2556455
theorem B9089617 : Blo 2127435 9089617 := bstep (se 2 (by rfl) ⟨3408606, by rfl⟩ : syracuseStep 9089617 = 6817213) B6817213
theorem B12119489 : Blo 2127435 12119489 := bstep (se 2 (by rfl) ⟨4544808, by rfl⟩ : syracuseStep 12119489 = 9089617) B9089617
theorem B8079659 : Blo 2127435 8079659 := bstep (se 1 (by rfl) ⟨6059744, by rfl⟩ : syracuseStep 8079659 = 12119489) B12119489
theorem B5386439 : Blo 2127435 5386439 := bstep (se 1 (by rfl) ⟨4039829, by rfl⟩ : syracuseStep 5386439 = 8079659) B8079659
theorem B3590959 : Blo 2127435 3590959 := bstep (se 1 (by rfl) ⟨2693219, by rfl⟩ : syracuseStep 3590959 = 5386439) B5386439
theorem B4787945 : Blo 2127435 4787945 := bstep (se 2 (by rfl) ⟨1795479, by rfl⟩ : syracuseStep 4787945 = 3590959) B3590959
theorem B3191963 : Blo 2127435 3191963 := bstep (se 1 (by rfl) ⟨2393972, by rfl⟩ : syracuseStep 3191963 = 4787945) B4787945
theorem B2127975 : Blo 2127435 2127975 := bstep (se 1 (by rfl) ⟨1595981, by rfl⟩ : syracuseStep 2127975 = 3191963) B3191963
theorem B2393977 : Blo 2127435 2393977 := bbase (se 2 (by rfl) ⟨897741, by rfl⟩ : syracuseStep 2393977 = 1795483) (by norm_num)
theorem B3191969 : Blo 2127435 3191969 := bstep (se 2 (by rfl) ⟨1196988, by rfl⟩ : syracuseStep 3191969 = 2393977) B2393977
theorem B2127979 : Blo 2127435 2127979 := bstep (se 1 (by rfl) ⟨1595984, by rfl⟩ : syracuseStep 2127979 = 3191969) B3191969
theorem B2426645 : Blo 2127435 2426645 := bbase (se 6 (by rfl) ⟨56874, by rfl⟩ : syracuseStep 2426645 = 113749) (by norm_num)
theorem B6471053 : Blo 2127435 6471053 := bstep (se 3 (by rfl) ⟨1213322, by rfl⟩ : syracuseStep 6471053 = 2426645) B2426645
theorem B4314035 : Blo 2127435 4314035 := bstep (se 1 (by rfl) ⟨3235526, by rfl⟩ : syracuseStep 4314035 = 6471053) B6471053
theorem B2876023 : Blo 2127435 2876023 := bstep (se 1 (by rfl) ⟨2157017, by rfl⟩ : syracuseStep 2876023 = 4314035) B4314035
theorem B3834697 : Blo 2127435 3834697 := bstep (se 2 (by rfl) ⟨1438011, by rfl⟩ : syracuseStep 3834697 = 2876023) B2876023
theorem B5112929 : Blo 2127435 5112929 := bstep (se 2 (by rfl) ⟨1917348, by rfl⟩ : syracuseStep 5112929 = 3834697) B3834697
theorem B13634477 : Blo 2127435 13634477 := bstep (se 3 (by rfl) ⟨2556464, by rfl⟩ : syracuseStep 13634477 = 5112929) B5112929
theorem B9089651 : Blo 2127435 9089651 := bstep (se 1 (by rfl) ⟨6817238, by rfl⟩ : syracuseStep 9089651 = 13634477) B13634477
theorem B6059767 : Blo 2127435 6059767 := bstep (se 1 (by rfl) ⟨4544825, by rfl⟩ : syracuseStep 6059767 = 9089651) B9089651
theorem B8079689 : Blo 2127435 8079689 := bstep (se 2 (by rfl) ⟨3029883, by rfl⟩ : syracuseStep 8079689 = 6059767) B6059767
theorem B5386459 : Blo 2127435 5386459 := bstep (se 1 (by rfl) ⟨4039844, by rfl⟩ : syracuseStep 5386459 = 8079689) B8079689
theorem B7181945 : Blo 2127435 7181945 := bstep (se 2 (by rfl) ⟨2693229, by rfl⟩ : syracuseStep 7181945 = 5386459) B5386459
theorem B4787963 : Blo 2127435 4787963 := bstep (se 1 (by rfl) ⟨3590972, by rfl⟩ : syracuseStep 4787963 = 7181945) B7181945
theorem B3191975 : Blo 2127435 3191975 := bstep (se 1 (by rfl) ⟨2393981, by rfl⟩ : syracuseStep 3191975 = 4787963) B4787963
theorem B2127983 : Blo 2127435 2127983 := bstep (se 1 (by rfl) ⟨1595987, by rfl⟩ : syracuseStep 2127983 = 3191975) B3191975
theorem B3191981 : Blo 2127435 3191981 := bbase (se 3 (by rfl) ⟨598496, by rfl⟩ : syracuseStep 3191981 = 1196993) (by norm_num)
theorem B2127987 : Blo 2127435 2127987 := bstep (se 1 (by rfl) ⟨1595990, by rfl⟩ : syracuseStep 2127987 = 3191981) B3191981
theorem B4787981 : Blo 2127435 4787981 := bbase (se 3 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 4787981 = 1795493) (by norm_num)
theorem B3191987 : Blo 2127435 3191987 := bstep (se 1 (by rfl) ⟨2393990, by rfl⟩ : syracuseStep 3191987 = 4787981) B4787981
theorem B2127991 : Blo 2127435 2127991 := bstep (se 1 (by rfl) ⟨1595993, by rfl⟩ : syracuseStep 2127991 = 3191987) B3191987
theorem B2693245 : Blo 2127435 2693245 := bbase (se 3 (by rfl) ⟨504983, by rfl⟩ : syracuseStep 2693245 = 1009967) (by norm_num)
theorem B3590993 : Blo 2127435 3590993 := bstep (se 2 (by rfl) ⟨1346622, by rfl⟩ : syracuseStep 3590993 = 2693245) B2693245
theorem B2393995 : Blo 2127435 2393995 := bstep (se 1 (by rfl) ⟨1795496, by rfl⟩ : syracuseStep 2393995 = 3590993) B3590993
theorem B3191993 : Blo 2127435 3191993 := bstep (se 2 (by rfl) ⟨1196997, by rfl⟩ : syracuseStep 3191993 = 2393995) B2393995
theorem B2127995 : Blo 2127435 2127995 := bstep (se 1 (by rfl) ⟨1595996, by rfl⟩ : syracuseStep 2127995 = 3191993) B3191993
theorem B8628133 : Blo 2127435 8628133 := bbase (se 4 (by rfl) ⟨808887, by rfl⟩ : syracuseStep 8628133 = 1617775) (by norm_num)
theorem B11504177 : Blo 2127435 11504177 := bstep (se 2 (by rfl) ⟨4314066, by rfl⟩ : syracuseStep 11504177 = 8628133) B8628133
theorem B7669451 : Blo 2127435 7669451 := bstep (se 1 (by rfl) ⟨5752088, by rfl⟩ : syracuseStep 7669451 = 11504177) B11504177
theorem B5112967 : Blo 2127435 5112967 := bstep (se 1 (by rfl) ⟨3834725, by rfl⟩ : syracuseStep 5112967 = 7669451) B7669451
theorem B6817289 : Blo 2127435 6817289 := bstep (se 2 (by rfl) ⟨2556483, by rfl⟩ : syracuseStep 6817289 = 5112967) B5112967
theorem B18179437 : Blo 2127435 18179437 := bstep (se 3 (by rfl) ⟨3408644, by rfl⟩ : syracuseStep 18179437 = 6817289) B6817289
theorem B24239249 : Blo 2127435 24239249 := bstep (se 2 (by rfl) ⟨9089718, by rfl⟩ : syracuseStep 24239249 = 18179437) B18179437
theorem B16159499 : Blo 2127435 16159499 := bstep (se 1 (by rfl) ⟨12119624, by rfl⟩ : syracuseStep 16159499 = 24239249) B24239249
theorem B10772999 : Blo 2127435 10772999 := bstep (se 1 (by rfl) ⟨8079749, by rfl⟩ : syracuseStep 10772999 = 16159499) B16159499
theorem B7181999 : Blo 2127435 7181999 := bstep (se 1 (by rfl) ⟨5386499, by rfl⟩ : syracuseStep 7181999 = 10772999) B10772999
theorem B4787999 : Blo 2127435 4787999 := bstep (se 1 (by rfl) ⟨3590999, by rfl⟩ : syracuseStep 4787999 = 7181999) B7181999
theorem B3191999 : Blo 2127435 3191999 := bstep (se 1 (by rfl) ⟨2393999, by rfl⟩ : syracuseStep 3191999 = 4787999) B4787999
theorem B2127999 : Blo 2127435 2127999 := bstep (se 1 (by rfl) ⟨1595999, by rfl⟩ : syracuseStep 2127999 = 3191999) B3191999
theorem B3192005 : Blo 2127435 3192005 := bbase (se 4 (by rfl) ⟨299250, by rfl⟩ : syracuseStep 3192005 = 598501) (by norm_num)
theorem B2128003 : Blo 2127435 2128003 := bstep (se 1 (by rfl) ⟨1596002, by rfl⟩ : syracuseStep 2128003 = 3192005) B3192005
theorem B3591013 : Blo 2127435 3591013 := bbase (se 4 (by rfl) ⟨336657, by rfl⟩ : syracuseStep 3591013 = 673315) (by norm_num)
theorem B4788017 : Blo 2127435 4788017 := bstep (se 2 (by rfl) ⟨1795506, by rfl⟩ : syracuseStep 4788017 = 3591013) B3591013
theorem B3192011 : Blo 2127435 3192011 := bstep (se 1 (by rfl) ⟨2394008, by rfl⟩ : syracuseStep 3192011 = 4788017) B4788017
theorem B2128007 : Blo 2127435 2128007 := bstep (se 1 (by rfl) ⟨1596005, by rfl⟩ : syracuseStep 2128007 = 3192011) B3192011
theorem B2394013 : Blo 2127435 2394013 := bbase (se 3 (by rfl) ⟨448877, by rfl⟩ : syracuseStep 2394013 = 897755) (by norm_num)
theorem B3192017 : Blo 2127435 3192017 := bstep (se 2 (by rfl) ⟨1197006, by rfl⟩ : syracuseStep 3192017 = 2394013) B2394013
theorem B2128011 : Blo 2127435 2128011 := bstep (se 1 (by rfl) ⟨1596008, by rfl⟩ : syracuseStep 2128011 = 3192017) B3192017
theorem B7182053 : Blo 2127435 7182053 := bbase (se 4 (by rfl) ⟨673317, by rfl⟩ : syracuseStep 7182053 = 1346635) (by norm_num)
theorem B4788035 : Blo 2127435 4788035 := bstep (se 1 (by rfl) ⟨3591026, by rfl⟩ : syracuseStep 4788035 = 7182053) B7182053
theorem B3192023 : Blo 2127435 3192023 := bstep (se 1 (by rfl) ⟨2394017, by rfl⟩ : syracuseStep 3192023 = 4788035) B4788035
theorem B2128015 : Blo 2127435 2128015 := bstep (se 1 (by rfl) ⟨1596011, by rfl⟩ : syracuseStep 2128015 = 3192023) B3192023
theorem B3192029 : Blo 2127435 3192029 := bbase (se 3 (by rfl) ⟨598505, by rfl⟩ : syracuseStep 3192029 = 1197011) (by norm_num)
theorem B2128019 : Blo 2127435 2128019 := bstep (se 1 (by rfl) ⟨1596014, by rfl⟩ : syracuseStep 2128019 = 3192029) B3192029
theorem B4788053 : Blo 2127435 4788053 := bbase (se 9 (by rfl) ⟨14027, by rfl⟩ : syracuseStep 4788053 = 28055) (by norm_num)
theorem B3192035 : Blo 2127435 3192035 := bstep (se 1 (by rfl) ⟨2394026, by rfl⟩ : syracuseStep 3192035 = 4788053) B4788053
theorem B2128023 : Blo 2127435 2128023 := bstep (se 1 (by rfl) ⟨1596017, by rfl⟩ : syracuseStep 2128023 = 3192035) B3192035
theorem B6059893 : Blo 2127435 6059893 := bbase (se 5 (by rfl) ⟨284057, by rfl⟩ : syracuseStep 6059893 = 568115) (by norm_num)
theorem B8079857 : Blo 2127435 8079857 := bstep (se 2 (by rfl) ⟨3029946, by rfl⟩ : syracuseStep 8079857 = 6059893) B6059893
theorem B5386571 : Blo 2127435 5386571 := bstep (se 1 (by rfl) ⟨4039928, by rfl⟩ : syracuseStep 5386571 = 8079857) B8079857
theorem B3591047 : Blo 2127435 3591047 := bstep (se 1 (by rfl) ⟨2693285, by rfl⟩ : syracuseStep 3591047 = 5386571) B5386571
theorem B2394031 : Blo 2127435 2394031 := bstep (se 1 (by rfl) ⟨1795523, by rfl⟩ : syracuseStep 2394031 = 3591047) B3591047
theorem B3192041 : Blo 2127435 3192041 := bstep (se 2 (by rfl) ⟨1197015, by rfl⟩ : syracuseStep 3192041 = 2394031) B2394031
theorem B2128027 : Blo 2127435 2128027 := bstep (se 1 (by rfl) ⟨1596020, by rfl⟩ : syracuseStep 2128027 = 3192041) B3192041
theorem B19946933 : Blo 2127435 19946933 := bbase (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) (by norm_num)
theorem B13297955 : Blo 2127435 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B141844853 : Blo 2127435 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B94563235 : Blo 2127435 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B126084313 : Blo 2127435 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B168112417 : Blo 2127435 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B224149889 : Blo 2127435 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B597733037 : Blo 2127435 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B398488691 : Blo 2127435 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B1062636509 : Blo 2127435 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B2833697357 : Blo 2127435 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B1889131571 : Blo 2127435 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B1259421047 : Blo 2127435 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B839614031 : Blo 2127435 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B559742687 : Blo 2127435 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B373161791 : Blo 2127435 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B248774527 : Blo 2127435 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B331699369 : Blo 2127435 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B442265825 : Blo 2127435 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B294843883 : Blo 2127435 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B393125177 : Blo 2127435 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B262083451 : Blo 2127435 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B349444601 : Blo 2127435 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B232963067 : Blo 2127435 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B155308711 : Blo 2127435 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B207078281 : Blo 2127435 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B138052187 : Blo 2127435 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B92034791 : Blo 2127435 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B61356527 : Blo 2127435 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B40904351 : Blo 2127435 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B27269567 : Blo 2127435 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B18179711 : Blo 2127435 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B12119807 : Blo 2127435 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B8079871 : Blo 2127435 8079871 := bstep (se 1 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 8079871 = 12119807) B12119807
theorem B10773161 : Blo 2127435 10773161 := bstep (se 2 (by rfl) ⟨4039935, by rfl⟩ : syracuseStep 10773161 = 8079871) B8079871
theorem B7182107 : Blo 2127435 7182107 := bstep (se 1 (by rfl) ⟨5386580, by rfl⟩ : syracuseStep 7182107 = 10773161) B10773161
theorem B4788071 : Blo 2127435 4788071 := bstep (se 1 (by rfl) ⟨3591053, by rfl⟩ : syracuseStep 4788071 = 7182107) B7182107
theorem B3192047 : Blo 2127435 3192047 := bstep (se 1 (by rfl) ⟨2394035, by rfl⟩ : syracuseStep 3192047 = 4788071) B4788071
theorem B2128031 : Blo 2127435 2128031 := bstep (se 1 (by rfl) ⟨1596023, by rfl⟩ : syracuseStep 2128031 = 3192047) B3192047
theorem B3192053 : Blo 2127435 3192053 := bbase (se 5 (by rfl) ⟨149627, by rfl⟩ : syracuseStep 3192053 = 299255) (by norm_num)
theorem B2128035 : Blo 2127435 2128035 := bstep (se 1 (by rfl) ⟨1596026, by rfl⟩ : syracuseStep 2128035 = 3192053) B3192053
theorem B13634837 : Blo 2127435 13634837 := bbase (se 6 (by rfl) ⟨319566, by rfl⟩ : syracuseStep 13634837 = 639133) (by norm_num)
theorem B9089891 : Blo 2127435 9089891 := bstep (se 1 (by rfl) ⟨6817418, by rfl⟩ : syracuseStep 9089891 = 13634837) B13634837
theorem B6059927 : Blo 2127435 6059927 := bstep (se 1 (by rfl) ⟨4544945, by rfl⟩ : syracuseStep 6059927 = 9089891) B9089891
theorem B4039951 : Blo 2127435 4039951 := bstep (se 1 (by rfl) ⟨3029963, by rfl⟩ : syracuseStep 4039951 = 6059927) B6059927
theorem B5386601 : Blo 2127435 5386601 := bstep (se 2 (by rfl) ⟨2019975, by rfl⟩ : syracuseStep 5386601 = 4039951) B4039951
theorem B3591067 : Blo 2127435 3591067 := bstep (se 1 (by rfl) ⟨2693300, by rfl⟩ : syracuseStep 3591067 = 5386601) B5386601
theorem B4788089 : Blo 2127435 4788089 := bstep (se 2 (by rfl) ⟨1795533, by rfl⟩ : syracuseStep 4788089 = 3591067) B3591067
theorem B3192059 : Blo 2127435 3192059 := bstep (se 1 (by rfl) ⟨2394044, by rfl⟩ : syracuseStep 3192059 = 4788089) B4788089
theorem B2128039 : Blo 2127435 2128039 := bstep (se 1 (by rfl) ⟨1596029, by rfl⟩ : syracuseStep 2128039 = 3192059) B3192059
theorem B2394049 : Blo 2127435 2394049 := bbase (se 2 (by rfl) ⟨897768, by rfl⟩ : syracuseStep 2394049 = 1795537) (by norm_num)
theorem B3192065 : Blo 2127435 3192065 := bstep (se 2 (by rfl) ⟨1197024, by rfl⟩ : syracuseStep 3192065 = 2394049) B2394049
theorem B2128043 : Blo 2127435 2128043 := bstep (se 1 (by rfl) ⟨1596032, by rfl⟩ : syracuseStep 2128043 = 3192065) B3192065
theorem B5386621 : Blo 2127435 5386621 := bbase (se 3 (by rfl) ⟨1009991, by rfl⟩ : syracuseStep 5386621 = 2019983) (by norm_num)
theorem B7182161 : Blo 2127435 7182161 := bstep (se 2 (by rfl) ⟨2693310, by rfl⟩ : syracuseStep 7182161 = 5386621) B5386621
theorem B4788107 : Blo 2127435 4788107 := bstep (se 1 (by rfl) ⟨3591080, by rfl⟩ : syracuseStep 4788107 = 7182161) B7182161
theorem B3192071 : Blo 2127435 3192071 := bstep (se 1 (by rfl) ⟨2394053, by rfl⟩ : syracuseStep 3192071 = 4788107) B4788107
theorem B2128047 : Blo 2127435 2128047 := bstep (se 1 (by rfl) ⟨1596035, by rfl⟩ : syracuseStep 2128047 = 3192071) B3192071
theorem B3192077 : Blo 2127435 3192077 := bbase (se 3 (by rfl) ⟨598514, by rfl⟩ : syracuseStep 3192077 = 1197029) (by norm_num)
theorem B2128051 : Blo 2127435 2128051 := bstep (se 1 (by rfl) ⟨1596038, by rfl⟩ : syracuseStep 2128051 = 3192077) B3192077
theorem B4788125 : Blo 2127435 4788125 := bbase (se 3 (by rfl) ⟨897773, by rfl⟩ : syracuseStep 4788125 = 1795547) (by norm_num)
theorem B3192083 : Blo 2127435 3192083 := bstep (se 1 (by rfl) ⟨2394062, by rfl⟩ : syracuseStep 3192083 = 4788125) B4788125
theorem B2128055 : Blo 2127435 2128055 := bstep (se 1 (by rfl) ⟨1596041, by rfl⟩ : syracuseStep 2128055 = 3192083) B3192083
theorem B3591101 : Blo 2127435 3591101 := bbase (se 3 (by rfl) ⟨673331, by rfl⟩ : syracuseStep 3591101 = 1346663) (by norm_num)
theorem B2394067 : Blo 2127435 2394067 := bstep (se 1 (by rfl) ⟨1795550, by rfl⟩ : syracuseStep 2394067 = 3591101) B3591101
theorem B3192089 : Blo 2127435 3192089 := bstep (se 2 (by rfl) ⟨1197033, by rfl⟩ : syracuseStep 3192089 = 2394067) B2394067
theorem B2128059 : Blo 2127435 2128059 := bstep (se 1 (by rfl) ⟨1596044, by rfl⟩ : syracuseStep 2128059 = 3192089) B3192089
theorem B12119989 : Blo 2127435 12119989 := bbase (se 5 (by rfl) ⟨568124, by rfl⟩ : syracuseStep 12119989 = 1136249) (by norm_num)
theorem B16159985 : Blo 2127435 16159985 := bstep (se 2 (by rfl) ⟨6059994, by rfl⟩ : syracuseStep 16159985 = 12119989) B12119989
theorem B10773323 : Blo 2127435 10773323 := bstep (se 1 (by rfl) ⟨8079992, by rfl⟩ : syracuseStep 10773323 = 16159985) B16159985
theorem B7182215 : Blo 2127435 7182215 := bstep (se 1 (by rfl) ⟨5386661, by rfl⟩ : syracuseStep 7182215 = 10773323) B10773323
theorem B4788143 : Blo 2127435 4788143 := bstep (se 1 (by rfl) ⟨3591107, by rfl⟩ : syracuseStep 4788143 = 7182215) B7182215
theorem B3192095 : Blo 2127435 3192095 := bstep (se 1 (by rfl) ⟨2394071, by rfl⟩ : syracuseStep 3192095 = 4788143) B4788143
theorem B2128063 : Blo 2127435 2128063 := bstep (se 1 (by rfl) ⟨1596047, by rfl⟩ : syracuseStep 2128063 = 3192095) B3192095
theorem B3192101 : Blo 2127435 3192101 := bbase (se 4 (by rfl) ⟨299259, by rfl⟩ : syracuseStep 3192101 = 598519) (by norm_num)
theorem B2128067 : Blo 2127435 2128067 := bstep (se 1 (by rfl) ⟨1596050, by rfl⟩ : syracuseStep 2128067 = 3192101) B3192101
theorem B2693341 : Blo 2127435 2693341 := bbase (se 3 (by rfl) ⟨505001, by rfl⟩ : syracuseStep 2693341 = 1010003) (by norm_num)
theorem B3591121 : Blo 2127435 3591121 := bstep (se 2 (by rfl) ⟨1346670, by rfl⟩ : syracuseStep 3591121 = 2693341) B2693341
theorem B4788161 : Blo 2127435 4788161 := bstep (se 2 (by rfl) ⟨1795560, by rfl⟩ : syracuseStep 4788161 = 3591121) B3591121
theorem B3192107 : Blo 2127435 3192107 := bstep (se 1 (by rfl) ⟨2394080, by rfl⟩ : syracuseStep 3192107 = 4788161) B4788161
theorem B2128071 : Blo 2127435 2128071 := bstep (se 1 (by rfl) ⟨1596053, by rfl⟩ : syracuseStep 2128071 = 3192107) B3192107
theorem B2394085 : Blo 2127435 2394085 := bbase (se 4 (by rfl) ⟨224445, by rfl⟩ : syracuseStep 2394085 = 448891) (by norm_num)
theorem B3192113 : Blo 2127435 3192113 := bstep (se 2 (by rfl) ⟨1197042, by rfl⟩ : syracuseStep 3192113 = 2394085) B2394085
theorem B2128075 : Blo 2127435 2128075 := bstep (se 1 (by rfl) ⟨1596056, by rfl⟩ : syracuseStep 2128075 = 3192113) B3192113
theorem B3640133 : Blo 2127435 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B2426755 : Blo 2127435 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B3235673 : Blo 2127435 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B2157115 : Blo 2127435 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B2876153 : Blo 2127435 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B7669741 : Blo 2127435 7669741 := bstep (se 3 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 7669741 = 2876153) B2876153
theorem B10226321 : Blo 2127435 10226321 := bstep (se 2 (by rfl) ⟨3834870, by rfl⟩ : syracuseStep 10226321 = 7669741) B7669741
theorem B6817547 : Blo 2127435 6817547 := bstep (se 1 (by rfl) ⟨5113160, by rfl⟩ : syracuseStep 6817547 = 10226321) B10226321
theorem B4545031 : Blo 2127435 4545031 := bstep (se 1 (by rfl) ⟨3408773, by rfl⟩ : syracuseStep 4545031 = 6817547) B6817547
theorem B6060041 : Blo 2127435 6060041 := bstep (se 2 (by rfl) ⟨2272515, by rfl⟩ : syracuseStep 6060041 = 4545031) B4545031
theorem B4040027 : Blo 2127435 4040027 := bstep (se 1 (by rfl) ⟨3030020, by rfl⟩ : syracuseStep 4040027 = 6060041) B6060041
theorem B2693351 : Blo 2127435 2693351 := bstep (se 1 (by rfl) ⟨2020013, by rfl⟩ : syracuseStep 2693351 = 4040027) B4040027
theorem B7182269 : Blo 2127435 7182269 := bstep (se 3 (by rfl) ⟨1346675, by rfl⟩ : syracuseStep 7182269 = 2693351) B2693351
theorem B4788179 : Blo 2127435 4788179 := bstep (se 1 (by rfl) ⟨3591134, by rfl⟩ : syracuseStep 4788179 = 7182269) B7182269
theorem B3192119 : Blo 2127435 3192119 := bstep (se 1 (by rfl) ⟨2394089, by rfl⟩ : syracuseStep 3192119 = 4788179) B4788179
theorem B2128079 : Blo 2127435 2128079 := bstep (se 1 (by rfl) ⟨1596059, by rfl⟩ : syracuseStep 2128079 = 3192119) B3192119
theorem B3192125 : Blo 2127435 3192125 := bbase (se 3 (by rfl) ⟨598523, by rfl⟩ : syracuseStep 3192125 = 1197047) (by norm_num)
theorem B2128083 : Blo 2127435 2128083 := bstep (se 1 (by rfl) ⟨1596062, by rfl⟩ : syracuseStep 2128083 = 3192125) B3192125
theorem B4788197 : Blo 2127435 4788197 := bbase (se 4 (by rfl) ⟨448893, by rfl⟩ : syracuseStep 4788197 = 897787) (by norm_num)
theorem B3192131 : Blo 2127435 3192131 := bstep (se 1 (by rfl) ⟨2394098, by rfl⟩ : syracuseStep 3192131 = 4788197) B4788197
theorem B2128087 : Blo 2127435 2128087 := bstep (se 1 (by rfl) ⟨1596065, by rfl⟩ : syracuseStep 2128087 = 3192131) B3192131
theorem B5386733 : Blo 2127435 5386733 := bbase (se 3 (by rfl) ⟨1010012, by rfl⟩ : syracuseStep 5386733 = 2020025) (by norm_num)
theorem B3591155 : Blo 2127435 3591155 := bstep (se 1 (by rfl) ⟨2693366, by rfl⟩ : syracuseStep 3591155 = 5386733) B5386733
theorem B2394103 : Blo 2127435 2394103 := bstep (se 1 (by rfl) ⟨1795577, by rfl⟩ : syracuseStep 2394103 = 3591155) B3591155
theorem B3192137 : Blo 2127435 3192137 := bstep (se 2 (by rfl) ⟨1197051, by rfl⟩ : syracuseStep 3192137 = 2394103) B2394103
theorem B2128091 : Blo 2127435 2128091 := bstep (se 1 (by rfl) ⟨1596068, by rfl⟩ : syracuseStep 2128091 = 3192137) B3192137
theorem B18428309 : Blo 2127435 18428309 := bbase (se 6 (by rfl) ⟨431913, by rfl⟩ : syracuseStep 18428309 = 863827) (by norm_num)
theorem B12285539 : Blo 2127435 12285539 := bstep (se 1 (by rfl) ⟨9214154, by rfl⟩ : syracuseStep 12285539 = 18428309) B18428309
theorem B8190359 : Blo 2127435 8190359 := bstep (se 1 (by rfl) ⟨6142769, by rfl⟩ : syracuseStep 8190359 = 12285539) B12285539
theorem B5460239 : Blo 2127435 5460239 := bstep (se 1 (by rfl) ⟨4095179, by rfl⟩ : syracuseStep 5460239 = 8190359) B8190359
theorem B3640159 : Blo 2127435 3640159 := bstep (se 1 (by rfl) ⟨2730119, by rfl⟩ : syracuseStep 3640159 = 5460239) B5460239
theorem B19414181 : Blo 2127435 19414181 := bstep (se 4 (by rfl) ⟨1820079, by rfl⟩ : syracuseStep 19414181 = 3640159) B3640159
theorem B12942787 : Blo 2127435 12942787 := bstep (se 1 (by rfl) ⟨9707090, by rfl⟩ : syracuseStep 12942787 = 19414181) B19414181
theorem B17257049 : Blo 2127435 17257049 := bstep (se 2 (by rfl) ⟨6471393, by rfl⟩ : syracuseStep 17257049 = 12942787) B12942787
theorem B11504699 : Blo 2127435 11504699 := bstep (se 1 (by rfl) ⟨8628524, by rfl⟩ : syracuseStep 11504699 = 17257049) B17257049
theorem B7669799 : Blo 2127435 7669799 := bstep (se 1 (by rfl) ⟨5752349, by rfl⟩ : syracuseStep 7669799 = 11504699) B11504699
theorem B5113199 : Blo 2127435 5113199 := bstep (se 1 (by rfl) ⟨3834899, by rfl⟩ : syracuseStep 5113199 = 7669799) B7669799
theorem B3408799 : Blo 2127435 3408799 := bstep (se 1 (by rfl) ⟨2556599, by rfl⟩ : syracuseStep 3408799 = 5113199) B5113199
theorem B4545065 : Blo 2127435 4545065 := bstep (se 2 (by rfl) ⟨1704399, by rfl⟩ : syracuseStep 4545065 = 3408799) B3408799
theorem B3030043 : Blo 2127435 3030043 := bstep (se 1 (by rfl) ⟨2272532, by rfl⟩ : syracuseStep 3030043 = 4545065) B4545065
theorem B4040057 : Blo 2127435 4040057 := bstep (se 2 (by rfl) ⟨1515021, by rfl⟩ : syracuseStep 4040057 = 3030043) B3030043
theorem B10773485 : Blo 2127435 10773485 := bstep (se 3 (by rfl) ⟨2020028, by rfl⟩ : syracuseStep 10773485 = 4040057) B4040057
theorem B7182323 : Blo 2127435 7182323 := bstep (se 1 (by rfl) ⟨5386742, by rfl⟩ : syracuseStep 7182323 = 10773485) B10773485
theorem B4788215 : Blo 2127435 4788215 := bstep (se 1 (by rfl) ⟨3591161, by rfl⟩ : syracuseStep 4788215 = 7182323) B7182323
theorem B3192143 : Blo 2127435 3192143 := bstep (se 1 (by rfl) ⟨2394107, by rfl⟩ : syracuseStep 3192143 = 4788215) B4788215
theorem B2128095 : Blo 2127435 2128095 := bstep (se 1 (by rfl) ⟨1596071, by rfl⟩ : syracuseStep 2128095 = 3192143) B3192143
theorem B3192149 : Blo 2127435 3192149 := bbase (se 13 (by rfl) ⟨584, by rfl⟩ : syracuseStep 3192149 = 1169) (by norm_num)
theorem B2128099 : Blo 2127435 2128099 := bstep (se 1 (by rfl) ⟨1596074, by rfl⟩ : syracuseStep 2128099 = 3192149) B3192149
theorem B2272541 : Blo 2127435 2272541 := bbase (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) (by norm_num)
theorem B6060109 : Blo 2127435 6060109 := bstep (se 3 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 6060109 = 2272541) B2272541
theorem B8080145 : Blo 2127435 8080145 := bstep (se 2 (by rfl) ⟨3030054, by rfl⟩ : syracuseStep 8080145 = 6060109) B6060109
theorem B5386763 : Blo 2127435 5386763 := bstep (se 1 (by rfl) ⟨4040072, by rfl⟩ : syracuseStep 5386763 = 8080145) B8080145
theorem B3591175 : Blo 2127435 3591175 := bstep (se 1 (by rfl) ⟨2693381, by rfl⟩ : syracuseStep 3591175 = 5386763) B5386763
theorem B4788233 : Blo 2127435 4788233 := bstep (se 2 (by rfl) ⟨1795587, by rfl⟩ : syracuseStep 4788233 = 3591175) B3591175
theorem B3192155 : Blo 2127435 3192155 := bstep (se 1 (by rfl) ⟨2394116, by rfl⟩ : syracuseStep 3192155 = 4788233) B4788233
theorem B2128103 : Blo 2127435 2128103 := bstep (se 1 (by rfl) ⟨1596077, by rfl⟩ : syracuseStep 2128103 = 3192155) B3192155
theorem B2394121 : Blo 2127435 2394121 := bbase (se 2 (by rfl) ⟨897795, by rfl⟩ : syracuseStep 2394121 = 1795591) (by norm_num)
theorem B3192161 : Blo 2127435 3192161 := bstep (se 2 (by rfl) ⟨1197060, by rfl⟩ : syracuseStep 3192161 = 2394121) B2394121
theorem B2128107 : Blo 2127435 2128107 := bstep (se 1 (by rfl) ⟨1596080, by rfl⟩ : syracuseStep 2128107 = 3192161) B3192161
theorem B7774501 : Blo 2127435 7774501 := bbase (se 4 (by rfl) ⟨728859, by rfl⟩ : syracuseStep 7774501 = 1457719) (by norm_num)
theorem B10366001 : Blo 2127435 10366001 := bstep (se 2 (by rfl) ⟨3887250, by rfl⟩ : syracuseStep 10366001 = 7774501) B7774501
theorem B6910667 : Blo 2127435 6910667 := bstep (se 1 (by rfl) ⟨5183000, by rfl⟩ : syracuseStep 6910667 = 10366001) B10366001
theorem B4607111 : Blo 2127435 4607111 := bstep (se 1 (by rfl) ⟨3455333, by rfl⟩ : syracuseStep 4607111 = 6910667) B6910667
theorem B3071407 : Blo 2127435 3071407 := bstep (se 1 (by rfl) ⟨2303555, by rfl⟩ : syracuseStep 3071407 = 4607111) B4607111
theorem B4095209 : Blo 2127435 4095209 := bstep (se 2 (by rfl) ⟨1535703, by rfl⟩ : syracuseStep 4095209 = 3071407) B3071407
theorem B10920557 : Blo 2127435 10920557 := bstep (se 3 (by rfl) ⟨2047604, by rfl⟩ : syracuseStep 10920557 = 4095209) B4095209
theorem B7280371 : Blo 2127435 7280371 := bstep (se 1 (by rfl) ⟨5460278, by rfl⟩ : syracuseStep 7280371 = 10920557) B10920557
theorem B9707161 : Blo 2127435 9707161 := bstep (se 2 (by rfl) ⟨3640185, by rfl⟩ : syracuseStep 9707161 = 7280371) B7280371
theorem B12942881 : Blo 2127435 12942881 := bstep (se 2 (by rfl) ⟨4853580, by rfl⟩ : syracuseStep 12942881 = 9707161) B9707161
theorem B8628587 : Blo 2127435 8628587 := bstep (se 1 (by rfl) ⟨6471440, by rfl⟩ : syracuseStep 8628587 = 12942881) B12942881
theorem B5752391 : Blo 2127435 5752391 := bstep (se 1 (by rfl) ⟨4314293, by rfl⟩ : syracuseStep 5752391 = 8628587) B8628587
theorem B15339709 : Blo 2127435 15339709 := bstep (se 3 (by rfl) ⟨2876195, by rfl⟩ : syracuseStep 15339709 = 5752391) B5752391
theorem B20452945 : Blo 2127435 20452945 := bstep (se 2 (by rfl) ⟨7669854, by rfl⟩ : syracuseStep 20452945 = 15339709) B15339709
theorem B27270593 : Blo 2127435 27270593 := bstep (se 2 (by rfl) ⟨10226472, by rfl⟩ : syracuseStep 27270593 = 20452945) B20452945
theorem B18180395 : Blo 2127435 18180395 := bstep (se 1 (by rfl) ⟨13635296, by rfl⟩ : syracuseStep 18180395 = 27270593) B27270593
theorem B12120263 : Blo 2127435 12120263 := bstep (se 1 (by rfl) ⟨9090197, by rfl⟩ : syracuseStep 12120263 = 18180395) B18180395
theorem B8080175 : Blo 2127435 8080175 := bstep (se 1 (by rfl) ⟨6060131, by rfl⟩ : syracuseStep 8080175 = 12120263) B12120263
theorem B5386783 : Blo 2127435 5386783 := bstep (se 1 (by rfl) ⟨4040087, by rfl⟩ : syracuseStep 5386783 = 8080175) B8080175
theorem B7182377 : Blo 2127435 7182377 := bstep (se 2 (by rfl) ⟨2693391, by rfl⟩ : syracuseStep 7182377 = 5386783) B5386783
theorem B4788251 : Blo 2127435 4788251 := bstep (se 1 (by rfl) ⟨3591188, by rfl⟩ : syracuseStep 4788251 = 7182377) B7182377
theorem B3192167 : Blo 2127435 3192167 := bstep (se 1 (by rfl) ⟨2394125, by rfl⟩ : syracuseStep 3192167 = 4788251) B4788251
theorem B2128111 : Blo 2127435 2128111 := bstep (se 1 (by rfl) ⟨1596083, by rfl⟩ : syracuseStep 2128111 = 3192167) B3192167
theorem B3192173 : Blo 2127435 3192173 := bbase (se 3 (by rfl) ⟨598532, by rfl⟩ : syracuseStep 3192173 = 1197065) (by norm_num)
theorem B2128115 : Blo 2127435 2128115 := bstep (se 1 (by rfl) ⟨1596086, by rfl⟩ : syracuseStep 2128115 = 3192173) B3192173
theorem B4788269 : Blo 2127435 4788269 := bbase (se 3 (by rfl) ⟨897800, by rfl⟩ : syracuseStep 4788269 = 1795601) (by norm_num)
theorem B3192179 : Blo 2127435 3192179 := bstep (se 1 (by rfl) ⟨2394134, by rfl⟩ : syracuseStep 3192179 = 4788269) B4788269
theorem B2128119 : Blo 2127435 2128119 := bstep (se 1 (by rfl) ⟨1596089, by rfl⟩ : syracuseStep 2128119 = 3192179) B3192179
theorem B10226533 : Blo 2127435 10226533 := bbase (se 4 (by rfl) ⟨958737, by rfl⟩ : syracuseStep 10226533 = 1917475) (by norm_num)
theorem B13635377 : Blo 2127435 13635377 := bstep (se 2 (by rfl) ⟨5113266, by rfl⟩ : syracuseStep 13635377 = 10226533) B10226533
theorem B9090251 : Blo 2127435 9090251 := bstep (se 1 (by rfl) ⟨6817688, by rfl⟩ : syracuseStep 9090251 = 13635377) B13635377
theorem B6060167 : Blo 2127435 6060167 := bstep (se 1 (by rfl) ⟨4545125, by rfl⟩ : syracuseStep 6060167 = 9090251) B9090251
theorem B4040111 : Blo 2127435 4040111 := bstep (se 1 (by rfl) ⟨3030083, by rfl⟩ : syracuseStep 4040111 = 6060167) B6060167
theorem B2693407 : Blo 2127435 2693407 := bstep (se 1 (by rfl) ⟨2020055, by rfl⟩ : syracuseStep 2693407 = 4040111) B4040111
theorem B3591209 : Blo 2127435 3591209 := bstep (se 2 (by rfl) ⟨1346703, by rfl⟩ : syracuseStep 3591209 = 2693407) B2693407
theorem B2394139 : Blo 2127435 2394139 := bstep (se 1 (by rfl) ⟨1795604, by rfl⟩ : syracuseStep 2394139 = 3591209) B3591209
theorem B3192185 : Blo 2127435 3192185 := bstep (se 2 (by rfl) ⟨1197069, by rfl⟩ : syracuseStep 3192185 = 2394139) B2394139
theorem B2128123 : Blo 2127435 2128123 := bstep (se 1 (by rfl) ⟨1596092, by rfl⟩ : syracuseStep 2128123 = 3192185) B3192185
theorem B10226549 : Blo 2127435 10226549 := bbase (se 5 (by rfl) ⟨479369, by rfl⟩ : syracuseStep 10226549 = 958739) (by norm_num)
theorem B6817699 : Blo 2127435 6817699 := bstep (se 1 (by rfl) ⟨5113274, by rfl⟩ : syracuseStep 6817699 = 10226549) B10226549
theorem B36361061 : Blo 2127435 36361061 := bstep (se 4 (by rfl) ⟨3408849, by rfl⟩ : syracuseStep 36361061 = 6817699) B6817699
theorem B24240707 : Blo 2127435 24240707 := bstep (se 1 (by rfl) ⟨18180530, by rfl⟩ : syracuseStep 24240707 = 36361061) B36361061
theorem B16160471 : Blo 2127435 16160471 := bstep (se 1 (by rfl) ⟨12120353, by rfl⟩ : syracuseStep 16160471 = 24240707) B24240707
theorem B10773647 : Blo 2127435 10773647 := bstep (se 1 (by rfl) ⟨8080235, by rfl⟩ : syracuseStep 10773647 = 16160471) B16160471
theorem B7182431 : Blo 2127435 7182431 := bstep (se 1 (by rfl) ⟨5386823, by rfl⟩ : syracuseStep 7182431 = 10773647) B10773647
theorem B4788287 : Blo 2127435 4788287 := bstep (se 1 (by rfl) ⟨3591215, by rfl⟩ : syracuseStep 4788287 = 7182431) B7182431
theorem B3192191 : Blo 2127435 3192191 := bstep (se 1 (by rfl) ⟨2394143, by rfl⟩ : syracuseStep 3192191 = 4788287) B4788287
theorem B2128127 : Blo 2127435 2128127 := bstep (se 1 (by rfl) ⟨1596095, by rfl⟩ : syracuseStep 2128127 = 3192191) B3192191
theorem B3192197 : Blo 2127435 3192197 := bbase (se 4 (by rfl) ⟨299268, by rfl⟩ : syracuseStep 3192197 = 598537) (by norm_num)
theorem B2128131 : Blo 2127435 2128131 := bstep (se 1 (by rfl) ⟨1596098, by rfl⟩ : syracuseStep 2128131 = 3192197) B3192197
theorem B3591229 : Blo 2127435 3591229 := bbase (se 3 (by rfl) ⟨673355, by rfl⟩ : syracuseStep 3591229 = 1346711) (by norm_num)
theorem B4788305 : Blo 2127435 4788305 := bstep (se 2 (by rfl) ⟨1795614, by rfl⟩ : syracuseStep 4788305 = 3591229) B3591229
theorem B3192203 : Blo 2127435 3192203 := bstep (se 1 (by rfl) ⟨2394152, by rfl⟩ : syracuseStep 3192203 = 4788305) B4788305
theorem B2128135 : Blo 2127435 2128135 := bstep (se 1 (by rfl) ⟨1596101, by rfl⟩ : syracuseStep 2128135 = 3192203) B3192203
theorem B2394157 : Blo 2127435 2394157 := bbase (se 3 (by rfl) ⟨448904, by rfl⟩ : syracuseStep 2394157 = 897809) (by norm_num)
theorem B3192209 : Blo 2127435 3192209 := bstep (se 2 (by rfl) ⟨1197078, by rfl⟩ : syracuseStep 3192209 = 2394157) B2394157
theorem B2128139 : Blo 2127435 2128139 := bstep (se 1 (by rfl) ⟨1596104, by rfl⟩ : syracuseStep 2128139 = 3192209) B3192209
theorem B7182485 : Blo 2127435 7182485 := bbase (se 6 (by rfl) ⟨168339, by rfl⟩ : syracuseStep 7182485 = 336679) (by norm_num)
theorem B4788323 : Blo 2127435 4788323 := bstep (se 1 (by rfl) ⟨3591242, by rfl⟩ : syracuseStep 4788323 = 7182485) B7182485
theorem B3192215 : Blo 2127435 3192215 := bstep (se 1 (by rfl) ⟨2394161, by rfl⟩ : syracuseStep 3192215 = 4788323) B4788323
theorem B2128143 : Blo 2127435 2128143 := bstep (se 1 (by rfl) ⟨1596107, by rfl⟩ : syracuseStep 2128143 = 3192215) B3192215
theorem B3192221 : Blo 2127435 3192221 := bbase (se 3 (by rfl) ⟨598541, by rfl⟩ : syracuseStep 3192221 = 1197083) (by norm_num)
theorem B2128147 : Blo 2127435 2128147 := bstep (se 1 (by rfl) ⟨1596110, by rfl⟩ : syracuseStep 2128147 = 3192221) B3192221
theorem B4788341 : Blo 2127435 4788341 := bbase (se 5 (by rfl) ⟨224453, by rfl⟩ : syracuseStep 4788341 = 448907) (by norm_num)
theorem B3192227 : Blo 2127435 3192227 := bstep (se 1 (by rfl) ⟨2394170, by rfl⟩ : syracuseStep 3192227 = 4788341) B4788341
theorem B2128151 : Blo 2127435 2128151 := bstep (se 1 (by rfl) ⟨1596113, by rfl⟩ : syracuseStep 2128151 = 3192227) B3192227
theorem B3455405 : Blo 2127435 3455405 := bbase (se 3 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 3455405 = 1295777) (by norm_num)
theorem B2303603 : Blo 2127435 2303603 := bstep (se 1 (by rfl) ⟨1727702, by rfl⟩ : syracuseStep 2303603 = 3455405) B3455405
theorem B24571765 : Blo 2127435 24571765 := bstep (se 5 (by rfl) ⟨1151801, by rfl⟩ : syracuseStep 24571765 = 2303603) B2303603
theorem B131049413 : Blo 2127435 131049413 := bstep (se 4 (by rfl) ⟨12285882, by rfl⟩ : syracuseStep 131049413 = 24571765) B24571765
theorem B87366275 : Blo 2127435 87366275 := bstep (se 1 (by rfl) ⟨65524706, by rfl⟩ : syracuseStep 87366275 = 131049413) B131049413
theorem B58244183 : Blo 2127435 58244183 := bstep (se 1 (by rfl) ⟨43683137, by rfl⟩ : syracuseStep 58244183 = 87366275) B87366275
theorem B38829455 : Blo 2127435 38829455 := bstep (se 1 (by rfl) ⟨29122091, by rfl⟩ : syracuseStep 38829455 = 58244183) B58244183
theorem B25886303 : Blo 2127435 25886303 := bstep (se 1 (by rfl) ⟨19414727, by rfl⟩ : syracuseStep 25886303 = 38829455) B38829455
theorem B17257535 : Blo 2127435 17257535 := bstep (se 1 (by rfl) ⟨12943151, by rfl⟩ : syracuseStep 17257535 = 25886303) B25886303
theorem B11505023 : Blo 2127435 11505023 := bstep (se 1 (by rfl) ⟨8628767, by rfl⟩ : syracuseStep 11505023 = 17257535) B17257535
theorem B7670015 : Blo 2127435 7670015 := bstep (se 1 (by rfl) ⟨5752511, by rfl⟩ : syracuseStep 7670015 = 11505023) B11505023
theorem B5113343 : Blo 2127435 5113343 := bstep (se 1 (by rfl) ⟨3835007, by rfl⟩ : syracuseStep 5113343 = 7670015) B7670015
theorem B3408895 : Blo 2127435 3408895 := bstep (se 1 (by rfl) ⟨2556671, by rfl⟩ : syracuseStep 3408895 = 5113343) B5113343
theorem B18180773 : Blo 2127435 18180773 := bstep (se 4 (by rfl) ⟨1704447, by rfl⟩ : syracuseStep 18180773 = 3408895) B3408895
theorem B12120515 : Blo 2127435 12120515 := bstep (se 1 (by rfl) ⟨9090386, by rfl⟩ : syracuseStep 12120515 = 18180773) B18180773
theorem B8080343 : Blo 2127435 8080343 := bstep (se 1 (by rfl) ⟨6060257, by rfl⟩ : syracuseStep 8080343 = 12120515) B12120515
theorem B5386895 : Blo 2127435 5386895 := bstep (se 1 (by rfl) ⟨4040171, by rfl⟩ : syracuseStep 5386895 = 8080343) B8080343
theorem B3591263 : Blo 2127435 3591263 := bstep (se 1 (by rfl) ⟨2693447, by rfl⟩ : syracuseStep 3591263 = 5386895) B5386895
theorem B2394175 : Blo 2127435 2394175 := bstep (se 1 (by rfl) ⟨1795631, by rfl⟩ : syracuseStep 2394175 = 3591263) B3591263
theorem B3192233 : Blo 2127435 3192233 := bstep (se 2 (by rfl) ⟨1197087, by rfl⟩ : syracuseStep 3192233 = 2394175) B2394175
theorem B2128155 : Blo 2127435 2128155 := bstep (se 1 (by rfl) ⟨1596116, by rfl⟩ : syracuseStep 2128155 = 3192233) B3192233
theorem B8080357 : Blo 2127435 8080357 := bbase (se 4 (by rfl) ⟨757533, by rfl⟩ : syracuseStep 8080357 = 1515067) (by norm_num)
theorem B10773809 : Blo 2127435 10773809 := bstep (se 2 (by rfl) ⟨4040178, by rfl⟩ : syracuseStep 10773809 = 8080357) B8080357
theorem B7182539 : Blo 2127435 7182539 := bstep (se 1 (by rfl) ⟨5386904, by rfl⟩ : syracuseStep 7182539 = 10773809) B10773809
theorem B4788359 : Blo 2127435 4788359 := bstep (se 1 (by rfl) ⟨3591269, by rfl⟩ : syracuseStep 4788359 = 7182539) B7182539
theorem B3192239 : Blo 2127435 3192239 := bstep (se 1 (by rfl) ⟨2394179, by rfl⟩ : syracuseStep 3192239 = 4788359) B4788359
theorem B2128159 : Blo 2127435 2128159 := bstep (se 1 (by rfl) ⟨1596119, by rfl⟩ : syracuseStep 2128159 = 3192239) B3192239
theorem B3192245 : Blo 2127435 3192245 := bbase (se 5 (by rfl) ⟨149636, by rfl⟩ : syracuseStep 3192245 = 299273) (by norm_num)
theorem B2128163 : Blo 2127435 2128163 := bstep (se 1 (by rfl) ⟨1596122, by rfl⟩ : syracuseStep 2128163 = 3192245) B3192245
theorem B5386925 : Blo 2127435 5386925 := bbase (se 3 (by rfl) ⟨1010048, by rfl⟩ : syracuseStep 5386925 = 2020097) (by norm_num)
theorem B3591283 : Blo 2127435 3591283 := bstep (se 1 (by rfl) ⟨2693462, by rfl⟩ : syracuseStep 3591283 = 5386925) B5386925
theorem B4788377 : Blo 2127435 4788377 := bstep (se 2 (by rfl) ⟨1795641, by rfl⟩ : syracuseStep 4788377 = 3591283) B3591283
theorem B3192251 : Blo 2127435 3192251 := bstep (se 1 (by rfl) ⟨2394188, by rfl⟩ : syracuseStep 3192251 = 4788377) B4788377
theorem B2128167 : Blo 2127435 2128167 := bstep (se 1 (by rfl) ⟨1596125, by rfl⟩ : syracuseStep 2128167 = 3192251) B3192251
theorem B2394193 : Blo 2127435 2394193 := bbase (se 2 (by rfl) ⟨897822, by rfl⟩ : syracuseStep 2394193 = 1795645) (by norm_num)
theorem B3192257 : Blo 2127435 3192257 := bstep (se 2 (by rfl) ⟨1197096, by rfl⟩ : syracuseStep 3192257 = 2394193) B2394193
theorem B2128171 : Blo 2127435 2128171 := bstep (se 1 (by rfl) ⟨1596128, by rfl⟩ : syracuseStep 2128171 = 3192257) B3192257
theorem B3030157 : Blo 2127435 3030157 := bbase (se 3 (by rfl) ⟨568154, by rfl⟩ : syracuseStep 3030157 = 1136309) (by norm_num)
theorem B4040209 : Blo 2127435 4040209 := bstep (se 2 (by rfl) ⟨1515078, by rfl⟩ : syracuseStep 4040209 = 3030157) B3030157
theorem B5386945 : Blo 2127435 5386945 := bstep (se 2 (by rfl) ⟨2020104, by rfl⟩ : syracuseStep 5386945 = 4040209) B4040209
theorem B7182593 : Blo 2127435 7182593 := bstep (se 2 (by rfl) ⟨2693472, by rfl⟩ : syracuseStep 7182593 = 5386945) B5386945
theorem B4788395 : Blo 2127435 4788395 := bstep (se 1 (by rfl) ⟨3591296, by rfl⟩ : syracuseStep 4788395 = 7182593) B7182593
theorem B3192263 : Blo 2127435 3192263 := bstep (se 1 (by rfl) ⟨2394197, by rfl⟩ : syracuseStep 3192263 = 4788395) B4788395
theorem B2128175 : Blo 2127435 2128175 := bstep (se 1 (by rfl) ⟨1596131, by rfl⟩ : syracuseStep 2128175 = 3192263) B3192263
theorem B3192269 : Blo 2127435 3192269 := bbase (se 3 (by rfl) ⟨598550, by rfl⟩ : syracuseStep 3192269 = 1197101) (by norm_num)
theorem B2128179 : Blo 2127435 2128179 := bstep (se 1 (by rfl) ⟨1596134, by rfl⟩ : syracuseStep 2128179 = 3192269) B3192269
theorem B4788413 : Blo 2127435 4788413 := bbase (se 3 (by rfl) ⟨897827, by rfl⟩ : syracuseStep 4788413 = 1795655) (by norm_num)
theorem B3192275 : Blo 2127435 3192275 := bstep (se 1 (by rfl) ⟨2394206, by rfl⟩ : syracuseStep 3192275 = 4788413) B4788413
theorem B2128183 : Blo 2127435 2128183 := bstep (se 1 (by rfl) ⟨1596137, by rfl⟩ : syracuseStep 2128183 = 3192275) B3192275
theorem B3591317 : Blo 2127435 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B2394211 : Blo 2127435 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B3192281 : Blo 2127435 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B2128187 : Blo 2127435 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B8190725 : Blo 2127435 8190725 := bbase (se 4 (by rfl) ⟨767880, by rfl⟩ : syracuseStep 8190725 = 1535761) (by norm_num)
theorem B87367733 : Blo 2127435 87367733 := bstep (se 5 (by rfl) ⟨4095362, by rfl⟩ : syracuseStep 87367733 = 8190725) B8190725
theorem B58245155 : Blo 2127435 58245155 := bstep (se 1 (by rfl) ⟨43683866, by rfl⟩ : syracuseStep 58245155 = 87367733) B87367733
theorem B38830103 : Blo 2127435 38830103 := bstep (se 1 (by rfl) ⟨29122577, by rfl⟩ : syracuseStep 38830103 = 58245155) B58245155
theorem B25886735 : Blo 2127435 25886735 := bstep (se 1 (by rfl) ⟨19415051, by rfl⟩ : syracuseStep 25886735 = 38830103) B38830103
theorem B17257823 : Blo 2127435 17257823 := bstep (se 1 (by rfl) ⟨12943367, by rfl⟩ : syracuseStep 17257823 = 25886735) B25886735
theorem B11505215 : Blo 2127435 11505215 := bstep (se 1 (by rfl) ⟨8628911, by rfl⟩ : syracuseStep 11505215 = 17257823) B17257823
theorem B7670143 : Blo 2127435 7670143 := bstep (se 1 (by rfl) ⟨5752607, by rfl⟩ : syracuseStep 7670143 = 11505215) B11505215
theorem B10226857 : Blo 2127435 10226857 := bstep (se 2 (by rfl) ⟨3835071, by rfl⟩ : syracuseStep 10226857 = 7670143) B7670143
theorem B13635809 : Blo 2127435 13635809 := bstep (se 2 (by rfl) ⟨5113428, by rfl⟩ : syracuseStep 13635809 = 10226857) B10226857
theorem B9090539 : Blo 2127435 9090539 := bstep (se 1 (by rfl) ⟨6817904, by rfl⟩ : syracuseStep 9090539 = 13635809) B13635809
theorem B6060359 : Blo 2127435 6060359 := bstep (se 1 (by rfl) ⟨4545269, by rfl⟩ : syracuseStep 6060359 = 9090539) B9090539
theorem B16160957 : Blo 2127435 16160957 := bstep (se 3 (by rfl) ⟨3030179, by rfl⟩ : syracuseStep 16160957 = 6060359) B6060359
theorem B10773971 : Blo 2127435 10773971 := bstep (se 1 (by rfl) ⟨8080478, by rfl⟩ : syracuseStep 10773971 = 16160957) B16160957
theorem B7182647 : Blo 2127435 7182647 := bstep (se 1 (by rfl) ⟨5386985, by rfl⟩ : syracuseStep 7182647 = 10773971) B10773971
theorem B4788431 : Blo 2127435 4788431 := bstep (se 1 (by rfl) ⟨3591323, by rfl⟩ : syracuseStep 4788431 = 7182647) B7182647
theorem B3192287 : Blo 2127435 3192287 := bstep (se 1 (by rfl) ⟨2394215, by rfl⟩ : syracuseStep 3192287 = 4788431) B4788431
theorem B2128191 : Blo 2127435 2128191 := bstep (se 1 (by rfl) ⟨1596143, by rfl⟩ : syracuseStep 2128191 = 3192287) B3192287
theorem B3192293 : Blo 2127435 3192293 := bbase (se 4 (by rfl) ⟨299277, by rfl⟩ : syracuseStep 3192293 = 598555) (by norm_num)
theorem B2128195 : Blo 2127435 2128195 := bstep (se 1 (by rfl) ⟨1596146, by rfl⟩ : syracuseStep 2128195 = 3192293) B3192293
theorem B10921013 : Blo 2127435 10921013 := bbase (se 5 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 10921013 = 1023845) (by norm_num)
theorem B7280675 : Blo 2127435 7280675 := bstep (se 1 (by rfl) ⟨5460506, by rfl⟩ : syracuseStep 7280675 = 10921013) B10921013
theorem B4853783 : Blo 2127435 4853783 := bstep (se 1 (by rfl) ⟨3640337, by rfl⟩ : syracuseStep 4853783 = 7280675) B7280675
theorem B3235855 : Blo 2127435 3235855 := bstep (se 1 (by rfl) ⟨2426891, by rfl⟩ : syracuseStep 3235855 = 4853783) B4853783
theorem B4314473 : Blo 2127435 4314473 := bstep (se 2 (by rfl) ⟨1617927, by rfl⟩ : syracuseStep 4314473 = 3235855) B3235855
theorem B2876315 : Blo 2127435 2876315 := bstep (se 1 (by rfl) ⟨2157236, by rfl⟩ : syracuseStep 2876315 = 4314473) B4314473
theorem B30680693 : Blo 2127435 30680693 := bstep (se 5 (by rfl) ⟨1438157, by rfl⟩ : syracuseStep 30680693 = 2876315) B2876315
theorem B20453795 : Blo 2127435 20453795 := bstep (se 1 (by rfl) ⟨15340346, by rfl⟩ : syracuseStep 20453795 = 30680693) B30680693
theorem B13635863 : Blo 2127435 13635863 := bstep (se 1 (by rfl) ⟨10226897, by rfl⟩ : syracuseStep 13635863 = 20453795) B20453795
theorem B9090575 : Blo 2127435 9090575 := bstep (se 1 (by rfl) ⟨6817931, by rfl⟩ : syracuseStep 9090575 = 13635863) B13635863
theorem B6060383 : Blo 2127435 6060383 := bstep (se 1 (by rfl) ⟨4545287, by rfl⟩ : syracuseStep 6060383 = 9090575) B9090575
theorem B4040255 : Blo 2127435 4040255 := bstep (se 1 (by rfl) ⟨3030191, by rfl⟩ : syracuseStep 4040255 = 6060383) B6060383
theorem B2693503 : Blo 2127435 2693503 := bstep (se 1 (by rfl) ⟨2020127, by rfl⟩ : syracuseStep 2693503 = 4040255) B4040255
theorem B3591337 : Blo 2127435 3591337 := bstep (se 2 (by rfl) ⟨1346751, by rfl⟩ : syracuseStep 3591337 = 2693503) B2693503
theorem B4788449 : Blo 2127435 4788449 := bstep (se 2 (by rfl) ⟨1795668, by rfl⟩ : syracuseStep 4788449 = 3591337) B3591337
theorem B3192299 : Blo 2127435 3192299 := bstep (se 1 (by rfl) ⟨2394224, by rfl⟩ : syracuseStep 3192299 = 4788449) B4788449
theorem B2128199 : Blo 2127435 2128199 := bstep (se 1 (by rfl) ⟨1596149, by rfl⟩ : syracuseStep 2128199 = 3192299) B3192299
theorem B2394229 : Blo 2127435 2394229 := bbase (se 5 (by rfl) ⟨112229, by rfl⟩ : syracuseStep 2394229 = 224459) (by norm_num)
theorem B3192305 : Blo 2127435 3192305 := bstep (se 2 (by rfl) ⟨1197114, by rfl⟩ : syracuseStep 3192305 = 2394229) B2394229
theorem B2128203 : Blo 2127435 2128203 := bstep (se 1 (by rfl) ⟨1596152, by rfl⟩ : syracuseStep 2128203 = 3192305) B3192305
theorem B2693513 : Blo 2127435 2693513 := bbase (se 2 (by rfl) ⟨1010067, by rfl⟩ : syracuseStep 2693513 = 2020135) (by norm_num)
theorem B7182701 : Blo 2127435 7182701 := bstep (se 3 (by rfl) ⟨1346756, by rfl⟩ : syracuseStep 7182701 = 2693513) B2693513
theorem B4788467 : Blo 2127435 4788467 := bstep (se 1 (by rfl) ⟨3591350, by rfl⟩ : syracuseStep 4788467 = 7182701) B7182701
theorem B3192311 : Blo 2127435 3192311 := bstep (se 1 (by rfl) ⟨2394233, by rfl⟩ : syracuseStep 3192311 = 4788467) B4788467
theorem B2128207 : Blo 2127435 2128207 := bstep (se 1 (by rfl) ⟨1596155, by rfl⟩ : syracuseStep 2128207 = 3192311) B3192311
theorem B3192317 : Blo 2127435 3192317 := bbase (se 3 (by rfl) ⟨598559, by rfl⟩ : syracuseStep 3192317 = 1197119) (by norm_num)
theorem B2128211 : Blo 2127435 2128211 := bstep (se 1 (by rfl) ⟨1596158, by rfl⟩ : syracuseStep 2128211 = 3192317) B3192317
theorem B4788485 : Blo 2127435 4788485 := bbase (se 4 (by rfl) ⟨448920, by rfl⟩ : syracuseStep 4788485 = 897841) (by norm_num)
theorem B3192323 : Blo 2127435 3192323 := bstep (se 1 (by rfl) ⟨2394242, by rfl⟩ : syracuseStep 3192323 = 4788485) B4788485
theorem B2128215 : Blo 2127435 2128215 := bstep (se 1 (by rfl) ⟨1596161, by rfl⟩ : syracuseStep 2128215 = 3192323) B3192323
theorem B4040293 : Blo 2127435 4040293 := bbase (se 4 (by rfl) ⟨378777, by rfl⟩ : syracuseStep 4040293 = 757555) (by norm_num)
theorem B5387057 : Blo 2127435 5387057 := bstep (se 2 (by rfl) ⟨2020146, by rfl⟩ : syracuseStep 5387057 = 4040293) B4040293
theorem B3591371 : Blo 2127435 3591371 := bstep (se 1 (by rfl) ⟨2693528, by rfl⟩ : syracuseStep 3591371 = 5387057) B5387057
theorem B2394247 : Blo 2127435 2394247 := bstep (se 1 (by rfl) ⟨1795685, by rfl⟩ : syracuseStep 2394247 = 3591371) B3591371
theorem B3192329 : Blo 2127435 3192329 := bstep (se 2 (by rfl) ⟨1197123, by rfl⟩ : syracuseStep 3192329 = 2394247) B2394247
theorem B2128219 : Blo 2127435 2128219 := bstep (se 1 (by rfl) ⟨1596164, by rfl⟩ : syracuseStep 2128219 = 3192329) B3192329
theorem B10774133 : Blo 2127435 10774133 := bbase (se 5 (by rfl) ⟨505037, by rfl⟩ : syracuseStep 10774133 = 1010075) (by norm_num)
theorem B7182755 : Blo 2127435 7182755 := bstep (se 1 (by rfl) ⟨5387066, by rfl⟩ : syracuseStep 7182755 = 10774133) B10774133
theorem B4788503 : Blo 2127435 4788503 := bstep (se 1 (by rfl) ⟨3591377, by rfl⟩ : syracuseStep 4788503 = 7182755) B7182755
theorem B3192335 : Blo 2127435 3192335 := bstep (se 1 (by rfl) ⟨2394251, by rfl⟩ : syracuseStep 3192335 = 4788503) B4788503
theorem B2128223 : Blo 2127435 2128223 := bstep (se 1 (by rfl) ⟨1596167, by rfl⟩ : syracuseStep 2128223 = 3192335) B3192335
theorem B3192341 : Blo 2127435 3192341 := bbase (se 6 (by rfl) ⟨74820, by rfl⟩ : syracuseStep 3192341 = 149641) (by norm_num)
theorem B2128227 : Blo 2127435 2128227 := bstep (se 1 (by rfl) ⟨1596170, by rfl⟩ : syracuseStep 2128227 = 3192341) B3192341
theorem B5113525 : Blo 2127435 5113525 := bbase (se 5 (by rfl) ⟨239696, by rfl⟩ : syracuseStep 5113525 = 479393) (by norm_num)
theorem B6818033 : Blo 2127435 6818033 := bstep (se 2 (by rfl) ⟨2556762, by rfl⟩ : syracuseStep 6818033 = 5113525) B5113525
theorem B18181421 : Blo 2127435 18181421 := bstep (se 3 (by rfl) ⟨3409016, by rfl⟩ : syracuseStep 18181421 = 6818033) B6818033
theorem B12120947 : Blo 2127435 12120947 := bstep (se 1 (by rfl) ⟨9090710, by rfl⟩ : syracuseStep 12120947 = 18181421) B18181421
theorem B8080631 : Blo 2127435 8080631 := bstep (se 1 (by rfl) ⟨6060473, by rfl⟩ : syracuseStep 8080631 = 12120947) B12120947
theorem B5387087 : Blo 2127435 5387087 := bstep (se 1 (by rfl) ⟨4040315, by rfl⟩ : syracuseStep 5387087 = 8080631) B8080631
theorem B3591391 : Blo 2127435 3591391 := bstep (se 1 (by rfl) ⟨2693543, by rfl⟩ : syracuseStep 3591391 = 5387087) B5387087
theorem B4788521 : Blo 2127435 4788521 := bstep (se 2 (by rfl) ⟨1795695, by rfl⟩ : syracuseStep 4788521 = 3591391) B3591391
theorem B3192347 : Blo 2127435 3192347 := bstep (se 1 (by rfl) ⟨2394260, by rfl⟩ : syracuseStep 3192347 = 4788521) B4788521
theorem B2128231 : Blo 2127435 2128231 := bstep (se 1 (by rfl) ⟨1596173, by rfl⟩ : syracuseStep 2128231 = 3192347) B3192347
theorem B2394265 : Blo 2127435 2394265 := bbase (se 2 (by rfl) ⟨897849, by rfl⟩ : syracuseStep 2394265 = 1795699) (by norm_num)
theorem B3192353 : Blo 2127435 3192353 := bstep (se 2 (by rfl) ⟨1197132, by rfl⟩ : syracuseStep 3192353 = 2394265) B2394265
theorem B2128235 : Blo 2127435 2128235 := bstep (se 1 (by rfl) ⟨1596176, by rfl⟩ : syracuseStep 2128235 = 3192353) B3192353
theorem B8080661 : Blo 2127435 8080661 := bbase (se 6 (by rfl) ⟨189390, by rfl⟩ : syracuseStep 8080661 = 378781) (by norm_num)
theorem B5387107 : Blo 2127435 5387107 := bstep (se 1 (by rfl) ⟨4040330, by rfl⟩ : syracuseStep 5387107 = 8080661) B8080661
theorem B7182809 : Blo 2127435 7182809 := bstep (se 2 (by rfl) ⟨2693553, by rfl⟩ : syracuseStep 7182809 = 5387107) B5387107
theorem B4788539 : Blo 2127435 4788539 := bstep (se 1 (by rfl) ⟨3591404, by rfl⟩ : syracuseStep 4788539 = 7182809) B7182809
theorem B3192359 : Blo 2127435 3192359 := bstep (se 1 (by rfl) ⟨2394269, by rfl⟩ : syracuseStep 3192359 = 4788539) B4788539
theorem B2128239 : Blo 2127435 2128239 := bstep (se 1 (by rfl) ⟨1596179, by rfl⟩ : syracuseStep 2128239 = 3192359) B3192359
theorem B3192365 : Blo 2127435 3192365 := bbase (se 3 (by rfl) ⟨598568, by rfl⟩ : syracuseStep 3192365 = 1197137) (by norm_num)
theorem B2128243 : Blo 2127435 2128243 := bstep (se 1 (by rfl) ⟨1596182, by rfl⟩ : syracuseStep 2128243 = 3192365) B3192365
theorem B4788557 : Blo 2127435 4788557 := bbase (se 3 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 4788557 = 1795709) (by norm_num)
theorem B3192371 : Blo 2127435 3192371 := bstep (se 1 (by rfl) ⟨2394278, by rfl⟩ : syracuseStep 3192371 = 4788557) B4788557
theorem B2128247 : Blo 2127435 2128247 := bstep (se 1 (by rfl) ⟨1596185, by rfl⟩ : syracuseStep 2128247 = 3192371) B3192371
theorem B2693569 : Blo 2127435 2693569 := bbase (se 2 (by rfl) ⟨1010088, by rfl⟩ : syracuseStep 2693569 = 2020177) (by norm_num)
theorem B3591425 : Blo 2127435 3591425 := bstep (se 2 (by rfl) ⟨1346784, by rfl⟩ : syracuseStep 3591425 = 2693569) B2693569
theorem B2394283 : Blo 2127435 2394283 := bstep (se 1 (by rfl) ⟨1795712, by rfl⟩ : syracuseStep 2394283 = 3591425) B3591425
theorem B3192377 : Blo 2127435 3192377 := bstep (se 2 (by rfl) ⟨1197141, by rfl⟩ : syracuseStep 3192377 = 2394283) B2394283
theorem B2128251 : Blo 2127435 2128251 := bstep (se 1 (by rfl) ⟨1596188, by rfl⟩ : syracuseStep 2128251 = 3192377) B3192377
theorem B3370205 : Blo 2127435 3370205 := bbase (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) (by norm_num)
theorem B8987213 : Blo 2127435 8987213 := bstep (se 3 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 8987213 = 3370205) B3370205
theorem B5991475 : Blo 2127435 5991475 := bstep (se 1 (by rfl) ⟨4493606, by rfl⟩ : syracuseStep 5991475 = 8987213) B8987213
theorem B7988633 : Blo 2127435 7988633 := bstep (se 2 (by rfl) ⟨2995737, by rfl⟩ : syracuseStep 7988633 = 5991475) B5991475
theorem B5325755 : Blo 2127435 5325755 := bstep (se 1 (by rfl) ⟨3994316, by rfl⟩ : syracuseStep 5325755 = 7988633) B7988633
theorem B14202013 : Blo 2127435 14202013 := bstep (se 3 (by rfl) ⟨2662877, by rfl⟩ : syracuseStep 14202013 = 5325755) B5325755
theorem B18936017 : Blo 2127435 18936017 := bstep (se 2 (by rfl) ⟨7101006, by rfl⟩ : syracuseStep 18936017 = 14202013) B14202013
theorem B12624011 : Blo 2127435 12624011 := bstep (se 1 (by rfl) ⟨9468008, by rfl⟩ : syracuseStep 12624011 = 18936017) B18936017
theorem B8416007 : Blo 2127435 8416007 := bstep (se 1 (by rfl) ⟨6312005, by rfl⟩ : syracuseStep 8416007 = 12624011) B12624011
theorem B5610671 : Blo 2127435 5610671 := bstep (se 1 (by rfl) ⟨4208003, by rfl⟩ : syracuseStep 5610671 = 8416007) B8416007
theorem B3740447 : Blo 2127435 3740447 := bstep (se 1 (by rfl) ⟨2805335, by rfl⟩ : syracuseStep 3740447 = 5610671) B5610671
theorem B2493631 : Blo 2127435 2493631 := bstep (se 1 (by rfl) ⟨1870223, by rfl⟩ : syracuseStep 2493631 = 3740447) B3740447
theorem B13299365 : Blo 2127435 13299365 := bstep (se 4 (by rfl) ⟨1246815, by rfl⟩ : syracuseStep 13299365 = 2493631) B2493631
theorem B35464973 : Blo 2127435 35464973 := bstep (se 3 (by rfl) ⟨6649682, by rfl⟩ : syracuseStep 35464973 = 13299365) B13299365
theorem B94573261 : Blo 2127435 94573261 := bstep (se 3 (by rfl) ⟨17732486, by rfl⟩ : syracuseStep 94573261 = 35464973) B35464973
theorem B126097681 : Blo 2127435 126097681 := bstep (se 2 (by rfl) ⟨47286630, by rfl⟩ : syracuseStep 126097681 = 94573261) B94573261
theorem B168130241 : Blo 2127435 168130241 := bstep (se 2 (by rfl) ⟨63048840, by rfl⟩ : syracuseStep 168130241 = 126097681) B126097681
theorem B112086827 : Blo 2127435 112086827 := bstep (se 1 (by rfl) ⟨84065120, by rfl⟩ : syracuseStep 112086827 = 168130241) B168130241
theorem B74724551 : Blo 2127435 74724551 := bstep (se 1 (by rfl) ⟨56043413, by rfl⟩ : syracuseStep 74724551 = 112086827) B112086827
theorem B49816367 : Blo 2127435 49816367 := bstep (se 1 (by rfl) ⟨37362275, by rfl⟩ : syracuseStep 49816367 = 74724551) B74724551
theorem B33210911 : Blo 2127435 33210911 := bstep (se 1 (by rfl) ⟨24908183, by rfl⟩ : syracuseStep 33210911 = 49816367) B49816367
theorem B88562429 : Blo 2127435 88562429 := bstep (se 3 (by rfl) ⟨16605455, by rfl⟩ : syracuseStep 88562429 = 33210911) B33210911
theorem B59041619 : Blo 2127435 59041619 := bstep (se 1 (by rfl) ⟨44281214, by rfl⟩ : syracuseStep 59041619 = 88562429) B88562429
theorem B39361079 : Blo 2127435 39361079 := bstep (se 1 (by rfl) ⟨29520809, by rfl⟩ : syracuseStep 39361079 = 59041619) B59041619
theorem B26240719 : Blo 2127435 26240719 := bstep (se 1 (by rfl) ⟨19680539, by rfl⟩ : syracuseStep 26240719 = 39361079) B39361079
theorem B34987625 : Blo 2127435 34987625 := bstep (se 2 (by rfl) ⟨13120359, by rfl⟩ : syracuseStep 34987625 = 26240719) B26240719
theorem B23325083 : Blo 2127435 23325083 := bstep (se 1 (by rfl) ⟨17493812, by rfl⟩ : syracuseStep 23325083 = 34987625) B34987625
theorem B15550055 : Blo 2127435 15550055 := bstep (se 1 (by rfl) ⟨11662541, by rfl⟩ : syracuseStep 15550055 = 23325083) B23325083
theorem B10366703 : Blo 2127435 10366703 := bstep (se 1 (by rfl) ⟨7775027, by rfl⟩ : syracuseStep 10366703 = 15550055) B15550055
theorem B6911135 : Blo 2127435 6911135 := bstep (se 1 (by rfl) ⟨5183351, by rfl⟩ : syracuseStep 6911135 = 10366703) B10366703
theorem B4607423 : Blo 2127435 4607423 := bstep (se 1 (by rfl) ⟨3455567, by rfl⟩ : syracuseStep 4607423 = 6911135) B6911135
theorem B3071615 : Blo 2127435 3071615 := bstep (se 1 (by rfl) ⟨2303711, by rfl⟩ : syracuseStep 3071615 = 4607423) B4607423
theorem B8190973 : Blo 2127435 8190973 := bstep (se 3 (by rfl) ⟨1535807, by rfl⟩ : syracuseStep 8190973 = 3071615) B3071615
theorem B43685189 : Blo 2127435 43685189 := bstep (se 4 (by rfl) ⟨4095486, by rfl⟩ : syracuseStep 43685189 = 8190973) B8190973
theorem B29123459 : Blo 2127435 29123459 := bstep (se 1 (by rfl) ⟨21842594, by rfl⟩ : syracuseStep 29123459 = 43685189) B43685189
theorem B19415639 : Blo 2127435 19415639 := bstep (se 1 (by rfl) ⟨14561729, by rfl⟩ : syracuseStep 19415639 = 29123459) B29123459
theorem B12943759 : Blo 2127435 12943759 := bstep (se 1 (by rfl) ⟨9707819, by rfl⟩ : syracuseStep 12943759 = 19415639) B19415639
theorem B17258345 : Blo 2127435 17258345 := bstep (se 2 (by rfl) ⟨6471879, by rfl⟩ : syracuseStep 17258345 = 12943759) B12943759
theorem B11505563 : Blo 2127435 11505563 := bstep (se 1 (by rfl) ⟨8629172, by rfl⟩ : syracuseStep 11505563 = 17258345) B17258345
theorem B7670375 : Blo 2127435 7670375 := bstep (se 1 (by rfl) ⟨5752781, by rfl⟩ : syracuseStep 7670375 = 11505563) B11505563
theorem B5113583 : Blo 2127435 5113583 := bstep (se 1 (by rfl) ⟨3835187, by rfl⟩ : syracuseStep 5113583 = 7670375) B7670375
theorem B3409055 : Blo 2127435 3409055 := bstep (se 1 (by rfl) ⟨2556791, by rfl⟩ : syracuseStep 3409055 = 5113583) B5113583
theorem B2272703 : Blo 2127435 2272703 := bstep (se 1 (by rfl) ⟨1704527, by rfl⟩ : syracuseStep 2272703 = 3409055) B3409055
theorem B24242165 : Blo 2127435 24242165 := bstep (se 5 (by rfl) ⟨1136351, by rfl⟩ : syracuseStep 24242165 = 2272703) B2272703
theorem B16161443 : Blo 2127435 16161443 := bstep (se 1 (by rfl) ⟨12121082, by rfl⟩ : syracuseStep 16161443 = 24242165) B24242165
theorem B10774295 : Blo 2127435 10774295 := bstep (se 1 (by rfl) ⟨8080721, by rfl⟩ : syracuseStep 10774295 = 16161443) B16161443
theorem B7182863 : Blo 2127435 7182863 := bstep (se 1 (by rfl) ⟨5387147, by rfl⟩ : syracuseStep 7182863 = 10774295) B10774295
theorem B4788575 : Blo 2127435 4788575 := bstep (se 1 (by rfl) ⟨3591431, by rfl⟩ : syracuseStep 4788575 = 7182863) B7182863
theorem B3192383 : Blo 2127435 3192383 := bstep (se 1 (by rfl) ⟨2394287, by rfl⟩ : syracuseStep 3192383 = 4788575) B4788575
theorem B2128255 : Blo 2127435 2128255 := bstep (se 1 (by rfl) ⟨1596191, by rfl⟩ : syracuseStep 2128255 = 3192383) B3192383
theorem B3192389 : Blo 2127435 3192389 := bbase (se 4 (by rfl) ⟨299286, by rfl⟩ : syracuseStep 3192389 = 598573) (by norm_num)
theorem B2128259 : Blo 2127435 2128259 := bstep (se 1 (by rfl) ⟨1596194, by rfl⟩ : syracuseStep 2128259 = 3192389) B3192389
theorem B3591445 : Blo 2127435 3591445 := bbase (se 6 (by rfl) ⟨84174, by rfl⟩ : syracuseStep 3591445 = 168349) (by norm_num)
theorem B4788593 : Blo 2127435 4788593 := bstep (se 2 (by rfl) ⟨1795722, by rfl⟩ : syracuseStep 4788593 = 3591445) B3591445
theorem B3192395 : Blo 2127435 3192395 := bstep (se 1 (by rfl) ⟨2394296, by rfl⟩ : syracuseStep 3192395 = 4788593) B4788593
theorem B2128263 : Blo 2127435 2128263 := bstep (se 1 (by rfl) ⟨1596197, by rfl⟩ : syracuseStep 2128263 = 3192395) B3192395
theorem B2394301 : Blo 2127435 2394301 := bbase (se 3 (by rfl) ⟨448931, by rfl⟩ : syracuseStep 2394301 = 897863) (by norm_num)
theorem B3192401 : Blo 2127435 3192401 := bstep (se 2 (by rfl) ⟨1197150, by rfl⟩ : syracuseStep 3192401 = 2394301) B2394301
theorem B2128267 : Blo 2127435 2128267 := bstep (se 1 (by rfl) ⟨1596200, by rfl⟩ : syracuseStep 2128267 = 3192401) B3192401
theorem B7182917 : Blo 2127435 7182917 := bbase (se 4 (by rfl) ⟨673398, by rfl⟩ : syracuseStep 7182917 = 1346797) (by norm_num)
theorem B4788611 : Blo 2127435 4788611 := bstep (se 1 (by rfl) ⟨3591458, by rfl⟩ : syracuseStep 4788611 = 7182917) B7182917
theorem B3192407 : Blo 2127435 3192407 := bstep (se 1 (by rfl) ⟨2394305, by rfl⟩ : syracuseStep 3192407 = 4788611) B4788611
theorem B2128271 : Blo 2127435 2128271 := bstep (se 1 (by rfl) ⟨1596203, by rfl⟩ : syracuseStep 2128271 = 3192407) B3192407
theorem B3192413 : Blo 2127435 3192413 := bbase (se 3 (by rfl) ⟨598577, by rfl⟩ : syracuseStep 3192413 = 1197155) (by norm_num)
theorem B2128275 : Blo 2127435 2128275 := bstep (se 1 (by rfl) ⟨1596206, by rfl⟩ : syracuseStep 2128275 = 3192413) B3192413
theorem B4788629 : Blo 2127435 4788629 := bbase (se 6 (by rfl) ⟨112233, by rfl⟩ : syracuseStep 4788629 = 224467) (by norm_num)
theorem B3192419 : Blo 2127435 3192419 := bstep (se 1 (by rfl) ⟨2394314, by rfl⟩ : syracuseStep 3192419 = 4788629) B4788629
theorem B2128279 : Blo 2127435 2128279 := bstep (se 1 (by rfl) ⟨1596209, by rfl⟩ : syracuseStep 2128279 = 3192419) B3192419
theorem B2876429 : Blo 2127435 2876429 := bbase (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) (by norm_num)
theorem B7670477 : Blo 2127435 7670477 := bstep (se 3 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 7670477 = 2876429) B2876429
theorem B5113651 : Blo 2127435 5113651 := bstep (se 1 (by rfl) ⟨3835238, by rfl⟩ : syracuseStep 5113651 = 7670477) B7670477
theorem B6818201 : Blo 2127435 6818201 := bstep (se 2 (by rfl) ⟨2556825, by rfl⟩ : syracuseStep 6818201 = 5113651) B5113651
theorem B4545467 : Blo 2127435 4545467 := bstep (se 1 (by rfl) ⟨3409100, by rfl⟩ : syracuseStep 4545467 = 6818201) B6818201
theorem B3030311 : Blo 2127435 3030311 := bstep (se 1 (by rfl) ⟨2272733, by rfl⟩ : syracuseStep 3030311 = 4545467) B4545467
theorem B8080829 : Blo 2127435 8080829 := bstep (se 3 (by rfl) ⟨1515155, by rfl⟩ : syracuseStep 8080829 = 3030311) B3030311
theorem B5387219 : Blo 2127435 5387219 := bstep (se 1 (by rfl) ⟨4040414, by rfl⟩ : syracuseStep 5387219 = 8080829) B8080829
theorem B3591479 : Blo 2127435 3591479 := bstep (se 1 (by rfl) ⟨2693609, by rfl⟩ : syracuseStep 3591479 = 5387219) B5387219
theorem B2394319 : Blo 2127435 2394319 := bstep (se 1 (by rfl) ⟨1795739, by rfl⟩ : syracuseStep 2394319 = 3591479) B3591479
theorem B3192425 : Blo 2127435 3192425 := bstep (se 2 (by rfl) ⟨1197159, by rfl⟩ : syracuseStep 3192425 = 2394319) B2394319
theorem B2128283 : Blo 2127435 2128283 := bstep (se 1 (by rfl) ⟨1596212, by rfl⟩ : syracuseStep 2128283 = 3192425) B3192425
theorem B9090949 : Blo 2127435 9090949 := bbase (se 4 (by rfl) ⟨852276, by rfl⟩ : syracuseStep 9090949 = 1704553) (by norm_num)
theorem B12121265 : Blo 2127435 12121265 := bstep (se 2 (by rfl) ⟨4545474, by rfl⟩ : syracuseStep 12121265 = 9090949) B9090949
theorem B8080843 : Blo 2127435 8080843 := bstep (se 1 (by rfl) ⟨6060632, by rfl⟩ : syracuseStep 8080843 = 12121265) B12121265
theorem B10774457 : Blo 2127435 10774457 := bstep (se 2 (by rfl) ⟨4040421, by rfl⟩ : syracuseStep 10774457 = 8080843) B8080843
theorem B7182971 : Blo 2127435 7182971 := bstep (se 1 (by rfl) ⟨5387228, by rfl⟩ : syracuseStep 7182971 = 10774457) B10774457
theorem B4788647 : Blo 2127435 4788647 := bstep (se 1 (by rfl) ⟨3591485, by rfl⟩ : syracuseStep 4788647 = 7182971) B7182971
theorem B3192431 : Blo 2127435 3192431 := bstep (se 1 (by rfl) ⟨2394323, by rfl⟩ : syracuseStep 3192431 = 4788647) B4788647
theorem B2128287 : Blo 2127435 2128287 := bstep (se 1 (by rfl) ⟨1596215, by rfl⟩ : syracuseStep 2128287 = 3192431) B3192431
theorem B3192437 : Blo 2127435 3192437 := bbase (se 5 (by rfl) ⟨149645, by rfl⟩ : syracuseStep 3192437 = 299291) (by norm_num)
theorem B2128291 : Blo 2127435 2128291 := bstep (se 1 (by rfl) ⟨1596218, by rfl⟩ : syracuseStep 2128291 = 3192437) B3192437
theorem B4040437 : Blo 2127435 4040437 := bbase (se 5 (by rfl) ⟨189395, by rfl⟩ : syracuseStep 4040437 = 378791) (by norm_num)
theorem B5387249 : Blo 2127435 5387249 := bstep (se 2 (by rfl) ⟨2020218, by rfl⟩ : syracuseStep 5387249 = 4040437) B4040437
theorem B3591499 : Blo 2127435 3591499 := bstep (se 1 (by rfl) ⟨2693624, by rfl⟩ : syracuseStep 3591499 = 5387249) B5387249
theorem B4788665 : Blo 2127435 4788665 := bstep (se 2 (by rfl) ⟨1795749, by rfl⟩ : syracuseStep 4788665 = 3591499) B3591499
theorem B3192443 : Blo 2127435 3192443 := bstep (se 1 (by rfl) ⟨2394332, by rfl⟩ : syracuseStep 3192443 = 4788665) B4788665
theorem B2128295 : Blo 2127435 2128295 := bstep (se 1 (by rfl) ⟨1596221, by rfl⟩ : syracuseStep 2128295 = 3192443) B3192443
theorem B2394337 : Blo 2127435 2394337 := bbase (se 2 (by rfl) ⟨897876, by rfl⟩ : syracuseStep 2394337 = 1795753) (by norm_num)
theorem B3192449 : Blo 2127435 3192449 := bstep (se 2 (by rfl) ⟨1197168, by rfl⟩ : syracuseStep 3192449 = 2394337) B2394337
theorem B2128299 : Blo 2127435 2128299 := bstep (se 1 (by rfl) ⟨1596224, by rfl⟩ : syracuseStep 2128299 = 3192449) B3192449
theorem B5387269 : Blo 2127435 5387269 := bbase (se 4 (by rfl) ⟨505056, by rfl⟩ : syracuseStep 5387269 = 1010113) (by norm_num)
theorem B7183025 : Blo 2127435 7183025 := bstep (se 2 (by rfl) ⟨2693634, by rfl⟩ : syracuseStep 7183025 = 5387269) B5387269
theorem B4788683 : Blo 2127435 4788683 := bstep (se 1 (by rfl) ⟨3591512, by rfl⟩ : syracuseStep 4788683 = 7183025) B7183025
theorem B3192455 : Blo 2127435 3192455 := bstep (se 1 (by rfl) ⟨2394341, by rfl⟩ : syracuseStep 3192455 = 4788683) B4788683
theorem B2128303 : Blo 2127435 2128303 := bstep (se 1 (by rfl) ⟨1596227, by rfl⟩ : syracuseStep 2128303 = 3192455) B3192455
theorem B3192461 : Blo 2127435 3192461 := bbase (se 3 (by rfl) ⟨598586, by rfl⟩ : syracuseStep 3192461 = 1197173) (by norm_num)
theorem B2128307 : Blo 2127435 2128307 := bstep (se 1 (by rfl) ⟨1596230, by rfl⟩ : syracuseStep 2128307 = 3192461) B3192461
theorem B4788701 : Blo 2127435 4788701 := bbase (se 3 (by rfl) ⟨897881, by rfl⟩ : syracuseStep 4788701 = 1795763) (by norm_num)
theorem B3192467 : Blo 2127435 3192467 := bstep (se 1 (by rfl) ⟨2394350, by rfl⟩ : syracuseStep 3192467 = 4788701) B4788701
theorem B2128311 : Blo 2127435 2128311 := bstep (se 1 (by rfl) ⟨1596233, by rfl⟩ : syracuseStep 2128311 = 3192467) B3192467
theorem B3591533 : Blo 2127435 3591533 := bbase (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) (by norm_num)
theorem B2394355 : Blo 2127435 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B3192473 : Blo 2127435 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B2128315 : Blo 2127435 2128315 := bstep (se 1 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 2128315 = 3192473) B3192473
theorem B5535317 : Blo 2127435 5535317 := bbase (se 8 (by rfl) ⟨32433, by rfl⟩ : syracuseStep 5535317 = 64867) (by norm_num)
theorem B3690211 : Blo 2127435 3690211 := bstep (se 1 (by rfl) ⟨2767658, by rfl⟩ : syracuseStep 3690211 = 5535317) B5535317
theorem B4920281 : Blo 2127435 4920281 := bstep (se 2 (by rfl) ⟨1845105, by rfl⟩ : syracuseStep 4920281 = 3690211) B3690211
theorem B3280187 : Blo 2127435 3280187 := bstep (se 1 (by rfl) ⟨2460140, by rfl⟩ : syracuseStep 3280187 = 4920281) B4920281
theorem B8747165 : Blo 2127435 8747165 := bstep (se 3 (by rfl) ⟨1640093, by rfl⟩ : syracuseStep 8747165 = 3280187) B3280187
theorem B5831443 : Blo 2127435 5831443 := bstep (se 1 (by rfl) ⟨4373582, by rfl⟩ : syracuseStep 5831443 = 8747165) B8747165
theorem B7775257 : Blo 2127435 7775257 := bstep (se 2 (by rfl) ⟨2915721, by rfl⟩ : syracuseStep 7775257 = 5831443) B5831443
theorem B10367009 : Blo 2127435 10367009 := bstep (se 2 (by rfl) ⟨3887628, by rfl⟩ : syracuseStep 10367009 = 7775257) B7775257
theorem B6911339 : Blo 2127435 6911339 := bstep (se 1 (by rfl) ⟨5183504, by rfl⟩ : syracuseStep 6911339 = 10367009) B10367009
theorem B18430237 : Blo 2127435 18430237 := bstep (se 3 (by rfl) ⟨3455669, by rfl⟩ : syracuseStep 18430237 = 6911339) B6911339
theorem B98294597 : Blo 2127435 98294597 := bstep (se 4 (by rfl) ⟨9215118, by rfl⟩ : syracuseStep 98294597 = 18430237) B18430237
theorem B65529731 : Blo 2127435 65529731 := bstep (se 1 (by rfl) ⟨49147298, by rfl⟩ : syracuseStep 65529731 = 98294597) B98294597
theorem B43686487 : Blo 2127435 43686487 := bstep (se 1 (by rfl) ⟨32764865, by rfl⟩ : syracuseStep 43686487 = 65529731) B65529731
theorem B58248649 : Blo 2127435 58248649 := bstep (se 2 (by rfl) ⟨21843243, by rfl⟩ : syracuseStep 58248649 = 43686487) B43686487
theorem B77664865 : Blo 2127435 77664865 := bstep (se 2 (by rfl) ⟨29124324, by rfl⟩ : syracuseStep 77664865 = 58248649) B58248649
theorem B103553153 : Blo 2127435 103553153 := bstep (se 2 (by rfl) ⟨38832432, by rfl⟩ : syracuseStep 103553153 = 77664865) B77664865
theorem B69035435 : Blo 2127435 69035435 := bstep (se 1 (by rfl) ⟨51776576, by rfl⟩ : syracuseStep 69035435 = 103553153) B103553153
theorem B46023623 : Blo 2127435 46023623 := bstep (se 1 (by rfl) ⟨34517717, by rfl⟩ : syracuseStep 46023623 = 69035435) B69035435
theorem B30682415 : Blo 2127435 30682415 := bstep (se 1 (by rfl) ⟨23011811, by rfl⟩ : syracuseStep 30682415 = 46023623) B46023623
theorem B20454943 : Blo 2127435 20454943 := bstep (se 1 (by rfl) ⟨15341207, by rfl⟩ : syracuseStep 20454943 = 30682415) B30682415
theorem B27273257 : Blo 2127435 27273257 := bstep (se 2 (by rfl) ⟨10227471, by rfl⟩ : syracuseStep 27273257 = 20454943) B20454943
theorem B18182171 : Blo 2127435 18182171 := bstep (se 1 (by rfl) ⟨13636628, by rfl⟩ : syracuseStep 18182171 = 27273257) B27273257
theorem B12121447 : Blo 2127435 12121447 := bstep (se 1 (by rfl) ⟨9091085, by rfl⟩ : syracuseStep 12121447 = 18182171) B18182171
theorem B16161929 : Blo 2127435 16161929 := bstep (se 2 (by rfl) ⟨6060723, by rfl⟩ : syracuseStep 16161929 = 12121447) B12121447
theorem B10774619 : Blo 2127435 10774619 := bstep (se 1 (by rfl) ⟨8080964, by rfl⟩ : syracuseStep 10774619 = 16161929) B16161929
theorem B7183079 : Blo 2127435 7183079 := bstep (se 1 (by rfl) ⟨5387309, by rfl⟩ : syracuseStep 7183079 = 10774619) B10774619
theorem B4788719 : Blo 2127435 4788719 := bstep (se 1 (by rfl) ⟨3591539, by rfl⟩ : syracuseStep 4788719 = 7183079) B7183079
theorem B3192479 : Blo 2127435 3192479 := bstep (se 1 (by rfl) ⟨2394359, by rfl⟩ : syracuseStep 3192479 = 4788719) B4788719
theorem B2128319 : Blo 2127435 2128319 := bstep (se 1 (by rfl) ⟨1596239, by rfl⟩ : syracuseStep 2128319 = 3192479) B3192479
theorem B3192485 : Blo 2127435 3192485 := bbase (se 4 (by rfl) ⟨299295, by rfl⟩ : syracuseStep 3192485 = 598591) (by norm_num)
theorem B2128323 : Blo 2127435 2128323 := bstep (se 1 (by rfl) ⟨1596242, by rfl⟩ : syracuseStep 2128323 = 3192485) B3192485
theorem B2693665 : Blo 2127435 2693665 := bbase (se 2 (by rfl) ⟨1010124, by rfl⟩ : syracuseStep 2693665 = 2020249) (by norm_num)
theorem B3591553 : Blo 2127435 3591553 := bstep (se 2 (by rfl) ⟨1346832, by rfl⟩ : syracuseStep 3591553 = 2693665) B2693665
theorem B4788737 : Blo 2127435 4788737 := bstep (se 2 (by rfl) ⟨1795776, by rfl⟩ : syracuseStep 4788737 = 3591553) B3591553
theorem B3192491 : Blo 2127435 3192491 := bstep (se 1 (by rfl) ⟨2394368, by rfl⟩ : syracuseStep 3192491 = 4788737) B4788737
theorem B2128327 : Blo 2127435 2128327 := bstep (se 1 (by rfl) ⟨1596245, by rfl⟩ : syracuseStep 2128327 = 3192491) B3192491
theorem B2394373 : Blo 2127435 2394373 := bbase (se 4 (by rfl) ⟨224472, by rfl⟩ : syracuseStep 2394373 = 448945) (by norm_num)
theorem B3192497 : Blo 2127435 3192497 := bstep (se 2 (by rfl) ⟨1197186, by rfl⟩ : syracuseStep 3192497 = 2394373) B2394373
theorem B2128331 : Blo 2127435 2128331 := bstep (se 1 (by rfl) ⟨1596248, by rfl⟩ : syracuseStep 2128331 = 3192497) B3192497
theorem B2272789 : Blo 2127435 2272789 := bbase (se 6 (by rfl) ⟨53268, by rfl⟩ : syracuseStep 2272789 = 106537) (by norm_num)
theorem B3030385 : Blo 2127435 3030385 := bstep (se 2 (by rfl) ⟨1136394, by rfl⟩ : syracuseStep 3030385 = 2272789) B2272789
theorem B4040513 : Blo 2127435 4040513 := bstep (se 2 (by rfl) ⟨1515192, by rfl⟩ : syracuseStep 4040513 = 3030385) B3030385
theorem B2693675 : Blo 2127435 2693675 := bstep (se 1 (by rfl) ⟨2020256, by rfl⟩ : syracuseStep 2693675 = 4040513) B4040513
theorem B7183133 : Blo 2127435 7183133 := bstep (se 3 (by rfl) ⟨1346837, by rfl⟩ : syracuseStep 7183133 = 2693675) B2693675
theorem B4788755 : Blo 2127435 4788755 := bstep (se 1 (by rfl) ⟨3591566, by rfl⟩ : syracuseStep 4788755 = 7183133) B7183133
theorem B3192503 : Blo 2127435 3192503 := bstep (se 1 (by rfl) ⟨2394377, by rfl⟩ : syracuseStep 3192503 = 4788755) B4788755
theorem B2128335 : Blo 2127435 2128335 := bstep (se 1 (by rfl) ⟨1596251, by rfl⟩ : syracuseStep 2128335 = 3192503) B3192503
theorem B3192509 : Blo 2127435 3192509 := bbase (se 3 (by rfl) ⟨598595, by rfl⟩ : syracuseStep 3192509 = 1197191) (by norm_num)
theorem B2128339 : Blo 2127435 2128339 := bstep (se 1 (by rfl) ⟨1596254, by rfl⟩ : syracuseStep 2128339 = 3192509) B3192509
theorem B4788773 : Blo 2127435 4788773 := bbase (se 4 (by rfl) ⟨448947, by rfl⟩ : syracuseStep 4788773 = 897895) (by norm_num)
theorem B3192515 : Blo 2127435 3192515 := bstep (se 1 (by rfl) ⟨2394386, by rfl⟩ : syracuseStep 3192515 = 4788773) B4788773
theorem B2128343 : Blo 2127435 2128343 := bstep (se 1 (by rfl) ⟨1596257, by rfl⟩ : syracuseStep 2128343 = 3192515) B3192515
theorem B5387381 : Blo 2127435 5387381 := bbase (se 5 (by rfl) ⟨252533, by rfl⟩ : syracuseStep 5387381 = 505067) (by norm_num)
theorem B3591587 : Blo 2127435 3591587 := bstep (se 1 (by rfl) ⟨2693690, by rfl⟩ : syracuseStep 3591587 = 5387381) B5387381
theorem B2394391 : Blo 2127435 2394391 := bstep (se 1 (by rfl) ⟨1795793, by rfl⟩ : syracuseStep 2394391 = 3591587) B3591587
theorem B3192521 : Blo 2127435 3192521 := bstep (se 2 (by rfl) ⟨1197195, by rfl⟩ : syracuseStep 3192521 = 2394391) B2394391
theorem B2128347 : Blo 2127435 2128347 := bstep (se 1 (by rfl) ⟨1596260, by rfl⟩ : syracuseStep 2128347 = 3192521) B3192521
theorem B20455253 : Blo 2127435 20455253 := bbase (se 9 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 20455253 = 119855) (by norm_num)
theorem B13636835 : Blo 2127435 13636835 := bstep (se 1 (by rfl) ⟨10227626, by rfl⟩ : syracuseStep 13636835 = 20455253) B20455253
theorem B9091223 : Blo 2127435 9091223 := bstep (se 1 (by rfl) ⟨6818417, by rfl⟩ : syracuseStep 9091223 = 13636835) B13636835
theorem B6060815 : Blo 2127435 6060815 := bstep (se 1 (by rfl) ⟨4545611, by rfl⟩ : syracuseStep 6060815 = 9091223) B9091223
theorem B4040543 : Blo 2127435 4040543 := bstep (se 1 (by rfl) ⟨3030407, by rfl⟩ : syracuseStep 4040543 = 6060815) B6060815
theorem B10774781 : Blo 2127435 10774781 := bstep (se 3 (by rfl) ⟨2020271, by rfl⟩ : syracuseStep 10774781 = 4040543) B4040543
theorem B7183187 : Blo 2127435 7183187 := bstep (se 1 (by rfl) ⟨5387390, by rfl⟩ : syracuseStep 7183187 = 10774781) B10774781
theorem B4788791 : Blo 2127435 4788791 := bstep (se 1 (by rfl) ⟨3591593, by rfl⟩ : syracuseStep 4788791 = 7183187) B7183187
theorem B3192527 : Blo 2127435 3192527 := bstep (se 1 (by rfl) ⟨2394395, by rfl⟩ : syracuseStep 3192527 = 4788791) B4788791
theorem B2128351 : Blo 2127435 2128351 := bstep (se 1 (by rfl) ⟨1596263, by rfl⟩ : syracuseStep 2128351 = 3192527) B3192527
theorem B3192533 : Blo 2127435 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B2128355 : Blo 2127435 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B4545629 : Blo 2127435 4545629 := bbase (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) (by norm_num)
theorem B3030419 : Blo 2127435 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B8081117 : Blo 2127435 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B5387411 : Blo 2127435 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B3591607 : Blo 2127435 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B4788809 : Blo 2127435 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B3192539 : Blo 2127435 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B2128359 : Blo 2127435 2128359 := bstep (se 1 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 2128359 = 3192539) B3192539
theorem B2394409 : Blo 2127435 2394409 := bbase (se 2 (by rfl) ⟨897903, by rfl⟩ : syracuseStep 2394409 = 1795807) (by norm_num)
theorem B3192545 : Blo 2127435 3192545 := bstep (se 2 (by rfl) ⟨1197204, by rfl⟩ : syracuseStep 3192545 = 2394409) B2394409
theorem B2128363 : Blo 2127435 2128363 := bstep (se 1 (by rfl) ⟨1596272, by rfl⟩ : syracuseStep 2128363 = 3192545) B3192545
theorem B8747365 : Blo 2127435 8747365 := bbase (se 4 (by rfl) ⟨820065, by rfl⟩ : syracuseStep 8747365 = 1640131) (by norm_num)
theorem B11663153 : Blo 2127435 11663153 := bstep (se 2 (by rfl) ⟨4373682, by rfl⟩ : syracuseStep 11663153 = 8747365) B8747365
theorem B7775435 : Blo 2127435 7775435 := bstep (se 1 (by rfl) ⟨5831576, by rfl⟩ : syracuseStep 7775435 = 11663153) B11663153
theorem B5183623 : Blo 2127435 5183623 := bstep (se 1 (by rfl) ⟨3887717, by rfl⟩ : syracuseStep 5183623 = 7775435) B7775435
theorem B6911497 : Blo 2127435 6911497 := bstep (se 2 (by rfl) ⟨2591811, by rfl⟩ : syracuseStep 6911497 = 5183623) B5183623
theorem B36861317 : Blo 2127435 36861317 := bstep (se 4 (by rfl) ⟨3455748, by rfl⟩ : syracuseStep 36861317 = 6911497) B6911497
theorem B24574211 : Blo 2127435 24574211 := bstep (se 1 (by rfl) ⟨18430658, by rfl⟩ : syracuseStep 24574211 = 36861317) B36861317
theorem B16382807 : Blo 2127435 16382807 := bstep (se 1 (by rfl) ⟨12287105, by rfl⟩ : syracuseStep 16382807 = 24574211) B24574211
theorem B10921871 : Blo 2127435 10921871 := bstep (se 1 (by rfl) ⟨8191403, by rfl⟩ : syracuseStep 10921871 = 16382807) B16382807
theorem B7281247 : Blo 2127435 7281247 := bstep (se 1 (by rfl) ⟨5460935, by rfl⟩ : syracuseStep 7281247 = 10921871) B10921871
theorem B9708329 : Blo 2127435 9708329 := bstep (se 2 (by rfl) ⟨3640623, by rfl⟩ : syracuseStep 9708329 = 7281247) B7281247
theorem B6472219 : Blo 2127435 6472219 := bstep (se 1 (by rfl) ⟨4854164, by rfl⟩ : syracuseStep 6472219 = 9708329) B9708329
theorem B8629625 : Blo 2127435 8629625 := bstep (se 2 (by rfl) ⟨3236109, by rfl⟩ : syracuseStep 8629625 = 6472219) B6472219
theorem B23012333 : Blo 2127435 23012333 := bstep (se 3 (by rfl) ⟨4314812, by rfl⟩ : syracuseStep 23012333 = 8629625) B8629625
theorem B15341555 : Blo 2127435 15341555 := bstep (se 1 (by rfl) ⟨11506166, by rfl⟩ : syracuseStep 15341555 = 23012333) B23012333
theorem B10227703 : Blo 2127435 10227703 := bstep (se 1 (by rfl) ⟨7670777, by rfl⟩ : syracuseStep 10227703 = 15341555) B15341555
theorem B13636937 : Blo 2127435 13636937 := bstep (se 2 (by rfl) ⟨5113851, by rfl⟩ : syracuseStep 13636937 = 10227703) B10227703
theorem B9091291 : Blo 2127435 9091291 := bstep (se 1 (by rfl) ⟨6818468, by rfl⟩ : syracuseStep 9091291 = 13636937) B13636937
theorem B12121721 : Blo 2127435 12121721 := bstep (se 2 (by rfl) ⟨4545645, by rfl⟩ : syracuseStep 12121721 = 9091291) B9091291
theorem B8081147 : Blo 2127435 8081147 := bstep (se 1 (by rfl) ⟨6060860, by rfl⟩ : syracuseStep 8081147 = 12121721) B12121721
theorem B5387431 : Blo 2127435 5387431 := bstep (se 1 (by rfl) ⟨4040573, by rfl⟩ : syracuseStep 5387431 = 8081147) B8081147
theorem B7183241 : Blo 2127435 7183241 := bstep (se 2 (by rfl) ⟨2693715, by rfl⟩ : syracuseStep 7183241 = 5387431) B5387431
theorem B4788827 : Blo 2127435 4788827 := bstep (se 1 (by rfl) ⟨3591620, by rfl⟩ : syracuseStep 4788827 = 7183241) B7183241
theorem B3192551 : Blo 2127435 3192551 := bstep (se 1 (by rfl) ⟨2394413, by rfl⟩ : syracuseStep 3192551 = 4788827) B4788827
theorem B2128367 : Blo 2127435 2128367 := bstep (se 1 (by rfl) ⟨1596275, by rfl⟩ : syracuseStep 2128367 = 3192551) B3192551
theorem B3192557 : Blo 2127435 3192557 := bbase (se 3 (by rfl) ⟨598604, by rfl⟩ : syracuseStep 3192557 = 1197209) (by norm_num)
theorem B2128371 : Blo 2127435 2128371 := bstep (se 1 (by rfl) ⟨1596278, by rfl⟩ : syracuseStep 2128371 = 3192557) B3192557
theorem B4788845 : Blo 2127435 4788845 := bbase (se 3 (by rfl) ⟨897908, by rfl⟩ : syracuseStep 4788845 = 1795817) (by norm_num)
theorem B3192563 : Blo 2127435 3192563 := bstep (se 1 (by rfl) ⟨2394422, by rfl⟩ : syracuseStep 3192563 = 4788845) B4788845
theorem B2128375 : Blo 2127435 2128375 := bstep (se 1 (by rfl) ⟨1596281, by rfl⟩ : syracuseStep 2128375 = 3192563) B3192563
theorem B4040597 : Blo 2127435 4040597 := bbase (se 6 (by rfl) ⟨94701, by rfl⟩ : syracuseStep 4040597 = 189403) (by norm_num)
theorem B2693731 : Blo 2127435 2693731 := bstep (se 1 (by rfl) ⟨2020298, by rfl⟩ : syracuseStep 2693731 = 4040597) B4040597
theorem B3591641 : Blo 2127435 3591641 := bstep (se 2 (by rfl) ⟨1346865, by rfl⟩ : syracuseStep 3591641 = 2693731) B2693731
theorem B2394427 : Blo 2127435 2394427 := bstep (se 1 (by rfl) ⟨1795820, by rfl⟩ : syracuseStep 2394427 = 3591641) B3591641
theorem B3192569 : Blo 2127435 3192569 := bstep (se 2 (by rfl) ⟨1197213, by rfl⟩ : syracuseStep 3192569 = 2394427) B2394427
theorem B2128379 : Blo 2127435 2128379 := bstep (se 1 (by rfl) ⟨1596284, by rfl⟩ : syracuseStep 2128379 = 3192569) B3192569
theorem B12944533 : Blo 2127435 12944533 := bbase (se 6 (by rfl) ⟨303387, by rfl⟩ : syracuseStep 12944533 = 606775) (by norm_num)
theorem B17259377 : Blo 2127435 17259377 := bstep (se 2 (by rfl) ⟨6472266, by rfl⟩ : syracuseStep 17259377 = 12944533) B12944533
theorem B46025005 : Blo 2127435 46025005 := bstep (se 3 (by rfl) ⟨8629688, by rfl⟩ : syracuseStep 46025005 = 17259377) B17259377
theorem B61366673 : Blo 2127435 61366673 := bstep (se 2 (by rfl) ⟨23012502, by rfl⟩ : syracuseStep 61366673 = 46025005) B46025005
theorem B40911115 : Blo 2127435 40911115 := bstep (se 1 (by rfl) ⟨30683336, by rfl⟩ : syracuseStep 40911115 = 61366673) B61366673
theorem B54548153 : Blo 2127435 54548153 := bstep (se 2 (by rfl) ⟨20455557, by rfl⟩ : syracuseStep 54548153 = 40911115) B40911115
theorem B36365435 : Blo 2127435 36365435 := bstep (se 1 (by rfl) ⟨27274076, by rfl⟩ : syracuseStep 36365435 = 54548153) B54548153
theorem B24243623 : Blo 2127435 24243623 := bstep (se 1 (by rfl) ⟨18182717, by rfl⟩ : syracuseStep 24243623 = 36365435) B36365435
theorem B16162415 : Blo 2127435 16162415 := bstep (se 1 (by rfl) ⟨12121811, by rfl⟩ : syracuseStep 16162415 = 24243623) B24243623
theorem B10774943 : Blo 2127435 10774943 := bstep (se 1 (by rfl) ⟨8081207, by rfl⟩ : syracuseStep 10774943 = 16162415) B16162415
theorem B7183295 : Blo 2127435 7183295 := bstep (se 1 (by rfl) ⟨5387471, by rfl⟩ : syracuseStep 7183295 = 10774943) B10774943
theorem B4788863 : Blo 2127435 4788863 := bstep (se 1 (by rfl) ⟨3591647, by rfl⟩ : syracuseStep 4788863 = 7183295) B7183295
theorem B3192575 : Blo 2127435 3192575 := bstep (se 1 (by rfl) ⟨2394431, by rfl⟩ : syracuseStep 3192575 = 4788863) B4788863
theorem B2128383 : Blo 2127435 2128383 := bstep (se 1 (by rfl) ⟨1596287, by rfl⟩ : syracuseStep 2128383 = 3192575) B3192575
theorem B3192581 : Blo 2127435 3192581 := bbase (se 4 (by rfl) ⟨299304, by rfl⟩ : syracuseStep 3192581 = 598609) (by norm_num)
theorem B2128387 : Blo 2127435 2128387 := bstep (se 1 (by rfl) ⟨1596290, by rfl⟩ : syracuseStep 2128387 = 3192581) B3192581
theorem B3591661 : Blo 2127435 3591661 := bbase (se 3 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 3591661 = 1346873) (by norm_num)
theorem B4788881 : Blo 2127435 4788881 := bstep (se 2 (by rfl) ⟨1795830, by rfl⟩ : syracuseStep 4788881 = 3591661) B3591661
theorem B3192587 : Blo 2127435 3192587 := bstep (se 1 (by rfl) ⟨2394440, by rfl⟩ : syracuseStep 3192587 = 4788881) B4788881
theorem B2128391 : Blo 2127435 2128391 := bstep (se 1 (by rfl) ⟨1596293, by rfl⟩ : syracuseStep 2128391 = 3192587) B3192587
theorem B2394445 : Blo 2127435 2394445 := bbase (se 3 (by rfl) ⟨448958, by rfl⟩ : syracuseStep 2394445 = 897917) (by norm_num)
theorem B3192593 : Blo 2127435 3192593 := bstep (se 2 (by rfl) ⟨1197222, by rfl⟩ : syracuseStep 3192593 = 2394445) B2394445
theorem B2128395 : Blo 2127435 2128395 := bstep (se 1 (by rfl) ⟨1596296, by rfl⟩ : syracuseStep 2128395 = 3192593) B3192593
theorem B7183349 : Blo 2127435 7183349 := bbase (se 5 (by rfl) ⟨336719, by rfl⟩ : syracuseStep 7183349 = 673439) (by norm_num)
theorem B4788899 : Blo 2127435 4788899 := bstep (se 1 (by rfl) ⟨3591674, by rfl⟩ : syracuseStep 4788899 = 7183349) B7183349
theorem B3192599 : Blo 2127435 3192599 := bstep (se 1 (by rfl) ⟨2394449, by rfl⟩ : syracuseStep 3192599 = 4788899) B4788899
theorem B2128399 : Blo 2127435 2128399 := bstep (se 1 (by rfl) ⟨1596299, by rfl⟩ : syracuseStep 2128399 = 3192599) B3192599
theorem B3192605 : Blo 2127435 3192605 := bbase (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) (by norm_num)
theorem B2128403 : Blo 2127435 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B4788917 : Blo 2127435 4788917 := bbase (se 5 (by rfl) ⟨224480, by rfl⟩ : syracuseStep 4788917 = 448961) (by norm_num)
theorem B3192611 : Blo 2127435 3192611 := bstep (se 1 (by rfl) ⟨2394458, by rfl⟩ : syracuseStep 3192611 = 4788917) B4788917
theorem B2128407 : Blo 2127435 2128407 := bstep (se 1 (by rfl) ⟨1596305, by rfl⟩ : syracuseStep 2128407 = 3192611) B3192611
theorem B12121973 : Blo 2127435 12121973 := bbase (se 5 (by rfl) ⟨568217, by rfl⟩ : syracuseStep 12121973 = 1136435) (by norm_num)
theorem B8081315 : Blo 2127435 8081315 := bstep (se 1 (by rfl) ⟨6060986, by rfl⟩ : syracuseStep 8081315 = 12121973) B12121973
theorem B5387543 : Blo 2127435 5387543 := bstep (se 1 (by rfl) ⟨4040657, by rfl⟩ : syracuseStep 5387543 = 8081315) B8081315
theorem B3591695 : Blo 2127435 3591695 := bstep (se 1 (by rfl) ⟨2693771, by rfl⟩ : syracuseStep 3591695 = 5387543) B5387543
theorem B2394463 : Blo 2127435 2394463 := bstep (se 1 (by rfl) ⟨1795847, by rfl⟩ : syracuseStep 2394463 = 3591695) B3591695
theorem B3192617 : Blo 2127435 3192617 := bstep (se 2 (by rfl) ⟨1197231, by rfl⟩ : syracuseStep 3192617 = 2394463) B2394463
theorem B2128411 : Blo 2127435 2128411 := bstep (se 1 (by rfl) ⟨1596308, by rfl⟩ : syracuseStep 2128411 = 3192617) B3192617
theorem B6060997 : Blo 2127435 6060997 := bbase (se 4 (by rfl) ⟨568218, by rfl⟩ : syracuseStep 6060997 = 1136437) (by norm_num)
theorem B8081329 : Blo 2127435 8081329 := bstep (se 2 (by rfl) ⟨3030498, by rfl⟩ : syracuseStep 8081329 = 6060997) B6060997
theorem B10775105 : Blo 2127435 10775105 := bstep (se 2 (by rfl) ⟨4040664, by rfl⟩ : syracuseStep 10775105 = 8081329) B8081329
theorem B7183403 : Blo 2127435 7183403 := bstep (se 1 (by rfl) ⟨5387552, by rfl⟩ : syracuseStep 7183403 = 10775105) B10775105
theorem B4788935 : Blo 2127435 4788935 := bstep (se 1 (by rfl) ⟨3591701, by rfl⟩ : syracuseStep 4788935 = 7183403) B7183403
theorem B3192623 : Blo 2127435 3192623 := bstep (se 1 (by rfl) ⟨2394467, by rfl⟩ : syracuseStep 3192623 = 4788935) B4788935
theorem B2128415 : Blo 2127435 2128415 := bstep (se 1 (by rfl) ⟨1596311, by rfl⟩ : syracuseStep 2128415 = 3192623) B3192623
theorem B3192629 : Blo 2127435 3192629 := bbase (se 5 (by rfl) ⟨149654, by rfl⟩ : syracuseStep 3192629 = 299309) (by norm_num)
theorem B2128419 : Blo 2127435 2128419 := bstep (se 1 (by rfl) ⟨1596314, by rfl⟩ : syracuseStep 2128419 = 3192629) B3192629
theorem B5387573 : Blo 2127435 5387573 := bbase (se 5 (by rfl) ⟨252542, by rfl⟩ : syracuseStep 5387573 = 505085) (by norm_num)
theorem B3591715 : Blo 2127435 3591715 := bstep (se 1 (by rfl) ⟨2693786, by rfl⟩ : syracuseStep 3591715 = 5387573) B5387573
theorem B4788953 : Blo 2127435 4788953 := bstep (se 2 (by rfl) ⟨1795857, by rfl⟩ : syracuseStep 4788953 = 3591715) B3591715
theorem B3192635 : Blo 2127435 3192635 := bstep (se 1 (by rfl) ⟨2394476, by rfl⟩ : syracuseStep 3192635 = 4788953) B4788953
theorem B2128423 : Blo 2127435 2128423 := bstep (se 1 (by rfl) ⟨1596317, by rfl⟩ : syracuseStep 2128423 = 3192635) B3192635
theorem B2394481 : Blo 2127435 2394481 := bbase (se 2 (by rfl) ⟨897930, by rfl⟩ : syracuseStep 2394481 = 1795861) (by norm_num)
theorem B3192641 : Blo 2127435 3192641 := bstep (se 2 (by rfl) ⟨1197240, by rfl⟩ : syracuseStep 3192641 = 2394481) B2394481
theorem B2128427 : Blo 2127435 2128427 := bstep (se 1 (by rfl) ⟨1596320, by rfl⟩ : syracuseStep 2128427 = 3192641) B3192641
theorem B2876629 : Blo 2127435 2876629 := bbase (se 7 (by rfl) ⟨33710, by rfl⟩ : syracuseStep 2876629 = 67421) (by norm_num)
theorem B3835505 : Blo 2127435 3835505 := bstep (se 2 (by rfl) ⟨1438314, by rfl⟩ : syracuseStep 3835505 = 2876629) B2876629
theorem B2557003 : Blo 2127435 2557003 := bstep (se 1 (by rfl) ⟨1917752, by rfl⟩ : syracuseStep 2557003 = 3835505) B3835505
theorem B3409337 : Blo 2127435 3409337 := bstep (se 2 (by rfl) ⟨1278501, by rfl⟩ : syracuseStep 3409337 = 2557003) B2557003
theorem B9091565 : Blo 2127435 9091565 := bstep (se 3 (by rfl) ⟨1704668, by rfl⟩ : syracuseStep 9091565 = 3409337) B3409337
theorem B6061043 : Blo 2127435 6061043 := bstep (se 1 (by rfl) ⟨4545782, by rfl⟩ : syracuseStep 6061043 = 9091565) B9091565
theorem B4040695 : Blo 2127435 4040695 := bstep (se 1 (by rfl) ⟨3030521, by rfl⟩ : syracuseStep 4040695 = 6061043) B6061043
theorem B5387593 : Blo 2127435 5387593 := bstep (se 2 (by rfl) ⟨2020347, by rfl⟩ : syracuseStep 5387593 = 4040695) B4040695
theorem B7183457 : Blo 2127435 7183457 := bstep (se 2 (by rfl) ⟨2693796, by rfl⟩ : syracuseStep 7183457 = 5387593) B5387593
theorem B4788971 : Blo 2127435 4788971 := bstep (se 1 (by rfl) ⟨3591728, by rfl⟩ : syracuseStep 4788971 = 7183457) B7183457
theorem B3192647 : Blo 2127435 3192647 := bstep (se 1 (by rfl) ⟨2394485, by rfl⟩ : syracuseStep 3192647 = 4788971) B4788971
theorem B2128431 : Blo 2127435 2128431 := bstep (se 1 (by rfl) ⟨1596323, by rfl⟩ : syracuseStep 2128431 = 3192647) B3192647
theorem B3192653 : Blo 2127435 3192653 := bbase (se 3 (by rfl) ⟨598622, by rfl⟩ : syracuseStep 3192653 = 1197245) (by norm_num)
theorem B2128435 : Blo 2127435 2128435 := bstep (se 1 (by rfl) ⟨1596326, by rfl⟩ : syracuseStep 2128435 = 3192653) B3192653
theorem B4788989 : Blo 2127435 4788989 := bbase (se 3 (by rfl) ⟨897935, by rfl⟩ : syracuseStep 4788989 = 1795871) (by norm_num)
theorem B3192659 : Blo 2127435 3192659 := bstep (se 1 (by rfl) ⟨2394494, by rfl⟩ : syracuseStep 3192659 = 4788989) B4788989
theorem B2128439 : Blo 2127435 2128439 := bstep (se 1 (by rfl) ⟨1596329, by rfl⟩ : syracuseStep 2128439 = 3192659) B3192659
theorem B3591749 : Blo 2127435 3591749 := bbase (se 4 (by rfl) ⟨336726, by rfl⟩ : syracuseStep 3591749 = 673453) (by norm_num)
theorem B2394499 : Blo 2127435 2394499 := bstep (se 1 (by rfl) ⟨1795874, by rfl⟩ : syracuseStep 2394499 = 3591749) B3591749
theorem B3192665 : Blo 2127435 3192665 := bstep (se 2 (by rfl) ⟨1197249, by rfl⟩ : syracuseStep 3192665 = 2394499) B2394499
theorem B2128443 : Blo 2127435 2128443 := bstep (se 1 (by rfl) ⟨1596332, by rfl⟩ : syracuseStep 2128443 = 3192665) B3192665
theorem B16162901 : Blo 2127435 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B10775267 : Blo 2127435 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B7183511 : Blo 2127435 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B4789007 : Blo 2127435 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B3192671 : Blo 2127435 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B2128447 : Blo 2127435 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B3192677 : Blo 2127435 3192677 := bbase (se 4 (by rfl) ⟨299313, by rfl⟩ : syracuseStep 3192677 = 598627) (by norm_num)
theorem B2128451 : Blo 2127435 2128451 := bstep (se 1 (by rfl) ⟨1596338, by rfl⟩ : syracuseStep 2128451 = 3192677) B3192677
theorem B4040741 : Blo 2127435 4040741 := bbase (se 4 (by rfl) ⟨378819, by rfl⟩ : syracuseStep 4040741 = 757639) (by norm_num)
theorem B2693827 : Blo 2127435 2693827 := bstep (se 1 (by rfl) ⟨2020370, by rfl⟩ : syracuseStep 2693827 = 4040741) B4040741
theorem B3591769 : Blo 2127435 3591769 := bstep (se 2 (by rfl) ⟨1346913, by rfl⟩ : syracuseStep 3591769 = 2693827) B2693827
theorem B4789025 : Blo 2127435 4789025 := bstep (se 2 (by rfl) ⟨1795884, by rfl⟩ : syracuseStep 4789025 = 3591769) B3591769
theorem B3192683 : Blo 2127435 3192683 := bstep (se 1 (by rfl) ⟨2394512, by rfl⟩ : syracuseStep 3192683 = 4789025) B4789025
theorem B2128455 : Blo 2127435 2128455 := bstep (se 1 (by rfl) ⟨1596341, by rfl⟩ : syracuseStep 2128455 = 3192683) B3192683
theorem B2394517 : Blo 2127435 2394517 := bbase (se 6 (by rfl) ⟨56121, by rfl⟩ : syracuseStep 2394517 = 112243) (by norm_num)
theorem B3192689 : Blo 2127435 3192689 := bstep (se 2 (by rfl) ⟨1197258, by rfl⟩ : syracuseStep 3192689 = 2394517) B2394517
theorem B2128459 : Blo 2127435 2128459 := bstep (se 1 (by rfl) ⟨1596344, by rfl⟩ : syracuseStep 2128459 = 3192689) B3192689
theorem B2693837 : Blo 2127435 2693837 := bbase (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) (by norm_num)
theorem B7183565 : Blo 2127435 7183565 := bstep (se 3 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 7183565 = 2693837) B2693837
theorem B4789043 : Blo 2127435 4789043 := bstep (se 1 (by rfl) ⟨3591782, by rfl⟩ : syracuseStep 4789043 = 7183565) B7183565
theorem B3192695 : Blo 2127435 3192695 := bstep (se 1 (by rfl) ⟨2394521, by rfl⟩ : syracuseStep 3192695 = 4789043) B4789043
theorem B2128463 : Blo 2127435 2128463 := bstep (se 1 (by rfl) ⟨1596347, by rfl⟩ : syracuseStep 2128463 = 3192695) B3192695
theorem B3192701 : Blo 2127435 3192701 := bbase (se 3 (by rfl) ⟨598631, by rfl⟩ : syracuseStep 3192701 = 1197263) (by norm_num)
theorem B2128467 : Blo 2127435 2128467 := bstep (se 1 (by rfl) ⟨1596350, by rfl⟩ : syracuseStep 2128467 = 3192701) B3192701
theorem B4789061 : Blo 2127435 4789061 := bbase (se 4 (by rfl) ⟨448974, by rfl⟩ : syracuseStep 4789061 = 897949) (by norm_num)
theorem B3192707 : Blo 2127435 3192707 := bstep (se 1 (by rfl) ⟨2394530, by rfl⟩ : syracuseStep 3192707 = 4789061) B4789061
theorem B2128471 : Blo 2127435 2128471 := bstep (se 1 (by rfl) ⟨1596353, by rfl⟩ : syracuseStep 2128471 = 3192707) B3192707
theorem B4545877 : Blo 2127435 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B6061169 : Blo 2127435 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B4040779 : Blo 2127435 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B5387705 : Blo 2127435 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B3591803 : Blo 2127435 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B2394535 : Blo 2127435 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B3192713 : Blo 2127435 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B2128475 : Blo 2127435 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B10775429 : Blo 2127435 10775429 := bbase (se 4 (by rfl) ⟨1010196, by rfl⟩ : syracuseStep 10775429 = 2020393) (by norm_num)
theorem B7183619 : Blo 2127435 7183619 := bstep (se 1 (by rfl) ⟨5387714, by rfl⟩ : syracuseStep 7183619 = 10775429) B10775429
theorem B4789079 : Blo 2127435 4789079 := bstep (se 1 (by rfl) ⟨3591809, by rfl⟩ : syracuseStep 4789079 = 7183619) B7183619
theorem B3192719 : Blo 2127435 3192719 := bstep (se 1 (by rfl) ⟨2394539, by rfl⟩ : syracuseStep 3192719 = 4789079) B4789079
theorem B2128479 : Blo 2127435 2128479 := bstep (se 1 (by rfl) ⟨1596359, by rfl⟩ : syracuseStep 2128479 = 3192719) B3192719
theorem B3192725 : Blo 2127435 3192725 := bbase (se 6 (by rfl) ⟨74829, by rfl⟩ : syracuseStep 3192725 = 149659) (by norm_num)
theorem B2128483 : Blo 2127435 2128483 := bstep (se 1 (by rfl) ⟨1596362, by rfl⟩ : syracuseStep 2128483 = 3192725) B3192725
theorem B5114141 : Blo 2127435 5114141 := bbase (se 3 (by rfl) ⟨958901, by rfl⟩ : syracuseStep 5114141 = 1917803) (by norm_num)
theorem B3409427 : Blo 2127435 3409427 := bstep (se 1 (by rfl) ⟨2557070, by rfl⟩ : syracuseStep 3409427 = 5114141) B5114141
theorem B2272951 : Blo 2127435 2272951 := bstep (se 1 (by rfl) ⟨1704713, by rfl⟩ : syracuseStep 2272951 = 3409427) B3409427
theorem B12122405 : Blo 2127435 12122405 := bstep (se 4 (by rfl) ⟨1136475, by rfl⟩ : syracuseStep 12122405 = 2272951) B2272951
theorem B8081603 : Blo 2127435 8081603 := bstep (se 1 (by rfl) ⟨6061202, by rfl⟩ : syracuseStep 8081603 = 12122405) B12122405
theorem B5387735 : Blo 2127435 5387735 := bstep (se 1 (by rfl) ⟨4040801, by rfl⟩ : syracuseStep 5387735 = 8081603) B8081603
theorem B3591823 : Blo 2127435 3591823 := bstep (se 1 (by rfl) ⟨2693867, by rfl⟩ : syracuseStep 3591823 = 5387735) B5387735
theorem B4789097 : Blo 2127435 4789097 := bstep (se 2 (by rfl) ⟨1795911, by rfl⟩ : syracuseStep 4789097 = 3591823) B3591823
theorem B3192731 : Blo 2127435 3192731 := bstep (se 1 (by rfl) ⟨2394548, by rfl⟩ : syracuseStep 3192731 = 4789097) B4789097
theorem B2128487 : Blo 2127435 2128487 := bstep (se 1 (by rfl) ⟨1596365, by rfl⟩ : syracuseStep 2128487 = 3192731) B3192731
theorem B2394553 : Blo 2127435 2394553 := bbase (se 2 (by rfl) ⟨897957, by rfl⟩ : syracuseStep 2394553 = 1795915) (by norm_num)
theorem B3192737 : Blo 2127435 3192737 := bstep (se 2 (by rfl) ⟨1197276, by rfl⟩ : syracuseStep 3192737 = 2394553) B2394553
theorem B2128491 : Blo 2127435 2128491 := bstep (se 1 (by rfl) ⟨1596368, by rfl⟩ : syracuseStep 2128491 = 3192737) B3192737
theorem B7281685 : Blo 2127435 7281685 := bbase (se 6 (by rfl) ⟨170664, by rfl⟩ : syracuseStep 7281685 = 341329) (by norm_num)
theorem B9708913 : Blo 2127435 9708913 := bstep (se 2 (by rfl) ⟨3640842, by rfl⟩ : syracuseStep 9708913 = 7281685) B7281685
theorem B51780869 : Blo 2127435 51780869 := bstep (se 4 (by rfl) ⟨4854456, by rfl⟩ : syracuseStep 51780869 = 9708913) B9708913
theorem B34520579 : Blo 2127435 34520579 := bstep (se 1 (by rfl) ⟨25890434, by rfl⟩ : syracuseStep 34520579 = 51780869) B51780869
theorem B23013719 : Blo 2127435 23013719 := bstep (se 1 (by rfl) ⟨17260289, by rfl⟩ : syracuseStep 23013719 = 34520579) B34520579
theorem B15342479 : Blo 2127435 15342479 := bstep (se 1 (by rfl) ⟨11506859, by rfl⟩ : syracuseStep 15342479 = 23013719) B23013719
theorem B10228319 : Blo 2127435 10228319 := bstep (se 1 (by rfl) ⟨7671239, by rfl⟩ : syracuseStep 10228319 = 15342479) B15342479
theorem B6818879 : Blo 2127435 6818879 := bstep (se 1 (by rfl) ⟨5114159, by rfl⟩ : syracuseStep 6818879 = 10228319) B10228319
theorem B4545919 : Blo 2127435 4545919 := bstep (se 1 (by rfl) ⟨3409439, by rfl⟩ : syracuseStep 4545919 = 6818879) B6818879
theorem B6061225 : Blo 2127435 6061225 := bstep (se 2 (by rfl) ⟨2272959, by rfl⟩ : syracuseStep 6061225 = 4545919) B4545919
theorem B8081633 : Blo 2127435 8081633 := bstep (se 2 (by rfl) ⟨3030612, by rfl⟩ : syracuseStep 8081633 = 6061225) B6061225
theorem B5387755 : Blo 2127435 5387755 := bstep (se 1 (by rfl) ⟨4040816, by rfl⟩ : syracuseStep 5387755 = 8081633) B8081633
theorem B7183673 : Blo 2127435 7183673 := bstep (se 2 (by rfl) ⟨2693877, by rfl⟩ : syracuseStep 7183673 = 5387755) B5387755
theorem B4789115 : Blo 2127435 4789115 := bstep (se 1 (by rfl) ⟨3591836, by rfl⟩ : syracuseStep 4789115 = 7183673) B7183673
theorem B3192743 : Blo 2127435 3192743 := bstep (se 1 (by rfl) ⟨2394557, by rfl⟩ : syracuseStep 3192743 = 4789115) B4789115
theorem B2128495 : Blo 2127435 2128495 := bstep (se 1 (by rfl) ⟨1596371, by rfl⟩ : syracuseStep 2128495 = 3192743) B3192743
theorem B3192749 : Blo 2127435 3192749 := bbase (se 3 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 3192749 = 1197281) (by norm_num)
theorem B2128499 : Blo 2127435 2128499 := bstep (se 1 (by rfl) ⟨1596374, by rfl⟩ : syracuseStep 2128499 = 3192749) B3192749
theorem B4789133 : Blo 2127435 4789133 := bbase (se 3 (by rfl) ⟨897962, by rfl⟩ : syracuseStep 4789133 = 1795925) (by norm_num)
theorem B3192755 : Blo 2127435 3192755 := bstep (se 1 (by rfl) ⟨2394566, by rfl⟩ : syracuseStep 3192755 = 4789133) B4789133
theorem B2128503 : Blo 2127435 2128503 := bstep (se 1 (by rfl) ⟨1596377, by rfl⟩ : syracuseStep 2128503 = 3192755) B3192755
theorem B2693893 : Blo 2127435 2693893 := bbase (se 4 (by rfl) ⟨252552, by rfl⟩ : syracuseStep 2693893 = 505105) (by norm_num)
theorem B3591857 : Blo 2127435 3591857 := bstep (se 2 (by rfl) ⟨1346946, by rfl⟩ : syracuseStep 3591857 = 2693893) B2693893
theorem B2394571 : Blo 2127435 2394571 := bstep (se 1 (by rfl) ⟨1795928, by rfl⟩ : syracuseStep 2394571 = 3591857) B3591857
theorem B3192761 : Blo 2127435 3192761 := bstep (se 2 (by rfl) ⟨1197285, by rfl⟩ : syracuseStep 3192761 = 2394571) B2394571
theorem B2128507 : Blo 2127435 2128507 := bstep (se 1 (by rfl) ⟨1596380, by rfl⟩ : syracuseStep 2128507 = 3192761) B3192761
theorem B5114197 : Blo 2127435 5114197 := bbase (se 10 (by rfl) ⟨7491, by rfl⟩ : syracuseStep 5114197 = 14983) (by norm_num)
theorem B27275717 : Blo 2127435 27275717 := bstep (se 4 (by rfl) ⟨2557098, by rfl⟩ : syracuseStep 27275717 = 5114197) B5114197
theorem B18183811 : Blo 2127435 18183811 := bstep (se 1 (by rfl) ⟨13637858, by rfl⟩ : syracuseStep 18183811 = 27275717) B27275717
theorem B24245081 : Blo 2127435 24245081 := bstep (se 2 (by rfl) ⟨9091905, by rfl⟩ : syracuseStep 24245081 = 18183811) B18183811
theorem B16163387 : Blo 2127435 16163387 := bstep (se 1 (by rfl) ⟨12122540, by rfl⟩ : syracuseStep 16163387 = 24245081) B24245081
theorem B10775591 : Blo 2127435 10775591 := bstep (se 1 (by rfl) ⟨8081693, by rfl⟩ : syracuseStep 10775591 = 16163387) B16163387
theorem B7183727 : Blo 2127435 7183727 := bstep (se 1 (by rfl) ⟨5387795, by rfl⟩ : syracuseStep 7183727 = 10775591) B10775591
theorem B4789151 : Blo 2127435 4789151 := bstep (se 1 (by rfl) ⟨3591863, by rfl⟩ : syracuseStep 4789151 = 7183727) B7183727
theorem B3192767 : Blo 2127435 3192767 := bstep (se 1 (by rfl) ⟨2394575, by rfl⟩ : syracuseStep 3192767 = 4789151) B4789151
theorem B2128511 : Blo 2127435 2128511 := bstep (se 1 (by rfl) ⟨1596383, by rfl⟩ : syracuseStep 2128511 = 3192767) B3192767
theorem B3192773 : Blo 2127435 3192773 := bbase (se 4 (by rfl) ⟨299322, by rfl⟩ : syracuseStep 3192773 = 598645) (by norm_num)
theorem B2128515 : Blo 2127435 2128515 := bstep (se 1 (by rfl) ⟨1596386, by rfl⟩ : syracuseStep 2128515 = 3192773) B3192773
theorem B3591877 : Blo 2127435 3591877 := bbase (se 4 (by rfl) ⟨336738, by rfl⟩ : syracuseStep 3591877 = 673477) (by norm_num)
theorem B4789169 : Blo 2127435 4789169 := bstep (se 2 (by rfl) ⟨1795938, by rfl⟩ : syracuseStep 4789169 = 3591877) B3591877
theorem B3192779 : Blo 2127435 3192779 := bstep (se 1 (by rfl) ⟨2394584, by rfl⟩ : syracuseStep 3192779 = 4789169) B4789169
theorem B2128519 : Blo 2127435 2128519 := bstep (se 1 (by rfl) ⟨1596389, by rfl⟩ : syracuseStep 2128519 = 3192779) B3192779
theorem B2394589 : Blo 2127435 2394589 := bbase (se 3 (by rfl) ⟨448985, by rfl⟩ : syracuseStep 2394589 = 897971) (by norm_num)
theorem B3192785 : Blo 2127435 3192785 := bstep (se 2 (by rfl) ⟨1197294, by rfl⟩ : syracuseStep 3192785 = 2394589) B2394589
theorem B2128523 : Blo 2127435 2128523 := bstep (se 1 (by rfl) ⟨1596392, by rfl⟩ : syracuseStep 2128523 = 3192785) B3192785
theorem B7183781 : Blo 2127435 7183781 := bbase (se 4 (by rfl) ⟨673479, by rfl⟩ : syracuseStep 7183781 = 1346959) (by norm_num)
theorem B4789187 : Blo 2127435 4789187 := bstep (se 1 (by rfl) ⟨3591890, by rfl⟩ : syracuseStep 4789187 = 7183781) B7183781
theorem B3192791 : Blo 2127435 3192791 := bstep (se 1 (by rfl) ⟨2394593, by rfl⟩ : syracuseStep 3192791 = 4789187) B4789187
theorem B2128527 : Blo 2127435 2128527 := bstep (se 1 (by rfl) ⟨1596395, by rfl⟩ : syracuseStep 2128527 = 3192791) B3192791
theorem B3192797 : Blo 2127435 3192797 := bbase (se 3 (by rfl) ⟨598649, by rfl⟩ : syracuseStep 3192797 = 1197299) (by norm_num)
theorem B2128531 : Blo 2127435 2128531 := bstep (se 1 (by rfl) ⟨1596398, by rfl⟩ : syracuseStep 2128531 = 3192797) B3192797
theorem B4789205 : Blo 2127435 4789205 := bbase (se 7 (by rfl) ⟨56123, by rfl⟩ : syracuseStep 4789205 = 112247) (by norm_num)
theorem B3192803 : Blo 2127435 3192803 := bstep (se 1 (by rfl) ⟨2394602, by rfl⟩ : syracuseStep 3192803 = 4789205) B4789205
theorem B2128535 : Blo 2127435 2128535 := bstep (se 1 (by rfl) ⟨1596401, by rfl⟩ : syracuseStep 2128535 = 3192803) B3192803
theorem B2157581 : Blo 2127435 2157581 := bbase (se 3 (by rfl) ⟨404546, by rfl⟩ : syracuseStep 2157581 = 809093) (by norm_num)
theorem B5753549 : Blo 2127435 5753549 := bstep (se 3 (by rfl) ⟨1078790, by rfl⟩ : syracuseStep 5753549 = 2157581) B2157581
theorem B15342797 : Blo 2127435 15342797 := bstep (se 3 (by rfl) ⟨2876774, by rfl⟩ : syracuseStep 15342797 = 5753549) B5753549
theorem B10228531 : Blo 2127435 10228531 := bstep (se 1 (by rfl) ⟨7671398, by rfl⟩ : syracuseStep 10228531 = 15342797) B15342797
theorem B13638041 : Blo 2127435 13638041 := bstep (se 2 (by rfl) ⟨5114265, by rfl⟩ : syracuseStep 13638041 = 10228531) B10228531
theorem B9092027 : Blo 2127435 9092027 := bstep (se 1 (by rfl) ⟨6819020, by rfl⟩ : syracuseStep 9092027 = 13638041) B13638041
theorem B6061351 : Blo 2127435 6061351 := bstep (se 1 (by rfl) ⟨4546013, by rfl⟩ : syracuseStep 6061351 = 9092027) B9092027
theorem B8081801 : Blo 2127435 8081801 := bstep (se 2 (by rfl) ⟨3030675, by rfl⟩ : syracuseStep 8081801 = 6061351) B6061351
theorem B5387867 : Blo 2127435 5387867 := bstep (se 1 (by rfl) ⟨4040900, by rfl⟩ : syracuseStep 5387867 = 8081801) B8081801
theorem B3591911 : Blo 2127435 3591911 := bstep (se 1 (by rfl) ⟨2693933, by rfl⟩ : syracuseStep 3591911 = 5387867) B5387867
theorem B2394607 : Blo 2127435 2394607 := bstep (se 1 (by rfl) ⟨1795955, by rfl⟩ : syracuseStep 2394607 = 3591911) B3591911
theorem B3192809 : Blo 2127435 3192809 := bstep (se 2 (by rfl) ⟨1197303, by rfl⟩ : syracuseStep 3192809 = 2394607) B2394607
theorem B2128539 : Blo 2127435 2128539 := bstep (se 1 (by rfl) ⟨1596404, by rfl⟩ : syracuseStep 2128539 = 3192809) B3192809
theorem B18184085 : Blo 2127435 18184085 := bbase (se 6 (by rfl) ⟨426189, by rfl⟩ : syracuseStep 18184085 = 852379) (by norm_num)
theorem B12122723 : Blo 2127435 12122723 := bstep (se 1 (by rfl) ⟨9092042, by rfl⟩ : syracuseStep 12122723 = 18184085) B18184085
theorem B8081815 : Blo 2127435 8081815 := bstep (se 1 (by rfl) ⟨6061361, by rfl⟩ : syracuseStep 8081815 = 12122723) B12122723
theorem B10775753 : Blo 2127435 10775753 := bstep (se 2 (by rfl) ⟨4040907, by rfl⟩ : syracuseStep 10775753 = 8081815) B8081815
theorem B7183835 : Blo 2127435 7183835 := bstep (se 1 (by rfl) ⟨5387876, by rfl⟩ : syracuseStep 7183835 = 10775753) B10775753
theorem B4789223 : Blo 2127435 4789223 := bstep (se 1 (by rfl) ⟨3591917, by rfl⟩ : syracuseStep 4789223 = 7183835) B7183835
theorem B3192815 : Blo 2127435 3192815 := bstep (se 1 (by rfl) ⟨2394611, by rfl⟩ : syracuseStep 3192815 = 4789223) B4789223
theorem B2128543 : Blo 2127435 2128543 := bstep (se 1 (by rfl) ⟨1596407, by rfl⟩ : syracuseStep 2128543 = 3192815) B3192815
theorem B3192821 : Blo 2127435 3192821 := bbase (se 5 (by rfl) ⟨149663, by rfl⟩ : syracuseStep 3192821 = 299327) (by norm_num)
theorem B2128547 : Blo 2127435 2128547 := bstep (se 1 (by rfl) ⟨1596410, by rfl⟩ : syracuseStep 2128547 = 3192821) B3192821
theorem B2427293 : Blo 2127435 2427293 := bbase (se 3 (by rfl) ⟨455117, by rfl⟩ : syracuseStep 2427293 = 910235) (by norm_num)
theorem B6472781 : Blo 2127435 6472781 := bstep (se 3 (by rfl) ⟨1213646, by rfl⟩ : syracuseStep 6472781 = 2427293) B2427293
theorem B4315187 : Blo 2127435 4315187 := bstep (se 1 (by rfl) ⟨3236390, by rfl⟩ : syracuseStep 4315187 = 6472781) B6472781
theorem B2876791 : Blo 2127435 2876791 := bstep (se 1 (by rfl) ⟨2157593, by rfl⟩ : syracuseStep 2876791 = 4315187) B4315187
theorem B3835721 : Blo 2127435 3835721 := bstep (se 2 (by rfl) ⟨1438395, by rfl⟩ : syracuseStep 3835721 = 2876791) B2876791
theorem B10228589 : Blo 2127435 10228589 := bstep (se 3 (by rfl) ⟨1917860, by rfl⟩ : syracuseStep 10228589 = 3835721) B3835721
theorem B6819059 : Blo 2127435 6819059 := bstep (se 1 (by rfl) ⟨5114294, by rfl⟩ : syracuseStep 6819059 = 10228589) B10228589
theorem B4546039 : Blo 2127435 4546039 := bstep (se 1 (by rfl) ⟨3409529, by rfl⟩ : syracuseStep 4546039 = 6819059) B6819059
theorem B6061385 : Blo 2127435 6061385 := bstep (se 2 (by rfl) ⟨2273019, by rfl⟩ : syracuseStep 6061385 = 4546039) B4546039
theorem B4040923 : Blo 2127435 4040923 := bstep (se 1 (by rfl) ⟨3030692, by rfl⟩ : syracuseStep 4040923 = 6061385) B6061385
theorem B5387897 : Blo 2127435 5387897 := bstep (se 2 (by rfl) ⟨2020461, by rfl⟩ : syracuseStep 5387897 = 4040923) B4040923
theorem B3591931 : Blo 2127435 3591931 := bstep (se 1 (by rfl) ⟨2693948, by rfl⟩ : syracuseStep 3591931 = 5387897) B5387897
theorem B4789241 : Blo 2127435 4789241 := bstep (se 2 (by rfl) ⟨1795965, by rfl⟩ : syracuseStep 4789241 = 3591931) B3591931
theorem B3192827 : Blo 2127435 3192827 := bstep (se 1 (by rfl) ⟨2394620, by rfl⟩ : syracuseStep 3192827 = 4789241) B4789241
theorem B2128551 : Blo 2127435 2128551 := bstep (se 1 (by rfl) ⟨1596413, by rfl⟩ : syracuseStep 2128551 = 3192827) B3192827
theorem B2394625 : Blo 2127435 2394625 := bbase (se 2 (by rfl) ⟨897984, by rfl⟩ : syracuseStep 2394625 = 1795969) (by norm_num)
theorem B3192833 : Blo 2127435 3192833 := bstep (se 2 (by rfl) ⟨1197312, by rfl⟩ : syracuseStep 3192833 = 2394625) B2394625
theorem B2128555 : Blo 2127435 2128555 := bstep (se 1 (by rfl) ⟨1596416, by rfl⟩ : syracuseStep 2128555 = 3192833) B3192833
theorem B5387917 : Blo 2127435 5387917 := bbase (se 3 (by rfl) ⟨1010234, by rfl⟩ : syracuseStep 5387917 = 2020469) (by norm_num)
theorem B7183889 : Blo 2127435 7183889 := bstep (se 2 (by rfl) ⟨2693958, by rfl⟩ : syracuseStep 7183889 = 5387917) B5387917
theorem B4789259 : Blo 2127435 4789259 := bstep (se 1 (by rfl) ⟨3591944, by rfl⟩ : syracuseStep 4789259 = 7183889) B7183889
theorem B3192839 : Blo 2127435 3192839 := bstep (se 1 (by rfl) ⟨2394629, by rfl⟩ : syracuseStep 3192839 = 4789259) B4789259
theorem B2128559 : Blo 2127435 2128559 := bstep (se 1 (by rfl) ⟨1596419, by rfl⟩ : syracuseStep 2128559 = 3192839) B3192839
theorem B3192845 : Blo 2127435 3192845 := bbase (se 3 (by rfl) ⟨598658, by rfl⟩ : syracuseStep 3192845 = 1197317) (by norm_num)
theorem B2128563 : Blo 2127435 2128563 := bstep (se 1 (by rfl) ⟨1596422, by rfl⟩ : syracuseStep 2128563 = 3192845) B3192845
theorem B4789277 : Blo 2127435 4789277 := bbase (se 3 (by rfl) ⟨897989, by rfl⟩ : syracuseStep 4789277 = 1795979) (by norm_num)
theorem B3192851 : Blo 2127435 3192851 := bstep (se 1 (by rfl) ⟨2394638, by rfl⟩ : syracuseStep 3192851 = 4789277) B4789277
theorem B2128567 : Blo 2127435 2128567 := bstep (se 1 (by rfl) ⟨1596425, by rfl⟩ : syracuseStep 2128567 = 3192851) B3192851
theorem B3591965 : Blo 2127435 3591965 := bbase (se 3 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 3591965 = 1346987) (by norm_num)
theorem B2394643 : Blo 2127435 2394643 := bstep (se 1 (by rfl) ⟨1795982, by rfl⟩ : syracuseStep 2394643 = 3591965) B3591965
theorem B3192857 : Blo 2127435 3192857 := bstep (se 2 (by rfl) ⟨1197321, by rfl⟩ : syracuseStep 3192857 = 2394643) B2394643
theorem B2128571 : Blo 2127435 2128571 := bstep (se 1 (by rfl) ⟨1596428, by rfl⟩ : syracuseStep 2128571 = 3192857) B3192857
theorem B9216229 : Blo 2127435 9216229 := bbase (se 4 (by rfl) ⟨864021, by rfl⟩ : syracuseStep 9216229 = 1728043) (by norm_num)
theorem B12288305 : Blo 2127435 12288305 := bstep (se 2 (by rfl) ⟨4608114, by rfl⟩ : syracuseStep 12288305 = 9216229) B9216229
theorem B32768813 : Blo 2127435 32768813 := bstep (se 3 (by rfl) ⟨6144152, by rfl⟩ : syracuseStep 32768813 = 12288305) B12288305
theorem B21845875 : Blo 2127435 21845875 := bstep (se 1 (by rfl) ⟨16384406, by rfl⟩ : syracuseStep 21845875 = 32768813) B32768813
theorem B29127833 : Blo 2127435 29127833 := bstep (se 2 (by rfl) ⟨10922937, by rfl⟩ : syracuseStep 29127833 = 21845875) B21845875
theorem B19418555 : Blo 2127435 19418555 := bstep (se 1 (by rfl) ⟨14563916, by rfl⟩ : syracuseStep 19418555 = 29127833) B29127833
theorem B12945703 : Blo 2127435 12945703 := bstep (se 1 (by rfl) ⟨9709277, by rfl⟩ : syracuseStep 12945703 = 19418555) B19418555
theorem B17260937 : Blo 2127435 17260937 := bstep (se 2 (by rfl) ⟨6472851, by rfl⟩ : syracuseStep 17260937 = 12945703) B12945703
theorem B11507291 : Blo 2127435 11507291 := bstep (se 1 (by rfl) ⟨8630468, by rfl⟩ : syracuseStep 11507291 = 17260937) B17260937
theorem B7671527 : Blo 2127435 7671527 := bstep (se 1 (by rfl) ⟨5753645, by rfl⟩ : syracuseStep 7671527 = 11507291) B11507291
theorem B5114351 : Blo 2127435 5114351 := bstep (se 1 (by rfl) ⟨3835763, by rfl⟩ : syracuseStep 5114351 = 7671527) B7671527
theorem B13638269 : Blo 2127435 13638269 := bstep (se 3 (by rfl) ⟨2557175, by rfl⟩ : syracuseStep 13638269 = 5114351) B5114351
theorem B9092179 : Blo 2127435 9092179 := bstep (se 1 (by rfl) ⟨6819134, by rfl⟩ : syracuseStep 9092179 = 13638269) B13638269
theorem B12122905 : Blo 2127435 12122905 := bstep (se 2 (by rfl) ⟨4546089, by rfl⟩ : syracuseStep 12122905 = 9092179) B9092179
theorem B16163873 : Blo 2127435 16163873 := bstep (se 2 (by rfl) ⟨6061452, by rfl⟩ : syracuseStep 16163873 = 12122905) B12122905
theorem B10775915 : Blo 2127435 10775915 := bstep (se 1 (by rfl) ⟨8081936, by rfl⟩ : syracuseStep 10775915 = 16163873) B16163873
theorem B7183943 : Blo 2127435 7183943 := bstep (se 1 (by rfl) ⟨5387957, by rfl⟩ : syracuseStep 7183943 = 10775915) B10775915
theorem B4789295 : Blo 2127435 4789295 := bstep (se 1 (by rfl) ⟨3591971, by rfl⟩ : syracuseStep 4789295 = 7183943) B7183943
theorem B3192863 : Blo 2127435 3192863 := bstep (se 1 (by rfl) ⟨2394647, by rfl⟩ : syracuseStep 3192863 = 4789295) B4789295
theorem B2128575 : Blo 2127435 2128575 := bstep (se 1 (by rfl) ⟨1596431, by rfl⟩ : syracuseStep 2128575 = 3192863) B3192863
theorem B3192869 : Blo 2127435 3192869 := bbase (se 4 (by rfl) ⟨299331, by rfl⟩ : syracuseStep 3192869 = 598663) (by norm_num)
theorem B2128579 : Blo 2127435 2128579 := bstep (se 1 (by rfl) ⟨1596434, by rfl⟩ : syracuseStep 2128579 = 3192869) B3192869
theorem B2693989 : Blo 2127435 2693989 := bbase (se 4 (by rfl) ⟨252561, by rfl⟩ : syracuseStep 2693989 = 505123) (by norm_num)
theorem B3591985 : Blo 2127435 3591985 := bstep (se 2 (by rfl) ⟨1346994, by rfl⟩ : syracuseStep 3591985 = 2693989) B2693989
theorem B4789313 : Blo 2127435 4789313 := bstep (se 2 (by rfl) ⟨1795992, by rfl⟩ : syracuseStep 4789313 = 3591985) B3591985
theorem B3192875 : Blo 2127435 3192875 := bstep (se 1 (by rfl) ⟨2394656, by rfl⟩ : syracuseStep 3192875 = 4789313) B4789313
theorem B2128583 : Blo 2127435 2128583 := bstep (se 1 (by rfl) ⟨1596437, by rfl⟩ : syracuseStep 2128583 = 3192875) B3192875
theorem B2394661 : Blo 2127435 2394661 := bbase (se 4 (by rfl) ⟨224499, by rfl⟩ : syracuseStep 2394661 = 448999) (by norm_num)
theorem B3192881 : Blo 2127435 3192881 := bstep (se 2 (by rfl) ⟨1197330, by rfl⟩ : syracuseStep 3192881 = 2394661) B2394661
theorem B2128587 : Blo 2127435 2128587 := bstep (se 1 (by rfl) ⟨1596440, by rfl⟩ : syracuseStep 2128587 = 3192881) B3192881
theorem B2876845 : Blo 2127435 2876845 := bbase (se 3 (by rfl) ⟨539408, by rfl⟩ : syracuseStep 2876845 = 1078817) (by norm_num)
theorem B3835793 : Blo 2127435 3835793 := bstep (se 2 (by rfl) ⟨1438422, by rfl⟩ : syracuseStep 3835793 = 2876845) B2876845
theorem B10228781 : Blo 2127435 10228781 := bstep (se 3 (by rfl) ⟨1917896, by rfl⟩ : syracuseStep 10228781 = 3835793) B3835793
theorem B6819187 : Blo 2127435 6819187 := bstep (se 1 (by rfl) ⟨5114390, by rfl⟩ : syracuseStep 6819187 = 10228781) B10228781
theorem B9092249 : Blo 2127435 9092249 := bstep (se 2 (by rfl) ⟨3409593, by rfl⟩ : syracuseStep 9092249 = 6819187) B6819187
theorem B6061499 : Blo 2127435 6061499 := bstep (se 1 (by rfl) ⟨4546124, by rfl⟩ : syracuseStep 6061499 = 9092249) B9092249
theorem B4040999 : Blo 2127435 4040999 := bstep (se 1 (by rfl) ⟨3030749, by rfl⟩ : syracuseStep 4040999 = 6061499) B6061499
theorem B2693999 : Blo 2127435 2693999 := bstep (se 1 (by rfl) ⟨2020499, by rfl⟩ : syracuseStep 2693999 = 4040999) B4040999
theorem B7183997 : Blo 2127435 7183997 := bstep (se 3 (by rfl) ⟨1346999, by rfl⟩ : syracuseStep 7183997 = 2693999) B2693999
theorem B4789331 : Blo 2127435 4789331 := bstep (se 1 (by rfl) ⟨3591998, by rfl⟩ : syracuseStep 4789331 = 7183997) B7183997
theorem B3192887 : Blo 2127435 3192887 := bstep (se 1 (by rfl) ⟨2394665, by rfl⟩ : syracuseStep 3192887 = 4789331) B4789331
theorem B2128591 : Blo 2127435 2128591 := bstep (se 1 (by rfl) ⟨1596443, by rfl⟩ : syracuseStep 2128591 = 3192887) B3192887
theorem B3192893 : Blo 2127435 3192893 := bbase (se 3 (by rfl) ⟨598667, by rfl⟩ : syracuseStep 3192893 = 1197335) (by norm_num)
theorem B2128595 : Blo 2127435 2128595 := bstep (se 1 (by rfl) ⟨1596446, by rfl⟩ : syracuseStep 2128595 = 3192893) B3192893
theorem B4789349 : Blo 2127435 4789349 := bbase (se 4 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 4789349 = 898003) (by norm_num)
theorem B3192899 : Blo 2127435 3192899 := bstep (se 1 (by rfl) ⟨2394674, by rfl⟩ : syracuseStep 3192899 = 4789349) B4789349
theorem B2128599 : Blo 2127435 2128599 := bstep (se 1 (by rfl) ⟨1596449, by rfl⟩ : syracuseStep 2128599 = 3192899) B3192899
theorem B5388029 : Blo 2127435 5388029 := bbase (se 3 (by rfl) ⟨1010255, by rfl⟩ : syracuseStep 5388029 = 2020511) (by norm_num)
theorem B3592019 : Blo 2127435 3592019 := bstep (se 1 (by rfl) ⟨2694014, by rfl⟩ : syracuseStep 3592019 = 5388029) B5388029
theorem B2394679 : Blo 2127435 2394679 := bstep (se 1 (by rfl) ⟨1796009, by rfl⟩ : syracuseStep 2394679 = 3592019) B3592019
theorem B3192905 : Blo 2127435 3192905 := bstep (se 2 (by rfl) ⟨1197339, by rfl⟩ : syracuseStep 3192905 = 2394679) B2394679
theorem B2128603 : Blo 2127435 2128603 := bstep (se 1 (by rfl) ⟨1596452, by rfl⟩ : syracuseStep 2128603 = 3192905) B3192905
theorem B4041029 : Blo 2127435 4041029 := bbase (se 4 (by rfl) ⟨378846, by rfl⟩ : syracuseStep 4041029 = 757693) (by norm_num)
theorem B10776077 : Blo 2127435 10776077 := bstep (se 3 (by rfl) ⟨2020514, by rfl⟩ : syracuseStep 10776077 = 4041029) B4041029
theorem B7184051 : Blo 2127435 7184051 := bstep (se 1 (by rfl) ⟨5388038, by rfl⟩ : syracuseStep 7184051 = 10776077) B10776077
theorem B4789367 : Blo 2127435 4789367 := bstep (se 1 (by rfl) ⟨3592025, by rfl⟩ : syracuseStep 4789367 = 7184051) B7184051
theorem B3192911 : Blo 2127435 3192911 := bstep (se 1 (by rfl) ⟨2394683, by rfl⟩ : syracuseStep 3192911 = 4789367) B4789367
theorem B2128607 : Blo 2127435 2128607 := bstep (se 1 (by rfl) ⟨1596455, by rfl⟩ : syracuseStep 2128607 = 3192911) B3192911
theorem B3192917 : Blo 2127435 3192917 := bbase (se 8 (by rfl) ⟨18708, by rfl⟩ : syracuseStep 3192917 = 37417) (by norm_num)
theorem B2128611 : Blo 2127435 2128611 := bstep (se 1 (by rfl) ⟨1596458, by rfl⟩ : syracuseStep 2128611 = 3192917) B3192917
theorem B2592113 : Blo 2127435 2592113 := bbase (se 2 (by rfl) ⟨972042, by rfl⟩ : syracuseStep 2592113 = 1944085) (by norm_num)
theorem B27649205 : Blo 2127435 27649205 := bstep (se 5 (by rfl) ⟨1296056, by rfl⟩ : syracuseStep 27649205 = 2592113) B2592113
theorem B18432803 : Blo 2127435 18432803 := bstep (se 1 (by rfl) ⟨13824602, by rfl⟩ : syracuseStep 18432803 = 27649205) B27649205
theorem B49154141 : Blo 2127435 49154141 := bstep (se 3 (by rfl) ⟨9216401, by rfl⟩ : syracuseStep 49154141 = 18432803) B18432803
theorem B131077709 : Blo 2127435 131077709 := bstep (se 3 (by rfl) ⟨24577070, by rfl⟩ : syracuseStep 131077709 = 49154141) B49154141
theorem B87385139 : Blo 2127435 87385139 := bstep (se 1 (by rfl) ⟨65538854, by rfl⟩ : syracuseStep 87385139 = 131077709) B131077709
theorem B58256759 : Blo 2127435 58256759 := bstep (se 1 (by rfl) ⟨43692569, by rfl⟩ : syracuseStep 58256759 = 87385139) B87385139
theorem B155351357 : Blo 2127435 155351357 := bstep (se 3 (by rfl) ⟨29128379, by rfl⟩ : syracuseStep 155351357 = 58256759) B58256759
theorem B103567571 : Blo 2127435 103567571 := bstep (se 1 (by rfl) ⟨77675678, by rfl⟩ : syracuseStep 103567571 = 155351357) B155351357
theorem B69045047 : Blo 2127435 69045047 := bstep (se 1 (by rfl) ⟨51783785, by rfl⟩ : syracuseStep 69045047 = 103567571) B103567571
theorem B46030031 : Blo 2127435 46030031 := bstep (se 1 (by rfl) ⟨34522523, by rfl⟩ : syracuseStep 46030031 = 69045047) B69045047
theorem B30686687 : Blo 2127435 30686687 := bstep (se 1 (by rfl) ⟨23015015, by rfl⟩ : syracuseStep 30686687 = 46030031) B46030031
theorem B20457791 : Blo 2127435 20457791 := bstep (se 1 (by rfl) ⟨15343343, by rfl⟩ : syracuseStep 20457791 = 30686687) B30686687
theorem B13638527 : Blo 2127435 13638527 := bstep (se 1 (by rfl) ⟨10228895, by rfl⟩ : syracuseStep 13638527 = 20457791) B20457791
theorem B9092351 : Blo 2127435 9092351 := bstep (se 1 (by rfl) ⟨6819263, by rfl⟩ : syracuseStep 9092351 = 13638527) B13638527
theorem B6061567 : Blo 2127435 6061567 := bstep (se 1 (by rfl) ⟨4546175, by rfl⟩ : syracuseStep 6061567 = 9092351) B9092351
theorem B8082089 : Blo 2127435 8082089 := bstep (se 2 (by rfl) ⟨3030783, by rfl⟩ : syracuseStep 8082089 = 6061567) B6061567
theorem B5388059 : Blo 2127435 5388059 := bstep (se 1 (by rfl) ⟨4041044, by rfl⟩ : syracuseStep 5388059 = 8082089) B8082089
theorem B3592039 : Blo 2127435 3592039 := bstep (se 1 (by rfl) ⟨2694029, by rfl⟩ : syracuseStep 3592039 = 5388059) B5388059
theorem B4789385 : Blo 2127435 4789385 := bstep (se 2 (by rfl) ⟨1796019, by rfl⟩ : syracuseStep 4789385 = 3592039) B3592039
theorem B3192923 : Blo 2127435 3192923 := bstep (se 1 (by rfl) ⟨2394692, by rfl⟩ : syracuseStep 3192923 = 4789385) B4789385
theorem B2128615 : Blo 2127435 2128615 := bstep (se 1 (by rfl) ⟨1596461, by rfl⟩ : syracuseStep 2128615 = 3192923) B3192923
theorem B2394697 : Blo 2127435 2394697 := bbase (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) (by norm_num)
theorem B3192929 : Blo 2127435 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B2128619 : Blo 2127435 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B10228933 : Blo 2127435 10228933 := bbase (se 4 (by rfl) ⟨958962, by rfl⟩ : syracuseStep 10228933 = 1917925) (by norm_num)
theorem B13638577 : Blo 2127435 13638577 := bstep (se 2 (by rfl) ⟨5114466, by rfl⟩ : syracuseStep 13638577 = 10228933) B10228933
theorem B18184769 : Blo 2127435 18184769 := bstep (se 2 (by rfl) ⟨6819288, by rfl⟩ : syracuseStep 18184769 = 13638577) B13638577
theorem B12123179 : Blo 2127435 12123179 := bstep (se 1 (by rfl) ⟨9092384, by rfl⟩ : syracuseStep 12123179 = 18184769) B18184769
theorem B8082119 : Blo 2127435 8082119 := bstep (se 1 (by rfl) ⟨6061589, by rfl⟩ : syracuseStep 8082119 = 12123179) B12123179
theorem B5388079 : Blo 2127435 5388079 := bstep (se 1 (by rfl) ⟨4041059, by rfl⟩ : syracuseStep 5388079 = 8082119) B8082119
theorem B7184105 : Blo 2127435 7184105 := bstep (se 2 (by rfl) ⟨2694039, by rfl⟩ : syracuseStep 7184105 = 5388079) B5388079
theorem B4789403 : Blo 2127435 4789403 := bstep (se 1 (by rfl) ⟨3592052, by rfl⟩ : syracuseStep 4789403 = 7184105) B7184105
theorem B3192935 : Blo 2127435 3192935 := bstep (se 1 (by rfl) ⟨2394701, by rfl⟩ : syracuseStep 3192935 = 4789403) B4789403
theorem B2128623 : Blo 2127435 2128623 := bstep (se 1 (by rfl) ⟨1596467, by rfl⟩ : syracuseStep 2128623 = 3192935) B3192935
theorem B3192941 : Blo 2127435 3192941 := bbase (se 3 (by rfl) ⟨598676, by rfl⟩ : syracuseStep 3192941 = 1197353) (by norm_num)
theorem B2128627 : Blo 2127435 2128627 := bstep (se 1 (by rfl) ⟨1596470, by rfl⟩ : syracuseStep 2128627 = 3192941) B3192941
theorem B4789421 : Blo 2127435 4789421 := bbase (se 3 (by rfl) ⟨898016, by rfl⟩ : syracuseStep 4789421 = 1796033) (by norm_num)
theorem B3192947 : Blo 2127435 3192947 := bstep (se 1 (by rfl) ⟨2394710, by rfl⟩ : syracuseStep 3192947 = 4789421) B4789421
theorem B2128631 : Blo 2127435 2128631 := bstep (se 1 (by rfl) ⟨1596473, by rfl⟩ : syracuseStep 2128631 = 3192947) B3192947
theorem B6912373 : Blo 2127435 6912373 := bbase (se 5 (by rfl) ⟨324017, by rfl⟩ : syracuseStep 6912373 = 648035) (by norm_num)
theorem B9216497 : Blo 2127435 9216497 := bstep (se 2 (by rfl) ⟨3456186, by rfl⟩ : syracuseStep 9216497 = 6912373) B6912373
theorem B6144331 : Blo 2127435 6144331 := bstep (se 1 (by rfl) ⟨4608248, by rfl⟩ : syracuseStep 6144331 = 9216497) B9216497
theorem B8192441 : Blo 2127435 8192441 := bstep (se 2 (by rfl) ⟨3072165, by rfl⟩ : syracuseStep 8192441 = 6144331) B6144331
theorem B5461627 : Blo 2127435 5461627 := bstep (se 1 (by rfl) ⟨4096220, by rfl⟩ : syracuseStep 5461627 = 8192441) B8192441
theorem B7282169 : Blo 2127435 7282169 := bstep (se 2 (by rfl) ⟨2730813, by rfl⟩ : syracuseStep 7282169 = 5461627) B5461627
theorem B4854779 : Blo 2127435 4854779 := bstep (se 1 (by rfl) ⟨3641084, by rfl⟩ : syracuseStep 4854779 = 7282169) B7282169
theorem B3236519 : Blo 2127435 3236519 := bstep (se 1 (by rfl) ⟨2427389, by rfl⟩ : syracuseStep 3236519 = 4854779) B4854779
theorem B2157679 : Blo 2127435 2157679 := bstep (se 1 (by rfl) ⟨1618259, by rfl⟩ : syracuseStep 2157679 = 3236519) B3236519
theorem B2876905 : Blo 2127435 2876905 := bstep (se 2 (by rfl) ⟨1078839, by rfl⟩ : syracuseStep 2876905 = 2157679) B2157679
theorem B3835873 : Blo 2127435 3835873 := bstep (se 2 (by rfl) ⟨1438452, by rfl⟩ : syracuseStep 3835873 = 2876905) B2876905
theorem B5114497 : Blo 2127435 5114497 := bstep (se 2 (by rfl) ⟨1917936, by rfl⟩ : syracuseStep 5114497 = 3835873) B3835873
theorem B6819329 : Blo 2127435 6819329 := bstep (se 2 (by rfl) ⟨2557248, by rfl⟩ : syracuseStep 6819329 = 5114497) B5114497
theorem B4546219 : Blo 2127435 4546219 := bstep (se 1 (by rfl) ⟨3409664, by rfl⟩ : syracuseStep 4546219 = 6819329) B6819329
theorem B6061625 : Blo 2127435 6061625 := bstep (se 2 (by rfl) ⟨2273109, by rfl⟩ : syracuseStep 6061625 = 4546219) B4546219
theorem B4041083 : Blo 2127435 4041083 := bstep (se 1 (by rfl) ⟨3030812, by rfl⟩ : syracuseStep 4041083 = 6061625) B6061625
theorem B2694055 : Blo 2127435 2694055 := bstep (se 1 (by rfl) ⟨2020541, by rfl⟩ : syracuseStep 2694055 = 4041083) B4041083
theorem B3592073 : Blo 2127435 3592073 := bstep (se 2 (by rfl) ⟨1347027, by rfl⟩ : syracuseStep 3592073 = 2694055) B2694055
theorem B2394715 : Blo 2127435 2394715 := bstep (se 1 (by rfl) ⟨1796036, by rfl⟩ : syracuseStep 2394715 = 3592073) B3592073
theorem B3192953 : Blo 2127435 3192953 := bstep (se 2 (by rfl) ⟨1197357, by rfl⟩ : syracuseStep 3192953 = 2394715) B2394715
theorem B2128635 : Blo 2127435 2128635 := bstep (se 1 (by rfl) ⟨1596476, by rfl⟩ : syracuseStep 2128635 = 3192953) B3192953
theorem B2876909 : Blo 2127435 2876909 := bbase (se 3 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 2876909 = 1078841) (by norm_num)
theorem B7671757 : Blo 2127435 7671757 := bstep (se 3 (by rfl) ⟨1438454, by rfl⟩ : syracuseStep 7671757 = 2876909) B2876909
theorem B10229009 : Blo 2127435 10229009 := bstep (se 2 (by rfl) ⟨3835878, by rfl⟩ : syracuseStep 10229009 = 7671757) B7671757
theorem B27277357 : Blo 2127435 27277357 := bstep (se 3 (by rfl) ⟨5114504, by rfl⟩ : syracuseStep 27277357 = 10229009) B10229009
theorem B36369809 : Blo 2127435 36369809 := bstep (se 2 (by rfl) ⟨13638678, by rfl⟩ : syracuseStep 36369809 = 27277357) B27277357
theorem B24246539 : Blo 2127435 24246539 := bstep (se 1 (by rfl) ⟨18184904, by rfl⟩ : syracuseStep 24246539 = 36369809) B36369809
theorem B16164359 : Blo 2127435 16164359 := bstep (se 1 (by rfl) ⟨12123269, by rfl⟩ : syracuseStep 16164359 = 24246539) B24246539
theorem B10776239 : Blo 2127435 10776239 := bstep (se 1 (by rfl) ⟨8082179, by rfl⟩ : syracuseStep 10776239 = 16164359) B16164359
theorem B7184159 : Blo 2127435 7184159 := bstep (se 1 (by rfl) ⟨5388119, by rfl⟩ : syracuseStep 7184159 = 10776239) B10776239
theorem B4789439 : Blo 2127435 4789439 := bstep (se 1 (by rfl) ⟨3592079, by rfl⟩ : syracuseStep 4789439 = 7184159) B7184159
theorem B3192959 : Blo 2127435 3192959 := bstep (se 1 (by rfl) ⟨2394719, by rfl⟩ : syracuseStep 3192959 = 4789439) B4789439
theorem B2128639 : Blo 2127435 2128639 := bstep (se 1 (by rfl) ⟨1596479, by rfl⟩ : syracuseStep 2128639 = 3192959) B3192959
theorem B3192965 : Blo 2127435 3192965 := bbase (se 4 (by rfl) ⟨299340, by rfl⟩ : syracuseStep 3192965 = 598681) (by norm_num)
theorem B2128643 : Blo 2127435 2128643 := bstep (se 1 (by rfl) ⟨1596482, by rfl⟩ : syracuseStep 2128643 = 3192965) B3192965
theorem B3592093 : Blo 2127435 3592093 := bbase (se 3 (by rfl) ⟨673517, by rfl⟩ : syracuseStep 3592093 = 1347035) (by norm_num)
theorem B4789457 : Blo 2127435 4789457 := bstep (se 2 (by rfl) ⟨1796046, by rfl⟩ : syracuseStep 4789457 = 3592093) B3592093
theorem B3192971 : Blo 2127435 3192971 := bstep (se 1 (by rfl) ⟨2394728, by rfl⟩ : syracuseStep 3192971 = 4789457) B4789457
theorem B2128647 : Blo 2127435 2128647 := bstep (se 1 (by rfl) ⟨1596485, by rfl⟩ : syracuseStep 2128647 = 3192971) B3192971
theorem B2394733 : Blo 2127435 2394733 := bbase (se 3 (by rfl) ⟨449012, by rfl⟩ : syracuseStep 2394733 = 898025) (by norm_num)
theorem B3192977 : Blo 2127435 3192977 := bstep (se 2 (by rfl) ⟨1197366, by rfl⟩ : syracuseStep 3192977 = 2394733) B2394733
theorem B2128651 : Blo 2127435 2128651 := bstep (se 1 (by rfl) ⟨1596488, by rfl⟩ : syracuseStep 2128651 = 3192977) B3192977
theorem B7184213 : Blo 2127435 7184213 := bbase (se 9 (by rfl) ⟨21047, by rfl⟩ : syracuseStep 7184213 = 42095) (by norm_num)
theorem B4789475 : Blo 2127435 4789475 := bstep (se 1 (by rfl) ⟨3592106, by rfl⟩ : syracuseStep 4789475 = 7184213) B7184213
theorem B3192983 : Blo 2127435 3192983 := bstep (se 1 (by rfl) ⟨2394737, by rfl⟩ : syracuseStep 3192983 = 4789475) B4789475
theorem B2128655 : Blo 2127435 2128655 := bstep (se 1 (by rfl) ⟨1596491, by rfl⟩ : syracuseStep 2128655 = 3192983) B3192983
theorem B3192989 : Blo 2127435 3192989 := bbase (se 3 (by rfl) ⟨598685, by rfl⟩ : syracuseStep 3192989 = 1197371) (by norm_num)
theorem B2128659 : Blo 2127435 2128659 := bstep (se 1 (by rfl) ⟨1596494, by rfl⟩ : syracuseStep 2128659 = 3192989) B3192989
theorem B4789493 : Blo 2127435 4789493 := bbase (se 5 (by rfl) ⟨224507, by rfl⟩ : syracuseStep 4789493 = 449015) (by norm_num)
theorem B3192995 : Blo 2127435 3192995 := bstep (se 1 (by rfl) ⟨2394746, by rfl⟩ : syracuseStep 3192995 = 4789493) B4789493
theorem B2128663 : Blo 2127435 2128663 := bstep (se 1 (by rfl) ⟨1596497, by rfl⟩ : syracuseStep 2128663 = 3192995) B3192995
theorem B4315421 : Blo 2127435 4315421 := bbase (se 3 (by rfl) ⟨809141, by rfl⟩ : syracuseStep 4315421 = 1618283) (by norm_num)
theorem B11507789 : Blo 2127435 11507789 := bstep (se 3 (by rfl) ⟨2157710, by rfl⟩ : syracuseStep 11507789 = 4315421) B4315421
theorem B30687437 : Blo 2127435 30687437 := bstep (se 3 (by rfl) ⟨5753894, by rfl⟩ : syracuseStep 30687437 = 11507789) B11507789
theorem B20458291 : Blo 2127435 20458291 := bstep (se 1 (by rfl) ⟨15343718, by rfl⟩ : syracuseStep 20458291 = 30687437) B30687437
theorem B27277721 : Blo 2127435 27277721 := bstep (se 2 (by rfl) ⟨10229145, by rfl⟩ : syracuseStep 27277721 = 20458291) B20458291
theorem B18185147 : Blo 2127435 18185147 := bstep (se 1 (by rfl) ⟨13638860, by rfl⟩ : syracuseStep 18185147 = 27277721) B27277721
theorem B12123431 : Blo 2127435 12123431 := bstep (se 1 (by rfl) ⟨9092573, by rfl⟩ : syracuseStep 12123431 = 18185147) B18185147
theorem B8082287 : Blo 2127435 8082287 := bstep (se 1 (by rfl) ⟨6061715, by rfl⟩ : syracuseStep 8082287 = 12123431) B12123431
theorem B5388191 : Blo 2127435 5388191 := bstep (se 1 (by rfl) ⟨4041143, by rfl⟩ : syracuseStep 5388191 = 8082287) B8082287
theorem B3592127 : Blo 2127435 3592127 := bstep (se 1 (by rfl) ⟨2694095, by rfl⟩ : syracuseStep 3592127 = 5388191) B5388191
theorem B2394751 : Blo 2127435 2394751 := bstep (se 1 (by rfl) ⟨1796063, by rfl⟩ : syracuseStep 2394751 = 3592127) B3592127
theorem B3193001 : Blo 2127435 3193001 := bstep (se 2 (by rfl) ⟨1197375, by rfl⟩ : syracuseStep 3193001 = 2394751) B2394751
theorem B2128667 : Blo 2127435 2128667 := bstep (se 1 (by rfl) ⟨1596500, by rfl⟩ : syracuseStep 2128667 = 3193001) B3193001
theorem B3236573 : Blo 2127435 3236573 := bbase (se 3 (by rfl) ⟨606857, by rfl⟩ : syracuseStep 3236573 = 1213715) (by norm_num)
theorem B2157715 : Blo 2127435 2157715 := bstep (se 1 (by rfl) ⟨1618286, by rfl⟩ : syracuseStep 2157715 = 3236573) B3236573
theorem B2876953 : Blo 2127435 2876953 := bstep (se 2 (by rfl) ⟨1078857, by rfl⟩ : syracuseStep 2876953 = 2157715) B2157715
theorem B3835937 : Blo 2127435 3835937 := bstep (se 2 (by rfl) ⟨1438476, by rfl⟩ : syracuseStep 3835937 = 2876953) B2876953
theorem B10229165 : Blo 2127435 10229165 := bstep (se 3 (by rfl) ⟨1917968, by rfl⟩ : syracuseStep 10229165 = 3835937) B3835937
theorem B6819443 : Blo 2127435 6819443 := bstep (se 1 (by rfl) ⟨5114582, by rfl⟩ : syracuseStep 6819443 = 10229165) B10229165
theorem B4546295 : Blo 2127435 4546295 := bstep (se 1 (by rfl) ⟨3409721, by rfl⟩ : syracuseStep 4546295 = 6819443) B6819443
theorem B3030863 : Blo 2127435 3030863 := bstep (se 1 (by rfl) ⟨2273147, by rfl⟩ : syracuseStep 3030863 = 4546295) B4546295
theorem B8082301 : Blo 2127435 8082301 := bstep (se 3 (by rfl) ⟨1515431, by rfl⟩ : syracuseStep 8082301 = 3030863) B3030863
theorem B10776401 : Blo 2127435 10776401 := bstep (se 2 (by rfl) ⟨4041150, by rfl⟩ : syracuseStep 10776401 = 8082301) B8082301
theorem B7184267 : Blo 2127435 7184267 := bstep (se 1 (by rfl) ⟨5388200, by rfl⟩ : syracuseStep 7184267 = 10776401) B10776401
theorem B4789511 : Blo 2127435 4789511 := bstep (se 1 (by rfl) ⟨3592133, by rfl⟩ : syracuseStep 4789511 = 7184267) B7184267
theorem B3193007 : Blo 2127435 3193007 := bstep (se 1 (by rfl) ⟨2394755, by rfl⟩ : syracuseStep 3193007 = 4789511) B4789511
theorem B2128671 : Blo 2127435 2128671 := bstep (se 1 (by rfl) ⟨1596503, by rfl⟩ : syracuseStep 2128671 = 3193007) B3193007
theorem B3193013 : Blo 2127435 3193013 := bbase (se 5 (by rfl) ⟨149672, by rfl⟩ : syracuseStep 3193013 = 299345) (by norm_num)
theorem B2128675 : Blo 2127435 2128675 := bstep (se 1 (by rfl) ⟨1596506, by rfl⟩ : syracuseStep 2128675 = 3193013) B3193013
theorem B5388221 : Blo 2127435 5388221 := bbase (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) (by norm_num)
theorem B3592147 : Blo 2127435 3592147 := bstep (se 1 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 3592147 = 5388221) B5388221
theorem B4789529 : Blo 2127435 4789529 := bstep (se 2 (by rfl) ⟨1796073, by rfl⟩ : syracuseStep 4789529 = 3592147) B3592147
theorem B3193019 : Blo 2127435 3193019 := bstep (se 1 (by rfl) ⟨2394764, by rfl⟩ : syracuseStep 3193019 = 4789529) B4789529
theorem B2128679 : Blo 2127435 2128679 := bstep (se 1 (by rfl) ⟨1596509, by rfl⟩ : syracuseStep 2128679 = 3193019) B3193019
theorem B2394769 : Blo 2127435 2394769 := bbase (se 2 (by rfl) ⟨898038, by rfl⟩ : syracuseStep 2394769 = 1796077) (by norm_num)
theorem B3193025 : Blo 2127435 3193025 := bstep (se 2 (by rfl) ⟨1197384, by rfl⟩ : syracuseStep 3193025 = 2394769) B2394769
theorem B2128683 : Blo 2127435 2128683 := bstep (se 1 (by rfl) ⟨1596512, by rfl⟩ : syracuseStep 2128683 = 3193025) B3193025
theorem B4041181 : Blo 2127435 4041181 := bbase (se 3 (by rfl) ⟨757721, by rfl⟩ : syracuseStep 4041181 = 1515443) (by norm_num)
theorem B5388241 : Blo 2127435 5388241 := bstep (se 2 (by rfl) ⟨2020590, by rfl⟩ : syracuseStep 5388241 = 4041181) B4041181
theorem B7184321 : Blo 2127435 7184321 := bstep (se 2 (by rfl) ⟨2694120, by rfl⟩ : syracuseStep 7184321 = 5388241) B5388241
theorem B4789547 : Blo 2127435 4789547 := bstep (se 1 (by rfl) ⟨3592160, by rfl⟩ : syracuseStep 4789547 = 7184321) B7184321
theorem B3193031 : Blo 2127435 3193031 := bstep (se 1 (by rfl) ⟨2394773, by rfl⟩ : syracuseStep 3193031 = 4789547) B4789547
theorem B2128687 : Blo 2127435 2128687 := bstep (se 1 (by rfl) ⟨1596515, by rfl⟩ : syracuseStep 2128687 = 3193031) B3193031
theorem B3193037 : Blo 2127435 3193037 := bbase (se 3 (by rfl) ⟨598694, by rfl⟩ : syracuseStep 3193037 = 1197389) (by norm_num)
theorem B2128691 : Blo 2127435 2128691 := bstep (se 1 (by rfl) ⟨1596518, by rfl⟩ : syracuseStep 2128691 = 3193037) B3193037
theorem B4789565 : Blo 2127435 4789565 := bbase (se 3 (by rfl) ⟨898043, by rfl⟩ : syracuseStep 4789565 = 1796087) (by norm_num)
theorem B3193043 : Blo 2127435 3193043 := bstep (se 1 (by rfl) ⟨2394782, by rfl⟩ : syracuseStep 3193043 = 4789565) B4789565
theorem B2128695 : Blo 2127435 2128695 := bstep (se 1 (by rfl) ⟨1596521, by rfl⟩ : syracuseStep 2128695 = 3193043) B3193043
theorem B3592181 : Blo 2127435 3592181 := bbase (se 5 (by rfl) ⟨168383, by rfl⟩ : syracuseStep 3592181 = 336767) (by norm_num)
theorem B2394787 : Blo 2127435 2394787 := bstep (se 1 (by rfl) ⟨1796090, by rfl⟩ : syracuseStep 2394787 = 3592181) B3592181
theorem B3193049 : Blo 2127435 3193049 := bstep (se 2 (by rfl) ⟨1197393, by rfl⟩ : syracuseStep 3193049 = 2394787) B2394787
theorem B2128699 : Blo 2127435 2128699 := bstep (se 1 (by rfl) ⟨1596524, by rfl⟩ : syracuseStep 2128699 = 3193049) B3193049
theorem B7671989 : Blo 2127435 7671989 := bbase (se 5 (by rfl) ⟨359624, by rfl⟩ : syracuseStep 7671989 = 719249) (by norm_num)
theorem B5114659 : Blo 2127435 5114659 := bstep (se 1 (by rfl) ⟨3835994, by rfl⟩ : syracuseStep 5114659 = 7671989) B7671989
theorem B6819545 : Blo 2127435 6819545 := bstep (se 2 (by rfl) ⟨2557329, by rfl⟩ : syracuseStep 6819545 = 5114659) B5114659
theorem B4546363 : Blo 2127435 4546363 := bstep (se 1 (by rfl) ⟨3409772, by rfl⟩ : syracuseStep 4546363 = 6819545) B6819545
theorem B6061817 : Blo 2127435 6061817 := bstep (se 2 (by rfl) ⟨2273181, by rfl⟩ : syracuseStep 6061817 = 4546363) B4546363
theorem B16164845 : Blo 2127435 16164845 := bstep (se 3 (by rfl) ⟨3030908, by rfl⟩ : syracuseStep 16164845 = 6061817) B6061817
theorem B10776563 : Blo 2127435 10776563 := bstep (se 1 (by rfl) ⟨8082422, by rfl⟩ : syracuseStep 10776563 = 16164845) B16164845
theorem B7184375 : Blo 2127435 7184375 := bstep (se 1 (by rfl) ⟨5388281, by rfl⟩ : syracuseStep 7184375 = 10776563) B10776563
theorem B4789583 : Blo 2127435 4789583 := bstep (se 1 (by rfl) ⟨3592187, by rfl⟩ : syracuseStep 4789583 = 7184375) B7184375
theorem B3193055 : Blo 2127435 3193055 := bstep (se 1 (by rfl) ⟨2394791, by rfl⟩ : syracuseStep 3193055 = 4789583) B4789583
theorem B2128703 : Blo 2127435 2128703 := bstep (se 1 (by rfl) ⟨1596527, by rfl⟩ : syracuseStep 2128703 = 3193055) B3193055
theorem B3193061 : Blo 2127435 3193061 := bbase (se 4 (by rfl) ⟨299349, by rfl⟩ : syracuseStep 3193061 = 598699) (by norm_num)
theorem B2128707 : Blo 2127435 2128707 := bstep (se 1 (by rfl) ⟨1596530, by rfl⟩ : syracuseStep 2128707 = 3193061) B3193061
theorem B4546381 : Blo 2127435 4546381 := bbase (se 3 (by rfl) ⟨852446, by rfl⟩ : syracuseStep 4546381 = 1704893) (by norm_num)
theorem B6061841 : Blo 2127435 6061841 := bstep (se 2 (by rfl) ⟨2273190, by rfl⟩ : syracuseStep 6061841 = 4546381) B4546381
theorem B4041227 : Blo 2127435 4041227 := bstep (se 1 (by rfl) ⟨3030920, by rfl⟩ : syracuseStep 4041227 = 6061841) B6061841
theorem B2694151 : Blo 2127435 2694151 := bstep (se 1 (by rfl) ⟨2020613, by rfl⟩ : syracuseStep 2694151 = 4041227) B4041227
theorem B3592201 : Blo 2127435 3592201 := bstep (se 2 (by rfl) ⟨1347075, by rfl⟩ : syracuseStep 3592201 = 2694151) B2694151
theorem B4789601 : Blo 2127435 4789601 := bstep (se 2 (by rfl) ⟨1796100, by rfl⟩ : syracuseStep 4789601 = 3592201) B3592201
theorem B3193067 : Blo 2127435 3193067 := bstep (se 1 (by rfl) ⟨2394800, by rfl⟩ : syracuseStep 3193067 = 4789601) B4789601
theorem B2128711 : Blo 2127435 2128711 := bstep (se 1 (by rfl) ⟨1596533, by rfl⟩ : syracuseStep 2128711 = 3193067) B3193067
theorem B2394805 : Blo 2127435 2394805 := bbase (se 5 (by rfl) ⟨112256, by rfl⟩ : syracuseStep 2394805 = 224513) (by norm_num)
theorem B3193073 : Blo 2127435 3193073 := bstep (se 2 (by rfl) ⟨1197402, by rfl⟩ : syracuseStep 3193073 = 2394805) B2394805
theorem B2128715 : Blo 2127435 2128715 := bstep (se 1 (by rfl) ⟨1596536, by rfl⟩ : syracuseStep 2128715 = 3193073) B3193073
theorem B2694161 : Blo 2127435 2694161 := bbase (se 2 (by rfl) ⟨1010310, by rfl⟩ : syracuseStep 2694161 = 2020621) (by norm_num)
theorem B7184429 : Blo 2127435 7184429 := bstep (se 3 (by rfl) ⟨1347080, by rfl⟩ : syracuseStep 7184429 = 2694161) B2694161
theorem B4789619 : Blo 2127435 4789619 := bstep (se 1 (by rfl) ⟨3592214, by rfl⟩ : syracuseStep 4789619 = 7184429) B7184429
theorem B3193079 : Blo 2127435 3193079 := bstep (se 1 (by rfl) ⟨2394809, by rfl⟩ : syracuseStep 3193079 = 4789619) B4789619
theorem B2128719 : Blo 2127435 2128719 := bstep (se 1 (by rfl) ⟨1596539, by rfl⟩ : syracuseStep 2128719 = 3193079) B3193079
theorem B3193085 : Blo 2127435 3193085 := bbase (se 3 (by rfl) ⟨598703, by rfl⟩ : syracuseStep 3193085 = 1197407) (by norm_num)
theorem B2128723 : Blo 2127435 2128723 := bstep (se 1 (by rfl) ⟨1596542, by rfl⟩ : syracuseStep 2128723 = 3193085) B3193085
theorem B4789637 : Blo 2127435 4789637 := bbase (se 4 (by rfl) ⟨449028, by rfl⟩ : syracuseStep 4789637 = 898057) (by norm_num)
theorem B3193091 : Blo 2127435 3193091 := bstep (se 1 (by rfl) ⟨2394818, by rfl⟩ : syracuseStep 3193091 = 4789637) B4789637
theorem B2128727 : Blo 2127435 2128727 := bstep (se 1 (by rfl) ⟨1596545, by rfl⟩ : syracuseStep 2128727 = 3193091) B3193091
theorem B3030949 : Blo 2127435 3030949 := bbase (se 4 (by rfl) ⟨284151, by rfl⟩ : syracuseStep 3030949 = 568303) (by norm_num)
theorem B4041265 : Blo 2127435 4041265 := bstep (se 2 (by rfl) ⟨1515474, by rfl⟩ : syracuseStep 4041265 = 3030949) B3030949
theorem B5388353 : Blo 2127435 5388353 := bstep (se 2 (by rfl) ⟨2020632, by rfl⟩ : syracuseStep 5388353 = 4041265) B4041265
theorem B3592235 : Blo 2127435 3592235 := bstep (se 1 (by rfl) ⟨2694176, by rfl⟩ : syracuseStep 3592235 = 5388353) B5388353
theorem B2394823 : Blo 2127435 2394823 := bstep (se 1 (by rfl) ⟨1796117, by rfl⟩ : syracuseStep 2394823 = 3592235) B3592235
theorem B3193097 : Blo 2127435 3193097 := bstep (se 2 (by rfl) ⟨1197411, by rfl⟩ : syracuseStep 3193097 = 2394823) B2394823
theorem B2128731 : Blo 2127435 2128731 := bstep (se 1 (by rfl) ⟨1596548, by rfl⟩ : syracuseStep 2128731 = 3193097) B3193097
theorem B10776725 : Blo 2127435 10776725 := bbase (se 6 (by rfl) ⟨252579, by rfl⟩ : syracuseStep 10776725 = 505159) (by norm_num)
theorem B7184483 : Blo 2127435 7184483 := bstep (se 1 (by rfl) ⟨5388362, by rfl⟩ : syracuseStep 7184483 = 10776725) B10776725
theorem B4789655 : Blo 2127435 4789655 := bstep (se 1 (by rfl) ⟨3592241, by rfl⟩ : syracuseStep 4789655 = 7184483) B7184483
theorem B3193103 : Blo 2127435 3193103 := bstep (se 1 (by rfl) ⟨2394827, by rfl⟩ : syracuseStep 3193103 = 4789655) B4789655
theorem B2128735 : Blo 2127435 2128735 := bstep (se 1 (by rfl) ⟨1596551, by rfl⟩ : syracuseStep 2128735 = 3193103) B3193103
theorem B3193109 : Blo 2127435 3193109 := bbase (se 6 (by rfl) ⟨74838, by rfl⟩ : syracuseStep 3193109 = 149677) (by norm_num)
theorem B2128739 : Blo 2127435 2128739 := bstep (se 1 (by rfl) ⟨1596554, by rfl⟩ : syracuseStep 2128739 = 3193109) B3193109
theorem B7672133 : Blo 2127435 7672133 := bbase (se 4 (by rfl) ⟨719262, by rfl⟩ : syracuseStep 7672133 = 1438525) (by norm_num)
theorem B5114755 : Blo 2127435 5114755 := bstep (se 1 (by rfl) ⟨3836066, by rfl⟩ : syracuseStep 5114755 = 7672133) B7672133
theorem B27278693 : Blo 2127435 27278693 := bstep (se 4 (by rfl) ⟨2557377, by rfl⟩ : syracuseStep 27278693 = 5114755) B5114755
theorem B18185795 : Blo 2127435 18185795 := bstep (se 1 (by rfl) ⟨13639346, by rfl⟩ : syracuseStep 18185795 = 27278693) B27278693
theorem B12123863 : Blo 2127435 12123863 := bstep (se 1 (by rfl) ⟨9092897, by rfl⟩ : syracuseStep 12123863 = 18185795) B18185795
theorem B8082575 : Blo 2127435 8082575 := bstep (se 1 (by rfl) ⟨6061931, by rfl⟩ : syracuseStep 8082575 = 12123863) B12123863
theorem B5388383 : Blo 2127435 5388383 := bstep (se 1 (by rfl) ⟨4041287, by rfl⟩ : syracuseStep 5388383 = 8082575) B8082575
theorem B3592255 : Blo 2127435 3592255 := bstep (se 1 (by rfl) ⟨2694191, by rfl⟩ : syracuseStep 3592255 = 5388383) B5388383
theorem B4789673 : Blo 2127435 4789673 := bstep (se 2 (by rfl) ⟨1796127, by rfl⟩ : syracuseStep 4789673 = 3592255) B3592255
theorem B3193115 : Blo 2127435 3193115 := bstep (se 1 (by rfl) ⟨2394836, by rfl⟩ : syracuseStep 3193115 = 4789673) B4789673
theorem B2128743 : Blo 2127435 2128743 := bstep (se 1 (by rfl) ⟨1596557, by rfl⟩ : syracuseStep 2128743 = 3193115) B3193115
theorem B2394841 : Blo 2127435 2394841 := bbase (se 2 (by rfl) ⟨898065, by rfl⟩ : syracuseStep 2394841 = 1796131) (by norm_num)
theorem B3193121 : Blo 2127435 3193121 := bstep (se 2 (by rfl) ⟨1197420, by rfl⟩ : syracuseStep 3193121 = 2394841) B2394841
theorem B2128747 : Blo 2127435 2128747 := bstep (se 1 (by rfl) ⟨1596560, by rfl⟩ : syracuseStep 2128747 = 3193121) B3193121
theorem B2273233 : Blo 2127435 2273233 := bbase (se 2 (by rfl) ⟨852462, by rfl⟩ : syracuseStep 2273233 = 1704925) (by norm_num)
theorem B3030977 : Blo 2127435 3030977 := bstep (se 2 (by rfl) ⟨1136616, by rfl⟩ : syracuseStep 3030977 = 2273233) B2273233
theorem B8082605 : Blo 2127435 8082605 := bstep (se 3 (by rfl) ⟨1515488, by rfl⟩ : syracuseStep 8082605 = 3030977) B3030977
theorem B5388403 : Blo 2127435 5388403 := bstep (se 1 (by rfl) ⟨4041302, by rfl⟩ : syracuseStep 5388403 = 8082605) B8082605
theorem B7184537 : Blo 2127435 7184537 := bstep (se 2 (by rfl) ⟨2694201, by rfl⟩ : syracuseStep 7184537 = 5388403) B5388403
theorem B4789691 : Blo 2127435 4789691 := bstep (se 1 (by rfl) ⟨3592268, by rfl⟩ : syracuseStep 4789691 = 7184537) B7184537
theorem B3193127 : Blo 2127435 3193127 := bstep (se 1 (by rfl) ⟨2394845, by rfl⟩ : syracuseStep 3193127 = 4789691) B4789691
theorem B2128751 : Blo 2127435 2128751 := bstep (se 1 (by rfl) ⟨1596563, by rfl⟩ : syracuseStep 2128751 = 3193127) B3193127
theorem B3193133 : Blo 2127435 3193133 := bbase (se 3 (by rfl) ⟨598712, by rfl⟩ : syracuseStep 3193133 = 1197425) (by norm_num)
theorem B2128755 : Blo 2127435 2128755 := bstep (se 1 (by rfl) ⟨1596566, by rfl⟩ : syracuseStep 2128755 = 3193133) B3193133
theorem B4789709 : Blo 2127435 4789709 := bbase (se 3 (by rfl) ⟨898070, by rfl⟩ : syracuseStep 4789709 = 1796141) (by norm_num)
theorem B3193139 : Blo 2127435 3193139 := bstep (se 1 (by rfl) ⟨2394854, by rfl⟩ : syracuseStep 3193139 = 4789709) B4789709
theorem B2128759 : Blo 2127435 2128759 := bstep (se 1 (by rfl) ⟨1596569, by rfl⟩ : syracuseStep 2128759 = 3193139) B3193139
theorem B2694217 : Blo 2127435 2694217 := bbase (se 2 (by rfl) ⟨1010331, by rfl⟩ : syracuseStep 2694217 = 2020663) (by norm_num)
theorem B3592289 : Blo 2127435 3592289 := bstep (se 2 (by rfl) ⟨1347108, by rfl⟩ : syracuseStep 3592289 = 2694217) B2694217
theorem B2394859 : Blo 2127435 2394859 := bstep (se 1 (by rfl) ⟨1796144, by rfl⟩ : syracuseStep 2394859 = 3592289) B3592289
theorem B3193145 : Blo 2127435 3193145 := bstep (se 2 (by rfl) ⟨1197429, by rfl⟩ : syracuseStep 3193145 = 2394859) B2394859
theorem B2128763 : Blo 2127435 2128763 := bstep (se 1 (by rfl) ⟨1596572, by rfl⟩ : syracuseStep 2128763 = 3193145) B3193145
theorem B15344437 : Blo 2127435 15344437 := bbase (se 5 (by rfl) ⟨719270, by rfl⟩ : syracuseStep 15344437 = 1438541) (by norm_num)
theorem B20459249 : Blo 2127435 20459249 := bstep (se 2 (by rfl) ⟨7672218, by rfl⟩ : syracuseStep 20459249 = 15344437) B15344437
theorem B13639499 : Blo 2127435 13639499 := bstep (se 1 (by rfl) ⟨10229624, by rfl⟩ : syracuseStep 13639499 = 20459249) B20459249
theorem B9092999 : Blo 2127435 9092999 := bstep (se 1 (by rfl) ⟨6819749, by rfl⟩ : syracuseStep 9092999 = 13639499) B13639499
theorem B24247997 : Blo 2127435 24247997 := bstep (se 3 (by rfl) ⟨4546499, by rfl⟩ : syracuseStep 24247997 = 9092999) B9092999
theorem B16165331 : Blo 2127435 16165331 := bstep (se 1 (by rfl) ⟨12123998, by rfl⟩ : syracuseStep 16165331 = 24247997) B24247997
theorem B10776887 : Blo 2127435 10776887 := bstep (se 1 (by rfl) ⟨8082665, by rfl⟩ : syracuseStep 10776887 = 16165331) B16165331
theorem B7184591 : Blo 2127435 7184591 := bstep (se 1 (by rfl) ⟨5388443, by rfl⟩ : syracuseStep 7184591 = 10776887) B10776887
theorem B4789727 : Blo 2127435 4789727 := bstep (se 1 (by rfl) ⟨3592295, by rfl⟩ : syracuseStep 4789727 = 7184591) B7184591
theorem B3193151 : Blo 2127435 3193151 := bstep (se 1 (by rfl) ⟨2394863, by rfl⟩ : syracuseStep 3193151 = 4789727) B4789727
theorem B2128767 : Blo 2127435 2128767 := bstep (se 1 (by rfl) ⟨1596575, by rfl⟩ : syracuseStep 2128767 = 3193151) B3193151
theorem B3193157 : Blo 2127435 3193157 := bbase (se 4 (by rfl) ⟨299358, by rfl⟩ : syracuseStep 3193157 = 598717) (by norm_num)
theorem B2128771 : Blo 2127435 2128771 := bstep (se 1 (by rfl) ⟨1596578, by rfl⟩ : syracuseStep 2128771 = 3193157) B3193157
theorem B3592309 : Blo 2127435 3592309 := bbase (se 5 (by rfl) ⟨168389, by rfl⟩ : syracuseStep 3592309 = 336779) (by norm_num)
theorem B4789745 : Blo 2127435 4789745 := bstep (se 2 (by rfl) ⟨1796154, by rfl⟩ : syracuseStep 4789745 = 3592309) B3592309
theorem B3193163 : Blo 2127435 3193163 := bstep (se 1 (by rfl) ⟨2394872, by rfl⟩ : syracuseStep 3193163 = 4789745) B4789745
theorem B2128775 : Blo 2127435 2128775 := bstep (se 1 (by rfl) ⟨1596581, by rfl⟩ : syracuseStep 2128775 = 3193163) B3193163
theorem B2394877 : Blo 2127435 2394877 := bbase (se 3 (by rfl) ⟨449039, by rfl⟩ : syracuseStep 2394877 = 898079) (by norm_num)
theorem B3193169 : Blo 2127435 3193169 := bstep (se 2 (by rfl) ⟨1197438, by rfl⟩ : syracuseStep 3193169 = 2394877) B2394877
theorem B2128779 : Blo 2127435 2128779 := bstep (se 1 (by rfl) ⟨1596584, by rfl⟩ : syracuseStep 2128779 = 3193169) B3193169
theorem B7184645 : Blo 2127435 7184645 := bbase (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) (by norm_num)
theorem B4789763 : Blo 2127435 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B3193175 : Blo 2127435 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B2128783 : Blo 2127435 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B3193181 : Blo 2127435 3193181 := bbase (se 3 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 3193181 = 1197443) (by norm_num)
theorem B2128787 : Blo 2127435 2128787 := bstep (se 1 (by rfl) ⟨1596590, by rfl⟩ : syracuseStep 2128787 = 3193181) B3193181
theorem B4789781 : Blo 2127435 4789781 := bbase (se 6 (by rfl) ⟨112260, by rfl⟩ : syracuseStep 4789781 = 224521) (by norm_num)
theorem B3193187 : Blo 2127435 3193187 := bstep (se 1 (by rfl) ⟨2394890, by rfl⟩ : syracuseStep 3193187 = 4789781) B4789781
theorem B2128791 : Blo 2127435 2128791 := bstep (se 1 (by rfl) ⟨1596593, by rfl⟩ : syracuseStep 2128791 = 3193187) B3193187
theorem B8082773 : Blo 2127435 8082773 := bbase (se 17 (by rfl) ⟨92, by rfl⟩ : syracuseStep 8082773 = 185) (by norm_num)
theorem B5388515 : Blo 2127435 5388515 := bstep (se 1 (by rfl) ⟨4041386, by rfl⟩ : syracuseStep 5388515 = 8082773) B8082773
theorem B3592343 : Blo 2127435 3592343 := bstep (se 1 (by rfl) ⟨2694257, by rfl⟩ : syracuseStep 3592343 = 5388515) B5388515
theorem B2394895 : Blo 2127435 2394895 := bstep (se 1 (by rfl) ⟨1796171, by rfl⟩ : syracuseStep 2394895 = 3592343) B3592343
theorem B3193193 : Blo 2127435 3193193 := bstep (se 2 (by rfl) ⟨1197447, by rfl⟩ : syracuseStep 3193193 = 2394895) B2394895
theorem B2128795 : Blo 2127435 2128795 := bstep (se 1 (by rfl) ⟨1596596, by rfl⟩ : syracuseStep 2128795 = 3193193) B3193193
theorem B12124181 : Blo 2127435 12124181 := bbase (se 6 (by rfl) ⟨284160, by rfl⟩ : syracuseStep 12124181 = 568321) (by norm_num)
theorem B8082787 : Blo 2127435 8082787 := bstep (se 1 (by rfl) ⟨6062090, by rfl⟩ : syracuseStep 8082787 = 12124181) B12124181
theorem B10777049 : Blo 2127435 10777049 := bstep (se 2 (by rfl) ⟨4041393, by rfl⟩ : syracuseStep 10777049 = 8082787) B8082787
theorem B7184699 : Blo 2127435 7184699 := bstep (se 1 (by rfl) ⟨5388524, by rfl⟩ : syracuseStep 7184699 = 10777049) B10777049
theorem B4789799 : Blo 2127435 4789799 := bstep (se 1 (by rfl) ⟨3592349, by rfl⟩ : syracuseStep 4789799 = 7184699) B7184699
theorem B3193199 : Blo 2127435 3193199 := bstep (se 1 (by rfl) ⟨2394899, by rfl⟩ : syracuseStep 3193199 = 4789799) B4789799
theorem B2128799 : Blo 2127435 2128799 := bstep (se 1 (by rfl) ⟨1596599, by rfl⟩ : syracuseStep 2128799 = 3193199) B3193199
theorem B3193205 : Blo 2127435 3193205 := bbase (se 5 (by rfl) ⟨149681, by rfl⟩ : syracuseStep 3193205 = 299363) (by norm_num)
theorem B2128803 : Blo 2127435 2128803 := bstep (se 1 (by rfl) ⟨1596602, by rfl⟩ : syracuseStep 2128803 = 3193205) B3193205
theorem B2273293 : Blo 2127435 2273293 := bbase (se 3 (by rfl) ⟨426242, by rfl⟩ : syracuseStep 2273293 = 852485) (by norm_num)
theorem B3031057 : Blo 2127435 3031057 := bstep (se 2 (by rfl) ⟨1136646, by rfl⟩ : syracuseStep 3031057 = 2273293) B2273293
theorem B4041409 : Blo 2127435 4041409 := bstep (se 2 (by rfl) ⟨1515528, by rfl⟩ : syracuseStep 4041409 = 3031057) B3031057
theorem B5388545 : Blo 2127435 5388545 := bstep (se 2 (by rfl) ⟨2020704, by rfl⟩ : syracuseStep 5388545 = 4041409) B4041409
theorem B3592363 : Blo 2127435 3592363 := bstep (se 1 (by rfl) ⟨2694272, by rfl⟩ : syracuseStep 3592363 = 5388545) B5388545
theorem B4789817 : Blo 2127435 4789817 := bstep (se 2 (by rfl) ⟨1796181, by rfl⟩ : syracuseStep 4789817 = 3592363) B3592363
theorem B3193211 : Blo 2127435 3193211 := bstep (se 1 (by rfl) ⟨2394908, by rfl⟩ : syracuseStep 3193211 = 4789817) B4789817
theorem B2128807 : Blo 2127435 2128807 := bstep (se 1 (by rfl) ⟨1596605, by rfl⟩ : syracuseStep 2128807 = 3193211) B3193211
theorem B2394913 : Blo 2127435 2394913 := bbase (se 2 (by rfl) ⟨898092, by rfl⟩ : syracuseStep 2394913 = 1796185) (by norm_num)
theorem B3193217 : Blo 2127435 3193217 := bstep (se 2 (by rfl) ⟨1197456, by rfl⟩ : syracuseStep 3193217 = 2394913) B2394913
theorem B2128811 : Blo 2127435 2128811 := bstep (se 1 (by rfl) ⟨1596608, by rfl⟩ : syracuseStep 2128811 = 3193217) B3193217
theorem B5388565 : Blo 2127435 5388565 := bbase (se 6 (by rfl) ⟨126294, by rfl⟩ : syracuseStep 5388565 = 252589) (by norm_num)
theorem B7184753 : Blo 2127435 7184753 := bstep (se 2 (by rfl) ⟨2694282, by rfl⟩ : syracuseStep 7184753 = 5388565) B5388565
theorem B4789835 : Blo 2127435 4789835 := bstep (se 1 (by rfl) ⟨3592376, by rfl⟩ : syracuseStep 4789835 = 7184753) B7184753
theorem B3193223 : Blo 2127435 3193223 := bstep (se 1 (by rfl) ⟨2394917, by rfl⟩ : syracuseStep 3193223 = 4789835) B4789835
theorem B2128815 : Blo 2127435 2128815 := bstep (se 1 (by rfl) ⟨1596611, by rfl⟩ : syracuseStep 2128815 = 3193223) B3193223
theorem B3193229 : Blo 2127435 3193229 := bbase (se 3 (by rfl) ⟨598730, by rfl⟩ : syracuseStep 3193229 = 1197461) (by norm_num)
theorem B2128819 : Blo 2127435 2128819 := bstep (se 1 (by rfl) ⟨1596614, by rfl⟩ : syracuseStep 2128819 = 3193229) B3193229
theorem B4789853 : Blo 2127435 4789853 := bbase (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) (by norm_num)
theorem B3193235 : Blo 2127435 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B2128823 : Blo 2127435 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B3592397 : Blo 2127435 3592397 := bbase (se 3 (by rfl) ⟨673574, by rfl⟩ : syracuseStep 3592397 = 1347149) (by norm_num)
theorem B2394931 : Blo 2127435 2394931 := bstep (se 1 (by rfl) ⟨1796198, by rfl⟩ : syracuseStep 2394931 = 3592397) B3592397
theorem B3193241 : Blo 2127435 3193241 := bstep (se 2 (by rfl) ⟨1197465, by rfl⟩ : syracuseStep 3193241 = 2394931) B2394931
theorem B2128827 : Blo 2127435 2128827 := bstep (se 1 (by rfl) ⟨1596620, by rfl⟩ : syracuseStep 2128827 = 3193241) B3193241
theorem B2157877 : Blo 2127435 2157877 := bbase (se 5 (by rfl) ⟨101150, by rfl⟩ : syracuseStep 2157877 = 202301) (by norm_num)
theorem B2877169 : Blo 2127435 2877169 := bstep (se 2 (by rfl) ⟨1078938, by rfl⟩ : syracuseStep 2877169 = 2157877) B2157877
theorem B3836225 : Blo 2127435 3836225 := bstep (se 2 (by rfl) ⟨1438584, by rfl⟩ : syracuseStep 3836225 = 2877169) B2877169
theorem B2557483 : Blo 2127435 2557483 := bstep (se 1 (by rfl) ⟨1918112, by rfl⟩ : syracuseStep 2557483 = 3836225) B3836225
theorem B13639909 : Blo 2127435 13639909 := bstep (se 4 (by rfl) ⟨1278741, by rfl⟩ : syracuseStep 13639909 = 2557483) B2557483
theorem B18186545 : Blo 2127435 18186545 := bstep (se 2 (by rfl) ⟨6819954, by rfl⟩ : syracuseStep 18186545 = 13639909) B13639909
theorem B12124363 : Blo 2127435 12124363 := bstep (se 1 (by rfl) ⟨9093272, by rfl⟩ : syracuseStep 12124363 = 18186545) B18186545
theorem B16165817 : Blo 2127435 16165817 := bstep (se 2 (by rfl) ⟨6062181, by rfl⟩ : syracuseStep 16165817 = 12124363) B12124363
theorem B10777211 : Blo 2127435 10777211 := bstep (se 1 (by rfl) ⟨8082908, by rfl⟩ : syracuseStep 10777211 = 16165817) B16165817
theorem B7184807 : Blo 2127435 7184807 := bstep (se 1 (by rfl) ⟨5388605, by rfl⟩ : syracuseStep 7184807 = 10777211) B10777211
theorem B4789871 : Blo 2127435 4789871 := bstep (se 1 (by rfl) ⟨3592403, by rfl⟩ : syracuseStep 4789871 = 7184807) B7184807
theorem B3193247 : Blo 2127435 3193247 := bstep (se 1 (by rfl) ⟨2394935, by rfl⟩ : syracuseStep 3193247 = 4789871) B4789871
theorem B2128831 : Blo 2127435 2128831 := bstep (se 1 (by rfl) ⟨1596623, by rfl⟩ : syracuseStep 2128831 = 3193247) B3193247
theorem B3193253 : Blo 2127435 3193253 := bbase (se 4 (by rfl) ⟨299367, by rfl⟩ : syracuseStep 3193253 = 598735) (by norm_num)
theorem B2128835 : Blo 2127435 2128835 := bstep (se 1 (by rfl) ⟨1596626, by rfl⟩ : syracuseStep 2128835 = 3193253) B3193253
theorem B2694313 : Blo 2127435 2694313 := bbase (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) (by norm_num)
theorem B3592417 : Blo 2127435 3592417 := bstep (se 2 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 3592417 = 2694313) B2694313
theorem B4789889 : Blo 2127435 4789889 := bstep (se 2 (by rfl) ⟨1796208, by rfl⟩ : syracuseStep 4789889 = 3592417) B3592417
theorem B3193259 : Blo 2127435 3193259 := bstep (se 1 (by rfl) ⟨2394944, by rfl⟩ : syracuseStep 3193259 = 4789889) B4789889
theorem B2128839 : Blo 2127435 2128839 := bstep (se 1 (by rfl) ⟨1596629, by rfl⟩ : syracuseStep 2128839 = 3193259) B3193259
theorem B2394949 : Blo 2127435 2394949 := bbase (se 4 (by rfl) ⟨224526, by rfl⟩ : syracuseStep 2394949 = 449053) (by norm_num)
theorem B3193265 : Blo 2127435 3193265 := bstep (se 2 (by rfl) ⟨1197474, by rfl⟩ : syracuseStep 3193265 = 2394949) B2394949
theorem B2128843 : Blo 2127435 2128843 := bstep (se 1 (by rfl) ⟨1596632, by rfl⟩ : syracuseStep 2128843 = 3193265) B3193265
theorem B4041485 : Blo 2127435 4041485 := bbase (se 3 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 4041485 = 1515557) (by norm_num)
theorem B2694323 : Blo 2127435 2694323 := bstep (se 1 (by rfl) ⟨2020742, by rfl⟩ : syracuseStep 2694323 = 4041485) B4041485
theorem B7184861 : Blo 2127435 7184861 := bstep (se 3 (by rfl) ⟨1347161, by rfl⟩ : syracuseStep 7184861 = 2694323) B2694323
theorem B4789907 : Blo 2127435 4789907 := bstep (se 1 (by rfl) ⟨3592430, by rfl⟩ : syracuseStep 4789907 = 7184861) B7184861
theorem B3193271 : Blo 2127435 3193271 := bstep (se 1 (by rfl) ⟨2394953, by rfl⟩ : syracuseStep 3193271 = 4789907) B4789907
theorem B2128847 : Blo 2127435 2128847 := bstep (se 1 (by rfl) ⟨1596635, by rfl⟩ : syracuseStep 2128847 = 3193271) B3193271
theorem B3193277 : Blo 2127435 3193277 := bbase (se 3 (by rfl) ⟨598739, by rfl⟩ : syracuseStep 3193277 = 1197479) (by norm_num)
theorem B2128851 : Blo 2127435 2128851 := bstep (se 1 (by rfl) ⟨1596638, by rfl⟩ : syracuseStep 2128851 = 3193277) B3193277
theorem B4789925 : Blo 2127435 4789925 := bbase (se 4 (by rfl) ⟨449055, by rfl⟩ : syracuseStep 4789925 = 898111) (by norm_num)
theorem B3193283 : Blo 2127435 3193283 := bstep (se 1 (by rfl) ⟨2394962, by rfl⟩ : syracuseStep 3193283 = 4789925) B4789925
theorem B2128855 : Blo 2127435 2128855 := bstep (se 1 (by rfl) ⟨1596641, by rfl⟩ : syracuseStep 2128855 = 3193283) B3193283
theorem B5388677 : Blo 2127435 5388677 := bbase (se 4 (by rfl) ⟨505188, by rfl⟩ : syracuseStep 5388677 = 1010377) (by norm_num)
theorem B3592451 : Blo 2127435 3592451 := bstep (se 1 (by rfl) ⟨2694338, by rfl⟩ : syracuseStep 3592451 = 5388677) B5388677
theorem B2394967 : Blo 2127435 2394967 := bstep (se 1 (by rfl) ⟨1796225, by rfl⟩ : syracuseStep 2394967 = 3592451) B3592451
theorem B3193289 : Blo 2127435 3193289 := bstep (se 2 (by rfl) ⟨1197483, by rfl⟩ : syracuseStep 3193289 = 2394967) B2394967
theorem B2128859 : Blo 2127435 2128859 := bstep (se 1 (by rfl) ⟨1596644, by rfl⟩ : syracuseStep 2128859 = 3193289) B3193289
theorem B3410029 : Blo 2127435 3410029 := bbase (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) (by norm_num)
theorem B4546705 : Blo 2127435 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B6062273 : Blo 2127435 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B4041515 : Blo 2127435 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B10777373 : Blo 2127435 10777373 := bstep (se 3 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 10777373 = 4041515) B4041515
theorem B7184915 : Blo 2127435 7184915 := bstep (se 1 (by rfl) ⟨5388686, by rfl⟩ : syracuseStep 7184915 = 10777373) B10777373
theorem B4789943 : Blo 2127435 4789943 := bstep (se 1 (by rfl) ⟨3592457, by rfl⟩ : syracuseStep 4789943 = 7184915) B7184915
theorem B3193295 : Blo 2127435 3193295 := bstep (se 1 (by rfl) ⟨2394971, by rfl⟩ : syracuseStep 3193295 = 4789943) B4789943
theorem B2128863 : Blo 2127435 2128863 := bstep (se 1 (by rfl) ⟨1596647, by rfl⟩ : syracuseStep 2128863 = 3193295) B3193295
theorem B3193301 : Blo 2127435 3193301 := bbase (se 7 (by rfl) ⟨37421, by rfl⟩ : syracuseStep 3193301 = 74843) (by norm_num)
theorem B2128867 : Blo 2127435 2128867 := bstep (se 1 (by rfl) ⟨1596650, by rfl⟩ : syracuseStep 2128867 = 3193301) B3193301
theorem B8083061 : Blo 2127435 8083061 := bbase (se 5 (by rfl) ⟨378893, by rfl⟩ : syracuseStep 8083061 = 757787) (by norm_num)
theorem B5388707 : Blo 2127435 5388707 := bstep (se 1 (by rfl) ⟨4041530, by rfl⟩ : syracuseStep 5388707 = 8083061) B8083061
theorem B3592471 : Blo 2127435 3592471 := bstep (se 1 (by rfl) ⟨2694353, by rfl⟩ : syracuseStep 3592471 = 5388707) B5388707
theorem B4789961 : Blo 2127435 4789961 := bstep (se 2 (by rfl) ⟨1796235, by rfl⟩ : syracuseStep 4789961 = 3592471) B3592471
theorem B3193307 : Blo 2127435 3193307 := bstep (se 1 (by rfl) ⟨2394980, by rfl⟩ : syracuseStep 3193307 = 4789961) B4789961
theorem B2128871 : Blo 2127435 2128871 := bstep (se 1 (by rfl) ⟨1596653, by rfl⟩ : syracuseStep 2128871 = 3193307) B3193307
theorem B2394985 : Blo 2127435 2394985 := bbase (se 2 (by rfl) ⟨898119, by rfl⟩ : syracuseStep 2394985 = 1796239) (by norm_num)
theorem B3193313 : Blo 2127435 3193313 := bstep (se 2 (by rfl) ⟨1197492, by rfl⟩ : syracuseStep 3193313 = 2394985) B2394985
theorem B2128875 : Blo 2127435 2128875 := bstep (se 1 (by rfl) ⟨1596656, by rfl⟩ : syracuseStep 2128875 = 3193313) B3193313
theorem B2557541 : Blo 2127435 2557541 := bbase (se 4 (by rfl) ⟨239769, by rfl⟩ : syracuseStep 2557541 = 479539) (by norm_num)
theorem B6820109 : Blo 2127435 6820109 := bstep (se 3 (by rfl) ⟨1278770, by rfl⟩ : syracuseStep 6820109 = 2557541) B2557541
theorem B4546739 : Blo 2127435 4546739 := bstep (se 1 (by rfl) ⟨3410054, by rfl⟩ : syracuseStep 4546739 = 6820109) B6820109
theorem B12124637 : Blo 2127435 12124637 := bstep (se 3 (by rfl) ⟨2273369, by rfl⟩ : syracuseStep 12124637 = 4546739) B4546739
theorem B8083091 : Blo 2127435 8083091 := bstep (se 1 (by rfl) ⟨6062318, by rfl⟩ : syracuseStep 8083091 = 12124637) B12124637
theorem B5388727 : Blo 2127435 5388727 := bstep (se 1 (by rfl) ⟨4041545, by rfl⟩ : syracuseStep 5388727 = 8083091) B8083091
theorem B7184969 : Blo 2127435 7184969 := bstep (se 2 (by rfl) ⟨2694363, by rfl⟩ : syracuseStep 7184969 = 5388727) B5388727
theorem B4789979 : Blo 2127435 4789979 := bstep (se 1 (by rfl) ⟨3592484, by rfl⟩ : syracuseStep 4789979 = 7184969) B7184969
theorem B3193319 : Blo 2127435 3193319 := bstep (se 1 (by rfl) ⟨2394989, by rfl⟩ : syracuseStep 3193319 = 4789979) B4789979
theorem B2128879 : Blo 2127435 2128879 := bstep (se 1 (by rfl) ⟨1596659, by rfl⟩ : syracuseStep 2128879 = 3193319) B3193319
theorem B3193325 : Blo 2127435 3193325 := bbase (se 3 (by rfl) ⟨598748, by rfl⟩ : syracuseStep 3193325 = 1197497) (by norm_num)
theorem B2128883 : Blo 2127435 2128883 := bstep (se 1 (by rfl) ⟨1596662, by rfl⟩ : syracuseStep 2128883 = 3193325) B3193325
theorem B4789997 : Blo 2127435 4789997 := bbase (se 3 (by rfl) ⟨898124, by rfl⟩ : syracuseStep 4789997 = 1796249) (by norm_num)
theorem B3193331 : Blo 2127435 3193331 := bstep (se 1 (by rfl) ⟨2394998, by rfl⟩ : syracuseStep 3193331 = 4789997) B4789997
theorem B2128887 : Blo 2127435 2128887 := bstep (se 1 (by rfl) ⟨1596665, by rfl⟩ : syracuseStep 2128887 = 3193331) B3193331
theorem B9710725 : Blo 2127435 9710725 := bbase (se 4 (by rfl) ⟨910380, by rfl⟩ : syracuseStep 9710725 = 1820761) (by norm_num)
theorem B12947633 : Blo 2127435 12947633 := bstep (se 2 (by rfl) ⟨4855362, by rfl⟩ : syracuseStep 12947633 = 9710725) B9710725
theorem B8631755 : Blo 2127435 8631755 := bstep (se 1 (by rfl) ⟨6473816, by rfl⟩ : syracuseStep 8631755 = 12947633) B12947633
theorem B5754503 : Blo 2127435 5754503 := bstep (se 1 (by rfl) ⟨4315877, by rfl⟩ : syracuseStep 5754503 = 8631755) B8631755
theorem B3836335 : Blo 2127435 3836335 := bstep (se 1 (by rfl) ⟨2877251, by rfl⟩ : syracuseStep 3836335 = 5754503) B5754503
theorem B5115113 : Blo 2127435 5115113 := bstep (se 2 (by rfl) ⟨1918167, by rfl⟩ : syracuseStep 5115113 = 3836335) B3836335
theorem B3410075 : Blo 2127435 3410075 := bstep (se 1 (by rfl) ⟨2557556, by rfl⟩ : syracuseStep 3410075 = 5115113) B5115113
theorem B2273383 : Blo 2127435 2273383 := bstep (se 1 (by rfl) ⟨1705037, by rfl⟩ : syracuseStep 2273383 = 3410075) B3410075
theorem B3031177 : Blo 2127435 3031177 := bstep (se 2 (by rfl) ⟨1136691, by rfl⟩ : syracuseStep 3031177 = 2273383) B2273383
theorem B4041569 : Blo 2127435 4041569 := bstep (se 2 (by rfl) ⟨1515588, by rfl⟩ : syracuseStep 4041569 = 3031177) B3031177
theorem B2694379 : Blo 2127435 2694379 := bstep (se 1 (by rfl) ⟨2020784, by rfl⟩ : syracuseStep 2694379 = 4041569) B4041569
theorem B3592505 : Blo 2127435 3592505 := bstep (se 2 (by rfl) ⟨1347189, by rfl⟩ : syracuseStep 3592505 = 2694379) B2694379
theorem B2395003 : Blo 2127435 2395003 := bstep (se 1 (by rfl) ⟨1796252, by rfl⟩ : syracuseStep 2395003 = 3592505) B3592505
theorem B3193337 : Blo 2127435 3193337 := bstep (se 2 (by rfl) ⟨1197501, by rfl⟩ : syracuseStep 3193337 = 2395003) B2395003
theorem B2128891 : Blo 2127435 2128891 := bstep (se 1 (by rfl) ⟨1596668, by rfl⟩ : syracuseStep 2128891 = 3193337) B3193337
theorem B3456605 : Blo 2127435 3456605 := bbase (se 3 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 3456605 = 1296227) (by norm_num)
theorem B9217613 : Blo 2127435 9217613 := bstep (se 3 (by rfl) ⟨1728302, by rfl⟩ : syracuseStep 9217613 = 3456605) B3456605
theorem B6145075 : Blo 2127435 6145075 := bstep (se 1 (by rfl) ⟨4608806, by rfl⟩ : syracuseStep 6145075 = 9217613) B9217613
theorem B32773733 : Blo 2127435 32773733 := bstep (se 4 (by rfl) ⟨3072537, by rfl⟩ : syracuseStep 32773733 = 6145075) B6145075
theorem B21849155 : Blo 2127435 21849155 := bstep (se 1 (by rfl) ⟨16386866, by rfl⟩ : syracuseStep 21849155 = 32773733) B32773733
theorem B14566103 : Blo 2127435 14566103 := bstep (se 1 (by rfl) ⟨10924577, by rfl⟩ : syracuseStep 14566103 = 21849155) B21849155
theorem B9710735 : Blo 2127435 9710735 := bstep (se 1 (by rfl) ⟨7283051, by rfl⟩ : syracuseStep 9710735 = 14566103) B14566103
theorem B103581173 : Blo 2127435 103581173 := bstep (se 5 (by rfl) ⟨4855367, by rfl⟩ : syracuseStep 103581173 = 9710735) B9710735
theorem B69054115 : Blo 2127435 69054115 := bstep (se 1 (by rfl) ⟨51790586, by rfl⟩ : syracuseStep 69054115 = 103581173) B103581173
theorem B92072153 : Blo 2127435 92072153 := bstep (se 2 (by rfl) ⟨34527057, by rfl⟩ : syracuseStep 92072153 = 69054115) B69054115
theorem B61381435 : Blo 2127435 61381435 := bstep (se 1 (by rfl) ⟨46036076, by rfl⟩ : syracuseStep 61381435 = 92072153) B92072153
theorem B81841913 : Blo 2127435 81841913 := bstep (se 2 (by rfl) ⟨30690717, by rfl⟩ : syracuseStep 81841913 = 61381435) B61381435
theorem B54561275 : Blo 2127435 54561275 := bstep (se 1 (by rfl) ⟨40920956, by rfl⟩ : syracuseStep 54561275 = 81841913) B81841913
theorem B36374183 : Blo 2127435 36374183 := bstep (se 1 (by rfl) ⟨27280637, by rfl⟩ : syracuseStep 36374183 = 54561275) B54561275
theorem B24249455 : Blo 2127435 24249455 := bstep (se 1 (by rfl) ⟨18187091, by rfl⟩ : syracuseStep 24249455 = 36374183) B36374183
theorem B16166303 : Blo 2127435 16166303 := bstep (se 1 (by rfl) ⟨12124727, by rfl⟩ : syracuseStep 16166303 = 24249455) B24249455
theorem B10777535 : Blo 2127435 10777535 := bstep (se 1 (by rfl) ⟨8083151, by rfl⟩ : syracuseStep 10777535 = 16166303) B16166303
theorem B7185023 : Blo 2127435 7185023 := bstep (se 1 (by rfl) ⟨5388767, by rfl⟩ : syracuseStep 7185023 = 10777535) B10777535
theorem B4790015 : Blo 2127435 4790015 := bstep (se 1 (by rfl) ⟨3592511, by rfl⟩ : syracuseStep 4790015 = 7185023) B7185023
theorem B3193343 : Blo 2127435 3193343 := bstep (se 1 (by rfl) ⟨2395007, by rfl⟩ : syracuseStep 3193343 = 4790015) B4790015
theorem B2128895 : Blo 2127435 2128895 := bstep (se 1 (by rfl) ⟨1596671, by rfl⟩ : syracuseStep 2128895 = 3193343) B3193343
theorem B3193349 : Blo 2127435 3193349 := bbase (se 4 (by rfl) ⟨299376, by rfl⟩ : syracuseStep 3193349 = 598753) (by norm_num)
theorem B2128899 : Blo 2127435 2128899 := bstep (se 1 (by rfl) ⟨1596674, by rfl⟩ : syracuseStep 2128899 = 3193349) B3193349
theorem B3592525 : Blo 2127435 3592525 := bbase (se 3 (by rfl) ⟨673598, by rfl⟩ : syracuseStep 3592525 = 1347197) (by norm_num)
theorem B4790033 : Blo 2127435 4790033 := bstep (se 2 (by rfl) ⟨1796262, by rfl⟩ : syracuseStep 4790033 = 3592525) B3592525
theorem B3193355 : Blo 2127435 3193355 := bstep (se 1 (by rfl) ⟨2395016, by rfl⟩ : syracuseStep 3193355 = 4790033) B4790033
theorem B2128903 : Blo 2127435 2128903 := bstep (se 1 (by rfl) ⟨1596677, by rfl⟩ : syracuseStep 2128903 = 3193355) B3193355
theorem B2395021 : Blo 2127435 2395021 := bbase (se 3 (by rfl) ⟨449066, by rfl⟩ : syracuseStep 2395021 = 898133) (by norm_num)
theorem B3193361 : Blo 2127435 3193361 := bstep (se 2 (by rfl) ⟨1197510, by rfl⟩ : syracuseStep 3193361 = 2395021) B2395021
theorem B2128907 : Blo 2127435 2128907 := bstep (se 1 (by rfl) ⟨1596680, by rfl⟩ : syracuseStep 2128907 = 3193361) B3193361
theorem B7185077 : Blo 2127435 7185077 := bbase (se 5 (by rfl) ⟨336800, by rfl⟩ : syracuseStep 7185077 = 673601) (by norm_num)
theorem B4790051 : Blo 2127435 4790051 := bstep (se 1 (by rfl) ⟨3592538, by rfl⟩ : syracuseStep 4790051 = 7185077) B7185077
theorem B3193367 : Blo 2127435 3193367 := bstep (se 1 (by rfl) ⟨2395025, by rfl⟩ : syracuseStep 3193367 = 4790051) B4790051
theorem B2128911 : Blo 2127435 2128911 := bstep (se 1 (by rfl) ⟨1596683, by rfl⟩ : syracuseStep 2128911 = 3193367) B3193367
theorem B3193373 : Blo 2127435 3193373 := bbase (se 3 (by rfl) ⟨598757, by rfl⟩ : syracuseStep 3193373 = 1197515) (by norm_num)
theorem B2128915 : Blo 2127435 2128915 := bstep (se 1 (by rfl) ⟨1596686, by rfl⟩ : syracuseStep 2128915 = 3193373) B3193373
theorem B4790069 : Blo 2127435 4790069 := bbase (se 5 (by rfl) ⟨224534, by rfl⟩ : syracuseStep 4790069 = 449069) (by norm_num)
theorem B3193379 : Blo 2127435 3193379 := bstep (se 1 (by rfl) ⟨2395034, by rfl⟩ : syracuseStep 3193379 = 4790069) B4790069
theorem B2128919 : Blo 2127435 2128919 := bstep (se 1 (by rfl) ⟨1596689, by rfl⟩ : syracuseStep 2128919 = 3193379) B3193379
theorem B13640501 : Blo 2127435 13640501 := bbase (se 5 (by rfl) ⟨639398, by rfl⟩ : syracuseStep 13640501 = 1278797) (by norm_num)
theorem B9093667 : Blo 2127435 9093667 := bstep (se 1 (by rfl) ⟨6820250, by rfl⟩ : syracuseStep 9093667 = 13640501) B13640501
theorem B12124889 : Blo 2127435 12124889 := bstep (se 2 (by rfl) ⟨4546833, by rfl⟩ : syracuseStep 12124889 = 9093667) B9093667
theorem B8083259 : Blo 2127435 8083259 := bstep (se 1 (by rfl) ⟨6062444, by rfl⟩ : syracuseStep 8083259 = 12124889) B12124889
theorem B5388839 : Blo 2127435 5388839 := bstep (se 1 (by rfl) ⟨4041629, by rfl⟩ : syracuseStep 5388839 = 8083259) B8083259
theorem B3592559 : Blo 2127435 3592559 := bstep (se 1 (by rfl) ⟨2694419, by rfl⟩ : syracuseStep 3592559 = 5388839) B5388839
theorem B2395039 : Blo 2127435 2395039 := bstep (se 1 (by rfl) ⟨1796279, by rfl⟩ : syracuseStep 2395039 = 3592559) B3592559
theorem B3193385 : Blo 2127435 3193385 := bstep (se 2 (by rfl) ⟨1197519, by rfl⟩ : syracuseStep 3193385 = 2395039) B2395039
theorem B2128923 : Blo 2127435 2128923 := bstep (se 1 (by rfl) ⟨1596692, by rfl⟩ : syracuseStep 2128923 = 3193385) B3193385
theorem B5115197 : Blo 2127435 5115197 := bbase (se 3 (by rfl) ⟨959099, by rfl⟩ : syracuseStep 5115197 = 1918199) (by norm_num)
theorem B13640525 : Blo 2127435 13640525 := bstep (se 3 (by rfl) ⟨2557598, by rfl⟩ : syracuseStep 13640525 = 5115197) B5115197
theorem B9093683 : Blo 2127435 9093683 := bstep (se 1 (by rfl) ⟨6820262, by rfl⟩ : syracuseStep 9093683 = 13640525) B13640525
theorem B6062455 : Blo 2127435 6062455 := bstep (se 1 (by rfl) ⟨4546841, by rfl⟩ : syracuseStep 6062455 = 9093683) B9093683
theorem B8083273 : Blo 2127435 8083273 := bstep (se 2 (by rfl) ⟨3031227, by rfl⟩ : syracuseStep 8083273 = 6062455) B6062455
theorem B10777697 : Blo 2127435 10777697 := bstep (se 2 (by rfl) ⟨4041636, by rfl⟩ : syracuseStep 10777697 = 8083273) B8083273
theorem B7185131 : Blo 2127435 7185131 := bstep (se 1 (by rfl) ⟨5388848, by rfl⟩ : syracuseStep 7185131 = 10777697) B10777697
theorem B4790087 : Blo 2127435 4790087 := bstep (se 1 (by rfl) ⟨3592565, by rfl⟩ : syracuseStep 4790087 = 7185131) B7185131
theorem B3193391 : Blo 2127435 3193391 := bstep (se 1 (by rfl) ⟨2395043, by rfl⟩ : syracuseStep 3193391 = 4790087) B4790087
theorem B2128927 : Blo 2127435 2128927 := bstep (se 1 (by rfl) ⟨1596695, by rfl⟩ : syracuseStep 2128927 = 3193391) B3193391
theorem B3193397 : Blo 2127435 3193397 := bbase (se 5 (by rfl) ⟨149690, by rfl⟩ : syracuseStep 3193397 = 299381) (by norm_num)
theorem B2128931 : Blo 2127435 2128931 := bstep (se 1 (by rfl) ⟨1596698, by rfl⟩ : syracuseStep 2128931 = 3193397) B3193397
theorem B5388869 : Blo 2127435 5388869 := bbase (se 4 (by rfl) ⟨505206, by rfl⟩ : syracuseStep 5388869 = 1010413) (by norm_num)
theorem B3592579 : Blo 2127435 3592579 := bstep (se 1 (by rfl) ⟨2694434, by rfl⟩ : syracuseStep 3592579 = 5388869) B5388869
theorem B4790105 : Blo 2127435 4790105 := bstep (se 2 (by rfl) ⟨1796289, by rfl⟩ : syracuseStep 4790105 = 3592579) B3592579
theorem B3193403 : Blo 2127435 3193403 := bstep (se 1 (by rfl) ⟨2395052, by rfl⟩ : syracuseStep 3193403 = 4790105) B4790105
theorem B2128935 : Blo 2127435 2128935 := bstep (se 1 (by rfl) ⟨1596701, by rfl⟩ : syracuseStep 2128935 = 3193403) B3193403
theorem B2395057 : Blo 2127435 2395057 := bbase (se 2 (by rfl) ⟨898146, by rfl⟩ : syracuseStep 2395057 = 1796293) (by norm_num)
theorem B3193409 : Blo 2127435 3193409 := bstep (se 2 (by rfl) ⟨1197528, by rfl⟩ : syracuseStep 3193409 = 2395057) B2395057
theorem B2128939 : Blo 2127435 2128939 := bstep (se 1 (by rfl) ⟨1596704, by rfl⟩ : syracuseStep 2128939 = 3193409) B3193409
theorem B6062501 : Blo 2127435 6062501 := bbase (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) (by norm_num)
theorem B4041667 : Blo 2127435 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B5388889 : Blo 2127435 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B7185185 : Blo 2127435 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B4790123 : Blo 2127435 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B3193415 : Blo 2127435 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B2128943 : Blo 2127435 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B3193421 : Blo 2127435 3193421 := bbase (se 3 (by rfl) ⟨598766, by rfl⟩ : syracuseStep 3193421 = 1197533) (by norm_num)
theorem B2128947 : Blo 2127435 2128947 := bstep (se 1 (by rfl) ⟨1596710, by rfl⟩ : syracuseStep 2128947 = 3193421) B3193421
theorem B4790141 : Blo 2127435 4790141 := bbase (se 3 (by rfl) ⟨898151, by rfl⟩ : syracuseStep 4790141 = 1796303) (by norm_num)
theorem B3193427 : Blo 2127435 3193427 := bstep (se 1 (by rfl) ⟨2395070, by rfl⟩ : syracuseStep 3193427 = 4790141) B4790141
theorem B2128951 : Blo 2127435 2128951 := bstep (se 1 (by rfl) ⟨1596713, by rfl⟩ : syracuseStep 2128951 = 3193427) B3193427
theorem B3592613 : Blo 2127435 3592613 := bbase (se 4 (by rfl) ⟨336807, by rfl⟩ : syracuseStep 3592613 = 673615) (by norm_num)
theorem B2395075 : Blo 2127435 2395075 := bstep (se 1 (by rfl) ⟨1796306, by rfl⟩ : syracuseStep 2395075 = 3592613) B3592613
theorem B3193433 : Blo 2127435 3193433 := bstep (se 2 (by rfl) ⟨1197537, by rfl⟩ : syracuseStep 3193433 = 2395075) B2395075
theorem B2128955 : Blo 2127435 2128955 := bstep (se 1 (by rfl) ⟨1596716, by rfl⟩ : syracuseStep 2128955 = 3193433) B3193433
theorem B4855517 : Blo 2127435 4855517 := bbase (se 3 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 4855517 = 1820819) (by norm_num)
theorem B3237011 : Blo 2127435 3237011 := bstep (se 1 (by rfl) ⟨2427758, by rfl⟩ : syracuseStep 3237011 = 4855517) B4855517
theorem B2158007 : Blo 2127435 2158007 := bstep (se 1 (by rfl) ⟨1618505, by rfl⟩ : syracuseStep 2158007 = 3237011) B3237011
theorem B5754685 : Blo 2127435 5754685 := bstep (se 3 (by rfl) ⟨1079003, by rfl⟩ : syracuseStep 5754685 = 2158007) B2158007
theorem B7672913 : Blo 2127435 7672913 := bstep (se 2 (by rfl) ⟨2877342, by rfl⟩ : syracuseStep 7672913 = 5754685) B5754685
theorem B5115275 : Blo 2127435 5115275 := bstep (se 1 (by rfl) ⟨3836456, by rfl⟩ : syracuseStep 5115275 = 7672913) B7672913
theorem B3410183 : Blo 2127435 3410183 := bstep (se 1 (by rfl) ⟨2557637, by rfl⟩ : syracuseStep 3410183 = 5115275) B5115275
theorem B2273455 : Blo 2127435 2273455 := bstep (se 1 (by rfl) ⟨1705091, by rfl⟩ : syracuseStep 2273455 = 3410183) B3410183
theorem B3031273 : Blo 2127435 3031273 := bstep (se 2 (by rfl) ⟨1136727, by rfl⟩ : syracuseStep 3031273 = 2273455) B2273455
theorem B16166789 : Blo 2127435 16166789 := bstep (se 4 (by rfl) ⟨1515636, by rfl⟩ : syracuseStep 16166789 = 3031273) B3031273
theorem B10777859 : Blo 2127435 10777859 := bstep (se 1 (by rfl) ⟨8083394, by rfl⟩ : syracuseStep 10777859 = 16166789) B16166789
theorem B7185239 : Blo 2127435 7185239 := bstep (se 1 (by rfl) ⟨5388929, by rfl⟩ : syracuseStep 7185239 = 10777859) B10777859
theorem B4790159 : Blo 2127435 4790159 := bstep (se 1 (by rfl) ⟨3592619, by rfl⟩ : syracuseStep 4790159 = 7185239) B7185239
theorem B3193439 : Blo 2127435 3193439 := bstep (se 1 (by rfl) ⟨2395079, by rfl⟩ : syracuseStep 3193439 = 4790159) B4790159
theorem B2128959 : Blo 2127435 2128959 := bstep (se 1 (by rfl) ⟨1596719, by rfl⟩ : syracuseStep 2128959 = 3193439) B3193439
theorem B3193445 : Blo 2127435 3193445 := bbase (se 4 (by rfl) ⟨299385, by rfl⟩ : syracuseStep 3193445 = 598771) (by norm_num)
theorem B2128963 : Blo 2127435 2128963 := bstep (se 1 (by rfl) ⟨1596722, by rfl⟩ : syracuseStep 2128963 = 3193445) B3193445
theorem B3031285 : Blo 2127435 3031285 := bbase (se 5 (by rfl) ⟨142091, by rfl⟩ : syracuseStep 3031285 = 284183) (by norm_num)
theorem B4041713 : Blo 2127435 4041713 := bstep (se 2 (by rfl) ⟨1515642, by rfl⟩ : syracuseStep 4041713 = 3031285) B3031285
theorem B2694475 : Blo 2127435 2694475 := bstep (se 1 (by rfl) ⟨2020856, by rfl⟩ : syracuseStep 2694475 = 4041713) B4041713
theorem B3592633 : Blo 2127435 3592633 := bstep (se 2 (by rfl) ⟨1347237, by rfl⟩ : syracuseStep 3592633 = 2694475) B2694475
theorem B4790177 : Blo 2127435 4790177 := bstep (se 2 (by rfl) ⟨1796316, by rfl⟩ : syracuseStep 4790177 = 3592633) B3592633
theorem B3193451 : Blo 2127435 3193451 := bstep (se 1 (by rfl) ⟨2395088, by rfl⟩ : syracuseStep 3193451 = 4790177) B4790177
theorem B2128967 : Blo 2127435 2128967 := bstep (se 1 (by rfl) ⟨1596725, by rfl⟩ : syracuseStep 2128967 = 3193451) B3193451
theorem B2395093 : Blo 2127435 2395093 := bbase (se 7 (by rfl) ⟨28067, by rfl⟩ : syracuseStep 2395093 = 56135) (by norm_num)
theorem B3193457 : Blo 2127435 3193457 := bstep (se 2 (by rfl) ⟨1197546, by rfl⟩ : syracuseStep 3193457 = 2395093) B2395093
theorem B2128971 : Blo 2127435 2128971 := bstep (se 1 (by rfl) ⟨1596728, by rfl⟩ : syracuseStep 2128971 = 3193457) B3193457
theorem B2694485 : Blo 2127435 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B7185293 : Blo 2127435 7185293 := bstep (se 3 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 7185293 = 2694485) B2694485
theorem B4790195 : Blo 2127435 4790195 := bstep (se 1 (by rfl) ⟨3592646, by rfl⟩ : syracuseStep 4790195 = 7185293) B7185293
theorem B3193463 : Blo 2127435 3193463 := bstep (se 1 (by rfl) ⟨2395097, by rfl⟩ : syracuseStep 3193463 = 4790195) B4790195
theorem B2128975 : Blo 2127435 2128975 := bstep (se 1 (by rfl) ⟨1596731, by rfl⟩ : syracuseStep 2128975 = 3193463) B3193463
theorem B3193469 : Blo 2127435 3193469 := bbase (se 3 (by rfl) ⟨598775, by rfl⟩ : syracuseStep 3193469 = 1197551) (by norm_num)
theorem B2128979 : Blo 2127435 2128979 := bstep (se 1 (by rfl) ⟨1596734, by rfl⟩ : syracuseStep 2128979 = 3193469) B3193469
theorem B4790213 : Blo 2127435 4790213 := bbase (se 4 (by rfl) ⟨449082, by rfl⟩ : syracuseStep 4790213 = 898165) (by norm_num)
theorem B3193475 : Blo 2127435 3193475 := bstep (se 1 (by rfl) ⟨2395106, by rfl⟩ : syracuseStep 3193475 = 4790213) B4790213
theorem B2128983 : Blo 2127435 2128983 := bstep (se 1 (by rfl) ⟨1596737, by rfl⟩ : syracuseStep 2128983 = 3193475) B3193475
theorem B9093941 : Blo 2127435 9093941 := bbase (se 5 (by rfl) ⟨426278, by rfl⟩ : syracuseStep 9093941 = 852557) (by norm_num)
theorem B6062627 : Blo 2127435 6062627 := bstep (se 1 (by rfl) ⟨4546970, by rfl⟩ : syracuseStep 6062627 = 9093941) B9093941
theorem B4041751 : Blo 2127435 4041751 := bstep (se 1 (by rfl) ⟨3031313, by rfl⟩ : syracuseStep 4041751 = 6062627) B6062627
theorem B5389001 : Blo 2127435 5389001 := bstep (se 2 (by rfl) ⟨2020875, by rfl⟩ : syracuseStep 5389001 = 4041751) B4041751
theorem B3592667 : Blo 2127435 3592667 := bstep (se 1 (by rfl) ⟨2694500, by rfl⟩ : syracuseStep 3592667 = 5389001) B5389001
theorem B2395111 : Blo 2127435 2395111 := bstep (se 1 (by rfl) ⟨1796333, by rfl⟩ : syracuseStep 2395111 = 3592667) B3592667
theorem B3193481 : Blo 2127435 3193481 := bstep (se 2 (by rfl) ⟨1197555, by rfl⟩ : syracuseStep 3193481 = 2395111) B2395111
theorem B2128987 : Blo 2127435 2128987 := bstep (se 1 (by rfl) ⟨1596740, by rfl⟩ : syracuseStep 2128987 = 3193481) B3193481
theorem B10778021 : Blo 2127435 10778021 := bbase (se 4 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 10778021 = 2020879) (by norm_num)
theorem B7185347 : Blo 2127435 7185347 := bstep (se 1 (by rfl) ⟨5389010, by rfl⟩ : syracuseStep 7185347 = 10778021) B10778021
theorem B4790231 : Blo 2127435 4790231 := bstep (se 1 (by rfl) ⟨3592673, by rfl⟩ : syracuseStep 4790231 = 7185347) B7185347
theorem B3193487 : Blo 2127435 3193487 := bstep (se 1 (by rfl) ⟨2395115, by rfl⟩ : syracuseStep 3193487 = 4790231) B4790231
theorem B2128991 : Blo 2127435 2128991 := bstep (se 1 (by rfl) ⟨1596743, by rfl⟩ : syracuseStep 2128991 = 3193487) B3193487
theorem B3193493 : Blo 2127435 3193493 := bbase (se 6 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 3193493 = 149695) (by norm_num)
theorem B2128995 : Blo 2127435 2128995 := bstep (se 1 (by rfl) ⟨1596746, by rfl⟩ : syracuseStep 2128995 = 3193493) B3193493
theorem B59062229 : Blo 2127435 59062229 := bbase (se 7 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 59062229 = 1384271) (by norm_num)
theorem B39374819 : Blo 2127435 39374819 := bstep (se 1 (by rfl) ⟨29531114, by rfl⟩ : syracuseStep 39374819 = 59062229) B59062229
theorem B26249879 : Blo 2127435 26249879 := bstep (se 1 (by rfl) ⟨19687409, by rfl⟩ : syracuseStep 26249879 = 39374819) B39374819
theorem B17499919 : Blo 2127435 17499919 := bstep (se 1 (by rfl) ⟨13124939, by rfl⟩ : syracuseStep 17499919 = 26249879) B26249879
theorem B23333225 : Blo 2127435 23333225 := bstep (se 2 (by rfl) ⟨8749959, by rfl⟩ : syracuseStep 23333225 = 17499919) B17499919
theorem B62221933 : Blo 2127435 62221933 := bstep (se 3 (by rfl) ⟨11666612, by rfl⟩ : syracuseStep 62221933 = 23333225) B23333225
theorem B82962577 : Blo 2127435 82962577 := bstep (se 2 (by rfl) ⟨31110966, by rfl⟩ : syracuseStep 82962577 = 62221933) B62221933
theorem B110616769 : Blo 2127435 110616769 := bstep (se 2 (by rfl) ⟨41481288, by rfl⟩ : syracuseStep 110616769 = 82962577) B82962577
theorem B147489025 : Blo 2127435 147489025 := bstep (se 2 (by rfl) ⟨55308384, by rfl⟩ : syracuseStep 147489025 = 110616769) B110616769
theorem B196652033 : Blo 2127435 196652033 := bstep (se 2 (by rfl) ⟨73744512, by rfl⟩ : syracuseStep 196652033 = 147489025) B147489025
theorem B131101355 : Blo 2127435 131101355 := bstep (se 1 (by rfl) ⟨98326016, by rfl⟩ : syracuseStep 131101355 = 196652033) B196652033
theorem B87400903 : Blo 2127435 87400903 := bstep (se 1 (by rfl) ⟨65550677, by rfl⟩ : syracuseStep 87400903 = 131101355) B131101355
theorem B116534537 : Blo 2127435 116534537 := bstep (se 2 (by rfl) ⟨43700451, by rfl⟩ : syracuseStep 116534537 = 87400903) B87400903
theorem B77689691 : Blo 2127435 77689691 := bstep (se 1 (by rfl) ⟨58267268, by rfl⟩ : syracuseStep 77689691 = 116534537) B116534537
theorem B51793127 : Blo 2127435 51793127 := bstep (se 1 (by rfl) ⟨38844845, by rfl⟩ : syracuseStep 51793127 = 77689691) B77689691
theorem B34528751 : Blo 2127435 34528751 := bstep (se 1 (by rfl) ⟨25896563, by rfl⟩ : syracuseStep 34528751 = 51793127) B51793127
theorem B23019167 : Blo 2127435 23019167 := bstep (se 1 (by rfl) ⟨17264375, by rfl⟩ : syracuseStep 23019167 = 34528751) B34528751
theorem B15346111 : Blo 2127435 15346111 := bstep (se 1 (by rfl) ⟨11509583, by rfl⟩ : syracuseStep 15346111 = 23019167) B23019167
theorem B20461481 : Blo 2127435 20461481 := bstep (se 2 (by rfl) ⟨7673055, by rfl⟩ : syracuseStep 20461481 = 15346111) B15346111
theorem B13640987 : Blo 2127435 13640987 := bstep (se 1 (by rfl) ⟨10230740, by rfl⟩ : syracuseStep 13640987 = 20461481) B20461481
theorem B9093991 : Blo 2127435 9093991 := bstep (se 1 (by rfl) ⟨6820493, by rfl⟩ : syracuseStep 9093991 = 13640987) B13640987
theorem B12125321 : Blo 2127435 12125321 := bstep (se 2 (by rfl) ⟨4546995, by rfl⟩ : syracuseStep 12125321 = 9093991) B9093991
theorem B8083547 : Blo 2127435 8083547 := bstep (se 1 (by rfl) ⟨6062660, by rfl⟩ : syracuseStep 8083547 = 12125321) B12125321
theorem B5389031 : Blo 2127435 5389031 := bstep (se 1 (by rfl) ⟨4041773, by rfl⟩ : syracuseStep 5389031 = 8083547) B8083547
theorem B3592687 : Blo 2127435 3592687 := bstep (se 1 (by rfl) ⟨2694515, by rfl⟩ : syracuseStep 3592687 = 5389031) B5389031
theorem B4790249 : Blo 2127435 4790249 := bstep (se 2 (by rfl) ⟨1796343, by rfl⟩ : syracuseStep 4790249 = 3592687) B3592687
theorem B3193499 : Blo 2127435 3193499 := bstep (se 1 (by rfl) ⟨2395124, by rfl⟩ : syracuseStep 3193499 = 4790249) B4790249
theorem B2128999 : Blo 2127435 2128999 := bstep (se 1 (by rfl) ⟨1596749, by rfl⟩ : syracuseStep 2128999 = 3193499) B3193499
theorem B2395129 : Blo 2127435 2395129 := bbase (se 2 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 2395129 = 1796347) (by norm_num)
theorem B3193505 : Blo 2127435 3193505 := bstep (se 2 (by rfl) ⟨1197564, by rfl⟩ : syracuseStep 3193505 = 2395129) B2395129
theorem B2129003 : Blo 2127435 2129003 := bstep (se 1 (by rfl) ⟨1596752, by rfl⟩ : syracuseStep 2129003 = 3193505) B3193505
theorem B16387733 : Blo 2127435 16387733 := bbase (se 6 (by rfl) ⟨384087, by rfl⟩ : syracuseStep 16387733 = 768175) (by norm_num)
theorem B10925155 : Blo 2127435 10925155 := bstep (se 1 (by rfl) ⟨8193866, by rfl⟩ : syracuseStep 10925155 = 16387733) B16387733
theorem B14566873 : Blo 2127435 14566873 := bstep (se 2 (by rfl) ⟨5462577, by rfl⟩ : syracuseStep 14566873 = 10925155) B10925155
theorem B19422497 : Blo 2127435 19422497 := bstep (se 2 (by rfl) ⟨7283436, by rfl⟩ : syracuseStep 19422497 = 14566873) B14566873
theorem B12948331 : Blo 2127435 12948331 := bstep (se 1 (by rfl) ⟨9711248, by rfl⟩ : syracuseStep 12948331 = 19422497) B19422497
theorem B17264441 : Blo 2127435 17264441 := bstep (se 2 (by rfl) ⟨6474165, by rfl⟩ : syracuseStep 17264441 = 12948331) B12948331
theorem B11509627 : Blo 2127435 11509627 := bstep (se 1 (by rfl) ⟨8632220, by rfl⟩ : syracuseStep 11509627 = 17264441) B17264441
theorem B15346169 : Blo 2127435 15346169 := bstep (se 2 (by rfl) ⟨5754813, by rfl⟩ : syracuseStep 15346169 = 11509627) B11509627
theorem B10230779 : Blo 2127435 10230779 := bstep (se 1 (by rfl) ⟨7673084, by rfl⟩ : syracuseStep 10230779 = 15346169) B15346169
theorem B6820519 : Blo 2127435 6820519 := bstep (se 1 (by rfl) ⟨5115389, by rfl⟩ : syracuseStep 6820519 = 10230779) B10230779
theorem B9094025 : Blo 2127435 9094025 := bstep (se 2 (by rfl) ⟨3410259, by rfl⟩ : syracuseStep 9094025 = 6820519) B6820519
theorem B6062683 : Blo 2127435 6062683 := bstep (se 1 (by rfl) ⟨4547012, by rfl⟩ : syracuseStep 6062683 = 9094025) B9094025
theorem B8083577 : Blo 2127435 8083577 := bstep (se 2 (by rfl) ⟨3031341, by rfl⟩ : syracuseStep 8083577 = 6062683) B6062683
theorem B5389051 : Blo 2127435 5389051 := bstep (se 1 (by rfl) ⟨4041788, by rfl⟩ : syracuseStep 5389051 = 8083577) B8083577
theorem B7185401 : Blo 2127435 7185401 := bstep (se 2 (by rfl) ⟨2694525, by rfl⟩ : syracuseStep 7185401 = 5389051) B5389051
theorem B4790267 : Blo 2127435 4790267 := bstep (se 1 (by rfl) ⟨3592700, by rfl⟩ : syracuseStep 4790267 = 7185401) B7185401
theorem B3193511 : Blo 2127435 3193511 := bstep (se 1 (by rfl) ⟨2395133, by rfl⟩ : syracuseStep 3193511 = 4790267) B4790267
theorem B2129007 : Blo 2127435 2129007 := bstep (se 1 (by rfl) ⟨1596755, by rfl⟩ : syracuseStep 2129007 = 3193511) B3193511
theorem B3193517 : Blo 2127435 3193517 := bbase (se 3 (by rfl) ⟨598784, by rfl⟩ : syracuseStep 3193517 = 1197569) (by norm_num)
theorem B2129011 : Blo 2127435 2129011 := bstep (se 1 (by rfl) ⟨1596758, by rfl⟩ : syracuseStep 2129011 = 3193517) B3193517
theorem B4790285 : Blo 2127435 4790285 := bbase (se 3 (by rfl) ⟨898178, by rfl⟩ : syracuseStep 4790285 = 1796357) (by norm_num)
theorem B3193523 : Blo 2127435 3193523 := bstep (se 1 (by rfl) ⟨2395142, by rfl⟩ : syracuseStep 3193523 = 4790285) B4790285
theorem B2129015 : Blo 2127435 2129015 := bstep (se 1 (by rfl) ⟨1596761, by rfl⟩ : syracuseStep 2129015 = 3193523) B3193523
theorem B2694541 : Blo 2127435 2694541 := bbase (se 3 (by rfl) ⟨505226, by rfl⟩ : syracuseStep 2694541 = 1010453) (by norm_num)
theorem B3592721 : Blo 2127435 3592721 := bstep (se 2 (by rfl) ⟨1347270, by rfl⟩ : syracuseStep 3592721 = 2694541) B2694541
theorem B2395147 : Blo 2127435 2395147 := bstep (se 1 (by rfl) ⟨1796360, by rfl⟩ : syracuseStep 2395147 = 3592721) B3592721
theorem B3193529 : Blo 2127435 3193529 := bstep (se 2 (by rfl) ⟨1197573, by rfl⟩ : syracuseStep 3193529 = 2395147) B2395147
theorem B2129019 : Blo 2127435 2129019 := bstep (se 1 (by rfl) ⟨1596764, by rfl⟩ : syracuseStep 2129019 = 3193529) B3193529
theorem B7673141 : Blo 2127435 7673141 := bbase (se 5 (by rfl) ⟨359678, by rfl⟩ : syracuseStep 7673141 = 719357) (by norm_num)
theorem B20461709 : Blo 2127435 20461709 := bstep (se 3 (by rfl) ⟨3836570, by rfl⟩ : syracuseStep 20461709 = 7673141) B7673141
theorem B13641139 : Blo 2127435 13641139 := bstep (se 1 (by rfl) ⟨10230854, by rfl⟩ : syracuseStep 13641139 = 20461709) B20461709
theorem B18188185 : Blo 2127435 18188185 := bstep (se 2 (by rfl) ⟨6820569, by rfl⟩ : syracuseStep 18188185 = 13641139) B13641139
theorem B24250913 : Blo 2127435 24250913 := bstep (se 2 (by rfl) ⟨9094092, by rfl⟩ : syracuseStep 24250913 = 18188185) B18188185
theorem B16167275 : Blo 2127435 16167275 := bstep (se 1 (by rfl) ⟨12125456, by rfl⟩ : syracuseStep 16167275 = 24250913) B24250913
theorem B10778183 : Blo 2127435 10778183 := bstep (se 1 (by rfl) ⟨8083637, by rfl⟩ : syracuseStep 10778183 = 16167275) B16167275
theorem B7185455 : Blo 2127435 7185455 := bstep (se 1 (by rfl) ⟨5389091, by rfl⟩ : syracuseStep 7185455 = 10778183) B10778183
theorem B4790303 : Blo 2127435 4790303 := bstep (se 1 (by rfl) ⟨3592727, by rfl⟩ : syracuseStep 4790303 = 7185455) B7185455
theorem B3193535 : Blo 2127435 3193535 := bstep (se 1 (by rfl) ⟨2395151, by rfl⟩ : syracuseStep 3193535 = 4790303) B4790303
theorem B2129023 : Blo 2127435 2129023 := bstep (se 1 (by rfl) ⟨1596767, by rfl⟩ : syracuseStep 2129023 = 3193535) B3193535
theorem B3193541 : Blo 2127435 3193541 := bbase (se 4 (by rfl) ⟨299394, by rfl⟩ : syracuseStep 3193541 = 598789) (by norm_num)
theorem B2129027 : Blo 2127435 2129027 := bstep (se 1 (by rfl) ⟨1596770, by rfl⟩ : syracuseStep 2129027 = 3193541) B3193541
theorem B3592741 : Blo 2127435 3592741 := bbase (se 4 (by rfl) ⟨336819, by rfl⟩ : syracuseStep 3592741 = 673639) (by norm_num)
theorem B4790321 : Blo 2127435 4790321 := bstep (se 2 (by rfl) ⟨1796370, by rfl⟩ : syracuseStep 4790321 = 3592741) B3592741
theorem B3193547 : Blo 2127435 3193547 := bstep (se 1 (by rfl) ⟨2395160, by rfl⟩ : syracuseStep 3193547 = 4790321) B4790321
theorem B2129031 : Blo 2127435 2129031 := bstep (se 1 (by rfl) ⟨1596773, by rfl⟩ : syracuseStep 2129031 = 3193547) B3193547
theorem B2395165 : Blo 2127435 2395165 := bbase (se 3 (by rfl) ⟨449093, by rfl⟩ : syracuseStep 2395165 = 898187) (by norm_num)
theorem B3193553 : Blo 2127435 3193553 := bstep (se 2 (by rfl) ⟨1197582, by rfl⟩ : syracuseStep 3193553 = 2395165) B2395165
theorem B2129035 : Blo 2127435 2129035 := bstep (se 1 (by rfl) ⟨1596776, by rfl⟩ : syracuseStep 2129035 = 3193553) B3193553
theorem B7185509 : Blo 2127435 7185509 := bbase (se 4 (by rfl) ⟨673641, by rfl⟩ : syracuseStep 7185509 = 1347283) (by norm_num)
theorem B4790339 : Blo 2127435 4790339 := bstep (se 1 (by rfl) ⟨3592754, by rfl⟩ : syracuseStep 4790339 = 7185509) B7185509
theorem B3193559 : Blo 2127435 3193559 := bstep (se 1 (by rfl) ⟨2395169, by rfl⟩ : syracuseStep 3193559 = 4790339) B4790339
theorem B2129039 : Blo 2127435 2129039 := bstep (se 1 (by rfl) ⟨1596779, by rfl⟩ : syracuseStep 2129039 = 3193559) B3193559
theorem B3193565 : Blo 2127435 3193565 := bbase (se 3 (by rfl) ⟨598793, by rfl⟩ : syracuseStep 3193565 = 1197587) (by norm_num)
theorem B2129043 : Blo 2127435 2129043 := bstep (se 1 (by rfl) ⟨1596782, by rfl⟩ : syracuseStep 2129043 = 3193565) B3193565
theorem B4790357 : Blo 2127435 4790357 := bbase (se 8 (by rfl) ⟨28068, by rfl⟩ : syracuseStep 4790357 = 56137) (by norm_num)
theorem B3193571 : Blo 2127435 3193571 := bstep (se 1 (by rfl) ⟨2395178, by rfl⟩ : syracuseStep 3193571 = 4790357) B4790357
theorem B2129047 : Blo 2127435 2129047 := bstep (se 1 (by rfl) ⟨1596785, by rfl⟩ : syracuseStep 2129047 = 3193571) B3193571
theorem B6820661 : Blo 2127435 6820661 := bbase (se 5 (by rfl) ⟨319718, by rfl⟩ : syracuseStep 6820661 = 639437) (by norm_num)
theorem B4547107 : Blo 2127435 4547107 := bstep (se 1 (by rfl) ⟨3410330, by rfl⟩ : syracuseStep 4547107 = 6820661) B6820661
theorem B6062809 : Blo 2127435 6062809 := bstep (se 2 (by rfl) ⟨2273553, by rfl⟩ : syracuseStep 6062809 = 4547107) B4547107
theorem B8083745 : Blo 2127435 8083745 := bstep (se 2 (by rfl) ⟨3031404, by rfl⟩ : syracuseStep 8083745 = 6062809) B6062809
theorem B5389163 : Blo 2127435 5389163 := bstep (se 1 (by rfl) ⟨4041872, by rfl⟩ : syracuseStep 5389163 = 8083745) B8083745
theorem B3592775 : Blo 2127435 3592775 := bstep (se 1 (by rfl) ⟨2694581, by rfl⟩ : syracuseStep 3592775 = 5389163) B5389163
theorem B2395183 : Blo 2127435 2395183 := bstep (se 1 (by rfl) ⟨1796387, by rfl⟩ : syracuseStep 2395183 = 3592775) B3592775
theorem B3193577 : Blo 2127435 3193577 := bstep (se 2 (by rfl) ⟨1197591, by rfl⟩ : syracuseStep 3193577 = 2395183) B2395183
theorem B2129051 : Blo 2127435 2129051 := bstep (se 1 (by rfl) ⟨1596788, by rfl⟩ : syracuseStep 2129051 = 3193577) B3193577
theorem B2304577 : Blo 2127435 2304577 := bbase (se 2 (by rfl) ⟨864216, by rfl⟩ : syracuseStep 2304577 = 1728433) (by norm_num)
theorem B12291077 : Blo 2127435 12291077 := bstep (se 4 (by rfl) ⟨1152288, by rfl⟩ : syracuseStep 12291077 = 2304577) B2304577
theorem B8194051 : Blo 2127435 8194051 := bstep (se 1 (by rfl) ⟨6145538, by rfl⟩ : syracuseStep 8194051 = 12291077) B12291077
theorem B10925401 : Blo 2127435 10925401 := bstep (se 2 (by rfl) ⟨4097025, by rfl⟩ : syracuseStep 10925401 = 8194051) B8194051
theorem B14567201 : Blo 2127435 14567201 := bstep (se 2 (by rfl) ⟨5462700, by rfl⟩ : syracuseStep 14567201 = 10925401) B10925401
theorem B9711467 : Blo 2127435 9711467 := bstep (se 1 (by rfl) ⟨7283600, by rfl⟩ : syracuseStep 9711467 = 14567201) B14567201
theorem B6474311 : Blo 2127435 6474311 := bstep (se 1 (by rfl) ⟨4855733, by rfl⟩ : syracuseStep 6474311 = 9711467) B9711467
theorem B4316207 : Blo 2127435 4316207 := bstep (se 1 (by rfl) ⟨3237155, by rfl⟩ : syracuseStep 4316207 = 6474311) B6474311
theorem B11509885 : Blo 2127435 11509885 := bstep (se 3 (by rfl) ⟨2158103, by rfl⟩ : syracuseStep 11509885 = 4316207) B4316207
theorem B15346513 : Blo 2127435 15346513 := bstep (se 2 (by rfl) ⟨5754942, by rfl⟩ : syracuseStep 15346513 = 11509885) B11509885
theorem B20462017 : Blo 2127435 20462017 := bstep (se 2 (by rfl) ⟨7673256, by rfl⟩ : syracuseStep 20462017 = 15346513) B15346513
theorem B27282689 : Blo 2127435 27282689 := bstep (se 2 (by rfl) ⟨10231008, by rfl⟩ : syracuseStep 27282689 = 20462017) B20462017
theorem B18188459 : Blo 2127435 18188459 := bstep (se 1 (by rfl) ⟨13641344, by rfl⟩ : syracuseStep 18188459 = 27282689) B27282689
theorem B12125639 : Blo 2127435 12125639 := bstep (se 1 (by rfl) ⟨9094229, by rfl⟩ : syracuseStep 12125639 = 18188459) B18188459
theorem B8083759 : Blo 2127435 8083759 := bstep (se 1 (by rfl) ⟨6062819, by rfl⟩ : syracuseStep 8083759 = 12125639) B12125639
theorem B10778345 : Blo 2127435 10778345 := bstep (se 2 (by rfl) ⟨4041879, by rfl⟩ : syracuseStep 10778345 = 8083759) B8083759
theorem B7185563 : Blo 2127435 7185563 := bstep (se 1 (by rfl) ⟨5389172, by rfl⟩ : syracuseStep 7185563 = 10778345) B10778345
theorem B4790375 : Blo 2127435 4790375 := bstep (se 1 (by rfl) ⟨3592781, by rfl⟩ : syracuseStep 4790375 = 7185563) B7185563
theorem B3193583 : Blo 2127435 3193583 := bstep (se 1 (by rfl) ⟨2395187, by rfl⟩ : syracuseStep 3193583 = 4790375) B4790375
theorem B2129055 : Blo 2127435 2129055 := bstep (se 1 (by rfl) ⟨1596791, by rfl⟩ : syracuseStep 2129055 = 3193583) B3193583
theorem B3193589 : Blo 2127435 3193589 := bbase (se 5 (by rfl) ⟨149699, by rfl⟩ : syracuseStep 3193589 = 299399) (by norm_num)
theorem B2129059 : Blo 2127435 2129059 := bstep (se 1 (by rfl) ⟨1596794, by rfl⟩ : syracuseStep 2129059 = 3193589) B3193589
theorem B2731361 : Blo 2127435 2731361 := bbase (se 2 (by rfl) ⟨1024260, by rfl⟩ : syracuseStep 2731361 = 2048521) (by norm_num)
theorem B7283629 : Blo 2127435 7283629 := bstep (se 3 (by rfl) ⟨1365680, by rfl⟩ : syracuseStep 7283629 = 2731361) B2731361
theorem B9711505 : Blo 2127435 9711505 := bstep (se 2 (by rfl) ⟨3641814, by rfl⟩ : syracuseStep 9711505 = 7283629) B7283629
theorem B12948673 : Blo 2127435 12948673 := bstep (se 2 (by rfl) ⟨4855752, by rfl⟩ : syracuseStep 12948673 = 9711505) B9711505
theorem B17264897 : Blo 2127435 17264897 := bstep (se 2 (by rfl) ⟨6474336, by rfl⟩ : syracuseStep 17264897 = 12948673) B12948673
theorem B11509931 : Blo 2127435 11509931 := bstep (se 1 (by rfl) ⟨8632448, by rfl⟩ : syracuseStep 11509931 = 17264897) B17264897
theorem B7673287 : Blo 2127435 7673287 := bstep (se 1 (by rfl) ⟨5754965, by rfl⟩ : syracuseStep 7673287 = 11509931) B11509931
theorem B10231049 : Blo 2127435 10231049 := bstep (se 2 (by rfl) ⟨3836643, by rfl⟩ : syracuseStep 10231049 = 7673287) B7673287
theorem B6820699 : Blo 2127435 6820699 := bstep (se 1 (by rfl) ⟨5115524, by rfl⟩ : syracuseStep 6820699 = 10231049) B10231049
theorem B9094265 : Blo 2127435 9094265 := bstep (se 2 (by rfl) ⟨3410349, by rfl⟩ : syracuseStep 9094265 = 6820699) B6820699
theorem B6062843 : Blo 2127435 6062843 := bstep (se 1 (by rfl) ⟨4547132, by rfl⟩ : syracuseStep 6062843 = 9094265) B9094265
theorem B4041895 : Blo 2127435 4041895 := bstep (se 1 (by rfl) ⟨3031421, by rfl⟩ : syracuseStep 4041895 = 6062843) B6062843
theorem B5389193 : Blo 2127435 5389193 := bstep (se 2 (by rfl) ⟨2020947, by rfl⟩ : syracuseStep 5389193 = 4041895) B4041895
theorem B3592795 : Blo 2127435 3592795 := bstep (se 1 (by rfl) ⟨2694596, by rfl⟩ : syracuseStep 3592795 = 5389193) B5389193
theorem B4790393 : Blo 2127435 4790393 := bstep (se 2 (by rfl) ⟨1796397, by rfl⟩ : syracuseStep 4790393 = 3592795) B3592795
theorem B3193595 : Blo 2127435 3193595 := bstep (se 1 (by rfl) ⟨2395196, by rfl⟩ : syracuseStep 3193595 = 4790393) B4790393
theorem B2129063 : Blo 2127435 2129063 := bstep (se 1 (by rfl) ⟨1596797, by rfl⟩ : syracuseStep 2129063 = 3193595) B3193595
theorem B2395201 : Blo 2127435 2395201 := bbase (se 2 (by rfl) ⟨898200, by rfl⟩ : syracuseStep 2395201 = 1796401) (by norm_num)
theorem B3193601 : Blo 2127435 3193601 := bstep (se 2 (by rfl) ⟨1197600, by rfl⟩ : syracuseStep 3193601 = 2395201) B2395201
theorem B2129067 : Blo 2127435 2129067 := bstep (se 1 (by rfl) ⟨1596800, by rfl⟩ : syracuseStep 2129067 = 3193601) B3193601
theorem B5389213 : Blo 2127435 5389213 := bbase (se 3 (by rfl) ⟨1010477, by rfl⟩ : syracuseStep 5389213 = 2020955) (by norm_num)
theorem B7185617 : Blo 2127435 7185617 := bstep (se 2 (by rfl) ⟨2694606, by rfl⟩ : syracuseStep 7185617 = 5389213) B5389213
theorem B4790411 : Blo 2127435 4790411 := bstep (se 1 (by rfl) ⟨3592808, by rfl⟩ : syracuseStep 4790411 = 7185617) B7185617
theorem B3193607 : Blo 2127435 3193607 := bstep (se 1 (by rfl) ⟨2395205, by rfl⟩ : syracuseStep 3193607 = 4790411) B4790411
theorem B2129071 : Blo 2127435 2129071 := bstep (se 1 (by rfl) ⟨1596803, by rfl⟩ : syracuseStep 2129071 = 3193607) B3193607
theorem B3193613 : Blo 2127435 3193613 := bbase (se 3 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 3193613 = 1197605) (by norm_num)
theorem B2129075 : Blo 2127435 2129075 := bstep (se 1 (by rfl) ⟨1596806, by rfl⟩ : syracuseStep 2129075 = 3193613) B3193613
theorem B4790429 : Blo 2127435 4790429 := bbase (se 3 (by rfl) ⟨898205, by rfl⟩ : syracuseStep 4790429 = 1796411) (by norm_num)
theorem B3193619 : Blo 2127435 3193619 := bstep (se 1 (by rfl) ⟨2395214, by rfl⟩ : syracuseStep 3193619 = 4790429) B4790429
theorem B2129079 : Blo 2127435 2129079 := bstep (se 1 (by rfl) ⟨1596809, by rfl⟩ : syracuseStep 2129079 = 3193619) B3193619
theorem B3592829 : Blo 2127435 3592829 := bbase (se 3 (by rfl) ⟨673655, by rfl⟩ : syracuseStep 3592829 = 1347311) (by norm_num)
theorem B2395219 : Blo 2127435 2395219 := bstep (se 1 (by rfl) ⟨1796414, by rfl⟩ : syracuseStep 2395219 = 3592829) B3592829
theorem B3193625 : Blo 2127435 3193625 := bstep (se 2 (by rfl) ⟨1197609, by rfl⟩ : syracuseStep 3193625 = 2395219) B2395219
theorem B2129083 : Blo 2127435 2129083 := bstep (se 1 (by rfl) ⟨1596812, by rfl⟩ : syracuseStep 2129083 = 3193625) B3193625
theorem B39913685 : Blo 2127435 39913685 := bbase (se 7 (by rfl) ⟨467738, by rfl⟩ : syracuseStep 39913685 = 935477) (by norm_num)
theorem B26609123 : Blo 2127435 26609123 := bstep (se 1 (by rfl) ⟨19956842, by rfl⟩ : syracuseStep 26609123 = 39913685) B39913685
theorem B17739415 : Blo 2127435 17739415 := bstep (se 1 (by rfl) ⟨13304561, by rfl⟩ : syracuseStep 17739415 = 26609123) B26609123
theorem B94610213 : Blo 2127435 94610213 := bstep (se 4 (by rfl) ⟨8869707, by rfl⟩ : syracuseStep 94610213 = 17739415) B17739415
theorem B63073475 : Blo 2127435 63073475 := bstep (se 1 (by rfl) ⟨47305106, by rfl⟩ : syracuseStep 63073475 = 94610213) B94610213
theorem B42048983 : Blo 2127435 42048983 := bstep (se 1 (by rfl) ⟨31536737, by rfl⟩ : syracuseStep 42048983 = 63073475) B63073475
theorem B28032655 : Blo 2127435 28032655 := bstep (se 1 (by rfl) ⟨21024491, by rfl⟩ : syracuseStep 28032655 = 42048983) B42048983
theorem B37376873 : Blo 2127435 37376873 := bstep (se 2 (by rfl) ⟨14016327, by rfl⟩ : syracuseStep 37376873 = 28032655) B28032655
theorem B24917915 : Blo 2127435 24917915 := bstep (se 1 (by rfl) ⟨18688436, by rfl⟩ : syracuseStep 24917915 = 37376873) B37376873
theorem B66447773 : Blo 2127435 66447773 := bstep (se 3 (by rfl) ⟨12458957, by rfl⟩ : syracuseStep 66447773 = 24917915) B24917915
theorem B44298515 : Blo 2127435 44298515 := bstep (se 1 (by rfl) ⟨33223886, by rfl⟩ : syracuseStep 44298515 = 66447773) B66447773
theorem B29532343 : Blo 2127435 29532343 := bstep (se 1 (by rfl) ⟨22149257, by rfl⟩ : syracuseStep 29532343 = 44298515) B44298515
theorem B39376457 : Blo 2127435 39376457 := bstep (se 2 (by rfl) ⟨14766171, by rfl⟩ : syracuseStep 39376457 = 29532343) B29532343
theorem B26250971 : Blo 2127435 26250971 := bstep (se 1 (by rfl) ⟨19688228, by rfl⟩ : syracuseStep 26250971 = 39376457) B39376457
theorem B70002589 : Blo 2127435 70002589 := bstep (se 3 (by rfl) ⟨13125485, by rfl⟩ : syracuseStep 70002589 = 26250971) B26250971
theorem B93336785 : Blo 2127435 93336785 := bstep (se 2 (by rfl) ⟨35001294, by rfl⟩ : syracuseStep 93336785 = 70002589) B70002589
theorem B62224523 : Blo 2127435 62224523 := bstep (se 1 (by rfl) ⟨46668392, by rfl⟩ : syracuseStep 62224523 = 93336785) B93336785
theorem B41483015 : Blo 2127435 41483015 := bstep (se 1 (by rfl) ⟨31112261, by rfl⟩ : syracuseStep 41483015 = 62224523) B62224523
theorem B27655343 : Blo 2127435 27655343 := bstep (se 1 (by rfl) ⟨20741507, by rfl⟩ : syracuseStep 27655343 = 41483015) B41483015
theorem B18436895 : Blo 2127435 18436895 := bstep (se 1 (by rfl) ⟨13827671, by rfl⟩ : syracuseStep 18436895 = 27655343) B27655343
theorem B12291263 : Blo 2127435 12291263 := bstep (se 1 (by rfl) ⟨9218447, by rfl⟩ : syracuseStep 12291263 = 18436895) B18436895
theorem B8194175 : Blo 2127435 8194175 := bstep (se 1 (by rfl) ⟨6145631, by rfl⟩ : syracuseStep 8194175 = 12291263) B12291263
theorem B5462783 : Blo 2127435 5462783 := bstep (se 1 (by rfl) ⟨4097087, by rfl⟩ : syracuseStep 5462783 = 8194175) B8194175
theorem B3641855 : Blo 2127435 3641855 := bstep (se 1 (by rfl) ⟨2731391, by rfl⟩ : syracuseStep 3641855 = 5462783) B5462783
theorem B9711613 : Blo 2127435 9711613 := bstep (se 3 (by rfl) ⟨1820927, by rfl⟩ : syracuseStep 9711613 = 3641855) B3641855
theorem B12948817 : Blo 2127435 12948817 := bstep (se 2 (by rfl) ⟨4855806, by rfl⟩ : syracuseStep 12948817 = 9711613) B9711613
theorem B17265089 : Blo 2127435 17265089 := bstep (se 2 (by rfl) ⟨6474408, by rfl⟩ : syracuseStep 17265089 = 12948817) B12948817
theorem B11510059 : Blo 2127435 11510059 := bstep (se 1 (by rfl) ⟨8632544, by rfl⟩ : syracuseStep 11510059 = 17265089) B17265089
theorem B15346745 : Blo 2127435 15346745 := bstep (se 2 (by rfl) ⟨5755029, by rfl⟩ : syracuseStep 15346745 = 11510059) B11510059
theorem B10231163 : Blo 2127435 10231163 := bstep (se 1 (by rfl) ⟨7673372, by rfl⟩ : syracuseStep 10231163 = 15346745) B15346745
theorem B6820775 : Blo 2127435 6820775 := bstep (se 1 (by rfl) ⟨5115581, by rfl⟩ : syracuseStep 6820775 = 10231163) B10231163
theorem B4547183 : Blo 2127435 4547183 := bstep (se 1 (by rfl) ⟨3410387, by rfl⟩ : syracuseStep 4547183 = 6820775) B6820775
theorem B12125821 : Blo 2127435 12125821 := bstep (se 3 (by rfl) ⟨2273591, by rfl⟩ : syracuseStep 12125821 = 4547183) B4547183
theorem B16167761 : Blo 2127435 16167761 := bstep (se 2 (by rfl) ⟨6062910, by rfl⟩ : syracuseStep 16167761 = 12125821) B12125821
theorem B10778507 : Blo 2127435 10778507 := bstep (se 1 (by rfl) ⟨8083880, by rfl⟩ : syracuseStep 10778507 = 16167761) B16167761
theorem B7185671 : Blo 2127435 7185671 := bstep (se 1 (by rfl) ⟨5389253, by rfl⟩ : syracuseStep 7185671 = 10778507) B10778507
theorem B4790447 : Blo 2127435 4790447 := bstep (se 1 (by rfl) ⟨3592835, by rfl⟩ : syracuseStep 4790447 = 7185671) B7185671
theorem B3193631 : Blo 2127435 3193631 := bstep (se 1 (by rfl) ⟨2395223, by rfl⟩ : syracuseStep 3193631 = 4790447) B4790447
theorem B2129087 : Blo 2127435 2129087 := bstep (se 1 (by rfl) ⟨1596815, by rfl⟩ : syracuseStep 2129087 = 3193631) B3193631
theorem B3193637 : Blo 2127435 3193637 := bbase (se 4 (by rfl) ⟨299403, by rfl⟩ : syracuseStep 3193637 = 598807) (by norm_num)
theorem B2129091 : Blo 2127435 2129091 := bstep (se 1 (by rfl) ⟨1596818, by rfl⟩ : syracuseStep 2129091 = 3193637) B3193637
theorem B2694637 : Blo 2127435 2694637 := bbase (se 3 (by rfl) ⟨505244, by rfl⟩ : syracuseStep 2694637 = 1010489) (by norm_num)
theorem B3592849 : Blo 2127435 3592849 := bstep (se 2 (by rfl) ⟨1347318, by rfl⟩ : syracuseStep 3592849 = 2694637) B2694637
theorem B4790465 : Blo 2127435 4790465 := bstep (se 2 (by rfl) ⟨1796424, by rfl⟩ : syracuseStep 4790465 = 3592849) B3592849
theorem B3193643 : Blo 2127435 3193643 := bstep (se 1 (by rfl) ⟨2395232, by rfl⟩ : syracuseStep 3193643 = 4790465) B4790465
theorem B2129095 : Blo 2127435 2129095 := bstep (se 1 (by rfl) ⟨1596821, by rfl⟩ : syracuseStep 2129095 = 3193643) B3193643
theorem B2395237 : Blo 2127435 2395237 := bbase (se 4 (by rfl) ⟨224553, by rfl⟩ : syracuseStep 2395237 = 449107) (by norm_num)
theorem B3193649 : Blo 2127435 3193649 := bstep (se 2 (by rfl) ⟨1197618, by rfl⟩ : syracuseStep 3193649 = 2395237) B2395237
theorem B2129099 : Blo 2127435 2129099 := bstep (se 1 (by rfl) ⟨1596824, by rfl⟩ : syracuseStep 2129099 = 3193649) B3193649
theorem B2273609 : Blo 2127435 2273609 := bbase (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) (by norm_num)
theorem B6062957 : Blo 2127435 6062957 := bstep (se 3 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 6062957 = 2273609) B2273609
theorem B4041971 : Blo 2127435 4041971 := bstep (se 1 (by rfl) ⟨3031478, by rfl⟩ : syracuseStep 4041971 = 6062957) B6062957
theorem B2694647 : Blo 2127435 2694647 := bstep (se 1 (by rfl) ⟨2020985, by rfl⟩ : syracuseStep 2694647 = 4041971) B4041971
theorem B7185725 : Blo 2127435 7185725 := bstep (se 3 (by rfl) ⟨1347323, by rfl⟩ : syracuseStep 7185725 = 2694647) B2694647
theorem B4790483 : Blo 2127435 4790483 := bstep (se 1 (by rfl) ⟨3592862, by rfl⟩ : syracuseStep 4790483 = 7185725) B7185725
theorem B3193655 : Blo 2127435 3193655 := bstep (se 1 (by rfl) ⟨2395241, by rfl⟩ : syracuseStep 3193655 = 4790483) B4790483
theorem B2129103 : Blo 2127435 2129103 := bstep (se 1 (by rfl) ⟨1596827, by rfl⟩ : syracuseStep 2129103 = 3193655) B3193655
theorem B3193661 : Blo 2127435 3193661 := bbase (se 3 (by rfl) ⟨598811, by rfl⟩ : syracuseStep 3193661 = 1197623) (by norm_num)
theorem B2129107 : Blo 2127435 2129107 := bstep (se 1 (by rfl) ⟨1596830, by rfl⟩ : syracuseStep 2129107 = 3193661) B3193661
theorem B4790501 : Blo 2127435 4790501 := bbase (se 4 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 4790501 = 898219) (by norm_num)
theorem B3193667 : Blo 2127435 3193667 := bstep (se 1 (by rfl) ⟨2395250, by rfl⟩ : syracuseStep 3193667 = 4790501) B4790501
theorem B2129111 : Blo 2127435 2129111 := bstep (se 1 (by rfl) ⟨1596833, by rfl⟩ : syracuseStep 2129111 = 3193667) B3193667
theorem B5389325 : Blo 2127435 5389325 := bbase (se 3 (by rfl) ⟨1010498, by rfl⟩ : syracuseStep 5389325 = 2020997) (by norm_num)
theorem B3592883 : Blo 2127435 3592883 := bstep (se 1 (by rfl) ⟨2694662, by rfl⟩ : syracuseStep 3592883 = 5389325) B5389325
theorem B2395255 : Blo 2127435 2395255 := bstep (se 1 (by rfl) ⟨1796441, by rfl⟩ : syracuseStep 2395255 = 3592883) B3592883
theorem B3193673 : Blo 2127435 3193673 := bstep (se 2 (by rfl) ⟨1197627, by rfl⟩ : syracuseStep 3193673 = 2395255) B2395255
theorem B2129115 : Blo 2127435 2129115 := bstep (se 1 (by rfl) ⟨1596836, by rfl⟩ : syracuseStep 2129115 = 3193673) B3193673
theorem B3031501 : Blo 2127435 3031501 := bbase (se 3 (by rfl) ⟨568406, by rfl⟩ : syracuseStep 3031501 = 1136813) (by norm_num)
theorem B4042001 : Blo 2127435 4042001 := bstep (se 2 (by rfl) ⟨1515750, by rfl⟩ : syracuseStep 4042001 = 3031501) B3031501
theorem B10778669 : Blo 2127435 10778669 := bstep (se 3 (by rfl) ⟨2021000, by rfl⟩ : syracuseStep 10778669 = 4042001) B4042001
theorem B7185779 : Blo 2127435 7185779 := bstep (se 1 (by rfl) ⟨5389334, by rfl⟩ : syracuseStep 7185779 = 10778669) B10778669
theorem B4790519 : Blo 2127435 4790519 := bstep (se 1 (by rfl) ⟨3592889, by rfl⟩ : syracuseStep 4790519 = 7185779) B7185779
theorem B3193679 : Blo 2127435 3193679 := bstep (se 1 (by rfl) ⟨2395259, by rfl⟩ : syracuseStep 3193679 = 4790519) B4790519
theorem B2129119 : Blo 2127435 2129119 := bstep (se 1 (by rfl) ⟨1596839, by rfl⟩ : syracuseStep 2129119 = 3193679) B3193679
theorem B3193685 : Blo 2127435 3193685 := bbase (se 9 (by rfl) ⟨9356, by rfl⟩ : syracuseStep 3193685 = 18713) (by norm_num)
theorem B2129123 : Blo 2127435 2129123 := bstep (se 1 (by rfl) ⟨1596842, by rfl⟩ : syracuseStep 2129123 = 3193685) B3193685
theorem B4547269 : Blo 2127435 4547269 := bbase (se 4 (by rfl) ⟨426306, by rfl⟩ : syracuseStep 4547269 = 852613) (by norm_num)
theorem B6063025 : Blo 2127435 6063025 := bstep (se 2 (by rfl) ⟨2273634, by rfl⟩ : syracuseStep 6063025 = 4547269) B4547269
theorem B8084033 : Blo 2127435 8084033 := bstep (se 2 (by rfl) ⟨3031512, by rfl⟩ : syracuseStep 8084033 = 6063025) B6063025
theorem B5389355 : Blo 2127435 5389355 := bstep (se 1 (by rfl) ⟨4042016, by rfl⟩ : syracuseStep 5389355 = 8084033) B8084033
theorem B3592903 : Blo 2127435 3592903 := bstep (se 1 (by rfl) ⟨2694677, by rfl⟩ : syracuseStep 3592903 = 5389355) B5389355
theorem B4790537 : Blo 2127435 4790537 := bstep (se 2 (by rfl) ⟨1796451, by rfl⟩ : syracuseStep 4790537 = 3592903) B3592903
theorem B3193691 : Blo 2127435 3193691 := bstep (se 1 (by rfl) ⟨2395268, by rfl⟩ : syracuseStep 3193691 = 4790537) B4790537
theorem B2129127 : Blo 2127435 2129127 := bstep (se 1 (by rfl) ⟨1596845, by rfl⟩ : syracuseStep 2129127 = 3193691) B3193691
theorem B2395273 : Blo 2127435 2395273 := bbase (se 2 (by rfl) ⟨898227, by rfl⟩ : syracuseStep 2395273 = 1796455) (by norm_num)
theorem B3193697 : Blo 2127435 3193697 := bstep (se 2 (by rfl) ⟨1197636, by rfl⟩ : syracuseStep 3193697 = 2395273) B2395273
theorem B2129131 : Blo 2127435 2129131 := bstep (se 1 (by rfl) ⟨1596848, by rfl⟩ : syracuseStep 2129131 = 3193697) B3193697
theorem B12949109 : Blo 2127435 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B8632739 : Blo 2127435 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B5755159 : Blo 2127435 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B7673545 : Blo 2127435 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B40925573 : Blo 2127435 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B27283715 : Blo 2127435 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B18189143 : Blo 2127435 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B12126095 : Blo 2127435 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B8084063 : Blo 2127435 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B5389375 : Blo 2127435 5389375 := bstep (se 1 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 5389375 = 8084063) B8084063
theorem B7185833 : Blo 2127435 7185833 := bstep (se 2 (by rfl) ⟨2694687, by rfl⟩ : syracuseStep 7185833 = 5389375) B5389375
theorem B4790555 : Blo 2127435 4790555 := bstep (se 1 (by rfl) ⟨3592916, by rfl⟩ : syracuseStep 4790555 = 7185833) B7185833
theorem B3193703 : Blo 2127435 3193703 := bstep (se 1 (by rfl) ⟨2395277, by rfl⟩ : syracuseStep 3193703 = 4790555) B4790555
theorem B2129135 : Blo 2127435 2129135 := bstep (se 1 (by rfl) ⟨1596851, by rfl⟩ : syracuseStep 2129135 = 3193703) B3193703
theorem B3193709 : Blo 2127435 3193709 := bbase (se 3 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 3193709 = 1197641) (by norm_num)
theorem B2129139 : Blo 2127435 2129139 := bstep (se 1 (by rfl) ⟨1596854, by rfl⟩ : syracuseStep 2129139 = 3193709) B3193709
theorem B4790573 : Blo 2127435 4790573 := bbase (se 3 (by rfl) ⟨898232, by rfl⟩ : syracuseStep 4790573 = 1796465) (by norm_num)
theorem B3193715 : Blo 2127435 3193715 := bstep (se 1 (by rfl) ⟨2395286, by rfl⟩ : syracuseStep 3193715 = 4790573) B4790573
theorem B2129143 : Blo 2127435 2129143 := bstep (se 1 (by rfl) ⟨1596857, by rfl⟩ : syracuseStep 2129143 = 3193715) B3193715
theorem B20742101 : Blo 2127435 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B13828067 : Blo 2127435 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B9218711 : Blo 2127435 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B6145807 : Blo 2127435 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B8194409 : Blo 2127435 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B5462939 : Blo 2127435 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B3641959 : Blo 2127435 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B4855945 : Blo 2127435 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B6474593 : Blo 2127435 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B17265581 : Blo 2127435 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B11510387 : Blo 2127435 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B7673591 : Blo 2127435 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B5115727 : Blo 2127435 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B6820969 : Blo 2127435 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B9094625 : Blo 2127435 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B6063083 : Blo 2127435 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B4042055 : Blo 2127435 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B2694703 : Blo 2127435 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B3592937 : Blo 2127435 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B2395291 : Blo 2127435 2395291 := bstep (se 1 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 2395291 = 3592937) B3592937
theorem B3193721 : Blo 2127435 3193721 := bstep (se 2 (by rfl) ⟨1197645, by rfl⟩ : syracuseStep 3193721 = 2395291) B2395291
theorem B2129147 : Blo 2127435 2129147 := bstep (se 1 (by rfl) ⟨1596860, by rfl⟩ : syracuseStep 2129147 = 3193721) B3193721
theorem B2336125 : Blo 2127435 2336125 := bbase (se 3 (by rfl) ⟨438023, by rfl⟩ : syracuseStep 2336125 = 876047) (by norm_num)
theorem B3114833 : Blo 2127435 3114833 := bstep (se 2 (by rfl) ⟨1168062, by rfl⟩ : syracuseStep 3114833 = 2336125) B2336125
theorem B8306221 : Blo 2127435 8306221 := bstep (se 3 (by rfl) ⟨1557416, by rfl⟩ : syracuseStep 8306221 = 3114833) B3114833
theorem B11074961 : Blo 2127435 11074961 := bstep (se 2 (by rfl) ⟨4153110, by rfl⟩ : syracuseStep 11074961 = 8306221) B8306221
theorem B7383307 : Blo 2127435 7383307 := bstep (se 1 (by rfl) ⟨5537480, by rfl⟩ : syracuseStep 7383307 = 11074961) B11074961
theorem B9844409 : Blo 2127435 9844409 := bstep (se 2 (by rfl) ⟨3691653, by rfl⟩ : syracuseStep 9844409 = 7383307) B7383307
theorem B6562939 : Blo 2127435 6562939 := bstep (se 1 (by rfl) ⟨4922204, by rfl⟩ : syracuseStep 6562939 = 9844409) B9844409
theorem B8750585 : Blo 2127435 8750585 := bstep (se 2 (by rfl) ⟨3281469, by rfl⟩ : syracuseStep 8750585 = 6562939) B6562939
theorem B5833723 : Blo 2127435 5833723 := bstep (se 1 (by rfl) ⟨4375292, by rfl⟩ : syracuseStep 5833723 = 8750585) B8750585
theorem B7778297 : Blo 2127435 7778297 := bstep (se 2 (by rfl) ⟨2916861, by rfl⟩ : syracuseStep 7778297 = 5833723) B5833723
theorem B5185531 : Blo 2127435 5185531 := bstep (se 1 (by rfl) ⟨3889148, by rfl⟩ : syracuseStep 5185531 = 7778297) B7778297
theorem B6914041 : Blo 2127435 6914041 := bstep (se 2 (by rfl) ⟨2592765, by rfl⟩ : syracuseStep 6914041 = 5185531) B5185531
theorem B36874885 : Blo 2127435 36874885 := bstep (se 4 (by rfl) ⟨3457020, by rfl⟩ : syracuseStep 36874885 = 6914041) B6914041
theorem B49166513 : Blo 2127435 49166513 := bstep (se 2 (by rfl) ⟨18437442, by rfl⟩ : syracuseStep 49166513 = 36874885) B36874885
theorem B32777675 : Blo 2127435 32777675 := bstep (se 1 (by rfl) ⟨24583256, by rfl⟩ : syracuseStep 32777675 = 49166513) B49166513
theorem B21851783 : Blo 2127435 21851783 := bstep (se 1 (by rfl) ⟨16388837, by rfl⟩ : syracuseStep 21851783 = 32777675) B32777675
theorem B14567855 : Blo 2127435 14567855 := bstep (se 1 (by rfl) ⟨10925891, by rfl⟩ : syracuseStep 14567855 = 21851783) B21851783
theorem B38847613 : Blo 2127435 38847613 := bstep (se 3 (by rfl) ⟨7283927, by rfl⟩ : syracuseStep 38847613 = 14567855) B14567855
theorem B51796817 : Blo 2127435 51796817 := bstep (se 2 (by rfl) ⟨19423806, by rfl⟩ : syracuseStep 51796817 = 38847613) B38847613
theorem B34531211 : Blo 2127435 34531211 := bstep (se 1 (by rfl) ⟨25898408, by rfl⟩ : syracuseStep 34531211 = 51796817) B51796817
theorem B23020807 : Blo 2127435 23020807 := bstep (se 1 (by rfl) ⟨17265605, by rfl⟩ : syracuseStep 23020807 = 34531211) B34531211
theorem B30694409 : Blo 2127435 30694409 := bstep (se 2 (by rfl) ⟨11510403, by rfl⟩ : syracuseStep 30694409 = 23020807) B23020807
theorem B20462939 : Blo 2127435 20462939 := bstep (se 1 (by rfl) ⟨15347204, by rfl⟩ : syracuseStep 20462939 = 30694409) B30694409
theorem B13641959 : Blo 2127435 13641959 := bstep (se 1 (by rfl) ⟨10231469, by rfl⟩ : syracuseStep 13641959 = 20462939) B20462939
theorem B36378557 : Blo 2127435 36378557 := bstep (se 3 (by rfl) ⟨6820979, by rfl⟩ : syracuseStep 36378557 = 13641959) B13641959
theorem B24252371 : Blo 2127435 24252371 := bstep (se 1 (by rfl) ⟨18189278, by rfl⟩ : syracuseStep 24252371 = 36378557) B36378557
theorem B16168247 : Blo 2127435 16168247 := bstep (se 1 (by rfl) ⟨12126185, by rfl⟩ : syracuseStep 16168247 = 24252371) B24252371
theorem B10778831 : Blo 2127435 10778831 := bstep (se 1 (by rfl) ⟨8084123, by rfl⟩ : syracuseStep 10778831 = 16168247) B16168247
theorem B7185887 : Blo 2127435 7185887 := bstep (se 1 (by rfl) ⟨5389415, by rfl⟩ : syracuseStep 7185887 = 10778831) B10778831
theorem B4790591 : Blo 2127435 4790591 := bstep (se 1 (by rfl) ⟨3592943, by rfl⟩ : syracuseStep 4790591 = 7185887) B7185887
theorem B3193727 : Blo 2127435 3193727 := bstep (se 1 (by rfl) ⟨2395295, by rfl⟩ : syracuseStep 3193727 = 4790591) B4790591
theorem B2129151 : Blo 2127435 2129151 := bstep (se 1 (by rfl) ⟨1596863, by rfl⟩ : syracuseStep 2129151 = 3193727) B3193727
theorem B3193733 : Blo 2127435 3193733 := bbase (se 4 (by rfl) ⟨299412, by rfl⟩ : syracuseStep 3193733 = 598825) (by norm_num)
theorem B2129155 : Blo 2127435 2129155 := bstep (se 1 (by rfl) ⟨1596866, by rfl⟩ : syracuseStep 2129155 = 3193733) B3193733
theorem B3592957 : Blo 2127435 3592957 := bbase (se 3 (by rfl) ⟨673679, by rfl⟩ : syracuseStep 3592957 = 1347359) (by norm_num)
theorem B4790609 : Blo 2127435 4790609 := bstep (se 2 (by rfl) ⟨1796478, by rfl⟩ : syracuseStep 4790609 = 3592957) B3592957
theorem B3193739 : Blo 2127435 3193739 := bstep (se 1 (by rfl) ⟨2395304, by rfl⟩ : syracuseStep 3193739 = 4790609) B4790609
theorem B2129159 : Blo 2127435 2129159 := bstep (se 1 (by rfl) ⟨1596869, by rfl⟩ : syracuseStep 2129159 = 3193739) B3193739
theorem B2395309 : Blo 2127435 2395309 := bbase (se 3 (by rfl) ⟨449120, by rfl⟩ : syracuseStep 2395309 = 898241) (by norm_num)
theorem B3193745 : Blo 2127435 3193745 := bstep (se 2 (by rfl) ⟨1197654, by rfl⟩ : syracuseStep 3193745 = 2395309) B2395309
theorem B2129163 : Blo 2127435 2129163 := bstep (se 1 (by rfl) ⟨1596872, by rfl⟩ : syracuseStep 2129163 = 3193745) B3193745
theorem B7185941 : Blo 2127435 7185941 := bbase (se 6 (by rfl) ⟨168420, by rfl⟩ : syracuseStep 7185941 = 336841) (by norm_num)
theorem B4790627 : Blo 2127435 4790627 := bstep (se 1 (by rfl) ⟨3592970, by rfl⟩ : syracuseStep 4790627 = 7185941) B7185941
theorem B3193751 : Blo 2127435 3193751 := bstep (se 1 (by rfl) ⟨2395313, by rfl⟩ : syracuseStep 3193751 = 4790627) B4790627
theorem B2129167 : Blo 2127435 2129167 := bstep (se 1 (by rfl) ⟨1596875, by rfl⟩ : syracuseStep 2129167 = 3193751) B3193751
theorem B3193757 : Blo 2127435 3193757 := bbase (se 3 (by rfl) ⟨598829, by rfl⟩ : syracuseStep 3193757 = 1197659) (by norm_num)
theorem B2129171 : Blo 2127435 2129171 := bstep (se 1 (by rfl) ⟨1596878, by rfl⟩ : syracuseStep 2129171 = 3193757) B3193757
theorem B4790645 : Blo 2127435 4790645 := bbase (se 5 (by rfl) ⟨224561, by rfl⟩ : syracuseStep 4790645 = 449123) (by norm_num)
theorem B3193763 : Blo 2127435 3193763 := bstep (se 1 (by rfl) ⟨2395322, by rfl⟩ : syracuseStep 3193763 = 4790645) B4790645
theorem B2129175 : Blo 2127435 2129175 := bstep (se 1 (by rfl) ⟨1596881, by rfl⟩ : syracuseStep 2129175 = 3193763) B3193763
theorem B3642013 : Blo 2127435 3642013 := bbase (se 3 (by rfl) ⟨682877, by rfl⟩ : syracuseStep 3642013 = 1365755) (by norm_num)
theorem B19424069 : Blo 2127435 19424069 := bstep (se 4 (by rfl) ⟨1821006, by rfl⟩ : syracuseStep 19424069 = 3642013) B3642013
theorem B12949379 : Blo 2127435 12949379 := bstep (se 1 (by rfl) ⟨9712034, by rfl⟩ : syracuseStep 12949379 = 19424069) B19424069
theorem B8632919 : Blo 2127435 8632919 := bstep (se 1 (by rfl) ⟨6474689, by rfl⟩ : syracuseStep 8632919 = 12949379) B12949379
theorem B5755279 : Blo 2127435 5755279 := bstep (se 1 (by rfl) ⟨4316459, by rfl⟩ : syracuseStep 5755279 = 8632919) B8632919
theorem B7673705 : Blo 2127435 7673705 := bstep (se 2 (by rfl) ⟨2877639, by rfl⟩ : syracuseStep 7673705 = 5755279) B5755279
theorem B5115803 : Blo 2127435 5115803 := bstep (se 1 (by rfl) ⟨3836852, by rfl⟩ : syracuseStep 5115803 = 7673705) B7673705
theorem B13642141 : Blo 2127435 13642141 := bstep (se 3 (by rfl) ⟨2557901, by rfl⟩ : syracuseStep 13642141 = 5115803) B5115803
theorem B18189521 : Blo 2127435 18189521 := bstep (se 2 (by rfl) ⟨6821070, by rfl⟩ : syracuseStep 18189521 = 13642141) B13642141
theorem B12126347 : Blo 2127435 12126347 := bstep (se 1 (by rfl) ⟨9094760, by rfl⟩ : syracuseStep 12126347 = 18189521) B18189521
theorem B8084231 : Blo 2127435 8084231 := bstep (se 1 (by rfl) ⟨6063173, by rfl⟩ : syracuseStep 8084231 = 12126347) B12126347
theorem B5389487 : Blo 2127435 5389487 := bstep (se 1 (by rfl) ⟨4042115, by rfl⟩ : syracuseStep 5389487 = 8084231) B8084231
theorem B3592991 : Blo 2127435 3592991 := bstep (se 1 (by rfl) ⟨2694743, by rfl⟩ : syracuseStep 3592991 = 5389487) B5389487
theorem B2395327 : Blo 2127435 2395327 := bstep (se 1 (by rfl) ⟨1796495, by rfl⟩ : syracuseStep 2395327 = 3592991) B3592991
theorem B3193769 : Blo 2127435 3193769 := bstep (se 2 (by rfl) ⟨1197663, by rfl⟩ : syracuseStep 3193769 = 2395327) B2395327
theorem B2129179 : Blo 2127435 2129179 := bstep (se 1 (by rfl) ⟨1596884, by rfl⟩ : syracuseStep 2129179 = 3193769) B3193769
theorem B8084245 : Blo 2127435 8084245 := bbase (se 6 (by rfl) ⟨189474, by rfl⟩ : syracuseStep 8084245 = 378949) (by norm_num)
theorem B10778993 : Blo 2127435 10778993 := bstep (se 2 (by rfl) ⟨4042122, by rfl⟩ : syracuseStep 10778993 = 8084245) B8084245
theorem B7185995 : Blo 2127435 7185995 := bstep (se 1 (by rfl) ⟨5389496, by rfl⟩ : syracuseStep 7185995 = 10778993) B10778993
theorem B4790663 : Blo 2127435 4790663 := bstep (se 1 (by rfl) ⟨3592997, by rfl⟩ : syracuseStep 4790663 = 7185995) B7185995
theorem B3193775 : Blo 2127435 3193775 := bstep (se 1 (by rfl) ⟨2395331, by rfl⟩ : syracuseStep 3193775 = 4790663) B4790663
theorem B2129183 : Blo 2127435 2129183 := bstep (se 1 (by rfl) ⟨1596887, by rfl⟩ : syracuseStep 2129183 = 3193775) B3193775
theorem B3193781 : Blo 2127435 3193781 := bbase (se 5 (by rfl) ⟨149708, by rfl⟩ : syracuseStep 3193781 = 299417) (by norm_num)
theorem B2129187 : Blo 2127435 2129187 := bstep (se 1 (by rfl) ⟨1596890, by rfl⟩ : syracuseStep 2129187 = 3193781) B3193781
theorem B5389517 : Blo 2127435 5389517 := bbase (se 3 (by rfl) ⟨1010534, by rfl⟩ : syracuseStep 5389517 = 2021069) (by norm_num)
theorem B3593011 : Blo 2127435 3593011 := bstep (se 1 (by rfl) ⟨2694758, by rfl⟩ : syracuseStep 3593011 = 5389517) B5389517
theorem B4790681 : Blo 2127435 4790681 := bstep (se 2 (by rfl) ⟨1796505, by rfl⟩ : syracuseStep 4790681 = 3593011) B3593011
theorem B3193787 : Blo 2127435 3193787 := bstep (se 1 (by rfl) ⟨2395340, by rfl⟩ : syracuseStep 3193787 = 4790681) B4790681
theorem B2129191 : Blo 2127435 2129191 := bstep (se 1 (by rfl) ⟨1596893, by rfl⟩ : syracuseStep 2129191 = 3193787) B3193787
theorem B2395345 : Blo 2127435 2395345 := bbase (se 2 (by rfl) ⟨898254, by rfl⟩ : syracuseStep 2395345 = 1796509) (by norm_num)
theorem B3193793 : Blo 2127435 3193793 := bstep (se 2 (by rfl) ⟨1197672, by rfl⟩ : syracuseStep 3193793 = 2395345) B2395345
theorem B2129195 : Blo 2127435 2129195 := bstep (se 1 (by rfl) ⟨1596896, by rfl⟩ : syracuseStep 2129195 = 3193793) B3193793
theorem B23021333 : Blo 2127435 23021333 := bbase (se 6 (by rfl) ⟨539562, by rfl⟩ : syracuseStep 23021333 = 1079125) (by norm_num)
theorem B15347555 : Blo 2127435 15347555 := bstep (se 1 (by rfl) ⟨11510666, by rfl⟩ : syracuseStep 15347555 = 23021333) B23021333
theorem B10231703 : Blo 2127435 10231703 := bstep (se 1 (by rfl) ⟨7673777, by rfl⟩ : syracuseStep 10231703 = 15347555) B15347555
theorem B6821135 : Blo 2127435 6821135 := bstep (se 1 (by rfl) ⟨5115851, by rfl⟩ : syracuseStep 6821135 = 10231703) B10231703
theorem B4547423 : Blo 2127435 4547423 := bstep (se 1 (by rfl) ⟨3410567, by rfl⟩ : syracuseStep 4547423 = 6821135) B6821135
theorem B3031615 : Blo 2127435 3031615 := bstep (se 1 (by rfl) ⟨2273711, by rfl⟩ : syracuseStep 3031615 = 4547423) B4547423
theorem B4042153 : Blo 2127435 4042153 := bstep (se 2 (by rfl) ⟨1515807, by rfl⟩ : syracuseStep 4042153 = 3031615) B3031615
theorem B5389537 : Blo 2127435 5389537 := bstep (se 2 (by rfl) ⟨2021076, by rfl⟩ : syracuseStep 5389537 = 4042153) B4042153
theorem B7186049 : Blo 2127435 7186049 := bstep (se 2 (by rfl) ⟨2694768, by rfl⟩ : syracuseStep 7186049 = 5389537) B5389537
theorem B4790699 : Blo 2127435 4790699 := bstep (se 1 (by rfl) ⟨3593024, by rfl⟩ : syracuseStep 4790699 = 7186049) B7186049
theorem B3193799 : Blo 2127435 3193799 := bstep (se 1 (by rfl) ⟨2395349, by rfl⟩ : syracuseStep 3193799 = 4790699) B4790699
theorem B2129199 : Blo 2127435 2129199 := bstep (se 1 (by rfl) ⟨1596899, by rfl⟩ : syracuseStep 2129199 = 3193799) B3193799
theorem B3193805 : Blo 2127435 3193805 := bbase (se 3 (by rfl) ⟨598838, by rfl⟩ : syracuseStep 3193805 = 1197677) (by norm_num)
theorem B2129203 : Blo 2127435 2129203 := bstep (se 1 (by rfl) ⟨1596902, by rfl⟩ : syracuseStep 2129203 = 3193805) B3193805
theorem B4790717 : Blo 2127435 4790717 := bbase (se 3 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 4790717 = 1796519) (by norm_num)
theorem B3193811 : Blo 2127435 3193811 := bstep (se 1 (by rfl) ⟨2395358, by rfl⟩ : syracuseStep 3193811 = 4790717) B4790717
theorem B2129207 : Blo 2127435 2129207 := bstep (se 1 (by rfl) ⟨1596905, by rfl⟩ : syracuseStep 2129207 = 3193811) B3193811
theorem B3593045 : Blo 2127435 3593045 := bbase (se 9 (by rfl) ⟨10526, by rfl⟩ : syracuseStep 3593045 = 21053) (by norm_num)
theorem B2395363 : Blo 2127435 2395363 := bstep (se 1 (by rfl) ⟨1796522, by rfl⟩ : syracuseStep 2395363 = 3593045) B3593045
theorem B3193817 : Blo 2127435 3193817 := bstep (se 2 (by rfl) ⟨1197681, by rfl⟩ : syracuseStep 3193817 = 2395363) B2395363
theorem B2129211 : Blo 2127435 2129211 := bstep (se 1 (by rfl) ⟨1596908, by rfl⟩ : syracuseStep 2129211 = 3193817) B3193817
theorem B3836917 : Blo 2127435 3836917 := bbase (se 5 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 3836917 = 359711) (by norm_num)
theorem B5115889 : Blo 2127435 5115889 := bstep (se 2 (by rfl) ⟨1918458, by rfl⟩ : syracuseStep 5115889 = 3836917) B3836917
theorem B6821185 : Blo 2127435 6821185 := bstep (se 2 (by rfl) ⟨2557944, by rfl⟩ : syracuseStep 6821185 = 5115889) B5115889
theorem B9094913 : Blo 2127435 9094913 := bstep (se 2 (by rfl) ⟨3410592, by rfl⟩ : syracuseStep 9094913 = 6821185) B6821185
theorem B6063275 : Blo 2127435 6063275 := bstep (se 1 (by rfl) ⟨4547456, by rfl⟩ : syracuseStep 6063275 = 9094913) B9094913
theorem B16168733 : Blo 2127435 16168733 := bstep (se 3 (by rfl) ⟨3031637, by rfl⟩ : syracuseStep 16168733 = 6063275) B6063275
theorem B10779155 : Blo 2127435 10779155 := bstep (se 1 (by rfl) ⟨8084366, by rfl⟩ : syracuseStep 10779155 = 16168733) B16168733
theorem B7186103 : Blo 2127435 7186103 := bstep (se 1 (by rfl) ⟨5389577, by rfl⟩ : syracuseStep 7186103 = 10779155) B10779155
theorem B4790735 : Blo 2127435 4790735 := bstep (se 1 (by rfl) ⟨3593051, by rfl⟩ : syracuseStep 4790735 = 7186103) B7186103
theorem B3193823 : Blo 2127435 3193823 := bstep (se 1 (by rfl) ⟨2395367, by rfl⟩ : syracuseStep 3193823 = 4790735) B4790735
theorem B2129215 : Blo 2127435 2129215 := bstep (se 1 (by rfl) ⟨1596911, by rfl⟩ : syracuseStep 2129215 = 3193823) B3193823
theorem B3193829 : Blo 2127435 3193829 := bbase (se 4 (by rfl) ⟨299421, by rfl⟩ : syracuseStep 3193829 = 598843) (by norm_num)
theorem B2129219 : Blo 2127435 2129219 := bstep (se 1 (by rfl) ⟨1596914, by rfl⟩ : syracuseStep 2129219 = 3193829) B3193829
theorem B9094949 : Blo 2127435 9094949 := bbase (se 4 (by rfl) ⟨852651, by rfl⟩ : syracuseStep 9094949 = 1705303) (by norm_num)
theorem B6063299 : Blo 2127435 6063299 := bstep (se 1 (by rfl) ⟨4547474, by rfl⟩ : syracuseStep 6063299 = 9094949) B9094949
theorem B4042199 : Blo 2127435 4042199 := bstep (se 1 (by rfl) ⟨3031649, by rfl⟩ : syracuseStep 4042199 = 6063299) B6063299
theorem B2694799 : Blo 2127435 2694799 := bstep (se 1 (by rfl) ⟨2021099, by rfl⟩ : syracuseStep 2694799 = 4042199) B4042199
theorem B3593065 : Blo 2127435 3593065 := bstep (se 2 (by rfl) ⟨1347399, by rfl⟩ : syracuseStep 3593065 = 2694799) B2694799
theorem B4790753 : Blo 2127435 4790753 := bstep (se 2 (by rfl) ⟨1796532, by rfl⟩ : syracuseStep 4790753 = 3593065) B3593065
theorem B3193835 : Blo 2127435 3193835 := bstep (se 1 (by rfl) ⟨2395376, by rfl⟩ : syracuseStep 3193835 = 4790753) B4790753
theorem B2129223 : Blo 2127435 2129223 := bstep (se 1 (by rfl) ⟨1596917, by rfl⟩ : syracuseStep 2129223 = 3193835) B3193835
theorem B2395381 : Blo 2127435 2395381 := bbase (se 5 (by rfl) ⟨112283, by rfl⟩ : syracuseStep 2395381 = 224567) (by norm_num)
theorem B3193841 : Blo 2127435 3193841 := bstep (se 2 (by rfl) ⟨1197690, by rfl⟩ : syracuseStep 3193841 = 2395381) B2395381
theorem B2129227 : Blo 2127435 2129227 := bstep (se 1 (by rfl) ⟨1596920, by rfl⟩ : syracuseStep 2129227 = 3193841) B3193841
theorem B2694809 : Blo 2127435 2694809 := bbase (se 2 (by rfl) ⟨1010553, by rfl⟩ : syracuseStep 2694809 = 2021107) (by norm_num)
theorem B7186157 : Blo 2127435 7186157 := bstep (se 3 (by rfl) ⟨1347404, by rfl⟩ : syracuseStep 7186157 = 2694809) B2694809
theorem B4790771 : Blo 2127435 4790771 := bstep (se 1 (by rfl) ⟨3593078, by rfl⟩ : syracuseStep 4790771 = 7186157) B7186157
theorem B3193847 : Blo 2127435 3193847 := bstep (se 1 (by rfl) ⟨2395385, by rfl⟩ : syracuseStep 3193847 = 4790771) B4790771
theorem B2129231 : Blo 2127435 2129231 := bstep (se 1 (by rfl) ⟨1596923, by rfl⟩ : syracuseStep 2129231 = 3193847) B3193847
theorem B3193853 : Blo 2127435 3193853 := bbase (se 3 (by rfl) ⟨598847, by rfl⟩ : syracuseStep 3193853 = 1197695) (by norm_num)
theorem B2129235 : Blo 2127435 2129235 := bstep (se 1 (by rfl) ⟨1596926, by rfl⟩ : syracuseStep 2129235 = 3193853) B3193853
theorem B4790789 : Blo 2127435 4790789 := bbase (se 4 (by rfl) ⟨449136, by rfl⟩ : syracuseStep 4790789 = 898273) (by norm_num)
theorem B3193859 : Blo 2127435 3193859 := bstep (se 1 (by rfl) ⟨2395394, by rfl⟩ : syracuseStep 3193859 = 4790789) B4790789
theorem B2129239 : Blo 2127435 2129239 := bstep (se 1 (by rfl) ⟨1596929, by rfl⟩ : syracuseStep 2129239 = 3193859) B3193859
theorem B4042237 : Blo 2127435 4042237 := bbase (se 3 (by rfl) ⟨757919, by rfl⟩ : syracuseStep 4042237 = 1515839) (by norm_num)
theorem B5389649 : Blo 2127435 5389649 := bstep (se 2 (by rfl) ⟨2021118, by rfl⟩ : syracuseStep 5389649 = 4042237) B4042237
theorem B3593099 : Blo 2127435 3593099 := bstep (se 1 (by rfl) ⟨2694824, by rfl⟩ : syracuseStep 3593099 = 5389649) B5389649
theorem B2395399 : Blo 2127435 2395399 := bstep (se 1 (by rfl) ⟨1796549, by rfl⟩ : syracuseStep 2395399 = 3593099) B3593099
theorem B3193865 : Blo 2127435 3193865 := bstep (se 2 (by rfl) ⟨1197699, by rfl⟩ : syracuseStep 3193865 = 2395399) B2395399
theorem B2129243 : Blo 2127435 2129243 := bstep (se 1 (by rfl) ⟨1596932, by rfl⟩ : syracuseStep 2129243 = 3193865) B3193865
theorem B10779317 : Blo 2127435 10779317 := bbase (se 5 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 10779317 = 1010561) (by norm_num)
theorem B7186211 : Blo 2127435 7186211 := bstep (se 1 (by rfl) ⟨5389658, by rfl⟩ : syracuseStep 7186211 = 10779317) B10779317
theorem B4790807 : Blo 2127435 4790807 := bstep (se 1 (by rfl) ⟨3593105, by rfl⟩ : syracuseStep 4790807 = 7186211) B7186211
theorem B3193871 : Blo 2127435 3193871 := bstep (se 1 (by rfl) ⟨2395403, by rfl⟩ : syracuseStep 3193871 = 4790807) B4790807
theorem B2129247 : Blo 2127435 2129247 := bstep (se 1 (by rfl) ⟨1596935, by rfl⟩ : syracuseStep 2129247 = 3193871) B3193871
theorem B3193877 : Blo 2127435 3193877 := bbase (se 6 (by rfl) ⟨74856, by rfl⟩ : syracuseStep 3193877 = 149713) (by norm_num)
theorem B2129251 : Blo 2127435 2129251 := bstep (se 1 (by rfl) ⟨1596938, by rfl⟩ : syracuseStep 2129251 = 3193877) B3193877
theorem B3836989 : Blo 2127435 3836989 := bbase (se 3 (by rfl) ⟨719435, by rfl⟩ : syracuseStep 3836989 = 1438871) (by norm_num)
theorem B20463941 : Blo 2127435 20463941 := bstep (se 4 (by rfl) ⟨1918494, by rfl⟩ : syracuseStep 20463941 = 3836989) B3836989
theorem B13642627 : Blo 2127435 13642627 := bstep (se 1 (by rfl) ⟨10231970, by rfl⟩ : syracuseStep 13642627 = 20463941) B20463941
theorem B18190169 : Blo 2127435 18190169 := bstep (se 2 (by rfl) ⟨6821313, by rfl⟩ : syracuseStep 18190169 = 13642627) B13642627
theorem B12126779 : Blo 2127435 12126779 := bstep (se 1 (by rfl) ⟨9095084, by rfl⟩ : syracuseStep 12126779 = 18190169) B18190169
theorem B8084519 : Blo 2127435 8084519 := bstep (se 1 (by rfl) ⟨6063389, by rfl⟩ : syracuseStep 8084519 = 12126779) B12126779
theorem B5389679 : Blo 2127435 5389679 := bstep (se 1 (by rfl) ⟨4042259, by rfl⟩ : syracuseStep 5389679 = 8084519) B8084519
theorem B3593119 : Blo 2127435 3593119 := bstep (se 1 (by rfl) ⟨2694839, by rfl⟩ : syracuseStep 3593119 = 5389679) B5389679
theorem B4790825 : Blo 2127435 4790825 := bstep (se 2 (by rfl) ⟨1796559, by rfl⟩ : syracuseStep 4790825 = 3593119) B3593119
theorem B3193883 : Blo 2127435 3193883 := bstep (se 1 (by rfl) ⟨2395412, by rfl⟩ : syracuseStep 3193883 = 4790825) B4790825
theorem B2129255 : Blo 2127435 2129255 := bstep (se 1 (by rfl) ⟨1596941, by rfl⟩ : syracuseStep 2129255 = 3193883) B3193883
theorem B2395417 : Blo 2127435 2395417 := bbase (se 2 (by rfl) ⟨898281, by rfl⟩ : syracuseStep 2395417 = 1796563) (by norm_num)
theorem B3193889 : Blo 2127435 3193889 := bstep (se 2 (by rfl) ⟨1197708, by rfl⟩ : syracuseStep 3193889 = 2395417) B2395417
theorem B2129259 : Blo 2127435 2129259 := bstep (se 1 (by rfl) ⟨1596944, by rfl⟩ : syracuseStep 2129259 = 3193889) B3193889
theorem B8084549 : Blo 2127435 8084549 := bbase (se 4 (by rfl) ⟨757926, by rfl⟩ : syracuseStep 8084549 = 1515853) (by norm_num)
theorem B5389699 : Blo 2127435 5389699 := bstep (se 1 (by rfl) ⟨4042274, by rfl⟩ : syracuseStep 5389699 = 8084549) B8084549
theorem B7186265 : Blo 2127435 7186265 := bstep (se 2 (by rfl) ⟨2694849, by rfl⟩ : syracuseStep 7186265 = 5389699) B5389699
theorem B4790843 : Blo 2127435 4790843 := bstep (se 1 (by rfl) ⟨3593132, by rfl⟩ : syracuseStep 4790843 = 7186265) B7186265
theorem B3193895 : Blo 2127435 3193895 := bstep (se 1 (by rfl) ⟨2395421, by rfl⟩ : syracuseStep 3193895 = 4790843) B4790843
theorem B2129263 : Blo 2127435 2129263 := bstep (se 1 (by rfl) ⟨1596947, by rfl⟩ : syracuseStep 2129263 = 3193895) B3193895
theorem B3193901 : Blo 2127435 3193901 := bbase (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) (by norm_num)
theorem B2129267 : Blo 2127435 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B4790861 : Blo 2127435 4790861 := bbase (se 3 (by rfl) ⟨898286, by rfl⟩ : syracuseStep 4790861 = 1796573) (by norm_num)
theorem B3193907 : Blo 2127435 3193907 := bstep (se 1 (by rfl) ⟨2395430, by rfl⟩ : syracuseStep 3193907 = 4790861) B4790861
theorem B2129271 : Blo 2127435 2129271 := bstep (se 1 (by rfl) ⟨1596953, by rfl⟩ : syracuseStep 2129271 = 3193907) B3193907
theorem B2694865 : Blo 2127435 2694865 := bbase (se 2 (by rfl) ⟨1010574, by rfl⟩ : syracuseStep 2694865 = 2021149) (by norm_num)
theorem B3593153 : Blo 2127435 3593153 := bstep (se 2 (by rfl) ⟨1347432, by rfl⟩ : syracuseStep 3593153 = 2694865) B2694865
theorem B2395435 : Blo 2127435 2395435 := bstep (se 1 (by rfl) ⟨1796576, by rfl⟩ : syracuseStep 2395435 = 3593153) B3593153
theorem B3193913 : Blo 2127435 3193913 := bstep (se 2 (by rfl) ⟨1197717, by rfl⟩ : syracuseStep 3193913 = 2395435) B2395435
theorem B2129275 : Blo 2127435 2129275 := bstep (se 1 (by rfl) ⟨1596956, by rfl⟩ : syracuseStep 2129275 = 3193913) B3193913
theorem B2304821 : Blo 2127435 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B6146189 : Blo 2127435 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B4097459 : Blo 2127435 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B2731639 : Blo 2127435 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B3642185 : Blo 2127435 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B2428123 : Blo 2127435 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B3237497 : Blo 2127435 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B2158331 : Blo 2127435 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B5755549 : Blo 2127435 5755549 := bstep (se 3 (by rfl) ⟨1079165, by rfl⟩ : syracuseStep 5755549 = 2158331) B2158331
theorem B7674065 : Blo 2127435 7674065 := bstep (se 2 (by rfl) ⟨2877774, by rfl⟩ : syracuseStep 7674065 = 5755549) B5755549
theorem B5116043 : Blo 2127435 5116043 := bstep (se 1 (by rfl) ⟨3837032, by rfl⟩ : syracuseStep 5116043 = 7674065) B7674065
theorem B3410695 : Blo 2127435 3410695 := bstep (se 1 (by rfl) ⟨2558021, by rfl⟩ : syracuseStep 3410695 = 5116043) B5116043
theorem B4547593 : Blo 2127435 4547593 := bstep (se 2 (by rfl) ⟨1705347, by rfl⟩ : syracuseStep 4547593 = 3410695) B3410695
theorem B24253829 : Blo 2127435 24253829 := bstep (se 4 (by rfl) ⟨2273796, by rfl⟩ : syracuseStep 24253829 = 4547593) B4547593
theorem B16169219 : Blo 2127435 16169219 := bstep (se 1 (by rfl) ⟨12126914, by rfl⟩ : syracuseStep 16169219 = 24253829) B24253829
theorem B10779479 : Blo 2127435 10779479 := bstep (se 1 (by rfl) ⟨8084609, by rfl⟩ : syracuseStep 10779479 = 16169219) B16169219
theorem B7186319 : Blo 2127435 7186319 := bstep (se 1 (by rfl) ⟨5389739, by rfl⟩ : syracuseStep 7186319 = 10779479) B10779479
theorem B4790879 : Blo 2127435 4790879 := bstep (se 1 (by rfl) ⟨3593159, by rfl⟩ : syracuseStep 4790879 = 7186319) B7186319
theorem B3193919 : Blo 2127435 3193919 := bstep (se 1 (by rfl) ⟨2395439, by rfl⟩ : syracuseStep 3193919 = 4790879) B4790879
theorem B2129279 : Blo 2127435 2129279 := bstep (se 1 (by rfl) ⟨1596959, by rfl⟩ : syracuseStep 2129279 = 3193919) B3193919
theorem B3193925 : Blo 2127435 3193925 := bbase (se 4 (by rfl) ⟨299430, by rfl⟩ : syracuseStep 3193925 = 598861) (by norm_num)
theorem B2129283 : Blo 2127435 2129283 := bstep (se 1 (by rfl) ⟨1596962, by rfl⟩ : syracuseStep 2129283 = 3193925) B3193925
theorem B3593173 : Blo 2127435 3593173 := bbase (se 7 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 3593173 = 84215) (by norm_num)
theorem B4790897 : Blo 2127435 4790897 := bstep (se 2 (by rfl) ⟨1796586, by rfl⟩ : syracuseStep 4790897 = 3593173) B3593173
theorem B3193931 : Blo 2127435 3193931 := bstep (se 1 (by rfl) ⟨2395448, by rfl⟩ : syracuseStep 3193931 = 4790897) B4790897
theorem B2129287 : Blo 2127435 2129287 := bstep (se 1 (by rfl) ⟨1596965, by rfl⟩ : syracuseStep 2129287 = 3193931) B3193931
theorem B2395453 : Blo 2127435 2395453 := bbase (se 3 (by rfl) ⟨449147, by rfl⟩ : syracuseStep 2395453 = 898295) (by norm_num)
theorem B3193937 : Blo 2127435 3193937 := bstep (se 2 (by rfl) ⟨1197726, by rfl⟩ : syracuseStep 3193937 = 2395453) B2395453
theorem B2129291 : Blo 2127435 2129291 := bstep (se 1 (by rfl) ⟨1596968, by rfl⟩ : syracuseStep 2129291 = 3193937) B3193937
theorem B7186373 : Blo 2127435 7186373 := bbase (se 4 (by rfl) ⟨673722, by rfl⟩ : syracuseStep 7186373 = 1347445) (by norm_num)
theorem B4790915 : Blo 2127435 4790915 := bstep (se 1 (by rfl) ⟨3593186, by rfl⟩ : syracuseStep 4790915 = 7186373) B7186373
theorem B3193943 : Blo 2127435 3193943 := bstep (se 1 (by rfl) ⟨2395457, by rfl⟩ : syracuseStep 3193943 = 4790915) B4790915
theorem B2129295 : Blo 2127435 2129295 := bstep (se 1 (by rfl) ⟨1596971, by rfl⟩ : syracuseStep 2129295 = 3193943) B3193943
theorem B3193949 : Blo 2127435 3193949 := bbase (se 3 (by rfl) ⟨598865, by rfl⟩ : syracuseStep 3193949 = 1197731) (by norm_num)
theorem B2129299 : Blo 2127435 2129299 := bstep (se 1 (by rfl) ⟨1596974, by rfl⟩ : syracuseStep 2129299 = 3193949) B3193949
theorem B4790933 : Blo 2127435 4790933 := bbase (se 6 (by rfl) ⟨112287, by rfl⟩ : syracuseStep 4790933 = 224575) (by norm_num)
theorem B3193955 : Blo 2127435 3193955 := bstep (se 1 (by rfl) ⟨2395466, by rfl⟩ : syracuseStep 3193955 = 4790933) B4790933
theorem B2129303 : Blo 2127435 2129303 := bstep (se 1 (by rfl) ⟨1596977, by rfl⟩ : syracuseStep 2129303 = 3193955) B3193955
theorem B3410741 : Blo 2127435 3410741 := bbase (se 5 (by rfl) ⟨159878, by rfl⟩ : syracuseStep 3410741 = 319757) (by norm_num)
theorem B2273827 : Blo 2127435 2273827 := bstep (se 1 (by rfl) ⟨1705370, by rfl⟩ : syracuseStep 2273827 = 3410741) B3410741
theorem B3031769 : Blo 2127435 3031769 := bstep (se 2 (by rfl) ⟨1136913, by rfl⟩ : syracuseStep 3031769 = 2273827) B2273827
theorem B8084717 : Blo 2127435 8084717 := bstep (se 3 (by rfl) ⟨1515884, by rfl⟩ : syracuseStep 8084717 = 3031769) B3031769
theorem B5389811 : Blo 2127435 5389811 := bstep (se 1 (by rfl) ⟨4042358, by rfl⟩ : syracuseStep 5389811 = 8084717) B8084717
theorem B3593207 : Blo 2127435 3593207 := bstep (se 1 (by rfl) ⟨2694905, by rfl⟩ : syracuseStep 3593207 = 5389811) B5389811
theorem B2395471 : Blo 2127435 2395471 := bstep (se 1 (by rfl) ⟨1796603, by rfl⟩ : syracuseStep 2395471 = 3593207) B3593207
theorem B3193961 : Blo 2127435 3193961 := bstep (se 2 (by rfl) ⟨1197735, by rfl⟩ : syracuseStep 3193961 = 2395471) B2395471
theorem B2129307 : Blo 2127435 2129307 := bstep (se 1 (by rfl) ⟨1596980, by rfl⟩ : syracuseStep 2129307 = 3193961) B3193961
theorem B4856317 : Blo 2127435 4856317 := bbase (se 3 (by rfl) ⟨910559, by rfl⟩ : syracuseStep 4856317 = 1821119) (by norm_num)
theorem B25900357 : Blo 2127435 25900357 := bstep (se 4 (by rfl) ⟨2428158, by rfl⟩ : syracuseStep 25900357 = 4856317) B4856317
theorem B34533809 : Blo 2127435 34533809 := bstep (se 2 (by rfl) ⟨12950178, by rfl⟩ : syracuseStep 34533809 = 25900357) B25900357
theorem B23022539 : Blo 2127435 23022539 := bstep (se 1 (by rfl) ⟨17266904, by rfl⟩ : syracuseStep 23022539 = 34533809) B34533809
theorem B15348359 : Blo 2127435 15348359 := bstep (se 1 (by rfl) ⟨11511269, by rfl⟩ : syracuseStep 15348359 = 23022539) B23022539
theorem B10232239 : Blo 2127435 10232239 := bstep (se 1 (by rfl) ⟨7674179, by rfl⟩ : syracuseStep 10232239 = 15348359) B15348359
theorem B13642985 : Blo 2127435 13642985 := bstep (se 2 (by rfl) ⟨5116119, by rfl⟩ : syracuseStep 13642985 = 10232239) B10232239
theorem B9095323 : Blo 2127435 9095323 := bstep (se 1 (by rfl) ⟨6821492, by rfl⟩ : syracuseStep 9095323 = 13642985) B13642985
theorem B12127097 : Blo 2127435 12127097 := bstep (se 2 (by rfl) ⟨4547661, by rfl⟩ : syracuseStep 12127097 = 9095323) B9095323
theorem B8084731 : Blo 2127435 8084731 := bstep (se 1 (by rfl) ⟨6063548, by rfl⟩ : syracuseStep 8084731 = 12127097) B12127097
theorem B10779641 : Blo 2127435 10779641 := bstep (se 2 (by rfl) ⟨4042365, by rfl⟩ : syracuseStep 10779641 = 8084731) B8084731
theorem B7186427 : Blo 2127435 7186427 := bstep (se 1 (by rfl) ⟨5389820, by rfl⟩ : syracuseStep 7186427 = 10779641) B10779641
theorem B4790951 : Blo 2127435 4790951 := bstep (se 1 (by rfl) ⟨3593213, by rfl⟩ : syracuseStep 4790951 = 7186427) B7186427
theorem B3193967 : Blo 2127435 3193967 := bstep (se 1 (by rfl) ⟨2395475, by rfl⟩ : syracuseStep 3193967 = 4790951) B4790951
theorem B2129311 : Blo 2127435 2129311 := bstep (se 1 (by rfl) ⟨1596983, by rfl⟩ : syracuseStep 2129311 = 3193967) B3193967
theorem B3193973 : Blo 2127435 3193973 := bbase (se 5 (by rfl) ⟨149717, by rfl⟩ : syracuseStep 3193973 = 299435) (by norm_num)
theorem B2129315 : Blo 2127435 2129315 := bstep (se 1 (by rfl) ⟨1596986, by rfl⟩ : syracuseStep 2129315 = 3193973) B3193973
theorem B4042381 : Blo 2127435 4042381 := bbase (se 3 (by rfl) ⟨757946, by rfl⟩ : syracuseStep 4042381 = 1515893) (by norm_num)
theorem B5389841 : Blo 2127435 5389841 := bstep (se 2 (by rfl) ⟨2021190, by rfl⟩ : syracuseStep 5389841 = 4042381) B4042381
theorem B3593227 : Blo 2127435 3593227 := bstep (se 1 (by rfl) ⟨2694920, by rfl⟩ : syracuseStep 3593227 = 5389841) B5389841
theorem B4790969 : Blo 2127435 4790969 := bstep (se 2 (by rfl) ⟨1796613, by rfl⟩ : syracuseStep 4790969 = 3593227) B3593227
theorem B3193979 : Blo 2127435 3193979 := bstep (se 1 (by rfl) ⟨2395484, by rfl⟩ : syracuseStep 3193979 = 4790969) B4790969
theorem B2129319 : Blo 2127435 2129319 := bstep (se 1 (by rfl) ⟨1596989, by rfl⟩ : syracuseStep 2129319 = 3193979) B3193979
theorem B2395489 : Blo 2127435 2395489 := bbase (se 2 (by rfl) ⟨898308, by rfl⟩ : syracuseStep 2395489 = 1796617) (by norm_num)
theorem B3193985 : Blo 2127435 3193985 := bstep (se 2 (by rfl) ⟨1197744, by rfl⟩ : syracuseStep 3193985 = 2395489) B2395489
theorem B2129323 : Blo 2127435 2129323 := bstep (se 1 (by rfl) ⟨1596992, by rfl⟩ : syracuseStep 2129323 = 3193985) B3193985
theorem B5389861 : Blo 2127435 5389861 := bbase (se 4 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 5389861 = 1010599) (by norm_num)
theorem B7186481 : Blo 2127435 7186481 := bstep (se 2 (by rfl) ⟨2694930, by rfl⟩ : syracuseStep 7186481 = 5389861) B5389861
theorem B4790987 : Blo 2127435 4790987 := bstep (se 1 (by rfl) ⟨3593240, by rfl⟩ : syracuseStep 4790987 = 7186481) B7186481
theorem B3193991 : Blo 2127435 3193991 := bstep (se 1 (by rfl) ⟨2395493, by rfl⟩ : syracuseStep 3193991 = 4790987) B4790987
theorem B2129327 : Blo 2127435 2129327 := bstep (se 1 (by rfl) ⟨1596995, by rfl⟩ : syracuseStep 2129327 = 3193991) B3193991
theorem B3193997 : Blo 2127435 3193997 := bbase (se 3 (by rfl) ⟨598874, by rfl⟩ : syracuseStep 3193997 = 1197749) (by norm_num)
theorem B2129331 : Blo 2127435 2129331 := bstep (se 1 (by rfl) ⟨1596998, by rfl⟩ : syracuseStep 2129331 = 3193997) B3193997
theorem B4791005 : Blo 2127435 4791005 := bbase (se 3 (by rfl) ⟨898313, by rfl⟩ : syracuseStep 4791005 = 1796627) (by norm_num)
theorem B3194003 : Blo 2127435 3194003 := bstep (se 1 (by rfl) ⟨2395502, by rfl⟩ : syracuseStep 3194003 = 4791005) B4791005
theorem B2129335 : Blo 2127435 2129335 := bstep (se 1 (by rfl) ⟨1597001, by rfl⟩ : syracuseStep 2129335 = 3194003) B3194003
theorem B3593261 : Blo 2127435 3593261 := bbase (se 3 (by rfl) ⟨673736, by rfl⟩ : syracuseStep 3593261 = 1347473) (by norm_num)
theorem B2395507 : Blo 2127435 2395507 := bstep (se 1 (by rfl) ⟨1796630, by rfl⟩ : syracuseStep 2395507 = 3593261) B3593261
theorem B3194009 : Blo 2127435 3194009 := bstep (se 2 (by rfl) ⟨1197753, by rfl⟩ : syracuseStep 3194009 = 2395507) B2395507
theorem B2129339 : Blo 2127435 2129339 := bstep (se 1 (by rfl) ⟨1597004, by rfl⟩ : syracuseStep 2129339 = 3194009) B3194009
theorem B3642293 : Blo 2127435 3642293 := bbase (se 5 (by rfl) ⟨170732, by rfl⟩ : syracuseStep 3642293 = 341465) (by norm_num)
theorem B2428195 : Blo 2127435 2428195 := bstep (se 1 (by rfl) ⟨1821146, by rfl⟩ : syracuseStep 2428195 = 3642293) B3642293
theorem B3237593 : Blo 2127435 3237593 := bstep (se 2 (by rfl) ⟨1214097, by rfl⟩ : syracuseStep 3237593 = 2428195) B2428195
theorem B34534325 : Blo 2127435 34534325 := bstep (se 5 (by rfl) ⟨1618796, by rfl⟩ : syracuseStep 34534325 = 3237593) B3237593
theorem B23022883 : Blo 2127435 23022883 := bstep (se 1 (by rfl) ⟨17267162, by rfl⟩ : syracuseStep 23022883 = 34534325) B34534325
theorem B30697177 : Blo 2127435 30697177 := bstep (se 2 (by rfl) ⟨11511441, by rfl⟩ : syracuseStep 30697177 = 23022883) B23022883
theorem B40929569 : Blo 2127435 40929569 := bstep (se 2 (by rfl) ⟨15348588, by rfl⟩ : syracuseStep 40929569 = 30697177) B30697177
theorem B27286379 : Blo 2127435 27286379 := bstep (se 1 (by rfl) ⟨20464784, by rfl⟩ : syracuseStep 27286379 = 40929569) B40929569
theorem B18190919 : Blo 2127435 18190919 := bstep (se 1 (by rfl) ⟨13643189, by rfl⟩ : syracuseStep 18190919 = 27286379) B27286379
theorem B12127279 : Blo 2127435 12127279 := bstep (se 1 (by rfl) ⟨9095459, by rfl⟩ : syracuseStep 12127279 = 18190919) B18190919
theorem B16169705 : Blo 2127435 16169705 := bstep (se 2 (by rfl) ⟨6063639, by rfl⟩ : syracuseStep 16169705 = 12127279) B12127279
theorem B10779803 : Blo 2127435 10779803 := bstep (se 1 (by rfl) ⟨8084852, by rfl⟩ : syracuseStep 10779803 = 16169705) B16169705
theorem B7186535 : Blo 2127435 7186535 := bstep (se 1 (by rfl) ⟨5389901, by rfl⟩ : syracuseStep 7186535 = 10779803) B10779803
theorem B4791023 : Blo 2127435 4791023 := bstep (se 1 (by rfl) ⟨3593267, by rfl⟩ : syracuseStep 4791023 = 7186535) B7186535
theorem B3194015 : Blo 2127435 3194015 := bstep (se 1 (by rfl) ⟨2395511, by rfl⟩ : syracuseStep 3194015 = 4791023) B4791023
theorem B2129343 : Blo 2127435 2129343 := bstep (se 1 (by rfl) ⟨1597007, by rfl⟩ : syracuseStep 2129343 = 3194015) B3194015
theorem B3194021 : Blo 2127435 3194021 := bbase (se 4 (by rfl) ⟨299439, by rfl⟩ : syracuseStep 3194021 = 598879) (by norm_num)
theorem B2129347 : Blo 2127435 2129347 := bstep (se 1 (by rfl) ⟨1597010, by rfl⟩ : syracuseStep 2129347 = 3194021) B3194021
theorem B2694961 : Blo 2127435 2694961 := bbase (se 2 (by rfl) ⟨1010610, by rfl⟩ : syracuseStep 2694961 = 2021221) (by norm_num)
theorem B3593281 : Blo 2127435 3593281 := bstep (se 2 (by rfl) ⟨1347480, by rfl⟩ : syracuseStep 3593281 = 2694961) B2694961
theorem B4791041 : Blo 2127435 4791041 := bstep (se 2 (by rfl) ⟨1796640, by rfl⟩ : syracuseStep 4791041 = 3593281) B3593281
theorem B3194027 : Blo 2127435 3194027 := bstep (se 1 (by rfl) ⟨2395520, by rfl⟩ : syracuseStep 3194027 = 4791041) B4791041
theorem B2129351 : Blo 2127435 2129351 := bstep (se 1 (by rfl) ⟨1597013, by rfl⟩ : syracuseStep 2129351 = 3194027) B3194027
theorem B2395525 : Blo 2127435 2395525 := bbase (se 4 (by rfl) ⟨224580, by rfl⟩ : syracuseStep 2395525 = 449161) (by norm_num)
theorem B3194033 : Blo 2127435 3194033 := bstep (se 2 (by rfl) ⟨1197762, by rfl⟩ : syracuseStep 3194033 = 2395525) B2395525
theorem B2129355 : Blo 2127435 2129355 := bstep (se 1 (by rfl) ⟨1597016, by rfl⟩ : syracuseStep 2129355 = 3194033) B3194033
theorem B4547765 : Blo 2127435 4547765 := bbase (se 5 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 4547765 = 426353) (by norm_num)
theorem B3031843 : Blo 2127435 3031843 := bstep (se 1 (by rfl) ⟨2273882, by rfl⟩ : syracuseStep 3031843 = 4547765) B4547765
theorem B4042457 : Blo 2127435 4042457 := bstep (se 2 (by rfl) ⟨1515921, by rfl⟩ : syracuseStep 4042457 = 3031843) B3031843
theorem B2694971 : Blo 2127435 2694971 := bstep (se 1 (by rfl) ⟨2021228, by rfl⟩ : syracuseStep 2694971 = 4042457) B4042457
theorem B7186589 : Blo 2127435 7186589 := bstep (se 3 (by rfl) ⟨1347485, by rfl⟩ : syracuseStep 7186589 = 2694971) B2694971
theorem B4791059 : Blo 2127435 4791059 := bstep (se 1 (by rfl) ⟨3593294, by rfl⟩ : syracuseStep 4791059 = 7186589) B7186589
theorem B3194039 : Blo 2127435 3194039 := bstep (se 1 (by rfl) ⟨2395529, by rfl⟩ : syracuseStep 3194039 = 4791059) B4791059
theorem B2129359 : Blo 2127435 2129359 := bstep (se 1 (by rfl) ⟨1597019, by rfl⟩ : syracuseStep 2129359 = 3194039) B3194039
theorem B3194045 : Blo 2127435 3194045 := bbase (se 3 (by rfl) ⟨598883, by rfl⟩ : syracuseStep 3194045 = 1197767) (by norm_num)
theorem B2129363 : Blo 2127435 2129363 := bstep (se 1 (by rfl) ⟨1597022, by rfl⟩ : syracuseStep 2129363 = 3194045) B3194045
theorem B4791077 : Blo 2127435 4791077 := bbase (se 4 (by rfl) ⟨449163, by rfl⟩ : syracuseStep 4791077 = 898327) (by norm_num)
theorem B3194051 : Blo 2127435 3194051 := bstep (se 1 (by rfl) ⟨2395538, by rfl⟩ : syracuseStep 3194051 = 4791077) B4791077
theorem B2129367 : Blo 2127435 2129367 := bstep (se 1 (by rfl) ⟨1597025, by rfl⟩ : syracuseStep 2129367 = 3194051) B3194051
theorem B5389973 : Blo 2127435 5389973 := bbase (se 6 (by rfl) ⟨126327, by rfl⟩ : syracuseStep 5389973 = 252655) (by norm_num)
theorem B3593315 : Blo 2127435 3593315 := bstep (se 1 (by rfl) ⟨2694986, by rfl⟩ : syracuseStep 3593315 = 5389973) B5389973
theorem B2395543 : Blo 2127435 2395543 := bstep (se 1 (by rfl) ⟨1796657, by rfl⟩ : syracuseStep 2395543 = 3593315) B3593315
theorem B3194057 : Blo 2127435 3194057 := bstep (se 2 (by rfl) ⟨1197771, by rfl⟩ : syracuseStep 3194057 = 2395543) B2395543
theorem B2129371 : Blo 2127435 2129371 := bstep (se 1 (by rfl) ⟨1597028, by rfl⟩ : syracuseStep 2129371 = 3194057) B3194057
theorem B2558137 : Blo 2127435 2558137 := bbase (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) (by norm_num)
theorem B3410849 : Blo 2127435 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B9095597 : Blo 2127435 9095597 := bstep (se 3 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 9095597 = 3410849) B3410849
theorem B6063731 : Blo 2127435 6063731 := bstep (se 1 (by rfl) ⟨4547798, by rfl⟩ : syracuseStep 6063731 = 9095597) B9095597
theorem B4042487 : Blo 2127435 4042487 := bstep (se 1 (by rfl) ⟨3031865, by rfl⟩ : syracuseStep 4042487 = 6063731) B6063731
theorem B10779965 : Blo 2127435 10779965 := bstep (se 3 (by rfl) ⟨2021243, by rfl⟩ : syracuseStep 10779965 = 4042487) B4042487
theorem B7186643 : Blo 2127435 7186643 := bstep (se 1 (by rfl) ⟨5389982, by rfl⟩ : syracuseStep 7186643 = 10779965) B10779965
theorem B4791095 : Blo 2127435 4791095 := bstep (se 1 (by rfl) ⟨3593321, by rfl⟩ : syracuseStep 4791095 = 7186643) B7186643
theorem B3194063 : Blo 2127435 3194063 := bstep (se 1 (by rfl) ⟨2395547, by rfl⟩ : syracuseStep 3194063 = 4791095) B4791095
theorem B2129375 : Blo 2127435 2129375 := bstep (se 1 (by rfl) ⟨1597031, by rfl⟩ : syracuseStep 2129375 = 3194063) B3194063
theorem B3194069 : Blo 2127435 3194069 := bbase (se 7 (by rfl) ⟨37430, by rfl⟩ : syracuseStep 3194069 = 74861) (by norm_num)
theorem B2129379 : Blo 2127435 2129379 := bstep (se 1 (by rfl) ⟨1597034, by rfl⟩ : syracuseStep 2129379 = 3194069) B3194069
theorem B3031877 : Blo 2127435 3031877 := bbase (se 4 (by rfl) ⟨284238, by rfl⟩ : syracuseStep 3031877 = 568477) (by norm_num)
theorem B8085005 : Blo 2127435 8085005 := bstep (se 3 (by rfl) ⟨1515938, by rfl⟩ : syracuseStep 8085005 = 3031877) B3031877
theorem B5390003 : Blo 2127435 5390003 := bstep (se 1 (by rfl) ⟨4042502, by rfl⟩ : syracuseStep 5390003 = 8085005) B8085005
theorem B3593335 : Blo 2127435 3593335 := bstep (se 1 (by rfl) ⟨2695001, by rfl⟩ : syracuseStep 3593335 = 5390003) B5390003
theorem B4791113 : Blo 2127435 4791113 := bstep (se 2 (by rfl) ⟨1796667, by rfl⟩ : syracuseStep 4791113 = 3593335) B3593335
theorem B3194075 : Blo 2127435 3194075 := bstep (se 1 (by rfl) ⟨2395556, by rfl⟩ : syracuseStep 3194075 = 4791113) B4791113
theorem B2129383 : Blo 2127435 2129383 := bstep (se 1 (by rfl) ⟨1597037, by rfl⟩ : syracuseStep 2129383 = 3194075) B3194075
theorem B2395561 : Blo 2127435 2395561 := bbase (se 2 (by rfl) ⟨898335, by rfl⟩ : syracuseStep 2395561 = 1796671) (by norm_num)
theorem B3194081 : Blo 2127435 3194081 := bstep (se 2 (by rfl) ⟨1197780, by rfl⟩ : syracuseStep 3194081 = 2395561) B2395561
theorem B2129387 : Blo 2127435 2129387 := bstep (se 1 (by rfl) ⟨1597040, by rfl⟩ : syracuseStep 2129387 = 3194081) B3194081
theorem B6821749 : Blo 2127435 6821749 := bbase (se 5 (by rfl) ⟨319769, by rfl⟩ : syracuseStep 6821749 = 639539) (by norm_num)
theorem B9095665 : Blo 2127435 9095665 := bstep (se 2 (by rfl) ⟨3410874, by rfl⟩ : syracuseStep 9095665 = 6821749) B6821749
theorem B12127553 : Blo 2127435 12127553 := bstep (se 2 (by rfl) ⟨4547832, by rfl⟩ : syracuseStep 12127553 = 9095665) B9095665
theorem B8085035 : Blo 2127435 8085035 := bstep (se 1 (by rfl) ⟨6063776, by rfl⟩ : syracuseStep 8085035 = 12127553) B12127553
theorem B5390023 : Blo 2127435 5390023 := bstep (se 1 (by rfl) ⟨4042517, by rfl⟩ : syracuseStep 5390023 = 8085035) B8085035
theorem B7186697 : Blo 2127435 7186697 := bstep (se 2 (by rfl) ⟨2695011, by rfl⟩ : syracuseStep 7186697 = 5390023) B5390023
theorem B4791131 : Blo 2127435 4791131 := bstep (se 1 (by rfl) ⟨3593348, by rfl⟩ : syracuseStep 4791131 = 7186697) B7186697
theorem B3194087 : Blo 2127435 3194087 := bstep (se 1 (by rfl) ⟨2395565, by rfl⟩ : syracuseStep 3194087 = 4791131) B4791131
theorem B2129391 : Blo 2127435 2129391 := bstep (se 1 (by rfl) ⟨1597043, by rfl⟩ : syracuseStep 2129391 = 3194087) B3194087
theorem B3194093 : Blo 2127435 3194093 := bbase (se 3 (by rfl) ⟨598892, by rfl⟩ : syracuseStep 3194093 = 1197785) (by norm_num)
theorem B2129395 : Blo 2127435 2129395 := bstep (se 1 (by rfl) ⟨1597046, by rfl⟩ : syracuseStep 2129395 = 3194093) B3194093
theorem B4791149 : Blo 2127435 4791149 := bbase (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) (by norm_num)
theorem B3194099 : Blo 2127435 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B2129399 : Blo 2127435 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B4042541 : Blo 2127435 4042541 := bbase (se 3 (by rfl) ⟨757976, by rfl⟩ : syracuseStep 4042541 = 1515953) (by norm_num)
theorem B2695027 : Blo 2127435 2695027 := bstep (se 1 (by rfl) ⟨2021270, by rfl⟩ : syracuseStep 2695027 = 4042541) B4042541
theorem B3593369 : Blo 2127435 3593369 := bstep (se 2 (by rfl) ⟨1347513, by rfl⟩ : syracuseStep 3593369 = 2695027) B2695027
theorem B2395579 : Blo 2127435 2395579 := bstep (se 1 (by rfl) ⟨1796684, by rfl⟩ : syracuseStep 2395579 = 3593369) B3593369
theorem B3194105 : Blo 2127435 3194105 := bstep (se 2 (by rfl) ⟨1197789, by rfl⟩ : syracuseStep 3194105 = 2395579) B2395579
theorem B2129403 : Blo 2127435 2129403 := bstep (se 1 (by rfl) ⟨1597052, by rfl⟩ : syracuseStep 2129403 = 3194105) B3194105
theorem B4922797 : Blo 2127435 4922797 := bbase (se 3 (by rfl) ⟨923024, by rfl⟩ : syracuseStep 4922797 = 1846049) (by norm_num)
theorem B6563729 : Blo 2127435 6563729 := bstep (se 2 (by rfl) ⟨2461398, by rfl⟩ : syracuseStep 6563729 = 4922797) B4922797
theorem B4375819 : Blo 2127435 4375819 := bstep (se 1 (by rfl) ⟨3281864, by rfl⟩ : syracuseStep 4375819 = 6563729) B6563729
theorem B5834425 : Blo 2127435 5834425 := bstep (se 2 (by rfl) ⟨2187909, by rfl⟩ : syracuseStep 5834425 = 4375819) B4375819
theorem B7779233 : Blo 2127435 7779233 := bstep (se 2 (by rfl) ⟨2917212, by rfl⟩ : syracuseStep 7779233 = 5834425) B5834425
theorem B5186155 : Blo 2127435 5186155 := bstep (se 1 (by rfl) ⟨3889616, by rfl⟩ : syracuseStep 5186155 = 7779233) B7779233
theorem B6914873 : Blo 2127435 6914873 := bstep (se 2 (by rfl) ⟨2593077, by rfl⟩ : syracuseStep 6914873 = 5186155) B5186155
theorem B4609915 : Blo 2127435 4609915 := bstep (se 1 (by rfl) ⟨3457436, by rfl⟩ : syracuseStep 4609915 = 6914873) B6914873
theorem B24586213 : Blo 2127435 24586213 := bstep (se 4 (by rfl) ⟨2304957, by rfl⟩ : syracuseStep 24586213 = 4609915) B4609915
theorem B32781617 : Blo 2127435 32781617 := bstep (se 2 (by rfl) ⟨12293106, by rfl⟩ : syracuseStep 32781617 = 24586213) B24586213
theorem B21854411 : Blo 2127435 21854411 := bstep (se 1 (by rfl) ⟨16390808, by rfl⟩ : syracuseStep 21854411 = 32781617) B32781617
theorem B14569607 : Blo 2127435 14569607 := bstep (se 1 (by rfl) ⟨10927205, by rfl⟩ : syracuseStep 14569607 = 21854411) B21854411
theorem B9713071 : Blo 2127435 9713071 := bstep (se 1 (by rfl) ⟨7284803, by rfl⟩ : syracuseStep 9713071 = 14569607) B14569607
theorem B12950761 : Blo 2127435 12950761 := bstep (se 2 (by rfl) ⟨4856535, by rfl⟩ : syracuseStep 12950761 = 9713071) B9713071
theorem B17267681 : Blo 2127435 17267681 := bstep (se 2 (by rfl) ⟨6475380, by rfl⟩ : syracuseStep 17267681 = 12950761) B12950761
theorem B46047149 : Blo 2127435 46047149 := bstep (se 3 (by rfl) ⟨8633840, by rfl⟩ : syracuseStep 46047149 = 17267681) B17267681
theorem B30698099 : Blo 2127435 30698099 := bstep (se 1 (by rfl) ⟨23023574, by rfl⟩ : syracuseStep 30698099 = 46047149) B46047149
theorem B20465399 : Blo 2127435 20465399 := bstep (se 1 (by rfl) ⟨15349049, by rfl⟩ : syracuseStep 20465399 = 30698099) B30698099
theorem B54574397 : Blo 2127435 54574397 := bstep (se 3 (by rfl) ⟨10232699, by rfl⟩ : syracuseStep 54574397 = 20465399) B20465399
theorem B36382931 : Blo 2127435 36382931 := bstep (se 1 (by rfl) ⟨27287198, by rfl⟩ : syracuseStep 36382931 = 54574397) B54574397
theorem B24255287 : Blo 2127435 24255287 := bstep (se 1 (by rfl) ⟨18191465, by rfl⟩ : syracuseStep 24255287 = 36382931) B36382931
theorem B16170191 : Blo 2127435 16170191 := bstep (se 1 (by rfl) ⟨12127643, by rfl⟩ : syracuseStep 16170191 = 24255287) B24255287
theorem B10780127 : Blo 2127435 10780127 := bstep (se 1 (by rfl) ⟨8085095, by rfl⟩ : syracuseStep 10780127 = 16170191) B16170191
theorem B7186751 : Blo 2127435 7186751 := bstep (se 1 (by rfl) ⟨5390063, by rfl⟩ : syracuseStep 7186751 = 10780127) B10780127
theorem B4791167 : Blo 2127435 4791167 := bstep (se 1 (by rfl) ⟨3593375, by rfl⟩ : syracuseStep 4791167 = 7186751) B7186751
theorem B3194111 : Blo 2127435 3194111 := bstep (se 1 (by rfl) ⟨2395583, by rfl⟩ : syracuseStep 3194111 = 4791167) B4791167
theorem B2129407 : Blo 2127435 2129407 := bstep (se 1 (by rfl) ⟨1597055, by rfl⟩ : syracuseStep 2129407 = 3194111) B3194111
theorem B3194117 : Blo 2127435 3194117 := bbase (se 4 (by rfl) ⟨299448, by rfl⟩ : syracuseStep 3194117 = 598897) (by norm_num)
theorem B2129411 : Blo 2127435 2129411 := bstep (se 1 (by rfl) ⟨1597058, by rfl⟩ : syracuseStep 2129411 = 3194117) B3194117
theorem B3593389 : Blo 2127435 3593389 := bbase (se 3 (by rfl) ⟨673760, by rfl⟩ : syracuseStep 3593389 = 1347521) (by norm_num)
theorem B4791185 : Blo 2127435 4791185 := bstep (se 2 (by rfl) ⟨1796694, by rfl⟩ : syracuseStep 4791185 = 3593389) B3593389
theorem B3194123 : Blo 2127435 3194123 := bstep (se 1 (by rfl) ⟨2395592, by rfl⟩ : syracuseStep 3194123 = 4791185) B4791185
theorem B2129415 : Blo 2127435 2129415 := bstep (se 1 (by rfl) ⟨1597061, by rfl⟩ : syracuseStep 2129415 = 3194123) B3194123
theorem B2395597 : Blo 2127435 2395597 := bbase (se 3 (by rfl) ⟨449174, by rfl⟩ : syracuseStep 2395597 = 898349) (by norm_num)
theorem B3194129 : Blo 2127435 3194129 := bstep (se 2 (by rfl) ⟨1197798, by rfl⟩ : syracuseStep 3194129 = 2395597) B2395597
theorem B2129419 : Blo 2127435 2129419 := bstep (se 1 (by rfl) ⟨1597064, by rfl⟩ : syracuseStep 2129419 = 3194129) B3194129
theorem B7186805 : Blo 2127435 7186805 := bbase (se 5 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 7186805 = 673763) (by norm_num)
theorem B4791203 : Blo 2127435 4791203 := bstep (se 1 (by rfl) ⟨3593402, by rfl⟩ : syracuseStep 4791203 = 7186805) B7186805
theorem B3194135 : Blo 2127435 3194135 := bstep (se 1 (by rfl) ⟨2395601, by rfl⟩ : syracuseStep 3194135 = 4791203) B4791203
theorem B2129423 : Blo 2127435 2129423 := bstep (se 1 (by rfl) ⟨1597067, by rfl⟩ : syracuseStep 2129423 = 3194135) B3194135
theorem B3194141 : Blo 2127435 3194141 := bbase (se 3 (by rfl) ⟨598901, by rfl⟩ : syracuseStep 3194141 = 1197803) (by norm_num)
theorem B2129427 : Blo 2127435 2129427 := bstep (se 1 (by rfl) ⟨1597070, by rfl⟩ : syracuseStep 2129427 = 3194141) B3194141
theorem B4791221 : Blo 2127435 4791221 := bbase (se 5 (by rfl) ⟨224588, by rfl⟩ : syracuseStep 4791221 = 449177) (by norm_num)
theorem B3194147 : Blo 2127435 3194147 := bstep (se 1 (by rfl) ⟨2395610, by rfl⟩ : syracuseStep 3194147 = 4791221) B4791221
theorem B2129431 : Blo 2127435 2129431 := bstep (se 1 (by rfl) ⟨1597073, by rfl⟩ : syracuseStep 2129431 = 3194147) B3194147
theorem B10232837 : Blo 2127435 10232837 := bbase (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) (by norm_num)
theorem B6821891 : Blo 2127435 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B4547927 : Blo 2127435 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B12127805 : Blo 2127435 12127805 := bstep (se 3 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 12127805 = 4547927) B4547927
theorem B8085203 : Blo 2127435 8085203 := bstep (se 1 (by rfl) ⟨6063902, by rfl⟩ : syracuseStep 8085203 = 12127805) B12127805
theorem B5390135 : Blo 2127435 5390135 := bstep (se 1 (by rfl) ⟨4042601, by rfl⟩ : syracuseStep 5390135 = 8085203) B8085203
theorem B3593423 : Blo 2127435 3593423 := bstep (se 1 (by rfl) ⟨2695067, by rfl⟩ : syracuseStep 3593423 = 5390135) B5390135
theorem B2395615 : Blo 2127435 2395615 := bstep (se 1 (by rfl) ⟨1796711, by rfl⟩ : syracuseStep 2395615 = 3593423) B3593423
theorem B3194153 : Blo 2127435 3194153 := bstep (se 2 (by rfl) ⟨1197807, by rfl⟩ : syracuseStep 3194153 = 2395615) B2395615
theorem B2129435 : Blo 2127435 2129435 := bstep (se 1 (by rfl) ⟨1597076, by rfl⟩ : syracuseStep 2129435 = 3194153) B3194153
theorem C0 (j : ℕ) (h1 : 531858 ≤ j) (h2 : j ≤ 532358) : Blo 2127435 (4 * j + 3) := by
  interval_cases j
  · exact B2127435
  · exact B2127439
  · exact B2127443
  · exact B2127447
  · exact B2127451
  · exact B2127455
  · exact B2127459
  · exact B2127463
  · exact B2127467
  · exact B2127471
  · exact B2127475
  · exact B2127479
  · exact B2127483
  · exact B2127487
  · exact B2127491
  · exact B2127495
  · exact B2127499
  · exact B2127503
  · exact B2127507
  · exact B2127511
  · exact B2127515
  · exact B2127519
  · exact B2127523
  · exact B2127527
  · exact B2127531
  · exact B2127535
  · exact B2127539
  · exact B2127543
  · exact B2127547
  · exact B2127551
  · exact B2127555
  · exact B2127559
  · exact B2127563
  · exact B2127567
  · exact B2127571
  · exact B2127575
  · exact B2127579
  · exact B2127583
  · exact B2127587
  · exact B2127591
  · exact B2127595
  · exact B2127599
  · exact B2127603
  · exact B2127607
  · exact B2127611
  · exact B2127615
  · exact B2127619
  · exact B2127623
  · exact B2127627
  · exact B2127631
  · exact B2127635
  · exact B2127639
  · exact B2127643
  · exact B2127647
  · exact B2127651
  · exact B2127655
  · exact B2127659
  · exact B2127663
  · exact B2127667
  · exact B2127671
  · exact B2127675
  · exact B2127679
  · exact B2127683
  · exact B2127687
  · exact B2127691
  · exact B2127695
  · exact B2127699
  · exact B2127703
  · exact B2127707
  · exact B2127711
  · exact B2127715
  · exact B2127719
  · exact B2127723
  · exact B2127727
  · exact B2127731
  · exact B2127735
  · exact B2127739
  · exact B2127743
  · exact B2127747
  · exact B2127751
  · exact B2127755
  · exact B2127759
  · exact B2127763
  · exact B2127767
  · exact B2127771
  · exact B2127775
  · exact B2127779
  · exact B2127783
  · exact B2127787
  · exact B2127791
  · exact B2127795
  · exact B2127799
  · exact B2127803
  · exact B2127807
  · exact B2127811
  · exact B2127815
  · exact B2127819
  · exact B2127823
  · exact B2127827
  · exact B2127831
  · exact B2127835
  · exact B2127839
  · exact B2127843
  · exact B2127847
  · exact B2127851
  · exact B2127855
  · exact B2127859
  · exact B2127863
  · exact B2127867
  · exact B2127871
  · exact B2127875
  · exact B2127879
  · exact B2127883
  · exact B2127887
  · exact B2127891
  · exact B2127895
  · exact B2127899
  · exact B2127903
  · exact B2127907
  · exact B2127911
  · exact B2127915
  · exact B2127919
  · exact B2127923
  · exact B2127927
  · exact B2127931
  · exact B2127935
  · exact B2127939
  · exact B2127943
  · exact B2127947
  · exact B2127951
  · exact B2127955
  · exact B2127959
  · exact B2127963
  · exact B2127967
  · exact B2127971
  · exact B2127975
  · exact B2127979
  · exact B2127983
  · exact B2127987
  · exact B2127991
  · exact B2127995
  · exact B2127999
  · exact B2128003
  · exact B2128007
  · exact B2128011
  · exact B2128015
  · exact B2128019
  · exact B2128023
  · exact B2128027
  · exact B2128031
  · exact B2128035
  · exact B2128039
  · exact B2128043
  · exact B2128047
  · exact B2128051
  · exact B2128055
  · exact B2128059
  · exact B2128063
  · exact B2128067
  · exact B2128071
  · exact B2128075
  · exact B2128079
  · exact B2128083
  · exact B2128087
  · exact B2128091
  · exact B2128095
  · exact B2128099
  · exact B2128103
  · exact B2128107
  · exact B2128111
  · exact B2128115
  · exact B2128119
  · exact B2128123
  · exact B2128127
  · exact B2128131
  · exact B2128135
  · exact B2128139
  · exact B2128143
  · exact B2128147
  · exact B2128151
  · exact B2128155
  · exact B2128159
  · exact B2128163
  · exact B2128167
  · exact B2128171
  · exact B2128175
  · exact B2128179
  · exact B2128183
  · exact B2128187
  · exact B2128191
  · exact B2128195
  · exact B2128199
  · exact B2128203
  · exact B2128207
  · exact B2128211
  · exact B2128215
  · exact B2128219
  · exact B2128223
  · exact B2128227
  · exact B2128231
  · exact B2128235
  · exact B2128239
  · exact B2128243
  · exact B2128247
  · exact B2128251
  · exact B2128255
  · exact B2128259
  · exact B2128263
  · exact B2128267
  · exact B2128271
  · exact B2128275
  · exact B2128279
  · exact B2128283
  · exact B2128287
  · exact B2128291
  · exact B2128295
  · exact B2128299
  · exact B2128303
  · exact B2128307
  · exact B2128311
  · exact B2128315
  · exact B2128319
  · exact B2128323
  · exact B2128327
  · exact B2128331
  · exact B2128335
  · exact B2128339
  · exact B2128343
  · exact B2128347
  · exact B2128351
  · exact B2128355
  · exact B2128359
  · exact B2128363
  · exact B2128367
  · exact B2128371
  · exact B2128375
  · exact B2128379
  · exact B2128383
  · exact B2128387
  · exact B2128391
  · exact B2128395
  · exact B2128399
  · exact B2128403
  · exact B2128407
  · exact B2128411
  · exact B2128415
  · exact B2128419
  · exact B2128423
  · exact B2128427
  · exact B2128431
  · exact B2128435
  · exact B2128439
  · exact B2128443
  · exact B2128447
  · exact B2128451
  · exact B2128455
  · exact B2128459
  · exact B2128463
  · exact B2128467
  · exact B2128471
  · exact B2128475
  · exact B2128479
  · exact B2128483
  · exact B2128487
  · exact B2128491
  · exact B2128495
  · exact B2128499
  · exact B2128503
  · exact B2128507
  · exact B2128511
  · exact B2128515
  · exact B2128519
  · exact B2128523
  · exact B2128527
  · exact B2128531
  · exact B2128535
  · exact B2128539
  · exact B2128543
  · exact B2128547
  · exact B2128551
  · exact B2128555
  · exact B2128559
  · exact B2128563
  · exact B2128567
  · exact B2128571
  · exact B2128575
  · exact B2128579
  · exact B2128583
  · exact B2128587
  · exact B2128591
  · exact B2128595
  · exact B2128599
  · exact B2128603
  · exact B2128607
  · exact B2128611
  · exact B2128615
  · exact B2128619
  · exact B2128623
  · exact B2128627
  · exact B2128631
  · exact B2128635
  · exact B2128639
  · exact B2128643
  · exact B2128647
  · exact B2128651
  · exact B2128655
  · exact B2128659
  · exact B2128663
  · exact B2128667
  · exact B2128671
  · exact B2128675
  · exact B2128679
  · exact B2128683
  · exact B2128687
  · exact B2128691
  · exact B2128695
  · exact B2128699
  · exact B2128703
  · exact B2128707
  · exact B2128711
  · exact B2128715
  · exact B2128719
  · exact B2128723
  · exact B2128727
  · exact B2128731
  · exact B2128735
  · exact B2128739
  · exact B2128743
  · exact B2128747
  · exact B2128751
  · exact B2128755
  · exact B2128759
  · exact B2128763
  · exact B2128767
  · exact B2128771
  · exact B2128775
  · exact B2128779
  · exact B2128783
  · exact B2128787
  · exact B2128791
  · exact B2128795
  · exact B2128799
  · exact B2128803
  · exact B2128807
  · exact B2128811
  · exact B2128815
  · exact B2128819
  · exact B2128823
  · exact B2128827
  · exact B2128831
  · exact B2128835
  · exact B2128839
  · exact B2128843
  · exact B2128847
  · exact B2128851
  · exact B2128855
  · exact B2128859
  · exact B2128863
  · exact B2128867
  · exact B2128871
  · exact B2128875
  · exact B2128879
  · exact B2128883
  · exact B2128887
  · exact B2128891
  · exact B2128895
  · exact B2128899
  · exact B2128903
  · exact B2128907
  · exact B2128911
  · exact B2128915
  · exact B2128919
  · exact B2128923
  · exact B2128927
  · exact B2128931
  · exact B2128935
  · exact B2128939
  · exact B2128943
  · exact B2128947
  · exact B2128951
  · exact B2128955
  · exact B2128959
  · exact B2128963
  · exact B2128967
  · exact B2128971
  · exact B2128975
  · exact B2128979
  · exact B2128983
  · exact B2128987
  · exact B2128991
  · exact B2128995
  · exact B2128999
  · exact B2129003
  · exact B2129007
  · exact B2129011
  · exact B2129015
  · exact B2129019
  · exact B2129023
  · exact B2129027
  · exact B2129031
  · exact B2129035
  · exact B2129039
  · exact B2129043
  · exact B2129047
  · exact B2129051
  · exact B2129055
  · exact B2129059
  · exact B2129063
  · exact B2129067
  · exact B2129071
  · exact B2129075
  · exact B2129079
  · exact B2129083
  · exact B2129087
  · exact B2129091
  · exact B2129095
  · exact B2129099
  · exact B2129103
  · exact B2129107
  · exact B2129111
  · exact B2129115
  · exact B2129119
  · exact B2129123
  · exact B2129127
  · exact B2129131
  · exact B2129135
  · exact B2129139
  · exact B2129143
  · exact B2129147
  · exact B2129151
  · exact B2129155
  · exact B2129159
  · exact B2129163
  · exact B2129167
  · exact B2129171
  · exact B2129175
  · exact B2129179
  · exact B2129183
  · exact B2129187
  · exact B2129191
  · exact B2129195
  · exact B2129199
  · exact B2129203
  · exact B2129207
  · exact B2129211
  · exact B2129215
  · exact B2129219
  · exact B2129223
  · exact B2129227
  · exact B2129231
  · exact B2129235
  · exact B2129239
  · exact B2129243
  · exact B2129247
  · exact B2129251
  · exact B2129255
  · exact B2129259
  · exact B2129263
  · exact B2129267
  · exact B2129271
  · exact B2129275
  · exact B2129279
  · exact B2129283
  · exact B2129287
  · exact B2129291
  · exact B2129295
  · exact B2129299
  · exact B2129303
  · exact B2129307
  · exact B2129311
  · exact B2129315
  · exact B2129319
  · exact B2129323
  · exact B2129327
  · exact B2129331
  · exact B2129335
  · exact B2129339
  · exact B2129343
  · exact B2129347
  · exact B2129351
  · exact B2129355
  · exact B2129359
  · exact B2129363
  · exact B2129367
  · exact B2129371
  · exact B2129375
  · exact B2129379
  · exact B2129383
  · exact B2129387
  · exact B2129391
  · exact B2129395
  · exact B2129399
  · exact B2129403
  · exact B2129407
  · exact B2129411
  · exact B2129415
  · exact B2129419
  · exact B2129423
  · exact B2129427
  · exact B2129431
  · exact B2129435
theorem solution (m : ℕ) (hlo : 2127435 ≤ m) (hhi : m ≤ 2129435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 531858 ≤ j := by omega
    have hj2 : j ≤ 532358 := by omega
    have hb : Blo 2127435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
