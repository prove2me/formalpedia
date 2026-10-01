-- Prove2me | solution 1 for syracuse_descends_range_2193435_2195435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:10.233793+00:00
-- url     : https://prove2.me/submissions/481dc28e-22be-4527-8cb0-597831fd6ade

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

theorem B3513461 : Blo 2193435 3513461 := bbase (se 5 (by rfl) ⟨164693, by rfl⟩ : syracuseStep 3513461 = 329387) (by norm_num)
theorem B9369229 : Blo 2193435 9369229 := bstep (se 3 (by rfl) ⟨1756730, by rfl⟩ : syracuseStep 9369229 = 3513461) B3513461
theorem B12492305 : Blo 2193435 12492305 := bstep (se 2 (by rfl) ⟨4684614, by rfl⟩ : syracuseStep 12492305 = 9369229) B9369229
theorem B8328203 : Blo 2193435 8328203 := bstep (se 1 (by rfl) ⟨6246152, by rfl⟩ : syracuseStep 8328203 = 12492305) B12492305
theorem B5552135 : Blo 2193435 5552135 := bstep (se 1 (by rfl) ⟨4164101, by rfl⟩ : syracuseStep 5552135 = 8328203) B8328203
theorem B3701423 : Blo 2193435 3701423 := bstep (se 1 (by rfl) ⟨2776067, by rfl⟩ : syracuseStep 3701423 = 5552135) B5552135
theorem B2467615 : Blo 2193435 2467615 := bstep (se 1 (by rfl) ⟨1850711, by rfl⟩ : syracuseStep 2467615 = 3701423) B3701423
theorem B3290153 : Blo 2193435 3290153 := bstep (se 2 (by rfl) ⟨1233807, by rfl⟩ : syracuseStep 3290153 = 2467615) B2467615
theorem B2193435 : Blo 2193435 2193435 := bstep (se 1 (by rfl) ⟨1645076, by rfl⟩ : syracuseStep 2193435 = 3290153) B3290153
theorem B4446733 : Blo 2193435 4446733 := bbase (se 3 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 4446733 = 1667525) (by norm_num)
theorem B5928977 : Blo 2193435 5928977 := bstep (se 2 (by rfl) ⟨2223366, by rfl⟩ : syracuseStep 5928977 = 4446733) B4446733
theorem B3952651 : Blo 2193435 3952651 := bstep (se 1 (by rfl) ⟨2964488, by rfl⟩ : syracuseStep 3952651 = 5928977) B5928977
theorem B5270201 : Blo 2193435 5270201 := bstep (se 2 (by rfl) ⟨1976325, by rfl⟩ : syracuseStep 5270201 = 3952651) B3952651
theorem B3513467 : Blo 2193435 3513467 := bstep (se 1 (by rfl) ⟨2635100, by rfl⟩ : syracuseStep 3513467 = 5270201) B5270201
theorem B9369245 : Blo 2193435 9369245 := bstep (se 3 (by rfl) ⟨1756733, by rfl⟩ : syracuseStep 9369245 = 3513467) B3513467
theorem B6246163 : Blo 2193435 6246163 := bstep (se 1 (by rfl) ⟨4684622, by rfl⟩ : syracuseStep 6246163 = 9369245) B9369245
theorem B8328217 : Blo 2193435 8328217 := bstep (se 2 (by rfl) ⟨3123081, by rfl⟩ : syracuseStep 8328217 = 6246163) B6246163
theorem B11104289 : Blo 2193435 11104289 := bstep (se 2 (by rfl) ⟨4164108, by rfl⟩ : syracuseStep 11104289 = 8328217) B8328217
theorem B7402859 : Blo 2193435 7402859 := bstep (se 1 (by rfl) ⟨5552144, by rfl⟩ : syracuseStep 7402859 = 11104289) B11104289
theorem B4935239 : Blo 2193435 4935239 := bstep (se 1 (by rfl) ⟨3701429, by rfl⟩ : syracuseStep 4935239 = 7402859) B7402859
theorem B3290159 : Blo 2193435 3290159 := bstep (se 1 (by rfl) ⟨2467619, by rfl⟩ : syracuseStep 3290159 = 4935239) B4935239
theorem B2193439 : Blo 2193435 2193439 := bstep (se 1 (by rfl) ⟨1645079, by rfl⟩ : syracuseStep 2193439 = 3290159) B3290159
theorem B3290165 : Blo 2193435 3290165 := bbase (se 5 (by rfl) ⟨154226, by rfl⟩ : syracuseStep 3290165 = 308453) (by norm_num)
theorem B2193443 : Blo 2193435 2193443 := bstep (se 1 (by rfl) ⟨1645082, by rfl⟩ : syracuseStep 2193443 = 3290165) B3290165
theorem B5552165 : Blo 2193435 5552165 := bbase (se 4 (by rfl) ⟨520515, by rfl⟩ : syracuseStep 5552165 = 1041031) (by norm_num)
theorem B3701443 : Blo 2193435 3701443 := bstep (se 1 (by rfl) ⟨2776082, by rfl⟩ : syracuseStep 3701443 = 5552165) B5552165
theorem B4935257 : Blo 2193435 4935257 := bstep (se 2 (by rfl) ⟨1850721, by rfl⟩ : syracuseStep 4935257 = 3701443) B3701443
theorem B3290171 : Blo 2193435 3290171 := bstep (se 1 (by rfl) ⟨2467628, by rfl⟩ : syracuseStep 3290171 = 4935257) B4935257
theorem B2193447 : Blo 2193435 2193447 := bstep (se 1 (by rfl) ⟨1645085, by rfl⟩ : syracuseStep 2193447 = 3290171) B3290171
theorem B2467633 : Blo 2193435 2467633 := bbase (se 2 (by rfl) ⟨925362, by rfl⟩ : syracuseStep 2467633 = 1850725) (by norm_num)
theorem B3290177 : Blo 2193435 3290177 := bstep (se 2 (by rfl) ⟨1233816, by rfl⟩ : syracuseStep 3290177 = 2467633) B2467633
theorem B2193451 : Blo 2193435 2193451 := bstep (se 1 (by rfl) ⟨1645088, by rfl⟩ : syracuseStep 2193451 = 3290177) B3290177
theorem B3513493 : Blo 2193435 3513493 := bbase (se 6 (by rfl) ⟨82347, by rfl⟩ : syracuseStep 3513493 = 164695) (by norm_num)
theorem B4684657 : Blo 2193435 4684657 := bstep (se 2 (by rfl) ⟨1756746, by rfl⟩ : syracuseStep 4684657 = 3513493) B3513493
theorem B6246209 : Blo 2193435 6246209 := bstep (se 2 (by rfl) ⟨2342328, by rfl⟩ : syracuseStep 6246209 = 4684657) B4684657
theorem B4164139 : Blo 2193435 4164139 := bstep (se 1 (by rfl) ⟨3123104, by rfl⟩ : syracuseStep 4164139 = 6246209) B6246209
theorem B5552185 : Blo 2193435 5552185 := bstep (se 2 (by rfl) ⟨2082069, by rfl⟩ : syracuseStep 5552185 = 4164139) B4164139
theorem B7402913 : Blo 2193435 7402913 := bstep (se 2 (by rfl) ⟨2776092, by rfl⟩ : syracuseStep 7402913 = 5552185) B5552185
theorem B4935275 : Blo 2193435 4935275 := bstep (se 1 (by rfl) ⟨3701456, by rfl⟩ : syracuseStep 4935275 = 7402913) B7402913
theorem B3290183 : Blo 2193435 3290183 := bstep (se 1 (by rfl) ⟨2467637, by rfl⟩ : syracuseStep 3290183 = 4935275) B4935275
theorem B2193455 : Blo 2193435 2193455 := bstep (se 1 (by rfl) ⟨1645091, by rfl⟩ : syracuseStep 2193455 = 3290183) B3290183
theorem B3290189 : Blo 2193435 3290189 := bbase (se 3 (by rfl) ⟨616910, by rfl⟩ : syracuseStep 3290189 = 1233821) (by norm_num)
theorem B2193459 : Blo 2193435 2193459 := bstep (se 1 (by rfl) ⟨1645094, by rfl⟩ : syracuseStep 2193459 = 3290189) B3290189
theorem B4935293 : Blo 2193435 4935293 := bbase (se 3 (by rfl) ⟨925367, by rfl⟩ : syracuseStep 4935293 = 1850735) (by norm_num)
theorem B3290195 : Blo 2193435 3290195 := bstep (se 1 (by rfl) ⟨2467646, by rfl⟩ : syracuseStep 3290195 = 4935293) B4935293
theorem B2193463 : Blo 2193435 2193463 := bstep (se 1 (by rfl) ⟨1645097, by rfl⟩ : syracuseStep 2193463 = 3290195) B3290195
theorem B3701477 : Blo 2193435 3701477 := bbase (se 4 (by rfl) ⟨347013, by rfl⟩ : syracuseStep 3701477 = 694027) (by norm_num)
theorem B2467651 : Blo 2193435 2467651 := bstep (se 1 (by rfl) ⟨1850738, by rfl⟩ : syracuseStep 2467651 = 3701477) B3701477
theorem B3290201 : Blo 2193435 3290201 := bstep (se 2 (by rfl) ⟨1233825, by rfl⟩ : syracuseStep 3290201 = 2467651) B2467651
theorem B2193467 : Blo 2193435 2193467 := bstep (se 1 (by rfl) ⟨1645100, by rfl⟩ : syracuseStep 2193467 = 3290201) B3290201
theorem B3952709 : Blo 2193435 3952709 := bbase (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) (by norm_num)
theorem B2635139 : Blo 2193435 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B7027037 : Blo 2193435 7027037 := bstep (se 3 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 7027037 = 2635139) B2635139
theorem B4684691 : Blo 2193435 4684691 := bstep (se 1 (by rfl) ⟨3513518, by rfl⟩ : syracuseStep 4684691 = 7027037) B7027037
theorem B3123127 : Blo 2193435 3123127 := bstep (se 1 (by rfl) ⟨2342345, by rfl⟩ : syracuseStep 3123127 = 4684691) B4684691
theorem B16656677 : Blo 2193435 16656677 := bstep (se 4 (by rfl) ⟨1561563, by rfl⟩ : syracuseStep 16656677 = 3123127) B3123127
theorem B11104451 : Blo 2193435 11104451 := bstep (se 1 (by rfl) ⟨8328338, by rfl⟩ : syracuseStep 11104451 = 16656677) B16656677
theorem B7402967 : Blo 2193435 7402967 := bstep (se 1 (by rfl) ⟨5552225, by rfl⟩ : syracuseStep 7402967 = 11104451) B11104451
theorem B4935311 : Blo 2193435 4935311 := bstep (se 1 (by rfl) ⟨3701483, by rfl⟩ : syracuseStep 4935311 = 7402967) B7402967
theorem B3290207 : Blo 2193435 3290207 := bstep (se 1 (by rfl) ⟨2467655, by rfl⟩ : syracuseStep 3290207 = 4935311) B4935311
theorem B2193471 : Blo 2193435 2193471 := bstep (se 1 (by rfl) ⟨1645103, by rfl⟩ : syracuseStep 2193471 = 3290207) B3290207
theorem B3290213 : Blo 2193435 3290213 := bbase (se 4 (by rfl) ⟨308457, by rfl⟩ : syracuseStep 3290213 = 616915) (by norm_num)
theorem B2193475 : Blo 2193435 2193475 := bstep (se 1 (by rfl) ⟨1645106, by rfl⟩ : syracuseStep 2193475 = 3290213) B3290213
theorem B4684709 : Blo 2193435 4684709 := bbase (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) (by norm_num)
theorem B3123139 : Blo 2193435 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B4164185 : Blo 2193435 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B2776123 : Blo 2193435 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B3701497 : Blo 2193435 3701497 := bstep (se 2 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 3701497 = 2776123) B2776123
theorem B4935329 : Blo 2193435 4935329 := bstep (se 2 (by rfl) ⟨1850748, by rfl⟩ : syracuseStep 4935329 = 3701497) B3701497
theorem B3290219 : Blo 2193435 3290219 := bstep (se 1 (by rfl) ⟨2467664, by rfl⟩ : syracuseStep 3290219 = 4935329) B4935329
theorem B2193479 : Blo 2193435 2193479 := bstep (se 1 (by rfl) ⟨1645109, by rfl⟩ : syracuseStep 2193479 = 3290219) B3290219
theorem B2467669 : Blo 2193435 2467669 := bbase (se 9 (by rfl) ⟨7229, by rfl⟩ : syracuseStep 2467669 = 14459) (by norm_num)
theorem B3290225 : Blo 2193435 3290225 := bstep (se 2 (by rfl) ⟨1233834, by rfl⟩ : syracuseStep 3290225 = 2467669) B2467669
theorem B2193483 : Blo 2193435 2193483 := bstep (se 1 (by rfl) ⟨1645112, by rfl⟩ : syracuseStep 2193483 = 3290225) B3290225
theorem B2776133 : Blo 2193435 2776133 := bbase (se 4 (by rfl) ⟨260262, by rfl⟩ : syracuseStep 2776133 = 520525) (by norm_num)
theorem B7403021 : Blo 2193435 7403021 := bstep (se 3 (by rfl) ⟨1388066, by rfl⟩ : syracuseStep 7403021 = 2776133) B2776133
theorem B4935347 : Blo 2193435 4935347 := bstep (se 1 (by rfl) ⟨3701510, by rfl⟩ : syracuseStep 4935347 = 7403021) B7403021
theorem B3290231 : Blo 2193435 3290231 := bstep (se 1 (by rfl) ⟨2467673, by rfl⟩ : syracuseStep 3290231 = 4935347) B4935347
theorem B2193487 : Blo 2193435 2193487 := bstep (se 1 (by rfl) ⟨1645115, by rfl⟩ : syracuseStep 2193487 = 3290231) B3290231
theorem B3290237 : Blo 2193435 3290237 := bbase (se 3 (by rfl) ⟨616919, by rfl⟩ : syracuseStep 3290237 = 1233839) (by norm_num)
theorem B2193491 : Blo 2193435 2193491 := bstep (se 1 (by rfl) ⟨1645118, by rfl⟩ : syracuseStep 2193491 = 3290237) B3290237
theorem B4935365 : Blo 2193435 4935365 := bbase (se 4 (by rfl) ⟨462690, by rfl⟩ : syracuseStep 4935365 = 925381) (by norm_num)
theorem B3290243 : Blo 2193435 3290243 := bstep (se 1 (by rfl) ⟨2467682, by rfl⟩ : syracuseStep 3290243 = 4935365) B4935365
theorem B2193495 : Blo 2193435 2193495 := bstep (se 1 (by rfl) ⟨1645121, by rfl⟩ : syracuseStep 2193495 = 3290243) B3290243
theorem B11256101 : Blo 2193435 11256101 := bbase (se 4 (by rfl) ⟨1055259, by rfl⟩ : syracuseStep 11256101 = 2110519) (by norm_num)
theorem B7504067 : Blo 2193435 7504067 := bstep (se 1 (by rfl) ⟨5628050, by rfl⟩ : syracuseStep 7504067 = 11256101) B11256101
theorem B20010845 : Blo 2193435 20010845 := bstep (se 3 (by rfl) ⟨3752033, by rfl⟩ : syracuseStep 20010845 = 7504067) B7504067
theorem B53362253 : Blo 2193435 53362253 := bstep (se 3 (by rfl) ⟨10005422, by rfl⟩ : syracuseStep 53362253 = 20010845) B20010845
theorem B35574835 : Blo 2193435 35574835 := bstep (se 1 (by rfl) ⟨26681126, by rfl⟩ : syracuseStep 35574835 = 53362253) B53362253
theorem B47433113 : Blo 2193435 47433113 := bstep (se 2 (by rfl) ⟨17787417, by rfl⟩ : syracuseStep 47433113 = 35574835) B35574835
theorem B31622075 : Blo 2193435 31622075 := bstep (se 1 (by rfl) ⟨23716556, by rfl⟩ : syracuseStep 31622075 = 47433113) B47433113
theorem B21081383 : Blo 2193435 21081383 := bstep (se 1 (by rfl) ⟨15811037, by rfl⟩ : syracuseStep 21081383 = 31622075) B31622075
theorem B14054255 : Blo 2193435 14054255 := bstep (se 1 (by rfl) ⟨10540691, by rfl⟩ : syracuseStep 14054255 = 21081383) B21081383
theorem B9369503 : Blo 2193435 9369503 := bstep (se 1 (by rfl) ⟨7027127, by rfl⟩ : syracuseStep 9369503 = 14054255) B14054255
theorem B6246335 : Blo 2193435 6246335 := bstep (se 1 (by rfl) ⟨4684751, by rfl⟩ : syracuseStep 6246335 = 9369503) B9369503
theorem B4164223 : Blo 2193435 4164223 := bstep (se 1 (by rfl) ⟨3123167, by rfl⟩ : syracuseStep 4164223 = 6246335) B6246335
theorem B5552297 : Blo 2193435 5552297 := bstep (se 2 (by rfl) ⟨2082111, by rfl⟩ : syracuseStep 5552297 = 4164223) B4164223
theorem B3701531 : Blo 2193435 3701531 := bstep (se 1 (by rfl) ⟨2776148, by rfl⟩ : syracuseStep 3701531 = 5552297) B5552297
theorem B2467687 : Blo 2193435 2467687 := bstep (se 1 (by rfl) ⟨1850765, by rfl⟩ : syracuseStep 2467687 = 3701531) B3701531
theorem B3290249 : Blo 2193435 3290249 := bstep (se 2 (by rfl) ⟨1233843, by rfl⟩ : syracuseStep 3290249 = 2467687) B2467687
theorem B2193499 : Blo 2193435 2193499 := bstep (se 1 (by rfl) ⟨1645124, by rfl⟩ : syracuseStep 2193499 = 3290249) B3290249
theorem B11104613 : Blo 2193435 11104613 := bbase (se 4 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 11104613 = 2082115) (by norm_num)
theorem B7403075 : Blo 2193435 7403075 := bstep (se 1 (by rfl) ⟨5552306, by rfl⟩ : syracuseStep 7403075 = 11104613) B11104613
theorem B4935383 : Blo 2193435 4935383 := bstep (se 1 (by rfl) ⟨3701537, by rfl⟩ : syracuseStep 4935383 = 7403075) B7403075
theorem B3290255 : Blo 2193435 3290255 := bstep (se 1 (by rfl) ⟨2467691, by rfl⟩ : syracuseStep 3290255 = 4935383) B4935383
theorem B2193503 : Blo 2193435 2193503 := bstep (se 1 (by rfl) ⟨1645127, by rfl⟩ : syracuseStep 2193503 = 3290255) B3290255
theorem B3290261 : Blo 2193435 3290261 := bbase (se 6 (by rfl) ⟨77115, by rfl⟩ : syracuseStep 3290261 = 154231) (by norm_num)
theorem B2193507 : Blo 2193435 2193507 := bstep (se 1 (by rfl) ⟨1645130, by rfl⟩ : syracuseStep 2193507 = 3290261) B3290261
theorem B3952781 : Blo 2193435 3952781 := bbase (se 3 (by rfl) ⟨741146, by rfl⟩ : syracuseStep 3952781 = 1482293) (by norm_num)
theorem B2635187 : Blo 2193435 2635187 := bstep (se 1 (by rfl) ⟨1976390, by rfl⟩ : syracuseStep 2635187 = 3952781) B3952781
theorem B7027165 : Blo 2193435 7027165 := bstep (se 3 (by rfl) ⟨1317593, by rfl⟩ : syracuseStep 7027165 = 2635187) B2635187
theorem B9369553 : Blo 2193435 9369553 := bstep (se 2 (by rfl) ⟨3513582, by rfl⟩ : syracuseStep 9369553 = 7027165) B7027165
theorem B12492737 : Blo 2193435 12492737 := bstep (se 2 (by rfl) ⟨4684776, by rfl⟩ : syracuseStep 12492737 = 9369553) B9369553
theorem B8328491 : Blo 2193435 8328491 := bstep (se 1 (by rfl) ⟨6246368, by rfl⟩ : syracuseStep 8328491 = 12492737) B12492737
theorem B5552327 : Blo 2193435 5552327 := bstep (se 1 (by rfl) ⟨4164245, by rfl⟩ : syracuseStep 5552327 = 8328491) B8328491
theorem B3701551 : Blo 2193435 3701551 := bstep (se 1 (by rfl) ⟨2776163, by rfl⟩ : syracuseStep 3701551 = 5552327) B5552327
theorem B4935401 : Blo 2193435 4935401 := bstep (se 2 (by rfl) ⟨1850775, by rfl⟩ : syracuseStep 4935401 = 3701551) B3701551
theorem B3290267 : Blo 2193435 3290267 := bstep (se 1 (by rfl) ⟨2467700, by rfl⟩ : syracuseStep 3290267 = 4935401) B4935401
theorem B2193511 : Blo 2193435 2193511 := bstep (se 1 (by rfl) ⟨1645133, by rfl⟩ : syracuseStep 2193511 = 3290267) B3290267
theorem B2467705 : Blo 2193435 2467705 := bbase (se 2 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 2467705 = 1850779) (by norm_num)
theorem B3290273 : Blo 2193435 3290273 := bstep (se 2 (by rfl) ⟨1233852, by rfl⟩ : syracuseStep 3290273 = 2467705) B2467705
theorem B2193515 : Blo 2193435 2193515 := bstep (se 1 (by rfl) ⟨1645136, by rfl⟩ : syracuseStep 2193515 = 3290273) B3290273
theorem B4221077 : Blo 2193435 4221077 := bbase (se 6 (by rfl) ⟨98931, by rfl⟩ : syracuseStep 4221077 = 197863) (by norm_num)
theorem B11256205 : Blo 2193435 11256205 := bstep (se 3 (by rfl) ⟨2110538, by rfl⟩ : syracuseStep 11256205 = 4221077) B4221077
theorem B15008273 : Blo 2193435 15008273 := bstep (se 2 (by rfl) ⟨5628102, by rfl⟩ : syracuseStep 15008273 = 11256205) B11256205
theorem B10005515 : Blo 2193435 10005515 := bstep (se 1 (by rfl) ⟨7504136, by rfl⟩ : syracuseStep 10005515 = 15008273) B15008273
theorem B6670343 : Blo 2193435 6670343 := bstep (se 1 (by rfl) ⟨5002757, by rfl⟩ : syracuseStep 6670343 = 10005515) B10005515
theorem B4446895 : Blo 2193435 4446895 := bstep (se 1 (by rfl) ⟨3335171, by rfl⟩ : syracuseStep 4446895 = 6670343) B6670343
theorem B5929193 : Blo 2193435 5929193 := bstep (se 2 (by rfl) ⟨2223447, by rfl⟩ : syracuseStep 5929193 = 4446895) B4446895
theorem B3952795 : Blo 2193435 3952795 := bstep (se 1 (by rfl) ⟨2964596, by rfl⟩ : syracuseStep 3952795 = 5929193) B5929193
theorem B5270393 : Blo 2193435 5270393 := bstep (se 2 (by rfl) ⟨1976397, by rfl⟩ : syracuseStep 5270393 = 3952795) B3952795
theorem B14054381 : Blo 2193435 14054381 := bstep (se 3 (by rfl) ⟨2635196, by rfl⟩ : syracuseStep 14054381 = 5270393) B5270393
theorem B9369587 : Blo 2193435 9369587 := bstep (se 1 (by rfl) ⟨7027190, by rfl⟩ : syracuseStep 9369587 = 14054381) B14054381
theorem B6246391 : Blo 2193435 6246391 := bstep (se 1 (by rfl) ⟨4684793, by rfl⟩ : syracuseStep 6246391 = 9369587) B9369587
theorem B8328521 : Blo 2193435 8328521 := bstep (se 2 (by rfl) ⟨3123195, by rfl⟩ : syracuseStep 8328521 = 6246391) B6246391
theorem B5552347 : Blo 2193435 5552347 := bstep (se 1 (by rfl) ⟨4164260, by rfl⟩ : syracuseStep 5552347 = 8328521) B8328521
theorem B7403129 : Blo 2193435 7403129 := bstep (se 2 (by rfl) ⟨2776173, by rfl⟩ : syracuseStep 7403129 = 5552347) B5552347
theorem B4935419 : Blo 2193435 4935419 := bstep (se 1 (by rfl) ⟨3701564, by rfl⟩ : syracuseStep 4935419 = 7403129) B7403129
theorem B3290279 : Blo 2193435 3290279 := bstep (se 1 (by rfl) ⟨2467709, by rfl⟩ : syracuseStep 3290279 = 4935419) B4935419
theorem B2193519 : Blo 2193435 2193519 := bstep (se 1 (by rfl) ⟨1645139, by rfl⟩ : syracuseStep 2193519 = 3290279) B3290279
theorem B3290285 : Blo 2193435 3290285 := bbase (se 3 (by rfl) ⟨616928, by rfl⟩ : syracuseStep 3290285 = 1233857) (by norm_num)
theorem B2193523 : Blo 2193435 2193523 := bstep (se 1 (by rfl) ⟨1645142, by rfl⟩ : syracuseStep 2193523 = 3290285) B3290285
theorem B4935437 : Blo 2193435 4935437 := bbase (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) (by norm_num)
theorem B3290291 : Blo 2193435 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B2193527 : Blo 2193435 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B2776189 : Blo 2193435 2776189 := bbase (se 3 (by rfl) ⟨520535, by rfl⟩ : syracuseStep 2776189 = 1041071) (by norm_num)
theorem B3701585 : Blo 2193435 3701585 := bstep (se 2 (by rfl) ⟨1388094, by rfl⟩ : syracuseStep 3701585 = 2776189) B2776189
theorem B2467723 : Blo 2193435 2467723 := bstep (se 1 (by rfl) ⟨1850792, by rfl⟩ : syracuseStep 2467723 = 3701585) B3701585
theorem B3290297 : Blo 2193435 3290297 := bstep (se 2 (by rfl) ⟨1233861, by rfl⟩ : syracuseStep 3290297 = 2467723) B2467723
theorem B2193531 : Blo 2193435 2193531 := bstep (se 1 (by rfl) ⟨1645148, by rfl⟩ : syracuseStep 2193531 = 3290297) B3290297
theorem B2374373 : Blo 2193435 2374373 := bbase (se 4 (by rfl) ⟨222597, by rfl⟩ : syracuseStep 2374373 = 445195) (by norm_num)
theorem B6331661 : Blo 2193435 6331661 := bstep (se 3 (by rfl) ⟨1187186, by rfl⟩ : syracuseStep 6331661 = 2374373) B2374373
theorem B4221107 : Blo 2193435 4221107 := bstep (se 1 (by rfl) ⟨3165830, by rfl⟩ : syracuseStep 4221107 = 6331661) B6331661
theorem B2814071 : Blo 2193435 2814071 := bstep (se 1 (by rfl) ⟨2110553, by rfl⟩ : syracuseStep 2814071 = 4221107) B4221107
theorem B30016757 : Blo 2193435 30016757 := bstep (se 5 (by rfl) ⟨1407035, by rfl⟩ : syracuseStep 30016757 = 2814071) B2814071
theorem B20011171 : Blo 2193435 20011171 := bstep (se 1 (by rfl) ⟨15008378, by rfl⟩ : syracuseStep 20011171 = 30016757) B30016757
theorem B26681561 : Blo 2193435 26681561 := bstep (se 2 (by rfl) ⟨10005585, by rfl⟩ : syracuseStep 26681561 = 20011171) B20011171
theorem B17787707 : Blo 2193435 17787707 := bstep (se 1 (by rfl) ⟨13340780, by rfl⟩ : syracuseStep 17787707 = 26681561) B26681561
theorem B11858471 : Blo 2193435 11858471 := bstep (se 1 (by rfl) ⟨8893853, by rfl⟩ : syracuseStep 11858471 = 17787707) B17787707
theorem B7905647 : Blo 2193435 7905647 := bstep (se 1 (by rfl) ⟨5929235, by rfl⟩ : syracuseStep 7905647 = 11858471) B11858471
theorem B5270431 : Blo 2193435 5270431 := bstep (se 1 (by rfl) ⟨3952823, by rfl⟩ : syracuseStep 5270431 = 7905647) B7905647
theorem B7027241 : Blo 2193435 7027241 := bstep (se 2 (by rfl) ⟨2635215, by rfl⟩ : syracuseStep 7027241 = 5270431) B5270431
theorem B18739309 : Blo 2193435 18739309 := bstep (se 3 (by rfl) ⟨3513620, by rfl⟩ : syracuseStep 18739309 = 7027241) B7027241
theorem B24985745 : Blo 2193435 24985745 := bstep (se 2 (by rfl) ⟨9369654, by rfl⟩ : syracuseStep 24985745 = 18739309) B18739309
theorem B16657163 : Blo 2193435 16657163 := bstep (se 1 (by rfl) ⟨12492872, by rfl⟩ : syracuseStep 16657163 = 24985745) B24985745
theorem B11104775 : Blo 2193435 11104775 := bstep (se 1 (by rfl) ⟨8328581, by rfl⟩ : syracuseStep 11104775 = 16657163) B16657163
theorem B7403183 : Blo 2193435 7403183 := bstep (se 1 (by rfl) ⟨5552387, by rfl⟩ : syracuseStep 7403183 = 11104775) B11104775
theorem B4935455 : Blo 2193435 4935455 := bstep (se 1 (by rfl) ⟨3701591, by rfl⟩ : syracuseStep 4935455 = 7403183) B7403183
theorem B3290303 : Blo 2193435 3290303 := bstep (se 1 (by rfl) ⟨2467727, by rfl⟩ : syracuseStep 3290303 = 4935455) B4935455
theorem B2193535 : Blo 2193435 2193535 := bstep (se 1 (by rfl) ⟨1645151, by rfl⟩ : syracuseStep 2193535 = 3290303) B3290303
theorem B3290309 : Blo 2193435 3290309 := bbase (se 4 (by rfl) ⟨308466, by rfl⟩ : syracuseStep 3290309 = 616933) (by norm_num)
theorem B2193539 : Blo 2193435 2193539 := bstep (se 1 (by rfl) ⟨1645154, by rfl⟩ : syracuseStep 2193539 = 3290309) B3290309
theorem B3701605 : Blo 2193435 3701605 := bbase (se 4 (by rfl) ⟨347025, by rfl⟩ : syracuseStep 3701605 = 694051) (by norm_num)
theorem B4935473 : Blo 2193435 4935473 := bstep (se 2 (by rfl) ⟨1850802, by rfl⟩ : syracuseStep 4935473 = 3701605) B3701605
theorem B3290315 : Blo 2193435 3290315 := bstep (se 1 (by rfl) ⟨2467736, by rfl⟩ : syracuseStep 3290315 = 4935473) B4935473
theorem B2193543 : Blo 2193435 2193543 := bstep (se 1 (by rfl) ⟨1645157, by rfl⟩ : syracuseStep 2193543 = 3290315) B3290315
theorem B2467741 : Blo 2193435 2467741 := bbase (se 3 (by rfl) ⟨462701, by rfl⟩ : syracuseStep 2467741 = 925403) (by norm_num)
theorem B3290321 : Blo 2193435 3290321 := bstep (se 2 (by rfl) ⟨1233870, by rfl⟩ : syracuseStep 3290321 = 2467741) B2467741
theorem B2193547 : Blo 2193435 2193547 := bstep (se 1 (by rfl) ⟨1645160, by rfl⟩ : syracuseStep 2193547 = 3290321) B3290321
theorem B7403237 : Blo 2193435 7403237 := bbase (se 4 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 7403237 = 1388107) (by norm_num)
theorem B4935491 : Blo 2193435 4935491 := bstep (se 1 (by rfl) ⟨3701618, by rfl⟩ : syracuseStep 4935491 = 7403237) B7403237
theorem B3290327 : Blo 2193435 3290327 := bstep (se 1 (by rfl) ⟨2467745, by rfl⟩ : syracuseStep 3290327 = 4935491) B4935491
theorem B2193551 : Blo 2193435 2193551 := bstep (se 1 (by rfl) ⟨1645163, by rfl⟩ : syracuseStep 2193551 = 3290327) B3290327
theorem B3290333 : Blo 2193435 3290333 := bbase (se 3 (by rfl) ⟨616937, by rfl⟩ : syracuseStep 3290333 = 1233875) (by norm_num)
theorem B2193555 : Blo 2193435 2193555 := bstep (se 1 (by rfl) ⟨1645166, by rfl⟩ : syracuseStep 2193555 = 3290333) B3290333
theorem B4935509 : Blo 2193435 4935509 := bbase (se 9 (by rfl) ⟨14459, by rfl⟩ : syracuseStep 4935509 = 28919) (by norm_num)
theorem B3290339 : Blo 2193435 3290339 := bstep (se 1 (by rfl) ⟨2467754, by rfl⟩ : syracuseStep 3290339 = 4935509) B4935509
theorem B2193559 : Blo 2193435 2193559 := bstep (se 1 (by rfl) ⟨1645169, by rfl⟩ : syracuseStep 2193559 = 3290339) B3290339
theorem B6246517 : Blo 2193435 6246517 := bbase (se 5 (by rfl) ⟨292805, by rfl⟩ : syracuseStep 6246517 = 585611) (by norm_num)
theorem B8328689 : Blo 2193435 8328689 := bstep (se 2 (by rfl) ⟨3123258, by rfl⟩ : syracuseStep 8328689 = 6246517) B6246517
theorem B5552459 : Blo 2193435 5552459 := bstep (se 1 (by rfl) ⟨4164344, by rfl⟩ : syracuseStep 5552459 = 8328689) B8328689
theorem B3701639 : Blo 2193435 3701639 := bstep (se 1 (by rfl) ⟨2776229, by rfl⟩ : syracuseStep 3701639 = 5552459) B5552459
theorem B2467759 : Blo 2193435 2467759 := bstep (se 1 (by rfl) ⟨1850819, by rfl⟩ : syracuseStep 2467759 = 3701639) B3701639
theorem B3290345 : Blo 2193435 3290345 := bstep (se 2 (by rfl) ⟨1233879, by rfl⟩ : syracuseStep 3290345 = 2467759) B2467759
theorem B2193563 : Blo 2193435 2193563 := bstep (se 1 (by rfl) ⟨1645172, by rfl⟩ : syracuseStep 2193563 = 3290345) B3290345
theorem B3752149 : Blo 2193435 3752149 := bbase (se 7 (by rfl) ⟨43970, by rfl⟩ : syracuseStep 3752149 = 87941) (by norm_num)
theorem B5002865 : Blo 2193435 5002865 := bstep (se 2 (by rfl) ⟨1876074, by rfl⟩ : syracuseStep 5002865 = 3752149) B3752149
theorem B213455573 : Blo 2193435 213455573 := bstep (se 7 (by rfl) ⟨2501432, by rfl⟩ : syracuseStep 213455573 = 5002865) B5002865
theorem B142303715 : Blo 2193435 142303715 := bstep (se 1 (by rfl) ⟨106727786, by rfl⟩ : syracuseStep 142303715 = 213455573) B213455573
theorem B94869143 : Blo 2193435 94869143 := bstep (se 1 (by rfl) ⟨71151857, by rfl⟩ : syracuseStep 94869143 = 142303715) B142303715
theorem B63246095 : Blo 2193435 63246095 := bstep (se 1 (by rfl) ⟨47434571, by rfl⟩ : syracuseStep 63246095 = 94869143) B94869143
theorem B42164063 : Blo 2193435 42164063 := bstep (se 1 (by rfl) ⟨31623047, by rfl⟩ : syracuseStep 42164063 = 63246095) B63246095
theorem B28109375 : Blo 2193435 28109375 := bstep (se 1 (by rfl) ⟨21082031, by rfl⟩ : syracuseStep 28109375 = 42164063) B42164063
theorem B18739583 : Blo 2193435 18739583 := bstep (se 1 (by rfl) ⟨14054687, by rfl⟩ : syracuseStep 18739583 = 28109375) B28109375
theorem B12493055 : Blo 2193435 12493055 := bstep (se 1 (by rfl) ⟨9369791, by rfl⟩ : syracuseStep 12493055 = 18739583) B18739583
theorem B8328703 : Blo 2193435 8328703 := bstep (se 1 (by rfl) ⟨6246527, by rfl⟩ : syracuseStep 8328703 = 12493055) B12493055
theorem B11104937 : Blo 2193435 11104937 := bstep (se 2 (by rfl) ⟨4164351, by rfl⟩ : syracuseStep 11104937 = 8328703) B8328703
theorem B7403291 : Blo 2193435 7403291 := bstep (se 1 (by rfl) ⟨5552468, by rfl⟩ : syracuseStep 7403291 = 11104937) B11104937
theorem B4935527 : Blo 2193435 4935527 := bstep (se 1 (by rfl) ⟨3701645, by rfl⟩ : syracuseStep 4935527 = 7403291) B7403291
theorem B3290351 : Blo 2193435 3290351 := bstep (se 1 (by rfl) ⟨2467763, by rfl⟩ : syracuseStep 3290351 = 4935527) B4935527
theorem B2193567 : Blo 2193435 2193567 := bstep (se 1 (by rfl) ⟨1645175, by rfl⟩ : syracuseStep 2193567 = 3290351) B3290351
theorem B3290357 : Blo 2193435 3290357 := bbase (se 5 (by rfl) ⟨154235, by rfl⟩ : syracuseStep 3290357 = 308471) (by norm_num)
theorem B2193571 : Blo 2193435 2193571 := bstep (se 1 (by rfl) ⟨1645178, by rfl⟩ : syracuseStep 2193571 = 3290357) B3290357
theorem B14054741 : Blo 2193435 14054741 := bbase (se 13 (by rfl) ⟨2573, by rfl⟩ : syracuseStep 14054741 = 5147) (by norm_num)
theorem B9369827 : Blo 2193435 9369827 := bstep (se 1 (by rfl) ⟨7027370, by rfl⟩ : syracuseStep 9369827 = 14054741) B14054741
theorem B6246551 : Blo 2193435 6246551 := bstep (se 1 (by rfl) ⟨4684913, by rfl⟩ : syracuseStep 6246551 = 9369827) B9369827
theorem B4164367 : Blo 2193435 4164367 := bstep (se 1 (by rfl) ⟨3123275, by rfl⟩ : syracuseStep 4164367 = 6246551) B6246551
theorem B5552489 : Blo 2193435 5552489 := bstep (se 2 (by rfl) ⟨2082183, by rfl⟩ : syracuseStep 5552489 = 4164367) B4164367
theorem B3701659 : Blo 2193435 3701659 := bstep (se 1 (by rfl) ⟨2776244, by rfl⟩ : syracuseStep 3701659 = 5552489) B5552489
theorem B4935545 : Blo 2193435 4935545 := bstep (se 2 (by rfl) ⟨1850829, by rfl⟩ : syracuseStep 4935545 = 3701659) B3701659
theorem B3290363 : Blo 2193435 3290363 := bstep (se 1 (by rfl) ⟨2467772, by rfl⟩ : syracuseStep 3290363 = 4935545) B4935545
theorem B2193575 : Blo 2193435 2193575 := bstep (se 1 (by rfl) ⟨1645181, by rfl⟩ : syracuseStep 2193575 = 3290363) B3290363
theorem B2467777 : Blo 2193435 2467777 := bbase (se 2 (by rfl) ⟨925416, by rfl⟩ : syracuseStep 2467777 = 1850833) (by norm_num)
theorem B3290369 : Blo 2193435 3290369 := bstep (se 2 (by rfl) ⟨1233888, by rfl⟩ : syracuseStep 3290369 = 2467777) B2467777
theorem B2193579 : Blo 2193435 2193579 := bstep (se 1 (by rfl) ⟨1645184, by rfl⟩ : syracuseStep 2193579 = 3290369) B3290369
theorem B5552509 : Blo 2193435 5552509 := bbase (se 3 (by rfl) ⟨1041095, by rfl⟩ : syracuseStep 5552509 = 2082191) (by norm_num)
theorem B7403345 : Blo 2193435 7403345 := bstep (se 2 (by rfl) ⟨2776254, by rfl⟩ : syracuseStep 7403345 = 5552509) B5552509
theorem B4935563 : Blo 2193435 4935563 := bstep (se 1 (by rfl) ⟨3701672, by rfl⟩ : syracuseStep 4935563 = 7403345) B7403345
theorem B3290375 : Blo 2193435 3290375 := bstep (se 1 (by rfl) ⟨2467781, by rfl⟩ : syracuseStep 3290375 = 4935563) B4935563
theorem B2193583 : Blo 2193435 2193583 := bstep (se 1 (by rfl) ⟨1645187, by rfl⟩ : syracuseStep 2193583 = 3290375) B3290375
theorem B3290381 : Blo 2193435 3290381 := bbase (se 3 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 3290381 = 1233893) (by norm_num)
theorem B2193587 : Blo 2193435 2193587 := bstep (se 1 (by rfl) ⟨1645190, by rfl⟩ : syracuseStep 2193587 = 3290381) B3290381
theorem B4935581 : Blo 2193435 4935581 := bbase (se 3 (by rfl) ⟨925421, by rfl⟩ : syracuseStep 4935581 = 1850843) (by norm_num)
theorem B3290387 : Blo 2193435 3290387 := bstep (se 1 (by rfl) ⟨2467790, by rfl⟩ : syracuseStep 3290387 = 4935581) B4935581
theorem B2193591 : Blo 2193435 2193591 := bstep (se 1 (by rfl) ⟨1645193, by rfl⟩ : syracuseStep 2193591 = 3290387) B3290387
theorem B3701693 : Blo 2193435 3701693 := bbase (se 3 (by rfl) ⟨694067, by rfl⟩ : syracuseStep 3701693 = 1388135) (by norm_num)
theorem B2467795 : Blo 2193435 2467795 := bstep (se 1 (by rfl) ⟨1850846, by rfl⟩ : syracuseStep 2467795 = 3701693) B3701693
theorem B3290393 : Blo 2193435 3290393 := bstep (se 2 (by rfl) ⟨1233897, by rfl⟩ : syracuseStep 3290393 = 2467795) B2467795
theorem B2193595 : Blo 2193435 2193595 := bstep (se 1 (by rfl) ⟨1645196, by rfl⟩ : syracuseStep 2193595 = 3290393) B3290393
theorem B12493237 : Blo 2193435 12493237 := bbase (se 5 (by rfl) ⟨585620, by rfl⟩ : syracuseStep 12493237 = 1171241) (by norm_num)
theorem B16657649 : Blo 2193435 16657649 := bstep (se 2 (by rfl) ⟨6246618, by rfl⟩ : syracuseStep 16657649 = 12493237) B12493237
theorem B11105099 : Blo 2193435 11105099 := bstep (se 1 (by rfl) ⟨8328824, by rfl⟩ : syracuseStep 11105099 = 16657649) B16657649
theorem B7403399 : Blo 2193435 7403399 := bstep (se 1 (by rfl) ⟨5552549, by rfl⟩ : syracuseStep 7403399 = 11105099) B11105099
theorem B4935599 : Blo 2193435 4935599 := bstep (se 1 (by rfl) ⟨3701699, by rfl⟩ : syracuseStep 4935599 = 7403399) B7403399
theorem B3290399 : Blo 2193435 3290399 := bstep (se 1 (by rfl) ⟨2467799, by rfl⟩ : syracuseStep 3290399 = 4935599) B4935599
theorem B2193599 : Blo 2193435 2193599 := bstep (se 1 (by rfl) ⟨1645199, by rfl⟩ : syracuseStep 2193599 = 3290399) B3290399
theorem B3290405 : Blo 2193435 3290405 := bbase (se 4 (by rfl) ⟨308475, by rfl⟩ : syracuseStep 3290405 = 616951) (by norm_num)
theorem B2193603 : Blo 2193435 2193603 := bstep (se 1 (by rfl) ⟨1645202, by rfl⟩ : syracuseStep 2193603 = 3290405) B3290405
theorem B2776285 : Blo 2193435 2776285 := bbase (se 3 (by rfl) ⟨520553, by rfl⟩ : syracuseStep 2776285 = 1041107) (by norm_num)
theorem B3701713 : Blo 2193435 3701713 := bstep (se 2 (by rfl) ⟨1388142, by rfl⟩ : syracuseStep 3701713 = 2776285) B2776285
theorem B4935617 : Blo 2193435 4935617 := bstep (se 2 (by rfl) ⟨1850856, by rfl⟩ : syracuseStep 4935617 = 3701713) B3701713
theorem B3290411 : Blo 2193435 3290411 := bstep (se 1 (by rfl) ⟨2467808, by rfl⟩ : syracuseStep 3290411 = 4935617) B4935617
theorem B2193607 : Blo 2193435 2193607 := bstep (se 1 (by rfl) ⟨1645205, by rfl⟩ : syracuseStep 2193607 = 3290411) B3290411
theorem B2467813 : Blo 2193435 2467813 := bbase (se 4 (by rfl) ⟨231357, by rfl⟩ : syracuseStep 2467813 = 462715) (by norm_num)
theorem B3290417 : Blo 2193435 3290417 := bstep (se 2 (by rfl) ⟨1233906, by rfl⟩ : syracuseStep 3290417 = 2467813) B2467813
theorem B2193611 : Blo 2193435 2193611 := bstep (se 1 (by rfl) ⟨1645208, by rfl⟩ : syracuseStep 2193611 = 3290417) B3290417
theorem B2223545 : Blo 2193435 2223545 := bbase (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) (by norm_num)
theorem B5929453 : Blo 2193435 5929453 := bstep (se 3 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 5929453 = 2223545) B2223545
theorem B7905937 : Blo 2193435 7905937 := bstep (se 2 (by rfl) ⟨2964726, by rfl⟩ : syracuseStep 7905937 = 5929453) B5929453
theorem B10541249 : Blo 2193435 10541249 := bstep (se 2 (by rfl) ⟨3952968, by rfl⟩ : syracuseStep 10541249 = 7905937) B7905937
theorem B7027499 : Blo 2193435 7027499 := bstep (se 1 (by rfl) ⟨5270624, by rfl⟩ : syracuseStep 7027499 = 10541249) B10541249
theorem B4684999 : Blo 2193435 4684999 := bstep (se 1 (by rfl) ⟨3513749, by rfl⟩ : syracuseStep 4684999 = 7027499) B7027499
theorem B6246665 : Blo 2193435 6246665 := bstep (se 2 (by rfl) ⟨2342499, by rfl⟩ : syracuseStep 6246665 = 4684999) B4684999
theorem B4164443 : Blo 2193435 4164443 := bstep (se 1 (by rfl) ⟨3123332, by rfl⟩ : syracuseStep 4164443 = 6246665) B6246665
theorem B2776295 : Blo 2193435 2776295 := bstep (se 1 (by rfl) ⟨2082221, by rfl⟩ : syracuseStep 2776295 = 4164443) B4164443
theorem B7403453 : Blo 2193435 7403453 := bstep (se 3 (by rfl) ⟨1388147, by rfl⟩ : syracuseStep 7403453 = 2776295) B2776295
theorem B4935635 : Blo 2193435 4935635 := bstep (se 1 (by rfl) ⟨3701726, by rfl⟩ : syracuseStep 4935635 = 7403453) B7403453
theorem B3290423 : Blo 2193435 3290423 := bstep (se 1 (by rfl) ⟨2467817, by rfl⟩ : syracuseStep 3290423 = 4935635) B4935635
theorem B2193615 : Blo 2193435 2193615 := bstep (se 1 (by rfl) ⟨1645211, by rfl⟩ : syracuseStep 2193615 = 3290423) B3290423
theorem B3290429 : Blo 2193435 3290429 := bbase (se 3 (by rfl) ⟨616955, by rfl⟩ : syracuseStep 3290429 = 1233911) (by norm_num)
theorem B2193619 : Blo 2193435 2193619 := bstep (se 1 (by rfl) ⟨1645214, by rfl⟩ : syracuseStep 2193619 = 3290429) B3290429
theorem B4935653 : Blo 2193435 4935653 := bbase (se 4 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 4935653 = 925435) (by norm_num)
theorem B3290435 : Blo 2193435 3290435 := bstep (se 1 (by rfl) ⟨2467826, by rfl⟩ : syracuseStep 3290435 = 4935653) B4935653
theorem B2193623 : Blo 2193435 2193623 := bstep (se 1 (by rfl) ⟨1645217, by rfl⟩ : syracuseStep 2193623 = 3290435) B3290435
theorem B5552621 : Blo 2193435 5552621 := bbase (se 3 (by rfl) ⟨1041116, by rfl⟩ : syracuseStep 5552621 = 2082233) (by norm_num)
theorem B3701747 : Blo 2193435 3701747 := bstep (se 1 (by rfl) ⟨2776310, by rfl⟩ : syracuseStep 3701747 = 5552621) B5552621
theorem B2467831 : Blo 2193435 2467831 := bstep (se 1 (by rfl) ⟨1850873, by rfl⟩ : syracuseStep 2467831 = 3701747) B3701747
theorem B3290441 : Blo 2193435 3290441 := bstep (se 2 (by rfl) ⟨1233915, by rfl⟩ : syracuseStep 3290441 = 2467831) B2467831
theorem B2193627 : Blo 2193435 2193627 := bstep (se 1 (by rfl) ⟨1645220, by rfl⟩ : syracuseStep 2193627 = 3290441) B3290441
theorem B8894245 : Blo 2193435 8894245 := bbase (se 4 (by rfl) ⟨833835, by rfl⟩ : syracuseStep 8894245 = 1667671) (by norm_num)
theorem B11858993 : Blo 2193435 11858993 := bstep (se 2 (by rfl) ⟨4447122, by rfl⟩ : syracuseStep 11858993 = 8894245) B8894245
theorem B7905995 : Blo 2193435 7905995 := bstep (se 1 (by rfl) ⟨5929496, by rfl⟩ : syracuseStep 7905995 = 11858993) B11858993
theorem B5270663 : Blo 2193435 5270663 := bstep (se 1 (by rfl) ⟨3952997, by rfl⟩ : syracuseStep 5270663 = 7905995) B7905995
theorem B3513775 : Blo 2193435 3513775 := bstep (se 1 (by rfl) ⟨2635331, by rfl⟩ : syracuseStep 3513775 = 5270663) B5270663
theorem B4685033 : Blo 2193435 4685033 := bstep (se 2 (by rfl) ⟨1756887, by rfl⟩ : syracuseStep 4685033 = 3513775) B3513775
theorem B3123355 : Blo 2193435 3123355 := bstep (se 1 (by rfl) ⟨2342516, by rfl⟩ : syracuseStep 3123355 = 4685033) B4685033
theorem B4164473 : Blo 2193435 4164473 := bstep (se 2 (by rfl) ⟨1561677, by rfl⟩ : syracuseStep 4164473 = 3123355) B3123355
theorem B11105261 : Blo 2193435 11105261 := bstep (se 3 (by rfl) ⟨2082236, by rfl⟩ : syracuseStep 11105261 = 4164473) B4164473
theorem B7403507 : Blo 2193435 7403507 := bstep (se 1 (by rfl) ⟨5552630, by rfl⟩ : syracuseStep 7403507 = 11105261) B11105261
theorem B4935671 : Blo 2193435 4935671 := bstep (se 1 (by rfl) ⟨3701753, by rfl⟩ : syracuseStep 4935671 = 7403507) B7403507
theorem B3290447 : Blo 2193435 3290447 := bstep (se 1 (by rfl) ⟨2467835, by rfl⟩ : syracuseStep 3290447 = 4935671) B4935671
theorem B2193631 : Blo 2193435 2193631 := bstep (se 1 (by rfl) ⟨1645223, by rfl⟩ : syracuseStep 2193631 = 3290447) B3290447
theorem B3290453 : Blo 2193435 3290453 := bbase (se 13 (by rfl) ⟨602, by rfl⟩ : syracuseStep 3290453 = 1205) (by norm_num)
theorem B2193635 : Blo 2193435 2193635 := bstep (se 1 (by rfl) ⟨1645226, by rfl⟩ : syracuseStep 2193635 = 3290453) B3290453
theorem B2342525 : Blo 2193435 2342525 := bbase (se 3 (by rfl) ⟨439223, by rfl⟩ : syracuseStep 2342525 = 878447) (by norm_num)
theorem B6246733 : Blo 2193435 6246733 := bstep (se 3 (by rfl) ⟨1171262, by rfl⟩ : syracuseStep 6246733 = 2342525) B2342525
theorem B8328977 : Blo 2193435 8328977 := bstep (se 2 (by rfl) ⟨3123366, by rfl⟩ : syracuseStep 8328977 = 6246733) B6246733
theorem B5552651 : Blo 2193435 5552651 := bstep (se 1 (by rfl) ⟨4164488, by rfl⟩ : syracuseStep 5552651 = 8328977) B8328977
theorem B3701767 : Blo 2193435 3701767 := bstep (se 1 (by rfl) ⟨2776325, by rfl⟩ : syracuseStep 3701767 = 5552651) B5552651
theorem B4935689 : Blo 2193435 4935689 := bstep (se 2 (by rfl) ⟨1850883, by rfl⟩ : syracuseStep 4935689 = 3701767) B3701767
theorem B3290459 : Blo 2193435 3290459 := bstep (se 1 (by rfl) ⟨2467844, by rfl⟩ : syracuseStep 3290459 = 4935689) B4935689
theorem B2193639 : Blo 2193435 2193639 := bstep (se 1 (by rfl) ⟨1645229, by rfl⟩ : syracuseStep 2193639 = 3290459) B3290459
theorem B2467849 : Blo 2193435 2467849 := bbase (se 2 (by rfl) ⟨925443, by rfl⟩ : syracuseStep 2467849 = 1850887) (by norm_num)
theorem B3290465 : Blo 2193435 3290465 := bstep (se 2 (by rfl) ⟨1233924, by rfl⟩ : syracuseStep 3290465 = 2467849) B2467849
theorem B2193643 : Blo 2193435 2193643 := bstep (se 1 (by rfl) ⟨1645232, by rfl⟩ : syracuseStep 2193643 = 3290465) B3290465
theorem B2223577 : Blo 2193435 2223577 := bbase (se 2 (by rfl) ⟨833841, by rfl⟩ : syracuseStep 2223577 = 1667683) (by norm_num)
theorem B2964769 : Blo 2193435 2964769 := bstep (se 2 (by rfl) ⟨1111788, by rfl⟩ : syracuseStep 2964769 = 2223577) B2223577
theorem B15812101 : Blo 2193435 15812101 := bstep (se 4 (by rfl) ⟨1482384, by rfl⟩ : syracuseStep 15812101 = 2964769) B2964769
theorem B21082801 : Blo 2193435 21082801 := bstep (se 2 (by rfl) ⟨7906050, by rfl⟩ : syracuseStep 21082801 = 15812101) B15812101
theorem B28110401 : Blo 2193435 28110401 := bstep (se 2 (by rfl) ⟨10541400, by rfl⟩ : syracuseStep 28110401 = 21082801) B21082801
theorem B18740267 : Blo 2193435 18740267 := bstep (se 1 (by rfl) ⟨14055200, by rfl⟩ : syracuseStep 18740267 = 28110401) B28110401
theorem B12493511 : Blo 2193435 12493511 := bstep (se 1 (by rfl) ⟨9370133, by rfl⟩ : syracuseStep 12493511 = 18740267) B18740267
theorem B8329007 : Blo 2193435 8329007 := bstep (se 1 (by rfl) ⟨6246755, by rfl⟩ : syracuseStep 8329007 = 12493511) B12493511
theorem B5552671 : Blo 2193435 5552671 := bstep (se 1 (by rfl) ⟨4164503, by rfl⟩ : syracuseStep 5552671 = 8329007) B8329007
theorem B7403561 : Blo 2193435 7403561 := bstep (se 2 (by rfl) ⟨2776335, by rfl⟩ : syracuseStep 7403561 = 5552671) B5552671
theorem B4935707 : Blo 2193435 4935707 := bstep (se 1 (by rfl) ⟨3701780, by rfl⟩ : syracuseStep 4935707 = 7403561) B7403561
theorem B3290471 : Blo 2193435 3290471 := bstep (se 1 (by rfl) ⟨2467853, by rfl⟩ : syracuseStep 3290471 = 4935707) B4935707
theorem B2193647 : Blo 2193435 2193647 := bstep (se 1 (by rfl) ⟨1645235, by rfl⟩ : syracuseStep 2193647 = 3290471) B3290471
theorem B3290477 : Blo 2193435 3290477 := bbase (se 3 (by rfl) ⟨616964, by rfl⟩ : syracuseStep 3290477 = 1233929) (by norm_num)
theorem B2193651 : Blo 2193435 2193651 := bstep (se 1 (by rfl) ⟨1645238, by rfl⟩ : syracuseStep 2193651 = 3290477) B3290477
theorem B4935725 : Blo 2193435 4935725 := bbase (se 3 (by rfl) ⟨925448, by rfl⟩ : syracuseStep 4935725 = 1850897) (by norm_num)
theorem B3290483 : Blo 2193435 3290483 := bstep (se 1 (by rfl) ⟨2467862, by rfl⟩ : syracuseStep 3290483 = 4935725) B4935725
theorem B2193655 : Blo 2193435 2193655 := bstep (se 1 (by rfl) ⟨1645241, by rfl⟩ : syracuseStep 2193655 = 3290483) B3290483
theorem B10541461 : Blo 2193435 10541461 := bbase (se 6 (by rfl) ⟨247065, by rfl⟩ : syracuseStep 10541461 = 494131) (by norm_num)
theorem B14055281 : Blo 2193435 14055281 := bstep (se 2 (by rfl) ⟨5270730, by rfl⟩ : syracuseStep 14055281 = 10541461) B10541461
theorem B9370187 : Blo 2193435 9370187 := bstep (se 1 (by rfl) ⟨7027640, by rfl⟩ : syracuseStep 9370187 = 14055281) B14055281
theorem B6246791 : Blo 2193435 6246791 := bstep (se 1 (by rfl) ⟨4685093, by rfl⟩ : syracuseStep 6246791 = 9370187) B9370187
theorem B4164527 : Blo 2193435 4164527 := bstep (se 1 (by rfl) ⟨3123395, by rfl⟩ : syracuseStep 4164527 = 6246791) B6246791
theorem B2776351 : Blo 2193435 2776351 := bstep (se 1 (by rfl) ⟨2082263, by rfl⟩ : syracuseStep 2776351 = 4164527) B4164527
theorem B3701801 : Blo 2193435 3701801 := bstep (se 2 (by rfl) ⟨1388175, by rfl⟩ : syracuseStep 3701801 = 2776351) B2776351
theorem B2467867 : Blo 2193435 2467867 := bstep (se 1 (by rfl) ⟨1850900, by rfl⟩ : syracuseStep 2467867 = 3701801) B3701801
theorem B3290489 : Blo 2193435 3290489 := bstep (se 2 (by rfl) ⟨1233933, by rfl⟩ : syracuseStep 3290489 = 2467867) B2467867
theorem B2193659 : Blo 2193435 2193659 := bstep (se 1 (by rfl) ⟨1645244, by rfl⟩ : syracuseStep 2193659 = 3290489) B3290489
theorem B10541477 : Blo 2193435 10541477 := bbase (se 4 (by rfl) ⟨988263, by rfl⟩ : syracuseStep 10541477 = 1976527) (by norm_num)
theorem B7027651 : Blo 2193435 7027651 := bstep (se 1 (by rfl) ⟨5270738, by rfl⟩ : syracuseStep 7027651 = 10541477) B10541477
theorem B37480805 : Blo 2193435 37480805 := bstep (se 4 (by rfl) ⟨3513825, by rfl⟩ : syracuseStep 37480805 = 7027651) B7027651
theorem B24987203 : Blo 2193435 24987203 := bstep (se 1 (by rfl) ⟨18740402, by rfl⟩ : syracuseStep 24987203 = 37480805) B37480805
theorem B16658135 : Blo 2193435 16658135 := bstep (se 1 (by rfl) ⟨12493601, by rfl⟩ : syracuseStep 16658135 = 24987203) B24987203
theorem B11105423 : Blo 2193435 11105423 := bstep (se 1 (by rfl) ⟨8329067, by rfl⟩ : syracuseStep 11105423 = 16658135) B16658135
theorem B7403615 : Blo 2193435 7403615 := bstep (se 1 (by rfl) ⟨5552711, by rfl⟩ : syracuseStep 7403615 = 11105423) B11105423
theorem B4935743 : Blo 2193435 4935743 := bstep (se 1 (by rfl) ⟨3701807, by rfl⟩ : syracuseStep 4935743 = 7403615) B7403615
theorem B3290495 : Blo 2193435 3290495 := bstep (se 1 (by rfl) ⟨2467871, by rfl⟩ : syracuseStep 3290495 = 4935743) B4935743
theorem B2193663 : Blo 2193435 2193663 := bstep (se 1 (by rfl) ⟨1645247, by rfl⟩ : syracuseStep 2193663 = 3290495) B3290495
theorem B3290501 : Blo 2193435 3290501 := bbase (se 4 (by rfl) ⟨308484, by rfl⟩ : syracuseStep 3290501 = 616969) (by norm_num)
theorem B2193667 : Blo 2193435 2193667 := bstep (se 1 (by rfl) ⟨1645250, by rfl⟩ : syracuseStep 2193667 = 3290501) B3290501
theorem B3701821 : Blo 2193435 3701821 := bbase (se 3 (by rfl) ⟨694091, by rfl⟩ : syracuseStep 3701821 = 1388183) (by norm_num)
theorem B4935761 : Blo 2193435 4935761 := bstep (se 2 (by rfl) ⟨1850910, by rfl⟩ : syracuseStep 4935761 = 3701821) B3701821
theorem B3290507 : Blo 2193435 3290507 := bstep (se 1 (by rfl) ⟨2467880, by rfl⟩ : syracuseStep 3290507 = 4935761) B4935761
theorem B2193671 : Blo 2193435 2193671 := bstep (se 1 (by rfl) ⟨1645253, by rfl⟩ : syracuseStep 2193671 = 3290507) B3290507
theorem B2467885 : Blo 2193435 2467885 := bbase (se 3 (by rfl) ⟨462728, by rfl⟩ : syracuseStep 2467885 = 925457) (by norm_num)
theorem B3290513 : Blo 2193435 3290513 := bstep (se 2 (by rfl) ⟨1233942, by rfl⟩ : syracuseStep 3290513 = 2467885) B2467885
theorem B2193675 : Blo 2193435 2193675 := bstep (se 1 (by rfl) ⟨1645256, by rfl⟩ : syracuseStep 2193675 = 3290513) B3290513
theorem B7403669 : Blo 2193435 7403669 := bbase (se 6 (by rfl) ⟨173523, by rfl⟩ : syracuseStep 7403669 = 347047) (by norm_num)
theorem B4935779 : Blo 2193435 4935779 := bstep (se 1 (by rfl) ⟨3701834, by rfl⟩ : syracuseStep 4935779 = 7403669) B7403669
theorem B3290519 : Blo 2193435 3290519 := bstep (se 1 (by rfl) ⟨2467889, by rfl⟩ : syracuseStep 3290519 = 4935779) B4935779
theorem B2193679 : Blo 2193435 2193679 := bstep (se 1 (by rfl) ⟨1645259, by rfl⟩ : syracuseStep 2193679 = 3290519) B3290519
theorem B3290525 : Blo 2193435 3290525 := bbase (se 3 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 3290525 = 1233947) (by norm_num)
theorem B2193683 : Blo 2193435 2193683 := bstep (se 1 (by rfl) ⟨1645262, by rfl⟩ : syracuseStep 2193683 = 3290525) B3290525
theorem B4935797 : Blo 2193435 4935797 := bbase (se 5 (by rfl) ⟨231365, by rfl⟩ : syracuseStep 4935797 = 462731) (by norm_num)
theorem B3290531 : Blo 2193435 3290531 := bstep (se 1 (by rfl) ⟨2467898, by rfl⟩ : syracuseStep 3290531 = 4935797) B4935797
theorem B2193687 : Blo 2193435 2193687 := bstep (se 1 (by rfl) ⟨1645265, by rfl⟩ : syracuseStep 2193687 = 3290531) B3290531
theorem B11859317 : Blo 2193435 11859317 := bbase (se 5 (by rfl) ⟨555905, by rfl⟩ : syracuseStep 11859317 = 1111811) (by norm_num)
theorem B7906211 : Blo 2193435 7906211 := bstep (se 1 (by rfl) ⟨5929658, by rfl⟩ : syracuseStep 7906211 = 11859317) B11859317
theorem B5270807 : Blo 2193435 5270807 := bstep (se 1 (by rfl) ⟨3953105, by rfl⟩ : syracuseStep 5270807 = 7906211) B7906211
theorem B3513871 : Blo 2193435 3513871 := bstep (se 1 (by rfl) ⟨2635403, by rfl⟩ : syracuseStep 3513871 = 5270807) B5270807
theorem B18740645 : Blo 2193435 18740645 := bstep (se 4 (by rfl) ⟨1756935, by rfl⟩ : syracuseStep 18740645 = 3513871) B3513871
theorem B12493763 : Blo 2193435 12493763 := bstep (se 1 (by rfl) ⟨9370322, by rfl⟩ : syracuseStep 12493763 = 18740645) B18740645
theorem B8329175 : Blo 2193435 8329175 := bstep (se 1 (by rfl) ⟨6246881, by rfl⟩ : syracuseStep 8329175 = 12493763) B12493763
theorem B5552783 : Blo 2193435 5552783 := bstep (se 1 (by rfl) ⟨4164587, by rfl⟩ : syracuseStep 5552783 = 8329175) B8329175
theorem B3701855 : Blo 2193435 3701855 := bstep (se 1 (by rfl) ⟨2776391, by rfl⟩ : syracuseStep 3701855 = 5552783) B5552783
theorem B2467903 : Blo 2193435 2467903 := bstep (se 1 (by rfl) ⟨1850927, by rfl⟩ : syracuseStep 2467903 = 3701855) B3701855
theorem B3290537 : Blo 2193435 3290537 := bstep (se 2 (by rfl) ⟨1233951, by rfl⟩ : syracuseStep 3290537 = 2467903) B2467903
theorem B2193691 : Blo 2193435 2193691 := bstep (se 1 (by rfl) ⟨1645268, by rfl⟩ : syracuseStep 2193691 = 3290537) B3290537
theorem B8329189 : Blo 2193435 8329189 := bbase (se 4 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 8329189 = 1561723) (by norm_num)
theorem B11105585 : Blo 2193435 11105585 := bstep (se 2 (by rfl) ⟨4164594, by rfl⟩ : syracuseStep 11105585 = 8329189) B8329189
theorem B7403723 : Blo 2193435 7403723 := bstep (se 1 (by rfl) ⟨5552792, by rfl⟩ : syracuseStep 7403723 = 11105585) B11105585
theorem B4935815 : Blo 2193435 4935815 := bstep (se 1 (by rfl) ⟨3701861, by rfl⟩ : syracuseStep 4935815 = 7403723) B7403723
theorem B3290543 : Blo 2193435 3290543 := bstep (se 1 (by rfl) ⟨2467907, by rfl⟩ : syracuseStep 3290543 = 4935815) B4935815
theorem B2193695 : Blo 2193435 2193695 := bstep (se 1 (by rfl) ⟨1645271, by rfl⟩ : syracuseStep 2193695 = 3290543) B3290543
theorem B3290549 : Blo 2193435 3290549 := bbase (se 5 (by rfl) ⟨154244, by rfl⟩ : syracuseStep 3290549 = 308489) (by norm_num)
theorem B2193699 : Blo 2193435 2193699 := bstep (se 1 (by rfl) ⟨1645274, by rfl⟩ : syracuseStep 2193699 = 3290549) B3290549
theorem B5552813 : Blo 2193435 5552813 := bbase (se 3 (by rfl) ⟨1041152, by rfl⟩ : syracuseStep 5552813 = 2082305) (by norm_num)
theorem B3701875 : Blo 2193435 3701875 := bstep (se 1 (by rfl) ⟨2776406, by rfl⟩ : syracuseStep 3701875 = 5552813) B5552813
theorem B4935833 : Blo 2193435 4935833 := bstep (se 2 (by rfl) ⟨1850937, by rfl⟩ : syracuseStep 4935833 = 3701875) B3701875
theorem B3290555 : Blo 2193435 3290555 := bstep (se 1 (by rfl) ⟨2467916, by rfl⟩ : syracuseStep 3290555 = 4935833) B4935833
theorem B2193703 : Blo 2193435 2193703 := bstep (se 1 (by rfl) ⟨1645277, by rfl⟩ : syracuseStep 2193703 = 3290555) B3290555
theorem B2467921 : Blo 2193435 2467921 := bbase (se 2 (by rfl) ⟨925470, by rfl⟩ : syracuseStep 2467921 = 1850941) (by norm_num)
theorem B3290561 : Blo 2193435 3290561 := bstep (se 2 (by rfl) ⟨1233960, by rfl⟩ : syracuseStep 3290561 = 2467921) B2467921
theorem B2193707 : Blo 2193435 2193707 := bstep (se 1 (by rfl) ⟨1645280, by rfl⟩ : syracuseStep 2193707 = 3290561) B3290561
theorem B3123469 : Blo 2193435 3123469 := bbase (se 3 (by rfl) ⟨585650, by rfl⟩ : syracuseStep 3123469 = 1171301) (by norm_num)
theorem B4164625 : Blo 2193435 4164625 := bstep (se 2 (by rfl) ⟨1561734, by rfl⟩ : syracuseStep 4164625 = 3123469) B3123469
theorem B5552833 : Blo 2193435 5552833 := bstep (se 2 (by rfl) ⟨2082312, by rfl⟩ : syracuseStep 5552833 = 4164625) B4164625
theorem B7403777 : Blo 2193435 7403777 := bstep (se 2 (by rfl) ⟨2776416, by rfl⟩ : syracuseStep 7403777 = 5552833) B5552833
theorem B4935851 : Blo 2193435 4935851 := bstep (se 1 (by rfl) ⟨3701888, by rfl⟩ : syracuseStep 4935851 = 7403777) B7403777
theorem B3290567 : Blo 2193435 3290567 := bstep (se 1 (by rfl) ⟨2467925, by rfl⟩ : syracuseStep 3290567 = 4935851) B4935851
theorem B2193711 : Blo 2193435 2193711 := bstep (se 1 (by rfl) ⟨1645283, by rfl⟩ : syracuseStep 2193711 = 3290567) B3290567
theorem B3290573 : Blo 2193435 3290573 := bbase (se 3 (by rfl) ⟨616982, by rfl⟩ : syracuseStep 3290573 = 1233965) (by norm_num)
theorem B2193715 : Blo 2193435 2193715 := bstep (se 1 (by rfl) ⟨1645286, by rfl⟩ : syracuseStep 2193715 = 3290573) B3290573
theorem B4935869 : Blo 2193435 4935869 := bbase (se 3 (by rfl) ⟨925475, by rfl⟩ : syracuseStep 4935869 = 1850951) (by norm_num)
theorem B3290579 : Blo 2193435 3290579 := bstep (se 1 (by rfl) ⟨2467934, by rfl⟩ : syracuseStep 3290579 = 4935869) B4935869
theorem B2193719 : Blo 2193435 2193719 := bstep (se 1 (by rfl) ⟨1645289, by rfl⟩ : syracuseStep 2193719 = 3290579) B3290579
theorem B3701909 : Blo 2193435 3701909 := bbase (se 6 (by rfl) ⟨86763, by rfl⟩ : syracuseStep 3701909 = 173527) (by norm_num)
theorem B2467939 : Blo 2193435 2467939 := bstep (se 1 (by rfl) ⟨1850954, by rfl⟩ : syracuseStep 2467939 = 3701909) B3701909
theorem B3290585 : Blo 2193435 3290585 := bstep (se 2 (by rfl) ⟨1233969, by rfl⟩ : syracuseStep 3290585 = 2467939) B2467939
theorem B2193723 : Blo 2193435 2193723 := bstep (se 1 (by rfl) ⟨1645292, by rfl⟩ : syracuseStep 2193723 = 3290585) B3290585
theorem B11859509 : Blo 2193435 11859509 := bbase (se 5 (by rfl) ⟨555914, by rfl⟩ : syracuseStep 11859509 = 1111829) (by norm_num)
theorem B7906339 : Blo 2193435 7906339 := bstep (se 1 (by rfl) ⟨5929754, by rfl⟩ : syracuseStep 7906339 = 11859509) B11859509
theorem B10541785 : Blo 2193435 10541785 := bstep (se 2 (by rfl) ⟨3953169, by rfl⟩ : syracuseStep 10541785 = 7906339) B7906339
theorem B14055713 : Blo 2193435 14055713 := bstep (se 2 (by rfl) ⟨5270892, by rfl⟩ : syracuseStep 14055713 = 10541785) B10541785
theorem B9370475 : Blo 2193435 9370475 := bstep (se 1 (by rfl) ⟨7027856, by rfl⟩ : syracuseStep 9370475 = 14055713) B14055713
theorem B6246983 : Blo 2193435 6246983 := bstep (se 1 (by rfl) ⟨4685237, by rfl⟩ : syracuseStep 6246983 = 9370475) B9370475
theorem B16658621 : Blo 2193435 16658621 := bstep (se 3 (by rfl) ⟨3123491, by rfl⟩ : syracuseStep 16658621 = 6246983) B6246983
theorem B11105747 : Blo 2193435 11105747 := bstep (se 1 (by rfl) ⟨8329310, by rfl⟩ : syracuseStep 11105747 = 16658621) B16658621
theorem B7403831 : Blo 2193435 7403831 := bstep (se 1 (by rfl) ⟨5552873, by rfl⟩ : syracuseStep 7403831 = 11105747) B11105747
theorem B4935887 : Blo 2193435 4935887 := bstep (se 1 (by rfl) ⟨3701915, by rfl⟩ : syracuseStep 4935887 = 7403831) B7403831
theorem B3290591 : Blo 2193435 3290591 := bstep (se 1 (by rfl) ⟨2467943, by rfl⟩ : syracuseStep 3290591 = 4935887) B4935887
theorem B2193727 : Blo 2193435 2193727 := bstep (se 1 (by rfl) ⟨1645295, by rfl⟩ : syracuseStep 2193727 = 3290591) B3290591
theorem B3290597 : Blo 2193435 3290597 := bbase (se 4 (by rfl) ⟨308493, by rfl⟩ : syracuseStep 3290597 = 616987) (by norm_num)
theorem B2193731 : Blo 2193435 2193731 := bstep (se 1 (by rfl) ⟨1645298, by rfl⟩ : syracuseStep 2193731 = 3290597) B3290597
theorem B4447333 : Blo 2193435 4447333 := bbase (se 4 (by rfl) ⟨416937, by rfl⟩ : syracuseStep 4447333 = 833875) (by norm_num)
theorem B5929777 : Blo 2193435 5929777 := bstep (se 2 (by rfl) ⟨2223666, by rfl⟩ : syracuseStep 5929777 = 4447333) B4447333
theorem B31625477 : Blo 2193435 31625477 := bstep (se 4 (by rfl) ⟨2964888, by rfl⟩ : syracuseStep 31625477 = 5929777) B5929777
theorem B21083651 : Blo 2193435 21083651 := bstep (se 1 (by rfl) ⟨15812738, by rfl⟩ : syracuseStep 21083651 = 31625477) B31625477
theorem B14055767 : Blo 2193435 14055767 := bstep (se 1 (by rfl) ⟨10541825, by rfl⟩ : syracuseStep 14055767 = 21083651) B21083651
theorem B9370511 : Blo 2193435 9370511 := bstep (se 1 (by rfl) ⟨7027883, by rfl⟩ : syracuseStep 9370511 = 14055767) B14055767
theorem B6247007 : Blo 2193435 6247007 := bstep (se 1 (by rfl) ⟨4685255, by rfl⟩ : syracuseStep 6247007 = 9370511) B9370511
theorem B4164671 : Blo 2193435 4164671 := bstep (se 1 (by rfl) ⟨3123503, by rfl⟩ : syracuseStep 4164671 = 6247007) B6247007
theorem B2776447 : Blo 2193435 2776447 := bstep (se 1 (by rfl) ⟨2082335, by rfl⟩ : syracuseStep 2776447 = 4164671) B4164671
theorem B3701929 : Blo 2193435 3701929 := bstep (se 2 (by rfl) ⟨1388223, by rfl⟩ : syracuseStep 3701929 = 2776447) B2776447
theorem B4935905 : Blo 2193435 4935905 := bstep (se 2 (by rfl) ⟨1850964, by rfl⟩ : syracuseStep 4935905 = 3701929) B3701929
theorem B3290603 : Blo 2193435 3290603 := bstep (se 1 (by rfl) ⟨2467952, by rfl⟩ : syracuseStep 3290603 = 4935905) B4935905
theorem B2193735 : Blo 2193435 2193735 := bstep (se 1 (by rfl) ⟨1645301, by rfl⟩ : syracuseStep 2193735 = 3290603) B3290603
theorem B2467957 : Blo 2193435 2467957 := bbase (se 5 (by rfl) ⟨115685, by rfl⟩ : syracuseStep 2467957 = 231371) (by norm_num)
theorem B3290609 : Blo 2193435 3290609 := bstep (se 2 (by rfl) ⟨1233978, by rfl⟩ : syracuseStep 3290609 = 2467957) B2467957
theorem B2193739 : Blo 2193435 2193739 := bstep (se 1 (by rfl) ⟨1645304, by rfl⟩ : syracuseStep 2193739 = 3290609) B3290609
theorem B2776457 : Blo 2193435 2776457 := bbase (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) (by norm_num)
theorem B7403885 : Blo 2193435 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B4935923 : Blo 2193435 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B3290615 : Blo 2193435 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B2193743 : Blo 2193435 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B3290621 : Blo 2193435 3290621 := bbase (se 3 (by rfl) ⟨616991, by rfl⟩ : syracuseStep 3290621 = 1233983) (by norm_num)
theorem B2193747 : Blo 2193435 2193747 := bstep (se 1 (by rfl) ⟨1645310, by rfl⟩ : syracuseStep 2193747 = 3290621) B3290621
theorem B4935941 : Blo 2193435 4935941 := bbase (se 4 (by rfl) ⟨462744, by rfl⟩ : syracuseStep 4935941 = 925489) (by norm_num)
theorem B3290627 : Blo 2193435 3290627 := bstep (se 1 (by rfl) ⟨2467970, by rfl⟩ : syracuseStep 3290627 = 4935941) B4935941
theorem B2193751 : Blo 2193435 2193751 := bstep (se 1 (by rfl) ⟨1645313, by rfl⟩ : syracuseStep 2193751 = 3290627) B3290627
theorem B4164709 : Blo 2193435 4164709 := bbase (se 4 (by rfl) ⟨390441, by rfl⟩ : syracuseStep 4164709 = 780883) (by norm_num)
theorem B5552945 : Blo 2193435 5552945 := bstep (se 2 (by rfl) ⟨2082354, by rfl⟩ : syracuseStep 5552945 = 4164709) B4164709
theorem B3701963 : Blo 2193435 3701963 := bstep (se 1 (by rfl) ⟨2776472, by rfl⟩ : syracuseStep 3701963 = 5552945) B5552945
theorem B2467975 : Blo 2193435 2467975 := bstep (se 1 (by rfl) ⟨1850981, by rfl⟩ : syracuseStep 2467975 = 3701963) B3701963
theorem B3290633 : Blo 2193435 3290633 := bstep (se 2 (by rfl) ⟨1233987, by rfl⟩ : syracuseStep 3290633 = 2467975) B2467975
theorem B2193755 : Blo 2193435 2193755 := bstep (se 1 (by rfl) ⟨1645316, by rfl⟩ : syracuseStep 2193755 = 3290633) B3290633
theorem B11105909 : Blo 2193435 11105909 := bbase (se 5 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 11105909 = 1041179) (by norm_num)
theorem B7403939 : Blo 2193435 7403939 := bstep (se 1 (by rfl) ⟨5552954, by rfl⟩ : syracuseStep 7403939 = 11105909) B11105909
theorem B4935959 : Blo 2193435 4935959 := bstep (se 1 (by rfl) ⟨3701969, by rfl⟩ : syracuseStep 4935959 = 7403939) B7403939
theorem B3290639 : Blo 2193435 3290639 := bstep (se 1 (by rfl) ⟨2467979, by rfl⟩ : syracuseStep 3290639 = 4935959) B4935959
theorem B2193759 : Blo 2193435 2193759 := bstep (se 1 (by rfl) ⟨1645319, by rfl⟩ : syracuseStep 2193759 = 3290639) B3290639
theorem B3290645 : Blo 2193435 3290645 := bbase (se 6 (by rfl) ⟨77124, by rfl⟩ : syracuseStep 3290645 = 154249) (by norm_num)
theorem B2193763 : Blo 2193435 2193763 := bstep (se 1 (by rfl) ⟨1645322, by rfl⟩ : syracuseStep 2193763 = 3290645) B3290645
theorem B5270989 : Blo 2193435 5270989 := bbase (se 3 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 5270989 = 1976621) (by norm_num)
theorem B7027985 : Blo 2193435 7027985 := bstep (se 2 (by rfl) ⟨2635494, by rfl⟩ : syracuseStep 7027985 = 5270989) B5270989
theorem B18741293 : Blo 2193435 18741293 := bstep (se 3 (by rfl) ⟨3513992, by rfl⟩ : syracuseStep 18741293 = 7027985) B7027985
theorem B12494195 : Blo 2193435 12494195 := bstep (se 1 (by rfl) ⟨9370646, by rfl⟩ : syracuseStep 12494195 = 18741293) B18741293
theorem B8329463 : Blo 2193435 8329463 := bstep (se 1 (by rfl) ⟨6247097, by rfl⟩ : syracuseStep 8329463 = 12494195) B12494195
theorem B5552975 : Blo 2193435 5552975 := bstep (se 1 (by rfl) ⟨4164731, by rfl⟩ : syracuseStep 5552975 = 8329463) B8329463
theorem B3701983 : Blo 2193435 3701983 := bstep (se 1 (by rfl) ⟨2776487, by rfl⟩ : syracuseStep 3701983 = 5552975) B5552975
theorem B4935977 : Blo 2193435 4935977 := bstep (se 2 (by rfl) ⟨1850991, by rfl⟩ : syracuseStep 4935977 = 3701983) B3701983
theorem B3290651 : Blo 2193435 3290651 := bstep (se 1 (by rfl) ⟨2467988, by rfl⟩ : syracuseStep 3290651 = 4935977) B4935977
theorem B2193767 : Blo 2193435 2193767 := bstep (se 1 (by rfl) ⟨1645325, by rfl⟩ : syracuseStep 2193767 = 3290651) B3290651
theorem B2467993 : Blo 2193435 2467993 := bbase (se 2 (by rfl) ⟨925497, by rfl⟩ : syracuseStep 2467993 = 1850995) (by norm_num)
theorem B3290657 : Blo 2193435 3290657 := bstep (se 2 (by rfl) ⟨1233996, by rfl⟩ : syracuseStep 3290657 = 2467993) B2467993
theorem B2193771 : Blo 2193435 2193771 := bstep (se 1 (by rfl) ⟨1645328, by rfl⟩ : syracuseStep 2193771 = 3290657) B3290657
theorem B8329493 : Blo 2193435 8329493 := bbase (se 6 (by rfl) ⟨195222, by rfl⟩ : syracuseStep 8329493 = 390445) (by norm_num)
theorem B5552995 : Blo 2193435 5552995 := bstep (se 1 (by rfl) ⟨4164746, by rfl⟩ : syracuseStep 5552995 = 8329493) B8329493
theorem B7403993 : Blo 2193435 7403993 := bstep (se 2 (by rfl) ⟨2776497, by rfl⟩ : syracuseStep 7403993 = 5552995) B5552995
theorem B4935995 : Blo 2193435 4935995 := bstep (se 1 (by rfl) ⟨3701996, by rfl⟩ : syracuseStep 4935995 = 7403993) B7403993
theorem B3290663 : Blo 2193435 3290663 := bstep (se 1 (by rfl) ⟨2467997, by rfl⟩ : syracuseStep 3290663 = 4935995) B4935995
theorem B2193775 : Blo 2193435 2193775 := bstep (se 1 (by rfl) ⟨1645331, by rfl⟩ : syracuseStep 2193775 = 3290663) B3290663
theorem B3290669 : Blo 2193435 3290669 := bbase (se 3 (by rfl) ⟨617000, by rfl⟩ : syracuseStep 3290669 = 1234001) (by norm_num)
theorem B2193779 : Blo 2193435 2193779 := bstep (se 1 (by rfl) ⟨1645334, by rfl⟩ : syracuseStep 2193779 = 3290669) B3290669
theorem B4936013 : Blo 2193435 4936013 := bbase (se 3 (by rfl) ⟨925502, by rfl⟩ : syracuseStep 4936013 = 1851005) (by norm_num)
theorem B3290675 : Blo 2193435 3290675 := bstep (se 1 (by rfl) ⟨2468006, by rfl⟩ : syracuseStep 3290675 = 4936013) B4936013
theorem B2193783 : Blo 2193435 2193783 := bstep (se 1 (by rfl) ⟨1645337, by rfl⟩ : syracuseStep 2193783 = 3290675) B3290675
theorem B2776513 : Blo 2193435 2776513 := bbase (se 2 (by rfl) ⟨1041192, by rfl⟩ : syracuseStep 2776513 = 2082385) (by norm_num)
theorem B3702017 : Blo 2193435 3702017 := bstep (se 2 (by rfl) ⟨1388256, by rfl⟩ : syracuseStep 3702017 = 2776513) B2776513
theorem B2468011 : Blo 2193435 2468011 := bstep (se 1 (by rfl) ⟨1851008, by rfl⟩ : syracuseStep 2468011 = 3702017) B3702017
theorem B3290681 : Blo 2193435 3290681 := bstep (se 2 (by rfl) ⟨1234005, by rfl⟩ : syracuseStep 3290681 = 2468011) B2468011
theorem B2193787 : Blo 2193435 2193787 := bstep (se 1 (by rfl) ⟨1645340, by rfl⟩ : syracuseStep 2193787 = 3290681) B3290681
theorem B2501689 : Blo 2193435 2501689 := bbase (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) (by norm_num)
theorem B3335585 : Blo 2193435 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B8894893 : Blo 2193435 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B11859857 : Blo 2193435 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B7906571 : Blo 2193435 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B5271047 : Blo 2193435 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B3514031 : Blo 2193435 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B2342687 : Blo 2193435 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B24988661 : Blo 2193435 24988661 := bstep (se 5 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 24988661 = 2342687) B2342687
theorem B16659107 : Blo 2193435 16659107 := bstep (se 1 (by rfl) ⟨12494330, by rfl⟩ : syracuseStep 16659107 = 24988661) B24988661
theorem B11106071 : Blo 2193435 11106071 := bstep (se 1 (by rfl) ⟨8329553, by rfl⟩ : syracuseStep 11106071 = 16659107) B16659107
theorem B7404047 : Blo 2193435 7404047 := bstep (se 1 (by rfl) ⟨5553035, by rfl⟩ : syracuseStep 7404047 = 11106071) B11106071
theorem B4936031 : Blo 2193435 4936031 := bstep (se 1 (by rfl) ⟨3702023, by rfl⟩ : syracuseStep 4936031 = 7404047) B7404047
theorem B3290687 : Blo 2193435 3290687 := bstep (se 1 (by rfl) ⟨2468015, by rfl⟩ : syracuseStep 3290687 = 4936031) B4936031
theorem B2193791 : Blo 2193435 2193791 := bstep (se 1 (by rfl) ⟨1645343, by rfl⟩ : syracuseStep 2193791 = 3290687) B3290687
theorem B3290693 : Blo 2193435 3290693 := bbase (se 4 (by rfl) ⟨308502, by rfl⟩ : syracuseStep 3290693 = 617005) (by norm_num)
theorem B2193795 : Blo 2193435 2193795 := bstep (se 1 (by rfl) ⟨1645346, by rfl⟩ : syracuseStep 2193795 = 3290693) B3290693
theorem B3702037 : Blo 2193435 3702037 := bbase (se 6 (by rfl) ⟨86766, by rfl⟩ : syracuseStep 3702037 = 173533) (by norm_num)
theorem B4936049 : Blo 2193435 4936049 := bstep (se 2 (by rfl) ⟨1851018, by rfl⟩ : syracuseStep 4936049 = 3702037) B3702037
theorem B3290699 : Blo 2193435 3290699 := bstep (se 1 (by rfl) ⟨2468024, by rfl⟩ : syracuseStep 3290699 = 4936049) B4936049
theorem B2193799 : Blo 2193435 2193799 := bstep (se 1 (by rfl) ⟨1645349, by rfl⟩ : syracuseStep 2193799 = 3290699) B3290699
theorem B2468029 : Blo 2193435 2468029 := bbase (se 3 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 2468029 = 925511) (by norm_num)
theorem B3290705 : Blo 2193435 3290705 := bstep (se 2 (by rfl) ⟨1234014, by rfl⟩ : syracuseStep 3290705 = 2468029) B2468029
theorem B2193803 : Blo 2193435 2193803 := bstep (se 1 (by rfl) ⟨1645352, by rfl⟩ : syracuseStep 2193803 = 3290705) B3290705
theorem B7404101 : Blo 2193435 7404101 := bbase (se 4 (by rfl) ⟨694134, by rfl⟩ : syracuseStep 7404101 = 1388269) (by norm_num)
theorem B4936067 : Blo 2193435 4936067 := bstep (se 1 (by rfl) ⟨3702050, by rfl⟩ : syracuseStep 4936067 = 7404101) B7404101
theorem B3290711 : Blo 2193435 3290711 := bstep (se 1 (by rfl) ⟨2468033, by rfl⟩ : syracuseStep 3290711 = 4936067) B4936067
theorem B2193807 : Blo 2193435 2193807 := bstep (se 1 (by rfl) ⟨1645355, by rfl⟩ : syracuseStep 2193807 = 3290711) B3290711
theorem B3290717 : Blo 2193435 3290717 := bbase (se 3 (by rfl) ⟨617009, by rfl⟩ : syracuseStep 3290717 = 1234019) (by norm_num)
theorem B2193811 : Blo 2193435 2193811 := bstep (se 1 (by rfl) ⟨1645358, by rfl⟩ : syracuseStep 2193811 = 3290717) B3290717
theorem B4936085 : Blo 2193435 4936085 := bbase (se 6 (by rfl) ⟨115689, by rfl⟩ : syracuseStep 4936085 = 231379) (by norm_num)
theorem B3290723 : Blo 2193435 3290723 := bstep (se 1 (by rfl) ⟨2468042, by rfl⟩ : syracuseStep 3290723 = 4936085) B4936085
theorem B2193815 : Blo 2193435 2193815 := bstep (se 1 (by rfl) ⟨1645361, by rfl⟩ : syracuseStep 2193815 = 3290723) B3290723
theorem B5930005 : Blo 2193435 5930005 := bbase (se 6 (by rfl) ⟨138984, by rfl⟩ : syracuseStep 5930005 = 277969) (by norm_num)
theorem B7906673 : Blo 2193435 7906673 := bstep (se 2 (by rfl) ⟨2965002, by rfl⟩ : syracuseStep 7906673 = 5930005) B5930005
theorem B5271115 : Blo 2193435 5271115 := bstep (se 1 (by rfl) ⟨3953336, by rfl⟩ : syracuseStep 5271115 = 7906673) B7906673
theorem B7028153 : Blo 2193435 7028153 := bstep (se 2 (by rfl) ⟨2635557, by rfl⟩ : syracuseStep 7028153 = 5271115) B5271115
theorem B4685435 : Blo 2193435 4685435 := bstep (se 1 (by rfl) ⟨3514076, by rfl⟩ : syracuseStep 4685435 = 7028153) B7028153
theorem B3123623 : Blo 2193435 3123623 := bstep (se 1 (by rfl) ⟨2342717, by rfl⟩ : syracuseStep 3123623 = 4685435) B4685435
theorem B8329661 : Blo 2193435 8329661 := bstep (se 3 (by rfl) ⟨1561811, by rfl⟩ : syracuseStep 8329661 = 3123623) B3123623
theorem B5553107 : Blo 2193435 5553107 := bstep (se 1 (by rfl) ⟨4164830, by rfl⟩ : syracuseStep 5553107 = 8329661) B8329661
theorem B3702071 : Blo 2193435 3702071 := bstep (se 1 (by rfl) ⟨2776553, by rfl⟩ : syracuseStep 3702071 = 5553107) B5553107
theorem B2468047 : Blo 2193435 2468047 := bstep (se 1 (by rfl) ⟨1851035, by rfl⟩ : syracuseStep 2468047 = 3702071) B3702071
theorem B3290729 : Blo 2193435 3290729 := bstep (se 2 (by rfl) ⟨1234023, by rfl⟩ : syracuseStep 3290729 = 2468047) B2468047
theorem B2193819 : Blo 2193435 2193819 := bstep (se 1 (by rfl) ⟨1645364, by rfl⟩ : syracuseStep 2193819 = 3290729) B3290729
theorem B9370885 : Blo 2193435 9370885 := bbase (se 4 (by rfl) ⟨878520, by rfl⟩ : syracuseStep 9370885 = 1757041) (by norm_num)
theorem B12494513 : Blo 2193435 12494513 := bstep (se 2 (by rfl) ⟨4685442, by rfl⟩ : syracuseStep 12494513 = 9370885) B9370885
theorem B8329675 : Blo 2193435 8329675 := bstep (se 1 (by rfl) ⟨6247256, by rfl⟩ : syracuseStep 8329675 = 12494513) B12494513
theorem B11106233 : Blo 2193435 11106233 := bstep (se 2 (by rfl) ⟨4164837, by rfl⟩ : syracuseStep 11106233 = 8329675) B8329675
theorem B7404155 : Blo 2193435 7404155 := bstep (se 1 (by rfl) ⟨5553116, by rfl⟩ : syracuseStep 7404155 = 11106233) B11106233
theorem B4936103 : Blo 2193435 4936103 := bstep (se 1 (by rfl) ⟨3702077, by rfl⟩ : syracuseStep 4936103 = 7404155) B7404155
theorem B3290735 : Blo 2193435 3290735 := bstep (se 1 (by rfl) ⟨2468051, by rfl⟩ : syracuseStep 3290735 = 4936103) B4936103
theorem B2193823 : Blo 2193435 2193823 := bstep (se 1 (by rfl) ⟨1645367, by rfl⟩ : syracuseStep 2193823 = 3290735) B3290735
theorem B3290741 : Blo 2193435 3290741 := bbase (se 5 (by rfl) ⟨154253, by rfl⟩ : syracuseStep 3290741 = 308507) (by norm_num)
theorem B2193827 : Blo 2193435 2193827 := bstep (se 1 (by rfl) ⟨1645370, by rfl⟩ : syracuseStep 2193827 = 3290741) B3290741
theorem B4164853 : Blo 2193435 4164853 := bbase (se 5 (by rfl) ⟨195227, by rfl⟩ : syracuseStep 4164853 = 390455) (by norm_num)
theorem B5553137 : Blo 2193435 5553137 := bstep (se 2 (by rfl) ⟨2082426, by rfl⟩ : syracuseStep 5553137 = 4164853) B4164853
theorem B3702091 : Blo 2193435 3702091 := bstep (se 1 (by rfl) ⟨2776568, by rfl⟩ : syracuseStep 3702091 = 5553137) B5553137
theorem B4936121 : Blo 2193435 4936121 := bstep (se 2 (by rfl) ⟨1851045, by rfl⟩ : syracuseStep 4936121 = 3702091) B3702091
theorem B3290747 : Blo 2193435 3290747 := bstep (se 1 (by rfl) ⟨2468060, by rfl⟩ : syracuseStep 3290747 = 4936121) B4936121
theorem B2193831 : Blo 2193435 2193831 := bstep (se 1 (by rfl) ⟨1645373, by rfl⟩ : syracuseStep 2193831 = 3290747) B3290747
theorem B2468065 : Blo 2193435 2468065 := bbase (se 2 (by rfl) ⟨925524, by rfl⟩ : syracuseStep 2468065 = 1851049) (by norm_num)
theorem B3290753 : Blo 2193435 3290753 := bstep (se 2 (by rfl) ⟨1234032, by rfl⟩ : syracuseStep 3290753 = 2468065) B2468065
theorem B2193835 : Blo 2193435 2193835 := bstep (se 1 (by rfl) ⟨1645376, by rfl⟩ : syracuseStep 2193835 = 3290753) B3290753
theorem B5553157 : Blo 2193435 5553157 := bbase (se 4 (by rfl) ⟨520608, by rfl⟩ : syracuseStep 5553157 = 1041217) (by norm_num)
theorem B7404209 : Blo 2193435 7404209 := bstep (se 2 (by rfl) ⟨2776578, by rfl⟩ : syracuseStep 7404209 = 5553157) B5553157
theorem B4936139 : Blo 2193435 4936139 := bstep (se 1 (by rfl) ⟨3702104, by rfl⟩ : syracuseStep 4936139 = 7404209) B7404209
theorem B3290759 : Blo 2193435 3290759 := bstep (se 1 (by rfl) ⟨2468069, by rfl⟩ : syracuseStep 3290759 = 4936139) B4936139
theorem B2193839 : Blo 2193435 2193839 := bstep (se 1 (by rfl) ⟨1645379, by rfl⟩ : syracuseStep 2193839 = 3290759) B3290759
theorem B3290765 : Blo 2193435 3290765 := bbase (se 3 (by rfl) ⟨617018, by rfl⟩ : syracuseStep 3290765 = 1234037) (by norm_num)
theorem B2193843 : Blo 2193435 2193843 := bstep (se 1 (by rfl) ⟨1645382, by rfl⟩ : syracuseStep 2193843 = 3290765) B3290765
theorem B4936157 : Blo 2193435 4936157 := bbase (se 3 (by rfl) ⟨925529, by rfl⟩ : syracuseStep 4936157 = 1851059) (by norm_num)
theorem B3290771 : Blo 2193435 3290771 := bstep (se 1 (by rfl) ⟨2468078, by rfl⟩ : syracuseStep 3290771 = 4936157) B4936157
theorem B2193847 : Blo 2193435 2193847 := bstep (se 1 (by rfl) ⟨1645385, by rfl⟩ : syracuseStep 2193847 = 3290771) B3290771
theorem B3702125 : Blo 2193435 3702125 := bbase (se 3 (by rfl) ⟨694148, by rfl⟩ : syracuseStep 3702125 = 1388297) (by norm_num)
theorem B2468083 : Blo 2193435 2468083 := bstep (se 1 (by rfl) ⟨1851062, by rfl⟩ : syracuseStep 2468083 = 3702125) B3702125
theorem B3290777 : Blo 2193435 3290777 := bstep (se 2 (by rfl) ⟨1234041, by rfl⟩ : syracuseStep 3290777 = 2468083) B2468083
theorem B2193851 : Blo 2193435 2193851 := bstep (se 1 (by rfl) ⟨1645388, by rfl⟩ : syracuseStep 2193851 = 3290777) B3290777
theorem B4814237 : Blo 2193435 4814237 := bbase (se 3 (by rfl) ⟨902669, by rfl⟩ : syracuseStep 4814237 = 1805339) (by norm_num)
theorem B3209491 : Blo 2193435 3209491 := bstep (se 1 (by rfl) ⟨2407118, by rfl⟩ : syracuseStep 3209491 = 4814237) B4814237
theorem B4279321 : Blo 2193435 4279321 := bstep (se 2 (by rfl) ⟨1604745, by rfl⟩ : syracuseStep 4279321 = 3209491) B3209491
theorem B22823045 : Blo 2193435 22823045 := bstep (se 4 (by rfl) ⟨2139660, by rfl⟩ : syracuseStep 22823045 = 4279321) B4279321
theorem B15215363 : Blo 2193435 15215363 := bstep (se 1 (by rfl) ⟨11411522, by rfl⟩ : syracuseStep 15215363 = 22823045) B22823045
theorem B10143575 : Blo 2193435 10143575 := bstep (se 1 (by rfl) ⟨7607681, by rfl⟩ : syracuseStep 10143575 = 15215363) B15215363
theorem B6762383 : Blo 2193435 6762383 := bstep (se 1 (by rfl) ⟨5071787, by rfl⟩ : syracuseStep 6762383 = 10143575) B10143575
theorem B4508255 : Blo 2193435 4508255 := bstep (se 1 (by rfl) ⟨3381191, by rfl⟩ : syracuseStep 4508255 = 6762383) B6762383
theorem B12022013 : Blo 2193435 12022013 := bstep (se 3 (by rfl) ⟨2254127, by rfl⟩ : syracuseStep 12022013 = 4508255) B4508255
theorem B8014675 : Blo 2193435 8014675 := bstep (se 1 (by rfl) ⟨6011006, by rfl⟩ : syracuseStep 8014675 = 12022013) B12022013
theorem B10686233 : Blo 2193435 10686233 := bstep (se 2 (by rfl) ⟨4007337, by rfl⟩ : syracuseStep 10686233 = 8014675) B8014675
theorem B28496621 : Blo 2193435 28496621 := bstep (se 3 (by rfl) ⟨5343116, by rfl⟩ : syracuseStep 28496621 = 10686233) B10686233
theorem B75990989 : Blo 2193435 75990989 := bstep (se 3 (by rfl) ⟨14248310, by rfl⟩ : syracuseStep 75990989 = 28496621) B28496621
theorem B50660659 : Blo 2193435 50660659 := bstep (se 1 (by rfl) ⟨37995494, by rfl⟩ : syracuseStep 50660659 = 75990989) B75990989
theorem B270190181 : Blo 2193435 270190181 := bstep (se 4 (by rfl) ⟨25330329, by rfl⟩ : syracuseStep 270190181 = 50660659) B50660659
theorem B180126787 : Blo 2193435 180126787 := bstep (se 1 (by rfl) ⟨135095090, by rfl⟩ : syracuseStep 180126787 = 270190181) B270190181
theorem B240169049 : Blo 2193435 240169049 := bstep (se 2 (by rfl) ⟨90063393, by rfl⟩ : syracuseStep 240169049 = 180126787) B180126787
theorem B160112699 : Blo 2193435 160112699 := bstep (se 1 (by rfl) ⟨120084524, by rfl⟩ : syracuseStep 160112699 = 240169049) B240169049
theorem B106741799 : Blo 2193435 106741799 := bstep (se 1 (by rfl) ⟨80056349, by rfl⟩ : syracuseStep 106741799 = 160112699) B160112699
theorem B71161199 : Blo 2193435 71161199 := bstep (se 1 (by rfl) ⟨53370899, by rfl⟩ : syracuseStep 71161199 = 106741799) B106741799
theorem B47440799 : Blo 2193435 47440799 := bstep (se 1 (by rfl) ⟨35580599, by rfl⟩ : syracuseStep 47440799 = 71161199) B71161199
theorem B31627199 : Blo 2193435 31627199 := bstep (se 1 (by rfl) ⟨23720399, by rfl⟩ : syracuseStep 31627199 = 47440799) B47440799
theorem B21084799 : Blo 2193435 21084799 := bstep (se 1 (by rfl) ⟨15813599, by rfl⟩ : syracuseStep 21084799 = 31627199) B31627199
theorem B28113065 : Blo 2193435 28113065 := bstep (se 2 (by rfl) ⟨10542399, by rfl⟩ : syracuseStep 28113065 = 21084799) B21084799
theorem B18742043 : Blo 2193435 18742043 := bstep (se 1 (by rfl) ⟨14056532, by rfl⟩ : syracuseStep 18742043 = 28113065) B28113065
theorem B12494695 : Blo 2193435 12494695 := bstep (se 1 (by rfl) ⟨9371021, by rfl⟩ : syracuseStep 12494695 = 18742043) B18742043
theorem B16659593 : Blo 2193435 16659593 := bstep (se 2 (by rfl) ⟨6247347, by rfl⟩ : syracuseStep 16659593 = 12494695) B12494695
theorem B11106395 : Blo 2193435 11106395 := bstep (se 1 (by rfl) ⟨8329796, by rfl⟩ : syracuseStep 11106395 = 16659593) B16659593
theorem B7404263 : Blo 2193435 7404263 := bstep (se 1 (by rfl) ⟨5553197, by rfl⟩ : syracuseStep 7404263 = 11106395) B11106395
theorem B4936175 : Blo 2193435 4936175 := bstep (se 1 (by rfl) ⟨3702131, by rfl⟩ : syracuseStep 4936175 = 7404263) B7404263
theorem B3290783 : Blo 2193435 3290783 := bstep (se 1 (by rfl) ⟨2468087, by rfl⟩ : syracuseStep 3290783 = 4936175) B4936175
theorem B2193855 : Blo 2193435 2193855 := bstep (se 1 (by rfl) ⟨1645391, by rfl⟩ : syracuseStep 2193855 = 3290783) B3290783
theorem B3290789 : Blo 2193435 3290789 := bbase (se 4 (by rfl) ⟨308511, by rfl⟩ : syracuseStep 3290789 = 617023) (by norm_num)
theorem B2193859 : Blo 2193435 2193859 := bstep (se 1 (by rfl) ⟨1645394, by rfl⟩ : syracuseStep 2193859 = 3290789) B3290789
theorem B2776609 : Blo 2193435 2776609 := bbase (se 2 (by rfl) ⟨1041228, by rfl⟩ : syracuseStep 2776609 = 2082457) (by norm_num)
theorem B3702145 : Blo 2193435 3702145 := bstep (se 2 (by rfl) ⟨1388304, by rfl⟩ : syracuseStep 3702145 = 2776609) B2776609
theorem B4936193 : Blo 2193435 4936193 := bstep (se 2 (by rfl) ⟨1851072, by rfl⟩ : syracuseStep 4936193 = 3702145) B3702145
theorem B3290795 : Blo 2193435 3290795 := bstep (se 1 (by rfl) ⟨2468096, by rfl⟩ : syracuseStep 3290795 = 4936193) B4936193
theorem B2193863 : Blo 2193435 2193863 := bstep (se 1 (by rfl) ⟨1645397, by rfl⟩ : syracuseStep 2193863 = 3290795) B3290795
theorem B2468101 : Blo 2193435 2468101 := bbase (se 4 (by rfl) ⟨231384, by rfl⟩ : syracuseStep 2468101 = 462769) (by norm_num)
theorem B3290801 : Blo 2193435 3290801 := bstep (se 2 (by rfl) ⟨1234050, by rfl⟩ : syracuseStep 3290801 = 2468101) B2468101
theorem B2193867 : Blo 2193435 2193867 := bstep (se 1 (by rfl) ⟨1645400, by rfl⟩ : syracuseStep 2193867 = 3290801) B3290801
theorem B2342773 : Blo 2193435 2342773 := bbase (se 5 (by rfl) ⟨109817, by rfl⟩ : syracuseStep 2342773 = 219635) (by norm_num)
theorem B3123697 : Blo 2193435 3123697 := bstep (se 2 (by rfl) ⟨1171386, by rfl⟩ : syracuseStep 3123697 = 2342773) B2342773
theorem B4164929 : Blo 2193435 4164929 := bstep (se 2 (by rfl) ⟨1561848, by rfl⟩ : syracuseStep 4164929 = 3123697) B3123697
theorem B2776619 : Blo 2193435 2776619 := bstep (se 1 (by rfl) ⟨2082464, by rfl⟩ : syracuseStep 2776619 = 4164929) B4164929
theorem B7404317 : Blo 2193435 7404317 := bstep (se 3 (by rfl) ⟨1388309, by rfl⟩ : syracuseStep 7404317 = 2776619) B2776619
theorem B4936211 : Blo 2193435 4936211 := bstep (se 1 (by rfl) ⟨3702158, by rfl⟩ : syracuseStep 4936211 = 7404317) B7404317
theorem B3290807 : Blo 2193435 3290807 := bstep (se 1 (by rfl) ⟨2468105, by rfl⟩ : syracuseStep 3290807 = 4936211) B4936211
theorem B2193871 : Blo 2193435 2193871 := bstep (se 1 (by rfl) ⟨1645403, by rfl⟩ : syracuseStep 2193871 = 3290807) B3290807
theorem B3290813 : Blo 2193435 3290813 := bbase (se 3 (by rfl) ⟨617027, by rfl⟩ : syracuseStep 3290813 = 1234055) (by norm_num)
theorem B2193875 : Blo 2193435 2193875 := bstep (se 1 (by rfl) ⟨1645406, by rfl⟩ : syracuseStep 2193875 = 3290813) B3290813
theorem B4936229 : Blo 2193435 4936229 := bbase (se 4 (by rfl) ⟨462771, by rfl⟩ : syracuseStep 4936229 = 925543) (by norm_num)
theorem B3290819 : Blo 2193435 3290819 := bstep (se 1 (by rfl) ⟨2468114, by rfl⟩ : syracuseStep 3290819 = 4936229) B4936229
theorem B2193879 : Blo 2193435 2193879 := bstep (se 1 (by rfl) ⟨1645409, by rfl⟩ : syracuseStep 2193879 = 3290819) B3290819
theorem B5553269 : Blo 2193435 5553269 := bbase (se 5 (by rfl) ⟨260309, by rfl⟩ : syracuseStep 5553269 = 520619) (by norm_num)
theorem B3702179 : Blo 2193435 3702179 := bstep (se 1 (by rfl) ⟨2776634, by rfl⟩ : syracuseStep 3702179 = 5553269) B5553269
theorem B2468119 : Blo 2193435 2468119 := bstep (se 1 (by rfl) ⟨1851089, by rfl⟩ : syracuseStep 2468119 = 3702179) B3702179
theorem B3290825 : Blo 2193435 3290825 := bstep (se 2 (by rfl) ⟨1234059, by rfl⟩ : syracuseStep 3290825 = 2468119) B2468119
theorem B2193883 : Blo 2193435 2193883 := bstep (se 1 (by rfl) ⟨1645412, by rfl⟩ : syracuseStep 2193883 = 3290825) B3290825
theorem B21085109 : Blo 2193435 21085109 := bbase (se 5 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 21085109 = 1976729) (by norm_num)
theorem B14056739 : Blo 2193435 14056739 := bstep (se 1 (by rfl) ⟨10542554, by rfl⟩ : syracuseStep 14056739 = 21085109) B21085109
theorem B9371159 : Blo 2193435 9371159 := bstep (se 1 (by rfl) ⟨7028369, by rfl⟩ : syracuseStep 9371159 = 14056739) B14056739
theorem B6247439 : Blo 2193435 6247439 := bstep (se 1 (by rfl) ⟨4685579, by rfl⟩ : syracuseStep 6247439 = 9371159) B9371159
theorem B4164959 : Blo 2193435 4164959 := bstep (se 1 (by rfl) ⟨3123719, by rfl⟩ : syracuseStep 4164959 = 6247439) B6247439
theorem B11106557 : Blo 2193435 11106557 := bstep (se 3 (by rfl) ⟨2082479, by rfl⟩ : syracuseStep 11106557 = 4164959) B4164959
theorem B7404371 : Blo 2193435 7404371 := bstep (se 1 (by rfl) ⟨5553278, by rfl⟩ : syracuseStep 7404371 = 11106557) B11106557
theorem B4936247 : Blo 2193435 4936247 := bstep (se 1 (by rfl) ⟨3702185, by rfl⟩ : syracuseStep 4936247 = 7404371) B7404371
theorem B3290831 : Blo 2193435 3290831 := bstep (se 1 (by rfl) ⟨2468123, by rfl⟩ : syracuseStep 3290831 = 4936247) B4936247
theorem B2193887 : Blo 2193435 2193887 := bstep (se 1 (by rfl) ⟨1645415, by rfl⟩ : syracuseStep 2193887 = 3290831) B3290831
theorem B3290837 : Blo 2193435 3290837 := bbase (se 7 (by rfl) ⟨38564, by rfl⟩ : syracuseStep 3290837 = 77129) (by norm_num)
theorem B2193891 : Blo 2193435 2193891 := bstep (se 1 (by rfl) ⟨1645418, by rfl⟩ : syracuseStep 2193891 = 3290837) B3290837
theorem B4685597 : Blo 2193435 4685597 := bbase (se 3 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 4685597 = 1757099) (by norm_num)
theorem B3123731 : Blo 2193435 3123731 := bstep (se 1 (by rfl) ⟨2342798, by rfl⟩ : syracuseStep 3123731 = 4685597) B4685597
theorem B8329949 : Blo 2193435 8329949 := bstep (se 3 (by rfl) ⟨1561865, by rfl⟩ : syracuseStep 8329949 = 3123731) B3123731
theorem B5553299 : Blo 2193435 5553299 := bstep (se 1 (by rfl) ⟨4164974, by rfl⟩ : syracuseStep 5553299 = 8329949) B8329949
theorem B3702199 : Blo 2193435 3702199 := bstep (se 1 (by rfl) ⟨2776649, by rfl⟩ : syracuseStep 3702199 = 5553299) B5553299
theorem B4936265 : Blo 2193435 4936265 := bstep (se 2 (by rfl) ⟨1851099, by rfl⟩ : syracuseStep 4936265 = 3702199) B3702199
theorem B3290843 : Blo 2193435 3290843 := bstep (se 1 (by rfl) ⟨2468132, by rfl⟩ : syracuseStep 3290843 = 4936265) B4936265
theorem B2193895 : Blo 2193435 2193895 := bstep (se 1 (by rfl) ⟨1645421, by rfl⟩ : syracuseStep 2193895 = 3290843) B3290843
theorem B2468137 : Blo 2193435 2468137 := bbase (se 2 (by rfl) ⟨925551, by rfl⟩ : syracuseStep 2468137 = 1851103) (by norm_num)
theorem B3290849 : Blo 2193435 3290849 := bstep (se 2 (by rfl) ⟨1234068, by rfl⟩ : syracuseStep 3290849 = 2468137) B2468137
theorem B2193899 : Blo 2193435 2193899 := bstep (se 1 (by rfl) ⟨1645424, by rfl⟩ : syracuseStep 2193899 = 3290849) B3290849
theorem B26686037 : Blo 2193435 26686037 := bbase (se 8 (by rfl) ⟨156363, by rfl⟩ : syracuseStep 26686037 = 312727) (by norm_num)
theorem B17790691 : Blo 2193435 17790691 := bstep (se 1 (by rfl) ⟨13343018, by rfl⟩ : syracuseStep 17790691 = 26686037) B26686037
theorem B23720921 : Blo 2193435 23720921 := bstep (se 2 (by rfl) ⟨8895345, by rfl⟩ : syracuseStep 23720921 = 17790691) B17790691
theorem B15813947 : Blo 2193435 15813947 := bstep (se 1 (by rfl) ⟨11860460, by rfl⟩ : syracuseStep 15813947 = 23720921) B23720921
theorem B10542631 : Blo 2193435 10542631 := bstep (se 1 (by rfl) ⟨7906973, by rfl⟩ : syracuseStep 10542631 = 15813947) B15813947
theorem B14056841 : Blo 2193435 14056841 := bstep (se 2 (by rfl) ⟨5271315, by rfl⟩ : syracuseStep 14056841 = 10542631) B10542631
theorem B9371227 : Blo 2193435 9371227 := bstep (se 1 (by rfl) ⟨7028420, by rfl⟩ : syracuseStep 9371227 = 14056841) B14056841
theorem B12494969 : Blo 2193435 12494969 := bstep (se 2 (by rfl) ⟨4685613, by rfl⟩ : syracuseStep 12494969 = 9371227) B9371227
theorem B8329979 : Blo 2193435 8329979 := bstep (se 1 (by rfl) ⟨6247484, by rfl⟩ : syracuseStep 8329979 = 12494969) B12494969
theorem B5553319 : Blo 2193435 5553319 := bstep (se 1 (by rfl) ⟨4164989, by rfl⟩ : syracuseStep 5553319 = 8329979) B8329979
theorem B7404425 : Blo 2193435 7404425 := bstep (se 2 (by rfl) ⟨2776659, by rfl⟩ : syracuseStep 7404425 = 5553319) B5553319
theorem B4936283 : Blo 2193435 4936283 := bstep (se 1 (by rfl) ⟨3702212, by rfl⟩ : syracuseStep 4936283 = 7404425) B7404425
theorem B3290855 : Blo 2193435 3290855 := bstep (se 1 (by rfl) ⟨2468141, by rfl⟩ : syracuseStep 3290855 = 4936283) B4936283
theorem B2193903 : Blo 2193435 2193903 := bstep (se 1 (by rfl) ⟨1645427, by rfl⟩ : syracuseStep 2193903 = 3290855) B3290855
theorem B3290861 : Blo 2193435 3290861 := bbase (se 3 (by rfl) ⟨617036, by rfl⟩ : syracuseStep 3290861 = 1234073) (by norm_num)
theorem B2193907 : Blo 2193435 2193907 := bstep (se 1 (by rfl) ⟨1645430, by rfl⟩ : syracuseStep 2193907 = 3290861) B3290861
theorem B4936301 : Blo 2193435 4936301 := bbase (se 3 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 4936301 = 1851113) (by norm_num)
theorem B3290867 : Blo 2193435 3290867 := bstep (se 1 (by rfl) ⟨2468150, by rfl⟩ : syracuseStep 3290867 = 4936301) B4936301
theorem B2193911 : Blo 2193435 2193911 := bstep (se 1 (by rfl) ⟨1645433, by rfl⟩ : syracuseStep 2193911 = 3290867) B3290867
theorem B4165013 : Blo 2193435 4165013 := bbase (se 6 (by rfl) ⟨97617, by rfl⟩ : syracuseStep 4165013 = 195235) (by norm_num)
theorem B2776675 : Blo 2193435 2776675 := bstep (se 1 (by rfl) ⟨2082506, by rfl⟩ : syracuseStep 2776675 = 4165013) B4165013
theorem B3702233 : Blo 2193435 3702233 := bstep (se 2 (by rfl) ⟨1388337, by rfl⟩ : syracuseStep 3702233 = 2776675) B2776675
theorem B2468155 : Blo 2193435 2468155 := bstep (se 1 (by rfl) ⟨1851116, by rfl⟩ : syracuseStep 2468155 = 3702233) B3702233
theorem B3290873 : Blo 2193435 3290873 := bstep (se 2 (by rfl) ⟨1234077, by rfl⟩ : syracuseStep 3290873 = 2468155) B2468155
theorem B2193915 : Blo 2193435 2193915 := bstep (se 1 (by rfl) ⟨1645436, by rfl⟩ : syracuseStep 2193915 = 3290873) B3290873
theorem B6671557 : Blo 2193435 6671557 := bbase (se 4 (by rfl) ⟨625458, by rfl⟩ : syracuseStep 6671557 = 1250917) (by norm_num)
theorem B8895409 : Blo 2193435 8895409 := bstep (se 2 (by rfl) ⟨3335778, by rfl⟩ : syracuseStep 8895409 = 6671557) B6671557
theorem B47442181 : Blo 2193435 47442181 := bstep (se 4 (by rfl) ⟨4447704, by rfl⟩ : syracuseStep 47442181 = 8895409) B8895409
theorem B63256241 : Blo 2193435 63256241 := bstep (se 2 (by rfl) ⟨23721090, by rfl⟩ : syracuseStep 63256241 = 47442181) B47442181
theorem B42170827 : Blo 2193435 42170827 := bstep (se 1 (by rfl) ⟨31628120, by rfl⟩ : syracuseStep 42170827 = 63256241) B63256241
theorem B56227769 : Blo 2193435 56227769 := bstep (se 2 (by rfl) ⟨21085413, by rfl⟩ : syracuseStep 56227769 = 42170827) B42170827
theorem B37485179 : Blo 2193435 37485179 := bstep (se 1 (by rfl) ⟨28113884, by rfl⟩ : syracuseStep 37485179 = 56227769) B56227769
theorem B24990119 : Blo 2193435 24990119 := bstep (se 1 (by rfl) ⟨18742589, by rfl⟩ : syracuseStep 24990119 = 37485179) B37485179
theorem B16660079 : Blo 2193435 16660079 := bstep (se 1 (by rfl) ⟨12495059, by rfl⟩ : syracuseStep 16660079 = 24990119) B24990119
theorem B11106719 : Blo 2193435 11106719 := bstep (se 1 (by rfl) ⟨8330039, by rfl⟩ : syracuseStep 11106719 = 16660079) B16660079
theorem B7404479 : Blo 2193435 7404479 := bstep (se 1 (by rfl) ⟨5553359, by rfl⟩ : syracuseStep 7404479 = 11106719) B11106719
theorem B4936319 : Blo 2193435 4936319 := bstep (se 1 (by rfl) ⟨3702239, by rfl⟩ : syracuseStep 4936319 = 7404479) B7404479
theorem B3290879 : Blo 2193435 3290879 := bstep (se 1 (by rfl) ⟨2468159, by rfl⟩ : syracuseStep 3290879 = 4936319) B4936319
theorem B2193919 : Blo 2193435 2193919 := bstep (se 1 (by rfl) ⟨1645439, by rfl⟩ : syracuseStep 2193919 = 3290879) B3290879
theorem B3290885 : Blo 2193435 3290885 := bbase (se 4 (by rfl) ⟨308520, by rfl⟩ : syracuseStep 3290885 = 617041) (by norm_num)
theorem B2193923 : Blo 2193435 2193923 := bstep (se 1 (by rfl) ⟨1645442, by rfl⟩ : syracuseStep 2193923 = 3290885) B3290885
theorem B3702253 : Blo 2193435 3702253 := bbase (se 3 (by rfl) ⟨694172, by rfl⟩ : syracuseStep 3702253 = 1388345) (by norm_num)
theorem B4936337 : Blo 2193435 4936337 := bstep (se 2 (by rfl) ⟨1851126, by rfl⟩ : syracuseStep 4936337 = 3702253) B3702253
theorem B3290891 : Blo 2193435 3290891 := bstep (se 1 (by rfl) ⟨2468168, by rfl⟩ : syracuseStep 3290891 = 4936337) B4936337
theorem B2193927 : Blo 2193435 2193927 := bstep (se 1 (by rfl) ⟨1645445, by rfl⟩ : syracuseStep 2193927 = 3290891) B3290891
theorem B2468173 : Blo 2193435 2468173 := bbase (se 3 (by rfl) ⟨462782, by rfl⟩ : syracuseStep 2468173 = 925565) (by norm_num)
theorem B3290897 : Blo 2193435 3290897 := bstep (se 2 (by rfl) ⟨1234086, by rfl⟩ : syracuseStep 3290897 = 2468173) B2468173
theorem B2193931 : Blo 2193435 2193931 := bstep (se 1 (by rfl) ⟨1645448, by rfl⟩ : syracuseStep 2193931 = 3290897) B3290897
theorem B7404533 : Blo 2193435 7404533 := bbase (se 5 (by rfl) ⟨347087, by rfl⟩ : syracuseStep 7404533 = 694175) (by norm_num)
theorem B4936355 : Blo 2193435 4936355 := bstep (se 1 (by rfl) ⟨3702266, by rfl⟩ : syracuseStep 4936355 = 7404533) B7404533
theorem B3290903 : Blo 2193435 3290903 := bstep (se 1 (by rfl) ⟨2468177, by rfl⟩ : syracuseStep 3290903 = 4936355) B4936355
theorem B2193935 : Blo 2193435 2193935 := bstep (se 1 (by rfl) ⟨1645451, by rfl⟩ : syracuseStep 2193935 = 3290903) B3290903
theorem B3290909 : Blo 2193435 3290909 := bbase (se 3 (by rfl) ⟨617045, by rfl⟩ : syracuseStep 3290909 = 1234091) (by norm_num)
theorem B2193939 : Blo 2193435 2193939 := bstep (se 1 (by rfl) ⟨1645454, by rfl⟩ : syracuseStep 2193939 = 3290909) B3290909
theorem B4936373 : Blo 2193435 4936373 := bbase (se 5 (by rfl) ⟨231392, by rfl⟩ : syracuseStep 4936373 = 462785) (by norm_num)
theorem B3290915 : Blo 2193435 3290915 := bstep (se 1 (by rfl) ⟨2468186, by rfl⟩ : syracuseStep 3290915 = 4936373) B4936373
theorem B2193943 : Blo 2193435 2193943 := bstep (se 1 (by rfl) ⟨1645457, by rfl⟩ : syracuseStep 2193943 = 3290915) B3290915
theorem B12495221 : Blo 2193435 12495221 := bbase (se 5 (by rfl) ⟨585713, by rfl⟩ : syracuseStep 12495221 = 1171427) (by norm_num)
theorem B8330147 : Blo 2193435 8330147 := bstep (se 1 (by rfl) ⟨6247610, by rfl⟩ : syracuseStep 8330147 = 12495221) B12495221
theorem B5553431 : Blo 2193435 5553431 := bstep (se 1 (by rfl) ⟨4165073, by rfl⟩ : syracuseStep 5553431 = 8330147) B8330147
theorem B3702287 : Blo 2193435 3702287 := bstep (se 1 (by rfl) ⟨2776715, by rfl⟩ : syracuseStep 3702287 = 5553431) B5553431
theorem B2468191 : Blo 2193435 2468191 := bstep (se 1 (by rfl) ⟨1851143, by rfl⟩ : syracuseStep 2468191 = 3702287) B3702287
theorem B3290921 : Blo 2193435 3290921 := bstep (se 2 (by rfl) ⟨1234095, by rfl⟩ : syracuseStep 3290921 = 2468191) B2468191
theorem B2193947 : Blo 2193435 2193947 := bstep (se 1 (by rfl) ⟨1645460, by rfl⟩ : syracuseStep 2193947 = 3290921) B3290921
theorem B6247621 : Blo 2193435 6247621 := bbase (se 4 (by rfl) ⟨585714, by rfl⟩ : syracuseStep 6247621 = 1171429) (by norm_num)
theorem B8330161 : Blo 2193435 8330161 := bstep (se 2 (by rfl) ⟨3123810, by rfl⟩ : syracuseStep 8330161 = 6247621) B6247621
theorem B11106881 : Blo 2193435 11106881 := bstep (se 2 (by rfl) ⟨4165080, by rfl⟩ : syracuseStep 11106881 = 8330161) B8330161
theorem B7404587 : Blo 2193435 7404587 := bstep (se 1 (by rfl) ⟨5553440, by rfl⟩ : syracuseStep 7404587 = 11106881) B11106881
theorem B4936391 : Blo 2193435 4936391 := bstep (se 1 (by rfl) ⟨3702293, by rfl⟩ : syracuseStep 4936391 = 7404587) B7404587
theorem B3290927 : Blo 2193435 3290927 := bstep (se 1 (by rfl) ⟨2468195, by rfl⟩ : syracuseStep 3290927 = 4936391) B4936391
theorem B2193951 : Blo 2193435 2193951 := bstep (se 1 (by rfl) ⟨1645463, by rfl⟩ : syracuseStep 2193951 = 3290927) B3290927
theorem B3290933 : Blo 2193435 3290933 := bbase (se 5 (by rfl) ⟨154262, by rfl⟩ : syracuseStep 3290933 = 308525) (by norm_num)
theorem B2193955 : Blo 2193435 2193955 := bstep (se 1 (by rfl) ⟨1645466, by rfl⟩ : syracuseStep 2193955 = 3290933) B3290933
theorem B5553461 : Blo 2193435 5553461 := bbase (se 5 (by rfl) ⟨260318, by rfl⟩ : syracuseStep 5553461 = 520637) (by norm_num)
theorem B3702307 : Blo 2193435 3702307 := bstep (se 1 (by rfl) ⟨2776730, by rfl⟩ : syracuseStep 3702307 = 5553461) B5553461
theorem B4936409 : Blo 2193435 4936409 := bstep (se 2 (by rfl) ⟨1851153, by rfl⟩ : syracuseStep 4936409 = 3702307) B3702307
theorem B3290939 : Blo 2193435 3290939 := bstep (se 1 (by rfl) ⟨2468204, by rfl⟩ : syracuseStep 3290939 = 4936409) B4936409
theorem B2193959 : Blo 2193435 2193959 := bstep (se 1 (by rfl) ⟨1645469, by rfl⟩ : syracuseStep 2193959 = 3290939) B3290939
theorem B2468209 : Blo 2193435 2468209 := bbase (se 2 (by rfl) ⟨925578, by rfl⟩ : syracuseStep 2468209 = 1851157) (by norm_num)
theorem B3290945 : Blo 2193435 3290945 := bstep (se 2 (by rfl) ⟨1234104, by rfl⟩ : syracuseStep 3290945 = 2468209) B2468209
theorem B2193963 : Blo 2193435 2193963 := bstep (se 1 (by rfl) ⟨1645472, by rfl⟩ : syracuseStep 2193963 = 3290945) B3290945
theorem B5930405 : Blo 2193435 5930405 := bbase (se 4 (by rfl) ⟨555975, by rfl⟩ : syracuseStep 5930405 = 1111951) (by norm_num)
theorem B3953603 : Blo 2193435 3953603 := bstep (se 1 (by rfl) ⟨2965202, by rfl⟩ : syracuseStep 3953603 = 5930405) B5930405
theorem B2635735 : Blo 2193435 2635735 := bstep (se 1 (by rfl) ⟨1976801, by rfl⟩ : syracuseStep 2635735 = 3953603) B3953603
theorem B3514313 : Blo 2193435 3514313 := bstep (se 2 (by rfl) ⟨1317867, by rfl⟩ : syracuseStep 3514313 = 2635735) B2635735
theorem B9371501 : Blo 2193435 9371501 := bstep (se 3 (by rfl) ⟨1757156, by rfl⟩ : syracuseStep 9371501 = 3514313) B3514313
theorem B6247667 : Blo 2193435 6247667 := bstep (se 1 (by rfl) ⟨4685750, by rfl⟩ : syracuseStep 6247667 = 9371501) B9371501
theorem B4165111 : Blo 2193435 4165111 := bstep (se 1 (by rfl) ⟨3123833, by rfl⟩ : syracuseStep 4165111 = 6247667) B6247667
theorem B5553481 : Blo 2193435 5553481 := bstep (se 2 (by rfl) ⟨2082555, by rfl⟩ : syracuseStep 5553481 = 4165111) B4165111
theorem B7404641 : Blo 2193435 7404641 := bstep (se 2 (by rfl) ⟨2776740, by rfl⟩ : syracuseStep 7404641 = 5553481) B5553481
theorem B4936427 : Blo 2193435 4936427 := bstep (se 1 (by rfl) ⟨3702320, by rfl⟩ : syracuseStep 4936427 = 7404641) B7404641
theorem B3290951 : Blo 2193435 3290951 := bstep (se 1 (by rfl) ⟨2468213, by rfl⟩ : syracuseStep 3290951 = 4936427) B4936427
theorem B2193967 : Blo 2193435 2193967 := bstep (se 1 (by rfl) ⟨1645475, by rfl⟩ : syracuseStep 2193967 = 3290951) B3290951
theorem B3290957 : Blo 2193435 3290957 := bbase (se 3 (by rfl) ⟨617054, by rfl⟩ : syracuseStep 3290957 = 1234109) (by norm_num)
theorem B2193971 : Blo 2193435 2193971 := bstep (se 1 (by rfl) ⟨1645478, by rfl⟩ : syracuseStep 2193971 = 3290957) B3290957
theorem B4936445 : Blo 2193435 4936445 := bbase (se 3 (by rfl) ⟨925583, by rfl⟩ : syracuseStep 4936445 = 1851167) (by norm_num)
theorem B3290963 : Blo 2193435 3290963 := bstep (se 1 (by rfl) ⟨2468222, by rfl⟩ : syracuseStep 3290963 = 4936445) B4936445
theorem B2193975 : Blo 2193435 2193975 := bstep (se 1 (by rfl) ⟨1645481, by rfl⟩ : syracuseStep 2193975 = 3290963) B3290963
theorem B3702341 : Blo 2193435 3702341 := bbase (se 4 (by rfl) ⟨347094, by rfl⟩ : syracuseStep 3702341 = 694189) (by norm_num)
theorem B2468227 : Blo 2193435 2468227 := bstep (se 1 (by rfl) ⟨1851170, by rfl⟩ : syracuseStep 2468227 = 3702341) B3702341
theorem B3290969 : Blo 2193435 3290969 := bstep (se 2 (by rfl) ⟨1234113, by rfl⟩ : syracuseStep 3290969 = 2468227) B2468227
theorem B2193979 : Blo 2193435 2193979 := bstep (se 1 (by rfl) ⟨1645484, by rfl⟩ : syracuseStep 2193979 = 3290969) B3290969
theorem B16660565 : Blo 2193435 16660565 := bbase (se 8 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 16660565 = 195241) (by norm_num)
theorem B11107043 : Blo 2193435 11107043 := bstep (se 1 (by rfl) ⟨8330282, by rfl⟩ : syracuseStep 11107043 = 16660565) B16660565
theorem B7404695 : Blo 2193435 7404695 := bstep (se 1 (by rfl) ⟨5553521, by rfl⟩ : syracuseStep 7404695 = 11107043) B11107043
theorem B4936463 : Blo 2193435 4936463 := bstep (se 1 (by rfl) ⟨3702347, by rfl⟩ : syracuseStep 4936463 = 7404695) B7404695
theorem B3290975 : Blo 2193435 3290975 := bstep (se 1 (by rfl) ⟨2468231, by rfl⟩ : syracuseStep 3290975 = 4936463) B4936463
theorem B2193983 : Blo 2193435 2193983 := bstep (se 1 (by rfl) ⟨1645487, by rfl⟩ : syracuseStep 2193983 = 3290975) B3290975
theorem B3290981 : Blo 2193435 3290981 := bbase (se 4 (by rfl) ⟨308529, by rfl⟩ : syracuseStep 3290981 = 617059) (by norm_num)
theorem B2193987 : Blo 2193435 2193987 := bstep (se 1 (by rfl) ⟨1645490, by rfl⟩ : syracuseStep 2193987 = 3290981) B3290981
theorem B4165157 : Blo 2193435 4165157 := bbase (se 4 (by rfl) ⟨390483, by rfl⟩ : syracuseStep 4165157 = 780967) (by norm_num)
theorem B2776771 : Blo 2193435 2776771 := bstep (se 1 (by rfl) ⟨2082578, by rfl⟩ : syracuseStep 2776771 = 4165157) B4165157
theorem B3702361 : Blo 2193435 3702361 := bstep (se 2 (by rfl) ⟨1388385, by rfl⟩ : syracuseStep 3702361 = 2776771) B2776771
theorem B4936481 : Blo 2193435 4936481 := bstep (se 2 (by rfl) ⟨1851180, by rfl⟩ : syracuseStep 4936481 = 3702361) B3702361
theorem B3290987 : Blo 2193435 3290987 := bstep (se 1 (by rfl) ⟨2468240, by rfl⟩ : syracuseStep 3290987 = 4936481) B4936481
theorem B2193991 : Blo 2193435 2193991 := bstep (se 1 (by rfl) ⟨1645493, by rfl⟩ : syracuseStep 2193991 = 3290987) B3290987
theorem B2468245 : Blo 2193435 2468245 := bbase (se 6 (by rfl) ⟨57849, by rfl⟩ : syracuseStep 2468245 = 115699) (by norm_num)
theorem B3290993 : Blo 2193435 3290993 := bstep (se 2 (by rfl) ⟨1234122, by rfl⟩ : syracuseStep 3290993 = 2468245) B2468245
theorem B2193995 : Blo 2193435 2193995 := bstep (se 1 (by rfl) ⟨1645496, by rfl⟩ : syracuseStep 2193995 = 3290993) B3290993
theorem B2776781 : Blo 2193435 2776781 := bbase (se 3 (by rfl) ⟨520646, by rfl⟩ : syracuseStep 2776781 = 1041293) (by norm_num)
theorem B7404749 : Blo 2193435 7404749 := bstep (se 3 (by rfl) ⟨1388390, by rfl⟩ : syracuseStep 7404749 = 2776781) B2776781
theorem B4936499 : Blo 2193435 4936499 := bstep (se 1 (by rfl) ⟨3702374, by rfl⟩ : syracuseStep 4936499 = 7404749) B7404749
theorem B3290999 : Blo 2193435 3290999 := bstep (se 1 (by rfl) ⟨2468249, by rfl⟩ : syracuseStep 3290999 = 4936499) B4936499
theorem B2193999 : Blo 2193435 2193999 := bstep (se 1 (by rfl) ⟨1645499, by rfl⟩ : syracuseStep 2193999 = 3290999) B3290999
theorem B3291005 : Blo 2193435 3291005 := bbase (se 3 (by rfl) ⟨617063, by rfl⟩ : syracuseStep 3291005 = 1234127) (by norm_num)
theorem B2194003 : Blo 2193435 2194003 := bstep (se 1 (by rfl) ⟨1645502, by rfl⟩ : syracuseStep 2194003 = 3291005) B3291005
theorem B4936517 : Blo 2193435 4936517 := bbase (se 4 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 4936517 = 925597) (by norm_num)
theorem B3291011 : Blo 2193435 3291011 := bstep (se 1 (by rfl) ⟨2468258, by rfl⟩ : syracuseStep 3291011 = 4936517) B4936517
theorem B2194007 : Blo 2193435 2194007 := bstep (se 1 (by rfl) ⟨1645505, by rfl⟩ : syracuseStep 2194007 = 3291011) B3291011
theorem B4685845 : Blo 2193435 4685845 := bbase (se 6 (by rfl) ⟨109824, by rfl⟩ : syracuseStep 4685845 = 219649) (by norm_num)
theorem B6247793 : Blo 2193435 6247793 := bstep (se 2 (by rfl) ⟨2342922, by rfl⟩ : syracuseStep 6247793 = 4685845) B4685845
theorem B4165195 : Blo 2193435 4165195 := bstep (se 1 (by rfl) ⟨3123896, by rfl⟩ : syracuseStep 4165195 = 6247793) B6247793
theorem B5553593 : Blo 2193435 5553593 := bstep (se 2 (by rfl) ⟨2082597, by rfl⟩ : syracuseStep 5553593 = 4165195) B4165195
theorem B3702395 : Blo 2193435 3702395 := bstep (se 1 (by rfl) ⟨2776796, by rfl⟩ : syracuseStep 3702395 = 5553593) B5553593
theorem B2468263 : Blo 2193435 2468263 := bstep (se 1 (by rfl) ⟨1851197, by rfl⟩ : syracuseStep 2468263 = 3702395) B3702395
theorem B3291017 : Blo 2193435 3291017 := bstep (se 2 (by rfl) ⟨1234131, by rfl⟩ : syracuseStep 3291017 = 2468263) B2468263
theorem B2194011 : Blo 2193435 2194011 := bstep (se 1 (by rfl) ⟨1645508, by rfl⟩ : syracuseStep 2194011 = 3291017) B3291017
theorem B11107205 : Blo 2193435 11107205 := bbase (se 4 (by rfl) ⟨1041300, by rfl⟩ : syracuseStep 11107205 = 2082601) (by norm_num)
theorem B7404803 : Blo 2193435 7404803 := bstep (se 1 (by rfl) ⟨5553602, by rfl⟩ : syracuseStep 7404803 = 11107205) B11107205
theorem B4936535 : Blo 2193435 4936535 := bstep (se 1 (by rfl) ⟨3702401, by rfl⟩ : syracuseStep 4936535 = 7404803) B7404803
theorem B3291023 : Blo 2193435 3291023 := bstep (se 1 (by rfl) ⟨2468267, by rfl⟩ : syracuseStep 3291023 = 4936535) B4936535
theorem B2194015 : Blo 2193435 2194015 := bstep (se 1 (by rfl) ⟨1645511, by rfl⟩ : syracuseStep 2194015 = 3291023) B3291023
theorem B3291029 : Blo 2193435 3291029 := bbase (se 6 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 3291029 = 154267) (by norm_num)
theorem B2194019 : Blo 2193435 2194019 := bstep (se 1 (by rfl) ⟨1645514, by rfl⟩ : syracuseStep 2194019 = 3291029) B3291029
theorem B5271605 : Blo 2193435 5271605 := bbase (se 5 (by rfl) ⟨247106, by rfl⟩ : syracuseStep 5271605 = 494213) (by norm_num)
theorem B3514403 : Blo 2193435 3514403 := bstep (se 1 (by rfl) ⟨2635802, by rfl⟩ : syracuseStep 3514403 = 5271605) B5271605
theorem B2342935 : Blo 2193435 2342935 := bstep (se 1 (by rfl) ⟨1757201, by rfl⟩ : syracuseStep 2342935 = 3514403) B3514403
theorem B12495653 : Blo 2193435 12495653 := bstep (se 4 (by rfl) ⟨1171467, by rfl⟩ : syracuseStep 12495653 = 2342935) B2342935
theorem B8330435 : Blo 2193435 8330435 := bstep (se 1 (by rfl) ⟨6247826, by rfl⟩ : syracuseStep 8330435 = 12495653) B12495653
theorem B5553623 : Blo 2193435 5553623 := bstep (se 1 (by rfl) ⟨4165217, by rfl⟩ : syracuseStep 5553623 = 8330435) B8330435
theorem B3702415 : Blo 2193435 3702415 := bstep (se 1 (by rfl) ⟨2776811, by rfl⟩ : syracuseStep 3702415 = 5553623) B5553623
theorem B4936553 : Blo 2193435 4936553 := bstep (se 2 (by rfl) ⟨1851207, by rfl⟩ : syracuseStep 4936553 = 3702415) B3702415
theorem B3291035 : Blo 2193435 3291035 := bstep (se 1 (by rfl) ⟨2468276, by rfl⟩ : syracuseStep 3291035 = 4936553) B4936553
theorem B2194023 : Blo 2193435 2194023 := bstep (se 1 (by rfl) ⟨1645517, by rfl⟩ : syracuseStep 2194023 = 3291035) B3291035
theorem B2468281 : Blo 2193435 2468281 := bbase (se 2 (by rfl) ⟨925605, by rfl⟩ : syracuseStep 2468281 = 1851211) (by norm_num)
theorem B3291041 : Blo 2193435 3291041 := bstep (se 2 (by rfl) ⟨1234140, by rfl⟩ : syracuseStep 3291041 = 2468281) B2468281
theorem B2194027 : Blo 2193435 2194027 := bstep (se 1 (by rfl) ⟨1645520, by rfl⟩ : syracuseStep 2194027 = 3291041) B3291041
theorem B9017237 : Blo 2193435 9017237 := bbase (se 6 (by rfl) ⟨211341, by rfl⟩ : syracuseStep 9017237 = 422683) (by norm_num)
theorem B6011491 : Blo 2193435 6011491 := bstep (se 1 (by rfl) ⟨4508618, by rfl⟩ : syracuseStep 6011491 = 9017237) B9017237
theorem B8015321 : Blo 2193435 8015321 := bstep (se 2 (by rfl) ⟨3005745, by rfl⟩ : syracuseStep 8015321 = 6011491) B6011491
theorem B21374189 : Blo 2193435 21374189 := bstep (se 3 (by rfl) ⟨4007660, by rfl⟩ : syracuseStep 21374189 = 8015321) B8015321
theorem B14249459 : Blo 2193435 14249459 := bstep (se 1 (by rfl) ⟨10687094, by rfl⟩ : syracuseStep 14249459 = 21374189) B21374189
theorem B37998557 : Blo 2193435 37998557 := bstep (se 3 (by rfl) ⟨7124729, by rfl⟩ : syracuseStep 37998557 = 14249459) B14249459
theorem B25332371 : Blo 2193435 25332371 := bstep (se 1 (by rfl) ⟨18999278, by rfl⟩ : syracuseStep 25332371 = 37998557) B37998557
theorem B16888247 : Blo 2193435 16888247 := bstep (se 1 (by rfl) ⟨12666185, by rfl⟩ : syracuseStep 16888247 = 25332371) B25332371
theorem B11258831 : Blo 2193435 11258831 := bstep (se 1 (by rfl) ⟨8444123, by rfl⟩ : syracuseStep 11258831 = 16888247) B16888247
theorem B7505887 : Blo 2193435 7505887 := bstep (se 1 (by rfl) ⟨5629415, by rfl⟩ : syracuseStep 7505887 = 11258831) B11258831
theorem B10007849 : Blo 2193435 10007849 := bstep (se 2 (by rfl) ⟨3752943, by rfl⟩ : syracuseStep 10007849 = 7505887) B7505887
theorem B6671899 : Blo 2193435 6671899 := bstep (se 1 (by rfl) ⟨5003924, by rfl⟩ : syracuseStep 6671899 = 10007849) B10007849
theorem B35583461 : Blo 2193435 35583461 := bstep (se 4 (by rfl) ⟨3335949, by rfl⟩ : syracuseStep 35583461 = 6671899) B6671899
theorem B23722307 : Blo 2193435 23722307 := bstep (se 1 (by rfl) ⟨17791730, by rfl⟩ : syracuseStep 23722307 = 35583461) B35583461
theorem B15814871 : Blo 2193435 15814871 := bstep (se 1 (by rfl) ⟨11861153, by rfl⟩ : syracuseStep 15814871 = 23722307) B23722307
theorem B10543247 : Blo 2193435 10543247 := bstep (se 1 (by rfl) ⟨7907435, by rfl⟩ : syracuseStep 10543247 = 15814871) B15814871
theorem B7028831 : Blo 2193435 7028831 := bstep (se 1 (by rfl) ⟨5271623, by rfl⟩ : syracuseStep 7028831 = 10543247) B10543247
theorem B4685887 : Blo 2193435 4685887 := bstep (se 1 (by rfl) ⟨3514415, by rfl⟩ : syracuseStep 4685887 = 7028831) B7028831
theorem B6247849 : Blo 2193435 6247849 := bstep (se 2 (by rfl) ⟨2342943, by rfl⟩ : syracuseStep 6247849 = 4685887) B4685887
theorem B8330465 : Blo 2193435 8330465 := bstep (se 2 (by rfl) ⟨3123924, by rfl⟩ : syracuseStep 8330465 = 6247849) B6247849
theorem B5553643 : Blo 2193435 5553643 := bstep (se 1 (by rfl) ⟨4165232, by rfl⟩ : syracuseStep 5553643 = 8330465) B8330465
theorem B7404857 : Blo 2193435 7404857 := bstep (se 2 (by rfl) ⟨2776821, by rfl⟩ : syracuseStep 7404857 = 5553643) B5553643
theorem B4936571 : Blo 2193435 4936571 := bstep (se 1 (by rfl) ⟨3702428, by rfl⟩ : syracuseStep 4936571 = 7404857) B7404857
theorem B3291047 : Blo 2193435 3291047 := bstep (se 1 (by rfl) ⟨2468285, by rfl⟩ : syracuseStep 3291047 = 4936571) B4936571
theorem B2194031 : Blo 2193435 2194031 := bstep (se 1 (by rfl) ⟨1645523, by rfl⟩ : syracuseStep 2194031 = 3291047) B3291047
theorem B3291053 : Blo 2193435 3291053 := bbase (se 3 (by rfl) ⟨617072, by rfl⟩ : syracuseStep 3291053 = 1234145) (by norm_num)
theorem B2194035 : Blo 2193435 2194035 := bstep (se 1 (by rfl) ⟨1645526, by rfl⟩ : syracuseStep 2194035 = 3291053) B3291053
theorem B4936589 : Blo 2193435 4936589 := bbase (se 3 (by rfl) ⟨925610, by rfl⟩ : syracuseStep 4936589 = 1851221) (by norm_num)
theorem B3291059 : Blo 2193435 3291059 := bstep (se 1 (by rfl) ⟨2468294, by rfl⟩ : syracuseStep 3291059 = 4936589) B4936589
theorem B2194039 : Blo 2193435 2194039 := bstep (se 1 (by rfl) ⟨1645529, by rfl⟩ : syracuseStep 2194039 = 3291059) B3291059
theorem B2776837 : Blo 2193435 2776837 := bbase (se 4 (by rfl) ⟨260328, by rfl⟩ : syracuseStep 2776837 = 520657) (by norm_num)
theorem B3702449 : Blo 2193435 3702449 := bstep (se 2 (by rfl) ⟨1388418, by rfl⟩ : syracuseStep 3702449 = 2776837) B2776837
theorem B2468299 : Blo 2193435 2468299 := bstep (se 1 (by rfl) ⟨1851224, by rfl⟩ : syracuseStep 2468299 = 3702449) B3702449
theorem B3291065 : Blo 2193435 3291065 := bstep (se 2 (by rfl) ⟨1234149, by rfl⟩ : syracuseStep 3291065 = 2468299) B2468299
theorem B2194043 : Blo 2193435 2194043 := bstep (se 1 (by rfl) ⟨1645532, by rfl⟩ : syracuseStep 2194043 = 3291065) B3291065
theorem B5271661 : Blo 2193435 5271661 := bbase (se 3 (by rfl) ⟨988436, by rfl⟩ : syracuseStep 5271661 = 1976873) (by norm_num)
theorem B28115525 : Blo 2193435 28115525 := bstep (se 4 (by rfl) ⟨2635830, by rfl⟩ : syracuseStep 28115525 = 5271661) B5271661
theorem B18743683 : Blo 2193435 18743683 := bstep (se 1 (by rfl) ⟨14057762, by rfl⟩ : syracuseStep 18743683 = 28115525) B28115525
theorem B24991577 : Blo 2193435 24991577 := bstep (se 2 (by rfl) ⟨9371841, by rfl⟩ : syracuseStep 24991577 = 18743683) B18743683
theorem B16661051 : Blo 2193435 16661051 := bstep (se 1 (by rfl) ⟨12495788, by rfl⟩ : syracuseStep 16661051 = 24991577) B24991577
theorem B11107367 : Blo 2193435 11107367 := bstep (se 1 (by rfl) ⟨8330525, by rfl⟩ : syracuseStep 11107367 = 16661051) B16661051
theorem B7404911 : Blo 2193435 7404911 := bstep (se 1 (by rfl) ⟨5553683, by rfl⟩ : syracuseStep 7404911 = 11107367) B11107367
theorem B4936607 : Blo 2193435 4936607 := bstep (se 1 (by rfl) ⟨3702455, by rfl⟩ : syracuseStep 4936607 = 7404911) B7404911
theorem B3291071 : Blo 2193435 3291071 := bstep (se 1 (by rfl) ⟨2468303, by rfl⟩ : syracuseStep 3291071 = 4936607) B4936607
theorem B2194047 : Blo 2193435 2194047 := bstep (se 1 (by rfl) ⟨1645535, by rfl⟩ : syracuseStep 2194047 = 3291071) B3291071
theorem B3291077 : Blo 2193435 3291077 := bbase (se 4 (by rfl) ⟨308538, by rfl⟩ : syracuseStep 3291077 = 617077) (by norm_num)
theorem B2194051 : Blo 2193435 2194051 := bstep (se 1 (by rfl) ⟨1645538, by rfl⟩ : syracuseStep 2194051 = 3291077) B3291077
theorem B3702469 : Blo 2193435 3702469 := bbase (se 4 (by rfl) ⟨347106, by rfl⟩ : syracuseStep 3702469 = 694213) (by norm_num)
theorem B4936625 : Blo 2193435 4936625 := bstep (se 2 (by rfl) ⟨1851234, by rfl⟩ : syracuseStep 4936625 = 3702469) B3702469
theorem B3291083 : Blo 2193435 3291083 := bstep (se 1 (by rfl) ⟨2468312, by rfl⟩ : syracuseStep 3291083 = 4936625) B4936625
theorem B2194055 : Blo 2193435 2194055 := bstep (se 1 (by rfl) ⟨1645541, by rfl⟩ : syracuseStep 2194055 = 3291083) B3291083
theorem B2468317 : Blo 2193435 2468317 := bbase (se 3 (by rfl) ⟨462809, by rfl⟩ : syracuseStep 2468317 = 925619) (by norm_num)
theorem B3291089 : Blo 2193435 3291089 := bstep (se 2 (by rfl) ⟨1234158, by rfl⟩ : syracuseStep 3291089 = 2468317) B2468317
theorem B2194059 : Blo 2193435 2194059 := bstep (se 1 (by rfl) ⟨1645544, by rfl⟩ : syracuseStep 2194059 = 3291089) B3291089
theorem B7404965 : Blo 2193435 7404965 := bbase (se 4 (by rfl) ⟨694215, by rfl⟩ : syracuseStep 7404965 = 1388431) (by norm_num)
theorem B4936643 : Blo 2193435 4936643 := bstep (se 1 (by rfl) ⟨3702482, by rfl⟩ : syracuseStep 4936643 = 7404965) B7404965
theorem B3291095 : Blo 2193435 3291095 := bstep (se 1 (by rfl) ⟨2468321, by rfl⟩ : syracuseStep 3291095 = 4936643) B4936643
theorem B2194063 : Blo 2193435 2194063 := bstep (se 1 (by rfl) ⟨1645547, by rfl⟩ : syracuseStep 2194063 = 3291095) B3291095
theorem B3291101 : Blo 2193435 3291101 := bbase (se 3 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 3291101 = 1234163) (by norm_num)
theorem B2194067 : Blo 2193435 2194067 := bstep (se 1 (by rfl) ⟨1645550, by rfl⟩ : syracuseStep 2194067 = 3291101) B3291101
theorem B4936661 : Blo 2193435 4936661 := bbase (se 7 (by rfl) ⟨57851, by rfl⟩ : syracuseStep 4936661 = 115703) (by norm_num)
theorem B3291107 : Blo 2193435 3291107 := bstep (se 1 (by rfl) ⟨2468330, by rfl⟩ : syracuseStep 3291107 = 4936661) B4936661
theorem B2194071 : Blo 2193435 2194071 := bstep (se 1 (by rfl) ⟨1645553, by rfl⟩ : syracuseStep 2194071 = 3291107) B3291107
theorem B15815189 : Blo 2193435 15815189 := bbase (se 6 (by rfl) ⟨370668, by rfl⟩ : syracuseStep 15815189 = 741337) (by norm_num)
theorem B10543459 : Blo 2193435 10543459 := bstep (se 1 (by rfl) ⟨7907594, by rfl⟩ : syracuseStep 10543459 = 15815189) B15815189
theorem B14057945 : Blo 2193435 14057945 := bstep (se 2 (by rfl) ⟨5271729, by rfl⟩ : syracuseStep 14057945 = 10543459) B10543459
theorem B9371963 : Blo 2193435 9371963 := bstep (se 1 (by rfl) ⟨7028972, by rfl⟩ : syracuseStep 9371963 = 14057945) B14057945
theorem B6247975 : Blo 2193435 6247975 := bstep (se 1 (by rfl) ⟨4685981, by rfl⟩ : syracuseStep 6247975 = 9371963) B9371963
theorem B8330633 : Blo 2193435 8330633 := bstep (se 2 (by rfl) ⟨3123987, by rfl⟩ : syracuseStep 8330633 = 6247975) B6247975
theorem B5553755 : Blo 2193435 5553755 := bstep (se 1 (by rfl) ⟨4165316, by rfl⟩ : syracuseStep 5553755 = 8330633) B8330633
theorem B3702503 : Blo 2193435 3702503 := bstep (se 1 (by rfl) ⟨2776877, by rfl⟩ : syracuseStep 3702503 = 5553755) B5553755
theorem B2468335 : Blo 2193435 2468335 := bstep (se 1 (by rfl) ⟨1851251, by rfl⟩ : syracuseStep 2468335 = 3702503) B3702503
theorem B3291113 : Blo 2193435 3291113 := bstep (se 2 (by rfl) ⟨1234167, by rfl⟩ : syracuseStep 3291113 = 2468335) B2468335
theorem B2194075 : Blo 2193435 2194075 := bstep (se 1 (by rfl) ⟨1645556, by rfl⟩ : syracuseStep 2194075 = 3291113) B3291113
theorem B18743957 : Blo 2193435 18743957 := bbase (se 6 (by rfl) ⟨439311, by rfl⟩ : syracuseStep 18743957 = 878623) (by norm_num)
theorem B12495971 : Blo 2193435 12495971 := bstep (se 1 (by rfl) ⟨9371978, by rfl⟩ : syracuseStep 12495971 = 18743957) B18743957
theorem B8330647 : Blo 2193435 8330647 := bstep (se 1 (by rfl) ⟨6247985, by rfl⟩ : syracuseStep 8330647 = 12495971) B12495971
theorem B11107529 : Blo 2193435 11107529 := bstep (se 2 (by rfl) ⟨4165323, by rfl⟩ : syracuseStep 11107529 = 8330647) B8330647
theorem B7405019 : Blo 2193435 7405019 := bstep (se 1 (by rfl) ⟨5553764, by rfl⟩ : syracuseStep 7405019 = 11107529) B11107529
theorem B4936679 : Blo 2193435 4936679 := bstep (se 1 (by rfl) ⟨3702509, by rfl⟩ : syracuseStep 4936679 = 7405019) B7405019
theorem B3291119 : Blo 2193435 3291119 := bstep (se 1 (by rfl) ⟨2468339, by rfl⟩ : syracuseStep 3291119 = 4936679) B4936679
theorem B2194079 : Blo 2193435 2194079 := bstep (se 1 (by rfl) ⟨1645559, by rfl⟩ : syracuseStep 2194079 = 3291119) B3291119
theorem B3291125 : Blo 2193435 3291125 := bbase (se 5 (by rfl) ⟨154271, by rfl⟩ : syracuseStep 3291125 = 308543) (by norm_num)
theorem B2194083 : Blo 2193435 2194083 := bstep (se 1 (by rfl) ⟨1645562, by rfl⟩ : syracuseStep 2194083 = 3291125) B3291125
theorem B8444341 : Blo 2193435 8444341 := bbase (se 5 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 8444341 = 791657) (by norm_num)
theorem B11259121 : Blo 2193435 11259121 := bstep (se 2 (by rfl) ⟨4222170, by rfl⟩ : syracuseStep 11259121 = 8444341) B8444341
theorem B15012161 : Blo 2193435 15012161 := bstep (se 2 (by rfl) ⟨5629560, by rfl⟩ : syracuseStep 15012161 = 11259121) B11259121
theorem B10008107 : Blo 2193435 10008107 := bstep (se 1 (by rfl) ⟨7506080, by rfl⟩ : syracuseStep 10008107 = 15012161) B15012161
theorem B6672071 : Blo 2193435 6672071 := bstep (se 1 (by rfl) ⟨5004053, by rfl⟩ : syracuseStep 6672071 = 10008107) B10008107
theorem B4448047 : Blo 2193435 4448047 := bstep (se 1 (by rfl) ⟨3336035, by rfl⟩ : syracuseStep 4448047 = 6672071) B6672071
theorem B5930729 : Blo 2193435 5930729 := bstep (se 2 (by rfl) ⟨2224023, by rfl⟩ : syracuseStep 5930729 = 4448047) B4448047
theorem B3953819 : Blo 2193435 3953819 := bstep (se 1 (by rfl) ⟨2965364, by rfl⟩ : syracuseStep 3953819 = 5930729) B5930729
theorem B10543517 : Blo 2193435 10543517 := bstep (se 3 (by rfl) ⟨1976909, by rfl⟩ : syracuseStep 10543517 = 3953819) B3953819
theorem B7029011 : Blo 2193435 7029011 := bstep (se 1 (by rfl) ⟨5271758, by rfl⟩ : syracuseStep 7029011 = 10543517) B10543517
theorem B4686007 : Blo 2193435 4686007 := bstep (se 1 (by rfl) ⟨3514505, by rfl⟩ : syracuseStep 4686007 = 7029011) B7029011
theorem B6248009 : Blo 2193435 6248009 := bstep (se 2 (by rfl) ⟨2343003, by rfl⟩ : syracuseStep 6248009 = 4686007) B4686007
theorem B4165339 : Blo 2193435 4165339 := bstep (se 1 (by rfl) ⟨3124004, by rfl⟩ : syracuseStep 4165339 = 6248009) B6248009
theorem B5553785 : Blo 2193435 5553785 := bstep (se 2 (by rfl) ⟨2082669, by rfl⟩ : syracuseStep 5553785 = 4165339) B4165339
theorem B3702523 : Blo 2193435 3702523 := bstep (se 1 (by rfl) ⟨2776892, by rfl⟩ : syracuseStep 3702523 = 5553785) B5553785
theorem B4936697 : Blo 2193435 4936697 := bstep (se 2 (by rfl) ⟨1851261, by rfl⟩ : syracuseStep 4936697 = 3702523) B3702523
theorem B3291131 : Blo 2193435 3291131 := bstep (se 1 (by rfl) ⟨2468348, by rfl⟩ : syracuseStep 3291131 = 4936697) B4936697
theorem B2194087 : Blo 2193435 2194087 := bstep (se 1 (by rfl) ⟨1645565, by rfl⟩ : syracuseStep 2194087 = 3291131) B3291131
theorem B2468353 : Blo 2193435 2468353 := bbase (se 2 (by rfl) ⟨925632, by rfl⟩ : syracuseStep 2468353 = 1851265) (by norm_num)
theorem B3291137 : Blo 2193435 3291137 := bstep (se 2 (by rfl) ⟨1234176, by rfl⟩ : syracuseStep 3291137 = 2468353) B2468353
theorem B2194091 : Blo 2193435 2194091 := bstep (se 1 (by rfl) ⟨1645568, by rfl⟩ : syracuseStep 2194091 = 3291137) B3291137
theorem B5553805 : Blo 2193435 5553805 := bbase (se 3 (by rfl) ⟨1041338, by rfl⟩ : syracuseStep 5553805 = 2082677) (by norm_num)
theorem B7405073 : Blo 2193435 7405073 := bstep (se 2 (by rfl) ⟨2776902, by rfl⟩ : syracuseStep 7405073 = 5553805) B5553805
theorem B4936715 : Blo 2193435 4936715 := bstep (se 1 (by rfl) ⟨3702536, by rfl⟩ : syracuseStep 4936715 = 7405073) B7405073
theorem B3291143 : Blo 2193435 3291143 := bstep (se 1 (by rfl) ⟨2468357, by rfl⟩ : syracuseStep 3291143 = 4936715) B4936715
theorem B2194095 : Blo 2193435 2194095 := bstep (se 1 (by rfl) ⟨1645571, by rfl⟩ : syracuseStep 2194095 = 3291143) B3291143
theorem B3291149 : Blo 2193435 3291149 := bbase (se 3 (by rfl) ⟨617090, by rfl⟩ : syracuseStep 3291149 = 1234181) (by norm_num)
theorem B2194099 : Blo 2193435 2194099 := bstep (se 1 (by rfl) ⟨1645574, by rfl⟩ : syracuseStep 2194099 = 3291149) B3291149
theorem B4936733 : Blo 2193435 4936733 := bbase (se 3 (by rfl) ⟨925637, by rfl⟩ : syracuseStep 4936733 = 1851275) (by norm_num)
theorem B3291155 : Blo 2193435 3291155 := bstep (se 1 (by rfl) ⟨2468366, by rfl⟩ : syracuseStep 3291155 = 4936733) B4936733
theorem B2194103 : Blo 2193435 2194103 := bstep (se 1 (by rfl) ⟨1645577, by rfl⟩ : syracuseStep 2194103 = 3291155) B3291155
theorem B3702557 : Blo 2193435 3702557 := bbase (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) (by norm_num)
theorem B2468371 : Blo 2193435 2468371 := bstep (se 1 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 2468371 = 3702557) B3702557
theorem B3291161 : Blo 2193435 3291161 := bstep (se 2 (by rfl) ⟨1234185, by rfl⟩ : syracuseStep 3291161 = 2468371) B2468371
theorem B2194107 : Blo 2193435 2194107 := bstep (se 1 (by rfl) ⟨1645580, by rfl⟩ : syracuseStep 2194107 = 3291161) B3291161
theorem B5629621 : Blo 2193435 5629621 := bbase (se 5 (by rfl) ⟨263888, by rfl⟩ : syracuseStep 5629621 = 527777) (by norm_num)
theorem B7506161 : Blo 2193435 7506161 := bstep (se 2 (by rfl) ⟨2814810, by rfl⟩ : syracuseStep 7506161 = 5629621) B5629621
theorem B5004107 : Blo 2193435 5004107 := bstep (se 1 (by rfl) ⟨3753080, by rfl⟩ : syracuseStep 5004107 = 7506161) B7506161
theorem B3336071 : Blo 2193435 3336071 := bstep (se 1 (by rfl) ⟨2502053, by rfl⟩ : syracuseStep 3336071 = 5004107) B5004107
theorem B8896189 : Blo 2193435 8896189 := bstep (se 3 (by rfl) ⟨1668035, by rfl⟩ : syracuseStep 8896189 = 3336071) B3336071
theorem B11861585 : Blo 2193435 11861585 := bstep (se 2 (by rfl) ⟨4448094, by rfl⟩ : syracuseStep 11861585 = 8896189) B8896189
theorem B7907723 : Blo 2193435 7907723 := bstep (se 1 (by rfl) ⟨5930792, by rfl⟩ : syracuseStep 7907723 = 11861585) B11861585
theorem B5271815 : Blo 2193435 5271815 := bstep (se 1 (by rfl) ⟨3953861, by rfl⟩ : syracuseStep 5271815 = 7907723) B7907723
theorem B14058173 : Blo 2193435 14058173 := bstep (se 3 (by rfl) ⟨2635907, by rfl⟩ : syracuseStep 14058173 = 5271815) B5271815
theorem B9372115 : Blo 2193435 9372115 := bstep (se 1 (by rfl) ⟨7029086, by rfl⟩ : syracuseStep 9372115 = 14058173) B14058173
theorem B12496153 : Blo 2193435 12496153 := bstep (se 2 (by rfl) ⟨4686057, by rfl⟩ : syracuseStep 12496153 = 9372115) B9372115
theorem B16661537 : Blo 2193435 16661537 := bstep (se 2 (by rfl) ⟨6248076, by rfl⟩ : syracuseStep 16661537 = 12496153) B12496153
theorem B11107691 : Blo 2193435 11107691 := bstep (se 1 (by rfl) ⟨8330768, by rfl⟩ : syracuseStep 11107691 = 16661537) B16661537
theorem B7405127 : Blo 2193435 7405127 := bstep (se 1 (by rfl) ⟨5553845, by rfl⟩ : syracuseStep 7405127 = 11107691) B11107691
theorem B4936751 : Blo 2193435 4936751 := bstep (se 1 (by rfl) ⟨3702563, by rfl⟩ : syracuseStep 4936751 = 7405127) B7405127
theorem B3291167 : Blo 2193435 3291167 := bstep (se 1 (by rfl) ⟨2468375, by rfl⟩ : syracuseStep 3291167 = 4936751) B4936751
theorem B2194111 : Blo 2193435 2194111 := bstep (se 1 (by rfl) ⟨1645583, by rfl⟩ : syracuseStep 2194111 = 3291167) B3291167
theorem B3291173 : Blo 2193435 3291173 := bbase (se 4 (by rfl) ⟨308547, by rfl⟩ : syracuseStep 3291173 = 617095) (by norm_num)
theorem B2194115 : Blo 2193435 2194115 := bstep (se 1 (by rfl) ⟨1645586, by rfl⟩ : syracuseStep 2194115 = 3291173) B3291173
theorem B2776933 : Blo 2193435 2776933 := bbase (se 4 (by rfl) ⟨260337, by rfl⟩ : syracuseStep 2776933 = 520675) (by norm_num)
theorem B3702577 : Blo 2193435 3702577 := bstep (se 2 (by rfl) ⟨1388466, by rfl⟩ : syracuseStep 3702577 = 2776933) B2776933
theorem B4936769 : Blo 2193435 4936769 := bstep (se 2 (by rfl) ⟨1851288, by rfl⟩ : syracuseStep 4936769 = 3702577) B3702577
theorem B3291179 : Blo 2193435 3291179 := bstep (se 1 (by rfl) ⟨2468384, by rfl⟩ : syracuseStep 3291179 = 4936769) B4936769
theorem B2194119 : Blo 2193435 2194119 := bstep (se 1 (by rfl) ⟨1645589, by rfl⟩ : syracuseStep 2194119 = 3291179) B3291179
theorem B2468389 : Blo 2193435 2468389 := bbase (se 4 (by rfl) ⟨231411, by rfl⟩ : syracuseStep 2468389 = 462823) (by norm_num)
theorem B3291185 : Blo 2193435 3291185 := bstep (se 2 (by rfl) ⟨1234194, by rfl⟩ : syracuseStep 3291185 = 2468389) B2468389
theorem B2194123 : Blo 2193435 2194123 := bstep (se 1 (by rfl) ⟨1645592, by rfl⟩ : syracuseStep 2194123 = 3291185) B3291185
theorem B5930837 : Blo 2193435 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B3953891 : Blo 2193435 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B10543709 : Blo 2193435 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B7029139 : Blo 2193435 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B9372185 : Blo 2193435 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B6248123 : Blo 2193435 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B4165415 : Blo 2193435 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B2776943 : Blo 2193435 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B7405181 : Blo 2193435 7405181 := bstep (se 3 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 7405181 = 2776943) B2776943
theorem B4936787 : Blo 2193435 4936787 := bstep (se 1 (by rfl) ⟨3702590, by rfl⟩ : syracuseStep 4936787 = 7405181) B7405181
theorem B3291191 : Blo 2193435 3291191 := bstep (se 1 (by rfl) ⟨2468393, by rfl⟩ : syracuseStep 3291191 = 4936787) B4936787
theorem B2194127 : Blo 2193435 2194127 := bstep (se 1 (by rfl) ⟨1645595, by rfl⟩ : syracuseStep 2194127 = 3291191) B3291191
theorem B3291197 : Blo 2193435 3291197 := bbase (se 3 (by rfl) ⟨617099, by rfl⟩ : syracuseStep 3291197 = 1234199) (by norm_num)
theorem B2194131 : Blo 2193435 2194131 := bstep (se 1 (by rfl) ⟨1645598, by rfl⟩ : syracuseStep 2194131 = 3291197) B3291197
theorem B4936805 : Blo 2193435 4936805 := bbase (se 4 (by rfl) ⟨462825, by rfl⟩ : syracuseStep 4936805 = 925651) (by norm_num)
theorem B3291203 : Blo 2193435 3291203 := bstep (se 1 (by rfl) ⟨2468402, by rfl⟩ : syracuseStep 3291203 = 4936805) B4936805
theorem B2194135 : Blo 2193435 2194135 := bstep (se 1 (by rfl) ⟨1645601, by rfl⟩ : syracuseStep 2194135 = 3291203) B3291203
theorem B5553917 : Blo 2193435 5553917 := bbase (se 3 (by rfl) ⟨1041359, by rfl⟩ : syracuseStep 5553917 = 2082719) (by norm_num)
theorem B3702611 : Blo 2193435 3702611 := bstep (se 1 (by rfl) ⟨2776958, by rfl⟩ : syracuseStep 3702611 = 5553917) B5553917
theorem B2468407 : Blo 2193435 2468407 := bstep (se 1 (by rfl) ⟨1851305, by rfl⟩ : syracuseStep 2468407 = 3702611) B3702611
theorem B3291209 : Blo 2193435 3291209 := bstep (se 2 (by rfl) ⟨1234203, by rfl⟩ : syracuseStep 3291209 = 2468407) B2468407
theorem B2194139 : Blo 2193435 2194139 := bstep (se 1 (by rfl) ⟨1645604, by rfl⟩ : syracuseStep 2194139 = 3291209) B3291209
theorem B4165445 : Blo 2193435 4165445 := bbase (se 4 (by rfl) ⟨390510, by rfl⟩ : syracuseStep 4165445 = 781021) (by norm_num)
theorem B11107853 : Blo 2193435 11107853 := bstep (se 3 (by rfl) ⟨2082722, by rfl⟩ : syracuseStep 11107853 = 4165445) B4165445
theorem B7405235 : Blo 2193435 7405235 := bstep (se 1 (by rfl) ⟨5553926, by rfl⟩ : syracuseStep 7405235 = 11107853) B11107853
theorem B4936823 : Blo 2193435 4936823 := bstep (se 1 (by rfl) ⟨3702617, by rfl⟩ : syracuseStep 4936823 = 7405235) B7405235
theorem B3291215 : Blo 2193435 3291215 := bstep (se 1 (by rfl) ⟨2468411, by rfl⟩ : syracuseStep 3291215 = 4936823) B4936823
theorem B2194143 : Blo 2193435 2194143 := bstep (se 1 (by rfl) ⟨1645607, by rfl⟩ : syracuseStep 2194143 = 3291215) B3291215
theorem B3291221 : Blo 2193435 3291221 := bbase (se 8 (by rfl) ⟨19284, by rfl⟩ : syracuseStep 3291221 = 38569) (by norm_num)
theorem B2194147 : Blo 2193435 2194147 := bstep (se 1 (by rfl) ⟨1645610, by rfl⟩ : syracuseStep 2194147 = 3291221) B3291221
theorem B3005909 : Blo 2193435 3005909 := bbase (se 7 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 3005909 = 70451) (by norm_num)
theorem B32063029 : Blo 2193435 32063029 := bstep (se 5 (by rfl) ⟨1502954, by rfl⟩ : syracuseStep 32063029 = 3005909) B3005909
theorem B171002821 : Blo 2193435 171002821 := bstep (se 4 (by rfl) ⟨16031514, by rfl⟩ : syracuseStep 171002821 = 32063029) B32063029
theorem B228003761 : Blo 2193435 228003761 := bstep (se 2 (by rfl) ⟨85501410, by rfl⟩ : syracuseStep 228003761 = 171002821) B171002821
theorem B152002507 : Blo 2193435 152002507 := bstep (se 1 (by rfl) ⟨114001880, by rfl⟩ : syracuseStep 152002507 = 228003761) B228003761
theorem B202670009 : Blo 2193435 202670009 := bstep (se 2 (by rfl) ⟨76001253, by rfl⟩ : syracuseStep 202670009 = 152002507) B152002507
theorem B135113339 : Blo 2193435 135113339 := bstep (se 1 (by rfl) ⟨101335004, by rfl⟩ : syracuseStep 135113339 = 202670009) B202670009
theorem B90075559 : Blo 2193435 90075559 := bstep (se 1 (by rfl) ⟨67556669, by rfl⟩ : syracuseStep 90075559 = 135113339) B135113339
theorem B120100745 : Blo 2193435 120100745 := bstep (se 2 (by rfl) ⟨45037779, by rfl⟩ : syracuseStep 120100745 = 90075559) B90075559
theorem B80067163 : Blo 2193435 80067163 := bstep (se 1 (by rfl) ⟨60050372, by rfl⟩ : syracuseStep 80067163 = 120100745) B120100745
theorem B106756217 : Blo 2193435 106756217 := bstep (se 2 (by rfl) ⟨40033581, by rfl⟩ : syracuseStep 106756217 = 80067163) B80067163
theorem B71170811 : Blo 2193435 71170811 := bstep (se 1 (by rfl) ⟨53378108, by rfl⟩ : syracuseStep 71170811 = 106756217) B106756217
theorem B47447207 : Blo 2193435 47447207 := bstep (se 1 (by rfl) ⟨35585405, by rfl⟩ : syracuseStep 47447207 = 71170811) B71170811
theorem B31631471 : Blo 2193435 31631471 := bstep (se 1 (by rfl) ⟨23723603, by rfl⟩ : syracuseStep 31631471 = 47447207) B47447207
theorem B21087647 : Blo 2193435 21087647 := bstep (se 1 (by rfl) ⟨15815735, by rfl⟩ : syracuseStep 21087647 = 31631471) B31631471
theorem B14058431 : Blo 2193435 14058431 := bstep (se 1 (by rfl) ⟨10543823, by rfl⟩ : syracuseStep 14058431 = 21087647) B21087647
theorem B9372287 : Blo 2193435 9372287 := bstep (se 1 (by rfl) ⟨7029215, by rfl⟩ : syracuseStep 9372287 = 14058431) B14058431
theorem B6248191 : Blo 2193435 6248191 := bstep (se 1 (by rfl) ⟨4686143, by rfl⟩ : syracuseStep 6248191 = 9372287) B9372287
theorem B8330921 : Blo 2193435 8330921 := bstep (se 2 (by rfl) ⟨3124095, by rfl⟩ : syracuseStep 8330921 = 6248191) B6248191
theorem B5553947 : Blo 2193435 5553947 := bstep (se 1 (by rfl) ⟨4165460, by rfl⟩ : syracuseStep 5553947 = 8330921) B8330921
theorem B3702631 : Blo 2193435 3702631 := bstep (se 1 (by rfl) ⟨2776973, by rfl⟩ : syracuseStep 3702631 = 5553947) B5553947
theorem B4936841 : Blo 2193435 4936841 := bstep (se 2 (by rfl) ⟨1851315, by rfl⟩ : syracuseStep 4936841 = 3702631) B3702631
theorem B3291227 : Blo 2193435 3291227 := bstep (se 1 (by rfl) ⟨2468420, by rfl⟩ : syracuseStep 3291227 = 4936841) B4936841
theorem B2194151 : Blo 2193435 2194151 := bstep (se 1 (by rfl) ⟨1645613, by rfl⟩ : syracuseStep 2194151 = 3291227) B3291227
theorem B2468425 : Blo 2193435 2468425 := bbase (se 2 (by rfl) ⟨925659, by rfl⟩ : syracuseStep 2468425 = 1851319) (by norm_num)
theorem B3291233 : Blo 2193435 3291233 := bstep (se 2 (by rfl) ⟨1234212, by rfl⟩ : syracuseStep 3291233 = 2468425) B2468425
theorem B2194155 : Blo 2193435 2194155 := bstep (se 1 (by rfl) ⟨1645616, by rfl⟩ : syracuseStep 2194155 = 3291233) B3291233
theorem B10543861 : Blo 2193435 10543861 := bbase (se 5 (by rfl) ⟨494243, by rfl⟩ : syracuseStep 10543861 = 988487) (by norm_num)
theorem B14058481 : Blo 2193435 14058481 := bstep (se 2 (by rfl) ⟨5271930, by rfl⟩ : syracuseStep 14058481 = 10543861) B10543861
theorem B18744641 : Blo 2193435 18744641 := bstep (se 2 (by rfl) ⟨7029240, by rfl⟩ : syracuseStep 18744641 = 14058481) B14058481
theorem B12496427 : Blo 2193435 12496427 := bstep (se 1 (by rfl) ⟨9372320, by rfl⟩ : syracuseStep 12496427 = 18744641) B18744641
theorem B8330951 : Blo 2193435 8330951 := bstep (se 1 (by rfl) ⟨6248213, by rfl⟩ : syracuseStep 8330951 = 12496427) B12496427
theorem B5553967 : Blo 2193435 5553967 := bstep (se 1 (by rfl) ⟨4165475, by rfl⟩ : syracuseStep 5553967 = 8330951) B8330951
theorem B7405289 : Blo 2193435 7405289 := bstep (se 2 (by rfl) ⟨2776983, by rfl⟩ : syracuseStep 7405289 = 5553967) B5553967
theorem B4936859 : Blo 2193435 4936859 := bstep (se 1 (by rfl) ⟨3702644, by rfl⟩ : syracuseStep 4936859 = 7405289) B7405289
theorem B3291239 : Blo 2193435 3291239 := bstep (se 1 (by rfl) ⟨2468429, by rfl⟩ : syracuseStep 3291239 = 4936859) B4936859
theorem B2194159 : Blo 2193435 2194159 := bstep (se 1 (by rfl) ⟨1645619, by rfl⟩ : syracuseStep 2194159 = 3291239) B3291239
theorem B3291245 : Blo 2193435 3291245 := bbase (se 3 (by rfl) ⟨617108, by rfl⟩ : syracuseStep 3291245 = 1234217) (by norm_num)
theorem B2194163 : Blo 2193435 2194163 := bstep (se 1 (by rfl) ⟨1645622, by rfl⟩ : syracuseStep 2194163 = 3291245) B3291245
theorem B4936877 : Blo 2193435 4936877 := bbase (se 3 (by rfl) ⟨925664, by rfl⟩ : syracuseStep 4936877 = 1851329) (by norm_num)
theorem B3291251 : Blo 2193435 3291251 := bstep (se 1 (by rfl) ⟨2468438, by rfl⟩ : syracuseStep 3291251 = 4936877) B4936877
theorem B2194167 : Blo 2193435 2194167 := bstep (se 1 (by rfl) ⟨1645625, by rfl⟩ : syracuseStep 2194167 = 3291251) B3291251
theorem B2224109 : Blo 2193435 2224109 := bbase (se 3 (by rfl) ⟨417020, by rfl⟩ : syracuseStep 2224109 = 834041) (by norm_num)
theorem B5930957 : Blo 2193435 5930957 := bstep (se 3 (by rfl) ⟨1112054, by rfl⟩ : syracuseStep 5930957 = 2224109) B2224109
theorem B3953971 : Blo 2193435 3953971 := bstep (se 1 (by rfl) ⟨2965478, by rfl⟩ : syracuseStep 3953971 = 5930957) B5930957
theorem B5271961 : Blo 2193435 5271961 := bstep (se 2 (by rfl) ⟨1976985, by rfl⟩ : syracuseStep 5271961 = 3953971) B3953971
theorem B7029281 : Blo 2193435 7029281 := bstep (se 2 (by rfl) ⟨2635980, by rfl⟩ : syracuseStep 7029281 = 5271961) B5271961
theorem B4686187 : Blo 2193435 4686187 := bstep (se 1 (by rfl) ⟨3514640, by rfl⟩ : syracuseStep 4686187 = 7029281) B7029281
theorem B6248249 : Blo 2193435 6248249 := bstep (se 2 (by rfl) ⟨2343093, by rfl⟩ : syracuseStep 6248249 = 4686187) B4686187
theorem B4165499 : Blo 2193435 4165499 := bstep (se 1 (by rfl) ⟨3124124, by rfl⟩ : syracuseStep 4165499 = 6248249) B6248249
theorem B2776999 : Blo 2193435 2776999 := bstep (se 1 (by rfl) ⟨2082749, by rfl⟩ : syracuseStep 2776999 = 4165499) B4165499
theorem B3702665 : Blo 2193435 3702665 := bstep (se 2 (by rfl) ⟨1388499, by rfl⟩ : syracuseStep 3702665 = 2776999) B2776999
theorem B2468443 : Blo 2193435 2468443 := bstep (se 1 (by rfl) ⟨1851332, by rfl⟩ : syracuseStep 2468443 = 3702665) B3702665
theorem B3291257 : Blo 2193435 3291257 := bstep (se 2 (by rfl) ⟨1234221, by rfl⟩ : syracuseStep 3291257 = 2468443) B2468443
theorem B2194171 : Blo 2193435 2194171 := bstep (se 1 (by rfl) ⟨1645628, by rfl⟩ : syracuseStep 2194171 = 3291257) B3291257
theorem B5930965 : Blo 2193435 5930965 := bbase (se 7 (by rfl) ⟨69503, by rfl⟩ : syracuseStep 5930965 = 139007) (by norm_num)
theorem B7907953 : Blo 2193435 7907953 := bstep (se 2 (by rfl) ⟨2965482, by rfl⟩ : syracuseStep 7907953 = 5930965) B5930965
theorem B10543937 : Blo 2193435 10543937 := bstep (se 2 (by rfl) ⟨3953976, by rfl⟩ : syracuseStep 10543937 = 7907953) B7907953
theorem B28117165 : Blo 2193435 28117165 := bstep (se 3 (by rfl) ⟨5271968, by rfl⟩ : syracuseStep 28117165 = 10543937) B10543937
theorem B37489553 : Blo 2193435 37489553 := bstep (se 2 (by rfl) ⟨14058582, by rfl⟩ : syracuseStep 37489553 = 28117165) B28117165
theorem B24993035 : Blo 2193435 24993035 := bstep (se 1 (by rfl) ⟨18744776, by rfl⟩ : syracuseStep 24993035 = 37489553) B37489553
theorem B16662023 : Blo 2193435 16662023 := bstep (se 1 (by rfl) ⟨12496517, by rfl⟩ : syracuseStep 16662023 = 24993035) B24993035
theorem B11108015 : Blo 2193435 11108015 := bstep (se 1 (by rfl) ⟨8331011, by rfl⟩ : syracuseStep 11108015 = 16662023) B16662023
theorem B7405343 : Blo 2193435 7405343 := bstep (se 1 (by rfl) ⟨5554007, by rfl⟩ : syracuseStep 7405343 = 11108015) B11108015
theorem B4936895 : Blo 2193435 4936895 := bstep (se 1 (by rfl) ⟨3702671, by rfl⟩ : syracuseStep 4936895 = 7405343) B7405343
theorem B3291263 : Blo 2193435 3291263 := bstep (se 1 (by rfl) ⟨2468447, by rfl⟩ : syracuseStep 3291263 = 4936895) B4936895
theorem B2194175 : Blo 2193435 2194175 := bstep (se 1 (by rfl) ⟨1645631, by rfl⟩ : syracuseStep 2194175 = 3291263) B3291263
theorem B3291269 : Blo 2193435 3291269 := bbase (se 4 (by rfl) ⟨308556, by rfl⟩ : syracuseStep 3291269 = 617113) (by norm_num)
theorem B2194179 : Blo 2193435 2194179 := bstep (se 1 (by rfl) ⟨1645634, by rfl⟩ : syracuseStep 2194179 = 3291269) B3291269
theorem B3702685 : Blo 2193435 3702685 := bbase (se 3 (by rfl) ⟨694253, by rfl⟩ : syracuseStep 3702685 = 1388507) (by norm_num)
theorem B4936913 : Blo 2193435 4936913 := bstep (se 2 (by rfl) ⟨1851342, by rfl⟩ : syracuseStep 4936913 = 3702685) B3702685
theorem B3291275 : Blo 2193435 3291275 := bstep (se 1 (by rfl) ⟨2468456, by rfl⟩ : syracuseStep 3291275 = 4936913) B4936913
theorem B2194183 : Blo 2193435 2194183 := bstep (se 1 (by rfl) ⟨1645637, by rfl⟩ : syracuseStep 2194183 = 3291275) B3291275
theorem B2468461 : Blo 2193435 2468461 := bbase (se 3 (by rfl) ⟨462836, by rfl⟩ : syracuseStep 2468461 = 925673) (by norm_num)
theorem B3291281 : Blo 2193435 3291281 := bstep (se 2 (by rfl) ⟨1234230, by rfl⟩ : syracuseStep 3291281 = 2468461) B2468461
theorem B2194187 : Blo 2193435 2194187 := bstep (se 1 (by rfl) ⟨1645640, by rfl⟩ : syracuseStep 2194187 = 3291281) B3291281
theorem B7405397 : Blo 2193435 7405397 := bbase (se 9 (by rfl) ⟨21695, by rfl⟩ : syracuseStep 7405397 = 43391) (by norm_num)
theorem B4936931 : Blo 2193435 4936931 := bstep (se 1 (by rfl) ⟨3702698, by rfl⟩ : syracuseStep 4936931 = 7405397) B7405397
theorem B3291287 : Blo 2193435 3291287 := bstep (se 1 (by rfl) ⟨2468465, by rfl⟩ : syracuseStep 3291287 = 4936931) B4936931
theorem B2194191 : Blo 2193435 2194191 := bstep (se 1 (by rfl) ⟨1645643, by rfl⟩ : syracuseStep 2194191 = 3291287) B3291287
theorem B3291293 : Blo 2193435 3291293 := bbase (se 3 (by rfl) ⟨617117, by rfl⟩ : syracuseStep 3291293 = 1234235) (by norm_num)
theorem B2194195 : Blo 2193435 2194195 := bstep (se 1 (by rfl) ⟨1645646, by rfl⟩ : syracuseStep 2194195 = 3291293) B3291293
theorem B4936949 : Blo 2193435 4936949 := bbase (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) (by norm_num)
theorem B3291299 : Blo 2193435 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B2194199 : Blo 2193435 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B5004317 : Blo 2193435 5004317 := bbase (se 3 (by rfl) ⟨938309, by rfl⟩ : syracuseStep 5004317 = 1876619) (by norm_num)
theorem B3336211 : Blo 2193435 3336211 := bstep (se 1 (by rfl) ⟨2502158, by rfl⟩ : syracuseStep 3336211 = 5004317) B5004317
theorem B17793125 : Blo 2193435 17793125 := bstep (se 4 (by rfl) ⟨1668105, by rfl⟩ : syracuseStep 17793125 = 3336211) B3336211
theorem B11862083 : Blo 2193435 11862083 := bstep (se 1 (by rfl) ⟨8896562, by rfl⟩ : syracuseStep 11862083 = 17793125) B17793125
theorem B31632221 : Blo 2193435 31632221 := bstep (se 3 (by rfl) ⟨5931041, by rfl⟩ : syracuseStep 31632221 = 11862083) B11862083
theorem B21088147 : Blo 2193435 21088147 := bstep (se 1 (by rfl) ⟨15816110, by rfl⟩ : syracuseStep 21088147 = 31632221) B31632221
theorem B28117529 : Blo 2193435 28117529 := bstep (se 2 (by rfl) ⟨10544073, by rfl⟩ : syracuseStep 28117529 = 21088147) B21088147
theorem B18745019 : Blo 2193435 18745019 := bstep (se 1 (by rfl) ⟨14058764, by rfl⟩ : syracuseStep 18745019 = 28117529) B28117529
theorem B12496679 : Blo 2193435 12496679 := bstep (se 1 (by rfl) ⟨9372509, by rfl⟩ : syracuseStep 12496679 = 18745019) B18745019
theorem B8331119 : Blo 2193435 8331119 := bstep (se 1 (by rfl) ⟨6248339, by rfl⟩ : syracuseStep 8331119 = 12496679) B12496679
theorem B5554079 : Blo 2193435 5554079 := bstep (se 1 (by rfl) ⟨4165559, by rfl⟩ : syracuseStep 5554079 = 8331119) B8331119
theorem B3702719 : Blo 2193435 3702719 := bstep (se 1 (by rfl) ⟨2777039, by rfl⟩ : syracuseStep 3702719 = 5554079) B5554079
theorem B2468479 : Blo 2193435 2468479 := bstep (se 1 (by rfl) ⟨1851359, by rfl⟩ : syracuseStep 2468479 = 3702719) B3702719
theorem B3291305 : Blo 2193435 3291305 := bstep (se 2 (by rfl) ⟨1234239, by rfl⟩ : syracuseStep 3291305 = 2468479) B2468479
theorem B2194203 : Blo 2193435 2194203 := bstep (se 1 (by rfl) ⟨1645652, by rfl⟩ : syracuseStep 2194203 = 3291305) B3291305
theorem B2224145 : Blo 2193435 2224145 := bbase (se 2 (by rfl) ⟨834054, by rfl⟩ : syracuseStep 2224145 = 1668109) (by norm_num)
theorem B5931053 : Blo 2193435 5931053 := bstep (se 3 (by rfl) ⟨1112072, by rfl⟩ : syracuseStep 5931053 = 2224145) B2224145
theorem B3954035 : Blo 2193435 3954035 := bstep (se 1 (by rfl) ⟨2965526, by rfl⟩ : syracuseStep 3954035 = 5931053) B5931053
theorem B10544093 : Blo 2193435 10544093 := bstep (se 3 (by rfl) ⟨1977017, by rfl⟩ : syracuseStep 10544093 = 3954035) B3954035
theorem B7029395 : Blo 2193435 7029395 := bstep (se 1 (by rfl) ⟨5272046, by rfl⟩ : syracuseStep 7029395 = 10544093) B10544093
theorem B4686263 : Blo 2193435 4686263 := bstep (se 1 (by rfl) ⟨3514697, by rfl⟩ : syracuseStep 4686263 = 7029395) B7029395
theorem B3124175 : Blo 2193435 3124175 := bstep (se 1 (by rfl) ⟨2343131, by rfl⟩ : syracuseStep 3124175 = 4686263) B4686263
theorem B8331133 : Blo 2193435 8331133 := bstep (se 3 (by rfl) ⟨1562087, by rfl⟩ : syracuseStep 8331133 = 3124175) B3124175
theorem B11108177 : Blo 2193435 11108177 := bstep (se 2 (by rfl) ⟨4165566, by rfl⟩ : syracuseStep 11108177 = 8331133) B8331133
theorem B7405451 : Blo 2193435 7405451 := bstep (se 1 (by rfl) ⟨5554088, by rfl⟩ : syracuseStep 7405451 = 11108177) B11108177
theorem B4936967 : Blo 2193435 4936967 := bstep (se 1 (by rfl) ⟨3702725, by rfl⟩ : syracuseStep 4936967 = 7405451) B7405451
theorem B3291311 : Blo 2193435 3291311 := bstep (se 1 (by rfl) ⟨2468483, by rfl⟩ : syracuseStep 3291311 = 4936967) B4936967
theorem B2194207 : Blo 2193435 2194207 := bstep (se 1 (by rfl) ⟨1645655, by rfl⟩ : syracuseStep 2194207 = 3291311) B3291311
theorem B3291317 : Blo 2193435 3291317 := bbase (se 5 (by rfl) ⟨154280, by rfl⟩ : syracuseStep 3291317 = 308561) (by norm_num)
theorem B2194211 : Blo 2193435 2194211 := bstep (se 1 (by rfl) ⟨1645658, by rfl⟩ : syracuseStep 2194211 = 3291317) B3291317
theorem B5554109 : Blo 2193435 5554109 := bbase (se 3 (by rfl) ⟨1041395, by rfl⟩ : syracuseStep 5554109 = 2082791) (by norm_num)
theorem B3702739 : Blo 2193435 3702739 := bstep (se 1 (by rfl) ⟨2777054, by rfl⟩ : syracuseStep 3702739 = 5554109) B5554109
theorem B4936985 : Blo 2193435 4936985 := bstep (se 2 (by rfl) ⟨1851369, by rfl⟩ : syracuseStep 4936985 = 3702739) B3702739
theorem B3291323 : Blo 2193435 3291323 := bstep (se 1 (by rfl) ⟨2468492, by rfl⟩ : syracuseStep 3291323 = 4936985) B4936985
theorem B2194215 : Blo 2193435 2194215 := bstep (se 1 (by rfl) ⟨1645661, by rfl⟩ : syracuseStep 2194215 = 3291323) B3291323
theorem B2468497 : Blo 2193435 2468497 := bbase (se 2 (by rfl) ⟨925686, by rfl⟩ : syracuseStep 2468497 = 1851373) (by norm_num)
theorem B3291329 : Blo 2193435 3291329 := bstep (se 2 (by rfl) ⟨1234248, by rfl⟩ : syracuseStep 3291329 = 2468497) B2468497
theorem B2194219 : Blo 2193435 2194219 := bstep (se 1 (by rfl) ⟨1645664, by rfl⟩ : syracuseStep 2194219 = 3291329) B3291329
theorem B4165597 : Blo 2193435 4165597 := bbase (se 3 (by rfl) ⟨781049, by rfl⟩ : syracuseStep 4165597 = 1562099) (by norm_num)
theorem B5554129 : Blo 2193435 5554129 := bstep (se 2 (by rfl) ⟨2082798, by rfl⟩ : syracuseStep 5554129 = 4165597) B4165597
theorem B7405505 : Blo 2193435 7405505 := bstep (se 2 (by rfl) ⟨2777064, by rfl⟩ : syracuseStep 7405505 = 5554129) B5554129
theorem B4937003 : Blo 2193435 4937003 := bstep (se 1 (by rfl) ⟨3702752, by rfl⟩ : syracuseStep 4937003 = 7405505) B7405505
theorem B3291335 : Blo 2193435 3291335 := bstep (se 1 (by rfl) ⟨2468501, by rfl⟩ : syracuseStep 3291335 = 4937003) B4937003
theorem B2194223 : Blo 2193435 2194223 := bstep (se 1 (by rfl) ⟨1645667, by rfl⟩ : syracuseStep 2194223 = 3291335) B3291335
theorem B3291341 : Blo 2193435 3291341 := bbase (se 3 (by rfl) ⟨617126, by rfl⟩ : syracuseStep 3291341 = 1234253) (by norm_num)
theorem B2194227 : Blo 2193435 2194227 := bstep (se 1 (by rfl) ⟨1645670, by rfl⟩ : syracuseStep 2194227 = 3291341) B3291341
theorem B4937021 : Blo 2193435 4937021 := bbase (se 3 (by rfl) ⟨925691, by rfl⟩ : syracuseStep 4937021 = 1851383) (by norm_num)
theorem B3291347 : Blo 2193435 3291347 := bstep (se 1 (by rfl) ⟨2468510, by rfl⟩ : syracuseStep 3291347 = 4937021) B4937021
theorem B2194231 : Blo 2193435 2194231 := bstep (se 1 (by rfl) ⟨1645673, by rfl⟩ : syracuseStep 2194231 = 3291347) B3291347
theorem B3702773 : Blo 2193435 3702773 := bbase (se 5 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 3702773 = 347135) (by norm_num)
theorem B2468515 : Blo 2193435 2468515 := bstep (se 1 (by rfl) ⟨1851386, by rfl⟩ : syracuseStep 2468515 = 3702773) B3702773
theorem B3291353 : Blo 2193435 3291353 := bstep (se 2 (by rfl) ⟨1234257, by rfl⟩ : syracuseStep 3291353 = 2468515) B2468515
theorem B2194235 : Blo 2193435 2194235 := bstep (se 1 (by rfl) ⟨1645676, by rfl⟩ : syracuseStep 2194235 = 3291353) B3291353
theorem B8896709 : Blo 2193435 8896709 := bbase (se 4 (by rfl) ⟨834066, by rfl⟩ : syracuseStep 8896709 = 1668133) (by norm_num)
theorem B5931139 : Blo 2193435 5931139 := bstep (se 1 (by rfl) ⟨4448354, by rfl⟩ : syracuseStep 5931139 = 8896709) B8896709
theorem B7908185 : Blo 2193435 7908185 := bstep (se 2 (by rfl) ⟨2965569, by rfl⟩ : syracuseStep 7908185 = 5931139) B5931139
theorem B5272123 : Blo 2193435 5272123 := bstep (se 1 (by rfl) ⟨3954092, by rfl⟩ : syracuseStep 5272123 = 7908185) B7908185
theorem B7029497 : Blo 2193435 7029497 := bstep (se 2 (by rfl) ⟨2636061, by rfl⟩ : syracuseStep 7029497 = 5272123) B5272123
theorem B4686331 : Blo 2193435 4686331 := bstep (se 1 (by rfl) ⟨3514748, by rfl⟩ : syracuseStep 4686331 = 7029497) B7029497
theorem B6248441 : Blo 2193435 6248441 := bstep (se 2 (by rfl) ⟨2343165, by rfl⟩ : syracuseStep 6248441 = 4686331) B4686331
theorem B16662509 : Blo 2193435 16662509 := bstep (se 3 (by rfl) ⟨3124220, by rfl⟩ : syracuseStep 16662509 = 6248441) B6248441
theorem B11108339 : Blo 2193435 11108339 := bstep (se 1 (by rfl) ⟨8331254, by rfl⟩ : syracuseStep 11108339 = 16662509) B16662509
theorem B7405559 : Blo 2193435 7405559 := bstep (se 1 (by rfl) ⟨5554169, by rfl⟩ : syracuseStep 7405559 = 11108339) B11108339
theorem B4937039 : Blo 2193435 4937039 := bstep (se 1 (by rfl) ⟨3702779, by rfl⟩ : syracuseStep 4937039 = 7405559) B7405559
theorem B3291359 : Blo 2193435 3291359 := bstep (se 1 (by rfl) ⟨2468519, by rfl⟩ : syracuseStep 3291359 = 4937039) B4937039
theorem B2194239 : Blo 2193435 2194239 := bstep (se 1 (by rfl) ⟨1645679, by rfl⟩ : syracuseStep 2194239 = 3291359) B3291359
theorem B3291365 : Blo 2193435 3291365 := bbase (se 4 (by rfl) ⟨308565, by rfl⟩ : syracuseStep 3291365 = 617131) (by norm_num)
theorem B2194243 : Blo 2193435 2194243 := bstep (se 1 (by rfl) ⟨1645682, by rfl⟩ : syracuseStep 2194243 = 3291365) B3291365
theorem B4686349 : Blo 2193435 4686349 := bbase (se 3 (by rfl) ⟨878690, by rfl⟩ : syracuseStep 4686349 = 1757381) (by norm_num)
theorem B6248465 : Blo 2193435 6248465 := bstep (se 2 (by rfl) ⟨2343174, by rfl⟩ : syracuseStep 6248465 = 4686349) B4686349
theorem B4165643 : Blo 2193435 4165643 := bstep (se 1 (by rfl) ⟨3124232, by rfl⟩ : syracuseStep 4165643 = 6248465) B6248465
theorem B2777095 : Blo 2193435 2777095 := bstep (se 1 (by rfl) ⟨2082821, by rfl⟩ : syracuseStep 2777095 = 4165643) B4165643
theorem B3702793 : Blo 2193435 3702793 := bstep (se 2 (by rfl) ⟨1388547, by rfl⟩ : syracuseStep 3702793 = 2777095) B2777095
theorem B4937057 : Blo 2193435 4937057 := bstep (se 2 (by rfl) ⟨1851396, by rfl⟩ : syracuseStep 4937057 = 3702793) B3702793
theorem B3291371 : Blo 2193435 3291371 := bstep (se 1 (by rfl) ⟨2468528, by rfl⟩ : syracuseStep 3291371 = 4937057) B4937057
theorem B2194247 : Blo 2193435 2194247 := bstep (se 1 (by rfl) ⟨1645685, by rfl⟩ : syracuseStep 2194247 = 3291371) B3291371
theorem B2468533 : Blo 2193435 2468533 := bbase (se 5 (by rfl) ⟨115712, by rfl⟩ : syracuseStep 2468533 = 231425) (by norm_num)
theorem B3291377 : Blo 2193435 3291377 := bstep (se 2 (by rfl) ⟨1234266, by rfl⟩ : syracuseStep 3291377 = 2468533) B2468533
theorem B2194251 : Blo 2193435 2194251 := bstep (se 1 (by rfl) ⟨1645688, by rfl⟩ : syracuseStep 2194251 = 3291377) B3291377
theorem B2777105 : Blo 2193435 2777105 := bbase (se 2 (by rfl) ⟨1041414, by rfl⟩ : syracuseStep 2777105 = 2082829) (by norm_num)
theorem B7405613 : Blo 2193435 7405613 := bstep (se 3 (by rfl) ⟨1388552, by rfl⟩ : syracuseStep 7405613 = 2777105) B2777105
theorem B4937075 : Blo 2193435 4937075 := bstep (se 1 (by rfl) ⟨3702806, by rfl⟩ : syracuseStep 4937075 = 7405613) B7405613
theorem B3291383 : Blo 2193435 3291383 := bstep (se 1 (by rfl) ⟨2468537, by rfl⟩ : syracuseStep 3291383 = 4937075) B4937075
theorem B2194255 : Blo 2193435 2194255 := bstep (se 1 (by rfl) ⟨1645691, by rfl⟩ : syracuseStep 2194255 = 3291383) B3291383
theorem B3291389 : Blo 2193435 3291389 := bbase (se 3 (by rfl) ⟨617135, by rfl⟩ : syracuseStep 3291389 = 1234271) (by norm_num)
theorem B2194259 : Blo 2193435 2194259 := bstep (se 1 (by rfl) ⟨1645694, by rfl⟩ : syracuseStep 2194259 = 3291389) B3291389
theorem B4937093 : Blo 2193435 4937093 := bbase (se 4 (by rfl) ⟨462852, by rfl⟩ : syracuseStep 4937093 = 925705) (by norm_num)
theorem B3291395 : Blo 2193435 3291395 := bstep (se 1 (by rfl) ⟨2468546, by rfl⟩ : syracuseStep 3291395 = 4937093) B4937093
theorem B2194263 : Blo 2193435 2194263 := bstep (se 1 (by rfl) ⟨1645697, by rfl⟩ : syracuseStep 2194263 = 3291395) B3291395
theorem B3124261 : Blo 2193435 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B4165681 : Blo 2193435 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B5554241 : Blo 2193435 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B3702827 : Blo 2193435 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B2468551 : Blo 2193435 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B3291401 : Blo 2193435 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B2194267 : Blo 2193435 2194267 := bstep (se 1 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 2194267 = 3291401) B3291401
theorem B11108501 : Blo 2193435 11108501 := bbase (se 6 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 11108501 = 520711) (by norm_num)
theorem B7405667 : Blo 2193435 7405667 := bstep (se 1 (by rfl) ⟨5554250, by rfl⟩ : syracuseStep 7405667 = 11108501) B11108501
theorem B4937111 : Blo 2193435 4937111 := bstep (se 1 (by rfl) ⟨3702833, by rfl⟩ : syracuseStep 4937111 = 7405667) B7405667
theorem B3291407 : Blo 2193435 3291407 := bstep (se 1 (by rfl) ⟨2468555, by rfl⟩ : syracuseStep 3291407 = 4937111) B4937111
theorem B2194271 : Blo 2193435 2194271 := bstep (se 1 (by rfl) ⟨1645703, by rfl⟩ : syracuseStep 2194271 = 3291407) B3291407
theorem B3291413 : Blo 2193435 3291413 := bbase (se 6 (by rfl) ⟨77142, by rfl⟩ : syracuseStep 3291413 = 154285) (by norm_num)
theorem B2194275 : Blo 2193435 2194275 := bstep (se 1 (by rfl) ⟨1645706, by rfl⟩ : syracuseStep 2194275 = 3291413) B3291413
theorem B12024341 : Blo 2193435 12024341 := bbase (se 6 (by rfl) ⟨281820, by rfl⟩ : syracuseStep 12024341 = 563641) (by norm_num)
theorem B8016227 : Blo 2193435 8016227 := bstep (se 1 (by rfl) ⟨6012170, by rfl⟩ : syracuseStep 8016227 = 12024341) B12024341
theorem B5344151 : Blo 2193435 5344151 := bstep (se 1 (by rfl) ⟨4008113, by rfl⟩ : syracuseStep 5344151 = 8016227) B8016227
theorem B14251069 : Blo 2193435 14251069 := bstep (se 3 (by rfl) ⟨2672075, by rfl⟩ : syracuseStep 14251069 = 5344151) B5344151
theorem B76005701 : Blo 2193435 76005701 := bstep (se 4 (by rfl) ⟨7125534, by rfl⟩ : syracuseStep 76005701 = 14251069) B14251069
theorem B50670467 : Blo 2193435 50670467 := bstep (se 1 (by rfl) ⟨38002850, by rfl⟩ : syracuseStep 50670467 = 76005701) B76005701
theorem B33780311 : Blo 2193435 33780311 := bstep (se 1 (by rfl) ⟨25335233, by rfl⟩ : syracuseStep 33780311 = 50670467) B50670467
theorem B22520207 : Blo 2193435 22520207 := bstep (se 1 (by rfl) ⟨16890155, by rfl⟩ : syracuseStep 22520207 = 33780311) B33780311
theorem B15013471 : Blo 2193435 15013471 := bstep (se 1 (by rfl) ⟨11260103, by rfl⟩ : syracuseStep 15013471 = 22520207) B22520207
theorem B20017961 : Blo 2193435 20017961 := bstep (se 2 (by rfl) ⟨7506735, by rfl⟩ : syracuseStep 20017961 = 15013471) B15013471
theorem B13345307 : Blo 2193435 13345307 := bstep (se 1 (by rfl) ⟨10008980, by rfl⟩ : syracuseStep 13345307 = 20017961) B20017961
theorem B8896871 : Blo 2193435 8896871 := bstep (se 1 (by rfl) ⟨6672653, by rfl⟩ : syracuseStep 8896871 = 13345307) B13345307
theorem B5931247 : Blo 2193435 5931247 := bstep (se 1 (by rfl) ⟨4448435, by rfl⟩ : syracuseStep 5931247 = 8896871) B8896871
theorem B7908329 : Blo 2193435 7908329 := bstep (se 2 (by rfl) ⟨2965623, by rfl⟩ : syracuseStep 7908329 = 5931247) B5931247
theorem B5272219 : Blo 2193435 5272219 := bstep (se 1 (by rfl) ⟨3954164, by rfl⟩ : syracuseStep 5272219 = 7908329) B7908329
theorem B28118501 : Blo 2193435 28118501 := bstep (se 4 (by rfl) ⟨2636109, by rfl⟩ : syracuseStep 28118501 = 5272219) B5272219
theorem B18745667 : Blo 2193435 18745667 := bstep (se 1 (by rfl) ⟨14059250, by rfl⟩ : syracuseStep 18745667 = 28118501) B28118501
theorem B12497111 : Blo 2193435 12497111 := bstep (se 1 (by rfl) ⟨9372833, by rfl⟩ : syracuseStep 12497111 = 18745667) B18745667
theorem B8331407 : Blo 2193435 8331407 := bstep (se 1 (by rfl) ⟨6248555, by rfl⟩ : syracuseStep 8331407 = 12497111) B12497111
theorem B5554271 : Blo 2193435 5554271 := bstep (se 1 (by rfl) ⟨4165703, by rfl⟩ : syracuseStep 5554271 = 8331407) B8331407
theorem B3702847 : Blo 2193435 3702847 := bstep (se 1 (by rfl) ⟨2777135, by rfl⟩ : syracuseStep 3702847 = 5554271) B5554271
theorem B4937129 : Blo 2193435 4937129 := bstep (se 2 (by rfl) ⟨1851423, by rfl⟩ : syracuseStep 4937129 = 3702847) B3702847
theorem B3291419 : Blo 2193435 3291419 := bstep (se 1 (by rfl) ⟨2468564, by rfl⟩ : syracuseStep 3291419 = 4937129) B4937129
theorem B2194279 : Blo 2193435 2194279 := bstep (se 1 (by rfl) ⟨1645709, by rfl⟩ : syracuseStep 2194279 = 3291419) B3291419
theorem B2468569 : Blo 2193435 2468569 := bbase (se 2 (by rfl) ⟨925713, by rfl⟩ : syracuseStep 2468569 = 1851427) (by norm_num)
theorem B3291425 : Blo 2193435 3291425 := bstep (se 2 (by rfl) ⟨1234284, by rfl⟩ : syracuseStep 3291425 = 2468569) B2468569
theorem B2194283 : Blo 2193435 2194283 := bstep (se 1 (by rfl) ⟨1645712, by rfl⟩ : syracuseStep 2194283 = 3291425) B3291425
theorem B2343217 : Blo 2193435 2343217 := bbase (se 2 (by rfl) ⟨878706, by rfl⟩ : syracuseStep 2343217 = 1757413) (by norm_num)
theorem B3124289 : Blo 2193435 3124289 := bstep (se 2 (by rfl) ⟨1171608, by rfl⟩ : syracuseStep 3124289 = 2343217) B2343217
theorem B8331437 : Blo 2193435 8331437 := bstep (se 3 (by rfl) ⟨1562144, by rfl⟩ : syracuseStep 8331437 = 3124289) B3124289
theorem B5554291 : Blo 2193435 5554291 := bstep (se 1 (by rfl) ⟨4165718, by rfl⟩ : syracuseStep 5554291 = 8331437) B8331437
theorem B7405721 : Blo 2193435 7405721 := bstep (se 2 (by rfl) ⟨2777145, by rfl⟩ : syracuseStep 7405721 = 5554291) B5554291
theorem B4937147 : Blo 2193435 4937147 := bstep (se 1 (by rfl) ⟨3702860, by rfl⟩ : syracuseStep 4937147 = 7405721) B7405721
theorem B3291431 : Blo 2193435 3291431 := bstep (se 1 (by rfl) ⟨2468573, by rfl⟩ : syracuseStep 3291431 = 4937147) B4937147
theorem B2194287 : Blo 2193435 2194287 := bstep (se 1 (by rfl) ⟨1645715, by rfl⟩ : syracuseStep 2194287 = 3291431) B3291431
theorem B3291437 : Blo 2193435 3291437 := bbase (se 3 (by rfl) ⟨617144, by rfl⟩ : syracuseStep 3291437 = 1234289) (by norm_num)
theorem B2194291 : Blo 2193435 2194291 := bstep (se 1 (by rfl) ⟨1645718, by rfl⟩ : syracuseStep 2194291 = 3291437) B3291437
theorem B4937165 : Blo 2193435 4937165 := bbase (se 3 (by rfl) ⟨925718, by rfl⟩ : syracuseStep 4937165 = 1851437) (by norm_num)
theorem B3291443 : Blo 2193435 3291443 := bstep (se 1 (by rfl) ⟨2468582, by rfl⟩ : syracuseStep 3291443 = 4937165) B4937165
theorem B2194295 : Blo 2193435 2194295 := bstep (se 1 (by rfl) ⟨1645721, by rfl⟩ : syracuseStep 2194295 = 3291443) B3291443
theorem B2777161 : Blo 2193435 2777161 := bbase (se 2 (by rfl) ⟨1041435, by rfl⟩ : syracuseStep 2777161 = 2082871) (by norm_num)
theorem B3702881 : Blo 2193435 3702881 := bstep (se 2 (by rfl) ⟨1388580, by rfl⟩ : syracuseStep 3702881 = 2777161) B2777161
theorem B2468587 : Blo 2193435 2468587 := bstep (se 1 (by rfl) ⟨1851440, by rfl⟩ : syracuseStep 2468587 = 3702881) B3702881
theorem B3291449 : Blo 2193435 3291449 := bstep (se 2 (by rfl) ⟨1234293, by rfl⟩ : syracuseStep 3291449 = 2468587) B2468587
theorem B2194299 : Blo 2193435 2194299 := bstep (se 1 (by rfl) ⟨1645724, by rfl⟩ : syracuseStep 2194299 = 3291449) B3291449
theorem B6333877 : Blo 2193435 6333877 := bbase (se 5 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 6333877 = 593801) (by norm_num)
theorem B8445169 : Blo 2193435 8445169 := bstep (se 2 (by rfl) ⟨3166938, by rfl⟩ : syracuseStep 8445169 = 6333877) B6333877
theorem B11260225 : Blo 2193435 11260225 := bstep (se 2 (by rfl) ⟨4222584, by rfl⟩ : syracuseStep 11260225 = 8445169) B8445169
theorem B15013633 : Blo 2193435 15013633 := bstep (se 2 (by rfl) ⟨5630112, by rfl⟩ : syracuseStep 15013633 = 11260225) B11260225
theorem B20018177 : Blo 2193435 20018177 := bstep (se 2 (by rfl) ⟨7506816, by rfl⟩ : syracuseStep 20018177 = 15013633) B15013633
theorem B13345451 : Blo 2193435 13345451 := bstep (se 1 (by rfl) ⟨10009088, by rfl⟩ : syracuseStep 13345451 = 20018177) B20018177
theorem B8896967 : Blo 2193435 8896967 := bstep (se 1 (by rfl) ⟨6672725, by rfl⟩ : syracuseStep 8896967 = 13345451) B13345451
theorem B5931311 : Blo 2193435 5931311 := bstep (se 1 (by rfl) ⟨4448483, by rfl⟩ : syracuseStep 5931311 = 8896967) B8896967
theorem B15816829 : Blo 2193435 15816829 := bstep (se 3 (by rfl) ⟨2965655, by rfl⟩ : syracuseStep 15816829 = 5931311) B5931311
theorem B21089105 : Blo 2193435 21089105 := bstep (se 2 (by rfl) ⟨7908414, by rfl⟩ : syracuseStep 21089105 = 15816829) B15816829
theorem B14059403 : Blo 2193435 14059403 := bstep (se 1 (by rfl) ⟨10544552, by rfl⟩ : syracuseStep 14059403 = 21089105) B21089105
theorem B9372935 : Blo 2193435 9372935 := bstep (se 1 (by rfl) ⟨7029701, by rfl⟩ : syracuseStep 9372935 = 14059403) B14059403
theorem B24994493 : Blo 2193435 24994493 := bstep (se 3 (by rfl) ⟨4686467, by rfl⟩ : syracuseStep 24994493 = 9372935) B9372935
theorem B16662995 : Blo 2193435 16662995 := bstep (se 1 (by rfl) ⟨12497246, by rfl⟩ : syracuseStep 16662995 = 24994493) B24994493
theorem B11108663 : Blo 2193435 11108663 := bstep (se 1 (by rfl) ⟨8331497, by rfl⟩ : syracuseStep 11108663 = 16662995) B16662995
theorem B7405775 : Blo 2193435 7405775 := bstep (se 1 (by rfl) ⟨5554331, by rfl⟩ : syracuseStep 7405775 = 11108663) B11108663
theorem B4937183 : Blo 2193435 4937183 := bstep (se 1 (by rfl) ⟨3702887, by rfl⟩ : syracuseStep 4937183 = 7405775) B7405775
theorem B3291455 : Blo 2193435 3291455 := bstep (se 1 (by rfl) ⟨2468591, by rfl⟩ : syracuseStep 3291455 = 4937183) B4937183
theorem B2194303 : Blo 2193435 2194303 := bstep (se 1 (by rfl) ⟨1645727, by rfl⟩ : syracuseStep 2194303 = 3291455) B3291455
theorem B3291461 : Blo 2193435 3291461 := bbase (se 4 (by rfl) ⟨308574, by rfl⟩ : syracuseStep 3291461 = 617149) (by norm_num)
theorem B2194307 : Blo 2193435 2194307 := bstep (se 1 (by rfl) ⟨1645730, by rfl⟩ : syracuseStep 2194307 = 3291461) B3291461
theorem B3702901 : Blo 2193435 3702901 := bbase (se 5 (by rfl) ⟨173573, by rfl⟩ : syracuseStep 3702901 = 347147) (by norm_num)
theorem B4937201 : Blo 2193435 4937201 := bstep (se 2 (by rfl) ⟨1851450, by rfl⟩ : syracuseStep 4937201 = 3702901) B3702901
theorem B3291467 : Blo 2193435 3291467 := bstep (se 1 (by rfl) ⟨2468600, by rfl⟩ : syracuseStep 3291467 = 4937201) B4937201
theorem B2194311 : Blo 2193435 2194311 := bstep (se 1 (by rfl) ⟨1645733, by rfl⟩ : syracuseStep 2194311 = 3291467) B3291467
theorem B2468605 : Blo 2193435 2468605 := bbase (se 3 (by rfl) ⟨462863, by rfl⟩ : syracuseStep 2468605 = 925727) (by norm_num)
theorem B3291473 : Blo 2193435 3291473 := bstep (se 2 (by rfl) ⟨1234302, by rfl⟩ : syracuseStep 3291473 = 2468605) B2468605
theorem B2194315 : Blo 2193435 2194315 := bstep (se 1 (by rfl) ⟨1645736, by rfl⟩ : syracuseStep 2194315 = 3291473) B3291473
theorem B7405829 : Blo 2193435 7405829 := bbase (se 4 (by rfl) ⟨694296, by rfl⟩ : syracuseStep 7405829 = 1388593) (by norm_num)
theorem B4937219 : Blo 2193435 4937219 := bstep (se 1 (by rfl) ⟨3702914, by rfl⟩ : syracuseStep 4937219 = 7405829) B7405829
theorem B3291479 : Blo 2193435 3291479 := bstep (se 1 (by rfl) ⟨2468609, by rfl⟩ : syracuseStep 3291479 = 4937219) B4937219
theorem B2194319 : Blo 2193435 2194319 := bstep (se 1 (by rfl) ⟨1645739, by rfl⟩ : syracuseStep 2194319 = 3291479) B3291479
theorem B3291485 : Blo 2193435 3291485 := bbase (se 3 (by rfl) ⟨617153, by rfl⟩ : syracuseStep 3291485 = 1234307) (by norm_num)
theorem B2194323 : Blo 2193435 2194323 := bstep (se 1 (by rfl) ⟨1645742, by rfl⟩ : syracuseStep 2194323 = 3291485) B3291485
theorem B4937237 : Blo 2193435 4937237 := bbase (se 6 (by rfl) ⟨115716, by rfl⟩ : syracuseStep 4937237 = 231433) (by norm_num)
theorem B3291491 : Blo 2193435 3291491 := bstep (se 1 (by rfl) ⟨2468618, by rfl⟩ : syracuseStep 3291491 = 4937237) B4937237
theorem B2194327 : Blo 2193435 2194327 := bstep (se 1 (by rfl) ⟨1645745, by rfl⟩ : syracuseStep 2194327 = 3291491) B3291491
theorem B8331605 : Blo 2193435 8331605 := bbase (se 10 (by rfl) ⟨12204, by rfl⟩ : syracuseStep 8331605 = 24409) (by norm_num)
theorem B5554403 : Blo 2193435 5554403 := bstep (se 1 (by rfl) ⟨4165802, by rfl⟩ : syracuseStep 5554403 = 8331605) B8331605
theorem B3702935 : Blo 2193435 3702935 := bstep (se 1 (by rfl) ⟨2777201, by rfl⟩ : syracuseStep 3702935 = 5554403) B5554403
theorem B2468623 : Blo 2193435 2468623 := bstep (se 1 (by rfl) ⟨1851467, by rfl⟩ : syracuseStep 2468623 = 3702935) B3702935
theorem B3291497 : Blo 2193435 3291497 := bstep (se 2 (by rfl) ⟨1234311, by rfl⟩ : syracuseStep 3291497 = 2468623) B2468623
theorem B2194331 : Blo 2193435 2194331 := bstep (se 1 (by rfl) ⟨1645748, by rfl⟩ : syracuseStep 2194331 = 3291497) B3291497
theorem B12497429 : Blo 2193435 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B8331619 : Blo 2193435 8331619 := bstep (se 1 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 8331619 = 12497429) B12497429
theorem B11108825 : Blo 2193435 11108825 := bstep (se 2 (by rfl) ⟨4165809, by rfl⟩ : syracuseStep 11108825 = 8331619) B8331619
theorem B7405883 : Blo 2193435 7405883 := bstep (se 1 (by rfl) ⟨5554412, by rfl⟩ : syracuseStep 7405883 = 11108825) B11108825
theorem B4937255 : Blo 2193435 4937255 := bstep (se 1 (by rfl) ⟨3702941, by rfl⟩ : syracuseStep 4937255 = 7405883) B7405883
theorem B3291503 : Blo 2193435 3291503 := bstep (se 1 (by rfl) ⟨2468627, by rfl⟩ : syracuseStep 3291503 = 4937255) B4937255
theorem B2194335 : Blo 2193435 2194335 := bstep (se 1 (by rfl) ⟨1645751, by rfl⟩ : syracuseStep 2194335 = 3291503) B3291503
theorem B3291509 : Blo 2193435 3291509 := bbase (se 5 (by rfl) ⟨154289, by rfl⟩ : syracuseStep 3291509 = 308579) (by norm_num)
theorem B2194339 : Blo 2193435 2194339 := bstep (se 1 (by rfl) ⟨1645754, by rfl⟩ : syracuseStep 2194339 = 3291509) B3291509
theorem B2343277 : Blo 2193435 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B3124369 : Blo 2193435 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B4165825 : Blo 2193435 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B5554433 : Blo 2193435 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B3702955 : Blo 2193435 3702955 := bstep (se 1 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 3702955 = 5554433) B5554433
theorem B4937273 : Blo 2193435 4937273 := bstep (se 2 (by rfl) ⟨1851477, by rfl⟩ : syracuseStep 4937273 = 3702955) B3702955
theorem B3291515 : Blo 2193435 3291515 := bstep (se 1 (by rfl) ⟨2468636, by rfl⟩ : syracuseStep 3291515 = 4937273) B4937273
theorem B2194343 : Blo 2193435 2194343 := bstep (se 1 (by rfl) ⟨1645757, by rfl⟩ : syracuseStep 2194343 = 3291515) B3291515
theorem B2468641 : Blo 2193435 2468641 := bbase (se 2 (by rfl) ⟨925740, by rfl⟩ : syracuseStep 2468641 = 1851481) (by norm_num)
theorem B3291521 : Blo 2193435 3291521 := bstep (se 2 (by rfl) ⟨1234320, by rfl⟩ : syracuseStep 3291521 = 2468641) B2468641
theorem B2194347 : Blo 2193435 2194347 := bstep (se 1 (by rfl) ⟨1645760, by rfl⟩ : syracuseStep 2194347 = 3291521) B3291521
theorem B5554453 : Blo 2193435 5554453 := bbase (se 6 (by rfl) ⟨130182, by rfl⟩ : syracuseStep 5554453 = 260365) (by norm_num)
theorem B7405937 : Blo 2193435 7405937 := bstep (se 2 (by rfl) ⟨2777226, by rfl⟩ : syracuseStep 7405937 = 5554453) B5554453
theorem B4937291 : Blo 2193435 4937291 := bstep (se 1 (by rfl) ⟨3702968, by rfl⟩ : syracuseStep 4937291 = 7405937) B7405937
theorem B3291527 : Blo 2193435 3291527 := bstep (se 1 (by rfl) ⟨2468645, by rfl⟩ : syracuseStep 3291527 = 4937291) B4937291
theorem B2194351 : Blo 2193435 2194351 := bstep (se 1 (by rfl) ⟨1645763, by rfl⟩ : syracuseStep 2194351 = 3291527) B3291527
theorem B3291533 : Blo 2193435 3291533 := bbase (se 3 (by rfl) ⟨617162, by rfl⟩ : syracuseStep 3291533 = 1234325) (by norm_num)
theorem B2194355 : Blo 2193435 2194355 := bstep (se 1 (by rfl) ⟨1645766, by rfl⟩ : syracuseStep 2194355 = 3291533) B3291533
theorem B4937309 : Blo 2193435 4937309 := bbase (se 3 (by rfl) ⟨925745, by rfl⟩ : syracuseStep 4937309 = 1851491) (by norm_num)
theorem B3291539 : Blo 2193435 3291539 := bstep (se 1 (by rfl) ⟨2468654, by rfl⟩ : syracuseStep 3291539 = 4937309) B4937309
theorem B2194359 : Blo 2193435 2194359 := bstep (se 1 (by rfl) ⟨1645769, by rfl⟩ : syracuseStep 2194359 = 3291539) B3291539
theorem B3702989 : Blo 2193435 3702989 := bbase (se 3 (by rfl) ⟨694310, by rfl⟩ : syracuseStep 3702989 = 1388621) (by norm_num)
theorem B2468659 : Blo 2193435 2468659 := bstep (se 1 (by rfl) ⟨1851494, by rfl⟩ : syracuseStep 2468659 = 3702989) B3702989
theorem B3291545 : Blo 2193435 3291545 := bstep (se 2 (by rfl) ⟨1234329, by rfl⟩ : syracuseStep 3291545 = 2468659) B2468659
theorem B2194363 : Blo 2193435 2194363 := bstep (se 1 (by rfl) ⟨1645772, by rfl⟩ : syracuseStep 2194363 = 3291545) B3291545
theorem B3336461 : Blo 2193435 3336461 := bbase (se 3 (by rfl) ⟨625586, by rfl⟩ : syracuseStep 3336461 = 1251173) (by norm_num)
theorem B2224307 : Blo 2193435 2224307 := bstep (se 1 (by rfl) ⟨1668230, by rfl⟩ : syracuseStep 2224307 = 3336461) B3336461
theorem B5931485 : Blo 2193435 5931485 := bstep (se 3 (by rfl) ⟨1112153, by rfl⟩ : syracuseStep 5931485 = 2224307) B2224307
theorem B3954323 : Blo 2193435 3954323 := bstep (se 1 (by rfl) ⟨2965742, by rfl⟩ : syracuseStep 3954323 = 5931485) B5931485
theorem B2636215 : Blo 2193435 2636215 := bstep (se 1 (by rfl) ⟨1977161, by rfl⟩ : syracuseStep 2636215 = 3954323) B3954323
theorem B14059813 : Blo 2193435 14059813 := bstep (se 4 (by rfl) ⟨1318107, by rfl⟩ : syracuseStep 14059813 = 2636215) B2636215
theorem B18746417 : Blo 2193435 18746417 := bstep (se 2 (by rfl) ⟨7029906, by rfl⟩ : syracuseStep 18746417 = 14059813) B14059813
theorem B12497611 : Blo 2193435 12497611 := bstep (se 1 (by rfl) ⟨9373208, by rfl⟩ : syracuseStep 12497611 = 18746417) B18746417
theorem B16663481 : Blo 2193435 16663481 := bstep (se 2 (by rfl) ⟨6248805, by rfl⟩ : syracuseStep 16663481 = 12497611) B12497611
theorem B11108987 : Blo 2193435 11108987 := bstep (se 1 (by rfl) ⟨8331740, by rfl⟩ : syracuseStep 11108987 = 16663481) B16663481
theorem B7405991 : Blo 2193435 7405991 := bstep (se 1 (by rfl) ⟨5554493, by rfl⟩ : syracuseStep 7405991 = 11108987) B11108987
theorem B4937327 : Blo 2193435 4937327 := bstep (se 1 (by rfl) ⟨3702995, by rfl⟩ : syracuseStep 4937327 = 7405991) B7405991
theorem B3291551 : Blo 2193435 3291551 := bstep (se 1 (by rfl) ⟨2468663, by rfl⟩ : syracuseStep 3291551 = 4937327) B4937327
theorem B2194367 : Blo 2193435 2194367 := bstep (se 1 (by rfl) ⟨1645775, by rfl⟩ : syracuseStep 2194367 = 3291551) B3291551
theorem B3291557 : Blo 2193435 3291557 := bbase (se 4 (by rfl) ⟨308583, by rfl⟩ : syracuseStep 3291557 = 617167) (by norm_num)
theorem B2194371 : Blo 2193435 2194371 := bstep (se 1 (by rfl) ⟨1645778, by rfl⟩ : syracuseStep 2194371 = 3291557) B3291557
theorem B2777257 : Blo 2193435 2777257 := bbase (se 2 (by rfl) ⟨1041471, by rfl⟩ : syracuseStep 2777257 = 2082943) (by norm_num)
theorem B3703009 : Blo 2193435 3703009 := bstep (se 2 (by rfl) ⟨1388628, by rfl⟩ : syracuseStep 3703009 = 2777257) B2777257
theorem B4937345 : Blo 2193435 4937345 := bstep (se 2 (by rfl) ⟨1851504, by rfl⟩ : syracuseStep 4937345 = 3703009) B3703009
theorem B3291563 : Blo 2193435 3291563 := bstep (se 1 (by rfl) ⟨2468672, by rfl⟩ : syracuseStep 3291563 = 4937345) B4937345
theorem B2194375 : Blo 2193435 2194375 := bstep (se 1 (by rfl) ⟨1645781, by rfl⟩ : syracuseStep 2194375 = 3291563) B3291563
theorem B2468677 : Blo 2193435 2468677 := bbase (se 4 (by rfl) ⟨231438, by rfl⟩ : syracuseStep 2468677 = 462877) (by norm_num)
theorem B3291569 : Blo 2193435 3291569 := bstep (se 2 (by rfl) ⟨1234338, by rfl⟩ : syracuseStep 3291569 = 2468677) B2468677
theorem B2194379 : Blo 2193435 2194379 := bstep (se 1 (by rfl) ⟨1645784, by rfl⟩ : syracuseStep 2194379 = 3291569) B3291569
theorem B4165901 : Blo 2193435 4165901 := bbase (se 3 (by rfl) ⟨781106, by rfl⟩ : syracuseStep 4165901 = 1562213) (by norm_num)
theorem B2777267 : Blo 2193435 2777267 := bstep (se 1 (by rfl) ⟨2082950, by rfl⟩ : syracuseStep 2777267 = 4165901) B4165901
theorem B7406045 : Blo 2193435 7406045 := bstep (se 3 (by rfl) ⟨1388633, by rfl⟩ : syracuseStep 7406045 = 2777267) B2777267
theorem B4937363 : Blo 2193435 4937363 := bstep (se 1 (by rfl) ⟨3703022, by rfl⟩ : syracuseStep 4937363 = 7406045) B7406045
theorem B3291575 : Blo 2193435 3291575 := bstep (se 1 (by rfl) ⟨2468681, by rfl⟩ : syracuseStep 3291575 = 4937363) B4937363
theorem B2194383 : Blo 2193435 2194383 := bstep (se 1 (by rfl) ⟨1645787, by rfl⟩ : syracuseStep 2194383 = 3291575) B3291575
theorem B3291581 : Blo 2193435 3291581 := bbase (se 3 (by rfl) ⟨617171, by rfl⟩ : syracuseStep 3291581 = 1234343) (by norm_num)
theorem B2194387 : Blo 2193435 2194387 := bstep (se 1 (by rfl) ⟨1645790, by rfl⟩ : syracuseStep 2194387 = 3291581) B3291581
theorem B4937381 : Blo 2193435 4937381 := bbase (se 4 (by rfl) ⟨462879, by rfl⟩ : syracuseStep 4937381 = 925759) (by norm_num)
theorem B3291587 : Blo 2193435 3291587 := bstep (se 1 (by rfl) ⟨2468690, by rfl⟩ : syracuseStep 3291587 = 4937381) B4937381
theorem B2194391 : Blo 2193435 2194391 := bstep (se 1 (by rfl) ⟨1645793, by rfl⟩ : syracuseStep 2194391 = 3291587) B3291587
theorem B5554565 : Blo 2193435 5554565 := bbase (se 4 (by rfl) ⟨520740, by rfl⟩ : syracuseStep 5554565 = 1041481) (by norm_num)
theorem B3703043 : Blo 2193435 3703043 := bstep (se 1 (by rfl) ⟨2777282, by rfl⟩ : syracuseStep 3703043 = 5554565) B5554565
theorem B2468695 : Blo 2193435 2468695 := bstep (se 1 (by rfl) ⟨1851521, by rfl⟩ : syracuseStep 2468695 = 3703043) B3703043
theorem B3291593 : Blo 2193435 3291593 := bstep (se 2 (by rfl) ⟨1234347, by rfl⟩ : syracuseStep 3291593 = 2468695) B2468695
theorem B2194395 : Blo 2193435 2194395 := bstep (se 1 (by rfl) ⟨1645796, by rfl⟩ : syracuseStep 2194395 = 3291593) B3291593
theorem B3515005 : Blo 2193435 3515005 := bbase (se 3 (by rfl) ⟨659063, by rfl⟩ : syracuseStep 3515005 = 1318127) (by norm_num)
theorem B4686673 : Blo 2193435 4686673 := bstep (se 2 (by rfl) ⟨1757502, by rfl⟩ : syracuseStep 4686673 = 3515005) B3515005
theorem B6248897 : Blo 2193435 6248897 := bstep (se 2 (by rfl) ⟨2343336, by rfl⟩ : syracuseStep 6248897 = 4686673) B4686673
theorem B4165931 : Blo 2193435 4165931 := bstep (se 1 (by rfl) ⟨3124448, by rfl⟩ : syracuseStep 4165931 = 6248897) B6248897
theorem B11109149 : Blo 2193435 11109149 := bstep (se 3 (by rfl) ⟨2082965, by rfl⟩ : syracuseStep 11109149 = 4165931) B4165931
theorem B7406099 : Blo 2193435 7406099 := bstep (se 1 (by rfl) ⟨5554574, by rfl⟩ : syracuseStep 7406099 = 11109149) B11109149
theorem B4937399 : Blo 2193435 4937399 := bstep (se 1 (by rfl) ⟨3703049, by rfl⟩ : syracuseStep 4937399 = 7406099) B7406099
theorem B3291599 : Blo 2193435 3291599 := bstep (se 1 (by rfl) ⟨2468699, by rfl⟩ : syracuseStep 3291599 = 4937399) B4937399
theorem B2194399 : Blo 2193435 2194399 := bstep (se 1 (by rfl) ⟨1645799, by rfl⟩ : syracuseStep 2194399 = 3291599) B3291599
theorem B3291605 : Blo 2193435 3291605 := bbase (se 7 (by rfl) ⟨38573, by rfl⟩ : syracuseStep 3291605 = 77147) (by norm_num)
theorem B2194403 : Blo 2193435 2194403 := bstep (se 1 (by rfl) ⟨1645802, by rfl⟩ : syracuseStep 2194403 = 3291605) B3291605
theorem B8331893 : Blo 2193435 8331893 := bbase (se 5 (by rfl) ⟨390557, by rfl⟩ : syracuseStep 8331893 = 781115) (by norm_num)
theorem B5554595 : Blo 2193435 5554595 := bstep (se 1 (by rfl) ⟨4165946, by rfl⟩ : syracuseStep 5554595 = 8331893) B8331893
theorem B3703063 : Blo 2193435 3703063 := bstep (se 1 (by rfl) ⟨2777297, by rfl⟩ : syracuseStep 3703063 = 5554595) B5554595
theorem B4937417 : Blo 2193435 4937417 := bstep (se 2 (by rfl) ⟨1851531, by rfl⟩ : syracuseStep 4937417 = 3703063) B3703063
theorem B3291611 : Blo 2193435 3291611 := bstep (se 1 (by rfl) ⟨2468708, by rfl⟩ : syracuseStep 3291611 = 4937417) B4937417
theorem B2194407 : Blo 2193435 2194407 := bstep (se 1 (by rfl) ⟨1645805, by rfl⟩ : syracuseStep 2194407 = 3291611) B3291611
theorem B2468713 : Blo 2193435 2468713 := bbase (se 2 (by rfl) ⟨925767, by rfl⟩ : syracuseStep 2468713 = 1851535) (by norm_num)
theorem B3291617 : Blo 2193435 3291617 := bstep (se 2 (by rfl) ⟨1234356, by rfl⟩ : syracuseStep 3291617 = 2468713) B2468713
theorem B2194411 : Blo 2193435 2194411 := bstep (se 1 (by rfl) ⟨1645808, by rfl⟩ : syracuseStep 2194411 = 3291617) B3291617
theorem B2636273 : Blo 2193435 2636273 := bbase (se 2 (by rfl) ⟨988602, by rfl⟩ : syracuseStep 2636273 = 1977205) (by norm_num)
theorem B7030061 : Blo 2193435 7030061 := bstep (se 3 (by rfl) ⟨1318136, by rfl⟩ : syracuseStep 7030061 = 2636273) B2636273
theorem B4686707 : Blo 2193435 4686707 := bstep (se 1 (by rfl) ⟨3515030, by rfl⟩ : syracuseStep 4686707 = 7030061) B7030061
theorem B12497885 : Blo 2193435 12497885 := bstep (se 3 (by rfl) ⟨2343353, by rfl⟩ : syracuseStep 12497885 = 4686707) B4686707
theorem B8331923 : Blo 2193435 8331923 := bstep (se 1 (by rfl) ⟨6248942, by rfl⟩ : syracuseStep 8331923 = 12497885) B12497885
theorem B5554615 : Blo 2193435 5554615 := bstep (se 1 (by rfl) ⟨4165961, by rfl⟩ : syracuseStep 5554615 = 8331923) B8331923
theorem B7406153 : Blo 2193435 7406153 := bstep (se 2 (by rfl) ⟨2777307, by rfl⟩ : syracuseStep 7406153 = 5554615) B5554615
theorem B4937435 : Blo 2193435 4937435 := bstep (se 1 (by rfl) ⟨3703076, by rfl⟩ : syracuseStep 4937435 = 7406153) B7406153
theorem B3291623 : Blo 2193435 3291623 := bstep (se 1 (by rfl) ⟨2468717, by rfl⟩ : syracuseStep 3291623 = 4937435) B4937435
theorem B2194415 : Blo 2193435 2194415 := bstep (se 1 (by rfl) ⟨1645811, by rfl⟩ : syracuseStep 2194415 = 3291623) B3291623
theorem B3291629 : Blo 2193435 3291629 := bbase (se 3 (by rfl) ⟨617180, by rfl⟩ : syracuseStep 3291629 = 1234361) (by norm_num)
theorem B2194419 : Blo 2193435 2194419 := bstep (se 1 (by rfl) ⟨1645814, by rfl⟩ : syracuseStep 2194419 = 3291629) B3291629
theorem B4937453 : Blo 2193435 4937453 := bbase (se 3 (by rfl) ⟨925772, by rfl⟩ : syracuseStep 4937453 = 1851545) (by norm_num)
theorem B3291635 : Blo 2193435 3291635 := bstep (se 1 (by rfl) ⟨2468726, by rfl⟩ : syracuseStep 3291635 = 4937453) B4937453
theorem B2194423 : Blo 2193435 2194423 := bstep (se 1 (by rfl) ⟨1645817, by rfl⟩ : syracuseStep 2194423 = 3291635) B3291635
theorem B2224369 : Blo 2193435 2224369 := bbase (se 2 (by rfl) ⟨834138, by rfl⟩ : syracuseStep 2224369 = 1668277) (by norm_num)
theorem B2965825 : Blo 2193435 2965825 := bstep (se 2 (by rfl) ⟨1112184, by rfl⟩ : syracuseStep 2965825 = 2224369) B2224369
theorem B3954433 : Blo 2193435 3954433 := bstep (se 2 (by rfl) ⟨1482912, by rfl⟩ : syracuseStep 3954433 = 2965825) B2965825
theorem B5272577 : Blo 2193435 5272577 := bstep (se 2 (by rfl) ⟨1977216, by rfl⟩ : syracuseStep 5272577 = 3954433) B3954433
theorem B3515051 : Blo 2193435 3515051 := bstep (se 1 (by rfl) ⟨2636288, by rfl⟩ : syracuseStep 3515051 = 5272577) B5272577
theorem B2343367 : Blo 2193435 2343367 := bstep (se 1 (by rfl) ⟨1757525, by rfl⟩ : syracuseStep 2343367 = 3515051) B3515051
theorem B3124489 : Blo 2193435 3124489 := bstep (se 2 (by rfl) ⟨1171683, by rfl⟩ : syracuseStep 3124489 = 2343367) B2343367
theorem B4165985 : Blo 2193435 4165985 := bstep (se 2 (by rfl) ⟨1562244, by rfl⟩ : syracuseStep 4165985 = 3124489) B3124489
theorem B2777323 : Blo 2193435 2777323 := bstep (se 1 (by rfl) ⟨2082992, by rfl⟩ : syracuseStep 2777323 = 4165985) B4165985
theorem B3703097 : Blo 2193435 3703097 := bstep (se 2 (by rfl) ⟨1388661, by rfl⟩ : syracuseStep 3703097 = 2777323) B2777323
theorem B2468731 : Blo 2193435 2468731 := bstep (se 1 (by rfl) ⟨1851548, by rfl⟩ : syracuseStep 2468731 = 3703097) B3703097
theorem B3291641 : Blo 2193435 3291641 := bstep (se 2 (by rfl) ⟨1234365, by rfl⟩ : syracuseStep 3291641 = 2468731) B2468731
theorem B2194427 : Blo 2193435 2194427 := bstep (se 1 (by rfl) ⟨1645820, by rfl⟩ : syracuseStep 2194427 = 3291641) B3291641
theorem B4016773 : Blo 2193435 4016773 := bbase (se 4 (by rfl) ⟨376572, by rfl⟩ : syracuseStep 4016773 = 753145) (by norm_num)
theorem B21422789 : Blo 2193435 21422789 := bstep (se 4 (by rfl) ⟨2008386, by rfl⟩ : syracuseStep 21422789 = 4016773) B4016773
theorem B14281859 : Blo 2193435 14281859 := bstep (se 1 (by rfl) ⟨10711394, by rfl⟩ : syracuseStep 14281859 = 21422789) B21422789
theorem B9521239 : Blo 2193435 9521239 := bstep (se 1 (by rfl) ⟨7140929, by rfl⟩ : syracuseStep 9521239 = 14281859) B14281859
theorem B12694985 : Blo 2193435 12694985 := bstep (se 2 (by rfl) ⟨4760619, by rfl⟩ : syracuseStep 12694985 = 9521239) B9521239
theorem B8463323 : Blo 2193435 8463323 := bstep (se 1 (by rfl) ⟨6347492, by rfl⟩ : syracuseStep 8463323 = 12694985) B12694985
theorem B22568861 : Blo 2193435 22568861 := bstep (se 3 (by rfl) ⟨4231661, by rfl⟩ : syracuseStep 22568861 = 8463323) B8463323
theorem B15045907 : Blo 2193435 15045907 := bstep (se 1 (by rfl) ⟨11284430, by rfl⟩ : syracuseStep 15045907 = 22568861) B22568861
theorem B20061209 : Blo 2193435 20061209 := bstep (se 2 (by rfl) ⟨7522953, by rfl⟩ : syracuseStep 20061209 = 15045907) B15045907
theorem B53496557 : Blo 2193435 53496557 := bstep (se 3 (by rfl) ⟨10030604, by rfl⟩ : syracuseStep 53496557 = 20061209) B20061209
theorem B35664371 : Blo 2193435 35664371 := bstep (se 1 (by rfl) ⟨26748278, by rfl⟩ : syracuseStep 35664371 = 53496557) B53496557
theorem B23776247 : Blo 2193435 23776247 := bstep (se 1 (by rfl) ⟨17832185, by rfl⟩ : syracuseStep 23776247 = 35664371) B35664371
theorem B15850831 : Blo 2193435 15850831 := bstep (se 1 (by rfl) ⟨11888123, by rfl⟩ : syracuseStep 15850831 = 23776247) B23776247
theorem B21134441 : Blo 2193435 21134441 := bstep (se 2 (by rfl) ⟨7925415, by rfl⟩ : syracuseStep 21134441 = 15850831) B15850831
theorem B14089627 : Blo 2193435 14089627 := bstep (se 1 (by rfl) ⟨10567220, by rfl⟩ : syracuseStep 14089627 = 21134441) B21134441
theorem B18786169 : Blo 2193435 18786169 := bstep (se 2 (by rfl) ⟨7044813, by rfl⟩ : syracuseStep 18786169 = 14089627) B14089627
theorem B25048225 : Blo 2193435 25048225 := bstep (se 2 (by rfl) ⟨9393084, by rfl⟩ : syracuseStep 25048225 = 18786169) B18786169
theorem B33397633 : Blo 2193435 33397633 := bstep (se 2 (by rfl) ⟨12524112, by rfl⟩ : syracuseStep 33397633 = 25048225) B25048225
theorem B44530177 : Blo 2193435 44530177 := bstep (se 2 (by rfl) ⟨16698816, by rfl⟩ : syracuseStep 44530177 = 33397633) B33397633
theorem B59373569 : Blo 2193435 59373569 := bstep (se 2 (by rfl) ⟨22265088, by rfl⟩ : syracuseStep 59373569 = 44530177) B44530177
theorem B39582379 : Blo 2193435 39582379 := bstep (se 1 (by rfl) ⟨29686784, by rfl⟩ : syracuseStep 39582379 = 59373569) B59373569
theorem B52776505 : Blo 2193435 52776505 := bstep (se 2 (by rfl) ⟨19791189, by rfl⟩ : syracuseStep 52776505 = 39582379) B39582379
theorem B70368673 : Blo 2193435 70368673 := bstep (se 2 (by rfl) ⟨26388252, by rfl⟩ : syracuseStep 70368673 = 52776505) B52776505
theorem B93824897 : Blo 2193435 93824897 := bstep (se 2 (by rfl) ⟨35184336, by rfl⟩ : syracuseStep 93824897 = 70368673) B70368673
theorem B1000798901 : Blo 2193435 1000798901 := bstep (se 5 (by rfl) ⟨46912448, by rfl⟩ : syracuseStep 1000798901 = 93824897) B93824897
theorem B667199267 : Blo 2193435 667199267 := bstep (se 1 (by rfl) ⟨500399450, by rfl⟩ : syracuseStep 667199267 = 1000798901) B1000798901
theorem B444799511 : Blo 2193435 444799511 := bstep (se 1 (by rfl) ⟨333599633, by rfl⟩ : syracuseStep 444799511 = 667199267) B667199267
theorem B296533007 : Blo 2193435 296533007 := bstep (se 1 (by rfl) ⟨222399755, by rfl⟩ : syracuseStep 296533007 = 444799511) B444799511
theorem B197688671 : Blo 2193435 197688671 := bstep (se 1 (by rfl) ⟨148266503, by rfl⟩ : syracuseStep 197688671 = 296533007) B296533007
theorem B131792447 : Blo 2193435 131792447 := bstep (se 1 (by rfl) ⟨98844335, by rfl⟩ : syracuseStep 131792447 = 197688671) B197688671
theorem B87861631 : Blo 2193435 87861631 := bstep (se 1 (by rfl) ⟨65896223, by rfl⟩ : syracuseStep 87861631 = 131792447) B131792447
theorem B117148841 : Blo 2193435 117148841 := bstep (se 2 (by rfl) ⟨43930815, by rfl⟩ : syracuseStep 117148841 = 87861631) B87861631
theorem B78099227 : Blo 2193435 78099227 := bstep (se 1 (by rfl) ⟨58574420, by rfl⟩ : syracuseStep 78099227 = 117148841) B117148841
theorem B52066151 : Blo 2193435 52066151 := bstep (se 1 (by rfl) ⟨39049613, by rfl⟩ : syracuseStep 52066151 = 78099227) B78099227
theorem B34710767 : Blo 2193435 34710767 := bstep (se 1 (by rfl) ⟨26033075, by rfl⟩ : syracuseStep 34710767 = 52066151) B52066151
theorem B23140511 : Blo 2193435 23140511 := bstep (se 1 (by rfl) ⟨17355383, by rfl⟩ : syracuseStep 23140511 = 34710767) B34710767
theorem B15427007 : Blo 2193435 15427007 := bstep (se 1 (by rfl) ⟨11570255, by rfl⟩ : syracuseStep 15427007 = 23140511) B23140511
theorem B10284671 : Blo 2193435 10284671 := bstep (se 1 (by rfl) ⟨7713503, by rfl⟩ : syracuseStep 10284671 = 15427007) B15427007
theorem B6856447 : Blo 2193435 6856447 := bstep (se 1 (by rfl) ⟨5142335, by rfl⟩ : syracuseStep 6856447 = 10284671) B10284671
theorem B9141929 : Blo 2193435 9141929 := bstep (se 2 (by rfl) ⟨3428223, by rfl⟩ : syracuseStep 9141929 = 6856447) B6856447
theorem B6094619 : Blo 2193435 6094619 := bstep (se 1 (by rfl) ⟨4570964, by rfl⟩ : syracuseStep 6094619 = 9141929) B9141929
theorem B4063079 : Blo 2193435 4063079 := bstep (se 1 (by rfl) ⟨3047309, by rfl⟩ : syracuseStep 4063079 = 6094619) B6094619
theorem B10834877 : Blo 2193435 10834877 := bstep (se 3 (by rfl) ⟨2031539, by rfl⟩ : syracuseStep 10834877 = 4063079) B4063079
theorem B7223251 : Blo 2193435 7223251 := bstep (se 1 (by rfl) ⟨5417438, by rfl⟩ : syracuseStep 7223251 = 10834877) B10834877
theorem B9631001 : Blo 2193435 9631001 := bstep (se 2 (by rfl) ⟨3611625, by rfl⟩ : syracuseStep 9631001 = 7223251) B7223251
theorem B25682669 : Blo 2193435 25682669 := bstep (se 3 (by rfl) ⟨4815500, by rfl⟩ : syracuseStep 25682669 = 9631001) B9631001
theorem B17121779 : Blo 2193435 17121779 := bstep (se 1 (by rfl) ⟨12841334, by rfl⟩ : syracuseStep 17121779 = 25682669) B25682669
theorem B11414519 : Blo 2193435 11414519 := bstep (se 1 (by rfl) ⟨8560889, by rfl⟩ : syracuseStep 11414519 = 17121779) B17121779
theorem B7609679 : Blo 2193435 7609679 := bstep (se 1 (by rfl) ⟨5707259, by rfl⟩ : syracuseStep 7609679 = 11414519) B11414519
theorem B5073119 : Blo 2193435 5073119 := bstep (se 1 (by rfl) ⟨3804839, by rfl⟩ : syracuseStep 5073119 = 7609679) B7609679
theorem B3382079 : Blo 2193435 3382079 := bstep (se 1 (by rfl) ⟨2536559, by rfl⟩ : syracuseStep 3382079 = 5073119) B5073119
theorem B9018877 : Blo 2193435 9018877 := bstep (se 3 (by rfl) ⟨1691039, by rfl⟩ : syracuseStep 9018877 = 3382079) B3382079
theorem B12025169 : Blo 2193435 12025169 := bstep (se 2 (by rfl) ⟨4509438, by rfl⟩ : syracuseStep 12025169 = 9018877) B9018877
theorem B8016779 : Blo 2193435 8016779 := bstep (se 1 (by rfl) ⟨6012584, by rfl⟩ : syracuseStep 8016779 = 12025169) B12025169
theorem B5344519 : Blo 2193435 5344519 := bstep (se 1 (by rfl) ⟨4008389, by rfl⟩ : syracuseStep 5344519 = 8016779) B8016779
theorem B114016405 : Blo 2193435 114016405 := bstep (se 6 (by rfl) ⟨2672259, by rfl⟩ : syracuseStep 114016405 = 5344519) B5344519
theorem B152021873 : Blo 2193435 152021873 := bstep (se 2 (by rfl) ⟨57008202, by rfl⟩ : syracuseStep 152021873 = 114016405) B114016405
theorem B405391661 : Blo 2193435 405391661 := bstep (se 3 (by rfl) ⟨76010936, by rfl⟩ : syracuseStep 405391661 = 152021873) B152021873
theorem B270261107 : Blo 2193435 270261107 := bstep (se 1 (by rfl) ⟨202695830, by rfl⟩ : syracuseStep 270261107 = 405391661) B405391661
theorem B180174071 : Blo 2193435 180174071 := bstep (se 1 (by rfl) ⟨135130553, by rfl⟩ : syracuseStep 180174071 = 270261107) B270261107
theorem B120116047 : Blo 2193435 120116047 := bstep (se 1 (by rfl) ⟨90087035, by rfl⟩ : syracuseStep 120116047 = 180174071) B180174071
theorem B160154729 : Blo 2193435 160154729 := bstep (se 2 (by rfl) ⟨60058023, by rfl⟩ : syracuseStep 160154729 = 120116047) B120116047
theorem B106769819 : Blo 2193435 106769819 := bstep (se 1 (by rfl) ⟨80077364, by rfl⟩ : syracuseStep 106769819 = 160154729) B160154729
theorem B71179879 : Blo 2193435 71179879 := bstep (se 1 (by rfl) ⟨53384909, by rfl⟩ : syracuseStep 71179879 = 106769819) B106769819
theorem B94906505 : Blo 2193435 94906505 := bstep (se 2 (by rfl) ⟨35589939, by rfl⟩ : syracuseStep 94906505 = 71179879) B71179879
theorem B63271003 : Blo 2193435 63271003 := bstep (se 1 (by rfl) ⟨47453252, by rfl⟩ : syracuseStep 63271003 = 94906505) B94906505
theorem B84361337 : Blo 2193435 84361337 := bstep (se 2 (by rfl) ⟨31635501, by rfl⟩ : syracuseStep 84361337 = 63271003) B63271003
theorem B56240891 : Blo 2193435 56240891 := bstep (se 1 (by rfl) ⟨42180668, by rfl⟩ : syracuseStep 56240891 = 84361337) B84361337
theorem B37493927 : Blo 2193435 37493927 := bstep (se 1 (by rfl) ⟨28120445, by rfl⟩ : syracuseStep 37493927 = 56240891) B56240891
theorem B24995951 : Blo 2193435 24995951 := bstep (se 1 (by rfl) ⟨18746963, by rfl⟩ : syracuseStep 24995951 = 37493927) B37493927
theorem B16663967 : Blo 2193435 16663967 := bstep (se 1 (by rfl) ⟨12497975, by rfl⟩ : syracuseStep 16663967 = 24995951) B24995951
theorem B11109311 : Blo 2193435 11109311 := bstep (se 1 (by rfl) ⟨8331983, by rfl⟩ : syracuseStep 11109311 = 16663967) B16663967
theorem B7406207 : Blo 2193435 7406207 := bstep (se 1 (by rfl) ⟨5554655, by rfl⟩ : syracuseStep 7406207 = 11109311) B11109311
theorem B4937471 : Blo 2193435 4937471 := bstep (se 1 (by rfl) ⟨3703103, by rfl⟩ : syracuseStep 4937471 = 7406207) B7406207
theorem B3291647 : Blo 2193435 3291647 := bstep (se 1 (by rfl) ⟨2468735, by rfl⟩ : syracuseStep 3291647 = 4937471) B4937471
theorem B2194431 : Blo 2193435 2194431 := bstep (se 1 (by rfl) ⟨1645823, by rfl⟩ : syracuseStep 2194431 = 3291647) B3291647
theorem B3291653 : Blo 2193435 3291653 := bbase (se 4 (by rfl) ⟨308592, by rfl⟩ : syracuseStep 3291653 = 617185) (by norm_num)
theorem B2194435 : Blo 2193435 2194435 := bstep (se 1 (by rfl) ⟨1645826, by rfl⟩ : syracuseStep 2194435 = 3291653) B3291653
theorem B3703117 : Blo 2193435 3703117 := bbase (se 3 (by rfl) ⟨694334, by rfl⟩ : syracuseStep 3703117 = 1388669) (by norm_num)
theorem B4937489 : Blo 2193435 4937489 := bstep (se 2 (by rfl) ⟨1851558, by rfl⟩ : syracuseStep 4937489 = 3703117) B3703117
theorem B3291659 : Blo 2193435 3291659 := bstep (se 1 (by rfl) ⟨2468744, by rfl⟩ : syracuseStep 3291659 = 4937489) B4937489
theorem B2194439 : Blo 2193435 2194439 := bstep (se 1 (by rfl) ⟨1645829, by rfl⟩ : syracuseStep 2194439 = 3291659) B3291659
theorem B2468749 : Blo 2193435 2468749 := bbase (se 3 (by rfl) ⟨462890, by rfl⟩ : syracuseStep 2468749 = 925781) (by norm_num)
theorem B3291665 : Blo 2193435 3291665 := bstep (se 2 (by rfl) ⟨1234374, by rfl⟩ : syracuseStep 3291665 = 2468749) B2468749
theorem B2194443 : Blo 2193435 2194443 := bstep (se 1 (by rfl) ⟨1645832, by rfl⟩ : syracuseStep 2194443 = 3291665) B3291665
theorem B7406261 : Blo 2193435 7406261 := bbase (se 5 (by rfl) ⟨347168, by rfl⟩ : syracuseStep 7406261 = 694337) (by norm_num)
theorem B4937507 : Blo 2193435 4937507 := bstep (se 1 (by rfl) ⟨3703130, by rfl⟩ : syracuseStep 4937507 = 7406261) B7406261
theorem B3291671 : Blo 2193435 3291671 := bstep (se 1 (by rfl) ⟨2468753, by rfl⟩ : syracuseStep 3291671 = 4937507) B4937507
theorem B2194447 : Blo 2193435 2194447 := bstep (se 1 (by rfl) ⟨1645835, by rfl⟩ : syracuseStep 2194447 = 3291671) B3291671
theorem B3291677 : Blo 2193435 3291677 := bbase (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) (by norm_num)
theorem B2194451 : Blo 2193435 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B4937525 : Blo 2193435 4937525 := bbase (se 5 (by rfl) ⟨231446, by rfl⟩ : syracuseStep 4937525 = 462893) (by norm_num)
theorem B3291683 : Blo 2193435 3291683 := bstep (se 1 (by rfl) ⟨2468762, by rfl⟩ : syracuseStep 3291683 = 4937525) B4937525
theorem B2194455 : Blo 2193435 2194455 := bstep (se 1 (by rfl) ⟨1645841, by rfl⟩ : syracuseStep 2194455 = 3291683) B3291683
theorem B14060405 : Blo 2193435 14060405 := bbase (se 5 (by rfl) ⟨659081, by rfl⟩ : syracuseStep 14060405 = 1318163) (by norm_num)
theorem B9373603 : Blo 2193435 9373603 := bstep (se 1 (by rfl) ⟨7030202, by rfl⟩ : syracuseStep 9373603 = 14060405) B14060405
theorem B12498137 : Blo 2193435 12498137 := bstep (se 2 (by rfl) ⟨4686801, by rfl⟩ : syracuseStep 12498137 = 9373603) B9373603
theorem B8332091 : Blo 2193435 8332091 := bstep (se 1 (by rfl) ⟨6249068, by rfl⟩ : syracuseStep 8332091 = 12498137) B12498137
theorem B5554727 : Blo 2193435 5554727 := bstep (se 1 (by rfl) ⟨4166045, by rfl⟩ : syracuseStep 5554727 = 8332091) B8332091
theorem B3703151 : Blo 2193435 3703151 := bstep (se 1 (by rfl) ⟨2777363, by rfl⟩ : syracuseStep 3703151 = 5554727) B5554727
theorem B2468767 : Blo 2193435 2468767 := bstep (se 1 (by rfl) ⟨1851575, by rfl⟩ : syracuseStep 2468767 = 3703151) B3703151
theorem B3291689 : Blo 2193435 3291689 := bstep (se 2 (by rfl) ⟨1234383, by rfl⟩ : syracuseStep 3291689 = 2468767) B2468767
theorem B2194459 : Blo 2193435 2194459 := bstep (se 1 (by rfl) ⟨1645844, by rfl⟩ : syracuseStep 2194459 = 3291689) B3291689
theorem B5272661 : Blo 2193435 5272661 := bbase (se 8 (by rfl) ⟨30894, by rfl⟩ : syracuseStep 5272661 = 61789) (by norm_num)
theorem B14060429 : Blo 2193435 14060429 := bstep (se 3 (by rfl) ⟨2636330, by rfl⟩ : syracuseStep 14060429 = 5272661) B5272661
theorem B9373619 : Blo 2193435 9373619 := bstep (se 1 (by rfl) ⟨7030214, by rfl⟩ : syracuseStep 9373619 = 14060429) B14060429
theorem B6249079 : Blo 2193435 6249079 := bstep (se 1 (by rfl) ⟨4686809, by rfl⟩ : syracuseStep 6249079 = 9373619) B9373619
theorem B8332105 : Blo 2193435 8332105 := bstep (se 2 (by rfl) ⟨3124539, by rfl⟩ : syracuseStep 8332105 = 6249079) B6249079
theorem B11109473 : Blo 2193435 11109473 := bstep (se 2 (by rfl) ⟨4166052, by rfl⟩ : syracuseStep 11109473 = 8332105) B8332105
theorem B7406315 : Blo 2193435 7406315 := bstep (se 1 (by rfl) ⟨5554736, by rfl⟩ : syracuseStep 7406315 = 11109473) B11109473
theorem B4937543 : Blo 2193435 4937543 := bstep (se 1 (by rfl) ⟨3703157, by rfl⟩ : syracuseStep 4937543 = 7406315) B7406315
theorem B3291695 : Blo 2193435 3291695 := bstep (se 1 (by rfl) ⟨2468771, by rfl⟩ : syracuseStep 3291695 = 4937543) B4937543
theorem B2194463 : Blo 2193435 2194463 := bstep (se 1 (by rfl) ⟨1645847, by rfl⟩ : syracuseStep 2194463 = 3291695) B3291695
theorem B3291701 : Blo 2193435 3291701 := bbase (se 5 (by rfl) ⟨154298, by rfl⟩ : syracuseStep 3291701 = 308597) (by norm_num)
theorem B2194467 : Blo 2193435 2194467 := bstep (se 1 (by rfl) ⟨1645850, by rfl⟩ : syracuseStep 2194467 = 3291701) B3291701
theorem B5554757 : Blo 2193435 5554757 := bbase (se 4 (by rfl) ⟨520758, by rfl⟩ : syracuseStep 5554757 = 1041517) (by norm_num)
theorem B3703171 : Blo 2193435 3703171 := bstep (se 1 (by rfl) ⟨2777378, by rfl⟩ : syracuseStep 3703171 = 5554757) B5554757
theorem B4937561 : Blo 2193435 4937561 := bstep (se 2 (by rfl) ⟨1851585, by rfl⟩ : syracuseStep 4937561 = 3703171) B3703171
theorem B3291707 : Blo 2193435 3291707 := bstep (se 1 (by rfl) ⟨2468780, by rfl⟩ : syracuseStep 3291707 = 4937561) B4937561
theorem B2194471 : Blo 2193435 2194471 := bstep (se 1 (by rfl) ⟨1645853, by rfl⟩ : syracuseStep 2194471 = 3291707) B3291707
theorem B2468785 : Blo 2193435 2468785 := bbase (se 2 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 2468785 = 1851589) (by norm_num)
theorem B3291713 : Blo 2193435 3291713 := bstep (se 2 (by rfl) ⟨1234392, by rfl⟩ : syracuseStep 3291713 = 2468785) B2468785
theorem B2194475 : Blo 2193435 2194475 := bstep (se 1 (by rfl) ⟨1645856, by rfl⟩ : syracuseStep 2194475 = 3291713) B3291713
theorem B6249125 : Blo 2193435 6249125 := bbase (se 4 (by rfl) ⟨585855, by rfl⟩ : syracuseStep 6249125 = 1171711) (by norm_num)
theorem B4166083 : Blo 2193435 4166083 := bstep (se 1 (by rfl) ⟨3124562, by rfl⟩ : syracuseStep 4166083 = 6249125) B6249125
theorem B5554777 : Blo 2193435 5554777 := bstep (se 2 (by rfl) ⟨2083041, by rfl⟩ : syracuseStep 5554777 = 4166083) B4166083
theorem B7406369 : Blo 2193435 7406369 := bstep (se 2 (by rfl) ⟨2777388, by rfl⟩ : syracuseStep 7406369 = 5554777) B5554777
theorem B4937579 : Blo 2193435 4937579 := bstep (se 1 (by rfl) ⟨3703184, by rfl⟩ : syracuseStep 4937579 = 7406369) B7406369
theorem B3291719 : Blo 2193435 3291719 := bstep (se 1 (by rfl) ⟨2468789, by rfl⟩ : syracuseStep 3291719 = 4937579) B4937579
theorem B2194479 : Blo 2193435 2194479 := bstep (se 1 (by rfl) ⟨1645859, by rfl⟩ : syracuseStep 2194479 = 3291719) B3291719
theorem B3291725 : Blo 2193435 3291725 := bbase (se 3 (by rfl) ⟨617198, by rfl⟩ : syracuseStep 3291725 = 1234397) (by norm_num)
theorem B2194483 : Blo 2193435 2194483 := bstep (se 1 (by rfl) ⟨1645862, by rfl⟩ : syracuseStep 2194483 = 3291725) B3291725
theorem B4937597 : Blo 2193435 4937597 := bbase (se 3 (by rfl) ⟨925799, by rfl⟩ : syracuseStep 4937597 = 1851599) (by norm_num)
theorem B3291731 : Blo 2193435 3291731 := bstep (se 1 (by rfl) ⟨2468798, by rfl⟩ : syracuseStep 3291731 = 4937597) B4937597
theorem B2194487 : Blo 2193435 2194487 := bstep (se 1 (by rfl) ⟨1645865, by rfl⟩ : syracuseStep 2194487 = 3291731) B3291731
theorem B3703205 : Blo 2193435 3703205 := bbase (se 4 (by rfl) ⟨347175, by rfl⟩ : syracuseStep 3703205 = 694351) (by norm_num)
theorem B2468803 : Blo 2193435 2468803 := bstep (se 1 (by rfl) ⟨1851602, by rfl⟩ : syracuseStep 2468803 = 3703205) B3703205
theorem B3291737 : Blo 2193435 3291737 := bstep (se 2 (by rfl) ⟨1234401, by rfl⟩ : syracuseStep 3291737 = 2468803) B2468803
theorem B2194491 : Blo 2193435 2194491 := bstep (se 1 (by rfl) ⟨1645868, by rfl⟩ : syracuseStep 2194491 = 3291737) B3291737
theorem B7909109 : Blo 2193435 7909109 := bbase (se 5 (by rfl) ⟨370739, by rfl⟩ : syracuseStep 7909109 = 741479) (by norm_num)
theorem B5272739 : Blo 2193435 5272739 := bstep (se 1 (by rfl) ⟨3954554, by rfl⟩ : syracuseStep 5272739 = 7909109) B7909109
theorem B3515159 : Blo 2193435 3515159 := bstep (se 1 (by rfl) ⟨2636369, by rfl⟩ : syracuseStep 3515159 = 5272739) B5272739
theorem B2343439 : Blo 2193435 2343439 := bstep (se 1 (by rfl) ⟨1757579, by rfl⟩ : syracuseStep 2343439 = 3515159) B3515159
theorem B3124585 : Blo 2193435 3124585 := bstep (se 2 (by rfl) ⟨1171719, by rfl⟩ : syracuseStep 3124585 = 2343439) B2343439
theorem B16664453 : Blo 2193435 16664453 := bstep (se 4 (by rfl) ⟨1562292, by rfl⟩ : syracuseStep 16664453 = 3124585) B3124585
theorem B11109635 : Blo 2193435 11109635 := bstep (se 1 (by rfl) ⟨8332226, by rfl⟩ : syracuseStep 11109635 = 16664453) B16664453
theorem B7406423 : Blo 2193435 7406423 := bstep (se 1 (by rfl) ⟨5554817, by rfl⟩ : syracuseStep 7406423 = 11109635) B11109635
theorem B4937615 : Blo 2193435 4937615 := bstep (se 1 (by rfl) ⟨3703211, by rfl⟩ : syracuseStep 4937615 = 7406423) B7406423
theorem B3291743 : Blo 2193435 3291743 := bstep (se 1 (by rfl) ⟨2468807, by rfl⟩ : syracuseStep 3291743 = 4937615) B4937615
theorem B2194495 : Blo 2193435 2194495 := bstep (se 1 (by rfl) ⟨1645871, by rfl⟩ : syracuseStep 2194495 = 3291743) B3291743
theorem B3291749 : Blo 2193435 3291749 := bbase (se 4 (by rfl) ⟨308601, by rfl⟩ : syracuseStep 3291749 = 617203) (by norm_num)
theorem B2194499 : Blo 2193435 2194499 := bstep (se 1 (by rfl) ⟨1645874, by rfl⟩ : syracuseStep 2194499 = 3291749) B3291749
theorem B3124597 : Blo 2193435 3124597 := bbase (se 5 (by rfl) ⟨146465, by rfl⟩ : syracuseStep 3124597 = 292931) (by norm_num)
theorem B4166129 : Blo 2193435 4166129 := bstep (se 2 (by rfl) ⟨1562298, by rfl⟩ : syracuseStep 4166129 = 3124597) B3124597
theorem B2777419 : Blo 2193435 2777419 := bstep (se 1 (by rfl) ⟨2083064, by rfl⟩ : syracuseStep 2777419 = 4166129) B4166129
theorem B3703225 : Blo 2193435 3703225 := bstep (se 2 (by rfl) ⟨1388709, by rfl⟩ : syracuseStep 3703225 = 2777419) B2777419
theorem B4937633 : Blo 2193435 4937633 := bstep (se 2 (by rfl) ⟨1851612, by rfl⟩ : syracuseStep 4937633 = 3703225) B3703225
theorem B3291755 : Blo 2193435 3291755 := bstep (se 1 (by rfl) ⟨2468816, by rfl⟩ : syracuseStep 3291755 = 4937633) B4937633
theorem B2194503 : Blo 2193435 2194503 := bstep (se 1 (by rfl) ⟨1645877, by rfl⟩ : syracuseStep 2194503 = 3291755) B3291755
theorem B2468821 : Blo 2193435 2468821 := bbase (se 7 (by rfl) ⟨28931, by rfl⟩ : syracuseStep 2468821 = 57863) (by norm_num)
theorem B3291761 : Blo 2193435 3291761 := bstep (se 2 (by rfl) ⟨1234410, by rfl⟩ : syracuseStep 3291761 = 2468821) B2468821
theorem B2194507 : Blo 2193435 2194507 := bstep (se 1 (by rfl) ⟨1645880, by rfl⟩ : syracuseStep 2194507 = 3291761) B3291761
theorem B2777429 : Blo 2193435 2777429 := bbase (se 10 (by rfl) ⟨4068, by rfl⟩ : syracuseStep 2777429 = 8137) (by norm_num)
theorem B7406477 : Blo 2193435 7406477 := bstep (se 3 (by rfl) ⟨1388714, by rfl⟩ : syracuseStep 7406477 = 2777429) B2777429
theorem B4937651 : Blo 2193435 4937651 := bstep (se 1 (by rfl) ⟨3703238, by rfl⟩ : syracuseStep 4937651 = 7406477) B7406477
theorem B3291767 : Blo 2193435 3291767 := bstep (se 1 (by rfl) ⟨2468825, by rfl⟩ : syracuseStep 3291767 = 4937651) B4937651
theorem B2194511 : Blo 2193435 2194511 := bstep (se 1 (by rfl) ⟨1645883, by rfl⟩ : syracuseStep 2194511 = 3291767) B3291767
theorem B3291773 : Blo 2193435 3291773 := bbase (se 3 (by rfl) ⟨617207, by rfl⟩ : syracuseStep 3291773 = 1234415) (by norm_num)
theorem B2194515 : Blo 2193435 2194515 := bstep (se 1 (by rfl) ⟨1645886, by rfl⟩ : syracuseStep 2194515 = 3291773) B3291773
theorem B4937669 : Blo 2193435 4937669 := bbase (se 4 (by rfl) ⟨462906, by rfl⟩ : syracuseStep 4937669 = 925813) (by norm_num)
theorem B3291779 : Blo 2193435 3291779 := bstep (se 1 (by rfl) ⟨2468834, by rfl⟩ : syracuseStep 3291779 = 4937669) B4937669
theorem B2194519 : Blo 2193435 2194519 := bstep (se 1 (by rfl) ⟨1645889, by rfl⟩ : syracuseStep 2194519 = 3291779) B3291779
theorem B9373877 : Blo 2193435 9373877 := bbase (se 5 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 9373877 = 878801) (by norm_num)
theorem B6249251 : Blo 2193435 6249251 := bstep (se 1 (by rfl) ⟨4686938, by rfl⟩ : syracuseStep 6249251 = 9373877) B9373877
theorem B4166167 : Blo 2193435 4166167 := bstep (se 1 (by rfl) ⟨3124625, by rfl⟩ : syracuseStep 4166167 = 6249251) B6249251
theorem B5554889 : Blo 2193435 5554889 := bstep (se 2 (by rfl) ⟨2083083, by rfl⟩ : syracuseStep 5554889 = 4166167) B4166167
theorem B3703259 : Blo 2193435 3703259 := bstep (se 1 (by rfl) ⟨2777444, by rfl⟩ : syracuseStep 3703259 = 5554889) B5554889
theorem B2468839 : Blo 2193435 2468839 := bstep (se 1 (by rfl) ⟨1851629, by rfl⟩ : syracuseStep 2468839 = 3703259) B3703259
theorem B3291785 : Blo 2193435 3291785 := bstep (se 2 (by rfl) ⟨1234419, by rfl⟩ : syracuseStep 3291785 = 2468839) B2468839
theorem B2194523 : Blo 2193435 2194523 := bstep (se 1 (by rfl) ⟨1645892, by rfl⟩ : syracuseStep 2194523 = 3291785) B3291785
theorem B11109797 : Blo 2193435 11109797 := bbase (se 4 (by rfl) ⟨1041543, by rfl⟩ : syracuseStep 11109797 = 2083087) (by norm_num)
theorem B7406531 : Blo 2193435 7406531 := bstep (se 1 (by rfl) ⟨5554898, by rfl⟩ : syracuseStep 7406531 = 11109797) B11109797
theorem B4937687 : Blo 2193435 4937687 := bstep (se 1 (by rfl) ⟨3703265, by rfl⟩ : syracuseStep 4937687 = 7406531) B7406531
theorem B3291791 : Blo 2193435 3291791 := bstep (se 1 (by rfl) ⟨2468843, by rfl⟩ : syracuseStep 3291791 = 4937687) B4937687
theorem B2194527 : Blo 2193435 2194527 := bstep (se 1 (by rfl) ⟨1645895, by rfl⟩ : syracuseStep 2194527 = 3291791) B3291791
theorem B3291797 : Blo 2193435 3291797 := bbase (se 6 (by rfl) ⟨77151, by rfl⟩ : syracuseStep 3291797 = 154303) (by norm_num)
theorem B2194531 : Blo 2193435 2194531 := bstep (se 1 (by rfl) ⟨1645898, by rfl⟩ : syracuseStep 2194531 = 3291797) B3291797
theorem B15015221 : Blo 2193435 15015221 := bbase (se 5 (by rfl) ⟨703838, by rfl⟩ : syracuseStep 15015221 = 1407677) (by norm_num)
theorem B10010147 : Blo 2193435 10010147 := bstep (se 1 (by rfl) ⟨7507610, by rfl⟩ : syracuseStep 10010147 = 15015221) B15015221
theorem B26693725 : Blo 2193435 26693725 := bstep (se 3 (by rfl) ⟨5005073, by rfl⟩ : syracuseStep 26693725 = 10010147) B10010147
theorem B35591633 : Blo 2193435 35591633 := bstep (se 2 (by rfl) ⟨13346862, by rfl⟩ : syracuseStep 35591633 = 26693725) B26693725
theorem B23727755 : Blo 2193435 23727755 := bstep (se 1 (by rfl) ⟨17795816, by rfl⟩ : syracuseStep 23727755 = 35591633) B35591633
theorem B15818503 : Blo 2193435 15818503 := bstep (se 1 (by rfl) ⟨11863877, by rfl⟩ : syracuseStep 15818503 = 23727755) B23727755
theorem B21091337 : Blo 2193435 21091337 := bstep (se 2 (by rfl) ⟨7909251, by rfl⟩ : syracuseStep 21091337 = 15818503) B15818503
theorem B14060891 : Blo 2193435 14060891 := bstep (se 1 (by rfl) ⟨10545668, by rfl⟩ : syracuseStep 14060891 = 21091337) B21091337
theorem B9373927 : Blo 2193435 9373927 := bstep (se 1 (by rfl) ⟨7030445, by rfl⟩ : syracuseStep 9373927 = 14060891) B14060891
theorem B12498569 : Blo 2193435 12498569 := bstep (se 2 (by rfl) ⟨4686963, by rfl⟩ : syracuseStep 12498569 = 9373927) B9373927
theorem B8332379 : Blo 2193435 8332379 := bstep (se 1 (by rfl) ⟨6249284, by rfl⟩ : syracuseStep 8332379 = 12498569) B12498569
theorem B5554919 : Blo 2193435 5554919 := bstep (se 1 (by rfl) ⟨4166189, by rfl⟩ : syracuseStep 5554919 = 8332379) B8332379
theorem B3703279 : Blo 2193435 3703279 := bstep (se 1 (by rfl) ⟨2777459, by rfl⟩ : syracuseStep 3703279 = 5554919) B5554919
theorem B4937705 : Blo 2193435 4937705 := bstep (se 2 (by rfl) ⟨1851639, by rfl⟩ : syracuseStep 4937705 = 3703279) B3703279
theorem B3291803 : Blo 2193435 3291803 := bstep (se 1 (by rfl) ⟨2468852, by rfl⟩ : syracuseStep 3291803 = 4937705) B4937705
theorem B2194535 : Blo 2193435 2194535 := bstep (se 1 (by rfl) ⟨1645901, by rfl⟩ : syracuseStep 2194535 = 3291803) B3291803
theorem B2468857 : Blo 2193435 2468857 := bbase (se 2 (by rfl) ⟨925821, by rfl⟩ : syracuseStep 2468857 = 1851643) (by norm_num)
theorem B3291809 : Blo 2193435 3291809 := bstep (se 2 (by rfl) ⟨1234428, by rfl⟩ : syracuseStep 3291809 = 2468857) B2468857
theorem B2194539 : Blo 2193435 2194539 := bstep (se 1 (by rfl) ⟨1645904, by rfl⟩ : syracuseStep 2194539 = 3291809) B3291809
theorem B8897941 : Blo 2193435 8897941 := bbase (se 6 (by rfl) ⟨208545, by rfl⟩ : syracuseStep 8897941 = 417091) (by norm_num)
theorem B11863921 : Blo 2193435 11863921 := bstep (se 2 (by rfl) ⟨4448970, by rfl⟩ : syracuseStep 11863921 = 8897941) B8897941
theorem B15818561 : Blo 2193435 15818561 := bstep (se 2 (by rfl) ⟨5931960, by rfl⟩ : syracuseStep 15818561 = 11863921) B11863921
theorem B10545707 : Blo 2193435 10545707 := bstep (se 1 (by rfl) ⟨7909280, by rfl⟩ : syracuseStep 10545707 = 15818561) B15818561
theorem B7030471 : Blo 2193435 7030471 := bstep (se 1 (by rfl) ⟨5272853, by rfl⟩ : syracuseStep 7030471 = 10545707) B10545707
theorem B9373961 : Blo 2193435 9373961 := bstep (se 2 (by rfl) ⟨3515235, by rfl⟩ : syracuseStep 9373961 = 7030471) B7030471
theorem B6249307 : Blo 2193435 6249307 := bstep (se 1 (by rfl) ⟨4686980, by rfl⟩ : syracuseStep 6249307 = 9373961) B9373961
theorem B8332409 : Blo 2193435 8332409 := bstep (se 2 (by rfl) ⟨3124653, by rfl⟩ : syracuseStep 8332409 = 6249307) B6249307
theorem B5554939 : Blo 2193435 5554939 := bstep (se 1 (by rfl) ⟨4166204, by rfl⟩ : syracuseStep 5554939 = 8332409) B8332409
theorem B7406585 : Blo 2193435 7406585 := bstep (se 2 (by rfl) ⟨2777469, by rfl⟩ : syracuseStep 7406585 = 5554939) B5554939
theorem B4937723 : Blo 2193435 4937723 := bstep (se 1 (by rfl) ⟨3703292, by rfl⟩ : syracuseStep 4937723 = 7406585) B7406585
theorem B3291815 : Blo 2193435 3291815 := bstep (se 1 (by rfl) ⟨2468861, by rfl⟩ : syracuseStep 3291815 = 4937723) B4937723
theorem B2194543 : Blo 2193435 2194543 := bstep (se 1 (by rfl) ⟨1645907, by rfl⟩ : syracuseStep 2194543 = 3291815) B3291815
theorem B3291821 : Blo 2193435 3291821 := bbase (se 3 (by rfl) ⟨617216, by rfl⟩ : syracuseStep 3291821 = 1234433) (by norm_num)
theorem B2194547 : Blo 2193435 2194547 := bstep (se 1 (by rfl) ⟨1645910, by rfl⟩ : syracuseStep 2194547 = 3291821) B3291821
theorem B4937741 : Blo 2193435 4937741 := bbase (se 3 (by rfl) ⟨925826, by rfl⟩ : syracuseStep 4937741 = 1851653) (by norm_num)
theorem B3291827 : Blo 2193435 3291827 := bstep (se 1 (by rfl) ⟨2468870, by rfl⟩ : syracuseStep 3291827 = 4937741) B4937741
theorem B2194551 : Blo 2193435 2194551 := bstep (se 1 (by rfl) ⟨1645913, by rfl⟩ : syracuseStep 2194551 = 3291827) B3291827
theorem B2777485 : Blo 2193435 2777485 := bbase (se 3 (by rfl) ⟨520778, by rfl⟩ : syracuseStep 2777485 = 1041557) (by norm_num)
theorem B3703313 : Blo 2193435 3703313 := bstep (se 2 (by rfl) ⟨1388742, by rfl⟩ : syracuseStep 3703313 = 2777485) B2777485
theorem B2468875 : Blo 2193435 2468875 := bstep (se 1 (by rfl) ⟨1851656, by rfl⟩ : syracuseStep 2468875 = 3703313) B3703313
theorem B3291833 : Blo 2193435 3291833 := bstep (se 2 (by rfl) ⟨1234437, by rfl⟩ : syracuseStep 3291833 = 2468875) B2468875
theorem B2194555 : Blo 2193435 2194555 := bstep (se 1 (by rfl) ⟨1645916, by rfl⟩ : syracuseStep 2194555 = 3291833) B3291833
theorem B8898005 : Blo 2193435 8898005 := bbase (se 7 (by rfl) ⟨104273, by rfl⟩ : syracuseStep 8898005 = 208547) (by norm_num)
theorem B5932003 : Blo 2193435 5932003 := bstep (se 1 (by rfl) ⟨4449002, by rfl⟩ : syracuseStep 5932003 = 8898005) B8898005
theorem B7909337 : Blo 2193435 7909337 := bstep (se 2 (by rfl) ⟨2966001, by rfl⟩ : syracuseStep 7909337 = 5932003) B5932003
theorem B21091565 : Blo 2193435 21091565 := bstep (se 3 (by rfl) ⟨3954668, by rfl⟩ : syracuseStep 21091565 = 7909337) B7909337
theorem B14061043 : Blo 2193435 14061043 := bstep (se 1 (by rfl) ⟨10545782, by rfl⟩ : syracuseStep 14061043 = 21091565) B21091565
theorem B18748057 : Blo 2193435 18748057 := bstep (se 2 (by rfl) ⟨7030521, by rfl⟩ : syracuseStep 18748057 = 14061043) B14061043
theorem B24997409 : Blo 2193435 24997409 := bstep (se 2 (by rfl) ⟨9374028, by rfl⟩ : syracuseStep 24997409 = 18748057) B18748057
theorem B16664939 : Blo 2193435 16664939 := bstep (se 1 (by rfl) ⟨12498704, by rfl⟩ : syracuseStep 16664939 = 24997409) B24997409
theorem B11109959 : Blo 2193435 11109959 := bstep (se 1 (by rfl) ⟨8332469, by rfl⟩ : syracuseStep 11109959 = 16664939) B16664939
theorem B7406639 : Blo 2193435 7406639 := bstep (se 1 (by rfl) ⟨5554979, by rfl⟩ : syracuseStep 7406639 = 11109959) B11109959
theorem B4937759 : Blo 2193435 4937759 := bstep (se 1 (by rfl) ⟨3703319, by rfl⟩ : syracuseStep 4937759 = 7406639) B7406639
theorem B3291839 : Blo 2193435 3291839 := bstep (se 1 (by rfl) ⟨2468879, by rfl⟩ : syracuseStep 3291839 = 4937759) B4937759
theorem B2194559 : Blo 2193435 2194559 := bstep (se 1 (by rfl) ⟨1645919, by rfl⟩ : syracuseStep 2194559 = 3291839) B3291839
theorem B3291845 : Blo 2193435 3291845 := bbase (se 4 (by rfl) ⟨308610, by rfl⟩ : syracuseStep 3291845 = 617221) (by norm_num)
theorem B2194563 : Blo 2193435 2194563 := bstep (se 1 (by rfl) ⟨1645922, by rfl⟩ : syracuseStep 2194563 = 3291845) B3291845
theorem B3703333 : Blo 2193435 3703333 := bbase (se 4 (by rfl) ⟨347187, by rfl⟩ : syracuseStep 3703333 = 694375) (by norm_num)
theorem B4937777 : Blo 2193435 4937777 := bstep (se 2 (by rfl) ⟨1851666, by rfl⟩ : syracuseStep 4937777 = 3703333) B3703333
theorem B3291851 : Blo 2193435 3291851 := bstep (se 1 (by rfl) ⟨2468888, by rfl⟩ : syracuseStep 3291851 = 4937777) B4937777
theorem B2194567 : Blo 2193435 2194567 := bstep (se 1 (by rfl) ⟨1645925, by rfl⟩ : syracuseStep 2194567 = 3291851) B3291851
theorem B2468893 : Blo 2193435 2468893 := bbase (se 3 (by rfl) ⟨462917, by rfl⟩ : syracuseStep 2468893 = 925835) (by norm_num)
theorem B3291857 : Blo 2193435 3291857 := bstep (se 2 (by rfl) ⟨1234446, by rfl⟩ : syracuseStep 3291857 = 2468893) B2468893
theorem B2194571 : Blo 2193435 2194571 := bstep (se 1 (by rfl) ⟨1645928, by rfl⟩ : syracuseStep 2194571 = 3291857) B3291857
theorem B7406693 : Blo 2193435 7406693 := bbase (se 4 (by rfl) ⟨694377, by rfl⟩ : syracuseStep 7406693 = 1388755) (by norm_num)
theorem B4937795 : Blo 2193435 4937795 := bstep (se 1 (by rfl) ⟨3703346, by rfl⟩ : syracuseStep 4937795 = 7406693) B7406693
theorem B3291863 : Blo 2193435 3291863 := bstep (se 1 (by rfl) ⟨2468897, by rfl⟩ : syracuseStep 3291863 = 4937795) B4937795
theorem B2194575 : Blo 2193435 2194575 := bstep (se 1 (by rfl) ⟨1645931, by rfl⟩ : syracuseStep 2194575 = 3291863) B3291863
theorem B3291869 : Blo 2193435 3291869 := bbase (se 3 (by rfl) ⟨617225, by rfl⟩ : syracuseStep 3291869 = 1234451) (by norm_num)
theorem B2194579 : Blo 2193435 2194579 := bstep (se 1 (by rfl) ⟨1645934, by rfl⟩ : syracuseStep 2194579 = 3291869) B3291869
theorem B4937813 : Blo 2193435 4937813 := bbase (se 8 (by rfl) ⟨28932, by rfl⟩ : syracuseStep 4937813 = 57865) (by norm_num)
theorem B3291875 : Blo 2193435 3291875 := bstep (se 1 (by rfl) ⟨2468906, by rfl⟩ : syracuseStep 3291875 = 4937813) B4937813
theorem B2194583 : Blo 2193435 2194583 := bstep (se 1 (by rfl) ⟨1645937, by rfl⟩ : syracuseStep 2194583 = 3291875) B3291875
theorem B7030613 : Blo 2193435 7030613 := bbase (se 9 (by rfl) ⟨20597, by rfl⟩ : syracuseStep 7030613 = 41195) (by norm_num)
theorem B4687075 : Blo 2193435 4687075 := bstep (se 1 (by rfl) ⟨3515306, by rfl⟩ : syracuseStep 4687075 = 7030613) B7030613
theorem B6249433 : Blo 2193435 6249433 := bstep (se 2 (by rfl) ⟨2343537, by rfl⟩ : syracuseStep 6249433 = 4687075) B4687075
theorem B8332577 : Blo 2193435 8332577 := bstep (se 2 (by rfl) ⟨3124716, by rfl⟩ : syracuseStep 8332577 = 6249433) B6249433
theorem B5555051 : Blo 2193435 5555051 := bstep (se 1 (by rfl) ⟨4166288, by rfl⟩ : syracuseStep 5555051 = 8332577) B8332577
theorem B3703367 : Blo 2193435 3703367 := bstep (se 1 (by rfl) ⟨2777525, by rfl⟩ : syracuseStep 3703367 = 5555051) B5555051
theorem B2468911 : Blo 2193435 2468911 := bstep (se 1 (by rfl) ⟨1851683, by rfl⟩ : syracuseStep 2468911 = 3703367) B3703367
theorem B3291881 : Blo 2193435 3291881 := bstep (se 2 (by rfl) ⟨1234455, by rfl⟩ : syracuseStep 3291881 = 2468911) B2468911
theorem B2194587 : Blo 2193435 2194587 := bstep (se 1 (by rfl) ⟨1645940, by rfl⟩ : syracuseStep 2194587 = 3291881) B3291881
theorem B3753901 : Blo 2193435 3753901 := bbase (se 3 (by rfl) ⟨703856, by rfl⟩ : syracuseStep 3753901 = 1407713) (by norm_num)
theorem B5005201 : Blo 2193435 5005201 := bstep (se 2 (by rfl) ⟨1876950, by rfl⟩ : syracuseStep 5005201 = 3753901) B3753901
theorem B6673601 : Blo 2193435 6673601 := bstep (se 2 (by rfl) ⟨2502600, by rfl⟩ : syracuseStep 6673601 = 5005201) B5005201
theorem B17796269 : Blo 2193435 17796269 := bstep (se 3 (by rfl) ⟨3336800, by rfl⟩ : syracuseStep 17796269 = 6673601) B6673601
theorem B11864179 : Blo 2193435 11864179 := bstep (se 1 (by rfl) ⟨8898134, by rfl⟩ : syracuseStep 11864179 = 17796269) B17796269
theorem B15818905 : Blo 2193435 15818905 := bstep (se 2 (by rfl) ⟨5932089, by rfl⟩ : syracuseStep 15818905 = 11864179) B11864179
theorem B21091873 : Blo 2193435 21091873 := bstep (se 2 (by rfl) ⟨7909452, by rfl⟩ : syracuseStep 21091873 = 15818905) B15818905
theorem B28122497 : Blo 2193435 28122497 := bstep (se 2 (by rfl) ⟨10545936, by rfl⟩ : syracuseStep 28122497 = 21091873) B21091873
theorem B18748331 : Blo 2193435 18748331 := bstep (se 1 (by rfl) ⟨14061248, by rfl⟩ : syracuseStep 18748331 = 28122497) B28122497
theorem B12498887 : Blo 2193435 12498887 := bstep (se 1 (by rfl) ⟨9374165, by rfl⟩ : syracuseStep 12498887 = 18748331) B18748331
theorem B8332591 : Blo 2193435 8332591 := bstep (se 1 (by rfl) ⟨6249443, by rfl⟩ : syracuseStep 8332591 = 12498887) B12498887
theorem B11110121 : Blo 2193435 11110121 := bstep (se 2 (by rfl) ⟨4166295, by rfl⟩ : syracuseStep 11110121 = 8332591) B8332591
theorem B7406747 : Blo 2193435 7406747 := bstep (se 1 (by rfl) ⟨5555060, by rfl⟩ : syracuseStep 7406747 = 11110121) B11110121
theorem B4937831 : Blo 2193435 4937831 := bstep (se 1 (by rfl) ⟨3703373, by rfl⟩ : syracuseStep 4937831 = 7406747) B7406747
theorem B3291887 : Blo 2193435 3291887 := bstep (se 1 (by rfl) ⟨2468915, by rfl⟩ : syracuseStep 3291887 = 4937831) B4937831
theorem B2194591 : Blo 2193435 2194591 := bstep (se 1 (by rfl) ⟨1645943, by rfl⟩ : syracuseStep 2194591 = 3291887) B3291887
theorem B3291893 : Blo 2193435 3291893 := bbase (se 5 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 3291893 = 308615) (by norm_num)
theorem B2194595 : Blo 2193435 2194595 := bstep (se 1 (by rfl) ⟨1645946, by rfl⟩ : syracuseStep 2194595 = 3291893) B3291893
theorem B2375525 : Blo 2193435 2375525 := bbase (se 4 (by rfl) ⟨222705, by rfl⟩ : syracuseStep 2375525 = 445411) (by norm_num)
theorem B6334733 : Blo 2193435 6334733 := bstep (se 3 (by rfl) ⟨1187762, by rfl⟩ : syracuseStep 6334733 = 2375525) B2375525
theorem B16892621 : Blo 2193435 16892621 := bstep (se 3 (by rfl) ⟨3167366, by rfl⟩ : syracuseStep 16892621 = 6334733) B6334733
theorem B11261747 : Blo 2193435 11261747 := bstep (se 1 (by rfl) ⟨8446310, by rfl⟩ : syracuseStep 11261747 = 16892621) B16892621
theorem B7507831 : Blo 2193435 7507831 := bstep (se 1 (by rfl) ⟨5630873, by rfl⟩ : syracuseStep 7507831 = 11261747) B11261747
theorem B10010441 : Blo 2193435 10010441 := bstep (se 2 (by rfl) ⟨3753915, by rfl⟩ : syracuseStep 10010441 = 7507831) B7507831
theorem B6673627 : Blo 2193435 6673627 := bstep (se 1 (by rfl) ⟨5005220, by rfl⟩ : syracuseStep 6673627 = 10010441) B10010441
theorem B8898169 : Blo 2193435 8898169 := bstep (se 2 (by rfl) ⟨3336813, by rfl⟩ : syracuseStep 8898169 = 6673627) B6673627
theorem B11864225 : Blo 2193435 11864225 := bstep (se 2 (by rfl) ⟨4449084, by rfl⟩ : syracuseStep 11864225 = 8898169) B8898169
theorem B7909483 : Blo 2193435 7909483 := bstep (se 1 (by rfl) ⟨5932112, by rfl⟩ : syracuseStep 7909483 = 11864225) B11864225
theorem B10545977 : Blo 2193435 10545977 := bstep (se 2 (by rfl) ⟨3954741, by rfl⟩ : syracuseStep 10545977 = 7909483) B7909483
theorem B7030651 : Blo 2193435 7030651 := bstep (se 1 (by rfl) ⟨5272988, by rfl⟩ : syracuseStep 7030651 = 10545977) B10545977
theorem B9374201 : Blo 2193435 9374201 := bstep (se 2 (by rfl) ⟨3515325, by rfl⟩ : syracuseStep 9374201 = 7030651) B7030651
theorem B6249467 : Blo 2193435 6249467 := bstep (se 1 (by rfl) ⟨4687100, by rfl⟩ : syracuseStep 6249467 = 9374201) B9374201
theorem B4166311 : Blo 2193435 4166311 := bstep (se 1 (by rfl) ⟨3124733, by rfl⟩ : syracuseStep 4166311 = 6249467) B6249467
theorem B5555081 : Blo 2193435 5555081 := bstep (se 2 (by rfl) ⟨2083155, by rfl⟩ : syracuseStep 5555081 = 4166311) B4166311
theorem B3703387 : Blo 2193435 3703387 := bstep (se 1 (by rfl) ⟨2777540, by rfl⟩ : syracuseStep 3703387 = 5555081) B5555081
theorem B4937849 : Blo 2193435 4937849 := bstep (se 2 (by rfl) ⟨1851693, by rfl⟩ : syracuseStep 4937849 = 3703387) B3703387
theorem B3291899 : Blo 2193435 3291899 := bstep (se 1 (by rfl) ⟨2468924, by rfl⟩ : syracuseStep 3291899 = 4937849) B4937849
theorem B2194599 : Blo 2193435 2194599 := bstep (se 1 (by rfl) ⟨1645949, by rfl⟩ : syracuseStep 2194599 = 3291899) B3291899
theorem B2468929 : Blo 2193435 2468929 := bbase (se 2 (by rfl) ⟨925848, by rfl⟩ : syracuseStep 2468929 = 1851697) (by norm_num)
theorem B3291905 : Blo 2193435 3291905 := bstep (se 2 (by rfl) ⟨1234464, by rfl⟩ : syracuseStep 3291905 = 2468929) B2468929
theorem B2194603 : Blo 2193435 2194603 := bstep (se 1 (by rfl) ⟨1645952, by rfl⟩ : syracuseStep 2194603 = 3291905) B3291905
theorem B5555101 : Blo 2193435 5555101 := bbase (se 3 (by rfl) ⟨1041581, by rfl⟩ : syracuseStep 5555101 = 2083163) (by norm_num)
theorem B7406801 : Blo 2193435 7406801 := bstep (se 2 (by rfl) ⟨2777550, by rfl⟩ : syracuseStep 7406801 = 5555101) B5555101
theorem B4937867 : Blo 2193435 4937867 := bstep (se 1 (by rfl) ⟨3703400, by rfl⟩ : syracuseStep 4937867 = 7406801) B7406801
theorem B3291911 : Blo 2193435 3291911 := bstep (se 1 (by rfl) ⟨2468933, by rfl⟩ : syracuseStep 3291911 = 4937867) B4937867
theorem B2194607 : Blo 2193435 2194607 := bstep (se 1 (by rfl) ⟨1645955, by rfl⟩ : syracuseStep 2194607 = 3291911) B3291911
theorem B3291917 : Blo 2193435 3291917 := bbase (se 3 (by rfl) ⟨617234, by rfl⟩ : syracuseStep 3291917 = 1234469) (by norm_num)
theorem B2194611 : Blo 2193435 2194611 := bstep (se 1 (by rfl) ⟨1645958, by rfl⟩ : syracuseStep 2194611 = 3291917) B3291917
theorem B4937885 : Blo 2193435 4937885 := bbase (se 3 (by rfl) ⟨925853, by rfl⟩ : syracuseStep 4937885 = 1851707) (by norm_num)
theorem B3291923 : Blo 2193435 3291923 := bstep (se 1 (by rfl) ⟨2468942, by rfl⟩ : syracuseStep 3291923 = 4937885) B4937885
theorem B2194615 : Blo 2193435 2194615 := bstep (se 1 (by rfl) ⟨1645961, by rfl⟩ : syracuseStep 2194615 = 3291923) B3291923
theorem B3703421 : Blo 2193435 3703421 := bbase (se 3 (by rfl) ⟨694391, by rfl⟩ : syracuseStep 3703421 = 1388783) (by norm_num)
theorem B2468947 : Blo 2193435 2468947 := bstep (se 1 (by rfl) ⟨1851710, by rfl⟩ : syracuseStep 2468947 = 3703421) B3703421
theorem B3291929 : Blo 2193435 3291929 := bstep (se 2 (by rfl) ⟨1234473, by rfl⟩ : syracuseStep 3291929 = 2468947) B2468947
theorem B2194619 : Blo 2193435 2194619 := bstep (se 1 (by rfl) ⟨1645964, by rfl⟩ : syracuseStep 2194619 = 3291929) B3291929
theorem B10010549 : Blo 2193435 10010549 := bbase (se 5 (by rfl) ⟨469244, by rfl⟩ : syracuseStep 10010549 = 938489) (by norm_num)
theorem B6673699 : Blo 2193435 6673699 := bstep (se 1 (by rfl) ⟨5005274, by rfl⟩ : syracuseStep 6673699 = 10010549) B10010549
theorem B8898265 : Blo 2193435 8898265 := bstep (se 2 (by rfl) ⟨3336849, by rfl⟩ : syracuseStep 8898265 = 6673699) B6673699
theorem B11864353 : Blo 2193435 11864353 := bstep (se 2 (by rfl) ⟨4449132, by rfl⟩ : syracuseStep 11864353 = 8898265) B8898265
theorem B15819137 : Blo 2193435 15819137 := bstep (se 2 (by rfl) ⟨5932176, by rfl⟩ : syracuseStep 15819137 = 11864353) B11864353
theorem B10546091 : Blo 2193435 10546091 := bstep (se 1 (by rfl) ⟨7909568, by rfl⟩ : syracuseStep 10546091 = 15819137) B15819137
theorem B7030727 : Blo 2193435 7030727 := bstep (se 1 (by rfl) ⟨5273045, by rfl⟩ : syracuseStep 7030727 = 10546091) B10546091
theorem B4687151 : Blo 2193435 4687151 := bstep (se 1 (by rfl) ⟨3515363, by rfl⟩ : syracuseStep 4687151 = 7030727) B7030727
theorem B12499069 : Blo 2193435 12499069 := bstep (se 3 (by rfl) ⟨2343575, by rfl⟩ : syracuseStep 12499069 = 4687151) B4687151
theorem B16665425 : Blo 2193435 16665425 := bstep (se 2 (by rfl) ⟨6249534, by rfl⟩ : syracuseStep 16665425 = 12499069) B12499069
theorem B11110283 : Blo 2193435 11110283 := bstep (se 1 (by rfl) ⟨8332712, by rfl⟩ : syracuseStep 11110283 = 16665425) B16665425
theorem B7406855 : Blo 2193435 7406855 := bstep (se 1 (by rfl) ⟨5555141, by rfl⟩ : syracuseStep 7406855 = 11110283) B11110283
theorem B4937903 : Blo 2193435 4937903 := bstep (se 1 (by rfl) ⟨3703427, by rfl⟩ : syracuseStep 4937903 = 7406855) B7406855
theorem B3291935 : Blo 2193435 3291935 := bstep (se 1 (by rfl) ⟨2468951, by rfl⟩ : syracuseStep 3291935 = 4937903) B4937903
theorem B2194623 : Blo 2193435 2194623 := bstep (se 1 (by rfl) ⟨1645967, by rfl⟩ : syracuseStep 2194623 = 3291935) B3291935
theorem B3291941 : Blo 2193435 3291941 := bbase (se 4 (by rfl) ⟨308619, by rfl⟩ : syracuseStep 3291941 = 617239) (by norm_num)
theorem B2194627 : Blo 2193435 2194627 := bstep (se 1 (by rfl) ⟨1645970, by rfl⟩ : syracuseStep 2194627 = 3291941) B3291941
theorem B2777581 : Blo 2193435 2777581 := bbase (se 3 (by rfl) ⟨520796, by rfl⟩ : syracuseStep 2777581 = 1041593) (by norm_num)
theorem B3703441 : Blo 2193435 3703441 := bstep (se 2 (by rfl) ⟨1388790, by rfl⟩ : syracuseStep 3703441 = 2777581) B2777581
theorem B4937921 : Blo 2193435 4937921 := bstep (se 2 (by rfl) ⟨1851720, by rfl⟩ : syracuseStep 4937921 = 3703441) B3703441
theorem B3291947 : Blo 2193435 3291947 := bstep (se 1 (by rfl) ⟨2468960, by rfl⟩ : syracuseStep 3291947 = 4937921) B4937921
theorem B2194631 : Blo 2193435 2194631 := bstep (se 1 (by rfl) ⟨1645973, by rfl⟩ : syracuseStep 2194631 = 3291947) B3291947
theorem B2468965 : Blo 2193435 2468965 := bbase (se 4 (by rfl) ⟨231465, by rfl⟩ : syracuseStep 2468965 = 462931) (by norm_num)
theorem B3291953 : Blo 2193435 3291953 := bstep (se 2 (by rfl) ⟨1234482, by rfl⟩ : syracuseStep 3291953 = 2468965) B2468965
theorem B2194635 : Blo 2193435 2194635 := bstep (se 1 (by rfl) ⟨1645976, by rfl⟩ : syracuseStep 2194635 = 3291953) B3291953
theorem B2343593 : Blo 2193435 2343593 := bbase (se 2 (by rfl) ⟨878847, by rfl⟩ : syracuseStep 2343593 = 1757695) (by norm_num)
theorem B6249581 : Blo 2193435 6249581 := bstep (se 3 (by rfl) ⟨1171796, by rfl⟩ : syracuseStep 6249581 = 2343593) B2343593
theorem B4166387 : Blo 2193435 4166387 := bstep (se 1 (by rfl) ⟨3124790, by rfl⟩ : syracuseStep 4166387 = 6249581) B6249581
theorem B2777591 : Blo 2193435 2777591 := bstep (se 1 (by rfl) ⟨2083193, by rfl⟩ : syracuseStep 2777591 = 4166387) B4166387
theorem B7406909 : Blo 2193435 7406909 := bstep (se 3 (by rfl) ⟨1388795, by rfl⟩ : syracuseStep 7406909 = 2777591) B2777591
theorem B4937939 : Blo 2193435 4937939 := bstep (se 1 (by rfl) ⟨3703454, by rfl⟩ : syracuseStep 4937939 = 7406909) B7406909
theorem B3291959 : Blo 2193435 3291959 := bstep (se 1 (by rfl) ⟨2468969, by rfl⟩ : syracuseStep 3291959 = 4937939) B4937939
theorem B2194639 : Blo 2193435 2194639 := bstep (se 1 (by rfl) ⟨1645979, by rfl⟩ : syracuseStep 2194639 = 3291959) B3291959
theorem B3291965 : Blo 2193435 3291965 := bbase (se 3 (by rfl) ⟨617243, by rfl⟩ : syracuseStep 3291965 = 1234487) (by norm_num)
theorem B2194643 : Blo 2193435 2194643 := bstep (se 1 (by rfl) ⟨1645982, by rfl⟩ : syracuseStep 2194643 = 3291965) B3291965
theorem B4937957 : Blo 2193435 4937957 := bbase (se 4 (by rfl) ⟨462933, by rfl⟩ : syracuseStep 4937957 = 925867) (by norm_num)
theorem B3291971 : Blo 2193435 3291971 := bstep (se 1 (by rfl) ⟨2468978, by rfl⟩ : syracuseStep 3291971 = 4937957) B4937957
theorem B2194647 : Blo 2193435 2194647 := bstep (se 1 (by rfl) ⟨1645985, by rfl⟩ : syracuseStep 2194647 = 3291971) B3291971
theorem B5555213 : Blo 2193435 5555213 := bbase (se 3 (by rfl) ⟨1041602, by rfl⟩ : syracuseStep 5555213 = 2083205) (by norm_num)
theorem B3703475 : Blo 2193435 3703475 := bstep (se 1 (by rfl) ⟨2777606, by rfl⟩ : syracuseStep 3703475 = 5555213) B5555213
theorem B2468983 : Blo 2193435 2468983 := bstep (se 1 (by rfl) ⟨1851737, by rfl⟩ : syracuseStep 2468983 = 3703475) B3703475
theorem B3291977 : Blo 2193435 3291977 := bstep (se 2 (by rfl) ⟨1234491, by rfl⟩ : syracuseStep 3291977 = 2468983) B2468983
theorem B2194651 : Blo 2193435 2194651 := bstep (se 1 (by rfl) ⟨1645988, by rfl⟩ : syracuseStep 2194651 = 3291977) B3291977
theorem B3124813 : Blo 2193435 3124813 := bbase (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) (by norm_num)
theorem B4166417 : Blo 2193435 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B11110445 : Blo 2193435 11110445 := bstep (se 3 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 11110445 = 4166417) B4166417
theorem B7406963 : Blo 2193435 7406963 := bstep (se 1 (by rfl) ⟨5555222, by rfl⟩ : syracuseStep 7406963 = 11110445) B11110445
theorem B4937975 : Blo 2193435 4937975 := bstep (se 1 (by rfl) ⟨3703481, by rfl⟩ : syracuseStep 4937975 = 7406963) B7406963
theorem B3291983 : Blo 2193435 3291983 := bstep (se 1 (by rfl) ⟨2468987, by rfl⟩ : syracuseStep 3291983 = 4937975) B4937975
theorem B2194655 : Blo 2193435 2194655 := bstep (se 1 (by rfl) ⟨1645991, by rfl⟩ : syracuseStep 2194655 = 3291983) B3291983
theorem B3291989 : Blo 2193435 3291989 := bbase (se 9 (by rfl) ⟨9644, by rfl⟩ : syracuseStep 3291989 = 19289) (by norm_num)
theorem B2194659 : Blo 2193435 2194659 := bstep (se 1 (by rfl) ⟨1645994, by rfl⟩ : syracuseStep 2194659 = 3291989) B3291989
theorem B4687237 : Blo 2193435 4687237 := bbase (se 4 (by rfl) ⟨439428, by rfl⟩ : syracuseStep 4687237 = 878857) (by norm_num)
theorem B6249649 : Blo 2193435 6249649 := bstep (se 2 (by rfl) ⟨2343618, by rfl⟩ : syracuseStep 6249649 = 4687237) B4687237
theorem B8332865 : Blo 2193435 8332865 := bstep (se 2 (by rfl) ⟨3124824, by rfl⟩ : syracuseStep 8332865 = 6249649) B6249649
theorem B5555243 : Blo 2193435 5555243 := bstep (se 1 (by rfl) ⟨4166432, by rfl⟩ : syracuseStep 5555243 = 8332865) B8332865
theorem B3703495 : Blo 2193435 3703495 := bstep (se 1 (by rfl) ⟨2777621, by rfl⟩ : syracuseStep 3703495 = 5555243) B5555243
theorem B4937993 : Blo 2193435 4937993 := bstep (se 2 (by rfl) ⟨1851747, by rfl⟩ : syracuseStep 4937993 = 3703495) B3703495
theorem B3291995 : Blo 2193435 3291995 := bstep (se 1 (by rfl) ⟨2468996, by rfl⟩ : syracuseStep 3291995 = 4937993) B4937993
theorem B2194663 : Blo 2193435 2194663 := bstep (se 1 (by rfl) ⟨1645997, by rfl⟩ : syracuseStep 2194663 = 3291995) B3291995
theorem B2469001 : Blo 2193435 2469001 := bbase (se 2 (by rfl) ⟨925875, by rfl⟩ : syracuseStep 2469001 = 1851751) (by norm_num)
theorem B3292001 : Blo 2193435 3292001 := bstep (se 2 (by rfl) ⟨1234500, by rfl⟩ : syracuseStep 3292001 = 2469001) B2469001
theorem B2194667 : Blo 2193435 2194667 := bstep (se 1 (by rfl) ⟨1646000, by rfl⟩ : syracuseStep 2194667 = 3292001) B3292001
theorem B10426133 : Blo 2193435 10426133 := bbase (se 6 (by rfl) ⟨244362, by rfl⟩ : syracuseStep 10426133 = 488725) (by norm_num)
theorem B6950755 : Blo 2193435 6950755 := bstep (se 1 (by rfl) ⟨5213066, by rfl⟩ : syracuseStep 6950755 = 10426133) B10426133
theorem B37070693 : Blo 2193435 37070693 := bstep (se 4 (by rfl) ⟨3475377, by rfl⟩ : syracuseStep 37070693 = 6950755) B6950755
theorem B24713795 : Blo 2193435 24713795 := bstep (se 1 (by rfl) ⟨18535346, by rfl⟩ : syracuseStep 24713795 = 37070693) B37070693
theorem B65903453 : Blo 2193435 65903453 := bstep (se 3 (by rfl) ⟨12356897, by rfl⟩ : syracuseStep 65903453 = 24713795) B24713795
theorem B43935635 : Blo 2193435 43935635 := bstep (se 1 (by rfl) ⟨32951726, by rfl⟩ : syracuseStep 43935635 = 65903453) B65903453
theorem B29290423 : Blo 2193435 29290423 := bstep (se 1 (by rfl) ⟨21967817, by rfl⟩ : syracuseStep 29290423 = 43935635) B43935635
theorem B39053897 : Blo 2193435 39053897 := bstep (se 2 (by rfl) ⟨14645211, by rfl⟩ : syracuseStep 39053897 = 29290423) B29290423
theorem B26035931 : Blo 2193435 26035931 := bstep (se 1 (by rfl) ⟨19526948, by rfl⟩ : syracuseStep 26035931 = 39053897) B39053897
theorem B69429149 : Blo 2193435 69429149 := bstep (se 3 (by rfl) ⟨13017965, by rfl⟩ : syracuseStep 69429149 = 26035931) B26035931
theorem B46286099 : Blo 2193435 46286099 := bstep (se 1 (by rfl) ⟨34714574, by rfl⟩ : syracuseStep 46286099 = 69429149) B69429149
theorem B30857399 : Blo 2193435 30857399 := bstep (se 1 (by rfl) ⟨23143049, by rfl⟩ : syracuseStep 30857399 = 46286099) B46286099
theorem B20571599 : Blo 2193435 20571599 := bstep (se 1 (by rfl) ⟨15428699, by rfl⟩ : syracuseStep 20571599 = 30857399) B30857399
theorem B13714399 : Blo 2193435 13714399 := bstep (se 1 (by rfl) ⟨10285799, by rfl⟩ : syracuseStep 13714399 = 20571599) B20571599
theorem B73143461 : Blo 2193435 73143461 := bstep (se 4 (by rfl) ⟨6857199, by rfl⟩ : syracuseStep 73143461 = 13714399) B13714399
theorem B48762307 : Blo 2193435 48762307 := bstep (se 1 (by rfl) ⟨36571730, by rfl⟩ : syracuseStep 48762307 = 73143461) B73143461
theorem B260065637 : Blo 2193435 260065637 := bstep (se 4 (by rfl) ⟨24381153, by rfl⟩ : syracuseStep 260065637 = 48762307) B48762307
theorem B173377091 : Blo 2193435 173377091 := bstep (se 1 (by rfl) ⟨130032818, by rfl⟩ : syracuseStep 173377091 = 260065637) B260065637
theorem B115584727 : Blo 2193435 115584727 := bstep (se 1 (by rfl) ⟨86688545, by rfl⟩ : syracuseStep 115584727 = 173377091) B173377091
theorem B154112969 : Blo 2193435 154112969 := bstep (se 2 (by rfl) ⟨57792363, by rfl⟩ : syracuseStep 154112969 = 115584727) B115584727
theorem B102741979 : Blo 2193435 102741979 := bstep (se 1 (by rfl) ⟨77056484, by rfl⟩ : syracuseStep 102741979 = 154112969) B154112969
theorem B136989305 : Blo 2193435 136989305 := bstep (se 2 (by rfl) ⟨51370989, by rfl⟩ : syracuseStep 136989305 = 102741979) B102741979
theorem B91326203 : Blo 2193435 91326203 := bstep (se 1 (by rfl) ⟨68494652, by rfl⟩ : syracuseStep 91326203 = 136989305) B136989305
theorem B60884135 : Blo 2193435 60884135 := bstep (se 1 (by rfl) ⟨45663101, by rfl⟩ : syracuseStep 60884135 = 91326203) B91326203
theorem B40589423 : Blo 2193435 40589423 := bstep (se 1 (by rfl) ⟨30442067, by rfl⟩ : syracuseStep 40589423 = 60884135) B60884135
theorem B27059615 : Blo 2193435 27059615 := bstep (se 1 (by rfl) ⟨20294711, by rfl⟩ : syracuseStep 27059615 = 40589423) B40589423
theorem B18039743 : Blo 2193435 18039743 := bstep (se 1 (by rfl) ⟨13529807, by rfl⟩ : syracuseStep 18039743 = 27059615) B27059615
theorem B12026495 : Blo 2193435 12026495 := bstep (se 1 (by rfl) ⟨9019871, by rfl⟩ : syracuseStep 12026495 = 18039743) B18039743
theorem B8017663 : Blo 2193435 8017663 := bstep (se 1 (by rfl) ⟨6013247, by rfl⟩ : syracuseStep 8017663 = 12026495) B12026495
theorem B10690217 : Blo 2193435 10690217 := bstep (se 2 (by rfl) ⟨4008831, by rfl⟩ : syracuseStep 10690217 = 8017663) B8017663
theorem B7126811 : Blo 2193435 7126811 := bstep (se 1 (by rfl) ⟨5345108, by rfl⟩ : syracuseStep 7126811 = 10690217) B10690217
theorem B4751207 : Blo 2193435 4751207 := bstep (se 1 (by rfl) ⟨3563405, by rfl⟩ : syracuseStep 4751207 = 7126811) B7126811
theorem B3167471 : Blo 2193435 3167471 := bstep (se 1 (by rfl) ⟨2375603, by rfl⟩ : syracuseStep 3167471 = 4751207) B4751207
theorem B8446589 : Blo 2193435 8446589 := bstep (se 3 (by rfl) ⟨1583735, by rfl⟩ : syracuseStep 8446589 = 3167471) B3167471
theorem B5631059 : Blo 2193435 5631059 := bstep (se 1 (by rfl) ⟨4223294, by rfl⟩ : syracuseStep 5631059 = 8446589) B8446589
theorem B3754039 : Blo 2193435 3754039 := bstep (se 1 (by rfl) ⟨2815529, by rfl⟩ : syracuseStep 3754039 = 5631059) B5631059
theorem B5005385 : Blo 2193435 5005385 := bstep (se 2 (by rfl) ⟨1877019, by rfl⟩ : syracuseStep 5005385 = 3754039) B3754039
theorem B3336923 : Blo 2193435 3336923 := bstep (se 1 (by rfl) ⟨2502692, by rfl⟩ : syracuseStep 3336923 = 5005385) B5005385
theorem B2224615 : Blo 2193435 2224615 := bstep (se 1 (by rfl) ⟨1668461, by rfl⟩ : syracuseStep 2224615 = 3336923) B3336923
theorem B2966153 : Blo 2193435 2966153 := bstep (se 2 (by rfl) ⟨1112307, by rfl⟩ : syracuseStep 2966153 = 2224615) B2224615
theorem B7909741 : Blo 2193435 7909741 := bstep (se 3 (by rfl) ⟨1483076, by rfl⟩ : syracuseStep 7909741 = 2966153) B2966153
theorem B42185285 : Blo 2193435 42185285 := bstep (se 4 (by rfl) ⟨3954870, by rfl⟩ : syracuseStep 42185285 = 7909741) B7909741
theorem B28123523 : Blo 2193435 28123523 := bstep (se 1 (by rfl) ⟨21092642, by rfl⟩ : syracuseStep 28123523 = 42185285) B42185285
theorem B18749015 : Blo 2193435 18749015 := bstep (se 1 (by rfl) ⟨14061761, by rfl⟩ : syracuseStep 18749015 = 28123523) B28123523
theorem B12499343 : Blo 2193435 12499343 := bstep (se 1 (by rfl) ⟨9374507, by rfl⟩ : syracuseStep 12499343 = 18749015) B18749015
theorem B8332895 : Blo 2193435 8332895 := bstep (se 1 (by rfl) ⟨6249671, by rfl⟩ : syracuseStep 8332895 = 12499343) B12499343
theorem B5555263 : Blo 2193435 5555263 := bstep (se 1 (by rfl) ⟨4166447, by rfl⟩ : syracuseStep 5555263 = 8332895) B8332895
theorem B7407017 : Blo 2193435 7407017 := bstep (se 2 (by rfl) ⟨2777631, by rfl⟩ : syracuseStep 7407017 = 5555263) B5555263
theorem B4938011 : Blo 2193435 4938011 := bstep (se 1 (by rfl) ⟨3703508, by rfl⟩ : syracuseStep 4938011 = 7407017) B7407017
theorem B3292007 : Blo 2193435 3292007 := bstep (se 1 (by rfl) ⟨2469005, by rfl⟩ : syracuseStep 3292007 = 4938011) B4938011
theorem B2194671 : Blo 2193435 2194671 := bstep (se 1 (by rfl) ⟨1646003, by rfl⟩ : syracuseStep 2194671 = 3292007) B3292007
theorem B3292013 : Blo 2193435 3292013 := bbase (se 3 (by rfl) ⟨617252, by rfl⟩ : syracuseStep 3292013 = 1234505) (by norm_num)
theorem B2194675 : Blo 2193435 2194675 := bstep (se 1 (by rfl) ⟨1646006, by rfl⟩ : syracuseStep 2194675 = 3292013) B3292013
theorem B4938029 : Blo 2193435 4938029 := bbase (se 3 (by rfl) ⟨925880, by rfl⟩ : syracuseStep 4938029 = 1851761) (by norm_num)
theorem B3292019 : Blo 2193435 3292019 := bstep (se 1 (by rfl) ⟨2469014, by rfl⟩ : syracuseStep 3292019 = 4938029) B4938029
theorem B2194679 : Blo 2193435 2194679 := bstep (se 1 (by rfl) ⟨1646009, by rfl⟩ : syracuseStep 2194679 = 3292019) B3292019
theorem B16893269 : Blo 2193435 16893269 := bbase (se 12 (by rfl) ⟨6186, by rfl⟩ : syracuseStep 16893269 = 12373) (by norm_num)
theorem B11262179 : Blo 2193435 11262179 := bstep (se 1 (by rfl) ⟨8446634, by rfl⟩ : syracuseStep 11262179 = 16893269) B16893269
theorem B30032477 : Blo 2193435 30032477 := bstep (se 3 (by rfl) ⟨5631089, by rfl⟩ : syracuseStep 30032477 = 11262179) B11262179
theorem B20021651 : Blo 2193435 20021651 := bstep (se 1 (by rfl) ⟨15016238, by rfl⟩ : syracuseStep 20021651 = 30032477) B30032477
theorem B13347767 : Blo 2193435 13347767 := bstep (se 1 (by rfl) ⟨10010825, by rfl⟩ : syracuseStep 13347767 = 20021651) B20021651
theorem B8898511 : Blo 2193435 8898511 := bstep (se 1 (by rfl) ⟨6673883, by rfl⟩ : syracuseStep 8898511 = 13347767) B13347767
theorem B11864681 : Blo 2193435 11864681 := bstep (se 2 (by rfl) ⟨4449255, by rfl⟩ : syracuseStep 11864681 = 8898511) B8898511
theorem B7909787 : Blo 2193435 7909787 := bstep (se 1 (by rfl) ⟨5932340, by rfl⟩ : syracuseStep 7909787 = 11864681) B11864681
theorem B5273191 : Blo 2193435 5273191 := bstep (se 1 (by rfl) ⟨3954893, by rfl⟩ : syracuseStep 5273191 = 7909787) B7909787
theorem B7030921 : Blo 2193435 7030921 := bstep (se 2 (by rfl) ⟨2636595, by rfl⟩ : syracuseStep 7030921 = 5273191) B5273191
theorem B9374561 : Blo 2193435 9374561 := bstep (se 2 (by rfl) ⟨3515460, by rfl⟩ : syracuseStep 9374561 = 7030921) B7030921
theorem B6249707 : Blo 2193435 6249707 := bstep (se 1 (by rfl) ⟨4687280, by rfl⟩ : syracuseStep 6249707 = 9374561) B9374561
theorem B4166471 : Blo 2193435 4166471 := bstep (se 1 (by rfl) ⟨3124853, by rfl⟩ : syracuseStep 4166471 = 6249707) B6249707
theorem B2777647 : Blo 2193435 2777647 := bstep (se 1 (by rfl) ⟨2083235, by rfl⟩ : syracuseStep 2777647 = 4166471) B4166471
theorem B3703529 : Blo 2193435 3703529 := bstep (se 2 (by rfl) ⟨1388823, by rfl⟩ : syracuseStep 3703529 = 2777647) B2777647
theorem B2469019 : Blo 2193435 2469019 := bstep (se 1 (by rfl) ⟨1851764, by rfl⟩ : syracuseStep 2469019 = 3703529) B3703529
theorem B3292025 : Blo 2193435 3292025 := bstep (se 2 (by rfl) ⟨1234509, by rfl⟩ : syracuseStep 3292025 = 2469019) B2469019
theorem B2194683 : Blo 2193435 2194683 := bstep (se 1 (by rfl) ⟨1646012, by rfl⟩ : syracuseStep 2194683 = 3292025) B3292025
theorem B8017717 : Blo 2193435 8017717 := bbase (se 5 (by rfl) ⟨375830, by rfl⟩ : syracuseStep 8017717 = 751661) (by norm_num)
theorem B10690289 : Blo 2193435 10690289 := bstep (se 2 (by rfl) ⟨4008858, by rfl⟩ : syracuseStep 10690289 = 8017717) B8017717
theorem B7126859 : Blo 2193435 7126859 := bstep (se 1 (by rfl) ⟨5345144, by rfl⟩ : syracuseStep 7126859 = 10690289) B10690289
theorem B4751239 : Blo 2193435 4751239 := bstep (se 1 (by rfl) ⟨3563429, by rfl⟩ : syracuseStep 4751239 = 7126859) B7126859
theorem B6334985 : Blo 2193435 6334985 := bstep (se 2 (by rfl) ⟨2375619, by rfl⟩ : syracuseStep 6334985 = 4751239) B4751239
theorem B4223323 : Blo 2193435 4223323 := bstep (se 1 (by rfl) ⟨3167492, by rfl⟩ : syracuseStep 4223323 = 6334985) B6334985
theorem B22524389 : Blo 2193435 22524389 := bstep (se 4 (by rfl) ⟨2111661, by rfl⟩ : syracuseStep 22524389 = 4223323) B4223323
theorem B15016259 : Blo 2193435 15016259 := bstep (se 1 (by rfl) ⟨11262194, by rfl⟩ : syracuseStep 15016259 = 22524389) B22524389
theorem B10010839 : Blo 2193435 10010839 := bstep (se 1 (by rfl) ⟨7508129, by rfl⟩ : syracuseStep 10010839 = 15016259) B15016259
theorem B13347785 : Blo 2193435 13347785 := bstep (se 2 (by rfl) ⟨5005419, by rfl⟩ : syracuseStep 13347785 = 10010839) B10010839
theorem B35594093 : Blo 2193435 35594093 := bstep (se 3 (by rfl) ⟨6673892, by rfl⟩ : syracuseStep 35594093 = 13347785) B13347785
theorem B23729395 : Blo 2193435 23729395 := bstep (se 1 (by rfl) ⟨17797046, by rfl⟩ : syracuseStep 23729395 = 35594093) B35594093
theorem B31639193 : Blo 2193435 31639193 := bstep (se 2 (by rfl) ⟨11864697, by rfl⟩ : syracuseStep 31639193 = 23729395) B23729395
theorem B21092795 : Blo 2193435 21092795 := bstep (se 1 (by rfl) ⟨15819596, by rfl⟩ : syracuseStep 21092795 = 31639193) B31639193
theorem B14061863 : Blo 2193435 14061863 := bstep (se 1 (by rfl) ⟨10546397, by rfl⟩ : syracuseStep 14061863 = 21092795) B21092795
theorem B37498301 : Blo 2193435 37498301 := bstep (se 3 (by rfl) ⟨7030931, by rfl⟩ : syracuseStep 37498301 = 14061863) B14061863
theorem B24998867 : Blo 2193435 24998867 := bstep (se 1 (by rfl) ⟨18749150, by rfl⟩ : syracuseStep 24998867 = 37498301) B37498301
theorem B16665911 : Blo 2193435 16665911 := bstep (se 1 (by rfl) ⟨12499433, by rfl⟩ : syracuseStep 16665911 = 24998867) B24998867
theorem B11110607 : Blo 2193435 11110607 := bstep (se 1 (by rfl) ⟨8332955, by rfl⟩ : syracuseStep 11110607 = 16665911) B16665911
theorem B7407071 : Blo 2193435 7407071 := bstep (se 1 (by rfl) ⟨5555303, by rfl⟩ : syracuseStep 7407071 = 11110607) B11110607
theorem B4938047 : Blo 2193435 4938047 := bstep (se 1 (by rfl) ⟨3703535, by rfl⟩ : syracuseStep 4938047 = 7407071) B7407071
theorem B3292031 : Blo 2193435 3292031 := bstep (se 1 (by rfl) ⟨2469023, by rfl⟩ : syracuseStep 3292031 = 4938047) B4938047
theorem B2194687 : Blo 2193435 2194687 := bstep (se 1 (by rfl) ⟨1646015, by rfl⟩ : syracuseStep 2194687 = 3292031) B3292031
theorem B3292037 : Blo 2193435 3292037 := bbase (se 4 (by rfl) ⟨308628, by rfl⟩ : syracuseStep 3292037 = 617257) (by norm_num)
theorem B2194691 : Blo 2193435 2194691 := bstep (se 1 (by rfl) ⟨1646018, by rfl⟩ : syracuseStep 2194691 = 3292037) B3292037
theorem B3703549 : Blo 2193435 3703549 := bbase (se 3 (by rfl) ⟨694415, by rfl⟩ : syracuseStep 3703549 = 1388831) (by norm_num)
theorem B4938065 : Blo 2193435 4938065 := bstep (se 2 (by rfl) ⟨1851774, by rfl⟩ : syracuseStep 4938065 = 3703549) B3703549
theorem B3292043 : Blo 2193435 3292043 := bstep (se 1 (by rfl) ⟨2469032, by rfl⟩ : syracuseStep 3292043 = 4938065) B4938065
theorem B2194695 : Blo 2193435 2194695 := bstep (se 1 (by rfl) ⟨1646021, by rfl⟩ : syracuseStep 2194695 = 3292043) B3292043
theorem B2469037 : Blo 2193435 2469037 := bbase (se 3 (by rfl) ⟨462944, by rfl⟩ : syracuseStep 2469037 = 925889) (by norm_num)
theorem B3292049 : Blo 2193435 3292049 := bstep (se 2 (by rfl) ⟨1234518, by rfl⟩ : syracuseStep 3292049 = 2469037) B2469037
theorem B2194699 : Blo 2193435 2194699 := bstep (se 1 (by rfl) ⟨1646024, by rfl⟩ : syracuseStep 2194699 = 3292049) B3292049
theorem B7407125 : Blo 2193435 7407125 := bbase (se 6 (by rfl) ⟨173604, by rfl⟩ : syracuseStep 7407125 = 347209) (by norm_num)
theorem B4938083 : Blo 2193435 4938083 := bstep (se 1 (by rfl) ⟨3703562, by rfl⟩ : syracuseStep 4938083 = 7407125) B7407125
theorem B3292055 : Blo 2193435 3292055 := bstep (se 1 (by rfl) ⟨2469041, by rfl⟩ : syracuseStep 3292055 = 4938083) B4938083
theorem B2194703 : Blo 2193435 2194703 := bstep (se 1 (by rfl) ⟨1646027, by rfl⟩ : syracuseStep 2194703 = 3292055) B3292055
theorem B3292061 : Blo 2193435 3292061 := bbase (se 3 (by rfl) ⟨617261, by rfl⟩ : syracuseStep 3292061 = 1234523) (by norm_num)
theorem B2194707 : Blo 2193435 2194707 := bstep (se 1 (by rfl) ⟨1646030, by rfl⟩ : syracuseStep 2194707 = 3292061) B3292061
theorem B4938101 : Blo 2193435 4938101 := bbase (se 5 (by rfl) ⟨231473, by rfl⟩ : syracuseStep 4938101 = 462947) (by norm_num)
theorem B3292067 : Blo 2193435 3292067 := bstep (se 1 (by rfl) ⟨2469050, by rfl⟩ : syracuseStep 3292067 = 4938101) B4938101
theorem B2194711 : Blo 2193435 2194711 := bstep (se 1 (by rfl) ⟨1646033, by rfl⟩ : syracuseStep 2194711 = 3292067) B3292067
theorem B2966213 : Blo 2193435 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B7909901 : Blo 2193435 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B5273267 : Blo 2193435 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B14062045 : Blo 2193435 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B18749393 : Blo 2193435 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B12499595 : Blo 2193435 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B8333063 : Blo 2193435 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B5555375 : Blo 2193435 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B3703583 : Blo 2193435 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B2469055 : Blo 2193435 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B3292073 : Blo 2193435 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B2194715 : Blo 2193435 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B8333077 : Blo 2193435 8333077 := bbase (se 6 (by rfl) ⟨195306, by rfl⟩ : syracuseStep 8333077 = 390613) (by norm_num)
theorem B11110769 : Blo 2193435 11110769 := bstep (se 2 (by rfl) ⟨4166538, by rfl⟩ : syracuseStep 11110769 = 8333077) B8333077
theorem B7407179 : Blo 2193435 7407179 := bstep (se 1 (by rfl) ⟨5555384, by rfl⟩ : syracuseStep 7407179 = 11110769) B11110769
theorem B4938119 : Blo 2193435 4938119 := bstep (se 1 (by rfl) ⟨3703589, by rfl⟩ : syracuseStep 4938119 = 7407179) B7407179
theorem B3292079 : Blo 2193435 3292079 := bstep (se 1 (by rfl) ⟨2469059, by rfl⟩ : syracuseStep 3292079 = 4938119) B4938119
theorem B2194719 : Blo 2193435 2194719 := bstep (se 1 (by rfl) ⟨1646039, by rfl⟩ : syracuseStep 2194719 = 3292079) B3292079
theorem B3292085 : Blo 2193435 3292085 := bbase (se 5 (by rfl) ⟨154316, by rfl⟩ : syracuseStep 3292085 = 308633) (by norm_num)
theorem B2194723 : Blo 2193435 2194723 := bstep (se 1 (by rfl) ⟨1646042, by rfl⟩ : syracuseStep 2194723 = 3292085) B3292085
theorem B5555405 : Blo 2193435 5555405 := bbase (se 3 (by rfl) ⟨1041638, by rfl⟩ : syracuseStep 5555405 = 2083277) (by norm_num)
theorem B3703603 : Blo 2193435 3703603 := bstep (se 1 (by rfl) ⟨2777702, by rfl⟩ : syracuseStep 3703603 = 5555405) B5555405
theorem B4938137 : Blo 2193435 4938137 := bstep (se 2 (by rfl) ⟨1851801, by rfl⟩ : syracuseStep 4938137 = 3703603) B3703603
theorem B3292091 : Blo 2193435 3292091 := bstep (se 1 (by rfl) ⟨2469068, by rfl⟩ : syracuseStep 3292091 = 4938137) B4938137
theorem B2194727 : Blo 2193435 2194727 := bstep (se 1 (by rfl) ⟨1646045, by rfl⟩ : syracuseStep 2194727 = 3292091) B3292091
theorem B2469073 : Blo 2193435 2469073 := bbase (se 2 (by rfl) ⟨925902, by rfl⟩ : syracuseStep 2469073 = 1851805) (by norm_num)
theorem B3292097 : Blo 2193435 3292097 := bstep (se 2 (by rfl) ⟨1234536, by rfl⟩ : syracuseStep 3292097 = 2469073) B2469073
theorem B2194731 : Blo 2193435 2194731 := bstep (se 1 (by rfl) ⟨1646048, by rfl⟩ : syracuseStep 2194731 = 3292097) B3292097
theorem B10011061 : Blo 2193435 10011061 := bbase (se 5 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 10011061 = 938537) (by norm_num)
theorem B13348081 : Blo 2193435 13348081 := bstep (se 2 (by rfl) ⟨5005530, by rfl⟩ : syracuseStep 13348081 = 10011061) B10011061
theorem B17797441 : Blo 2193435 17797441 := bstep (se 2 (by rfl) ⟨6674040, by rfl⟩ : syracuseStep 17797441 = 13348081) B13348081
theorem B23729921 : Blo 2193435 23729921 := bstep (se 2 (by rfl) ⟨8898720, by rfl⟩ : syracuseStep 23729921 = 17797441) B17797441
theorem B15819947 : Blo 2193435 15819947 := bstep (se 1 (by rfl) ⟨11864960, by rfl⟩ : syracuseStep 15819947 = 23729921) B23729921
theorem B10546631 : Blo 2193435 10546631 := bstep (se 1 (by rfl) ⟨7909973, by rfl⟩ : syracuseStep 10546631 = 15819947) B15819947
theorem B7031087 : Blo 2193435 7031087 := bstep (se 1 (by rfl) ⟨5273315, by rfl⟩ : syracuseStep 7031087 = 10546631) B10546631
theorem B4687391 : Blo 2193435 4687391 := bstep (se 1 (by rfl) ⟨3515543, by rfl⟩ : syracuseStep 4687391 = 7031087) B7031087
theorem B3124927 : Blo 2193435 3124927 := bstep (se 1 (by rfl) ⟨2343695, by rfl⟩ : syracuseStep 3124927 = 4687391) B4687391
theorem B4166569 : Blo 2193435 4166569 := bstep (se 2 (by rfl) ⟨1562463, by rfl⟩ : syracuseStep 4166569 = 3124927) B3124927
theorem B5555425 : Blo 2193435 5555425 := bstep (se 2 (by rfl) ⟨2083284, by rfl⟩ : syracuseStep 5555425 = 4166569) B4166569
theorem B7407233 : Blo 2193435 7407233 := bstep (se 2 (by rfl) ⟨2777712, by rfl⟩ : syracuseStep 7407233 = 5555425) B5555425
theorem B4938155 : Blo 2193435 4938155 := bstep (se 1 (by rfl) ⟨3703616, by rfl⟩ : syracuseStep 4938155 = 7407233) B7407233
theorem B3292103 : Blo 2193435 3292103 := bstep (se 1 (by rfl) ⟨2469077, by rfl⟩ : syracuseStep 3292103 = 4938155) B4938155
theorem B2194735 : Blo 2193435 2194735 := bstep (se 1 (by rfl) ⟨1646051, by rfl⟩ : syracuseStep 2194735 = 3292103) B3292103
theorem B3292109 : Blo 2193435 3292109 := bbase (se 3 (by rfl) ⟨617270, by rfl⟩ : syracuseStep 3292109 = 1234541) (by norm_num)
theorem B2194739 : Blo 2193435 2194739 := bstep (se 1 (by rfl) ⟨1646054, by rfl⟩ : syracuseStep 2194739 = 3292109) B3292109
theorem B4938173 : Blo 2193435 4938173 := bbase (se 3 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 4938173 = 1851815) (by norm_num)
theorem B3292115 : Blo 2193435 3292115 := bstep (se 1 (by rfl) ⟨2469086, by rfl⟩ : syracuseStep 3292115 = 4938173) B4938173
theorem B2194743 : Blo 2193435 2194743 := bstep (se 1 (by rfl) ⟨1646057, by rfl⟩ : syracuseStep 2194743 = 3292115) B3292115
theorem B3703637 : Blo 2193435 3703637 := bbase (se 9 (by rfl) ⟨10850, by rfl⟩ : syracuseStep 3703637 = 21701) (by norm_num)
theorem B2469091 : Blo 2193435 2469091 := bstep (se 1 (by rfl) ⟨1851818, by rfl⟩ : syracuseStep 2469091 = 3703637) B3703637
theorem B3292121 : Blo 2193435 3292121 := bstep (se 2 (by rfl) ⟨1234545, by rfl⟩ : syracuseStep 3292121 = 2469091) B2469091
theorem B2194747 : Blo 2193435 2194747 := bstep (se 1 (by rfl) ⟨1646060, by rfl⟩ : syracuseStep 2194747 = 3292121) B3292121
theorem B85524821 : Blo 2193435 85524821 := bbase (se 10 (by rfl) ⟨125280, by rfl⟩ : syracuseStep 85524821 = 250561) (by norm_num)
theorem B57016547 : Blo 2193435 57016547 := bstep (se 1 (by rfl) ⟨42762410, by rfl⟩ : syracuseStep 57016547 = 85524821) B85524821
theorem B38011031 : Blo 2193435 38011031 := bstep (se 1 (by rfl) ⟨28508273, by rfl⟩ : syracuseStep 38011031 = 57016547) B57016547
theorem B25340687 : Blo 2193435 25340687 := bstep (se 1 (by rfl) ⟨19005515, by rfl⟩ : syracuseStep 25340687 = 38011031) B38011031
theorem B16893791 : Blo 2193435 16893791 := bstep (se 1 (by rfl) ⟨12670343, by rfl⟩ : syracuseStep 16893791 = 25340687) B25340687
theorem B11262527 : Blo 2193435 11262527 := bstep (se 1 (by rfl) ⟨8446895, by rfl⟩ : syracuseStep 11262527 = 16893791) B16893791
theorem B7508351 : Blo 2193435 7508351 := bstep (se 1 (by rfl) ⟨5631263, by rfl⟩ : syracuseStep 7508351 = 11262527) B11262527
theorem B5005567 : Blo 2193435 5005567 := bstep (se 1 (by rfl) ⟨3754175, by rfl⟩ : syracuseStep 5005567 = 7508351) B7508351
theorem B6674089 : Blo 2193435 6674089 := bstep (se 2 (by rfl) ⟨2502783, by rfl⟩ : syracuseStep 6674089 = 5005567) B5005567
theorem B8898785 : Blo 2193435 8898785 := bstep (se 2 (by rfl) ⟨3337044, by rfl⟩ : syracuseStep 8898785 = 6674089) B6674089
theorem B5932523 : Blo 2193435 5932523 := bstep (se 1 (by rfl) ⟨4449392, by rfl⟩ : syracuseStep 5932523 = 8898785) B8898785
theorem B3955015 : Blo 2193435 3955015 := bstep (se 1 (by rfl) ⟨2966261, by rfl⟩ : syracuseStep 3955015 = 5932523) B5932523
theorem B5273353 : Blo 2193435 5273353 := bstep (se 2 (by rfl) ⟨1977507, by rfl⟩ : syracuseStep 5273353 = 3955015) B3955015
theorem B7031137 : Blo 2193435 7031137 := bstep (se 2 (by rfl) ⟨2636676, by rfl⟩ : syracuseStep 7031137 = 5273353) B5273353
theorem B9374849 : Blo 2193435 9374849 := bstep (se 2 (by rfl) ⟨3515568, by rfl⟩ : syracuseStep 9374849 = 7031137) B7031137
theorem B6249899 : Blo 2193435 6249899 := bstep (se 1 (by rfl) ⟨4687424, by rfl⟩ : syracuseStep 6249899 = 9374849) B9374849
theorem B16666397 : Blo 2193435 16666397 := bstep (se 3 (by rfl) ⟨3124949, by rfl⟩ : syracuseStep 16666397 = 6249899) B6249899
theorem B11110931 : Blo 2193435 11110931 := bstep (se 1 (by rfl) ⟨8333198, by rfl⟩ : syracuseStep 11110931 = 16666397) B16666397
theorem B7407287 : Blo 2193435 7407287 := bstep (se 1 (by rfl) ⟨5555465, by rfl⟩ : syracuseStep 7407287 = 11110931) B11110931
theorem B4938191 : Blo 2193435 4938191 := bstep (se 1 (by rfl) ⟨3703643, by rfl⟩ : syracuseStep 4938191 = 7407287) B7407287
theorem B3292127 : Blo 2193435 3292127 := bstep (se 1 (by rfl) ⟨2469095, by rfl⟩ : syracuseStep 3292127 = 4938191) B4938191
theorem B2194751 : Blo 2193435 2194751 := bstep (se 1 (by rfl) ⟨1646063, by rfl⟩ : syracuseStep 2194751 = 3292127) B3292127
theorem B3292133 : Blo 2193435 3292133 := bbase (se 4 (by rfl) ⟨308637, by rfl⟩ : syracuseStep 3292133 = 617275) (by norm_num)
theorem B2194755 : Blo 2193435 2194755 := bstep (se 1 (by rfl) ⟨1646066, by rfl⟩ : syracuseStep 2194755 = 3292133) B3292133
theorem B9374885 : Blo 2193435 9374885 := bbase (se 4 (by rfl) ⟨878895, by rfl⟩ : syracuseStep 9374885 = 1757791) (by norm_num)
theorem B6249923 : Blo 2193435 6249923 := bstep (se 1 (by rfl) ⟨4687442, by rfl⟩ : syracuseStep 6249923 = 9374885) B9374885
theorem B4166615 : Blo 2193435 4166615 := bstep (se 1 (by rfl) ⟨3124961, by rfl⟩ : syracuseStep 4166615 = 6249923) B6249923
theorem B2777743 : Blo 2193435 2777743 := bstep (se 1 (by rfl) ⟨2083307, by rfl⟩ : syracuseStep 2777743 = 4166615) B4166615
theorem B3703657 : Blo 2193435 3703657 := bstep (se 2 (by rfl) ⟨1388871, by rfl⟩ : syracuseStep 3703657 = 2777743) B2777743
theorem B4938209 : Blo 2193435 4938209 := bstep (se 2 (by rfl) ⟨1851828, by rfl⟩ : syracuseStep 4938209 = 3703657) B3703657
theorem B3292139 : Blo 2193435 3292139 := bstep (se 1 (by rfl) ⟨2469104, by rfl⟩ : syracuseStep 3292139 = 4938209) B4938209
theorem B2194759 : Blo 2193435 2194759 := bstep (se 1 (by rfl) ⟨1646069, by rfl⟩ : syracuseStep 2194759 = 3292139) B3292139
theorem B2469109 : Blo 2193435 2469109 := bbase (se 5 (by rfl) ⟨115739, by rfl⟩ : syracuseStep 2469109 = 231479) (by norm_num)
theorem B3292145 : Blo 2193435 3292145 := bstep (se 2 (by rfl) ⟨1234554, by rfl⟩ : syracuseStep 3292145 = 2469109) B2469109
theorem B2194763 : Blo 2193435 2194763 := bstep (se 1 (by rfl) ⟨1646072, by rfl⟩ : syracuseStep 2194763 = 3292145) B3292145
theorem B2777753 : Blo 2193435 2777753 := bbase (se 2 (by rfl) ⟨1041657, by rfl⟩ : syracuseStep 2777753 = 2083315) (by norm_num)
theorem B7407341 : Blo 2193435 7407341 := bstep (se 3 (by rfl) ⟨1388876, by rfl⟩ : syracuseStep 7407341 = 2777753) B2777753
theorem B4938227 : Blo 2193435 4938227 := bstep (se 1 (by rfl) ⟨3703670, by rfl⟩ : syracuseStep 4938227 = 7407341) B7407341
theorem B3292151 : Blo 2193435 3292151 := bstep (se 1 (by rfl) ⟨2469113, by rfl⟩ : syracuseStep 3292151 = 4938227) B4938227
theorem B2194767 : Blo 2193435 2194767 := bstep (se 1 (by rfl) ⟨1646075, by rfl⟩ : syracuseStep 2194767 = 3292151) B3292151
theorem B3292157 : Blo 2193435 3292157 := bbase (se 3 (by rfl) ⟨617279, by rfl⟩ : syracuseStep 3292157 = 1234559) (by norm_num)
theorem B2194771 : Blo 2193435 2194771 := bstep (se 1 (by rfl) ⟨1646078, by rfl⟩ : syracuseStep 2194771 = 3292157) B3292157
theorem B4938245 : Blo 2193435 4938245 := bbase (se 4 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 4938245 = 925921) (by norm_num)
theorem B3292163 : Blo 2193435 3292163 := bstep (se 1 (by rfl) ⟨2469122, by rfl⟩ : syracuseStep 3292163 = 4938245) B4938245
theorem B2194775 : Blo 2193435 2194775 := bstep (se 1 (by rfl) ⟨1646081, by rfl⟩ : syracuseStep 2194775 = 3292163) B3292163
theorem B4166653 : Blo 2193435 4166653 := bbase (se 3 (by rfl) ⟨781247, by rfl⟩ : syracuseStep 4166653 = 1562495) (by norm_num)
theorem B5555537 : Blo 2193435 5555537 := bstep (se 2 (by rfl) ⟨2083326, by rfl⟩ : syracuseStep 5555537 = 4166653) B4166653
theorem B3703691 : Blo 2193435 3703691 := bstep (se 1 (by rfl) ⟨2777768, by rfl⟩ : syracuseStep 3703691 = 5555537) B5555537
theorem B2469127 : Blo 2193435 2469127 := bstep (se 1 (by rfl) ⟨1851845, by rfl⟩ : syracuseStep 2469127 = 3703691) B3703691
theorem B3292169 : Blo 2193435 3292169 := bstep (se 2 (by rfl) ⟨1234563, by rfl⟩ : syracuseStep 3292169 = 2469127) B2469127
theorem B2194779 : Blo 2193435 2194779 := bstep (se 1 (by rfl) ⟨1646084, by rfl⟩ : syracuseStep 2194779 = 3292169) B3292169
theorem B11111093 : Blo 2193435 11111093 := bbase (se 5 (by rfl) ⟨520832, by rfl⟩ : syracuseStep 11111093 = 1041665) (by norm_num)
theorem B7407395 : Blo 2193435 7407395 := bstep (se 1 (by rfl) ⟨5555546, by rfl⟩ : syracuseStep 7407395 = 11111093) B11111093
theorem B4938263 : Blo 2193435 4938263 := bstep (se 1 (by rfl) ⟨3703697, by rfl⟩ : syracuseStep 4938263 = 7407395) B7407395
theorem B3292175 : Blo 2193435 3292175 := bstep (se 1 (by rfl) ⟨2469131, by rfl⟩ : syracuseStep 3292175 = 4938263) B4938263
theorem B2194783 : Blo 2193435 2194783 := bstep (se 1 (by rfl) ⟨1646087, by rfl⟩ : syracuseStep 2194783 = 3292175) B3292175
theorem B3292181 : Blo 2193435 3292181 := bbase (se 6 (by rfl) ⟨77160, by rfl⟩ : syracuseStep 3292181 = 154321) (by norm_num)
theorem B2194787 : Blo 2193435 2194787 := bstep (se 1 (by rfl) ⟨1646090, by rfl⟩ : syracuseStep 2194787 = 3292181) B3292181
theorem B2502829 : Blo 2193435 2502829 := bbase (se 3 (by rfl) ⟨469280, by rfl⟩ : syracuseStep 2502829 = 938561) (by norm_num)
theorem B13348421 : Blo 2193435 13348421 := bstep (se 4 (by rfl) ⟨1251414, by rfl⟩ : syracuseStep 13348421 = 2502829) B2502829
theorem B8898947 : Blo 2193435 8898947 := bstep (se 1 (by rfl) ⟨6674210, by rfl⟩ : syracuseStep 8898947 = 13348421) B13348421
theorem B5932631 : Blo 2193435 5932631 := bstep (se 1 (by rfl) ⟨4449473, by rfl⟩ : syracuseStep 5932631 = 8898947) B8898947
theorem B3955087 : Blo 2193435 3955087 := bstep (se 1 (by rfl) ⟨2966315, by rfl⟩ : syracuseStep 3955087 = 5932631) B5932631
theorem B21093797 : Blo 2193435 21093797 := bstep (se 4 (by rfl) ⟨1977543, by rfl⟩ : syracuseStep 21093797 = 3955087) B3955087
theorem B14062531 : Blo 2193435 14062531 := bstep (se 1 (by rfl) ⟨10546898, by rfl⟩ : syracuseStep 14062531 = 21093797) B21093797
theorem B18750041 : Blo 2193435 18750041 := bstep (se 2 (by rfl) ⟨7031265, by rfl⟩ : syracuseStep 18750041 = 14062531) B14062531
theorem B12500027 : Blo 2193435 12500027 := bstep (se 1 (by rfl) ⟨9375020, by rfl⟩ : syracuseStep 12500027 = 18750041) B18750041
theorem B8333351 : Blo 2193435 8333351 := bstep (se 1 (by rfl) ⟨6250013, by rfl⟩ : syracuseStep 8333351 = 12500027) B12500027
theorem B5555567 : Blo 2193435 5555567 := bstep (se 1 (by rfl) ⟨4166675, by rfl⟩ : syracuseStep 5555567 = 8333351) B8333351
theorem B3703711 : Blo 2193435 3703711 := bstep (se 1 (by rfl) ⟨2777783, by rfl⟩ : syracuseStep 3703711 = 5555567) B5555567
theorem B4938281 : Blo 2193435 4938281 := bstep (se 2 (by rfl) ⟨1851855, by rfl⟩ : syracuseStep 4938281 = 3703711) B3703711
theorem B3292187 : Blo 2193435 3292187 := bstep (se 1 (by rfl) ⟨2469140, by rfl⟩ : syracuseStep 3292187 = 4938281) B4938281
theorem B2194791 : Blo 2193435 2194791 := bstep (se 1 (by rfl) ⟨1646093, by rfl⟩ : syracuseStep 2194791 = 3292187) B3292187
theorem B2469145 : Blo 2193435 2469145 := bbase (se 2 (by rfl) ⟨925929, by rfl⟩ : syracuseStep 2469145 = 1851859) (by norm_num)
theorem B3292193 : Blo 2193435 3292193 := bstep (se 2 (by rfl) ⟨1234572, by rfl⟩ : syracuseStep 3292193 = 2469145) B2469145
theorem B2194795 : Blo 2193435 2194795 := bstep (se 1 (by rfl) ⟨1646096, by rfl⟩ : syracuseStep 2194795 = 3292193) B3292193
theorem B8333381 : Blo 2193435 8333381 := bbase (se 4 (by rfl) ⟨781254, by rfl⟩ : syracuseStep 8333381 = 1562509) (by norm_num)
theorem B5555587 : Blo 2193435 5555587 := bstep (se 1 (by rfl) ⟨4166690, by rfl⟩ : syracuseStep 5555587 = 8333381) B8333381
theorem B7407449 : Blo 2193435 7407449 := bstep (se 2 (by rfl) ⟨2777793, by rfl⟩ : syracuseStep 7407449 = 5555587) B5555587
theorem B4938299 : Blo 2193435 4938299 := bstep (se 1 (by rfl) ⟨3703724, by rfl⟩ : syracuseStep 4938299 = 7407449) B7407449
theorem B3292199 : Blo 2193435 3292199 := bstep (se 1 (by rfl) ⟨2469149, by rfl⟩ : syracuseStep 3292199 = 4938299) B4938299
theorem B2194799 : Blo 2193435 2194799 := bstep (se 1 (by rfl) ⟨1646099, by rfl⟩ : syracuseStep 2194799 = 3292199) B3292199
theorem B3292205 : Blo 2193435 3292205 := bbase (se 3 (by rfl) ⟨617288, by rfl⟩ : syracuseStep 3292205 = 1234577) (by norm_num)
theorem B2194803 : Blo 2193435 2194803 := bstep (se 1 (by rfl) ⟨1646102, by rfl⟩ : syracuseStep 2194803 = 3292205) B3292205
theorem B4938317 : Blo 2193435 4938317 := bbase (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) (by norm_num)
theorem B3292211 : Blo 2193435 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B2194807 : Blo 2193435 2194807 := bstep (se 1 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 2194807 = 3292211) B3292211
theorem B2777809 : Blo 2193435 2777809 := bbase (se 2 (by rfl) ⟨1041678, by rfl⟩ : syracuseStep 2777809 = 2083357) (by norm_num)
theorem B3703745 : Blo 2193435 3703745 := bstep (se 2 (by rfl) ⟨1388904, by rfl⟩ : syracuseStep 3703745 = 2777809) B2777809
theorem B2469163 : Blo 2193435 2469163 := bstep (se 1 (by rfl) ⟨1851872, by rfl⟩ : syracuseStep 2469163 = 3703745) B3703745
theorem B3292217 : Blo 2193435 3292217 := bstep (se 2 (by rfl) ⟨1234581, by rfl⟩ : syracuseStep 3292217 = 2469163) B2469163
theorem B2194811 : Blo 2193435 2194811 := bstep (se 1 (by rfl) ⟨1646108, by rfl⟩ : syracuseStep 2194811 = 3292217) B3292217
theorem B7910261 : Blo 2193435 7910261 := bbase (se 5 (by rfl) ⟨370793, by rfl⟩ : syracuseStep 7910261 = 741587) (by norm_num)
theorem B5273507 : Blo 2193435 5273507 := bstep (se 1 (by rfl) ⟨3955130, by rfl⟩ : syracuseStep 5273507 = 7910261) B7910261
theorem B3515671 : Blo 2193435 3515671 := bstep (se 1 (by rfl) ⟨2636753, by rfl⟩ : syracuseStep 3515671 = 5273507) B5273507
theorem B4687561 : Blo 2193435 4687561 := bstep (se 2 (by rfl) ⟨1757835, by rfl⟩ : syracuseStep 4687561 = 3515671) B3515671
theorem B25000325 : Blo 2193435 25000325 := bstep (se 4 (by rfl) ⟨2343780, by rfl⟩ : syracuseStep 25000325 = 4687561) B4687561
theorem B16666883 : Blo 2193435 16666883 := bstep (se 1 (by rfl) ⟨12500162, by rfl⟩ : syracuseStep 16666883 = 25000325) B25000325
theorem B11111255 : Blo 2193435 11111255 := bstep (se 1 (by rfl) ⟨8333441, by rfl⟩ : syracuseStep 11111255 = 16666883) B16666883
theorem B7407503 : Blo 2193435 7407503 := bstep (se 1 (by rfl) ⟨5555627, by rfl⟩ : syracuseStep 7407503 = 11111255) B11111255
theorem B4938335 : Blo 2193435 4938335 := bstep (se 1 (by rfl) ⟨3703751, by rfl⟩ : syracuseStep 4938335 = 7407503) B7407503
theorem B3292223 : Blo 2193435 3292223 := bstep (se 1 (by rfl) ⟨2469167, by rfl⟩ : syracuseStep 3292223 = 4938335) B4938335
theorem B2194815 : Blo 2193435 2194815 := bstep (se 1 (by rfl) ⟨1646111, by rfl⟩ : syracuseStep 2194815 = 3292223) B3292223
theorem B3292229 : Blo 2193435 3292229 := bbase (se 4 (by rfl) ⟨308646, by rfl⟩ : syracuseStep 3292229 = 617293) (by norm_num)
theorem B2194819 : Blo 2193435 2194819 := bstep (se 1 (by rfl) ⟨1646114, by rfl⟩ : syracuseStep 2194819 = 3292229) B3292229
theorem B3703765 : Blo 2193435 3703765 := bbase (se 7 (by rfl) ⟨43403, by rfl⟩ : syracuseStep 3703765 = 86807) (by norm_num)
theorem B4938353 : Blo 2193435 4938353 := bstep (se 2 (by rfl) ⟨1851882, by rfl⟩ : syracuseStep 4938353 = 3703765) B3703765
theorem B3292235 : Blo 2193435 3292235 := bstep (se 1 (by rfl) ⟨2469176, by rfl⟩ : syracuseStep 3292235 = 4938353) B4938353
theorem B2194823 : Blo 2193435 2194823 := bstep (se 1 (by rfl) ⟨1646117, by rfl⟩ : syracuseStep 2194823 = 3292235) B3292235
theorem B2469181 : Blo 2193435 2469181 := bbase (se 3 (by rfl) ⟨462971, by rfl⟩ : syracuseStep 2469181 = 925943) (by norm_num)
theorem B3292241 : Blo 2193435 3292241 := bstep (se 2 (by rfl) ⟨1234590, by rfl⟩ : syracuseStep 3292241 = 2469181) B2469181
theorem B2194827 : Blo 2193435 2194827 := bstep (se 1 (by rfl) ⟨1646120, by rfl⟩ : syracuseStep 2194827 = 3292241) B3292241
theorem B7407557 : Blo 2193435 7407557 := bbase (se 4 (by rfl) ⟨694458, by rfl⟩ : syracuseStep 7407557 = 1388917) (by norm_num)
theorem B4938371 : Blo 2193435 4938371 := bstep (se 1 (by rfl) ⟨3703778, by rfl⟩ : syracuseStep 4938371 = 7407557) B7407557
theorem B3292247 : Blo 2193435 3292247 := bstep (se 1 (by rfl) ⟨2469185, by rfl⟩ : syracuseStep 3292247 = 4938371) B4938371
theorem B2194831 : Blo 2193435 2194831 := bstep (se 1 (by rfl) ⟨1646123, by rfl⟩ : syracuseStep 2194831 = 3292247) B3292247
theorem B3292253 : Blo 2193435 3292253 := bbase (se 3 (by rfl) ⟨617297, by rfl⟩ : syracuseStep 3292253 = 1234595) (by norm_num)
theorem B2194835 : Blo 2193435 2194835 := bstep (se 1 (by rfl) ⟨1646126, by rfl⟩ : syracuseStep 2194835 = 3292253) B3292253
theorem B4938389 : Blo 2193435 4938389 := bbase (se 6 (by rfl) ⟨115743, by rfl⟩ : syracuseStep 4938389 = 231487) (by norm_num)
theorem B3292259 : Blo 2193435 3292259 := bstep (se 1 (by rfl) ⟨2469194, by rfl⟩ : syracuseStep 3292259 = 4938389) B4938389
theorem B2194839 : Blo 2193435 2194839 := bstep (se 1 (by rfl) ⟨1646129, by rfl⟩ : syracuseStep 2194839 = 3292259) B3292259
theorem B3515717 : Blo 2193435 3515717 := bbase (se 4 (by rfl) ⟨329598, by rfl⟩ : syracuseStep 3515717 = 659197) (by norm_num)
theorem B2343811 : Blo 2193435 2343811 := bstep (se 1 (by rfl) ⟨1757858, by rfl⟩ : syracuseStep 2343811 = 3515717) B3515717
theorem B3125081 : Blo 2193435 3125081 := bstep (se 2 (by rfl) ⟨1171905, by rfl⟩ : syracuseStep 3125081 = 2343811) B2343811
theorem B8333549 : Blo 2193435 8333549 := bstep (se 3 (by rfl) ⟨1562540, by rfl⟩ : syracuseStep 8333549 = 3125081) B3125081
theorem B5555699 : Blo 2193435 5555699 := bstep (se 1 (by rfl) ⟨4166774, by rfl⟩ : syracuseStep 5555699 = 8333549) B8333549
theorem B3703799 : Blo 2193435 3703799 := bstep (se 1 (by rfl) ⟨2777849, by rfl⟩ : syracuseStep 3703799 = 5555699) B5555699
theorem B2469199 : Blo 2193435 2469199 := bstep (se 1 (by rfl) ⟨1851899, by rfl⟩ : syracuseStep 2469199 = 3703799) B3703799
theorem B3292265 : Blo 2193435 3292265 := bstep (se 2 (by rfl) ⟨1234599, by rfl⟩ : syracuseStep 3292265 = 2469199) B2469199
theorem B2194843 : Blo 2193435 2194843 := bstep (se 1 (by rfl) ⟨1646132, by rfl⟩ : syracuseStep 2194843 = 3292265) B3292265
theorem B30034709 : Blo 2193435 30034709 := bbase (se 6 (by rfl) ⟨703938, by rfl⟩ : syracuseStep 30034709 = 1407877) (by norm_num)
theorem B20023139 : Blo 2193435 20023139 := bstep (se 1 (by rfl) ⟨15017354, by rfl⟩ : syracuseStep 20023139 = 30034709) B30034709
theorem B53395037 : Blo 2193435 53395037 := bstep (se 3 (by rfl) ⟨10011569, by rfl⟩ : syracuseStep 53395037 = 20023139) B20023139
theorem B35596691 : Blo 2193435 35596691 := bstep (se 1 (by rfl) ⟨26697518, by rfl⟩ : syracuseStep 35596691 = 53395037) B53395037
theorem B23731127 : Blo 2193435 23731127 := bstep (se 1 (by rfl) ⟨17798345, by rfl⟩ : syracuseStep 23731127 = 35596691) B35596691
theorem B15820751 : Blo 2193435 15820751 := bstep (se 1 (by rfl) ⟨11865563, by rfl⟩ : syracuseStep 15820751 = 23731127) B23731127
theorem B10547167 : Blo 2193435 10547167 := bstep (se 1 (by rfl) ⟨7910375, by rfl⟩ : syracuseStep 10547167 = 15820751) B15820751
theorem B14062889 : Blo 2193435 14062889 := bstep (se 2 (by rfl) ⟨5273583, by rfl⟩ : syracuseStep 14062889 = 10547167) B10547167
theorem B9375259 : Blo 2193435 9375259 := bstep (se 1 (by rfl) ⟨7031444, by rfl⟩ : syracuseStep 9375259 = 14062889) B14062889
theorem B12500345 : Blo 2193435 12500345 := bstep (se 2 (by rfl) ⟨4687629, by rfl⟩ : syracuseStep 12500345 = 9375259) B9375259
theorem B8333563 : Blo 2193435 8333563 := bstep (se 1 (by rfl) ⟨6250172, by rfl⟩ : syracuseStep 8333563 = 12500345) B12500345
theorem B11111417 : Blo 2193435 11111417 := bstep (se 2 (by rfl) ⟨4166781, by rfl⟩ : syracuseStep 11111417 = 8333563) B8333563
theorem B7407611 : Blo 2193435 7407611 := bstep (se 1 (by rfl) ⟨5555708, by rfl⟩ : syracuseStep 7407611 = 11111417) B11111417
theorem B4938407 : Blo 2193435 4938407 := bstep (se 1 (by rfl) ⟨3703805, by rfl⟩ : syracuseStep 4938407 = 7407611) B7407611
theorem B3292271 : Blo 2193435 3292271 := bstep (se 1 (by rfl) ⟨2469203, by rfl⟩ : syracuseStep 3292271 = 4938407) B4938407
theorem B2194847 : Blo 2193435 2194847 := bstep (se 1 (by rfl) ⟨1646135, by rfl⟩ : syracuseStep 2194847 = 3292271) B3292271
theorem B3292277 : Blo 2193435 3292277 := bbase (se 5 (by rfl) ⟨154325, by rfl⟩ : syracuseStep 3292277 = 308651) (by norm_num)
theorem B2194851 : Blo 2193435 2194851 := bstep (se 1 (by rfl) ⟨1646138, by rfl⟩ : syracuseStep 2194851 = 3292277) B3292277
theorem B4166797 : Blo 2193435 4166797 := bbase (se 3 (by rfl) ⟨781274, by rfl⟩ : syracuseStep 4166797 = 1562549) (by norm_num)
theorem B5555729 : Blo 2193435 5555729 := bstep (se 2 (by rfl) ⟨2083398, by rfl⟩ : syracuseStep 5555729 = 4166797) B4166797
theorem B3703819 : Blo 2193435 3703819 := bstep (se 1 (by rfl) ⟨2777864, by rfl⟩ : syracuseStep 3703819 = 5555729) B5555729
theorem B4938425 : Blo 2193435 4938425 := bstep (se 2 (by rfl) ⟨1851909, by rfl⟩ : syracuseStep 4938425 = 3703819) B3703819
theorem B3292283 : Blo 2193435 3292283 := bstep (se 1 (by rfl) ⟨2469212, by rfl⟩ : syracuseStep 3292283 = 4938425) B4938425
theorem B2194855 : Blo 2193435 2194855 := bstep (se 1 (by rfl) ⟨1646141, by rfl⟩ : syracuseStep 2194855 = 3292283) B3292283
theorem B2469217 : Blo 2193435 2469217 := bbase (se 2 (by rfl) ⟨925956, by rfl⟩ : syracuseStep 2469217 = 1851913) (by norm_num)
theorem B3292289 : Blo 2193435 3292289 := bstep (se 2 (by rfl) ⟨1234608, by rfl⟩ : syracuseStep 3292289 = 2469217) B2469217
theorem B2194859 : Blo 2193435 2194859 := bstep (se 1 (by rfl) ⟨1646144, by rfl⟩ : syracuseStep 2194859 = 3292289) B3292289
theorem B5555749 : Blo 2193435 5555749 := bbase (se 4 (by rfl) ⟨520851, by rfl⟩ : syracuseStep 5555749 = 1041703) (by norm_num)
theorem B7407665 : Blo 2193435 7407665 := bstep (se 2 (by rfl) ⟨2777874, by rfl⟩ : syracuseStep 7407665 = 5555749) B5555749
theorem B4938443 : Blo 2193435 4938443 := bstep (se 1 (by rfl) ⟨3703832, by rfl⟩ : syracuseStep 4938443 = 7407665) B7407665
theorem B3292295 : Blo 2193435 3292295 := bstep (se 1 (by rfl) ⟨2469221, by rfl⟩ : syracuseStep 3292295 = 4938443) B4938443
theorem B2194863 : Blo 2193435 2194863 := bstep (se 1 (by rfl) ⟨1646147, by rfl⟩ : syracuseStep 2194863 = 3292295) B3292295
theorem B3292301 : Blo 2193435 3292301 := bbase (se 3 (by rfl) ⟨617306, by rfl⟩ : syracuseStep 3292301 = 1234613) (by norm_num)
theorem B2194867 : Blo 2193435 2194867 := bstep (se 1 (by rfl) ⟨1646150, by rfl⟩ : syracuseStep 2194867 = 3292301) B3292301
theorem B4938461 : Blo 2193435 4938461 := bbase (se 3 (by rfl) ⟨925961, by rfl⟩ : syracuseStep 4938461 = 1851923) (by norm_num)
theorem B3292307 : Blo 2193435 3292307 := bstep (se 1 (by rfl) ⟨2469230, by rfl⟩ : syracuseStep 3292307 = 4938461) B4938461
theorem B2194871 : Blo 2193435 2194871 := bstep (se 1 (by rfl) ⟨1646153, by rfl⟩ : syracuseStep 2194871 = 3292307) B3292307
theorem B3703853 : Blo 2193435 3703853 := bbase (se 3 (by rfl) ⟨694472, by rfl⟩ : syracuseStep 3703853 = 1388945) (by norm_num)
theorem B2469235 : Blo 2193435 2469235 := bstep (se 1 (by rfl) ⟨1851926, by rfl⟩ : syracuseStep 2469235 = 3703853) B3703853
theorem B3292313 : Blo 2193435 3292313 := bstep (se 2 (by rfl) ⟨1234617, by rfl⟩ : syracuseStep 3292313 = 2469235) B2469235
theorem B2194875 : Blo 2193435 2194875 := bstep (se 1 (by rfl) ⟨1646156, by rfl⟩ : syracuseStep 2194875 = 3292313) B3292313
theorem B4223693 : Blo 2193435 4223693 := bbase (se 3 (by rfl) ⟨791942, by rfl⟩ : syracuseStep 4223693 = 1583885) (by norm_num)
theorem B2815795 : Blo 2193435 2815795 := bstep (se 1 (by rfl) ⟨2111846, by rfl⟩ : syracuseStep 2815795 = 4223693) B4223693
theorem B3754393 : Blo 2193435 3754393 := bstep (se 2 (by rfl) ⟨1407897, by rfl⟩ : syracuseStep 3754393 = 2815795) B2815795
theorem B80093717 : Blo 2193435 80093717 := bstep (se 6 (by rfl) ⟨1877196, by rfl⟩ : syracuseStep 80093717 = 3754393) B3754393
theorem B53395811 : Blo 2193435 53395811 := bstep (se 1 (by rfl) ⟨40046858, by rfl⟩ : syracuseStep 53395811 = 80093717) B80093717
theorem B35597207 : Blo 2193435 35597207 := bstep (se 1 (by rfl) ⟨26697905, by rfl⟩ : syracuseStep 35597207 = 53395811) B53395811
theorem B23731471 : Blo 2193435 23731471 := bstep (se 1 (by rfl) ⟨17798603, by rfl⟩ : syracuseStep 23731471 = 35597207) B35597207
theorem B31641961 : Blo 2193435 31641961 := bstep (se 2 (by rfl) ⟨11865735, by rfl⟩ : syracuseStep 31641961 = 23731471) B23731471
theorem B42189281 : Blo 2193435 42189281 := bstep (se 2 (by rfl) ⟨15820980, by rfl⟩ : syracuseStep 42189281 = 31641961) B31641961
theorem B28126187 : Blo 2193435 28126187 := bstep (se 1 (by rfl) ⟨21094640, by rfl⟩ : syracuseStep 28126187 = 42189281) B42189281
theorem B18750791 : Blo 2193435 18750791 := bstep (se 1 (by rfl) ⟨14063093, by rfl⟩ : syracuseStep 18750791 = 28126187) B28126187
theorem B12500527 : Blo 2193435 12500527 := bstep (se 1 (by rfl) ⟨9375395, by rfl⟩ : syracuseStep 12500527 = 18750791) B18750791
theorem B16667369 : Blo 2193435 16667369 := bstep (se 2 (by rfl) ⟨6250263, by rfl⟩ : syracuseStep 16667369 = 12500527) B12500527
theorem B11111579 : Blo 2193435 11111579 := bstep (se 1 (by rfl) ⟨8333684, by rfl⟩ : syracuseStep 11111579 = 16667369) B16667369
theorem B7407719 : Blo 2193435 7407719 := bstep (se 1 (by rfl) ⟨5555789, by rfl⟩ : syracuseStep 7407719 = 11111579) B11111579
theorem B4938479 : Blo 2193435 4938479 := bstep (se 1 (by rfl) ⟨3703859, by rfl⟩ : syracuseStep 4938479 = 7407719) B7407719
theorem B3292319 : Blo 2193435 3292319 := bstep (se 1 (by rfl) ⟨2469239, by rfl⟩ : syracuseStep 3292319 = 4938479) B4938479
theorem B2194879 : Blo 2193435 2194879 := bstep (se 1 (by rfl) ⟨1646159, by rfl⟩ : syracuseStep 2194879 = 3292319) B3292319
theorem B3292325 : Blo 2193435 3292325 := bbase (se 4 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 3292325 = 617311) (by norm_num)
theorem B2194883 : Blo 2193435 2194883 := bstep (se 1 (by rfl) ⟨1646162, by rfl⟩ : syracuseStep 2194883 = 3292325) B3292325
theorem B2777905 : Blo 2193435 2777905 := bbase (se 2 (by rfl) ⟨1041714, by rfl⟩ : syracuseStep 2777905 = 2083429) (by norm_num)
theorem B3703873 : Blo 2193435 3703873 := bstep (se 2 (by rfl) ⟨1388952, by rfl⟩ : syracuseStep 3703873 = 2777905) B2777905
theorem B4938497 : Blo 2193435 4938497 := bstep (se 2 (by rfl) ⟨1851936, by rfl⟩ : syracuseStep 4938497 = 3703873) B3703873
theorem B3292331 : Blo 2193435 3292331 := bstep (se 1 (by rfl) ⟨2469248, by rfl⟩ : syracuseStep 3292331 = 4938497) B4938497
theorem B2194887 : Blo 2193435 2194887 := bstep (se 1 (by rfl) ⟨1646165, by rfl⟩ : syracuseStep 2194887 = 3292331) B3292331
theorem B2469253 : Blo 2193435 2469253 := bbase (se 4 (by rfl) ⟨231492, by rfl⟩ : syracuseStep 2469253 = 462985) (by norm_num)
theorem B3292337 : Blo 2193435 3292337 := bstep (se 2 (by rfl) ⟨1234626, by rfl⟩ : syracuseStep 3292337 = 2469253) B2469253
theorem B2194891 : Blo 2193435 2194891 := bstep (se 1 (by rfl) ⟨1646168, by rfl⟩ : syracuseStep 2194891 = 3292337) B3292337
theorem B4687733 : Blo 2193435 4687733 := bbase (se 5 (by rfl) ⟨219737, by rfl⟩ : syracuseStep 4687733 = 439475) (by norm_num)
theorem B3125155 : Blo 2193435 3125155 := bstep (se 1 (by rfl) ⟨2343866, by rfl⟩ : syracuseStep 3125155 = 4687733) B4687733
theorem B4166873 : Blo 2193435 4166873 := bstep (se 2 (by rfl) ⟨1562577, by rfl⟩ : syracuseStep 4166873 = 3125155) B3125155
theorem B2777915 : Blo 2193435 2777915 := bstep (se 1 (by rfl) ⟨2083436, by rfl⟩ : syracuseStep 2777915 = 4166873) B4166873
theorem B7407773 : Blo 2193435 7407773 := bstep (se 3 (by rfl) ⟨1388957, by rfl⟩ : syracuseStep 7407773 = 2777915) B2777915
theorem B4938515 : Blo 2193435 4938515 := bstep (se 1 (by rfl) ⟨3703886, by rfl⟩ : syracuseStep 4938515 = 7407773) B7407773
theorem B3292343 : Blo 2193435 3292343 := bstep (se 1 (by rfl) ⟨2469257, by rfl⟩ : syracuseStep 3292343 = 4938515) B4938515
theorem B2194895 : Blo 2193435 2194895 := bstep (se 1 (by rfl) ⟨1646171, by rfl⟩ : syracuseStep 2194895 = 3292343) B3292343
theorem B3292349 : Blo 2193435 3292349 := bbase (se 3 (by rfl) ⟨617315, by rfl⟩ : syracuseStep 3292349 = 1234631) (by norm_num)
theorem B2194899 : Blo 2193435 2194899 := bstep (se 1 (by rfl) ⟨1646174, by rfl⟩ : syracuseStep 2194899 = 3292349) B3292349
theorem B4938533 : Blo 2193435 4938533 := bbase (se 4 (by rfl) ⟨462987, by rfl⟩ : syracuseStep 4938533 = 925975) (by norm_num)
theorem B3292355 : Blo 2193435 3292355 := bstep (se 1 (by rfl) ⟨2469266, by rfl⟩ : syracuseStep 3292355 = 4938533) B4938533
theorem B2194903 : Blo 2193435 2194903 := bstep (se 1 (by rfl) ⟨1646177, by rfl⟩ : syracuseStep 2194903 = 3292355) B3292355
theorem B5555861 : Blo 2193435 5555861 := bbase (se 6 (by rfl) ⟨130215, by rfl⟩ : syracuseStep 5555861 = 260431) (by norm_num)
theorem B3703907 : Blo 2193435 3703907 := bstep (se 1 (by rfl) ⟨2777930, by rfl⟩ : syracuseStep 3703907 = 5555861) B5555861
theorem B2469271 : Blo 2193435 2469271 := bstep (se 1 (by rfl) ⟨1851953, by rfl⟩ : syracuseStep 2469271 = 3703907) B3703907
theorem B3292361 : Blo 2193435 3292361 := bstep (se 2 (by rfl) ⟨1234635, by rfl⟩ : syracuseStep 3292361 = 2469271) B2469271
theorem B2194907 : Blo 2193435 2194907 := bstep (se 1 (by rfl) ⟨1646180, by rfl⟩ : syracuseStep 2194907 = 3292361) B3292361
theorem B2636869 : Blo 2193435 2636869 := bbase (se 4 (by rfl) ⟨247206, by rfl⟩ : syracuseStep 2636869 = 494413) (by norm_num)
theorem B3515825 : Blo 2193435 3515825 := bstep (se 2 (by rfl) ⟨1318434, by rfl⟩ : syracuseStep 3515825 = 2636869) B2636869
theorem B9375533 : Blo 2193435 9375533 := bstep (se 3 (by rfl) ⟨1757912, by rfl⟩ : syracuseStep 9375533 = 3515825) B3515825
theorem B6250355 : Blo 2193435 6250355 := bstep (se 1 (by rfl) ⟨4687766, by rfl⟩ : syracuseStep 6250355 = 9375533) B9375533
theorem B4166903 : Blo 2193435 4166903 := bstep (se 1 (by rfl) ⟨3125177, by rfl⟩ : syracuseStep 4166903 = 6250355) B6250355
theorem B11111741 : Blo 2193435 11111741 := bstep (se 3 (by rfl) ⟨2083451, by rfl⟩ : syracuseStep 11111741 = 4166903) B4166903
theorem B7407827 : Blo 2193435 7407827 := bstep (se 1 (by rfl) ⟨5555870, by rfl⟩ : syracuseStep 7407827 = 11111741) B11111741
theorem B4938551 : Blo 2193435 4938551 := bstep (se 1 (by rfl) ⟨3703913, by rfl⟩ : syracuseStep 4938551 = 7407827) B7407827
theorem B3292367 : Blo 2193435 3292367 := bstep (se 1 (by rfl) ⟨2469275, by rfl⟩ : syracuseStep 3292367 = 4938551) B4938551
theorem B2194911 : Blo 2193435 2194911 := bstep (se 1 (by rfl) ⟨1646183, by rfl⟩ : syracuseStep 2194911 = 3292367) B3292367
theorem B3292373 : Blo 2193435 3292373 := bbase (se 7 (by rfl) ⟨38582, by rfl⟩ : syracuseStep 3292373 = 77165) (by norm_num)
theorem B2194915 : Blo 2193435 2194915 := bstep (se 1 (by rfl) ⟨1646186, by rfl⟩ : syracuseStep 2194915 = 3292373) B3292373
theorem B3125189 : Blo 2193435 3125189 := bbase (se 4 (by rfl) ⟨292986, by rfl⟩ : syracuseStep 3125189 = 585973) (by norm_num)
theorem B8333837 : Blo 2193435 8333837 := bstep (se 3 (by rfl) ⟨1562594, by rfl⟩ : syracuseStep 8333837 = 3125189) B3125189
theorem B5555891 : Blo 2193435 5555891 := bstep (se 1 (by rfl) ⟨4166918, by rfl⟩ : syracuseStep 5555891 = 8333837) B8333837
theorem B3703927 : Blo 2193435 3703927 := bstep (se 1 (by rfl) ⟨2777945, by rfl⟩ : syracuseStep 3703927 = 5555891) B5555891
theorem B4938569 : Blo 2193435 4938569 := bstep (se 2 (by rfl) ⟨1851963, by rfl⟩ : syracuseStep 4938569 = 3703927) B3703927
theorem B3292379 : Blo 2193435 3292379 := bstep (se 1 (by rfl) ⟨2469284, by rfl⟩ : syracuseStep 3292379 = 4938569) B4938569
theorem B2194919 : Blo 2193435 2194919 := bstep (se 1 (by rfl) ⟨1646189, by rfl⟩ : syracuseStep 2194919 = 3292379) B3292379
theorem B2469289 : Blo 2193435 2469289 := bbase (se 2 (by rfl) ⟨925983, by rfl⟩ : syracuseStep 2469289 = 1851967) (by norm_num)
theorem B3292385 : Blo 2193435 3292385 := bstep (se 2 (by rfl) ⟨1234644, by rfl⟩ : syracuseStep 3292385 = 2469289) B2469289
theorem B2194923 : Blo 2193435 2194923 := bstep (se 1 (by rfl) ⟨1646192, by rfl⟩ : syracuseStep 2194923 = 3292385) B3292385
theorem B7031701 : Blo 2193435 7031701 := bbase (se 6 (by rfl) ⟨164805, by rfl⟩ : syracuseStep 7031701 = 329611) (by norm_num)
theorem B9375601 : Blo 2193435 9375601 := bstep (se 2 (by rfl) ⟨3515850, by rfl⟩ : syracuseStep 9375601 = 7031701) B7031701
theorem B12500801 : Blo 2193435 12500801 := bstep (se 2 (by rfl) ⟨4687800, by rfl⟩ : syracuseStep 12500801 = 9375601) B9375601
theorem B8333867 : Blo 2193435 8333867 := bstep (se 1 (by rfl) ⟨6250400, by rfl⟩ : syracuseStep 8333867 = 12500801) B12500801
theorem B5555911 : Blo 2193435 5555911 := bstep (se 1 (by rfl) ⟨4166933, by rfl⟩ : syracuseStep 5555911 = 8333867) B8333867
theorem B7407881 : Blo 2193435 7407881 := bstep (se 2 (by rfl) ⟨2777955, by rfl⟩ : syracuseStep 7407881 = 5555911) B5555911
theorem B4938587 : Blo 2193435 4938587 := bstep (se 1 (by rfl) ⟨3703940, by rfl⟩ : syracuseStep 4938587 = 7407881) B7407881
theorem B3292391 : Blo 2193435 3292391 := bstep (se 1 (by rfl) ⟨2469293, by rfl⟩ : syracuseStep 3292391 = 4938587) B4938587
theorem B2194927 : Blo 2193435 2194927 := bstep (se 1 (by rfl) ⟨1646195, by rfl⟩ : syracuseStep 2194927 = 3292391) B3292391
theorem B3292397 : Blo 2193435 3292397 := bbase (se 3 (by rfl) ⟨617324, by rfl⟩ : syracuseStep 3292397 = 1234649) (by norm_num)
theorem B2194931 : Blo 2193435 2194931 := bstep (se 1 (by rfl) ⟨1646198, by rfl⟩ : syracuseStep 2194931 = 3292397) B3292397
theorem B4938605 : Blo 2193435 4938605 := bbase (se 3 (by rfl) ⟨925988, by rfl⟩ : syracuseStep 4938605 = 1851977) (by norm_num)
theorem B3292403 : Blo 2193435 3292403 := bstep (se 1 (by rfl) ⟨2469302, by rfl⟩ : syracuseStep 3292403 = 4938605) B4938605
theorem B2194935 : Blo 2193435 2194935 := bstep (se 1 (by rfl) ⟨1646201, by rfl⟩ : syracuseStep 2194935 = 3292403) B3292403
theorem B4166957 : Blo 2193435 4166957 := bbase (se 3 (by rfl) ⟨781304, by rfl⟩ : syracuseStep 4166957 = 1562609) (by norm_num)
theorem B2777971 : Blo 2193435 2777971 := bstep (se 1 (by rfl) ⟨2083478, by rfl⟩ : syracuseStep 2777971 = 4166957) B4166957
theorem B3703961 : Blo 2193435 3703961 := bstep (se 2 (by rfl) ⟨1388985, by rfl⟩ : syracuseStep 3703961 = 2777971) B2777971
theorem B2469307 : Blo 2193435 2469307 := bstep (se 1 (by rfl) ⟨1851980, by rfl⟩ : syracuseStep 2469307 = 3703961) B3703961
theorem B3292409 : Blo 2193435 3292409 := bstep (se 2 (by rfl) ⟨1234653, by rfl⟩ : syracuseStep 3292409 = 2469307) B2469307
theorem B2194939 : Blo 2193435 2194939 := bstep (se 1 (by rfl) ⟨1646204, by rfl⟩ : syracuseStep 2194939 = 3292409) B3292409
theorem B64149205 : Blo 2193435 64149205 := bbase (se 7 (by rfl) ⟨751748, by rfl⟩ : syracuseStep 64149205 = 1503497) (by norm_num)
theorem B85532273 : Blo 2193435 85532273 := bstep (se 2 (by rfl) ⟨32074602, by rfl⟩ : syracuseStep 85532273 = 64149205) B64149205
theorem B57021515 : Blo 2193435 57021515 := bstep (se 1 (by rfl) ⟨42766136, by rfl⟩ : syracuseStep 57021515 = 85532273) B85532273
theorem B38014343 : Blo 2193435 38014343 := bstep (se 1 (by rfl) ⟨28510757, by rfl⟩ : syracuseStep 38014343 = 57021515) B57021515
theorem B25342895 : Blo 2193435 25342895 := bstep (se 1 (by rfl) ⟨19007171, by rfl⟩ : syracuseStep 25342895 = 38014343) B38014343
theorem B16895263 : Blo 2193435 16895263 := bstep (se 1 (by rfl) ⟨12671447, by rfl⟩ : syracuseStep 16895263 = 25342895) B25342895
theorem B22527017 : Blo 2193435 22527017 := bstep (se 2 (by rfl) ⟨8447631, by rfl⟩ : syracuseStep 22527017 = 16895263) B16895263
theorem B15018011 : Blo 2193435 15018011 := bstep (se 1 (by rfl) ⟨11263508, by rfl⟩ : syracuseStep 15018011 = 22527017) B22527017
theorem B10012007 : Blo 2193435 10012007 := bstep (se 1 (by rfl) ⟨7509005, by rfl⟩ : syracuseStep 10012007 = 15018011) B15018011
theorem B6674671 : Blo 2193435 6674671 := bstep (se 1 (by rfl) ⟨5006003, by rfl⟩ : syracuseStep 6674671 = 10012007) B10012007
theorem B8899561 : Blo 2193435 8899561 := bstep (se 2 (by rfl) ⟨3337335, by rfl⟩ : syracuseStep 8899561 = 6674671) B6674671
theorem B47464325 : Blo 2193435 47464325 := bstep (se 4 (by rfl) ⟨4449780, by rfl⟩ : syracuseStep 47464325 = 8899561) B8899561
theorem B31642883 : Blo 2193435 31642883 := bstep (se 1 (by rfl) ⟨23732162, by rfl⟩ : syracuseStep 31642883 = 47464325) B47464325
theorem B21095255 : Blo 2193435 21095255 := bstep (se 1 (by rfl) ⟨15821441, by rfl⟩ : syracuseStep 21095255 = 31642883) B31642883
theorem B56254013 : Blo 2193435 56254013 := bstep (se 3 (by rfl) ⟨10547627, by rfl⟩ : syracuseStep 56254013 = 21095255) B21095255
theorem B37502675 : Blo 2193435 37502675 := bstep (se 1 (by rfl) ⟨28127006, by rfl⟩ : syracuseStep 37502675 = 56254013) B56254013
theorem B25001783 : Blo 2193435 25001783 := bstep (se 1 (by rfl) ⟨18751337, by rfl⟩ : syracuseStep 25001783 = 37502675) B37502675
theorem B16667855 : Blo 2193435 16667855 := bstep (se 1 (by rfl) ⟨12500891, by rfl⟩ : syracuseStep 16667855 = 25001783) B25001783
theorem B11111903 : Blo 2193435 11111903 := bstep (se 1 (by rfl) ⟨8333927, by rfl⟩ : syracuseStep 11111903 = 16667855) B16667855
theorem B7407935 : Blo 2193435 7407935 := bstep (se 1 (by rfl) ⟨5555951, by rfl⟩ : syracuseStep 7407935 = 11111903) B11111903
theorem B4938623 : Blo 2193435 4938623 := bstep (se 1 (by rfl) ⟨3703967, by rfl⟩ : syracuseStep 4938623 = 7407935) B7407935
theorem B3292415 : Blo 2193435 3292415 := bstep (se 1 (by rfl) ⟨2469311, by rfl⟩ : syracuseStep 3292415 = 4938623) B4938623
theorem B2194943 : Blo 2193435 2194943 := bstep (se 1 (by rfl) ⟨1646207, by rfl⟩ : syracuseStep 2194943 = 3292415) B3292415
theorem B3292421 : Blo 2193435 3292421 := bbase (se 4 (by rfl) ⟨308664, by rfl⟩ : syracuseStep 3292421 = 617329) (by norm_num)
theorem B2194947 : Blo 2193435 2194947 := bstep (se 1 (by rfl) ⟨1646210, by rfl⟩ : syracuseStep 2194947 = 3292421) B3292421
theorem B3703981 : Blo 2193435 3703981 := bbase (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) (by norm_num)
theorem B4938641 : Blo 2193435 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B3292427 : Blo 2193435 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B2194951 : Blo 2193435 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B2469325 : Blo 2193435 2469325 := bbase (se 3 (by rfl) ⟨462998, by rfl⟩ : syracuseStep 2469325 = 925997) (by norm_num)
theorem B3292433 : Blo 2193435 3292433 := bstep (se 2 (by rfl) ⟨1234662, by rfl⟩ : syracuseStep 3292433 = 2469325) B2469325
theorem B2194955 : Blo 2193435 2194955 := bstep (se 1 (by rfl) ⟨1646216, by rfl⟩ : syracuseStep 2194955 = 3292433) B3292433
theorem B7407989 : Blo 2193435 7407989 := bbase (se 5 (by rfl) ⟨347249, by rfl⟩ : syracuseStep 7407989 = 694499) (by norm_num)
theorem B4938659 : Blo 2193435 4938659 := bstep (se 1 (by rfl) ⟨3703994, by rfl⟩ : syracuseStep 4938659 = 7407989) B7407989
theorem B3292439 : Blo 2193435 3292439 := bstep (se 1 (by rfl) ⟨2469329, by rfl⟩ : syracuseStep 3292439 = 4938659) B4938659
theorem B2194959 : Blo 2193435 2194959 := bstep (se 1 (by rfl) ⟨1646219, by rfl⟩ : syracuseStep 2194959 = 3292439) B3292439
theorem B3292445 : Blo 2193435 3292445 := bbase (se 3 (by rfl) ⟨617333, by rfl⟩ : syracuseStep 3292445 = 1234667) (by norm_num)
theorem B2194963 : Blo 2193435 2194963 := bstep (se 1 (by rfl) ⟨1646222, by rfl⟩ : syracuseStep 2194963 = 3292445) B3292445
theorem B4938677 : Blo 2193435 4938677 := bbase (se 5 (by rfl) ⟨231500, by rfl⟩ : syracuseStep 4938677 = 463001) (by norm_num)
theorem B3292451 : Blo 2193435 3292451 := bstep (se 1 (by rfl) ⟨2469338, by rfl⟩ : syracuseStep 3292451 = 4938677) B4938677
theorem B2194967 : Blo 2193435 2194967 := bstep (se 1 (by rfl) ⟨1646225, by rfl⟩ : syracuseStep 2194967 = 3292451) B3292451
theorem B10547765 : Blo 2193435 10547765 := bbase (se 5 (by rfl) ⟨494426, by rfl⟩ : syracuseStep 10547765 = 988853) (by norm_num)
theorem B7031843 : Blo 2193435 7031843 := bstep (se 1 (by rfl) ⟨5273882, by rfl⟩ : syracuseStep 7031843 = 10547765) B10547765
theorem B4687895 : Blo 2193435 4687895 := bstep (se 1 (by rfl) ⟨3515921, by rfl⟩ : syracuseStep 4687895 = 7031843) B7031843
theorem B12501053 : Blo 2193435 12501053 := bstep (se 3 (by rfl) ⟨2343947, by rfl⟩ : syracuseStep 12501053 = 4687895) B4687895
theorem B8334035 : Blo 2193435 8334035 := bstep (se 1 (by rfl) ⟨6250526, by rfl⟩ : syracuseStep 8334035 = 12501053) B12501053
theorem B5556023 : Blo 2193435 5556023 := bstep (se 1 (by rfl) ⟨4167017, by rfl⟩ : syracuseStep 5556023 = 8334035) B8334035
theorem B3704015 : Blo 2193435 3704015 := bstep (se 1 (by rfl) ⟨2778011, by rfl⟩ : syracuseStep 3704015 = 5556023) B5556023
theorem B2469343 : Blo 2193435 2469343 := bstep (se 1 (by rfl) ⟨1852007, by rfl⟩ : syracuseStep 2469343 = 3704015) B3704015
theorem B3292457 : Blo 2193435 3292457 := bstep (se 2 (by rfl) ⟨1234671, by rfl⟩ : syracuseStep 3292457 = 2469343) B2469343
theorem B2194971 : Blo 2193435 2194971 := bstep (se 1 (by rfl) ⟨1646228, by rfl⟩ : syracuseStep 2194971 = 3292457) B3292457
theorem B20024309 : Blo 2193435 20024309 := bbase (se 5 (by rfl) ⟨938639, by rfl⟩ : syracuseStep 20024309 = 1877279) (by norm_num)
theorem B13349539 : Blo 2193435 13349539 := bstep (se 1 (by rfl) ⟨10012154, by rfl⟩ : syracuseStep 13349539 = 20024309) B20024309
theorem B17799385 : Blo 2193435 17799385 := bstep (se 2 (by rfl) ⟨6674769, by rfl⟩ : syracuseStep 17799385 = 13349539) B13349539
theorem B23732513 : Blo 2193435 23732513 := bstep (se 2 (by rfl) ⟨8899692, by rfl⟩ : syracuseStep 23732513 = 17799385) B17799385
theorem B15821675 : Blo 2193435 15821675 := bstep (se 1 (by rfl) ⟨11866256, by rfl⟩ : syracuseStep 15821675 = 23732513) B23732513
theorem B10547783 : Blo 2193435 10547783 := bstep (se 1 (by rfl) ⟨7910837, by rfl⟩ : syracuseStep 10547783 = 15821675) B15821675
theorem B7031855 : Blo 2193435 7031855 := bstep (se 1 (by rfl) ⟨5273891, by rfl⟩ : syracuseStep 7031855 = 10547783) B10547783
theorem B4687903 : Blo 2193435 4687903 := bstep (se 1 (by rfl) ⟨3515927, by rfl⟩ : syracuseStep 4687903 = 7031855) B7031855
theorem B6250537 : Blo 2193435 6250537 := bstep (se 2 (by rfl) ⟨2343951, by rfl⟩ : syracuseStep 6250537 = 4687903) B4687903
theorem B8334049 : Blo 2193435 8334049 := bstep (se 2 (by rfl) ⟨3125268, by rfl⟩ : syracuseStep 8334049 = 6250537) B6250537
theorem B11112065 : Blo 2193435 11112065 := bstep (se 2 (by rfl) ⟨4167024, by rfl⟩ : syracuseStep 11112065 = 8334049) B8334049
theorem B7408043 : Blo 2193435 7408043 := bstep (se 1 (by rfl) ⟨5556032, by rfl⟩ : syracuseStep 7408043 = 11112065) B11112065
theorem B4938695 : Blo 2193435 4938695 := bstep (se 1 (by rfl) ⟨3704021, by rfl⟩ : syracuseStep 4938695 = 7408043) B7408043
theorem B3292463 : Blo 2193435 3292463 := bstep (se 1 (by rfl) ⟨2469347, by rfl⟩ : syracuseStep 3292463 = 4938695) B4938695
theorem B2194975 : Blo 2193435 2194975 := bstep (se 1 (by rfl) ⟨1646231, by rfl⟩ : syracuseStep 2194975 = 3292463) B3292463
theorem B3292469 : Blo 2193435 3292469 := bbase (se 5 (by rfl) ⟨154334, by rfl⟩ : syracuseStep 3292469 = 308669) (by norm_num)
theorem B2194979 : Blo 2193435 2194979 := bstep (se 1 (by rfl) ⟨1646234, by rfl⟩ : syracuseStep 2194979 = 3292469) B3292469
theorem B5556053 : Blo 2193435 5556053 := bbase (se 9 (by rfl) ⟨16277, by rfl⟩ : syracuseStep 5556053 = 32555) (by norm_num)
theorem B3704035 : Blo 2193435 3704035 := bstep (se 1 (by rfl) ⟨2778026, by rfl⟩ : syracuseStep 3704035 = 5556053) B5556053
theorem B4938713 : Blo 2193435 4938713 := bstep (se 2 (by rfl) ⟨1852017, by rfl⟩ : syracuseStep 4938713 = 3704035) B3704035
theorem B3292475 : Blo 2193435 3292475 := bstep (se 1 (by rfl) ⟨2469356, by rfl⟩ : syracuseStep 3292475 = 4938713) B4938713
theorem B2194983 : Blo 2193435 2194983 := bstep (se 1 (by rfl) ⟨1646237, by rfl⟩ : syracuseStep 2194983 = 3292475) B3292475
theorem B2469361 : Blo 2193435 2469361 := bbase (se 2 (by rfl) ⟨926010, by rfl⟩ : syracuseStep 2469361 = 1852021) (by norm_num)
theorem B3292481 : Blo 2193435 3292481 := bstep (se 2 (by rfl) ⟨1234680, by rfl⟩ : syracuseStep 3292481 = 2469361) B2469361
theorem B2194987 : Blo 2193435 2194987 := bstep (se 1 (by rfl) ⟨1646240, by rfl⟩ : syracuseStep 2194987 = 3292481) B3292481
theorem B2636965 : Blo 2193435 2636965 := bbase (se 4 (by rfl) ⟨247215, by rfl⟩ : syracuseStep 2636965 = 494431) (by norm_num)
theorem B14063813 : Blo 2193435 14063813 := bstep (se 4 (by rfl) ⟨1318482, by rfl⟩ : syracuseStep 14063813 = 2636965) B2636965
theorem B9375875 : Blo 2193435 9375875 := bstep (se 1 (by rfl) ⟨7031906, by rfl⟩ : syracuseStep 9375875 = 14063813) B14063813
theorem B6250583 : Blo 2193435 6250583 := bstep (se 1 (by rfl) ⟨4687937, by rfl⟩ : syracuseStep 6250583 = 9375875) B9375875
theorem B4167055 : Blo 2193435 4167055 := bstep (se 1 (by rfl) ⟨3125291, by rfl⟩ : syracuseStep 4167055 = 6250583) B6250583
theorem B5556073 : Blo 2193435 5556073 := bstep (se 2 (by rfl) ⟨2083527, by rfl⟩ : syracuseStep 5556073 = 4167055) B4167055
theorem B7408097 : Blo 2193435 7408097 := bstep (se 2 (by rfl) ⟨2778036, by rfl⟩ : syracuseStep 7408097 = 5556073) B5556073
theorem B4938731 : Blo 2193435 4938731 := bstep (se 1 (by rfl) ⟨3704048, by rfl⟩ : syracuseStep 4938731 = 7408097) B7408097
theorem B3292487 : Blo 2193435 3292487 := bstep (se 1 (by rfl) ⟨2469365, by rfl⟩ : syracuseStep 3292487 = 4938731) B4938731
theorem B2194991 : Blo 2193435 2194991 := bstep (se 1 (by rfl) ⟨1646243, by rfl⟩ : syracuseStep 2194991 = 3292487) B3292487
theorem B3292493 : Blo 2193435 3292493 := bbase (se 3 (by rfl) ⟨617342, by rfl⟩ : syracuseStep 3292493 = 1234685) (by norm_num)
theorem B2194995 : Blo 2193435 2194995 := bstep (se 1 (by rfl) ⟨1646246, by rfl⟩ : syracuseStep 2194995 = 3292493) B3292493
theorem B4938749 : Blo 2193435 4938749 := bbase (se 3 (by rfl) ⟨926015, by rfl⟩ : syracuseStep 4938749 = 1852031) (by norm_num)
theorem B3292499 : Blo 2193435 3292499 := bstep (se 1 (by rfl) ⟨2469374, by rfl⟩ : syracuseStep 3292499 = 4938749) B4938749
theorem B2194999 : Blo 2193435 2194999 := bstep (se 1 (by rfl) ⟨1646249, by rfl⟩ : syracuseStep 2194999 = 3292499) B3292499
theorem B3704069 : Blo 2193435 3704069 := bbase (se 4 (by rfl) ⟨347256, by rfl⟩ : syracuseStep 3704069 = 694513) (by norm_num)
theorem B2469379 : Blo 2193435 2469379 := bstep (se 1 (by rfl) ⟨1852034, by rfl⟩ : syracuseStep 2469379 = 3704069) B3704069
theorem B3292505 : Blo 2193435 3292505 := bstep (se 2 (by rfl) ⟨1234689, by rfl⟩ : syracuseStep 3292505 = 2469379) B2469379
theorem B2195003 : Blo 2193435 2195003 := bstep (se 1 (by rfl) ⟨1646252, by rfl⟩ : syracuseStep 2195003 = 3292505) B3292505
theorem B16668341 : Blo 2193435 16668341 := bbase (se 5 (by rfl) ⟨781328, by rfl⟩ : syracuseStep 16668341 = 1562657) (by norm_num)
theorem B11112227 : Blo 2193435 11112227 := bstep (se 1 (by rfl) ⟨8334170, by rfl⟩ : syracuseStep 11112227 = 16668341) B16668341
theorem B7408151 : Blo 2193435 7408151 := bstep (se 1 (by rfl) ⟨5556113, by rfl⟩ : syracuseStep 7408151 = 11112227) B11112227
theorem B4938767 : Blo 2193435 4938767 := bstep (se 1 (by rfl) ⟨3704075, by rfl⟩ : syracuseStep 4938767 = 7408151) B7408151
theorem B3292511 : Blo 2193435 3292511 := bstep (se 1 (by rfl) ⟨2469383, by rfl⟩ : syracuseStep 3292511 = 4938767) B4938767
theorem B2195007 : Blo 2193435 2195007 := bstep (se 1 (by rfl) ⟨1646255, by rfl⟩ : syracuseStep 2195007 = 3292511) B3292511
theorem B3292517 : Blo 2193435 3292517 := bbase (se 4 (by rfl) ⟨308673, by rfl⟩ : syracuseStep 3292517 = 617347) (by norm_num)
theorem B2195011 : Blo 2193435 2195011 := bstep (se 1 (by rfl) ⟨1646258, by rfl⟩ : syracuseStep 2195011 = 3292517) B3292517
theorem B4167101 : Blo 2193435 4167101 := bbase (se 3 (by rfl) ⟨781331, by rfl⟩ : syracuseStep 4167101 = 1562663) (by norm_num)
theorem B2778067 : Blo 2193435 2778067 := bstep (se 1 (by rfl) ⟨2083550, by rfl⟩ : syracuseStep 2778067 = 4167101) B4167101
theorem B3704089 : Blo 2193435 3704089 := bstep (se 2 (by rfl) ⟨1389033, by rfl⟩ : syracuseStep 3704089 = 2778067) B2778067
theorem B4938785 : Blo 2193435 4938785 := bstep (se 2 (by rfl) ⟨1852044, by rfl⟩ : syracuseStep 4938785 = 3704089) B3704089
theorem B3292523 : Blo 2193435 3292523 := bstep (se 1 (by rfl) ⟨2469392, by rfl⟩ : syracuseStep 3292523 = 4938785) B4938785
theorem B2195015 : Blo 2193435 2195015 := bstep (se 1 (by rfl) ⟨1646261, by rfl⟩ : syracuseStep 2195015 = 3292523) B3292523
theorem B2469397 : Blo 2193435 2469397 := bbase (se 6 (by rfl) ⟨57876, by rfl⟩ : syracuseStep 2469397 = 115753) (by norm_num)
theorem B3292529 : Blo 2193435 3292529 := bstep (se 2 (by rfl) ⟨1234698, by rfl⟩ : syracuseStep 3292529 = 2469397) B2469397
theorem B2195019 : Blo 2193435 2195019 := bstep (se 1 (by rfl) ⟨1646264, by rfl⟩ : syracuseStep 2195019 = 3292529) B3292529
theorem B2778077 : Blo 2193435 2778077 := bbase (se 3 (by rfl) ⟨520889, by rfl⟩ : syracuseStep 2778077 = 1041779) (by norm_num)
theorem B7408205 : Blo 2193435 7408205 := bstep (se 3 (by rfl) ⟨1389038, by rfl⟩ : syracuseStep 7408205 = 2778077) B2778077
theorem B4938803 : Blo 2193435 4938803 := bstep (se 1 (by rfl) ⟨3704102, by rfl⟩ : syracuseStep 4938803 = 7408205) B7408205
theorem B3292535 : Blo 2193435 3292535 := bstep (se 1 (by rfl) ⟨2469401, by rfl⟩ : syracuseStep 3292535 = 4938803) B4938803
theorem B2195023 : Blo 2193435 2195023 := bstep (se 1 (by rfl) ⟨1646267, by rfl⟩ : syracuseStep 2195023 = 3292535) B3292535
theorem B3292541 : Blo 2193435 3292541 := bbase (se 3 (by rfl) ⟨617351, by rfl⟩ : syracuseStep 3292541 = 1234703) (by norm_num)
theorem B2195027 : Blo 2193435 2195027 := bstep (se 1 (by rfl) ⟨1646270, by rfl⟩ : syracuseStep 2195027 = 3292541) B3292541
theorem B4938821 : Blo 2193435 4938821 := bbase (se 4 (by rfl) ⟨463014, by rfl⟩ : syracuseStep 4938821 = 926029) (by norm_num)
theorem B3292547 : Blo 2193435 3292547 := bstep (se 1 (by rfl) ⟨2469410, by rfl⟩ : syracuseStep 3292547 = 4938821) B4938821
theorem B2195031 : Blo 2193435 2195031 := bstep (se 1 (by rfl) ⟨1646273, by rfl⟩ : syracuseStep 2195031 = 3292547) B3292547
theorem B6250709 : Blo 2193435 6250709 := bbase (se 7 (by rfl) ⟨73250, by rfl⟩ : syracuseStep 6250709 = 146501) (by norm_num)
theorem B4167139 : Blo 2193435 4167139 := bstep (se 1 (by rfl) ⟨3125354, by rfl⟩ : syracuseStep 4167139 = 6250709) B6250709
theorem B5556185 : Blo 2193435 5556185 := bstep (se 2 (by rfl) ⟨2083569, by rfl⟩ : syracuseStep 5556185 = 4167139) B4167139
theorem B3704123 : Blo 2193435 3704123 := bstep (se 1 (by rfl) ⟨2778092, by rfl⟩ : syracuseStep 3704123 = 5556185) B5556185
theorem B2469415 : Blo 2193435 2469415 := bstep (se 1 (by rfl) ⟨1852061, by rfl⟩ : syracuseStep 2469415 = 3704123) B3704123
theorem B3292553 : Blo 2193435 3292553 := bstep (se 2 (by rfl) ⟨1234707, by rfl⟩ : syracuseStep 3292553 = 2469415) B2469415
theorem B2195035 : Blo 2193435 2195035 := bstep (se 1 (by rfl) ⟨1646276, by rfl⟩ : syracuseStep 2195035 = 3292553) B3292553
theorem B11112389 : Blo 2193435 11112389 := bbase (se 4 (by rfl) ⟨1041786, by rfl⟩ : syracuseStep 11112389 = 2083573) (by norm_num)
theorem B7408259 : Blo 2193435 7408259 := bstep (se 1 (by rfl) ⟨5556194, by rfl⟩ : syracuseStep 7408259 = 11112389) B11112389
theorem B4938839 : Blo 2193435 4938839 := bstep (se 1 (by rfl) ⟨3704129, by rfl⟩ : syracuseStep 4938839 = 7408259) B7408259
theorem B3292559 : Blo 2193435 3292559 := bstep (se 1 (by rfl) ⟨2469419, by rfl⟩ : syracuseStep 3292559 = 4938839) B4938839
theorem B2195039 : Blo 2193435 2195039 := bstep (se 1 (by rfl) ⟨1646279, by rfl⟩ : syracuseStep 2195039 = 3292559) B3292559
theorem B3292565 : Blo 2193435 3292565 := bbase (se 6 (by rfl) ⟨77169, by rfl⟩ : syracuseStep 3292565 = 154339) (by norm_num)
theorem B2195043 : Blo 2193435 2195043 := bstep (se 1 (by rfl) ⟨1646282, by rfl⟩ : syracuseStep 2195043 = 3292565) B3292565
theorem B3955549 : Blo 2193435 3955549 := bbase (se 3 (by rfl) ⟨741665, by rfl⟩ : syracuseStep 3955549 = 1483331) (by norm_num)
theorem B5274065 : Blo 2193435 5274065 := bstep (se 2 (by rfl) ⟨1977774, by rfl⟩ : syracuseStep 5274065 = 3955549) B3955549
theorem B3516043 : Blo 2193435 3516043 := bstep (se 1 (by rfl) ⟨2637032, by rfl⟩ : syracuseStep 3516043 = 5274065) B5274065
theorem B4688057 : Blo 2193435 4688057 := bstep (se 2 (by rfl) ⟨1758021, by rfl⟩ : syracuseStep 4688057 = 3516043) B3516043
theorem B12501485 : Blo 2193435 12501485 := bstep (se 3 (by rfl) ⟨2344028, by rfl⟩ : syracuseStep 12501485 = 4688057) B4688057
theorem B8334323 : Blo 2193435 8334323 := bstep (se 1 (by rfl) ⟨6250742, by rfl⟩ : syracuseStep 8334323 = 12501485) B12501485
theorem B5556215 : Blo 2193435 5556215 := bstep (se 1 (by rfl) ⟨4167161, by rfl⟩ : syracuseStep 5556215 = 8334323) B8334323
theorem B3704143 : Blo 2193435 3704143 := bstep (se 1 (by rfl) ⟨2778107, by rfl⟩ : syracuseStep 3704143 = 5556215) B5556215
theorem B4938857 : Blo 2193435 4938857 := bstep (se 2 (by rfl) ⟨1852071, by rfl⟩ : syracuseStep 4938857 = 3704143) B3704143
theorem B3292571 : Blo 2193435 3292571 := bstep (se 1 (by rfl) ⟨2469428, by rfl⟩ : syracuseStep 3292571 = 4938857) B4938857
theorem B2195047 : Blo 2193435 2195047 := bstep (se 1 (by rfl) ⟨1646285, by rfl⟩ : syracuseStep 2195047 = 3292571) B3292571
theorem B2469433 : Blo 2193435 2469433 := bbase (se 2 (by rfl) ⟨926037, by rfl⟩ : syracuseStep 2469433 = 1852075) (by norm_num)
theorem B3292577 : Blo 2193435 3292577 := bstep (se 2 (by rfl) ⟨1234716, by rfl⟩ : syracuseStep 3292577 = 2469433) B2469433
theorem B2195051 : Blo 2193435 2195051 := bstep (se 1 (by rfl) ⟨1646288, by rfl⟩ : syracuseStep 2195051 = 3292577) B3292577
theorem B2344037 : Blo 2193435 2344037 := bbase (se 4 (by rfl) ⟨219753, by rfl⟩ : syracuseStep 2344037 = 439507) (by norm_num)
theorem B6250765 : Blo 2193435 6250765 := bstep (se 3 (by rfl) ⟨1172018, by rfl⟩ : syracuseStep 6250765 = 2344037) B2344037
theorem B8334353 : Blo 2193435 8334353 := bstep (se 2 (by rfl) ⟨3125382, by rfl⟩ : syracuseStep 8334353 = 6250765) B6250765
theorem B5556235 : Blo 2193435 5556235 := bstep (se 1 (by rfl) ⟨4167176, by rfl⟩ : syracuseStep 5556235 = 8334353) B8334353
theorem B7408313 : Blo 2193435 7408313 := bstep (se 2 (by rfl) ⟨2778117, by rfl⟩ : syracuseStep 7408313 = 5556235) B5556235
theorem B4938875 : Blo 2193435 4938875 := bstep (se 1 (by rfl) ⟨3704156, by rfl⟩ : syracuseStep 4938875 = 7408313) B7408313
theorem B3292583 : Blo 2193435 3292583 := bstep (se 1 (by rfl) ⟨2469437, by rfl⟩ : syracuseStep 3292583 = 4938875) B4938875
theorem B2195055 : Blo 2193435 2195055 := bstep (se 1 (by rfl) ⟨1646291, by rfl⟩ : syracuseStep 2195055 = 3292583) B3292583
theorem B3292589 : Blo 2193435 3292589 := bbase (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) (by norm_num)
theorem B2195059 : Blo 2193435 2195059 := bstep (se 1 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 2195059 = 3292589) B3292589
theorem B4938893 : Blo 2193435 4938893 := bbase (se 3 (by rfl) ⟨926042, by rfl⟩ : syracuseStep 4938893 = 1852085) (by norm_num)
theorem B3292595 : Blo 2193435 3292595 := bstep (se 1 (by rfl) ⟨2469446, by rfl⟩ : syracuseStep 3292595 = 4938893) B4938893
theorem B2195063 : Blo 2193435 2195063 := bstep (se 1 (by rfl) ⟨1646297, by rfl⟩ : syracuseStep 2195063 = 3292595) B3292595
theorem B2778133 : Blo 2193435 2778133 := bbase (se 6 (by rfl) ⟨65112, by rfl⟩ : syracuseStep 2778133 = 130225) (by norm_num)
theorem B3704177 : Blo 2193435 3704177 := bstep (se 2 (by rfl) ⟨1389066, by rfl⟩ : syracuseStep 3704177 = 2778133) B2778133
theorem B2469451 : Blo 2193435 2469451 := bstep (se 1 (by rfl) ⟨1852088, by rfl⟩ : syracuseStep 2469451 = 3704177) B3704177
theorem B3292601 : Blo 2193435 3292601 := bstep (se 2 (by rfl) ⟨1234725, by rfl⟩ : syracuseStep 3292601 = 2469451) B2469451
theorem B2195067 : Blo 2193435 2195067 := bstep (se 1 (by rfl) ⟨1646300, by rfl⟩ : syracuseStep 2195067 = 3292601) B3292601
theorem B47467093 : Blo 2193435 47467093 := bbase (se 8 (by rfl) ⟨278127, by rfl⟩ : syracuseStep 47467093 = 556255) (by norm_num)
theorem B63289457 : Blo 2193435 63289457 := bstep (se 2 (by rfl) ⟨23733546, by rfl⟩ : syracuseStep 63289457 = 47467093) B47467093
theorem B42192971 : Blo 2193435 42192971 := bstep (se 1 (by rfl) ⟨31644728, by rfl⟩ : syracuseStep 42192971 = 63289457) B63289457
theorem B28128647 : Blo 2193435 28128647 := bstep (se 1 (by rfl) ⟨21096485, by rfl⟩ : syracuseStep 28128647 = 42192971) B42192971
theorem B18752431 : Blo 2193435 18752431 := bstep (se 1 (by rfl) ⟨14064323, by rfl⟩ : syracuseStep 18752431 = 28128647) B28128647
theorem B25003241 : Blo 2193435 25003241 := bstep (se 2 (by rfl) ⟨9376215, by rfl⟩ : syracuseStep 25003241 = 18752431) B18752431
theorem B16668827 : Blo 2193435 16668827 := bstep (se 1 (by rfl) ⟨12501620, by rfl⟩ : syracuseStep 16668827 = 25003241) B25003241
theorem B11112551 : Blo 2193435 11112551 := bstep (se 1 (by rfl) ⟨8334413, by rfl⟩ : syracuseStep 11112551 = 16668827) B16668827
theorem B7408367 : Blo 2193435 7408367 := bstep (se 1 (by rfl) ⟨5556275, by rfl⟩ : syracuseStep 7408367 = 11112551) B11112551
theorem B4938911 : Blo 2193435 4938911 := bstep (se 1 (by rfl) ⟨3704183, by rfl⟩ : syracuseStep 4938911 = 7408367) B7408367
theorem B3292607 : Blo 2193435 3292607 := bstep (se 1 (by rfl) ⟨2469455, by rfl⟩ : syracuseStep 3292607 = 4938911) B4938911
theorem B2195071 : Blo 2193435 2195071 := bstep (se 1 (by rfl) ⟨1646303, by rfl⟩ : syracuseStep 2195071 = 3292607) B3292607
theorem B3292613 : Blo 2193435 3292613 := bbase (se 4 (by rfl) ⟨308682, by rfl⟩ : syracuseStep 3292613 = 617365) (by norm_num)
theorem B2195075 : Blo 2193435 2195075 := bstep (se 1 (by rfl) ⟨1646306, by rfl⟩ : syracuseStep 2195075 = 3292613) B3292613
theorem B3704197 : Blo 2193435 3704197 := bbase (se 4 (by rfl) ⟨347268, by rfl⟩ : syracuseStep 3704197 = 694537) (by norm_num)
theorem B4938929 : Blo 2193435 4938929 := bstep (se 2 (by rfl) ⟨1852098, by rfl⟩ : syracuseStep 4938929 = 3704197) B3704197
theorem B3292619 : Blo 2193435 3292619 := bstep (se 1 (by rfl) ⟨2469464, by rfl⟩ : syracuseStep 3292619 = 4938929) B4938929
theorem B2195079 : Blo 2193435 2195079 := bstep (se 1 (by rfl) ⟨1646309, by rfl⟩ : syracuseStep 2195079 = 3292619) B3292619
theorem B2469469 : Blo 2193435 2469469 := bbase (se 3 (by rfl) ⟨463025, by rfl⟩ : syracuseStep 2469469 = 926051) (by norm_num)
theorem B3292625 : Blo 2193435 3292625 := bstep (se 2 (by rfl) ⟨1234734, by rfl⟩ : syracuseStep 3292625 = 2469469) B2469469
theorem B2195083 : Blo 2193435 2195083 := bstep (se 1 (by rfl) ⟨1646312, by rfl⟩ : syracuseStep 2195083 = 3292625) B3292625
theorem B7408421 : Blo 2193435 7408421 := bbase (se 4 (by rfl) ⟨694539, by rfl⟩ : syracuseStep 7408421 = 1389079) (by norm_num)
theorem B4938947 : Blo 2193435 4938947 := bstep (se 1 (by rfl) ⟨3704210, by rfl⟩ : syracuseStep 4938947 = 7408421) B7408421
theorem B3292631 : Blo 2193435 3292631 := bstep (se 1 (by rfl) ⟨2469473, by rfl⟩ : syracuseStep 3292631 = 4938947) B4938947
theorem B2195087 : Blo 2193435 2195087 := bstep (se 1 (by rfl) ⟨1646315, by rfl⟩ : syracuseStep 2195087 = 3292631) B3292631
theorem B3292637 : Blo 2193435 3292637 := bbase (se 3 (by rfl) ⟨617369, by rfl⟩ : syracuseStep 3292637 = 1234739) (by norm_num)
theorem B2195091 : Blo 2193435 2195091 := bstep (se 1 (by rfl) ⟨1646318, by rfl⟩ : syracuseStep 2195091 = 3292637) B3292637
theorem B4938965 : Blo 2193435 4938965 := bbase (se 7 (by rfl) ⟨57878, by rfl⟩ : syracuseStep 4938965 = 115757) (by norm_num)
theorem B3292643 : Blo 2193435 3292643 := bstep (se 1 (by rfl) ⟨2469482, by rfl⟩ : syracuseStep 3292643 = 4938965) B4938965
theorem B2195095 : Blo 2193435 2195095 := bstep (se 1 (by rfl) ⟨1646321, by rfl⟩ : syracuseStep 2195095 = 3292643) B3292643
theorem B2503181 : Blo 2193435 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B6675149 : Blo 2193435 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B4450099 : Blo 2193435 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B5933465 : Blo 2193435 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B3955643 : Blo 2193435 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B2637095 : Blo 2193435 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B7032253 : Blo 2193435 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B9376337 : Blo 2193435 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B6250891 : Blo 2193435 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B8334521 : Blo 2193435 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B5556347 : Blo 2193435 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B3704231 : Blo 2193435 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B2469487 : Blo 2193435 2469487 := bstep (se 1 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 2469487 = 3704231) B3704231
theorem B3292649 : Blo 2193435 3292649 := bstep (se 2 (by rfl) ⟨1234743, by rfl⟩ : syracuseStep 3292649 = 2469487) B2469487
theorem B2195099 : Blo 2193435 2195099 := bstep (se 1 (by rfl) ⟨1646324, by rfl⟩ : syracuseStep 2195099 = 3292649) B3292649
theorem B2225053 : Blo 2193435 2225053 := bbase (se 3 (by rfl) ⟨417197, by rfl⟩ : syracuseStep 2225053 = 834395) (by norm_num)
theorem B2966737 : Blo 2193435 2966737 := bstep (se 2 (by rfl) ⟨1112526, by rfl⟩ : syracuseStep 2966737 = 2225053) B2225053
theorem B3955649 : Blo 2193435 3955649 := bstep (se 2 (by rfl) ⟨1483368, by rfl⟩ : syracuseStep 3955649 = 2966737) B2966737
theorem B10548397 : Blo 2193435 10548397 := bstep (se 3 (by rfl) ⟨1977824, by rfl⟩ : syracuseStep 10548397 = 3955649) B3955649
theorem B14064529 : Blo 2193435 14064529 := bstep (se 2 (by rfl) ⟨5274198, by rfl⟩ : syracuseStep 14064529 = 10548397) B10548397
theorem B18752705 : Blo 2193435 18752705 := bstep (se 2 (by rfl) ⟨7032264, by rfl⟩ : syracuseStep 18752705 = 14064529) B14064529
theorem B12501803 : Blo 2193435 12501803 := bstep (se 1 (by rfl) ⟨9376352, by rfl⟩ : syracuseStep 12501803 = 18752705) B18752705
theorem B8334535 : Blo 2193435 8334535 := bstep (se 1 (by rfl) ⟨6250901, by rfl⟩ : syracuseStep 8334535 = 12501803) B12501803
theorem B11112713 : Blo 2193435 11112713 := bstep (se 2 (by rfl) ⟨4167267, by rfl⟩ : syracuseStep 11112713 = 8334535) B8334535
theorem B7408475 : Blo 2193435 7408475 := bstep (se 1 (by rfl) ⟨5556356, by rfl⟩ : syracuseStep 7408475 = 11112713) B11112713
theorem B4938983 : Blo 2193435 4938983 := bstep (se 1 (by rfl) ⟨3704237, by rfl⟩ : syracuseStep 4938983 = 7408475) B7408475
theorem B3292655 : Blo 2193435 3292655 := bstep (se 1 (by rfl) ⟨2469491, by rfl⟩ : syracuseStep 3292655 = 4938983) B4938983
theorem B2195103 : Blo 2193435 2195103 := bstep (se 1 (by rfl) ⟨1646327, by rfl⟩ : syracuseStep 2195103 = 3292655) B3292655
theorem B3292661 : Blo 2193435 3292661 := bbase (se 5 (by rfl) ⟨154343, by rfl⟩ : syracuseStep 3292661 = 308687) (by norm_num)
theorem B2195107 : Blo 2193435 2195107 := bstep (se 1 (by rfl) ⟨1646330, by rfl⟩ : syracuseStep 2195107 = 3292661) B3292661
theorem B2344097 : Blo 2193435 2344097 := bbase (se 2 (by rfl) ⟨879036, by rfl⟩ : syracuseStep 2344097 = 1758073) (by norm_num)
theorem B6250925 : Blo 2193435 6250925 := bstep (se 3 (by rfl) ⟨1172048, by rfl⟩ : syracuseStep 6250925 = 2344097) B2344097
theorem B4167283 : Blo 2193435 4167283 := bstep (se 1 (by rfl) ⟨3125462, by rfl⟩ : syracuseStep 4167283 = 6250925) B6250925
theorem B5556377 : Blo 2193435 5556377 := bstep (se 2 (by rfl) ⟨2083641, by rfl⟩ : syracuseStep 5556377 = 4167283) B4167283
theorem B3704251 : Blo 2193435 3704251 := bstep (se 1 (by rfl) ⟨2778188, by rfl⟩ : syracuseStep 3704251 = 5556377) B5556377
theorem B4939001 : Blo 2193435 4939001 := bstep (se 2 (by rfl) ⟨1852125, by rfl⟩ : syracuseStep 4939001 = 3704251) B3704251
theorem B3292667 : Blo 2193435 3292667 := bstep (se 1 (by rfl) ⟨2469500, by rfl⟩ : syracuseStep 3292667 = 4939001) B4939001
theorem B2195111 : Blo 2193435 2195111 := bstep (se 1 (by rfl) ⟨1646333, by rfl⟩ : syracuseStep 2195111 = 3292667) B3292667
theorem B2469505 : Blo 2193435 2469505 := bbase (se 2 (by rfl) ⟨926064, by rfl⟩ : syracuseStep 2469505 = 1852129) (by norm_num)
theorem B3292673 : Blo 2193435 3292673 := bstep (se 2 (by rfl) ⟨1234752, by rfl⟩ : syracuseStep 3292673 = 2469505) B2469505
theorem B2195115 : Blo 2193435 2195115 := bstep (se 1 (by rfl) ⟨1646336, by rfl⟩ : syracuseStep 2195115 = 3292673) B3292673
theorem B5556397 : Blo 2193435 5556397 := bbase (se 3 (by rfl) ⟨1041824, by rfl⟩ : syracuseStep 5556397 = 2083649) (by norm_num)
theorem B7408529 : Blo 2193435 7408529 := bstep (se 2 (by rfl) ⟨2778198, by rfl⟩ : syracuseStep 7408529 = 5556397) B5556397
theorem B4939019 : Blo 2193435 4939019 := bstep (se 1 (by rfl) ⟨3704264, by rfl⟩ : syracuseStep 4939019 = 7408529) B7408529
theorem B3292679 : Blo 2193435 3292679 := bstep (se 1 (by rfl) ⟨2469509, by rfl⟩ : syracuseStep 3292679 = 4939019) B4939019
theorem B2195119 : Blo 2193435 2195119 := bstep (se 1 (by rfl) ⟨1646339, by rfl⟩ : syracuseStep 2195119 = 3292679) B3292679
theorem B3292685 : Blo 2193435 3292685 := bbase (se 3 (by rfl) ⟨617378, by rfl⟩ : syracuseStep 3292685 = 1234757) (by norm_num)
theorem B2195123 : Blo 2193435 2195123 := bstep (se 1 (by rfl) ⟨1646342, by rfl⟩ : syracuseStep 2195123 = 3292685) B3292685
theorem B4939037 : Blo 2193435 4939037 := bbase (se 3 (by rfl) ⟨926069, by rfl⟩ : syracuseStep 4939037 = 1852139) (by norm_num)
theorem B3292691 : Blo 2193435 3292691 := bstep (se 1 (by rfl) ⟨2469518, by rfl⟩ : syracuseStep 3292691 = 4939037) B4939037
theorem B2195127 : Blo 2193435 2195127 := bstep (se 1 (by rfl) ⟨1646345, by rfl⟩ : syracuseStep 2195127 = 3292691) B3292691
theorem B3704285 : Blo 2193435 3704285 := bbase (se 3 (by rfl) ⟨694553, by rfl⟩ : syracuseStep 3704285 = 1389107) (by norm_num)
theorem B2469523 : Blo 2193435 2469523 := bstep (se 1 (by rfl) ⟨1852142, by rfl⟩ : syracuseStep 2469523 = 3704285) B3704285
theorem B3292697 : Blo 2193435 3292697 := bstep (se 2 (by rfl) ⟨1234761, by rfl⟩ : syracuseStep 3292697 = 2469523) B2469523
theorem B2195131 : Blo 2193435 2195131 := bstep (se 1 (by rfl) ⟨1646348, by rfl⟩ : syracuseStep 2195131 = 3292697) B3292697
theorem B3383165 : Blo 2193435 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B9021773 : Blo 2193435 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B6014515 : Blo 2193435 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B8019353 : Blo 2193435 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B5346235 : Blo 2193435 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B7128313 : Blo 2193435 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B38017669 : Blo 2193435 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B50690225 : Blo 2193435 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B33793483 : Blo 2193435 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B45057977 : Blo 2193435 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B30038651 : Blo 2193435 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B20025767 : Blo 2193435 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B13350511 : Blo 2193435 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B17800681 : Blo 2193435 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B23734241 : Blo 2193435 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B15822827 : Blo 2193435 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B10548551 : Blo 2193435 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B7032367 : Blo 2193435 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B9376489 : Blo 2193435 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B12501985 : Blo 2193435 12501985 := bstep (se 2 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 12501985 = 9376489) B9376489
theorem B16669313 : Blo 2193435 16669313 := bstep (se 2 (by rfl) ⟨6250992, by rfl⟩ : syracuseStep 16669313 = 12501985) B12501985
theorem B11112875 : Blo 2193435 11112875 := bstep (se 1 (by rfl) ⟨8334656, by rfl⟩ : syracuseStep 11112875 = 16669313) B16669313
theorem B7408583 : Blo 2193435 7408583 := bstep (se 1 (by rfl) ⟨5556437, by rfl⟩ : syracuseStep 7408583 = 11112875) B11112875
theorem B4939055 : Blo 2193435 4939055 := bstep (se 1 (by rfl) ⟨3704291, by rfl⟩ : syracuseStep 4939055 = 7408583) B7408583
theorem B3292703 : Blo 2193435 3292703 := bstep (se 1 (by rfl) ⟨2469527, by rfl⟩ : syracuseStep 3292703 = 4939055) B4939055
theorem B2195135 : Blo 2193435 2195135 := bstep (se 1 (by rfl) ⟨1646351, by rfl⟩ : syracuseStep 2195135 = 3292703) B3292703
theorem B3292709 : Blo 2193435 3292709 := bbase (se 4 (by rfl) ⟨308691, by rfl⟩ : syracuseStep 3292709 = 617383) (by norm_num)
theorem B2195139 : Blo 2193435 2195139 := bstep (se 1 (by rfl) ⟨1646354, by rfl⟩ : syracuseStep 2195139 = 3292709) B3292709
theorem B2778229 : Blo 2193435 2778229 := bbase (se 5 (by rfl) ⟨130229, by rfl⟩ : syracuseStep 2778229 = 260459) (by norm_num)
theorem B3704305 : Blo 2193435 3704305 := bstep (se 2 (by rfl) ⟨1389114, by rfl⟩ : syracuseStep 3704305 = 2778229) B2778229
theorem B4939073 : Blo 2193435 4939073 := bstep (se 2 (by rfl) ⟨1852152, by rfl⟩ : syracuseStep 4939073 = 3704305) B3704305
theorem B3292715 : Blo 2193435 3292715 := bstep (se 1 (by rfl) ⟨2469536, by rfl⟩ : syracuseStep 3292715 = 4939073) B4939073
theorem B2195143 : Blo 2193435 2195143 := bstep (se 1 (by rfl) ⟨1646357, by rfl⟩ : syracuseStep 2195143 = 3292715) B3292715
theorem B2469541 : Blo 2193435 2469541 := bbase (se 4 (by rfl) ⟨231519, by rfl⟩ : syracuseStep 2469541 = 463039) (by norm_num)
theorem B3292721 : Blo 2193435 3292721 := bstep (se 2 (by rfl) ⟨1234770, by rfl⟩ : syracuseStep 3292721 = 2469541) B2469541
theorem B2195147 : Blo 2193435 2195147 := bstep (se 1 (by rfl) ⟨1646360, by rfl⟩ : syracuseStep 2195147 = 3292721) B3292721
theorem B4752245 : Blo 2193435 4752245 := bbase (se 5 (by rfl) ⟨222761, by rfl⟩ : syracuseStep 4752245 = 445523) (by norm_num)
theorem B3168163 : Blo 2193435 3168163 := bstep (se 1 (by rfl) ⟨2376122, by rfl⟩ : syracuseStep 3168163 = 4752245) B4752245
theorem B16896869 : Blo 2193435 16896869 := bstep (se 4 (by rfl) ⟨1584081, by rfl⟩ : syracuseStep 16896869 = 3168163) B3168163
theorem B11264579 : Blo 2193435 11264579 := bstep (se 1 (by rfl) ⟨8448434, by rfl⟩ : syracuseStep 11264579 = 16896869) B16896869
theorem B7509719 : Blo 2193435 7509719 := bstep (se 1 (by rfl) ⟨5632289, by rfl⟩ : syracuseStep 7509719 = 11264579) B11264579
theorem B5006479 : Blo 2193435 5006479 := bstep (se 1 (by rfl) ⟨3754859, by rfl⟩ : syracuseStep 5006479 = 7509719) B7509719
theorem B6675305 : Blo 2193435 6675305 := bstep (se 2 (by rfl) ⟨2503239, by rfl⟩ : syracuseStep 6675305 = 5006479) B5006479
theorem B17800813 : Blo 2193435 17800813 := bstep (se 3 (by rfl) ⟨3337652, by rfl⟩ : syracuseStep 17800813 = 6675305) B6675305
theorem B23734417 : Blo 2193435 23734417 := bstep (se 2 (by rfl) ⟨8900406, by rfl⟩ : syracuseStep 23734417 = 17800813) B17800813
theorem B31645889 : Blo 2193435 31645889 := bstep (se 2 (by rfl) ⟨11867208, by rfl⟩ : syracuseStep 31645889 = 23734417) B23734417
theorem B21097259 : Blo 2193435 21097259 := bstep (se 1 (by rfl) ⟨15822944, by rfl⟩ : syracuseStep 21097259 = 31645889) B31645889
theorem B14064839 : Blo 2193435 14064839 := bstep (se 1 (by rfl) ⟨10548629, by rfl⟩ : syracuseStep 14064839 = 21097259) B21097259
theorem B9376559 : Blo 2193435 9376559 := bstep (se 1 (by rfl) ⟨7032419, by rfl⟩ : syracuseStep 9376559 = 14064839) B14064839
theorem B6251039 : Blo 2193435 6251039 := bstep (se 1 (by rfl) ⟨4688279, by rfl⟩ : syracuseStep 6251039 = 9376559) B9376559
theorem B4167359 : Blo 2193435 4167359 := bstep (se 1 (by rfl) ⟨3125519, by rfl⟩ : syracuseStep 4167359 = 6251039) B6251039
theorem B2778239 : Blo 2193435 2778239 := bstep (se 1 (by rfl) ⟨2083679, by rfl⟩ : syracuseStep 2778239 = 4167359) B4167359
theorem B7408637 : Blo 2193435 7408637 := bstep (se 3 (by rfl) ⟨1389119, by rfl⟩ : syracuseStep 7408637 = 2778239) B2778239
theorem B4939091 : Blo 2193435 4939091 := bstep (se 1 (by rfl) ⟨3704318, by rfl⟩ : syracuseStep 4939091 = 7408637) B7408637
theorem B3292727 : Blo 2193435 3292727 := bstep (se 1 (by rfl) ⟨2469545, by rfl⟩ : syracuseStep 3292727 = 4939091) B4939091
theorem B2195151 : Blo 2193435 2195151 := bstep (se 1 (by rfl) ⟨1646363, by rfl⟩ : syracuseStep 2195151 = 3292727) B3292727
theorem B3292733 : Blo 2193435 3292733 := bbase (se 3 (by rfl) ⟨617387, by rfl⟩ : syracuseStep 3292733 = 1234775) (by norm_num)
theorem B2195155 : Blo 2193435 2195155 := bstep (se 1 (by rfl) ⟨1646366, by rfl⟩ : syracuseStep 2195155 = 3292733) B3292733
theorem B4939109 : Blo 2193435 4939109 := bbase (se 4 (by rfl) ⟨463041, by rfl⟩ : syracuseStep 4939109 = 926083) (by norm_num)
theorem B3292739 : Blo 2193435 3292739 := bstep (se 1 (by rfl) ⟨2469554, by rfl⟩ : syracuseStep 3292739 = 4939109) B4939109
theorem B2195159 : Blo 2193435 2195159 := bstep (se 1 (by rfl) ⟨1646369, by rfl⟩ : syracuseStep 2195159 = 3292739) B3292739
theorem B5556509 : Blo 2193435 5556509 := bbase (se 3 (by rfl) ⟨1041845, by rfl⟩ : syracuseStep 5556509 = 2083691) (by norm_num)
theorem B3704339 : Blo 2193435 3704339 := bstep (se 1 (by rfl) ⟨2778254, by rfl⟩ : syracuseStep 3704339 = 5556509) B5556509
theorem B2469559 : Blo 2193435 2469559 := bstep (se 1 (by rfl) ⟨1852169, by rfl⟩ : syracuseStep 2469559 = 3704339) B3704339
theorem B3292745 : Blo 2193435 3292745 := bstep (se 2 (by rfl) ⟨1234779, by rfl⟩ : syracuseStep 3292745 = 2469559) B2469559
theorem B2195163 : Blo 2193435 2195163 := bstep (se 1 (by rfl) ⟨1646372, by rfl⟩ : syracuseStep 2195163 = 3292745) B3292745
theorem B4167389 : Blo 2193435 4167389 := bbase (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) (by norm_num)
theorem B11113037 : Blo 2193435 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B7408691 : Blo 2193435 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B4939127 : Blo 2193435 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B3292751 : Blo 2193435 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B2195167 : Blo 2193435 2195167 := bstep (se 1 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 2195167 = 3292751) B3292751
theorem B3292757 : Blo 2193435 3292757 := bbase (se 8 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 3292757 = 38587) (by norm_num)
theorem B2195171 : Blo 2193435 2195171 := bstep (se 1 (by rfl) ⟨1646378, by rfl⟩ : syracuseStep 2195171 = 3292757) B3292757
theorem B9376661 : Blo 2193435 9376661 := bbase (se 6 (by rfl) ⟨219765, by rfl⟩ : syracuseStep 9376661 = 439531) (by norm_num)
theorem B6251107 : Blo 2193435 6251107 := bstep (se 1 (by rfl) ⟨4688330, by rfl⟩ : syracuseStep 6251107 = 9376661) B9376661
theorem B8334809 : Blo 2193435 8334809 := bstep (se 2 (by rfl) ⟨3125553, by rfl⟩ : syracuseStep 8334809 = 6251107) B6251107
theorem B5556539 : Blo 2193435 5556539 := bstep (se 1 (by rfl) ⟨4167404, by rfl⟩ : syracuseStep 5556539 = 8334809) B8334809
theorem B3704359 : Blo 2193435 3704359 := bstep (se 1 (by rfl) ⟨2778269, by rfl⟩ : syracuseStep 3704359 = 5556539) B5556539
theorem B4939145 : Blo 2193435 4939145 := bstep (se 2 (by rfl) ⟨1852179, by rfl⟩ : syracuseStep 4939145 = 3704359) B3704359
theorem B3292763 : Blo 2193435 3292763 := bstep (se 1 (by rfl) ⟨2469572, by rfl⟩ : syracuseStep 3292763 = 4939145) B4939145
theorem B2195175 : Blo 2193435 2195175 := bstep (se 1 (by rfl) ⟨1646381, by rfl⟩ : syracuseStep 2195175 = 3292763) B3292763
theorem B2469577 : Blo 2193435 2469577 := bbase (se 2 (by rfl) ⟨926091, by rfl⟩ : syracuseStep 2469577 = 1852183) (by norm_num)
theorem B3292769 : Blo 2193435 3292769 := bstep (se 2 (by rfl) ⟨1234788, by rfl⟩ : syracuseStep 3292769 = 2469577) B2469577
theorem B2195179 : Blo 2193435 2195179 := bstep (se 1 (by rfl) ⟨1646384, by rfl⟩ : syracuseStep 2195179 = 3292769) B3292769
theorem B11867381 : Blo 2193435 11867381 := bbase (se 5 (by rfl) ⟨556283, by rfl⟩ : syracuseStep 11867381 = 1112567) (by norm_num)
theorem B7911587 : Blo 2193435 7911587 := bstep (se 1 (by rfl) ⟨5933690, by rfl⟩ : syracuseStep 7911587 = 11867381) B11867381
theorem B5274391 : Blo 2193435 5274391 := bstep (se 1 (by rfl) ⟨3955793, by rfl⟩ : syracuseStep 5274391 = 7911587) B7911587
theorem B7032521 : Blo 2193435 7032521 := bstep (se 2 (by rfl) ⟨2637195, by rfl⟩ : syracuseStep 7032521 = 5274391) B5274391
theorem B18753389 : Blo 2193435 18753389 := bstep (se 3 (by rfl) ⟨3516260, by rfl⟩ : syracuseStep 18753389 = 7032521) B7032521
theorem B12502259 : Blo 2193435 12502259 := bstep (se 1 (by rfl) ⟨9376694, by rfl⟩ : syracuseStep 12502259 = 18753389) B18753389
theorem B8334839 : Blo 2193435 8334839 := bstep (se 1 (by rfl) ⟨6251129, by rfl⟩ : syracuseStep 8334839 = 12502259) B12502259
theorem B5556559 : Blo 2193435 5556559 := bstep (se 1 (by rfl) ⟨4167419, by rfl⟩ : syracuseStep 5556559 = 8334839) B8334839
theorem B7408745 : Blo 2193435 7408745 := bstep (se 2 (by rfl) ⟨2778279, by rfl⟩ : syracuseStep 7408745 = 5556559) B5556559
theorem B4939163 : Blo 2193435 4939163 := bstep (se 1 (by rfl) ⟨3704372, by rfl⟩ : syracuseStep 4939163 = 7408745) B7408745
theorem B3292775 : Blo 2193435 3292775 := bstep (se 1 (by rfl) ⟨2469581, by rfl⟩ : syracuseStep 3292775 = 4939163) B4939163
theorem B2195183 : Blo 2193435 2195183 := bstep (se 1 (by rfl) ⟨1646387, by rfl⟩ : syracuseStep 2195183 = 3292775) B3292775
theorem B3292781 : Blo 2193435 3292781 := bbase (se 3 (by rfl) ⟨617396, by rfl⟩ : syracuseStep 3292781 = 1234793) (by norm_num)
theorem B2195187 : Blo 2193435 2195187 := bstep (se 1 (by rfl) ⟨1646390, by rfl⟩ : syracuseStep 2195187 = 3292781) B3292781
theorem B4939181 : Blo 2193435 4939181 := bbase (se 3 (by rfl) ⟨926096, by rfl⟩ : syracuseStep 4939181 = 1852193) (by norm_num)
theorem B3292787 : Blo 2193435 3292787 := bstep (se 1 (by rfl) ⟨2469590, by rfl⟩ : syracuseStep 3292787 = 4939181) B4939181
theorem B2195191 : Blo 2193435 2195191 := bstep (se 1 (by rfl) ⟨1646393, by rfl⟩ : syracuseStep 2195191 = 3292787) B3292787
theorem B3168229 : Blo 2193435 3168229 := bbase (se 4 (by rfl) ⟨297021, by rfl⟩ : syracuseStep 3168229 = 594043) (by norm_num)
theorem B4224305 : Blo 2193435 4224305 := bstep (se 2 (by rfl) ⟨1584114, by rfl⟩ : syracuseStep 4224305 = 3168229) B3168229
theorem B2816203 : Blo 2193435 2816203 := bstep (se 1 (by rfl) ⟨2112152, by rfl⟩ : syracuseStep 2816203 = 4224305) B4224305
theorem B3754937 : Blo 2193435 3754937 := bstep (se 2 (by rfl) ⟨1408101, by rfl⟩ : syracuseStep 3754937 = 2816203) B2816203
theorem B10013165 : Blo 2193435 10013165 := bstep (se 3 (by rfl) ⟨1877468, by rfl⟩ : syracuseStep 10013165 = 3754937) B3754937
theorem B6675443 : Blo 2193435 6675443 := bstep (se 1 (by rfl) ⟨5006582, by rfl⟩ : syracuseStep 6675443 = 10013165) B10013165
theorem B4450295 : Blo 2193435 4450295 := bstep (se 1 (by rfl) ⟨3337721, by rfl⟩ : syracuseStep 4450295 = 6675443) B6675443
theorem B2966863 : Blo 2193435 2966863 := bstep (se 1 (by rfl) ⟨2225147, by rfl⟩ : syracuseStep 2966863 = 4450295) B4450295
theorem B3955817 : Blo 2193435 3955817 := bstep (se 2 (by rfl) ⟨1483431, by rfl⟩ : syracuseStep 3955817 = 2966863) B2966863
theorem B2637211 : Blo 2193435 2637211 := bstep (se 1 (by rfl) ⟨1977908, by rfl⟩ : syracuseStep 2637211 = 3955817) B3955817
theorem B3516281 : Blo 2193435 3516281 := bstep (se 2 (by rfl) ⟨1318605, by rfl⟩ : syracuseStep 3516281 = 2637211) B2637211
theorem B2344187 : Blo 2193435 2344187 := bstep (se 1 (by rfl) ⟨1758140, by rfl⟩ : syracuseStep 2344187 = 3516281) B3516281
theorem B6251165 : Blo 2193435 6251165 := bstep (se 3 (by rfl) ⟨1172093, by rfl⟩ : syracuseStep 6251165 = 2344187) B2344187
theorem B4167443 : Blo 2193435 4167443 := bstep (se 1 (by rfl) ⟨3125582, by rfl⟩ : syracuseStep 4167443 = 6251165) B6251165
theorem B2778295 : Blo 2193435 2778295 := bstep (se 1 (by rfl) ⟨2083721, by rfl⟩ : syracuseStep 2778295 = 4167443) B4167443
theorem B3704393 : Blo 2193435 3704393 := bstep (se 2 (by rfl) ⟨1389147, by rfl⟩ : syracuseStep 3704393 = 2778295) B2778295
theorem B2469595 : Blo 2193435 2469595 := bstep (se 1 (by rfl) ⟨1852196, by rfl⟩ : syracuseStep 2469595 = 3704393) B3704393
theorem B3292793 : Blo 2193435 3292793 := bstep (se 2 (by rfl) ⟨1234797, by rfl⟩ : syracuseStep 3292793 = 2469595) B2469595
theorem B2195195 : Blo 2193435 2195195 := bstep (se 1 (by rfl) ⟨1646396, by rfl⟩ : syracuseStep 2195195 = 3292793) B3292793
theorem B9634373 : Blo 2193435 9634373 := bbase (se 4 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 9634373 = 1806445) (by norm_num)
theorem B6422915 : Blo 2193435 6422915 := bstep (se 1 (by rfl) ⟨4817186, by rfl⟩ : syracuseStep 6422915 = 9634373) B9634373
theorem B4281943 : Blo 2193435 4281943 := bstep (se 1 (by rfl) ⟨3211457, by rfl⟩ : syracuseStep 4281943 = 6422915) B6422915
theorem B5709257 : Blo 2193435 5709257 := bstep (se 2 (by rfl) ⟨2140971, by rfl⟩ : syracuseStep 5709257 = 4281943) B4281943
theorem B3806171 : Blo 2193435 3806171 := bstep (se 1 (by rfl) ⟨2854628, by rfl⟩ : syracuseStep 3806171 = 5709257) B5709257
theorem B2537447 : Blo 2193435 2537447 := bstep (se 1 (by rfl) ⟨1903085, by rfl⟩ : syracuseStep 2537447 = 3806171) B3806171
theorem B6766525 : Blo 2193435 6766525 := bstep (se 3 (by rfl) ⟨1268723, by rfl⟩ : syracuseStep 6766525 = 2537447) B2537447
theorem B9022033 : Blo 2193435 9022033 := bstep (se 2 (by rfl) ⟨3383262, by rfl⟩ : syracuseStep 9022033 = 6766525) B6766525
theorem B48117509 : Blo 2193435 48117509 := bstep (se 4 (by rfl) ⟨4511016, by rfl⟩ : syracuseStep 48117509 = 9022033) B9022033
theorem B32078339 : Blo 2193435 32078339 := bstep (se 1 (by rfl) ⟨24058754, by rfl⟩ : syracuseStep 32078339 = 48117509) B48117509
theorem B21385559 : Blo 2193435 21385559 := bstep (se 1 (by rfl) ⟨16039169, by rfl⟩ : syracuseStep 21385559 = 32078339) B32078339
theorem B57028157 : Blo 2193435 57028157 := bstep (se 3 (by rfl) ⟨10692779, by rfl⟩ : syracuseStep 57028157 = 21385559) B21385559
theorem B38018771 : Blo 2193435 38018771 := bstep (se 1 (by rfl) ⟨28514078, by rfl⟩ : syracuseStep 38018771 = 57028157) B57028157
theorem B25345847 : Blo 2193435 25345847 := bstep (se 1 (by rfl) ⟨19009385, by rfl⟩ : syracuseStep 25345847 = 38018771) B38018771
theorem B16897231 : Blo 2193435 16897231 := bstep (se 1 (by rfl) ⟨12672923, by rfl⟩ : syracuseStep 16897231 = 25345847) B25345847
theorem B90118565 : Blo 2193435 90118565 := bstep (se 4 (by rfl) ⟨8448615, by rfl⟩ : syracuseStep 90118565 = 16897231) B16897231
theorem B60079043 : Blo 2193435 60079043 := bstep (se 1 (by rfl) ⟨45059282, by rfl⟩ : syracuseStep 60079043 = 90118565) B90118565
theorem B160210781 : Blo 2193435 160210781 := bstep (se 3 (by rfl) ⟨30039521, by rfl⟩ : syracuseStep 160210781 = 60079043) B60079043
theorem B106807187 : Blo 2193435 106807187 := bstep (se 1 (by rfl) ⟨80105390, by rfl⟩ : syracuseStep 106807187 = 160210781) B160210781
theorem B71204791 : Blo 2193435 71204791 := bstep (se 1 (by rfl) ⟨53403593, by rfl⟩ : syracuseStep 71204791 = 106807187) B106807187
theorem B94939721 : Blo 2193435 94939721 := bstep (se 2 (by rfl) ⟨35602395, by rfl⟩ : syracuseStep 94939721 = 71204791) B71204791
theorem B63293147 : Blo 2193435 63293147 := bstep (se 1 (by rfl) ⟨47469860, by rfl⟩ : syracuseStep 63293147 = 94939721) B94939721
theorem B42195431 : Blo 2193435 42195431 := bstep (se 1 (by rfl) ⟨31646573, by rfl⟩ : syracuseStep 42195431 = 63293147) B63293147
theorem B28130287 : Blo 2193435 28130287 := bstep (se 1 (by rfl) ⟨21097715, by rfl⟩ : syracuseStep 28130287 = 42195431) B42195431
theorem B37507049 : Blo 2193435 37507049 := bstep (se 2 (by rfl) ⟨14065143, by rfl⟩ : syracuseStep 37507049 = 28130287) B28130287
theorem B25004699 : Blo 2193435 25004699 := bstep (se 1 (by rfl) ⟨18753524, by rfl⟩ : syracuseStep 25004699 = 37507049) B37507049
theorem B16669799 : Blo 2193435 16669799 := bstep (se 1 (by rfl) ⟨12502349, by rfl⟩ : syracuseStep 16669799 = 25004699) B25004699
theorem B11113199 : Blo 2193435 11113199 := bstep (se 1 (by rfl) ⟨8334899, by rfl⟩ : syracuseStep 11113199 = 16669799) B16669799
theorem B7408799 : Blo 2193435 7408799 := bstep (se 1 (by rfl) ⟨5556599, by rfl⟩ : syracuseStep 7408799 = 11113199) B11113199
theorem B4939199 : Blo 2193435 4939199 := bstep (se 1 (by rfl) ⟨3704399, by rfl⟩ : syracuseStep 4939199 = 7408799) B7408799
theorem B3292799 : Blo 2193435 3292799 := bstep (se 1 (by rfl) ⟨2469599, by rfl⟩ : syracuseStep 3292799 = 4939199) B4939199
theorem B2195199 : Blo 2193435 2195199 := bstep (se 1 (by rfl) ⟨1646399, by rfl⟩ : syracuseStep 2195199 = 3292799) B3292799
theorem B3292805 : Blo 2193435 3292805 := bbase (se 4 (by rfl) ⟨308700, by rfl⟩ : syracuseStep 3292805 = 617401) (by norm_num)
theorem B2195203 : Blo 2193435 2195203 := bstep (se 1 (by rfl) ⟨1646402, by rfl⟩ : syracuseStep 2195203 = 3292805) B3292805
theorem B3704413 : Blo 2193435 3704413 := bbase (se 3 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 3704413 = 1389155) (by norm_num)
theorem B4939217 : Blo 2193435 4939217 := bstep (se 2 (by rfl) ⟨1852206, by rfl⟩ : syracuseStep 4939217 = 3704413) B3704413
theorem B3292811 : Blo 2193435 3292811 := bstep (se 1 (by rfl) ⟨2469608, by rfl⟩ : syracuseStep 3292811 = 4939217) B4939217
theorem B2195207 : Blo 2193435 2195207 := bstep (se 1 (by rfl) ⟨1646405, by rfl⟩ : syracuseStep 2195207 = 3292811) B3292811
theorem B2469613 : Blo 2193435 2469613 := bbase (se 3 (by rfl) ⟨463052, by rfl⟩ : syracuseStep 2469613 = 926105) (by norm_num)
theorem B3292817 : Blo 2193435 3292817 := bstep (se 2 (by rfl) ⟨1234806, by rfl⟩ : syracuseStep 3292817 = 2469613) B2469613
theorem B2195211 : Blo 2193435 2195211 := bstep (se 1 (by rfl) ⟨1646408, by rfl⟩ : syracuseStep 2195211 = 3292817) B3292817
theorem B7408853 : Blo 2193435 7408853 := bbase (se 7 (by rfl) ⟨86822, by rfl⟩ : syracuseStep 7408853 = 173645) (by norm_num)
theorem B4939235 : Blo 2193435 4939235 := bstep (se 1 (by rfl) ⟨3704426, by rfl⟩ : syracuseStep 4939235 = 7408853) B7408853
theorem B3292823 : Blo 2193435 3292823 := bstep (se 1 (by rfl) ⟨2469617, by rfl⟩ : syracuseStep 3292823 = 4939235) B4939235
theorem B2195215 : Blo 2193435 2195215 := bstep (se 1 (by rfl) ⟨1646411, by rfl⟩ : syracuseStep 2195215 = 3292823) B3292823
theorem B3292829 : Blo 2193435 3292829 := bbase (se 3 (by rfl) ⟨617405, by rfl⟩ : syracuseStep 3292829 = 1234811) (by norm_num)
theorem B2195219 : Blo 2193435 2195219 := bstep (se 1 (by rfl) ⟨1646414, by rfl⟩ : syracuseStep 2195219 = 3292829) B3292829
theorem B4939253 : Blo 2193435 4939253 := bbase (se 5 (by rfl) ⟨231527, by rfl⟩ : syracuseStep 4939253 = 463055) (by norm_num)
theorem B3292835 : Blo 2193435 3292835 := bstep (se 1 (by rfl) ⟨2469626, by rfl⟩ : syracuseStep 3292835 = 4939253) B4939253
theorem B2195223 : Blo 2193435 2195223 := bstep (se 1 (by rfl) ⟨1646417, by rfl⟩ : syracuseStep 2195223 = 3292835) B3292835
theorem B125145173 : Blo 2193435 125145173 := bbase (se 8 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 125145173 = 1466545) (by norm_num)
theorem B333720461 : Blo 2193435 333720461 := bstep (se 3 (by rfl) ⟨62572586, by rfl⟩ : syracuseStep 333720461 = 125145173) B125145173
theorem B222480307 : Blo 2193435 222480307 := bstep (se 1 (by rfl) ⟨166860230, by rfl⟩ : syracuseStep 222480307 = 333720461) B333720461
theorem B296640409 : Blo 2193435 296640409 := bstep (se 2 (by rfl) ⟨111240153, by rfl⟩ : syracuseStep 296640409 = 222480307) B222480307
theorem B395520545 : Blo 2193435 395520545 := bstep (se 2 (by rfl) ⟨148320204, by rfl⟩ : syracuseStep 395520545 = 296640409) B296640409
theorem B263680363 : Blo 2193435 263680363 := bstep (se 1 (by rfl) ⟨197760272, by rfl⟩ : syracuseStep 263680363 = 395520545) B395520545
theorem B351573817 : Blo 2193435 351573817 := bstep (se 2 (by rfl) ⟨131840181, by rfl⟩ : syracuseStep 351573817 = 263680363) B263680363
theorem B468765089 : Blo 2193435 468765089 := bstep (se 2 (by rfl) ⟨175786908, by rfl⟩ : syracuseStep 468765089 = 351573817) B351573817
theorem B312510059 : Blo 2193435 312510059 := bstep (se 1 (by rfl) ⟨234382544, by rfl⟩ : syracuseStep 312510059 = 468765089) B468765089
theorem B208340039 : Blo 2193435 208340039 := bstep (se 1 (by rfl) ⟨156255029, by rfl⟩ : syracuseStep 208340039 = 312510059) B312510059
theorem B555573437 : Blo 2193435 555573437 := bstep (se 3 (by rfl) ⟨104170019, by rfl⟩ : syracuseStep 555573437 = 208340039) B208340039
theorem B370382291 : Blo 2193435 370382291 := bstep (se 1 (by rfl) ⟨277786718, by rfl⟩ : syracuseStep 370382291 = 555573437) B555573437
theorem B246921527 : Blo 2193435 246921527 := bstep (se 1 (by rfl) ⟨185191145, by rfl⟩ : syracuseStep 246921527 = 370382291) B370382291
theorem B164614351 : Blo 2193435 164614351 := bstep (se 1 (by rfl) ⟨123460763, by rfl⟩ : syracuseStep 164614351 = 246921527) B246921527
theorem B219485801 : Blo 2193435 219485801 := bstep (se 2 (by rfl) ⟨82307175, by rfl⟩ : syracuseStep 219485801 = 164614351) B164614351
theorem B146323867 : Blo 2193435 146323867 := bstep (se 1 (by rfl) ⟨109742900, by rfl⟩ : syracuseStep 146323867 = 219485801) B219485801
theorem B195098489 : Blo 2193435 195098489 := bstep (se 2 (by rfl) ⟨73161933, by rfl⟩ : syracuseStep 195098489 = 146323867) B146323867
theorem B130065659 : Blo 2193435 130065659 := bstep (se 1 (by rfl) ⟨97549244, by rfl⟩ : syracuseStep 130065659 = 195098489) B195098489
theorem B86710439 : Blo 2193435 86710439 := bstep (se 1 (by rfl) ⟨65032829, by rfl⟩ : syracuseStep 86710439 = 130065659) B130065659
theorem B57806959 : Blo 2193435 57806959 := bstep (se 1 (by rfl) ⟨43355219, by rfl⟩ : syracuseStep 57806959 = 86710439) B86710439
theorem B77075945 : Blo 2193435 77075945 := bstep (se 2 (by rfl) ⟨28903479, by rfl⟩ : syracuseStep 77075945 = 57806959) B57806959
theorem B51383963 : Blo 2193435 51383963 := bstep (se 1 (by rfl) ⟨38537972, by rfl⟩ : syracuseStep 51383963 = 77075945) B77075945
theorem B34255975 : Blo 2193435 34255975 := bstep (se 1 (by rfl) ⟨25691981, by rfl⟩ : syracuseStep 34255975 = 51383963) B51383963
theorem B45674633 : Blo 2193435 45674633 := bstep (se 2 (by rfl) ⟨17127987, by rfl⟩ : syracuseStep 45674633 = 34255975) B34255975
theorem B30449755 : Blo 2193435 30449755 := bstep (se 1 (by rfl) ⟨22837316, by rfl⟩ : syracuseStep 30449755 = 45674633) B45674633
theorem B40599673 : Blo 2193435 40599673 := bstep (se 2 (by rfl) ⟨15224877, by rfl⟩ : syracuseStep 40599673 = 30449755) B30449755
theorem B866126357 : Blo 2193435 866126357 := bstep (se 6 (by rfl) ⟨20299836, by rfl⟩ : syracuseStep 866126357 = 40599673) B40599673
theorem B577417571 : Blo 2193435 577417571 := bstep (se 1 (by rfl) ⟨433063178, by rfl⟩ : syracuseStep 577417571 = 866126357) B866126357
theorem B384945047 : Blo 2193435 384945047 := bstep (se 1 (by rfl) ⟨288708785, by rfl⟩ : syracuseStep 384945047 = 577417571) B577417571
theorem B256630031 : Blo 2193435 256630031 := bstep (se 1 (by rfl) ⟨192472523, by rfl⟩ : syracuseStep 256630031 = 384945047) B384945047
theorem B171086687 : Blo 2193435 171086687 := bstep (se 1 (by rfl) ⟨128315015, by rfl⟩ : syracuseStep 171086687 = 256630031) B256630031
theorem B114057791 : Blo 2193435 114057791 := bstep (se 1 (by rfl) ⟨85543343, by rfl⟩ : syracuseStep 114057791 = 171086687) B171086687
theorem B76038527 : Blo 2193435 76038527 := bstep (se 1 (by rfl) ⟨57028895, by rfl⟩ : syracuseStep 76038527 = 114057791) B114057791
theorem B50692351 : Blo 2193435 50692351 := bstep (se 1 (by rfl) ⟨38019263, by rfl⟩ : syracuseStep 50692351 = 76038527) B76038527
theorem B67589801 : Blo 2193435 67589801 := bstep (se 2 (by rfl) ⟨25346175, by rfl⟩ : syracuseStep 67589801 = 50692351) B50692351
theorem B45059867 : Blo 2193435 45059867 := bstep (se 1 (by rfl) ⟨33794900, by rfl⟩ : syracuseStep 45059867 = 67589801) B67589801
theorem B30039911 : Blo 2193435 30039911 := bstep (se 1 (by rfl) ⟨22529933, by rfl⟩ : syracuseStep 30039911 = 45059867) B45059867
theorem B20026607 : Blo 2193435 20026607 := bstep (se 1 (by rfl) ⟨15019955, by rfl⟩ : syracuseStep 20026607 = 30039911) B30039911
theorem B53404285 : Blo 2193435 53404285 := bstep (se 3 (by rfl) ⟨10013303, by rfl⟩ : syracuseStep 53404285 = 20026607) B20026607
theorem B71205713 : Blo 2193435 71205713 := bstep (se 2 (by rfl) ⟨26702142, by rfl⟩ : syracuseStep 71205713 = 53404285) B53404285
theorem B47470475 : Blo 2193435 47470475 := bstep (se 1 (by rfl) ⟨35602856, by rfl⟩ : syracuseStep 47470475 = 71205713) B71205713
theorem B31646983 : Blo 2193435 31646983 := bstep (se 1 (by rfl) ⟨23735237, by rfl⟩ : syracuseStep 31646983 = 47470475) B47470475
theorem B42195977 : Blo 2193435 42195977 := bstep (se 2 (by rfl) ⟨15823491, by rfl⟩ : syracuseStep 42195977 = 31646983) B31646983
theorem B28130651 : Blo 2193435 28130651 := bstep (se 1 (by rfl) ⟨21097988, by rfl⟩ : syracuseStep 28130651 = 42195977) B42195977
theorem B18753767 : Blo 2193435 18753767 := bstep (se 1 (by rfl) ⟨14065325, by rfl⟩ : syracuseStep 18753767 = 28130651) B28130651
theorem B12502511 : Blo 2193435 12502511 := bstep (se 1 (by rfl) ⟨9376883, by rfl⟩ : syracuseStep 12502511 = 18753767) B18753767
theorem B8335007 : Blo 2193435 8335007 := bstep (se 1 (by rfl) ⟨6251255, by rfl⟩ : syracuseStep 8335007 = 12502511) B12502511
theorem B5556671 : Blo 2193435 5556671 := bstep (se 1 (by rfl) ⟨4167503, by rfl⟩ : syracuseStep 5556671 = 8335007) B8335007
theorem B3704447 : Blo 2193435 3704447 := bstep (se 1 (by rfl) ⟨2778335, by rfl⟩ : syracuseStep 3704447 = 5556671) B5556671
theorem B2469631 : Blo 2193435 2469631 := bstep (se 1 (by rfl) ⟨1852223, by rfl⟩ : syracuseStep 2469631 = 3704447) B3704447
theorem B3292841 : Blo 2193435 3292841 := bstep (se 2 (by rfl) ⟨1234815, by rfl⟩ : syracuseStep 3292841 = 2469631) B2469631
theorem B2195227 : Blo 2193435 2195227 := bstep (se 1 (by rfl) ⟨1646420, by rfl⟩ : syracuseStep 2195227 = 3292841) B3292841
theorem B2344225 : Blo 2193435 2344225 := bbase (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) (by norm_num)
theorem B3125633 : Blo 2193435 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B8335021 : Blo 2193435 8335021 := bstep (se 3 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 8335021 = 3125633) B3125633
theorem B11113361 : Blo 2193435 11113361 := bstep (se 2 (by rfl) ⟨4167510, by rfl⟩ : syracuseStep 11113361 = 8335021) B8335021
theorem B7408907 : Blo 2193435 7408907 := bstep (se 1 (by rfl) ⟨5556680, by rfl⟩ : syracuseStep 7408907 = 11113361) B11113361
theorem B4939271 : Blo 2193435 4939271 := bstep (se 1 (by rfl) ⟨3704453, by rfl⟩ : syracuseStep 4939271 = 7408907) B7408907
theorem B3292847 : Blo 2193435 3292847 := bstep (se 1 (by rfl) ⟨2469635, by rfl⟩ : syracuseStep 3292847 = 4939271) B4939271
theorem B2195231 : Blo 2193435 2195231 := bstep (se 1 (by rfl) ⟨1646423, by rfl⟩ : syracuseStep 2195231 = 3292847) B3292847
theorem B3292853 : Blo 2193435 3292853 := bbase (se 5 (by rfl) ⟨154352, by rfl⟩ : syracuseStep 3292853 = 308705) (by norm_num)
theorem B2195235 : Blo 2193435 2195235 := bstep (se 1 (by rfl) ⟨1646426, by rfl⟩ : syracuseStep 2195235 = 3292853) B3292853
theorem B5556701 : Blo 2193435 5556701 := bbase (se 3 (by rfl) ⟨1041881, by rfl⟩ : syracuseStep 5556701 = 2083763) (by norm_num)
theorem B3704467 : Blo 2193435 3704467 := bstep (se 1 (by rfl) ⟨2778350, by rfl⟩ : syracuseStep 3704467 = 5556701) B5556701
theorem B4939289 : Blo 2193435 4939289 := bstep (se 2 (by rfl) ⟨1852233, by rfl⟩ : syracuseStep 4939289 = 3704467) B3704467
theorem B3292859 : Blo 2193435 3292859 := bstep (se 1 (by rfl) ⟨2469644, by rfl⟩ : syracuseStep 3292859 = 4939289) B4939289
theorem B2195239 : Blo 2193435 2195239 := bstep (se 1 (by rfl) ⟨1646429, by rfl⟩ : syracuseStep 2195239 = 3292859) B3292859
theorem B2469649 : Blo 2193435 2469649 := bbase (se 2 (by rfl) ⟨926118, by rfl⟩ : syracuseStep 2469649 = 1852237) (by norm_num)
theorem B3292865 : Blo 2193435 3292865 := bstep (se 2 (by rfl) ⟨1234824, by rfl⟩ : syracuseStep 3292865 = 2469649) B2469649
theorem B2195243 : Blo 2193435 2195243 := bstep (se 1 (by rfl) ⟨1646432, by rfl⟩ : syracuseStep 2195243 = 3292865) B3292865
theorem B4167541 : Blo 2193435 4167541 := bbase (se 5 (by rfl) ⟨195353, by rfl⟩ : syracuseStep 4167541 = 390707) (by norm_num)
theorem B5556721 : Blo 2193435 5556721 := bstep (se 2 (by rfl) ⟨2083770, by rfl⟩ : syracuseStep 5556721 = 4167541) B4167541
theorem B7408961 : Blo 2193435 7408961 := bstep (se 2 (by rfl) ⟨2778360, by rfl⟩ : syracuseStep 7408961 = 5556721) B5556721
theorem B4939307 : Blo 2193435 4939307 := bstep (se 1 (by rfl) ⟨3704480, by rfl⟩ : syracuseStep 4939307 = 7408961) B7408961
theorem B3292871 : Blo 2193435 3292871 := bstep (se 1 (by rfl) ⟨2469653, by rfl⟩ : syracuseStep 3292871 = 4939307) B4939307
theorem B2195247 : Blo 2193435 2195247 := bstep (se 1 (by rfl) ⟨1646435, by rfl⟩ : syracuseStep 2195247 = 3292871) B3292871
theorem B3292877 : Blo 2193435 3292877 := bbase (se 3 (by rfl) ⟨617414, by rfl⟩ : syracuseStep 3292877 = 1234829) (by norm_num)
theorem B2195251 : Blo 2193435 2195251 := bstep (se 1 (by rfl) ⟨1646438, by rfl⟩ : syracuseStep 2195251 = 3292877) B3292877
theorem B4939325 : Blo 2193435 4939325 := bbase (se 3 (by rfl) ⟨926123, by rfl⟩ : syracuseStep 4939325 = 1852247) (by norm_num)
theorem B3292883 : Blo 2193435 3292883 := bstep (se 1 (by rfl) ⟨2469662, by rfl⟩ : syracuseStep 3292883 = 4939325) B4939325
theorem B2195255 : Blo 2193435 2195255 := bstep (se 1 (by rfl) ⟨1646441, by rfl⟩ : syracuseStep 2195255 = 3292883) B3292883
theorem B3704501 : Blo 2193435 3704501 := bbase (se 5 (by rfl) ⟨173648, by rfl⟩ : syracuseStep 3704501 = 347297) (by norm_num)
theorem B2469667 : Blo 2193435 2469667 := bstep (se 1 (by rfl) ⟨1852250, by rfl⟩ : syracuseStep 2469667 = 3704501) B3704501
theorem B3292889 : Blo 2193435 3292889 := bstep (se 2 (by rfl) ⟨1234833, by rfl⟩ : syracuseStep 3292889 = 2469667) B2469667
theorem B2195259 : Blo 2193435 2195259 := bstep (se 1 (by rfl) ⟨1646444, by rfl⟩ : syracuseStep 2195259 = 3292889) B3292889
theorem B3516389 : Blo 2193435 3516389 := bbase (se 4 (by rfl) ⟨329661, by rfl⟩ : syracuseStep 3516389 = 659323) (by norm_num)
theorem B2344259 : Blo 2193435 2344259 := bstep (se 1 (by rfl) ⟨1758194, by rfl⟩ : syracuseStep 2344259 = 3516389) B3516389
theorem B6251357 : Blo 2193435 6251357 := bstep (se 3 (by rfl) ⟨1172129, by rfl⟩ : syracuseStep 6251357 = 2344259) B2344259
theorem B16670285 : Blo 2193435 16670285 := bstep (se 3 (by rfl) ⟨3125678, by rfl⟩ : syracuseStep 16670285 = 6251357) B6251357
theorem B11113523 : Blo 2193435 11113523 := bstep (se 1 (by rfl) ⟨8335142, by rfl⟩ : syracuseStep 11113523 = 16670285) B16670285
theorem B7409015 : Blo 2193435 7409015 := bstep (se 1 (by rfl) ⟨5556761, by rfl⟩ : syracuseStep 7409015 = 11113523) B11113523
theorem B4939343 : Blo 2193435 4939343 := bstep (se 1 (by rfl) ⟨3704507, by rfl⟩ : syracuseStep 4939343 = 7409015) B7409015
theorem B3292895 : Blo 2193435 3292895 := bstep (se 1 (by rfl) ⟨2469671, by rfl⟩ : syracuseStep 3292895 = 4939343) B4939343
theorem B2195263 : Blo 2193435 2195263 := bstep (se 1 (by rfl) ⟨1646447, by rfl⟩ : syracuseStep 2195263 = 3292895) B3292895
theorem B3292901 : Blo 2193435 3292901 := bbase (se 4 (by rfl) ⟨308709, by rfl⟩ : syracuseStep 3292901 = 617419) (by norm_num)
theorem B2195267 : Blo 2193435 2195267 := bstep (se 1 (by rfl) ⟨1646450, by rfl⟩ : syracuseStep 2195267 = 3292901) B3292901
theorem B6251381 : Blo 2193435 6251381 := bbase (se 5 (by rfl) ⟨293033, by rfl⟩ : syracuseStep 6251381 = 586067) (by norm_num)
theorem B4167587 : Blo 2193435 4167587 := bstep (se 1 (by rfl) ⟨3125690, by rfl⟩ : syracuseStep 4167587 = 6251381) B6251381
theorem B2778391 : Blo 2193435 2778391 := bstep (se 1 (by rfl) ⟨2083793, by rfl⟩ : syracuseStep 2778391 = 4167587) B4167587
theorem B3704521 : Blo 2193435 3704521 := bstep (se 2 (by rfl) ⟨1389195, by rfl⟩ : syracuseStep 3704521 = 2778391) B2778391
theorem B4939361 : Blo 2193435 4939361 := bstep (se 2 (by rfl) ⟨1852260, by rfl⟩ : syracuseStep 4939361 = 3704521) B3704521
theorem B3292907 : Blo 2193435 3292907 := bstep (se 1 (by rfl) ⟨2469680, by rfl⟩ : syracuseStep 3292907 = 4939361) B4939361
theorem B2195271 : Blo 2193435 2195271 := bstep (se 1 (by rfl) ⟨1646453, by rfl⟩ : syracuseStep 2195271 = 3292907) B3292907
theorem B2469685 : Blo 2193435 2469685 := bbase (se 5 (by rfl) ⟨115766, by rfl⟩ : syracuseStep 2469685 = 231533) (by norm_num)
theorem B3292913 : Blo 2193435 3292913 := bstep (se 2 (by rfl) ⟨1234842, by rfl⟩ : syracuseStep 3292913 = 2469685) B2469685
theorem B2195275 : Blo 2193435 2195275 := bstep (se 1 (by rfl) ⟨1646456, by rfl⟩ : syracuseStep 2195275 = 3292913) B3292913
theorem B2778401 : Blo 2193435 2778401 := bbase (se 2 (by rfl) ⟨1041900, by rfl⟩ : syracuseStep 2778401 = 2083801) (by norm_num)
theorem B7409069 : Blo 2193435 7409069 := bstep (se 3 (by rfl) ⟨1389200, by rfl⟩ : syracuseStep 7409069 = 2778401) B2778401
theorem B4939379 : Blo 2193435 4939379 := bstep (se 1 (by rfl) ⟨3704534, by rfl⟩ : syracuseStep 4939379 = 7409069) B7409069
theorem B3292919 : Blo 2193435 3292919 := bstep (se 1 (by rfl) ⟨2469689, by rfl⟩ : syracuseStep 3292919 = 4939379) B4939379
theorem B2195279 : Blo 2193435 2195279 := bstep (se 1 (by rfl) ⟨1646459, by rfl⟩ : syracuseStep 2195279 = 3292919) B3292919
theorem B3292925 : Blo 2193435 3292925 := bbase (se 3 (by rfl) ⟨617423, by rfl⟩ : syracuseStep 3292925 = 1234847) (by norm_num)
theorem B2195283 : Blo 2193435 2195283 := bstep (se 1 (by rfl) ⟨1646462, by rfl⟩ : syracuseStep 2195283 = 3292925) B3292925
theorem B4939397 : Blo 2193435 4939397 := bbase (se 4 (by rfl) ⟨463068, by rfl⟩ : syracuseStep 4939397 = 926137) (by norm_num)
theorem B3292931 : Blo 2193435 3292931 := bstep (se 1 (by rfl) ⟨2469698, by rfl⟩ : syracuseStep 3292931 = 4939397) B4939397
theorem B2195287 : Blo 2193435 2195287 := bstep (se 1 (by rfl) ⟨1646465, by rfl⟩ : syracuseStep 2195287 = 3292931) B3292931
theorem B7032869 : Blo 2193435 7032869 := bbase (se 4 (by rfl) ⟨659331, by rfl⟩ : syracuseStep 7032869 = 1318663) (by norm_num)
theorem B4688579 : Blo 2193435 4688579 := bstep (se 1 (by rfl) ⟨3516434, by rfl⟩ : syracuseStep 4688579 = 7032869) B7032869
theorem B3125719 : Blo 2193435 3125719 := bstep (se 1 (by rfl) ⟨2344289, by rfl⟩ : syracuseStep 3125719 = 4688579) B4688579
theorem B4167625 : Blo 2193435 4167625 := bstep (se 2 (by rfl) ⟨1562859, by rfl⟩ : syracuseStep 4167625 = 3125719) B3125719
theorem B5556833 : Blo 2193435 5556833 := bstep (se 2 (by rfl) ⟨2083812, by rfl⟩ : syracuseStep 5556833 = 4167625) B4167625
theorem B3704555 : Blo 2193435 3704555 := bstep (se 1 (by rfl) ⟨2778416, by rfl⟩ : syracuseStep 3704555 = 5556833) B5556833
theorem B2469703 : Blo 2193435 2469703 := bstep (se 1 (by rfl) ⟨1852277, by rfl⟩ : syracuseStep 2469703 = 3704555) B3704555
theorem B3292937 : Blo 2193435 3292937 := bstep (se 2 (by rfl) ⟨1234851, by rfl⟩ : syracuseStep 3292937 = 2469703) B2469703
theorem B2195291 : Blo 2193435 2195291 := bstep (se 1 (by rfl) ⟨1646468, by rfl⟩ : syracuseStep 2195291 = 3292937) B3292937
theorem B11113685 : Blo 2193435 11113685 := bbase (se 7 (by rfl) ⟨130238, by rfl⟩ : syracuseStep 11113685 = 260477) (by norm_num)
theorem B7409123 : Blo 2193435 7409123 := bstep (se 1 (by rfl) ⟨5556842, by rfl⟩ : syracuseStep 7409123 = 11113685) B11113685
theorem B4939415 : Blo 2193435 4939415 := bstep (se 1 (by rfl) ⟨3704561, by rfl⟩ : syracuseStep 4939415 = 7409123) B7409123
theorem B3292943 : Blo 2193435 3292943 := bstep (se 1 (by rfl) ⟨2469707, by rfl⟩ : syracuseStep 3292943 = 4939415) B4939415
theorem B2195295 : Blo 2193435 2195295 := bstep (se 1 (by rfl) ⟨1646471, by rfl⟩ : syracuseStep 2195295 = 3292943) B3292943
theorem B3292949 : Blo 2193435 3292949 := bbase (se 6 (by rfl) ⟨77178, by rfl⟩ : syracuseStep 3292949 = 154357) (by norm_num)
theorem B2195299 : Blo 2193435 2195299 := bstep (se 1 (by rfl) ⟨1646474, by rfl⟩ : syracuseStep 2195299 = 3292949) B3292949
theorem B4224509 : Blo 2193435 4224509 := bbase (se 3 (by rfl) ⟨792095, by rfl⟩ : syracuseStep 4224509 = 1584191) (by norm_num)
theorem B2816339 : Blo 2193435 2816339 := bstep (se 1 (by rfl) ⟨2112254, by rfl⟩ : syracuseStep 2816339 = 4224509) B4224509
theorem B30040949 : Blo 2193435 30040949 := bstep (se 5 (by rfl) ⟨1408169, by rfl⟩ : syracuseStep 30040949 = 2816339) B2816339
theorem B20027299 : Blo 2193435 20027299 := bstep (se 1 (by rfl) ⟨15020474, by rfl⟩ : syracuseStep 20027299 = 30040949) B30040949
theorem B26703065 : Blo 2193435 26703065 := bstep (se 2 (by rfl) ⟨10013649, by rfl⟩ : syracuseStep 26703065 = 20027299) B20027299
theorem B71208173 : Blo 2193435 71208173 := bstep (se 3 (by rfl) ⟨13351532, by rfl⟩ : syracuseStep 71208173 = 26703065) B26703065
theorem B47472115 : Blo 2193435 47472115 := bstep (se 1 (by rfl) ⟨35604086, by rfl⟩ : syracuseStep 47472115 = 71208173) B71208173
theorem B63296153 : Blo 2193435 63296153 := bstep (se 2 (by rfl) ⟨23736057, by rfl⟩ : syracuseStep 63296153 = 47472115) B47472115
theorem B42197435 : Blo 2193435 42197435 := bstep (se 1 (by rfl) ⟨31648076, by rfl⟩ : syracuseStep 42197435 = 63296153) B63296153
theorem B28131623 : Blo 2193435 28131623 := bstep (se 1 (by rfl) ⟨21098717, by rfl⟩ : syracuseStep 28131623 = 42197435) B42197435
theorem B18754415 : Blo 2193435 18754415 := bstep (se 1 (by rfl) ⟨14065811, by rfl⟩ : syracuseStep 18754415 = 28131623) B28131623
theorem B12502943 : Blo 2193435 12502943 := bstep (se 1 (by rfl) ⟨9377207, by rfl⟩ : syracuseStep 12502943 = 18754415) B18754415
theorem B8335295 : Blo 2193435 8335295 := bstep (se 1 (by rfl) ⟨6251471, by rfl⟩ : syracuseStep 8335295 = 12502943) B12502943
theorem B5556863 : Blo 2193435 5556863 := bstep (se 1 (by rfl) ⟨4167647, by rfl⟩ : syracuseStep 5556863 = 8335295) B8335295
theorem B3704575 : Blo 2193435 3704575 := bstep (se 1 (by rfl) ⟨2778431, by rfl⟩ : syracuseStep 3704575 = 5556863) B5556863
theorem B4939433 : Blo 2193435 4939433 := bstep (se 2 (by rfl) ⟨1852287, by rfl⟩ : syracuseStep 4939433 = 3704575) B3704575
theorem B3292955 : Blo 2193435 3292955 := bstep (se 1 (by rfl) ⟨2469716, by rfl⟩ : syracuseStep 3292955 = 4939433) B4939433
theorem B2195303 : Blo 2193435 2195303 := bstep (se 1 (by rfl) ⟨1646477, by rfl⟩ : syracuseStep 2195303 = 3292955) B3292955
theorem B2469721 : Blo 2193435 2469721 := bbase (se 2 (by rfl) ⟨926145, by rfl⟩ : syracuseStep 2469721 = 1852291) (by norm_num)
theorem B3292961 : Blo 2193435 3292961 := bstep (se 2 (by rfl) ⟨1234860, by rfl⟩ : syracuseStep 3292961 = 2469721) B2469721
theorem B2195307 : Blo 2193435 2195307 := bstep (se 1 (by rfl) ⟨1646480, by rfl⟩ : syracuseStep 2195307 = 3292961) B3292961
theorem B4688621 : Blo 2193435 4688621 := bbase (se 3 (by rfl) ⟨879116, by rfl⟩ : syracuseStep 4688621 = 1758233) (by norm_num)
theorem B3125747 : Blo 2193435 3125747 := bstep (se 1 (by rfl) ⟨2344310, by rfl⟩ : syracuseStep 3125747 = 4688621) B4688621
theorem B8335325 : Blo 2193435 8335325 := bstep (se 3 (by rfl) ⟨1562873, by rfl⟩ : syracuseStep 8335325 = 3125747) B3125747
theorem B5556883 : Blo 2193435 5556883 := bstep (se 1 (by rfl) ⟨4167662, by rfl⟩ : syracuseStep 5556883 = 8335325) B8335325
theorem B7409177 : Blo 2193435 7409177 := bstep (se 2 (by rfl) ⟨2778441, by rfl⟩ : syracuseStep 7409177 = 5556883) B5556883
theorem B4939451 : Blo 2193435 4939451 := bstep (se 1 (by rfl) ⟨3704588, by rfl⟩ : syracuseStep 4939451 = 7409177) B7409177
theorem B3292967 : Blo 2193435 3292967 := bstep (se 1 (by rfl) ⟨2469725, by rfl⟩ : syracuseStep 3292967 = 4939451) B4939451
theorem B2195311 : Blo 2193435 2195311 := bstep (se 1 (by rfl) ⟨1646483, by rfl⟩ : syracuseStep 2195311 = 3292967) B3292967
theorem B3292973 : Blo 2193435 3292973 := bbase (se 3 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 3292973 = 1234865) (by norm_num)
theorem B2195315 : Blo 2193435 2195315 := bstep (se 1 (by rfl) ⟨1646486, by rfl⟩ : syracuseStep 2195315 = 3292973) B3292973
theorem B4939469 : Blo 2193435 4939469 := bbase (se 3 (by rfl) ⟨926150, by rfl⟩ : syracuseStep 4939469 = 1852301) (by norm_num)
theorem B3292979 : Blo 2193435 3292979 := bstep (se 1 (by rfl) ⟨2469734, by rfl⟩ : syracuseStep 3292979 = 4939469) B4939469
theorem B2195319 : Blo 2193435 2195319 := bstep (se 1 (by rfl) ⟨1646489, by rfl⟩ : syracuseStep 2195319 = 3292979) B3292979
theorem B2778457 : Blo 2193435 2778457 := bbase (se 2 (by rfl) ⟨1041921, by rfl⟩ : syracuseStep 2778457 = 2083843) (by norm_num)
theorem B3704609 : Blo 2193435 3704609 := bstep (se 2 (by rfl) ⟨1389228, by rfl⟩ : syracuseStep 3704609 = 2778457) B2778457
theorem B2469739 : Blo 2193435 2469739 := bstep (se 1 (by rfl) ⟨1852304, by rfl⟩ : syracuseStep 2469739 = 3704609) B3704609
theorem B3292985 : Blo 2193435 3292985 := bstep (se 2 (by rfl) ⟨1234869, by rfl⟩ : syracuseStep 3292985 = 2469739) B2469739
theorem B2195323 : Blo 2193435 2195323 := bstep (se 1 (by rfl) ⟨1646492, by rfl⟩ : syracuseStep 2195323 = 3292985) B3292985
theorem B3956053 : Blo 2193435 3956053 := bbase (se 11 (by rfl) ⟨2897, by rfl⟩ : syracuseStep 3956053 = 5795) (by norm_num)
theorem B5274737 : Blo 2193435 5274737 := bstep (se 2 (by rfl) ⟨1978026, by rfl⟩ : syracuseStep 5274737 = 3956053) B3956053
theorem B3516491 : Blo 2193435 3516491 := bstep (se 1 (by rfl) ⟨2637368, by rfl⟩ : syracuseStep 3516491 = 5274737) B5274737
theorem B9377309 : Blo 2193435 9377309 := bstep (se 3 (by rfl) ⟨1758245, by rfl⟩ : syracuseStep 9377309 = 3516491) B3516491
theorem B25006157 : Blo 2193435 25006157 := bstep (se 3 (by rfl) ⟨4688654, by rfl⟩ : syracuseStep 25006157 = 9377309) B9377309
theorem B16670771 : Blo 2193435 16670771 := bstep (se 1 (by rfl) ⟨12503078, by rfl⟩ : syracuseStep 16670771 = 25006157) B25006157
theorem B11113847 : Blo 2193435 11113847 := bstep (se 1 (by rfl) ⟨8335385, by rfl⟩ : syracuseStep 11113847 = 16670771) B16670771
theorem B7409231 : Blo 2193435 7409231 := bstep (se 1 (by rfl) ⟨5556923, by rfl⟩ : syracuseStep 7409231 = 11113847) B11113847
theorem B4939487 : Blo 2193435 4939487 := bstep (se 1 (by rfl) ⟨3704615, by rfl⟩ : syracuseStep 4939487 = 7409231) B7409231
theorem B3292991 : Blo 2193435 3292991 := bstep (se 1 (by rfl) ⟨2469743, by rfl⟩ : syracuseStep 3292991 = 4939487) B4939487
theorem B2195327 : Blo 2193435 2195327 := bstep (se 1 (by rfl) ⟨1646495, by rfl⟩ : syracuseStep 2195327 = 3292991) B3292991
theorem B3292997 : Blo 2193435 3292997 := bbase (se 4 (by rfl) ⟨308718, by rfl⟩ : syracuseStep 3292997 = 617437) (by norm_num)
theorem B2195331 : Blo 2193435 2195331 := bstep (se 1 (by rfl) ⟨1646498, by rfl⟩ : syracuseStep 2195331 = 3292997) B3292997
theorem B3704629 : Blo 2193435 3704629 := bbase (se 5 (by rfl) ⟨173654, by rfl⟩ : syracuseStep 3704629 = 347309) (by norm_num)
theorem B4939505 : Blo 2193435 4939505 := bstep (se 2 (by rfl) ⟨1852314, by rfl⟩ : syracuseStep 4939505 = 3704629) B3704629
theorem B3293003 : Blo 2193435 3293003 := bstep (se 1 (by rfl) ⟨2469752, by rfl⟩ : syracuseStep 3293003 = 4939505) B4939505
theorem B2195335 : Blo 2193435 2195335 := bstep (se 1 (by rfl) ⟨1646501, by rfl⟩ : syracuseStep 2195335 = 3293003) B3293003
theorem B2469757 : Blo 2193435 2469757 := bbase (se 3 (by rfl) ⟨463079, by rfl⟩ : syracuseStep 2469757 = 926159) (by norm_num)
theorem B3293009 : Blo 2193435 3293009 := bstep (se 2 (by rfl) ⟨1234878, by rfl⟩ : syracuseStep 3293009 = 2469757) B2469757
theorem B2195339 : Blo 2193435 2195339 := bstep (se 1 (by rfl) ⟨1646504, by rfl⟩ : syracuseStep 2195339 = 3293009) B3293009
theorem B7409285 : Blo 2193435 7409285 := bbase (se 4 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 7409285 = 1389241) (by norm_num)
theorem B4939523 : Blo 2193435 4939523 := bstep (se 1 (by rfl) ⟨3704642, by rfl⟩ : syracuseStep 4939523 = 7409285) B7409285
theorem B3293015 : Blo 2193435 3293015 := bstep (se 1 (by rfl) ⟨2469761, by rfl⟩ : syracuseStep 3293015 = 4939523) B4939523
theorem B2195343 : Blo 2193435 2195343 := bstep (se 1 (by rfl) ⟨1646507, by rfl⟩ : syracuseStep 2195343 = 3293015) B3293015
theorem B3293021 : Blo 2193435 3293021 := bbase (se 3 (by rfl) ⟨617441, by rfl⟩ : syracuseStep 3293021 = 1234883) (by norm_num)
theorem B2195347 : Blo 2193435 2195347 := bstep (se 1 (by rfl) ⟨1646510, by rfl⟩ : syracuseStep 2195347 = 3293021) B3293021
theorem B4939541 : Blo 2193435 4939541 := bbase (se 6 (by rfl) ⟨115770, by rfl⟩ : syracuseStep 4939541 = 231541) (by norm_num)
theorem B3293027 : Blo 2193435 3293027 := bstep (se 1 (by rfl) ⟨2469770, by rfl⟩ : syracuseStep 3293027 = 4939541) B4939541
theorem B2195351 : Blo 2193435 2195351 := bstep (se 1 (by rfl) ⟨1646513, by rfl⟩ : syracuseStep 2195351 = 3293027) B3293027
theorem B8335493 : Blo 2193435 8335493 := bbase (se 4 (by rfl) ⟨781452, by rfl⟩ : syracuseStep 8335493 = 1562905) (by norm_num)
theorem B5556995 : Blo 2193435 5556995 := bstep (se 1 (by rfl) ⟨4167746, by rfl⟩ : syracuseStep 5556995 = 8335493) B8335493
theorem B3704663 : Blo 2193435 3704663 := bstep (se 1 (by rfl) ⟨2778497, by rfl⟩ : syracuseStep 3704663 = 5556995) B5556995
theorem B2469775 : Blo 2193435 2469775 := bstep (se 1 (by rfl) ⟨1852331, by rfl⟩ : syracuseStep 2469775 = 3704663) B3704663
theorem B3293033 : Blo 2193435 3293033 := bstep (se 2 (by rfl) ⟨1234887, by rfl⟩ : syracuseStep 3293033 = 2469775) B2469775
theorem B2195355 : Blo 2193435 2195355 := bstep (se 1 (by rfl) ⟨1646516, by rfl⟩ : syracuseStep 2195355 = 3293033) B3293033
theorem B2503477 : Blo 2193435 2503477 := bbase (se 5 (by rfl) ⟨117350, by rfl⟩ : syracuseStep 2503477 = 234701) (by norm_num)
theorem B13351877 : Blo 2193435 13351877 := bstep (se 4 (by rfl) ⟨1251738, by rfl⟩ : syracuseStep 13351877 = 2503477) B2503477
theorem B8901251 : Blo 2193435 8901251 := bstep (se 1 (by rfl) ⟨6675938, by rfl⟩ : syracuseStep 8901251 = 13351877) B13351877
theorem B5934167 : Blo 2193435 5934167 := bstep (se 1 (by rfl) ⟨4450625, by rfl⟩ : syracuseStep 5934167 = 8901251) B8901251
theorem B3956111 : Blo 2193435 3956111 := bstep (se 1 (by rfl) ⟨2967083, by rfl⟩ : syracuseStep 3956111 = 5934167) B5934167
theorem B2637407 : Blo 2193435 2637407 := bstep (se 1 (by rfl) ⟨1978055, by rfl⟩ : syracuseStep 2637407 = 3956111) B3956111
theorem B7033085 : Blo 2193435 7033085 := bstep (se 3 (by rfl) ⟨1318703, by rfl⟩ : syracuseStep 7033085 = 2637407) B2637407
theorem B4688723 : Blo 2193435 4688723 := bstep (se 1 (by rfl) ⟨3516542, by rfl⟩ : syracuseStep 4688723 = 7033085) B7033085
theorem B12503261 : Blo 2193435 12503261 := bstep (se 3 (by rfl) ⟨2344361, by rfl⟩ : syracuseStep 12503261 = 4688723) B4688723
theorem B8335507 : Blo 2193435 8335507 := bstep (se 1 (by rfl) ⟨6251630, by rfl⟩ : syracuseStep 8335507 = 12503261) B12503261
theorem B11114009 : Blo 2193435 11114009 := bstep (se 2 (by rfl) ⟨4167753, by rfl⟩ : syracuseStep 11114009 = 8335507) B8335507
theorem B7409339 : Blo 2193435 7409339 := bstep (se 1 (by rfl) ⟨5557004, by rfl⟩ : syracuseStep 7409339 = 11114009) B11114009
theorem B4939559 : Blo 2193435 4939559 := bstep (se 1 (by rfl) ⟨3704669, by rfl⟩ : syracuseStep 4939559 = 7409339) B7409339
theorem B3293039 : Blo 2193435 3293039 := bstep (se 1 (by rfl) ⟨2469779, by rfl⟩ : syracuseStep 3293039 = 4939559) B4939559
theorem B2195359 : Blo 2193435 2195359 := bstep (se 1 (by rfl) ⟨1646519, by rfl⟩ : syracuseStep 2195359 = 3293039) B3293039
theorem B3293045 : Blo 2193435 3293045 := bbase (se 5 (by rfl) ⟨154361, by rfl⟩ : syracuseStep 3293045 = 308723) (by norm_num)
theorem B2195363 : Blo 2193435 2195363 := bstep (se 1 (by rfl) ⟨1646522, by rfl⟩ : syracuseStep 2195363 = 3293045) B3293045
theorem B4688741 : Blo 2193435 4688741 := bbase (se 4 (by rfl) ⟨439569, by rfl⟩ : syracuseStep 4688741 = 879139) (by norm_num)
theorem B3125827 : Blo 2193435 3125827 := bstep (se 1 (by rfl) ⟨2344370, by rfl⟩ : syracuseStep 3125827 = 4688741) B4688741
theorem B4167769 : Blo 2193435 4167769 := bstep (se 2 (by rfl) ⟨1562913, by rfl⟩ : syracuseStep 4167769 = 3125827) B3125827
theorem B5557025 : Blo 2193435 5557025 := bstep (se 2 (by rfl) ⟨2083884, by rfl⟩ : syracuseStep 5557025 = 4167769) B4167769
theorem B3704683 : Blo 2193435 3704683 := bstep (se 1 (by rfl) ⟨2778512, by rfl⟩ : syracuseStep 3704683 = 5557025) B5557025
theorem B4939577 : Blo 2193435 4939577 := bstep (se 2 (by rfl) ⟨1852341, by rfl⟩ : syracuseStep 4939577 = 3704683) B3704683
theorem B3293051 : Blo 2193435 3293051 := bstep (se 1 (by rfl) ⟨2469788, by rfl⟩ : syracuseStep 3293051 = 4939577) B4939577
theorem B2195367 : Blo 2193435 2195367 := bstep (se 1 (by rfl) ⟨1646525, by rfl⟩ : syracuseStep 2195367 = 3293051) B3293051
theorem B2469793 : Blo 2193435 2469793 := bbase (se 2 (by rfl) ⟨926172, by rfl⟩ : syracuseStep 2469793 = 1852345) (by norm_num)
theorem B3293057 : Blo 2193435 3293057 := bstep (se 2 (by rfl) ⟨1234896, by rfl⟩ : syracuseStep 3293057 = 2469793) B2469793
theorem B2195371 : Blo 2193435 2195371 := bstep (se 1 (by rfl) ⟨1646528, by rfl⟩ : syracuseStep 2195371 = 3293057) B3293057
theorem B5557045 : Blo 2193435 5557045 := bbase (se 5 (by rfl) ⟨260486, by rfl⟩ : syracuseStep 5557045 = 520973) (by norm_num)
theorem B7409393 : Blo 2193435 7409393 := bstep (se 2 (by rfl) ⟨2778522, by rfl⟩ : syracuseStep 7409393 = 5557045) B5557045
theorem B4939595 : Blo 2193435 4939595 := bstep (se 1 (by rfl) ⟨3704696, by rfl⟩ : syracuseStep 4939595 = 7409393) B7409393
theorem B3293063 : Blo 2193435 3293063 := bstep (se 1 (by rfl) ⟨2469797, by rfl⟩ : syracuseStep 3293063 = 4939595) B4939595
theorem B2195375 : Blo 2193435 2195375 := bstep (se 1 (by rfl) ⟨1646531, by rfl⟩ : syracuseStep 2195375 = 3293063) B3293063
theorem B3293069 : Blo 2193435 3293069 := bbase (se 3 (by rfl) ⟨617450, by rfl⟩ : syracuseStep 3293069 = 1234901) (by norm_num)
theorem B2195379 : Blo 2193435 2195379 := bstep (se 1 (by rfl) ⟨1646534, by rfl⟩ : syracuseStep 2195379 = 3293069) B3293069
theorem B4939613 : Blo 2193435 4939613 := bbase (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) (by norm_num)
theorem B3293075 : Blo 2193435 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B2195383 : Blo 2193435 2195383 := bstep (se 1 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 2195383 = 3293075) B3293075
theorem B3704717 : Blo 2193435 3704717 := bbase (se 3 (by rfl) ⟨694634, by rfl⟩ : syracuseStep 3704717 = 1389269) (by norm_num)
theorem B2469811 : Blo 2193435 2469811 := bstep (se 1 (by rfl) ⟨1852358, by rfl⟩ : syracuseStep 2469811 = 3704717) B3704717
theorem B3293081 : Blo 2193435 3293081 := bstep (se 2 (by rfl) ⟨1234905, by rfl⟩ : syracuseStep 3293081 = 2469811) B2469811
theorem B2195387 : Blo 2193435 2195387 := bstep (se 1 (by rfl) ⟨1646540, by rfl⟩ : syracuseStep 2195387 = 3293081) B3293081
theorem B10549781 : Blo 2193435 10549781 := bbase (se 6 (by rfl) ⟨247260, by rfl⟩ : syracuseStep 10549781 = 494521) (by norm_num)
theorem B7033187 : Blo 2193435 7033187 := bstep (se 1 (by rfl) ⟨5274890, by rfl⟩ : syracuseStep 7033187 = 10549781) B10549781
theorem B18755165 : Blo 2193435 18755165 := bstep (se 3 (by rfl) ⟨3516593, by rfl⟩ : syracuseStep 18755165 = 7033187) B7033187
theorem B12503443 : Blo 2193435 12503443 := bstep (se 1 (by rfl) ⟨9377582, by rfl⟩ : syracuseStep 12503443 = 18755165) B18755165
theorem B16671257 : Blo 2193435 16671257 := bstep (se 2 (by rfl) ⟨6251721, by rfl⟩ : syracuseStep 16671257 = 12503443) B12503443
theorem B11114171 : Blo 2193435 11114171 := bstep (se 1 (by rfl) ⟨8335628, by rfl⟩ : syracuseStep 11114171 = 16671257) B16671257
theorem B7409447 : Blo 2193435 7409447 := bstep (se 1 (by rfl) ⟨5557085, by rfl⟩ : syracuseStep 7409447 = 11114171) B11114171
theorem B4939631 : Blo 2193435 4939631 := bstep (se 1 (by rfl) ⟨3704723, by rfl⟩ : syracuseStep 4939631 = 7409447) B7409447
theorem B3293087 : Blo 2193435 3293087 := bstep (se 1 (by rfl) ⟨2469815, by rfl⟩ : syracuseStep 3293087 = 4939631) B4939631
theorem B2195391 : Blo 2193435 2195391 := bstep (se 1 (by rfl) ⟨1646543, by rfl⟩ : syracuseStep 2195391 = 3293087) B3293087
theorem B3293093 : Blo 2193435 3293093 := bbase (se 4 (by rfl) ⟨308727, by rfl⟩ : syracuseStep 3293093 = 617455) (by norm_num)
theorem B2195395 : Blo 2193435 2195395 := bstep (se 1 (by rfl) ⟨1646546, by rfl⟩ : syracuseStep 2195395 = 3293093) B3293093
theorem B2778553 : Blo 2193435 2778553 := bbase (se 2 (by rfl) ⟨1041957, by rfl⟩ : syracuseStep 2778553 = 2083915) (by norm_num)
theorem B3704737 : Blo 2193435 3704737 := bstep (se 2 (by rfl) ⟨1389276, by rfl⟩ : syracuseStep 3704737 = 2778553) B2778553
theorem B4939649 : Blo 2193435 4939649 := bstep (se 2 (by rfl) ⟨1852368, by rfl⟩ : syracuseStep 4939649 = 3704737) B3704737
theorem B3293099 : Blo 2193435 3293099 := bstep (se 1 (by rfl) ⟨2469824, by rfl⟩ : syracuseStep 3293099 = 4939649) B4939649
theorem B2195399 : Blo 2193435 2195399 := bstep (se 1 (by rfl) ⟨1646549, by rfl⟩ : syracuseStep 2195399 = 3293099) B3293099
theorem B2469829 : Blo 2193435 2469829 := bbase (se 4 (by rfl) ⟨231546, by rfl⟩ : syracuseStep 2469829 = 463093) (by norm_num)
theorem B3293105 : Blo 2193435 3293105 := bstep (se 2 (by rfl) ⟨1234914, by rfl⟩ : syracuseStep 3293105 = 2469829) B2469829
theorem B2195403 : Blo 2193435 2195403 := bstep (se 1 (by rfl) ⟨1646552, by rfl⟩ : syracuseStep 2195403 = 3293105) B3293105
theorem B4167845 : Blo 2193435 4167845 := bbase (se 4 (by rfl) ⟨390735, by rfl⟩ : syracuseStep 4167845 = 781471) (by norm_num)
theorem B2778563 : Blo 2193435 2778563 := bstep (se 1 (by rfl) ⟨2083922, by rfl⟩ : syracuseStep 2778563 = 4167845) B4167845
theorem B7409501 : Blo 2193435 7409501 := bstep (se 3 (by rfl) ⟨1389281, by rfl⟩ : syracuseStep 7409501 = 2778563) B2778563
theorem B4939667 : Blo 2193435 4939667 := bstep (se 1 (by rfl) ⟨3704750, by rfl⟩ : syracuseStep 4939667 = 7409501) B7409501
theorem B3293111 : Blo 2193435 3293111 := bstep (se 1 (by rfl) ⟨2469833, by rfl⟩ : syracuseStep 3293111 = 4939667) B4939667
theorem B2195407 : Blo 2193435 2195407 := bstep (se 1 (by rfl) ⟨1646555, by rfl⟩ : syracuseStep 2195407 = 3293111) B3293111
theorem B3293117 : Blo 2193435 3293117 := bbase (se 3 (by rfl) ⟨617459, by rfl⟩ : syracuseStep 3293117 = 1234919) (by norm_num)
theorem B2195411 : Blo 2193435 2195411 := bstep (se 1 (by rfl) ⟨1646558, by rfl⟩ : syracuseStep 2195411 = 3293117) B3293117
theorem B4939685 : Blo 2193435 4939685 := bbase (se 4 (by rfl) ⟨463095, by rfl⟩ : syracuseStep 4939685 = 926191) (by norm_num)
theorem B3293123 : Blo 2193435 3293123 := bstep (se 1 (by rfl) ⟨2469842, by rfl⟩ : syracuseStep 3293123 = 4939685) B4939685
theorem B2195415 : Blo 2193435 2195415 := bstep (se 1 (by rfl) ⟨1646561, by rfl⟩ : syracuseStep 2195415 = 3293123) B3293123
theorem B5557157 : Blo 2193435 5557157 := bbase (se 4 (by rfl) ⟨520983, by rfl⟩ : syracuseStep 5557157 = 1041967) (by norm_num)
theorem B3704771 : Blo 2193435 3704771 := bstep (se 1 (by rfl) ⟨2778578, by rfl⟩ : syracuseStep 3704771 = 5557157) B5557157
theorem B2469847 : Blo 2193435 2469847 := bstep (se 1 (by rfl) ⟨1852385, by rfl⟩ : syracuseStep 2469847 = 3704771) B3704771
theorem B3293129 : Blo 2193435 3293129 := bstep (se 2 (by rfl) ⟨1234923, by rfl⟩ : syracuseStep 3293129 = 2469847) B2469847
theorem B2195419 : Blo 2193435 2195419 := bstep (se 1 (by rfl) ⟨1646564, by rfl⟩ : syracuseStep 2195419 = 3293129) B3293129
theorem B6251813 : Blo 2193435 6251813 := bbase (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) (by norm_num)
theorem B4167875 : Blo 2193435 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B11114333 : Blo 2193435 11114333 := bstep (se 3 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 11114333 = 4167875) B4167875
theorem B7409555 : Blo 2193435 7409555 := bstep (se 1 (by rfl) ⟨5557166, by rfl⟩ : syracuseStep 7409555 = 11114333) B11114333
theorem B4939703 : Blo 2193435 4939703 := bstep (se 1 (by rfl) ⟨3704777, by rfl⟩ : syracuseStep 4939703 = 7409555) B7409555
theorem B3293135 : Blo 2193435 3293135 := bstep (se 1 (by rfl) ⟨2469851, by rfl⟩ : syracuseStep 3293135 = 4939703) B4939703
theorem B2195423 : Blo 2193435 2195423 := bstep (se 1 (by rfl) ⟨1646567, by rfl⟩ : syracuseStep 2195423 = 3293135) B3293135
theorem B3293141 : Blo 2193435 3293141 := bbase (se 7 (by rfl) ⟨38591, by rfl⟩ : syracuseStep 3293141 = 77183) (by norm_num)
theorem B2195427 : Blo 2193435 2195427 := bstep (se 1 (by rfl) ⟨1646570, by rfl⟩ : syracuseStep 2195427 = 3293141) B3293141
theorem B8335781 : Blo 2193435 8335781 := bbase (se 4 (by rfl) ⟨781479, by rfl⟩ : syracuseStep 8335781 = 1562959) (by norm_num)
theorem B5557187 : Blo 2193435 5557187 := bstep (se 1 (by rfl) ⟨4167890, by rfl⟩ : syracuseStep 5557187 = 8335781) B8335781
theorem B3704791 : Blo 2193435 3704791 := bstep (se 1 (by rfl) ⟨2778593, by rfl⟩ : syracuseStep 3704791 = 5557187) B5557187
theorem B4939721 : Blo 2193435 4939721 := bstep (se 2 (by rfl) ⟨1852395, by rfl⟩ : syracuseStep 4939721 = 3704791) B3704791
theorem B3293147 : Blo 2193435 3293147 := bstep (se 1 (by rfl) ⟨2469860, by rfl⟩ : syracuseStep 3293147 = 4939721) B4939721
theorem B2195431 : Blo 2193435 2195431 := bstep (se 1 (by rfl) ⟨1646573, by rfl⟩ : syracuseStep 2195431 = 3293147) B3293147
theorem B2469865 : Blo 2193435 2469865 := bbase (se 2 (by rfl) ⟨926199, by rfl⟩ : syracuseStep 2469865 = 1852399) (by norm_num)
theorem B3293153 : Blo 2193435 3293153 := bstep (se 2 (by rfl) ⟨1234932, by rfl⟩ : syracuseStep 3293153 = 2469865) B2469865
theorem B2195435 : Blo 2193435 2195435 := bstep (se 1 (by rfl) ⟨1646576, by rfl⟩ : syracuseStep 2195435 = 3293153) B3293153
theorem C0 (j : ℕ) (h1 : 548358 ≤ j) (h2 : j ≤ 548858) : Blo 2193435 (4 * j + 3) := by
  interval_cases j
  · exact B2193435
  · exact B2193439
  · exact B2193443
  · exact B2193447
  · exact B2193451
  · exact B2193455
  · exact B2193459
  · exact B2193463
  · exact B2193467
  · exact B2193471
  · exact B2193475
  · exact B2193479
  · exact B2193483
  · exact B2193487
  · exact B2193491
  · exact B2193495
  · exact B2193499
  · exact B2193503
  · exact B2193507
  · exact B2193511
  · exact B2193515
  · exact B2193519
  · exact B2193523
  · exact B2193527
  · exact B2193531
  · exact B2193535
  · exact B2193539
  · exact B2193543
  · exact B2193547
  · exact B2193551
  · exact B2193555
  · exact B2193559
  · exact B2193563
  · exact B2193567
  · exact B2193571
  · exact B2193575
  · exact B2193579
  · exact B2193583
  · exact B2193587
  · exact B2193591
  · exact B2193595
  · exact B2193599
  · exact B2193603
  · exact B2193607
  · exact B2193611
  · exact B2193615
  · exact B2193619
  · exact B2193623
  · exact B2193627
  · exact B2193631
  · exact B2193635
  · exact B2193639
  · exact B2193643
  · exact B2193647
  · exact B2193651
  · exact B2193655
  · exact B2193659
  · exact B2193663
  · exact B2193667
  · exact B2193671
  · exact B2193675
  · exact B2193679
  · exact B2193683
  · exact B2193687
  · exact B2193691
  · exact B2193695
  · exact B2193699
  · exact B2193703
  · exact B2193707
  · exact B2193711
  · exact B2193715
  · exact B2193719
  · exact B2193723
  · exact B2193727
  · exact B2193731
  · exact B2193735
  · exact B2193739
  · exact B2193743
  · exact B2193747
  · exact B2193751
  · exact B2193755
  · exact B2193759
  · exact B2193763
  · exact B2193767
  · exact B2193771
  · exact B2193775
  · exact B2193779
  · exact B2193783
  · exact B2193787
  · exact B2193791
  · exact B2193795
  · exact B2193799
  · exact B2193803
  · exact B2193807
  · exact B2193811
  · exact B2193815
  · exact B2193819
  · exact B2193823
  · exact B2193827
  · exact B2193831
  · exact B2193835
  · exact B2193839
  · exact B2193843
  · exact B2193847
  · exact B2193851
  · exact B2193855
  · exact B2193859
  · exact B2193863
  · exact B2193867
  · exact B2193871
  · exact B2193875
  · exact B2193879
  · exact B2193883
  · exact B2193887
  · exact B2193891
  · exact B2193895
  · exact B2193899
  · exact B2193903
  · exact B2193907
  · exact B2193911
  · exact B2193915
  · exact B2193919
  · exact B2193923
  · exact B2193927
  · exact B2193931
  · exact B2193935
  · exact B2193939
  · exact B2193943
  · exact B2193947
  · exact B2193951
  · exact B2193955
  · exact B2193959
  · exact B2193963
  · exact B2193967
  · exact B2193971
  · exact B2193975
  · exact B2193979
  · exact B2193983
  · exact B2193987
  · exact B2193991
  · exact B2193995
  · exact B2193999
  · exact B2194003
  · exact B2194007
  · exact B2194011
  · exact B2194015
  · exact B2194019
  · exact B2194023
  · exact B2194027
  · exact B2194031
  · exact B2194035
  · exact B2194039
  · exact B2194043
  · exact B2194047
  · exact B2194051
  · exact B2194055
  · exact B2194059
  · exact B2194063
  · exact B2194067
  · exact B2194071
  · exact B2194075
  · exact B2194079
  · exact B2194083
  · exact B2194087
  · exact B2194091
  · exact B2194095
  · exact B2194099
  · exact B2194103
  · exact B2194107
  · exact B2194111
  · exact B2194115
  · exact B2194119
  · exact B2194123
  · exact B2194127
  · exact B2194131
  · exact B2194135
  · exact B2194139
  · exact B2194143
  · exact B2194147
  · exact B2194151
  · exact B2194155
  · exact B2194159
  · exact B2194163
  · exact B2194167
  · exact B2194171
  · exact B2194175
  · exact B2194179
  · exact B2194183
  · exact B2194187
  · exact B2194191
  · exact B2194195
  · exact B2194199
  · exact B2194203
  · exact B2194207
  · exact B2194211
  · exact B2194215
  · exact B2194219
  · exact B2194223
  · exact B2194227
  · exact B2194231
  · exact B2194235
  · exact B2194239
  · exact B2194243
  · exact B2194247
  · exact B2194251
  · exact B2194255
  · exact B2194259
  · exact B2194263
  · exact B2194267
  · exact B2194271
  · exact B2194275
  · exact B2194279
  · exact B2194283
  · exact B2194287
  · exact B2194291
  · exact B2194295
  · exact B2194299
  · exact B2194303
  · exact B2194307
  · exact B2194311
  · exact B2194315
  · exact B2194319
  · exact B2194323
  · exact B2194327
  · exact B2194331
  · exact B2194335
  · exact B2194339
  · exact B2194343
  · exact B2194347
  · exact B2194351
  · exact B2194355
  · exact B2194359
  · exact B2194363
  · exact B2194367
  · exact B2194371
  · exact B2194375
  · exact B2194379
  · exact B2194383
  · exact B2194387
  · exact B2194391
  · exact B2194395
  · exact B2194399
  · exact B2194403
  · exact B2194407
  · exact B2194411
  · exact B2194415
  · exact B2194419
  · exact B2194423
  · exact B2194427
  · exact B2194431
  · exact B2194435
  · exact B2194439
  · exact B2194443
  · exact B2194447
  · exact B2194451
  · exact B2194455
  · exact B2194459
  · exact B2194463
  · exact B2194467
  · exact B2194471
  · exact B2194475
  · exact B2194479
  · exact B2194483
  · exact B2194487
  · exact B2194491
  · exact B2194495
  · exact B2194499
  · exact B2194503
  · exact B2194507
  · exact B2194511
  · exact B2194515
  · exact B2194519
  · exact B2194523
  · exact B2194527
  · exact B2194531
  · exact B2194535
  · exact B2194539
  · exact B2194543
  · exact B2194547
  · exact B2194551
  · exact B2194555
  · exact B2194559
  · exact B2194563
  · exact B2194567
  · exact B2194571
  · exact B2194575
  · exact B2194579
  · exact B2194583
  · exact B2194587
  · exact B2194591
  · exact B2194595
  · exact B2194599
  · exact B2194603
  · exact B2194607
  · exact B2194611
  · exact B2194615
  · exact B2194619
  · exact B2194623
  · exact B2194627
  · exact B2194631
  · exact B2194635
  · exact B2194639
  · exact B2194643
  · exact B2194647
  · exact B2194651
  · exact B2194655
  · exact B2194659
  · exact B2194663
  · exact B2194667
  · exact B2194671
  · exact B2194675
  · exact B2194679
  · exact B2194683
  · exact B2194687
  · exact B2194691
  · exact B2194695
  · exact B2194699
  · exact B2194703
  · exact B2194707
  · exact B2194711
  · exact B2194715
  · exact B2194719
  · exact B2194723
  · exact B2194727
  · exact B2194731
  · exact B2194735
  · exact B2194739
  · exact B2194743
  · exact B2194747
  · exact B2194751
  · exact B2194755
  · exact B2194759
  · exact B2194763
  · exact B2194767
  · exact B2194771
  · exact B2194775
  · exact B2194779
  · exact B2194783
  · exact B2194787
  · exact B2194791
  · exact B2194795
  · exact B2194799
  · exact B2194803
  · exact B2194807
  · exact B2194811
  · exact B2194815
  · exact B2194819
  · exact B2194823
  · exact B2194827
  · exact B2194831
  · exact B2194835
  · exact B2194839
  · exact B2194843
  · exact B2194847
  · exact B2194851
  · exact B2194855
  · exact B2194859
  · exact B2194863
  · exact B2194867
  · exact B2194871
  · exact B2194875
  · exact B2194879
  · exact B2194883
  · exact B2194887
  · exact B2194891
  · exact B2194895
  · exact B2194899
  · exact B2194903
  · exact B2194907
  · exact B2194911
  · exact B2194915
  · exact B2194919
  · exact B2194923
  · exact B2194927
  · exact B2194931
  · exact B2194935
  · exact B2194939
  · exact B2194943
  · exact B2194947
  · exact B2194951
  · exact B2194955
  · exact B2194959
  · exact B2194963
  · exact B2194967
  · exact B2194971
  · exact B2194975
  · exact B2194979
  · exact B2194983
  · exact B2194987
  · exact B2194991
  · exact B2194995
  · exact B2194999
  · exact B2195003
  · exact B2195007
  · exact B2195011
  · exact B2195015
  · exact B2195019
  · exact B2195023
  · exact B2195027
  · exact B2195031
  · exact B2195035
  · exact B2195039
  · exact B2195043
  · exact B2195047
  · exact B2195051
  · exact B2195055
  · exact B2195059
  · exact B2195063
  · exact B2195067
  · exact B2195071
  · exact B2195075
  · exact B2195079
  · exact B2195083
  · exact B2195087
  · exact B2195091
  · exact B2195095
  · exact B2195099
  · exact B2195103
  · exact B2195107
  · exact B2195111
  · exact B2195115
  · exact B2195119
  · exact B2195123
  · exact B2195127
  · exact B2195131
  · exact B2195135
  · exact B2195139
  · exact B2195143
  · exact B2195147
  · exact B2195151
  · exact B2195155
  · exact B2195159
  · exact B2195163
  · exact B2195167
  · exact B2195171
  · exact B2195175
  · exact B2195179
  · exact B2195183
  · exact B2195187
  · exact B2195191
  · exact B2195195
  · exact B2195199
  · exact B2195203
  · exact B2195207
  · exact B2195211
  · exact B2195215
  · exact B2195219
  · exact B2195223
  · exact B2195227
  · exact B2195231
  · exact B2195235
  · exact B2195239
  · exact B2195243
  · exact B2195247
  · exact B2195251
  · exact B2195255
  · exact B2195259
  · exact B2195263
  · exact B2195267
  · exact B2195271
  · exact B2195275
  · exact B2195279
  · exact B2195283
  · exact B2195287
  · exact B2195291
  · exact B2195295
  · exact B2195299
  · exact B2195303
  · exact B2195307
  · exact B2195311
  · exact B2195315
  · exact B2195319
  · exact B2195323
  · exact B2195327
  · exact B2195331
  · exact B2195335
  · exact B2195339
  · exact B2195343
  · exact B2195347
  · exact B2195351
  · exact B2195355
  · exact B2195359
  · exact B2195363
  · exact B2195367
  · exact B2195371
  · exact B2195375
  · exact B2195379
  · exact B2195383
  · exact B2195387
  · exact B2195391
  · exact B2195395
  · exact B2195399
  · exact B2195403
  · exact B2195407
  · exact B2195411
  · exact B2195415
  · exact B2195419
  · exact B2195423
  · exact B2195427
  · exact B2195431
  · exact B2195435
theorem solution (m : ℕ) (hlo : 2193435 ≤ m) (hhi : m ≤ 2195435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 548358 ≤ j := by omega
    have hj2 : j ≤ 548858 := by omega
    have hb : Blo 2193435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
