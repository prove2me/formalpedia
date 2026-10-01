-- Prove2me | solution 1 for syracuse_descends_range_2129435_2131435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:05.746496+00:00
-- url     : https://prove2.me/submissions/beaf90d2-34f5-4595-bd7b-0f3b19a6ecbe

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

theorem B10232837 : Blo 2129435 10232837 := bbase (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) (by norm_num)
theorem B6821891 : Blo 2129435 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B4547927 : Blo 2129435 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B12127805 : Blo 2129435 12127805 := bstep (se 3 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 12127805 = 4547927) B4547927
theorem B8085203 : Blo 2129435 8085203 := bstep (se 1 (by rfl) ⟨6063902, by rfl⟩ : syracuseStep 8085203 = 12127805) B12127805
theorem B5390135 : Blo 2129435 5390135 := bstep (se 1 (by rfl) ⟨4042601, by rfl⟩ : syracuseStep 5390135 = 8085203) B8085203
theorem B3593423 : Blo 2129435 3593423 := bstep (se 1 (by rfl) ⟨2695067, by rfl⟩ : syracuseStep 3593423 = 5390135) B5390135
theorem B2395615 : Blo 2129435 2395615 := bstep (se 1 (by rfl) ⟨1796711, by rfl⟩ : syracuseStep 2395615 = 3593423) B3593423
theorem B3194153 : Blo 2129435 3194153 := bstep (se 2 (by rfl) ⟨1197807, by rfl⟩ : syracuseStep 3194153 = 2395615) B2395615
theorem B2129435 : Blo 2129435 2129435 := bstep (se 1 (by rfl) ⟨1597076, by rfl⟩ : syracuseStep 2129435 = 3194153) B3194153
theorem B2158493 : Blo 2129435 2158493 := bbase (se 3 (by rfl) ⟨404717, by rfl⟩ : syracuseStep 2158493 = 809435) (by norm_num)
theorem B23023925 : Blo 2129435 23023925 := bstep (se 5 (by rfl) ⟨1079246, by rfl⟩ : syracuseStep 23023925 = 2158493) B2158493
theorem B15349283 : Blo 2129435 15349283 := bstep (se 1 (by rfl) ⟨11511962, by rfl⟩ : syracuseStep 15349283 = 23023925) B23023925
theorem B10232855 : Blo 2129435 10232855 := bstep (se 1 (by rfl) ⟨7674641, by rfl⟩ : syracuseStep 10232855 = 15349283) B15349283
theorem B6821903 : Blo 2129435 6821903 := bstep (se 1 (by rfl) ⟨5116427, by rfl⟩ : syracuseStep 6821903 = 10232855) B10232855
theorem B4547935 : Blo 2129435 4547935 := bstep (se 1 (by rfl) ⟨3410951, by rfl⟩ : syracuseStep 4547935 = 6821903) B6821903
theorem B6063913 : Blo 2129435 6063913 := bstep (se 2 (by rfl) ⟨2273967, by rfl⟩ : syracuseStep 6063913 = 4547935) B4547935
theorem B8085217 : Blo 2129435 8085217 := bstep (se 2 (by rfl) ⟨3031956, by rfl⟩ : syracuseStep 8085217 = 6063913) B6063913
theorem B10780289 : Blo 2129435 10780289 := bstep (se 2 (by rfl) ⟨4042608, by rfl⟩ : syracuseStep 10780289 = 8085217) B8085217
theorem B7186859 : Blo 2129435 7186859 := bstep (se 1 (by rfl) ⟨5390144, by rfl⟩ : syracuseStep 7186859 = 10780289) B10780289
theorem B4791239 : Blo 2129435 4791239 := bstep (se 1 (by rfl) ⟨3593429, by rfl⟩ : syracuseStep 4791239 = 7186859) B7186859
theorem B3194159 : Blo 2129435 3194159 := bstep (se 1 (by rfl) ⟨2395619, by rfl⟩ : syracuseStep 3194159 = 4791239) B4791239
theorem B2129439 : Blo 2129435 2129439 := bstep (se 1 (by rfl) ⟨1597079, by rfl⟩ : syracuseStep 2129439 = 3194159) B3194159
theorem B3194165 : Blo 2129435 3194165 := bbase (se 5 (by rfl) ⟨149726, by rfl⟩ : syracuseStep 3194165 = 299453) (by norm_num)
theorem B2129443 : Blo 2129435 2129443 := bstep (se 1 (by rfl) ⟨1597082, by rfl⟩ : syracuseStep 2129443 = 3194165) B3194165
theorem B5390165 : Blo 2129435 5390165 := bbase (se 9 (by rfl) ⟨15791, by rfl⟩ : syracuseStep 5390165 = 31583) (by norm_num)
theorem B3593443 : Blo 2129435 3593443 := bstep (se 1 (by rfl) ⟨2695082, by rfl⟩ : syracuseStep 3593443 = 5390165) B5390165
theorem B4791257 : Blo 2129435 4791257 := bstep (se 2 (by rfl) ⟨1796721, by rfl⟩ : syracuseStep 4791257 = 3593443) B3593443
theorem B3194171 : Blo 2129435 3194171 := bstep (se 1 (by rfl) ⟨2395628, by rfl⟩ : syracuseStep 3194171 = 4791257) B4791257
theorem B2129447 : Blo 2129435 2129447 := bstep (se 1 (by rfl) ⟨1597085, by rfl⟩ : syracuseStep 2129447 = 3194171) B3194171
theorem B2395633 : Blo 2129435 2395633 := bbase (se 2 (by rfl) ⟨898362, by rfl⟩ : syracuseStep 2395633 = 1796725) (by norm_num)
theorem B3194177 : Blo 2129435 3194177 := bstep (se 2 (by rfl) ⟨1197816, by rfl⟩ : syracuseStep 3194177 = 2395633) B2395633
theorem B2129451 : Blo 2129435 2129451 := bstep (se 1 (by rfl) ⟨1597088, by rfl⟩ : syracuseStep 2129451 = 3194177) B3194177
theorem B2558233 : Blo 2129435 2558233 := bbase (se 2 (by rfl) ⟨959337, by rfl⟩ : syracuseStep 2558233 = 1918675) (by norm_num)
theorem B13643909 : Blo 2129435 13643909 := bstep (se 4 (by rfl) ⟨1279116, by rfl⟩ : syracuseStep 13643909 = 2558233) B2558233
theorem B9095939 : Blo 2129435 9095939 := bstep (se 1 (by rfl) ⟨6821954, by rfl⟩ : syracuseStep 9095939 = 13643909) B13643909
theorem B6063959 : Blo 2129435 6063959 := bstep (se 1 (by rfl) ⟨4547969, by rfl⟩ : syracuseStep 6063959 = 9095939) B9095939
theorem B4042639 : Blo 2129435 4042639 := bstep (se 1 (by rfl) ⟨3031979, by rfl⟩ : syracuseStep 4042639 = 6063959) B6063959
theorem B5390185 : Blo 2129435 5390185 := bstep (se 2 (by rfl) ⟨2021319, by rfl⟩ : syracuseStep 5390185 = 4042639) B4042639
theorem B7186913 : Blo 2129435 7186913 := bstep (se 2 (by rfl) ⟨2695092, by rfl⟩ : syracuseStep 7186913 = 5390185) B5390185
theorem B4791275 : Blo 2129435 4791275 := bstep (se 1 (by rfl) ⟨3593456, by rfl⟩ : syracuseStep 4791275 = 7186913) B7186913
theorem B3194183 : Blo 2129435 3194183 := bstep (se 1 (by rfl) ⟨2395637, by rfl⟩ : syracuseStep 3194183 = 4791275) B4791275
theorem B2129455 : Blo 2129435 2129455 := bstep (se 1 (by rfl) ⟨1597091, by rfl⟩ : syracuseStep 2129455 = 3194183) B3194183
theorem B3194189 : Blo 2129435 3194189 := bbase (se 3 (by rfl) ⟨598910, by rfl⟩ : syracuseStep 3194189 = 1197821) (by norm_num)
theorem B2129459 : Blo 2129435 2129459 := bstep (se 1 (by rfl) ⟨1597094, by rfl⟩ : syracuseStep 2129459 = 3194189) B3194189
theorem B4791293 : Blo 2129435 4791293 := bbase (se 3 (by rfl) ⟨898367, by rfl⟩ : syracuseStep 4791293 = 1796735) (by norm_num)
theorem B3194195 : Blo 2129435 3194195 := bstep (se 1 (by rfl) ⟨2395646, by rfl⟩ : syracuseStep 3194195 = 4791293) B4791293
theorem B2129463 : Blo 2129435 2129463 := bstep (se 1 (by rfl) ⟨1597097, by rfl⟩ : syracuseStep 2129463 = 3194195) B3194195
theorem B3593477 : Blo 2129435 3593477 := bbase (se 4 (by rfl) ⟨336888, by rfl⟩ : syracuseStep 3593477 = 673777) (by norm_num)
theorem B2395651 : Blo 2129435 2395651 := bstep (se 1 (by rfl) ⟨1796738, by rfl⟩ : syracuseStep 2395651 = 3593477) B3593477
theorem B3194201 : Blo 2129435 3194201 := bstep (se 2 (by rfl) ⟨1197825, by rfl⟩ : syracuseStep 3194201 = 2395651) B2395651
theorem B2129467 : Blo 2129435 2129467 := bstep (se 1 (by rfl) ⟨1597100, by rfl⟩ : syracuseStep 2129467 = 3194201) B3194201
theorem B16170677 : Blo 2129435 16170677 := bbase (se 5 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 16170677 = 1516001) (by norm_num)
theorem B10780451 : Blo 2129435 10780451 := bstep (se 1 (by rfl) ⟨8085338, by rfl⟩ : syracuseStep 10780451 = 16170677) B16170677
theorem B7186967 : Blo 2129435 7186967 := bstep (se 1 (by rfl) ⟨5390225, by rfl⟩ : syracuseStep 7186967 = 10780451) B10780451
theorem B4791311 : Blo 2129435 4791311 := bstep (se 1 (by rfl) ⟨3593483, by rfl⟩ : syracuseStep 4791311 = 7186967) B7186967
theorem B3194207 : Blo 2129435 3194207 := bstep (se 1 (by rfl) ⟨2395655, by rfl⟩ : syracuseStep 3194207 = 4791311) B4791311
theorem B2129471 : Blo 2129435 2129471 := bstep (se 1 (by rfl) ⟨1597103, by rfl⟩ : syracuseStep 2129471 = 3194207) B3194207
theorem B3194213 : Blo 2129435 3194213 := bbase (se 4 (by rfl) ⟨299457, by rfl⟩ : syracuseStep 3194213 = 598915) (by norm_num)
theorem B2129475 : Blo 2129435 2129475 := bstep (se 1 (by rfl) ⟨1597106, by rfl⟩ : syracuseStep 2129475 = 3194213) B3194213
theorem B4042685 : Blo 2129435 4042685 := bbase (se 3 (by rfl) ⟨758003, by rfl⟩ : syracuseStep 4042685 = 1516007) (by norm_num)
theorem B2695123 : Blo 2129435 2695123 := bstep (se 1 (by rfl) ⟨2021342, by rfl⟩ : syracuseStep 2695123 = 4042685) B4042685
theorem B3593497 : Blo 2129435 3593497 := bstep (se 2 (by rfl) ⟨1347561, by rfl⟩ : syracuseStep 3593497 = 2695123) B2695123
theorem B4791329 : Blo 2129435 4791329 := bstep (se 2 (by rfl) ⟨1796748, by rfl⟩ : syracuseStep 4791329 = 3593497) B3593497
theorem B3194219 : Blo 2129435 3194219 := bstep (se 1 (by rfl) ⟨2395664, by rfl⟩ : syracuseStep 3194219 = 4791329) B4791329
theorem B2129479 : Blo 2129435 2129479 := bstep (se 1 (by rfl) ⟨1597109, by rfl⟩ : syracuseStep 2129479 = 3194219) B3194219
theorem B2395669 : Blo 2129435 2395669 := bbase (se 6 (by rfl) ⟨56148, by rfl⟩ : syracuseStep 2395669 = 112297) (by norm_num)
theorem B3194225 : Blo 2129435 3194225 := bstep (se 2 (by rfl) ⟨1197834, by rfl⟩ : syracuseStep 3194225 = 2395669) B2395669
theorem B2129483 : Blo 2129435 2129483 := bstep (se 1 (by rfl) ⟨1597112, by rfl⟩ : syracuseStep 2129483 = 3194225) B3194225
theorem B2695133 : Blo 2129435 2695133 := bbase (se 3 (by rfl) ⟨505337, by rfl⟩ : syracuseStep 2695133 = 1010675) (by norm_num)
theorem B7187021 : Blo 2129435 7187021 := bstep (se 3 (by rfl) ⟨1347566, by rfl⟩ : syracuseStep 7187021 = 2695133) B2695133
theorem B4791347 : Blo 2129435 4791347 := bstep (se 1 (by rfl) ⟨3593510, by rfl⟩ : syracuseStep 4791347 = 7187021) B7187021
theorem B3194231 : Blo 2129435 3194231 := bstep (se 1 (by rfl) ⟨2395673, by rfl⟩ : syracuseStep 3194231 = 4791347) B4791347
theorem B2129487 : Blo 2129435 2129487 := bstep (se 1 (by rfl) ⟨1597115, by rfl⟩ : syracuseStep 2129487 = 3194231) B3194231
theorem B3194237 : Blo 2129435 3194237 := bbase (se 3 (by rfl) ⟨598919, by rfl⟩ : syracuseStep 3194237 = 1197839) (by norm_num)
theorem B2129491 : Blo 2129435 2129491 := bstep (se 1 (by rfl) ⟨1597118, by rfl⟩ : syracuseStep 2129491 = 3194237) B3194237
theorem B4791365 : Blo 2129435 4791365 := bbase (se 4 (by rfl) ⟨449190, by rfl⟩ : syracuseStep 4791365 = 898381) (by norm_num)
theorem B3194243 : Blo 2129435 3194243 := bstep (se 1 (by rfl) ⟨2395682, by rfl⟩ : syracuseStep 3194243 = 4791365) B4791365
theorem B2129495 : Blo 2129435 2129495 := bstep (se 1 (by rfl) ⟨1597121, by rfl⟩ : syracuseStep 2129495 = 3194243) B3194243
theorem B6064085 : Blo 2129435 6064085 := bbase (se 7 (by rfl) ⟨71063, by rfl⟩ : syracuseStep 6064085 = 142127) (by norm_num)
theorem B4042723 : Blo 2129435 4042723 := bstep (se 1 (by rfl) ⟨3032042, by rfl⟩ : syracuseStep 4042723 = 6064085) B6064085
theorem B5390297 : Blo 2129435 5390297 := bstep (se 2 (by rfl) ⟨2021361, by rfl⟩ : syracuseStep 5390297 = 4042723) B4042723
theorem B3593531 : Blo 2129435 3593531 := bstep (se 1 (by rfl) ⟨2695148, by rfl⟩ : syracuseStep 3593531 = 5390297) B5390297
theorem B2395687 : Blo 2129435 2395687 := bstep (se 1 (by rfl) ⟨1796765, by rfl⟩ : syracuseStep 2395687 = 3593531) B3593531
theorem B3194249 : Blo 2129435 3194249 := bstep (se 2 (by rfl) ⟨1197843, by rfl⟩ : syracuseStep 3194249 = 2395687) B2395687
theorem B2129499 : Blo 2129435 2129499 := bstep (se 1 (by rfl) ⟨1597124, by rfl⟩ : syracuseStep 2129499 = 3194249) B3194249
theorem B10780613 : Blo 2129435 10780613 := bbase (se 4 (by rfl) ⟨1010682, by rfl⟩ : syracuseStep 10780613 = 2021365) (by norm_num)
theorem B7187075 : Blo 2129435 7187075 := bstep (se 1 (by rfl) ⟨5390306, by rfl⟩ : syracuseStep 7187075 = 10780613) B10780613
theorem B4791383 : Blo 2129435 4791383 := bstep (se 1 (by rfl) ⟨3593537, by rfl⟩ : syracuseStep 4791383 = 7187075) B7187075
theorem B3194255 : Blo 2129435 3194255 := bstep (se 1 (by rfl) ⟨2395691, by rfl⟩ : syracuseStep 3194255 = 4791383) B4791383
theorem B2129503 : Blo 2129435 2129503 := bstep (se 1 (by rfl) ⟨1597127, by rfl⟩ : syracuseStep 2129503 = 3194255) B3194255
theorem B3194261 : Blo 2129435 3194261 := bbase (se 6 (by rfl) ⟨74865, by rfl⟩ : syracuseStep 3194261 = 149731) (by norm_num)
theorem B2129507 : Blo 2129435 2129507 := bstep (se 1 (by rfl) ⟨1597130, by rfl⟩ : syracuseStep 2129507 = 3194261) B3194261
theorem B4317133 : Blo 2129435 4317133 := bbase (se 3 (by rfl) ⟨809462, by rfl⟩ : syracuseStep 4317133 = 1618925) (by norm_num)
theorem B5756177 : Blo 2129435 5756177 := bstep (se 2 (by rfl) ⟨2158566, by rfl⟩ : syracuseStep 5756177 = 4317133) B4317133
theorem B3837451 : Blo 2129435 3837451 := bstep (se 1 (by rfl) ⟨2878088, by rfl⟩ : syracuseStep 3837451 = 5756177) B5756177
theorem B5116601 : Blo 2129435 5116601 := bstep (se 2 (by rfl) ⟨1918725, by rfl⟩ : syracuseStep 5116601 = 3837451) B3837451
theorem B3411067 : Blo 2129435 3411067 := bstep (se 1 (by rfl) ⟨2558300, by rfl⟩ : syracuseStep 3411067 = 5116601) B5116601
theorem B4548089 : Blo 2129435 4548089 := bstep (se 2 (by rfl) ⟨1705533, by rfl⟩ : syracuseStep 4548089 = 3411067) B3411067
theorem B12128237 : Blo 2129435 12128237 := bstep (se 3 (by rfl) ⟨2274044, by rfl⟩ : syracuseStep 12128237 = 4548089) B4548089
theorem B8085491 : Blo 2129435 8085491 := bstep (se 1 (by rfl) ⟨6064118, by rfl⟩ : syracuseStep 8085491 = 12128237) B12128237
theorem B5390327 : Blo 2129435 5390327 := bstep (se 1 (by rfl) ⟨4042745, by rfl⟩ : syracuseStep 5390327 = 8085491) B8085491
theorem B3593551 : Blo 2129435 3593551 := bstep (se 1 (by rfl) ⟨2695163, by rfl⟩ : syracuseStep 3593551 = 5390327) B5390327
theorem B4791401 : Blo 2129435 4791401 := bstep (se 2 (by rfl) ⟨1796775, by rfl⟩ : syracuseStep 4791401 = 3593551) B3593551
theorem B3194267 : Blo 2129435 3194267 := bstep (se 1 (by rfl) ⟨2395700, by rfl⟩ : syracuseStep 3194267 = 4791401) B4791401
theorem B2129511 : Blo 2129435 2129511 := bstep (se 1 (by rfl) ⟨1597133, by rfl⟩ : syracuseStep 2129511 = 3194267) B3194267
theorem B2395705 : Blo 2129435 2395705 := bbase (se 2 (by rfl) ⟨898389, by rfl⟩ : syracuseStep 2395705 = 1796779) (by norm_num)
theorem B3194273 : Blo 2129435 3194273 := bstep (se 2 (by rfl) ⟨1197852, by rfl⟩ : syracuseStep 3194273 = 2395705) B2395705
theorem B2129515 : Blo 2129435 2129515 := bstep (se 1 (by rfl) ⟨1597136, by rfl⟩ : syracuseStep 2129515 = 3194273) B3194273
theorem B2274053 : Blo 2129435 2274053 := bbase (se 4 (by rfl) ⟨213192, by rfl⟩ : syracuseStep 2274053 = 426385) (by norm_num)
theorem B6064141 : Blo 2129435 6064141 := bstep (se 3 (by rfl) ⟨1137026, by rfl⟩ : syracuseStep 6064141 = 2274053) B2274053
theorem B8085521 : Blo 2129435 8085521 := bstep (se 2 (by rfl) ⟨3032070, by rfl⟩ : syracuseStep 8085521 = 6064141) B6064141
theorem B5390347 : Blo 2129435 5390347 := bstep (se 1 (by rfl) ⟨4042760, by rfl⟩ : syracuseStep 5390347 = 8085521) B8085521
theorem B7187129 : Blo 2129435 7187129 := bstep (se 2 (by rfl) ⟨2695173, by rfl⟩ : syracuseStep 7187129 = 5390347) B5390347
theorem B4791419 : Blo 2129435 4791419 := bstep (se 1 (by rfl) ⟨3593564, by rfl⟩ : syracuseStep 4791419 = 7187129) B7187129
theorem B3194279 : Blo 2129435 3194279 := bstep (se 1 (by rfl) ⟨2395709, by rfl⟩ : syracuseStep 3194279 = 4791419) B4791419
theorem B2129519 : Blo 2129435 2129519 := bstep (se 1 (by rfl) ⟨1597139, by rfl⟩ : syracuseStep 2129519 = 3194279) B3194279
theorem B3194285 : Blo 2129435 3194285 := bbase (se 3 (by rfl) ⟨598928, by rfl⟩ : syracuseStep 3194285 = 1197857) (by norm_num)
theorem B2129523 : Blo 2129435 2129523 := bstep (se 1 (by rfl) ⟨1597142, by rfl⟩ : syracuseStep 2129523 = 3194285) B3194285
theorem B4791437 : Blo 2129435 4791437 := bbase (se 3 (by rfl) ⟨898394, by rfl⟩ : syracuseStep 4791437 = 1796789) (by norm_num)
theorem B3194291 : Blo 2129435 3194291 := bstep (se 1 (by rfl) ⟨2395718, by rfl⟩ : syracuseStep 3194291 = 4791437) B4791437
theorem B2129527 : Blo 2129435 2129527 := bstep (se 1 (by rfl) ⟨1597145, by rfl⟩ : syracuseStep 2129527 = 3194291) B3194291
theorem B2695189 : Blo 2129435 2695189 := bbase (se 6 (by rfl) ⟨63168, by rfl⟩ : syracuseStep 2695189 = 126337) (by norm_num)
theorem B3593585 : Blo 2129435 3593585 := bstep (se 2 (by rfl) ⟨1347594, by rfl⟩ : syracuseStep 3593585 = 2695189) B2695189
theorem B2395723 : Blo 2129435 2395723 := bstep (se 1 (by rfl) ⟨1796792, by rfl⟩ : syracuseStep 2395723 = 3593585) B3593585
theorem B3194297 : Blo 2129435 3194297 := bstep (se 2 (by rfl) ⟨1197861, by rfl⟩ : syracuseStep 3194297 = 2395723) B2395723
theorem B2129531 : Blo 2129435 2129531 := bstep (se 1 (by rfl) ⟨1597148, by rfl⟩ : syracuseStep 2129531 = 3194297) B3194297
theorem B6230789 : Blo 2129435 6230789 := bbase (se 4 (by rfl) ⟨584136, by rfl⟩ : syracuseStep 6230789 = 1168273) (by norm_num)
theorem B4153859 : Blo 2129435 4153859 := bstep (se 1 (by rfl) ⟨3115394, by rfl⟩ : syracuseStep 4153859 = 6230789) B6230789
theorem B2769239 : Blo 2129435 2769239 := bstep (se 1 (by rfl) ⟨2076929, by rfl⟩ : syracuseStep 2769239 = 4153859) B4153859
theorem B7384637 : Blo 2129435 7384637 := bstep (se 3 (by rfl) ⟨1384619, by rfl⟩ : syracuseStep 7384637 = 2769239) B2769239
theorem B4923091 : Blo 2129435 4923091 := bstep (se 1 (by rfl) ⟨3692318, by rfl⟩ : syracuseStep 4923091 = 7384637) B7384637
theorem B6564121 : Blo 2129435 6564121 := bstep (se 2 (by rfl) ⟨2461545, by rfl⟩ : syracuseStep 6564121 = 4923091) B4923091
theorem B140034581 : Blo 2129435 140034581 := bstep (se 6 (by rfl) ⟨3282060, by rfl⟩ : syracuseStep 140034581 = 6564121) B6564121
theorem B93356387 : Blo 2129435 93356387 := bstep (se 1 (by rfl) ⟨70017290, by rfl⟩ : syracuseStep 93356387 = 140034581) B140034581
theorem B62237591 : Blo 2129435 62237591 := bstep (se 1 (by rfl) ⟨46678193, by rfl⟩ : syracuseStep 62237591 = 93356387) B93356387
theorem B41491727 : Blo 2129435 41491727 := bstep (se 1 (by rfl) ⟨31118795, by rfl⟩ : syracuseStep 41491727 = 62237591) B62237591
theorem B27661151 : Blo 2129435 27661151 := bstep (se 1 (by rfl) ⟨20745863, by rfl⟩ : syracuseStep 27661151 = 41491727) B41491727
theorem B18440767 : Blo 2129435 18440767 := bstep (se 1 (by rfl) ⟨13830575, by rfl⟩ : syracuseStep 18440767 = 27661151) B27661151
theorem B98350757 : Blo 2129435 98350757 := bstep (se 4 (by rfl) ⟨9220383, by rfl⟩ : syracuseStep 98350757 = 18440767) B18440767
theorem B65567171 : Blo 2129435 65567171 := bstep (se 1 (by rfl) ⟨49175378, by rfl⟩ : syracuseStep 65567171 = 98350757) B98350757
theorem B43711447 : Blo 2129435 43711447 := bstep (se 1 (by rfl) ⟨32783585, by rfl⟩ : syracuseStep 43711447 = 65567171) B65567171
theorem B58281929 : Blo 2129435 58281929 := bstep (se 2 (by rfl) ⟨21855723, by rfl⟩ : syracuseStep 58281929 = 43711447) B43711447
theorem B38854619 : Blo 2129435 38854619 := bstep (se 1 (by rfl) ⟨29140964, by rfl⟩ : syracuseStep 38854619 = 58281929) B58281929
theorem B25903079 : Blo 2129435 25903079 := bstep (se 1 (by rfl) ⟨19427309, by rfl⟩ : syracuseStep 25903079 = 38854619) B38854619
theorem B17268719 : Blo 2129435 17268719 := bstep (se 1 (by rfl) ⟨12951539, by rfl⟩ : syracuseStep 17268719 = 25903079) B25903079
theorem B46049917 : Blo 2129435 46049917 := bstep (se 3 (by rfl) ⟨8634359, by rfl⟩ : syracuseStep 46049917 = 17268719) B17268719
theorem B61399889 : Blo 2129435 61399889 := bstep (se 2 (by rfl) ⟨23024958, by rfl⟩ : syracuseStep 61399889 = 46049917) B46049917
theorem B40933259 : Blo 2129435 40933259 := bstep (se 1 (by rfl) ⟨30699944, by rfl⟩ : syracuseStep 40933259 = 61399889) B61399889
theorem B27288839 : Blo 2129435 27288839 := bstep (se 1 (by rfl) ⟨20466629, by rfl⟩ : syracuseStep 27288839 = 40933259) B40933259
theorem B18192559 : Blo 2129435 18192559 := bstep (se 1 (by rfl) ⟨13644419, by rfl⟩ : syracuseStep 18192559 = 27288839) B27288839
theorem B24256745 : Blo 2129435 24256745 := bstep (se 2 (by rfl) ⟨9096279, by rfl⟩ : syracuseStep 24256745 = 18192559) B18192559
theorem B16171163 : Blo 2129435 16171163 := bstep (se 1 (by rfl) ⟨12128372, by rfl⟩ : syracuseStep 16171163 = 24256745) B24256745
theorem B10780775 : Blo 2129435 10780775 := bstep (se 1 (by rfl) ⟨8085581, by rfl⟩ : syracuseStep 10780775 = 16171163) B16171163
theorem B7187183 : Blo 2129435 7187183 := bstep (se 1 (by rfl) ⟨5390387, by rfl⟩ : syracuseStep 7187183 = 10780775) B10780775
theorem B4791455 : Blo 2129435 4791455 := bstep (se 1 (by rfl) ⟨3593591, by rfl⟩ : syracuseStep 4791455 = 7187183) B7187183
theorem B3194303 : Blo 2129435 3194303 := bstep (se 1 (by rfl) ⟨2395727, by rfl⟩ : syracuseStep 3194303 = 4791455) B4791455
theorem B2129535 : Blo 2129435 2129535 := bstep (se 1 (by rfl) ⟨1597151, by rfl⟩ : syracuseStep 2129535 = 3194303) B3194303
theorem B3194309 : Blo 2129435 3194309 := bbase (se 4 (by rfl) ⟨299466, by rfl⟩ : syracuseStep 3194309 = 598933) (by norm_num)
theorem B2129539 : Blo 2129435 2129539 := bstep (se 1 (by rfl) ⟨1597154, by rfl⟩ : syracuseStep 2129539 = 3194309) B3194309
theorem B3593605 : Blo 2129435 3593605 := bbase (se 4 (by rfl) ⟨336900, by rfl⟩ : syracuseStep 3593605 = 673801) (by norm_num)
theorem B4791473 : Blo 2129435 4791473 := bstep (se 2 (by rfl) ⟨1796802, by rfl⟩ : syracuseStep 4791473 = 3593605) B3593605
theorem B3194315 : Blo 2129435 3194315 := bstep (se 1 (by rfl) ⟨2395736, by rfl⟩ : syracuseStep 3194315 = 4791473) B4791473
theorem B2129543 : Blo 2129435 2129543 := bstep (se 1 (by rfl) ⟨1597157, by rfl⟩ : syracuseStep 2129543 = 3194315) B3194315
theorem B2395741 : Blo 2129435 2395741 := bbase (se 3 (by rfl) ⟨449201, by rfl⟩ : syracuseStep 2395741 = 898403) (by norm_num)
theorem B3194321 : Blo 2129435 3194321 := bstep (se 2 (by rfl) ⟨1197870, by rfl⟩ : syracuseStep 3194321 = 2395741) B2395741
theorem B2129547 : Blo 2129435 2129547 := bstep (se 1 (by rfl) ⟨1597160, by rfl⟩ : syracuseStep 2129547 = 3194321) B3194321
theorem B7187237 : Blo 2129435 7187237 := bbase (se 4 (by rfl) ⟨673803, by rfl⟩ : syracuseStep 7187237 = 1347607) (by norm_num)
theorem B4791491 : Blo 2129435 4791491 := bstep (se 1 (by rfl) ⟨3593618, by rfl⟩ : syracuseStep 4791491 = 7187237) B7187237
theorem B3194327 : Blo 2129435 3194327 := bstep (se 1 (by rfl) ⟨2395745, by rfl⟩ : syracuseStep 3194327 = 4791491) B4791491
theorem B2129551 : Blo 2129435 2129551 := bstep (se 1 (by rfl) ⟨1597163, by rfl⟩ : syracuseStep 2129551 = 3194327) B3194327
theorem B3194333 : Blo 2129435 3194333 := bbase (se 3 (by rfl) ⟨598937, by rfl⟩ : syracuseStep 3194333 = 1197875) (by norm_num)
theorem B2129555 : Blo 2129435 2129555 := bstep (se 1 (by rfl) ⟨1597166, by rfl⟩ : syracuseStep 2129555 = 3194333) B3194333
theorem B4791509 : Blo 2129435 4791509 := bbase (se 7 (by rfl) ⟨56150, by rfl⟩ : syracuseStep 4791509 = 112301) (by norm_num)
theorem B3194339 : Blo 2129435 3194339 := bstep (se 1 (by rfl) ⟨2395754, by rfl⟩ : syracuseStep 3194339 = 4791509) B4791509
theorem B2129559 : Blo 2129435 2129559 := bstep (se 1 (by rfl) ⟨1597169, by rfl⟩ : syracuseStep 2129559 = 3194339) B3194339
theorem B5538557 : Blo 2129435 5538557 := bbase (se 3 (by rfl) ⟨1038479, by rfl⟩ : syracuseStep 5538557 = 2076959) (by norm_num)
theorem B14769485 : Blo 2129435 14769485 := bstep (se 3 (by rfl) ⟨2769278, by rfl⟩ : syracuseStep 14769485 = 5538557) B5538557
theorem B9846323 : Blo 2129435 9846323 := bstep (se 1 (by rfl) ⟨7384742, by rfl⟩ : syracuseStep 9846323 = 14769485) B14769485
theorem B6564215 : Blo 2129435 6564215 := bstep (se 1 (by rfl) ⟨4923161, by rfl⟩ : syracuseStep 6564215 = 9846323) B9846323
theorem B4376143 : Blo 2129435 4376143 := bstep (se 1 (by rfl) ⟨3282107, by rfl⟩ : syracuseStep 4376143 = 6564215) B6564215
theorem B5834857 : Blo 2129435 5834857 := bstep (se 2 (by rfl) ⟨2188071, by rfl⟩ : syracuseStep 5834857 = 4376143) B4376143
theorem B7779809 : Blo 2129435 7779809 := bstep (se 2 (by rfl) ⟨2917428, by rfl⟩ : syracuseStep 7779809 = 5834857) B5834857
theorem B5186539 : Blo 2129435 5186539 := bstep (se 1 (by rfl) ⟨3889904, by rfl⟩ : syracuseStep 5186539 = 7779809) B7779809
theorem B6915385 : Blo 2129435 6915385 := bstep (se 2 (by rfl) ⟨2593269, by rfl⟩ : syracuseStep 6915385 = 5186539) B5186539
theorem B9220513 : Blo 2129435 9220513 := bstep (se 2 (by rfl) ⟨3457692, by rfl⟩ : syracuseStep 9220513 = 6915385) B6915385
theorem B12294017 : Blo 2129435 12294017 := bstep (se 2 (by rfl) ⟨4610256, by rfl⟩ : syracuseStep 12294017 = 9220513) B9220513
theorem B8196011 : Blo 2129435 8196011 := bstep (se 1 (by rfl) ⟨6147008, by rfl⟩ : syracuseStep 8196011 = 12294017) B12294017
theorem B5464007 : Blo 2129435 5464007 := bstep (se 1 (by rfl) ⟨4098005, by rfl⟩ : syracuseStep 5464007 = 8196011) B8196011
theorem B3642671 : Blo 2129435 3642671 := bstep (se 1 (by rfl) ⟨2732003, by rfl⟩ : syracuseStep 3642671 = 5464007) B5464007
theorem B9713789 : Blo 2129435 9713789 := bstep (se 3 (by rfl) ⟨1821335, by rfl⟩ : syracuseStep 9713789 = 3642671) B3642671
theorem B6475859 : Blo 2129435 6475859 := bstep (se 1 (by rfl) ⟨4856894, by rfl⟩ : syracuseStep 6475859 = 9713789) B9713789
theorem B4317239 : Blo 2129435 4317239 := bstep (se 1 (by rfl) ⟨3237929, by rfl⟩ : syracuseStep 4317239 = 6475859) B6475859
theorem B2878159 : Blo 2129435 2878159 := bstep (se 1 (by rfl) ⟨2158619, by rfl⟩ : syracuseStep 2878159 = 4317239) B4317239
theorem B3837545 : Blo 2129435 3837545 := bstep (se 2 (by rfl) ⟨1439079, by rfl⟩ : syracuseStep 3837545 = 2878159) B2878159
theorem B2558363 : Blo 2129435 2558363 := bstep (se 1 (by rfl) ⟨1918772, by rfl⟩ : syracuseStep 2558363 = 3837545) B3837545
theorem B6822301 : Blo 2129435 6822301 := bstep (se 3 (by rfl) ⟨1279181, by rfl⟩ : syracuseStep 6822301 = 2558363) B2558363
theorem B9096401 : Blo 2129435 9096401 := bstep (se 2 (by rfl) ⟨3411150, by rfl⟩ : syracuseStep 9096401 = 6822301) B6822301
theorem B6064267 : Blo 2129435 6064267 := bstep (se 1 (by rfl) ⟨4548200, by rfl⟩ : syracuseStep 6064267 = 9096401) B9096401
theorem B8085689 : Blo 2129435 8085689 := bstep (se 2 (by rfl) ⟨3032133, by rfl⟩ : syracuseStep 8085689 = 6064267) B6064267
theorem B5390459 : Blo 2129435 5390459 := bstep (se 1 (by rfl) ⟨4042844, by rfl⟩ : syracuseStep 5390459 = 8085689) B8085689
theorem B3593639 : Blo 2129435 3593639 := bstep (se 1 (by rfl) ⟨2695229, by rfl⟩ : syracuseStep 3593639 = 5390459) B5390459
theorem B2395759 : Blo 2129435 2395759 := bstep (se 1 (by rfl) ⟨1796819, by rfl⟩ : syracuseStep 2395759 = 3593639) B3593639
theorem B3194345 : Blo 2129435 3194345 := bstep (se 2 (by rfl) ⟨1197879, by rfl⟩ : syracuseStep 3194345 = 2395759) B2395759
theorem B2129563 : Blo 2129435 2129563 := bstep (se 1 (by rfl) ⟨1597172, by rfl⟩ : syracuseStep 2129563 = 3194345) B3194345
theorem B10373093 : Blo 2129435 10373093 := bbase (se 4 (by rfl) ⟨972477, by rfl⟩ : syracuseStep 10373093 = 1944955) (by norm_num)
theorem B6915395 : Blo 2129435 6915395 := bstep (se 1 (by rfl) ⟨5186546, by rfl⟩ : syracuseStep 6915395 = 10373093) B10373093
theorem B4610263 : Blo 2129435 4610263 := bstep (se 1 (by rfl) ⟨3457697, by rfl⟩ : syracuseStep 4610263 = 6915395) B6915395
theorem B6147017 : Blo 2129435 6147017 := bstep (se 2 (by rfl) ⟨2305131, by rfl⟩ : syracuseStep 6147017 = 4610263) B4610263
theorem B4098011 : Blo 2129435 4098011 := bstep (se 1 (by rfl) ⟨3073508, by rfl⟩ : syracuseStep 4098011 = 6147017) B6147017
theorem B10928029 : Blo 2129435 10928029 := bstep (se 3 (by rfl) ⟨2049005, by rfl⟩ : syracuseStep 10928029 = 4098011) B4098011
theorem B14570705 : Blo 2129435 14570705 := bstep (se 2 (by rfl) ⟨5464014, by rfl⟩ : syracuseStep 14570705 = 10928029) B10928029
theorem B9713803 : Blo 2129435 9713803 := bstep (se 1 (by rfl) ⟨7285352, by rfl⟩ : syracuseStep 9713803 = 14570705) B14570705
theorem B12951737 : Blo 2129435 12951737 := bstep (se 2 (by rfl) ⟨4856901, by rfl⟩ : syracuseStep 12951737 = 9713803) B9713803
theorem B8634491 : Blo 2129435 8634491 := bstep (se 1 (by rfl) ⟨6475868, by rfl⟩ : syracuseStep 8634491 = 12951737) B12951737
theorem B5756327 : Blo 2129435 5756327 := bstep (se 1 (by rfl) ⟨4317245, by rfl⟩ : syracuseStep 5756327 = 8634491) B8634491
theorem B3837551 : Blo 2129435 3837551 := bstep (se 1 (by rfl) ⟨2878163, by rfl⟩ : syracuseStep 3837551 = 5756327) B5756327
theorem B10233469 : Blo 2129435 10233469 := bstep (se 3 (by rfl) ⟨1918775, by rfl⟩ : syracuseStep 10233469 = 3837551) B3837551
theorem B13644625 : Blo 2129435 13644625 := bstep (se 2 (by rfl) ⟨5116734, by rfl⟩ : syracuseStep 13644625 = 10233469) B10233469
theorem B18192833 : Blo 2129435 18192833 := bstep (se 2 (by rfl) ⟨6822312, by rfl⟩ : syracuseStep 18192833 = 13644625) B13644625
theorem B12128555 : Blo 2129435 12128555 := bstep (se 1 (by rfl) ⟨9096416, by rfl⟩ : syracuseStep 12128555 = 18192833) B18192833
theorem B8085703 : Blo 2129435 8085703 := bstep (se 1 (by rfl) ⟨6064277, by rfl⟩ : syracuseStep 8085703 = 12128555) B12128555
theorem B10780937 : Blo 2129435 10780937 := bstep (se 2 (by rfl) ⟨4042851, by rfl⟩ : syracuseStep 10780937 = 8085703) B8085703
theorem B7187291 : Blo 2129435 7187291 := bstep (se 1 (by rfl) ⟨5390468, by rfl⟩ : syracuseStep 7187291 = 10780937) B10780937
theorem B4791527 : Blo 2129435 4791527 := bstep (se 1 (by rfl) ⟨3593645, by rfl⟩ : syracuseStep 4791527 = 7187291) B7187291
theorem B3194351 : Blo 2129435 3194351 := bstep (se 1 (by rfl) ⟨2395763, by rfl⟩ : syracuseStep 3194351 = 4791527) B4791527
theorem B2129567 : Blo 2129435 2129567 := bstep (se 1 (by rfl) ⟨1597175, by rfl⟩ : syracuseStep 2129567 = 3194351) B3194351
theorem B3194357 : Blo 2129435 3194357 := bbase (se 5 (by rfl) ⟨149735, by rfl⟩ : syracuseStep 3194357 = 299471) (by norm_num)
theorem B2129571 : Blo 2129435 2129571 := bstep (se 1 (by rfl) ⟨1597178, by rfl⟩ : syracuseStep 2129571 = 3194357) B3194357
theorem B2274113 : Blo 2129435 2274113 := bbase (se 2 (by rfl) ⟨852792, by rfl⟩ : syracuseStep 2274113 = 1705585) (by norm_num)
theorem B6064301 : Blo 2129435 6064301 := bstep (se 3 (by rfl) ⟨1137056, by rfl⟩ : syracuseStep 6064301 = 2274113) B2274113
theorem B4042867 : Blo 2129435 4042867 := bstep (se 1 (by rfl) ⟨3032150, by rfl⟩ : syracuseStep 4042867 = 6064301) B6064301
theorem B5390489 : Blo 2129435 5390489 := bstep (se 2 (by rfl) ⟨2021433, by rfl⟩ : syracuseStep 5390489 = 4042867) B4042867
theorem B3593659 : Blo 2129435 3593659 := bstep (se 1 (by rfl) ⟨2695244, by rfl⟩ : syracuseStep 3593659 = 5390489) B5390489
theorem B4791545 : Blo 2129435 4791545 := bstep (se 2 (by rfl) ⟨1796829, by rfl⟩ : syracuseStep 4791545 = 3593659) B3593659
theorem B3194363 : Blo 2129435 3194363 := bstep (se 1 (by rfl) ⟨2395772, by rfl⟩ : syracuseStep 3194363 = 4791545) B4791545
theorem B2129575 : Blo 2129435 2129575 := bstep (se 1 (by rfl) ⟨1597181, by rfl⟩ : syracuseStep 2129575 = 3194363) B3194363
theorem B2395777 : Blo 2129435 2395777 := bbase (se 2 (by rfl) ⟨898416, by rfl⟩ : syracuseStep 2395777 = 1796833) (by norm_num)
theorem B3194369 : Blo 2129435 3194369 := bstep (se 2 (by rfl) ⟨1197888, by rfl⟩ : syracuseStep 3194369 = 2395777) B2395777
theorem B2129579 : Blo 2129435 2129579 := bstep (se 1 (by rfl) ⟨1597184, by rfl⟩ : syracuseStep 2129579 = 3194369) B3194369
theorem B5390509 : Blo 2129435 5390509 := bbase (se 3 (by rfl) ⟨1010720, by rfl⟩ : syracuseStep 5390509 = 2021441) (by norm_num)
theorem B7187345 : Blo 2129435 7187345 := bstep (se 2 (by rfl) ⟨2695254, by rfl⟩ : syracuseStep 7187345 = 5390509) B5390509
theorem B4791563 : Blo 2129435 4791563 := bstep (se 1 (by rfl) ⟨3593672, by rfl⟩ : syracuseStep 4791563 = 7187345) B7187345
theorem B3194375 : Blo 2129435 3194375 := bstep (se 1 (by rfl) ⟨2395781, by rfl⟩ : syracuseStep 3194375 = 4791563) B4791563
theorem B2129583 : Blo 2129435 2129583 := bstep (se 1 (by rfl) ⟨1597187, by rfl⟩ : syracuseStep 2129583 = 3194375) B3194375
theorem B3194381 : Blo 2129435 3194381 := bbase (se 3 (by rfl) ⟨598946, by rfl⟩ : syracuseStep 3194381 = 1197893) (by norm_num)
theorem B2129587 : Blo 2129435 2129587 := bstep (se 1 (by rfl) ⟨1597190, by rfl⟩ : syracuseStep 2129587 = 3194381) B3194381
theorem B4791581 : Blo 2129435 4791581 := bbase (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) (by norm_num)
theorem B3194387 : Blo 2129435 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B2129591 : Blo 2129435 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B3593693 : Blo 2129435 3593693 := bbase (se 3 (by rfl) ⟨673817, by rfl⟩ : syracuseStep 3593693 = 1347635) (by norm_num)
theorem B2395795 : Blo 2129435 2395795 := bstep (se 1 (by rfl) ⟨1796846, by rfl⟩ : syracuseStep 2395795 = 3593693) B3593693
theorem B3194393 : Blo 2129435 3194393 := bstep (se 2 (by rfl) ⟨1197897, by rfl⟩ : syracuseStep 3194393 = 2395795) B2395795
theorem B2129595 : Blo 2129435 2129595 := bstep (se 1 (by rfl) ⟨1597196, by rfl⟩ : syracuseStep 2129595 = 3194393) B3194393
theorem B4610333 : Blo 2129435 4610333 := bbase (se 3 (by rfl) ⟨864437, by rfl⟩ : syracuseStep 4610333 = 1728875) (by norm_num)
theorem B3073555 : Blo 2129435 3073555 := bstep (se 1 (by rfl) ⟨2305166, by rfl⟩ : syracuseStep 3073555 = 4610333) B4610333
theorem B16392293 : Blo 2129435 16392293 := bstep (se 4 (by rfl) ⟨1536777, by rfl⟩ : syracuseStep 16392293 = 3073555) B3073555
theorem B10928195 : Blo 2129435 10928195 := bstep (se 1 (by rfl) ⟨8196146, by rfl⟩ : syracuseStep 10928195 = 16392293) B16392293
theorem B7285463 : Blo 2129435 7285463 := bstep (se 1 (by rfl) ⟨5464097, by rfl⟩ : syracuseStep 7285463 = 10928195) B10928195
theorem B4856975 : Blo 2129435 4856975 := bstep (se 1 (by rfl) ⟨3642731, by rfl⟩ : syracuseStep 4856975 = 7285463) B7285463
theorem B3237983 : Blo 2129435 3237983 := bstep (se 1 (by rfl) ⟨2428487, by rfl⟩ : syracuseStep 3237983 = 4856975) B4856975
theorem B2158655 : Blo 2129435 2158655 := bstep (se 1 (by rfl) ⟨1618991, by rfl⟩ : syracuseStep 2158655 = 3237983) B3237983
theorem B23025653 : Blo 2129435 23025653 := bstep (se 5 (by rfl) ⟨1079327, by rfl⟩ : syracuseStep 23025653 = 2158655) B2158655
theorem B15350435 : Blo 2129435 15350435 := bstep (se 1 (by rfl) ⟨11512826, by rfl⟩ : syracuseStep 15350435 = 23025653) B23025653
theorem B10233623 : Blo 2129435 10233623 := bstep (se 1 (by rfl) ⟨7675217, by rfl⟩ : syracuseStep 10233623 = 15350435) B15350435
theorem B6822415 : Blo 2129435 6822415 := bstep (se 1 (by rfl) ⟨5116811, by rfl⟩ : syracuseStep 6822415 = 10233623) B10233623
theorem B9096553 : Blo 2129435 9096553 := bstep (se 2 (by rfl) ⟨3411207, by rfl⟩ : syracuseStep 9096553 = 6822415) B6822415
theorem B12128737 : Blo 2129435 12128737 := bstep (se 2 (by rfl) ⟨4548276, by rfl⟩ : syracuseStep 12128737 = 9096553) B9096553
theorem B16171649 : Blo 2129435 16171649 := bstep (se 2 (by rfl) ⟨6064368, by rfl⟩ : syracuseStep 16171649 = 12128737) B12128737
theorem B10781099 : Blo 2129435 10781099 := bstep (se 1 (by rfl) ⟨8085824, by rfl⟩ : syracuseStep 10781099 = 16171649) B16171649
theorem B7187399 : Blo 2129435 7187399 := bstep (se 1 (by rfl) ⟨5390549, by rfl⟩ : syracuseStep 7187399 = 10781099) B10781099
theorem B4791599 : Blo 2129435 4791599 := bstep (se 1 (by rfl) ⟨3593699, by rfl⟩ : syracuseStep 4791599 = 7187399) B7187399
theorem B3194399 : Blo 2129435 3194399 := bstep (se 1 (by rfl) ⟨2395799, by rfl⟩ : syracuseStep 3194399 = 4791599) B4791599
theorem B2129599 : Blo 2129435 2129599 := bstep (se 1 (by rfl) ⟨1597199, by rfl⟩ : syracuseStep 2129599 = 3194399) B3194399
theorem B3194405 : Blo 2129435 3194405 := bbase (se 4 (by rfl) ⟨299475, by rfl⟩ : syracuseStep 3194405 = 598951) (by norm_num)
theorem B2129603 : Blo 2129435 2129603 := bstep (se 1 (by rfl) ⟨1597202, by rfl⟩ : syracuseStep 2129603 = 3194405) B3194405
theorem B2695285 : Blo 2129435 2695285 := bbase (se 5 (by rfl) ⟨126341, by rfl⟩ : syracuseStep 2695285 = 252683) (by norm_num)
theorem B3593713 : Blo 2129435 3593713 := bstep (se 2 (by rfl) ⟨1347642, by rfl⟩ : syracuseStep 3593713 = 2695285) B2695285
theorem B4791617 : Blo 2129435 4791617 := bstep (se 2 (by rfl) ⟨1796856, by rfl⟩ : syracuseStep 4791617 = 3593713) B3593713
theorem B3194411 : Blo 2129435 3194411 := bstep (se 1 (by rfl) ⟨2395808, by rfl⟩ : syracuseStep 3194411 = 4791617) B4791617
theorem B2129607 : Blo 2129435 2129607 := bstep (se 1 (by rfl) ⟨1597205, by rfl⟩ : syracuseStep 2129607 = 3194411) B3194411
theorem B2395813 : Blo 2129435 2395813 := bbase (se 4 (by rfl) ⟨224607, by rfl⟩ : syracuseStep 2395813 = 449215) (by norm_num)
theorem B3194417 : Blo 2129435 3194417 := bstep (se 2 (by rfl) ⟨1197906, by rfl⟩ : syracuseStep 3194417 = 2395813) B2395813
theorem B2129611 : Blo 2129435 2129611 := bstep (se 1 (by rfl) ⟨1597208, by rfl⟩ : syracuseStep 2129611 = 3194417) B3194417
theorem B8536277 : Blo 2129435 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B22763405 : Blo 2129435 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B15175603 : Blo 2129435 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B20234137 : Blo 2129435 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B26978849 : Blo 2129435 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B17985899 : Blo 2129435 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B47962397 : Blo 2129435 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B31974931 : Blo 2129435 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B170532965 : Blo 2129435 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B113688643 : Blo 2129435 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B151584857 : Blo 2129435 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B101056571 : Blo 2129435 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B67371047 : Blo 2129435 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B44914031 : Blo 2129435 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B29942687 : Blo 2129435 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B79847165 : Blo 2129435 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B212925773 : Blo 2129435 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B141950515 : Blo 2129435 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B189267353 : Blo 2129435 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B126178235 : Blo 2129435 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B84118823 : Blo 2129435 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B56079215 : Blo 2129435 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B37386143 : Blo 2129435 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B24924095 : Blo 2129435 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B16616063 : Blo 2129435 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B44309501 : Blo 2129435 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B29539667 : Blo 2129435 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B78772445 : Blo 2129435 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B52514963 : Blo 2129435 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B35009975 : Blo 2129435 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B23339983 : Blo 2129435 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B31119977 : Blo 2129435 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B82986605 : Blo 2129435 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B55324403 : Blo 2129435 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B36882935 : Blo 2129435 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B24588623 : Blo 2129435 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B16392415 : Blo 2129435 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B21856553 : Blo 2129435 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B14571035 : Blo 2129435 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B9714023 : Blo 2129435 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B6476015 : Blo 2129435 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B4317343 : Blo 2129435 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B23025829 : Blo 2129435 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B30701105 : Blo 2129435 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B20467403 : Blo 2129435 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B13644935 : Blo 2129435 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B9096623 : Blo 2129435 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B6064415 : Blo 2129435 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B4042943 : Blo 2129435 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B2695295 : Blo 2129435 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B7187453 : Blo 2129435 7187453 := bstep (se 3 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 7187453 = 2695295) B2695295
theorem B4791635 : Blo 2129435 4791635 := bstep (se 1 (by rfl) ⟨3593726, by rfl⟩ : syracuseStep 4791635 = 7187453) B7187453
theorem B3194423 : Blo 2129435 3194423 := bstep (se 1 (by rfl) ⟨2395817, by rfl⟩ : syracuseStep 3194423 = 4791635) B4791635
theorem B2129615 : Blo 2129435 2129615 := bstep (se 1 (by rfl) ⟨1597211, by rfl⟩ : syracuseStep 2129615 = 3194423) B3194423
theorem B3194429 : Blo 2129435 3194429 := bbase (se 3 (by rfl) ⟨598955, by rfl⟩ : syracuseStep 3194429 = 1197911) (by norm_num)
theorem B2129619 : Blo 2129435 2129619 := bstep (se 1 (by rfl) ⟨1597214, by rfl⟩ : syracuseStep 2129619 = 3194429) B3194429
theorem B4791653 : Blo 2129435 4791653 := bbase (se 4 (by rfl) ⟨449217, by rfl⟩ : syracuseStep 4791653 = 898435) (by norm_num)
theorem B3194435 : Blo 2129435 3194435 := bstep (se 1 (by rfl) ⟨2395826, by rfl⟩ : syracuseStep 3194435 = 4791653) B4791653
theorem B2129623 : Blo 2129435 2129623 := bstep (se 1 (by rfl) ⟨1597217, by rfl⟩ : syracuseStep 2129623 = 3194435) B3194435
theorem B5390621 : Blo 2129435 5390621 := bbase (se 3 (by rfl) ⟨1010741, by rfl⟩ : syracuseStep 5390621 = 2021483) (by norm_num)
theorem B3593747 : Blo 2129435 3593747 := bstep (se 1 (by rfl) ⟨2695310, by rfl⟩ : syracuseStep 3593747 = 5390621) B5390621
theorem B2395831 : Blo 2129435 2395831 := bstep (se 1 (by rfl) ⟨1796873, by rfl⟩ : syracuseStep 2395831 = 3593747) B3593747
theorem B3194441 : Blo 2129435 3194441 := bstep (se 2 (by rfl) ⟨1197915, by rfl⟩ : syracuseStep 3194441 = 2395831) B2395831
theorem B2129627 : Blo 2129435 2129627 := bstep (se 1 (by rfl) ⟨1597220, by rfl⟩ : syracuseStep 2129627 = 3194441) B3194441
theorem B4042973 : Blo 2129435 4042973 := bbase (se 3 (by rfl) ⟨758057, by rfl⟩ : syracuseStep 4042973 = 1516115) (by norm_num)
theorem B10781261 : Blo 2129435 10781261 := bstep (se 3 (by rfl) ⟨2021486, by rfl⟩ : syracuseStep 10781261 = 4042973) B4042973
theorem B7187507 : Blo 2129435 7187507 := bstep (se 1 (by rfl) ⟨5390630, by rfl⟩ : syracuseStep 7187507 = 10781261) B10781261
theorem B4791671 : Blo 2129435 4791671 := bstep (se 1 (by rfl) ⟨3593753, by rfl⟩ : syracuseStep 4791671 = 7187507) B7187507
theorem B3194447 : Blo 2129435 3194447 := bstep (se 1 (by rfl) ⟨2395835, by rfl⟩ : syracuseStep 3194447 = 4791671) B4791671
theorem B2129631 : Blo 2129435 2129631 := bstep (se 1 (by rfl) ⟨1597223, by rfl⟩ : syracuseStep 2129631 = 3194447) B3194447
theorem B3194453 : Blo 2129435 3194453 := bbase (se 8 (by rfl) ⟨18717, by rfl⟩ : syracuseStep 3194453 = 37435) (by norm_num)
theorem B2129635 : Blo 2129435 2129635 := bstep (se 1 (by rfl) ⟨1597226, by rfl⟩ : syracuseStep 2129635 = 3194453) B3194453
theorem B9096725 : Blo 2129435 9096725 := bbase (se 6 (by rfl) ⟨213204, by rfl⟩ : syracuseStep 9096725 = 426409) (by norm_num)
theorem B6064483 : Blo 2129435 6064483 := bstep (se 1 (by rfl) ⟨4548362, by rfl⟩ : syracuseStep 6064483 = 9096725) B9096725
theorem B8085977 : Blo 2129435 8085977 := bstep (se 2 (by rfl) ⟨3032241, by rfl⟩ : syracuseStep 8085977 = 6064483) B6064483
theorem B5390651 : Blo 2129435 5390651 := bstep (se 1 (by rfl) ⟨4042988, by rfl⟩ : syracuseStep 5390651 = 8085977) B8085977
theorem B3593767 : Blo 2129435 3593767 := bstep (se 1 (by rfl) ⟨2695325, by rfl⟩ : syracuseStep 3593767 = 5390651) B5390651
theorem B4791689 : Blo 2129435 4791689 := bstep (se 2 (by rfl) ⟨1796883, by rfl⟩ : syracuseStep 4791689 = 3593767) B3593767
theorem B3194459 : Blo 2129435 3194459 := bstep (se 1 (by rfl) ⟨2395844, by rfl⟩ : syracuseStep 3194459 = 4791689) B4791689
theorem B2129639 : Blo 2129435 2129639 := bstep (se 1 (by rfl) ⟨1597229, by rfl⟩ : syracuseStep 2129639 = 3194459) B3194459
theorem B2395849 : Blo 2129435 2395849 := bbase (se 2 (by rfl) ⟨898443, by rfl⟩ : syracuseStep 2395849 = 1796887) (by norm_num)
theorem B3194465 : Blo 2129435 3194465 := bstep (se 2 (by rfl) ⟨1197924, by rfl⟩ : syracuseStep 3194465 = 2395849) B2395849
theorem B2129643 : Blo 2129435 2129643 := bstep (se 1 (by rfl) ⟨1597232, by rfl⟩ : syracuseStep 2129643 = 3194465) B3194465
theorem B6077189 : Blo 2129435 6077189 := bbase (se 4 (by rfl) ⟨569736, by rfl⟩ : syracuseStep 6077189 = 1139473) (by norm_num)
theorem B16205837 : Blo 2129435 16205837 := bstep (se 3 (by rfl) ⟨3038594, by rfl⟩ : syracuseStep 16205837 = 6077189) B6077189
theorem B43215565 : Blo 2129435 43215565 := bstep (se 3 (by rfl) ⟨8102918, by rfl⟩ : syracuseStep 43215565 = 16205837) B16205837
theorem B57620753 : Blo 2129435 57620753 := bstep (se 2 (by rfl) ⟨21607782, by rfl⟩ : syracuseStep 57620753 = 43215565) B43215565
theorem B38413835 : Blo 2129435 38413835 := bstep (se 1 (by rfl) ⟨28810376, by rfl⟩ : syracuseStep 38413835 = 57620753) B57620753
theorem B25609223 : Blo 2129435 25609223 := bstep (se 1 (by rfl) ⟨19206917, by rfl⟩ : syracuseStep 25609223 = 38413835) B38413835
theorem B17072815 : Blo 2129435 17072815 := bstep (se 1 (by rfl) ⟨12804611, by rfl⟩ : syracuseStep 17072815 = 25609223) B25609223
theorem B22763753 : Blo 2129435 22763753 := bstep (se 2 (by rfl) ⟨8536407, by rfl⟩ : syracuseStep 22763753 = 17072815) B17072815
theorem B15175835 : Blo 2129435 15175835 := bstep (se 1 (by rfl) ⟨11381876, by rfl⟩ : syracuseStep 15175835 = 22763753) B22763753
theorem B10117223 : Blo 2129435 10117223 := bstep (se 1 (by rfl) ⟨7587917, by rfl⟩ : syracuseStep 10117223 = 15175835) B15175835
theorem B6744815 : Blo 2129435 6744815 := bstep (se 1 (by rfl) ⟨5058611, by rfl⟩ : syracuseStep 6744815 = 10117223) B10117223
theorem B4496543 : Blo 2129435 4496543 := bstep (se 1 (by rfl) ⟨3372407, by rfl⟩ : syracuseStep 4496543 = 6744815) B6744815
theorem B2997695 : Blo 2129435 2997695 := bstep (se 1 (by rfl) ⟨2248271, by rfl⟩ : syracuseStep 2997695 = 4496543) B4496543
theorem B7993853 : Blo 2129435 7993853 := bstep (se 3 (by rfl) ⟨1498847, by rfl⟩ : syracuseStep 7993853 = 2997695) B2997695
theorem B5329235 : Blo 2129435 5329235 := bstep (se 1 (by rfl) ⟨3996926, by rfl⟩ : syracuseStep 5329235 = 7993853) B7993853
theorem B14211293 : Blo 2129435 14211293 := bstep (se 3 (by rfl) ⟨2664617, by rfl⟩ : syracuseStep 14211293 = 5329235) B5329235
theorem B37896781 : Blo 2129435 37896781 := bstep (se 3 (by rfl) ⟨7105646, by rfl⟩ : syracuseStep 37896781 = 14211293) B14211293
theorem B50529041 : Blo 2129435 50529041 := bstep (se 2 (by rfl) ⟨18948390, by rfl⟩ : syracuseStep 50529041 = 37896781) B37896781
theorem B33686027 : Blo 2129435 33686027 := bstep (se 1 (by rfl) ⟨25264520, by rfl⟩ : syracuseStep 33686027 = 50529041) B50529041
theorem B22457351 : Blo 2129435 22457351 := bstep (se 1 (by rfl) ⟨16843013, by rfl⟩ : syracuseStep 22457351 = 33686027) B33686027
theorem B14971567 : Blo 2129435 14971567 := bstep (se 1 (by rfl) ⟨11228675, by rfl⟩ : syracuseStep 14971567 = 22457351) B22457351
theorem B19962089 : Blo 2129435 19962089 := bstep (se 2 (by rfl) ⟨7485783, by rfl⟩ : syracuseStep 19962089 = 14971567) B14971567
theorem B13308059 : Blo 2129435 13308059 := bstep (se 1 (by rfl) ⟨9981044, by rfl⟩ : syracuseStep 13308059 = 19962089) B19962089
theorem B8872039 : Blo 2129435 8872039 := bstep (se 1 (by rfl) ⟨6654029, by rfl⟩ : syracuseStep 8872039 = 13308059) B13308059
theorem B11829385 : Blo 2129435 11829385 := bstep (se 2 (by rfl) ⟨4436019, by rfl⟩ : syracuseStep 11829385 = 8872039) B8872039
theorem B63090053 : Blo 2129435 63090053 := bstep (se 4 (by rfl) ⟨5914692, by rfl⟩ : syracuseStep 63090053 = 11829385) B11829385
theorem B42060035 : Blo 2129435 42060035 := bstep (se 1 (by rfl) ⟨31545026, by rfl⟩ : syracuseStep 42060035 = 63090053) B63090053
theorem B28040023 : Blo 2129435 28040023 := bstep (se 1 (by rfl) ⟨21030017, by rfl⟩ : syracuseStep 28040023 = 42060035) B42060035
theorem B37386697 : Blo 2129435 37386697 := bstep (se 2 (by rfl) ⟨14020011, by rfl⟩ : syracuseStep 37386697 = 28040023) B28040023
theorem B49848929 : Blo 2129435 49848929 := bstep (se 2 (by rfl) ⟨18693348, by rfl⟩ : syracuseStep 49848929 = 37386697) B37386697
theorem B33232619 : Blo 2129435 33232619 := bstep (se 1 (by rfl) ⟨24924464, by rfl⟩ : syracuseStep 33232619 = 49848929) B49848929
theorem B88620317 : Blo 2129435 88620317 := bstep (se 3 (by rfl) ⟨16616309, by rfl⟩ : syracuseStep 88620317 = 33232619) B33232619
theorem B59080211 : Blo 2129435 59080211 := bstep (se 1 (by rfl) ⟨44310158, by rfl⟩ : syracuseStep 59080211 = 88620317) B88620317
theorem B39386807 : Blo 2129435 39386807 := bstep (se 1 (by rfl) ⟨29540105, by rfl⟩ : syracuseStep 39386807 = 59080211) B59080211
theorem B26257871 : Blo 2129435 26257871 := bstep (se 1 (by rfl) ⟨19693403, by rfl⟩ : syracuseStep 26257871 = 39386807) B39386807
theorem B17505247 : Blo 2129435 17505247 := bstep (se 1 (by rfl) ⟨13128935, by rfl⟩ : syracuseStep 17505247 = 26257871) B26257871
theorem B23340329 : Blo 2129435 23340329 := bstep (se 2 (by rfl) ⟨8752623, by rfl⟩ : syracuseStep 23340329 = 17505247) B17505247
theorem B15560219 : Blo 2129435 15560219 := bstep (se 1 (by rfl) ⟨11670164, by rfl⟩ : syracuseStep 15560219 = 23340329) B23340329
theorem B41493917 : Blo 2129435 41493917 := bstep (se 3 (by rfl) ⟨7780109, by rfl⟩ : syracuseStep 41493917 = 15560219) B15560219
theorem B110650445 : Blo 2129435 110650445 := bstep (se 3 (by rfl) ⟨20746958, by rfl⟩ : syracuseStep 110650445 = 41493917) B41493917
theorem B73766963 : Blo 2129435 73766963 := bstep (se 1 (by rfl) ⟨55325222, by rfl⟩ : syracuseStep 73766963 = 110650445) B110650445
theorem B196711901 : Blo 2129435 196711901 := bstep (se 3 (by rfl) ⟨36883481, by rfl⟩ : syracuseStep 196711901 = 73766963) B73766963
theorem B131141267 : Blo 2129435 131141267 := bstep (se 1 (by rfl) ⟨98355950, by rfl⟩ : syracuseStep 131141267 = 196711901) B196711901
theorem B87427511 : Blo 2129435 87427511 := bstep (se 1 (by rfl) ⟨65570633, by rfl⟩ : syracuseStep 87427511 = 131141267) B131141267
theorem B58285007 : Blo 2129435 58285007 := bstep (se 1 (by rfl) ⟨43713755, by rfl⟩ : syracuseStep 58285007 = 87427511) B87427511
theorem B38856671 : Blo 2129435 38856671 := bstep (se 1 (by rfl) ⟨29142503, by rfl⟩ : syracuseStep 38856671 = 58285007) B58285007
theorem B25904447 : Blo 2129435 25904447 := bstep (se 1 (by rfl) ⟨19428335, by rfl⟩ : syracuseStep 25904447 = 38856671) B38856671
theorem B17269631 : Blo 2129435 17269631 := bstep (se 1 (by rfl) ⟨12952223, by rfl⟩ : syracuseStep 17269631 = 25904447) B25904447
theorem B11513087 : Blo 2129435 11513087 := bstep (se 1 (by rfl) ⟨8634815, by rfl⟩ : syracuseStep 11513087 = 17269631) B17269631
theorem B7675391 : Blo 2129435 7675391 := bstep (se 1 (by rfl) ⟨5756543, by rfl⟩ : syracuseStep 7675391 = 11513087) B11513087
theorem B5116927 : Blo 2129435 5116927 := bstep (se 1 (by rfl) ⟨3837695, by rfl⟩ : syracuseStep 5116927 = 7675391) B7675391
theorem B6822569 : Blo 2129435 6822569 := bstep (se 2 (by rfl) ⟨2558463, by rfl⟩ : syracuseStep 6822569 = 5116927) B5116927
theorem B18193517 : Blo 2129435 18193517 := bstep (se 3 (by rfl) ⟨3411284, by rfl⟩ : syracuseStep 18193517 = 6822569) B6822569
theorem B12129011 : Blo 2129435 12129011 := bstep (se 1 (by rfl) ⟨9096758, by rfl⟩ : syracuseStep 12129011 = 18193517) B18193517
theorem B8086007 : Blo 2129435 8086007 := bstep (se 1 (by rfl) ⟨6064505, by rfl⟩ : syracuseStep 8086007 = 12129011) B12129011
theorem B5390671 : Blo 2129435 5390671 := bstep (se 1 (by rfl) ⟨4043003, by rfl⟩ : syracuseStep 5390671 = 8086007) B8086007
theorem B7187561 : Blo 2129435 7187561 := bstep (se 2 (by rfl) ⟨2695335, by rfl⟩ : syracuseStep 7187561 = 5390671) B5390671
theorem B4791707 : Blo 2129435 4791707 := bstep (se 1 (by rfl) ⟨3593780, by rfl⟩ : syracuseStep 4791707 = 7187561) B7187561
theorem B3194471 : Blo 2129435 3194471 := bstep (se 1 (by rfl) ⟨2395853, by rfl⟩ : syracuseStep 3194471 = 4791707) B4791707
theorem B2129647 : Blo 2129435 2129647 := bstep (se 1 (by rfl) ⟨1597235, by rfl⟩ : syracuseStep 2129647 = 3194471) B3194471
theorem B3194477 : Blo 2129435 3194477 := bbase (se 3 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 3194477 = 1197929) (by norm_num)
theorem B2129651 : Blo 2129435 2129651 := bstep (se 1 (by rfl) ⟨1597238, by rfl⟩ : syracuseStep 2129651 = 3194477) B3194477
theorem B4791725 : Blo 2129435 4791725 := bbase (se 3 (by rfl) ⟨898448, by rfl⟩ : syracuseStep 4791725 = 1796897) (by norm_num)
theorem B3194483 : Blo 2129435 3194483 := bstep (se 1 (by rfl) ⟨2395862, by rfl⟩ : syracuseStep 3194483 = 4791725) B4791725
theorem B2129655 : Blo 2129435 2129655 := bstep (se 1 (by rfl) ⟨1597241, by rfl⟩ : syracuseStep 2129655 = 3194483) B3194483
theorem B8634869 : Blo 2129435 8634869 := bbase (se 5 (by rfl) ⟨404759, by rfl⟩ : syracuseStep 8634869 = 809519) (by norm_num)
theorem B5756579 : Blo 2129435 5756579 := bstep (se 1 (by rfl) ⟨4317434, by rfl⟩ : syracuseStep 5756579 = 8634869) B8634869
theorem B3837719 : Blo 2129435 3837719 := bstep (se 1 (by rfl) ⟨2878289, by rfl⟩ : syracuseStep 3837719 = 5756579) B5756579
theorem B2558479 : Blo 2129435 2558479 := bstep (se 1 (by rfl) ⟨1918859, by rfl⟩ : syracuseStep 2558479 = 3837719) B3837719
theorem B3411305 : Blo 2129435 3411305 := bstep (se 2 (by rfl) ⟨1279239, by rfl⟩ : syracuseStep 3411305 = 2558479) B2558479
theorem B2274203 : Blo 2129435 2274203 := bstep (se 1 (by rfl) ⟨1705652, by rfl⟩ : syracuseStep 2274203 = 3411305) B3411305
theorem B6064541 : Blo 2129435 6064541 := bstep (se 3 (by rfl) ⟨1137101, by rfl⟩ : syracuseStep 6064541 = 2274203) B2274203
theorem B4043027 : Blo 2129435 4043027 := bstep (se 1 (by rfl) ⟨3032270, by rfl⟩ : syracuseStep 4043027 = 6064541) B6064541
theorem B2695351 : Blo 2129435 2695351 := bstep (se 1 (by rfl) ⟨2021513, by rfl⟩ : syracuseStep 2695351 = 4043027) B4043027
theorem B3593801 : Blo 2129435 3593801 := bstep (se 2 (by rfl) ⟨1347675, by rfl⟩ : syracuseStep 3593801 = 2695351) B2695351
theorem B2395867 : Blo 2129435 2395867 := bstep (se 1 (by rfl) ⟨1796900, by rfl⟩ : syracuseStep 2395867 = 3593801) B3593801
theorem B3194489 : Blo 2129435 3194489 := bstep (se 2 (by rfl) ⟨1197933, by rfl⟩ : syracuseStep 3194489 = 2395867) B2395867
theorem B2129659 : Blo 2129435 2129659 := bstep (se 1 (by rfl) ⟨1597244, by rfl⟩ : syracuseStep 2129659 = 3194489) B3194489
theorem B5835125 : Blo 2129435 5835125 := bbase (se 5 (by rfl) ⟨273521, by rfl⟩ : syracuseStep 5835125 = 547043) (by norm_num)
theorem B15560333 : Blo 2129435 15560333 := bstep (se 3 (by rfl) ⟨2917562, by rfl⟩ : syracuseStep 15560333 = 5835125) B5835125
theorem B10373555 : Blo 2129435 10373555 := bstep (se 1 (by rfl) ⟨7780166, by rfl⟩ : syracuseStep 10373555 = 15560333) B15560333
theorem B27662813 : Blo 2129435 27662813 := bstep (se 3 (by rfl) ⟨5186777, by rfl⟩ : syracuseStep 27662813 = 10373555) B10373555
theorem B18441875 : Blo 2129435 18441875 := bstep (se 1 (by rfl) ⟨13831406, by rfl⟩ : syracuseStep 18441875 = 27662813) B27662813
theorem B49178333 : Blo 2129435 49178333 := bstep (se 3 (by rfl) ⟨9220937, by rfl⟩ : syracuseStep 49178333 = 18441875) B18441875
theorem B32785555 : Blo 2129435 32785555 := bstep (se 1 (by rfl) ⟨24589166, by rfl⟩ : syracuseStep 32785555 = 49178333) B49178333
theorem B43714073 : Blo 2129435 43714073 := bstep (se 2 (by rfl) ⟨16392777, by rfl⟩ : syracuseStep 43714073 = 32785555) B32785555
theorem B29142715 : Blo 2129435 29142715 := bstep (se 1 (by rfl) ⟨21857036, by rfl⟩ : syracuseStep 29142715 = 43714073) B43714073
theorem B38856953 : Blo 2129435 38856953 := bstep (se 2 (by rfl) ⟨14571357, by rfl⟩ : syracuseStep 38856953 = 29142715) B29142715
theorem B103618541 : Blo 2129435 103618541 := bstep (se 3 (by rfl) ⟨19428476, by rfl⟩ : syracuseStep 103618541 = 38856953) B38856953
theorem B69079027 : Blo 2129435 69079027 := bstep (se 1 (by rfl) ⟨51809270, by rfl⟩ : syracuseStep 69079027 = 103618541) B103618541
theorem B92105369 : Blo 2129435 92105369 := bstep (se 2 (by rfl) ⟨34539513, by rfl⟩ : syracuseStep 92105369 = 69079027) B69079027
theorem B61403579 : Blo 2129435 61403579 := bstep (se 1 (by rfl) ⟨46052684, by rfl⟩ : syracuseStep 61403579 = 92105369) B92105369
theorem B40935719 : Blo 2129435 40935719 := bstep (se 1 (by rfl) ⟨30701789, by rfl⟩ : syracuseStep 40935719 = 61403579) B61403579
theorem B27290479 : Blo 2129435 27290479 := bstep (se 1 (by rfl) ⟨20467859, by rfl⟩ : syracuseStep 27290479 = 40935719) B40935719
theorem B36387305 : Blo 2129435 36387305 := bstep (se 2 (by rfl) ⟨13645239, by rfl⟩ : syracuseStep 36387305 = 27290479) B27290479
theorem B24258203 : Blo 2129435 24258203 := bstep (se 1 (by rfl) ⟨18193652, by rfl⟩ : syracuseStep 24258203 = 36387305) B36387305
theorem B16172135 : Blo 2129435 16172135 := bstep (se 1 (by rfl) ⟨12129101, by rfl⟩ : syracuseStep 16172135 = 24258203) B24258203
theorem B10781423 : Blo 2129435 10781423 := bstep (se 1 (by rfl) ⟨8086067, by rfl⟩ : syracuseStep 10781423 = 16172135) B16172135
theorem B7187615 : Blo 2129435 7187615 := bstep (se 1 (by rfl) ⟨5390711, by rfl⟩ : syracuseStep 7187615 = 10781423) B10781423
theorem B4791743 : Blo 2129435 4791743 := bstep (se 1 (by rfl) ⟨3593807, by rfl⟩ : syracuseStep 4791743 = 7187615) B7187615
theorem B3194495 : Blo 2129435 3194495 := bstep (se 1 (by rfl) ⟨2395871, by rfl⟩ : syracuseStep 3194495 = 4791743) B4791743
theorem B2129663 : Blo 2129435 2129663 := bstep (se 1 (by rfl) ⟨1597247, by rfl⟩ : syracuseStep 2129663 = 3194495) B3194495
theorem B3194501 : Blo 2129435 3194501 := bbase (se 4 (by rfl) ⟨299484, by rfl⟩ : syracuseStep 3194501 = 598969) (by norm_num)
theorem B2129667 : Blo 2129435 2129667 := bstep (se 1 (by rfl) ⟨1597250, by rfl⟩ : syracuseStep 2129667 = 3194501) B3194501
theorem B3593821 : Blo 2129435 3593821 := bbase (se 3 (by rfl) ⟨673841, by rfl⟩ : syracuseStep 3593821 = 1347683) (by norm_num)
theorem B4791761 : Blo 2129435 4791761 := bstep (se 2 (by rfl) ⟨1796910, by rfl⟩ : syracuseStep 4791761 = 3593821) B3593821
theorem B3194507 : Blo 2129435 3194507 := bstep (se 1 (by rfl) ⟨2395880, by rfl⟩ : syracuseStep 3194507 = 4791761) B4791761
theorem B2129671 : Blo 2129435 2129671 := bstep (se 1 (by rfl) ⟨1597253, by rfl⟩ : syracuseStep 2129671 = 3194507) B3194507
theorem B2395885 : Blo 2129435 2395885 := bbase (se 3 (by rfl) ⟨449228, by rfl⟩ : syracuseStep 2395885 = 898457) (by norm_num)
theorem B3194513 : Blo 2129435 3194513 := bstep (se 2 (by rfl) ⟨1197942, by rfl⟩ : syracuseStep 3194513 = 2395885) B2395885
theorem B2129675 : Blo 2129435 2129675 := bstep (se 1 (by rfl) ⟨1597256, by rfl⟩ : syracuseStep 2129675 = 3194513) B3194513
theorem B7187669 : Blo 2129435 7187669 := bbase (se 7 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 7187669 = 168461) (by norm_num)
theorem B4791779 : Blo 2129435 4791779 := bstep (se 1 (by rfl) ⟨3593834, by rfl⟩ : syracuseStep 4791779 = 7187669) B7187669
theorem B3194519 : Blo 2129435 3194519 := bstep (se 1 (by rfl) ⟨2395889, by rfl⟩ : syracuseStep 3194519 = 4791779) B4791779
theorem B2129679 : Blo 2129435 2129679 := bstep (se 1 (by rfl) ⟨1597259, by rfl⟩ : syracuseStep 2129679 = 3194519) B3194519
theorem B3194525 : Blo 2129435 3194525 := bbase (se 3 (by rfl) ⟨598973, by rfl⟩ : syracuseStep 3194525 = 1197947) (by norm_num)
theorem B2129683 : Blo 2129435 2129683 := bstep (se 1 (by rfl) ⟨1597262, by rfl⟩ : syracuseStep 2129683 = 3194525) B3194525
theorem B4791797 : Blo 2129435 4791797 := bbase (se 5 (by rfl) ⟨224615, by rfl⟩ : syracuseStep 4791797 = 449231) (by norm_num)
theorem B3194531 : Blo 2129435 3194531 := bstep (se 1 (by rfl) ⟨2395898, by rfl⟩ : syracuseStep 3194531 = 4791797) B4791797
theorem B2129687 : Blo 2129435 2129687 := bstep (se 1 (by rfl) ⟨1597265, by rfl⟩ : syracuseStep 2129687 = 3194531) B3194531
theorem B25904981 : Blo 2129435 25904981 := bbase (se 9 (by rfl) ⟨75893, by rfl⟩ : syracuseStep 25904981 = 151787) (by norm_num)
theorem B69079949 : Blo 2129435 69079949 := bstep (se 3 (by rfl) ⟨12952490, by rfl⟩ : syracuseStep 69079949 = 25904981) B25904981
theorem B46053299 : Blo 2129435 46053299 := bstep (se 1 (by rfl) ⟨34539974, by rfl⟩ : syracuseStep 46053299 = 69079949) B69079949
theorem B30702199 : Blo 2129435 30702199 := bstep (se 1 (by rfl) ⟨23026649, by rfl⟩ : syracuseStep 30702199 = 46053299) B46053299
theorem B40936265 : Blo 2129435 40936265 := bstep (se 2 (by rfl) ⟨15351099, by rfl⟩ : syracuseStep 40936265 = 30702199) B30702199
theorem B27290843 : Blo 2129435 27290843 := bstep (se 1 (by rfl) ⟨20468132, by rfl⟩ : syracuseStep 27290843 = 40936265) B40936265
theorem B18193895 : Blo 2129435 18193895 := bstep (se 1 (by rfl) ⟨13645421, by rfl⟩ : syracuseStep 18193895 = 27290843) B27290843
theorem B12129263 : Blo 2129435 12129263 := bstep (se 1 (by rfl) ⟨9096947, by rfl⟩ : syracuseStep 12129263 = 18193895) B18193895
theorem B8086175 : Blo 2129435 8086175 := bstep (se 1 (by rfl) ⟨6064631, by rfl⟩ : syracuseStep 8086175 = 12129263) B12129263
theorem B5390783 : Blo 2129435 5390783 := bstep (se 1 (by rfl) ⟨4043087, by rfl⟩ : syracuseStep 5390783 = 8086175) B8086175
theorem B3593855 : Blo 2129435 3593855 := bstep (se 1 (by rfl) ⟨2695391, by rfl⟩ : syracuseStep 3593855 = 5390783) B5390783
theorem B2395903 : Blo 2129435 2395903 := bstep (se 1 (by rfl) ⟨1796927, by rfl⟩ : syracuseStep 2395903 = 3593855) B3593855
theorem B3194537 : Blo 2129435 3194537 := bstep (se 2 (by rfl) ⟨1197951, by rfl⟩ : syracuseStep 3194537 = 2395903) B2395903
theorem B2129691 : Blo 2129435 2129691 := bstep (se 1 (by rfl) ⟨1597268, by rfl⟩ : syracuseStep 2129691 = 3194537) B3194537
theorem B2274241 : Blo 2129435 2274241 := bbase (se 2 (by rfl) ⟨852840, by rfl⟩ : syracuseStep 2274241 = 1705681) (by norm_num)
theorem B3032321 : Blo 2129435 3032321 := bstep (se 2 (by rfl) ⟨1137120, by rfl⟩ : syracuseStep 3032321 = 2274241) B2274241
theorem B8086189 : Blo 2129435 8086189 := bstep (se 3 (by rfl) ⟨1516160, by rfl⟩ : syracuseStep 8086189 = 3032321) B3032321
theorem B10781585 : Blo 2129435 10781585 := bstep (se 2 (by rfl) ⟨4043094, by rfl⟩ : syracuseStep 10781585 = 8086189) B8086189
theorem B7187723 : Blo 2129435 7187723 := bstep (se 1 (by rfl) ⟨5390792, by rfl⟩ : syracuseStep 7187723 = 10781585) B10781585
theorem B4791815 : Blo 2129435 4791815 := bstep (se 1 (by rfl) ⟨3593861, by rfl⟩ : syracuseStep 4791815 = 7187723) B7187723
theorem B3194543 : Blo 2129435 3194543 := bstep (se 1 (by rfl) ⟨2395907, by rfl⟩ : syracuseStep 3194543 = 4791815) B4791815
theorem B2129695 : Blo 2129435 2129695 := bstep (se 1 (by rfl) ⟨1597271, by rfl⟩ : syracuseStep 2129695 = 3194543) B3194543
theorem B3194549 : Blo 2129435 3194549 := bbase (se 5 (by rfl) ⟨149744, by rfl⟩ : syracuseStep 3194549 = 299489) (by norm_num)
theorem B2129699 : Blo 2129435 2129699 := bstep (se 1 (by rfl) ⟨1597274, by rfl⟩ : syracuseStep 2129699 = 3194549) B3194549
theorem B5390813 : Blo 2129435 5390813 := bbase (se 3 (by rfl) ⟨1010777, by rfl⟩ : syracuseStep 5390813 = 2021555) (by norm_num)
theorem B3593875 : Blo 2129435 3593875 := bstep (se 1 (by rfl) ⟨2695406, by rfl⟩ : syracuseStep 3593875 = 5390813) B5390813
theorem B4791833 : Blo 2129435 4791833 := bstep (se 2 (by rfl) ⟨1796937, by rfl⟩ : syracuseStep 4791833 = 3593875) B3593875
theorem B3194555 : Blo 2129435 3194555 := bstep (se 1 (by rfl) ⟨2395916, by rfl⟩ : syracuseStep 3194555 = 4791833) B4791833
theorem B2129703 : Blo 2129435 2129703 := bstep (se 1 (by rfl) ⟨1597277, by rfl⟩ : syracuseStep 2129703 = 3194555) B3194555
theorem B2395921 : Blo 2129435 2395921 := bbase (se 2 (by rfl) ⟨898470, by rfl⟩ : syracuseStep 2395921 = 1796941) (by norm_num)
theorem B3194561 : Blo 2129435 3194561 := bstep (se 2 (by rfl) ⟨1197960, by rfl⟩ : syracuseStep 3194561 = 2395921) B2395921
theorem B2129707 : Blo 2129435 2129707 := bstep (se 1 (by rfl) ⟨1597280, by rfl⟩ : syracuseStep 2129707 = 3194561) B3194561
theorem B4043125 : Blo 2129435 4043125 := bbase (se 5 (by rfl) ⟨189521, by rfl⟩ : syracuseStep 4043125 = 379043) (by norm_num)
theorem B5390833 : Blo 2129435 5390833 := bstep (se 2 (by rfl) ⟨2021562, by rfl⟩ : syracuseStep 5390833 = 4043125) B4043125
theorem B7187777 : Blo 2129435 7187777 := bstep (se 2 (by rfl) ⟨2695416, by rfl⟩ : syracuseStep 7187777 = 5390833) B5390833
theorem B4791851 : Blo 2129435 4791851 := bstep (se 1 (by rfl) ⟨3593888, by rfl⟩ : syracuseStep 4791851 = 7187777) B7187777
theorem B3194567 : Blo 2129435 3194567 := bstep (se 1 (by rfl) ⟨2395925, by rfl⟩ : syracuseStep 3194567 = 4791851) B4791851
theorem B2129711 : Blo 2129435 2129711 := bstep (se 1 (by rfl) ⟨1597283, by rfl⟩ : syracuseStep 2129711 = 3194567) B3194567
theorem B3194573 : Blo 2129435 3194573 := bbase (se 3 (by rfl) ⟨598982, by rfl⟩ : syracuseStep 3194573 = 1197965) (by norm_num)
theorem B2129715 : Blo 2129435 2129715 := bstep (se 1 (by rfl) ⟨1597286, by rfl⟩ : syracuseStep 2129715 = 3194573) B3194573
theorem B4791869 : Blo 2129435 4791869 := bbase (se 3 (by rfl) ⟨898475, by rfl⟩ : syracuseStep 4791869 = 1796951) (by norm_num)
theorem B3194579 : Blo 2129435 3194579 := bstep (se 1 (by rfl) ⟨2395934, by rfl⟩ : syracuseStep 3194579 = 4791869) B4791869
theorem B2129719 : Blo 2129435 2129719 := bstep (se 1 (by rfl) ⟨1597289, by rfl⟩ : syracuseStep 2129719 = 3194579) B3194579
theorem B3593909 : Blo 2129435 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B2395939 : Blo 2129435 2395939 := bstep (se 1 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 2395939 = 3593909) B3593909
theorem B3194585 : Blo 2129435 3194585 := bstep (se 2 (by rfl) ⟨1197969, by rfl⟩ : syracuseStep 3194585 = 2395939) B2395939
theorem B2129723 : Blo 2129435 2129723 := bstep (se 1 (by rfl) ⟨1597292, by rfl⟩ : syracuseStep 2129723 = 3194585) B3194585
theorem B3411413 : Blo 2129435 3411413 := bbase (se 7 (by rfl) ⟨39977, by rfl⟩ : syracuseStep 3411413 = 79955) (by norm_num)
theorem B2274275 : Blo 2129435 2274275 := bstep (se 1 (by rfl) ⟨1705706, by rfl⟩ : syracuseStep 2274275 = 3411413) B3411413
theorem B6064733 : Blo 2129435 6064733 := bstep (se 3 (by rfl) ⟨1137137, by rfl⟩ : syracuseStep 6064733 = 2274275) B2274275
theorem B16172621 : Blo 2129435 16172621 := bstep (se 3 (by rfl) ⟨3032366, by rfl⟩ : syracuseStep 16172621 = 6064733) B6064733
theorem B10781747 : Blo 2129435 10781747 := bstep (se 1 (by rfl) ⟨8086310, by rfl⟩ : syracuseStep 10781747 = 16172621) B16172621
theorem B7187831 : Blo 2129435 7187831 := bstep (se 1 (by rfl) ⟨5390873, by rfl⟩ : syracuseStep 7187831 = 10781747) B10781747
theorem B4791887 : Blo 2129435 4791887 := bstep (se 1 (by rfl) ⟨3593915, by rfl⟩ : syracuseStep 4791887 = 7187831) B7187831
theorem B3194591 : Blo 2129435 3194591 := bstep (se 1 (by rfl) ⟨2395943, by rfl⟩ : syracuseStep 3194591 = 4791887) B4791887
theorem B2129727 : Blo 2129435 2129727 := bstep (se 1 (by rfl) ⟨1597295, by rfl⟩ : syracuseStep 2129727 = 3194591) B3194591
theorem B3194597 : Blo 2129435 3194597 := bbase (se 4 (by rfl) ⟨299493, by rfl⟩ : syracuseStep 3194597 = 598987) (by norm_num)
theorem B2129731 : Blo 2129435 2129731 := bstep (se 1 (by rfl) ⟨1597298, by rfl⟩ : syracuseStep 2129731 = 3194597) B3194597
theorem B6064757 : Blo 2129435 6064757 := bbase (se 5 (by rfl) ⟨284285, by rfl⟩ : syracuseStep 6064757 = 568571) (by norm_num)
theorem B4043171 : Blo 2129435 4043171 := bstep (se 1 (by rfl) ⟨3032378, by rfl⟩ : syracuseStep 4043171 = 6064757) B6064757
theorem B2695447 : Blo 2129435 2695447 := bstep (se 1 (by rfl) ⟨2021585, by rfl⟩ : syracuseStep 2695447 = 4043171) B4043171
theorem B3593929 : Blo 2129435 3593929 := bstep (se 2 (by rfl) ⟨1347723, by rfl⟩ : syracuseStep 3593929 = 2695447) B2695447
theorem B4791905 : Blo 2129435 4791905 := bstep (se 2 (by rfl) ⟨1796964, by rfl⟩ : syracuseStep 4791905 = 3593929) B3593929
theorem B3194603 : Blo 2129435 3194603 := bstep (se 1 (by rfl) ⟨2395952, by rfl⟩ : syracuseStep 3194603 = 4791905) B4791905
theorem B2129735 : Blo 2129435 2129735 := bstep (se 1 (by rfl) ⟨1597301, by rfl⟩ : syracuseStep 2129735 = 3194603) B3194603
theorem B2395957 : Blo 2129435 2395957 := bbase (se 5 (by rfl) ⟨112310, by rfl⟩ : syracuseStep 2395957 = 224621) (by norm_num)
theorem B3194609 : Blo 2129435 3194609 := bstep (se 2 (by rfl) ⟨1197978, by rfl⟩ : syracuseStep 3194609 = 2395957) B2395957
theorem B2129739 : Blo 2129435 2129739 := bstep (se 1 (by rfl) ⟨1597304, by rfl⟩ : syracuseStep 2129739 = 3194609) B3194609
theorem B2695457 : Blo 2129435 2695457 := bbase (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) (by norm_num)
theorem B7187885 : Blo 2129435 7187885 := bstep (se 3 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 7187885 = 2695457) B2695457
theorem B4791923 : Blo 2129435 4791923 := bstep (se 1 (by rfl) ⟨3593942, by rfl⟩ : syracuseStep 4791923 = 7187885) B7187885
theorem B3194615 : Blo 2129435 3194615 := bstep (se 1 (by rfl) ⟨2395961, by rfl⟩ : syracuseStep 3194615 = 4791923) B4791923
theorem B2129743 : Blo 2129435 2129743 := bstep (se 1 (by rfl) ⟨1597307, by rfl⟩ : syracuseStep 2129743 = 3194615) B3194615
theorem B3194621 : Blo 2129435 3194621 := bbase (se 3 (by rfl) ⟨598991, by rfl⟩ : syracuseStep 3194621 = 1197983) (by norm_num)
theorem B2129747 : Blo 2129435 2129747 := bstep (se 1 (by rfl) ⟨1597310, by rfl⟩ : syracuseStep 2129747 = 3194621) B3194621
theorem B4791941 : Blo 2129435 4791941 := bbase (se 4 (by rfl) ⟨449244, by rfl⟩ : syracuseStep 4791941 = 898489) (by norm_num)
theorem B3194627 : Blo 2129435 3194627 := bstep (se 1 (by rfl) ⟨2395970, by rfl⟩ : syracuseStep 3194627 = 4791941) B4791941
theorem B2129751 : Blo 2129435 2129751 := bstep (se 1 (by rfl) ⟨1597313, by rfl⟩ : syracuseStep 2129751 = 3194627) B3194627
theorem B6822917 : Blo 2129435 6822917 := bbase (se 4 (by rfl) ⟨639648, by rfl⟩ : syracuseStep 6822917 = 1279297) (by norm_num)
theorem B4548611 : Blo 2129435 4548611 := bstep (se 1 (by rfl) ⟨3411458, by rfl⟩ : syracuseStep 4548611 = 6822917) B6822917
theorem B3032407 : Blo 2129435 3032407 := bstep (se 1 (by rfl) ⟨2274305, by rfl⟩ : syracuseStep 3032407 = 4548611) B4548611
theorem B4043209 : Blo 2129435 4043209 := bstep (se 2 (by rfl) ⟨1516203, by rfl⟩ : syracuseStep 4043209 = 3032407) B3032407
theorem B5390945 : Blo 2129435 5390945 := bstep (se 2 (by rfl) ⟨2021604, by rfl⟩ : syracuseStep 5390945 = 4043209) B4043209
theorem B3593963 : Blo 2129435 3593963 := bstep (se 1 (by rfl) ⟨2695472, by rfl⟩ : syracuseStep 3593963 = 5390945) B5390945
theorem B2395975 : Blo 2129435 2395975 := bstep (se 1 (by rfl) ⟨1796981, by rfl⟩ : syracuseStep 2395975 = 3593963) B3593963
theorem B3194633 : Blo 2129435 3194633 := bstep (se 2 (by rfl) ⟨1197987, by rfl⟩ : syracuseStep 3194633 = 2395975) B2395975
theorem B2129755 : Blo 2129435 2129755 := bstep (se 1 (by rfl) ⟨1597316, by rfl⟩ : syracuseStep 2129755 = 3194633) B3194633
theorem B10781909 : Blo 2129435 10781909 := bbase (se 7 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 10781909 = 252701) (by norm_num)
theorem B7187939 : Blo 2129435 7187939 := bstep (se 1 (by rfl) ⟨5390954, by rfl⟩ : syracuseStep 7187939 = 10781909) B10781909
theorem B4791959 : Blo 2129435 4791959 := bstep (se 1 (by rfl) ⟨3593969, by rfl⟩ : syracuseStep 4791959 = 7187939) B7187939
theorem B3194639 : Blo 2129435 3194639 := bstep (se 1 (by rfl) ⟨2395979, by rfl⟩ : syracuseStep 3194639 = 4791959) B4791959
theorem B2129759 : Blo 2129435 2129759 := bstep (se 1 (by rfl) ⟨1597319, by rfl⟩ : syracuseStep 2129759 = 3194639) B3194639
theorem B3194645 : Blo 2129435 3194645 := bbase (se 6 (by rfl) ⟨74874, by rfl⟩ : syracuseStep 3194645 = 149749) (by norm_num)
theorem B2129763 : Blo 2129435 2129763 := bstep (se 1 (by rfl) ⟨1597322, by rfl⟩ : syracuseStep 2129763 = 3194645) B3194645
theorem B4990805 : Blo 2129435 4990805 := bbase (se 9 (by rfl) ⟨14621, by rfl⟩ : syracuseStep 4990805 = 29243) (by norm_num)
theorem B3327203 : Blo 2129435 3327203 := bstep (se 1 (by rfl) ⟨2495402, by rfl⟩ : syracuseStep 3327203 = 4990805) B4990805
theorem B8872541 : Blo 2129435 8872541 := bstep (se 3 (by rfl) ⟨1663601, by rfl⟩ : syracuseStep 8872541 = 3327203) B3327203
theorem B5915027 : Blo 2129435 5915027 := bstep (se 1 (by rfl) ⟨4436270, by rfl⟩ : syracuseStep 5915027 = 8872541) B8872541
theorem B3943351 : Blo 2129435 3943351 := bstep (se 1 (by rfl) ⟨2957513, by rfl⟩ : syracuseStep 3943351 = 5915027) B5915027
theorem B5257801 : Blo 2129435 5257801 := bstep (se 2 (by rfl) ⟨1971675, by rfl⟩ : syracuseStep 5257801 = 3943351) B3943351
theorem B7010401 : Blo 2129435 7010401 := bstep (se 2 (by rfl) ⟨2628900, by rfl⟩ : syracuseStep 7010401 = 5257801) B5257801
theorem B9347201 : Blo 2129435 9347201 := bstep (se 2 (by rfl) ⟨3505200, by rfl⟩ : syracuseStep 9347201 = 7010401) B7010401
theorem B6231467 : Blo 2129435 6231467 := bstep (se 1 (by rfl) ⟨4673600, by rfl⟩ : syracuseStep 6231467 = 9347201) B9347201
theorem B4154311 : Blo 2129435 4154311 := bstep (se 1 (by rfl) ⟨3115733, by rfl⟩ : syracuseStep 4154311 = 6231467) B6231467
theorem B22156325 : Blo 2129435 22156325 := bstep (se 4 (by rfl) ⟨2077155, by rfl⟩ : syracuseStep 22156325 = 4154311) B4154311
theorem B14770883 : Blo 2129435 14770883 := bstep (se 1 (by rfl) ⟨11078162, by rfl⟩ : syracuseStep 14770883 = 22156325) B22156325
theorem B9847255 : Blo 2129435 9847255 := bstep (se 1 (by rfl) ⟨7385441, by rfl⟩ : syracuseStep 9847255 = 14770883) B14770883
theorem B13129673 : Blo 2129435 13129673 := bstep (se 2 (by rfl) ⟨4923627, by rfl⟩ : syracuseStep 13129673 = 9847255) B9847255
theorem B35012461 : Blo 2129435 35012461 := bstep (se 3 (by rfl) ⟨6564836, by rfl⟩ : syracuseStep 35012461 = 13129673) B13129673
theorem B46683281 : Blo 2129435 46683281 := bstep (se 2 (by rfl) ⟨17506230, by rfl⟩ : syracuseStep 46683281 = 35012461) B35012461
theorem B31122187 : Blo 2129435 31122187 := bstep (se 1 (by rfl) ⟨23341640, by rfl⟩ : syracuseStep 31122187 = 46683281) B46683281
theorem B165984997 : Blo 2129435 165984997 := bstep (se 4 (by rfl) ⟨15561093, by rfl⟩ : syracuseStep 165984997 = 31122187) B31122187
theorem B221313329 : Blo 2129435 221313329 := bstep (se 2 (by rfl) ⟨82992498, by rfl⟩ : syracuseStep 221313329 = 165984997) B165984997
theorem B147542219 : Blo 2129435 147542219 := bstep (se 1 (by rfl) ⟨110656664, by rfl⟩ : syracuseStep 147542219 = 221313329) B221313329
theorem B98361479 : Blo 2129435 98361479 := bstep (se 1 (by rfl) ⟨73771109, by rfl⟩ : syracuseStep 98361479 = 147542219) B147542219
theorem B262297277 : Blo 2129435 262297277 := bstep (se 3 (by rfl) ⟨49180739, by rfl⟩ : syracuseStep 262297277 = 98361479) B98361479
theorem B174864851 : Blo 2129435 174864851 := bstep (se 1 (by rfl) ⟨131148638, by rfl⟩ : syracuseStep 174864851 = 262297277) B262297277
theorem B116576567 : Blo 2129435 116576567 := bstep (se 1 (by rfl) ⟨87432425, by rfl⟩ : syracuseStep 116576567 = 174864851) B174864851
theorem B77717711 : Blo 2129435 77717711 := bstep (se 1 (by rfl) ⟨58288283, by rfl⟩ : syracuseStep 77717711 = 116576567) B116576567
theorem B51811807 : Blo 2129435 51811807 := bstep (se 1 (by rfl) ⟨38858855, by rfl⟩ : syracuseStep 51811807 = 77717711) B77717711
theorem B69082409 : Blo 2129435 69082409 := bstep (se 2 (by rfl) ⟨25905903, by rfl⟩ : syracuseStep 69082409 = 51811807) B51811807
theorem B46054939 : Blo 2129435 46054939 := bstep (se 1 (by rfl) ⟨34541204, by rfl⟩ : syracuseStep 46054939 = 69082409) B69082409
theorem B61406585 : Blo 2129435 61406585 := bstep (se 2 (by rfl) ⟨23027469, by rfl⟩ : syracuseStep 61406585 = 46054939) B46054939
theorem B40937723 : Blo 2129435 40937723 := bstep (se 1 (by rfl) ⟨30703292, by rfl⟩ : syracuseStep 40937723 = 61406585) B61406585
theorem B27291815 : Blo 2129435 27291815 := bstep (se 1 (by rfl) ⟨20468861, by rfl⟩ : syracuseStep 27291815 = 40937723) B40937723
theorem B18194543 : Blo 2129435 18194543 := bstep (se 1 (by rfl) ⟨13645907, by rfl⟩ : syracuseStep 18194543 = 27291815) B27291815
theorem B12129695 : Blo 2129435 12129695 := bstep (se 1 (by rfl) ⟨9097271, by rfl⟩ : syracuseStep 12129695 = 18194543) B18194543
theorem B8086463 : Blo 2129435 8086463 := bstep (se 1 (by rfl) ⟨6064847, by rfl⟩ : syracuseStep 8086463 = 12129695) B12129695
theorem B5390975 : Blo 2129435 5390975 := bstep (se 1 (by rfl) ⟨4043231, by rfl⟩ : syracuseStep 5390975 = 8086463) B8086463
theorem B3593983 : Blo 2129435 3593983 := bstep (se 1 (by rfl) ⟨2695487, by rfl⟩ : syracuseStep 3593983 = 5390975) B5390975
theorem B4791977 : Blo 2129435 4791977 := bstep (se 2 (by rfl) ⟨1796991, by rfl⟩ : syracuseStep 4791977 = 3593983) B3593983
theorem B3194651 : Blo 2129435 3194651 := bstep (se 1 (by rfl) ⟨2395988, by rfl⟩ : syracuseStep 3194651 = 4791977) B4791977
theorem B2129767 : Blo 2129435 2129767 := bstep (se 1 (by rfl) ⟨1597325, by rfl⟩ : syracuseStep 2129767 = 3194651) B3194651
theorem B2395993 : Blo 2129435 2395993 := bbase (se 2 (by rfl) ⟨898497, by rfl⟩ : syracuseStep 2395993 = 1796995) (by norm_num)
theorem B3194657 : Blo 2129435 3194657 := bstep (se 2 (by rfl) ⟨1197996, by rfl⟩ : syracuseStep 3194657 = 2395993) B2395993
theorem B2129771 : Blo 2129435 2129771 := bstep (se 1 (by rfl) ⟨1597328, by rfl⟩ : syracuseStep 2129771 = 3194657) B3194657
theorem B4548653 : Blo 2129435 4548653 := bbase (se 3 (by rfl) ⟨852872, by rfl⟩ : syracuseStep 4548653 = 1705745) (by norm_num)
theorem B3032435 : Blo 2129435 3032435 := bstep (se 1 (by rfl) ⟨2274326, by rfl⟩ : syracuseStep 3032435 = 4548653) B4548653
theorem B8086493 : Blo 2129435 8086493 := bstep (se 3 (by rfl) ⟨1516217, by rfl⟩ : syracuseStep 8086493 = 3032435) B3032435
theorem B5390995 : Blo 2129435 5390995 := bstep (se 1 (by rfl) ⟨4043246, by rfl⟩ : syracuseStep 5390995 = 8086493) B8086493
theorem B7187993 : Blo 2129435 7187993 := bstep (se 2 (by rfl) ⟨2695497, by rfl⟩ : syracuseStep 7187993 = 5390995) B5390995
theorem B4791995 : Blo 2129435 4791995 := bstep (se 1 (by rfl) ⟨3593996, by rfl⟩ : syracuseStep 4791995 = 7187993) B7187993
theorem B3194663 : Blo 2129435 3194663 := bstep (se 1 (by rfl) ⟨2395997, by rfl⟩ : syracuseStep 3194663 = 4791995) B4791995
theorem B2129775 : Blo 2129435 2129775 := bstep (se 1 (by rfl) ⟨1597331, by rfl⟩ : syracuseStep 2129775 = 3194663) B3194663
theorem B3194669 : Blo 2129435 3194669 := bbase (se 3 (by rfl) ⟨599000, by rfl⟩ : syracuseStep 3194669 = 1198001) (by norm_num)
theorem B2129779 : Blo 2129435 2129779 := bstep (se 1 (by rfl) ⟨1597334, by rfl⟩ : syracuseStep 2129779 = 3194669) B3194669
theorem B4792013 : Blo 2129435 4792013 := bbase (se 3 (by rfl) ⟨898502, by rfl⟩ : syracuseStep 4792013 = 1797005) (by norm_num)
theorem B3194675 : Blo 2129435 3194675 := bstep (se 1 (by rfl) ⟨2396006, by rfl⟩ : syracuseStep 3194675 = 4792013) B4792013
theorem B2129783 : Blo 2129435 2129783 := bstep (se 1 (by rfl) ⟨1597337, by rfl⟩ : syracuseStep 2129783 = 3194675) B3194675
theorem B2695513 : Blo 2129435 2695513 := bbase (se 2 (by rfl) ⟨1010817, by rfl⟩ : syracuseStep 2695513 = 2021635) (by norm_num)
theorem B3594017 : Blo 2129435 3594017 := bstep (se 2 (by rfl) ⟨1347756, by rfl⟩ : syracuseStep 3594017 = 2695513) B2695513
theorem B2396011 : Blo 2129435 2396011 := bstep (se 1 (by rfl) ⟨1797008, by rfl⟩ : syracuseStep 2396011 = 3594017) B3594017
theorem B3194681 : Blo 2129435 3194681 := bstep (se 2 (by rfl) ⟨1198005, by rfl⟩ : syracuseStep 3194681 = 2396011) B2396011
theorem B2129787 : Blo 2129435 2129787 := bstep (se 1 (by rfl) ⟨1597340, by rfl⟩ : syracuseStep 2129787 = 3194681) B3194681
theorem B5756933 : Blo 2129435 5756933 := bbase (se 4 (by rfl) ⟨539712, by rfl⟩ : syracuseStep 5756933 = 1079425) (by norm_num)
theorem B3837955 : Blo 2129435 3837955 := bstep (se 1 (by rfl) ⟨2878466, by rfl⟩ : syracuseStep 3837955 = 5756933) B5756933
theorem B5117273 : Blo 2129435 5117273 := bstep (se 2 (by rfl) ⟨1918977, by rfl⟩ : syracuseStep 5117273 = 3837955) B3837955
theorem B3411515 : Blo 2129435 3411515 := bstep (se 1 (by rfl) ⟨2558636, by rfl⟩ : syracuseStep 3411515 = 5117273) B5117273
theorem B9097373 : Blo 2129435 9097373 := bstep (se 3 (by rfl) ⟨1705757, by rfl⟩ : syracuseStep 9097373 = 3411515) B3411515
theorem B24259661 : Blo 2129435 24259661 := bstep (se 3 (by rfl) ⟨4548686, by rfl⟩ : syracuseStep 24259661 = 9097373) B9097373
theorem B16173107 : Blo 2129435 16173107 := bstep (se 1 (by rfl) ⟨12129830, by rfl⟩ : syracuseStep 16173107 = 24259661) B24259661
theorem B10782071 : Blo 2129435 10782071 := bstep (se 1 (by rfl) ⟨8086553, by rfl⟩ : syracuseStep 10782071 = 16173107) B16173107
theorem B7188047 : Blo 2129435 7188047 := bstep (se 1 (by rfl) ⟨5391035, by rfl⟩ : syracuseStep 7188047 = 10782071) B10782071
theorem B4792031 : Blo 2129435 4792031 := bstep (se 1 (by rfl) ⟨3594023, by rfl⟩ : syracuseStep 4792031 = 7188047) B7188047
theorem B3194687 : Blo 2129435 3194687 := bstep (se 1 (by rfl) ⟨2396015, by rfl⟩ : syracuseStep 3194687 = 4792031) B4792031
theorem B2129791 : Blo 2129435 2129791 := bstep (se 1 (by rfl) ⟨1597343, by rfl⟩ : syracuseStep 2129791 = 3194687) B3194687
theorem B3194693 : Blo 2129435 3194693 := bbase (se 4 (by rfl) ⟨299502, by rfl⟩ : syracuseStep 3194693 = 599005) (by norm_num)
theorem B2129795 : Blo 2129435 2129795 := bstep (se 1 (by rfl) ⟨1597346, by rfl⟩ : syracuseStep 2129795 = 3194693) B3194693
theorem B3594037 : Blo 2129435 3594037 := bbase (se 5 (by rfl) ⟨168470, by rfl⟩ : syracuseStep 3594037 = 336941) (by norm_num)
theorem B4792049 : Blo 2129435 4792049 := bstep (se 2 (by rfl) ⟨1797018, by rfl⟩ : syracuseStep 4792049 = 3594037) B3594037
theorem B3194699 : Blo 2129435 3194699 := bstep (se 1 (by rfl) ⟨2396024, by rfl⟩ : syracuseStep 3194699 = 4792049) B4792049
theorem B2129799 : Blo 2129435 2129799 := bstep (se 1 (by rfl) ⟨1597349, by rfl⟩ : syracuseStep 2129799 = 3194699) B3194699
theorem B2396029 : Blo 2129435 2396029 := bbase (se 3 (by rfl) ⟨449255, by rfl⟩ : syracuseStep 2396029 = 898511) (by norm_num)
theorem B3194705 : Blo 2129435 3194705 := bstep (se 2 (by rfl) ⟨1198014, by rfl⟩ : syracuseStep 3194705 = 2396029) B2396029
theorem B2129803 : Blo 2129435 2129803 := bstep (se 1 (by rfl) ⟨1597352, by rfl⟩ : syracuseStep 2129803 = 3194705) B3194705
theorem B7188101 : Blo 2129435 7188101 := bbase (se 4 (by rfl) ⟨673884, by rfl⟩ : syracuseStep 7188101 = 1347769) (by norm_num)
theorem B4792067 : Blo 2129435 4792067 := bstep (se 1 (by rfl) ⟨3594050, by rfl⟩ : syracuseStep 4792067 = 7188101) B7188101
theorem B3194711 : Blo 2129435 3194711 := bstep (se 1 (by rfl) ⟨2396033, by rfl⟩ : syracuseStep 3194711 = 4792067) B4792067
theorem B2129807 : Blo 2129435 2129807 := bstep (se 1 (by rfl) ⟨1597355, by rfl⟩ : syracuseStep 2129807 = 3194711) B3194711
theorem B3194717 : Blo 2129435 3194717 := bbase (se 3 (by rfl) ⟨599009, by rfl⟩ : syracuseStep 3194717 = 1198019) (by norm_num)
theorem B2129811 : Blo 2129435 2129811 := bstep (se 1 (by rfl) ⟨1597358, by rfl⟩ : syracuseStep 2129811 = 3194717) B3194717
theorem B4792085 : Blo 2129435 4792085 := bbase (se 6 (by rfl) ⟨112314, by rfl⟩ : syracuseStep 4792085 = 224629) (by norm_num)
theorem B3194723 : Blo 2129435 3194723 := bstep (se 1 (by rfl) ⟨2396042, by rfl⟩ : syracuseStep 3194723 = 4792085) B4792085
theorem B2129815 : Blo 2129435 2129815 := bstep (se 1 (by rfl) ⟨1597361, by rfl⟩ : syracuseStep 2129815 = 3194723) B3194723
theorem B8086661 : Blo 2129435 8086661 := bbase (se 4 (by rfl) ⟨758124, by rfl⟩ : syracuseStep 8086661 = 1516249) (by norm_num)
theorem B5391107 : Blo 2129435 5391107 := bstep (se 1 (by rfl) ⟨4043330, by rfl⟩ : syracuseStep 5391107 = 8086661) B8086661
theorem B3594071 : Blo 2129435 3594071 := bstep (se 1 (by rfl) ⟨2695553, by rfl⟩ : syracuseStep 3594071 = 5391107) B5391107
theorem B2396047 : Blo 2129435 2396047 := bstep (se 1 (by rfl) ⟨1797035, by rfl⟩ : syracuseStep 2396047 = 3594071) B3594071
theorem B3194729 : Blo 2129435 3194729 := bstep (se 2 (by rfl) ⟨1198023, by rfl⟩ : syracuseStep 3194729 = 2396047) B2396047
theorem B2129819 : Blo 2129435 2129819 := bstep (se 1 (by rfl) ⟨1597364, by rfl⟩ : syracuseStep 2129819 = 3194729) B3194729
theorem B3838013 : Blo 2129435 3838013 := bbase (se 3 (by rfl) ⟨719627, by rfl⟩ : syracuseStep 3838013 = 1439255) (by norm_num)
theorem B2558675 : Blo 2129435 2558675 := bstep (se 1 (by rfl) ⟨1919006, by rfl⟩ : syracuseStep 2558675 = 3838013) B3838013
theorem B6823133 : Blo 2129435 6823133 := bstep (se 3 (by rfl) ⟨1279337, by rfl⟩ : syracuseStep 6823133 = 2558675) B2558675
theorem B4548755 : Blo 2129435 4548755 := bstep (se 1 (by rfl) ⟨3411566, by rfl⟩ : syracuseStep 4548755 = 6823133) B6823133
theorem B12130013 : Blo 2129435 12130013 := bstep (se 3 (by rfl) ⟨2274377, by rfl⟩ : syracuseStep 12130013 = 4548755) B4548755
theorem B8086675 : Blo 2129435 8086675 := bstep (se 1 (by rfl) ⟨6065006, by rfl⟩ : syracuseStep 8086675 = 12130013) B12130013
theorem B10782233 : Blo 2129435 10782233 := bstep (se 2 (by rfl) ⟨4043337, by rfl⟩ : syracuseStep 10782233 = 8086675) B8086675
theorem B7188155 : Blo 2129435 7188155 := bstep (se 1 (by rfl) ⟨5391116, by rfl⟩ : syracuseStep 7188155 = 10782233) B10782233
theorem B4792103 : Blo 2129435 4792103 := bstep (se 1 (by rfl) ⟨3594077, by rfl⟩ : syracuseStep 4792103 = 7188155) B7188155
theorem B3194735 : Blo 2129435 3194735 := bstep (se 1 (by rfl) ⟨2396051, by rfl⟩ : syracuseStep 3194735 = 4792103) B4792103
theorem B2129823 : Blo 2129435 2129823 := bstep (se 1 (by rfl) ⟨1597367, by rfl⟩ : syracuseStep 2129823 = 3194735) B3194735
theorem B3194741 : Blo 2129435 3194741 := bbase (se 5 (by rfl) ⟨149753, by rfl⟩ : syracuseStep 3194741 = 299507) (by norm_num)
theorem B2129827 : Blo 2129435 2129827 := bstep (se 1 (by rfl) ⟨1597370, by rfl⟩ : syracuseStep 2129827 = 3194741) B3194741
theorem B4548773 : Blo 2129435 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B3032515 : Blo 2129435 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B4043353 : Blo 2129435 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B5391137 : Blo 2129435 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B3594091 : Blo 2129435 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B4792121 : Blo 2129435 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B3194747 : Blo 2129435 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B2129831 : Blo 2129435 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B2396065 : Blo 2129435 2396065 := bbase (se 2 (by rfl) ⟨898524, by rfl⟩ : syracuseStep 2396065 = 1797049) (by norm_num)
theorem B3194753 : Blo 2129435 3194753 := bstep (se 2 (by rfl) ⟨1198032, by rfl⟩ : syracuseStep 3194753 = 2396065) B2396065
theorem B2129835 : Blo 2129435 2129835 := bstep (se 1 (by rfl) ⟨1597376, by rfl⟩ : syracuseStep 2129835 = 3194753) B3194753
theorem B5391157 : Blo 2129435 5391157 := bbase (se 5 (by rfl) ⟨252710, by rfl⟩ : syracuseStep 5391157 = 505421) (by norm_num)
theorem B7188209 : Blo 2129435 7188209 := bstep (se 2 (by rfl) ⟨2695578, by rfl⟩ : syracuseStep 7188209 = 5391157) B5391157
theorem B4792139 : Blo 2129435 4792139 := bstep (se 1 (by rfl) ⟨3594104, by rfl⟩ : syracuseStep 4792139 = 7188209) B7188209
theorem B3194759 : Blo 2129435 3194759 := bstep (se 1 (by rfl) ⟨2396069, by rfl⟩ : syracuseStep 3194759 = 4792139) B4792139
theorem B2129839 : Blo 2129435 2129839 := bstep (se 1 (by rfl) ⟨1597379, by rfl⟩ : syracuseStep 2129839 = 3194759) B3194759
theorem B3194765 : Blo 2129435 3194765 := bbase (se 3 (by rfl) ⟨599018, by rfl⟩ : syracuseStep 3194765 = 1198037) (by norm_num)
theorem B2129843 : Blo 2129435 2129843 := bstep (se 1 (by rfl) ⟨1597382, by rfl⟩ : syracuseStep 2129843 = 3194765) B3194765
theorem B4792157 : Blo 2129435 4792157 := bbase (se 3 (by rfl) ⟨898529, by rfl⟩ : syracuseStep 4792157 = 1797059) (by norm_num)
theorem B3194771 : Blo 2129435 3194771 := bstep (se 1 (by rfl) ⟨2396078, by rfl⟩ : syracuseStep 3194771 = 4792157) B4792157
theorem B2129847 : Blo 2129435 2129847 := bstep (se 1 (by rfl) ⟨1597385, by rfl⟩ : syracuseStep 2129847 = 3194771) B3194771
theorem B3594125 : Blo 2129435 3594125 := bbase (se 3 (by rfl) ⟨673898, by rfl⟩ : syracuseStep 3594125 = 1347797) (by norm_num)
theorem B2396083 : Blo 2129435 2396083 := bstep (se 1 (by rfl) ⟨1797062, by rfl⟩ : syracuseStep 2396083 = 3594125) B3594125
theorem B3194777 : Blo 2129435 3194777 := bstep (se 2 (by rfl) ⟨1198041, by rfl⟩ : syracuseStep 3194777 = 2396083) B2396083
theorem B2129851 : Blo 2129435 2129851 := bstep (se 1 (by rfl) ⟨1597388, by rfl⟩ : syracuseStep 2129851 = 3194777) B3194777
theorem B10234853 : Blo 2129435 10234853 := bbase (se 4 (by rfl) ⟨959517, by rfl⟩ : syracuseStep 10234853 = 1919035) (by norm_num)
theorem B6823235 : Blo 2129435 6823235 := bstep (se 1 (by rfl) ⟨5117426, by rfl⟩ : syracuseStep 6823235 = 10234853) B10234853
theorem B18195293 : Blo 2129435 18195293 := bstep (se 3 (by rfl) ⟨3411617, by rfl⟩ : syracuseStep 18195293 = 6823235) B6823235
theorem B12130195 : Blo 2129435 12130195 := bstep (se 1 (by rfl) ⟨9097646, by rfl⟩ : syracuseStep 12130195 = 18195293) B18195293
theorem B16173593 : Blo 2129435 16173593 := bstep (se 2 (by rfl) ⟨6065097, by rfl⟩ : syracuseStep 16173593 = 12130195) B12130195
theorem B10782395 : Blo 2129435 10782395 := bstep (se 1 (by rfl) ⟨8086796, by rfl⟩ : syracuseStep 10782395 = 16173593) B16173593
theorem B7188263 : Blo 2129435 7188263 := bstep (se 1 (by rfl) ⟨5391197, by rfl⟩ : syracuseStep 7188263 = 10782395) B10782395
theorem B4792175 : Blo 2129435 4792175 := bstep (se 1 (by rfl) ⟨3594131, by rfl⟩ : syracuseStep 4792175 = 7188263) B7188263
theorem B3194783 : Blo 2129435 3194783 := bstep (se 1 (by rfl) ⟨2396087, by rfl⟩ : syracuseStep 3194783 = 4792175) B4792175
theorem B2129855 : Blo 2129435 2129855 := bstep (se 1 (by rfl) ⟨1597391, by rfl⟩ : syracuseStep 2129855 = 3194783) B3194783
theorem B3194789 : Blo 2129435 3194789 := bbase (se 4 (by rfl) ⟨299511, by rfl⟩ : syracuseStep 3194789 = 599023) (by norm_num)
theorem B2129859 : Blo 2129435 2129859 := bstep (se 1 (by rfl) ⟨1597394, by rfl⟩ : syracuseStep 2129859 = 3194789) B3194789
theorem B2695609 : Blo 2129435 2695609 := bbase (se 2 (by rfl) ⟨1010853, by rfl⟩ : syracuseStep 2695609 = 2021707) (by norm_num)
theorem B3594145 : Blo 2129435 3594145 := bstep (se 2 (by rfl) ⟨1347804, by rfl⟩ : syracuseStep 3594145 = 2695609) B2695609
theorem B4792193 : Blo 2129435 4792193 := bstep (se 2 (by rfl) ⟨1797072, by rfl⟩ : syracuseStep 4792193 = 3594145) B3594145
theorem B3194795 : Blo 2129435 3194795 := bstep (se 1 (by rfl) ⟨2396096, by rfl⟩ : syracuseStep 3194795 = 4792193) B4792193
theorem B2129863 : Blo 2129435 2129863 := bstep (se 1 (by rfl) ⟨1597397, by rfl⟩ : syracuseStep 2129863 = 3194795) B3194795
theorem B2396101 : Blo 2129435 2396101 := bbase (se 4 (by rfl) ⟨224634, by rfl⟩ : syracuseStep 2396101 = 449269) (by norm_num)
theorem B3194801 : Blo 2129435 3194801 := bstep (se 2 (by rfl) ⟨1198050, by rfl⟩ : syracuseStep 3194801 = 2396101) B2396101
theorem B2129867 : Blo 2129435 2129867 := bstep (se 1 (by rfl) ⟨1597400, by rfl⟩ : syracuseStep 2129867 = 3194801) B3194801
theorem B4043429 : Blo 2129435 4043429 := bbase (se 4 (by rfl) ⟨379071, by rfl⟩ : syracuseStep 4043429 = 758143) (by norm_num)
theorem B2695619 : Blo 2129435 2695619 := bstep (se 1 (by rfl) ⟨2021714, by rfl⟩ : syracuseStep 2695619 = 4043429) B4043429
theorem B7188317 : Blo 2129435 7188317 := bstep (se 3 (by rfl) ⟨1347809, by rfl⟩ : syracuseStep 7188317 = 2695619) B2695619
theorem B4792211 : Blo 2129435 4792211 := bstep (se 1 (by rfl) ⟨3594158, by rfl⟩ : syracuseStep 4792211 = 7188317) B7188317
theorem B3194807 : Blo 2129435 3194807 := bstep (se 1 (by rfl) ⟨2396105, by rfl⟩ : syracuseStep 3194807 = 4792211) B4792211
theorem B2129871 : Blo 2129435 2129871 := bstep (se 1 (by rfl) ⟨1597403, by rfl⟩ : syracuseStep 2129871 = 3194807) B3194807
theorem B3194813 : Blo 2129435 3194813 := bbase (se 3 (by rfl) ⟨599027, by rfl⟩ : syracuseStep 3194813 = 1198055) (by norm_num)
theorem B2129875 : Blo 2129435 2129875 := bstep (se 1 (by rfl) ⟨1597406, by rfl⟩ : syracuseStep 2129875 = 3194813) B3194813
theorem B4792229 : Blo 2129435 4792229 := bbase (se 4 (by rfl) ⟨449271, by rfl⟩ : syracuseStep 4792229 = 898543) (by norm_num)
theorem B3194819 : Blo 2129435 3194819 := bstep (se 1 (by rfl) ⟨2396114, by rfl⟩ : syracuseStep 3194819 = 4792229) B4792229
theorem B2129879 : Blo 2129435 2129879 := bstep (se 1 (by rfl) ⟨1597409, by rfl⟩ : syracuseStep 2129879 = 3194819) B3194819
theorem B5391269 : Blo 2129435 5391269 := bbase (se 4 (by rfl) ⟨505431, by rfl⟩ : syracuseStep 5391269 = 1010863) (by norm_num)
theorem B3594179 : Blo 2129435 3594179 := bstep (se 1 (by rfl) ⟨2695634, by rfl⟩ : syracuseStep 3594179 = 5391269) B5391269
theorem B2396119 : Blo 2129435 2396119 := bstep (se 1 (by rfl) ⟨1797089, by rfl⟩ : syracuseStep 2396119 = 3594179) B3594179
theorem B3194825 : Blo 2129435 3194825 := bstep (se 2 (by rfl) ⟨1198059, by rfl⟩ : syracuseStep 3194825 = 2396119) B2396119
theorem B2129883 : Blo 2129435 2129883 := bstep (se 1 (by rfl) ⟨1597412, by rfl⟩ : syracuseStep 2129883 = 3194825) B3194825
theorem B6065189 : Blo 2129435 6065189 := bbase (se 4 (by rfl) ⟨568611, by rfl⟩ : syracuseStep 6065189 = 1137223) (by norm_num)
theorem B4043459 : Blo 2129435 4043459 := bstep (se 1 (by rfl) ⟨3032594, by rfl⟩ : syracuseStep 4043459 = 6065189) B6065189
theorem B10782557 : Blo 2129435 10782557 := bstep (se 3 (by rfl) ⟨2021729, by rfl⟩ : syracuseStep 10782557 = 4043459) B4043459
theorem B7188371 : Blo 2129435 7188371 := bstep (se 1 (by rfl) ⟨5391278, by rfl⟩ : syracuseStep 7188371 = 10782557) B10782557
theorem B4792247 : Blo 2129435 4792247 := bstep (se 1 (by rfl) ⟨3594185, by rfl⟩ : syracuseStep 4792247 = 7188371) B7188371
theorem B3194831 : Blo 2129435 3194831 := bstep (se 1 (by rfl) ⟨2396123, by rfl⟩ : syracuseStep 3194831 = 4792247) B4792247
theorem B2129887 : Blo 2129435 2129887 := bstep (se 1 (by rfl) ⟨1597415, by rfl⟩ : syracuseStep 2129887 = 3194831) B3194831
theorem B3194837 : Blo 2129435 3194837 := bbase (se 7 (by rfl) ⟨37439, by rfl⟩ : syracuseStep 3194837 = 74879) (by norm_num)
theorem B2129891 : Blo 2129435 2129891 := bstep (se 1 (by rfl) ⟨1597418, by rfl⟩ : syracuseStep 2129891 = 3194837) B3194837
theorem B8086949 : Blo 2129435 8086949 := bbase (se 4 (by rfl) ⟨758151, by rfl⟩ : syracuseStep 8086949 = 1516303) (by norm_num)
theorem B5391299 : Blo 2129435 5391299 := bstep (se 1 (by rfl) ⟨4043474, by rfl⟩ : syracuseStep 5391299 = 8086949) B8086949
theorem B3594199 : Blo 2129435 3594199 := bstep (se 1 (by rfl) ⟨2695649, by rfl⟩ : syracuseStep 3594199 = 5391299) B5391299
theorem B4792265 : Blo 2129435 4792265 := bstep (se 2 (by rfl) ⟨1797099, by rfl⟩ : syracuseStep 4792265 = 3594199) B3594199
theorem B3194843 : Blo 2129435 3194843 := bstep (se 1 (by rfl) ⟨2396132, by rfl⟩ : syracuseStep 3194843 = 4792265) B4792265
theorem B2129895 : Blo 2129435 2129895 := bstep (se 1 (by rfl) ⟨1597421, by rfl⟩ : syracuseStep 2129895 = 3194843) B3194843
theorem B2396137 : Blo 2129435 2396137 := bbase (se 2 (by rfl) ⟨898551, by rfl⟩ : syracuseStep 2396137 = 1797103) (by norm_num)
theorem B3194849 : Blo 2129435 3194849 := bstep (se 2 (by rfl) ⟨1198068, by rfl⟩ : syracuseStep 3194849 = 2396137) B2396137
theorem B2129899 : Blo 2129435 2129899 := bstep (se 1 (by rfl) ⟨1597424, by rfl⟩ : syracuseStep 2129899 = 3194849) B3194849
theorem B5258141 : Blo 2129435 5258141 := bbase (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) (by norm_num)
theorem B3505427 : Blo 2129435 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B2336951 : Blo 2129435 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B6231869 : Blo 2129435 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B4154579 : Blo 2129435 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B2769719 : Blo 2129435 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B7385917 : Blo 2129435 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B9847889 : Blo 2129435 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B6565259 : Blo 2129435 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B17507357 : Blo 2129435 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B11671571 : Blo 2129435 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B31124189 : Blo 2129435 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B20749459 : Blo 2129435 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B27665945 : Blo 2129435 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B18443963 : Blo 2129435 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B12295975 : Blo 2129435 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B16394633 : Blo 2129435 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B10929755 : Blo 2129435 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B29146013 : Blo 2129435 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B19430675 : Blo 2129435 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B12953783 : Blo 2129435 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B8635855 : Blo 2129435 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B11514473 : Blo 2129435 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B7676315 : Blo 2129435 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B5117543 : Blo 2129435 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B3411695 : Blo 2129435 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B2274463 : Blo 2129435 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B12130469 : Blo 2129435 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B8086979 : Blo 2129435 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B5391319 : Blo 2129435 5391319 := bstep (se 1 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 5391319 = 8086979) B8086979
theorem B7188425 : Blo 2129435 7188425 := bstep (se 2 (by rfl) ⟨2695659, by rfl⟩ : syracuseStep 7188425 = 5391319) B5391319
theorem B4792283 : Blo 2129435 4792283 := bstep (se 1 (by rfl) ⟨3594212, by rfl⟩ : syracuseStep 4792283 = 7188425) B7188425
theorem B3194855 : Blo 2129435 3194855 := bstep (se 1 (by rfl) ⟨2396141, by rfl⟩ : syracuseStep 3194855 = 4792283) B4792283
theorem B2129903 : Blo 2129435 2129903 := bstep (se 1 (by rfl) ⟨1597427, by rfl⟩ : syracuseStep 2129903 = 3194855) B3194855
theorem B3194861 : Blo 2129435 3194861 := bbase (se 3 (by rfl) ⟨599036, by rfl⟩ : syracuseStep 3194861 = 1198073) (by norm_num)
theorem B2129907 : Blo 2129435 2129907 := bstep (se 1 (by rfl) ⟨1597430, by rfl⟩ : syracuseStep 2129907 = 3194861) B3194861
theorem B4792301 : Blo 2129435 4792301 := bbase (se 3 (by rfl) ⟨898556, by rfl⟩ : syracuseStep 4792301 = 1797113) (by norm_num)
theorem B3194867 : Blo 2129435 3194867 := bstep (se 1 (by rfl) ⟨2396150, by rfl⟩ : syracuseStep 3194867 = 4792301) B4792301
theorem B2129911 : Blo 2129435 2129911 := bstep (se 1 (by rfl) ⟨1597433, by rfl⟩ : syracuseStep 2129911 = 3194867) B3194867
theorem B5117573 : Blo 2129435 5117573 := bbase (se 4 (by rfl) ⟨479772, by rfl⟩ : syracuseStep 5117573 = 959545) (by norm_num)
theorem B3411715 : Blo 2129435 3411715 := bstep (se 1 (by rfl) ⟨2558786, by rfl⟩ : syracuseStep 3411715 = 5117573) B5117573
theorem B4548953 : Blo 2129435 4548953 := bstep (se 2 (by rfl) ⟨1705857, by rfl⟩ : syracuseStep 4548953 = 3411715) B3411715
theorem B3032635 : Blo 2129435 3032635 := bstep (se 1 (by rfl) ⟨2274476, by rfl⟩ : syracuseStep 3032635 = 4548953) B4548953
theorem B4043513 : Blo 2129435 4043513 := bstep (se 2 (by rfl) ⟨1516317, by rfl⟩ : syracuseStep 4043513 = 3032635) B3032635
theorem B2695675 : Blo 2129435 2695675 := bstep (se 1 (by rfl) ⟨2021756, by rfl⟩ : syracuseStep 2695675 = 4043513) B4043513
theorem B3594233 : Blo 2129435 3594233 := bstep (se 2 (by rfl) ⟨1347837, by rfl⟩ : syracuseStep 3594233 = 2695675) B2695675
theorem B2396155 : Blo 2129435 2396155 := bstep (se 1 (by rfl) ⟨1797116, by rfl⟩ : syracuseStep 2396155 = 3594233) B3594233
theorem B3194873 : Blo 2129435 3194873 := bstep (se 2 (by rfl) ⟨1198077, by rfl⟩ : syracuseStep 3194873 = 2396155) B2396155
theorem B2129915 : Blo 2129435 2129915 := bstep (se 1 (by rfl) ⟨1597436, by rfl⟩ : syracuseStep 2129915 = 3194873) B3194873
theorem B3282653 : Blo 2129435 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B2188435 : Blo 2129435 2188435 := bstep (se 1 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 2188435 = 3282653) B3282653
theorem B2917913 : Blo 2129435 2917913 := bstep (se 2 (by rfl) ⟨1094217, by rfl⟩ : syracuseStep 2917913 = 2188435) B2188435
theorem B31124405 : Blo 2129435 31124405 := bstep (se 5 (by rfl) ⟨1458956, by rfl⟩ : syracuseStep 31124405 = 2917913) B2917913
theorem B20749603 : Blo 2129435 20749603 := bstep (se 1 (by rfl) ⟨15562202, by rfl⟩ : syracuseStep 20749603 = 31124405) B31124405
theorem B27666137 : Blo 2129435 27666137 := bstep (se 2 (by rfl) ⟨10374801, by rfl⟩ : syracuseStep 27666137 = 20749603) B20749603
theorem B73776365 : Blo 2129435 73776365 := bstep (se 3 (by rfl) ⟨13833068, by rfl⟩ : syracuseStep 73776365 = 27666137) B27666137
theorem B49184243 : Blo 2129435 49184243 := bstep (se 1 (by rfl) ⟨36888182, by rfl⟩ : syracuseStep 49184243 = 73776365) B73776365
theorem B32789495 : Blo 2129435 32789495 := bstep (se 1 (by rfl) ⟨24592121, by rfl⟩ : syracuseStep 32789495 = 49184243) B49184243
theorem B21859663 : Blo 2129435 21859663 := bstep (se 1 (by rfl) ⟨16394747, by rfl⟩ : syracuseStep 21859663 = 32789495) B32789495
theorem B466339477 : Blo 2129435 466339477 := bstep (se 6 (by rfl) ⟨10929831, by rfl⟩ : syracuseStep 466339477 = 21859663) B21859663
theorem B621785969 : Blo 2129435 621785969 := bstep (se 2 (by rfl) ⟨233169738, by rfl⟩ : syracuseStep 621785969 = 466339477) B466339477
theorem B414523979 : Blo 2129435 414523979 := bstep (se 1 (by rfl) ⟨310892984, by rfl⟩ : syracuseStep 414523979 = 621785969) B621785969
theorem B276349319 : Blo 2129435 276349319 := bstep (se 1 (by rfl) ⟨207261989, by rfl⟩ : syracuseStep 276349319 = 414523979) B414523979
theorem B184232879 : Blo 2129435 184232879 := bstep (se 1 (by rfl) ⟨138174659, by rfl⟩ : syracuseStep 184232879 = 276349319) B276349319
theorem B122821919 : Blo 2129435 122821919 := bstep (se 1 (by rfl) ⟨92116439, by rfl⟩ : syracuseStep 122821919 = 184232879) B184232879
theorem B81881279 : Blo 2129435 81881279 := bstep (se 1 (by rfl) ⟨61410959, by rfl⟩ : syracuseStep 81881279 = 122821919) B122821919
theorem B54587519 : Blo 2129435 54587519 := bstep (se 1 (by rfl) ⟨40940639, by rfl⟩ : syracuseStep 54587519 = 81881279) B81881279
theorem B36391679 : Blo 2129435 36391679 := bstep (se 1 (by rfl) ⟨27293759, by rfl⟩ : syracuseStep 36391679 = 54587519) B54587519
theorem B24261119 : Blo 2129435 24261119 := bstep (se 1 (by rfl) ⟨18195839, by rfl⟩ : syracuseStep 24261119 = 36391679) B36391679
theorem B16174079 : Blo 2129435 16174079 := bstep (se 1 (by rfl) ⟨12130559, by rfl⟩ : syracuseStep 16174079 = 24261119) B24261119
theorem B10782719 : Blo 2129435 10782719 := bstep (se 1 (by rfl) ⟨8087039, by rfl⟩ : syracuseStep 10782719 = 16174079) B16174079
theorem B7188479 : Blo 2129435 7188479 := bstep (se 1 (by rfl) ⟨5391359, by rfl⟩ : syracuseStep 7188479 = 10782719) B10782719
theorem B4792319 : Blo 2129435 4792319 := bstep (se 1 (by rfl) ⟨3594239, by rfl⟩ : syracuseStep 4792319 = 7188479) B7188479
theorem B3194879 : Blo 2129435 3194879 := bstep (se 1 (by rfl) ⟨2396159, by rfl⟩ : syracuseStep 3194879 = 4792319) B4792319
theorem B2129919 : Blo 2129435 2129919 := bstep (se 1 (by rfl) ⟨1597439, by rfl⟩ : syracuseStep 2129919 = 3194879) B3194879
theorem B3194885 : Blo 2129435 3194885 := bbase (se 4 (by rfl) ⟨299520, by rfl⟩ : syracuseStep 3194885 = 599041) (by norm_num)
theorem B2129923 : Blo 2129435 2129923 := bstep (se 1 (by rfl) ⟨1597442, by rfl⟩ : syracuseStep 2129923 = 3194885) B3194885
theorem B3594253 : Blo 2129435 3594253 := bbase (se 3 (by rfl) ⟨673922, by rfl⟩ : syracuseStep 3594253 = 1347845) (by norm_num)
theorem B4792337 : Blo 2129435 4792337 := bstep (se 2 (by rfl) ⟨1797126, by rfl⟩ : syracuseStep 4792337 = 3594253) B3594253
theorem B3194891 : Blo 2129435 3194891 := bstep (se 1 (by rfl) ⟨2396168, by rfl⟩ : syracuseStep 3194891 = 4792337) B4792337
theorem B2129927 : Blo 2129435 2129927 := bstep (se 1 (by rfl) ⟨1597445, by rfl⟩ : syracuseStep 2129927 = 3194891) B3194891
theorem B2396173 : Blo 2129435 2396173 := bbase (se 3 (by rfl) ⟨449282, by rfl⟩ : syracuseStep 2396173 = 898565) (by norm_num)
theorem B3194897 : Blo 2129435 3194897 := bstep (se 2 (by rfl) ⟨1198086, by rfl⟩ : syracuseStep 3194897 = 2396173) B2396173
theorem B2129931 : Blo 2129435 2129931 := bstep (se 1 (by rfl) ⟨1597448, by rfl⟩ : syracuseStep 2129931 = 3194897) B3194897
theorem B7188533 : Blo 2129435 7188533 := bbase (se 5 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 7188533 = 673925) (by norm_num)
theorem B4792355 : Blo 2129435 4792355 := bstep (se 1 (by rfl) ⟨3594266, by rfl⟩ : syracuseStep 4792355 = 7188533) B7188533
theorem B3194903 : Blo 2129435 3194903 := bstep (se 1 (by rfl) ⟨2396177, by rfl⟩ : syracuseStep 3194903 = 4792355) B4792355
theorem B2129935 : Blo 2129435 2129935 := bstep (se 1 (by rfl) ⟨1597451, by rfl⟩ : syracuseStep 2129935 = 3194903) B3194903
theorem B3194909 : Blo 2129435 3194909 := bbase (se 3 (by rfl) ⟨599045, by rfl⟩ : syracuseStep 3194909 = 1198091) (by norm_num)
theorem B2129939 : Blo 2129435 2129939 := bstep (se 1 (by rfl) ⟨1597454, by rfl⟩ : syracuseStep 2129939 = 3194909) B3194909
theorem B4792373 : Blo 2129435 4792373 := bbase (se 5 (by rfl) ⟨224642, by rfl⟩ : syracuseStep 4792373 = 449285) (by norm_num)
theorem B3194915 : Blo 2129435 3194915 := bstep (se 1 (by rfl) ⟨2396186, by rfl⟩ : syracuseStep 3194915 = 4792373) B4792373
theorem B2129943 : Blo 2129435 2129943 := bstep (se 1 (by rfl) ⟨1597457, by rfl⟩ : syracuseStep 2129943 = 3194915) B3194915
theorem B8753861 : Blo 2129435 8753861 := bbase (se 4 (by rfl) ⟨820674, by rfl⟩ : syracuseStep 8753861 = 1641349) (by norm_num)
theorem B5835907 : Blo 2129435 5835907 := bstep (se 1 (by rfl) ⟨4376930, by rfl⟩ : syracuseStep 5835907 = 8753861) B8753861
theorem B31124837 : Blo 2129435 31124837 := bstep (se 4 (by rfl) ⟨2917953, by rfl⟩ : syracuseStep 31124837 = 5835907) B5835907
theorem B20749891 : Blo 2129435 20749891 := bstep (se 1 (by rfl) ⟨15562418, by rfl⟩ : syracuseStep 20749891 = 31124837) B31124837
theorem B27666521 : Blo 2129435 27666521 := bstep (se 2 (by rfl) ⟨10374945, by rfl⟩ : syracuseStep 27666521 = 20749891) B20749891
theorem B18444347 : Blo 2129435 18444347 := bstep (se 1 (by rfl) ⟨13833260, by rfl⟩ : syracuseStep 18444347 = 27666521) B27666521
theorem B12296231 : Blo 2129435 12296231 := bstep (se 1 (by rfl) ⟨9222173, by rfl⟩ : syracuseStep 12296231 = 18444347) B18444347
theorem B8197487 : Blo 2129435 8197487 := bstep (se 1 (by rfl) ⟨6148115, by rfl⟩ : syracuseStep 8197487 = 12296231) B12296231
theorem B5464991 : Blo 2129435 5464991 := bstep (se 1 (by rfl) ⟨4098743, by rfl⟩ : syracuseStep 5464991 = 8197487) B8197487
theorem B3643327 : Blo 2129435 3643327 := bstep (se 1 (by rfl) ⟨2732495, by rfl⟩ : syracuseStep 3643327 = 5464991) B5464991
theorem B4857769 : Blo 2129435 4857769 := bstep (se 2 (by rfl) ⟨1821663, by rfl⟩ : syracuseStep 4857769 = 3643327) B3643327
theorem B6477025 : Blo 2129435 6477025 := bstep (se 2 (by rfl) ⟨2428884, by rfl⟩ : syracuseStep 6477025 = 4857769) B4857769
theorem B8636033 : Blo 2129435 8636033 := bstep (se 2 (by rfl) ⟨3238512, by rfl⟩ : syracuseStep 8636033 = 6477025) B6477025
theorem B5757355 : Blo 2129435 5757355 := bstep (se 1 (by rfl) ⟨4318016, by rfl⟩ : syracuseStep 5757355 = 8636033) B8636033
theorem B7676473 : Blo 2129435 7676473 := bstep (se 2 (by rfl) ⟨2878677, by rfl⟩ : syracuseStep 7676473 = 5757355) B5757355
theorem B10235297 : Blo 2129435 10235297 := bstep (se 2 (by rfl) ⟨3838236, by rfl⟩ : syracuseStep 10235297 = 7676473) B7676473
theorem B6823531 : Blo 2129435 6823531 := bstep (se 1 (by rfl) ⟨5117648, by rfl⟩ : syracuseStep 6823531 = 10235297) B10235297
theorem B9098041 : Blo 2129435 9098041 := bstep (se 2 (by rfl) ⟨3411765, by rfl⟩ : syracuseStep 9098041 = 6823531) B6823531
theorem B12130721 : Blo 2129435 12130721 := bstep (se 2 (by rfl) ⟨4549020, by rfl⟩ : syracuseStep 12130721 = 9098041) B9098041
theorem B8087147 : Blo 2129435 8087147 := bstep (se 1 (by rfl) ⟨6065360, by rfl⟩ : syracuseStep 8087147 = 12130721) B12130721
theorem B5391431 : Blo 2129435 5391431 := bstep (se 1 (by rfl) ⟨4043573, by rfl⟩ : syracuseStep 5391431 = 8087147) B8087147
theorem B3594287 : Blo 2129435 3594287 := bstep (se 1 (by rfl) ⟨2695715, by rfl⟩ : syracuseStep 3594287 = 5391431) B5391431
theorem B2396191 : Blo 2129435 2396191 := bstep (se 1 (by rfl) ⟨1797143, by rfl⟩ : syracuseStep 2396191 = 3594287) B3594287
theorem B3194921 : Blo 2129435 3194921 := bstep (se 2 (by rfl) ⟨1198095, by rfl⟩ : syracuseStep 3194921 = 2396191) B2396191
theorem B2129947 : Blo 2129435 2129947 := bstep (se 1 (by rfl) ⟨1597460, by rfl⟩ : syracuseStep 2129947 = 3194921) B3194921
theorem B5757365 : Blo 2129435 5757365 := bbase (se 5 (by rfl) ⟨269876, by rfl⟩ : syracuseStep 5757365 = 539753) (by norm_num)
theorem B15352973 : Blo 2129435 15352973 := bstep (se 3 (by rfl) ⟨2878682, by rfl⟩ : syracuseStep 15352973 = 5757365) B5757365
theorem B10235315 : Blo 2129435 10235315 := bstep (se 1 (by rfl) ⟨7676486, by rfl⟩ : syracuseStep 10235315 = 15352973) B15352973
theorem B6823543 : Blo 2129435 6823543 := bstep (se 1 (by rfl) ⟨5117657, by rfl⟩ : syracuseStep 6823543 = 10235315) B10235315
theorem B9098057 : Blo 2129435 9098057 := bstep (se 2 (by rfl) ⟨3411771, by rfl⟩ : syracuseStep 9098057 = 6823543) B6823543
theorem B6065371 : Blo 2129435 6065371 := bstep (se 1 (by rfl) ⟨4549028, by rfl⟩ : syracuseStep 6065371 = 9098057) B9098057
theorem B8087161 : Blo 2129435 8087161 := bstep (se 2 (by rfl) ⟨3032685, by rfl⟩ : syracuseStep 8087161 = 6065371) B6065371
theorem B10782881 : Blo 2129435 10782881 := bstep (se 2 (by rfl) ⟨4043580, by rfl⟩ : syracuseStep 10782881 = 8087161) B8087161
theorem B7188587 : Blo 2129435 7188587 := bstep (se 1 (by rfl) ⟨5391440, by rfl⟩ : syracuseStep 7188587 = 10782881) B10782881
theorem B4792391 : Blo 2129435 4792391 := bstep (se 1 (by rfl) ⟨3594293, by rfl⟩ : syracuseStep 4792391 = 7188587) B7188587
theorem B3194927 : Blo 2129435 3194927 := bstep (se 1 (by rfl) ⟨2396195, by rfl⟩ : syracuseStep 3194927 = 4792391) B4792391
theorem B2129951 : Blo 2129435 2129951 := bstep (se 1 (by rfl) ⟨1597463, by rfl⟩ : syracuseStep 2129951 = 3194927) B3194927
theorem B3194933 : Blo 2129435 3194933 := bbase (se 5 (by rfl) ⟨149762, by rfl⟩ : syracuseStep 3194933 = 299525) (by norm_num)
theorem B2129955 : Blo 2129435 2129955 := bstep (se 1 (by rfl) ⟨1597466, by rfl⟩ : syracuseStep 2129955 = 3194933) B3194933
theorem B5391461 : Blo 2129435 5391461 := bbase (se 4 (by rfl) ⟨505449, by rfl⟩ : syracuseStep 5391461 = 1010899) (by norm_num)
theorem B3594307 : Blo 2129435 3594307 := bstep (se 1 (by rfl) ⟨2695730, by rfl⟩ : syracuseStep 3594307 = 5391461) B5391461
theorem B4792409 : Blo 2129435 4792409 := bstep (se 2 (by rfl) ⟨1797153, by rfl⟩ : syracuseStep 4792409 = 3594307) B3594307
theorem B3194939 : Blo 2129435 3194939 := bstep (se 1 (by rfl) ⟨2396204, by rfl⟩ : syracuseStep 3194939 = 4792409) B4792409
theorem B2129959 : Blo 2129435 2129959 := bstep (se 1 (by rfl) ⟨1597469, by rfl⟩ : syracuseStep 2129959 = 3194939) B3194939
theorem B2396209 : Blo 2129435 2396209 := bbase (se 2 (by rfl) ⟨898578, by rfl⟩ : syracuseStep 2396209 = 1797157) (by norm_num)
theorem B3194945 : Blo 2129435 3194945 := bstep (se 2 (by rfl) ⟨1198104, by rfl⟩ : syracuseStep 3194945 = 2396209) B2396209
theorem B2129963 : Blo 2129435 2129963 := bstep (se 1 (by rfl) ⟨1597472, by rfl⟩ : syracuseStep 2129963 = 3194945) B3194945
theorem B10930085 : Blo 2129435 10930085 := bbase (se 4 (by rfl) ⟨1024695, by rfl⟩ : syracuseStep 10930085 = 2049391) (by norm_num)
theorem B7286723 : Blo 2129435 7286723 := bstep (se 1 (by rfl) ⟨5465042, by rfl⟩ : syracuseStep 7286723 = 10930085) B10930085
theorem B4857815 : Blo 2129435 4857815 := bstep (se 1 (by rfl) ⟨3643361, by rfl⟩ : syracuseStep 4857815 = 7286723) B7286723
theorem B3238543 : Blo 2129435 3238543 := bstep (se 1 (by rfl) ⟨2428907, by rfl⟩ : syracuseStep 3238543 = 4857815) B4857815
theorem B4318057 : Blo 2129435 4318057 := bstep (se 2 (by rfl) ⟨1619271, by rfl⟩ : syracuseStep 4318057 = 3238543) B3238543
theorem B5757409 : Blo 2129435 5757409 := bstep (se 2 (by rfl) ⟨2159028, by rfl⟩ : syracuseStep 5757409 = 4318057) B4318057
theorem B7676545 : Blo 2129435 7676545 := bstep (se 2 (by rfl) ⟨2878704, by rfl⟩ : syracuseStep 7676545 = 5757409) B5757409
theorem B10235393 : Blo 2129435 10235393 := bstep (se 2 (by rfl) ⟨3838272, by rfl⟩ : syracuseStep 10235393 = 7676545) B7676545
theorem B6823595 : Blo 2129435 6823595 := bstep (se 1 (by rfl) ⟨5117696, by rfl⟩ : syracuseStep 6823595 = 10235393) B10235393
theorem B4549063 : Blo 2129435 4549063 := bstep (se 1 (by rfl) ⟨3411797, by rfl⟩ : syracuseStep 4549063 = 6823595) B6823595
theorem B6065417 : Blo 2129435 6065417 := bstep (se 2 (by rfl) ⟨2274531, by rfl⟩ : syracuseStep 6065417 = 4549063) B4549063
theorem B4043611 : Blo 2129435 4043611 := bstep (se 1 (by rfl) ⟨3032708, by rfl⟩ : syracuseStep 4043611 = 6065417) B6065417
theorem B5391481 : Blo 2129435 5391481 := bstep (se 2 (by rfl) ⟨2021805, by rfl⟩ : syracuseStep 5391481 = 4043611) B4043611
theorem B7188641 : Blo 2129435 7188641 := bstep (se 2 (by rfl) ⟨2695740, by rfl⟩ : syracuseStep 7188641 = 5391481) B5391481
theorem B4792427 : Blo 2129435 4792427 := bstep (se 1 (by rfl) ⟨3594320, by rfl⟩ : syracuseStep 4792427 = 7188641) B7188641
theorem B3194951 : Blo 2129435 3194951 := bstep (se 1 (by rfl) ⟨2396213, by rfl⟩ : syracuseStep 3194951 = 4792427) B4792427
theorem B2129967 : Blo 2129435 2129967 := bstep (se 1 (by rfl) ⟨1597475, by rfl⟩ : syracuseStep 2129967 = 3194951) B3194951
theorem B3194957 : Blo 2129435 3194957 := bbase (se 3 (by rfl) ⟨599054, by rfl⟩ : syracuseStep 3194957 = 1198109) (by norm_num)
theorem B2129971 : Blo 2129435 2129971 := bstep (se 1 (by rfl) ⟨1597478, by rfl⟩ : syracuseStep 2129971 = 3194957) B3194957
theorem B4792445 : Blo 2129435 4792445 := bbase (se 3 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 4792445 = 1797167) (by norm_num)
theorem B3194963 : Blo 2129435 3194963 := bstep (se 1 (by rfl) ⟨2396222, by rfl⟩ : syracuseStep 3194963 = 4792445) B4792445
theorem B2129975 : Blo 2129435 2129975 := bstep (se 1 (by rfl) ⟨1597481, by rfl⟩ : syracuseStep 2129975 = 3194963) B3194963
theorem B3594341 : Blo 2129435 3594341 := bbase (se 4 (by rfl) ⟨336969, by rfl⟩ : syracuseStep 3594341 = 673939) (by norm_num)
theorem B2396227 : Blo 2129435 2396227 := bstep (se 1 (by rfl) ⟨1797170, by rfl⟩ : syracuseStep 2396227 = 3594341) B3594341
theorem B3194969 : Blo 2129435 3194969 := bstep (se 2 (by rfl) ⟨1198113, by rfl⟩ : syracuseStep 3194969 = 2396227) B2396227
theorem B2129979 : Blo 2129435 2129979 := bstep (se 1 (by rfl) ⟨1597484, by rfl⟩ : syracuseStep 2129979 = 3194969) B3194969
theorem B4377005 : Blo 2129435 4377005 := bbase (se 3 (by rfl) ⟨820688, by rfl⟩ : syracuseStep 4377005 = 1641377) (by norm_num)
theorem B2918003 : Blo 2129435 2918003 := bstep (se 1 (by rfl) ⟨2188502, by rfl⟩ : syracuseStep 2918003 = 4377005) B4377005
theorem B7781341 : Blo 2129435 7781341 := bstep (se 3 (by rfl) ⟨1459001, by rfl⟩ : syracuseStep 7781341 = 2918003) B2918003
theorem B10375121 : Blo 2129435 10375121 := bstep (se 2 (by rfl) ⟨3890670, by rfl⟩ : syracuseStep 10375121 = 7781341) B7781341
theorem B6916747 : Blo 2129435 6916747 := bstep (se 1 (by rfl) ⟨5187560, by rfl⟩ : syracuseStep 6916747 = 10375121) B10375121
theorem B9222329 : Blo 2129435 9222329 := bstep (se 2 (by rfl) ⟨3458373, by rfl⟩ : syracuseStep 9222329 = 6916747) B6916747
theorem B6148219 : Blo 2129435 6148219 := bstep (se 1 (by rfl) ⟨4611164, by rfl⟩ : syracuseStep 6148219 = 9222329) B9222329
theorem B8197625 : Blo 2129435 8197625 := bstep (se 2 (by rfl) ⟨3074109, by rfl⟩ : syracuseStep 8197625 = 6148219) B6148219
theorem B5465083 : Blo 2129435 5465083 := bstep (se 1 (by rfl) ⟨4098812, by rfl⟩ : syracuseStep 5465083 = 8197625) B8197625
theorem B7286777 : Blo 2129435 7286777 := bstep (se 2 (by rfl) ⟨2732541, by rfl⟩ : syracuseStep 7286777 = 5465083) B5465083
theorem B4857851 : Blo 2129435 4857851 := bstep (se 1 (by rfl) ⟨3643388, by rfl⟩ : syracuseStep 4857851 = 7286777) B7286777
theorem B12954269 : Blo 2129435 12954269 := bstep (se 3 (by rfl) ⟨2428925, by rfl⟩ : syracuseStep 12954269 = 4857851) B4857851
theorem B8636179 : Blo 2129435 8636179 := bstep (se 1 (by rfl) ⟨6477134, by rfl⟩ : syracuseStep 8636179 = 12954269) B12954269
theorem B11514905 : Blo 2129435 11514905 := bstep (se 2 (by rfl) ⟨4318089, by rfl⟩ : syracuseStep 11514905 = 8636179) B8636179
theorem B7676603 : Blo 2129435 7676603 := bstep (se 1 (by rfl) ⟨5757452, by rfl⟩ : syracuseStep 7676603 = 11514905) B11514905
theorem B5117735 : Blo 2129435 5117735 := bstep (se 1 (by rfl) ⟨3838301, by rfl⟩ : syracuseStep 5117735 = 7676603) B7676603
theorem B3411823 : Blo 2129435 3411823 := bstep (se 1 (by rfl) ⟨2558867, by rfl⟩ : syracuseStep 3411823 = 5117735) B5117735
theorem B4549097 : Blo 2129435 4549097 := bstep (se 2 (by rfl) ⟨1705911, by rfl⟩ : syracuseStep 4549097 = 3411823) B3411823
theorem B3032731 : Blo 2129435 3032731 := bstep (se 1 (by rfl) ⟨2274548, by rfl⟩ : syracuseStep 3032731 = 4549097) B4549097
theorem B16174565 : Blo 2129435 16174565 := bstep (se 4 (by rfl) ⟨1516365, by rfl⟩ : syracuseStep 16174565 = 3032731) B3032731
theorem B10783043 : Blo 2129435 10783043 := bstep (se 1 (by rfl) ⟨8087282, by rfl⟩ : syracuseStep 10783043 = 16174565) B16174565
theorem B7188695 : Blo 2129435 7188695 := bstep (se 1 (by rfl) ⟨5391521, by rfl⟩ : syracuseStep 7188695 = 10783043) B10783043
theorem B4792463 : Blo 2129435 4792463 := bstep (se 1 (by rfl) ⟨3594347, by rfl⟩ : syracuseStep 4792463 = 7188695) B7188695
theorem B3194975 : Blo 2129435 3194975 := bstep (se 1 (by rfl) ⟨2396231, by rfl⟩ : syracuseStep 3194975 = 4792463) B4792463
theorem B2129983 : Blo 2129435 2129983 := bstep (se 1 (by rfl) ⟨1597487, by rfl⟩ : syracuseStep 2129983 = 3194975) B3194975
theorem B3194981 : Blo 2129435 3194981 := bbase (se 4 (by rfl) ⟨299529, by rfl⟩ : syracuseStep 3194981 = 599059) (by norm_num)
theorem B2129987 : Blo 2129435 2129987 := bstep (se 1 (by rfl) ⟨1597490, by rfl⟩ : syracuseStep 2129987 = 3194981) B3194981
theorem B8636213 : Blo 2129435 8636213 := bbase (se 5 (by rfl) ⟨404822, by rfl⟩ : syracuseStep 8636213 = 809645) (by norm_num)
theorem B5757475 : Blo 2129435 5757475 := bstep (se 1 (by rfl) ⟨4318106, by rfl⟩ : syracuseStep 5757475 = 8636213) B8636213
theorem B7676633 : Blo 2129435 7676633 := bstep (se 2 (by rfl) ⟨2878737, by rfl⟩ : syracuseStep 7676633 = 5757475) B5757475
theorem B5117755 : Blo 2129435 5117755 := bstep (se 1 (by rfl) ⟨3838316, by rfl⟩ : syracuseStep 5117755 = 7676633) B7676633
theorem B6823673 : Blo 2129435 6823673 := bstep (se 2 (by rfl) ⟨2558877, by rfl⟩ : syracuseStep 6823673 = 5117755) B5117755
theorem B4549115 : Blo 2129435 4549115 := bstep (se 1 (by rfl) ⟨3411836, by rfl⟩ : syracuseStep 4549115 = 6823673) B6823673
theorem B3032743 : Blo 2129435 3032743 := bstep (se 1 (by rfl) ⟨2274557, by rfl⟩ : syracuseStep 3032743 = 4549115) B4549115
theorem B4043657 : Blo 2129435 4043657 := bstep (se 2 (by rfl) ⟨1516371, by rfl⟩ : syracuseStep 4043657 = 3032743) B3032743
theorem B2695771 : Blo 2129435 2695771 := bstep (se 1 (by rfl) ⟨2021828, by rfl⟩ : syracuseStep 2695771 = 4043657) B4043657
theorem B3594361 : Blo 2129435 3594361 := bstep (se 2 (by rfl) ⟨1347885, by rfl⟩ : syracuseStep 3594361 = 2695771) B2695771
theorem B4792481 : Blo 2129435 4792481 := bstep (se 2 (by rfl) ⟨1797180, by rfl⟩ : syracuseStep 4792481 = 3594361) B3594361
theorem B3194987 : Blo 2129435 3194987 := bstep (se 1 (by rfl) ⟨2396240, by rfl⟩ : syracuseStep 3194987 = 4792481) B4792481
theorem B2129991 : Blo 2129435 2129991 := bstep (se 1 (by rfl) ⟨1597493, by rfl⟩ : syracuseStep 2129991 = 3194987) B3194987
theorem B2396245 : Blo 2129435 2396245 := bbase (se 8 (by rfl) ⟨14040, by rfl⟩ : syracuseStep 2396245 = 28081) (by norm_num)
theorem B3194993 : Blo 2129435 3194993 := bstep (se 2 (by rfl) ⟨1198122, by rfl⟩ : syracuseStep 3194993 = 2396245) B2396245
theorem B2129995 : Blo 2129435 2129995 := bstep (se 1 (by rfl) ⟨1597496, by rfl⟩ : syracuseStep 2129995 = 3194993) B3194993
theorem B2695781 : Blo 2129435 2695781 := bbase (se 4 (by rfl) ⟨252729, by rfl⟩ : syracuseStep 2695781 = 505459) (by norm_num)
theorem B7188749 : Blo 2129435 7188749 := bstep (se 3 (by rfl) ⟨1347890, by rfl⟩ : syracuseStep 7188749 = 2695781) B2695781
theorem B4792499 : Blo 2129435 4792499 := bstep (se 1 (by rfl) ⟨3594374, by rfl⟩ : syracuseStep 4792499 = 7188749) B7188749
theorem B3194999 : Blo 2129435 3194999 := bstep (se 1 (by rfl) ⟨2396249, by rfl⟩ : syracuseStep 3194999 = 4792499) B4792499
theorem B2129999 : Blo 2129435 2129999 := bstep (se 1 (by rfl) ⟨1597499, by rfl⟩ : syracuseStep 2129999 = 3194999) B3194999
theorem B3195005 : Blo 2129435 3195005 := bbase (se 3 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 3195005 = 1198127) (by norm_num)
theorem B2130003 : Blo 2129435 2130003 := bstep (se 1 (by rfl) ⟨1597502, by rfl⟩ : syracuseStep 2130003 = 3195005) B3195005
theorem B4792517 : Blo 2129435 4792517 := bbase (se 4 (by rfl) ⟨449298, by rfl⟩ : syracuseStep 4792517 = 898597) (by norm_num)
theorem B3195011 : Blo 2129435 3195011 := bstep (se 1 (by rfl) ⟨2396258, by rfl⟩ : syracuseStep 3195011 = 4792517) B4792517
theorem B2130007 : Blo 2129435 2130007 := bstep (se 1 (by rfl) ⟨1597505, by rfl⟩ : syracuseStep 2130007 = 3195011) B3195011
theorem B10235605 : Blo 2129435 10235605 := bbase (se 7 (by rfl) ⟨119948, by rfl⟩ : syracuseStep 10235605 = 239897) (by norm_num)
theorem B13647473 : Blo 2129435 13647473 := bstep (se 2 (by rfl) ⟨5117802, by rfl⟩ : syracuseStep 13647473 = 10235605) B10235605
theorem B9098315 : Blo 2129435 9098315 := bstep (se 1 (by rfl) ⟨6823736, by rfl⟩ : syracuseStep 9098315 = 13647473) B13647473
theorem B6065543 : Blo 2129435 6065543 := bstep (se 1 (by rfl) ⟨4549157, by rfl⟩ : syracuseStep 6065543 = 9098315) B9098315
theorem B4043695 : Blo 2129435 4043695 := bstep (se 1 (by rfl) ⟨3032771, by rfl⟩ : syracuseStep 4043695 = 6065543) B6065543
theorem B5391593 : Blo 2129435 5391593 := bstep (se 2 (by rfl) ⟨2021847, by rfl⟩ : syracuseStep 5391593 = 4043695) B4043695
theorem B3594395 : Blo 2129435 3594395 := bstep (se 1 (by rfl) ⟨2695796, by rfl⟩ : syracuseStep 3594395 = 5391593) B5391593
theorem B2396263 : Blo 2129435 2396263 := bstep (se 1 (by rfl) ⟨1797197, by rfl⟩ : syracuseStep 2396263 = 3594395) B3594395
theorem B3195017 : Blo 2129435 3195017 := bstep (se 2 (by rfl) ⟨1198131, by rfl⟩ : syracuseStep 3195017 = 2396263) B2396263
theorem B2130011 : Blo 2129435 2130011 := bstep (se 1 (by rfl) ⟨1597508, by rfl⟩ : syracuseStep 2130011 = 3195017) B3195017
theorem B10783205 : Blo 2129435 10783205 := bbase (se 4 (by rfl) ⟨1010925, by rfl⟩ : syracuseStep 10783205 = 2021851) (by norm_num)
theorem B7188803 : Blo 2129435 7188803 := bstep (se 1 (by rfl) ⟨5391602, by rfl⟩ : syracuseStep 7188803 = 10783205) B10783205
theorem B4792535 : Blo 2129435 4792535 := bstep (se 1 (by rfl) ⟨3594401, by rfl⟩ : syracuseStep 4792535 = 7188803) B7188803
theorem B3195023 : Blo 2129435 3195023 := bstep (se 1 (by rfl) ⟨2396267, by rfl⟩ : syracuseStep 3195023 = 4792535) B4792535
theorem B2130015 : Blo 2129435 2130015 := bstep (se 1 (by rfl) ⟨1597511, by rfl⟩ : syracuseStep 2130015 = 3195023) B3195023
theorem B3195029 : Blo 2129435 3195029 := bbase (se 6 (by rfl) ⟨74883, by rfl⟩ : syracuseStep 3195029 = 149767) (by norm_num)
theorem B2130019 : Blo 2129435 2130019 := bstep (se 1 (by rfl) ⟨1597514, by rfl⟩ : syracuseStep 2130019 = 3195029) B3195029
theorem B8636341 : Blo 2129435 8636341 := bbase (se 5 (by rfl) ⟨404828, by rfl⟩ : syracuseStep 8636341 = 809657) (by norm_num)
theorem B11515121 : Blo 2129435 11515121 := bstep (se 2 (by rfl) ⟨4318170, by rfl⟩ : syracuseStep 11515121 = 8636341) B8636341
theorem B7676747 : Blo 2129435 7676747 := bstep (se 1 (by rfl) ⟨5757560, by rfl⟩ : syracuseStep 7676747 = 11515121) B11515121
theorem B5117831 : Blo 2129435 5117831 := bstep (se 1 (by rfl) ⟨3838373, by rfl⟩ : syracuseStep 5117831 = 7676747) B7676747
theorem B3411887 : Blo 2129435 3411887 := bstep (se 1 (by rfl) ⟨2558915, by rfl⟩ : syracuseStep 3411887 = 5117831) B5117831
theorem B9098365 : Blo 2129435 9098365 := bstep (se 3 (by rfl) ⟨1705943, by rfl⟩ : syracuseStep 9098365 = 3411887) B3411887
theorem B12131153 : Blo 2129435 12131153 := bstep (se 2 (by rfl) ⟨4549182, by rfl⟩ : syracuseStep 12131153 = 9098365) B9098365
theorem B8087435 : Blo 2129435 8087435 := bstep (se 1 (by rfl) ⟨6065576, by rfl⟩ : syracuseStep 8087435 = 12131153) B12131153
theorem B5391623 : Blo 2129435 5391623 := bstep (se 1 (by rfl) ⟨4043717, by rfl⟩ : syracuseStep 5391623 = 8087435) B8087435
theorem B3594415 : Blo 2129435 3594415 := bstep (se 1 (by rfl) ⟨2695811, by rfl⟩ : syracuseStep 3594415 = 5391623) B5391623
theorem B4792553 : Blo 2129435 4792553 := bstep (se 2 (by rfl) ⟨1797207, by rfl⟩ : syracuseStep 4792553 = 3594415) B3594415
theorem B3195035 : Blo 2129435 3195035 := bstep (se 1 (by rfl) ⟨2396276, by rfl⟩ : syracuseStep 3195035 = 4792553) B4792553
theorem B2130023 : Blo 2129435 2130023 := bstep (se 1 (by rfl) ⟨1597517, by rfl⟩ : syracuseStep 2130023 = 3195035) B3195035
theorem B2396281 : Blo 2129435 2396281 := bbase (se 2 (by rfl) ⟨898605, by rfl⟩ : syracuseStep 2396281 = 1797211) (by norm_num)
theorem B3195041 : Blo 2129435 3195041 := bstep (se 2 (by rfl) ⟨1198140, by rfl⟩ : syracuseStep 3195041 = 2396281) B2396281
theorem B2130027 : Blo 2129435 2130027 := bstep (se 1 (by rfl) ⟨1597520, by rfl⟩ : syracuseStep 2130027 = 3195041) B3195041
theorem B10375349 : Blo 2129435 10375349 := bbase (se 5 (by rfl) ⟨486344, by rfl⟩ : syracuseStep 10375349 = 972689) (by norm_num)
theorem B27667597 : Blo 2129435 27667597 := bstep (se 3 (by rfl) ⟨5187674, by rfl⟩ : syracuseStep 27667597 = 10375349) B10375349
theorem B36890129 : Blo 2129435 36890129 := bstep (se 2 (by rfl) ⟨13833798, by rfl⟩ : syracuseStep 36890129 = 27667597) B27667597
theorem B24593419 : Blo 2129435 24593419 := bstep (se 1 (by rfl) ⟨18445064, by rfl⟩ : syracuseStep 24593419 = 36890129) B36890129
theorem B32791225 : Blo 2129435 32791225 := bstep (se 2 (by rfl) ⟨12296709, by rfl⟩ : syracuseStep 32791225 = 24593419) B24593419
theorem B43721633 : Blo 2129435 43721633 := bstep (se 2 (by rfl) ⟨16395612, by rfl⟩ : syracuseStep 43721633 = 32791225) B32791225
theorem B116591021 : Blo 2129435 116591021 := bstep (se 3 (by rfl) ⟨21860816, by rfl⟩ : syracuseStep 116591021 = 43721633) B43721633
theorem B77727347 : Blo 2129435 77727347 := bstep (se 1 (by rfl) ⟨58295510, by rfl⟩ : syracuseStep 77727347 = 116591021) B116591021
theorem B51818231 : Blo 2129435 51818231 := bstep (se 1 (by rfl) ⟨38863673, by rfl⟩ : syracuseStep 51818231 = 77727347) B77727347
theorem B34545487 : Blo 2129435 34545487 := bstep (se 1 (by rfl) ⟨25909115, by rfl⟩ : syracuseStep 34545487 = 51818231) B51818231
theorem B46060649 : Blo 2129435 46060649 := bstep (se 2 (by rfl) ⟨17272743, by rfl⟩ : syracuseStep 46060649 = 34545487) B34545487
theorem B30707099 : Blo 2129435 30707099 := bstep (se 1 (by rfl) ⟨23030324, by rfl⟩ : syracuseStep 30707099 = 46060649) B46060649
theorem B20471399 : Blo 2129435 20471399 := bstep (se 1 (by rfl) ⟨15353549, by rfl⟩ : syracuseStep 20471399 = 30707099) B30707099
theorem B13647599 : Blo 2129435 13647599 := bstep (se 1 (by rfl) ⟨10235699, by rfl⟩ : syracuseStep 13647599 = 20471399) B20471399
theorem B9098399 : Blo 2129435 9098399 := bstep (se 1 (by rfl) ⟨6823799, by rfl⟩ : syracuseStep 9098399 = 13647599) B13647599
theorem B6065599 : Blo 2129435 6065599 := bstep (se 1 (by rfl) ⟨4549199, by rfl⟩ : syracuseStep 6065599 = 9098399) B9098399
theorem B8087465 : Blo 2129435 8087465 := bstep (se 2 (by rfl) ⟨3032799, by rfl⟩ : syracuseStep 8087465 = 6065599) B6065599
theorem B5391643 : Blo 2129435 5391643 := bstep (se 1 (by rfl) ⟨4043732, by rfl⟩ : syracuseStep 5391643 = 8087465) B8087465
theorem B7188857 : Blo 2129435 7188857 := bstep (se 2 (by rfl) ⟨2695821, by rfl⟩ : syracuseStep 7188857 = 5391643) B5391643
theorem B4792571 : Blo 2129435 4792571 := bstep (se 1 (by rfl) ⟨3594428, by rfl⟩ : syracuseStep 4792571 = 7188857) B7188857
theorem B3195047 : Blo 2129435 3195047 := bstep (se 1 (by rfl) ⟨2396285, by rfl⟩ : syracuseStep 3195047 = 4792571) B4792571
theorem B2130031 : Blo 2129435 2130031 := bstep (se 1 (by rfl) ⟨1597523, by rfl⟩ : syracuseStep 2130031 = 3195047) B3195047
theorem B3195053 : Blo 2129435 3195053 := bbase (se 3 (by rfl) ⟨599072, by rfl⟩ : syracuseStep 3195053 = 1198145) (by norm_num)
theorem B2130035 : Blo 2129435 2130035 := bstep (se 1 (by rfl) ⟨1597526, by rfl⟩ : syracuseStep 2130035 = 3195053) B3195053
theorem B4792589 : Blo 2129435 4792589 := bbase (se 3 (by rfl) ⟨898610, by rfl⟩ : syracuseStep 4792589 = 1797221) (by norm_num)
theorem B3195059 : Blo 2129435 3195059 := bstep (se 1 (by rfl) ⟨2396294, by rfl⟩ : syracuseStep 3195059 = 4792589) B4792589
theorem B2130039 : Blo 2129435 2130039 := bstep (se 1 (by rfl) ⟨1597529, by rfl⟩ : syracuseStep 2130039 = 3195059) B3195059
theorem B2695837 : Blo 2129435 2695837 := bbase (se 3 (by rfl) ⟨505469, by rfl⟩ : syracuseStep 2695837 = 1010939) (by norm_num)
theorem B3594449 : Blo 2129435 3594449 := bstep (se 2 (by rfl) ⟨1347918, by rfl⟩ : syracuseStep 3594449 = 2695837) B2695837
theorem B2396299 : Blo 2129435 2396299 := bstep (se 1 (by rfl) ⟨1797224, by rfl⟩ : syracuseStep 2396299 = 3594449) B3594449
theorem B3195065 : Blo 2129435 3195065 := bstep (se 2 (by rfl) ⟨1198149, by rfl⟩ : syracuseStep 3195065 = 2396299) B2396299
theorem B2130043 : Blo 2129435 2130043 := bstep (se 1 (by rfl) ⟨1597532, by rfl⟩ : syracuseStep 2130043 = 3195065) B3195065
theorem B3411925 : Blo 2129435 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B18196933 : Blo 2129435 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B24262577 : Blo 2129435 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B16175051 : Blo 2129435 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B10783367 : Blo 2129435 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B7188911 : Blo 2129435 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B4792607 : Blo 2129435 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B3195071 : Blo 2129435 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B2130047 : Blo 2129435 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B3195077 : Blo 2129435 3195077 := bbase (se 4 (by rfl) ⟨299538, by rfl⟩ : syracuseStep 3195077 = 599077) (by norm_num)
theorem B2130051 : Blo 2129435 2130051 := bstep (se 1 (by rfl) ⟨1597538, by rfl⟩ : syracuseStep 2130051 = 3195077) B3195077
theorem B3594469 : Blo 2129435 3594469 := bbase (se 4 (by rfl) ⟨336981, by rfl⟩ : syracuseStep 3594469 = 673963) (by norm_num)
theorem B4792625 : Blo 2129435 4792625 := bstep (se 2 (by rfl) ⟨1797234, by rfl⟩ : syracuseStep 4792625 = 3594469) B3594469
theorem B3195083 : Blo 2129435 3195083 := bstep (se 1 (by rfl) ⟨2396312, by rfl⟩ : syracuseStep 3195083 = 4792625) B4792625
theorem B2130055 : Blo 2129435 2130055 := bstep (se 1 (by rfl) ⟨1597541, by rfl⟩ : syracuseStep 2130055 = 3195083) B3195083
theorem B2396317 : Blo 2129435 2396317 := bbase (se 3 (by rfl) ⟨449309, by rfl⟩ : syracuseStep 2396317 = 898619) (by norm_num)
theorem B3195089 : Blo 2129435 3195089 := bstep (se 2 (by rfl) ⟨1198158, by rfl⟩ : syracuseStep 3195089 = 2396317) B2396317
theorem B2130059 : Blo 2129435 2130059 := bstep (se 1 (by rfl) ⟨1597544, by rfl⟩ : syracuseStep 2130059 = 3195089) B3195089
theorem B7188965 : Blo 2129435 7188965 := bbase (se 4 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 7188965 = 1347931) (by norm_num)
theorem B4792643 : Blo 2129435 4792643 := bstep (se 1 (by rfl) ⟨3594482, by rfl⟩ : syracuseStep 4792643 = 7188965) B7188965
theorem B3195095 : Blo 2129435 3195095 := bstep (se 1 (by rfl) ⟨2396321, by rfl⟩ : syracuseStep 3195095 = 4792643) B4792643
theorem B2130063 : Blo 2129435 2130063 := bstep (se 1 (by rfl) ⟨1597547, by rfl⟩ : syracuseStep 2130063 = 3195095) B3195095
theorem B3195101 : Blo 2129435 3195101 := bbase (se 3 (by rfl) ⟨599081, by rfl⟩ : syracuseStep 3195101 = 1198163) (by norm_num)
theorem B2130067 : Blo 2129435 2130067 := bstep (se 1 (by rfl) ⟨1597550, by rfl⟩ : syracuseStep 2130067 = 3195101) B3195101
theorem B4792661 : Blo 2129435 4792661 := bbase (se 10 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 4792661 = 14041) (by norm_num)
theorem B3195107 : Blo 2129435 3195107 := bstep (se 1 (by rfl) ⟨2396330, by rfl⟩ : syracuseStep 3195107 = 4792661) B4792661
theorem B2130071 : Blo 2129435 2130071 := bstep (se 1 (by rfl) ⟨1597553, by rfl⟩ : syracuseStep 2130071 = 3195107) B3195107
theorem B5117957 : Blo 2129435 5117957 := bbase (se 4 (by rfl) ⟨479808, by rfl⟩ : syracuseStep 5117957 = 959617) (by norm_num)
theorem B3411971 : Blo 2129435 3411971 := bstep (se 1 (by rfl) ⟨2558978, by rfl⟩ : syracuseStep 3411971 = 5117957) B5117957
theorem B2274647 : Blo 2129435 2274647 := bstep (se 1 (by rfl) ⟨1705985, by rfl⟩ : syracuseStep 2274647 = 3411971) B3411971
theorem B6065725 : Blo 2129435 6065725 := bstep (se 3 (by rfl) ⟨1137323, by rfl⟩ : syracuseStep 6065725 = 2274647) B2274647
theorem B8087633 : Blo 2129435 8087633 := bstep (se 2 (by rfl) ⟨3032862, by rfl⟩ : syracuseStep 8087633 = 6065725) B6065725
theorem B5391755 : Blo 2129435 5391755 := bstep (se 1 (by rfl) ⟨4043816, by rfl⟩ : syracuseStep 5391755 = 8087633) B8087633
theorem B3594503 : Blo 2129435 3594503 := bstep (se 1 (by rfl) ⟨2695877, by rfl⟩ : syracuseStep 3594503 = 5391755) B5391755
theorem B2396335 : Blo 2129435 2396335 := bstep (se 1 (by rfl) ⟨1797251, by rfl⟩ : syracuseStep 2396335 = 3594503) B3594503
theorem B3195113 : Blo 2129435 3195113 := bstep (se 2 (by rfl) ⟨1198167, by rfl⟩ : syracuseStep 3195113 = 2396335) B2396335
theorem B2130075 : Blo 2129435 2130075 := bstep (se 1 (by rfl) ⟨1597556, by rfl⟩ : syracuseStep 2130075 = 3195113) B3195113
theorem B4858069 : Blo 2129435 4858069 := bbase (se 7 (by rfl) ⟨56930, by rfl⟩ : syracuseStep 4858069 = 113861) (by norm_num)
theorem B6477425 : Blo 2129435 6477425 := bstep (se 2 (by rfl) ⟨2429034, by rfl⟩ : syracuseStep 6477425 = 4858069) B4858069
theorem B4318283 : Blo 2129435 4318283 := bstep (se 1 (by rfl) ⟨3238712, by rfl⟩ : syracuseStep 4318283 = 6477425) B6477425
theorem B11515421 : Blo 2129435 11515421 := bstep (se 3 (by rfl) ⟨2159141, by rfl⟩ : syracuseStep 11515421 = 4318283) B4318283
theorem B7676947 : Blo 2129435 7676947 := bstep (se 1 (by rfl) ⟨5757710, by rfl⟩ : syracuseStep 7676947 = 11515421) B11515421
theorem B40943717 : Blo 2129435 40943717 := bstep (se 4 (by rfl) ⟨3838473, by rfl⟩ : syracuseStep 40943717 = 7676947) B7676947
theorem B27295811 : Blo 2129435 27295811 := bstep (se 1 (by rfl) ⟨20471858, by rfl⟩ : syracuseStep 27295811 = 40943717) B40943717
theorem B18197207 : Blo 2129435 18197207 := bstep (se 1 (by rfl) ⟨13647905, by rfl⟩ : syracuseStep 18197207 = 27295811) B27295811
theorem B12131471 : Blo 2129435 12131471 := bstep (se 1 (by rfl) ⟨9098603, by rfl⟩ : syracuseStep 12131471 = 18197207) B18197207
theorem B8087647 : Blo 2129435 8087647 := bstep (se 1 (by rfl) ⟨6065735, by rfl⟩ : syracuseStep 8087647 = 12131471) B12131471
theorem B10783529 : Blo 2129435 10783529 := bstep (se 2 (by rfl) ⟨4043823, by rfl⟩ : syracuseStep 10783529 = 8087647) B8087647
theorem B7189019 : Blo 2129435 7189019 := bstep (se 1 (by rfl) ⟨5391764, by rfl⟩ : syracuseStep 7189019 = 10783529) B10783529
theorem B4792679 : Blo 2129435 4792679 := bstep (se 1 (by rfl) ⟨3594509, by rfl⟩ : syracuseStep 4792679 = 7189019) B7189019
theorem B3195119 : Blo 2129435 3195119 := bstep (se 1 (by rfl) ⟨2396339, by rfl⟩ : syracuseStep 3195119 = 4792679) B4792679
theorem B2130079 : Blo 2129435 2130079 := bstep (se 1 (by rfl) ⟨1597559, by rfl⟩ : syracuseStep 2130079 = 3195119) B3195119
theorem B3195125 : Blo 2129435 3195125 := bbase (se 5 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 3195125 = 299543) (by norm_num)
theorem B2130083 : Blo 2129435 2130083 := bstep (se 1 (by rfl) ⟨1597562, by rfl⟩ : syracuseStep 2130083 = 3195125) B3195125
theorem B5757733 : Blo 2129435 5757733 := bbase (se 4 (by rfl) ⟨539787, by rfl⟩ : syracuseStep 5757733 = 1079575) (by norm_num)
theorem B30707909 : Blo 2129435 30707909 := bstep (se 4 (by rfl) ⟨2878866, by rfl⟩ : syracuseStep 30707909 = 5757733) B5757733
theorem B20471939 : Blo 2129435 20471939 := bstep (se 1 (by rfl) ⟨15353954, by rfl⟩ : syracuseStep 20471939 = 30707909) B30707909
theorem B13647959 : Blo 2129435 13647959 := bstep (se 1 (by rfl) ⟨10235969, by rfl⟩ : syracuseStep 13647959 = 20471939) B20471939
theorem B9098639 : Blo 2129435 9098639 := bstep (se 1 (by rfl) ⟨6823979, by rfl⟩ : syracuseStep 9098639 = 13647959) B13647959
theorem B6065759 : Blo 2129435 6065759 := bstep (se 1 (by rfl) ⟨4549319, by rfl⟩ : syracuseStep 6065759 = 9098639) B9098639
theorem B4043839 : Blo 2129435 4043839 := bstep (se 1 (by rfl) ⟨3032879, by rfl⟩ : syracuseStep 4043839 = 6065759) B6065759
theorem B5391785 : Blo 2129435 5391785 := bstep (se 2 (by rfl) ⟨2021919, by rfl⟩ : syracuseStep 5391785 = 4043839) B4043839
theorem B3594523 : Blo 2129435 3594523 := bstep (se 1 (by rfl) ⟨2695892, by rfl⟩ : syracuseStep 3594523 = 5391785) B5391785
theorem B4792697 : Blo 2129435 4792697 := bstep (se 2 (by rfl) ⟨1797261, by rfl⟩ : syracuseStep 4792697 = 3594523) B3594523
theorem B3195131 : Blo 2129435 3195131 := bstep (se 1 (by rfl) ⟨2396348, by rfl⟩ : syracuseStep 3195131 = 4792697) B4792697
theorem B2130087 : Blo 2129435 2130087 := bstep (se 1 (by rfl) ⟨1597565, by rfl⟩ : syracuseStep 2130087 = 3195131) B3195131
theorem B2396353 : Blo 2129435 2396353 := bbase (se 2 (by rfl) ⟨898632, by rfl⟩ : syracuseStep 2396353 = 1797265) (by norm_num)
theorem B3195137 : Blo 2129435 3195137 := bstep (se 2 (by rfl) ⟨1198176, by rfl⟩ : syracuseStep 3195137 = 2396353) B2396353
theorem B2130091 : Blo 2129435 2130091 := bstep (se 1 (by rfl) ⟨1597568, by rfl⟩ : syracuseStep 2130091 = 3195137) B3195137
theorem B5391805 : Blo 2129435 5391805 := bbase (se 3 (by rfl) ⟨1010963, by rfl⟩ : syracuseStep 5391805 = 2021927) (by norm_num)
theorem B7189073 : Blo 2129435 7189073 := bstep (se 2 (by rfl) ⟨2695902, by rfl⟩ : syracuseStep 7189073 = 5391805) B5391805
theorem B4792715 : Blo 2129435 4792715 := bstep (se 1 (by rfl) ⟨3594536, by rfl⟩ : syracuseStep 4792715 = 7189073) B7189073
theorem B3195143 : Blo 2129435 3195143 := bstep (se 1 (by rfl) ⟨2396357, by rfl⟩ : syracuseStep 3195143 = 4792715) B4792715
theorem B2130095 : Blo 2129435 2130095 := bstep (se 1 (by rfl) ⟨1597571, by rfl⟩ : syracuseStep 2130095 = 3195143) B3195143
theorem B3195149 : Blo 2129435 3195149 := bbase (se 3 (by rfl) ⟨599090, by rfl⟩ : syracuseStep 3195149 = 1198181) (by norm_num)
theorem B2130099 : Blo 2129435 2130099 := bstep (se 1 (by rfl) ⟨1597574, by rfl⟩ : syracuseStep 2130099 = 3195149) B3195149
theorem B4792733 : Blo 2129435 4792733 := bbase (se 3 (by rfl) ⟨898637, by rfl⟩ : syracuseStep 4792733 = 1797275) (by norm_num)
theorem B3195155 : Blo 2129435 3195155 := bstep (se 1 (by rfl) ⟨2396366, by rfl⟩ : syracuseStep 3195155 = 4792733) B4792733
theorem B2130103 : Blo 2129435 2130103 := bstep (se 1 (by rfl) ⟨1597577, by rfl⟩ : syracuseStep 2130103 = 3195155) B3195155
theorem B3594557 : Blo 2129435 3594557 := bbase (se 3 (by rfl) ⟨673979, by rfl⟩ : syracuseStep 3594557 = 1347959) (by norm_num)
theorem B2396371 : Blo 2129435 2396371 := bstep (se 1 (by rfl) ⟨1797278, by rfl⟩ : syracuseStep 2396371 = 3594557) B3594557
theorem B3195161 : Blo 2129435 3195161 := bstep (se 2 (by rfl) ⟨1198185, by rfl⟩ : syracuseStep 3195161 = 2396371) B2396371
theorem B2130107 : Blo 2129435 2130107 := bstep (se 1 (by rfl) ⟨1597580, by rfl⟩ : syracuseStep 2130107 = 3195161) B3195161
theorem B2274685 : Blo 2129435 2274685 := bbase (se 3 (by rfl) ⟨426503, by rfl⟩ : syracuseStep 2274685 = 853007) (by norm_num)
theorem B12131653 : Blo 2129435 12131653 := bstep (se 4 (by rfl) ⟨1137342, by rfl⟩ : syracuseStep 12131653 = 2274685) B2274685
theorem B16175537 : Blo 2129435 16175537 := bstep (se 2 (by rfl) ⟨6065826, by rfl⟩ : syracuseStep 16175537 = 12131653) B12131653
theorem B10783691 : Blo 2129435 10783691 := bstep (se 1 (by rfl) ⟨8087768, by rfl⟩ : syracuseStep 10783691 = 16175537) B16175537
theorem B7189127 : Blo 2129435 7189127 := bstep (se 1 (by rfl) ⟨5391845, by rfl⟩ : syracuseStep 7189127 = 10783691) B10783691
theorem B4792751 : Blo 2129435 4792751 := bstep (se 1 (by rfl) ⟨3594563, by rfl⟩ : syracuseStep 4792751 = 7189127) B7189127
theorem B3195167 : Blo 2129435 3195167 := bstep (se 1 (by rfl) ⟨2396375, by rfl⟩ : syracuseStep 3195167 = 4792751) B4792751
theorem B2130111 : Blo 2129435 2130111 := bstep (se 1 (by rfl) ⟨1597583, by rfl⟩ : syracuseStep 2130111 = 3195167) B3195167
theorem B3195173 : Blo 2129435 3195173 := bbase (se 4 (by rfl) ⟨299547, by rfl⟩ : syracuseStep 3195173 = 599095) (by norm_num)
theorem B2130115 : Blo 2129435 2130115 := bstep (se 1 (by rfl) ⟨1597586, by rfl⟩ : syracuseStep 2130115 = 3195173) B3195173
theorem B2695933 : Blo 2129435 2695933 := bbase (se 3 (by rfl) ⟨505487, by rfl⟩ : syracuseStep 2695933 = 1010975) (by norm_num)
theorem B3594577 : Blo 2129435 3594577 := bstep (se 2 (by rfl) ⟨1347966, by rfl⟩ : syracuseStep 3594577 = 2695933) B2695933
theorem B4792769 : Blo 2129435 4792769 := bstep (se 2 (by rfl) ⟨1797288, by rfl⟩ : syracuseStep 4792769 = 3594577) B3594577
theorem B3195179 : Blo 2129435 3195179 := bstep (se 1 (by rfl) ⟨2396384, by rfl⟩ : syracuseStep 3195179 = 4792769) B4792769
theorem B2130119 : Blo 2129435 2130119 := bstep (se 1 (by rfl) ⟨1597589, by rfl⟩ : syracuseStep 2130119 = 3195179) B3195179
theorem B2396389 : Blo 2129435 2396389 := bbase (se 4 (by rfl) ⟨224661, by rfl⟩ : syracuseStep 2396389 = 449323) (by norm_num)
theorem B3195185 : Blo 2129435 3195185 := bstep (se 2 (by rfl) ⟨1198194, by rfl⟩ : syracuseStep 3195185 = 2396389) B2396389
theorem B2130123 : Blo 2129435 2130123 := bstep (se 1 (by rfl) ⟨1597592, by rfl⟩ : syracuseStep 2130123 = 3195185) B3195185
theorem B4549405 : Blo 2129435 4549405 := bbase (se 3 (by rfl) ⟨853013, by rfl⟩ : syracuseStep 4549405 = 1706027) (by norm_num)
theorem B6065873 : Blo 2129435 6065873 := bstep (se 2 (by rfl) ⟨2274702, by rfl⟩ : syracuseStep 6065873 = 4549405) B4549405
theorem B4043915 : Blo 2129435 4043915 := bstep (se 1 (by rfl) ⟨3032936, by rfl⟩ : syracuseStep 4043915 = 6065873) B6065873
theorem B2695943 : Blo 2129435 2695943 := bstep (se 1 (by rfl) ⟨2021957, by rfl⟩ : syracuseStep 2695943 = 4043915) B4043915
theorem B7189181 : Blo 2129435 7189181 := bstep (se 3 (by rfl) ⟨1347971, by rfl⟩ : syracuseStep 7189181 = 2695943) B2695943
theorem B4792787 : Blo 2129435 4792787 := bstep (se 1 (by rfl) ⟨3594590, by rfl⟩ : syracuseStep 4792787 = 7189181) B7189181
theorem B3195191 : Blo 2129435 3195191 := bstep (se 1 (by rfl) ⟨2396393, by rfl⟩ : syracuseStep 3195191 = 4792787) B4792787
theorem B2130127 : Blo 2129435 2130127 := bstep (se 1 (by rfl) ⟨1597595, by rfl⟩ : syracuseStep 2130127 = 3195191) B3195191
theorem B3195197 : Blo 2129435 3195197 := bbase (se 3 (by rfl) ⟨599099, by rfl⟩ : syracuseStep 3195197 = 1198199) (by norm_num)
theorem B2130131 : Blo 2129435 2130131 := bstep (se 1 (by rfl) ⟨1597598, by rfl⟩ : syracuseStep 2130131 = 3195197) B3195197
theorem B4792805 : Blo 2129435 4792805 := bbase (se 4 (by rfl) ⟨449325, by rfl⟩ : syracuseStep 4792805 = 898651) (by norm_num)
theorem B3195203 : Blo 2129435 3195203 := bstep (se 1 (by rfl) ⟨2396402, by rfl⟩ : syracuseStep 3195203 = 4792805) B4792805
theorem B2130135 : Blo 2129435 2130135 := bstep (se 1 (by rfl) ⟨1597601, by rfl⟩ : syracuseStep 2130135 = 3195203) B3195203
theorem B5391917 : Blo 2129435 5391917 := bbase (se 3 (by rfl) ⟨1010984, by rfl⟩ : syracuseStep 5391917 = 2021969) (by norm_num)
theorem B3594611 : Blo 2129435 3594611 := bstep (se 1 (by rfl) ⟨2695958, by rfl⟩ : syracuseStep 3594611 = 5391917) B5391917
theorem B2396407 : Blo 2129435 2396407 := bstep (se 1 (by rfl) ⟨1797305, by rfl⟩ : syracuseStep 2396407 = 3594611) B3594611
theorem B3195209 : Blo 2129435 3195209 := bstep (se 2 (by rfl) ⟨1198203, by rfl⟩ : syracuseStep 3195209 = 2396407) B2396407
theorem B2130139 : Blo 2129435 2130139 := bstep (se 1 (by rfl) ⟨1597604, by rfl⟩ : syracuseStep 2130139 = 3195209) B3195209
theorem B11672885 : Blo 2129435 11672885 := bbase (se 5 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 11672885 = 1094333) (by norm_num)
theorem B7781923 : Blo 2129435 7781923 := bstep (se 1 (by rfl) ⟨5836442, by rfl⟩ : syracuseStep 7781923 = 11672885) B11672885
theorem B41503589 : Blo 2129435 41503589 := bstep (se 4 (by rfl) ⟨3890961, by rfl⟩ : syracuseStep 41503589 = 7781923) B7781923
theorem B27669059 : Blo 2129435 27669059 := bstep (se 1 (by rfl) ⟨20751794, by rfl⟩ : syracuseStep 27669059 = 41503589) B41503589
theorem B18446039 : Blo 2129435 18446039 := bstep (se 1 (by rfl) ⟨13834529, by rfl⟩ : syracuseStep 18446039 = 27669059) B27669059
theorem B12297359 : Blo 2129435 12297359 := bstep (se 1 (by rfl) ⟨9223019, by rfl⟩ : syracuseStep 12297359 = 18446039) B18446039
theorem B32792957 : Blo 2129435 32792957 := bstep (se 3 (by rfl) ⟨6148679, by rfl⟩ : syracuseStep 32792957 = 12297359) B12297359
theorem B21861971 : Blo 2129435 21861971 := bstep (se 1 (by rfl) ⟨16396478, by rfl⟩ : syracuseStep 21861971 = 32792957) B32792957
theorem B14574647 : Blo 2129435 14574647 := bstep (se 1 (by rfl) ⟨10930985, by rfl⟩ : syracuseStep 14574647 = 21861971) B21861971
theorem B9716431 : Blo 2129435 9716431 := bstep (se 1 (by rfl) ⟨7287323, by rfl⟩ : syracuseStep 9716431 = 14574647) B14574647
theorem B12955241 : Blo 2129435 12955241 := bstep (se 2 (by rfl) ⟨4858215, by rfl⟩ : syracuseStep 12955241 = 9716431) B9716431
theorem B34547309 : Blo 2129435 34547309 := bstep (se 3 (by rfl) ⟨6477620, by rfl⟩ : syracuseStep 34547309 = 12955241) B12955241
theorem B23031539 : Blo 2129435 23031539 := bstep (se 1 (by rfl) ⟨17273654, by rfl⟩ : syracuseStep 23031539 = 34547309) B34547309
theorem B15354359 : Blo 2129435 15354359 := bstep (se 1 (by rfl) ⟨11515769, by rfl⟩ : syracuseStep 15354359 = 23031539) B23031539
theorem B10236239 : Blo 2129435 10236239 := bstep (se 1 (by rfl) ⟨7677179, by rfl⟩ : syracuseStep 10236239 = 15354359) B15354359
theorem B6824159 : Blo 2129435 6824159 := bstep (se 1 (by rfl) ⟨5118119, by rfl⟩ : syracuseStep 6824159 = 10236239) B10236239
theorem B4549439 : Blo 2129435 4549439 := bstep (se 1 (by rfl) ⟨3412079, by rfl⟩ : syracuseStep 4549439 = 6824159) B6824159
theorem B3032959 : Blo 2129435 3032959 := bstep (se 1 (by rfl) ⟨2274719, by rfl⟩ : syracuseStep 3032959 = 4549439) B4549439
theorem B4043945 : Blo 2129435 4043945 := bstep (se 2 (by rfl) ⟨1516479, by rfl⟩ : syracuseStep 4043945 = 3032959) B3032959
theorem B10783853 : Blo 2129435 10783853 := bstep (se 3 (by rfl) ⟨2021972, by rfl⟩ : syracuseStep 10783853 = 4043945) B4043945
theorem B7189235 : Blo 2129435 7189235 := bstep (se 1 (by rfl) ⟨5391926, by rfl⟩ : syracuseStep 7189235 = 10783853) B10783853
theorem B4792823 : Blo 2129435 4792823 := bstep (se 1 (by rfl) ⟨3594617, by rfl⟩ : syracuseStep 4792823 = 7189235) B7189235
theorem B3195215 : Blo 2129435 3195215 := bstep (se 1 (by rfl) ⟨2396411, by rfl⟩ : syracuseStep 3195215 = 4792823) B4792823
theorem B2130143 : Blo 2129435 2130143 := bstep (se 1 (by rfl) ⟨1597607, by rfl⟩ : syracuseStep 2130143 = 3195215) B3195215
theorem B3195221 : Blo 2129435 3195221 := bbase (se 10 (by rfl) ⟨4680, by rfl⟩ : syracuseStep 3195221 = 9361) (by norm_num)
theorem B2130147 : Blo 2129435 2130147 := bstep (se 1 (by rfl) ⟨1597610, by rfl⟩ : syracuseStep 2130147 = 3195221) B3195221
theorem B6065941 : Blo 2129435 6065941 := bbase (se 6 (by rfl) ⟨142170, by rfl⟩ : syracuseStep 6065941 = 284341) (by norm_num)
theorem B8087921 : Blo 2129435 8087921 := bstep (se 2 (by rfl) ⟨3032970, by rfl⟩ : syracuseStep 8087921 = 6065941) B6065941
theorem B5391947 : Blo 2129435 5391947 := bstep (se 1 (by rfl) ⟨4043960, by rfl⟩ : syracuseStep 5391947 = 8087921) B8087921
theorem B3594631 : Blo 2129435 3594631 := bstep (se 1 (by rfl) ⟨2695973, by rfl⟩ : syracuseStep 3594631 = 5391947) B5391947
theorem B4792841 : Blo 2129435 4792841 := bstep (se 2 (by rfl) ⟨1797315, by rfl⟩ : syracuseStep 4792841 = 3594631) B3594631
theorem B3195227 : Blo 2129435 3195227 := bstep (se 1 (by rfl) ⟨2396420, by rfl⟩ : syracuseStep 3195227 = 4792841) B4792841
theorem B2130151 : Blo 2129435 2130151 := bstep (se 1 (by rfl) ⟨1597613, by rfl⟩ : syracuseStep 2130151 = 3195227) B3195227
theorem B2396425 : Blo 2129435 2396425 := bbase (se 2 (by rfl) ⟨898659, by rfl⟩ : syracuseStep 2396425 = 1797319) (by norm_num)
theorem B3195233 : Blo 2129435 3195233 := bstep (se 2 (by rfl) ⟨1198212, by rfl⟩ : syracuseStep 3195233 = 2396425) B2396425
theorem B2130155 : Blo 2129435 2130155 := bstep (se 1 (by rfl) ⟨1597616, by rfl⟩ : syracuseStep 2130155 = 3195233) B3195233
theorem B5118157 : Blo 2129435 5118157 := bbase (se 3 (by rfl) ⟨959654, by rfl⟩ : syracuseStep 5118157 = 1919309) (by norm_num)
theorem B27296837 : Blo 2129435 27296837 := bstep (se 4 (by rfl) ⟨2559078, by rfl⟩ : syracuseStep 27296837 = 5118157) B5118157
theorem B18197891 : Blo 2129435 18197891 := bstep (se 1 (by rfl) ⟨13648418, by rfl⟩ : syracuseStep 18197891 = 27296837) B27296837
theorem B12131927 : Blo 2129435 12131927 := bstep (se 1 (by rfl) ⟨9098945, by rfl⟩ : syracuseStep 12131927 = 18197891) B18197891
theorem B8087951 : Blo 2129435 8087951 := bstep (se 1 (by rfl) ⟨6065963, by rfl⟩ : syracuseStep 8087951 = 12131927) B12131927
theorem B5391967 : Blo 2129435 5391967 := bstep (se 1 (by rfl) ⟨4043975, by rfl⟩ : syracuseStep 5391967 = 8087951) B8087951
theorem B7189289 : Blo 2129435 7189289 := bstep (se 2 (by rfl) ⟨2695983, by rfl⟩ : syracuseStep 7189289 = 5391967) B5391967
theorem B4792859 : Blo 2129435 4792859 := bstep (se 1 (by rfl) ⟨3594644, by rfl⟩ : syracuseStep 4792859 = 7189289) B7189289
theorem B3195239 : Blo 2129435 3195239 := bstep (se 1 (by rfl) ⟨2396429, by rfl⟩ : syracuseStep 3195239 = 4792859) B4792859
theorem B2130159 : Blo 2129435 2130159 := bstep (se 1 (by rfl) ⟨1597619, by rfl⟩ : syracuseStep 2130159 = 3195239) B3195239
theorem B3195245 : Blo 2129435 3195245 := bbase (se 3 (by rfl) ⟨599108, by rfl⟩ : syracuseStep 3195245 = 1198217) (by norm_num)
theorem B2130163 : Blo 2129435 2130163 := bstep (se 1 (by rfl) ⟨1597622, by rfl⟩ : syracuseStep 2130163 = 3195245) B3195245
theorem B4792877 : Blo 2129435 4792877 := bbase (se 3 (by rfl) ⟨898664, by rfl⟩ : syracuseStep 4792877 = 1797329) (by norm_num)
theorem B3195251 : Blo 2129435 3195251 := bstep (se 1 (by rfl) ⟨2396438, by rfl⟩ : syracuseStep 3195251 = 4792877) B4792877
theorem B2130167 : Blo 2129435 2130167 := bstep (se 1 (by rfl) ⟨1597625, by rfl⟩ : syracuseStep 2130167 = 3195251) B3195251
theorem B4497653 : Blo 2129435 4497653 := bbase (se 5 (by rfl) ⟨210827, by rfl⟩ : syracuseStep 4497653 = 421655) (by norm_num)
theorem B11993741 : Blo 2129435 11993741 := bstep (se 3 (by rfl) ⟨2248826, by rfl⟩ : syracuseStep 11993741 = 4497653) B4497653
theorem B7995827 : Blo 2129435 7995827 := bstep (se 1 (by rfl) ⟨5996870, by rfl⟩ : syracuseStep 7995827 = 11993741) B11993741
theorem B5330551 : Blo 2129435 5330551 := bstep (se 1 (by rfl) ⟨3997913, by rfl⟩ : syracuseStep 5330551 = 7995827) B7995827
theorem B7107401 : Blo 2129435 7107401 := bstep (se 2 (by rfl) ⟨2665275, by rfl⟩ : syracuseStep 7107401 = 5330551) B5330551
theorem B4738267 : Blo 2129435 4738267 := bstep (se 1 (by rfl) ⟨3553700, by rfl⟩ : syracuseStep 4738267 = 7107401) B7107401
theorem B6317689 : Blo 2129435 6317689 := bstep (se 2 (by rfl) ⟨2369133, by rfl⟩ : syracuseStep 6317689 = 4738267) B4738267
theorem B8423585 : Blo 2129435 8423585 := bstep (se 2 (by rfl) ⟨3158844, by rfl⟩ : syracuseStep 8423585 = 6317689) B6317689
theorem B5615723 : Blo 2129435 5615723 := bstep (se 1 (by rfl) ⟨4211792, by rfl⟩ : syracuseStep 5615723 = 8423585) B8423585
theorem B14975261 : Blo 2129435 14975261 := bstep (se 3 (by rfl) ⟨2807861, by rfl⟩ : syracuseStep 14975261 = 5615723) B5615723
theorem B9983507 : Blo 2129435 9983507 := bstep (se 1 (by rfl) ⟨7487630, by rfl⟩ : syracuseStep 9983507 = 14975261) B14975261
theorem B26622685 : Blo 2129435 26622685 := bstep (se 3 (by rfl) ⟨4991753, by rfl⟩ : syracuseStep 26622685 = 9983507) B9983507
theorem B35496913 : Blo 2129435 35496913 := bstep (se 2 (by rfl) ⟨13311342, by rfl⟩ : syracuseStep 35496913 = 26622685) B26622685
theorem B47329217 : Blo 2129435 47329217 := bstep (se 2 (by rfl) ⟨17748456, by rfl⟩ : syracuseStep 47329217 = 35496913) B35496913
theorem B31552811 : Blo 2129435 31552811 := bstep (se 1 (by rfl) ⟨23664608, by rfl⟩ : syracuseStep 31552811 = 47329217) B47329217
theorem B21035207 : Blo 2129435 21035207 := bstep (se 1 (by rfl) ⟨15776405, by rfl⟩ : syracuseStep 21035207 = 31552811) B31552811
theorem B56093885 : Blo 2129435 56093885 := bstep (se 3 (by rfl) ⟨10517603, by rfl⟩ : syracuseStep 56093885 = 21035207) B21035207
theorem B37395923 : Blo 2129435 37395923 := bstep (se 1 (by rfl) ⟨28046942, by rfl⟩ : syracuseStep 37395923 = 56093885) B56093885
theorem B99722461 : Blo 2129435 99722461 := bstep (se 3 (by rfl) ⟨18697961, by rfl⟩ : syracuseStep 99722461 = 37395923) B37395923
theorem B132963281 : Blo 2129435 132963281 := bstep (se 2 (by rfl) ⟨49861230, by rfl⟩ : syracuseStep 132963281 = 99722461) B99722461
theorem B88642187 : Blo 2129435 88642187 := bstep (se 1 (by rfl) ⟨66481640, by rfl⟩ : syracuseStep 88642187 = 132963281) B132963281
theorem B59094791 : Blo 2129435 59094791 := bstep (se 1 (by rfl) ⟨44321093, by rfl⟩ : syracuseStep 59094791 = 88642187) B88642187
theorem B39396527 : Blo 2129435 39396527 := bstep (se 1 (by rfl) ⟨29547395, by rfl⟩ : syracuseStep 39396527 = 59094791) B59094791
theorem B26264351 : Blo 2129435 26264351 := bstep (se 1 (by rfl) ⟨19698263, by rfl⟩ : syracuseStep 26264351 = 39396527) B39396527
theorem B17509567 : Blo 2129435 17509567 := bstep (se 1 (by rfl) ⟨13132175, by rfl⟩ : syracuseStep 17509567 = 26264351) B26264351
theorem B23346089 : Blo 2129435 23346089 := bstep (se 2 (by rfl) ⟨8754783, by rfl⟩ : syracuseStep 23346089 = 17509567) B17509567
theorem B15564059 : Blo 2129435 15564059 := bstep (se 1 (by rfl) ⟨11673044, by rfl⟩ : syracuseStep 15564059 = 23346089) B23346089
theorem B10376039 : Blo 2129435 10376039 := bstep (se 1 (by rfl) ⟨7782029, by rfl⟩ : syracuseStep 10376039 = 15564059) B15564059
theorem B6917359 : Blo 2129435 6917359 := bstep (se 1 (by rfl) ⟨5188019, by rfl⟩ : syracuseStep 6917359 = 10376039) B10376039
theorem B9223145 : Blo 2129435 9223145 := bstep (se 2 (by rfl) ⟨3458679, by rfl⟩ : syracuseStep 9223145 = 6917359) B6917359
theorem B6148763 : Blo 2129435 6148763 := bstep (se 1 (by rfl) ⟨4611572, by rfl⟩ : syracuseStep 6148763 = 9223145) B9223145
theorem B4099175 : Blo 2129435 4099175 := bstep (se 1 (by rfl) ⟨3074381, by rfl⟩ : syracuseStep 4099175 = 6148763) B6148763
theorem B2732783 : Blo 2129435 2732783 := bstep (se 1 (by rfl) ⟨2049587, by rfl⟩ : syracuseStep 2732783 = 4099175) B4099175
theorem B7287421 : Blo 2129435 7287421 := bstep (se 3 (by rfl) ⟨1366391, by rfl⟩ : syracuseStep 7287421 = 2732783) B2732783
theorem B9716561 : Blo 2129435 9716561 := bstep (se 2 (by rfl) ⟨3643710, by rfl⟩ : syracuseStep 9716561 = 7287421) B7287421
theorem B6477707 : Blo 2129435 6477707 := bstep (se 1 (by rfl) ⟨4858280, by rfl⟩ : syracuseStep 6477707 = 9716561) B9716561
theorem B4318471 : Blo 2129435 4318471 := bstep (se 1 (by rfl) ⟨3238853, by rfl⟩ : syracuseStep 4318471 = 6477707) B6477707
theorem B5757961 : Blo 2129435 5757961 := bstep (se 2 (by rfl) ⟨2159235, by rfl⟩ : syracuseStep 5757961 = 4318471) B4318471
theorem B7677281 : Blo 2129435 7677281 := bstep (se 2 (by rfl) ⟨2878980, by rfl⟩ : syracuseStep 7677281 = 5757961) B5757961
theorem B20472749 : Blo 2129435 20472749 := bstep (se 3 (by rfl) ⟨3838640, by rfl⟩ : syracuseStep 20472749 = 7677281) B7677281
theorem B13648499 : Blo 2129435 13648499 := bstep (se 1 (by rfl) ⟨10236374, by rfl⟩ : syracuseStep 13648499 = 20472749) B20472749
theorem B9098999 : Blo 2129435 9098999 := bstep (se 1 (by rfl) ⟨6824249, by rfl⟩ : syracuseStep 9098999 = 13648499) B13648499
theorem B6065999 : Blo 2129435 6065999 := bstep (se 1 (by rfl) ⟨4549499, by rfl⟩ : syracuseStep 6065999 = 9098999) B9098999
theorem B4043999 : Blo 2129435 4043999 := bstep (se 1 (by rfl) ⟨3032999, by rfl⟩ : syracuseStep 4043999 = 6065999) B6065999
theorem B2695999 : Blo 2129435 2695999 := bstep (se 1 (by rfl) ⟨2021999, by rfl⟩ : syracuseStep 2695999 = 4043999) B4043999
theorem B3594665 : Blo 2129435 3594665 := bstep (se 2 (by rfl) ⟨1347999, by rfl⟩ : syracuseStep 3594665 = 2695999) B2695999
theorem B2396443 : Blo 2129435 2396443 := bstep (se 1 (by rfl) ⟨1797332, by rfl⟩ : syracuseStep 2396443 = 3594665) B3594665
theorem B3195257 : Blo 2129435 3195257 := bstep (se 2 (by rfl) ⟨1198221, by rfl⟩ : syracuseStep 3195257 = 2396443) B2396443
theorem B2130171 : Blo 2129435 2130171 := bstep (se 1 (by rfl) ⟨1597628, by rfl⟩ : syracuseStep 2130171 = 3195257) B3195257
theorem B36396053 : Blo 2129435 36396053 := bbase (se 6 (by rfl) ⟨853032, by rfl⟩ : syracuseStep 36396053 = 1706065) (by norm_num)
theorem B24264035 : Blo 2129435 24264035 := bstep (se 1 (by rfl) ⟨18198026, by rfl⟩ : syracuseStep 24264035 = 36396053) B36396053
theorem B16176023 : Blo 2129435 16176023 := bstep (se 1 (by rfl) ⟨12132017, by rfl⟩ : syracuseStep 16176023 = 24264035) B24264035
theorem B10784015 : Blo 2129435 10784015 := bstep (se 1 (by rfl) ⟨8088011, by rfl⟩ : syracuseStep 10784015 = 16176023) B16176023
theorem B7189343 : Blo 2129435 7189343 := bstep (se 1 (by rfl) ⟨5392007, by rfl⟩ : syracuseStep 7189343 = 10784015) B10784015
theorem B4792895 : Blo 2129435 4792895 := bstep (se 1 (by rfl) ⟨3594671, by rfl⟩ : syracuseStep 4792895 = 7189343) B7189343
theorem B3195263 : Blo 2129435 3195263 := bstep (se 1 (by rfl) ⟨2396447, by rfl⟩ : syracuseStep 3195263 = 4792895) B4792895
theorem B2130175 : Blo 2129435 2130175 := bstep (se 1 (by rfl) ⟨1597631, by rfl⟩ : syracuseStep 2130175 = 3195263) B3195263
theorem B3195269 : Blo 2129435 3195269 := bbase (se 4 (by rfl) ⟨299556, by rfl⟩ : syracuseStep 3195269 = 599113) (by norm_num)
theorem B2130179 : Blo 2129435 2130179 := bstep (se 1 (by rfl) ⟨1597634, by rfl⟩ : syracuseStep 2130179 = 3195269) B3195269
theorem B3594685 : Blo 2129435 3594685 := bbase (se 3 (by rfl) ⟨674003, by rfl⟩ : syracuseStep 3594685 = 1348007) (by norm_num)
theorem B4792913 : Blo 2129435 4792913 := bstep (se 2 (by rfl) ⟨1797342, by rfl⟩ : syracuseStep 4792913 = 3594685) B3594685
theorem B3195275 : Blo 2129435 3195275 := bstep (se 1 (by rfl) ⟨2396456, by rfl⟩ : syracuseStep 3195275 = 4792913) B4792913
theorem B2130183 : Blo 2129435 2130183 := bstep (se 1 (by rfl) ⟨1597637, by rfl⟩ : syracuseStep 2130183 = 3195275) B3195275
theorem B2396461 : Blo 2129435 2396461 := bbase (se 3 (by rfl) ⟨449336, by rfl⟩ : syracuseStep 2396461 = 898673) (by norm_num)
theorem B3195281 : Blo 2129435 3195281 := bstep (se 2 (by rfl) ⟨1198230, by rfl⟩ : syracuseStep 3195281 = 2396461) B2396461
theorem B2130187 : Blo 2129435 2130187 := bstep (se 1 (by rfl) ⟨1597640, by rfl⟩ : syracuseStep 2130187 = 3195281) B3195281
theorem B7189397 : Blo 2129435 7189397 := bbase (se 6 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 7189397 = 337003) (by norm_num)
theorem B4792931 : Blo 2129435 4792931 := bstep (se 1 (by rfl) ⟨3594698, by rfl⟩ : syracuseStep 4792931 = 7189397) B7189397
theorem B3195287 : Blo 2129435 3195287 := bstep (se 1 (by rfl) ⟨2396465, by rfl⟩ : syracuseStep 3195287 = 4792931) B4792931
theorem B2130191 : Blo 2129435 2130191 := bstep (se 1 (by rfl) ⟨1597643, by rfl⟩ : syracuseStep 2130191 = 3195287) B3195287
theorem B3195293 : Blo 2129435 3195293 := bbase (se 3 (by rfl) ⟨599117, by rfl⟩ : syracuseStep 3195293 = 1198235) (by norm_num)
theorem B2130195 : Blo 2129435 2130195 := bstep (se 1 (by rfl) ⟨1597646, by rfl⟩ : syracuseStep 2130195 = 3195293) B3195293
theorem B4792949 : Blo 2129435 4792949 := bbase (se 5 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 4792949 = 449339) (by norm_num)
theorem B3195299 : Blo 2129435 3195299 := bstep (se 1 (by rfl) ⟨2396474, by rfl⟩ : syracuseStep 3195299 = 4792949) B4792949
theorem B2130199 : Blo 2129435 2130199 := bstep (se 1 (by rfl) ⟨1597649, by rfl⟩ : syracuseStep 2130199 = 3195299) B3195299
theorem B147881045 : Blo 2129435 147881045 := bbase (se 8 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 147881045 = 1732981) (by norm_num)
theorem B98587363 : Blo 2129435 98587363 := bstep (se 1 (by rfl) ⟨73940522, by rfl⟩ : syracuseStep 98587363 = 147881045) B147881045
theorem B131449817 : Blo 2129435 131449817 := bstep (se 2 (by rfl) ⟨49293681, by rfl⟩ : syracuseStep 131449817 = 98587363) B98587363
theorem B87633211 : Blo 2129435 87633211 := bstep (se 1 (by rfl) ⟨65724908, by rfl⟩ : syracuseStep 87633211 = 131449817) B131449817
theorem B116844281 : Blo 2129435 116844281 := bstep (se 2 (by rfl) ⟨43816605, by rfl⟩ : syracuseStep 116844281 = 87633211) B87633211
theorem B77896187 : Blo 2129435 77896187 := bstep (se 1 (by rfl) ⟨58422140, by rfl⟩ : syracuseStep 77896187 = 116844281) B116844281
theorem B51930791 : Blo 2129435 51930791 := bstep (se 1 (by rfl) ⟨38948093, by rfl⟩ : syracuseStep 51930791 = 77896187) B77896187
theorem B34620527 : Blo 2129435 34620527 := bstep (se 1 (by rfl) ⟨25965395, by rfl⟩ : syracuseStep 34620527 = 51930791) B51930791
theorem B23080351 : Blo 2129435 23080351 := bstep (se 1 (by rfl) ⟨17310263, by rfl⟩ : syracuseStep 23080351 = 34620527) B34620527
theorem B30773801 : Blo 2129435 30773801 := bstep (se 2 (by rfl) ⟨11540175, by rfl⟩ : syracuseStep 30773801 = 23080351) B23080351
theorem B82063469 : Blo 2129435 82063469 := bstep (se 3 (by rfl) ⟨15386900, by rfl⟩ : syracuseStep 82063469 = 30773801) B30773801
theorem B54708979 : Blo 2129435 54708979 := bstep (se 1 (by rfl) ⟨41031734, by rfl⟩ : syracuseStep 54708979 = 82063469) B82063469
theorem B72945305 : Blo 2129435 72945305 := bstep (se 2 (by rfl) ⟨27354489, by rfl⟩ : syracuseStep 72945305 = 54708979) B54708979
theorem B48630203 : Blo 2129435 48630203 := bstep (se 1 (by rfl) ⟨36472652, by rfl⟩ : syracuseStep 48630203 = 72945305) B72945305
theorem B32420135 : Blo 2129435 32420135 := bstep (se 1 (by rfl) ⟨24315101, by rfl⟩ : syracuseStep 32420135 = 48630203) B48630203
theorem B21613423 : Blo 2129435 21613423 := bstep (se 1 (by rfl) ⟨16210067, by rfl⟩ : syracuseStep 21613423 = 32420135) B32420135
theorem B28817897 : Blo 2129435 28817897 := bstep (se 2 (by rfl) ⟨10806711, by rfl⟩ : syracuseStep 28817897 = 21613423) B21613423
theorem B76847725 : Blo 2129435 76847725 := bstep (se 3 (by rfl) ⟨14408948, by rfl⟩ : syracuseStep 76847725 = 28817897) B28817897
theorem B102463633 : Blo 2129435 102463633 := bstep (se 2 (by rfl) ⟨38423862, by rfl⟩ : syracuseStep 102463633 = 76847725) B76847725
theorem B136618177 : Blo 2129435 136618177 := bstep (se 2 (by rfl) ⟨51231816, by rfl⟩ : syracuseStep 136618177 = 102463633) B102463633
theorem B182157569 : Blo 2129435 182157569 := bstep (se 2 (by rfl) ⟨68309088, by rfl⟩ : syracuseStep 182157569 = 136618177) B136618177
theorem B121438379 : Blo 2129435 121438379 := bstep (se 1 (by rfl) ⟨91078784, by rfl⟩ : syracuseStep 121438379 = 182157569) B182157569
theorem B80958919 : Blo 2129435 80958919 := bstep (se 1 (by rfl) ⟨60719189, by rfl⟩ : syracuseStep 80958919 = 121438379) B121438379
theorem B107945225 : Blo 2129435 107945225 := bstep (se 2 (by rfl) ⟨40479459, by rfl⟩ : syracuseStep 107945225 = 80958919) B80958919
theorem B71963483 : Blo 2129435 71963483 := bstep (se 1 (by rfl) ⟨53972612, by rfl⟩ : syracuseStep 71963483 = 107945225) B107945225
theorem B191902621 : Blo 2129435 191902621 := bstep (se 3 (by rfl) ⟨35981741, by rfl⟩ : syracuseStep 191902621 = 71963483) B71963483
theorem B255870161 : Blo 2129435 255870161 := bstep (se 2 (by rfl) ⟨95951310, by rfl⟩ : syracuseStep 255870161 = 191902621) B191902621
theorem B170580107 : Blo 2129435 170580107 := bstep (se 1 (by rfl) ⟨127935080, by rfl⟩ : syracuseStep 170580107 = 255870161) B255870161
theorem B113720071 : Blo 2129435 113720071 := bstep (se 1 (by rfl) ⟨85290053, by rfl⟩ : syracuseStep 113720071 = 170580107) B170580107
theorem B151626761 : Blo 2129435 151626761 := bstep (se 2 (by rfl) ⟨56860035, by rfl⟩ : syracuseStep 151626761 = 113720071) B113720071
theorem B101084507 : Blo 2129435 101084507 := bstep (se 1 (by rfl) ⟨75813380, by rfl⟩ : syracuseStep 101084507 = 151626761) B151626761
theorem B67389671 : Blo 2129435 67389671 := bstep (se 1 (by rfl) ⟨50542253, by rfl⟩ : syracuseStep 67389671 = 101084507) B101084507
theorem B179705789 : Blo 2129435 179705789 := bstep (se 3 (by rfl) ⟨33694835, by rfl⟩ : syracuseStep 179705789 = 67389671) B67389671
theorem B119803859 : Blo 2129435 119803859 := bstep (se 1 (by rfl) ⟨89852894, by rfl⟩ : syracuseStep 119803859 = 179705789) B179705789
theorem B79869239 : Blo 2129435 79869239 := bstep (se 1 (by rfl) ⟨59901929, by rfl⟩ : syracuseStep 79869239 = 119803859) B119803859
theorem B53246159 : Blo 2129435 53246159 := bstep (se 1 (by rfl) ⟨39934619, by rfl⟩ : syracuseStep 53246159 = 79869239) B79869239
theorem B35497439 : Blo 2129435 35497439 := bstep (se 1 (by rfl) ⟨26623079, by rfl⟩ : syracuseStep 35497439 = 53246159) B53246159
theorem B23664959 : Blo 2129435 23664959 := bstep (se 1 (by rfl) ⟨17748719, by rfl⟩ : syracuseStep 23664959 = 35497439) B35497439
theorem B15776639 : Blo 2129435 15776639 := bstep (se 1 (by rfl) ⟨11832479, by rfl⟩ : syracuseStep 15776639 = 23664959) B23664959
theorem B10517759 : Blo 2129435 10517759 := bstep (se 1 (by rfl) ⟨7888319, by rfl⟩ : syracuseStep 10517759 = 15776639) B15776639
theorem B7011839 : Blo 2129435 7011839 := bstep (se 1 (by rfl) ⟨5258879, by rfl⟩ : syracuseStep 7011839 = 10517759) B10517759
theorem B4674559 : Blo 2129435 4674559 := bstep (se 1 (by rfl) ⟨3505919, by rfl⟩ : syracuseStep 4674559 = 7011839) B7011839
theorem B6232745 : Blo 2129435 6232745 := bstep (se 2 (by rfl) ⟨2337279, by rfl⟩ : syracuseStep 6232745 = 4674559) B4674559
theorem B16620653 : Blo 2129435 16620653 := bstep (se 3 (by rfl) ⟨3116372, by rfl⟩ : syracuseStep 16620653 = 6232745) B6232745
theorem B44321741 : Blo 2129435 44321741 := bstep (se 3 (by rfl) ⟨8310326, by rfl⟩ : syracuseStep 44321741 = 16620653) B16620653
theorem B29547827 : Blo 2129435 29547827 := bstep (se 1 (by rfl) ⟨22160870, by rfl⟩ : syracuseStep 29547827 = 44321741) B44321741
theorem B19698551 : Blo 2129435 19698551 := bstep (se 1 (by rfl) ⟨14773913, by rfl⟩ : syracuseStep 19698551 = 29547827) B29547827
theorem B13132367 : Blo 2129435 13132367 := bstep (se 1 (by rfl) ⟨9849275, by rfl⟩ : syracuseStep 13132367 = 19698551) B19698551
theorem B8754911 : Blo 2129435 8754911 := bstep (se 1 (by rfl) ⟨6566183, by rfl⟩ : syracuseStep 8754911 = 13132367) B13132367
theorem B5836607 : Blo 2129435 5836607 := bstep (se 1 (by rfl) ⟨4377455, by rfl⟩ : syracuseStep 5836607 = 8754911) B8754911
theorem B3891071 : Blo 2129435 3891071 := bstep (se 1 (by rfl) ⟨2918303, by rfl⟩ : syracuseStep 3891071 = 5836607) B5836607
theorem B10376189 : Blo 2129435 10376189 := bstep (se 3 (by rfl) ⟨1945535, by rfl⟩ : syracuseStep 10376189 = 3891071) B3891071
theorem B6917459 : Blo 2129435 6917459 := bstep (se 1 (by rfl) ⟨5188094, by rfl⟩ : syracuseStep 6917459 = 10376189) B10376189
theorem B18446557 : Blo 2129435 18446557 := bstep (se 3 (by rfl) ⟨3458729, by rfl⟩ : syracuseStep 18446557 = 6917459) B6917459
theorem B24595409 : Blo 2129435 24595409 := bstep (se 2 (by rfl) ⟨9223278, by rfl⟩ : syracuseStep 24595409 = 18446557) B18446557
theorem B16396939 : Blo 2129435 16396939 := bstep (se 1 (by rfl) ⟨12297704, by rfl⟩ : syracuseStep 16396939 = 24595409) B24595409
theorem B21862585 : Blo 2129435 21862585 := bstep (se 2 (by rfl) ⟨8198469, by rfl⟩ : syracuseStep 21862585 = 16396939) B16396939
theorem B29150113 : Blo 2129435 29150113 := bstep (se 2 (by rfl) ⟨10931292, by rfl⟩ : syracuseStep 29150113 = 21862585) B21862585
theorem B38866817 : Blo 2129435 38866817 := bstep (se 2 (by rfl) ⟨14575056, by rfl⟩ : syracuseStep 38866817 = 29150113) B29150113
theorem B25911211 : Blo 2129435 25911211 := bstep (se 1 (by rfl) ⟨19433408, by rfl⟩ : syracuseStep 25911211 = 38866817) B38866817
theorem B34548281 : Blo 2129435 34548281 := bstep (se 2 (by rfl) ⟨12955605, by rfl⟩ : syracuseStep 34548281 = 25911211) B25911211
theorem B23032187 : Blo 2129435 23032187 := bstep (se 1 (by rfl) ⟨17274140, by rfl⟩ : syracuseStep 23032187 = 34548281) B34548281
theorem B15354791 : Blo 2129435 15354791 := bstep (se 1 (by rfl) ⟨11516093, by rfl⟩ : syracuseStep 15354791 = 23032187) B23032187
theorem B10236527 : Blo 2129435 10236527 := bstep (se 1 (by rfl) ⟨7677395, by rfl⟩ : syracuseStep 10236527 = 15354791) B15354791
theorem B6824351 : Blo 2129435 6824351 := bstep (se 1 (by rfl) ⟨5118263, by rfl⟩ : syracuseStep 6824351 = 10236527) B10236527
theorem B18198269 : Blo 2129435 18198269 := bstep (se 3 (by rfl) ⟨3412175, by rfl⟩ : syracuseStep 18198269 = 6824351) B6824351
theorem B12132179 : Blo 2129435 12132179 := bstep (se 1 (by rfl) ⟨9099134, by rfl⟩ : syracuseStep 12132179 = 18198269) B18198269
theorem B8088119 : Blo 2129435 8088119 := bstep (se 1 (by rfl) ⟨6066089, by rfl⟩ : syracuseStep 8088119 = 12132179) B12132179
theorem B5392079 : Blo 2129435 5392079 := bstep (se 1 (by rfl) ⟨4044059, by rfl⟩ : syracuseStep 5392079 = 8088119) B8088119
theorem B3594719 : Blo 2129435 3594719 := bstep (se 1 (by rfl) ⟨2696039, by rfl⟩ : syracuseStep 3594719 = 5392079) B5392079
theorem B2396479 : Blo 2129435 2396479 := bstep (se 1 (by rfl) ⟨1797359, by rfl⟩ : syracuseStep 2396479 = 3594719) B3594719
theorem B3195305 : Blo 2129435 3195305 := bstep (se 2 (by rfl) ⟨1198239, by rfl⟩ : syracuseStep 3195305 = 2396479) B2396479
theorem B2130203 : Blo 2129435 2130203 := bstep (se 1 (by rfl) ⟨1597652, by rfl⟩ : syracuseStep 2130203 = 3195305) B3195305
theorem B8088133 : Blo 2129435 8088133 := bbase (se 4 (by rfl) ⟨758262, by rfl⟩ : syracuseStep 8088133 = 1516525) (by norm_num)
theorem B10784177 : Blo 2129435 10784177 := bstep (se 2 (by rfl) ⟨4044066, by rfl⟩ : syracuseStep 10784177 = 8088133) B8088133
theorem B7189451 : Blo 2129435 7189451 := bstep (se 1 (by rfl) ⟨5392088, by rfl⟩ : syracuseStep 7189451 = 10784177) B10784177
theorem B4792967 : Blo 2129435 4792967 := bstep (se 1 (by rfl) ⟨3594725, by rfl⟩ : syracuseStep 4792967 = 7189451) B7189451
theorem B3195311 : Blo 2129435 3195311 := bstep (se 1 (by rfl) ⟨2396483, by rfl⟩ : syracuseStep 3195311 = 4792967) B4792967
theorem B2130207 : Blo 2129435 2130207 := bstep (se 1 (by rfl) ⟨1597655, by rfl⟩ : syracuseStep 2130207 = 3195311) B3195311
theorem B3195317 : Blo 2129435 3195317 := bbase (se 5 (by rfl) ⟨149780, by rfl⟩ : syracuseStep 3195317 = 299561) (by norm_num)
theorem B2130211 : Blo 2129435 2130211 := bstep (se 1 (by rfl) ⟨1597658, by rfl⟩ : syracuseStep 2130211 = 3195317) B3195317
theorem B5392109 : Blo 2129435 5392109 := bbase (se 3 (by rfl) ⟨1011020, by rfl⟩ : syracuseStep 5392109 = 2022041) (by norm_num)
theorem B3594739 : Blo 2129435 3594739 := bstep (se 1 (by rfl) ⟨2696054, by rfl⟩ : syracuseStep 3594739 = 5392109) B5392109
theorem B4792985 : Blo 2129435 4792985 := bstep (se 2 (by rfl) ⟨1797369, by rfl⟩ : syracuseStep 4792985 = 3594739) B3594739
theorem B3195323 : Blo 2129435 3195323 := bstep (se 1 (by rfl) ⟨2396492, by rfl⟩ : syracuseStep 3195323 = 4792985) B4792985
theorem B2130215 : Blo 2129435 2130215 := bstep (se 1 (by rfl) ⟨1597661, by rfl⟩ : syracuseStep 2130215 = 3195323) B3195323
theorem B2396497 : Blo 2129435 2396497 := bbase (se 2 (by rfl) ⟨898686, by rfl⟩ : syracuseStep 2396497 = 1797373) (by norm_num)
theorem B3195329 : Blo 2129435 3195329 := bstep (se 2 (by rfl) ⟨1198248, by rfl⟩ : syracuseStep 3195329 = 2396497) B2396497
theorem B2130219 : Blo 2129435 2130219 := bstep (se 1 (by rfl) ⟨1597664, by rfl⟩ : syracuseStep 2130219 = 3195329) B3195329
theorem B2274805 : Blo 2129435 2274805 := bbase (se 5 (by rfl) ⟨106631, by rfl⟩ : syracuseStep 2274805 = 213263) (by norm_num)
theorem B3033073 : Blo 2129435 3033073 := bstep (se 2 (by rfl) ⟨1137402, by rfl⟩ : syracuseStep 3033073 = 2274805) B2274805
theorem B4044097 : Blo 2129435 4044097 := bstep (se 2 (by rfl) ⟨1516536, by rfl⟩ : syracuseStep 4044097 = 3033073) B3033073
theorem B5392129 : Blo 2129435 5392129 := bstep (se 2 (by rfl) ⟨2022048, by rfl⟩ : syracuseStep 5392129 = 4044097) B4044097
theorem B7189505 : Blo 2129435 7189505 := bstep (se 2 (by rfl) ⟨2696064, by rfl⟩ : syracuseStep 7189505 = 5392129) B5392129
theorem B4793003 : Blo 2129435 4793003 := bstep (se 1 (by rfl) ⟨3594752, by rfl⟩ : syracuseStep 4793003 = 7189505) B7189505
theorem B3195335 : Blo 2129435 3195335 := bstep (se 1 (by rfl) ⟨2396501, by rfl⟩ : syracuseStep 3195335 = 4793003) B4793003
theorem B2130223 : Blo 2129435 2130223 := bstep (se 1 (by rfl) ⟨1597667, by rfl⟩ : syracuseStep 2130223 = 3195335) B3195335
theorem B3195341 : Blo 2129435 3195341 := bbase (se 3 (by rfl) ⟨599126, by rfl⟩ : syracuseStep 3195341 = 1198253) (by norm_num)
theorem B2130227 : Blo 2129435 2130227 := bstep (se 1 (by rfl) ⟨1597670, by rfl⟩ : syracuseStep 2130227 = 3195341) B3195341
theorem B4793021 : Blo 2129435 4793021 := bbase (se 3 (by rfl) ⟨898691, by rfl⟩ : syracuseStep 4793021 = 1797383) (by norm_num)
theorem B3195347 : Blo 2129435 3195347 := bstep (se 1 (by rfl) ⟨2396510, by rfl⟩ : syracuseStep 3195347 = 4793021) B4793021
theorem B2130231 : Blo 2129435 2130231 := bstep (se 1 (by rfl) ⟨1597673, by rfl⟩ : syracuseStep 2130231 = 3195347) B3195347
theorem B3594773 : Blo 2129435 3594773 := bbase (se 6 (by rfl) ⟨84252, by rfl⟩ : syracuseStep 3594773 = 168505) (by norm_num)
theorem B2396515 : Blo 2129435 2396515 := bstep (se 1 (by rfl) ⟨1797386, by rfl⟩ : syracuseStep 2396515 = 3594773) B3594773
theorem B3195353 : Blo 2129435 3195353 := bstep (se 2 (by rfl) ⟨1198257, by rfl⟩ : syracuseStep 3195353 = 2396515) B2396515
theorem B2130235 : Blo 2129435 2130235 := bstep (se 1 (by rfl) ⟨1597676, by rfl⟩ : syracuseStep 2130235 = 3195353) B3195353
theorem B20473397 : Blo 2129435 20473397 := bbase (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) (by norm_num)
theorem B13648931 : Blo 2129435 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B9099287 : Blo 2129435 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B6066191 : Blo 2129435 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B16176509 : Blo 2129435 16176509 := bstep (se 3 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 16176509 = 6066191) B6066191
theorem B10784339 : Blo 2129435 10784339 := bstep (se 1 (by rfl) ⟨8088254, by rfl⟩ : syracuseStep 10784339 = 16176509) B16176509
theorem B7189559 : Blo 2129435 7189559 := bstep (se 1 (by rfl) ⟨5392169, by rfl⟩ : syracuseStep 7189559 = 10784339) B10784339
theorem B4793039 : Blo 2129435 4793039 := bstep (se 1 (by rfl) ⟨3594779, by rfl⟩ : syracuseStep 4793039 = 7189559) B7189559
theorem B3195359 : Blo 2129435 3195359 := bstep (se 1 (by rfl) ⟨2396519, by rfl⟩ : syracuseStep 3195359 = 4793039) B4793039
theorem B2130239 : Blo 2129435 2130239 := bstep (se 1 (by rfl) ⟨1597679, by rfl⟩ : syracuseStep 2130239 = 3195359) B3195359
theorem B3195365 : Blo 2129435 3195365 := bbase (se 4 (by rfl) ⟨299565, by rfl⟩ : syracuseStep 3195365 = 599131) (by norm_num)
theorem B2130243 : Blo 2129435 2130243 := bstep (se 1 (by rfl) ⟨1597682, by rfl⟩ : syracuseStep 2130243 = 3195365) B3195365
theorem B2732881 : Blo 2129435 2732881 := bbase (se 2 (by rfl) ⟨1024830, by rfl⟩ : syracuseStep 2732881 = 2049661) (by norm_num)
theorem B3643841 : Blo 2129435 3643841 := bstep (se 2 (by rfl) ⟨1366440, by rfl⟩ : syracuseStep 3643841 = 2732881) B2732881
theorem B2429227 : Blo 2129435 2429227 := bstep (se 1 (by rfl) ⟨1821920, by rfl⟩ : syracuseStep 2429227 = 3643841) B3643841
theorem B3238969 : Blo 2129435 3238969 := bstep (se 2 (by rfl) ⟨1214613, by rfl⟩ : syracuseStep 3238969 = 2429227) B2429227
theorem B4318625 : Blo 2129435 4318625 := bstep (se 2 (by rfl) ⟨1619484, by rfl⟩ : syracuseStep 4318625 = 3238969) B3238969
theorem B2879083 : Blo 2129435 2879083 := bstep (se 1 (by rfl) ⟨2159312, by rfl⟩ : syracuseStep 2879083 = 4318625) B4318625
theorem B15355109 : Blo 2129435 15355109 := bstep (se 4 (by rfl) ⟨1439541, by rfl⟩ : syracuseStep 15355109 = 2879083) B2879083
theorem B10236739 : Blo 2129435 10236739 := bstep (se 1 (by rfl) ⟨7677554, by rfl⟩ : syracuseStep 10236739 = 15355109) B15355109
theorem B13648985 : Blo 2129435 13648985 := bstep (se 2 (by rfl) ⟨5118369, by rfl⟩ : syracuseStep 13648985 = 10236739) B10236739
theorem B9099323 : Blo 2129435 9099323 := bstep (se 1 (by rfl) ⟨6824492, by rfl⟩ : syracuseStep 9099323 = 13648985) B13648985
theorem B6066215 : Blo 2129435 6066215 := bstep (se 1 (by rfl) ⟨4549661, by rfl⟩ : syracuseStep 6066215 = 9099323) B9099323
theorem B4044143 : Blo 2129435 4044143 := bstep (se 1 (by rfl) ⟨3033107, by rfl⟩ : syracuseStep 4044143 = 6066215) B6066215
theorem B2696095 : Blo 2129435 2696095 := bstep (se 1 (by rfl) ⟨2022071, by rfl⟩ : syracuseStep 2696095 = 4044143) B4044143
theorem B3594793 : Blo 2129435 3594793 := bstep (se 2 (by rfl) ⟨1348047, by rfl⟩ : syracuseStep 3594793 = 2696095) B2696095
theorem B4793057 : Blo 2129435 4793057 := bstep (se 2 (by rfl) ⟨1797396, by rfl⟩ : syracuseStep 4793057 = 3594793) B3594793
theorem B3195371 : Blo 2129435 3195371 := bstep (se 1 (by rfl) ⟨2396528, by rfl⟩ : syracuseStep 3195371 = 4793057) B4793057
theorem B2130247 : Blo 2129435 2130247 := bstep (se 1 (by rfl) ⟨1597685, by rfl⟩ : syracuseStep 2130247 = 3195371) B3195371
theorem B2396533 : Blo 2129435 2396533 := bbase (se 5 (by rfl) ⟨112337, by rfl⟩ : syracuseStep 2396533 = 224675) (by norm_num)
theorem B3195377 : Blo 2129435 3195377 := bstep (se 2 (by rfl) ⟨1198266, by rfl⟩ : syracuseStep 3195377 = 2396533) B2396533
theorem B2130251 : Blo 2129435 2130251 := bstep (se 1 (by rfl) ⟨1597688, by rfl⟩ : syracuseStep 2130251 = 3195377) B3195377
theorem B2696105 : Blo 2129435 2696105 := bbase (se 2 (by rfl) ⟨1011039, by rfl⟩ : syracuseStep 2696105 = 2022079) (by norm_num)
theorem B7189613 : Blo 2129435 7189613 := bstep (se 3 (by rfl) ⟨1348052, by rfl⟩ : syracuseStep 7189613 = 2696105) B2696105
theorem B4793075 : Blo 2129435 4793075 := bstep (se 1 (by rfl) ⟨3594806, by rfl⟩ : syracuseStep 4793075 = 7189613) B7189613
theorem B3195383 : Blo 2129435 3195383 := bstep (se 1 (by rfl) ⟨2396537, by rfl⟩ : syracuseStep 3195383 = 4793075) B4793075
theorem B2130255 : Blo 2129435 2130255 := bstep (se 1 (by rfl) ⟨1597691, by rfl⟩ : syracuseStep 2130255 = 3195383) B3195383
theorem B3195389 : Blo 2129435 3195389 := bbase (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) (by norm_num)
theorem B2130259 : Blo 2129435 2130259 := bstep (se 1 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 2130259 = 3195389) B3195389
theorem B4793093 : Blo 2129435 4793093 := bbase (se 4 (by rfl) ⟨449352, by rfl⟩ : syracuseStep 4793093 = 898705) (by norm_num)
theorem B3195395 : Blo 2129435 3195395 := bstep (se 1 (by rfl) ⟨2396546, by rfl⟩ : syracuseStep 3195395 = 4793093) B4793093
theorem B2130263 : Blo 2129435 2130263 := bstep (se 1 (by rfl) ⟨1597697, by rfl⟩ : syracuseStep 2130263 = 3195395) B3195395
theorem B4044181 : Blo 2129435 4044181 := bbase (se 6 (by rfl) ⟨94785, by rfl⟩ : syracuseStep 4044181 = 189571) (by norm_num)
theorem B5392241 : Blo 2129435 5392241 := bstep (se 2 (by rfl) ⟨2022090, by rfl⟩ : syracuseStep 5392241 = 4044181) B4044181
theorem B3594827 : Blo 2129435 3594827 := bstep (se 1 (by rfl) ⟨2696120, by rfl⟩ : syracuseStep 3594827 = 5392241) B5392241
theorem B2396551 : Blo 2129435 2396551 := bstep (se 1 (by rfl) ⟨1797413, by rfl⟩ : syracuseStep 2396551 = 3594827) B3594827
theorem B3195401 : Blo 2129435 3195401 := bstep (se 2 (by rfl) ⟨1198275, by rfl⟩ : syracuseStep 3195401 = 2396551) B2396551
theorem B2130267 : Blo 2129435 2130267 := bstep (se 1 (by rfl) ⟨1597700, by rfl⟩ : syracuseStep 2130267 = 3195401) B3195401
theorem B10784501 : Blo 2129435 10784501 := bbase (se 5 (by rfl) ⟨505523, by rfl⟩ : syracuseStep 10784501 = 1011047) (by norm_num)
theorem B7189667 : Blo 2129435 7189667 := bstep (se 1 (by rfl) ⟨5392250, by rfl⟩ : syracuseStep 7189667 = 10784501) B10784501
theorem B4793111 : Blo 2129435 4793111 := bstep (se 1 (by rfl) ⟨3594833, by rfl⟩ : syracuseStep 4793111 = 7189667) B7189667
theorem B3195407 : Blo 2129435 3195407 := bstep (se 1 (by rfl) ⟨2396555, by rfl⟩ : syracuseStep 3195407 = 4793111) B4793111
theorem B2130271 : Blo 2129435 2130271 := bstep (se 1 (by rfl) ⟨1597703, by rfl⟩ : syracuseStep 2130271 = 3195407) B3195407
theorem B3195413 : Blo 2129435 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B2130275 : Blo 2129435 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B2159345 : Blo 2129435 2159345 := bbase (se 2 (by rfl) ⟨809754, by rfl⟩ : syracuseStep 2159345 = 1619509) (by norm_num)
theorem B5758253 : Blo 2129435 5758253 := bstep (se 3 (by rfl) ⟨1079672, by rfl⟩ : syracuseStep 5758253 = 2159345) B2159345
theorem B3838835 : Blo 2129435 3838835 := bstep (se 1 (by rfl) ⟨2879126, by rfl⟩ : syracuseStep 3838835 = 5758253) B5758253
theorem B2559223 : Blo 2129435 2559223 := bstep (se 1 (by rfl) ⟨1919417, by rfl⟩ : syracuseStep 2559223 = 3838835) B3838835
theorem B3412297 : Blo 2129435 3412297 := bstep (se 2 (by rfl) ⟨1279611, by rfl⟩ : syracuseStep 3412297 = 2559223) B2559223
theorem B18198917 : Blo 2129435 18198917 := bstep (se 4 (by rfl) ⟨1706148, by rfl⟩ : syracuseStep 18198917 = 3412297) B3412297
theorem B12132611 : Blo 2129435 12132611 := bstep (se 1 (by rfl) ⟨9099458, by rfl⟩ : syracuseStep 12132611 = 18198917) B18198917
theorem B8088407 : Blo 2129435 8088407 := bstep (se 1 (by rfl) ⟨6066305, by rfl⟩ : syracuseStep 8088407 = 12132611) B12132611
theorem B5392271 : Blo 2129435 5392271 := bstep (se 1 (by rfl) ⟨4044203, by rfl⟩ : syracuseStep 5392271 = 8088407) B8088407
theorem B3594847 : Blo 2129435 3594847 := bstep (se 1 (by rfl) ⟨2696135, by rfl⟩ : syracuseStep 3594847 = 5392271) B5392271
theorem B4793129 : Blo 2129435 4793129 := bstep (se 2 (by rfl) ⟨1797423, by rfl⟩ : syracuseStep 4793129 = 3594847) B3594847
theorem B3195419 : Blo 2129435 3195419 := bstep (se 1 (by rfl) ⟨2396564, by rfl⟩ : syracuseStep 3195419 = 4793129) B4793129
theorem B2130279 : Blo 2129435 2130279 := bstep (se 1 (by rfl) ⟨1597709, by rfl⟩ : syracuseStep 2130279 = 3195419) B3195419
theorem B2396569 : Blo 2129435 2396569 := bbase (se 2 (by rfl) ⟨898713, by rfl⟩ : syracuseStep 2396569 = 1797427) (by norm_num)
theorem B3195425 : Blo 2129435 3195425 := bstep (se 2 (by rfl) ⟨1198284, by rfl⟩ : syracuseStep 3195425 = 2396569) B2396569
theorem B2130283 : Blo 2129435 2130283 := bstep (se 1 (by rfl) ⟨1597712, by rfl⟩ : syracuseStep 2130283 = 3195425) B3195425
theorem B8088437 : Blo 2129435 8088437 := bbase (se 5 (by rfl) ⟨379145, by rfl⟩ : syracuseStep 8088437 = 758291) (by norm_num)
theorem B5392291 : Blo 2129435 5392291 := bstep (se 1 (by rfl) ⟨4044218, by rfl⟩ : syracuseStep 5392291 = 8088437) B8088437
theorem B7189721 : Blo 2129435 7189721 := bstep (se 2 (by rfl) ⟨2696145, by rfl⟩ : syracuseStep 7189721 = 5392291) B5392291
theorem B4793147 : Blo 2129435 4793147 := bstep (se 1 (by rfl) ⟨3594860, by rfl⟩ : syracuseStep 4793147 = 7189721) B7189721
theorem B3195431 : Blo 2129435 3195431 := bstep (se 1 (by rfl) ⟨2396573, by rfl⟩ : syracuseStep 3195431 = 4793147) B4793147
theorem B2130287 : Blo 2129435 2130287 := bstep (se 1 (by rfl) ⟨1597715, by rfl⟩ : syracuseStep 2130287 = 3195431) B3195431
theorem B3195437 : Blo 2129435 3195437 := bbase (se 3 (by rfl) ⟨599144, by rfl⟩ : syracuseStep 3195437 = 1198289) (by norm_num)
theorem B2130291 : Blo 2129435 2130291 := bstep (se 1 (by rfl) ⟨1597718, by rfl⟩ : syracuseStep 2130291 = 3195437) B3195437
theorem B4793165 : Blo 2129435 4793165 := bbase (se 3 (by rfl) ⟨898718, by rfl⟩ : syracuseStep 4793165 = 1797437) (by norm_num)
theorem B3195443 : Blo 2129435 3195443 := bstep (se 1 (by rfl) ⟨2396582, by rfl⟩ : syracuseStep 3195443 = 4793165) B4793165
theorem B2130295 : Blo 2129435 2130295 := bstep (se 1 (by rfl) ⟨1597721, by rfl⟩ : syracuseStep 2130295 = 3195443) B3195443
theorem B2696161 : Blo 2129435 2696161 := bbase (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) (by norm_num)
theorem B3594881 : Blo 2129435 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B2396587 : Blo 2129435 2396587 := bstep (se 1 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 2396587 = 3594881) B3594881
theorem B3195449 : Blo 2129435 3195449 := bstep (se 2 (by rfl) ⟨1198293, by rfl⟩ : syracuseStep 3195449 = 2396587) B2396587
theorem B2130299 : Blo 2129435 2130299 := bstep (se 1 (by rfl) ⟨1597724, by rfl⟩ : syracuseStep 2130299 = 3195449) B3195449
theorem B24265493 : Blo 2129435 24265493 := bbase (se 6 (by rfl) ⟨568722, by rfl⟩ : syracuseStep 24265493 = 1137445) (by norm_num)
theorem B16176995 : Blo 2129435 16176995 := bstep (se 1 (by rfl) ⟨12132746, by rfl⟩ : syracuseStep 16176995 = 24265493) B24265493
theorem B10784663 : Blo 2129435 10784663 := bstep (se 1 (by rfl) ⟨8088497, by rfl⟩ : syracuseStep 10784663 = 16176995) B16176995
theorem B7189775 : Blo 2129435 7189775 := bstep (se 1 (by rfl) ⟨5392331, by rfl⟩ : syracuseStep 7189775 = 10784663) B10784663
theorem B4793183 : Blo 2129435 4793183 := bstep (se 1 (by rfl) ⟨3594887, by rfl⟩ : syracuseStep 4793183 = 7189775) B7189775
theorem B3195455 : Blo 2129435 3195455 := bstep (se 1 (by rfl) ⟨2396591, by rfl⟩ : syracuseStep 3195455 = 4793183) B4793183
theorem B2130303 : Blo 2129435 2130303 := bstep (se 1 (by rfl) ⟨1597727, by rfl⟩ : syracuseStep 2130303 = 3195455) B3195455
theorem B3195461 : Blo 2129435 3195461 := bbase (se 4 (by rfl) ⟨299574, by rfl⟩ : syracuseStep 3195461 = 599149) (by norm_num)
theorem B2130307 : Blo 2129435 2130307 := bstep (se 1 (by rfl) ⟨1597730, by rfl⟩ : syracuseStep 2130307 = 3195461) B3195461
theorem B3594901 : Blo 2129435 3594901 := bbase (se 6 (by rfl) ⟨84255, by rfl⟩ : syracuseStep 3594901 = 168511) (by norm_num)
theorem B4793201 : Blo 2129435 4793201 := bstep (se 2 (by rfl) ⟨1797450, by rfl⟩ : syracuseStep 4793201 = 3594901) B3594901
theorem B3195467 : Blo 2129435 3195467 := bstep (se 1 (by rfl) ⟨2396600, by rfl⟩ : syracuseStep 3195467 = 4793201) B4793201
theorem B2130311 : Blo 2129435 2130311 := bstep (se 1 (by rfl) ⟨1597733, by rfl⟩ : syracuseStep 2130311 = 3195467) B3195467
theorem B2396605 : Blo 2129435 2396605 := bbase (se 3 (by rfl) ⟨449363, by rfl⟩ : syracuseStep 2396605 = 898727) (by norm_num)
theorem B3195473 : Blo 2129435 3195473 := bstep (se 2 (by rfl) ⟨1198302, by rfl⟩ : syracuseStep 3195473 = 2396605) B2396605
theorem B2130315 : Blo 2129435 2130315 := bstep (se 1 (by rfl) ⟨1597736, by rfl⟩ : syracuseStep 2130315 = 3195473) B3195473
theorem B7189829 : Blo 2129435 7189829 := bbase (se 4 (by rfl) ⟨674046, by rfl⟩ : syracuseStep 7189829 = 1348093) (by norm_num)
theorem B4793219 : Blo 2129435 4793219 := bstep (se 1 (by rfl) ⟨3594914, by rfl⟩ : syracuseStep 4793219 = 7189829) B7189829
theorem B3195479 : Blo 2129435 3195479 := bstep (se 1 (by rfl) ⟨2396609, by rfl⟩ : syracuseStep 3195479 = 4793219) B4793219
theorem B2130319 : Blo 2129435 2130319 := bstep (se 1 (by rfl) ⟨1597739, by rfl⟩ : syracuseStep 2130319 = 3195479) B3195479
theorem B3195485 : Blo 2129435 3195485 := bbase (se 3 (by rfl) ⟨599153, by rfl⟩ : syracuseStep 3195485 = 1198307) (by norm_num)
theorem B2130323 : Blo 2129435 2130323 := bstep (se 1 (by rfl) ⟨1597742, by rfl⟩ : syracuseStep 2130323 = 3195485) B3195485
theorem B4793237 : Blo 2129435 4793237 := bbase (se 6 (by rfl) ⟨112341, by rfl⟩ : syracuseStep 4793237 = 224683) (by norm_num)
theorem B3195491 : Blo 2129435 3195491 := bstep (se 1 (by rfl) ⟨2396618, by rfl⟩ : syracuseStep 3195491 = 4793237) B4793237
theorem B2130327 : Blo 2129435 2130327 := bstep (se 1 (by rfl) ⟨1597745, by rfl⟩ : syracuseStep 2130327 = 3195491) B3195491
theorem B3412381 : Blo 2129435 3412381 := bbase (se 3 (by rfl) ⟨639821, by rfl⟩ : syracuseStep 3412381 = 1279643) (by norm_num)
theorem B4549841 : Blo 2129435 4549841 := bstep (se 2 (by rfl) ⟨1706190, by rfl⟩ : syracuseStep 4549841 = 3412381) B3412381
theorem B3033227 : Blo 2129435 3033227 := bstep (se 1 (by rfl) ⟨2274920, by rfl⟩ : syracuseStep 3033227 = 4549841) B4549841
theorem B8088605 : Blo 2129435 8088605 := bstep (se 3 (by rfl) ⟨1516613, by rfl⟩ : syracuseStep 8088605 = 3033227) B3033227
theorem B5392403 : Blo 2129435 5392403 := bstep (se 1 (by rfl) ⟨4044302, by rfl⟩ : syracuseStep 5392403 = 8088605) B8088605
theorem B3594935 : Blo 2129435 3594935 := bstep (se 1 (by rfl) ⟨2696201, by rfl⟩ : syracuseStep 3594935 = 5392403) B5392403
theorem B2396623 : Blo 2129435 2396623 := bstep (se 1 (by rfl) ⟨1797467, by rfl⟩ : syracuseStep 2396623 = 3594935) B3594935
theorem B3195497 : Blo 2129435 3195497 := bstep (se 2 (by rfl) ⟨1198311, by rfl⟩ : syracuseStep 3195497 = 2396623) B2396623
theorem B2130331 : Blo 2129435 2130331 := bstep (se 1 (by rfl) ⟨1597748, by rfl⟩ : syracuseStep 2130331 = 3195497) B3195497
theorem B6824773 : Blo 2129435 6824773 := bbase (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) (by norm_num)
theorem B9099697 : Blo 2129435 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B12132929 : Blo 2129435 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B8088619 : Blo 2129435 8088619 := bstep (se 1 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 8088619 = 12132929) B12132929
theorem B10784825 : Blo 2129435 10784825 := bstep (se 2 (by rfl) ⟨4044309, by rfl⟩ : syracuseStep 10784825 = 8088619) B8088619
theorem B7189883 : Blo 2129435 7189883 := bstep (se 1 (by rfl) ⟨5392412, by rfl⟩ : syracuseStep 7189883 = 10784825) B10784825
theorem B4793255 : Blo 2129435 4793255 := bstep (se 1 (by rfl) ⟨3594941, by rfl⟩ : syracuseStep 4793255 = 7189883) B7189883
theorem B3195503 : Blo 2129435 3195503 := bstep (se 1 (by rfl) ⟨2396627, by rfl⟩ : syracuseStep 3195503 = 4793255) B4793255
theorem B2130335 : Blo 2129435 2130335 := bstep (se 1 (by rfl) ⟨1597751, by rfl⟩ : syracuseStep 2130335 = 3195503) B3195503
theorem B3195509 : Blo 2129435 3195509 := bbase (se 5 (by rfl) ⟨149789, by rfl⟩ : syracuseStep 3195509 = 299579) (by norm_num)
theorem B2130339 : Blo 2129435 2130339 := bstep (se 1 (by rfl) ⟨1597754, by rfl⟩ : syracuseStep 2130339 = 3195509) B3195509
theorem B4044325 : Blo 2129435 4044325 := bbase (se 4 (by rfl) ⟨379155, by rfl⟩ : syracuseStep 4044325 = 758311) (by norm_num)
theorem B5392433 : Blo 2129435 5392433 := bstep (se 2 (by rfl) ⟨2022162, by rfl⟩ : syracuseStep 5392433 = 4044325) B4044325
theorem B3594955 : Blo 2129435 3594955 := bstep (se 1 (by rfl) ⟨2696216, by rfl⟩ : syracuseStep 3594955 = 5392433) B5392433
theorem B4793273 : Blo 2129435 4793273 := bstep (se 2 (by rfl) ⟨1797477, by rfl⟩ : syracuseStep 4793273 = 3594955) B3594955
theorem B3195515 : Blo 2129435 3195515 := bstep (se 1 (by rfl) ⟨2396636, by rfl⟩ : syracuseStep 3195515 = 4793273) B4793273
theorem B2130343 : Blo 2129435 2130343 := bstep (se 1 (by rfl) ⟨1597757, by rfl⟩ : syracuseStep 2130343 = 3195515) B3195515
theorem B2396641 : Blo 2129435 2396641 := bbase (se 2 (by rfl) ⟨898740, by rfl⟩ : syracuseStep 2396641 = 1797481) (by norm_num)
theorem B3195521 : Blo 2129435 3195521 := bstep (se 2 (by rfl) ⟨1198320, by rfl⟩ : syracuseStep 3195521 = 2396641) B2396641
theorem B2130347 : Blo 2129435 2130347 := bstep (se 1 (by rfl) ⟨1597760, by rfl⟩ : syracuseStep 2130347 = 3195521) B3195521
theorem B5392453 : Blo 2129435 5392453 := bbase (se 4 (by rfl) ⟨505542, by rfl⟩ : syracuseStep 5392453 = 1011085) (by norm_num)
theorem B7189937 : Blo 2129435 7189937 := bstep (se 2 (by rfl) ⟨2696226, by rfl⟩ : syracuseStep 7189937 = 5392453) B5392453
theorem B4793291 : Blo 2129435 4793291 := bstep (se 1 (by rfl) ⟨3594968, by rfl⟩ : syracuseStep 4793291 = 7189937) B7189937
theorem B3195527 : Blo 2129435 3195527 := bstep (se 1 (by rfl) ⟨2396645, by rfl⟩ : syracuseStep 3195527 = 4793291) B4793291
theorem B2130351 : Blo 2129435 2130351 := bstep (se 1 (by rfl) ⟨1597763, by rfl⟩ : syracuseStep 2130351 = 3195527) B3195527
theorem B3195533 : Blo 2129435 3195533 := bbase (se 3 (by rfl) ⟨599162, by rfl⟩ : syracuseStep 3195533 = 1198325) (by norm_num)
theorem B2130355 : Blo 2129435 2130355 := bstep (se 1 (by rfl) ⟨1597766, by rfl⟩ : syracuseStep 2130355 = 3195533) B3195533
theorem B4793309 : Blo 2129435 4793309 := bbase (se 3 (by rfl) ⟨898745, by rfl⟩ : syracuseStep 4793309 = 1797491) (by norm_num)
theorem B3195539 : Blo 2129435 3195539 := bstep (se 1 (by rfl) ⟨2396654, by rfl⟩ : syracuseStep 3195539 = 4793309) B4793309
theorem B2130359 : Blo 2129435 2130359 := bstep (se 1 (by rfl) ⟨1597769, by rfl⟩ : syracuseStep 2130359 = 3195539) B3195539
theorem B3594989 : Blo 2129435 3594989 := bbase (se 3 (by rfl) ⟨674060, by rfl⟩ : syracuseStep 3594989 = 1348121) (by norm_num)
theorem B2396659 : Blo 2129435 2396659 := bstep (se 1 (by rfl) ⟨1797494, by rfl⟩ : syracuseStep 2396659 = 3594989) B3594989
theorem B3195545 : Blo 2129435 3195545 := bstep (se 2 (by rfl) ⟨1198329, by rfl⟩ : syracuseStep 3195545 = 2396659) B2396659
theorem B2130363 : Blo 2129435 2130363 := bstep (se 1 (by rfl) ⟨1597772, by rfl⟩ : syracuseStep 2130363 = 3195545) B3195545
theorem B3644045 : Blo 2129435 3644045 := bbase (se 3 (by rfl) ⟨683258, by rfl⟩ : syracuseStep 3644045 = 1366517) (by norm_num)
theorem B2429363 : Blo 2129435 2429363 := bstep (se 1 (by rfl) ⟨1822022, by rfl⟩ : syracuseStep 2429363 = 3644045) B3644045
theorem B6478301 : Blo 2129435 6478301 := bstep (se 3 (by rfl) ⟨1214681, by rfl⟩ : syracuseStep 6478301 = 2429363) B2429363
theorem B4318867 : Blo 2129435 4318867 := bstep (se 1 (by rfl) ⟨3239150, by rfl⟩ : syracuseStep 4318867 = 6478301) B6478301
theorem B5758489 : Blo 2129435 5758489 := bstep (se 2 (by rfl) ⟨2159433, by rfl⟩ : syracuseStep 5758489 = 4318867) B4318867
theorem B7677985 : Blo 2129435 7677985 := bstep (se 2 (by rfl) ⟨2879244, by rfl⟩ : syracuseStep 7677985 = 5758489) B5758489
theorem B10237313 : Blo 2129435 10237313 := bstep (se 2 (by rfl) ⟨3838992, by rfl⟩ : syracuseStep 10237313 = 7677985) B7677985
theorem B27299501 : Blo 2129435 27299501 := bstep (se 3 (by rfl) ⟨5118656, by rfl⟩ : syracuseStep 27299501 = 10237313) B10237313
theorem B18199667 : Blo 2129435 18199667 := bstep (se 1 (by rfl) ⟨13649750, by rfl⟩ : syracuseStep 18199667 = 27299501) B27299501
theorem B12133111 : Blo 2129435 12133111 := bstep (se 1 (by rfl) ⟨9099833, by rfl⟩ : syracuseStep 12133111 = 18199667) B18199667
theorem B16177481 : Blo 2129435 16177481 := bstep (se 2 (by rfl) ⟨6066555, by rfl⟩ : syracuseStep 16177481 = 12133111) B12133111
theorem B10784987 : Blo 2129435 10784987 := bstep (se 1 (by rfl) ⟨8088740, by rfl⟩ : syracuseStep 10784987 = 16177481) B16177481
theorem B7189991 : Blo 2129435 7189991 := bstep (se 1 (by rfl) ⟨5392493, by rfl⟩ : syracuseStep 7189991 = 10784987) B10784987
theorem B4793327 : Blo 2129435 4793327 := bstep (se 1 (by rfl) ⟨3594995, by rfl⟩ : syracuseStep 4793327 = 7189991) B7189991
theorem B3195551 : Blo 2129435 3195551 := bstep (se 1 (by rfl) ⟨2396663, by rfl⟩ : syracuseStep 3195551 = 4793327) B4793327
theorem B2130367 : Blo 2129435 2130367 := bstep (se 1 (by rfl) ⟨1597775, by rfl⟩ : syracuseStep 2130367 = 3195551) B3195551
theorem B3195557 : Blo 2129435 3195557 := bbase (se 4 (by rfl) ⟨299583, by rfl⟩ : syracuseStep 3195557 = 599167) (by norm_num)
theorem B2130371 : Blo 2129435 2130371 := bstep (se 1 (by rfl) ⟨1597778, by rfl⟩ : syracuseStep 2130371 = 3195557) B3195557
theorem B2696257 : Blo 2129435 2696257 := bbase (se 2 (by rfl) ⟨1011096, by rfl⟩ : syracuseStep 2696257 = 2022193) (by norm_num)
theorem B3595009 : Blo 2129435 3595009 := bstep (se 2 (by rfl) ⟨1348128, by rfl⟩ : syracuseStep 3595009 = 2696257) B2696257
theorem B4793345 : Blo 2129435 4793345 := bstep (se 2 (by rfl) ⟨1797504, by rfl⟩ : syracuseStep 4793345 = 3595009) B3595009
theorem B3195563 : Blo 2129435 3195563 := bstep (se 1 (by rfl) ⟨2396672, by rfl⟩ : syracuseStep 3195563 = 4793345) B4793345
theorem B2130375 : Blo 2129435 2130375 := bstep (se 1 (by rfl) ⟨1597781, by rfl⟩ : syracuseStep 2130375 = 3195563) B3195563
theorem B2396677 : Blo 2129435 2396677 := bbase (se 4 (by rfl) ⟨224688, by rfl⟩ : syracuseStep 2396677 = 449377) (by norm_num)
theorem B3195569 : Blo 2129435 3195569 := bstep (se 2 (by rfl) ⟨1198338, by rfl⟩ : syracuseStep 3195569 = 2396677) B2396677
theorem B2130379 : Blo 2129435 2130379 := bstep (se 1 (by rfl) ⟨1597784, by rfl⟩ : syracuseStep 2130379 = 3195569) B3195569
theorem B3033301 : Blo 2129435 3033301 := bbase (se 7 (by rfl) ⟨35546, by rfl⟩ : syracuseStep 3033301 = 71093) (by norm_num)
theorem B4044401 : Blo 2129435 4044401 := bstep (se 2 (by rfl) ⟨1516650, by rfl⟩ : syracuseStep 4044401 = 3033301) B3033301
theorem B2696267 : Blo 2129435 2696267 := bstep (se 1 (by rfl) ⟨2022200, by rfl⟩ : syracuseStep 2696267 = 4044401) B4044401
theorem B7190045 : Blo 2129435 7190045 := bstep (se 3 (by rfl) ⟨1348133, by rfl⟩ : syracuseStep 7190045 = 2696267) B2696267
theorem B4793363 : Blo 2129435 4793363 := bstep (se 1 (by rfl) ⟨3595022, by rfl⟩ : syracuseStep 4793363 = 7190045) B7190045
theorem B3195575 : Blo 2129435 3195575 := bstep (se 1 (by rfl) ⟨2396681, by rfl⟩ : syracuseStep 3195575 = 4793363) B4793363
theorem B2130383 : Blo 2129435 2130383 := bstep (se 1 (by rfl) ⟨1597787, by rfl⟩ : syracuseStep 2130383 = 3195575) B3195575
theorem B3195581 : Blo 2129435 3195581 := bbase (se 3 (by rfl) ⟨599171, by rfl⟩ : syracuseStep 3195581 = 1198343) (by norm_num)
theorem B2130387 : Blo 2129435 2130387 := bstep (se 1 (by rfl) ⟨1597790, by rfl⟩ : syracuseStep 2130387 = 3195581) B3195581
theorem B4793381 : Blo 2129435 4793381 := bbase (se 4 (by rfl) ⟨449379, by rfl⟩ : syracuseStep 4793381 = 898759) (by norm_num)
theorem B3195587 : Blo 2129435 3195587 := bstep (se 1 (by rfl) ⟨2396690, by rfl⟩ : syracuseStep 3195587 = 4793381) B4793381
theorem B2130391 : Blo 2129435 2130391 := bstep (se 1 (by rfl) ⟨1597793, by rfl⟩ : syracuseStep 2130391 = 3195587) B3195587
theorem B5392565 : Blo 2129435 5392565 := bbase (se 5 (by rfl) ⟨252776, by rfl⟩ : syracuseStep 5392565 = 505553) (by norm_num)
theorem B3595043 : Blo 2129435 3595043 := bstep (se 1 (by rfl) ⟨2696282, by rfl⟩ : syracuseStep 3595043 = 5392565) B5392565
theorem B2396695 : Blo 2129435 2396695 := bstep (se 1 (by rfl) ⟨1797521, by rfl⟩ : syracuseStep 2396695 = 3595043) B3595043
theorem B3195593 : Blo 2129435 3195593 := bstep (se 2 (by rfl) ⟨1198347, by rfl⟩ : syracuseStep 3195593 = 2396695) B2396695
theorem B2130395 : Blo 2129435 2130395 := bstep (se 1 (by rfl) ⟨1597796, by rfl⟩ : syracuseStep 2130395 = 3195593) B3195593
theorem B4318933 : Blo 2129435 4318933 := bbase (se 7 (by rfl) ⟨50612, by rfl⟩ : syracuseStep 4318933 = 101225) (by norm_num)
theorem B5758577 : Blo 2129435 5758577 := bstep (se 2 (by rfl) ⟨2159466, by rfl⟩ : syracuseStep 5758577 = 4318933) B4318933
theorem B3839051 : Blo 2129435 3839051 := bstep (se 1 (by rfl) ⟨2879288, by rfl⟩ : syracuseStep 3839051 = 5758577) B5758577
theorem B2559367 : Blo 2129435 2559367 := bstep (se 1 (by rfl) ⟨1919525, by rfl⟩ : syracuseStep 2559367 = 3839051) B3839051
theorem B13649957 : Blo 2129435 13649957 := bstep (se 4 (by rfl) ⟨1279683, by rfl⟩ : syracuseStep 13649957 = 2559367) B2559367
theorem B9099971 : Blo 2129435 9099971 := bstep (se 1 (by rfl) ⟨6824978, by rfl⟩ : syracuseStep 9099971 = 13649957) B13649957
theorem B6066647 : Blo 2129435 6066647 := bstep (se 1 (by rfl) ⟨4549985, by rfl⟩ : syracuseStep 6066647 = 9099971) B9099971
theorem B4044431 : Blo 2129435 4044431 := bstep (se 1 (by rfl) ⟨3033323, by rfl⟩ : syracuseStep 4044431 = 6066647) B6066647
theorem B10785149 : Blo 2129435 10785149 := bstep (se 3 (by rfl) ⟨2022215, by rfl⟩ : syracuseStep 10785149 = 4044431) B4044431
theorem B7190099 : Blo 2129435 7190099 := bstep (se 1 (by rfl) ⟨5392574, by rfl⟩ : syracuseStep 7190099 = 10785149) B10785149
theorem B4793399 : Blo 2129435 4793399 := bstep (se 1 (by rfl) ⟨3595049, by rfl⟩ : syracuseStep 4793399 = 7190099) B7190099
theorem B3195599 : Blo 2129435 3195599 := bstep (se 1 (by rfl) ⟨2396699, by rfl⟩ : syracuseStep 3195599 = 4793399) B4793399
theorem B2130399 : Blo 2129435 2130399 := bstep (se 1 (by rfl) ⟨1597799, by rfl⟩ : syracuseStep 2130399 = 3195599) B3195599
theorem B3195605 : Blo 2129435 3195605 := bbase (se 7 (by rfl) ⟨37448, by rfl⟩ : syracuseStep 3195605 = 74897) (by norm_num)
theorem B2130403 : Blo 2129435 2130403 := bstep (se 1 (by rfl) ⟨1597802, by rfl⟩ : syracuseStep 2130403 = 3195605) B3195605
theorem B2559377 : Blo 2129435 2559377 := bbase (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) (by norm_num)
theorem B6825005 : Blo 2129435 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B4550003 : Blo 2129435 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B3033335 : Blo 2129435 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B8088893 : Blo 2129435 8088893 := bstep (se 3 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 8088893 = 3033335) B3033335
theorem B5392595 : Blo 2129435 5392595 := bstep (se 1 (by rfl) ⟨4044446, by rfl⟩ : syracuseStep 5392595 = 8088893) B8088893
theorem B3595063 : Blo 2129435 3595063 := bstep (se 1 (by rfl) ⟨2696297, by rfl⟩ : syracuseStep 3595063 = 5392595) B5392595
theorem B4793417 : Blo 2129435 4793417 := bstep (se 2 (by rfl) ⟨1797531, by rfl⟩ : syracuseStep 4793417 = 3595063) B3595063
theorem B3195611 : Blo 2129435 3195611 := bstep (se 1 (by rfl) ⟨2396708, by rfl⟩ : syracuseStep 3195611 = 4793417) B4793417
theorem B2130407 : Blo 2129435 2130407 := bstep (se 1 (by rfl) ⟨1597805, by rfl⟩ : syracuseStep 2130407 = 3195611) B3195611
theorem B2396713 : Blo 2129435 2396713 := bbase (se 2 (by rfl) ⟨898767, by rfl⟩ : syracuseStep 2396713 = 1797535) (by norm_num)
theorem B3195617 : Blo 2129435 3195617 := bstep (se 2 (by rfl) ⟨1198356, by rfl⟩ : syracuseStep 3195617 = 2396713) B2396713
theorem B2130411 : Blo 2129435 2130411 := bstep (se 1 (by rfl) ⟨1597808, by rfl⟩ : syracuseStep 2130411 = 3195617) B3195617
theorem B8755781 : Blo 2129435 8755781 := bbase (se 4 (by rfl) ⟨820854, by rfl⟩ : syracuseStep 8755781 = 1641709) (by norm_num)
theorem B23348749 : Blo 2129435 23348749 := bstep (se 3 (by rfl) ⟨4377890, by rfl⟩ : syracuseStep 23348749 = 8755781) B8755781
theorem B31131665 : Blo 2129435 31131665 := bstep (se 2 (by rfl) ⟨11674374, by rfl⟩ : syracuseStep 31131665 = 23348749) B23348749
theorem B20754443 : Blo 2129435 20754443 := bstep (se 1 (by rfl) ⟨15565832, by rfl⟩ : syracuseStep 20754443 = 31131665) B31131665
theorem B13836295 : Blo 2129435 13836295 := bstep (se 1 (by rfl) ⟨10377221, by rfl⟩ : syracuseStep 13836295 = 20754443) B20754443
theorem B18448393 : Blo 2129435 18448393 := bstep (se 2 (by rfl) ⟨6918147, by rfl⟩ : syracuseStep 18448393 = 13836295) B13836295
theorem B24597857 : Blo 2129435 24597857 := bstep (se 2 (by rfl) ⟨9224196, by rfl⟩ : syracuseStep 24597857 = 18448393) B18448393
theorem B16398571 : Blo 2129435 16398571 := bstep (se 1 (by rfl) ⟨12298928, by rfl⟩ : syracuseStep 16398571 = 24597857) B24597857
theorem B21864761 : Blo 2129435 21864761 := bstep (se 2 (by rfl) ⟨8199285, by rfl⟩ : syracuseStep 21864761 = 16398571) B16398571
theorem B14576507 : Blo 2129435 14576507 := bstep (se 1 (by rfl) ⟨10932380, by rfl⟩ : syracuseStep 14576507 = 21864761) B21864761
theorem B9717671 : Blo 2129435 9717671 := bstep (se 1 (by rfl) ⟨7288253, by rfl⟩ : syracuseStep 9717671 = 14576507) B14576507
theorem B6478447 : Blo 2129435 6478447 := bstep (se 1 (by rfl) ⟨4858835, by rfl⟩ : syracuseStep 6478447 = 9717671) B9717671
theorem B8637929 : Blo 2129435 8637929 := bstep (se 2 (by rfl) ⟨3239223, by rfl⟩ : syracuseStep 8637929 = 6478447) B6478447
theorem B5758619 : Blo 2129435 5758619 := bstep (se 1 (by rfl) ⟨4318964, by rfl⟩ : syracuseStep 5758619 = 8637929) B8637929
theorem B15356317 : Blo 2129435 15356317 := bstep (se 3 (by rfl) ⟨2879309, by rfl⟩ : syracuseStep 15356317 = 5758619) B5758619
theorem B20475089 : Blo 2129435 20475089 := bstep (se 2 (by rfl) ⟨7678158, by rfl⟩ : syracuseStep 20475089 = 15356317) B15356317
theorem B13650059 : Blo 2129435 13650059 := bstep (se 1 (by rfl) ⟨10237544, by rfl⟩ : syracuseStep 13650059 = 20475089) B20475089
theorem B9100039 : Blo 2129435 9100039 := bstep (se 1 (by rfl) ⟨6825029, by rfl⟩ : syracuseStep 9100039 = 13650059) B13650059
theorem B12133385 : Blo 2129435 12133385 := bstep (se 2 (by rfl) ⟨4550019, by rfl⟩ : syracuseStep 12133385 = 9100039) B9100039
theorem B8088923 : Blo 2129435 8088923 := bstep (se 1 (by rfl) ⟨6066692, by rfl⟩ : syracuseStep 8088923 = 12133385) B12133385
theorem B5392615 : Blo 2129435 5392615 := bstep (se 1 (by rfl) ⟨4044461, by rfl⟩ : syracuseStep 5392615 = 8088923) B8088923
theorem B7190153 : Blo 2129435 7190153 := bstep (se 2 (by rfl) ⟨2696307, by rfl⟩ : syracuseStep 7190153 = 5392615) B5392615
theorem B4793435 : Blo 2129435 4793435 := bstep (se 1 (by rfl) ⟨3595076, by rfl⟩ : syracuseStep 4793435 = 7190153) B7190153
theorem B3195623 : Blo 2129435 3195623 := bstep (se 1 (by rfl) ⟨2396717, by rfl⟩ : syracuseStep 3195623 = 4793435) B4793435
theorem B2130415 : Blo 2129435 2130415 := bstep (se 1 (by rfl) ⟨1597811, by rfl⟩ : syracuseStep 2130415 = 3195623) B3195623
theorem B3195629 : Blo 2129435 3195629 := bbase (se 3 (by rfl) ⟨599180, by rfl⟩ : syracuseStep 3195629 = 1198361) (by norm_num)
theorem B2130419 : Blo 2129435 2130419 := bstep (se 1 (by rfl) ⟨1597814, by rfl⟩ : syracuseStep 2130419 = 3195629) B3195629
theorem B4793453 : Blo 2129435 4793453 := bbase (se 3 (by rfl) ⟨898772, by rfl⟩ : syracuseStep 4793453 = 1797545) (by norm_num)
theorem B3195635 : Blo 2129435 3195635 := bstep (se 1 (by rfl) ⟨2396726, by rfl⟩ : syracuseStep 3195635 = 4793453) B4793453
theorem B2130423 : Blo 2129435 2130423 := bstep (se 1 (by rfl) ⟨1597817, by rfl⟩ : syracuseStep 2130423 = 3195635) B3195635
theorem B4044485 : Blo 2129435 4044485 := bbase (se 4 (by rfl) ⟨379170, by rfl⟩ : syracuseStep 4044485 = 758341) (by norm_num)
theorem B2696323 : Blo 2129435 2696323 := bstep (se 1 (by rfl) ⟨2022242, by rfl⟩ : syracuseStep 2696323 = 4044485) B4044485
theorem B3595097 : Blo 2129435 3595097 := bstep (se 2 (by rfl) ⟨1348161, by rfl⟩ : syracuseStep 3595097 = 2696323) B2696323
theorem B2396731 : Blo 2129435 2396731 := bstep (se 1 (by rfl) ⟨1797548, by rfl⟩ : syracuseStep 2396731 = 3595097) B3595097
theorem B3195641 : Blo 2129435 3195641 := bstep (se 2 (by rfl) ⟨1198365, by rfl⟩ : syracuseStep 3195641 = 2396731) B2396731
theorem B2130427 : Blo 2129435 2130427 := bstep (se 1 (by rfl) ⟨1597820, by rfl⟩ : syracuseStep 2130427 = 3195641) B3195641
theorem B4612133 : Blo 2129435 4612133 := bbase (se 4 (by rfl) ⟨432387, by rfl⟩ : syracuseStep 4612133 = 864775) (by norm_num)
theorem B3074755 : Blo 2129435 3074755 := bstep (se 1 (by rfl) ⟨2306066, by rfl⟩ : syracuseStep 3074755 = 4612133) B4612133
theorem B4099673 : Blo 2129435 4099673 := bstep (se 2 (by rfl) ⟨1537377, by rfl⟩ : syracuseStep 4099673 = 3074755) B3074755
theorem B10932461 : Blo 2129435 10932461 := bstep (se 3 (by rfl) ⟨2049836, by rfl⟩ : syracuseStep 10932461 = 4099673) B4099673
theorem B7288307 : Blo 2129435 7288307 := bstep (se 1 (by rfl) ⟨5466230, by rfl⟩ : syracuseStep 7288307 = 10932461) B10932461
theorem B4858871 : Blo 2129435 4858871 := bstep (se 1 (by rfl) ⟨3644153, by rfl⟩ : syracuseStep 4858871 = 7288307) B7288307
theorem B12956989 : Blo 2129435 12956989 := bstep (se 3 (by rfl) ⟨2429435, by rfl⟩ : syracuseStep 12956989 = 4858871) B4858871
theorem B17275985 : Blo 2129435 17275985 := bstep (se 2 (by rfl) ⟨6478494, by rfl⟩ : syracuseStep 17275985 = 12956989) B12956989
theorem B11517323 : Blo 2129435 11517323 := bstep (se 1 (by rfl) ⟨8637992, by rfl⟩ : syracuseStep 11517323 = 17275985) B17275985
theorem B30712861 : Blo 2129435 30712861 := bstep (se 3 (by rfl) ⟨5758661, by rfl⟩ : syracuseStep 30712861 = 11517323) B11517323
theorem B40950481 : Blo 2129435 40950481 := bstep (se 2 (by rfl) ⟨15356430, by rfl⟩ : syracuseStep 40950481 = 30712861) B30712861
theorem B54600641 : Blo 2129435 54600641 := bstep (se 2 (by rfl) ⟨20475240, by rfl⟩ : syracuseStep 54600641 = 40950481) B40950481
theorem B36400427 : Blo 2129435 36400427 := bstep (se 1 (by rfl) ⟨27300320, by rfl⟩ : syracuseStep 36400427 = 54600641) B54600641
theorem B24266951 : Blo 2129435 24266951 := bstep (se 1 (by rfl) ⟨18200213, by rfl⟩ : syracuseStep 24266951 = 36400427) B36400427
theorem B16177967 : Blo 2129435 16177967 := bstep (se 1 (by rfl) ⟨12133475, by rfl⟩ : syracuseStep 16177967 = 24266951) B24266951
theorem B10785311 : Blo 2129435 10785311 := bstep (se 1 (by rfl) ⟨8088983, by rfl⟩ : syracuseStep 10785311 = 16177967) B16177967
theorem B7190207 : Blo 2129435 7190207 := bstep (se 1 (by rfl) ⟨5392655, by rfl⟩ : syracuseStep 7190207 = 10785311) B10785311
theorem B4793471 : Blo 2129435 4793471 := bstep (se 1 (by rfl) ⟨3595103, by rfl⟩ : syracuseStep 4793471 = 7190207) B7190207
theorem B3195647 : Blo 2129435 3195647 := bstep (se 1 (by rfl) ⟨2396735, by rfl⟩ : syracuseStep 3195647 = 4793471) B4793471
theorem B2130431 : Blo 2129435 2130431 := bstep (se 1 (by rfl) ⟨1597823, by rfl⟩ : syracuseStep 2130431 = 3195647) B3195647
theorem B3195653 : Blo 2129435 3195653 := bbase (se 4 (by rfl) ⟨299592, by rfl⟩ : syracuseStep 3195653 = 599185) (by norm_num)
theorem B2130435 : Blo 2129435 2130435 := bstep (se 1 (by rfl) ⟨1597826, by rfl⟩ : syracuseStep 2130435 = 3195653) B3195653
theorem B3595117 : Blo 2129435 3595117 := bbase (se 3 (by rfl) ⟨674084, by rfl⟩ : syracuseStep 3595117 = 1348169) (by norm_num)
theorem B4793489 : Blo 2129435 4793489 := bstep (se 2 (by rfl) ⟨1797558, by rfl⟩ : syracuseStep 4793489 = 3595117) B3595117
theorem B3195659 : Blo 2129435 3195659 := bstep (se 1 (by rfl) ⟨2396744, by rfl⟩ : syracuseStep 3195659 = 4793489) B4793489
theorem B2130439 : Blo 2129435 2130439 := bstep (se 1 (by rfl) ⟨1597829, by rfl⟩ : syracuseStep 2130439 = 3195659) B3195659
theorem B2396749 : Blo 2129435 2396749 := bbase (se 3 (by rfl) ⟨449390, by rfl⟩ : syracuseStep 2396749 = 898781) (by norm_num)
theorem B3195665 : Blo 2129435 3195665 := bstep (se 2 (by rfl) ⟨1198374, by rfl⟩ : syracuseStep 3195665 = 2396749) B2396749
theorem B2130443 : Blo 2129435 2130443 := bstep (se 1 (by rfl) ⟨1597832, by rfl⟩ : syracuseStep 2130443 = 3195665) B3195665
theorem B7190261 : Blo 2129435 7190261 := bbase (se 5 (by rfl) ⟨337043, by rfl⟩ : syracuseStep 7190261 = 674087) (by norm_num)
theorem B4793507 : Blo 2129435 4793507 := bstep (se 1 (by rfl) ⟨3595130, by rfl⟩ : syracuseStep 4793507 = 7190261) B7190261
theorem B3195671 : Blo 2129435 3195671 := bstep (se 1 (by rfl) ⟨2396753, by rfl⟩ : syracuseStep 3195671 = 4793507) B4793507
theorem B2130447 : Blo 2129435 2130447 := bstep (se 1 (by rfl) ⟨1597835, by rfl⟩ : syracuseStep 2130447 = 3195671) B3195671
theorem B3195677 : Blo 2129435 3195677 := bbase (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) (by norm_num)
theorem B2130451 : Blo 2129435 2130451 := bstep (se 1 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 2130451 = 3195677) B3195677
theorem B4793525 : Blo 2129435 4793525 := bbase (se 5 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 4793525 = 449393) (by norm_num)
theorem B3195683 : Blo 2129435 3195683 := bstep (se 1 (by rfl) ⟨2396762, by rfl⟩ : syracuseStep 3195683 = 4793525) B4793525
theorem B2130455 : Blo 2129435 2130455 := bstep (se 1 (by rfl) ⟨1597841, by rfl⟩ : syracuseStep 2130455 = 3195683) B3195683
theorem B2275057 : Blo 2129435 2275057 := bbase (se 2 (by rfl) ⟨853146, by rfl⟩ : syracuseStep 2275057 = 1706293) (by norm_num)
theorem B12133637 : Blo 2129435 12133637 := bstep (se 4 (by rfl) ⟨1137528, by rfl⟩ : syracuseStep 12133637 = 2275057) B2275057
theorem B8089091 : Blo 2129435 8089091 := bstep (se 1 (by rfl) ⟨6066818, by rfl⟩ : syracuseStep 8089091 = 12133637) B12133637
theorem B5392727 : Blo 2129435 5392727 := bstep (se 1 (by rfl) ⟨4044545, by rfl⟩ : syracuseStep 5392727 = 8089091) B8089091
theorem B3595151 : Blo 2129435 3595151 := bstep (se 1 (by rfl) ⟨2696363, by rfl⟩ : syracuseStep 3595151 = 5392727) B5392727
theorem B2396767 : Blo 2129435 2396767 := bstep (se 1 (by rfl) ⟨1797575, by rfl⟩ : syracuseStep 2396767 = 3595151) B3595151
theorem B3195689 : Blo 2129435 3195689 := bstep (se 2 (by rfl) ⟨1198383, by rfl⟩ : syracuseStep 3195689 = 2396767) B2396767
theorem B2130459 : Blo 2129435 2130459 := bstep (se 1 (by rfl) ⟨1597844, by rfl⟩ : syracuseStep 2130459 = 3195689) B3195689
theorem B2275061 : Blo 2129435 2275061 := bbase (se 5 (by rfl) ⟨106643, by rfl⟩ : syracuseStep 2275061 = 213287) (by norm_num)
theorem B6066829 : Blo 2129435 6066829 := bstep (se 3 (by rfl) ⟨1137530, by rfl⟩ : syracuseStep 6066829 = 2275061) B2275061
theorem B8089105 : Blo 2129435 8089105 := bstep (se 2 (by rfl) ⟨3033414, by rfl⟩ : syracuseStep 8089105 = 6066829) B6066829
theorem B10785473 : Blo 2129435 10785473 := bstep (se 2 (by rfl) ⟨4044552, by rfl⟩ : syracuseStep 10785473 = 8089105) B8089105
theorem B7190315 : Blo 2129435 7190315 := bstep (se 1 (by rfl) ⟨5392736, by rfl⟩ : syracuseStep 7190315 = 10785473) B10785473
theorem B4793543 : Blo 2129435 4793543 := bstep (se 1 (by rfl) ⟨3595157, by rfl⟩ : syracuseStep 4793543 = 7190315) B7190315
theorem B3195695 : Blo 2129435 3195695 := bstep (se 1 (by rfl) ⟨2396771, by rfl⟩ : syracuseStep 3195695 = 4793543) B4793543
theorem B2130463 : Blo 2129435 2130463 := bstep (se 1 (by rfl) ⟨1597847, by rfl⟩ : syracuseStep 2130463 = 3195695) B3195695
theorem B3195701 : Blo 2129435 3195701 := bbase (se 5 (by rfl) ⟨149798, by rfl⟩ : syracuseStep 3195701 = 299597) (by norm_num)
theorem B2130467 : Blo 2129435 2130467 := bstep (se 1 (by rfl) ⟨1597850, by rfl⟩ : syracuseStep 2130467 = 3195701) B3195701
theorem B5392757 : Blo 2129435 5392757 := bbase (se 5 (by rfl) ⟨252785, by rfl⟩ : syracuseStep 5392757 = 505571) (by norm_num)
theorem B3595171 : Blo 2129435 3595171 := bstep (se 1 (by rfl) ⟨2696378, by rfl⟩ : syracuseStep 3595171 = 5392757) B5392757
theorem B4793561 : Blo 2129435 4793561 := bstep (se 2 (by rfl) ⟨1797585, by rfl⟩ : syracuseStep 4793561 = 3595171) B3595171
theorem B3195707 : Blo 2129435 3195707 := bstep (se 1 (by rfl) ⟨2396780, by rfl⟩ : syracuseStep 3195707 = 4793561) B4793561
theorem B2130471 : Blo 2129435 2130471 := bstep (se 1 (by rfl) ⟨1597853, by rfl⟩ : syracuseStep 2130471 = 3195707) B3195707
theorem B2396785 : Blo 2129435 2396785 := bbase (se 2 (by rfl) ⟨898794, by rfl⟩ : syracuseStep 2396785 = 1797589) (by norm_num)
theorem B3195713 : Blo 2129435 3195713 := bstep (se 2 (by rfl) ⟨1198392, by rfl⟩ : syracuseStep 3195713 = 2396785) B2396785
theorem B2130475 : Blo 2129435 2130475 := bstep (se 1 (by rfl) ⟨1597856, by rfl⟩ : syracuseStep 2130475 = 3195713) B3195713
theorem B3644237 : Blo 2129435 3644237 := bbase (se 3 (by rfl) ⟨683294, by rfl⟩ : syracuseStep 3644237 = 1366589) (by norm_num)
theorem B9717965 : Blo 2129435 9717965 := bstep (se 3 (by rfl) ⟨1822118, by rfl⟩ : syracuseStep 9717965 = 3644237) B3644237
theorem B6478643 : Blo 2129435 6478643 := bstep (se 1 (by rfl) ⟨4858982, by rfl⟩ : syracuseStep 6478643 = 9717965) B9717965
theorem B4319095 : Blo 2129435 4319095 := bstep (se 1 (by rfl) ⟨3239321, by rfl⟩ : syracuseStep 4319095 = 6478643) B6478643
theorem B5758793 : Blo 2129435 5758793 := bstep (se 2 (by rfl) ⟨2159547, by rfl⟩ : syracuseStep 5758793 = 4319095) B4319095
theorem B3839195 : Blo 2129435 3839195 := bstep (se 1 (by rfl) ⟨2879396, by rfl⟩ : syracuseStep 3839195 = 5758793) B5758793
theorem B10237853 : Blo 2129435 10237853 := bstep (se 3 (by rfl) ⟨1919597, by rfl⟩ : syracuseStep 10237853 = 3839195) B3839195
theorem B6825235 : Blo 2129435 6825235 := bstep (se 1 (by rfl) ⟨5118926, by rfl⟩ : syracuseStep 6825235 = 10237853) B10237853
theorem B9100313 : Blo 2129435 9100313 := bstep (se 2 (by rfl) ⟨3412617, by rfl⟩ : syracuseStep 9100313 = 6825235) B6825235
theorem B6066875 : Blo 2129435 6066875 := bstep (se 1 (by rfl) ⟨4550156, by rfl⟩ : syracuseStep 6066875 = 9100313) B9100313
theorem B4044583 : Blo 2129435 4044583 := bstep (se 1 (by rfl) ⟨3033437, by rfl⟩ : syracuseStep 4044583 = 6066875) B6066875
theorem B5392777 : Blo 2129435 5392777 := bstep (se 2 (by rfl) ⟨2022291, by rfl⟩ : syracuseStep 5392777 = 4044583) B4044583
theorem B7190369 : Blo 2129435 7190369 := bstep (se 2 (by rfl) ⟨2696388, by rfl⟩ : syracuseStep 7190369 = 5392777) B5392777
theorem B4793579 : Blo 2129435 4793579 := bstep (se 1 (by rfl) ⟨3595184, by rfl⟩ : syracuseStep 4793579 = 7190369) B7190369
theorem B3195719 : Blo 2129435 3195719 := bstep (se 1 (by rfl) ⟨2396789, by rfl⟩ : syracuseStep 3195719 = 4793579) B4793579
theorem B2130479 : Blo 2129435 2130479 := bstep (se 1 (by rfl) ⟨1597859, by rfl⟩ : syracuseStep 2130479 = 3195719) B3195719
theorem B3195725 : Blo 2129435 3195725 := bbase (se 3 (by rfl) ⟨599198, by rfl⟩ : syracuseStep 3195725 = 1198397) (by norm_num)
theorem B2130483 : Blo 2129435 2130483 := bstep (se 1 (by rfl) ⟨1597862, by rfl⟩ : syracuseStep 2130483 = 3195725) B3195725
theorem B4793597 : Blo 2129435 4793597 := bbase (se 3 (by rfl) ⟨898799, by rfl⟩ : syracuseStep 4793597 = 1797599) (by norm_num)
theorem B3195731 : Blo 2129435 3195731 := bstep (se 1 (by rfl) ⟨2396798, by rfl⟩ : syracuseStep 3195731 = 4793597) B4793597
theorem B2130487 : Blo 2129435 2130487 := bstep (se 1 (by rfl) ⟨1597865, by rfl⟩ : syracuseStep 2130487 = 3195731) B3195731
theorem B3595205 : Blo 2129435 3595205 := bbase (se 4 (by rfl) ⟨337050, by rfl⟩ : syracuseStep 3595205 = 674101) (by norm_num)
theorem B2396803 : Blo 2129435 2396803 := bstep (se 1 (by rfl) ⟨1797602, by rfl⟩ : syracuseStep 2396803 = 3595205) B3595205
theorem B3195737 : Blo 2129435 3195737 := bstep (se 2 (by rfl) ⟨1198401, by rfl⟩ : syracuseStep 3195737 = 2396803) B2396803
theorem B2130491 : Blo 2129435 2130491 := bstep (se 1 (by rfl) ⟨1597868, by rfl⟩ : syracuseStep 2130491 = 3195737) B3195737
theorem B16178453 : Blo 2129435 16178453 := bbase (se 6 (by rfl) ⟨379182, by rfl⟩ : syracuseStep 16178453 = 758365) (by norm_num)
theorem B10785635 : Blo 2129435 10785635 := bstep (se 1 (by rfl) ⟨8089226, by rfl⟩ : syracuseStep 10785635 = 16178453) B16178453
theorem B7190423 : Blo 2129435 7190423 := bstep (se 1 (by rfl) ⟨5392817, by rfl⟩ : syracuseStep 7190423 = 10785635) B10785635
theorem B4793615 : Blo 2129435 4793615 := bstep (se 1 (by rfl) ⟨3595211, by rfl⟩ : syracuseStep 4793615 = 7190423) B7190423
theorem B3195743 : Blo 2129435 3195743 := bstep (se 1 (by rfl) ⟨2396807, by rfl⟩ : syracuseStep 3195743 = 4793615) B4793615
theorem B2130495 : Blo 2129435 2130495 := bstep (se 1 (by rfl) ⟨1597871, by rfl⟩ : syracuseStep 2130495 = 3195743) B3195743
theorem B3195749 : Blo 2129435 3195749 := bbase (se 4 (by rfl) ⟨299601, by rfl⟩ : syracuseStep 3195749 = 599203) (by norm_num)
theorem B2130499 : Blo 2129435 2130499 := bstep (se 1 (by rfl) ⟨1597874, by rfl⟩ : syracuseStep 2130499 = 3195749) B3195749
theorem B4044629 : Blo 2129435 4044629 := bbase (se 9 (by rfl) ⟨11849, by rfl⟩ : syracuseStep 4044629 = 23699) (by norm_num)
theorem B2696419 : Blo 2129435 2696419 := bstep (se 1 (by rfl) ⟨2022314, by rfl⟩ : syracuseStep 2696419 = 4044629) B4044629
theorem B3595225 : Blo 2129435 3595225 := bstep (se 2 (by rfl) ⟨1348209, by rfl⟩ : syracuseStep 3595225 = 2696419) B2696419
theorem B4793633 : Blo 2129435 4793633 := bstep (se 2 (by rfl) ⟨1797612, by rfl⟩ : syracuseStep 4793633 = 3595225) B3595225
theorem B3195755 : Blo 2129435 3195755 := bstep (se 1 (by rfl) ⟨2396816, by rfl⟩ : syracuseStep 3195755 = 4793633) B4793633
theorem B2130503 : Blo 2129435 2130503 := bstep (se 1 (by rfl) ⟨1597877, by rfl⟩ : syracuseStep 2130503 = 3195755) B3195755
theorem B2396821 : Blo 2129435 2396821 := bbase (se 6 (by rfl) ⟨56175, by rfl⟩ : syracuseStep 2396821 = 112351) (by norm_num)
theorem B3195761 : Blo 2129435 3195761 := bstep (se 2 (by rfl) ⟨1198410, by rfl⟩ : syracuseStep 3195761 = 2396821) B2396821
theorem B2130507 : Blo 2129435 2130507 := bstep (se 1 (by rfl) ⟨1597880, by rfl⟩ : syracuseStep 2130507 = 3195761) B3195761
theorem B2696429 : Blo 2129435 2696429 := bbase (se 3 (by rfl) ⟨505580, by rfl⟩ : syracuseStep 2696429 = 1011161) (by norm_num)
theorem B7190477 : Blo 2129435 7190477 := bstep (se 3 (by rfl) ⟨1348214, by rfl⟩ : syracuseStep 7190477 = 2696429) B2696429
theorem B4793651 : Blo 2129435 4793651 := bstep (se 1 (by rfl) ⟨3595238, by rfl⟩ : syracuseStep 4793651 = 7190477) B7190477
theorem B3195767 : Blo 2129435 3195767 := bstep (se 1 (by rfl) ⟨2396825, by rfl⟩ : syracuseStep 3195767 = 4793651) B4793651
theorem B2130511 : Blo 2129435 2130511 := bstep (se 1 (by rfl) ⟨1597883, by rfl⟩ : syracuseStep 2130511 = 3195767) B3195767
theorem B3195773 : Blo 2129435 3195773 := bbase (se 3 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 3195773 = 1198415) (by norm_num)
theorem B2130515 : Blo 2129435 2130515 := bstep (se 1 (by rfl) ⟨1597886, by rfl⟩ : syracuseStep 2130515 = 3195773) B3195773
theorem B4793669 : Blo 2129435 4793669 := bbase (se 4 (by rfl) ⟨449406, by rfl⟩ : syracuseStep 4793669 = 898813) (by norm_num)
theorem B3195779 : Blo 2129435 3195779 := bstep (se 1 (by rfl) ⟨2396834, by rfl⟩ : syracuseStep 3195779 = 4793669) B4793669
theorem B2130519 : Blo 2129435 2130519 := bstep (se 1 (by rfl) ⟨1597889, by rfl⟩ : syracuseStep 2130519 = 3195779) B3195779
theorem B3239389 : Blo 2129435 3239389 := bbase (se 3 (by rfl) ⟨607385, by rfl⟩ : syracuseStep 3239389 = 1214771) (by norm_num)
theorem B4319185 : Blo 2129435 4319185 := bstep (se 2 (by rfl) ⟨1619694, by rfl⟩ : syracuseStep 4319185 = 3239389) B3239389
theorem B5758913 : Blo 2129435 5758913 := bstep (se 2 (by rfl) ⟨2159592, by rfl⟩ : syracuseStep 5758913 = 4319185) B4319185
theorem B3839275 : Blo 2129435 3839275 := bstep (se 1 (by rfl) ⟨2879456, by rfl⟩ : syracuseStep 3839275 = 5758913) B5758913
theorem B5119033 : Blo 2129435 5119033 := bstep (se 2 (by rfl) ⟨1919637, by rfl⟩ : syracuseStep 5119033 = 3839275) B3839275
theorem B6825377 : Blo 2129435 6825377 := bstep (se 2 (by rfl) ⟨2559516, by rfl⟩ : syracuseStep 6825377 = 5119033) B5119033
theorem B4550251 : Blo 2129435 4550251 := bstep (se 1 (by rfl) ⟨3412688, by rfl⟩ : syracuseStep 4550251 = 6825377) B6825377
theorem B6067001 : Blo 2129435 6067001 := bstep (se 2 (by rfl) ⟨2275125, by rfl⟩ : syracuseStep 6067001 = 4550251) B4550251
theorem B4044667 : Blo 2129435 4044667 := bstep (se 1 (by rfl) ⟨3033500, by rfl⟩ : syracuseStep 4044667 = 6067001) B6067001
theorem B5392889 : Blo 2129435 5392889 := bstep (se 2 (by rfl) ⟨2022333, by rfl⟩ : syracuseStep 5392889 = 4044667) B4044667
theorem B3595259 : Blo 2129435 3595259 := bstep (se 1 (by rfl) ⟨2696444, by rfl⟩ : syracuseStep 3595259 = 5392889) B5392889
theorem B2396839 : Blo 2129435 2396839 := bstep (se 1 (by rfl) ⟨1797629, by rfl⟩ : syracuseStep 2396839 = 3595259) B3595259
theorem B3195785 : Blo 2129435 3195785 := bstep (se 2 (by rfl) ⟨1198419, by rfl⟩ : syracuseStep 3195785 = 2396839) B2396839
theorem B2130523 : Blo 2129435 2130523 := bstep (se 1 (by rfl) ⟨1597892, by rfl⟩ : syracuseStep 2130523 = 3195785) B3195785
theorem B10785797 : Blo 2129435 10785797 := bbase (se 4 (by rfl) ⟨1011168, by rfl⟩ : syracuseStep 10785797 = 2022337) (by norm_num)
theorem B7190531 : Blo 2129435 7190531 := bstep (se 1 (by rfl) ⟨5392898, by rfl⟩ : syracuseStep 7190531 = 10785797) B10785797
theorem B4793687 : Blo 2129435 4793687 := bstep (se 1 (by rfl) ⟨3595265, by rfl⟩ : syracuseStep 4793687 = 7190531) B7190531
theorem B3195791 : Blo 2129435 3195791 := bstep (se 1 (by rfl) ⟨2396843, by rfl⟩ : syracuseStep 3195791 = 4793687) B4793687
theorem B2130527 : Blo 2129435 2130527 := bstep (se 1 (by rfl) ⟨1597895, by rfl⟩ : syracuseStep 2130527 = 3195791) B3195791
theorem B3195797 : Blo 2129435 3195797 := bbase (se 6 (by rfl) ⟨74901, by rfl⟩ : syracuseStep 3195797 = 149803) (by norm_num)
theorem B2130531 : Blo 2129435 2130531 := bstep (se 1 (by rfl) ⟨1597898, by rfl⟩ : syracuseStep 2130531 = 3195797) B3195797
theorem B12134069 : Blo 2129435 12134069 := bbase (se 5 (by rfl) ⟨568784, by rfl⟩ : syracuseStep 12134069 = 1137569) (by norm_num)
theorem B8089379 : Blo 2129435 8089379 := bstep (se 1 (by rfl) ⟨6067034, by rfl⟩ : syracuseStep 8089379 = 12134069) B12134069
theorem B5392919 : Blo 2129435 5392919 := bstep (se 1 (by rfl) ⟨4044689, by rfl⟩ : syracuseStep 5392919 = 8089379) B8089379
theorem B3595279 : Blo 2129435 3595279 := bstep (se 1 (by rfl) ⟨2696459, by rfl⟩ : syracuseStep 3595279 = 5392919) B5392919
theorem B4793705 : Blo 2129435 4793705 := bstep (se 2 (by rfl) ⟨1797639, by rfl⟩ : syracuseStep 4793705 = 3595279) B3595279
theorem B3195803 : Blo 2129435 3195803 := bstep (se 1 (by rfl) ⟨2396852, by rfl⟩ : syracuseStep 3195803 = 4793705) B4793705
theorem B2130535 : Blo 2129435 2130535 := bstep (se 1 (by rfl) ⟨1597901, by rfl⟩ : syracuseStep 2130535 = 3195803) B3195803
theorem B2396857 : Blo 2129435 2396857 := bbase (se 2 (by rfl) ⟨898821, by rfl⟩ : syracuseStep 2396857 = 1797643) (by norm_num)
theorem B3195809 : Blo 2129435 3195809 := bstep (se 2 (by rfl) ⟨1198428, by rfl⟩ : syracuseStep 3195809 = 2396857) B2396857
theorem B2130539 : Blo 2129435 2130539 := bstep (se 1 (by rfl) ⟨1597904, by rfl⟩ : syracuseStep 2130539 = 3195809) B3195809
theorem B4550293 : Blo 2129435 4550293 := bbase (se 6 (by rfl) ⟨106647, by rfl⟩ : syracuseStep 4550293 = 213295) (by norm_num)
theorem B6067057 : Blo 2129435 6067057 := bstep (se 2 (by rfl) ⟨2275146, by rfl⟩ : syracuseStep 6067057 = 4550293) B4550293
theorem B8089409 : Blo 2129435 8089409 := bstep (se 2 (by rfl) ⟨3033528, by rfl⟩ : syracuseStep 8089409 = 6067057) B6067057
theorem B5392939 : Blo 2129435 5392939 := bstep (se 1 (by rfl) ⟨4044704, by rfl⟩ : syracuseStep 5392939 = 8089409) B8089409
theorem B7190585 : Blo 2129435 7190585 := bstep (se 2 (by rfl) ⟨2696469, by rfl⟩ : syracuseStep 7190585 = 5392939) B5392939
theorem B4793723 : Blo 2129435 4793723 := bstep (se 1 (by rfl) ⟨3595292, by rfl⟩ : syracuseStep 4793723 = 7190585) B7190585
theorem B3195815 : Blo 2129435 3195815 := bstep (se 1 (by rfl) ⟨2396861, by rfl⟩ : syracuseStep 3195815 = 4793723) B4793723
theorem B2130543 : Blo 2129435 2130543 := bstep (se 1 (by rfl) ⟨1597907, by rfl⟩ : syracuseStep 2130543 = 3195815) B3195815
theorem B3195821 : Blo 2129435 3195821 := bbase (se 3 (by rfl) ⟨599216, by rfl⟩ : syracuseStep 3195821 = 1198433) (by norm_num)
theorem B2130547 : Blo 2129435 2130547 := bstep (se 1 (by rfl) ⟨1597910, by rfl⟩ : syracuseStep 2130547 = 3195821) B3195821
theorem B4793741 : Blo 2129435 4793741 := bbase (se 3 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 4793741 = 1797653) (by norm_num)
theorem B3195827 : Blo 2129435 3195827 := bstep (se 1 (by rfl) ⟨2396870, by rfl⟩ : syracuseStep 3195827 = 4793741) B4793741
theorem B2130551 : Blo 2129435 2130551 := bstep (se 1 (by rfl) ⟨1597913, by rfl⟩ : syracuseStep 2130551 = 3195827) B3195827
theorem B2696485 : Blo 2129435 2696485 := bbase (se 4 (by rfl) ⟨252795, by rfl⟩ : syracuseStep 2696485 = 505591) (by norm_num)
theorem B3595313 : Blo 2129435 3595313 := bstep (se 2 (by rfl) ⟨1348242, by rfl⟩ : syracuseStep 3595313 = 2696485) B2696485
theorem B2396875 : Blo 2129435 2396875 := bstep (se 1 (by rfl) ⟨1797656, by rfl⟩ : syracuseStep 2396875 = 3595313) B3595313
theorem B3195833 : Blo 2129435 3195833 := bstep (se 2 (by rfl) ⟨1198437, by rfl⟩ : syracuseStep 3195833 = 2396875) B2396875
theorem B2130555 : Blo 2129435 2130555 := bstep (se 1 (by rfl) ⟨1597916, by rfl⟩ : syracuseStep 2130555 = 3195833) B3195833
theorem B27674453 : Blo 2129435 27674453 := bbase (se 9 (by rfl) ⟨81077, by rfl⟩ : syracuseStep 27674453 = 162155) (by norm_num)
theorem B18449635 : Blo 2129435 18449635 := bstep (se 1 (by rfl) ⟨13837226, by rfl⟩ : syracuseStep 18449635 = 27674453) B27674453
theorem B24599513 : Blo 2129435 24599513 := bstep (se 2 (by rfl) ⟨9224817, by rfl⟩ : syracuseStep 24599513 = 18449635) B18449635
theorem B16399675 : Blo 2129435 16399675 := bstep (se 1 (by rfl) ⟨12299756, by rfl⟩ : syracuseStep 16399675 = 24599513) B24599513
theorem B87464933 : Blo 2129435 87464933 := bstep (se 4 (by rfl) ⟨8199837, by rfl⟩ : syracuseStep 87464933 = 16399675) B16399675
theorem B58309955 : Blo 2129435 58309955 := bstep (se 1 (by rfl) ⟨43732466, by rfl⟩ : syracuseStep 58309955 = 87464933) B87464933
theorem B38873303 : Blo 2129435 38873303 := bstep (se 1 (by rfl) ⟨29154977, by rfl⟩ : syracuseStep 38873303 = 58309955) B58309955
theorem B25915535 : Blo 2129435 25915535 := bstep (se 1 (by rfl) ⟨19436651, by rfl⟩ : syracuseStep 25915535 = 38873303) B38873303
theorem B17277023 : Blo 2129435 17277023 := bstep (se 1 (by rfl) ⟨12957767, by rfl⟩ : syracuseStep 17277023 = 25915535) B25915535
theorem B46072061 : Blo 2129435 46072061 := bstep (se 3 (by rfl) ⟨8638511, by rfl⟩ : syracuseStep 46072061 = 17277023) B17277023
theorem B30714707 : Blo 2129435 30714707 := bstep (se 1 (by rfl) ⟨23036030, by rfl⟩ : syracuseStep 30714707 = 46072061) B46072061
theorem B20476471 : Blo 2129435 20476471 := bstep (se 1 (by rfl) ⟨15357353, by rfl⟩ : syracuseStep 20476471 = 30714707) B30714707
theorem B27301961 : Blo 2129435 27301961 := bstep (se 2 (by rfl) ⟨10238235, by rfl⟩ : syracuseStep 27301961 = 20476471) B20476471
theorem B18201307 : Blo 2129435 18201307 := bstep (se 1 (by rfl) ⟨13650980, by rfl⟩ : syracuseStep 18201307 = 27301961) B27301961
theorem B24268409 : Blo 2129435 24268409 := bstep (se 2 (by rfl) ⟨9100653, by rfl⟩ : syracuseStep 24268409 = 18201307) B18201307
theorem B16178939 : Blo 2129435 16178939 := bstep (se 1 (by rfl) ⟨12134204, by rfl⟩ : syracuseStep 16178939 = 24268409) B24268409
theorem B10785959 : Blo 2129435 10785959 := bstep (se 1 (by rfl) ⟨8089469, by rfl⟩ : syracuseStep 10785959 = 16178939) B16178939
theorem B7190639 : Blo 2129435 7190639 := bstep (se 1 (by rfl) ⟨5392979, by rfl⟩ : syracuseStep 7190639 = 10785959) B10785959
theorem B4793759 : Blo 2129435 4793759 := bstep (se 1 (by rfl) ⟨3595319, by rfl⟩ : syracuseStep 4793759 = 7190639) B7190639
theorem B3195839 : Blo 2129435 3195839 := bstep (se 1 (by rfl) ⟨2396879, by rfl⟩ : syracuseStep 3195839 = 4793759) B4793759
theorem B2130559 : Blo 2129435 2130559 := bstep (se 1 (by rfl) ⟨1597919, by rfl⟩ : syracuseStep 2130559 = 3195839) B3195839
theorem B3195845 : Blo 2129435 3195845 := bbase (se 4 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 3195845 = 599221) (by norm_num)
theorem B2130563 : Blo 2129435 2130563 := bstep (se 1 (by rfl) ⟨1597922, by rfl⟩ : syracuseStep 2130563 = 3195845) B3195845
theorem B3595333 : Blo 2129435 3595333 := bbase (se 4 (by rfl) ⟨337062, by rfl⟩ : syracuseStep 3595333 = 674125) (by norm_num)
theorem B4793777 : Blo 2129435 4793777 := bstep (se 2 (by rfl) ⟨1797666, by rfl⟩ : syracuseStep 4793777 = 3595333) B3595333
theorem B3195851 : Blo 2129435 3195851 := bstep (se 1 (by rfl) ⟨2396888, by rfl⟩ : syracuseStep 3195851 = 4793777) B4793777
theorem B2130567 : Blo 2129435 2130567 := bstep (se 1 (by rfl) ⟨1597925, by rfl⟩ : syracuseStep 2130567 = 3195851) B3195851
theorem B2396893 : Blo 2129435 2396893 := bbase (se 3 (by rfl) ⟨449417, by rfl⟩ : syracuseStep 2396893 = 898835) (by norm_num)
theorem B3195857 : Blo 2129435 3195857 := bstep (se 2 (by rfl) ⟨1198446, by rfl⟩ : syracuseStep 3195857 = 2396893) B2396893
theorem B2130571 : Blo 2129435 2130571 := bstep (se 1 (by rfl) ⟨1597928, by rfl⟩ : syracuseStep 2130571 = 3195857) B3195857
theorem B7190693 : Blo 2129435 7190693 := bbase (se 4 (by rfl) ⟨674127, by rfl⟩ : syracuseStep 7190693 = 1348255) (by norm_num)
theorem B4793795 : Blo 2129435 4793795 := bstep (se 1 (by rfl) ⟨3595346, by rfl⟩ : syracuseStep 4793795 = 7190693) B7190693
theorem B3195863 : Blo 2129435 3195863 := bstep (se 1 (by rfl) ⟨2396897, by rfl⟩ : syracuseStep 3195863 = 4793795) B4793795
theorem B2130575 : Blo 2129435 2130575 := bstep (se 1 (by rfl) ⟨1597931, by rfl⟩ : syracuseStep 2130575 = 3195863) B3195863
theorem B3195869 : Blo 2129435 3195869 := bbase (se 3 (by rfl) ⟨599225, by rfl⟩ : syracuseStep 3195869 = 1198451) (by norm_num)
theorem B2130579 : Blo 2129435 2130579 := bstep (se 1 (by rfl) ⟨1597934, by rfl⟩ : syracuseStep 2130579 = 3195869) B3195869
theorem B4793813 : Blo 2129435 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B3195875 : Blo 2129435 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B2130583 : Blo 2129435 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B12957941 : Blo 2129435 12957941 := bbase (se 5 (by rfl) ⟨607403, by rfl⟩ : syracuseStep 12957941 = 1214807) (by norm_num)
theorem B34554509 : Blo 2129435 34554509 := bstep (se 3 (by rfl) ⟨6478970, by rfl⟩ : syracuseStep 34554509 = 12957941) B12957941
theorem B23036339 : Blo 2129435 23036339 := bstep (se 1 (by rfl) ⟨17277254, by rfl⟩ : syracuseStep 23036339 = 34554509) B34554509
theorem B15357559 : Blo 2129435 15357559 := bstep (se 1 (by rfl) ⟨11518169, by rfl⟩ : syracuseStep 15357559 = 23036339) B23036339
theorem B20476745 : Blo 2129435 20476745 := bstep (se 2 (by rfl) ⟨7678779, by rfl⟩ : syracuseStep 20476745 = 15357559) B15357559
theorem B13651163 : Blo 2129435 13651163 := bstep (se 1 (by rfl) ⟨10238372, by rfl⟩ : syracuseStep 13651163 = 20476745) B20476745
theorem B9100775 : Blo 2129435 9100775 := bstep (se 1 (by rfl) ⟨6825581, by rfl⟩ : syracuseStep 9100775 = 13651163) B13651163
theorem B6067183 : Blo 2129435 6067183 := bstep (se 1 (by rfl) ⟨4550387, by rfl⟩ : syracuseStep 6067183 = 9100775) B9100775
theorem B8089577 : Blo 2129435 8089577 := bstep (se 2 (by rfl) ⟨3033591, by rfl⟩ : syracuseStep 8089577 = 6067183) B6067183
theorem B5393051 : Blo 2129435 5393051 := bstep (se 1 (by rfl) ⟨4044788, by rfl⟩ : syracuseStep 5393051 = 8089577) B8089577
theorem B3595367 : Blo 2129435 3595367 := bstep (se 1 (by rfl) ⟨2696525, by rfl⟩ : syracuseStep 3595367 = 5393051) B5393051
theorem B2396911 : Blo 2129435 2396911 := bstep (se 1 (by rfl) ⟨1797683, by rfl⟩ : syracuseStep 2396911 = 3595367) B3595367
theorem B3195881 : Blo 2129435 3195881 := bstep (se 2 (by rfl) ⟨1198455, by rfl⟩ : syracuseStep 3195881 = 2396911) B2396911
theorem B2130587 : Blo 2129435 2130587 := bstep (se 1 (by rfl) ⟨1597940, by rfl⟩ : syracuseStep 2130587 = 3195881) B3195881
theorem B4859237 : Blo 2129435 4859237 := bbase (se 4 (by rfl) ⟨455553, by rfl⟩ : syracuseStep 4859237 = 911107) (by norm_num)
theorem B12957965 : Blo 2129435 12957965 := bstep (se 3 (by rfl) ⟨2429618, by rfl⟩ : syracuseStep 12957965 = 4859237) B4859237
theorem B8638643 : Blo 2129435 8638643 := bstep (se 1 (by rfl) ⟨6478982, by rfl⟩ : syracuseStep 8638643 = 12957965) B12957965
theorem B5759095 : Blo 2129435 5759095 := bstep (se 1 (by rfl) ⟨4319321, by rfl⟩ : syracuseStep 5759095 = 8638643) B8638643
theorem B7678793 : Blo 2129435 7678793 := bstep (se 2 (by rfl) ⟨2879547, by rfl⟩ : syracuseStep 7678793 = 5759095) B5759095
theorem B5119195 : Blo 2129435 5119195 := bstep (se 1 (by rfl) ⟨3839396, by rfl⟩ : syracuseStep 5119195 = 7678793) B7678793
theorem B6825593 : Blo 2129435 6825593 := bstep (se 2 (by rfl) ⟨2559597, by rfl⟩ : syracuseStep 6825593 = 5119195) B5119195
theorem B18201581 : Blo 2129435 18201581 := bstep (se 3 (by rfl) ⟨3412796, by rfl⟩ : syracuseStep 18201581 = 6825593) B6825593
theorem B12134387 : Blo 2129435 12134387 := bstep (se 1 (by rfl) ⟨9100790, by rfl⟩ : syracuseStep 12134387 = 18201581) B18201581
theorem B8089591 : Blo 2129435 8089591 := bstep (se 1 (by rfl) ⟨6067193, by rfl⟩ : syracuseStep 8089591 = 12134387) B12134387
theorem B10786121 : Blo 2129435 10786121 := bstep (se 2 (by rfl) ⟨4044795, by rfl⟩ : syracuseStep 10786121 = 8089591) B8089591
theorem B7190747 : Blo 2129435 7190747 := bstep (se 1 (by rfl) ⟨5393060, by rfl⟩ : syracuseStep 7190747 = 10786121) B10786121
theorem B4793831 : Blo 2129435 4793831 := bstep (se 1 (by rfl) ⟨3595373, by rfl⟩ : syracuseStep 4793831 = 7190747) B7190747
theorem B3195887 : Blo 2129435 3195887 := bstep (se 1 (by rfl) ⟨2396915, by rfl⟩ : syracuseStep 3195887 = 4793831) B4793831
theorem B2130591 : Blo 2129435 2130591 := bstep (se 1 (by rfl) ⟨1597943, by rfl⟩ : syracuseStep 2130591 = 3195887) B3195887
theorem B3195893 : Blo 2129435 3195893 := bbase (se 5 (by rfl) ⟨149807, by rfl⟩ : syracuseStep 3195893 = 299615) (by norm_num)
theorem B2130595 : Blo 2129435 2130595 := bstep (se 1 (by rfl) ⟨1597946, by rfl⟩ : syracuseStep 2130595 = 3195893) B3195893
theorem B4550413 : Blo 2129435 4550413 := bbase (se 3 (by rfl) ⟨853202, by rfl⟩ : syracuseStep 4550413 = 1706405) (by norm_num)
theorem B6067217 : Blo 2129435 6067217 := bstep (se 2 (by rfl) ⟨2275206, by rfl⟩ : syracuseStep 6067217 = 4550413) B4550413
theorem B4044811 : Blo 2129435 4044811 := bstep (se 1 (by rfl) ⟨3033608, by rfl⟩ : syracuseStep 4044811 = 6067217) B6067217
theorem B5393081 : Blo 2129435 5393081 := bstep (se 2 (by rfl) ⟨2022405, by rfl⟩ : syracuseStep 5393081 = 4044811) B4044811
theorem B3595387 : Blo 2129435 3595387 := bstep (se 1 (by rfl) ⟨2696540, by rfl⟩ : syracuseStep 3595387 = 5393081) B5393081
theorem B4793849 : Blo 2129435 4793849 := bstep (se 2 (by rfl) ⟨1797693, by rfl⟩ : syracuseStep 4793849 = 3595387) B3595387
theorem B3195899 : Blo 2129435 3195899 := bstep (se 1 (by rfl) ⟨2396924, by rfl⟩ : syracuseStep 3195899 = 4793849) B4793849
theorem B2130599 : Blo 2129435 2130599 := bstep (se 1 (by rfl) ⟨1597949, by rfl⟩ : syracuseStep 2130599 = 3195899) B3195899
theorem B2396929 : Blo 2129435 2396929 := bbase (se 2 (by rfl) ⟨898848, by rfl⟩ : syracuseStep 2396929 = 1797697) (by norm_num)
theorem B3195905 : Blo 2129435 3195905 := bstep (se 2 (by rfl) ⟨1198464, by rfl⟩ : syracuseStep 3195905 = 2396929) B2396929
theorem B2130603 : Blo 2129435 2130603 := bstep (se 1 (by rfl) ⟨1597952, by rfl⟩ : syracuseStep 2130603 = 3195905) B3195905
theorem B5393101 : Blo 2129435 5393101 := bbase (se 3 (by rfl) ⟨1011206, by rfl⟩ : syracuseStep 5393101 = 2022413) (by norm_num)
theorem B7190801 : Blo 2129435 7190801 := bstep (se 2 (by rfl) ⟨2696550, by rfl⟩ : syracuseStep 7190801 = 5393101) B5393101
theorem B4793867 : Blo 2129435 4793867 := bstep (se 1 (by rfl) ⟨3595400, by rfl⟩ : syracuseStep 4793867 = 7190801) B7190801
theorem B3195911 : Blo 2129435 3195911 := bstep (se 1 (by rfl) ⟨2396933, by rfl⟩ : syracuseStep 3195911 = 4793867) B4793867
theorem B2130607 : Blo 2129435 2130607 := bstep (se 1 (by rfl) ⟨1597955, by rfl⟩ : syracuseStep 2130607 = 3195911) B3195911
theorem B3195917 : Blo 2129435 3195917 := bbase (se 3 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 3195917 = 1198469) (by norm_num)
theorem B2130611 : Blo 2129435 2130611 := bstep (se 1 (by rfl) ⟨1597958, by rfl⟩ : syracuseStep 2130611 = 3195917) B3195917
theorem B4793885 : Blo 2129435 4793885 := bbase (se 3 (by rfl) ⟨898853, by rfl⟩ : syracuseStep 4793885 = 1797707) (by norm_num)
theorem B3195923 : Blo 2129435 3195923 := bstep (se 1 (by rfl) ⟨2396942, by rfl⟩ : syracuseStep 3195923 = 4793885) B4793885
theorem B2130615 : Blo 2129435 2130615 := bstep (se 1 (by rfl) ⟨1597961, by rfl⟩ : syracuseStep 2130615 = 3195923) B3195923
theorem B3595421 : Blo 2129435 3595421 := bbase (se 3 (by rfl) ⟨674141, by rfl⟩ : syracuseStep 3595421 = 1348283) (by norm_num)
theorem B2396947 : Blo 2129435 2396947 := bstep (se 1 (by rfl) ⟨1797710, by rfl⟩ : syracuseStep 2396947 = 3595421) B3595421
theorem B3195929 : Blo 2129435 3195929 := bstep (se 2 (by rfl) ⟨1198473, by rfl⟩ : syracuseStep 3195929 = 2396947) B2396947
theorem B2130619 : Blo 2129435 2130619 := bstep (se 1 (by rfl) ⟨1597964, by rfl⟩ : syracuseStep 2130619 = 3195929) B3195929
theorem B44330453 : Blo 2129435 44330453 := bbase (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) (by norm_num)
theorem B472858165 : Blo 2129435 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B630477553 : Blo 2129435 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B840636737 : Blo 2129435 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B560424491 : Blo 2129435 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B373616327 : Blo 2129435 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B249077551 : Blo 2129435 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B332103401 : Blo 2129435 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B221402267 : Blo 2129435 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B147601511 : Blo 2129435 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B98401007 : Blo 2129435 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B262402685 : Blo 2129435 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B174935123 : Blo 2129435 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B116623415 : Blo 2129435 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B77748943 : Blo 2129435 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B103665257 : Blo 2129435 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B69110171 : Blo 2129435 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B46073447 : Blo 2129435 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B30715631 : Blo 2129435 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B20477087 : Blo 2129435 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B13651391 : Blo 2129435 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B9100927 : Blo 2129435 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B12134569 : Blo 2129435 12134569 := bstep (se 2 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 12134569 = 9100927) B9100927
theorem B16179425 : Blo 2129435 16179425 := bstep (se 2 (by rfl) ⟨6067284, by rfl⟩ : syracuseStep 16179425 = 12134569) B12134569
theorem B10786283 : Blo 2129435 10786283 := bstep (se 1 (by rfl) ⟨8089712, by rfl⟩ : syracuseStep 10786283 = 16179425) B16179425
theorem B7190855 : Blo 2129435 7190855 := bstep (se 1 (by rfl) ⟨5393141, by rfl⟩ : syracuseStep 7190855 = 10786283) B10786283
theorem B4793903 : Blo 2129435 4793903 := bstep (se 1 (by rfl) ⟨3595427, by rfl⟩ : syracuseStep 4793903 = 7190855) B7190855
theorem B3195935 : Blo 2129435 3195935 := bstep (se 1 (by rfl) ⟨2396951, by rfl⟩ : syracuseStep 3195935 = 4793903) B4793903
theorem B2130623 : Blo 2129435 2130623 := bstep (se 1 (by rfl) ⟨1597967, by rfl⟩ : syracuseStep 2130623 = 3195935) B3195935
theorem B3195941 : Blo 2129435 3195941 := bbase (se 4 (by rfl) ⟨299619, by rfl⟩ : syracuseStep 3195941 = 599239) (by norm_num)
theorem B2130627 : Blo 2129435 2130627 := bstep (se 1 (by rfl) ⟨1597970, by rfl⟩ : syracuseStep 2130627 = 3195941) B3195941
theorem B2696581 : Blo 2129435 2696581 := bbase (se 4 (by rfl) ⟨252804, by rfl⟩ : syracuseStep 2696581 = 505609) (by norm_num)
theorem B3595441 : Blo 2129435 3595441 := bstep (se 2 (by rfl) ⟨1348290, by rfl⟩ : syracuseStep 3595441 = 2696581) B2696581
theorem B4793921 : Blo 2129435 4793921 := bstep (se 2 (by rfl) ⟨1797720, by rfl⟩ : syracuseStep 4793921 = 3595441) B3595441
theorem B3195947 : Blo 2129435 3195947 := bstep (se 1 (by rfl) ⟨2396960, by rfl⟩ : syracuseStep 3195947 = 4793921) B4793921
theorem B2130631 : Blo 2129435 2130631 := bstep (se 1 (by rfl) ⟨1597973, by rfl⟩ : syracuseStep 2130631 = 3195947) B3195947
theorem B2396965 : Blo 2129435 2396965 := bbase (se 4 (by rfl) ⟨224715, by rfl⟩ : syracuseStep 2396965 = 449431) (by norm_num)
theorem B3195953 : Blo 2129435 3195953 := bstep (se 2 (by rfl) ⟨1198482, by rfl⟩ : syracuseStep 3195953 = 2396965) B2396965
theorem B2130635 : Blo 2129435 2130635 := bstep (se 1 (by rfl) ⟨1597976, by rfl⟩ : syracuseStep 2130635 = 3195953) B3195953
theorem B9100997 : Blo 2129435 9100997 := bbase (se 4 (by rfl) ⟨853218, by rfl⟩ : syracuseStep 9100997 = 1706437) (by norm_num)
theorem B6067331 : Blo 2129435 6067331 := bstep (se 1 (by rfl) ⟨4550498, by rfl⟩ : syracuseStep 6067331 = 9100997) B9100997
theorem B4044887 : Blo 2129435 4044887 := bstep (se 1 (by rfl) ⟨3033665, by rfl⟩ : syracuseStep 4044887 = 6067331) B6067331
theorem B2696591 : Blo 2129435 2696591 := bstep (se 1 (by rfl) ⟨2022443, by rfl⟩ : syracuseStep 2696591 = 4044887) B4044887
theorem B7190909 : Blo 2129435 7190909 := bstep (se 3 (by rfl) ⟨1348295, by rfl⟩ : syracuseStep 7190909 = 2696591) B2696591
theorem B4793939 : Blo 2129435 4793939 := bstep (se 1 (by rfl) ⟨3595454, by rfl⟩ : syracuseStep 4793939 = 7190909) B7190909
theorem B3195959 : Blo 2129435 3195959 := bstep (se 1 (by rfl) ⟨2396969, by rfl⟩ : syracuseStep 3195959 = 4793939) B4793939
theorem B2130639 : Blo 2129435 2130639 := bstep (se 1 (by rfl) ⟨1597979, by rfl⟩ : syracuseStep 2130639 = 3195959) B3195959
theorem B3195965 : Blo 2129435 3195965 := bbase (se 3 (by rfl) ⟨599243, by rfl⟩ : syracuseStep 3195965 = 1198487) (by norm_num)
theorem B2130643 : Blo 2129435 2130643 := bstep (se 1 (by rfl) ⟨1597982, by rfl⟩ : syracuseStep 2130643 = 3195965) B3195965
theorem B4793957 : Blo 2129435 4793957 := bbase (se 4 (by rfl) ⟨449433, by rfl⟩ : syracuseStep 4793957 = 898867) (by norm_num)
theorem B3195971 : Blo 2129435 3195971 := bstep (se 1 (by rfl) ⟨2396978, by rfl⟩ : syracuseStep 3195971 = 4793957) B4793957
theorem B2130647 : Blo 2129435 2130647 := bstep (se 1 (by rfl) ⟨1597985, by rfl⟩ : syracuseStep 2130647 = 3195971) B3195971
theorem B5393213 : Blo 2129435 5393213 := bbase (se 3 (by rfl) ⟨1011227, by rfl⟩ : syracuseStep 5393213 = 2022455) (by norm_num)
theorem B3595475 : Blo 2129435 3595475 := bstep (se 1 (by rfl) ⟨2696606, by rfl⟩ : syracuseStep 3595475 = 5393213) B5393213
theorem B2396983 : Blo 2129435 2396983 := bstep (se 1 (by rfl) ⟨1797737, by rfl⟩ : syracuseStep 2396983 = 3595475) B3595475
theorem B3195977 : Blo 2129435 3195977 := bstep (se 2 (by rfl) ⟨1198491, by rfl⟩ : syracuseStep 3195977 = 2396983) B2396983
theorem B2130651 : Blo 2129435 2130651 := bstep (se 1 (by rfl) ⟨1597988, by rfl⟩ : syracuseStep 2130651 = 3195977) B3195977
theorem B4044917 : Blo 2129435 4044917 := bbase (se 5 (by rfl) ⟨189605, by rfl⟩ : syracuseStep 4044917 = 379211) (by norm_num)
theorem B10786445 : Blo 2129435 10786445 := bstep (se 3 (by rfl) ⟨2022458, by rfl⟩ : syracuseStep 10786445 = 4044917) B4044917
theorem B7190963 : Blo 2129435 7190963 := bstep (se 1 (by rfl) ⟨5393222, by rfl⟩ : syracuseStep 7190963 = 10786445) B10786445
theorem B4793975 : Blo 2129435 4793975 := bstep (se 1 (by rfl) ⟨3595481, by rfl⟩ : syracuseStep 4793975 = 7190963) B7190963
theorem B3195983 : Blo 2129435 3195983 := bstep (se 1 (by rfl) ⟨2396987, by rfl⟩ : syracuseStep 3195983 = 4793975) B4793975
theorem B2130655 : Blo 2129435 2130655 := bstep (se 1 (by rfl) ⟨1597991, by rfl⟩ : syracuseStep 2130655 = 3195983) B3195983
theorem B3195989 : Blo 2129435 3195989 := bbase (se 8 (by rfl) ⟨18726, by rfl⟩ : syracuseStep 3195989 = 37453) (by norm_num)
theorem B2130659 : Blo 2129435 2130659 := bstep (se 1 (by rfl) ⟨1597994, by rfl⟩ : syracuseStep 2130659 = 3195989) B3195989
theorem B2879645 : Blo 2129435 2879645 := bbase (se 3 (by rfl) ⟨539933, by rfl⟩ : syracuseStep 2879645 = 1079867) (by norm_num)
theorem B7679053 : Blo 2129435 7679053 := bstep (se 3 (by rfl) ⟨1439822, by rfl⟩ : syracuseStep 7679053 = 2879645) B2879645
theorem B10238737 : Blo 2129435 10238737 := bstep (se 2 (by rfl) ⟨3839526, by rfl⟩ : syracuseStep 10238737 = 7679053) B7679053
theorem B13651649 : Blo 2129435 13651649 := bstep (se 2 (by rfl) ⟨5119368, by rfl⟩ : syracuseStep 13651649 = 10238737) B10238737
theorem B9101099 : Blo 2129435 9101099 := bstep (se 1 (by rfl) ⟨6825824, by rfl⟩ : syracuseStep 9101099 = 13651649) B13651649
theorem B6067399 : Blo 2129435 6067399 := bstep (se 1 (by rfl) ⟨4550549, by rfl⟩ : syracuseStep 6067399 = 9101099) B9101099
theorem B8089865 : Blo 2129435 8089865 := bstep (se 2 (by rfl) ⟨3033699, by rfl⟩ : syracuseStep 8089865 = 6067399) B6067399
theorem B5393243 : Blo 2129435 5393243 := bstep (se 1 (by rfl) ⟨4044932, by rfl⟩ : syracuseStep 5393243 = 8089865) B8089865
theorem B3595495 : Blo 2129435 3595495 := bstep (se 1 (by rfl) ⟨2696621, by rfl⟩ : syracuseStep 3595495 = 5393243) B5393243
theorem B4793993 : Blo 2129435 4793993 := bstep (se 2 (by rfl) ⟨1797747, by rfl⟩ : syracuseStep 4793993 = 3595495) B3595495
theorem B3195995 : Blo 2129435 3195995 := bstep (se 1 (by rfl) ⟨2396996, by rfl⟩ : syracuseStep 3195995 = 4793993) B4793993
theorem B2130663 : Blo 2129435 2130663 := bstep (se 1 (by rfl) ⟨1597997, by rfl⟩ : syracuseStep 2130663 = 3195995) B3195995
theorem B2397001 : Blo 2129435 2397001 := bbase (se 2 (by rfl) ⟨898875, by rfl⟩ : syracuseStep 2397001 = 1797751) (by norm_num)
theorem B3196001 : Blo 2129435 3196001 := bstep (se 2 (by rfl) ⟨1198500, by rfl⟩ : syracuseStep 3196001 = 2397001) B2397001
theorem B2130667 : Blo 2129435 2130667 := bstep (se 1 (by rfl) ⟨1598000, by rfl⟩ : syracuseStep 2130667 = 3196001) B3196001
theorem B10378469 : Blo 2129435 10378469 := bbase (se 4 (by rfl) ⟨972981, by rfl⟩ : syracuseStep 10378469 = 1945963) (by norm_num)
theorem B27675917 : Blo 2129435 27675917 := bstep (se 3 (by rfl) ⟨5189234, by rfl⟩ : syracuseStep 27675917 = 10378469) B10378469
theorem B18450611 : Blo 2129435 18450611 := bstep (se 1 (by rfl) ⟨13837958, by rfl⟩ : syracuseStep 18450611 = 27675917) B27675917
theorem B12300407 : Blo 2129435 12300407 := bstep (se 1 (by rfl) ⟨9225305, by rfl⟩ : syracuseStep 12300407 = 18450611) B18450611
theorem B8200271 : Blo 2129435 8200271 := bstep (se 1 (by rfl) ⟨6150203, by rfl⟩ : syracuseStep 8200271 = 12300407) B12300407
theorem B5466847 : Blo 2129435 5466847 := bstep (se 1 (by rfl) ⟨4100135, by rfl⟩ : syracuseStep 5466847 = 8200271) B8200271
theorem B7289129 : Blo 2129435 7289129 := bstep (se 2 (by rfl) ⟨2733423, by rfl⟩ : syracuseStep 7289129 = 5466847) B5466847
theorem B19437677 : Blo 2129435 19437677 := bstep (se 3 (by rfl) ⟨3644564, by rfl⟩ : syracuseStep 19437677 = 7289129) B7289129
theorem B12958451 : Blo 2129435 12958451 := bstep (se 1 (by rfl) ⟨9718838, by rfl⟩ : syracuseStep 12958451 = 19437677) B19437677
theorem B8638967 : Blo 2129435 8638967 := bstep (se 1 (by rfl) ⟨6479225, by rfl⟩ : syracuseStep 8638967 = 12958451) B12958451
theorem B5759311 : Blo 2129435 5759311 := bstep (se 1 (by rfl) ⟨4319483, by rfl⟩ : syracuseStep 5759311 = 8638967) B8638967
theorem B7679081 : Blo 2129435 7679081 := bstep (se 2 (by rfl) ⟨2879655, by rfl⟩ : syracuseStep 7679081 = 5759311) B5759311
theorem B20477549 : Blo 2129435 20477549 := bstep (se 3 (by rfl) ⟨3839540, by rfl⟩ : syracuseStep 20477549 = 7679081) B7679081
theorem B13651699 : Blo 2129435 13651699 := bstep (se 1 (by rfl) ⟨10238774, by rfl⟩ : syracuseStep 13651699 = 20477549) B20477549
theorem B18202265 : Blo 2129435 18202265 := bstep (se 2 (by rfl) ⟨6825849, by rfl⟩ : syracuseStep 18202265 = 13651699) B13651699
theorem B12134843 : Blo 2129435 12134843 := bstep (se 1 (by rfl) ⟨9101132, by rfl⟩ : syracuseStep 12134843 = 18202265) B18202265
theorem B8089895 : Blo 2129435 8089895 := bstep (se 1 (by rfl) ⟨6067421, by rfl⟩ : syracuseStep 8089895 = 12134843) B12134843
theorem B5393263 : Blo 2129435 5393263 := bstep (se 1 (by rfl) ⟨4044947, by rfl⟩ : syracuseStep 5393263 = 8089895) B8089895
theorem B7191017 : Blo 2129435 7191017 := bstep (se 2 (by rfl) ⟨2696631, by rfl⟩ : syracuseStep 7191017 = 5393263) B5393263
theorem B4794011 : Blo 2129435 4794011 := bstep (se 1 (by rfl) ⟨3595508, by rfl⟩ : syracuseStep 4794011 = 7191017) B7191017
theorem B3196007 : Blo 2129435 3196007 := bstep (se 1 (by rfl) ⟨2397005, by rfl⟩ : syracuseStep 3196007 = 4794011) B4794011
theorem B2130671 : Blo 2129435 2130671 := bstep (se 1 (by rfl) ⟨1598003, by rfl⟩ : syracuseStep 2130671 = 3196007) B3196007
theorem B3196013 : Blo 2129435 3196013 := bbase (se 3 (by rfl) ⟨599252, by rfl⟩ : syracuseStep 3196013 = 1198505) (by norm_num)
theorem B2130675 : Blo 2129435 2130675 := bstep (se 1 (by rfl) ⟨1598006, by rfl⟩ : syracuseStep 2130675 = 3196013) B3196013
theorem B4794029 : Blo 2129435 4794029 := bbase (se 3 (by rfl) ⟨898880, by rfl⟩ : syracuseStep 4794029 = 1797761) (by norm_num)
theorem B3196019 : Blo 2129435 3196019 := bstep (se 1 (by rfl) ⟨2397014, by rfl⟩ : syracuseStep 3196019 = 4794029) B4794029
theorem B2130679 : Blo 2129435 2130679 := bstep (se 1 (by rfl) ⟨1598009, by rfl⟩ : syracuseStep 2130679 = 3196019) B3196019
theorem B2559709 : Blo 2129435 2559709 := bbase (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) (by norm_num)
theorem B3412945 : Blo 2129435 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B4550593 : Blo 2129435 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B6067457 : Blo 2129435 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B4044971 : Blo 2129435 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B2696647 : Blo 2129435 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B3595529 : Blo 2129435 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B2397019 : Blo 2129435 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B3196025 : Blo 2129435 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B2130683 : Blo 2129435 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B2879677 : Blo 2129435 2879677 := bbase (se 3 (by rfl) ⟨539939, by rfl⟩ : syracuseStep 2879677 = 1079879) (by norm_num)
theorem B3839569 : Blo 2129435 3839569 := bstep (se 2 (by rfl) ⟨1439838, by rfl⟩ : syracuseStep 3839569 = 2879677) B2879677
theorem B20477701 : Blo 2129435 20477701 := bstep (se 4 (by rfl) ⟨1919784, by rfl⟩ : syracuseStep 20477701 = 3839569) B3839569
theorem B27303601 : Blo 2129435 27303601 := bstep (se 2 (by rfl) ⟨10238850, by rfl⟩ : syracuseStep 27303601 = 20477701) B20477701
theorem B36404801 : Blo 2129435 36404801 := bstep (se 2 (by rfl) ⟨13651800, by rfl⟩ : syracuseStep 36404801 = 27303601) B27303601
theorem B24269867 : Blo 2129435 24269867 := bstep (se 1 (by rfl) ⟨18202400, by rfl⟩ : syracuseStep 24269867 = 36404801) B36404801
theorem B16179911 : Blo 2129435 16179911 := bstep (se 1 (by rfl) ⟨12134933, by rfl⟩ : syracuseStep 16179911 = 24269867) B24269867
theorem B10786607 : Blo 2129435 10786607 := bstep (se 1 (by rfl) ⟨8089955, by rfl⟩ : syracuseStep 10786607 = 16179911) B16179911
theorem B7191071 : Blo 2129435 7191071 := bstep (se 1 (by rfl) ⟨5393303, by rfl⟩ : syracuseStep 7191071 = 10786607) B10786607
theorem B4794047 : Blo 2129435 4794047 := bstep (se 1 (by rfl) ⟨3595535, by rfl⟩ : syracuseStep 4794047 = 7191071) B7191071
theorem B3196031 : Blo 2129435 3196031 := bstep (se 1 (by rfl) ⟨2397023, by rfl⟩ : syracuseStep 3196031 = 4794047) B4794047
theorem B2130687 : Blo 2129435 2130687 := bstep (se 1 (by rfl) ⟨1598015, by rfl⟩ : syracuseStep 2130687 = 3196031) B3196031
theorem B3196037 : Blo 2129435 3196037 := bbase (se 4 (by rfl) ⟨299628, by rfl⟩ : syracuseStep 3196037 = 599257) (by norm_num)
theorem B2130691 : Blo 2129435 2130691 := bstep (se 1 (by rfl) ⟨1598018, by rfl⟩ : syracuseStep 2130691 = 3196037) B3196037
theorem B3595549 : Blo 2129435 3595549 := bbase (se 3 (by rfl) ⟨674165, by rfl⟩ : syracuseStep 3595549 = 1348331) (by norm_num)
theorem B4794065 : Blo 2129435 4794065 := bstep (se 2 (by rfl) ⟨1797774, by rfl⟩ : syracuseStep 4794065 = 3595549) B3595549
theorem B3196043 : Blo 2129435 3196043 := bstep (se 1 (by rfl) ⟨2397032, by rfl⟩ : syracuseStep 3196043 = 4794065) B4794065
theorem B2130695 : Blo 2129435 2130695 := bstep (se 1 (by rfl) ⟨1598021, by rfl⟩ : syracuseStep 2130695 = 3196043) B3196043
theorem B2397037 : Blo 2129435 2397037 := bbase (se 3 (by rfl) ⟨449444, by rfl⟩ : syracuseStep 2397037 = 898889) (by norm_num)
theorem B3196049 : Blo 2129435 3196049 := bstep (se 2 (by rfl) ⟨1198518, by rfl⟩ : syracuseStep 3196049 = 2397037) B2397037
theorem B2130699 : Blo 2129435 2130699 := bstep (se 1 (by rfl) ⟨1598024, by rfl⟩ : syracuseStep 2130699 = 3196049) B3196049
theorem B7191125 : Blo 2129435 7191125 := bbase (se 8 (by rfl) ⟨42135, by rfl⟩ : syracuseStep 7191125 = 84271) (by norm_num)
theorem B4794083 : Blo 2129435 4794083 := bstep (se 1 (by rfl) ⟨3595562, by rfl⟩ : syracuseStep 4794083 = 7191125) B7191125
theorem B3196055 : Blo 2129435 3196055 := bstep (se 1 (by rfl) ⟨2397041, by rfl⟩ : syracuseStep 3196055 = 4794083) B4794083
theorem B2130703 : Blo 2129435 2130703 := bstep (se 1 (by rfl) ⟨1598027, by rfl⟩ : syracuseStep 2130703 = 3196055) B3196055
theorem B3196061 : Blo 2129435 3196061 := bbase (se 3 (by rfl) ⟨599261, by rfl⟩ : syracuseStep 3196061 = 1198523) (by norm_num)
theorem B2130707 : Blo 2129435 2130707 := bstep (se 1 (by rfl) ⟨1598030, by rfl⟩ : syracuseStep 2130707 = 3196061) B3196061
theorem B4794101 : Blo 2129435 4794101 := bbase (se 5 (by rfl) ⟨224723, by rfl⟩ : syracuseStep 4794101 = 449447) (by norm_num)
theorem B3196067 : Blo 2129435 3196067 := bstep (se 1 (by rfl) ⟨2397050, by rfl⟩ : syracuseStep 3196067 = 4794101) B4794101
theorem B2130711 : Blo 2129435 2130711 := bstep (se 1 (by rfl) ⟨1598033, by rfl⟩ : syracuseStep 2130711 = 3196067) B3196067
theorem B4319573 : Blo 2129435 4319573 := bbase (se 10 (by rfl) ⟨6327, by rfl⟩ : syracuseStep 4319573 = 12655) (by norm_num)
theorem B11518861 : Blo 2129435 11518861 := bstep (se 3 (by rfl) ⟨2159786, by rfl⟩ : syracuseStep 11518861 = 4319573) B4319573
theorem B15358481 : Blo 2129435 15358481 := bstep (se 2 (by rfl) ⟨5759430, by rfl⟩ : syracuseStep 15358481 = 11518861) B11518861
theorem B10238987 : Blo 2129435 10238987 := bstep (se 1 (by rfl) ⟨7679240, by rfl⟩ : syracuseStep 10238987 = 15358481) B15358481
theorem B27303965 : Blo 2129435 27303965 := bstep (se 3 (by rfl) ⟨5119493, by rfl⟩ : syracuseStep 27303965 = 10238987) B10238987
theorem B18202643 : Blo 2129435 18202643 := bstep (se 1 (by rfl) ⟨13651982, by rfl⟩ : syracuseStep 18202643 = 27303965) B27303965
theorem B12135095 : Blo 2129435 12135095 := bstep (se 1 (by rfl) ⟨9101321, by rfl⟩ : syracuseStep 12135095 = 18202643) B18202643
theorem B8090063 : Blo 2129435 8090063 := bstep (se 1 (by rfl) ⟨6067547, by rfl⟩ : syracuseStep 8090063 = 12135095) B12135095
theorem B5393375 : Blo 2129435 5393375 := bstep (se 1 (by rfl) ⟨4045031, by rfl⟩ : syracuseStep 5393375 = 8090063) B8090063
theorem B3595583 : Blo 2129435 3595583 := bstep (se 1 (by rfl) ⟨2696687, by rfl⟩ : syracuseStep 3595583 = 5393375) B5393375
theorem B2397055 : Blo 2129435 2397055 := bstep (se 1 (by rfl) ⟨1797791, by rfl⟩ : syracuseStep 2397055 = 3595583) B3595583
theorem B3196073 : Blo 2129435 3196073 := bstep (se 2 (by rfl) ⟨1198527, by rfl⟩ : syracuseStep 3196073 = 2397055) B2397055
theorem B2130715 : Blo 2129435 2130715 := bstep (se 1 (by rfl) ⟨1598036, by rfl⟩ : syracuseStep 2130715 = 3196073) B3196073
theorem B4550669 : Blo 2129435 4550669 := bbase (se 3 (by rfl) ⟨853250, by rfl⟩ : syracuseStep 4550669 = 1706501) (by norm_num)
theorem B3033779 : Blo 2129435 3033779 := bstep (se 1 (by rfl) ⟨2275334, by rfl⟩ : syracuseStep 3033779 = 4550669) B4550669
theorem B8090077 : Blo 2129435 8090077 := bstep (se 3 (by rfl) ⟨1516889, by rfl⟩ : syracuseStep 8090077 = 3033779) B3033779
theorem B10786769 : Blo 2129435 10786769 := bstep (se 2 (by rfl) ⟨4045038, by rfl⟩ : syracuseStep 10786769 = 8090077) B8090077
theorem B7191179 : Blo 2129435 7191179 := bstep (se 1 (by rfl) ⟨5393384, by rfl⟩ : syracuseStep 7191179 = 10786769) B10786769
theorem B4794119 : Blo 2129435 4794119 := bstep (se 1 (by rfl) ⟨3595589, by rfl⟩ : syracuseStep 4794119 = 7191179) B7191179
theorem B3196079 : Blo 2129435 3196079 := bstep (se 1 (by rfl) ⟨2397059, by rfl⟩ : syracuseStep 3196079 = 4794119) B4794119
theorem B2130719 : Blo 2129435 2130719 := bstep (se 1 (by rfl) ⟨1598039, by rfl⟩ : syracuseStep 2130719 = 3196079) B3196079
theorem B3196085 : Blo 2129435 3196085 := bbase (se 5 (by rfl) ⟨149816, by rfl⟩ : syracuseStep 3196085 = 299633) (by norm_num)
theorem B2130723 : Blo 2129435 2130723 := bstep (se 1 (by rfl) ⟨1598042, by rfl⟩ : syracuseStep 2130723 = 3196085) B3196085
theorem B5393405 : Blo 2129435 5393405 := bbase (se 3 (by rfl) ⟨1011263, by rfl⟩ : syracuseStep 5393405 = 2022527) (by norm_num)
theorem B3595603 : Blo 2129435 3595603 := bstep (se 1 (by rfl) ⟨2696702, by rfl⟩ : syracuseStep 3595603 = 5393405) B5393405
theorem B4794137 : Blo 2129435 4794137 := bstep (se 2 (by rfl) ⟨1797801, by rfl⟩ : syracuseStep 4794137 = 3595603) B3595603
theorem B3196091 : Blo 2129435 3196091 := bstep (se 1 (by rfl) ⟨2397068, by rfl⟩ : syracuseStep 3196091 = 4794137) B4794137
theorem B2130727 : Blo 2129435 2130727 := bstep (se 1 (by rfl) ⟨1598045, by rfl⟩ : syracuseStep 2130727 = 3196091) B3196091
theorem B2397073 : Blo 2129435 2397073 := bbase (se 2 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 2397073 = 1797805) (by norm_num)
theorem B3196097 : Blo 2129435 3196097 := bstep (se 2 (by rfl) ⟨1198536, by rfl⟩ : syracuseStep 3196097 = 2397073) B2397073
theorem B2130731 : Blo 2129435 2130731 := bstep (se 1 (by rfl) ⟨1598048, by rfl⟩ : syracuseStep 2130731 = 3196097) B3196097
theorem B4045069 : Blo 2129435 4045069 := bbase (se 3 (by rfl) ⟨758450, by rfl⟩ : syracuseStep 4045069 = 1516901) (by norm_num)
theorem B5393425 : Blo 2129435 5393425 := bstep (se 2 (by rfl) ⟨2022534, by rfl⟩ : syracuseStep 5393425 = 4045069) B4045069
theorem B7191233 : Blo 2129435 7191233 := bstep (se 2 (by rfl) ⟨2696712, by rfl⟩ : syracuseStep 7191233 = 5393425) B5393425
theorem B4794155 : Blo 2129435 4794155 := bstep (se 1 (by rfl) ⟨3595616, by rfl⟩ : syracuseStep 4794155 = 7191233) B7191233
theorem B3196103 : Blo 2129435 3196103 := bstep (se 1 (by rfl) ⟨2397077, by rfl⟩ : syracuseStep 3196103 = 4794155) B4794155
theorem B2130735 : Blo 2129435 2130735 := bstep (se 1 (by rfl) ⟨1598051, by rfl⟩ : syracuseStep 2130735 = 3196103) B3196103
theorem B3196109 : Blo 2129435 3196109 := bbase (se 3 (by rfl) ⟨599270, by rfl⟩ : syracuseStep 3196109 = 1198541) (by norm_num)
theorem B2130739 : Blo 2129435 2130739 := bstep (se 1 (by rfl) ⟨1598054, by rfl⟩ : syracuseStep 2130739 = 3196109) B3196109
theorem B4794173 : Blo 2129435 4794173 := bbase (se 3 (by rfl) ⟨898907, by rfl⟩ : syracuseStep 4794173 = 1797815) (by norm_num)
theorem B3196115 : Blo 2129435 3196115 := bstep (se 1 (by rfl) ⟨2397086, by rfl⟩ : syracuseStep 3196115 = 4794173) B4794173
theorem B2130743 : Blo 2129435 2130743 := bstep (se 1 (by rfl) ⟨1598057, by rfl⟩ : syracuseStep 2130743 = 3196115) B3196115
theorem B3595637 : Blo 2129435 3595637 := bbase (se 5 (by rfl) ⟨168545, by rfl⟩ : syracuseStep 3595637 = 337091) (by norm_num)
theorem B2397091 : Blo 2129435 2397091 := bstep (se 1 (by rfl) ⟨1797818, by rfl⟩ : syracuseStep 2397091 = 3595637) B3595637
theorem B3196121 : Blo 2129435 3196121 := bstep (se 2 (by rfl) ⟨1198545, by rfl⟩ : syracuseStep 3196121 = 2397091) B2397091
theorem B2130747 : Blo 2129435 2130747 := bstep (se 1 (by rfl) ⟨1598060, by rfl⟩ : syracuseStep 2130747 = 3196121) B3196121
theorem B3413053 : Blo 2129435 3413053 := bbase (se 3 (by rfl) ⟨639947, by rfl⟩ : syracuseStep 3413053 = 1279895) (by norm_num)
theorem B4550737 : Blo 2129435 4550737 := bstep (se 2 (by rfl) ⟨1706526, by rfl⟩ : syracuseStep 4550737 = 3413053) B3413053
theorem B6067649 : Blo 2129435 6067649 := bstep (se 2 (by rfl) ⟨2275368, by rfl⟩ : syracuseStep 6067649 = 4550737) B4550737
theorem B16180397 : Blo 2129435 16180397 := bstep (se 3 (by rfl) ⟨3033824, by rfl⟩ : syracuseStep 16180397 = 6067649) B6067649
theorem B10786931 : Blo 2129435 10786931 := bstep (se 1 (by rfl) ⟨8090198, by rfl⟩ : syracuseStep 10786931 = 16180397) B16180397
theorem B7191287 : Blo 2129435 7191287 := bstep (se 1 (by rfl) ⟨5393465, by rfl⟩ : syracuseStep 7191287 = 10786931) B10786931
theorem B4794191 : Blo 2129435 4794191 := bstep (se 1 (by rfl) ⟨3595643, by rfl⟩ : syracuseStep 4794191 = 7191287) B7191287
theorem B3196127 : Blo 2129435 3196127 := bstep (se 1 (by rfl) ⟨2397095, by rfl⟩ : syracuseStep 3196127 = 4794191) B4794191
theorem B2130751 : Blo 2129435 2130751 := bstep (se 1 (by rfl) ⟨1598063, by rfl⟩ : syracuseStep 2130751 = 3196127) B3196127
theorem B3196133 : Blo 2129435 3196133 := bbase (se 4 (by rfl) ⟨299637, by rfl⟩ : syracuseStep 3196133 = 599275) (by norm_num)
theorem B2130755 : Blo 2129435 2130755 := bstep (se 1 (by rfl) ⟨1598066, by rfl⟩ : syracuseStep 2130755 = 3196133) B3196133
theorem B6826133 : Blo 2129435 6826133 := bbase (se 6 (by rfl) ⟨159987, by rfl⟩ : syracuseStep 6826133 = 319975) (by norm_num)
theorem B4550755 : Blo 2129435 4550755 := bstep (se 1 (by rfl) ⟨3413066, by rfl⟩ : syracuseStep 4550755 = 6826133) B6826133
theorem B6067673 : Blo 2129435 6067673 := bstep (se 2 (by rfl) ⟨2275377, by rfl⟩ : syracuseStep 6067673 = 4550755) B4550755
theorem B4045115 : Blo 2129435 4045115 := bstep (se 1 (by rfl) ⟨3033836, by rfl⟩ : syracuseStep 4045115 = 6067673) B6067673
theorem B2696743 : Blo 2129435 2696743 := bstep (se 1 (by rfl) ⟨2022557, by rfl⟩ : syracuseStep 2696743 = 4045115) B4045115
theorem B3595657 : Blo 2129435 3595657 := bstep (se 2 (by rfl) ⟨1348371, by rfl⟩ : syracuseStep 3595657 = 2696743) B2696743
theorem B4794209 : Blo 2129435 4794209 := bstep (se 2 (by rfl) ⟨1797828, by rfl⟩ : syracuseStep 4794209 = 3595657) B3595657
theorem B3196139 : Blo 2129435 3196139 := bstep (se 1 (by rfl) ⟨2397104, by rfl⟩ : syracuseStep 3196139 = 4794209) B4794209
theorem B2130759 : Blo 2129435 2130759 := bstep (se 1 (by rfl) ⟨1598069, by rfl⟩ : syracuseStep 2130759 = 3196139) B3196139
theorem B2397109 : Blo 2129435 2397109 := bbase (se 5 (by rfl) ⟨112364, by rfl⟩ : syracuseStep 2397109 = 224729) (by norm_num)
theorem B3196145 : Blo 2129435 3196145 := bstep (se 2 (by rfl) ⟨1198554, by rfl⟩ : syracuseStep 3196145 = 2397109) B2397109
theorem B2130763 : Blo 2129435 2130763 := bstep (se 1 (by rfl) ⟨1598072, by rfl⟩ : syracuseStep 2130763 = 3196145) B3196145
theorem B2696753 : Blo 2129435 2696753 := bbase (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) (by norm_num)
theorem B7191341 : Blo 2129435 7191341 := bstep (se 3 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 7191341 = 2696753) B2696753
theorem B4794227 : Blo 2129435 4794227 := bstep (se 1 (by rfl) ⟨3595670, by rfl⟩ : syracuseStep 4794227 = 7191341) B7191341
theorem B3196151 : Blo 2129435 3196151 := bstep (se 1 (by rfl) ⟨2397113, by rfl⟩ : syracuseStep 3196151 = 4794227) B4794227
theorem B2130767 : Blo 2129435 2130767 := bstep (se 1 (by rfl) ⟨1598075, by rfl⟩ : syracuseStep 2130767 = 3196151) B3196151
theorem B3196157 : Blo 2129435 3196157 := bbase (se 3 (by rfl) ⟨599279, by rfl⟩ : syracuseStep 3196157 = 1198559) (by norm_num)
theorem B2130771 : Blo 2129435 2130771 := bstep (se 1 (by rfl) ⟨1598078, by rfl⟩ : syracuseStep 2130771 = 3196157) B3196157
theorem B4794245 : Blo 2129435 4794245 := bbase (se 4 (by rfl) ⟨449460, by rfl⟩ : syracuseStep 4794245 = 898921) (by norm_num)
theorem B3196163 : Blo 2129435 3196163 := bstep (se 1 (by rfl) ⟨2397122, by rfl⟩ : syracuseStep 3196163 = 4794245) B4794245
theorem B2130775 : Blo 2129435 2130775 := bstep (se 1 (by rfl) ⟨1598081, by rfl⟩ : syracuseStep 2130775 = 3196163) B3196163
theorem B4859669 : Blo 2129435 4859669 := bbase (se 6 (by rfl) ⟨113898, by rfl⟩ : syracuseStep 4859669 = 227797) (by norm_num)
theorem B3239779 : Blo 2129435 3239779 := bstep (se 1 (by rfl) ⟨2429834, by rfl⟩ : syracuseStep 3239779 = 4859669) B4859669
theorem B4319705 : Blo 2129435 4319705 := bstep (se 2 (by rfl) ⟨1619889, by rfl⟩ : syracuseStep 4319705 = 3239779) B3239779
theorem B2879803 : Blo 2129435 2879803 := bstep (se 1 (by rfl) ⟨2159852, by rfl⟩ : syracuseStep 2879803 = 4319705) B4319705
theorem B3839737 : Blo 2129435 3839737 := bstep (se 2 (by rfl) ⟨1439901, by rfl⟩ : syracuseStep 3839737 = 2879803) B2879803
theorem B5119649 : Blo 2129435 5119649 := bstep (se 2 (by rfl) ⟨1919868, by rfl⟩ : syracuseStep 5119649 = 3839737) B3839737
theorem B3413099 : Blo 2129435 3413099 := bstep (se 1 (by rfl) ⟨2559824, by rfl⟩ : syracuseStep 3413099 = 5119649) B5119649
theorem B2275399 : Blo 2129435 2275399 := bstep (se 1 (by rfl) ⟨1706549, by rfl⟩ : syracuseStep 2275399 = 3413099) B3413099
theorem B3033865 : Blo 2129435 3033865 := bstep (se 2 (by rfl) ⟨1137699, by rfl⟩ : syracuseStep 3033865 = 2275399) B2275399
theorem B4045153 : Blo 2129435 4045153 := bstep (se 2 (by rfl) ⟨1516932, by rfl⟩ : syracuseStep 4045153 = 3033865) B3033865
theorem B5393537 : Blo 2129435 5393537 := bstep (se 2 (by rfl) ⟨2022576, by rfl⟩ : syracuseStep 5393537 = 4045153) B4045153
theorem B3595691 : Blo 2129435 3595691 := bstep (se 1 (by rfl) ⟨2696768, by rfl⟩ : syracuseStep 3595691 = 5393537) B5393537
theorem B2397127 : Blo 2129435 2397127 := bstep (se 1 (by rfl) ⟨1797845, by rfl⟩ : syracuseStep 2397127 = 3595691) B3595691
theorem B3196169 : Blo 2129435 3196169 := bstep (se 2 (by rfl) ⟨1198563, by rfl⟩ : syracuseStep 3196169 = 2397127) B2397127
theorem B2130779 : Blo 2129435 2130779 := bstep (se 1 (by rfl) ⟨1598084, by rfl⟩ : syracuseStep 2130779 = 3196169) B3196169
theorem B10787093 : Blo 2129435 10787093 := bbase (se 6 (by rfl) ⟨252822, by rfl⟩ : syracuseStep 10787093 = 505645) (by norm_num)
theorem B7191395 : Blo 2129435 7191395 := bstep (se 1 (by rfl) ⟨5393546, by rfl⟩ : syracuseStep 7191395 = 10787093) B10787093
theorem B4794263 : Blo 2129435 4794263 := bstep (se 1 (by rfl) ⟨3595697, by rfl⟩ : syracuseStep 4794263 = 7191395) B7191395
theorem B3196175 : Blo 2129435 3196175 := bstep (se 1 (by rfl) ⟨2397131, by rfl⟩ : syracuseStep 3196175 = 4794263) B4794263
theorem B2130783 : Blo 2129435 2130783 := bstep (se 1 (by rfl) ⟨1598087, by rfl⟩ : syracuseStep 2130783 = 3196175) B3196175
theorem B3196181 : Blo 2129435 3196181 := bbase (se 6 (by rfl) ⟨74910, by rfl⟩ : syracuseStep 3196181 = 149821) (by norm_num)
theorem B2130787 : Blo 2129435 2130787 := bstep (se 1 (by rfl) ⟨1598090, by rfl⟩ : syracuseStep 2130787 = 3196181) B3196181
theorem B3283997 : Blo 2129435 3283997 := bbase (se 3 (by rfl) ⟨615749, by rfl⟩ : syracuseStep 3283997 = 1231499) (by norm_num)
theorem B8757325 : Blo 2129435 8757325 := bstep (se 3 (by rfl) ⟨1641998, by rfl⟩ : syracuseStep 8757325 = 3283997) B3283997
theorem B11676433 : Blo 2129435 11676433 := bstep (se 2 (by rfl) ⟨4378662, by rfl⟩ : syracuseStep 11676433 = 8757325) B8757325
theorem B15568577 : Blo 2129435 15568577 := bstep (se 2 (by rfl) ⟨5838216, by rfl⟩ : syracuseStep 15568577 = 11676433) B11676433
theorem B10379051 : Blo 2129435 10379051 := bstep (se 1 (by rfl) ⟨7784288, by rfl⟩ : syracuseStep 10379051 = 15568577) B15568577
theorem B6919367 : Blo 2129435 6919367 := bstep (se 1 (by rfl) ⟨5189525, by rfl⟩ : syracuseStep 6919367 = 10379051) B10379051
theorem B18451645 : Blo 2129435 18451645 := bstep (se 3 (by rfl) ⟨3459683, by rfl⟩ : syracuseStep 18451645 = 6919367) B6919367
theorem B98408773 : Blo 2129435 98408773 := bstep (se 4 (by rfl) ⟨9225822, by rfl⟩ : syracuseStep 98408773 = 18451645) B18451645
theorem B131211697 : Blo 2129435 131211697 := bstep (se 2 (by rfl) ⟨49204386, by rfl⟩ : syracuseStep 131211697 = 98408773) B98408773
theorem B174948929 : Blo 2129435 174948929 := bstep (se 2 (by rfl) ⟨65605848, by rfl⟩ : syracuseStep 174948929 = 131211697) B131211697
theorem B116632619 : Blo 2129435 116632619 := bstep (se 1 (by rfl) ⟨87474464, by rfl⟩ : syracuseStep 116632619 = 174948929) B174948929
theorem B77755079 : Blo 2129435 77755079 := bstep (se 1 (by rfl) ⟨58316309, by rfl⟩ : syracuseStep 77755079 = 116632619) B116632619
theorem B51836719 : Blo 2129435 51836719 := bstep (se 1 (by rfl) ⟨38877539, by rfl⟩ : syracuseStep 51836719 = 77755079) B77755079
theorem B69115625 : Blo 2129435 69115625 := bstep (se 2 (by rfl) ⟨25918359, by rfl⟩ : syracuseStep 69115625 = 51836719) B51836719
theorem B46077083 : Blo 2129435 46077083 := bstep (se 1 (by rfl) ⟨34557812, by rfl⟩ : syracuseStep 46077083 = 69115625) B69115625
theorem B30718055 : Blo 2129435 30718055 := bstep (se 1 (by rfl) ⟨23038541, by rfl⟩ : syracuseStep 30718055 = 46077083) B46077083
theorem B20478703 : Blo 2129435 20478703 := bstep (se 1 (by rfl) ⟨15359027, by rfl⟩ : syracuseStep 20478703 = 30718055) B30718055
theorem B27304937 : Blo 2129435 27304937 := bstep (se 2 (by rfl) ⟨10239351, by rfl⟩ : syracuseStep 27304937 = 20478703) B20478703
theorem B18203291 : Blo 2129435 18203291 := bstep (se 1 (by rfl) ⟨13652468, by rfl⟩ : syracuseStep 18203291 = 27304937) B27304937
theorem B12135527 : Blo 2129435 12135527 := bstep (se 1 (by rfl) ⟨9101645, by rfl⟩ : syracuseStep 12135527 = 18203291) B18203291
theorem B8090351 : Blo 2129435 8090351 := bstep (se 1 (by rfl) ⟨6067763, by rfl⟩ : syracuseStep 8090351 = 12135527) B12135527
theorem B5393567 : Blo 2129435 5393567 := bstep (se 1 (by rfl) ⟨4045175, by rfl⟩ : syracuseStep 5393567 = 8090351) B8090351
theorem B3595711 : Blo 2129435 3595711 := bstep (se 1 (by rfl) ⟨2696783, by rfl⟩ : syracuseStep 3595711 = 5393567) B5393567
theorem B4794281 : Blo 2129435 4794281 := bstep (se 2 (by rfl) ⟨1797855, by rfl⟩ : syracuseStep 4794281 = 3595711) B3595711
theorem B3196187 : Blo 2129435 3196187 := bstep (se 1 (by rfl) ⟨2397140, by rfl⟩ : syracuseStep 3196187 = 4794281) B4794281
theorem B2130791 : Blo 2129435 2130791 := bstep (se 1 (by rfl) ⟨1598093, by rfl⟩ : syracuseStep 2130791 = 3196187) B3196187
theorem B2397145 : Blo 2129435 2397145 := bbase (se 2 (by rfl) ⟨898929, by rfl⟩ : syracuseStep 2397145 = 1797859) (by norm_num)
theorem B3196193 : Blo 2129435 3196193 := bstep (se 2 (by rfl) ⟨1198572, by rfl⟩ : syracuseStep 3196193 = 2397145) B2397145
theorem B2130795 : Blo 2129435 2130795 := bstep (se 1 (by rfl) ⟨1598096, by rfl⟩ : syracuseStep 2130795 = 3196193) B3196193
theorem B3033893 : Blo 2129435 3033893 := bbase (se 4 (by rfl) ⟨284427, by rfl⟩ : syracuseStep 3033893 = 568855) (by norm_num)
theorem B8090381 : Blo 2129435 8090381 := bstep (se 3 (by rfl) ⟨1516946, by rfl⟩ : syracuseStep 8090381 = 3033893) B3033893
theorem B5393587 : Blo 2129435 5393587 := bstep (se 1 (by rfl) ⟨4045190, by rfl⟩ : syracuseStep 5393587 = 8090381) B8090381
theorem B7191449 : Blo 2129435 7191449 := bstep (se 2 (by rfl) ⟨2696793, by rfl⟩ : syracuseStep 7191449 = 5393587) B5393587
theorem B4794299 : Blo 2129435 4794299 := bstep (se 1 (by rfl) ⟨3595724, by rfl⟩ : syracuseStep 4794299 = 7191449) B7191449
theorem B3196199 : Blo 2129435 3196199 := bstep (se 1 (by rfl) ⟨2397149, by rfl⟩ : syracuseStep 3196199 = 4794299) B4794299
theorem B2130799 : Blo 2129435 2130799 := bstep (se 1 (by rfl) ⟨1598099, by rfl⟩ : syracuseStep 2130799 = 3196199) B3196199
theorem B3196205 : Blo 2129435 3196205 := bbase (se 3 (by rfl) ⟨599288, by rfl⟩ : syracuseStep 3196205 = 1198577) (by norm_num)
theorem B2130803 : Blo 2129435 2130803 := bstep (se 1 (by rfl) ⟨1598102, by rfl⟩ : syracuseStep 2130803 = 3196205) B3196205
theorem B4794317 : Blo 2129435 4794317 := bbase (se 3 (by rfl) ⟨898934, by rfl⟩ : syracuseStep 4794317 = 1797869) (by norm_num)
theorem B3196211 : Blo 2129435 3196211 := bstep (se 1 (by rfl) ⟨2397158, by rfl⟩ : syracuseStep 3196211 = 4794317) B4794317
theorem B2130807 : Blo 2129435 2130807 := bstep (se 1 (by rfl) ⟨1598105, by rfl⟩ : syracuseStep 2130807 = 3196211) B3196211
theorem B2696809 : Blo 2129435 2696809 := bbase (se 2 (by rfl) ⟨1011303, by rfl⟩ : syracuseStep 2696809 = 2022607) (by norm_num)
theorem B3595745 : Blo 2129435 3595745 := bstep (se 2 (by rfl) ⟨1348404, by rfl⟩ : syracuseStep 3595745 = 2696809) B2696809
theorem B2397163 : Blo 2129435 2397163 := bstep (se 1 (by rfl) ⟨1797872, by rfl⟩ : syracuseStep 2397163 = 3595745) B3595745
theorem B3196217 : Blo 2129435 3196217 := bstep (se 2 (by rfl) ⟨1198581, by rfl⟩ : syracuseStep 3196217 = 2397163) B2397163
theorem B2130811 : Blo 2129435 2130811 := bstep (se 1 (by rfl) ⟨1598108, by rfl⟩ : syracuseStep 2130811 = 3196217) B3196217
theorem B5119733 : Blo 2129435 5119733 := bbase (se 5 (by rfl) ⟨239987, by rfl⟩ : syracuseStep 5119733 = 479975) (by norm_num)
theorem B13652621 : Blo 2129435 13652621 := bstep (se 3 (by rfl) ⟨2559866, by rfl⟩ : syracuseStep 13652621 = 5119733) B5119733
theorem B9101747 : Blo 2129435 9101747 := bstep (se 1 (by rfl) ⟨6826310, by rfl⟩ : syracuseStep 9101747 = 13652621) B13652621
theorem B24271325 : Blo 2129435 24271325 := bstep (se 3 (by rfl) ⟨4550873, by rfl⟩ : syracuseStep 24271325 = 9101747) B9101747
theorem B16180883 : Blo 2129435 16180883 := bstep (se 1 (by rfl) ⟨12135662, by rfl⟩ : syracuseStep 16180883 = 24271325) B24271325
theorem B10787255 : Blo 2129435 10787255 := bstep (se 1 (by rfl) ⟨8090441, by rfl⟩ : syracuseStep 10787255 = 16180883) B16180883
theorem B7191503 : Blo 2129435 7191503 := bstep (se 1 (by rfl) ⟨5393627, by rfl⟩ : syracuseStep 7191503 = 10787255) B10787255
theorem B4794335 : Blo 2129435 4794335 := bstep (se 1 (by rfl) ⟨3595751, by rfl⟩ : syracuseStep 4794335 = 7191503) B7191503
theorem B3196223 : Blo 2129435 3196223 := bstep (se 1 (by rfl) ⟨2397167, by rfl⟩ : syracuseStep 3196223 = 4794335) B4794335
theorem B2130815 : Blo 2129435 2130815 := bstep (se 1 (by rfl) ⟨1598111, by rfl⟩ : syracuseStep 2130815 = 3196223) B3196223
theorem B3196229 : Blo 2129435 3196229 := bbase (se 4 (by rfl) ⟨299646, by rfl⟩ : syracuseStep 3196229 = 599293) (by norm_num)
theorem B2130819 : Blo 2129435 2130819 := bstep (se 1 (by rfl) ⟨1598114, by rfl⟩ : syracuseStep 2130819 = 3196229) B3196229
theorem B3595765 : Blo 2129435 3595765 := bbase (se 5 (by rfl) ⟨168551, by rfl⟩ : syracuseStep 3595765 = 337103) (by norm_num)
theorem B4794353 : Blo 2129435 4794353 := bstep (se 2 (by rfl) ⟨1797882, by rfl⟩ : syracuseStep 4794353 = 3595765) B3595765
theorem B3196235 : Blo 2129435 3196235 := bstep (se 1 (by rfl) ⟨2397176, by rfl⟩ : syracuseStep 3196235 = 4794353) B4794353
theorem B2130823 : Blo 2129435 2130823 := bstep (se 1 (by rfl) ⟨1598117, by rfl⟩ : syracuseStep 2130823 = 3196235) B3196235
theorem B2397181 : Blo 2129435 2397181 := bbase (se 3 (by rfl) ⟨449471, by rfl⟩ : syracuseStep 2397181 = 898943) (by norm_num)
theorem B3196241 : Blo 2129435 3196241 := bstep (se 2 (by rfl) ⟨1198590, by rfl⟩ : syracuseStep 3196241 = 2397181) B2397181
theorem B2130827 : Blo 2129435 2130827 := bstep (se 1 (by rfl) ⟨1598120, by rfl⟩ : syracuseStep 2130827 = 3196241) B3196241
theorem B7191557 : Blo 2129435 7191557 := bbase (se 4 (by rfl) ⟨674208, by rfl⟩ : syracuseStep 7191557 = 1348417) (by norm_num)
theorem B4794371 : Blo 2129435 4794371 := bstep (se 1 (by rfl) ⟨3595778, by rfl⟩ : syracuseStep 4794371 = 7191557) B7191557
theorem B3196247 : Blo 2129435 3196247 := bstep (se 1 (by rfl) ⟨2397185, by rfl⟩ : syracuseStep 3196247 = 4794371) B4794371
theorem B2130831 : Blo 2129435 2130831 := bstep (se 1 (by rfl) ⟨1598123, by rfl⟩ : syracuseStep 2130831 = 3196247) B3196247
theorem B3196253 : Blo 2129435 3196253 := bbase (se 3 (by rfl) ⟨599297, by rfl⟩ : syracuseStep 3196253 = 1198595) (by norm_num)
theorem B2130835 : Blo 2129435 2130835 := bstep (se 1 (by rfl) ⟨1598126, by rfl⟩ : syracuseStep 2130835 = 3196253) B3196253
theorem B4794389 : Blo 2129435 4794389 := bbase (se 6 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 4794389 = 224737) (by norm_num)
theorem B3196259 : Blo 2129435 3196259 := bstep (se 1 (by rfl) ⟨2397194, by rfl⟩ : syracuseStep 3196259 = 4794389) B4794389
theorem B2130839 : Blo 2129435 2130839 := bstep (se 1 (by rfl) ⟨1598129, by rfl⟩ : syracuseStep 2130839 = 3196259) B3196259
theorem B8090549 : Blo 2129435 8090549 := bbase (se 5 (by rfl) ⟨379244, by rfl⟩ : syracuseStep 8090549 = 758489) (by norm_num)
theorem B5393699 : Blo 2129435 5393699 := bstep (se 1 (by rfl) ⟨4045274, by rfl⟩ : syracuseStep 5393699 = 8090549) B8090549
theorem B3595799 : Blo 2129435 3595799 := bstep (se 1 (by rfl) ⟨2696849, by rfl⟩ : syracuseStep 3595799 = 5393699) B5393699
theorem B2397199 : Blo 2129435 2397199 := bstep (se 1 (by rfl) ⟨1797899, by rfl⟩ : syracuseStep 2397199 = 3595799) B3595799
theorem B3196265 : Blo 2129435 3196265 := bstep (se 2 (by rfl) ⟨1198599, by rfl⟩ : syracuseStep 3196265 = 2397199) B2397199
theorem B2130843 : Blo 2129435 2130843 := bstep (se 1 (by rfl) ⟨1598132, by rfl⟩ : syracuseStep 2130843 = 3196265) B3196265
theorem B7679717 : Blo 2129435 7679717 := bbase (se 4 (by rfl) ⟨719973, by rfl⟩ : syracuseStep 7679717 = 1439947) (by norm_num)
theorem B5119811 : Blo 2129435 5119811 := bstep (se 1 (by rfl) ⟨3839858, by rfl⟩ : syracuseStep 5119811 = 7679717) B7679717
theorem B3413207 : Blo 2129435 3413207 := bstep (se 1 (by rfl) ⟨2559905, by rfl⟩ : syracuseStep 3413207 = 5119811) B5119811
theorem B2275471 : Blo 2129435 2275471 := bstep (se 1 (by rfl) ⟨1706603, by rfl⟩ : syracuseStep 2275471 = 3413207) B3413207
theorem B12135845 : Blo 2129435 12135845 := bstep (se 4 (by rfl) ⟨1137735, by rfl⟩ : syracuseStep 12135845 = 2275471) B2275471
theorem B8090563 : Blo 2129435 8090563 := bstep (se 1 (by rfl) ⟨6067922, by rfl⟩ : syracuseStep 8090563 = 12135845) B12135845
theorem B10787417 : Blo 2129435 10787417 := bstep (se 2 (by rfl) ⟨4045281, by rfl⟩ : syracuseStep 10787417 = 8090563) B8090563
theorem B7191611 : Blo 2129435 7191611 := bstep (se 1 (by rfl) ⟨5393708, by rfl⟩ : syracuseStep 7191611 = 10787417) B10787417
theorem B4794407 : Blo 2129435 4794407 := bstep (se 1 (by rfl) ⟨3595805, by rfl⟩ : syracuseStep 4794407 = 7191611) B7191611
theorem B3196271 : Blo 2129435 3196271 := bstep (se 1 (by rfl) ⟨2397203, by rfl⟩ : syracuseStep 3196271 = 4794407) B4794407
theorem B2130847 : Blo 2129435 2130847 := bstep (se 1 (by rfl) ⟨1598135, by rfl⟩ : syracuseStep 2130847 = 3196271) B3196271
theorem B3196277 : Blo 2129435 3196277 := bbase (se 5 (by rfl) ⟨149825, by rfl⟩ : syracuseStep 3196277 = 299651) (by norm_num)
theorem B2130851 : Blo 2129435 2130851 := bstep (se 1 (by rfl) ⟨1598138, by rfl⟩ : syracuseStep 2130851 = 3196277) B3196277
theorem B3033973 : Blo 2129435 3033973 := bbase (se 5 (by rfl) ⟨142217, by rfl⟩ : syracuseStep 3033973 = 284435) (by norm_num)
theorem B4045297 : Blo 2129435 4045297 := bstep (se 2 (by rfl) ⟨1516986, by rfl⟩ : syracuseStep 4045297 = 3033973) B3033973
theorem B5393729 : Blo 2129435 5393729 := bstep (se 2 (by rfl) ⟨2022648, by rfl⟩ : syracuseStep 5393729 = 4045297) B4045297
theorem B3595819 : Blo 2129435 3595819 := bstep (se 1 (by rfl) ⟨2696864, by rfl⟩ : syracuseStep 3595819 = 5393729) B5393729
theorem B4794425 : Blo 2129435 4794425 := bstep (se 2 (by rfl) ⟨1797909, by rfl⟩ : syracuseStep 4794425 = 3595819) B3595819
theorem B3196283 : Blo 2129435 3196283 := bstep (se 1 (by rfl) ⟨2397212, by rfl⟩ : syracuseStep 3196283 = 4794425) B4794425
theorem B2130855 : Blo 2129435 2130855 := bstep (se 1 (by rfl) ⟨1598141, by rfl⟩ : syracuseStep 2130855 = 3196283) B3196283
theorem B2397217 : Blo 2129435 2397217 := bbase (se 2 (by rfl) ⟨898956, by rfl⟩ : syracuseStep 2397217 = 1797913) (by norm_num)
theorem B3196289 : Blo 2129435 3196289 := bstep (se 2 (by rfl) ⟨1198608, by rfl⟩ : syracuseStep 3196289 = 2397217) B2397217
theorem B2130859 : Blo 2129435 2130859 := bstep (se 1 (by rfl) ⟨1598144, by rfl⟩ : syracuseStep 2130859 = 3196289) B3196289
theorem B5393749 : Blo 2129435 5393749 := bbase (se 11 (by rfl) ⟨3950, by rfl⟩ : syracuseStep 5393749 = 7901) (by norm_num)
theorem B7191665 : Blo 2129435 7191665 := bstep (se 2 (by rfl) ⟨2696874, by rfl⟩ : syracuseStep 7191665 = 5393749) B5393749
theorem B4794443 : Blo 2129435 4794443 := bstep (se 1 (by rfl) ⟨3595832, by rfl⟩ : syracuseStep 4794443 = 7191665) B7191665
theorem B3196295 : Blo 2129435 3196295 := bstep (se 1 (by rfl) ⟨2397221, by rfl⟩ : syracuseStep 3196295 = 4794443) B4794443
theorem B2130863 : Blo 2129435 2130863 := bstep (se 1 (by rfl) ⟨1598147, by rfl⟩ : syracuseStep 2130863 = 3196295) B3196295
theorem B3196301 : Blo 2129435 3196301 := bbase (se 3 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 3196301 = 1198613) (by norm_num)
theorem B2130867 : Blo 2129435 2130867 := bstep (se 1 (by rfl) ⟨1598150, by rfl⟩ : syracuseStep 2130867 = 3196301) B3196301
theorem B4794461 : Blo 2129435 4794461 := bbase (se 3 (by rfl) ⟨898961, by rfl⟩ : syracuseStep 4794461 = 1797923) (by norm_num)
theorem B3196307 : Blo 2129435 3196307 := bstep (se 1 (by rfl) ⟨2397230, by rfl⟩ : syracuseStep 3196307 = 4794461) B4794461
theorem B2130871 : Blo 2129435 2130871 := bstep (se 1 (by rfl) ⟨1598153, by rfl⟩ : syracuseStep 2130871 = 3196307) B3196307
theorem B3595853 : Blo 2129435 3595853 := bbase (se 3 (by rfl) ⟨674222, by rfl⟩ : syracuseStep 3595853 = 1348445) (by norm_num)
theorem B2397235 : Blo 2129435 2397235 := bstep (se 1 (by rfl) ⟨1797926, by rfl⟩ : syracuseStep 2397235 = 3595853) B3595853
theorem B3196313 : Blo 2129435 3196313 := bstep (se 2 (by rfl) ⟨1198617, by rfl⟩ : syracuseStep 3196313 = 2397235) B2397235
theorem B2130875 : Blo 2129435 2130875 := bstep (se 1 (by rfl) ⟨1598156, by rfl⟩ : syracuseStep 2130875 = 3196313) B3196313
theorem B4859893 : Blo 2129435 4859893 := bbase (se 5 (by rfl) ⟨227807, by rfl⟩ : syracuseStep 4859893 = 455615) (by norm_num)
theorem B6479857 : Blo 2129435 6479857 := bstep (se 2 (by rfl) ⟨2429946, by rfl⟩ : syracuseStep 6479857 = 4859893) B4859893
theorem B34559237 : Blo 2129435 34559237 := bstep (se 4 (by rfl) ⟨3239928, by rfl⟩ : syracuseStep 34559237 = 6479857) B6479857
theorem B23039491 : Blo 2129435 23039491 := bstep (se 1 (by rfl) ⟨17279618, by rfl⟩ : syracuseStep 23039491 = 34559237) B34559237
theorem B30719321 : Blo 2129435 30719321 := bstep (se 2 (by rfl) ⟨11519745, by rfl⟩ : syracuseStep 30719321 = 23039491) B23039491
theorem B20479547 : Blo 2129435 20479547 := bstep (se 1 (by rfl) ⟨15359660, by rfl⟩ : syracuseStep 20479547 = 30719321) B30719321
theorem B13653031 : Blo 2129435 13653031 := bstep (se 1 (by rfl) ⟨10239773, by rfl⟩ : syracuseStep 13653031 = 20479547) B20479547
theorem B18204041 : Blo 2129435 18204041 := bstep (se 2 (by rfl) ⟨6826515, by rfl⟩ : syracuseStep 18204041 = 13653031) B13653031
theorem B12136027 : Blo 2129435 12136027 := bstep (se 1 (by rfl) ⟨9102020, by rfl⟩ : syracuseStep 12136027 = 18204041) B18204041
theorem B16181369 : Blo 2129435 16181369 := bstep (se 2 (by rfl) ⟨6068013, by rfl⟩ : syracuseStep 16181369 = 12136027) B12136027
theorem B10787579 : Blo 2129435 10787579 := bstep (se 1 (by rfl) ⟨8090684, by rfl⟩ : syracuseStep 10787579 = 16181369) B16181369
theorem B7191719 : Blo 2129435 7191719 := bstep (se 1 (by rfl) ⟨5393789, by rfl⟩ : syracuseStep 7191719 = 10787579) B10787579
theorem B4794479 : Blo 2129435 4794479 := bstep (se 1 (by rfl) ⟨3595859, by rfl⟩ : syracuseStep 4794479 = 7191719) B7191719
theorem B3196319 : Blo 2129435 3196319 := bstep (se 1 (by rfl) ⟨2397239, by rfl⟩ : syracuseStep 3196319 = 4794479) B4794479
theorem B2130879 : Blo 2129435 2130879 := bstep (se 1 (by rfl) ⟨1598159, by rfl⟩ : syracuseStep 2130879 = 3196319) B3196319
theorem B3196325 : Blo 2129435 3196325 := bbase (se 4 (by rfl) ⟨299655, by rfl⟩ : syracuseStep 3196325 = 599311) (by norm_num)
theorem B2130883 : Blo 2129435 2130883 := bstep (se 1 (by rfl) ⟨1598162, by rfl⟩ : syracuseStep 2130883 = 3196325) B3196325
theorem B2696905 : Blo 2129435 2696905 := bbase (se 2 (by rfl) ⟨1011339, by rfl⟩ : syracuseStep 2696905 = 2022679) (by norm_num)
theorem B3595873 : Blo 2129435 3595873 := bstep (se 2 (by rfl) ⟨1348452, by rfl⟩ : syracuseStep 3595873 = 2696905) B2696905
theorem B4794497 : Blo 2129435 4794497 := bstep (se 2 (by rfl) ⟨1797936, by rfl⟩ : syracuseStep 4794497 = 3595873) B3595873
theorem B3196331 : Blo 2129435 3196331 := bstep (se 1 (by rfl) ⟨2397248, by rfl⟩ : syracuseStep 3196331 = 4794497) B4794497
theorem B2130887 : Blo 2129435 2130887 := bstep (se 1 (by rfl) ⟨1598165, by rfl⟩ : syracuseStep 2130887 = 3196331) B3196331
theorem B2397253 : Blo 2129435 2397253 := bbase (se 4 (by rfl) ⟨224742, by rfl⟩ : syracuseStep 2397253 = 449485) (by norm_num)
theorem B3196337 : Blo 2129435 3196337 := bstep (se 2 (by rfl) ⟨1198626, by rfl⟩ : syracuseStep 3196337 = 2397253) B2397253
theorem B2130891 : Blo 2129435 2130891 := bstep (se 1 (by rfl) ⟨1598168, by rfl⟩ : syracuseStep 2130891 = 3196337) B3196337
theorem B4045373 : Blo 2129435 4045373 := bbase (se 3 (by rfl) ⟨758507, by rfl⟩ : syracuseStep 4045373 = 1517015) (by norm_num)
theorem B2696915 : Blo 2129435 2696915 := bstep (se 1 (by rfl) ⟨2022686, by rfl⟩ : syracuseStep 2696915 = 4045373) B4045373
theorem B7191773 : Blo 2129435 7191773 := bstep (se 3 (by rfl) ⟨1348457, by rfl⟩ : syracuseStep 7191773 = 2696915) B2696915
theorem B4794515 : Blo 2129435 4794515 := bstep (se 1 (by rfl) ⟨3595886, by rfl⟩ : syracuseStep 4794515 = 7191773) B7191773
theorem B3196343 : Blo 2129435 3196343 := bstep (se 1 (by rfl) ⟨2397257, by rfl⟩ : syracuseStep 3196343 = 4794515) B4794515
theorem B2130895 : Blo 2129435 2130895 := bstep (se 1 (by rfl) ⟨1598171, by rfl⟩ : syracuseStep 2130895 = 3196343) B3196343
theorem B3196349 : Blo 2129435 3196349 := bbase (se 3 (by rfl) ⟨599315, by rfl⟩ : syracuseStep 3196349 = 1198631) (by norm_num)
theorem B2130899 : Blo 2129435 2130899 := bstep (se 1 (by rfl) ⟨1598174, by rfl⟩ : syracuseStep 2130899 = 3196349) B3196349
theorem B4794533 : Blo 2129435 4794533 := bbase (se 4 (by rfl) ⟨449487, by rfl⟩ : syracuseStep 4794533 = 898975) (by norm_num)
theorem B3196355 : Blo 2129435 3196355 := bstep (se 1 (by rfl) ⟨2397266, by rfl⟩ : syracuseStep 3196355 = 4794533) B4794533
theorem B2130903 : Blo 2129435 2130903 := bstep (se 1 (by rfl) ⟨1598177, by rfl⟩ : syracuseStep 2130903 = 3196355) B3196355
theorem B5393861 : Blo 2129435 5393861 := bbase (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) (by norm_num)
theorem B3595907 : Blo 2129435 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B2397271 : Blo 2129435 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B3196361 : Blo 2129435 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B2130907 : Blo 2129435 2130907 := bstep (se 1 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 2130907 = 3196361) B3196361
theorem B8639941 : Blo 2129435 8639941 := bbase (se 4 (by rfl) ⟨809994, by rfl⟩ : syracuseStep 8639941 = 1619989) (by norm_num)
theorem B11519921 : Blo 2129435 11519921 := bstep (se 2 (by rfl) ⟨4319970, by rfl⟩ : syracuseStep 11519921 = 8639941) B8639941
theorem B7679947 : Blo 2129435 7679947 := bstep (se 1 (by rfl) ⟨5759960, by rfl⟩ : syracuseStep 7679947 = 11519921) B11519921
theorem B10239929 : Blo 2129435 10239929 := bstep (se 2 (by rfl) ⟨3839973, by rfl⟩ : syracuseStep 10239929 = 7679947) B7679947
theorem B6826619 : Blo 2129435 6826619 := bstep (se 1 (by rfl) ⟨5119964, by rfl⟩ : syracuseStep 6826619 = 10239929) B10239929
theorem B4551079 : Blo 2129435 4551079 := bstep (se 1 (by rfl) ⟨3413309, by rfl⟩ : syracuseStep 4551079 = 6826619) B6826619
theorem B6068105 : Blo 2129435 6068105 := bstep (se 2 (by rfl) ⟨2275539, by rfl⟩ : syracuseStep 6068105 = 4551079) B4551079
theorem B4045403 : Blo 2129435 4045403 := bstep (se 1 (by rfl) ⟨3034052, by rfl⟩ : syracuseStep 4045403 = 6068105) B6068105
theorem B10787741 : Blo 2129435 10787741 := bstep (se 3 (by rfl) ⟨2022701, by rfl⟩ : syracuseStep 10787741 = 4045403) B4045403
theorem B7191827 : Blo 2129435 7191827 := bstep (se 1 (by rfl) ⟨5393870, by rfl⟩ : syracuseStep 7191827 = 10787741) B10787741
theorem B4794551 : Blo 2129435 4794551 := bstep (se 1 (by rfl) ⟨3595913, by rfl⟩ : syracuseStep 4794551 = 7191827) B7191827
theorem B3196367 : Blo 2129435 3196367 := bstep (se 1 (by rfl) ⟨2397275, by rfl⟩ : syracuseStep 3196367 = 4794551) B4794551
theorem B2130911 : Blo 2129435 2130911 := bstep (se 1 (by rfl) ⟨1598183, by rfl⟩ : syracuseStep 2130911 = 3196367) B3196367
theorem B3196373 : Blo 2129435 3196373 := bbase (se 7 (by rfl) ⟨37457, by rfl⟩ : syracuseStep 3196373 = 74915) (by norm_num)
theorem B2130915 : Blo 2129435 2130915 := bstep (se 1 (by rfl) ⟨1598186, by rfl⟩ : syracuseStep 2130915 = 3196373) B3196373
theorem B8090837 : Blo 2129435 8090837 := bbase (se 7 (by rfl) ⟨94814, by rfl⟩ : syracuseStep 8090837 = 189629) (by norm_num)
theorem B5393891 : Blo 2129435 5393891 := bstep (se 1 (by rfl) ⟨4045418, by rfl⟩ : syracuseStep 5393891 = 8090837) B8090837
theorem B3595927 : Blo 2129435 3595927 := bstep (se 1 (by rfl) ⟨2696945, by rfl⟩ : syracuseStep 3595927 = 5393891) B5393891
theorem B4794569 : Blo 2129435 4794569 := bstep (se 2 (by rfl) ⟨1797963, by rfl⟩ : syracuseStep 4794569 = 3595927) B3595927
theorem B3196379 : Blo 2129435 3196379 := bstep (se 1 (by rfl) ⟨2397284, by rfl⟩ : syracuseStep 3196379 = 4794569) B4794569
theorem B2130919 : Blo 2129435 2130919 := bstep (se 1 (by rfl) ⟨1598189, by rfl⟩ : syracuseStep 2130919 = 3196379) B3196379
theorem B2397289 : Blo 2129435 2397289 := bbase (se 2 (by rfl) ⟨898983, by rfl⟩ : syracuseStep 2397289 = 1797967) (by norm_num)
theorem B3196385 : Blo 2129435 3196385 := bstep (se 2 (by rfl) ⟨1198644, by rfl⟩ : syracuseStep 3196385 = 2397289) B2397289
theorem B2130923 : Blo 2129435 2130923 := bstep (se 1 (by rfl) ⟨1598192, by rfl⟩ : syracuseStep 2130923 = 3196385) B3196385
theorem B7680005 : Blo 2129435 7680005 := bbase (se 4 (by rfl) ⟨720000, by rfl⟩ : syracuseStep 7680005 = 1440001) (by norm_num)
theorem B5120003 : Blo 2129435 5120003 := bstep (se 1 (by rfl) ⟨3840002, by rfl⟩ : syracuseStep 5120003 = 7680005) B7680005
theorem B3413335 : Blo 2129435 3413335 := bstep (se 1 (by rfl) ⟨2560001, by rfl⟩ : syracuseStep 3413335 = 5120003) B5120003
theorem B4551113 : Blo 2129435 4551113 := bstep (se 2 (by rfl) ⟨1706667, by rfl⟩ : syracuseStep 4551113 = 3413335) B3413335
theorem B12136301 : Blo 2129435 12136301 := bstep (se 3 (by rfl) ⟨2275556, by rfl⟩ : syracuseStep 12136301 = 4551113) B4551113
theorem B8090867 : Blo 2129435 8090867 := bstep (se 1 (by rfl) ⟨6068150, by rfl⟩ : syracuseStep 8090867 = 12136301) B12136301
theorem B5393911 : Blo 2129435 5393911 := bstep (se 1 (by rfl) ⟨4045433, by rfl⟩ : syracuseStep 5393911 = 8090867) B8090867
theorem B7191881 : Blo 2129435 7191881 := bstep (se 2 (by rfl) ⟨2696955, by rfl⟩ : syracuseStep 7191881 = 5393911) B5393911
theorem B4794587 : Blo 2129435 4794587 := bstep (se 1 (by rfl) ⟨3595940, by rfl⟩ : syracuseStep 4794587 = 7191881) B7191881
theorem B3196391 : Blo 2129435 3196391 := bstep (se 1 (by rfl) ⟨2397293, by rfl⟩ : syracuseStep 3196391 = 4794587) B4794587
theorem B2130927 : Blo 2129435 2130927 := bstep (se 1 (by rfl) ⟨1598195, by rfl⟩ : syracuseStep 2130927 = 3196391) B3196391
theorem B3196397 : Blo 2129435 3196397 := bbase (se 3 (by rfl) ⟨599324, by rfl⟩ : syracuseStep 3196397 = 1198649) (by norm_num)
theorem B2130931 : Blo 2129435 2130931 := bstep (se 1 (by rfl) ⟨1598198, by rfl⟩ : syracuseStep 2130931 = 3196397) B3196397
theorem B4794605 : Blo 2129435 4794605 := bbase (se 3 (by rfl) ⟨898988, by rfl⟩ : syracuseStep 4794605 = 1797977) (by norm_num)
theorem B3196403 : Blo 2129435 3196403 := bstep (se 1 (by rfl) ⟨2397302, by rfl⟩ : syracuseStep 3196403 = 4794605) B4794605
theorem B2130935 : Blo 2129435 2130935 := bstep (se 1 (by rfl) ⟨1598201, by rfl⟩ : syracuseStep 2130935 = 3196403) B3196403
theorem B3034093 : Blo 2129435 3034093 := bbase (se 3 (by rfl) ⟨568892, by rfl⟩ : syracuseStep 3034093 = 1137785) (by norm_num)
theorem B4045457 : Blo 2129435 4045457 := bstep (se 2 (by rfl) ⟨1517046, by rfl⟩ : syracuseStep 4045457 = 3034093) B3034093
theorem B2696971 : Blo 2129435 2696971 := bstep (se 1 (by rfl) ⟨2022728, by rfl⟩ : syracuseStep 2696971 = 4045457) B4045457
theorem B3595961 : Blo 2129435 3595961 := bstep (se 2 (by rfl) ⟨1348485, by rfl⟩ : syracuseStep 3595961 = 2696971) B2696971
theorem B2397307 : Blo 2129435 2397307 := bstep (se 1 (by rfl) ⟨1797980, by rfl⟩ : syracuseStep 2397307 = 3595961) B3595961
theorem B3196409 : Blo 2129435 3196409 := bstep (se 2 (by rfl) ⟨1198653, by rfl⟩ : syracuseStep 3196409 = 2397307) B2397307
theorem B2130939 : Blo 2129435 2130939 := bstep (se 1 (by rfl) ⟨1598204, by rfl⟩ : syracuseStep 2130939 = 3196409) B3196409
theorem B5542141 : Blo 2129435 5542141 := bbase (se 3 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 5542141 = 2078303) (by norm_num)
theorem B7389521 : Blo 2129435 7389521 := bstep (se 2 (by rfl) ⟨2771070, by rfl⟩ : syracuseStep 7389521 = 5542141) B5542141
theorem B4926347 : Blo 2129435 4926347 := bstep (se 1 (by rfl) ⟨3694760, by rfl⟩ : syracuseStep 4926347 = 7389521) B7389521
theorem B3284231 : Blo 2129435 3284231 := bstep (se 1 (by rfl) ⟨2463173, by rfl⟩ : syracuseStep 3284231 = 4926347) B4926347
theorem B8757949 : Blo 2129435 8757949 := bstep (se 3 (by rfl) ⟨1642115, by rfl⟩ : syracuseStep 8757949 = 3284231) B3284231
theorem B11677265 : Blo 2129435 11677265 := bstep (se 2 (by rfl) ⟨4378974, by rfl⟩ : syracuseStep 11677265 = 8757949) B8757949
theorem B7784843 : Blo 2129435 7784843 := bstep (se 1 (by rfl) ⟨5838632, by rfl⟩ : syracuseStep 7784843 = 11677265) B11677265
theorem B20759581 : Blo 2129435 20759581 := bstep (se 3 (by rfl) ⟨3892421, by rfl⟩ : syracuseStep 20759581 = 7784843) B7784843
theorem B110717765 : Blo 2129435 110717765 := bstep (se 4 (by rfl) ⟨10379790, by rfl⟩ : syracuseStep 110717765 = 20759581) B20759581
theorem B73811843 : Blo 2129435 73811843 := bstep (se 1 (by rfl) ⟨55358882, by rfl⟩ : syracuseStep 73811843 = 110717765) B110717765
theorem B49207895 : Blo 2129435 49207895 := bstep (se 1 (by rfl) ⟨36905921, by rfl⟩ : syracuseStep 49207895 = 73811843) B73811843
theorem B32805263 : Blo 2129435 32805263 := bstep (se 1 (by rfl) ⟨24603947, by rfl⟩ : syracuseStep 32805263 = 49207895) B49207895
theorem B21870175 : Blo 2129435 21870175 := bstep (se 1 (by rfl) ⟨16402631, by rfl⟩ : syracuseStep 21870175 = 32805263) B32805263
theorem B29160233 : Blo 2129435 29160233 := bstep (se 2 (by rfl) ⟨10935087, by rfl⟩ : syracuseStep 29160233 = 21870175) B21870175
theorem B19440155 : Blo 2129435 19440155 := bstep (se 1 (by rfl) ⟨14580116, by rfl⟩ : syracuseStep 19440155 = 29160233) B29160233
theorem B12960103 : Blo 2129435 12960103 := bstep (se 1 (by rfl) ⟨9720077, by rfl⟩ : syracuseStep 12960103 = 19440155) B19440155
theorem B17280137 : Blo 2129435 17280137 := bstep (se 2 (by rfl) ⟨6480051, by rfl⟩ : syracuseStep 17280137 = 12960103) B12960103
theorem B11520091 : Blo 2129435 11520091 := bstep (se 1 (by rfl) ⟨8640068, by rfl⟩ : syracuseStep 11520091 = 17280137) B17280137
theorem B15360121 : Blo 2129435 15360121 := bstep (se 2 (by rfl) ⟨5760045, by rfl⟩ : syracuseStep 15360121 = 11520091) B11520091
theorem B81920645 : Blo 2129435 81920645 := bstep (se 4 (by rfl) ⟨7680060, by rfl⟩ : syracuseStep 81920645 = 15360121) B15360121
theorem B54613763 : Blo 2129435 54613763 := bstep (se 1 (by rfl) ⟨40960322, by rfl⟩ : syracuseStep 54613763 = 81920645) B81920645
theorem B36409175 : Blo 2129435 36409175 := bstep (se 1 (by rfl) ⟨27306881, by rfl⟩ : syracuseStep 36409175 = 54613763) B54613763
theorem B24272783 : Blo 2129435 24272783 := bstep (se 1 (by rfl) ⟨18204587, by rfl⟩ : syracuseStep 24272783 = 36409175) B36409175
theorem B16181855 : Blo 2129435 16181855 := bstep (se 1 (by rfl) ⟨12136391, by rfl⟩ : syracuseStep 16181855 = 24272783) B24272783
theorem B10787903 : Blo 2129435 10787903 := bstep (se 1 (by rfl) ⟨8090927, by rfl⟩ : syracuseStep 10787903 = 16181855) B16181855
theorem B7191935 : Blo 2129435 7191935 := bstep (se 1 (by rfl) ⟨5393951, by rfl⟩ : syracuseStep 7191935 = 10787903) B10787903
theorem B4794623 : Blo 2129435 4794623 := bstep (se 1 (by rfl) ⟨3595967, by rfl⟩ : syracuseStep 4794623 = 7191935) B7191935
theorem B3196415 : Blo 2129435 3196415 := bstep (se 1 (by rfl) ⟨2397311, by rfl⟩ : syracuseStep 3196415 = 4794623) B4794623
theorem B2130943 : Blo 2129435 2130943 := bstep (se 1 (by rfl) ⟨1598207, by rfl⟩ : syracuseStep 2130943 = 3196415) B3196415
theorem B3196421 : Blo 2129435 3196421 := bbase (se 4 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 3196421 = 599329) (by norm_num)
theorem B2130947 : Blo 2129435 2130947 := bstep (se 1 (by rfl) ⟨1598210, by rfl⟩ : syracuseStep 2130947 = 3196421) B3196421
theorem B3595981 : Blo 2129435 3595981 := bbase (se 3 (by rfl) ⟨674246, by rfl⟩ : syracuseStep 3595981 = 1348493) (by norm_num)
theorem B4794641 : Blo 2129435 4794641 := bstep (se 2 (by rfl) ⟨1797990, by rfl⟩ : syracuseStep 4794641 = 3595981) B3595981
theorem B3196427 : Blo 2129435 3196427 := bstep (se 1 (by rfl) ⟨2397320, by rfl⟩ : syracuseStep 3196427 = 4794641) B4794641
theorem B2130951 : Blo 2129435 2130951 := bstep (se 1 (by rfl) ⟨1598213, by rfl⟩ : syracuseStep 2130951 = 3196427) B3196427
theorem B2397325 : Blo 2129435 2397325 := bbase (se 3 (by rfl) ⟨449498, by rfl⟩ : syracuseStep 2397325 = 898997) (by norm_num)
theorem B3196433 : Blo 2129435 3196433 := bstep (se 2 (by rfl) ⟨1198662, by rfl⟩ : syracuseStep 3196433 = 2397325) B2397325
theorem B2130955 : Blo 2129435 2130955 := bstep (se 1 (by rfl) ⟨1598216, by rfl⟩ : syracuseStep 2130955 = 3196433) B3196433
theorem B7191989 : Blo 2129435 7191989 := bbase (se 5 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 7191989 = 674249) (by norm_num)
theorem B4794659 : Blo 2129435 4794659 := bstep (se 1 (by rfl) ⟨3595994, by rfl⟩ : syracuseStep 4794659 = 7191989) B7191989
theorem B3196439 : Blo 2129435 3196439 := bstep (se 1 (by rfl) ⟨2397329, by rfl⟩ : syracuseStep 3196439 = 4794659) B4794659
theorem B2130959 : Blo 2129435 2130959 := bstep (se 1 (by rfl) ⟨1598219, by rfl⟩ : syracuseStep 2130959 = 3196439) B3196439
theorem B3196445 : Blo 2129435 3196445 := bbase (se 3 (by rfl) ⟨599333, by rfl⟩ : syracuseStep 3196445 = 1198667) (by norm_num)
theorem B2130963 : Blo 2129435 2130963 := bstep (se 1 (by rfl) ⟨1598222, by rfl⟩ : syracuseStep 2130963 = 3196445) B3196445
theorem B4794677 : Blo 2129435 4794677 := bbase (se 5 (by rfl) ⟨224750, by rfl⟩ : syracuseStep 4794677 = 449501) (by norm_num)
theorem B3196451 : Blo 2129435 3196451 := bstep (se 1 (by rfl) ⟨2397338, by rfl⟩ : syracuseStep 3196451 = 4794677) B4794677
theorem B2130967 : Blo 2129435 2130967 := bstep (se 1 (by rfl) ⟨1598225, by rfl⟩ : syracuseStep 2130967 = 3196451) B3196451
theorem B11520245 : Blo 2129435 11520245 := bbase (se 5 (by rfl) ⟨540011, by rfl⟩ : syracuseStep 11520245 = 1080023) (by norm_num)
theorem B30720653 : Blo 2129435 30720653 := bstep (se 3 (by rfl) ⟨5760122, by rfl⟩ : syracuseStep 30720653 = 11520245) B11520245
theorem B20480435 : Blo 2129435 20480435 := bstep (se 1 (by rfl) ⟨15360326, by rfl⟩ : syracuseStep 20480435 = 30720653) B30720653
theorem B13653623 : Blo 2129435 13653623 := bstep (se 1 (by rfl) ⟨10240217, by rfl⟩ : syracuseStep 13653623 = 20480435) B20480435
theorem B9102415 : Blo 2129435 9102415 := bstep (se 1 (by rfl) ⟨6826811, by rfl⟩ : syracuseStep 9102415 = 13653623) B13653623
theorem B12136553 : Blo 2129435 12136553 := bstep (se 2 (by rfl) ⟨4551207, by rfl⟩ : syracuseStep 12136553 = 9102415) B9102415
theorem B8091035 : Blo 2129435 8091035 := bstep (se 1 (by rfl) ⟨6068276, by rfl⟩ : syracuseStep 8091035 = 12136553) B12136553
theorem B5394023 : Blo 2129435 5394023 := bstep (se 1 (by rfl) ⟨4045517, by rfl⟩ : syracuseStep 5394023 = 8091035) B8091035
theorem B3596015 : Blo 2129435 3596015 := bstep (se 1 (by rfl) ⟨2697011, by rfl⟩ : syracuseStep 3596015 = 5394023) B5394023
theorem B2397343 : Blo 2129435 2397343 := bstep (se 1 (by rfl) ⟨1798007, by rfl⟩ : syracuseStep 2397343 = 3596015) B3596015
theorem B3196457 : Blo 2129435 3196457 := bstep (se 2 (by rfl) ⟨1198671, by rfl⟩ : syracuseStep 3196457 = 2397343) B2397343
theorem B2130971 : Blo 2129435 2130971 := bstep (se 1 (by rfl) ⟨1598228, by rfl⟩ : syracuseStep 2130971 = 3196457) B3196457
theorem B10935253 : Blo 2129435 10935253 := bbase (se 7 (by rfl) ⟨128147, by rfl⟩ : syracuseStep 10935253 = 256295) (by norm_num)
theorem B14580337 : Blo 2129435 14580337 := bstep (se 2 (by rfl) ⟨5467626, by rfl⟩ : syracuseStep 14580337 = 10935253) B10935253
theorem B19440449 : Blo 2129435 19440449 := bstep (se 2 (by rfl) ⟨7290168, by rfl⟩ : syracuseStep 19440449 = 14580337) B14580337
theorem B12960299 : Blo 2129435 12960299 := bstep (se 1 (by rfl) ⟨9720224, by rfl⟩ : syracuseStep 12960299 = 19440449) B19440449
theorem B8640199 : Blo 2129435 8640199 := bstep (se 1 (by rfl) ⟨6480149, by rfl⟩ : syracuseStep 8640199 = 12960299) B12960299
theorem B46081061 : Blo 2129435 46081061 := bstep (se 4 (by rfl) ⟨4320099, by rfl⟩ : syracuseStep 46081061 = 8640199) B8640199
theorem B30720707 : Blo 2129435 30720707 := bstep (se 1 (by rfl) ⟨23040530, by rfl⟩ : syracuseStep 30720707 = 46081061) B46081061
theorem B20480471 : Blo 2129435 20480471 := bstep (se 1 (by rfl) ⟨15360353, by rfl⟩ : syracuseStep 20480471 = 30720707) B30720707
theorem B13653647 : Blo 2129435 13653647 := bstep (se 1 (by rfl) ⟨10240235, by rfl⟩ : syracuseStep 13653647 = 20480471) B20480471
theorem B9102431 : Blo 2129435 9102431 := bstep (se 1 (by rfl) ⟨6826823, by rfl⟩ : syracuseStep 9102431 = 13653647) B13653647
theorem B6068287 : Blo 2129435 6068287 := bstep (se 1 (by rfl) ⟨4551215, by rfl⟩ : syracuseStep 6068287 = 9102431) B9102431
theorem B8091049 : Blo 2129435 8091049 := bstep (se 2 (by rfl) ⟨3034143, by rfl⟩ : syracuseStep 8091049 = 6068287) B6068287
theorem B10788065 : Blo 2129435 10788065 := bstep (se 2 (by rfl) ⟨4045524, by rfl⟩ : syracuseStep 10788065 = 8091049) B8091049
theorem B7192043 : Blo 2129435 7192043 := bstep (se 1 (by rfl) ⟨5394032, by rfl⟩ : syracuseStep 7192043 = 10788065) B10788065
theorem B4794695 : Blo 2129435 4794695 := bstep (se 1 (by rfl) ⟨3596021, by rfl⟩ : syracuseStep 4794695 = 7192043) B7192043
theorem B3196463 : Blo 2129435 3196463 := bstep (se 1 (by rfl) ⟨2397347, by rfl⟩ : syracuseStep 3196463 = 4794695) B4794695
theorem B2130975 : Blo 2129435 2130975 := bstep (se 1 (by rfl) ⟨1598231, by rfl⟩ : syracuseStep 2130975 = 3196463) B3196463
theorem B3196469 : Blo 2129435 3196469 := bbase (se 5 (by rfl) ⟨149834, by rfl⟩ : syracuseStep 3196469 = 299669) (by norm_num)
theorem B2130979 : Blo 2129435 2130979 := bstep (se 1 (by rfl) ⟨1598234, by rfl⟩ : syracuseStep 2130979 = 3196469) B3196469
theorem B5394053 : Blo 2129435 5394053 := bbase (se 4 (by rfl) ⟨505692, by rfl⟩ : syracuseStep 5394053 = 1011385) (by norm_num)
theorem B3596035 : Blo 2129435 3596035 := bstep (se 1 (by rfl) ⟨2697026, by rfl⟩ : syracuseStep 3596035 = 5394053) B5394053
theorem B4794713 : Blo 2129435 4794713 := bstep (se 2 (by rfl) ⟨1798017, by rfl⟩ : syracuseStep 4794713 = 3596035) B3596035
theorem B3196475 : Blo 2129435 3196475 := bstep (se 1 (by rfl) ⟨2397356, by rfl⟩ : syracuseStep 3196475 = 4794713) B4794713
theorem B2130983 : Blo 2129435 2130983 := bstep (se 1 (by rfl) ⟨1598237, by rfl⟩ : syracuseStep 2130983 = 3196475) B3196475
theorem B2397361 : Blo 2129435 2397361 := bbase (se 2 (by rfl) ⟨899010, by rfl⟩ : syracuseStep 2397361 = 1798021) (by norm_num)
theorem B3196481 : Blo 2129435 3196481 := bstep (se 2 (by rfl) ⟨1198680, by rfl⟩ : syracuseStep 3196481 = 2397361) B2397361
theorem B2130987 : Blo 2129435 2130987 := bstep (se 1 (by rfl) ⟨1598240, by rfl⟩ : syracuseStep 2130987 = 3196481) B3196481
theorem B2275625 : Blo 2129435 2275625 := bbase (se 2 (by rfl) ⟨853359, by rfl⟩ : syracuseStep 2275625 = 1706719) (by norm_num)
theorem B6068333 : Blo 2129435 6068333 := bstep (se 3 (by rfl) ⟨1137812, by rfl⟩ : syracuseStep 6068333 = 2275625) B2275625
theorem B4045555 : Blo 2129435 4045555 := bstep (se 1 (by rfl) ⟨3034166, by rfl⟩ : syracuseStep 4045555 = 6068333) B6068333
theorem B5394073 : Blo 2129435 5394073 := bstep (se 2 (by rfl) ⟨2022777, by rfl⟩ : syracuseStep 5394073 = 4045555) B4045555
theorem B7192097 : Blo 2129435 7192097 := bstep (se 2 (by rfl) ⟨2697036, by rfl⟩ : syracuseStep 7192097 = 5394073) B5394073
theorem B4794731 : Blo 2129435 4794731 := bstep (se 1 (by rfl) ⟨3596048, by rfl⟩ : syracuseStep 4794731 = 7192097) B7192097
theorem B3196487 : Blo 2129435 3196487 := bstep (se 1 (by rfl) ⟨2397365, by rfl⟩ : syracuseStep 3196487 = 4794731) B4794731
theorem B2130991 : Blo 2129435 2130991 := bstep (se 1 (by rfl) ⟨1598243, by rfl⟩ : syracuseStep 2130991 = 3196487) B3196487
theorem B3196493 : Blo 2129435 3196493 := bbase (se 3 (by rfl) ⟨599342, by rfl⟩ : syracuseStep 3196493 = 1198685) (by norm_num)
theorem B2130995 : Blo 2129435 2130995 := bstep (se 1 (by rfl) ⟨1598246, by rfl⟩ : syracuseStep 2130995 = 3196493) B3196493
theorem B4794749 : Blo 2129435 4794749 := bbase (se 3 (by rfl) ⟨899015, by rfl⟩ : syracuseStep 4794749 = 1798031) (by norm_num)
theorem B3196499 : Blo 2129435 3196499 := bstep (se 1 (by rfl) ⟨2397374, by rfl⟩ : syracuseStep 3196499 = 4794749) B4794749
theorem B2130999 : Blo 2129435 2130999 := bstep (se 1 (by rfl) ⟨1598249, by rfl⟩ : syracuseStep 2130999 = 3196499) B3196499
theorem B3596069 : Blo 2129435 3596069 := bbase (se 4 (by rfl) ⟨337131, by rfl⟩ : syracuseStep 3596069 = 674263) (by norm_num)
theorem B2397379 : Blo 2129435 2397379 := bstep (se 1 (by rfl) ⟨1798034, by rfl⟩ : syracuseStep 2397379 = 3596069) B3596069
theorem B3196505 : Blo 2129435 3196505 := bstep (se 2 (by rfl) ⟨1198689, by rfl⟩ : syracuseStep 3196505 = 2397379) B2397379
theorem B2131003 : Blo 2129435 2131003 := bstep (se 1 (by rfl) ⟨1598252, by rfl⟩ : syracuseStep 2131003 = 3196505) B3196505
theorem B3034189 : Blo 2129435 3034189 := bbase (se 3 (by rfl) ⟨568910, by rfl⟩ : syracuseStep 3034189 = 1137821) (by norm_num)
theorem B16182341 : Blo 2129435 16182341 := bstep (se 4 (by rfl) ⟨1517094, by rfl⟩ : syracuseStep 16182341 = 3034189) B3034189
theorem B10788227 : Blo 2129435 10788227 := bstep (se 1 (by rfl) ⟨8091170, by rfl⟩ : syracuseStep 10788227 = 16182341) B16182341
theorem B7192151 : Blo 2129435 7192151 := bstep (se 1 (by rfl) ⟨5394113, by rfl⟩ : syracuseStep 7192151 = 10788227) B10788227
theorem B4794767 : Blo 2129435 4794767 := bstep (se 1 (by rfl) ⟨3596075, by rfl⟩ : syracuseStep 4794767 = 7192151) B7192151
theorem B3196511 : Blo 2129435 3196511 := bstep (se 1 (by rfl) ⟨2397383, by rfl⟩ : syracuseStep 3196511 = 4794767) B4794767
theorem B2131007 : Blo 2129435 2131007 := bstep (se 1 (by rfl) ⟨1598255, by rfl⟩ : syracuseStep 2131007 = 3196511) B3196511
theorem B3196517 : Blo 2129435 3196517 := bbase (se 4 (by rfl) ⟨299673, by rfl⟩ : syracuseStep 3196517 = 599347) (by norm_num)
theorem B2131011 : Blo 2129435 2131011 := bstep (se 1 (by rfl) ⟨1598258, by rfl⟩ : syracuseStep 2131011 = 3196517) B3196517
theorem B3413477 : Blo 2129435 3413477 := bbase (se 4 (by rfl) ⟨320013, by rfl⟩ : syracuseStep 3413477 = 640027) (by norm_num)
theorem B2275651 : Blo 2129435 2275651 := bstep (se 1 (by rfl) ⟨1706738, by rfl⟩ : syracuseStep 2275651 = 3413477) B3413477
theorem B3034201 : Blo 2129435 3034201 := bstep (se 2 (by rfl) ⟨1137825, by rfl⟩ : syracuseStep 3034201 = 2275651) B2275651
theorem B4045601 : Blo 2129435 4045601 := bstep (se 2 (by rfl) ⟨1517100, by rfl⟩ : syracuseStep 4045601 = 3034201) B3034201
theorem B2697067 : Blo 2129435 2697067 := bstep (se 1 (by rfl) ⟨2022800, by rfl⟩ : syracuseStep 2697067 = 4045601) B4045601
theorem B3596089 : Blo 2129435 3596089 := bstep (se 2 (by rfl) ⟨1348533, by rfl⟩ : syracuseStep 3596089 = 2697067) B2697067
theorem B4794785 : Blo 2129435 4794785 := bstep (se 2 (by rfl) ⟨1798044, by rfl⟩ : syracuseStep 4794785 = 3596089) B3596089
theorem B3196523 : Blo 2129435 3196523 := bstep (se 1 (by rfl) ⟨2397392, by rfl⟩ : syracuseStep 3196523 = 4794785) B4794785
theorem B2131015 : Blo 2129435 2131015 := bstep (se 1 (by rfl) ⟨1598261, by rfl⟩ : syracuseStep 2131015 = 3196523) B3196523
theorem B2397397 : Blo 2129435 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B3196529 : Blo 2129435 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B2131019 : Blo 2129435 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B2697077 : Blo 2129435 2697077 := bbase (se 5 (by rfl) ⟨126425, by rfl⟩ : syracuseStep 2697077 = 252851) (by norm_num)
theorem B7192205 : Blo 2129435 7192205 := bstep (se 3 (by rfl) ⟨1348538, by rfl⟩ : syracuseStep 7192205 = 2697077) B2697077
theorem B4794803 : Blo 2129435 4794803 := bstep (se 1 (by rfl) ⟨3596102, by rfl⟩ : syracuseStep 4794803 = 7192205) B7192205
theorem B3196535 : Blo 2129435 3196535 := bstep (se 1 (by rfl) ⟨2397401, by rfl⟩ : syracuseStep 3196535 = 4794803) B4794803
theorem B2131023 : Blo 2129435 2131023 := bstep (se 1 (by rfl) ⟨1598267, by rfl⟩ : syracuseStep 2131023 = 3196535) B3196535
theorem B3196541 : Blo 2129435 3196541 := bbase (se 3 (by rfl) ⟨599351, by rfl⟩ : syracuseStep 3196541 = 1198703) (by norm_num)
theorem B2131027 : Blo 2129435 2131027 := bstep (se 1 (by rfl) ⟨1598270, by rfl⟩ : syracuseStep 2131027 = 3196541) B3196541
theorem B4794821 : Blo 2129435 4794821 := bbase (se 4 (by rfl) ⟨449514, by rfl⟩ : syracuseStep 4794821 = 899029) (by norm_num)
theorem B3196547 : Blo 2129435 3196547 := bstep (se 1 (by rfl) ⟨2397410, by rfl⟩ : syracuseStep 3196547 = 4794821) B4794821
theorem B2131031 : Blo 2129435 2131031 := bstep (se 1 (by rfl) ⟨1598273, by rfl⟩ : syracuseStep 2131031 = 3196547) B3196547
theorem B9226885 : Blo 2129435 9226885 := bbase (se 4 (by rfl) ⟨865020, by rfl⟩ : syracuseStep 9226885 = 1730041) (by norm_num)
theorem B12302513 : Blo 2129435 12302513 := bstep (se 2 (by rfl) ⟨4613442, by rfl⟩ : syracuseStep 12302513 = 9226885) B9226885
theorem B8201675 : Blo 2129435 8201675 := bstep (se 1 (by rfl) ⟨6151256, by rfl⟩ : syracuseStep 8201675 = 12302513) B12302513
theorem B5467783 : Blo 2129435 5467783 := bstep (se 1 (by rfl) ⟨4100837, by rfl⟩ : syracuseStep 5467783 = 8201675) B8201675
theorem B7290377 : Blo 2129435 7290377 := bstep (se 2 (by rfl) ⟨2733891, by rfl⟩ : syracuseStep 7290377 = 5467783) B5467783
theorem B4860251 : Blo 2129435 4860251 := bstep (se 1 (by rfl) ⟨3645188, by rfl⟩ : syracuseStep 4860251 = 7290377) B7290377
theorem B3240167 : Blo 2129435 3240167 := bstep (se 1 (by rfl) ⟨2430125, by rfl⟩ : syracuseStep 3240167 = 4860251) B4860251
theorem B8640445 : Blo 2129435 8640445 := bstep (se 3 (by rfl) ⟨1620083, by rfl⟩ : syracuseStep 8640445 = 3240167) B3240167
theorem B11520593 : Blo 2129435 11520593 := bstep (se 2 (by rfl) ⟨4320222, by rfl⟩ : syracuseStep 11520593 = 8640445) B8640445
theorem B7680395 : Blo 2129435 7680395 := bstep (se 1 (by rfl) ⟨5760296, by rfl⟩ : syracuseStep 7680395 = 11520593) B11520593
theorem B5120263 : Blo 2129435 5120263 := bstep (se 1 (by rfl) ⟨3840197, by rfl⟩ : syracuseStep 5120263 = 7680395) B7680395
theorem B6827017 : Blo 2129435 6827017 := bstep (se 2 (by rfl) ⟨2560131, by rfl⟩ : syracuseStep 6827017 = 5120263) B5120263
theorem B9102689 : Blo 2129435 9102689 := bstep (se 2 (by rfl) ⟨3413508, by rfl⟩ : syracuseStep 9102689 = 6827017) B6827017
theorem B6068459 : Blo 2129435 6068459 := bstep (se 1 (by rfl) ⟨4551344, by rfl⟩ : syracuseStep 6068459 = 9102689) B9102689
theorem B4045639 : Blo 2129435 4045639 := bstep (se 1 (by rfl) ⟨3034229, by rfl⟩ : syracuseStep 4045639 = 6068459) B6068459
theorem B5394185 : Blo 2129435 5394185 := bstep (se 2 (by rfl) ⟨2022819, by rfl⟩ : syracuseStep 5394185 = 4045639) B4045639
theorem B3596123 : Blo 2129435 3596123 := bstep (se 1 (by rfl) ⟨2697092, by rfl⟩ : syracuseStep 3596123 = 5394185) B5394185
theorem B2397415 : Blo 2129435 2397415 := bstep (se 1 (by rfl) ⟨1798061, by rfl⟩ : syracuseStep 2397415 = 3596123) B3596123
theorem B3196553 : Blo 2129435 3196553 := bstep (se 2 (by rfl) ⟨1198707, by rfl⟩ : syracuseStep 3196553 = 2397415) B2397415
theorem B2131035 : Blo 2129435 2131035 := bstep (se 1 (by rfl) ⟨1598276, by rfl⟩ : syracuseStep 2131035 = 3196553) B3196553
theorem B10788389 : Blo 2129435 10788389 := bbase (se 4 (by rfl) ⟨1011411, by rfl⟩ : syracuseStep 10788389 = 2022823) (by norm_num)
theorem B7192259 : Blo 2129435 7192259 := bstep (se 1 (by rfl) ⟨5394194, by rfl⟩ : syracuseStep 7192259 = 10788389) B10788389
theorem B4794839 : Blo 2129435 4794839 := bstep (se 1 (by rfl) ⟨3596129, by rfl⟩ : syracuseStep 4794839 = 7192259) B7192259
theorem B3196559 : Blo 2129435 3196559 := bstep (se 1 (by rfl) ⟨2397419, by rfl⟩ : syracuseStep 3196559 = 4794839) B4794839
theorem B2131039 : Blo 2129435 2131039 := bstep (se 1 (by rfl) ⟨1598279, by rfl⟩ : syracuseStep 2131039 = 3196559) B3196559
theorem B3196565 : Blo 2129435 3196565 := bbase (se 6 (by rfl) ⟨74919, by rfl⟩ : syracuseStep 3196565 = 149839) (by norm_num)
theorem B2131043 : Blo 2129435 2131043 := bstep (se 1 (by rfl) ⟨1598282, by rfl⟩ : syracuseStep 2131043 = 3196565) B3196565
theorem B7680437 : Blo 2129435 7680437 := bbase (se 5 (by rfl) ⟨360020, by rfl⟩ : syracuseStep 7680437 = 720041) (by norm_num)
theorem B5120291 : Blo 2129435 5120291 := bstep (se 1 (by rfl) ⟨3840218, by rfl⟩ : syracuseStep 5120291 = 7680437) B7680437
theorem B13654109 : Blo 2129435 13654109 := bstep (se 3 (by rfl) ⟨2560145, by rfl⟩ : syracuseStep 13654109 = 5120291) B5120291
theorem B9102739 : Blo 2129435 9102739 := bstep (se 1 (by rfl) ⟨6827054, by rfl⟩ : syracuseStep 9102739 = 13654109) B13654109
theorem B12136985 : Blo 2129435 12136985 := bstep (se 2 (by rfl) ⟨4551369, by rfl⟩ : syracuseStep 12136985 = 9102739) B9102739
theorem B8091323 : Blo 2129435 8091323 := bstep (se 1 (by rfl) ⟨6068492, by rfl⟩ : syracuseStep 8091323 = 12136985) B12136985
theorem B5394215 : Blo 2129435 5394215 := bstep (se 1 (by rfl) ⟨4045661, by rfl⟩ : syracuseStep 5394215 = 8091323) B8091323
theorem B3596143 : Blo 2129435 3596143 := bstep (se 1 (by rfl) ⟨2697107, by rfl⟩ : syracuseStep 3596143 = 5394215) B5394215
theorem B4794857 : Blo 2129435 4794857 := bstep (se 2 (by rfl) ⟨1798071, by rfl⟩ : syracuseStep 4794857 = 3596143) B3596143
theorem B3196571 : Blo 2129435 3196571 := bstep (se 1 (by rfl) ⟨2397428, by rfl⟩ : syracuseStep 3196571 = 4794857) B4794857
theorem B2131047 : Blo 2129435 2131047 := bstep (se 1 (by rfl) ⟨1598285, by rfl⟩ : syracuseStep 2131047 = 3196571) B3196571
theorem B2397433 : Blo 2129435 2397433 := bbase (se 2 (by rfl) ⟨899037, by rfl⟩ : syracuseStep 2397433 = 1798075) (by norm_num)
theorem B3196577 : Blo 2129435 3196577 := bstep (se 2 (by rfl) ⟨1198716, by rfl⟩ : syracuseStep 3196577 = 2397433) B2397433
theorem B2131051 : Blo 2129435 2131051 := bstep (se 1 (by rfl) ⟨1598288, by rfl⟩ : syracuseStep 2131051 = 3196577) B3196577
theorem B9102773 : Blo 2129435 9102773 := bbase (se 5 (by rfl) ⟨426692, by rfl⟩ : syracuseStep 9102773 = 853385) (by norm_num)
theorem B6068515 : Blo 2129435 6068515 := bstep (se 1 (by rfl) ⟨4551386, by rfl⟩ : syracuseStep 6068515 = 9102773) B9102773
theorem B8091353 : Blo 2129435 8091353 := bstep (se 2 (by rfl) ⟨3034257, by rfl⟩ : syracuseStep 8091353 = 6068515) B6068515
theorem B5394235 : Blo 2129435 5394235 := bstep (se 1 (by rfl) ⟨4045676, by rfl⟩ : syracuseStep 5394235 = 8091353) B8091353
theorem B7192313 : Blo 2129435 7192313 := bstep (se 2 (by rfl) ⟨2697117, by rfl⟩ : syracuseStep 7192313 = 5394235) B5394235
theorem B4794875 : Blo 2129435 4794875 := bstep (se 1 (by rfl) ⟨3596156, by rfl⟩ : syracuseStep 4794875 = 7192313) B7192313
theorem B3196583 : Blo 2129435 3196583 := bstep (se 1 (by rfl) ⟨2397437, by rfl⟩ : syracuseStep 3196583 = 4794875) B4794875
theorem B2131055 : Blo 2129435 2131055 := bstep (se 1 (by rfl) ⟨1598291, by rfl⟩ : syracuseStep 2131055 = 3196583) B3196583
theorem B3196589 : Blo 2129435 3196589 := bbase (se 3 (by rfl) ⟨599360, by rfl⟩ : syracuseStep 3196589 = 1198721) (by norm_num)
theorem B2131059 : Blo 2129435 2131059 := bstep (se 1 (by rfl) ⟨1598294, by rfl⟩ : syracuseStep 2131059 = 3196589) B3196589
theorem B4794893 : Blo 2129435 4794893 := bbase (se 3 (by rfl) ⟨899042, by rfl⟩ : syracuseStep 4794893 = 1798085) (by norm_num)
theorem B3196595 : Blo 2129435 3196595 := bstep (se 1 (by rfl) ⟨2397446, by rfl⟩ : syracuseStep 3196595 = 4794893) B4794893
theorem B2131063 : Blo 2129435 2131063 := bstep (se 1 (by rfl) ⟨1598297, by rfl⟩ : syracuseStep 2131063 = 3196595) B3196595
theorem B2697133 : Blo 2129435 2697133 := bbase (se 3 (by rfl) ⟨505712, by rfl⟩ : syracuseStep 2697133 = 1011425) (by norm_num)
theorem B3596177 : Blo 2129435 3596177 := bstep (se 2 (by rfl) ⟨1348566, by rfl⟩ : syracuseStep 3596177 = 2697133) B2697133
theorem B2397451 : Blo 2129435 2397451 := bstep (se 1 (by rfl) ⟨1798088, by rfl⟩ : syracuseStep 2397451 = 3596177) B3596177
theorem B3196601 : Blo 2129435 3196601 := bstep (se 2 (by rfl) ⟨1198725, by rfl⟩ : syracuseStep 3196601 = 2397451) B2397451
theorem B2131067 : Blo 2129435 2131067 := bstep (se 1 (by rfl) ⟨1598300, by rfl⟩ : syracuseStep 2131067 = 3196601) B3196601
theorem B13654261 : Blo 2129435 13654261 := bbase (se 5 (by rfl) ⟨640043, by rfl⟩ : syracuseStep 13654261 = 1280087) (by norm_num)
theorem B18205681 : Blo 2129435 18205681 := bstep (se 2 (by rfl) ⟨6827130, by rfl⟩ : syracuseStep 18205681 = 13654261) B13654261
theorem B24274241 : Blo 2129435 24274241 := bstep (se 2 (by rfl) ⟨9102840, by rfl⟩ : syracuseStep 24274241 = 18205681) B18205681
theorem B16182827 : Blo 2129435 16182827 := bstep (se 1 (by rfl) ⟨12137120, by rfl⟩ : syracuseStep 16182827 = 24274241) B24274241
theorem B10788551 : Blo 2129435 10788551 := bstep (se 1 (by rfl) ⟨8091413, by rfl⟩ : syracuseStep 10788551 = 16182827) B16182827
theorem B7192367 : Blo 2129435 7192367 := bstep (se 1 (by rfl) ⟨5394275, by rfl⟩ : syracuseStep 7192367 = 10788551) B10788551
theorem B4794911 : Blo 2129435 4794911 := bstep (se 1 (by rfl) ⟨3596183, by rfl⟩ : syracuseStep 4794911 = 7192367) B7192367
theorem B3196607 : Blo 2129435 3196607 := bstep (se 1 (by rfl) ⟨2397455, by rfl⟩ : syracuseStep 3196607 = 4794911) B4794911
theorem B2131071 : Blo 2129435 2131071 := bstep (se 1 (by rfl) ⟨1598303, by rfl⟩ : syracuseStep 2131071 = 3196607) B3196607
theorem B3196613 : Blo 2129435 3196613 := bbase (se 4 (by rfl) ⟨299682, by rfl⟩ : syracuseStep 3196613 = 599365) (by norm_num)
theorem B2131075 : Blo 2129435 2131075 := bstep (se 1 (by rfl) ⟨1598306, by rfl⟩ : syracuseStep 2131075 = 3196613) B3196613
theorem B3596197 : Blo 2129435 3596197 := bbase (se 4 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 3596197 = 674287) (by norm_num)
theorem B4794929 : Blo 2129435 4794929 := bstep (se 2 (by rfl) ⟨1798098, by rfl⟩ : syracuseStep 4794929 = 3596197) B3596197
theorem B3196619 : Blo 2129435 3196619 := bstep (se 1 (by rfl) ⟨2397464, by rfl⟩ : syracuseStep 3196619 = 4794929) B4794929
theorem B2131079 : Blo 2129435 2131079 := bstep (se 1 (by rfl) ⟨1598309, by rfl⟩ : syracuseStep 2131079 = 3196619) B3196619
theorem B2397469 : Blo 2129435 2397469 := bbase (se 3 (by rfl) ⟨449525, by rfl⟩ : syracuseStep 2397469 = 899051) (by norm_num)
theorem B3196625 : Blo 2129435 3196625 := bstep (se 2 (by rfl) ⟨1198734, by rfl⟩ : syracuseStep 3196625 = 2397469) B2397469
theorem B2131083 : Blo 2129435 2131083 := bstep (se 1 (by rfl) ⟨1598312, by rfl⟩ : syracuseStep 2131083 = 3196625) B3196625
theorem B7192421 : Blo 2129435 7192421 := bbase (se 4 (by rfl) ⟨674289, by rfl⟩ : syracuseStep 7192421 = 1348579) (by norm_num)
theorem B4794947 : Blo 2129435 4794947 := bstep (se 1 (by rfl) ⟨3596210, by rfl⟩ : syracuseStep 4794947 = 7192421) B7192421
theorem B3196631 : Blo 2129435 3196631 := bstep (se 1 (by rfl) ⟨2397473, by rfl⟩ : syracuseStep 3196631 = 4794947) B4794947
theorem B2131087 : Blo 2129435 2131087 := bstep (se 1 (by rfl) ⟨1598315, by rfl⟩ : syracuseStep 2131087 = 3196631) B3196631
theorem B3196637 : Blo 2129435 3196637 := bbase (se 3 (by rfl) ⟨599369, by rfl⟩ : syracuseStep 3196637 = 1198739) (by norm_num)
theorem B2131091 : Blo 2129435 2131091 := bstep (se 1 (by rfl) ⟨1598318, by rfl⟩ : syracuseStep 2131091 = 3196637) B3196637
theorem B4794965 : Blo 2129435 4794965 := bbase (se 8 (by rfl) ⟨28095, by rfl⟩ : syracuseStep 4794965 = 56191) (by norm_num)
theorem B3196643 : Blo 2129435 3196643 := bstep (se 1 (by rfl) ⟨2397482, by rfl⟩ : syracuseStep 3196643 = 4794965) B4794965
theorem B2131095 : Blo 2129435 2131095 := bstep (se 1 (by rfl) ⟨1598321, by rfl⟩ : syracuseStep 2131095 = 3196643) B3196643
theorem B5467949 : Blo 2129435 5467949 := bbase (se 3 (by rfl) ⟨1025240, by rfl⟩ : syracuseStep 5467949 = 2050481) (by norm_num)
theorem B3645299 : Blo 2129435 3645299 := bstep (se 1 (by rfl) ⟨2733974, by rfl⟩ : syracuseStep 3645299 = 5467949) B5467949
theorem B2430199 : Blo 2129435 2430199 := bstep (se 1 (by rfl) ⟨1822649, by rfl⟩ : syracuseStep 2430199 = 3645299) B3645299
theorem B3240265 : Blo 2129435 3240265 := bstep (se 2 (by rfl) ⟨1215099, by rfl⟩ : syracuseStep 3240265 = 2430199) B2430199
theorem B4320353 : Blo 2129435 4320353 := bstep (se 2 (by rfl) ⟨1620132, by rfl⟩ : syracuseStep 4320353 = 3240265) B3240265
theorem B2880235 : Blo 2129435 2880235 := bstep (se 1 (by rfl) ⟨2160176, by rfl⟩ : syracuseStep 2880235 = 4320353) B4320353
theorem B3840313 : Blo 2129435 3840313 := bstep (se 2 (by rfl) ⟨1440117, by rfl⟩ : syracuseStep 3840313 = 2880235) B2880235
theorem B5120417 : Blo 2129435 5120417 := bstep (se 2 (by rfl) ⟨1920156, by rfl⟩ : syracuseStep 5120417 = 3840313) B3840313
theorem B3413611 : Blo 2129435 3413611 := bstep (se 1 (by rfl) ⟨2560208, by rfl⟩ : syracuseStep 3413611 = 5120417) B5120417
theorem B4551481 : Blo 2129435 4551481 := bstep (se 2 (by rfl) ⟨1706805, by rfl⟩ : syracuseStep 4551481 = 3413611) B3413611
theorem B6068641 : Blo 2129435 6068641 := bstep (se 2 (by rfl) ⟨2275740, by rfl⟩ : syracuseStep 6068641 = 4551481) B4551481
theorem B8091521 : Blo 2129435 8091521 := bstep (se 2 (by rfl) ⟨3034320, by rfl⟩ : syracuseStep 8091521 = 6068641) B6068641
theorem B5394347 : Blo 2129435 5394347 := bstep (se 1 (by rfl) ⟨4045760, by rfl⟩ : syracuseStep 5394347 = 8091521) B8091521
theorem B3596231 : Blo 2129435 3596231 := bstep (se 1 (by rfl) ⟨2697173, by rfl⟩ : syracuseStep 3596231 = 5394347) B5394347
theorem B2397487 : Blo 2129435 2397487 := bstep (se 1 (by rfl) ⟨1798115, by rfl⟩ : syracuseStep 2397487 = 3596231) B3596231
theorem B3196649 : Blo 2129435 3196649 := bstep (se 2 (by rfl) ⟨1198743, by rfl⟩ : syracuseStep 3196649 = 2397487) B2397487
theorem B2131099 : Blo 2129435 2131099 := bstep (se 1 (by rfl) ⟨1598324, by rfl⟩ : syracuseStep 2131099 = 3196649) B3196649
theorem B18706133 : Blo 2129435 18706133 := bbase (se 7 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 18706133 = 438425) (by norm_num)
theorem B12470755 : Blo 2129435 12470755 := bstep (se 1 (by rfl) ⟨9353066, by rfl⟩ : syracuseStep 12470755 = 18706133) B18706133
theorem B16627673 : Blo 2129435 16627673 := bstep (se 2 (by rfl) ⟨6235377, by rfl⟩ : syracuseStep 16627673 = 12470755) B12470755
theorem B11085115 : Blo 2129435 11085115 := bstep (se 1 (by rfl) ⟨8313836, by rfl⟩ : syracuseStep 11085115 = 16627673) B16627673
theorem B14780153 : Blo 2129435 14780153 := bstep (se 2 (by rfl) ⟨5542557, by rfl⟩ : syracuseStep 14780153 = 11085115) B11085115
theorem B9853435 : Blo 2129435 9853435 := bstep (se 1 (by rfl) ⟨7390076, by rfl⟩ : syracuseStep 9853435 = 14780153) B14780153
theorem B13137913 : Blo 2129435 13137913 := bstep (se 2 (by rfl) ⟨4926717, by rfl⟩ : syracuseStep 13137913 = 9853435) B9853435
theorem B17517217 : Blo 2129435 17517217 := bstep (se 2 (by rfl) ⟨6568956, by rfl⟩ : syracuseStep 17517217 = 13137913) B13137913
theorem B23356289 : Blo 2129435 23356289 := bstep (se 2 (by rfl) ⟨8758608, by rfl⟩ : syracuseStep 23356289 = 17517217) B17517217
theorem B62283437 : Blo 2129435 62283437 := bstep (se 3 (by rfl) ⟨11678144, by rfl⟩ : syracuseStep 62283437 = 23356289) B23356289
theorem B41522291 : Blo 2129435 41522291 := bstep (se 1 (by rfl) ⟨31141718, by rfl⟩ : syracuseStep 41522291 = 62283437) B62283437
theorem B27681527 : Blo 2129435 27681527 := bstep (se 1 (by rfl) ⟨20761145, by rfl⟩ : syracuseStep 27681527 = 41522291) B41522291
theorem B18454351 : Blo 2129435 18454351 := bstep (se 1 (by rfl) ⟨13840763, by rfl⟩ : syracuseStep 18454351 = 27681527) B27681527
theorem B24605801 : Blo 2129435 24605801 := bstep (se 2 (by rfl) ⟨9227175, by rfl⟩ : syracuseStep 24605801 = 18454351) B18454351
theorem B16403867 : Blo 2129435 16403867 := bstep (se 1 (by rfl) ⟨12302900, by rfl⟩ : syracuseStep 16403867 = 24605801) B24605801
theorem B10935911 : Blo 2129435 10935911 := bstep (se 1 (by rfl) ⟨8201933, by rfl⟩ : syracuseStep 10935911 = 16403867) B16403867
theorem B29162429 : Blo 2129435 29162429 := bstep (se 3 (by rfl) ⟨5467955, by rfl⟩ : syracuseStep 29162429 = 10935911) B10935911
theorem B19441619 : Blo 2129435 19441619 := bstep (se 1 (by rfl) ⟨14581214, by rfl⟩ : syracuseStep 19441619 = 29162429) B29162429
theorem B12961079 : Blo 2129435 12961079 := bstep (se 1 (by rfl) ⟨9720809, by rfl⟩ : syracuseStep 12961079 = 19441619) B19441619
theorem B8640719 : Blo 2129435 8640719 := bstep (se 1 (by rfl) ⟨6480539, by rfl⟩ : syracuseStep 8640719 = 12961079) B12961079
theorem B5760479 : Blo 2129435 5760479 := bstep (se 1 (by rfl) ⟨4320359, by rfl⟩ : syracuseStep 5760479 = 8640719) B8640719
theorem B3840319 : Blo 2129435 3840319 := bstep (se 1 (by rfl) ⟨2880239, by rfl⟩ : syracuseStep 3840319 = 5760479) B5760479
theorem B5120425 : Blo 2129435 5120425 := bstep (se 2 (by rfl) ⟨1920159, by rfl⟩ : syracuseStep 5120425 = 3840319) B3840319
theorem B27308933 : Blo 2129435 27308933 := bstep (se 4 (by rfl) ⟨2560212, by rfl⟩ : syracuseStep 27308933 = 5120425) B5120425
theorem B18205955 : Blo 2129435 18205955 := bstep (se 1 (by rfl) ⟨13654466, by rfl⟩ : syracuseStep 18205955 = 27308933) B27308933
theorem B12137303 : Blo 2129435 12137303 := bstep (se 1 (by rfl) ⟨9102977, by rfl⟩ : syracuseStep 12137303 = 18205955) B18205955
theorem B8091535 : Blo 2129435 8091535 := bstep (se 1 (by rfl) ⟨6068651, by rfl⟩ : syracuseStep 8091535 = 12137303) B12137303
theorem B10788713 : Blo 2129435 10788713 := bstep (se 2 (by rfl) ⟨4045767, by rfl⟩ : syracuseStep 10788713 = 8091535) B8091535
theorem B7192475 : Blo 2129435 7192475 := bstep (se 1 (by rfl) ⟨5394356, by rfl⟩ : syracuseStep 7192475 = 10788713) B10788713
theorem B4794983 : Blo 2129435 4794983 := bstep (se 1 (by rfl) ⟨3596237, by rfl⟩ : syracuseStep 4794983 = 7192475) B7192475
theorem B3196655 : Blo 2129435 3196655 := bstep (se 1 (by rfl) ⟨2397491, by rfl⟩ : syracuseStep 3196655 = 4794983) B4794983
theorem B2131103 : Blo 2129435 2131103 := bstep (se 1 (by rfl) ⟨1598327, by rfl⟩ : syracuseStep 2131103 = 3196655) B3196655
theorem B3196661 : Blo 2129435 3196661 := bbase (se 5 (by rfl) ⟨149843, by rfl⟩ : syracuseStep 3196661 = 299687) (by norm_num)
theorem B2131107 : Blo 2129435 2131107 := bstep (se 1 (by rfl) ⟨1598330, by rfl⟩ : syracuseStep 2131107 = 3196661) B3196661
theorem B9103013 : Blo 2129435 9103013 := bbase (se 4 (by rfl) ⟨853407, by rfl⟩ : syracuseStep 9103013 = 1706815) (by norm_num)
theorem B6068675 : Blo 2129435 6068675 := bstep (se 1 (by rfl) ⟨4551506, by rfl⟩ : syracuseStep 6068675 = 9103013) B9103013
theorem B4045783 : Blo 2129435 4045783 := bstep (se 1 (by rfl) ⟨3034337, by rfl⟩ : syracuseStep 4045783 = 6068675) B6068675
theorem B5394377 : Blo 2129435 5394377 := bstep (se 2 (by rfl) ⟨2022891, by rfl⟩ : syracuseStep 5394377 = 4045783) B4045783
theorem B3596251 : Blo 2129435 3596251 := bstep (se 1 (by rfl) ⟨2697188, by rfl⟩ : syracuseStep 3596251 = 5394377) B5394377
theorem B4795001 : Blo 2129435 4795001 := bstep (se 2 (by rfl) ⟨1798125, by rfl⟩ : syracuseStep 4795001 = 3596251) B3596251
theorem B3196667 : Blo 2129435 3196667 := bstep (se 1 (by rfl) ⟨2397500, by rfl⟩ : syracuseStep 3196667 = 4795001) B4795001
theorem B2131111 : Blo 2129435 2131111 := bstep (se 1 (by rfl) ⟨1598333, by rfl⟩ : syracuseStep 2131111 = 3196667) B3196667
theorem B2397505 : Blo 2129435 2397505 := bbase (se 2 (by rfl) ⟨899064, by rfl⟩ : syracuseStep 2397505 = 1798129) (by norm_num)
theorem B3196673 : Blo 2129435 3196673 := bstep (se 2 (by rfl) ⟨1198752, by rfl⟩ : syracuseStep 3196673 = 2397505) B2397505
theorem B2131115 : Blo 2129435 2131115 := bstep (se 1 (by rfl) ⟨1598336, by rfl⟩ : syracuseStep 2131115 = 3196673) B3196673
theorem B5394397 : Blo 2129435 5394397 := bbase (se 3 (by rfl) ⟨1011449, by rfl⟩ : syracuseStep 5394397 = 2022899) (by norm_num)
theorem B7192529 : Blo 2129435 7192529 := bstep (se 2 (by rfl) ⟨2697198, by rfl⟩ : syracuseStep 7192529 = 5394397) B5394397
theorem B4795019 : Blo 2129435 4795019 := bstep (se 1 (by rfl) ⟨3596264, by rfl⟩ : syracuseStep 4795019 = 7192529) B7192529
theorem B3196679 : Blo 2129435 3196679 := bstep (se 1 (by rfl) ⟨2397509, by rfl⟩ : syracuseStep 3196679 = 4795019) B4795019
theorem B2131119 : Blo 2129435 2131119 := bstep (se 1 (by rfl) ⟨1598339, by rfl⟩ : syracuseStep 2131119 = 3196679) B3196679
theorem B3196685 : Blo 2129435 3196685 := bbase (se 3 (by rfl) ⟨599378, by rfl⟩ : syracuseStep 3196685 = 1198757) (by norm_num)
theorem B2131123 : Blo 2129435 2131123 := bstep (se 1 (by rfl) ⟨1598342, by rfl⟩ : syracuseStep 2131123 = 3196685) B3196685
theorem B4795037 : Blo 2129435 4795037 := bbase (se 3 (by rfl) ⟨899069, by rfl⟩ : syracuseStep 4795037 = 1798139) (by norm_num)
theorem B3196691 : Blo 2129435 3196691 := bstep (se 1 (by rfl) ⟨2397518, by rfl⟩ : syracuseStep 3196691 = 4795037) B4795037
theorem B2131127 : Blo 2129435 2131127 := bstep (se 1 (by rfl) ⟨1598345, by rfl⟩ : syracuseStep 2131127 = 3196691) B3196691
theorem B3596285 : Blo 2129435 3596285 := bbase (se 3 (by rfl) ⟨674303, by rfl⟩ : syracuseStep 3596285 = 1348607) (by norm_num)
theorem B2397523 : Blo 2129435 2397523 := bstep (se 1 (by rfl) ⟨1798142, by rfl⟩ : syracuseStep 2397523 = 3596285) B3596285
theorem B3196697 : Blo 2129435 3196697 := bstep (se 2 (by rfl) ⟨1198761, by rfl⟩ : syracuseStep 3196697 = 2397523) B2397523
theorem B2131131 : Blo 2129435 2131131 := bstep (se 1 (by rfl) ⟨1598348, by rfl⟩ : syracuseStep 2131131 = 3196697) B3196697
theorem B4551557 : Blo 2129435 4551557 := bbase (se 4 (by rfl) ⟨426708, by rfl⟩ : syracuseStep 4551557 = 853417) (by norm_num)
theorem B12137485 : Blo 2129435 12137485 := bstep (se 3 (by rfl) ⟨2275778, by rfl⟩ : syracuseStep 12137485 = 4551557) B4551557
theorem B16183313 : Blo 2129435 16183313 := bstep (se 2 (by rfl) ⟨6068742, by rfl⟩ : syracuseStep 16183313 = 12137485) B12137485
theorem B10788875 : Blo 2129435 10788875 := bstep (se 1 (by rfl) ⟨8091656, by rfl⟩ : syracuseStep 10788875 = 16183313) B16183313
theorem B7192583 : Blo 2129435 7192583 := bstep (se 1 (by rfl) ⟨5394437, by rfl⟩ : syracuseStep 7192583 = 10788875) B10788875
theorem B4795055 : Blo 2129435 4795055 := bstep (se 1 (by rfl) ⟨3596291, by rfl⟩ : syracuseStep 4795055 = 7192583) B7192583
theorem B3196703 : Blo 2129435 3196703 := bstep (se 1 (by rfl) ⟨2397527, by rfl⟩ : syracuseStep 3196703 = 4795055) B4795055
theorem B2131135 : Blo 2129435 2131135 := bstep (se 1 (by rfl) ⟨1598351, by rfl⟩ : syracuseStep 2131135 = 3196703) B3196703
theorem B3196709 : Blo 2129435 3196709 := bbase (se 4 (by rfl) ⟨299691, by rfl⟩ : syracuseStep 3196709 = 599383) (by norm_num)
theorem B2131139 : Blo 2129435 2131139 := bstep (se 1 (by rfl) ⟨1598354, by rfl⟩ : syracuseStep 2131139 = 3196709) B3196709
theorem B2697229 : Blo 2129435 2697229 := bbase (se 3 (by rfl) ⟨505730, by rfl⟩ : syracuseStep 2697229 = 1011461) (by norm_num)
theorem B3596305 : Blo 2129435 3596305 := bstep (se 2 (by rfl) ⟨1348614, by rfl⟩ : syracuseStep 3596305 = 2697229) B2697229
theorem B4795073 : Blo 2129435 4795073 := bstep (se 2 (by rfl) ⟨1798152, by rfl⟩ : syracuseStep 4795073 = 3596305) B3596305
theorem B3196715 : Blo 2129435 3196715 := bstep (se 1 (by rfl) ⟨2397536, by rfl⟩ : syracuseStep 3196715 = 4795073) B4795073
theorem B2131143 : Blo 2129435 2131143 := bstep (se 1 (by rfl) ⟨1598357, by rfl⟩ : syracuseStep 2131143 = 3196715) B3196715
theorem B2397541 : Blo 2129435 2397541 := bbase (se 4 (by rfl) ⟨224769, by rfl⟩ : syracuseStep 2397541 = 449539) (by norm_num)
theorem B3196721 : Blo 2129435 3196721 := bstep (se 2 (by rfl) ⟨1198770, by rfl⟩ : syracuseStep 3196721 = 2397541) B2397541
theorem B2131147 : Blo 2129435 2131147 := bstep (se 1 (by rfl) ⟨1598360, by rfl⟩ : syracuseStep 2131147 = 3196721) B3196721
theorem B6068789 : Blo 2129435 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B4045859 : Blo 2129435 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B2697239 : Blo 2129435 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B7192637 : Blo 2129435 7192637 := bstep (se 3 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 7192637 = 2697239) B2697239
theorem B4795091 : Blo 2129435 4795091 := bstep (se 1 (by rfl) ⟨3596318, by rfl⟩ : syracuseStep 4795091 = 7192637) B7192637
theorem B3196727 : Blo 2129435 3196727 := bstep (se 1 (by rfl) ⟨2397545, by rfl⟩ : syracuseStep 3196727 = 4795091) B4795091
theorem B2131151 : Blo 2129435 2131151 := bstep (se 1 (by rfl) ⟨1598363, by rfl⟩ : syracuseStep 2131151 = 3196727) B3196727
theorem B3196733 : Blo 2129435 3196733 := bbase (se 3 (by rfl) ⟨599387, by rfl⟩ : syracuseStep 3196733 = 1198775) (by norm_num)
theorem B2131155 : Blo 2129435 2131155 := bstep (se 1 (by rfl) ⟨1598366, by rfl⟩ : syracuseStep 2131155 = 3196733) B3196733
theorem B4795109 : Blo 2129435 4795109 := bbase (se 4 (by rfl) ⟨449541, by rfl⟩ : syracuseStep 4795109 = 899083) (by norm_num)
theorem B3196739 : Blo 2129435 3196739 := bstep (se 1 (by rfl) ⟨2397554, by rfl⟩ : syracuseStep 3196739 = 4795109) B4795109
theorem B2131159 : Blo 2129435 2131159 := bstep (se 1 (by rfl) ⟨1598369, by rfl⟩ : syracuseStep 2131159 = 3196739) B3196739
theorem B5394509 : Blo 2129435 5394509 := bbase (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) (by norm_num)
theorem B3596339 : Blo 2129435 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B2397559 : Blo 2129435 2397559 := bstep (se 1 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 2397559 = 3596339) B3596339
theorem B3196745 : Blo 2129435 3196745 := bstep (se 2 (by rfl) ⟨1198779, by rfl⟩ : syracuseStep 3196745 = 2397559) B2397559
theorem B2131163 : Blo 2129435 2131163 := bstep (se 1 (by rfl) ⟨1598372, by rfl⟩ : syracuseStep 2131163 = 3196745) B3196745
theorem B2275813 : Blo 2129435 2275813 := bbase (se 4 (by rfl) ⟨213357, by rfl⟩ : syracuseStep 2275813 = 426715) (by norm_num)
theorem B3034417 : Blo 2129435 3034417 := bstep (se 2 (by rfl) ⟨1137906, by rfl⟩ : syracuseStep 3034417 = 2275813) B2275813
theorem B4045889 : Blo 2129435 4045889 := bstep (se 2 (by rfl) ⟨1517208, by rfl⟩ : syracuseStep 4045889 = 3034417) B3034417
theorem B10789037 : Blo 2129435 10789037 := bstep (se 3 (by rfl) ⟨2022944, by rfl⟩ : syracuseStep 10789037 = 4045889) B4045889
theorem B7192691 : Blo 2129435 7192691 := bstep (se 1 (by rfl) ⟨5394518, by rfl⟩ : syracuseStep 7192691 = 10789037) B10789037
theorem B4795127 : Blo 2129435 4795127 := bstep (se 1 (by rfl) ⟨3596345, by rfl⟩ : syracuseStep 4795127 = 7192691) B7192691
theorem B3196751 : Blo 2129435 3196751 := bstep (se 1 (by rfl) ⟨2397563, by rfl⟩ : syracuseStep 3196751 = 4795127) B4795127
theorem B2131167 : Blo 2129435 2131167 := bstep (se 1 (by rfl) ⟨1598375, by rfl⟩ : syracuseStep 2131167 = 3196751) B3196751
theorem B3196757 : Blo 2129435 3196757 := bbase (se 9 (by rfl) ⟨9365, by rfl⟩ : syracuseStep 3196757 = 18731) (by norm_num)
theorem B2131171 : Blo 2129435 2131171 := bstep (se 1 (by rfl) ⟨1598378, by rfl⟩ : syracuseStep 2131171 = 3196757) B3196757
theorem B2160253 : Blo 2129435 2160253 := bbase (se 3 (by rfl) ⟨405047, by rfl⟩ : syracuseStep 2160253 = 810095) (by norm_num)
theorem B11521349 : Blo 2129435 11521349 := bstep (se 4 (by rfl) ⟨1080126, by rfl⟩ : syracuseStep 11521349 = 2160253) B2160253
theorem B7680899 : Blo 2129435 7680899 := bstep (se 1 (by rfl) ⟨5760674, by rfl⟩ : syracuseStep 7680899 = 11521349) B11521349
theorem B5120599 : Blo 2129435 5120599 := bstep (se 1 (by rfl) ⟨3840449, by rfl⟩ : syracuseStep 5120599 = 7680899) B7680899
theorem B6827465 : Blo 2129435 6827465 := bstep (se 2 (by rfl) ⟨2560299, by rfl⟩ : syracuseStep 6827465 = 5120599) B5120599
theorem B4551643 : Blo 2129435 4551643 := bstep (se 1 (by rfl) ⟨3413732, by rfl⟩ : syracuseStep 4551643 = 6827465) B6827465
theorem B6068857 : Blo 2129435 6068857 := bstep (se 2 (by rfl) ⟨2275821, by rfl⟩ : syracuseStep 6068857 = 4551643) B4551643
theorem B8091809 : Blo 2129435 8091809 := bstep (se 2 (by rfl) ⟨3034428, by rfl⟩ : syracuseStep 8091809 = 6068857) B6068857
theorem B5394539 : Blo 2129435 5394539 := bstep (se 1 (by rfl) ⟨4045904, by rfl⟩ : syracuseStep 5394539 = 8091809) B8091809
theorem B3596359 : Blo 2129435 3596359 := bstep (se 1 (by rfl) ⟨2697269, by rfl⟩ : syracuseStep 3596359 = 5394539) B5394539
theorem B4795145 : Blo 2129435 4795145 := bstep (se 2 (by rfl) ⟨1798179, by rfl⟩ : syracuseStep 4795145 = 3596359) B3596359
theorem B3196763 : Blo 2129435 3196763 := bstep (se 1 (by rfl) ⟨2397572, by rfl⟩ : syracuseStep 3196763 = 4795145) B4795145
theorem B2131175 : Blo 2129435 2131175 := bstep (se 1 (by rfl) ⟨1598381, by rfl⟩ : syracuseStep 2131175 = 3196763) B3196763
theorem B2397577 : Blo 2129435 2397577 := bbase (se 2 (by rfl) ⟨899091, by rfl⟩ : syracuseStep 2397577 = 1798183) (by norm_num)
theorem B3196769 : Blo 2129435 3196769 := bstep (se 2 (by rfl) ⟨1198788, by rfl⟩ : syracuseStep 3196769 = 2397577) B2397577
theorem B2131179 : Blo 2129435 2131179 := bstep (se 1 (by rfl) ⟨1598384, by rfl⟩ : syracuseStep 2131179 = 3196769) B3196769
theorem B2306881 : Blo 2129435 2306881 := bbase (se 2 (by rfl) ⟨865080, by rfl⟩ : syracuseStep 2306881 = 1730161) (by norm_num)
theorem B3075841 : Blo 2129435 3075841 := bstep (se 2 (by rfl) ⟨1153440, by rfl⟩ : syracuseStep 3075841 = 2306881) B2306881
theorem B4101121 : Blo 2129435 4101121 := bstep (se 2 (by rfl) ⟨1537920, by rfl⟩ : syracuseStep 4101121 = 3075841) B3075841
theorem B5468161 : Blo 2129435 5468161 := bstep (se 2 (by rfl) ⟨2050560, by rfl⟩ : syracuseStep 5468161 = 4101121) B4101121
theorem B7290881 : Blo 2129435 7290881 := bstep (se 2 (by rfl) ⟨2734080, by rfl⟩ : syracuseStep 7290881 = 5468161) B5468161
theorem B4860587 : Blo 2129435 4860587 := bstep (se 1 (by rfl) ⟨3645440, by rfl⟩ : syracuseStep 4860587 = 7290881) B7290881
theorem B3240391 : Blo 2129435 3240391 := bstep (se 1 (by rfl) ⟨2430293, by rfl⟩ : syracuseStep 3240391 = 4860587) B4860587
theorem B4320521 : Blo 2129435 4320521 := bstep (se 2 (by rfl) ⟨1620195, by rfl⟩ : syracuseStep 4320521 = 3240391) B3240391
theorem B46085557 : Blo 2129435 46085557 := bstep (se 5 (by rfl) ⟨2160260, by rfl⟩ : syracuseStep 46085557 = 4320521) B4320521
theorem B61447409 : Blo 2129435 61447409 := bstep (se 2 (by rfl) ⟨23042778, by rfl⟩ : syracuseStep 61447409 = 46085557) B46085557
theorem B40964939 : Blo 2129435 40964939 := bstep (se 1 (by rfl) ⟨30723704, by rfl⟩ : syracuseStep 40964939 = 61447409) B61447409
theorem B27309959 : Blo 2129435 27309959 := bstep (se 1 (by rfl) ⟨20482469, by rfl⟩ : syracuseStep 27309959 = 40964939) B40964939
theorem B18206639 : Blo 2129435 18206639 := bstep (se 1 (by rfl) ⟨13654979, by rfl⟩ : syracuseStep 18206639 = 27309959) B27309959
theorem B12137759 : Blo 2129435 12137759 := bstep (se 1 (by rfl) ⟨9103319, by rfl⟩ : syracuseStep 12137759 = 18206639) B18206639
theorem B8091839 : Blo 2129435 8091839 := bstep (se 1 (by rfl) ⟨6068879, by rfl⟩ : syracuseStep 8091839 = 12137759) B12137759
theorem B5394559 : Blo 2129435 5394559 := bstep (se 1 (by rfl) ⟨4045919, by rfl⟩ : syracuseStep 5394559 = 8091839) B8091839
theorem B7192745 : Blo 2129435 7192745 := bstep (se 2 (by rfl) ⟨2697279, by rfl⟩ : syracuseStep 7192745 = 5394559) B5394559
theorem B4795163 : Blo 2129435 4795163 := bstep (se 1 (by rfl) ⟨3596372, by rfl⟩ : syracuseStep 4795163 = 7192745) B7192745
theorem B3196775 : Blo 2129435 3196775 := bstep (se 1 (by rfl) ⟨2397581, by rfl⟩ : syracuseStep 3196775 = 4795163) B4795163
theorem B2131183 : Blo 2129435 2131183 := bstep (se 1 (by rfl) ⟨1598387, by rfl⟩ : syracuseStep 2131183 = 3196775) B3196775
theorem B3196781 : Blo 2129435 3196781 := bbase (se 3 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 3196781 = 1198793) (by norm_num)
theorem B2131187 : Blo 2129435 2131187 := bstep (se 1 (by rfl) ⟨1598390, by rfl⟩ : syracuseStep 2131187 = 3196781) B3196781
theorem B4795181 : Blo 2129435 4795181 := bbase (se 3 (by rfl) ⟨899096, by rfl⟩ : syracuseStep 4795181 = 1798193) (by norm_num)
theorem B3196787 : Blo 2129435 3196787 := bstep (se 1 (by rfl) ⟨2397590, by rfl⟩ : syracuseStep 3196787 = 4795181) B4795181
theorem B2131191 : Blo 2129435 2131191 := bstep (se 1 (by rfl) ⟨1598393, by rfl⟩ : syracuseStep 2131191 = 3196787) B3196787
theorem B3413765 : Blo 2129435 3413765 := bbase (se 4 (by rfl) ⟨320040, by rfl⟩ : syracuseStep 3413765 = 640081) (by norm_num)
theorem B9103373 : Blo 2129435 9103373 := bstep (se 3 (by rfl) ⟨1706882, by rfl⟩ : syracuseStep 9103373 = 3413765) B3413765
theorem B6068915 : Blo 2129435 6068915 := bstep (se 1 (by rfl) ⟨4551686, by rfl⟩ : syracuseStep 6068915 = 9103373) B9103373
theorem B4045943 : Blo 2129435 4045943 := bstep (se 1 (by rfl) ⟨3034457, by rfl⟩ : syracuseStep 4045943 = 6068915) B6068915
theorem B2697295 : Blo 2129435 2697295 := bstep (se 1 (by rfl) ⟨2022971, by rfl⟩ : syracuseStep 2697295 = 4045943) B4045943
theorem B3596393 : Blo 2129435 3596393 := bstep (se 2 (by rfl) ⟨1348647, by rfl⟩ : syracuseStep 3596393 = 2697295) B2697295
theorem B2397595 : Blo 2129435 2397595 := bstep (se 1 (by rfl) ⟨1798196, by rfl⟩ : syracuseStep 2397595 = 3596393) B3596393
theorem B3196793 : Blo 2129435 3196793 := bstep (se 2 (by rfl) ⟨1198797, by rfl⟩ : syracuseStep 3196793 = 2397595) B2397595
theorem B2131195 : Blo 2129435 2131195 := bstep (se 1 (by rfl) ⟨1598396, by rfl⟩ : syracuseStep 2131195 = 3196793) B3196793
theorem B12471317 : Blo 2129435 12471317 := bbase (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) (by norm_num)
theorem B8314211 : Blo 2129435 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B22171229 : Blo 2129435 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B14780819 : Blo 2129435 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B39415517 : Blo 2129435 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B26277011 : Blo 2129435 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B17518007 : Blo 2129435 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B11678671 : Blo 2129435 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B15571561 : Blo 2129435 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B20762081 : Blo 2129435 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B13841387 : Blo 2129435 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B9227591 : Blo 2129435 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B6151727 : Blo 2129435 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B4101151 : Blo 2129435 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B5468201 : Blo 2129435 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B3645467 : Blo 2129435 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B38884981 : Blo 2129435 38884981 := bstep (se 5 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 38884981 = 3645467) B3645467
theorem B51846641 : Blo 2129435 51846641 := bstep (se 2 (by rfl) ⟨19442490, by rfl⟩ : syracuseStep 51846641 = 38884981) B38884981
theorem B34564427 : Blo 2129435 34564427 := bstep (se 1 (by rfl) ⟨25923320, by rfl⟩ : syracuseStep 34564427 = 51846641) B51846641
theorem B23042951 : Blo 2129435 23042951 := bstep (se 1 (by rfl) ⟨17282213, by rfl⟩ : syracuseStep 23042951 = 34564427) B34564427
theorem B15361967 : Blo 2129435 15361967 := bstep (se 1 (by rfl) ⟨11521475, by rfl⟩ : syracuseStep 15361967 = 23042951) B23042951
theorem B10241311 : Blo 2129435 10241311 := bstep (se 1 (by rfl) ⟨7680983, by rfl⟩ : syracuseStep 10241311 = 15361967) B15361967
theorem B13655081 : Blo 2129435 13655081 := bstep (se 2 (by rfl) ⟨5120655, by rfl⟩ : syracuseStep 13655081 = 10241311) B10241311
theorem B36413549 : Blo 2129435 36413549 := bstep (se 3 (by rfl) ⟨6827540, by rfl⟩ : syracuseStep 36413549 = 13655081) B13655081
theorem B24275699 : Blo 2129435 24275699 := bstep (se 1 (by rfl) ⟨18206774, by rfl⟩ : syracuseStep 24275699 = 36413549) B36413549
theorem B16183799 : Blo 2129435 16183799 := bstep (se 1 (by rfl) ⟨12137849, by rfl⟩ : syracuseStep 16183799 = 24275699) B24275699
theorem B10789199 : Blo 2129435 10789199 := bstep (se 1 (by rfl) ⟨8091899, by rfl⟩ : syracuseStep 10789199 = 16183799) B16183799
theorem B7192799 : Blo 2129435 7192799 := bstep (se 1 (by rfl) ⟨5394599, by rfl⟩ : syracuseStep 7192799 = 10789199) B10789199
theorem B4795199 : Blo 2129435 4795199 := bstep (se 1 (by rfl) ⟨3596399, by rfl⟩ : syracuseStep 4795199 = 7192799) B7192799
theorem B3196799 : Blo 2129435 3196799 := bstep (se 1 (by rfl) ⟨2397599, by rfl⟩ : syracuseStep 3196799 = 4795199) B4795199
theorem B2131199 : Blo 2129435 2131199 := bstep (se 1 (by rfl) ⟨1598399, by rfl⟩ : syracuseStep 2131199 = 3196799) B3196799
theorem B3196805 : Blo 2129435 3196805 := bbase (se 4 (by rfl) ⟨299700, by rfl⟩ : syracuseStep 3196805 = 599401) (by norm_num)
theorem B2131203 : Blo 2129435 2131203 := bstep (se 1 (by rfl) ⟨1598402, by rfl⟩ : syracuseStep 2131203 = 3196805) B3196805
theorem B3596413 : Blo 2129435 3596413 := bbase (se 3 (by rfl) ⟨674327, by rfl⟩ : syracuseStep 3596413 = 1348655) (by norm_num)
theorem B4795217 : Blo 2129435 4795217 := bstep (se 2 (by rfl) ⟨1798206, by rfl⟩ : syracuseStep 4795217 = 3596413) B3596413
theorem B3196811 : Blo 2129435 3196811 := bstep (se 1 (by rfl) ⟨2397608, by rfl⟩ : syracuseStep 3196811 = 4795217) B4795217
theorem B2131207 : Blo 2129435 2131207 := bstep (se 1 (by rfl) ⟨1598405, by rfl⟩ : syracuseStep 2131207 = 3196811) B3196811
theorem B2397613 : Blo 2129435 2397613 := bbase (se 3 (by rfl) ⟨449552, by rfl⟩ : syracuseStep 2397613 = 899105) (by norm_num)
theorem B3196817 : Blo 2129435 3196817 := bstep (se 2 (by rfl) ⟨1198806, by rfl⟩ : syracuseStep 3196817 = 2397613) B2397613
theorem B2131211 : Blo 2129435 2131211 := bstep (se 1 (by rfl) ⟨1598408, by rfl⟩ : syracuseStep 2131211 = 3196817) B3196817
theorem B7192853 : Blo 2129435 7192853 := bbase (se 6 (by rfl) ⟨168582, by rfl⟩ : syracuseStep 7192853 = 337165) (by norm_num)
theorem B4795235 : Blo 2129435 4795235 := bstep (se 1 (by rfl) ⟨3596426, by rfl⟩ : syracuseStep 4795235 = 7192853) B7192853
theorem B3196823 : Blo 2129435 3196823 := bstep (se 1 (by rfl) ⟨2397617, by rfl⟩ : syracuseStep 3196823 = 4795235) B4795235
theorem B2131215 : Blo 2129435 2131215 := bstep (se 1 (by rfl) ⟨1598411, by rfl⟩ : syracuseStep 2131215 = 3196823) B3196823
theorem B3196829 : Blo 2129435 3196829 := bbase (se 3 (by rfl) ⟨599405, by rfl⟩ : syracuseStep 3196829 = 1198811) (by norm_num)
theorem B2131219 : Blo 2129435 2131219 := bstep (se 1 (by rfl) ⟨1598414, by rfl⟩ : syracuseStep 2131219 = 3196829) B3196829
theorem B4795253 : Blo 2129435 4795253 := bbase (se 5 (by rfl) ⟨224777, by rfl⟩ : syracuseStep 4795253 = 449555) (by norm_num)
theorem B3196835 : Blo 2129435 3196835 := bstep (se 1 (by rfl) ⟨2397626, by rfl⟩ : syracuseStep 3196835 = 4795253) B4795253
theorem B2131223 : Blo 2129435 2131223 := bstep (se 1 (by rfl) ⟨1598417, by rfl⟩ : syracuseStep 2131223 = 3196835) B3196835
theorem B16404821 : Blo 2129435 16404821 := bbase (se 10 (by rfl) ⟨24030, by rfl⟩ : syracuseStep 16404821 = 48061) (by norm_num)
theorem B10936547 : Blo 2129435 10936547 := bstep (se 1 (by rfl) ⟨8202410, by rfl⟩ : syracuseStep 10936547 = 16404821) B16404821
theorem B7291031 : Blo 2129435 7291031 := bstep (se 1 (by rfl) ⟨5468273, by rfl⟩ : syracuseStep 7291031 = 10936547) B10936547
theorem B19442749 : Blo 2129435 19442749 := bstep (se 3 (by rfl) ⟨3645515, by rfl⟩ : syracuseStep 19442749 = 7291031) B7291031
theorem B25923665 : Blo 2129435 25923665 := bstep (se 2 (by rfl) ⟨9721374, by rfl⟩ : syracuseStep 25923665 = 19442749) B19442749
theorem B69129773 : Blo 2129435 69129773 := bstep (se 3 (by rfl) ⟨12961832, by rfl⟩ : syracuseStep 69129773 = 25923665) B25923665
theorem B46086515 : Blo 2129435 46086515 := bstep (se 1 (by rfl) ⟨34564886, by rfl⟩ : syracuseStep 46086515 = 69129773) B69129773
theorem B30724343 : Blo 2129435 30724343 := bstep (se 1 (by rfl) ⟨23043257, by rfl⟩ : syracuseStep 30724343 = 46086515) B46086515
theorem B20482895 : Blo 2129435 20482895 := bstep (se 1 (by rfl) ⟨15362171, by rfl⟩ : syracuseStep 20482895 = 30724343) B30724343
theorem B13655263 : Blo 2129435 13655263 := bstep (se 1 (by rfl) ⟨10241447, by rfl⟩ : syracuseStep 13655263 = 20482895) B20482895
theorem B18207017 : Blo 2129435 18207017 := bstep (se 2 (by rfl) ⟨6827631, by rfl⟩ : syracuseStep 18207017 = 13655263) B13655263
theorem B12138011 : Blo 2129435 12138011 := bstep (se 1 (by rfl) ⟨9103508, by rfl⟩ : syracuseStep 12138011 = 18207017) B18207017
theorem B8092007 : Blo 2129435 8092007 := bstep (se 1 (by rfl) ⟨6069005, by rfl⟩ : syracuseStep 8092007 = 12138011) B12138011
theorem B5394671 : Blo 2129435 5394671 := bstep (se 1 (by rfl) ⟨4046003, by rfl⟩ : syracuseStep 5394671 = 8092007) B8092007
theorem B3596447 : Blo 2129435 3596447 := bstep (se 1 (by rfl) ⟨2697335, by rfl⟩ : syracuseStep 3596447 = 5394671) B5394671
theorem B2397631 : Blo 2129435 2397631 := bstep (se 1 (by rfl) ⟨1798223, by rfl⟩ : syracuseStep 2397631 = 3596447) B3596447
theorem B3196841 : Blo 2129435 3196841 := bstep (se 2 (by rfl) ⟨1198815, by rfl⟩ : syracuseStep 3196841 = 2397631) B2397631
theorem B2131227 : Blo 2129435 2131227 := bstep (se 1 (by rfl) ⟨1598420, by rfl⟩ : syracuseStep 2131227 = 3196841) B3196841
theorem B8092021 : Blo 2129435 8092021 := bbase (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) (by norm_num)
theorem B10789361 : Blo 2129435 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B7192907 : Blo 2129435 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B4795271 : Blo 2129435 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B3196847 : Blo 2129435 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B2131231 : Blo 2129435 2131231 := bstep (se 1 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 2131231 = 3196847) B3196847
theorem B3196853 : Blo 2129435 3196853 := bbase (se 5 (by rfl) ⟨149852, by rfl⟩ : syracuseStep 3196853 = 299705) (by norm_num)
theorem B2131235 : Blo 2129435 2131235 := bstep (se 1 (by rfl) ⟨1598426, by rfl⟩ : syracuseStep 2131235 = 3196853) B3196853
theorem B5394701 : Blo 2129435 5394701 := bbase (se 3 (by rfl) ⟨1011506, by rfl⟩ : syracuseStep 5394701 = 2023013) (by norm_num)
theorem B3596467 : Blo 2129435 3596467 := bstep (se 1 (by rfl) ⟨2697350, by rfl⟩ : syracuseStep 3596467 = 5394701) B5394701
theorem B4795289 : Blo 2129435 4795289 := bstep (se 2 (by rfl) ⟨1798233, by rfl⟩ : syracuseStep 4795289 = 3596467) B3596467
theorem B3196859 : Blo 2129435 3196859 := bstep (se 1 (by rfl) ⟨2397644, by rfl⟩ : syracuseStep 3196859 = 4795289) B4795289
theorem B2131239 : Blo 2129435 2131239 := bstep (se 1 (by rfl) ⟨1598429, by rfl⟩ : syracuseStep 2131239 = 3196859) B3196859
theorem B2397649 : Blo 2129435 2397649 := bbase (se 2 (by rfl) ⟨899118, by rfl⟩ : syracuseStep 2397649 = 1798237) (by norm_num)
theorem B3196865 : Blo 2129435 3196865 := bstep (se 2 (by rfl) ⟨1198824, by rfl⟩ : syracuseStep 3196865 = 2397649) B2397649
theorem B2131243 : Blo 2129435 2131243 := bstep (se 1 (by rfl) ⟨1598432, by rfl⟩ : syracuseStep 2131243 = 3196865) B3196865
theorem B4551797 : Blo 2129435 4551797 := bbase (se 5 (by rfl) ⟨213365, by rfl⟩ : syracuseStep 4551797 = 426731) (by norm_num)
theorem B3034531 : Blo 2129435 3034531 := bstep (se 1 (by rfl) ⟨2275898, by rfl⟩ : syracuseStep 3034531 = 4551797) B4551797
theorem B4046041 : Blo 2129435 4046041 := bstep (se 2 (by rfl) ⟨1517265, by rfl⟩ : syracuseStep 4046041 = 3034531) B3034531
theorem B5394721 : Blo 2129435 5394721 := bstep (se 2 (by rfl) ⟨2023020, by rfl⟩ : syracuseStep 5394721 = 4046041) B4046041
theorem B7192961 : Blo 2129435 7192961 := bstep (se 2 (by rfl) ⟨2697360, by rfl⟩ : syracuseStep 7192961 = 5394721) B5394721
theorem B4795307 : Blo 2129435 4795307 := bstep (se 1 (by rfl) ⟨3596480, by rfl⟩ : syracuseStep 4795307 = 7192961) B7192961
theorem B3196871 : Blo 2129435 3196871 := bstep (se 1 (by rfl) ⟨2397653, by rfl⟩ : syracuseStep 3196871 = 4795307) B4795307
theorem B2131247 : Blo 2129435 2131247 := bstep (se 1 (by rfl) ⟨1598435, by rfl⟩ : syracuseStep 2131247 = 3196871) B3196871
theorem B3196877 : Blo 2129435 3196877 := bbase (se 3 (by rfl) ⟨599414, by rfl⟩ : syracuseStep 3196877 = 1198829) (by norm_num)
theorem B2131251 : Blo 2129435 2131251 := bstep (se 1 (by rfl) ⟨1598438, by rfl⟩ : syracuseStep 2131251 = 3196877) B3196877
theorem B4795325 : Blo 2129435 4795325 := bbase (se 3 (by rfl) ⟨899123, by rfl⟩ : syracuseStep 4795325 = 1798247) (by norm_num)
theorem B3196883 : Blo 2129435 3196883 := bstep (se 1 (by rfl) ⟨2397662, by rfl⟩ : syracuseStep 3196883 = 4795325) B4795325
theorem B2131255 : Blo 2129435 2131255 := bstep (se 1 (by rfl) ⟨1598441, by rfl⟩ : syracuseStep 2131255 = 3196883) B3196883
theorem B3596501 : Blo 2129435 3596501 := bbase (se 7 (by rfl) ⟨42146, by rfl⟩ : syracuseStep 3596501 = 84293) (by norm_num)
theorem B2397667 : Blo 2129435 2397667 := bstep (se 1 (by rfl) ⟨1798250, by rfl⟩ : syracuseStep 2397667 = 3596501) B3596501
theorem B3196889 : Blo 2129435 3196889 := bstep (se 2 (by rfl) ⟨1198833, by rfl⟩ : syracuseStep 3196889 = 2397667) B2397667
theorem B2131259 : Blo 2129435 2131259 := bstep (se 1 (by rfl) ⟨1598444, by rfl⟩ : syracuseStep 2131259 = 3196889) B3196889
theorem B2560405 : Blo 2129435 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B3413873 : Blo 2129435 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B9103661 : Blo 2129435 9103661 := bstep (se 3 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 9103661 = 3413873) B3413873
theorem B6069107 : Blo 2129435 6069107 := bstep (se 1 (by rfl) ⟨4551830, by rfl⟩ : syracuseStep 6069107 = 9103661) B9103661
theorem B16184285 : Blo 2129435 16184285 := bstep (se 3 (by rfl) ⟨3034553, by rfl⟩ : syracuseStep 16184285 = 6069107) B6069107
theorem B10789523 : Blo 2129435 10789523 := bstep (se 1 (by rfl) ⟨8092142, by rfl⟩ : syracuseStep 10789523 = 16184285) B16184285
theorem B7193015 : Blo 2129435 7193015 := bstep (se 1 (by rfl) ⟨5394761, by rfl⟩ : syracuseStep 7193015 = 10789523) B10789523
theorem B4795343 : Blo 2129435 4795343 := bstep (se 1 (by rfl) ⟨3596507, by rfl⟩ : syracuseStep 4795343 = 7193015) B7193015
theorem B3196895 : Blo 2129435 3196895 := bstep (se 1 (by rfl) ⟨2397671, by rfl⟩ : syracuseStep 3196895 = 4795343) B4795343
theorem B2131263 : Blo 2129435 2131263 := bstep (se 1 (by rfl) ⟨1598447, by rfl⟩ : syracuseStep 2131263 = 3196895) B3196895
theorem B3196901 : Blo 2129435 3196901 := bbase (se 4 (by rfl) ⟨299709, by rfl⟩ : syracuseStep 3196901 = 599419) (by norm_num)
theorem B2131267 : Blo 2129435 2131267 := bstep (se 1 (by rfl) ⟨1598450, by rfl⟩ : syracuseStep 2131267 = 3196901) B3196901
theorem B2595349 : Blo 2129435 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B3460465 : Blo 2129435 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B18455813 : Blo 2129435 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B12303875 : Blo 2129435 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B8202583 : Blo 2129435 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B10936777 : Blo 2129435 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B14582369 : Blo 2129435 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B9721579 : Blo 2129435 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B12962105 : Blo 2129435 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B8641403 : Blo 2129435 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B5760935 : Blo 2129435 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B3840623 : Blo 2129435 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B2560415 : Blo 2129435 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B6827773 : Blo 2129435 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B9103697 : Blo 2129435 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B6069131 : Blo 2129435 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B4046087 : Blo 2129435 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B2697391 : Blo 2129435 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B3596521 : Blo 2129435 3596521 := bstep (se 2 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 3596521 = 2697391) B2697391
theorem B4795361 : Blo 2129435 4795361 := bstep (se 2 (by rfl) ⟨1798260, by rfl⟩ : syracuseStep 4795361 = 3596521) B3596521
theorem B3196907 : Blo 2129435 3196907 := bstep (se 1 (by rfl) ⟨2397680, by rfl⟩ : syracuseStep 3196907 = 4795361) B4795361
theorem B2131271 : Blo 2129435 2131271 := bstep (se 1 (by rfl) ⟨1598453, by rfl⟩ : syracuseStep 2131271 = 3196907) B3196907
theorem B2397685 : Blo 2129435 2397685 := bbase (se 5 (by rfl) ⟨112391, by rfl⟩ : syracuseStep 2397685 = 224783) (by norm_num)
theorem B3196913 : Blo 2129435 3196913 := bstep (se 2 (by rfl) ⟨1198842, by rfl⟩ : syracuseStep 3196913 = 2397685) B2397685
theorem B2131275 : Blo 2129435 2131275 := bstep (se 1 (by rfl) ⟨1598456, by rfl⟩ : syracuseStep 2131275 = 3196913) B3196913
theorem B2697401 : Blo 2129435 2697401 := bbase (se 2 (by rfl) ⟨1011525, by rfl⟩ : syracuseStep 2697401 = 2023051) (by norm_num)
theorem B7193069 : Blo 2129435 7193069 := bstep (se 3 (by rfl) ⟨1348700, by rfl⟩ : syracuseStep 7193069 = 2697401) B2697401
theorem B4795379 : Blo 2129435 4795379 := bstep (se 1 (by rfl) ⟨3596534, by rfl⟩ : syracuseStep 4795379 = 7193069) B7193069
theorem B3196919 : Blo 2129435 3196919 := bstep (se 1 (by rfl) ⟨2397689, by rfl⟩ : syracuseStep 3196919 = 4795379) B4795379
theorem B2131279 : Blo 2129435 2131279 := bstep (se 1 (by rfl) ⟨1598459, by rfl⟩ : syracuseStep 2131279 = 3196919) B3196919
theorem B3196925 : Blo 2129435 3196925 := bbase (se 3 (by rfl) ⟨599423, by rfl⟩ : syracuseStep 3196925 = 1198847) (by norm_num)
theorem B2131283 : Blo 2129435 2131283 := bstep (se 1 (by rfl) ⟨1598462, by rfl⟩ : syracuseStep 2131283 = 3196925) B3196925
theorem B4795397 : Blo 2129435 4795397 := bbase (se 4 (by rfl) ⟨449568, by rfl⟩ : syracuseStep 4795397 = 899137) (by norm_num)
theorem B3196931 : Blo 2129435 3196931 := bstep (se 1 (by rfl) ⟨2397698, by rfl⟩ : syracuseStep 3196931 = 4795397) B4795397
theorem B2131287 : Blo 2129435 2131287 := bstep (se 1 (by rfl) ⟨1598465, by rfl⟩ : syracuseStep 2131287 = 3196931) B3196931
theorem B4046125 : Blo 2129435 4046125 := bbase (se 3 (by rfl) ⟨758648, by rfl⟩ : syracuseStep 4046125 = 1517297) (by norm_num)
theorem B5394833 : Blo 2129435 5394833 := bstep (se 2 (by rfl) ⟨2023062, by rfl⟩ : syracuseStep 5394833 = 4046125) B4046125
theorem B3596555 : Blo 2129435 3596555 := bstep (se 1 (by rfl) ⟨2697416, by rfl⟩ : syracuseStep 3596555 = 5394833) B5394833
theorem B2397703 : Blo 2129435 2397703 := bstep (se 1 (by rfl) ⟨1798277, by rfl⟩ : syracuseStep 2397703 = 3596555) B3596555
theorem B3196937 : Blo 2129435 3196937 := bstep (se 2 (by rfl) ⟨1198851, by rfl⟩ : syracuseStep 3196937 = 2397703) B2397703
theorem B2131291 : Blo 2129435 2131291 := bstep (se 1 (by rfl) ⟨1598468, by rfl⟩ : syracuseStep 2131291 = 3196937) B3196937
theorem B10789685 : Blo 2129435 10789685 := bbase (se 5 (by rfl) ⟨505766, by rfl⟩ : syracuseStep 10789685 = 1011533) (by norm_num)
theorem B7193123 : Blo 2129435 7193123 := bstep (se 1 (by rfl) ⟨5394842, by rfl⟩ : syracuseStep 7193123 = 10789685) B10789685
theorem B4795415 : Blo 2129435 4795415 := bstep (se 1 (by rfl) ⟨3596561, by rfl⟩ : syracuseStep 4795415 = 7193123) B7193123
theorem B3196943 : Blo 2129435 3196943 := bstep (se 1 (by rfl) ⟨2397707, by rfl⟩ : syracuseStep 3196943 = 4795415) B4795415
theorem B2131295 : Blo 2129435 2131295 := bstep (se 1 (by rfl) ⟨1598471, by rfl⟩ : syracuseStep 2131295 = 3196943) B3196943
theorem B3196949 : Blo 2129435 3196949 := bbase (se 6 (by rfl) ⟨74928, by rfl⟩ : syracuseStep 3196949 = 149857) (by norm_num)
theorem B2131299 : Blo 2129435 2131299 := bstep (se 1 (by rfl) ⟨1598474, by rfl⟩ : syracuseStep 2131299 = 3196949) B3196949
theorem B2560453 : Blo 2129435 2560453 := bbase (se 4 (by rfl) ⟨240042, by rfl⟩ : syracuseStep 2560453 = 480085) (by norm_num)
theorem B13655749 : Blo 2129435 13655749 := bstep (se 4 (by rfl) ⟨1280226, by rfl⟩ : syracuseStep 13655749 = 2560453) B2560453
theorem B18207665 : Blo 2129435 18207665 := bstep (se 2 (by rfl) ⟨6827874, by rfl⟩ : syracuseStep 18207665 = 13655749) B13655749
theorem B12138443 : Blo 2129435 12138443 := bstep (se 1 (by rfl) ⟨9103832, by rfl⟩ : syracuseStep 12138443 = 18207665) B18207665
theorem B8092295 : Blo 2129435 8092295 := bstep (se 1 (by rfl) ⟨6069221, by rfl⟩ : syracuseStep 8092295 = 12138443) B12138443
theorem B5394863 : Blo 2129435 5394863 := bstep (se 1 (by rfl) ⟨4046147, by rfl⟩ : syracuseStep 5394863 = 8092295) B8092295
theorem B3596575 : Blo 2129435 3596575 := bstep (se 1 (by rfl) ⟨2697431, by rfl⟩ : syracuseStep 3596575 = 5394863) B5394863
theorem B4795433 : Blo 2129435 4795433 := bstep (se 2 (by rfl) ⟨1798287, by rfl⟩ : syracuseStep 4795433 = 3596575) B3596575
theorem B3196955 : Blo 2129435 3196955 := bstep (se 1 (by rfl) ⟨2397716, by rfl⟩ : syracuseStep 3196955 = 4795433) B4795433
theorem B2131303 : Blo 2129435 2131303 := bstep (se 1 (by rfl) ⟨1598477, by rfl⟩ : syracuseStep 2131303 = 3196955) B3196955
theorem B2397721 : Blo 2129435 2397721 := bbase (se 2 (by rfl) ⟨899145, by rfl⟩ : syracuseStep 2397721 = 1798291) (by norm_num)
theorem B3196961 : Blo 2129435 3196961 := bstep (se 2 (by rfl) ⟨1198860, by rfl⟩ : syracuseStep 3196961 = 2397721) B2397721
theorem B2131307 : Blo 2129435 2131307 := bstep (se 1 (by rfl) ⟨1598480, by rfl⟩ : syracuseStep 2131307 = 3196961) B3196961
theorem B8092325 : Blo 2129435 8092325 := bbase (se 4 (by rfl) ⟨758655, by rfl⟩ : syracuseStep 8092325 = 1517311) (by norm_num)
theorem B5394883 : Blo 2129435 5394883 := bstep (se 1 (by rfl) ⟨4046162, by rfl⟩ : syracuseStep 5394883 = 8092325) B8092325
theorem B7193177 : Blo 2129435 7193177 := bstep (se 2 (by rfl) ⟨2697441, by rfl⟩ : syracuseStep 7193177 = 5394883) B5394883
theorem B4795451 : Blo 2129435 4795451 := bstep (se 1 (by rfl) ⟨3596588, by rfl⟩ : syracuseStep 4795451 = 7193177) B7193177
theorem B3196967 : Blo 2129435 3196967 := bstep (se 1 (by rfl) ⟨2397725, by rfl⟩ : syracuseStep 3196967 = 4795451) B4795451
theorem B2131311 : Blo 2129435 2131311 := bstep (se 1 (by rfl) ⟨1598483, by rfl⟩ : syracuseStep 2131311 = 3196967) B3196967
theorem B3196973 : Blo 2129435 3196973 := bbase (se 3 (by rfl) ⟨599432, by rfl⟩ : syracuseStep 3196973 = 1198865) (by norm_num)
theorem B2131315 : Blo 2129435 2131315 := bstep (se 1 (by rfl) ⟨1598486, by rfl⟩ : syracuseStep 2131315 = 3196973) B3196973
theorem B4795469 : Blo 2129435 4795469 := bbase (se 3 (by rfl) ⟨899150, by rfl⟩ : syracuseStep 4795469 = 1798301) (by norm_num)
theorem B3196979 : Blo 2129435 3196979 := bstep (se 1 (by rfl) ⟨2397734, by rfl⟩ : syracuseStep 3196979 = 4795469) B4795469
theorem B2131319 : Blo 2129435 2131319 := bstep (se 1 (by rfl) ⟨1598489, by rfl⟩ : syracuseStep 2131319 = 3196979) B3196979
theorem B2697457 : Blo 2129435 2697457 := bbase (se 2 (by rfl) ⟨1011546, by rfl⟩ : syracuseStep 2697457 = 2023093) (by norm_num)
theorem B3596609 : Blo 2129435 3596609 := bstep (se 2 (by rfl) ⟨1348728, by rfl⟩ : syracuseStep 3596609 = 2697457) B2697457
theorem B2397739 : Blo 2129435 2397739 := bstep (se 1 (by rfl) ⟨1798304, by rfl⟩ : syracuseStep 2397739 = 3596609) B3596609
theorem B3196985 : Blo 2129435 3196985 := bstep (se 2 (by rfl) ⟨1198869, by rfl⟩ : syracuseStep 3196985 = 2397739) B2397739
theorem B2131323 : Blo 2129435 2131323 := bstep (se 1 (by rfl) ⟨1598492, by rfl⟩ : syracuseStep 2131323 = 3196985) B3196985
theorem B17283253 : Blo 2129435 17283253 := bbase (se 5 (by rfl) ⟨810152, by rfl⟩ : syracuseStep 17283253 = 1620305) (by norm_num)
theorem B23044337 : Blo 2129435 23044337 := bstep (se 2 (by rfl) ⟨8641626, by rfl⟩ : syracuseStep 23044337 = 17283253) B17283253
theorem B15362891 : Blo 2129435 15362891 := bstep (se 1 (by rfl) ⟨11522168, by rfl⟩ : syracuseStep 15362891 = 23044337) B23044337
theorem B10241927 : Blo 2129435 10241927 := bstep (se 1 (by rfl) ⟨7681445, by rfl⟩ : syracuseStep 10241927 = 15362891) B15362891
theorem B6827951 : Blo 2129435 6827951 := bstep (se 1 (by rfl) ⟨5120963, by rfl⟩ : syracuseStep 6827951 = 10241927) B10241927
theorem B4551967 : Blo 2129435 4551967 := bstep (se 1 (by rfl) ⟨3413975, by rfl⟩ : syracuseStep 4551967 = 6827951) B6827951
theorem B24277157 : Blo 2129435 24277157 := bstep (se 4 (by rfl) ⟨2275983, by rfl⟩ : syracuseStep 24277157 = 4551967) B4551967
theorem B16184771 : Blo 2129435 16184771 := bstep (se 1 (by rfl) ⟨12138578, by rfl⟩ : syracuseStep 16184771 = 24277157) B24277157
theorem B10789847 : Blo 2129435 10789847 := bstep (se 1 (by rfl) ⟨8092385, by rfl⟩ : syracuseStep 10789847 = 16184771) B16184771
theorem B7193231 : Blo 2129435 7193231 := bstep (se 1 (by rfl) ⟨5394923, by rfl⟩ : syracuseStep 7193231 = 10789847) B10789847
theorem B4795487 : Blo 2129435 4795487 := bstep (se 1 (by rfl) ⟨3596615, by rfl⟩ : syracuseStep 4795487 = 7193231) B7193231
theorem B3196991 : Blo 2129435 3196991 := bstep (se 1 (by rfl) ⟨2397743, by rfl⟩ : syracuseStep 3196991 = 4795487) B4795487
theorem B2131327 : Blo 2129435 2131327 := bstep (se 1 (by rfl) ⟨1598495, by rfl⟩ : syracuseStep 2131327 = 3196991) B3196991
theorem B3196997 : Blo 2129435 3196997 := bbase (se 4 (by rfl) ⟨299718, by rfl⟩ : syracuseStep 3196997 = 599437) (by norm_num)
theorem B2131331 : Blo 2129435 2131331 := bstep (se 1 (by rfl) ⟨1598498, by rfl⟩ : syracuseStep 2131331 = 3196997) B3196997
theorem B3596629 : Blo 2129435 3596629 := bbase (se 10 (by rfl) ⟨5268, by rfl⟩ : syracuseStep 3596629 = 10537) (by norm_num)
theorem B4795505 : Blo 2129435 4795505 := bstep (se 2 (by rfl) ⟨1798314, by rfl⟩ : syracuseStep 4795505 = 3596629) B3596629
theorem B3197003 : Blo 2129435 3197003 := bstep (se 1 (by rfl) ⟨2397752, by rfl⟩ : syracuseStep 3197003 = 4795505) B4795505
theorem B2131335 : Blo 2129435 2131335 := bstep (se 1 (by rfl) ⟨1598501, by rfl⟩ : syracuseStep 2131335 = 3197003) B3197003
theorem B2397757 : Blo 2129435 2397757 := bbase (se 3 (by rfl) ⟨449579, by rfl⟩ : syracuseStep 2397757 = 899159) (by norm_num)
theorem B3197009 : Blo 2129435 3197009 := bstep (se 2 (by rfl) ⟨1198878, by rfl⟩ : syracuseStep 3197009 = 2397757) B2397757
theorem B2131339 : Blo 2129435 2131339 := bstep (se 1 (by rfl) ⟨1598504, by rfl⟩ : syracuseStep 2131339 = 3197009) B3197009
theorem B7193285 : Blo 2129435 7193285 := bbase (se 4 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 7193285 = 1348741) (by norm_num)
theorem B4795523 : Blo 2129435 4795523 := bstep (se 1 (by rfl) ⟨3596642, by rfl⟩ : syracuseStep 4795523 = 7193285) B7193285
theorem B3197015 : Blo 2129435 3197015 := bstep (se 1 (by rfl) ⟨2397761, by rfl⟩ : syracuseStep 3197015 = 4795523) B4795523
theorem B2131343 : Blo 2129435 2131343 := bstep (se 1 (by rfl) ⟨1598507, by rfl⟩ : syracuseStep 2131343 = 3197015) B3197015
theorem B3197021 : Blo 2129435 3197021 := bbase (se 3 (by rfl) ⟨599441, by rfl⟩ : syracuseStep 3197021 = 1198883) (by norm_num)
theorem B2131347 : Blo 2129435 2131347 := bstep (se 1 (by rfl) ⟨1598510, by rfl⟩ : syracuseStep 2131347 = 3197021) B3197021
theorem B4795541 : Blo 2129435 4795541 := bbase (se 6 (by rfl) ⟨112395, by rfl⟩ : syracuseStep 4795541 = 224791) (by norm_num)
theorem B3197027 : Blo 2129435 3197027 := bstep (se 1 (by rfl) ⟨2397770, by rfl⟩ : syracuseStep 3197027 = 4795541) B4795541
theorem B2131351 : Blo 2129435 2131351 := bstep (se 1 (by rfl) ⟨1598513, by rfl⟩ : syracuseStep 2131351 = 3197027) B3197027
theorem B3034685 : Blo 2129435 3034685 := bbase (se 3 (by rfl) ⟨569003, by rfl⟩ : syracuseStep 3034685 = 1138007) (by norm_num)
theorem B8092493 : Blo 2129435 8092493 := bstep (se 3 (by rfl) ⟨1517342, by rfl⟩ : syracuseStep 8092493 = 3034685) B3034685
theorem B5394995 : Blo 2129435 5394995 := bstep (se 1 (by rfl) ⟨4046246, by rfl⟩ : syracuseStep 5394995 = 8092493) B8092493
theorem B3596663 : Blo 2129435 3596663 := bstep (se 1 (by rfl) ⟨2697497, by rfl⟩ : syracuseStep 3596663 = 5394995) B5394995
theorem B2397775 : Blo 2129435 2397775 := bstep (se 1 (by rfl) ⟨1798331, by rfl⟩ : syracuseStep 2397775 = 3596663) B3596663
theorem B3197033 : Blo 2129435 3197033 := bstep (se 2 (by rfl) ⟨1198887, by rfl⟩ : syracuseStep 3197033 = 2397775) B2397775
theorem B2131355 : Blo 2129435 2131355 := bstep (se 1 (by rfl) ⟨1598516, by rfl⟩ : syracuseStep 2131355 = 3197033) B3197033
theorem B4860989 : Blo 2129435 4860989 := bbase (se 3 (by rfl) ⟨911435, by rfl⟩ : syracuseStep 4860989 = 1822871) (by norm_num)
theorem B3240659 : Blo 2129435 3240659 := bstep (se 1 (by rfl) ⟨2430494, by rfl⟩ : syracuseStep 3240659 = 4860989) B4860989
theorem B2160439 : Blo 2129435 2160439 := bstep (se 1 (by rfl) ⟨1620329, by rfl⟩ : syracuseStep 2160439 = 3240659) B3240659
theorem B11522341 : Blo 2129435 11522341 := bstep (se 4 (by rfl) ⟨1080219, by rfl⟩ : syracuseStep 11522341 = 2160439) B2160439
theorem B15363121 : Blo 2129435 15363121 := bstep (se 2 (by rfl) ⟨5761170, by rfl⟩ : syracuseStep 15363121 = 11522341) B11522341
theorem B20484161 : Blo 2129435 20484161 := bstep (se 2 (by rfl) ⟨7681560, by rfl⟩ : syracuseStep 20484161 = 15363121) B15363121
theorem B13656107 : Blo 2129435 13656107 := bstep (se 1 (by rfl) ⟨10242080, by rfl⟩ : syracuseStep 13656107 = 20484161) B20484161
theorem B9104071 : Blo 2129435 9104071 := bstep (se 1 (by rfl) ⟨6828053, by rfl⟩ : syracuseStep 9104071 = 13656107) B13656107
theorem B12138761 : Blo 2129435 12138761 := bstep (se 2 (by rfl) ⟨4552035, by rfl⟩ : syracuseStep 12138761 = 9104071) B9104071
theorem B8092507 : Blo 2129435 8092507 := bstep (se 1 (by rfl) ⟨6069380, by rfl⟩ : syracuseStep 8092507 = 12138761) B12138761
theorem B10790009 : Blo 2129435 10790009 := bstep (se 2 (by rfl) ⟨4046253, by rfl⟩ : syracuseStep 10790009 = 8092507) B8092507
theorem B7193339 : Blo 2129435 7193339 := bstep (se 1 (by rfl) ⟨5395004, by rfl⟩ : syracuseStep 7193339 = 10790009) B10790009
theorem B4795559 : Blo 2129435 4795559 := bstep (se 1 (by rfl) ⟨3596669, by rfl⟩ : syracuseStep 4795559 = 7193339) B7193339
theorem B3197039 : Blo 2129435 3197039 := bstep (se 1 (by rfl) ⟨2397779, by rfl⟩ : syracuseStep 3197039 = 4795559) B4795559
theorem B2131359 : Blo 2129435 2131359 := bstep (se 1 (by rfl) ⟨1598519, by rfl⟩ : syracuseStep 2131359 = 3197039) B3197039
theorem B3197045 : Blo 2129435 3197045 := bbase (se 5 (by rfl) ⟨149861, by rfl⟩ : syracuseStep 3197045 = 299723) (by norm_num)
theorem B2131363 : Blo 2129435 2131363 := bstep (se 1 (by rfl) ⟨1598522, by rfl⟩ : syracuseStep 2131363 = 3197045) B3197045
theorem B4046269 : Blo 2129435 4046269 := bbase (se 3 (by rfl) ⟨758675, by rfl⟩ : syracuseStep 4046269 = 1517351) (by norm_num)
theorem B5395025 : Blo 2129435 5395025 := bstep (se 2 (by rfl) ⟨2023134, by rfl⟩ : syracuseStep 5395025 = 4046269) B4046269
theorem B3596683 : Blo 2129435 3596683 := bstep (se 1 (by rfl) ⟨2697512, by rfl⟩ : syracuseStep 3596683 = 5395025) B5395025
theorem B4795577 : Blo 2129435 4795577 := bstep (se 2 (by rfl) ⟨1798341, by rfl⟩ : syracuseStep 4795577 = 3596683) B3596683
theorem B3197051 : Blo 2129435 3197051 := bstep (se 1 (by rfl) ⟨2397788, by rfl⟩ : syracuseStep 3197051 = 4795577) B4795577
theorem B2131367 : Blo 2129435 2131367 := bstep (se 1 (by rfl) ⟨1598525, by rfl⟩ : syracuseStep 2131367 = 3197051) B3197051
theorem B2397793 : Blo 2129435 2397793 := bbase (se 2 (by rfl) ⟨899172, by rfl⟩ : syracuseStep 2397793 = 1798345) (by norm_num)
theorem B3197057 : Blo 2129435 3197057 := bstep (se 2 (by rfl) ⟨1198896, by rfl⟩ : syracuseStep 3197057 = 2397793) B2397793
theorem B2131371 : Blo 2129435 2131371 := bstep (se 1 (by rfl) ⟨1598528, by rfl⟩ : syracuseStep 2131371 = 3197057) B3197057
theorem B5395045 : Blo 2129435 5395045 := bbase (se 4 (by rfl) ⟨505785, by rfl⟩ : syracuseStep 5395045 = 1011571) (by norm_num)
theorem B7193393 : Blo 2129435 7193393 := bstep (se 2 (by rfl) ⟨2697522, by rfl⟩ : syracuseStep 7193393 = 5395045) B5395045
theorem B4795595 : Blo 2129435 4795595 := bstep (se 1 (by rfl) ⟨3596696, by rfl⟩ : syracuseStep 4795595 = 7193393) B7193393
theorem B3197063 : Blo 2129435 3197063 := bstep (se 1 (by rfl) ⟨2397797, by rfl⟩ : syracuseStep 3197063 = 4795595) B4795595
theorem B2131375 : Blo 2129435 2131375 := bstep (se 1 (by rfl) ⟨1598531, by rfl⟩ : syracuseStep 2131375 = 3197063) B3197063
theorem B3197069 : Blo 2129435 3197069 := bbase (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) (by norm_num)
theorem B2131379 : Blo 2129435 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B4795613 : Blo 2129435 4795613 := bbase (se 3 (by rfl) ⟨899177, by rfl⟩ : syracuseStep 4795613 = 1798355) (by norm_num)
theorem B3197075 : Blo 2129435 3197075 := bstep (se 1 (by rfl) ⟨2397806, by rfl⟩ : syracuseStep 3197075 = 4795613) B4795613
theorem B2131383 : Blo 2129435 2131383 := bstep (se 1 (by rfl) ⟨1598537, by rfl⟩ : syracuseStep 2131383 = 3197075) B3197075
theorem B3596717 : Blo 2129435 3596717 := bbase (se 3 (by rfl) ⟨674384, by rfl⟩ : syracuseStep 3596717 = 1348769) (by norm_num)
theorem B2397811 : Blo 2129435 2397811 := bstep (se 1 (by rfl) ⟨1798358, by rfl⟩ : syracuseStep 2397811 = 3596717) B3596717
theorem B3197081 : Blo 2129435 3197081 := bstep (se 2 (by rfl) ⟨1198905, by rfl⟩ : syracuseStep 3197081 = 2397811) B2397811
theorem B2131387 : Blo 2129435 2131387 := bstep (se 1 (by rfl) ⟨1598540, by rfl⟩ : syracuseStep 2131387 = 3197081) B3197081
theorem B35517205 : Blo 2129435 35517205 := bbase (se 6 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 35517205 = 1664869) (by norm_num)
theorem B47356273 : Blo 2129435 47356273 := bstep (se 2 (by rfl) ⟨17758602, by rfl⟩ : syracuseStep 47356273 = 35517205) B35517205
theorem B63141697 : Blo 2129435 63141697 := bstep (se 2 (by rfl) ⟨23678136, by rfl⟩ : syracuseStep 63141697 = 47356273) B47356273
theorem B84188929 : Blo 2129435 84188929 := bstep (se 2 (by rfl) ⟨31570848, by rfl⟩ : syracuseStep 84188929 = 63141697) B63141697
theorem B112251905 : Blo 2129435 112251905 := bstep (se 2 (by rfl) ⟨42094464, by rfl⟩ : syracuseStep 112251905 = 84188929) B84188929
theorem B74834603 : Blo 2129435 74834603 := bstep (se 1 (by rfl) ⟨56125952, by rfl⟩ : syracuseStep 74834603 = 112251905) B112251905
theorem B49889735 : Blo 2129435 49889735 := bstep (se 1 (by rfl) ⟨37417301, by rfl⟩ : syracuseStep 49889735 = 74834603) B74834603
theorem B33259823 : Blo 2129435 33259823 := bstep (se 1 (by rfl) ⟨24944867, by rfl⟩ : syracuseStep 33259823 = 49889735) B49889735
theorem B22173215 : Blo 2129435 22173215 := bstep (se 1 (by rfl) ⟨16629911, by rfl⟩ : syracuseStep 22173215 = 33259823) B33259823
theorem B59128573 : Blo 2129435 59128573 := bstep (se 3 (by rfl) ⟨11086607, by rfl⟩ : syracuseStep 59128573 = 22173215) B22173215
theorem B1261409557 : Blo 2129435 1261409557 := bstep (se 6 (by rfl) ⟨29564286, by rfl⟩ : syracuseStep 1261409557 = 59128573) B59128573
theorem B1681879409 : Blo 2129435 1681879409 := bstep (se 2 (by rfl) ⟨630704778, by rfl⟩ : syracuseStep 1681879409 = 1261409557) B1261409557
theorem B1121252939 : Blo 2129435 1121252939 := bstep (se 1 (by rfl) ⟨840939704, by rfl⟩ : syracuseStep 1121252939 = 1681879409) B1681879409
theorem B747501959 : Blo 2129435 747501959 := bstep (se 1 (by rfl) ⟨560626469, by rfl⟩ : syracuseStep 747501959 = 1121252939) B1121252939
theorem B498334639 : Blo 2129435 498334639 := bstep (se 1 (by rfl) ⟨373750979, by rfl⟩ : syracuseStep 498334639 = 747501959) B747501959
theorem B664446185 : Blo 2129435 664446185 := bstep (se 2 (by rfl) ⟨249167319, by rfl⟩ : syracuseStep 664446185 = 498334639) B498334639
theorem B442964123 : Blo 2129435 442964123 := bstep (se 1 (by rfl) ⟨332223092, by rfl⟩ : syracuseStep 442964123 = 664446185) B664446185
theorem B295309415 : Blo 2129435 295309415 := bstep (se 1 (by rfl) ⟨221482061, by rfl⟩ : syracuseStep 295309415 = 442964123) B442964123
theorem B196872943 : Blo 2129435 196872943 := bstep (se 1 (by rfl) ⟨147654707, by rfl⟩ : syracuseStep 196872943 = 295309415) B295309415
theorem B262497257 : Blo 2129435 262497257 := bstep (se 2 (by rfl) ⟨98436471, by rfl⟩ : syracuseStep 262497257 = 196872943) B196872943
theorem B174998171 : Blo 2129435 174998171 := bstep (se 1 (by rfl) ⟨131248628, by rfl⟩ : syracuseStep 174998171 = 262497257) B262497257
theorem B116665447 : Blo 2129435 116665447 := bstep (se 1 (by rfl) ⟨87499085, by rfl⟩ : syracuseStep 116665447 = 174998171) B174998171
theorem B155553929 : Blo 2129435 155553929 := bstep (se 2 (by rfl) ⟨58332723, by rfl⟩ : syracuseStep 155553929 = 116665447) B116665447
theorem B103702619 : Blo 2129435 103702619 := bstep (se 1 (by rfl) ⟨77776964, by rfl⟩ : syracuseStep 103702619 = 155553929) B155553929
theorem B69135079 : Blo 2129435 69135079 := bstep (se 1 (by rfl) ⟨51851309, by rfl⟩ : syracuseStep 69135079 = 103702619) B103702619
theorem B92180105 : Blo 2129435 92180105 := bstep (se 2 (by rfl) ⟨34567539, by rfl⟩ : syracuseStep 92180105 = 69135079) B69135079
theorem B61453403 : Blo 2129435 61453403 := bstep (se 1 (by rfl) ⟨46090052, by rfl⟩ : syracuseStep 61453403 = 92180105) B92180105
theorem B40968935 : Blo 2129435 40968935 := bstep (se 1 (by rfl) ⟨30726701, by rfl⟩ : syracuseStep 40968935 = 61453403) B61453403
theorem B27312623 : Blo 2129435 27312623 := bstep (se 1 (by rfl) ⟨20484467, by rfl⟩ : syracuseStep 27312623 = 40968935) B40968935
theorem B18208415 : Blo 2129435 18208415 := bstep (se 1 (by rfl) ⟨13656311, by rfl⟩ : syracuseStep 18208415 = 27312623) B27312623
theorem B12138943 : Blo 2129435 12138943 := bstep (se 1 (by rfl) ⟨9104207, by rfl⟩ : syracuseStep 12138943 = 18208415) B18208415
theorem B16185257 : Blo 2129435 16185257 := bstep (se 2 (by rfl) ⟨6069471, by rfl⟩ : syracuseStep 16185257 = 12138943) B12138943
theorem B10790171 : Blo 2129435 10790171 := bstep (se 1 (by rfl) ⟨8092628, by rfl⟩ : syracuseStep 10790171 = 16185257) B16185257
theorem B7193447 : Blo 2129435 7193447 := bstep (se 1 (by rfl) ⟨5395085, by rfl⟩ : syracuseStep 7193447 = 10790171) B10790171
theorem B4795631 : Blo 2129435 4795631 := bstep (se 1 (by rfl) ⟨3596723, by rfl⟩ : syracuseStep 4795631 = 7193447) B7193447
theorem B3197087 : Blo 2129435 3197087 := bstep (se 1 (by rfl) ⟨2397815, by rfl⟩ : syracuseStep 3197087 = 4795631) B4795631
theorem B2131391 : Blo 2129435 2131391 := bstep (se 1 (by rfl) ⟨1598543, by rfl⟩ : syracuseStep 2131391 = 3197087) B3197087
theorem B3197093 : Blo 2129435 3197093 := bbase (se 4 (by rfl) ⟨299727, by rfl⟩ : syracuseStep 3197093 = 599455) (by norm_num)
theorem B2131395 : Blo 2129435 2131395 := bstep (se 1 (by rfl) ⟨1598546, by rfl⟩ : syracuseStep 2131395 = 3197093) B3197093
theorem B2697553 : Blo 2129435 2697553 := bbase (se 2 (by rfl) ⟨1011582, by rfl⟩ : syracuseStep 2697553 = 2023165) (by norm_num)
theorem B3596737 : Blo 2129435 3596737 := bstep (se 2 (by rfl) ⟨1348776, by rfl⟩ : syracuseStep 3596737 = 2697553) B2697553
theorem B4795649 : Blo 2129435 4795649 := bstep (se 2 (by rfl) ⟨1798368, by rfl⟩ : syracuseStep 4795649 = 3596737) B3596737
theorem B3197099 : Blo 2129435 3197099 := bstep (se 1 (by rfl) ⟨2397824, by rfl⟩ : syracuseStep 3197099 = 4795649) B4795649
theorem B2131399 : Blo 2129435 2131399 := bstep (se 1 (by rfl) ⟨1598549, by rfl⟩ : syracuseStep 2131399 = 3197099) B3197099
theorem B2397829 : Blo 2129435 2397829 := bbase (se 4 (by rfl) ⟨224796, by rfl⟩ : syracuseStep 2397829 = 449593) (by norm_num)
theorem B3197105 : Blo 2129435 3197105 := bstep (se 2 (by rfl) ⟨1198914, by rfl⟩ : syracuseStep 3197105 = 2397829) B2397829
theorem B2131403 : Blo 2129435 2131403 := bstep (se 1 (by rfl) ⟨1598552, by rfl⟩ : syracuseStep 2131403 = 3197105) B3197105
theorem B5121157 : Blo 2129435 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B6828209 : Blo 2129435 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B4552139 : Blo 2129435 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B3034759 : Blo 2129435 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B4046345 : Blo 2129435 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B2697563 : Blo 2129435 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B7193501 : Blo 2129435 7193501 := bstep (se 3 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 7193501 = 2697563) B2697563
theorem B4795667 : Blo 2129435 4795667 := bstep (se 1 (by rfl) ⟨3596750, by rfl⟩ : syracuseStep 4795667 = 7193501) B7193501
theorem B3197111 : Blo 2129435 3197111 := bstep (se 1 (by rfl) ⟨2397833, by rfl⟩ : syracuseStep 3197111 = 4795667) B4795667
theorem B2131407 : Blo 2129435 2131407 := bstep (se 1 (by rfl) ⟨1598555, by rfl⟩ : syracuseStep 2131407 = 3197111) B3197111
theorem B3197117 : Blo 2129435 3197117 := bbase (se 3 (by rfl) ⟨599459, by rfl⟩ : syracuseStep 3197117 = 1198919) (by norm_num)
theorem B2131411 : Blo 2129435 2131411 := bstep (se 1 (by rfl) ⟨1598558, by rfl⟩ : syracuseStep 2131411 = 3197117) B3197117
theorem B4795685 : Blo 2129435 4795685 := bbase (se 4 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 4795685 = 899191) (by norm_num)
theorem B3197123 : Blo 2129435 3197123 := bstep (se 1 (by rfl) ⟨2397842, by rfl⟩ : syracuseStep 3197123 = 4795685) B4795685
theorem B2131415 : Blo 2129435 2131415 := bstep (se 1 (by rfl) ⟨1598561, by rfl⟩ : syracuseStep 2131415 = 3197123) B3197123
theorem B5395157 : Blo 2129435 5395157 := bbase (se 7 (by rfl) ⟨63224, by rfl⟩ : syracuseStep 5395157 = 126449) (by norm_num)
theorem B3596771 : Blo 2129435 3596771 := bstep (se 1 (by rfl) ⟨2697578, by rfl⟩ : syracuseStep 3596771 = 5395157) B5395157
theorem B2397847 : Blo 2129435 2397847 := bstep (se 1 (by rfl) ⟨1798385, by rfl⟩ : syracuseStep 2397847 = 3596771) B3596771
theorem B3197129 : Blo 2129435 3197129 := bstep (se 2 (by rfl) ⟨1198923, by rfl⟩ : syracuseStep 3197129 = 2397847) B2397847
theorem B2131419 : Blo 2129435 2131419 := bstep (se 1 (by rfl) ⟨1598564, by rfl⟩ : syracuseStep 2131419 = 3197129) B3197129
theorem B10242389 : Blo 2129435 10242389 := bbase (se 10 (by rfl) ⟨15003, by rfl⟩ : syracuseStep 10242389 = 30007) (by norm_num)
theorem B6828259 : Blo 2129435 6828259 := bstep (se 1 (by rfl) ⟨5121194, by rfl⟩ : syracuseStep 6828259 = 10242389) B10242389
theorem B9104345 : Blo 2129435 9104345 := bstep (se 2 (by rfl) ⟨3414129, by rfl⟩ : syracuseStep 9104345 = 6828259) B6828259
theorem B6069563 : Blo 2129435 6069563 := bstep (se 1 (by rfl) ⟨4552172, by rfl⟩ : syracuseStep 6069563 = 9104345) B9104345
theorem B4046375 : Blo 2129435 4046375 := bstep (se 1 (by rfl) ⟨3034781, by rfl⟩ : syracuseStep 4046375 = 6069563) B6069563
theorem B10790333 : Blo 2129435 10790333 := bstep (se 3 (by rfl) ⟨2023187, by rfl⟩ : syracuseStep 10790333 = 4046375) B4046375
theorem B7193555 : Blo 2129435 7193555 := bstep (se 1 (by rfl) ⟨5395166, by rfl⟩ : syracuseStep 7193555 = 10790333) B10790333
theorem B4795703 : Blo 2129435 4795703 := bstep (se 1 (by rfl) ⟨3596777, by rfl⟩ : syracuseStep 4795703 = 7193555) B7193555
theorem B3197135 : Blo 2129435 3197135 := bstep (se 1 (by rfl) ⟨2397851, by rfl⟩ : syracuseStep 3197135 = 4795703) B4795703
theorem B2131423 : Blo 2129435 2131423 := bstep (se 1 (by rfl) ⟨1598567, by rfl⟩ : syracuseStep 2131423 = 3197135) B3197135
theorem B3197141 : Blo 2129435 3197141 := bbase (se 7 (by rfl) ⟨37466, by rfl⟩ : syracuseStep 3197141 = 74933) (by norm_num)
theorem B2131427 : Blo 2129435 2131427 := bstep (se 1 (by rfl) ⟨1598570, by rfl⟩ : syracuseStep 2131427 = 3197141) B3197141
theorem B3555805 : Blo 2129435 3555805 := bbase (se 3 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 3555805 = 1333427) (by norm_num)
theorem B4741073 : Blo 2129435 4741073 := bstep (se 2 (by rfl) ⟨1777902, by rfl⟩ : syracuseStep 4741073 = 3555805) B3555805
theorem B3160715 : Blo 2129435 3160715 := bstep (se 1 (by rfl) ⟨2370536, by rfl⟩ : syracuseStep 3160715 = 4741073) B4741073
theorem B8428573 : Blo 2129435 8428573 := bstep (se 3 (by rfl) ⟨1580357, by rfl⟩ : syracuseStep 8428573 = 3160715) B3160715
theorem B11238097 : Blo 2129435 11238097 := bstep (se 2 (by rfl) ⟨4214286, by rfl⟩ : syracuseStep 11238097 = 8428573) B8428573
theorem B14984129 : Blo 2129435 14984129 := bstep (se 2 (by rfl) ⟨5619048, by rfl⟩ : syracuseStep 14984129 = 11238097) B11238097
theorem B9989419 : Blo 2129435 9989419 := bstep (se 1 (by rfl) ⟨7492064, by rfl⟩ : syracuseStep 9989419 = 14984129) B14984129
theorem B13319225 : Blo 2129435 13319225 := bstep (se 2 (by rfl) ⟨4994709, by rfl⟩ : syracuseStep 13319225 = 9989419) B9989419
theorem B8879483 : Blo 2129435 8879483 := bstep (se 1 (by rfl) ⟨6659612, by rfl⟩ : syracuseStep 8879483 = 13319225) B13319225
theorem B5919655 : Blo 2129435 5919655 := bstep (se 1 (by rfl) ⟨4439741, by rfl⟩ : syracuseStep 5919655 = 8879483) B8879483
theorem B7892873 : Blo 2129435 7892873 := bstep (se 2 (by rfl) ⟨2959827, by rfl⟩ : syracuseStep 7892873 = 5919655) B5919655
theorem B5261915 : Blo 2129435 5261915 := bstep (se 1 (by rfl) ⟨3946436, by rfl⟩ : syracuseStep 5261915 = 7892873) B7892873
theorem B3507943 : Blo 2129435 3507943 := bstep (se 1 (by rfl) ⟨2630957, by rfl⟩ : syracuseStep 3507943 = 5261915) B5261915
theorem B4677257 : Blo 2129435 4677257 := bstep (se 2 (by rfl) ⟨1753971, by rfl⟩ : syracuseStep 4677257 = 3507943) B3507943
theorem B3118171 : Blo 2129435 3118171 := bstep (se 1 (by rfl) ⟨2338628, by rfl⟩ : syracuseStep 3118171 = 4677257) B4677257
theorem B4157561 : Blo 2129435 4157561 := bstep (se 2 (by rfl) ⟨1559085, by rfl⟩ : syracuseStep 4157561 = 3118171) B3118171
theorem B2771707 : Blo 2129435 2771707 := bstep (se 1 (by rfl) ⟨2078780, by rfl⟩ : syracuseStep 2771707 = 4157561) B4157561
theorem B3695609 : Blo 2129435 3695609 := bstep (se 2 (by rfl) ⟨1385853, by rfl⟩ : syracuseStep 3695609 = 2771707) B2771707
theorem B2463739 : Blo 2129435 2463739 := bstep (se 1 (by rfl) ⟨1847804, by rfl⟩ : syracuseStep 2463739 = 3695609) B3695609
theorem B13139941 : Blo 2129435 13139941 := bstep (se 4 (by rfl) ⟨1231869, by rfl⟩ : syracuseStep 13139941 = 2463739) B2463739
theorem B17519921 : Blo 2129435 17519921 := bstep (se 2 (by rfl) ⟨6569970, by rfl⟩ : syracuseStep 17519921 = 13139941) B13139941
theorem B11679947 : Blo 2129435 11679947 := bstep (se 1 (by rfl) ⟨8759960, by rfl⟩ : syracuseStep 11679947 = 17519921) B17519921
theorem B7786631 : Blo 2129435 7786631 := bstep (se 1 (by rfl) ⟨5839973, by rfl⟩ : syracuseStep 7786631 = 11679947) B11679947
theorem B20764349 : Blo 2129435 20764349 := bstep (se 3 (by rfl) ⟨3893315, by rfl⟩ : syracuseStep 20764349 = 7786631) B7786631
theorem B13842899 : Blo 2129435 13842899 := bstep (se 1 (by rfl) ⟨10382174, by rfl⟩ : syracuseStep 13842899 = 20764349) B20764349
theorem B9228599 : Blo 2129435 9228599 := bstep (se 1 (by rfl) ⟨6921449, by rfl⟩ : syracuseStep 9228599 = 13842899) B13842899
theorem B6152399 : Blo 2129435 6152399 := bstep (se 1 (by rfl) ⟨4614299, by rfl⟩ : syracuseStep 6152399 = 9228599) B9228599
theorem B4101599 : Blo 2129435 4101599 := bstep (se 1 (by rfl) ⟨3076199, by rfl⟩ : syracuseStep 4101599 = 6152399) B6152399
theorem B10937597 : Blo 2129435 10937597 := bstep (se 3 (by rfl) ⟨2050799, by rfl⟩ : syracuseStep 10937597 = 4101599) B4101599
theorem B29166925 : Blo 2129435 29166925 := bstep (se 3 (by rfl) ⟨5468798, by rfl⟩ : syracuseStep 29166925 = 10937597) B10937597
theorem B38889233 : Blo 2129435 38889233 := bstep (se 2 (by rfl) ⟨14583462, by rfl⟩ : syracuseStep 38889233 = 29166925) B29166925
theorem B25926155 : Blo 2129435 25926155 := bstep (se 1 (by rfl) ⟨19444616, by rfl⟩ : syracuseStep 25926155 = 38889233) B38889233
theorem B17284103 : Blo 2129435 17284103 := bstep (se 1 (by rfl) ⟨12963077, by rfl⟩ : syracuseStep 17284103 = 25926155) B25926155
theorem B11522735 : Blo 2129435 11522735 := bstep (se 1 (by rfl) ⟨8642051, by rfl⟩ : syracuseStep 11522735 = 17284103) B17284103
theorem B7681823 : Blo 2129435 7681823 := bstep (se 1 (by rfl) ⟨5761367, by rfl⟩ : syracuseStep 7681823 = 11522735) B11522735
theorem B5121215 : Blo 2129435 5121215 := bstep (se 1 (by rfl) ⟨3840911, by rfl⟩ : syracuseStep 5121215 = 7681823) B7681823
theorem B3414143 : Blo 2129435 3414143 := bstep (se 1 (by rfl) ⟨2560607, by rfl⟩ : syracuseStep 3414143 = 5121215) B5121215
theorem B2276095 : Blo 2129435 2276095 := bstep (se 1 (by rfl) ⟨1707071, by rfl⟩ : syracuseStep 2276095 = 3414143) B3414143
theorem B3034793 : Blo 2129435 3034793 := bstep (se 2 (by rfl) ⟨1138047, by rfl⟩ : syracuseStep 3034793 = 2276095) B2276095
theorem B8092781 : Blo 2129435 8092781 := bstep (se 3 (by rfl) ⟨1517396, by rfl⟩ : syracuseStep 8092781 = 3034793) B3034793
theorem B5395187 : Blo 2129435 5395187 := bstep (se 1 (by rfl) ⟨4046390, by rfl⟩ : syracuseStep 5395187 = 8092781) B8092781
theorem B3596791 : Blo 2129435 3596791 := bstep (se 1 (by rfl) ⟨2697593, by rfl⟩ : syracuseStep 3596791 = 5395187) B5395187
theorem B4795721 : Blo 2129435 4795721 := bstep (se 2 (by rfl) ⟨1798395, by rfl⟩ : syracuseStep 4795721 = 3596791) B3596791
theorem B3197147 : Blo 2129435 3197147 := bstep (se 1 (by rfl) ⟨2397860, by rfl⟩ : syracuseStep 3197147 = 4795721) B4795721
theorem B2131431 : Blo 2129435 2131431 := bstep (se 1 (by rfl) ⟨1598573, by rfl⟩ : syracuseStep 2131431 = 3197147) B3197147
theorem B2397865 : Blo 2129435 2397865 := bbase (se 2 (by rfl) ⟨899199, by rfl⟩ : syracuseStep 2397865 = 1798399) (by norm_num)
theorem B3197153 : Blo 2129435 3197153 := bstep (se 2 (by rfl) ⟨1198932, by rfl⟩ : syracuseStep 3197153 = 2397865) B2397865
theorem B2131435 : Blo 2129435 2131435 := bstep (se 1 (by rfl) ⟨1598576, by rfl⟩ : syracuseStep 2131435 = 3197153) B3197153
theorem C0 (j : ℕ) (h1 : 532358 ≤ j) (h2 : j ≤ 532858) : Blo 2129435 (4 * j + 3) := by
  interval_cases j
  · exact B2129435
  · exact B2129439
  · exact B2129443
  · exact B2129447
  · exact B2129451
  · exact B2129455
  · exact B2129459
  · exact B2129463
  · exact B2129467
  · exact B2129471
  · exact B2129475
  · exact B2129479
  · exact B2129483
  · exact B2129487
  · exact B2129491
  · exact B2129495
  · exact B2129499
  · exact B2129503
  · exact B2129507
  · exact B2129511
  · exact B2129515
  · exact B2129519
  · exact B2129523
  · exact B2129527
  · exact B2129531
  · exact B2129535
  · exact B2129539
  · exact B2129543
  · exact B2129547
  · exact B2129551
  · exact B2129555
  · exact B2129559
  · exact B2129563
  · exact B2129567
  · exact B2129571
  · exact B2129575
  · exact B2129579
  · exact B2129583
  · exact B2129587
  · exact B2129591
  · exact B2129595
  · exact B2129599
  · exact B2129603
  · exact B2129607
  · exact B2129611
  · exact B2129615
  · exact B2129619
  · exact B2129623
  · exact B2129627
  · exact B2129631
  · exact B2129635
  · exact B2129639
  · exact B2129643
  · exact B2129647
  · exact B2129651
  · exact B2129655
  · exact B2129659
  · exact B2129663
  · exact B2129667
  · exact B2129671
  · exact B2129675
  · exact B2129679
  · exact B2129683
  · exact B2129687
  · exact B2129691
  · exact B2129695
  · exact B2129699
  · exact B2129703
  · exact B2129707
  · exact B2129711
  · exact B2129715
  · exact B2129719
  · exact B2129723
  · exact B2129727
  · exact B2129731
  · exact B2129735
  · exact B2129739
  · exact B2129743
  · exact B2129747
  · exact B2129751
  · exact B2129755
  · exact B2129759
  · exact B2129763
  · exact B2129767
  · exact B2129771
  · exact B2129775
  · exact B2129779
  · exact B2129783
  · exact B2129787
  · exact B2129791
  · exact B2129795
  · exact B2129799
  · exact B2129803
  · exact B2129807
  · exact B2129811
  · exact B2129815
  · exact B2129819
  · exact B2129823
  · exact B2129827
  · exact B2129831
  · exact B2129835
  · exact B2129839
  · exact B2129843
  · exact B2129847
  · exact B2129851
  · exact B2129855
  · exact B2129859
  · exact B2129863
  · exact B2129867
  · exact B2129871
  · exact B2129875
  · exact B2129879
  · exact B2129883
  · exact B2129887
  · exact B2129891
  · exact B2129895
  · exact B2129899
  · exact B2129903
  · exact B2129907
  · exact B2129911
  · exact B2129915
  · exact B2129919
  · exact B2129923
  · exact B2129927
  · exact B2129931
  · exact B2129935
  · exact B2129939
  · exact B2129943
  · exact B2129947
  · exact B2129951
  · exact B2129955
  · exact B2129959
  · exact B2129963
  · exact B2129967
  · exact B2129971
  · exact B2129975
  · exact B2129979
  · exact B2129983
  · exact B2129987
  · exact B2129991
  · exact B2129995
  · exact B2129999
  · exact B2130003
  · exact B2130007
  · exact B2130011
  · exact B2130015
  · exact B2130019
  · exact B2130023
  · exact B2130027
  · exact B2130031
  · exact B2130035
  · exact B2130039
  · exact B2130043
  · exact B2130047
  · exact B2130051
  · exact B2130055
  · exact B2130059
  · exact B2130063
  · exact B2130067
  · exact B2130071
  · exact B2130075
  · exact B2130079
  · exact B2130083
  · exact B2130087
  · exact B2130091
  · exact B2130095
  · exact B2130099
  · exact B2130103
  · exact B2130107
  · exact B2130111
  · exact B2130115
  · exact B2130119
  · exact B2130123
  · exact B2130127
  · exact B2130131
  · exact B2130135
  · exact B2130139
  · exact B2130143
  · exact B2130147
  · exact B2130151
  · exact B2130155
  · exact B2130159
  · exact B2130163
  · exact B2130167
  · exact B2130171
  · exact B2130175
  · exact B2130179
  · exact B2130183
  · exact B2130187
  · exact B2130191
  · exact B2130195
  · exact B2130199
  · exact B2130203
  · exact B2130207
  · exact B2130211
  · exact B2130215
  · exact B2130219
  · exact B2130223
  · exact B2130227
  · exact B2130231
  · exact B2130235
  · exact B2130239
  · exact B2130243
  · exact B2130247
  · exact B2130251
  · exact B2130255
  · exact B2130259
  · exact B2130263
  · exact B2130267
  · exact B2130271
  · exact B2130275
  · exact B2130279
  · exact B2130283
  · exact B2130287
  · exact B2130291
  · exact B2130295
  · exact B2130299
  · exact B2130303
  · exact B2130307
  · exact B2130311
  · exact B2130315
  · exact B2130319
  · exact B2130323
  · exact B2130327
  · exact B2130331
  · exact B2130335
  · exact B2130339
  · exact B2130343
  · exact B2130347
  · exact B2130351
  · exact B2130355
  · exact B2130359
  · exact B2130363
  · exact B2130367
  · exact B2130371
  · exact B2130375
  · exact B2130379
  · exact B2130383
  · exact B2130387
  · exact B2130391
  · exact B2130395
  · exact B2130399
  · exact B2130403
  · exact B2130407
  · exact B2130411
  · exact B2130415
  · exact B2130419
  · exact B2130423
  · exact B2130427
  · exact B2130431
  · exact B2130435
  · exact B2130439
  · exact B2130443
  · exact B2130447
  · exact B2130451
  · exact B2130455
  · exact B2130459
  · exact B2130463
  · exact B2130467
  · exact B2130471
  · exact B2130475
  · exact B2130479
  · exact B2130483
  · exact B2130487
  · exact B2130491
  · exact B2130495
  · exact B2130499
  · exact B2130503
  · exact B2130507
  · exact B2130511
  · exact B2130515
  · exact B2130519
  · exact B2130523
  · exact B2130527
  · exact B2130531
  · exact B2130535
  · exact B2130539
  · exact B2130543
  · exact B2130547
  · exact B2130551
  · exact B2130555
  · exact B2130559
  · exact B2130563
  · exact B2130567
  · exact B2130571
  · exact B2130575
  · exact B2130579
  · exact B2130583
  · exact B2130587
  · exact B2130591
  · exact B2130595
  · exact B2130599
  · exact B2130603
  · exact B2130607
  · exact B2130611
  · exact B2130615
  · exact B2130619
  · exact B2130623
  · exact B2130627
  · exact B2130631
  · exact B2130635
  · exact B2130639
  · exact B2130643
  · exact B2130647
  · exact B2130651
  · exact B2130655
  · exact B2130659
  · exact B2130663
  · exact B2130667
  · exact B2130671
  · exact B2130675
  · exact B2130679
  · exact B2130683
  · exact B2130687
  · exact B2130691
  · exact B2130695
  · exact B2130699
  · exact B2130703
  · exact B2130707
  · exact B2130711
  · exact B2130715
  · exact B2130719
  · exact B2130723
  · exact B2130727
  · exact B2130731
  · exact B2130735
  · exact B2130739
  · exact B2130743
  · exact B2130747
  · exact B2130751
  · exact B2130755
  · exact B2130759
  · exact B2130763
  · exact B2130767
  · exact B2130771
  · exact B2130775
  · exact B2130779
  · exact B2130783
  · exact B2130787
  · exact B2130791
  · exact B2130795
  · exact B2130799
  · exact B2130803
  · exact B2130807
  · exact B2130811
  · exact B2130815
  · exact B2130819
  · exact B2130823
  · exact B2130827
  · exact B2130831
  · exact B2130835
  · exact B2130839
  · exact B2130843
  · exact B2130847
  · exact B2130851
  · exact B2130855
  · exact B2130859
  · exact B2130863
  · exact B2130867
  · exact B2130871
  · exact B2130875
  · exact B2130879
  · exact B2130883
  · exact B2130887
  · exact B2130891
  · exact B2130895
  · exact B2130899
  · exact B2130903
  · exact B2130907
  · exact B2130911
  · exact B2130915
  · exact B2130919
  · exact B2130923
  · exact B2130927
  · exact B2130931
  · exact B2130935
  · exact B2130939
  · exact B2130943
  · exact B2130947
  · exact B2130951
  · exact B2130955
  · exact B2130959
  · exact B2130963
  · exact B2130967
  · exact B2130971
  · exact B2130975
  · exact B2130979
  · exact B2130983
  · exact B2130987
  · exact B2130991
  · exact B2130995
  · exact B2130999
  · exact B2131003
  · exact B2131007
  · exact B2131011
  · exact B2131015
  · exact B2131019
  · exact B2131023
  · exact B2131027
  · exact B2131031
  · exact B2131035
  · exact B2131039
  · exact B2131043
  · exact B2131047
  · exact B2131051
  · exact B2131055
  · exact B2131059
  · exact B2131063
  · exact B2131067
  · exact B2131071
  · exact B2131075
  · exact B2131079
  · exact B2131083
  · exact B2131087
  · exact B2131091
  · exact B2131095
  · exact B2131099
  · exact B2131103
  · exact B2131107
  · exact B2131111
  · exact B2131115
  · exact B2131119
  · exact B2131123
  · exact B2131127
  · exact B2131131
  · exact B2131135
  · exact B2131139
  · exact B2131143
  · exact B2131147
  · exact B2131151
  · exact B2131155
  · exact B2131159
  · exact B2131163
  · exact B2131167
  · exact B2131171
  · exact B2131175
  · exact B2131179
  · exact B2131183
  · exact B2131187
  · exact B2131191
  · exact B2131195
  · exact B2131199
  · exact B2131203
  · exact B2131207
  · exact B2131211
  · exact B2131215
  · exact B2131219
  · exact B2131223
  · exact B2131227
  · exact B2131231
  · exact B2131235
  · exact B2131239
  · exact B2131243
  · exact B2131247
  · exact B2131251
  · exact B2131255
  · exact B2131259
  · exact B2131263
  · exact B2131267
  · exact B2131271
  · exact B2131275
  · exact B2131279
  · exact B2131283
  · exact B2131287
  · exact B2131291
  · exact B2131295
  · exact B2131299
  · exact B2131303
  · exact B2131307
  · exact B2131311
  · exact B2131315
  · exact B2131319
  · exact B2131323
  · exact B2131327
  · exact B2131331
  · exact B2131335
  · exact B2131339
  · exact B2131343
  · exact B2131347
  · exact B2131351
  · exact B2131355
  · exact B2131359
  · exact B2131363
  · exact B2131367
  · exact B2131371
  · exact B2131375
  · exact B2131379
  · exact B2131383
  · exact B2131387
  · exact B2131391
  · exact B2131395
  · exact B2131399
  · exact B2131403
  · exact B2131407
  · exact B2131411
  · exact B2131415
  · exact B2131419
  · exact B2131423
  · exact B2131427
  · exact B2131431
  · exact B2131435
theorem solution (m : ℕ) (hlo : 2129435 ≤ m) (hhi : m ≤ 2131435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 532358 ≤ j := by omega
    have hj2 : j ≤ 532858 := by omega
    have hb : Blo 2129435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
