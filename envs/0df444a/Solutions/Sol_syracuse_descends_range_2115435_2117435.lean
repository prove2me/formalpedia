-- Prove2me | solution 1 for syracuse_descends_range_2115435_2117435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:52.283557+00:00
-- url     : https://prove2.me/submissions/76feba5c-109a-4680-8b00-f7749e4cf297

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

theorem B2379865 : Blo 2115435 2379865 := bbase (se 2 (by rfl) ⟨892449, by rfl⟩ : syracuseStep 2379865 = 1784899) (by norm_num)
theorem B3173153 : Blo 2115435 3173153 := bstep (se 2 (by rfl) ⟨1189932, by rfl⟩ : syracuseStep 3173153 = 2379865) B2379865
theorem B2115435 : Blo 2115435 2115435 := bstep (se 1 (by rfl) ⟨1586576, by rfl⟩ : syracuseStep 2115435 = 3173153) B3173153
theorem B3812093 : Blo 2115435 3812093 := bbase (se 3 (by rfl) ⟨714767, by rfl⟩ : syracuseStep 3812093 = 1429535) (by norm_num)
theorem B2541395 : Blo 2115435 2541395 := bstep (se 1 (by rfl) ⟨1906046, by rfl⟩ : syracuseStep 2541395 = 3812093) B3812093
theorem B6777053 : Blo 2115435 6777053 := bstep (se 3 (by rfl) ⟨1270697, by rfl⟩ : syracuseStep 6777053 = 2541395) B2541395
theorem B4518035 : Blo 2115435 4518035 := bstep (se 1 (by rfl) ⟨3388526, by rfl⟩ : syracuseStep 4518035 = 6777053) B6777053
theorem B3012023 : Blo 2115435 3012023 := bstep (se 1 (by rfl) ⟨2259017, by rfl⟩ : syracuseStep 3012023 = 4518035) B4518035
theorem B8032061 : Blo 2115435 8032061 := bstep (se 3 (by rfl) ⟨1506011, by rfl⟩ : syracuseStep 8032061 = 3012023) B3012023
theorem B5354707 : Blo 2115435 5354707 := bstep (se 1 (by rfl) ⟨4016030, by rfl⟩ : syracuseStep 5354707 = 8032061) B8032061
theorem B7139609 : Blo 2115435 7139609 := bstep (se 2 (by rfl) ⟨2677353, by rfl⟩ : syracuseStep 7139609 = 5354707) B5354707
theorem B4759739 : Blo 2115435 4759739 := bstep (se 1 (by rfl) ⟨3569804, by rfl⟩ : syracuseStep 4759739 = 7139609) B7139609
theorem B3173159 : Blo 2115435 3173159 := bstep (se 1 (by rfl) ⟨2379869, by rfl⟩ : syracuseStep 3173159 = 4759739) B4759739
theorem B2115439 : Blo 2115435 2115439 := bstep (se 1 (by rfl) ⟨1586579, by rfl⟩ : syracuseStep 2115439 = 3173159) B3173159
theorem B3173165 : Blo 2115435 3173165 := bbase (se 3 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 3173165 = 1189937) (by norm_num)
theorem B2115443 : Blo 2115435 2115443 := bstep (se 1 (by rfl) ⟨1586582, by rfl⟩ : syracuseStep 2115443 = 3173165) B3173165
theorem B4759757 : Blo 2115435 4759757 := bbase (se 3 (by rfl) ⟨892454, by rfl⟩ : syracuseStep 4759757 = 1784909) (by norm_num)
theorem B3173171 : Blo 2115435 3173171 := bstep (se 1 (by rfl) ⟨2379878, by rfl⟩ : syracuseStep 3173171 = 4759757) B4759757
theorem B2115447 : Blo 2115435 2115447 := bstep (se 1 (by rfl) ⟨1586585, by rfl⟩ : syracuseStep 2115447 = 3173171) B3173171
theorem B2677369 : Blo 2115435 2677369 := bbase (se 2 (by rfl) ⟨1004013, by rfl⟩ : syracuseStep 2677369 = 2008027) (by norm_num)
theorem B3569825 : Blo 2115435 3569825 := bstep (se 2 (by rfl) ⟨1338684, by rfl⟩ : syracuseStep 3569825 = 2677369) B2677369
theorem B2379883 : Blo 2115435 2379883 := bstep (se 1 (by rfl) ⟨1784912, by rfl⟩ : syracuseStep 2379883 = 3569825) B3569825
theorem B3173177 : Blo 2115435 3173177 := bstep (se 2 (by rfl) ⟨1189941, by rfl⟩ : syracuseStep 3173177 = 2379883) B2379883
theorem B2115451 : Blo 2115435 2115451 := bstep (se 1 (by rfl) ⟨1586588, by rfl⟩ : syracuseStep 2115451 = 3173177) B3173177
theorem B22872725 : Blo 2115435 22872725 := bbase (se 6 (by rfl) ⟨536079, by rfl⟩ : syracuseStep 22872725 = 1072159) (by norm_num)
theorem B15248483 : Blo 2115435 15248483 := bstep (se 1 (by rfl) ⟨11436362, by rfl⟩ : syracuseStep 15248483 = 22872725) B22872725
theorem B10165655 : Blo 2115435 10165655 := bstep (se 1 (by rfl) ⟨7624241, by rfl⟩ : syracuseStep 10165655 = 15248483) B15248483
theorem B6777103 : Blo 2115435 6777103 := bstep (se 1 (by rfl) ⟨5082827, by rfl⟩ : syracuseStep 6777103 = 10165655) B10165655
theorem B9036137 : Blo 2115435 9036137 := bstep (se 2 (by rfl) ⟨3388551, by rfl⟩ : syracuseStep 9036137 = 6777103) B6777103
theorem B24096365 : Blo 2115435 24096365 := bstep (se 3 (by rfl) ⟨4518068, by rfl⟩ : syracuseStep 24096365 = 9036137) B9036137
theorem B16064243 : Blo 2115435 16064243 := bstep (se 1 (by rfl) ⟨12048182, by rfl⟩ : syracuseStep 16064243 = 24096365) B24096365
theorem B10709495 : Blo 2115435 10709495 := bstep (se 1 (by rfl) ⟨8032121, by rfl⟩ : syracuseStep 10709495 = 16064243) B16064243
theorem B7139663 : Blo 2115435 7139663 := bstep (se 1 (by rfl) ⟨5354747, by rfl⟩ : syracuseStep 7139663 = 10709495) B10709495
theorem B4759775 : Blo 2115435 4759775 := bstep (se 1 (by rfl) ⟨3569831, by rfl⟩ : syracuseStep 4759775 = 7139663) B7139663
theorem B3173183 : Blo 2115435 3173183 := bstep (se 1 (by rfl) ⟨2379887, by rfl⟩ : syracuseStep 3173183 = 4759775) B4759775
theorem B2115455 : Blo 2115435 2115455 := bstep (se 1 (by rfl) ⟨1586591, by rfl⟩ : syracuseStep 2115455 = 3173183) B3173183
theorem B3173189 : Blo 2115435 3173189 := bbase (se 4 (by rfl) ⟨297486, by rfl⟩ : syracuseStep 3173189 = 594973) (by norm_num)
theorem B2115459 : Blo 2115435 2115459 := bstep (se 1 (by rfl) ⟨1586594, by rfl⟩ : syracuseStep 2115459 = 3173189) B3173189
theorem B3569845 : Blo 2115435 3569845 := bbase (se 5 (by rfl) ⟨167336, by rfl⟩ : syracuseStep 3569845 = 334673) (by norm_num)
theorem B4759793 : Blo 2115435 4759793 := bstep (se 2 (by rfl) ⟨1784922, by rfl⟩ : syracuseStep 4759793 = 3569845) B3569845
theorem B3173195 : Blo 2115435 3173195 := bstep (se 1 (by rfl) ⟨2379896, by rfl⟩ : syracuseStep 3173195 = 4759793) B4759793
theorem B2115463 : Blo 2115435 2115463 := bstep (se 1 (by rfl) ⟨1586597, by rfl⟩ : syracuseStep 2115463 = 3173195) B3173195
theorem B2379901 : Blo 2115435 2379901 := bbase (se 3 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 2379901 = 892463) (by norm_num)
theorem B3173201 : Blo 2115435 3173201 := bstep (se 2 (by rfl) ⟨1189950, by rfl⟩ : syracuseStep 3173201 = 2379901) B2379901
theorem B2115467 : Blo 2115435 2115467 := bstep (se 1 (by rfl) ⟨1586600, by rfl⟩ : syracuseStep 2115467 = 3173201) B3173201
theorem B7139717 : Blo 2115435 7139717 := bbase (se 4 (by rfl) ⟨669348, by rfl⟩ : syracuseStep 7139717 = 1338697) (by norm_num)
theorem B4759811 : Blo 2115435 4759811 := bstep (se 1 (by rfl) ⟨3569858, by rfl⟩ : syracuseStep 4759811 = 7139717) B7139717
theorem B3173207 : Blo 2115435 3173207 := bstep (se 1 (by rfl) ⟨2379905, by rfl⟩ : syracuseStep 3173207 = 4759811) B4759811
theorem B2115471 : Blo 2115435 2115471 := bstep (se 1 (by rfl) ⟨1586603, by rfl⟩ : syracuseStep 2115471 = 3173207) B3173207
theorem B3173213 : Blo 2115435 3173213 := bbase (se 3 (by rfl) ⟨594977, by rfl⟩ : syracuseStep 3173213 = 1189955) (by norm_num)
theorem B2115475 : Blo 2115435 2115475 := bstep (se 1 (by rfl) ⟨1586606, by rfl⟩ : syracuseStep 2115475 = 3173213) B3173213
theorem B4759829 : Blo 2115435 4759829 := bbase (se 6 (by rfl) ⟨111558, by rfl⟩ : syracuseStep 4759829 = 223117) (by norm_num)
theorem B3173219 : Blo 2115435 3173219 := bstep (se 1 (by rfl) ⟨2379914, by rfl⟩ : syracuseStep 3173219 = 4759829) B4759829
theorem B2115479 : Blo 2115435 2115479 := bstep (se 1 (by rfl) ⟨1586609, by rfl⟩ : syracuseStep 2115479 = 3173219) B3173219
theorem B8032229 : Blo 2115435 8032229 := bbase (se 4 (by rfl) ⟨753021, by rfl⟩ : syracuseStep 8032229 = 1506043) (by norm_num)
theorem B5354819 : Blo 2115435 5354819 := bstep (se 1 (by rfl) ⟨4016114, by rfl⟩ : syracuseStep 5354819 = 8032229) B8032229
theorem B3569879 : Blo 2115435 3569879 := bstep (se 1 (by rfl) ⟨2677409, by rfl⟩ : syracuseStep 3569879 = 5354819) B5354819
theorem B2379919 : Blo 2115435 2379919 := bstep (se 1 (by rfl) ⟨1784939, by rfl⟩ : syracuseStep 2379919 = 3569879) B3569879
theorem B3173225 : Blo 2115435 3173225 := bstep (se 2 (by rfl) ⟨1189959, by rfl⟩ : syracuseStep 3173225 = 2379919) B2379919
theorem B2115483 : Blo 2115435 2115483 := bstep (se 1 (by rfl) ⟨1586612, by rfl⟩ : syracuseStep 2115483 = 3173225) B3173225
theorem B10855781 : Blo 2115435 10855781 := bbase (se 4 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 10855781 = 2035459) (by norm_num)
theorem B7237187 : Blo 2115435 7237187 := bstep (se 1 (by rfl) ⟨5427890, by rfl⟩ : syracuseStep 7237187 = 10855781) B10855781
theorem B4824791 : Blo 2115435 4824791 := bstep (se 1 (by rfl) ⟨3618593, by rfl⟩ : syracuseStep 4824791 = 7237187) B7237187
theorem B3216527 : Blo 2115435 3216527 := bstep (se 1 (by rfl) ⟨2412395, by rfl⟩ : syracuseStep 3216527 = 4824791) B4824791
theorem B2144351 : Blo 2115435 2144351 := bstep (se 1 (by rfl) ⟨1608263, by rfl⟩ : syracuseStep 2144351 = 3216527) B3216527
theorem B5718269 : Blo 2115435 5718269 := bstep (se 3 (by rfl) ⟨1072175, by rfl⟩ : syracuseStep 5718269 = 2144351) B2144351
theorem B3812179 : Blo 2115435 3812179 := bstep (se 1 (by rfl) ⟨2859134, by rfl⟩ : syracuseStep 3812179 = 5718269) B5718269
theorem B5082905 : Blo 2115435 5082905 := bstep (se 2 (by rfl) ⟨1906089, by rfl⟩ : syracuseStep 5082905 = 3812179) B3812179
theorem B3388603 : Blo 2115435 3388603 := bstep (se 1 (by rfl) ⟨2541452, by rfl⟩ : syracuseStep 3388603 = 5082905) B5082905
theorem B4518137 : Blo 2115435 4518137 := bstep (se 2 (by rfl) ⟨1694301, by rfl⟩ : syracuseStep 4518137 = 3388603) B3388603
theorem B12048365 : Blo 2115435 12048365 := bstep (se 3 (by rfl) ⟨2259068, by rfl⟩ : syracuseStep 12048365 = 4518137) B4518137
theorem B8032243 : Blo 2115435 8032243 := bstep (se 1 (by rfl) ⟨6024182, by rfl⟩ : syracuseStep 8032243 = 12048365) B12048365
theorem B10709657 : Blo 2115435 10709657 := bstep (se 2 (by rfl) ⟨4016121, by rfl⟩ : syracuseStep 10709657 = 8032243) B8032243
theorem B7139771 : Blo 2115435 7139771 := bstep (se 1 (by rfl) ⟨5354828, by rfl⟩ : syracuseStep 7139771 = 10709657) B10709657
theorem B4759847 : Blo 2115435 4759847 := bstep (se 1 (by rfl) ⟨3569885, by rfl⟩ : syracuseStep 4759847 = 7139771) B7139771
theorem B3173231 : Blo 2115435 3173231 := bstep (se 1 (by rfl) ⟨2379923, by rfl⟩ : syracuseStep 3173231 = 4759847) B4759847
theorem B2115487 : Blo 2115435 2115487 := bstep (se 1 (by rfl) ⟨1586615, by rfl⟩ : syracuseStep 2115487 = 3173231) B3173231
theorem B3173237 : Blo 2115435 3173237 := bbase (se 5 (by rfl) ⟨148745, by rfl⟩ : syracuseStep 3173237 = 297491) (by norm_num)
theorem B2115491 : Blo 2115435 2115491 := bstep (se 1 (by rfl) ⟨1586618, by rfl⟩ : syracuseStep 2115491 = 3173237) B3173237
theorem B5082925 : Blo 2115435 5082925 := bbase (se 3 (by rfl) ⟨953048, by rfl⟩ : syracuseStep 5082925 = 1906097) (by norm_num)
theorem B6777233 : Blo 2115435 6777233 := bstep (se 2 (by rfl) ⟨2541462, by rfl⟩ : syracuseStep 6777233 = 5082925) B5082925
theorem B4518155 : Blo 2115435 4518155 := bstep (se 1 (by rfl) ⟨3388616, by rfl⟩ : syracuseStep 4518155 = 6777233) B6777233
theorem B3012103 : Blo 2115435 3012103 := bstep (se 1 (by rfl) ⟨2259077, by rfl⟩ : syracuseStep 3012103 = 4518155) B4518155
theorem B4016137 : Blo 2115435 4016137 := bstep (se 2 (by rfl) ⟨1506051, by rfl⟩ : syracuseStep 4016137 = 3012103) B3012103
theorem B5354849 : Blo 2115435 5354849 := bstep (se 2 (by rfl) ⟨2008068, by rfl⟩ : syracuseStep 5354849 = 4016137) B4016137
theorem B3569899 : Blo 2115435 3569899 := bstep (se 1 (by rfl) ⟨2677424, by rfl⟩ : syracuseStep 3569899 = 5354849) B5354849
theorem B4759865 : Blo 2115435 4759865 := bstep (se 2 (by rfl) ⟨1784949, by rfl⟩ : syracuseStep 4759865 = 3569899) B3569899
theorem B3173243 : Blo 2115435 3173243 := bstep (se 1 (by rfl) ⟨2379932, by rfl⟩ : syracuseStep 3173243 = 4759865) B4759865
theorem B2115495 : Blo 2115435 2115495 := bstep (se 1 (by rfl) ⟨1586621, by rfl⟩ : syracuseStep 2115495 = 3173243) B3173243
theorem B2379937 : Blo 2115435 2379937 := bbase (se 2 (by rfl) ⟨892476, by rfl⟩ : syracuseStep 2379937 = 1784953) (by norm_num)
theorem B3173249 : Blo 2115435 3173249 := bstep (se 2 (by rfl) ⟨1189968, by rfl⟩ : syracuseStep 3173249 = 2379937) B2379937
theorem B2115499 : Blo 2115435 2115499 := bstep (se 1 (by rfl) ⟨1586624, by rfl⟩ : syracuseStep 2115499 = 3173249) B3173249
theorem B5354869 : Blo 2115435 5354869 := bbase (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) (by norm_num)
theorem B7139825 : Blo 2115435 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B4759883 : Blo 2115435 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B3173255 : Blo 2115435 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B2115503 : Blo 2115435 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B3173261 : Blo 2115435 3173261 := bbase (se 3 (by rfl) ⟨594986, by rfl⟩ : syracuseStep 3173261 = 1189973) (by norm_num)
theorem B2115507 : Blo 2115435 2115507 := bstep (se 1 (by rfl) ⟨1586630, by rfl⟩ : syracuseStep 2115507 = 3173261) B3173261
theorem B4759901 : Blo 2115435 4759901 := bbase (se 3 (by rfl) ⟨892481, by rfl⟩ : syracuseStep 4759901 = 1784963) (by norm_num)
theorem B3173267 : Blo 2115435 3173267 := bstep (se 1 (by rfl) ⟨2379950, by rfl⟩ : syracuseStep 3173267 = 4759901) B4759901
theorem B2115511 : Blo 2115435 2115511 := bstep (se 1 (by rfl) ⟨1586633, by rfl⟩ : syracuseStep 2115511 = 3173267) B3173267
theorem B3569933 : Blo 2115435 3569933 := bbase (se 3 (by rfl) ⟨669362, by rfl⟩ : syracuseStep 3569933 = 1338725) (by norm_num)
theorem B2379955 : Blo 2115435 2379955 := bstep (se 1 (by rfl) ⟨1784966, by rfl⟩ : syracuseStep 2379955 = 3569933) B3569933
theorem B3173273 : Blo 2115435 3173273 := bstep (se 2 (by rfl) ⟨1189977, by rfl⟩ : syracuseStep 3173273 = 2379955) B2379955
theorem B2115515 : Blo 2115435 2115515 := bstep (se 1 (by rfl) ⟨1586636, by rfl⟩ : syracuseStep 2115515 = 3173273) B3173273
theorem B18072821 : Blo 2115435 18072821 := bbase (se 5 (by rfl) ⟨847163, by rfl⟩ : syracuseStep 18072821 = 1694327) (by norm_num)
theorem B12048547 : Blo 2115435 12048547 := bstep (se 1 (by rfl) ⟨9036410, by rfl⟩ : syracuseStep 12048547 = 18072821) B18072821
theorem B16064729 : Blo 2115435 16064729 := bstep (se 2 (by rfl) ⟨6024273, by rfl⟩ : syracuseStep 16064729 = 12048547) B12048547
theorem B10709819 : Blo 2115435 10709819 := bstep (se 1 (by rfl) ⟨8032364, by rfl⟩ : syracuseStep 10709819 = 16064729) B16064729
theorem B7139879 : Blo 2115435 7139879 := bstep (se 1 (by rfl) ⟨5354909, by rfl⟩ : syracuseStep 7139879 = 10709819) B10709819
theorem B4759919 : Blo 2115435 4759919 := bstep (se 1 (by rfl) ⟨3569939, by rfl⟩ : syracuseStep 4759919 = 7139879) B7139879
theorem B3173279 : Blo 2115435 3173279 := bstep (se 1 (by rfl) ⟨2379959, by rfl⟩ : syracuseStep 3173279 = 4759919) B4759919
theorem B2115519 : Blo 2115435 2115519 := bstep (se 1 (by rfl) ⟨1586639, by rfl⟩ : syracuseStep 2115519 = 3173279) B3173279
theorem B3173285 : Blo 2115435 3173285 := bbase (se 4 (by rfl) ⟨297495, by rfl⟩ : syracuseStep 3173285 = 594991) (by norm_num)
theorem B2115523 : Blo 2115435 2115523 := bstep (se 1 (by rfl) ⟨1586642, by rfl⟩ : syracuseStep 2115523 = 3173285) B3173285
theorem B2677465 : Blo 2115435 2677465 := bbase (se 2 (by rfl) ⟨1004049, by rfl⟩ : syracuseStep 2677465 = 2008099) (by norm_num)
theorem B3569953 : Blo 2115435 3569953 := bstep (se 2 (by rfl) ⟨1338732, by rfl⟩ : syracuseStep 3569953 = 2677465) B2677465
theorem B4759937 : Blo 2115435 4759937 := bstep (se 2 (by rfl) ⟨1784976, by rfl⟩ : syracuseStep 4759937 = 3569953) B3569953
theorem B3173291 : Blo 2115435 3173291 := bstep (se 1 (by rfl) ⟨2379968, by rfl⟩ : syracuseStep 3173291 = 4759937) B4759937
theorem B2115527 : Blo 2115435 2115527 := bstep (se 1 (by rfl) ⟨1586645, by rfl⟩ : syracuseStep 2115527 = 3173291) B3173291
theorem B2379973 : Blo 2115435 2379973 := bbase (se 4 (by rfl) ⟨223122, by rfl⟩ : syracuseStep 2379973 = 446245) (by norm_num)
theorem B3173297 : Blo 2115435 3173297 := bstep (se 2 (by rfl) ⟨1189986, by rfl⟩ : syracuseStep 3173297 = 2379973) B2379973
theorem B2115531 : Blo 2115435 2115531 := bstep (se 1 (by rfl) ⟨1586648, by rfl⟩ : syracuseStep 2115531 = 3173297) B3173297
theorem B4016213 : Blo 2115435 4016213 := bbase (se 8 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 4016213 = 47065) (by norm_num)
theorem B2677475 : Blo 2115435 2677475 := bstep (se 1 (by rfl) ⟨2008106, by rfl⟩ : syracuseStep 2677475 = 4016213) B4016213
theorem B7139933 : Blo 2115435 7139933 := bstep (se 3 (by rfl) ⟨1338737, by rfl⟩ : syracuseStep 7139933 = 2677475) B2677475
theorem B4759955 : Blo 2115435 4759955 := bstep (se 1 (by rfl) ⟨3569966, by rfl⟩ : syracuseStep 4759955 = 7139933) B7139933
theorem B3173303 : Blo 2115435 3173303 := bstep (se 1 (by rfl) ⟨2379977, by rfl⟩ : syracuseStep 3173303 = 4759955) B4759955
theorem B2115535 : Blo 2115435 2115535 := bstep (se 1 (by rfl) ⟨1586651, by rfl⟩ : syracuseStep 2115535 = 3173303) B3173303
theorem B3173309 : Blo 2115435 3173309 := bbase (se 3 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 3173309 = 1189991) (by norm_num)
theorem B2115539 : Blo 2115435 2115539 := bstep (se 1 (by rfl) ⟨1586654, by rfl⟩ : syracuseStep 2115539 = 3173309) B3173309
theorem B4759973 : Blo 2115435 4759973 := bbase (se 4 (by rfl) ⟨446247, by rfl⟩ : syracuseStep 4759973 = 892495) (by norm_num)
theorem B3173315 : Blo 2115435 3173315 := bstep (se 1 (by rfl) ⟨2379986, by rfl⟩ : syracuseStep 3173315 = 4759973) B4759973
theorem B2115543 : Blo 2115435 2115543 := bstep (se 1 (by rfl) ⟨1586657, by rfl⟩ : syracuseStep 2115543 = 3173315) B3173315
theorem B5354981 : Blo 2115435 5354981 := bbase (se 4 (by rfl) ⟨502029, by rfl⟩ : syracuseStep 5354981 = 1004059) (by norm_num)
theorem B3569987 : Blo 2115435 3569987 := bstep (se 1 (by rfl) ⟨2677490, by rfl⟩ : syracuseStep 3569987 = 5354981) B5354981
theorem B2379991 : Blo 2115435 2379991 := bstep (se 1 (by rfl) ⟨1784993, by rfl⟩ : syracuseStep 2379991 = 3569987) B3569987
theorem B3173321 : Blo 2115435 3173321 := bstep (se 2 (by rfl) ⟨1189995, by rfl⟩ : syracuseStep 3173321 = 2379991) B2379991
theorem B2115547 : Blo 2115435 2115547 := bstep (se 1 (by rfl) ⟨1586660, by rfl⟩ : syracuseStep 2115547 = 3173321) B3173321
theorem B2259137 : Blo 2115435 2259137 := bbase (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) (by norm_num)
theorem B6024365 : Blo 2115435 6024365 := bstep (se 3 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 6024365 = 2259137) B2259137
theorem B4016243 : Blo 2115435 4016243 := bstep (se 1 (by rfl) ⟨3012182, by rfl⟩ : syracuseStep 4016243 = 6024365) B6024365
theorem B10709981 : Blo 2115435 10709981 := bstep (se 3 (by rfl) ⟨2008121, by rfl⟩ : syracuseStep 10709981 = 4016243) B4016243
theorem B7139987 : Blo 2115435 7139987 := bstep (se 1 (by rfl) ⟨5354990, by rfl⟩ : syracuseStep 7139987 = 10709981) B10709981
theorem B4759991 : Blo 2115435 4759991 := bstep (se 1 (by rfl) ⟨3569993, by rfl⟩ : syracuseStep 4759991 = 7139987) B7139987
theorem B3173327 : Blo 2115435 3173327 := bstep (se 1 (by rfl) ⟨2379995, by rfl⟩ : syracuseStep 3173327 = 4759991) B4759991
theorem B2115551 : Blo 2115435 2115551 := bstep (se 1 (by rfl) ⟨1586663, by rfl⟩ : syracuseStep 2115551 = 3173327) B3173327
theorem B3173333 : Blo 2115435 3173333 := bbase (se 7 (by rfl) ⟨37187, by rfl⟩ : syracuseStep 3173333 = 74375) (by norm_num)
theorem B2115555 : Blo 2115435 2115555 := bstep (se 1 (by rfl) ⟨1586666, by rfl⟩ : syracuseStep 2115555 = 3173333) B3173333
theorem B8032517 : Blo 2115435 8032517 := bbase (se 4 (by rfl) ⟨753048, by rfl⟩ : syracuseStep 8032517 = 1506097) (by norm_num)
theorem B5355011 : Blo 2115435 5355011 := bstep (se 1 (by rfl) ⟨4016258, by rfl⟩ : syracuseStep 5355011 = 8032517) B8032517
theorem B3570007 : Blo 2115435 3570007 := bstep (se 1 (by rfl) ⟨2677505, by rfl⟩ : syracuseStep 3570007 = 5355011) B5355011
theorem B4760009 : Blo 2115435 4760009 := bstep (se 2 (by rfl) ⟨1785003, by rfl⟩ : syracuseStep 4760009 = 3570007) B3570007
theorem B3173339 : Blo 2115435 3173339 := bstep (se 1 (by rfl) ⟨2380004, by rfl⟩ : syracuseStep 3173339 = 4760009) B4760009
theorem B2115559 : Blo 2115435 2115559 := bstep (se 1 (by rfl) ⟨1586669, by rfl⟩ : syracuseStep 2115559 = 3173339) B3173339
theorem B2380009 : Blo 2115435 2380009 := bbase (se 2 (by rfl) ⟨892503, by rfl⟩ : syracuseStep 2380009 = 1785007) (by norm_num)
theorem B3173345 : Blo 2115435 3173345 := bstep (se 2 (by rfl) ⟨1190004, by rfl⟩ : syracuseStep 3173345 = 2380009) B2380009
theorem B2115563 : Blo 2115435 2115563 := bstep (se 1 (by rfl) ⟨1586672, by rfl⟩ : syracuseStep 2115563 = 3173345) B3173345
theorem B12048821 : Blo 2115435 12048821 := bbase (se 5 (by rfl) ⟨564788, by rfl⟩ : syracuseStep 12048821 = 1129577) (by norm_num)
theorem B8032547 : Blo 2115435 8032547 := bstep (se 1 (by rfl) ⟨6024410, by rfl⟩ : syracuseStep 8032547 = 12048821) B12048821
theorem B5355031 : Blo 2115435 5355031 := bstep (se 1 (by rfl) ⟨4016273, by rfl⟩ : syracuseStep 5355031 = 8032547) B8032547
theorem B7140041 : Blo 2115435 7140041 := bstep (se 2 (by rfl) ⟨2677515, by rfl⟩ : syracuseStep 7140041 = 5355031) B5355031
theorem B4760027 : Blo 2115435 4760027 := bstep (se 1 (by rfl) ⟨3570020, by rfl⟩ : syracuseStep 4760027 = 7140041) B7140041
theorem B3173351 : Blo 2115435 3173351 := bstep (se 1 (by rfl) ⟨2380013, by rfl⟩ : syracuseStep 3173351 = 4760027) B4760027
theorem B2115567 : Blo 2115435 2115567 := bstep (se 1 (by rfl) ⟨1586675, by rfl⟩ : syracuseStep 2115567 = 3173351) B3173351
theorem B3173357 : Blo 2115435 3173357 := bbase (se 3 (by rfl) ⟨595004, by rfl⟩ : syracuseStep 3173357 = 1190009) (by norm_num)
theorem B2115571 : Blo 2115435 2115571 := bstep (se 1 (by rfl) ⟨1586678, by rfl⟩ : syracuseStep 2115571 = 3173357) B3173357
theorem B4760045 : Blo 2115435 4760045 := bbase (se 3 (by rfl) ⟨892508, by rfl⟩ : syracuseStep 4760045 = 1785017) (by norm_num)
theorem B3173363 : Blo 2115435 3173363 := bstep (se 1 (by rfl) ⟨2380022, by rfl⟩ : syracuseStep 3173363 = 4760045) B4760045
theorem B2115575 : Blo 2115435 2115575 := bstep (se 1 (by rfl) ⟨1586681, by rfl⟩ : syracuseStep 2115575 = 3173363) B3173363
theorem B18319925 : Blo 2115435 18319925 := bbase (se 5 (by rfl) ⟨858746, by rfl⟩ : syracuseStep 18319925 = 1717493) (by norm_num)
theorem B12213283 : Blo 2115435 12213283 := bstep (se 1 (by rfl) ⟨9159962, by rfl⟩ : syracuseStep 12213283 = 18319925) B18319925
theorem B16284377 : Blo 2115435 16284377 := bstep (se 2 (by rfl) ⟨6106641, by rfl⟩ : syracuseStep 16284377 = 12213283) B12213283
theorem B10856251 : Blo 2115435 10856251 := bstep (se 1 (by rfl) ⟨8142188, by rfl⟩ : syracuseStep 10856251 = 16284377) B16284377
theorem B57900005 : Blo 2115435 57900005 := bstep (se 4 (by rfl) ⟨5428125, by rfl⟩ : syracuseStep 57900005 = 10856251) B10856251
theorem B38600003 : Blo 2115435 38600003 := bstep (se 1 (by rfl) ⟨28950002, by rfl⟩ : syracuseStep 38600003 = 57900005) B57900005
theorem B25733335 : Blo 2115435 25733335 := bstep (se 1 (by rfl) ⟨19300001, by rfl⟩ : syracuseStep 25733335 = 38600003) B38600003
theorem B34311113 : Blo 2115435 34311113 := bstep (se 2 (by rfl) ⟨12866667, by rfl⟩ : syracuseStep 34311113 = 25733335) B25733335
theorem B22874075 : Blo 2115435 22874075 := bstep (se 1 (by rfl) ⟨17155556, by rfl⟩ : syracuseStep 22874075 = 34311113) B34311113
theorem B15249383 : Blo 2115435 15249383 := bstep (se 1 (by rfl) ⟨11437037, by rfl⟩ : syracuseStep 15249383 = 22874075) B22874075
theorem B10166255 : Blo 2115435 10166255 := bstep (se 1 (by rfl) ⟨7624691, by rfl⟩ : syracuseStep 10166255 = 15249383) B15249383
theorem B6777503 : Blo 2115435 6777503 := bstep (se 1 (by rfl) ⟨5083127, by rfl⟩ : syracuseStep 6777503 = 10166255) B10166255
theorem B4518335 : Blo 2115435 4518335 := bstep (se 1 (by rfl) ⟨3388751, by rfl⟩ : syracuseStep 4518335 = 6777503) B6777503
theorem B3012223 : Blo 2115435 3012223 := bstep (se 1 (by rfl) ⟨2259167, by rfl⟩ : syracuseStep 3012223 = 4518335) B4518335
theorem B4016297 : Blo 2115435 4016297 := bstep (se 2 (by rfl) ⟨1506111, by rfl⟩ : syracuseStep 4016297 = 3012223) B3012223
theorem B2677531 : Blo 2115435 2677531 := bstep (se 1 (by rfl) ⟨2008148, by rfl⟩ : syracuseStep 2677531 = 4016297) B4016297
theorem B3570041 : Blo 2115435 3570041 := bstep (se 2 (by rfl) ⟨1338765, by rfl⟩ : syracuseStep 3570041 = 2677531) B2677531
theorem B2380027 : Blo 2115435 2380027 := bstep (se 1 (by rfl) ⟨1785020, by rfl⟩ : syracuseStep 2380027 = 3570041) B3570041
theorem B3173369 : Blo 2115435 3173369 := bstep (se 2 (by rfl) ⟨1190013, by rfl⟩ : syracuseStep 3173369 = 2380027) B2380027
theorem B2115579 : Blo 2115435 2115579 := bstep (se 1 (by rfl) ⟨1586684, by rfl⟩ : syracuseStep 2115579 = 3173369) B3173369
theorem B3864365 : Blo 2115435 3864365 := bbase (se 3 (by rfl) ⟨724568, by rfl⟩ : syracuseStep 3864365 = 1449137) (by norm_num)
theorem B2576243 : Blo 2115435 2576243 := bstep (se 1 (by rfl) ⟨1932182, by rfl⟩ : syracuseStep 2576243 = 3864365) B3864365
theorem B6869981 : Blo 2115435 6869981 := bstep (se 3 (by rfl) ⟨1288121, by rfl⟩ : syracuseStep 6869981 = 2576243) B2576243
theorem B4579987 : Blo 2115435 4579987 := bstep (se 1 (by rfl) ⟨3434990, by rfl⟩ : syracuseStep 4579987 = 6869981) B6869981
theorem B390825557 : Blo 2115435 390825557 := bstep (se 8 (by rfl) ⟨2289993, by rfl⟩ : syracuseStep 390825557 = 4579987) B4579987
theorem B260550371 : Blo 2115435 260550371 := bstep (se 1 (by rfl) ⟨195412778, by rfl⟩ : syracuseStep 260550371 = 390825557) B390825557
theorem B173700247 : Blo 2115435 173700247 := bstep (se 1 (by rfl) ⟨130275185, by rfl⟩ : syracuseStep 173700247 = 260550371) B260550371
theorem B231600329 : Blo 2115435 231600329 := bstep (se 2 (by rfl) ⟨86850123, by rfl⟩ : syracuseStep 231600329 = 173700247) B173700247
theorem B154400219 : Blo 2115435 154400219 := bstep (se 1 (by rfl) ⟨115800164, by rfl⟩ : syracuseStep 154400219 = 231600329) B231600329
theorem B102933479 : Blo 2115435 102933479 := bstep (se 1 (by rfl) ⟨77200109, by rfl⟩ : syracuseStep 102933479 = 154400219) B154400219
theorem B68622319 : Blo 2115435 68622319 := bstep (se 1 (by rfl) ⟨51466739, by rfl⟩ : syracuseStep 68622319 = 102933479) B102933479
theorem B91496425 : Blo 2115435 91496425 := bstep (se 2 (by rfl) ⟨34311159, by rfl⟩ : syracuseStep 91496425 = 68622319) B68622319
theorem B121995233 : Blo 2115435 121995233 := bstep (se 2 (by rfl) ⟨45748212, by rfl⟩ : syracuseStep 121995233 = 91496425) B91496425
theorem B81330155 : Blo 2115435 81330155 := bstep (se 1 (by rfl) ⟨60997616, by rfl⟩ : syracuseStep 81330155 = 121995233) B121995233
theorem B54220103 : Blo 2115435 54220103 := bstep (se 1 (by rfl) ⟨40665077, by rfl⟩ : syracuseStep 54220103 = 81330155) B81330155
theorem B36146735 : Blo 2115435 36146735 := bstep (se 1 (by rfl) ⟨27110051, by rfl⟩ : syracuseStep 36146735 = 54220103) B54220103
theorem B24097823 : Blo 2115435 24097823 := bstep (se 1 (by rfl) ⟨18073367, by rfl⟩ : syracuseStep 24097823 = 36146735) B36146735
theorem B16065215 : Blo 2115435 16065215 := bstep (se 1 (by rfl) ⟨12048911, by rfl⟩ : syracuseStep 16065215 = 24097823) B24097823
theorem B10710143 : Blo 2115435 10710143 := bstep (se 1 (by rfl) ⟨8032607, by rfl⟩ : syracuseStep 10710143 = 16065215) B16065215
theorem B7140095 : Blo 2115435 7140095 := bstep (se 1 (by rfl) ⟨5355071, by rfl⟩ : syracuseStep 7140095 = 10710143) B10710143
theorem B4760063 : Blo 2115435 4760063 := bstep (se 1 (by rfl) ⟨3570047, by rfl⟩ : syracuseStep 4760063 = 7140095) B7140095
theorem B3173375 : Blo 2115435 3173375 := bstep (se 1 (by rfl) ⟨2380031, by rfl⟩ : syracuseStep 3173375 = 4760063) B4760063
theorem B2115583 : Blo 2115435 2115583 := bstep (se 1 (by rfl) ⟨1586687, by rfl⟩ : syracuseStep 2115583 = 3173375) B3173375
theorem B3173381 : Blo 2115435 3173381 := bbase (se 4 (by rfl) ⟨297504, by rfl⟩ : syracuseStep 3173381 = 595009) (by norm_num)
theorem B2115587 : Blo 2115435 2115587 := bstep (se 1 (by rfl) ⟨1586690, by rfl⟩ : syracuseStep 2115587 = 3173381) B3173381
theorem B3570061 : Blo 2115435 3570061 := bbase (se 3 (by rfl) ⟨669386, by rfl⟩ : syracuseStep 3570061 = 1338773) (by norm_num)
theorem B4760081 : Blo 2115435 4760081 := bstep (se 2 (by rfl) ⟨1785030, by rfl⟩ : syracuseStep 4760081 = 3570061) B3570061
theorem B3173387 : Blo 2115435 3173387 := bstep (se 1 (by rfl) ⟨2380040, by rfl⟩ : syracuseStep 3173387 = 4760081) B4760081
theorem B2115591 : Blo 2115435 2115591 := bstep (se 1 (by rfl) ⟨1586693, by rfl⟩ : syracuseStep 2115591 = 3173387) B3173387
theorem B2380045 : Blo 2115435 2380045 := bbase (se 3 (by rfl) ⟨446258, by rfl⟩ : syracuseStep 2380045 = 892517) (by norm_num)
theorem B3173393 : Blo 2115435 3173393 := bstep (se 2 (by rfl) ⟨1190022, by rfl⟩ : syracuseStep 3173393 = 2380045) B2380045
theorem B2115595 : Blo 2115435 2115595 := bstep (se 1 (by rfl) ⟨1586696, by rfl⟩ : syracuseStep 2115595 = 3173393) B3173393
theorem B7140149 : Blo 2115435 7140149 := bbase (se 5 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 7140149 = 669389) (by norm_num)
theorem B4760099 : Blo 2115435 4760099 := bstep (se 1 (by rfl) ⟨3570074, by rfl⟩ : syracuseStep 4760099 = 7140149) B7140149
theorem B3173399 : Blo 2115435 3173399 := bstep (se 1 (by rfl) ⟨2380049, by rfl⟩ : syracuseStep 3173399 = 4760099) B4760099
theorem B2115599 : Blo 2115435 2115599 := bstep (se 1 (by rfl) ⟨1586699, by rfl⟩ : syracuseStep 2115599 = 3173399) B3173399
theorem B3173405 : Blo 2115435 3173405 := bbase (se 3 (by rfl) ⟨595013, by rfl⟩ : syracuseStep 3173405 = 1190027) (by norm_num)
theorem B2115603 : Blo 2115435 2115603 := bstep (se 1 (by rfl) ⟨1586702, by rfl⟩ : syracuseStep 2115603 = 3173405) B3173405
theorem B4760117 : Blo 2115435 4760117 := bbase (se 5 (by rfl) ⟨223130, by rfl⟩ : syracuseStep 4760117 = 446261) (by norm_num)
theorem B3173411 : Blo 2115435 3173411 := bstep (se 1 (by rfl) ⟨2380058, by rfl⟩ : syracuseStep 3173411 = 4760117) B4760117
theorem B2115607 : Blo 2115435 2115607 := bstep (se 1 (by rfl) ⟨1586705, by rfl⟩ : syracuseStep 2115607 = 3173411) B3173411
theorem B9036805 : Blo 2115435 9036805 := bbase (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) (by norm_num)
theorem B12049073 : Blo 2115435 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B8032715 : Blo 2115435 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B5355143 : Blo 2115435 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B3570095 : Blo 2115435 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B2380063 : Blo 2115435 2380063 := bstep (se 1 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 2380063 = 3570095) B3570095
theorem B3173417 : Blo 2115435 3173417 := bstep (se 2 (by rfl) ⟨1190031, by rfl⟩ : syracuseStep 3173417 = 2380063) B2380063
theorem B2115611 : Blo 2115435 2115611 := bstep (se 1 (by rfl) ⟨1586708, by rfl⟩ : syracuseStep 2115611 = 3173417) B3173417
theorem B9036821 : Blo 2115435 9036821 := bbase (se 6 (by rfl) ⟨211800, by rfl⟩ : syracuseStep 9036821 = 423601) (by norm_num)
theorem B6024547 : Blo 2115435 6024547 := bstep (se 1 (by rfl) ⟨4518410, by rfl⟩ : syracuseStep 6024547 = 9036821) B9036821
theorem B8032729 : Blo 2115435 8032729 := bstep (se 2 (by rfl) ⟨3012273, by rfl⟩ : syracuseStep 8032729 = 6024547) B6024547
theorem B10710305 : Blo 2115435 10710305 := bstep (se 2 (by rfl) ⟨4016364, by rfl⟩ : syracuseStep 10710305 = 8032729) B8032729
theorem B7140203 : Blo 2115435 7140203 := bstep (se 1 (by rfl) ⟨5355152, by rfl⟩ : syracuseStep 7140203 = 10710305) B10710305
theorem B4760135 : Blo 2115435 4760135 := bstep (se 1 (by rfl) ⟨3570101, by rfl⟩ : syracuseStep 4760135 = 7140203) B7140203
theorem B3173423 : Blo 2115435 3173423 := bstep (se 1 (by rfl) ⟨2380067, by rfl⟩ : syracuseStep 3173423 = 4760135) B4760135
theorem B2115615 : Blo 2115435 2115615 := bstep (se 1 (by rfl) ⟨1586711, by rfl⟩ : syracuseStep 2115615 = 3173423) B3173423
theorem B3173429 : Blo 2115435 3173429 := bbase (se 5 (by rfl) ⟨148754, by rfl⟩ : syracuseStep 3173429 = 297509) (by norm_num)
theorem B2115619 : Blo 2115435 2115619 := bstep (se 1 (by rfl) ⟨1586714, by rfl⟩ : syracuseStep 2115619 = 3173429) B3173429
theorem B5355173 : Blo 2115435 5355173 := bbase (se 4 (by rfl) ⟨502047, by rfl⟩ : syracuseStep 5355173 = 1004095) (by norm_num)
theorem B3570115 : Blo 2115435 3570115 := bstep (se 1 (by rfl) ⟨2677586, by rfl⟩ : syracuseStep 3570115 = 5355173) B5355173
theorem B4760153 : Blo 2115435 4760153 := bstep (se 2 (by rfl) ⟨1785057, by rfl⟩ : syracuseStep 4760153 = 3570115) B3570115
theorem B3173435 : Blo 2115435 3173435 := bstep (se 1 (by rfl) ⟨2380076, by rfl⟩ : syracuseStep 3173435 = 4760153) B4760153
theorem B2115623 : Blo 2115435 2115623 := bstep (se 1 (by rfl) ⟨1586717, by rfl⟩ : syracuseStep 2115623 = 3173435) B3173435
theorem B2380081 : Blo 2115435 2380081 := bbase (se 2 (by rfl) ⟨892530, by rfl⟩ : syracuseStep 2380081 = 1785061) (by norm_num)
theorem B3173441 : Blo 2115435 3173441 := bstep (se 2 (by rfl) ⟨1190040, by rfl⟩ : syracuseStep 3173441 = 2380081) B2380081
theorem B2115627 : Blo 2115435 2115627 := bstep (se 1 (by rfl) ⟨1586720, by rfl⟩ : syracuseStep 2115627 = 3173441) B3173441
theorem B4518445 : Blo 2115435 4518445 := bbase (se 3 (by rfl) ⟨847208, by rfl⟩ : syracuseStep 4518445 = 1694417) (by norm_num)
theorem B6024593 : Blo 2115435 6024593 := bstep (se 2 (by rfl) ⟨2259222, by rfl⟩ : syracuseStep 6024593 = 4518445) B4518445
theorem B4016395 : Blo 2115435 4016395 := bstep (se 1 (by rfl) ⟨3012296, by rfl⟩ : syracuseStep 4016395 = 6024593) B6024593
theorem B5355193 : Blo 2115435 5355193 := bstep (se 2 (by rfl) ⟨2008197, by rfl⟩ : syracuseStep 5355193 = 4016395) B4016395
theorem B7140257 : Blo 2115435 7140257 := bstep (se 2 (by rfl) ⟨2677596, by rfl⟩ : syracuseStep 7140257 = 5355193) B5355193
theorem B4760171 : Blo 2115435 4760171 := bstep (se 1 (by rfl) ⟨3570128, by rfl⟩ : syracuseStep 4760171 = 7140257) B7140257
theorem B3173447 : Blo 2115435 3173447 := bstep (se 1 (by rfl) ⟨2380085, by rfl⟩ : syracuseStep 3173447 = 4760171) B4760171
theorem B2115631 : Blo 2115435 2115631 := bstep (se 1 (by rfl) ⟨1586723, by rfl⟩ : syracuseStep 2115631 = 3173447) B3173447
theorem B3173453 : Blo 2115435 3173453 := bbase (se 3 (by rfl) ⟨595022, by rfl⟩ : syracuseStep 3173453 = 1190045) (by norm_num)
theorem B2115635 : Blo 2115435 2115635 := bstep (se 1 (by rfl) ⟨1586726, by rfl⟩ : syracuseStep 2115635 = 3173453) B3173453
theorem B4760189 : Blo 2115435 4760189 := bbase (se 3 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 4760189 = 1785071) (by norm_num)
theorem B3173459 : Blo 2115435 3173459 := bstep (se 1 (by rfl) ⟨2380094, by rfl⟩ : syracuseStep 3173459 = 4760189) B4760189
theorem B2115639 : Blo 2115435 2115639 := bstep (se 1 (by rfl) ⟨1586729, by rfl⟩ : syracuseStep 2115639 = 3173459) B3173459
theorem B3570149 : Blo 2115435 3570149 := bbase (se 4 (by rfl) ⟨334701, by rfl⟩ : syracuseStep 3570149 = 669403) (by norm_num)
theorem B2380099 : Blo 2115435 2380099 := bstep (se 1 (by rfl) ⟨1785074, by rfl⟩ : syracuseStep 2380099 = 3570149) B3570149
theorem B3173465 : Blo 2115435 3173465 := bstep (se 2 (by rfl) ⟨1190049, by rfl⟩ : syracuseStep 3173465 = 2380099) B2380099
theorem B2115643 : Blo 2115435 2115643 := bstep (se 1 (by rfl) ⟨1586732, by rfl⟩ : syracuseStep 2115643 = 3173465) B3173465
theorem B2144513 : Blo 2115435 2144513 := bbase (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) (by norm_num)
theorem B5718701 : Blo 2115435 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B15249869 : Blo 2115435 15249869 := bstep (se 3 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 15249869 = 5718701) B5718701
theorem B10166579 : Blo 2115435 10166579 := bstep (se 1 (by rfl) ⟨7624934, by rfl⟩ : syracuseStep 10166579 = 15249869) B15249869
theorem B6777719 : Blo 2115435 6777719 := bstep (se 1 (by rfl) ⟨5083289, by rfl⟩ : syracuseStep 6777719 = 10166579) B10166579
theorem B4518479 : Blo 2115435 4518479 := bstep (se 1 (by rfl) ⟨3388859, by rfl⟩ : syracuseStep 4518479 = 6777719) B6777719
theorem B3012319 : Blo 2115435 3012319 := bstep (se 1 (by rfl) ⟨2259239, by rfl⟩ : syracuseStep 3012319 = 4518479) B4518479
theorem B16065701 : Blo 2115435 16065701 := bstep (se 4 (by rfl) ⟨1506159, by rfl⟩ : syracuseStep 16065701 = 3012319) B3012319
theorem B10710467 : Blo 2115435 10710467 := bstep (se 1 (by rfl) ⟨8032850, by rfl⟩ : syracuseStep 10710467 = 16065701) B16065701
theorem B7140311 : Blo 2115435 7140311 := bstep (se 1 (by rfl) ⟨5355233, by rfl⟩ : syracuseStep 7140311 = 10710467) B10710467
theorem B4760207 : Blo 2115435 4760207 := bstep (se 1 (by rfl) ⟨3570155, by rfl⟩ : syracuseStep 4760207 = 7140311) B7140311
theorem B3173471 : Blo 2115435 3173471 := bstep (se 1 (by rfl) ⟨2380103, by rfl⟩ : syracuseStep 3173471 = 4760207) B4760207
theorem B2115647 : Blo 2115435 2115647 := bstep (se 1 (by rfl) ⟨1586735, by rfl⟩ : syracuseStep 2115647 = 3173471) B3173471
theorem B3173477 : Blo 2115435 3173477 := bbase (se 4 (by rfl) ⟨297513, by rfl⟩ : syracuseStep 3173477 = 595027) (by norm_num)
theorem B2115651 : Blo 2115435 2115651 := bstep (se 1 (by rfl) ⟨1586738, by rfl⟩ : syracuseStep 2115651 = 3173477) B3173477
theorem B5718725 : Blo 2115435 5718725 := bbase (se 4 (by rfl) ⟨536130, by rfl⟩ : syracuseStep 5718725 = 1072261) (by norm_num)
theorem B3812483 : Blo 2115435 3812483 := bstep (se 1 (by rfl) ⟨2859362, by rfl⟩ : syracuseStep 3812483 = 5718725) B5718725
theorem B2541655 : Blo 2115435 2541655 := bstep (se 1 (by rfl) ⟨1906241, by rfl⟩ : syracuseStep 2541655 = 3812483) B3812483
theorem B3388873 : Blo 2115435 3388873 := bstep (se 2 (by rfl) ⟨1270827, by rfl⟩ : syracuseStep 3388873 = 2541655) B2541655
theorem B4518497 : Blo 2115435 4518497 := bstep (se 2 (by rfl) ⟨1694436, by rfl⟩ : syracuseStep 4518497 = 3388873) B3388873
theorem B3012331 : Blo 2115435 3012331 := bstep (se 1 (by rfl) ⟨2259248, by rfl⟩ : syracuseStep 3012331 = 4518497) B4518497
theorem B4016441 : Blo 2115435 4016441 := bstep (se 2 (by rfl) ⟨1506165, by rfl⟩ : syracuseStep 4016441 = 3012331) B3012331
theorem B2677627 : Blo 2115435 2677627 := bstep (se 1 (by rfl) ⟨2008220, by rfl⟩ : syracuseStep 2677627 = 4016441) B4016441
theorem B3570169 : Blo 2115435 3570169 := bstep (se 2 (by rfl) ⟨1338813, by rfl⟩ : syracuseStep 3570169 = 2677627) B2677627
theorem B4760225 : Blo 2115435 4760225 := bstep (se 2 (by rfl) ⟨1785084, by rfl⟩ : syracuseStep 4760225 = 3570169) B3570169
theorem B3173483 : Blo 2115435 3173483 := bstep (se 1 (by rfl) ⟨2380112, by rfl⟩ : syracuseStep 3173483 = 4760225) B4760225
theorem B2115655 : Blo 2115435 2115655 := bstep (se 1 (by rfl) ⟨1586741, by rfl⟩ : syracuseStep 2115655 = 3173483) B3173483
theorem B2380117 : Blo 2115435 2380117 := bbase (se 10 (by rfl) ⟨3486, by rfl⟩ : syracuseStep 2380117 = 6973) (by norm_num)
theorem B3173489 : Blo 2115435 3173489 := bstep (se 2 (by rfl) ⟨1190058, by rfl⟩ : syracuseStep 3173489 = 2380117) B2380117
theorem B2115659 : Blo 2115435 2115659 := bstep (se 1 (by rfl) ⟨1586744, by rfl⟩ : syracuseStep 2115659 = 3173489) B3173489
theorem B2677637 : Blo 2115435 2677637 := bbase (se 4 (by rfl) ⟨251028, by rfl⟩ : syracuseStep 2677637 = 502057) (by norm_num)
theorem B7140365 : Blo 2115435 7140365 := bstep (se 3 (by rfl) ⟨1338818, by rfl⟩ : syracuseStep 7140365 = 2677637) B2677637
theorem B4760243 : Blo 2115435 4760243 := bstep (se 1 (by rfl) ⟨3570182, by rfl⟩ : syracuseStep 4760243 = 7140365) B7140365
theorem B3173495 : Blo 2115435 3173495 := bstep (se 1 (by rfl) ⟨2380121, by rfl⟩ : syracuseStep 3173495 = 4760243) B4760243
theorem B2115663 : Blo 2115435 2115663 := bstep (se 1 (by rfl) ⟨1586747, by rfl⟩ : syracuseStep 2115663 = 3173495) B3173495
theorem B3173501 : Blo 2115435 3173501 := bbase (se 3 (by rfl) ⟨595031, by rfl⟩ : syracuseStep 3173501 = 1190063) (by norm_num)
theorem B2115667 : Blo 2115435 2115667 := bstep (se 1 (by rfl) ⟨1586750, by rfl⟩ : syracuseStep 2115667 = 3173501) B3173501
theorem B4760261 : Blo 2115435 4760261 := bbase (se 4 (by rfl) ⟨446274, by rfl⟩ : syracuseStep 4760261 = 892549) (by norm_num)
theorem B3173507 : Blo 2115435 3173507 := bstep (se 1 (by rfl) ⟨2380130, by rfl⟩ : syracuseStep 3173507 = 4760261) B4760261
theorem B2115671 : Blo 2115435 2115671 := bstep (se 1 (by rfl) ⟨1586753, by rfl⟩ : syracuseStep 2115671 = 3173507) B3173507
theorem B20333429 : Blo 2115435 20333429 := bbase (se 5 (by rfl) ⟨953129, by rfl⟩ : syracuseStep 20333429 = 1906259) (by norm_num)
theorem B13555619 : Blo 2115435 13555619 := bstep (se 1 (by rfl) ⟨10166714, by rfl⟩ : syracuseStep 13555619 = 20333429) B20333429
theorem B9037079 : Blo 2115435 9037079 := bstep (se 1 (by rfl) ⟨6777809, by rfl⟩ : syracuseStep 9037079 = 13555619) B13555619
theorem B6024719 : Blo 2115435 6024719 := bstep (se 1 (by rfl) ⟨4518539, by rfl⟩ : syracuseStep 6024719 = 9037079) B9037079
theorem B4016479 : Blo 2115435 4016479 := bstep (se 1 (by rfl) ⟨3012359, by rfl⟩ : syracuseStep 4016479 = 6024719) B6024719
theorem B5355305 : Blo 2115435 5355305 := bstep (se 2 (by rfl) ⟨2008239, by rfl⟩ : syracuseStep 5355305 = 4016479) B4016479
theorem B3570203 : Blo 2115435 3570203 := bstep (se 1 (by rfl) ⟨2677652, by rfl⟩ : syracuseStep 3570203 = 5355305) B5355305
theorem B2380135 : Blo 2115435 2380135 := bstep (se 1 (by rfl) ⟨1785101, by rfl⟩ : syracuseStep 2380135 = 3570203) B3570203
theorem B3173513 : Blo 2115435 3173513 := bstep (se 2 (by rfl) ⟨1190067, by rfl⟩ : syracuseStep 3173513 = 2380135) B2380135
theorem B2115675 : Blo 2115435 2115675 := bstep (se 1 (by rfl) ⟨1586756, by rfl⟩ : syracuseStep 2115675 = 3173513) B3173513
theorem B10710629 : Blo 2115435 10710629 := bbase (se 4 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 10710629 = 2008243) (by norm_num)
theorem B7140419 : Blo 2115435 7140419 := bstep (se 1 (by rfl) ⟨5355314, by rfl⟩ : syracuseStep 7140419 = 10710629) B10710629
theorem B4760279 : Blo 2115435 4760279 := bstep (se 1 (by rfl) ⟨3570209, by rfl⟩ : syracuseStep 4760279 = 7140419) B7140419
theorem B3173519 : Blo 2115435 3173519 := bstep (se 1 (by rfl) ⟨2380139, by rfl⟩ : syracuseStep 3173519 = 4760279) B4760279
theorem B2115679 : Blo 2115435 2115679 := bstep (se 1 (by rfl) ⟨1586759, by rfl⟩ : syracuseStep 2115679 = 3173519) B3173519
theorem B3173525 : Blo 2115435 3173525 := bbase (se 6 (by rfl) ⟨74379, by rfl⟩ : syracuseStep 3173525 = 148759) (by norm_num)
theorem B2115683 : Blo 2115435 2115683 := bstep (se 1 (by rfl) ⟨1586762, by rfl⟩ : syracuseStep 2115683 = 3173525) B3173525
theorem B3053477 : Blo 2115435 3053477 := bbase (se 4 (by rfl) ⟨286263, by rfl⟩ : syracuseStep 3053477 = 572527) (by norm_num)
theorem B8142605 : Blo 2115435 8142605 := bstep (se 3 (by rfl) ⟨1526738, by rfl⟩ : syracuseStep 8142605 = 3053477) B3053477
theorem B5428403 : Blo 2115435 5428403 := bstep (se 1 (by rfl) ⟨4071302, by rfl⟩ : syracuseStep 5428403 = 8142605) B8142605
theorem B3618935 : Blo 2115435 3618935 := bstep (se 1 (by rfl) ⟨2714201, by rfl⟩ : syracuseStep 3618935 = 5428403) B5428403
theorem B2412623 : Blo 2115435 2412623 := bstep (se 1 (by rfl) ⟨1809467, by rfl⟩ : syracuseStep 2412623 = 3618935) B3618935
theorem B6433661 : Blo 2115435 6433661 := bstep (se 3 (by rfl) ⟨1206311, by rfl⟩ : syracuseStep 6433661 = 2412623) B2412623
theorem B4289107 : Blo 2115435 4289107 := bstep (se 1 (by rfl) ⟨3216830, by rfl⟩ : syracuseStep 4289107 = 6433661) B6433661
theorem B5718809 : Blo 2115435 5718809 := bstep (se 2 (by rfl) ⟨2144553, by rfl⟩ : syracuseStep 5718809 = 4289107) B4289107
theorem B15250157 : Blo 2115435 15250157 := bstep (se 3 (by rfl) ⟨2859404, by rfl⟩ : syracuseStep 15250157 = 5718809) B5718809
theorem B10166771 : Blo 2115435 10166771 := bstep (se 1 (by rfl) ⟨7625078, by rfl⟩ : syracuseStep 10166771 = 15250157) B15250157
theorem B6777847 : Blo 2115435 6777847 := bstep (se 1 (by rfl) ⟨5083385, by rfl⟩ : syracuseStep 6777847 = 10166771) B10166771
theorem B9037129 : Blo 2115435 9037129 := bstep (se 2 (by rfl) ⟨3388923, by rfl⟩ : syracuseStep 9037129 = 6777847) B6777847
theorem B12049505 : Blo 2115435 12049505 := bstep (se 2 (by rfl) ⟨4518564, by rfl⟩ : syracuseStep 12049505 = 9037129) B9037129
theorem B8033003 : Blo 2115435 8033003 := bstep (se 1 (by rfl) ⟨6024752, by rfl⟩ : syracuseStep 8033003 = 12049505) B12049505
theorem B5355335 : Blo 2115435 5355335 := bstep (se 1 (by rfl) ⟨4016501, by rfl⟩ : syracuseStep 5355335 = 8033003) B8033003
theorem B3570223 : Blo 2115435 3570223 := bstep (se 1 (by rfl) ⟨2677667, by rfl⟩ : syracuseStep 3570223 = 5355335) B5355335
theorem B4760297 : Blo 2115435 4760297 := bstep (se 2 (by rfl) ⟨1785111, by rfl⟩ : syracuseStep 4760297 = 3570223) B3570223
theorem B3173531 : Blo 2115435 3173531 := bstep (se 1 (by rfl) ⟨2380148, by rfl⟩ : syracuseStep 3173531 = 4760297) B4760297
theorem B2115687 : Blo 2115435 2115687 := bstep (se 1 (by rfl) ⟨1586765, by rfl⟩ : syracuseStep 2115687 = 3173531) B3173531
theorem B2380153 : Blo 2115435 2380153 := bbase (se 2 (by rfl) ⟨892557, by rfl⟩ : syracuseStep 2380153 = 1785115) (by norm_num)
theorem B3173537 : Blo 2115435 3173537 := bstep (se 2 (by rfl) ⟨1190076, by rfl⟩ : syracuseStep 3173537 = 2380153) B2380153
theorem B2115691 : Blo 2115435 2115691 := bstep (se 1 (by rfl) ⟨1586768, by rfl⟩ : syracuseStep 2115691 = 3173537) B3173537
theorem B6433685 : Blo 2115435 6433685 := bbase (se 6 (by rfl) ⟨150789, by rfl⟩ : syracuseStep 6433685 = 301579) (by norm_num)
theorem B4289123 : Blo 2115435 4289123 := bstep (se 1 (by rfl) ⟨3216842, by rfl⟩ : syracuseStep 4289123 = 6433685) B6433685
theorem B11437661 : Blo 2115435 11437661 := bstep (se 3 (by rfl) ⟨2144561, by rfl⟩ : syracuseStep 11437661 = 4289123) B4289123
theorem B7625107 : Blo 2115435 7625107 := bstep (se 1 (by rfl) ⟨5718830, by rfl⟩ : syracuseStep 7625107 = 11437661) B11437661
theorem B10166809 : Blo 2115435 10166809 := bstep (se 2 (by rfl) ⟨3812553, by rfl⟩ : syracuseStep 10166809 = 7625107) B7625107
theorem B13555745 : Blo 2115435 13555745 := bstep (se 2 (by rfl) ⟨5083404, by rfl⟩ : syracuseStep 13555745 = 10166809) B10166809
theorem B9037163 : Blo 2115435 9037163 := bstep (se 1 (by rfl) ⟨6777872, by rfl⟩ : syracuseStep 9037163 = 13555745) B13555745
theorem B6024775 : Blo 2115435 6024775 := bstep (se 1 (by rfl) ⟨4518581, by rfl⟩ : syracuseStep 6024775 = 9037163) B9037163
theorem B8033033 : Blo 2115435 8033033 := bstep (se 2 (by rfl) ⟨3012387, by rfl⟩ : syracuseStep 8033033 = 6024775) B6024775
theorem B5355355 : Blo 2115435 5355355 := bstep (se 1 (by rfl) ⟨4016516, by rfl⟩ : syracuseStep 5355355 = 8033033) B8033033
theorem B7140473 : Blo 2115435 7140473 := bstep (se 2 (by rfl) ⟨2677677, by rfl⟩ : syracuseStep 7140473 = 5355355) B5355355
theorem B4760315 : Blo 2115435 4760315 := bstep (se 1 (by rfl) ⟨3570236, by rfl⟩ : syracuseStep 4760315 = 7140473) B7140473
theorem B3173543 : Blo 2115435 3173543 := bstep (se 1 (by rfl) ⟨2380157, by rfl⟩ : syracuseStep 3173543 = 4760315) B4760315
theorem B2115695 : Blo 2115435 2115695 := bstep (se 1 (by rfl) ⟨1586771, by rfl⟩ : syracuseStep 2115695 = 3173543) B3173543
theorem B3173549 : Blo 2115435 3173549 := bbase (se 3 (by rfl) ⟨595040, by rfl⟩ : syracuseStep 3173549 = 1190081) (by norm_num)
theorem B2115699 : Blo 2115435 2115699 := bstep (se 1 (by rfl) ⟨1586774, by rfl⟩ : syracuseStep 2115699 = 3173549) B3173549
theorem B4760333 : Blo 2115435 4760333 := bbase (se 3 (by rfl) ⟨892562, by rfl⟩ : syracuseStep 4760333 = 1785125) (by norm_num)
theorem B3173555 : Blo 2115435 3173555 := bstep (se 1 (by rfl) ⟨2380166, by rfl⟩ : syracuseStep 3173555 = 4760333) B4760333
theorem B2115703 : Blo 2115435 2115703 := bstep (se 1 (by rfl) ⟨1586777, by rfl⟩ : syracuseStep 2115703 = 3173555) B3173555
theorem B2677693 : Blo 2115435 2677693 := bbase (se 3 (by rfl) ⟨502067, by rfl⟩ : syracuseStep 2677693 = 1004135) (by norm_num)
theorem B3570257 : Blo 2115435 3570257 := bstep (se 2 (by rfl) ⟨1338846, by rfl⟩ : syracuseStep 3570257 = 2677693) B2677693
theorem B2380171 : Blo 2115435 2380171 := bstep (se 1 (by rfl) ⟨1785128, by rfl⟩ : syracuseStep 2380171 = 3570257) B3570257
theorem B3173561 : Blo 2115435 3173561 := bstep (se 2 (by rfl) ⟨1190085, by rfl⟩ : syracuseStep 3173561 = 2380171) B2380171
theorem B2115707 : Blo 2115435 2115707 := bstep (se 1 (by rfl) ⟨1586780, by rfl⟩ : syracuseStep 2115707 = 3173561) B3173561
theorem B10166885 : Blo 2115435 10166885 := bbase (se 4 (by rfl) ⟨953145, by rfl⟩ : syracuseStep 10166885 = 1906291) (by norm_num)
theorem B6777923 : Blo 2115435 6777923 := bstep (se 1 (by rfl) ⟨5083442, by rfl⟩ : syracuseStep 6777923 = 10166885) B10166885
theorem B18074461 : Blo 2115435 18074461 := bstep (se 3 (by rfl) ⟨3388961, by rfl⟩ : syracuseStep 18074461 = 6777923) B6777923
theorem B24099281 : Blo 2115435 24099281 := bstep (se 2 (by rfl) ⟨9037230, by rfl⟩ : syracuseStep 24099281 = 18074461) B18074461
theorem B16066187 : Blo 2115435 16066187 := bstep (se 1 (by rfl) ⟨12049640, by rfl⟩ : syracuseStep 16066187 = 24099281) B24099281
theorem B10710791 : Blo 2115435 10710791 := bstep (se 1 (by rfl) ⟨8033093, by rfl⟩ : syracuseStep 10710791 = 16066187) B16066187
theorem B7140527 : Blo 2115435 7140527 := bstep (se 1 (by rfl) ⟨5355395, by rfl⟩ : syracuseStep 7140527 = 10710791) B10710791
theorem B4760351 : Blo 2115435 4760351 := bstep (se 1 (by rfl) ⟨3570263, by rfl⟩ : syracuseStep 4760351 = 7140527) B7140527
theorem B3173567 : Blo 2115435 3173567 := bstep (se 1 (by rfl) ⟨2380175, by rfl⟩ : syracuseStep 3173567 = 4760351) B4760351
theorem B2115711 : Blo 2115435 2115711 := bstep (se 1 (by rfl) ⟨1586783, by rfl⟩ : syracuseStep 2115711 = 3173567) B3173567
theorem B3173573 : Blo 2115435 3173573 := bbase (se 4 (by rfl) ⟨297522, by rfl⟩ : syracuseStep 3173573 = 595045) (by norm_num)
theorem B2115715 : Blo 2115435 2115715 := bstep (se 1 (by rfl) ⟨1586786, by rfl⟩ : syracuseStep 2115715 = 3173573) B3173573
theorem B3570277 : Blo 2115435 3570277 := bbase (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) (by norm_num)
theorem B4760369 : Blo 2115435 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B3173579 : Blo 2115435 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B2115719 : Blo 2115435 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B2380189 : Blo 2115435 2380189 := bbase (se 3 (by rfl) ⟨446285, by rfl⟩ : syracuseStep 2380189 = 892571) (by norm_num)
theorem B3173585 : Blo 2115435 3173585 := bstep (se 2 (by rfl) ⟨1190094, by rfl⟩ : syracuseStep 3173585 = 2380189) B2380189
theorem B2115723 : Blo 2115435 2115723 := bstep (se 1 (by rfl) ⟨1586792, by rfl⟩ : syracuseStep 2115723 = 3173585) B3173585
theorem B7140581 : Blo 2115435 7140581 := bbase (se 4 (by rfl) ⟨669429, by rfl⟩ : syracuseStep 7140581 = 1338859) (by norm_num)
theorem B4760387 : Blo 2115435 4760387 := bstep (se 1 (by rfl) ⟨3570290, by rfl⟩ : syracuseStep 4760387 = 7140581) B7140581
theorem B3173591 : Blo 2115435 3173591 := bstep (se 1 (by rfl) ⟨2380193, by rfl⟩ : syracuseStep 3173591 = 4760387) B4760387
theorem B2115727 : Blo 2115435 2115727 := bstep (se 1 (by rfl) ⟨1586795, by rfl⟩ : syracuseStep 2115727 = 3173591) B3173591
theorem B3173597 : Blo 2115435 3173597 := bbase (se 3 (by rfl) ⟨595049, by rfl⟩ : syracuseStep 3173597 = 1190099) (by norm_num)
theorem B2115731 : Blo 2115435 2115731 := bstep (se 1 (by rfl) ⟨1586798, by rfl⟩ : syracuseStep 2115731 = 3173597) B3173597
theorem B4760405 : Blo 2115435 4760405 := bbase (se 9 (by rfl) ⟨13946, by rfl⟩ : syracuseStep 4760405 = 27893) (by norm_num)
theorem B3173603 : Blo 2115435 3173603 := bstep (se 1 (by rfl) ⟨2380202, by rfl⟩ : syracuseStep 3173603 = 4760405) B4760405
theorem B2115735 : Blo 2115435 2115735 := bstep (se 1 (by rfl) ⟨1586801, by rfl⟩ : syracuseStep 2115735 = 3173603) B3173603
theorem B6024901 : Blo 2115435 6024901 := bbase (se 4 (by rfl) ⟨564834, by rfl⟩ : syracuseStep 6024901 = 1129669) (by norm_num)
theorem B8033201 : Blo 2115435 8033201 := bstep (se 2 (by rfl) ⟨3012450, by rfl⟩ : syracuseStep 8033201 = 6024901) B6024901
theorem B5355467 : Blo 2115435 5355467 := bstep (se 1 (by rfl) ⟨4016600, by rfl⟩ : syracuseStep 5355467 = 8033201) B8033201
theorem B3570311 : Blo 2115435 3570311 := bstep (se 1 (by rfl) ⟨2677733, by rfl⟩ : syracuseStep 3570311 = 5355467) B5355467
theorem B2380207 : Blo 2115435 2380207 := bstep (se 1 (by rfl) ⟨1785155, by rfl⟩ : syracuseStep 2380207 = 3570311) B3570311
theorem B3173609 : Blo 2115435 3173609 := bstep (se 2 (by rfl) ⟨1190103, by rfl⟩ : syracuseStep 3173609 = 2380207) B2380207
theorem B2115739 : Blo 2115435 2115739 := bstep (se 1 (by rfl) ⟨1586804, by rfl⟩ : syracuseStep 2115739 = 3173609) B3173609
theorem B2203529 : Blo 2115435 2203529 := bbase (se 2 (by rfl) ⟨826323, by rfl⟩ : syracuseStep 2203529 = 1652647) (by norm_num)
theorem B5876077 : Blo 2115435 5876077 := bstep (se 3 (by rfl) ⟨1101764, by rfl⟩ : syracuseStep 5876077 = 2203529) B2203529
theorem B7834769 : Blo 2115435 7834769 := bstep (se 2 (by rfl) ⟨2938038, by rfl⟩ : syracuseStep 7834769 = 5876077) B5876077
theorem B5223179 : Blo 2115435 5223179 := bstep (se 1 (by rfl) ⟨3917384, by rfl⟩ : syracuseStep 5223179 = 7834769) B7834769
theorem B3482119 : Blo 2115435 3482119 := bstep (se 1 (by rfl) ⟨2611589, by rfl⟩ : syracuseStep 3482119 = 5223179) B5223179
theorem B18571301 : Blo 2115435 18571301 := bstep (se 4 (by rfl) ⟨1741059, by rfl⟩ : syracuseStep 18571301 = 3482119) B3482119
theorem B12380867 : Blo 2115435 12380867 := bstep (se 1 (by rfl) ⟨9285650, by rfl⟩ : syracuseStep 12380867 = 18571301) B18571301
theorem B8253911 : Blo 2115435 8253911 := bstep (se 1 (by rfl) ⟨6190433, by rfl⟩ : syracuseStep 8253911 = 12380867) B12380867
theorem B22010429 : Blo 2115435 22010429 := bstep (se 3 (by rfl) ⟨4126955, by rfl⟩ : syracuseStep 22010429 = 8253911) B8253911
theorem B14673619 : Blo 2115435 14673619 := bstep (se 1 (by rfl) ⟨11005214, by rfl⟩ : syracuseStep 14673619 = 22010429) B22010429
theorem B78259301 : Blo 2115435 78259301 := bstep (se 4 (by rfl) ⟨7336809, by rfl⟩ : syracuseStep 78259301 = 14673619) B14673619
theorem B52172867 : Blo 2115435 52172867 := bstep (se 1 (by rfl) ⟨39129650, by rfl⟩ : syracuseStep 52172867 = 78259301) B78259301
theorem B139127645 : Blo 2115435 139127645 := bstep (se 3 (by rfl) ⟨26086433, by rfl⟩ : syracuseStep 139127645 = 52172867) B52172867
theorem B92751763 : Blo 2115435 92751763 := bstep (se 1 (by rfl) ⟨69563822, by rfl⟩ : syracuseStep 92751763 = 139127645) B139127645
theorem B123669017 : Blo 2115435 123669017 := bstep (se 2 (by rfl) ⟨46375881, by rfl⟩ : syracuseStep 123669017 = 92751763) B92751763
theorem B82446011 : Blo 2115435 82446011 := bstep (se 1 (by rfl) ⟨61834508, by rfl⟩ : syracuseStep 82446011 = 123669017) B123669017
theorem B54964007 : Blo 2115435 54964007 := bstep (se 1 (by rfl) ⟨41223005, by rfl⟩ : syracuseStep 54964007 = 82446011) B82446011
theorem B36642671 : Blo 2115435 36642671 := bstep (se 1 (by rfl) ⟨27482003, by rfl⟩ : syracuseStep 36642671 = 54964007) B54964007
theorem B24428447 : Blo 2115435 24428447 := bstep (se 1 (by rfl) ⟨18321335, by rfl⟩ : syracuseStep 24428447 = 36642671) B36642671
theorem B16285631 : Blo 2115435 16285631 := bstep (se 1 (by rfl) ⟨12214223, by rfl⟩ : syracuseStep 16285631 = 24428447) B24428447
theorem B43428349 : Blo 2115435 43428349 := bstep (se 3 (by rfl) ⟨8142815, by rfl⟩ : syracuseStep 43428349 = 16285631) B16285631
theorem B57904465 : Blo 2115435 57904465 := bstep (se 2 (by rfl) ⟨21714174, by rfl⟩ : syracuseStep 57904465 = 43428349) B43428349
theorem B77205953 : Blo 2115435 77205953 := bstep (se 2 (by rfl) ⟨28952232, by rfl⟩ : syracuseStep 77205953 = 57904465) B57904465
theorem B51470635 : Blo 2115435 51470635 := bstep (se 1 (by rfl) ⟨38602976, by rfl⟩ : syracuseStep 51470635 = 77205953) B77205953
theorem B68627513 : Blo 2115435 68627513 := bstep (se 2 (by rfl) ⟨25735317, by rfl⟩ : syracuseStep 68627513 = 51470635) B51470635
theorem B45751675 : Blo 2115435 45751675 := bstep (se 1 (by rfl) ⟨34313756, by rfl⟩ : syracuseStep 45751675 = 68627513) B68627513
theorem B61002233 : Blo 2115435 61002233 := bstep (se 2 (by rfl) ⟨22875837, by rfl⟩ : syracuseStep 61002233 = 45751675) B45751675
theorem B40668155 : Blo 2115435 40668155 := bstep (se 1 (by rfl) ⟨30501116, by rfl⟩ : syracuseStep 40668155 = 61002233) B61002233
theorem B27112103 : Blo 2115435 27112103 := bstep (se 1 (by rfl) ⟨20334077, by rfl⟩ : syracuseStep 27112103 = 40668155) B40668155
theorem B18074735 : Blo 2115435 18074735 := bstep (se 1 (by rfl) ⟨13556051, by rfl⟩ : syracuseStep 18074735 = 27112103) B27112103
theorem B12049823 : Blo 2115435 12049823 := bstep (se 1 (by rfl) ⟨9037367, by rfl⟩ : syracuseStep 12049823 = 18074735) B18074735
theorem B8033215 : Blo 2115435 8033215 := bstep (se 1 (by rfl) ⟨6024911, by rfl⟩ : syracuseStep 8033215 = 12049823) B12049823
theorem B10710953 : Blo 2115435 10710953 := bstep (se 2 (by rfl) ⟨4016607, by rfl⟩ : syracuseStep 10710953 = 8033215) B8033215
theorem B7140635 : Blo 2115435 7140635 := bstep (se 1 (by rfl) ⟨5355476, by rfl⟩ : syracuseStep 7140635 = 10710953) B10710953
theorem B4760423 : Blo 2115435 4760423 := bstep (se 1 (by rfl) ⟨3570317, by rfl⟩ : syracuseStep 4760423 = 7140635) B7140635
theorem B3173615 : Blo 2115435 3173615 := bstep (se 1 (by rfl) ⟨2380211, by rfl⟩ : syracuseStep 3173615 = 4760423) B4760423
theorem B2115743 : Blo 2115435 2115743 := bstep (se 1 (by rfl) ⟨1586807, by rfl⟩ : syracuseStep 2115743 = 3173615) B3173615
theorem B3173621 : Blo 2115435 3173621 := bbase (se 5 (by rfl) ⟨148763, by rfl⟩ : syracuseStep 3173621 = 297527) (by norm_num)
theorem B2115747 : Blo 2115435 2115747 := bstep (se 1 (by rfl) ⟨1586810, by rfl⟩ : syracuseStep 2115747 = 3173621) B3173621
theorem B4891229 : Blo 2115435 4891229 := bbase (se 3 (by rfl) ⟨917105, by rfl⟩ : syracuseStep 4891229 = 1834211) (by norm_num)
theorem B3260819 : Blo 2115435 3260819 := bstep (se 1 (by rfl) ⟨2445614, by rfl⟩ : syracuseStep 3260819 = 4891229) B4891229
theorem B2173879 : Blo 2115435 2173879 := bstep (se 1 (by rfl) ⟨1630409, by rfl⟩ : syracuseStep 2173879 = 3260819) B3260819
theorem B2898505 : Blo 2115435 2898505 := bstep (se 2 (by rfl) ⟨1086939, by rfl⟩ : syracuseStep 2898505 = 2173879) B2173879
theorem B3864673 : Blo 2115435 3864673 := bstep (se 2 (by rfl) ⟨1449252, by rfl⟩ : syracuseStep 3864673 = 2898505) B2898505
theorem B5152897 : Blo 2115435 5152897 := bstep (se 2 (by rfl) ⟨1932336, by rfl⟩ : syracuseStep 5152897 = 3864673) B3864673
theorem B6870529 : Blo 2115435 6870529 := bstep (se 2 (by rfl) ⟨2576448, by rfl⟩ : syracuseStep 6870529 = 5152897) B5152897
theorem B9160705 : Blo 2115435 9160705 := bstep (se 2 (by rfl) ⟨3435264, by rfl⟩ : syracuseStep 9160705 = 6870529) B6870529
theorem B48857093 : Blo 2115435 48857093 := bstep (se 4 (by rfl) ⟨4580352, by rfl⟩ : syracuseStep 48857093 = 9160705) B9160705
theorem B32571395 : Blo 2115435 32571395 := bstep (se 1 (by rfl) ⟨24428546, by rfl⟩ : syracuseStep 32571395 = 48857093) B48857093
theorem B21714263 : Blo 2115435 21714263 := bstep (se 1 (by rfl) ⟨16285697, by rfl⟩ : syracuseStep 21714263 = 32571395) B32571395
theorem B14476175 : Blo 2115435 14476175 := bstep (se 1 (by rfl) ⟨10857131, by rfl⟩ : syracuseStep 14476175 = 21714263) B21714263
theorem B9650783 : Blo 2115435 9650783 := bstep (se 1 (by rfl) ⟨7238087, by rfl⟩ : syracuseStep 9650783 = 14476175) B14476175
theorem B25735421 : Blo 2115435 25735421 := bstep (se 3 (by rfl) ⟨4825391, by rfl⟩ : syracuseStep 25735421 = 9650783) B9650783
theorem B17156947 : Blo 2115435 17156947 := bstep (se 1 (by rfl) ⟨12867710, by rfl⟩ : syracuseStep 17156947 = 25735421) B25735421
theorem B22875929 : Blo 2115435 22875929 := bstep (se 2 (by rfl) ⟨8578473, by rfl⟩ : syracuseStep 22875929 = 17156947) B17156947
theorem B15250619 : Blo 2115435 15250619 := bstep (se 1 (by rfl) ⟨11437964, by rfl⟩ : syracuseStep 15250619 = 22875929) B22875929
theorem B10167079 : Blo 2115435 10167079 := bstep (se 1 (by rfl) ⟨7625309, by rfl⟩ : syracuseStep 10167079 = 15250619) B15250619
theorem B13556105 : Blo 2115435 13556105 := bstep (se 2 (by rfl) ⟨5083539, by rfl⟩ : syracuseStep 13556105 = 10167079) B10167079
theorem B9037403 : Blo 2115435 9037403 := bstep (se 1 (by rfl) ⟨6778052, by rfl⟩ : syracuseStep 9037403 = 13556105) B13556105
theorem B6024935 : Blo 2115435 6024935 := bstep (se 1 (by rfl) ⟨4518701, by rfl⟩ : syracuseStep 6024935 = 9037403) B9037403
theorem B4016623 : Blo 2115435 4016623 := bstep (se 1 (by rfl) ⟨3012467, by rfl⟩ : syracuseStep 4016623 = 6024935) B6024935
theorem B5355497 : Blo 2115435 5355497 := bstep (se 2 (by rfl) ⟨2008311, by rfl⟩ : syracuseStep 5355497 = 4016623) B4016623
theorem B3570331 : Blo 2115435 3570331 := bstep (se 1 (by rfl) ⟨2677748, by rfl⟩ : syracuseStep 3570331 = 5355497) B5355497
theorem B4760441 : Blo 2115435 4760441 := bstep (se 2 (by rfl) ⟨1785165, by rfl⟩ : syracuseStep 4760441 = 3570331) B3570331
theorem B3173627 : Blo 2115435 3173627 := bstep (se 1 (by rfl) ⟨2380220, by rfl⟩ : syracuseStep 3173627 = 4760441) B4760441
theorem B2115751 : Blo 2115435 2115751 := bstep (se 1 (by rfl) ⟨1586813, by rfl⟩ : syracuseStep 2115751 = 3173627) B3173627
theorem B2380225 : Blo 2115435 2380225 := bbase (se 2 (by rfl) ⟨892584, by rfl⟩ : syracuseStep 2380225 = 1785169) (by norm_num)
theorem B3173633 : Blo 2115435 3173633 := bstep (se 2 (by rfl) ⟨1190112, by rfl⟩ : syracuseStep 3173633 = 2380225) B2380225
theorem B2115755 : Blo 2115435 2115755 := bstep (se 1 (by rfl) ⟨1586816, by rfl⟩ : syracuseStep 2115755 = 3173633) B3173633
theorem B5355517 : Blo 2115435 5355517 := bbase (se 3 (by rfl) ⟨1004159, by rfl⟩ : syracuseStep 5355517 = 2008319) (by norm_num)
theorem B7140689 : Blo 2115435 7140689 := bstep (se 2 (by rfl) ⟨2677758, by rfl⟩ : syracuseStep 7140689 = 5355517) B5355517
theorem B4760459 : Blo 2115435 4760459 := bstep (se 1 (by rfl) ⟨3570344, by rfl⟩ : syracuseStep 4760459 = 7140689) B7140689
theorem B3173639 : Blo 2115435 3173639 := bstep (se 1 (by rfl) ⟨2380229, by rfl⟩ : syracuseStep 3173639 = 4760459) B4760459
theorem B2115759 : Blo 2115435 2115759 := bstep (se 1 (by rfl) ⟨1586819, by rfl⟩ : syracuseStep 2115759 = 3173639) B3173639
theorem B3173645 : Blo 2115435 3173645 := bbase (se 3 (by rfl) ⟨595058, by rfl⟩ : syracuseStep 3173645 = 1190117) (by norm_num)
theorem B2115763 : Blo 2115435 2115763 := bstep (se 1 (by rfl) ⟨1586822, by rfl⟩ : syracuseStep 2115763 = 3173645) B3173645
theorem B4760477 : Blo 2115435 4760477 := bbase (se 3 (by rfl) ⟨892589, by rfl⟩ : syracuseStep 4760477 = 1785179) (by norm_num)
theorem B3173651 : Blo 2115435 3173651 := bstep (se 1 (by rfl) ⟨2380238, by rfl⟩ : syracuseStep 3173651 = 4760477) B4760477
theorem B2115767 : Blo 2115435 2115767 := bstep (se 1 (by rfl) ⟨1586825, by rfl⟩ : syracuseStep 2115767 = 3173651) B3173651
theorem B3570365 : Blo 2115435 3570365 := bbase (se 3 (by rfl) ⟨669443, by rfl⟩ : syracuseStep 3570365 = 1338887) (by norm_num)
theorem B2380243 : Blo 2115435 2380243 := bstep (se 1 (by rfl) ⟨1785182, by rfl⟩ : syracuseStep 2380243 = 3570365) B3570365
theorem B3173657 : Blo 2115435 3173657 := bstep (se 2 (by rfl) ⟨1190121, by rfl⟩ : syracuseStep 3173657 = 2380243) B2380243
theorem B2115771 : Blo 2115435 2115771 := bstep (se 1 (by rfl) ⟨1586828, by rfl⟩ : syracuseStep 2115771 = 3173657) B3173657
theorem B12050005 : Blo 2115435 12050005 := bbase (se 8 (by rfl) ⟨70605, by rfl⟩ : syracuseStep 12050005 = 141211) (by norm_num)
theorem B16066673 : Blo 2115435 16066673 := bstep (se 2 (by rfl) ⟨6025002, by rfl⟩ : syracuseStep 16066673 = 12050005) B12050005
theorem B10711115 : Blo 2115435 10711115 := bstep (se 1 (by rfl) ⟨8033336, by rfl⟩ : syracuseStep 10711115 = 16066673) B16066673
theorem B7140743 : Blo 2115435 7140743 := bstep (se 1 (by rfl) ⟨5355557, by rfl⟩ : syracuseStep 7140743 = 10711115) B10711115
theorem B4760495 : Blo 2115435 4760495 := bstep (se 1 (by rfl) ⟨3570371, by rfl⟩ : syracuseStep 4760495 = 7140743) B7140743
theorem B3173663 : Blo 2115435 3173663 := bstep (se 1 (by rfl) ⟨2380247, by rfl⟩ : syracuseStep 3173663 = 4760495) B4760495
theorem B2115775 : Blo 2115435 2115775 := bstep (se 1 (by rfl) ⟨1586831, by rfl⟩ : syracuseStep 2115775 = 3173663) B3173663
theorem B3173669 : Blo 2115435 3173669 := bbase (se 4 (by rfl) ⟨297531, by rfl⟩ : syracuseStep 3173669 = 595063) (by norm_num)
theorem B2115779 : Blo 2115435 2115779 := bstep (se 1 (by rfl) ⟨1586834, by rfl⟩ : syracuseStep 2115779 = 3173669) B3173669
theorem B2677789 : Blo 2115435 2677789 := bbase (se 3 (by rfl) ⟨502085, by rfl⟩ : syracuseStep 2677789 = 1004171) (by norm_num)
theorem B3570385 : Blo 2115435 3570385 := bstep (se 2 (by rfl) ⟨1338894, by rfl⟩ : syracuseStep 3570385 = 2677789) B2677789
theorem B4760513 : Blo 2115435 4760513 := bstep (se 2 (by rfl) ⟨1785192, by rfl⟩ : syracuseStep 4760513 = 3570385) B3570385
theorem B3173675 : Blo 2115435 3173675 := bstep (se 1 (by rfl) ⟨2380256, by rfl⟩ : syracuseStep 3173675 = 4760513) B4760513
theorem B2115783 : Blo 2115435 2115783 := bstep (se 1 (by rfl) ⟨1586837, by rfl⟩ : syracuseStep 2115783 = 3173675) B3173675
theorem B2380261 : Blo 2115435 2380261 := bbase (se 4 (by rfl) ⟨223149, by rfl⟩ : syracuseStep 2380261 = 446299) (by norm_num)
theorem B3173681 : Blo 2115435 3173681 := bstep (se 2 (by rfl) ⟨1190130, by rfl⟩ : syracuseStep 3173681 = 2380261) B2380261
theorem B2115787 : Blo 2115435 2115787 := bstep (se 1 (by rfl) ⟨1586840, by rfl⟩ : syracuseStep 2115787 = 3173681) B3173681
theorem B6778181 : Blo 2115435 6778181 := bbase (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) (by norm_num)
theorem B4518787 : Blo 2115435 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B6025049 : Blo 2115435 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B4016699 : Blo 2115435 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B2677799 : Blo 2115435 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B7140797 : Blo 2115435 7140797 := bstep (se 3 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 7140797 = 2677799) B2677799
theorem B4760531 : Blo 2115435 4760531 := bstep (se 1 (by rfl) ⟨3570398, by rfl⟩ : syracuseStep 4760531 = 7140797) B7140797
theorem B3173687 : Blo 2115435 3173687 := bstep (se 1 (by rfl) ⟨2380265, by rfl⟩ : syracuseStep 3173687 = 4760531) B4760531
theorem B2115791 : Blo 2115435 2115791 := bstep (se 1 (by rfl) ⟨1586843, by rfl⟩ : syracuseStep 2115791 = 3173687) B3173687
theorem B3173693 : Blo 2115435 3173693 := bbase (se 3 (by rfl) ⟨595067, by rfl⟩ : syracuseStep 3173693 = 1190135) (by norm_num)
theorem B2115795 : Blo 2115435 2115795 := bstep (se 1 (by rfl) ⟨1586846, by rfl⟩ : syracuseStep 2115795 = 3173693) B3173693
theorem B4760549 : Blo 2115435 4760549 := bbase (se 4 (by rfl) ⟨446301, by rfl⟩ : syracuseStep 4760549 = 892603) (by norm_num)
theorem B3173699 : Blo 2115435 3173699 := bstep (se 1 (by rfl) ⟨2380274, by rfl⟩ : syracuseStep 3173699 = 4760549) B4760549
theorem B2115799 : Blo 2115435 2115799 := bstep (se 1 (by rfl) ⟨1586849, by rfl⟩ : syracuseStep 2115799 = 3173699) B3173699
theorem B5355629 : Blo 2115435 5355629 := bbase (se 3 (by rfl) ⟨1004180, by rfl⟩ : syracuseStep 5355629 = 2008361) (by norm_num)
theorem B3570419 : Blo 2115435 3570419 := bstep (se 1 (by rfl) ⟨2677814, by rfl⟩ : syracuseStep 3570419 = 5355629) B5355629
theorem B2380279 : Blo 2115435 2380279 := bstep (se 1 (by rfl) ⟨1785209, by rfl⟩ : syracuseStep 2380279 = 3570419) B3570419
theorem B3173705 : Blo 2115435 3173705 := bstep (se 2 (by rfl) ⟨1190139, by rfl⟩ : syracuseStep 3173705 = 2380279) B2380279
theorem B2115803 : Blo 2115435 2115803 := bstep (se 1 (by rfl) ⟨1586852, by rfl⟩ : syracuseStep 2115803 = 3173705) B3173705
theorem B4518821 : Blo 2115435 4518821 := bbase (se 4 (by rfl) ⟨423639, by rfl⟩ : syracuseStep 4518821 = 847279) (by norm_num)
theorem B3012547 : Blo 2115435 3012547 := bstep (se 1 (by rfl) ⟨2259410, by rfl⟩ : syracuseStep 3012547 = 4518821) B4518821
theorem B4016729 : Blo 2115435 4016729 := bstep (se 2 (by rfl) ⟨1506273, by rfl⟩ : syracuseStep 4016729 = 3012547) B3012547
theorem B10711277 : Blo 2115435 10711277 := bstep (se 3 (by rfl) ⟨2008364, by rfl⟩ : syracuseStep 10711277 = 4016729) B4016729
theorem B7140851 : Blo 2115435 7140851 := bstep (se 1 (by rfl) ⟨5355638, by rfl⟩ : syracuseStep 7140851 = 10711277) B10711277
theorem B4760567 : Blo 2115435 4760567 := bstep (se 1 (by rfl) ⟨3570425, by rfl⟩ : syracuseStep 4760567 = 7140851) B7140851
theorem B3173711 : Blo 2115435 3173711 := bstep (se 1 (by rfl) ⟨2380283, by rfl⟩ : syracuseStep 3173711 = 4760567) B4760567
theorem B2115807 : Blo 2115435 2115807 := bstep (se 1 (by rfl) ⟨1586855, by rfl⟩ : syracuseStep 2115807 = 3173711) B3173711
theorem B3173717 : Blo 2115435 3173717 := bbase (se 11 (by rfl) ⟨2324, by rfl⟩ : syracuseStep 3173717 = 4649) (by norm_num)
theorem B2115811 : Blo 2115435 2115811 := bstep (se 1 (by rfl) ⟨1586858, by rfl⟩ : syracuseStep 2115811 = 3173717) B3173717
theorem B5719157 : Blo 2115435 5719157 := bbase (se 5 (by rfl) ⟨268085, by rfl⟩ : syracuseStep 5719157 = 536171) (by norm_num)
theorem B3812771 : Blo 2115435 3812771 := bstep (se 1 (by rfl) ⟨2859578, by rfl⟩ : syracuseStep 3812771 = 5719157) B5719157
theorem B2541847 : Blo 2115435 2541847 := bstep (se 1 (by rfl) ⟨1906385, by rfl⟩ : syracuseStep 2541847 = 3812771) B3812771
theorem B3389129 : Blo 2115435 3389129 := bstep (se 2 (by rfl) ⟨1270923, by rfl⟩ : syracuseStep 3389129 = 2541847) B2541847
theorem B2259419 : Blo 2115435 2259419 := bstep (se 1 (by rfl) ⟨1694564, by rfl⟩ : syracuseStep 2259419 = 3389129) B3389129
theorem B6025117 : Blo 2115435 6025117 := bstep (se 3 (by rfl) ⟨1129709, by rfl⟩ : syracuseStep 6025117 = 2259419) B2259419
theorem B8033489 : Blo 2115435 8033489 := bstep (se 2 (by rfl) ⟨3012558, by rfl⟩ : syracuseStep 8033489 = 6025117) B6025117
theorem B5355659 : Blo 2115435 5355659 := bstep (se 1 (by rfl) ⟨4016744, by rfl⟩ : syracuseStep 5355659 = 8033489) B8033489
theorem B3570439 : Blo 2115435 3570439 := bstep (se 1 (by rfl) ⟨2677829, by rfl⟩ : syracuseStep 3570439 = 5355659) B5355659
theorem B4760585 : Blo 2115435 4760585 := bstep (se 2 (by rfl) ⟨1785219, by rfl⟩ : syracuseStep 4760585 = 3570439) B3570439
theorem B3173723 : Blo 2115435 3173723 := bstep (se 1 (by rfl) ⟨2380292, by rfl⟩ : syracuseStep 3173723 = 4760585) B4760585
theorem B2115815 : Blo 2115435 2115815 := bstep (se 1 (by rfl) ⟨1586861, by rfl⟩ : syracuseStep 2115815 = 3173723) B3173723
theorem B2380297 : Blo 2115435 2380297 := bbase (se 2 (by rfl) ⟨892611, by rfl⟩ : syracuseStep 2380297 = 1785223) (by norm_num)
theorem B3173729 : Blo 2115435 3173729 := bstep (se 2 (by rfl) ⟨1190148, by rfl⟩ : syracuseStep 3173729 = 2380297) B2380297
theorem B2115819 : Blo 2115435 2115819 := bstep (se 1 (by rfl) ⟨1586864, by rfl⟩ : syracuseStep 2115819 = 3173729) B3173729
theorem B5797205 : Blo 2115435 5797205 := bbase (se 13 (by rfl) ⟨1061, by rfl⟩ : syracuseStep 5797205 = 2123) (by norm_num)
theorem B3864803 : Blo 2115435 3864803 := bstep (se 1 (by rfl) ⟨2898602, by rfl⟩ : syracuseStep 3864803 = 5797205) B5797205
theorem B41224565 : Blo 2115435 41224565 := bstep (se 5 (by rfl) ⟨1932401, by rfl⟩ : syracuseStep 41224565 = 3864803) B3864803
theorem B27483043 : Blo 2115435 27483043 := bstep (se 1 (by rfl) ⟨20612282, by rfl⟩ : syracuseStep 27483043 = 41224565) B41224565
theorem B36644057 : Blo 2115435 36644057 := bstep (se 2 (by rfl) ⟨13741521, by rfl⟩ : syracuseStep 36644057 = 27483043) B27483043
theorem B24429371 : Blo 2115435 24429371 := bstep (se 1 (by rfl) ⟨18322028, by rfl⟩ : syracuseStep 24429371 = 36644057) B36644057
theorem B65144989 : Blo 2115435 65144989 := bstep (se 3 (by rfl) ⟨12214685, by rfl⟩ : syracuseStep 65144989 = 24429371) B24429371
theorem B347439941 : Blo 2115435 347439941 := bstep (se 4 (by rfl) ⟨32572494, by rfl⟩ : syracuseStep 347439941 = 65144989) B65144989
theorem B231626627 : Blo 2115435 231626627 := bstep (se 1 (by rfl) ⟨173719970, by rfl⟩ : syracuseStep 231626627 = 347439941) B347439941
theorem B154417751 : Blo 2115435 154417751 := bstep (se 1 (by rfl) ⟨115813313, by rfl⟩ : syracuseStep 154417751 = 231626627) B231626627
theorem B102945167 : Blo 2115435 102945167 := bstep (se 1 (by rfl) ⟨77208875, by rfl⟩ : syracuseStep 102945167 = 154417751) B154417751
theorem B68630111 : Blo 2115435 68630111 := bstep (se 1 (by rfl) ⟨51472583, by rfl⟩ : syracuseStep 68630111 = 102945167) B102945167
theorem B45753407 : Blo 2115435 45753407 := bstep (se 1 (by rfl) ⟨34315055, by rfl⟩ : syracuseStep 45753407 = 68630111) B68630111
theorem B30502271 : Blo 2115435 30502271 := bstep (se 1 (by rfl) ⟨22876703, by rfl⟩ : syracuseStep 30502271 = 45753407) B45753407
theorem B20334847 : Blo 2115435 20334847 := bstep (se 1 (by rfl) ⟨15251135, by rfl⟩ : syracuseStep 20334847 = 30502271) B30502271
theorem B27113129 : Blo 2115435 27113129 := bstep (se 2 (by rfl) ⟨10167423, by rfl⟩ : syracuseStep 27113129 = 20334847) B20334847
theorem B18075419 : Blo 2115435 18075419 := bstep (se 1 (by rfl) ⟨13556564, by rfl⟩ : syracuseStep 18075419 = 27113129) B27113129
theorem B12050279 : Blo 2115435 12050279 := bstep (se 1 (by rfl) ⟨9037709, by rfl⟩ : syracuseStep 12050279 = 18075419) B18075419
theorem B8033519 : Blo 2115435 8033519 := bstep (se 1 (by rfl) ⟨6025139, by rfl⟩ : syracuseStep 8033519 = 12050279) B12050279
theorem B5355679 : Blo 2115435 5355679 := bstep (se 1 (by rfl) ⟨4016759, by rfl⟩ : syracuseStep 5355679 = 8033519) B8033519
theorem B7140905 : Blo 2115435 7140905 := bstep (se 2 (by rfl) ⟨2677839, by rfl⟩ : syracuseStep 7140905 = 5355679) B5355679
theorem B4760603 : Blo 2115435 4760603 := bstep (se 1 (by rfl) ⟨3570452, by rfl⟩ : syracuseStep 4760603 = 7140905) B7140905
theorem B3173735 : Blo 2115435 3173735 := bstep (se 1 (by rfl) ⟨2380301, by rfl⟩ : syracuseStep 3173735 = 4760603) B4760603
theorem B2115823 : Blo 2115435 2115823 := bstep (se 1 (by rfl) ⟨1586867, by rfl⟩ : syracuseStep 2115823 = 3173735) B3173735
theorem B3173741 : Blo 2115435 3173741 := bbase (se 3 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 3173741 = 1190153) (by norm_num)
theorem B2115827 : Blo 2115435 2115827 := bstep (se 1 (by rfl) ⟨1586870, by rfl⟩ : syracuseStep 2115827 = 3173741) B3173741
theorem B4760621 : Blo 2115435 4760621 := bbase (se 3 (by rfl) ⟨892616, by rfl⟩ : syracuseStep 4760621 = 1785233) (by norm_num)
theorem B3173747 : Blo 2115435 3173747 := bstep (se 1 (by rfl) ⟨2380310, by rfl⟩ : syracuseStep 3173747 = 4760621) B4760621
theorem B2115831 : Blo 2115435 2115831 := bstep (se 1 (by rfl) ⟨1586873, by rfl⟩ : syracuseStep 2115831 = 3173747) B3173747
theorem B3619189 : Blo 2115435 3619189 := bbase (se 5 (by rfl) ⟨169649, by rfl⟩ : syracuseStep 3619189 = 339299) (by norm_num)
theorem B4825585 : Blo 2115435 4825585 := bstep (se 2 (by rfl) ⟨1809594, by rfl⟩ : syracuseStep 4825585 = 3619189) B3619189
theorem B6434113 : Blo 2115435 6434113 := bstep (se 2 (by rfl) ⟨2412792, by rfl⟩ : syracuseStep 6434113 = 4825585) B4825585
theorem B8578817 : Blo 2115435 8578817 := bstep (se 2 (by rfl) ⟨3217056, by rfl⟩ : syracuseStep 8578817 = 6434113) B6434113
theorem B5719211 : Blo 2115435 5719211 := bstep (se 1 (by rfl) ⟨4289408, by rfl⟩ : syracuseStep 5719211 = 8578817) B8578817
theorem B3812807 : Blo 2115435 3812807 := bstep (se 1 (by rfl) ⟨2859605, by rfl⟩ : syracuseStep 3812807 = 5719211) B5719211
theorem B2541871 : Blo 2115435 2541871 := bstep (se 1 (by rfl) ⟨1906403, by rfl⟩ : syracuseStep 2541871 = 3812807) B3812807
theorem B13556645 : Blo 2115435 13556645 := bstep (se 4 (by rfl) ⟨1270935, by rfl⟩ : syracuseStep 13556645 = 2541871) B2541871
theorem B9037763 : Blo 2115435 9037763 := bstep (se 1 (by rfl) ⟨6778322, by rfl⟩ : syracuseStep 9037763 = 13556645) B13556645
theorem B6025175 : Blo 2115435 6025175 := bstep (se 1 (by rfl) ⟨4518881, by rfl⟩ : syracuseStep 6025175 = 9037763) B9037763
theorem B4016783 : Blo 2115435 4016783 := bstep (se 1 (by rfl) ⟨3012587, by rfl⟩ : syracuseStep 4016783 = 6025175) B6025175
theorem B2677855 : Blo 2115435 2677855 := bstep (se 1 (by rfl) ⟨2008391, by rfl⟩ : syracuseStep 2677855 = 4016783) B4016783
theorem B3570473 : Blo 2115435 3570473 := bstep (se 2 (by rfl) ⟨1338927, by rfl⟩ : syracuseStep 3570473 = 2677855) B2677855
theorem B2380315 : Blo 2115435 2380315 := bstep (se 1 (by rfl) ⟨1785236, by rfl⟩ : syracuseStep 2380315 = 3570473) B3570473
theorem B3173753 : Blo 2115435 3173753 := bstep (se 2 (by rfl) ⟨1190157, by rfl⟩ : syracuseStep 3173753 = 2380315) B2380315
theorem B2115835 : Blo 2115435 2115835 := bstep (se 1 (by rfl) ⟨1586876, by rfl⟩ : syracuseStep 2115835 = 3173753) B3173753
theorem B3812813 : Blo 2115435 3812813 := bbase (se 3 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 3812813 = 1429805) (by norm_num)
theorem B2541875 : Blo 2115435 2541875 := bstep (se 1 (by rfl) ⟨1906406, by rfl⟩ : syracuseStep 2541875 = 3812813) B3812813
theorem B6778333 : Blo 2115435 6778333 := bstep (se 3 (by rfl) ⟨1270937, by rfl⟩ : syracuseStep 6778333 = 2541875) B2541875
theorem B36151109 : Blo 2115435 36151109 := bstep (se 4 (by rfl) ⟨3389166, by rfl⟩ : syracuseStep 36151109 = 6778333) B6778333
theorem B24100739 : Blo 2115435 24100739 := bstep (se 1 (by rfl) ⟨18075554, by rfl⟩ : syracuseStep 24100739 = 36151109) B36151109
theorem B16067159 : Blo 2115435 16067159 := bstep (se 1 (by rfl) ⟨12050369, by rfl⟩ : syracuseStep 16067159 = 24100739) B24100739
theorem B10711439 : Blo 2115435 10711439 := bstep (se 1 (by rfl) ⟨8033579, by rfl⟩ : syracuseStep 10711439 = 16067159) B16067159
theorem B7140959 : Blo 2115435 7140959 := bstep (se 1 (by rfl) ⟨5355719, by rfl⟩ : syracuseStep 7140959 = 10711439) B10711439
theorem B4760639 : Blo 2115435 4760639 := bstep (se 1 (by rfl) ⟨3570479, by rfl⟩ : syracuseStep 4760639 = 7140959) B7140959
theorem B3173759 : Blo 2115435 3173759 := bstep (se 1 (by rfl) ⟨2380319, by rfl⟩ : syracuseStep 3173759 = 4760639) B4760639
theorem B2115839 : Blo 2115435 2115839 := bstep (se 1 (by rfl) ⟨1586879, by rfl⟩ : syracuseStep 2115839 = 3173759) B3173759
theorem B3173765 : Blo 2115435 3173765 := bbase (se 4 (by rfl) ⟨297540, by rfl⟩ : syracuseStep 3173765 = 595081) (by norm_num)
theorem B2115843 : Blo 2115435 2115843 := bstep (se 1 (by rfl) ⟨1586882, by rfl⟩ : syracuseStep 2115843 = 3173765) B3173765
theorem B3570493 : Blo 2115435 3570493 := bbase (se 3 (by rfl) ⟨669467, by rfl⟩ : syracuseStep 3570493 = 1338935) (by norm_num)
theorem B4760657 : Blo 2115435 4760657 := bstep (se 2 (by rfl) ⟨1785246, by rfl⟩ : syracuseStep 4760657 = 3570493) B3570493
theorem B3173771 : Blo 2115435 3173771 := bstep (se 1 (by rfl) ⟨2380328, by rfl⟩ : syracuseStep 3173771 = 4760657) B4760657
theorem B2115847 : Blo 2115435 2115847 := bstep (se 1 (by rfl) ⟨1586885, by rfl⟩ : syracuseStep 2115847 = 3173771) B3173771
theorem B2380333 : Blo 2115435 2380333 := bbase (se 3 (by rfl) ⟨446312, by rfl⟩ : syracuseStep 2380333 = 892625) (by norm_num)
theorem B3173777 : Blo 2115435 3173777 := bstep (se 2 (by rfl) ⟨1190166, by rfl⟩ : syracuseStep 3173777 = 2380333) B2380333
theorem B2115851 : Blo 2115435 2115851 := bstep (se 1 (by rfl) ⟨1586888, by rfl⟩ : syracuseStep 2115851 = 3173777) B3173777
theorem B7141013 : Blo 2115435 7141013 := bbase (se 6 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 7141013 = 334735) (by norm_num)
theorem B4760675 : Blo 2115435 4760675 := bstep (se 1 (by rfl) ⟨3570506, by rfl⟩ : syracuseStep 4760675 = 7141013) B7141013
theorem B3173783 : Blo 2115435 3173783 := bstep (se 1 (by rfl) ⟨2380337, by rfl⟩ : syracuseStep 3173783 = 4760675) B4760675
theorem B2115855 : Blo 2115435 2115855 := bstep (se 1 (by rfl) ⟨1586891, by rfl⟩ : syracuseStep 2115855 = 3173783) B3173783
theorem B3173789 : Blo 2115435 3173789 := bbase (se 3 (by rfl) ⟨595085, by rfl⟩ : syracuseStep 3173789 = 1190171) (by norm_num)
theorem B2115859 : Blo 2115435 2115859 := bstep (se 1 (by rfl) ⟨1586894, by rfl⟩ : syracuseStep 2115859 = 3173789) B3173789
theorem B4760693 : Blo 2115435 4760693 := bbase (se 5 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 4760693 = 446315) (by norm_num)
theorem B3173795 : Blo 2115435 3173795 := bstep (se 1 (by rfl) ⟨2380346, by rfl⟩ : syracuseStep 3173795 = 4760693) B4760693
theorem B2115863 : Blo 2115435 2115863 := bstep (se 1 (by rfl) ⟨1586897, by rfl⟩ : syracuseStep 2115863 = 3173795) B3173795
theorem B18075797 : Blo 2115435 18075797 := bbase (se 6 (by rfl) ⟨423651, by rfl⟩ : syracuseStep 18075797 = 847303) (by norm_num)
theorem B12050531 : Blo 2115435 12050531 := bstep (se 1 (by rfl) ⟨9037898, by rfl⟩ : syracuseStep 12050531 = 18075797) B18075797
theorem B8033687 : Blo 2115435 8033687 := bstep (se 1 (by rfl) ⟨6025265, by rfl⟩ : syracuseStep 8033687 = 12050531) B12050531
theorem B5355791 : Blo 2115435 5355791 := bstep (se 1 (by rfl) ⟨4016843, by rfl⟩ : syracuseStep 5355791 = 8033687) B8033687
theorem B3570527 : Blo 2115435 3570527 := bstep (se 1 (by rfl) ⟨2677895, by rfl⟩ : syracuseStep 3570527 = 5355791) B5355791
theorem B2380351 : Blo 2115435 2380351 := bstep (se 1 (by rfl) ⟨1785263, by rfl⟩ : syracuseStep 2380351 = 3570527) B3570527
theorem B3173801 : Blo 2115435 3173801 := bstep (se 2 (by rfl) ⟨1190175, by rfl⟩ : syracuseStep 3173801 = 2380351) B2380351
theorem B2115867 : Blo 2115435 2115867 := bstep (se 1 (by rfl) ⟨1586900, by rfl⟩ : syracuseStep 2115867 = 3173801) B3173801
theorem B8033701 : Blo 2115435 8033701 := bbase (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) (by norm_num)
theorem B10711601 : Blo 2115435 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B7141067 : Blo 2115435 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B4760711 : Blo 2115435 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B3173807 : Blo 2115435 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B2115871 : Blo 2115435 2115871 := bstep (se 1 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 2115871 = 3173807) B3173807
theorem B3173813 : Blo 2115435 3173813 := bbase (se 5 (by rfl) ⟨148772, by rfl⟩ : syracuseStep 3173813 = 297545) (by norm_num)
theorem B2115875 : Blo 2115435 2115875 := bstep (se 1 (by rfl) ⟨1586906, by rfl⟩ : syracuseStep 2115875 = 3173813) B3173813
theorem B5355821 : Blo 2115435 5355821 := bbase (se 3 (by rfl) ⟨1004216, by rfl⟩ : syracuseStep 5355821 = 2008433) (by norm_num)
theorem B3570547 : Blo 2115435 3570547 := bstep (se 1 (by rfl) ⟨2677910, by rfl⟩ : syracuseStep 3570547 = 5355821) B5355821
theorem B4760729 : Blo 2115435 4760729 := bstep (se 2 (by rfl) ⟨1785273, by rfl⟩ : syracuseStep 4760729 = 3570547) B3570547
theorem B3173819 : Blo 2115435 3173819 := bstep (se 1 (by rfl) ⟨2380364, by rfl⟩ : syracuseStep 3173819 = 4760729) B4760729
theorem B2115879 : Blo 2115435 2115879 := bstep (se 1 (by rfl) ⟨1586909, by rfl⟩ : syracuseStep 2115879 = 3173819) B3173819
theorem B2380369 : Blo 2115435 2380369 := bbase (se 2 (by rfl) ⟨892638, by rfl⟩ : syracuseStep 2380369 = 1785277) (by norm_num)
theorem B3173825 : Blo 2115435 3173825 := bstep (se 2 (by rfl) ⟨1190184, by rfl⟩ : syracuseStep 3173825 = 2380369) B2380369
theorem B2115883 : Blo 2115435 2115883 := bstep (se 1 (by rfl) ⟨1586912, by rfl⟩ : syracuseStep 2115883 = 3173825) B3173825
theorem B3012661 : Blo 2115435 3012661 := bbase (se 5 (by rfl) ⟨141218, by rfl⟩ : syracuseStep 3012661 = 282437) (by norm_num)
theorem B4016881 : Blo 2115435 4016881 := bstep (se 2 (by rfl) ⟨1506330, by rfl⟩ : syracuseStep 4016881 = 3012661) B3012661
theorem B5355841 : Blo 2115435 5355841 := bstep (se 2 (by rfl) ⟨2008440, by rfl⟩ : syracuseStep 5355841 = 4016881) B4016881
theorem B7141121 : Blo 2115435 7141121 := bstep (se 2 (by rfl) ⟨2677920, by rfl⟩ : syracuseStep 7141121 = 5355841) B5355841
theorem B4760747 : Blo 2115435 4760747 := bstep (se 1 (by rfl) ⟨3570560, by rfl⟩ : syracuseStep 4760747 = 7141121) B7141121
theorem B3173831 : Blo 2115435 3173831 := bstep (se 1 (by rfl) ⟨2380373, by rfl⟩ : syracuseStep 3173831 = 4760747) B4760747
theorem B2115887 : Blo 2115435 2115887 := bstep (se 1 (by rfl) ⟨1586915, by rfl⟩ : syracuseStep 2115887 = 3173831) B3173831
theorem B3173837 : Blo 2115435 3173837 := bbase (se 3 (by rfl) ⟨595094, by rfl⟩ : syracuseStep 3173837 = 1190189) (by norm_num)
theorem B2115891 : Blo 2115435 2115891 := bstep (se 1 (by rfl) ⟨1586918, by rfl⟩ : syracuseStep 2115891 = 3173837) B3173837
theorem B4760765 : Blo 2115435 4760765 := bbase (se 3 (by rfl) ⟨892643, by rfl⟩ : syracuseStep 4760765 = 1785287) (by norm_num)
theorem B3173843 : Blo 2115435 3173843 := bstep (se 1 (by rfl) ⟨2380382, by rfl⟩ : syracuseStep 3173843 = 4760765) B4760765
theorem B2115895 : Blo 2115435 2115895 := bstep (se 1 (by rfl) ⟨1586921, by rfl⟩ : syracuseStep 2115895 = 3173843) B3173843
theorem B3570581 : Blo 2115435 3570581 := bbase (se 6 (by rfl) ⟨83685, by rfl⟩ : syracuseStep 3570581 = 167371) (by norm_num)
theorem B2380387 : Blo 2115435 2380387 := bstep (se 1 (by rfl) ⟨1785290, by rfl⟩ : syracuseStep 2380387 = 3570581) B3570581
theorem B3173849 : Blo 2115435 3173849 := bstep (se 2 (by rfl) ⟨1190193, by rfl⟩ : syracuseStep 3173849 = 2380387) B2380387
theorem B2115899 : Blo 2115435 2115899 := bstep (se 1 (by rfl) ⟨1586924, by rfl⟩ : syracuseStep 2115899 = 3173849) B3173849
theorem B13557077 : Blo 2115435 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B9038051 : Blo 2115435 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B6025367 : Blo 2115435 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B16067645 : Blo 2115435 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B10711763 : Blo 2115435 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B7141175 : Blo 2115435 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B4760783 : Blo 2115435 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B3173855 : Blo 2115435 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B2115903 : Blo 2115435 2115903 := bstep (se 1 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 2115903 = 3173855) B3173855
theorem B3173861 : Blo 2115435 3173861 := bbase (se 4 (by rfl) ⟨297549, by rfl⟩ : syracuseStep 3173861 = 595099) (by norm_num)
theorem B2115907 : Blo 2115435 2115907 := bstep (se 1 (by rfl) ⟨1586930, by rfl⟩ : syracuseStep 2115907 = 3173861) B3173861
theorem B4825757 : Blo 2115435 4825757 := bbase (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) (by norm_num)
theorem B12868685 : Blo 2115435 12868685 := bstep (se 3 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 12868685 = 4825757) B4825757
theorem B8579123 : Blo 2115435 8579123 := bstep (se 1 (by rfl) ⟨6434342, by rfl⟩ : syracuseStep 8579123 = 12868685) B12868685
theorem B5719415 : Blo 2115435 5719415 := bstep (se 1 (by rfl) ⟨4289561, by rfl⟩ : syracuseStep 5719415 = 8579123) B8579123
theorem B15251773 : Blo 2115435 15251773 := bstep (se 3 (by rfl) ⟨2859707, by rfl⟩ : syracuseStep 15251773 = 5719415) B5719415
theorem B20335697 : Blo 2115435 20335697 := bstep (se 2 (by rfl) ⟨7625886, by rfl⟩ : syracuseStep 20335697 = 15251773) B15251773
theorem B13557131 : Blo 2115435 13557131 := bstep (se 1 (by rfl) ⟨10167848, by rfl⟩ : syracuseStep 13557131 = 20335697) B20335697
theorem B9038087 : Blo 2115435 9038087 := bstep (se 1 (by rfl) ⟨6778565, by rfl⟩ : syracuseStep 9038087 = 13557131) B13557131
theorem B6025391 : Blo 2115435 6025391 := bstep (se 1 (by rfl) ⟨4519043, by rfl⟩ : syracuseStep 6025391 = 9038087) B9038087
theorem B4016927 : Blo 2115435 4016927 := bstep (se 1 (by rfl) ⟨3012695, by rfl⟩ : syracuseStep 4016927 = 6025391) B6025391
theorem B2677951 : Blo 2115435 2677951 := bstep (se 1 (by rfl) ⟨2008463, by rfl⟩ : syracuseStep 2677951 = 4016927) B4016927
theorem B3570601 : Blo 2115435 3570601 := bstep (se 2 (by rfl) ⟨1338975, by rfl⟩ : syracuseStep 3570601 = 2677951) B2677951
theorem B4760801 : Blo 2115435 4760801 := bstep (se 2 (by rfl) ⟨1785300, by rfl⟩ : syracuseStep 4760801 = 3570601) B3570601
theorem B3173867 : Blo 2115435 3173867 := bstep (se 1 (by rfl) ⟨2380400, by rfl⟩ : syracuseStep 3173867 = 4760801) B4760801
theorem B2115911 : Blo 2115435 2115911 := bstep (se 1 (by rfl) ⟨1586933, by rfl⟩ : syracuseStep 2115911 = 3173867) B3173867
theorem B2380405 : Blo 2115435 2380405 := bbase (se 5 (by rfl) ⟨111581, by rfl⟩ : syracuseStep 2380405 = 223163) (by norm_num)
theorem B3173873 : Blo 2115435 3173873 := bstep (se 2 (by rfl) ⟨1190202, by rfl⟩ : syracuseStep 3173873 = 2380405) B2380405
theorem B2115915 : Blo 2115435 2115915 := bstep (se 1 (by rfl) ⟨1586936, by rfl⟩ : syracuseStep 2115915 = 3173873) B3173873
theorem B2677961 : Blo 2115435 2677961 := bbase (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) (by norm_num)
theorem B7141229 : Blo 2115435 7141229 := bstep (se 3 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 7141229 = 2677961) B2677961
theorem B4760819 : Blo 2115435 4760819 := bstep (se 1 (by rfl) ⟨3570614, by rfl⟩ : syracuseStep 4760819 = 7141229) B7141229
theorem B3173879 : Blo 2115435 3173879 := bstep (se 1 (by rfl) ⟨2380409, by rfl⟩ : syracuseStep 3173879 = 4760819) B4760819
theorem B2115919 : Blo 2115435 2115919 := bstep (se 1 (by rfl) ⟨1586939, by rfl⟩ : syracuseStep 2115919 = 3173879) B3173879
theorem B3173885 : Blo 2115435 3173885 := bbase (se 3 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 3173885 = 1190207) (by norm_num)
theorem B2115923 : Blo 2115435 2115923 := bstep (se 1 (by rfl) ⟨1586942, by rfl⟩ : syracuseStep 2115923 = 3173885) B3173885
theorem B4760837 : Blo 2115435 4760837 := bbase (se 4 (by rfl) ⟨446328, by rfl⟩ : syracuseStep 4760837 = 892657) (by norm_num)
theorem B3173891 : Blo 2115435 3173891 := bstep (se 1 (by rfl) ⟨2380418, by rfl⟩ : syracuseStep 3173891 = 4760837) B4760837
theorem B2115927 : Blo 2115435 2115927 := bstep (se 1 (by rfl) ⟨1586945, by rfl⟩ : syracuseStep 2115927 = 3173891) B3173891
theorem B4016965 : Blo 2115435 4016965 := bbase (se 4 (by rfl) ⟨376590, by rfl⟩ : syracuseStep 4016965 = 753181) (by norm_num)
theorem B5355953 : Blo 2115435 5355953 := bstep (se 2 (by rfl) ⟨2008482, by rfl⟩ : syracuseStep 5355953 = 4016965) B4016965
theorem B3570635 : Blo 2115435 3570635 := bstep (se 1 (by rfl) ⟨2677976, by rfl⟩ : syracuseStep 3570635 = 5355953) B5355953
theorem B2380423 : Blo 2115435 2380423 := bstep (se 1 (by rfl) ⟨1785317, by rfl⟩ : syracuseStep 2380423 = 3570635) B3570635
theorem B3173897 : Blo 2115435 3173897 := bstep (se 2 (by rfl) ⟨1190211, by rfl⟩ : syracuseStep 3173897 = 2380423) B2380423
theorem B2115931 : Blo 2115435 2115931 := bstep (se 1 (by rfl) ⟨1586948, by rfl⟩ : syracuseStep 2115931 = 3173897) B3173897
theorem B10711925 : Blo 2115435 10711925 := bbase (se 5 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 10711925 = 1004243) (by norm_num)
theorem B7141283 : Blo 2115435 7141283 := bstep (se 1 (by rfl) ⟨5355962, by rfl⟩ : syracuseStep 7141283 = 10711925) B10711925
theorem B4760855 : Blo 2115435 4760855 := bstep (se 1 (by rfl) ⟨3570641, by rfl⟩ : syracuseStep 4760855 = 7141283) B7141283
theorem B3173903 : Blo 2115435 3173903 := bstep (se 1 (by rfl) ⟨2380427, by rfl⟩ : syracuseStep 3173903 = 4760855) B4760855
theorem B2115935 : Blo 2115435 2115935 := bstep (se 1 (by rfl) ⟨1586951, by rfl⟩ : syracuseStep 2115935 = 3173903) B3173903
theorem B3173909 : Blo 2115435 3173909 := bbase (se 6 (by rfl) ⟨74388, by rfl⟩ : syracuseStep 3173909 = 148777) (by norm_num)
theorem B2115939 : Blo 2115435 2115939 := bstep (se 1 (by rfl) ⟨1586954, by rfl⟩ : syracuseStep 2115939 = 3173909) B3173909
theorem B2144813 : Blo 2115435 2144813 := bbase (se 3 (by rfl) ⟨402152, by rfl⟩ : syracuseStep 2144813 = 804305) (by norm_num)
theorem B5719501 : Blo 2115435 5719501 := bstep (se 3 (by rfl) ⟨1072406, by rfl⟩ : syracuseStep 5719501 = 2144813) B2144813
theorem B7626001 : Blo 2115435 7626001 := bstep (se 2 (by rfl) ⟨2859750, by rfl⟩ : syracuseStep 7626001 = 5719501) B5719501
theorem B10168001 : Blo 2115435 10168001 := bstep (se 2 (by rfl) ⟨3813000, by rfl⟩ : syracuseStep 10168001 = 7626001) B7626001
theorem B6778667 : Blo 2115435 6778667 := bstep (se 1 (by rfl) ⟨5084000, by rfl⟩ : syracuseStep 6778667 = 10168001) B10168001
theorem B18076445 : Blo 2115435 18076445 := bstep (se 3 (by rfl) ⟨3389333, by rfl⟩ : syracuseStep 18076445 = 6778667) B6778667
theorem B12050963 : Blo 2115435 12050963 := bstep (se 1 (by rfl) ⟨9038222, by rfl⟩ : syracuseStep 12050963 = 18076445) B18076445
theorem B8033975 : Blo 2115435 8033975 := bstep (se 1 (by rfl) ⟨6025481, by rfl⟩ : syracuseStep 8033975 = 12050963) B12050963
theorem B5355983 : Blo 2115435 5355983 := bstep (se 1 (by rfl) ⟨4016987, by rfl⟩ : syracuseStep 5355983 = 8033975) B8033975
theorem B3570655 : Blo 2115435 3570655 := bstep (se 1 (by rfl) ⟨2677991, by rfl⟩ : syracuseStep 3570655 = 5355983) B5355983
theorem B4760873 : Blo 2115435 4760873 := bstep (se 2 (by rfl) ⟨1785327, by rfl⟩ : syracuseStep 4760873 = 3570655) B3570655
theorem B3173915 : Blo 2115435 3173915 := bstep (se 1 (by rfl) ⟨2380436, by rfl⟩ : syracuseStep 3173915 = 4760873) B4760873
theorem B2115943 : Blo 2115435 2115943 := bstep (se 1 (by rfl) ⟨1586957, by rfl⟩ : syracuseStep 2115943 = 3173915) B3173915
theorem B2380441 : Blo 2115435 2380441 := bbase (se 2 (by rfl) ⟨892665, by rfl⟩ : syracuseStep 2380441 = 1785331) (by norm_num)
theorem B3173921 : Blo 2115435 3173921 := bstep (se 2 (by rfl) ⟨1190220, by rfl⟩ : syracuseStep 3173921 = 2380441) B2380441
theorem B2115947 : Blo 2115435 2115947 := bstep (se 1 (by rfl) ⟨1586960, by rfl⟩ : syracuseStep 2115947 = 3173921) B3173921
theorem B8034005 : Blo 2115435 8034005 := bbase (se 7 (by rfl) ⟨94148, by rfl⟩ : syracuseStep 8034005 = 188297) (by norm_num)
theorem B5356003 : Blo 2115435 5356003 := bstep (se 1 (by rfl) ⟨4017002, by rfl⟩ : syracuseStep 5356003 = 8034005) B8034005
theorem B7141337 : Blo 2115435 7141337 := bstep (se 2 (by rfl) ⟨2678001, by rfl⟩ : syracuseStep 7141337 = 5356003) B5356003
theorem B4760891 : Blo 2115435 4760891 := bstep (se 1 (by rfl) ⟨3570668, by rfl⟩ : syracuseStep 4760891 = 7141337) B7141337
theorem B3173927 : Blo 2115435 3173927 := bstep (se 1 (by rfl) ⟨2380445, by rfl⟩ : syracuseStep 3173927 = 4760891) B4760891
theorem B2115951 : Blo 2115435 2115951 := bstep (se 1 (by rfl) ⟨1586963, by rfl⟩ : syracuseStep 2115951 = 3173927) B3173927
theorem B3173933 : Blo 2115435 3173933 := bbase (se 3 (by rfl) ⟨595112, by rfl⟩ : syracuseStep 3173933 = 1190225) (by norm_num)
theorem B2115955 : Blo 2115435 2115955 := bstep (se 1 (by rfl) ⟨1586966, by rfl⟩ : syracuseStep 2115955 = 3173933) B3173933
theorem B4760909 : Blo 2115435 4760909 := bbase (se 3 (by rfl) ⟨892670, by rfl⟩ : syracuseStep 4760909 = 1785341) (by norm_num)
theorem B3173939 : Blo 2115435 3173939 := bstep (se 1 (by rfl) ⟨2380454, by rfl⟩ : syracuseStep 3173939 = 4760909) B4760909
theorem B2115959 : Blo 2115435 2115959 := bstep (se 1 (by rfl) ⟨1586969, by rfl⟩ : syracuseStep 2115959 = 3173939) B3173939
theorem B2678017 : Blo 2115435 2678017 := bbase (se 2 (by rfl) ⟨1004256, by rfl⟩ : syracuseStep 2678017 = 2008513) (by norm_num)
theorem B3570689 : Blo 2115435 3570689 := bstep (se 2 (by rfl) ⟨1339008, by rfl⟩ : syracuseStep 3570689 = 2678017) B2678017
theorem B2380459 : Blo 2115435 2380459 := bstep (se 1 (by rfl) ⟨1785344, by rfl⟩ : syracuseStep 2380459 = 3570689) B3570689
theorem B3173945 : Blo 2115435 3173945 := bstep (se 2 (by rfl) ⟨1190229, by rfl⟩ : syracuseStep 3173945 = 2380459) B2380459
theorem B2115963 : Blo 2115435 2115963 := bstep (se 1 (by rfl) ⟨1586972, by rfl⟩ : syracuseStep 2115963 = 3173945) B3173945
theorem B2259581 : Blo 2115435 2259581 := bbase (se 3 (by rfl) ⟨423671, by rfl⟩ : syracuseStep 2259581 = 847343) (by norm_num)
theorem B24102197 : Blo 2115435 24102197 := bstep (se 5 (by rfl) ⟨1129790, by rfl⟩ : syracuseStep 24102197 = 2259581) B2259581
theorem B16068131 : Blo 2115435 16068131 := bstep (se 1 (by rfl) ⟨12051098, by rfl⟩ : syracuseStep 16068131 = 24102197) B24102197
theorem B10712087 : Blo 2115435 10712087 := bstep (se 1 (by rfl) ⟨8034065, by rfl⟩ : syracuseStep 10712087 = 16068131) B16068131
theorem B7141391 : Blo 2115435 7141391 := bstep (se 1 (by rfl) ⟨5356043, by rfl⟩ : syracuseStep 7141391 = 10712087) B10712087
theorem B4760927 : Blo 2115435 4760927 := bstep (se 1 (by rfl) ⟨3570695, by rfl⟩ : syracuseStep 4760927 = 7141391) B7141391
theorem B3173951 : Blo 2115435 3173951 := bstep (se 1 (by rfl) ⟨2380463, by rfl⟩ : syracuseStep 3173951 = 4760927) B4760927
theorem B2115967 : Blo 2115435 2115967 := bstep (se 1 (by rfl) ⟨1586975, by rfl⟩ : syracuseStep 2115967 = 3173951) B3173951
theorem B3173957 : Blo 2115435 3173957 := bbase (se 4 (by rfl) ⟨297558, by rfl⟩ : syracuseStep 3173957 = 595117) (by norm_num)
theorem B2115971 : Blo 2115435 2115971 := bstep (se 1 (by rfl) ⟨1586978, by rfl⟩ : syracuseStep 2115971 = 3173957) B3173957
theorem B3570709 : Blo 2115435 3570709 := bbase (se 6 (by rfl) ⟨83688, by rfl⟩ : syracuseStep 3570709 = 167377) (by norm_num)
theorem B4760945 : Blo 2115435 4760945 := bstep (se 2 (by rfl) ⟨1785354, by rfl⟩ : syracuseStep 4760945 = 3570709) B3570709
theorem B3173963 : Blo 2115435 3173963 := bstep (se 1 (by rfl) ⟨2380472, by rfl⟩ : syracuseStep 3173963 = 4760945) B4760945
theorem B2115975 : Blo 2115435 2115975 := bstep (se 1 (by rfl) ⟨1586981, by rfl⟩ : syracuseStep 2115975 = 3173963) B3173963
theorem B2380477 : Blo 2115435 2380477 := bbase (se 3 (by rfl) ⟨446339, by rfl⟩ : syracuseStep 2380477 = 892679) (by norm_num)
theorem B3173969 : Blo 2115435 3173969 := bstep (se 2 (by rfl) ⟨1190238, by rfl⟩ : syracuseStep 3173969 = 2380477) B2380477
theorem B2115979 : Blo 2115435 2115979 := bstep (se 1 (by rfl) ⟨1586984, by rfl⟩ : syracuseStep 2115979 = 3173969) B3173969
theorem B7141445 : Blo 2115435 7141445 := bbase (se 4 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 7141445 = 1339021) (by norm_num)
theorem B4760963 : Blo 2115435 4760963 := bstep (se 1 (by rfl) ⟨3570722, by rfl⟩ : syracuseStep 4760963 = 7141445) B7141445
theorem B3173975 : Blo 2115435 3173975 := bstep (se 1 (by rfl) ⟨2380481, by rfl⟩ : syracuseStep 3173975 = 4760963) B4760963
theorem B2115983 : Blo 2115435 2115983 := bstep (se 1 (by rfl) ⟨1586987, by rfl⟩ : syracuseStep 2115983 = 3173975) B3173975
theorem B3173981 : Blo 2115435 3173981 := bbase (se 3 (by rfl) ⟨595121, by rfl⟩ : syracuseStep 3173981 = 1190243) (by norm_num)
theorem B2115987 : Blo 2115435 2115987 := bstep (se 1 (by rfl) ⟨1586990, by rfl⟩ : syracuseStep 2115987 = 3173981) B3173981
theorem B4760981 : Blo 2115435 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B3173987 : Blo 2115435 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B2115991 : Blo 2115435 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B9161765 : Blo 2115435 9161765 := bbase (se 4 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 9161765 = 1717831) (by norm_num)
theorem B6107843 : Blo 2115435 6107843 := bstep (se 1 (by rfl) ⟨4580882, by rfl⟩ : syracuseStep 6107843 = 9161765) B9161765
theorem B16287581 : Blo 2115435 16287581 := bstep (se 3 (by rfl) ⟨3053921, by rfl⟩ : syracuseStep 16287581 = 6107843) B6107843
theorem B10858387 : Blo 2115435 10858387 := bstep (se 1 (by rfl) ⟨8143790, by rfl⟩ : syracuseStep 10858387 = 16287581) B16287581
theorem B14477849 : Blo 2115435 14477849 := bstep (se 2 (by rfl) ⟨5429193, by rfl⟩ : syracuseStep 14477849 = 10858387) B10858387
theorem B9651899 : Blo 2115435 9651899 := bstep (se 1 (by rfl) ⟨7238924, by rfl⟩ : syracuseStep 9651899 = 14477849) B14477849
theorem B6434599 : Blo 2115435 6434599 := bstep (se 1 (by rfl) ⟨4825949, by rfl⟩ : syracuseStep 6434599 = 9651899) B9651899
theorem B8579465 : Blo 2115435 8579465 := bstep (se 2 (by rfl) ⟨3217299, by rfl⟩ : syracuseStep 8579465 = 6434599) B6434599
theorem B5719643 : Blo 2115435 5719643 := bstep (se 1 (by rfl) ⟨4289732, by rfl⟩ : syracuseStep 5719643 = 8579465) B8579465
theorem B3813095 : Blo 2115435 3813095 := bstep (se 1 (by rfl) ⟨2859821, by rfl⟩ : syracuseStep 3813095 = 5719643) B5719643
theorem B10168253 : Blo 2115435 10168253 := bstep (se 3 (by rfl) ⟨1906547, by rfl⟩ : syracuseStep 10168253 = 3813095) B3813095
theorem B6778835 : Blo 2115435 6778835 := bstep (se 1 (by rfl) ⟨5084126, by rfl⟩ : syracuseStep 6778835 = 10168253) B10168253
theorem B4519223 : Blo 2115435 4519223 := bstep (se 1 (by rfl) ⟨3389417, by rfl⟩ : syracuseStep 4519223 = 6778835) B6778835
theorem B3012815 : Blo 2115435 3012815 := bstep (se 1 (by rfl) ⟨2259611, by rfl⟩ : syracuseStep 3012815 = 4519223) B4519223
theorem B8034173 : Blo 2115435 8034173 := bstep (se 3 (by rfl) ⟨1506407, by rfl⟩ : syracuseStep 8034173 = 3012815) B3012815
theorem B5356115 : Blo 2115435 5356115 := bstep (se 1 (by rfl) ⟨4017086, by rfl⟩ : syracuseStep 5356115 = 8034173) B8034173
theorem B3570743 : Blo 2115435 3570743 := bstep (se 1 (by rfl) ⟨2678057, by rfl⟩ : syracuseStep 3570743 = 5356115) B5356115
theorem B2380495 : Blo 2115435 2380495 := bstep (se 1 (by rfl) ⟨1785371, by rfl⟩ : syracuseStep 2380495 = 3570743) B3570743
theorem B3173993 : Blo 2115435 3173993 := bstep (se 2 (by rfl) ⟨1190247, by rfl⟩ : syracuseStep 3173993 = 2380495) B2380495
theorem B2115995 : Blo 2115435 2115995 := bstep (se 1 (by rfl) ⟨1586996, by rfl⟩ : syracuseStep 2115995 = 3173993) B3173993
theorem B19303829 : Blo 2115435 19303829 := bbase (se 6 (by rfl) ⟨452433, by rfl⟩ : syracuseStep 19303829 = 904867) (by norm_num)
theorem B12869219 : Blo 2115435 12869219 := bstep (se 1 (by rfl) ⟨9651914, by rfl⟩ : syracuseStep 12869219 = 19303829) B19303829
theorem B8579479 : Blo 2115435 8579479 := bstep (se 1 (by rfl) ⟨6434609, by rfl⟩ : syracuseStep 8579479 = 12869219) B12869219
theorem B11439305 : Blo 2115435 11439305 := bstep (se 2 (by rfl) ⟨4289739, by rfl⟩ : syracuseStep 11439305 = 8579479) B8579479
theorem B7626203 : Blo 2115435 7626203 := bstep (se 1 (by rfl) ⟨5719652, by rfl⟩ : syracuseStep 7626203 = 11439305) B11439305
theorem B5084135 : Blo 2115435 5084135 := bstep (se 1 (by rfl) ⟨3813101, by rfl⟩ : syracuseStep 5084135 = 7626203) B7626203
theorem B3389423 : Blo 2115435 3389423 := bstep (se 1 (by rfl) ⟨2542067, by rfl⟩ : syracuseStep 3389423 = 5084135) B5084135
theorem B9038461 : Blo 2115435 9038461 := bstep (se 3 (by rfl) ⟨1694711, by rfl⟩ : syracuseStep 9038461 = 3389423) B3389423
theorem B12051281 : Blo 2115435 12051281 := bstep (se 2 (by rfl) ⟨4519230, by rfl⟩ : syracuseStep 12051281 = 9038461) B9038461
theorem B8034187 : Blo 2115435 8034187 := bstep (se 1 (by rfl) ⟨6025640, by rfl⟩ : syracuseStep 8034187 = 12051281) B12051281
theorem B10712249 : Blo 2115435 10712249 := bstep (se 2 (by rfl) ⟨4017093, by rfl⟩ : syracuseStep 10712249 = 8034187) B8034187
theorem B7141499 : Blo 2115435 7141499 := bstep (se 1 (by rfl) ⟨5356124, by rfl⟩ : syracuseStep 7141499 = 10712249) B10712249
theorem B4760999 : Blo 2115435 4760999 := bstep (se 1 (by rfl) ⟨3570749, by rfl⟩ : syracuseStep 4760999 = 7141499) B7141499
theorem B3173999 : Blo 2115435 3173999 := bstep (se 1 (by rfl) ⟨2380499, by rfl⟩ : syracuseStep 3173999 = 4760999) B4760999
theorem B2115999 : Blo 2115435 2115999 := bstep (se 1 (by rfl) ⟨1586999, by rfl⟩ : syracuseStep 2115999 = 3173999) B3173999
theorem B3174005 : Blo 2115435 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B2116003 : Blo 2115435 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B4017109 : Blo 2115435 4017109 := bbase (se 7 (by rfl) ⟨47075, by rfl⟩ : syracuseStep 4017109 = 94151) (by norm_num)
theorem B5356145 : Blo 2115435 5356145 := bstep (se 2 (by rfl) ⟨2008554, by rfl⟩ : syracuseStep 5356145 = 4017109) B4017109
theorem B3570763 : Blo 2115435 3570763 := bstep (se 1 (by rfl) ⟨2678072, by rfl⟩ : syracuseStep 3570763 = 5356145) B5356145
theorem B4761017 : Blo 2115435 4761017 := bstep (se 2 (by rfl) ⟨1785381, by rfl⟩ : syracuseStep 4761017 = 3570763) B3570763
theorem B3174011 : Blo 2115435 3174011 := bstep (se 1 (by rfl) ⟨2380508, by rfl⟩ : syracuseStep 3174011 = 4761017) B4761017
theorem B2116007 : Blo 2115435 2116007 := bstep (se 1 (by rfl) ⟨1587005, by rfl⟩ : syracuseStep 2116007 = 3174011) B3174011
theorem B2380513 : Blo 2115435 2380513 := bbase (se 2 (by rfl) ⟨892692, by rfl⟩ : syracuseStep 2380513 = 1785385) (by norm_num)
theorem B3174017 : Blo 2115435 3174017 := bstep (se 2 (by rfl) ⟨1190256, by rfl⟩ : syracuseStep 3174017 = 2380513) B2380513
theorem B2116011 : Blo 2115435 2116011 := bstep (se 1 (by rfl) ⟨1587008, by rfl⟩ : syracuseStep 2116011 = 3174017) B3174017
theorem B5356165 : Blo 2115435 5356165 := bbase (se 4 (by rfl) ⟨502140, by rfl⟩ : syracuseStep 5356165 = 1004281) (by norm_num)
theorem B7141553 : Blo 2115435 7141553 := bstep (se 2 (by rfl) ⟨2678082, by rfl⟩ : syracuseStep 7141553 = 5356165) B5356165
theorem B4761035 : Blo 2115435 4761035 := bstep (se 1 (by rfl) ⟨3570776, by rfl⟩ : syracuseStep 4761035 = 7141553) B7141553
theorem B3174023 : Blo 2115435 3174023 := bstep (se 1 (by rfl) ⟨2380517, by rfl⟩ : syracuseStep 3174023 = 4761035) B4761035
theorem B2116015 : Blo 2115435 2116015 := bstep (se 1 (by rfl) ⟨1587011, by rfl⟩ : syracuseStep 2116015 = 3174023) B3174023
theorem B3174029 : Blo 2115435 3174029 := bbase (se 3 (by rfl) ⟨595130, by rfl⟩ : syracuseStep 3174029 = 1190261) (by norm_num)
theorem B2116019 : Blo 2115435 2116019 := bstep (se 1 (by rfl) ⟨1587014, by rfl⟩ : syracuseStep 2116019 = 3174029) B3174029
theorem B4761053 : Blo 2115435 4761053 := bbase (se 3 (by rfl) ⟨892697, by rfl⟩ : syracuseStep 4761053 = 1785395) (by norm_num)
theorem B3174035 : Blo 2115435 3174035 := bstep (se 1 (by rfl) ⟨2380526, by rfl⟩ : syracuseStep 3174035 = 4761053) B4761053
theorem B2116023 : Blo 2115435 2116023 := bstep (se 1 (by rfl) ⟨1587017, by rfl⟩ : syracuseStep 2116023 = 3174035) B3174035
theorem B3570797 : Blo 2115435 3570797 := bbase (se 3 (by rfl) ⟨669524, by rfl⟩ : syracuseStep 3570797 = 1339049) (by norm_num)
theorem B2380531 : Blo 2115435 2380531 := bstep (se 1 (by rfl) ⟨1785398, by rfl⟩ : syracuseStep 2380531 = 3570797) B3570797
theorem B3174041 : Blo 2115435 3174041 := bstep (se 2 (by rfl) ⟨1190265, by rfl⟩ : syracuseStep 3174041 = 2380531) B2380531
theorem B2116027 : Blo 2115435 2116027 := bstep (se 1 (by rfl) ⟨1587020, by rfl⟩ : syracuseStep 2116027 = 3174041) B3174041
theorem B2859869 : Blo 2115435 2859869 := bbase (se 3 (by rfl) ⟨536225, by rfl⟩ : syracuseStep 2859869 = 1072451) (by norm_num)
theorem B7626317 : Blo 2115435 7626317 := bstep (se 3 (by rfl) ⟨1429934, by rfl⟩ : syracuseStep 7626317 = 2859869) B2859869
theorem B20336845 : Blo 2115435 20336845 := bstep (se 3 (by rfl) ⟨3813158, by rfl⟩ : syracuseStep 20336845 = 7626317) B7626317
theorem B27115793 : Blo 2115435 27115793 := bstep (se 2 (by rfl) ⟨10168422, by rfl⟩ : syracuseStep 27115793 = 20336845) B20336845
theorem B18077195 : Blo 2115435 18077195 := bstep (se 1 (by rfl) ⟨13557896, by rfl⟩ : syracuseStep 18077195 = 27115793) B27115793
theorem B12051463 : Blo 2115435 12051463 := bstep (se 1 (by rfl) ⟨9038597, by rfl⟩ : syracuseStep 12051463 = 18077195) B18077195
theorem B16068617 : Blo 2115435 16068617 := bstep (se 2 (by rfl) ⟨6025731, by rfl⟩ : syracuseStep 16068617 = 12051463) B12051463
theorem B10712411 : Blo 2115435 10712411 := bstep (se 1 (by rfl) ⟨8034308, by rfl⟩ : syracuseStep 10712411 = 16068617) B16068617
theorem B7141607 : Blo 2115435 7141607 := bstep (se 1 (by rfl) ⟨5356205, by rfl⟩ : syracuseStep 7141607 = 10712411) B10712411
theorem B4761071 : Blo 2115435 4761071 := bstep (se 1 (by rfl) ⟨3570803, by rfl⟩ : syracuseStep 4761071 = 7141607) B7141607
theorem B3174047 : Blo 2115435 3174047 := bstep (se 1 (by rfl) ⟨2380535, by rfl⟩ : syracuseStep 3174047 = 4761071) B4761071
theorem B2116031 : Blo 2115435 2116031 := bstep (se 1 (by rfl) ⟨1587023, by rfl⟩ : syracuseStep 2116031 = 3174047) B3174047
theorem B3174053 : Blo 2115435 3174053 := bbase (se 4 (by rfl) ⟨297567, by rfl⟩ : syracuseStep 3174053 = 595135) (by norm_num)
theorem B2116035 : Blo 2115435 2116035 := bstep (se 1 (by rfl) ⟨1587026, by rfl⟩ : syracuseStep 2116035 = 3174053) B3174053
theorem B2678113 : Blo 2115435 2678113 := bbase (se 2 (by rfl) ⟨1004292, by rfl⟩ : syracuseStep 2678113 = 2008585) (by norm_num)
theorem B3570817 : Blo 2115435 3570817 := bstep (se 2 (by rfl) ⟨1339056, by rfl⟩ : syracuseStep 3570817 = 2678113) B2678113
theorem B4761089 : Blo 2115435 4761089 := bstep (se 2 (by rfl) ⟨1785408, by rfl⟩ : syracuseStep 4761089 = 3570817) B3570817
theorem B3174059 : Blo 2115435 3174059 := bstep (se 1 (by rfl) ⟨2380544, by rfl⟩ : syracuseStep 3174059 = 4761089) B4761089
theorem B2116039 : Blo 2115435 2116039 := bstep (se 1 (by rfl) ⟨1587029, by rfl⟩ : syracuseStep 2116039 = 3174059) B3174059
theorem B2380549 : Blo 2115435 2380549 := bbase (se 4 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 2380549 = 446353) (by norm_num)
theorem B3174065 : Blo 2115435 3174065 := bstep (se 2 (by rfl) ⟨1190274, by rfl⟩ : syracuseStep 3174065 = 2380549) B2380549
theorem B2116043 : Blo 2115435 2116043 := bstep (se 1 (by rfl) ⟨1587032, by rfl⟩ : syracuseStep 2116043 = 3174065) B3174065
theorem B3389501 : Blo 2115435 3389501 := bbase (se 3 (by rfl) ⟨635531, by rfl⟩ : syracuseStep 3389501 = 1271063) (by norm_num)
theorem B2259667 : Blo 2115435 2259667 := bstep (se 1 (by rfl) ⟨1694750, by rfl⟩ : syracuseStep 2259667 = 3389501) B3389501
theorem B3012889 : Blo 2115435 3012889 := bstep (se 2 (by rfl) ⟨1129833, by rfl⟩ : syracuseStep 3012889 = 2259667) B2259667
theorem B4017185 : Blo 2115435 4017185 := bstep (se 2 (by rfl) ⟨1506444, by rfl⟩ : syracuseStep 4017185 = 3012889) B3012889
theorem B2678123 : Blo 2115435 2678123 := bstep (se 1 (by rfl) ⟨2008592, by rfl⟩ : syracuseStep 2678123 = 4017185) B4017185
theorem B7141661 : Blo 2115435 7141661 := bstep (se 3 (by rfl) ⟨1339061, by rfl⟩ : syracuseStep 7141661 = 2678123) B2678123
theorem B4761107 : Blo 2115435 4761107 := bstep (se 1 (by rfl) ⟨3570830, by rfl⟩ : syracuseStep 4761107 = 7141661) B7141661
theorem B3174071 : Blo 2115435 3174071 := bstep (se 1 (by rfl) ⟨2380553, by rfl⟩ : syracuseStep 3174071 = 4761107) B4761107
theorem B2116047 : Blo 2115435 2116047 := bstep (se 1 (by rfl) ⟨1587035, by rfl⟩ : syracuseStep 2116047 = 3174071) B3174071
theorem B3174077 : Blo 2115435 3174077 := bbase (se 3 (by rfl) ⟨595139, by rfl⟩ : syracuseStep 3174077 = 1190279) (by norm_num)
theorem B2116051 : Blo 2115435 2116051 := bstep (se 1 (by rfl) ⟨1587038, by rfl⟩ : syracuseStep 2116051 = 3174077) B3174077
theorem B4761125 : Blo 2115435 4761125 := bbase (se 4 (by rfl) ⟨446355, by rfl⟩ : syracuseStep 4761125 = 892711) (by norm_num)
theorem B3174083 : Blo 2115435 3174083 := bstep (se 1 (by rfl) ⟨2380562, by rfl⟩ : syracuseStep 3174083 = 4761125) B4761125
theorem B2116055 : Blo 2115435 2116055 := bstep (se 1 (by rfl) ⟨1587041, by rfl⟩ : syracuseStep 2116055 = 3174083) B3174083
theorem B5356277 : Blo 2115435 5356277 := bbase (se 5 (by rfl) ⟨251075, by rfl⟩ : syracuseStep 5356277 = 502151) (by norm_num)
theorem B3570851 : Blo 2115435 3570851 := bstep (se 1 (by rfl) ⟨2678138, by rfl⟩ : syracuseStep 3570851 = 5356277) B5356277
theorem B2380567 : Blo 2115435 2380567 := bstep (se 1 (by rfl) ⟨1785425, by rfl⟩ : syracuseStep 2380567 = 3570851) B3570851
theorem B3174089 : Blo 2115435 3174089 := bstep (se 2 (by rfl) ⟨1190283, by rfl⟩ : syracuseStep 3174089 = 2380567) B2380567
theorem B2116059 : Blo 2115435 2116059 := bstep (se 1 (by rfl) ⟨1587044, by rfl⟩ : syracuseStep 2116059 = 3174089) B3174089
theorem B4289869 : Blo 2115435 4289869 := bbase (se 3 (by rfl) ⟨804350, by rfl⟩ : syracuseStep 4289869 = 1608701) (by norm_num)
theorem B5719825 : Blo 2115435 5719825 := bstep (se 2 (by rfl) ⟨2144934, by rfl⟩ : syracuseStep 5719825 = 4289869) B4289869
theorem B30505733 : Blo 2115435 30505733 := bstep (se 4 (by rfl) ⟨2859912, by rfl⟩ : syracuseStep 30505733 = 5719825) B5719825
theorem B20337155 : Blo 2115435 20337155 := bstep (se 1 (by rfl) ⟨15252866, by rfl⟩ : syracuseStep 20337155 = 30505733) B30505733
theorem B13558103 : Blo 2115435 13558103 := bstep (se 1 (by rfl) ⟨10168577, by rfl⟩ : syracuseStep 13558103 = 20337155) B20337155
theorem B9038735 : Blo 2115435 9038735 := bstep (se 1 (by rfl) ⟨6779051, by rfl⟩ : syracuseStep 9038735 = 13558103) B13558103
theorem B6025823 : Blo 2115435 6025823 := bstep (se 1 (by rfl) ⟨4519367, by rfl⟩ : syracuseStep 6025823 = 9038735) B9038735
theorem B4017215 : Blo 2115435 4017215 := bstep (se 1 (by rfl) ⟨3012911, by rfl⟩ : syracuseStep 4017215 = 6025823) B6025823
theorem B10712573 : Blo 2115435 10712573 := bstep (se 3 (by rfl) ⟨2008607, by rfl⟩ : syracuseStep 10712573 = 4017215) B4017215
theorem B7141715 : Blo 2115435 7141715 := bstep (se 1 (by rfl) ⟨5356286, by rfl⟩ : syracuseStep 7141715 = 10712573) B10712573
theorem B4761143 : Blo 2115435 4761143 := bstep (se 1 (by rfl) ⟨3570857, by rfl⟩ : syracuseStep 4761143 = 7141715) B7141715
theorem B3174095 : Blo 2115435 3174095 := bstep (se 1 (by rfl) ⟨2380571, by rfl⟩ : syracuseStep 3174095 = 4761143) B4761143
theorem B2116063 : Blo 2115435 2116063 := bstep (se 1 (by rfl) ⟨1587047, by rfl⟩ : syracuseStep 2116063 = 3174095) B3174095
theorem B3174101 : Blo 2115435 3174101 := bbase (se 7 (by rfl) ⟨37196, by rfl⟩ : syracuseStep 3174101 = 74393) (by norm_num)
theorem B2116067 : Blo 2115435 2116067 := bstep (se 1 (by rfl) ⟨1587050, by rfl⟩ : syracuseStep 2116067 = 3174101) B3174101
theorem B5084309 : Blo 2115435 5084309 := bbase (se 6 (by rfl) ⟨119163, by rfl⟩ : syracuseStep 5084309 = 238327) (by norm_num)
theorem B3389539 : Blo 2115435 3389539 := bstep (se 1 (by rfl) ⟨2542154, by rfl⟩ : syracuseStep 3389539 = 5084309) B5084309
theorem B4519385 : Blo 2115435 4519385 := bstep (se 2 (by rfl) ⟨1694769, by rfl⟩ : syracuseStep 4519385 = 3389539) B3389539
theorem B3012923 : Blo 2115435 3012923 := bstep (se 1 (by rfl) ⟨2259692, by rfl⟩ : syracuseStep 3012923 = 4519385) B4519385
theorem B8034461 : Blo 2115435 8034461 := bstep (se 3 (by rfl) ⟨1506461, by rfl⟩ : syracuseStep 8034461 = 3012923) B3012923
theorem B5356307 : Blo 2115435 5356307 := bstep (se 1 (by rfl) ⟨4017230, by rfl⟩ : syracuseStep 5356307 = 8034461) B8034461
theorem B3570871 : Blo 2115435 3570871 := bstep (se 1 (by rfl) ⟨2678153, by rfl⟩ : syracuseStep 3570871 = 5356307) B5356307
theorem B4761161 : Blo 2115435 4761161 := bstep (se 2 (by rfl) ⟨1785435, by rfl⟩ : syracuseStep 4761161 = 3570871) B3570871
theorem B3174107 : Blo 2115435 3174107 := bstep (se 1 (by rfl) ⟨2380580, by rfl⟩ : syracuseStep 3174107 = 4761161) B4761161
theorem B2116071 : Blo 2115435 2116071 := bstep (se 1 (by rfl) ⟨1587053, by rfl⟩ : syracuseStep 2116071 = 3174107) B3174107
theorem B2380585 : Blo 2115435 2380585 := bbase (se 2 (by rfl) ⟨892719, by rfl⟩ : syracuseStep 2380585 = 1785439) (by norm_num)
theorem B3174113 : Blo 2115435 3174113 := bstep (se 2 (by rfl) ⟨1190292, by rfl⟩ : syracuseStep 3174113 = 2380585) B2380585
theorem B2116075 : Blo 2115435 2116075 := bstep (se 1 (by rfl) ⟨1587056, by rfl⟩ : syracuseStep 2116075 = 3174113) B3174113
theorem B6275893 : Blo 2115435 6275893 := bbase (se 5 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 6275893 = 588365) (by norm_num)
theorem B8367857 : Blo 2115435 8367857 := bstep (se 2 (by rfl) ⟨3137946, by rfl⟩ : syracuseStep 8367857 = 6275893) B6275893
theorem B5578571 : Blo 2115435 5578571 := bstep (se 1 (by rfl) ⟨4183928, by rfl⟩ : syracuseStep 5578571 = 8367857) B8367857
theorem B3719047 : Blo 2115435 3719047 := bstep (se 1 (by rfl) ⟨2789285, by rfl⟩ : syracuseStep 3719047 = 5578571) B5578571
theorem B4958729 : Blo 2115435 4958729 := bstep (se 2 (by rfl) ⟨1859523, by rfl⟩ : syracuseStep 4958729 = 3719047) B3719047
theorem B3305819 : Blo 2115435 3305819 := bstep (se 1 (by rfl) ⟨2479364, by rfl⟩ : syracuseStep 3305819 = 4958729) B4958729
theorem B8815517 : Blo 2115435 8815517 := bstep (se 3 (by rfl) ⟨1652909, by rfl⟩ : syracuseStep 8815517 = 3305819) B3305819
theorem B5877011 : Blo 2115435 5877011 := bstep (se 1 (by rfl) ⟨4407758, by rfl⟩ : syracuseStep 5877011 = 8815517) B8815517
theorem B3918007 : Blo 2115435 3918007 := bstep (se 1 (by rfl) ⟨2938505, by rfl⟩ : syracuseStep 3918007 = 5877011) B5877011
theorem B20896037 : Blo 2115435 20896037 := bstep (se 4 (by rfl) ⟨1959003, by rfl⟩ : syracuseStep 20896037 = 3918007) B3918007
theorem B891564245 : Blo 2115435 891564245 := bstep (se 7 (by rfl) ⟨10448018, by rfl⟩ : syracuseStep 891564245 = 20896037) B20896037
theorem B594376163 : Blo 2115435 594376163 := bstep (se 1 (by rfl) ⟨445782122, by rfl⟩ : syracuseStep 594376163 = 891564245) B891564245
theorem B396250775 : Blo 2115435 396250775 := bstep (se 1 (by rfl) ⟨297188081, by rfl⟩ : syracuseStep 396250775 = 594376163) B594376163
theorem B264167183 : Blo 2115435 264167183 := bstep (se 1 (by rfl) ⟨198125387, by rfl⟩ : syracuseStep 264167183 = 396250775) B396250775
theorem B176111455 : Blo 2115435 176111455 := bstep (se 1 (by rfl) ⟨132083591, by rfl⟩ : syracuseStep 176111455 = 264167183) B264167183
theorem B234815273 : Blo 2115435 234815273 := bstep (se 2 (by rfl) ⟨88055727, by rfl⟩ : syracuseStep 234815273 = 176111455) B176111455
theorem B156543515 : Blo 2115435 156543515 := bstep (se 1 (by rfl) ⟨117407636, by rfl⟩ : syracuseStep 156543515 = 234815273) B234815273
theorem B104362343 : Blo 2115435 104362343 := bstep (se 1 (by rfl) ⟨78271757, by rfl⟩ : syracuseStep 104362343 = 156543515) B156543515
theorem B69574895 : Blo 2115435 69574895 := bstep (se 1 (by rfl) ⟨52181171, by rfl⟩ : syracuseStep 69574895 = 104362343) B104362343
theorem B46383263 : Blo 2115435 46383263 := bstep (se 1 (by rfl) ⟨34787447, by rfl⟩ : syracuseStep 46383263 = 69574895) B69574895
theorem B30922175 : Blo 2115435 30922175 := bstep (se 1 (by rfl) ⟨23191631, by rfl⟩ : syracuseStep 30922175 = 46383263) B46383263
theorem B20614783 : Blo 2115435 20614783 := bstep (se 1 (by rfl) ⟨15461087, by rfl⟩ : syracuseStep 20614783 = 30922175) B30922175
theorem B27486377 : Blo 2115435 27486377 := bstep (se 2 (by rfl) ⟨10307391, by rfl⟩ : syracuseStep 27486377 = 20614783) B20614783
theorem B18324251 : Blo 2115435 18324251 := bstep (se 1 (by rfl) ⟨13743188, by rfl⟩ : syracuseStep 18324251 = 27486377) B27486377
theorem B12216167 : Blo 2115435 12216167 := bstep (se 1 (by rfl) ⟨9162125, by rfl⟩ : syracuseStep 12216167 = 18324251) B18324251
theorem B8144111 : Blo 2115435 8144111 := bstep (se 1 (by rfl) ⟨6108083, by rfl⟩ : syracuseStep 8144111 = 12216167) B12216167
theorem B21717629 : Blo 2115435 21717629 := bstep (se 3 (by rfl) ⟨4072055, by rfl⟩ : syracuseStep 21717629 = 8144111) B8144111
theorem B14478419 : Blo 2115435 14478419 := bstep (se 1 (by rfl) ⟨10858814, by rfl⟩ : syracuseStep 14478419 = 21717629) B21717629
theorem B9652279 : Blo 2115435 9652279 := bstep (se 1 (by rfl) ⟨7239209, by rfl⟩ : syracuseStep 9652279 = 14478419) B14478419
theorem B12869705 : Blo 2115435 12869705 := bstep (se 2 (by rfl) ⟨4826139, by rfl⟩ : syracuseStep 12869705 = 9652279) B9652279
theorem B8579803 : Blo 2115435 8579803 := bstep (se 1 (by rfl) ⟨6434852, by rfl⟩ : syracuseStep 8579803 = 12869705) B12869705
theorem B11439737 : Blo 2115435 11439737 := bstep (se 2 (by rfl) ⟨4289901, by rfl⟩ : syracuseStep 11439737 = 8579803) B8579803
theorem B7626491 : Blo 2115435 7626491 := bstep (se 1 (by rfl) ⟨5719868, by rfl⟩ : syracuseStep 7626491 = 11439737) B11439737
theorem B5084327 : Blo 2115435 5084327 := bstep (se 1 (by rfl) ⟨3813245, by rfl⟩ : syracuseStep 5084327 = 7626491) B7626491
theorem B13558205 : Blo 2115435 13558205 := bstep (se 3 (by rfl) ⟨2542163, by rfl⟩ : syracuseStep 13558205 = 5084327) B5084327
theorem B9038803 : Blo 2115435 9038803 := bstep (se 1 (by rfl) ⟨6779102, by rfl⟩ : syracuseStep 9038803 = 13558205) B13558205
theorem B12051737 : Blo 2115435 12051737 := bstep (se 2 (by rfl) ⟨4519401, by rfl⟩ : syracuseStep 12051737 = 9038803) B9038803
theorem B8034491 : Blo 2115435 8034491 := bstep (se 1 (by rfl) ⟨6025868, by rfl⟩ : syracuseStep 8034491 = 12051737) B12051737
theorem B5356327 : Blo 2115435 5356327 := bstep (se 1 (by rfl) ⟨4017245, by rfl⟩ : syracuseStep 5356327 = 8034491) B8034491
theorem B7141769 : Blo 2115435 7141769 := bstep (se 2 (by rfl) ⟨2678163, by rfl⟩ : syracuseStep 7141769 = 5356327) B5356327
theorem B4761179 : Blo 2115435 4761179 := bstep (se 1 (by rfl) ⟨3570884, by rfl⟩ : syracuseStep 4761179 = 7141769) B7141769
theorem B3174119 : Blo 2115435 3174119 := bstep (se 1 (by rfl) ⟨2380589, by rfl⟩ : syracuseStep 3174119 = 4761179) B4761179
theorem B2116079 : Blo 2115435 2116079 := bstep (se 1 (by rfl) ⟨1587059, by rfl⟩ : syracuseStep 2116079 = 3174119) B3174119
theorem B3174125 : Blo 2115435 3174125 := bbase (se 3 (by rfl) ⟨595148, by rfl⟩ : syracuseStep 3174125 = 1190297) (by norm_num)
theorem B2116083 : Blo 2115435 2116083 := bstep (se 1 (by rfl) ⟨1587062, by rfl⟩ : syracuseStep 2116083 = 3174125) B3174125
theorem B4761197 : Blo 2115435 4761197 := bbase (se 3 (by rfl) ⟨892724, by rfl⟩ : syracuseStep 4761197 = 1785449) (by norm_num)
theorem B3174131 : Blo 2115435 3174131 := bstep (se 1 (by rfl) ⟨2380598, by rfl⟩ : syracuseStep 3174131 = 4761197) B4761197
theorem B2116087 : Blo 2115435 2116087 := bstep (se 1 (by rfl) ⟨1587065, by rfl⟩ : syracuseStep 2116087 = 3174131) B3174131
theorem B4017269 : Blo 2115435 4017269 := bbase (se 5 (by rfl) ⟨188309, by rfl⟩ : syracuseStep 4017269 = 376619) (by norm_num)
theorem B2678179 : Blo 2115435 2678179 := bstep (se 1 (by rfl) ⟨2008634, by rfl⟩ : syracuseStep 2678179 = 4017269) B4017269
theorem B3570905 : Blo 2115435 3570905 := bstep (se 2 (by rfl) ⟨1339089, by rfl⟩ : syracuseStep 3570905 = 2678179) B2678179
theorem B2380603 : Blo 2115435 2380603 := bstep (se 1 (by rfl) ⟨1785452, by rfl⟩ : syracuseStep 2380603 = 3570905) B3570905
theorem B3174137 : Blo 2115435 3174137 := bstep (se 2 (by rfl) ⟨1190301, by rfl⟩ : syracuseStep 3174137 = 2380603) B2380603
theorem B2116091 : Blo 2115435 2116091 := bstep (se 1 (by rfl) ⟨1587068, by rfl⟩ : syracuseStep 2116091 = 3174137) B3174137
theorem B32205397 : Blo 2115435 32205397 := bbase (se 8 (by rfl) ⟨188703, by rfl⟩ : syracuseStep 32205397 = 377407) (by norm_num)
theorem B42940529 : Blo 2115435 42940529 := bstep (se 2 (by rfl) ⟨16102698, by rfl⟩ : syracuseStep 42940529 = 32205397) B32205397
theorem B28627019 : Blo 2115435 28627019 := bstep (se 1 (by rfl) ⟨21470264, by rfl⟩ : syracuseStep 28627019 = 42940529) B42940529
theorem B19084679 : Blo 2115435 19084679 := bstep (se 1 (by rfl) ⟨14313509, by rfl⟩ : syracuseStep 19084679 = 28627019) B28627019
theorem B12723119 : Blo 2115435 12723119 := bstep (se 1 (by rfl) ⟨9542339, by rfl⟩ : syracuseStep 12723119 = 19084679) B19084679
theorem B8482079 : Blo 2115435 8482079 := bstep (se 1 (by rfl) ⟨6361559, by rfl⟩ : syracuseStep 8482079 = 12723119) B12723119
theorem B5654719 : Blo 2115435 5654719 := bstep (se 1 (by rfl) ⟨4241039, by rfl⟩ : syracuseStep 5654719 = 8482079) B8482079
theorem B7539625 : Blo 2115435 7539625 := bstep (se 2 (by rfl) ⟨2827359, by rfl⟩ : syracuseStep 7539625 = 5654719) B5654719
theorem B10052833 : Blo 2115435 10052833 := bstep (se 2 (by rfl) ⟨3769812, by rfl⟩ : syracuseStep 10052833 = 7539625) B7539625
theorem B13403777 : Blo 2115435 13403777 := bstep (se 2 (by rfl) ⟨5026416, by rfl⟩ : syracuseStep 13403777 = 10052833) B10052833
theorem B142973621 : Blo 2115435 142973621 := bstep (se 5 (by rfl) ⟨6701888, by rfl⟩ : syracuseStep 142973621 = 13403777) B13403777
theorem B95315747 : Blo 2115435 95315747 := bstep (se 1 (by rfl) ⟨71486810, by rfl⟩ : syracuseStep 95315747 = 142973621) B142973621
theorem B1016701301 : Blo 2115435 1016701301 := bstep (se 5 (by rfl) ⟨47657873, by rfl⟩ : syracuseStep 1016701301 = 95315747) B95315747
theorem B677800867 : Blo 2115435 677800867 := bstep (se 1 (by rfl) ⟨508350650, by rfl⟩ : syracuseStep 677800867 = 1016701301) B1016701301
theorem B903734489 : Blo 2115435 903734489 := bstep (se 2 (by rfl) ⟨338900433, by rfl⟩ : syracuseStep 903734489 = 677800867) B677800867
theorem B602489659 : Blo 2115435 602489659 := bstep (se 1 (by rfl) ⟨451867244, by rfl⟩ : syracuseStep 602489659 = 903734489) B903734489
theorem B803319545 : Blo 2115435 803319545 := bstep (se 2 (by rfl) ⟨301244829, by rfl⟩ : syracuseStep 803319545 = 602489659) B602489659
theorem B2142185453 : Blo 2115435 2142185453 := bstep (se 3 (by rfl) ⟨401659772, by rfl⟩ : syracuseStep 2142185453 = 803319545) B803319545
theorem B1428123635 : Blo 2115435 1428123635 := bstep (se 1 (by rfl) ⟨1071092726, by rfl⟩ : syracuseStep 1428123635 = 2142185453) B2142185453
theorem B952082423 : Blo 2115435 952082423 := bstep (se 1 (by rfl) ⟨714061817, by rfl⟩ : syracuseStep 952082423 = 1428123635) B1428123635
theorem B634721615 : Blo 2115435 634721615 := bstep (se 1 (by rfl) ⟨476041211, by rfl⟩ : syracuseStep 634721615 = 952082423) B952082423
theorem B423147743 : Blo 2115435 423147743 := bstep (se 1 (by rfl) ⟨317360807, by rfl⟩ : syracuseStep 423147743 = 634721615) B634721615
theorem B282098495 : Blo 2115435 282098495 := bstep (se 1 (by rfl) ⟨211573871, by rfl⟩ : syracuseStep 282098495 = 423147743) B423147743
theorem B752262653 : Blo 2115435 752262653 := bstep (se 3 (by rfl) ⟨141049247, by rfl⟩ : syracuseStep 752262653 = 282098495) B282098495
theorem B501508435 : Blo 2115435 501508435 := bstep (se 1 (by rfl) ⟨376131326, by rfl⟩ : syracuseStep 501508435 = 752262653) B752262653
theorem B668677913 : Blo 2115435 668677913 := bstep (se 2 (by rfl) ⟨250754217, by rfl⟩ : syracuseStep 668677913 = 501508435) B501508435
theorem B445785275 : Blo 2115435 445785275 := bstep (se 1 (by rfl) ⟨334338956, by rfl⟩ : syracuseStep 445785275 = 668677913) B668677913
theorem B297190183 : Blo 2115435 297190183 := bstep (se 1 (by rfl) ⟨222892637, by rfl⟩ : syracuseStep 297190183 = 445785275) B445785275
theorem B396253577 : Blo 2115435 396253577 := bstep (se 2 (by rfl) ⟨148595091, by rfl⟩ : syracuseStep 396253577 = 297190183) B297190183
theorem B1056676205 : Blo 2115435 1056676205 := bstep (se 3 (by rfl) ⟨198126788, by rfl⟩ : syracuseStep 1056676205 = 396253577) B396253577
theorem B2817803213 : Blo 2115435 2817803213 := bstep (se 3 (by rfl) ⟨528338102, by rfl⟩ : syracuseStep 2817803213 = 1056676205) B1056676205
theorem B1878535475 : Blo 2115435 1878535475 := bstep (se 1 (by rfl) ⟨1408901606, by rfl⟩ : syracuseStep 1878535475 = 2817803213) B2817803213
theorem B1252356983 : Blo 2115435 1252356983 := bstep (se 1 (by rfl) ⟨939267737, by rfl⟩ : syracuseStep 1252356983 = 1878535475) B1878535475
theorem B834904655 : Blo 2115435 834904655 := bstep (se 1 (by rfl) ⟨626178491, by rfl⟩ : syracuseStep 834904655 = 1252356983) B1252356983
theorem B556603103 : Blo 2115435 556603103 := bstep (se 1 (by rfl) ⟨417452327, by rfl⟩ : syracuseStep 556603103 = 834904655) B834904655
theorem B371068735 : Blo 2115435 371068735 := bstep (se 1 (by rfl) ⟨278301551, by rfl⟩ : syracuseStep 371068735 = 556603103) B556603103
theorem B494758313 : Blo 2115435 494758313 := bstep (se 2 (by rfl) ⟨185534367, by rfl⟩ : syracuseStep 494758313 = 371068735) B371068735
theorem B329838875 : Blo 2115435 329838875 := bstep (se 1 (by rfl) ⟨247379156, by rfl⟩ : syracuseStep 329838875 = 494758313) B494758313
theorem B219892583 : Blo 2115435 219892583 := bstep (se 1 (by rfl) ⟨164919437, by rfl⟩ : syracuseStep 219892583 = 329838875) B329838875
theorem B146595055 : Blo 2115435 146595055 := bstep (se 1 (by rfl) ⟨109946291, by rfl⟩ : syracuseStep 146595055 = 219892583) B219892583
theorem B195460073 : Blo 2115435 195460073 := bstep (se 2 (by rfl) ⟨73297527, by rfl⟩ : syracuseStep 195460073 = 146595055) B146595055
theorem B130306715 : Blo 2115435 130306715 := bstep (se 1 (by rfl) ⟨97730036, by rfl⟩ : syracuseStep 130306715 = 195460073) B195460073
theorem B86871143 : Blo 2115435 86871143 := bstep (se 1 (by rfl) ⟨65153357, by rfl⟩ : syracuseStep 86871143 = 130306715) B130306715
theorem B231656381 : Blo 2115435 231656381 := bstep (se 3 (by rfl) ⟨43435571, by rfl⟩ : syracuseStep 231656381 = 86871143) B86871143
theorem B154437587 : Blo 2115435 154437587 := bstep (se 1 (by rfl) ⟨115828190, by rfl⟩ : syracuseStep 154437587 = 231656381) B231656381
theorem B102958391 : Blo 2115435 102958391 := bstep (se 1 (by rfl) ⟨77218793, by rfl⟩ : syracuseStep 102958391 = 154437587) B154437587
theorem B68638927 : Blo 2115435 68638927 := bstep (se 1 (by rfl) ⟨51479195, by rfl⟩ : syracuseStep 68638927 = 102958391) B102958391
theorem B91518569 : Blo 2115435 91518569 := bstep (se 2 (by rfl) ⟨34319463, by rfl⟩ : syracuseStep 91518569 = 68638927) B68638927
theorem B61012379 : Blo 2115435 61012379 := bstep (se 1 (by rfl) ⟨45759284, by rfl⟩ : syracuseStep 61012379 = 91518569) B91518569
theorem B40674919 : Blo 2115435 40674919 := bstep (se 1 (by rfl) ⟨30506189, by rfl⟩ : syracuseStep 40674919 = 61012379) B61012379
theorem B54233225 : Blo 2115435 54233225 := bstep (se 2 (by rfl) ⟨20337459, by rfl⟩ : syracuseStep 54233225 = 40674919) B40674919
theorem B36155483 : Blo 2115435 36155483 := bstep (se 1 (by rfl) ⟨27116612, by rfl⟩ : syracuseStep 36155483 = 54233225) B54233225
theorem B24103655 : Blo 2115435 24103655 := bstep (se 1 (by rfl) ⟨18077741, by rfl⟩ : syracuseStep 24103655 = 36155483) B36155483
theorem B16069103 : Blo 2115435 16069103 := bstep (se 1 (by rfl) ⟨12051827, by rfl⟩ : syracuseStep 16069103 = 24103655) B24103655
theorem B10712735 : Blo 2115435 10712735 := bstep (se 1 (by rfl) ⟨8034551, by rfl⟩ : syracuseStep 10712735 = 16069103) B16069103
theorem B7141823 : Blo 2115435 7141823 := bstep (se 1 (by rfl) ⟨5356367, by rfl⟩ : syracuseStep 7141823 = 10712735) B10712735
theorem B4761215 : Blo 2115435 4761215 := bstep (se 1 (by rfl) ⟨3570911, by rfl⟩ : syracuseStep 4761215 = 7141823) B7141823
theorem B3174143 : Blo 2115435 3174143 := bstep (se 1 (by rfl) ⟨2380607, by rfl⟩ : syracuseStep 3174143 = 4761215) B4761215
theorem B2116095 : Blo 2115435 2116095 := bstep (se 1 (by rfl) ⟨1587071, by rfl⟩ : syracuseStep 2116095 = 3174143) B3174143
theorem B3174149 : Blo 2115435 3174149 := bbase (se 4 (by rfl) ⟨297576, by rfl⟩ : syracuseStep 3174149 = 595153) (by norm_num)
theorem B2116099 : Blo 2115435 2116099 := bstep (se 1 (by rfl) ⟨1587074, by rfl⟩ : syracuseStep 2116099 = 3174149) B3174149
theorem B3570925 : Blo 2115435 3570925 := bbase (se 3 (by rfl) ⟨669548, by rfl⟩ : syracuseStep 3570925 = 1339097) (by norm_num)
theorem B4761233 : Blo 2115435 4761233 := bstep (se 2 (by rfl) ⟨1785462, by rfl⟩ : syracuseStep 4761233 = 3570925) B3570925
theorem B3174155 : Blo 2115435 3174155 := bstep (se 1 (by rfl) ⟨2380616, by rfl⟩ : syracuseStep 3174155 = 4761233) B4761233
theorem B2116103 : Blo 2115435 2116103 := bstep (se 1 (by rfl) ⟨1587077, by rfl⟩ : syracuseStep 2116103 = 3174155) B3174155
theorem B2380621 : Blo 2115435 2380621 := bbase (se 3 (by rfl) ⟨446366, by rfl⟩ : syracuseStep 2380621 = 892733) (by norm_num)
theorem B3174161 : Blo 2115435 3174161 := bstep (se 2 (by rfl) ⟨1190310, by rfl⟩ : syracuseStep 3174161 = 2380621) B2380621
theorem B2116107 : Blo 2115435 2116107 := bstep (se 1 (by rfl) ⟨1587080, by rfl⟩ : syracuseStep 2116107 = 3174161) B3174161
theorem B7141877 : Blo 2115435 7141877 := bbase (se 5 (by rfl) ⟨334775, by rfl⟩ : syracuseStep 7141877 = 669551) (by norm_num)
theorem B4761251 : Blo 2115435 4761251 := bstep (se 1 (by rfl) ⟨3570938, by rfl⟩ : syracuseStep 4761251 = 7141877) B7141877
theorem B3174167 : Blo 2115435 3174167 := bstep (se 1 (by rfl) ⟨2380625, by rfl⟩ : syracuseStep 3174167 = 4761251) B4761251
theorem B2116111 : Blo 2115435 2116111 := bstep (se 1 (by rfl) ⟨1587083, by rfl⟩ : syracuseStep 2116111 = 3174167) B3174167
theorem B3174173 : Blo 2115435 3174173 := bbase (se 3 (by rfl) ⟨595157, by rfl⟩ : syracuseStep 3174173 = 1190315) (by norm_num)
theorem B2116115 : Blo 2115435 2116115 := bstep (se 1 (by rfl) ⟨1587086, by rfl⟩ : syracuseStep 2116115 = 3174173) B3174173
theorem B4761269 : Blo 2115435 4761269 := bbase (se 5 (by rfl) ⟨223184, by rfl⟩ : syracuseStep 4761269 = 446369) (by norm_num)
theorem B3174179 : Blo 2115435 3174179 := bstep (se 1 (by rfl) ⟨2380634, by rfl⟩ : syracuseStep 3174179 = 4761269) B4761269
theorem B2116119 : Blo 2115435 2116119 := bstep (se 1 (by rfl) ⟨1587089, by rfl⟩ : syracuseStep 2116119 = 3174179) B3174179
theorem B12051989 : Blo 2115435 12051989 := bbase (se 6 (by rfl) ⟨282468, by rfl⟩ : syracuseStep 12051989 = 564937) (by norm_num)
theorem B8034659 : Blo 2115435 8034659 := bstep (se 1 (by rfl) ⟨6025994, by rfl⟩ : syracuseStep 8034659 = 12051989) B12051989
theorem B5356439 : Blo 2115435 5356439 := bstep (se 1 (by rfl) ⟨4017329, by rfl⟩ : syracuseStep 5356439 = 8034659) B8034659
theorem B3570959 : Blo 2115435 3570959 := bstep (se 1 (by rfl) ⟨2678219, by rfl⟩ : syracuseStep 3570959 = 5356439) B5356439
theorem B2380639 : Blo 2115435 2380639 := bstep (se 1 (by rfl) ⟨1785479, by rfl⟩ : syracuseStep 2380639 = 3570959) B3570959
theorem B3174185 : Blo 2115435 3174185 := bstep (se 2 (by rfl) ⟨1190319, by rfl⟩ : syracuseStep 3174185 = 2380639) B2380639
theorem B2116123 : Blo 2115435 2116123 := bstep (se 1 (by rfl) ⟨1587092, by rfl⟩ : syracuseStep 2116123 = 3174185) B3174185
theorem B6026005 : Blo 2115435 6026005 := bbase (se 6 (by rfl) ⟨141234, by rfl⟩ : syracuseStep 6026005 = 282469) (by norm_num)
theorem B8034673 : Blo 2115435 8034673 := bstep (se 2 (by rfl) ⟨3013002, by rfl⟩ : syracuseStep 8034673 = 6026005) B6026005
theorem B10712897 : Blo 2115435 10712897 := bstep (se 2 (by rfl) ⟨4017336, by rfl⟩ : syracuseStep 10712897 = 8034673) B8034673
theorem B7141931 : Blo 2115435 7141931 := bstep (se 1 (by rfl) ⟨5356448, by rfl⟩ : syracuseStep 7141931 = 10712897) B10712897
theorem B4761287 : Blo 2115435 4761287 := bstep (se 1 (by rfl) ⟨3570965, by rfl⟩ : syracuseStep 4761287 = 7141931) B7141931
theorem B3174191 : Blo 2115435 3174191 := bstep (se 1 (by rfl) ⟨2380643, by rfl⟩ : syracuseStep 3174191 = 4761287) B4761287
theorem B2116127 : Blo 2115435 2116127 := bstep (se 1 (by rfl) ⟨1587095, by rfl⟩ : syracuseStep 2116127 = 3174191) B3174191
theorem B3174197 : Blo 2115435 3174197 := bbase (se 5 (by rfl) ⟨148790, by rfl⟩ : syracuseStep 3174197 = 297581) (by norm_num)
theorem B2116131 : Blo 2115435 2116131 := bstep (se 1 (by rfl) ⟨1587098, by rfl⟩ : syracuseStep 2116131 = 3174197) B3174197
theorem B5356469 : Blo 2115435 5356469 := bbase (se 5 (by rfl) ⟨251084, by rfl⟩ : syracuseStep 5356469 = 502169) (by norm_num)
theorem B3570979 : Blo 2115435 3570979 := bstep (se 1 (by rfl) ⟨2678234, by rfl⟩ : syracuseStep 3570979 = 5356469) B5356469
theorem B4761305 : Blo 2115435 4761305 := bstep (se 2 (by rfl) ⟨1785489, by rfl⟩ : syracuseStep 4761305 = 3570979) B3570979
theorem B3174203 : Blo 2115435 3174203 := bstep (se 1 (by rfl) ⟨2380652, by rfl⟩ : syracuseStep 3174203 = 4761305) B4761305
theorem B2116135 : Blo 2115435 2116135 := bstep (se 1 (by rfl) ⟨1587101, by rfl⟩ : syracuseStep 2116135 = 3174203) B3174203
theorem B2380657 : Blo 2115435 2380657 := bbase (se 2 (by rfl) ⟨892746, by rfl⟩ : syracuseStep 2380657 = 1785493) (by norm_num)
theorem B3174209 : Blo 2115435 3174209 := bstep (se 2 (by rfl) ⟨1190328, by rfl⟩ : syracuseStep 3174209 = 2380657) B2380657
theorem B2116139 : Blo 2115435 2116139 := bstep (se 1 (by rfl) ⟨1587104, by rfl⟩ : syracuseStep 2116139 = 3174209) B3174209
theorem B9039077 : Blo 2115435 9039077 := bbase (se 4 (by rfl) ⟨847413, by rfl⟩ : syracuseStep 9039077 = 1694827) (by norm_num)
theorem B6026051 : Blo 2115435 6026051 := bstep (se 1 (by rfl) ⟨4519538, by rfl⟩ : syracuseStep 6026051 = 9039077) B9039077
theorem B4017367 : Blo 2115435 4017367 := bstep (se 1 (by rfl) ⟨3013025, by rfl⟩ : syracuseStep 4017367 = 6026051) B6026051
theorem B5356489 : Blo 2115435 5356489 := bstep (se 2 (by rfl) ⟨2008683, by rfl⟩ : syracuseStep 5356489 = 4017367) B4017367
theorem B7141985 : Blo 2115435 7141985 := bstep (se 2 (by rfl) ⟨2678244, by rfl⟩ : syracuseStep 7141985 = 5356489) B5356489
theorem B4761323 : Blo 2115435 4761323 := bstep (se 1 (by rfl) ⟨3570992, by rfl⟩ : syracuseStep 4761323 = 7141985) B7141985
theorem B3174215 : Blo 2115435 3174215 := bstep (se 1 (by rfl) ⟨2380661, by rfl⟩ : syracuseStep 3174215 = 4761323) B4761323
theorem B2116143 : Blo 2115435 2116143 := bstep (se 1 (by rfl) ⟨1587107, by rfl⟩ : syracuseStep 2116143 = 3174215) B3174215
theorem B3174221 : Blo 2115435 3174221 := bbase (se 3 (by rfl) ⟨595166, by rfl⟩ : syracuseStep 3174221 = 1190333) (by norm_num)
theorem B2116147 : Blo 2115435 2116147 := bstep (se 1 (by rfl) ⟨1587110, by rfl⟩ : syracuseStep 2116147 = 3174221) B3174221
theorem B4761341 : Blo 2115435 4761341 := bbase (se 3 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 4761341 = 1785503) (by norm_num)
theorem B3174227 : Blo 2115435 3174227 := bstep (se 1 (by rfl) ⟨2380670, by rfl⟩ : syracuseStep 3174227 = 4761341) B4761341
theorem B2116151 : Blo 2115435 2116151 := bstep (se 1 (by rfl) ⟨1587113, by rfl⟩ : syracuseStep 2116151 = 3174227) B3174227
theorem B3571013 : Blo 2115435 3571013 := bbase (se 4 (by rfl) ⟨334782, by rfl⟩ : syracuseStep 3571013 = 669565) (by norm_num)
theorem B2380675 : Blo 2115435 2380675 := bstep (se 1 (by rfl) ⟨1785506, by rfl⟩ : syracuseStep 2380675 = 3571013) B3571013
theorem B3174233 : Blo 2115435 3174233 := bstep (se 2 (by rfl) ⟨1190337, by rfl⟩ : syracuseStep 3174233 = 2380675) B2380675
theorem B2116155 : Blo 2115435 2116155 := bstep (se 1 (by rfl) ⟨1587116, by rfl⟩ : syracuseStep 2116155 = 3174233) B3174233
theorem B16069589 : Blo 2115435 16069589 := bbase (se 7 (by rfl) ⟨188315, by rfl⟩ : syracuseStep 16069589 = 376631) (by norm_num)
theorem B10713059 : Blo 2115435 10713059 := bstep (se 1 (by rfl) ⟨8034794, by rfl⟩ : syracuseStep 10713059 = 16069589) B16069589
theorem B7142039 : Blo 2115435 7142039 := bstep (se 1 (by rfl) ⟨5356529, by rfl⟩ : syracuseStep 7142039 = 10713059) B10713059
theorem B4761359 : Blo 2115435 4761359 := bstep (se 1 (by rfl) ⟨3571019, by rfl⟩ : syracuseStep 4761359 = 7142039) B7142039
theorem B3174239 : Blo 2115435 3174239 := bstep (se 1 (by rfl) ⟨2380679, by rfl⟩ : syracuseStep 3174239 = 4761359) B4761359
theorem B2116159 : Blo 2115435 2116159 := bstep (se 1 (by rfl) ⟨1587119, by rfl⟩ : syracuseStep 2116159 = 3174239) B3174239
theorem B3174245 : Blo 2115435 3174245 := bbase (se 4 (by rfl) ⟨297585, by rfl⟩ : syracuseStep 3174245 = 595171) (by norm_num)
theorem B2116163 : Blo 2115435 2116163 := bstep (se 1 (by rfl) ⟨1587122, by rfl⟩ : syracuseStep 2116163 = 3174245) B3174245
theorem B4017413 : Blo 2115435 4017413 := bbase (se 4 (by rfl) ⟨376632, by rfl⟩ : syracuseStep 4017413 = 753265) (by norm_num)
theorem B2678275 : Blo 2115435 2678275 := bstep (se 1 (by rfl) ⟨2008706, by rfl⟩ : syracuseStep 2678275 = 4017413) B4017413
theorem B3571033 : Blo 2115435 3571033 := bstep (se 2 (by rfl) ⟨1339137, by rfl⟩ : syracuseStep 3571033 = 2678275) B2678275
theorem B4761377 : Blo 2115435 4761377 := bstep (se 2 (by rfl) ⟨1785516, by rfl⟩ : syracuseStep 4761377 = 3571033) B3571033
theorem B3174251 : Blo 2115435 3174251 := bstep (se 1 (by rfl) ⟨2380688, by rfl⟩ : syracuseStep 3174251 = 4761377) B4761377
theorem B2116167 : Blo 2115435 2116167 := bstep (se 1 (by rfl) ⟨1587125, by rfl⟩ : syracuseStep 2116167 = 3174251) B3174251
theorem B2380693 : Blo 2115435 2380693 := bbase (se 6 (by rfl) ⟨55797, by rfl⟩ : syracuseStep 2380693 = 111595) (by norm_num)
theorem B3174257 : Blo 2115435 3174257 := bstep (se 2 (by rfl) ⟨1190346, by rfl⟩ : syracuseStep 3174257 = 2380693) B2380693
theorem B2116171 : Blo 2115435 2116171 := bstep (se 1 (by rfl) ⟨1587128, by rfl⟩ : syracuseStep 2116171 = 3174257) B3174257
theorem B2678285 : Blo 2115435 2678285 := bbase (se 3 (by rfl) ⟨502178, by rfl⟩ : syracuseStep 2678285 = 1004357) (by norm_num)
theorem B7142093 : Blo 2115435 7142093 := bstep (se 3 (by rfl) ⟨1339142, by rfl⟩ : syracuseStep 7142093 = 2678285) B2678285
theorem B4761395 : Blo 2115435 4761395 := bstep (se 1 (by rfl) ⟨3571046, by rfl⟩ : syracuseStep 4761395 = 7142093) B7142093
theorem B3174263 : Blo 2115435 3174263 := bstep (se 1 (by rfl) ⟨2380697, by rfl⟩ : syracuseStep 3174263 = 4761395) B4761395
theorem B2116175 : Blo 2115435 2116175 := bstep (se 1 (by rfl) ⟨1587131, by rfl⟩ : syracuseStep 2116175 = 3174263) B3174263
theorem B3174269 : Blo 2115435 3174269 := bbase (se 3 (by rfl) ⟨595175, by rfl⟩ : syracuseStep 3174269 = 1190351) (by norm_num)
theorem B2116179 : Blo 2115435 2116179 := bstep (se 1 (by rfl) ⟨1587134, by rfl⟩ : syracuseStep 2116179 = 3174269) B3174269
theorem B4761413 : Blo 2115435 4761413 := bbase (se 4 (by rfl) ⟨446382, by rfl⟩ : syracuseStep 4761413 = 892765) (by norm_num)
theorem B3174275 : Blo 2115435 3174275 := bstep (se 1 (by rfl) ⟨2380706, by rfl⟩ : syracuseStep 3174275 = 4761413) B4761413
theorem B2116183 : Blo 2115435 2116183 := bstep (se 1 (by rfl) ⟨1587137, by rfl⟩ : syracuseStep 2116183 = 3174275) B3174275
theorem B3389725 : Blo 2115435 3389725 := bbase (se 3 (by rfl) ⟨635573, by rfl⟩ : syracuseStep 3389725 = 1271147) (by norm_num)
theorem B4519633 : Blo 2115435 4519633 := bstep (se 2 (by rfl) ⟨1694862, by rfl⟩ : syracuseStep 4519633 = 3389725) B3389725
theorem B6026177 : Blo 2115435 6026177 := bstep (se 2 (by rfl) ⟨2259816, by rfl⟩ : syracuseStep 6026177 = 4519633) B4519633
theorem B4017451 : Blo 2115435 4017451 := bstep (se 1 (by rfl) ⟨3013088, by rfl⟩ : syracuseStep 4017451 = 6026177) B6026177
theorem B5356601 : Blo 2115435 5356601 := bstep (se 2 (by rfl) ⟨2008725, by rfl⟩ : syracuseStep 5356601 = 4017451) B4017451
theorem B3571067 : Blo 2115435 3571067 := bstep (se 1 (by rfl) ⟨2678300, by rfl⟩ : syracuseStep 3571067 = 5356601) B5356601
theorem B2380711 : Blo 2115435 2380711 := bstep (se 1 (by rfl) ⟨1785533, by rfl⟩ : syracuseStep 2380711 = 3571067) B3571067
theorem B3174281 : Blo 2115435 3174281 := bstep (se 2 (by rfl) ⟨1190355, by rfl⟩ : syracuseStep 3174281 = 2380711) B2380711
theorem B2116187 : Blo 2115435 2116187 := bstep (se 1 (by rfl) ⟨1587140, by rfl⟩ : syracuseStep 2116187 = 3174281) B3174281
theorem B10713221 : Blo 2115435 10713221 := bbase (se 4 (by rfl) ⟨1004364, by rfl⟩ : syracuseStep 10713221 = 2008729) (by norm_num)
theorem B7142147 : Blo 2115435 7142147 := bstep (se 1 (by rfl) ⟨5356610, by rfl⟩ : syracuseStep 7142147 = 10713221) B10713221
theorem B4761431 : Blo 2115435 4761431 := bstep (se 1 (by rfl) ⟨3571073, by rfl⟩ : syracuseStep 4761431 = 7142147) B7142147
theorem B3174287 : Blo 2115435 3174287 := bstep (se 1 (by rfl) ⟨2380715, by rfl⟩ : syracuseStep 3174287 = 4761431) B4761431
theorem B2116191 : Blo 2115435 2116191 := bstep (se 1 (by rfl) ⟨1587143, by rfl⟩ : syracuseStep 2116191 = 3174287) B3174287
theorem B3174293 : Blo 2115435 3174293 := bbase (se 6 (by rfl) ⟨74397, by rfl⟩ : syracuseStep 3174293 = 148795) (by norm_num)
theorem B2116195 : Blo 2115435 2116195 := bstep (se 1 (by rfl) ⟨1587146, by rfl⟩ : syracuseStep 2116195 = 3174293) B3174293
theorem B2259829 : Blo 2115435 2259829 := bbase (se 5 (by rfl) ⟨105929, by rfl⟩ : syracuseStep 2259829 = 211859) (by norm_num)
theorem B12052421 : Blo 2115435 12052421 := bstep (se 4 (by rfl) ⟨1129914, by rfl⟩ : syracuseStep 12052421 = 2259829) B2259829
theorem B8034947 : Blo 2115435 8034947 := bstep (se 1 (by rfl) ⟨6026210, by rfl⟩ : syracuseStep 8034947 = 12052421) B12052421
theorem B5356631 : Blo 2115435 5356631 := bstep (se 1 (by rfl) ⟨4017473, by rfl⟩ : syracuseStep 5356631 = 8034947) B8034947
theorem B3571087 : Blo 2115435 3571087 := bstep (se 1 (by rfl) ⟨2678315, by rfl⟩ : syracuseStep 3571087 = 5356631) B5356631
theorem B4761449 : Blo 2115435 4761449 := bstep (se 2 (by rfl) ⟨1785543, by rfl⟩ : syracuseStep 4761449 = 3571087) B3571087
theorem B3174299 : Blo 2115435 3174299 := bstep (se 1 (by rfl) ⟨2380724, by rfl⟩ : syracuseStep 3174299 = 4761449) B4761449
theorem B2116199 : Blo 2115435 2116199 := bstep (se 1 (by rfl) ⟨1587149, by rfl⟩ : syracuseStep 2116199 = 3174299) B3174299
theorem B2380729 : Blo 2115435 2380729 := bbase (se 2 (by rfl) ⟨892773, by rfl⟩ : syracuseStep 2380729 = 1785547) (by norm_num)
theorem B3174305 : Blo 2115435 3174305 := bstep (se 2 (by rfl) ⟨1190364, by rfl⟩ : syracuseStep 3174305 = 2380729) B2380729
theorem B2116203 : Blo 2115435 2116203 := bstep (se 1 (by rfl) ⟨1587152, by rfl⟩ : syracuseStep 2116203 = 3174305) B3174305
theorem B12870485 : Blo 2115435 12870485 := bbase (se 9 (by rfl) ⟨37706, by rfl⟩ : syracuseStep 12870485 = 75413) (by norm_num)
theorem B8580323 : Blo 2115435 8580323 := bstep (se 1 (by rfl) ⟨6435242, by rfl⟩ : syracuseStep 8580323 = 12870485) B12870485
theorem B5720215 : Blo 2115435 5720215 := bstep (se 1 (by rfl) ⟨4290161, by rfl⟩ : syracuseStep 5720215 = 8580323) B8580323
theorem B7626953 : Blo 2115435 7626953 := bstep (se 2 (by rfl) ⟨2860107, by rfl⟩ : syracuseStep 7626953 = 5720215) B5720215
theorem B5084635 : Blo 2115435 5084635 := bstep (se 1 (by rfl) ⟨3813476, by rfl⟩ : syracuseStep 5084635 = 7626953) B7626953
theorem B6779513 : Blo 2115435 6779513 := bstep (se 2 (by rfl) ⟨2542317, by rfl⟩ : syracuseStep 6779513 = 5084635) B5084635
theorem B4519675 : Blo 2115435 4519675 := bstep (se 1 (by rfl) ⟨3389756, by rfl⟩ : syracuseStep 4519675 = 6779513) B6779513
theorem B6026233 : Blo 2115435 6026233 := bstep (se 2 (by rfl) ⟨2259837, by rfl⟩ : syracuseStep 6026233 = 4519675) B4519675
theorem B8034977 : Blo 2115435 8034977 := bstep (se 2 (by rfl) ⟨3013116, by rfl⟩ : syracuseStep 8034977 = 6026233) B6026233
theorem B5356651 : Blo 2115435 5356651 := bstep (se 1 (by rfl) ⟨4017488, by rfl⟩ : syracuseStep 5356651 = 8034977) B8034977
theorem B7142201 : Blo 2115435 7142201 := bstep (se 2 (by rfl) ⟨2678325, by rfl⟩ : syracuseStep 7142201 = 5356651) B5356651
theorem B4761467 : Blo 2115435 4761467 := bstep (se 1 (by rfl) ⟨3571100, by rfl⟩ : syracuseStep 4761467 = 7142201) B7142201
theorem B3174311 : Blo 2115435 3174311 := bstep (se 1 (by rfl) ⟨2380733, by rfl⟩ : syracuseStep 3174311 = 4761467) B4761467
theorem B2116207 : Blo 2115435 2116207 := bstep (se 1 (by rfl) ⟨1587155, by rfl⟩ : syracuseStep 2116207 = 3174311) B3174311
theorem B3174317 : Blo 2115435 3174317 := bbase (se 3 (by rfl) ⟨595184, by rfl⟩ : syracuseStep 3174317 = 1190369) (by norm_num)
theorem B2116211 : Blo 2115435 2116211 := bstep (se 1 (by rfl) ⟨1587158, by rfl⟩ : syracuseStep 2116211 = 3174317) B3174317
theorem B4761485 : Blo 2115435 4761485 := bbase (se 3 (by rfl) ⟨892778, by rfl⟩ : syracuseStep 4761485 = 1785557) (by norm_num)
theorem B3174323 : Blo 2115435 3174323 := bstep (se 1 (by rfl) ⟨2380742, by rfl⟩ : syracuseStep 3174323 = 4761485) B4761485
theorem B2116215 : Blo 2115435 2116215 := bstep (se 1 (by rfl) ⟨1587161, by rfl⟩ : syracuseStep 2116215 = 3174323) B3174323
theorem B2678341 : Blo 2115435 2678341 := bbase (se 4 (by rfl) ⟨251094, by rfl⟩ : syracuseStep 2678341 = 502189) (by norm_num)
theorem B3571121 : Blo 2115435 3571121 := bstep (se 2 (by rfl) ⟨1339170, by rfl⟩ : syracuseStep 3571121 = 2678341) B2678341
theorem B2380747 : Blo 2115435 2380747 := bstep (se 1 (by rfl) ⟨1785560, by rfl⟩ : syracuseStep 2380747 = 3571121) B3571121
theorem B3174329 : Blo 2115435 3174329 := bstep (se 2 (by rfl) ⟨1190373, by rfl⟩ : syracuseStep 3174329 = 2380747) B2380747
theorem B2116219 : Blo 2115435 2116219 := bstep (se 1 (by rfl) ⟨1587164, by rfl⟩ : syracuseStep 2116219 = 3174329) B3174329
theorem B3217645 : Blo 2115435 3217645 := bbase (se 3 (by rfl) ⟨603308, by rfl⟩ : syracuseStep 3217645 = 1206617) (by norm_num)
theorem B4290193 : Blo 2115435 4290193 := bstep (se 2 (by rfl) ⟨1608822, by rfl⟩ : syracuseStep 4290193 = 3217645) B3217645
theorem B5720257 : Blo 2115435 5720257 := bstep (se 2 (by rfl) ⟨2145096, by rfl⟩ : syracuseStep 5720257 = 4290193) B4290193
theorem B7627009 : Blo 2115435 7627009 := bstep (se 2 (by rfl) ⟨2860128, by rfl⟩ : syracuseStep 7627009 = 5720257) B5720257
theorem B10169345 : Blo 2115435 10169345 := bstep (se 2 (by rfl) ⟨3813504, by rfl⟩ : syracuseStep 10169345 = 7627009) B7627009
theorem B27118253 : Blo 2115435 27118253 := bstep (se 3 (by rfl) ⟨5084672, by rfl⟩ : syracuseStep 27118253 = 10169345) B10169345
theorem B18078835 : Blo 2115435 18078835 := bstep (se 1 (by rfl) ⟨13559126, by rfl⟩ : syracuseStep 18078835 = 27118253) B27118253
theorem B24105113 : Blo 2115435 24105113 := bstep (se 2 (by rfl) ⟨9039417, by rfl⟩ : syracuseStep 24105113 = 18078835) B18078835
theorem B16070075 : Blo 2115435 16070075 := bstep (se 1 (by rfl) ⟨12052556, by rfl⟩ : syracuseStep 16070075 = 24105113) B24105113
theorem B10713383 : Blo 2115435 10713383 := bstep (se 1 (by rfl) ⟨8035037, by rfl⟩ : syracuseStep 10713383 = 16070075) B16070075
theorem B7142255 : Blo 2115435 7142255 := bstep (se 1 (by rfl) ⟨5356691, by rfl⟩ : syracuseStep 7142255 = 10713383) B10713383
theorem B4761503 : Blo 2115435 4761503 := bstep (se 1 (by rfl) ⟨3571127, by rfl⟩ : syracuseStep 4761503 = 7142255) B7142255
theorem B3174335 : Blo 2115435 3174335 := bstep (se 1 (by rfl) ⟨2380751, by rfl⟩ : syracuseStep 3174335 = 4761503) B4761503
theorem B2116223 : Blo 2115435 2116223 := bstep (se 1 (by rfl) ⟨1587167, by rfl⟩ : syracuseStep 2116223 = 3174335) B3174335
theorem B3174341 : Blo 2115435 3174341 := bbase (se 4 (by rfl) ⟨297594, by rfl⟩ : syracuseStep 3174341 = 595189) (by norm_num)
theorem B2116227 : Blo 2115435 2116227 := bstep (se 1 (by rfl) ⟨1587170, by rfl⟩ : syracuseStep 2116227 = 3174341) B3174341
theorem B3571141 : Blo 2115435 3571141 := bbase (se 4 (by rfl) ⟨334794, by rfl⟩ : syracuseStep 3571141 = 669589) (by norm_num)
theorem B4761521 : Blo 2115435 4761521 := bstep (se 2 (by rfl) ⟨1785570, by rfl⟩ : syracuseStep 4761521 = 3571141) B3571141
theorem B3174347 : Blo 2115435 3174347 := bstep (se 1 (by rfl) ⟨2380760, by rfl⟩ : syracuseStep 3174347 = 4761521) B4761521
theorem B2116231 : Blo 2115435 2116231 := bstep (se 1 (by rfl) ⟨1587173, by rfl⟩ : syracuseStep 2116231 = 3174347) B3174347
theorem B2380765 : Blo 2115435 2380765 := bbase (se 3 (by rfl) ⟨446393, by rfl⟩ : syracuseStep 2380765 = 892787) (by norm_num)
theorem B3174353 : Blo 2115435 3174353 := bstep (se 2 (by rfl) ⟨1190382, by rfl⟩ : syracuseStep 3174353 = 2380765) B2380765
theorem B2116235 : Blo 2115435 2116235 := bstep (se 1 (by rfl) ⟨1587176, by rfl⟩ : syracuseStep 2116235 = 3174353) B3174353
theorem B7142309 : Blo 2115435 7142309 := bbase (se 4 (by rfl) ⟨669591, by rfl⟩ : syracuseStep 7142309 = 1339183) (by norm_num)
theorem B4761539 : Blo 2115435 4761539 := bstep (se 1 (by rfl) ⟨3571154, by rfl⟩ : syracuseStep 4761539 = 7142309) B7142309
theorem B3174359 : Blo 2115435 3174359 := bstep (se 1 (by rfl) ⟨2380769, by rfl⟩ : syracuseStep 3174359 = 4761539) B4761539
theorem B2116239 : Blo 2115435 2116239 := bstep (se 1 (by rfl) ⟨1587179, by rfl⟩ : syracuseStep 2116239 = 3174359) B3174359
theorem B3174365 : Blo 2115435 3174365 := bbase (se 3 (by rfl) ⟨595193, by rfl⟩ : syracuseStep 3174365 = 1190387) (by norm_num)
theorem B2116243 : Blo 2115435 2116243 := bstep (se 1 (by rfl) ⟨1587182, by rfl⟩ : syracuseStep 2116243 = 3174365) B3174365
theorem B4761557 : Blo 2115435 4761557 := bbase (se 7 (by rfl) ⟨55799, by rfl⟩ : syracuseStep 4761557 = 111599) (by norm_num)
theorem B3174371 : Blo 2115435 3174371 := bstep (se 1 (by rfl) ⟨2380778, by rfl⟩ : syracuseStep 3174371 = 4761557) B4761557
theorem B2116247 : Blo 2115435 2116247 := bstep (se 1 (by rfl) ⟨1587185, by rfl⟩ : syracuseStep 2116247 = 3174371) B3174371
theorem B5084741 : Blo 2115435 5084741 := bbase (se 4 (by rfl) ⟨476694, by rfl⟩ : syracuseStep 5084741 = 953389) (by norm_num)
theorem B13559309 : Blo 2115435 13559309 := bstep (se 3 (by rfl) ⟨2542370, by rfl⟩ : syracuseStep 13559309 = 5084741) B5084741
theorem B9039539 : Blo 2115435 9039539 := bstep (se 1 (by rfl) ⟨6779654, by rfl⟩ : syracuseStep 9039539 = 13559309) B13559309
theorem B6026359 : Blo 2115435 6026359 := bstep (se 1 (by rfl) ⟨4519769, by rfl⟩ : syracuseStep 6026359 = 9039539) B9039539
theorem B8035145 : Blo 2115435 8035145 := bstep (se 2 (by rfl) ⟨3013179, by rfl⟩ : syracuseStep 8035145 = 6026359) B6026359
theorem B5356763 : Blo 2115435 5356763 := bstep (se 1 (by rfl) ⟨4017572, by rfl⟩ : syracuseStep 5356763 = 8035145) B8035145
theorem B3571175 : Blo 2115435 3571175 := bstep (se 1 (by rfl) ⟨2678381, by rfl⟩ : syracuseStep 3571175 = 5356763) B5356763
theorem B2380783 : Blo 2115435 2380783 := bstep (se 1 (by rfl) ⟨1785587, by rfl⟩ : syracuseStep 2380783 = 3571175) B3571175
theorem B3174377 : Blo 2115435 3174377 := bstep (se 2 (by rfl) ⟨1190391, by rfl⟩ : syracuseStep 3174377 = 2380783) B2380783
theorem B2116251 : Blo 2115435 2116251 := bstep (se 1 (by rfl) ⟨1587188, by rfl⟩ : syracuseStep 2116251 = 3174377) B3174377
theorem B5429861 : Blo 2115435 5429861 := bbase (se 4 (by rfl) ⟨509049, by rfl⟩ : syracuseStep 5429861 = 1018099) (by norm_num)
theorem B3619907 : Blo 2115435 3619907 := bstep (se 1 (by rfl) ⟨2714930, by rfl⟩ : syracuseStep 3619907 = 5429861) B5429861
theorem B2413271 : Blo 2115435 2413271 := bstep (se 1 (by rfl) ⟨1809953, by rfl⟩ : syracuseStep 2413271 = 3619907) B3619907
theorem B6435389 : Blo 2115435 6435389 := bstep (se 3 (by rfl) ⟨1206635, by rfl⟩ : syracuseStep 6435389 = 2413271) B2413271
theorem B4290259 : Blo 2115435 4290259 := bstep (se 1 (by rfl) ⟨3217694, by rfl⟩ : syracuseStep 4290259 = 6435389) B6435389
theorem B5720345 : Blo 2115435 5720345 := bstep (se 2 (by rfl) ⟨2145129, by rfl⟩ : syracuseStep 5720345 = 4290259) B4290259
theorem B3813563 : Blo 2115435 3813563 := bstep (se 1 (by rfl) ⟨2860172, by rfl⟩ : syracuseStep 3813563 = 5720345) B5720345
theorem B2542375 : Blo 2115435 2542375 := bstep (se 1 (by rfl) ⟨1906781, by rfl⟩ : syracuseStep 2542375 = 3813563) B3813563
theorem B3389833 : Blo 2115435 3389833 := bstep (se 2 (by rfl) ⟨1271187, by rfl⟩ : syracuseStep 3389833 = 2542375) B2542375
theorem B18079109 : Blo 2115435 18079109 := bstep (se 4 (by rfl) ⟨1694916, by rfl⟩ : syracuseStep 18079109 = 3389833) B3389833
theorem B12052739 : Blo 2115435 12052739 := bstep (se 1 (by rfl) ⟨9039554, by rfl⟩ : syracuseStep 12052739 = 18079109) B18079109
theorem B8035159 : Blo 2115435 8035159 := bstep (se 1 (by rfl) ⟨6026369, by rfl⟩ : syracuseStep 8035159 = 12052739) B12052739
theorem B10713545 : Blo 2115435 10713545 := bstep (se 2 (by rfl) ⟨4017579, by rfl⟩ : syracuseStep 10713545 = 8035159) B8035159
theorem B7142363 : Blo 2115435 7142363 := bstep (se 1 (by rfl) ⟨5356772, by rfl⟩ : syracuseStep 7142363 = 10713545) B10713545
theorem B4761575 : Blo 2115435 4761575 := bstep (se 1 (by rfl) ⟨3571181, by rfl⟩ : syracuseStep 4761575 = 7142363) B7142363
theorem B3174383 : Blo 2115435 3174383 := bstep (se 1 (by rfl) ⟨2380787, by rfl⟩ : syracuseStep 3174383 = 4761575) B4761575
theorem B2116255 : Blo 2115435 2116255 := bstep (se 1 (by rfl) ⟨1587191, by rfl⟩ : syracuseStep 2116255 = 3174383) B3174383
theorem B3174389 : Blo 2115435 3174389 := bbase (se 5 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 3174389 = 297599) (by norm_num)
theorem B2116259 : Blo 2115435 2116259 := bstep (se 1 (by rfl) ⟨1587194, by rfl⟩ : syracuseStep 2116259 = 3174389) B3174389
theorem B2542385 : Blo 2115435 2542385 := bbase (se 2 (by rfl) ⟨953394, by rfl⟩ : syracuseStep 2542385 = 1906789) (by norm_num)
theorem B6779693 : Blo 2115435 6779693 := bstep (se 3 (by rfl) ⟨1271192, by rfl⟩ : syracuseStep 6779693 = 2542385) B2542385
theorem B4519795 : Blo 2115435 4519795 := bstep (se 1 (by rfl) ⟨3389846, by rfl⟩ : syracuseStep 4519795 = 6779693) B6779693
theorem B6026393 : Blo 2115435 6026393 := bstep (se 2 (by rfl) ⟨2259897, by rfl⟩ : syracuseStep 6026393 = 4519795) B4519795
theorem B4017595 : Blo 2115435 4017595 := bstep (se 1 (by rfl) ⟨3013196, by rfl⟩ : syracuseStep 4017595 = 6026393) B6026393
theorem B5356793 : Blo 2115435 5356793 := bstep (se 2 (by rfl) ⟨2008797, by rfl⟩ : syracuseStep 5356793 = 4017595) B4017595
theorem B3571195 : Blo 2115435 3571195 := bstep (se 1 (by rfl) ⟨2678396, by rfl⟩ : syracuseStep 3571195 = 5356793) B5356793
theorem B4761593 : Blo 2115435 4761593 := bstep (se 2 (by rfl) ⟨1785597, by rfl⟩ : syracuseStep 4761593 = 3571195) B3571195
theorem B3174395 : Blo 2115435 3174395 := bstep (se 1 (by rfl) ⟨2380796, by rfl⟩ : syracuseStep 3174395 = 4761593) B4761593
theorem B2116263 : Blo 2115435 2116263 := bstep (se 1 (by rfl) ⟨1587197, by rfl⟩ : syracuseStep 2116263 = 3174395) B3174395
theorem B2380801 : Blo 2115435 2380801 := bbase (se 2 (by rfl) ⟨892800, by rfl⟩ : syracuseStep 2380801 = 1785601) (by norm_num)
theorem B3174401 : Blo 2115435 3174401 := bstep (se 2 (by rfl) ⟨1190400, by rfl⟩ : syracuseStep 3174401 = 2380801) B2380801
theorem B2116267 : Blo 2115435 2116267 := bstep (se 1 (by rfl) ⟨1587200, by rfl⟩ : syracuseStep 2116267 = 3174401) B3174401
theorem B5356813 : Blo 2115435 5356813 := bbase (se 3 (by rfl) ⟨1004402, by rfl⟩ : syracuseStep 5356813 = 2008805) (by norm_num)
theorem B7142417 : Blo 2115435 7142417 := bstep (se 2 (by rfl) ⟨2678406, by rfl⟩ : syracuseStep 7142417 = 5356813) B5356813
theorem B4761611 : Blo 2115435 4761611 := bstep (se 1 (by rfl) ⟨3571208, by rfl⟩ : syracuseStep 4761611 = 7142417) B7142417
theorem B3174407 : Blo 2115435 3174407 := bstep (se 1 (by rfl) ⟨2380805, by rfl⟩ : syracuseStep 3174407 = 4761611) B4761611
theorem B2116271 : Blo 2115435 2116271 := bstep (se 1 (by rfl) ⟨1587203, by rfl⟩ : syracuseStep 2116271 = 3174407) B3174407
theorem B3174413 : Blo 2115435 3174413 := bbase (se 3 (by rfl) ⟨595202, by rfl⟩ : syracuseStep 3174413 = 1190405) (by norm_num)
theorem B2116275 : Blo 2115435 2116275 := bstep (se 1 (by rfl) ⟨1587206, by rfl⟩ : syracuseStep 2116275 = 3174413) B3174413
theorem B4761629 : Blo 2115435 4761629 := bbase (se 3 (by rfl) ⟨892805, by rfl⟩ : syracuseStep 4761629 = 1785611) (by norm_num)
theorem B3174419 : Blo 2115435 3174419 := bstep (se 1 (by rfl) ⟨2380814, by rfl⟩ : syracuseStep 3174419 = 4761629) B4761629
theorem B2116279 : Blo 2115435 2116279 := bstep (se 1 (by rfl) ⟨1587209, by rfl⟩ : syracuseStep 2116279 = 3174419) B3174419
theorem B3571229 : Blo 2115435 3571229 := bbase (se 3 (by rfl) ⟨669605, by rfl⟩ : syracuseStep 3571229 = 1339211) (by norm_num)
theorem B2380819 : Blo 2115435 2380819 := bstep (se 1 (by rfl) ⟨1785614, by rfl⟩ : syracuseStep 2380819 = 3571229) B3571229
theorem B3174425 : Blo 2115435 3174425 := bstep (se 2 (by rfl) ⟨1190409, by rfl⟩ : syracuseStep 3174425 = 2380819) B2380819
theorem B2116283 : Blo 2115435 2116283 := bstep (se 1 (by rfl) ⟨1587212, by rfl⟩ : syracuseStep 2116283 = 3174425) B3174425
theorem B10169653 : Blo 2115435 10169653 := bbase (se 5 (by rfl) ⟨476702, by rfl⟩ : syracuseStep 10169653 = 953405) (by norm_num)
theorem B13559537 : Blo 2115435 13559537 := bstep (se 2 (by rfl) ⟨5084826, by rfl⟩ : syracuseStep 13559537 = 10169653) B10169653
theorem B9039691 : Blo 2115435 9039691 := bstep (se 1 (by rfl) ⟨6779768, by rfl⟩ : syracuseStep 9039691 = 13559537) B13559537
theorem B12052921 : Blo 2115435 12052921 := bstep (se 2 (by rfl) ⟨4519845, by rfl⟩ : syracuseStep 12052921 = 9039691) B9039691
theorem B16070561 : Blo 2115435 16070561 := bstep (se 2 (by rfl) ⟨6026460, by rfl⟩ : syracuseStep 16070561 = 12052921) B12052921
theorem B10713707 : Blo 2115435 10713707 := bstep (se 1 (by rfl) ⟨8035280, by rfl⟩ : syracuseStep 10713707 = 16070561) B16070561
theorem B7142471 : Blo 2115435 7142471 := bstep (se 1 (by rfl) ⟨5356853, by rfl⟩ : syracuseStep 7142471 = 10713707) B10713707
theorem B4761647 : Blo 2115435 4761647 := bstep (se 1 (by rfl) ⟨3571235, by rfl⟩ : syracuseStep 4761647 = 7142471) B7142471
theorem B3174431 : Blo 2115435 3174431 := bstep (se 1 (by rfl) ⟨2380823, by rfl⟩ : syracuseStep 3174431 = 4761647) B4761647
theorem B2116287 : Blo 2115435 2116287 := bstep (se 1 (by rfl) ⟨1587215, by rfl⟩ : syracuseStep 2116287 = 3174431) B3174431
theorem B3174437 : Blo 2115435 3174437 := bbase (se 4 (by rfl) ⟨297603, by rfl⟩ : syracuseStep 3174437 = 595207) (by norm_num)
theorem B2116291 : Blo 2115435 2116291 := bstep (se 1 (by rfl) ⟨1587218, by rfl⟩ : syracuseStep 2116291 = 3174437) B3174437
theorem B2678437 : Blo 2115435 2678437 := bbase (se 4 (by rfl) ⟨251103, by rfl⟩ : syracuseStep 2678437 = 502207) (by norm_num)
theorem B3571249 : Blo 2115435 3571249 := bstep (se 2 (by rfl) ⟨1339218, by rfl⟩ : syracuseStep 3571249 = 2678437) B2678437
theorem B4761665 : Blo 2115435 4761665 := bstep (se 2 (by rfl) ⟨1785624, by rfl⟩ : syracuseStep 4761665 = 3571249) B3571249
theorem B3174443 : Blo 2115435 3174443 := bstep (se 1 (by rfl) ⟨2380832, by rfl⟩ : syracuseStep 3174443 = 4761665) B4761665
theorem B2116295 : Blo 2115435 2116295 := bstep (se 1 (by rfl) ⟨1587221, by rfl⟩ : syracuseStep 2116295 = 3174443) B3174443
theorem B2380837 : Blo 2115435 2380837 := bbase (se 4 (by rfl) ⟨223203, by rfl⟩ : syracuseStep 2380837 = 446407) (by norm_num)
theorem B3174449 : Blo 2115435 3174449 := bstep (se 2 (by rfl) ⟨1190418, by rfl⟩ : syracuseStep 3174449 = 2380837) B2380837
theorem B2116299 : Blo 2115435 2116299 := bstep (se 1 (by rfl) ⟨1587224, by rfl⟩ : syracuseStep 2116299 = 3174449) B3174449
theorem B2542433 : Blo 2115435 2542433 := bbase (se 2 (by rfl) ⟨953412, by rfl⟩ : syracuseStep 2542433 = 1906825) (by norm_num)
theorem B6779821 : Blo 2115435 6779821 := bstep (se 3 (by rfl) ⟨1271216, by rfl⟩ : syracuseStep 6779821 = 2542433) B2542433
theorem B9039761 : Blo 2115435 9039761 := bstep (se 2 (by rfl) ⟨3389910, by rfl⟩ : syracuseStep 9039761 = 6779821) B6779821
theorem B6026507 : Blo 2115435 6026507 := bstep (se 1 (by rfl) ⟨4519880, by rfl⟩ : syracuseStep 6026507 = 9039761) B9039761
theorem B4017671 : Blo 2115435 4017671 := bstep (se 1 (by rfl) ⟨3013253, by rfl⟩ : syracuseStep 4017671 = 6026507) B6026507
theorem B2678447 : Blo 2115435 2678447 := bstep (se 1 (by rfl) ⟨2008835, by rfl⟩ : syracuseStep 2678447 = 4017671) B4017671
theorem B7142525 : Blo 2115435 7142525 := bstep (se 3 (by rfl) ⟨1339223, by rfl⟩ : syracuseStep 7142525 = 2678447) B2678447
theorem B4761683 : Blo 2115435 4761683 := bstep (se 1 (by rfl) ⟨3571262, by rfl⟩ : syracuseStep 4761683 = 7142525) B7142525
theorem B3174455 : Blo 2115435 3174455 := bstep (se 1 (by rfl) ⟨2380841, by rfl⟩ : syracuseStep 3174455 = 4761683) B4761683
theorem B2116303 : Blo 2115435 2116303 := bstep (se 1 (by rfl) ⟨1587227, by rfl⟩ : syracuseStep 2116303 = 3174455) B3174455
theorem B3174461 : Blo 2115435 3174461 := bbase (se 3 (by rfl) ⟨595211, by rfl⟩ : syracuseStep 3174461 = 1190423) (by norm_num)
theorem B2116307 : Blo 2115435 2116307 := bstep (se 1 (by rfl) ⟨1587230, by rfl⟩ : syracuseStep 2116307 = 3174461) B3174461
theorem B4761701 : Blo 2115435 4761701 := bbase (se 4 (by rfl) ⟨446409, by rfl⟩ : syracuseStep 4761701 = 892819) (by norm_num)
theorem B3174467 : Blo 2115435 3174467 := bstep (se 1 (by rfl) ⟨2380850, by rfl⟩ : syracuseStep 3174467 = 4761701) B4761701
theorem B2116311 : Blo 2115435 2116311 := bstep (se 1 (by rfl) ⟨1587233, by rfl⟩ : syracuseStep 2116311 = 3174467) B3174467
theorem B5356925 : Blo 2115435 5356925 := bbase (se 3 (by rfl) ⟨1004423, by rfl⟩ : syracuseStep 5356925 = 2008847) (by norm_num)
theorem B3571283 : Blo 2115435 3571283 := bstep (se 1 (by rfl) ⟨2678462, by rfl⟩ : syracuseStep 3571283 = 5356925) B5356925
theorem B2380855 : Blo 2115435 2380855 := bstep (se 1 (by rfl) ⟨1785641, by rfl⟩ : syracuseStep 2380855 = 3571283) B3571283
theorem B3174473 : Blo 2115435 3174473 := bstep (se 2 (by rfl) ⟨1190427, by rfl⟩ : syracuseStep 3174473 = 2380855) B2380855
theorem B2116315 : Blo 2115435 2116315 := bstep (se 1 (by rfl) ⟨1587236, by rfl⟩ : syracuseStep 2116315 = 3174473) B3174473
theorem B4017701 : Blo 2115435 4017701 := bbase (se 4 (by rfl) ⟨376659, by rfl⟩ : syracuseStep 4017701 = 753319) (by norm_num)
theorem B10713869 : Blo 2115435 10713869 := bstep (se 3 (by rfl) ⟨2008850, by rfl⟩ : syracuseStep 10713869 = 4017701) B4017701
theorem B7142579 : Blo 2115435 7142579 := bstep (se 1 (by rfl) ⟨5356934, by rfl⟩ : syracuseStep 7142579 = 10713869) B10713869
theorem B4761719 : Blo 2115435 4761719 := bstep (se 1 (by rfl) ⟨3571289, by rfl⟩ : syracuseStep 4761719 = 7142579) B7142579
theorem B3174479 : Blo 2115435 3174479 := bstep (se 1 (by rfl) ⟨2380859, by rfl⟩ : syracuseStep 3174479 = 4761719) B4761719
theorem B2116319 : Blo 2115435 2116319 := bstep (se 1 (by rfl) ⟨1587239, by rfl⟩ : syracuseStep 2116319 = 3174479) B3174479
theorem B3174485 : Blo 2115435 3174485 := bbase (se 8 (by rfl) ⟨18600, by rfl⟩ : syracuseStep 3174485 = 37201) (by norm_num)
theorem B2116323 : Blo 2115435 2116323 := bstep (se 1 (by rfl) ⟨1587242, by rfl⟩ : syracuseStep 2116323 = 3174485) B3174485
theorem B14480117 : Blo 2115435 14480117 := bbase (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) (by norm_num)
theorem B9653411 : Blo 2115435 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B6435607 : Blo 2115435 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B8580809 : Blo 2115435 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B5720539 : Blo 2115435 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B7627385 : Blo 2115435 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B20339693 : Blo 2115435 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B13559795 : Blo 2115435 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B9039863 : Blo 2115435 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B6026575 : Blo 2115435 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B8035433 : Blo 2115435 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B5356955 : Blo 2115435 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B3571303 : Blo 2115435 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B4761737 : Blo 2115435 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B3174491 : Blo 2115435 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B2116327 : Blo 2115435 2116327 := bstep (se 1 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 2116327 = 3174491) B3174491
theorem B2380873 : Blo 2115435 2380873 := bbase (se 2 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 2380873 = 1785655) (by norm_num)
theorem B3174497 : Blo 2115435 3174497 := bstep (se 2 (by rfl) ⟨1190436, by rfl⟩ : syracuseStep 3174497 = 2380873) B2380873
theorem B2116331 : Blo 2115435 2116331 := bstep (se 1 (by rfl) ⟨1587248, by rfl⟩ : syracuseStep 2116331 = 3174497) B3174497
theorem B4290421 : Blo 2115435 4290421 := bbase (se 5 (by rfl) ⟨201113, by rfl⟩ : syracuseStep 4290421 = 402227) (by norm_num)
theorem B5720561 : Blo 2115435 5720561 := bstep (se 2 (by rfl) ⟨2145210, by rfl⟩ : syracuseStep 5720561 = 4290421) B4290421
theorem B3813707 : Blo 2115435 3813707 := bstep (se 1 (by rfl) ⟨2860280, by rfl⟩ : syracuseStep 3813707 = 5720561) B5720561
theorem B2542471 : Blo 2115435 2542471 := bstep (se 1 (by rfl) ⟨1906853, by rfl⟩ : syracuseStep 2542471 = 3813707) B3813707
theorem B13559845 : Blo 2115435 13559845 := bstep (se 4 (by rfl) ⟨1271235, by rfl⟩ : syracuseStep 13559845 = 2542471) B2542471
theorem B18079793 : Blo 2115435 18079793 := bstep (se 2 (by rfl) ⟨6779922, by rfl⟩ : syracuseStep 18079793 = 13559845) B13559845
theorem B12053195 : Blo 2115435 12053195 := bstep (se 1 (by rfl) ⟨9039896, by rfl⟩ : syracuseStep 12053195 = 18079793) B18079793
theorem B8035463 : Blo 2115435 8035463 := bstep (se 1 (by rfl) ⟨6026597, by rfl⟩ : syracuseStep 8035463 = 12053195) B12053195
theorem B5356975 : Blo 2115435 5356975 := bstep (se 1 (by rfl) ⟨4017731, by rfl⟩ : syracuseStep 5356975 = 8035463) B8035463
theorem B7142633 : Blo 2115435 7142633 := bstep (se 2 (by rfl) ⟨2678487, by rfl⟩ : syracuseStep 7142633 = 5356975) B5356975
theorem B4761755 : Blo 2115435 4761755 := bstep (se 1 (by rfl) ⟨3571316, by rfl⟩ : syracuseStep 4761755 = 7142633) B7142633
theorem B3174503 : Blo 2115435 3174503 := bstep (se 1 (by rfl) ⟨2380877, by rfl⟩ : syracuseStep 3174503 = 4761755) B4761755
theorem B2116335 : Blo 2115435 2116335 := bstep (se 1 (by rfl) ⟨1587251, by rfl⟩ : syracuseStep 2116335 = 3174503) B3174503
theorem B3174509 : Blo 2115435 3174509 := bbase (se 3 (by rfl) ⟨595220, by rfl⟩ : syracuseStep 3174509 = 1190441) (by norm_num)
theorem B2116339 : Blo 2115435 2116339 := bstep (se 1 (by rfl) ⟨1587254, by rfl⟩ : syracuseStep 2116339 = 3174509) B3174509
theorem B4761773 : Blo 2115435 4761773 := bbase (se 3 (by rfl) ⟨892832, by rfl⟩ : syracuseStep 4761773 = 1785665) (by norm_num)
theorem B3174515 : Blo 2115435 3174515 := bstep (se 1 (by rfl) ⟨2380886, by rfl⟩ : syracuseStep 3174515 = 4761773) B4761773
theorem B2116343 : Blo 2115435 2116343 := bstep (se 1 (by rfl) ⟨1587257, by rfl⟩ : syracuseStep 2116343 = 3174515) B3174515
theorem B2715049 : Blo 2115435 2715049 := bbase (se 2 (by rfl) ⟨1018143, by rfl⟩ : syracuseStep 2715049 = 2036287) (by norm_num)
theorem B3620065 : Blo 2115435 3620065 := bstep (se 2 (by rfl) ⟨1357524, by rfl⟩ : syracuseStep 3620065 = 2715049) B2715049
theorem B4826753 : Blo 2115435 4826753 := bstep (se 2 (by rfl) ⟨1810032, by rfl⟩ : syracuseStep 4826753 = 3620065) B3620065
theorem B3217835 : Blo 2115435 3217835 := bstep (se 1 (by rfl) ⟨2413376, by rfl⟩ : syracuseStep 3217835 = 4826753) B4826753
theorem B2145223 : Blo 2115435 2145223 := bstep (se 1 (by rfl) ⟨1608917, by rfl⟩ : syracuseStep 2145223 = 3217835) B3217835
theorem B11441189 : Blo 2115435 11441189 := bstep (se 4 (by rfl) ⟨1072611, by rfl⟩ : syracuseStep 11441189 = 2145223) B2145223
theorem B7627459 : Blo 2115435 7627459 := bstep (se 1 (by rfl) ⟨5720594, by rfl⟩ : syracuseStep 7627459 = 11441189) B11441189
theorem B10169945 : Blo 2115435 10169945 := bstep (se 2 (by rfl) ⟨3813729, by rfl⟩ : syracuseStep 10169945 = 7627459) B7627459
theorem B6779963 : Blo 2115435 6779963 := bstep (se 1 (by rfl) ⟨5084972, by rfl⟩ : syracuseStep 6779963 = 10169945) B10169945
theorem B4519975 : Blo 2115435 4519975 := bstep (se 1 (by rfl) ⟨3389981, by rfl⟩ : syracuseStep 4519975 = 6779963) B6779963
theorem B6026633 : Blo 2115435 6026633 := bstep (se 2 (by rfl) ⟨2259987, by rfl⟩ : syracuseStep 6026633 = 4519975) B4519975
theorem B4017755 : Blo 2115435 4017755 := bstep (se 1 (by rfl) ⟨3013316, by rfl⟩ : syracuseStep 4017755 = 6026633) B6026633
theorem B2678503 : Blo 2115435 2678503 := bstep (se 1 (by rfl) ⟨2008877, by rfl⟩ : syracuseStep 2678503 = 4017755) B4017755
theorem B3571337 : Blo 2115435 3571337 := bstep (se 2 (by rfl) ⟨1339251, by rfl⟩ : syracuseStep 3571337 = 2678503) B2678503
theorem B2380891 : Blo 2115435 2380891 := bstep (se 1 (by rfl) ⟨1785668, by rfl⟩ : syracuseStep 2380891 = 3571337) B3571337
theorem B3174521 : Blo 2115435 3174521 := bstep (se 2 (by rfl) ⟨1190445, by rfl⟩ : syracuseStep 3174521 = 2380891) B2380891
theorem B2116347 : Blo 2115435 2116347 := bstep (se 1 (by rfl) ⟨1587260, by rfl⟩ : syracuseStep 2116347 = 3174521) B3174521
theorem B27119893 : Blo 2115435 27119893 := bbase (se 6 (by rfl) ⟨635622, by rfl⟩ : syracuseStep 27119893 = 1271245) (by norm_num)
theorem B36159857 : Blo 2115435 36159857 := bstep (se 2 (by rfl) ⟨13559946, by rfl⟩ : syracuseStep 36159857 = 27119893) B27119893
theorem B24106571 : Blo 2115435 24106571 := bstep (se 1 (by rfl) ⟨18079928, by rfl⟩ : syracuseStep 24106571 = 36159857) B36159857
theorem B16071047 : Blo 2115435 16071047 := bstep (se 1 (by rfl) ⟨12053285, by rfl⟩ : syracuseStep 16071047 = 24106571) B24106571
theorem B10714031 : Blo 2115435 10714031 := bstep (se 1 (by rfl) ⟨8035523, by rfl⟩ : syracuseStep 10714031 = 16071047) B16071047
theorem B7142687 : Blo 2115435 7142687 := bstep (se 1 (by rfl) ⟨5357015, by rfl⟩ : syracuseStep 7142687 = 10714031) B10714031
theorem B4761791 : Blo 2115435 4761791 := bstep (se 1 (by rfl) ⟨3571343, by rfl⟩ : syracuseStep 4761791 = 7142687) B7142687
theorem B3174527 : Blo 2115435 3174527 := bstep (se 1 (by rfl) ⟨2380895, by rfl⟩ : syracuseStep 3174527 = 4761791) B4761791
theorem B2116351 : Blo 2115435 2116351 := bstep (se 1 (by rfl) ⟨1587263, by rfl⟩ : syracuseStep 2116351 = 3174527) B3174527
theorem B3174533 : Blo 2115435 3174533 := bbase (se 4 (by rfl) ⟨297612, by rfl⟩ : syracuseStep 3174533 = 595225) (by norm_num)
theorem B2116355 : Blo 2115435 2116355 := bstep (se 1 (by rfl) ⟨1587266, by rfl⟩ : syracuseStep 2116355 = 3174533) B3174533
theorem B3571357 : Blo 2115435 3571357 := bbase (se 3 (by rfl) ⟨669629, by rfl⟩ : syracuseStep 3571357 = 1339259) (by norm_num)
theorem B4761809 : Blo 2115435 4761809 := bstep (se 2 (by rfl) ⟨1785678, by rfl⟩ : syracuseStep 4761809 = 3571357) B3571357
theorem B3174539 : Blo 2115435 3174539 := bstep (se 1 (by rfl) ⟨2380904, by rfl⟩ : syracuseStep 3174539 = 4761809) B4761809
theorem B2116359 : Blo 2115435 2116359 := bstep (se 1 (by rfl) ⟨1587269, by rfl⟩ : syracuseStep 2116359 = 3174539) B3174539
theorem B2380909 : Blo 2115435 2380909 := bbase (se 3 (by rfl) ⟨446420, by rfl⟩ : syracuseStep 2380909 = 892841) (by norm_num)
theorem B3174545 : Blo 2115435 3174545 := bstep (se 2 (by rfl) ⟨1190454, by rfl⟩ : syracuseStep 3174545 = 2380909) B2380909
theorem B2116363 : Blo 2115435 2116363 := bstep (se 1 (by rfl) ⟨1587272, by rfl⟩ : syracuseStep 2116363 = 3174545) B3174545
theorem B7142741 : Blo 2115435 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B4761827 : Blo 2115435 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B3174551 : Blo 2115435 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B2116367 : Blo 2115435 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B3174557 : Blo 2115435 3174557 := bbase (se 3 (by rfl) ⟨595229, by rfl⟩ : syracuseStep 3174557 = 1190459) (by norm_num)
theorem B2116371 : Blo 2115435 2116371 := bstep (se 1 (by rfl) ⟨1587278, by rfl⟩ : syracuseStep 2116371 = 3174557) B3174557
theorem B4761845 : Blo 2115435 4761845 := bbase (se 5 (by rfl) ⟨223211, by rfl⟩ : syracuseStep 4761845 = 446423) (by norm_num)
theorem B3174563 : Blo 2115435 3174563 := bstep (se 1 (by rfl) ⟨2380922, by rfl⟩ : syracuseStep 3174563 = 4761845) B4761845
theorem B2116375 : Blo 2115435 2116375 := bstep (se 1 (by rfl) ⟨1587281, by rfl⟩ : syracuseStep 2116375 = 3174563) B3174563
theorem B6108949 : Blo 2115435 6108949 := bbase (se 6 (by rfl) ⟨143178, by rfl⟩ : syracuseStep 6108949 = 286357) (by norm_num)
theorem B32581061 : Blo 2115435 32581061 := bstep (se 4 (by rfl) ⟨3054474, by rfl⟩ : syracuseStep 32581061 = 6108949) B6108949
theorem B21720707 : Blo 2115435 21720707 := bstep (se 1 (by rfl) ⟨16290530, by rfl⟩ : syracuseStep 21720707 = 32581061) B32581061
theorem B14480471 : Blo 2115435 14480471 := bstep (se 1 (by rfl) ⟨10860353, by rfl⟩ : syracuseStep 14480471 = 21720707) B21720707
theorem B38614589 : Blo 2115435 38614589 := bstep (se 3 (by rfl) ⟨7240235, by rfl⟩ : syracuseStep 38614589 = 14480471) B14480471
theorem B25743059 : Blo 2115435 25743059 := bstep (se 1 (by rfl) ⟨19307294, by rfl⟩ : syracuseStep 25743059 = 38614589) B38614589
theorem B17162039 : Blo 2115435 17162039 := bstep (se 1 (by rfl) ⟨12871529, by rfl⟩ : syracuseStep 17162039 = 25743059) B25743059
theorem B11441359 : Blo 2115435 11441359 := bstep (se 1 (by rfl) ⟨8581019, by rfl⟩ : syracuseStep 11441359 = 17162039) B17162039
theorem B15255145 : Blo 2115435 15255145 := bstep (se 2 (by rfl) ⟨5720679, by rfl⟩ : syracuseStep 15255145 = 11441359) B11441359
theorem B20340193 : Blo 2115435 20340193 := bstep (se 2 (by rfl) ⟨7627572, by rfl⟩ : syracuseStep 20340193 = 15255145) B15255145
theorem B27120257 : Blo 2115435 27120257 := bstep (se 2 (by rfl) ⟨10170096, by rfl⟩ : syracuseStep 27120257 = 20340193) B20340193
theorem B18080171 : Blo 2115435 18080171 := bstep (se 1 (by rfl) ⟨13560128, by rfl⟩ : syracuseStep 18080171 = 27120257) B27120257
theorem B12053447 : Blo 2115435 12053447 := bstep (se 1 (by rfl) ⟨9040085, by rfl⟩ : syracuseStep 12053447 = 18080171) B18080171
theorem B8035631 : Blo 2115435 8035631 := bstep (se 1 (by rfl) ⟨6026723, by rfl⟩ : syracuseStep 8035631 = 12053447) B12053447
theorem B5357087 : Blo 2115435 5357087 := bstep (se 1 (by rfl) ⟨4017815, by rfl⟩ : syracuseStep 5357087 = 8035631) B8035631
theorem B3571391 : Blo 2115435 3571391 := bstep (se 1 (by rfl) ⟨2678543, by rfl⟩ : syracuseStep 3571391 = 5357087) B5357087
theorem B2380927 : Blo 2115435 2380927 := bstep (se 1 (by rfl) ⟨1785695, by rfl⟩ : syracuseStep 2380927 = 3571391) B3571391
theorem B3174569 : Blo 2115435 3174569 := bstep (se 2 (by rfl) ⟨1190463, by rfl⟩ : syracuseStep 3174569 = 2380927) B2380927
theorem B2116379 : Blo 2115435 2116379 := bstep (se 1 (by rfl) ⟨1587284, by rfl⟩ : syracuseStep 2116379 = 3174569) B3174569
theorem B2542529 : Blo 2115435 2542529 := bbase (se 2 (by rfl) ⟨953448, by rfl⟩ : syracuseStep 2542529 = 1906897) (by norm_num)
theorem B6780077 : Blo 2115435 6780077 := bstep (se 3 (by rfl) ⟨1271264, by rfl⟩ : syracuseStep 6780077 = 2542529) B2542529
theorem B4520051 : Blo 2115435 4520051 := bstep (se 1 (by rfl) ⟨3390038, by rfl⟩ : syracuseStep 4520051 = 6780077) B6780077
theorem B3013367 : Blo 2115435 3013367 := bstep (se 1 (by rfl) ⟨2260025, by rfl⟩ : syracuseStep 3013367 = 4520051) B4520051
theorem B8035645 : Blo 2115435 8035645 := bstep (se 3 (by rfl) ⟨1506683, by rfl⟩ : syracuseStep 8035645 = 3013367) B3013367
theorem B10714193 : Blo 2115435 10714193 := bstep (se 2 (by rfl) ⟨4017822, by rfl⟩ : syracuseStep 10714193 = 8035645) B8035645
theorem B7142795 : Blo 2115435 7142795 := bstep (se 1 (by rfl) ⟨5357096, by rfl⟩ : syracuseStep 7142795 = 10714193) B10714193
theorem B4761863 : Blo 2115435 4761863 := bstep (se 1 (by rfl) ⟨3571397, by rfl⟩ : syracuseStep 4761863 = 7142795) B7142795
theorem B3174575 : Blo 2115435 3174575 := bstep (se 1 (by rfl) ⟨2380931, by rfl⟩ : syracuseStep 3174575 = 4761863) B4761863
theorem B2116383 : Blo 2115435 2116383 := bstep (se 1 (by rfl) ⟨1587287, by rfl⟩ : syracuseStep 2116383 = 3174575) B3174575
theorem B3174581 : Blo 2115435 3174581 := bbase (se 5 (by rfl) ⟨148808, by rfl⟩ : syracuseStep 3174581 = 297617) (by norm_num)
theorem B2116387 : Blo 2115435 2116387 := bstep (se 1 (by rfl) ⟨1587290, by rfl⟩ : syracuseStep 2116387 = 3174581) B3174581
theorem B5357117 : Blo 2115435 5357117 := bbase (se 3 (by rfl) ⟨1004459, by rfl⟩ : syracuseStep 5357117 = 2008919) (by norm_num)
theorem B3571411 : Blo 2115435 3571411 := bstep (se 1 (by rfl) ⟨2678558, by rfl⟩ : syracuseStep 3571411 = 5357117) B5357117
theorem B4761881 : Blo 2115435 4761881 := bstep (se 2 (by rfl) ⟨1785705, by rfl⟩ : syracuseStep 4761881 = 3571411) B3571411
theorem B3174587 : Blo 2115435 3174587 := bstep (se 1 (by rfl) ⟨2380940, by rfl⟩ : syracuseStep 3174587 = 4761881) B4761881
theorem B2116391 : Blo 2115435 2116391 := bstep (se 1 (by rfl) ⟨1587293, by rfl⟩ : syracuseStep 2116391 = 3174587) B3174587
theorem B2380945 : Blo 2115435 2380945 := bbase (se 2 (by rfl) ⟨892854, by rfl⟩ : syracuseStep 2380945 = 1785709) (by norm_num)
theorem B3174593 : Blo 2115435 3174593 := bstep (se 2 (by rfl) ⟨1190472, by rfl⟩ : syracuseStep 3174593 = 2380945) B2380945
theorem B2116395 : Blo 2115435 2116395 := bstep (se 1 (by rfl) ⟨1587296, by rfl⟩ : syracuseStep 2116395 = 3174593) B3174593
theorem B4017853 : Blo 2115435 4017853 := bbase (se 3 (by rfl) ⟨753347, by rfl⟩ : syracuseStep 4017853 = 1506695) (by norm_num)
theorem B5357137 : Blo 2115435 5357137 := bstep (se 2 (by rfl) ⟨2008926, by rfl⟩ : syracuseStep 5357137 = 4017853) B4017853
theorem B7142849 : Blo 2115435 7142849 := bstep (se 2 (by rfl) ⟨2678568, by rfl⟩ : syracuseStep 7142849 = 5357137) B5357137
theorem B4761899 : Blo 2115435 4761899 := bstep (se 1 (by rfl) ⟨3571424, by rfl⟩ : syracuseStep 4761899 = 7142849) B7142849
theorem B3174599 : Blo 2115435 3174599 := bstep (se 1 (by rfl) ⟨2380949, by rfl⟩ : syracuseStep 3174599 = 4761899) B4761899
theorem B2116399 : Blo 2115435 2116399 := bstep (se 1 (by rfl) ⟨1587299, by rfl⟩ : syracuseStep 2116399 = 3174599) B3174599
theorem B3174605 : Blo 2115435 3174605 := bbase (se 3 (by rfl) ⟨595238, by rfl⟩ : syracuseStep 3174605 = 1190477) (by norm_num)
theorem B2116403 : Blo 2115435 2116403 := bstep (se 1 (by rfl) ⟨1587302, by rfl⟩ : syracuseStep 2116403 = 3174605) B3174605
theorem B4761917 : Blo 2115435 4761917 := bbase (se 3 (by rfl) ⟨892859, by rfl⟩ : syracuseStep 4761917 = 1785719) (by norm_num)
theorem B3174611 : Blo 2115435 3174611 := bstep (se 1 (by rfl) ⟨2380958, by rfl⟩ : syracuseStep 3174611 = 4761917) B4761917
theorem B2116407 : Blo 2115435 2116407 := bstep (se 1 (by rfl) ⟨1587305, by rfl⟩ : syracuseStep 2116407 = 3174611) B3174611
theorem B3571445 : Blo 2115435 3571445 := bbase (se 5 (by rfl) ⟨167411, by rfl⟩ : syracuseStep 3571445 = 334823) (by norm_num)
theorem B2380963 : Blo 2115435 2380963 := bstep (se 1 (by rfl) ⟨1785722, by rfl⟩ : syracuseStep 2380963 = 3571445) B3571445
theorem B3174617 : Blo 2115435 3174617 := bstep (se 2 (by rfl) ⟨1190481, by rfl⟩ : syracuseStep 3174617 = 2380963) B2380963
theorem B2116411 : Blo 2115435 2116411 := bstep (se 1 (by rfl) ⟨1587308, by rfl⟩ : syracuseStep 2116411 = 3174617) B3174617
theorem B9653813 : Blo 2115435 9653813 := bbase (se 5 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 9653813 = 905045) (by norm_num)
theorem B6435875 : Blo 2115435 6435875 := bstep (se 1 (by rfl) ⟨4826906, by rfl⟩ : syracuseStep 6435875 = 9653813) B9653813
theorem B4290583 : Blo 2115435 4290583 := bstep (se 1 (by rfl) ⟨3217937, by rfl⟩ : syracuseStep 4290583 = 6435875) B6435875
theorem B5720777 : Blo 2115435 5720777 := bstep (se 2 (by rfl) ⟨2145291, by rfl⟩ : syracuseStep 5720777 = 4290583) B4290583
theorem B3813851 : Blo 2115435 3813851 := bstep (se 1 (by rfl) ⟨2860388, by rfl⟩ : syracuseStep 3813851 = 5720777) B5720777
theorem B10170269 : Blo 2115435 10170269 := bstep (se 3 (by rfl) ⟨1906925, by rfl⟩ : syracuseStep 10170269 = 3813851) B3813851
theorem B6780179 : Blo 2115435 6780179 := bstep (se 1 (by rfl) ⟨5085134, by rfl⟩ : syracuseStep 6780179 = 10170269) B10170269
theorem B4520119 : Blo 2115435 4520119 := bstep (se 1 (by rfl) ⟨3390089, by rfl⟩ : syracuseStep 4520119 = 6780179) B6780179
theorem B6026825 : Blo 2115435 6026825 := bstep (se 2 (by rfl) ⟨2260059, by rfl⟩ : syracuseStep 6026825 = 4520119) B4520119
theorem B16071533 : Blo 2115435 16071533 := bstep (se 3 (by rfl) ⟨3013412, by rfl⟩ : syracuseStep 16071533 = 6026825) B6026825
theorem B10714355 : Blo 2115435 10714355 := bstep (se 1 (by rfl) ⟨8035766, by rfl⟩ : syracuseStep 10714355 = 16071533) B16071533
theorem B7142903 : Blo 2115435 7142903 := bstep (se 1 (by rfl) ⟨5357177, by rfl⟩ : syracuseStep 7142903 = 10714355) B10714355
theorem B4761935 : Blo 2115435 4761935 := bstep (se 1 (by rfl) ⟨3571451, by rfl⟩ : syracuseStep 4761935 = 7142903) B7142903
theorem B3174623 : Blo 2115435 3174623 := bstep (se 1 (by rfl) ⟨2380967, by rfl⟩ : syracuseStep 3174623 = 4761935) B4761935
theorem B2116415 : Blo 2115435 2116415 := bstep (se 1 (by rfl) ⟨1587311, by rfl⟩ : syracuseStep 2116415 = 3174623) B3174623
theorem B3174629 : Blo 2115435 3174629 := bbase (se 4 (by rfl) ⟨297621, by rfl⟩ : syracuseStep 3174629 = 595243) (by norm_num)
theorem B2116419 : Blo 2115435 2116419 := bstep (se 1 (by rfl) ⟨1587314, by rfl⟩ : syracuseStep 2116419 = 3174629) B3174629
theorem B7627733 : Blo 2115435 7627733 := bbase (se 7 (by rfl) ⟨89387, by rfl⟩ : syracuseStep 7627733 = 178775) (by norm_num)
theorem B5085155 : Blo 2115435 5085155 := bstep (se 1 (by rfl) ⟨3813866, by rfl⟩ : syracuseStep 5085155 = 7627733) B7627733
theorem B3390103 : Blo 2115435 3390103 := bstep (se 1 (by rfl) ⟨2542577, by rfl⟩ : syracuseStep 3390103 = 5085155) B5085155
theorem B4520137 : Blo 2115435 4520137 := bstep (se 2 (by rfl) ⟨1695051, by rfl⟩ : syracuseStep 4520137 = 3390103) B3390103
theorem B6026849 : Blo 2115435 6026849 := bstep (se 2 (by rfl) ⟨2260068, by rfl⟩ : syracuseStep 6026849 = 4520137) B4520137
theorem B4017899 : Blo 2115435 4017899 := bstep (se 1 (by rfl) ⟨3013424, by rfl⟩ : syracuseStep 4017899 = 6026849) B6026849
theorem B2678599 : Blo 2115435 2678599 := bstep (se 1 (by rfl) ⟨2008949, by rfl⟩ : syracuseStep 2678599 = 4017899) B4017899
theorem B3571465 : Blo 2115435 3571465 := bstep (se 2 (by rfl) ⟨1339299, by rfl⟩ : syracuseStep 3571465 = 2678599) B2678599
theorem B4761953 : Blo 2115435 4761953 := bstep (se 2 (by rfl) ⟨1785732, by rfl⟩ : syracuseStep 4761953 = 3571465) B3571465
theorem B3174635 : Blo 2115435 3174635 := bstep (se 1 (by rfl) ⟨2380976, by rfl⟩ : syracuseStep 3174635 = 4761953) B4761953
theorem B2116423 : Blo 2115435 2116423 := bstep (se 1 (by rfl) ⟨1587317, by rfl⟩ : syracuseStep 2116423 = 3174635) B3174635
theorem B2380981 : Blo 2115435 2380981 := bbase (se 5 (by rfl) ⟨111608, by rfl⟩ : syracuseStep 2380981 = 223217) (by norm_num)
theorem B3174641 : Blo 2115435 3174641 := bstep (se 2 (by rfl) ⟨1190490, by rfl⟩ : syracuseStep 3174641 = 2380981) B2380981
theorem B2116427 : Blo 2115435 2116427 := bstep (se 1 (by rfl) ⟨1587320, by rfl⟩ : syracuseStep 2116427 = 3174641) B3174641
theorem B2678609 : Blo 2115435 2678609 := bbase (se 2 (by rfl) ⟨1004478, by rfl⟩ : syracuseStep 2678609 = 2008957) (by norm_num)
theorem B7142957 : Blo 2115435 7142957 := bstep (se 3 (by rfl) ⟨1339304, by rfl⟩ : syracuseStep 7142957 = 2678609) B2678609
theorem B4761971 : Blo 2115435 4761971 := bstep (se 1 (by rfl) ⟨3571478, by rfl⟩ : syracuseStep 4761971 = 7142957) B7142957
theorem B3174647 : Blo 2115435 3174647 := bstep (se 1 (by rfl) ⟨2380985, by rfl⟩ : syracuseStep 3174647 = 4761971) B4761971
theorem B2116431 : Blo 2115435 2116431 := bstep (se 1 (by rfl) ⟨1587323, by rfl⟩ : syracuseStep 2116431 = 3174647) B3174647
theorem B3174653 : Blo 2115435 3174653 := bbase (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) (by norm_num)
theorem B2116435 : Blo 2115435 2116435 := bstep (se 1 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 2116435 = 3174653) B3174653
theorem B4761989 : Blo 2115435 4761989 := bbase (se 4 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 4761989 = 892873) (by norm_num)
theorem B3174659 : Blo 2115435 3174659 := bstep (se 1 (by rfl) ⟨2380994, by rfl⟩ : syracuseStep 3174659 = 4761989) B4761989
theorem B2116439 : Blo 2115435 2116439 := bstep (se 1 (by rfl) ⟨1587329, by rfl⟩ : syracuseStep 2116439 = 3174659) B3174659
theorem B3013453 : Blo 2115435 3013453 := bbase (se 3 (by rfl) ⟨565022, by rfl⟩ : syracuseStep 3013453 = 1130045) (by norm_num)
theorem B4017937 : Blo 2115435 4017937 := bstep (se 2 (by rfl) ⟨1506726, by rfl⟩ : syracuseStep 4017937 = 3013453) B3013453
theorem B5357249 : Blo 2115435 5357249 := bstep (se 2 (by rfl) ⟨2008968, by rfl⟩ : syracuseStep 5357249 = 4017937) B4017937
theorem B3571499 : Blo 2115435 3571499 := bstep (se 1 (by rfl) ⟨2678624, by rfl⟩ : syracuseStep 3571499 = 5357249) B5357249
theorem B2380999 : Blo 2115435 2380999 := bstep (se 1 (by rfl) ⟨1785749, by rfl⟩ : syracuseStep 2380999 = 3571499) B3571499
theorem B3174665 : Blo 2115435 3174665 := bstep (se 2 (by rfl) ⟨1190499, by rfl⟩ : syracuseStep 3174665 = 2380999) B2380999
theorem B2116443 : Blo 2115435 2116443 := bstep (se 1 (by rfl) ⟨1587332, by rfl⟩ : syracuseStep 2116443 = 3174665) B3174665
theorem B10714517 : Blo 2115435 10714517 := bbase (se 6 (by rfl) ⟨251121, by rfl⟩ : syracuseStep 10714517 = 502243) (by norm_num)
theorem B7143011 : Blo 2115435 7143011 := bstep (se 1 (by rfl) ⟨5357258, by rfl⟩ : syracuseStep 7143011 = 10714517) B10714517
theorem B4762007 : Blo 2115435 4762007 := bstep (se 1 (by rfl) ⟨3571505, by rfl⟩ : syracuseStep 4762007 = 7143011) B7143011
theorem B3174671 : Blo 2115435 3174671 := bstep (se 1 (by rfl) ⟨2381003, by rfl⟩ : syracuseStep 3174671 = 4762007) B4762007
theorem B2116447 : Blo 2115435 2116447 := bstep (se 1 (by rfl) ⟨1587335, by rfl⟩ : syracuseStep 2116447 = 3174671) B3174671
theorem B3174677 : Blo 2115435 3174677 := bbase (se 6 (by rfl) ⟨74406, by rfl⟩ : syracuseStep 3174677 = 148813) (by norm_num)
theorem B2116451 : Blo 2115435 2116451 := bstep (se 1 (by rfl) ⟨1587338, by rfl⟩ : syracuseStep 2116451 = 3174677) B3174677
theorem B5720885 : Blo 2115435 5720885 := bbase (se 5 (by rfl) ⟨268166, by rfl⟩ : syracuseStep 5720885 = 536333) (by norm_num)
theorem B3813923 : Blo 2115435 3813923 := bstep (se 1 (by rfl) ⟨2860442, by rfl⟩ : syracuseStep 3813923 = 5720885) B5720885
theorem B10170461 : Blo 2115435 10170461 := bstep (se 3 (by rfl) ⟨1906961, by rfl⟩ : syracuseStep 10170461 = 3813923) B3813923
theorem B27121229 : Blo 2115435 27121229 := bstep (se 3 (by rfl) ⟨5085230, by rfl⟩ : syracuseStep 27121229 = 10170461) B10170461
theorem B18080819 : Blo 2115435 18080819 := bstep (se 1 (by rfl) ⟨13560614, by rfl⟩ : syracuseStep 18080819 = 27121229) B27121229
theorem B12053879 : Blo 2115435 12053879 := bstep (se 1 (by rfl) ⟨9040409, by rfl⟩ : syracuseStep 12053879 = 18080819) B18080819
theorem B8035919 : Blo 2115435 8035919 := bstep (se 1 (by rfl) ⟨6026939, by rfl⟩ : syracuseStep 8035919 = 12053879) B12053879
theorem B5357279 : Blo 2115435 5357279 := bstep (se 1 (by rfl) ⟨4017959, by rfl⟩ : syracuseStep 5357279 = 8035919) B8035919
theorem B3571519 : Blo 2115435 3571519 := bstep (se 1 (by rfl) ⟨2678639, by rfl⟩ : syracuseStep 3571519 = 5357279) B5357279
theorem B4762025 : Blo 2115435 4762025 := bstep (se 2 (by rfl) ⟨1785759, by rfl⟩ : syracuseStep 4762025 = 3571519) B3571519
theorem B3174683 : Blo 2115435 3174683 := bstep (se 1 (by rfl) ⟨2381012, by rfl⟩ : syracuseStep 3174683 = 4762025) B4762025
theorem B2116455 : Blo 2115435 2116455 := bstep (se 1 (by rfl) ⟨1587341, by rfl⟩ : syracuseStep 2116455 = 3174683) B3174683
theorem B2381017 : Blo 2115435 2381017 := bbase (se 2 (by rfl) ⟨892881, by rfl⟩ : syracuseStep 2381017 = 1785763) (by norm_num)
theorem B3174689 : Blo 2115435 3174689 := bstep (se 2 (by rfl) ⟨1190508, by rfl⟩ : syracuseStep 3174689 = 2381017) B2381017
theorem B2116459 : Blo 2115435 2116459 := bstep (se 1 (by rfl) ⟨1587344, by rfl⟩ : syracuseStep 2116459 = 3174689) B3174689
theorem B7627877 : Blo 2115435 7627877 := bbase (se 4 (by rfl) ⟨715113, by rfl⟩ : syracuseStep 7627877 = 1430227) (by norm_num)
theorem B5085251 : Blo 2115435 5085251 := bstep (se 1 (by rfl) ⟨3813938, by rfl⟩ : syracuseStep 5085251 = 7627877) B7627877
theorem B3390167 : Blo 2115435 3390167 := bstep (se 1 (by rfl) ⟨2542625, by rfl⟩ : syracuseStep 3390167 = 5085251) B5085251
theorem B2260111 : Blo 2115435 2260111 := bstep (se 1 (by rfl) ⟨1695083, by rfl⟩ : syracuseStep 2260111 = 3390167) B3390167
theorem B3013481 : Blo 2115435 3013481 := bstep (se 2 (by rfl) ⟨1130055, by rfl⟩ : syracuseStep 3013481 = 2260111) B2260111
theorem B8035949 : Blo 2115435 8035949 := bstep (se 3 (by rfl) ⟨1506740, by rfl⟩ : syracuseStep 8035949 = 3013481) B3013481
theorem B5357299 : Blo 2115435 5357299 := bstep (se 1 (by rfl) ⟨4017974, by rfl⟩ : syracuseStep 5357299 = 8035949) B8035949
theorem B7143065 : Blo 2115435 7143065 := bstep (se 2 (by rfl) ⟨2678649, by rfl⟩ : syracuseStep 7143065 = 5357299) B5357299
theorem B4762043 : Blo 2115435 4762043 := bstep (se 1 (by rfl) ⟨3571532, by rfl⟩ : syracuseStep 4762043 = 7143065) B7143065
theorem B3174695 : Blo 2115435 3174695 := bstep (se 1 (by rfl) ⟨2381021, by rfl⟩ : syracuseStep 3174695 = 4762043) B4762043
theorem B2116463 : Blo 2115435 2116463 := bstep (se 1 (by rfl) ⟨1587347, by rfl⟩ : syracuseStep 2116463 = 3174695) B3174695
theorem B3174701 : Blo 2115435 3174701 := bbase (se 3 (by rfl) ⟨595256, by rfl⟩ : syracuseStep 3174701 = 1190513) (by norm_num)
theorem B2116467 : Blo 2115435 2116467 := bstep (se 1 (by rfl) ⟨1587350, by rfl⟩ : syracuseStep 2116467 = 3174701) B3174701
theorem B4762061 : Blo 2115435 4762061 := bbase (se 3 (by rfl) ⟨892886, by rfl⟩ : syracuseStep 4762061 = 1785773) (by norm_num)
theorem B3174707 : Blo 2115435 3174707 := bstep (se 1 (by rfl) ⟨2381030, by rfl⟩ : syracuseStep 3174707 = 4762061) B4762061
theorem B2116471 : Blo 2115435 2116471 := bstep (se 1 (by rfl) ⟨1587353, by rfl⟩ : syracuseStep 2116471 = 3174707) B3174707
theorem B2678665 : Blo 2115435 2678665 := bbase (se 2 (by rfl) ⟨1004499, by rfl⟩ : syracuseStep 2678665 = 2008999) (by norm_num)
theorem B3571553 : Blo 2115435 3571553 := bstep (se 2 (by rfl) ⟨1339332, by rfl⟩ : syracuseStep 3571553 = 2678665) B2678665
theorem B2381035 : Blo 2115435 2381035 := bstep (se 1 (by rfl) ⟨1785776, by rfl⟩ : syracuseStep 2381035 = 3571553) B3571553
theorem B3174713 : Blo 2115435 3174713 := bstep (se 2 (by rfl) ⟨1190517, by rfl⟩ : syracuseStep 3174713 = 2381035) B2381035
theorem B2116475 : Blo 2115435 2116475 := bstep (se 1 (by rfl) ⟨1587356, by rfl⟩ : syracuseStep 2116475 = 3174713) B3174713
theorem B198162773 : Blo 2115435 198162773 := bbase (se 10 (by rfl) ⟨290277, by rfl⟩ : syracuseStep 198162773 = 580555) (by norm_num)
theorem B132108515 : Blo 2115435 132108515 := bstep (se 1 (by rfl) ⟨99081386, by rfl⟩ : syracuseStep 132108515 = 198162773) B198162773
theorem B88072343 : Blo 2115435 88072343 := bstep (se 1 (by rfl) ⟨66054257, by rfl⟩ : syracuseStep 88072343 = 132108515) B132108515
theorem B58714895 : Blo 2115435 58714895 := bstep (se 1 (by rfl) ⟨44036171, by rfl⟩ : syracuseStep 58714895 = 88072343) B88072343
theorem B39143263 : Blo 2115435 39143263 := bstep (se 1 (by rfl) ⟨29357447, by rfl⟩ : syracuseStep 39143263 = 58714895) B58714895
theorem B52191017 : Blo 2115435 52191017 := bstep (se 2 (by rfl) ⟨19571631, by rfl⟩ : syracuseStep 52191017 = 39143263) B39143263
theorem B34794011 : Blo 2115435 34794011 := bstep (se 1 (by rfl) ⟨26095508, by rfl⟩ : syracuseStep 34794011 = 52191017) B52191017
theorem B23196007 : Blo 2115435 23196007 := bstep (se 1 (by rfl) ⟨17397005, by rfl⟩ : syracuseStep 23196007 = 34794011) B34794011
theorem B30928009 : Blo 2115435 30928009 := bstep (se 2 (by rfl) ⟨11598003, by rfl⟩ : syracuseStep 30928009 = 23196007) B23196007
theorem B41237345 : Blo 2115435 41237345 := bstep (se 2 (by rfl) ⟨15464004, by rfl⟩ : syracuseStep 41237345 = 30928009) B30928009
theorem B27491563 : Blo 2115435 27491563 := bstep (se 1 (by rfl) ⟨20618672, by rfl⟩ : syracuseStep 27491563 = 41237345) B41237345
theorem B36655417 : Blo 2115435 36655417 := bstep (se 2 (by rfl) ⟨13745781, by rfl⟩ : syracuseStep 36655417 = 27491563) B27491563
theorem B48873889 : Blo 2115435 48873889 := bstep (se 2 (by rfl) ⟨18327708, by rfl⟩ : syracuseStep 48873889 = 36655417) B36655417
theorem B65165185 : Blo 2115435 65165185 := bstep (se 2 (by rfl) ⟨24436944, by rfl⟩ : syracuseStep 65165185 = 48873889) B48873889
theorem B86886913 : Blo 2115435 86886913 := bstep (se 2 (by rfl) ⟨32582592, by rfl⟩ : syracuseStep 86886913 = 65165185) B65165185
theorem B115849217 : Blo 2115435 115849217 := bstep (se 2 (by rfl) ⟨43443456, by rfl⟩ : syracuseStep 115849217 = 86886913) B86886913
theorem B77232811 : Blo 2115435 77232811 := bstep (se 1 (by rfl) ⟨57924608, by rfl⟩ : syracuseStep 77232811 = 115849217) B115849217
theorem B102977081 : Blo 2115435 102977081 := bstep (se 2 (by rfl) ⟨38616405, by rfl⟩ : syracuseStep 102977081 = 77232811) B77232811
theorem B68651387 : Blo 2115435 68651387 := bstep (se 1 (by rfl) ⟨51488540, by rfl⟩ : syracuseStep 68651387 = 102977081) B102977081
theorem B45767591 : Blo 2115435 45767591 := bstep (se 1 (by rfl) ⟨34325693, by rfl⟩ : syracuseStep 45767591 = 68651387) B68651387
theorem B30511727 : Blo 2115435 30511727 := bstep (se 1 (by rfl) ⟨22883795, by rfl⟩ : syracuseStep 30511727 = 45767591) B45767591
theorem B20341151 : Blo 2115435 20341151 := bstep (se 1 (by rfl) ⟨15255863, by rfl⟩ : syracuseStep 20341151 = 30511727) B30511727
theorem B13560767 : Blo 2115435 13560767 := bstep (se 1 (by rfl) ⟨10170575, by rfl⟩ : syracuseStep 13560767 = 20341151) B20341151
theorem B9040511 : Blo 2115435 9040511 := bstep (se 1 (by rfl) ⟨6780383, by rfl⟩ : syracuseStep 9040511 = 13560767) B13560767
theorem B24108029 : Blo 2115435 24108029 := bstep (se 3 (by rfl) ⟨4520255, by rfl⟩ : syracuseStep 24108029 = 9040511) B9040511
theorem B16072019 : Blo 2115435 16072019 := bstep (se 1 (by rfl) ⟨12054014, by rfl⟩ : syracuseStep 16072019 = 24108029) B24108029
theorem B10714679 : Blo 2115435 10714679 := bstep (se 1 (by rfl) ⟨8036009, by rfl⟩ : syracuseStep 10714679 = 16072019) B16072019
theorem B7143119 : Blo 2115435 7143119 := bstep (se 1 (by rfl) ⟨5357339, by rfl⟩ : syracuseStep 7143119 = 10714679) B10714679
theorem B4762079 : Blo 2115435 4762079 := bstep (se 1 (by rfl) ⟨3571559, by rfl⟩ : syracuseStep 4762079 = 7143119) B7143119
theorem B3174719 : Blo 2115435 3174719 := bstep (se 1 (by rfl) ⟨2381039, by rfl⟩ : syracuseStep 3174719 = 4762079) B4762079
theorem B2116479 : Blo 2115435 2116479 := bstep (se 1 (by rfl) ⟨1587359, by rfl⟩ : syracuseStep 2116479 = 3174719) B3174719
theorem B3174725 : Blo 2115435 3174725 := bbase (se 4 (by rfl) ⟨297630, by rfl⟩ : syracuseStep 3174725 = 595261) (by norm_num)
theorem B2116483 : Blo 2115435 2116483 := bstep (se 1 (by rfl) ⟨1587362, by rfl⟩ : syracuseStep 2116483 = 3174725) B3174725
theorem B3571573 : Blo 2115435 3571573 := bbase (se 5 (by rfl) ⟨167417, by rfl⟩ : syracuseStep 3571573 = 334835) (by norm_num)
theorem B4762097 : Blo 2115435 4762097 := bstep (se 2 (by rfl) ⟨1785786, by rfl⟩ : syracuseStep 4762097 = 3571573) B3571573
theorem B3174731 : Blo 2115435 3174731 := bstep (se 1 (by rfl) ⟨2381048, by rfl⟩ : syracuseStep 3174731 = 4762097) B4762097
theorem B2116487 : Blo 2115435 2116487 := bstep (se 1 (by rfl) ⟨1587365, by rfl⟩ : syracuseStep 2116487 = 3174731) B3174731
theorem B2381053 : Blo 2115435 2381053 := bbase (se 3 (by rfl) ⟨446447, by rfl⟩ : syracuseStep 2381053 = 892895) (by norm_num)
theorem B3174737 : Blo 2115435 3174737 := bstep (se 2 (by rfl) ⟨1190526, by rfl⟩ : syracuseStep 3174737 = 2381053) B2381053
theorem B2116491 : Blo 2115435 2116491 := bstep (se 1 (by rfl) ⟨1587368, by rfl⟩ : syracuseStep 2116491 = 3174737) B3174737
theorem B7143173 : Blo 2115435 7143173 := bbase (se 4 (by rfl) ⟨669672, by rfl⟩ : syracuseStep 7143173 = 1339345) (by norm_num)
theorem B4762115 : Blo 2115435 4762115 := bstep (se 1 (by rfl) ⟨3571586, by rfl⟩ : syracuseStep 4762115 = 7143173) B7143173
theorem B3174743 : Blo 2115435 3174743 := bstep (se 1 (by rfl) ⟨2381057, by rfl⟩ : syracuseStep 3174743 = 4762115) B4762115
theorem B2116495 : Blo 2115435 2116495 := bstep (se 1 (by rfl) ⟨1587371, by rfl⟩ : syracuseStep 2116495 = 3174743) B3174743
theorem B3174749 : Blo 2115435 3174749 := bbase (se 3 (by rfl) ⟨595265, by rfl⟩ : syracuseStep 3174749 = 1190531) (by norm_num)
theorem B2116499 : Blo 2115435 2116499 := bstep (se 1 (by rfl) ⟨1587374, by rfl⟩ : syracuseStep 2116499 = 3174749) B3174749
theorem B4762133 : Blo 2115435 4762133 := bbase (se 6 (by rfl) ⟨111612, by rfl⟩ : syracuseStep 4762133 = 223225) (by norm_num)
theorem B3174755 : Blo 2115435 3174755 := bstep (se 1 (by rfl) ⟨2381066, by rfl⟩ : syracuseStep 3174755 = 4762133) B4762133
theorem B2116503 : Blo 2115435 2116503 := bstep (se 1 (by rfl) ⟨1587377, by rfl⟩ : syracuseStep 2116503 = 3174755) B3174755
theorem B8036117 : Blo 2115435 8036117 := bbase (se 6 (by rfl) ⟨188346, by rfl⟩ : syracuseStep 8036117 = 376693) (by norm_num)
theorem B5357411 : Blo 2115435 5357411 := bstep (se 1 (by rfl) ⟨4018058, by rfl⟩ : syracuseStep 5357411 = 8036117) B8036117
theorem B3571607 : Blo 2115435 3571607 := bstep (se 1 (by rfl) ⟨2678705, by rfl⟩ : syracuseStep 3571607 = 5357411) B5357411
theorem B2381071 : Blo 2115435 2381071 := bstep (se 1 (by rfl) ⟨1785803, by rfl⟩ : syracuseStep 2381071 = 3571607) B3571607
theorem B3174761 : Blo 2115435 3174761 := bstep (se 2 (by rfl) ⟨1190535, by rfl⟩ : syracuseStep 3174761 = 2381071) B2381071
theorem B2116507 : Blo 2115435 2116507 := bstep (se 1 (by rfl) ⟨1587380, by rfl⟩ : syracuseStep 2116507 = 3174761) B3174761
theorem B12054197 : Blo 2115435 12054197 := bbase (se 5 (by rfl) ⟨565040, by rfl⟩ : syracuseStep 12054197 = 1130081) (by norm_num)
theorem B8036131 : Blo 2115435 8036131 := bstep (se 1 (by rfl) ⟨6027098, by rfl⟩ : syracuseStep 8036131 = 12054197) B12054197
theorem B10714841 : Blo 2115435 10714841 := bstep (se 2 (by rfl) ⟨4018065, by rfl⟩ : syracuseStep 10714841 = 8036131) B8036131
theorem B7143227 : Blo 2115435 7143227 := bstep (se 1 (by rfl) ⟨5357420, by rfl⟩ : syracuseStep 7143227 = 10714841) B10714841
theorem B4762151 : Blo 2115435 4762151 := bstep (se 1 (by rfl) ⟨3571613, by rfl⟩ : syracuseStep 4762151 = 7143227) B7143227
theorem B3174767 : Blo 2115435 3174767 := bstep (se 1 (by rfl) ⟨2381075, by rfl⟩ : syracuseStep 3174767 = 4762151) B4762151
theorem B2116511 : Blo 2115435 2116511 := bstep (se 1 (by rfl) ⟨1587383, by rfl⟩ : syracuseStep 2116511 = 3174767) B3174767
theorem B3174773 : Blo 2115435 3174773 := bbase (se 5 (by rfl) ⟨148817, by rfl⟩ : syracuseStep 3174773 = 297635) (by norm_num)
theorem B2116515 : Blo 2115435 2116515 := bstep (se 1 (by rfl) ⟨1587386, by rfl⟩ : syracuseStep 2116515 = 3174773) B3174773
theorem B2542693 : Blo 2115435 2542693 := bbase (se 4 (by rfl) ⟨238377, by rfl⟩ : syracuseStep 2542693 = 476755) (by norm_num)
theorem B3390257 : Blo 2115435 3390257 := bstep (se 2 (by rfl) ⟨1271346, by rfl⟩ : syracuseStep 3390257 = 2542693) B2542693
theorem B2260171 : Blo 2115435 2260171 := bstep (se 1 (by rfl) ⟨1695128, by rfl⟩ : syracuseStep 2260171 = 3390257) B3390257
theorem B3013561 : Blo 2115435 3013561 := bstep (se 2 (by rfl) ⟨1130085, by rfl⟩ : syracuseStep 3013561 = 2260171) B2260171
theorem B4018081 : Blo 2115435 4018081 := bstep (se 2 (by rfl) ⟨1506780, by rfl⟩ : syracuseStep 4018081 = 3013561) B3013561
theorem B5357441 : Blo 2115435 5357441 := bstep (se 2 (by rfl) ⟨2009040, by rfl⟩ : syracuseStep 5357441 = 4018081) B4018081
theorem B3571627 : Blo 2115435 3571627 := bstep (se 1 (by rfl) ⟨2678720, by rfl⟩ : syracuseStep 3571627 = 5357441) B5357441
theorem B4762169 : Blo 2115435 4762169 := bstep (se 2 (by rfl) ⟨1785813, by rfl⟩ : syracuseStep 4762169 = 3571627) B3571627
theorem B3174779 : Blo 2115435 3174779 := bstep (se 1 (by rfl) ⟨2381084, by rfl⟩ : syracuseStep 3174779 = 4762169) B4762169
theorem B2116519 : Blo 2115435 2116519 := bstep (se 1 (by rfl) ⟨1587389, by rfl⟩ : syracuseStep 2116519 = 3174779) B3174779
theorem B2381089 : Blo 2115435 2381089 := bbase (se 2 (by rfl) ⟨892908, by rfl⟩ : syracuseStep 2381089 = 1785817) (by norm_num)
theorem B3174785 : Blo 2115435 3174785 := bstep (se 2 (by rfl) ⟨1190544, by rfl⟩ : syracuseStep 3174785 = 2381089) B2381089
theorem B2116523 : Blo 2115435 2116523 := bstep (se 1 (by rfl) ⟨1587392, by rfl⟩ : syracuseStep 2116523 = 3174785) B3174785
theorem B5357461 : Blo 2115435 5357461 := bbase (se 6 (by rfl) ⟨125565, by rfl⟩ : syracuseStep 5357461 = 251131) (by norm_num)
theorem B7143281 : Blo 2115435 7143281 := bstep (se 2 (by rfl) ⟨2678730, by rfl⟩ : syracuseStep 7143281 = 5357461) B5357461
theorem B4762187 : Blo 2115435 4762187 := bstep (se 1 (by rfl) ⟨3571640, by rfl⟩ : syracuseStep 4762187 = 7143281) B7143281
theorem B3174791 : Blo 2115435 3174791 := bstep (se 1 (by rfl) ⟨2381093, by rfl⟩ : syracuseStep 3174791 = 4762187) B4762187
theorem B2116527 : Blo 2115435 2116527 := bstep (se 1 (by rfl) ⟨1587395, by rfl⟩ : syracuseStep 2116527 = 3174791) B3174791
theorem B3174797 : Blo 2115435 3174797 := bbase (se 3 (by rfl) ⟨595274, by rfl⟩ : syracuseStep 3174797 = 1190549) (by norm_num)
theorem B2116531 : Blo 2115435 2116531 := bstep (se 1 (by rfl) ⟨1587398, by rfl⟩ : syracuseStep 2116531 = 3174797) B3174797
theorem B4762205 : Blo 2115435 4762205 := bbase (se 3 (by rfl) ⟨892913, by rfl⟩ : syracuseStep 4762205 = 1785827) (by norm_num)
theorem B3174803 : Blo 2115435 3174803 := bstep (se 1 (by rfl) ⟨2381102, by rfl⟩ : syracuseStep 3174803 = 4762205) B4762205
theorem B2116535 : Blo 2115435 2116535 := bstep (se 1 (by rfl) ⟨1587401, by rfl⟩ : syracuseStep 2116535 = 3174803) B3174803
theorem B3571661 : Blo 2115435 3571661 := bbase (se 3 (by rfl) ⟨669686, by rfl⟩ : syracuseStep 3571661 = 1339373) (by norm_num)
theorem B2381107 : Blo 2115435 2381107 := bstep (se 1 (by rfl) ⟨1785830, by rfl⟩ : syracuseStep 2381107 = 3571661) B3571661
theorem B3174809 : Blo 2115435 3174809 := bstep (se 2 (by rfl) ⟨1190553, by rfl⟩ : syracuseStep 3174809 = 2381107) B2381107
theorem B2116539 : Blo 2115435 2116539 := bstep (se 1 (by rfl) ⟨1587404, by rfl⟩ : syracuseStep 2116539 = 3174809) B3174809
theorem B2145421 : Blo 2115435 2145421 := bbase (se 3 (by rfl) ⟨402266, by rfl⟩ : syracuseStep 2145421 = 804533) (by norm_num)
theorem B2860561 : Blo 2115435 2860561 := bstep (se 2 (by rfl) ⟨1072710, by rfl⟩ : syracuseStep 2860561 = 2145421) B2145421
theorem B15256325 : Blo 2115435 15256325 := bstep (se 4 (by rfl) ⟨1430280, by rfl⟩ : syracuseStep 15256325 = 2860561) B2860561
theorem B10170883 : Blo 2115435 10170883 := bstep (se 1 (by rfl) ⟨7628162, by rfl⟩ : syracuseStep 10170883 = 15256325) B15256325
theorem B13561177 : Blo 2115435 13561177 := bstep (se 2 (by rfl) ⟨5085441, by rfl⟩ : syracuseStep 13561177 = 10170883) B10170883
theorem B18081569 : Blo 2115435 18081569 := bstep (se 2 (by rfl) ⟨6780588, by rfl⟩ : syracuseStep 18081569 = 13561177) B13561177
theorem B12054379 : Blo 2115435 12054379 := bstep (se 1 (by rfl) ⟨9040784, by rfl⟩ : syracuseStep 12054379 = 18081569) B18081569
theorem B16072505 : Blo 2115435 16072505 := bstep (se 2 (by rfl) ⟨6027189, by rfl⟩ : syracuseStep 16072505 = 12054379) B12054379
theorem B10715003 : Blo 2115435 10715003 := bstep (se 1 (by rfl) ⟨8036252, by rfl⟩ : syracuseStep 10715003 = 16072505) B16072505
theorem B7143335 : Blo 2115435 7143335 := bstep (se 1 (by rfl) ⟨5357501, by rfl⟩ : syracuseStep 7143335 = 10715003) B10715003
theorem B4762223 : Blo 2115435 4762223 := bstep (se 1 (by rfl) ⟨3571667, by rfl⟩ : syracuseStep 4762223 = 7143335) B7143335
theorem B3174815 : Blo 2115435 3174815 := bstep (se 1 (by rfl) ⟨2381111, by rfl⟩ : syracuseStep 3174815 = 4762223) B4762223
theorem B2116543 : Blo 2115435 2116543 := bstep (se 1 (by rfl) ⟨1587407, by rfl⟩ : syracuseStep 2116543 = 3174815) B3174815
theorem B3174821 : Blo 2115435 3174821 := bbase (se 4 (by rfl) ⟨297639, by rfl⟩ : syracuseStep 3174821 = 595279) (by norm_num)
theorem B2116547 : Blo 2115435 2116547 := bstep (se 1 (by rfl) ⟨1587410, by rfl⟩ : syracuseStep 2116547 = 3174821) B3174821
theorem B2678761 : Blo 2115435 2678761 := bbase (se 2 (by rfl) ⟨1004535, by rfl⟩ : syracuseStep 2678761 = 2009071) (by norm_num)
theorem B3571681 : Blo 2115435 3571681 := bstep (se 2 (by rfl) ⟨1339380, by rfl⟩ : syracuseStep 3571681 = 2678761) B2678761
theorem B4762241 : Blo 2115435 4762241 := bstep (se 2 (by rfl) ⟨1785840, by rfl⟩ : syracuseStep 4762241 = 3571681) B3571681
theorem B3174827 : Blo 2115435 3174827 := bstep (se 1 (by rfl) ⟨2381120, by rfl⟩ : syracuseStep 3174827 = 4762241) B4762241
theorem B2116551 : Blo 2115435 2116551 := bstep (se 1 (by rfl) ⟨1587413, by rfl⟩ : syracuseStep 2116551 = 3174827) B3174827
theorem B2381125 : Blo 2115435 2381125 := bbase (se 4 (by rfl) ⟨223230, by rfl⟩ : syracuseStep 2381125 = 446461) (by norm_num)
theorem B3174833 : Blo 2115435 3174833 := bstep (se 2 (by rfl) ⟨1190562, by rfl⟩ : syracuseStep 3174833 = 2381125) B2381125
theorem B2116555 : Blo 2115435 2116555 := bstep (se 1 (by rfl) ⟨1587416, by rfl⟩ : syracuseStep 2116555 = 3174833) B3174833
theorem B4018157 : Blo 2115435 4018157 := bbase (se 3 (by rfl) ⟨753404, by rfl⟩ : syracuseStep 4018157 = 1506809) (by norm_num)
theorem B2678771 : Blo 2115435 2678771 := bstep (se 1 (by rfl) ⟨2009078, by rfl⟩ : syracuseStep 2678771 = 4018157) B4018157
theorem B7143389 : Blo 2115435 7143389 := bstep (se 3 (by rfl) ⟨1339385, by rfl⟩ : syracuseStep 7143389 = 2678771) B2678771
theorem B4762259 : Blo 2115435 4762259 := bstep (se 1 (by rfl) ⟨3571694, by rfl⟩ : syracuseStep 4762259 = 7143389) B7143389
theorem B3174839 : Blo 2115435 3174839 := bstep (se 1 (by rfl) ⟨2381129, by rfl⟩ : syracuseStep 3174839 = 4762259) B4762259
theorem B2116559 : Blo 2115435 2116559 := bstep (se 1 (by rfl) ⟨1587419, by rfl⟩ : syracuseStep 2116559 = 3174839) B3174839
theorem B3174845 : Blo 2115435 3174845 := bbase (se 3 (by rfl) ⟨595283, by rfl⟩ : syracuseStep 3174845 = 1190567) (by norm_num)
theorem B2116563 : Blo 2115435 2116563 := bstep (se 1 (by rfl) ⟨1587422, by rfl⟩ : syracuseStep 2116563 = 3174845) B3174845
theorem B4762277 : Blo 2115435 4762277 := bbase (se 4 (by rfl) ⟨446463, by rfl⟩ : syracuseStep 4762277 = 892927) (by norm_num)
theorem B3174851 : Blo 2115435 3174851 := bstep (se 1 (by rfl) ⟨2381138, by rfl⟩ : syracuseStep 3174851 = 4762277) B4762277
theorem B2116567 : Blo 2115435 2116567 := bstep (se 1 (by rfl) ⟨1587425, by rfl⟩ : syracuseStep 2116567 = 3174851) B3174851
theorem B5357573 : Blo 2115435 5357573 := bbase (se 4 (by rfl) ⟨502272, by rfl⟩ : syracuseStep 5357573 = 1004545) (by norm_num)
theorem B3571715 : Blo 2115435 3571715 := bstep (se 1 (by rfl) ⟨2678786, by rfl⟩ : syracuseStep 3571715 = 5357573) B5357573
theorem B2381143 : Blo 2115435 2381143 := bstep (se 1 (by rfl) ⟨1785857, by rfl⟩ : syracuseStep 2381143 = 3571715) B3571715
theorem B3174857 : Blo 2115435 3174857 := bstep (se 2 (by rfl) ⟨1190571, by rfl⟩ : syracuseStep 3174857 = 2381143) B2381143
theorem B2116571 : Blo 2115435 2116571 := bstep (se 1 (by rfl) ⟨1587428, by rfl⟩ : syracuseStep 2116571 = 3174857) B3174857
theorem B4520461 : Blo 2115435 4520461 := bbase (se 3 (by rfl) ⟨847586, by rfl⟩ : syracuseStep 4520461 = 1695173) (by norm_num)
theorem B6027281 : Blo 2115435 6027281 := bstep (se 2 (by rfl) ⟨2260230, by rfl⟩ : syracuseStep 6027281 = 4520461) B4520461
theorem B4018187 : Blo 2115435 4018187 := bstep (se 1 (by rfl) ⟨3013640, by rfl⟩ : syracuseStep 4018187 = 6027281) B6027281
theorem B10715165 : Blo 2115435 10715165 := bstep (se 3 (by rfl) ⟨2009093, by rfl⟩ : syracuseStep 10715165 = 4018187) B4018187
theorem B7143443 : Blo 2115435 7143443 := bstep (se 1 (by rfl) ⟨5357582, by rfl⟩ : syracuseStep 7143443 = 10715165) B10715165
theorem B4762295 : Blo 2115435 4762295 := bstep (se 1 (by rfl) ⟨3571721, by rfl⟩ : syracuseStep 4762295 = 7143443) B7143443
theorem B3174863 : Blo 2115435 3174863 := bstep (se 1 (by rfl) ⟨2381147, by rfl⟩ : syracuseStep 3174863 = 4762295) B4762295
theorem B2116575 : Blo 2115435 2116575 := bstep (se 1 (by rfl) ⟨1587431, by rfl⟩ : syracuseStep 2116575 = 3174863) B3174863
theorem B3174869 : Blo 2115435 3174869 := bbase (se 7 (by rfl) ⟨37205, by rfl⟩ : syracuseStep 3174869 = 74411) (by norm_num)
theorem B2116579 : Blo 2115435 2116579 := bstep (se 1 (by rfl) ⟨1587434, by rfl⟩ : syracuseStep 2116579 = 3174869) B3174869
theorem B8036405 : Blo 2115435 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B5357603 : Blo 2115435 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B3571735 : Blo 2115435 3571735 := bstep (se 1 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 3571735 = 5357603) B5357603
theorem B4762313 : Blo 2115435 4762313 := bstep (se 2 (by rfl) ⟨1785867, by rfl⟩ : syracuseStep 4762313 = 3571735) B3571735
theorem B3174875 : Blo 2115435 3174875 := bstep (se 1 (by rfl) ⟨2381156, by rfl⟩ : syracuseStep 3174875 = 4762313) B4762313
theorem B2116583 : Blo 2115435 2116583 := bstep (se 1 (by rfl) ⟨1587437, by rfl⟩ : syracuseStep 2116583 = 3174875) B3174875
theorem B2381161 : Blo 2115435 2381161 := bbase (se 2 (by rfl) ⟨892935, by rfl⟩ : syracuseStep 2381161 = 1785871) (by norm_num)
theorem B3174881 : Blo 2115435 3174881 := bstep (se 2 (by rfl) ⟨1190580, by rfl⟩ : syracuseStep 3174881 = 2381161) B2381161
theorem B2116587 : Blo 2115435 2116587 := bstep (se 1 (by rfl) ⟨1587440, by rfl⟩ : syracuseStep 2116587 = 3174881) B3174881
theorem B3054781 : Blo 2115435 3054781 := bbase (se 3 (by rfl) ⟨572771, by rfl⟩ : syracuseStep 3054781 = 1145543) (by norm_num)
theorem B4073041 : Blo 2115435 4073041 := bstep (se 2 (by rfl) ⟨1527390, by rfl⟩ : syracuseStep 4073041 = 3054781) B3054781
theorem B5430721 : Blo 2115435 5430721 := bstep (se 2 (by rfl) ⟨2036520, by rfl⟩ : syracuseStep 5430721 = 4073041) B4073041
theorem B7240961 : Blo 2115435 7240961 := bstep (se 2 (by rfl) ⟨2715360, by rfl⟩ : syracuseStep 7240961 = 5430721) B5430721
theorem B19309229 : Blo 2115435 19309229 := bstep (se 3 (by rfl) ⟨3620480, by rfl⟩ : syracuseStep 19309229 = 7240961) B7240961
theorem B12872819 : Blo 2115435 12872819 := bstep (se 1 (by rfl) ⟨9654614, by rfl⟩ : syracuseStep 12872819 = 19309229) B19309229
theorem B8581879 : Blo 2115435 8581879 := bstep (se 1 (by rfl) ⟨6436409, by rfl⟩ : syracuseStep 8581879 = 12872819) B12872819
theorem B11442505 : Blo 2115435 11442505 := bstep (se 2 (by rfl) ⟨4290939, by rfl⟩ : syracuseStep 11442505 = 8581879) B8581879
theorem B15256673 : Blo 2115435 15256673 := bstep (se 2 (by rfl) ⟨5721252, by rfl⟩ : syracuseStep 15256673 = 11442505) B11442505
theorem B10171115 : Blo 2115435 10171115 := bstep (se 1 (by rfl) ⟨7628336, by rfl⟩ : syracuseStep 10171115 = 15256673) B15256673
theorem B6780743 : Blo 2115435 6780743 := bstep (se 1 (by rfl) ⟨5085557, by rfl⟩ : syracuseStep 6780743 = 10171115) B10171115
theorem B4520495 : Blo 2115435 4520495 := bstep (se 1 (by rfl) ⟨3390371, by rfl⟩ : syracuseStep 4520495 = 6780743) B6780743
theorem B12054653 : Blo 2115435 12054653 := bstep (se 3 (by rfl) ⟨2260247, by rfl⟩ : syracuseStep 12054653 = 4520495) B4520495
theorem B8036435 : Blo 2115435 8036435 := bstep (se 1 (by rfl) ⟨6027326, by rfl⟩ : syracuseStep 8036435 = 12054653) B12054653
theorem B5357623 : Blo 2115435 5357623 := bstep (se 1 (by rfl) ⟨4018217, by rfl⟩ : syracuseStep 5357623 = 8036435) B8036435
theorem B7143497 : Blo 2115435 7143497 := bstep (se 2 (by rfl) ⟨2678811, by rfl⟩ : syracuseStep 7143497 = 5357623) B5357623
theorem B4762331 : Blo 2115435 4762331 := bstep (se 1 (by rfl) ⟨3571748, by rfl⟩ : syracuseStep 4762331 = 7143497) B7143497
theorem B3174887 : Blo 2115435 3174887 := bstep (se 1 (by rfl) ⟨2381165, by rfl⟩ : syracuseStep 3174887 = 4762331) B4762331
theorem B2116591 : Blo 2115435 2116591 := bstep (se 1 (by rfl) ⟨1587443, by rfl⟩ : syracuseStep 2116591 = 3174887) B3174887
theorem B3174893 : Blo 2115435 3174893 := bbase (se 3 (by rfl) ⟨595292, by rfl⟩ : syracuseStep 3174893 = 1190585) (by norm_num)
theorem B2116595 : Blo 2115435 2116595 := bstep (se 1 (by rfl) ⟨1587446, by rfl⟩ : syracuseStep 2116595 = 3174893) B3174893
theorem B4762349 : Blo 2115435 4762349 := bbase (se 3 (by rfl) ⟨892940, by rfl⟩ : syracuseStep 4762349 = 1785881) (by norm_num)
theorem B3174899 : Blo 2115435 3174899 := bstep (se 1 (by rfl) ⟨2381174, by rfl⟩ : syracuseStep 3174899 = 4762349) B4762349
theorem B2116599 : Blo 2115435 2116599 := bstep (se 1 (by rfl) ⟨1587449, by rfl⟩ : syracuseStep 2116599 = 3174899) B3174899
theorem B2260261 : Blo 2115435 2260261 := bbase (se 4 (by rfl) ⟨211899, by rfl⟩ : syracuseStep 2260261 = 423799) (by norm_num)
theorem B3013681 : Blo 2115435 3013681 := bstep (se 2 (by rfl) ⟨1130130, by rfl⟩ : syracuseStep 3013681 = 2260261) B2260261
theorem B4018241 : Blo 2115435 4018241 := bstep (se 2 (by rfl) ⟨1506840, by rfl⟩ : syracuseStep 4018241 = 3013681) B3013681
theorem B2678827 : Blo 2115435 2678827 := bstep (se 1 (by rfl) ⟨2009120, by rfl⟩ : syracuseStep 2678827 = 4018241) B4018241
theorem B3571769 : Blo 2115435 3571769 := bstep (se 2 (by rfl) ⟨1339413, by rfl⟩ : syracuseStep 3571769 = 2678827) B2678827
theorem B2381179 : Blo 2115435 2381179 := bstep (se 1 (by rfl) ⟨1785884, by rfl⟩ : syracuseStep 2381179 = 3571769) B3571769
theorem B3174905 : Blo 2115435 3174905 := bstep (se 2 (by rfl) ⟨1190589, by rfl⟩ : syracuseStep 3174905 = 2381179) B2381179
theorem B2116603 : Blo 2115435 2116603 := bstep (se 1 (by rfl) ⟨1587452, by rfl⟩ : syracuseStep 2116603 = 3174905) B3174905
theorem B11598709 : Blo 2115435 11598709 := bbase (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) (by norm_num)
theorem B15464945 : Blo 2115435 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B10309963 : Blo 2115435 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B13746617 : Blo 2115435 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B9164411 : Blo 2115435 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B6109607 : Blo 2115435 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B16292285 : Blo 2115435 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B10861523 : Blo 2115435 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B7241015 : Blo 2115435 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B4827343 : Blo 2115435 4827343 := bstep (se 1 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 4827343 = 7241015) B7241015
theorem B6436457 : Blo 2115435 6436457 := bstep (se 2 (by rfl) ⟨2413671, by rfl⟩ : syracuseStep 6436457 = 4827343) B4827343
theorem B4290971 : Blo 2115435 4290971 := bstep (se 1 (by rfl) ⟨3218228, by rfl⟩ : syracuseStep 4290971 = 6436457) B6436457
theorem B11442589 : Blo 2115435 11442589 := bstep (se 3 (by rfl) ⟨2145485, by rfl⟩ : syracuseStep 11442589 = 4290971) B4290971
theorem B61027141 : Blo 2115435 61027141 := bstep (se 4 (by rfl) ⟨5721294, by rfl⟩ : syracuseStep 61027141 = 11442589) B11442589
theorem B81369521 : Blo 2115435 81369521 := bstep (se 2 (by rfl) ⟨30513570, by rfl⟩ : syracuseStep 81369521 = 61027141) B61027141
theorem B54246347 : Blo 2115435 54246347 := bstep (se 1 (by rfl) ⟨40684760, by rfl⟩ : syracuseStep 54246347 = 81369521) B81369521
theorem B36164231 : Blo 2115435 36164231 := bstep (se 1 (by rfl) ⟨27123173, by rfl⟩ : syracuseStep 36164231 = 54246347) B54246347
theorem B24109487 : Blo 2115435 24109487 := bstep (se 1 (by rfl) ⟨18082115, by rfl⟩ : syracuseStep 24109487 = 36164231) B36164231
theorem B16072991 : Blo 2115435 16072991 := bstep (se 1 (by rfl) ⟨12054743, by rfl⟩ : syracuseStep 16072991 = 24109487) B24109487
theorem B10715327 : Blo 2115435 10715327 := bstep (se 1 (by rfl) ⟨8036495, by rfl⟩ : syracuseStep 10715327 = 16072991) B16072991
theorem B7143551 : Blo 2115435 7143551 := bstep (se 1 (by rfl) ⟨5357663, by rfl⟩ : syracuseStep 7143551 = 10715327) B10715327
theorem B4762367 : Blo 2115435 4762367 := bstep (se 1 (by rfl) ⟨3571775, by rfl⟩ : syracuseStep 4762367 = 7143551) B7143551
theorem B3174911 : Blo 2115435 3174911 := bstep (se 1 (by rfl) ⟨2381183, by rfl⟩ : syracuseStep 3174911 = 4762367) B4762367
theorem B2116607 : Blo 2115435 2116607 := bstep (se 1 (by rfl) ⟨1587455, by rfl⟩ : syracuseStep 2116607 = 3174911) B3174911
theorem B3174917 : Blo 2115435 3174917 := bbase (se 4 (by rfl) ⟨297648, by rfl⟩ : syracuseStep 3174917 = 595297) (by norm_num)
theorem B2116611 : Blo 2115435 2116611 := bstep (se 1 (by rfl) ⟨1587458, by rfl⟩ : syracuseStep 2116611 = 3174917) B3174917
theorem B3571789 : Blo 2115435 3571789 := bbase (se 3 (by rfl) ⟨669710, by rfl⟩ : syracuseStep 3571789 = 1339421) (by norm_num)
theorem B4762385 : Blo 2115435 4762385 := bstep (se 2 (by rfl) ⟨1785894, by rfl⟩ : syracuseStep 4762385 = 3571789) B3571789
theorem B3174923 : Blo 2115435 3174923 := bstep (se 1 (by rfl) ⟨2381192, by rfl⟩ : syracuseStep 3174923 = 4762385) B4762385
theorem B2116615 : Blo 2115435 2116615 := bstep (se 1 (by rfl) ⟨1587461, by rfl⟩ : syracuseStep 2116615 = 3174923) B3174923
theorem B2381197 : Blo 2115435 2381197 := bbase (se 3 (by rfl) ⟨446474, by rfl⟩ : syracuseStep 2381197 = 892949) (by norm_num)
theorem B3174929 : Blo 2115435 3174929 := bstep (se 2 (by rfl) ⟨1190598, by rfl⟩ : syracuseStep 3174929 = 2381197) B2381197
theorem B2116619 : Blo 2115435 2116619 := bstep (se 1 (by rfl) ⟨1587464, by rfl⟩ : syracuseStep 2116619 = 3174929) B3174929
theorem B7143605 : Blo 2115435 7143605 := bbase (se 5 (by rfl) ⟨334856, by rfl⟩ : syracuseStep 7143605 = 669713) (by norm_num)
theorem B4762403 : Blo 2115435 4762403 := bstep (se 1 (by rfl) ⟨3571802, by rfl⟩ : syracuseStep 4762403 = 7143605) B7143605
theorem B3174935 : Blo 2115435 3174935 := bstep (se 1 (by rfl) ⟨2381201, by rfl⟩ : syracuseStep 3174935 = 4762403) B4762403
theorem B2116623 : Blo 2115435 2116623 := bstep (se 1 (by rfl) ⟨1587467, by rfl⟩ : syracuseStep 2116623 = 3174935) B3174935
theorem B3174941 : Blo 2115435 3174941 := bbase (se 3 (by rfl) ⟨595301, by rfl⟩ : syracuseStep 3174941 = 1190603) (by norm_num)
theorem B2116627 : Blo 2115435 2116627 := bstep (se 1 (by rfl) ⟨1587470, by rfl⟩ : syracuseStep 2116627 = 3174941) B3174941
theorem B4762421 : Blo 2115435 4762421 := bbase (se 5 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 4762421 = 446477) (by norm_num)
theorem B3174947 : Blo 2115435 3174947 := bstep (se 1 (by rfl) ⟨2381210, by rfl⟩ : syracuseStep 3174947 = 4762421) B4762421
theorem B2116631 : Blo 2115435 2116631 := bstep (se 1 (by rfl) ⟨1587473, by rfl⟩ : syracuseStep 2116631 = 3174947) B3174947
theorem B6193045 : Blo 2115435 6193045 := bbase (se 6 (by rfl) ⟨145149, by rfl⟩ : syracuseStep 6193045 = 290299) (by norm_num)
theorem B8257393 : Blo 2115435 8257393 := bstep (se 2 (by rfl) ⟨3096522, by rfl⟩ : syracuseStep 8257393 = 6193045) B6193045
theorem B11009857 : Blo 2115435 11009857 := bstep (se 2 (by rfl) ⟨4128696, by rfl⟩ : syracuseStep 11009857 = 8257393) B8257393
theorem B14679809 : Blo 2115435 14679809 := bstep (se 2 (by rfl) ⟨5504928, by rfl⟩ : syracuseStep 14679809 = 11009857) B11009857
theorem B9786539 : Blo 2115435 9786539 := bstep (se 1 (by rfl) ⟨7339904, by rfl⟩ : syracuseStep 9786539 = 14679809) B14679809
theorem B26097437 : Blo 2115435 26097437 := bstep (se 3 (by rfl) ⟨4893269, by rfl⟩ : syracuseStep 26097437 = 9786539) B9786539
theorem B69593165 : Blo 2115435 69593165 := bstep (se 3 (by rfl) ⟨13048718, by rfl⟩ : syracuseStep 69593165 = 26097437) B26097437
theorem B46395443 : Blo 2115435 46395443 := bstep (se 1 (by rfl) ⟨34796582, by rfl⟩ : syracuseStep 46395443 = 69593165) B69593165
theorem B123721181 : Blo 2115435 123721181 := bstep (se 3 (by rfl) ⟨23197721, by rfl⟩ : syracuseStep 123721181 = 46395443) B46395443
theorem B82480787 : Blo 2115435 82480787 := bstep (se 1 (by rfl) ⟨61860590, by rfl⟩ : syracuseStep 82480787 = 123721181) B123721181
theorem B54987191 : Blo 2115435 54987191 := bstep (se 1 (by rfl) ⟨41240393, by rfl⟩ : syracuseStep 54987191 = 82480787) B82480787
theorem B36658127 : Blo 2115435 36658127 := bstep (se 1 (by rfl) ⟨27493595, by rfl⟩ : syracuseStep 36658127 = 54987191) B54987191
theorem B97755005 : Blo 2115435 97755005 := bstep (se 3 (by rfl) ⟨18329063, by rfl⟩ : syracuseStep 97755005 = 36658127) B36658127
theorem B65170003 : Blo 2115435 65170003 := bstep (se 1 (by rfl) ⟨48877502, by rfl⟩ : syracuseStep 65170003 = 97755005) B97755005
theorem B86893337 : Blo 2115435 86893337 := bstep (se 2 (by rfl) ⟨32585001, by rfl⟩ : syracuseStep 86893337 = 65170003) B65170003
theorem B57928891 : Blo 2115435 57928891 := bstep (se 1 (by rfl) ⟨43446668, by rfl⟩ : syracuseStep 57928891 = 86893337) B86893337
theorem B77238521 : Blo 2115435 77238521 := bstep (se 2 (by rfl) ⟨28964445, by rfl⟩ : syracuseStep 77238521 = 57928891) B57928891
theorem B51492347 : Blo 2115435 51492347 := bstep (se 1 (by rfl) ⟨38619260, by rfl⟩ : syracuseStep 51492347 = 77238521) B77238521
theorem B34328231 : Blo 2115435 34328231 := bstep (se 1 (by rfl) ⟨25746173, by rfl⟩ : syracuseStep 34328231 = 51492347) B51492347
theorem B22885487 : Blo 2115435 22885487 := bstep (se 1 (by rfl) ⟨17164115, by rfl⟩ : syracuseStep 22885487 = 34328231) B34328231
theorem B15256991 : Blo 2115435 15256991 := bstep (se 1 (by rfl) ⟨11442743, by rfl⟩ : syracuseStep 15256991 = 22885487) B22885487
theorem B10171327 : Blo 2115435 10171327 := bstep (se 1 (by rfl) ⟨7628495, by rfl⟩ : syracuseStep 10171327 = 15256991) B15256991
theorem B13561769 : Blo 2115435 13561769 := bstep (se 2 (by rfl) ⟨5085663, by rfl⟩ : syracuseStep 13561769 = 10171327) B10171327
theorem B9041179 : Blo 2115435 9041179 := bstep (se 1 (by rfl) ⟨6780884, by rfl⟩ : syracuseStep 9041179 = 13561769) B13561769
theorem B12054905 : Blo 2115435 12054905 := bstep (se 2 (by rfl) ⟨4520589, by rfl⟩ : syracuseStep 12054905 = 9041179) B9041179
theorem B8036603 : Blo 2115435 8036603 := bstep (se 1 (by rfl) ⟨6027452, by rfl⟩ : syracuseStep 8036603 = 12054905) B12054905
theorem B5357735 : Blo 2115435 5357735 := bstep (se 1 (by rfl) ⟨4018301, by rfl⟩ : syracuseStep 5357735 = 8036603) B8036603
theorem B3571823 : Blo 2115435 3571823 := bstep (se 1 (by rfl) ⟨2678867, by rfl⟩ : syracuseStep 3571823 = 5357735) B5357735
theorem B2381215 : Blo 2115435 2381215 := bstep (se 1 (by rfl) ⟨1785911, by rfl⟩ : syracuseStep 2381215 = 3571823) B3571823
theorem B3174953 : Blo 2115435 3174953 := bstep (se 2 (by rfl) ⟨1190607, by rfl⟩ : syracuseStep 3174953 = 2381215) B2381215
theorem B2116635 : Blo 2115435 2116635 := bstep (se 1 (by rfl) ⟨1587476, by rfl⟩ : syracuseStep 2116635 = 3174953) B3174953
theorem B4291037 : Blo 2115435 4291037 := bbase (se 3 (by rfl) ⟨804569, by rfl⟩ : syracuseStep 4291037 = 1609139) (by norm_num)
theorem B2860691 : Blo 2115435 2860691 := bstep (se 1 (by rfl) ⟨2145518, by rfl⟩ : syracuseStep 2860691 = 4291037) B4291037
theorem B7628509 : Blo 2115435 7628509 := bstep (se 3 (by rfl) ⟨1430345, by rfl⟩ : syracuseStep 7628509 = 2860691) B2860691
theorem B10171345 : Blo 2115435 10171345 := bstep (se 2 (by rfl) ⟨3814254, by rfl⟩ : syracuseStep 10171345 = 7628509) B7628509
theorem B13561793 : Blo 2115435 13561793 := bstep (se 2 (by rfl) ⟨5085672, by rfl⟩ : syracuseStep 13561793 = 10171345) B10171345
theorem B9041195 : Blo 2115435 9041195 := bstep (se 1 (by rfl) ⟨6780896, by rfl⟩ : syracuseStep 9041195 = 13561793) B13561793
theorem B6027463 : Blo 2115435 6027463 := bstep (se 1 (by rfl) ⟨4520597, by rfl⟩ : syracuseStep 6027463 = 9041195) B9041195
theorem B8036617 : Blo 2115435 8036617 := bstep (se 2 (by rfl) ⟨3013731, by rfl⟩ : syracuseStep 8036617 = 6027463) B6027463
theorem B10715489 : Blo 2115435 10715489 := bstep (se 2 (by rfl) ⟨4018308, by rfl⟩ : syracuseStep 10715489 = 8036617) B8036617
theorem B7143659 : Blo 2115435 7143659 := bstep (se 1 (by rfl) ⟨5357744, by rfl⟩ : syracuseStep 7143659 = 10715489) B10715489
theorem B4762439 : Blo 2115435 4762439 := bstep (se 1 (by rfl) ⟨3571829, by rfl⟩ : syracuseStep 4762439 = 7143659) B7143659
theorem B3174959 : Blo 2115435 3174959 := bstep (se 1 (by rfl) ⟨2381219, by rfl⟩ : syracuseStep 3174959 = 4762439) B4762439
theorem B2116639 : Blo 2115435 2116639 := bstep (se 1 (by rfl) ⟨1587479, by rfl⟩ : syracuseStep 2116639 = 3174959) B3174959
theorem B3174965 : Blo 2115435 3174965 := bbase (se 5 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 3174965 = 297653) (by norm_num)
theorem B2116643 : Blo 2115435 2116643 := bstep (se 1 (by rfl) ⟨1587482, by rfl⟩ : syracuseStep 2116643 = 3174965) B3174965
theorem B5357765 : Blo 2115435 5357765 := bbase (se 4 (by rfl) ⟨502290, by rfl⟩ : syracuseStep 5357765 = 1004581) (by norm_num)
theorem B3571843 : Blo 2115435 3571843 := bstep (se 1 (by rfl) ⟨2678882, by rfl⟩ : syracuseStep 3571843 = 5357765) B5357765
theorem B4762457 : Blo 2115435 4762457 := bstep (se 2 (by rfl) ⟨1785921, by rfl⟩ : syracuseStep 4762457 = 3571843) B3571843
theorem B3174971 : Blo 2115435 3174971 := bstep (se 1 (by rfl) ⟨2381228, by rfl⟩ : syracuseStep 3174971 = 4762457) B4762457
theorem B2116647 : Blo 2115435 2116647 := bstep (se 1 (by rfl) ⟨1587485, by rfl⟩ : syracuseStep 2116647 = 3174971) B3174971
theorem B2381233 : Blo 2115435 2381233 := bbase (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) (by norm_num)
theorem B3174977 : Blo 2115435 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B2116651 : Blo 2115435 2116651 := bstep (se 1 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 2116651 = 3174977) B3174977
theorem B6027509 : Blo 2115435 6027509 := bbase (se 5 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 6027509 = 565079) (by norm_num)
theorem B4018339 : Blo 2115435 4018339 := bstep (se 1 (by rfl) ⟨3013754, by rfl⟩ : syracuseStep 4018339 = 6027509) B6027509
theorem B5357785 : Blo 2115435 5357785 := bstep (se 2 (by rfl) ⟨2009169, by rfl⟩ : syracuseStep 5357785 = 4018339) B4018339
theorem B7143713 : Blo 2115435 7143713 := bstep (se 2 (by rfl) ⟨2678892, by rfl⟩ : syracuseStep 7143713 = 5357785) B5357785
theorem B4762475 : Blo 2115435 4762475 := bstep (se 1 (by rfl) ⟨3571856, by rfl⟩ : syracuseStep 4762475 = 7143713) B7143713
theorem B3174983 : Blo 2115435 3174983 := bstep (se 1 (by rfl) ⟨2381237, by rfl⟩ : syracuseStep 3174983 = 4762475) B4762475
theorem B2116655 : Blo 2115435 2116655 := bstep (se 1 (by rfl) ⟨1587491, by rfl⟩ : syracuseStep 2116655 = 3174983) B3174983
theorem B3174989 : Blo 2115435 3174989 := bbase (se 3 (by rfl) ⟨595310, by rfl⟩ : syracuseStep 3174989 = 1190621) (by norm_num)
theorem B2116659 : Blo 2115435 2116659 := bstep (se 1 (by rfl) ⟨1587494, by rfl⟩ : syracuseStep 2116659 = 3174989) B3174989
theorem B4762493 : Blo 2115435 4762493 := bbase (se 3 (by rfl) ⟨892967, by rfl⟩ : syracuseStep 4762493 = 1785935) (by norm_num)
theorem B3174995 : Blo 2115435 3174995 := bstep (se 1 (by rfl) ⟨2381246, by rfl⟩ : syracuseStep 3174995 = 4762493) B4762493
theorem B2116663 : Blo 2115435 2116663 := bstep (se 1 (by rfl) ⟨1587497, by rfl⟩ : syracuseStep 2116663 = 3174995) B3174995
theorem B3571877 : Blo 2115435 3571877 := bbase (se 4 (by rfl) ⟨334863, by rfl⟩ : syracuseStep 3571877 = 669727) (by norm_num)
theorem B2381251 : Blo 2115435 2381251 := bstep (se 1 (by rfl) ⟨1785938, by rfl⟩ : syracuseStep 2381251 = 3571877) B3571877
theorem B3175001 : Blo 2115435 3175001 := bstep (se 2 (by rfl) ⟨1190625, by rfl⟩ : syracuseStep 3175001 = 2381251) B2381251
theorem B2116667 : Blo 2115435 2116667 := bstep (se 1 (by rfl) ⟨1587500, by rfl⟩ : syracuseStep 2116667 = 3175001) B3175001
theorem B2260333 : Blo 2115435 2260333 := bbase (se 3 (by rfl) ⟨423812, by rfl⟩ : syracuseStep 2260333 = 847625) (by norm_num)
theorem B3013777 : Blo 2115435 3013777 := bstep (se 2 (by rfl) ⟨1130166, by rfl⟩ : syracuseStep 3013777 = 2260333) B2260333
theorem B16073477 : Blo 2115435 16073477 := bstep (se 4 (by rfl) ⟨1506888, by rfl⟩ : syracuseStep 16073477 = 3013777) B3013777
theorem B10715651 : Blo 2115435 10715651 := bstep (se 1 (by rfl) ⟨8036738, by rfl⟩ : syracuseStep 10715651 = 16073477) B16073477
theorem B7143767 : Blo 2115435 7143767 := bstep (se 1 (by rfl) ⟨5357825, by rfl⟩ : syracuseStep 7143767 = 10715651) B10715651
theorem B4762511 : Blo 2115435 4762511 := bstep (se 1 (by rfl) ⟨3571883, by rfl⟩ : syracuseStep 4762511 = 7143767) B7143767
theorem B3175007 : Blo 2115435 3175007 := bstep (se 1 (by rfl) ⟨2381255, by rfl⟩ : syracuseStep 3175007 = 4762511) B4762511
theorem B2116671 : Blo 2115435 2116671 := bstep (se 1 (by rfl) ⟨1587503, by rfl⟩ : syracuseStep 2116671 = 3175007) B3175007
theorem B3175013 : Blo 2115435 3175013 := bbase (se 4 (by rfl) ⟨297657, by rfl⟩ : syracuseStep 3175013 = 595315) (by norm_num)
theorem B2116675 : Blo 2115435 2116675 := bstep (se 1 (by rfl) ⟨1587506, by rfl⟩ : syracuseStep 2116675 = 3175013) B3175013
theorem B3013789 : Blo 2115435 3013789 := bbase (se 3 (by rfl) ⟨565085, by rfl⟩ : syracuseStep 3013789 = 1130171) (by norm_num)
theorem B4018385 : Blo 2115435 4018385 := bstep (se 2 (by rfl) ⟨1506894, by rfl⟩ : syracuseStep 4018385 = 3013789) B3013789
theorem B2678923 : Blo 2115435 2678923 := bstep (se 1 (by rfl) ⟨2009192, by rfl⟩ : syracuseStep 2678923 = 4018385) B4018385
theorem B3571897 : Blo 2115435 3571897 := bstep (se 2 (by rfl) ⟨1339461, by rfl⟩ : syracuseStep 3571897 = 2678923) B2678923
theorem B4762529 : Blo 2115435 4762529 := bstep (se 2 (by rfl) ⟨1785948, by rfl⟩ : syracuseStep 4762529 = 3571897) B3571897
theorem B3175019 : Blo 2115435 3175019 := bstep (se 1 (by rfl) ⟨2381264, by rfl⟩ : syracuseStep 3175019 = 4762529) B4762529
theorem B2116679 : Blo 2115435 2116679 := bstep (se 1 (by rfl) ⟨1587509, by rfl⟩ : syracuseStep 2116679 = 3175019) B3175019
theorem B2381269 : Blo 2115435 2381269 := bbase (se 7 (by rfl) ⟨27905, by rfl⟩ : syracuseStep 2381269 = 55811) (by norm_num)
theorem B3175025 : Blo 2115435 3175025 := bstep (se 2 (by rfl) ⟨1190634, by rfl⟩ : syracuseStep 3175025 = 2381269) B2381269
theorem B2116683 : Blo 2115435 2116683 := bstep (se 1 (by rfl) ⟨1587512, by rfl⟩ : syracuseStep 2116683 = 3175025) B3175025
theorem B2678933 : Blo 2115435 2678933 := bbase (se 6 (by rfl) ⟨62787, by rfl⟩ : syracuseStep 2678933 = 125575) (by norm_num)
theorem B7143821 : Blo 2115435 7143821 := bstep (se 3 (by rfl) ⟨1339466, by rfl⟩ : syracuseStep 7143821 = 2678933) B2678933
theorem B4762547 : Blo 2115435 4762547 := bstep (se 1 (by rfl) ⟨3571910, by rfl⟩ : syracuseStep 4762547 = 7143821) B7143821
theorem B3175031 : Blo 2115435 3175031 := bstep (se 1 (by rfl) ⟨2381273, by rfl⟩ : syracuseStep 3175031 = 4762547) B4762547
theorem B2116687 : Blo 2115435 2116687 := bstep (se 1 (by rfl) ⟨1587515, by rfl⟩ : syracuseStep 2116687 = 3175031) B3175031
theorem B3175037 : Blo 2115435 3175037 := bbase (se 3 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 3175037 = 1190639) (by norm_num)
theorem B2116691 : Blo 2115435 2116691 := bstep (se 1 (by rfl) ⟨1587518, by rfl⟩ : syracuseStep 2116691 = 3175037) B3175037
theorem B4762565 : Blo 2115435 4762565 := bbase (se 4 (by rfl) ⟨446490, by rfl⟩ : syracuseStep 4762565 = 892981) (by norm_num)
theorem B3175043 : Blo 2115435 3175043 := bstep (se 1 (by rfl) ⟨2381282, by rfl⟩ : syracuseStep 3175043 = 4762565) B4762565
theorem B2116695 : Blo 2115435 2116695 := bstep (se 1 (by rfl) ⟨1587521, by rfl⟩ : syracuseStep 2116695 = 3175043) B3175043
theorem B2542909 : Blo 2115435 2542909 := bbase (se 3 (by rfl) ⟨476795, by rfl⟩ : syracuseStep 2542909 = 953591) (by norm_num)
theorem B3390545 : Blo 2115435 3390545 := bstep (se 2 (by rfl) ⟨1271454, by rfl⟩ : syracuseStep 3390545 = 2542909) B2542909
theorem B9041453 : Blo 2115435 9041453 := bstep (se 3 (by rfl) ⟨1695272, by rfl⟩ : syracuseStep 9041453 = 3390545) B3390545
theorem B6027635 : Blo 2115435 6027635 := bstep (se 1 (by rfl) ⟨4520726, by rfl⟩ : syracuseStep 6027635 = 9041453) B9041453
theorem B4018423 : Blo 2115435 4018423 := bstep (se 1 (by rfl) ⟨3013817, by rfl⟩ : syracuseStep 4018423 = 6027635) B6027635
theorem B5357897 : Blo 2115435 5357897 := bstep (se 2 (by rfl) ⟨2009211, by rfl⟩ : syracuseStep 5357897 = 4018423) B4018423
theorem B3571931 : Blo 2115435 3571931 := bstep (se 1 (by rfl) ⟨2678948, by rfl⟩ : syracuseStep 3571931 = 5357897) B5357897
theorem B2381287 : Blo 2115435 2381287 := bstep (se 1 (by rfl) ⟨1785965, by rfl⟩ : syracuseStep 2381287 = 3571931) B3571931
theorem B3175049 : Blo 2115435 3175049 := bstep (se 2 (by rfl) ⟨1190643, by rfl⟩ : syracuseStep 3175049 = 2381287) B2381287
theorem B2116699 : Blo 2115435 2116699 := bstep (se 1 (by rfl) ⟨1587524, by rfl⟩ : syracuseStep 2116699 = 3175049) B3175049
theorem B10715813 : Blo 2115435 10715813 := bbase (se 4 (by rfl) ⟨1004607, by rfl⟩ : syracuseStep 10715813 = 2009215) (by norm_num)
theorem B7143875 : Blo 2115435 7143875 := bstep (se 1 (by rfl) ⟨5357906, by rfl⟩ : syracuseStep 7143875 = 10715813) B10715813
theorem B4762583 : Blo 2115435 4762583 := bstep (se 1 (by rfl) ⟨3571937, by rfl⟩ : syracuseStep 4762583 = 7143875) B7143875
theorem B3175055 : Blo 2115435 3175055 := bstep (se 1 (by rfl) ⟨2381291, by rfl⟩ : syracuseStep 3175055 = 4762583) B4762583
theorem B2116703 : Blo 2115435 2116703 := bstep (se 1 (by rfl) ⟨1587527, by rfl⟩ : syracuseStep 2116703 = 3175055) B3175055
theorem B3175061 : Blo 2115435 3175061 := bbase (se 6 (by rfl) ⟨74415, by rfl⟩ : syracuseStep 3175061 = 148831) (by norm_num)
theorem B2116707 : Blo 2115435 2116707 := bstep (se 1 (by rfl) ⟨1587530, by rfl⟩ : syracuseStep 2116707 = 3175061) B3175061
theorem B4827581 : Blo 2115435 4827581 := bbase (se 3 (by rfl) ⟨905171, by rfl⟩ : syracuseStep 4827581 = 1810343) (by norm_num)
theorem B3218387 : Blo 2115435 3218387 := bstep (se 1 (by rfl) ⟨2413790, by rfl⟩ : syracuseStep 3218387 = 4827581) B4827581
theorem B8582365 : Blo 2115435 8582365 := bstep (se 3 (by rfl) ⟨1609193, by rfl⟩ : syracuseStep 8582365 = 3218387) B3218387
theorem B45772613 : Blo 2115435 45772613 := bstep (se 4 (by rfl) ⟨4291182, by rfl⟩ : syracuseStep 45772613 = 8582365) B8582365
theorem B30515075 : Blo 2115435 30515075 := bstep (se 1 (by rfl) ⟨22886306, by rfl⟩ : syracuseStep 30515075 = 45772613) B45772613
theorem B20343383 : Blo 2115435 20343383 := bstep (se 1 (by rfl) ⟨15257537, by rfl⟩ : syracuseStep 20343383 = 30515075) B30515075
theorem B13562255 : Blo 2115435 13562255 := bstep (se 1 (by rfl) ⟨10171691, by rfl⟩ : syracuseStep 13562255 = 20343383) B20343383
theorem B9041503 : Blo 2115435 9041503 := bstep (se 1 (by rfl) ⟨6781127, by rfl⟩ : syracuseStep 9041503 = 13562255) B13562255
theorem B12055337 : Blo 2115435 12055337 := bstep (se 2 (by rfl) ⟨4520751, by rfl⟩ : syracuseStep 12055337 = 9041503) B9041503
theorem B8036891 : Blo 2115435 8036891 := bstep (se 1 (by rfl) ⟨6027668, by rfl⟩ : syracuseStep 8036891 = 12055337) B12055337
theorem B5357927 : Blo 2115435 5357927 := bstep (se 1 (by rfl) ⟨4018445, by rfl⟩ : syracuseStep 5357927 = 8036891) B8036891
theorem B3571951 : Blo 2115435 3571951 := bstep (se 1 (by rfl) ⟨2678963, by rfl⟩ : syracuseStep 3571951 = 5357927) B5357927
theorem B4762601 : Blo 2115435 4762601 := bstep (se 2 (by rfl) ⟨1785975, by rfl⟩ : syracuseStep 4762601 = 3571951) B3571951
theorem B3175067 : Blo 2115435 3175067 := bstep (se 1 (by rfl) ⟨2381300, by rfl⟩ : syracuseStep 3175067 = 4762601) B4762601
theorem B2116711 : Blo 2115435 2116711 := bstep (se 1 (by rfl) ⟨1587533, by rfl⟩ : syracuseStep 2116711 = 3175067) B3175067
theorem B2381305 : Blo 2115435 2381305 := bbase (se 2 (by rfl) ⟨892989, by rfl⟩ : syracuseStep 2381305 = 1785979) (by norm_num)
theorem B3175073 : Blo 2115435 3175073 := bstep (se 2 (by rfl) ⟨1190652, by rfl⟩ : syracuseStep 3175073 = 2381305) B2381305
theorem B2116715 : Blo 2115435 2116715 := bstep (se 1 (by rfl) ⟨1587536, by rfl⟩ : syracuseStep 2116715 = 3175073) B3175073
theorem B2446733 : Blo 2115435 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B6524621 : Blo 2115435 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B4349747 : Blo 2115435 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B2899831 : Blo 2115435 2899831 := bstep (se 1 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 2899831 = 4349747) B4349747
theorem B3866441 : Blo 2115435 3866441 := bstep (se 2 (by rfl) ⟨1449915, by rfl⟩ : syracuseStep 3866441 = 2899831) B2899831
theorem B10310509 : Blo 2115435 10310509 := bstep (se 3 (by rfl) ⟨1933220, by rfl⟩ : syracuseStep 10310509 = 3866441) B3866441
theorem B54989381 : Blo 2115435 54989381 := bstep (se 4 (by rfl) ⟨5155254, by rfl⟩ : syracuseStep 54989381 = 10310509) B10310509
theorem B146638349 : Blo 2115435 146638349 := bstep (se 3 (by rfl) ⟨27494690, by rfl⟩ : syracuseStep 146638349 = 54989381) B54989381
theorem B97758899 : Blo 2115435 97758899 := bstep (se 1 (by rfl) ⟨73319174, by rfl⟩ : syracuseStep 97758899 = 146638349) B146638349
theorem B65172599 : Blo 2115435 65172599 := bstep (se 1 (by rfl) ⟨48879449, by rfl⟩ : syracuseStep 65172599 = 97758899) B97758899
theorem B43448399 : Blo 2115435 43448399 := bstep (se 1 (by rfl) ⟨32586299, by rfl⟩ : syracuseStep 43448399 = 65172599) B65172599
theorem B28965599 : Blo 2115435 28965599 := bstep (se 1 (by rfl) ⟨21724199, by rfl⟩ : syracuseStep 28965599 = 43448399) B43448399
theorem B19310399 : Blo 2115435 19310399 := bstep (se 1 (by rfl) ⟨14482799, by rfl⟩ : syracuseStep 19310399 = 28965599) B28965599
theorem B12873599 : Blo 2115435 12873599 := bstep (se 1 (by rfl) ⟨9655199, by rfl⟩ : syracuseStep 12873599 = 19310399) B19310399
theorem B8582399 : Blo 2115435 8582399 := bstep (se 1 (by rfl) ⟨6436799, by rfl⟩ : syracuseStep 8582399 = 12873599) B12873599
theorem B5721599 : Blo 2115435 5721599 := bstep (se 1 (by rfl) ⟨4291199, by rfl⟩ : syracuseStep 5721599 = 8582399) B8582399
theorem B3814399 : Blo 2115435 3814399 := bstep (se 1 (by rfl) ⟨2860799, by rfl⟩ : syracuseStep 3814399 = 5721599) B5721599
theorem B5085865 : Blo 2115435 5085865 := bstep (se 2 (by rfl) ⟨1907199, by rfl⟩ : syracuseStep 5085865 = 3814399) B3814399
theorem B6781153 : Blo 2115435 6781153 := bstep (se 2 (by rfl) ⟨2542932, by rfl⟩ : syracuseStep 6781153 = 5085865) B5085865
theorem B9041537 : Blo 2115435 9041537 := bstep (se 2 (by rfl) ⟨3390576, by rfl⟩ : syracuseStep 9041537 = 6781153) B6781153
theorem B6027691 : Blo 2115435 6027691 := bstep (se 1 (by rfl) ⟨4520768, by rfl⟩ : syracuseStep 6027691 = 9041537) B9041537
theorem B8036921 : Blo 2115435 8036921 := bstep (se 2 (by rfl) ⟨3013845, by rfl⟩ : syracuseStep 8036921 = 6027691) B6027691
theorem B5357947 : Blo 2115435 5357947 := bstep (se 1 (by rfl) ⟨4018460, by rfl⟩ : syracuseStep 5357947 = 8036921) B8036921
theorem B7143929 : Blo 2115435 7143929 := bstep (se 2 (by rfl) ⟨2678973, by rfl⟩ : syracuseStep 7143929 = 5357947) B5357947
theorem B4762619 : Blo 2115435 4762619 := bstep (se 1 (by rfl) ⟨3571964, by rfl⟩ : syracuseStep 4762619 = 7143929) B7143929
theorem B3175079 : Blo 2115435 3175079 := bstep (se 1 (by rfl) ⟨2381309, by rfl⟩ : syracuseStep 3175079 = 4762619) B4762619
theorem B2116719 : Blo 2115435 2116719 := bstep (se 1 (by rfl) ⟨1587539, by rfl⟩ : syracuseStep 2116719 = 3175079) B3175079
theorem B3175085 : Blo 2115435 3175085 := bbase (se 3 (by rfl) ⟨595328, by rfl⟩ : syracuseStep 3175085 = 1190657) (by norm_num)
theorem B2116723 : Blo 2115435 2116723 := bstep (se 1 (by rfl) ⟨1587542, by rfl⟩ : syracuseStep 2116723 = 3175085) B3175085
theorem B4762637 : Blo 2115435 4762637 := bbase (se 3 (by rfl) ⟨892994, by rfl⟩ : syracuseStep 4762637 = 1785989) (by norm_num)
theorem B3175091 : Blo 2115435 3175091 := bstep (se 1 (by rfl) ⟨2381318, by rfl⟩ : syracuseStep 3175091 = 4762637) B4762637
theorem B2116727 : Blo 2115435 2116727 := bstep (se 1 (by rfl) ⟨1587545, by rfl⟩ : syracuseStep 2116727 = 3175091) B3175091
theorem B2678989 : Blo 2115435 2678989 := bbase (se 3 (by rfl) ⟨502310, by rfl⟩ : syracuseStep 2678989 = 1004621) (by norm_num)
theorem B3571985 : Blo 2115435 3571985 := bstep (se 2 (by rfl) ⟨1339494, by rfl⟩ : syracuseStep 3571985 = 2678989) B2678989
theorem B2381323 : Blo 2115435 2381323 := bstep (se 1 (by rfl) ⟨1785992, by rfl⟩ : syracuseStep 2381323 = 3571985) B3571985
theorem B3175097 : Blo 2115435 3175097 := bstep (se 2 (by rfl) ⟨1190661, by rfl⟩ : syracuseStep 3175097 = 2381323) B2381323
theorem B2116731 : Blo 2115435 2116731 := bstep (se 1 (by rfl) ⟨1587548, by rfl⟩ : syracuseStep 2116731 = 3175097) B3175097
theorem B2715545 : Blo 2115435 2715545 := bbase (se 2 (by rfl) ⟨1018329, by rfl⟩ : syracuseStep 2715545 = 2036659) (by norm_num)
theorem B7241453 : Blo 2115435 7241453 := bstep (se 3 (by rfl) ⟨1357772, by rfl⟩ : syracuseStep 7241453 = 2715545) B2715545
theorem B4827635 : Blo 2115435 4827635 := bstep (se 1 (by rfl) ⟨3620726, by rfl⟩ : syracuseStep 4827635 = 7241453) B7241453
theorem B3218423 : Blo 2115435 3218423 := bstep (se 1 (by rfl) ⟨2413817, by rfl⟩ : syracuseStep 3218423 = 4827635) B4827635
theorem B34329845 : Blo 2115435 34329845 := bstep (se 5 (by rfl) ⟨1609211, by rfl⟩ : syracuseStep 34329845 = 3218423) B3218423
theorem B22886563 : Blo 2115435 22886563 := bstep (se 1 (by rfl) ⟨17164922, by rfl⟩ : syracuseStep 22886563 = 34329845) B34329845
theorem B30515417 : Blo 2115435 30515417 := bstep (se 2 (by rfl) ⟨11443281, by rfl⟩ : syracuseStep 30515417 = 22886563) B22886563
theorem B20343611 : Blo 2115435 20343611 := bstep (se 1 (by rfl) ⟨15257708, by rfl⟩ : syracuseStep 20343611 = 30515417) B30515417
theorem B13562407 : Blo 2115435 13562407 := bstep (se 1 (by rfl) ⟨10171805, by rfl⟩ : syracuseStep 13562407 = 20343611) B20343611
theorem B18083209 : Blo 2115435 18083209 := bstep (se 2 (by rfl) ⟨6781203, by rfl⟩ : syracuseStep 18083209 = 13562407) B13562407
theorem B24110945 : Blo 2115435 24110945 := bstep (se 2 (by rfl) ⟨9041604, by rfl⟩ : syracuseStep 24110945 = 18083209) B18083209
theorem B16073963 : Blo 2115435 16073963 := bstep (se 1 (by rfl) ⟨12055472, by rfl⟩ : syracuseStep 16073963 = 24110945) B24110945
theorem B10715975 : Blo 2115435 10715975 := bstep (se 1 (by rfl) ⟨8036981, by rfl⟩ : syracuseStep 10715975 = 16073963) B16073963
theorem B7143983 : Blo 2115435 7143983 := bstep (se 1 (by rfl) ⟨5357987, by rfl⟩ : syracuseStep 7143983 = 10715975) B10715975
theorem B4762655 : Blo 2115435 4762655 := bstep (se 1 (by rfl) ⟨3571991, by rfl⟩ : syracuseStep 4762655 = 7143983) B7143983
theorem B3175103 : Blo 2115435 3175103 := bstep (se 1 (by rfl) ⟨2381327, by rfl⟩ : syracuseStep 3175103 = 4762655) B4762655
theorem B2116735 : Blo 2115435 2116735 := bstep (se 1 (by rfl) ⟨1587551, by rfl⟩ : syracuseStep 2116735 = 3175103) B3175103
theorem B3175109 : Blo 2115435 3175109 := bbase (se 4 (by rfl) ⟨297666, by rfl⟩ : syracuseStep 3175109 = 595333) (by norm_num)
theorem B2116739 : Blo 2115435 2116739 := bstep (se 1 (by rfl) ⟨1587554, by rfl⟩ : syracuseStep 2116739 = 3175109) B3175109
theorem B3572005 : Blo 2115435 3572005 := bbase (se 4 (by rfl) ⟨334875, by rfl⟩ : syracuseStep 3572005 = 669751) (by norm_num)
theorem B4762673 : Blo 2115435 4762673 := bstep (se 2 (by rfl) ⟨1786002, by rfl⟩ : syracuseStep 4762673 = 3572005) B3572005
theorem B3175115 : Blo 2115435 3175115 := bstep (se 1 (by rfl) ⟨2381336, by rfl⟩ : syracuseStep 3175115 = 4762673) B4762673
theorem B2116743 : Blo 2115435 2116743 := bstep (se 1 (by rfl) ⟨1587557, by rfl⟩ : syracuseStep 2116743 = 3175115) B3175115
theorem B2381341 : Blo 2115435 2381341 := bbase (se 3 (by rfl) ⟨446501, by rfl⟩ : syracuseStep 2381341 = 893003) (by norm_num)
theorem B3175121 : Blo 2115435 3175121 := bstep (se 2 (by rfl) ⟨1190670, by rfl⟩ : syracuseStep 3175121 = 2381341) B2381341
theorem B2116747 : Blo 2115435 2116747 := bstep (se 1 (by rfl) ⟨1587560, by rfl⟩ : syracuseStep 2116747 = 3175121) B3175121
theorem B7144037 : Blo 2115435 7144037 := bbase (se 4 (by rfl) ⟨669753, by rfl⟩ : syracuseStep 7144037 = 1339507) (by norm_num)
theorem B4762691 : Blo 2115435 4762691 := bstep (se 1 (by rfl) ⟨3572018, by rfl⟩ : syracuseStep 4762691 = 7144037) B7144037
theorem B3175127 : Blo 2115435 3175127 := bstep (se 1 (by rfl) ⟨2381345, by rfl⟩ : syracuseStep 3175127 = 4762691) B4762691
theorem B2116751 : Blo 2115435 2116751 := bstep (se 1 (by rfl) ⟨1587563, by rfl⟩ : syracuseStep 2116751 = 3175127) B3175127
theorem B3175133 : Blo 2115435 3175133 := bbase (se 3 (by rfl) ⟨595337, by rfl⟩ : syracuseStep 3175133 = 1190675) (by norm_num)
theorem B2116755 : Blo 2115435 2116755 := bstep (se 1 (by rfl) ⟨1587566, by rfl⟩ : syracuseStep 2116755 = 3175133) B3175133
theorem B4762709 : Blo 2115435 4762709 := bbase (se 8 (by rfl) ⟨27906, by rfl⟩ : syracuseStep 4762709 = 55813) (by norm_num)
theorem B3175139 : Blo 2115435 3175139 := bstep (se 1 (by rfl) ⟨2381354, by rfl⟩ : syracuseStep 3175139 = 4762709) B4762709
theorem B2116759 : Blo 2115435 2116759 := bstep (se 1 (by rfl) ⟨1587569, by rfl⟩ : syracuseStep 2116759 = 3175139) B3175139
theorem B25747733 : Blo 2115435 25747733 := bbase (se 6 (by rfl) ⟨603462, by rfl⟩ : syracuseStep 25747733 = 1206925) (by norm_num)
theorem B17165155 : Blo 2115435 17165155 := bstep (se 1 (by rfl) ⟨12873866, by rfl⟩ : syracuseStep 17165155 = 25747733) B25747733
theorem B22886873 : Blo 2115435 22886873 := bstep (se 2 (by rfl) ⟨8582577, by rfl⟩ : syracuseStep 22886873 = 17165155) B17165155
theorem B15257915 : Blo 2115435 15257915 := bstep (se 1 (by rfl) ⟨11443436, by rfl⟩ : syracuseStep 15257915 = 22886873) B22886873
theorem B10171943 : Blo 2115435 10171943 := bstep (se 1 (by rfl) ⟨7628957, by rfl⟩ : syracuseStep 10171943 = 15257915) B15257915
theorem B6781295 : Blo 2115435 6781295 := bstep (se 1 (by rfl) ⟨5085971, by rfl⟩ : syracuseStep 6781295 = 10171943) B10171943
theorem B4520863 : Blo 2115435 4520863 := bstep (se 1 (by rfl) ⟨3390647, by rfl⟩ : syracuseStep 4520863 = 6781295) B6781295
theorem B6027817 : Blo 2115435 6027817 := bstep (se 2 (by rfl) ⟨2260431, by rfl⟩ : syracuseStep 6027817 = 4520863) B4520863
theorem B8037089 : Blo 2115435 8037089 := bstep (se 2 (by rfl) ⟨3013908, by rfl⟩ : syracuseStep 8037089 = 6027817) B6027817
theorem B5358059 : Blo 2115435 5358059 := bstep (se 1 (by rfl) ⟨4018544, by rfl⟩ : syracuseStep 5358059 = 8037089) B8037089
theorem B3572039 : Blo 2115435 3572039 := bstep (se 1 (by rfl) ⟨2679029, by rfl⟩ : syracuseStep 3572039 = 5358059) B5358059
theorem B2381359 : Blo 2115435 2381359 := bstep (se 1 (by rfl) ⟨1786019, by rfl⟩ : syracuseStep 2381359 = 3572039) B3572039
theorem B3175145 : Blo 2115435 3175145 := bstep (se 2 (by rfl) ⟨1190679, by rfl⟩ : syracuseStep 3175145 = 2381359) B2381359
theorem B2116763 : Blo 2115435 2116763 := bstep (se 1 (by rfl) ⟨1587572, by rfl⟩ : syracuseStep 2116763 = 3175145) B3175145
theorem B6704021 : Blo 2115435 6704021 := bbase (se 6 (by rfl) ⟨157125, by rfl⟩ : syracuseStep 6704021 = 314251) (by norm_num)
theorem B4469347 : Blo 2115435 4469347 := bstep (se 1 (by rfl) ⟨3352010, by rfl⟩ : syracuseStep 4469347 = 6704021) B6704021
theorem B5959129 : Blo 2115435 5959129 := bstep (se 2 (by rfl) ⟨2234673, by rfl⟩ : syracuseStep 5959129 = 4469347) B4469347
theorem B7945505 : Blo 2115435 7945505 := bstep (se 2 (by rfl) ⟨2979564, by rfl⟩ : syracuseStep 7945505 = 5959129) B5959129
theorem B5297003 : Blo 2115435 5297003 := bstep (se 1 (by rfl) ⟨3972752, by rfl⟩ : syracuseStep 5297003 = 7945505) B7945505
theorem B3531335 : Blo 2115435 3531335 := bstep (se 1 (by rfl) ⟨2648501, by rfl⟩ : syracuseStep 3531335 = 5297003) B5297003
theorem B37667573 : Blo 2115435 37667573 := bstep (se 5 (by rfl) ⟨1765667, by rfl⟩ : syracuseStep 37667573 = 3531335) B3531335
theorem B25111715 : Blo 2115435 25111715 := bstep (se 1 (by rfl) ⟨18833786, by rfl⟩ : syracuseStep 25111715 = 37667573) B37667573
theorem B66964573 : Blo 2115435 66964573 := bstep (se 3 (by rfl) ⟨12555857, by rfl⟩ : syracuseStep 66964573 = 25111715) B25111715
theorem B89286097 : Blo 2115435 89286097 := bstep (se 2 (by rfl) ⟨33482286, by rfl⟩ : syracuseStep 89286097 = 66964573) B66964573
theorem B119048129 : Blo 2115435 119048129 := bstep (se 2 (by rfl) ⟨44643048, by rfl⟩ : syracuseStep 119048129 = 89286097) B89286097
theorem B79365419 : Blo 2115435 79365419 := bstep (se 1 (by rfl) ⟨59524064, by rfl⟩ : syracuseStep 79365419 = 119048129) B119048129
theorem B52910279 : Blo 2115435 52910279 := bstep (se 1 (by rfl) ⟨39682709, by rfl⟩ : syracuseStep 52910279 = 79365419) B79365419
theorem B35273519 : Blo 2115435 35273519 := bstep (se 1 (by rfl) ⟨26455139, by rfl⟩ : syracuseStep 35273519 = 52910279) B52910279
theorem B23515679 : Blo 2115435 23515679 := bstep (se 1 (by rfl) ⟨17636759, by rfl⟩ : syracuseStep 23515679 = 35273519) B35273519
theorem B15677119 : Blo 2115435 15677119 := bstep (se 1 (by rfl) ⟨11757839, by rfl⟩ : syracuseStep 15677119 = 23515679) B23515679
theorem B20902825 : Blo 2115435 20902825 := bstep (se 2 (by rfl) ⟨7838559, by rfl⟩ : syracuseStep 20902825 = 15677119) B15677119
theorem B111481733 : Blo 2115435 111481733 := bstep (se 4 (by rfl) ⟨10451412, by rfl⟩ : syracuseStep 111481733 = 20902825) B20902825
theorem B74321155 : Blo 2115435 74321155 := bstep (se 1 (by rfl) ⟨55740866, by rfl⟩ : syracuseStep 74321155 = 111481733) B111481733
theorem B99094873 : Blo 2115435 99094873 := bstep (se 2 (by rfl) ⟨37160577, by rfl⟩ : syracuseStep 99094873 = 74321155) B74321155
theorem B132126497 : Blo 2115435 132126497 := bstep (se 2 (by rfl) ⟨49547436, by rfl⟩ : syracuseStep 132126497 = 99094873) B99094873
theorem B88084331 : Blo 2115435 88084331 := bstep (se 1 (by rfl) ⟨66063248, by rfl⟩ : syracuseStep 88084331 = 132126497) B132126497
theorem B58722887 : Blo 2115435 58722887 := bstep (se 1 (by rfl) ⟨44042165, by rfl⟩ : syracuseStep 58722887 = 88084331) B88084331
theorem B39148591 : Blo 2115435 39148591 := bstep (se 1 (by rfl) ⟨29361443, by rfl⟩ : syracuseStep 39148591 = 58722887) B58722887
theorem B52198121 : Blo 2115435 52198121 := bstep (se 2 (by rfl) ⟨19574295, by rfl⟩ : syracuseStep 52198121 = 39148591) B39148591
theorem B34798747 : Blo 2115435 34798747 := bstep (se 1 (by rfl) ⟨26099060, by rfl⟩ : syracuseStep 34798747 = 52198121) B52198121
theorem B46398329 : Blo 2115435 46398329 := bstep (se 2 (by rfl) ⟨17399373, by rfl⟩ : syracuseStep 46398329 = 34798747) B34798747
theorem B30932219 : Blo 2115435 30932219 := bstep (se 1 (by rfl) ⟨23199164, by rfl⟩ : syracuseStep 30932219 = 46398329) B46398329
theorem B20621479 : Blo 2115435 20621479 := bstep (se 1 (by rfl) ⟨15466109, by rfl⟩ : syracuseStep 20621479 = 30932219) B30932219
theorem B27495305 : Blo 2115435 27495305 := bstep (se 2 (by rfl) ⟨10310739, by rfl⟩ : syracuseStep 27495305 = 20621479) B20621479
theorem B18330203 : Blo 2115435 18330203 := bstep (se 1 (by rfl) ⟨13747652, by rfl⟩ : syracuseStep 18330203 = 27495305) B27495305
theorem B12220135 : Blo 2115435 12220135 := bstep (se 1 (by rfl) ⟨9165101, by rfl⟩ : syracuseStep 12220135 = 18330203) B18330203
theorem B65174053 : Blo 2115435 65174053 := bstep (se 4 (by rfl) ⟨6110067, by rfl⟩ : syracuseStep 65174053 = 12220135) B12220135
theorem B86898737 : Blo 2115435 86898737 := bstep (se 2 (by rfl) ⟨32587026, by rfl⟩ : syracuseStep 86898737 = 65174053) B65174053
theorem B57932491 : Blo 2115435 57932491 := bstep (se 1 (by rfl) ⟨43449368, by rfl⟩ : syracuseStep 57932491 = 86898737) B86898737
theorem B77243321 : Blo 2115435 77243321 := bstep (se 2 (by rfl) ⟨28966245, by rfl⟩ : syracuseStep 77243321 = 57932491) B57932491
theorem B51495547 : Blo 2115435 51495547 := bstep (se 1 (by rfl) ⟨38621660, by rfl⟩ : syracuseStep 51495547 = 77243321) B77243321
theorem B68660729 : Blo 2115435 68660729 := bstep (se 2 (by rfl) ⟨25747773, by rfl⟩ : syracuseStep 68660729 = 51495547) B51495547
theorem B45773819 : Blo 2115435 45773819 := bstep (se 1 (by rfl) ⟨34330364, by rfl⟩ : syracuseStep 45773819 = 68660729) B68660729
theorem B30515879 : Blo 2115435 30515879 := bstep (se 1 (by rfl) ⟨22886909, by rfl⟩ : syracuseStep 30515879 = 45773819) B45773819
theorem B20343919 : Blo 2115435 20343919 := bstep (se 1 (by rfl) ⟨15257939, by rfl⟩ : syracuseStep 20343919 = 30515879) B30515879
theorem B27125225 : Blo 2115435 27125225 := bstep (se 2 (by rfl) ⟨10171959, by rfl⟩ : syracuseStep 27125225 = 20343919) B20343919
theorem B18083483 : Blo 2115435 18083483 := bstep (se 1 (by rfl) ⟨13562612, by rfl⟩ : syracuseStep 18083483 = 27125225) B27125225
theorem B12055655 : Blo 2115435 12055655 := bstep (se 1 (by rfl) ⟨9041741, by rfl⟩ : syracuseStep 12055655 = 18083483) B18083483
theorem B8037103 : Blo 2115435 8037103 := bstep (se 1 (by rfl) ⟨6027827, by rfl⟩ : syracuseStep 8037103 = 12055655) B12055655
theorem B10716137 : Blo 2115435 10716137 := bstep (se 2 (by rfl) ⟨4018551, by rfl⟩ : syracuseStep 10716137 = 8037103) B8037103
theorem B7144091 : Blo 2115435 7144091 := bstep (se 1 (by rfl) ⟨5358068, by rfl⟩ : syracuseStep 7144091 = 10716137) B10716137
theorem B4762727 : Blo 2115435 4762727 := bstep (se 1 (by rfl) ⟨3572045, by rfl⟩ : syracuseStep 4762727 = 7144091) B7144091
theorem B3175151 : Blo 2115435 3175151 := bstep (se 1 (by rfl) ⟨2381363, by rfl⟩ : syracuseStep 3175151 = 4762727) B4762727
theorem B2116767 : Blo 2115435 2116767 := bstep (se 1 (by rfl) ⟨1587575, by rfl⟩ : syracuseStep 2116767 = 3175151) B3175151
theorem B3175157 : Blo 2115435 3175157 := bbase (se 5 (by rfl) ⟨148835, by rfl⟩ : syracuseStep 3175157 = 297671) (by norm_num)
theorem B2116771 : Blo 2115435 2116771 := bstep (se 1 (by rfl) ⟨1587578, by rfl⟩ : syracuseStep 2116771 = 3175157) B3175157
theorem B6781333 : Blo 2115435 6781333 := bbase (se 6 (by rfl) ⟨158937, by rfl⟩ : syracuseStep 6781333 = 317875) (by norm_num)
theorem B9041777 : Blo 2115435 9041777 := bstep (se 2 (by rfl) ⟨3390666, by rfl⟩ : syracuseStep 9041777 = 6781333) B6781333
theorem B6027851 : Blo 2115435 6027851 := bstep (se 1 (by rfl) ⟨4520888, by rfl⟩ : syracuseStep 6027851 = 9041777) B9041777
theorem B4018567 : Blo 2115435 4018567 := bstep (se 1 (by rfl) ⟨3013925, by rfl⟩ : syracuseStep 4018567 = 6027851) B6027851
theorem B5358089 : Blo 2115435 5358089 := bstep (se 2 (by rfl) ⟨2009283, by rfl⟩ : syracuseStep 5358089 = 4018567) B4018567
theorem B3572059 : Blo 2115435 3572059 := bstep (se 1 (by rfl) ⟨2679044, by rfl⟩ : syracuseStep 3572059 = 5358089) B5358089
theorem B4762745 : Blo 2115435 4762745 := bstep (se 2 (by rfl) ⟨1786029, by rfl⟩ : syracuseStep 4762745 = 3572059) B3572059
theorem B3175163 : Blo 2115435 3175163 := bstep (se 1 (by rfl) ⟨2381372, by rfl⟩ : syracuseStep 3175163 = 4762745) B4762745
theorem B2116775 : Blo 2115435 2116775 := bstep (se 1 (by rfl) ⟨1587581, by rfl⟩ : syracuseStep 2116775 = 3175163) B3175163
theorem B2381377 : Blo 2115435 2381377 := bbase (se 2 (by rfl) ⟨893016, by rfl⟩ : syracuseStep 2381377 = 1786033) (by norm_num)
theorem B3175169 : Blo 2115435 3175169 := bstep (se 2 (by rfl) ⟨1190688, by rfl⟩ : syracuseStep 3175169 = 2381377) B2381377
theorem B2116779 : Blo 2115435 2116779 := bstep (se 1 (by rfl) ⟨1587584, by rfl⟩ : syracuseStep 2116779 = 3175169) B3175169
theorem B5358109 : Blo 2115435 5358109 := bbase (se 3 (by rfl) ⟨1004645, by rfl⟩ : syracuseStep 5358109 = 2009291) (by norm_num)
theorem B7144145 : Blo 2115435 7144145 := bstep (se 2 (by rfl) ⟨2679054, by rfl⟩ : syracuseStep 7144145 = 5358109) B5358109
theorem B4762763 : Blo 2115435 4762763 := bstep (se 1 (by rfl) ⟨3572072, by rfl⟩ : syracuseStep 4762763 = 7144145) B7144145
theorem B3175175 : Blo 2115435 3175175 := bstep (se 1 (by rfl) ⟨2381381, by rfl⟩ : syracuseStep 3175175 = 4762763) B4762763
theorem B2116783 : Blo 2115435 2116783 := bstep (se 1 (by rfl) ⟨1587587, by rfl⟩ : syracuseStep 2116783 = 3175175) B3175175
theorem B3175181 : Blo 2115435 3175181 := bbase (se 3 (by rfl) ⟨595346, by rfl⟩ : syracuseStep 3175181 = 1190693) (by norm_num)
theorem B2116787 : Blo 2115435 2116787 := bstep (se 1 (by rfl) ⟨1587590, by rfl⟩ : syracuseStep 2116787 = 3175181) B3175181
theorem B4762781 : Blo 2115435 4762781 := bbase (se 3 (by rfl) ⟨893021, by rfl⟩ : syracuseStep 4762781 = 1786043) (by norm_num)
theorem B3175187 : Blo 2115435 3175187 := bstep (se 1 (by rfl) ⟨2381390, by rfl⟩ : syracuseStep 3175187 = 4762781) B4762781
theorem B2116791 : Blo 2115435 2116791 := bstep (se 1 (by rfl) ⟨1587593, by rfl⟩ : syracuseStep 2116791 = 3175187) B3175187
theorem B3572093 : Blo 2115435 3572093 := bbase (se 3 (by rfl) ⟨669767, by rfl⟩ : syracuseStep 3572093 = 1339535) (by norm_num)
theorem B2381395 : Blo 2115435 2381395 := bstep (se 1 (by rfl) ⟨1786046, by rfl⟩ : syracuseStep 2381395 = 3572093) B3572093
theorem B3175193 : Blo 2115435 3175193 := bstep (se 2 (by rfl) ⟨1190697, by rfl⟩ : syracuseStep 3175193 = 2381395) B2381395
theorem B2116795 : Blo 2115435 2116795 := bstep (se 1 (by rfl) ⟨1587596, by rfl⟩ : syracuseStep 2116795 = 3175193) B3175193
theorem B3620837 : Blo 2115435 3620837 := bbase (se 4 (by rfl) ⟨339453, by rfl⟩ : syracuseStep 3620837 = 678907) (by norm_num)
theorem B2413891 : Blo 2115435 2413891 := bstep (se 1 (by rfl) ⟨1810418, by rfl⟩ : syracuseStep 2413891 = 3620837) B3620837
theorem B12874085 : Blo 2115435 12874085 := bstep (se 4 (by rfl) ⟨1206945, by rfl⟩ : syracuseStep 12874085 = 2413891) B2413891
theorem B8582723 : Blo 2115435 8582723 := bstep (se 1 (by rfl) ⟨6437042, by rfl⟩ : syracuseStep 8582723 = 12874085) B12874085
theorem B5721815 : Blo 2115435 5721815 := bstep (se 1 (by rfl) ⟨4291361, by rfl⟩ : syracuseStep 5721815 = 8582723) B8582723
theorem B3814543 : Blo 2115435 3814543 := bstep (se 1 (by rfl) ⟨2860907, by rfl⟩ : syracuseStep 3814543 = 5721815) B5721815
theorem B5086057 : Blo 2115435 5086057 := bstep (se 2 (by rfl) ⟨1907271, by rfl⟩ : syracuseStep 5086057 = 3814543) B3814543
theorem B6781409 : Blo 2115435 6781409 := bstep (se 2 (by rfl) ⟨2543028, by rfl⟩ : syracuseStep 6781409 = 5086057) B5086057
theorem B4520939 : Blo 2115435 4520939 := bstep (se 1 (by rfl) ⟨3390704, by rfl⟩ : syracuseStep 4520939 = 6781409) B6781409
theorem B12055837 : Blo 2115435 12055837 := bstep (se 3 (by rfl) ⟨2260469, by rfl⟩ : syracuseStep 12055837 = 4520939) B4520939
theorem B16074449 : Blo 2115435 16074449 := bstep (se 2 (by rfl) ⟨6027918, by rfl⟩ : syracuseStep 16074449 = 12055837) B12055837
theorem B10716299 : Blo 2115435 10716299 := bstep (se 1 (by rfl) ⟨8037224, by rfl⟩ : syracuseStep 10716299 = 16074449) B16074449
theorem B7144199 : Blo 2115435 7144199 := bstep (se 1 (by rfl) ⟨5358149, by rfl⟩ : syracuseStep 7144199 = 10716299) B10716299
theorem B4762799 : Blo 2115435 4762799 := bstep (se 1 (by rfl) ⟨3572099, by rfl⟩ : syracuseStep 4762799 = 7144199) B7144199
theorem B3175199 : Blo 2115435 3175199 := bstep (se 1 (by rfl) ⟨2381399, by rfl⟩ : syracuseStep 3175199 = 4762799) B4762799
theorem B2116799 : Blo 2115435 2116799 := bstep (se 1 (by rfl) ⟨1587599, by rfl⟩ : syracuseStep 2116799 = 3175199) B3175199
theorem B3175205 : Blo 2115435 3175205 := bbase (se 4 (by rfl) ⟨297675, by rfl⟩ : syracuseStep 3175205 = 595351) (by norm_num)
theorem B2116803 : Blo 2115435 2116803 := bstep (se 1 (by rfl) ⟨1587602, by rfl⟩ : syracuseStep 2116803 = 3175205) B3175205
theorem B2679085 : Blo 2115435 2679085 := bbase (se 3 (by rfl) ⟨502328, by rfl⟩ : syracuseStep 2679085 = 1004657) (by norm_num)
theorem B3572113 : Blo 2115435 3572113 := bstep (se 2 (by rfl) ⟨1339542, by rfl⟩ : syracuseStep 3572113 = 2679085) B2679085
theorem B4762817 : Blo 2115435 4762817 := bstep (se 2 (by rfl) ⟨1786056, by rfl⟩ : syracuseStep 4762817 = 3572113) B3572113
theorem B3175211 : Blo 2115435 3175211 := bstep (se 1 (by rfl) ⟨2381408, by rfl⟩ : syracuseStep 3175211 = 4762817) B4762817
theorem B2116807 : Blo 2115435 2116807 := bstep (se 1 (by rfl) ⟨1587605, by rfl⟩ : syracuseStep 2116807 = 3175211) B3175211
theorem B2381413 : Blo 2115435 2381413 := bbase (se 4 (by rfl) ⟨223257, by rfl⟩ : syracuseStep 2381413 = 446515) (by norm_num)
theorem B3175217 : Blo 2115435 3175217 := bstep (se 2 (by rfl) ⟨1190706, by rfl⟩ : syracuseStep 3175217 = 2381413) B2381413
theorem B2116811 : Blo 2115435 2116811 := bstep (se 1 (by rfl) ⟨1587608, by rfl⟩ : syracuseStep 2116811 = 3175217) B3175217
theorem B3814573 : Blo 2115435 3814573 := bbase (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) (by norm_num)
theorem B5086097 : Blo 2115435 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B3390731 : Blo 2115435 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B2260487 : Blo 2115435 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B6027965 : Blo 2115435 6027965 := bstep (se 3 (by rfl) ⟨1130243, by rfl⟩ : syracuseStep 6027965 = 2260487) B2260487
theorem B4018643 : Blo 2115435 4018643 := bstep (se 1 (by rfl) ⟨3013982, by rfl⟩ : syracuseStep 4018643 = 6027965) B6027965
theorem B2679095 : Blo 2115435 2679095 := bstep (se 1 (by rfl) ⟨2009321, by rfl⟩ : syracuseStep 2679095 = 4018643) B4018643
theorem B7144253 : Blo 2115435 7144253 := bstep (se 3 (by rfl) ⟨1339547, by rfl⟩ : syracuseStep 7144253 = 2679095) B2679095
theorem B4762835 : Blo 2115435 4762835 := bstep (se 1 (by rfl) ⟨3572126, by rfl⟩ : syracuseStep 4762835 = 7144253) B7144253
theorem B3175223 : Blo 2115435 3175223 := bstep (se 1 (by rfl) ⟨2381417, by rfl⟩ : syracuseStep 3175223 = 4762835) B4762835
theorem B2116815 : Blo 2115435 2116815 := bstep (se 1 (by rfl) ⟨1587611, by rfl⟩ : syracuseStep 2116815 = 3175223) B3175223
theorem B3175229 : Blo 2115435 3175229 := bbase (se 3 (by rfl) ⟨595355, by rfl⟩ : syracuseStep 3175229 = 1190711) (by norm_num)
theorem B2116819 : Blo 2115435 2116819 := bstep (se 1 (by rfl) ⟨1587614, by rfl⟩ : syracuseStep 2116819 = 3175229) B3175229
theorem B4762853 : Blo 2115435 4762853 := bbase (se 4 (by rfl) ⟨446517, by rfl⟩ : syracuseStep 4762853 = 893035) (by norm_num)
theorem B3175235 : Blo 2115435 3175235 := bstep (se 1 (by rfl) ⟨2381426, by rfl⟩ : syracuseStep 3175235 = 4762853) B4762853
theorem B2116823 : Blo 2115435 2116823 := bstep (se 1 (by rfl) ⟨1587617, by rfl⟩ : syracuseStep 2116823 = 3175235) B3175235
theorem B5358221 : Blo 2115435 5358221 := bbase (se 3 (by rfl) ⟨1004666, by rfl⟩ : syracuseStep 5358221 = 2009333) (by norm_num)
theorem B3572147 : Blo 2115435 3572147 := bstep (se 1 (by rfl) ⟨2679110, by rfl⟩ : syracuseStep 3572147 = 5358221) B5358221
theorem B2381431 : Blo 2115435 2381431 := bstep (se 1 (by rfl) ⟨1786073, by rfl⟩ : syracuseStep 2381431 = 3572147) B3572147
theorem B3175241 : Blo 2115435 3175241 := bstep (se 2 (by rfl) ⟨1190715, by rfl⟩ : syracuseStep 3175241 = 2381431) B2381431
theorem B2116827 : Blo 2115435 2116827 := bstep (se 1 (by rfl) ⟨1587620, by rfl⟩ : syracuseStep 2116827 = 3175241) B3175241
theorem B3014005 : Blo 2115435 3014005 := bbase (se 5 (by rfl) ⟨141281, by rfl⟩ : syracuseStep 3014005 = 282563) (by norm_num)
theorem B4018673 : Blo 2115435 4018673 := bstep (se 2 (by rfl) ⟨1507002, by rfl⟩ : syracuseStep 4018673 = 3014005) B3014005
theorem B10716461 : Blo 2115435 10716461 := bstep (se 3 (by rfl) ⟨2009336, by rfl⟩ : syracuseStep 10716461 = 4018673) B4018673
theorem B7144307 : Blo 2115435 7144307 := bstep (se 1 (by rfl) ⟨5358230, by rfl⟩ : syracuseStep 7144307 = 10716461) B10716461
theorem B4762871 : Blo 2115435 4762871 := bstep (se 1 (by rfl) ⟨3572153, by rfl⟩ : syracuseStep 4762871 = 7144307) B7144307
theorem B3175247 : Blo 2115435 3175247 := bstep (se 1 (by rfl) ⟨2381435, by rfl⟩ : syracuseStep 3175247 = 4762871) B4762871
theorem B2116831 : Blo 2115435 2116831 := bstep (se 1 (by rfl) ⟨1587623, by rfl⟩ : syracuseStep 2116831 = 3175247) B3175247
theorem B3175253 : Blo 2115435 3175253 := bbase (se 9 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 3175253 = 18605) (by norm_num)
theorem B2116835 : Blo 2115435 2116835 := bstep (se 1 (by rfl) ⟨1587626, by rfl⟩ : syracuseStep 2116835 = 3175253) B3175253
theorem B2543077 : Blo 2115435 2543077 := bbase (se 4 (by rfl) ⟨238413, by rfl⟩ : syracuseStep 2543077 = 476827) (by norm_num)
theorem B3390769 : Blo 2115435 3390769 := bstep (se 2 (by rfl) ⟨1271538, by rfl⟩ : syracuseStep 3390769 = 2543077) B2543077
theorem B4521025 : Blo 2115435 4521025 := bstep (se 2 (by rfl) ⟨1695384, by rfl⟩ : syracuseStep 4521025 = 3390769) B3390769
theorem B6028033 : Blo 2115435 6028033 := bstep (se 2 (by rfl) ⟨2260512, by rfl⟩ : syracuseStep 6028033 = 4521025) B4521025
theorem B8037377 : Blo 2115435 8037377 := bstep (se 2 (by rfl) ⟨3014016, by rfl⟩ : syracuseStep 8037377 = 6028033) B6028033
theorem B5358251 : Blo 2115435 5358251 := bstep (se 1 (by rfl) ⟨4018688, by rfl⟩ : syracuseStep 5358251 = 8037377) B8037377
theorem B3572167 : Blo 2115435 3572167 := bstep (se 1 (by rfl) ⟨2679125, by rfl⟩ : syracuseStep 3572167 = 5358251) B5358251
theorem B4762889 : Blo 2115435 4762889 := bstep (se 2 (by rfl) ⟨1786083, by rfl⟩ : syracuseStep 4762889 = 3572167) B3572167
theorem B3175259 : Blo 2115435 3175259 := bstep (se 1 (by rfl) ⟨2381444, by rfl⟩ : syracuseStep 3175259 = 4762889) B4762889
theorem B2116839 : Blo 2115435 2116839 := bstep (se 1 (by rfl) ⟨1587629, by rfl⟩ : syracuseStep 2116839 = 3175259) B3175259
theorem B2381449 : Blo 2115435 2381449 := bbase (se 2 (by rfl) ⟨893043, by rfl⟩ : syracuseStep 2381449 = 1786087) (by norm_num)
theorem B3175265 : Blo 2115435 3175265 := bstep (se 2 (by rfl) ⟨1190724, by rfl⟩ : syracuseStep 3175265 = 2381449) B2381449
theorem B2116843 : Blo 2115435 2116843 := bstep (se 1 (by rfl) ⟨1587632, by rfl⟩ : syracuseStep 2116843 = 3175265) B3175265
theorem B26100053 : Blo 2115435 26100053 := bbase (se 10 (by rfl) ⟨38232, by rfl⟩ : syracuseStep 26100053 = 76465) (by norm_num)
theorem B17400035 : Blo 2115435 17400035 := bstep (se 1 (by rfl) ⟨13050026, by rfl⟩ : syracuseStep 17400035 = 26100053) B26100053
theorem B11600023 : Blo 2115435 11600023 := bstep (se 1 (by rfl) ⟨8700017, by rfl⟩ : syracuseStep 11600023 = 17400035) B17400035
theorem B15466697 : Blo 2115435 15466697 := bstep (se 2 (by rfl) ⟨5800011, by rfl⟩ : syracuseStep 15466697 = 11600023) B11600023
theorem B10311131 : Blo 2115435 10311131 := bstep (se 1 (by rfl) ⟨7733348, by rfl⟩ : syracuseStep 10311131 = 15466697) B15466697
theorem B6874087 : Blo 2115435 6874087 := bstep (se 1 (by rfl) ⟨5155565, by rfl⟩ : syracuseStep 6874087 = 10311131) B10311131
theorem B9165449 : Blo 2115435 9165449 := bstep (se 2 (by rfl) ⟨3437043, by rfl⟩ : syracuseStep 9165449 = 6874087) B6874087
theorem B6110299 : Blo 2115435 6110299 := bstep (se 1 (by rfl) ⟨4582724, by rfl⟩ : syracuseStep 6110299 = 9165449) B9165449
theorem B8147065 : Blo 2115435 8147065 := bstep (se 2 (by rfl) ⟨3055149, by rfl⟩ : syracuseStep 8147065 = 6110299) B6110299
theorem B10862753 : Blo 2115435 10862753 := bstep (se 2 (by rfl) ⟨4073532, by rfl⟩ : syracuseStep 10862753 = 8147065) B8147065
theorem B115869365 : Blo 2115435 115869365 := bstep (se 5 (by rfl) ⟨5431376, by rfl⟩ : syracuseStep 115869365 = 10862753) B10862753
theorem B77246243 : Blo 2115435 77246243 := bstep (se 1 (by rfl) ⟨57934682, by rfl⟩ : syracuseStep 77246243 = 115869365) B115869365
theorem B51497495 : Blo 2115435 51497495 := bstep (se 1 (by rfl) ⟨38623121, by rfl⟩ : syracuseStep 51497495 = 77246243) B77246243
theorem B34331663 : Blo 2115435 34331663 := bstep (se 1 (by rfl) ⟨25748747, by rfl⟩ : syracuseStep 34331663 = 51497495) B51497495
theorem B22887775 : Blo 2115435 22887775 := bstep (se 1 (by rfl) ⟨17165831, by rfl⟩ : syracuseStep 22887775 = 34331663) B34331663
theorem B30517033 : Blo 2115435 30517033 := bstep (se 2 (by rfl) ⟨11443887, by rfl⟩ : syracuseStep 30517033 = 22887775) B22887775
theorem B40689377 : Blo 2115435 40689377 := bstep (se 2 (by rfl) ⟨15258516, by rfl⟩ : syracuseStep 40689377 = 30517033) B30517033
theorem B27126251 : Blo 2115435 27126251 := bstep (se 1 (by rfl) ⟨20344688, by rfl⟩ : syracuseStep 27126251 = 40689377) B40689377
theorem B18084167 : Blo 2115435 18084167 := bstep (se 1 (by rfl) ⟨13563125, by rfl⟩ : syracuseStep 18084167 = 27126251) B27126251
theorem B12056111 : Blo 2115435 12056111 := bstep (se 1 (by rfl) ⟨9042083, by rfl⟩ : syracuseStep 12056111 = 18084167) B18084167
theorem B8037407 : Blo 2115435 8037407 := bstep (se 1 (by rfl) ⟨6028055, by rfl⟩ : syracuseStep 8037407 = 12056111) B12056111
theorem B5358271 : Blo 2115435 5358271 := bstep (se 1 (by rfl) ⟨4018703, by rfl⟩ : syracuseStep 5358271 = 8037407) B8037407
theorem B7144361 : Blo 2115435 7144361 := bstep (se 2 (by rfl) ⟨2679135, by rfl⟩ : syracuseStep 7144361 = 5358271) B5358271
theorem B4762907 : Blo 2115435 4762907 := bstep (se 1 (by rfl) ⟨3572180, by rfl⟩ : syracuseStep 4762907 = 7144361) B7144361
theorem B3175271 : Blo 2115435 3175271 := bstep (se 1 (by rfl) ⟨2381453, by rfl⟩ : syracuseStep 3175271 = 4762907) B4762907
theorem B2116847 : Blo 2115435 2116847 := bstep (se 1 (by rfl) ⟨1587635, by rfl⟩ : syracuseStep 2116847 = 3175271) B3175271
theorem B3175277 : Blo 2115435 3175277 := bbase (se 3 (by rfl) ⟨595364, by rfl⟩ : syracuseStep 3175277 = 1190729) (by norm_num)
theorem B2116851 : Blo 2115435 2116851 := bstep (se 1 (by rfl) ⟨1587638, by rfl⟩ : syracuseStep 2116851 = 3175277) B3175277
theorem B4762925 : Blo 2115435 4762925 := bbase (se 3 (by rfl) ⟨893048, by rfl⟩ : syracuseStep 4762925 = 1786097) (by norm_num)
theorem B3175283 : Blo 2115435 3175283 := bstep (se 1 (by rfl) ⟨2381462, by rfl⟩ : syracuseStep 3175283 = 4762925) B4762925
theorem B2116855 : Blo 2115435 2116855 := bstep (se 1 (by rfl) ⟨1587641, by rfl⟩ : syracuseStep 2116855 = 3175283) B3175283
theorem B10172405 : Blo 2115435 10172405 := bbase (se 5 (by rfl) ⟨476831, by rfl⟩ : syracuseStep 10172405 = 953663) (by norm_num)
theorem B6781603 : Blo 2115435 6781603 := bstep (se 1 (by rfl) ⟨5086202, by rfl⟩ : syracuseStep 6781603 = 10172405) B10172405
theorem B9042137 : Blo 2115435 9042137 := bstep (se 2 (by rfl) ⟨3390801, by rfl⟩ : syracuseStep 9042137 = 6781603) B6781603
theorem B6028091 : Blo 2115435 6028091 := bstep (se 1 (by rfl) ⟨4521068, by rfl⟩ : syracuseStep 6028091 = 9042137) B9042137
theorem B4018727 : Blo 2115435 4018727 := bstep (se 1 (by rfl) ⟨3014045, by rfl⟩ : syracuseStep 4018727 = 6028091) B6028091
theorem B2679151 : Blo 2115435 2679151 := bstep (se 1 (by rfl) ⟨2009363, by rfl⟩ : syracuseStep 2679151 = 4018727) B4018727
theorem B3572201 : Blo 2115435 3572201 := bstep (se 2 (by rfl) ⟨1339575, by rfl⟩ : syracuseStep 3572201 = 2679151) B2679151
theorem B2381467 : Blo 2115435 2381467 := bstep (se 1 (by rfl) ⟨1786100, by rfl⟩ : syracuseStep 2381467 = 3572201) B3572201
theorem B3175289 : Blo 2115435 3175289 := bstep (se 2 (by rfl) ⟨1190733, by rfl⟩ : syracuseStep 3175289 = 2381467) B2381467
theorem B2116859 : Blo 2115435 2116859 := bstep (se 1 (by rfl) ⟨1587644, by rfl⟩ : syracuseStep 2116859 = 3175289) B3175289
theorem B2715709 : Blo 2115435 2715709 := bbase (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) (by norm_num)
theorem B3620945 : Blo 2115435 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B9655853 : Blo 2115435 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B25748941 : Blo 2115435 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B34331921 : Blo 2115435 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B22887947 : Blo 2115435 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B15258631 : Blo 2115435 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B20344841 : Blo 2115435 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B13563227 : Blo 2115435 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B36168605 : Blo 2115435 36168605 := bstep (se 3 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 36168605 = 13563227) B13563227
theorem B24112403 : Blo 2115435 24112403 := bstep (se 1 (by rfl) ⟨18084302, by rfl⟩ : syracuseStep 24112403 = 36168605) B36168605
theorem B16074935 : Blo 2115435 16074935 := bstep (se 1 (by rfl) ⟨12056201, by rfl⟩ : syracuseStep 16074935 = 24112403) B24112403
theorem B10716623 : Blo 2115435 10716623 := bstep (se 1 (by rfl) ⟨8037467, by rfl⟩ : syracuseStep 10716623 = 16074935) B16074935
theorem B7144415 : Blo 2115435 7144415 := bstep (se 1 (by rfl) ⟨5358311, by rfl⟩ : syracuseStep 7144415 = 10716623) B10716623
theorem B4762943 : Blo 2115435 4762943 := bstep (se 1 (by rfl) ⟨3572207, by rfl⟩ : syracuseStep 4762943 = 7144415) B7144415
theorem B3175295 : Blo 2115435 3175295 := bstep (se 1 (by rfl) ⟨2381471, by rfl⟩ : syracuseStep 3175295 = 4762943) B4762943
theorem B2116863 : Blo 2115435 2116863 := bstep (se 1 (by rfl) ⟨1587647, by rfl⟩ : syracuseStep 2116863 = 3175295) B3175295
theorem B3175301 : Blo 2115435 3175301 := bbase (se 4 (by rfl) ⟨297684, by rfl⟩ : syracuseStep 3175301 = 595369) (by norm_num)
theorem B2116867 : Blo 2115435 2116867 := bstep (se 1 (by rfl) ⟨1587650, by rfl⟩ : syracuseStep 2116867 = 3175301) B3175301
theorem B3572221 : Blo 2115435 3572221 := bbase (se 3 (by rfl) ⟨669791, by rfl⟩ : syracuseStep 3572221 = 1339583) (by norm_num)
theorem B4762961 : Blo 2115435 4762961 := bstep (se 2 (by rfl) ⟨1786110, by rfl⟩ : syracuseStep 4762961 = 3572221) B3572221
theorem B3175307 : Blo 2115435 3175307 := bstep (se 1 (by rfl) ⟨2381480, by rfl⟩ : syracuseStep 3175307 = 4762961) B4762961
theorem B2116871 : Blo 2115435 2116871 := bstep (se 1 (by rfl) ⟨1587653, by rfl⟩ : syracuseStep 2116871 = 3175307) B3175307
theorem B2381485 : Blo 2115435 2381485 := bbase (se 3 (by rfl) ⟨446528, by rfl⟩ : syracuseStep 2381485 = 893057) (by norm_num)
theorem B3175313 : Blo 2115435 3175313 := bstep (se 2 (by rfl) ⟨1190742, by rfl⟩ : syracuseStep 3175313 = 2381485) B2381485
theorem B2116875 : Blo 2115435 2116875 := bstep (se 1 (by rfl) ⟨1587656, by rfl⟩ : syracuseStep 2116875 = 3175313) B3175313
theorem B7144469 : Blo 2115435 7144469 := bbase (se 6 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 7144469 = 334897) (by norm_num)
theorem B4762979 : Blo 2115435 4762979 := bstep (se 1 (by rfl) ⟨3572234, by rfl⟩ : syracuseStep 4762979 = 7144469) B7144469
theorem B3175319 : Blo 2115435 3175319 := bstep (se 1 (by rfl) ⟨2381489, by rfl⟩ : syracuseStep 3175319 = 4762979) B4762979
theorem B2116879 : Blo 2115435 2116879 := bstep (se 1 (by rfl) ⟨1587659, by rfl⟩ : syracuseStep 2116879 = 3175319) B3175319
theorem B3175325 : Blo 2115435 3175325 := bbase (se 3 (by rfl) ⟨595373, by rfl⟩ : syracuseStep 3175325 = 1190747) (by norm_num)
theorem B2116883 : Blo 2115435 2116883 := bstep (se 1 (by rfl) ⟨1587662, by rfl⟩ : syracuseStep 2116883 = 3175325) B3175325
theorem B4762997 : Blo 2115435 4762997 := bbase (se 5 (by rfl) ⟨223265, by rfl⟩ : syracuseStep 4762997 = 446531) (by norm_num)
theorem B3175331 : Blo 2115435 3175331 := bstep (se 1 (by rfl) ⟨2381498, by rfl⟩ : syracuseStep 3175331 = 4762997) B4762997
theorem B2116887 : Blo 2115435 2116887 := bstep (se 1 (by rfl) ⟨1587665, by rfl⟩ : syracuseStep 2116887 = 3175331) B3175331
theorem B3814709 : Blo 2115435 3814709 := bbase (se 5 (by rfl) ⟨178814, by rfl⟩ : syracuseStep 3814709 = 357629) (by norm_num)
theorem B10172557 : Blo 2115435 10172557 := bstep (se 3 (by rfl) ⟨1907354, by rfl⟩ : syracuseStep 10172557 = 3814709) B3814709
theorem B13563409 : Blo 2115435 13563409 := bstep (se 2 (by rfl) ⟨5086278, by rfl⟩ : syracuseStep 13563409 = 10172557) B10172557
theorem B18084545 : Blo 2115435 18084545 := bstep (se 2 (by rfl) ⟨6781704, by rfl⟩ : syracuseStep 18084545 = 13563409) B13563409
theorem B12056363 : Blo 2115435 12056363 := bstep (se 1 (by rfl) ⟨9042272, by rfl⟩ : syracuseStep 12056363 = 18084545) B18084545
theorem B8037575 : Blo 2115435 8037575 := bstep (se 1 (by rfl) ⟨6028181, by rfl⟩ : syracuseStep 8037575 = 12056363) B12056363
theorem B5358383 : Blo 2115435 5358383 := bstep (se 1 (by rfl) ⟨4018787, by rfl⟩ : syracuseStep 5358383 = 8037575) B8037575
theorem B3572255 : Blo 2115435 3572255 := bstep (se 1 (by rfl) ⟨2679191, by rfl⟩ : syracuseStep 3572255 = 5358383) B5358383
theorem B2381503 : Blo 2115435 2381503 := bstep (se 1 (by rfl) ⟨1786127, by rfl⟩ : syracuseStep 2381503 = 3572255) B3572255
theorem B3175337 : Blo 2115435 3175337 := bstep (se 2 (by rfl) ⟨1190751, by rfl⟩ : syracuseStep 3175337 = 2381503) B2381503
theorem B2116891 : Blo 2115435 2116891 := bstep (se 1 (by rfl) ⟨1587668, by rfl⟩ : syracuseStep 2116891 = 3175337) B3175337
theorem B8037589 : Blo 2115435 8037589 := bbase (se 7 (by rfl) ⟨94190, by rfl⟩ : syracuseStep 8037589 = 188381) (by norm_num)
theorem B10716785 : Blo 2115435 10716785 := bstep (se 2 (by rfl) ⟨4018794, by rfl⟩ : syracuseStep 10716785 = 8037589) B8037589
theorem B7144523 : Blo 2115435 7144523 := bstep (se 1 (by rfl) ⟨5358392, by rfl⟩ : syracuseStep 7144523 = 10716785) B10716785
theorem B4763015 : Blo 2115435 4763015 := bstep (se 1 (by rfl) ⟨3572261, by rfl⟩ : syracuseStep 4763015 = 7144523) B7144523
theorem B3175343 : Blo 2115435 3175343 := bstep (se 1 (by rfl) ⟨2381507, by rfl⟩ : syracuseStep 3175343 = 4763015) B4763015
theorem B2116895 : Blo 2115435 2116895 := bstep (se 1 (by rfl) ⟨1587671, by rfl⟩ : syracuseStep 2116895 = 3175343) B3175343
theorem B3175349 : Blo 2115435 3175349 := bbase (se 5 (by rfl) ⟨148844, by rfl⟩ : syracuseStep 3175349 = 297689) (by norm_num)
theorem B2116899 : Blo 2115435 2116899 := bstep (se 1 (by rfl) ⟨1587674, by rfl⟩ : syracuseStep 2116899 = 3175349) B3175349
theorem B5358413 : Blo 2115435 5358413 := bbase (se 3 (by rfl) ⟨1004702, by rfl⟩ : syracuseStep 5358413 = 2009405) (by norm_num)
theorem B3572275 : Blo 2115435 3572275 := bstep (se 1 (by rfl) ⟨2679206, by rfl⟩ : syracuseStep 3572275 = 5358413) B5358413
theorem B4763033 : Blo 2115435 4763033 := bstep (se 2 (by rfl) ⟨1786137, by rfl⟩ : syracuseStep 4763033 = 3572275) B3572275
theorem B3175355 : Blo 2115435 3175355 := bstep (se 1 (by rfl) ⟨2381516, by rfl⟩ : syracuseStep 3175355 = 4763033) B4763033
theorem B2116903 : Blo 2115435 2116903 := bstep (se 1 (by rfl) ⟨1587677, by rfl⟩ : syracuseStep 2116903 = 3175355) B3175355
theorem B2381521 : Blo 2115435 2381521 := bbase (se 2 (by rfl) ⟨893070, by rfl⟩ : syracuseStep 2381521 = 1786141) (by norm_num)
theorem B3175361 : Blo 2115435 3175361 := bstep (se 2 (by rfl) ⟨1190760, by rfl⟩ : syracuseStep 3175361 = 2381521) B2381521
theorem B2116907 : Blo 2115435 2116907 := bstep (se 1 (by rfl) ⟨1587680, by rfl⟩ : syracuseStep 2116907 = 3175361) B3175361
theorem B4291589 : Blo 2115435 4291589 := bbase (se 4 (by rfl) ⟨402336, by rfl⟩ : syracuseStep 4291589 = 804673) (by norm_num)
theorem B11444237 : Blo 2115435 11444237 := bstep (se 3 (by rfl) ⟨2145794, by rfl⟩ : syracuseStep 11444237 = 4291589) B4291589
theorem B7629491 : Blo 2115435 7629491 := bstep (se 1 (by rfl) ⟨5722118, by rfl⟩ : syracuseStep 7629491 = 11444237) B11444237
theorem B5086327 : Blo 2115435 5086327 := bstep (se 1 (by rfl) ⟨3814745, by rfl⟩ : syracuseStep 5086327 = 7629491) B7629491
theorem B6781769 : Blo 2115435 6781769 := bstep (se 2 (by rfl) ⟨2543163, by rfl⟩ : syracuseStep 6781769 = 5086327) B5086327
theorem B4521179 : Blo 2115435 4521179 := bstep (se 1 (by rfl) ⟨3390884, by rfl⟩ : syracuseStep 4521179 = 6781769) B6781769
theorem B3014119 : Blo 2115435 3014119 := bstep (se 1 (by rfl) ⟨2260589, by rfl⟩ : syracuseStep 3014119 = 4521179) B4521179
theorem B4018825 : Blo 2115435 4018825 := bstep (se 2 (by rfl) ⟨1507059, by rfl⟩ : syracuseStep 4018825 = 3014119) B3014119
theorem B5358433 : Blo 2115435 5358433 := bstep (se 2 (by rfl) ⟨2009412, by rfl⟩ : syracuseStep 5358433 = 4018825) B4018825
theorem B7144577 : Blo 2115435 7144577 := bstep (se 2 (by rfl) ⟨2679216, by rfl⟩ : syracuseStep 7144577 = 5358433) B5358433
theorem B4763051 : Blo 2115435 4763051 := bstep (se 1 (by rfl) ⟨3572288, by rfl⟩ : syracuseStep 4763051 = 7144577) B7144577
theorem B3175367 : Blo 2115435 3175367 := bstep (se 1 (by rfl) ⟨2381525, by rfl⟩ : syracuseStep 3175367 = 4763051) B4763051
theorem B2116911 : Blo 2115435 2116911 := bstep (se 1 (by rfl) ⟨1587683, by rfl⟩ : syracuseStep 2116911 = 3175367) B3175367
theorem B3175373 : Blo 2115435 3175373 := bbase (se 3 (by rfl) ⟨595382, by rfl⟩ : syracuseStep 3175373 = 1190765) (by norm_num)
theorem B2116915 : Blo 2115435 2116915 := bstep (se 1 (by rfl) ⟨1587686, by rfl⟩ : syracuseStep 2116915 = 3175373) B3175373
theorem B4763069 : Blo 2115435 4763069 := bbase (se 3 (by rfl) ⟨893075, by rfl⟩ : syracuseStep 4763069 = 1786151) (by norm_num)
theorem B3175379 : Blo 2115435 3175379 := bstep (se 1 (by rfl) ⟨2381534, by rfl⟩ : syracuseStep 3175379 = 4763069) B4763069
theorem B2116919 : Blo 2115435 2116919 := bstep (se 1 (by rfl) ⟨1587689, by rfl⟩ : syracuseStep 2116919 = 3175379) B3175379
theorem B3572309 : Blo 2115435 3572309 := bbase (se 8 (by rfl) ⟨20931, by rfl⟩ : syracuseStep 3572309 = 41863) (by norm_num)
theorem B2381539 : Blo 2115435 2381539 := bstep (se 1 (by rfl) ⟨1786154, by rfl⟩ : syracuseStep 2381539 = 3572309) B3572309
theorem B3175385 : Blo 2115435 3175385 := bstep (se 2 (by rfl) ⟨1190769, by rfl⟩ : syracuseStep 3175385 = 2381539) B2381539
theorem B2116923 : Blo 2115435 2116923 := bstep (se 1 (by rfl) ⟨1587692, by rfl⟩ : syracuseStep 2116923 = 3175385) B3175385
theorem B3866821 : Blo 2115435 3866821 := bbase (se 4 (by rfl) ⟨362514, by rfl⟩ : syracuseStep 3866821 = 725029) (by norm_num)
theorem B20623045 : Blo 2115435 20623045 := bstep (se 4 (by rfl) ⟨1933410, by rfl⟩ : syracuseStep 20623045 = 3866821) B3866821
theorem B27497393 : Blo 2115435 27497393 := bstep (se 2 (by rfl) ⟨10311522, by rfl⟩ : syracuseStep 27497393 = 20623045) B20623045
theorem B18331595 : Blo 2115435 18331595 := bstep (se 1 (by rfl) ⟨13748696, by rfl⟩ : syracuseStep 18331595 = 27497393) B27497393
theorem B12221063 : Blo 2115435 12221063 := bstep (se 1 (by rfl) ⟨9165797, by rfl⟩ : syracuseStep 12221063 = 18331595) B18331595
theorem B8147375 : Blo 2115435 8147375 := bstep (se 1 (by rfl) ⟨6110531, by rfl⟩ : syracuseStep 8147375 = 12221063) B12221063
theorem B5431583 : Blo 2115435 5431583 := bstep (se 1 (by rfl) ⟨4073687, by rfl⟩ : syracuseStep 5431583 = 8147375) B8147375
theorem B14484221 : Blo 2115435 14484221 := bstep (se 3 (by rfl) ⟨2715791, by rfl⟩ : syracuseStep 14484221 = 5431583) B5431583
theorem B9656147 : Blo 2115435 9656147 := bstep (se 1 (by rfl) ⟨7242110, by rfl⟩ : syracuseStep 9656147 = 14484221) B14484221
theorem B6437431 : Blo 2115435 6437431 := bstep (se 1 (by rfl) ⟨4828073, by rfl⟩ : syracuseStep 6437431 = 9656147) B9656147
theorem B8583241 : Blo 2115435 8583241 := bstep (se 2 (by rfl) ⟨3218715, by rfl⟩ : syracuseStep 8583241 = 6437431) B6437431
theorem B11444321 : Blo 2115435 11444321 := bstep (se 2 (by rfl) ⟨4291620, by rfl⟩ : syracuseStep 11444321 = 8583241) B8583241
theorem B7629547 : Blo 2115435 7629547 := bstep (se 1 (by rfl) ⟨5722160, by rfl⟩ : syracuseStep 7629547 = 11444321) B11444321
theorem B10172729 : Blo 2115435 10172729 := bstep (se 2 (by rfl) ⟨3814773, by rfl⟩ : syracuseStep 10172729 = 7629547) B7629547
theorem B6781819 : Blo 2115435 6781819 := bstep (se 1 (by rfl) ⟨5086364, by rfl⟩ : syracuseStep 6781819 = 10172729) B10172729
theorem B9042425 : Blo 2115435 9042425 := bstep (se 2 (by rfl) ⟨3390909, by rfl⟩ : syracuseStep 9042425 = 6781819) B6781819
theorem B6028283 : Blo 2115435 6028283 := bstep (se 1 (by rfl) ⟨4521212, by rfl⟩ : syracuseStep 6028283 = 9042425) B9042425
theorem B16075421 : Blo 2115435 16075421 := bstep (se 3 (by rfl) ⟨3014141, by rfl⟩ : syracuseStep 16075421 = 6028283) B6028283
theorem B10716947 : Blo 2115435 10716947 := bstep (se 1 (by rfl) ⟨8037710, by rfl⟩ : syracuseStep 10716947 = 16075421) B16075421
theorem B7144631 : Blo 2115435 7144631 := bstep (se 1 (by rfl) ⟨5358473, by rfl⟩ : syracuseStep 7144631 = 10716947) B10716947
theorem B4763087 : Blo 2115435 4763087 := bstep (se 1 (by rfl) ⟨3572315, by rfl⟩ : syracuseStep 4763087 = 7144631) B7144631
theorem B3175391 : Blo 2115435 3175391 := bstep (se 1 (by rfl) ⟨2381543, by rfl⟩ : syracuseStep 3175391 = 4763087) B4763087
theorem B2116927 : Blo 2115435 2116927 := bstep (se 1 (by rfl) ⟨1587695, by rfl⟩ : syracuseStep 2116927 = 3175391) B3175391
theorem B3175397 : Blo 2115435 3175397 := bbase (se 4 (by rfl) ⟨297693, by rfl⟩ : syracuseStep 3175397 = 595387) (by norm_num)
theorem B2116931 : Blo 2115435 2116931 := bstep (se 1 (by rfl) ⟨1587698, by rfl⟩ : syracuseStep 2116931 = 3175397) B3175397
theorem B3814789 : Blo 2115435 3814789 := bbase (se 4 (by rfl) ⟨357636, by rfl⟩ : syracuseStep 3814789 = 715273) (by norm_num)
theorem B5086385 : Blo 2115435 5086385 := bstep (se 2 (by rfl) ⟨1907394, by rfl⟩ : syracuseStep 5086385 = 3814789) B3814789
theorem B3390923 : Blo 2115435 3390923 := bstep (se 1 (by rfl) ⟨2543192, by rfl⟩ : syracuseStep 3390923 = 5086385) B5086385
theorem B9042461 : Blo 2115435 9042461 := bstep (se 3 (by rfl) ⟨1695461, by rfl⟩ : syracuseStep 9042461 = 3390923) B3390923
theorem B6028307 : Blo 2115435 6028307 := bstep (se 1 (by rfl) ⟨4521230, by rfl⟩ : syracuseStep 6028307 = 9042461) B9042461
theorem B4018871 : Blo 2115435 4018871 := bstep (se 1 (by rfl) ⟨3014153, by rfl⟩ : syracuseStep 4018871 = 6028307) B6028307
theorem B2679247 : Blo 2115435 2679247 := bstep (se 1 (by rfl) ⟨2009435, by rfl⟩ : syracuseStep 2679247 = 4018871) B4018871
theorem B3572329 : Blo 2115435 3572329 := bstep (se 2 (by rfl) ⟨1339623, by rfl⟩ : syracuseStep 3572329 = 2679247) B2679247
theorem B4763105 : Blo 2115435 4763105 := bstep (se 2 (by rfl) ⟨1786164, by rfl⟩ : syracuseStep 4763105 = 3572329) B3572329
theorem B3175403 : Blo 2115435 3175403 := bstep (se 1 (by rfl) ⟨2381552, by rfl⟩ : syracuseStep 3175403 = 4763105) B4763105
theorem B2116935 : Blo 2115435 2116935 := bstep (se 1 (by rfl) ⟨1587701, by rfl⟩ : syracuseStep 2116935 = 3175403) B3175403
theorem B2381557 : Blo 2115435 2381557 := bbase (se 5 (by rfl) ⟨111635, by rfl⟩ : syracuseStep 2381557 = 223271) (by norm_num)
theorem B3175409 : Blo 2115435 3175409 := bstep (se 2 (by rfl) ⟨1190778, by rfl⟩ : syracuseStep 3175409 = 2381557) B2381557
theorem B2116939 : Blo 2115435 2116939 := bstep (se 1 (by rfl) ⟨1587704, by rfl⟩ : syracuseStep 2116939 = 3175409) B3175409
theorem B2679257 : Blo 2115435 2679257 := bbase (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) (by norm_num)
theorem B7144685 : Blo 2115435 7144685 := bstep (se 3 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 7144685 = 2679257) B2679257
theorem B4763123 : Blo 2115435 4763123 := bstep (se 1 (by rfl) ⟨3572342, by rfl⟩ : syracuseStep 4763123 = 7144685) B7144685
theorem B3175415 : Blo 2115435 3175415 := bstep (se 1 (by rfl) ⟨2381561, by rfl⟩ : syracuseStep 3175415 = 4763123) B4763123
theorem B2116943 : Blo 2115435 2116943 := bstep (se 1 (by rfl) ⟨1587707, by rfl⟩ : syracuseStep 2116943 = 3175415) B3175415
theorem B3175421 : Blo 2115435 3175421 := bbase (se 3 (by rfl) ⟨595391, by rfl⟩ : syracuseStep 3175421 = 1190783) (by norm_num)
theorem B2116947 : Blo 2115435 2116947 := bstep (se 1 (by rfl) ⟨1587710, by rfl⟩ : syracuseStep 2116947 = 3175421) B3175421
theorem B4763141 : Blo 2115435 4763141 := bbase (se 4 (by rfl) ⟨446544, by rfl⟩ : syracuseStep 4763141 = 893089) (by norm_num)
theorem B3175427 : Blo 2115435 3175427 := bstep (se 1 (by rfl) ⟨2381570, by rfl⟩ : syracuseStep 3175427 = 4763141) B4763141
theorem B2116951 : Blo 2115435 2116951 := bstep (se 1 (by rfl) ⟨1587713, by rfl⟩ : syracuseStep 2116951 = 3175427) B3175427
theorem B4018909 : Blo 2115435 4018909 := bbase (se 3 (by rfl) ⟨753545, by rfl⟩ : syracuseStep 4018909 = 1507091) (by norm_num)
theorem B5358545 : Blo 2115435 5358545 := bstep (se 2 (by rfl) ⟨2009454, by rfl⟩ : syracuseStep 5358545 = 4018909) B4018909
theorem B3572363 : Blo 2115435 3572363 := bstep (se 1 (by rfl) ⟨2679272, by rfl⟩ : syracuseStep 3572363 = 5358545) B5358545
theorem B2381575 : Blo 2115435 2381575 := bstep (se 1 (by rfl) ⟨1786181, by rfl⟩ : syracuseStep 2381575 = 3572363) B3572363
theorem B3175433 : Blo 2115435 3175433 := bstep (se 2 (by rfl) ⟨1190787, by rfl⟩ : syracuseStep 3175433 = 2381575) B2381575
theorem B2116955 : Blo 2115435 2116955 := bstep (se 1 (by rfl) ⟨1587716, by rfl⟩ : syracuseStep 2116955 = 3175433) B3175433
theorem B10717109 : Blo 2115435 10717109 := bbase (se 5 (by rfl) ⟨502364, by rfl⟩ : syracuseStep 10717109 = 1004729) (by norm_num)
theorem B7144739 : Blo 2115435 7144739 := bstep (se 1 (by rfl) ⟨5358554, by rfl⟩ : syracuseStep 7144739 = 10717109) B10717109
theorem B4763159 : Blo 2115435 4763159 := bstep (se 1 (by rfl) ⟨3572369, by rfl⟩ : syracuseStep 4763159 = 7144739) B7144739
theorem B3175439 : Blo 2115435 3175439 := bstep (se 1 (by rfl) ⟨2381579, by rfl⟩ : syracuseStep 3175439 = 4763159) B4763159
theorem B2116959 : Blo 2115435 2116959 := bstep (se 1 (by rfl) ⟨1587719, by rfl⟩ : syracuseStep 2116959 = 3175439) B3175439
theorem B3175445 : Blo 2115435 3175445 := bbase (se 6 (by rfl) ⟨74424, by rfl⟩ : syracuseStep 3175445 = 148849) (by norm_num)
theorem B2116963 : Blo 2115435 2116963 := bstep (se 1 (by rfl) ⟨1587722, by rfl⟩ : syracuseStep 2116963 = 3175445) B3175445
theorem B3262693 : Blo 2115435 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B4350257 : Blo 2115435 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B2900171 : Blo 2115435 2900171 := bstep (se 1 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 2900171 = 4350257) B4350257
theorem B7733789 : Blo 2115435 7733789 := bstep (se 3 (by rfl) ⟨1450085, by rfl⟩ : syracuseStep 7733789 = 2900171) B2900171
theorem B5155859 : Blo 2115435 5155859 := bstep (se 1 (by rfl) ⟨3866894, by rfl⟩ : syracuseStep 5155859 = 7733789) B7733789
theorem B3437239 : Blo 2115435 3437239 := bstep (se 1 (by rfl) ⟨2577929, by rfl⟩ : syracuseStep 3437239 = 5155859) B5155859
theorem B4582985 : Blo 2115435 4582985 := bstep (se 2 (by rfl) ⟨1718619, by rfl⟩ : syracuseStep 4582985 = 3437239) B3437239
theorem B12221293 : Blo 2115435 12221293 := bstep (se 3 (by rfl) ⟨2291492, by rfl⟩ : syracuseStep 12221293 = 4582985) B4582985
theorem B16295057 : Blo 2115435 16295057 := bstep (se 2 (by rfl) ⟨6110646, by rfl⟩ : syracuseStep 16295057 = 12221293) B12221293
theorem B10863371 : Blo 2115435 10863371 := bstep (se 1 (by rfl) ⟨8147528, by rfl⟩ : syracuseStep 10863371 = 16295057) B16295057
theorem B7242247 : Blo 2115435 7242247 := bstep (se 1 (by rfl) ⟨5431685, by rfl⟩ : syracuseStep 7242247 = 10863371) B10863371
theorem B9656329 : Blo 2115435 9656329 := bstep (se 2 (by rfl) ⟨3621123, by rfl⟩ : syracuseStep 9656329 = 7242247) B7242247
theorem B12875105 : Blo 2115435 12875105 := bstep (se 2 (by rfl) ⟨4828164, by rfl⟩ : syracuseStep 12875105 = 9656329) B9656329
theorem B8583403 : Blo 2115435 8583403 := bstep (se 1 (by rfl) ⟨6437552, by rfl⟩ : syracuseStep 8583403 = 12875105) B12875105
theorem B11444537 : Blo 2115435 11444537 := bstep (se 2 (by rfl) ⟨4291701, by rfl⟩ : syracuseStep 11444537 = 8583403) B8583403
theorem B30518765 : Blo 2115435 30518765 := bstep (se 3 (by rfl) ⟨5722268, by rfl⟩ : syracuseStep 30518765 = 11444537) B11444537
theorem B20345843 : Blo 2115435 20345843 := bstep (se 1 (by rfl) ⟨15259382, by rfl⟩ : syracuseStep 20345843 = 30518765) B30518765
theorem B13563895 : Blo 2115435 13563895 := bstep (se 1 (by rfl) ⟨10172921, by rfl⟩ : syracuseStep 13563895 = 20345843) B20345843
theorem B18085193 : Blo 2115435 18085193 := bstep (se 2 (by rfl) ⟨6781947, by rfl⟩ : syracuseStep 18085193 = 13563895) B13563895
theorem B12056795 : Blo 2115435 12056795 := bstep (se 1 (by rfl) ⟨9042596, by rfl⟩ : syracuseStep 12056795 = 18085193) B18085193
theorem B8037863 : Blo 2115435 8037863 := bstep (se 1 (by rfl) ⟨6028397, by rfl⟩ : syracuseStep 8037863 = 12056795) B12056795
theorem B5358575 : Blo 2115435 5358575 := bstep (se 1 (by rfl) ⟨4018931, by rfl⟩ : syracuseStep 5358575 = 8037863) B8037863
theorem B3572383 : Blo 2115435 3572383 := bstep (se 1 (by rfl) ⟨2679287, by rfl⟩ : syracuseStep 3572383 = 5358575) B5358575
theorem B4763177 : Blo 2115435 4763177 := bstep (se 2 (by rfl) ⟨1786191, by rfl⟩ : syracuseStep 4763177 = 3572383) B3572383
theorem B3175451 : Blo 2115435 3175451 := bstep (se 1 (by rfl) ⟨2381588, by rfl⟩ : syracuseStep 3175451 = 4763177) B4763177
theorem B2116967 : Blo 2115435 2116967 := bstep (se 1 (by rfl) ⟨1587725, by rfl⟩ : syracuseStep 2116967 = 3175451) B3175451
theorem B2381593 : Blo 2115435 2381593 := bbase (se 2 (by rfl) ⟨893097, by rfl⟩ : syracuseStep 2381593 = 1786195) (by norm_num)
theorem B3175457 : Blo 2115435 3175457 := bstep (se 2 (by rfl) ⟨1190796, by rfl⟩ : syracuseStep 3175457 = 2381593) B2381593
theorem B2116971 : Blo 2115435 2116971 := bstep (se 1 (by rfl) ⟨1587728, by rfl⟩ : syracuseStep 2116971 = 3175457) B3175457
theorem B8037893 : Blo 2115435 8037893 := bbase (se 4 (by rfl) ⟨753552, by rfl⟩ : syracuseStep 8037893 = 1507105) (by norm_num)
theorem B5358595 : Blo 2115435 5358595 := bstep (se 1 (by rfl) ⟨4018946, by rfl⟩ : syracuseStep 5358595 = 8037893) B8037893
theorem B7144793 : Blo 2115435 7144793 := bstep (se 2 (by rfl) ⟨2679297, by rfl⟩ : syracuseStep 7144793 = 5358595) B5358595
theorem B4763195 : Blo 2115435 4763195 := bstep (se 1 (by rfl) ⟨3572396, by rfl⟩ : syracuseStep 4763195 = 7144793) B7144793
theorem B3175463 : Blo 2115435 3175463 := bstep (se 1 (by rfl) ⟨2381597, by rfl⟩ : syracuseStep 3175463 = 4763195) B4763195
theorem B2116975 : Blo 2115435 2116975 := bstep (se 1 (by rfl) ⟨1587731, by rfl⟩ : syracuseStep 2116975 = 3175463) B3175463
theorem B3175469 : Blo 2115435 3175469 := bbase (se 3 (by rfl) ⟨595400, by rfl⟩ : syracuseStep 3175469 = 1190801) (by norm_num)
theorem B2116979 : Blo 2115435 2116979 := bstep (se 1 (by rfl) ⟨1587734, by rfl⟩ : syracuseStep 2116979 = 3175469) B3175469
theorem B4763213 : Blo 2115435 4763213 := bbase (se 3 (by rfl) ⟨893102, by rfl⟩ : syracuseStep 4763213 = 1786205) (by norm_num)
theorem B3175475 : Blo 2115435 3175475 := bstep (se 1 (by rfl) ⟨2381606, by rfl⟩ : syracuseStep 3175475 = 4763213) B4763213
theorem B2116983 : Blo 2115435 2116983 := bstep (se 1 (by rfl) ⟨1587737, by rfl⟩ : syracuseStep 2116983 = 3175475) B3175475
theorem B2679313 : Blo 2115435 2679313 := bbase (se 2 (by rfl) ⟨1004742, by rfl⟩ : syracuseStep 2679313 = 2009485) (by norm_num)
theorem B3572417 : Blo 2115435 3572417 := bstep (se 2 (by rfl) ⟨1339656, by rfl⟩ : syracuseStep 3572417 = 2679313) B2679313
theorem B2381611 : Blo 2115435 2381611 := bstep (se 1 (by rfl) ⟨1786208, by rfl⟩ : syracuseStep 2381611 = 3572417) B3572417
theorem B3175481 : Blo 2115435 3175481 := bstep (se 2 (by rfl) ⟨1190805, by rfl⟩ : syracuseStep 3175481 = 2381611) B2381611
theorem B2116987 : Blo 2115435 2116987 := bstep (se 1 (by rfl) ⟨1587740, by rfl⟩ : syracuseStep 2116987 = 3175481) B3175481
theorem B4521349 : Blo 2115435 4521349 := bbase (se 4 (by rfl) ⟨423876, by rfl⟩ : syracuseStep 4521349 = 847753) (by norm_num)
theorem B24113861 : Blo 2115435 24113861 := bstep (se 4 (by rfl) ⟨2260674, by rfl⟩ : syracuseStep 24113861 = 4521349) B4521349
theorem B16075907 : Blo 2115435 16075907 := bstep (se 1 (by rfl) ⟨12056930, by rfl⟩ : syracuseStep 16075907 = 24113861) B24113861
theorem B10717271 : Blo 2115435 10717271 := bstep (se 1 (by rfl) ⟨8037953, by rfl⟩ : syracuseStep 10717271 = 16075907) B16075907
theorem B7144847 : Blo 2115435 7144847 := bstep (se 1 (by rfl) ⟨5358635, by rfl⟩ : syracuseStep 7144847 = 10717271) B10717271
theorem B4763231 : Blo 2115435 4763231 := bstep (se 1 (by rfl) ⟨3572423, by rfl⟩ : syracuseStep 4763231 = 7144847) B7144847
theorem B3175487 : Blo 2115435 3175487 := bstep (se 1 (by rfl) ⟨2381615, by rfl⟩ : syracuseStep 3175487 = 4763231) B4763231
theorem B2116991 : Blo 2115435 2116991 := bstep (se 1 (by rfl) ⟨1587743, by rfl⟩ : syracuseStep 2116991 = 3175487) B3175487
theorem B3175493 : Blo 2115435 3175493 := bbase (se 4 (by rfl) ⟨297702, by rfl⟩ : syracuseStep 3175493 = 595405) (by norm_num)
theorem B2116995 : Blo 2115435 2116995 := bstep (se 1 (by rfl) ⟨1587746, by rfl⟩ : syracuseStep 2116995 = 3175493) B3175493
theorem B3572437 : Blo 2115435 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B4763249 : Blo 2115435 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B3175499 : Blo 2115435 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B2116999 : Blo 2115435 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B2381629 : Blo 2115435 2381629 := bbase (se 3 (by rfl) ⟨446555, by rfl⟩ : syracuseStep 2381629 = 893111) (by norm_num)
theorem B3175505 : Blo 2115435 3175505 := bstep (se 2 (by rfl) ⟨1190814, by rfl⟩ : syracuseStep 3175505 = 2381629) B2381629
theorem B2117003 : Blo 2115435 2117003 := bstep (se 1 (by rfl) ⟨1587752, by rfl⟩ : syracuseStep 2117003 = 3175505) B3175505
theorem B7144901 : Blo 2115435 7144901 := bbase (se 4 (by rfl) ⟨669834, by rfl⟩ : syracuseStep 7144901 = 1339669) (by norm_num)
theorem B4763267 : Blo 2115435 4763267 := bstep (se 1 (by rfl) ⟨3572450, by rfl⟩ : syracuseStep 4763267 = 7144901) B7144901
theorem B3175511 : Blo 2115435 3175511 := bstep (se 1 (by rfl) ⟨2381633, by rfl⟩ : syracuseStep 3175511 = 4763267) B4763267
theorem B2117007 : Blo 2115435 2117007 := bstep (se 1 (by rfl) ⟨1587755, by rfl⟩ : syracuseStep 2117007 = 3175511) B3175511
theorem B3175517 : Blo 2115435 3175517 := bbase (se 3 (by rfl) ⟨595409, by rfl⟩ : syracuseStep 3175517 = 1190819) (by norm_num)
theorem B2117011 : Blo 2115435 2117011 := bstep (se 1 (by rfl) ⟨1587758, by rfl⟩ : syracuseStep 2117011 = 3175517) B3175517
theorem B4763285 : Blo 2115435 4763285 := bbase (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) (by norm_num)
theorem B3175523 : Blo 2115435 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B2117015 : Blo 2115435 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B2260705 : Blo 2115435 2260705 := bbase (se 2 (by rfl) ⟨847764, by rfl⟩ : syracuseStep 2260705 = 1695529) (by norm_num)
theorem B3014273 : Blo 2115435 3014273 := bstep (se 2 (by rfl) ⟨1130352, by rfl⟩ : syracuseStep 3014273 = 2260705) B2260705
theorem B8038061 : Blo 2115435 8038061 := bstep (se 3 (by rfl) ⟨1507136, by rfl⟩ : syracuseStep 8038061 = 3014273) B3014273
theorem B5358707 : Blo 2115435 5358707 := bstep (se 1 (by rfl) ⟨4019030, by rfl⟩ : syracuseStep 5358707 = 8038061) B8038061
theorem B3572471 : Blo 2115435 3572471 := bstep (se 1 (by rfl) ⟨2679353, by rfl⟩ : syracuseStep 3572471 = 5358707) B5358707
theorem B2381647 : Blo 2115435 2381647 := bstep (se 1 (by rfl) ⟨1786235, by rfl⟩ : syracuseStep 2381647 = 3572471) B3572471
theorem B3175529 : Blo 2115435 3175529 := bstep (se 2 (by rfl) ⟨1190823, by rfl⟩ : syracuseStep 3175529 = 2381647) B2381647
theorem B2117019 : Blo 2115435 2117019 := bstep (se 1 (by rfl) ⟨1587764, by rfl⟩ : syracuseStep 2117019 = 3175529) B3175529
theorem B7629893 : Blo 2115435 7629893 := bbase (se 4 (by rfl) ⟨715302, by rfl⟩ : syracuseStep 7629893 = 1430605) (by norm_num)
theorem B5086595 : Blo 2115435 5086595 := bstep (se 1 (by rfl) ⟨3814946, by rfl⟩ : syracuseStep 5086595 = 7629893) B7629893
theorem B13564253 : Blo 2115435 13564253 := bstep (se 3 (by rfl) ⟨2543297, by rfl⟩ : syracuseStep 13564253 = 5086595) B5086595
theorem B9042835 : Blo 2115435 9042835 := bstep (se 1 (by rfl) ⟨6782126, by rfl⟩ : syracuseStep 9042835 = 13564253) B13564253
theorem B12057113 : Blo 2115435 12057113 := bstep (se 2 (by rfl) ⟨4521417, by rfl⟩ : syracuseStep 12057113 = 9042835) B9042835
theorem B8038075 : Blo 2115435 8038075 := bstep (se 1 (by rfl) ⟨6028556, by rfl⟩ : syracuseStep 8038075 = 12057113) B12057113
theorem B10717433 : Blo 2115435 10717433 := bstep (se 2 (by rfl) ⟨4019037, by rfl⟩ : syracuseStep 10717433 = 8038075) B8038075
theorem B7144955 : Blo 2115435 7144955 := bstep (se 1 (by rfl) ⟨5358716, by rfl⟩ : syracuseStep 7144955 = 10717433) B10717433
theorem B4763303 : Blo 2115435 4763303 := bstep (se 1 (by rfl) ⟨3572477, by rfl⟩ : syracuseStep 4763303 = 7144955) B7144955
theorem B3175535 : Blo 2115435 3175535 := bstep (se 1 (by rfl) ⟨2381651, by rfl⟩ : syracuseStep 3175535 = 4763303) B4763303
theorem B2117023 : Blo 2115435 2117023 := bstep (se 1 (by rfl) ⟨1587767, by rfl⟩ : syracuseStep 2117023 = 3175535) B3175535
theorem B3175541 : Blo 2115435 3175541 := bbase (se 5 (by rfl) ⟨148853, by rfl⟩ : syracuseStep 3175541 = 297707) (by norm_num)
theorem B2117027 : Blo 2115435 2117027 := bstep (se 1 (by rfl) ⟨1587770, by rfl⟩ : syracuseStep 2117027 = 3175541) B3175541
theorem B4019053 : Blo 2115435 4019053 := bbase (se 3 (by rfl) ⟨753572, by rfl⟩ : syracuseStep 4019053 = 1507145) (by norm_num)
theorem B5358737 : Blo 2115435 5358737 := bstep (se 2 (by rfl) ⟨2009526, by rfl⟩ : syracuseStep 5358737 = 4019053) B4019053
theorem B3572491 : Blo 2115435 3572491 := bstep (se 1 (by rfl) ⟨2679368, by rfl⟩ : syracuseStep 3572491 = 5358737) B5358737
theorem B4763321 : Blo 2115435 4763321 := bstep (se 2 (by rfl) ⟨1786245, by rfl⟩ : syracuseStep 4763321 = 3572491) B3572491
theorem B3175547 : Blo 2115435 3175547 := bstep (se 1 (by rfl) ⟨2381660, by rfl⟩ : syracuseStep 3175547 = 4763321) B4763321
theorem B2117031 : Blo 2115435 2117031 := bstep (se 1 (by rfl) ⟨1587773, by rfl⟩ : syracuseStep 2117031 = 3175547) B3175547
theorem B2381665 : Blo 2115435 2381665 := bbase (se 2 (by rfl) ⟨893124, by rfl⟩ : syracuseStep 2381665 = 1786249) (by norm_num)
theorem B3175553 : Blo 2115435 3175553 := bstep (se 2 (by rfl) ⟨1190832, by rfl⟩ : syracuseStep 3175553 = 2381665) B2381665
theorem B2117035 : Blo 2115435 2117035 := bstep (se 1 (by rfl) ⟨1587776, by rfl⟩ : syracuseStep 2117035 = 3175553) B3175553
theorem B5358757 : Blo 2115435 5358757 := bbase (se 4 (by rfl) ⟨502383, by rfl⟩ : syracuseStep 5358757 = 1004767) (by norm_num)
theorem B7145009 : Blo 2115435 7145009 := bstep (se 2 (by rfl) ⟨2679378, by rfl⟩ : syracuseStep 7145009 = 5358757) B5358757
theorem B4763339 : Blo 2115435 4763339 := bstep (se 1 (by rfl) ⟨3572504, by rfl⟩ : syracuseStep 4763339 = 7145009) B7145009
theorem B3175559 : Blo 2115435 3175559 := bstep (se 1 (by rfl) ⟨2381669, by rfl⟩ : syracuseStep 3175559 = 4763339) B4763339
theorem B2117039 : Blo 2115435 2117039 := bstep (se 1 (by rfl) ⟨1587779, by rfl⟩ : syracuseStep 2117039 = 3175559) B3175559
theorem B3175565 : Blo 2115435 3175565 := bbase (se 3 (by rfl) ⟨595418, by rfl⟩ : syracuseStep 3175565 = 1190837) (by norm_num)
theorem B2117043 : Blo 2115435 2117043 := bstep (se 1 (by rfl) ⟨1587782, by rfl⟩ : syracuseStep 2117043 = 3175565) B3175565
theorem B4763357 : Blo 2115435 4763357 := bbase (se 3 (by rfl) ⟨893129, by rfl⟩ : syracuseStep 4763357 = 1786259) (by norm_num)
theorem B3175571 : Blo 2115435 3175571 := bstep (se 1 (by rfl) ⟨2381678, by rfl⟩ : syracuseStep 3175571 = 4763357) B4763357
theorem B2117047 : Blo 2115435 2117047 := bstep (se 1 (by rfl) ⟨1587785, by rfl⟩ : syracuseStep 2117047 = 3175571) B3175571
theorem B3572525 : Blo 2115435 3572525 := bbase (se 3 (by rfl) ⟨669848, by rfl⟩ : syracuseStep 3572525 = 1339697) (by norm_num)
theorem B2381683 : Blo 2115435 2381683 := bstep (se 1 (by rfl) ⟨1786262, by rfl⟩ : syracuseStep 2381683 = 3572525) B3572525
theorem B3175577 : Blo 2115435 3175577 := bstep (se 2 (by rfl) ⟨1190841, by rfl⟩ : syracuseStep 3175577 = 2381683) B2381683
theorem B2117051 : Blo 2115435 2117051 := bstep (se 1 (by rfl) ⟨1587788, by rfl⟩ : syracuseStep 2117051 = 3175577) B3175577
theorem B4073933 : Blo 2115435 4073933 := bbase (se 3 (by rfl) ⟨763862, by rfl⟩ : syracuseStep 4073933 = 1527725) (by norm_num)
theorem B2715955 : Blo 2115435 2715955 := bstep (se 1 (by rfl) ⟨2036966, by rfl⟩ : syracuseStep 2715955 = 4073933) B4073933
theorem B57940373 : Blo 2115435 57940373 := bstep (se 6 (by rfl) ⟨1357977, by rfl⟩ : syracuseStep 57940373 = 2715955) B2715955
theorem B38626915 : Blo 2115435 38626915 := bstep (se 1 (by rfl) ⟨28970186, by rfl⟩ : syracuseStep 38626915 = 57940373) B57940373
theorem B51502553 : Blo 2115435 51502553 := bstep (se 2 (by rfl) ⟨19313457, by rfl⟩ : syracuseStep 51502553 = 38626915) B38626915
theorem B34335035 : Blo 2115435 34335035 := bstep (se 1 (by rfl) ⟨25751276, by rfl⟩ : syracuseStep 34335035 = 51502553) B51502553
theorem B22890023 : Blo 2115435 22890023 := bstep (se 1 (by rfl) ⟨17167517, by rfl⟩ : syracuseStep 22890023 = 34335035) B34335035
theorem B15260015 : Blo 2115435 15260015 := bstep (se 1 (by rfl) ⟨11445011, by rfl⟩ : syracuseStep 15260015 = 22890023) B22890023
theorem B40693373 : Blo 2115435 40693373 := bstep (se 3 (by rfl) ⟨7630007, by rfl⟩ : syracuseStep 40693373 = 15260015) B15260015
theorem B27128915 : Blo 2115435 27128915 := bstep (se 1 (by rfl) ⟨20346686, by rfl⟩ : syracuseStep 27128915 = 40693373) B40693373
theorem B18085943 : Blo 2115435 18085943 := bstep (se 1 (by rfl) ⟨13564457, by rfl⟩ : syracuseStep 18085943 = 27128915) B27128915
theorem B12057295 : Blo 2115435 12057295 := bstep (se 1 (by rfl) ⟨9042971, by rfl⟩ : syracuseStep 12057295 = 18085943) B18085943
theorem B16076393 : Blo 2115435 16076393 := bstep (se 2 (by rfl) ⟨6028647, by rfl⟩ : syracuseStep 16076393 = 12057295) B12057295
theorem B10717595 : Blo 2115435 10717595 := bstep (se 1 (by rfl) ⟨8038196, by rfl⟩ : syracuseStep 10717595 = 16076393) B16076393
theorem B7145063 : Blo 2115435 7145063 := bstep (se 1 (by rfl) ⟨5358797, by rfl⟩ : syracuseStep 7145063 = 10717595) B10717595
theorem B4763375 : Blo 2115435 4763375 := bstep (se 1 (by rfl) ⟨3572531, by rfl⟩ : syracuseStep 4763375 = 7145063) B7145063
theorem B3175583 : Blo 2115435 3175583 := bstep (se 1 (by rfl) ⟨2381687, by rfl⟩ : syracuseStep 3175583 = 4763375) B4763375
theorem B2117055 : Blo 2115435 2117055 := bstep (se 1 (by rfl) ⟨1587791, by rfl⟩ : syracuseStep 2117055 = 3175583) B3175583
theorem B3175589 : Blo 2115435 3175589 := bbase (se 4 (by rfl) ⟨297711, by rfl⟩ : syracuseStep 3175589 = 595423) (by norm_num)
theorem B2117059 : Blo 2115435 2117059 := bstep (se 1 (by rfl) ⟨1587794, by rfl⟩ : syracuseStep 2117059 = 3175589) B3175589
theorem B2679409 : Blo 2115435 2679409 := bbase (se 2 (by rfl) ⟨1004778, by rfl⟩ : syracuseStep 2679409 = 2009557) (by norm_num)
theorem B3572545 : Blo 2115435 3572545 := bstep (se 2 (by rfl) ⟨1339704, by rfl⟩ : syracuseStep 3572545 = 2679409) B2679409
theorem B4763393 : Blo 2115435 4763393 := bstep (se 2 (by rfl) ⟨1786272, by rfl⟩ : syracuseStep 4763393 = 3572545) B3572545
theorem B3175595 : Blo 2115435 3175595 := bstep (se 1 (by rfl) ⟨2381696, by rfl⟩ : syracuseStep 3175595 = 4763393) B4763393
theorem B2117063 : Blo 2115435 2117063 := bstep (se 1 (by rfl) ⟨1587797, by rfl⟩ : syracuseStep 2117063 = 3175595) B3175595
theorem B2381701 : Blo 2115435 2381701 := bbase (se 4 (by rfl) ⟨223284, by rfl⟩ : syracuseStep 2381701 = 446569) (by norm_num)
theorem B3175601 : Blo 2115435 3175601 := bstep (se 2 (by rfl) ⟨1190850, by rfl⟩ : syracuseStep 3175601 = 2381701) B2381701
theorem B2117067 : Blo 2115435 2117067 := bstep (se 1 (by rfl) ⟨1587800, by rfl⟩ : syracuseStep 2117067 = 3175601) B3175601
theorem B3391141 : Blo 2115435 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B4521521 : Blo 2115435 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B3014347 : Blo 2115435 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B4019129 : Blo 2115435 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B2679419 : Blo 2115435 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B7145117 : Blo 2115435 7145117 := bstep (se 3 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 7145117 = 2679419) B2679419
theorem B4763411 : Blo 2115435 4763411 := bstep (se 1 (by rfl) ⟨3572558, by rfl⟩ : syracuseStep 4763411 = 7145117) B7145117
theorem B3175607 : Blo 2115435 3175607 := bstep (se 1 (by rfl) ⟨2381705, by rfl⟩ : syracuseStep 3175607 = 4763411) B4763411
theorem B2117071 : Blo 2115435 2117071 := bstep (se 1 (by rfl) ⟨1587803, by rfl⟩ : syracuseStep 2117071 = 3175607) B3175607
theorem B3175613 : Blo 2115435 3175613 := bbase (se 3 (by rfl) ⟨595427, by rfl⟩ : syracuseStep 3175613 = 1190855) (by norm_num)
theorem B2117075 : Blo 2115435 2117075 := bstep (se 1 (by rfl) ⟨1587806, by rfl⟩ : syracuseStep 2117075 = 3175613) B3175613
theorem B4763429 : Blo 2115435 4763429 := bbase (se 4 (by rfl) ⟨446571, by rfl⟩ : syracuseStep 4763429 = 893143) (by norm_num)
theorem B3175619 : Blo 2115435 3175619 := bstep (se 1 (by rfl) ⟨2381714, by rfl⟩ : syracuseStep 3175619 = 4763429) B4763429
theorem B2117079 : Blo 2115435 2117079 := bstep (se 1 (by rfl) ⟨1587809, by rfl⟩ : syracuseStep 2117079 = 3175619) B3175619
theorem B5358869 : Blo 2115435 5358869 := bbase (se 6 (by rfl) ⟨125598, by rfl⟩ : syracuseStep 5358869 = 251197) (by norm_num)
theorem B3572579 : Blo 2115435 3572579 := bstep (se 1 (by rfl) ⟨2679434, by rfl⟩ : syracuseStep 3572579 = 5358869) B5358869
theorem B2381719 : Blo 2115435 2381719 := bstep (se 1 (by rfl) ⟨1786289, by rfl⟩ : syracuseStep 2381719 = 3572579) B3572579
theorem B3175625 : Blo 2115435 3175625 := bstep (se 2 (by rfl) ⟨1190859, by rfl⟩ : syracuseStep 3175625 = 2381719) B2381719
theorem B2117083 : Blo 2115435 2117083 := bstep (se 1 (by rfl) ⟨1587812, by rfl⟩ : syracuseStep 2117083 = 3175625) B3175625
theorem B9043109 : Blo 2115435 9043109 := bbase (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) (by norm_num)
theorem B6028739 : Blo 2115435 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B4019159 : Blo 2115435 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B10717757 : Blo 2115435 10717757 := bstep (se 3 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 10717757 = 4019159) B4019159
theorem B7145171 : Blo 2115435 7145171 := bstep (se 1 (by rfl) ⟨5358878, by rfl⟩ : syracuseStep 7145171 = 10717757) B10717757
theorem B4763447 : Blo 2115435 4763447 := bstep (se 1 (by rfl) ⟨3572585, by rfl⟩ : syracuseStep 4763447 = 7145171) B7145171
theorem B3175631 : Blo 2115435 3175631 := bstep (se 1 (by rfl) ⟨2381723, by rfl⟩ : syracuseStep 3175631 = 4763447) B4763447
theorem B2117087 : Blo 2115435 2117087 := bstep (se 1 (by rfl) ⟨1587815, by rfl⟩ : syracuseStep 2117087 = 3175631) B3175631
theorem B3175637 : Blo 2115435 3175637 := bbase (se 7 (by rfl) ⟨37214, by rfl⟩ : syracuseStep 3175637 = 74429) (by norm_num)
theorem B2117091 : Blo 2115435 2117091 := bstep (se 1 (by rfl) ⟨1587818, by rfl⟩ : syracuseStep 2117091 = 3175637) B3175637
theorem B3014381 : Blo 2115435 3014381 := bbase (se 3 (by rfl) ⟨565196, by rfl⟩ : syracuseStep 3014381 = 1130393) (by norm_num)
theorem B8038349 : Blo 2115435 8038349 := bstep (se 3 (by rfl) ⟨1507190, by rfl⟩ : syracuseStep 8038349 = 3014381) B3014381
theorem B5358899 : Blo 2115435 5358899 := bstep (se 1 (by rfl) ⟨4019174, by rfl⟩ : syracuseStep 5358899 = 8038349) B8038349
theorem B3572599 : Blo 2115435 3572599 := bstep (se 1 (by rfl) ⟨2679449, by rfl⟩ : syracuseStep 3572599 = 5358899) B5358899
theorem B4763465 : Blo 2115435 4763465 := bstep (se 2 (by rfl) ⟨1786299, by rfl⟩ : syracuseStep 4763465 = 3572599) B3572599
theorem B3175643 : Blo 2115435 3175643 := bstep (se 1 (by rfl) ⟨2381732, by rfl⟩ : syracuseStep 3175643 = 4763465) B4763465
theorem B2117095 : Blo 2115435 2117095 := bstep (se 1 (by rfl) ⟨1587821, by rfl⟩ : syracuseStep 2117095 = 3175643) B3175643
theorem B2381737 : Blo 2115435 2381737 := bbase (se 2 (by rfl) ⟨893151, by rfl⟩ : syracuseStep 2381737 = 1786303) (by norm_num)
theorem B3175649 : Blo 2115435 3175649 := bstep (se 2 (by rfl) ⟨1190868, by rfl⟩ : syracuseStep 3175649 = 2381737) B2381737
theorem B2117099 : Blo 2115435 2117099 := bstep (se 1 (by rfl) ⟨1587824, by rfl⟩ : syracuseStep 2117099 = 3175649) B3175649
theorem B8148053 : Blo 2115435 8148053 := bbase (se 8 (by rfl) ⟨47742, by rfl⟩ : syracuseStep 8148053 = 95485) (by norm_num)
theorem B5432035 : Blo 2115435 5432035 := bstep (se 1 (by rfl) ⟨4074026, by rfl⟩ : syracuseStep 5432035 = 8148053) B8148053
theorem B7242713 : Blo 2115435 7242713 := bstep (se 2 (by rfl) ⟨2716017, by rfl⟩ : syracuseStep 7242713 = 5432035) B5432035
theorem B4828475 : Blo 2115435 4828475 := bstep (se 1 (by rfl) ⟨3621356, by rfl⟩ : syracuseStep 4828475 = 7242713) B7242713
theorem B3218983 : Blo 2115435 3218983 := bstep (se 1 (by rfl) ⟨2414237, by rfl⟩ : syracuseStep 3218983 = 4828475) B4828475
theorem B17167909 : Blo 2115435 17167909 := bstep (se 4 (by rfl) ⟨1609491, by rfl⟩ : syracuseStep 17167909 = 3218983) B3218983
theorem B22890545 : Blo 2115435 22890545 := bstep (se 2 (by rfl) ⟨8583954, by rfl⟩ : syracuseStep 22890545 = 17167909) B17167909
theorem B15260363 : Blo 2115435 15260363 := bstep (se 1 (by rfl) ⟨11445272, by rfl⟩ : syracuseStep 15260363 = 22890545) B22890545
theorem B10173575 : Blo 2115435 10173575 := bstep (se 1 (by rfl) ⟨7630181, by rfl⟩ : syracuseStep 10173575 = 15260363) B15260363
theorem B6782383 : Blo 2115435 6782383 := bstep (se 1 (by rfl) ⟨5086787, by rfl⟩ : syracuseStep 6782383 = 10173575) B10173575
theorem B9043177 : Blo 2115435 9043177 := bstep (se 2 (by rfl) ⟨3391191, by rfl⟩ : syracuseStep 9043177 = 6782383) B6782383
theorem B12057569 : Blo 2115435 12057569 := bstep (se 2 (by rfl) ⟨4521588, by rfl⟩ : syracuseStep 12057569 = 9043177) B9043177
theorem B8038379 : Blo 2115435 8038379 := bstep (se 1 (by rfl) ⟨6028784, by rfl⟩ : syracuseStep 8038379 = 12057569) B12057569
theorem B5358919 : Blo 2115435 5358919 := bstep (se 1 (by rfl) ⟨4019189, by rfl⟩ : syracuseStep 5358919 = 8038379) B8038379
theorem B7145225 : Blo 2115435 7145225 := bstep (se 2 (by rfl) ⟨2679459, by rfl⟩ : syracuseStep 7145225 = 5358919) B5358919
theorem B4763483 : Blo 2115435 4763483 := bstep (se 1 (by rfl) ⟨3572612, by rfl⟩ : syracuseStep 4763483 = 7145225) B7145225
theorem B3175655 : Blo 2115435 3175655 := bstep (se 1 (by rfl) ⟨2381741, by rfl⟩ : syracuseStep 3175655 = 4763483) B4763483
theorem B2117103 : Blo 2115435 2117103 := bstep (se 1 (by rfl) ⟨1587827, by rfl⟩ : syracuseStep 2117103 = 3175655) B3175655
theorem B3175661 : Blo 2115435 3175661 := bbase (se 3 (by rfl) ⟨595436, by rfl⟩ : syracuseStep 3175661 = 1190873) (by norm_num)
theorem B2117107 : Blo 2115435 2117107 := bstep (se 1 (by rfl) ⟨1587830, by rfl⟩ : syracuseStep 2117107 = 3175661) B3175661
theorem B4763501 : Blo 2115435 4763501 := bbase (se 3 (by rfl) ⟨893156, by rfl⟩ : syracuseStep 4763501 = 1786313) (by norm_num)
theorem B3175667 : Blo 2115435 3175667 := bstep (se 1 (by rfl) ⟨2381750, by rfl⟩ : syracuseStep 3175667 = 4763501) B4763501
theorem B2117111 : Blo 2115435 2117111 := bstep (se 1 (by rfl) ⟨1587833, by rfl⟩ : syracuseStep 2117111 = 3175667) B3175667
theorem B4019213 : Blo 2115435 4019213 := bbase (se 3 (by rfl) ⟨753602, by rfl⟩ : syracuseStep 4019213 = 1507205) (by norm_num)
theorem B2679475 : Blo 2115435 2679475 := bstep (se 1 (by rfl) ⟨2009606, by rfl⟩ : syracuseStep 2679475 = 4019213) B4019213
theorem B3572633 : Blo 2115435 3572633 := bstep (se 2 (by rfl) ⟨1339737, by rfl⟩ : syracuseStep 3572633 = 2679475) B2679475
theorem B2381755 : Blo 2115435 2381755 := bstep (se 1 (by rfl) ⟨1786316, by rfl⟩ : syracuseStep 2381755 = 3572633) B3572633
theorem B3175673 : Blo 2115435 3175673 := bstep (se 2 (by rfl) ⟨1190877, by rfl⟩ : syracuseStep 3175673 = 2381755) B2381755
theorem B2117115 : Blo 2115435 2117115 := bstep (se 1 (by rfl) ⟨1587836, by rfl⟩ : syracuseStep 2117115 = 3175673) B3175673
theorem B2291657 : Blo 2115435 2291657 := bbase (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) (by norm_num)
theorem B24444341 : Blo 2115435 24444341 := bstep (se 5 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 24444341 = 2291657) B2291657
theorem B16296227 : Blo 2115435 16296227 := bstep (se 1 (by rfl) ⟨12222170, by rfl⟩ : syracuseStep 16296227 = 24444341) B24444341
theorem B10864151 : Blo 2115435 10864151 := bstep (se 1 (by rfl) ⟨8148113, by rfl⟩ : syracuseStep 10864151 = 16296227) B16296227
theorem B7242767 : Blo 2115435 7242767 := bstep (se 1 (by rfl) ⟨5432075, by rfl⟩ : syracuseStep 7242767 = 10864151) B10864151
theorem B4828511 : Blo 2115435 4828511 := bstep (se 1 (by rfl) ⟨3621383, by rfl⟩ : syracuseStep 4828511 = 7242767) B7242767
theorem B12876029 : Blo 2115435 12876029 := bstep (se 3 (by rfl) ⟨2414255, by rfl⟩ : syracuseStep 12876029 = 4828511) B4828511
theorem B8584019 : Blo 2115435 8584019 := bstep (se 1 (by rfl) ⟨6438014, by rfl⟩ : syracuseStep 8584019 = 12876029) B12876029
theorem B5722679 : Blo 2115435 5722679 := bstep (se 1 (by rfl) ⟨4292009, by rfl⟩ : syracuseStep 5722679 = 8584019) B8584019
theorem B3815119 : Blo 2115435 3815119 := bstep (se 1 (by rfl) ⟨2861339, by rfl⟩ : syracuseStep 3815119 = 5722679) B5722679
theorem B20347301 : Blo 2115435 20347301 := bstep (se 4 (by rfl) ⟨1907559, by rfl⟩ : syracuseStep 20347301 = 3815119) B3815119
theorem B54259469 : Blo 2115435 54259469 := bstep (se 3 (by rfl) ⟨10173650, by rfl⟩ : syracuseStep 54259469 = 20347301) B20347301
theorem B36172979 : Blo 2115435 36172979 := bstep (se 1 (by rfl) ⟨27129734, by rfl⟩ : syracuseStep 36172979 = 54259469) B54259469
theorem B24115319 : Blo 2115435 24115319 := bstep (se 1 (by rfl) ⟨18086489, by rfl⟩ : syracuseStep 24115319 = 36172979) B36172979
theorem B16076879 : Blo 2115435 16076879 := bstep (se 1 (by rfl) ⟨12057659, by rfl⟩ : syracuseStep 16076879 = 24115319) B24115319
theorem B10717919 : Blo 2115435 10717919 := bstep (se 1 (by rfl) ⟨8038439, by rfl⟩ : syracuseStep 10717919 = 16076879) B16076879
theorem B7145279 : Blo 2115435 7145279 := bstep (se 1 (by rfl) ⟨5358959, by rfl⟩ : syracuseStep 7145279 = 10717919) B10717919
theorem B4763519 : Blo 2115435 4763519 := bstep (se 1 (by rfl) ⟨3572639, by rfl⟩ : syracuseStep 4763519 = 7145279) B7145279
theorem B3175679 : Blo 2115435 3175679 := bstep (se 1 (by rfl) ⟨2381759, by rfl⟩ : syracuseStep 3175679 = 4763519) B4763519
theorem B2117119 : Blo 2115435 2117119 := bstep (se 1 (by rfl) ⟨1587839, by rfl⟩ : syracuseStep 2117119 = 3175679) B3175679
theorem B3175685 : Blo 2115435 3175685 := bbase (se 4 (by rfl) ⟨297720, by rfl⟩ : syracuseStep 3175685 = 595441) (by norm_num)
theorem B2117123 : Blo 2115435 2117123 := bstep (se 1 (by rfl) ⟨1587842, by rfl⟩ : syracuseStep 2117123 = 3175685) B3175685
theorem B3572653 : Blo 2115435 3572653 := bbase (se 3 (by rfl) ⟨669872, by rfl⟩ : syracuseStep 3572653 = 1339745) (by norm_num)
theorem B4763537 : Blo 2115435 4763537 := bstep (se 2 (by rfl) ⟨1786326, by rfl⟩ : syracuseStep 4763537 = 3572653) B3572653
theorem B3175691 : Blo 2115435 3175691 := bstep (se 1 (by rfl) ⟨2381768, by rfl⟩ : syracuseStep 3175691 = 4763537) B4763537
theorem B2117127 : Blo 2115435 2117127 := bstep (se 1 (by rfl) ⟨1587845, by rfl⟩ : syracuseStep 2117127 = 3175691) B3175691
theorem B2381773 : Blo 2115435 2381773 := bbase (se 3 (by rfl) ⟨446582, by rfl⟩ : syracuseStep 2381773 = 893165) (by norm_num)
theorem B3175697 : Blo 2115435 3175697 := bstep (se 2 (by rfl) ⟨1190886, by rfl⟩ : syracuseStep 3175697 = 2381773) B2381773
theorem B2117131 : Blo 2115435 2117131 := bstep (se 1 (by rfl) ⟨1587848, by rfl⟩ : syracuseStep 2117131 = 3175697) B3175697
theorem B7145333 : Blo 2115435 7145333 := bbase (se 5 (by rfl) ⟨334937, by rfl⟩ : syracuseStep 7145333 = 669875) (by norm_num)
theorem B4763555 : Blo 2115435 4763555 := bstep (se 1 (by rfl) ⟨3572666, by rfl⟩ : syracuseStep 4763555 = 7145333) B7145333
theorem B3175703 : Blo 2115435 3175703 := bstep (se 1 (by rfl) ⟨2381777, by rfl⟩ : syracuseStep 3175703 = 4763555) B4763555
theorem B2117135 : Blo 2115435 2117135 := bstep (se 1 (by rfl) ⟨1587851, by rfl⟩ : syracuseStep 2117135 = 3175703) B3175703
theorem B3175709 : Blo 2115435 3175709 := bbase (se 3 (by rfl) ⟨595445, by rfl⟩ : syracuseStep 3175709 = 1190891) (by norm_num)
theorem B2117139 : Blo 2115435 2117139 := bstep (se 1 (by rfl) ⟨1587854, by rfl⟩ : syracuseStep 2117139 = 3175709) B3175709
theorem B4763573 : Blo 2115435 4763573 := bbase (se 5 (by rfl) ⟨223292, by rfl⟩ : syracuseStep 4763573 = 446585) (by norm_num)
theorem B3175715 : Blo 2115435 3175715 := bstep (se 1 (by rfl) ⟨2381786, by rfl⟩ : syracuseStep 3175715 = 4763573) B4763573
theorem B2117143 : Blo 2115435 2117143 := bstep (se 1 (by rfl) ⟨1587857, by rfl⟩ : syracuseStep 2117143 = 3175715) B3175715
theorem B5722757 : Blo 2115435 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B3815171 : Blo 2115435 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B2543447 : Blo 2115435 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B6782525 : Blo 2115435 6782525 := bstep (se 3 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 6782525 = 2543447) B2543447
theorem B4521683 : Blo 2115435 4521683 := bstep (se 1 (by rfl) ⟨3391262, by rfl⟩ : syracuseStep 4521683 = 6782525) B6782525
theorem B12057821 : Blo 2115435 12057821 := bstep (se 3 (by rfl) ⟨2260841, by rfl⟩ : syracuseStep 12057821 = 4521683) B4521683
theorem B8038547 : Blo 2115435 8038547 := bstep (se 1 (by rfl) ⟨6028910, by rfl⟩ : syracuseStep 8038547 = 12057821) B12057821
theorem B5359031 : Blo 2115435 5359031 := bstep (se 1 (by rfl) ⟨4019273, by rfl⟩ : syracuseStep 5359031 = 8038547) B8038547
theorem B3572687 : Blo 2115435 3572687 := bstep (se 1 (by rfl) ⟨2679515, by rfl⟩ : syracuseStep 3572687 = 5359031) B5359031
theorem B2381791 : Blo 2115435 2381791 := bstep (se 1 (by rfl) ⟨1786343, by rfl⟩ : syracuseStep 2381791 = 3572687) B3572687
theorem B3175721 : Blo 2115435 3175721 := bstep (se 2 (by rfl) ⟨1190895, by rfl⟩ : syracuseStep 3175721 = 2381791) B2381791
theorem B2117147 : Blo 2115435 2117147 := bstep (se 1 (by rfl) ⟨1587860, by rfl⟩ : syracuseStep 2117147 = 3175721) B3175721
theorem B27500309 : Blo 2115435 27500309 := bbase (se 6 (by rfl) ⟨644538, by rfl⟩ : syracuseStep 27500309 = 1289077) (by norm_num)
theorem B18333539 : Blo 2115435 18333539 := bstep (se 1 (by rfl) ⟨13750154, by rfl⟩ : syracuseStep 18333539 = 27500309) B27500309
theorem B12222359 : Blo 2115435 12222359 := bstep (se 1 (by rfl) ⟨9166769, by rfl⟩ : syracuseStep 12222359 = 18333539) B18333539
theorem B8148239 : Blo 2115435 8148239 := bstep (se 1 (by rfl) ⟨6111179, by rfl⟩ : syracuseStep 8148239 = 12222359) B12222359
theorem B5432159 : Blo 2115435 5432159 := bstep (se 1 (by rfl) ⟨4074119, by rfl⟩ : syracuseStep 5432159 = 8148239) B8148239
theorem B3621439 : Blo 2115435 3621439 := bstep (se 1 (by rfl) ⟨2716079, by rfl⟩ : syracuseStep 3621439 = 5432159) B5432159
theorem B4828585 : Blo 2115435 4828585 := bstep (se 2 (by rfl) ⟨1810719, by rfl⟩ : syracuseStep 4828585 = 3621439) B3621439
theorem B6438113 : Blo 2115435 6438113 := bstep (se 2 (by rfl) ⟨2414292, by rfl⟩ : syracuseStep 6438113 = 4828585) B4828585
theorem B4292075 : Blo 2115435 4292075 := bstep (se 1 (by rfl) ⟨3219056, by rfl⟩ : syracuseStep 4292075 = 6438113) B6438113
theorem B11445533 : Blo 2115435 11445533 := bstep (se 3 (by rfl) ⟨2146037, by rfl⟩ : syracuseStep 11445533 = 4292075) B4292075
theorem B7630355 : Blo 2115435 7630355 := bstep (se 1 (by rfl) ⟨5722766, by rfl⟩ : syracuseStep 7630355 = 11445533) B11445533
theorem B5086903 : Blo 2115435 5086903 := bstep (se 1 (by rfl) ⟨3815177, by rfl⟩ : syracuseStep 5086903 = 7630355) B7630355
theorem B6782537 : Blo 2115435 6782537 := bstep (se 2 (by rfl) ⟨2543451, by rfl⟩ : syracuseStep 6782537 = 5086903) B5086903
theorem B4521691 : Blo 2115435 4521691 := bstep (se 1 (by rfl) ⟨3391268, by rfl⟩ : syracuseStep 4521691 = 6782537) B6782537
theorem B6028921 : Blo 2115435 6028921 := bstep (se 2 (by rfl) ⟨2260845, by rfl⟩ : syracuseStep 6028921 = 4521691) B4521691
theorem B8038561 : Blo 2115435 8038561 := bstep (se 2 (by rfl) ⟨3014460, by rfl⟩ : syracuseStep 8038561 = 6028921) B6028921
theorem B10718081 : Blo 2115435 10718081 := bstep (se 2 (by rfl) ⟨4019280, by rfl⟩ : syracuseStep 10718081 = 8038561) B8038561
theorem B7145387 : Blo 2115435 7145387 := bstep (se 1 (by rfl) ⟨5359040, by rfl⟩ : syracuseStep 7145387 = 10718081) B10718081
theorem B4763591 : Blo 2115435 4763591 := bstep (se 1 (by rfl) ⟨3572693, by rfl⟩ : syracuseStep 4763591 = 7145387) B7145387
theorem B3175727 : Blo 2115435 3175727 := bstep (se 1 (by rfl) ⟨2381795, by rfl⟩ : syracuseStep 3175727 = 4763591) B4763591
theorem B2117151 : Blo 2115435 2117151 := bstep (se 1 (by rfl) ⟨1587863, by rfl⟩ : syracuseStep 2117151 = 3175727) B3175727
theorem B3175733 : Blo 2115435 3175733 := bbase (se 5 (by rfl) ⟨148862, by rfl⟩ : syracuseStep 3175733 = 297725) (by norm_num)
theorem B2117155 : Blo 2115435 2117155 := bstep (se 1 (by rfl) ⟨1587866, by rfl⟩ : syracuseStep 2117155 = 3175733) B3175733
theorem B5359061 : Blo 2115435 5359061 := bbase (se 7 (by rfl) ⟨62801, by rfl⟩ : syracuseStep 5359061 = 125603) (by norm_num)
theorem B3572707 : Blo 2115435 3572707 := bstep (se 1 (by rfl) ⟨2679530, by rfl⟩ : syracuseStep 3572707 = 5359061) B5359061
theorem B4763609 : Blo 2115435 4763609 := bstep (se 2 (by rfl) ⟨1786353, by rfl⟩ : syracuseStep 4763609 = 3572707) B3572707
theorem B3175739 : Blo 2115435 3175739 := bstep (se 1 (by rfl) ⟨2381804, by rfl⟩ : syracuseStep 3175739 = 4763609) B4763609
theorem B2117159 : Blo 2115435 2117159 := bstep (se 1 (by rfl) ⟨1587869, by rfl⟩ : syracuseStep 2117159 = 3175739) B3175739
theorem B2381809 : Blo 2115435 2381809 := bbase (se 2 (by rfl) ⟨893178, by rfl⟩ : syracuseStep 2381809 = 1786357) (by norm_num)
theorem B3175745 : Blo 2115435 3175745 := bstep (se 2 (by rfl) ⟨1190904, by rfl⟩ : syracuseStep 3175745 = 2381809) B2381809
theorem B2117163 : Blo 2115435 2117163 := bstep (se 1 (by rfl) ⟨1587872, by rfl⟩ : syracuseStep 2117163 = 3175745) B3175745
theorem B4828621 : Blo 2115435 4828621 := bbase (se 3 (by rfl) ⟨905366, by rfl⟩ : syracuseStep 4828621 = 1810733) (by norm_num)
theorem B6438161 : Blo 2115435 6438161 := bstep (se 2 (by rfl) ⟨2414310, by rfl⟩ : syracuseStep 6438161 = 4828621) B4828621
theorem B17168429 : Blo 2115435 17168429 := bstep (se 3 (by rfl) ⟨3219080, by rfl⟩ : syracuseStep 17168429 = 6438161) B6438161
theorem B11445619 : Blo 2115435 11445619 := bstep (se 1 (by rfl) ⟨8584214, by rfl⟩ : syracuseStep 11445619 = 17168429) B17168429
theorem B15260825 : Blo 2115435 15260825 := bstep (se 2 (by rfl) ⟨5722809, by rfl⟩ : syracuseStep 15260825 = 11445619) B11445619
theorem B10173883 : Blo 2115435 10173883 := bstep (se 1 (by rfl) ⟨7630412, by rfl⟩ : syracuseStep 10173883 = 15260825) B15260825
theorem B13565177 : Blo 2115435 13565177 := bstep (se 2 (by rfl) ⟨5086941, by rfl⟩ : syracuseStep 13565177 = 10173883) B10173883
theorem B9043451 : Blo 2115435 9043451 := bstep (se 1 (by rfl) ⟨6782588, by rfl⟩ : syracuseStep 9043451 = 13565177) B13565177
theorem B6028967 : Blo 2115435 6028967 := bstep (se 1 (by rfl) ⟨4521725, by rfl⟩ : syracuseStep 6028967 = 9043451) B9043451
theorem B4019311 : Blo 2115435 4019311 := bstep (se 1 (by rfl) ⟨3014483, by rfl⟩ : syracuseStep 4019311 = 6028967) B6028967
theorem B5359081 : Blo 2115435 5359081 := bstep (se 2 (by rfl) ⟨2009655, by rfl⟩ : syracuseStep 5359081 = 4019311) B4019311
theorem B7145441 : Blo 2115435 7145441 := bstep (se 2 (by rfl) ⟨2679540, by rfl⟩ : syracuseStep 7145441 = 5359081) B5359081
theorem B4763627 : Blo 2115435 4763627 := bstep (se 1 (by rfl) ⟨3572720, by rfl⟩ : syracuseStep 4763627 = 7145441) B7145441
theorem B3175751 : Blo 2115435 3175751 := bstep (se 1 (by rfl) ⟨2381813, by rfl⟩ : syracuseStep 3175751 = 4763627) B4763627
theorem B2117167 : Blo 2115435 2117167 := bstep (se 1 (by rfl) ⟨1587875, by rfl⟩ : syracuseStep 2117167 = 3175751) B3175751
theorem B3175757 : Blo 2115435 3175757 := bbase (se 3 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 3175757 = 1190909) (by norm_num)
theorem B2117171 : Blo 2115435 2117171 := bstep (se 1 (by rfl) ⟨1587878, by rfl⟩ : syracuseStep 2117171 = 3175757) B3175757
theorem B4763645 : Blo 2115435 4763645 := bbase (se 3 (by rfl) ⟨893183, by rfl⟩ : syracuseStep 4763645 = 1786367) (by norm_num)
theorem B3175763 : Blo 2115435 3175763 := bstep (se 1 (by rfl) ⟨2381822, by rfl⟩ : syracuseStep 3175763 = 4763645) B4763645
theorem B2117175 : Blo 2115435 2117175 := bstep (se 1 (by rfl) ⟨1587881, by rfl⟩ : syracuseStep 2117175 = 3175763) B3175763
theorem B3572741 : Blo 2115435 3572741 := bbase (se 4 (by rfl) ⟨334944, by rfl⟩ : syracuseStep 3572741 = 669889) (by norm_num)
theorem B2381827 : Blo 2115435 2381827 := bstep (se 1 (by rfl) ⟨1786370, by rfl⟩ : syracuseStep 2381827 = 3572741) B3572741
theorem B3175769 : Blo 2115435 3175769 := bstep (se 2 (by rfl) ⟨1190913, by rfl⟩ : syracuseStep 3175769 = 2381827) B2381827
theorem B2117179 : Blo 2115435 2117179 := bstep (se 1 (by rfl) ⟨1587884, by rfl⟩ : syracuseStep 2117179 = 3175769) B3175769
theorem B16077365 : Blo 2115435 16077365 := bbase (se 5 (by rfl) ⟨753626, by rfl⟩ : syracuseStep 16077365 = 1507253) (by norm_num)
theorem B10718243 : Blo 2115435 10718243 := bstep (se 1 (by rfl) ⟨8038682, by rfl⟩ : syracuseStep 10718243 = 16077365) B16077365
theorem B7145495 : Blo 2115435 7145495 := bstep (se 1 (by rfl) ⟨5359121, by rfl⟩ : syracuseStep 7145495 = 10718243) B10718243
theorem B4763663 : Blo 2115435 4763663 := bstep (se 1 (by rfl) ⟨3572747, by rfl⟩ : syracuseStep 4763663 = 7145495) B7145495
theorem B3175775 : Blo 2115435 3175775 := bstep (se 1 (by rfl) ⟨2381831, by rfl⟩ : syracuseStep 3175775 = 4763663) B4763663
theorem B2117183 : Blo 2115435 2117183 := bstep (se 1 (by rfl) ⟨1587887, by rfl⟩ : syracuseStep 2117183 = 3175775) B3175775
theorem B3175781 : Blo 2115435 3175781 := bbase (se 4 (by rfl) ⟨297729, by rfl⟩ : syracuseStep 3175781 = 595459) (by norm_num)
theorem B2117187 : Blo 2115435 2117187 := bstep (se 1 (by rfl) ⟨1587890, by rfl⟩ : syracuseStep 2117187 = 3175781) B3175781
theorem B4019357 : Blo 2115435 4019357 := bbase (se 3 (by rfl) ⟨753629, by rfl⟩ : syracuseStep 4019357 = 1507259) (by norm_num)
theorem B2679571 : Blo 2115435 2679571 := bstep (se 1 (by rfl) ⟨2009678, by rfl⟩ : syracuseStep 2679571 = 4019357) B4019357
theorem B3572761 : Blo 2115435 3572761 := bstep (se 2 (by rfl) ⟨1339785, by rfl⟩ : syracuseStep 3572761 = 2679571) B2679571
theorem B4763681 : Blo 2115435 4763681 := bstep (se 2 (by rfl) ⟨1786380, by rfl⟩ : syracuseStep 4763681 = 3572761) B3572761
theorem B3175787 : Blo 2115435 3175787 := bstep (se 1 (by rfl) ⟨2381840, by rfl⟩ : syracuseStep 3175787 = 4763681) B4763681
theorem B2117191 : Blo 2115435 2117191 := bstep (se 1 (by rfl) ⟨1587893, by rfl⟩ : syracuseStep 2117191 = 3175787) B3175787
theorem B2381845 : Blo 2115435 2381845 := bbase (se 6 (by rfl) ⟨55824, by rfl⟩ : syracuseStep 2381845 = 111649) (by norm_num)
theorem B3175793 : Blo 2115435 3175793 := bstep (se 2 (by rfl) ⟨1190922, by rfl⟩ : syracuseStep 3175793 = 2381845) B2381845
theorem B2117195 : Blo 2115435 2117195 := bstep (se 1 (by rfl) ⟨1587896, by rfl⟩ : syracuseStep 2117195 = 3175793) B3175793
theorem B2679581 : Blo 2115435 2679581 := bbase (se 3 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 2679581 = 1004843) (by norm_num)
theorem B7145549 : Blo 2115435 7145549 := bstep (se 3 (by rfl) ⟨1339790, by rfl⟩ : syracuseStep 7145549 = 2679581) B2679581
theorem B4763699 : Blo 2115435 4763699 := bstep (se 1 (by rfl) ⟨3572774, by rfl⟩ : syracuseStep 4763699 = 7145549) B7145549
theorem B3175799 : Blo 2115435 3175799 := bstep (se 1 (by rfl) ⟨2381849, by rfl⟩ : syracuseStep 3175799 = 4763699) B4763699
theorem B2117199 : Blo 2115435 2117199 := bstep (se 1 (by rfl) ⟨1587899, by rfl⟩ : syracuseStep 2117199 = 3175799) B3175799
theorem B3175805 : Blo 2115435 3175805 := bbase (se 3 (by rfl) ⟨595463, by rfl⟩ : syracuseStep 3175805 = 1190927) (by norm_num)
theorem B2117203 : Blo 2115435 2117203 := bstep (se 1 (by rfl) ⟨1587902, by rfl⟩ : syracuseStep 2117203 = 3175805) B3175805
theorem B4763717 : Blo 2115435 4763717 := bbase (se 4 (by rfl) ⟨446598, by rfl⟩ : syracuseStep 4763717 = 893197) (by norm_num)
theorem B3175811 : Blo 2115435 3175811 := bstep (se 1 (by rfl) ⟨2381858, by rfl⟩ : syracuseStep 3175811 = 4763717) B4763717
theorem B2117207 : Blo 2115435 2117207 := bstep (se 1 (by rfl) ⟨1587905, by rfl⟩ : syracuseStep 2117207 = 3175811) B3175811
theorem B6029093 : Blo 2115435 6029093 := bbase (se 4 (by rfl) ⟨565227, by rfl⟩ : syracuseStep 6029093 = 1130455) (by norm_num)
theorem B4019395 : Blo 2115435 4019395 := bstep (se 1 (by rfl) ⟨3014546, by rfl⟩ : syracuseStep 4019395 = 6029093) B6029093
theorem B5359193 : Blo 2115435 5359193 := bstep (se 2 (by rfl) ⟨2009697, by rfl⟩ : syracuseStep 5359193 = 4019395) B4019395
theorem B3572795 : Blo 2115435 3572795 := bstep (se 1 (by rfl) ⟨2679596, by rfl⟩ : syracuseStep 3572795 = 5359193) B5359193
theorem B2381863 : Blo 2115435 2381863 := bstep (se 1 (by rfl) ⟨1786397, by rfl⟩ : syracuseStep 2381863 = 3572795) B3572795
theorem B3175817 : Blo 2115435 3175817 := bstep (se 2 (by rfl) ⟨1190931, by rfl⟩ : syracuseStep 3175817 = 2381863) B2381863
theorem B2117211 : Blo 2115435 2117211 := bstep (se 1 (by rfl) ⟨1587908, by rfl⟩ : syracuseStep 2117211 = 3175817) B3175817
theorem B10718405 : Blo 2115435 10718405 := bbase (se 4 (by rfl) ⟨1004850, by rfl⟩ : syracuseStep 10718405 = 2009701) (by norm_num)
theorem B7145603 : Blo 2115435 7145603 := bstep (se 1 (by rfl) ⟨5359202, by rfl⟩ : syracuseStep 7145603 = 10718405) B10718405
theorem B4763735 : Blo 2115435 4763735 := bstep (se 1 (by rfl) ⟨3572801, by rfl⟩ : syracuseStep 4763735 = 7145603) B7145603
theorem B3175823 : Blo 2115435 3175823 := bstep (se 1 (by rfl) ⟨2381867, by rfl⟩ : syracuseStep 3175823 = 4763735) B4763735
theorem B2117215 : Blo 2115435 2117215 := bstep (se 1 (by rfl) ⟨1587911, by rfl⟩ : syracuseStep 2117215 = 3175823) B3175823
theorem B3175829 : Blo 2115435 3175829 := bbase (se 6 (by rfl) ⟨74433, by rfl⟩ : syracuseStep 3175829 = 148867) (by norm_num)
theorem B2117219 : Blo 2115435 2117219 := bstep (se 1 (by rfl) ⟨1587914, by rfl⟩ : syracuseStep 2117219 = 3175829) B3175829
theorem B4521845 : Blo 2115435 4521845 := bbase (se 5 (by rfl) ⟨211961, by rfl⟩ : syracuseStep 4521845 = 423923) (by norm_num)
theorem B12058253 : Blo 2115435 12058253 := bstep (se 3 (by rfl) ⟨2260922, by rfl⟩ : syracuseStep 12058253 = 4521845) B4521845
theorem B8038835 : Blo 2115435 8038835 := bstep (se 1 (by rfl) ⟨6029126, by rfl⟩ : syracuseStep 8038835 = 12058253) B12058253
theorem B5359223 : Blo 2115435 5359223 := bstep (se 1 (by rfl) ⟨4019417, by rfl⟩ : syracuseStep 5359223 = 8038835) B8038835
theorem B3572815 : Blo 2115435 3572815 := bstep (se 1 (by rfl) ⟨2679611, by rfl⟩ : syracuseStep 3572815 = 5359223) B5359223
theorem B4763753 : Blo 2115435 4763753 := bstep (se 2 (by rfl) ⟨1786407, by rfl⟩ : syracuseStep 4763753 = 3572815) B3572815
theorem B3175835 : Blo 2115435 3175835 := bstep (se 1 (by rfl) ⟨2381876, by rfl⟩ : syracuseStep 3175835 = 4763753) B4763753
theorem B2117223 : Blo 2115435 2117223 := bstep (se 1 (by rfl) ⟨1587917, by rfl⟩ : syracuseStep 2117223 = 3175835) B3175835
theorem B2381881 : Blo 2115435 2381881 := bbase (se 2 (by rfl) ⟨893205, by rfl⟩ : syracuseStep 2381881 = 1786411) (by norm_num)
theorem B3175841 : Blo 2115435 3175841 := bstep (se 2 (by rfl) ⟨1190940, by rfl⟩ : syracuseStep 3175841 = 2381881) B2381881
theorem B2117227 : Blo 2115435 2117227 := bstep (se 1 (by rfl) ⟨1587920, by rfl⟩ : syracuseStep 2117227 = 3175841) B3175841
theorem B3391397 : Blo 2115435 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B2260931 : Blo 2115435 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B6029149 : Blo 2115435 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B8038865 : Blo 2115435 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B5359243 : Blo 2115435 5359243 := bstep (se 1 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 5359243 = 8038865) B8038865
theorem B7145657 : Blo 2115435 7145657 := bstep (se 2 (by rfl) ⟨2679621, by rfl⟩ : syracuseStep 7145657 = 5359243) B5359243
theorem B4763771 : Blo 2115435 4763771 := bstep (se 1 (by rfl) ⟨3572828, by rfl⟩ : syracuseStep 4763771 = 7145657) B7145657
theorem B3175847 : Blo 2115435 3175847 := bstep (se 1 (by rfl) ⟨2381885, by rfl⟩ : syracuseStep 3175847 = 4763771) B4763771
theorem B2117231 : Blo 2115435 2117231 := bstep (se 1 (by rfl) ⟨1587923, by rfl⟩ : syracuseStep 2117231 = 3175847) B3175847
theorem B3175853 : Blo 2115435 3175853 := bbase (se 3 (by rfl) ⟨595472, by rfl⟩ : syracuseStep 3175853 = 1190945) (by norm_num)
theorem B2117235 : Blo 2115435 2117235 := bstep (se 1 (by rfl) ⟨1587926, by rfl⟩ : syracuseStep 2117235 = 3175853) B3175853
theorem B4763789 : Blo 2115435 4763789 := bbase (se 3 (by rfl) ⟨893210, by rfl⟩ : syracuseStep 4763789 = 1786421) (by norm_num)
theorem B3175859 : Blo 2115435 3175859 := bstep (se 1 (by rfl) ⟨2381894, by rfl⟩ : syracuseStep 3175859 = 4763789) B4763789
theorem B2117239 : Blo 2115435 2117239 := bstep (se 1 (by rfl) ⟨1587929, by rfl⟩ : syracuseStep 2117239 = 3175859) B3175859
theorem B2679637 : Blo 2115435 2679637 := bbase (se 9 (by rfl) ⟨7850, by rfl⟩ : syracuseStep 2679637 = 15701) (by norm_num)
theorem B3572849 : Blo 2115435 3572849 := bstep (se 2 (by rfl) ⟨1339818, by rfl⟩ : syracuseStep 3572849 = 2679637) B2679637
theorem B2381899 : Blo 2115435 2381899 := bstep (se 1 (by rfl) ⟨1786424, by rfl⟩ : syracuseStep 2381899 = 3572849) B3572849
theorem B3175865 : Blo 2115435 3175865 := bstep (se 2 (by rfl) ⟨1190949, by rfl⟩ : syracuseStep 3175865 = 2381899) B2381899
theorem B2117243 : Blo 2115435 2117243 := bstep (se 1 (by rfl) ⟨1587932, by rfl⟩ : syracuseStep 2117243 = 3175865) B3175865
theorem B10313077 : Blo 2115435 10313077 := bbase (se 5 (by rfl) ⟨483425, by rfl⟩ : syracuseStep 10313077 = 966851) (by norm_num)
theorem B13750769 : Blo 2115435 13750769 := bstep (se 2 (by rfl) ⟨5156538, by rfl⟩ : syracuseStep 13750769 = 10313077) B10313077
theorem B36668717 : Blo 2115435 36668717 := bstep (se 3 (by rfl) ⟨6875384, by rfl⟩ : syracuseStep 36668717 = 13750769) B13750769
theorem B24445811 : Blo 2115435 24445811 := bstep (se 1 (by rfl) ⟨18334358, by rfl⟩ : syracuseStep 24445811 = 36668717) B36668717
theorem B16297207 : Blo 2115435 16297207 := bstep (se 1 (by rfl) ⟨12222905, by rfl⟩ : syracuseStep 16297207 = 24445811) B24445811
theorem B86918437 : Blo 2115435 86918437 := bstep (se 4 (by rfl) ⟨8148603, by rfl⟩ : syracuseStep 86918437 = 16297207) B16297207
theorem B115891249 : Blo 2115435 115891249 := bstep (se 2 (by rfl) ⟨43459218, by rfl⟩ : syracuseStep 115891249 = 86918437) B86918437
theorem B154521665 : Blo 2115435 154521665 := bstep (se 2 (by rfl) ⟨57945624, by rfl⟩ : syracuseStep 154521665 = 115891249) B115891249
theorem B103014443 : Blo 2115435 103014443 := bstep (se 1 (by rfl) ⟨77260832, by rfl⟩ : syracuseStep 103014443 = 154521665) B154521665
theorem B68676295 : Blo 2115435 68676295 := bstep (se 1 (by rfl) ⟨51507221, by rfl⟩ : syracuseStep 68676295 = 103014443) B103014443
theorem B91568393 : Blo 2115435 91568393 := bstep (se 2 (by rfl) ⟨34338147, by rfl⟩ : syracuseStep 91568393 = 68676295) B68676295
theorem B61045595 : Blo 2115435 61045595 := bstep (se 1 (by rfl) ⟨45784196, by rfl⟩ : syracuseStep 61045595 = 91568393) B91568393
theorem B40697063 : Blo 2115435 40697063 := bstep (se 1 (by rfl) ⟨30522797, by rfl⟩ : syracuseStep 40697063 = 61045595) B61045595
theorem B27131375 : Blo 2115435 27131375 := bstep (se 1 (by rfl) ⟨20348531, by rfl⟩ : syracuseStep 27131375 = 40697063) B40697063
theorem B18087583 : Blo 2115435 18087583 := bstep (se 1 (by rfl) ⟨13565687, by rfl⟩ : syracuseStep 18087583 = 27131375) B27131375
theorem B24116777 : Blo 2115435 24116777 := bstep (se 2 (by rfl) ⟨9043791, by rfl⟩ : syracuseStep 24116777 = 18087583) B18087583
theorem B16077851 : Blo 2115435 16077851 := bstep (se 1 (by rfl) ⟨12058388, by rfl⟩ : syracuseStep 16077851 = 24116777) B24116777
theorem B10718567 : Blo 2115435 10718567 := bstep (se 1 (by rfl) ⟨8038925, by rfl⟩ : syracuseStep 10718567 = 16077851) B16077851
theorem B7145711 : Blo 2115435 7145711 := bstep (se 1 (by rfl) ⟨5359283, by rfl⟩ : syracuseStep 7145711 = 10718567) B10718567
theorem B4763807 : Blo 2115435 4763807 := bstep (se 1 (by rfl) ⟨3572855, by rfl⟩ : syracuseStep 4763807 = 7145711) B7145711
theorem B3175871 : Blo 2115435 3175871 := bstep (se 1 (by rfl) ⟨2381903, by rfl⟩ : syracuseStep 3175871 = 4763807) B4763807
theorem B2117247 : Blo 2115435 2117247 := bstep (se 1 (by rfl) ⟨1587935, by rfl⟩ : syracuseStep 2117247 = 3175871) B3175871
theorem B3175877 : Blo 2115435 3175877 := bbase (se 4 (by rfl) ⟨297738, by rfl⟩ : syracuseStep 3175877 = 595477) (by norm_num)
theorem B2117251 : Blo 2115435 2117251 := bstep (se 1 (by rfl) ⟨1587938, by rfl⟩ : syracuseStep 2117251 = 3175877) B3175877
theorem B3572869 : Blo 2115435 3572869 := bbase (se 4 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 3572869 = 669913) (by norm_num)
theorem B4763825 : Blo 2115435 4763825 := bstep (se 2 (by rfl) ⟨1786434, by rfl⟩ : syracuseStep 4763825 = 3572869) B3572869
theorem B3175883 : Blo 2115435 3175883 := bstep (se 1 (by rfl) ⟨2381912, by rfl⟩ : syracuseStep 3175883 = 4763825) B4763825
theorem B2117255 : Blo 2115435 2117255 := bstep (se 1 (by rfl) ⟨1587941, by rfl⟩ : syracuseStep 2117255 = 3175883) B3175883
theorem B2381917 : Blo 2115435 2381917 := bbase (se 3 (by rfl) ⟨446609, by rfl⟩ : syracuseStep 2381917 = 893219) (by norm_num)
theorem B3175889 : Blo 2115435 3175889 := bstep (se 2 (by rfl) ⟨1190958, by rfl⟩ : syracuseStep 3175889 = 2381917) B2381917
theorem B2117259 : Blo 2115435 2117259 := bstep (se 1 (by rfl) ⟨1587944, by rfl⟩ : syracuseStep 2117259 = 3175889) B3175889
theorem B7145765 : Blo 2115435 7145765 := bbase (se 4 (by rfl) ⟨669915, by rfl⟩ : syracuseStep 7145765 = 1339831) (by norm_num)
theorem B4763843 : Blo 2115435 4763843 := bstep (se 1 (by rfl) ⟨3572882, by rfl⟩ : syracuseStep 4763843 = 7145765) B7145765
theorem B3175895 : Blo 2115435 3175895 := bstep (se 1 (by rfl) ⟨2381921, by rfl⟩ : syracuseStep 3175895 = 4763843) B4763843
theorem B2117263 : Blo 2115435 2117263 := bstep (se 1 (by rfl) ⟨1587947, by rfl⟩ : syracuseStep 2117263 = 3175895) B3175895
theorem B3175901 : Blo 2115435 3175901 := bbase (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) (by norm_num)
theorem B2117267 : Blo 2115435 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B4763861 : Blo 2115435 4763861 := bbase (se 7 (by rfl) ⟨55826, by rfl⟩ : syracuseStep 4763861 = 111653) (by norm_num)
theorem B3175907 : Blo 2115435 3175907 := bstep (se 1 (by rfl) ⟨2381930, by rfl⟩ : syracuseStep 3175907 = 4763861) B4763861
theorem B2117271 : Blo 2115435 2117271 := bstep (se 1 (by rfl) ⟨1587953, by rfl⟩ : syracuseStep 2117271 = 3175907) B3175907
theorem B18334613 : Blo 2115435 18334613 := bbase (se 6 (by rfl) ⟨429717, by rfl⟩ : syracuseStep 18334613 = 859435) (by norm_num)
theorem B12223075 : Blo 2115435 12223075 := bstep (se 1 (by rfl) ⟨9167306, by rfl⟩ : syracuseStep 12223075 = 18334613) B18334613
theorem B16297433 : Blo 2115435 16297433 := bstep (se 2 (by rfl) ⟨6111537, by rfl⟩ : syracuseStep 16297433 = 12223075) B12223075
theorem B10864955 : Blo 2115435 10864955 := bstep (se 1 (by rfl) ⟨8148716, by rfl⟩ : syracuseStep 10864955 = 16297433) B16297433
theorem B7243303 : Blo 2115435 7243303 := bstep (se 1 (by rfl) ⟨5432477, by rfl⟩ : syracuseStep 7243303 = 10864955) B10864955
theorem B9657737 : Blo 2115435 9657737 := bstep (se 2 (by rfl) ⟨3621651, by rfl⟩ : syracuseStep 9657737 = 7243303) B7243303
theorem B6438491 : Blo 2115435 6438491 := bstep (se 1 (by rfl) ⟨4828868, by rfl⟩ : syracuseStep 6438491 = 9657737) B9657737
theorem B4292327 : Blo 2115435 4292327 := bstep (se 1 (by rfl) ⟨3219245, by rfl⟩ : syracuseStep 4292327 = 6438491) B6438491
theorem B2861551 : Blo 2115435 2861551 := bstep (se 1 (by rfl) ⟨2146163, by rfl⟩ : syracuseStep 2861551 = 4292327) B4292327
theorem B15261605 : Blo 2115435 15261605 := bstep (se 4 (by rfl) ⟨1430775, by rfl⟩ : syracuseStep 15261605 = 2861551) B2861551
theorem B10174403 : Blo 2115435 10174403 := bstep (se 1 (by rfl) ⟨7630802, by rfl⟩ : syracuseStep 10174403 = 15261605) B15261605
theorem B6782935 : Blo 2115435 6782935 := bstep (se 1 (by rfl) ⟨5087201, by rfl⟩ : syracuseStep 6782935 = 10174403) B10174403
theorem B9043913 : Blo 2115435 9043913 := bstep (se 2 (by rfl) ⟨3391467, by rfl⟩ : syracuseStep 9043913 = 6782935) B6782935
theorem B6029275 : Blo 2115435 6029275 := bstep (se 1 (by rfl) ⟨4521956, by rfl⟩ : syracuseStep 6029275 = 9043913) B9043913
theorem B8039033 : Blo 2115435 8039033 := bstep (se 2 (by rfl) ⟨3014637, by rfl⟩ : syracuseStep 8039033 = 6029275) B6029275
theorem B5359355 : Blo 2115435 5359355 := bstep (se 1 (by rfl) ⟨4019516, by rfl⟩ : syracuseStep 5359355 = 8039033) B8039033
theorem B3572903 : Blo 2115435 3572903 := bstep (se 1 (by rfl) ⟨2679677, by rfl⟩ : syracuseStep 3572903 = 5359355) B5359355
theorem B2381935 : Blo 2115435 2381935 := bstep (se 1 (by rfl) ⟨1786451, by rfl⟩ : syracuseStep 2381935 = 3572903) B3572903
theorem B3175913 : Blo 2115435 3175913 := bstep (se 2 (by rfl) ⟨1190967, by rfl⟩ : syracuseStep 3175913 = 2381935) B2381935
theorem B2117275 : Blo 2115435 2117275 := bstep (se 1 (by rfl) ⟨1587956, by rfl⟩ : syracuseStep 2117275 = 3175913) B3175913
theorem B2543605 : Blo 2115435 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B13565893 : Blo 2115435 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B18087857 : Blo 2115435 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B12058571 : Blo 2115435 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B8039047 : Blo 2115435 8039047 := bstep (se 1 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 8039047 = 12058571) B12058571
theorem B10718729 : Blo 2115435 10718729 := bstep (se 2 (by rfl) ⟨4019523, by rfl⟩ : syracuseStep 10718729 = 8039047) B8039047
theorem B7145819 : Blo 2115435 7145819 := bstep (se 1 (by rfl) ⟨5359364, by rfl⟩ : syracuseStep 7145819 = 10718729) B10718729
theorem B4763879 : Blo 2115435 4763879 := bstep (se 1 (by rfl) ⟨3572909, by rfl⟩ : syracuseStep 4763879 = 7145819) B7145819
theorem B3175919 : Blo 2115435 3175919 := bstep (se 1 (by rfl) ⟨2381939, by rfl⟩ : syracuseStep 3175919 = 4763879) B4763879
theorem B2117279 : Blo 2115435 2117279 := bstep (se 1 (by rfl) ⟨1587959, by rfl⟩ : syracuseStep 2117279 = 3175919) B3175919
theorem B3175925 : Blo 2115435 3175925 := bbase (se 5 (by rfl) ⟨148871, by rfl⟩ : syracuseStep 3175925 = 297743) (by norm_num)
theorem B2117283 : Blo 2115435 2117283 := bstep (se 1 (by rfl) ⟨1587962, by rfl⟩ : syracuseStep 2117283 = 3175925) B3175925
theorem B55754581 : Blo 2115435 55754581 := bbase (se 9 (by rfl) ⟨163343, by rfl⟩ : syracuseStep 55754581 = 326687) (by norm_num)
theorem B74339441 : Blo 2115435 74339441 := bstep (se 2 (by rfl) ⟨27877290, by rfl⟩ : syracuseStep 74339441 = 55754581) B55754581
theorem B49559627 : Blo 2115435 49559627 := bstep (se 1 (by rfl) ⟨37169720, by rfl⟩ : syracuseStep 49559627 = 74339441) B74339441
theorem B132159005 : Blo 2115435 132159005 := bstep (se 3 (by rfl) ⟨24779813, by rfl⟩ : syracuseStep 132159005 = 49559627) B49559627
theorem B88106003 : Blo 2115435 88106003 := bstep (se 1 (by rfl) ⟨66079502, by rfl⟩ : syracuseStep 88106003 = 132159005) B132159005
theorem B58737335 : Blo 2115435 58737335 := bstep (se 1 (by rfl) ⟨44053001, by rfl⟩ : syracuseStep 58737335 = 88106003) B88106003
theorem B626531573 : Blo 2115435 626531573 := bstep (se 5 (by rfl) ⟨29368667, by rfl⟩ : syracuseStep 626531573 = 58737335) B58737335
theorem B417687715 : Blo 2115435 417687715 := bstep (se 1 (by rfl) ⟨313265786, by rfl⟩ : syracuseStep 417687715 = 626531573) B626531573
theorem B556916953 : Blo 2115435 556916953 := bstep (se 2 (by rfl) ⟨208843857, by rfl⟩ : syracuseStep 556916953 = 417687715) B417687715
theorem B742555937 : Blo 2115435 742555937 := bstep (se 2 (by rfl) ⟨278458476, by rfl⟩ : syracuseStep 742555937 = 556916953) B556916953
theorem B495037291 : Blo 2115435 495037291 := bstep (se 1 (by rfl) ⟨371277968, by rfl⟩ : syracuseStep 495037291 = 742555937) B742555937
theorem B660049721 : Blo 2115435 660049721 := bstep (se 2 (by rfl) ⟨247518645, by rfl⟩ : syracuseStep 660049721 = 495037291) B495037291
theorem B440033147 : Blo 2115435 440033147 := bstep (se 1 (by rfl) ⟨330024860, by rfl⟩ : syracuseStep 440033147 = 660049721) B660049721
theorem B293355431 : Blo 2115435 293355431 := bstep (se 1 (by rfl) ⟨220016573, by rfl⟩ : syracuseStep 293355431 = 440033147) B440033147
theorem B195570287 : Blo 2115435 195570287 := bstep (se 1 (by rfl) ⟨146677715, by rfl⟩ : syracuseStep 195570287 = 293355431) B293355431
theorem B130380191 : Blo 2115435 130380191 := bstep (se 1 (by rfl) ⟨97785143, by rfl⟩ : syracuseStep 130380191 = 195570287) B195570287
theorem B86920127 : Blo 2115435 86920127 := bstep (se 1 (by rfl) ⟨65190095, by rfl⟩ : syracuseStep 86920127 = 130380191) B130380191
theorem B57946751 : Blo 2115435 57946751 := bstep (se 1 (by rfl) ⟨43460063, by rfl⟩ : syracuseStep 57946751 = 86920127) B86920127
theorem B38631167 : Blo 2115435 38631167 := bstep (se 1 (by rfl) ⟨28973375, by rfl⟩ : syracuseStep 38631167 = 57946751) B57946751
theorem B25754111 : Blo 2115435 25754111 := bstep (se 1 (by rfl) ⟨19315583, by rfl⟩ : syracuseStep 25754111 = 38631167) B38631167
theorem B17169407 : Blo 2115435 17169407 := bstep (se 1 (by rfl) ⟨12877055, by rfl⟩ : syracuseStep 17169407 = 25754111) B25754111
theorem B11446271 : Blo 2115435 11446271 := bstep (se 1 (by rfl) ⟨8584703, by rfl⟩ : syracuseStep 11446271 = 17169407) B17169407
theorem B7630847 : Blo 2115435 7630847 := bstep (se 1 (by rfl) ⟨5723135, by rfl⟩ : syracuseStep 7630847 = 11446271) B11446271
theorem B5087231 : Blo 2115435 5087231 := bstep (se 1 (by rfl) ⟨3815423, by rfl⟩ : syracuseStep 5087231 = 7630847) B7630847
theorem B3391487 : Blo 2115435 3391487 := bstep (se 1 (by rfl) ⟨2543615, by rfl⟩ : syracuseStep 3391487 = 5087231) B5087231
theorem B2260991 : Blo 2115435 2260991 := bstep (se 1 (by rfl) ⟨1695743, by rfl⟩ : syracuseStep 2260991 = 3391487) B3391487
theorem B6029309 : Blo 2115435 6029309 := bstep (se 3 (by rfl) ⟨1130495, by rfl⟩ : syracuseStep 6029309 = 2260991) B2260991
theorem B4019539 : Blo 2115435 4019539 := bstep (se 1 (by rfl) ⟨3014654, by rfl⟩ : syracuseStep 4019539 = 6029309) B6029309
theorem B5359385 : Blo 2115435 5359385 := bstep (se 2 (by rfl) ⟨2009769, by rfl⟩ : syracuseStep 5359385 = 4019539) B4019539
theorem B3572923 : Blo 2115435 3572923 := bstep (se 1 (by rfl) ⟨2679692, by rfl⟩ : syracuseStep 3572923 = 5359385) B5359385
theorem B4763897 : Blo 2115435 4763897 := bstep (se 2 (by rfl) ⟨1786461, by rfl⟩ : syracuseStep 4763897 = 3572923) B3572923
theorem B3175931 : Blo 2115435 3175931 := bstep (se 1 (by rfl) ⟨2381948, by rfl⟩ : syracuseStep 3175931 = 4763897) B4763897
theorem B2117287 : Blo 2115435 2117287 := bstep (se 1 (by rfl) ⟨1587965, by rfl⟩ : syracuseStep 2117287 = 3175931) B3175931
theorem B2381953 : Blo 2115435 2381953 := bbase (se 2 (by rfl) ⟨893232, by rfl⟩ : syracuseStep 2381953 = 1786465) (by norm_num)
theorem B3175937 : Blo 2115435 3175937 := bstep (se 2 (by rfl) ⟨1190976, by rfl⟩ : syracuseStep 3175937 = 2381953) B2381953
theorem B2117291 : Blo 2115435 2117291 := bstep (se 1 (by rfl) ⟨1587968, by rfl⟩ : syracuseStep 2117291 = 3175937) B3175937
theorem B5359405 : Blo 2115435 5359405 := bbase (se 3 (by rfl) ⟨1004888, by rfl⟩ : syracuseStep 5359405 = 2009777) (by norm_num)
theorem B7145873 : Blo 2115435 7145873 := bstep (se 2 (by rfl) ⟨2679702, by rfl⟩ : syracuseStep 7145873 = 5359405) B5359405
theorem B4763915 : Blo 2115435 4763915 := bstep (se 1 (by rfl) ⟨3572936, by rfl⟩ : syracuseStep 4763915 = 7145873) B7145873
theorem B3175943 : Blo 2115435 3175943 := bstep (se 1 (by rfl) ⟨2381957, by rfl⟩ : syracuseStep 3175943 = 4763915) B4763915
theorem B2117295 : Blo 2115435 2117295 := bstep (se 1 (by rfl) ⟨1587971, by rfl⟩ : syracuseStep 2117295 = 3175943) B3175943
theorem B3175949 : Blo 2115435 3175949 := bbase (se 3 (by rfl) ⟨595490, by rfl⟩ : syracuseStep 3175949 = 1190981) (by norm_num)
theorem B2117299 : Blo 2115435 2117299 := bstep (se 1 (by rfl) ⟨1587974, by rfl⟩ : syracuseStep 2117299 = 3175949) B3175949
theorem B4763933 : Blo 2115435 4763933 := bbase (se 3 (by rfl) ⟨893237, by rfl⟩ : syracuseStep 4763933 = 1786475) (by norm_num)
theorem B3175955 : Blo 2115435 3175955 := bstep (se 1 (by rfl) ⟨2381966, by rfl⟩ : syracuseStep 3175955 = 4763933) B4763933
theorem B2117303 : Blo 2115435 2117303 := bstep (se 1 (by rfl) ⟨1587977, by rfl⟩ : syracuseStep 2117303 = 3175955) B3175955
theorem B3572957 : Blo 2115435 3572957 := bbase (se 3 (by rfl) ⟨669929, by rfl⟩ : syracuseStep 3572957 = 1339859) (by norm_num)
theorem B2381971 : Blo 2115435 2381971 := bstep (se 1 (by rfl) ⟨1786478, by rfl⟩ : syracuseStep 2381971 = 3572957) B3572957
theorem B3175961 : Blo 2115435 3175961 := bstep (se 2 (by rfl) ⟨1190985, by rfl⟩ : syracuseStep 3175961 = 2381971) B2381971
theorem B2117307 : Blo 2115435 2117307 := bstep (se 1 (by rfl) ⟨1587980, by rfl⟩ : syracuseStep 2117307 = 3175961) B3175961
theorem B8148853 : Blo 2115435 8148853 := bbase (se 5 (by rfl) ⟨381977, by rfl⟩ : syracuseStep 8148853 = 763955) (by norm_num)
theorem B10865137 : Blo 2115435 10865137 := bstep (se 2 (by rfl) ⟨4074426, by rfl⟩ : syracuseStep 10865137 = 8148853) B8148853
theorem B14486849 : Blo 2115435 14486849 := bstep (se 2 (by rfl) ⟨5432568, by rfl⟩ : syracuseStep 14486849 = 10865137) B10865137
theorem B9657899 : Blo 2115435 9657899 := bstep (se 1 (by rfl) ⟨7243424, by rfl⟩ : syracuseStep 9657899 = 14486849) B14486849
theorem B6438599 : Blo 2115435 6438599 := bstep (se 1 (by rfl) ⟨4828949, by rfl⟩ : syracuseStep 6438599 = 9657899) B9657899
theorem B4292399 : Blo 2115435 4292399 := bstep (se 1 (by rfl) ⟨3219299, by rfl⟩ : syracuseStep 4292399 = 6438599) B6438599
theorem B11446397 : Blo 2115435 11446397 := bstep (se 3 (by rfl) ⟨2146199, by rfl⟩ : syracuseStep 11446397 = 4292399) B4292399
theorem B7630931 : Blo 2115435 7630931 := bstep (se 1 (by rfl) ⟨5723198, by rfl⟩ : syracuseStep 7630931 = 11446397) B11446397
theorem B5087287 : Blo 2115435 5087287 := bstep (se 1 (by rfl) ⟨3815465, by rfl⟩ : syracuseStep 5087287 = 7630931) B7630931
theorem B6783049 : Blo 2115435 6783049 := bstep (se 2 (by rfl) ⟨2543643, by rfl⟩ : syracuseStep 6783049 = 5087287) B5087287
theorem B9044065 : Blo 2115435 9044065 := bstep (se 2 (by rfl) ⟨3391524, by rfl⟩ : syracuseStep 9044065 = 6783049) B6783049
theorem B12058753 : Blo 2115435 12058753 := bstep (se 2 (by rfl) ⟨4522032, by rfl⟩ : syracuseStep 12058753 = 9044065) B9044065
theorem B16078337 : Blo 2115435 16078337 := bstep (se 2 (by rfl) ⟨6029376, by rfl⟩ : syracuseStep 16078337 = 12058753) B12058753
theorem B10718891 : Blo 2115435 10718891 := bstep (se 1 (by rfl) ⟨8039168, by rfl⟩ : syracuseStep 10718891 = 16078337) B16078337
theorem B7145927 : Blo 2115435 7145927 := bstep (se 1 (by rfl) ⟨5359445, by rfl⟩ : syracuseStep 7145927 = 10718891) B10718891
theorem B4763951 : Blo 2115435 4763951 := bstep (se 1 (by rfl) ⟨3572963, by rfl⟩ : syracuseStep 4763951 = 7145927) B7145927
theorem B3175967 : Blo 2115435 3175967 := bstep (se 1 (by rfl) ⟨2381975, by rfl⟩ : syracuseStep 3175967 = 4763951) B4763951
theorem B2117311 : Blo 2115435 2117311 := bstep (se 1 (by rfl) ⟨1587983, by rfl⟩ : syracuseStep 2117311 = 3175967) B3175967
theorem B3175973 : Blo 2115435 3175973 := bbase (se 4 (by rfl) ⟨297747, by rfl⟩ : syracuseStep 3175973 = 595495) (by norm_num)
theorem B2117315 : Blo 2115435 2117315 := bstep (se 1 (by rfl) ⟨1587986, by rfl⟩ : syracuseStep 2117315 = 3175973) B3175973
theorem B2679733 : Blo 2115435 2679733 := bbase (se 5 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 2679733 = 251225) (by norm_num)
theorem B3572977 : Blo 2115435 3572977 := bstep (se 2 (by rfl) ⟨1339866, by rfl⟩ : syracuseStep 3572977 = 2679733) B2679733
theorem B4763969 : Blo 2115435 4763969 := bstep (se 2 (by rfl) ⟨1786488, by rfl⟩ : syracuseStep 4763969 = 3572977) B3572977
theorem B3175979 : Blo 2115435 3175979 := bstep (se 1 (by rfl) ⟨2381984, by rfl⟩ : syracuseStep 3175979 = 4763969) B4763969
theorem B2117319 : Blo 2115435 2117319 := bstep (se 1 (by rfl) ⟨1587989, by rfl⟩ : syracuseStep 2117319 = 3175979) B3175979
theorem B2381989 : Blo 2115435 2381989 := bbase (se 4 (by rfl) ⟨223311, by rfl⟩ : syracuseStep 2381989 = 446623) (by norm_num)
theorem B3175985 : Blo 2115435 3175985 := bstep (se 2 (by rfl) ⟨1190994, by rfl⟩ : syracuseStep 3175985 = 2381989) B2381989
theorem B2117323 : Blo 2115435 2117323 := bstep (se 1 (by rfl) ⟨1587992, by rfl⟩ : syracuseStep 2117323 = 3175985) B3175985
theorem B2685349 : Blo 2115435 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B3580465 : Blo 2115435 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B4773953 : Blo 2115435 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B3182635 : Blo 2115435 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B4243513 : Blo 2115435 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B5658017 : Blo 2115435 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B15088045 : Blo 2115435 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B20117393 : Blo 2115435 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B13411595 : Blo 2115435 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B35764253 : Blo 2115435 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B23842835 : Blo 2115435 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B15895223 : Blo 2115435 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B10596815 : Blo 2115435 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B7064543 : Blo 2115435 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B18838781 : Blo 2115435 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B12559187 : Blo 2115435 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B8372791 : Blo 2115435 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B44654885 : Blo 2115435 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B29769923 : Blo 2115435 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B19846615 : Blo 2115435 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B26462153 : Blo 2115435 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B70565741 : Blo 2115435 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B47043827 : Blo 2115435 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B31362551 : Blo 2115435 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B20908367 : Blo 2115435 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B13938911 : Blo 2115435 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B9292607 : Blo 2115435 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B6195071 : Blo 2115435 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B4130047 : Blo 2115435 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B22026917 : Blo 2115435 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B14684611 : Blo 2115435 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B19579481 : Blo 2115435 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B13052987 : Blo 2115435 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B8701991 : Blo 2115435 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B5801327 : Blo 2115435 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B3867551 : Blo 2115435 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B41253877 : Blo 2115435 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B55005169 : Blo 2115435 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B73340225 : Blo 2115435 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B48893483 : Blo 2115435 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B130382621 : Blo 2115435 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B86921747 : Blo 2115435 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B57947831 : Blo 2115435 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B38631887 : Blo 2115435 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B25754591 : Blo 2115435 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B17169727 : Blo 2115435 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B22892969 : Blo 2115435 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B15261979 : Blo 2115435 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B20349305 : Blo 2115435 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B13566203 : Blo 2115435 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B9044135 : Blo 2115435 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B6029423 : Blo 2115435 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B4019615 : Blo 2115435 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B2679743 : Blo 2115435 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B7145981 : Blo 2115435 7145981 := bstep (se 3 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 7145981 = 2679743) B2679743
theorem B4763987 : Blo 2115435 4763987 := bstep (se 1 (by rfl) ⟨3572990, by rfl⟩ : syracuseStep 4763987 = 7145981) B7145981
theorem B3175991 : Blo 2115435 3175991 := bstep (se 1 (by rfl) ⟨2381993, by rfl⟩ : syracuseStep 3175991 = 4763987) B4763987
theorem B2117327 : Blo 2115435 2117327 := bstep (se 1 (by rfl) ⟨1587995, by rfl⟩ : syracuseStep 2117327 = 3175991) B3175991
theorem B3175997 : Blo 2115435 3175997 := bbase (se 3 (by rfl) ⟨595499, by rfl⟩ : syracuseStep 3175997 = 1190999) (by norm_num)
theorem B2117331 : Blo 2115435 2117331 := bstep (se 1 (by rfl) ⟨1587998, by rfl⟩ : syracuseStep 2117331 = 3175997) B3175997
theorem B4764005 : Blo 2115435 4764005 := bbase (se 4 (by rfl) ⟨446625, by rfl⟩ : syracuseStep 4764005 = 893251) (by norm_num)
theorem B3176003 : Blo 2115435 3176003 := bstep (se 1 (by rfl) ⟨2382002, by rfl⟩ : syracuseStep 3176003 = 4764005) B4764005
theorem B2117335 : Blo 2115435 2117335 := bstep (se 1 (by rfl) ⟨1588001, by rfl⟩ : syracuseStep 2117335 = 3176003) B3176003
theorem B5359517 : Blo 2115435 5359517 := bbase (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) (by norm_num)
theorem B3573011 : Blo 2115435 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B2382007 : Blo 2115435 2382007 := bstep (se 1 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 2382007 = 3573011) B3573011
theorem B3176009 : Blo 2115435 3176009 := bstep (se 2 (by rfl) ⟨1191003, by rfl⟩ : syracuseStep 3176009 = 2382007) B2382007
theorem B2117339 : Blo 2115435 2117339 := bstep (se 1 (by rfl) ⟨1588004, by rfl⟩ : syracuseStep 2117339 = 3176009) B3176009
theorem B4019645 : Blo 2115435 4019645 := bbase (se 3 (by rfl) ⟨753683, by rfl⟩ : syracuseStep 4019645 = 1507367) (by norm_num)
theorem B10719053 : Blo 2115435 10719053 := bstep (se 3 (by rfl) ⟨2009822, by rfl⟩ : syracuseStep 10719053 = 4019645) B4019645
theorem B7146035 : Blo 2115435 7146035 := bstep (se 1 (by rfl) ⟨5359526, by rfl⟩ : syracuseStep 7146035 = 10719053) B10719053
theorem B4764023 : Blo 2115435 4764023 := bstep (se 1 (by rfl) ⟨3573017, by rfl⟩ : syracuseStep 4764023 = 7146035) B7146035
theorem B3176015 : Blo 2115435 3176015 := bstep (se 1 (by rfl) ⟨2382011, by rfl⟩ : syracuseStep 3176015 = 4764023) B4764023
theorem B2117343 : Blo 2115435 2117343 := bstep (se 1 (by rfl) ⟨1588007, by rfl⟩ : syracuseStep 2117343 = 3176015) B3176015
theorem B3176021 : Blo 2115435 3176021 := bbase (se 8 (by rfl) ⟨18609, by rfl⟩ : syracuseStep 3176021 = 37219) (by norm_num)
theorem B2117347 : Blo 2115435 2117347 := bstep (se 1 (by rfl) ⟨1588010, by rfl⟩ : syracuseStep 2117347 = 3176021) B3176021
theorem B3391589 : Blo 2115435 3391589 := bbase (se 4 (by rfl) ⟨317961, by rfl⟩ : syracuseStep 3391589 = 635923) (by norm_num)
theorem B9044237 : Blo 2115435 9044237 := bstep (se 3 (by rfl) ⟨1695794, by rfl⟩ : syracuseStep 9044237 = 3391589) B3391589
theorem B6029491 : Blo 2115435 6029491 := bstep (se 1 (by rfl) ⟨4522118, by rfl⟩ : syracuseStep 6029491 = 9044237) B9044237
theorem B8039321 : Blo 2115435 8039321 := bstep (se 2 (by rfl) ⟨3014745, by rfl⟩ : syracuseStep 8039321 = 6029491) B6029491
theorem B5359547 : Blo 2115435 5359547 := bstep (se 1 (by rfl) ⟨4019660, by rfl⟩ : syracuseStep 5359547 = 8039321) B8039321
theorem B3573031 : Blo 2115435 3573031 := bstep (se 1 (by rfl) ⟨2679773, by rfl⟩ : syracuseStep 3573031 = 5359547) B5359547
theorem B4764041 : Blo 2115435 4764041 := bstep (se 2 (by rfl) ⟨1786515, by rfl⟩ : syracuseStep 4764041 = 3573031) B3573031
theorem B3176027 : Blo 2115435 3176027 := bstep (se 1 (by rfl) ⟨2382020, by rfl⟩ : syracuseStep 3176027 = 4764041) B4764041
theorem B2117351 : Blo 2115435 2117351 := bstep (se 1 (by rfl) ⟨1588013, by rfl⟩ : syracuseStep 2117351 = 3176027) B3176027
theorem B2382025 : Blo 2115435 2382025 := bbase (se 2 (by rfl) ⟨893259, by rfl⟩ : syracuseStep 2382025 = 1786519) (by norm_num)
theorem B3176033 : Blo 2115435 3176033 := bstep (se 2 (by rfl) ⟨1191012, by rfl⟩ : syracuseStep 3176033 = 2382025) B2382025
theorem B2117355 : Blo 2115435 2117355 := bstep (se 1 (by rfl) ⟨1588016, by rfl⟩ : syracuseStep 2117355 = 3176033) B3176033
theorem B10174805 : Blo 2115435 10174805 := bbase (se 10 (by rfl) ⟨14904, by rfl⟩ : syracuseStep 10174805 = 29809) (by norm_num)
theorem B6783203 : Blo 2115435 6783203 := bstep (se 1 (by rfl) ⟨5087402, by rfl⟩ : syracuseStep 6783203 = 10174805) B10174805
theorem B18088541 : Blo 2115435 18088541 := bstep (se 3 (by rfl) ⟨3391601, by rfl⟩ : syracuseStep 18088541 = 6783203) B6783203
theorem B12059027 : Blo 2115435 12059027 := bstep (se 1 (by rfl) ⟨9044270, by rfl⟩ : syracuseStep 12059027 = 18088541) B18088541
theorem B8039351 : Blo 2115435 8039351 := bstep (se 1 (by rfl) ⟨6029513, by rfl⟩ : syracuseStep 8039351 = 12059027) B12059027
theorem B5359567 : Blo 2115435 5359567 := bstep (se 1 (by rfl) ⟨4019675, by rfl⟩ : syracuseStep 5359567 = 8039351) B8039351
theorem B7146089 : Blo 2115435 7146089 := bstep (se 2 (by rfl) ⟨2679783, by rfl⟩ : syracuseStep 7146089 = 5359567) B5359567
theorem B4764059 : Blo 2115435 4764059 := bstep (se 1 (by rfl) ⟨3573044, by rfl⟩ : syracuseStep 4764059 = 7146089) B7146089
theorem B3176039 : Blo 2115435 3176039 := bstep (se 1 (by rfl) ⟨2382029, by rfl⟩ : syracuseStep 3176039 = 4764059) B4764059
theorem B2117359 : Blo 2115435 2117359 := bstep (se 1 (by rfl) ⟨1588019, by rfl⟩ : syracuseStep 2117359 = 3176039) B3176039
theorem B3176045 : Blo 2115435 3176045 := bbase (se 3 (by rfl) ⟨595508, by rfl⟩ : syracuseStep 3176045 = 1191017) (by norm_num)
theorem B2117363 : Blo 2115435 2117363 := bstep (se 1 (by rfl) ⟨1588022, by rfl⟩ : syracuseStep 2117363 = 3176045) B3176045
theorem B4764077 : Blo 2115435 4764077 := bbase (se 3 (by rfl) ⟨893264, by rfl⟩ : syracuseStep 4764077 = 1786529) (by norm_num)
theorem B3176051 : Blo 2115435 3176051 := bstep (se 1 (by rfl) ⟨2382038, by rfl⟩ : syracuseStep 3176051 = 4764077) B4764077
theorem B2117367 : Blo 2115435 2117367 := bstep (se 1 (by rfl) ⟨1588025, by rfl⟩ : syracuseStep 2117367 = 3176051) B3176051
theorem B2261081 : Blo 2115435 2261081 := bbase (se 2 (by rfl) ⟨847905, by rfl⟩ : syracuseStep 2261081 = 1695811) (by norm_num)
theorem B6029549 : Blo 2115435 6029549 := bstep (se 3 (by rfl) ⟨1130540, by rfl⟩ : syracuseStep 6029549 = 2261081) B2261081
theorem B4019699 : Blo 2115435 4019699 := bstep (se 1 (by rfl) ⟨3014774, by rfl⟩ : syracuseStep 4019699 = 6029549) B6029549
theorem B2679799 : Blo 2115435 2679799 := bstep (se 1 (by rfl) ⟨2009849, by rfl⟩ : syracuseStep 2679799 = 4019699) B4019699
theorem B3573065 : Blo 2115435 3573065 := bstep (se 2 (by rfl) ⟨1339899, by rfl⟩ : syracuseStep 3573065 = 2679799) B2679799
theorem B2382043 : Blo 2115435 2382043 := bstep (se 1 (by rfl) ⟨1786532, by rfl⟩ : syracuseStep 2382043 = 3573065) B3573065
theorem B3176057 : Blo 2115435 3176057 := bstep (se 2 (by rfl) ⟨1191021, by rfl⟩ : syracuseStep 3176057 = 2382043) B2382043
theorem B2117371 : Blo 2115435 2117371 := bstep (se 1 (by rfl) ⟨1588028, by rfl⟩ : syracuseStep 2117371 = 3176057) B3176057
theorem B11446741 : Blo 2115435 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B61049285 : Blo 2115435 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B40699523 : Blo 2115435 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B27133015 : Blo 2115435 27133015 := bstep (se 1 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 27133015 = 40699523) B40699523
theorem B36177353 : Blo 2115435 36177353 := bstep (se 2 (by rfl) ⟨13566507, by rfl⟩ : syracuseStep 36177353 = 27133015) B27133015
theorem B24118235 : Blo 2115435 24118235 := bstep (se 1 (by rfl) ⟨18088676, by rfl⟩ : syracuseStep 24118235 = 36177353) B36177353
theorem B16078823 : Blo 2115435 16078823 := bstep (se 1 (by rfl) ⟨12059117, by rfl⟩ : syracuseStep 16078823 = 24118235) B24118235
theorem B10719215 : Blo 2115435 10719215 := bstep (se 1 (by rfl) ⟨8039411, by rfl⟩ : syracuseStep 10719215 = 16078823) B16078823
theorem B7146143 : Blo 2115435 7146143 := bstep (se 1 (by rfl) ⟨5359607, by rfl⟩ : syracuseStep 7146143 = 10719215) B10719215
theorem B4764095 : Blo 2115435 4764095 := bstep (se 1 (by rfl) ⟨3573071, by rfl⟩ : syracuseStep 4764095 = 7146143) B7146143
theorem B3176063 : Blo 2115435 3176063 := bstep (se 1 (by rfl) ⟨2382047, by rfl⟩ : syracuseStep 3176063 = 4764095) B4764095
theorem B2117375 : Blo 2115435 2117375 := bstep (se 1 (by rfl) ⟨1588031, by rfl⟩ : syracuseStep 2117375 = 3176063) B3176063
theorem B3176069 : Blo 2115435 3176069 := bbase (se 4 (by rfl) ⟨297756, by rfl⟩ : syracuseStep 3176069 = 595513) (by norm_num)
theorem B2117379 : Blo 2115435 2117379 := bstep (se 1 (by rfl) ⟨1588034, by rfl⟩ : syracuseStep 2117379 = 3176069) B3176069
theorem B3573085 : Blo 2115435 3573085 := bbase (se 3 (by rfl) ⟨669953, by rfl⟩ : syracuseStep 3573085 = 1339907) (by norm_num)
theorem B4764113 : Blo 2115435 4764113 := bstep (se 2 (by rfl) ⟨1786542, by rfl⟩ : syracuseStep 4764113 = 3573085) B3573085
theorem B3176075 : Blo 2115435 3176075 := bstep (se 1 (by rfl) ⟨2382056, by rfl⟩ : syracuseStep 3176075 = 4764113) B4764113
theorem B2117383 : Blo 2115435 2117383 := bstep (se 1 (by rfl) ⟨1588037, by rfl⟩ : syracuseStep 2117383 = 3176075) B3176075
theorem B2382061 : Blo 2115435 2382061 := bbase (se 3 (by rfl) ⟨446636, by rfl⟩ : syracuseStep 2382061 = 893273) (by norm_num)
theorem B3176081 : Blo 2115435 3176081 := bstep (se 2 (by rfl) ⟨1191030, by rfl⟩ : syracuseStep 3176081 = 2382061) B2382061
theorem B2117387 : Blo 2115435 2117387 := bstep (se 1 (by rfl) ⟨1588040, by rfl⟩ : syracuseStep 2117387 = 3176081) B3176081
theorem B7146197 : Blo 2115435 7146197 := bbase (se 7 (by rfl) ⟨83744, by rfl⟩ : syracuseStep 7146197 = 167489) (by norm_num)
theorem B4764131 : Blo 2115435 4764131 := bstep (se 1 (by rfl) ⟨3573098, by rfl⟩ : syracuseStep 4764131 = 7146197) B7146197
theorem B3176087 : Blo 2115435 3176087 := bstep (se 1 (by rfl) ⟨2382065, by rfl⟩ : syracuseStep 3176087 = 4764131) B4764131
theorem B2117391 : Blo 2115435 2117391 := bstep (se 1 (by rfl) ⟨1588043, by rfl⟩ : syracuseStep 2117391 = 3176087) B3176087
theorem B3176093 : Blo 2115435 3176093 := bbase (se 3 (by rfl) ⟨595517, by rfl⟩ : syracuseStep 3176093 = 1191035) (by norm_num)
theorem B2117395 : Blo 2115435 2117395 := bstep (se 1 (by rfl) ⟨1588046, by rfl⟩ : syracuseStep 2117395 = 3176093) B3176093
theorem B4764149 : Blo 2115435 4764149 := bbase (se 5 (by rfl) ⟨223319, by rfl⟩ : syracuseStep 4764149 = 446639) (by norm_num)
theorem B3176099 : Blo 2115435 3176099 := bstep (se 1 (by rfl) ⟨2382074, by rfl⟩ : syracuseStep 3176099 = 4764149) B4764149
theorem B2117399 : Blo 2115435 2117399 := bstep (se 1 (by rfl) ⟨1588049, by rfl⟩ : syracuseStep 2117399 = 3176099) B3176099
theorem B6875893 : Blo 2115435 6875893 := bbase (se 5 (by rfl) ⟨322307, by rfl⟩ : syracuseStep 6875893 = 644615) (by norm_num)
theorem B36671429 : Blo 2115435 36671429 := bstep (se 4 (by rfl) ⟨3437946, by rfl⟩ : syracuseStep 36671429 = 6875893) B6875893
theorem B24447619 : Blo 2115435 24447619 := bstep (se 1 (by rfl) ⟨18335714, by rfl⟩ : syracuseStep 24447619 = 36671429) B36671429
theorem B32596825 : Blo 2115435 32596825 := bstep (se 2 (by rfl) ⟨12223809, by rfl⟩ : syracuseStep 32596825 = 24447619) B24447619
theorem B43462433 : Blo 2115435 43462433 := bstep (se 2 (by rfl) ⟨16298412, by rfl⟩ : syracuseStep 43462433 = 32596825) B32596825
theorem B28974955 : Blo 2115435 28974955 := bstep (se 1 (by rfl) ⟨21731216, by rfl⟩ : syracuseStep 28974955 = 43462433) B43462433
theorem B38633273 : Blo 2115435 38633273 := bstep (se 2 (by rfl) ⟨14487477, by rfl⟩ : syracuseStep 38633273 = 28974955) B28974955
theorem B25755515 : Blo 2115435 25755515 := bstep (se 1 (by rfl) ⟨19316636, by rfl⟩ : syracuseStep 25755515 = 38633273) B38633273
theorem B17170343 : Blo 2115435 17170343 := bstep (se 1 (by rfl) ⟨12877757, by rfl⟩ : syracuseStep 17170343 = 25755515) B25755515
theorem B11446895 : Blo 2115435 11446895 := bstep (se 1 (by rfl) ⟨8585171, by rfl⟩ : syracuseStep 11446895 = 17170343) B17170343
theorem B7631263 : Blo 2115435 7631263 := bstep (se 1 (by rfl) ⟨5723447, by rfl⟩ : syracuseStep 7631263 = 11446895) B11446895
theorem B40700069 : Blo 2115435 40700069 := bstep (se 4 (by rfl) ⟨3815631, by rfl⟩ : syracuseStep 40700069 = 7631263) B7631263
theorem B27133379 : Blo 2115435 27133379 := bstep (se 1 (by rfl) ⟨20350034, by rfl⟩ : syracuseStep 27133379 = 40700069) B40700069
theorem B18088919 : Blo 2115435 18088919 := bstep (se 1 (by rfl) ⟨13566689, by rfl⟩ : syracuseStep 18088919 = 27133379) B27133379
theorem B12059279 : Blo 2115435 12059279 := bstep (se 1 (by rfl) ⟨9044459, by rfl⟩ : syracuseStep 12059279 = 18088919) B18088919
theorem B8039519 : Blo 2115435 8039519 := bstep (se 1 (by rfl) ⟨6029639, by rfl⟩ : syracuseStep 8039519 = 12059279) B12059279
theorem B5359679 : Blo 2115435 5359679 := bstep (se 1 (by rfl) ⟨4019759, by rfl⟩ : syracuseStep 5359679 = 8039519) B8039519
theorem B3573119 : Blo 2115435 3573119 := bstep (se 1 (by rfl) ⟨2679839, by rfl⟩ : syracuseStep 3573119 = 5359679) B5359679
theorem B2382079 : Blo 2115435 2382079 := bstep (se 1 (by rfl) ⟨1786559, by rfl⟩ : syracuseStep 2382079 = 3573119) B3573119
theorem B3176105 : Blo 2115435 3176105 := bstep (se 2 (by rfl) ⟨1191039, by rfl⟩ : syracuseStep 3176105 = 2382079) B2382079
theorem B2117403 : Blo 2115435 2117403 := bstep (se 1 (by rfl) ⟨1588052, by rfl⟩ : syracuseStep 2117403 = 3176105) B3176105
theorem B3621877 : Blo 2115435 3621877 := bbase (se 5 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 3621877 = 339551) (by norm_num)
theorem B19316677 : Blo 2115435 19316677 := bstep (se 4 (by rfl) ⟨1810938, by rfl⟩ : syracuseStep 19316677 = 3621877) B3621877
theorem B25755569 : Blo 2115435 25755569 := bstep (se 2 (by rfl) ⟨9658338, by rfl⟩ : syracuseStep 25755569 = 19316677) B19316677
theorem B17170379 : Blo 2115435 17170379 := bstep (se 1 (by rfl) ⟨12877784, by rfl⟩ : syracuseStep 17170379 = 25755569) B25755569
theorem B11446919 : Blo 2115435 11446919 := bstep (se 1 (by rfl) ⟨8585189, by rfl⟩ : syracuseStep 11446919 = 17170379) B17170379
theorem B7631279 : Blo 2115435 7631279 := bstep (se 1 (by rfl) ⟨5723459, by rfl⟩ : syracuseStep 7631279 = 11446919) B11446919
theorem B5087519 : Blo 2115435 5087519 := bstep (se 1 (by rfl) ⟨3815639, by rfl⟩ : syracuseStep 5087519 = 7631279) B7631279
theorem B3391679 : Blo 2115435 3391679 := bstep (se 1 (by rfl) ⟨2543759, by rfl⟩ : syracuseStep 3391679 = 5087519) B5087519
theorem B2261119 : Blo 2115435 2261119 := bstep (se 1 (by rfl) ⟨1695839, by rfl⟩ : syracuseStep 2261119 = 3391679) B3391679
theorem B3014825 : Blo 2115435 3014825 := bstep (se 2 (by rfl) ⟨1130559, by rfl⟩ : syracuseStep 3014825 = 2261119) B2261119
theorem B8039533 : Blo 2115435 8039533 := bstep (se 3 (by rfl) ⟨1507412, by rfl⟩ : syracuseStep 8039533 = 3014825) B3014825
theorem B10719377 : Blo 2115435 10719377 := bstep (se 2 (by rfl) ⟨4019766, by rfl⟩ : syracuseStep 10719377 = 8039533) B8039533
theorem B7146251 : Blo 2115435 7146251 := bstep (se 1 (by rfl) ⟨5359688, by rfl⟩ : syracuseStep 7146251 = 10719377) B10719377
theorem B4764167 : Blo 2115435 4764167 := bstep (se 1 (by rfl) ⟨3573125, by rfl⟩ : syracuseStep 4764167 = 7146251) B7146251
theorem B3176111 : Blo 2115435 3176111 := bstep (se 1 (by rfl) ⟨2382083, by rfl⟩ : syracuseStep 3176111 = 4764167) B4764167
theorem B2117407 : Blo 2115435 2117407 := bstep (se 1 (by rfl) ⟨1588055, by rfl⟩ : syracuseStep 2117407 = 3176111) B3176111
theorem B3176117 : Blo 2115435 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B2117411 : Blo 2115435 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B5359709 : Blo 2115435 5359709 := bbase (se 3 (by rfl) ⟨1004945, by rfl⟩ : syracuseStep 5359709 = 2009891) (by norm_num)
theorem B3573139 : Blo 2115435 3573139 := bstep (se 1 (by rfl) ⟨2679854, by rfl⟩ : syracuseStep 3573139 = 5359709) B5359709
theorem B4764185 : Blo 2115435 4764185 := bstep (se 2 (by rfl) ⟨1786569, by rfl⟩ : syracuseStep 4764185 = 3573139) B3573139
theorem B3176123 : Blo 2115435 3176123 := bstep (se 1 (by rfl) ⟨2382092, by rfl⟩ : syracuseStep 3176123 = 4764185) B4764185
theorem B2117415 : Blo 2115435 2117415 := bstep (se 1 (by rfl) ⟨1588061, by rfl⟩ : syracuseStep 2117415 = 3176123) B3176123
theorem B2382097 : Blo 2115435 2382097 := bbase (se 2 (by rfl) ⟨893286, by rfl⟩ : syracuseStep 2382097 = 1786573) (by norm_num)
theorem B3176129 : Blo 2115435 3176129 := bstep (se 2 (by rfl) ⟨1191048, by rfl⟩ : syracuseStep 3176129 = 2382097) B2382097
theorem B2117419 : Blo 2115435 2117419 := bstep (se 1 (by rfl) ⟨1588064, by rfl⟩ : syracuseStep 2117419 = 3176129) B3176129
theorem B4019797 : Blo 2115435 4019797 := bbase (se 8 (by rfl) ⟨23553, by rfl⟩ : syracuseStep 4019797 = 47107) (by norm_num)
theorem B5359729 : Blo 2115435 5359729 := bstep (se 2 (by rfl) ⟨2009898, by rfl⟩ : syracuseStep 5359729 = 4019797) B4019797
theorem B7146305 : Blo 2115435 7146305 := bstep (se 2 (by rfl) ⟨2679864, by rfl⟩ : syracuseStep 7146305 = 5359729) B5359729
theorem B4764203 : Blo 2115435 4764203 := bstep (se 1 (by rfl) ⟨3573152, by rfl⟩ : syracuseStep 4764203 = 7146305) B7146305
theorem B3176135 : Blo 2115435 3176135 := bstep (se 1 (by rfl) ⟨2382101, by rfl⟩ : syracuseStep 3176135 = 4764203) B4764203
theorem B2117423 : Blo 2115435 2117423 := bstep (se 1 (by rfl) ⟨1588067, by rfl⟩ : syracuseStep 2117423 = 3176135) B3176135
theorem B3176141 : Blo 2115435 3176141 := bbase (se 3 (by rfl) ⟨595526, by rfl⟩ : syracuseStep 3176141 = 1191053) (by norm_num)
theorem B2117427 : Blo 2115435 2117427 := bstep (se 1 (by rfl) ⟨1588070, by rfl⟩ : syracuseStep 2117427 = 3176141) B3176141
theorem B4764221 : Blo 2115435 4764221 := bbase (se 3 (by rfl) ⟨893291, by rfl⟩ : syracuseStep 4764221 = 1786583) (by norm_num)
theorem B3176147 : Blo 2115435 3176147 := bstep (se 1 (by rfl) ⟨2382110, by rfl⟩ : syracuseStep 3176147 = 4764221) B4764221
theorem B2117431 : Blo 2115435 2117431 := bstep (se 1 (by rfl) ⟨1588073, by rfl⟩ : syracuseStep 2117431 = 3176147) B3176147
theorem B3573173 : Blo 2115435 3573173 := bbase (se 5 (by rfl) ⟨167492, by rfl⟩ : syracuseStep 3573173 = 334985) (by norm_num)
theorem B2382115 : Blo 2115435 2382115 := bstep (se 1 (by rfl) ⟨1786586, by rfl⟩ : syracuseStep 2382115 = 3573173) B3573173
theorem B3176153 : Blo 2115435 3176153 := bstep (se 2 (by rfl) ⟨1191057, by rfl⟩ : syracuseStep 3176153 = 2382115) B2382115
theorem B2117435 : Blo 2115435 2117435 := bstep (se 1 (by rfl) ⟨1588076, by rfl⟩ : syracuseStep 2117435 = 3176153) B3176153
theorem C0 (j : ℕ) (h1 : 528858 ≤ j) (h2 : j ≤ 529358) : Blo 2115435 (4 * j + 3) := by
  interval_cases j
  · exact B2115435
  · exact B2115439
  · exact B2115443
  · exact B2115447
  · exact B2115451
  · exact B2115455
  · exact B2115459
  · exact B2115463
  · exact B2115467
  · exact B2115471
  · exact B2115475
  · exact B2115479
  · exact B2115483
  · exact B2115487
  · exact B2115491
  · exact B2115495
  · exact B2115499
  · exact B2115503
  · exact B2115507
  · exact B2115511
  · exact B2115515
  · exact B2115519
  · exact B2115523
  · exact B2115527
  · exact B2115531
  · exact B2115535
  · exact B2115539
  · exact B2115543
  · exact B2115547
  · exact B2115551
  · exact B2115555
  · exact B2115559
  · exact B2115563
  · exact B2115567
  · exact B2115571
  · exact B2115575
  · exact B2115579
  · exact B2115583
  · exact B2115587
  · exact B2115591
  · exact B2115595
  · exact B2115599
  · exact B2115603
  · exact B2115607
  · exact B2115611
  · exact B2115615
  · exact B2115619
  · exact B2115623
  · exact B2115627
  · exact B2115631
  · exact B2115635
  · exact B2115639
  · exact B2115643
  · exact B2115647
  · exact B2115651
  · exact B2115655
  · exact B2115659
  · exact B2115663
  · exact B2115667
  · exact B2115671
  · exact B2115675
  · exact B2115679
  · exact B2115683
  · exact B2115687
  · exact B2115691
  · exact B2115695
  · exact B2115699
  · exact B2115703
  · exact B2115707
  · exact B2115711
  · exact B2115715
  · exact B2115719
  · exact B2115723
  · exact B2115727
  · exact B2115731
  · exact B2115735
  · exact B2115739
  · exact B2115743
  · exact B2115747
  · exact B2115751
  · exact B2115755
  · exact B2115759
  · exact B2115763
  · exact B2115767
  · exact B2115771
  · exact B2115775
  · exact B2115779
  · exact B2115783
  · exact B2115787
  · exact B2115791
  · exact B2115795
  · exact B2115799
  · exact B2115803
  · exact B2115807
  · exact B2115811
  · exact B2115815
  · exact B2115819
  · exact B2115823
  · exact B2115827
  · exact B2115831
  · exact B2115835
  · exact B2115839
  · exact B2115843
  · exact B2115847
  · exact B2115851
  · exact B2115855
  · exact B2115859
  · exact B2115863
  · exact B2115867
  · exact B2115871
  · exact B2115875
  · exact B2115879
  · exact B2115883
  · exact B2115887
  · exact B2115891
  · exact B2115895
  · exact B2115899
  · exact B2115903
  · exact B2115907
  · exact B2115911
  · exact B2115915
  · exact B2115919
  · exact B2115923
  · exact B2115927
  · exact B2115931
  · exact B2115935
  · exact B2115939
  · exact B2115943
  · exact B2115947
  · exact B2115951
  · exact B2115955
  · exact B2115959
  · exact B2115963
  · exact B2115967
  · exact B2115971
  · exact B2115975
  · exact B2115979
  · exact B2115983
  · exact B2115987
  · exact B2115991
  · exact B2115995
  · exact B2115999
  · exact B2116003
  · exact B2116007
  · exact B2116011
  · exact B2116015
  · exact B2116019
  · exact B2116023
  · exact B2116027
  · exact B2116031
  · exact B2116035
  · exact B2116039
  · exact B2116043
  · exact B2116047
  · exact B2116051
  · exact B2116055
  · exact B2116059
  · exact B2116063
  · exact B2116067
  · exact B2116071
  · exact B2116075
  · exact B2116079
  · exact B2116083
  · exact B2116087
  · exact B2116091
  · exact B2116095
  · exact B2116099
  · exact B2116103
  · exact B2116107
  · exact B2116111
  · exact B2116115
  · exact B2116119
  · exact B2116123
  · exact B2116127
  · exact B2116131
  · exact B2116135
  · exact B2116139
  · exact B2116143
  · exact B2116147
  · exact B2116151
  · exact B2116155
  · exact B2116159
  · exact B2116163
  · exact B2116167
  · exact B2116171
  · exact B2116175
  · exact B2116179
  · exact B2116183
  · exact B2116187
  · exact B2116191
  · exact B2116195
  · exact B2116199
  · exact B2116203
  · exact B2116207
  · exact B2116211
  · exact B2116215
  · exact B2116219
  · exact B2116223
  · exact B2116227
  · exact B2116231
  · exact B2116235
  · exact B2116239
  · exact B2116243
  · exact B2116247
  · exact B2116251
  · exact B2116255
  · exact B2116259
  · exact B2116263
  · exact B2116267
  · exact B2116271
  · exact B2116275
  · exact B2116279
  · exact B2116283
  · exact B2116287
  · exact B2116291
  · exact B2116295
  · exact B2116299
  · exact B2116303
  · exact B2116307
  · exact B2116311
  · exact B2116315
  · exact B2116319
  · exact B2116323
  · exact B2116327
  · exact B2116331
  · exact B2116335
  · exact B2116339
  · exact B2116343
  · exact B2116347
  · exact B2116351
  · exact B2116355
  · exact B2116359
  · exact B2116363
  · exact B2116367
  · exact B2116371
  · exact B2116375
  · exact B2116379
  · exact B2116383
  · exact B2116387
  · exact B2116391
  · exact B2116395
  · exact B2116399
  · exact B2116403
  · exact B2116407
  · exact B2116411
  · exact B2116415
  · exact B2116419
  · exact B2116423
  · exact B2116427
  · exact B2116431
  · exact B2116435
  · exact B2116439
  · exact B2116443
  · exact B2116447
  · exact B2116451
  · exact B2116455
  · exact B2116459
  · exact B2116463
  · exact B2116467
  · exact B2116471
  · exact B2116475
  · exact B2116479
  · exact B2116483
  · exact B2116487
  · exact B2116491
  · exact B2116495
  · exact B2116499
  · exact B2116503
  · exact B2116507
  · exact B2116511
  · exact B2116515
  · exact B2116519
  · exact B2116523
  · exact B2116527
  · exact B2116531
  · exact B2116535
  · exact B2116539
  · exact B2116543
  · exact B2116547
  · exact B2116551
  · exact B2116555
  · exact B2116559
  · exact B2116563
  · exact B2116567
  · exact B2116571
  · exact B2116575
  · exact B2116579
  · exact B2116583
  · exact B2116587
  · exact B2116591
  · exact B2116595
  · exact B2116599
  · exact B2116603
  · exact B2116607
  · exact B2116611
  · exact B2116615
  · exact B2116619
  · exact B2116623
  · exact B2116627
  · exact B2116631
  · exact B2116635
  · exact B2116639
  · exact B2116643
  · exact B2116647
  · exact B2116651
  · exact B2116655
  · exact B2116659
  · exact B2116663
  · exact B2116667
  · exact B2116671
  · exact B2116675
  · exact B2116679
  · exact B2116683
  · exact B2116687
  · exact B2116691
  · exact B2116695
  · exact B2116699
  · exact B2116703
  · exact B2116707
  · exact B2116711
  · exact B2116715
  · exact B2116719
  · exact B2116723
  · exact B2116727
  · exact B2116731
  · exact B2116735
  · exact B2116739
  · exact B2116743
  · exact B2116747
  · exact B2116751
  · exact B2116755
  · exact B2116759
  · exact B2116763
  · exact B2116767
  · exact B2116771
  · exact B2116775
  · exact B2116779
  · exact B2116783
  · exact B2116787
  · exact B2116791
  · exact B2116795
  · exact B2116799
  · exact B2116803
  · exact B2116807
  · exact B2116811
  · exact B2116815
  · exact B2116819
  · exact B2116823
  · exact B2116827
  · exact B2116831
  · exact B2116835
  · exact B2116839
  · exact B2116843
  · exact B2116847
  · exact B2116851
  · exact B2116855
  · exact B2116859
  · exact B2116863
  · exact B2116867
  · exact B2116871
  · exact B2116875
  · exact B2116879
  · exact B2116883
  · exact B2116887
  · exact B2116891
  · exact B2116895
  · exact B2116899
  · exact B2116903
  · exact B2116907
  · exact B2116911
  · exact B2116915
  · exact B2116919
  · exact B2116923
  · exact B2116927
  · exact B2116931
  · exact B2116935
  · exact B2116939
  · exact B2116943
  · exact B2116947
  · exact B2116951
  · exact B2116955
  · exact B2116959
  · exact B2116963
  · exact B2116967
  · exact B2116971
  · exact B2116975
  · exact B2116979
  · exact B2116983
  · exact B2116987
  · exact B2116991
  · exact B2116995
  · exact B2116999
  · exact B2117003
  · exact B2117007
  · exact B2117011
  · exact B2117015
  · exact B2117019
  · exact B2117023
  · exact B2117027
  · exact B2117031
  · exact B2117035
  · exact B2117039
  · exact B2117043
  · exact B2117047
  · exact B2117051
  · exact B2117055
  · exact B2117059
  · exact B2117063
  · exact B2117067
  · exact B2117071
  · exact B2117075
  · exact B2117079
  · exact B2117083
  · exact B2117087
  · exact B2117091
  · exact B2117095
  · exact B2117099
  · exact B2117103
  · exact B2117107
  · exact B2117111
  · exact B2117115
  · exact B2117119
  · exact B2117123
  · exact B2117127
  · exact B2117131
  · exact B2117135
  · exact B2117139
  · exact B2117143
  · exact B2117147
  · exact B2117151
  · exact B2117155
  · exact B2117159
  · exact B2117163
  · exact B2117167
  · exact B2117171
  · exact B2117175
  · exact B2117179
  · exact B2117183
  · exact B2117187
  · exact B2117191
  · exact B2117195
  · exact B2117199
  · exact B2117203
  · exact B2117207
  · exact B2117211
  · exact B2117215
  · exact B2117219
  · exact B2117223
  · exact B2117227
  · exact B2117231
  · exact B2117235
  · exact B2117239
  · exact B2117243
  · exact B2117247
  · exact B2117251
  · exact B2117255
  · exact B2117259
  · exact B2117263
  · exact B2117267
  · exact B2117271
  · exact B2117275
  · exact B2117279
  · exact B2117283
  · exact B2117287
  · exact B2117291
  · exact B2117295
  · exact B2117299
  · exact B2117303
  · exact B2117307
  · exact B2117311
  · exact B2117315
  · exact B2117319
  · exact B2117323
  · exact B2117327
  · exact B2117331
  · exact B2117335
  · exact B2117339
  · exact B2117343
  · exact B2117347
  · exact B2117351
  · exact B2117355
  · exact B2117359
  · exact B2117363
  · exact B2117367
  · exact B2117371
  · exact B2117375
  · exact B2117379
  · exact B2117383
  · exact B2117387
  · exact B2117391
  · exact B2117395
  · exact B2117399
  · exact B2117403
  · exact B2117407
  · exact B2117411
  · exact B2117415
  · exact B2117419
  · exact B2117423
  · exact B2117427
  · exact B2117431
  · exact B2117435
theorem solution (m : ℕ) (hlo : 2115435 ≤ m) (hhi : m ≤ 2117435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 528858 ≤ j := by omega
    have hj2 : j ≤ 529358 := by omega
    have hb : Blo 2115435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
