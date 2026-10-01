-- Prove2me | solution 1 for syracuse_descends_range_2191435_2193435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:07.823665+00:00
-- url     : https://prove2.me/submissions/dca2c706-9e81-4d13-b894-676e41ed8b49

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

theorem B2465365 : Blo 2191435 2465365 := bbase (se 8 (by rfl) ⟨14445, by rfl⟩ : syracuseStep 2465365 = 28891) (by norm_num)
theorem B3287153 : Blo 2191435 3287153 := bstep (se 2 (by rfl) ⟨1232682, by rfl⟩ : syracuseStep 3287153 = 2465365) B2465365
theorem B2191435 : Blo 2191435 2191435 := bstep (se 1 (by rfl) ⟨1643576, by rfl⟩ : syracuseStep 2191435 = 3287153) B3287153
theorem B2773541 : Blo 2191435 2773541 := bbase (se 4 (by rfl) ⟨260019, by rfl⟩ : syracuseStep 2773541 = 520039) (by norm_num)
theorem B7396109 : Blo 2191435 7396109 := bstep (se 3 (by rfl) ⟨1386770, by rfl⟩ : syracuseStep 7396109 = 2773541) B2773541
theorem B4930739 : Blo 2191435 4930739 := bstep (se 1 (by rfl) ⟨3698054, by rfl⟩ : syracuseStep 4930739 = 7396109) B7396109
theorem B3287159 : Blo 2191435 3287159 := bstep (se 1 (by rfl) ⟨2465369, by rfl⟩ : syracuseStep 3287159 = 4930739) B4930739
theorem B2191439 : Blo 2191435 2191439 := bstep (se 1 (by rfl) ⟨1643579, by rfl⟩ : syracuseStep 2191439 = 3287159) B3287159
theorem B3287165 : Blo 2191435 3287165 := bbase (se 3 (by rfl) ⟨616343, by rfl⟩ : syracuseStep 3287165 = 1232687) (by norm_num)
theorem B2191443 : Blo 2191435 2191443 := bstep (se 1 (by rfl) ⟨1643582, by rfl⟩ : syracuseStep 2191443 = 3287165) B3287165
theorem B4930757 : Blo 2191435 4930757 := bbase (se 4 (by rfl) ⟨462258, by rfl⟩ : syracuseStep 4930757 = 924517) (by norm_num)
theorem B3287171 : Blo 2191435 3287171 := bstep (se 1 (by rfl) ⟨2465378, by rfl⟩ : syracuseStep 3287171 = 4930757) B4930757
theorem B2191447 : Blo 2191435 2191447 := bstep (se 1 (by rfl) ⟨1643585, by rfl⟩ : syracuseStep 2191447 = 3287171) B3287171
theorem B3949069 : Blo 2191435 3949069 := bbase (se 3 (by rfl) ⟨740450, by rfl⟩ : syracuseStep 3949069 = 1480901) (by norm_num)
theorem B5265425 : Blo 2191435 5265425 := bstep (se 2 (by rfl) ⟨1974534, by rfl⟩ : syracuseStep 5265425 = 3949069) B3949069
theorem B14041133 : Blo 2191435 14041133 := bstep (se 3 (by rfl) ⟨2632712, by rfl⟩ : syracuseStep 14041133 = 5265425) B5265425
theorem B9360755 : Blo 2191435 9360755 := bstep (se 1 (by rfl) ⟨7020566, by rfl⟩ : syracuseStep 9360755 = 14041133) B14041133
theorem B6240503 : Blo 2191435 6240503 := bstep (se 1 (by rfl) ⟨4680377, by rfl⟩ : syracuseStep 6240503 = 9360755) B9360755
theorem B4160335 : Blo 2191435 4160335 := bstep (se 1 (by rfl) ⟨3120251, by rfl⟩ : syracuseStep 4160335 = 6240503) B6240503
theorem B5547113 : Blo 2191435 5547113 := bstep (se 2 (by rfl) ⟨2080167, by rfl⟩ : syracuseStep 5547113 = 4160335) B4160335
theorem B3698075 : Blo 2191435 3698075 := bstep (se 1 (by rfl) ⟨2773556, by rfl⟩ : syracuseStep 3698075 = 5547113) B5547113
theorem B2465383 : Blo 2191435 2465383 := bstep (se 1 (by rfl) ⟨1849037, by rfl⟩ : syracuseStep 2465383 = 3698075) B3698075
theorem B3287177 : Blo 2191435 3287177 := bstep (se 2 (by rfl) ⟨1232691, by rfl⟩ : syracuseStep 3287177 = 2465383) B2465383
theorem B2191451 : Blo 2191435 2191451 := bstep (se 1 (by rfl) ⟨1643588, by rfl⟩ : syracuseStep 2191451 = 3287177) B3287177
theorem B11094245 : Blo 2191435 11094245 := bbase (se 4 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 11094245 = 2080171) (by norm_num)
theorem B7396163 : Blo 2191435 7396163 := bstep (se 1 (by rfl) ⟨5547122, by rfl⟩ : syracuseStep 7396163 = 11094245) B11094245
theorem B4930775 : Blo 2191435 4930775 := bstep (se 1 (by rfl) ⟨3698081, by rfl⟩ : syracuseStep 4930775 = 7396163) B7396163
theorem B3287183 : Blo 2191435 3287183 := bstep (se 1 (by rfl) ⟨2465387, by rfl⟩ : syracuseStep 3287183 = 4930775) B4930775
theorem B2191455 : Blo 2191435 2191455 := bstep (se 1 (by rfl) ⟨1643591, by rfl⟩ : syracuseStep 2191455 = 3287183) B3287183
theorem B3287189 : Blo 2191435 3287189 := bbase (se 6 (by rfl) ⟨77043, by rfl⟩ : syracuseStep 3287189 = 154087) (by norm_num)
theorem B2191459 : Blo 2191435 2191459 := bstep (se 1 (by rfl) ⟨1643594, by rfl⟩ : syracuseStep 2191459 = 3287189) B3287189
theorem B9360805 : Blo 2191435 9360805 := bbase (se 4 (by rfl) ⟨877575, by rfl⟩ : syracuseStep 9360805 = 1755151) (by norm_num)
theorem B12481073 : Blo 2191435 12481073 := bstep (se 2 (by rfl) ⟨4680402, by rfl⟩ : syracuseStep 12481073 = 9360805) B9360805
theorem B8320715 : Blo 2191435 8320715 := bstep (se 1 (by rfl) ⟨6240536, by rfl⟩ : syracuseStep 8320715 = 12481073) B12481073
theorem B5547143 : Blo 2191435 5547143 := bstep (se 1 (by rfl) ⟨4160357, by rfl⟩ : syracuseStep 5547143 = 8320715) B8320715
theorem B3698095 : Blo 2191435 3698095 := bstep (se 1 (by rfl) ⟨2773571, by rfl⟩ : syracuseStep 3698095 = 5547143) B5547143
theorem B4930793 : Blo 2191435 4930793 := bstep (se 2 (by rfl) ⟨1849047, by rfl⟩ : syracuseStep 4930793 = 3698095) B3698095
theorem B3287195 : Blo 2191435 3287195 := bstep (se 1 (by rfl) ⟨2465396, by rfl⟩ : syracuseStep 3287195 = 4930793) B4930793
theorem B2191463 : Blo 2191435 2191463 := bstep (se 1 (by rfl) ⟨1643597, by rfl⟩ : syracuseStep 2191463 = 3287195) B3287195
theorem B2465401 : Blo 2191435 2465401 := bbase (se 2 (by rfl) ⟨924525, by rfl⟩ : syracuseStep 2465401 = 1849051) (by norm_num)
theorem B3287201 : Blo 2191435 3287201 := bstep (se 2 (by rfl) ⟨1232700, by rfl⟩ : syracuseStep 3287201 = 2465401) B2465401
theorem B2191467 : Blo 2191435 2191467 := bstep (se 1 (by rfl) ⟨1643600, by rfl⟩ : syracuseStep 2191467 = 3287201) B3287201
theorem B3748565 : Blo 2191435 3748565 := bbase (se 7 (by rfl) ⟨43928, by rfl⟩ : syracuseStep 3748565 = 87857) (by norm_num)
theorem B2499043 : Blo 2191435 2499043 := bstep (se 1 (by rfl) ⟨1874282, by rfl⟩ : syracuseStep 2499043 = 3748565) B3748565
theorem B3332057 : Blo 2191435 3332057 := bstep (se 2 (by rfl) ⟨1249521, by rfl⟩ : syracuseStep 3332057 = 2499043) B2499043
theorem B8885485 : Blo 2191435 8885485 := bstep (se 3 (by rfl) ⟨1666028, by rfl⟩ : syracuseStep 8885485 = 3332057) B3332057
theorem B11847313 : Blo 2191435 11847313 := bstep (se 2 (by rfl) ⟨4442742, by rfl⟩ : syracuseStep 11847313 = 8885485) B8885485
theorem B15796417 : Blo 2191435 15796417 := bstep (se 2 (by rfl) ⟨5923656, by rfl⟩ : syracuseStep 15796417 = 11847313) B11847313
theorem B21061889 : Blo 2191435 21061889 := bstep (se 2 (by rfl) ⟨7898208, by rfl⟩ : syracuseStep 21061889 = 15796417) B15796417
theorem B14041259 : Blo 2191435 14041259 := bstep (se 1 (by rfl) ⟨10530944, by rfl⟩ : syracuseStep 14041259 = 21061889) B21061889
theorem B9360839 : Blo 2191435 9360839 := bstep (se 1 (by rfl) ⟨7020629, by rfl⟩ : syracuseStep 9360839 = 14041259) B14041259
theorem B6240559 : Blo 2191435 6240559 := bstep (se 1 (by rfl) ⟨4680419, by rfl⟩ : syracuseStep 6240559 = 9360839) B9360839
theorem B8320745 : Blo 2191435 8320745 := bstep (se 2 (by rfl) ⟨3120279, by rfl⟩ : syracuseStep 8320745 = 6240559) B6240559
theorem B5547163 : Blo 2191435 5547163 := bstep (se 1 (by rfl) ⟨4160372, by rfl⟩ : syracuseStep 5547163 = 8320745) B8320745
theorem B7396217 : Blo 2191435 7396217 := bstep (se 2 (by rfl) ⟨2773581, by rfl⟩ : syracuseStep 7396217 = 5547163) B5547163
theorem B4930811 : Blo 2191435 4930811 := bstep (se 1 (by rfl) ⟨3698108, by rfl⟩ : syracuseStep 4930811 = 7396217) B7396217
theorem B3287207 : Blo 2191435 3287207 := bstep (se 1 (by rfl) ⟨2465405, by rfl⟩ : syracuseStep 3287207 = 4930811) B4930811
theorem B2191471 : Blo 2191435 2191471 := bstep (se 1 (by rfl) ⟨1643603, by rfl⟩ : syracuseStep 2191471 = 3287207) B3287207
theorem B3287213 : Blo 2191435 3287213 := bbase (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) (by norm_num)
theorem B2191475 : Blo 2191435 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B4930829 : Blo 2191435 4930829 := bbase (se 3 (by rfl) ⟨924530, by rfl⟩ : syracuseStep 4930829 = 1849061) (by norm_num)
theorem B3287219 : Blo 2191435 3287219 := bstep (se 1 (by rfl) ⟨2465414, by rfl⟩ : syracuseStep 3287219 = 4930829) B4930829
theorem B2191479 : Blo 2191435 2191479 := bstep (se 1 (by rfl) ⟨1643609, by rfl⟩ : syracuseStep 2191479 = 3287219) B3287219
theorem B2773597 : Blo 2191435 2773597 := bbase (se 3 (by rfl) ⟨520049, by rfl⟩ : syracuseStep 2773597 = 1040099) (by norm_num)
theorem B3698129 : Blo 2191435 3698129 := bstep (se 2 (by rfl) ⟨1386798, by rfl⟩ : syracuseStep 3698129 = 2773597) B2773597
theorem B2465419 : Blo 2191435 2465419 := bstep (se 1 (by rfl) ⟨1849064, by rfl⟩ : syracuseStep 2465419 = 3698129) B3698129
theorem B3287225 : Blo 2191435 3287225 := bstep (se 2 (by rfl) ⟨1232709, by rfl⟩ : syracuseStep 3287225 = 2465419) B2465419
theorem B2191483 : Blo 2191435 2191483 := bstep (se 1 (by rfl) ⟨1643612, by rfl⟩ : syracuseStep 2191483 = 3287225) B3287225
theorem B18721813 : Blo 2191435 18721813 := bbase (se 6 (by rfl) ⟨438792, by rfl⟩ : syracuseStep 18721813 = 877585) (by norm_num)
theorem B24962417 : Blo 2191435 24962417 := bstep (se 2 (by rfl) ⟨9360906, by rfl⟩ : syracuseStep 24962417 = 18721813) B18721813
theorem B16641611 : Blo 2191435 16641611 := bstep (se 1 (by rfl) ⟨12481208, by rfl⟩ : syracuseStep 16641611 = 24962417) B24962417
theorem B11094407 : Blo 2191435 11094407 := bstep (se 1 (by rfl) ⟨8320805, by rfl⟩ : syracuseStep 11094407 = 16641611) B16641611
theorem B7396271 : Blo 2191435 7396271 := bstep (se 1 (by rfl) ⟨5547203, by rfl⟩ : syracuseStep 7396271 = 11094407) B11094407
theorem B4930847 : Blo 2191435 4930847 := bstep (se 1 (by rfl) ⟨3698135, by rfl⟩ : syracuseStep 4930847 = 7396271) B7396271
theorem B3287231 : Blo 2191435 3287231 := bstep (se 1 (by rfl) ⟨2465423, by rfl⟩ : syracuseStep 3287231 = 4930847) B4930847
theorem B2191487 : Blo 2191435 2191487 := bstep (se 1 (by rfl) ⟨1643615, by rfl⟩ : syracuseStep 2191487 = 3287231) B3287231
theorem B3287237 : Blo 2191435 3287237 := bbase (se 4 (by rfl) ⟨308178, by rfl⟩ : syracuseStep 3287237 = 616357) (by norm_num)
theorem B2191491 : Blo 2191435 2191491 := bstep (se 1 (by rfl) ⟨1643618, by rfl⟩ : syracuseStep 2191491 = 3287237) B3287237
theorem B3698149 : Blo 2191435 3698149 := bbase (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) (by norm_num)
theorem B4930865 : Blo 2191435 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B3287243 : Blo 2191435 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B2191495 : Blo 2191435 2191495 := bstep (se 1 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 2191495 = 3287243) B3287243
theorem B2465437 : Blo 2191435 2465437 := bbase (se 3 (by rfl) ⟨462269, by rfl⟩ : syracuseStep 2465437 = 924539) (by norm_num)
theorem B3287249 : Blo 2191435 3287249 := bstep (se 2 (by rfl) ⟨1232718, by rfl⟩ : syracuseStep 3287249 = 2465437) B2465437
theorem B2191499 : Blo 2191435 2191499 := bstep (se 1 (by rfl) ⟨1643624, by rfl⟩ : syracuseStep 2191499 = 3287249) B3287249
theorem B7396325 : Blo 2191435 7396325 := bbase (se 4 (by rfl) ⟨693405, by rfl⟩ : syracuseStep 7396325 = 1386811) (by norm_num)
theorem B4930883 : Blo 2191435 4930883 := bstep (se 1 (by rfl) ⟨3698162, by rfl⟩ : syracuseStep 4930883 = 7396325) B7396325
theorem B3287255 : Blo 2191435 3287255 := bstep (se 1 (by rfl) ⟨2465441, by rfl⟩ : syracuseStep 3287255 = 4930883) B4930883
theorem B2191503 : Blo 2191435 2191503 := bstep (se 1 (by rfl) ⟨1643627, by rfl⟩ : syracuseStep 2191503 = 3287255) B3287255
theorem B3287261 : Blo 2191435 3287261 := bbase (se 3 (by rfl) ⟨616361, by rfl⟩ : syracuseStep 3287261 = 1232723) (by norm_num)
theorem B2191507 : Blo 2191435 2191507 := bstep (se 1 (by rfl) ⟨1643630, by rfl⟩ : syracuseStep 2191507 = 3287261) B3287261
theorem B4930901 : Blo 2191435 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B3287267 : Blo 2191435 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B2191511 : Blo 2191435 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B2340257 : Blo 2191435 2340257 := bbase (se 2 (by rfl) ⟨877596, by rfl⟩ : syracuseStep 2340257 = 1755193) (by norm_num)
theorem B6240685 : Blo 2191435 6240685 := bstep (se 3 (by rfl) ⟨1170128, by rfl⟩ : syracuseStep 6240685 = 2340257) B2340257
theorem B8320913 : Blo 2191435 8320913 := bstep (se 2 (by rfl) ⟨3120342, by rfl⟩ : syracuseStep 8320913 = 6240685) B6240685
theorem B5547275 : Blo 2191435 5547275 := bstep (se 1 (by rfl) ⟨4160456, by rfl⟩ : syracuseStep 5547275 = 8320913) B8320913
theorem B3698183 : Blo 2191435 3698183 := bstep (se 1 (by rfl) ⟨2773637, by rfl⟩ : syracuseStep 3698183 = 5547275) B5547275
theorem B2465455 : Blo 2191435 2465455 := bstep (se 1 (by rfl) ⟨1849091, by rfl⟩ : syracuseStep 2465455 = 3698183) B3698183
theorem B3287273 : Blo 2191435 3287273 := bstep (se 2 (by rfl) ⟨1232727, by rfl⟩ : syracuseStep 3287273 = 2465455) B2465455
theorem B2191515 : Blo 2191435 2191515 := bstep (se 1 (by rfl) ⟨1643636, by rfl⟩ : syracuseStep 2191515 = 3287273) B3287273
theorem B9996389 : Blo 2191435 9996389 := bbase (se 4 (by rfl) ⟨937161, by rfl⟩ : syracuseStep 9996389 = 1874323) (by norm_num)
theorem B6664259 : Blo 2191435 6664259 := bstep (se 1 (by rfl) ⟨4998194, by rfl⟩ : syracuseStep 6664259 = 9996389) B9996389
theorem B17771357 : Blo 2191435 17771357 := bstep (se 3 (by rfl) ⟨3332129, by rfl⟩ : syracuseStep 17771357 = 6664259) B6664259
theorem B47390285 : Blo 2191435 47390285 := bstep (se 3 (by rfl) ⟨8885678, by rfl⟩ : syracuseStep 47390285 = 17771357) B17771357
theorem B31593523 : Blo 2191435 31593523 := bstep (se 1 (by rfl) ⟨23695142, by rfl⟩ : syracuseStep 31593523 = 47390285) B47390285
theorem B42124697 : Blo 2191435 42124697 := bstep (se 2 (by rfl) ⟨15796761, by rfl⟩ : syracuseStep 42124697 = 31593523) B31593523
theorem B28083131 : Blo 2191435 28083131 := bstep (se 1 (by rfl) ⟨21062348, by rfl⟩ : syracuseStep 28083131 = 42124697) B42124697
theorem B18722087 : Blo 2191435 18722087 := bstep (se 1 (by rfl) ⟨14041565, by rfl⟩ : syracuseStep 18722087 = 28083131) B28083131
theorem B12481391 : Blo 2191435 12481391 := bstep (se 1 (by rfl) ⟨9361043, by rfl⟩ : syracuseStep 12481391 = 18722087) B18722087
theorem B8320927 : Blo 2191435 8320927 := bstep (se 1 (by rfl) ⟨6240695, by rfl⟩ : syracuseStep 8320927 = 12481391) B12481391
theorem B11094569 : Blo 2191435 11094569 := bstep (se 2 (by rfl) ⟨4160463, by rfl⟩ : syracuseStep 11094569 = 8320927) B8320927
theorem B7396379 : Blo 2191435 7396379 := bstep (se 1 (by rfl) ⟨5547284, by rfl⟩ : syracuseStep 7396379 = 11094569) B11094569
theorem B4930919 : Blo 2191435 4930919 := bstep (se 1 (by rfl) ⟨3698189, by rfl⟩ : syracuseStep 4930919 = 7396379) B7396379
theorem B3287279 : Blo 2191435 3287279 := bstep (se 1 (by rfl) ⟨2465459, by rfl⟩ : syracuseStep 3287279 = 4930919) B4930919
theorem B2191519 : Blo 2191435 2191519 := bstep (se 1 (by rfl) ⟨1643639, by rfl⟩ : syracuseStep 2191519 = 3287279) B3287279
theorem B3287285 : Blo 2191435 3287285 := bbase (se 5 (by rfl) ⟨154091, by rfl⟩ : syracuseStep 3287285 = 308183) (by norm_num)
theorem B2191523 : Blo 2191435 2191523 := bstep (se 1 (by rfl) ⟨1643642, by rfl⟩ : syracuseStep 2191523 = 3287285) B3287285
theorem B3748661 : Blo 2191435 3748661 := bbase (se 5 (by rfl) ⟨175718, by rfl⟩ : syracuseStep 3748661 = 351437) (by norm_num)
theorem B2499107 : Blo 2191435 2499107 := bstep (se 1 (by rfl) ⟨1874330, by rfl⟩ : syracuseStep 2499107 = 3748661) B3748661
theorem B6664285 : Blo 2191435 6664285 := bstep (se 3 (by rfl) ⟨1249553, by rfl⟩ : syracuseStep 6664285 = 2499107) B2499107
theorem B8885713 : Blo 2191435 8885713 := bstep (se 2 (by rfl) ⟨3332142, by rfl⟩ : syracuseStep 8885713 = 6664285) B6664285
theorem B11847617 : Blo 2191435 11847617 := bstep (se 2 (by rfl) ⟨4442856, by rfl⟩ : syracuseStep 11847617 = 8885713) B8885713
theorem B7898411 : Blo 2191435 7898411 := bstep (se 1 (by rfl) ⟨5923808, by rfl⟩ : syracuseStep 7898411 = 11847617) B11847617
theorem B21062429 : Blo 2191435 21062429 := bstep (se 3 (by rfl) ⟨3949205, by rfl⟩ : syracuseStep 21062429 = 7898411) B7898411
theorem B14041619 : Blo 2191435 14041619 := bstep (se 1 (by rfl) ⟨10531214, by rfl⟩ : syracuseStep 14041619 = 21062429) B21062429
theorem B9361079 : Blo 2191435 9361079 := bstep (se 1 (by rfl) ⟨7020809, by rfl⟩ : syracuseStep 9361079 = 14041619) B14041619
theorem B6240719 : Blo 2191435 6240719 := bstep (se 1 (by rfl) ⟨4680539, by rfl⟩ : syracuseStep 6240719 = 9361079) B9361079
theorem B4160479 : Blo 2191435 4160479 := bstep (se 1 (by rfl) ⟨3120359, by rfl⟩ : syracuseStep 4160479 = 6240719) B6240719
theorem B5547305 : Blo 2191435 5547305 := bstep (se 2 (by rfl) ⟨2080239, by rfl⟩ : syracuseStep 5547305 = 4160479) B4160479
theorem B3698203 : Blo 2191435 3698203 := bstep (se 1 (by rfl) ⟨2773652, by rfl⟩ : syracuseStep 3698203 = 5547305) B5547305
theorem B4930937 : Blo 2191435 4930937 := bstep (se 2 (by rfl) ⟨1849101, by rfl⟩ : syracuseStep 4930937 = 3698203) B3698203
theorem B3287291 : Blo 2191435 3287291 := bstep (se 1 (by rfl) ⟨2465468, by rfl⟩ : syracuseStep 3287291 = 4930937) B4930937
theorem B2191527 : Blo 2191435 2191527 := bstep (se 1 (by rfl) ⟨1643645, by rfl⟩ : syracuseStep 2191527 = 3287291) B3287291
theorem B2465473 : Blo 2191435 2465473 := bbase (se 2 (by rfl) ⟨924552, by rfl⟩ : syracuseStep 2465473 = 1849105) (by norm_num)
theorem B3287297 : Blo 2191435 3287297 := bstep (se 2 (by rfl) ⟨1232736, by rfl⟩ : syracuseStep 3287297 = 2465473) B2465473
theorem B2191531 : Blo 2191435 2191531 := bstep (se 1 (by rfl) ⟨1643648, by rfl⟩ : syracuseStep 2191531 = 3287297) B3287297
theorem B5547325 : Blo 2191435 5547325 := bbase (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) (by norm_num)
theorem B7396433 : Blo 2191435 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B4930955 : Blo 2191435 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B3287303 : Blo 2191435 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B2191535 : Blo 2191435 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B3287309 : Blo 2191435 3287309 := bbase (se 3 (by rfl) ⟨616370, by rfl⟩ : syracuseStep 3287309 = 1232741) (by norm_num)
theorem B2191539 : Blo 2191435 2191539 := bstep (se 1 (by rfl) ⟨1643654, by rfl⟩ : syracuseStep 2191539 = 3287309) B3287309
theorem B4930973 : Blo 2191435 4930973 := bbase (se 3 (by rfl) ⟨924557, by rfl⟩ : syracuseStep 4930973 = 1849115) (by norm_num)
theorem B3287315 : Blo 2191435 3287315 := bstep (se 1 (by rfl) ⟨2465486, by rfl⟩ : syracuseStep 3287315 = 4930973) B4930973
theorem B2191543 : Blo 2191435 2191543 := bstep (se 1 (by rfl) ⟨1643657, by rfl⟩ : syracuseStep 2191543 = 3287315) B3287315
theorem B3698237 : Blo 2191435 3698237 := bbase (se 3 (by rfl) ⟨693419, by rfl⟩ : syracuseStep 3698237 = 1386839) (by norm_num)
theorem B2465491 : Blo 2191435 2465491 := bstep (se 1 (by rfl) ⟨1849118, by rfl⟩ : syracuseStep 2465491 = 3698237) B3698237
theorem B3287321 : Blo 2191435 3287321 := bstep (se 2 (by rfl) ⟨1232745, by rfl⟩ : syracuseStep 3287321 = 2465491) B2465491
theorem B2191547 : Blo 2191435 2191547 := bstep (se 1 (by rfl) ⟨1643660, by rfl⟩ : syracuseStep 2191547 = 3287321) B3287321
theorem B2221453 : Blo 2191435 2221453 := bbase (se 3 (by rfl) ⟨416522, by rfl⟩ : syracuseStep 2221453 = 833045) (by norm_num)
theorem B2961937 : Blo 2191435 2961937 := bstep (se 2 (by rfl) ⟨1110726, by rfl⟩ : syracuseStep 2961937 = 2221453) B2221453
theorem B3949249 : Blo 2191435 3949249 := bstep (se 2 (by rfl) ⟨1480968, by rfl⟩ : syracuseStep 3949249 = 2961937) B2961937
theorem B5265665 : Blo 2191435 5265665 := bstep (se 2 (by rfl) ⟨1974624, by rfl⟩ : syracuseStep 5265665 = 3949249) B3949249
theorem B3510443 : Blo 2191435 3510443 := bstep (se 1 (by rfl) ⟨2632832, by rfl⟩ : syracuseStep 3510443 = 5265665) B5265665
theorem B2340295 : Blo 2191435 2340295 := bstep (se 1 (by rfl) ⟨1755221, by rfl⟩ : syracuseStep 2340295 = 3510443) B3510443
theorem B12481573 : Blo 2191435 12481573 := bstep (se 4 (by rfl) ⟨1170147, by rfl⟩ : syracuseStep 12481573 = 2340295) B2340295
theorem B16642097 : Blo 2191435 16642097 := bstep (se 2 (by rfl) ⟨6240786, by rfl⟩ : syracuseStep 16642097 = 12481573) B12481573
theorem B11094731 : Blo 2191435 11094731 := bstep (se 1 (by rfl) ⟨8321048, by rfl⟩ : syracuseStep 11094731 = 16642097) B16642097
theorem B7396487 : Blo 2191435 7396487 := bstep (se 1 (by rfl) ⟨5547365, by rfl⟩ : syracuseStep 7396487 = 11094731) B11094731
theorem B4930991 : Blo 2191435 4930991 := bstep (se 1 (by rfl) ⟨3698243, by rfl⟩ : syracuseStep 4930991 = 7396487) B7396487
theorem B3287327 : Blo 2191435 3287327 := bstep (se 1 (by rfl) ⟨2465495, by rfl⟩ : syracuseStep 3287327 = 4930991) B4930991
theorem B2191551 : Blo 2191435 2191551 := bstep (se 1 (by rfl) ⟨1643663, by rfl⟩ : syracuseStep 2191551 = 3287327) B3287327
theorem B3287333 : Blo 2191435 3287333 := bbase (se 4 (by rfl) ⟨308187, by rfl⟩ : syracuseStep 3287333 = 616375) (by norm_num)
theorem B2191555 : Blo 2191435 2191555 := bstep (se 1 (by rfl) ⟨1643666, by rfl⟩ : syracuseStep 2191555 = 3287333) B3287333
theorem B2773693 : Blo 2191435 2773693 := bbase (se 3 (by rfl) ⟨520067, by rfl⟩ : syracuseStep 2773693 = 1040135) (by norm_num)
theorem B3698257 : Blo 2191435 3698257 := bstep (se 2 (by rfl) ⟨1386846, by rfl⟩ : syracuseStep 3698257 = 2773693) B2773693
theorem B4931009 : Blo 2191435 4931009 := bstep (se 2 (by rfl) ⟨1849128, by rfl⟩ : syracuseStep 4931009 = 3698257) B3698257
theorem B3287339 : Blo 2191435 3287339 := bstep (se 1 (by rfl) ⟨2465504, by rfl⟩ : syracuseStep 3287339 = 4931009) B4931009
theorem B2191559 : Blo 2191435 2191559 := bstep (se 1 (by rfl) ⟨1643669, by rfl⟩ : syracuseStep 2191559 = 3287339) B3287339
theorem B2465509 : Blo 2191435 2465509 := bbase (se 4 (by rfl) ⟨231141, by rfl⟩ : syracuseStep 2465509 = 462283) (by norm_num)
theorem B3287345 : Blo 2191435 3287345 := bstep (se 2 (by rfl) ⟨1232754, by rfl⟩ : syracuseStep 3287345 = 2465509) B2465509
theorem B2191563 : Blo 2191435 2191563 := bstep (se 1 (by rfl) ⟨1643672, by rfl⟩ : syracuseStep 2191563 = 3287345) B3287345
theorem B3510469 : Blo 2191435 3510469 := bbase (se 4 (by rfl) ⟨329106, by rfl⟩ : syracuseStep 3510469 = 658213) (by norm_num)
theorem B4680625 : Blo 2191435 4680625 := bstep (se 2 (by rfl) ⟨1755234, by rfl⟩ : syracuseStep 4680625 = 3510469) B3510469
theorem B6240833 : Blo 2191435 6240833 := bstep (se 2 (by rfl) ⟨2340312, by rfl⟩ : syracuseStep 6240833 = 4680625) B4680625
theorem B4160555 : Blo 2191435 4160555 := bstep (se 1 (by rfl) ⟨3120416, by rfl⟩ : syracuseStep 4160555 = 6240833) B6240833
theorem B2773703 : Blo 2191435 2773703 := bstep (se 1 (by rfl) ⟨2080277, by rfl⟩ : syracuseStep 2773703 = 4160555) B4160555
theorem B7396541 : Blo 2191435 7396541 := bstep (se 3 (by rfl) ⟨1386851, by rfl⟩ : syracuseStep 7396541 = 2773703) B2773703
theorem B4931027 : Blo 2191435 4931027 := bstep (se 1 (by rfl) ⟨3698270, by rfl⟩ : syracuseStep 4931027 = 7396541) B7396541
theorem B3287351 : Blo 2191435 3287351 := bstep (se 1 (by rfl) ⟨2465513, by rfl⟩ : syracuseStep 3287351 = 4931027) B4931027
theorem B2191567 : Blo 2191435 2191567 := bstep (se 1 (by rfl) ⟨1643675, by rfl⟩ : syracuseStep 2191567 = 3287351) B3287351
theorem B3287357 : Blo 2191435 3287357 := bbase (se 3 (by rfl) ⟨616379, by rfl⟩ : syracuseStep 3287357 = 1232759) (by norm_num)
theorem B2191571 : Blo 2191435 2191571 := bstep (se 1 (by rfl) ⟨1643678, by rfl⟩ : syracuseStep 2191571 = 3287357) B3287357
theorem B4931045 : Blo 2191435 4931045 := bbase (se 4 (by rfl) ⟨462285, by rfl⟩ : syracuseStep 4931045 = 924571) (by norm_num)
theorem B3287363 : Blo 2191435 3287363 := bstep (se 1 (by rfl) ⟨2465522, by rfl⟩ : syracuseStep 3287363 = 4931045) B4931045
theorem B2191575 : Blo 2191435 2191575 := bstep (se 1 (by rfl) ⟨1643681, by rfl⟩ : syracuseStep 2191575 = 3287363) B3287363
theorem B5547437 : Blo 2191435 5547437 := bbase (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) (by norm_num)
theorem B3698291 : Blo 2191435 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B2465527 : Blo 2191435 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B3287369 : Blo 2191435 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B2191579 : Blo 2191435 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B2372261 : Blo 2191435 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B6326029 : Blo 2191435 6326029 := bstep (se 3 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 6326029 = 2372261) B2372261
theorem B8434705 : Blo 2191435 8434705 := bstep (se 2 (by rfl) ⟨3163014, by rfl⟩ : syracuseStep 8434705 = 6326029) B6326029
theorem B11246273 : Blo 2191435 11246273 := bstep (se 2 (by rfl) ⟨4217352, by rfl⟩ : syracuseStep 11246273 = 8434705) B8434705
theorem B7497515 : Blo 2191435 7497515 := bstep (se 1 (by rfl) ⟨5623136, by rfl⟩ : syracuseStep 7497515 = 11246273) B11246273
theorem B4998343 : Blo 2191435 4998343 := bstep (se 1 (by rfl) ⟨3748757, by rfl⟩ : syracuseStep 4998343 = 7497515) B7497515
theorem B6664457 : Blo 2191435 6664457 := bstep (se 2 (by rfl) ⟨2499171, by rfl⟩ : syracuseStep 6664457 = 4998343) B4998343
theorem B4442971 : Blo 2191435 4442971 := bstep (se 1 (by rfl) ⟨3332228, by rfl⟩ : syracuseStep 4442971 = 6664457) B6664457
theorem B5923961 : Blo 2191435 5923961 := bstep (se 2 (by rfl) ⟨2221485, by rfl⟩ : syracuseStep 5923961 = 4442971) B4442971
theorem B3949307 : Blo 2191435 3949307 := bstep (se 1 (by rfl) ⟨2961980, by rfl⟩ : syracuseStep 3949307 = 5923961) B5923961
theorem B2632871 : Blo 2191435 2632871 := bstep (se 1 (by rfl) ⟨1974653, by rfl⟩ : syracuseStep 2632871 = 3949307) B3949307
theorem B7020989 : Blo 2191435 7020989 := bstep (se 3 (by rfl) ⟨1316435, by rfl⟩ : syracuseStep 7020989 = 2632871) B2632871
theorem B4680659 : Blo 2191435 4680659 := bstep (se 1 (by rfl) ⟨3510494, by rfl⟩ : syracuseStep 4680659 = 7020989) B7020989
theorem B3120439 : Blo 2191435 3120439 := bstep (se 1 (by rfl) ⟨2340329, by rfl⟩ : syracuseStep 3120439 = 4680659) B4680659
theorem B4160585 : Blo 2191435 4160585 := bstep (se 2 (by rfl) ⟨1560219, by rfl⟩ : syracuseStep 4160585 = 3120439) B3120439
theorem B11094893 : Blo 2191435 11094893 := bstep (se 3 (by rfl) ⟨2080292, by rfl⟩ : syracuseStep 11094893 = 4160585) B4160585
theorem B7396595 : Blo 2191435 7396595 := bstep (se 1 (by rfl) ⟨5547446, by rfl⟩ : syracuseStep 7396595 = 11094893) B11094893
theorem B4931063 : Blo 2191435 4931063 := bstep (se 1 (by rfl) ⟨3698297, by rfl⟩ : syracuseStep 4931063 = 7396595) B7396595
theorem B3287375 : Blo 2191435 3287375 := bstep (se 1 (by rfl) ⟨2465531, by rfl⟩ : syracuseStep 3287375 = 4931063) B4931063
theorem B2191583 : Blo 2191435 2191583 := bstep (se 1 (by rfl) ⟨1643687, by rfl⟩ : syracuseStep 2191583 = 3287375) B3287375
theorem B3287381 : Blo 2191435 3287381 := bbase (se 10 (by rfl) ⟨4815, by rfl⟩ : syracuseStep 3287381 = 9631) (by norm_num)
theorem B2191587 : Blo 2191435 2191587 := bstep (se 1 (by rfl) ⟨1643690, by rfl⟩ : syracuseStep 2191587 = 3287381) B3287381
theorem B6240901 : Blo 2191435 6240901 := bbase (se 4 (by rfl) ⟨585084, by rfl⟩ : syracuseStep 6240901 = 1170169) (by norm_num)
theorem B8321201 : Blo 2191435 8321201 := bstep (se 2 (by rfl) ⟨3120450, by rfl⟩ : syracuseStep 8321201 = 6240901) B6240901
theorem B5547467 : Blo 2191435 5547467 := bstep (se 1 (by rfl) ⟨4160600, by rfl⟩ : syracuseStep 5547467 = 8321201) B8321201
theorem B3698311 : Blo 2191435 3698311 := bstep (se 1 (by rfl) ⟨2773733, by rfl⟩ : syracuseStep 3698311 = 5547467) B5547467
theorem B4931081 : Blo 2191435 4931081 := bstep (se 2 (by rfl) ⟨1849155, by rfl⟩ : syracuseStep 4931081 = 3698311) B3698311
theorem B3287387 : Blo 2191435 3287387 := bstep (se 1 (by rfl) ⟨2465540, by rfl⟩ : syracuseStep 3287387 = 4931081) B4931081
theorem B2191591 : Blo 2191435 2191591 := bstep (se 1 (by rfl) ⟨1643693, by rfl⟩ : syracuseStep 2191591 = 3287387) B3287387
theorem B2465545 : Blo 2191435 2465545 := bbase (se 2 (by rfl) ⟨924579, by rfl⟩ : syracuseStep 2465545 = 1849159) (by norm_num)
theorem B3287393 : Blo 2191435 3287393 := bstep (se 2 (by rfl) ⟨1232772, by rfl⟩ : syracuseStep 3287393 = 2465545) B2465545
theorem B2191595 : Blo 2191435 2191595 := bstep (se 1 (by rfl) ⟨1643696, by rfl⟩ : syracuseStep 2191595 = 3287393) B3287393
theorem B12009653 : Blo 2191435 12009653 := bbase (se 5 (by rfl) ⟨562952, by rfl⟩ : syracuseStep 12009653 = 1125905) (by norm_num)
theorem B8006435 : Blo 2191435 8006435 := bstep (se 1 (by rfl) ⟨6004826, by rfl⟩ : syracuseStep 8006435 = 12009653) B12009653
theorem B5337623 : Blo 2191435 5337623 := bstep (se 1 (by rfl) ⟨4003217, by rfl⟩ : syracuseStep 5337623 = 8006435) B8006435
theorem B14233661 : Blo 2191435 14233661 := bstep (se 3 (by rfl) ⟨2668811, by rfl⟩ : syracuseStep 14233661 = 5337623) B5337623
theorem B9489107 : Blo 2191435 9489107 := bstep (se 1 (by rfl) ⟨7116830, by rfl⟩ : syracuseStep 9489107 = 14233661) B14233661
theorem B25304285 : Blo 2191435 25304285 := bstep (se 3 (by rfl) ⟨4744553, by rfl⟩ : syracuseStep 25304285 = 9489107) B9489107
theorem B67478093 : Blo 2191435 67478093 := bstep (se 3 (by rfl) ⟨12652142, by rfl⟩ : syracuseStep 67478093 = 25304285) B25304285
theorem B44985395 : Blo 2191435 44985395 := bstep (se 1 (by rfl) ⟨33739046, by rfl⟩ : syracuseStep 44985395 = 67478093) B67478093
theorem B29990263 : Blo 2191435 29990263 := bstep (se 1 (by rfl) ⟨22492697, by rfl⟩ : syracuseStep 29990263 = 44985395) B44985395
theorem B39987017 : Blo 2191435 39987017 := bstep (se 2 (by rfl) ⟨14995131, by rfl⟩ : syracuseStep 39987017 = 29990263) B29990263
theorem B26658011 : Blo 2191435 26658011 := bstep (se 1 (by rfl) ⟨19993508, by rfl⟩ : syracuseStep 26658011 = 39987017) B39987017
theorem B17772007 : Blo 2191435 17772007 := bstep (se 1 (by rfl) ⟨13329005, by rfl⟩ : syracuseStep 17772007 = 26658011) B26658011
theorem B23696009 : Blo 2191435 23696009 := bstep (se 2 (by rfl) ⟨8886003, by rfl⟩ : syracuseStep 23696009 = 17772007) B17772007
theorem B15797339 : Blo 2191435 15797339 := bstep (se 1 (by rfl) ⟨11848004, by rfl⟩ : syracuseStep 15797339 = 23696009) B23696009
theorem B10531559 : Blo 2191435 10531559 := bstep (se 1 (by rfl) ⟨7898669, by rfl⟩ : syracuseStep 10531559 = 15797339) B15797339
theorem B28084157 : Blo 2191435 28084157 := bstep (se 3 (by rfl) ⟨5265779, by rfl⟩ : syracuseStep 28084157 = 10531559) B10531559
theorem B18722771 : Blo 2191435 18722771 := bstep (se 1 (by rfl) ⟨14042078, by rfl⟩ : syracuseStep 18722771 = 28084157) B28084157
theorem B12481847 : Blo 2191435 12481847 := bstep (se 1 (by rfl) ⟨9361385, by rfl⟩ : syracuseStep 12481847 = 18722771) B18722771
theorem B8321231 : Blo 2191435 8321231 := bstep (se 1 (by rfl) ⟨6240923, by rfl⟩ : syracuseStep 8321231 = 12481847) B12481847
theorem B5547487 : Blo 2191435 5547487 := bstep (se 1 (by rfl) ⟨4160615, by rfl⟩ : syracuseStep 5547487 = 8321231) B8321231
theorem B7396649 : Blo 2191435 7396649 := bstep (se 2 (by rfl) ⟨2773743, by rfl⟩ : syracuseStep 7396649 = 5547487) B5547487
theorem B4931099 : Blo 2191435 4931099 := bstep (se 1 (by rfl) ⟨3698324, by rfl⟩ : syracuseStep 4931099 = 7396649) B7396649
theorem B3287399 : Blo 2191435 3287399 := bstep (se 1 (by rfl) ⟨2465549, by rfl⟩ : syracuseStep 3287399 = 4931099) B4931099
theorem B2191599 : Blo 2191435 2191599 := bstep (se 1 (by rfl) ⟨1643699, by rfl⟩ : syracuseStep 2191599 = 3287399) B3287399
theorem B3287405 : Blo 2191435 3287405 := bbase (se 3 (by rfl) ⟨616388, by rfl⟩ : syracuseStep 3287405 = 1232777) (by norm_num)
theorem B2191603 : Blo 2191435 2191603 := bstep (se 1 (by rfl) ⟨1643702, by rfl⟩ : syracuseStep 2191603 = 3287405) B3287405
theorem B4931117 : Blo 2191435 4931117 := bbase (se 3 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 4931117 = 1849169) (by norm_num)
theorem B3287411 : Blo 2191435 3287411 := bstep (se 1 (by rfl) ⟨2465558, by rfl⟩ : syracuseStep 3287411 = 4931117) B4931117
theorem B2191607 : Blo 2191435 2191607 := bstep (se 1 (by rfl) ⟨1643705, by rfl⟩ : syracuseStep 2191607 = 3287411) B3287411
theorem B4217405 : Blo 2191435 4217405 := bbase (se 3 (by rfl) ⟨790763, by rfl⟩ : syracuseStep 4217405 = 1581527) (by norm_num)
theorem B11246413 : Blo 2191435 11246413 := bstep (se 3 (by rfl) ⟨2108702, by rfl⟩ : syracuseStep 11246413 = 4217405) B4217405
theorem B14995217 : Blo 2191435 14995217 := bstep (se 2 (by rfl) ⟨5623206, by rfl⟩ : syracuseStep 14995217 = 11246413) B11246413
theorem B39987245 : Blo 2191435 39987245 := bstep (se 3 (by rfl) ⟨7497608, by rfl⟩ : syracuseStep 39987245 = 14995217) B14995217
theorem B26658163 : Blo 2191435 26658163 := bstep (se 1 (by rfl) ⟨19993622, by rfl⟩ : syracuseStep 26658163 = 39987245) B39987245
theorem B35544217 : Blo 2191435 35544217 := bstep (se 2 (by rfl) ⟨13329081, by rfl⟩ : syracuseStep 35544217 = 26658163) B26658163
theorem B47392289 : Blo 2191435 47392289 := bstep (se 2 (by rfl) ⟨17772108, by rfl⟩ : syracuseStep 47392289 = 35544217) B35544217
theorem B31594859 : Blo 2191435 31594859 := bstep (se 1 (by rfl) ⟨23696144, by rfl⟩ : syracuseStep 31594859 = 47392289) B47392289
theorem B21063239 : Blo 2191435 21063239 := bstep (se 1 (by rfl) ⟨15797429, by rfl⟩ : syracuseStep 21063239 = 31594859) B31594859
theorem B14042159 : Blo 2191435 14042159 := bstep (se 1 (by rfl) ⟨10531619, by rfl⟩ : syracuseStep 14042159 = 21063239) B21063239
theorem B9361439 : Blo 2191435 9361439 := bstep (se 1 (by rfl) ⟨7021079, by rfl⟩ : syracuseStep 9361439 = 14042159) B14042159
theorem B6240959 : Blo 2191435 6240959 := bstep (se 1 (by rfl) ⟨4680719, by rfl⟩ : syracuseStep 6240959 = 9361439) B9361439
theorem B4160639 : Blo 2191435 4160639 := bstep (se 1 (by rfl) ⟨3120479, by rfl⟩ : syracuseStep 4160639 = 6240959) B6240959
theorem B2773759 : Blo 2191435 2773759 := bstep (se 1 (by rfl) ⟨2080319, by rfl⟩ : syracuseStep 2773759 = 4160639) B4160639
theorem B3698345 : Blo 2191435 3698345 := bstep (se 2 (by rfl) ⟨1386879, by rfl⟩ : syracuseStep 3698345 = 2773759) B2773759
theorem B2465563 : Blo 2191435 2465563 := bstep (se 1 (by rfl) ⟨1849172, by rfl⟩ : syracuseStep 2465563 = 3698345) B3698345
theorem B3287417 : Blo 2191435 3287417 := bstep (se 2 (by rfl) ⟨1232781, by rfl⟩ : syracuseStep 3287417 = 2465563) B2465563
theorem B2191611 : Blo 2191435 2191611 := bstep (se 1 (by rfl) ⟨1643708, by rfl⟩ : syracuseStep 2191611 = 3287417) B3287417
theorem B2632909 : Blo 2191435 2632909 := bbase (se 3 (by rfl) ⟨493670, by rfl⟩ : syracuseStep 2632909 = 987341) (by norm_num)
theorem B3510545 : Blo 2191435 3510545 := bstep (se 2 (by rfl) ⟨1316454, by rfl⟩ : syracuseStep 3510545 = 2632909) B2632909
theorem B37445813 : Blo 2191435 37445813 := bstep (se 5 (by rfl) ⟨1755272, by rfl⟩ : syracuseStep 37445813 = 3510545) B3510545
theorem B24963875 : Blo 2191435 24963875 := bstep (se 1 (by rfl) ⟨18722906, by rfl⟩ : syracuseStep 24963875 = 37445813) B37445813
theorem B16642583 : Blo 2191435 16642583 := bstep (se 1 (by rfl) ⟨12481937, by rfl⟩ : syracuseStep 16642583 = 24963875) B24963875
theorem B11095055 : Blo 2191435 11095055 := bstep (se 1 (by rfl) ⟨8321291, by rfl⟩ : syracuseStep 11095055 = 16642583) B16642583
theorem B7396703 : Blo 2191435 7396703 := bstep (se 1 (by rfl) ⟨5547527, by rfl⟩ : syracuseStep 7396703 = 11095055) B11095055
theorem B4931135 : Blo 2191435 4931135 := bstep (se 1 (by rfl) ⟨3698351, by rfl⟩ : syracuseStep 4931135 = 7396703) B7396703
theorem B3287423 : Blo 2191435 3287423 := bstep (se 1 (by rfl) ⟨2465567, by rfl⟩ : syracuseStep 3287423 = 4931135) B4931135
theorem B2191615 : Blo 2191435 2191615 := bstep (se 1 (by rfl) ⟨1643711, by rfl⟩ : syracuseStep 2191615 = 3287423) B3287423
theorem B3287429 : Blo 2191435 3287429 := bbase (se 4 (by rfl) ⟨308196, by rfl⟩ : syracuseStep 3287429 = 616393) (by norm_num)
theorem B2191619 : Blo 2191435 2191619 := bstep (se 1 (by rfl) ⟨1643714, by rfl⟩ : syracuseStep 2191619 = 3287429) B3287429
theorem B3698365 : Blo 2191435 3698365 := bbase (se 3 (by rfl) ⟨693443, by rfl⟩ : syracuseStep 3698365 = 1386887) (by norm_num)
theorem B4931153 : Blo 2191435 4931153 := bstep (se 2 (by rfl) ⟨1849182, by rfl⟩ : syracuseStep 4931153 = 3698365) B3698365
theorem B3287435 : Blo 2191435 3287435 := bstep (se 1 (by rfl) ⟨2465576, by rfl⟩ : syracuseStep 3287435 = 4931153) B4931153
theorem B2191623 : Blo 2191435 2191623 := bstep (se 1 (by rfl) ⟨1643717, by rfl⟩ : syracuseStep 2191623 = 3287435) B3287435
theorem B2465581 : Blo 2191435 2465581 := bbase (se 3 (by rfl) ⟨462296, by rfl⟩ : syracuseStep 2465581 = 924593) (by norm_num)
theorem B3287441 : Blo 2191435 3287441 := bstep (se 2 (by rfl) ⟨1232790, by rfl⟩ : syracuseStep 3287441 = 2465581) B2465581
theorem B2191627 : Blo 2191435 2191627 := bstep (se 1 (by rfl) ⟨1643720, by rfl⟩ : syracuseStep 2191627 = 3287441) B3287441
theorem B7396757 : Blo 2191435 7396757 := bbase (se 6 (by rfl) ⟨173361, by rfl⟩ : syracuseStep 7396757 = 346723) (by norm_num)
theorem B4931171 : Blo 2191435 4931171 := bstep (se 1 (by rfl) ⟨3698378, by rfl⟩ : syracuseStep 4931171 = 7396757) B7396757
theorem B3287447 : Blo 2191435 3287447 := bstep (se 1 (by rfl) ⟨2465585, by rfl⟩ : syracuseStep 3287447 = 4931171) B4931171
theorem B2191631 : Blo 2191435 2191631 := bstep (se 1 (by rfl) ⟨1643723, by rfl⟩ : syracuseStep 2191631 = 3287447) B3287447
theorem B3287453 : Blo 2191435 3287453 := bbase (se 3 (by rfl) ⟨616397, by rfl⟩ : syracuseStep 3287453 = 1232795) (by norm_num)
theorem B2191635 : Blo 2191435 2191635 := bstep (se 1 (by rfl) ⟨1643726, by rfl⟩ : syracuseStep 2191635 = 3287453) B3287453
theorem B4931189 : Blo 2191435 4931189 := bbase (se 5 (by rfl) ⟨231149, by rfl⟩ : syracuseStep 4931189 = 462299) (by norm_num)
theorem B3287459 : Blo 2191435 3287459 := bstep (se 1 (by rfl) ⟨2465594, by rfl⟩ : syracuseStep 3287459 = 4931189) B4931189
theorem B2191639 : Blo 2191435 2191639 := bstep (se 1 (by rfl) ⟨1643729, by rfl⟩ : syracuseStep 2191639 = 3287459) B3287459
theorem B6004949 : Blo 2191435 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B16013197 : Blo 2191435 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B85403717 : Blo 2191435 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B56935811 : Blo 2191435 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B37957207 : Blo 2191435 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B50609609 : Blo 2191435 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B33739739 : Blo 2191435 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B22493159 : Blo 2191435 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B14995439 : Blo 2191435 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B9996959 : Blo 2191435 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B6664639 : Blo 2191435 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B8886185 : Blo 2191435 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B5924123 : Blo 2191435 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B3949415 : Blo 2191435 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B2632943 : Blo 2191435 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B7021181 : Blo 2191435 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B18723149 : Blo 2191435 18723149 := bstep (se 3 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 18723149 = 7021181) B7021181
theorem B12482099 : Blo 2191435 12482099 := bstep (se 1 (by rfl) ⟨9361574, by rfl⟩ : syracuseStep 12482099 = 18723149) B18723149
theorem B8321399 : Blo 2191435 8321399 := bstep (se 1 (by rfl) ⟨6241049, by rfl⟩ : syracuseStep 8321399 = 12482099) B12482099
theorem B5547599 : Blo 2191435 5547599 := bstep (se 1 (by rfl) ⟨4160699, by rfl⟩ : syracuseStep 5547599 = 8321399) B8321399
theorem B3698399 : Blo 2191435 3698399 := bstep (se 1 (by rfl) ⟨2773799, by rfl⟩ : syracuseStep 3698399 = 5547599) B5547599
theorem B2465599 : Blo 2191435 2465599 := bstep (se 1 (by rfl) ⟨1849199, by rfl⟩ : syracuseStep 2465599 = 3698399) B3698399
theorem B3287465 : Blo 2191435 3287465 := bstep (se 2 (by rfl) ⟨1232799, by rfl⟩ : syracuseStep 3287465 = 2465599) B2465599
theorem B2191643 : Blo 2191435 2191643 := bstep (se 1 (by rfl) ⟨1643732, by rfl⟩ : syracuseStep 2191643 = 3287465) B3287465
theorem B8321413 : Blo 2191435 8321413 := bbase (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) (by norm_num)
theorem B11095217 : Blo 2191435 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B7396811 : Blo 2191435 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B4931207 : Blo 2191435 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B3287471 : Blo 2191435 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B2191647 : Blo 2191435 2191647 := bstep (se 1 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 2191647 = 3287471) B3287471
theorem B3287477 : Blo 2191435 3287477 := bbase (se 5 (by rfl) ⟨154100, by rfl⟩ : syracuseStep 3287477 = 308201) (by norm_num)
theorem B2191651 : Blo 2191435 2191651 := bstep (se 1 (by rfl) ⟨1643738, by rfl⟩ : syracuseStep 2191651 = 3287477) B3287477
theorem B5547629 : Blo 2191435 5547629 := bbase (se 3 (by rfl) ⟨1040180, by rfl⟩ : syracuseStep 5547629 = 2080361) (by norm_num)
theorem B3698419 : Blo 2191435 3698419 := bstep (se 1 (by rfl) ⟨2773814, by rfl⟩ : syracuseStep 3698419 = 5547629) B5547629
theorem B4931225 : Blo 2191435 4931225 := bstep (se 2 (by rfl) ⟨1849209, by rfl⟩ : syracuseStep 4931225 = 3698419) B3698419
theorem B3287483 : Blo 2191435 3287483 := bstep (se 1 (by rfl) ⟨2465612, by rfl⟩ : syracuseStep 3287483 = 4931225) B4931225
theorem B2191655 : Blo 2191435 2191655 := bstep (se 1 (by rfl) ⟨1643741, by rfl⟩ : syracuseStep 2191655 = 3287483) B3287483
theorem B2465617 : Blo 2191435 2465617 := bbase (se 2 (by rfl) ⟨924606, by rfl⟩ : syracuseStep 2465617 = 1849213) (by norm_num)
theorem B3287489 : Blo 2191435 3287489 := bstep (se 2 (by rfl) ⟨1232808, by rfl⟩ : syracuseStep 3287489 = 2465617) B2465617
theorem B2191659 : Blo 2191435 2191659 := bstep (se 1 (by rfl) ⟨1643744, by rfl⟩ : syracuseStep 2191659 = 3287489) B3287489
theorem B17772533 : Blo 2191435 17772533 := bbase (se 5 (by rfl) ⟨833087, by rfl⟩ : syracuseStep 17772533 = 1666175) (by norm_num)
theorem B11848355 : Blo 2191435 11848355 := bstep (se 1 (by rfl) ⟨8886266, by rfl⟩ : syracuseStep 11848355 = 17772533) B17772533
theorem B7898903 : Blo 2191435 7898903 := bstep (se 1 (by rfl) ⟨5924177, by rfl⟩ : syracuseStep 7898903 = 11848355) B11848355
theorem B5265935 : Blo 2191435 5265935 := bstep (se 1 (by rfl) ⟨3949451, by rfl⟩ : syracuseStep 5265935 = 7898903) B7898903
theorem B3510623 : Blo 2191435 3510623 := bstep (se 1 (by rfl) ⟨2632967, by rfl⟩ : syracuseStep 3510623 = 5265935) B5265935
theorem B2340415 : Blo 2191435 2340415 := bstep (se 1 (by rfl) ⟨1755311, by rfl⟩ : syracuseStep 2340415 = 3510623) B3510623
theorem B3120553 : Blo 2191435 3120553 := bstep (se 2 (by rfl) ⟨1170207, by rfl⟩ : syracuseStep 3120553 = 2340415) B2340415
theorem B4160737 : Blo 2191435 4160737 := bstep (se 2 (by rfl) ⟨1560276, by rfl⟩ : syracuseStep 4160737 = 3120553) B3120553
theorem B5547649 : Blo 2191435 5547649 := bstep (se 2 (by rfl) ⟨2080368, by rfl⟩ : syracuseStep 5547649 = 4160737) B4160737
theorem B7396865 : Blo 2191435 7396865 := bstep (se 2 (by rfl) ⟨2773824, by rfl⟩ : syracuseStep 7396865 = 5547649) B5547649
theorem B4931243 : Blo 2191435 4931243 := bstep (se 1 (by rfl) ⟨3698432, by rfl⟩ : syracuseStep 4931243 = 7396865) B7396865
theorem B3287495 : Blo 2191435 3287495 := bstep (se 1 (by rfl) ⟨2465621, by rfl⟩ : syracuseStep 3287495 = 4931243) B4931243
theorem B2191663 : Blo 2191435 2191663 := bstep (se 1 (by rfl) ⟨1643747, by rfl⟩ : syracuseStep 2191663 = 3287495) B3287495
theorem B3287501 : Blo 2191435 3287501 := bbase (se 3 (by rfl) ⟨616406, by rfl⟩ : syracuseStep 3287501 = 1232813) (by norm_num)
theorem B2191667 : Blo 2191435 2191667 := bstep (se 1 (by rfl) ⟨1643750, by rfl⟩ : syracuseStep 2191667 = 3287501) B3287501
theorem B4931261 : Blo 2191435 4931261 := bbase (se 3 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 4931261 = 1849223) (by norm_num)
theorem B3287507 : Blo 2191435 3287507 := bstep (se 1 (by rfl) ⟨2465630, by rfl⟩ : syracuseStep 3287507 = 4931261) B4931261
theorem B2191671 : Blo 2191435 2191671 := bstep (se 1 (by rfl) ⟨1643753, by rfl⟩ : syracuseStep 2191671 = 3287507) B3287507
theorem B3698453 : Blo 2191435 3698453 := bbase (se 6 (by rfl) ⟨86682, by rfl⟩ : syracuseStep 3698453 = 173365) (by norm_num)
theorem B2465635 : Blo 2191435 2465635 := bstep (se 1 (by rfl) ⟨1849226, by rfl⟩ : syracuseStep 2465635 = 3698453) B3698453
theorem B3287513 : Blo 2191435 3287513 := bstep (se 2 (by rfl) ⟨1232817, by rfl⟩ : syracuseStep 3287513 = 2465635) B2465635
theorem B2191675 : Blo 2191435 2191675 := bstep (se 1 (by rfl) ⟨1643756, by rfl⟩ : syracuseStep 2191675 = 3287513) B3287513
theorem B4574773 : Blo 2191435 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B6099697 : Blo 2191435 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B32531717 : Blo 2191435 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B86751245 : Blo 2191435 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B57834163 : Blo 2191435 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B77112217 : Blo 2191435 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B102816289 : Blo 2191435 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B137088385 : Blo 2191435 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B2924552213 : Blo 2191435 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B1949701475 : Blo 2191435 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B5199203933 : Blo 2191435 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B3466135955 : Blo 2191435 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B2310757303 : Blo 2191435 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B3081009737 : Blo 2191435 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B8216025965 : Blo 2191435 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B5477350643 : Blo 2191435 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B3651567095 : Blo 2191435 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B2434378063 : Blo 2191435 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B3245837417 : Blo 2191435 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B2163891611 : Blo 2191435 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B1442594407 : Blo 2191435 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B1923459209 : Blo 2191435 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B1282306139 : Blo 2191435 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B854870759 : Blo 2191435 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B569913839 : Blo 2191435 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B379942559 : Blo 2191435 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B253295039 : Blo 2191435 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B168863359 : Blo 2191435 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B225151145 : Blo 2191435 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B2401612213 : Blo 2191435 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B3202149617 : Blo 2191435 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B2134766411 : Blo 2191435 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B1423177607 : Blo 2191435 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B948785071 : Blo 2191435 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B1265046761 : Blo 2191435 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B843364507 : Blo 2191435 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B1124486009 : Blo 2191435 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B749657339 : Blo 2191435 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B499771559 : Blo 2191435 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B333181039 : Blo 2191435 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B444241385 : Blo 2191435 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B296160923 : Blo 2191435 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B197440615 : Blo 2191435 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B263254153 : Blo 2191435 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B351005537 : Blo 2191435 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B234003691 : Blo 2191435 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B312004921 : Blo 2191435 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B416006561 : Blo 2191435 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B1109350829 : Blo 2191435 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B739567219 : Blo 2191435 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B986089625 : Blo 2191435 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B657393083 : Blo 2191435 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B438262055 : Blo 2191435 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B292174703 : Blo 2191435 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 2191435 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B519421693 : Blo 2191435 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 2191435 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B461708171 : Blo 2191435 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B307805447 : Blo 2191435 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B205203631 : Blo 2191435 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B273604841 : Blo 2191435 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B182403227 : Blo 2191435 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 2191435 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B648544805 : Blo 2191435 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B432363203 : Blo 2191435 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 2191435 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 2191435 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 2191435 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 2191435 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 2191435 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 2191435 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 2191435 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 2191435 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 2191435 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 2191435 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 2191435 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 2191435 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 2191435 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 2191435 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 2191435 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 2191435 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 2191435 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 2191435 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 2191435 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B16643069 : Blo 2191435 16643069 := bstep (se 3 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 16643069 = 6241151) B6241151
theorem B11095379 : Blo 2191435 11095379 := bstep (se 1 (by rfl) ⟨8321534, by rfl⟩ : syracuseStep 11095379 = 16643069) B16643069
theorem B7396919 : Blo 2191435 7396919 := bstep (se 1 (by rfl) ⟨5547689, by rfl⟩ : syracuseStep 7396919 = 11095379) B11095379
theorem B4931279 : Blo 2191435 4931279 := bstep (se 1 (by rfl) ⟨3698459, by rfl⟩ : syracuseStep 4931279 = 7396919) B7396919
theorem B3287519 : Blo 2191435 3287519 := bstep (se 1 (by rfl) ⟨2465639, by rfl⟩ : syracuseStep 3287519 = 4931279) B4931279
theorem B2191679 : Blo 2191435 2191679 := bstep (se 1 (by rfl) ⟨1643759, by rfl⟩ : syracuseStep 2191679 = 3287519) B3287519
theorem B3287525 : Blo 2191435 3287525 := bbase (se 4 (by rfl) ⟨308205, by rfl⟩ : syracuseStep 3287525 = 616411) (by norm_num)
theorem B2191683 : Blo 2191435 2191683 := bstep (se 1 (by rfl) ⟨1643762, by rfl⟩ : syracuseStep 2191683 = 3287525) B3287525
theorem B14042645 : Blo 2191435 14042645 := bbase (se 6 (by rfl) ⟨329124, by rfl⟩ : syracuseStep 14042645 = 658249) (by norm_num)
theorem B9361763 : Blo 2191435 9361763 := bstep (se 1 (by rfl) ⟨7021322, by rfl⟩ : syracuseStep 9361763 = 14042645) B14042645
theorem B6241175 : Blo 2191435 6241175 := bstep (se 1 (by rfl) ⟨4680881, by rfl⟩ : syracuseStep 6241175 = 9361763) B9361763
theorem B4160783 : Blo 2191435 4160783 := bstep (se 1 (by rfl) ⟨3120587, by rfl⟩ : syracuseStep 4160783 = 6241175) B6241175
theorem B2773855 : Blo 2191435 2773855 := bstep (se 1 (by rfl) ⟨2080391, by rfl⟩ : syracuseStep 2773855 = 4160783) B4160783
theorem B3698473 : Blo 2191435 3698473 := bstep (se 2 (by rfl) ⟨1386927, by rfl⟩ : syracuseStep 3698473 = 2773855) B2773855
theorem B4931297 : Blo 2191435 4931297 := bstep (se 2 (by rfl) ⟨1849236, by rfl⟩ : syracuseStep 4931297 = 3698473) B3698473
theorem B3287531 : Blo 2191435 3287531 := bstep (se 1 (by rfl) ⟨2465648, by rfl⟩ : syracuseStep 3287531 = 4931297) B4931297
theorem B2191687 : Blo 2191435 2191687 := bstep (se 1 (by rfl) ⟨1643765, by rfl⟩ : syracuseStep 2191687 = 3287531) B3287531
theorem B2465653 : Blo 2191435 2465653 := bbase (se 5 (by rfl) ⟨115577, by rfl⟩ : syracuseStep 2465653 = 231155) (by norm_num)
theorem B3287537 : Blo 2191435 3287537 := bstep (se 2 (by rfl) ⟨1232826, by rfl⟩ : syracuseStep 3287537 = 2465653) B2465653
theorem B2191691 : Blo 2191435 2191691 := bstep (se 1 (by rfl) ⟨1643768, by rfl⟩ : syracuseStep 2191691 = 3287537) B3287537
theorem B2773865 : Blo 2191435 2773865 := bbase (se 2 (by rfl) ⟨1040199, by rfl⟩ : syracuseStep 2773865 = 2080399) (by norm_num)
theorem B7396973 : Blo 2191435 7396973 := bstep (se 3 (by rfl) ⟨1386932, by rfl⟩ : syracuseStep 7396973 = 2773865) B2773865
theorem B4931315 : Blo 2191435 4931315 := bstep (se 1 (by rfl) ⟨3698486, by rfl⟩ : syracuseStep 4931315 = 7396973) B7396973
theorem B3287543 : Blo 2191435 3287543 := bstep (se 1 (by rfl) ⟨2465657, by rfl⟩ : syracuseStep 3287543 = 4931315) B4931315
theorem B2191695 : Blo 2191435 2191695 := bstep (se 1 (by rfl) ⟨1643771, by rfl⟩ : syracuseStep 2191695 = 3287543) B3287543
theorem B3287549 : Blo 2191435 3287549 := bbase (se 3 (by rfl) ⟨616415, by rfl⟩ : syracuseStep 3287549 = 1232831) (by norm_num)
theorem B2191699 : Blo 2191435 2191699 := bstep (se 1 (by rfl) ⟨1643774, by rfl⟩ : syracuseStep 2191699 = 3287549) B3287549
theorem B4931333 : Blo 2191435 4931333 := bbase (se 4 (by rfl) ⟨462312, by rfl⟩ : syracuseStep 4931333 = 924625) (by norm_num)
theorem B3287555 : Blo 2191435 3287555 := bstep (se 1 (by rfl) ⟨2465666, by rfl⟩ : syracuseStep 3287555 = 4931333) B4931333
theorem B2191703 : Blo 2191435 2191703 := bstep (se 1 (by rfl) ⟨1643777, by rfl⟩ : syracuseStep 2191703 = 3287555) B3287555
theorem B4160821 : Blo 2191435 4160821 := bbase (se 5 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 4160821 = 390077) (by norm_num)
theorem B5547761 : Blo 2191435 5547761 := bstep (se 2 (by rfl) ⟨2080410, by rfl⟩ : syracuseStep 5547761 = 4160821) B4160821
theorem B3698507 : Blo 2191435 3698507 := bstep (se 1 (by rfl) ⟨2773880, by rfl⟩ : syracuseStep 3698507 = 5547761) B5547761
theorem B2465671 : Blo 2191435 2465671 := bstep (se 1 (by rfl) ⟨1849253, by rfl⟩ : syracuseStep 2465671 = 3698507) B3698507
theorem B3287561 : Blo 2191435 3287561 := bstep (se 2 (by rfl) ⟨1232835, by rfl⟩ : syracuseStep 3287561 = 2465671) B2465671
theorem B2191707 : Blo 2191435 2191707 := bstep (se 1 (by rfl) ⟨1643780, by rfl⟩ : syracuseStep 2191707 = 3287561) B3287561
theorem B11095541 : Blo 2191435 11095541 := bbase (se 5 (by rfl) ⟨520103, by rfl⟩ : syracuseStep 11095541 = 1040207) (by norm_num)
theorem B7397027 : Blo 2191435 7397027 := bstep (se 1 (by rfl) ⟨5547770, by rfl⟩ : syracuseStep 7397027 = 11095541) B11095541
theorem B4931351 : Blo 2191435 4931351 := bstep (se 1 (by rfl) ⟨3698513, by rfl⟩ : syracuseStep 4931351 = 7397027) B7397027
theorem B3287567 : Blo 2191435 3287567 := bstep (se 1 (by rfl) ⟨2465675, by rfl⟩ : syracuseStep 3287567 = 4931351) B4931351
theorem B2191711 : Blo 2191435 2191711 := bstep (se 1 (by rfl) ⟨1643783, by rfl⟩ : syracuseStep 2191711 = 3287567) B3287567
theorem B3287573 : Blo 2191435 3287573 := bbase (se 6 (by rfl) ⟨77052, by rfl⟩ : syracuseStep 3287573 = 154105) (by norm_num)
theorem B2191715 : Blo 2191435 2191715 := bstep (se 1 (by rfl) ⟨1643786, by rfl⟩ : syracuseStep 2191715 = 3287573) B3287573
theorem B18723797 : Blo 2191435 18723797 := bbase (se 7 (by rfl) ⟨219419, by rfl⟩ : syracuseStep 18723797 = 438839) (by norm_num)
theorem B12482531 : Blo 2191435 12482531 := bstep (se 1 (by rfl) ⟨9361898, by rfl⟩ : syracuseStep 12482531 = 18723797) B18723797
theorem B8321687 : Blo 2191435 8321687 := bstep (se 1 (by rfl) ⟨6241265, by rfl⟩ : syracuseStep 8321687 = 12482531) B12482531
theorem B5547791 : Blo 2191435 5547791 := bstep (se 1 (by rfl) ⟨4160843, by rfl⟩ : syracuseStep 5547791 = 8321687) B8321687
theorem B3698527 : Blo 2191435 3698527 := bstep (se 1 (by rfl) ⟨2773895, by rfl⟩ : syracuseStep 3698527 = 5547791) B5547791
theorem B4931369 : Blo 2191435 4931369 := bstep (se 2 (by rfl) ⟨1849263, by rfl⟩ : syracuseStep 4931369 = 3698527) B3698527
theorem B3287579 : Blo 2191435 3287579 := bstep (se 1 (by rfl) ⟨2465684, by rfl⟩ : syracuseStep 3287579 = 4931369) B4931369
theorem B2191719 : Blo 2191435 2191719 := bstep (se 1 (by rfl) ⟨1643789, by rfl⟩ : syracuseStep 2191719 = 3287579) B3287579
theorem B2465689 : Blo 2191435 2465689 := bbase (se 2 (by rfl) ⟨924633, by rfl⟩ : syracuseStep 2465689 = 1849267) (by norm_num)
theorem B3287585 : Blo 2191435 3287585 := bstep (se 2 (by rfl) ⟨1232844, by rfl⟩ : syracuseStep 3287585 = 2465689) B2465689
theorem B2191723 : Blo 2191435 2191723 := bstep (se 1 (by rfl) ⟨1643792, by rfl⟩ : syracuseStep 2191723 = 3287585) B3287585
theorem B8321717 : Blo 2191435 8321717 := bbase (se 5 (by rfl) ⟨390080, by rfl⟩ : syracuseStep 8321717 = 780161) (by norm_num)
theorem B5547811 : Blo 2191435 5547811 := bstep (se 1 (by rfl) ⟨4160858, by rfl⟩ : syracuseStep 5547811 = 8321717) B8321717
theorem B7397081 : Blo 2191435 7397081 := bstep (se 2 (by rfl) ⟨2773905, by rfl⟩ : syracuseStep 7397081 = 5547811) B5547811
theorem B4931387 : Blo 2191435 4931387 := bstep (se 1 (by rfl) ⟨3698540, by rfl⟩ : syracuseStep 4931387 = 7397081) B7397081
theorem B3287591 : Blo 2191435 3287591 := bstep (se 1 (by rfl) ⟨2465693, by rfl⟩ : syracuseStep 3287591 = 4931387) B4931387
theorem B2191727 : Blo 2191435 2191727 := bstep (se 1 (by rfl) ⟨1643795, by rfl⟩ : syracuseStep 2191727 = 3287591) B3287591
theorem B3287597 : Blo 2191435 3287597 := bbase (se 3 (by rfl) ⟨616424, by rfl⟩ : syracuseStep 3287597 = 1232849) (by norm_num)
theorem B2191731 : Blo 2191435 2191731 := bstep (se 1 (by rfl) ⟨1643798, by rfl⟩ : syracuseStep 2191731 = 3287597) B3287597
theorem B4931405 : Blo 2191435 4931405 := bbase (se 3 (by rfl) ⟨924638, by rfl⟩ : syracuseStep 4931405 = 1849277) (by norm_num)
theorem B3287603 : Blo 2191435 3287603 := bstep (se 1 (by rfl) ⟨2465702, by rfl⟩ : syracuseStep 3287603 = 4931405) B4931405
theorem B2191735 : Blo 2191435 2191735 := bstep (se 1 (by rfl) ⟨1643801, by rfl⟩ : syracuseStep 2191735 = 3287603) B3287603
theorem B2773921 : Blo 2191435 2773921 := bbase (se 2 (by rfl) ⟨1040220, by rfl⟩ : syracuseStep 2773921 = 2080441) (by norm_num)
theorem B3698561 : Blo 2191435 3698561 := bstep (se 2 (by rfl) ⟨1386960, by rfl⟩ : syracuseStep 3698561 = 2773921) B2773921
theorem B2465707 : Blo 2191435 2465707 := bstep (se 1 (by rfl) ⟨1849280, by rfl⟩ : syracuseStep 2465707 = 3698561) B3698561
theorem B3287609 : Blo 2191435 3287609 := bstep (se 2 (by rfl) ⟨1232853, by rfl⟩ : syracuseStep 3287609 = 2465707) B2465707
theorem B2191739 : Blo 2191435 2191739 := bstep (se 1 (by rfl) ⟨1643804, by rfl⟩ : syracuseStep 2191739 = 3287609) B3287609
theorem B24965333 : Blo 2191435 24965333 := bbase (se 7 (by rfl) ⟨292562, by rfl⟩ : syracuseStep 24965333 = 585125) (by norm_num)
theorem B16643555 : Blo 2191435 16643555 := bstep (se 1 (by rfl) ⟨12482666, by rfl⟩ : syracuseStep 16643555 = 24965333) B24965333
theorem B11095703 : Blo 2191435 11095703 := bstep (se 1 (by rfl) ⟨8321777, by rfl⟩ : syracuseStep 11095703 = 16643555) B16643555
theorem B7397135 : Blo 2191435 7397135 := bstep (se 1 (by rfl) ⟨5547851, by rfl⟩ : syracuseStep 7397135 = 11095703) B11095703
theorem B4931423 : Blo 2191435 4931423 := bstep (se 1 (by rfl) ⟨3698567, by rfl⟩ : syracuseStep 4931423 = 7397135) B7397135
theorem B3287615 : Blo 2191435 3287615 := bstep (se 1 (by rfl) ⟨2465711, by rfl⟩ : syracuseStep 3287615 = 4931423) B4931423
theorem B2191743 : Blo 2191435 2191743 := bstep (se 1 (by rfl) ⟨1643807, by rfl⟩ : syracuseStep 2191743 = 3287615) B3287615
theorem B3287621 : Blo 2191435 3287621 := bbase (se 4 (by rfl) ⟨308214, by rfl⟩ : syracuseStep 3287621 = 616429) (by norm_num)
theorem B2191747 : Blo 2191435 2191747 := bstep (se 1 (by rfl) ⟨1643810, by rfl⟩ : syracuseStep 2191747 = 3287621) B3287621
theorem B3698581 : Blo 2191435 3698581 := bbase (se 6 (by rfl) ⟨86685, by rfl⟩ : syracuseStep 3698581 = 173371) (by norm_num)
theorem B4931441 : Blo 2191435 4931441 := bstep (se 2 (by rfl) ⟨1849290, by rfl⟩ : syracuseStep 4931441 = 3698581) B3698581
theorem B3287627 : Blo 2191435 3287627 := bstep (se 1 (by rfl) ⟨2465720, by rfl⟩ : syracuseStep 3287627 = 4931441) B4931441
theorem B2191751 : Blo 2191435 2191751 := bstep (se 1 (by rfl) ⟨1643813, by rfl⟩ : syracuseStep 2191751 = 3287627) B3287627
theorem B2465725 : Blo 2191435 2465725 := bbase (se 3 (by rfl) ⟨462323, by rfl⟩ : syracuseStep 2465725 = 924647) (by norm_num)
theorem B3287633 : Blo 2191435 3287633 := bstep (se 2 (by rfl) ⟨1232862, by rfl⟩ : syracuseStep 3287633 = 2465725) B2465725
theorem B2191755 : Blo 2191435 2191755 := bstep (se 1 (by rfl) ⟨1643816, by rfl⟩ : syracuseStep 2191755 = 3287633) B3287633
theorem B7397189 : Blo 2191435 7397189 := bbase (se 4 (by rfl) ⟨693486, by rfl⟩ : syracuseStep 7397189 = 1386973) (by norm_num)
theorem B4931459 : Blo 2191435 4931459 := bstep (se 1 (by rfl) ⟨3698594, by rfl⟩ : syracuseStep 4931459 = 7397189) B7397189
theorem B3287639 : Blo 2191435 3287639 := bstep (se 1 (by rfl) ⟨2465729, by rfl⟩ : syracuseStep 3287639 = 4931459) B4931459
theorem B2191759 : Blo 2191435 2191759 := bstep (se 1 (by rfl) ⟨1643819, by rfl⟩ : syracuseStep 2191759 = 3287639) B3287639
theorem B3287645 : Blo 2191435 3287645 := bbase (se 3 (by rfl) ⟨616433, by rfl⟩ : syracuseStep 3287645 = 1232867) (by norm_num)
theorem B2191763 : Blo 2191435 2191763 := bstep (se 1 (by rfl) ⟨1643822, by rfl⟩ : syracuseStep 2191763 = 3287645) B3287645
theorem B4931477 : Blo 2191435 4931477 := bbase (se 6 (by rfl) ⟨115581, by rfl⟩ : syracuseStep 4931477 = 231163) (by norm_num)
theorem B3287651 : Blo 2191435 3287651 := bstep (se 1 (by rfl) ⟨2465738, by rfl⟩ : syracuseStep 3287651 = 4931477) B4931477
theorem B2191767 : Blo 2191435 2191767 := bstep (se 1 (by rfl) ⟨1643825, by rfl⟩ : syracuseStep 2191767 = 3287651) B3287651
theorem B4681061 : Blo 2191435 4681061 := bbase (se 4 (by rfl) ⟨438849, by rfl⟩ : syracuseStep 4681061 = 877699) (by norm_num)
theorem B3120707 : Blo 2191435 3120707 := bstep (se 1 (by rfl) ⟨2340530, by rfl⟩ : syracuseStep 3120707 = 4681061) B4681061
theorem B8321885 : Blo 2191435 8321885 := bstep (se 3 (by rfl) ⟨1560353, by rfl⟩ : syracuseStep 8321885 = 3120707) B3120707
theorem B5547923 : Blo 2191435 5547923 := bstep (se 1 (by rfl) ⟨4160942, by rfl⟩ : syracuseStep 5547923 = 8321885) B8321885
theorem B3698615 : Blo 2191435 3698615 := bstep (se 1 (by rfl) ⟨2773961, by rfl⟩ : syracuseStep 3698615 = 5547923) B5547923
theorem B2465743 : Blo 2191435 2465743 := bstep (se 1 (by rfl) ⟨1849307, by rfl⟩ : syracuseStep 2465743 = 3698615) B3698615
theorem B3287657 : Blo 2191435 3287657 := bstep (se 2 (by rfl) ⟨1232871, by rfl⟩ : syracuseStep 3287657 = 2465743) B2465743
theorem B2191771 : Blo 2191435 2191771 := bstep (se 1 (by rfl) ⟨1643828, by rfl⟩ : syracuseStep 2191771 = 3287657) B3287657
theorem B10532405 : Blo 2191435 10532405 := bbase (se 5 (by rfl) ⟨493706, by rfl⟩ : syracuseStep 10532405 = 987413) (by norm_num)
theorem B7021603 : Blo 2191435 7021603 := bstep (se 1 (by rfl) ⟨5266202, by rfl⟩ : syracuseStep 7021603 = 10532405) B10532405
theorem B9362137 : Blo 2191435 9362137 := bstep (se 2 (by rfl) ⟨3510801, by rfl⟩ : syracuseStep 9362137 = 7021603) B7021603
theorem B12482849 : Blo 2191435 12482849 := bstep (se 2 (by rfl) ⟨4681068, by rfl⟩ : syracuseStep 12482849 = 9362137) B9362137
theorem B8321899 : Blo 2191435 8321899 := bstep (se 1 (by rfl) ⟨6241424, by rfl⟩ : syracuseStep 8321899 = 12482849) B12482849
theorem B11095865 : Blo 2191435 11095865 := bstep (se 2 (by rfl) ⟨4160949, by rfl⟩ : syracuseStep 11095865 = 8321899) B8321899
theorem B7397243 : Blo 2191435 7397243 := bstep (se 1 (by rfl) ⟨5547932, by rfl⟩ : syracuseStep 7397243 = 11095865) B11095865
theorem B4931495 : Blo 2191435 4931495 := bstep (se 1 (by rfl) ⟨3698621, by rfl⟩ : syracuseStep 4931495 = 7397243) B7397243
theorem B3287663 : Blo 2191435 3287663 := bstep (se 1 (by rfl) ⟨2465747, by rfl⟩ : syracuseStep 3287663 = 4931495) B4931495
theorem B2191775 : Blo 2191435 2191775 := bstep (se 1 (by rfl) ⟨1643831, by rfl⟩ : syracuseStep 2191775 = 3287663) B3287663
theorem B3287669 : Blo 2191435 3287669 := bbase (se 5 (by rfl) ⟨154109, by rfl⟩ : syracuseStep 3287669 = 308219) (by norm_num)
theorem B2191779 : Blo 2191435 2191779 := bstep (se 1 (by rfl) ⟨1643834, by rfl⟩ : syracuseStep 2191779 = 3287669) B3287669
theorem B4160965 : Blo 2191435 4160965 := bbase (se 4 (by rfl) ⟨390090, by rfl⟩ : syracuseStep 4160965 = 780181) (by norm_num)
theorem B5547953 : Blo 2191435 5547953 := bstep (se 2 (by rfl) ⟨2080482, by rfl⟩ : syracuseStep 5547953 = 4160965) B4160965
theorem B3698635 : Blo 2191435 3698635 := bstep (se 1 (by rfl) ⟨2773976, by rfl⟩ : syracuseStep 3698635 = 5547953) B5547953
theorem B4931513 : Blo 2191435 4931513 := bstep (se 2 (by rfl) ⟨1849317, by rfl⟩ : syracuseStep 4931513 = 3698635) B3698635
theorem B3287675 : Blo 2191435 3287675 := bstep (se 1 (by rfl) ⟨2465756, by rfl⟩ : syracuseStep 3287675 = 4931513) B4931513
theorem B2191783 : Blo 2191435 2191783 := bstep (se 1 (by rfl) ⟨1643837, by rfl⟩ : syracuseStep 2191783 = 3287675) B3287675
theorem B2465761 : Blo 2191435 2465761 := bbase (se 2 (by rfl) ⟨924660, by rfl⟩ : syracuseStep 2465761 = 1849321) (by norm_num)
theorem B3287681 : Blo 2191435 3287681 := bstep (se 2 (by rfl) ⟨1232880, by rfl⟩ : syracuseStep 3287681 = 2465761) B2465761
theorem B2191787 : Blo 2191435 2191787 := bstep (se 1 (by rfl) ⟨1643840, by rfl⟩ : syracuseStep 2191787 = 3287681) B3287681
theorem B5547973 : Blo 2191435 5547973 := bbase (se 4 (by rfl) ⟨520122, by rfl⟩ : syracuseStep 5547973 = 1040245) (by norm_num)
theorem B7397297 : Blo 2191435 7397297 := bstep (se 2 (by rfl) ⟨2773986, by rfl⟩ : syracuseStep 7397297 = 5547973) B5547973
theorem B4931531 : Blo 2191435 4931531 := bstep (se 1 (by rfl) ⟨3698648, by rfl⟩ : syracuseStep 4931531 = 7397297) B7397297
theorem B3287687 : Blo 2191435 3287687 := bstep (se 1 (by rfl) ⟨2465765, by rfl⟩ : syracuseStep 3287687 = 4931531) B4931531
theorem B2191791 : Blo 2191435 2191791 := bstep (se 1 (by rfl) ⟨1643843, by rfl⟩ : syracuseStep 2191791 = 3287687) B3287687
theorem B3287693 : Blo 2191435 3287693 := bbase (se 3 (by rfl) ⟨616442, by rfl⟩ : syracuseStep 3287693 = 1232885) (by norm_num)
theorem B2191795 : Blo 2191435 2191795 := bstep (se 1 (by rfl) ⟨1643846, by rfl⟩ : syracuseStep 2191795 = 3287693) B3287693
theorem B4931549 : Blo 2191435 4931549 := bbase (se 3 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 4931549 = 1849331) (by norm_num)
theorem B3287699 : Blo 2191435 3287699 := bstep (se 1 (by rfl) ⟨2465774, by rfl⟩ : syracuseStep 3287699 = 4931549) B4931549
theorem B2191799 : Blo 2191435 2191799 := bstep (se 1 (by rfl) ⟨1643849, by rfl⟩ : syracuseStep 2191799 = 3287699) B3287699
theorem B3698669 : Blo 2191435 3698669 := bbase (se 3 (by rfl) ⟨693500, by rfl⟩ : syracuseStep 3698669 = 1387001) (by norm_num)
theorem B2465779 : Blo 2191435 2465779 := bstep (se 1 (by rfl) ⟨1849334, by rfl⟩ : syracuseStep 2465779 = 3698669) B3698669
theorem B3287705 : Blo 2191435 3287705 := bstep (se 2 (by rfl) ⟨1232889, by rfl⟩ : syracuseStep 3287705 = 2465779) B2465779
theorem B2191803 : Blo 2191435 2191803 := bstep (se 1 (by rfl) ⟨1643852, by rfl⟩ : syracuseStep 2191803 = 3287705) B3287705
theorem B67484501 : Blo 2191435 67484501 := bbase (se 9 (by rfl) ⟨197708, by rfl⟩ : syracuseStep 67484501 = 395417) (by norm_num)
theorem B44989667 : Blo 2191435 44989667 := bstep (se 1 (by rfl) ⟨33742250, by rfl⟩ : syracuseStep 44989667 = 67484501) B67484501
theorem B29993111 : Blo 2191435 29993111 := bstep (se 1 (by rfl) ⟨22494833, by rfl⟩ : syracuseStep 29993111 = 44989667) B44989667
theorem B19995407 : Blo 2191435 19995407 := bstep (se 1 (by rfl) ⟨14996555, by rfl⟩ : syracuseStep 19995407 = 29993111) B29993111
theorem B13330271 : Blo 2191435 13330271 := bstep (se 1 (by rfl) ⟨9997703, by rfl⟩ : syracuseStep 13330271 = 19995407) B19995407
theorem B8886847 : Blo 2191435 8886847 := bstep (se 1 (by rfl) ⟨6665135, by rfl⟩ : syracuseStep 8886847 = 13330271) B13330271
theorem B11849129 : Blo 2191435 11849129 := bstep (se 2 (by rfl) ⟨4443423, by rfl⟩ : syracuseStep 11849129 = 8886847) B8886847
theorem B7899419 : Blo 2191435 7899419 := bstep (se 1 (by rfl) ⟨5924564, by rfl⟩ : syracuseStep 7899419 = 11849129) B11849129
theorem B5266279 : Blo 2191435 5266279 := bstep (se 1 (by rfl) ⟨3949709, by rfl⟩ : syracuseStep 5266279 = 7899419) B7899419
theorem B28086821 : Blo 2191435 28086821 := bstep (se 4 (by rfl) ⟨2633139, by rfl⟩ : syracuseStep 28086821 = 5266279) B5266279
theorem B18724547 : Blo 2191435 18724547 := bstep (se 1 (by rfl) ⟨14043410, by rfl⟩ : syracuseStep 18724547 = 28086821) B28086821
theorem B12483031 : Blo 2191435 12483031 := bstep (se 1 (by rfl) ⟨9362273, by rfl⟩ : syracuseStep 12483031 = 18724547) B18724547
theorem B16644041 : Blo 2191435 16644041 := bstep (se 2 (by rfl) ⟨6241515, by rfl⟩ : syracuseStep 16644041 = 12483031) B12483031
theorem B11096027 : Blo 2191435 11096027 := bstep (se 1 (by rfl) ⟨8322020, by rfl⟩ : syracuseStep 11096027 = 16644041) B16644041
theorem B7397351 : Blo 2191435 7397351 := bstep (se 1 (by rfl) ⟨5548013, by rfl⟩ : syracuseStep 7397351 = 11096027) B11096027
theorem B4931567 : Blo 2191435 4931567 := bstep (se 1 (by rfl) ⟨3698675, by rfl⟩ : syracuseStep 4931567 = 7397351) B7397351
theorem B3287711 : Blo 2191435 3287711 := bstep (se 1 (by rfl) ⟨2465783, by rfl⟩ : syracuseStep 3287711 = 4931567) B4931567
theorem B2191807 : Blo 2191435 2191807 := bstep (se 1 (by rfl) ⟨1643855, by rfl⟩ : syracuseStep 2191807 = 3287711) B3287711
theorem B3287717 : Blo 2191435 3287717 := bbase (se 4 (by rfl) ⟨308223, by rfl⟩ : syracuseStep 3287717 = 616447) (by norm_num)
theorem B2191811 : Blo 2191435 2191811 := bstep (se 1 (by rfl) ⟨1643858, by rfl⟩ : syracuseStep 2191811 = 3287717) B3287717
theorem B2774017 : Blo 2191435 2774017 := bbase (se 2 (by rfl) ⟨1040256, by rfl⟩ : syracuseStep 2774017 = 2080513) (by norm_num)
theorem B3698689 : Blo 2191435 3698689 := bstep (se 2 (by rfl) ⟨1387008, by rfl⟩ : syracuseStep 3698689 = 2774017) B2774017
theorem B4931585 : Blo 2191435 4931585 := bstep (se 2 (by rfl) ⟨1849344, by rfl⟩ : syracuseStep 4931585 = 3698689) B3698689
theorem B3287723 : Blo 2191435 3287723 := bstep (se 1 (by rfl) ⟨2465792, by rfl⟩ : syracuseStep 3287723 = 4931585) B4931585
theorem B2191815 : Blo 2191435 2191815 := bstep (se 1 (by rfl) ⟨1643861, by rfl⟩ : syracuseStep 2191815 = 3287723) B3287723
theorem B2465797 : Blo 2191435 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B3287729 : Blo 2191435 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B2191819 : Blo 2191435 2191819 := bstep (se 1 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 2191819 = 3287729) B3287729
theorem B3120781 : Blo 2191435 3120781 := bbase (se 3 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 3120781 = 1170293) (by norm_num)
theorem B4161041 : Blo 2191435 4161041 := bstep (se 2 (by rfl) ⟨1560390, by rfl⟩ : syracuseStep 4161041 = 3120781) B3120781
theorem B2774027 : Blo 2191435 2774027 := bstep (se 1 (by rfl) ⟨2080520, by rfl⟩ : syracuseStep 2774027 = 4161041) B4161041
theorem B7397405 : Blo 2191435 7397405 := bstep (se 3 (by rfl) ⟨1387013, by rfl⟩ : syracuseStep 7397405 = 2774027) B2774027
theorem B4931603 : Blo 2191435 4931603 := bstep (se 1 (by rfl) ⟨3698702, by rfl⟩ : syracuseStep 4931603 = 7397405) B7397405
theorem B3287735 : Blo 2191435 3287735 := bstep (se 1 (by rfl) ⟨2465801, by rfl⟩ : syracuseStep 3287735 = 4931603) B4931603
theorem B2191823 : Blo 2191435 2191823 := bstep (se 1 (by rfl) ⟨1643867, by rfl⟩ : syracuseStep 2191823 = 3287735) B3287735
theorem B3287741 : Blo 2191435 3287741 := bbase (se 3 (by rfl) ⟨616451, by rfl⟩ : syracuseStep 3287741 = 1232903) (by norm_num)
theorem B2191827 : Blo 2191435 2191827 := bstep (se 1 (by rfl) ⟨1643870, by rfl⟩ : syracuseStep 2191827 = 3287741) B3287741
theorem B4931621 : Blo 2191435 4931621 := bbase (se 4 (by rfl) ⟨462339, by rfl⟩ : syracuseStep 4931621 = 924679) (by norm_num)
theorem B3287747 : Blo 2191435 3287747 := bstep (se 1 (by rfl) ⟨2465810, by rfl⟩ : syracuseStep 3287747 = 4931621) B4931621
theorem B2191831 : Blo 2191435 2191831 := bstep (se 1 (by rfl) ⟨1643873, by rfl⟩ : syracuseStep 2191831 = 3287747) B3287747
theorem B5548085 : Blo 2191435 5548085 := bbase (se 5 (by rfl) ⟨260066, by rfl⟩ : syracuseStep 5548085 = 520133) (by norm_num)
theorem B3698723 : Blo 2191435 3698723 := bstep (se 1 (by rfl) ⟨2774042, by rfl⟩ : syracuseStep 3698723 = 5548085) B5548085
theorem B2465815 : Blo 2191435 2465815 := bstep (se 1 (by rfl) ⟨1849361, by rfl⟩ : syracuseStep 2465815 = 3698723) B3698723
theorem B3287753 : Blo 2191435 3287753 := bstep (se 2 (by rfl) ⟨1232907, by rfl⟩ : syracuseStep 3287753 = 2465815) B2465815
theorem B2191835 : Blo 2191435 2191835 := bstep (se 1 (by rfl) ⟨1643876, by rfl⟩ : syracuseStep 2191835 = 3287753) B3287753
theorem B4998925 : Blo 2191435 4998925 := bbase (se 3 (by rfl) ⟨937298, by rfl⟩ : syracuseStep 4998925 = 1874597) (by norm_num)
theorem B26660933 : Blo 2191435 26660933 := bstep (se 4 (by rfl) ⟨2499462, by rfl⟩ : syracuseStep 26660933 = 4998925) B4998925
theorem B17773955 : Blo 2191435 17773955 := bstep (se 1 (by rfl) ⟨13330466, by rfl⟩ : syracuseStep 17773955 = 26660933) B26660933
theorem B11849303 : Blo 2191435 11849303 := bstep (se 1 (by rfl) ⟨8886977, by rfl⟩ : syracuseStep 11849303 = 17773955) B17773955
theorem B7899535 : Blo 2191435 7899535 := bstep (se 1 (by rfl) ⟨5924651, by rfl⟩ : syracuseStep 7899535 = 11849303) B11849303
theorem B10532713 : Blo 2191435 10532713 := bstep (se 2 (by rfl) ⟨3949767, by rfl⟩ : syracuseStep 10532713 = 7899535) B7899535
theorem B14043617 : Blo 2191435 14043617 := bstep (se 2 (by rfl) ⟨5266356, by rfl⟩ : syracuseStep 14043617 = 10532713) B10532713
theorem B9362411 : Blo 2191435 9362411 := bstep (se 1 (by rfl) ⟨7021808, by rfl⟩ : syracuseStep 9362411 = 14043617) B14043617
theorem B6241607 : Blo 2191435 6241607 := bstep (se 1 (by rfl) ⟨4681205, by rfl⟩ : syracuseStep 6241607 = 9362411) B9362411
theorem B4161071 : Blo 2191435 4161071 := bstep (se 1 (by rfl) ⟨3120803, by rfl⟩ : syracuseStep 4161071 = 6241607) B6241607
theorem B11096189 : Blo 2191435 11096189 := bstep (se 3 (by rfl) ⟨2080535, by rfl⟩ : syracuseStep 11096189 = 4161071) B4161071
theorem B7397459 : Blo 2191435 7397459 := bstep (se 1 (by rfl) ⟨5548094, by rfl⟩ : syracuseStep 7397459 = 11096189) B11096189
theorem B4931639 : Blo 2191435 4931639 := bstep (se 1 (by rfl) ⟨3698729, by rfl⟩ : syracuseStep 4931639 = 7397459) B7397459
theorem B3287759 : Blo 2191435 3287759 := bstep (se 1 (by rfl) ⟨2465819, by rfl⟩ : syracuseStep 3287759 = 4931639) B4931639
theorem B2191839 : Blo 2191435 2191839 := bstep (se 1 (by rfl) ⟨1643879, by rfl⟩ : syracuseStep 2191839 = 3287759) B3287759
theorem B3287765 : Blo 2191435 3287765 := bbase (se 7 (by rfl) ⟨38528, by rfl⟩ : syracuseStep 3287765 = 77057) (by norm_num)
theorem B2191843 : Blo 2191435 2191843 := bstep (se 1 (by rfl) ⟨1643882, by rfl⟩ : syracuseStep 2191843 = 3287765) B3287765
theorem B2221753 : Blo 2191435 2221753 := bbase (se 2 (by rfl) ⟨833157, by rfl⟩ : syracuseStep 2221753 = 1666315) (by norm_num)
theorem B2962337 : Blo 2191435 2962337 := bstep (se 2 (by rfl) ⟨1110876, by rfl⟩ : syracuseStep 2962337 = 2221753) B2221753
theorem B7899565 : Blo 2191435 7899565 := bstep (se 3 (by rfl) ⟨1481168, by rfl⟩ : syracuseStep 7899565 = 2962337) B2962337
theorem B10532753 : Blo 2191435 10532753 := bstep (se 2 (by rfl) ⟨3949782, by rfl⟩ : syracuseStep 10532753 = 7899565) B7899565
theorem B7021835 : Blo 2191435 7021835 := bstep (se 1 (by rfl) ⟨5266376, by rfl⟩ : syracuseStep 7021835 = 10532753) B10532753
theorem B4681223 : Blo 2191435 4681223 := bstep (se 1 (by rfl) ⟨3510917, by rfl⟩ : syracuseStep 4681223 = 7021835) B7021835
theorem B3120815 : Blo 2191435 3120815 := bstep (se 1 (by rfl) ⟨2340611, by rfl⟩ : syracuseStep 3120815 = 4681223) B4681223
theorem B8322173 : Blo 2191435 8322173 := bstep (se 3 (by rfl) ⟨1560407, by rfl⟩ : syracuseStep 8322173 = 3120815) B3120815
theorem B5548115 : Blo 2191435 5548115 := bstep (se 1 (by rfl) ⟨4161086, by rfl⟩ : syracuseStep 5548115 = 8322173) B8322173
theorem B3698743 : Blo 2191435 3698743 := bstep (se 1 (by rfl) ⟨2774057, by rfl⟩ : syracuseStep 3698743 = 5548115) B5548115
theorem B4931657 : Blo 2191435 4931657 := bstep (se 2 (by rfl) ⟨1849371, by rfl⟩ : syracuseStep 4931657 = 3698743) B3698743
theorem B3287771 : Blo 2191435 3287771 := bstep (se 1 (by rfl) ⟨2465828, by rfl⟩ : syracuseStep 3287771 = 4931657) B4931657
theorem B2191847 : Blo 2191435 2191847 := bstep (se 1 (by rfl) ⟨1643885, by rfl⟩ : syracuseStep 2191847 = 3287771) B3287771
theorem B2465833 : Blo 2191435 2465833 := bbase (se 2 (by rfl) ⟨924687, by rfl⟩ : syracuseStep 2465833 = 1849375) (by norm_num)
theorem B3287777 : Blo 2191435 3287777 := bstep (se 2 (by rfl) ⟨1232916, by rfl⟩ : syracuseStep 3287777 = 2465833) B2465833
theorem B2191851 : Blo 2191435 2191851 := bstep (se 1 (by rfl) ⟨1643888, by rfl⟩ : syracuseStep 2191851 = 3287777) B3287777
theorem B3749221 : Blo 2191435 3749221 := bbase (se 4 (by rfl) ⟨351489, by rfl⟩ : syracuseStep 3749221 = 702979) (by norm_num)
theorem B4998961 : Blo 2191435 4998961 := bstep (se 2 (by rfl) ⟨1874610, by rfl⟩ : syracuseStep 4998961 = 3749221) B3749221
theorem B26661125 : Blo 2191435 26661125 := bstep (se 4 (by rfl) ⟨2499480, by rfl⟩ : syracuseStep 26661125 = 4998961) B4998961
theorem B17774083 : Blo 2191435 17774083 := bstep (se 1 (by rfl) ⟨13330562, by rfl⟩ : syracuseStep 17774083 = 26661125) B26661125
theorem B23698777 : Blo 2191435 23698777 := bstep (se 2 (by rfl) ⟨8887041, by rfl⟩ : syracuseStep 23698777 = 17774083) B17774083
theorem B31598369 : Blo 2191435 31598369 := bstep (se 2 (by rfl) ⟨11849388, by rfl⟩ : syracuseStep 31598369 = 23698777) B23698777
theorem B21065579 : Blo 2191435 21065579 := bstep (se 1 (by rfl) ⟨15799184, by rfl⟩ : syracuseStep 21065579 = 31598369) B31598369
theorem B14043719 : Blo 2191435 14043719 := bstep (se 1 (by rfl) ⟨10532789, by rfl⟩ : syracuseStep 14043719 = 21065579) B21065579
theorem B9362479 : Blo 2191435 9362479 := bstep (se 1 (by rfl) ⟨7021859, by rfl⟩ : syracuseStep 9362479 = 14043719) B14043719
theorem B12483305 : Blo 2191435 12483305 := bstep (se 2 (by rfl) ⟨4681239, by rfl⟩ : syracuseStep 12483305 = 9362479) B9362479
theorem B8322203 : Blo 2191435 8322203 := bstep (se 1 (by rfl) ⟨6241652, by rfl⟩ : syracuseStep 8322203 = 12483305) B12483305
theorem B5548135 : Blo 2191435 5548135 := bstep (se 1 (by rfl) ⟨4161101, by rfl⟩ : syracuseStep 5548135 = 8322203) B8322203
theorem B7397513 : Blo 2191435 7397513 := bstep (se 2 (by rfl) ⟨2774067, by rfl⟩ : syracuseStep 7397513 = 5548135) B5548135
theorem B4931675 : Blo 2191435 4931675 := bstep (se 1 (by rfl) ⟨3698756, by rfl⟩ : syracuseStep 4931675 = 7397513) B7397513
theorem B3287783 : Blo 2191435 3287783 := bstep (se 1 (by rfl) ⟨2465837, by rfl⟩ : syracuseStep 3287783 = 4931675) B4931675
theorem B2191855 : Blo 2191435 2191855 := bstep (se 1 (by rfl) ⟨1643891, by rfl⟩ : syracuseStep 2191855 = 3287783) B3287783
theorem B3287789 : Blo 2191435 3287789 := bbase (se 3 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 3287789 = 1232921) (by norm_num)
theorem B2191859 : Blo 2191435 2191859 := bstep (se 1 (by rfl) ⟨1643894, by rfl⟩ : syracuseStep 2191859 = 3287789) B3287789
theorem B4931693 : Blo 2191435 4931693 := bbase (se 3 (by rfl) ⟨924692, by rfl⟩ : syracuseStep 4931693 = 1849385) (by norm_num)
theorem B3287795 : Blo 2191435 3287795 := bstep (se 1 (by rfl) ⟨2465846, by rfl⟩ : syracuseStep 3287795 = 4931693) B4931693
theorem B2191863 : Blo 2191435 2191863 := bstep (se 1 (by rfl) ⟨1643897, by rfl⟩ : syracuseStep 2191863 = 3287795) B3287795
theorem B4161125 : Blo 2191435 4161125 := bbase (se 4 (by rfl) ⟨390105, by rfl⟩ : syracuseStep 4161125 = 780211) (by norm_num)
theorem B2774083 : Blo 2191435 2774083 := bstep (se 1 (by rfl) ⟨2080562, by rfl⟩ : syracuseStep 2774083 = 4161125) B4161125
theorem B3698777 : Blo 2191435 3698777 := bstep (se 2 (by rfl) ⟨1387041, by rfl⟩ : syracuseStep 3698777 = 2774083) B2774083
theorem B2465851 : Blo 2191435 2465851 := bstep (se 1 (by rfl) ⟨1849388, by rfl⟩ : syracuseStep 2465851 = 3698777) B3698777
theorem B3287801 : Blo 2191435 3287801 := bstep (se 2 (by rfl) ⟨1232925, by rfl⟩ : syracuseStep 3287801 = 2465851) B2465851
theorem B2191867 : Blo 2191435 2191867 := bstep (se 1 (by rfl) ⟨1643900, by rfl⟩ : syracuseStep 2191867 = 3287801) B3287801
theorem B2811937 : Blo 2191435 2811937 := bbase (se 2 (by rfl) ⟨1054476, by rfl⟩ : syracuseStep 2811937 = 2108953) (by norm_num)
theorem B3749249 : Blo 2191435 3749249 := bstep (se 2 (by rfl) ⟨1405968, by rfl⟩ : syracuseStep 3749249 = 2811937) B2811937
theorem B2499499 : Blo 2191435 2499499 := bstep (se 1 (by rfl) ⟨1874624, by rfl⟩ : syracuseStep 2499499 = 3749249) B3749249
theorem B3332665 : Blo 2191435 3332665 := bstep (se 2 (by rfl) ⟨1249749, by rfl⟩ : syracuseStep 3332665 = 2499499) B2499499
theorem B4443553 : Blo 2191435 4443553 := bstep (se 2 (by rfl) ⟨1666332, by rfl⟩ : syracuseStep 4443553 = 3332665) B3332665
theorem B5924737 : Blo 2191435 5924737 := bstep (se 2 (by rfl) ⟨2221776, by rfl⟩ : syracuseStep 5924737 = 4443553) B4443553
theorem B7899649 : Blo 2191435 7899649 := bstep (se 2 (by rfl) ⟨2962368, by rfl⟩ : syracuseStep 7899649 = 5924737) B5924737
theorem B42131461 : Blo 2191435 42131461 := bstep (se 4 (by rfl) ⟨3949824, by rfl⟩ : syracuseStep 42131461 = 7899649) B7899649
theorem B56175281 : Blo 2191435 56175281 := bstep (se 2 (by rfl) ⟨21065730, by rfl⟩ : syracuseStep 56175281 = 42131461) B42131461
theorem B37450187 : Blo 2191435 37450187 := bstep (se 1 (by rfl) ⟨28087640, by rfl⟩ : syracuseStep 37450187 = 56175281) B56175281
theorem B24966791 : Blo 2191435 24966791 := bstep (se 1 (by rfl) ⟨18725093, by rfl⟩ : syracuseStep 24966791 = 37450187) B37450187
theorem B16644527 : Blo 2191435 16644527 := bstep (se 1 (by rfl) ⟨12483395, by rfl⟩ : syracuseStep 16644527 = 24966791) B24966791
theorem B11096351 : Blo 2191435 11096351 := bstep (se 1 (by rfl) ⟨8322263, by rfl⟩ : syracuseStep 11096351 = 16644527) B16644527
theorem B7397567 : Blo 2191435 7397567 := bstep (se 1 (by rfl) ⟨5548175, by rfl⟩ : syracuseStep 7397567 = 11096351) B11096351
theorem B4931711 : Blo 2191435 4931711 := bstep (se 1 (by rfl) ⟨3698783, by rfl⟩ : syracuseStep 4931711 = 7397567) B7397567
theorem B3287807 : Blo 2191435 3287807 := bstep (se 1 (by rfl) ⟨2465855, by rfl⟩ : syracuseStep 3287807 = 4931711) B4931711
theorem B2191871 : Blo 2191435 2191871 := bstep (se 1 (by rfl) ⟨1643903, by rfl⟩ : syracuseStep 2191871 = 3287807) B3287807
theorem B3287813 : Blo 2191435 3287813 := bbase (se 4 (by rfl) ⟨308232, by rfl⟩ : syracuseStep 3287813 = 616465) (by norm_num)
theorem B2191875 : Blo 2191435 2191875 := bstep (se 1 (by rfl) ⟨1643906, by rfl⟩ : syracuseStep 2191875 = 3287813) B3287813
theorem B3698797 : Blo 2191435 3698797 := bbase (se 3 (by rfl) ⟨693524, by rfl⟩ : syracuseStep 3698797 = 1387049) (by norm_num)
theorem B4931729 : Blo 2191435 4931729 := bstep (se 2 (by rfl) ⟨1849398, by rfl⟩ : syracuseStep 4931729 = 3698797) B3698797
theorem B3287819 : Blo 2191435 3287819 := bstep (se 1 (by rfl) ⟨2465864, by rfl⟩ : syracuseStep 3287819 = 4931729) B4931729
theorem B2191879 : Blo 2191435 2191879 := bstep (se 1 (by rfl) ⟨1643909, by rfl⟩ : syracuseStep 2191879 = 3287819) B3287819
theorem B2465869 : Blo 2191435 2465869 := bbase (se 3 (by rfl) ⟨462350, by rfl⟩ : syracuseStep 2465869 = 924701) (by norm_num)
theorem B3287825 : Blo 2191435 3287825 := bstep (se 2 (by rfl) ⟨1232934, by rfl⟩ : syracuseStep 3287825 = 2465869) B2465869
theorem B2191883 : Blo 2191435 2191883 := bstep (se 1 (by rfl) ⟨1643912, by rfl⟩ : syracuseStep 2191883 = 3287825) B3287825
theorem B7397621 : Blo 2191435 7397621 := bbase (se 5 (by rfl) ⟨346763, by rfl⟩ : syracuseStep 7397621 = 693527) (by norm_num)
theorem B4931747 : Blo 2191435 4931747 := bstep (se 1 (by rfl) ⟨3698810, by rfl⟩ : syracuseStep 4931747 = 7397621) B7397621
theorem B3287831 : Blo 2191435 3287831 := bstep (se 1 (by rfl) ⟨2465873, by rfl⟩ : syracuseStep 3287831 = 4931747) B4931747
theorem B2191887 : Blo 2191435 2191887 := bstep (se 1 (by rfl) ⟨1643915, by rfl⟩ : syracuseStep 2191887 = 3287831) B3287831
theorem B3287837 : Blo 2191435 3287837 := bbase (se 3 (by rfl) ⟨616469, by rfl⟩ : syracuseStep 3287837 = 1232939) (by norm_num)
theorem B2191891 : Blo 2191435 2191891 := bstep (se 1 (by rfl) ⟨1643918, by rfl⟩ : syracuseStep 2191891 = 3287837) B3287837
theorem B4931765 : Blo 2191435 4931765 := bbase (se 5 (by rfl) ⟨231176, by rfl⟩ : syracuseStep 4931765 = 462353) (by norm_num)
theorem B3287843 : Blo 2191435 3287843 := bstep (se 1 (by rfl) ⟨2465882, by rfl⟩ : syracuseStep 3287843 = 4931765) B4931765
theorem B2191895 : Blo 2191435 2191895 := bstep (se 1 (by rfl) ⟨1643921, by rfl⟩ : syracuseStep 2191895 = 3287843) B3287843
theorem B3949877 : Blo 2191435 3949877 := bbase (se 5 (by rfl) ⟨185150, by rfl⟩ : syracuseStep 3949877 = 370301) (by norm_num)
theorem B2633251 : Blo 2191435 2633251 := bstep (se 1 (by rfl) ⟨1974938, by rfl⟩ : syracuseStep 2633251 = 3949877) B3949877
theorem B3511001 : Blo 2191435 3511001 := bstep (se 2 (by rfl) ⟨1316625, by rfl⟩ : syracuseStep 3511001 = 2633251) B2633251
theorem B2340667 : Blo 2191435 2340667 := bstep (se 1 (by rfl) ⟨1755500, by rfl⟩ : syracuseStep 2340667 = 3511001) B3511001
theorem B12483557 : Blo 2191435 12483557 := bstep (se 4 (by rfl) ⟨1170333, by rfl⟩ : syracuseStep 12483557 = 2340667) B2340667
theorem B8322371 : Blo 2191435 8322371 := bstep (se 1 (by rfl) ⟨6241778, by rfl⟩ : syracuseStep 8322371 = 12483557) B12483557
theorem B5548247 : Blo 2191435 5548247 := bstep (se 1 (by rfl) ⟨4161185, by rfl⟩ : syracuseStep 5548247 = 8322371) B8322371
theorem B3698831 : Blo 2191435 3698831 := bstep (se 1 (by rfl) ⟨2774123, by rfl⟩ : syracuseStep 3698831 = 5548247) B5548247
theorem B2465887 : Blo 2191435 2465887 := bstep (se 1 (by rfl) ⟨1849415, by rfl⟩ : syracuseStep 2465887 = 3698831) B3698831
theorem B3287849 : Blo 2191435 3287849 := bstep (se 2 (by rfl) ⟨1232943, by rfl⟩ : syracuseStep 3287849 = 2465887) B2465887
theorem B2191899 : Blo 2191435 2191899 := bstep (se 1 (by rfl) ⟨1643924, by rfl⟩ : syracuseStep 2191899 = 3287849) B3287849
theorem B6665429 : Blo 2191435 6665429 := bbase (se 7 (by rfl) ⟨78110, by rfl⟩ : syracuseStep 6665429 = 156221) (by norm_num)
theorem B17774477 : Blo 2191435 17774477 := bstep (se 3 (by rfl) ⟨3332714, by rfl⟩ : syracuseStep 17774477 = 6665429) B6665429
theorem B11849651 : Blo 2191435 11849651 := bstep (se 1 (by rfl) ⟨8887238, by rfl⟩ : syracuseStep 11849651 = 17774477) B17774477
theorem B7899767 : Blo 2191435 7899767 := bstep (se 1 (by rfl) ⟨5924825, by rfl⟩ : syracuseStep 7899767 = 11849651) B11849651
theorem B5266511 : Blo 2191435 5266511 := bstep (se 1 (by rfl) ⟨3949883, by rfl⟩ : syracuseStep 5266511 = 7899767) B7899767
theorem B3511007 : Blo 2191435 3511007 := bstep (se 1 (by rfl) ⟨2633255, by rfl⟩ : syracuseStep 3511007 = 5266511) B5266511
theorem B2340671 : Blo 2191435 2340671 := bstep (se 1 (by rfl) ⟨1755503, by rfl⟩ : syracuseStep 2340671 = 3511007) B3511007
theorem B6241789 : Blo 2191435 6241789 := bstep (se 3 (by rfl) ⟨1170335, by rfl⟩ : syracuseStep 6241789 = 2340671) B2340671
theorem B8322385 : Blo 2191435 8322385 := bstep (se 2 (by rfl) ⟨3120894, by rfl⟩ : syracuseStep 8322385 = 6241789) B6241789
theorem B11096513 : Blo 2191435 11096513 := bstep (se 2 (by rfl) ⟨4161192, by rfl⟩ : syracuseStep 11096513 = 8322385) B8322385
theorem B7397675 : Blo 2191435 7397675 := bstep (se 1 (by rfl) ⟨5548256, by rfl⟩ : syracuseStep 7397675 = 11096513) B11096513
theorem B4931783 : Blo 2191435 4931783 := bstep (se 1 (by rfl) ⟨3698837, by rfl⟩ : syracuseStep 4931783 = 7397675) B7397675
theorem B3287855 : Blo 2191435 3287855 := bstep (se 1 (by rfl) ⟨2465891, by rfl⟩ : syracuseStep 3287855 = 4931783) B4931783
theorem B2191903 : Blo 2191435 2191903 := bstep (se 1 (by rfl) ⟨1643927, by rfl⟩ : syracuseStep 2191903 = 3287855) B3287855
theorem B3287861 : Blo 2191435 3287861 := bbase (se 5 (by rfl) ⟨154118, by rfl⟩ : syracuseStep 3287861 = 308237) (by norm_num)
theorem B2191907 : Blo 2191435 2191907 := bstep (se 1 (by rfl) ⟨1643930, by rfl⟩ : syracuseStep 2191907 = 3287861) B3287861
theorem B5548277 : Blo 2191435 5548277 := bbase (se 5 (by rfl) ⟨260075, by rfl⟩ : syracuseStep 5548277 = 520151) (by norm_num)
theorem B3698851 : Blo 2191435 3698851 := bstep (se 1 (by rfl) ⟨2774138, by rfl⟩ : syracuseStep 3698851 = 5548277) B5548277
theorem B4931801 : Blo 2191435 4931801 := bstep (se 2 (by rfl) ⟨1849425, by rfl⟩ : syracuseStep 4931801 = 3698851) B3698851
theorem B3287867 : Blo 2191435 3287867 := bstep (se 1 (by rfl) ⟨2465900, by rfl⟩ : syracuseStep 3287867 = 4931801) B4931801
theorem B2191911 : Blo 2191435 2191911 := bstep (se 1 (by rfl) ⟨1643933, by rfl⟩ : syracuseStep 2191911 = 3287867) B3287867
theorem B2465905 : Blo 2191435 2465905 := bbase (se 2 (by rfl) ⟨924714, by rfl⟩ : syracuseStep 2465905 = 1849429) (by norm_num)
theorem B3287873 : Blo 2191435 3287873 := bstep (se 2 (by rfl) ⟨1232952, by rfl⟩ : syracuseStep 3287873 = 2465905) B2465905
theorem B2191915 : Blo 2191435 2191915 := bstep (se 1 (by rfl) ⟨1643936, by rfl⟩ : syracuseStep 2191915 = 3287873) B3287873
theorem B5266549 : Blo 2191435 5266549 := bbase (se 5 (by rfl) ⟨246869, by rfl⟩ : syracuseStep 5266549 = 493739) (by norm_num)
theorem B7022065 : Blo 2191435 7022065 := bstep (se 2 (by rfl) ⟨2633274, by rfl⟩ : syracuseStep 7022065 = 5266549) B5266549
theorem B9362753 : Blo 2191435 9362753 := bstep (se 2 (by rfl) ⟨3511032, by rfl⟩ : syracuseStep 9362753 = 7022065) B7022065
theorem B6241835 : Blo 2191435 6241835 := bstep (se 1 (by rfl) ⟨4681376, by rfl⟩ : syracuseStep 6241835 = 9362753) B9362753
theorem B4161223 : Blo 2191435 4161223 := bstep (se 1 (by rfl) ⟨3120917, by rfl⟩ : syracuseStep 4161223 = 6241835) B6241835
theorem B5548297 : Blo 2191435 5548297 := bstep (se 2 (by rfl) ⟨2080611, by rfl⟩ : syracuseStep 5548297 = 4161223) B4161223
theorem B7397729 : Blo 2191435 7397729 := bstep (se 2 (by rfl) ⟨2774148, by rfl⟩ : syracuseStep 7397729 = 5548297) B5548297
theorem B4931819 : Blo 2191435 4931819 := bstep (se 1 (by rfl) ⟨3698864, by rfl⟩ : syracuseStep 4931819 = 7397729) B7397729
theorem B3287879 : Blo 2191435 3287879 := bstep (se 1 (by rfl) ⟨2465909, by rfl⟩ : syracuseStep 3287879 = 4931819) B4931819
theorem B2191919 : Blo 2191435 2191919 := bstep (se 1 (by rfl) ⟨1643939, by rfl⟩ : syracuseStep 2191919 = 3287879) B3287879
theorem B3287885 : Blo 2191435 3287885 := bbase (se 3 (by rfl) ⟨616478, by rfl⟩ : syracuseStep 3287885 = 1232957) (by norm_num)
theorem B2191923 : Blo 2191435 2191923 := bstep (se 1 (by rfl) ⟨1643942, by rfl⟩ : syracuseStep 2191923 = 3287885) B3287885
theorem B4931837 : Blo 2191435 4931837 := bbase (se 3 (by rfl) ⟨924719, by rfl⟩ : syracuseStep 4931837 = 1849439) (by norm_num)
theorem B3287891 : Blo 2191435 3287891 := bstep (se 1 (by rfl) ⟨2465918, by rfl⟩ : syracuseStep 3287891 = 4931837) B4931837
theorem B2191927 : Blo 2191435 2191927 := bstep (se 1 (by rfl) ⟨1643945, by rfl⟩ : syracuseStep 2191927 = 3287891) B3287891
theorem B3698885 : Blo 2191435 3698885 := bbase (se 4 (by rfl) ⟨346770, by rfl⟩ : syracuseStep 3698885 = 693541) (by norm_num)
theorem B2465923 : Blo 2191435 2465923 := bstep (se 1 (by rfl) ⟨1849442, by rfl⟩ : syracuseStep 2465923 = 3698885) B3698885
theorem B3287897 : Blo 2191435 3287897 := bstep (se 2 (by rfl) ⟨1232961, by rfl⟩ : syracuseStep 3287897 = 2465923) B2465923
theorem B2191931 : Blo 2191435 2191931 := bstep (se 1 (by rfl) ⟨1643948, by rfl⟩ : syracuseStep 2191931 = 3287897) B3287897
theorem B16645013 : Blo 2191435 16645013 := bbase (se 6 (by rfl) ⟨390117, by rfl⟩ : syracuseStep 16645013 = 780235) (by norm_num)
theorem B11096675 : Blo 2191435 11096675 := bstep (se 1 (by rfl) ⟨8322506, by rfl⟩ : syracuseStep 11096675 = 16645013) B16645013
theorem B7397783 : Blo 2191435 7397783 := bstep (se 1 (by rfl) ⟨5548337, by rfl⟩ : syracuseStep 7397783 = 11096675) B11096675
theorem B4931855 : Blo 2191435 4931855 := bstep (se 1 (by rfl) ⟨3698891, by rfl⟩ : syracuseStep 4931855 = 7397783) B7397783
theorem B3287903 : Blo 2191435 3287903 := bstep (se 1 (by rfl) ⟨2465927, by rfl⟩ : syracuseStep 3287903 = 4931855) B4931855
theorem B2191935 : Blo 2191435 2191935 := bstep (se 1 (by rfl) ⟨1643951, by rfl⟩ : syracuseStep 2191935 = 3287903) B3287903
theorem B3287909 : Blo 2191435 3287909 := bbase (se 4 (by rfl) ⟨308241, by rfl⟩ : syracuseStep 3287909 = 616483) (by norm_num)
theorem B2191939 : Blo 2191435 2191939 := bstep (se 1 (by rfl) ⟨1643954, by rfl⟩ : syracuseStep 2191939 = 3287909) B3287909
theorem B4161269 : Blo 2191435 4161269 := bbase (se 5 (by rfl) ⟨195059, by rfl⟩ : syracuseStep 4161269 = 390119) (by norm_num)
theorem B2774179 : Blo 2191435 2774179 := bstep (se 1 (by rfl) ⟨2080634, by rfl⟩ : syracuseStep 2774179 = 4161269) B4161269
theorem B3698905 : Blo 2191435 3698905 := bstep (se 2 (by rfl) ⟨1387089, by rfl⟩ : syracuseStep 3698905 = 2774179) B2774179
theorem B4931873 : Blo 2191435 4931873 := bstep (se 2 (by rfl) ⟨1849452, by rfl⟩ : syracuseStep 4931873 = 3698905) B3698905
theorem B3287915 : Blo 2191435 3287915 := bstep (se 1 (by rfl) ⟨2465936, by rfl⟩ : syracuseStep 3287915 = 4931873) B4931873
theorem B2191943 : Blo 2191435 2191943 := bstep (se 1 (by rfl) ⟨1643957, by rfl⟩ : syracuseStep 2191943 = 3287915) B3287915
theorem B2465941 : Blo 2191435 2465941 := bbase (se 6 (by rfl) ⟨57795, by rfl⟩ : syracuseStep 2465941 = 115591) (by norm_num)
theorem B3287921 : Blo 2191435 3287921 := bstep (se 2 (by rfl) ⟨1232970, by rfl⟩ : syracuseStep 3287921 = 2465941) B2465941
theorem B2191947 : Blo 2191435 2191947 := bstep (se 1 (by rfl) ⟨1643960, by rfl⟩ : syracuseStep 2191947 = 3287921) B3287921
theorem B2774189 : Blo 2191435 2774189 := bbase (se 3 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 2774189 = 1040321) (by norm_num)
theorem B7397837 : Blo 2191435 7397837 := bstep (se 3 (by rfl) ⟨1387094, by rfl⟩ : syracuseStep 7397837 = 2774189) B2774189
theorem B4931891 : Blo 2191435 4931891 := bstep (se 1 (by rfl) ⟨3698918, by rfl⟩ : syracuseStep 4931891 = 7397837) B7397837
theorem B3287927 : Blo 2191435 3287927 := bstep (se 1 (by rfl) ⟨2465945, by rfl⟩ : syracuseStep 3287927 = 4931891) B4931891
theorem B2191951 : Blo 2191435 2191951 := bstep (se 1 (by rfl) ⟨1643963, by rfl⟩ : syracuseStep 2191951 = 3287927) B3287927
theorem B3287933 : Blo 2191435 3287933 := bbase (se 3 (by rfl) ⟨616487, by rfl⟩ : syracuseStep 3287933 = 1232975) (by norm_num)
theorem B2191955 : Blo 2191435 2191955 := bstep (se 1 (by rfl) ⟨1643966, by rfl⟩ : syracuseStep 2191955 = 3287933) B3287933
theorem B4931909 : Blo 2191435 4931909 := bbase (se 4 (by rfl) ⟨462366, by rfl⟩ : syracuseStep 4931909 = 924733) (by norm_num)
theorem B3287939 : Blo 2191435 3287939 := bstep (se 1 (by rfl) ⟨2465954, by rfl⟩ : syracuseStep 3287939 = 4931909) B4931909
theorem B2191959 : Blo 2191435 2191959 := bstep (se 1 (by rfl) ⟨1643969, by rfl⟩ : syracuseStep 2191959 = 3287939) B3287939
theorem B16234037 : Blo 2191435 16234037 := bbase (se 5 (by rfl) ⟨760970, by rfl⟩ : syracuseStep 16234037 = 1521941) (by norm_num)
theorem B10822691 : Blo 2191435 10822691 := bstep (se 1 (by rfl) ⟨8117018, by rfl⟩ : syracuseStep 10822691 = 16234037) B16234037
theorem B28860509 : Blo 2191435 28860509 := bstep (se 3 (by rfl) ⟨5411345, by rfl⟩ : syracuseStep 28860509 = 10822691) B10822691
theorem B19240339 : Blo 2191435 19240339 := bstep (se 1 (by rfl) ⟨14430254, by rfl⟩ : syracuseStep 19240339 = 28860509) B28860509
theorem B25653785 : Blo 2191435 25653785 := bstep (se 2 (by rfl) ⟨9620169, by rfl⟩ : syracuseStep 25653785 = 19240339) B19240339
theorem B68410093 : Blo 2191435 68410093 := bstep (se 3 (by rfl) ⟨12826892, by rfl⟩ : syracuseStep 68410093 = 25653785) B25653785
theorem B91213457 : Blo 2191435 91213457 := bstep (se 2 (by rfl) ⟨34205046, by rfl⟩ : syracuseStep 91213457 = 68410093) B68410093
theorem B243235885 : Blo 2191435 243235885 := bstep (se 3 (by rfl) ⟨45606728, by rfl⟩ : syracuseStep 243235885 = 91213457) B91213457
theorem B324314513 : Blo 2191435 324314513 := bstep (se 2 (by rfl) ⟨121617942, by rfl⟩ : syracuseStep 324314513 = 243235885) B243235885
theorem B216209675 : Blo 2191435 216209675 := bstep (se 1 (by rfl) ⟨162157256, by rfl⟩ : syracuseStep 216209675 = 324314513) B324314513
theorem B144139783 : Blo 2191435 144139783 := bstep (se 1 (by rfl) ⟨108104837, by rfl⟩ : syracuseStep 144139783 = 216209675) B216209675
theorem B192186377 : Blo 2191435 192186377 := bstep (se 2 (by rfl) ⟨72069891, by rfl⟩ : syracuseStep 192186377 = 144139783) B144139783
theorem B128124251 : Blo 2191435 128124251 := bstep (se 1 (by rfl) ⟨96093188, by rfl⟩ : syracuseStep 128124251 = 192186377) B192186377
theorem B85416167 : Blo 2191435 85416167 := bstep (se 1 (by rfl) ⟨64062125, by rfl⟩ : syracuseStep 85416167 = 128124251) B128124251
theorem B227776445 : Blo 2191435 227776445 := bstep (se 3 (by rfl) ⟨42708083, by rfl⟩ : syracuseStep 227776445 = 85416167) B85416167
theorem B151850963 : Blo 2191435 151850963 := bstep (se 1 (by rfl) ⟨113888222, by rfl⟩ : syracuseStep 151850963 = 227776445) B227776445
theorem B101233975 : Blo 2191435 101233975 := bstep (se 1 (by rfl) ⟨75925481, by rfl⟩ : syracuseStep 101233975 = 151850963) B151850963
theorem B134978633 : Blo 2191435 134978633 := bstep (se 2 (by rfl) ⟨50616987, by rfl⟩ : syracuseStep 134978633 = 101233975) B101233975
theorem B89985755 : Blo 2191435 89985755 := bstep (se 1 (by rfl) ⟨67489316, by rfl⟩ : syracuseStep 89985755 = 134978633) B134978633
theorem B59990503 : Blo 2191435 59990503 := bstep (se 1 (by rfl) ⟨44992877, by rfl⟩ : syracuseStep 59990503 = 89985755) B89985755
theorem B79987337 : Blo 2191435 79987337 := bstep (se 2 (by rfl) ⟨29995251, by rfl⟩ : syracuseStep 79987337 = 59990503) B59990503
theorem B53324891 : Blo 2191435 53324891 := bstep (se 1 (by rfl) ⟨39993668, by rfl⟩ : syracuseStep 53324891 = 79987337) B79987337
theorem B35549927 : Blo 2191435 35549927 := bstep (se 1 (by rfl) ⟨26662445, by rfl⟩ : syracuseStep 35549927 = 53324891) B53324891
theorem B23699951 : Blo 2191435 23699951 := bstep (se 1 (by rfl) ⟨17774963, by rfl⟩ : syracuseStep 23699951 = 35549927) B35549927
theorem B15799967 : Blo 2191435 15799967 := bstep (se 1 (by rfl) ⟨11849975, by rfl⟩ : syracuseStep 15799967 = 23699951) B23699951
theorem B10533311 : Blo 2191435 10533311 := bstep (se 1 (by rfl) ⟨7899983, by rfl⟩ : syracuseStep 10533311 = 15799967) B15799967
theorem B7022207 : Blo 2191435 7022207 := bstep (se 1 (by rfl) ⟨5266655, by rfl⟩ : syracuseStep 7022207 = 10533311) B10533311
theorem B4681471 : Blo 2191435 4681471 := bstep (se 1 (by rfl) ⟨3511103, by rfl⟩ : syracuseStep 4681471 = 7022207) B7022207
theorem B6241961 : Blo 2191435 6241961 := bstep (se 2 (by rfl) ⟨2340735, by rfl⟩ : syracuseStep 6241961 = 4681471) B4681471
theorem B4161307 : Blo 2191435 4161307 := bstep (se 1 (by rfl) ⟨3120980, by rfl⟩ : syracuseStep 4161307 = 6241961) B6241961
theorem B5548409 : Blo 2191435 5548409 := bstep (se 2 (by rfl) ⟨2080653, by rfl⟩ : syracuseStep 5548409 = 4161307) B4161307
theorem B3698939 : Blo 2191435 3698939 := bstep (se 1 (by rfl) ⟨2774204, by rfl⟩ : syracuseStep 3698939 = 5548409) B5548409
theorem B2465959 : Blo 2191435 2465959 := bstep (se 1 (by rfl) ⟨1849469, by rfl⟩ : syracuseStep 2465959 = 3698939) B3698939
theorem B3287945 : Blo 2191435 3287945 := bstep (se 2 (by rfl) ⟨1232979, by rfl⟩ : syracuseStep 3287945 = 2465959) B2465959
theorem B2191963 : Blo 2191435 2191963 := bstep (se 1 (by rfl) ⟨1643972, by rfl⟩ : syracuseStep 2191963 = 3287945) B3287945
theorem B11096837 : Blo 2191435 11096837 := bbase (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) (by norm_num)
theorem B7397891 : Blo 2191435 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B4931927 : Blo 2191435 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B3287951 : Blo 2191435 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B2191967 : Blo 2191435 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B3287957 : Blo 2191435 3287957 := bbase (se 6 (by rfl) ⟨77061, by rfl⟩ : syracuseStep 3287957 = 154123) (by norm_num)
theorem B2191971 : Blo 2191435 2191971 := bstep (se 1 (by rfl) ⟨1643978, by rfl⟩ : syracuseStep 2191971 = 3287957) B3287957
theorem B12483989 : Blo 2191435 12483989 := bbase (se 6 (by rfl) ⟨292593, by rfl⟩ : syracuseStep 12483989 = 585187) (by norm_num)
theorem B8322659 : Blo 2191435 8322659 := bstep (se 1 (by rfl) ⟨6241994, by rfl⟩ : syracuseStep 8322659 = 12483989) B12483989
theorem B5548439 : Blo 2191435 5548439 := bstep (se 1 (by rfl) ⟨4161329, by rfl⟩ : syracuseStep 5548439 = 8322659) B8322659
theorem B3698959 : Blo 2191435 3698959 := bstep (se 1 (by rfl) ⟨2774219, by rfl⟩ : syracuseStep 3698959 = 5548439) B5548439
theorem B4931945 : Blo 2191435 4931945 := bstep (se 2 (by rfl) ⟨1849479, by rfl⟩ : syracuseStep 4931945 = 3698959) B3698959
theorem B3287963 : Blo 2191435 3287963 := bstep (se 1 (by rfl) ⟨2465972, by rfl⟩ : syracuseStep 3287963 = 4931945) B4931945
theorem B2191975 : Blo 2191435 2191975 := bstep (se 1 (by rfl) ⟨1643981, by rfl⟩ : syracuseStep 2191975 = 3287963) B3287963
theorem B2465977 : Blo 2191435 2465977 := bbase (se 2 (by rfl) ⟨924741, by rfl⟩ : syracuseStep 2465977 = 1849483) (by norm_num)
theorem B3287969 : Blo 2191435 3287969 := bstep (se 2 (by rfl) ⟨1232988, by rfl⟩ : syracuseStep 3287969 = 2465977) B2465977
theorem B2191979 : Blo 2191435 2191979 := bstep (se 1 (by rfl) ⟨1643984, by rfl⟩ : syracuseStep 2191979 = 3287969) B3287969
theorem B17775125 : Blo 2191435 17775125 := bbase (se 6 (by rfl) ⟨416604, by rfl⟩ : syracuseStep 17775125 = 833209) (by norm_num)
theorem B11850083 : Blo 2191435 11850083 := bstep (se 1 (by rfl) ⟨8887562, by rfl⟩ : syracuseStep 11850083 = 17775125) B17775125
theorem B7900055 : Blo 2191435 7900055 := bstep (se 1 (by rfl) ⟨5925041, by rfl⟩ : syracuseStep 7900055 = 11850083) B11850083
theorem B5266703 : Blo 2191435 5266703 := bstep (se 1 (by rfl) ⟨3950027, by rfl⟩ : syracuseStep 5266703 = 7900055) B7900055
theorem B3511135 : Blo 2191435 3511135 := bstep (se 1 (by rfl) ⟨2633351, by rfl⟩ : syracuseStep 3511135 = 5266703) B5266703
theorem B4681513 : Blo 2191435 4681513 := bstep (se 2 (by rfl) ⟨1755567, by rfl⟩ : syracuseStep 4681513 = 3511135) B3511135
theorem B6242017 : Blo 2191435 6242017 := bstep (se 2 (by rfl) ⟨2340756, by rfl⟩ : syracuseStep 6242017 = 4681513) B4681513
theorem B8322689 : Blo 2191435 8322689 := bstep (se 2 (by rfl) ⟨3121008, by rfl⟩ : syracuseStep 8322689 = 6242017) B6242017
theorem B5548459 : Blo 2191435 5548459 := bstep (se 1 (by rfl) ⟨4161344, by rfl⟩ : syracuseStep 5548459 = 8322689) B8322689
theorem B7397945 : Blo 2191435 7397945 := bstep (se 2 (by rfl) ⟨2774229, by rfl⟩ : syracuseStep 7397945 = 5548459) B5548459
theorem B4931963 : Blo 2191435 4931963 := bstep (se 1 (by rfl) ⟨3698972, by rfl⟩ : syracuseStep 4931963 = 7397945) B7397945
theorem B3287975 : Blo 2191435 3287975 := bstep (se 1 (by rfl) ⟨2465981, by rfl⟩ : syracuseStep 3287975 = 4931963) B4931963
theorem B2191983 : Blo 2191435 2191983 := bstep (se 1 (by rfl) ⟨1643987, by rfl⟩ : syracuseStep 2191983 = 3287975) B3287975
theorem B3287981 : Blo 2191435 3287981 := bbase (se 3 (by rfl) ⟨616496, by rfl⟩ : syracuseStep 3287981 = 1232993) (by norm_num)
theorem B2191987 : Blo 2191435 2191987 := bstep (se 1 (by rfl) ⟨1643990, by rfl⟩ : syracuseStep 2191987 = 3287981) B3287981
theorem B4931981 : Blo 2191435 4931981 := bbase (se 3 (by rfl) ⟨924746, by rfl⟩ : syracuseStep 4931981 = 1849493) (by norm_num)
theorem B3287987 : Blo 2191435 3287987 := bstep (se 1 (by rfl) ⟨2465990, by rfl⟩ : syracuseStep 3287987 = 4931981) B4931981
theorem B2191991 : Blo 2191435 2191991 := bstep (se 1 (by rfl) ⟨1643993, by rfl⟩ : syracuseStep 2191991 = 3287987) B3287987
theorem B2774245 : Blo 2191435 2774245 := bbase (se 4 (by rfl) ⟨260085, by rfl⟩ : syracuseStep 2774245 = 520171) (by norm_num)
theorem B3698993 : Blo 2191435 3698993 := bstep (se 2 (by rfl) ⟨1387122, by rfl⟩ : syracuseStep 3698993 = 2774245) B2774245
theorem B2465995 : Blo 2191435 2465995 := bstep (se 1 (by rfl) ⟨1849496, by rfl⟩ : syracuseStep 2465995 = 3698993) B3698993
theorem B3287993 : Blo 2191435 3287993 := bstep (se 2 (by rfl) ⟨1232997, by rfl⟩ : syracuseStep 3287993 = 2465995) B2465995
theorem B2191995 : Blo 2191435 2191995 := bstep (se 1 (by rfl) ⟨1643996, by rfl⟩ : syracuseStep 2191995 = 3287993) B3287993
theorem B4003949 : Blo 2191435 4003949 := bbase (se 3 (by rfl) ⟨750740, by rfl⟩ : syracuseStep 4003949 = 1501481) (by norm_num)
theorem B10677197 : Blo 2191435 10677197 := bstep (se 3 (by rfl) ⟨2001974, by rfl⟩ : syracuseStep 10677197 = 4003949) B4003949
theorem B7118131 : Blo 2191435 7118131 := bstep (se 1 (by rfl) ⟨5338598, by rfl⟩ : syracuseStep 7118131 = 10677197) B10677197
theorem B9490841 : Blo 2191435 9490841 := bstep (se 2 (by rfl) ⟨3559065, by rfl⟩ : syracuseStep 9490841 = 7118131) B7118131
theorem B6327227 : Blo 2191435 6327227 := bstep (se 1 (by rfl) ⟨4745420, by rfl⟩ : syracuseStep 6327227 = 9490841) B9490841
theorem B4218151 : Blo 2191435 4218151 := bstep (se 1 (by rfl) ⟨3163613, by rfl⟩ : syracuseStep 4218151 = 6327227) B6327227
theorem B5624201 : Blo 2191435 5624201 := bstep (se 2 (by rfl) ⟨2109075, by rfl⟩ : syracuseStep 5624201 = 4218151) B4218151
theorem B14997869 : Blo 2191435 14997869 := bstep (se 3 (by rfl) ⟨2812100, by rfl⟩ : syracuseStep 14997869 = 5624201) B5624201
theorem B9998579 : Blo 2191435 9998579 := bstep (se 1 (by rfl) ⟨7498934, by rfl⟩ : syracuseStep 9998579 = 14997869) B14997869
theorem B6665719 : Blo 2191435 6665719 := bstep (se 1 (by rfl) ⟨4999289, by rfl⟩ : syracuseStep 6665719 = 9998579) B9998579
theorem B8887625 : Blo 2191435 8887625 := bstep (se 2 (by rfl) ⟨3332859, by rfl⟩ : syracuseStep 8887625 = 6665719) B6665719
theorem B5925083 : Blo 2191435 5925083 := bstep (se 1 (by rfl) ⟨4443812, by rfl⟩ : syracuseStep 5925083 = 8887625) B8887625
theorem B15800221 : Blo 2191435 15800221 := bstep (se 3 (by rfl) ⟨2962541, by rfl⟩ : syracuseStep 15800221 = 5925083) B5925083
theorem B21066961 : Blo 2191435 21066961 := bstep (se 2 (by rfl) ⟨7900110, by rfl⟩ : syracuseStep 21066961 = 15800221) B15800221
theorem B28089281 : Blo 2191435 28089281 := bstep (se 2 (by rfl) ⟨10533480, by rfl⟩ : syracuseStep 28089281 = 21066961) B21066961
theorem B18726187 : Blo 2191435 18726187 := bstep (se 1 (by rfl) ⟨14044640, by rfl⟩ : syracuseStep 18726187 = 28089281) B28089281
theorem B24968249 : Blo 2191435 24968249 := bstep (se 2 (by rfl) ⟨9363093, by rfl⟩ : syracuseStep 24968249 = 18726187) B18726187
theorem B16645499 : Blo 2191435 16645499 := bstep (se 1 (by rfl) ⟨12484124, by rfl⟩ : syracuseStep 16645499 = 24968249) B24968249
theorem B11096999 : Blo 2191435 11096999 := bstep (se 1 (by rfl) ⟨8322749, by rfl⟩ : syracuseStep 11096999 = 16645499) B16645499
theorem B7397999 : Blo 2191435 7397999 := bstep (se 1 (by rfl) ⟨5548499, by rfl⟩ : syracuseStep 7397999 = 11096999) B11096999
theorem B4931999 : Blo 2191435 4931999 := bstep (se 1 (by rfl) ⟨3698999, by rfl⟩ : syracuseStep 4931999 = 7397999) B7397999
theorem B3287999 : Blo 2191435 3287999 := bstep (se 1 (by rfl) ⟨2465999, by rfl⟩ : syracuseStep 3287999 = 4931999) B4931999
theorem B2191999 : Blo 2191435 2191999 := bstep (se 1 (by rfl) ⟨1643999, by rfl⟩ : syracuseStep 2191999 = 3287999) B3287999
theorem B3288005 : Blo 2191435 3288005 := bbase (se 4 (by rfl) ⟨308250, by rfl⟩ : syracuseStep 3288005 = 616501) (by norm_num)
theorem B2192003 : Blo 2191435 2192003 := bstep (se 1 (by rfl) ⟨1644002, by rfl⟩ : syracuseStep 2192003 = 3288005) B3288005
theorem B3699013 : Blo 2191435 3699013 := bbase (se 4 (by rfl) ⟨346782, by rfl⟩ : syracuseStep 3699013 = 693565) (by norm_num)
theorem B4932017 : Blo 2191435 4932017 := bstep (se 2 (by rfl) ⟨1849506, by rfl⟩ : syracuseStep 4932017 = 3699013) B3699013
theorem B3288011 : Blo 2191435 3288011 := bstep (se 1 (by rfl) ⟨2466008, by rfl⟩ : syracuseStep 3288011 = 4932017) B4932017
theorem B2192007 : Blo 2191435 2192007 := bstep (se 1 (by rfl) ⟨1644005, by rfl⟩ : syracuseStep 2192007 = 3288011) B3288011
theorem B2466013 : Blo 2191435 2466013 := bbase (se 3 (by rfl) ⟨462377, by rfl⟩ : syracuseStep 2466013 = 924755) (by norm_num)
theorem B3288017 : Blo 2191435 3288017 := bstep (se 2 (by rfl) ⟨1233006, by rfl⟩ : syracuseStep 3288017 = 2466013) B2466013
theorem B2192011 : Blo 2191435 2192011 := bstep (se 1 (by rfl) ⟨1644008, by rfl⟩ : syracuseStep 2192011 = 3288017) B3288017
theorem B7398053 : Blo 2191435 7398053 := bbase (se 4 (by rfl) ⟨693567, by rfl⟩ : syracuseStep 7398053 = 1387135) (by norm_num)
theorem B4932035 : Blo 2191435 4932035 := bstep (se 1 (by rfl) ⟨3699026, by rfl⟩ : syracuseStep 4932035 = 7398053) B7398053
theorem B3288023 : Blo 2191435 3288023 := bstep (se 1 (by rfl) ⟨2466017, by rfl⟩ : syracuseStep 3288023 = 4932035) B4932035
theorem B2192015 : Blo 2191435 2192015 := bstep (se 1 (by rfl) ⟨1644011, by rfl⟩ : syracuseStep 2192015 = 3288023) B3288023
theorem B3288029 : Blo 2191435 3288029 := bbase (se 3 (by rfl) ⟨616505, by rfl⟩ : syracuseStep 3288029 = 1233011) (by norm_num)
theorem B2192019 : Blo 2191435 2192019 := bstep (se 1 (by rfl) ⟨1644014, by rfl⟩ : syracuseStep 2192019 = 3288029) B3288029
theorem B4932053 : Blo 2191435 4932053 := bbase (se 7 (by rfl) ⟨57797, by rfl⟩ : syracuseStep 4932053 = 115595) (by norm_num)
theorem B3288035 : Blo 2191435 3288035 := bstep (se 1 (by rfl) ⟨2466026, by rfl⟩ : syracuseStep 3288035 = 4932053) B4932053
theorem B2192023 : Blo 2191435 2192023 := bstep (se 1 (by rfl) ⟨1644017, by rfl⟩ : syracuseStep 2192023 = 3288035) B3288035
theorem B31600853 : Blo 2191435 31600853 := bbase (se 7 (by rfl) ⟨370322, by rfl⟩ : syracuseStep 31600853 = 740645) (by norm_num)
theorem B21067235 : Blo 2191435 21067235 := bstep (se 1 (by rfl) ⟨15800426, by rfl⟩ : syracuseStep 21067235 = 31600853) B31600853
theorem B14044823 : Blo 2191435 14044823 := bstep (se 1 (by rfl) ⟨10533617, by rfl⟩ : syracuseStep 14044823 = 21067235) B21067235
theorem B9363215 : Blo 2191435 9363215 := bstep (se 1 (by rfl) ⟨7022411, by rfl⟩ : syracuseStep 9363215 = 14044823) B14044823
theorem B6242143 : Blo 2191435 6242143 := bstep (se 1 (by rfl) ⟨4681607, by rfl⟩ : syracuseStep 6242143 = 9363215) B9363215
theorem B8322857 : Blo 2191435 8322857 := bstep (se 2 (by rfl) ⟨3121071, by rfl⟩ : syracuseStep 8322857 = 6242143) B6242143
theorem B5548571 : Blo 2191435 5548571 := bstep (se 1 (by rfl) ⟨4161428, by rfl⟩ : syracuseStep 5548571 = 8322857) B8322857
theorem B3699047 : Blo 2191435 3699047 := bstep (se 1 (by rfl) ⟨2774285, by rfl⟩ : syracuseStep 3699047 = 5548571) B5548571
theorem B2466031 : Blo 2191435 2466031 := bstep (se 1 (by rfl) ⟨1849523, by rfl⟩ : syracuseStep 2466031 = 3699047) B3699047
theorem B3288041 : Blo 2191435 3288041 := bstep (se 2 (by rfl) ⟨1233015, by rfl⟩ : syracuseStep 3288041 = 2466031) B2466031
theorem B2192027 : Blo 2191435 2192027 := bstep (se 1 (by rfl) ⟨1644020, by rfl⟩ : syracuseStep 2192027 = 3288041) B3288041
theorem B3332909 : Blo 2191435 3332909 := bbase (se 3 (by rfl) ⟨624920, by rfl⟩ : syracuseStep 3332909 = 1249841) (by norm_num)
theorem B2221939 : Blo 2191435 2221939 := bstep (se 1 (by rfl) ⟨1666454, by rfl⟩ : syracuseStep 2221939 = 3332909) B3332909
theorem B2962585 : Blo 2191435 2962585 := bstep (se 2 (by rfl) ⟨1110969, by rfl⟩ : syracuseStep 2962585 = 2221939) B2221939
theorem B15800453 : Blo 2191435 15800453 := bstep (se 4 (by rfl) ⟨1481292, by rfl⟩ : syracuseStep 15800453 = 2962585) B2962585
theorem B10533635 : Blo 2191435 10533635 := bstep (se 1 (by rfl) ⟨7900226, by rfl⟩ : syracuseStep 10533635 = 15800453) B15800453
theorem B7022423 : Blo 2191435 7022423 := bstep (se 1 (by rfl) ⟨5266817, by rfl⟩ : syracuseStep 7022423 = 10533635) B10533635
theorem B18726461 : Blo 2191435 18726461 := bstep (se 3 (by rfl) ⟨3511211, by rfl⟩ : syracuseStep 18726461 = 7022423) B7022423
theorem B12484307 : Blo 2191435 12484307 := bstep (se 1 (by rfl) ⟨9363230, by rfl⟩ : syracuseStep 12484307 = 18726461) B18726461
theorem B8322871 : Blo 2191435 8322871 := bstep (se 1 (by rfl) ⟨6242153, by rfl⟩ : syracuseStep 8322871 = 12484307) B12484307
theorem B11097161 : Blo 2191435 11097161 := bstep (se 2 (by rfl) ⟨4161435, by rfl⟩ : syracuseStep 11097161 = 8322871) B8322871
theorem B7398107 : Blo 2191435 7398107 := bstep (se 1 (by rfl) ⟨5548580, by rfl⟩ : syracuseStep 7398107 = 11097161) B11097161
theorem B4932071 : Blo 2191435 4932071 := bstep (se 1 (by rfl) ⟨3699053, by rfl⟩ : syracuseStep 4932071 = 7398107) B7398107
theorem B3288047 : Blo 2191435 3288047 := bstep (se 1 (by rfl) ⟨2466035, by rfl⟩ : syracuseStep 3288047 = 4932071) B4932071
theorem B2192031 : Blo 2191435 2192031 := bstep (se 1 (by rfl) ⟨1644023, by rfl⟩ : syracuseStep 2192031 = 3288047) B3288047
theorem B3288053 : Blo 2191435 3288053 := bbase (se 5 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 3288053 = 308255) (by norm_num)
theorem B2192035 : Blo 2191435 2192035 := bstep (se 1 (by rfl) ⟨1644026, by rfl⟩ : syracuseStep 2192035 = 3288053) B3288053
theorem B2962597 : Blo 2191435 2962597 := bbase (se 4 (by rfl) ⟨277743, by rfl⟩ : syracuseStep 2962597 = 555487) (by norm_num)
theorem B3950129 : Blo 2191435 3950129 := bstep (se 2 (by rfl) ⟨1481298, by rfl⟩ : syracuseStep 3950129 = 2962597) B2962597
theorem B2633419 : Blo 2191435 2633419 := bstep (se 1 (by rfl) ⟨1975064, by rfl⟩ : syracuseStep 2633419 = 3950129) B3950129
theorem B3511225 : Blo 2191435 3511225 := bstep (se 2 (by rfl) ⟨1316709, by rfl⟩ : syracuseStep 3511225 = 2633419) B2633419
theorem B4681633 : Blo 2191435 4681633 := bstep (se 2 (by rfl) ⟨1755612, by rfl⟩ : syracuseStep 4681633 = 3511225) B3511225
theorem B6242177 : Blo 2191435 6242177 := bstep (se 2 (by rfl) ⟨2340816, by rfl⟩ : syracuseStep 6242177 = 4681633) B4681633
theorem B4161451 : Blo 2191435 4161451 := bstep (se 1 (by rfl) ⟨3121088, by rfl⟩ : syracuseStep 4161451 = 6242177) B6242177
theorem B5548601 : Blo 2191435 5548601 := bstep (se 2 (by rfl) ⟨2080725, by rfl⟩ : syracuseStep 5548601 = 4161451) B4161451
theorem B3699067 : Blo 2191435 3699067 := bstep (se 1 (by rfl) ⟨2774300, by rfl⟩ : syracuseStep 3699067 = 5548601) B5548601
theorem B4932089 : Blo 2191435 4932089 := bstep (se 2 (by rfl) ⟨1849533, by rfl⟩ : syracuseStep 4932089 = 3699067) B3699067
theorem B3288059 : Blo 2191435 3288059 := bstep (se 1 (by rfl) ⟨2466044, by rfl⟩ : syracuseStep 3288059 = 4932089) B4932089
theorem B2192039 : Blo 2191435 2192039 := bstep (se 1 (by rfl) ⟨1644029, by rfl⟩ : syracuseStep 2192039 = 3288059) B3288059
theorem B2466049 : Blo 2191435 2466049 := bbase (se 2 (by rfl) ⟨924768, by rfl⟩ : syracuseStep 2466049 = 1849537) (by norm_num)
theorem B3288065 : Blo 2191435 3288065 := bstep (se 2 (by rfl) ⟨1233024, by rfl⟩ : syracuseStep 3288065 = 2466049) B2466049
theorem B2192043 : Blo 2191435 2192043 := bstep (se 1 (by rfl) ⟨1644032, by rfl⟩ : syracuseStep 2192043 = 3288065) B3288065
theorem B5548621 : Blo 2191435 5548621 := bbase (se 3 (by rfl) ⟨1040366, by rfl⟩ : syracuseStep 5548621 = 2080733) (by norm_num)
theorem B7398161 : Blo 2191435 7398161 := bstep (se 2 (by rfl) ⟨2774310, by rfl⟩ : syracuseStep 7398161 = 5548621) B5548621
theorem B4932107 : Blo 2191435 4932107 := bstep (se 1 (by rfl) ⟨3699080, by rfl⟩ : syracuseStep 4932107 = 7398161) B7398161
theorem B3288071 : Blo 2191435 3288071 := bstep (se 1 (by rfl) ⟨2466053, by rfl⟩ : syracuseStep 3288071 = 4932107) B4932107
theorem B2192047 : Blo 2191435 2192047 := bstep (se 1 (by rfl) ⟨1644035, by rfl⟩ : syracuseStep 2192047 = 3288071) B3288071
theorem B3288077 : Blo 2191435 3288077 := bbase (se 3 (by rfl) ⟨616514, by rfl⟩ : syracuseStep 3288077 = 1233029) (by norm_num)
theorem B2192051 : Blo 2191435 2192051 := bstep (se 1 (by rfl) ⟨1644038, by rfl⟩ : syracuseStep 2192051 = 3288077) B3288077
theorem B4932125 : Blo 2191435 4932125 := bbase (se 3 (by rfl) ⟨924773, by rfl⟩ : syracuseStep 4932125 = 1849547) (by norm_num)
theorem B3288083 : Blo 2191435 3288083 := bstep (se 1 (by rfl) ⟨2466062, by rfl⟩ : syracuseStep 3288083 = 4932125) B4932125
theorem B2192055 : Blo 2191435 2192055 := bstep (se 1 (by rfl) ⟨1644041, by rfl⟩ : syracuseStep 2192055 = 3288083) B3288083
theorem B3699101 : Blo 2191435 3699101 := bbase (se 3 (by rfl) ⟨693581, by rfl⟩ : syracuseStep 3699101 = 1387163) (by norm_num)
theorem B2466067 : Blo 2191435 2466067 := bstep (se 1 (by rfl) ⟨1849550, by rfl⟩ : syracuseStep 2466067 = 3699101) B3699101
theorem B3288089 : Blo 2191435 3288089 := bstep (se 2 (by rfl) ⟨1233033, by rfl⟩ : syracuseStep 3288089 = 2466067) B2466067
theorem B2192059 : Blo 2191435 2192059 := bstep (se 1 (by rfl) ⟨1644044, by rfl⟩ : syracuseStep 2192059 = 3288089) B3288089
theorem B5624365 : Blo 2191435 5624365 := bbase (se 3 (by rfl) ⟨1054568, by rfl⟩ : syracuseStep 5624365 = 2109137) (by norm_num)
theorem B7499153 : Blo 2191435 7499153 := bstep (se 2 (by rfl) ⟨2812182, by rfl⟩ : syracuseStep 7499153 = 5624365) B5624365
theorem B19997741 : Blo 2191435 19997741 := bstep (se 3 (by rfl) ⟨3749576, by rfl⟩ : syracuseStep 19997741 = 7499153) B7499153
theorem B13331827 : Blo 2191435 13331827 := bstep (se 1 (by rfl) ⟨9998870, by rfl⟩ : syracuseStep 13331827 = 19997741) B19997741
theorem B17775769 : Blo 2191435 17775769 := bstep (se 2 (by rfl) ⟨6665913, by rfl⟩ : syracuseStep 17775769 = 13331827) B13331827
theorem B23701025 : Blo 2191435 23701025 := bstep (se 2 (by rfl) ⟨8887884, by rfl⟩ : syracuseStep 23701025 = 17775769) B17775769
theorem B15800683 : Blo 2191435 15800683 := bstep (se 1 (by rfl) ⟨11850512, by rfl⟩ : syracuseStep 15800683 = 23701025) B23701025
theorem B21067577 : Blo 2191435 21067577 := bstep (se 2 (by rfl) ⟨7900341, by rfl⟩ : syracuseStep 21067577 = 15800683) B15800683
theorem B14045051 : Blo 2191435 14045051 := bstep (se 1 (by rfl) ⟨10533788, by rfl⟩ : syracuseStep 14045051 = 21067577) B21067577
theorem B9363367 : Blo 2191435 9363367 := bstep (se 1 (by rfl) ⟨7022525, by rfl⟩ : syracuseStep 9363367 = 14045051) B14045051
theorem B12484489 : Blo 2191435 12484489 := bstep (se 2 (by rfl) ⟨4681683, by rfl⟩ : syracuseStep 12484489 = 9363367) B9363367
theorem B16645985 : Blo 2191435 16645985 := bstep (se 2 (by rfl) ⟨6242244, by rfl⟩ : syracuseStep 16645985 = 12484489) B12484489
theorem B11097323 : Blo 2191435 11097323 := bstep (se 1 (by rfl) ⟨8322992, by rfl⟩ : syracuseStep 11097323 = 16645985) B16645985
theorem B7398215 : Blo 2191435 7398215 := bstep (se 1 (by rfl) ⟨5548661, by rfl⟩ : syracuseStep 7398215 = 11097323) B11097323
theorem B4932143 : Blo 2191435 4932143 := bstep (se 1 (by rfl) ⟨3699107, by rfl⟩ : syracuseStep 4932143 = 7398215) B7398215
theorem B3288095 : Blo 2191435 3288095 := bstep (se 1 (by rfl) ⟨2466071, by rfl⟩ : syracuseStep 3288095 = 4932143) B4932143
theorem B2192063 : Blo 2191435 2192063 := bstep (se 1 (by rfl) ⟨1644047, by rfl⟩ : syracuseStep 2192063 = 3288095) B3288095
theorem B3288101 : Blo 2191435 3288101 := bbase (se 4 (by rfl) ⟨308259, by rfl⟩ : syracuseStep 3288101 = 616519) (by norm_num)
theorem B2192067 : Blo 2191435 2192067 := bstep (se 1 (by rfl) ⟨1644050, by rfl⟩ : syracuseStep 2192067 = 3288101) B3288101
theorem B2774341 : Blo 2191435 2774341 := bbase (se 4 (by rfl) ⟨260094, by rfl⟩ : syracuseStep 2774341 = 520189) (by norm_num)
theorem B3699121 : Blo 2191435 3699121 := bstep (se 2 (by rfl) ⟨1387170, by rfl⟩ : syracuseStep 3699121 = 2774341) B2774341
theorem B4932161 : Blo 2191435 4932161 := bstep (se 2 (by rfl) ⟨1849560, by rfl⟩ : syracuseStep 4932161 = 3699121) B3699121
theorem B3288107 : Blo 2191435 3288107 := bstep (se 1 (by rfl) ⟨2466080, by rfl⟩ : syracuseStep 3288107 = 4932161) B4932161
theorem B2192071 : Blo 2191435 2192071 := bstep (se 1 (by rfl) ⟨1644053, by rfl⟩ : syracuseStep 2192071 = 3288107) B3288107
theorem B2466085 : Blo 2191435 2466085 := bbase (se 4 (by rfl) ⟨231195, by rfl⟩ : syracuseStep 2466085 = 462391) (by norm_num)
theorem B3288113 : Blo 2191435 3288113 := bstep (se 2 (by rfl) ⟨1233042, by rfl⟩ : syracuseStep 3288113 = 2466085) B2466085
theorem B2192075 : Blo 2191435 2192075 := bstep (se 1 (by rfl) ⟨1644056, by rfl⟩ : syracuseStep 2192075 = 3288113) B3288113
theorem B2812205 : Blo 2191435 2812205 := bbase (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) (by norm_num)
theorem B7499213 : Blo 2191435 7499213 := bstep (se 3 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 7499213 = 2812205) B2812205
theorem B4999475 : Blo 2191435 4999475 := bstep (se 1 (by rfl) ⟨3749606, by rfl⟩ : syracuseStep 4999475 = 7499213) B7499213
theorem B3332983 : Blo 2191435 3332983 := bstep (se 1 (by rfl) ⟨2499737, by rfl⟩ : syracuseStep 3332983 = 4999475) B4999475
theorem B4443977 : Blo 2191435 4443977 := bstep (se 2 (by rfl) ⟨1666491, by rfl⟩ : syracuseStep 4443977 = 3332983) B3332983
theorem B2962651 : Blo 2191435 2962651 := bstep (se 1 (by rfl) ⟨2221988, by rfl⟩ : syracuseStep 2962651 = 4443977) B4443977
theorem B3950201 : Blo 2191435 3950201 := bstep (se 2 (by rfl) ⟨1481325, by rfl⟩ : syracuseStep 3950201 = 2962651) B2962651
theorem B2633467 : Blo 2191435 2633467 := bstep (se 1 (by rfl) ⟨1975100, by rfl⟩ : syracuseStep 2633467 = 3950201) B3950201
theorem B3511289 : Blo 2191435 3511289 := bstep (se 2 (by rfl) ⟨1316733, by rfl⟩ : syracuseStep 3511289 = 2633467) B2633467
theorem B9363437 : Blo 2191435 9363437 := bstep (se 3 (by rfl) ⟨1755644, by rfl⟩ : syracuseStep 9363437 = 3511289) B3511289
theorem B6242291 : Blo 2191435 6242291 := bstep (se 1 (by rfl) ⟨4681718, by rfl⟩ : syracuseStep 6242291 = 9363437) B9363437
theorem B4161527 : Blo 2191435 4161527 := bstep (se 1 (by rfl) ⟨3121145, by rfl⟩ : syracuseStep 4161527 = 6242291) B6242291
theorem B2774351 : Blo 2191435 2774351 := bstep (se 1 (by rfl) ⟨2080763, by rfl⟩ : syracuseStep 2774351 = 4161527) B4161527
theorem B7398269 : Blo 2191435 7398269 := bstep (se 3 (by rfl) ⟨1387175, by rfl⟩ : syracuseStep 7398269 = 2774351) B2774351
theorem B4932179 : Blo 2191435 4932179 := bstep (se 1 (by rfl) ⟨3699134, by rfl⟩ : syracuseStep 4932179 = 7398269) B7398269
theorem B3288119 : Blo 2191435 3288119 := bstep (se 1 (by rfl) ⟨2466089, by rfl⟩ : syracuseStep 3288119 = 4932179) B4932179
theorem B2192079 : Blo 2191435 2192079 := bstep (se 1 (by rfl) ⟨1644059, by rfl⟩ : syracuseStep 2192079 = 3288119) B3288119
theorem B3288125 : Blo 2191435 3288125 := bbase (se 3 (by rfl) ⟨616523, by rfl⟩ : syracuseStep 3288125 = 1233047) (by norm_num)
theorem B2192083 : Blo 2191435 2192083 := bstep (se 1 (by rfl) ⟨1644062, by rfl⟩ : syracuseStep 2192083 = 3288125) B3288125
theorem B4932197 : Blo 2191435 4932197 := bbase (se 4 (by rfl) ⟨462393, by rfl⟩ : syracuseStep 4932197 = 924787) (by norm_num)
theorem B3288131 : Blo 2191435 3288131 := bstep (se 1 (by rfl) ⟨2466098, by rfl⟩ : syracuseStep 3288131 = 4932197) B4932197
theorem B2192087 : Blo 2191435 2192087 := bstep (se 1 (by rfl) ⟨1644065, by rfl⟩ : syracuseStep 2192087 = 3288131) B3288131
theorem B5548733 : Blo 2191435 5548733 := bbase (se 3 (by rfl) ⟨1040387, by rfl⟩ : syracuseStep 5548733 = 2080775) (by norm_num)
theorem B3699155 : Blo 2191435 3699155 := bstep (se 1 (by rfl) ⟨2774366, by rfl⟩ : syracuseStep 3699155 = 5548733) B5548733
theorem B2466103 : Blo 2191435 2466103 := bstep (se 1 (by rfl) ⟨1849577, by rfl⟩ : syracuseStep 2466103 = 3699155) B3699155
theorem B3288137 : Blo 2191435 3288137 := bstep (se 2 (by rfl) ⟨1233051, by rfl⟩ : syracuseStep 3288137 = 2466103) B2466103
theorem B2192091 : Blo 2191435 2192091 := bstep (se 1 (by rfl) ⟨1644068, by rfl⟩ : syracuseStep 2192091 = 3288137) B3288137
theorem B4161557 : Blo 2191435 4161557 := bbase (se 6 (by rfl) ⟨97536, by rfl⟩ : syracuseStep 4161557 = 195073) (by norm_num)
theorem B11097485 : Blo 2191435 11097485 := bstep (se 3 (by rfl) ⟨2080778, by rfl⟩ : syracuseStep 11097485 = 4161557) B4161557
theorem B7398323 : Blo 2191435 7398323 := bstep (se 1 (by rfl) ⟨5548742, by rfl⟩ : syracuseStep 7398323 = 11097485) B11097485
theorem B4932215 : Blo 2191435 4932215 := bstep (se 1 (by rfl) ⟨3699161, by rfl⟩ : syracuseStep 4932215 = 7398323) B7398323
theorem B3288143 : Blo 2191435 3288143 := bstep (se 1 (by rfl) ⟨2466107, by rfl⟩ : syracuseStep 3288143 = 4932215) B4932215
theorem B2192095 : Blo 2191435 2192095 := bstep (se 1 (by rfl) ⟨1644071, by rfl⟩ : syracuseStep 2192095 = 3288143) B3288143
theorem B3288149 : Blo 2191435 3288149 := bbase (se 8 (by rfl) ⟨19266, by rfl⟩ : syracuseStep 3288149 = 38533) (by norm_num)
theorem B2192099 : Blo 2191435 2192099 := bstep (se 1 (by rfl) ⟨1644074, by rfl⟩ : syracuseStep 2192099 = 3288149) B3288149
theorem B10135477 : Blo 2191435 10135477 := bbase (se 5 (by rfl) ⟨475100, by rfl⟩ : syracuseStep 10135477 = 950201) (by norm_num)
theorem B13513969 : Blo 2191435 13513969 := bstep (se 2 (by rfl) ⟨5067738, by rfl⟩ : syracuseStep 13513969 = 10135477) B10135477
theorem B18018625 : Blo 2191435 18018625 := bstep (se 2 (by rfl) ⟨6756984, by rfl⟩ : syracuseStep 18018625 = 13513969) B13513969
theorem B24024833 : Blo 2191435 24024833 := bstep (se 2 (by rfl) ⟨9009312, by rfl⟩ : syracuseStep 24024833 = 18018625) B18018625
theorem B16016555 : Blo 2191435 16016555 := bstep (se 1 (by rfl) ⟨12012416, by rfl⟩ : syracuseStep 16016555 = 24024833) B24024833
theorem B42710813 : Blo 2191435 42710813 := bstep (se 3 (by rfl) ⟨8008277, by rfl⟩ : syracuseStep 42710813 = 16016555) B16016555
theorem B28473875 : Blo 2191435 28473875 := bstep (se 1 (by rfl) ⟨21355406, by rfl⟩ : syracuseStep 28473875 = 42710813) B42710813
theorem B18982583 : Blo 2191435 18982583 := bstep (se 1 (by rfl) ⟨14236937, by rfl⟩ : syracuseStep 18982583 = 28473875) B28473875
theorem B12655055 : Blo 2191435 12655055 := bstep (se 1 (by rfl) ⟨9491291, by rfl⟩ : syracuseStep 12655055 = 18982583) B18982583
theorem B33746813 : Blo 2191435 33746813 := bstep (se 3 (by rfl) ⟨6327527, by rfl⟩ : syracuseStep 33746813 = 12655055) B12655055
theorem B22497875 : Blo 2191435 22497875 := bstep (se 1 (by rfl) ⟨16873406, by rfl⟩ : syracuseStep 22497875 = 33746813) B33746813
theorem B14998583 : Blo 2191435 14998583 := bstep (se 1 (by rfl) ⟨11248937, by rfl⟩ : syracuseStep 14998583 = 22497875) B22497875
theorem B9999055 : Blo 2191435 9999055 := bstep (se 1 (by rfl) ⟨7499291, by rfl⟩ : syracuseStep 9999055 = 14998583) B14998583
theorem B13332073 : Blo 2191435 13332073 := bstep (se 2 (by rfl) ⟨4999527, by rfl⟩ : syracuseStep 13332073 = 9999055) B9999055
theorem B17776097 : Blo 2191435 17776097 := bstep (se 2 (by rfl) ⟨6666036, by rfl⟩ : syracuseStep 17776097 = 13332073) B13332073
theorem B11850731 : Blo 2191435 11850731 := bstep (se 1 (by rfl) ⟨8888048, by rfl⟩ : syracuseStep 11850731 = 17776097) B17776097
theorem B7900487 : Blo 2191435 7900487 := bstep (se 1 (by rfl) ⟨5925365, by rfl⟩ : syracuseStep 7900487 = 11850731) B11850731
theorem B5266991 : Blo 2191435 5266991 := bstep (se 1 (by rfl) ⟨3950243, by rfl⟩ : syracuseStep 5266991 = 7900487) B7900487
theorem B14045309 : Blo 2191435 14045309 := bstep (se 3 (by rfl) ⟨2633495, by rfl⟩ : syracuseStep 14045309 = 5266991) B5266991
theorem B9363539 : Blo 2191435 9363539 := bstep (se 1 (by rfl) ⟨7022654, by rfl⟩ : syracuseStep 9363539 = 14045309) B14045309
theorem B6242359 : Blo 2191435 6242359 := bstep (se 1 (by rfl) ⟨4681769, by rfl⟩ : syracuseStep 6242359 = 9363539) B9363539
theorem B8323145 : Blo 2191435 8323145 := bstep (se 2 (by rfl) ⟨3121179, by rfl⟩ : syracuseStep 8323145 = 6242359) B6242359
theorem B5548763 : Blo 2191435 5548763 := bstep (se 1 (by rfl) ⟨4161572, by rfl⟩ : syracuseStep 5548763 = 8323145) B8323145
theorem B3699175 : Blo 2191435 3699175 := bstep (se 1 (by rfl) ⟨2774381, by rfl⟩ : syracuseStep 3699175 = 5548763) B5548763
theorem B4932233 : Blo 2191435 4932233 := bstep (se 2 (by rfl) ⟨1849587, by rfl⟩ : syracuseStep 4932233 = 3699175) B3699175
theorem B3288155 : Blo 2191435 3288155 := bstep (se 1 (by rfl) ⟨2466116, by rfl⟩ : syracuseStep 3288155 = 4932233) B4932233
theorem B2192103 : Blo 2191435 2192103 := bstep (se 1 (by rfl) ⟨1644077, by rfl⟩ : syracuseStep 2192103 = 3288155) B3288155
theorem B2466121 : Blo 2191435 2466121 := bbase (se 2 (by rfl) ⟨924795, by rfl⟩ : syracuseStep 2466121 = 1849591) (by norm_num)
theorem B3288161 : Blo 2191435 3288161 := bstep (se 2 (by rfl) ⟨1233060, by rfl⟩ : syracuseStep 3288161 = 2466121) B2466121
theorem B2192107 : Blo 2191435 2192107 := bstep (se 1 (by rfl) ⟨1644080, by rfl⟩ : syracuseStep 2192107 = 3288161) B3288161
theorem B29997269 : Blo 2191435 29997269 := bbase (se 7 (by rfl) ⟨351530, by rfl⟩ : syracuseStep 29997269 = 703061) (by norm_num)
theorem B19998179 : Blo 2191435 19998179 := bstep (se 1 (by rfl) ⟨14998634, by rfl⟩ : syracuseStep 19998179 = 29997269) B29997269
theorem B13332119 : Blo 2191435 13332119 := bstep (se 1 (by rfl) ⟨9999089, by rfl⟩ : syracuseStep 13332119 = 19998179) B19998179
theorem B35552317 : Blo 2191435 35552317 := bstep (se 3 (by rfl) ⟨6666059, by rfl⟩ : syracuseStep 35552317 = 13332119) B13332119
theorem B47403089 : Blo 2191435 47403089 := bstep (se 2 (by rfl) ⟨17776158, by rfl⟩ : syracuseStep 47403089 = 35552317) B35552317
theorem B31602059 : Blo 2191435 31602059 := bstep (se 1 (by rfl) ⟨23701544, by rfl⟩ : syracuseStep 31602059 = 47403089) B47403089
theorem B21068039 : Blo 2191435 21068039 := bstep (se 1 (by rfl) ⟨15801029, by rfl⟩ : syracuseStep 21068039 = 31602059) B31602059
theorem B14045359 : Blo 2191435 14045359 := bstep (se 1 (by rfl) ⟨10534019, by rfl⟩ : syracuseStep 14045359 = 21068039) B21068039
theorem B18727145 : Blo 2191435 18727145 := bstep (se 2 (by rfl) ⟨7022679, by rfl⟩ : syracuseStep 18727145 = 14045359) B14045359
theorem B12484763 : Blo 2191435 12484763 := bstep (se 1 (by rfl) ⟨9363572, by rfl⟩ : syracuseStep 12484763 = 18727145) B18727145
theorem B8323175 : Blo 2191435 8323175 := bstep (se 1 (by rfl) ⟨6242381, by rfl⟩ : syracuseStep 8323175 = 12484763) B12484763
theorem B5548783 : Blo 2191435 5548783 := bstep (se 1 (by rfl) ⟨4161587, by rfl⟩ : syracuseStep 5548783 = 8323175) B8323175
theorem B7398377 : Blo 2191435 7398377 := bstep (se 2 (by rfl) ⟨2774391, by rfl⟩ : syracuseStep 7398377 = 5548783) B5548783
theorem B4932251 : Blo 2191435 4932251 := bstep (se 1 (by rfl) ⟨3699188, by rfl⟩ : syracuseStep 4932251 = 7398377) B7398377
theorem B3288167 : Blo 2191435 3288167 := bstep (se 1 (by rfl) ⟨2466125, by rfl⟩ : syracuseStep 3288167 = 4932251) B4932251
theorem B2192111 : Blo 2191435 2192111 := bstep (se 1 (by rfl) ⟨1644083, by rfl⟩ : syracuseStep 2192111 = 3288167) B3288167
theorem B3288173 : Blo 2191435 3288173 := bbase (se 3 (by rfl) ⟨616532, by rfl⟩ : syracuseStep 3288173 = 1233065) (by norm_num)
theorem B2192115 : Blo 2191435 2192115 := bstep (se 1 (by rfl) ⟨1644086, by rfl⟩ : syracuseStep 2192115 = 3288173) B3288173
theorem B4932269 : Blo 2191435 4932269 := bbase (se 3 (by rfl) ⟨924800, by rfl⟩ : syracuseStep 4932269 = 1849601) (by norm_num)
theorem B3288179 : Blo 2191435 3288179 := bstep (se 1 (by rfl) ⟨2466134, by rfl⟩ : syracuseStep 3288179 = 4932269) B4932269
theorem B2192119 : Blo 2191435 2192119 := bstep (se 1 (by rfl) ⟨1644089, by rfl⟩ : syracuseStep 2192119 = 3288179) B3288179
theorem B4681813 : Blo 2191435 4681813 := bbase (se 8 (by rfl) ⟨27432, by rfl⟩ : syracuseStep 4681813 = 54865) (by norm_num)
theorem B6242417 : Blo 2191435 6242417 := bstep (se 2 (by rfl) ⟨2340906, by rfl⟩ : syracuseStep 6242417 = 4681813) B4681813
theorem B4161611 : Blo 2191435 4161611 := bstep (se 1 (by rfl) ⟨3121208, by rfl⟩ : syracuseStep 4161611 = 6242417) B6242417
theorem B2774407 : Blo 2191435 2774407 := bstep (se 1 (by rfl) ⟨2080805, by rfl⟩ : syracuseStep 2774407 = 4161611) B4161611
theorem B3699209 : Blo 2191435 3699209 := bstep (se 2 (by rfl) ⟨1387203, by rfl⟩ : syracuseStep 3699209 = 2774407) B2774407
theorem B2466139 : Blo 2191435 2466139 := bstep (se 1 (by rfl) ⟨1849604, by rfl⟩ : syracuseStep 2466139 = 3699209) B3699209
theorem B3288185 : Blo 2191435 3288185 := bstep (se 2 (by rfl) ⟨1233069, by rfl⟩ : syracuseStep 3288185 = 2466139) B2466139
theorem B2192123 : Blo 2191435 2192123 := bstep (se 1 (by rfl) ⟨1644092, by rfl⟩ : syracuseStep 2192123 = 3288185) B3288185
theorem B12655189 : Blo 2191435 12655189 := bbase (se 8 (by rfl) ⟨74151, by rfl⟩ : syracuseStep 12655189 = 148303) (by norm_num)
theorem B16873585 : Blo 2191435 16873585 := bstep (se 2 (by rfl) ⟨6327594, by rfl⟩ : syracuseStep 16873585 = 12655189) B12655189
theorem B89992453 : Blo 2191435 89992453 := bstep (se 4 (by rfl) ⟨8436792, by rfl⟩ : syracuseStep 89992453 = 16873585) B16873585
theorem B119989937 : Blo 2191435 119989937 := bstep (se 2 (by rfl) ⟨44996226, by rfl⟩ : syracuseStep 119989937 = 89992453) B89992453
theorem B79993291 : Blo 2191435 79993291 := bstep (se 1 (by rfl) ⟨59994968, by rfl⟩ : syracuseStep 79993291 = 119989937) B119989937
theorem B106657721 : Blo 2191435 106657721 := bstep (se 2 (by rfl) ⟨39996645, by rfl⟩ : syracuseStep 106657721 = 79993291) B79993291
theorem B71105147 : Blo 2191435 71105147 := bstep (se 1 (by rfl) ⟨53328860, by rfl⟩ : syracuseStep 71105147 = 106657721) B106657721
theorem B47403431 : Blo 2191435 47403431 := bstep (se 1 (by rfl) ⟨35552573, by rfl⟩ : syracuseStep 47403431 = 71105147) B71105147
theorem B31602287 : Blo 2191435 31602287 := bstep (se 1 (by rfl) ⟨23701715, by rfl⟩ : syracuseStep 31602287 = 47403431) B47403431
theorem B21068191 : Blo 2191435 21068191 := bstep (se 1 (by rfl) ⟨15801143, by rfl⟩ : syracuseStep 21068191 = 31602287) B31602287
theorem B28090921 : Blo 2191435 28090921 := bstep (se 2 (by rfl) ⟨10534095, by rfl⟩ : syracuseStep 28090921 = 21068191) B21068191
theorem B37454561 : Blo 2191435 37454561 := bstep (se 2 (by rfl) ⟨14045460, by rfl⟩ : syracuseStep 37454561 = 28090921) B28090921
theorem B24969707 : Blo 2191435 24969707 := bstep (se 1 (by rfl) ⟨18727280, by rfl⟩ : syracuseStep 24969707 = 37454561) B37454561
theorem B16646471 : Blo 2191435 16646471 := bstep (se 1 (by rfl) ⟨12484853, by rfl⟩ : syracuseStep 16646471 = 24969707) B24969707
theorem B11097647 : Blo 2191435 11097647 := bstep (se 1 (by rfl) ⟨8323235, by rfl⟩ : syracuseStep 11097647 = 16646471) B16646471
theorem B7398431 : Blo 2191435 7398431 := bstep (se 1 (by rfl) ⟨5548823, by rfl⟩ : syracuseStep 7398431 = 11097647) B11097647
theorem B4932287 : Blo 2191435 4932287 := bstep (se 1 (by rfl) ⟨3699215, by rfl⟩ : syracuseStep 4932287 = 7398431) B7398431
theorem B3288191 : Blo 2191435 3288191 := bstep (se 1 (by rfl) ⟨2466143, by rfl⟩ : syracuseStep 3288191 = 4932287) B4932287
theorem B2192127 : Blo 2191435 2192127 := bstep (se 1 (by rfl) ⟨1644095, by rfl⟩ : syracuseStep 2192127 = 3288191) B3288191
theorem B3288197 : Blo 2191435 3288197 := bbase (se 4 (by rfl) ⟨308268, by rfl⟩ : syracuseStep 3288197 = 616537) (by norm_num)
theorem B2192131 : Blo 2191435 2192131 := bstep (se 1 (by rfl) ⟨1644098, by rfl⟩ : syracuseStep 2192131 = 3288197) B3288197
theorem B3699229 : Blo 2191435 3699229 := bbase (se 3 (by rfl) ⟨693605, by rfl⟩ : syracuseStep 3699229 = 1387211) (by norm_num)
theorem B4932305 : Blo 2191435 4932305 := bstep (se 2 (by rfl) ⟨1849614, by rfl⟩ : syracuseStep 4932305 = 3699229) B3699229
theorem B3288203 : Blo 2191435 3288203 := bstep (se 1 (by rfl) ⟨2466152, by rfl⟩ : syracuseStep 3288203 = 4932305) B4932305
theorem B2192135 : Blo 2191435 2192135 := bstep (se 1 (by rfl) ⟨1644101, by rfl⟩ : syracuseStep 2192135 = 3288203) B3288203
theorem B2466157 : Blo 2191435 2466157 := bbase (se 3 (by rfl) ⟨462404, by rfl⟩ : syracuseStep 2466157 = 924809) (by norm_num)
theorem B3288209 : Blo 2191435 3288209 := bstep (se 2 (by rfl) ⟨1233078, by rfl⟩ : syracuseStep 3288209 = 2466157) B2466157
theorem B2192139 : Blo 2191435 2192139 := bstep (se 1 (by rfl) ⟨1644104, by rfl⟩ : syracuseStep 2192139 = 3288209) B3288209
theorem B7398485 : Blo 2191435 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B4932323 : Blo 2191435 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B3288215 : Blo 2191435 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B2192143 : Blo 2191435 2192143 := bstep (se 1 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 2192143 = 3288215) B3288215
theorem B3288221 : Blo 2191435 3288221 := bbase (se 3 (by rfl) ⟨616541, by rfl⟩ : syracuseStep 3288221 = 1233083) (by norm_num)
theorem B2192147 : Blo 2191435 2192147 := bstep (se 1 (by rfl) ⟨1644110, by rfl⟩ : syracuseStep 2192147 = 3288221) B3288221
theorem B4932341 : Blo 2191435 4932341 := bbase (se 5 (by rfl) ⟨231203, by rfl⟩ : syracuseStep 4932341 = 462407) (by norm_num)
theorem B3288227 : Blo 2191435 3288227 := bstep (se 1 (by rfl) ⟨2466170, by rfl⟩ : syracuseStep 3288227 = 4932341) B4932341
theorem B2192151 : Blo 2191435 2192151 := bstep (se 1 (by rfl) ⟨1644113, by rfl⟩ : syracuseStep 2192151 = 3288227) B3288227
theorem B28091285 : Blo 2191435 28091285 := bbase (se 6 (by rfl) ⟨658389, by rfl⟩ : syracuseStep 28091285 = 1316779) (by norm_num)
theorem B18727523 : Blo 2191435 18727523 := bstep (se 1 (by rfl) ⟨14045642, by rfl⟩ : syracuseStep 18727523 = 28091285) B28091285
theorem B12485015 : Blo 2191435 12485015 := bstep (se 1 (by rfl) ⟨9363761, by rfl⟩ : syracuseStep 12485015 = 18727523) B18727523
theorem B8323343 : Blo 2191435 8323343 := bstep (se 1 (by rfl) ⟨6242507, by rfl⟩ : syracuseStep 8323343 = 12485015) B12485015
theorem B5548895 : Blo 2191435 5548895 := bstep (se 1 (by rfl) ⟨4161671, by rfl⟩ : syracuseStep 5548895 = 8323343) B8323343
theorem B3699263 : Blo 2191435 3699263 := bstep (se 1 (by rfl) ⟨2774447, by rfl⟩ : syracuseStep 3699263 = 5548895) B5548895
theorem B2466175 : Blo 2191435 2466175 := bstep (se 1 (by rfl) ⟨1849631, by rfl⟩ : syracuseStep 2466175 = 3699263) B3699263
theorem B3288233 : Blo 2191435 3288233 := bstep (se 2 (by rfl) ⟨1233087, by rfl⟩ : syracuseStep 3288233 = 2466175) B2466175
theorem B2192155 : Blo 2191435 2192155 := bstep (se 1 (by rfl) ⟨1644116, by rfl⟩ : syracuseStep 2192155 = 3288233) B3288233
theorem B10823669 : Blo 2191435 10823669 := bbase (se 5 (by rfl) ⟨507359, by rfl⟩ : syracuseStep 10823669 = 1014719) (by norm_num)
theorem B7215779 : Blo 2191435 7215779 := bstep (se 1 (by rfl) ⟨5411834, by rfl⟩ : syracuseStep 7215779 = 10823669) B10823669
theorem B4810519 : Blo 2191435 4810519 := bstep (se 1 (by rfl) ⟨3607889, by rfl⟩ : syracuseStep 4810519 = 7215779) B7215779
theorem B25656101 : Blo 2191435 25656101 := bstep (se 4 (by rfl) ⟨2405259, by rfl⟩ : syracuseStep 25656101 = 4810519) B4810519
theorem B17104067 : Blo 2191435 17104067 := bstep (se 1 (by rfl) ⟨12828050, by rfl⟩ : syracuseStep 17104067 = 25656101) B25656101
theorem B11402711 : Blo 2191435 11402711 := bstep (se 1 (by rfl) ⟨8552033, by rfl⟩ : syracuseStep 11402711 = 17104067) B17104067
theorem B7601807 : Blo 2191435 7601807 := bstep (se 1 (by rfl) ⟨5701355, by rfl⟩ : syracuseStep 7601807 = 11402711) B11402711
theorem B20271485 : Blo 2191435 20271485 := bstep (se 3 (by rfl) ⟨3800903, by rfl⟩ : syracuseStep 20271485 = 7601807) B7601807
theorem B13514323 : Blo 2191435 13514323 := bstep (se 1 (by rfl) ⟨10135742, by rfl⟩ : syracuseStep 13514323 = 20271485) B20271485
theorem B18019097 : Blo 2191435 18019097 := bstep (se 2 (by rfl) ⟨6757161, by rfl⟩ : syracuseStep 18019097 = 13514323) B13514323
theorem B12012731 : Blo 2191435 12012731 := bstep (se 1 (by rfl) ⟨9009548, by rfl⟩ : syracuseStep 12012731 = 18019097) B18019097
theorem B8008487 : Blo 2191435 8008487 := bstep (se 1 (by rfl) ⟨6006365, by rfl⟩ : syracuseStep 8008487 = 12012731) B12012731
theorem B5338991 : Blo 2191435 5338991 := bstep (se 1 (by rfl) ⟨4004243, by rfl⟩ : syracuseStep 5338991 = 8008487) B8008487
theorem B14237309 : Blo 2191435 14237309 := bstep (se 3 (by rfl) ⟨2669495, by rfl⟩ : syracuseStep 14237309 = 5338991) B5338991
theorem B9491539 : Blo 2191435 9491539 := bstep (se 1 (by rfl) ⟨7118654, by rfl⟩ : syracuseStep 9491539 = 14237309) B14237309
theorem B12655385 : Blo 2191435 12655385 := bstep (se 2 (by rfl) ⟨4745769, by rfl⟩ : syracuseStep 12655385 = 9491539) B9491539
theorem B8436923 : Blo 2191435 8436923 := bstep (se 1 (by rfl) ⟨6327692, by rfl⟩ : syracuseStep 8436923 = 12655385) B12655385
theorem B5624615 : Blo 2191435 5624615 := bstep (se 1 (by rfl) ⟨4218461, by rfl⟩ : syracuseStep 5624615 = 8436923) B8436923
theorem B3749743 : Blo 2191435 3749743 := bstep (se 1 (by rfl) ⟨2812307, by rfl⟩ : syracuseStep 3749743 = 5624615) B5624615
theorem B4999657 : Blo 2191435 4999657 := bstep (se 2 (by rfl) ⟨1874871, by rfl⟩ : syracuseStep 4999657 = 3749743) B3749743
theorem B6666209 : Blo 2191435 6666209 := bstep (se 2 (by rfl) ⟨2499828, by rfl⟩ : syracuseStep 6666209 = 4999657) B4999657
theorem B4444139 : Blo 2191435 4444139 := bstep (se 1 (by rfl) ⟨3333104, by rfl⟩ : syracuseStep 4444139 = 6666209) B6666209
theorem B2962759 : Blo 2191435 2962759 := bstep (se 1 (by rfl) ⟨2222069, by rfl⟩ : syracuseStep 2962759 = 4444139) B4444139
theorem B3950345 : Blo 2191435 3950345 := bstep (se 2 (by rfl) ⟨1481379, by rfl⟩ : syracuseStep 3950345 = 2962759) B2962759
theorem B2633563 : Blo 2191435 2633563 := bstep (se 1 (by rfl) ⟨1975172, by rfl⟩ : syracuseStep 2633563 = 3950345) B3950345
theorem B3511417 : Blo 2191435 3511417 := bstep (se 2 (by rfl) ⟨1316781, by rfl⟩ : syracuseStep 3511417 = 2633563) B2633563
theorem B4681889 : Blo 2191435 4681889 := bstep (se 2 (by rfl) ⟨1755708, by rfl⟩ : syracuseStep 4681889 = 3511417) B3511417
theorem B3121259 : Blo 2191435 3121259 := bstep (se 1 (by rfl) ⟨2340944, by rfl⟩ : syracuseStep 3121259 = 4681889) B4681889
theorem B8323357 : Blo 2191435 8323357 := bstep (se 3 (by rfl) ⟨1560629, by rfl⟩ : syracuseStep 8323357 = 3121259) B3121259
theorem B11097809 : Blo 2191435 11097809 := bstep (se 2 (by rfl) ⟨4161678, by rfl⟩ : syracuseStep 11097809 = 8323357) B8323357
theorem B7398539 : Blo 2191435 7398539 := bstep (se 1 (by rfl) ⟨5548904, by rfl⟩ : syracuseStep 7398539 = 11097809) B11097809
theorem B4932359 : Blo 2191435 4932359 := bstep (se 1 (by rfl) ⟨3699269, by rfl⟩ : syracuseStep 4932359 = 7398539) B7398539
theorem B3288239 : Blo 2191435 3288239 := bstep (se 1 (by rfl) ⟨2466179, by rfl⟩ : syracuseStep 3288239 = 4932359) B4932359
theorem B2192159 : Blo 2191435 2192159 := bstep (se 1 (by rfl) ⟨1644119, by rfl⟩ : syracuseStep 2192159 = 3288239) B3288239
theorem B3288245 : Blo 2191435 3288245 := bbase (se 5 (by rfl) ⟨154136, by rfl⟩ : syracuseStep 3288245 = 308273) (by norm_num)
theorem B2192163 : Blo 2191435 2192163 := bstep (se 1 (by rfl) ⟨1644122, by rfl⟩ : syracuseStep 2192163 = 3288245) B3288245
theorem B5548925 : Blo 2191435 5548925 := bbase (se 3 (by rfl) ⟨1040423, by rfl⟩ : syracuseStep 5548925 = 2080847) (by norm_num)
theorem B3699283 : Blo 2191435 3699283 := bstep (se 1 (by rfl) ⟨2774462, by rfl⟩ : syracuseStep 3699283 = 5548925) B5548925
theorem B4932377 : Blo 2191435 4932377 := bstep (se 2 (by rfl) ⟨1849641, by rfl⟩ : syracuseStep 4932377 = 3699283) B3699283
theorem B3288251 : Blo 2191435 3288251 := bstep (se 1 (by rfl) ⟨2466188, by rfl⟩ : syracuseStep 3288251 = 4932377) B4932377
theorem B2192167 : Blo 2191435 2192167 := bstep (se 1 (by rfl) ⟨1644125, by rfl⟩ : syracuseStep 2192167 = 3288251) B3288251
theorem B2466193 : Blo 2191435 2466193 := bbase (se 2 (by rfl) ⟨924822, by rfl⟩ : syracuseStep 2466193 = 1849645) (by norm_num)
theorem B3288257 : Blo 2191435 3288257 := bstep (se 2 (by rfl) ⟨1233096, by rfl⟩ : syracuseStep 3288257 = 2466193) B2466193
theorem B2192171 : Blo 2191435 2192171 := bstep (se 1 (by rfl) ⟨1644128, by rfl⟩ : syracuseStep 2192171 = 3288257) B3288257
theorem B4161709 : Blo 2191435 4161709 := bbase (se 3 (by rfl) ⟨780320, by rfl⟩ : syracuseStep 4161709 = 1560641) (by norm_num)
theorem B5548945 : Blo 2191435 5548945 := bstep (se 2 (by rfl) ⟨2080854, by rfl⟩ : syracuseStep 5548945 = 4161709) B4161709
theorem B7398593 : Blo 2191435 7398593 := bstep (se 2 (by rfl) ⟨2774472, by rfl⟩ : syracuseStep 7398593 = 5548945) B5548945
theorem B4932395 : Blo 2191435 4932395 := bstep (se 1 (by rfl) ⟨3699296, by rfl⟩ : syracuseStep 4932395 = 7398593) B7398593
theorem B3288263 : Blo 2191435 3288263 := bstep (se 1 (by rfl) ⟨2466197, by rfl⟩ : syracuseStep 3288263 = 4932395) B4932395
theorem B2192175 : Blo 2191435 2192175 := bstep (se 1 (by rfl) ⟨1644131, by rfl⟩ : syracuseStep 2192175 = 3288263) B3288263
theorem B3288269 : Blo 2191435 3288269 := bbase (se 3 (by rfl) ⟨616550, by rfl⟩ : syracuseStep 3288269 = 1233101) (by norm_num)
theorem B2192179 : Blo 2191435 2192179 := bstep (se 1 (by rfl) ⟨1644134, by rfl⟩ : syracuseStep 2192179 = 3288269) B3288269
theorem B4932413 : Blo 2191435 4932413 := bbase (se 3 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 4932413 = 1849655) (by norm_num)
theorem B3288275 : Blo 2191435 3288275 := bstep (se 1 (by rfl) ⟨2466206, by rfl⟩ : syracuseStep 3288275 = 4932413) B4932413
theorem B2192183 : Blo 2191435 2192183 := bstep (se 1 (by rfl) ⟨1644137, by rfl⟩ : syracuseStep 2192183 = 3288275) B3288275
theorem B3699317 : Blo 2191435 3699317 := bbase (se 5 (by rfl) ⟨173405, by rfl⟩ : syracuseStep 3699317 = 346811) (by norm_num)
theorem B2466211 : Blo 2191435 2466211 := bstep (se 1 (by rfl) ⟨1849658, by rfl⟩ : syracuseStep 2466211 = 3699317) B3699317
theorem B3288281 : Blo 2191435 3288281 := bstep (se 2 (by rfl) ⟨1233105, by rfl⟩ : syracuseStep 3288281 = 2466211) B2466211
theorem B2192187 : Blo 2191435 2192187 := bstep (se 1 (by rfl) ⟨1644140, by rfl⟩ : syracuseStep 2192187 = 3288281) B3288281
theorem B4681957 : Blo 2191435 4681957 := bbase (se 4 (by rfl) ⟨438933, by rfl⟩ : syracuseStep 4681957 = 877867) (by norm_num)
theorem B6242609 : Blo 2191435 6242609 := bstep (se 2 (by rfl) ⟨2340978, by rfl⟩ : syracuseStep 6242609 = 4681957) B4681957
theorem B16646957 : Blo 2191435 16646957 := bstep (se 3 (by rfl) ⟨3121304, by rfl⟩ : syracuseStep 16646957 = 6242609) B6242609
theorem B11097971 : Blo 2191435 11097971 := bstep (se 1 (by rfl) ⟨8323478, by rfl⟩ : syracuseStep 11097971 = 16646957) B16646957
theorem B7398647 : Blo 2191435 7398647 := bstep (se 1 (by rfl) ⟨5548985, by rfl⟩ : syracuseStep 7398647 = 11097971) B11097971
theorem B4932431 : Blo 2191435 4932431 := bstep (se 1 (by rfl) ⟨3699323, by rfl⟩ : syracuseStep 4932431 = 7398647) B7398647
theorem B3288287 : Blo 2191435 3288287 := bstep (se 1 (by rfl) ⟨2466215, by rfl⟩ : syracuseStep 3288287 = 4932431) B4932431
theorem B2192191 : Blo 2191435 2192191 := bstep (se 1 (by rfl) ⟨1644143, by rfl⟩ : syracuseStep 2192191 = 3288287) B3288287
theorem B3288293 : Blo 2191435 3288293 := bbase (se 4 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 3288293 = 616555) (by norm_num)
theorem B2192195 : Blo 2191435 2192195 := bstep (se 1 (by rfl) ⟨1644146, by rfl⟩ : syracuseStep 2192195 = 3288293) B3288293
theorem B2962813 : Blo 2191435 2962813 := bbase (se 3 (by rfl) ⟨555527, by rfl⟩ : syracuseStep 2962813 = 1111055) (by norm_num)
theorem B3950417 : Blo 2191435 3950417 := bstep (se 2 (by rfl) ⟨1481406, by rfl⟩ : syracuseStep 3950417 = 2962813) B2962813
theorem B10534445 : Blo 2191435 10534445 := bstep (se 3 (by rfl) ⟨1975208, by rfl⟩ : syracuseStep 10534445 = 3950417) B3950417
theorem B7022963 : Blo 2191435 7022963 := bstep (se 1 (by rfl) ⟨5267222, by rfl⟩ : syracuseStep 7022963 = 10534445) B10534445
theorem B4681975 : Blo 2191435 4681975 := bstep (se 1 (by rfl) ⟨3511481, by rfl⟩ : syracuseStep 4681975 = 7022963) B7022963
theorem B6242633 : Blo 2191435 6242633 := bstep (se 2 (by rfl) ⟨2340987, by rfl⟩ : syracuseStep 6242633 = 4681975) B4681975
theorem B4161755 : Blo 2191435 4161755 := bstep (se 1 (by rfl) ⟨3121316, by rfl⟩ : syracuseStep 4161755 = 6242633) B6242633
theorem B2774503 : Blo 2191435 2774503 := bstep (se 1 (by rfl) ⟨2080877, by rfl⟩ : syracuseStep 2774503 = 4161755) B4161755
theorem B3699337 : Blo 2191435 3699337 := bstep (se 2 (by rfl) ⟨1387251, by rfl⟩ : syracuseStep 3699337 = 2774503) B2774503
theorem B4932449 : Blo 2191435 4932449 := bstep (se 2 (by rfl) ⟨1849668, by rfl⟩ : syracuseStep 4932449 = 3699337) B3699337
theorem B3288299 : Blo 2191435 3288299 := bstep (se 1 (by rfl) ⟨2466224, by rfl⟩ : syracuseStep 3288299 = 4932449) B4932449
theorem B2192199 : Blo 2191435 2192199 := bstep (se 1 (by rfl) ⟨1644149, by rfl⟩ : syracuseStep 2192199 = 3288299) B3288299
theorem B2466229 : Blo 2191435 2466229 := bbase (se 5 (by rfl) ⟨115604, by rfl⟩ : syracuseStep 2466229 = 231209) (by norm_num)
theorem B3288305 : Blo 2191435 3288305 := bstep (se 2 (by rfl) ⟨1233114, by rfl⟩ : syracuseStep 3288305 = 2466229) B2466229
theorem B2192203 : Blo 2191435 2192203 := bstep (se 1 (by rfl) ⟨1644152, by rfl⟩ : syracuseStep 2192203 = 3288305) B3288305
theorem B2774513 : Blo 2191435 2774513 := bbase (se 2 (by rfl) ⟨1040442, by rfl⟩ : syracuseStep 2774513 = 2080885) (by norm_num)
theorem B7398701 : Blo 2191435 7398701 := bstep (se 3 (by rfl) ⟨1387256, by rfl⟩ : syracuseStep 7398701 = 2774513) B2774513
theorem B4932467 : Blo 2191435 4932467 := bstep (se 1 (by rfl) ⟨3699350, by rfl⟩ : syracuseStep 4932467 = 7398701) B7398701
theorem B3288311 : Blo 2191435 3288311 := bstep (se 1 (by rfl) ⟨2466233, by rfl⟩ : syracuseStep 3288311 = 4932467) B4932467
theorem B2192207 : Blo 2191435 2192207 := bstep (se 1 (by rfl) ⟨1644155, by rfl⟩ : syracuseStep 2192207 = 3288311) B3288311
theorem B3288317 : Blo 2191435 3288317 := bbase (se 3 (by rfl) ⟨616559, by rfl⟩ : syracuseStep 3288317 = 1233119) (by norm_num)
theorem B2192211 : Blo 2191435 2192211 := bstep (se 1 (by rfl) ⟨1644158, by rfl⟩ : syracuseStep 2192211 = 3288317) B3288317
theorem B4932485 : Blo 2191435 4932485 := bbase (se 4 (by rfl) ⟨462420, by rfl⟩ : syracuseStep 4932485 = 924841) (by norm_num)
theorem B3288323 : Blo 2191435 3288323 := bstep (se 1 (by rfl) ⟨2466242, by rfl⟩ : syracuseStep 3288323 = 4932485) B4932485
theorem B2192215 : Blo 2191435 2192215 := bstep (se 1 (by rfl) ⟨1644161, by rfl⟩ : syracuseStep 2192215 = 3288323) B3288323
theorem B2341009 : Blo 2191435 2341009 := bbase (se 2 (by rfl) ⟨877878, by rfl⟩ : syracuseStep 2341009 = 1755757) (by norm_num)
theorem B3121345 : Blo 2191435 3121345 := bstep (se 2 (by rfl) ⟨1170504, by rfl⟩ : syracuseStep 3121345 = 2341009) B2341009
theorem B4161793 : Blo 2191435 4161793 := bstep (se 2 (by rfl) ⟨1560672, by rfl⟩ : syracuseStep 4161793 = 3121345) B3121345
theorem B5549057 : Blo 2191435 5549057 := bstep (se 2 (by rfl) ⟨2080896, by rfl⟩ : syracuseStep 5549057 = 4161793) B4161793
theorem B3699371 : Blo 2191435 3699371 := bstep (se 1 (by rfl) ⟨2774528, by rfl⟩ : syracuseStep 3699371 = 5549057) B5549057
theorem B2466247 : Blo 2191435 2466247 := bstep (se 1 (by rfl) ⟨1849685, by rfl⟩ : syracuseStep 2466247 = 3699371) B3699371
theorem B3288329 : Blo 2191435 3288329 := bstep (se 2 (by rfl) ⟨1233123, by rfl⟩ : syracuseStep 3288329 = 2466247) B2466247
theorem B2192219 : Blo 2191435 2192219 := bstep (se 1 (by rfl) ⟨1644164, by rfl⟩ : syracuseStep 2192219 = 3288329) B3288329
theorem B11098133 : Blo 2191435 11098133 := bbase (se 6 (by rfl) ⟨260112, by rfl⟩ : syracuseStep 11098133 = 520225) (by norm_num)
theorem B7398755 : Blo 2191435 7398755 := bstep (se 1 (by rfl) ⟨5549066, by rfl⟩ : syracuseStep 7398755 = 11098133) B11098133
theorem B4932503 : Blo 2191435 4932503 := bstep (se 1 (by rfl) ⟨3699377, by rfl⟩ : syracuseStep 4932503 = 7398755) B7398755
theorem B3288335 : Blo 2191435 3288335 := bstep (se 1 (by rfl) ⟨2466251, by rfl⟩ : syracuseStep 3288335 = 4932503) B4932503
theorem B2192223 : Blo 2191435 2192223 := bstep (se 1 (by rfl) ⟨1644167, by rfl⟩ : syracuseStep 2192223 = 3288335) B3288335
theorem B3288341 : Blo 2191435 3288341 := bbase (se 6 (by rfl) ⟨77070, by rfl⟩ : syracuseStep 3288341 = 154141) (by norm_num)
theorem B2192227 : Blo 2191435 2192227 := bstep (se 1 (by rfl) ⟨1644170, by rfl⟩ : syracuseStep 2192227 = 3288341) B3288341
theorem B39998549 : Blo 2191435 39998549 := bbase (se 8 (by rfl) ⟨234366, by rfl⟩ : syracuseStep 39998549 = 468733) (by norm_num)
theorem B26665699 : Blo 2191435 26665699 := bstep (se 1 (by rfl) ⟨19999274, by rfl⟩ : syracuseStep 26665699 = 39998549) B39998549
theorem B35554265 : Blo 2191435 35554265 := bstep (se 2 (by rfl) ⟨13332849, by rfl⟩ : syracuseStep 35554265 = 26665699) B26665699
theorem B23702843 : Blo 2191435 23702843 := bstep (se 1 (by rfl) ⟨17777132, by rfl⟩ : syracuseStep 23702843 = 35554265) B35554265
theorem B15801895 : Blo 2191435 15801895 := bstep (se 1 (by rfl) ⟨11851421, by rfl⟩ : syracuseStep 15801895 = 23702843) B23702843
theorem B21069193 : Blo 2191435 21069193 := bstep (se 2 (by rfl) ⟨7900947, by rfl⟩ : syracuseStep 21069193 = 15801895) B15801895
theorem B28092257 : Blo 2191435 28092257 := bstep (se 2 (by rfl) ⟨10534596, by rfl⟩ : syracuseStep 28092257 = 21069193) B21069193
theorem B18728171 : Blo 2191435 18728171 := bstep (se 1 (by rfl) ⟨14046128, by rfl⟩ : syracuseStep 18728171 = 28092257) B28092257
theorem B12485447 : Blo 2191435 12485447 := bstep (se 1 (by rfl) ⟨9364085, by rfl⟩ : syracuseStep 12485447 = 18728171) B18728171
theorem B8323631 : Blo 2191435 8323631 := bstep (se 1 (by rfl) ⟨6242723, by rfl⟩ : syracuseStep 8323631 = 12485447) B12485447
theorem B5549087 : Blo 2191435 5549087 := bstep (se 1 (by rfl) ⟨4161815, by rfl⟩ : syracuseStep 5549087 = 8323631) B8323631
theorem B3699391 : Blo 2191435 3699391 := bstep (se 1 (by rfl) ⟨2774543, by rfl⟩ : syracuseStep 3699391 = 5549087) B5549087
theorem B4932521 : Blo 2191435 4932521 := bstep (se 2 (by rfl) ⟨1849695, by rfl⟩ : syracuseStep 4932521 = 3699391) B3699391
theorem B3288347 : Blo 2191435 3288347 := bstep (se 1 (by rfl) ⟨2466260, by rfl⟩ : syracuseStep 3288347 = 4932521) B4932521
theorem B2192231 : Blo 2191435 2192231 := bstep (se 1 (by rfl) ⟨1644173, by rfl⟩ : syracuseStep 2192231 = 3288347) B3288347
theorem B2466265 : Blo 2191435 2466265 := bbase (se 2 (by rfl) ⟨924849, by rfl⟩ : syracuseStep 2466265 = 1849699) (by norm_num)
theorem B3288353 : Blo 2191435 3288353 := bstep (se 2 (by rfl) ⟨1233132, by rfl⟩ : syracuseStep 3288353 = 2466265) B2466265
theorem B2192235 : Blo 2191435 2192235 := bstep (se 1 (by rfl) ⟨1644176, by rfl⟩ : syracuseStep 2192235 = 3288353) B3288353
theorem B3121373 : Blo 2191435 3121373 := bbase (se 3 (by rfl) ⟨585257, by rfl⟩ : syracuseStep 3121373 = 1170515) (by norm_num)
theorem B8323661 : Blo 2191435 8323661 := bstep (se 3 (by rfl) ⟨1560686, by rfl⟩ : syracuseStep 8323661 = 3121373) B3121373
theorem B5549107 : Blo 2191435 5549107 := bstep (se 1 (by rfl) ⟨4161830, by rfl⟩ : syracuseStep 5549107 = 8323661) B8323661
theorem B7398809 : Blo 2191435 7398809 := bstep (se 2 (by rfl) ⟨2774553, by rfl⟩ : syracuseStep 7398809 = 5549107) B5549107
theorem B4932539 : Blo 2191435 4932539 := bstep (se 1 (by rfl) ⟨3699404, by rfl⟩ : syracuseStep 4932539 = 7398809) B7398809
theorem B3288359 : Blo 2191435 3288359 := bstep (se 1 (by rfl) ⟨2466269, by rfl⟩ : syracuseStep 3288359 = 4932539) B4932539
theorem B2192239 : Blo 2191435 2192239 := bstep (se 1 (by rfl) ⟨1644179, by rfl⟩ : syracuseStep 2192239 = 3288359) B3288359
theorem B3288365 : Blo 2191435 3288365 := bbase (se 3 (by rfl) ⟨616568, by rfl⟩ : syracuseStep 3288365 = 1233137) (by norm_num)
theorem B2192243 : Blo 2191435 2192243 := bstep (se 1 (by rfl) ⟨1644182, by rfl⟩ : syracuseStep 2192243 = 3288365) B3288365
theorem B4932557 : Blo 2191435 4932557 := bbase (se 3 (by rfl) ⟨924854, by rfl⟩ : syracuseStep 4932557 = 1849709) (by norm_num)
theorem B3288371 : Blo 2191435 3288371 := bstep (se 1 (by rfl) ⟨2466278, by rfl⟩ : syracuseStep 3288371 = 4932557) B4932557
theorem B2192247 : Blo 2191435 2192247 := bstep (se 1 (by rfl) ⟨1644185, by rfl⟩ : syracuseStep 2192247 = 3288371) B3288371
theorem B2774569 : Blo 2191435 2774569 := bbase (se 2 (by rfl) ⟨1040463, by rfl⟩ : syracuseStep 2774569 = 2080927) (by norm_num)
theorem B3699425 : Blo 2191435 3699425 := bstep (se 2 (by rfl) ⟨1387284, by rfl⟩ : syracuseStep 3699425 = 2774569) B2774569
theorem B2466283 : Blo 2191435 2466283 := bstep (se 1 (by rfl) ⟨1849712, by rfl⟩ : syracuseStep 2466283 = 3699425) B3699425
theorem B3288377 : Blo 2191435 3288377 := bstep (se 2 (by rfl) ⟨1233141, by rfl⟩ : syracuseStep 3288377 = 2466283) B2466283
theorem B2192251 : Blo 2191435 2192251 := bstep (se 1 (by rfl) ⟨1644188, by rfl⟩ : syracuseStep 2192251 = 3288377) B3288377
theorem B2812429 : Blo 2191435 2812429 := bbase (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) (by norm_num)
theorem B3749905 : Blo 2191435 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B19999493 : Blo 2191435 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B13332995 : Blo 2191435 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B8888663 : Blo 2191435 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B23703101 : Blo 2191435 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B15802067 : Blo 2191435 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B10534711 : Blo 2191435 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B14046281 : Blo 2191435 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B9364187 : Blo 2191435 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B24971165 : Blo 2191435 24971165 := bstep (se 3 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 24971165 = 9364187) B9364187
theorem B16647443 : Blo 2191435 16647443 := bstep (se 1 (by rfl) ⟨12485582, by rfl⟩ : syracuseStep 16647443 = 24971165) B24971165
theorem B11098295 : Blo 2191435 11098295 := bstep (se 1 (by rfl) ⟨8323721, by rfl⟩ : syracuseStep 11098295 = 16647443) B16647443
theorem B7398863 : Blo 2191435 7398863 := bstep (se 1 (by rfl) ⟨5549147, by rfl⟩ : syracuseStep 7398863 = 11098295) B11098295
theorem B4932575 : Blo 2191435 4932575 := bstep (se 1 (by rfl) ⟨3699431, by rfl⟩ : syracuseStep 4932575 = 7398863) B7398863
theorem B3288383 : Blo 2191435 3288383 := bstep (se 1 (by rfl) ⟨2466287, by rfl⟩ : syracuseStep 3288383 = 4932575) B4932575
theorem B2192255 : Blo 2191435 2192255 := bstep (se 1 (by rfl) ⟨1644191, by rfl⟩ : syracuseStep 2192255 = 3288383) B3288383
theorem B3288389 : Blo 2191435 3288389 := bbase (se 4 (by rfl) ⟨308286, by rfl⟩ : syracuseStep 3288389 = 616573) (by norm_num)
theorem B2192259 : Blo 2191435 2192259 := bstep (se 1 (by rfl) ⟨1644194, by rfl⟩ : syracuseStep 2192259 = 3288389) B3288389
theorem B3699445 : Blo 2191435 3699445 := bbase (se 5 (by rfl) ⟨173411, by rfl⟩ : syracuseStep 3699445 = 346823) (by norm_num)
theorem B4932593 : Blo 2191435 4932593 := bstep (se 2 (by rfl) ⟨1849722, by rfl⟩ : syracuseStep 4932593 = 3699445) B3699445
theorem B3288395 : Blo 2191435 3288395 := bstep (se 1 (by rfl) ⟨2466296, by rfl⟩ : syracuseStep 3288395 = 4932593) B4932593
theorem B2192263 : Blo 2191435 2192263 := bstep (se 1 (by rfl) ⟨1644197, by rfl⟩ : syracuseStep 2192263 = 3288395) B3288395
theorem B2466301 : Blo 2191435 2466301 := bbase (se 3 (by rfl) ⟨462431, by rfl⟩ : syracuseStep 2466301 = 924863) (by norm_num)
theorem B3288401 : Blo 2191435 3288401 := bstep (se 2 (by rfl) ⟨1233150, by rfl⟩ : syracuseStep 3288401 = 2466301) B2466301
theorem B2192267 : Blo 2191435 2192267 := bstep (se 1 (by rfl) ⟨1644200, by rfl⟩ : syracuseStep 2192267 = 3288401) B3288401
theorem B7398917 : Blo 2191435 7398917 := bbase (se 4 (by rfl) ⟨693648, by rfl⟩ : syracuseStep 7398917 = 1387297) (by norm_num)
theorem B4932611 : Blo 2191435 4932611 := bstep (se 1 (by rfl) ⟨3699458, by rfl⟩ : syracuseStep 4932611 = 7398917) B7398917
theorem B3288407 : Blo 2191435 3288407 := bstep (se 1 (by rfl) ⟨2466305, by rfl⟩ : syracuseStep 3288407 = 4932611) B4932611
theorem B2192271 : Blo 2191435 2192271 := bstep (se 1 (by rfl) ⟨1644203, by rfl⟩ : syracuseStep 2192271 = 3288407) B3288407
theorem B3288413 : Blo 2191435 3288413 := bbase (se 3 (by rfl) ⟨616577, by rfl⟩ : syracuseStep 3288413 = 1233155) (by norm_num)
theorem B2192275 : Blo 2191435 2192275 := bstep (se 1 (by rfl) ⟨1644206, by rfl⟩ : syracuseStep 2192275 = 3288413) B3288413
theorem B4932629 : Blo 2191435 4932629 := bbase (se 6 (by rfl) ⟨115608, by rfl⟩ : syracuseStep 4932629 = 231217) (by norm_num)
theorem B3288419 : Blo 2191435 3288419 := bstep (se 1 (by rfl) ⟨2466314, by rfl⟩ : syracuseStep 3288419 = 4932629) B4932629
theorem B2192279 : Blo 2191435 2192279 := bstep (se 1 (by rfl) ⟨1644209, by rfl⟩ : syracuseStep 2192279 = 3288419) B3288419
theorem B8323829 : Blo 2191435 8323829 := bbase (se 5 (by rfl) ⟨390179, by rfl⟩ : syracuseStep 8323829 = 780359) (by norm_num)
theorem B5549219 : Blo 2191435 5549219 := bstep (se 1 (by rfl) ⟨4161914, by rfl⟩ : syracuseStep 5549219 = 8323829) B8323829
theorem B3699479 : Blo 2191435 3699479 := bstep (se 1 (by rfl) ⟨2774609, by rfl⟩ : syracuseStep 3699479 = 5549219) B5549219
theorem B2466319 : Blo 2191435 2466319 := bstep (se 1 (by rfl) ⟨1849739, by rfl⟩ : syracuseStep 2466319 = 3699479) B3699479
theorem B3288425 : Blo 2191435 3288425 := bstep (se 2 (by rfl) ⟨1233159, by rfl⟩ : syracuseStep 3288425 = 2466319) B2466319
theorem B2192283 : Blo 2191435 2192283 := bstep (se 1 (by rfl) ⟨1644212, by rfl⟩ : syracuseStep 2192283 = 3288425) B3288425
theorem B2341081 : Blo 2191435 2341081 := bbase (se 2 (by rfl) ⟨877905, by rfl⟩ : syracuseStep 2341081 = 1755811) (by norm_num)
theorem B12485765 : Blo 2191435 12485765 := bstep (se 4 (by rfl) ⟨1170540, by rfl⟩ : syracuseStep 12485765 = 2341081) B2341081
theorem B8323843 : Blo 2191435 8323843 := bstep (se 1 (by rfl) ⟨6242882, by rfl⟩ : syracuseStep 8323843 = 12485765) B12485765
theorem B11098457 : Blo 2191435 11098457 := bstep (se 2 (by rfl) ⟨4161921, by rfl⟩ : syracuseStep 11098457 = 8323843) B8323843
theorem B7398971 : Blo 2191435 7398971 := bstep (se 1 (by rfl) ⟨5549228, by rfl⟩ : syracuseStep 7398971 = 11098457) B11098457
theorem B4932647 : Blo 2191435 4932647 := bstep (se 1 (by rfl) ⟨3699485, by rfl⟩ : syracuseStep 4932647 = 7398971) B7398971
theorem B3288431 : Blo 2191435 3288431 := bstep (se 1 (by rfl) ⟨2466323, by rfl⟩ : syracuseStep 3288431 = 4932647) B4932647
theorem B2192287 : Blo 2191435 2192287 := bstep (se 1 (by rfl) ⟨1644215, by rfl⟩ : syracuseStep 2192287 = 3288431) B3288431
theorem B3288437 : Blo 2191435 3288437 := bbase (se 5 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 3288437 = 308291) (by norm_num)
theorem B2192291 : Blo 2191435 2192291 := bstep (se 1 (by rfl) ⟨1644218, by rfl⟩ : syracuseStep 2192291 = 3288437) B3288437
theorem B3121453 : Blo 2191435 3121453 := bbase (se 3 (by rfl) ⟨585272, by rfl⟩ : syracuseStep 3121453 = 1170545) (by norm_num)
theorem B4161937 : Blo 2191435 4161937 := bstep (se 2 (by rfl) ⟨1560726, by rfl⟩ : syracuseStep 4161937 = 3121453) B3121453
theorem B5549249 : Blo 2191435 5549249 := bstep (se 2 (by rfl) ⟨2080968, by rfl⟩ : syracuseStep 5549249 = 4161937) B4161937
theorem B3699499 : Blo 2191435 3699499 := bstep (se 1 (by rfl) ⟨2774624, by rfl⟩ : syracuseStep 3699499 = 5549249) B5549249
theorem B4932665 : Blo 2191435 4932665 := bstep (se 2 (by rfl) ⟨1849749, by rfl⟩ : syracuseStep 4932665 = 3699499) B3699499
theorem B3288443 : Blo 2191435 3288443 := bstep (se 1 (by rfl) ⟨2466332, by rfl⟩ : syracuseStep 3288443 = 4932665) B4932665
theorem B2192295 : Blo 2191435 2192295 := bstep (se 1 (by rfl) ⟨1644221, by rfl⟩ : syracuseStep 2192295 = 3288443) B3288443
theorem B2466337 : Blo 2191435 2466337 := bbase (se 2 (by rfl) ⟨924876, by rfl⟩ : syracuseStep 2466337 = 1849753) (by norm_num)
theorem B3288449 : Blo 2191435 3288449 := bstep (se 2 (by rfl) ⟨1233168, by rfl⟩ : syracuseStep 3288449 = 2466337) B2466337
theorem B2192299 : Blo 2191435 2192299 := bstep (se 1 (by rfl) ⟨1644224, by rfl⟩ : syracuseStep 2192299 = 3288449) B3288449
theorem B5549269 : Blo 2191435 5549269 := bbase (se 7 (by rfl) ⟨65030, by rfl⟩ : syracuseStep 5549269 = 130061) (by norm_num)
theorem B7399025 : Blo 2191435 7399025 := bstep (se 2 (by rfl) ⟨2774634, by rfl⟩ : syracuseStep 7399025 = 5549269) B5549269
theorem B4932683 : Blo 2191435 4932683 := bstep (se 1 (by rfl) ⟨3699512, by rfl⟩ : syracuseStep 4932683 = 7399025) B7399025
theorem B3288455 : Blo 2191435 3288455 := bstep (se 1 (by rfl) ⟨2466341, by rfl⟩ : syracuseStep 3288455 = 4932683) B4932683
theorem B2192303 : Blo 2191435 2192303 := bstep (se 1 (by rfl) ⟨1644227, by rfl⟩ : syracuseStep 2192303 = 3288455) B3288455
theorem B3288461 : Blo 2191435 3288461 := bbase (se 3 (by rfl) ⟨616586, by rfl⟩ : syracuseStep 3288461 = 1233173) (by norm_num)
theorem B2192307 : Blo 2191435 2192307 := bstep (se 1 (by rfl) ⟨1644230, by rfl⟩ : syracuseStep 2192307 = 3288461) B3288461
theorem B4932701 : Blo 2191435 4932701 := bbase (se 3 (by rfl) ⟨924881, by rfl⟩ : syracuseStep 4932701 = 1849763) (by norm_num)
theorem B3288467 : Blo 2191435 3288467 := bstep (se 1 (by rfl) ⟨2466350, by rfl⟩ : syracuseStep 3288467 = 4932701) B4932701
theorem B2192311 : Blo 2191435 2192311 := bstep (se 1 (by rfl) ⟨1644233, by rfl⟩ : syracuseStep 2192311 = 3288467) B3288467
theorem B3699533 : Blo 2191435 3699533 := bbase (se 3 (by rfl) ⟨693662, by rfl⟩ : syracuseStep 3699533 = 1387325) (by norm_num)
theorem B2466355 : Blo 2191435 2466355 := bstep (se 1 (by rfl) ⟨1849766, by rfl⟩ : syracuseStep 2466355 = 3699533) B3699533
theorem B3288473 : Blo 2191435 3288473 := bstep (se 2 (by rfl) ⟨1233177, by rfl⟩ : syracuseStep 3288473 = 2466355) B2466355
theorem B2192315 : Blo 2191435 2192315 := bstep (se 1 (by rfl) ⟨1644236, by rfl⟩ : syracuseStep 2192315 = 3288473) B3288473
theorem B21070037 : Blo 2191435 21070037 := bbase (se 7 (by rfl) ⟨246914, by rfl⟩ : syracuseStep 21070037 = 493829) (by norm_num)
theorem B14046691 : Blo 2191435 14046691 := bstep (se 1 (by rfl) ⟨10535018, by rfl⟩ : syracuseStep 14046691 = 21070037) B21070037
theorem B18728921 : Blo 2191435 18728921 := bstep (se 2 (by rfl) ⟨7023345, by rfl⟩ : syracuseStep 18728921 = 14046691) B14046691
theorem B12485947 : Blo 2191435 12485947 := bstep (se 1 (by rfl) ⟨9364460, by rfl⟩ : syracuseStep 12485947 = 18728921) B18728921
theorem B16647929 : Blo 2191435 16647929 := bstep (se 2 (by rfl) ⟨6242973, by rfl⟩ : syracuseStep 16647929 = 12485947) B12485947
theorem B11098619 : Blo 2191435 11098619 := bstep (se 1 (by rfl) ⟨8323964, by rfl⟩ : syracuseStep 11098619 = 16647929) B16647929
theorem B7399079 : Blo 2191435 7399079 := bstep (se 1 (by rfl) ⟨5549309, by rfl⟩ : syracuseStep 7399079 = 11098619) B11098619
theorem B4932719 : Blo 2191435 4932719 := bstep (se 1 (by rfl) ⟨3699539, by rfl⟩ : syracuseStep 4932719 = 7399079) B7399079
theorem B3288479 : Blo 2191435 3288479 := bstep (se 1 (by rfl) ⟨2466359, by rfl⟩ : syracuseStep 3288479 = 4932719) B4932719
theorem B2192319 : Blo 2191435 2192319 := bstep (se 1 (by rfl) ⟨1644239, by rfl⟩ : syracuseStep 2192319 = 3288479) B3288479
theorem B3288485 : Blo 2191435 3288485 := bbase (se 4 (by rfl) ⟨308295, by rfl⟩ : syracuseStep 3288485 = 616591) (by norm_num)
theorem B2192323 : Blo 2191435 2192323 := bstep (se 1 (by rfl) ⟨1644242, by rfl⟩ : syracuseStep 2192323 = 3288485) B3288485
theorem B2774665 : Blo 2191435 2774665 := bbase (se 2 (by rfl) ⟨1040499, by rfl⟩ : syracuseStep 2774665 = 2080999) (by norm_num)
theorem B3699553 : Blo 2191435 3699553 := bstep (se 2 (by rfl) ⟨1387332, by rfl⟩ : syracuseStep 3699553 = 2774665) B2774665
theorem B4932737 : Blo 2191435 4932737 := bstep (se 2 (by rfl) ⟨1849776, by rfl⟩ : syracuseStep 4932737 = 3699553) B3699553
theorem B3288491 : Blo 2191435 3288491 := bstep (se 1 (by rfl) ⟨2466368, by rfl⟩ : syracuseStep 3288491 = 4932737) B4932737
theorem B2192327 : Blo 2191435 2192327 := bstep (se 1 (by rfl) ⟨1644245, by rfl⟩ : syracuseStep 2192327 = 3288491) B3288491
theorem B2466373 : Blo 2191435 2466373 := bbase (se 4 (by rfl) ⟨231222, by rfl⟩ : syracuseStep 2466373 = 462445) (by norm_num)
theorem B3288497 : Blo 2191435 3288497 := bstep (se 2 (by rfl) ⟨1233186, by rfl⟩ : syracuseStep 3288497 = 2466373) B2466373
theorem B2192331 : Blo 2191435 2192331 := bstep (se 1 (by rfl) ⟨1644248, by rfl⟩ : syracuseStep 2192331 = 3288497) B3288497
theorem B4162013 : Blo 2191435 4162013 := bbase (se 3 (by rfl) ⟨780377, by rfl⟩ : syracuseStep 4162013 = 1560755) (by norm_num)
theorem B2774675 : Blo 2191435 2774675 := bstep (se 1 (by rfl) ⟨2081006, by rfl⟩ : syracuseStep 2774675 = 4162013) B4162013
theorem B7399133 : Blo 2191435 7399133 := bstep (se 3 (by rfl) ⟨1387337, by rfl⟩ : syracuseStep 7399133 = 2774675) B2774675
theorem B4932755 : Blo 2191435 4932755 := bstep (se 1 (by rfl) ⟨3699566, by rfl⟩ : syracuseStep 4932755 = 7399133) B7399133
theorem B3288503 : Blo 2191435 3288503 := bstep (se 1 (by rfl) ⟨2466377, by rfl⟩ : syracuseStep 3288503 = 4932755) B4932755
theorem B2192335 : Blo 2191435 2192335 := bstep (se 1 (by rfl) ⟨1644251, by rfl⟩ : syracuseStep 2192335 = 3288503) B3288503
theorem B3288509 : Blo 2191435 3288509 := bbase (se 3 (by rfl) ⟨616595, by rfl⟩ : syracuseStep 3288509 = 1233191) (by norm_num)
theorem B2192339 : Blo 2191435 2192339 := bstep (se 1 (by rfl) ⟨1644254, by rfl⟩ : syracuseStep 2192339 = 3288509) B3288509
theorem B4932773 : Blo 2191435 4932773 := bbase (se 4 (by rfl) ⟨462447, by rfl⟩ : syracuseStep 4932773 = 924895) (by norm_num)
theorem B3288515 : Blo 2191435 3288515 := bstep (se 1 (by rfl) ⟨2466386, by rfl⟩ : syracuseStep 3288515 = 4932773) B4932773
theorem B2192343 : Blo 2191435 2192343 := bstep (se 1 (by rfl) ⟨1644257, by rfl⟩ : syracuseStep 2192343 = 3288515) B3288515
theorem B5549381 : Blo 2191435 5549381 := bbase (se 4 (by rfl) ⟨520254, by rfl⟩ : syracuseStep 5549381 = 1040509) (by norm_num)
theorem B3699587 : Blo 2191435 3699587 := bstep (se 1 (by rfl) ⟨2774690, by rfl⟩ : syracuseStep 3699587 = 5549381) B5549381
theorem B2466391 : Blo 2191435 2466391 := bstep (se 1 (by rfl) ⟨1849793, by rfl⟩ : syracuseStep 2466391 = 3699587) B3699587
theorem B3288521 : Blo 2191435 3288521 := bstep (se 2 (by rfl) ⟨1233195, by rfl⟩ : syracuseStep 3288521 = 2466391) B2466391
theorem B2192347 : Blo 2191435 2192347 := bstep (se 1 (by rfl) ⟨1644260, by rfl⟩ : syracuseStep 2192347 = 3288521) B3288521
theorem B7901381 : Blo 2191435 7901381 := bbase (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) (by norm_num)
theorem B5267587 : Blo 2191435 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B7023449 : Blo 2191435 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B4682299 : Blo 2191435 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B6243065 : Blo 2191435 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B4162043 : Blo 2191435 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B11098781 : Blo 2191435 11098781 := bstep (se 3 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 11098781 = 4162043) B4162043
theorem B7399187 : Blo 2191435 7399187 := bstep (se 1 (by rfl) ⟨5549390, by rfl⟩ : syracuseStep 7399187 = 11098781) B11098781
theorem B4932791 : Blo 2191435 4932791 := bstep (se 1 (by rfl) ⟨3699593, by rfl⟩ : syracuseStep 4932791 = 7399187) B7399187
theorem B3288527 : Blo 2191435 3288527 := bstep (se 1 (by rfl) ⟨2466395, by rfl⟩ : syracuseStep 3288527 = 4932791) B4932791
theorem B2192351 : Blo 2191435 2192351 := bstep (se 1 (by rfl) ⟨1644263, by rfl⟩ : syracuseStep 2192351 = 3288527) B3288527
theorem B3288533 : Blo 2191435 3288533 := bbase (se 7 (by rfl) ⟨38537, by rfl⟩ : syracuseStep 3288533 = 77075) (by norm_num)
theorem B2192355 : Blo 2191435 2192355 := bstep (se 1 (by rfl) ⟨1644266, by rfl⟩ : syracuseStep 2192355 = 3288533) B3288533
theorem B8324117 : Blo 2191435 8324117 := bbase (se 6 (by rfl) ⟨195096, by rfl⟩ : syracuseStep 8324117 = 390193) (by norm_num)
theorem B5549411 : Blo 2191435 5549411 := bstep (se 1 (by rfl) ⟨4162058, by rfl⟩ : syracuseStep 5549411 = 8324117) B8324117
theorem B3699607 : Blo 2191435 3699607 := bstep (se 1 (by rfl) ⟨2774705, by rfl⟩ : syracuseStep 3699607 = 5549411) B5549411
theorem B4932809 : Blo 2191435 4932809 := bstep (se 2 (by rfl) ⟨1849803, by rfl⟩ : syracuseStep 4932809 = 3699607) B3699607
theorem B3288539 : Blo 2191435 3288539 := bstep (se 1 (by rfl) ⟨2466404, by rfl⟩ : syracuseStep 3288539 = 4932809) B4932809
theorem B2192359 : Blo 2191435 2192359 := bstep (se 1 (by rfl) ⟨1644269, by rfl⟩ : syracuseStep 2192359 = 3288539) B3288539
theorem B2466409 : Blo 2191435 2466409 := bbase (se 2 (by rfl) ⟨924903, by rfl⟩ : syracuseStep 2466409 = 1849807) (by norm_num)
theorem B3288545 : Blo 2191435 3288545 := bstep (se 2 (by rfl) ⟨1233204, by rfl⟩ : syracuseStep 3288545 = 2466409) B2466409
theorem B2192363 : Blo 2191435 2192363 := bstep (se 1 (by rfl) ⟨1644272, by rfl⟩ : syracuseStep 2192363 = 3288545) B3288545
theorem B4682333 : Blo 2191435 4682333 := bbase (se 3 (by rfl) ⟨877937, by rfl⟩ : syracuseStep 4682333 = 1755875) (by norm_num)
theorem B12486221 : Blo 2191435 12486221 := bstep (se 3 (by rfl) ⟨2341166, by rfl⟩ : syracuseStep 12486221 = 4682333) B4682333
theorem B8324147 : Blo 2191435 8324147 := bstep (se 1 (by rfl) ⟨6243110, by rfl⟩ : syracuseStep 8324147 = 12486221) B12486221
theorem B5549431 : Blo 2191435 5549431 := bstep (se 1 (by rfl) ⟨4162073, by rfl⟩ : syracuseStep 5549431 = 8324147) B8324147
theorem B7399241 : Blo 2191435 7399241 := bstep (se 2 (by rfl) ⟨2774715, by rfl⟩ : syracuseStep 7399241 = 5549431) B5549431
theorem B4932827 : Blo 2191435 4932827 := bstep (se 1 (by rfl) ⟨3699620, by rfl⟩ : syracuseStep 4932827 = 7399241) B7399241
theorem B3288551 : Blo 2191435 3288551 := bstep (se 1 (by rfl) ⟨2466413, by rfl⟩ : syracuseStep 3288551 = 4932827) B4932827
theorem B2192367 : Blo 2191435 2192367 := bstep (se 1 (by rfl) ⟨1644275, by rfl⟩ : syracuseStep 2192367 = 3288551) B3288551
theorem B3288557 : Blo 2191435 3288557 := bbase (se 3 (by rfl) ⟨616604, by rfl⟩ : syracuseStep 3288557 = 1233209) (by norm_num)
theorem B2192371 : Blo 2191435 2192371 := bstep (se 1 (by rfl) ⟨1644278, by rfl⟩ : syracuseStep 2192371 = 3288557) B3288557
theorem B4932845 : Blo 2191435 4932845 := bbase (se 3 (by rfl) ⟨924908, by rfl⟩ : syracuseStep 4932845 = 1849817) (by norm_num)
theorem B3288563 : Blo 2191435 3288563 := bstep (se 1 (by rfl) ⟨2466422, by rfl⟩ : syracuseStep 3288563 = 4932845) B4932845
theorem B2192375 : Blo 2191435 2192375 := bstep (se 1 (by rfl) ⟨1644281, by rfl⟩ : syracuseStep 2192375 = 3288563) B3288563
theorem B3121573 : Blo 2191435 3121573 := bbase (se 4 (by rfl) ⟨292647, by rfl⟩ : syracuseStep 3121573 = 585295) (by norm_num)
theorem B4162097 : Blo 2191435 4162097 := bstep (se 2 (by rfl) ⟨1560786, by rfl⟩ : syracuseStep 4162097 = 3121573) B3121573
theorem B2774731 : Blo 2191435 2774731 := bstep (se 1 (by rfl) ⟨2081048, by rfl⟩ : syracuseStep 2774731 = 4162097) B4162097
theorem B3699641 : Blo 2191435 3699641 := bstep (se 2 (by rfl) ⟨1387365, by rfl⟩ : syracuseStep 3699641 = 2774731) B2774731
theorem B2466427 : Blo 2191435 2466427 := bstep (se 1 (by rfl) ⟨1849820, by rfl⟩ : syracuseStep 2466427 = 3699641) B3699641
theorem B3288569 : Blo 2191435 3288569 := bstep (se 2 (by rfl) ⟨1233213, by rfl⟩ : syracuseStep 3288569 = 2466427) B2466427
theorem B2192379 : Blo 2191435 2192379 := bstep (se 1 (by rfl) ⟨1644284, by rfl⟩ : syracuseStep 2192379 = 3288569) B3288569
theorem B5000165 : Blo 2191435 5000165 := bbase (se 4 (by rfl) ⟨468765, by rfl⟩ : syracuseStep 5000165 = 937531) (by norm_num)
theorem B3333443 : Blo 2191435 3333443 := bstep (se 1 (by rfl) ⟨2500082, by rfl⟩ : syracuseStep 3333443 = 5000165) B5000165
theorem B35556725 : Blo 2191435 35556725 := bstep (se 5 (by rfl) ⟨1666721, by rfl⟩ : syracuseStep 35556725 = 3333443) B3333443
theorem B23704483 : Blo 2191435 23704483 := bstep (se 1 (by rfl) ⟨17778362, by rfl⟩ : syracuseStep 23704483 = 35556725) B35556725
theorem B31605977 : Blo 2191435 31605977 := bstep (se 2 (by rfl) ⟨11852241, by rfl⟩ : syracuseStep 31605977 = 23704483) B23704483
theorem B84282605 : Blo 2191435 84282605 := bstep (se 3 (by rfl) ⟨15802988, by rfl⟩ : syracuseStep 84282605 = 31605977) B31605977
theorem B56188403 : Blo 2191435 56188403 := bstep (se 1 (by rfl) ⟨42141302, by rfl⟩ : syracuseStep 56188403 = 84282605) B84282605
theorem B37458935 : Blo 2191435 37458935 := bstep (se 1 (by rfl) ⟨28094201, by rfl⟩ : syracuseStep 37458935 = 56188403) B56188403
theorem B24972623 : Blo 2191435 24972623 := bstep (se 1 (by rfl) ⟨18729467, by rfl⟩ : syracuseStep 24972623 = 37458935) B37458935
theorem B16648415 : Blo 2191435 16648415 := bstep (se 1 (by rfl) ⟨12486311, by rfl⟩ : syracuseStep 16648415 = 24972623) B24972623
theorem B11098943 : Blo 2191435 11098943 := bstep (se 1 (by rfl) ⟨8324207, by rfl⟩ : syracuseStep 11098943 = 16648415) B16648415
theorem B7399295 : Blo 2191435 7399295 := bstep (se 1 (by rfl) ⟨5549471, by rfl⟩ : syracuseStep 7399295 = 11098943) B11098943
theorem B4932863 : Blo 2191435 4932863 := bstep (se 1 (by rfl) ⟨3699647, by rfl⟩ : syracuseStep 4932863 = 7399295) B7399295
theorem B3288575 : Blo 2191435 3288575 := bstep (se 1 (by rfl) ⟨2466431, by rfl⟩ : syracuseStep 3288575 = 4932863) B4932863
theorem B2192383 : Blo 2191435 2192383 := bstep (se 1 (by rfl) ⟨1644287, by rfl⟩ : syracuseStep 2192383 = 3288575) B3288575
theorem B3288581 : Blo 2191435 3288581 := bbase (se 4 (by rfl) ⟨308304, by rfl⟩ : syracuseStep 3288581 = 616609) (by norm_num)
theorem B2192387 : Blo 2191435 2192387 := bstep (se 1 (by rfl) ⟨1644290, by rfl⟩ : syracuseStep 2192387 = 3288581) B3288581
theorem B3699661 : Blo 2191435 3699661 := bbase (se 3 (by rfl) ⟨693686, by rfl⟩ : syracuseStep 3699661 = 1387373) (by norm_num)
theorem B4932881 : Blo 2191435 4932881 := bstep (se 2 (by rfl) ⟨1849830, by rfl⟩ : syracuseStep 4932881 = 3699661) B3699661
theorem B3288587 : Blo 2191435 3288587 := bstep (se 1 (by rfl) ⟨2466440, by rfl⟩ : syracuseStep 3288587 = 4932881) B4932881
theorem B2192391 : Blo 2191435 2192391 := bstep (se 1 (by rfl) ⟨1644293, by rfl⟩ : syracuseStep 2192391 = 3288587) B3288587
theorem B2466445 : Blo 2191435 2466445 := bbase (se 3 (by rfl) ⟨462458, by rfl⟩ : syracuseStep 2466445 = 924917) (by norm_num)
theorem B3288593 : Blo 2191435 3288593 := bstep (se 2 (by rfl) ⟨1233222, by rfl⟩ : syracuseStep 3288593 = 2466445) B2466445
theorem B2192395 : Blo 2191435 2192395 := bstep (se 1 (by rfl) ⟨1644296, by rfl⟩ : syracuseStep 2192395 = 3288593) B3288593
theorem B7399349 : Blo 2191435 7399349 := bbase (se 5 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 7399349 = 693689) (by norm_num)
theorem B4932899 : Blo 2191435 4932899 := bstep (se 1 (by rfl) ⟨3699674, by rfl⟩ : syracuseStep 4932899 = 7399349) B7399349
theorem B3288599 : Blo 2191435 3288599 := bstep (se 1 (by rfl) ⟨2466449, by rfl⟩ : syracuseStep 3288599 = 4932899) B4932899
theorem B2192399 : Blo 2191435 2192399 := bstep (se 1 (by rfl) ⟨1644299, by rfl⟩ : syracuseStep 2192399 = 3288599) B3288599
theorem B3288605 : Blo 2191435 3288605 := bbase (se 3 (by rfl) ⟨616613, by rfl⟩ : syracuseStep 3288605 = 1233227) (by norm_num)
theorem B2192403 : Blo 2191435 2192403 := bstep (se 1 (by rfl) ⟨1644302, by rfl⟩ : syracuseStep 2192403 = 3288605) B3288605
theorem B4932917 : Blo 2191435 4932917 := bbase (se 5 (by rfl) ⟨231230, by rfl⟩ : syracuseStep 4932917 = 462461) (by norm_num)
theorem B3288611 : Blo 2191435 3288611 := bstep (se 1 (by rfl) ⟨2466458, by rfl⟩ : syracuseStep 3288611 = 4932917) B4932917
theorem B2192407 : Blo 2191435 2192407 := bstep (se 1 (by rfl) ⟨1644305, by rfl⟩ : syracuseStep 2192407 = 3288611) B3288611
theorem B2373157 : Blo 2191435 2373157 := bbase (se 4 (by rfl) ⟨222483, by rfl⟩ : syracuseStep 2373157 = 444967) (by norm_num)
theorem B12656837 : Blo 2191435 12656837 := bstep (se 4 (by rfl) ⟨1186578, by rfl⟩ : syracuseStep 12656837 = 2373157) B2373157
theorem B8437891 : Blo 2191435 8437891 := bstep (se 1 (by rfl) ⟨6328418, by rfl⟩ : syracuseStep 8437891 = 12656837) B12656837
theorem B11250521 : Blo 2191435 11250521 := bstep (se 2 (by rfl) ⟨4218945, by rfl⟩ : syracuseStep 11250521 = 8437891) B8437891
theorem B7500347 : Blo 2191435 7500347 := bstep (se 1 (by rfl) ⟨5625260, by rfl⟩ : syracuseStep 7500347 = 11250521) B11250521
theorem B5000231 : Blo 2191435 5000231 := bstep (se 1 (by rfl) ⟨3750173, by rfl⟩ : syracuseStep 5000231 = 7500347) B7500347
theorem B3333487 : Blo 2191435 3333487 := bstep (se 1 (by rfl) ⟨2500115, by rfl⟩ : syracuseStep 3333487 = 5000231) B5000231
theorem B4444649 : Blo 2191435 4444649 := bstep (se 2 (by rfl) ⟨1666743, by rfl⟩ : syracuseStep 4444649 = 3333487) B3333487
theorem B2963099 : Blo 2191435 2963099 := bstep (se 1 (by rfl) ⟨2222324, by rfl⟩ : syracuseStep 2963099 = 4444649) B4444649
theorem B7901597 : Blo 2191435 7901597 := bstep (se 3 (by rfl) ⟨1481549, by rfl⟩ : syracuseStep 7901597 = 2963099) B2963099
theorem B21070925 : Blo 2191435 21070925 := bstep (se 3 (by rfl) ⟨3950798, by rfl⟩ : syracuseStep 21070925 = 7901597) B7901597
theorem B14047283 : Blo 2191435 14047283 := bstep (se 1 (by rfl) ⟨10535462, by rfl⟩ : syracuseStep 14047283 = 21070925) B21070925
theorem B9364855 : Blo 2191435 9364855 := bstep (se 1 (by rfl) ⟨7023641, by rfl⟩ : syracuseStep 9364855 = 14047283) B14047283
theorem B12486473 : Blo 2191435 12486473 := bstep (se 2 (by rfl) ⟨4682427, by rfl⟩ : syracuseStep 12486473 = 9364855) B9364855
theorem B8324315 : Blo 2191435 8324315 := bstep (se 1 (by rfl) ⟨6243236, by rfl⟩ : syracuseStep 8324315 = 12486473) B12486473
theorem B5549543 : Blo 2191435 5549543 := bstep (se 1 (by rfl) ⟨4162157, by rfl⟩ : syracuseStep 5549543 = 8324315) B8324315
theorem B3699695 : Blo 2191435 3699695 := bstep (se 1 (by rfl) ⟨2774771, by rfl⟩ : syracuseStep 3699695 = 5549543) B5549543
theorem B2466463 : Blo 2191435 2466463 := bstep (se 1 (by rfl) ⟨1849847, by rfl⟩ : syracuseStep 2466463 = 3699695) B3699695
theorem B3288617 : Blo 2191435 3288617 := bstep (se 2 (by rfl) ⟨1233231, by rfl⟩ : syracuseStep 3288617 = 2466463) B2466463
theorem B2192411 : Blo 2191435 2192411 := bstep (se 1 (by rfl) ⟨1644308, by rfl⟩ : syracuseStep 2192411 = 3288617) B3288617
theorem B15803221 : Blo 2191435 15803221 := bbase (se 9 (by rfl) ⟨46298, by rfl⟩ : syracuseStep 15803221 = 92597) (by norm_num)
theorem B21070961 : Blo 2191435 21070961 := bstep (se 2 (by rfl) ⟨7901610, by rfl⟩ : syracuseStep 21070961 = 15803221) B15803221
theorem B14047307 : Blo 2191435 14047307 := bstep (se 1 (by rfl) ⟨10535480, by rfl⟩ : syracuseStep 14047307 = 21070961) B21070961
theorem B9364871 : Blo 2191435 9364871 := bstep (se 1 (by rfl) ⟨7023653, by rfl⟩ : syracuseStep 9364871 = 14047307) B14047307
theorem B6243247 : Blo 2191435 6243247 := bstep (se 1 (by rfl) ⟨4682435, by rfl⟩ : syracuseStep 6243247 = 9364871) B9364871
theorem B8324329 : Blo 2191435 8324329 := bstep (se 2 (by rfl) ⟨3121623, by rfl⟩ : syracuseStep 8324329 = 6243247) B6243247
theorem B11099105 : Blo 2191435 11099105 := bstep (se 2 (by rfl) ⟨4162164, by rfl⟩ : syracuseStep 11099105 = 8324329) B8324329
theorem B7399403 : Blo 2191435 7399403 := bstep (se 1 (by rfl) ⟨5549552, by rfl⟩ : syracuseStep 7399403 = 11099105) B11099105
theorem B4932935 : Blo 2191435 4932935 := bstep (se 1 (by rfl) ⟨3699701, by rfl⟩ : syracuseStep 4932935 = 7399403) B7399403
theorem B3288623 : Blo 2191435 3288623 := bstep (se 1 (by rfl) ⟨2466467, by rfl⟩ : syracuseStep 3288623 = 4932935) B4932935
theorem B2192415 : Blo 2191435 2192415 := bstep (se 1 (by rfl) ⟨1644311, by rfl⟩ : syracuseStep 2192415 = 3288623) B3288623
theorem B3288629 : Blo 2191435 3288629 := bbase (se 5 (by rfl) ⟨154154, by rfl⟩ : syracuseStep 3288629 = 308309) (by norm_num)
theorem B2192419 : Blo 2191435 2192419 := bstep (se 1 (by rfl) ⟨1644314, by rfl⟩ : syracuseStep 2192419 = 3288629) B3288629
theorem B5549573 : Blo 2191435 5549573 := bbase (se 4 (by rfl) ⟨520272, by rfl⟩ : syracuseStep 5549573 = 1040545) (by norm_num)
theorem B3699715 : Blo 2191435 3699715 := bstep (se 1 (by rfl) ⟨2774786, by rfl⟩ : syracuseStep 3699715 = 5549573) B5549573
theorem B4932953 : Blo 2191435 4932953 := bstep (se 2 (by rfl) ⟨1849857, by rfl⟩ : syracuseStep 4932953 = 3699715) B3699715
theorem B3288635 : Blo 2191435 3288635 := bstep (se 1 (by rfl) ⟨2466476, by rfl⟩ : syracuseStep 3288635 = 4932953) B4932953
theorem B2192423 : Blo 2191435 2192423 := bstep (se 1 (by rfl) ⟨1644317, by rfl⟩ : syracuseStep 2192423 = 3288635) B3288635
theorem B2466481 : Blo 2191435 2466481 := bbase (se 2 (by rfl) ⟨924930, by rfl⟩ : syracuseStep 2466481 = 1849861) (by norm_num)
theorem B3288641 : Blo 2191435 3288641 := bstep (se 2 (by rfl) ⟨1233240, by rfl⟩ : syracuseStep 3288641 = 2466481) B2466481
theorem B2192427 : Blo 2191435 2192427 := bstep (se 1 (by rfl) ⟨1644320, by rfl⟩ : syracuseStep 2192427 = 3288641) B3288641
theorem B3511853 : Blo 2191435 3511853 := bbase (se 3 (by rfl) ⟨658472, by rfl⟩ : syracuseStep 3511853 = 1316945) (by norm_num)
theorem B2341235 : Blo 2191435 2341235 := bstep (se 1 (by rfl) ⟨1755926, by rfl⟩ : syracuseStep 2341235 = 3511853) B3511853
theorem B6243293 : Blo 2191435 6243293 := bstep (se 3 (by rfl) ⟨1170617, by rfl⟩ : syracuseStep 6243293 = 2341235) B2341235
theorem B4162195 : Blo 2191435 4162195 := bstep (se 1 (by rfl) ⟨3121646, by rfl⟩ : syracuseStep 4162195 = 6243293) B6243293
theorem B5549593 : Blo 2191435 5549593 := bstep (se 2 (by rfl) ⟨2081097, by rfl⟩ : syracuseStep 5549593 = 4162195) B4162195
theorem B7399457 : Blo 2191435 7399457 := bstep (se 2 (by rfl) ⟨2774796, by rfl⟩ : syracuseStep 7399457 = 5549593) B5549593
theorem B4932971 : Blo 2191435 4932971 := bstep (se 1 (by rfl) ⟨3699728, by rfl⟩ : syracuseStep 4932971 = 7399457) B7399457
theorem B3288647 : Blo 2191435 3288647 := bstep (se 1 (by rfl) ⟨2466485, by rfl⟩ : syracuseStep 3288647 = 4932971) B4932971
theorem B2192431 : Blo 2191435 2192431 := bstep (se 1 (by rfl) ⟨1644323, by rfl⟩ : syracuseStep 2192431 = 3288647) B3288647
theorem B3288653 : Blo 2191435 3288653 := bbase (se 3 (by rfl) ⟨616622, by rfl⟩ : syracuseStep 3288653 = 1233245) (by norm_num)
theorem B2192435 : Blo 2191435 2192435 := bstep (se 1 (by rfl) ⟨1644326, by rfl⟩ : syracuseStep 2192435 = 3288653) B3288653
theorem B4932989 : Blo 2191435 4932989 := bbase (se 3 (by rfl) ⟨924935, by rfl⟩ : syracuseStep 4932989 = 1849871) (by norm_num)
theorem B3288659 : Blo 2191435 3288659 := bstep (se 1 (by rfl) ⟨2466494, by rfl⟩ : syracuseStep 3288659 = 4932989) B4932989
theorem B2192439 : Blo 2191435 2192439 := bstep (se 1 (by rfl) ⟨1644329, by rfl⟩ : syracuseStep 2192439 = 3288659) B3288659
theorem B3699749 : Blo 2191435 3699749 := bbase (se 4 (by rfl) ⟨346851, by rfl⟩ : syracuseStep 3699749 = 693703) (by norm_num)
theorem B2466499 : Blo 2191435 2466499 := bstep (se 1 (by rfl) ⟨1849874, by rfl⟩ : syracuseStep 2466499 = 3699749) B3699749
theorem B3288665 : Blo 2191435 3288665 := bstep (se 2 (by rfl) ⟨1233249, by rfl⟩ : syracuseStep 3288665 = 2466499) B2466499
theorem B2192443 : Blo 2191435 2192443 := bstep (se 1 (by rfl) ⟨1644332, by rfl⟩ : syracuseStep 2192443 = 3288665) B3288665
theorem B3121669 : Blo 2191435 3121669 := bbase (se 4 (by rfl) ⟨292656, by rfl⟩ : syracuseStep 3121669 = 585313) (by norm_num)
theorem B16648901 : Blo 2191435 16648901 := bstep (se 4 (by rfl) ⟨1560834, by rfl⟩ : syracuseStep 16648901 = 3121669) B3121669
theorem B11099267 : Blo 2191435 11099267 := bstep (se 1 (by rfl) ⟨8324450, by rfl⟩ : syracuseStep 11099267 = 16648901) B16648901
theorem B7399511 : Blo 2191435 7399511 := bstep (se 1 (by rfl) ⟨5549633, by rfl⟩ : syracuseStep 7399511 = 11099267) B11099267
theorem B4933007 : Blo 2191435 4933007 := bstep (se 1 (by rfl) ⟨3699755, by rfl⟩ : syracuseStep 4933007 = 7399511) B7399511
theorem B3288671 : Blo 2191435 3288671 := bstep (se 1 (by rfl) ⟨2466503, by rfl⟩ : syracuseStep 3288671 = 4933007) B4933007
theorem B2192447 : Blo 2191435 2192447 := bstep (se 1 (by rfl) ⟨1644335, by rfl⟩ : syracuseStep 2192447 = 3288671) B3288671
theorem B3288677 : Blo 2191435 3288677 := bbase (se 4 (by rfl) ⟨308313, by rfl⟩ : syracuseStep 3288677 = 616627) (by norm_num)
theorem B2192451 : Blo 2191435 2192451 := bstep (se 1 (by rfl) ⟨1644338, by rfl⟩ : syracuseStep 2192451 = 3288677) B3288677
theorem B2341261 : Blo 2191435 2341261 := bbase (se 3 (by rfl) ⟨438986, by rfl⟩ : syracuseStep 2341261 = 877973) (by norm_num)
theorem B3121681 : Blo 2191435 3121681 := bstep (se 2 (by rfl) ⟨1170630, by rfl⟩ : syracuseStep 3121681 = 2341261) B2341261
theorem B4162241 : Blo 2191435 4162241 := bstep (se 2 (by rfl) ⟨1560840, by rfl⟩ : syracuseStep 4162241 = 3121681) B3121681
theorem B2774827 : Blo 2191435 2774827 := bstep (se 1 (by rfl) ⟨2081120, by rfl⟩ : syracuseStep 2774827 = 4162241) B4162241
theorem B3699769 : Blo 2191435 3699769 := bstep (se 2 (by rfl) ⟨1387413, by rfl⟩ : syracuseStep 3699769 = 2774827) B2774827
theorem B4933025 : Blo 2191435 4933025 := bstep (se 2 (by rfl) ⟨1849884, by rfl⟩ : syracuseStep 4933025 = 3699769) B3699769
theorem B3288683 : Blo 2191435 3288683 := bstep (se 1 (by rfl) ⟨2466512, by rfl⟩ : syracuseStep 3288683 = 4933025) B4933025
theorem B2192455 : Blo 2191435 2192455 := bstep (se 1 (by rfl) ⟨1644341, by rfl⟩ : syracuseStep 2192455 = 3288683) B3288683
theorem B2466517 : Blo 2191435 2466517 := bbase (se 7 (by rfl) ⟨28904, by rfl⟩ : syracuseStep 2466517 = 57809) (by norm_num)
theorem B3288689 : Blo 2191435 3288689 := bstep (se 2 (by rfl) ⟨1233258, by rfl⟩ : syracuseStep 3288689 = 2466517) B2466517
theorem B2192459 : Blo 2191435 2192459 := bstep (se 1 (by rfl) ⟨1644344, by rfl⟩ : syracuseStep 2192459 = 3288689) B3288689
theorem B2774837 : Blo 2191435 2774837 := bbase (se 5 (by rfl) ⟨130070, by rfl⟩ : syracuseStep 2774837 = 260141) (by norm_num)
theorem B7399565 : Blo 2191435 7399565 := bstep (se 3 (by rfl) ⟨1387418, by rfl⟩ : syracuseStep 7399565 = 2774837) B2774837
theorem B4933043 : Blo 2191435 4933043 := bstep (se 1 (by rfl) ⟨3699782, by rfl⟩ : syracuseStep 4933043 = 7399565) B7399565
theorem B3288695 : Blo 2191435 3288695 := bstep (se 1 (by rfl) ⟨2466521, by rfl⟩ : syracuseStep 3288695 = 4933043) B4933043
theorem B2192463 : Blo 2191435 2192463 := bstep (se 1 (by rfl) ⟨1644347, by rfl⟩ : syracuseStep 2192463 = 3288695) B3288695
theorem B3288701 : Blo 2191435 3288701 := bbase (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) (by norm_num)
theorem B2192467 : Blo 2191435 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B4933061 : Blo 2191435 4933061 := bbase (se 4 (by rfl) ⟨462474, by rfl⟩ : syracuseStep 4933061 = 924949) (by norm_num)
theorem B3288707 : Blo 2191435 3288707 := bstep (se 1 (by rfl) ⟨2466530, by rfl⟩ : syracuseStep 3288707 = 4933061) B4933061
theorem B2192471 : Blo 2191435 2192471 := bstep (se 1 (by rfl) ⟨1644353, by rfl⟩ : syracuseStep 2192471 = 3288707) B3288707
theorem B22808693 : Blo 2191435 22808693 := bbase (se 5 (by rfl) ⟨1069157, by rfl⟩ : syracuseStep 22808693 = 2138315) (by norm_num)
theorem B60823181 : Blo 2191435 60823181 := bstep (se 3 (by rfl) ⟨11404346, by rfl⟩ : syracuseStep 60823181 = 22808693) B22808693
theorem B162195149 : Blo 2191435 162195149 := bstep (se 3 (by rfl) ⟨30411590, by rfl⟩ : syracuseStep 162195149 = 60823181) B60823181
theorem B108130099 : Blo 2191435 108130099 := bstep (se 1 (by rfl) ⟨81097574, by rfl⟩ : syracuseStep 108130099 = 162195149) B162195149
theorem B144173465 : Blo 2191435 144173465 := bstep (se 2 (by rfl) ⟨54065049, by rfl⟩ : syracuseStep 144173465 = 108130099) B108130099
theorem B96115643 : Blo 2191435 96115643 := bstep (se 1 (by rfl) ⟨72086732, by rfl⟩ : syracuseStep 96115643 = 144173465) B144173465
theorem B64077095 : Blo 2191435 64077095 := bstep (se 1 (by rfl) ⟨48057821, by rfl⟩ : syracuseStep 64077095 = 96115643) B96115643
theorem B42718063 : Blo 2191435 42718063 := bstep (se 1 (by rfl) ⟨32038547, by rfl⟩ : syracuseStep 42718063 = 64077095) B64077095
theorem B56957417 : Blo 2191435 56957417 := bstep (se 2 (by rfl) ⟨21359031, by rfl⟩ : syracuseStep 56957417 = 42718063) B42718063
theorem B37971611 : Blo 2191435 37971611 := bstep (se 1 (by rfl) ⟨28478708, by rfl⟩ : syracuseStep 37971611 = 56957417) B56957417
theorem B25314407 : Blo 2191435 25314407 := bstep (se 1 (by rfl) ⟨18985805, by rfl⟩ : syracuseStep 25314407 = 37971611) B37971611
theorem B16876271 : Blo 2191435 16876271 := bstep (se 1 (by rfl) ⟨12657203, by rfl⟩ : syracuseStep 16876271 = 25314407) B25314407
theorem B11250847 : Blo 2191435 11250847 := bstep (se 1 (by rfl) ⟨8438135, by rfl⟩ : syracuseStep 11250847 = 16876271) B16876271
theorem B15001129 : Blo 2191435 15001129 := bstep (se 2 (by rfl) ⟨5625423, by rfl⟩ : syracuseStep 15001129 = 11250847) B11250847
theorem B20001505 : Blo 2191435 20001505 := bstep (se 2 (by rfl) ⟨7500564, by rfl⟩ : syracuseStep 20001505 = 15001129) B15001129
theorem B26668673 : Blo 2191435 26668673 := bstep (se 2 (by rfl) ⟨10000752, by rfl⟩ : syracuseStep 26668673 = 20001505) B20001505
theorem B17779115 : Blo 2191435 17779115 := bstep (se 1 (by rfl) ⟨13334336, by rfl⟩ : syracuseStep 17779115 = 26668673) B26668673
theorem B11852743 : Blo 2191435 11852743 := bstep (se 1 (by rfl) ⟨8889557, by rfl⟩ : syracuseStep 11852743 = 17779115) B17779115
theorem B15803657 : Blo 2191435 15803657 := bstep (se 2 (by rfl) ⟨5926371, by rfl⟩ : syracuseStep 15803657 = 11852743) B11852743
theorem B10535771 : Blo 2191435 10535771 := bstep (se 1 (by rfl) ⟨7901828, by rfl⟩ : syracuseStep 10535771 = 15803657) B15803657
theorem B7023847 : Blo 2191435 7023847 := bstep (se 1 (by rfl) ⟨5267885, by rfl⟩ : syracuseStep 7023847 = 10535771) B10535771
theorem B9365129 : Blo 2191435 9365129 := bstep (se 2 (by rfl) ⟨3511923, by rfl⟩ : syracuseStep 9365129 = 7023847) B7023847
theorem B6243419 : Blo 2191435 6243419 := bstep (se 1 (by rfl) ⟨4682564, by rfl⟩ : syracuseStep 6243419 = 9365129) B9365129
theorem B4162279 : Blo 2191435 4162279 := bstep (se 1 (by rfl) ⟨3121709, by rfl⟩ : syracuseStep 4162279 = 6243419) B6243419
theorem B5549705 : Blo 2191435 5549705 := bstep (se 2 (by rfl) ⟨2081139, by rfl⟩ : syracuseStep 5549705 = 4162279) B4162279
theorem B3699803 : Blo 2191435 3699803 := bstep (se 1 (by rfl) ⟨2774852, by rfl⟩ : syracuseStep 3699803 = 5549705) B5549705
theorem B2466535 : Blo 2191435 2466535 := bstep (se 1 (by rfl) ⟨1849901, by rfl⟩ : syracuseStep 2466535 = 3699803) B3699803
theorem B3288713 : Blo 2191435 3288713 := bstep (se 2 (by rfl) ⟨1233267, by rfl⟩ : syracuseStep 3288713 = 2466535) B2466535
theorem B2192475 : Blo 2191435 2192475 := bstep (se 1 (by rfl) ⟨1644356, by rfl⟩ : syracuseStep 2192475 = 3288713) B3288713
theorem B11099429 : Blo 2191435 11099429 := bbase (se 4 (by rfl) ⟨1040571, by rfl⟩ : syracuseStep 11099429 = 2081143) (by norm_num)
theorem B7399619 : Blo 2191435 7399619 := bstep (se 1 (by rfl) ⟨5549714, by rfl⟩ : syracuseStep 7399619 = 11099429) B11099429
theorem B4933079 : Blo 2191435 4933079 := bstep (se 1 (by rfl) ⟨3699809, by rfl⟩ : syracuseStep 4933079 = 7399619) B7399619
theorem B3288719 : Blo 2191435 3288719 := bstep (se 1 (by rfl) ⟨2466539, by rfl⟩ : syracuseStep 3288719 = 4933079) B4933079
theorem B2192479 : Blo 2191435 2192479 := bstep (se 1 (by rfl) ⟨1644359, by rfl⟩ : syracuseStep 2192479 = 3288719) B3288719
theorem B3288725 : Blo 2191435 3288725 := bbase (se 6 (by rfl) ⟨77079, by rfl⟩ : syracuseStep 3288725 = 154159) (by norm_num)
theorem B2192483 : Blo 2191435 2192483 := bstep (se 1 (by rfl) ⟨1644362, by rfl⟩ : syracuseStep 2192483 = 3288725) B3288725
theorem B8889605 : Blo 2191435 8889605 := bbase (se 4 (by rfl) ⟨833400, by rfl⟩ : syracuseStep 8889605 = 1666801) (by norm_num)
theorem B5926403 : Blo 2191435 5926403 := bstep (se 1 (by rfl) ⟨4444802, by rfl⟩ : syracuseStep 5926403 = 8889605) B8889605
theorem B15803741 : Blo 2191435 15803741 := bstep (se 3 (by rfl) ⟨2963201, by rfl⟩ : syracuseStep 15803741 = 5926403) B5926403
theorem B10535827 : Blo 2191435 10535827 := bstep (se 1 (by rfl) ⟨7901870, by rfl⟩ : syracuseStep 10535827 = 15803741) B15803741
theorem B14047769 : Blo 2191435 14047769 := bstep (se 2 (by rfl) ⟨5267913, by rfl⟩ : syracuseStep 14047769 = 10535827) B10535827
theorem B9365179 : Blo 2191435 9365179 := bstep (se 1 (by rfl) ⟨7023884, by rfl⟩ : syracuseStep 9365179 = 14047769) B14047769
theorem B12486905 : Blo 2191435 12486905 := bstep (se 2 (by rfl) ⟨4682589, by rfl⟩ : syracuseStep 12486905 = 9365179) B9365179
theorem B8324603 : Blo 2191435 8324603 := bstep (se 1 (by rfl) ⟨6243452, by rfl⟩ : syracuseStep 8324603 = 12486905) B12486905
theorem B5549735 : Blo 2191435 5549735 := bstep (se 1 (by rfl) ⟨4162301, by rfl⟩ : syracuseStep 5549735 = 8324603) B8324603
theorem B3699823 : Blo 2191435 3699823 := bstep (se 1 (by rfl) ⟨2774867, by rfl⟩ : syracuseStep 3699823 = 5549735) B5549735
theorem B4933097 : Blo 2191435 4933097 := bstep (se 2 (by rfl) ⟨1849911, by rfl⟩ : syracuseStep 4933097 = 3699823) B3699823
theorem B3288731 : Blo 2191435 3288731 := bstep (se 1 (by rfl) ⟨2466548, by rfl⟩ : syracuseStep 3288731 = 4933097) B4933097
theorem B2192487 : Blo 2191435 2192487 := bstep (se 1 (by rfl) ⟨1644365, by rfl⟩ : syracuseStep 2192487 = 3288731) B3288731
theorem B2466553 : Blo 2191435 2466553 := bbase (se 2 (by rfl) ⟨924957, by rfl⟩ : syracuseStep 2466553 = 1849915) (by norm_num)
theorem B3288737 : Blo 2191435 3288737 := bstep (se 2 (by rfl) ⟨1233276, by rfl⟩ : syracuseStep 3288737 = 2466553) B2466553
theorem B2192491 : Blo 2191435 2192491 := bstep (se 1 (by rfl) ⟨1644368, by rfl⟩ : syracuseStep 2192491 = 3288737) B3288737
theorem B5267933 : Blo 2191435 5267933 := bbase (se 3 (by rfl) ⟨987737, by rfl⟩ : syracuseStep 5267933 = 1975475) (by norm_num)
theorem B3511955 : Blo 2191435 3511955 := bstep (se 1 (by rfl) ⟨2633966, by rfl⟩ : syracuseStep 3511955 = 5267933) B5267933
theorem B9365213 : Blo 2191435 9365213 := bstep (se 3 (by rfl) ⟨1755977, by rfl⟩ : syracuseStep 9365213 = 3511955) B3511955
theorem B6243475 : Blo 2191435 6243475 := bstep (se 1 (by rfl) ⟨4682606, by rfl⟩ : syracuseStep 6243475 = 9365213) B9365213
theorem B8324633 : Blo 2191435 8324633 := bstep (se 2 (by rfl) ⟨3121737, by rfl⟩ : syracuseStep 8324633 = 6243475) B6243475
theorem B5549755 : Blo 2191435 5549755 := bstep (se 1 (by rfl) ⟨4162316, by rfl⟩ : syracuseStep 5549755 = 8324633) B8324633
theorem B7399673 : Blo 2191435 7399673 := bstep (se 2 (by rfl) ⟨2774877, by rfl⟩ : syracuseStep 7399673 = 5549755) B5549755
theorem B4933115 : Blo 2191435 4933115 := bstep (se 1 (by rfl) ⟨3699836, by rfl⟩ : syracuseStep 4933115 = 7399673) B7399673
theorem B3288743 : Blo 2191435 3288743 := bstep (se 1 (by rfl) ⟨2466557, by rfl⟩ : syracuseStep 3288743 = 4933115) B4933115
theorem B2192495 : Blo 2191435 2192495 := bstep (se 1 (by rfl) ⟨1644371, by rfl⟩ : syracuseStep 2192495 = 3288743) B3288743
theorem B3288749 : Blo 2191435 3288749 := bbase (se 3 (by rfl) ⟨616640, by rfl⟩ : syracuseStep 3288749 = 1233281) (by norm_num)
theorem B2192499 : Blo 2191435 2192499 := bstep (se 1 (by rfl) ⟨1644374, by rfl⟩ : syracuseStep 2192499 = 3288749) B3288749
theorem B4933133 : Blo 2191435 4933133 := bbase (se 3 (by rfl) ⟨924962, by rfl⟩ : syracuseStep 4933133 = 1849925) (by norm_num)
theorem B3288755 : Blo 2191435 3288755 := bstep (se 1 (by rfl) ⟨2466566, by rfl⟩ : syracuseStep 3288755 = 4933133) B4933133
theorem B2192503 : Blo 2191435 2192503 := bstep (se 1 (by rfl) ⟨1644377, by rfl⟩ : syracuseStep 2192503 = 3288755) B3288755
theorem B2774893 : Blo 2191435 2774893 := bbase (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) (by norm_num)
theorem B3699857 : Blo 2191435 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B2466571 : Blo 2191435 2466571 := bstep (se 1 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 2466571 = 3699857) B3699857
theorem B3288761 : Blo 2191435 3288761 := bstep (se 2 (by rfl) ⟨1233285, by rfl⟩ : syracuseStep 3288761 = 2466571) B2466571
theorem B2192507 : Blo 2191435 2192507 := bstep (se 1 (by rfl) ⟨1644380, by rfl⟩ : syracuseStep 2192507 = 3288761) B3288761
theorem B10535941 : Blo 2191435 10535941 := bbase (se 4 (by rfl) ⟨987744, by rfl⟩ : syracuseStep 10535941 = 1975489) (by norm_num)
theorem B14047921 : Blo 2191435 14047921 := bstep (se 2 (by rfl) ⟨5267970, by rfl⟩ : syracuseStep 14047921 = 10535941) B10535941
theorem B18730561 : Blo 2191435 18730561 := bstep (se 2 (by rfl) ⟨7023960, by rfl⟩ : syracuseStep 18730561 = 14047921) B14047921
theorem B24974081 : Blo 2191435 24974081 := bstep (se 2 (by rfl) ⟨9365280, by rfl⟩ : syracuseStep 24974081 = 18730561) B18730561
theorem B16649387 : Blo 2191435 16649387 := bstep (se 1 (by rfl) ⟨12487040, by rfl⟩ : syracuseStep 16649387 = 24974081) B24974081
theorem B11099591 : Blo 2191435 11099591 := bstep (se 1 (by rfl) ⟨8324693, by rfl⟩ : syracuseStep 11099591 = 16649387) B16649387
theorem B7399727 : Blo 2191435 7399727 := bstep (se 1 (by rfl) ⟨5549795, by rfl⟩ : syracuseStep 7399727 = 11099591) B11099591
theorem B4933151 : Blo 2191435 4933151 := bstep (se 1 (by rfl) ⟨3699863, by rfl⟩ : syracuseStep 4933151 = 7399727) B7399727
theorem B3288767 : Blo 2191435 3288767 := bstep (se 1 (by rfl) ⟨2466575, by rfl⟩ : syracuseStep 3288767 = 4933151) B4933151
theorem B2192511 : Blo 2191435 2192511 := bstep (se 1 (by rfl) ⟨1644383, by rfl⟩ : syracuseStep 2192511 = 3288767) B3288767
theorem B3288773 : Blo 2191435 3288773 := bbase (se 4 (by rfl) ⟨308322, by rfl⟩ : syracuseStep 3288773 = 616645) (by norm_num)
theorem B2192515 : Blo 2191435 2192515 := bstep (se 1 (by rfl) ⟨1644386, by rfl⟩ : syracuseStep 2192515 = 3288773) B3288773
theorem B3699877 : Blo 2191435 3699877 := bbase (se 4 (by rfl) ⟨346863, by rfl⟩ : syracuseStep 3699877 = 693727) (by norm_num)
theorem B4933169 : Blo 2191435 4933169 := bstep (se 2 (by rfl) ⟨1849938, by rfl⟩ : syracuseStep 4933169 = 3699877) B3699877
theorem B3288779 : Blo 2191435 3288779 := bstep (se 1 (by rfl) ⟨2466584, by rfl⟩ : syracuseStep 3288779 = 4933169) B4933169
theorem B2192519 : Blo 2191435 2192519 := bstep (se 1 (by rfl) ⟨1644389, by rfl⟩ : syracuseStep 2192519 = 3288779) B3288779
theorem B2466589 : Blo 2191435 2466589 := bbase (se 3 (by rfl) ⟨462485, by rfl⟩ : syracuseStep 2466589 = 924971) (by norm_num)
theorem B3288785 : Blo 2191435 3288785 := bstep (se 2 (by rfl) ⟨1233294, by rfl⟩ : syracuseStep 3288785 = 2466589) B2466589
theorem B2192523 : Blo 2191435 2192523 := bstep (se 1 (by rfl) ⟨1644392, by rfl⟩ : syracuseStep 2192523 = 3288785) B3288785
theorem B7399781 : Blo 2191435 7399781 := bbase (se 4 (by rfl) ⟨693729, by rfl⟩ : syracuseStep 7399781 = 1387459) (by norm_num)
theorem B4933187 : Blo 2191435 4933187 := bstep (se 1 (by rfl) ⟨3699890, by rfl⟩ : syracuseStep 4933187 = 7399781) B7399781
theorem B3288791 : Blo 2191435 3288791 := bstep (se 1 (by rfl) ⟨2466593, by rfl⟩ : syracuseStep 3288791 = 4933187) B4933187
theorem B2192527 : Blo 2191435 2192527 := bstep (se 1 (by rfl) ⟨1644395, by rfl⟩ : syracuseStep 2192527 = 3288791) B3288791
theorem B3288797 : Blo 2191435 3288797 := bbase (se 3 (by rfl) ⟨616649, by rfl⟩ : syracuseStep 3288797 = 1233299) (by norm_num)
theorem B2192531 : Blo 2191435 2192531 := bstep (se 1 (by rfl) ⟨1644398, by rfl⟩ : syracuseStep 2192531 = 3288797) B3288797
theorem B4933205 : Blo 2191435 4933205 := bbase (se 8 (by rfl) ⟨28905, by rfl⟩ : syracuseStep 4933205 = 57811) (by norm_num)
theorem B3288803 : Blo 2191435 3288803 := bstep (se 1 (by rfl) ⟨2466602, by rfl⟩ : syracuseStep 3288803 = 4933205) B4933205
theorem B2192535 : Blo 2191435 2192535 := bstep (se 1 (by rfl) ⟨1644401, by rfl⟩ : syracuseStep 2192535 = 3288803) B3288803
theorem B4682701 : Blo 2191435 4682701 := bbase (se 3 (by rfl) ⟨878006, by rfl⟩ : syracuseStep 4682701 = 1756013) (by norm_num)
theorem B6243601 : Blo 2191435 6243601 := bstep (se 2 (by rfl) ⟨2341350, by rfl⟩ : syracuseStep 6243601 = 4682701) B4682701
theorem B8324801 : Blo 2191435 8324801 := bstep (se 2 (by rfl) ⟨3121800, by rfl⟩ : syracuseStep 8324801 = 6243601) B6243601
theorem B5549867 : Blo 2191435 5549867 := bstep (se 1 (by rfl) ⟨4162400, by rfl⟩ : syracuseStep 5549867 = 8324801) B8324801
theorem B3699911 : Blo 2191435 3699911 := bstep (se 1 (by rfl) ⟨2774933, by rfl⟩ : syracuseStep 3699911 = 5549867) B5549867
theorem B2466607 : Blo 2191435 2466607 := bstep (se 1 (by rfl) ⟨1849955, by rfl⟩ : syracuseStep 2466607 = 3699911) B3699911
theorem B3288809 : Blo 2191435 3288809 := bstep (se 2 (by rfl) ⟨1233303, by rfl⟩ : syracuseStep 3288809 = 2466607) B2466607
theorem B2192539 : Blo 2191435 2192539 := bstep (se 1 (by rfl) ⟨1644404, by rfl⟩ : syracuseStep 2192539 = 3288809) B3288809
theorem B57736277 : Blo 2191435 57736277 := bbase (se 8 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 57736277 = 676597) (by norm_num)
theorem B38490851 : Blo 2191435 38490851 := bstep (se 1 (by rfl) ⟨28868138, by rfl⟩ : syracuseStep 38490851 = 57736277) B57736277
theorem B25660567 : Blo 2191435 25660567 := bstep (se 1 (by rfl) ⟨19245425, by rfl⟩ : syracuseStep 25660567 = 38490851) B38490851
theorem B34214089 : Blo 2191435 34214089 := bstep (se 2 (by rfl) ⟨12830283, by rfl⟩ : syracuseStep 34214089 = 25660567) B25660567
theorem B45618785 : Blo 2191435 45618785 := bstep (se 2 (by rfl) ⟨17107044, by rfl⟩ : syracuseStep 45618785 = 34214089) B34214089
theorem B30412523 : Blo 2191435 30412523 := bstep (se 1 (by rfl) ⟨22809392, by rfl⟩ : syracuseStep 30412523 = 45618785) B45618785
theorem B81100061 : Blo 2191435 81100061 := bstep (se 3 (by rfl) ⟨15206261, by rfl⟩ : syracuseStep 81100061 = 30412523) B30412523
theorem B54066707 : Blo 2191435 54066707 := bstep (se 1 (by rfl) ⟨40550030, by rfl⟩ : syracuseStep 54066707 = 81100061) B81100061
theorem B36044471 : Blo 2191435 36044471 := bstep (se 1 (by rfl) ⟨27033353, by rfl⟩ : syracuseStep 36044471 = 54066707) B54066707
theorem B96118589 : Blo 2191435 96118589 := bstep (se 3 (by rfl) ⟨18022235, by rfl⟩ : syracuseStep 96118589 = 36044471) B36044471
theorem B64079059 : Blo 2191435 64079059 := bstep (se 1 (by rfl) ⟨48059294, by rfl⟩ : syracuseStep 64079059 = 96118589) B96118589
theorem B85438745 : Blo 2191435 85438745 := bstep (se 2 (by rfl) ⟨32039529, by rfl⟩ : syracuseStep 85438745 = 64079059) B64079059
theorem B56959163 : Blo 2191435 56959163 := bstep (se 1 (by rfl) ⟨42719372, by rfl⟩ : syracuseStep 56959163 = 85438745) B85438745
theorem B37972775 : Blo 2191435 37972775 := bstep (se 1 (by rfl) ⟨28479581, by rfl⟩ : syracuseStep 37972775 = 56959163) B56959163
theorem B25315183 : Blo 2191435 25315183 := bstep (se 1 (by rfl) ⟨18986387, by rfl⟩ : syracuseStep 25315183 = 37972775) B37972775
theorem B135014309 : Blo 2191435 135014309 := bstep (se 4 (by rfl) ⟨12657591, by rfl⟩ : syracuseStep 135014309 = 25315183) B25315183
theorem B90009539 : Blo 2191435 90009539 := bstep (se 1 (by rfl) ⟨67507154, by rfl⟩ : syracuseStep 90009539 = 135014309) B135014309
theorem B60006359 : Blo 2191435 60006359 := bstep (se 1 (by rfl) ⟨45004769, by rfl⟩ : syracuseStep 60006359 = 90009539) B90009539
theorem B40004239 : Blo 2191435 40004239 := bstep (se 1 (by rfl) ⟨30003179, by rfl⟩ : syracuseStep 40004239 = 60006359) B60006359
theorem B53338985 : Blo 2191435 53338985 := bstep (se 2 (by rfl) ⟨20002119, by rfl⟩ : syracuseStep 53338985 = 40004239) B40004239
theorem B35559323 : Blo 2191435 35559323 := bstep (se 1 (by rfl) ⟨26669492, by rfl⟩ : syracuseStep 35559323 = 53338985) B53338985
theorem B23706215 : Blo 2191435 23706215 := bstep (se 1 (by rfl) ⟨17779661, by rfl⟩ : syracuseStep 23706215 = 35559323) B35559323
theorem B15804143 : Blo 2191435 15804143 := bstep (se 1 (by rfl) ⟨11853107, by rfl⟩ : syracuseStep 15804143 = 23706215) B23706215
theorem B10536095 : Blo 2191435 10536095 := bstep (se 1 (by rfl) ⟨7902071, by rfl⟩ : syracuseStep 10536095 = 15804143) B15804143
theorem B28096253 : Blo 2191435 28096253 := bstep (se 3 (by rfl) ⟨5268047, by rfl⟩ : syracuseStep 28096253 = 10536095) B10536095
theorem B18730835 : Blo 2191435 18730835 := bstep (se 1 (by rfl) ⟨14048126, by rfl⟩ : syracuseStep 18730835 = 28096253) B28096253
theorem B12487223 : Blo 2191435 12487223 := bstep (se 1 (by rfl) ⟨9365417, by rfl⟩ : syracuseStep 12487223 = 18730835) B18730835
theorem B8324815 : Blo 2191435 8324815 := bstep (se 1 (by rfl) ⟨6243611, by rfl⟩ : syracuseStep 8324815 = 12487223) B12487223
theorem B11099753 : Blo 2191435 11099753 := bstep (se 2 (by rfl) ⟨4162407, by rfl⟩ : syracuseStep 11099753 = 8324815) B8324815
theorem B7399835 : Blo 2191435 7399835 := bstep (se 1 (by rfl) ⟨5549876, by rfl⟩ : syracuseStep 7399835 = 11099753) B11099753
theorem B4933223 : Blo 2191435 4933223 := bstep (se 1 (by rfl) ⟨3699917, by rfl⟩ : syracuseStep 4933223 = 7399835) B7399835
theorem B3288815 : Blo 2191435 3288815 := bstep (se 1 (by rfl) ⟨2466611, by rfl⟩ : syracuseStep 3288815 = 4933223) B4933223
theorem B2192543 : Blo 2191435 2192543 := bstep (se 1 (by rfl) ⟨1644407, by rfl⟩ : syracuseStep 2192543 = 3288815) B3288815
theorem B3288821 : Blo 2191435 3288821 := bbase (se 5 (by rfl) ⟨154163, by rfl⟩ : syracuseStep 3288821 = 308327) (by norm_num)
theorem B2192547 : Blo 2191435 2192547 := bstep (se 1 (by rfl) ⟨1644410, by rfl⟩ : syracuseStep 2192547 = 3288821) B3288821
theorem B3512045 : Blo 2191435 3512045 := bbase (se 3 (by rfl) ⟨658508, by rfl⟩ : syracuseStep 3512045 = 1317017) (by norm_num)
theorem B9365453 : Blo 2191435 9365453 := bstep (se 3 (by rfl) ⟨1756022, by rfl⟩ : syracuseStep 9365453 = 3512045) B3512045
theorem B6243635 : Blo 2191435 6243635 := bstep (se 1 (by rfl) ⟨4682726, by rfl⟩ : syracuseStep 6243635 = 9365453) B9365453
theorem B4162423 : Blo 2191435 4162423 := bstep (se 1 (by rfl) ⟨3121817, by rfl⟩ : syracuseStep 4162423 = 6243635) B6243635
theorem B5549897 : Blo 2191435 5549897 := bstep (se 2 (by rfl) ⟨2081211, by rfl⟩ : syracuseStep 5549897 = 4162423) B4162423
theorem B3699931 : Blo 2191435 3699931 := bstep (se 1 (by rfl) ⟨2774948, by rfl⟩ : syracuseStep 3699931 = 5549897) B5549897
theorem B4933241 : Blo 2191435 4933241 := bstep (se 2 (by rfl) ⟨1849965, by rfl⟩ : syracuseStep 4933241 = 3699931) B3699931
theorem B3288827 : Blo 2191435 3288827 := bstep (se 1 (by rfl) ⟨2466620, by rfl⟩ : syracuseStep 3288827 = 4933241) B4933241
theorem B2192551 : Blo 2191435 2192551 := bstep (se 1 (by rfl) ⟨1644413, by rfl⟩ : syracuseStep 2192551 = 3288827) B3288827
theorem B2466625 : Blo 2191435 2466625 := bbase (se 2 (by rfl) ⟨924984, by rfl⟩ : syracuseStep 2466625 = 1849969) (by norm_num)
theorem B3288833 : Blo 2191435 3288833 := bstep (se 2 (by rfl) ⟨1233312, by rfl⟩ : syracuseStep 3288833 = 2466625) B2466625
theorem B2192555 : Blo 2191435 2192555 := bstep (se 1 (by rfl) ⟨1644416, by rfl⟩ : syracuseStep 2192555 = 3288833) B3288833
theorem B5549917 : Blo 2191435 5549917 := bbase (se 3 (by rfl) ⟨1040609, by rfl⟩ : syracuseStep 5549917 = 2081219) (by norm_num)
theorem B7399889 : Blo 2191435 7399889 := bstep (se 2 (by rfl) ⟨2774958, by rfl⟩ : syracuseStep 7399889 = 5549917) B5549917
theorem B4933259 : Blo 2191435 4933259 := bstep (se 1 (by rfl) ⟨3699944, by rfl⟩ : syracuseStep 4933259 = 7399889) B7399889
theorem B3288839 : Blo 2191435 3288839 := bstep (se 1 (by rfl) ⟨2466629, by rfl⟩ : syracuseStep 3288839 = 4933259) B4933259
theorem B2192559 : Blo 2191435 2192559 := bstep (se 1 (by rfl) ⟨1644419, by rfl⟩ : syracuseStep 2192559 = 3288839) B3288839
theorem B3288845 : Blo 2191435 3288845 := bbase (se 3 (by rfl) ⟨616658, by rfl⟩ : syracuseStep 3288845 = 1233317) (by norm_num)
theorem B2192563 : Blo 2191435 2192563 := bstep (se 1 (by rfl) ⟨1644422, by rfl⟩ : syracuseStep 2192563 = 3288845) B3288845
theorem B4933277 : Blo 2191435 4933277 := bbase (se 3 (by rfl) ⟨924989, by rfl⟩ : syracuseStep 4933277 = 1849979) (by norm_num)
theorem B3288851 : Blo 2191435 3288851 := bstep (se 1 (by rfl) ⟨2466638, by rfl⟩ : syracuseStep 3288851 = 4933277) B4933277
theorem B2192567 : Blo 2191435 2192567 := bstep (se 1 (by rfl) ⟨1644425, by rfl⟩ : syracuseStep 2192567 = 3288851) B3288851
theorem B3699965 : Blo 2191435 3699965 := bbase (se 3 (by rfl) ⟨693743, by rfl⟩ : syracuseStep 3699965 = 1387487) (by norm_num)
theorem B2466643 : Blo 2191435 2466643 := bstep (se 1 (by rfl) ⟨1849982, by rfl⟩ : syracuseStep 2466643 = 3699965) B3699965
theorem B3288857 : Blo 2191435 3288857 := bstep (se 2 (by rfl) ⟨1233321, by rfl⟩ : syracuseStep 3288857 = 2466643) B2466643
theorem B2192571 : Blo 2191435 2192571 := bstep (se 1 (by rfl) ⟨1644428, by rfl⟩ : syracuseStep 2192571 = 3288857) B3288857
theorem B5268125 : Blo 2191435 5268125 := bbase (se 3 (by rfl) ⟨987773, by rfl⟩ : syracuseStep 5268125 = 1975547) (by norm_num)
theorem B3512083 : Blo 2191435 3512083 := bstep (se 1 (by rfl) ⟨2634062, by rfl⟩ : syracuseStep 3512083 = 5268125) B5268125
theorem B4682777 : Blo 2191435 4682777 := bstep (se 2 (by rfl) ⟨1756041, by rfl⟩ : syracuseStep 4682777 = 3512083) B3512083
theorem B12487405 : Blo 2191435 12487405 := bstep (se 3 (by rfl) ⟨2341388, by rfl⟩ : syracuseStep 12487405 = 4682777) B4682777
theorem B16649873 : Blo 2191435 16649873 := bstep (se 2 (by rfl) ⟨6243702, by rfl⟩ : syracuseStep 16649873 = 12487405) B12487405
theorem B11099915 : Blo 2191435 11099915 := bstep (se 1 (by rfl) ⟨8324936, by rfl⟩ : syracuseStep 11099915 = 16649873) B16649873
theorem B7399943 : Blo 2191435 7399943 := bstep (se 1 (by rfl) ⟨5549957, by rfl⟩ : syracuseStep 7399943 = 11099915) B11099915
theorem B4933295 : Blo 2191435 4933295 := bstep (se 1 (by rfl) ⟨3699971, by rfl⟩ : syracuseStep 4933295 = 7399943) B7399943
theorem B3288863 : Blo 2191435 3288863 := bstep (se 1 (by rfl) ⟨2466647, by rfl⟩ : syracuseStep 3288863 = 4933295) B4933295
theorem B2192575 : Blo 2191435 2192575 := bstep (se 1 (by rfl) ⟨1644431, by rfl⟩ : syracuseStep 2192575 = 3288863) B3288863
theorem B3288869 : Blo 2191435 3288869 := bbase (se 4 (by rfl) ⟨308331, by rfl⟩ : syracuseStep 3288869 = 616663) (by norm_num)
theorem B2192579 : Blo 2191435 2192579 := bstep (se 1 (by rfl) ⟨1644434, by rfl⟩ : syracuseStep 2192579 = 3288869) B3288869
theorem B2774989 : Blo 2191435 2774989 := bbase (se 3 (by rfl) ⟨520310, by rfl⟩ : syracuseStep 2774989 = 1040621) (by norm_num)
theorem B3699985 : Blo 2191435 3699985 := bstep (se 2 (by rfl) ⟨1387494, by rfl⟩ : syracuseStep 3699985 = 2774989) B2774989
theorem B4933313 : Blo 2191435 4933313 := bstep (se 2 (by rfl) ⟨1849992, by rfl⟩ : syracuseStep 4933313 = 3699985) B3699985
theorem B3288875 : Blo 2191435 3288875 := bstep (se 1 (by rfl) ⟨2466656, by rfl⟩ : syracuseStep 3288875 = 4933313) B4933313
theorem B2192583 : Blo 2191435 2192583 := bstep (se 1 (by rfl) ⟨1644437, by rfl⟩ : syracuseStep 2192583 = 3288875) B3288875
theorem B2466661 : Blo 2191435 2466661 := bbase (se 4 (by rfl) ⟨231249, by rfl⟩ : syracuseStep 2466661 = 462499) (by norm_num)
theorem B3288881 : Blo 2191435 3288881 := bstep (se 2 (by rfl) ⟨1233330, by rfl⟩ : syracuseStep 3288881 = 2466661) B2466661
theorem B2192587 : Blo 2191435 2192587 := bstep (se 1 (by rfl) ⟨1644440, by rfl⟩ : syracuseStep 2192587 = 3288881) B3288881
theorem B6243749 : Blo 2191435 6243749 := bbase (se 4 (by rfl) ⟨585351, by rfl⟩ : syracuseStep 6243749 = 1170703) (by norm_num)
theorem B4162499 : Blo 2191435 4162499 := bstep (se 1 (by rfl) ⟨3121874, by rfl⟩ : syracuseStep 4162499 = 6243749) B6243749
theorem B2774999 : Blo 2191435 2774999 := bstep (se 1 (by rfl) ⟨2081249, by rfl⟩ : syracuseStep 2774999 = 4162499) B4162499
theorem B7399997 : Blo 2191435 7399997 := bstep (se 3 (by rfl) ⟨1387499, by rfl⟩ : syracuseStep 7399997 = 2774999) B2774999
theorem B4933331 : Blo 2191435 4933331 := bstep (se 1 (by rfl) ⟨3699998, by rfl⟩ : syracuseStep 4933331 = 7399997) B7399997
theorem B3288887 : Blo 2191435 3288887 := bstep (se 1 (by rfl) ⟨2466665, by rfl⟩ : syracuseStep 3288887 = 4933331) B4933331
theorem B2192591 : Blo 2191435 2192591 := bstep (se 1 (by rfl) ⟨1644443, by rfl⟩ : syracuseStep 2192591 = 3288887) B3288887
theorem B3288893 : Blo 2191435 3288893 := bbase (se 3 (by rfl) ⟨616667, by rfl⟩ : syracuseStep 3288893 = 1233335) (by norm_num)
theorem B2192595 : Blo 2191435 2192595 := bstep (se 1 (by rfl) ⟨1644446, by rfl⟩ : syracuseStep 2192595 = 3288893) B3288893
theorem B4933349 : Blo 2191435 4933349 := bbase (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) (by norm_num)
theorem B3288899 : Blo 2191435 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B2192599 : Blo 2191435 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B5550029 : Blo 2191435 5550029 := bbase (se 3 (by rfl) ⟨1040630, by rfl⟩ : syracuseStep 5550029 = 2081261) (by norm_num)
theorem B3700019 : Blo 2191435 3700019 := bstep (se 1 (by rfl) ⟨2775014, by rfl⟩ : syracuseStep 3700019 = 5550029) B5550029
theorem B2466679 : Blo 2191435 2466679 := bstep (se 1 (by rfl) ⟨1850009, by rfl⟩ : syracuseStep 2466679 = 3700019) B3700019
theorem B3288905 : Blo 2191435 3288905 := bstep (se 2 (by rfl) ⟨1233339, by rfl⟩ : syracuseStep 3288905 = 2466679) B2466679
theorem B2192603 : Blo 2191435 2192603 := bstep (se 1 (by rfl) ⟨1644452, by rfl⟩ : syracuseStep 2192603 = 3288905) B3288905
theorem B3750509 : Blo 2191435 3750509 := bbase (se 3 (by rfl) ⟨703220, by rfl⟩ : syracuseStep 3750509 = 1406441) (by norm_num)
theorem B10001357 : Blo 2191435 10001357 := bstep (se 3 (by rfl) ⟨1875254, by rfl⟩ : syracuseStep 10001357 = 3750509) B3750509
theorem B6667571 : Blo 2191435 6667571 := bstep (se 1 (by rfl) ⟨5000678, by rfl⟩ : syracuseStep 6667571 = 10001357) B10001357
theorem B4445047 : Blo 2191435 4445047 := bstep (se 1 (by rfl) ⟨3333785, by rfl⟩ : syracuseStep 4445047 = 6667571) B6667571
theorem B5926729 : Blo 2191435 5926729 := bstep (se 2 (by rfl) ⟨2222523, by rfl⟩ : syracuseStep 5926729 = 4445047) B4445047
theorem B7902305 : Blo 2191435 7902305 := bstep (se 2 (by rfl) ⟨2963364, by rfl⟩ : syracuseStep 7902305 = 5926729) B5926729
theorem B5268203 : Blo 2191435 5268203 := bstep (se 1 (by rfl) ⟨3951152, by rfl⟩ : syracuseStep 5268203 = 7902305) B7902305
theorem B3512135 : Blo 2191435 3512135 := bstep (se 1 (by rfl) ⟨2634101, by rfl⟩ : syracuseStep 3512135 = 5268203) B5268203
theorem B2341423 : Blo 2191435 2341423 := bstep (se 1 (by rfl) ⟨1756067, by rfl⟩ : syracuseStep 2341423 = 3512135) B3512135
theorem B3121897 : Blo 2191435 3121897 := bstep (se 2 (by rfl) ⟨1170711, by rfl⟩ : syracuseStep 3121897 = 2341423) B2341423
theorem B4162529 : Blo 2191435 4162529 := bstep (se 2 (by rfl) ⟨1560948, by rfl⟩ : syracuseStep 4162529 = 3121897) B3121897
theorem B11100077 : Blo 2191435 11100077 := bstep (se 3 (by rfl) ⟨2081264, by rfl⟩ : syracuseStep 11100077 = 4162529) B4162529
theorem B7400051 : Blo 2191435 7400051 := bstep (se 1 (by rfl) ⟨5550038, by rfl⟩ : syracuseStep 7400051 = 11100077) B11100077
theorem B4933367 : Blo 2191435 4933367 := bstep (se 1 (by rfl) ⟨3700025, by rfl⟩ : syracuseStep 4933367 = 7400051) B7400051
theorem B3288911 : Blo 2191435 3288911 := bstep (se 1 (by rfl) ⟨2466683, by rfl⟩ : syracuseStep 3288911 = 4933367) B4933367
theorem B2192607 : Blo 2191435 2192607 := bstep (se 1 (by rfl) ⟨1644455, by rfl⟩ : syracuseStep 2192607 = 3288911) B3288911
theorem B3288917 : Blo 2191435 3288917 := bbase (se 9 (by rfl) ⟨9635, by rfl⟩ : syracuseStep 3288917 = 19271) (by norm_num)
theorem B2192611 : Blo 2191435 2192611 := bstep (se 1 (by rfl) ⟨1644458, by rfl⟩ : syracuseStep 2192611 = 3288917) B3288917
theorem B7120133 : Blo 2191435 7120133 := bbase (se 4 (by rfl) ⟨667512, by rfl⟩ : syracuseStep 7120133 = 1335025) (by norm_num)
theorem B4746755 : Blo 2191435 4746755 := bstep (se 1 (by rfl) ⟨3560066, by rfl⟩ : syracuseStep 4746755 = 7120133) B7120133
theorem B3164503 : Blo 2191435 3164503 := bstep (se 1 (by rfl) ⟨2373377, by rfl⟩ : syracuseStep 3164503 = 4746755) B4746755
theorem B4219337 : Blo 2191435 4219337 := bstep (se 2 (by rfl) ⟨1582251, by rfl⟩ : syracuseStep 4219337 = 3164503) B3164503
theorem B11251565 : Blo 2191435 11251565 := bstep (se 3 (by rfl) ⟨2109668, by rfl⟩ : syracuseStep 11251565 = 4219337) B4219337
theorem B7501043 : Blo 2191435 7501043 := bstep (se 1 (by rfl) ⟨5625782, by rfl⟩ : syracuseStep 7501043 = 11251565) B11251565
theorem B20002781 : Blo 2191435 20002781 := bstep (se 3 (by rfl) ⟨3750521, by rfl⟩ : syracuseStep 20002781 = 7501043) B7501043
theorem B13335187 : Blo 2191435 13335187 := bstep (se 1 (by rfl) ⟨10001390, by rfl⟩ : syracuseStep 13335187 = 20002781) B20002781
theorem B17780249 : Blo 2191435 17780249 := bstep (se 2 (by rfl) ⟨6667593, by rfl⟩ : syracuseStep 17780249 = 13335187) B13335187
theorem B11853499 : Blo 2191435 11853499 := bstep (se 1 (by rfl) ⟨8890124, by rfl⟩ : syracuseStep 11853499 = 17780249) B17780249
theorem B15804665 : Blo 2191435 15804665 := bstep (se 2 (by rfl) ⟨5926749, by rfl⟩ : syracuseStep 15804665 = 11853499) B11853499
theorem B10536443 : Blo 2191435 10536443 := bstep (se 1 (by rfl) ⟨7902332, by rfl⟩ : syracuseStep 10536443 = 15804665) B15804665
theorem B7024295 : Blo 2191435 7024295 := bstep (se 1 (by rfl) ⟨5268221, by rfl⟩ : syracuseStep 7024295 = 10536443) B10536443
theorem B4682863 : Blo 2191435 4682863 := bstep (se 1 (by rfl) ⟨3512147, by rfl⟩ : syracuseStep 4682863 = 7024295) B7024295
theorem B6243817 : Blo 2191435 6243817 := bstep (se 2 (by rfl) ⟨2341431, by rfl⟩ : syracuseStep 6243817 = 4682863) B4682863
theorem B8325089 : Blo 2191435 8325089 := bstep (se 2 (by rfl) ⟨3121908, by rfl⟩ : syracuseStep 8325089 = 6243817) B6243817
theorem B5550059 : Blo 2191435 5550059 := bstep (se 1 (by rfl) ⟨4162544, by rfl⟩ : syracuseStep 5550059 = 8325089) B8325089
theorem B3700039 : Blo 2191435 3700039 := bstep (se 1 (by rfl) ⟨2775029, by rfl⟩ : syracuseStep 3700039 = 5550059) B5550059
theorem B4933385 : Blo 2191435 4933385 := bstep (se 2 (by rfl) ⟨1850019, by rfl⟩ : syracuseStep 4933385 = 3700039) B3700039
theorem B3288923 : Blo 2191435 3288923 := bstep (se 1 (by rfl) ⟨2466692, by rfl⟩ : syracuseStep 3288923 = 4933385) B4933385
theorem B2192615 : Blo 2191435 2192615 := bstep (se 1 (by rfl) ⟨1644461, by rfl⟩ : syracuseStep 2192615 = 3288923) B3288923
theorem B2466697 : Blo 2191435 2466697 := bbase (se 2 (by rfl) ⟨925011, by rfl⟩ : syracuseStep 2466697 = 1850023) (by norm_num)
theorem B3288929 : Blo 2191435 3288929 := bstep (se 2 (by rfl) ⟨1233348, by rfl⟩ : syracuseStep 3288929 = 2466697) B2466697
theorem B2192619 : Blo 2191435 2192619 := bstep (se 1 (by rfl) ⟨1644464, by rfl⟩ : syracuseStep 2192619 = 3288929) B3288929
theorem B40551509 : Blo 2191435 40551509 := bbase (se 8 (by rfl) ⟨237606, by rfl⟩ : syracuseStep 40551509 = 475213) (by norm_num)
theorem B27034339 : Blo 2191435 27034339 := bstep (se 1 (by rfl) ⟨20275754, by rfl⟩ : syracuseStep 27034339 = 40551509) B40551509
theorem B36045785 : Blo 2191435 36045785 := bstep (se 2 (by rfl) ⟨13517169, by rfl⟩ : syracuseStep 36045785 = 27034339) B27034339
theorem B24030523 : Blo 2191435 24030523 := bstep (se 1 (by rfl) ⟨18022892, by rfl⟩ : syracuseStep 24030523 = 36045785) B36045785
theorem B32040697 : Blo 2191435 32040697 := bstep (se 2 (by rfl) ⟨12015261, by rfl⟩ : syracuseStep 32040697 = 24030523) B24030523
theorem B42720929 : Blo 2191435 42720929 := bstep (se 2 (by rfl) ⟨16020348, by rfl⟩ : syracuseStep 42720929 = 32040697) B32040697
theorem B28480619 : Blo 2191435 28480619 := bstep (se 1 (by rfl) ⟨21360464, by rfl⟩ : syracuseStep 28480619 = 42720929) B42720929
theorem B75948317 : Blo 2191435 75948317 := bstep (se 3 (by rfl) ⟨14240309, by rfl⟩ : syracuseStep 75948317 = 28480619) B28480619
theorem B50632211 : Blo 2191435 50632211 := bstep (se 1 (by rfl) ⟨37974158, by rfl⟩ : syracuseStep 50632211 = 75948317) B75948317
theorem B135019229 : Blo 2191435 135019229 := bstep (se 3 (by rfl) ⟨25316105, by rfl⟩ : syracuseStep 135019229 = 50632211) B50632211
theorem B360051277 : Blo 2191435 360051277 := bstep (se 3 (by rfl) ⟨67509614, by rfl⟩ : syracuseStep 360051277 = 135019229) B135019229
theorem B480068369 : Blo 2191435 480068369 := bstep (se 2 (by rfl) ⟨180025638, by rfl⟩ : syracuseStep 480068369 = 360051277) B360051277
theorem B320045579 : Blo 2191435 320045579 := bstep (se 1 (by rfl) ⟨240034184, by rfl⟩ : syracuseStep 320045579 = 480068369) B480068369
theorem B213363719 : Blo 2191435 213363719 := bstep (se 1 (by rfl) ⟨160022789, by rfl⟩ : syracuseStep 213363719 = 320045579) B320045579
theorem B142242479 : Blo 2191435 142242479 := bstep (se 1 (by rfl) ⟨106681859, by rfl⟩ : syracuseStep 142242479 = 213363719) B213363719
theorem B94828319 : Blo 2191435 94828319 := bstep (se 1 (by rfl) ⟨71121239, by rfl⟩ : syracuseStep 94828319 = 142242479) B142242479
theorem B63218879 : Blo 2191435 63218879 := bstep (se 1 (by rfl) ⟨47414159, by rfl⟩ : syracuseStep 63218879 = 94828319) B94828319
theorem B42145919 : Blo 2191435 42145919 := bstep (se 1 (by rfl) ⟨31609439, by rfl⟩ : syracuseStep 42145919 = 63218879) B63218879
theorem B28097279 : Blo 2191435 28097279 := bstep (se 1 (by rfl) ⟨21072959, by rfl⟩ : syracuseStep 28097279 = 42145919) B42145919
theorem B18731519 : Blo 2191435 18731519 := bstep (se 1 (by rfl) ⟨14048639, by rfl⟩ : syracuseStep 18731519 = 28097279) B28097279
theorem B12487679 : Blo 2191435 12487679 := bstep (se 1 (by rfl) ⟨9365759, by rfl⟩ : syracuseStep 12487679 = 18731519) B18731519
theorem B8325119 : Blo 2191435 8325119 := bstep (se 1 (by rfl) ⟨6243839, by rfl⟩ : syracuseStep 8325119 = 12487679) B12487679
theorem B5550079 : Blo 2191435 5550079 := bstep (se 1 (by rfl) ⟨4162559, by rfl⟩ : syracuseStep 5550079 = 8325119) B8325119
theorem B7400105 : Blo 2191435 7400105 := bstep (se 2 (by rfl) ⟨2775039, by rfl⟩ : syracuseStep 7400105 = 5550079) B5550079
theorem B4933403 : Blo 2191435 4933403 := bstep (se 1 (by rfl) ⟨3700052, by rfl⟩ : syracuseStep 4933403 = 7400105) B7400105
theorem B3288935 : Blo 2191435 3288935 := bstep (se 1 (by rfl) ⟨2466701, by rfl⟩ : syracuseStep 3288935 = 4933403) B4933403
theorem B2192623 : Blo 2191435 2192623 := bstep (se 1 (by rfl) ⟨1644467, by rfl⟩ : syracuseStep 2192623 = 3288935) B3288935
theorem B3288941 : Blo 2191435 3288941 := bbase (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) (by norm_num)
theorem B2192627 : Blo 2191435 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B4933421 : Blo 2191435 4933421 := bbase (se 3 (by rfl) ⟨925016, by rfl⟩ : syracuseStep 4933421 = 1850033) (by norm_num)
theorem B3288947 : Blo 2191435 3288947 := bstep (se 1 (by rfl) ⟨2466710, by rfl⟩ : syracuseStep 3288947 = 4933421) B4933421
theorem B2192631 : Blo 2191435 2192631 := bstep (se 1 (by rfl) ⟨1644473, by rfl⟩ : syracuseStep 2192631 = 3288947) B3288947
theorem B9365813 : Blo 2191435 9365813 := bbase (se 5 (by rfl) ⟨439022, by rfl⟩ : syracuseStep 9365813 = 878045) (by norm_num)
theorem B6243875 : Blo 2191435 6243875 := bstep (se 1 (by rfl) ⟨4682906, by rfl⟩ : syracuseStep 6243875 = 9365813) B9365813
theorem B4162583 : Blo 2191435 4162583 := bstep (se 1 (by rfl) ⟨3121937, by rfl⟩ : syracuseStep 4162583 = 6243875) B6243875
theorem B2775055 : Blo 2191435 2775055 := bstep (se 1 (by rfl) ⟨2081291, by rfl⟩ : syracuseStep 2775055 = 4162583) B4162583
theorem B3700073 : Blo 2191435 3700073 := bstep (se 2 (by rfl) ⟨1387527, by rfl⟩ : syracuseStep 3700073 = 2775055) B2775055
theorem B2466715 : Blo 2191435 2466715 := bstep (se 1 (by rfl) ⟨1850036, by rfl⟩ : syracuseStep 2466715 = 3700073) B3700073
theorem B3288953 : Blo 2191435 3288953 := bstep (se 2 (by rfl) ⟨1233357, by rfl⟩ : syracuseStep 3288953 = 2466715) B2466715
theorem B2192635 : Blo 2191435 2192635 := bstep (se 1 (by rfl) ⟨1644476, by rfl⟩ : syracuseStep 2192635 = 3288953) B3288953
theorem B5625845 : Blo 2191435 5625845 := bbase (se 5 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 5625845 = 527423) (by norm_num)
theorem B3750563 : Blo 2191435 3750563 := bstep (se 1 (by rfl) ⟨2812922, by rfl⟩ : syracuseStep 3750563 = 5625845) B5625845
theorem B10001501 : Blo 2191435 10001501 := bstep (se 3 (by rfl) ⟨1875281, by rfl⟩ : syracuseStep 10001501 = 3750563) B3750563
theorem B6667667 : Blo 2191435 6667667 := bstep (se 1 (by rfl) ⟨5000750, by rfl⟩ : syracuseStep 6667667 = 10001501) B10001501
theorem B4445111 : Blo 2191435 4445111 := bstep (se 1 (by rfl) ⟨3333833, by rfl⟩ : syracuseStep 4445111 = 6667667) B6667667
theorem B2963407 : Blo 2191435 2963407 := bstep (se 1 (by rfl) ⟨2222555, by rfl⟩ : syracuseStep 2963407 = 4445111) B4445111
theorem B3951209 : Blo 2191435 3951209 := bstep (se 2 (by rfl) ⟨1481703, by rfl⟩ : syracuseStep 3951209 = 2963407) B2963407
theorem B2634139 : Blo 2191435 2634139 := bstep (se 1 (by rfl) ⟨1975604, by rfl⟩ : syracuseStep 2634139 = 3951209) B3951209
theorem B14048741 : Blo 2191435 14048741 := bstep (se 4 (by rfl) ⟨1317069, by rfl⟩ : syracuseStep 14048741 = 2634139) B2634139
theorem B37463309 : Blo 2191435 37463309 := bstep (se 3 (by rfl) ⟨7024370, by rfl⟩ : syracuseStep 37463309 = 14048741) B14048741
theorem B24975539 : Blo 2191435 24975539 := bstep (se 1 (by rfl) ⟨18731654, by rfl⟩ : syracuseStep 24975539 = 37463309) B37463309
theorem B16650359 : Blo 2191435 16650359 := bstep (se 1 (by rfl) ⟨12487769, by rfl⟩ : syracuseStep 16650359 = 24975539) B24975539
theorem B11100239 : Blo 2191435 11100239 := bstep (se 1 (by rfl) ⟨8325179, by rfl⟩ : syracuseStep 11100239 = 16650359) B16650359
theorem B7400159 : Blo 2191435 7400159 := bstep (se 1 (by rfl) ⟨5550119, by rfl⟩ : syracuseStep 7400159 = 11100239) B11100239
theorem B4933439 : Blo 2191435 4933439 := bstep (se 1 (by rfl) ⟨3700079, by rfl⟩ : syracuseStep 4933439 = 7400159) B7400159
theorem B3288959 : Blo 2191435 3288959 := bstep (se 1 (by rfl) ⟨2466719, by rfl⟩ : syracuseStep 3288959 = 4933439) B4933439
theorem B2192639 : Blo 2191435 2192639 := bstep (se 1 (by rfl) ⟨1644479, by rfl⟩ : syracuseStep 2192639 = 3288959) B3288959
theorem B3288965 : Blo 2191435 3288965 := bbase (se 4 (by rfl) ⟨308340, by rfl⟩ : syracuseStep 3288965 = 616681) (by norm_num)
theorem B2192643 : Blo 2191435 2192643 := bstep (se 1 (by rfl) ⟨1644482, by rfl⟩ : syracuseStep 2192643 = 3288965) B3288965
theorem B3700093 : Blo 2191435 3700093 := bbase (se 3 (by rfl) ⟨693767, by rfl⟩ : syracuseStep 3700093 = 1387535) (by norm_num)
theorem B4933457 : Blo 2191435 4933457 := bstep (se 2 (by rfl) ⟨1850046, by rfl⟩ : syracuseStep 4933457 = 3700093) B3700093
theorem B3288971 : Blo 2191435 3288971 := bstep (se 1 (by rfl) ⟨2466728, by rfl⟩ : syracuseStep 3288971 = 4933457) B4933457
theorem B2192647 : Blo 2191435 2192647 := bstep (se 1 (by rfl) ⟨1644485, by rfl⟩ : syracuseStep 2192647 = 3288971) B3288971
theorem B2466733 : Blo 2191435 2466733 := bbase (se 3 (by rfl) ⟨462512, by rfl⟩ : syracuseStep 2466733 = 925025) (by norm_num)
theorem B3288977 : Blo 2191435 3288977 := bstep (se 2 (by rfl) ⟨1233366, by rfl⟩ : syracuseStep 3288977 = 2466733) B2466733
theorem B2192651 : Blo 2191435 2192651 := bstep (se 1 (by rfl) ⟨1644488, by rfl⟩ : syracuseStep 2192651 = 3288977) B3288977
theorem B7400213 : Blo 2191435 7400213 := bbase (se 6 (by rfl) ⟨173442, by rfl⟩ : syracuseStep 7400213 = 346885) (by norm_num)
theorem B4933475 : Blo 2191435 4933475 := bstep (se 1 (by rfl) ⟨3700106, by rfl⟩ : syracuseStep 4933475 = 7400213) B7400213
theorem B3288983 : Blo 2191435 3288983 := bstep (se 1 (by rfl) ⟨2466737, by rfl⟩ : syracuseStep 3288983 = 4933475) B4933475
theorem B2192655 : Blo 2191435 2192655 := bstep (se 1 (by rfl) ⟨1644491, by rfl⟩ : syracuseStep 2192655 = 3288983) B3288983
theorem B3288989 : Blo 2191435 3288989 := bbase (se 3 (by rfl) ⟨616685, by rfl⟩ : syracuseStep 3288989 = 1233371) (by norm_num)
theorem B2192659 : Blo 2191435 2192659 := bstep (se 1 (by rfl) ⟨1644494, by rfl⟩ : syracuseStep 2192659 = 3288989) B3288989
theorem B4933493 : Blo 2191435 4933493 := bbase (se 5 (by rfl) ⟨231257, by rfl⟩ : syracuseStep 4933493 = 462515) (by norm_num)
theorem B3288995 : Blo 2191435 3288995 := bstep (se 1 (by rfl) ⟨2466746, by rfl⟩ : syracuseStep 3288995 = 4933493) B4933493
theorem B2192663 : Blo 2191435 2192663 := bstep (se 1 (by rfl) ⟨1644497, by rfl⟩ : syracuseStep 2192663 = 3288995) B3288995
theorem B2373433 : Blo 2191435 2373433 := bbase (se 2 (by rfl) ⟨890037, by rfl⟩ : syracuseStep 2373433 = 1780075) (by norm_num)
theorem B50633237 : Blo 2191435 50633237 := bstep (se 6 (by rfl) ⟨1186716, by rfl⟩ : syracuseStep 50633237 = 2373433) B2373433
theorem B33755491 : Blo 2191435 33755491 := bstep (se 1 (by rfl) ⟨25316618, by rfl⟩ : syracuseStep 33755491 = 50633237) B50633237
theorem B45007321 : Blo 2191435 45007321 := bstep (se 2 (by rfl) ⟨16877745, by rfl⟩ : syracuseStep 45007321 = 33755491) B33755491
theorem B60009761 : Blo 2191435 60009761 := bstep (se 2 (by rfl) ⟨22503660, by rfl⟩ : syracuseStep 60009761 = 45007321) B45007321
theorem B40006507 : Blo 2191435 40006507 := bstep (se 1 (by rfl) ⟨30004880, by rfl⟩ : syracuseStep 40006507 = 60009761) B60009761
theorem B53342009 : Blo 2191435 53342009 := bstep (se 2 (by rfl) ⟨20003253, by rfl⟩ : syracuseStep 53342009 = 40006507) B40006507
theorem B35561339 : Blo 2191435 35561339 := bstep (se 1 (by rfl) ⟨26671004, by rfl⟩ : syracuseStep 35561339 = 53342009) B53342009
theorem B23707559 : Blo 2191435 23707559 := bstep (se 1 (by rfl) ⟨17780669, by rfl⟩ : syracuseStep 23707559 = 35561339) B35561339
theorem B15805039 : Blo 2191435 15805039 := bstep (se 1 (by rfl) ⟨11853779, by rfl⟩ : syracuseStep 15805039 = 23707559) B23707559
theorem B21073385 : Blo 2191435 21073385 := bstep (se 2 (by rfl) ⟨7902519, by rfl⟩ : syracuseStep 21073385 = 15805039) B15805039
theorem B14048923 : Blo 2191435 14048923 := bstep (se 1 (by rfl) ⟨10536692, by rfl⟩ : syracuseStep 14048923 = 21073385) B21073385
theorem B18731897 : Blo 2191435 18731897 := bstep (se 2 (by rfl) ⟨7024461, by rfl⟩ : syracuseStep 18731897 = 14048923) B14048923
theorem B12487931 : Blo 2191435 12487931 := bstep (se 1 (by rfl) ⟨9365948, by rfl⟩ : syracuseStep 12487931 = 18731897) B18731897
theorem B8325287 : Blo 2191435 8325287 := bstep (se 1 (by rfl) ⟨6243965, by rfl⟩ : syracuseStep 8325287 = 12487931) B12487931
theorem B5550191 : Blo 2191435 5550191 := bstep (se 1 (by rfl) ⟨4162643, by rfl⟩ : syracuseStep 5550191 = 8325287) B8325287
theorem B3700127 : Blo 2191435 3700127 := bstep (se 1 (by rfl) ⟨2775095, by rfl⟩ : syracuseStep 3700127 = 5550191) B5550191
theorem B2466751 : Blo 2191435 2466751 := bstep (se 1 (by rfl) ⟨1850063, by rfl⟩ : syracuseStep 2466751 = 3700127) B3700127
theorem B3289001 : Blo 2191435 3289001 := bstep (se 2 (by rfl) ⟨1233375, by rfl⟩ : syracuseStep 3289001 = 2466751) B2466751
theorem B2192667 : Blo 2191435 2192667 := bstep (se 1 (by rfl) ⟨1644500, by rfl⟩ : syracuseStep 2192667 = 3289001) B3289001
theorem B8325301 : Blo 2191435 8325301 := bbase (se 5 (by rfl) ⟨390248, by rfl⟩ : syracuseStep 8325301 = 780497) (by norm_num)
theorem B11100401 : Blo 2191435 11100401 := bstep (se 2 (by rfl) ⟨4162650, by rfl⟩ : syracuseStep 11100401 = 8325301) B8325301
theorem B7400267 : Blo 2191435 7400267 := bstep (se 1 (by rfl) ⟨5550200, by rfl⟩ : syracuseStep 7400267 = 11100401) B11100401
theorem B4933511 : Blo 2191435 4933511 := bstep (se 1 (by rfl) ⟨3700133, by rfl⟩ : syracuseStep 4933511 = 7400267) B7400267
theorem B3289007 : Blo 2191435 3289007 := bstep (se 1 (by rfl) ⟨2466755, by rfl⟩ : syracuseStep 3289007 = 4933511) B4933511
theorem B2192671 : Blo 2191435 2192671 := bstep (se 1 (by rfl) ⟨1644503, by rfl⟩ : syracuseStep 2192671 = 3289007) B3289007
theorem B3289013 : Blo 2191435 3289013 := bbase (se 5 (by rfl) ⟨154172, by rfl⟩ : syracuseStep 3289013 = 308345) (by norm_num)
theorem B2192675 : Blo 2191435 2192675 := bstep (se 1 (by rfl) ⟨1644506, by rfl⟩ : syracuseStep 2192675 = 3289013) B3289013
theorem B5550221 : Blo 2191435 5550221 := bbase (se 3 (by rfl) ⟨1040666, by rfl⟩ : syracuseStep 5550221 = 2081333) (by norm_num)
theorem B3700147 : Blo 2191435 3700147 := bstep (se 1 (by rfl) ⟨2775110, by rfl⟩ : syracuseStep 3700147 = 5550221) B5550221
theorem B4933529 : Blo 2191435 4933529 := bstep (se 2 (by rfl) ⟨1850073, by rfl⟩ : syracuseStep 4933529 = 3700147) B3700147
theorem B3289019 : Blo 2191435 3289019 := bstep (se 1 (by rfl) ⟨2466764, by rfl⟩ : syracuseStep 3289019 = 4933529) B4933529
theorem B2192679 : Blo 2191435 2192679 := bstep (se 1 (by rfl) ⟨1644509, by rfl⟩ : syracuseStep 2192679 = 3289019) B3289019
theorem B2466769 : Blo 2191435 2466769 := bbase (se 2 (by rfl) ⟨925038, by rfl⟩ : syracuseStep 2466769 = 1850077) (by norm_num)
theorem B3289025 : Blo 2191435 3289025 := bstep (se 2 (by rfl) ⟨1233384, by rfl⟩ : syracuseStep 3289025 = 2466769) B2466769
theorem B2192683 : Blo 2191435 2192683 := bstep (se 1 (by rfl) ⟨1644512, by rfl⟩ : syracuseStep 2192683 = 3289025) B3289025
theorem B5000861 : Blo 2191435 5000861 := bbase (se 3 (by rfl) ⟨937661, by rfl⟩ : syracuseStep 5000861 = 1875323) (by norm_num)
theorem B3333907 : Blo 2191435 3333907 := bstep (se 1 (by rfl) ⟨2500430, by rfl⟩ : syracuseStep 3333907 = 5000861) B5000861
theorem B4445209 : Blo 2191435 4445209 := bstep (se 2 (by rfl) ⟨1666953, by rfl⟩ : syracuseStep 4445209 = 3333907) B3333907
theorem B5926945 : Blo 2191435 5926945 := bstep (se 2 (by rfl) ⟨2222604, by rfl⟩ : syracuseStep 5926945 = 4445209) B4445209
theorem B7902593 : Blo 2191435 7902593 := bstep (se 2 (by rfl) ⟨2963472, by rfl⟩ : syracuseStep 7902593 = 5926945) B5926945
theorem B5268395 : Blo 2191435 5268395 := bstep (se 1 (by rfl) ⟨3951296, by rfl⟩ : syracuseStep 5268395 = 7902593) B7902593
theorem B3512263 : Blo 2191435 3512263 := bstep (se 1 (by rfl) ⟨2634197, by rfl⟩ : syracuseStep 3512263 = 5268395) B5268395
theorem B4683017 : Blo 2191435 4683017 := bstep (se 2 (by rfl) ⟨1756131, by rfl⟩ : syracuseStep 4683017 = 3512263) B3512263
theorem B3122011 : Blo 2191435 3122011 := bstep (se 1 (by rfl) ⟨2341508, by rfl⟩ : syracuseStep 3122011 = 4683017) B4683017
theorem B4162681 : Blo 2191435 4162681 := bstep (se 2 (by rfl) ⟨1561005, by rfl⟩ : syracuseStep 4162681 = 3122011) B3122011
theorem B5550241 : Blo 2191435 5550241 := bstep (se 2 (by rfl) ⟨2081340, by rfl⟩ : syracuseStep 5550241 = 4162681) B4162681
theorem B7400321 : Blo 2191435 7400321 := bstep (se 2 (by rfl) ⟨2775120, by rfl⟩ : syracuseStep 7400321 = 5550241) B5550241
theorem B4933547 : Blo 2191435 4933547 := bstep (se 1 (by rfl) ⟨3700160, by rfl⟩ : syracuseStep 4933547 = 7400321) B7400321
theorem B3289031 : Blo 2191435 3289031 := bstep (se 1 (by rfl) ⟨2466773, by rfl⟩ : syracuseStep 3289031 = 4933547) B4933547
theorem B2192687 : Blo 2191435 2192687 := bstep (se 1 (by rfl) ⟨1644515, by rfl⟩ : syracuseStep 2192687 = 3289031) B3289031
theorem B3289037 : Blo 2191435 3289037 := bbase (se 3 (by rfl) ⟨616694, by rfl⟩ : syracuseStep 3289037 = 1233389) (by norm_num)
theorem B2192691 : Blo 2191435 2192691 := bstep (se 1 (by rfl) ⟨1644518, by rfl⟩ : syracuseStep 2192691 = 3289037) B3289037
theorem B4933565 : Blo 2191435 4933565 := bbase (se 3 (by rfl) ⟨925043, by rfl⟩ : syracuseStep 4933565 = 1850087) (by norm_num)
theorem B3289043 : Blo 2191435 3289043 := bstep (se 1 (by rfl) ⟨2466782, by rfl⟩ : syracuseStep 3289043 = 4933565) B4933565
theorem B2192695 : Blo 2191435 2192695 := bstep (se 1 (by rfl) ⟨1644521, by rfl⟩ : syracuseStep 2192695 = 3289043) B3289043
theorem B3700181 : Blo 2191435 3700181 := bbase (se 7 (by rfl) ⟨43361, by rfl⟩ : syracuseStep 3700181 = 86723) (by norm_num)
theorem B2466787 : Blo 2191435 2466787 := bstep (se 1 (by rfl) ⟨1850090, by rfl⟩ : syracuseStep 2466787 = 3700181) B3700181
theorem B3289049 : Blo 2191435 3289049 := bstep (se 2 (by rfl) ⟨1233393, by rfl⟩ : syracuseStep 3289049 = 2466787) B2466787
theorem B2192699 : Blo 2191435 2192699 := bstep (se 1 (by rfl) ⟨1644524, by rfl⟩ : syracuseStep 2192699 = 3289049) B3289049
theorem B9366101 : Blo 2191435 9366101 := bbase (se 8 (by rfl) ⟨54879, by rfl⟩ : syracuseStep 9366101 = 109759) (by norm_num)
theorem B6244067 : Blo 2191435 6244067 := bstep (se 1 (by rfl) ⟨4683050, by rfl⟩ : syracuseStep 6244067 = 9366101) B9366101
theorem B16650845 : Blo 2191435 16650845 := bstep (se 3 (by rfl) ⟨3122033, by rfl⟩ : syracuseStep 16650845 = 6244067) B6244067
theorem B11100563 : Blo 2191435 11100563 := bstep (se 1 (by rfl) ⟨8325422, by rfl⟩ : syracuseStep 11100563 = 16650845) B16650845
theorem B7400375 : Blo 2191435 7400375 := bstep (se 1 (by rfl) ⟨5550281, by rfl⟩ : syracuseStep 7400375 = 11100563) B11100563
theorem B4933583 : Blo 2191435 4933583 := bstep (se 1 (by rfl) ⟨3700187, by rfl⟩ : syracuseStep 4933583 = 7400375) B7400375
theorem B3289055 : Blo 2191435 3289055 := bstep (se 1 (by rfl) ⟨2466791, by rfl⟩ : syracuseStep 3289055 = 4933583) B4933583
theorem B2192703 : Blo 2191435 2192703 := bstep (se 1 (by rfl) ⟨1644527, by rfl⟩ : syracuseStep 2192703 = 3289055) B3289055
theorem B3289061 : Blo 2191435 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B2192707 : Blo 2191435 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B6329285 : Blo 2191435 6329285 := bbase (se 4 (by rfl) ⟨593370, by rfl⟩ : syracuseStep 6329285 = 1186741) (by norm_num)
theorem B4219523 : Blo 2191435 4219523 := bstep (se 1 (by rfl) ⟨3164642, by rfl⟩ : syracuseStep 4219523 = 6329285) B6329285
theorem B2813015 : Blo 2191435 2813015 := bstep (se 1 (by rfl) ⟨2109761, by rfl⟩ : syracuseStep 2813015 = 4219523) B4219523
theorem B7501373 : Blo 2191435 7501373 := bstep (se 3 (by rfl) ⟨1406507, by rfl⟩ : syracuseStep 7501373 = 2813015) B2813015
theorem B5000915 : Blo 2191435 5000915 := bstep (se 1 (by rfl) ⟨3750686, by rfl⟩ : syracuseStep 5000915 = 7501373) B7501373
theorem B3333943 : Blo 2191435 3333943 := bstep (se 1 (by rfl) ⟨2500457, by rfl⟩ : syracuseStep 3333943 = 5000915) B5000915
theorem B17781029 : Blo 2191435 17781029 := bstep (se 4 (by rfl) ⟨1666971, by rfl⟩ : syracuseStep 17781029 = 3333943) B3333943
theorem B11854019 : Blo 2191435 11854019 := bstep (se 1 (by rfl) ⟨8890514, by rfl⟩ : syracuseStep 11854019 = 17781029) B17781029
theorem B7902679 : Blo 2191435 7902679 := bstep (se 1 (by rfl) ⟨5927009, by rfl⟩ : syracuseStep 7902679 = 11854019) B11854019
theorem B10536905 : Blo 2191435 10536905 := bstep (se 2 (by rfl) ⟨3951339, by rfl⟩ : syracuseStep 10536905 = 7902679) B7902679
theorem B7024603 : Blo 2191435 7024603 := bstep (se 1 (by rfl) ⟨5268452, by rfl⟩ : syracuseStep 7024603 = 10536905) B10536905
theorem B9366137 : Blo 2191435 9366137 := bstep (se 2 (by rfl) ⟨3512301, by rfl⟩ : syracuseStep 9366137 = 7024603) B7024603
theorem B6244091 : Blo 2191435 6244091 := bstep (se 1 (by rfl) ⟨4683068, by rfl⟩ : syracuseStep 6244091 = 9366137) B9366137
theorem B4162727 : Blo 2191435 4162727 := bstep (se 1 (by rfl) ⟨3122045, by rfl⟩ : syracuseStep 4162727 = 6244091) B6244091
theorem B2775151 : Blo 2191435 2775151 := bstep (se 1 (by rfl) ⟨2081363, by rfl⟩ : syracuseStep 2775151 = 4162727) B4162727
theorem B3700201 : Blo 2191435 3700201 := bstep (se 2 (by rfl) ⟨1387575, by rfl⟩ : syracuseStep 3700201 = 2775151) B2775151
theorem B4933601 : Blo 2191435 4933601 := bstep (se 2 (by rfl) ⟨1850100, by rfl⟩ : syracuseStep 4933601 = 3700201) B3700201
theorem B3289067 : Blo 2191435 3289067 := bstep (se 1 (by rfl) ⟨2466800, by rfl⟩ : syracuseStep 3289067 = 4933601) B4933601
theorem B2192711 : Blo 2191435 2192711 := bstep (se 1 (by rfl) ⟨1644533, by rfl⟩ : syracuseStep 2192711 = 3289067) B3289067
theorem B2466805 : Blo 2191435 2466805 := bbase (se 5 (by rfl) ⟨115631, by rfl⟩ : syracuseStep 2466805 = 231263) (by norm_num)
theorem B3289073 : Blo 2191435 3289073 := bstep (se 2 (by rfl) ⟨1233402, by rfl⟩ : syracuseStep 3289073 = 2466805) B2466805
theorem B2192715 : Blo 2191435 2192715 := bstep (se 1 (by rfl) ⟨1644536, by rfl⟩ : syracuseStep 2192715 = 3289073) B3289073
theorem B2775161 : Blo 2191435 2775161 := bbase (se 2 (by rfl) ⟨1040685, by rfl⟩ : syracuseStep 2775161 = 2081371) (by norm_num)
theorem B7400429 : Blo 2191435 7400429 := bstep (se 3 (by rfl) ⟨1387580, by rfl⟩ : syracuseStep 7400429 = 2775161) B2775161
theorem B4933619 : Blo 2191435 4933619 := bstep (se 1 (by rfl) ⟨3700214, by rfl⟩ : syracuseStep 4933619 = 7400429) B7400429
theorem B3289079 : Blo 2191435 3289079 := bstep (se 1 (by rfl) ⟨2466809, by rfl⟩ : syracuseStep 3289079 = 4933619) B4933619
theorem B2192719 : Blo 2191435 2192719 := bstep (se 1 (by rfl) ⟨1644539, by rfl⟩ : syracuseStep 2192719 = 3289079) B3289079
theorem B3289085 : Blo 2191435 3289085 := bbase (se 3 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 3289085 = 1233407) (by norm_num)
theorem B2192723 : Blo 2191435 2192723 := bstep (se 1 (by rfl) ⟨1644542, by rfl⟩ : syracuseStep 2192723 = 3289085) B3289085
theorem B4933637 : Blo 2191435 4933637 := bbase (se 4 (by rfl) ⟨462528, by rfl⟩ : syracuseStep 4933637 = 925057) (by norm_num)
theorem B3289091 : Blo 2191435 3289091 := bstep (se 1 (by rfl) ⟨2466818, by rfl⟩ : syracuseStep 3289091 = 4933637) B4933637
theorem B2192727 : Blo 2191435 2192727 := bstep (se 1 (by rfl) ⟨1644545, by rfl⟩ : syracuseStep 2192727 = 3289091) B3289091
theorem B4162765 : Blo 2191435 4162765 := bbase (se 3 (by rfl) ⟨780518, by rfl⟩ : syracuseStep 4162765 = 1561037) (by norm_num)
theorem B5550353 : Blo 2191435 5550353 := bstep (se 2 (by rfl) ⟨2081382, by rfl⟩ : syracuseStep 5550353 = 4162765) B4162765
theorem B3700235 : Blo 2191435 3700235 := bstep (se 1 (by rfl) ⟨2775176, by rfl⟩ : syracuseStep 3700235 = 5550353) B5550353
theorem B2466823 : Blo 2191435 2466823 := bstep (se 1 (by rfl) ⟨1850117, by rfl⟩ : syracuseStep 2466823 = 3700235) B3700235
theorem B3289097 : Blo 2191435 3289097 := bstep (se 2 (by rfl) ⟨1233411, by rfl⟩ : syracuseStep 3289097 = 2466823) B2466823
theorem B2192731 : Blo 2191435 2192731 := bstep (se 1 (by rfl) ⟨1644548, by rfl⟩ : syracuseStep 2192731 = 3289097) B3289097
theorem B11100725 : Blo 2191435 11100725 := bbase (se 5 (by rfl) ⟨520346, by rfl⟩ : syracuseStep 11100725 = 1040693) (by norm_num)
theorem B7400483 : Blo 2191435 7400483 := bstep (se 1 (by rfl) ⟨5550362, by rfl⟩ : syracuseStep 7400483 = 11100725) B11100725
theorem B4933655 : Blo 2191435 4933655 := bstep (se 1 (by rfl) ⟨3700241, by rfl⟩ : syracuseStep 4933655 = 7400483) B7400483
theorem B3289103 : Blo 2191435 3289103 := bstep (se 1 (by rfl) ⟨2466827, by rfl⟩ : syracuseStep 3289103 = 4933655) B4933655
theorem B2192735 : Blo 2191435 2192735 := bstep (se 1 (by rfl) ⟨1644551, by rfl⟩ : syracuseStep 2192735 = 3289103) B3289103
theorem B3289109 : Blo 2191435 3289109 := bbase (se 6 (by rfl) ⟨77088, by rfl⟩ : syracuseStep 3289109 = 154177) (by norm_num)
theorem B2192739 : Blo 2191435 2192739 := bstep (se 1 (by rfl) ⟨1644554, by rfl⟩ : syracuseStep 2192739 = 3289109) B3289109
theorem B6851173 : Blo 2191435 6851173 := bbase (se 4 (by rfl) ⟨642297, by rfl⟩ : syracuseStep 6851173 = 1284595) (by norm_num)
theorem B9134897 : Blo 2191435 9134897 := bstep (se 2 (by rfl) ⟨3425586, by rfl⟩ : syracuseStep 9134897 = 6851173) B6851173
theorem B24359725 : Blo 2191435 24359725 := bstep (se 3 (by rfl) ⟨4567448, by rfl⟩ : syracuseStep 24359725 = 9134897) B9134897
theorem B32479633 : Blo 2191435 32479633 := bstep (se 2 (by rfl) ⟨12179862, by rfl⟩ : syracuseStep 32479633 = 24359725) B24359725
theorem B43306177 : Blo 2191435 43306177 := bstep (se 2 (by rfl) ⟨16239816, by rfl⟩ : syracuseStep 43306177 = 32479633) B32479633
theorem B57741569 : Blo 2191435 57741569 := bstep (se 2 (by rfl) ⟨21653088, by rfl⟩ : syracuseStep 57741569 = 43306177) B43306177
theorem B38494379 : Blo 2191435 38494379 := bstep (se 1 (by rfl) ⟨28870784, by rfl⟩ : syracuseStep 38494379 = 57741569) B57741569
theorem B25662919 : Blo 2191435 25662919 := bstep (se 1 (by rfl) ⟨19247189, by rfl⟩ : syracuseStep 25662919 = 38494379) B38494379
theorem B34217225 : Blo 2191435 34217225 := bstep (se 2 (by rfl) ⟨12831459, by rfl⟩ : syracuseStep 34217225 = 25662919) B25662919
theorem B22811483 : Blo 2191435 22811483 := bstep (se 1 (by rfl) ⟨17108612, by rfl⟩ : syracuseStep 22811483 = 34217225) B34217225
theorem B60830621 : Blo 2191435 60830621 := bstep (se 3 (by rfl) ⟨11405741, by rfl⟩ : syracuseStep 60830621 = 22811483) B22811483
theorem B40553747 : Blo 2191435 40553747 := bstep (se 1 (by rfl) ⟨30415310, by rfl⟩ : syracuseStep 40553747 = 60830621) B60830621
theorem B27035831 : Blo 2191435 27035831 := bstep (se 1 (by rfl) ⟨20276873, by rfl⟩ : syracuseStep 27035831 = 40553747) B40553747
theorem B18023887 : Blo 2191435 18023887 := bstep (se 1 (by rfl) ⟨13517915, by rfl⟩ : syracuseStep 18023887 = 27035831) B27035831
theorem B96127397 : Blo 2191435 96127397 := bstep (se 4 (by rfl) ⟨9011943, by rfl⟩ : syracuseStep 96127397 = 18023887) B18023887
theorem B64084931 : Blo 2191435 64084931 := bstep (se 1 (by rfl) ⟨48063698, by rfl⟩ : syracuseStep 64084931 = 96127397) B96127397
theorem B42723287 : Blo 2191435 42723287 := bstep (se 1 (by rfl) ⟨32042465, by rfl⟩ : syracuseStep 42723287 = 64084931) B64084931
theorem B28482191 : Blo 2191435 28482191 := bstep (se 1 (by rfl) ⟨21361643, by rfl⟩ : syracuseStep 28482191 = 42723287) B42723287
theorem B18988127 : Blo 2191435 18988127 := bstep (se 1 (by rfl) ⟨14241095, by rfl⟩ : syracuseStep 18988127 = 28482191) B28482191
theorem B12658751 : Blo 2191435 12658751 := bstep (se 1 (by rfl) ⟨9494063, by rfl⟩ : syracuseStep 12658751 = 18988127) B18988127
theorem B8439167 : Blo 2191435 8439167 := bstep (se 1 (by rfl) ⟨6329375, by rfl⟩ : syracuseStep 8439167 = 12658751) B12658751
theorem B5626111 : Blo 2191435 5626111 := bstep (se 1 (by rfl) ⟨4219583, by rfl⟩ : syracuseStep 5626111 = 8439167) B8439167
theorem B7501481 : Blo 2191435 7501481 := bstep (se 2 (by rfl) ⟨2813055, by rfl⟩ : syracuseStep 7501481 = 5626111) B5626111
theorem B5000987 : Blo 2191435 5000987 := bstep (se 1 (by rfl) ⟨3750740, by rfl⟩ : syracuseStep 5000987 = 7501481) B7501481
theorem B13335965 : Blo 2191435 13335965 := bstep (se 3 (by rfl) ⟨2500493, by rfl⟩ : syracuseStep 13335965 = 5000987) B5000987
theorem B8890643 : Blo 2191435 8890643 := bstep (se 1 (by rfl) ⟨6667982, by rfl⟩ : syracuseStep 8890643 = 13335965) B13335965
theorem B5927095 : Blo 2191435 5927095 := bstep (se 1 (by rfl) ⟨4445321, by rfl⟩ : syracuseStep 5927095 = 8890643) B8890643
theorem B7902793 : Blo 2191435 7902793 := bstep (se 2 (by rfl) ⟨2963547, by rfl⟩ : syracuseStep 7902793 = 5927095) B5927095
theorem B10537057 : Blo 2191435 10537057 := bstep (se 2 (by rfl) ⟨3951396, by rfl⟩ : syracuseStep 10537057 = 7902793) B7902793
theorem B14049409 : Blo 2191435 14049409 := bstep (se 2 (by rfl) ⟨5268528, by rfl⟩ : syracuseStep 14049409 = 10537057) B10537057
theorem B18732545 : Blo 2191435 18732545 := bstep (se 2 (by rfl) ⟨7024704, by rfl⟩ : syracuseStep 18732545 = 14049409) B14049409
theorem B12488363 : Blo 2191435 12488363 := bstep (se 1 (by rfl) ⟨9366272, by rfl⟩ : syracuseStep 12488363 = 18732545) B18732545
theorem B8325575 : Blo 2191435 8325575 := bstep (se 1 (by rfl) ⟨6244181, by rfl⟩ : syracuseStep 8325575 = 12488363) B12488363
theorem B5550383 : Blo 2191435 5550383 := bstep (se 1 (by rfl) ⟨4162787, by rfl⟩ : syracuseStep 5550383 = 8325575) B8325575
theorem B3700255 : Blo 2191435 3700255 := bstep (se 1 (by rfl) ⟨2775191, by rfl⟩ : syracuseStep 3700255 = 5550383) B5550383
theorem B4933673 : Blo 2191435 4933673 := bstep (se 2 (by rfl) ⟨1850127, by rfl⟩ : syracuseStep 4933673 = 3700255) B3700255
theorem B3289115 : Blo 2191435 3289115 := bstep (se 1 (by rfl) ⟨2466836, by rfl⟩ : syracuseStep 3289115 = 4933673) B4933673
theorem B2192743 : Blo 2191435 2192743 := bstep (se 1 (by rfl) ⟨1644557, by rfl⟩ : syracuseStep 2192743 = 3289115) B3289115
theorem B2466841 : Blo 2191435 2466841 := bbase (se 2 (by rfl) ⟨925065, by rfl⟩ : syracuseStep 2466841 = 1850131) (by norm_num)
theorem B3289121 : Blo 2191435 3289121 := bstep (se 2 (by rfl) ⟨1233420, by rfl⟩ : syracuseStep 3289121 = 2466841) B2466841
theorem B2192747 : Blo 2191435 2192747 := bstep (se 1 (by rfl) ⟨1644560, by rfl⟩ : syracuseStep 2192747 = 3289121) B3289121
theorem B8325605 : Blo 2191435 8325605 := bbase (se 4 (by rfl) ⟨780525, by rfl⟩ : syracuseStep 8325605 = 1561051) (by norm_num)
theorem B5550403 : Blo 2191435 5550403 := bstep (se 1 (by rfl) ⟨4162802, by rfl⟩ : syracuseStep 5550403 = 8325605) B8325605
theorem B7400537 : Blo 2191435 7400537 := bstep (se 2 (by rfl) ⟨2775201, by rfl⟩ : syracuseStep 7400537 = 5550403) B5550403
theorem B4933691 : Blo 2191435 4933691 := bstep (se 1 (by rfl) ⟨3700268, by rfl⟩ : syracuseStep 4933691 = 7400537) B7400537
theorem B3289127 : Blo 2191435 3289127 := bstep (se 1 (by rfl) ⟨2466845, by rfl⟩ : syracuseStep 3289127 = 4933691) B4933691
theorem B2192751 : Blo 2191435 2192751 := bstep (se 1 (by rfl) ⟨1644563, by rfl⟩ : syracuseStep 2192751 = 3289127) B3289127
theorem B3289133 : Blo 2191435 3289133 := bbase (se 3 (by rfl) ⟨616712, by rfl⟩ : syracuseStep 3289133 = 1233425) (by norm_num)
theorem B2192755 : Blo 2191435 2192755 := bstep (se 1 (by rfl) ⟨1644566, by rfl⟩ : syracuseStep 2192755 = 3289133) B3289133
theorem B4933709 : Blo 2191435 4933709 := bbase (se 3 (by rfl) ⟨925070, by rfl⟩ : syracuseStep 4933709 = 1850141) (by norm_num)
theorem B3289139 : Blo 2191435 3289139 := bstep (se 1 (by rfl) ⟨2466854, by rfl⟩ : syracuseStep 3289139 = 4933709) B4933709
theorem B2192759 : Blo 2191435 2192759 := bstep (se 1 (by rfl) ⟨1644569, by rfl⟩ : syracuseStep 2192759 = 3289139) B3289139
theorem B2775217 : Blo 2191435 2775217 := bbase (se 2 (by rfl) ⟨1040706, by rfl⟩ : syracuseStep 2775217 = 2081413) (by norm_num)
theorem B3700289 : Blo 2191435 3700289 := bstep (se 2 (by rfl) ⟨1387608, by rfl⟩ : syracuseStep 3700289 = 2775217) B2775217
theorem B2466859 : Blo 2191435 2466859 := bstep (se 1 (by rfl) ⟨1850144, by rfl⟩ : syracuseStep 2466859 = 3700289) B3700289
theorem B3289145 : Blo 2191435 3289145 := bstep (se 2 (by rfl) ⟨1233429, by rfl⟩ : syracuseStep 3289145 = 2466859) B2466859
theorem B2192763 : Blo 2191435 2192763 := bstep (se 1 (by rfl) ⟨1644572, by rfl⟩ : syracuseStep 2192763 = 3289145) B3289145
theorem B2634293 : Blo 2191435 2634293 := bbase (se 5 (by rfl) ⟨123482, by rfl⟩ : syracuseStep 2634293 = 246965) (by norm_num)
theorem B7024781 : Blo 2191435 7024781 := bstep (se 3 (by rfl) ⟨1317146, by rfl⟩ : syracuseStep 7024781 = 2634293) B2634293
theorem B4683187 : Blo 2191435 4683187 := bstep (se 1 (by rfl) ⟨3512390, by rfl⟩ : syracuseStep 4683187 = 7024781) B7024781
theorem B24976997 : Blo 2191435 24976997 := bstep (se 4 (by rfl) ⟨2341593, by rfl⟩ : syracuseStep 24976997 = 4683187) B4683187
theorem B16651331 : Blo 2191435 16651331 := bstep (se 1 (by rfl) ⟨12488498, by rfl⟩ : syracuseStep 16651331 = 24976997) B24976997
theorem B11100887 : Blo 2191435 11100887 := bstep (se 1 (by rfl) ⟨8325665, by rfl⟩ : syracuseStep 11100887 = 16651331) B16651331
theorem B7400591 : Blo 2191435 7400591 := bstep (se 1 (by rfl) ⟨5550443, by rfl⟩ : syracuseStep 7400591 = 11100887) B11100887
theorem B4933727 : Blo 2191435 4933727 := bstep (se 1 (by rfl) ⟨3700295, by rfl⟩ : syracuseStep 4933727 = 7400591) B7400591
theorem B3289151 : Blo 2191435 3289151 := bstep (se 1 (by rfl) ⟨2466863, by rfl⟩ : syracuseStep 3289151 = 4933727) B4933727
theorem B2192767 : Blo 2191435 2192767 := bstep (se 1 (by rfl) ⟨1644575, by rfl⟩ : syracuseStep 2192767 = 3289151) B3289151
theorem B3289157 : Blo 2191435 3289157 := bbase (se 4 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 3289157 = 616717) (by norm_num)
theorem B2192771 : Blo 2191435 2192771 := bstep (se 1 (by rfl) ⟨1644578, by rfl⟩ : syracuseStep 2192771 = 3289157) B3289157
theorem B3700309 : Blo 2191435 3700309 := bbase (se 8 (by rfl) ⟨21681, by rfl⟩ : syracuseStep 3700309 = 43363) (by norm_num)
theorem B4933745 : Blo 2191435 4933745 := bstep (se 2 (by rfl) ⟨1850154, by rfl⟩ : syracuseStep 4933745 = 3700309) B3700309
theorem B3289163 : Blo 2191435 3289163 := bstep (se 1 (by rfl) ⟨2466872, by rfl⟩ : syracuseStep 3289163 = 4933745) B4933745
theorem B2192775 : Blo 2191435 2192775 := bstep (se 1 (by rfl) ⟨1644581, by rfl⟩ : syracuseStep 2192775 = 3289163) B3289163
theorem B2466877 : Blo 2191435 2466877 := bbase (se 3 (by rfl) ⟨462539, by rfl⟩ : syracuseStep 2466877 = 925079) (by norm_num)
theorem B3289169 : Blo 2191435 3289169 := bstep (se 2 (by rfl) ⟨1233438, by rfl⟩ : syracuseStep 3289169 = 2466877) B2466877
theorem B2192779 : Blo 2191435 2192779 := bstep (se 1 (by rfl) ⟨1644584, by rfl⟩ : syracuseStep 2192779 = 3289169) B3289169
theorem B7400645 : Blo 2191435 7400645 := bbase (se 4 (by rfl) ⟨693810, by rfl⟩ : syracuseStep 7400645 = 1387621) (by norm_num)
theorem B4933763 : Blo 2191435 4933763 := bstep (se 1 (by rfl) ⟨3700322, by rfl⟩ : syracuseStep 4933763 = 7400645) B7400645
theorem B3289175 : Blo 2191435 3289175 := bstep (se 1 (by rfl) ⟨2466881, by rfl⟩ : syracuseStep 3289175 = 4933763) B4933763
theorem B2192783 : Blo 2191435 2192783 := bstep (se 1 (by rfl) ⟨1644587, by rfl⟩ : syracuseStep 2192783 = 3289175) B3289175
theorem B3289181 : Blo 2191435 3289181 := bbase (se 3 (by rfl) ⟨616721, by rfl⟩ : syracuseStep 3289181 = 1233443) (by norm_num)
theorem B2192787 : Blo 2191435 2192787 := bstep (se 1 (by rfl) ⟨1644590, by rfl⟩ : syracuseStep 2192787 = 3289181) B3289181
theorem B4933781 : Blo 2191435 4933781 := bbase (se 6 (by rfl) ⟨115635, by rfl⟩ : syracuseStep 4933781 = 231271) (by norm_num)
theorem B3289187 : Blo 2191435 3289187 := bstep (se 1 (by rfl) ⟨2466890, by rfl⟩ : syracuseStep 3289187 = 4933781) B4933781
theorem B2192791 : Blo 2191435 2192791 := bstep (se 1 (by rfl) ⟨1644593, by rfl⟩ : syracuseStep 2192791 = 3289187) B3289187
theorem B3122165 : Blo 2191435 3122165 := bbase (se 5 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 3122165 = 292703) (by norm_num)
theorem B8325773 : Blo 2191435 8325773 := bstep (se 3 (by rfl) ⟨1561082, by rfl⟩ : syracuseStep 8325773 = 3122165) B3122165
theorem B5550515 : Blo 2191435 5550515 := bstep (se 1 (by rfl) ⟨4162886, by rfl⟩ : syracuseStep 5550515 = 8325773) B8325773
theorem B3700343 : Blo 2191435 3700343 := bstep (se 1 (by rfl) ⟨2775257, by rfl⟩ : syracuseStep 3700343 = 5550515) B5550515
theorem B2466895 : Blo 2191435 2466895 := bstep (se 1 (by rfl) ⟨1850171, by rfl⟩ : syracuseStep 2466895 = 3700343) B3700343
theorem B3289193 : Blo 2191435 3289193 := bstep (se 2 (by rfl) ⟨1233447, by rfl⟩ : syracuseStep 3289193 = 2466895) B2466895
theorem B2192795 : Blo 2191435 2192795 := bstep (se 1 (by rfl) ⟨1644596, by rfl⟩ : syracuseStep 2192795 = 3289193) B3289193
theorem B4567565 : Blo 2191435 4567565 := bbase (se 3 (by rfl) ⟨856418, by rfl⟩ : syracuseStep 4567565 = 1712837) (by norm_num)
theorem B3045043 : Blo 2191435 3045043 := bstep (se 1 (by rfl) ⟨2283782, by rfl⟩ : syracuseStep 3045043 = 4567565) B4567565
theorem B4060057 : Blo 2191435 4060057 := bstep (se 2 (by rfl) ⟨1522521, by rfl⟩ : syracuseStep 4060057 = 3045043) B3045043
theorem B5413409 : Blo 2191435 5413409 := bstep (se 2 (by rfl) ⟨2030028, by rfl⟩ : syracuseStep 5413409 = 4060057) B4060057
theorem B3608939 : Blo 2191435 3608939 := bstep (se 1 (by rfl) ⟨2706704, by rfl⟩ : syracuseStep 3608939 = 5413409) B5413409
theorem B9623837 : Blo 2191435 9623837 := bstep (se 3 (by rfl) ⟨1804469, by rfl⟩ : syracuseStep 9623837 = 3608939) B3608939
theorem B6415891 : Blo 2191435 6415891 := bstep (se 1 (by rfl) ⟨4811918, by rfl⟩ : syracuseStep 6415891 = 9623837) B9623837
theorem B34218085 : Blo 2191435 34218085 := bstep (se 4 (by rfl) ⟨3207945, by rfl⟩ : syracuseStep 34218085 = 6415891) B6415891
theorem B45624113 : Blo 2191435 45624113 := bstep (se 2 (by rfl) ⟨17109042, by rfl⟩ : syracuseStep 45624113 = 34218085) B34218085
theorem B30416075 : Blo 2191435 30416075 := bstep (se 1 (by rfl) ⟨22812056, by rfl⟩ : syracuseStep 30416075 = 45624113) B45624113
theorem B20277383 : Blo 2191435 20277383 := bstep (se 1 (by rfl) ⟨15208037, by rfl⟩ : syracuseStep 20277383 = 30416075) B30416075
theorem B54073021 : Blo 2191435 54073021 := bstep (se 3 (by rfl) ⟨10138691, by rfl⟩ : syracuseStep 54073021 = 20277383) B20277383
theorem B72097361 : Blo 2191435 72097361 := bstep (se 2 (by rfl) ⟨27036510, by rfl⟩ : syracuseStep 72097361 = 54073021) B54073021
theorem B48064907 : Blo 2191435 48064907 := bstep (se 1 (by rfl) ⟨36048680, by rfl⟩ : syracuseStep 48064907 = 72097361) B72097361
theorem B32043271 : Blo 2191435 32043271 := bstep (se 1 (by rfl) ⟨24032453, by rfl⟩ : syracuseStep 32043271 = 48064907) B48064907
theorem B42724361 : Blo 2191435 42724361 := bstep (se 2 (by rfl) ⟨16021635, by rfl⟩ : syracuseStep 42724361 = 32043271) B32043271
theorem B113931629 : Blo 2191435 113931629 := bstep (se 3 (by rfl) ⟨21362180, by rfl⟩ : syracuseStep 113931629 = 42724361) B42724361
theorem B75954419 : Blo 2191435 75954419 := bstep (se 1 (by rfl) ⟨56965814, by rfl⟩ : syracuseStep 75954419 = 113931629) B113931629
theorem B50636279 : Blo 2191435 50636279 := bstep (se 1 (by rfl) ⟨37977209, by rfl⟩ : syracuseStep 50636279 = 75954419) B75954419
theorem B33757519 : Blo 2191435 33757519 := bstep (se 1 (by rfl) ⟨25318139, by rfl⟩ : syracuseStep 33757519 = 50636279) B50636279
theorem B45010025 : Blo 2191435 45010025 := bstep (se 2 (by rfl) ⟨16878759, by rfl⟩ : syracuseStep 45010025 = 33757519) B33757519
theorem B30006683 : Blo 2191435 30006683 := bstep (se 1 (by rfl) ⟨22505012, by rfl⟩ : syracuseStep 30006683 = 45010025) B45010025
theorem B20004455 : Blo 2191435 20004455 := bstep (se 1 (by rfl) ⟨15003341, by rfl⟩ : syracuseStep 20004455 = 30006683) B30006683
theorem B53345213 : Blo 2191435 53345213 := bstep (se 3 (by rfl) ⟨10002227, by rfl⟩ : syracuseStep 53345213 = 20004455) B20004455
theorem B35563475 : Blo 2191435 35563475 := bstep (se 1 (by rfl) ⟨26672606, by rfl⟩ : syracuseStep 35563475 = 53345213) B53345213
theorem B23708983 : Blo 2191435 23708983 := bstep (se 1 (by rfl) ⟨17781737, by rfl⟩ : syracuseStep 23708983 = 35563475) B35563475
theorem B31611977 : Blo 2191435 31611977 := bstep (se 2 (by rfl) ⟨11854491, by rfl⟩ : syracuseStep 31611977 = 23708983) B23708983
theorem B21074651 : Blo 2191435 21074651 := bstep (se 1 (by rfl) ⟨15805988, by rfl⟩ : syracuseStep 21074651 = 31611977) B31611977
theorem B14049767 : Blo 2191435 14049767 := bstep (se 1 (by rfl) ⟨10537325, by rfl⟩ : syracuseStep 14049767 = 21074651) B21074651
theorem B9366511 : Blo 2191435 9366511 := bstep (se 1 (by rfl) ⟨7024883, by rfl⟩ : syracuseStep 9366511 = 14049767) B14049767
theorem B12488681 : Blo 2191435 12488681 := bstep (se 2 (by rfl) ⟨4683255, by rfl⟩ : syracuseStep 12488681 = 9366511) B9366511
theorem B8325787 : Blo 2191435 8325787 := bstep (se 1 (by rfl) ⟨6244340, by rfl⟩ : syracuseStep 8325787 = 12488681) B12488681
theorem B11101049 : Blo 2191435 11101049 := bstep (se 2 (by rfl) ⟨4162893, by rfl⟩ : syracuseStep 11101049 = 8325787) B8325787
theorem B7400699 : Blo 2191435 7400699 := bstep (se 1 (by rfl) ⟨5550524, by rfl⟩ : syracuseStep 7400699 = 11101049) B11101049
theorem B4933799 : Blo 2191435 4933799 := bstep (se 1 (by rfl) ⟨3700349, by rfl⟩ : syracuseStep 4933799 = 7400699) B7400699
theorem B3289199 : Blo 2191435 3289199 := bstep (se 1 (by rfl) ⟨2466899, by rfl⟩ : syracuseStep 3289199 = 4933799) B4933799
theorem B2192799 : Blo 2191435 2192799 := bstep (se 1 (by rfl) ⟨1644599, by rfl⟩ : syracuseStep 2192799 = 3289199) B3289199
theorem B3289205 : Blo 2191435 3289205 := bbase (se 5 (by rfl) ⟨154181, by rfl⟩ : syracuseStep 3289205 = 308363) (by norm_num)
theorem B2192803 : Blo 2191435 2192803 := bstep (se 1 (by rfl) ⟨1644602, by rfl⟩ : syracuseStep 2192803 = 3289205) B3289205
theorem B4162909 : Blo 2191435 4162909 := bbase (se 3 (by rfl) ⟨780545, by rfl⟩ : syracuseStep 4162909 = 1561091) (by norm_num)
theorem B5550545 : Blo 2191435 5550545 := bstep (se 2 (by rfl) ⟨2081454, by rfl⟩ : syracuseStep 5550545 = 4162909) B4162909
theorem B3700363 : Blo 2191435 3700363 := bstep (se 1 (by rfl) ⟨2775272, by rfl⟩ : syracuseStep 3700363 = 5550545) B5550545
theorem B4933817 : Blo 2191435 4933817 := bstep (se 2 (by rfl) ⟨1850181, by rfl⟩ : syracuseStep 4933817 = 3700363) B3700363
theorem B3289211 : Blo 2191435 3289211 := bstep (se 1 (by rfl) ⟨2466908, by rfl⟩ : syracuseStep 3289211 = 4933817) B4933817
theorem B2192807 : Blo 2191435 2192807 := bstep (se 1 (by rfl) ⟨1644605, by rfl⟩ : syracuseStep 2192807 = 3289211) B3289211
theorem B2466913 : Blo 2191435 2466913 := bbase (se 2 (by rfl) ⟨925092, by rfl⟩ : syracuseStep 2466913 = 1850185) (by norm_num)
theorem B3289217 : Blo 2191435 3289217 := bstep (se 2 (by rfl) ⟨1233456, by rfl⟩ : syracuseStep 3289217 = 2466913) B2466913
theorem B2192811 : Blo 2191435 2192811 := bstep (se 1 (by rfl) ⟨1644608, by rfl⟩ : syracuseStep 2192811 = 3289217) B3289217
theorem B5550565 : Blo 2191435 5550565 := bbase (se 4 (by rfl) ⟨520365, by rfl⟩ : syracuseStep 5550565 = 1040731) (by norm_num)
theorem B7400753 : Blo 2191435 7400753 := bstep (se 2 (by rfl) ⟨2775282, by rfl⟩ : syracuseStep 7400753 = 5550565) B5550565
theorem B4933835 : Blo 2191435 4933835 := bstep (se 1 (by rfl) ⟨3700376, by rfl⟩ : syracuseStep 4933835 = 7400753) B7400753
theorem B3289223 : Blo 2191435 3289223 := bstep (se 1 (by rfl) ⟨2466917, by rfl⟩ : syracuseStep 3289223 = 4933835) B4933835
theorem B2192815 : Blo 2191435 2192815 := bstep (se 1 (by rfl) ⟨1644611, by rfl⟩ : syracuseStep 2192815 = 3289223) B3289223
theorem B3289229 : Blo 2191435 3289229 := bbase (se 3 (by rfl) ⟨616730, by rfl⟩ : syracuseStep 3289229 = 1233461) (by norm_num)
theorem B2192819 : Blo 2191435 2192819 := bstep (se 1 (by rfl) ⟨1644614, by rfl⟩ : syracuseStep 2192819 = 3289229) B3289229
theorem B4933853 : Blo 2191435 4933853 := bbase (se 3 (by rfl) ⟨925097, by rfl⟩ : syracuseStep 4933853 = 1850195) (by norm_num)
theorem B3289235 : Blo 2191435 3289235 := bstep (se 1 (by rfl) ⟨2466926, by rfl⟩ : syracuseStep 3289235 = 4933853) B4933853
theorem B2192823 : Blo 2191435 2192823 := bstep (se 1 (by rfl) ⟨1644617, by rfl⟩ : syracuseStep 2192823 = 3289235) B3289235
theorem B3700397 : Blo 2191435 3700397 := bbase (se 3 (by rfl) ⟨693824, by rfl⟩ : syracuseStep 3700397 = 1387649) (by norm_num)
theorem B2466931 : Blo 2191435 2466931 := bstep (se 1 (by rfl) ⟨1850198, by rfl⟩ : syracuseStep 2466931 = 3700397) B3700397
theorem B3289241 : Blo 2191435 3289241 := bstep (se 2 (by rfl) ⟨1233465, by rfl⟩ : syracuseStep 3289241 = 2466931) B2466931
theorem B2192827 : Blo 2191435 2192827 := bstep (se 1 (by rfl) ⟨1644620, by rfl⟩ : syracuseStep 2192827 = 3289241) B3289241
theorem B2851549 : Blo 2191435 2851549 := bbase (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) (by norm_num)
theorem B60833045 : Blo 2191435 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B40555363 : Blo 2191435 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B54073817 : Blo 2191435 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B36049211 : Blo 2191435 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B24032807 : Blo 2191435 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B16021871 : Blo 2191435 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B10681247 : Blo 2191435 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B7120831 : Blo 2191435 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B9494441 : Blo 2191435 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B6329627 : Blo 2191435 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B4219751 : Blo 2191435 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B180042709 : Blo 2191435 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B240056945 : Blo 2191435 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B160037963 : Blo 2191435 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B106691975 : Blo 2191435 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B71127983 : Blo 2191435 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B47418655 : Blo 2191435 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B63224873 : Blo 2191435 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B42149915 : Blo 2191435 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B28099943 : Blo 2191435 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B18733295 : Blo 2191435 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B12488863 : Blo 2191435 12488863 := bstep (se 1 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 12488863 = 18733295) B18733295
theorem B16651817 : Blo 2191435 16651817 := bstep (se 2 (by rfl) ⟨6244431, by rfl⟩ : syracuseStep 16651817 = 12488863) B12488863
theorem B11101211 : Blo 2191435 11101211 := bstep (se 1 (by rfl) ⟨8325908, by rfl⟩ : syracuseStep 11101211 = 16651817) B16651817
theorem B7400807 : Blo 2191435 7400807 := bstep (se 1 (by rfl) ⟨5550605, by rfl⟩ : syracuseStep 7400807 = 11101211) B11101211
theorem B4933871 : Blo 2191435 4933871 := bstep (se 1 (by rfl) ⟨3700403, by rfl⟩ : syracuseStep 4933871 = 7400807) B7400807
theorem B3289247 : Blo 2191435 3289247 := bstep (se 1 (by rfl) ⟨2466935, by rfl⟩ : syracuseStep 3289247 = 4933871) B4933871
theorem B2192831 : Blo 2191435 2192831 := bstep (se 1 (by rfl) ⟨1644623, by rfl⟩ : syracuseStep 2192831 = 3289247) B3289247
theorem B3289253 : Blo 2191435 3289253 := bbase (se 4 (by rfl) ⟨308367, by rfl⟩ : syracuseStep 3289253 = 616735) (by norm_num)
theorem B2192835 : Blo 2191435 2192835 := bstep (se 1 (by rfl) ⟨1644626, by rfl⟩ : syracuseStep 2192835 = 3289253) B3289253
theorem B2775313 : Blo 2191435 2775313 := bbase (se 2 (by rfl) ⟨1040742, by rfl⟩ : syracuseStep 2775313 = 2081485) (by norm_num)
theorem B3700417 : Blo 2191435 3700417 := bstep (se 2 (by rfl) ⟨1387656, by rfl⟩ : syracuseStep 3700417 = 2775313) B2775313
theorem B4933889 : Blo 2191435 4933889 := bstep (se 2 (by rfl) ⟨1850208, by rfl⟩ : syracuseStep 4933889 = 3700417) B3700417
theorem B3289259 : Blo 2191435 3289259 := bstep (se 1 (by rfl) ⟨2466944, by rfl⟩ : syracuseStep 3289259 = 4933889) B4933889
theorem B2192839 : Blo 2191435 2192839 := bstep (se 1 (by rfl) ⟨1644629, by rfl⟩ : syracuseStep 2192839 = 3289259) B3289259
theorem B2466949 : Blo 2191435 2466949 := bbase (se 4 (by rfl) ⟨231276, by rfl⟩ : syracuseStep 2466949 = 462553) (by norm_num)
theorem B3289265 : Blo 2191435 3289265 := bstep (se 2 (by rfl) ⟨1233474, by rfl⟩ : syracuseStep 3289265 = 2466949) B2466949
theorem B2192843 : Blo 2191435 2192843 := bstep (se 1 (by rfl) ⟨1644632, by rfl⟩ : syracuseStep 2192843 = 3289265) B3289265
theorem B4445533 : Blo 2191435 4445533 := bbase (se 3 (by rfl) ⟨833537, by rfl⟩ : syracuseStep 4445533 = 1667075) (by norm_num)
theorem B23709509 : Blo 2191435 23709509 := bstep (se 4 (by rfl) ⟨2222766, by rfl⟩ : syracuseStep 23709509 = 4445533) B4445533
theorem B15806339 : Blo 2191435 15806339 := bstep (se 1 (by rfl) ⟨11854754, by rfl⟩ : syracuseStep 15806339 = 23709509) B23709509
theorem B10537559 : Blo 2191435 10537559 := bstep (se 1 (by rfl) ⟨7903169, by rfl⟩ : syracuseStep 10537559 = 15806339) B15806339
theorem B7025039 : Blo 2191435 7025039 := bstep (se 1 (by rfl) ⟨5268779, by rfl⟩ : syracuseStep 7025039 = 10537559) B10537559
theorem B4683359 : Blo 2191435 4683359 := bstep (se 1 (by rfl) ⟨3512519, by rfl⟩ : syracuseStep 4683359 = 7025039) B7025039
theorem B3122239 : Blo 2191435 3122239 := bstep (se 1 (by rfl) ⟨2341679, by rfl⟩ : syracuseStep 3122239 = 4683359) B4683359
theorem B4162985 : Blo 2191435 4162985 := bstep (se 2 (by rfl) ⟨1561119, by rfl⟩ : syracuseStep 4162985 = 3122239) B3122239
theorem B2775323 : Blo 2191435 2775323 := bstep (se 1 (by rfl) ⟨2081492, by rfl⟩ : syracuseStep 2775323 = 4162985) B4162985
theorem B7400861 : Blo 2191435 7400861 := bstep (se 3 (by rfl) ⟨1387661, by rfl⟩ : syracuseStep 7400861 = 2775323) B2775323
theorem B4933907 : Blo 2191435 4933907 := bstep (se 1 (by rfl) ⟨3700430, by rfl⟩ : syracuseStep 4933907 = 7400861) B7400861
theorem B3289271 : Blo 2191435 3289271 := bstep (se 1 (by rfl) ⟨2466953, by rfl⟩ : syracuseStep 3289271 = 4933907) B4933907
theorem B2192847 : Blo 2191435 2192847 := bstep (se 1 (by rfl) ⟨1644635, by rfl⟩ : syracuseStep 2192847 = 3289271) B3289271
theorem B3289277 : Blo 2191435 3289277 := bbase (se 3 (by rfl) ⟨616739, by rfl⟩ : syracuseStep 3289277 = 1233479) (by norm_num)
theorem B2192851 : Blo 2191435 2192851 := bstep (se 1 (by rfl) ⟨1644638, by rfl⟩ : syracuseStep 2192851 = 3289277) B3289277
theorem B4933925 : Blo 2191435 4933925 := bbase (se 4 (by rfl) ⟨462555, by rfl⟩ : syracuseStep 4933925 = 925111) (by norm_num)
theorem B3289283 : Blo 2191435 3289283 := bstep (se 1 (by rfl) ⟨2466962, by rfl⟩ : syracuseStep 3289283 = 4933925) B4933925
theorem B2192855 : Blo 2191435 2192855 := bstep (se 1 (by rfl) ⟨1644641, by rfl⟩ : syracuseStep 2192855 = 3289283) B3289283
theorem B5550677 : Blo 2191435 5550677 := bbase (se 8 (by rfl) ⟨32523, by rfl⟩ : syracuseStep 5550677 = 65047) (by norm_num)
theorem B3700451 : Blo 2191435 3700451 := bstep (se 1 (by rfl) ⟨2775338, by rfl⟩ : syracuseStep 3700451 = 5550677) B5550677
theorem B2466967 : Blo 2191435 2466967 := bstep (se 1 (by rfl) ⟨1850225, by rfl⟩ : syracuseStep 2466967 = 3700451) B3700451
theorem B3289289 : Blo 2191435 3289289 := bstep (se 2 (by rfl) ⟨1233483, by rfl⟩ : syracuseStep 3289289 = 2466967) B2466967
theorem B2192859 : Blo 2191435 2192859 := bstep (se 1 (by rfl) ⟨1644644, by rfl⟩ : syracuseStep 2192859 = 3289289) B3289289
theorem B3951613 : Blo 2191435 3951613 := bbase (se 3 (by rfl) ⟨740927, by rfl⟩ : syracuseStep 3951613 = 1481855) (by norm_num)
theorem B5268817 : Blo 2191435 5268817 := bstep (se 2 (by rfl) ⟨1975806, by rfl⟩ : syracuseStep 5268817 = 3951613) B3951613
theorem B7025089 : Blo 2191435 7025089 := bstep (se 2 (by rfl) ⟨2634408, by rfl⟩ : syracuseStep 7025089 = 5268817) B5268817
theorem B9366785 : Blo 2191435 9366785 := bstep (se 2 (by rfl) ⟨3512544, by rfl⟩ : syracuseStep 9366785 = 7025089) B7025089
theorem B6244523 : Blo 2191435 6244523 := bstep (se 1 (by rfl) ⟨4683392, by rfl⟩ : syracuseStep 6244523 = 9366785) B9366785
theorem B4163015 : Blo 2191435 4163015 := bstep (se 1 (by rfl) ⟨3122261, by rfl⟩ : syracuseStep 4163015 = 6244523) B6244523
theorem B11101373 : Blo 2191435 11101373 := bstep (se 3 (by rfl) ⟨2081507, by rfl⟩ : syracuseStep 11101373 = 4163015) B4163015
theorem B7400915 : Blo 2191435 7400915 := bstep (se 1 (by rfl) ⟨5550686, by rfl⟩ : syracuseStep 7400915 = 11101373) B11101373
theorem B4933943 : Blo 2191435 4933943 := bstep (se 1 (by rfl) ⟨3700457, by rfl⟩ : syracuseStep 4933943 = 7400915) B7400915
theorem B3289295 : Blo 2191435 3289295 := bstep (se 1 (by rfl) ⟨2466971, by rfl⟩ : syracuseStep 3289295 = 4933943) B4933943
theorem B2192863 : Blo 2191435 2192863 := bstep (se 1 (by rfl) ⟨1644647, by rfl⟩ : syracuseStep 2192863 = 3289295) B3289295
theorem B3289301 : Blo 2191435 3289301 := bbase (se 7 (by rfl) ⟨38546, by rfl⟩ : syracuseStep 3289301 = 77093) (by norm_num)
theorem B2192867 : Blo 2191435 2192867 := bstep (se 1 (by rfl) ⟨1644650, by rfl⟩ : syracuseStep 2192867 = 3289301) B3289301
theorem B2341705 : Blo 2191435 2341705 := bbase (se 2 (by rfl) ⟨878139, by rfl⟩ : syracuseStep 2341705 = 1756279) (by norm_num)
theorem B3122273 : Blo 2191435 3122273 := bstep (se 2 (by rfl) ⟨1170852, by rfl⟩ : syracuseStep 3122273 = 2341705) B2341705
theorem B8326061 : Blo 2191435 8326061 := bstep (se 3 (by rfl) ⟨1561136, by rfl⟩ : syracuseStep 8326061 = 3122273) B3122273
theorem B5550707 : Blo 2191435 5550707 := bstep (se 1 (by rfl) ⟨4163030, by rfl⟩ : syracuseStep 5550707 = 8326061) B8326061
theorem B3700471 : Blo 2191435 3700471 := bstep (se 1 (by rfl) ⟨2775353, by rfl⟩ : syracuseStep 3700471 = 5550707) B5550707
theorem B4933961 : Blo 2191435 4933961 := bstep (se 2 (by rfl) ⟨1850235, by rfl⟩ : syracuseStep 4933961 = 3700471) B3700471
theorem B3289307 : Blo 2191435 3289307 := bstep (se 1 (by rfl) ⟨2466980, by rfl⟩ : syracuseStep 3289307 = 4933961) B4933961
theorem B2192871 : Blo 2191435 2192871 := bstep (se 1 (by rfl) ⟨1644653, by rfl⟩ : syracuseStep 2192871 = 3289307) B3289307
theorem B2466985 : Blo 2191435 2466985 := bbase (se 2 (by rfl) ⟨925119, by rfl⟩ : syracuseStep 2466985 = 1850239) (by norm_num)
theorem B3289313 : Blo 2191435 3289313 := bstep (se 2 (by rfl) ⟨1233492, by rfl⟩ : syracuseStep 3289313 = 2466985) B2466985
theorem B2192875 : Blo 2191435 2192875 := bstep (se 1 (by rfl) ⟨1644656, by rfl⟩ : syracuseStep 2192875 = 3289313) B3289313
theorem B9366853 : Blo 2191435 9366853 := bbase (se 4 (by rfl) ⟨878142, by rfl⟩ : syracuseStep 9366853 = 1756285) (by norm_num)
theorem B12489137 : Blo 2191435 12489137 := bstep (se 2 (by rfl) ⟨4683426, by rfl⟩ : syracuseStep 12489137 = 9366853) B9366853
theorem B8326091 : Blo 2191435 8326091 := bstep (se 1 (by rfl) ⟨6244568, by rfl⟩ : syracuseStep 8326091 = 12489137) B12489137
theorem B5550727 : Blo 2191435 5550727 := bstep (se 1 (by rfl) ⟨4163045, by rfl⟩ : syracuseStep 5550727 = 8326091) B8326091
theorem B7400969 : Blo 2191435 7400969 := bstep (se 2 (by rfl) ⟨2775363, by rfl⟩ : syracuseStep 7400969 = 5550727) B5550727
theorem B4933979 : Blo 2191435 4933979 := bstep (se 1 (by rfl) ⟨3700484, by rfl⟩ : syracuseStep 4933979 = 7400969) B7400969
theorem B3289319 : Blo 2191435 3289319 := bstep (se 1 (by rfl) ⟨2466989, by rfl⟩ : syracuseStep 3289319 = 4933979) B4933979
theorem B2192879 : Blo 2191435 2192879 := bstep (se 1 (by rfl) ⟨1644659, by rfl⟩ : syracuseStep 2192879 = 3289319) B3289319
theorem B3289325 : Blo 2191435 3289325 := bbase (se 3 (by rfl) ⟨616748, by rfl⟩ : syracuseStep 3289325 = 1233497) (by norm_num)
theorem B2192883 : Blo 2191435 2192883 := bstep (se 1 (by rfl) ⟨1644662, by rfl⟩ : syracuseStep 2192883 = 3289325) B3289325
theorem B4933997 : Blo 2191435 4933997 := bbase (se 3 (by rfl) ⟨925124, by rfl⟩ : syracuseStep 4933997 = 1850249) (by norm_num)
theorem B3289331 : Blo 2191435 3289331 := bstep (se 1 (by rfl) ⟨2466998, by rfl⟩ : syracuseStep 3289331 = 4933997) B4933997
theorem B2192887 : Blo 2191435 2192887 := bstep (se 1 (by rfl) ⟨1644665, by rfl⟩ : syracuseStep 2192887 = 3289331) B3289331
theorem B4163069 : Blo 2191435 4163069 := bbase (se 3 (by rfl) ⟨780575, by rfl⟩ : syracuseStep 4163069 = 1561151) (by norm_num)
theorem B2775379 : Blo 2191435 2775379 := bstep (se 1 (by rfl) ⟨2081534, by rfl⟩ : syracuseStep 2775379 = 4163069) B4163069
theorem B3700505 : Blo 2191435 3700505 := bstep (se 2 (by rfl) ⟨1387689, by rfl⟩ : syracuseStep 3700505 = 2775379) B2775379
theorem B2467003 : Blo 2191435 2467003 := bstep (se 1 (by rfl) ⟨1850252, by rfl⟩ : syracuseStep 2467003 = 3700505) B3700505
theorem B3289337 : Blo 2191435 3289337 := bstep (se 2 (by rfl) ⟨1233501, by rfl⟩ : syracuseStep 3289337 = 2467003) B2467003
theorem B2192891 : Blo 2191435 2192891 := bstep (se 1 (by rfl) ⟨1644668, by rfl⟩ : syracuseStep 2192891 = 3289337) B3289337
theorem B5268893 : Blo 2191435 5268893 := bbase (se 3 (by rfl) ⟨987917, by rfl⟩ : syracuseStep 5268893 = 1975835) (by norm_num)
theorem B56201525 : Blo 2191435 56201525 := bstep (se 5 (by rfl) ⟨2634446, by rfl⟩ : syracuseStep 56201525 = 5268893) B5268893
theorem B37467683 : Blo 2191435 37467683 := bstep (se 1 (by rfl) ⟨28100762, by rfl⟩ : syracuseStep 37467683 = 56201525) B56201525
theorem B24978455 : Blo 2191435 24978455 := bstep (se 1 (by rfl) ⟨18733841, by rfl⟩ : syracuseStep 24978455 = 37467683) B37467683
theorem B16652303 : Blo 2191435 16652303 := bstep (se 1 (by rfl) ⟨12489227, by rfl⟩ : syracuseStep 16652303 = 24978455) B24978455
theorem B11101535 : Blo 2191435 11101535 := bstep (se 1 (by rfl) ⟨8326151, by rfl⟩ : syracuseStep 11101535 = 16652303) B16652303
theorem B7401023 : Blo 2191435 7401023 := bstep (se 1 (by rfl) ⟨5550767, by rfl⟩ : syracuseStep 7401023 = 11101535) B11101535
theorem B4934015 : Blo 2191435 4934015 := bstep (se 1 (by rfl) ⟨3700511, by rfl⟩ : syracuseStep 4934015 = 7401023) B7401023
theorem B3289343 : Blo 2191435 3289343 := bstep (se 1 (by rfl) ⟨2467007, by rfl⟩ : syracuseStep 3289343 = 4934015) B4934015
theorem B2192895 : Blo 2191435 2192895 := bstep (se 1 (by rfl) ⟨1644671, by rfl⟩ : syracuseStep 2192895 = 3289343) B3289343
theorem B3289349 : Blo 2191435 3289349 := bbase (se 4 (by rfl) ⟨308376, by rfl⟩ : syracuseStep 3289349 = 616753) (by norm_num)
theorem B2192899 : Blo 2191435 2192899 := bstep (se 1 (by rfl) ⟨1644674, by rfl⟩ : syracuseStep 2192899 = 3289349) B3289349
theorem B3700525 : Blo 2191435 3700525 := bbase (se 3 (by rfl) ⟨693848, by rfl⟩ : syracuseStep 3700525 = 1387697) (by norm_num)
theorem B4934033 : Blo 2191435 4934033 := bstep (se 2 (by rfl) ⟨1850262, by rfl⟩ : syracuseStep 4934033 = 3700525) B3700525
theorem B3289355 : Blo 2191435 3289355 := bstep (se 1 (by rfl) ⟨2467016, by rfl⟩ : syracuseStep 3289355 = 4934033) B4934033
theorem B2192903 : Blo 2191435 2192903 := bstep (se 1 (by rfl) ⟨1644677, by rfl⟩ : syracuseStep 2192903 = 3289355) B3289355
theorem B2467021 : Blo 2191435 2467021 := bbase (se 3 (by rfl) ⟨462566, by rfl⟩ : syracuseStep 2467021 = 925133) (by norm_num)
theorem B3289361 : Blo 2191435 3289361 := bstep (se 2 (by rfl) ⟨1233510, by rfl⟩ : syracuseStep 3289361 = 2467021) B2467021
theorem B2192907 : Blo 2191435 2192907 := bstep (se 1 (by rfl) ⟨1644680, by rfl⟩ : syracuseStep 2192907 = 3289361) B3289361
theorem B7401077 : Blo 2191435 7401077 := bbase (se 5 (by rfl) ⟨346925, by rfl⟩ : syracuseStep 7401077 = 693851) (by norm_num)
theorem B4934051 : Blo 2191435 4934051 := bstep (se 1 (by rfl) ⟨3700538, by rfl⟩ : syracuseStep 4934051 = 7401077) B7401077
theorem B3289367 : Blo 2191435 3289367 := bstep (se 1 (by rfl) ⟨2467025, by rfl⟩ : syracuseStep 3289367 = 4934051) B4934051
theorem B2192911 : Blo 2191435 2192911 := bstep (se 1 (by rfl) ⟨1644683, by rfl⟩ : syracuseStep 2192911 = 3289367) B3289367
theorem B3289373 : Blo 2191435 3289373 := bbase (se 3 (by rfl) ⟨616757, by rfl⟩ : syracuseStep 3289373 = 1233515) (by norm_num)
theorem B2192915 : Blo 2191435 2192915 := bstep (se 1 (by rfl) ⟨1644686, by rfl⟩ : syracuseStep 2192915 = 3289373) B3289373
theorem B4934069 : Blo 2191435 4934069 := bbase (se 5 (by rfl) ⟨231284, by rfl⟩ : syracuseStep 4934069 = 462569) (by norm_num)
theorem B3289379 : Blo 2191435 3289379 := bstep (se 1 (by rfl) ⟨2467034, by rfl⟩ : syracuseStep 3289379 = 4934069) B4934069
theorem B2192919 : Blo 2191435 2192919 := bstep (se 1 (by rfl) ⟨1644689, by rfl⟩ : syracuseStep 2192919 = 3289379) B3289379
theorem B2634481 : Blo 2191435 2634481 := bbase (se 2 (by rfl) ⟨987930, by rfl⟩ : syracuseStep 2634481 = 1975861) (by norm_num)
theorem B3512641 : Blo 2191435 3512641 := bstep (se 2 (by rfl) ⟨1317240, by rfl⟩ : syracuseStep 3512641 = 2634481) B2634481
theorem B4683521 : Blo 2191435 4683521 := bstep (se 2 (by rfl) ⟨1756320, by rfl⟩ : syracuseStep 4683521 = 3512641) B3512641
theorem B12489389 : Blo 2191435 12489389 := bstep (se 3 (by rfl) ⟨2341760, by rfl⟩ : syracuseStep 12489389 = 4683521) B4683521
theorem B8326259 : Blo 2191435 8326259 := bstep (se 1 (by rfl) ⟨6244694, by rfl⟩ : syracuseStep 8326259 = 12489389) B12489389
theorem B5550839 : Blo 2191435 5550839 := bstep (se 1 (by rfl) ⟨4163129, by rfl⟩ : syracuseStep 5550839 = 8326259) B8326259
theorem B3700559 : Blo 2191435 3700559 := bstep (se 1 (by rfl) ⟨2775419, by rfl⟩ : syracuseStep 3700559 = 5550839) B5550839
theorem B2467039 : Blo 2191435 2467039 := bstep (se 1 (by rfl) ⟨1850279, by rfl⟩ : syracuseStep 2467039 = 3700559) B3700559
theorem B3289385 : Blo 2191435 3289385 := bstep (se 2 (by rfl) ⟨1233519, by rfl⟩ : syracuseStep 3289385 = 2467039) B2467039
theorem B2192923 : Blo 2191435 2192923 := bstep (se 1 (by rfl) ⟨1644692, by rfl⟩ : syracuseStep 2192923 = 3289385) B3289385
theorem B5069645 : Blo 2191435 5069645 := bbase (se 3 (by rfl) ⟨950558, by rfl⟩ : syracuseStep 5069645 = 1901117) (by norm_num)
theorem B3379763 : Blo 2191435 3379763 := bstep (se 1 (by rfl) ⟨2534822, by rfl⟩ : syracuseStep 3379763 = 5069645) B5069645
theorem B9012701 : Blo 2191435 9012701 := bstep (se 3 (by rfl) ⟨1689881, by rfl⟩ : syracuseStep 9012701 = 3379763) B3379763
theorem B6008467 : Blo 2191435 6008467 := bstep (se 1 (by rfl) ⟨4506350, by rfl⟩ : syracuseStep 6008467 = 9012701) B9012701
theorem B8011289 : Blo 2191435 8011289 := bstep (se 2 (by rfl) ⟨3004233, by rfl⟩ : syracuseStep 8011289 = 6008467) B6008467
theorem B5340859 : Blo 2191435 5340859 := bstep (se 1 (by rfl) ⟨4005644, by rfl⟩ : syracuseStep 5340859 = 8011289) B8011289
theorem B113938325 : Blo 2191435 113938325 := bstep (se 6 (by rfl) ⟨2670429, by rfl⟩ : syracuseStep 113938325 = 5340859) B5340859
theorem B75958883 : Blo 2191435 75958883 := bstep (se 1 (by rfl) ⟨56969162, by rfl⟩ : syracuseStep 75958883 = 113938325) B113938325
theorem B50639255 : Blo 2191435 50639255 := bstep (se 1 (by rfl) ⟨37979441, by rfl⟩ : syracuseStep 50639255 = 75958883) B75958883
theorem B33759503 : Blo 2191435 33759503 := bstep (se 1 (by rfl) ⟨25319627, by rfl⟩ : syracuseStep 33759503 = 50639255) B50639255
theorem B22506335 : Blo 2191435 22506335 := bstep (se 1 (by rfl) ⟨16879751, by rfl⟩ : syracuseStep 22506335 = 33759503) B33759503
theorem B15004223 : Blo 2191435 15004223 := bstep (se 1 (by rfl) ⟨11253167, by rfl⟩ : syracuseStep 15004223 = 22506335) B22506335
theorem B10002815 : Blo 2191435 10002815 := bstep (se 1 (by rfl) ⟨7502111, by rfl⟩ : syracuseStep 10002815 = 15004223) B15004223
theorem B6668543 : Blo 2191435 6668543 := bstep (se 1 (by rfl) ⟨5001407, by rfl⟩ : syracuseStep 6668543 = 10002815) B10002815
theorem B4445695 : Blo 2191435 4445695 := bstep (se 1 (by rfl) ⟨3334271, by rfl⟩ : syracuseStep 4445695 = 6668543) B6668543
theorem B5927593 : Blo 2191435 5927593 := bstep (se 2 (by rfl) ⟨2222847, by rfl⟩ : syracuseStep 5927593 = 4445695) B4445695
theorem B7903457 : Blo 2191435 7903457 := bstep (se 2 (by rfl) ⟨2963796, by rfl⟩ : syracuseStep 7903457 = 5927593) B5927593
theorem B5268971 : Blo 2191435 5268971 := bstep (se 1 (by rfl) ⟨3951728, by rfl⟩ : syracuseStep 5268971 = 7903457) B7903457
theorem B3512647 : Blo 2191435 3512647 := bstep (se 1 (by rfl) ⟨2634485, by rfl⟩ : syracuseStep 3512647 = 5268971) B5268971
theorem B4683529 : Blo 2191435 4683529 := bstep (se 2 (by rfl) ⟨1756323, by rfl⟩ : syracuseStep 4683529 = 3512647) B3512647
theorem B6244705 : Blo 2191435 6244705 := bstep (se 2 (by rfl) ⟨2341764, by rfl⟩ : syracuseStep 6244705 = 4683529) B4683529
theorem B8326273 : Blo 2191435 8326273 := bstep (se 2 (by rfl) ⟨3122352, by rfl⟩ : syracuseStep 8326273 = 6244705) B6244705
theorem B11101697 : Blo 2191435 11101697 := bstep (se 2 (by rfl) ⟨4163136, by rfl⟩ : syracuseStep 11101697 = 8326273) B8326273
theorem B7401131 : Blo 2191435 7401131 := bstep (se 1 (by rfl) ⟨5550848, by rfl⟩ : syracuseStep 7401131 = 11101697) B11101697
theorem B4934087 : Blo 2191435 4934087 := bstep (se 1 (by rfl) ⟨3700565, by rfl⟩ : syracuseStep 4934087 = 7401131) B7401131
theorem B3289391 : Blo 2191435 3289391 := bstep (se 1 (by rfl) ⟨2467043, by rfl⟩ : syracuseStep 3289391 = 4934087) B4934087
theorem B2192927 : Blo 2191435 2192927 := bstep (se 1 (by rfl) ⟨1644695, by rfl⟩ : syracuseStep 2192927 = 3289391) B3289391
theorem B3289397 : Blo 2191435 3289397 := bbase (se 5 (by rfl) ⟨154190, by rfl⟩ : syracuseStep 3289397 = 308381) (by norm_num)
theorem B2192931 : Blo 2191435 2192931 := bstep (se 1 (by rfl) ⟨1644698, by rfl⟩ : syracuseStep 2192931 = 3289397) B3289397
theorem B5550869 : Blo 2191435 5550869 := bbase (se 6 (by rfl) ⟨130098, by rfl⟩ : syracuseStep 5550869 = 260197) (by norm_num)
theorem B3700579 : Blo 2191435 3700579 := bstep (se 1 (by rfl) ⟨2775434, by rfl⟩ : syracuseStep 3700579 = 5550869) B5550869
theorem B4934105 : Blo 2191435 4934105 := bstep (se 2 (by rfl) ⟨1850289, by rfl⟩ : syracuseStep 4934105 = 3700579) B3700579
theorem B3289403 : Blo 2191435 3289403 := bstep (se 1 (by rfl) ⟨2467052, by rfl⟩ : syracuseStep 3289403 = 4934105) B4934105
theorem B2192935 : Blo 2191435 2192935 := bstep (se 1 (by rfl) ⟨1644701, by rfl⟩ : syracuseStep 2192935 = 3289403) B3289403
theorem B2467057 : Blo 2191435 2467057 := bbase (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) (by norm_num)
theorem B3289409 : Blo 2191435 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B2192939 : Blo 2191435 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B3951757 : Blo 2191435 3951757 := bbase (se 3 (by rfl) ⟨740954, by rfl⟩ : syracuseStep 3951757 = 1481909) (by norm_num)
theorem B21076037 : Blo 2191435 21076037 := bstep (se 4 (by rfl) ⟨1975878, by rfl⟩ : syracuseStep 21076037 = 3951757) B3951757
theorem B14050691 : Blo 2191435 14050691 := bstep (se 1 (by rfl) ⟨10538018, by rfl⟩ : syracuseStep 14050691 = 21076037) B21076037
theorem B9367127 : Blo 2191435 9367127 := bstep (se 1 (by rfl) ⟨7025345, by rfl⟩ : syracuseStep 9367127 = 14050691) B14050691
theorem B6244751 : Blo 2191435 6244751 := bstep (se 1 (by rfl) ⟨4683563, by rfl⟩ : syracuseStep 6244751 = 9367127) B9367127
theorem B4163167 : Blo 2191435 4163167 := bstep (se 1 (by rfl) ⟨3122375, by rfl⟩ : syracuseStep 4163167 = 6244751) B6244751
theorem B5550889 : Blo 2191435 5550889 := bstep (se 2 (by rfl) ⟨2081583, by rfl⟩ : syracuseStep 5550889 = 4163167) B4163167
theorem B7401185 : Blo 2191435 7401185 := bstep (se 2 (by rfl) ⟨2775444, by rfl⟩ : syracuseStep 7401185 = 5550889) B5550889
theorem B4934123 : Blo 2191435 4934123 := bstep (se 1 (by rfl) ⟨3700592, by rfl⟩ : syracuseStep 4934123 = 7401185) B7401185
theorem B3289415 : Blo 2191435 3289415 := bstep (se 1 (by rfl) ⟨2467061, by rfl⟩ : syracuseStep 3289415 = 4934123) B4934123
theorem B2192943 : Blo 2191435 2192943 := bstep (se 1 (by rfl) ⟨1644707, by rfl⟩ : syracuseStep 2192943 = 3289415) B3289415
theorem B3289421 : Blo 2191435 3289421 := bbase (se 3 (by rfl) ⟨616766, by rfl⟩ : syracuseStep 3289421 = 1233533) (by norm_num)
theorem B2192947 : Blo 2191435 2192947 := bstep (se 1 (by rfl) ⟨1644710, by rfl⟩ : syracuseStep 2192947 = 3289421) B3289421
theorem B4934141 : Blo 2191435 4934141 := bbase (se 3 (by rfl) ⟨925151, by rfl⟩ : syracuseStep 4934141 = 1850303) (by norm_num)
theorem B3289427 : Blo 2191435 3289427 := bstep (se 1 (by rfl) ⟨2467070, by rfl⟩ : syracuseStep 3289427 = 4934141) B4934141
theorem B2192951 : Blo 2191435 2192951 := bstep (se 1 (by rfl) ⟨1644713, by rfl⟩ : syracuseStep 2192951 = 3289427) B3289427
theorem B3700613 : Blo 2191435 3700613 := bbase (se 4 (by rfl) ⟨346932, by rfl⟩ : syracuseStep 3700613 = 693865) (by norm_num)
theorem B2467075 : Blo 2191435 2467075 := bstep (se 1 (by rfl) ⟨1850306, by rfl⟩ : syracuseStep 2467075 = 3700613) B3700613
theorem B3289433 : Blo 2191435 3289433 := bstep (se 2 (by rfl) ⟨1233537, by rfl⟩ : syracuseStep 3289433 = 2467075) B2467075
theorem B2192955 : Blo 2191435 2192955 := bstep (se 1 (by rfl) ⟨1644716, by rfl⟩ : syracuseStep 2192955 = 3289433) B3289433
theorem B16652789 : Blo 2191435 16652789 := bbase (se 5 (by rfl) ⟨780599, by rfl⟩ : syracuseStep 16652789 = 1561199) (by norm_num)
theorem B11101859 : Blo 2191435 11101859 := bstep (se 1 (by rfl) ⟨8326394, by rfl⟩ : syracuseStep 11101859 = 16652789) B16652789
theorem B7401239 : Blo 2191435 7401239 := bstep (se 1 (by rfl) ⟨5550929, by rfl⟩ : syracuseStep 7401239 = 11101859) B11101859
theorem B4934159 : Blo 2191435 4934159 := bstep (se 1 (by rfl) ⟨3700619, by rfl⟩ : syracuseStep 4934159 = 7401239) B7401239
theorem B3289439 : Blo 2191435 3289439 := bstep (se 1 (by rfl) ⟨2467079, by rfl⟩ : syracuseStep 3289439 = 4934159) B4934159
theorem B2192959 : Blo 2191435 2192959 := bstep (se 1 (by rfl) ⟨1644719, by rfl⟩ : syracuseStep 2192959 = 3289439) B3289439
theorem B3289445 : Blo 2191435 3289445 := bbase (se 4 (by rfl) ⟨308385, by rfl⟩ : syracuseStep 3289445 = 616771) (by norm_num)
theorem B2192963 : Blo 2191435 2192963 := bstep (se 1 (by rfl) ⟨1644722, by rfl⟩ : syracuseStep 2192963 = 3289445) B3289445
theorem B4163213 : Blo 2191435 4163213 := bbase (se 3 (by rfl) ⟨780602, by rfl⟩ : syracuseStep 4163213 = 1561205) (by norm_num)
theorem B2775475 : Blo 2191435 2775475 := bstep (se 1 (by rfl) ⟨2081606, by rfl⟩ : syracuseStep 2775475 = 4163213) B4163213
theorem B3700633 : Blo 2191435 3700633 := bstep (se 2 (by rfl) ⟨1387737, by rfl⟩ : syracuseStep 3700633 = 2775475) B2775475
theorem B4934177 : Blo 2191435 4934177 := bstep (se 2 (by rfl) ⟨1850316, by rfl⟩ : syracuseStep 4934177 = 3700633) B3700633
theorem B3289451 : Blo 2191435 3289451 := bstep (se 1 (by rfl) ⟨2467088, by rfl⟩ : syracuseStep 3289451 = 4934177) B4934177
theorem B2192967 : Blo 2191435 2192967 := bstep (se 1 (by rfl) ⟨1644725, by rfl⟩ : syracuseStep 2192967 = 3289451) B3289451
theorem B2467093 : Blo 2191435 2467093 := bbase (se 6 (by rfl) ⟨57822, by rfl⟩ : syracuseStep 2467093 = 115645) (by norm_num)
theorem B3289457 : Blo 2191435 3289457 := bstep (se 2 (by rfl) ⟨1233546, by rfl⟩ : syracuseStep 3289457 = 2467093) B2467093
theorem B2192971 : Blo 2191435 2192971 := bstep (se 1 (by rfl) ⟨1644728, by rfl⟩ : syracuseStep 2192971 = 3289457) B3289457
theorem B2775485 : Blo 2191435 2775485 := bbase (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) (by norm_num)
theorem B7401293 : Blo 2191435 7401293 := bstep (se 3 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 7401293 = 2775485) B2775485
theorem B4934195 : Blo 2191435 4934195 := bstep (se 1 (by rfl) ⟨3700646, by rfl⟩ : syracuseStep 4934195 = 7401293) B7401293
theorem B3289463 : Blo 2191435 3289463 := bstep (se 1 (by rfl) ⟨2467097, by rfl⟩ : syracuseStep 3289463 = 4934195) B4934195
theorem B2192975 : Blo 2191435 2192975 := bstep (se 1 (by rfl) ⟨1644731, by rfl⟩ : syracuseStep 2192975 = 3289463) B3289463
theorem B3289469 : Blo 2191435 3289469 := bbase (se 3 (by rfl) ⟨616775, by rfl⟩ : syracuseStep 3289469 = 1233551) (by norm_num)
theorem B2192979 : Blo 2191435 2192979 := bstep (se 1 (by rfl) ⟨1644734, by rfl⟩ : syracuseStep 2192979 = 3289469) B3289469
theorem B4934213 : Blo 2191435 4934213 := bbase (se 4 (by rfl) ⟨462582, by rfl⟩ : syracuseStep 4934213 = 925165) (by norm_num)
theorem B3289475 : Blo 2191435 3289475 := bstep (se 1 (by rfl) ⟨2467106, by rfl⟩ : syracuseStep 3289475 = 4934213) B4934213
theorem B2192983 : Blo 2191435 2192983 := bstep (se 1 (by rfl) ⟨1644737, by rfl⟩ : syracuseStep 2192983 = 3289475) B3289475
theorem B2341829 : Blo 2191435 2341829 := bbase (se 4 (by rfl) ⟨219546, by rfl⟩ : syracuseStep 2341829 = 439093) (by norm_num)
theorem B6244877 : Blo 2191435 6244877 := bstep (se 3 (by rfl) ⟨1170914, by rfl⟩ : syracuseStep 6244877 = 2341829) B2341829
theorem B4163251 : Blo 2191435 4163251 := bstep (se 1 (by rfl) ⟨3122438, by rfl⟩ : syracuseStep 4163251 = 6244877) B6244877
theorem B5551001 : Blo 2191435 5551001 := bstep (se 2 (by rfl) ⟨2081625, by rfl⟩ : syracuseStep 5551001 = 4163251) B4163251
theorem B3700667 : Blo 2191435 3700667 := bstep (se 1 (by rfl) ⟨2775500, by rfl⟩ : syracuseStep 3700667 = 5551001) B5551001
theorem B2467111 : Blo 2191435 2467111 := bstep (se 1 (by rfl) ⟨1850333, by rfl⟩ : syracuseStep 2467111 = 3700667) B3700667
theorem B3289481 : Blo 2191435 3289481 := bstep (se 2 (by rfl) ⟨1233555, by rfl⟩ : syracuseStep 3289481 = 2467111) B2467111
theorem B2192987 : Blo 2191435 2192987 := bstep (se 1 (by rfl) ⟨1644740, by rfl⟩ : syracuseStep 2192987 = 3289481) B3289481
theorem B11102021 : Blo 2191435 11102021 := bbase (se 4 (by rfl) ⟨1040814, by rfl⟩ : syracuseStep 11102021 = 2081629) (by norm_num)
theorem B7401347 : Blo 2191435 7401347 := bstep (se 1 (by rfl) ⟨5551010, by rfl⟩ : syracuseStep 7401347 = 11102021) B11102021
theorem B4934231 : Blo 2191435 4934231 := bstep (se 1 (by rfl) ⟨3700673, by rfl⟩ : syracuseStep 4934231 = 7401347) B7401347
theorem B3289487 : Blo 2191435 3289487 := bstep (se 1 (by rfl) ⟨2467115, by rfl⟩ : syracuseStep 3289487 = 4934231) B4934231
theorem B2192991 : Blo 2191435 2192991 := bstep (se 1 (by rfl) ⟨1644743, by rfl⟩ : syracuseStep 2192991 = 3289487) B3289487
theorem B3289493 : Blo 2191435 3289493 := bbase (se 6 (by rfl) ⟨77097, by rfl⟩ : syracuseStep 3289493 = 154195) (by norm_num)
theorem B2192995 : Blo 2191435 2192995 := bstep (se 1 (by rfl) ⟨1644746, by rfl⟩ : syracuseStep 2192995 = 3289493) B3289493
theorem B7025525 : Blo 2191435 7025525 := bbase (se 5 (by rfl) ⟨329321, by rfl⟩ : syracuseStep 7025525 = 658643) (by norm_num)
theorem B4683683 : Blo 2191435 4683683 := bstep (se 1 (by rfl) ⟨3512762, by rfl⟩ : syracuseStep 4683683 = 7025525) B7025525
theorem B12489821 : Blo 2191435 12489821 := bstep (se 3 (by rfl) ⟨2341841, by rfl⟩ : syracuseStep 12489821 = 4683683) B4683683
theorem B8326547 : Blo 2191435 8326547 := bstep (se 1 (by rfl) ⟨6244910, by rfl⟩ : syracuseStep 8326547 = 12489821) B12489821
theorem B5551031 : Blo 2191435 5551031 := bstep (se 1 (by rfl) ⟨4163273, by rfl⟩ : syracuseStep 5551031 = 8326547) B8326547
theorem B3700687 : Blo 2191435 3700687 := bstep (se 1 (by rfl) ⟨2775515, by rfl⟩ : syracuseStep 3700687 = 5551031) B5551031
theorem B4934249 : Blo 2191435 4934249 := bstep (se 2 (by rfl) ⟨1850343, by rfl⟩ : syracuseStep 4934249 = 3700687) B3700687
theorem B3289499 : Blo 2191435 3289499 := bstep (se 1 (by rfl) ⟨2467124, by rfl⟩ : syracuseStep 3289499 = 4934249) B4934249
theorem B2192999 : Blo 2191435 2192999 := bstep (se 1 (by rfl) ⟨1644749, by rfl⟩ : syracuseStep 2192999 = 3289499) B3289499
theorem B2467129 : Blo 2191435 2467129 := bbase (se 2 (by rfl) ⟨925173, by rfl⟩ : syracuseStep 2467129 = 1850347) (by norm_num)
theorem B3289505 : Blo 2191435 3289505 := bstep (se 2 (by rfl) ⟨1233564, by rfl⟩ : syracuseStep 3289505 = 2467129) B2467129
theorem B2193003 : Blo 2191435 2193003 := bstep (se 1 (by rfl) ⟨1644752, by rfl⟩ : syracuseStep 2193003 = 3289505) B3289505
theorem B6244933 : Blo 2191435 6244933 := bbase (se 4 (by rfl) ⟨585462, by rfl⟩ : syracuseStep 6244933 = 1170925) (by norm_num)
theorem B8326577 : Blo 2191435 8326577 := bstep (se 2 (by rfl) ⟨3122466, by rfl⟩ : syracuseStep 8326577 = 6244933) B6244933
theorem B5551051 : Blo 2191435 5551051 := bstep (se 1 (by rfl) ⟨4163288, by rfl⟩ : syracuseStep 5551051 = 8326577) B8326577
theorem B7401401 : Blo 2191435 7401401 := bstep (se 2 (by rfl) ⟨2775525, by rfl⟩ : syracuseStep 7401401 = 5551051) B5551051
theorem B4934267 : Blo 2191435 4934267 := bstep (se 1 (by rfl) ⟨3700700, by rfl⟩ : syracuseStep 4934267 = 7401401) B7401401
theorem B3289511 : Blo 2191435 3289511 := bstep (se 1 (by rfl) ⟨2467133, by rfl⟩ : syracuseStep 3289511 = 4934267) B4934267
theorem B2193007 : Blo 2191435 2193007 := bstep (se 1 (by rfl) ⟨1644755, by rfl⟩ : syracuseStep 2193007 = 3289511) B3289511
theorem B3289517 : Blo 2191435 3289517 := bbase (se 3 (by rfl) ⟨616784, by rfl⟩ : syracuseStep 3289517 = 1233569) (by norm_num)
theorem B2193011 : Blo 2191435 2193011 := bstep (se 1 (by rfl) ⟨1644758, by rfl⟩ : syracuseStep 2193011 = 3289517) B3289517
theorem B4934285 : Blo 2191435 4934285 := bbase (se 3 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 4934285 = 1850357) (by norm_num)
theorem B3289523 : Blo 2191435 3289523 := bstep (se 1 (by rfl) ⟨2467142, by rfl⟩ : syracuseStep 3289523 = 4934285) B4934285
theorem B2193015 : Blo 2191435 2193015 := bstep (se 1 (by rfl) ⟨1644761, by rfl⟩ : syracuseStep 2193015 = 3289523) B3289523
theorem B2775541 : Blo 2191435 2775541 := bbase (se 5 (by rfl) ⟨130103, by rfl⟩ : syracuseStep 2775541 = 260207) (by norm_num)
theorem B3700721 : Blo 2191435 3700721 := bstep (se 2 (by rfl) ⟨1387770, by rfl⟩ : syracuseStep 3700721 = 2775541) B2775541
theorem B2467147 : Blo 2191435 2467147 := bstep (se 1 (by rfl) ⟨1850360, by rfl⟩ : syracuseStep 2467147 = 3700721) B3700721
theorem B3289529 : Blo 2191435 3289529 := bstep (se 2 (by rfl) ⟨1233573, by rfl⟩ : syracuseStep 3289529 = 2467147) B2467147
theorem B2193019 : Blo 2191435 2193019 := bstep (se 1 (by rfl) ⟨1644764, by rfl⟩ : syracuseStep 2193019 = 3289529) B3289529
theorem B5626829 : Blo 2191435 5626829 := bbase (se 3 (by rfl) ⟨1055030, by rfl⟩ : syracuseStep 5626829 = 2110061) (by norm_num)
theorem B3751219 : Blo 2191435 3751219 := bstep (se 1 (by rfl) ⟨2813414, by rfl⟩ : syracuseStep 3751219 = 5626829) B5626829
theorem B5001625 : Blo 2191435 5001625 := bstep (se 2 (by rfl) ⟨1875609, by rfl⟩ : syracuseStep 5001625 = 3751219) B3751219
theorem B6668833 : Blo 2191435 6668833 := bstep (se 2 (by rfl) ⟨2500812, by rfl⟩ : syracuseStep 6668833 = 5001625) B5001625
theorem B8891777 : Blo 2191435 8891777 := bstep (se 2 (by rfl) ⟨3334416, by rfl⟩ : syracuseStep 8891777 = 6668833) B6668833
theorem B5927851 : Blo 2191435 5927851 := bstep (se 1 (by rfl) ⟨4445888, by rfl⟩ : syracuseStep 5927851 = 8891777) B8891777
theorem B7903801 : Blo 2191435 7903801 := bstep (se 2 (by rfl) ⟨2963925, by rfl⟩ : syracuseStep 7903801 = 5927851) B5927851
theorem B42153605 : Blo 2191435 42153605 := bstep (se 4 (by rfl) ⟨3951900, by rfl⟩ : syracuseStep 42153605 = 7903801) B7903801
theorem B28102403 : Blo 2191435 28102403 := bstep (se 1 (by rfl) ⟨21076802, by rfl⟩ : syracuseStep 28102403 = 42153605) B42153605
theorem B18734935 : Blo 2191435 18734935 := bstep (se 1 (by rfl) ⟨14051201, by rfl⟩ : syracuseStep 18734935 = 28102403) B28102403
theorem B24979913 : Blo 2191435 24979913 := bstep (se 2 (by rfl) ⟨9367467, by rfl⟩ : syracuseStep 24979913 = 18734935) B18734935
theorem B16653275 : Blo 2191435 16653275 := bstep (se 1 (by rfl) ⟨12489956, by rfl⟩ : syracuseStep 16653275 = 24979913) B24979913
theorem B11102183 : Blo 2191435 11102183 := bstep (se 1 (by rfl) ⟨8326637, by rfl⟩ : syracuseStep 11102183 = 16653275) B16653275
theorem B7401455 : Blo 2191435 7401455 := bstep (se 1 (by rfl) ⟨5551091, by rfl⟩ : syracuseStep 7401455 = 11102183) B11102183
theorem B4934303 : Blo 2191435 4934303 := bstep (se 1 (by rfl) ⟨3700727, by rfl⟩ : syracuseStep 4934303 = 7401455) B7401455
theorem B3289535 : Blo 2191435 3289535 := bstep (se 1 (by rfl) ⟨2467151, by rfl⟩ : syracuseStep 3289535 = 4934303) B4934303
theorem B2193023 : Blo 2191435 2193023 := bstep (se 1 (by rfl) ⟨1644767, by rfl⟩ : syracuseStep 2193023 = 3289535) B3289535
theorem B3289541 : Blo 2191435 3289541 := bbase (se 4 (by rfl) ⟨308394, by rfl⟩ : syracuseStep 3289541 = 616789) (by norm_num)
theorem B2193027 : Blo 2191435 2193027 := bstep (se 1 (by rfl) ⟨1644770, by rfl⟩ : syracuseStep 2193027 = 3289541) B3289541
theorem B3700741 : Blo 2191435 3700741 := bbase (se 4 (by rfl) ⟨346944, by rfl⟩ : syracuseStep 3700741 = 693889) (by norm_num)
theorem B4934321 : Blo 2191435 4934321 := bstep (se 2 (by rfl) ⟨1850370, by rfl⟩ : syracuseStep 4934321 = 3700741) B3700741
theorem B3289547 : Blo 2191435 3289547 := bstep (se 1 (by rfl) ⟨2467160, by rfl⟩ : syracuseStep 3289547 = 4934321) B4934321
theorem B2193031 : Blo 2191435 2193031 := bstep (se 1 (by rfl) ⟨1644773, by rfl⟩ : syracuseStep 2193031 = 3289547) B3289547
theorem B2467165 : Blo 2191435 2467165 := bbase (se 3 (by rfl) ⟨462593, by rfl⟩ : syracuseStep 2467165 = 925187) (by norm_num)
theorem B3289553 : Blo 2191435 3289553 := bstep (se 2 (by rfl) ⟨1233582, by rfl⟩ : syracuseStep 3289553 = 2467165) B2467165
theorem B2193035 : Blo 2191435 2193035 := bstep (se 1 (by rfl) ⟨1644776, by rfl⟩ : syracuseStep 2193035 = 3289553) B3289553
theorem B7401509 : Blo 2191435 7401509 := bbase (se 4 (by rfl) ⟨693891, by rfl⟩ : syracuseStep 7401509 = 1387783) (by norm_num)
theorem B4934339 : Blo 2191435 4934339 := bstep (se 1 (by rfl) ⟨3700754, by rfl⟩ : syracuseStep 4934339 = 7401509) B7401509
theorem B3289559 : Blo 2191435 3289559 := bstep (se 1 (by rfl) ⟨2467169, by rfl⟩ : syracuseStep 3289559 = 4934339) B4934339
theorem B2193039 : Blo 2191435 2193039 := bstep (se 1 (by rfl) ⟨1644779, by rfl⟩ : syracuseStep 2193039 = 3289559) B3289559
theorem B3289565 : Blo 2191435 3289565 := bbase (se 3 (by rfl) ⟨616793, by rfl⟩ : syracuseStep 3289565 = 1233587) (by norm_num)
theorem B2193043 : Blo 2191435 2193043 := bstep (se 1 (by rfl) ⟨1644782, by rfl⟩ : syracuseStep 2193043 = 3289565) B3289565
theorem B4934357 : Blo 2191435 4934357 := bbase (se 7 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 4934357 = 115649) (by norm_num)
theorem B3289571 : Blo 2191435 3289571 := bstep (se 1 (by rfl) ⟨2467178, by rfl⟩ : syracuseStep 3289571 = 4934357) B4934357
theorem B2193047 : Blo 2191435 2193047 := bstep (se 1 (by rfl) ⟨1644785, by rfl⟩ : syracuseStep 2193047 = 3289571) B3289571
theorem B9367589 : Blo 2191435 9367589 := bbase (se 4 (by rfl) ⟨878211, by rfl⟩ : syracuseStep 9367589 = 1756423) (by norm_num)
theorem B6245059 : Blo 2191435 6245059 := bstep (se 1 (by rfl) ⟨4683794, by rfl⟩ : syracuseStep 6245059 = 9367589) B9367589
theorem B8326745 : Blo 2191435 8326745 := bstep (se 2 (by rfl) ⟨3122529, by rfl⟩ : syracuseStep 8326745 = 6245059) B6245059
theorem B5551163 : Blo 2191435 5551163 := bstep (se 1 (by rfl) ⟨4163372, by rfl⟩ : syracuseStep 5551163 = 8326745) B8326745
theorem B3700775 : Blo 2191435 3700775 := bstep (se 1 (by rfl) ⟨2775581, by rfl⟩ : syracuseStep 3700775 = 5551163) B5551163
theorem B2467183 : Blo 2191435 2467183 := bstep (se 1 (by rfl) ⟨1850387, by rfl⟩ : syracuseStep 2467183 = 3700775) B3700775
theorem B3289577 : Blo 2191435 3289577 := bstep (se 2 (by rfl) ⟨1233591, by rfl⟩ : syracuseStep 3289577 = 2467183) B2467183
theorem B2193051 : Blo 2191435 2193051 := bstep (se 1 (by rfl) ⟨1644788, by rfl⟩ : syracuseStep 2193051 = 3289577) B3289577
theorem B2500849 : Blo 2191435 2500849 := bbase (se 2 (by rfl) ⟨937818, by rfl⟩ : syracuseStep 2500849 = 1875637) (by norm_num)
theorem B3334465 : Blo 2191435 3334465 := bstep (se 2 (by rfl) ⟨1250424, by rfl⟩ : syracuseStep 3334465 = 2500849) B2500849
theorem B17783813 : Blo 2191435 17783813 := bstep (se 4 (by rfl) ⟨1667232, by rfl⟩ : syracuseStep 17783813 = 3334465) B3334465
theorem B47423501 : Blo 2191435 47423501 := bstep (se 3 (by rfl) ⟨8891906, by rfl⟩ : syracuseStep 47423501 = 17783813) B17783813
theorem B31615667 : Blo 2191435 31615667 := bstep (se 1 (by rfl) ⟨23711750, by rfl⟩ : syracuseStep 31615667 = 47423501) B47423501
theorem B21077111 : Blo 2191435 21077111 := bstep (se 1 (by rfl) ⟨15807833, by rfl⟩ : syracuseStep 21077111 = 31615667) B31615667
theorem B14051407 : Blo 2191435 14051407 := bstep (se 1 (by rfl) ⟨10538555, by rfl⟩ : syracuseStep 14051407 = 21077111) B21077111
theorem B18735209 : Blo 2191435 18735209 := bstep (se 2 (by rfl) ⟨7025703, by rfl⟩ : syracuseStep 18735209 = 14051407) B14051407
theorem B12490139 : Blo 2191435 12490139 := bstep (se 1 (by rfl) ⟨9367604, by rfl⟩ : syracuseStep 12490139 = 18735209) B18735209
theorem B8326759 : Blo 2191435 8326759 := bstep (se 1 (by rfl) ⟨6245069, by rfl⟩ : syracuseStep 8326759 = 12490139) B12490139
theorem B11102345 : Blo 2191435 11102345 := bstep (se 2 (by rfl) ⟨4163379, by rfl⟩ : syracuseStep 11102345 = 8326759) B8326759
theorem B7401563 : Blo 2191435 7401563 := bstep (se 1 (by rfl) ⟨5551172, by rfl⟩ : syracuseStep 7401563 = 11102345) B11102345
theorem B4934375 : Blo 2191435 4934375 := bstep (se 1 (by rfl) ⟨3700781, by rfl⟩ : syracuseStep 4934375 = 7401563) B7401563
theorem B3289583 : Blo 2191435 3289583 := bstep (se 1 (by rfl) ⟨2467187, by rfl⟩ : syracuseStep 3289583 = 4934375) B4934375
theorem B2193055 : Blo 2191435 2193055 := bstep (se 1 (by rfl) ⟨1644791, by rfl⟩ : syracuseStep 2193055 = 3289583) B3289583
theorem B3289589 : Blo 2191435 3289589 := bbase (se 5 (by rfl) ⟨154199, by rfl⟩ : syracuseStep 3289589 = 308399) (by norm_num)
theorem B2193059 : Blo 2191435 2193059 := bstep (se 1 (by rfl) ⟨1644794, by rfl⟩ : syracuseStep 2193059 = 3289589) B3289589
theorem B6245093 : Blo 2191435 6245093 := bbase (se 4 (by rfl) ⟨585477, by rfl⟩ : syracuseStep 6245093 = 1170955) (by norm_num)
theorem B4163395 : Blo 2191435 4163395 := bstep (se 1 (by rfl) ⟨3122546, by rfl⟩ : syracuseStep 4163395 = 6245093) B6245093
theorem B5551193 : Blo 2191435 5551193 := bstep (se 2 (by rfl) ⟨2081697, by rfl⟩ : syracuseStep 5551193 = 4163395) B4163395
theorem B3700795 : Blo 2191435 3700795 := bstep (se 1 (by rfl) ⟨2775596, by rfl⟩ : syracuseStep 3700795 = 5551193) B5551193
theorem B4934393 : Blo 2191435 4934393 := bstep (se 2 (by rfl) ⟨1850397, by rfl⟩ : syracuseStep 4934393 = 3700795) B3700795
theorem B3289595 : Blo 2191435 3289595 := bstep (se 1 (by rfl) ⟨2467196, by rfl⟩ : syracuseStep 3289595 = 4934393) B4934393
theorem B2193063 : Blo 2191435 2193063 := bstep (se 1 (by rfl) ⟨1644797, by rfl⟩ : syracuseStep 2193063 = 3289595) B3289595
theorem B2467201 : Blo 2191435 2467201 := bbase (se 2 (by rfl) ⟨925200, by rfl⟩ : syracuseStep 2467201 = 1850401) (by norm_num)
theorem B3289601 : Blo 2191435 3289601 := bstep (se 2 (by rfl) ⟨1233600, by rfl⟩ : syracuseStep 3289601 = 2467201) B2467201
theorem B2193067 : Blo 2191435 2193067 := bstep (se 1 (by rfl) ⟨1644800, by rfl⟩ : syracuseStep 2193067 = 3289601) B3289601
theorem B5551213 : Blo 2191435 5551213 := bbase (se 3 (by rfl) ⟨1040852, by rfl⟩ : syracuseStep 5551213 = 2081705) (by norm_num)
theorem B7401617 : Blo 2191435 7401617 := bstep (se 2 (by rfl) ⟨2775606, by rfl⟩ : syracuseStep 7401617 = 5551213) B5551213
theorem B4934411 : Blo 2191435 4934411 := bstep (se 1 (by rfl) ⟨3700808, by rfl⟩ : syracuseStep 4934411 = 7401617) B7401617
theorem B3289607 : Blo 2191435 3289607 := bstep (se 1 (by rfl) ⟨2467205, by rfl⟩ : syracuseStep 3289607 = 4934411) B4934411
theorem B2193071 : Blo 2191435 2193071 := bstep (se 1 (by rfl) ⟨1644803, by rfl⟩ : syracuseStep 2193071 = 3289607) B3289607
theorem B3289613 : Blo 2191435 3289613 := bbase (se 3 (by rfl) ⟨616802, by rfl⟩ : syracuseStep 3289613 = 1233605) (by norm_num)
theorem B2193075 : Blo 2191435 2193075 := bstep (se 1 (by rfl) ⟨1644806, by rfl⟩ : syracuseStep 2193075 = 3289613) B3289613
theorem B4934429 : Blo 2191435 4934429 := bbase (se 3 (by rfl) ⟨925205, by rfl⟩ : syracuseStep 4934429 = 1850411) (by norm_num)
theorem B3289619 : Blo 2191435 3289619 := bstep (se 1 (by rfl) ⟨2467214, by rfl⟩ : syracuseStep 3289619 = 4934429) B4934429
theorem B2193079 : Blo 2191435 2193079 := bstep (se 1 (by rfl) ⟨1644809, by rfl⟩ : syracuseStep 2193079 = 3289619) B3289619
theorem B3700829 : Blo 2191435 3700829 := bbase (se 3 (by rfl) ⟨693905, by rfl⟩ : syracuseStep 3700829 = 1387811) (by norm_num)
theorem B2467219 : Blo 2191435 2467219 := bstep (se 1 (by rfl) ⟨1850414, by rfl⟩ : syracuseStep 2467219 = 3700829) B3700829
theorem B3289625 : Blo 2191435 3289625 := bstep (se 2 (by rfl) ⟨1233609, by rfl⟩ : syracuseStep 3289625 = 2467219) B2467219
theorem B2193083 : Blo 2191435 2193083 := bstep (se 1 (by rfl) ⟨1644812, by rfl⟩ : syracuseStep 2193083 = 3289625) B3289625
theorem B6669029 : Blo 2191435 6669029 := bbase (se 4 (by rfl) ⟨625221, by rfl⟩ : syracuseStep 6669029 = 1250443) (by norm_num)
theorem B4446019 : Blo 2191435 4446019 := bstep (se 1 (by rfl) ⟨3334514, by rfl⟩ : syracuseStep 4446019 = 6669029) B6669029
theorem B5928025 : Blo 2191435 5928025 := bstep (se 2 (by rfl) ⟨2223009, by rfl⟩ : syracuseStep 5928025 = 4446019) B4446019
theorem B7904033 : Blo 2191435 7904033 := bstep (se 2 (by rfl) ⟨2964012, by rfl⟩ : syracuseStep 7904033 = 5928025) B5928025
theorem B5269355 : Blo 2191435 5269355 := bstep (se 1 (by rfl) ⟨3952016, by rfl⟩ : syracuseStep 5269355 = 7904033) B7904033
theorem B3512903 : Blo 2191435 3512903 := bstep (se 1 (by rfl) ⟨2634677, by rfl⟩ : syracuseStep 3512903 = 5269355) B5269355
theorem B9367741 : Blo 2191435 9367741 := bstep (se 3 (by rfl) ⟨1756451, by rfl⟩ : syracuseStep 9367741 = 3512903) B3512903
theorem B12490321 : Blo 2191435 12490321 := bstep (se 2 (by rfl) ⟨4683870, by rfl⟩ : syracuseStep 12490321 = 9367741) B9367741
theorem B16653761 : Blo 2191435 16653761 := bstep (se 2 (by rfl) ⟨6245160, by rfl⟩ : syracuseStep 16653761 = 12490321) B12490321
theorem B11102507 : Blo 2191435 11102507 := bstep (se 1 (by rfl) ⟨8326880, by rfl⟩ : syracuseStep 11102507 = 16653761) B16653761
theorem B7401671 : Blo 2191435 7401671 := bstep (se 1 (by rfl) ⟨5551253, by rfl⟩ : syracuseStep 7401671 = 11102507) B11102507
theorem B4934447 : Blo 2191435 4934447 := bstep (se 1 (by rfl) ⟨3700835, by rfl⟩ : syracuseStep 4934447 = 7401671) B7401671
theorem B3289631 : Blo 2191435 3289631 := bstep (se 1 (by rfl) ⟨2467223, by rfl⟩ : syracuseStep 3289631 = 4934447) B4934447
theorem B2193087 : Blo 2191435 2193087 := bstep (se 1 (by rfl) ⟨1644815, by rfl⟩ : syracuseStep 2193087 = 3289631) B3289631
theorem B3289637 : Blo 2191435 3289637 := bbase (se 4 (by rfl) ⟨308403, by rfl⟩ : syracuseStep 3289637 = 616807) (by norm_num)
theorem B2193091 : Blo 2191435 2193091 := bstep (se 1 (by rfl) ⟨1644818, by rfl⟩ : syracuseStep 2193091 = 3289637) B3289637
theorem B2775637 : Blo 2191435 2775637 := bbase (se 8 (by rfl) ⟨16263, by rfl⟩ : syracuseStep 2775637 = 32527) (by norm_num)
theorem B3700849 : Blo 2191435 3700849 := bstep (se 2 (by rfl) ⟨1387818, by rfl⟩ : syracuseStep 3700849 = 2775637) B2775637
theorem B4934465 : Blo 2191435 4934465 := bstep (se 2 (by rfl) ⟨1850424, by rfl⟩ : syracuseStep 4934465 = 3700849) B3700849
theorem B3289643 : Blo 2191435 3289643 := bstep (se 1 (by rfl) ⟨2467232, by rfl⟩ : syracuseStep 3289643 = 4934465) B4934465
theorem B2193095 : Blo 2191435 2193095 := bstep (se 1 (by rfl) ⟨1644821, by rfl⟩ : syracuseStep 2193095 = 3289643) B3289643
theorem B2467237 : Blo 2191435 2467237 := bbase (se 4 (by rfl) ⟨231303, by rfl⟩ : syracuseStep 2467237 = 462607) (by norm_num)
theorem B3289649 : Blo 2191435 3289649 := bstep (se 2 (by rfl) ⟨1233618, by rfl⟩ : syracuseStep 3289649 = 2467237) B2467237
theorem B2193099 : Blo 2191435 2193099 := bstep (se 1 (by rfl) ⟨1644824, by rfl⟩ : syracuseStep 2193099 = 3289649) B3289649
theorem B2634697 : Blo 2191435 2634697 := bbase (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) (by norm_num)
theorem B14051717 : Blo 2191435 14051717 := bstep (se 4 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 14051717 = 2634697) B2634697
theorem B9367811 : Blo 2191435 9367811 := bstep (se 1 (by rfl) ⟨7025858, by rfl⟩ : syracuseStep 9367811 = 14051717) B14051717
theorem B6245207 : Blo 2191435 6245207 := bstep (se 1 (by rfl) ⟨4683905, by rfl⟩ : syracuseStep 6245207 = 9367811) B9367811
theorem B4163471 : Blo 2191435 4163471 := bstep (se 1 (by rfl) ⟨3122603, by rfl⟩ : syracuseStep 4163471 = 6245207) B6245207
theorem B2775647 : Blo 2191435 2775647 := bstep (se 1 (by rfl) ⟨2081735, by rfl⟩ : syracuseStep 2775647 = 4163471) B4163471
theorem B7401725 : Blo 2191435 7401725 := bstep (se 3 (by rfl) ⟨1387823, by rfl⟩ : syracuseStep 7401725 = 2775647) B2775647
theorem B4934483 : Blo 2191435 4934483 := bstep (se 1 (by rfl) ⟨3700862, by rfl⟩ : syracuseStep 4934483 = 7401725) B7401725
theorem B3289655 : Blo 2191435 3289655 := bstep (se 1 (by rfl) ⟨2467241, by rfl⟩ : syracuseStep 3289655 = 4934483) B4934483
theorem B2193103 : Blo 2191435 2193103 := bstep (se 1 (by rfl) ⟨1644827, by rfl⟩ : syracuseStep 2193103 = 3289655) B3289655
theorem B3289661 : Blo 2191435 3289661 := bbase (se 3 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 3289661 = 1233623) (by norm_num)
theorem B2193107 : Blo 2191435 2193107 := bstep (se 1 (by rfl) ⟨1644830, by rfl⟩ : syracuseStep 2193107 = 3289661) B3289661
theorem B4934501 : Blo 2191435 4934501 := bbase (se 4 (by rfl) ⟨462609, by rfl⟩ : syracuseStep 4934501 = 925219) (by norm_num)
theorem B3289667 : Blo 2191435 3289667 := bstep (se 1 (by rfl) ⟨2467250, by rfl⟩ : syracuseStep 3289667 = 4934501) B4934501
theorem B2193111 : Blo 2191435 2193111 := bstep (se 1 (by rfl) ⟨1644833, by rfl⟩ : syracuseStep 2193111 = 3289667) B3289667
theorem B5551325 : Blo 2191435 5551325 := bbase (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) (by norm_num)
theorem B3700883 : Blo 2191435 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B2467255 : Blo 2191435 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B3289673 : Blo 2191435 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B2193115 : Blo 2191435 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B4163501 : Blo 2191435 4163501 := bbase (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) (by norm_num)
theorem B11102669 : Blo 2191435 11102669 := bstep (se 3 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 11102669 = 4163501) B4163501
theorem B7401779 : Blo 2191435 7401779 := bstep (se 1 (by rfl) ⟨5551334, by rfl⟩ : syracuseStep 7401779 = 11102669) B11102669
theorem B4934519 : Blo 2191435 4934519 := bstep (se 1 (by rfl) ⟨3700889, by rfl⟩ : syracuseStep 4934519 = 7401779) B7401779
theorem B3289679 : Blo 2191435 3289679 := bstep (se 1 (by rfl) ⟨2467259, by rfl⟩ : syracuseStep 3289679 = 4934519) B4934519
theorem B2193119 : Blo 2191435 2193119 := bstep (se 1 (by rfl) ⟨1644839, by rfl⟩ : syracuseStep 2193119 = 3289679) B3289679
theorem B3289685 : Blo 2191435 3289685 := bbase (se 8 (by rfl) ⟨19275, by rfl⟩ : syracuseStep 3289685 = 38551) (by norm_num)
theorem B2193123 : Blo 2191435 2193123 := bstep (se 1 (by rfl) ⟨1644842, by rfl⟩ : syracuseStep 2193123 = 3289685) B3289685
theorem B23712533 : Blo 2191435 23712533 := bbase (se 6 (by rfl) ⟨555762, by rfl⟩ : syracuseStep 23712533 = 1111525) (by norm_num)
theorem B15808355 : Blo 2191435 15808355 := bstep (se 1 (by rfl) ⟨11856266, by rfl⟩ : syracuseStep 15808355 = 23712533) B23712533
theorem B10538903 : Blo 2191435 10538903 := bstep (se 1 (by rfl) ⟨7904177, by rfl⟩ : syracuseStep 10538903 = 15808355) B15808355
theorem B7025935 : Blo 2191435 7025935 := bstep (se 1 (by rfl) ⟨5269451, by rfl⟩ : syracuseStep 7025935 = 10538903) B10538903
theorem B9367913 : Blo 2191435 9367913 := bstep (se 2 (by rfl) ⟨3512967, by rfl⟩ : syracuseStep 9367913 = 7025935) B7025935
theorem B6245275 : Blo 2191435 6245275 := bstep (se 1 (by rfl) ⟨4683956, by rfl⟩ : syracuseStep 6245275 = 9367913) B9367913
theorem B8327033 : Blo 2191435 8327033 := bstep (se 2 (by rfl) ⟨3122637, by rfl⟩ : syracuseStep 8327033 = 6245275) B6245275
theorem B5551355 : Blo 2191435 5551355 := bstep (se 1 (by rfl) ⟨4163516, by rfl⟩ : syracuseStep 5551355 = 8327033) B8327033
theorem B3700903 : Blo 2191435 3700903 := bstep (se 1 (by rfl) ⟨2775677, by rfl⟩ : syracuseStep 3700903 = 5551355) B5551355
theorem B4934537 : Blo 2191435 4934537 := bstep (se 2 (by rfl) ⟨1850451, by rfl⟩ : syracuseStep 4934537 = 3700903) B3700903
theorem B3289691 : Blo 2191435 3289691 := bstep (se 1 (by rfl) ⟨2467268, by rfl⟩ : syracuseStep 3289691 = 4934537) B4934537
theorem B2193127 : Blo 2191435 2193127 := bstep (se 1 (by rfl) ⟨1644845, by rfl⟩ : syracuseStep 2193127 = 3289691) B3289691
theorem B2467273 : Blo 2191435 2467273 := bbase (se 2 (by rfl) ⟨925227, by rfl⟩ : syracuseStep 2467273 = 1850455) (by norm_num)
theorem B3289697 : Blo 2191435 3289697 := bstep (se 2 (by rfl) ⟨1233636, by rfl⟩ : syracuseStep 3289697 = 2467273) B2467273
theorem B2193131 : Blo 2191435 2193131 := bstep (se 1 (by rfl) ⟨1644848, by rfl⟩ : syracuseStep 2193131 = 3289697) B3289697
theorem B18735893 : Blo 2191435 18735893 := bbase (se 6 (by rfl) ⟨439122, by rfl⟩ : syracuseStep 18735893 = 878245) (by norm_num)
theorem B12490595 : Blo 2191435 12490595 := bstep (se 1 (by rfl) ⟨9367946, by rfl⟩ : syracuseStep 12490595 = 18735893) B18735893
theorem B8327063 : Blo 2191435 8327063 := bstep (se 1 (by rfl) ⟨6245297, by rfl⟩ : syracuseStep 8327063 = 12490595) B12490595
theorem B5551375 : Blo 2191435 5551375 := bstep (se 1 (by rfl) ⟨4163531, by rfl⟩ : syracuseStep 5551375 = 8327063) B8327063
theorem B7401833 : Blo 2191435 7401833 := bstep (se 2 (by rfl) ⟨2775687, by rfl⟩ : syracuseStep 7401833 = 5551375) B5551375
theorem B4934555 : Blo 2191435 4934555 := bstep (se 1 (by rfl) ⟨3700916, by rfl⟩ : syracuseStep 4934555 = 7401833) B7401833
theorem B3289703 : Blo 2191435 3289703 := bstep (se 1 (by rfl) ⟨2467277, by rfl⟩ : syracuseStep 3289703 = 4934555) B4934555
theorem B2193135 : Blo 2191435 2193135 := bstep (se 1 (by rfl) ⟨1644851, by rfl⟩ : syracuseStep 2193135 = 3289703) B3289703
theorem B3289709 : Blo 2191435 3289709 := bbase (se 3 (by rfl) ⟨616820, by rfl⟩ : syracuseStep 3289709 = 1233641) (by norm_num)
theorem B2193139 : Blo 2191435 2193139 := bstep (se 1 (by rfl) ⟨1644854, by rfl⟩ : syracuseStep 2193139 = 3289709) B3289709
theorem B4934573 : Blo 2191435 4934573 := bbase (se 3 (by rfl) ⟨925232, by rfl⟩ : syracuseStep 4934573 = 1850465) (by norm_num)
theorem B3289715 : Blo 2191435 3289715 := bstep (se 1 (by rfl) ⟨2467286, by rfl⟩ : syracuseStep 3289715 = 4934573) B4934573
theorem B2193143 : Blo 2191435 2193143 := bstep (se 1 (by rfl) ⟨1644857, by rfl⟩ : syracuseStep 2193143 = 3289715) B3289715
theorem B6245333 : Blo 2191435 6245333 := bbase (se 7 (by rfl) ⟨73187, by rfl⟩ : syracuseStep 6245333 = 146375) (by norm_num)
theorem B4163555 : Blo 2191435 4163555 := bstep (se 1 (by rfl) ⟨3122666, by rfl⟩ : syracuseStep 4163555 = 6245333) B6245333
theorem B2775703 : Blo 2191435 2775703 := bstep (se 1 (by rfl) ⟨2081777, by rfl⟩ : syracuseStep 2775703 = 4163555) B4163555
theorem B3700937 : Blo 2191435 3700937 := bstep (se 2 (by rfl) ⟨1387851, by rfl⟩ : syracuseStep 3700937 = 2775703) B2775703
theorem B2467291 : Blo 2191435 2467291 := bstep (se 1 (by rfl) ⟨1850468, by rfl⟩ : syracuseStep 2467291 = 3700937) B3700937
theorem B3289721 : Blo 2191435 3289721 := bstep (se 2 (by rfl) ⟨1233645, by rfl⟩ : syracuseStep 3289721 = 2467291) B2467291
theorem B2193147 : Blo 2191435 2193147 := bstep (se 1 (by rfl) ⟨1644860, by rfl⟩ : syracuseStep 2193147 = 3289721) B3289721
theorem B15005749 : Blo 2191435 15005749 := bbase (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) (by norm_num)
theorem B20007665 : Blo 2191435 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B13338443 : Blo 2191435 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B35569181 : Blo 2191435 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B23712787 : Blo 2191435 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B31617049 : Blo 2191435 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B42156065 : Blo 2191435 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B28104043 : Blo 2191435 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B37472057 : Blo 2191435 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B24981371 : Blo 2191435 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B16654247 : Blo 2191435 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B11102831 : Blo 2191435 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B7401887 : Blo 2191435 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B4934591 : Blo 2191435 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B3289727 : Blo 2191435 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B2193151 : Blo 2191435 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B3289733 : Blo 2191435 3289733 := bbase (se 4 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 3289733 = 616825) (by norm_num)
theorem B2193155 : Blo 2191435 2193155 := bstep (se 1 (by rfl) ⟨1644866, by rfl⟩ : syracuseStep 2193155 = 3289733) B3289733
theorem B3700957 : Blo 2191435 3700957 := bbase (se 3 (by rfl) ⟨693929, by rfl⟩ : syracuseStep 3700957 = 1387859) (by norm_num)
theorem B4934609 : Blo 2191435 4934609 := bstep (se 2 (by rfl) ⟨1850478, by rfl⟩ : syracuseStep 4934609 = 3700957) B3700957
theorem B3289739 : Blo 2191435 3289739 := bstep (se 1 (by rfl) ⟨2467304, by rfl⟩ : syracuseStep 3289739 = 4934609) B4934609
theorem B2193159 : Blo 2191435 2193159 := bstep (se 1 (by rfl) ⟨1644869, by rfl⟩ : syracuseStep 2193159 = 3289739) B3289739
theorem B2467309 : Blo 2191435 2467309 := bbase (se 3 (by rfl) ⟨462620, by rfl⟩ : syracuseStep 2467309 = 925241) (by norm_num)
theorem B3289745 : Blo 2191435 3289745 := bstep (se 2 (by rfl) ⟨1233654, by rfl⟩ : syracuseStep 3289745 = 2467309) B2467309
theorem B2193163 : Blo 2191435 2193163 := bstep (se 1 (by rfl) ⟨1644872, by rfl⟩ : syracuseStep 2193163 = 3289745) B3289745
theorem B7401941 : Blo 2191435 7401941 := bbase (se 7 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 7401941 = 173483) (by norm_num)
theorem B4934627 : Blo 2191435 4934627 := bstep (se 1 (by rfl) ⟨3700970, by rfl⟩ : syracuseStep 4934627 = 7401941) B7401941
theorem B3289751 : Blo 2191435 3289751 := bstep (se 1 (by rfl) ⟨2467313, by rfl⟩ : syracuseStep 3289751 = 4934627) B4934627
theorem B2193167 : Blo 2191435 2193167 := bstep (se 1 (by rfl) ⟨1644875, by rfl⟩ : syracuseStep 2193167 = 3289751) B3289751
theorem B3289757 : Blo 2191435 3289757 := bbase (se 3 (by rfl) ⟨616829, by rfl⟩ : syracuseStep 3289757 = 1233659) (by norm_num)
theorem B2193171 : Blo 2191435 2193171 := bstep (se 1 (by rfl) ⟨1644878, by rfl⟩ : syracuseStep 2193171 = 3289757) B3289757
theorem B4934645 : Blo 2191435 4934645 := bbase (se 5 (by rfl) ⟨231311, by rfl⟩ : syracuseStep 4934645 = 462623) (by norm_num)
theorem B3289763 : Blo 2191435 3289763 := bstep (se 1 (by rfl) ⟨2467322, by rfl⟩ : syracuseStep 3289763 = 4934645) B4934645
theorem B2193175 : Blo 2191435 2193175 := bstep (se 1 (by rfl) ⟨1644881, by rfl⟩ : syracuseStep 2193175 = 3289763) B3289763
theorem B17784821 : Blo 2191435 17784821 := bbase (se 5 (by rfl) ⟨833663, by rfl⟩ : syracuseStep 17784821 = 1667327) (by norm_num)
theorem B11856547 : Blo 2191435 11856547 := bstep (se 1 (by rfl) ⟨8892410, by rfl⟩ : syracuseStep 11856547 = 17784821) B17784821
theorem B63234917 : Blo 2191435 63234917 := bstep (se 4 (by rfl) ⟨5928273, by rfl⟩ : syracuseStep 63234917 = 11856547) B11856547
theorem B42156611 : Blo 2191435 42156611 := bstep (se 1 (by rfl) ⟨31617458, by rfl⟩ : syracuseStep 42156611 = 63234917) B63234917
theorem B28104407 : Blo 2191435 28104407 := bstep (se 1 (by rfl) ⟨21078305, by rfl⟩ : syracuseStep 28104407 = 42156611) B42156611
theorem B18736271 : Blo 2191435 18736271 := bstep (se 1 (by rfl) ⟨14052203, by rfl⟩ : syracuseStep 18736271 = 28104407) B28104407
theorem B12490847 : Blo 2191435 12490847 := bstep (se 1 (by rfl) ⟨9368135, by rfl⟩ : syracuseStep 12490847 = 18736271) B18736271
theorem B8327231 : Blo 2191435 8327231 := bstep (se 1 (by rfl) ⟨6245423, by rfl⟩ : syracuseStep 8327231 = 12490847) B12490847
theorem B5551487 : Blo 2191435 5551487 := bstep (se 1 (by rfl) ⟨4163615, by rfl⟩ : syracuseStep 5551487 = 8327231) B8327231
theorem B3700991 : Blo 2191435 3700991 := bstep (se 1 (by rfl) ⟨2775743, by rfl⟩ : syracuseStep 3700991 = 5551487) B5551487
theorem B2467327 : Blo 2191435 2467327 := bstep (se 1 (by rfl) ⟨1850495, by rfl⟩ : syracuseStep 2467327 = 3700991) B3700991
theorem B3289769 : Blo 2191435 3289769 := bstep (se 2 (by rfl) ⟨1233663, by rfl⟩ : syracuseStep 3289769 = 2467327) B2467327
theorem B2193179 : Blo 2191435 2193179 := bstep (se 1 (by rfl) ⟨1644884, by rfl⟩ : syracuseStep 2193179 = 3289769) B3289769
theorem B3122717 : Blo 2191435 3122717 := bbase (se 3 (by rfl) ⟨585509, by rfl⟩ : syracuseStep 3122717 = 1171019) (by norm_num)
theorem B8327245 : Blo 2191435 8327245 := bstep (se 3 (by rfl) ⟨1561358, by rfl⟩ : syracuseStep 8327245 = 3122717) B3122717
theorem B11102993 : Blo 2191435 11102993 := bstep (se 2 (by rfl) ⟨4163622, by rfl⟩ : syracuseStep 11102993 = 8327245) B8327245
theorem B7401995 : Blo 2191435 7401995 := bstep (se 1 (by rfl) ⟨5551496, by rfl⟩ : syracuseStep 7401995 = 11102993) B11102993
theorem B4934663 : Blo 2191435 4934663 := bstep (se 1 (by rfl) ⟨3700997, by rfl⟩ : syracuseStep 4934663 = 7401995) B7401995
theorem B3289775 : Blo 2191435 3289775 := bstep (se 1 (by rfl) ⟨2467331, by rfl⟩ : syracuseStep 3289775 = 4934663) B4934663
theorem B2193183 : Blo 2191435 2193183 := bstep (se 1 (by rfl) ⟨1644887, by rfl⟩ : syracuseStep 2193183 = 3289775) B3289775
theorem B3289781 : Blo 2191435 3289781 := bbase (se 5 (by rfl) ⟨154208, by rfl⟩ : syracuseStep 3289781 = 308417) (by norm_num)
theorem B2193187 : Blo 2191435 2193187 := bstep (se 1 (by rfl) ⟨1644890, by rfl⟩ : syracuseStep 2193187 = 3289781) B3289781
theorem B5551517 : Blo 2191435 5551517 := bbase (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) (by norm_num)
theorem B3701011 : Blo 2191435 3701011 := bstep (se 1 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 3701011 = 5551517) B5551517
theorem B4934681 : Blo 2191435 4934681 := bstep (se 2 (by rfl) ⟨1850505, by rfl⟩ : syracuseStep 4934681 = 3701011) B3701011
theorem B3289787 : Blo 2191435 3289787 := bstep (se 1 (by rfl) ⟨2467340, by rfl⟩ : syracuseStep 3289787 = 4934681) B4934681
theorem B2193191 : Blo 2191435 2193191 := bstep (se 1 (by rfl) ⟨1644893, by rfl⟩ : syracuseStep 2193191 = 3289787) B3289787
theorem B2467345 : Blo 2191435 2467345 := bbase (se 2 (by rfl) ⟨925254, by rfl⟩ : syracuseStep 2467345 = 1850509) (by norm_num)
theorem B3289793 : Blo 2191435 3289793 := bstep (se 2 (by rfl) ⟨1233672, by rfl⟩ : syracuseStep 3289793 = 2467345) B2467345
theorem B2193195 : Blo 2191435 2193195 := bstep (se 1 (by rfl) ⟨1644896, by rfl⟩ : syracuseStep 2193195 = 3289793) B3289793
theorem B4163653 : Blo 2191435 4163653 := bbase (se 4 (by rfl) ⟨390342, by rfl⟩ : syracuseStep 4163653 = 780685) (by norm_num)
theorem B5551537 : Blo 2191435 5551537 := bstep (se 2 (by rfl) ⟨2081826, by rfl⟩ : syracuseStep 5551537 = 4163653) B4163653
theorem B7402049 : Blo 2191435 7402049 := bstep (se 2 (by rfl) ⟨2775768, by rfl⟩ : syracuseStep 7402049 = 5551537) B5551537
theorem B4934699 : Blo 2191435 4934699 := bstep (se 1 (by rfl) ⟨3701024, by rfl⟩ : syracuseStep 4934699 = 7402049) B7402049
theorem B3289799 : Blo 2191435 3289799 := bstep (se 1 (by rfl) ⟨2467349, by rfl⟩ : syracuseStep 3289799 = 4934699) B4934699
theorem B2193199 : Blo 2191435 2193199 := bstep (se 1 (by rfl) ⟨1644899, by rfl⟩ : syracuseStep 2193199 = 3289799) B3289799
theorem B3289805 : Blo 2191435 3289805 := bbase (se 3 (by rfl) ⟨616838, by rfl⟩ : syracuseStep 3289805 = 1233677) (by norm_num)
theorem B2193203 : Blo 2191435 2193203 := bstep (se 1 (by rfl) ⟨1644902, by rfl⟩ : syracuseStep 2193203 = 3289805) B3289805
theorem B4934717 : Blo 2191435 4934717 := bbase (se 3 (by rfl) ⟨925259, by rfl⟩ : syracuseStep 4934717 = 1850519) (by norm_num)
theorem B3289811 : Blo 2191435 3289811 := bstep (se 1 (by rfl) ⟨2467358, by rfl⟩ : syracuseStep 3289811 = 4934717) B4934717
theorem B2193207 : Blo 2191435 2193207 := bstep (se 1 (by rfl) ⟨1644905, by rfl⟩ : syracuseStep 2193207 = 3289811) B3289811
theorem B3701045 : Blo 2191435 3701045 := bbase (se 5 (by rfl) ⟨173486, by rfl⟩ : syracuseStep 3701045 = 346973) (by norm_num)
theorem B2467363 : Blo 2191435 2467363 := bstep (se 1 (by rfl) ⟨1850522, by rfl⟩ : syracuseStep 2467363 = 3701045) B3701045
theorem B3289817 : Blo 2191435 3289817 := bstep (se 2 (by rfl) ⟨1233681, by rfl⟩ : syracuseStep 3289817 = 2467363) B2467363
theorem B2193211 : Blo 2191435 2193211 := bstep (se 1 (by rfl) ⟨1644908, by rfl⟩ : syracuseStep 2193211 = 3289817) B3289817
theorem B6245525 : Blo 2191435 6245525 := bbase (se 6 (by rfl) ⟨146379, by rfl⟩ : syracuseStep 6245525 = 292759) (by norm_num)
theorem B16654733 : Blo 2191435 16654733 := bstep (se 3 (by rfl) ⟨3122762, by rfl⟩ : syracuseStep 16654733 = 6245525) B6245525
theorem B11103155 : Blo 2191435 11103155 := bstep (se 1 (by rfl) ⟨8327366, by rfl⟩ : syracuseStep 11103155 = 16654733) B16654733
theorem B7402103 : Blo 2191435 7402103 := bstep (se 1 (by rfl) ⟨5551577, by rfl⟩ : syracuseStep 7402103 = 11103155) B11103155
theorem B4934735 : Blo 2191435 4934735 := bstep (se 1 (by rfl) ⟨3701051, by rfl⟩ : syracuseStep 4934735 = 7402103) B7402103
theorem B3289823 : Blo 2191435 3289823 := bstep (se 1 (by rfl) ⟨2467367, by rfl⟩ : syracuseStep 3289823 = 4934735) B4934735
theorem B2193215 : Blo 2191435 2193215 := bstep (se 1 (by rfl) ⟨1644911, by rfl⟩ : syracuseStep 2193215 = 3289823) B3289823
theorem B3289829 : Blo 2191435 3289829 := bbase (se 4 (by rfl) ⟨308421, by rfl⟩ : syracuseStep 3289829 = 616843) (by norm_num)
theorem B2193219 : Blo 2191435 2193219 := bstep (se 1 (by rfl) ⟨1644914, by rfl⟩ : syracuseStep 2193219 = 3289829) B3289829
theorem B2342081 : Blo 2191435 2342081 := bbase (se 2 (by rfl) ⟨878280, by rfl⟩ : syracuseStep 2342081 = 1756561) (by norm_num)
theorem B6245549 : Blo 2191435 6245549 := bstep (se 3 (by rfl) ⟨1171040, by rfl⟩ : syracuseStep 6245549 = 2342081) B2342081
theorem B4163699 : Blo 2191435 4163699 := bstep (se 1 (by rfl) ⟨3122774, by rfl⟩ : syracuseStep 4163699 = 6245549) B6245549
theorem B2775799 : Blo 2191435 2775799 := bstep (se 1 (by rfl) ⟨2081849, by rfl⟩ : syracuseStep 2775799 = 4163699) B4163699
theorem B3701065 : Blo 2191435 3701065 := bstep (se 2 (by rfl) ⟨1387899, by rfl⟩ : syracuseStep 3701065 = 2775799) B2775799
theorem B4934753 : Blo 2191435 4934753 := bstep (se 2 (by rfl) ⟨1850532, by rfl⟩ : syracuseStep 4934753 = 3701065) B3701065
theorem B3289835 : Blo 2191435 3289835 := bstep (se 1 (by rfl) ⟨2467376, by rfl⟩ : syracuseStep 3289835 = 4934753) B4934753
theorem B2193223 : Blo 2191435 2193223 := bstep (se 1 (by rfl) ⟨1644917, by rfl⟩ : syracuseStep 2193223 = 3289835) B3289835
theorem B2467381 : Blo 2191435 2467381 := bbase (se 5 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 2467381 = 231317) (by norm_num)
theorem B3289841 : Blo 2191435 3289841 := bstep (se 2 (by rfl) ⟨1233690, by rfl⟩ : syracuseStep 3289841 = 2467381) B2467381
theorem B2193227 : Blo 2191435 2193227 := bstep (se 1 (by rfl) ⟨1644920, by rfl⟩ : syracuseStep 2193227 = 3289841) B3289841
theorem B2775809 : Blo 2191435 2775809 := bbase (se 2 (by rfl) ⟨1040928, by rfl⟩ : syracuseStep 2775809 = 2081857) (by norm_num)
theorem B7402157 : Blo 2191435 7402157 := bstep (se 3 (by rfl) ⟨1387904, by rfl⟩ : syracuseStep 7402157 = 2775809) B2775809
theorem B4934771 : Blo 2191435 4934771 := bstep (se 1 (by rfl) ⟨3701078, by rfl⟩ : syracuseStep 4934771 = 7402157) B7402157
theorem B3289847 : Blo 2191435 3289847 := bstep (se 1 (by rfl) ⟨2467385, by rfl⟩ : syracuseStep 3289847 = 4934771) B4934771
theorem B2193231 : Blo 2191435 2193231 := bstep (se 1 (by rfl) ⟨1644923, by rfl⟩ : syracuseStep 2193231 = 3289847) B3289847
theorem B3289853 : Blo 2191435 3289853 := bbase (se 3 (by rfl) ⟨616847, by rfl⟩ : syracuseStep 3289853 = 1233695) (by norm_num)
theorem B2193235 : Blo 2191435 2193235 := bstep (se 1 (by rfl) ⟨1644926, by rfl⟩ : syracuseStep 2193235 = 3289853) B3289853
theorem B4934789 : Blo 2191435 4934789 := bbase (se 4 (by rfl) ⟨462636, by rfl⟩ : syracuseStep 4934789 = 925273) (by norm_num)
theorem B3289859 : Blo 2191435 3289859 := bstep (se 1 (by rfl) ⟨2467394, by rfl⟩ : syracuseStep 3289859 = 4934789) B4934789
theorem B2193239 : Blo 2191435 2193239 := bstep (se 1 (by rfl) ⟨1644929, by rfl⟩ : syracuseStep 2193239 = 3289859) B3289859
theorem B4684205 : Blo 2191435 4684205 := bbase (se 3 (by rfl) ⟨878288, by rfl⟩ : syracuseStep 4684205 = 1756577) (by norm_num)
theorem B3122803 : Blo 2191435 3122803 := bstep (se 1 (by rfl) ⟨2342102, by rfl⟩ : syracuseStep 3122803 = 4684205) B4684205
theorem B4163737 : Blo 2191435 4163737 := bstep (se 2 (by rfl) ⟨1561401, by rfl⟩ : syracuseStep 4163737 = 3122803) B3122803
theorem B5551649 : Blo 2191435 5551649 := bstep (se 2 (by rfl) ⟨2081868, by rfl⟩ : syracuseStep 5551649 = 4163737) B4163737
theorem B3701099 : Blo 2191435 3701099 := bstep (se 1 (by rfl) ⟨2775824, by rfl⟩ : syracuseStep 3701099 = 5551649) B5551649
theorem B2467399 : Blo 2191435 2467399 := bstep (se 1 (by rfl) ⟨1850549, by rfl⟩ : syracuseStep 2467399 = 3701099) B3701099
theorem B3289865 : Blo 2191435 3289865 := bstep (se 2 (by rfl) ⟨1233699, by rfl⟩ : syracuseStep 3289865 = 2467399) B2467399
theorem B2193243 : Blo 2191435 2193243 := bstep (se 1 (by rfl) ⟨1644932, by rfl⟩ : syracuseStep 2193243 = 3289865) B3289865
theorem B11103317 : Blo 2191435 11103317 := bbase (se 8 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 11103317 = 130117) (by norm_num)
theorem B7402211 : Blo 2191435 7402211 := bstep (se 1 (by rfl) ⟨5551658, by rfl⟩ : syracuseStep 7402211 = 11103317) B11103317
theorem B4934807 : Blo 2191435 4934807 := bstep (se 1 (by rfl) ⟨3701105, by rfl⟩ : syracuseStep 4934807 = 7402211) B7402211
theorem B3289871 : Blo 2191435 3289871 := bstep (se 1 (by rfl) ⟨2467403, by rfl⟩ : syracuseStep 3289871 = 4934807) B4934807
theorem B2193247 : Blo 2191435 2193247 := bstep (se 1 (by rfl) ⟨1644935, by rfl⟩ : syracuseStep 2193247 = 3289871) B3289871
theorem B3289877 : Blo 2191435 3289877 := bbase (se 6 (by rfl) ⟨77106, by rfl⟩ : syracuseStep 3289877 = 154213) (by norm_num)
theorem B2193251 : Blo 2191435 2193251 := bstep (se 1 (by rfl) ⟨1644938, by rfl⟩ : syracuseStep 2193251 = 3289877) B3289877
theorem B6009365 : Blo 2191435 6009365 := bbase (se 6 (by rfl) ⟨140844, by rfl⟩ : syracuseStep 6009365 = 281689) (by norm_num)
theorem B4006243 : Blo 2191435 4006243 := bstep (se 1 (by rfl) ⟨3004682, by rfl⟩ : syracuseStep 4006243 = 6009365) B6009365
theorem B21366629 : Blo 2191435 21366629 := bstep (se 4 (by rfl) ⟨2003121, by rfl⟩ : syracuseStep 21366629 = 4006243) B4006243
theorem B14244419 : Blo 2191435 14244419 := bstep (se 1 (by rfl) ⟨10683314, by rfl⟩ : syracuseStep 14244419 = 21366629) B21366629
theorem B9496279 : Blo 2191435 9496279 := bstep (se 1 (by rfl) ⟨7122209, by rfl⟩ : syracuseStep 9496279 = 14244419) B14244419
theorem B12661705 : Blo 2191435 12661705 := bstep (se 2 (by rfl) ⟨4748139, by rfl⟩ : syracuseStep 12661705 = 9496279) B9496279
theorem B16882273 : Blo 2191435 16882273 := bstep (se 2 (by rfl) ⟨6330852, by rfl⟩ : syracuseStep 16882273 = 12661705) B12661705
theorem B22509697 : Blo 2191435 22509697 := bstep (se 2 (by rfl) ⟨8441136, by rfl⟩ : syracuseStep 22509697 = 16882273) B16882273
theorem B30012929 : Blo 2191435 30012929 := bstep (se 2 (by rfl) ⟨11254848, by rfl⟩ : syracuseStep 30012929 = 22509697) B22509697
theorem B20008619 : Blo 2191435 20008619 := bstep (se 1 (by rfl) ⟨15006464, by rfl⟩ : syracuseStep 20008619 = 30012929) B30012929
theorem B13339079 : Blo 2191435 13339079 := bstep (se 1 (by rfl) ⟨10004309, by rfl⟩ : syracuseStep 13339079 = 20008619) B20008619
theorem B8892719 : Blo 2191435 8892719 := bstep (se 1 (by rfl) ⟨6669539, by rfl⟩ : syracuseStep 8892719 = 13339079) B13339079
theorem B5928479 : Blo 2191435 5928479 := bstep (se 1 (by rfl) ⟨4446359, by rfl⟩ : syracuseStep 5928479 = 8892719) B8892719
theorem B3952319 : Blo 2191435 3952319 := bstep (se 1 (by rfl) ⟨2964239, by rfl⟩ : syracuseStep 3952319 = 5928479) B5928479
theorem B42158069 : Blo 2191435 42158069 := bstep (se 5 (by rfl) ⟨1976159, by rfl⟩ : syracuseStep 42158069 = 3952319) B3952319
theorem B28105379 : Blo 2191435 28105379 := bstep (se 1 (by rfl) ⟨21079034, by rfl⟩ : syracuseStep 28105379 = 42158069) B42158069
theorem B18736919 : Blo 2191435 18736919 := bstep (se 1 (by rfl) ⟨14052689, by rfl⟩ : syracuseStep 18736919 = 28105379) B28105379
theorem B12491279 : Blo 2191435 12491279 := bstep (se 1 (by rfl) ⟨9368459, by rfl⟩ : syracuseStep 12491279 = 18736919) B18736919
theorem B8327519 : Blo 2191435 8327519 := bstep (se 1 (by rfl) ⟨6245639, by rfl⟩ : syracuseStep 8327519 = 12491279) B12491279
theorem B5551679 : Blo 2191435 5551679 := bstep (se 1 (by rfl) ⟨4163759, by rfl⟩ : syracuseStep 5551679 = 8327519) B8327519
theorem B3701119 : Blo 2191435 3701119 := bstep (se 1 (by rfl) ⟨2775839, by rfl⟩ : syracuseStep 3701119 = 5551679) B5551679
theorem B4934825 : Blo 2191435 4934825 := bstep (se 2 (by rfl) ⟨1850559, by rfl⟩ : syracuseStep 4934825 = 3701119) B3701119
theorem B3289883 : Blo 2191435 3289883 := bstep (se 1 (by rfl) ⟨2467412, by rfl⟩ : syracuseStep 3289883 = 4934825) B4934825
theorem B2193255 : Blo 2191435 2193255 := bstep (se 1 (by rfl) ⟨1644941, by rfl⟩ : syracuseStep 2193255 = 3289883) B3289883
theorem B2467417 : Blo 2191435 2467417 := bbase (se 2 (by rfl) ⟨925281, by rfl⟩ : syracuseStep 2467417 = 1850563) (by norm_num)
theorem B3289889 : Blo 2191435 3289889 := bstep (se 2 (by rfl) ⟨1233708, by rfl⟩ : syracuseStep 3289889 = 2467417) B2467417
theorem B2193259 : Blo 2191435 2193259 := bstep (se 1 (by rfl) ⟨1644944, by rfl⟩ : syracuseStep 2193259 = 3289889) B3289889
theorem B10539557 : Blo 2191435 10539557 := bbase (se 4 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 10539557 = 1976167) (by norm_num)
theorem B7026371 : Blo 2191435 7026371 := bstep (se 1 (by rfl) ⟨5269778, by rfl⟩ : syracuseStep 7026371 = 10539557) B10539557
theorem B4684247 : Blo 2191435 4684247 := bstep (se 1 (by rfl) ⟨3513185, by rfl⟩ : syracuseStep 4684247 = 7026371) B7026371
theorem B3122831 : Blo 2191435 3122831 := bstep (se 1 (by rfl) ⟨2342123, by rfl⟩ : syracuseStep 3122831 = 4684247) B4684247
theorem B8327549 : Blo 2191435 8327549 := bstep (se 3 (by rfl) ⟨1561415, by rfl⟩ : syracuseStep 8327549 = 3122831) B3122831
theorem B5551699 : Blo 2191435 5551699 := bstep (se 1 (by rfl) ⟨4163774, by rfl⟩ : syracuseStep 5551699 = 8327549) B8327549
theorem B7402265 : Blo 2191435 7402265 := bstep (se 2 (by rfl) ⟨2775849, by rfl⟩ : syracuseStep 7402265 = 5551699) B5551699
theorem B4934843 : Blo 2191435 4934843 := bstep (se 1 (by rfl) ⟨3701132, by rfl⟩ : syracuseStep 4934843 = 7402265) B7402265
theorem B3289895 : Blo 2191435 3289895 := bstep (se 1 (by rfl) ⟨2467421, by rfl⟩ : syracuseStep 3289895 = 4934843) B4934843
theorem B2193263 : Blo 2191435 2193263 := bstep (se 1 (by rfl) ⟨1644947, by rfl⟩ : syracuseStep 2193263 = 3289895) B3289895
theorem B3289901 : Blo 2191435 3289901 := bbase (se 3 (by rfl) ⟨616856, by rfl⟩ : syracuseStep 3289901 = 1233713) (by norm_num)
theorem B2193267 : Blo 2191435 2193267 := bstep (se 1 (by rfl) ⟨1644950, by rfl⟩ : syracuseStep 2193267 = 3289901) B3289901
theorem B4934861 : Blo 2191435 4934861 := bbase (se 3 (by rfl) ⟨925286, by rfl⟩ : syracuseStep 4934861 = 1850573) (by norm_num)
theorem B3289907 : Blo 2191435 3289907 := bstep (se 1 (by rfl) ⟨2467430, by rfl⟩ : syracuseStep 3289907 = 4934861) B4934861
theorem B2193271 : Blo 2191435 2193271 := bstep (se 1 (by rfl) ⟨1644953, by rfl⟩ : syracuseStep 2193271 = 3289907) B3289907
theorem B2775865 : Blo 2191435 2775865 := bbase (se 2 (by rfl) ⟨1040949, by rfl⟩ : syracuseStep 2775865 = 2081899) (by norm_num)
theorem B3701153 : Blo 2191435 3701153 := bstep (se 2 (by rfl) ⟨1387932, by rfl⟩ : syracuseStep 3701153 = 2775865) B2775865
theorem B2467435 : Blo 2191435 2467435 := bstep (se 1 (by rfl) ⟨1850576, by rfl⟩ : syracuseStep 2467435 = 3701153) B3701153
theorem B3289913 : Blo 2191435 3289913 := bstep (se 2 (by rfl) ⟨1233717, by rfl⟩ : syracuseStep 3289913 = 2467435) B2467435
theorem B2193275 : Blo 2191435 2193275 := bstep (se 1 (by rfl) ⟨1644956, by rfl⟩ : syracuseStep 2193275 = 3289913) B3289913
theorem B7026421 : Blo 2191435 7026421 := bbase (se 5 (by rfl) ⟨329363, by rfl⟩ : syracuseStep 7026421 = 658727) (by norm_num)
theorem B9368561 : Blo 2191435 9368561 := bstep (se 2 (by rfl) ⟨3513210, by rfl⟩ : syracuseStep 9368561 = 7026421) B7026421
theorem B24982829 : Blo 2191435 24982829 := bstep (se 3 (by rfl) ⟨4684280, by rfl⟩ : syracuseStep 24982829 = 9368561) B9368561
theorem B16655219 : Blo 2191435 16655219 := bstep (se 1 (by rfl) ⟨12491414, by rfl⟩ : syracuseStep 16655219 = 24982829) B24982829
theorem B11103479 : Blo 2191435 11103479 := bstep (se 1 (by rfl) ⟨8327609, by rfl⟩ : syracuseStep 11103479 = 16655219) B16655219
theorem B7402319 : Blo 2191435 7402319 := bstep (se 1 (by rfl) ⟨5551739, by rfl⟩ : syracuseStep 7402319 = 11103479) B11103479
theorem B4934879 : Blo 2191435 4934879 := bstep (se 1 (by rfl) ⟨3701159, by rfl⟩ : syracuseStep 4934879 = 7402319) B7402319
theorem B3289919 : Blo 2191435 3289919 := bstep (se 1 (by rfl) ⟨2467439, by rfl⟩ : syracuseStep 3289919 = 4934879) B4934879
theorem B2193279 : Blo 2191435 2193279 := bstep (se 1 (by rfl) ⟨1644959, by rfl⟩ : syracuseStep 2193279 = 3289919) B3289919
theorem B3289925 : Blo 2191435 3289925 := bbase (se 4 (by rfl) ⟨308430, by rfl⟩ : syracuseStep 3289925 = 616861) (by norm_num)
theorem B2193283 : Blo 2191435 2193283 := bstep (se 1 (by rfl) ⟨1644962, by rfl⟩ : syracuseStep 2193283 = 3289925) B3289925
theorem B3701173 : Blo 2191435 3701173 := bbase (se 5 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 3701173 = 346985) (by norm_num)
theorem B4934897 : Blo 2191435 4934897 := bstep (se 2 (by rfl) ⟨1850586, by rfl⟩ : syracuseStep 4934897 = 3701173) B3701173
theorem B3289931 : Blo 2191435 3289931 := bstep (se 1 (by rfl) ⟨2467448, by rfl⟩ : syracuseStep 3289931 = 4934897) B4934897
theorem B2193287 : Blo 2191435 2193287 := bstep (se 1 (by rfl) ⟨1644965, by rfl⟩ : syracuseStep 2193287 = 3289931) B3289931
theorem B2467453 : Blo 2191435 2467453 := bbase (se 3 (by rfl) ⟨462647, by rfl⟩ : syracuseStep 2467453 = 925295) (by norm_num)
theorem B3289937 : Blo 2191435 3289937 := bstep (se 2 (by rfl) ⟨1233726, by rfl⟩ : syracuseStep 3289937 = 2467453) B2467453
theorem B2193291 : Blo 2191435 2193291 := bstep (se 1 (by rfl) ⟨1644968, by rfl⟩ : syracuseStep 2193291 = 3289937) B3289937
theorem B7402373 : Blo 2191435 7402373 := bbase (se 4 (by rfl) ⟨693972, by rfl⟩ : syracuseStep 7402373 = 1387945) (by norm_num)
theorem B4934915 : Blo 2191435 4934915 := bstep (se 1 (by rfl) ⟨3701186, by rfl⟩ : syracuseStep 4934915 = 7402373) B7402373
theorem B3289943 : Blo 2191435 3289943 := bstep (se 1 (by rfl) ⟨2467457, by rfl⟩ : syracuseStep 3289943 = 4934915) B4934915
theorem B2193295 : Blo 2191435 2193295 := bstep (se 1 (by rfl) ⟨1644971, by rfl⟩ : syracuseStep 2193295 = 3289943) B3289943
theorem B3289949 : Blo 2191435 3289949 := bbase (se 3 (by rfl) ⟨616865, by rfl⟩ : syracuseStep 3289949 = 1233731) (by norm_num)
theorem B2193299 : Blo 2191435 2193299 := bstep (se 1 (by rfl) ⟨1644974, by rfl⟩ : syracuseStep 2193299 = 3289949) B3289949
theorem B4934933 : Blo 2191435 4934933 := bbase (se 6 (by rfl) ⟨115662, by rfl⟩ : syracuseStep 4934933 = 231325) (by norm_num)
theorem B3289955 : Blo 2191435 3289955 := bstep (se 1 (by rfl) ⟨2467466, by rfl⟩ : syracuseStep 3289955 = 4934933) B4934933
theorem B2193303 : Blo 2191435 2193303 := bstep (se 1 (by rfl) ⟨1644977, by rfl⟩ : syracuseStep 2193303 = 3289955) B3289955
theorem B8327717 : Blo 2191435 8327717 := bbase (se 4 (by rfl) ⟨780723, by rfl⟩ : syracuseStep 8327717 = 1561447) (by norm_num)
theorem B5551811 : Blo 2191435 5551811 := bstep (se 1 (by rfl) ⟨4163858, by rfl⟩ : syracuseStep 5551811 = 8327717) B8327717
theorem B3701207 : Blo 2191435 3701207 := bstep (se 1 (by rfl) ⟨2775905, by rfl⟩ : syracuseStep 3701207 = 5551811) B5551811
theorem B2467471 : Blo 2191435 2467471 := bstep (se 1 (by rfl) ⟨1850603, by rfl⟩ : syracuseStep 2467471 = 3701207) B3701207
theorem B3289961 : Blo 2191435 3289961 := bstep (se 2 (by rfl) ⟨1233735, by rfl⟩ : syracuseStep 3289961 = 2467471) B2467471
theorem B2193307 : Blo 2191435 2193307 := bstep (se 1 (by rfl) ⟨1644980, by rfl⟩ : syracuseStep 2193307 = 3289961) B3289961
theorem B4684349 : Blo 2191435 4684349 := bbase (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) (by norm_num)
theorem B12491597 : Blo 2191435 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B8327731 : Blo 2191435 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B11103641 : Blo 2191435 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B7402427 : Blo 2191435 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B4934951 : Blo 2191435 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B3289967 : Blo 2191435 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B2193311 : Blo 2191435 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B3289973 : Blo 2191435 3289973 := bbase (se 5 (by rfl) ⟨154217, by rfl⟩ : syracuseStep 3289973 = 308435) (by norm_num)
theorem B2193315 : Blo 2191435 2193315 := bstep (se 1 (by rfl) ⟨1644986, by rfl⟩ : syracuseStep 2193315 = 3289973) B3289973
theorem B2223245 : Blo 2191435 2223245 := bbase (se 3 (by rfl) ⟨416858, by rfl⟩ : syracuseStep 2223245 = 833717) (by norm_num)
theorem B5928653 : Blo 2191435 5928653 := bstep (se 3 (by rfl) ⟨1111622, by rfl⟩ : syracuseStep 5928653 = 2223245) B2223245
theorem B15809741 : Blo 2191435 15809741 := bstep (se 3 (by rfl) ⟨2964326, by rfl⟩ : syracuseStep 15809741 = 5928653) B5928653
theorem B10539827 : Blo 2191435 10539827 := bstep (se 1 (by rfl) ⟨7904870, by rfl⟩ : syracuseStep 10539827 = 15809741) B15809741
theorem B7026551 : Blo 2191435 7026551 := bstep (se 1 (by rfl) ⟨5269913, by rfl⟩ : syracuseStep 7026551 = 10539827) B10539827
theorem B4684367 : Blo 2191435 4684367 := bstep (se 1 (by rfl) ⟨3513275, by rfl⟩ : syracuseStep 4684367 = 7026551) B7026551
theorem B3122911 : Blo 2191435 3122911 := bstep (se 1 (by rfl) ⟨2342183, by rfl⟩ : syracuseStep 3122911 = 4684367) B4684367
theorem B4163881 : Blo 2191435 4163881 := bstep (se 2 (by rfl) ⟨1561455, by rfl⟩ : syracuseStep 4163881 = 3122911) B3122911
theorem B5551841 : Blo 2191435 5551841 := bstep (se 2 (by rfl) ⟨2081940, by rfl⟩ : syracuseStep 5551841 = 4163881) B4163881
theorem B3701227 : Blo 2191435 3701227 := bstep (se 1 (by rfl) ⟨2775920, by rfl⟩ : syracuseStep 3701227 = 5551841) B5551841
theorem B4934969 : Blo 2191435 4934969 := bstep (se 2 (by rfl) ⟨1850613, by rfl⟩ : syracuseStep 4934969 = 3701227) B3701227
theorem B3289979 : Blo 2191435 3289979 := bstep (se 1 (by rfl) ⟨2467484, by rfl⟩ : syracuseStep 3289979 = 4934969) B4934969
theorem B2193319 : Blo 2191435 2193319 := bstep (se 1 (by rfl) ⟨1644989, by rfl⟩ : syracuseStep 2193319 = 3289979) B3289979
theorem B2467489 : Blo 2191435 2467489 := bbase (se 2 (by rfl) ⟨925308, by rfl⟩ : syracuseStep 2467489 = 1850617) (by norm_num)
theorem B3289985 : Blo 2191435 3289985 := bstep (se 2 (by rfl) ⟨1233744, by rfl⟩ : syracuseStep 3289985 = 2467489) B2467489
theorem B2193323 : Blo 2191435 2193323 := bstep (se 1 (by rfl) ⟨1644992, by rfl⟩ : syracuseStep 2193323 = 3289985) B3289985
theorem B5551861 : Blo 2191435 5551861 := bbase (se 5 (by rfl) ⟨260243, by rfl⟩ : syracuseStep 5551861 = 520487) (by norm_num)
theorem B7402481 : Blo 2191435 7402481 := bstep (se 2 (by rfl) ⟨2775930, by rfl⟩ : syracuseStep 7402481 = 5551861) B5551861
theorem B4934987 : Blo 2191435 4934987 := bstep (se 1 (by rfl) ⟨3701240, by rfl⟩ : syracuseStep 4934987 = 7402481) B7402481
theorem B3289991 : Blo 2191435 3289991 := bstep (se 1 (by rfl) ⟨2467493, by rfl⟩ : syracuseStep 3289991 = 4934987) B4934987
theorem B2193327 : Blo 2191435 2193327 := bstep (se 1 (by rfl) ⟨1644995, by rfl⟩ : syracuseStep 2193327 = 3289991) B3289991
theorem B3289997 : Blo 2191435 3289997 := bbase (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) (by norm_num)
theorem B2193331 : Blo 2191435 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B4935005 : Blo 2191435 4935005 := bbase (se 3 (by rfl) ⟨925313, by rfl⟩ : syracuseStep 4935005 = 1850627) (by norm_num)
theorem B3290003 : Blo 2191435 3290003 := bstep (se 1 (by rfl) ⟨2467502, by rfl⟩ : syracuseStep 3290003 = 4935005) B4935005
theorem B2193335 : Blo 2191435 2193335 := bstep (se 1 (by rfl) ⟨1645001, by rfl⟩ : syracuseStep 2193335 = 3290003) B3290003
theorem B3701261 : Blo 2191435 3701261 := bbase (se 3 (by rfl) ⟨693986, by rfl⟩ : syracuseStep 3701261 = 1387973) (by norm_num)
theorem B2467507 : Blo 2191435 2467507 := bstep (se 1 (by rfl) ⟨1850630, by rfl⟩ : syracuseStep 2467507 = 3701261) B3701261
theorem B3290009 : Blo 2191435 3290009 := bstep (se 2 (by rfl) ⟨1233753, by rfl⟩ : syracuseStep 3290009 = 2467507) B2467507
theorem B2193339 : Blo 2191435 2193339 := bstep (se 1 (by rfl) ⟨1645004, by rfl⟩ : syracuseStep 2193339 = 3290009) B3290009
theorem B2634985 : Blo 2191435 2634985 := bbase (se 2 (by rfl) ⟨988119, by rfl⟩ : syracuseStep 2634985 = 1976239) (by norm_num)
theorem B3513313 : Blo 2191435 3513313 := bstep (se 2 (by rfl) ⟨1317492, by rfl⟩ : syracuseStep 3513313 = 2634985) B2634985
theorem B18737669 : Blo 2191435 18737669 := bstep (se 4 (by rfl) ⟨1756656, by rfl⟩ : syracuseStep 18737669 = 3513313) B3513313
theorem B12491779 : Blo 2191435 12491779 := bstep (se 1 (by rfl) ⟨9368834, by rfl⟩ : syracuseStep 12491779 = 18737669) B18737669
theorem B16655705 : Blo 2191435 16655705 := bstep (se 2 (by rfl) ⟨6245889, by rfl⟩ : syracuseStep 16655705 = 12491779) B12491779
theorem B11103803 : Blo 2191435 11103803 := bstep (se 1 (by rfl) ⟨8327852, by rfl⟩ : syracuseStep 11103803 = 16655705) B16655705
theorem B7402535 : Blo 2191435 7402535 := bstep (se 1 (by rfl) ⟨5551901, by rfl⟩ : syracuseStep 7402535 = 11103803) B11103803
theorem B4935023 : Blo 2191435 4935023 := bstep (se 1 (by rfl) ⟨3701267, by rfl⟩ : syracuseStep 4935023 = 7402535) B7402535
theorem B3290015 : Blo 2191435 3290015 := bstep (se 1 (by rfl) ⟨2467511, by rfl⟩ : syracuseStep 3290015 = 4935023) B4935023
theorem B2193343 : Blo 2191435 2193343 := bstep (se 1 (by rfl) ⟨1645007, by rfl⟩ : syracuseStep 2193343 = 3290015) B3290015
theorem B3290021 : Blo 2191435 3290021 := bbase (se 4 (by rfl) ⟨308439, by rfl⟩ : syracuseStep 3290021 = 616879) (by norm_num)
theorem B2193347 : Blo 2191435 2193347 := bstep (se 1 (by rfl) ⟨1645010, by rfl⟩ : syracuseStep 2193347 = 3290021) B3290021
theorem B2775961 : Blo 2191435 2775961 := bbase (se 2 (by rfl) ⟨1040985, by rfl⟩ : syracuseStep 2775961 = 2081971) (by norm_num)
theorem B3701281 : Blo 2191435 3701281 := bstep (se 2 (by rfl) ⟨1387980, by rfl⟩ : syracuseStep 3701281 = 2775961) B2775961
theorem B4935041 : Blo 2191435 4935041 := bstep (se 2 (by rfl) ⟨1850640, by rfl⟩ : syracuseStep 4935041 = 3701281) B3701281
theorem B3290027 : Blo 2191435 3290027 := bstep (se 1 (by rfl) ⟨2467520, by rfl⟩ : syracuseStep 3290027 = 4935041) B4935041
theorem B2193351 : Blo 2191435 2193351 := bstep (se 1 (by rfl) ⟨1645013, by rfl⟩ : syracuseStep 2193351 = 3290027) B3290027
theorem B2467525 : Blo 2191435 2467525 := bbase (se 4 (by rfl) ⟨231330, by rfl⟩ : syracuseStep 2467525 = 462661) (by norm_num)
theorem B3290033 : Blo 2191435 3290033 := bstep (se 2 (by rfl) ⟨1233762, by rfl⟩ : syracuseStep 3290033 = 2467525) B2467525
theorem B2193355 : Blo 2191435 2193355 := bstep (se 1 (by rfl) ⟨1645016, by rfl⟩ : syracuseStep 2193355 = 3290033) B3290033
theorem B4163957 : Blo 2191435 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B2775971 : Blo 2191435 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B7402589 : Blo 2191435 7402589 := bstep (se 3 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 7402589 = 2775971) B2775971
theorem B4935059 : Blo 2191435 4935059 := bstep (se 1 (by rfl) ⟨3701294, by rfl⟩ : syracuseStep 4935059 = 7402589) B7402589
theorem B3290039 : Blo 2191435 3290039 := bstep (se 1 (by rfl) ⟨2467529, by rfl⟩ : syracuseStep 3290039 = 4935059) B4935059
theorem B2193359 : Blo 2191435 2193359 := bstep (se 1 (by rfl) ⟨1645019, by rfl⟩ : syracuseStep 2193359 = 3290039) B3290039
theorem B3290045 : Blo 2191435 3290045 := bbase (se 3 (by rfl) ⟨616883, by rfl⟩ : syracuseStep 3290045 = 1233767) (by norm_num)
theorem B2193363 : Blo 2191435 2193363 := bstep (se 1 (by rfl) ⟨1645022, by rfl⟩ : syracuseStep 2193363 = 3290045) B3290045
theorem B4935077 : Blo 2191435 4935077 := bbase (se 4 (by rfl) ⟨462663, by rfl⟩ : syracuseStep 4935077 = 925327) (by norm_num)
theorem B3290051 : Blo 2191435 3290051 := bstep (se 1 (by rfl) ⟨2467538, by rfl⟩ : syracuseStep 3290051 = 4935077) B4935077
theorem B2193367 : Blo 2191435 2193367 := bstep (se 1 (by rfl) ⟨1645025, by rfl⟩ : syracuseStep 2193367 = 3290051) B3290051
theorem B5551973 : Blo 2191435 5551973 := bbase (se 4 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 5551973 = 1040995) (by norm_num)
theorem B3701315 : Blo 2191435 3701315 := bstep (se 1 (by rfl) ⟨2775986, by rfl⟩ : syracuseStep 3701315 = 5551973) B5551973
theorem B2467543 : Blo 2191435 2467543 := bstep (se 1 (by rfl) ⟨1850657, by rfl⟩ : syracuseStep 2467543 = 3701315) B3701315
theorem B3290057 : Blo 2191435 3290057 := bstep (se 2 (by rfl) ⟨1233771, by rfl⟩ : syracuseStep 3290057 = 2467543) B2467543
theorem B2193371 : Blo 2191435 2193371 := bstep (se 1 (by rfl) ⟨1645028, by rfl⟩ : syracuseStep 2193371 = 3290057) B3290057
theorem B3513365 : Blo 2191435 3513365 := bbase (se 6 (by rfl) ⟨82344, by rfl⟩ : syracuseStep 3513365 = 164689) (by norm_num)
theorem B2342243 : Blo 2191435 2342243 := bstep (se 1 (by rfl) ⟨1756682, by rfl⟩ : syracuseStep 2342243 = 3513365) B3513365
theorem B6245981 : Blo 2191435 6245981 := bstep (se 3 (by rfl) ⟨1171121, by rfl⟩ : syracuseStep 6245981 = 2342243) B2342243
theorem B4163987 : Blo 2191435 4163987 := bstep (se 1 (by rfl) ⟨3122990, by rfl⟩ : syracuseStep 4163987 = 6245981) B6245981
theorem B11103965 : Blo 2191435 11103965 := bstep (se 3 (by rfl) ⟨2081993, by rfl⟩ : syracuseStep 11103965 = 4163987) B4163987
theorem B7402643 : Blo 2191435 7402643 := bstep (se 1 (by rfl) ⟨5551982, by rfl⟩ : syracuseStep 7402643 = 11103965) B11103965
theorem B4935095 : Blo 2191435 4935095 := bstep (se 1 (by rfl) ⟨3701321, by rfl⟩ : syracuseStep 4935095 = 7402643) B7402643
theorem B3290063 : Blo 2191435 3290063 := bstep (se 1 (by rfl) ⟨2467547, by rfl⟩ : syracuseStep 3290063 = 4935095) B4935095
theorem B2193375 : Blo 2191435 2193375 := bstep (se 1 (by rfl) ⟨1645031, by rfl⟩ : syracuseStep 2193375 = 3290063) B3290063
theorem B3290069 : Blo 2191435 3290069 := bbase (se 7 (by rfl) ⟨38555, by rfl⟩ : syracuseStep 3290069 = 77111) (by norm_num)
theorem B2193379 : Blo 2191435 2193379 := bstep (se 1 (by rfl) ⟨1645034, by rfl⟩ : syracuseStep 2193379 = 3290069) B3290069
theorem B8328005 : Blo 2191435 8328005 := bbase (se 4 (by rfl) ⟨780750, by rfl⟩ : syracuseStep 8328005 = 1561501) (by norm_num)
theorem B5552003 : Blo 2191435 5552003 := bstep (se 1 (by rfl) ⟨4164002, by rfl⟩ : syracuseStep 5552003 = 8328005) B8328005
theorem B3701335 : Blo 2191435 3701335 := bstep (se 1 (by rfl) ⟨2776001, by rfl⟩ : syracuseStep 3701335 = 5552003) B5552003
theorem B4935113 : Blo 2191435 4935113 := bstep (se 2 (by rfl) ⟨1850667, by rfl⟩ : syracuseStep 4935113 = 3701335) B3701335
theorem B3290075 : Blo 2191435 3290075 := bstep (se 1 (by rfl) ⟨2467556, by rfl⟩ : syracuseStep 3290075 = 4935113) B4935113
theorem B2193383 : Blo 2191435 2193383 := bstep (se 1 (by rfl) ⟨1645037, by rfl⟩ : syracuseStep 2193383 = 3290075) B3290075
theorem B2467561 : Blo 2191435 2467561 := bbase (se 2 (by rfl) ⟨925335, by rfl⟩ : syracuseStep 2467561 = 1850671) (by norm_num)
theorem B3290081 : Blo 2191435 3290081 := bstep (se 2 (by rfl) ⟨1233780, by rfl⟩ : syracuseStep 3290081 = 2467561) B2467561
theorem B2193387 : Blo 2191435 2193387 := bstep (se 1 (by rfl) ⟨1645040, by rfl⟩ : syracuseStep 2193387 = 3290081) B3290081
theorem B12492053 : Blo 2191435 12492053 := bbase (se 6 (by rfl) ⟨292782, by rfl⟩ : syracuseStep 12492053 = 585565) (by norm_num)
theorem B8328035 : Blo 2191435 8328035 := bstep (se 1 (by rfl) ⟨6246026, by rfl⟩ : syracuseStep 8328035 = 12492053) B12492053
theorem B5552023 : Blo 2191435 5552023 := bstep (se 1 (by rfl) ⟨4164017, by rfl⟩ : syracuseStep 5552023 = 8328035) B8328035
theorem B7402697 : Blo 2191435 7402697 := bstep (se 2 (by rfl) ⟨2776011, by rfl⟩ : syracuseStep 7402697 = 5552023) B5552023
theorem B4935131 : Blo 2191435 4935131 := bstep (se 1 (by rfl) ⟨3701348, by rfl⟩ : syracuseStep 4935131 = 7402697) B7402697
theorem B3290087 : Blo 2191435 3290087 := bstep (se 1 (by rfl) ⟨2467565, by rfl⟩ : syracuseStep 3290087 = 4935131) B4935131
theorem B2193391 : Blo 2191435 2193391 := bstep (se 1 (by rfl) ⟨1645043, by rfl⟩ : syracuseStep 2193391 = 3290087) B3290087
theorem B3290093 : Blo 2191435 3290093 := bbase (se 3 (by rfl) ⟨616892, by rfl⟩ : syracuseStep 3290093 = 1233785) (by norm_num)
theorem B2193395 : Blo 2191435 2193395 := bstep (se 1 (by rfl) ⟨1645046, by rfl⟩ : syracuseStep 2193395 = 3290093) B3290093
theorem B4935149 : Blo 2191435 4935149 := bbase (se 3 (by rfl) ⟨925340, by rfl⟩ : syracuseStep 4935149 = 1850681) (by norm_num)
theorem B3290099 : Blo 2191435 3290099 := bstep (se 1 (by rfl) ⟨2467574, by rfl⟩ : syracuseStep 3290099 = 4935149) B4935149
theorem B2193399 : Blo 2191435 2193399 := bstep (se 1 (by rfl) ⟨1645049, by rfl⟩ : syracuseStep 2193399 = 3290099) B3290099
theorem B7026821 : Blo 2191435 7026821 := bbase (se 4 (by rfl) ⟨658764, by rfl⟩ : syracuseStep 7026821 = 1317529) (by norm_num)
theorem B4684547 : Blo 2191435 4684547 := bstep (se 1 (by rfl) ⟨3513410, by rfl⟩ : syracuseStep 4684547 = 7026821) B7026821
theorem B3123031 : Blo 2191435 3123031 := bstep (se 1 (by rfl) ⟨2342273, by rfl⟩ : syracuseStep 3123031 = 4684547) B4684547
theorem B4164041 : Blo 2191435 4164041 := bstep (se 2 (by rfl) ⟨1561515, by rfl⟩ : syracuseStep 4164041 = 3123031) B3123031
theorem B2776027 : Blo 2191435 2776027 := bstep (se 1 (by rfl) ⟨2082020, by rfl⟩ : syracuseStep 2776027 = 4164041) B4164041
theorem B3701369 : Blo 2191435 3701369 := bstep (se 2 (by rfl) ⟨1388013, by rfl⟩ : syracuseStep 3701369 = 2776027) B2776027
theorem B2467579 : Blo 2191435 2467579 := bstep (se 1 (by rfl) ⟨1850684, by rfl⟩ : syracuseStep 2467579 = 3701369) B3701369
theorem B3290105 : Blo 2191435 3290105 := bstep (se 2 (by rfl) ⟨1233789, by rfl⟩ : syracuseStep 3290105 = 2467579) B2467579
theorem B2193403 : Blo 2191435 2193403 := bstep (se 1 (by rfl) ⟨1645052, by rfl⟩ : syracuseStep 2193403 = 3290105) B3290105
theorem B8893333 : Blo 2191435 8893333 := bbase (se 6 (by rfl) ⟨208437, by rfl⟩ : syracuseStep 8893333 = 416875) (by norm_num)
theorem B47431109 : Blo 2191435 47431109 := bstep (se 4 (by rfl) ⟨4446666, by rfl⟩ : syracuseStep 47431109 = 8893333) B8893333
theorem B126482957 : Blo 2191435 126482957 := bstep (se 3 (by rfl) ⟨23715554, by rfl⟩ : syracuseStep 126482957 = 47431109) B47431109
theorem B84321971 : Blo 2191435 84321971 := bstep (se 1 (by rfl) ⟨63241478, by rfl⟩ : syracuseStep 84321971 = 126482957) B126482957
theorem B56214647 : Blo 2191435 56214647 := bstep (se 1 (by rfl) ⟨42160985, by rfl⟩ : syracuseStep 56214647 = 84321971) B84321971
theorem B37476431 : Blo 2191435 37476431 := bstep (se 1 (by rfl) ⟨28107323, by rfl⟩ : syracuseStep 37476431 = 56214647) B56214647
theorem B24984287 : Blo 2191435 24984287 := bstep (se 1 (by rfl) ⟨18738215, by rfl⟩ : syracuseStep 24984287 = 37476431) B37476431
theorem B16656191 : Blo 2191435 16656191 := bstep (se 1 (by rfl) ⟨12492143, by rfl⟩ : syracuseStep 16656191 = 24984287) B24984287
theorem B11104127 : Blo 2191435 11104127 := bstep (se 1 (by rfl) ⟨8328095, by rfl⟩ : syracuseStep 11104127 = 16656191) B16656191
theorem B7402751 : Blo 2191435 7402751 := bstep (se 1 (by rfl) ⟨5552063, by rfl⟩ : syracuseStep 7402751 = 11104127) B11104127
theorem B4935167 : Blo 2191435 4935167 := bstep (se 1 (by rfl) ⟨3701375, by rfl⟩ : syracuseStep 4935167 = 7402751) B7402751
theorem B3290111 : Blo 2191435 3290111 := bstep (se 1 (by rfl) ⟨2467583, by rfl⟩ : syracuseStep 3290111 = 4935167) B4935167
theorem B2193407 : Blo 2191435 2193407 := bstep (se 1 (by rfl) ⟨1645055, by rfl⟩ : syracuseStep 2193407 = 3290111) B3290111
theorem B3290117 : Blo 2191435 3290117 := bbase (se 4 (by rfl) ⟨308448, by rfl⟩ : syracuseStep 3290117 = 616897) (by norm_num)
theorem B2193411 : Blo 2191435 2193411 := bstep (se 1 (by rfl) ⟨1645058, by rfl⟩ : syracuseStep 2193411 = 3290117) B3290117
theorem B3701389 : Blo 2191435 3701389 := bbase (se 3 (by rfl) ⟨694010, by rfl⟩ : syracuseStep 3701389 = 1388021) (by norm_num)
theorem B4935185 : Blo 2191435 4935185 := bstep (se 2 (by rfl) ⟨1850694, by rfl⟩ : syracuseStep 4935185 = 3701389) B3701389
theorem B3290123 : Blo 2191435 3290123 := bstep (se 1 (by rfl) ⟨2467592, by rfl⟩ : syracuseStep 3290123 = 4935185) B4935185
theorem B2193415 : Blo 2191435 2193415 := bstep (se 1 (by rfl) ⟨1645061, by rfl⟩ : syracuseStep 2193415 = 3290123) B3290123
theorem B2467597 : Blo 2191435 2467597 := bbase (se 3 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 2467597 = 925349) (by norm_num)
theorem B3290129 : Blo 2191435 3290129 := bstep (se 2 (by rfl) ⟨1233798, by rfl⟩ : syracuseStep 3290129 = 2467597) B2467597
theorem B2193419 : Blo 2191435 2193419 := bstep (se 1 (by rfl) ⟨1645064, by rfl⟩ : syracuseStep 2193419 = 3290129) B3290129
theorem B7402805 : Blo 2191435 7402805 := bbase (se 5 (by rfl) ⟨347006, by rfl⟩ : syracuseStep 7402805 = 694013) (by norm_num)
theorem B4935203 : Blo 2191435 4935203 := bstep (se 1 (by rfl) ⟨3701402, by rfl⟩ : syracuseStep 4935203 = 7402805) B7402805
theorem B3290135 : Blo 2191435 3290135 := bstep (se 1 (by rfl) ⟨2467601, by rfl⟩ : syracuseStep 3290135 = 4935203) B4935203
theorem B2193423 : Blo 2191435 2193423 := bstep (se 1 (by rfl) ⟨1645067, by rfl⟩ : syracuseStep 2193423 = 3290135) B3290135
theorem B3290141 : Blo 2191435 3290141 := bbase (se 3 (by rfl) ⟨616901, by rfl⟩ : syracuseStep 3290141 = 1233803) (by norm_num)
theorem B2193427 : Blo 2191435 2193427 := bstep (se 1 (by rfl) ⟨1645070, by rfl⟩ : syracuseStep 2193427 = 3290141) B3290141
theorem B4935221 : Blo 2191435 4935221 := bbase (se 5 (by rfl) ⟨231338, by rfl⟩ : syracuseStep 4935221 = 462677) (by norm_num)
theorem B3290147 : Blo 2191435 3290147 := bstep (se 1 (by rfl) ⟨2467610, by rfl⟩ : syracuseStep 3290147 = 4935221) B4935221
theorem B2193431 : Blo 2191435 2193431 := bstep (se 1 (by rfl) ⟨1645073, by rfl⟩ : syracuseStep 2193431 = 3290147) B3290147
theorem B3513461 : Blo 2191435 3513461 := bbase (se 5 (by rfl) ⟨164693, by rfl⟩ : syracuseStep 3513461 = 329387) (by norm_num)
theorem B9369229 : Blo 2191435 9369229 := bstep (se 3 (by rfl) ⟨1756730, by rfl⟩ : syracuseStep 9369229 = 3513461) B3513461
theorem B12492305 : Blo 2191435 12492305 := bstep (se 2 (by rfl) ⟨4684614, by rfl⟩ : syracuseStep 12492305 = 9369229) B9369229
theorem B8328203 : Blo 2191435 8328203 := bstep (se 1 (by rfl) ⟨6246152, by rfl⟩ : syracuseStep 8328203 = 12492305) B12492305
theorem B5552135 : Blo 2191435 5552135 := bstep (se 1 (by rfl) ⟨4164101, by rfl⟩ : syracuseStep 5552135 = 8328203) B8328203
theorem B3701423 : Blo 2191435 3701423 := bstep (se 1 (by rfl) ⟨2776067, by rfl⟩ : syracuseStep 3701423 = 5552135) B5552135
theorem B2467615 : Blo 2191435 2467615 := bstep (se 1 (by rfl) ⟨1850711, by rfl⟩ : syracuseStep 2467615 = 3701423) B3701423
theorem B3290153 : Blo 2191435 3290153 := bstep (se 2 (by rfl) ⟨1233807, by rfl⟩ : syracuseStep 3290153 = 2467615) B2467615
theorem B2193435 : Blo 2191435 2193435 := bstep (se 1 (by rfl) ⟨1645076, by rfl⟩ : syracuseStep 2193435 = 3290153) B3290153
theorem C0 (j : ℕ) (h1 : 547858 ≤ j) (h2 : j ≤ 548358) : Blo 2191435 (4 * j + 3) := by
  interval_cases j
  · exact B2191435
  · exact B2191439
  · exact B2191443
  · exact B2191447
  · exact B2191451
  · exact B2191455
  · exact B2191459
  · exact B2191463
  · exact B2191467
  · exact B2191471
  · exact B2191475
  · exact B2191479
  · exact B2191483
  · exact B2191487
  · exact B2191491
  · exact B2191495
  · exact B2191499
  · exact B2191503
  · exact B2191507
  · exact B2191511
  · exact B2191515
  · exact B2191519
  · exact B2191523
  · exact B2191527
  · exact B2191531
  · exact B2191535
  · exact B2191539
  · exact B2191543
  · exact B2191547
  · exact B2191551
  · exact B2191555
  · exact B2191559
  · exact B2191563
  · exact B2191567
  · exact B2191571
  · exact B2191575
  · exact B2191579
  · exact B2191583
  · exact B2191587
  · exact B2191591
  · exact B2191595
  · exact B2191599
  · exact B2191603
  · exact B2191607
  · exact B2191611
  · exact B2191615
  · exact B2191619
  · exact B2191623
  · exact B2191627
  · exact B2191631
  · exact B2191635
  · exact B2191639
  · exact B2191643
  · exact B2191647
  · exact B2191651
  · exact B2191655
  · exact B2191659
  · exact B2191663
  · exact B2191667
  · exact B2191671
  · exact B2191675
  · exact B2191679
  · exact B2191683
  · exact B2191687
  · exact B2191691
  · exact B2191695
  · exact B2191699
  · exact B2191703
  · exact B2191707
  · exact B2191711
  · exact B2191715
  · exact B2191719
  · exact B2191723
  · exact B2191727
  · exact B2191731
  · exact B2191735
  · exact B2191739
  · exact B2191743
  · exact B2191747
  · exact B2191751
  · exact B2191755
  · exact B2191759
  · exact B2191763
  · exact B2191767
  · exact B2191771
  · exact B2191775
  · exact B2191779
  · exact B2191783
  · exact B2191787
  · exact B2191791
  · exact B2191795
  · exact B2191799
  · exact B2191803
  · exact B2191807
  · exact B2191811
  · exact B2191815
  · exact B2191819
  · exact B2191823
  · exact B2191827
  · exact B2191831
  · exact B2191835
  · exact B2191839
  · exact B2191843
  · exact B2191847
  · exact B2191851
  · exact B2191855
  · exact B2191859
  · exact B2191863
  · exact B2191867
  · exact B2191871
  · exact B2191875
  · exact B2191879
  · exact B2191883
  · exact B2191887
  · exact B2191891
  · exact B2191895
  · exact B2191899
  · exact B2191903
  · exact B2191907
  · exact B2191911
  · exact B2191915
  · exact B2191919
  · exact B2191923
  · exact B2191927
  · exact B2191931
  · exact B2191935
  · exact B2191939
  · exact B2191943
  · exact B2191947
  · exact B2191951
  · exact B2191955
  · exact B2191959
  · exact B2191963
  · exact B2191967
  · exact B2191971
  · exact B2191975
  · exact B2191979
  · exact B2191983
  · exact B2191987
  · exact B2191991
  · exact B2191995
  · exact B2191999
  · exact B2192003
  · exact B2192007
  · exact B2192011
  · exact B2192015
  · exact B2192019
  · exact B2192023
  · exact B2192027
  · exact B2192031
  · exact B2192035
  · exact B2192039
  · exact B2192043
  · exact B2192047
  · exact B2192051
  · exact B2192055
  · exact B2192059
  · exact B2192063
  · exact B2192067
  · exact B2192071
  · exact B2192075
  · exact B2192079
  · exact B2192083
  · exact B2192087
  · exact B2192091
  · exact B2192095
  · exact B2192099
  · exact B2192103
  · exact B2192107
  · exact B2192111
  · exact B2192115
  · exact B2192119
  · exact B2192123
  · exact B2192127
  · exact B2192131
  · exact B2192135
  · exact B2192139
  · exact B2192143
  · exact B2192147
  · exact B2192151
  · exact B2192155
  · exact B2192159
  · exact B2192163
  · exact B2192167
  · exact B2192171
  · exact B2192175
  · exact B2192179
  · exact B2192183
  · exact B2192187
  · exact B2192191
  · exact B2192195
  · exact B2192199
  · exact B2192203
  · exact B2192207
  · exact B2192211
  · exact B2192215
  · exact B2192219
  · exact B2192223
  · exact B2192227
  · exact B2192231
  · exact B2192235
  · exact B2192239
  · exact B2192243
  · exact B2192247
  · exact B2192251
  · exact B2192255
  · exact B2192259
  · exact B2192263
  · exact B2192267
  · exact B2192271
  · exact B2192275
  · exact B2192279
  · exact B2192283
  · exact B2192287
  · exact B2192291
  · exact B2192295
  · exact B2192299
  · exact B2192303
  · exact B2192307
  · exact B2192311
  · exact B2192315
  · exact B2192319
  · exact B2192323
  · exact B2192327
  · exact B2192331
  · exact B2192335
  · exact B2192339
  · exact B2192343
  · exact B2192347
  · exact B2192351
  · exact B2192355
  · exact B2192359
  · exact B2192363
  · exact B2192367
  · exact B2192371
  · exact B2192375
  · exact B2192379
  · exact B2192383
  · exact B2192387
  · exact B2192391
  · exact B2192395
  · exact B2192399
  · exact B2192403
  · exact B2192407
  · exact B2192411
  · exact B2192415
  · exact B2192419
  · exact B2192423
  · exact B2192427
  · exact B2192431
  · exact B2192435
  · exact B2192439
  · exact B2192443
  · exact B2192447
  · exact B2192451
  · exact B2192455
  · exact B2192459
  · exact B2192463
  · exact B2192467
  · exact B2192471
  · exact B2192475
  · exact B2192479
  · exact B2192483
  · exact B2192487
  · exact B2192491
  · exact B2192495
  · exact B2192499
  · exact B2192503
  · exact B2192507
  · exact B2192511
  · exact B2192515
  · exact B2192519
  · exact B2192523
  · exact B2192527
  · exact B2192531
  · exact B2192535
  · exact B2192539
  · exact B2192543
  · exact B2192547
  · exact B2192551
  · exact B2192555
  · exact B2192559
  · exact B2192563
  · exact B2192567
  · exact B2192571
  · exact B2192575
  · exact B2192579
  · exact B2192583
  · exact B2192587
  · exact B2192591
  · exact B2192595
  · exact B2192599
  · exact B2192603
  · exact B2192607
  · exact B2192611
  · exact B2192615
  · exact B2192619
  · exact B2192623
  · exact B2192627
  · exact B2192631
  · exact B2192635
  · exact B2192639
  · exact B2192643
  · exact B2192647
  · exact B2192651
  · exact B2192655
  · exact B2192659
  · exact B2192663
  · exact B2192667
  · exact B2192671
  · exact B2192675
  · exact B2192679
  · exact B2192683
  · exact B2192687
  · exact B2192691
  · exact B2192695
  · exact B2192699
  · exact B2192703
  · exact B2192707
  · exact B2192711
  · exact B2192715
  · exact B2192719
  · exact B2192723
  · exact B2192727
  · exact B2192731
  · exact B2192735
  · exact B2192739
  · exact B2192743
  · exact B2192747
  · exact B2192751
  · exact B2192755
  · exact B2192759
  · exact B2192763
  · exact B2192767
  · exact B2192771
  · exact B2192775
  · exact B2192779
  · exact B2192783
  · exact B2192787
  · exact B2192791
  · exact B2192795
  · exact B2192799
  · exact B2192803
  · exact B2192807
  · exact B2192811
  · exact B2192815
  · exact B2192819
  · exact B2192823
  · exact B2192827
  · exact B2192831
  · exact B2192835
  · exact B2192839
  · exact B2192843
  · exact B2192847
  · exact B2192851
  · exact B2192855
  · exact B2192859
  · exact B2192863
  · exact B2192867
  · exact B2192871
  · exact B2192875
  · exact B2192879
  · exact B2192883
  · exact B2192887
  · exact B2192891
  · exact B2192895
  · exact B2192899
  · exact B2192903
  · exact B2192907
  · exact B2192911
  · exact B2192915
  · exact B2192919
  · exact B2192923
  · exact B2192927
  · exact B2192931
  · exact B2192935
  · exact B2192939
  · exact B2192943
  · exact B2192947
  · exact B2192951
  · exact B2192955
  · exact B2192959
  · exact B2192963
  · exact B2192967
  · exact B2192971
  · exact B2192975
  · exact B2192979
  · exact B2192983
  · exact B2192987
  · exact B2192991
  · exact B2192995
  · exact B2192999
  · exact B2193003
  · exact B2193007
  · exact B2193011
  · exact B2193015
  · exact B2193019
  · exact B2193023
  · exact B2193027
  · exact B2193031
  · exact B2193035
  · exact B2193039
  · exact B2193043
  · exact B2193047
  · exact B2193051
  · exact B2193055
  · exact B2193059
  · exact B2193063
  · exact B2193067
  · exact B2193071
  · exact B2193075
  · exact B2193079
  · exact B2193083
  · exact B2193087
  · exact B2193091
  · exact B2193095
  · exact B2193099
  · exact B2193103
  · exact B2193107
  · exact B2193111
  · exact B2193115
  · exact B2193119
  · exact B2193123
  · exact B2193127
  · exact B2193131
  · exact B2193135
  · exact B2193139
  · exact B2193143
  · exact B2193147
  · exact B2193151
  · exact B2193155
  · exact B2193159
  · exact B2193163
  · exact B2193167
  · exact B2193171
  · exact B2193175
  · exact B2193179
  · exact B2193183
  · exact B2193187
  · exact B2193191
  · exact B2193195
  · exact B2193199
  · exact B2193203
  · exact B2193207
  · exact B2193211
  · exact B2193215
  · exact B2193219
  · exact B2193223
  · exact B2193227
  · exact B2193231
  · exact B2193235
  · exact B2193239
  · exact B2193243
  · exact B2193247
  · exact B2193251
  · exact B2193255
  · exact B2193259
  · exact B2193263
  · exact B2193267
  · exact B2193271
  · exact B2193275
  · exact B2193279
  · exact B2193283
  · exact B2193287
  · exact B2193291
  · exact B2193295
  · exact B2193299
  · exact B2193303
  · exact B2193307
  · exact B2193311
  · exact B2193315
  · exact B2193319
  · exact B2193323
  · exact B2193327
  · exact B2193331
  · exact B2193335
  · exact B2193339
  · exact B2193343
  · exact B2193347
  · exact B2193351
  · exact B2193355
  · exact B2193359
  · exact B2193363
  · exact B2193367
  · exact B2193371
  · exact B2193375
  · exact B2193379
  · exact B2193383
  · exact B2193387
  · exact B2193391
  · exact B2193395
  · exact B2193399
  · exact B2193403
  · exact B2193407
  · exact B2193411
  · exact B2193415
  · exact B2193419
  · exact B2193423
  · exact B2193427
  · exact B2193431
  · exact B2193435
theorem solution (m : ℕ) (hlo : 2191435 ≤ m) (hhi : m ≤ 2193435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 547858 ≤ j := by omega
    have hj2 : j ≤ 548358 := by omega
    have hb : Blo 2191435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
